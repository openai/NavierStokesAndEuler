import NavierStokes.R3.H3BoxIntegral
import Mathlib.MeasureTheory.Group.Integral

/-! # The whole-space H³ supremum estimate

The unit-cube fundamental-theorem-of-calculus estimate is applied after
translation to an arbitrary point. Each local derivative integral is bounded
by its genuine Lebesgue integral over all of ℝ³.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

theorem spatialPartial_translate (i : Fin 3) (f : Space → Space) (a : Space) :
    spatialPartial i (fun x => f (x + a)) = fun x => spatialPartial i f (x + a) := by
  funext x
  exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector i))
    (fderiv_comp_add_right a)

theorem squareEnergy_translate (f : Space → Space) (a : Space) :
    squareEnergy (fun x => f (x + a)) = squareEnergy f :=
  integral_add_right_eq_self (fun x => ‖f x‖ ^ 2) a

theorem mixedEnergy_translate (f : Space → Space) (a : Space) :
    mixedEnergy (fun x => f (x + a)) = mixedEnergy f := by
  simp only [mixedEnergy, spatialPartial_translate, squareEnergy_translate]

theorem HasFiniteH3.translate {f : Space → Space} (h : HasFiniteH3 f) (a : Space) :
    HasFiniteH3 (fun x => f (x + a)) := by
  have hi {g : Space → ℝ} (hg : Integrable g) : Integrable (fun x => g (x + a)) :=
    ((measurePreserving_add_right volume a).integrable_comp hg.aestronglyMeasurable).2 hg
  refine ⟨hi h.1, ?_, ?_, ?_⟩
  · intro i
    simpa only [spatialPartial_translate] using hi (h.2.1 i)
  · intro i j
    simpa only [spatialPartial_translate] using hi (h.2.2.1 i j)
  · intro i j k
    simpa only [spatialPartial_translate] using hi (h.2.2.2 i j k)

theorem cubeMixedEnergy_le_mixedEnergy {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) :
    NavierStokes.PeriodicSobolev.mixedEnergy f ≤ mixedEnergy f := by
  have hd (g : Space → Space) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :=
    NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hg i
  have h0 := hd f hf 0
  have h1 := hd f hf 1
  have h2 := hd f hf 2
  have h10 := hd _ h0 1
  have h20 := hd _ h0 2
  have h21 := hd _ h1 2
  have h210 := hd _ h10 2
  have hb {g : Space → Space} (hg : Continuous g)
      (hgi : Integrable (fun x => ‖g x‖ ^ 2)) :
      NavierStokes.PeriodicSobolev.boxIntegral
        (NavierStokes.PeriodicSobolev.sqField g) ≤ squareEnergy g :=
    boxIntegral_le_integral (hg.norm.pow 2) hgi (fun x => sq_nonneg _)
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (hb hf.continuous hi.1) (hb h0.continuous (hi.2.1 0)))
    (hb h1.continuous (hi.2.1 1))) (hb h2.continuous (hi.2.1 2)))
    (hb h10.continuous (hi.2.2.1 1 0))) (hb h20.continuous (hi.2.2.1 2 0)))
    (hb h21.continuous (hi.2.2.1 2 1))) (hb h210.continuous (hi.2.2.2 2 1 0))

/-- H³(ℝ³) controls the value at every spatial point, with a universal
constant independent of the support or of the chosen point. -/
theorem norm_sq_le_eight_derivativeH3Energy {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) (x : Space) :
    ‖f x‖ ^ 2 ≤ 8 * derivativeH3Energy f := by
  have hs : ContDiff ℝ ∞ (fun y => f (y + x)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hlocal := NavierStokes.PeriodicSobolev.norm_sq_le_eight_mixedEnergy_on_cube hs 0
    (fun _ => by simp)
  have hglobal := cubeMixedEnergy_le_mixedEnergy hs (hi.translate x)
  rw [mixedEnergy_translate] at hglobal
  have hm := mixedEnergy_le_derivativeH3Energy f
  simpa only [zero_add] using hlocal.trans (mul_le_mul_of_nonneg_left
    (hglobal.trans hm) (by norm_num : (0 : ℝ) ≤ 8))

/-- A convenient linear form of the whole-space Sobolev bound. -/
theorem norm_le_three_derivativeH3Norm {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hi : HasFiniteH3 f) (x : Space) :
    ‖f x‖ ≤ 3 * derivativeH3Norm f := by
  have he := norm_sq_le_eight_derivativeH3Energy hf hi x
  have hn := derivativeH3Norm_nonneg f
  have hs : derivativeH3Norm f ^ 2 = derivativeH3Energy f :=
    Real.sq_sqrt (derivativeH3Energy_nonneg f)
  nlinarith [derivativeH3Energy_nonneg f]

end NavierStokesR3.H3Embedding
