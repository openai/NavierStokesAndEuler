import NavierStokes.R3.H3Curve

/-! # The classical H³ solution class on a finite Euclidean slab

Velocity and its spatial jets belong to the genuine H³ completion. Time
differentiation is in L², and the equation holds almost everywhere in space.
Pressure is an arbitrary C¹ spatial potential;
no normalization, support, or bound on the pressure itself is imposed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Comparison

open ProblemStatement

def weakAdvection (u : Space → Space) (du : Fin 3 → Space → Space) (x : Space) : Space :=
  ∑ i, u x i • du i x

def weakLaplacian (ddu : Fin 3 → Fin 3 → Space → Space) (x : Space) : Space :=
  ∑ i, ddu i i x

def weakDivergence (du : Fin 3 → Space → Space) (x : Space) : ℝ := ∑ i, du i x i

/-- The usual strong formulation on a closed time slab, with H³ spatial
regularity and an actual L² time derivative at interior times. -/
structure StrongSolutionOnIcc (ν : ℝ) (f : VelocityField) (a b : ℝ)
    (u : VelocityField) (p : PressureField) where
  time_lt : a < b
  curve : H3Curve u (Icc a b)
  timeDerivative : VelocityField
  timeDerivative_memLp : ∀ t ∈ Ioo a b, MemLp (fun x => timeDerivative (t, x)) 2 volume
  hasDerivAt_velocity : ∀ t (ht : t ∈ Ioo a b),
    HasDerivAt curve.velocityLp
      ((timeDerivative_memLp t ht).toLp (fun x => timeDerivative (t, x))) t
  pressure_C1 : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x => p (t, x))
  divergence_free : ∀ t ∈ Ioo a b,
    ∀ᵐ x ∂volume, weakDivergence (fun i x => curve.first i (t, x)) x = 0
  navier_stokes : ∀ t ∈ Ioo a b, ∀ᵐ x ∂volume,
    timeDerivative (t, x) + weakAdvection (fun x => u (t, x))
        (fun i x => curve.first i (t, x)) x -
      ν • weakLaplacian (fun i j x => curve.second i j (t, x)) x +
      NavierStokes.ProblemStatement.pressureGradient p t x = f (t, x)

theorem weakAdvection_memLp {u : Space → Space} {du : Fin 3 → Space → Space}
    (hu : Continuous u) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, ‖u x‖ ≤ B)
    (hd : ∀ i, MemLp (du i) 2 volume) : MemLp (weakAdvection u du) 2 volume := by
  apply memLp_finsetSum
  intro i _
  apply ((hd i).const_smul B).mono
  · exact ((EuclideanSpace.proj i).continuous.comp hu).aestronglyMeasurable.smul
      (hd i).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (u x) i).trans (hb x))
      (norm_nonneg _)

/-- In the ordinary H³ solution class the pressure gradient is square
integrable because the equation expresses it as a sum of L² fields. This is
a conclusion, not an added pressure normalization hypothesis. -/
theorem StrongSolutionOnIcc.pressureGradient_memLp {ν a b : ℝ} {f u : VelocityField}
    {p : PressureField} (h : StrongSolutionOnIcc ν f a b u p)
    {t : ℝ} (ht : t ∈ Ioo a b) (hf : MemLp (fun x => f (t, x)) 2 volume) :
    MemLp (fun x => NavierStokes.ProblemStatement.pressureGradient p t x) 2 volume := by
  have htt : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hd := h.curve.approximation t htt
  have had := weakAdvection_memLp (h.curve.spatial_continuous t htt)
    (mul_nonneg (by norm_num) (h.curve.normAt_nonneg t)) (h.curve.norm_le htt)
    hd.derivative_memLp
  have hla : MemLp (weakLaplacian (fun i j x => h.curve.second i j (t, x))) 2 volume := by
    apply memLp_finsetSum
    intro i _
    exact hd.second_memLp i i
  apply (hf.sub ((h.timeDerivative_memLp t ht).add had) |>.add (hla.const_smul ν)).ae_eq
  filter_upwards [h.navier_stokes t ht] with x hx
  change f (t, x) - (h.timeDerivative (t, x) + weakAdvection (fun x => u (t, x))
    (fun i x => h.curve.first i (t, x)) x) +
      ν • weakLaplacian (fun i j x => h.curve.second i j (t, x)) x = _
  rw [← hx]
  abel

/-- A classical H³ solution on a half-open lifespan. The same velocity and
pressure solve the equation on every shorter closed slab. -/
structure ClassicalH3Solution (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) where
  lifespan_pos : 0 < T
  initial_velocity : ∀ x, u (0, x) = initial x
  on_shorter_interval : ∀ S ∈ Ioo (0 : ℝ) T, StrongSolutionOnIcc ν f 0 S u p

end NavierStokesR3.H3Comparison
