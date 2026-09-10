import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# The sharp scalar estimate for forced kinetic energy

Regularizing the square root removes the apparent singularity at zero energy.
The estimate requires derivatives only in the interior of the time interval.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.SharpEnergyBound

/-- A zero-initial-energy differential inequality controls the square root of
the energy by the time integral of the forcing norm. -/
theorem sqrt_energy_le_integral {T : ℝ} {E E' q : ℝ → ℝ}
    (hT : 0 ≤ T) (hcont : ContinuousOn E (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hinitial : E 0 = 0)
    (hq : ContinuousOn q (Icc 0 T)) (hqnonneg : ∀ t ∈ Ioo 0 T, 0 ≤ q t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ 2 * Real.sqrt (E t) * q t) :
    Real.sqrt (E T) ≤ ∫ t in 0..T, q t := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < E t + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (hnonneg t ht) (sq_pos_of_pos hε)
  have hscont : ContinuousOn (fun t => Real.sqrt (E t + ε ^ 2)) (Icc 0 T) :=
    Real.continuous_sqrt.comp_continuousOn (hcont.add continuousOn_const)
  have hsderiv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivWithinAt (fun t => Real.sqrt (E t + ε ^ 2))
        (E' t / (2 * Real.sqrt (E t + ε ^ 2))) (Ioi t) t :=
    ((hderiv t ht).add_const (ε ^ 2)).sqrt
      (ne_of_gt (hpos t ⟨ht.1.le, ht.2.le⟩)) |>.hasDerivWithinAt
  have hsbound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      E' t / (2 * Real.sqrt (E t + ε ^ 2)) ≤ q t := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.sqrt_pos.2 (hpos t ⟨ht.1.le, ht.2.le⟩)))).2
    have hsqrt : Real.sqrt (E t) ≤ Real.sqrt (E t + ε ^ 2) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
    have hmul := mul_le_mul_of_nonneg_right hsqrt (hqnonneg t ht)
    nlinarith [hbound t ht]
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hT hscont hsderiv (hq.integrableOn_Icc) hsbound
  have hzero : Real.sqrt (E 0 + ε ^ 2) = ε := by
    rw [hinitial, zero_add, Real.sqrt_sq hε.le]
  rw [hzero] at h
  have hsqrt : Real.sqrt (E T) ≤ Real.sqrt (E T + ε ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  linarith

/-- The corresponding sharp squared-energy bound. -/
theorem energy_le_integral_sq {T : ℝ} {E E' q : ℝ → ℝ}
    (hT : 0 ≤ T) (hcont : ContinuousOn E (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hinitial : E 0 = 0)
    (hq : ContinuousOn q (Icc 0 T)) (hqnonneg : ∀ t ∈ Ioo 0 T, 0 ≤ q t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ 2 * Real.sqrt (E t) * q t) :
    E T ≤ (∫ t in 0..T, q t) ^ 2 := by
  have h := sqrt_energy_le_integral hT hcont hnonneg hinitial hq hqnonneg hderiv hbound
  have hi : 0 ≤ ∫ t in 0..T, q t := (Real.sqrt_nonneg _).trans h
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) hi).2 h
  simpa only [Real.sq_sqrt (hnonneg T ⟨hT, le_rfl⟩)] using hs

end NavierStokesR3.SharpEnergyBound
