import NavierStokes.R3.CompactEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time primitive of the spatial L² norm of a compact force

All spatial and temporal integrals use ordinary Lebesgue volume.
-/

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokesR3.CompactEnergy

open NavierStokes.ProblemStatement

/-- The ordinary spatial L² norm, used with square-integrable slices. -/
def l2Norm (f : VelocityField) (t : ℝ) : ℝ := Real.sqrt (l2Sq f t)

/-- The time integral of the spatial L² norm starting at time zero. -/
def cumulativeForceNorm (f : VelocityField) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, l2Norm f t

theorem l2Norm_nonneg (f : VelocityField) (t : ℝ) : 0 ≤ l2Norm f t :=
  Real.sqrt_nonneg _

/-- A compact spacetime support supplies one compact spatial support for every
slice, and therefore continuity of the full spatial square integral. -/
theorem l2Sq_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (l2Sq f) := by
  let K : Set Space := Prod.snd '' tsupport f
  have hK : IsCompact K := hcf.isCompact.image continuous_snd
  rw [← continuousOn_univ]
  apply CompactTimeIntegral.continuousOn_integral
    (F := fun z : SpaceTime => ‖f z‖ ^ 2) hK (hf.norm.pow 2).continuousOn
  intro t ht x hx
  have hz : f (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ⟨(t, x), h, rfl⟩
  simp [hz]

theorem l2Norm_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (l2Norm f) :=
  (l2Sq_continuous hf hcf).sqrt

theorem l2Norm_intervalIntegrable {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (a b : ℝ) :
    IntervalIntegrable (l2Norm f) volume a b :=
  (l2Norm_continuous hf hcf).intervalIntegrable a b

@[simp] theorem cumulativeForceNorm_zero (f : VelocityField) :
    cumulativeForceNorm f 0 = 0 := by
  simp [cumulativeForceNorm]

theorem cumulativeForceNorm_continuous {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Continuous (cumulativeForceNorm f) :=
  intervalIntegral.continuous_primitive (l2Norm_intervalIntegrable hf hcf) 0

theorem cumulativeForceNorm_hasDerivAt {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (t : ℝ) :
    HasDerivAt (cumulativeForceNorm f) (l2Norm f t) t := by
  have hc := l2Norm_continuous hf hcf
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem cumulativeForceNorm_nonneg (f : VelocityField) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ cumulativeForceNorm f T :=
  intervalIntegral.integral_nonneg_of_forall hT (l2Norm_nonneg f)

/-- The primitive is monotone because the spatial L² norm is nonnegative. -/
theorem cumulativeForceNorm_monotone {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) : Monotone (cumulativeForceNorm f) := by
  apply monotone_of_hasDerivAt_nonneg (cumulativeForceNorm_hasDerivAt hf hcf)
  exact l2Norm_nonneg f

/-- The exact square-primitive identity needed in the integrated energy bound. -/
theorem integral_l2Norm_cumulative_eq_sq {f : VelocityField} (hf : Continuous f)
    (hcf : HasCompactSupport f) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, 2 * l2Norm f t * cumulativeForceNorm f t) =
      (cumulativeForceNorm f T) ^ 2 := by
  have hc := l2Norm_continuous hf hcf
  have hF := cumulativeForceNorm_continuous hf hcf
  have hderiv (t : ℝ) :
      HasDerivAt (fun s => (cumulativeForceNorm f s) ^ 2)
        (2 * l2Norm f t * cumulativeForceNorm f t) t := by
    convert! (cumulativeForceNorm_hasDerivAt hf hcf t).pow 2 using 1
    norm_num
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (((continuous_const.mul hc).mul hF).intervalIntegrable 0 T)
  simpa using h

end NavierStokesR3.CompactEnergy
