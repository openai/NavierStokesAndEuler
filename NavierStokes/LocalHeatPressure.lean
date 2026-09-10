import NavierStokes.BaseExterior
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Canonical heat pressure in the radius coordinate

The canonical pressure in the regular coordinate `s = r ^ 2 / 2` is exactly
the radius tail integral of the squared heat amplitude divided by the radius.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokes.LocalHeatPressure

private theorem radiusChange_image {r : ℝ} (hr : 0 < r) :
    (fun ρ : ℝ => ρ ^ 2 / 2) '' Ioi r = Ioi (r ^ 2 / 2) := by
  ext s
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    change r < ρ at hρ
    change r ^ 2 / 2 < ρ ^ 2 / 2
    nlinarith
  · intro hs
    change r ^ 2 / 2 < s at hs
    have hs0 : 0 < s := by
      have hr2 := sq_nonneg r
      linarith
    refine ⟨Real.sqrt (2 * s), ?_, ?_⟩
    · have hsq := Real.sq_sqrt (show 0 ≤ 2 * s by positivity)
      have hnonneg := Real.sqrt_nonneg (2 * s)
      change r < Real.sqrt (2 * s)
      nlinarith
    · dsimp only
      rw [Real.sq_sqrt (by positivity)]
      ring

private theorem radiusChange_deriv (r ρ : ℝ) :
    HasDerivWithinAt (fun x : ℝ => x ^ 2 / 2) ρ (Ioi r) ρ := by
  simpa using (((hasDerivAt_id ρ).pow 2).div_const 2).hasDerivWithinAt (s := Ioi r)

private theorem radiusChange_injOn {r : ℝ} (hr : 0 < r) :
    InjOn (fun ρ : ℝ => ρ ^ 2 / 2) (Ioi r) := by
  intro x hx y hy hxy
  change r < x at hx
  change r < y at hy
  change x ^ 2 / 2 = y ^ 2 / 2 at hxy
  nlinarith

/-- Change the canonical pressure integral from `s` to the physical radius. -/
theorem canonicalPressure_radius_integral (F : SimilarityProfile.PhysicalProfile)
    (t z : ℝ) {r : ℝ} (hr : 0 < r) :
    TerminalStress.canonicalPressure F (TerminalStress.radiusPoint t r z) =
      -(∫ ρ in Ioi r, ρ * F (TerminalStress.radiusPoint t ρ z) ^ 2) := by
  unfold TerminalStress.canonicalPressure TerminalStress.radiusPoint
  dsimp only
  congr 1
  rw [← radiusChange_image hr]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun ρ _ => radiusChange_deriv r ρ) (radiusChange_injOn hr)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  dsimp only
  rw [abs_of_pos (hr.trans hρ), smul_eq_mul]

/-- The regular swirl coefficient is the heat amplitude divided by the radius. -/
theorem heatCoefficient_radius (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatCoefficient C h (TerminalStress.radiusPoint t r z) =
      TerminalStress.heatAmplitude C (1 + h) t r / r := by
  have he := TerminalStress.swirlCoefficient_amplitude C h (fun _ => 1) t z hr
  simp only [TerminalStress.radialSlice, TerminalStress.flattening, mul_one] at he
  apply (eq_div_iff hr.ne').2
  exact (mul_comm _ _).trans he

/-- The canonical pure heat pressure is the literal radial improper integral. -/
theorem heatPressure_radius_integral (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatPressure C h (TerminalStress.radiusPoint t r z) =
      -(∫ ρ in Ioi r, TerminalStress.heatAmplitude C (1 + h) t ρ ^ 2 / ρ) := by
  rw [BaseExterior.heatPressure, canonicalPressure_radius_integral _ t z hr]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  dsimp only
  rw [heatCoefficient_radius C h t z (hr.trans hρ)]
  field_simp

/-- The radius pressure integrand is integrable on every positive exterior tail. -/
theorem heatAmplitude_sq_div_integrable (C : ℝ) {h t r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ht : t < 1) (hr : 0 < r) :
    IntegrableOn (fun ρ => TerminalStress.heatAmplitude C (1 + h) t ρ ^ 2 / ρ)
      (Ioi r) := by
  have hi := BaseExterior.heatCoefficient_sq_integrable C hh hh1
    (z := 0) ht (show 0 < r ^ 2 / 2 by positivity)
  rw [← radiusChange_image hr] at hi
  have hi' := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun ρ _ => radiusChange_deriv r ρ) (radiusChange_injOn hr)
    (fun s => BaseExterior.heatCoefficient C h (t, (s, 0)) ^ 2)).mp hi
  apply hi'.congr_fun _ measurableSet_Ioi
  intro ρ hρ
  change |ρ| • BaseExterior.heatCoefficient C h
      (TerminalStress.radiusPoint t ρ 0) ^ 2 = _
  rw [abs_of_pos (hr.trans hρ), smul_eq_mul,
    heatCoefficient_radius C h t 0 (hr.trans hρ)]
  field_simp

end NavierStokes.LocalHeatPressure
