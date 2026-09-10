import NavierStokes.R3.ProblemStatement
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Kinetic energy under spatial dilation

Spatial dilation and multiplication of velocity by a fixed amplitude preserve
one energy bound over any prescribed set of times.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3.ProblemStatement

/-- Dilation of space by a nonzero scalar preserves square integrability,
even when the velocity amplitude vanishes. -/
theorem SquareIntegrableAtTime.spatial_smul {u : VelocityField} {t : ℝ}
    (hu : SquareIntegrableAtTime u t) (a b : ℝ) (hb : b ≠ 0) :
    SquareIntegrableAtTime (fun z => a • u (z.1, b • z.2)) t := by
  have h := hu.comp_smul hb
  simpa only [SquareIntegrableAtTime, norm_smul, mul_pow] using h.const_mul (‖a‖ ^ 2)

/-- The exact energy factor for velocity amplitude `a` and spatial dilation `b`.
This identity also holds for the totalized integral when a slice is not integrable. -/
theorem kineticEnergy_spatial_smul (u : VelocityField) (a b t : ℝ) :
    kineticEnergy (fun z => a • u (z.1, b • z.2)) t =
      (‖a‖ ^ 2 * |(b ^ 3)⁻¹|) * kineticEnergy u t := by
  simp only [kineticEnergy, norm_smul, mul_pow]
  rw [integral_const_mul,
    Measure.integral_comp_smul volume (fun x : Space => ‖u (t, x)‖ ^ 2) b]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space, NavierStokes.ProblemStatement.Space]
  rw [hd]
  simp only [smul_eq_mul]
  ring

/-- A single finite energy bound survives any fixed amplitude and nonzero
spatial dilation without changing the time interval. -/
theorem UniformFiniteEnergy.spatial_smul {times : Set ℝ} {u : VelocityField}
    (hu : UniformFiniteEnergy times u) (a b : ℝ) (hb : b ≠ 0) :
    UniformFiniteEnergy times (fun z => a • u (z.1, b • z.2)) := by
  obtain ⟨E, hE, hu⟩ := hu
  have hc : 0 ≤ ‖a‖ ^ 2 * |(b ^ 3)⁻¹| := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  refine ⟨(‖a‖ ^ 2 * |(b ^ 3)⁻¹|) * E, mul_nonneg hc hE, ?_⟩
  intro t ht
  obtain ⟨hI, hB⟩ := hu t ht
  refine ⟨hI.spatial_smul a b hb, ?_⟩
  rw [kineticEnergy_spatial_smul]
  exact mul_le_mul_of_nonneg_left hB hc

end NavierStokesR3.ProblemStatement
