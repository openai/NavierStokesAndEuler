import NavierStokes.LocalHeatPressure
import NavierStokes.DirectAngularDiagonal

/-!
# The literal exterior heat profile in radial coordinates

This packages the existing heat solution using the manuscript's argument
`τ / r²`, with its fixed normalization absorbed into the exterior profile.
-/

noncomputable section

namespace NavierStokes.LocalHeatFormula

open Set
open scoped ContDiff

/-- The exterior profile with the fixed physical normalization absorbed. -/
noncomputable def exteriorProfile (C h y : ℝ) : ℝ :=
  C * (2 : ℝ) ^ (1 / 2 + h) * RadialHeatProfile.profile (1 + h) (4 * y)

theorem exteriorProfile_smooth (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (exteriorProfile C h) (Ici 0) := by
  have hm : MapsTo (fun y : ℝ => 4 * y) (Ici 0) (Ici 0) := by
    intro y hy
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hy
  exact contDiffOn_const.mul
    ((RadialHeatProfile.profile_contDiffOn (show 1 < 1 + h by linarith)).comp
      (contDiffOn_const.mul contDiffOn_id) hm)

theorem exteriorProfile_iteratedDerivWithin (C : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y =
      (C * (2 : ℝ) ^ (1 / 2 + h)) * (4 : ℝ) ^ n *
        iteratedDerivWithin n (RadialHeatProfile.profile (1 + h)) (Ici 0) (4 * y) := by
  unfold exteriorProfile
  rw [iteratedDerivWithin_const_mul_field]
  rw [iteratedDerivWithin_comp_const_smul (s := Ici (0 : ℝ)) hy (uniqueDiffOn_Ici 0)
    ((RadialHeatProfile.profile_contDiffOn (show 1 < 1 + h by linarith)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) 4
    (fun z hz => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hz)]
  simp only [smul_eq_mul, mul_assoc]

/-- A finite bound independent of the nonnegative profile argument. -/
noncomputable def exteriorDerivativeBound (C h : ℝ) (n : ℕ) : ℝ :=
  |C * (2 : ℝ) ^ (1 / 2 + h)| * (4 : ℝ) ^ n *
    (|(Real.Gamma (1 + h))⁻¹ * RadialHeatProfile.derivativeCoeff (1 + h) n| *
      Real.Gamma (1 + h + (n : ℝ)))

theorem exteriorProfile_derivative_bound (C : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    |iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y| ≤ exteriorDerivativeBound C h n := by
  rw [exteriorProfile_iteratedDerivWithin C hh n hy, abs_mul, abs_mul,
    abs_of_nonneg (show 0 ≤ (4 : ℝ) ^ n by positivity)]
  exact mul_le_mul_of_nonneg_left
    (RadialHeatProfile.profile_derivative_bound (show 1 < 1 + h by linarith) n
      (mul_nonneg (by norm_num) hy)) (by positivity)

theorem exteriorProfile_all_derivatives_bounded (C : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ici (0 : ℝ),
      |iteratedDerivWithin n (exteriorProfile C h) (Ici 0) y| ≤ M := by
  refine ⟨exteriorDerivativeBound C h n, ?_, fun y hy => exteriorProfile_derivative_bound C hh n hy⟩
  exact (abs_nonneg _).trans (exteriorProfile_derivative_bound C hh n (y := 0) le_rfl)

/-- The angular speed expressed using backward time. -/
noncomputable def amplitude (C h τ r : ℝ) : ℝ :=
  C * RadialHeatProfile.radialProfile (1 + h) τ r

theorem amplitude_formula (C h τ : ℝ) {r : ℝ} (hr : 0 < r) :
    amplitude C h τ r = r ^ (-1 - 2 * h) * exteriorProfile C h (τ / r ^ 2) := by
  have hpow : (r ^ 2 / 2) ^ (-(1 / 2 + h)) =
      r ^ (-1 - 2 * h) * (2 : ℝ) ^ (1 / 2 + h) := by
    rw [Real.div_rpow (sq_nonneg r) (by norm_num), ← Real.rpow_natCast r 2,
      ← Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * -(1 / 2 + h) = -1 - 2 * h by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have harg : 2 * τ / (r ^ 2 / 2) = 4 * (τ / r ^ 2) := by ring
  rw [amplitude, RadialHeatProfile.radialProfile_source_formula, hpow, harg, exteriorProfile]
  ring

theorem amplitude_heat_equation (C : ℝ) {h τ r : ℝ}
    (hh : 0 < h) (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => amplitude C h τ r) τ =
      iteratedDeriv 2 (amplitude C h τ) r + deriv (amplitude C h τ) r / r -
        amplitude C h τ r / r ^ 2 := by
  have he := RadialHeatProfile.radial_heat_equation (show 1 < 1 + h by linarith) hτ hr
  change -deriv (fun τ => C * RadialHeatProfile.radialProfile (1 + h) τ r) τ =
    iteratedDeriv 2 (fun r => C * RadialHeatProfile.radialProfile (1 + h) τ r) r +
      deriv (fun r => C * RadialHeatProfile.radialProfile (1 + h) τ r) r / r -
      C * RadialHeatProfile.radialProfile (1 + h) τ r / r ^ 2
  rw [iteratedDeriv_const_mul_field, deriv_const_mul_field, deriv_const_mul_field]
  linear_combination C * he

theorem amplitude_eq_heatAmplitude (C h t r : ℝ) :
    amplitude C h (1 - t) r = TerminalStress.heatAmplitude C (1 + h) t r := rfl

theorem heatCoefficient_radius (C h t z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatCoefficient C h (TerminalStress.radiusPoint t r z) =
      amplitude C h (1 - t) r / r := by
  have he := TerminalStress.swirlCoefficient_amplitude C h (fun _ => 1) t z hr
  simp only [TerminalStress.radialSlice, TerminalStress.flattening, mul_one] at he
  apply (eq_div_iff hr.ne').mpr
  simpa only [BaseExterior.heatCoefficient, amplitude_eq_heatAmplitude, mul_comm] using he

theorem heatVelocity_formula (C h : ℝ) {w : ProblemStatement.SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatVelocity C h w =
      (amplitude C h (1 - w.1) (Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)) /
        Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)) • BaseResidual.angularVector w := by
  rw [BaseExterior.heatVelocity_eq_angularVector]
  have he := heatCoefficient_radius C h w.1 (w.2 2)
    (show 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) by positivity)
  rw [TerminalStress.radiusPoint_profilePoint hs.le] at he
  rw [he]

theorem heatVelocity_eq_angularField (C h : ℝ) {w : ProblemStatement.SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatVelocity C h w =
      DirectAngularDiagonal.angularField (fun p => amplitude C h (1 - p.1) p.2.1) w := by
  rw [heatVelocity_formula C h hs, DirectAngularDiagonal.angularField_eq_rotationField]
  simp only [DirectAngularDiagonal.rotationField, DirectAngularDiagonal.rate,
    DirectAngularDiagonal.profileToCyl, AxisymmetricFields.profilePoint,
    AxisymmetricResidual.pack, BaseResidual.angularVector, smul_add, smul_smul,
    zero_smul, add_zero]
  congr 1 <;> congr 1 <;> ring

theorem pressure_radius_integral (C h τ z : ℝ) {r : ℝ} (hr : 0 < r) :
    BaseExterior.heatPressure C h (TerminalStress.radiusPoint (1 - τ) r z) =
      -(∫ ρ in Ioi r, amplitude C h τ ρ ^ 2 / ρ) := by
  simpa only [TerminalStress.heatAmplitude, show 1 - (1 - τ) = τ by ring, amplitude] using
    LocalHeatPressure.heatPressure_radius_integral C h (1 - τ) z hr

theorem pressure_integrand_integrable (C : ℝ) {h τ r : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hτ : 0 < τ) (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun ρ => amplitude C h τ ρ ^ 2 / ρ) (Ioi r) := by
  simpa only [TerminalStress.heatAmplitude, show 1 - (1 - τ) = τ by ring, amplitude] using
    LocalHeatPressure.heatAmplitude_sq_div_integrable C hh hh1 (show 1 - τ < 1 by linarith) hr

end NavierStokes.LocalHeatFormula
