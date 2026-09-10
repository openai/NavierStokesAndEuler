import NavierStokes.WholeDomainHeatGeometry

/-! # Exact scaling identities for the physical heat velocity and pressure -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainHeatBounds

open ProblemStatement PhysicalWaveSum

theorem rescale_angularVector (a : ℝ) (ha : 0 < a) (z : ℝ) (w : SpaceTime) :
    BaseResidual.angularVector (rescale a ha z w) =
      (Real.sqrt a)⁻¹ • BaseResidual.angularVector w := by
  ext i
  fin_cases i <;> simp [BaseResidual.angularVector, rescale_space, coordinateVector]

theorem rescale_heat_ratio (a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    (1-(rescale a ha z w).1) / AxisymmetricFields.radialEnergy (rescale a ha z w).2 =
      (1-w.1) / AxisymmetricFields.radialEnergy w.2 := by
  rw [rescale_time, rescale_radialEnergy]
  field_simp
  ring

theorem heatCoefficient_rescale (C h a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    a ^ RadialHeatProfile.spatialExponent (1+h) *
      BaseExterior.heatCoefficient C h (AxisymmetricFields.profilePoint
        (rescale a ha z w).1 (rescale a ha z w).2) * (Real.sqrt a)⁻¹ =
      BaseExterior.heatCoefficient C h (AxisymmetricFields.profilePoint w.1 w.2) := by
  rw [BaseExterior.heatCoefficient_eq, BaseExterior.heatCoefficient_eq]
  simp only [TerminalStress.physicalHeat, RadialHeatProfile.spatialProfile,
    AxisymmetricFields.profilePoint]
  rw [rescale_radialEnergy, rescale_time]
  have hr : 2*(1-(1-(1-w.1)/a)) / (AxisymmetricFields.radialEnergy w.2/a) =
      2*(1-w.1) / AxisymmetricFields.radialEnergy w.2 := by field_simp; ring
  rw [hr, Real.div_rpow hs.le ha.le]
  rw [show 2*(AxisymmetricFields.radialEnergy w.2/a) =
      (2*AxisymmetricFields.radialEnergy w.2)/a by ring,
    Real.sqrt_div (by positivity : 0 ≤ 2*AxisymmetricFields.radialEnergy w.2)]
  have hp : a ^ RadialHeatProfile.spatialExponent (1+h) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  have hroot : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp

theorem heatVelocity_rescale (C h a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatVelocity C h w =
      a ^ RadialHeatProfile.spatialExponent (1+h) •
        BaseExterior.heatVelocity C h (rescale a ha z w) := by
  rw [BaseExterior.heatVelocity_eq_angularVector,
    BaseExterior.heatVelocity_eq_angularVector, rescale_angularVector,
    smul_smul, smul_smul, heatCoefficient_rescale C h a ha z hs]

theorem heatPressure_rescale (C h a : ℝ) (ha : 0 < a) (z : ℝ) {w : SpaceTime}
    (hs : 0 < AxisymmetricFields.radialEnergy w.2) :
    BaseExterior.heatPressureField C h w =
      a ^ (-2*TerminalPressure.amplitudeExponent h) *
        BaseExterior.heatPressureField C h (rescale a ha z w) := by
  change BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint w.1 w.2) =
    a ^ (-2*TerminalPressure.amplitudeExponent h) *
      BaseExterior.heatPressure C h (AxisymmetricFields.profilePoint
        (rescale a ha z w).1 (rescale a ha z w).2)
  rw [BaseExterior.heatPressure_formula C h hs,
    BaseExterior.heatPressure_formula C h (by
      change 0 < AxisymmetricFields.radialEnergy (rescale a ha z w).2
      rw [rescale_radialEnergy]; exact div_pos hs ha)]
  dsimp only [AxisymmetricFields.profilePoint]
  rw [rescale_heat_ratio a ha z hs, rescale_radialEnergy, Real.div_rpow hs.le ha.le]
  have hp : a ^ (-2*TerminalPressure.amplitudeExponent h) ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  field_simp

end NavierStokes.WholeDomainHeatBounds
