import NavierStokes.LocalAngularGrowth

/-!
# A scalar representation of the selected direct angular field

The same locally finite cutoffs can be summed as scalar cylindrical
coefficients. The resulting scalar is independent of the polar angle, and
its angular vector field is the actual selected direct sum.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace NavierStokes.LocalAngularScalar

open ProblemStatement DirectAngularDiagonal CorrectionInitialization

def angularDirection (w : SpaceTime) : Space :=
  (-w.2 1 / radius w) • coordinateVector 0 +
    (w.2 0 / radius w) • coordinateVector 1

theorem angularField_eq_smul (b : Coefficient) (w : SpaceTime) :
    angularField b w = b (cylPoint w) • angularDirection w := by
  simp only [angularField, angularDirection, smul_add, smul_smul]
  rw [mul_comm (b (cylPoint w)) (-w.2 1 / radius w),
    mul_comm (b (cylPoint w)) (w.2 0 / radius w)]

theorem angularField_add (b c : Coefficient) :
    angularField (fun p => b p + c p) = fun w => angularField b w + angularField c w := by
  funext w
  simp only [angularField_eq_smul, add_smul]

/-- Convert a smooth coefficient of the Cartesian rotation vector into its
physical angular magnitude in cylindrical coordinates. -/
def magnitudeOfProfile (F : AxisymmetricFields.Profile) : Coefficient :=
  fun p => p.2.1 * F (p.1, (p.2.1 ^ 2 / 2, p.2.2))

theorem angularField_magnitudeOfProfile (F : AxisymmetricFields.Profile) (w : SpaceTime) :
    angularField (magnitudeOfProfile F) w =
      F (AxisymmetricFields.profilePoint w.1 w.2) • BaseResidual.angularVector w := by
  have hrsq : radius w ^ 2 = w.2 0 ^ 2 + w.2 1 ^ 2 :=
    PolarCharts.radius_sq (PhysicalGraphBounds.radialProjection w)
  have hval : magnitudeOfProfile F (cylPoint w) =
      radius w * F (AxisymmetricFields.profilePoint w.1 w.2) := by
    simp only [magnitudeOfProfile, cylPoint, hrsq, AxisymmetricFields.profilePoint,
      AxisymmetricFields.radialEnergy]
  simp only [angularField, hval, BaseResidual.angularVector, smul_add, smul_smul]
  by_cases hr : radius w = 0
  · have hx0 : w.2 0 = 0 := by rw [hr] at hrsq; nlinarith [sq_nonneg (w.2 1)]
    have hx1 : w.2 1 = 0 := by rw [hr] at hrsq; nlinarith [sq_nonneg (w.2 0)]
    simp only [hx0, hx1, neg_zero, zero_div, zero_mul, mul_zero, zero_smul, add_zero]
  · have h0 : (-w.2 1 / radius w) *
        (radius w * F (AxisymmetricFields.profilePoint w.1 w.2)) =
          F (AxisymmetricFields.profilePoint w.1 w.2) * -w.2 1 := by
      field_simp [hr]
    have h1 : (w.2 0 / radius w) *
        (radius w * F (AxisymmetricFields.profilePoint w.1 w.2)) =
          F (AxisymmetricFields.profilePoint w.1 w.2) * w.2 0 := by
      field_simp [hr]
    rw [h0, h1]

def scalarSum (a : ℕ → ℝ) (q : Coefficient) (b : ℕ → Coefficient) : Coefficient :=
  fun p => ∑' j : ℕ, SmoothCutoffs.scaledCutoff (a j) (q p) * b j p

/-- Local finiteness of the cutoff series justifies pulling the angular
direction through the scalar sum, including at the axis. -/
theorem angularSum_eq_scalarSum {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    (q : Coefficient) (b : ℕ → Coefficient) {w : SpaceTime}
    (hq : ContinuousAt (fun y : SpaceTime => q (cylPoint y)) w)
    (hpos : 0 < q (cylPoint w)) :
    angularSum a (fun y => q (cylPoint y)) b w = angularField (scalarSum a q b) w := by
  have hs : Summable (fun j : ℕ =>
      SmoothCutoffs.scaledCutoff (a j) (q (cylPoint w)) * b j (cylPoint w)) := by
    simpa only [SolenoidalDiagonal.cutStage, smul_eq_mul] using
      SolenoidalDiagonal.summable_cutStage ha hq hpos
        (fun j (y : SpaceTime) => b j (cylPoint y))
  simp only [angularSum, SolenoidalDiagonal.potentialSum, SolenoidalDiagonal.cutStage,
    angularField_eq_smul, smul_smul]
  rw [hs.tsum_smul_const]
  rfl

def selectedScalar (a : ℕ → ℕ) : Coefficient :=
  scalarSum (fun j => (a j : ℝ)) (qCoefficient ActualPrimary.h)
    (fun j => (ActualCandidateAssembly.directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry j).scalar)

/-- The actual selected direct sum is one axisymmetric scalar times the
angular unit vector on the entire preterminal domain. -/
theorem selectedDirect_eq_angularField {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) :
    EqOn (LocalAngularGrowth.selectedDirect a) (angularField (selectedScalar a))
      PhysicalWaveSum.preterminal := by
  intro w hw
  have hq : ContinuousAt (fun y : SpaceTime => qCoefficient ActualPrimary.h (cylPoint y)) w :=
    (PhysicalWaveSum.physicalQ_smoothAt ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw).continuousAt
  have hpos : 0 < qCoefficient ActualPrimary.h (cylPoint w) :=
    PhysicalWaveSum.physicalQ_pos ActualPrimary.outgoing.data.h_pos
      ActualPrimary.outgoing.data.h_lt_half hw
  exact angularSum_eq_scalarSum ha (qCoefficient ActualPrimary.h)
    (fun j => (ActualCandidateAssembly.directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold
      ActualCandidateConstruction.selectedThreshold_geometry j).scalar) hq hpos

end NavierStokes.LocalAngularScalar
