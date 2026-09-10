import NavierStokes.TailGaugePotential

/-!
# The axial part of the actual slow-base potential

The stream coefficients vanish in the proved heat exterior. Consequently the
anchored potential is purely axial there, and its axial projection has the
same spatial curl as the constructed slow base.
-/

noncomputable section

namespace NavierStokes.LocalHeatExterior

open Set Filter ProblemStatement
open scoped Topology ContDiff

/-- Projection of a potential onto its axial component. -/
noncomputable def axialPart (A : VelocityField) : VelocityField :=
  fun w => A w 2 • coordinateVector 2

theorem axialPart_smooth {A : VelocityField} {S : Set SpaceTime}
    (hA : ContDiffOn ℝ ∞ A S) : ContDiffOn ℝ ∞ (axialPart A) S := by
  exact ((AxisymmetricFields.projection 2).contDiff.comp_contDiffOn hA).smul_const
    (coordinateVector 2)

theorem axialPart_awayExtensions {A : VelocityField}
    (hA : JointResidualLimits.AwayExtensions A) :
    JointResidualLimits.AwayExtensions (axialPart A) := by
  intro x hx
  obtain ⟨e⟩ := hA x hx
  refine ⟨{
    value := axialPart e.value
    domain := e.domain
    isOpen := e.isOpen
    mem := e.mem
    smooth := axialPart_smooth e.smooth
    agrees := ?_ }⟩
  intro w hw
  exact congrArg (fun u : Space => u 2 • coordinateVector 2) (e.agrees hw)

theorem axialPart_potential (H K : AxisymmetricFields.Profile) :
    axialPart (AxisymmetricFields.potential H K) = AxisymmetricFields.potential (fun _ => 0) K := by
  ext w i
  fin_cases i <;> simp [axialPart, AxisymmetricFields.potential, coordinateVector]

theorem axialPotential_curl (K : AxisymmetricFields.Profile) {w : SpaceTime}
    (hK : DifferentiableAt ℝ K (AxisymmetricFields.profilePoint w.1 w.2)) :
    SpatialCurl.spatialCurl (AxisymmetricFields.potential (fun _ => 0) K) w =
      (-AxisymmetricFields.partialS K (AxisymmetricFields.profilePoint w.1 w.2)) •
        BaseResidual.angularVector w := by
  change AxisymmetricFields.velocity (fun _ => 0) K w = _
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 0 = _
    rw [AxisymmetricFields.velocity_zero (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialZ, BaseResidual.angularVector, coordinateVector]
    ring
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 1 = _
    rw [AxisymmetricFields.velocity_one (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialZ, BaseResidual.angularVector, coordinateVector]
    ring
  · change AxisymmetricFields.velocity (fun _ => 0) K (w.1, w.2) 2 = _
    rw [AxisymmetricFields.velocity_two (fun _ => 0) K w.1 w.2 (differentiableAt_const 0) hK]
    simp [AxisymmetricFields.partialS, BaseResidual.angularVector, coordinateVector]

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

/-- The angular coefficient of the curl of the axial projection. -/
noncomputable def axialCurlCoefficient (upper : ℝ) (B : ℕ) : AxisymmetricFields.Profile :=
  fun p => -AxisymmetricFields.partialS
    (TailGaugePotential.gaugedSwirl (FinalSlowBase.scales H v upper B) F.data.h
      W.axis.normalization (FinalSlowBase.coefficients H v)) p

theorem axialCurlCoefficient_smoothAt (upper : ℝ) (B : ℕ)
    {p : AxisymmetricFields.ProfilePoint} (ht : p.1 < 1) :
    ContDiffAt ℝ ∞ (axialCurlCoefficient H v upper B) p := by
  have hK := TailGaugePotential.gaugedSwirl_smoothAt
    (C := W.axis.normalization) (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) ht
  exact ((hK.fderiv_right (show ∞ + 1 ≤ ∞ by simp)).clm_apply contDiffAt_const).neg

theorem axialPart_finalPotential_curl_angular (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (ht : w.1 < 1) :
    SpatialCurl.spatialCurl (axialPart (TailGaugePotential.finalPotential H v upper B)) w =
      axialCurlCoefficient H v upper B (AxisymmetricFields.profilePoint w.1 w.2) •
        BaseResidual.angularVector w := by
  unfold TailGaugePotential.finalPotential TailGaugePotential.potential
  rw [axialPart_potential]
  exact axialPotential_curl _
    ((TailGaugePotential.gaugedSwirl_smoothAt (FinalSlowBase.scales_strictMono H v upper B)
      F.data.h_pos F.data.h_lt_half (FinalSlowBase.coefficients_smooth H v) ht).differentiableAt
      (by simp))

theorem finalPotential_eq_axialPart (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    TailGaugePotential.finalPotential H v upper B w =
      axialPart (TailGaugePotential.finalPotential H v upper B) w := by
  have hext := ModulatedExterior.realized_exterior_coefficients W v.profiles v.finiteModification
    (FinalSlowBase.realizesScheme H v) (EntranceAlignedBase.modulated_base_eq H v)
    (EntranceAlignedBase.modulated_outer H v)
  have hzero := BaseExterior.exterior_stream_zero
    (a := FinalSlowBase.scales H v upper B) (C := W.axis.normalization)
    (p := AxisymmetricFields.profilePoint w.1 w.2)
    F.data.h_pos F.data.h_lt_half (BaseExterior.nominalExteriorRadius_pos W).le hext hw
  have he : TailGaugePotential.finalPotential H v upper B w =
      TailGaugePotential.gaugedSwirl (FinalSlowBase.scales H v upper B) F.data.h
        W.axis.normalization (FinalSlowBase.coefficients H v)
        (AxisymmetricFields.profilePoint w.1 w.2) • coordinateVector 2 := by
    simp only [TailGaugePotential.finalPotential, TailGaugePotential.potential,
      AxisymmetricFields.potential, hzero, mul_zero, zero_smul, zero_add]
  unfold axialPart
  rw [he]
  simp [coordinateVector]

theorem finalPotential_components_zero (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    TailGaugePotential.finalPotential H v upper B w 0 = 0 ∧
      TailGaugePotential.finalPotential H v upper B w 1 = 0 := by
  rw [finalPotential_eq_axialPart H v upper B hw]
  simp [axialPart, coordinateVector]

theorem axialPart_finalPotential_germ (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    axialPart (TailGaugePotential.finalPotential H v upper B) =ᶠ[𝓝 w]
      TailGaugePotential.finalPotential H v upper B := by
  filter_upwards [(BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius W)).mem_nhds hw] with y hy
  exact (finalPotential_eq_axialPart H v upper B hy).symm

theorem axialPart_finalPotential_curl (upper : ℝ) (B : ℕ) {w : SpaceTime}
    (hw : w ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    SpatialCurl.spatialCurl (axialPart (TailGaugePotential.finalPotential H v upper B)) w =
      FinalSlowBase.velocity H v upper B w := by
  rw [(SolenoidalDiagonal.spatialCurl_eventuallyEq
    (axialPart_finalPotential_germ H v upper B hw)).self_of_nhds]
  exact TailGaugePotential.finalPotential_sameCurl H v upper B hw.1

theorem axialPart_finalPotential_smooth (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (axialPart (TailGaugePotential.finalPotential H v upper B)) BaseResidual.past :=
  axialPart_smooth (TailGaugePotential.finalPotential_smooth H v upper B)

theorem axialPart_finalPotential_awayExtensions (upper : ℝ) (B : ℕ) :
    JointResidualLimits.AwayExtensions (axialPart (TailGaugePotential.finalPotential H v upper B)) :=
  axialPart_awayExtensions (TailGaugePotential.finalPotential_awayExtensions H v upper B)

end ActualBase

end NavierStokes.LocalHeatExterior
