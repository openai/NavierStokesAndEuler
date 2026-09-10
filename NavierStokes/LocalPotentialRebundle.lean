import NavierStokes.LocalAngularGrowth
import NavierStokes.LocalHeatExterior
import NavierStokes.LocalAngularScalar

/-!
# The local paper's potential representation

The selected construction stores the base swirl in an axial potential.
Moving that axial component into the direct angular field preserves the
velocity and gives the paper's vanishing vector potential in the heat exterior.
-/

noncomputable section

namespace NavierStokes.LocalPotentialRebundle

open Set Filter ProblemStatement CorrectionInitialization
open scoped Topology ContDiff

abbrev basePotential : VelocityField :=
  TailGaugePotential.finalPotential ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper ActualCandidateConstruction.selectedBudget

def removedPotential : VelocityField := LocalHeatExterior.axialPart basePotential

def potential (a : ℕ → ℕ) : VelocityField :=
  fun w => LocalAngularGrowth.selectedPotential a w - removedPotential w

def direct (a : ℕ → ℕ) : VelocityField :=
  fun w => LocalAngularGrowth.selectedDirect a w + SpatialCurl.spatialCurl removedPotential w

def pressure (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
    (PhysicalWaveSum.physicalQ ActualPrimary.h) ActualCandidateAssembly.selectedPressureStages

def velocity (a : ℕ → ℕ) : VelocityField :=
  MixedPeriodicAssembly.velocity (potential a) (direct a)

/-- The tangential magnitude is a scalar in cylindrical `(t,r,z)` coordinates. -/
def angularScalar (a : ℕ → ℕ) : DirectAngularDiagonal.Coefficient :=
  fun p => LocalAngularScalar.selectedScalar a p +
    LocalAngularScalar.magnitudeOfProfile
      (LocalHeatExterior.axialCurlCoefficient ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget) p

theorem direct_eq_angularField {a : ℕ → ℕ}
    (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    direct a w = DirectAngularDiagonal.angularField (angularScalar a) w := by
  change direct a w = DirectAngularDiagonal.angularField
    (fun p => LocalAngularScalar.selectedScalar a p +
      LocalAngularScalar.magnitudeOfProfile
        (LocalHeatExterior.axialCurlCoefficient ActualPrimary.certificate
          ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget) p) w
  rw [LocalAngularScalar.angularField_add]
  dsimp only
  change LocalAngularGrowth.selectedDirect a w + SpatialCurl.spatialCurl removedPotential w = _
  rw [LocalAngularScalar.selectedDirect_eq_angularField ha hw,
    LocalAngularScalar.angularField_magnitudeOfProfile]
  exact congrArg (fun v : Space =>
    DirectAngularDiagonal.angularField (LocalAngularScalar.selectedScalar a) w + v)
    (LocalHeatExterior.axialPart_finalPotential_curl_angular ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget hw)

theorem spatialCurl_sub {A J : VelocityField} {w : SpaceTime}
    (hA : ContDiffAt ℝ ∞ A w) (hJ : ContDiffAt ℝ ∞ J w) :
    SpatialCurl.spatialCurl (fun z => A z - J z) w =
      SpatialCurl.spatialCurl A w - SpatialCurl.spatialCurl J w := by
  exact BaseResidual.spatialCurl_sub
    (hA.differentiableAt (by simp)) (hJ.differentiableAt (by simp))

theorem removedPotential_smooth : ContDiffOn ℝ ∞ removedPotential PhysicalWaveSum.preterminal :=
  LocalHeatExterior.axialPart_smooth
    ((TailGaugePotential.finalPotential_smooth ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper ActualCandidateConstruction.selectedBudget).mono
        (fun _ hw => ⟨hw, mem_univ _⟩))

theorem potential_smooth {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) :
    ContDiffOn ℝ ∞ (potential a) PhysicalWaveSum.preterminal :=
  hs.potential.sub removedPotential_smooth

theorem direct_smooth {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) :
    ContDiffOn ℝ ∞ (direct a) PhysicalWaveSum.preterminal := by
  intro w hw
  exact ((hs.direct.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw)).add
    (SpatialCurl.contDiffAt_spatialCurl
      (removedPotential_smooth.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))
      (by simp))).contDiffWithinAt

theorem velocity_eq_original {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    velocity a w = MixedPeriodicAssembly.velocity
      (LocalAngularGrowth.selectedPotential a) (LocalAngularGrowth.selectedDirect a) w := by
  change SpatialCurl.spatialCurl
    (fun z => LocalAngularGrowth.selectedPotential a z - removedPotential z) w + direct a w = _
  rw [spatialCurl_sub (A := LocalAngularGrowth.selectedPotential a)
    (hs.potential.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))
    (removedPotential_smooth.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw))]
  simp only [direct, MixedPeriodicAssembly.velocity]
  abel

theorem velocity_eq_original_germ {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    velocity a =ᶠ[𝓝 w] MixedPeriodicAssembly.velocity
      (LocalAngularGrowth.selectedPotential a) (LocalAngularGrowth.selectedDirect a) := by
  filter_upwards [PhysicalWaveSum.preterminal_open.mem_nhds hw] with z hz
  exact velocity_eq_original hs hz

theorem residual_eq_original_germ {a : ℕ → ℕ}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a ActualPrimary.h
      ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
      ActualCandidateAssembly.selectedPressureStages) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    (fun z => navierStokesResidual (velocity a) (pressure a) z.1 z.2) =ᶠ[𝓝 w]
      MixedDiagonalResidual.residual (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ ActualPrimary.h)
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages :=
  ResidualRegularity.residual_eventuallyEq (velocity_eq_original_germ hs hw) Filter.EventuallyEq.rfl

theorem sum_eq_first {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : ℕ → SpaceTime → V} {f : SpaceTime → V} {a : ℕ → ℝ}
    {q : SpaceTime → ℝ} {w : SpaceTime}
    (h0 : A 0 w = f w) (hz : ∀ k, A (k + 1) w = 0)
    (hsmall : |a 0 * q w| < 1 / 2) :
    SolenoidalDiagonal.potentialSum a q A w = f w := by
  rw [SolenoidalDiagonal.potentialSum, tsum_eq_single 0]
  · simp only [SolenoidalDiagonal.cutStage,
      (SmoothCutoffs.scaledCutoff_eventually_one hsmall).self_of_nhds, one_smul, h0]
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [SolenoidalDiagonal.cutStage, hz k, smul_zero]

theorem selectedPotential_eq_base {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    LocalAngularGrowth.selectedPotential a w = basePotential w := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  exact sum_eq_first (H.potential_zero hw) (fun k => H.potential_succ k hw) hsmall

theorem selectedDirect_eq_zero {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold)) :
    LocalAngularGrowth.selectedDirect a w = 0 := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  have hz (j : ℕ) : ActualCandidateAssembly.selectedDirectStages j w = 0 := H.direct_zero j hw
  simp only [LocalAngularGrowth.selectedDirect, SolenoidalDiagonal.potentialSum,
    SolenoidalDiagonal.cutStage, hz, smul_zero, tsum_zero]

theorem pressure_eq_base {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    pressure a w = FinalSlowBase.pressure ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper ActualCandidateConstruction.selectedBudget w := by
  have H := ActualCandidateAssembly.exteriorStages ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry
  exact sum_eq_first (H.pressure_zero hw) (fun k => H.pressure_succ k hw) hsmall

/-- All three fields have the literal heat-exterior representation from
the local theorem, after transferring the axial potential to direct swirl. -/
theorem exterior {a : ℕ → ℕ} {w : SpaceTime}
    (hw : w ∈ ActualExteriorPrefix.exteriorDomain
      (ActualCandidateConstruction.residualBand ActualCandidateConstruction.selectedBudget
        ActualCandidateConstruction.selectedThreshold))
    (he : w ∈ BaseExterior.cartesianExterior ActualPrimary.h
      (BaseExterior.nominalExteriorRadius ActualPrimary.nominal))
    (hsmall : |(a 0 : ℝ) * PhysicalWaveSum.physicalQ ActualPrimary.h w| < 1 / 2) :
    potential a w = 0 ∧
      direct a w = BaseExterior.heatVelocity
        (BaseExterior.nominalHeatNormalization ActualPrimary.nominal) ActualPrimary.h w ∧
      pressure a w = BaseExterior.heatPressureField
        (BaseExterior.nominalHeatNormalization ActualPrimary.nominal) ActualPrimary.h w := by
  refine ⟨?_, ?_, ?_⟩
  · rw [potential, selectedPotential_eq_base hw hsmall]
    exact sub_eq_zero.mpr (LocalHeatExterior.finalPotential_eq_axialPart
      ActualPrimary.certificate ActualPrimary.modulation ActualPrimary.upper
      ActualCandidateConstruction.selectedBudget he)
  · rw [direct, selectedDirect_eq_zero hw, zero_add]
    exact (LocalHeatExterior.axialPart_finalPotential_curl ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget he).trans
      ((FinalSlowBase.exterior_fields_eq_heat ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget).1 he)
  · exact (pressure_eq_base hw hsmall).trans
      ((FinalSlowBase.exterior_fields_eq_heat ActualPrimary.certificate
        ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget).2 he)

theorem extension_sub {A J : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (eJ : JointResidualLimits.OneSidedExtension J x) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => A w - J w) x) := by
  refine ⟨{ value := fun w => eA.value w - eJ.value w
            domain := eA.domain ∩ eJ.domain
            isOpen := eA.isOpen.inter eJ.isOpen
            mem := ⟨eA.mem, eJ.mem⟩
            smooth := (eA.smooth.mono inter_subset_left).sub (eJ.smooth.mono inter_subset_right)
            agrees := ?_ }⟩
  intro w hw
  dsimp only
  rw [eA.agrees ⟨hw.1.1, hw.2⟩, eJ.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_add {A J : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x)
    (eJ : JointResidualLimits.OneSidedExtension J x) :
    Nonempty (JointResidualLimits.OneSidedExtension (fun w => A w + J w) x) := by
  refine ⟨{ value := fun w => eA.value w + eJ.value w
            domain := eA.domain ∩ eJ.domain
            isOpen := eA.isOpen.inter eJ.isOpen
            mem := ⟨eA.mem, eJ.mem⟩
            smooth := (eA.smooth.mono inter_subset_left).add (eJ.smooth.mono inter_subset_right)
            agrees := ?_ }⟩
  intro w hw
  dsimp only
  rw [eA.agrees ⟨hw.1.1, hw.2⟩, eJ.agrees ⟨hw.1.2, hw.2⟩]

theorem extension_curl {A : VelocityField} {x : Space}
    (eA : JointResidualLimits.OneSidedExtension A x) :
    Nonempty (JointResidualLimits.OneSidedExtension (SpatialCurl.spatialCurl A) x) := by
  refine ⟨{ value := SpatialCurl.spatialCurl eA.value
            domain := eA.domain
            isOpen := eA.isOpen
            mem := eA.mem
            smooth := ?_
            agrees := ?_ }⟩
  · intro w hw
    exact (SpatialCurl.contDiffAt_spatialCurl
      (eA.smooth.contDiffAt (eA.isOpen.mem_nhds hw)) (by simp)).contDiffWithinAt
  · intro w hw
    have hnear : eA.value =ᶠ[𝓝 w] A := by
      filter_upwards [(eA.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds hw]
        with z hz
      exact eA.agrees hz
    exact SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq hnear

theorem removedPotential_awayExtensions : JointResidualLimits.AwayExtensions removedPotential :=
  LocalHeatExterior.axialPart_awayExtensions
    (TailGaugePotential.finalPotential_awayExtensions ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper ActualCandidateConstruction.selectedBudget)

theorem awayExtensions {a : ℕ → ℕ}
    (eA : JointResidualLimits.AwayExtensions (LocalAngularGrowth.selectedPotential a))
    (eD : JointResidualLimits.AwayExtensions (LocalAngularGrowth.selectedDirect a)) :
    JointResidualLimits.AwayExtensions (potential a) ∧
      JointResidualLimits.AwayExtensions (direct a) := by
  constructor
  · intro x hx
    exact extension_sub (Classical.choice (eA x hx))
      (Classical.choice (removedPotential_awayExtensions x hx))
  · intro x hx
    exact extension_add (Classical.choice (eD x hx))
      (Classical.choice (extension_curl (Classical.choice (removedPotential_awayExtensions x hx))))

end NavierStokes.LocalPotentialRebundle
