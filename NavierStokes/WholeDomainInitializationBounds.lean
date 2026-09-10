import NavierStokes.WholeDomainActualStageBounds
import NavierStokes.SharpPhysicalLogBounds

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

private noncomputable abbrev seedT (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialTemporalInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedR (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialRankInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedB (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialAngularInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)
private noncomputable abbrev seedP (B N0 : ℕ) :=
  ActualPhysicalStageBounds.actualInitialPressureInput B N0 (ActualCandidateConstruction.firstBand B N0)
    (ActualCandidateConstruction.firstBand_four B N0)

noncomputable def seedPotentialLoss (B N0 : ℕ) : ℕ → ℝ :=
  InitializedPhysicalBackground.seedPotentialLoss h (InitialPhysicalData.potentialWaveData B N0).alpha
    (InitialPhysicalData.potentialWaveData B N0).shift (min (seedT B N0).alpha (seedR B N0).alpha)

noncomputable def seedDirectLoss (B N0 : ℕ) : ℕ → ℝ :=
  InitializedPhysicalBackground.seedDirectLoss h (seedB B N0).alpha

noncomputable def seedPressureLoss (B N0 : ℕ) : ℕ → ℝ :=
  ActualPhysicalStageBounds.initialPressureLoss h (InitialPhysicalData.pressureWaveData B N0).alpha
    (InitialPhysicalData.pressureWaveData B N0).shift (seedP B N0).alpha

theorem initialPotential_bound (B N0 m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (initialPotential B N0) m (-seedPotentialLoss B N0 m) := by
  rw [initialPotential_eq_increment]
  exact LogBound.of_bound (ActualPhysicalStageBounds.initialIncrement_bound
    (InitialPhysicalData.potentialWaveData B N0) (seedT B N0) (seedR B N0)
    outgoing.data.h_pos outgoing.data.h_lt_half le_rfl le_rfl m)

theorem initialPressure_bound (B N0 m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (initialPressure B N0) m (-seedPressureLoss B N0 m) := by
  rw [initialPressure_eq_increment]
  exact LogBound.of_bound (ActualPhysicalStageBounds.initialPressureIncrement_bound
    (InitialPhysicalData.pressureWaveData B N0) (seedP B N0)
    outgoing.data.h_pos outgoing.data.h_lt_half le_rfl m)

theorem initialDirect_bound (B N0 m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (initialDirect B N0) m (-seedDirectLoss B N0 m) := by
  have he : initialDirect B N0 = (seedB B N0).family.angularField := by
    unfold initialDirect
    rw [ActualCandidateConstruction.angularMeanStages_zero]
    rfl
  rw [he]
  apply LogBound.of_bound
  have hb := (seedB B N0).angular_bound_with_gain (g := 0) (delta := -(h*(seedB B N0).alpha))
    outgoing.data.h_pos outgoing.data.h_lt_half (qbig := ActualCandidateConstruction.qbig B N0)
    le_rfl (by linarith) m
  simpa only [zero_sub, seedDirectLoss, InitializedPhysicalBackground.seedDirectLoss,
    PhysicalStageBounds.directLoss] using hb

noncomputable def initialVelocityLoss (B N0 : ℕ) (base : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (base m) (max (seedPotentialLoss B N0 (m+1)) (seedDirectLoss B N0 m))

noncomputable def initialPressureTotalLoss (B N0 : ℕ) (base : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (base m) (seedPressureLoss B N0 m)

theorem initial_velocity_of_base_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) {qbig : ℝ}
    (hq : qbig ≤ ActualCandidateConstruction.qbig B N0) (base : ℕ → ℝ) (m : ℕ)
    (hb : LogBound h qbig (FinalSlowBase.velocity certificate modulation upper B) m (-base m)) :
    LogBound h qbig (finiteVelocity B N0 hN 0) m (-initialVelocityLoss B N0 base m) := by
  have hsub : CutStageEstimates.physicalSublevel h qbig ⊆ ActualCandidateConstruction.physicalDomain B N0 :=
    fun _ hw => ⟨hw.1,hw.2.trans_le hq⟩
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
  have sp := (initialPotential_smooth B N0).mono hsub
  have sd := (initialDirect_smooth B N0).mono hsub
  have sb : ContDiffOn ℝ ∞ (FinalSlowBase.velocity certificate modulation upper B)
      (CutStageEstimates.physicalSublevel h qbig) :=
    (FinalSlowBase.velocity_smooth certificate modulation upper B).mono (fun _ hw => ⟨hw.1,mem_univ _⟩)
  have sc := InitializedPhysicalBackground.spatialCurl_smoothOn hU sp
  have hbase := hb.weaken (s := -initialVelocityLoss B N0 base m)
    outgoing.data.h_pos outgoing.data.h_lt_half (neg_le_neg (le_max_left _ _))
  have hc := (((initialPotential_bound B N0 (m+1)).mono_domain hq).spatialCurl
    outgoing.data.h_pos outgoing.data.h_lt_half sp).weaken (s := -initialVelocityLoss B N0 base m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (neg_le_neg ((le_max_left _ _).trans (le_max_right _ _)))
  have hd := ((initialDirect_bound B N0 m).mono_domain hq).weaken (s := -initialVelocityLoss B N0 base m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (neg_le_neg ((le_max_right _ _).trans (le_max_right _ _)))
  have hsum := (hbase.add hc outgoing.data.h_pos outgoing.data.h_lt_half sb sc).add hd
    outgoing.data.h_pos outgoing.data.h_lt_half (sb.add sc) sd
  apply hsum.congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w hw
  rw [finiteVelocity,MixedFiniteBackground.uncutVelocity_zero]
  change _ = SpatialCurl.spatialCurl (potentialStages B N0 hN 0) w + directStages B N0 hN 0 w
  rw [potentialStages_zero,directStages_zero,zerothPotential]
  have spa : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential certificate modulation upper B)
      (CutStageEstimates.physicalSublevel h qbig) :=
    (TailGaugePotential.finalPotential_smooth certificate modulation upper B).mono
      (fun _ hw => ⟨hw.1,mem_univ _⟩)
  change _ = SpatialCurl.spatialCurl (fun z =>
    TailGaugePotential.finalPotential certificate modulation upper B z + initialPotential B N0 z) w +
      initialDirect B N0 w
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU spa sp hw]
  dsimp only
  rw [TailGaugePotential.finalPotential_sameCurl certificate modulation upper B hw.1]

theorem initial_pressure_of_base_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) {qbig : ℝ}
    (hq : qbig ≤ ActualCandidateConstruction.qbig B N0) (base : ℕ → ℝ) (m : ℕ)
    (hb : LogBound h qbig (FinalSlowBase.pressure certificate modulation upper B) m (-base m)) :
    LogBound h qbig (pressureStages B N0 hN 0) m (-initialPressureTotalLoss B N0 base m) := by
  have sb : ContDiffOn ℝ ∞ (FinalSlowBase.pressure certificate modulation upper B)
      (CutStageEstimates.physicalSublevel h qbig) :=
    (FinalSlowBase.pressure_smooth certificate modulation upper B).mono (fun _ hw => ⟨hw.1,mem_univ _⟩)
  have si := (initialPressure_smooth B N0).mono
    (show CutStageEstimates.physicalSublevel h qbig ⊆ ActualCandidateConstruction.physicalDomain B N0 from
      fun _ hw => ⟨hw.1,hw.2.trans_le hq⟩)
  have hbase := hb.weaken (s := -initialPressureTotalLoss B N0 base m)
    outgoing.data.h_pos outgoing.data.h_lt_half (neg_le_neg (le_max_left _ _))
  have hi := ((initialPressure_bound B N0 m).mono_domain hq).weaken (s := -initialPressureTotalLoss B N0 base m)
    outgoing.data.h_pos outgoing.data.h_lt_half (neg_le_neg (le_max_right _ _))
  exact hbase.add hi outgoing.data.h_pos outgoing.data.h_lt_half sb si

end NavierStokes.WholeDomainStageBounds
