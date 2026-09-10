import NavierStokes.SharpGluedStageBounds
import NavierStokes.ActualCandidateAssembly

noncomputable section

namespace NavierStokes.SharpActualStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

theorem potential_of_particular (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ)
    (hb : LogBound h (ActualCandidateConstruction.qbig B N0) (particularPotential B N0 j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (potentialStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have he := representations B N0 hN
  exact (potential_printed_bound (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
    le_rfl j m (particular_smooth B N0 hN j).1 hb).congr outgoing.data.h_pos outgoing.data.h_lt_half
    (he.potential_succ j)

theorem pressure_of_particular (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ)
    (hb : LogBound h (ActualCandidateConstruction.qbig B N0) (particularPressure B N0 j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (pressureStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have he := representations B N0 hN
  exact (pressure_printed_bound (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
    le_rfl j m (particular_smooth B N0 hN j).2 hb).congr outgoing.data.h_pos outgoing.data.h_lt_half
    (he.pressure_succ j)

theorem curl_of_particular (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ)
    (hb : LogBound h (ActualCandidateConstruction.qbig B N0)
      (SpatialCurl.spatialCurl (particularPotential B N0 j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h (ActualCandidateConstruction.qbig B N0)
      (SpatialCurl.spatialCurl (potentialStages B N0 hN (j+1))) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have he := representations B N0 hN
  have hc := curl_printed_bound (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) (ActualSignedWaveData.signedInputs B N0 hN)
    le_rfl j m (particular_smooth B N0 hN j).1 hb
  apply hc.congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w hw
  exact (SolenoidalDiagonal.spatialCurl_eventuallyEq
    (Filter.eventuallyEq_of_mem
      ((CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half _).mem_nhds hw)
      (he.potential_succ j))).self_of_nhds

theorem direct_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (directStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  (direct_printed_bound (runData B N0 hN) (meanCycleInput B N0 hN)
    (ActualCandidateConstruction.firstBand_four B N0) le_rfl j m).congr
      outgoing.data.h_pos outgoing.data.h_lt_half ((representations B N0 hN).direct_succ j)

theorem velocity_of_particular (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ)
    (hb : LogBound h (ActualCandidateConstruction.qbig B N0)
      (SpatialCurl.spatialCurl (particularPotential B N0 j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h (ActualCandidateConstruction.qbig B N0)
      (MixedFiniteBackground.stageVelocity (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have hs := stages_smooth B N0 hN
  exact (curl_of_particular B N0 hN j m hb).add (direct_bound B N0 hN j m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (InitializedPhysicalBackground.spatialCurl_smoothOn
      (CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half _)
      (hs.1 (j+1))) (hs.2.1 (j+1))

end NavierStokes.SharpActualStageBounds
