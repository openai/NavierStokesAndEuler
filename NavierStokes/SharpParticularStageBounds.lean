import NavierStokes.SharpParticularGluing
import NavierStokes.SharpCurrentParticularBounds
import NavierStokes.SharpActualStageBounds

noncomputable section

namespace NavierStokes.SharpParticularStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

theorem potential_log_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (particularPotential B N0 j) m
      (h*(ActualIterationLedger.sigma j+1)-h-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h) := by
  have H := ActualCyclePreservation.state_invariant B N0 hN j
  obtain ⟨C,hC,P,hb⟩ := SharpParticularGluing.localPotential_bound_of_modes H hN m
    (fun k hk => SharpCurrentParticularBounds.current_potential_mode_bound H hN k hk m)
  exact SharpParticularGluing.glued_bound_of_local m
    (GluedStageEstimates.current_compatible (runData B N0 hN)
      (ActualCyclePreservation.state_coherent B N0 hN) hN j (ActualCandidateConstruction.firstBand B N0)).1
    le_rfl ⟨C,hC,P,fun n hn w hw _ hqw => hb n ((ActualCandidateConstruction.firstBand_four B N0).trans hn) w hw hqw⟩

theorem pressure_log_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (particularPressure B N0 j) m
      (h*(ActualIterationLedger.sigma j+1)-2*CoordinateAlgebra.A h-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h) := by
  have H := ActualCyclePreservation.state_invariant B N0 hN j
  obtain ⟨C,hC,P,hb⟩ := SharpParticularGluing.localPressure_bound_of_modes H hN m
    (fun k hk => SharpCurrentParticularBounds.current_pressure_mode_bound H hN k hk m)
  exact SharpParticularGluing.glued_bound_of_local m
    (GluedStageEstimates.current_compatible (runData B N0 hN)
      (ActualCyclePreservation.state_coherent B N0 hN) hN j (ActualCandidateConstruction.firstBand B N0)).2
    le_rfl ⟨C,hC,P,fun n hn w hw _ hqw => hb n ((ActualCandidateConstruction.firstBand_four B N0).trans hn) w hw hqw⟩

private theorem common_loss (j m k : ℕ) {degree : ℝ} (hd : degree ≤ 2*CoordinateAlgebra.A h)
    (hk : k ≤ m+1) :
    ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m ≤
      h*(ActualIterationLedger.sigma j+1)-degree-(k:ℝ)*SharpPhysicalCarrier.derivativeCost h := by
  have hg := GluedStageEstimates.gain_le_current_exponent j
  have hk' : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hk
  have hc : 0 ≤ SharpPhysicalCarrier.derivativeCost h := by
    unfold SharpPhysicalCarrier.derivativeCost
    linarith [outgoing.data.h_pos]
  unfold SharpPhysicalCarrier.physicalLoss
  nlinarith

theorem potential_printed_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (particularPotential B N0 j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  (potential_log_bound B N0 hN j m).weaken outgoing.data.h_pos outgoing.data.h_lt_half
    (common_loss j m m (by unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) (by omega))

theorem pressure_printed_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (particularPressure B N0 j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  (pressure_log_bound B N0 hN j m).weaken outgoing.data.h_pos outgoing.data.h_lt_half
    (common_loss j m m le_rfl (by omega))

theorem curl_printed_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (SpatialCurl.spatialCurl (particularPotential B N0 j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  ((potential_log_bound B N0 hN j (m+1)).spatialCurl outgoing.data.h_pos outgoing.data.h_lt_half
    (particular_smooth B N0 hN j).1).weaken outgoing.data.h_pos outgoing.data.h_lt_half
    (common_loss j m (m+1) (by unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) le_rfl)

/-- The full actual potential increment satisfies exactly the printed
stage-independent loss, with all native and physical inputs discharged. -/
theorem actual_potential_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (potentialStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  SharpActualStageBounds.potential_of_particular B N0 hN j m (potential_printed_bound B N0 hN j m)

theorem actual_pressure_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0) (pressureStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  SharpActualStageBounds.pressure_of_particular B N0 hN j m (pressure_printed_bound B N0 hN j m)

theorem actual_velocity_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    LogBound h (ActualCandidateConstruction.qbig B N0)
      (MixedFiniteBackground.stageVelocity (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) :=
  SharpActualStageBounds.velocity_of_particular B N0 hN j m (curl_printed_bound B N0 hN j m)

end NavierStokes.SharpParticularStageBounds
