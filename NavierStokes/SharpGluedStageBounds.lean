import NavierStokes.GluedStageEstimates
import NavierStokes.SharpPhysicalLogBounds
import NavierStokes.SharpWaveStageBounds
import NavierStokes.SharpMeanStageBounds

noncomputable section
namespace NavierStokes.SharpGluedStageBounds
open Set Function Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff BigOperators

open CorrectionInitialization CorrectionInitialization.ActualPrimary ActualStageEstimates

section SignedAndMean

variable {B N0 N : ℕ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*} (R : RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : GluedStageEstimates.SignedInputs D I K)

private theorem potential_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (W.potential j).alpha := by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← nativePotential_eq_ledger j] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left (W.potential_exponent j) outgoing.data.h_pos.le)

private theorem pressure_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (W.pressure j).alpha := by
  have hg := ActualIterationLedger.gain_le_wavePressure outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← nativePressure_eq_ledger j] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left (W.pressure_exponent j) outgoing.data.h_pos.le)

private theorem mean_gain (j : ℕ) :
    ActualIterationLedger.gain h (j+1) ≤ h * (1+ActualIterationLedger.sigma j-2*ChartScales.kappa) := by
  rw [nativeMean_eq_ledger]
  exact ActualIterationLedger.gain_le_mean outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)

private theorem mean_degree : CoordinateAlgebra.A h - 1/2 ≤ 2*CoordinateAlgebra.A h := by
  unfold CoordinateAlgebra.A
  linarith [outgoing.data.h_pos]

theorem signedMeanPotential_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.signedMeanPotential R M hN W j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.potential j).vector_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.potential_shift]; unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  have hs : LogBound h qbig (W.potential j).vector m
      (h*(W.potential j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have ht : LogBound h qbig (temporalInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (temporalInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
      hq mean_degree m
  have hr : LogBound h qbig (rankInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (rankInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
      hq mean_degree m
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left
  have st := (temporalInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have sr := (rankInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  exact ((hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (potential_gain W j) _)).add
    (ht.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half ss st).add
      (hr.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
      outgoing.data.h_pos outgoing.data.h_lt_half (ss.add st) sr

theorem signedMeanPressure_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.signedMeanPressure R M hN W j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.pressure j).pressure_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.pressure_shift]) m
  have hs : LogBound h qbig (W.pressure j).pressure m
      (h*(W.pressure j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have hm : LogBound h qbig (pressureInput R M hN j).family.field m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (pressureInput R M hN j).field_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq le_rfl m
  exact (hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (pressure_gain W j) _)).add
    (hm.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half
    (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left)
    ((pressureInput R M hN j).field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem direct_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (GluedStageEstimates.direct R M hN j) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hm : LogBound h qbig (angularInput R M hN j).family.angularField m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (angularInput R M hN j).angular_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq
      (by unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  exact hm.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _)

theorem signedMeanCurl_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    LogBound h qbig (SpatialCurl.spatialCurl (GluedStageEstimates.signedMeanPotential R M hN W j)) m
      (ActualIterationLedger.gain h (j+1) - SharpPhysicalCarrier.physicalLoss h m) := by
  have hs0 := (W.potential j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half
    (by rw [W.potential_shift]; unfold CoordinateAlgebra.A; linarith [outgoing.data.h_pos]) m
  have hs : LogBound h qbig (SpatialCurl.spatialCurl (W.potential j).vector) m
      (h*(W.potential j).alpha-SharpPhysicalCarrier.physicalLoss h m) := by
    obtain ⟨C,hC,n,hb⟩ := hs0
    exact ⟨C,hC,n,fun w hw hqw => hb w hw.1 hqw⟩
  have ht : LogBound h qbig (SpatialCurl.spatialCurl (temporalInput R M hN j).family.angularField) m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (temporalInput R M hN j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq mean_degree m
  have hr : LogBound h qbig (SpatialCurl.spatialCurl (rankInput R M hN j).family.angularField) m
      (h*(1+ActualIterationLedger.sigma j-2*ChartScales.kappa)-SharpPhysicalCarrier.physicalLoss h m) :=
    (rankInput R M hN j).curl_printed_bound outgoing.data.h_pos outgoing.data.h_lt_half hq mean_degree m
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono inter_subset_left
  have st := (temporalInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have sr := (rankInput R M hN j).angular_smooth outgoing.data.h_pos outgoing.data.h_lt_half hq
  have scs := InitializedPhysicalBackground.spatialCurl_smoothOn hU ss
  have sct := InitializedPhysicalBackground.spatialCurl_smoothOn hU st
  have scr := InitializedPhysicalBackground.spatialCurl_smoothOn hU sr
  have hb := ((hs.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (potential_gain W j) _)).add
    (ht.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
    outgoing.data.h_pos outgoing.data.h_lt_half scs sct).add
      (hr.weaken outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_right (mean_gain j) _))
      outgoing.data.h_pos outgoing.data.h_lt_half (scs.add sct) scr
  apply hb.congr outgoing.data.h_pos outgoing.data.h_lt_half
  intro w hw
  change _ = SpatialCurl.spatialCurl (fun z => (W.potential j).vector z +
    (temporalInput R M hN j).family.angularField z + (rankInput R M hN j).family.angularField z) w
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU (ss.add st) sr hw]
  dsimp only
  rw [InitializedPhysicalBackground.spatialCurl_add_on hU ss st hw]

theorem potential_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → VelocityField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (GluedStageEstimates.potential R M hN W particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  rw [GluedStageEstimates.potential_eq]
  exact hb.add (signedMeanPotential_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half hs
    (GluedStageEstimates.signedMeanPotential_smooth R M hN W hq j)

theorem pressure_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → PressureField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (GluedStageEstimates.pressure R M hN W particular j) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  rw [GluedStageEstimates.pressure_eq]
  exact hb.add (signedMeanPressure_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half hs
    (GluedStageEstimates.signedMeanPressure_smooth R M hN W hq j)

theorem curl_printed_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)
    {particular : ℕ → VelocityField} (j m : ℕ)
    (hs : ContDiffOn ℝ ∞ (particular j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : LogBound h qbig (SpatialCurl.spatialCurl (particular j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) :
    LogBound h qbig (SpatialCurl.spatialCurl (GluedStageEstimates.potential R M hN W particular j)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) := by
  have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half qbig
  have ss := GluedStageEstimates.signedMeanPotential_smooth R M hN W hq j
  have hsum := hb.add (signedMeanCurl_printed_bound R M hN W hq j m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (InitializedPhysicalBackground.spatialCurl_smoothOn hU hs)
    (InitializedPhysicalBackground.spatialCurl_smoothOn hU ss)
  rw [GluedStageEstimates.potential_eq]
  exact hsum.congr outgoing.data.h_pos outgoing.data.h_lt_half
    (InitializedPhysicalBackground.spatialCurl_add_on hU hs ss).symm

end SignedAndMean

end NavierStokes.SharpGluedStageBounds
