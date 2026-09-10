import NavierStokes.ActualPhysicalStageBounds
import NavierStokes.SharpMeanJetBounds

noncomputable section
namespace NavierStokes.ActualPhysicalStageBounds.MeanInput
open Set Function Filter ProblemStatement
open SharpMeanJetBounds SharpPhysicalCarrier
open scoped Topology ContDiff

/-- Coherent physical scalar means retain the exact graph loss and the
native logarithmic factor on their original common physical domain. -/
theorem field_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.field_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w hw.1 (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)

theorem angular_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.angularField_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w hw.1 (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw) (hw.2.le.trans hq)

theorem curl_log_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl M.family.angularField) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-meanLoss h degree (m+1))*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpMeanJetBounds.curl_angularField_log_bound M.family hh hh1 M.lower_pos
    M.radii_lt M.band_four (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets m
  refine ⟨C,hC,N,?_⟩
  intro w hw hqw
  exact hb w ⟨hw.1, hw.2.trans_le hq⟩ (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hqw)

private theorem common_loss_bound {h degree q C α : ℝ} {m k : ℕ}
    (hh : 0 ≤ h) (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (hkm : k ≤ m+1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C) (N : ℕ) :
    C*q^(h*α-meanLoss h degree k)*(1+|Real.log q|)^N ≤
      C*q^(h*α-physicalLoss h m)*(1+|Real.log q|)^N := by
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have hm : 0 ≤ (m:ℝ)+1 := by positivity
  have he : h*α-physicalLoss h m ≤ h*α-meanLoss h degree k := by
    unfold physicalLoss meanLoss derivativeCost
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1 he) hC) (by positivity)

theorem field_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.field_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree (by omega) (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

theorem angular_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.angular_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree (by omega) (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

theorem curl_printed_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1/2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hdegree : degree ≤ 2*CoordinateAlgebra.A h) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl M.family.angularField) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*M.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := M.curl_log_bound hh hh1 hq m
  exact ⟨C,hC,N,fun w hw hqw => (hb w hw hqw).trans
    (common_loss_bound hh.le hdegree le_rfl (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hC N)⟩

end NavierStokes.ActualPhysicalStageBounds.MeanInput
