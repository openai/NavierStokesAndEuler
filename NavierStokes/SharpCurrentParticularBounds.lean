import NavierStokes.SharpCurrentModeJets
import NavierStokes.CurrentPhysicalRadialClosure
import NavierStokes.CurrentParticularLabelBounds

noncomputable section

namespace NavierStokes.SharpCurrentParticularBounds

open Set Function Filter ProblemStatement CorrectionStep
open CorrectionInitialization ActualCurrentParticularBounds
open CorrectionInitialization.ActualPrimary (h outgoing nominal)
open LocalPhysicalCopyBounds SharpCurrentModeJets
open SharpCurrentPhysicalPhase (nativeMap fullMap smoothNear_comp weightedPhase_smoothNear nativeMap_smoothNear)
open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}

private theorem commonGap_bound (n : ℕ) :
    CurrentPhysicalModeGerms.commonGap n ≤ CommonWindow.gap h := by
  have hn := CommonWindow.native_le_index_add h outgoing.data.h_pos.le n
  unfold CurrentPhysicalModeGerms.commonGap
  omega

/-- The sharp bound first on the strict profile annulus, where the native
coefficient class is defined. The phase is used only on its actual copy cell. -/
theorem potential_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_potential_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := rotated_mode_bound (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := HarmonicCalculus.ComplexVector)
    (F := Space) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    h D 3 p hD (by norm_num)
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := potentialCoefficient y l j n
  let F : SpaceTime → HarmonicCalculus.ComplexVector := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        CurrentPhysicalChartJets.rotated CurrentModeGeometry.chartInner c f (PhysicalWaveSum.commonLift h n d z)
  have hmode : ActualCurrentParticularPhysical.localPotentialMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPotentialMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePotential_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.rotated,
      CurrentPhysicalChartJets.rotation, CurrentPhysicalChartJets.chartMap,
      CurrentPhysicalChartJets.realVectorCLM_apply, rotationMap_complex_smul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hrot := CurrentPhysicalChartJets.rotated_smoothNear CurrentModeGeometry.chartInner_pos
      (PhysicalClassBounds.commonLift_mem_cylindricalDomain CurrentModeGeometry.chartInner_pos h n d w hann) hnear
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hrot (commonLift_smoothNear n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      CurrentPhysicalChartJets.realVectorCLM CurrentPhysicalChartJets.norm_realVectorCLM_le
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - h =
        h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.1.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      simp only [F, CurrentPhysicalChartJets.rotated, f, nativeMap, Function.comp_def] at hz ⊢
      rw [hz, map_zero, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-h) • CurrentPhysicalChartJets.realVectorCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

theorem pressure_mode_strict_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ActualCurrentWaveSupport.profileRadius h w ∈
        Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  let y := ActualCycleParameters.particularState x
  have hcar := ActualParticularCycleData.preservesCarriers H
  have hin := ActualParticularCycleData.native_inputSupport H
  have hsrc := ActualParticularCycleData.native_source_class H j hj
  have hf := actual_pressure_coefficient_class y hcar hin hN j hj hsrc
  obtain ⟨A, hA, e, hab⟩ := (native_source_bounds hf).chart_bound m
  have hg : h * ((1 / 2 + σ) + 1 / 2) = h * (σ + 1) := by ring
  rw [hg] at hab
  obtain ⟨D, hD, p, hd⟩ := native_mode_bound (E := ℂ) (B := B) (N0 := N0)
    (b := CurrentModeGeometry.chartOuter) CurrentModeGeometry.chartInner_pos
    (CommonWindow.gap h) m (h * (σ + 1)) A e hA j
  obtain ⟨C, hC, P, hc⟩ := rescaled_log_bound (E := ℂ)
    (F := ℝ) m (h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h)
    (2 * CoordinateAlgebra.A h) D 1 p hD zero_le_one
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq hr
  have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hann := CurrentModeGeometry.scaledRadial_mem_annulus n hw ⟨hr.1.le, hr.2.le⟩
  let c := PhysicalWaveSum.chooseChart CurrentModeGeometry.chartInner (PhysicalGraphBounds.scaledRadial n w)
  let d := CurrentPhysicalModeGerms.commonGap n
  have hchart := PhysicalWaveSum.chooseChart_valid CurrentModeGeometry.chartInner_pos hann
  have hzD := CurrentModeGeometry.point_mem_nativeDomain n CurrentModeGeometry.chartInner_pos c hw hchart
  have hzR := CurrentModeGeometry.point_profileRadius n CurrentModeGeometry.chartInner_pos c hw.1 hchart
  have hz : nativeMap CurrentModeGeometry.chartInner c n d w ∈ nativeStrip.domain := by
    apply ActualCurrentParticularPhysical.nativeStrip_mem hzD
    rwa [hzR]
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree CurrentModeGeometry.chartInner_pos hann)
  let f := (ActualParticularStageControls.data y l j).common.pressure n
  let F : SpaceTime → ℂ := fun z =>
    PhysicalGraphBounds.character (j : ℝ) (ActualCurrentCarrierJets.weightedPhase l n
      (nativeMap CurrentModeGeometry.chartInner c n d z)) •
        f (nativeMap CurrentModeGeometry.chartInner c n d z)
  have hmode : ActualCurrentParticularPhysical.localPressureMode y l j n =ᶠ[𝓝 w]
      (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z)) := by
    have he := CurrentPhysicalModeGerms.localPressureMode_germ y l j
      (ActualParticularStageControls.preserves_frequency hcar l) n CurrentModeGeometry.chartInner_pos c hchart
    filter_upwards [he] with z hz
    rw [hz, actual_nativePressure_eq_character y hcar]
    simp only [F, f, nativeMap, Function.comp_def, CurrentPhysicalChartJets.chartMap,
      neg_mul, smul_eq_mul]
    rfl
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hmode m]
  rcases common_control_or_zero y hin hN l j n hz with ⟨k, hk⟩ | hzero
  · have hi : fullMap CurrentModeGeometry.chartInner c n d w ∈ ActualPhaseJetBounds.phaseCell n (l,k) :=
      ActualParticularStageControls.controlPatch_subset_padded l n k hk
    have hnear : SmoothNear f (nativeMap CurrentModeGeometry.chartInner c n d w) :=
      ⟨_, nativeStrip.isOpen_domain, hz, hf.smooth l n⟩
    have hjets := hd n hn d (commonGap_bound n) c (l,k) w hann
      (PhysicalStageBounds.abs_time_le_one outgoing.data.h_pos outgoing.data.h_lt_half hw.1 hq)
      hi f hnear (hab l n hn _ hz)
    have hFn : SmoothNear F w := modulated_smoothNear
      (smoothNear_comp hnear (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis))
      (weightedPhase_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis hi) (j : ℝ)
    have he := hc n (by omega) _ hqpos (CurrentModeGeometry.band_q_comparison n hw).1
      (CurrentModeGeometry.band_q_comparison n hw).2 w F hFn hjets
      Complex.reCLM (by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro z
        simpa only [Complex.reCLM_apply, Real.norm_eq_abs, one_mul] using Complex.abs_re_le_norm z)
    have heq : h * (σ + 1) - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h - 2 * CoordinateAlgebra.A h =
        h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h := by ring
    simpa only [heq] using he
  · have h0 := hzero.2.comp_tendsto
      (nativeMap_smoothNear CurrentModeGeometry.chartInner_pos c n d haxis).contDiffAt.continuousAt
    have hF0 : F =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [h0] with z hz
      change PhysicalGraphBounds.character _ _ • f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0
      change f (nativeMap CurrentModeGeometry.chartInner c n d z) = 0 at hz
      rw [hz, smul_zero]
    have hscaled : (fun z => ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) • Complex.reCLM (F z))
        =ᶠ[𝓝 w] (fun _ => 0) := by
      filter_upwards [hF0] with z hz
      rw [hz, map_zero, smul_zero]
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hscaled m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The full valid-band bound for the actual current potential mode. Closed
annulus edges follow by continuity in a fixed physical-scale fiber. -/
theorem current_potential_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := potential_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).1 m
      (fun q => C * q ^ (h * (σ + 1) - h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
        (1 + |Real.log q|) ^ P) (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).1
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

/-- The pressure estimate has its literal quadratic physical scale and the
same per-derivative loss as the potential estimate. -/
theorem current_pressure_mode_bound (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (hj : j ≠ 0) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ (l : Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * (σ + 1) - 2 * CoordinateAlgebra.A h - (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) *
            (1 + |Real.log (PhysicalWaveSum.physicalQ h w)|) ^ P := by
  obtain ⟨C, hC, P, hb⟩ := pressure_mode_strict_bound H hN j hj m
  refine ⟨C, hC, P, ?_⟩
  intro l n hn w hw hq
  by_cases hr : ActualCurrentWaveSupport.profileRadius h w ∈
      Icc (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
  · exact CurrentPhysicalRadialClosure.jet_bound_on_closed outgoing.data.h_pos
      outgoing.data.h_lt_half (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
      (CurrentParticularLabelBounds.current_modes_contDiffOn H hN l j hj n).2 m
      (fun q => C * q ^ (h * (σ + 1) - 2 * CoordinateAlgebra.A h -
        (m : ℝ) * SharpPhysicalCarrier.derivativeCost h) * (1 + |Real.log q|) ^ P)
      (hb l n hn) hw hq hr
  · have hs := (ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l (H.inputSupport (l.2,l.1)) j 0).2
    rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq
      (hs.zero_germ outgoing.data.h_pos outgoing.data.h_lt_half (Nat.zero_le n) hw hr) m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    have hqpos := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
    exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos hqpos _).le) (by positivity)

end NavierStokes.SharpCurrentParticularBounds
