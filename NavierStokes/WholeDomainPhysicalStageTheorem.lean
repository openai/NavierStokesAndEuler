import NavierStokes.WholeDomainBaseBounds
import NavierStokes.WholeDomainInitializationBounds
import NavierStokes.WholeDomainPrefixBounds
import NavierStokes.SharpParticularStageBounds

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly
open scoped Topology ContDiff BigOperators

/-- One derivative loss controls both finite fields. It contains no
finite-stage index and is chosen on the original fixed construction. -/
noncomputable def finiteLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max
    (prefixLoss (initialVelocityLoss B N0 ActualBaseVelocityBounds.heatLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)
    (prefixLoss (initialPressureTotalLoss B N0 ActualBasePressureBounds.pressureLoss)
      (SharpPhysicalCarrier.physicalLoss h) m)

private theorem commonDomain_subset (B N0 : ℕ) :
    CutStageEstimates.physicalSublevel h (commonQ B N0) ⊆ ActualCandidateConstruction.physicalDomain B N0 :=
  fun _ hw => ⟨hw.1,hw.2.trans (commonQ_lt_original B N0)⟩

/-- Every literal finite velocity prefix is bounded throughout one
common domain, including the unbounded radial exterior. -/
theorem actual_finite_velocity_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J m : ℕ) :
    LogBound h (commonQ B N0) (finiteVelocity B N0 hN J) m (-finiteLoss B N0 m) := by
  have hs := stages_smooth B N0 hN
  have hA := fun j => (hs.1 j).mono (commonDomain_subset B N0)
  have hB := fun j => (hs.2.1 j).mono (commonDomain_subset B N0)
  have hzero : ∀ k, LogBound h (commonQ B N0) (finiteVelocity B N0 hN 0) k
      (-initialVelocityLoss B N0 ActualBaseVelocityBounds.heatLoss k) := by
    intro k
    apply initial_velocity_of_base_bound B N0 hN (commonQ_lt_original B N0).le
      ActualBaseVelocityBounds.heatLoss k
    apply LogBound.of_bound
    obtain ⟨C,hC,hb⟩ := WholeDomainBaseBounds.velocity_bound certificate modulation upper B k
    exact ⟨C,hC,fun w hw hq => hb w hw.1 hq⟩
  have hpos := fun j k => (SharpParticularStageBounds.actual_velocity_bound B N0 hN j k).mono_domain
    (commonQ_lt_original B N0).le
  exact (finite_velocity_log_bound outgoing.data.h_pos outgoing.data.h_lt_half hA hB
    (ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le) hzero hpos J m).weaken
      outgoing.data.h_pos outgoing.data.h_lt_half (neg_le_neg (le_max_left _ _))

/-- The pressure prefix has the same fixed domain and the same loss as
the velocity prefix. -/
theorem actual_finite_pressure_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J m : ℕ) :
    LogBound h (commonQ B N0) (finitePressure B N0 hN J) m (-finiteLoss B N0 m) := by
  have hs := fun j => ((stages_smooth B N0 hN).2.2 j).mono (commonDomain_subset B N0)
  have hzero : ∀ k, LogBound h (commonQ B N0) (pressureStages B N0 hN 0) k
      (-initialPressureTotalLoss B N0 ActualBasePressureBounds.pressureLoss k) := by
    intro k
    apply initial_pressure_of_base_bound B N0 hN (commonQ_lt_original B N0).le
      ActualBasePressureBounds.pressureLoss k
    apply LogBound.of_bound
    obtain ⟨C,hC,hb⟩ := WholeDomainBaseBounds.pressure_bound certificate modulation upper B k
    exact ⟨C,hC,fun w hw hq => hb w hw.1 hq⟩
  have hpos := fun j k => (SharpParticularStageBounds.actual_pressure_bound B N0 hN j k).mono_domain
    (commonQ_lt_original B N0).le
  exact (prefix_log_bound outgoing.data.h_pos outgoing.data.h_lt_half hs
    (ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le) hzero hpos J m).weaken
      outgoing.data.h_pos outgoing.data.h_lt_half (neg_le_neg (le_max_right _ _))

/-- Both fields of a finite prefix obey a single whole-domain estimate. -/
theorem actual_finite_fields_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (finiteVelocity B N0 hN J) w‖ +
        ‖iteratedFDeriv ℝ m (finitePressure B N0 hN J) w‖ ≤
        C * physicalQ h w ^ (-finiteLoss B N0 m) * (1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨C,hC,P,hv⟩ := actual_finite_velocity_bound B N0 hN J m
  obtain ⟨D,hD,Q,hp⟩ := actual_finite_pressure_bound B N0 hN J m
  refine ⟨C+D,add_nonneg hC hD,P+Q,?_⟩
  intro w hw
  have hq := hw.2.le.trans (commonQ_le_one B N0)
  have hq0 := physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have hv' := (hv w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (Nat.le_add_right P Q)) (mul_nonneg hC (Real.rpow_nonneg hq0.le _)))
  have hp' := (hp w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (Nat.le_add_left Q P)) (mul_nonneg hD (Real.rpow_nonneg hq0.le _)))
  exact (add_le_add hv' hp').trans_eq (by ring)

/-- Whole-domain physical-loss estimates for the actual iteration: every
stage uses the same positive scale, every finite prefix uses the same
derivative loss, and each increment has the manuscript's printed loss. -/
theorem physical_stage_estimates (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    0 < commonQ B N0 ∧
    (∀ J m, LogBound h (commonQ B N0) (finiteVelocity B N0 hN J) m (-finiteLoss B N0 m) ∧
      LogBound h (commonQ B N0) (finitePressure B N0 hN J) m (-finiteLoss B N0 m)) ∧
    (∀ J m, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (fun z => navierStokesResidual
        (finiteVelocity B N0 hN J) (finitePressure B N0 hN J) z.1 z.2) w‖ ≤
        C * physicalQ h w ^ (h*ActualIterationLedger.sigma J-ActualCycleResidualBounds.fixedLoss m)) ∧
    (∀ j m, LogBound h (commonQ B N0)
      (MixedFiniteBackground.stageVelocity (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) ∧
      LogBound h (commonQ B N0) (pressureStages B N0 hN (j+1)) m
      (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m)) := by
  refine ⟨commonQ_pos B N0,?_,actual_finite_residual_bound B N0 hN,?_⟩
  · exact fun J m => ⟨actual_finite_velocity_bound B N0 hN J m,actual_finite_pressure_bound B N0 hN J m⟩
  · exact fun j m => ⟨(SharpParticularStageBounds.actual_velocity_bound B N0 hN j m).mono_domain
      (commonQ_lt_original B N0).le,
      (SharpParticularStageBounds.actual_pressure_bound B N0 hN j m).mono_domain (commonQ_lt_original B N0).le⟩

/-- Every component of `Z_j = (A_j, B_j, p_j)` and the recovered velocity
increment obey one common constant and logarithmic power. -/
theorem actual_increment_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (potentialStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (directStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (pressureStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (MixedFiniteBackground.stageVelocity
          (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) w‖ ≤
      C * physicalQ h w ^ (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) *
        (1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨C,hC,P,hv⟩ := (SharpParticularStageBounds.actual_potential_bound B N0 hN j m).mono_domain
    (commonQ_lt_original B N0).le
  obtain ⟨D,hD,Q,hd⟩ := (SharpActualStageBounds.direct_bound B N0 hN j m).mono_domain
    (commonQ_lt_original B N0).le
  obtain ⟨F,hF,R,hp⟩ := (SharpParticularStageBounds.actual_pressure_bound B N0 hN j m).mono_domain
    (commonQ_lt_original B N0).le
  obtain ⟨G,hG,S,hu⟩ := (SharpParticularStageBounds.actual_velocity_bound B N0 hN j m).mono_domain
    (commonQ_lt_original B N0).le
  refine ⟨C+D+F+G,by positivity,P+Q+R+S,?_⟩
  intro w hw
  have hq := hw.2.le.trans (commonQ_le_one B N0)
  have hq0 := physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have hv' := (hv w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (show P ≤ P+Q+R+S by omega)) (mul_nonneg hC (Real.rpow_nonneg hq0.le _)))
  have hd' := (hd w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (show Q ≤ P+Q+R+S by omega)) (mul_nonneg hD (Real.rpow_nonneg hq0.le _)))
  have hp' := (hp w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (show R ≤ P+Q+R+S by omega)) (mul_nonneg hF (Real.rpow_nonneg hq0.le _)))
  have hu' := (hu w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (show S ≤ P+Q+R+S by omega)) (mul_nonneg hG (Real.rpow_nonneg hq0.le _)))
  exact (add_le_add (add_le_add (add_le_add hv' hd') hp') hu').trans_eq (by ring)

noncomputable def paperLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  max (finiteLoss B N0 m) (ActualCycleResidualBounds.fixedLoss m)

/-- The three quantitative conclusions of `iter:physical-loss`, with one
domain and one common finite-prefix/residual loss. The residual conclusion
is stronger than the displayed estimate: all flat remainders are absorbed,
so its additional flat-error term can be chosen to be zero. -/
theorem exact_physical_loss (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    0 < commonQ B N0 ∧
    (∀ j m, ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (potentialStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (directStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (pressureStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ m (MixedFiniteBackground.stageVelocity
          (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) w‖ ≤
      C * physicalQ h w ^ (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) *
        (1+|Real.log (physicalQ h w)|)^P) ∧
    (∀ J m, ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (finiteVelocity B N0 hN J) w‖ +
        ‖iteratedFDeriv ℝ m (finitePressure B N0 hN J) w‖ ≤
        C * physicalQ h w ^ (-paperLoss B N0 m) * (1+|Real.log (physicalQ h w)|)^P) ∧
    (∀ J m, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (fun z => navierStokesResidual
        (finiteVelocity B N0 hN J) (finitePressure B N0 hN J) z.1 z.2) w‖ ≤
        C * physicalQ h w ^ (h*ActualIterationLedger.sigma J-paperLoss B N0 m)) := by
  refine ⟨commonQ_pos B N0,actual_increment_bound B N0 hN,?_,?_⟩
  · intro J m
    obtain ⟨C,hC,P,hb⟩ := actual_finite_fields_bound B N0 hN J m
    refine ⟨C,hC,P,fun w hw => (hb w hw).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
        (hw.2.le.trans (commonQ_le_one B N0)) (neg_le_neg (le_max_left _ _))) hC) (by positivity)
  · intro J m
    obtain ⟨C,hC,hb⟩ := actual_finite_residual_bound B N0 hN J m
    refine ⟨C,hC,fun w hw => (hb w hw).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
        (hw.2.le.trans (commonQ_le_one B N0)) (sub_le_sub_left (le_max_right _ _) _)) hC

/-- A stage-independent loss for all derivatives through the specified order. -/
noncomputable def paperJetLoss (B N0 : ℕ) (m : ℕ) : ℝ :=
  ∑ k : Fin (m+1), |paperLoss B N0 k.val|

theorem paperLoss_le_paperJetLoss (B N0 m k : ℕ) (hk : k ≤ m) :
    paperLoss B N0 k ≤ paperJetLoss B N0 m := by
  exact (le_abs_self _).trans (Finset.single_le_sum
    (fun t _ => abs_nonneg (paperLoss B N0 t.val))
    (Finset.mem_univ (⟨k,by omega⟩ : Fin (m+1))))

private theorem physicalLoss_mono {k m : ℕ} (hkm : k ≤ m) :
    SharpPhysicalCarrier.physicalLoss h k ≤ SharpPhysicalCarrier.physicalLoss h m := by
  have hk : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  unfold SharpPhysicalCarrier.physicalLoss SharpPhysicalCarrier.derivativeCost
  nlinarith [outgoing.data.h_pos]

private theorem finite_log_bounds (B N0 m : ℕ) (F : ℕ → SpaceTime → ℝ) (e : ℝ)
    (hF : ∀ k ≤ m, ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      F k w ≤ C * physicalQ h w ^ e * (1+|Real.log (physicalQ h w)|)^P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ k ≤ m,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      F k w ≤ C * physicalQ h w ^ e * (1+|Real.log (physicalQ h w)|)^P := by
  choose C hC P hb using fun k : Fin (m+1) => hF k.val (by omega)
  refine ⟨∑ k, C k,Finset.sum_nonneg (fun k _ => hC k),∑ k, P k,?_⟩
  intro k hk w hw
  let i : Fin (m+1) := ⟨k,by omega⟩
  have hq := (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have hP : P i ≤ ∑ t, P t := Finset.single_le_sum (fun t _ => Nat.zero_le (P t)) (Finset.mem_univ i)
  have hCi : C i ≤ ∑ t, C t := Finset.single_le_sum (fun t _ => hC t) (Finset.mem_univ i)
  exact (hb i w hw).trans ((mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL hP) (mul_nonneg (hC i) (Real.rpow_nonneg hq _))).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg hq _))
      (pow_nonneg (by linarith) _)))

private theorem finite_power_bounds (B N0 m : ℕ) (F : ℕ → SpaceTime → ℝ) (e : ℝ)
    (hF : ∀ k ≤ m, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      F k w ≤ C * physicalQ h w ^ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ m,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      F k w ≤ C * physicalQ h w ^ e := by
  choose C hC hb using fun k : Fin (m+1) => hF k.val (by omega)
  refine ⟨∑ k, C k,Finset.sum_nonneg (fun k _ => hC k),?_⟩
  intro k hk w hw
  let i : Fin (m+1) := ⟨k,by omega⟩
  exact (hb i w hw).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun t _ => hC t) (Finset.mem_univ i))
    (Real.rpow_nonneg (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le _))

/-- The complete printed physical-loss statement. All components of `Z_j`
and the velocity increment are included, and each bound simultaneously covers
every derivative through order `m`, as required by the manuscript's jet norm.
The scale is common to all stages and orders; the prefix/residual loss is
independent of the finite-stage index. -/
theorem paper_physical_loss (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    0 < commonQ B N0 ∧
    (∀ j m, ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ k ≤ m,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ k (potentialStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ k (directStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ k (pressureStages B N0 hN (j+1)) w‖ +
        ‖iteratedFDeriv ℝ k (MixedFiniteBackground.stageVelocity
          (potentialStages B N0 hN) (directStages B N0 hN) (j+1)) w‖ ≤
      C * physicalQ h w ^ (ActualIterationLedger.gain h (j+1)-SharpPhysicalCarrier.physicalLoss h m) *
        (1+|Real.log (physicalQ h w)|)^P) ∧
    (∀ J m, ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ k ≤ m,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ k (finiteVelocity B N0 hN J) w‖ +
        ‖iteratedFDeriv ℝ k (finitePressure B N0 hN J) w‖ ≤
        C * physicalQ h w ^ (-paperJetLoss B N0 m) * (1+|Real.log (physicalQ h w)|)^P) ∧
    (∀ J m, ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ m,
      ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ k (fun z => navierStokesResidual
        (finiteVelocity B N0 hN J) (finitePressure B N0 hN J) z.1 z.2) w‖ ≤
        C * physicalQ h w ^ (h*ActualIterationLedger.sigma J-paperJetLoss B N0 m)) := by
  obtain ⟨hq,hi,hf,hr⟩ := exact_physical_loss B N0 hN
  refine ⟨hq,?_,?_,?_⟩
  · intro j m
    apply finite_log_bounds
    intro k hk
    obtain ⟨C,hC,P,hb⟩ := hi j k
    refine ⟨C,hC,P,fun w hw => (hb w hw).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
        (hw.2.le.trans (commonQ_le_one B N0)) (sub_le_sub_left (physicalLoss_mono hk) _)) hC) (by positivity)
  · intro J m
    apply finite_log_bounds
    intro k hk
    obtain ⟨C,hC,P,hb⟩ := hf J k
    refine ⟨C,hC,P,fun w hw => (hb w hw).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
        (hw.2.le.trans (commonQ_le_one B N0)) (neg_le_neg (paperLoss_le_paperJetLoss B N0 m k hk))) hC) (by positivity)
  · intro J m
    apply finite_power_bounds
    intro k hk
    obtain ⟨C,hC,hb⟩ := hr J k
    refine ⟨C,hC,fun w hw => (hb w hw).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
        (hw.2.le.trans (commonQ_le_one B N0))
        (sub_le_sub_left (paperLoss_le_paperJetLoss B N0 m k hk) _)) hC

end NavierStokes.WholeDomainStageBounds
