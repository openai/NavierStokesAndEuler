import NavierStokes.GluedStageEstimates
import NavierStokes.SharpPhysicalLogBounds

noncomputable section

namespace NavierStokes.SharpParticularGluing

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open CorrectionInitialization.ActualPrimary CorrectionStep
open scoped Topology ContDiff BigOperators

theorem glued_bound_of_local {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {N : ℕ} {f : ℕ → SpaceTime → V} {qbig r : ℝ} (m : ℕ)
    (hf : ValidDyadicBandCover.Compatible h N f) (hq : qbig ≤ ChartScales.Q N)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n, N ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      physicalQ h w ≤ ChartScales.Q n → physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (f n) w‖ ≤ C * physicalQ h w ^ r * (1+|Real.log (physicalQ h w)|)^P) :
    LogBound h qbig (ValidDyadicBandCover.field h N f) m r := by
  obtain ⟨C,hC,P,hb⟩ := hb
  refine ⟨C,hC,P,fun w hw hqw => ?_⟩
  exact ValidDyadicBandCover.field_jet_bound_at outgoing.data.h_pos outgoing.data.h_lt_half
    hf hw.1 (hw.2.le.trans hq) m (fun n hn hband hcomp => hb n hn w hband hcomp hqw)

private theorem choose_mode_constants {P : ℤ → ℝ → ℕ → Prop}
    (hP : ∀ k, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, P k C N) :
    ∃ C : ℤ → ℝ, (∀ k, 0 ≤ C k) ∧ ∃ N : ℤ → ℕ, ∀ k, k ≠ 0 → P k (C k) (N k) := by
  classical
  have hs (k : ℤ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, k ≠ 0 → P k C N := by
    by_cases hk : k = 0
    · exact ⟨0,le_rfl,0,fun hn => (hn hk).elim⟩
    · obtain ⟨C,hC,N,hb⟩ := hP k hk
      exact ⟨C,hC,N,fun _ => hb⟩
  choose C hC N hb using hs
  exact ⟨C,hC,N,hb⟩

section HarmonicSums

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}
  (H : ActualParticularCycleData.Invariant σ x)
  (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)

include H hGeom

theorem localPotential_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ,
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
        C * physicalQ h w ^ r * (1+|Real.log (physicalQ h w)|)^P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      physicalQ h w ≤ 1 → ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPotential x n) w‖ ≤
        C * physicalQ h w ^ r * (1+|Real.log (physicalQ h w)|)^P := by
  classical
  obtain ⟨C,hC,P,hb⟩ := choose_mode_constants hb
  let modes := ParticularWaveAssembly.modes x.coefficients.residualBand
  refine ⟨2250*∑ k ∈ modes,C k,mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)),
    ∑ k ∈ modes,P k,?_⟩
  intro n hn w hw hq
  have hq0 := physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have he := CurrentParticularLabelBounds.localPotential_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k*physicalQ h w^r*(1+|Real.log (physicalQ h w)|)^(∑ k ∈ modes,P k))
    (fun k _ => mul_nonneg (mul_nonneg (hC k) (Real.rpow_nonneg hq0.le r)) (by positivity))
    (by
      intro l hl k hk hc
      apply (hb k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hC k) (Real.rpow_nonneg hq0.le r))
      exact pow_le_pow_right₀ hL (Finset.single_le_sum (by intros; omega) hk))
  exact he.trans_eq (by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring)

theorem localPressure_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ,
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
        C * physicalQ h w ^ r * (1+|Real.log (physicalQ h w)|)^P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      physicalQ h w ≤ 1 → ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPressure x n) w‖ ≤
        C * physicalQ h w ^ r * (1+|Real.log (physicalQ h w)|)^P := by
  classical
  obtain ⟨C,hC,P,hb⟩ := choose_mode_constants hb
  let modes := ParticularWaveAssembly.modes x.coefficients.residualBand
  refine ⟨2250*∑ k ∈ modes,C k,mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)),
    ∑ k ∈ modes,P k,?_⟩
  intro n hn w hw hq
  have hq0 := physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have he := CurrentParticularLabelBounds.localPressure_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k*physicalQ h w^r*(1+|Real.log (physicalQ h w)|)^(∑ k ∈ modes,P k))
    (fun k _ => mul_nonneg (mul_nonneg (hC k) (Real.rpow_nonneg hq0.le r)) (by positivity))
    (by
      intro l hl k hk hc
      apply (hb k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq).trans
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hC k) (Real.rpow_nonneg hq0.le r))
      exact pow_le_pow_right₀ hL (Finset.single_le_sum (by intros; omega) hk))
  exact he.trans_eq (by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring)

end HarmonicSums

end NavierStokes.SharpParticularGluing
