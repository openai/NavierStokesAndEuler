import NavierStokes.PhysicalStageBounds

noncomputable section

namespace NavierStokes.SharpGluedStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum
open scoped Topology ContDiff BigOperators

/-- A power-log bound on every point of a fixed physical sublevel. -/
def LogBound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h qbig : ℝ) (f : SpaceTime → V) (m : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    physicalQ h w ≤ 1 → ‖iteratedFDeriv ℝ m f w‖ ≤
      C * physicalQ h w ^ r * (1 + |Real.log (physicalQ h w)|)^N

section Algebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig r s : ℝ} {f g : SpaceTime → V} {m : ℕ}

theorem LogBound.of_bound
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      physicalQ h w ≤ 1 → ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ r) :
    LogBound h qbig f m r := by
  obtain ⟨C,hC,hb⟩ := hf
  exact ⟨C,hC,0,fun w hw hq => by simpa only [pow_zero,mul_one] using hb w hw hq⟩

theorem LogBound.mono_domain {qsmall : ℝ} (hf : LogBound h qbig f m r)
    (hq : qsmall ≤ qbig) : LogBound h qsmall f m r := by
  obtain ⟨C,hC,N,hb⟩ := hf
  exact ⟨C,hC,N,fun w hw hqw => hb w ⟨hw.1,hw.2.trans_le hq⟩ hqw⟩

theorem LogBound.weaken (hf : LogBound h qbig f m r)
    (hh : 0 < h) (hh1 : h < 1/2) (hs : s ≤ r) : LogBound h qbig f m s := by
  obtain ⟨C,hC,N,hb⟩ := hf
  refine ⟨C,hC,N,fun w hw hq => (hb w hw hq).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos hh hh1 hw.1) hq hs) hC) (by positivity)

theorem LogBound.add (hf : LogBound h qbig f m r) (hg : LogBound h qbig g m r)
    (hh : 0 < h) (hh1 : h < 1/2)
    (sf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (sg : ContDiffOn ℝ ∞ g (CutStageEstimates.physicalSublevel h qbig)) :
    LogBound h qbig (fun w => f w + g w) m r := by
  obtain ⟨C,hC,N,hf⟩ := hf
  obtain ⟨D,hD,M,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,N+M,?_⟩
  intro w hw hq
  have hq0 := physicalQ_pos hh hh1 hw.1
  have hL : 1 ≤ 1+|Real.log (physicalQ h w)| := by linarith [abs_nonneg (Real.log (physicalQ h w))]
  have hf' := (hf w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (Nat.le_add_right N M)) (mul_nonneg hC (Real.rpow_nonneg hq0.le r)))
  have hg' := (hg w hw hq).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (Nat.le_add_left M N)) (mul_nonneg hD (Real.rpow_nonneg hq0.le r)))
  exact (ResidualStability.norm_jet_add_le
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) sf sg hw m).trans
      ((add_le_add hf' hg').trans_eq (by ring))

theorem LogBound.congr (hf : LogBound h qbig f m r)
    (hh : 0 < h) (hh1 : h < 1/2)
    (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig)) : LogBound h qbig g m r := by
  obtain ⟨C,hC,N,hb⟩ := hf
  refine ⟨C,hC,N,?_⟩
  intro w hw hq
  rw [← ResidualStability.iteratedFDeriv_eqOn
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) he m hw]
  exact hb w hw hq

end Algebra

section Sums

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig r : ℝ} {m : ℕ}

theorem LogBound.zero : LogBound h qbig (fun _ : SpaceTime => (0 : V)) m r := by
  refine ⟨0,le_rfl,0,?_⟩
  intro w hw hq
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_mul, le_refl]

theorem LogBound.finset_sum {ι : Type*} (s : Finset ι) {f : ι → SpaceTime → V}
    (hh : 0 < h) (hh1 : h < 1/2)
    (hs : ∀ i ∈ s, ContDiffOn ℝ ∞ (f i) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ i ∈ s, LogBound h qbig (f i) m r) :
    LogBound h qbig (fun w => ∑ i ∈ s, f i w) m r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (LogBound.zero (h := h) (qbig := qbig) (m := m) (r := r) (V := V))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply (hb i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
        (fun j hj => hb j (Finset.mem_insert_of_mem hj))) hh hh1
      (hs i (Finset.mem_insert_self i s))
    exact ContDiffOn.sum (fun j hj => hs j (Finset.mem_insert_of_mem hj))

end Sums

theorem LogBound.spatialCurl {h qbig r : ℝ} {m : ℕ} {f : VelocityField}
    (hf : LogBound h qbig f (m+1) r) (hh : 0 < h) (hh1 : h < 1/2)
    (hs : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig)) :
    LogBound h qbig (SpatialCurl.spatialCurl f) m r := by
  obtain ⟨C,hC,N,hb⟩ := hf
  refine ⟨‖PhysicalClassBounds.jointCurl‖*C,mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC,N,?_⟩
  intro w hw hq
  exact (PhysicalClassBounds.spatialCurl_jet_bound
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) hs hw m).trans
    ((mul_le_mul_of_nonneg_left (hb w hw hq) (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

end NavierStokes.SharpGluedStageBounds
