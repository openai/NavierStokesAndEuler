import NavierStokes.JointResidualLimits
import NavierStokes.LocalScaleGeometry
import NavierStokes.AnnularEndpoint
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform local jet bounds up to the terminal slice

Actual smooth extensions at each nonsingular terminal point provide compatible
limits of every derivative. Compactness turns those local bounds into one bound
on any compact spacetime set avoiding the singular point.
-/

noncomputable section

open Set Filter Bornology
open scoped Topology ContDiff

namespace NavierStokes.LocalJetBounds

open ProblemStatement
open JointResidualLimits (AwayExtensions)

/-- A limit at each point of a compact set bounds the function on the
approaching part of that set. The boundary values need not have been assigned
to the original function. -/
theorem isBounded_image_of_compact_limits {X V : Type*} [TopologicalSpace X]
    [PseudoMetricSpace V] {K S : Set X} {f : X → V} (hK : IsCompact K)
    (hf : ∀ x ∈ K, ∃ y : V, Tendsto f (𝓝[S] x) (𝓝 y)) :
    IsBounded (f '' (K ∩ S)) := by
  have hd : Disjoint (𝓝ˢ K ⊓ 𝓟 S) (comap f (cobounded V)) := by
    rw [disjoint_assoc, inf_comm, hK.disjoint_nhdsSet_left]
    intro x hx
    obtain ⟨y, hy⟩ := hf x hx
    exact disjoint_left_comm.2 <|
      tendsto_comap.disjoint (Metric.disjoint_cobounded_nhds y) hy
  obtain ⟨U, ⟨hUo, hKU⟩, t, ht, hUt⟩ :=
    ((((hasBasis_nhdsSet K).inf_principal S)).disjoint_iff
      ((basis_sets _).comap f)).1 hd
  have hb : IsBounded (f '' (U ∩ S)) := by
    apply (isBounded_compl_iff.2 ht).subset
    rwa [image_subset_iff, preimage_compl, subset_compl_iff_disjoint_right]
  exact hb.subset (image_mono (inter_subset_inter_left S hKU))

/-- Smoothness in the past and actual one-sided extensions give every
derivative a finite limit at each nonsingular point of the closed past. -/
theorem jet_has_limit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {w : SpaceTime} (ht : w.1 ≤ 1)
    (hw : w ≠ (1, (0 : Space))) (n : ℕ) :
    ∃ L, Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] w) (𝓝 L) := by
  by_cases hp : w.1 < 1
  · have hc := hf.contDiffAt ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds
      (show w ∈ SpacetimeEndpoint.openPast 1 from ⟨hp, mem_univ _⟩))
    have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ n f) w :=
      hc.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (n : ℕ∞) ≤ ⊤))
    exact ⟨_, hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  · have ht1 : w.1 = 1 := le_antisymm ht (le_of_not_gt hp)
    have hx : w.2 ≠ 0 := by
      intro hx
      exact hw (Prod.ext ht1 hx)
    obtain ⟨e⟩ := he w.2 hx
    have hw1 : w = (1, w.2) := Prod.ext ht1 rfl
    rw [hw1]
    exact ⟨_, e.jet_tendsto n⟩

/-- Uniform bounds for every Cartesian derivative on compact subsets of the
closed past that avoid the singular point, including approach from `t < 1`. -/
theorem uniform_jets_on_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {K : Set SpaceTime} (hK : IsCompact K)
    (hKt : ∀ w ∈ K, w.1 ≤ 1) (hK0 : (1, (0 : Space)) ∉ K) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, w.1 < 1 → ‖iteratedFDeriv ℝ n f w‖ ≤ C := by
  have hb := isBounded_image_of_compact_limits hK (fun w hw =>
    jet_has_limit hf he (hKt w hw) (fun heq => hK0 (heq ▸ hw)) n)
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos_norm_le
  exact ⟨C, hC, fun w hw ht => hbound _ ⟨w, ⟨hw, ht, mem_univ _⟩, rfl⟩⟩

/-- The exact compact-spatial, positive-scale-strip bounds of the local
theorem. The bound remains valid as the terminal slice is approached. -/
theorem uniform_jets_on_scale_strip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (he : AwayExtensions f) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {K : Set Space} (hK : IsCompact K) {c c' : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : SpaceTime, w.1 < 1 → w.2 ∈ K →
      c ≤ PhysicalWaveSum.physicalQ h w → PhysicalWaveSum.physicalQ h w ≤ c' →
      ‖iteratedFDeriv ℝ n f w‖ ≤ C := by
  let S : Set SpaceTime := {w | w.1 < 1 ∧ w.2 ∈ K ∧
    c ≤ PhysicalWaveSum.physicalQ h w ∧ PhysicalWaveSum.physicalQ h w ≤ c'}
  have hsub : S ⊆ Icc (1 - c') 1 ×ˢ K := by
    intro w hw
    have ht := LocalScaleGeometry.time_dist_le hh hh1 hw.1
    rw [abs_of_neg (sub_neg.mpr hw.1)] at ht
    exact ⟨⟨by linarith [hw.2.2.2], hw.1.le⟩, hw.2.1⟩
  have hclosedSub : closure S ⊆ Icc (1 - c') 1 ×ˢ K :=
    closure_minimal hsub (isClosed_Icc.prod hK.isClosed)
  have hcompact : IsCompact (closure S) :=
    (isCompact_Icc.prod hK).of_isClosed_subset isClosed_closure hclosedSub
  have hzero : (1, (0 : Space)) ∉ closure S := by
    have hq := (AnnularEndpoint.physicalQ_tendsto_zero hh hh1
      (x := (0 : Space)) rfl).eventually (gt_mem_nhds hc)
    obtain ⟨U, hU, hUp⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hq
    intro hcl
    obtain ⟨w, hw, hs⟩ := mem_closure_iff_nhds.mp hcl U hU
    have hlt := hUp ⟨hw, hs.1, mem_univ _⟩
    exact (not_lt_of_ge hs.2.2.1) hlt
  obtain ⟨C, hC, hb⟩ := uniform_jets_on_compact hf he hcompact
    (fun w hw => (hclosedSub hw).1.2) hzero n
  exact ⟨C, hC, fun w ht hx hlow hhigh =>
    hb w (subset_closure ⟨ht, hx, hlow, hhigh⟩) ht⟩

end NavierStokes.LocalJetBounds
