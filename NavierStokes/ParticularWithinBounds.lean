import NavierStokes.WithinJointODE
import NavierStokes.ParticularWaveBounds

/-! # The particular inverse estimate at closed slow and pulse endpoints -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter
open scoped ContDiff Topology InnerProductSpace
open PrimaryPulseBounds

variable {Q H : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The same explicit forced bound for genuine within jets, at slow-time
boundaries and at both pulse endpoints. Input estimates are required only
in the interior slow domain. Their constants survive passage to the trace.
-/
theorem forced_joint_jet_bound_within
    {L S K μ w : ℝ} (hL : 0 < L) (hS : 1 ≤ S) (hK : 1 ≤ K) (hμ : 0 ≤ μ)
    (hw : 0 ≤ w) (hslot : L ≤ K * S) (hExp : Real.exp (μ * L) ≤ K)
    {U : Set Q} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (A : Q × ℝ → H →L[ℝ] H) (hA : ContDiffOn ℝ ∞ A (U ×ˢ univ))
    (P rate : ℝ → ℝ) (hP : ∀ t, 0 < P t)
    (hdP : ∀ t, HasDerivAt P (rate t * P t) t)
    (f : Q × ℝ → H) (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    {p : Q} (hp : p ∈ U) (hpc : p ∈ closure (interior U))
    {t : ℝ} (ht : t ∈ Icc 0 L)
    (henergy : ∀ q ∈ interior U, ∀ v ∈ Icc 0 L, ∀ x : H,
      ⟪x, A (q, v) x⟫_ℝ ≤ (rate v + μ) * ‖x‖ ^ 2)
    (m N : ℕ)
    (hjets : ∀ q ∈ interior U, ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j A (q, v)‖ ≤ K * S ^ m)
    (hfjets : ∀ q ∈ interior U, ∀ j ≤ N, ∀ v ∈ Icc 0 L,
      ‖iteratedFDeriv ℝ j f (q, v)‖ ≤ w * K * S ^ m * P v)
    (j : ℕ) (hj : j ≤ N) :
    ‖iteratedFDerivWithin ℝ j
      (JointODE.actualSolution hL.le A (fun _ => 0) f) (U ×ˢ Icc 0 L) (p, t)‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (j + 1) *
        S ^ ((m + 2) * (j + 1)) * P t := by
  let r := JointODE.reparamSolution 0 A (fun _ => 0) f
  have hrs : ContDiffOn ℝ ∞ r (U ×ˢ univ) :=
    WithinJointODE.contDiffOn_reparamSolution hU hu A (fun _ => 0) f hA contDiffOn_const hf
  have heq : EqOn r (JointODE.actualSolution hL.le A (fun _ => 0) f) (U ×ˢ Icc 0 L) := by
    intro z hz
    exact JointODE.reparamSolution_eq_actualSolution hL.le A (fun _ => 0) f
      (hA.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _)))
      (hf.continuousOn.mono (Set.prod_mono Subset.rfl (subset_univ _))) hz
  rw [← iteratedFDerivWithin_congr heq ⟨hp, ht⟩ j,
    iteratedFDerivWithin_subset (Set.prod_mono Subset.rfl (subset_univ _))
      (hu.prod (uniqueDiffOn_Icc hL)) (hu.prod uniqueDiffOn_univ)
      (hrs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)) ⟨hp, ht⟩]
  let B : Q × ℝ → ℝ := fun z =>
    w * ((2 : ℝ) ^ (N + 1) * rescaleConstant N K ^ 3) ^ (j + 1) *
      S ^ ((m + 2) * (j + 1)) * P z.2
  have hPc : Continuous P := continuous_iff_continuousAt.mpr (fun x => (hdP x).continuousAt)
  refine WithinJetClosure.norm_iteratedFDerivWithin_le
    (O := interior U ×ˢ Ioo (0 : ℝ) L) (hu.prod uniqueDiffOn_univ)
    (isOpen_interior.prod isOpen_Ioo) (Set.prod_mono interior_subset (subset_univ _)) hrs
    (B := B) (continuous_const.mul (hPc.comp continuous_snd)).continuousOn j ?_
    ⟨hp, mem_univ _⟩ ?_
  · intro z hz
    exact forced_joint_jet_bound hL hS hK hμ hw hslot hExp
      (interior U) univ isOpen_interior isOpen_univ (subset_univ _) A
      (hA.mono (Set.prod_mono interior_subset Subset.rfl)) P rate hP hdP f
      (hf.mono (Set.prod_mono interior_subset Subset.rfl)) hz.1 (Ioo_subset_Icc_self hz.2)
      (henergy z.1 hz.1) m N (hjets z.1 hz.1) (hfjets z.1 hz.1) j hj
  · rw [closure_prod_eq, closure_Ioo hL.ne]
    exact ⟨hpc, ht⟩

end NavierStokes.ParticularWaveBounds
