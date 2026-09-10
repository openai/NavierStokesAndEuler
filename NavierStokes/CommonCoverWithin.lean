import NavierStokes.WithinJointODE
import NavierStokes.CommonCoverSolve
import NavierStokes.CommonCoverClass

/-! # Common-torus inverse at a one-sided slow endpoint

All inputs have genuine joint within regularity on the slow domain. The
actual copy and common-torus solves inherit it; an open continuation of the
source is not required.
-/

noncomputable section

namespace NavierStokes.CommonCoverSolve.LinearData

open Set Filter Function
open scoped Topology ContDiff
open TorusInverse

variable {P V E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (d : LinearData P V E) (g : Geometry) (hab : a ≤ b)
  {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
  (hA : ContDiffOn ℝ ∞ d.coefficient (U ×ˢ univ))
  (hB : ContDiffOn ℝ ∞ d.forcingMap (U ×ˢ univ))
  (hf : ContDiffOn ℝ ∞ d.source (U ×ˢ univ))

include hU hu hA hB hf

/-- The original anchored Volterra solve is smooth within the closed slow
domain and the entire closed pulse interval, including their corners. -/
theorem anchoredSolve_contDiffOn_within (k : Frequency) :
    ContDiffOn ℝ ∞ (fun z : (P × Plane) × ℝ => d.anchoredSolve g hab k z.1 z.2)
      ((U ×ˢ univ) ×ˢ Icc a b) :=
  WithinJointODE.contDiffOn_actualSolution hab (hU.prod convex_univ)
    (hu.prod uniqueDiffOn_univ) (d.coefficientAlong g k) (fun _ => 0)
    (d.forcingAlong g k) (d.coefficientAlong_contDiffOn g k hA) contDiffOn_const
    (d.forcingAlong_contDiffOn g k hB hf)

/-- The current copy argument with the unclamped endpoint-rescaled solve. -/
noncomputable def copySolveRepresentative (k : Frequency) (p : P × Plane) : E :=
  JointODE.reparamSolution a (d.coefficientAlong g k) (fun _ => 0)
    (d.forcingAlong g k) (p, (g.coordinates k p.2).2)

theorem copySolveRepresentative_contDiffOn (k : Frequency) :
    ContDiffOn ℝ ∞ (d.copySolveRepresentative g (a := a) k) (U ×ˢ univ) := by
  have hh := WithinJointODE.contDiffOn_reparamSolution (a := a)
    (hU.prod convex_univ) (hu.prod uniqueDiffOn_univ) (d.coefficientAlong g k)
    (fun _ => 0) (d.forcingAlong g k) (d.coefficientAlong_contDiffOn g k hA)
    contDiffOn_const (d.forcingAlong_contDiffOn g k hB hf)
  exact hh.comp (CommonCoverClass.currentArgument_smooth (P := P) g k).contDiffOn
    (fun _ hz => ⟨hz, mem_univ _⟩)

omit hU hu hA hB hf in
theorem copySolveRepresentative_eq (k : Frequency)
    (hA : ContinuousOn d.coefficient (U ×ˢ univ))
    (hB : ContinuousOn d.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn d.source (U ×ˢ univ))
    {p : P × Plane} (hp : p.1 ∈ U)
    (ht : (g.coordinates k p.2).2 ∈ Icc a b) :
    d.copySolveRepresentative g (a := a) k p = d.copySolve g hab k p :=
  JointODE.reparamSolution_eq_actualSolution hab _ _ _
    ((d.coefficientAlong_continuousOn g k hA).mono (prod_mono Subset.rfl (subset_univ _)))
    ((d.forcingAlong_continuousOn g k hB hf).mono (prod_mono Subset.rfl (subset_univ _)))
    ⟨⟨hp, mem_univ _⟩, ht⟩

theorem copySolve_contDiffOn_closed_within (k : Frequency) :
    ContDiffOn ℝ ∞ (d.copySolve g hab k)
      {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b} := by
  apply ((d.copySolveRepresentative_contDiffOn g hU hu hA hB hf k (a := a)).mono
    (fun p hp => ⟨hp.1, mem_univ _⟩)).congr
  intro p hp
  exact (d.copySolveRepresentative_eq g hab k hA.continuousOn hB.continuousOn hf.continuousOn
    hp.1 hp.2).symm

theorem copySolve_contDiffOn_current_within (k : Frequency)
    {D : Set (P × Plane)} (hDU : ∀ p ∈ D, p.1 ∈ U)
    (hslot : ∀ p ∈ D, (g.coordinates k p.2).2 ∈ Icc a b) :
    ContDiffOn ℝ ∞ (d.copySolve g hab k) D :=
  (d.copySolve_contDiffOn_closed_within g hab hU hu hA hB hf k).mono
    (fun p hp => ⟨hDU p hp, hslot p hp⟩)

/-- Multiplication by the original pulse cutoff identifies the smooth
representative with the actual localized inverse everywhere in the slow
domain. This leaves the original construction unchanged. -/
theorem localizedCopy_contDiffOn_within (k : Frequency)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) :
    ContDiffOn ℝ ∞ (d.localizedCopy g hab κ k) (U ×ˢ univ) := by
  have hc : ContDiffOn ℝ ∞ (fun p : P × Plane => κ (g.coordinates k p.2))
      (U ×ˢ univ) := (hκ.comp ((g.coordinates_contDiff k).comp contDiff_snd)).contDiffOn
  have hh := hc.smul (d.copySolveRepresentative_contDiffOn g hU hu hA hB hf k (a := a))
  apply hh.congr
  intro p hp
  change κ (g.coordinates k p.2) • d.copySolve g hab k p =
    κ (g.coordinates k p.2) • d.copySolveRepresentative g (a := a) k p
  by_cases hz : κ (g.coordinates k p.2) = 0
  · simp only [hz, zero_smul]
  · rw [d.copySolveRepresentative_eq g hab k hA.continuousOn hB.continuousOn hf.continuousOn
      hp.1 (Ioo_subset_Icc_self (hsupp (subset_tsupport κ hz)).2)]

/-- The actual locally finite common-torus sum has all one-sided slow jets.
The source need only descend to the common torus; no band descent is added. -/
theorem commonSolve_contDiffOn_within
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) :
    ContDiffOn ℝ ∞ (d.commonSolve g hab κ) (U ×ˢ univ) := by
  intro p hp
  obtain ⟨s, hs⟩ := d.commonSolve_eventually_eq_sum g hab hcκ p
  have hsum : ContDiffWithinAt ℝ ∞ (fun q => ∑ k ∈ s, d.localizedCopy g hab κ k q)
      (U ×ˢ univ) p := ContDiffWithinAt.sum (fun k _ =>
    d.localizedCopy_contDiffOn_within g hab hU hu hA hB hf k hκ hsupp p hp)
  exact hsum.congr_of_eventuallyEq (hs.filter_mono nhdsWithin_le_nhds) hs.self_of_nhds

theorem commonSolve_boundary_jet_limit
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b)
    {O : Set P} (hO : IsOpen O) (hOU : O ⊆ U)
    (n : ℕ) {p : P × Plane} (hp : p.1 ∈ U) :
    Tendsto (iteratedFDeriv ℝ n (d.commonSolve g hab κ)) (𝓝[O ×ˢ univ] p)
      (𝓝 (iteratedFDerivWithin ℝ n (d.commonSolve g hab κ) (U ×ˢ univ) p)) :=
  WithinJetClosure.tendsto_iteratedFDeriv (hu.prod uniqueDiffOn_univ)
    (hO.prod isOpen_univ) (Set.prod_mono hOU Subset.rfl)
    (d.commonSolve_contDiffOn_within g hab hU hu hA hB hf hκ hcκ hsupp) n ⟨hp, mem_univ _⟩

end NavierStokes.CommonCoverSolve.LinearData
