import NavierStokes.CommonCoverWithin
import NavierStokes.ParticularWaveBounds

/-! # One-sided jets of the actual particular velocity and pressure -/

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Filter Function
open scoped ContDiff Topology InnerProductSpace
open CommonCoverSolve TorusInverse

section Real

variable {P H : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem tangent_coefficients_contDiffOn {S : Set (P × Plane)} (t : TangentData P H)
    (hN : ContDiffOn ℝ ∞ t.normal S) (hNd : ContDiffOn ℝ ∞ t.normalDot S)
    (hK : ContDiffOn ℝ ∞ t.action S) (hδ : ContDiffOn ℝ ∞ t.damping S)
    (hn : ∀ x ∈ S, t.normal x ≠ 0) :
    ContDiffOn ℝ ∞ t.linearData.coefficient S ∧
      ContDiffOn ℝ ∞ t.linearData.forcingMap S := by
  have hden := (hN.inner ℝ hN).inv (fun x hx => inner_self_ne_zero.mpr (hn x hx))
  have hi := (innerSL ℝ).contDiff.comp_contDiffOn hN
  have hid := (innerSL ℝ).contDiff.comp_contDiffOn hNd
  constructor
  · exact (hK.neg.add (((hi.clm_comp hK).sub hid).smulRight (hden.smul hN))).sub
      (hδ.smul contDiffOn_const)
  · exact (contDiffOn_const.sub (hi.smulRight (hden.smul hN))).neg

theorem copyPressure_contDiffOn_within (t : TangentData P H) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (hN : ContDiffOn ℝ ∞ t.normal (U ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (U ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (U ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ t.source (U ×ˢ univ))
    (hn : ∀ x ∈ U ×ˢ univ, t.normal x ≠ 0) (k : Frequency) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (copyPressure t g hab k frequency)
      {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b} := by
  let D := {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b}
  have hmap : MapsTo (nativePoint (P := P) g k) D (U ×ˢ univ) :=
    fun _ hx => ⟨hx.1, mem_univ _⟩
  have hnativ : ContDiff ℝ ∞ (nativePoint (P := P) g k) :=
    contDiff_fst.prodMk ((g.coordinates_contDiff k).comp contDiff_snd)
  have hNc := hN.comp hnativ.contDiffOn hmap
  have hNdc := hNd.comp hnativ.contDiffOn hmap
  have hKc := hK.comp hnativ.contDiffOn hmap
  have hfc := hf.mono (show D ⊆ U ×ˢ univ from fun _ hx => ⟨hx.1, mem_univ _⟩)
  obtain ⟨hA, hB⟩ := tangent_coefficients_contDiffOn t hN hNd hK hδ hn
  have hv := t.linearData.copySolve_contDiffOn_closed_within g hab hU hu hA hB hf k
  have hreal : ContDiffOn ℝ ∞ (copyPressureReal t g hab k) D :=
    (((hNc.inner ℝ (hKc.clm_apply hv)).sub (hNdc.inner ℝ hv)).add (hNc.inner ℝ hfc)).div
      (hNc.inner ℝ hNc) (fun x hx => inner_self_ne_zero.mpr (hn _ (hmap hx)))
  have hcomplex := Complex.ofRealCLM.contDiff.comp_contDiffOn hreal
  exact (contDiffOn_const.mul hcomplex).div_const _

end Real

section Complex

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem complexCopy_contDiffOn_within (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (hN : ContDiffOn ℝ ∞ t.normal (U ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (U ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (U ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hn : ∀ x ∈ U ×ˢ univ, t.normal x ≠ 0) (k : Frequency) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (complexCopyVelocity t f g hab k)
        {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b} ∧
      ContDiffOn ℝ ∞ (complexCopyPressure t f g hab k frequency)
        {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b} := by
  have hr : ContDiffOn ℝ ∞ (realData t f).source (U ×ˢ univ) :=
    realPart.contDiff.comp_contDiffOn hf
  have hi : ContDiffOn ℝ ∞ (imagData t f).source (U ×ˢ univ) :=
    imagPart.contDiff.comp_contDiffOn hf
  obtain ⟨hA, hB⟩ := tangent_coefficients_contDiffOn t hN hNd hK hδ hn
  have hrv := (realData t f).linearData.copySolve_contDiffOn_closed_within g hab hU hu hA hB hr k
  have hiv := (imagData t f).linearData.copySolve_contDiffOn_closed_within g hab hU hu hA hB hi k
  have hrp := copyPressure_contDiffOn_within (realData t f) g hab hU hu hN hNd hK hδ hr hn k frequency
  have hip := copyPressure_contDiffOn_within (imagData t f) g hab hU hu hN hNd hK hδ hi hn k frequency
  constructor
  · have hv := (CurlClassBounds.complexify.contDiff.comp_contDiffOn hrv).add
      ((contDiffOn_const (c := Complex.I)).smul
        (CurlClassBounds.complexify.contDiff.comp_contDiffOn hiv))
    exact hv
  · exact hrp.add (contDiffOn_const.mul hip)

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem periodizedCopies_contDiffOn_within (g : Geometry)
    {a b : ℝ} {U : Set P} {κ : Plane → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b)
    (F : Frequency → P × Plane → H)
    (hF : ∀ k, ContDiffOn ℝ ∞ (F k)
      {p : P × Plane | p.1 ∈ U ∧ (g.coordinates k p.2).2 ∈ Icc a b}) :
    ContDiffOn ℝ ∞ (periodizedCopies g κ F) (U ×ˢ univ) := by
  have hterm (k : Frequency) : ContDiffOn ℝ ∞
      (fun p : P × Plane => κ (g.coordinates k p.2) • F k p) (U ×ˢ univ) := by
    intro p hp
    have hc : ContDiff ℝ ∞ (fun q : P × Plane => g.coordinates k q.2) :=
      (g.coordinates_contDiff k).comp contDiff_snd
    by_cases hz : g.coordinates k p.2 ∈ tsupport κ
    · have hη := (hsupp hz).2
      have hnear : {q : P × Plane | q.1 ∈ U ∧ (g.coordinates k q.2).2 ∈ Icc a b}
          ∈ 𝓝[U ×ˢ univ] p := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hc.snd.continuous.tendsto p |>.eventually
            (isOpen_Ioo.mem_nhds hη))] with q hq hηq
        exact ⟨hq.1, Ioo_subset_Icc_self hηq⟩
      exact (hκ.comp hc).contDiffAt.contDiffWithinAt.smul
        ((hF k p ⟨hp.1, Ioo_subset_Icc_self hη⟩).mono_of_mem_nhdsWithin hnear)
    · have hzero : (fun q : P × Plane => κ (g.coordinates k q.2) • F k q)
          =ᶠ[𝓝 p] fun _ => (0 : H) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
          hc.continuous.continuousAt] with q hq
        change κ (g.coordinates k q.2) = 0 at hq
        rw [hq, zero_smul]
      exact contDiffWithinAt_const.congr_of_eventuallyEq
        (hzero.filter_mono nhdsWithin_le_nhds) hzero.self_of_nhds
  intro p hp
  obtain ⟨I, hI⟩ := g.finite_copy_cutoffs hcκ (‖p.2‖ + 1)
  have he : periodizedCopies g κ F =ᶠ[𝓝 p]
      fun q => ∑ k ∈ I, κ (g.coordinates k q.2) • F k q := by
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_const).mem_nhds
      (show ‖p.2‖ < ‖p.2‖ + 1 by linarith)] with q hq
    apply tsum_eq_sum
    intro k hk
    rw [hI q.2 hq.le k hk, zero_smul]
  exact (ContDiffWithinAt.sum (fun k _ => hterm k p hp)).congr_of_eventuallyEq
    (he.filter_mono nhdsWithin_le_nhds) he.self_of_nhds

/-- The actual common-torus velocity and pressure inherit all mixed
one-sided slow derivatives from the primitive geometry and source. -/
theorem commonCoefficients_contDiffOn_within (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {U : Set P} (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (hN : ContDiffOn ℝ ∞ t.normal (U ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (U ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (U ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (U ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ))
    (hn : ∀ x ∈ U ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (commonVelocity t f g hab κ) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (commonPressure t f g hab κ frequency) (U ×ˢ univ) :=
  ⟨periodizedCopies_contDiffOn_within g hκ hcκ hsupp _ (fun k =>
      (complexCopy_contDiffOn_within t f g hab hU hu hN hNd hK hδ hf hn k frequency).1),
    periodizedCopies_contDiffOn_within g hκ hcκ hsupp _ (fun k =>
      (complexCopy_contDiffOn_within t f g hab hU hu hN hNd hK hδ hf hn k frequency).2)⟩

end Complex

end NavierStokes.ParticularWaveBounds
