import NavierStokes.R3.ProblemStatement

/-!
# Compact support under spatial rescaling

A nonzero spatial dilation leaves time unchanged, so it preserves compact
support contained in positive time. The same inverse image of a compact spatial
set contains the supports of all rescaled time slices.
-/

noncomputable section

open Set

namespace NavierStokesR3.ProblemStatement

/-- A continuous spatial dilation maps compact sets to compact sets. -/
theorem isCompact_spatialScale_image {K : Set Space} (hK : IsCompact K) (b : ℝ) :
    IsCompact ((fun x : Space => b⁻¹ • x) '' K) :=
  hK.image (continuous_id.const_smul b⁻¹)

/-- A fixed inverse dilation contains the support of a rescaled spatial slice,
with no assumption on the amplitude. -/
theorem tsupport_spatialScale_subset {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    {f : Space → V} {K : Set Space} (hf : tsupport f ⊆ K)
    (a b : ℝ) (hb : b ≠ 0) :
    tsupport (fun x : Space => a • f (b • x)) ⊆
      (fun x : Space => b⁻¹ • x) '' K := by
  intro x hx
  have hscaled : b • x ∈ tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.const_smul b)
      (tsupport_smul_subset_right (fun _ : Space => a) (fun x => f (b • x)) hx)
  exact ⟨b • x, hf hscaled, by simp [smul_smul, hb]⟩

/-- The inverse dilation of a spacetime compact set is compact. -/
theorem isCompact_spacetimeSpatialScale_image {K : Set SpaceTime}
    (hK : IsCompact K) (b : ℝ) :
    IsCompact ((fun z : SpaceTime => (z.1, b⁻¹ • z.2)) '' K) :=
  hK.image (continuous_fst.prodMk (continuous_snd.const_smul b⁻¹))

/-- Spatial scaling and amplitude scaling preserve compact force support in
strictly positive time. -/
theorem CompactPositiveTimeSupport.spatialScale {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) (a b : ℝ) (hb : b ≠ 0) :
    CompactPositiveTimeSupport (fun z : SpaceTime => a • f (z.1, b • z.2)) := by
  have hsub : tsupport (fun z : SpaceTime => a • f (z.1, b • z.2)) ⊆
      (fun z : SpaceTime => (z.1, b⁻¹ • z.2)) '' tsupport f := by
    intro z hz
    have hz' : (z.1, b • z.2) ∈ tsupport f :=
      tsupport_comp_subset_preimage f
        (continuous_fst.prodMk (continuous_snd.const_smul b))
        (tsupport_smul_subset_right (fun _ : SpaceTime => a)
          (fun z => f (z.1, b • z.2)) hz)
    exact ⟨(z.1, b • z.2), hz', by simp [smul_smul, hb]⟩
  constructor
  · exact (isCompact_spacetimeSpatialScale_image hf.1 b).of_isClosed_subset
      (isClosed_tsupport _) hsub
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hsub hz
    exact ⟨(hf.2 hw).1, mem_univ _⟩

end NavierStokesR3.ProblemStatement
