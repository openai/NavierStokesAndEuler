import NavierStokes.R3.SpatialSupportScaling

/-!
# Support after affine time and spatial rescaling

Positive affine time slopes and nonpositive time offsets preserve the force
class. A sufficiently large spatial dilation puts any compact spatial support
inside the central coordinate cube.
-/

noncomputable section

open Set

namespace NavierStokesR3.ProblemStatement

/-- The inverse affine spacetime transform maps compact sets to compact sets. -/
theorem isCompact_affineSpacetime_image {K : Set SpaceTime} (hK : IsCompact K)
    (b c d : ℝ) :
    IsCompact ((fun z : SpaceTime => ((z.1 - d) / c, b⁻¹ • z.2)) '' K) := by
  exact hK.image (((continuous_fst.sub continuous_const).div_const c).prodMk
    (continuous_snd.const_smul b⁻¹))

/-- Affine pullback with a positive time slope and a nonpositive offset
preserves compact support in strictly positive time. -/
theorem CompactPositiveTimeSupport.affineScale {f : VelocityField}
    (hf : CompactPositiveTimeSupport f) (a b c d : ℝ) (hb : b ≠ 0)
    (hc : 0 < c) (hd : d ≤ 0) :
    CompactPositiveTimeSupport
      (fun z : SpaceTime => a • f (c * z.1 + d, b • z.2)) := by
  have hsub : tsupport (fun z : SpaceTime => a • f (c * z.1 + d, b • z.2)) ⊆
      (fun z : SpaceTime => ((z.1 - d) / c, b⁻¹ • z.2)) '' tsupport f := by
    intro z hz
    have hz' : (c * z.1 + d, b • z.2) ∈ tsupport f :=
      tsupport_comp_subset_preimage f
        (((continuous_fst.const_mul c).add continuous_const).prodMk
          (continuous_snd.const_smul b))
        (tsupport_smul_subset_right (fun _ : SpaceTime => a)
          (fun z => f (c * z.1 + d, b • z.2)) hz)
    refine ⟨(c * z.1 + d, b • z.2), hz', ?_⟩
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · simp [smul_smul, hb]
  constructor
  · exact (isCompact_affineSpacetime_image hf.1 b c d).of_isClosed_subset
      (isClosed_tsupport _) hsub
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hsub hz
    refine ⟨div_pos (sub_pos.mpr ?_) hc, mem_univ _⟩
    exact hd.trans_lt (hf.2 hw).1

/-- Every compact spatial set can be put in the central quarter cube by an
inverse dilation whose factor is greater than one. -/
theorem exists_spatialScale_into_quarterCube {K : Set Space} (hK : IsCompact K) :
    ∃ b : ℝ, 1 < b ∧ ∀ x ∈ (fun y : Space => b⁻¹ • y) '' K,
      ∀ i : Fin 3, |x i| ≤ (1 / 4 : ℝ) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨4 * R + 2, by linarith, ?_⟩
  rintro x ⟨y, hy, rfl⟩ i
  have hb : 0 < 4 * R + 2 := by linarith
  have hyi : |y i| ≤ R := (PiLp.norm_apply_le y i).trans (hbound y hy)
  change |(4 * R + 2)⁻¹ * y i| ≤ _
  rw [abs_mul, abs_of_pos (inv_pos.mpr hb)]
  have hdiv : |y i| / (4 * R + 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hb).mpr
    linarith
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

end NavierStokesR3.ProblemStatement
