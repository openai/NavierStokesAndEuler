import NavierStokes.SmoothPathFamily

/-! # Smooth parameter families on a convex closed domain

The parameter set need not be open. In particular, all mixed one-sided jets
at a slow-time endpoint pass to the actual continuous-path Banach space.
-/

noncomputable section

namespace NavierStokes.WithinPathFamily

open Set Filter Function Metric Asymptotics
open scoped Topology ContDiff
open SmoothPathFamily

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ}

/-- Uniform differentiability of continuous paths using only derivatives
within the convex parameter domain. -/
theorem hasFDerivWithinAt_pathFamily {U : Set P} (hU : Convex ℝ U)
    (F : P × ℝ → E) (G : P × ℝ → P →L[ℝ] E)
    (hF : ContinuousOn F (U ×ˢ Icc a b))
    (hG : ContinuousOn G (U ×ˢ Icc a b))
    (hderiv : ∀ p ∈ U, ∀ t : Icc a b,
      HasFDerivWithinAt (fun q => F (q, t)) (G (p, t)) U p)
    {p : P} (hp : p ∈ U) :
    HasFDerivWithinAt (pathFamily (a := a) (b := b) F)
      (flipPath (P := P) (E := E) (pathFamily (a := a) (b := b) G p)) U p := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply isLittleO_iff.mpr
  intro ε hε
  have hgc := continuousOn_pathFamily hG p hp
  have hsmall : ∀ᶠ q in 𝓝[U] p,
      ‖pathFamily (a := a) (b := b) G q - pathFamily G p‖ < ε := by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp hgc ε hε
  obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhdsWithin_iff.mp hsmall
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p hδ),
    self_mem_nhdsWithin] with q hq hqU
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg (q - p)))).mpr
  intro t
  simp only [ContinuousMap.sub_apply, flipPath_apply,
    pathFamily_apply F q (slice_continuous hF hqU),
    pathFamily_apply F p (slice_continuous hF hp),
    pathFamily_apply G p (slice_continuous hG hp)]
  have hd : ∀ r ∈ ball p δ ∩ U,
      HasFDerivWithinAt (fun r => F (r, t) - G (p, t) r)
        (G (r, t) - G (p, t)) (ball p δ ∩ U) r := by
    intro r hr
    exact ((hderiv r hr.2 t).sub (G (p, t)).hasFDerivAt.hasFDerivWithinAt).mono
      inter_subset_right
  have hb : ∀ r ∈ ball p δ ∩ U, ‖G (r, t) - G (p, t)‖ ≤ ε := by
    intro r hr
    calc
      _ = ‖(pathFamily G r - pathFamily G p : C(Icc a b, P →L[ℝ] E)) t‖ := by
        simp only [ContinuousMap.sub_apply,
          pathFamily_apply G r (slice_continuous hG hr.2),
          pathFamily_apply G p (slice_continuous hG hp)]
      _ ≤ ‖pathFamily (a := a) (b := b) G r - pathFamily G p‖ :=
        ContinuousMap.norm_coe_le_norm _ t
      _ ≤ ε := (hδmem hr).le
  have hh := ((convex_ball p δ).inter hU).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hd hb ⟨mem_ball_self hδ, hp⟩ ⟨hq, hqU⟩
  have he : F (q, t) - F (p, t) - G (p, t) (q - p) =
      (F (q, t) - G (p, t) q) - (F (p, t) - G (p, t) p) := by
    rw [map_sub]
    abel
  rw [he]
  exact hh

noncomputable def parameterDerivativeWithin (U : Set P) (V : Set ℝ)
    (F : P × ℝ → E) (z : P × ℝ) : P →L[ℝ] E :=
  (fderivWithin ℝ F (U ×ˢ V) z).comp (ContinuousLinearMap.inl ℝ P ℝ)

/-- Every finite order of genuine joint within regularity passes to the
path space. No extension across the parameter boundary is an assumption. -/
theorem contDiffOn_pathFamily_nat (U : Set P) (V : Set ℝ)
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U) (hv : UniqueDiffOn ℝ V)
    (hI : Icc a b ⊆ V) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : P × ℝ → W),
      ContDiffOn ℝ n F (U ×ˢ V) →
      ContDiffOn ℝ n (pathFamily (a := a) (b := b) F) U := by
  induction n with
  | zero =>
    intro W _ _ F hF
    exact contDiffOn_zero.mpr (continuousOn_pathFamily
      (hF.continuousOn.mono (prod_mono Subset.rfl hI)))
  | succ n ih =>
    intro W _ _ F hF
    have hFs : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) F (U ×ˢ V) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hF
    have hdata := (contDiffOn_succ_iff_fderivWithin (hu.prod hv)).mp hFs
    have hD : ContDiffOn ℝ n (parameterDerivativeWithin U V F) (U ×ˢ V) :=
      hdata.2.2.clm_comp contDiffOn_const
    have hd : ∀ p ∈ U, HasFDerivWithinAt (pathFamily (a := a) (b := b) F)
        (flipPath (P := P) (E := W)
          (pathFamily (a := a) (b := b) (parameterDerivativeWithin U V F) p)) U p := by
      intro p hp
      apply hasFDerivWithinAt_pathFamily hU F (parameterDerivativeWithin U V F)
        (hF.continuousOn.mono (prod_mono Subset.rfl hI))
        (hD.continuousOn.mono (prod_mono Subset.rfl hI)) _ hp
      intro q hq t
      change HasFDerivWithinAt (fun r => F (r, (t : ℝ)))
        ((fderivWithin ℝ F (U ×ˢ V) (q, t)).comp
          (ContinuousLinearMap.inl ℝ P ℝ)) U q
      exact (hdata.1 (q, (t : ℝ)) ⟨hq, hI t.2⟩).hasFDerivWithinAt.comp q
        ((hasFDerivAt_prodMk_left q (t : ℝ)).hasFDerivWithinAt (s := U))
        (show MapsTo (fun r : P => (r, (t : ℝ))) U (U ×ˢ V) from
          fun r hr => ⟨hr, hI t.2⟩)
    have hpathD := ih (parameterDerivativeWithin U V F) hD
    let L : C(Icc a b, P →L[ℝ] W) →L[ℝ] P →L[ℝ] C(Icc a b, W) :=
      flipPath (P := P) (E := W) (a := a) (b := b)
    have hL : ContDiff ℝ (n : WithTop ℕ∞) L :=
      ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := C(Icc a b, P →L[ℝ] W)) (F := P →L[ℝ] C(Icc a b, W)) L
    have hflip : ContDiffOn ℝ n
        (fun p => flipPath (P := P) (E := W) (a := a) (b := b)
          (pathFamily (a := a) (b := b) (parameterDerivativeWithin U V F) p)) U :=
      hL.comp_contDiffOn hpathD
    have hh : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (pathFamily (a := a) (b := b) F) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hu).mpr
      refine ⟨?_, _, hflip, hd⟩
      intro hω
      exact (WithTop.coe_ne_top hω).elim
    simpa only [Nat.cast_add, Nat.cast_one] using hh

theorem contDiffOn_pathFamily (U : Set P) (V : Set ℝ)
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U) (hv : UniqueDiffOn ℝ V)
    (hI : Icc a b ⊆ V) (F : P × ℝ → E)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (pathFamily (a := a) (b := b) F) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_pathFamily_nat U V hU hu hv hI n F
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))

end NavierStokes.WithinPathFamily
