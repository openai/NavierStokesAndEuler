import NavierStokes.R3.H3WeakEmbedding
import NavierStokes.R3.CompactTimeIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # L² time differentiation for compact smooth fields

Pointwise time differentiation passes to the actual L² space by dominated
convergence of the squared slope error. A compact uniform derivative bound
supplies the domination through the mean value theorem.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement

theorem lp_norm_sq_eq_integral (v : Lp Space 2 (volume : Measure Space)) :
    ‖v‖ ^ 2 = ∫ x : Space, ‖v x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => real_inner_self_eq_norm_sq (v x))

/-- A compact spatially supported field whose pointwise time derivative is
jointly continuous has the asserted derivative in the genuine L² space. -/
theorem hasDerivAt_L2_of_compact_support
    {a b t : ℝ} {u du : VelocityField} {K : Set Space}
    (hK : IsCompact K) (hu : ContinuousOn u (Icc a b ×ˢ univ))
    (hdu : ContinuousOn du (Icc a b ×ˢ univ))
    (hsu : ∀ r ∈ Icc a b, ∀ x ∉ K, u (r, x) = 0)
    (hsdu : ∀ r ∈ Icc a b, ∀ x ∉ K, du (r, x) = 0)
    (hd : ∀ r ∈ Icc a b, ∀ x : Space,
      HasDerivAt (fun s => u (s, x)) (du (r, x)) r)
    (ht : t ∈ Ioo a b)
    {F : ℝ → Lp Space 2 (volume : Measure Space)}
    (hF : ∀ r ∈ Icc a b, F r =ᵐ[volume] fun x => u (r, x))
    {D : Lp Space 2 (volume : Measure Space)} (hD : D =ᵐ[volume] fun x => du (t, x)) :
    HasDerivAt F D t := by
  have htt : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hdu.mono (Set.prod_mono (Subset.refl _) (subset_univ K)))
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (r : ℝ) (hr : r ∈ Icc a b) (x : Space) : ‖du (r, x)‖ ≤ M := by
    by_cases hx : x ∈ K
    · exact (hC (r, x) ⟨hr, hx⟩).trans (le_max_left _ _)
    · rw [hsdu r hr x hx, norm_zero]
      exact hM
  let E : ℝ → Space → Space := fun r x => (r - t)⁻¹ • (u (r, x) - u (t, x)) - du (t, x)
  have hEsupport (r : ℝ) (hr : r ∈ Icc a b) (x : Space) (hx : x ∉ K) : E r x = 0 := by
    simp only [E, hsu r hr x hx, hsu t htt x hx, hsdu t htt x hx, sub_self,
      smul_zero]
  have hEnorm (r : ℝ) (hr : r ∈ Icc a b) (hrt : r ≠ t) (x : Space) : ‖E r x‖ ≤ 2 * M := by
    have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs x).hasDerivWithinAt) (fun s hs => hbound s hs x)
      (convex_Icc a b) htt hr
    have hslope : ‖(r - t)⁻¹ • (u (r, x) - u (t, x))‖ ≤ M := by
      rw [norm_smul, norm_inv]
      calc
        ‖r - t‖⁻¹ * ‖u (r, x) - u (t, x)‖ ≤ ‖r - t‖⁻¹ * (M * ‖r - t‖) :=
          mul_le_mul_of_nonneg_left hlip (inv_nonneg.mpr (norm_nonneg _))
        _ = M := by
          have hn : ‖r - t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrt)
          field_simp
    exact (norm_sub_le _ _).trans (by linarith [hbound t htt x])
  have hnear : ∀ᶠ r in 𝓝[≠] t, r ∈ Icc a b ∧ r ≠ t := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2), self_mem_nhdsWithin]
      with r hr hrt
    exact ⟨Ioo_subset_Icc_self hr, hrt⟩
  let bound : Space → ℝ := K.indicator (fun _ => (2 * M) ^ 2)
  have hboundi : Integrable bound := by
    exact (integrableOn_const (C := (2 * M) ^ 2) hK.measure_ne_top).integrable_indicator hK.measurableSet
  have hmeas : ∀ᶠ r in 𝓝[≠] t, AEStronglyMeasurable (fun x => ‖E r x‖ ^ 2) volume := by
    filter_upwards [hnear] with r hr
    exact (((CompactTimeIntegral.continuous_slice hu hr.1).sub
      (CompactTimeIntegral.continuous_slice hu htt)).const_smul (r - t)⁻¹ |>.sub
      (CompactTimeIntegral.continuous_slice hdu htt)).norm.pow 2 |>.aestronglyMeasurable
  have hdom : ∀ᶠ r in 𝓝[≠] t, ∀ᵐ x ∂volume, ‖‖E r x‖ ^ 2‖ ≤ bound x := by
    filter_upwards [hnear] with r hr
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ K
    · dsimp only [bound]
      rw [Set.indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (hEnorm r hr.1 hr.2 x) 2
    · dsimp only [bound]
      rw [Set.indicator_of_notMem hx, hEsupport r hr.1 x hx]
      simp
  have hpoint : ∀ᵐ x ∂volume, Tendsto (fun r => ‖E r x‖ ^ 2) (𝓝[≠] t) (𝓝 0) := by
    apply Filter.Eventually.of_forall
    intro x
    have hs := (hd t htt x).tendsto_slope
    have hc : Tendsto (fun _ : ℝ => du (t, x)) (𝓝[≠] t) (𝓝 (du (t, x))) :=
      tendsto_const_nhds
    simpa only [E, slope_def_module, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] using (hs.sub hc).norm.pow 2
  have hint := tendsto_integral_filter_of_dominated_convergence bound hmeas hdom hboundi hpoint
  have hint0 : Tendsto (fun r => ∫ x, ‖E r x‖ ^ 2) (𝓝[≠] t) (𝓝 0) := by
    simpa only [integral_zero] using hint
  have hcoe (r : ℝ) (hr : r ∈ Icc a b) :
      (slope F t r - D : Lp Space 2 (volume : Measure Space)) =ᵐ[volume] E r := by
    filter_upwards [Lp.coeFn_sub (slope F t r) D,
      Lp.coeFn_smul (r - t)⁻¹ (F r - F t), Lp.coeFn_sub (F r) (F t), hF r hr, hF t htt, hD]
      with x h1 h2 h3 h4 h5 h6
    simp only [Pi.smul_apply, Pi.sub_apply] at h1 h2 h3
    rw [h1]
    change ((r - t)⁻¹ • (F r - F t) : Lp Space 2 (volume : Measure Space)) x - D x = _
    rw [h2, h3, h4, h5, h6]
  have heq : (fun r => ‖slope F t r - D‖ ^ 2) =ᶠ[𝓝[≠] t] fun r => ∫ x, ‖E r x‖ ^ 2 := by
    filter_upwards [hnear] with r hr
    rw [lp_norm_sq_eq_integral]
    exact integral_congr_ae ((hcoe r hr.1).fun_comp (fun x => ‖x‖ ^ 2))
  have hsquare := hint0.congr' heq.symm
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsquare.sqrt

end NavierStokesR3.H3Comparison
