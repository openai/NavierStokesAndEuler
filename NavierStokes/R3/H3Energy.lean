import NavierStokes.R3.H3Transport
import NavierStokes.R3.ComparisonGronwall

/-! # Difference energy for ordinary H³ fields

The time derivative is a derivative in the L² Hilbert space. Spatial
integration by parts uses the actual weak derivative approximations.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement

/-- The L² Hilbert norm is the ordinary integral, with no totalized
nonintegrable expression entering the identity. -/
theorem integral_norm_sq_eq_toLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Space → E} (hf : MemLp f 2 volume) :
    (∫ x, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [real_inner_self_eq_norm_sq]

/-- Differentiability in L² suffices to differentiate the whole-space energy;
no pointwise or joint time smoothness is needed. -/
theorem hasDerivAt_integral_norm_sq {u : ℝ → Space → Space} {du : Space → Space}
    (hu : ∀ t, MemLp (u t) 2 volume) (hdu : MemLp du 2 volume) {t : ℝ}
    (hd : HasDerivAt (fun s => (hu s).toLp (u s)) (hdu.toLp du) t) :
    HasDerivAt (fun s => ∫ x, ‖u s x‖ ^ 2) (2 * ∫ x, ⟪u t x, du x⟫_ℝ) t := by
  have he : (fun s => ∫ x, ‖u s x‖ ^ 2) = fun s => ‖(hu s).toLp (u s)‖ ^ 2 :=
    funext (fun s => integral_norm_sq_eq_toLp (hu s))
  rw [he]
  simpa only [inner_toLp] using hd.norm_sq

/-- The exact weak difference equation yields the usual Gronwall energy
bound. Pressure orthogonality is a separate analytic input, allowing any
valid normalization or homogeneous-gradient recovery theorem. -/
theorem difference_rate_le {w v dt g : Space → Space}
    {dw dv : Fin 3 → Space → Space}
    {ddw ddv : Fin 3 → Fin 3 → Space → Space}
    {dddw dddv : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (hw : H3Approximation w dw ddw dddw) (hv : H3Approximation v dv ddv dddv)
    (hcw : Continuous w) (hcv : Continuous v)
    (hg : MemLp g 2 volume) {ν G : ℝ} (hν : 0 ≤ ν)
    (A : Space → Space →L[ℝ] Space) (hA : AEStronglyMeasurable A volume)
    (hG : ∀ x, ‖A x‖ ≤ G)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dv i x i) = 0)
    (hpressure : (∫ x, ⟪w x, g x⟫_ℝ) = 0)
    (hNS : ∀ᵐ x ∂volume, dt x = ν • (∑ i : Fin 3, ddw i i x) - A x (w x) -
      (∑ i : Fin 3, (v x i) • dw i x) - g x) :
    2 * (∫ x, ⟪w x, dt x⟫_ℝ) ≤ 2 * G * (∫ x, ‖w x‖ ^ 2) := by
  have hAw : MemLp (fun x => A x (w x)) 2 volume := by
    apply hw.memLp.of_le_mul
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hw.memLp.1))
    exact Filter.Eventually.of_forall (fun x =>
      ((A x).le_opNorm (w x)).trans (mul_le_mul_of_nonneg_right (hG x) (norm_nonneg _)))
  have hiC := integrable_inner_of_memLp hw.memLp hAw
  have hiP := integrable_inner_of_memLp hw.memLp hg
  have hiL : Integrable (fun x => ⟪w x, ∑ i : Fin 3, ddw i i x⟫_ℝ) := by
    simp only [inner_sum]
    exact integrable_finsetSum _ (fun i _ => integrable_inner_of_memLp hw.memLp (hw.second_memLp i i))
  have hiT : Integrable (fun x => ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) :=
    integrable_finsetSum _ (fun i _ => integrable_transport hw.memLp hv.memLp.1 hw.derivative_memLp
      (H3Embedding.norm_le_weakH3Norm hv hcv) i)
  have hid : (∫ x, ⟪w x, dt x⟫_ℝ) =
      ν * (∫ x, ⟪w x, ∑ i : Fin 3, ddw i i x⟫_ℝ) -
        (∫ x, ⟪w x, A x (w x)⟫_ℝ) -
        (∫ x, ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) - (∫ x, ⟪w x, g x⟫_ℝ) := by
    have he : (fun x => ⟪w x, dt x⟫_ℝ) =ᵐ[volume]
        (fun x => ν * ⟪w x, ∑ i : Fin 3, ddw i i x⟫_ℝ - ⟪w x, A x (w x)⟫_ℝ -
          (∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) - ⟪w x, g x⟫_ℝ) := by
      filter_upwards [hNS] with x hx
      rw [hx]
      simp only [inner_sub_right, inner_smul_right, inner_sum]
    have hsub₁ := integral_sub (((hiL.const_mul ν).sub hiC).sub hiT) hiP
    have hsub₂ := integral_sub ((hiL.const_mul ν).sub hiC) hiT
    have hsub₃ := integral_sub (hiL.const_mul ν) hiC
    simp only [Pi.sub_apply] at hsub₁ hsub₂ hsub₃
    rw [integral_congr_ae he, hsub₁, hsub₂, hsub₃, integral_const_mul]
  rw [hw.integral_inner_laplacian, hw.transport_zero hv hcw hcv hdiv, hpressure,
    sub_zero, sub_zero] at hid
  have hnonneg : 0 ≤ ∑ i : Fin 3, ∫ x, ‖dw i x‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hie : Integrable (fun x => ‖w x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hw.memLp.1).mp hw.memLp
  have hneg : -(∫ x, ⟪w x, A x (w x)⟫_ℝ) ≤ G * (∫ x, ‖w x‖ ^ 2) := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hiC.neg (hie.const_mul G)
    intro x
    calc
      -⟪w x, A x (w x)⟫_ℝ ≤ ‖⟪w x, A x (w x)⟫_ℝ‖ := neg_le_abs _
      _ ≤ ‖w x‖ * ‖A x (w x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖w x‖ * (G * ‖w x‖) :=
        mul_le_mul_of_nonneg_left (((A x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hG x) (norm_nonneg _))) (norm_nonneg _)
      _ = G * ‖w x‖ ^ 2 := by ring
  rw [hid]
  nlinarith [mul_nonneg hν hnonneg]

/-- Gronwall in the L² Hilbert space, with only interior differentiability
and continuity at the endpoints. -/
theorem hilbert_curve_zero {T G : ℝ} (hT : 0 ≤ T) (hG : 0 ≤ G)
    {W D : ℝ → Lp Space 2 (volume : Measure Space)}
    (hc : ContinuousOn W (Icc 0 T)) (hzero : W 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt W (D t) t)
    (hrate : ∀ t ∈ Ioo 0 T, 2 * ⟪W t, D t⟫_ℝ ≤ 2 * G * ‖W t‖ ^ 2) :
    ∀ t ∈ Icc 0 T, W t = 0 := by
  have hinit : ‖W 0‖ ^ 2 ≤ 0 := by rw [hzero, norm_zero]; norm_num
  have hbound := ComparisonGronwall.le_exp_mul_of_deriv_le hT
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hG) (le_refl (0 : ℝ))
    (hc.norm.pow 2) hinit (fun t ht => (hd t ht).norm_sq)
    (fun t ht => by simpa only [add_zero, Pi.pow_apply] using! hrate t ht)
  intro t ht
  have he : ‖W t‖ ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg _)
    simpa only [zero_mul, Pi.pow_apply] using! hbound t ht
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)

/-- Equality in L² implies equality of the continuous spatial representatives. -/
theorem eq_of_toLp_eq {u v : Space → Space} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hcu : Continuous u) (hcv : Continuous v) (he : hu.toLp u = hv.toLp v) : u = v := by
  have hae : u =ᵐ[volume] v := by
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    rw [← hx, ← hy, he]
  exact Measure.eq_of_ae_eq hae hcu hcv

end NavierStokesR3.H3Comparison
