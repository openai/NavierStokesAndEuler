import NavierStokes.R3.H3Products
import NavierStokes.R3.H3UniformApproximation

/-! # Divergence-free transport for weak H³ limits

The compact smooth approximants need not themselves be divergence-free.
Their divergence terms converge to the zero weak divergence of the limit.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness

private def transportProduct (i : Fin 3) : Space →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.lsmul ℝ ℝ).comp (EuclideanSpace.proj i)

private theorem transportProduct_apply (i : Fin 3) (v w : Space) :
    transportProduct i v w = (v i) • w := rfl

private def realInnerBilinear : Space →L[ℝ] Space →L[ℝ] ℝ := innerSL ℝ

private theorem realInnerBilinear_apply (v w : Space) :
    realInnerBilinear v w = ⟪v, w⟫_ℝ := rfl

private theorem compact_transport {w v : Space → Space}
    (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    (hcw : HasCompactSupport w) (hcv : HasCompactSupport v) :
    2 * (∑ i : Fin 3, ∫ x, v x i * ⟪w x, spatialPartial i w x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * spatialPartial i v x i) := by
  have hiL (i : Fin 3) : Integrable (fun x => v x i * ⟪w x, spatialPartial i w x⟫_ℝ) :=
    ((component_contDiff hv i).continuous.mul
      (hw.inner ℝ (spatial_partial_contDiff hw i)).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_component hcv i).mul_right
  have hiR (i : Fin 3) : Integrable (fun x => ‖w x‖ ^ 2 * spatialPartial i v x i) :=
    ((hw.continuous.norm.pow 2).mul
      (component_contDiff (spatial_partial_contDiff hv i) i).continuous).integrable_of_hasCompactSupport
      (CompactEnergy.compact_norm_sq hcw).mul_right
  have h := CompactEnergy.integral_fderiv_apply (hw.norm_sq ℝ) hv hcv
  have he (x : Space) : fderiv ℝ (fun y => ‖w y‖ ^ 2) x (v x) =
      2 * ∑ i : Fin 3, v x i * ⟪w x, spatialPartial i w x⟫_ℝ := by
    rw [fderiv_normsq hw]
    have hlin : fderiv ℝ w x (v x) = ∑ i : Fin 3, (v x i) • spatialPartial i w x := by
      calc
        fderiv ℝ w x (v x) = fderiv ℝ w x (∑ i : Fin 3, (v x i) • coordinateVector i) :=
          congrArg (fderiv ℝ w x) (sum_coordinates (v x)).symm
        _ = _ := by simp only [map_sum, map_smul, spatialPartial]
    rw [hlin, inner_sum]
    simp only [inner_smul_right]
  simp_rw [he] at h
  have hright : (fun x => ‖w x‖ ^ 2 * ∑ i : Fin 3, spatialPartial i v x i) =
      (fun x => ∑ i : Fin 3, ‖w x‖ ^ 2 * spatialPartial i v x i) :=
    funext (fun _ => Finset.mul_sum _ _ _)
  rw [hright] at h
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hiL i),
    integral_finsetSum _ (fun i _ => hiR i)] at h
  exact h

/-- All integrals of the weak transport term are genuine integrable products. -/
theorem integrable_transport {w v : Space → Space} {dw : Fin 3 → Space → Space}
    (hw : MemLp w 2 volume) (hv : AEStronglyMeasurable v volume)
    (hdw : ∀ i, MemLp (dw i) 2 volume) {C : ℝ} (hC : ∀ x, ‖v x‖ ≤ C)
    (i : Fin 3) : Integrable (fun x => v x i * ⟪w x, dw i x⟫_ℝ) := by
  have hi := integrable_inner_of_memLp
    (memLp_bilinear_bounded (transportProduct i) hv hw hC) (hdw i)
  simpa only [transportProduct_apply, real_inner_smul_left] using! hi

/-- Transport cancels for weak first derivatives obtained from Sobolev
approximants that converge uniformly in velocity. No pointwise derivative of
the limiting fields, pressure condition, or energy identity is assumed. -/
theorem weak_transport_zero {w v : Space → Space} {dw dv : Fin 3 → Space → Space}
    (hw : H1Approximation w dw) (hv : H1Approximation v dv)
    {aw av : ℕ → ℝ} (haw : Tendsto aw atTop (𝓝 0)) (hav : Tendsto av atTop (𝓝 0))
    (hew : ∀ n x, ‖hw.approx n x - w x‖ ≤ aw n)
    (hev : ∀ n x, ‖hv.approx n x - v x‖ ≤ av n)
    {Cw Cv : ℝ} (hcw : ∀ x, ‖w x‖ ≤ Cw) (hcv : ∀ x, ‖v x‖ ≤ Cv)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dv i x i) = 0) :
    (∫ x, ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) = 0 := by
  have hlimL (i : Fin 3) : Tendsto
      (fun n => ∫ x, hv.approx n x i * ⟪hw.approx n x, spatialPartial i (hw.approx n) x⟫_ℝ)
      atTop (𝓝 (∫ x, v x i * ⟪w x, dw i x⟫_ℝ)) := by
    obtain ⟨hp, hlim⟩ := tendsto_toLp_bilinear (transportProduct i)
      (fun n => (hv.smooth n).continuous.aestronglyMeasurable) hv.memLp.1
      hw.approx_memLp hw.memLp hav hev hcv hw.tendsto
    have h := tendsto_integral_inner hp (fun n => hw.derivative_approx_memLp n i)
      (memLp_bilinear_bounded (transportProduct i) hv.memLp.1 hw.memLp hcv)
      (hw.derivative_memLp i) hlim (hw.derivative_tendsto i)
    simpa only [transportProduct_apply, real_inner_smul_left] using! h
  obtain ⟨hp, hlimp⟩ := tendsto_toLp_bilinear realInnerBilinear
    (fun n => (hw.smooth n).continuous.aestronglyMeasurable) hw.memLp.1
    hw.approx_memLp hw.memLp haw hew hcw hw.tendsto
  have hp₀ := memLp_bilinear_bounded realInnerBilinear hw.memLp.1 hw.memLp hcw
  have hlimR (i : Fin 3) : Tendsto
      (fun n => ∫ x, ‖hw.approx n x‖ ^ 2 * spatialPartial i (hv.approx n) x i)
      atTop (𝓝 (∫ x, ‖w x‖ ^ 2 * dv i x i)) := by
    let hvi := hv.map (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
    have h := tendsto_integral_inner hp (fun n => hvi.derivative_approx_memLp n i)
      hp₀ (hvi.derivative_memLp i) hlimp (hvi.derivative_tendsto i)
    have he (n : ℕ) : spatialPartial i (hvi.approx n) =
        fun x => spatialPartial i (hv.approx n) x i := by
      funext x
      exact fderiv_component (hv.smooth n) i x (coordinateVector i)
    simp only [he, realInnerBilinear_apply, real_inner_self_eq_norm_sq] at h
    change Tendsto (fun n => ∫ x, spatialPartial i (hv.approx n) x i * ‖hw.approx n x‖ ^ 2)
      atTop (𝓝 (∫ x, dv i x i * ‖w x‖ ^ 2)) at h
    simpa only [mul_comm] using! h
  have hcompact (n : ℕ) := compact_transport (hw.smooth n) (hv.smooth n) (hw.compact n) (hv.compact n)
  have hL := (tendsto_finsetSum Finset.univ (fun i _ => hlimL i)).const_mul 2
  have hR := (tendsto_finsetSum Finset.univ (fun i _ => hlimR i)).neg
  have hid : 2 * (∑ i : Fin 3, ∫ x, v x i * ⟪w x, dw i x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * dv i x i) :=
    tendsto_nhds_unique (hL.congr hcompact) hR
  have hiR (i : Fin 3) : Integrable (fun x => ‖w x‖ ^ 2 * dv i x i) := by
    have hvi := hv.map (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
    simpa only [realInnerBilinear_apply, real_inner_self_eq_norm_sq, Pi.mul_apply, Function.comp_apply] using!
      hp₀.integrable_mul (hvi.derivative_memLp i)
  have hzero : (∑ i : Fin 3, ∫ x, ‖w x‖ ^ 2 * dv i x i) = 0 := by
    rw [← integral_finsetSum _ (fun i _ => hiR i)]
    apply integral_eq_zero_of_ae
    filter_upwards [hdiv] with x hx
    simp only [← Finset.mul_sum, hx, mul_zero, Pi.zero_apply]
  rw [hzero, neg_zero] at hid
  rw [integral_finsetSum _ (fun i _ =>
    integrable_transport hw.memLp hv.memLp.1 hw.derivative_memLp hcv i)]
  linarith

/-- Ordinary H³ velocities have the exact transport energy cancellation.
Uniform convergence and boundedness are consequences of H³, not premises. -/
theorem H3Approximation.transport_zero {w v : Space → Space}
    {dw dv : Fin 3 → Space → Space}
    {ddw ddv : Fin 3 → Fin 3 → Space → Space}
    {dddw dddv : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (hw : H3Approximation w dw ddw dddw) (hv : H3Approximation v dv ddv dddv)
    (hcw : Continuous w) (hcv : Continuous v)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dv i x i) = 0) :
    (∫ x, ∑ i : Fin 3, v x i * ⟪w x, dw i x⟫_ℝ) = 0 := by
  obtain ⟨aw, _, haw, hew⟩ := H3Embedding.approximation_uniform_error hw hcw
  obtain ⟨av, _, hav, hev⟩ := H3Embedding.approximation_uniform_error hv hcv
  exact weak_transport_zero hw.toH1Approximation hv.toH1Approximation haw hav hew hev
    (H3Embedding.norm_le_weakH3Norm hw hcw) (H3Embedding.norm_le_weakH3Norm hv hcv) hdiv

end NavierStokesR3.H3Comparison
