import NavierStokes.R3.H3Approximation

/-! # Whole-space integration by parts for Sobolev competitors

The limiting fields need not be classically differentiable. Integration by
parts follows from their actual L² weak-derivative approximations.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hilbert pairing equals the ordinary whole-space integral. -/
theorem inner_toLp {f g : Space → E} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, ⟪f x, g x⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem integrable_inner_of_memLp {f g : Space → E}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun x => ⟪f x, g x⟫_ℝ) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

/-- Simultaneous L² convergence passes products to their actual integrals. -/
theorem tendsto_integral_inner {f g : ℕ → Space → E} {F G : Space → E}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : ∀ n, MemLp (g n) 2 volume)
    (hF : MemLp F 2 volume) (hG : MemLp G 2 volume)
    (hflim : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hF.toLp F)))
    (hglim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hG.toLp G))) :
    Tendsto (fun n => ∫ x, ⟪f n x, g n x⟫_ℝ) atTop (𝓝 (∫ x, ⟪F x, G x⟫_ℝ)) := by
  have h : Tendsto (fun n => ⟪(hf n).toLp (f n), (hg n).toLp (g n)⟫_ℝ) atTop
      (𝓝 ⟪hF.toLp F, hG.toLp G⟫_ℝ) := hflim.inner hglim
  simpa only [inner_toLp] using h

private theorem compact_inner_partial {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (i : Fin 3) :
    (∫ x, ⟪f x, spatialPartial i g x⟫_ℝ) =
      -(∫ x, ⟪spatialPartial i f x, g x⟫_ℝ) := by
  have hfl := smooth_compact_memLp hf hcf
  have hgl := smooth_compact_memLp hg hcg
  have hdfl := smooth_compact_memLp (spatial_partial_contDiff hf i)
    (hcf.fderiv_apply ℝ (coordinateVector i))
  have hdgl := smooth_compact_memLp (spatial_partial_contDiff hg i)
    (hcg.fderiv_apply ℝ (coordinateVector i))
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := innerSL ℝ)
    (integrable_inner_of_memLp hdfl hgl) (integrable_inner_of_memLp hfl hdgl)
    (integrable_inner_of_memLp hfl hgl)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

/-- Global integration by parts for genuine H¹ fields, with no classical
smoothness or compact support requirement on either limiting field. -/
theorem H1Approximation.integral_inner_derivative {f g : Space → E}
    {df dg : Fin 3 → Space → E} (hf : H1Approximation f df) (hg : H1Approximation g dg)
    (i : Fin 3) :
    (∫ x, ⟪f x, dg i x⟫_ℝ) = -(∫ x, ⟪df i x, g x⟫_ℝ) := by
  have hl := tendsto_integral_inner hf.approx_memLp (fun n => hg.derivative_approx_memLp n i)
    hf.memLp (hg.derivative_memLp i) hf.tendsto (hg.derivative_tendsto i)
  have hr := (tendsto_integral_inner (fun n => hf.derivative_approx_memLp n i) hg.approx_memLp
    (hf.derivative_memLp i) hg.memLp (hf.derivative_tendsto i) hg.tendsto).neg
  have he (n : ℕ) := compact_inner_partial (hf.smooth n) (hg.smooth n) (hf.compact n) (hg.compact n) i
  exact tendsto_nhds_unique (hl.congr (fun n => he n)) hr

/-- The weak H³ Laplacian has the usual negative energy pairing. -/
theorem H3Approximation.integral_inner_laplacian {f : Space → E}
    {df : Fin 3 → Space → E} {ddf : Fin 3 → Fin 3 → Space → E}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → E}
    (hf : H3Approximation f df ddf dddf) :
    (∫ x, ⟪f x, ∑ i : Fin 3, ddf i i x⟫_ℝ) =
      -(∑ i : Fin 3, ∫ x, ‖df i x‖ ^ 2) := by
  simp only [inner_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_inner_of_memLp hf.memLp (hf.second_memLp i i)),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [real_inner_self_eq_norm_sq] using
    hf.toH1Approximation.integral_inner_derivative (hf.partial_toH1 i) i

/-- A normalized H¹ pressure gradient is orthogonal to every divergence-free
H¹ velocity on the whole space. Both derivatives are weak derivatives and
neither field needs compact support or classical differentiability. -/
theorem pressure_orthogonality {w : Space → Space} {dw : Fin 3 → Space → Space}
    {p : Space → ℝ} {dp : Fin 3 → Space → ℝ}
    (hw : H1Approximation w dw) (hp : H1Approximation p dp)
    (hdiv : ∀ᵐ x ∂volume, (∑ i : Fin 3, dw i x i) = 0) :
    (∫ x, ∑ i : Fin 3, w x i * dp i x) = 0 := by
  have hwi (i : Fin 3) := hw.map (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
  have hparts (i : Fin 3) : (∫ x, w x i * dp i x) = -(∫ x, dw i x i * p x) := by
    have h := (hwi i).integral_inner_derivative hp i
    change (∫ x, dp i x * w x i) = -(∫ x, p x * dw i x i) at h
    simpa only [mul_comm] using h
  have hil (i : Fin 3) : Integrable (fun x => w x i * dp i x) :=
    (hwi i).memLp.integrable_mul (hp.derivative_memLp i)
  have hir (i : Fin 3) : Integrable (fun x => dw i x i * p x) :=
    ((hwi i).derivative_memLp i).integrable_mul hp.memLp
  rw [integral_finsetSum _ (fun i _ => hil i)]
  simp_rw [hparts]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hir i)]
  have hz : (∫ x, ∑ i : Fin 3, dw i x i * p x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hdiv] with x hx
    simp only [← Finset.sum_mul, hx, zero_mul, Pi.zero_apply]
  rw [hz, neg_zero]

end NavierStokesR3.H3Comparison
