import NavierStokes.R3.H3WeakEmbedding
import NavierStokes.R3.H3Operations

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open H3Comparison

theorem squareEnergy_difference_tendsto {f : ℕ → Space → Space} {g : Space → Space}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => squareEnergy (f n - g)) atTop (𝓝 0) := by
  have he : (fun n => squareEnergy (f n - g)) =
      fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 := by
    funext n
    rw [squareEnergy_eq_norm_toLp ((hf n).sub hg), MemLp.toLp_sub]
  rw [he]
  have hc : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) := tendsto_const_nhds
  simpa only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] using (ht.sub hc).norm.pow 2

def approximationErrorNorm {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (n : ℕ) : ℝ :=
  weakH3Norm (h.approx n - f) (fun i => spatialPartial i (h.approx n) - df i)
    (fun i j => spatialPartial i (spatialPartial j (h.approx n)) - ddf i j)
    (fun i j k => spatialPartial i (spatialPartial j (spatialPartial k (h.approx n))) - dddf i j k)

theorem approximationErrorNorm_tendsto {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    Tendsto (approximationErrorNorm h) atTop (𝓝 0) := by
  have h0 := squareEnergy_difference_tendsto h.approx_memLp h.memLp h.tendsto
  have h1 (i) := squareEnergy_difference_tendsto (fun n => h.derivative_approx_memLp n i)
    (h.derivative_memLp i) (h.derivative_tendsto i)
  have h2 (i j) := squareEnergy_difference_tendsto (fun n => h.second_approx_memLp n i j)
    (h.second_memLp i j) (h.second_tendsto i j)
  have h3 (i j k) := squareEnergy_difference_tendsto (fun n => h.third_approx_memLp n i j k)
    (h.third_memLp i j k) (h.third_tendsto i j k)
  have hs2 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => h2 i j))
  have hs3 := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      tendsto_finsetSum Finset.univ (fun k _ => h3 i j k)))
  have hm := ((((((h0.add (h1 0)).add (h1 1)).add (h1 2)).add (h2 1 0)).add
    (h2 2 0)).add (h2 2 1))
  have he := (((hm.add (h3 2 1 0)).add hs2).add hs3)
  unfold approximationErrorNorm weakH3Norm weakH3Energy
  simpa only [Finset.sum_const_zero, add_zero, Real.sqrt_zero] using he.sqrt

theorem approximation_norm_sub_le {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (n : ℕ) (x : Space) :
    ‖h.approx n x - f x‖ ≤ 3 * approximationErrorNorm h n := by
  have ha := (H3Approximation.of_contDiff_compact (h.smooth n) (h.compact n)).sub h
  exact norm_le_weakH3Norm ha ((h.smooth n).continuous.sub hf) x

theorem approximation_uniform_error {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) :
    ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧ Tendsto a atTop (𝓝 0) ∧
      ∀ n x, ‖h.approx n x - f x‖ ≤ a n := by
  refine ⟨fun n => 3 * approximationErrorNorm h n, ?_, ?_, approximation_norm_sub_le h hf⟩
  · intro n
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · simpa only [mul_zero] using tendsto_const_nhds.mul (approximationErrorNorm_tendsto h)

/-- Approximation in the genuine H³ topology is uniformly convergent to the
continuous representative on all of ℝ³. -/
theorem approximation_tendstoUniformly {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) :
    TendstoUniformly h.approx f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have he : Tendsto (fun n => 3 * approximationErrorNorm h n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (approximationErrorNorm_tendsto h)
  filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (approximation_norm_sub_le h hf n x).trans_lt hn

end NavierStokesR3.H3Embedding
