import NavierStokes.R3.H3Embedding
import NavierStokes.R3.H3Approximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Sobolev embedding for genuine weak H³ fields

The estimate is passed through a smooth compact approximation in L² of all
weak jets. No classical derivatives of the limiting field are used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators

namespace NavierStokesR3.H3Embedding

open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open H3Comparison

def weakH3Energy (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) : ℝ :=
  squareEnergy f + squareEnergy (df 0) + squareEnergy (df 1) + squareEnergy (df 2) +
    squareEnergy (ddf 1 0) + squareEnergy (ddf 2 0) + squareEnergy (ddf 2 1) +
    squareEnergy (dddf 2 1 0) + (∑ i, ∑ j, squareEnergy (ddf i j)) +
    (∑ i, ∑ j, ∑ k, squareEnergy (dddf i j k))

def weakH3Norm (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) : ℝ :=
  Real.sqrt (weakH3Energy f df ddf dddf)

theorem weakH3Energy_nonneg (f : Space → Space) (df : Fin 3 → Space → Space)
    (ddf : Fin 3 → Fin 3 → Space → Space)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space) :
    0 ≤ weakH3Energy f df ddf dddf := by
  have h2 : 0 ≤ ∑ i, ∑ j, squareEnergy (ddf i j) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _))
  have h3 : 0 ≤ ∑ i, ∑ j, ∑ k, squareEnergy (dddf i j k) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => squareEnergy_nonneg _)))
  unfold weakH3Energy
  apply add_nonneg (add_nonneg _ h2) h3
  repeat' apply add_nonneg
  all_goals exact squareEnergy_nonneg _

theorem squareEnergy_eq_norm_toLp {f : Space → Space} (hf : MemLp f 2 volume) :
    squareEnergy f = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem squareEnergy_tendsto_of_toLp {f : ℕ → Space → Space} {g : Space → Space}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g))) :
    Tendsto (fun n => squareEnergy (f n)) atTop (𝓝 (squareEnergy g)) := by
  have he : (fun n => squareEnergy (f n)) = fun n => ‖(hf n).toLp (f n)‖ ^ 2 :=
    funext (fun n => squareEnergy_eq_norm_toLp (hf n))
  rw [he, squareEnergy_eq_norm_toLp hg]
  exact ht.norm.pow 2

theorem approximation_energy_tendsto {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    Tendsto (fun n => derivativeH3Energy (h.approx n)) atTop
      (𝓝 (weakH3Energy f df ddf dddf)) := by
  have h0 := squareEnergy_tendsto_of_toLp h.approx_memLp h.memLp h.tendsto
  have h1 (i) := squareEnergy_tendsto_of_toLp (fun n => h.derivative_approx_memLp n i)
    (h.derivative_memLp i) (h.derivative_tendsto i)
  have h2 (i j) := squareEnergy_tendsto_of_toLp (fun n => h.second_approx_memLp n i j)
    (h.second_memLp i j) (h.second_tendsto i j)
  have h3 (i j k) := squareEnergy_tendsto_of_toLp (fun n => h.third_approx_memLp n i j k)
    (h.third_memLp i j k) (h.third_tendsto i j k)
  apply ((((((((h0.add (h1 0)).add (h1 1)).add (h1 2)).add (h2 1 0)).add
    (h2 2 0)).add (h2 2 1)).add (h3 2 1 0)).add ?_).add ?_
  · exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => h2 i j))
  · exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
      tendsto_finsetSum _ (fun k _ => h3 i j k)))

theorem approximation_finiteH3 {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (n : ℕ) : HasFiniteH3 (h.approx n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm (h.approx_memLp n).aestronglyMeasurable).1
      (h.approx_memLp n)
  · intro i
    exact (memLp_two_iff_integrable_sq_norm
      (h.derivative_approx_memLp n i).aestronglyMeasurable).1 (h.derivative_approx_memLp n i)
  · intro i j
    exact (memLp_two_iff_integrable_sq_norm
      (h.second_approx_memLp n i j).aestronglyMeasurable).1 (h.second_approx_memLp n i j)
  · intro i j k
    exact (memLp_two_iff_integrable_sq_norm
      (h.third_approx_memLp n i j k).aestronglyMeasurable).1 (h.third_approx_memLp n i j k)

/-- The whole-space Sobolev estimate for almost every value of any weak H³
representative. -/
theorem ae_norm_sq_le_weakH3Energy {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) :
    ∀ᵐ x ∂volume, ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h.tendsto).exists_seq_tendsto_ae
  have ha : ∀ᵐ x ∂volume, ∀ n, (h.approx_memLp (ns n)).toLp (h.approx (ns n)) x =
      h.approx (ns n) x :=
    ae_all_iff.2 (fun n => (h.approx_memLp (ns n)).coeFn_toLp)
  filter_upwards [hae, ha, h.memLp.coeFn_toLp] with x hx hax hfx
  have ht : Tendsto (fun n => h.approx (ns n) x) atTop (𝓝 (f x)) := by
    simpa only [hax, hfx] using hx
  have hen := (approximation_energy_tendsto h).comp hns.tendsto_atTop
  exact le_of_tendsto_of_tendsto (ht.norm.pow 2) (tendsto_const_nhds.mul hen)
    (Filter.Eventually.of_forall (fun n =>
      norm_sq_le_eight_derivativeH3Energy (h.smooth (ns n)) (approximation_finiteH3 h (ns n)) x))

/-- A continuous representative of a weak H³ field satisfies the Sobolev
bound at every point. -/
theorem norm_sq_le_weakH3Energy {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (x : Space) :
    ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf := by
  have hc : IsClosed {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf} :=
    isClosed_le (hf.norm.pow 2) continuous_const
  have heq := hc.ae_eq_univ_iff_eq.mp (show
      {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf} =ᵐ[volume] univ from by
    filter_upwards [ae_norm_sq_le_weakH3Energy h] with y hy
    exact propext ⟨fun _ => mem_univ y, fun _ => hy⟩)
  change x ∈ {x | ‖f x‖ ^ 2 ≤ 8 * weakH3Energy f df ddf dddf}
  rw [heq]
  exact mem_univ _

theorem norm_le_weakH3Norm {f : Space → Space} {df : Fin 3 → Space → Space}
    {ddf : Fin 3 → Fin 3 → Space → Space}
    {dddf : Fin 3 → Fin 3 → Fin 3 → Space → Space}
    (h : H3Approximation f df ddf dddf) (hf : Continuous f) (x : Space) :
    ‖f x‖ ≤ 3 * weakH3Norm f df ddf dddf := by
  have he := norm_sq_le_weakH3Energy h hf x
  have hn : 0 ≤ weakH3Norm f df ddf dddf := Real.sqrt_nonneg _
  have hs : weakH3Norm f df ddf dddf ^ 2 = weakH3Energy f df ddf dddf :=
    Real.sq_sqrt (weakH3Energy_nonneg f df ddf dddf)
  nlinarith [weakH3Energy_nonneg f df ddf dddf]

end NavierStokesR3.H3Embedding
