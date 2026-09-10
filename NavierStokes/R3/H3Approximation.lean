import NavierStokes.R3.CompactEnergy
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Sobolev fields represented by smooth compact approximations

The derivatives in these records are genuine weak derivatives: each is the
L² limit of the corresponding derivatives of one smooth compact sequence.
No pointwise differentiability is required of the limiting field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Compact smooth fields are in the ordinary whole-space L² space. -/
theorem smooth_compact_memLp {f : Space → E} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hc

/-- The standard completion definition of a first-order Sobolev field. -/
structure H1Approximation (f : Space → E) (df : Fin 3 → Space → E) where
  memLp : MemLp f 2 volume
  derivative_memLp : ∀ i, MemLp (df i) 2 volume
  approx : ℕ → Space → E
  smooth : ∀ n, ContDiff ℝ ∞ (approx n)
  compact : ∀ n, HasCompactSupport (approx n)
  approx_memLp : ∀ n, MemLp (approx n) 2 volume
  derivative_approx_memLp : ∀ n i, MemLp (spatialPartial i (approx n)) 2 volume
  tendsto : Tendsto (fun n => (approx_memLp n).toLp (approx n)) atTop (𝓝 (memLp.toLp f))
  derivative_tendsto : ∀ i,
    Tendsto (fun n => (derivative_approx_memLp n i).toLp (spatialPartial i (approx n)))
      atTop (𝓝 ((derivative_memLp i).toLp (df i)))

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A bounded linear map acts continuously on representatives in L². -/
theorem toLp_comp (L : E →L[ℝ] F) {f : Space → E} (hf : MemLp f 2 volume) :
    (L.comp_memLp' hf).toLp (L ∘ f) = L.compLpL 2 volume (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [(L.comp_memLp' hf).coeFn_toLp,
    L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp] with x hx hy hz
  simp only [hx, hy, Function.comp_apply, hz]

private theorem partial_comp (L : E →L[ℝ] F) {f : Space → E}
    (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    spatialPartial i (L ∘ f) = L ∘ spatialPartial i f := by
  funext x
  have hd := (L.hasFDerivAt.comp x (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun M => M (coordinateVector i)) hd

/-- Taking a component or any fixed bounded linear image preserves genuine
weak first derivatives. -/
def H1Approximation.map {f : Space → E} {df : Fin 3 → Space → E}
    (hf : H1Approximation f df) (L : E →L[ℝ] F) :
    H1Approximation (L ∘ f) (fun i => L ∘ df i) where
  memLp := L.comp_memLp' hf.memLp
  derivative_memLp := fun i => L.comp_memLp' (hf.derivative_memLp i)
  approx := fun n => L ∘ hf.approx n
  smooth := fun n => L.contDiff.comp (hf.smooth n)
  compact := fun n => (hf.compact n).comp_left L.map_zero
  approx_memLp := fun n => L.comp_memLp' (hf.approx_memLp n)
  derivative_approx_memLp := fun n i => by
    rw [partial_comp L (hf.smooth n) i]
    exact L.comp_memLp' (hf.derivative_approx_memLp n i)
  tendsto := by
    exact (L.compLpL 2 volume).continuous.tendsto _ |>.comp hf.tendsto
  derivative_tendsto := by
    intro i
    simp only [partial_comp L, hf.smooth]
    exact (L.compLpL 2 volume).continuous.tendsto _ |>.comp (hf.derivative_tendsto i)

/-- One smooth compact approximation controls all ordered derivatives through
order three, the usual completion definition of H³ on Euclidean space. -/
structure H3Approximation (f : Space → E) (df : Fin 3 → Space → E)
    (ddf : Fin 3 → Fin 3 → Space → E)
    (dddf : Fin 3 → Fin 3 → Fin 3 → Space → E) extends H1Approximation f df where
  second_memLp : ∀ i j, MemLp (ddf i j) 2 volume
  third_memLp : ∀ i j k, MemLp (dddf i j k) 2 volume
  second_approx_memLp : ∀ n i j,
    MemLp (spatialPartial i (spatialPartial j (approx n))) 2 volume
  third_approx_memLp : ∀ n i j k,
    MemLp (spatialPartial i (spatialPartial j (spatialPartial k (approx n)))) 2 volume
  second_tendsto : ∀ i j,
    Tendsto (fun n => (second_approx_memLp n i j).toLp
      (spatialPartial i (spatialPartial j (approx n)))) atTop
        (𝓝 ((second_memLp i j).toLp (ddf i j)))
  third_tendsto : ∀ i j k,
    Tendsto (fun n => (third_approx_memLp n i j k).toLp
      (spatialPartial i (spatialPartial j (spatialPartial k (approx n))))) atTop
        (𝓝 ((third_memLp i j k).toLp (dddf i j k)))

namespace H3Approximation

variable {f : Space → E} {df : Fin 3 → Space → E}
  {ddf : Fin 3 → Fin 3 → Space → E} {dddf : Fin 3 → Fin 3 → Fin 3 → Space → E}

/-- The weak derivative is itself an H¹ field, with the next weak jets. -/
def partial_toH1 (h : H3Approximation f df ddf dddf) (i : Fin 3) :
    H1Approximation (df i) (fun j => ddf j i) where
  memLp := h.derivative_memLp i
  derivative_memLp := fun j => h.second_memLp j i
  approx := fun n => spatialPartial i (h.approx n)
  smooth := fun n => spatial_partial_contDiff (h.smooth n) i
  compact := fun n => (h.compact n).fderiv_apply ℝ (coordinateVector i)
  approx_memLp := fun n => h.derivative_approx_memLp n i
  derivative_approx_memLp := fun n j => h.second_approx_memLp n j i
  tendsto := h.derivative_tendsto i
  derivative_tendsto := fun j => h.second_tendsto j i

/-- Every compact smooth field supplies its weak jets by a constant
approximating sequence. -/
def of_contDiff_compact (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    H3Approximation f (fun i => spatialPartial i f)
      (fun i j => spatialPartial i (spatialPartial j f))
      (fun i j k => spatialPartial i (spatialPartial j (spatialPartial k f))) where
  memLp := smooth_compact_memLp hf hc
  derivative_memLp := fun i => smooth_compact_memLp (spatial_partial_contDiff hf i)
    (hc.fderiv_apply ℝ (coordinateVector i))
  approx := fun _ => f
  smooth := fun _ => hf
  compact := fun _ => hc
  approx_memLp := fun _ => smooth_compact_memLp hf hc
  derivative_approx_memLp := fun _ i => smooth_compact_memLp (spatial_partial_contDiff hf i)
    (hc.fderiv_apply ℝ (coordinateVector i))
  tendsto := tendsto_const_nhds
  derivative_tendsto := fun _ => tendsto_const_nhds
  second_memLp := fun i j => smooth_compact_memLp
    (spatial_partial_contDiff (spatial_partial_contDiff hf j) i)
    ((hc.fderiv_apply ℝ (coordinateVector j)).fderiv_apply ℝ (coordinateVector i))
  third_memLp := fun i j k => smooth_compact_memLp
    (spatial_partial_contDiff (spatial_partial_contDiff (spatial_partial_contDiff hf k) j) i)
    (((hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector j)).fderiv_apply ℝ (coordinateVector i))
  second_approx_memLp := fun _ i j => smooth_compact_memLp
    (spatial_partial_contDiff (spatial_partial_contDiff hf j) i)
    ((hc.fderiv_apply ℝ (coordinateVector j)).fderiv_apply ℝ (coordinateVector i))
  third_approx_memLp := fun _ i j k => smooth_compact_memLp
    (spatial_partial_contDiff (spatial_partial_contDiff (spatial_partial_contDiff hf k) j) i)
    (((hc.fderiv_apply ℝ (coordinateVector k)).fderiv_apply ℝ (coordinateVector j)).fderiv_apply ℝ (coordinateVector i))
  second_tendsto := fun _ _ => tendsto_const_nhds
  third_tendsto := fun _ _ _ => tendsto_const_nhds

end H3Approximation

end NavierStokesR3.H3Comparison
