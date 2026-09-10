import NavierStokes.R3.H3Approximation

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem spatialPartial_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    spatialPartial i (f - g) = spatialPartial i f - spatialPartial i g := by
  funext x
  exact congrArg (fun L : Space →L[ℝ] E => L (coordinateVector i))
    (fderiv_sub (hf.differentiable (by simp) x) (hg.differentiable (by simp) x))

theorem spatialPartial_two_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i j : Fin 3) :
    spatialPartial i (spatialPartial j (f - g)) =
      spatialPartial i (spatialPartial j f) - spatialPartial i (spatialPartial j g) := by
  rw [spatialPartial_sub_smooth hf hg j]
  exact spatialPartial_sub_smooth (spatial_partial_contDiff hf j)
    (spatial_partial_contDiff hg j) i

theorem spatialPartial_three_sub_smooth {f g : Space → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i j k : Fin 3) :
    spatialPartial i (spatialPartial j (spatialPartial k (f - g))) =
      spatialPartial i (spatialPartial j (spatialPartial k f)) -
        spatialPartial i (spatialPartial j (spatialPartial k g)) := by
  rw [spatialPartial_two_sub_smooth hf hg j k]
  exact spatialPartial_sub_smooth
    (spatial_partial_contDiff (spatial_partial_contDiff hf k) j)
    (spatial_partial_contDiff (spatial_partial_contDiff hg k) j) i

def H1Approximation.sub {f g : Space → E} {df dg : Fin 3 → Space → E}
    (hf : H1Approximation f df) (hg : H1Approximation g dg) :
    H1Approximation (f - g) (df - dg) where
  memLp := hf.memLp.sub hg.memLp
  derivative_memLp := fun i => (hf.derivative_memLp i).sub (hg.derivative_memLp i)
  approx := fun n => hf.approx n - hg.approx n
  smooth := fun n => (hf.smooth n).sub (hg.smooth n)
  compact := fun n => (hf.compact n).sub (hg.compact n)
  approx_memLp := fun n => (hf.approx_memLp n).sub (hg.approx_memLp n)
  derivative_approx_memLp := fun n i => by
    rw [spatialPartial_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.derivative_approx_memLp n i).sub (hg.derivative_approx_memLp n i)
  tendsto := by
    simpa only [MemLp.toLp_sub hf.memLp hg.memLp,
      MemLp.toLp_sub (hf.approx_memLp _) (hg.approx_memLp _)] using hf.tendsto.sub hg.tendsto
  derivative_tendsto := fun i => by
    simpa only [spatialPartial_sub_smooth (hf.smooth _) (hg.smooth _), Pi.sub_apply,
      MemLp.toLp_sub (hf.derivative_memLp i) (hg.derivative_memLp i),
      MemLp.toLp_sub (hf.derivative_approx_memLp _ i) (hg.derivative_approx_memLp _ i)] using
      (hf.derivative_tendsto i).sub (hg.derivative_tendsto i)

def H3Approximation.sub {f g : Space → E} {df dg : Fin 3 → Space → E}
    {ddf ddg : Fin 3 → Fin 3 → Space → E}
    {dddf dddg : Fin 3 → Fin 3 → Fin 3 → Space → E}
    (hf : H3Approximation f df ddf dddf) (hg : H3Approximation g dg ddg dddg) :
    H3Approximation (f - g) (df - dg) (ddf - ddg) (dddf - dddg) where
  toH1Approximation := hf.toH1Approximation.sub hg.toH1Approximation
  second_memLp := fun i j => (hf.second_memLp i j).sub (hg.second_memLp i j)
  third_memLp := fun i j k => (hf.third_memLp i j k).sub (hg.third_memLp i j k)
  second_approx_memLp := fun n i j => by
    change MemLp (spatialPartial i (spatialPartial j (hf.approx n - hg.approx n))) 2 volume
    rw [spatialPartial_two_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.second_approx_memLp n i j).sub (hg.second_approx_memLp n i j)
  third_approx_memLp := fun n i j k => by
    change MemLp (spatialPartial i (spatialPartial j (spatialPartial k
      (hf.approx n - hg.approx n)))) 2 volume
    rw [spatialPartial_three_sub_smooth (hf.smooth n) (hg.smooth n)]
    exact (hf.third_approx_memLp n i j k).sub (hg.third_approx_memLp n i j k)
  second_tendsto := fun i j => by
    simpa only [H1Approximation.sub, spatialPartial_two_sub_smooth (hf.smooth _) (hg.smooth _),
      Pi.sub_apply, MemLp.toLp_sub (hf.second_memLp i j) (hg.second_memLp i j),
      MemLp.toLp_sub (hf.second_approx_memLp _ i j) (hg.second_approx_memLp _ i j)] using
      (hf.second_tendsto i j).sub (hg.second_tendsto i j)
  third_tendsto := fun i j k => by
    simpa only [H1Approximation.sub, spatialPartial_three_sub_smooth (hf.smooth _) (hg.smooth _),
      Pi.sub_apply, MemLp.toLp_sub (hf.third_memLp i j k) (hg.third_memLp i j k),
      MemLp.toLp_sub (hf.third_approx_memLp _ i j k) (hg.third_approx_memLp _ i j k)] using
      (hf.third_tendsto i j k).sub (hg.third_tendsto i j k)

end NavierStokesR3.H3Comparison
