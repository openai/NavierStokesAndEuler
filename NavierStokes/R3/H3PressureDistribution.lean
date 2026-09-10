import NavierStokes.R3.H3Comparison
import NavierStokes.R3.SchwartzCompactApproximation
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Weak derivatives of L² fields and the curl of an arbitrary C¹ pressure
gradient. The pressure itself need not be integrable at infinity. -/

noncomputable section

open Set Filter MeasureTheory LineDeriv
open scoped ContDiff Topology BigOperators SchwartzMap LineDeriv

namespace NavierStokesR3.H3PressureDistribution

open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (spatial_partial_contDiff)
open H3Comparison

abbrev ComplexTest := SchwartzMap Space ℂ
abbrev ComplexL2 := Lp ℂ 2 (volume : Measure Space)
abbrev ComplexDistribution := TemperedDistribution Space ℂ

def distribution (f : ComplexL2) : ComplexDistribution := Lp.toTemperedDistribution f

theorem partial_continuous {f : Space → ℂ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (spatialPartial i f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Compact support is required only of the first factor. -/
theorem compact_integration_by_parts {f g : Space → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    (∫ x, f x * spatialPartial i g x) = -(∫ x, spatialPartial i f x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((partial_continuous hf i).mul hg.continuous).integrable_of_hasCompactSupport
      (hcf.fderiv_apply ℝ (coordinateVector i)).mul_right
  · exact (hf.continuous.mul (partial_continuous hg i)).integrable_of_hasCompactSupport
      hcf.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right
  · intro x _; exact hf.differentiable (by norm_num) x
  · intro x _; exact hg.differentiable (by norm_num) x

theorem partial_partial_eq {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (spatialPartial j f) x =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) := by
  have hdf := (hf.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) x
  change fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector j)) x (coordinateVector i) = _
  rw [fderiv_clm_apply hdf (differentiableAt_const (coordinateVector j))]
  simp

theorem partial_commute {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin 3) : spatialPartial i (spatialPartial j f) = spatialPartial j (spatialPartial i f) := by
  funext x
  rw [partial_partial_eq hf, partial_partial_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- Integration by parts twice puts all second derivatives on the compact
test. Thus only one pressure derivative is used. -/
theorem gradient_compact_test_commute {p ψ : Space → ℂ}
    (hp : ContDiff ℝ 1 p) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (i j : Fin 3) :
    (∫ x, spatialPartial i ψ x * spatialPartial j p x) =
      ∫ x, spatialPartial j ψ x * spatialPartial i p x := by
  calc
    _ = -(∫ x, spatialPartial j (spatialPartial i ψ) x * p x) :=
      compact_integration_by_parts ((spatial_partial_contDiff hψ i).of_le (by simp)) hp
        (hcψ.fderiv_apply ℝ (coordinateVector i)) j
    _ = -(∫ x, spatialPartial i (spatialPartial j ψ) x * p x) := by
      rw [partial_commute hψ j i]
    _ = _ := (compact_integration_by_parts ((spatial_partial_contDiff hψ j).of_le (by simp)) hp
      (hcψ.fderiv_apply ℝ (coordinateVector j)) i).symm

/-- Formula for a distributional derivative, using any L² representative. -/
theorem derivative_toLp_apply {f : Space → ℂ} (hf : MemLp f 2 volume)
    (i : Fin 3) (ψ : ComplexTest) :
    (∂_{coordinateVector i} (distribution (hf.toLp f))) ψ =
      -(∫ x, spatialPartial i (ψ : Space → ℂ) x * f x) := by
  rw [TemperedDistribution.lineDerivOp_apply_apply, distribution, Lp.toTemperedDistribution_apply]
  calc
    (∫ x : Space, (-∂_{coordinateVector i} ψ) x • (hf.toLp f) x) =
        ∫ x : Space, -(spatialPartial i (ψ : Space → ℂ) x * f x) := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
        smul_eq_mul, neg_mul, spatialPartial]
    _ = _ := integral_neg _

/-- For a smooth compact function, the weak derivative is the ordinary one. -/
theorem derivative_toLp_of_compact {f : Space → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (i : Fin 3) :
    ∂_{coordinateVector i} (distribution ((smooth_compact_memLp hf hcf).toLp f)) =
      distribution ((smooth_compact_memLp (spatial_partial_contDiff hf i)
        (hcf.fderiv_apply ℝ (coordinateVector i))).toLp (spatialPartial i f)) := by
  ext ψ
  rw [derivative_toLp_apply, distribution, Lp.toTemperedDistribution_apply]
  have he := compact_integration_by_parts (hf.of_le (by simp))
    ((ψ.smooth ⊤).of_le (by simp)) hcf i
  have hswap : (∫ x, spatialPartial i (ψ : Space → ℂ) x * f x) =
      -(∫ x, (ψ : Space → ℂ) x * spatialPartial i f x) := by
    simpa only [mul_comm] using he
  rw [hswap, neg_neg]
  apply integral_congr_ae
  filter_upwards [(smooth_compact_memLp (spatial_partial_contDiff hf i)
    (hcf.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with x hx
  exact congrArg (fun z : ℂ => ψ x * z) hx.symm

/-- Passing the actual smooth approximation through continuous distributional
differentiation identifies the ordinary weak derivative. -/
theorem H1Approximation.derivative_distribution {f : Space → ℂ}
    {df : Fin 3 → Space → ℂ} (h : H1Approximation f df) (i : Fin 3) :
    ∂_{coordinateVector i} (distribution (h.memLp.toLp f)) =
      distribution ((h.derivative_memLp i).toLp (df i)) := by
  let T : ComplexL2 →L[ℂ] ComplexDistribution := Lp.toTemperedDistributionCLM ℂ volume 2
  have hl := ((lineDerivOpCLM ℂ ComplexDistribution (coordinateVector i)).continuous.comp
    T.continuous).tendsto _ |>.comp h.tendsto
  have hr := T.continuous.tendsto _ |>.comp (h.derivative_tendsto i)
  have he (n : ℕ) :
      ∂_{coordinateVector i} (T ((h.approx_memLp n).toLp (h.approx n))) =
        T ((h.derivative_approx_memLp n i).toLp (spatialPartial i (h.approx n))) :=
    derivative_toLp_of_compact (h.smooth n) (h.compact n) i
  exact tendsto_nhds_unique (hl.congr (fun n => he n)) hr

/-- A C¹ pressure with square-integrable gradient has zero distributional
curl. No global bound, normalization, or integrability of the pressure is
assumed. -/
theorem gradient_curl_free {p : Space → ℂ} (hp : ContDiff ℝ 1 p)
    (hg : ∀ i, MemLp (spatialPartial i p) 2 volume) (i j : Fin 3) :
    ∂_{coordinateVector i} (distribution ((hg j).toLp (spatialPartial j p))) =
      ∂_{coordinateVector j} (distribution ((hg i).toLp (spatialPartial i p))) := by
  apply sub_eq_zero.mp
  ext ψ
  apply SchwartzCompactApproximation.continuous_zero_of_compactSupport
    (F := fun φ =>
      ((∂_{coordinateVector i} (distribution ((hg j).toLp (spatialPartial j p)))) -
        (∂_{coordinateVector j} (distribution ((hg i).toLp (spatialPartial i p))))) φ)
  · exact ContinuousLinearMap.continuous _
  · intro φ hcφ
    change (∂_{coordinateVector i} (distribution ((hg j).toLp (spatialPartial j p)))) φ -
      (∂_{coordinateVector j} (distribution ((hg i).toLp (spatialPartial i p)))) φ = 0
    rw [derivative_toLp_apply, derivative_toLp_apply,
      gradient_compact_test_commute hp (φ.smooth ⊤) hcφ i j, sub_self]

end NavierStokesR3.H3PressureDistribution
