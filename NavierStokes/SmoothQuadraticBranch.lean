import NavierStokes.SmoothMomentRepair
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Smoothness of a continuous quadratic correction branch, including on
closed parameter sets. The implicit function theorem is applied in the
universal coefficient space, so no extension of the parameter data is needed. -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.SmoothQuadraticBranch

variable {P D E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous solution of a regular implicit equation inherits all the
within-parameter derivatives of its data. -/
theorem continuous_branch_contDiffOn [CompleteSpace D] [CompleteSpace E]
    {S : Set P} (F : D × E → E)
    (hF : ContDiff ℝ ∞ F) (data : P → D) (c : P → E)
    (hdata : ContDiffOn ℝ ∞ data S) (hc : ContinuousOn c S)
    (heq : ∀ p ∈ S, F (data p, c p) = 0)
    (hinv : ∀ p ∈ S,
      (fderiv ℝ F (data p, c p) ∘L ContinuousLinearMap.inr ℝ D E).IsInvertible) :
    ContDiffOn ℝ ∞ c S := by
  intro p hp
  have hFp := hF.contDiffAt (x := (data p, c p))
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let g : D → E := hFp.implicitFunction hn (hinv p hp)
  have hg : ContDiffAt ℝ ∞ g (data p) :=
    hFp.contDiffAt_implicitFunction hn (hinv p hp)
  have ht : Tendsto (fun x => (data x, c x)) (𝓝[S] p) (𝓝 (data p, c p)) :=
    (hdata p hp).continuousWithinAt.prodMk (hc p hp)
  have hloc := ht.eventually (hFp.eventually_apply_eq_iff_implicitFunction hn (hinv p hp))
  have hagree : c =ᶠ[𝓝[S] p] (fun x => g (data x)) := by
    filter_upwards [hloc, self_mem_nhdsWithin] with x hx hxs
    exact (hx.mp ((heq x hxs).trans (heq p hp).symm)).symm
  exact (hg.comp_contDiffWithinAt p (hdata p hp)).congr_of_eventuallyEq_of_mem hagree hp

open SmoothMomentRepair

/-- The universal quadratic residual in coefficients, debt, and correction. -/
def residual (z : RepairData E × E) : E :=
  z.1.1.1 z.2 + z.1.1.2 z.2 z.2 - z.1.2

theorem residual_contDiff : ContDiff ℝ ∞ (residual : RepairData E × E → E) :=
  ((contDiff_fst.fst.fst.clm_apply contDiff_snd).add
    ((contDiff_fst.fst.snd.clm_apply contDiff_snd).clm_apply contDiff_snd)).sub
    contDiff_fst.snd

/-- Its correction derivative is the actual linearized moment operator. -/
theorem residual_partial (z : RepairData E) (c : E) :
    fderiv ℝ residual (z, c) ∘L ContinuousLinearMap.inr ℝ (RepairData E) E =
      z.1.1 + z.1.2 c + z.1.2.flip c := by
  have hres := (residual_contDiff.differentiable (by simp) (z, c)).hasFDerivAt
  have hslice := hres.comp c (hasFDerivAt_prodMk_right z c)
  have hquad := (z.1.2.hasFDerivAt (x := c)).clm_apply (hasFDerivAt_id c)
  have hpoly := ((z.1.1.hasFDerivAt (x := c)).add hquad).sub_const z.2
  have heq := hslice.unique hpoly
  simpa [residual, ContinuousLinearMap.comp_id, add_assoc] using heq

/-- Smooth coefficient and debt families give a smooth continuous solution
branch whenever the actual correction linearization is invertible. -/
theorem continuous_quadratic_branch_contDiffOn [CompleteSpace E] {S : Set P}
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E) (d c : P → E)
    (hB : ContDiffOn ℝ ∞ B S) (hA : ContDiffOn ℝ ∞ A S)
    (hd : ContDiffOn ℝ ∞ d S) (hc : ContinuousOn c S)
    (heq : ∀ p ∈ S, B p (c p) + A p (c p) (c p) = d p)
    (hinv : ∀ p ∈ S, (B p + A p (c p) + (A p).flip (c p)).IsInvertible) :
    ContDiffOn ℝ ∞ c S := by
  apply continuous_branch_contDiffOn residual residual_contDiff
    (fun p => ((B p, A p), d p)) c ((hB.prodMk hA).prodMk hd) hc
  · intro p hp
    exact sub_eq_zero.mpr (heq p hp)
  · intro p hp
    rw [residual_partial]
    exact hinv p hp

end NavierStokes.SmoothQuadraticBranch
