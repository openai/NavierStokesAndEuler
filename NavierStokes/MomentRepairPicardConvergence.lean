import NavierStokes.SmoothMomentRepair

/-! # Convergence of the actual quadratic moment-repair iterates

The Banach fixed-point theorem is applied to the explicit correction iteration
on its invariant quantitative ball. The returned solution is the limit of
those iterates starting from zero.
-/

noncomputable section

open Set Function Filter
open scoped Topology NNReal

namespace NavierStokes.MomentRepairPicardConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The same explicit Picard sequence converges to an exact small correction.
This identifies the correction across compatible Banach-space realizations. -/
theorem exists_small_solution_with_iterates
    (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (d : E)
    (hsmall : 8 * ‖B.symm.toContinuousLinearMap‖ ^ 2 * ‖A‖ * ‖d‖ ≤ 1) :
    ∃ c : E, ‖c‖ ≤ 2 * ‖B.symm.toContinuousLinearMap‖ * ‖d‖ ∧
      B c + A c c = d ∧
      Tendsto (fun n : ℕ => (MomentRepair.correctionIteration B (fun x => A x x) d)^[n] 0)
        atTop (𝓝 c) := by
  let β : ℝ := ‖B.symm.toContinuousLinearMap‖
  let r : ℝ := 2 * β * ‖d‖
  let Q : E → E := fun c => A c c
  let f : E → E := MomentRepair.correctionIteration B Q d
  let S : Set E := Metric.closedBall 0 r
  have hβ : 0 ≤ β := norm_nonneg _
  have hr : 0 ≤ r := mul_nonneg (mul_nonneg (by norm_num) hβ) (norm_nonneg d)
  have hB : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖ :=
    fun x => B.symm.toContinuousLinearMap.le_opNorm x
  have hQnorm : ∀ x, ‖x‖ ≤ r → ‖Q x‖ ≤ ‖A‖ * ‖x‖ ^ 2 :=
    fun x _ => SmoothMomentRepair.quadratic_norm_le A x
  have hQdiff : ∀ x, ‖x‖ ≤ r → ∀ y, ‖y‖ ≤ r →
      ‖Q x - Q y‖ ≤ ‖A‖ * (‖x‖ + ‖y‖) * ‖x - y‖ :=
    fun x _ y _ => SmoothMomentRepair.quadratic_sub_le A x y
  have hsmall' : 4 * β * ‖A‖ * r ≤ 1 := by
    convert! hsmall using 1
    dsimp only [r, β]
    ring
  have hmaps : MapsTo f S S := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact MomentRepair.correctionIteration_norm_le B Q d β ‖A‖ r hβ (norm_nonneg A) hr
      hB hQnorm hsmall' le_rfl x
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx)
  have hcontract : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict f S S) := by
    refine ⟨(div_lt_one (by norm_num : (0 : ℝ≥0) < 2)).mpr (by norm_num),
      LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (f x) (f y) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (x : E) (y : E)
    simp only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    exact MomentRepair.correctionIteration_sub_le B Q d β ‖A‖ r hβ (norm_nonneg A)
      hB hQdiff hsmall' x y
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using x.property)
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using y.property)
  have hcomplete : IsComplete S := Metric.isClosed_closedBall.isComplete
  have hzero : (0 : E) ∈ S := by simpa [S] using hr
  obtain ⟨c, hcS, hfix, hconv, _⟩ :=
    ContractingWith.exists_fixedPoint' hcomplete hmaps hcontract hzero (edist_ne_top 0 (f 0))
  have hc : ‖c‖ ≤ r := by
    simpa only [S, Metric.mem_closedBall, dist_zero_right] using hcS
  have heq : B c + Q c = d := by
    apply eq_sub_iff_add_eq.mp
    have h := congrArg B hfix
    simpa only [f, MomentRepair.correctionIteration, ContinuousLinearEquiv.apply_symm_apply] using h.symm
  exact ⟨c, hc, heq, hconv⟩

end NavierStokes.MomentRepairPicardConvergence
