import NavierStokes.SmoothMomentRepair
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section

namespace NavierStokes.QuadraticLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative in the correction variable is invertible throughout the
quantitative correction ball, by its actual Neumann-series inverse. -/
theorem isInvertible (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (c : E)
    (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q)
    (hB : ‖B.symm.toContinuousLinearMap‖ ≤ ν) (hA : ‖A‖ ≤ q)
    (hc : ‖c‖ ≤ 2 * ν * δ) (hsmall : 8 * ν^2 * q * δ ≤ 1) :
    (B.toContinuousLinearMap + A c + A.flip c).IsInvertible := by
  let P : E →L[ℝ] E := B.symm.toContinuousLinearMap.comp (A c + A.flip c)
  have hflip : ‖A.flip‖ = ‖A‖ := ContinuousLinearMap.opNorm_flip A
  have hnorm : ‖P‖ ≤ 4 * ν^2 * q * δ := by
    calc
      ‖P‖ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖A c + A.flip c‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ν * (‖A c‖ + ‖A.flip c‖) :=
        mul_le_mul hB (norm_add_le _ _) (norm_nonneg _) hν
      _ ≤ ν * (‖A‖*‖c‖ + ‖A‖*‖c‖) := by
        apply mul_le_mul_of_nonneg_left _ hν
        apply add_le_add (A.le_opNorm c)
        simpa only [hflip] using A.flip.le_opNorm c
      _ ≤ ν * (q*(2*ν*δ) + q*(2*ν*δ)) := by
        apply mul_le_mul_of_nonneg_left _ hν
        exact add_le_add (mul_le_mul hA hc (norm_nonneg _) hq)
          (mul_le_mul hA hc (norm_nonneg _) hq)
      _ = _ := by ring
  have hlt : ‖-P‖ < 1 := by rw [norm_neg]; linarith
  let u : (E →L[ℝ] E)ˣ := Units.oneSub (-P) hlt
  refine ⟨(ContinuousLinearEquiv.ofUnit u).trans B, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  change B ((u : E →L[ℝ] E) z) = _
  rw [Units.val_oneSub]
  simp only [sub_neg_eq_add, add_apply, one_apply_eq_self,
    map_add, P, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  abel

end NavierStokes.QuadraticLinearization
