import NavierStokes.NilpotentVolterra

noncomputable section

namespace NavierStokes.NilpotentVolterra

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integrating factor cancels the singular zeroth-order coefficient. -/
theorem integratingFactor_hasDerivAt (c : ℕ) {W g : ℝ → E} {r : ℝ}
    (hr : r ≠ 0) (hW : HasDerivAt W (g r - ((c : ℝ) / r) • W r) r) :
    HasDerivAt (fun s => s ^ c • W s) (r ^ c • g r) r := by
  have hfactor : (c : ℝ) * r ^ (c - 1) = r ^ c * ((c : ℝ) / r) := by
    cases c with
    | zero => simp
    | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
  convert (hasDerivAt_pow c r).fun_smul hW using 1
  rw [smul_sub, smul_smul, hfactor]
  exact (sub_add_cancel _ _).symm

/-- Every continuous zero-axis solution of the regular singular equation is
the actual Volterra integral, including at both ends of the radial interval. -/
theorem eq_regularPrimitive_of_hasDerivAt [CompleteSpace E] (c : ℕ)
    {R : ℝ} {W g : ℝ → E}
    (hW : ContinuousOn W (Icc (0 : ℝ) R))
    (hg : ContinuousOn g (Icc (0 : ℝ) R)) (hW0 : W 0 = 0)
    (hderiv : ∀ r ∈ Ioo (0 : ℝ) R,
      HasDerivAt W (g r - ((c : ℝ) / r) • W r) r)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) R) :
    W r = regularPrimitive c g r := by
  by_cases hr0 : r = 0
  · simpa only [hr0, regularPrimitive_zero] using hW0
  have hsub : Icc (0 : ℝ) r ⊆ Icc (0 : ℝ) R := Icc_subset_Icc le_rfl hr.2
  have hcont : ContinuousOn (fun s => s ^ c • W s) (Icc (0 : ℝ) r) :=
    (continuous_id.pow c).continuousOn.smul (hW.mono hsub)
  have hint : IntervalIntegrable (fun s => s ^ c • g s) volume 0 r :=
    ((continuous_id.pow c).continuousOn.smul (hg.mono hsub)).intervalIntegrable_of_Icc hr.1
  have heq : (∫ s in (0 : ℝ)..r, s ^ c • g s) = r ^ c • W r := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 hcont
      (fun s hs => integratingFactor_hasDerivAt c hs.1.ne'
        (hderiv s ⟨hs.1, hs.2.trans_le hr.2⟩)) hint
    simpa only [hW0, smul_zero, sub_zero] using hftc
  rw [regularPrimitive_eq_div c g hr0, heq, inv_smul_smul₀ (pow_ne_zero c hr0)]

end NavierStokes.NilpotentVolterra
