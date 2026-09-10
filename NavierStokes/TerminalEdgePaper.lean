import NavierStokes.TerminalEdgeFactor

/-! The lower weighted estimate for the actual terminal stress. -/

noncomputable section

open Set

namespace NavierStokes.TerminalEdgePaper

open TerminalEdgeFactor OutgoingTail

/-- The complete stress has the printed exponential-over-cubic lower
bound on one collar, uniformly through both endpoints of the parameter
interval. All constants depend only on the fixed profile data. -/
theorem profileStress_lower_bound {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      ∀ x : ℝ, 0 < x → x < ε →
        c * FlatCutoff.edge 4 x / x ^ 3 ≤ ‖profileStress C d y0 (η, x)‖ := by
  obtain ⟨ε, c, hε, hc, hb⟩ := profile_uniform_cone hC d y0
  refine ⟨ε, c, hε, hc, ?_⟩
  intro η hη x hx hxε
  have ha := (hb η hη x (by simpa only [abs_of_pos hx] using hxε)).1
  have he : 0 ≤ FlatCutoff.edge 4 x / x ^ 3 :=
    (div_pos (FlatCutoff.edge_pos 4 hx) (pow_pos hx _)).le
  calc
    c * FlatCutoff.edge 4 x / x ^ 3 = (FlatCutoff.edge 4 x / x ^ 3) * c := by ring
    _ ≤ (FlatCutoff.edge 4 x / x ^ 3) * profileAngularFactor C d y0 (η, x) :=
      mul_le_mul_of_nonneg_left ha he
    _ = profileAngularStress C d y0 (η, x) :=
      (profileAngularStress_factorization C d y0 (η, x)).symm
    _ ≤ |profileAngularStress C d y0 (η, x)| := le_abs_self _
    _ ≤ ‖profileStress C d y0 (η, x)‖ := by
      exact (norm_fst_le (profileStress C d y0 (η, x)))

end NavierStokes.TerminalEdgePaper
