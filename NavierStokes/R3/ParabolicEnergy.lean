import NavierStokes.R3.ParabolicDefinitions

/-!
# Energy and blowup under an affine parabolic change of variables

The affine clock fixes time one.  Extension by zero before time zero lets a
uniform kinetic-energy bound pass through the change of variables on the
entire interval starting at zero.
-/

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open ProblemStatement Set MeasureTheory

theorem velocity_energy_bounded {u : VelocityField} {l : ℝ}
    (hu : UniformFiniteEnergy (Ico 0 1) u) (hl : 1 < l) :
    UniformFiniteEnergy (Ico 0 1) (velocity l u) := by
  have hp : 0 < l := lt_trans zero_lt_one hl
  have htime : UniformFiniteEnergy (Ico 0 1)
      (fun z => zeroBefore u (clock l z.1, z.2)) := by
    obtain ⟨E, hE, hu⟩ := hu
    refine ⟨E, hE, ?_⟩
    intro t ht
    by_cases hc : 0 ≤ clock l t
    · simpa only [SquareIntegrableAtTime, kineticEnergy, zeroBefore,
        ite_eq_left hc] using hu (clock l t) ⟨hc, clock_lt_one hp ht.2⟩
    · constructor
      · simp [SquareIntegrableAtTime, zeroBefore, hc]
      · simpa [kineticEnergy, zeroBefore, hc] using hE
  exact htime.spatial_smul l l hp.ne'

theorem velocity_speed_unbounded {u : VelocityField} {l : ℝ}
    (hu : SpeedUnboundedAtOne u) (hl : 1 < l) :
    SpeedUnboundedAtOne (velocity l u) := by
  have hp : 0 < l := lt_trans zero_lt_one hl
  have hq : 0 < l ^ 2 := sq_pos_of_pos hp
  have hq1 : 1 ≤ l ^ 2 := by nlinarith
  intro M hM δ hδ
  obtain ⟨t, x, ht, hδt, hMtx⟩ := hu M hM δ hδ
  let s : ℝ := (t - 1) / l ^ 2 + 1
  have hs1 : s < 1 := by
    dsimp [s]
    have : (t - 1) / l ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith [ht.2]) hq
    linarith
  have hts : t ≤ s := by
    have hprod : (t - 1) * (l ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (by linarith)
    have hd : t - 1 ≤ (t - 1) / l ^ 2 := (le_div_iff₀ hq).2 (by nlinarith)
    dsimp [s]
    linarith
  have hclock : clock l s = t := by
    dsimp [clock, s]
    field_simp
    ring
  refine ⟨s, l⁻¹ • x, ⟨lt_of_lt_of_le ht.1 hts, hs1⟩, lt_of_lt_of_le hδt hts, ?_⟩
  simp only [velocity, pull, hclock, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  rw [zeroBefore_eq_of_nonneg u ht.1.le, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
  have hn : 0 ≤ ‖u (t, x)‖ := norm_nonneg _
  nlinarith

end NavierStokesR3.ParabolicScaling
