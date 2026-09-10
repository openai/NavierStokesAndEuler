import NavierStokes.SharpPhysicalCarrier

noncomputable section
namespace NavierStokes.SharpLogWeights
open PhysicalGraphBounds

/-- Dyadic slow powers become a polynomial in the physical logarithm,
without sacrificing any power of the physical scale. -/
theorem slow_power_log_bound (e : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ,
      0 < q → q/2 ≤ ChartScales.Q n →
      ChartScales.S n^e ≤ C*(1+|Real.log q|)^P := by
  let D := (Real.log 2+1)/Real.log 2
  let P := ⌈2*e⌉₊
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D^P, pow_pos hD P, P, ?_⟩
  intro n hn q hq hlo
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlogQ : Real.log (ChartScales.Q n) = -(n:ℝ)*Real.log 2 := by
    simp only [ChartScales.Q, SlotColoring.dyadicQ, Real.log_rpow (by norm_num : (0:ℝ)<2)]
  have hl := Real.log_le_log (by positivity : 0 < q/2) hlo
  rw [Real.log_div hq.ne' (by norm_num : (2:ℝ)≠0), hlogQ] at hl
  have hnlog : (n:ℝ) ≤ D*(1+|Real.log q|) := by
    dsimp [D]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlog).mpr
    nlinarith [neg_le_abs (Real.log q), abs_nonneg (Real.log q)]
  calc
    ChartScales.S n^e = (n:ℝ)^(2*e) := by
      unfold ChartScales.S
      rw [← Real.rpow_natCast_mul (show 0 ≤ (n:ℝ) by positivity)]
      norm_num
    _ ≤ (n:ℝ)^(P:ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil _)
    _ = (n:ℝ)^P := Real.rpow_natCast _ _
    _ ≤ (D*(1+|Real.log q|))^P := pow_le_pow_left₀ (by positivity) hnlog P
    _ = _ := mul_pow _ _ _

/-- Preserve the exact real exponent while comparing a dyadic chart with
its physical scale and converting the remaining slow factor to logarithms. -/
theorem chart_weight_bound (g e : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ,
      0 < q → q/2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2*q →
      ChartScales.Q n^g * ChartScales.S n^e ≤ C*q^g*(1+|Real.log q|)^P := by
  obtain ⟨D,hD,P,hslow⟩ := slow_power_log_bound e
  refine ⟨2^|g| * D, by positivity, P, ?_⟩
  intro n hn q hq hlo hhi
  calc
    _ ≤ (2^|g| * q^g)*(D*(1+|Real.log q|)^P) :=
      mul_le_mul (comparable_rpow (ChartScales.Q_pos n) hq hlo hhi g)
        (hslow n hn q hq hlo) (Real.rpow_nonneg (sq_nonneg _) _) (by positivity)
    _ = _ := by ring

end NavierStokes.SharpLogWeights
