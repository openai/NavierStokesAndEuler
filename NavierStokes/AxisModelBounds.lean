import NavierStokes.AxisSeries

/-!
# The numerical bounds for the axis comparison profile

The profile in `axis:model-series` is an actual convergent series.  The
following bounds retain the rational lower bound in `axis:model-positive`,
including its stated decimal consequence, on the whole interval `[0, 4.1]`.
-/

noncomputable section

namespace NavierStokes.AxisModelBounds

/-- The comparison function `f₀` in the axis construction. -/
def model (z : ℝ) : ℝ := AxisSeries.profile 1 z

theorem model_eq_series (z : ℝ) :
    model z = ∑' n : ℕ,
      (-z / 2) ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  simpa only [model, neg_mul, one_mul] using AxisSeries.profile_eq_tsum 1 z

/-- The cubic truncation is bounded below by its exact endpoint value. -/
theorem cubicLower_ge_endpoint (t : ℝ) (ht : t ≤ 41 / 20) :
    (305719 / 1152000 : ℝ) ≤ AxisProfile.cubicLower t := by
  have hd : 0 ≤ 41 / 20 - t := sub_nonneg.mpr ht
  have h2 : 0 ≤ (41 / 20 - t) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ (41 / 20 - t) ^ 3 := pow_nonneg hd _
  have hidentity : AxisProfile.cubicLower t =
      AxisProfile.cubicLower (41 / 20) +
      (1 / 2 - (41 / 20) / 6 + (41 / 20) ^ 2 / 48) * (41 / 20 - t) +
      (1 / 12 - (41 / 20) / 48) * (41 / 20 - t) ^ 2 +
      (41 / 20 - t) ^ 3 / 144 := by
    unfold AxisProfile.cubicLower
    ring
  norm_num [AxisProfile.cubicLower] at hidentity
  unfold AxisProfile.cubicLower
  nlinarith

theorem bessel_one_lower (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 41 / 20) :
    (305719 / 1152000 : ℝ) ≤ AxisSeries.bessel 1 t :=
  (cubicLower_ge_endpoint t ht).trans (AxisSeries.cubic_lower_le_bessel t ht0 ht)

/-- The full bounds hold uniformly for every `0 ≤ χ ≤ 1`. -/
theorem profile_bounds (χ Y : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10) :
    (305719 / 1152000 : ℝ) ≤ AxisSeries.profile χ Y ∧
      AxisSeries.profile χ Y ≤ 1 := by
  have ht0 : 0 ≤ (χ / 2) * Y := mul_nonneg (div_nonneg hχ0 (by norm_num)) hY0
  have ht : (χ / 2) * Y ≤ 41 / 20 := by nlinarith
  exact ⟨bessel_one_lower _ ht0 ht,
    AxisSeries.bessel_one_le_one _ ht0 (by linarith)⟩

/-- The exact rational and decimal bounds printed for `f₀`. -/
theorem model_bounds (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 41 / 10) :
    (53 / 200 : ℝ) < (305719 / 1152000 : ℝ) ∧
      (305719 / 1152000 : ℝ) ≤ model z ∧ model z ≤ 1 := by
  exact ⟨by norm_num, profile_bounds 1 z (by norm_num) (by norm_num) hz0 hz1⟩

end NavierStokes.AxisModelBounds
