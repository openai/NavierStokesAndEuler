import NavierStokes.HeatProfileExtension

/-! Exact endpoint jets and quantitative small-argument estimates for the
gamma integral in `heat:exterior`. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.AppendixHeatResults

open RadialHeatProfile

/-- The rising factorial used in the manuscript. -/
def rising (b : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (b + k)

theorem rising_zero (b : ℝ) : rising b 0 = 1 := by simp [rising]

theorem rising_succ (b : ℝ) (n : ℕ) :
    rising b (n + 1) = rising b n * (b + n) := by
  simp [rising, Finset.prod_range_succ]

theorem rising_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 ≤ rising b n := by
  apply Finset.prod_nonneg
  intro k _
  positivity

theorem rising_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < rising b n := by
  apply Finset.prod_pos
  intro k _
  positivity

theorem rising_mono {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) (n : ℕ) :
    rising b n ≤ rising c n := by
  apply Finset.prod_le_prod
  · intro k _; positivity
  · intro k _; linarith

theorem rising_succ_left (b : ℝ) (n : ℕ) :
    rising b (n + 1) = b * rising (1 + b) n := by
  induction n with
  | zero => simp [rising_succ, rising_zero]
  | succ n ih =>
    rw [rising_succ b (n + 1), ih, rising_succ (1 + b) n]
    push_cast
    ring

theorem derivativeCoeff_eq_rising (h : ℝ) (n : ℕ) :
    derivativeCoeff (1 + h) n = (-1 : ℝ) ^ n * rising h n := by
  induction n with
  | zero => simp [derivativeCoeff, rising_zero]
  | succ n ih => rw [derivativeCoeff, ih, rising_succ, pow_succ]; ring

theorem gamma_add_nat {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n) = Real.Gamma a * rising a n := by
  induction n with
  | zero => simp [rising_zero]
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      Real.Gamma_add_one (by positivity : a + (n : ℝ) ≠ 0), ih, rising_succ]
    ring

/-- The displayed endpoint formula holds for actual one-sided derivatives,
not merely a recursively specified formal series. -/
theorem endpoint_derivatives {h : ℝ} (hh : 0 < h) (n : ℕ) :
    iteratedDerivWithin n (profile (1 + h)) (Ici 0) 0 =
      (-1 : ℝ) ^ n * rising h n * rising (1 + h) n := by
  rw [iteratedDerivWithin_profile (by linarith : 1 < 1 + h) n le_rfl,
    profileJet, moment_zero (by linarith : 1 < 1 + h), derivativeCoeff_eq_rising,
    gamma_add_nat (by linarith : 0 < 1 + h)]
  have hg := (Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)).ne'
  field_simp

/-- Every derivative is bounded by the magnitude of its endpoint value. -/
theorem derivative_bound_rising {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) (n : ℕ) :
    |iteratedDerivWithin n (profile (1 + h)) (Ici 0) z| ≤
      rising h n * rising (1 + h) n := by
  have hb := profile_derivative_bound (a := 1 + h) (by linarith) n hz
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)
  rw [derivativeCoeff_eq_rising, gamma_add_nat (by linarith : 0 < 1 + h),
    abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (rising_nonneg hh.le n), abs_of_pos (inv_pos.mpr hg)] at hb
  convert hb using 1
  field_simp

/-- The positive-order jets are uniformly `O(h)` for bounded positive `h`.
The explicit constant is independent of the argument on the whole half-line. -/
theorem uniform_positive_derivative_bound {h h₀ z : ℝ}
    (hh : 0 < h) (hh₀ : h ≤ h₀) (hz : 0 ≤ z) (n : ℕ) :
    |iteratedDerivWithin (n + 1) (profile (1 + h)) (Ici 0) z| ≤
      (rising (1 + h₀) n * rising (1 + h₀) (n + 1)) * h := by
  have hb := derivative_bound_rising hh hz (n + 1)
  rw [rising_succ_left h n] at hb
  calc
    _ ≤ (h * rising (1 + h) n) * rising (1 + h) (n + 1) := hb
    _ ≤ (h * rising (1 + h₀) n) * rising (1 + h₀) (n + 1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (rising_mono (by linarith) (by linarith) n) hh.le
      · exact rising_mono (by linarith) (by linarith) (n + 1)
      · exact rising_nonneg (by linarith) _
      · exact mul_nonneg hh.le (rising_nonneg (by linarith) _)
    _ = _ := by ring

theorem first_endpoint_jet {h : ℝ} (hh : 0 < h) :
    profileJet (1 + h) 1 0 = -h * (1 + h) := by
  rw [← iteratedDerivWithin_profile (by linarith : 1 < 1 + h) 1 le_rfl,
    endpoint_derivatives hh]
  simp [rising]

/-- An explicit derivative bound on the entire nonnegative half-line. -/
theorem second_jet_bound {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profileJet (1 + h) 2 z| ≤ h * (1 + h) ^ 2 * (2 + h) := by
  have hb := profile_derivative_bound (a := 1 + h) (by linarith) 2 hz
  rw [iteratedDerivWithin_profile (by linarith : 1 < 1 + h) 2 hz] at hb
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < 1 + h)
  have he : |(Real.Gamma (1 + h))⁻¹ * derivativeCoeff (1 + h) 2| *
      Real.Gamma (1 + h + (2 : ℕ)) = h * (1 + h) ^ 2 * (2 + h) := by
    rw [gamma_add_nat (by linarith : 0 < 1 + h)]
    have hc : derivativeCoeff (1 + h) 2 = h * (1 + h) := by
      simp [derivativeCoeff]; ring
    rw [hc, abs_of_pos (by positivity)]
    simp only [rising, Finset.prod_range_succ, Finset.range_zero,
      Finset.prod_empty, Nat.cast_zero, Nat.cast_one]
    field_simp
    ring
  exact hb.trans_eq he

theorem first_jet_remainder {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profileJet (1 + h) 1 z + h * (1 + h)| ≤
      h * (1 + h) ^ 2 * (2 + h) * z := by
  have H := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := profileJet (1 + h) 1) (f' := profileJet (1 + h) 2)
    (a := 0) (b := z) (C := h * (1 + h) ^ 2 * (2 + h))
    (fun x hx => (profileJet_hasDerivWithinAt (by linarith : 1 < 1 + h) 1 hx.1).mono
      Icc_subset_Ici_self)
    (fun x hx => by simpa only [Real.norm_eq_abs] using second_jet_bound hh hx.1)
  simpa only [Real.norm_eq_abs, first_endpoint_jet hh, neg_mul, sub_neg_eq_add, sub_zero]
    using H z ⟨hz, le_rfl⟩

/-- The finite Taylor estimate asserted in `heat:small-argument`, with an
explicit remainder constant and no analyticity assumption. -/
theorem small_argument_remainder {h z : ℝ} (hh : 0 < h) (hz : 0 ≤ z) :
    |profile (1 + h) z - 1 + h * (1 + h) * z| ≤
      h * (1 + h) ^ 2 * (2 + h) * z ^ 2 := by
  let B := h * (1 + h) ^ 2 * (2 + h)
  let g := fun x => profile (1 + h) x - 1 + h * (1 + h) * x
  have H := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := g) (f' := fun x => profileJet (1 + h) 1 x + h * (1 + h))
    (a := 0) (b := z) (C := B * z)
    (fun x hx => by
      convert!
        (((profile_hasDerivWithinAt (by linarith : 1 < 1 + h) hx.1).sub_const 1).add
        ((hasDerivWithinAt_id x (Ici 0)).const_mul (h * (1 + h)))).mono
          (Icc_subset_Ici_self : Icc (0 : ℝ) z ⊆ Ici 0) using 1
      simp)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (first_jet_remainder hh hx.1).trans
        (mul_le_mul_of_nonneg_left hx.2.le (by positivity)))
  have hh0 : profile (1 + h) 0 = 1 := profile_zero (by linarith)
  simpa [g, hh0, sub_zero, B, pow_two, mul_assoc] using H z ⟨hz, le_rfl⟩

/-- The constant in the first-order small-argument estimate is uniform when
the positive exponent ranges below any fixed upper bound. -/
theorem uniform_small_argument {h h₀ z : ℝ} (hh : 0 < h) (hh₀ : h ≤ h₀)
    (hz : 0 ≤ z) :
    |profile (1 + h) z - 1| + |z * derivWithin (profile (1 + h)) (Ici 0) z| ≤
      (2 * (1 + h₀)) * h * z := by
  have H₀ := profile_h_sub_one_bound hh hz
  have H₁ := profile_first_derivative_bound (a := 1 + h) (by linarith) hz
  rw [abs_mul, abs_of_nonneg hz]
  have H₂ := mul_le_mul_of_nonneg_left H₁ hz
  have H₃ := mul_le_mul_of_nonneg_right hh₀ (mul_nonneg hh.le hz)
  nlinarith

end NavierStokes.AppendixHeatResults
