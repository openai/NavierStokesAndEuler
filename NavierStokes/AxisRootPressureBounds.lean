import NavierStokes.NaturalAxisRange

/-! # Pressure-scaled positivity at the actual natural-axis root -/

noncomputable section

namespace NavierStokes.AxisRootPressureBounds

open Set NaturalAxisData

/-- The root margin retains the square of the pressure-prefix amplitude. -/
theorem Z_at_root_pressure_lower {h j η B : ℝ} {P : ℝ → ℝ}
    (p : NaturalAxisRange.Parameters h j) (hB : 2 ≤ B)
    (hη : η ∈ Ioo (-j / 4) (-j / 5)) (hz : H h j η = 0)
    (hP : P η ≤ -(B ^ 2 / 4)) (hP' : deriv P η ≤ 0) :
    j * B ^ 2 / 20 < Z h j P η := by
  have hηn : η < 0 := by linarith [hη.2, p.j_pos]
  have hI : η ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη.1, hη.2, p.j_pos, p.j_le]
  have hU : 0 < U j η := by dsimp [U]; linarith [hη.1]
  have hUj : U j η < j / 5 := by dsimp [U]; linarith [hη.2]
  have hrU : -η * U j η ≤ U j η := by
    simpa using mul_le_mul_of_nonneg_right (show -η ≤ 1 by linarith [hI.1]) hU.le
  have hfactor : 1 - 2 * η * U j η ≤ 2 := by nlinarith [p.j_le]
  have hadverse : (1 - 2 * η * U j η) * U j η < 2 * j / 5 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfactor hU.le) (by linarith)
  have hBsq : (4 : ℝ) ≤ B ^ 2 := by nlinarith
  have hpressure := mul_le_mul_of_nonpos_left hP hηn.le
  have hroot := mul_lt_mul_of_pos_right hη.2 (show 0 < B ^ 2 by positivity)
  have hcore : j * B ^ 2 / 10 < -(1 - 2 * η * U j η) * U j η + 4 * η * P η := by
    have hjB := mul_le_mul_of_nonneg_left hBsq p.j_pos.le
    nlinarith
  have hderiv : d η * deriv P η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (d_nonneg hI) hP'
  calc
    j * B ^ 2 / 20 ≤ A h * (j * B ^ 2 / 10) := by
      have hm := mul_nonneg (show 0 ≤ A h - 1 / 2 by
        linarith [(NaturalAxisRange.A_bounds p).1])
        (mul_nonneg p.j_pos.le (sq_nonneg B))
      nlinarith
    _ < A h * (-(1 - 2 * η * U j η) * U j η + 4 * η * P η) :=
      mul_lt_mul_of_pos_left hcore (NaturalAxisRange.A_pos p)
    _ ≤ Z h j P η := by
      unfold Z
      rw [hz]
      nlinarith

/-- The actual integral pressure supplies the pressure-scaled root margin,
with the root and its uniqueness both constructed rather than assumed. -/
theorem ideal_prefix_root_pressure_lower {h j : ℝ}
    (p : NaturalAxisRange.Parameters h j) {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j * B ^ 2 / 20 < Z h j (PressureDatum.pressure g a) η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  obtain ⟨η₀, hη₀, hz, huniq⟩ := NaturalAxisRange.exists_unique_root p
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_pos, p.j_le]
  have hn : η₀ < 0 := by linarith [hη₀.2, p.j_pos]
  have hs : η₀ ^ 2 ≤ 1 := by nlinarith [hI.1, hI.2]
  have hi : 1 / 2 ≤ (1 + η₀ ^ 2)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (show (0 : ℝ) < 1 + η₀ ^ 2 by positivity)).mpr
    linarith
  have hi2 : (1 / 4 : ℝ) ≤ ((1 + η₀ ^ 2)⁻¹) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hi2 (sq_nonneg B)
  have hp0 : PressureDatum.pressure g a η₀ ≤ -(B ^ 2 / 4) := by
    have hb := PressureDatum.pressure_le_of_ideal_prefix hp hg ha η₀
    nlinarith
  exact ⟨η₀, hη₀, hz, Z_at_root_pressure_lower p hB hη₀ hz hp0
    ((pressureData_of_ideal_prefix hp hB hg ha).deriv_nonpos hI hn), huniq⟩

end NavierStokes.AxisRootPressureBounds
