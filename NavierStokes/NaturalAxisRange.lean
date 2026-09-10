import NavierStokes.NaturalAxisData

/-! # The full numerical axis parameter range in the current manuscript -/

noncomputable section

namespace NavierStokes.NaturalAxisRange

open Set NaturalAxisData
open scoped ContDiff Topology

/-- The complete printed range, before the subsequent scale and cutoff choices. -/
structure Parameters (h j : ℝ) : Prop where
  h_pos : 0 < h
  h_le : h ≤ 1 / 100
  j_pos : 0 < j
  j_le : j ≤ 1 / 20

/-- Existing selected parameters remain valid without changing their tighter bounds. -/
theorem ofSmall {h j : ℝ} (p : NaturalAxisData.SmallParameters h j) : Parameters h j :=
  ⟨p.h_pos, by linarith [p.h_le], p.j_pos, by linarith [p.j_le]⟩

instance {h j : ℝ} : CoeOut (NaturalAxisData.SmallParameters h j) (Parameters h j) := ⟨ofSmall⟩

theorem D_bounds {h j : ℝ} (p : Parameters h j) :
    49 / 100 ≤ D h ∧ D h < 1 / 2 := by
  unfold D
  constructor <;> linarith [p.h_pos, p.h_le]

theorem D_pos {h j : ℝ} (p : Parameters h j) : 0 < D h := by
  linarith [(D_bounds p).1]

theorem A_bounds {h j : ℝ} (p : Parameters h j) :
    1 / 2 < A h ∧ A h ≤ 51 / 100 := by
  unfold A
  constructor <;> linarith [p.h_pos, p.h_le]

theorem A_pos {h j : ℝ} (p : Parameters h j) : 0 < A h := by
  linarith [(A_bounds p).1]

theorem L_lower_bound {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 49 / 50 ≤ L h η := by
  have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
  dsimp [d, L] at *
  nlinarith [p.h_le]

theorem L_pos {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 0 < L h η := by
  linarith [L_lower_bound p hη]

theorem neg_W_lower_bound {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 287 / 100 ≤ -W h j η := by
  have hDj : 0 ≤ 2 * D h * j :=
    mul_nonneg (mul_nonneg (by norm_num) (D_pos p).le) p.j_pos.le
  have hDjle : 2 * D h * j ≤ j := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - 2 * D h by linarith [(D_bounds p).2]) p.j_pos.le]
  have hηDj : -(2 * D h * j) ≤ 2 * D h * j * η := by
    nlinarith [mul_nonneg hDj (show 0 ≤ η + 1 by linarith [hη.1])]
  have hhη : h * η ^ 2 ≤ h := by
    have hp := mul_nonneg p.h_pos.le (d_nonneg hη)
    dsimp [d] at hp
    nlinarith
  rw [neg_W_formula]
  nlinarith [p.h_le, p.j_le]

theorem neg_W_gt {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) : 14 / 5 < -W h j η := by
  linarith [neg_W_lower_bound p hη]

theorem H_left_neg {h j : ℝ} (p : Parameters h j) : H h j (-j / 4) < 0 := by
  rw [H_at_left]
  have hp := mul_pos (D_pos p) p.j_pos
  linarith

theorem H_right_pos {h j : ℝ} (p : Parameters h j) : 0 < H h j (-j / 5) := by
  rw [H_at_right]
  apply mul_pos (div_pos p.j_pos (by norm_num))
  have hj1 : j ≤ 1 := by linarith [p.j_le]
  have hj2 : j ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hj1) (show 0 ≤ j + 1 by linarith [p.j_pos])]
  nlinarith [(D_bounds p).2]

theorem H_pos_of_nonneg {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hη0 : 0 ≤ η) : 0 < H h j η := by
  rcases eq_or_lt_of_le hη0 with heq | hpos
  · subst η
    simpa [H, U, d] using p.j_pos
  · have hU : 0 ≤ U j η := by dsimp [U]; linarith [p.j_pos]
    exact add_pos_of_pos_of_nonneg (mul_pos (D_pos p) hpos)
      (mul_nonneg (d_nonneg hη) hU)

theorem H_neg_of_le_left {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hleft : η ≤ -j / 4) : H h j η < 0 := by
  have hη0 : η < 0 := by linarith [p.j_pos]
  have hU : U j η ≤ 0 := by dsimp [U]; linarith
  exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (D_pos p) hη0)
    (mul_nonpos_of_nonneg_of_nonpos (d_nonneg hη) hU)

theorem root_negative {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hzero : H h j η = 0) : η < 0 := by
  by_contra hn
  have hp := H_pos_of_nonneg p hη (le_of_not_gt hn)
  linarith

theorem root_unique {h j x y : ℝ} (p : Parameters h j)
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1)
    (hx0 : H h j x = 0) (hy0 : H h j y = 0) : x = y := by
  have hxn := root_negative p hx hx0
  have hyn := root_negative p hy hy0
  have hxy : 0 < x * y := mul_pos_of_neg_of_neg hxn hyn
  have hp : 0 < D h * (1 + x * y) + 4 * d x * d y :=
    add_pos_of_pos_of_nonneg (mul_pos (D_pos p) (by linarith))
      (mul_nonneg (mul_nonneg (by norm_num) (d_nonneg hx)) (d_nonneg hy))
  have hid := cross_identity h j x y
  rw [hx0, hy0] at hid
  have hprod : (x - y) * (D h * (1 + x * y) + 4 * d x * d y) = 0 := by
    linarith
  have heq := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hp)
  linarith

theorem exists_unique_root {h j : ℝ} (p : Parameters h j) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  have hab : -j / 4 ≤ -j / 5 := by linarith [p.j_pos]
  obtain ⟨η₀, hη₀, hz⟩ :=
    intermediate_value_Ioo (f := H h j) hab (H_contDiff h j).continuous.continuousOn
      (show (0 : ℝ) ∈ Ioo (H h j (-j / 4)) (H h j (-j / 5)) from
        ⟨H_left_neg p, H_right_pos p⟩)
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_le, p.j_pos]
  exact ⟨η₀, hη₀, hz, fun η hη hzero => root_unique p hη hI hzero hz⟩

theorem Z_at_root_lower {h j η : ℝ} {P : ℝ → ℝ} (p : Parameters h j)
    (hη : η ∈ Ioo (-j / 4) (-j / 5)) (hz : H h j η = 0)
    (hP : P η ≤ -1) (hP' : deriv P η ≤ 0) : j / 5 < Z h j P η := by
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
  have hpressure := mul_le_mul_of_nonpos_left hP hηn.le
  have hcore : 2 * j / 5 < -(1 - 2 * η * U j η) * U j η + 4 * η * P η := by
    nlinarith [hη.2]
  have hderiv : d η * deriv P η ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (d_nonneg hI) hP'
  calc
    j / 5 ≤ A h * (2 * j / 5) := by
      nlinarith [mul_nonneg (show 0 ≤ A h - 1 / 2 by linarith [(A_bounds p).1]) p.j_pos.le]
    _ < A h * (-(1 - 2 * η * U j η) * U j η + 4 * η * P η) :=
      mul_lt_mul_of_pos_left hcore (A_pos p)
    _ ≤ Z h j P η := by
      unfold Z
      rw [hz]
      nlinarith

theorem exists_root_with_positive_Z {h j : ℝ} {P : ℝ → ℝ}
    (p : Parameters h j) (pP : PressureData P) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j P η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ := by
  obtain ⟨η₀, hη₀, hz, huniq⟩ := exists_unique_root p
  have hI : η₀ ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hη₀.1, hη₀.2, p.j_pos, p.j_le]
  have hn : η₀ < 0 := by linarith [hη₀.2, p.j_pos]
  exact ⟨η₀, hη₀, hz, Z_at_root_lower p hη₀ hz (pP.negative η₀ hI)
    (pP.deriv_nonpos hI hn), huniq⟩

theorem low_Z_has_H_margin {h j : ℝ} {P : ℝ → ℝ}
    (p : Parameters h j) (pP : PressureData P) :
    ∃ m : ℝ, 0 < m ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → m ≤ (H h j η) ^ 2 := by
  obtain ⟨η₀, hη₀, hz, hZpos, huniq⟩ := exists_root_with_positive_Z p pP
  let K : Set ℝ := Icc (-1) 1 ∩ {η | |Z h j P η| ≤ j / 10}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le (Z_continuous h j pP.smooth).abs continuous_const)
  have hnonzero : ∀ η ∈ K, H h j η ≠ 0 := by
    intro η hη hzero
    have heq := huniq η hη.1 hzero
    have hbound : Z h j P η ≤ j / 10 := (le_abs_self _).trans hη.2
    rw [heq] at hbound
    linarith [p.j_pos]
  have hpositive : ∀ η ∈ K, 0 < (H h j η) ^ 2 :=
    fun η hη => sq_pos_of_ne_zero (hnonzero η hη)
  obtain ⟨m, hm, hbound⟩ := hK.exists_forall_le'
    ((H_contDiff h j).continuous.pow 2).continuousOn hpositive
  exact ⟨m, hm, fun η hη hZ => hbound η ⟨hη, hZ⟩⟩

theorem exists_sigma {h j : ℝ} {P : ℝ → ℝ}
    (p : Parameters h j) (pP : PressureData P) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ η ∈ Icc (-1 : ℝ) 1,
      |Z h j P η| ≤ j / 10 → 99 / 100 < chi h j σ η := by
  obtain ⟨m, hm, hbound⟩ := low_Z_has_H_margin p pP
  let σ : ℝ := Real.sqrt m / 20
  have hσ : 0 < σ := div_pos (Real.sqrt_pos.mpr hm) (by norm_num)
  have hsq : σ ^ 2 = m / 400 := by
    dsimp [σ]
    rw [div_pow, Real.sq_sqrt hm.le]
    norm_num
  refine ⟨σ, hσ, ?_⟩
  intro η hη hZ
  have hH := hbound η hη hZ
  have hden : 0 < (H h j η) ^ 2 + σ ^ 2 := by nlinarith [sq_nonneg σ]
  unfold chi
  apply (lt_div_iff₀ hden).mpr
  nlinarith

theorem exists_cutoff_parameters {h j : ℝ} {P : ℝ → ℝ}
    (p : Parameters h j) (pP : PressureData P) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, |Z h j P η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) := by
  obtain ⟨σ, hσ, hcut⟩ := exists_sigma p pP
  exact ⟨j / 10, σ, div_pos p.j_pos (by norm_num), hσ, hcut, chi_contDiff h j hσ⟩

theorem ideal_prefix_cutoff_parameters {h j : ℝ} (p : Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |Z h j (PressureDatum.pressure g a) η| ≤ δ → 99 / 100 < chi h j σ η) ∧
      ContDiff ℝ ∞ (chi h j σ) :=
  exists_cutoff_parameters p (pressureData_of_ideal_prefix hp hB hg ha)

theorem ideal_prefix_root_positive {h j : ℝ} (p : Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ η₀ : ℝ, η₀ ∈ Ioo (-j / 4) (-j / 5) ∧ H h j η₀ = 0 ∧
      j / 5 < Z h j (PressureDatum.pressure g a) η₀ ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, H h j η = 0 → η = η₀ :=
  exists_root_with_positive_Z p (pressureData_of_ideal_prefix hp hB hg ha)

/-- Cancellation in the complete axis source preserves its strict margin. -/
theorem base_source_lower {h j η : ℝ} (p : Parameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    (29 / 10 : ℝ) < -W h j η - h * (1 - 2 * η * U j η) := by
  have he : -W h j η - h * (1 - 2 * η * U j η) = 3 - h + j * η := by
    unfold W U d D
    ring
  rw [he]
  have hm := mul_nonneg p.j_pos.le (show 0 ≤ η + 1 by linarith [hη.1])
  nlinarith [p.h_le, p.j_le]

end NavierStokes.NaturalAxisRange
