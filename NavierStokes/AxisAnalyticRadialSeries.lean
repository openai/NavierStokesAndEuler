import NavierStokes.AxisAnalyticCoefficients
import NavierStokes.CauchyRestriction

/-! # A convergent radial series in a Banach space of parameter-disk functions -/

noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisJointAnalytic

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Uniform geometric coefficient bounds yield a genuine Banach-valued
holomorphic radial sum throughout the indicated disk. -/
theorem geometricSeries_analytic {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n : ℕ, z ^ n • a n) (ball 0 R) := by
  have hg : Summable (fun n : ℕ => C * (R * ρ) ^ n) :=
    (summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C
  apply (Complex.differentiableOn_tsum_of_summable_norm hg _ isOpen_ball _).analyticOnNhd isOpen_ball
  · intro n
    exact ((differentiable_id.pow n).smul_const (a n)).differentiableOn
  · intro n z hz
    have hzR : ‖z‖ ≤ R := (mem_ball_zero_iff.mp hz).le
    rw [norm_smul, norm_pow]
    calc
      _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hzR n)
        (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
      _ = _ := by rw [mul_pow]; ring

theorem geometricSeries_summable {a : ℕ → E} {C ρ R : ℝ}
    (_hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hR : 0 < R) (hq : R * ρ < 1)
    (ha : ∀ n, ‖a n‖ ≤ C * ρ ^ n) {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n : ℕ => z ^ n • a n) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hR.le hρ)]
      exact hq)).mul_left C)
  intro n
  rw [norm_smul, norm_pow]
  calc
    _ ≤ R ^ n * (C * ρ ^ n) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz n)
      (ha n) (norm_nonneg _) (pow_nonneg hR.le n)
    _ = _ := by rw [mul_pow]; ring

end Geometric

/-- Each coefficient restricted to a closed disk inside the common strip. -/
def diskCoefficient (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (n : ℕ) : C(Disk c σ, ℂ) where
  toFun z := complexCoefficient I ε A n z
  continuous_toFun := (complexCoefficient_analytic I hε hs hs1 A n).continuousOn.comp_continuous
    continuous_subtype_val (fun z => hK z.2)

theorem diskCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s))) (n : ℕ) :
    ‖diskCoefficient I hε hs hs1 A c σ hK n‖ ≤
      (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  exact complexCoefficient_bound I hε hs hs1 A n (hK z.2)

/-- The same coefficient series, evaluated at a real radius and a complex
parameter. Its real slice is the original constructed profile. -/
def radialExtension (I : Window) (ε : ℝ) (A : AxisSpace I ε) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (Y : ℂ) ^ n * complexCoefficient I ε A n z

theorem radialExtension_ofReal (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) {Y : ℝ} (hY : |Y| < 20) (x : ℝ) :
    radialExtension I ε A Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) := by
  unfold radialExtension profile
  simp only [complexCoefficient_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact (Complex.ofRealCLM.map_tsum (profile_hasSum I hε A (p := (Y, x)) hY).summable).symm

end NavierStokes.AxisJointAnalytic
