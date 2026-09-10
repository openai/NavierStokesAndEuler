import NavierStokes.AxisHolomorphic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Holomorphic radial coefficients with a common geometric bound -/

noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic

namespace NavierStokes.AxisJointAnalytic

def coefficientJet (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n m : ℕ) (x : ℝ) : ℝ :=
  jet I (weight ε) A.1 n m x / (m.factorial : ℝ)

theorem coefficientJet_hasDerivAt (I : Window) {ε : ℝ} (_hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo I.left I.right) :
    HasDerivAt (coefficientJet I ε A n m)
      (((m : ℝ) + 1) * coefficientJet I ε A n (m + 1) x) x := by
  have hd := (hasDerivAt_jet_interior I (weight ε) A n m hx).div_const (m.factorial : ℝ)
  convert! hd using 1
  unfold coefficientJet
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem coefficientJet_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) :
    ‖coefficientJet I ε A n m x‖ ≤
      (‖A‖ / (1 - s) * (1 / 20 / s) ^ n) * ((ε * (1 - s))⁻¹) ^ m := by
  have hb := term_factorial_bound I hε (R := 1) (by rfl) hs hs1 A 0 m n
    (p := (1, x)) (by norm_num)
  simp only [term, polynomialJet, Nat.descFactorial_zero, Nat.cast_one, Nat.sub_zero,
    one_pow, one_mul, pow_zero, mul_one] at hb
  rw [coefficientJet, norm_div, Real.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)).mpr
  calc
    _ ≤ _ := hb
    _ = _ := by ring

/-- The actual vertical Taylor extension of radial coefficient `n`. -/
def complexCoefficient (I : Window) (ε : ℝ) (A : AxisSpace I ε) (n : ℕ) : ℂ → ℂ :=
  verticalExtension (coefficientJet I ε A n)

theorem complexCoefficient_ofReal (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (n : ℕ) (x : ℝ) :
    complexCoefficient I ε A n (x : ℂ) = (coefficient I (weight ε) A n x : ℂ) := by
  rw [complexCoefficient, verticalExtension_ofReal]
  simp [coefficientJet, coefficient]

theorem complexCoefficient_analytic (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ) :
    AnalyticOnNhd ℂ (complexCoefficient I ε A n) (parameterStrip I (ε * (1 - s))) := by
  apply verticalExtension_analytic I (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith))
  · intro m x hx
    exact coefficientJet_hasDerivAt I hε A n m hx
  · intro m x _
    exact coefficientJet_bound I hε hs hs1 A n m x

theorem complexCoefficient_bound (I : Window) {ε s : ℝ} (hε : 0 < ε)
    (hs : (1 : ℝ) / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (n : ℕ)
    {z : ℂ} (hz : z ∈ parameterStrip I (ε * (1 - s))) :
    ‖complexCoefficient I ε A n z‖ ≤ (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n := by
  have hb := verticalExtension_bound
    (C := ‖A‖ / (1 - s) * (1 / 20 / s) ^ n)
    (mul_nonneg (div_nonneg (norm_nonneg A) (by linarith)) (by positivity))
    (mul_pos hε (by linarith)) hz.2.le
    (fun m => coefficientJet_bound I hε hs hs1 A n m z.re)
  change ‖verticalExtension (coefficientJet I ε A n) z‖ ≤ _
  convert! hb using 1
  ring

end NavierStokes.AxisJointAnalytic
