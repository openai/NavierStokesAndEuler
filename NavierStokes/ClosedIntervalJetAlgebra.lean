import NavierStokes.WeightedQuotients
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace NavierStokes.ClosedIntervalJetAlgebra

open Set
open scoped ContDiff BigOperators

abbrev J : Set ℝ := Icc (-1 : ℝ) 1

theorem uniqueDiff : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by norm_num)

def Bound (k : ℕ) (f : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ n ≤ k, ∀ η ∈ J, ‖iteratedFDerivWithin ℝ n f J η‖ ≤ B

theorem Bound.mono {k : ℕ} {f : ℝ → ℝ} {B C : ℝ}
    (hf : Bound k f B) (hBC : B ≤ C) : Bound k f C :=
  fun n hn η hη => (hf n hn η hη).trans hBC

theorem Bound.nonneg {k : ℕ} {f : ℝ → ℝ} {B : ℝ} (hf : Bound k f B) : 0 ≤ B :=
  (norm_nonneg _).trans (hf 0 (Nat.zero_le _) 0 (by constructor <;> norm_num))

theorem Bound.value {k : ℕ} {f : ℝ → ℝ} {B η : ℝ}
    (hf : Bound k f B) (hη : η ∈ J) : |f η| ≤ B := by
  simpa only [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs] using hf 0 (Nat.zero_le _) η hη

theorem Bound.const (k : ℕ) (c : ℝ) : Bound k (fun _ => c) |c| := by
  intro n hn η hη
  by_cases hn0 : n = 0
  · subst n; simp
  · rw [iteratedFDerivWithin_const_of_ne hn0]
    simpa only [Pi.zero_apply, norm_zero] using abs_nonneg c

theorem Bound.add {k : ℕ} {f g : ℝ → ℝ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f J) (hg : ContDiffOn ℝ ∞ g J)
    (ha : Bound k f A) (hb : Bound k g B) : Bound k (fun η => f η + g η) (A + B) := by
  intro n hn η hη
  rw [fun_iteratedFDerivWithin_add_apply ((hf η hη).of_le (WeightedQuotients.nat_le_infty n))
    ((hg η hη).of_le (WeightedQuotients.nat_le_infty n)) uniqueDiff hη]
  exact (norm_add_le _ _).trans (add_le_add (ha n hn η hη) (hb n hn η hη))

theorem Bound.sub {k : ℕ} {f g : ℝ → ℝ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f J) (hg : ContDiffOn ℝ ∞ g J)
    (ha : Bound k f A) (hb : Bound k g B) : Bound k (fun η => f η - g η) (A + B) := by
  intro n hn η hη
  rw [fun_iteratedFDerivWithin_sub_apply ((hf η hη).of_le (WeightedQuotients.nat_le_infty n))
    ((hg η hη).of_le (WeightedQuotients.nat_le_infty n)) uniqueDiff hη]
  exact (norm_sub_le _ _).trans (add_le_add (ha n hn η hη) (hb n hn η hη))

theorem Bound.congr {k : ℕ} {f g : ℝ → ℝ} {B : ℝ}
    (hf : Bound k f B) (he : EqOn g f J) : Bound k g B := by
  intro n hn η hη
  rw [iteratedFDerivWithin_congr he hη]
  exact hf n hn η hη

theorem Bound.mul {k : ℕ} {f g : ℝ → ℝ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f J) (hg : ContDiffOn ℝ ∞ g J)
    (ha : Bound k f A) (hb : Bound k g B) :
    Bound k (fun η => f η * g η) ((2 : ℝ)^k * A * B) := by
  intro n hn η hη
  refine (norm_iteratedFDerivWithin_mul_le hf hg uniqueDiff hη
    (WeightedQuotients.nat_le_infty n)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i (hin.trans hn) η hη)
        (Nat.cast_nonneg _)) (hb (n-i) ((Nat.sub_le _ _).trans hn) η hη)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ha.nonneg)
    _ = (2 : ℝ)^n * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose n
    _ ≤ (2 : ℝ)^k * A * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) hn) ha.nonneg) hb.nonneg

/-- The inverse bound depends only on the positive lower bound and the input jet bound. -/
theorem inverse_bound (k : ℕ) (μ B : ℝ) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f J →
      (∀ η ∈ J, μ ≤ f η) → Bound k f B → Bound k (fun η => (f η)⁻¹) C := by
  let R := max 1 (max B μ⁻¹)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let C := (k.factorial : ℝ) * WeightedQuotients.coeffBound (-1) k * R^(2*k+1)
  have hcoef := WeightedQuotients.coeffBound_nonneg (-1) k
  refine ⟨C, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hcoef) (pow_nonneg hR0 _), ?_⟩
  intro f hf hp hb n hn η hη
  have hfpos : ∀ η ∈ J, 0 < f η := fun η hη => hμ.trans_le (hp η hη)
  have hg : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ (-1 : ℝ)) (Ioi 0) := by
    intro t ht
    exact (Real.contDiffAt_rpow_const_of_ne (show 0 < t from ht).ne').contDiffWithinAt
  have hinv : (f η)⁻¹ ≤ R := (inv_anti₀ hμ (hp η hη)).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hc := norm_iteratedFDerivWithin_comp_le hg hf (WeightedQuotients.nat_le_infty n)
    isOpen_Ioi.uniqueDiffOn uniqueDiff hfpos hη (C := WeightedQuotients.coeffBound (-1) k * R^(k+1))
    (D := R) (by
      intro i hi
      rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (hfpos η hη)]
      apply WeightedQuotients.rpow_jet_bound (-1) hR (hfpos η hη) _ hinv (hi.trans hn)
      simpa only [Real.rpow_neg_one] using hinv) (by
      intro i hi hik
      exact (hb i (hik.trans hn) η hη).trans
        (((le_max_left _ _).trans (le_max_right _ _)).trans
          (by simpa only [pow_one] using pow_le_pow_right₀ hR hi)))
  simp only [Function.comp_def, Real.rpow_neg_one] at hc
  refine hc.trans ?_
  dsimp [C]
  calc
    (n.factorial : ℝ) * (WeightedQuotients.coeffBound (-1) k * R^(k+1)) * R^n
      = n.factorial * WeightedQuotients.coeffBound (-1) k * R^(k+1+n) := by rw [pow_add]; ring
    _ ≤ k.factorial * WeightedQuotients.coeffBound (-1) k * R^(2*k+1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) hcoef)
        (pow_le_pow_right₀ hR (by omega)) (pow_nonneg hR0 _)
        (mul_nonneg (Nat.cast_nonneg _) hcoef)

/-- Uniform algebraic control of a pair and a linear bound for its difference. -/
structure PairBound (k : ℕ) (f g : ℝ → ℝ) (B C ε : ℝ) : Prop where
  smooth_left : ContDiffOn ℝ ∞ f J
  smooth_right : ContDiffOn ℝ ∞ g J
  left : Bound k f B
  right : Bound k g B
  difference : Bound k (fun η => g η - f η) (C * ε)



namespace PairBound

variable {k : ℕ} {f g u v : ℝ → ℝ} {A B C D ε : ℝ}

theorem mono (h : PairBound k f g A C ε) {A' C' : ℝ}
    (ha : A ≤ A') (hc : C ≤ C') (hε : 0 ≤ ε) : PairBound k f g A' C' ε :=
  ⟨h.smooth_left, h.smooth_right, h.left.mono ha, h.right.mono ha,
    h.difference.mono (mul_le_mul_of_nonneg_right hc hε)⟩

theorem same (hf : ContDiffOn ℝ ∞ f J) (hb : Bound k f A) (ε : ℝ) :
    PairBound k f f A 0 ε := by
  refine ⟨hf, hf, hb, hb, ?_⟩
  simpa only [sub_self, zero_mul, abs_zero] using Bound.const k 0

theorem const (k : ℕ) (c ε : ℝ) : PairBound k (fun _ => c) (fun _ => c) |c| 0 ε :=
  same contDiffOn_const (Bound.const k c) ε

theorem add (h : PairBound k f g A C ε) (i : PairBound k u v B D ε) :
    PairBound k (fun η => f η + u η) (fun η => g η + v η) (A+B) (C+D) ε := by
  refine ⟨h.smooth_left.add i.smooth_left, h.smooth_right.add i.smooth_right,
    h.left.add h.smooth_left i.smooth_left i.left,
    h.right.add h.smooth_right i.smooth_right i.right, ?_⟩
  have hd := h.difference.add (h.smooth_right.sub h.smooth_left)
    (i.smooth_right.sub i.smooth_left) i.difference
  rw [← add_mul] at hd
  exact hd.congr (fun η _ => by ring)

theorem sub (h : PairBound k f g A C ε) (i : PairBound k u v B D ε) :
    PairBound k (fun η => f η - u η) (fun η => g η - v η) (A+B) (C+D) ε := by
  refine ⟨h.smooth_left.sub i.smooth_left, h.smooth_right.sub i.smooth_right,
    h.left.sub h.smooth_left i.smooth_left i.left,
    h.right.sub h.smooth_right i.smooth_right i.right, ?_⟩
  have hd := h.difference.sub (h.smooth_right.sub h.smooth_left)
    (i.smooth_right.sub i.smooth_left) i.difference
  rw [← add_mul] at hd
  exact hd.congr (fun η _ => by ring)

theorem mul (h : PairBound k f g A C ε) (i : PairBound k u v B D ε) :
    PairBound k (fun η => f η * u η) (fun η => g η * v η)
      ((2 : ℝ)^k*A*B) ((2 : ℝ)^k*(C*B+A*D)) ε := by
  refine ⟨h.smooth_left.mul i.smooth_left, h.smooth_right.mul i.smooth_right,
    h.left.mul h.smooth_left i.smooth_left i.left,
    h.right.mul h.smooth_right i.smooth_right i.right, ?_⟩
  have h₁ := h.difference.mul (h.smooth_right.sub h.smooth_left) i.smooth_right i.right
  have h₂ := h.left.mul h.smooth_left (i.smooth_right.sub i.smooth_left) i.difference
  have hd := h₁.add ((h.smooth_right.sub h.smooth_left).mul i.smooth_right)
    (h.smooth_left.mul (i.smooth_right.sub i.smooth_left)) h₂
  convert hd.congr (fun η _ => show g η * v η - f η * u η =
    (g η-f η)*v η+f η*(v η-u η) by ring) using 1; ring

theorem inverse (h : PairBound k f g A C ε) {μ T : ℝ} (hμ : 0 < μ)
    (hf : ∀ η ∈ J, μ ≤ f η) (hg : ∀ η ∈ J, μ ≤ g η)
    (hb : ∀ z : ℝ → ℝ, ContDiffOn ℝ ∞ z J →
      (∀ η ∈ J, μ ≤ z η) → Bound k z A → Bound k (fun η => (z η)⁻¹) T) :
    PairBound k (fun η => (f η)⁻¹) (fun η => (g η)⁻¹) T
      ((2 : ℝ)^k*((2 : ℝ)^k*C*T)*T) ε := by
  have hfn : ∀ η ∈ J, f η ≠ 0 := fun η hη => (hμ.trans_le (hf η hη)).ne'
  have hgn : ∀ η ∈ J, g η ≠ 0 := fun η hη => (hμ.trans_le (hg η hη)).ne'
  have hfs := h.smooth_left.inv hfn
  have hgs := h.smooth_right.inv hgn
  have hfb := hb f h.smooth_left hf h.left
  have hgb := hb g h.smooth_right hg h.right
  refine ⟨hfs, hgs, hfb, hgb, ?_⟩
  have hd := ((h.difference.mul (h.smooth_right.sub h.smooth_left) hgs hgb).mul
    ((h.smooth_right.sub h.smooth_left).mul hgs) hfs hfb)
  have hd' : Bound k (fun η => -((g η-f η)*(g η)⁻¹*(f η)⁻¹))
      ((2 : ℝ)^k*((2 : ℝ)^k*C*T)*T*ε) := by
    have hz := (Bound.const k 0).sub contDiffOn_const
      (((h.smooth_right.sub h.smooth_left).mul hgs).mul hfs) hd
    convert hz using 1 <;> first | (ext η; simp) | ring
  exact hd'.congr (fun η hη => by field_simp [hfn η hη, hgn η hη]; ring)

end PairBound

theorem Bound.derivWithin {k : ℕ} {f : ℝ → ℝ} {B : ℝ}
    (hf : Bound (k+1) f B) : Bound k (derivWithin f J) B := by
  intro n hn η hη
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    ← iteratedDerivWithin_succ', ← norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
  exact hf (n+1) (by omega) η hη

theorem PairBound.derivWithin {k : ℕ} {f g : ℝ → ℝ} {B C ε : ℝ}
    (h : PairBound (k+1) f g B C ε) :
    PairBound k (derivWithin f J) (derivWithin g J) B C ε := by
  refine ⟨h.smooth_left.derivWithin uniqueDiff (by simp),
    h.smooth_right.derivWithin uniqueDiff (by simp), h.left.derivWithin,
    h.right.derivWithin, ?_⟩
  apply h.difference.derivWithin.congr
  intro η hη
  symm
  exact derivWithin_sub ((h.smooth_right.differentiableOn (by simp)) η hη)
    ((h.smooth_left.differentiableOn (by simp)) η hη)



theorem Bound.id (k : ℕ) : Bound k (fun η => η) 1 := by
  intro n hn η hη
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_fun_id hη uniqueDiff]
  split_ifs <;> simp only [Real.norm_eq_abs, abs_one, abs_zero]
  · exact abs_le.mpr hη
  · exact le_rfl
  · norm_num

theorem Bound.of_le {k l : ℕ} {f : ℝ → ℝ} {B : ℝ}
    (hf : Bound l f B) (hkl : k ≤ l) : Bound k f B :=
  fun n hn η hη => hf n (hn.trans hkl) η hη

theorem PairBound.of_le {k l : ℕ} {f g : ℝ → ℝ} {B C ε : ℝ}
    (hf : PairBound l f g B C ε) (hkl : k ≤ l) : PairBound k f g B C ε :=
  ⟨hf.smooth_left, hf.smooth_right, hf.left.of_le hkl, hf.right.of_le hkl,
    hf.difference.of_le hkl⟩

/-- A finite expression made from the exact scalar additions and products. -/
inductive PolynomialExpression (ι : Type)
  | input : ι → PolynomialExpression ι
  | constant : ℝ → PolynomialExpression ι
  | add : PolynomialExpression ι → PolynomialExpression ι → PolynomialExpression ι
  | sub : PolynomialExpression ι → PolynomialExpression ι → PolynomialExpression ι
  | mul : PolynomialExpression ι → PolynomialExpression ι → PolynomialExpression ι

namespace PolynomialExpression

variable {ι : Type}

def eval (x : ι → ℝ → ℝ) : PolynomialExpression ι → ℝ → ℝ
  | input i => x i
  | constant c => fun _ => c
  | add p q => fun η => eval x p η + eval x q η
  | sub p q => fun η => eval x p η - eval x q η
  | mul p q => fun η => eval x p η * eval x q η

def bounds (k : ℕ) (B C : ι → ℝ) : PolynomialExpression ι → ℝ × ℝ
  | input i => (B i, C i)
  | constant c => (|c|, 0)
  | add p q | sub p q => ((bounds k B C p).1+(bounds k B C q).1,
      (bounds k B C p).2+(bounds k B C q).2)
  | mul p q => ((2 : ℝ)^k*(bounds k B C p).1*(bounds k B C q).1,
      (2 : ℝ)^k*((bounds k B C p).2*(bounds k B C q).1+
        (bounds k B C p).1*(bounds k B C q).2))

theorem bounds_nonneg (k : ℕ) {B C : ι → ℝ} (hB : ∀ i, 0 ≤ B i)
    (hC : ∀ i, 0 ≤ C i) (p : PolynomialExpression ι) :
    0 ≤ (bounds k B C p).1 ∧ 0 ≤ (bounds k B C p).2 := by
  induction p with
  | input i => exact ⟨hB i, hC i⟩
  | constant c => exact ⟨abs_nonneg c, le_rfl⟩
  | add p q hp hq | sub p q hp hq => exact ⟨add_nonneg hp.1 hq.1, add_nonneg hp.2 hq.2⟩
  | mul p q hp hq => exact ⟨mul_nonneg (mul_nonneg (by positivity) hp.1) hq.1,
      mul_nonneg (by positivity) (add_nonneg (mul_nonneg hp.2 hq.1) (mul_nonneg hp.1 hq.2))⟩

theorem eval_pairBound {k : ℕ} {f g : ι → ℝ → ℝ} {B C : ι → ℝ} {ε : ℝ}
    (h : ∀ i, PairBound k (f i) (g i) (B i) (C i) ε) (p : PolynomialExpression ι) :
    PairBound k (p.eval f) (p.eval g) (bounds k B C p).1 (bounds k B C p).2 ε := by
  induction p with
  | input i => exact h i
  | constant c => exact PairBound.const k c ε
  | add p q hp hq => exact hp.add hq
  | sub p q hp hq => exact hp.sub hq
  | mul p q hp hq => exact hp.mul hq

end PolynomialExpression

end NavierStokes.ClosedIntervalJetAlgebra
