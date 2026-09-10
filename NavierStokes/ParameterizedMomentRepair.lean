import NavierStokes.UniformQuadraticBranch
import NavierStokes.ClosedIntervalMomentRepair

noncomputable section

namespace NavierStokes.ParameterizedMomentRepair

open Set
open scoped ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A single smooth branch in all parameters, on an arbitrary closed parameter
set, under uniform quantitative moment-repair bounds. -/
theorem exists_smooth_uniform_branch (S : Set P)
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E) (d : P → E)
    (hB : ContDiffOn ℝ ∞ B S) (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S)
    (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hBi : ∀ p ∈ S, (B p).IsInvertible)
    (hBn : ∀ p ∈ S, ‖(B p).inverse‖ ≤ ν)
    (hAn : ∀ p ∈ S, ‖A p‖ ≤ q) (hdn : ∀ p ∈ S, ‖d p‖ ≤ δ)
    (hsmall : 8 * ν^2 * q * δ ≤ 1) :
    ∃ c : P → E, ContDiffOn ℝ ∞ c S ∧
      (∀ p ∈ S, ‖c p‖ ≤ 2 * ν * ‖d p‖ ∧ B p (c p) + A p (c p) (c p) = d p) ∧
      (∀ p ∈ S, ∀ e : E, ‖e‖ ≤ 2 * ν * δ →
        B p e + A p e e = d p → e = c p) := by
  obtain ⟨c, hc, hspec, huniq⟩ := UniformQuadraticBranch.exists_smooth_small_branch
    B A d hB hA hd ν q δ hν hq hδ hBi hBn hAn hdn hsmall
  refine ⟨c, hc, ?_, huniq⟩
  intro p hp
  refine ⟨?_, (hspec p hp).2⟩
  have hs : 4 * ν * q * (2 * ν * δ) ≤ 1 := by nlinarith [hsmall]
  have hb := UniformQuadraticBranch.norm_sub_le (B p) (B p) (A p) (A p)
    (0 : E) (d p) (0 : E) (c p) ν q (2*ν*δ) hν hq (by positivity)
    (hBi p hp) (hBn p hp) (hAn p hp) (by simp; positivity) (hspec p hp).1
    (by simp) (hspec p hp).2 hs
  have hzero : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := norm_zero (E := E →L[ℝ] E →L[ℝ] E)
  simpa only [sub_zero, sub_self, norm_zero, hzero, zero_mul, add_zero] using hb

open ClosedIntervalCk ClosedIntervalMomentRepair

/-- A parameter slice selected in a common uniform correction ball has the
same exact finite-jet estimate as the canonical C⁰ Picard branch. -/
theorem same_branch_finite_jet_bound (D : Data E) (c : ℝ → E)
    (hc : ContDiffOn ℝ ∞ c I) (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hν₀ : D.inverseNorm 0 ≤ ν) (hq₀ : D.quadraticNorm 0 ≤ q) (hd₀ : D.debtNorm 0 ≤ δ)
    (hbound : ‖ofContDiffOn c (hc.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))‖ ≤ 2 * ν * δ)
    (heq : ∀ x ∈ I, D.B x (c x) + D.A x (c x) (c x) = D.d x)
    (hsmall : 8 * ν^2 * q * δ ≤ 1) :
    ∀ k : ℕ, D.Small k →
      ‖ofContDiffOn c (hc.of_le (by simp : (k : ℕ∞ω) ≤ ∞))‖ ≤
        2 * D.inverseNorm k * D.debtNorm k := by
  have hνn : 0 ≤ D.inverseNorm 0 := norm_nonneg _
  have hqn : 0 ≤ D.quadraticNorm 0 := norm_nonneg (D.bilinearMap 0)
  have hdn : 0 ≤ D.debtNorm 0 := norm_nonneg _
  have hs₀ : D.Small 0 := by
    calc
      _ ≤ 8 * ν^2 * q * δ := by
        gcongr
      _ ≤ 1 := hsmall
  obtain ⟨f, hf, hf₀, hfeq, hfk, _, _⟩ := D.exists_smooth_same_branch hs₀
  have hfb : ∀ x : I, ‖f x‖ ≤ 2 * ν * δ := by
    intro x
    have hb := (norm_ofContDiffOn_le_iff f (hf.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
      (by positivity : 0 ≤ 2 * D.inverseNorm 0 * D.debtNorm 0)).mp hf₀ 0 le_rfl x
    simp only [iteratedDerivWithin_zero] at hb
    exact hb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hν₀ (by norm_num)) hd₀ hdn (by positivity))
  have hcb : ∀ x : I, ‖c x‖ ≤ 2 * ν * δ := by
    intro x
    simpa only [iteratedDerivWithin_zero] using
      (norm_ofContDiffOn_le_iff c (hc.of_le (by simp : (0 : ℕ∞ω) ≤ ∞))
        (by positivity : 0 ≤ 2 * ν * δ)).mp hbound 0 le_rfl x
  have hs : 4 * ν * q * (2 * ν * δ) ≤ 1 := by nlinarith [hsmall]
  have hfc : EqOn f c I := by
    intro x hx
    have hb := UniformQuadraticBranch.norm_sub_le (D.B x) (D.B x) (D.A x) (D.A x)
      (D.d x) (D.d x) (c x) (f x) ν q (2*ν*δ) hν hq (by positivity)
      (D.invertible x hx) ((D.pointwise_inverse_bound ⟨x,hx⟩).trans hν₀)
      ((D.pointwise_bilinear_bound ⟨x,hx⟩).trans hq₀) (hcb ⟨x,hx⟩) (hfb ⟨x,hx⟩)
      (heq x hx) (hfeq x hx) hs
    have hz : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := norm_zero (E := E →L[ℝ] E →L[ℝ] E)
    have hn : ‖f x-c x‖ ≤ 0 := by
      simpa only [sub_self, norm_zero, hz, zero_mul, zero_add, mul_zero] using hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  intro k hk
  have he : ofContDiffOn c (hc.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) =
      ofContDiffOn f (hf.of_le (by simp : (k : ℕ∞ω) ≤ ∞)) := by
    apply value_injective k
    ext x
    exact (hfc x.property).symm
  rw [he]
  exact hfk k hk

end NavierStokes.ParameterizedMomentRepair
