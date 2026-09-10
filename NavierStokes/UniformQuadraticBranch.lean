import NavierStokes.SmoothQuadraticBranch
import NavierStokes.QuadraticLinearization

/-! Uniform dependence of the small quadratic correction on every parameter.
The estimate applies to any selected solution in the common correction ball. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.UniformQuadraticBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stability in the correction ball, with a fixed inverse bound. -/
theorem norm_sub_le (B B' : E →L[ℝ] E) (A A' : E →L[ℝ] E →L[ℝ] E)
    (d d' c c' : E) (ν q r : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hBi : B.IsInvertible) (hB : ‖B.inverse‖ ≤ ν) (hA : ‖A‖ ≤ q)
    (hc : ‖c‖ ≤ r) (hc' : ‖c'‖ ≤ r)
    (heq : B c + A c c = d) (heq' : B' c' + A' c' c' = d')
    (hsmall : 4 * ν * q * r ≤ 1) :
    ‖c' - c‖ ≤ 2 * ν * (‖d' - d‖ + ‖B' - B‖ * r + ‖A' - A‖ * r ^ 2) := by
  have he : B (c' - c) = d' - d - (B' - B) c' - (A' - A) c' c' -
      (A c' c' - A c c) := by
    rw [← heq, ← heq']
    simp only [map_sub, sub_apply]
    abel
  have hlin : ‖(B' - B) c'‖ ≤ ‖B' - B‖ * r :=
    ((B' - B).le_opNorm c').trans (mul_le_mul_of_nonneg_left hc' (norm_nonneg _))
  have hcoeff : ‖(A' - A) c' c'‖ ≤ ‖A' - A‖ * r ^ 2 := by
    apply ((A' - A).le_opNorm₂ c' c').trans
    calc
      _ ≤ ‖A' - A‖ * r * r :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc' (norm_nonneg (A' - A))) hc'
          (norm_nonneg c') (mul_nonneg (norm_nonneg (A' - A)) hr)
      _ = _ := by ring
  have hquad : ‖A c' c' - A c c‖ ≤ q * (r + r) * ‖c' - c‖ :=
    (SmoothMomentRepair.quadratic_sub_le A c' c).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hA (add_le_add hc' hc) (by positivity) hq) (norm_nonneg _))
  have hres : ‖B (c' - c)‖ ≤
      ‖d' - d‖ + ‖B' - B‖ * r + ‖A' - A‖ * r ^ 2 + q * (r + r) * ‖c' - c‖ := by
    rw [he]
    exact (_root_.norm_sub_le _ _).trans (add_le_add
      ((_root_.norm_sub_le _ _).trans (add_le_add
        ((_root_.norm_sub_le _ _).trans (add_le_add le_rfl hlin)) hcoeff)) hquad)
  have hbound : ‖c' - c‖ ≤ ν *
      (‖d' - d‖ + ‖B' - B‖ * r + ‖A' - A‖ * r ^ 2 + q * (r + r) * ‖c' - c‖) := by
    calc
      ‖c' - c‖ = ‖B.inverse (B (c' - c))‖ := by rw [hBi.inverse_apply_self]
      _ ≤ ‖B.inverse‖ * ‖B (c' - c)‖ := B.inverse.le_opNorm _
      _ ≤ _ := mul_le_mul hB hres (norm_nonneg _) hν
  have hhalf : ν * (q * (r + r)) ≤ 1 / 2 := by nlinarith [hsmall]
  have habs := mul_le_mul_of_nonneg_right hhalf (norm_nonneg (c' - c))
  nlinarith [hbound]

variable {P : Type*} [TopologicalSpace P]

/-- Uniform contraction bounds imply joint continuity of any selected small
branch. The parameter set need not be open. -/
theorem continuousOn {S : Set P}
    (B : P → E →L[ℝ] E) (A : P → E →L[ℝ] E →L[ℝ] E) (d c : P → E)
    (hB : ContinuousOn B S) (hA : ContinuousOn A S) (hd : ContinuousOn d S)
    (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hBi : ∀ p ∈ S, (B p).IsInvertible)
    (hBn : ∀ p ∈ S, ‖(B p).inverse‖ ≤ ν) (hAn : ∀ p ∈ S, ‖A p‖ ≤ q)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ 2 * ν * δ)
    (heq : ∀ p ∈ S, B p (c p) + A p (c p) (c p) = d p)
    (hsmall : 8 * ν ^ 2 * q * δ ≤ 1) : ContinuousOn c S := by
  intro p hp
  let r : ℝ := 2 * ν * δ
  have hr : 0 ≤ r := by positivity
  have hs : 4 * ν * q * r ≤ 1 := by dsimp [r]; nlinarith [hsmall]
  have hbound : ∀ᶠ x in 𝓝[S] p, ‖c x - c p‖ ≤
      2 * ν * (‖d x - d p‖ + ‖B x - B p‖ * r + ‖A x - A p‖ * r ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact norm_sub_le (B p) (B x) (A p) (A x) (d p) (d x) (c p) (c x)
      ν q r hν hq hr (hBi p hp) (hBn p hp) (hAn p hp) (hc p hp) (hc x hx)
      (heq p hp) (heq x hx) hs
  have hlim : Tendsto (fun x => 2 * ν *
      (‖d x - d p‖ + ‖B x - B p‖ * r + ‖A x - A p‖ * r ^ 2)) (𝓝[S] p) (𝓝 0) := by
    have hdt : ContinuousWithinAt (fun x => ‖d x - d p‖) S p :=
      ((hd p hp).sub (continuousWithinAt_const (b := d p))).norm
    have hBt : ContinuousWithinAt (fun x => ‖B x - B p‖) S p :=
      ((hB p hp).sub (continuousWithinAt_const (b := B p))).norm
    have hAt : ContinuousWithinAt (fun x => ‖A x - A p‖) S p := by
      exact ContinuousWithinAt.norm (E := E →L[ℝ] E →L[ℝ] E)
        ((hA p hp).sub (continuousWithinAt_const (b := A p)))
    have hz : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 :=
      norm_zero (E := E →L[ℝ] E →L[ℝ] E)
    have ht : ContinuousWithinAt (fun x => 2 * ν *
        (‖d x - d p‖ + ‖B x - B p‖ * r + ‖A x - A p‖ * r ^ 2)) S p :=
      (continuousWithinAt_const (b := 2 * ν)).mul
        ((hdt.add (hBt.mul (continuousWithinAt_const (b := r)))).add
          (hAt.mul (continuousWithinAt_const (b := r ^ 2))))
    simpa only [sub_self, norm_zero, hz, zero_mul, add_zero, mul_zero] using ht.tendsto
  have hzero := squeeze_zero_norm' hbound hlim
  have hadd := hzero.add (tendsto_const_nhds (x := c p))
  change Tendsto c (𝓝[S] p) (𝓝 (c p))
  simpa using hadd

section Smooth

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace E]

/-- The same selected small correction is jointly smooth in any collection
of real parameters, including on closed parameter domains. -/
theorem contDiffOn {S : Set V}
    (B : V → E →L[ℝ] E) (A : V → E →L[ℝ] E →L[ℝ] E) (d c : V → E)
    (hB : ContDiffOn ℝ ∞ B S) (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S)
    (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hBi : ∀ p ∈ S, (B p).IsInvertible)
    (hBn : ∀ p ∈ S, ‖(B p).inverse‖ ≤ ν) (hAn : ∀ p ∈ S, ‖A p‖ ≤ q)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ 2 * ν * δ)
    (heq : ∀ p ∈ S, B p (c p) + A p (c p) (c p) = d p)
    (hsmall : 8 * ν ^ 2 * q * δ ≤ 1) : ContDiffOn ℝ ∞ c S := by
  apply SmoothQuadraticBranch.continuous_quadratic_branch_contDiffOn B A d c hB hA hd
    (continuousOn B A d c hB.continuousOn hA.continuousOn hd.continuousOn
      ν q δ hν hq hδ hBi hBn hAn hc heq hsmall) heq
  intro p hp
  obtain ⟨e, he⟩ := hBi p hp
  have heinv : ‖e.symm.toContinuousLinearMap‖ ≤ ν := by
    simpa only [← he, ContinuousLinearMap.inverse_equiv] using hBn p hp
  simpa only [he] using QuadraticLinearization.isInvertible e (A p) (c p)
    ν q δ hν hq heinv (hAn p hp) (hc p hp) hsmall

/-- Uniform smallness selects one jointly smooth family of corrections,
unique throughout the common correction ball. This applies in particular
to the interval together with any additional compact parameter set. -/
theorem exists_smooth_small_branch {S : Set V}
    (B : V → E →L[ℝ] E) (A : V → E →L[ℝ] E →L[ℝ] E) (d : V → E)
    (hB : ContDiffOn ℝ ∞ B S) (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S)
    (ν q δ : ℝ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hBi : ∀ p ∈ S, (B p).IsInvertible)
    (hBn : ∀ p ∈ S, ‖(B p).inverse‖ ≤ ν) (hAn : ∀ p ∈ S, ‖A p‖ ≤ q)
    (hdn : ∀ p ∈ S, ‖d p‖ ≤ δ) (hsmall : 8 * ν ^ 2 * q * δ ≤ 1) :
    ∃ c : V → E, ContDiffOn ℝ ∞ c S ∧
      (∀ p ∈ S, ‖c p‖ ≤ 2 * ν * δ ∧ B p (c p) + A p (c p) (c p) = d p) ∧
      ∀ p ∈ S, ∀ x : E, ‖x‖ ≤ 2 * ν * δ → B p x + A p x x = d p → x = c p := by
  classical
  have hpoints : ∀ p ∈ S, ∃! x : E,
      ‖x‖ ≤ 2 * ν * δ ∧ B p x + A p x x = d p := by
    intro p hp
    obtain ⟨e, he⟩ := hBi p hp
    have heinv : ‖e.symm.toContinuousLinearMap‖ ≤ ν := by
      simpa only [← he, ContinuousLinearMap.inverse_equiv] using hBn p hp
    have hs : 4 * ‖e.symm.toContinuousLinearMap‖ * ‖A p‖ * (2 * ν * δ) ≤ 1 := by
      calc
        _ ≤ 4 * ν * q * (2 * ν * δ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left heinv (by norm_num))
            (hAn p hp) (norm_nonneg (A p)) (by positivity)
        _ = 8 * ν ^ 2 * q * δ := by ring
        _ ≤ 1 := hsmall
    have hdebt : 2 * ‖e.symm.toContinuousLinearMap‖ * ‖d p‖ ≤ 2 * ν * δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left heinv (by norm_num)) (hdn p hp)
        (norm_nonneg _) (by positivity)
    rw [← he]
    exact SmoothMomentRepair.exists_unique_quadratic_correction e (A p) (d p)
      (2 * ν * δ) (by positivity) hs hdebt
  choose cp hcp using fun p hp => (hpoints p hp).exists
  let c : V → E := fun p => if hp : p ∈ S then cp p hp else 0
  have hc : ∀ p ∈ S, ‖c p‖ ≤ 2 * ν * δ ∧ B p (c p) + A p (c p) (c p) = d p := by
    intro p hp
    simpa only [c, dite_eq_left hp] using hcp p hp
  refine ⟨c, contDiffOn B A d c hB hA hd ν q δ hν hq hδ hBi hBn hAn
    (fun p hp => (hc p hp).1) (fun p hp => (hc p hp).2) hsmall, hc, ?_⟩
  intro p hp x hx heq
  exact (hpoints p hp).unique ⟨hx, heq⟩ (hc p hp)

end Smooth

end NavierStokes.UniformQuadraticBranch
