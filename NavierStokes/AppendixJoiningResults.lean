import NavierStokes.ReferenceBounds

/-!
# Additional literal bounds in the axis and joining appendices
-/

noncomputable section

namespace NavierStokes.AppendixJoiningResults

open Set
open scoped ContDiff
open NaturalAxisCoefficients NaturalProfile ProfileHistories ReferenceBounds

/-- The printed axis margin holds on the entire numerical range allowed
before the subsequent choices of sufficiently small parameters. -/
theorem axis_initial_margin {h j η : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ 1 / 100)
    (hj0 : 0 ≤ j) (hj : j ≤ 1 / 20) (hη : η ∈ Icc (-1 : ℝ) 1) :
    (14 / 5 : ℝ) < -NaturalAxisData.W h j η := by
  have hD : 0 ≤ NaturalAxisData.D h := by
    unfold NaturalAxisData.D
    linarith
  have hD1 : 2 * NaturalAxisData.D h ≤ 1 := by
    unfold NaturalAxisData.D
    linarith
  have hDj : 0 ≤ 2 * NaturalAxisData.D h * j := by positivity
  have hDj1 : 2 * NaturalAxisData.D h * j ≤ j := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD1 hj0
  have hlow : -(2 * NaturalAxisData.D h * j) ≤ 2 * NaturalAxisData.D h * j * η := by
    nlinarith [mul_nonneg hDj (show 0 ≤ η + 1 by linarith [hη.1])]
  have hhη : h * η ^ 2 ≤ h := by
    have hs : η ^ 2 ≤ 1 := by nlinarith [hη.1, hη.2]
    nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hs)]
  rw [NaturalAxisData.neg_W_formula]
  nlinarith

/-- The apparent quadratic parameter contributions cancel in the complete
constant angular source. This keeps its margin on the full printed range. -/
theorem axis_base_source_identity (h j η : ℝ) :
    -NaturalAxisData.W h j η - h * (1 - 2 * η * NaturalAxisData.U j η) =
      3 - h + j * η := by
  unfold NaturalAxisData.W NaturalAxisData.U NaturalAxisData.d NaturalAxisData.D
  ring

theorem axis_base_source_lower {h j η : ℝ}
    (hh : h ≤ 1 / 100) (hj0 : 0 ≤ j) (hj : j ≤ 1 / 20)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    (29 / 10 : ℝ) < -NaturalAxisData.W h j η -
      h * (1 - 2 * η * NaturalAxisData.U j η) := by
  rw [axis_base_source_identity]
  have hm := mul_nonneg hj0 (show 0 ≤ η + 1 by linarith [hη.1])
  nlinarith

/-- The real denominator remains positive on the existing enlarged window
even under the larger `h ≤ .01` range of the current manuscript. -/
theorem axis_L_lower_bound_window {h η : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / 100)
    (hη : η ∈ window.interval) : (4879 / 5000 : ℝ) ≤ NaturalAxisData.L h η := by
  have he : η ∈ Icc (-11 / 10 : ℝ) (11 / 10) := hη
  have hs : η ^ 2 ≤ 121 / 100 := by nlinarith [he.1, he.2]
  have hm := mul_nonneg hh0 (sub_nonneg.mpr hs)
  unfold NaturalAxisData.L
  nlinarith

/-- The reference lower bound holds throughout `[100,110]`, including both
endpoints, for the very same reference selected by `exists_reference_bounds`. -/
theorem reference_first_gt_three {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0)
    (hb : ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0)
    {X η : ℝ} (hX : X ∈ Icc (100 : ℝ) 110) (hη : η ∈ Icc (-1 : ℝ) 1) :
    3 < p1 (referenceProfiles E.profile hΛ hδ hδT hP0) h (X, η) := by
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX.1
  have hL := NaturalAxisData.L_pos hsmall hη
  have hL1 := NaturalEntrance.L_le_one (NaturalAxisRange.ofSmall hsmall) η
  have hp := reference_mem E.profile hΛ (p := (X, η)) hX0.le hη
  have hf : ∀ s ∈ Icc (0 : ℝ) X, 0 < P.f (s, η) := by
    intro s hs
    exact N.refF_pos δ (reference_mem E.profile hΛ (p := (s, η)) hs.1 hη) hs.1
  have hsource : ∀ s ∈ Icc (0 : ℝ) X, (12 / 5 : ℝ) ≤ sourceQ P h (s, η) := by
    intro s hs
    have he := hb.source_lower (s, η) ⟨⟨hs.1, hs.2.trans hX.2⟩, hη⟩
    have hn : 0 ≤ (47 / 50 : ℝ) * NaturalAxisData.L h η * Λ *
        NaturalAxisData.chi h j σ η := by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le)
        (NaturalAxisData.chi_bounds h j hσ η).1
    change (47 / 50 : ℝ) * NaturalAxisData.L h η * Λ *
      NaturalAxisData.chi h j σ η + 12 / 5 < sourceQ P h (s, η) at he
    linarith
  have hbound := p1_lower_from_source P hp hX0 h hL (by norm_num : (0 : ℝ) ≤ 12 / 5)
    hf (reference_antitone E hΛ hδ hδT hP0 hX0.le hη) hsource
  have hthree : (3 : ℝ) < (12 / 5) * X / (2 * NaturalAxisData.L h η) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hL)).mpr
    nlinarith [hX.1]
  exact hthree.trans_le hbound

end NavierStokes.AppendixJoiningResults
