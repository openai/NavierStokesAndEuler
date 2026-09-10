import NavierStokes.NaturalProfile
import NavierStokes.ProfileHistories
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Entrance estimates for the actual natural profiles

The source and cone coordinates below are expressions in the actual smooth
profiles. Uniform estimates and the regular radial integral are used to check
the entrance test before any outgoing controlled continuation.
-/

noncomputable section

namespace NavierStokes.NaturalEntrance

open Set Filter NaturalProfile NaturalAxisBridge NaturalAxisCoefficients
open scoped Topology ContDiff

private local instance (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance
private local instance (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

def Sq (h : ℝ) (f U V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -transportW h V p * (1 + p.1 * partialY f p / f p) -
    h * (1 - 2 * p.2 * U p) - transportH h U p * (partialEta f p / f p)

def p1 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -2 * p.1 * partialY f p / f p

def ns (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := -2 * partialY U p

def angularVelocity (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (2 * p.1) * f p

def p2 (f U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * ns U p / angularVelocity f p

def coneSize (f U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p1 f p + (p2 f U p) ^ 2 / p1 f p

theorem Sq_eq_radial {h j Λ : ℝ} {P0 a₀ : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : IsNaturalSolution h j Λ P0 a₀ f U V Pr)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hf : f p ≠ 0) :
    Sq h f U V p = -2 * NaturalAxisData.L h p.2 * radialDifferential 2 f p / f p := by
  have he := hs.angular_equation p hp
  unfold Sq
  apply (eq_div_iff hf).mpr
  field_simp
  linear_combination he

/-- The strictly positive axis contribution is quantitative on the entire
original parameter interval. -/
theorem base_source_lower {h j : ℝ} (hsmall : NaturalAxisRange.Parameters h j)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    (29 / 10 : ℝ) < -NaturalAxisData.W h j η -
      h * (1 - 2 * η * NaturalAxisData.U j η) := by
  exact NaturalAxisRange.base_source_lower hsmall hη

theorem chi_zero_imp_H_zero (h j : ℝ) {σ η : ℝ} (hσ : 0 < σ)
    (hchi : NaturalAxisData.chi h j σ η = 0) : NaturalAxisData.H h j η = 0 := by
  have hden : NaturalAxisData.H h j η ^ 2 + σ ^ 2 ≠ 0 := by positivity
  have hs : NaturalAxisData.H h j η ^ 2 = 0 :=
    (div_eq_zero_iff.mp hchi).resolve_right hden
  exact (pow_eq_zero_iff (by norm_num)).mp hs

theorem gradient_zero_of_chi_zero (h j : ℝ) {σ η : ℝ} (hσ : 0 < σ)
    (hchi : NaturalAxisData.chi h j σ η = 0) : realGradient h j σ η = 0 := by
  simp [realGradient, chi_zero_imp_H_zero h j hσ hchi]

/-- A large second coordinate yields a strict cone-size margin uniformly
over every positive first coordinate. -/
theorem cone_size_of_second_large {a b : ℝ} (ha : 0 < a) (hb : (6 / 5 : ℝ) ^ 2 < b ^ 2) :
    12 / 5 < a + b ^ 2 / a := by
  calc
    12 / 5 < (a ^ 2 + b ^ 2) / a := by
      apply (lt_div_iff₀ ha).mpr
      nlinarith [sq_nonneg (a - 6 / 5)]
    _ = _ := by field_simp

/-- Compactness supplies one absorption scale when the limiting remainder
is already positive on the zero set of the nonnegative growing coefficient. -/
theorem compact_absorption {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (χ R : K → ℝ) (hχ : Continuous χ) (hR : Continuous R)
    (hnonneg : ∀ p, 0 ≤ χ p) (b : ℝ) (hzero : ∀ p, χ p = 0 → b < R p) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ p, b < Λ * χ p + R p := by
  classical
  let U : ℝ → Set K := fun a => {p | b < a * χ p + R p}
  have hU : ∀ a, IsOpen (U a) := fun a =>
    isOpen_lt continuous_const ((continuous_const.mul hχ).add hR)
  have hcover : (univ : Set K) ⊆ ⋃ a : ℝ, U a := by
    intro p _
    by_cases hp : χ p = 0
    · apply mem_iUnion.mpr ⟨0, ?_⟩
      simpa [U] using hzero p hp
    · have hp' : 0 < χ p := lt_of_le_of_ne (hnonneg p) (Ne.symm hp)
      apply mem_iUnion.mpr ⟨(b - R p + 1) / χ p, ?_⟩
      change b < (b - R p + 1) / χ p * χ p + R p
      rw [div_mul_cancel₀ _ hp]
      linarith
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let M : ℝ := 1 + ∑ a ∈ s, |a|
  have hsum : 0 ≤ ∑ a ∈ s, |a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨M, by dsimp [M]; linarith, ?_⟩
  intro Λ hΛ p
  have hc : ∃ a ∈ s, b < a * χ p + R p := by
    simpa only [U, mem_iUnion, Set.mem_ofPred_eq, exists_prop] using hs (mem_univ p)
  obtain ⟨a, ha, hpa⟩ := hc
  have ham : a ≤ M := by
    have hterm : |a| ≤ ∑ a ∈ s, |a| :=
      Finset.single_le_sum (fun _ _ => abs_nonneg _) ha
    dsimp [M]
    linarith [le_abs_self a]
  exact hpa.trans_le (add_le_add_left
    (mul_le_mul_of_nonneg_right (ham.trans hΛ) (hnonneg p)) _)

/-- A continuous expression satisfies a uniform small-perturbation estimate
around its zero-perturbation graph over a compact parameter set. -/
theorem compact_small_perturbation {K E : Type*} [MetricSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [ProperSpace E] (F : K × E → ℝ) (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p e, ‖e‖ < δ → |F (p, e) - F (p, 0)| < ε := by
  have hcomp : IsCompact ((univ : Set K) ×ˢ Metric.closedBall (0 : E) 1) :=
    isCompact_univ.prod (isCompact_closedBall 0 1)
  have hu := hcomp.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro p e he
  have he1 : ‖e‖ < 1 := he.trans_le (min_le_left _ _)
  have heδ : ‖e‖ < δ := he.trans_le (min_le_right _ _)
  have hp : (p, e) ∈ (univ : Set K) ×ˢ Metric.closedBall (0 : E) 1 :=
    ⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using he1.le⟩
  have hp0 : (p, (0 : E)) ∈ (univ : Set K) ×ˢ Metric.closedBall (0 : E) 1 :=
    ⟨mem_univ _, Metric.mem_closedBall_self zero_le_one⟩
  have hd : dist (p, e) (p, (0 : E)) < δ := by
    simpa only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg e)] using heδ
  simpa only [Real.dist_eq] using hδF (p, e) hp (p, 0) hp0 hd

theorem radial_flux_hasDerivAt {f : ℝ → ℝ} {X : ℝ} (hf : ContDiffAt ℝ 2 f X) :
    HasDerivAt (fun x : ℝ => x ^ 2 * deriv f x)
      (X * (X * deriv (deriv f) X + 2 * deriv f X)) X := by
  have hf' : ContDiffAt ℝ 1 (deriv f) X := by
    exact
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  convert! ((hasDerivAt_id X).fun_pow 2).fun_mul
    (hf'.differentiableAt (by norm_num)).hasDerivAt using 1
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub, mul_one, id_eq]
  ring

/-- The regular branch starts with zero radial flux. A positive source
therefore forces a strictly negative radial derivative away from the axis. -/
theorem derivative_neg_of_regular_source {f : ℝ → ℝ} {R L : ℝ}
    (hR : 0 < R) (hL : 0 < L)
    (hf : ∀ x ∈ Icc (0 : ℝ) R, ContDiffAt ℝ 2 f x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) R, 0 < f x)
    (hsource : ∀ x ∈ Ioo (0 : ℝ) R,
      0 < -2 * L * (x * deriv (deriv f) x + 2 * deriv f x) / f x) :
    deriv f R < 0 := by
  have hflux : ContinuousOn (fun x : ℝ => x ^ 2 * deriv f x) (Icc (0 : ℝ) R) := by
    intro x hx
    exact (radial_flux_hasDerivAt (hf x hx)).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn (fun x : ℝ => x ^ 2 * deriv f x) (Icc (0 : ℝ) R) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hflux
    intro x hx
    rw [interior_Icc] at hx
    rw [(radial_flux_hasDerivAt (hf x ⟨hx.1.le, hx.2.le⟩)).deriv]
    have hsrc := hsource x hx
    have hfx := hpos x ⟨hx.1.le, hx.2.le⟩
    have hnum : 0 < -2 * L * (x * deriv (deriv f) x + 2 * deriv f x) :=
      (div_pos_iff_of_pos_right hfx).mp hsrc
    have hrad : x * deriv (deriv f) x + 2 * deriv f x < 0 := by
      nlinarith
    exact mul_neg_of_pos_of_neg hx.1 hrad
  have hneg := hanti (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, hR.le⟩)
    (show R ∈ Icc 0 R from ⟨hR.le, le_rfl⟩) hR
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hneg
  by_contra hd
  have hm := mul_nonneg (sq_nonneg R) (le_of_not_gt hd)
  linarith

def entranceSet : Set (ℝ × ℝ) := Icc (0 : ℝ) (41 / 10) ×ˢ Icc (-1 : ℝ) 1

instance : CompactSpace entranceSet :=
  isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)

theorem entrance_mem_strip {p : ℝ × ℝ} (hp : p ∈ entranceSet) :
    p ∈ AxisEvaluation.strip window 20 := by
  refine ⟨?_, original_interval_interior hp.2⟩
  constructor <;> linarith [hp.1.1, hp.1.2]

theorem entrance_abs_le_five {p : ℝ × ℝ} (hp : p ∈ entranceSet) : |p.1| ≤ 5 := by
  rw [abs_of_nonneg hp.1.1]
  linarith [hp.1.2]

abbrev CoefficientPair (ε : ℝ) :=
  AxisCoefficientSpace.AxisSpace window ε × AxisCoefficientSpace.AxisSpace window ε

/-- The finite jets needed by the angular source, including the genuine
bounded average operator. -/
def sourceJets {ε : ℝ} (hε : 0 < ε) (x : CoefficientPair ε) (p : ℝ × ℝ) : Fin 6 → ℝ :=
  ![AxisEvaluation.mixedSeries window ε x.1 0 0 p,
    AxisEvaluation.mixedSeries window ε x.1 1 0 p,
    AxisEvaluation.mixedSeries window ε x.1 0 1 p,
    AxisEvaluation.mixedSeries window ε x.2 0 0 p,
    AxisEvaluation.mixedSeries window ε (AxisOperators.average window hε x.2) 0 0 p,
    AxisEvaluation.mixedSeries window ε (AxisOperators.average window hε x.2) 0 1 p]

def sourceJetConstant (ε : ℝ) : ℝ := 1 + AxisEvaluation.jetBound ε 5 0 0 +
  AxisEvaluation.jetBound ε 5 1 0 + AxisEvaluation.jetBound ε 5 0 1

theorem sourceJetConstant_pos {ε : ℝ} (hε : 0 < ε) : 0 < sourceJetConstant ε := by
  have h0 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have h1 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have h2 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 1
  unfold sourceJetConstant
  linarith

theorem sourceJets_sub_bound {ε : ℝ} (hε : 0 < ε) (x y : CoefficientPair ε)
    {p : ℝ × ℝ} (hp : p ∈ entranceSet) :
    ‖sourceJets hε x p - sourceJets hε y p‖ ≤ sourceJetConstant ε * ‖x - y‖ := by
  let N := ‖x - y‖
  have hN : 0 ≤ N := norm_nonneg (x - y)
  have hj0 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 0
  have hj1 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hj2 := AxisEvaluation.jetBound_nonneg hε (by norm_num : (1 : ℝ) ≤ 5) 0 1
  have hc0 : AxisEvaluation.jetBound ε 5 0 0 ≤ sourceJetConstant ε := by
    unfold sourceJetConstant; linarith
  have hc1 : AxisEvaluation.jetBound ε 5 1 0 ≤ sourceJetConstant ε := by
    unfold sourceJetConstant; linarith
  have hc2 : AxisEvaluation.jetBound ε 5 0 1 ≤ sourceJetConstant ε := by
    unfold sourceJetConstant; linarith
  have hfst : ‖x.1 - y.1‖ ≤ N := norm_fst_le (x - y)
  have hsnd : ‖x.2 - y.2‖ ≤ N := norm_snd_le (x - y)
  have havg : ‖AxisOperators.average window hε x.2 - AxisOperators.average window hε y.2‖ ≤ N := by
    rw [← map_sub]
    exact ((AxisOperators.average window hε).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (AxisOperators.norm_average_le window hε) (norm_nonneg _)).trans
        (by simpa using hsnd))
  have hb (A B : AxisCoefficientSpace.AxisSpace window ε) (k m : ℕ)
      (hAB : ‖A - B‖ ≤ N) (hc : AxisEvaluation.jetBound ε 5 k m ≤ sourceJetConstant ε) :
      ‖AxisEvaluation.mixedSeries window ε A k m p -
        AxisEvaluation.mixedSeries window ε B k m p‖ ≤ sourceJetConstant ε * N := by
    exact (AxisEvaluation.mixedSeries_sub_bound window hε (by norm_num) (by norm_num)
      A B k m (entrance_abs_le_five hp)).trans
      ((mul_le_mul_of_nonneg_left hAB
        (AxisEvaluation.jetBound_nonneg hε (by norm_num) k m)).trans
          (mul_le_mul_of_nonneg_right hc hN))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (sourceJetConstant_pos hε).le hN)).mpr
  intro i
  fin_cases i
  · simpa [sourceJets] using hb x.1 y.1 0 0 hfst hc0
  · simpa [sourceJets] using hb x.1 y.1 1 0 hfst hc1
  · simpa [sourceJets] using hb x.1 y.1 0 1 hfst hc2
  · simpa [sourceJets] using hb x.2 y.2 0 0 hsnd hc0
  · simpa [sourceJets] using hb _ _ 0 0 havg hc0
  · simpa [sourceJets] using hb _ _ 0 1 havg hc2

theorem sourceJets_continuous {ε : ℝ} (hε : 0 < ε) (x : CoefficientPair ε) :
    Continuous (fun p : entranceSet => sourceJets hε x p) := by
  have hm (A : AxisCoefficientSpace.AxisSpace window ε) (k m : ℕ) :
      Continuous (fun p : entranceSet => AxisEvaluation.mixedSeries window ε A k m p) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (AxisEvaluation.mixedSeries_smooth window hε A k m
      (entrance_mem_strip p.property)).continuousAt.comp continuous_subtype_val.continuousAt
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [sourceJets] using hm x.1 0 0
  · simpa [sourceJets] using hm x.1 1 0
  · simpa [sourceJets] using hm x.1 0 1
  · simpa [sourceJets] using hm x.2 0 0
  · simpa [sourceJets] using hm (AxisOperators.average window hε x.2) 0 0
  · simpa [sourceJets] using hm (AxisOperators.average window hε x.2) 0 1

/-- Subtracting the growing term `L Λ χ` leaves this continuous expression.
The clipped denominator agrees with every profile used below and makes the
finite-dimensional uniform-continuity argument global. -/
def sourceRemainder (h j σ : ℝ) (p : ℝ × ℝ) (t : ℝ) (v : Fin 6 → ℝ) : ℝ :=
  let phi := max (1 / 8 : ℝ) (v 0)
  let W := NaturalAxisData.W h j p.2 -
    t * (2 * NaturalAxisData.D h * p.2 * v 4 + NaturalAxisData.d p.2 * v 5)
  let U := NaturalAxisData.U j p.2 + t * v 3
  let H := NaturalAxisData.H h j p.2 + t * NaturalAxisData.d p.2 * v 3
  show ℝ from -W * (1 + p.1 * v 1 / phi) - h * (1 - 2 * p.2 * U) - H * (v 2 / phi) -
      NaturalAxisData.d p.2 * v 3 * realGradient h j σ p.2

theorem realGradient_continuous (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (realGradient h j σ) := by
  have hden : ∀ η : ℝ, NaturalAxisData.H h j η ^ 2 + σ ^ 2 ≠ 0 := by
    intro η
    positivity
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  have hH := (NaturalAxisData.H_contDiff h j).continuous
  exact (hL.neg.mul hH).div ((hH.pow 2).add continuous_const) hden

theorem sourceRemainder_continuous (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun z : (ℝ × ℝ) × (ℝ × (Fin 6 → ℝ)) =>
      sourceRemainder h j σ z.1 z.2.1 z.2.2) := by
  have hc := realGradient_continuous h j hσ
  have hn : ∀ v : Fin 6 → ℝ, max (1 / 8 : ℝ) (v 0) ≠ 0 := by
    intro v
    have := le_max_left (1 / 8 : ℝ) (v 0)
    linarith
  dsimp only [sourceRemainder, NaturalAxisData.W, NaturalAxisData.H,
    NaturalAxisData.U, NaturalAxisData.d]
  fun_prop (disch := first | exact fun x => hn x.2.2 | exact hn _ | positivity)

def referencePair {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0) :
    CoefficientPair v.epsilon :=
  referenceCoefficients window v.epsilon_pos (v.elements .chi) v.axisData

def referenceRemainder {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0)
    (p : entranceSet) : ℝ :=
  sourceRemainder h j σ p 0 (sourceJets v.epsilon_pos (referencePair v) p)

theorem reference_phi_value {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0)
    (p : entranceSet) :
    sourceJets v.epsilon_pos (referencePair v) p 0 =
      AxisSeries.profile (NaturalAxisData.chi h j σ p.val.2) p.val.1 := by
  have hη : p.val.2 ∈ window.interval :=
    ⟨(original_interval_interior p.property.2).1.le, (original_interval_interior p.property.2).2.le⟩
  change AxisEvaluation.mixedSeries window v.epsilon (referencePair v).1 0 0 p.val = _
  rw [AxisEvaluation.mixedSeries_zero]
  change AxisEvaluation.profile window v.epsilon
    (referenceCoefficients window v.epsilon_pos (v.elements .chi) v.axisData).1
      (p.val.1, p.val.2) = _
  rw [AxisReference.referenceCoefficients_profile_eq_series window v.epsilon_pos
    (v.elements .chi) v.axisData v.compatible hη]
  rw [v.value .chi hη]
  rfl

theorem reference_phi_lower {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0)
    (hσ : 0 < σ) (p : entranceSet) :
    1 / 4 < sourceJets v.epsilon_pos (referencePair v) p 0 := by
  rw [reference_phi_value v p]
  exact AxisSeries.profile_gt_quarter _ _ (NaturalAxisData.chi_bounds h j hσ _).1
    (NaturalAxisData.chi_bounds h j hσ _).2.le p.property.1.1 p.property.1.2

theorem reference_phiY_zero {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0)
    (p : entranceSet) (hchi : NaturalAxisData.chi h j σ p.val.2 = 0) :
    sourceJets v.epsilon_pos (referencePair v) p 1 = 0 := by
  have hp := entrance_mem_strip p.property
  have hη : p.val.2 ∈ window.interval := ⟨hp.2.1.le, hp.2.2.le⟩
  change AxisEvaluation.mixedSeries window v.epsilon (referencePair v).1 1 0 p.val = 0
  rw [← partialY_profile window v.epsilon_pos (referencePair v).1 hp]
  unfold partialY
  unfold referencePair
  rw [AxisReference.referenceCoefficients_deriv_Y_eq window v.epsilon_pos
    (v.elements .chi) v.axisData v.compatible hη]
  rw [v.value .chi hη]
  change deriv (AxisSeries.profile (NaturalAxisData.chi h j σ p.val.2)) p.val.1 = 0
  rw [hchi, AxisSeries.deriv_profile]
  simp

theorem referenceRemainder_continuous {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hσ : 0 < σ) : Continuous (referenceRemainder v) := by
  let m : entranceSet → (ℝ × ℝ) × (ℝ × (Fin 6 → ℝ)) :=
    fun p => (p.val, (0, sourceJets v.epsilon_pos (referencePair v) p.val))
  have hm : Continuous m := continuous_subtype_val.prodMk
    (continuous_const.prodMk (sourceJets_continuous v.epsilon_pos (referencePair v)))
  have hc := (sourceRemainder_continuous h j hσ).comp hm
  exact hc

theorem referenceRemainder_at_chi_zero {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hσ : 0 < σ) (p : entranceSet)
    (hchi : NaturalAxisData.chi h j σ p.val.2 = 0) :
    referenceRemainder v p = -NaturalAxisData.W h j p.val.2 -
      h * (1 - 2 * p.val.2 * NaturalAxisData.U j p.val.2) := by
  have hH := chi_zero_imp_H_zero h j hσ hchi
  have hk := gradient_zero_of_chi_zero h j hσ hchi
  have hy := reference_phiY_zero v p hchi
  simp only [referenceRemainder, sourceRemainder, zero_mul, add_zero, sub_zero,
    hH, hk, hy, mul_zero, zero_div, mul_one]

theorem chi_continuous (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (NaturalAxisData.chi h j σ) := by
  have hH := (NaturalAxisData.H_contDiff h j).continuous
  apply (hH.fun_pow 2).div ((hH.fun_pow 2).fun_add continuous_const)
  intro η
  positivity

theorem reference_source_absorption {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ p : entranceSet,
      27 / 10 < Λ * ((1 / 20 : ℝ) * NaturalAxisData.L h p.val.2 *
        NaturalAxisData.chi h j σ p.val.2) + referenceRemainder v p := by
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  apply compact_absorption _ _
    ((continuous_const.mul (hL.comp (continuous_snd.comp continuous_subtype_val))).mul
      ((chi_continuous h j hσ).comp (continuous_snd.comp continuous_subtype_val)))
    (referenceRemainder_continuous v hσ)
  · intro p
    exact mul_nonneg
      (mul_nonneg (by norm_num) (NaturalAxisRange.L_pos hsmall p.property.2).le)
      (NaturalAxisData.chi_bounds h j hσ _).1
  · intro p hp
    have hfac : (1 / 20 : ℝ) * NaturalAxisData.L h p.val.2 ≠ 0 :=
      mul_ne_zero (by norm_num) (NaturalAxisRange.L_pos hsmall p.property.2).ne'
    have hchi := (mul_eq_zero.mp hp).resolve_left hfac
    rw [referenceRemainder_at_chi_zero v hσ p hchi]
    linarith [base_source_lower hsmall p.property.2]

def perturbationSource {h j σ : ℝ} {P0 : ℝ → ℝ} (v : CoefficientFamily h j σ P0)
    (q : entranceSet × (ℝ × (Fin 6 → ℝ))) : ℝ :=
  sourceRemainder h j σ q.1 q.2.1 (sourceJets v.epsilon_pos (referencePair v) q.1 + q.2.2)

theorem perturbationSource_continuous {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hσ : 0 < σ) : Continuous (perturbationSource v) := by
  let m : entranceSet × (ℝ × (Fin 6 → ℝ)) → (ℝ × ℝ) × (ℝ × (Fin 6 → ℝ)) :=
    fun q => (q.1.val, (q.2.1,
      sourceJets v.epsilon_pos (referencePair v) q.1.val + q.2.2))
  have hm : Continuous m := (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (((sourceJets_continuous v.epsilon_pos (referencePair v)).comp continuous_fst).add
        (continuous_snd.comp continuous_snd)))
  have hc := (sourceRemainder_continuous h j hσ).comp hm
  exact hc

/-- The finite-dimensional source correction converges uniformly, using the
proved evaluation operator bounds and the actual coefficient-space norm error. -/
theorem sourceRemainder_uniform_limit {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hσ : 0 < σ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ x : CoefficientPair v.epsilon,
      ‖x - referencePair v‖ ≤ K / (2 * Λ) → ∀ p : entranceSet,
        |sourceRemainder h j σ p (1 / Λ) (sourceJets v.epsilon_pos x p) -
          referenceRemainder v p| < 1 / 10 := by
  obtain ⟨δ, hδ, hδF⟩ := compact_small_perturbation (perturbationSource v)
    (perturbationSource_continuous v hσ) (by norm_num : (0 : ℝ) < 1 / 10)
  let J := sourceJetConstant v.epsilon
  have hJ : 0 < J := sourceJetConstant_pos v.epsilon_pos
  let M := 1 + (1 + J * K) / δ
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ x hx p
  have hΛpos : 0 < Λ := hM.trans_le hΛ
  have hratio : (1 + J * K) / δ < Λ := by dsimp [M] at hΛ; linarith
  have hmul := (div_lt_iff₀ hδ).mp hratio
  have htime : |1 / Λ| < δ := by
    rw [abs_of_pos (one_div_pos.mpr hΛpos), div_lt_iff₀ hΛpos]
    nlinarith [mul_nonneg hJ.le hK]
  have hjets : ‖sourceJets v.epsilon_pos x p -
      sourceJets v.epsilon_pos (referencePair v) p‖ < δ := by
    apply (sourceJets_sub_bound v.epsilon_pos x (referencePair v) p.property).trans_lt
    apply (mul_le_mul_of_nonneg_left hx hJ.le).trans_lt
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * Λ)]
    nlinarith [mul_nonneg hJ.le hK]
  have hpert : ‖((1 / Λ), sourceJets v.epsilon_pos x p -
      sourceJets v.epsilon_pos (referencePair v) p)‖ < δ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using And.intro htime hjets
  have h := hδF p ((1 / Λ), sourceJets v.epsilon_pos x p -
    sourceJets v.epsilon_pos (referencePair v) p) hpert
  simpa only [perturbationSource, Prod.fst_zero, Prod.snd_zero, add_zero,
    add_sub_cancel, referenceRemainder] using h

/-- The exact coefficient-space approximation gives the desired quantitative
source bound after one common large-scale choice. -/
theorem source_uniform_lower {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ x : CoefficientPair v.epsilon,
      ‖x - referencePair v‖ ≤ K / (2 * Λ) → ∀ p : entranceSet,
        (19 / 20 : ℝ) * NaturalAxisData.L h p.val.2 * Λ *
            NaturalAxisData.chi h j σ p.val.2 + 5 / 2 <
          NaturalAxisData.L h p.val.2 * Λ * NaturalAxisData.chi h j σ p.val.2 +
            sourceRemainder h j σ p (1 / Λ) (sourceJets v.epsilon_pos x p) := by
  obtain ⟨M₁, hM₁, hmain⟩ := reference_source_absorption v hsmall hσ
  obtain ⟨M₂, hM₂, herr⟩ := sourceRemainder_uniform_limit v hσ hK
  refine ⟨max M₁ M₂, hM₁.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ x hx p
  have hbase := hmain Λ ((le_max_left _ _).trans hΛ) p
  have he := (abs_lt.mp (herr Λ ((le_max_right _ _).trans hΛ) x hx p)).1
  nlinarith

theorem angularProfile_radial_log_derivative {a : ℝ → ℝ} {Λ : ℝ}
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : a p.2 ≠ 0)
    (_hval : Φ (rescalePoint Λ p) ≠ 0) :
    p.1 * partialY (angularProfile a Λ Φ) p / angularProfile a Λ Φ p =
      (rescalePoint Λ p).1 * partialY Φ (rescalePoint Λ p) / Φ (rescalePoint Λ p) := by
  rw [angularProfile_partialY hΦ a Λ hp]
  change p.1 * (a p.2 * Λ * partialY Φ (rescalePoint Λ p)) /
    (a p.2 * Φ (rescalePoint Λ p)) =
      (Λ * p.1) * partialY Φ (rescalePoint Λ p) / Φ (rescalePoint Λ p)
  rw [show p.1 * (a p.2 * Λ * partialY Φ (rescalePoint Λ p)) =
      a p.2 * ((Λ * p.1) * partialY Φ (rescalePoint Λ p)) by ring]
  exact mul_div_mul_left _ _ ha

theorem angularProfile_parameter_log_derivative {a : ℝ → ℝ} {Λ κ : ℝ}
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : a p.2 ≠ 0)
    (hval : Φ (rescalePoint Λ p) ≠ 0)
    (had : HasDerivAt a ((Λ * κ) * a p.2) p.2) :
    partialEta (angularProfile a Λ Φ) p / angularProfile a Λ Φ p =
      Λ * κ + partialEta Φ (rescalePoint Λ p) / Φ (rescalePoint Λ p) := by
  rw [angularProfile_partialEta hΦ Λ hp had]
  simp only [angularProfile, pullback]
  field_simp

private theorem source_remainder_algebra {Λ L χ Hs κ d u W h η U Y φ φY φEta : ℝ}
    (hΛ : Λ ≠ 0) (hφ : φ ≠ 0) (hgrad : Hs * κ = -L * χ) :
    -W * (1 + Y * φY / φ) - h * (1 - 2 * η * U) -
      (Hs + (1 / Λ) * d * u) * (Λ * κ + φEta / φ) =
      L * Λ * χ + (-W * (1 + Y * φY / φ) - h * (1 - 2 * η * U) -
        (Hs + (1 / Λ) * d * u) * (φEta / φ) - d * u * κ) := by
  calc
    _ = (-W * (1 + Y * φY / φ) - h * (1 - 2 * η * U) -
        (Hs + (1 / Λ) * d * u) * (φEta / φ) - d * u * κ) - Λ * (Hs * κ) := by
      field_simp ; ring
    _ = _ := by rw [hgrad]; ring

theorem Sq_reconstruction {h j σ Λ : ℝ} (P0 : ℝ → ℝ) {a : ℝ → ℝ}
    {Φ u B : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (hB : ContDiffOn ℝ ∞ B (AxisEvaluation.strip window 20))
    (hΛ : Λ ≠ 0) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : a p.2 ≠ 0)
    (hval : 1 / 8 ≤ Φ (rescalePoint Λ p))
    (had : HasDerivAt a ((Λ * realGradient h j σ p.2) * a p.2) p.2) :
    Sq h (angularProfile a Λ Φ)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p =
      NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
        sourceRemainder h j σ (rescalePoint Λ p) (1 / Λ)
          ![Φ (rescalePoint Λ p), partialY Φ (rescalePoint Λ p),
            partialEta Φ (rescalePoint Λ p), u (rescalePoint Λ p),
            B (rescalePoint Λ p), partialEta B (rescalePoint Λ p)] := by
  have hφ : Φ (rescalePoint Λ p) ≠ 0 := by linarith
  unfold Sq
  rw [angularProfile_radial_log_derivative hΦ hp ha hφ,
    angularProfile_parameter_log_derivative hΦ hp ha hφ had,
    transportW_reconstruct (σ := σ) P0 hB hp, transportH_reconstruct h j σ Λ P0 u p]
  dsimp only [sourceRemainder]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    max_eq_right hval, reconstructedH, reconstructedW, actualData,
    affineProfile, pullback]
  dsimp only [rescalePoint]
  dsimp only [rescalePoint] at hval hφ
  apply source_remainder_algebra hΛ hφ (gradient_identity h j σ p.2)

theorem sourceJets_eq {ε : ℝ} (hε : 0 < ε) (x : CoefficientPair ε)
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    sourceJets hε x p =
      ![AxisEvaluation.profile window ε x.1 p,
        partialY (AxisEvaluation.profile window ε x.1) p,
        partialEta (AxisEvaluation.profile window ε x.1) p,
        AxisEvaluation.profile window ε x.2 p,
        AxisEvaluation.profile window ε (AxisOperators.average window hε x.2) p,
        partialEta (AxisEvaluation.profile window ε (AxisOperators.average window hε x.2)) p] := by
  simp only [sourceJets, partialY_profile window hε _ hp,
    partialEta_profile window hε _ hp, AxisEvaluation.mixedSeries_zero]

noncomputable def angularField (h j σ Λ C : ℝ) {ε : ℝ} (x : CoefficientPair ε) :
    ℝ × ℝ → ℝ := angularProfile (realAmplitude h j σ Λ C) Λ
      (AxisEvaluation.profile window ε x.1)

noncomputable def axialField (j Λ : ℝ) {ε : ℝ} (x : CoefficientPair ε) :
    ℝ × ℝ → ℝ := affineProfile (NaturalAxisData.U j) (1 / Λ) Λ
      (AxisEvaluation.profile window ε x.2)

noncomputable def averageField (j Λ : ℝ) {ε : ℝ} (hε : 0 < ε) (x : CoefficientPair ε) :
    ℝ × ℝ → ℝ := affineProfile (NaturalAxisData.U j) (1 / Λ) Λ
      (AxisEvaluation.profile window ε (AxisOperators.average window hε x.2))

theorem Sq_coefficient_identity {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (x : CoefficientPair d.coefficients.epsilon)
    (hΛ : 0 < Λ) (hC : 0 < C) {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    (hval : 1 / 8 ≤ AxisEvaluation.profile window d.coefficients.epsilon x.1
      (rescalePoint Λ p)) :
    Sq h (angularField h j σ Λ C x) (axialField j Λ x)
        (averageField j Λ d.coefficients.epsilon_pos x) p =
      NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
        sourceRemainder h j σ (rescalePoint Λ p) (1 / Λ)
          (sourceJets d.coefficients.epsilon_pos x (rescalePoint Λ p)) := by
  rw [sourceJets_eq d.coefficients.epsilon_pos x hp]
  exact Sq_reconstruction P0
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos x.1)
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos _)
    hΛ.ne' hp (realAmplitude_pos h j σ Λ hC p.2).ne' hval
    (d.realAmplitude_hasDerivAt Λ C ⟨hp.2.1.le, hp.2.2.le⟩)

theorem physical_mem_domain {Λ X η : ℝ}
    (hY0 : 0 ≤ Λ * X) (hY1 : Λ * X ≤ 41 / 10)
    (hη : η ∈ Icc (-1 : ℝ) 1) : (X, η) ∈ domain Λ :=
  entrance_mem_strip ⟨⟨hY0, hY1⟩, hη⟩

/-- The source estimate forces the actual logarithmic radial slope to be
strictly positive on the regular branch, including every positive radius
up to the entrance. -/
theorem p1_pos_of_source {h j Λ R η : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ}
    (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) (hR : 0 < R) (hYR : Λ * R ≤ 41 / 10)
    (hη : η ∈ Icc (-1 : ℝ) 1) (hL : 0 < NaturalAxisData.L h η)
    (hpos : ∀ X ∈ Icc (0 : ℝ) R, 0 < f (X, η))
    (hsource : ∀ X ∈ Icc (0 : ℝ) R, 0 < Sq h f U V (X, η)) :
    0 < p1 f (R, η) := by
  have hmem (X : ℝ) (hX : X ∈ Icc (0 : ℝ) R) : (X, η) ∈ domain Λ :=
    physical_mem_domain (mul_nonneg hΛ.le hX.1)
      ((mul_le_mul_of_nonneg_left hX.2 hΛ.le).trans hYR) hη
  have hreg (X : ℝ) (hX : X ∈ Icc (0 : ℝ) R) :
      ContDiffAt ℝ 2 (fun y : ℝ => f (y, η)) X := by
    apply (((hs.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds (hmem X hX))).comp X
      (contDiffAt_id.prodMk contDiffAt_const))).of_le
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hneg : deriv (fun y : ℝ => f (y, η)) R < 0 := by
    apply derivative_neg_of_regular_source hR hL hreg hpos
    intro X hX
    have hXc : X ∈ Icc (0 : ℝ) R := ⟨hX.1.le, hX.2.le⟩
    have heq := Sq_eq_radial hs (hmem X hXc) (hpos X hXc).ne'
    have hsrc := hsource X hXc
    rw [heq] at hsrc
    simpa only [radialDifferential, partialY, iteratedDeriv_succ,
      iteratedDeriv_zero, Nat.cast_ofNat] using hsrc
  unfold p1 partialY
  exact div_pos (mul_pos_of_neg_of_neg (by nlinarith) hneg) (hpos R ⟨hR.le, le_rfl⟩)

/-- Applying the actual regular inverse to radially constant data gives
exactly its degree-one polynomial. -/
theorem regularInverse_one_constant {ε : ℝ} (hε : 0 < ε)
    (A : AxisCoefficientSpace.AxisSpace window ε) (hA : RadiallyConstant window ε A)
    (Y : ℝ) {η : ℝ} (hη : η ∈ window.interval) :
    AxisEvaluation.profile window ε (AxisOperators.regularInverse window hε 1 (by norm_num) A)
      (Y, η) = Y * inputValue window ε A η := by
  classical
  let J := AxisOperators.regularInverse window hε 1 (by norm_num) A
  have hzero : AxisCoefficientSpace.coefficient window (AxisWeightEstimates.weight ε) J 0 η = 0 :=
    AxisOperators.jet_regularInverse_zero window hε 1 (by norm_num) A 0 hη
  have hsucc (n : ℕ) :
      AxisCoefficientSpace.coefficient window (AxisWeightEstimates.weight ε) J (n + 1) η =
        AxisCoefficientSpace.coefficient window (AxisWeightEstimates.weight ε) A n η /
          AxisWeightEstimates.radialDivisor 1 n :=
    AxisOperators.jet_regularInverse_succ window hε 1 (by norm_num) A n 0 hη
  change (∑' n : ℕ, Y ^ n *
    AxisCoefficientSpace.coefficient window (AxisWeightEstimates.weight ε) J n η) = _
  rw [tsum_eq_single 1]
  · rw [show (1 : ℕ) = 0 + 1 by omega, hsucc]
    simp [inputValue, AxisWeightEstimates.radialDivisor]
  · intro n hn
    cases n with
    | zero => simp [hzero]
    | succ n =>
      rw [hsucc]
      have hn0 : n ≠ 0 := by omega
      rw [hA n hn0 η hη, zero_div, mul_zero]

theorem reference_u_value {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (Y : ℝ) {η : ℝ} (hη : η ∈ window.interval) :
    AxisEvaluation.profile window v.epsilon (referencePair v).2 (Y, η) =
      -(Y * NaturalAxisData.Z h j P0 η / (2 * NaturalAxisData.L h η)) := by
  let A := AxisOperators.product window v.epsilon_pos
    (v.elements .inverseL) (v.elements .zStar)
  have hA : RadiallyConstant window v.epsilon A := by
    intro n hn t ht
    rw [coefficient_product_constant window v.epsilon_pos _ _
      (v.radiallyConstant .inverseL) n ht, v.radiallyConstant .zStar n hn t ht, mul_zero]
  change AxisEvaluation.profile window v.epsilon
    (-(1 / 2 : ℝ) • AxisOperators.regularInverse window v.epsilon_pos 1 (by norm_num) A)
      (Y, η) = _
  rw [profile_smul, regularInverse_one_constant v.epsilon_pos A hA Y hη]
  have hvalue : inputValue window v.epsilon A η =
      (NaturalAxisData.L h η)⁻¹ * NaturalAxisData.Z h j P0 η := by
    change AxisCoefficientSpace.coefficient window (AxisWeightEstimates.weight v.epsilon) A 0 η = _
    rw [coefficient_product_constant window v.epsilon_pos _ _
      (v.radiallyConstant .inverseL) 0 hη]
    change inputValue window v.epsilon (v.elements .inverseL) η *
      inputValue window v.epsilon (v.elements .zStar) η = _
    rw [v.value .inverseL hη, v.value .zStar hη]
    rfl
  rw [hvalue]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem reference_u_derivative {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) {p : ℝ × ℝ} (hη : p.2 ∈ window.interval) :
    partialY (AxisEvaluation.profile window v.epsilon (referencePair v).2) p =
      -NaturalAxisData.Z h j P0 p.2 / (2 * NaturalAxisData.L h p.2) := by
  have heq : (fun Y : ℝ => AxisEvaluation.profile window v.epsilon (referencePair v).2
      (Y, p.2)) = fun Y : ℝ => -(Y * NaturalAxisData.Z h j P0 p.2 /
        (2 * NaturalAxisData.L h p.2)) := by
    funext Y
    exact reference_u_value v Y hη
  unfold partialY
  rw [heq]
  convert! (((hasDerivAt_id p.1).mul_const (NaturalAxisData.Z h j P0 p.2)).div_const
    (2 * NaturalAxisData.L h p.2)).neg.deriv using 1
  simp [neg_div]

theorem coefficient_phi_lower {h j σ Λ K : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hσ : 0 < σ) (hK : 0 ≤ K)
    (hscale : AxisReference.stabilityScale v.epsilon K ≤ Λ)
    (x : CoefficientPair v.epsilon) (hx : ‖x - referencePair v‖ ≤ K / (2 * Λ))
    {Y η : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y ≤ 41 / 10)
    (hη : η ∈ Ioo window.left window.right) :
    1 / 8 < AxisEvaluation.profile window v.epsilon x.1 (Y, η) := by
  have herr := uniformMixedError_of_norm window v.epsilon_pos x (referencePair v)
    (K / (2 * Λ)) hx
  apply AxisReference.positive_of_uniformMixedError window v.epsilon_pos
    (v.elements .chi) v.axisData v.compatible hK hscale herr hY0 hY1 hη
  · rw [v.value .chi ⟨hη.1.le, hη.2.le⟩]
    exact (NaturalAxisData.chi_bounds h j hσ η).1
  · rw [v.value .chi ⟨hη.1.le, hη.2.le⟩]
    exact (NaturalAxisData.chi_bounds h j hσ η).2.le

/-- The quantitative source inequality is proved for every actual
coefficient-space profile in the solver's error ball. The scale is chosen
before the normalization `C`. -/
theorem actual_source_lower {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ C : ℝ, 0 < C →
      ∀ x : CoefficientPair d.coefficients.epsilon,
        ‖x - referencePair d.coefficients‖ ≤ K / (2 * Λ) →
        ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet →
          (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 5 / 2 <
            Sq h (angularField h j σ Λ C x) (axialField j Λ x)
              (averageField j Λ d.coefficients.epsilon_pos x) p := by
  obtain ⟨M, hM, hsource⟩ := source_uniform_lower d.coefficients hsmall hσ hK
  refine ⟨max M (AxisReference.stabilityScale d.coefficients.epsilon K),
    hM.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ C hC x hx p hp
  have hΛpos : 0 < Λ := hM.trans_le ((le_max_left _ _).trans hΛ)
  have hval := coefficient_phi_lower d.coefficients hσ hK
    ((le_max_right _ _).trans hΛ) x hx hp.1.1 hp.1.2 (original_interval_interior hp.2)
  rw [Sq_coefficient_identity d x hΛpos hC (entrance_mem_strip hp) hval.le]
  exact hsource Λ ((le_max_left _ _).trans hΛ) x hx ⟨rescalePoint Λ p, hp⟩

theorem axialField_partialY {j Λ ε : ℝ} (hε : 0 < ε) (hΛ : Λ ≠ 0)
    (x : CoefficientPair ε) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (axialField j Λ x) p =
      partialY (AxisEvaluation.profile window ε x.2) (rescalePoint Λ p) := by
  rw [axialField, affineProfile_partialY (AxisEvaluation.profile_smooth window hε x.2)
    (NaturalAxisData.U j) (1 / Λ) Λ hp, one_div_mul_cancel hΛ, one_mul]

/-- The actual axial slope converges uniformly to the explicitly computed
reference slope, with the coefficient-space error constant. -/
theorem ns_error {h j σ Λ K : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hΛ : 0 < Λ) (_hK : 0 ≤ K)
    (x : CoefficientPair v.epsilon) (hx : ‖x - referencePair v‖ ≤ K / (2 * Λ))
    {p : ℝ × ℝ} (hp : rescalePoint Λ p ∈ entranceSet)
    (hL : NaturalAxisData.L h p.2 ≠ 0) :
    |ns (axialField j Λ x) p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2| ≤
      AxisEvaluation.jetBound v.epsilon 5 1 0 * K / Λ := by
  let q := rescalePoint Λ p
  have hq : q ∈ AxisEvaluation.strip window 20 := entrance_mem_strip hp
  have herr : |partialY (AxisEvaluation.profile window v.epsilon x.2) q -
      partialY (AxisEvaluation.profile window v.epsilon (referencePair v).2) q| ≤
        AxisEvaluation.jetBound v.epsilon 5 1 0 * (K / (2 * Λ)) := by
    rw [partialY_profile window v.epsilon_pos _ hq, partialY_profile window v.epsilon_pos _ hq]
    exact (AxisEvaluation.mixedSeries_sub_bound window v.epsilon_pos
      (by norm_num) (by norm_num) x.2 (referencePair v).2 1 0 (entrance_abs_le_five hp)).trans
      (mul_le_mul_of_nonneg_left ((norm_snd_le (x - referencePair v)).trans hx)
        (AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num) 1 0))
  have heq : ns (axialField j Λ x) p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2 =
      -2 * (partialY (AxisEvaluation.profile window v.epsilon x.2) q -
        partialY (AxisEvaluation.profile window v.epsilon (referencePair v).2) q) := by
    rw [ns, axialField_partialY v.epsilon_pos hΛ.ne' x hq,
      reference_u_derivative v ⟨hq.2.1.le, hq.2.2.le⟩]
    dsimp only [q, rescalePoint]
    field_simp ; ring
  rw [heq, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  calc
    2 * |partialY (AxisEvaluation.profile window v.epsilon x.2) q -
        partialY (AxisEvaluation.profile window v.epsilon (referencePair v).2) q| ≤
      2 * (AxisEvaluation.jetBound v.epsilon 5 1 0 * (K / (2 * Λ))) :=
        mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = AxisEvaluation.jetBound v.epsilon 5 1 0 * K / Λ := by field_simp

theorem L_le_one {h j : ℝ} (hsmall : NaturalAxisRange.Parameters h j) (η : ℝ) :
    NaturalAxisData.L h η ≤ 1 := by
  unfold NaturalAxisData.L
  nlinarith [mul_nonneg hsmall.h_pos.le (sq_nonneg η)]

/-- Where `Z*` is separated from zero, the actual axial shear is separated
from zero uniformly in the normalization. -/
theorem ns_separated {h j σ Λ K δ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hscale : 1 + 2 * AxisEvaluation.jetBound v.epsilon 5 1 0 * K / δ ≤ Λ)
    (x : CoefficientPair v.epsilon) (hx : ‖x - referencePair v‖ ≤ K / (2 * Λ))
    {p : ℝ × ℝ} (hp : rescalePoint Λ p ∈ entranceSet)
    (hZ : δ < |NaturalAxisData.Z h j P0 p.2|) :
    δ / 2 < |ns (axialField j Λ x) p| := by
  have hb := AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num : (1 : ℝ) ≤ 5) 1 0
  have hbK : 0 ≤ AxisEvaluation.jetBound v.epsilon 5 1 0 * K := mul_nonneg hb hK
  have hΛ : 0 < Λ := by
    have ht : 0 ≤ 2 * AxisEvaluation.jetBound v.epsilon 5 1 0 * K / δ := by positivity
    linarith
  have hΛ' : 2 * AxisEvaluation.jetBound v.epsilon 5 1 0 * K / δ < Λ := by linarith
  have hL : 0 < NaturalAxisData.L h p.2 := NaturalAxisRange.L_pos hsmall hp.2
  have he := ns_error v hΛ hK x hx hp hL.ne'
  have he' : |ns (axialField j Λ x) p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2| <
      δ / 2 := by
    apply he.trans_lt
    rw [div_lt_iff₀ hΛ]
    have ht := (div_lt_iff₀ hδ).mp hΛ'
    nlinarith
  have hratio : δ < |NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2| := by
    rw [abs_div, abs_of_pos hL]
    apply hZ.trans_le
    apply (le_div_iff₀ hL).mpr
    exact mul_le_of_le_one_right (abs_nonneg _) (L_le_one hsmall p.2)
  have habs := abs_sub_abs_le_abs_sub
    (NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2) (ns (axialField j Λ x) p)
  rw [abs_sub_comm] at habs
  linarith

noncomputable def profileBound {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) : ℝ :=
  1 + AxisEvaluation.jetBound v.epsilon 5 0 0 * (‖referencePair v‖ + 1)

theorem profileBound_pos {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) : 0 < profileBound v := by
  have hb := AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num : (1 : ℝ) ≤ 5) 0 0
  unfold profileBound
  positivity

theorem coefficient_profile_le {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (x : CoefficientPair v.epsilon)
    (hx : ‖x - referencePair v‖ ≤ 1) {p : ℝ × ℝ} (hp : |p.1| ≤ 5) :
    |AxisEvaluation.profile window v.epsilon x.1 p| ≤ profileBound v := by
  have hn : ‖x‖ ≤ ‖referencePair v‖ + 1 := by
    have heq : x = (x - referencePair v) + referencePair v :=
      (sub_add_cancel x (referencePair v)).symm
    calc
      ‖x‖ = ‖(x - referencePair v) + referencePair v‖ := congrArg norm heq
      _ ≤ ‖x - referencePair v‖ + ‖referencePair v‖ := norm_add_le _ _
      _ ≤ ‖referencePair v‖ + 1 := by linarith
  have hb := AxisEvaluation.mixedSeries_bound window v.epsilon_pos
    (by norm_num : (1 : ℝ) ≤ 5) (by norm_num : (5 : ℝ) < 20) x.1 0 0 hp
  rw [AxisEvaluation.mixedSeries_zero, Real.norm_eq_abs] at hb
  apply hb.trans
  have he := mul_le_mul_of_nonneg_left ((norm_fst_le x).trans hn)
    (AxisEvaluation.jetBound_nonneg v.epsilon_pos (by norm_num : (1 : ℝ) ≤ 5) 0 0)
  unfold profileBound
  linarith

theorem realAmplitude_le_threshold {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 ≤ Λ) (hC : 0 < C)
    {η : ℝ} (hη : η ∈ window.interval) :
    realAmplitude h j σ Λ C η ≤ d.normalizationThreshold Λ / C := by
  apply div_le_div_of_nonneg_right _ hC.le
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hΛ
  have h := AnalyticCoefficientBounds.re_le_realPartSup d.isCompact
    d.phase_analytic.continuousOn (d.real_mem_compact hη)
  simpa only [axisPhase_ofReal, Complex.ofReal_re] using h

/-- The normalization threshold is selected only after the scale. It
retains the analytic-amplitude threshold and supplies a uniform small
swirl bound without changing any coefficient-space constants. -/
noncomputable def entranceNormalization {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ δ : ℝ) : ℝ :=
  d.normalizationThreshold Λ * (1 + 100 * Λ * profileBound d.coefficients / δ)

theorem entranceNormalization_ge {h j σ Λ δ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 < Λ) (hδ : 0 < δ) :
    d.normalizationThreshold Λ ≤ entranceNormalization d Λ δ := by
  have hT : 0 < d.normalizationThreshold Λ := Real.exp_pos _
  have hB := profileBound_pos d.coefficients
  unfold entranceNormalization
  nlinarith [div_nonneg (by positivity : 0 ≤ 100 * Λ * profileBound d.coefficients) hδ.le]

theorem angularField_small {h j σ Λ C δ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 < Λ) (hδ : 0 < δ)
    (hC : entranceNormalization d Λ δ ≤ C)
    (x : CoefficientPair d.coefficients.epsilon) (hx : ‖x - referencePair d.coefficients‖ ≤ 1)
    {p : ℝ × ℝ} (hp : rescalePoint Λ p ∈ entranceSet) :
    100 * Λ * angularField h j σ Λ C x p ≤ δ := by
  have hT : 0 < d.normalizationThreshold Λ := Real.exp_pos _
  have hCpos : 0 < C := hT.trans_le ((entranceNormalization_ge d hΛ hδ).trans hC)
  have hB := profileBound_pos d.coefficients
  have ha := realAmplitude_le_threshold d hΛ.le hCpos
    (show p.2 ∈ window.interval from
      ⟨(original_interval_interior hp.2).1.le, (original_interval_interior hp.2).2.le⟩)
  have hφ := (le_abs_self (AxisEvaluation.profile window d.coefficients.epsilon x.1
      (rescalePoint Λ p))).trans (coefficient_profile_le d.coefficients x hx (entrance_abs_le_five hp))
  have hf : angularField h j σ Λ C x p ≤ d.normalizationThreshold Λ / C *
      profileBound d.coefficients := by
    exact (mul_le_mul_of_nonneg_left hφ (realAmplitude_pos h j σ Λ hCpos p.2).le).trans
      (mul_le_mul_of_nonneg_right ha hB.le)
  apply (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 100 * Λ)).trans
  apply (mul_le_mul_iff_left₀ hCpos).mp
  have hscalar : 100 * Λ * (d.normalizationThreshold Λ / C * profileBound d.coefficients) * C =
      100 * Λ * d.normalizationThreshold Λ * profileBound d.coefficients := by
    field_simp
  rw [hscalar]
  have hc' : d.normalizationThreshold Λ *
      (δ + 100 * Λ * profileBound d.coefficients) ≤ C * δ := by
    have hh := mul_le_mul_of_nonneg_right hC hδ.le
    have hid : entranceNormalization d Λ δ * δ = d.normalizationThreshold Λ *
        (δ + 100 * Λ * profileBound d.coefficients) := by
      unfold entranceNormalization
      field_simp
    rwa [hid] at hh
  nlinarith [mul_pos hT hδ]

theorem second_coordinate_large {Λ δ f n : ℝ}
    (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hf : 0 < f)
    (hsmall : 100 * Λ * f ≤ δ) (hn : δ / 2 < |n|) :
    (6 / 5 : ℝ) ^ 2 < ((4 / Λ) * n / (Real.sqrt (2 * (4 / Λ)) * f)) ^ 2 := by
  have hΛpos : 0 < Λ := by linarith
  have hX : 0 < 4 / Λ := by positivity
  have hprod : Λ * (4 / Λ) = 4 := by field_simp
  have hXupper : 4 / Λ ≤ 4 := by
    apply (div_le_iff₀ hΛpos).mpr
    linarith
  have hsqrt : Real.sqrt (2 * (4 / Λ)) ≤ 3 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by linarith⟩
  have hE : 0 < Real.sqrt (2 * (4 / Λ)) * f := by positivity
  have hEb : Λ * (Real.sqrt (2 * (4 / Λ)) * f) ≤ 3 * δ / 100 := by
    have hm := mul_le_mul_of_nonneg_right hsqrt hf.le
    have hm' := mul_le_mul_of_nonneg_left hm hΛpos.le
    nlinarith
  have hn' : 2 * δ < Λ * ((4 / Λ) * |n|) := by
    rw [← mul_assoc, hprod]
    linarith
  have hlarge : (6 / 5 : ℝ) * (Real.sqrt (2 * (4 / Λ)) * f) < (4 / Λ) * |n| := by
    apply (mul_lt_mul_iff_of_pos_left hΛpos).mp
    nlinarith
  have habs : |(4 / Λ) * n / (Real.sqrt (2 * (4 / Λ)) * f)| =
      (4 / Λ) * |n| / (Real.sqrt (2 * (4 / Λ)) * f) := by
    rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hE]
  have hr : (6 / 5 : ℝ) < |(4 / Λ) * n / (Real.sqrt (2 * (4 / Λ)) * f)| := by
    rw [habs]
    exact (lt_div_iff₀ hE).mpr hlarge
  nlinarith [sq_abs ((4 / Λ) * n / (Real.sqrt (2 * (4 / Λ)) * f))]

/-- A natural profile with its actual coefficient-space witness retained.
The witness supplies all radial and parameter jet bounds needed by later
continuation estimates. -/
structure CoefficientProfile {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) where
  family : ProfileFamily d Λ C
  coefficients : CoefficientPair d.coefficients.epsilon
  phi_eq : family.phi = AxisEvaluation.profile window d.coefficients.epsilon coefficients.1
  u_eq : family.u = AxisEvaluation.profile window d.coefficients.epsilon coefficients.2
  average_eq : family.average = AxisEvaluation.profile window d.coefficients.epsilon
    (AxisOperators.average window d.coefficients.epsilon_pos coefficients.2)
  norm_ball : ‖coefficients - referencePair d.coefficients‖ ≤ 1
  norm_error : ‖coefficients - referencePair d.coefficients‖ ≤ profileErrorConstant d / (2 * Λ)
  scaled : IsScaledSolution window (actualData h j σ P0) (1 / Λ)
    (realAmplitude h j σ Λ C) family.phi family.u family.average family.pressure

theorem CoefficientProfile.f_eq {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C) :
    F.family.f = angularField h j σ Λ C F.coefficients := by
  simp only [ProfileFamily.f, angularField, F.phi_eq]

theorem CoefficientProfile.U_eq {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C) :
    F.family.U = axialField j Λ F.coefficients := by
  simp only [ProfileFamily.U, axialField, F.u_eq]

theorem CoefficientProfile.Ubar_eq {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C) :
    F.family.Ubar = averageField j Λ d.coefficients.epsilon_pos F.coefficients := by
  simp only [ProfileFamily.Ubar, averageField, F.average_eq]

theorem profileErrorConstant_nonneg {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) : 0 ≤ profileErrorConstant d :=
  errorConstant_nonneg window d.coefficients.epsilon_pos (d.coefficients.elements .chi)
    d.coefficients.axisData d.amplitudeBound d.amplitudeBound_nonneg

/-- The fixed-point theorem constructs the retained witness uniformly
throughout the full allowed normalization range. -/
theorem exists_coefficientProfile {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ C : ℝ,
      d.normalizationThreshold Λ ≤ C → Nonempty (CoefficientProfile d Λ C) := by
  let v := d.coefficients
  let K := profileErrorConstant d
  have hK : 0 ≤ K := profileErrorConstant_nonneg d
  obtain ⟨M, hM, hex⟩ := AxisContraction.natural_axis_profiles window v.epsilon_pos
    (v.elements .chi) v.axisData d.amplitudeBound d.amplitudeBound_nonneg
  refine ⟨max M (AxisReference.stabilityScale v.epsilon K),
    hM.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ C hC
  have hΛpos : 0 < Λ := hM.trans_le ((le_max_left _ _).trans hΛ)
  have hscale : AxisReference.stabilityScale v.epsilon K ≤ Λ := (le_max_right _ _).trans hΛ
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  obtain ⟨a, ha, harad, havalue⟩ := d.uniformAmplitude Λ hΛpos.le C hC
  obtain ⟨x, hball, herr, hφ, hu, _, _⟩ := hex Λ ((le_max_left _ _).trans hΛ) a ha
  change ‖x - referencePair v‖ ≤ K / (2 * Λ) at herr
  have hst : 2 * (1 / (2 * Λ)) = 1 / Λ := by field_simp
  have hs := integrated_solution window v.epsilon_pos (v.elements .chi) v.axisData v.compatible
    (1 / Λ) (1 / (2 * Λ)) hst a harad x hφ hu
  have hs' := materialize_scaled v a havalue hs
  have he := uniformMixedError_of_norm window v.epsilon_pos x (referencePair v) (K / (2 * Λ)) herr
  have hpositive (Y : ℝ) (hY : Y ∈ Icc (0 : ℝ) (41 / 10))
      (η : ℝ) (hη : η ∈ Ioo window.left window.right) :
      1 / 8 < AxisEvaluation.profile window v.epsilon x.1 (Y, η) :=
    coefficient_phi_lower v hσ hK hscale x herr hY.1 hY.2 hη
  let F : ProfileFamily d Λ C := {
    phi := AxisEvaluation.profile window v.epsilon x.1
    u := AxisEvaluation.profile window v.epsilon x.2
    average := AxisEvaluation.profile window v.epsilon (AxisOperators.average window v.epsilon_pos x.2)
    pressure := AxisEvaluation.profile window v.epsilon (pressureCoefficient window v.epsilon_pos a x.1)
    natural := reconstruct_solution hsmall hΛpos hP0 (amplitude_smooth d Λ C)
      (fun η hη => d.realAmplitude_hasDerivAt Λ C ⟨hη.1.le, hη.2.le⟩) hs'
    mixed_error := he
    positive := by
      intro p hp hY0 hY1
      exact mul_pos (realAmplitude_pos h j σ Λ hCpos p.2)
        (lt_trans (by norm_num) (hpositive (Λ * p.1) ⟨hY0, hY1⟩ p.2 hp.2))
    slope := by
      intro η hη hchi
      rw [angularProfile_log_slope_at_four hΛpos hs.phi_smooth hη
        (realAmplitude_pos h j σ Λ hCpos η)
        (lt_trans (by norm_num) (hpositive 4 (by norm_num) η hη))]
      apply AxisReference.log_slope_of_uniformMixedError window v.epsilon_pos
        (v.elements .chi) v.axisData v.compatible hK hscale he hη
      · rw [v.value .chi ⟨hη.1.le, hη.2.le⟩]
        exact hchi
      · rw [v.value .chi ⟨hη.1.le, hη.2.le⟩]
        exact (NaturalAxisData.chi_bounds h j hσ η).2.le }
  exact ⟨{
    family := F
    coefficients := x
    phi_eq := rfl
    u_eq := rfl
    average_eq := rfl
    norm_ball := hball
    norm_error := herr
    scaled := hs'
  }⟩

theorem CoefficientProfile.p1_pos {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    (hsource : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet →
      0 < Sq h F.family.f F.family.U F.family.Ubar p)
    {p : ℝ × ℝ} (hp : rescalePoint Λ p ∈ entranceSet) (hX : 0 < p.1) :
    0 < p1 F.family.f p := by
  have hsegment (X : ℝ) (hX' : X ∈ Icc (0 : ℝ) p.1) :
      rescalePoint Λ (X, p.2) ∈ entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hX'.1, (mul_le_mul_of_nonneg_left hX'.2 hΛ.le).trans hp.1.2⟩, hp.2⟩
  apply p1_pos_of_source F.family.natural hΛ hX hp.1.2 hp.2 (NaturalAxisRange.L_pos hsmall hp.2)
  · intro X hX'
    exact F.family.positive (X, p.2) (entrance_mem_strip (hsegment X hX'))
      (hsegment X hX').1.1 (hsegment X hX').1.2
  · intro X hX'
    exact hsource (X, p.2) (hsegment X hX')

theorem CoefficientProfile.cone_at_four {h j σ Λ C δ : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hsmall : NaturalAxisRange.Parameters h j) (hδ : 0 < δ) (hΛ : 1 ≤ Λ)
    (hscale : 1 + 2 * AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 *
      profileErrorConstant d / δ ≤ Λ)
    (hC : entranceNormalization d Λ δ ≤ C)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ δ →
      99 / 100 < NaturalAxisData.chi h j σ η)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1)
    (hp1 : 0 < p1 F.family.f (4 / Λ, η)) :
    9 / 4 < coneSize F.family.f F.family.U (4 / Λ, η) := by
  have hΛpos : 0 < Λ := by linarith
  have hrescale : rescalePoint Λ (4 / Λ, η) = (4, η) := by
    unfold rescalePoint
    congr 1
    field_simp
  have hpoint : rescalePoint Λ (4 / Λ, η) ∈ entranceSet := by
    rw [hrescale]
    exact ⟨by norm_num, hη⟩
  by_cases hchi : 99 / 100 ≤ NaturalAxisData.chi h j σ η
  · have hs := F.family.slope η (original_interval_interior hη) hchi
    change 23 / 10 < p1 F.family.f (4 / Λ, η) at hs
    have hnonneg := div_nonneg (sq_nonneg (p2 F.family.f F.family.U (4 / Λ, η))) hp1.le
    unfold coneSize
    linarith
  · have hZ : δ < |NaturalAxisData.Z h j P0 η| := by
      by_contra hn
      exact hchi (hcut η hη (le_of_not_gt hn)).le
    have hns : δ / 2 < |ns F.family.U (4 / Λ, η)| := by
      rw [F.U_eq]
      exact ns_separated d.coefficients hsmall (profileErrorConstant_nonneg d) hδ hscale
        F.coefficients F.norm_error hpoint hZ
    have hf : 0 < F.family.f (4 / Λ, η) :=
      F.family.positive (4 / Λ, η) (entrance_mem_strip hpoint) hpoint.1.1 hpoint.1.2
    have hsmallf : 100 * Λ * F.family.f (4 / Λ, η) ≤ δ := by
      rw [F.f_eq]
      exact angularField_small d hΛpos hδ hC F.coefficients F.norm_ball hpoint
    have hb : (6 / 5 : ℝ) ^ 2 < (p2 F.family.f F.family.U (4 / Λ, η)) ^ 2 :=
      second_coordinate_large hΛ hδ hf hsmallf hns
    have hc := cone_size_of_second_large hp1 hb
    change 9 / 4 < p1 F.family.f (4 / Λ, η) +
      p2 F.family.f F.family.U (4 / Λ, η) ^ 2 / p1 F.family.f (4 / Λ, η)
    linarith

/-- The actual natural profiles satisfy the entrance test, with a fixed
strict cone margin and their complete coefficient-space witness. -/
structure EntranceProfile {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) where
  profile : CoefficientProfile d Λ C
  source_lower : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet →
    (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 5 / 2 <
      Sq h profile.family.f profile.family.U profile.family.Ubar p
  slope_positive : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet → 0 < p.1 →
    0 < p1 profile.family.f p
  cone_margin : ∀ η ∈ Icc (-1 : ℝ) 1,
    9 / 4 < coneSize profile.family.f profile.family.U (4 / Λ, η)

/-- A single large scale works for every subsequent sufficiently large
normalization. Both choices are made from the constructed analytic inputs. -/
theorem exists_entranceProfile {h j σ δ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hδ : 0 < δ)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ δ →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ C : ℝ,
      entranceNormalization d Λ δ ≤ C → Nonempty (EntranceProfile d Λ C) := by
  obtain ⟨M₁, hM₁, hfamily⟩ := exists_coefficientProfile d hsmall hσ hP0
  obtain ⟨M₂, hM₂, hsource⟩ := actual_source_lower d hsmall hσ (profileErrorConstant_nonneg d)
  let N := 1 + 2 * AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 *
    profileErrorConstant d / δ
  refine ⟨max 1 (max M₁ (max M₂ N)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ C hC
  have hΛone : 1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛone
  have hΛa := (le_max_right _ _).trans hΛ
  have hΛ₁ : M₁ ≤ Λ := (le_max_left _ _).trans hΛa
  have hΛb := (le_max_right _ _).trans hΛa
  have hΛ₂ : M₂ ≤ Λ := (le_max_left _ _).trans hΛb
  have hΛN : N ≤ Λ := (le_max_right _ _).trans hΛb
  have hCnormal : d.normalizationThreshold Λ ≤ C := (entranceNormalization_ge d hΛpos hδ).trans hC
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hCnormal
  obtain ⟨F⟩ := hfamily Λ hΛ₁ C hCnormal
  have hs : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet →
      (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 5 / 2 <
        Sq h F.family.f F.family.U F.family.Ubar p := by
    intro p hp
    rw [F.f_eq, F.U_eq, F.Ubar_eq]
    exact hsource Λ hΛ₂ C hCpos F.coefficients F.norm_error p hp
  have hspos : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet →
      0 < Sq h F.family.f F.family.U F.family.Ubar p := by
    intro p hp
    have hc : 0 ≤ NaturalAxisData.chi h j σ p.2 := (NaturalAxisData.chi_bounds h j hσ p.2).1
    have hL : 0 < NaturalAxisData.L h p.2 := NaturalAxisRange.L_pos hsmall hp.2
    have hg : 0 ≤ (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ *
      NaturalAxisData.chi h j σ p.2 := by positivity
    linarith [hs p hp]
  have ha : ∀ p : ℝ × ℝ, rescalePoint Λ p ∈ entranceSet → 0 < p.1 →
      0 < p1 F.family.f p := fun p hp hX => F.p1_pos hsmall hΛpos hspos hp hX
  refine ⟨{profile := F, source_lower := hs, slope_positive := ha, cone_margin := ?_}⟩
  intro η hη
  have hpoint : rescalePoint Λ (4 / Λ, η) ∈ entranceSet := by
    have heq : Λ * (4 / Λ) = 4 := by field_simp
    change (Λ * (4 / Λ), η) ∈ entranceSet
    rw [heq]
    exact ⟨by norm_num, hη⟩
  exact F.cone_at_four hsmall hδ hΛone hΛN hC hcut hη
    (ha (4 / Λ, η) hpoint (by positivity))

/-- Ideal-prefix pressure data produce the actual initial stress-free
cone test in the prescribed order: cutoff, common analytic radius, scale,
and only then normalization. -/
theorem ideal_prefix_entranceProfile {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      ∃ d : AnalyticInputs h j σ (PressureDatum.pressure g a),
        ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ C : ℝ,
          entranceNormalization d Λ δ ≤ C → Nonempty (EntranceProfile d Λ C) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ := ideal_prefix_analytic_inputs hsmall hp hB hg ha
  exact ⟨δ, σ, hδ, hσ, d,
    exists_entranceProfile d hsmall hσ (PressureDatum.pressure_contDiff hp) hδ hcut⟩

private theorem first_two_derivatives_continuous {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) :
    ContinuousAt (deriv g) x ∧ ContinuousAt (deriv (deriv g)) x := by
  have hfirst : ContDiffAt ℝ 1 (deriv g) x := by
    exact
      (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hsecond : ContDiffAt ℝ 0 (deriv (deriv g)) x := by
    exact
      (hfirst.fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const
  exact ⟨hfirst.continuousAt, hsecond.continuousAt⟩

theorem angular_flux_integral {g : ℝ → ℝ} (L R : ℝ)
    (hg : ∀ x ∈ uIcc (0 : ℝ) R, ContDiffAt ℝ 2 g x) :
    (∫ x in (0 : ℝ)..R, -4 * L * x * (x * deriv (deriv g) x + 2 * deriv g x)) =
      -4 * L * R ^ 2 * deriv g R := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => -4 * L * (t ^ 2 * deriv g t))
        (-4 * L * x * (x * deriv (deriv g) x + 2 * deriv g x)) x := by
    intro x hx
    convert! (radial_flux_hasDerivAt (hg x hx)).const_mul (-4 * L) using 1
    ring
  have hc : ContinuousOn (fun x : ℝ => -4 * L * x *
      (x * deriv (deriv g) x + 2 * deriv g x)) (uIcc (0 : ℝ) R) := by
    intro x hx
    have hj := first_two_derivatives_continuous (hg x hx)
    exact ((continuousAt_const.mul continuousAt_id).mul
      ((continuousAt_id.mul hj.2).add (continuousAt_const.mul hj.1))).continuousWithinAt
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, sub_zero, mul_assoc] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

theorem axial_flux_integral {g : ℝ → ℝ} (L R : ℝ)
    (hg : ∀ x ∈ uIcc (0 : ℝ) R, ContDiffAt ℝ 2 g x) :
    (∫ x in (0 : ℝ)..R, -2 * L * (x * deriv (deriv g) x + deriv g x)) =
      -2 * L * R * deriv g R := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => -2 * L * (t * deriv g t))
        (-2 * L * (x * deriv (deriv g) x + deriv g x)) x := by
    intro x hx
    have hfirst : ContDiffAt ℝ 1 (deriv g) x := by
      exact
        ((hg x hx).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    convert! ((hasDerivAt_id x).mul
      (hfirst.differentiableAt (by norm_num)).hasDerivAt).const_mul (-2 * L) using 1
    simp only [id_eq, one_mul]
    ring
  have hc : ContinuousOn (fun x : ℝ => -2 * L *
      (x * deriv (deriv g) x + deriv g x)) (uIcc (0 : ℝ) R) := by
    intro x hx
    have hj := first_two_derivatives_continuous (hg x hx)
    exact (continuousAt_const.mul
      ((continuousAt_id.mul hj.2).add hj.1)).continuousWithinAt
  simpa only [zero_mul, mul_zero, sub_zero, mul_assoc] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- The regular angular primitive of the actual source. This is the
manuscript's `Q_s`, before multiplication by `X/L`. -/
noncomputable def regularAngularLag (h : ℝ) (f U V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..p.1, (2 * x * f (x, p.2)) * Sq h f U V (x, p.2)) /
    (p.1 * (2 * p.1 * f p))

theorem angular_source_integral {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    (hf : ∀ x ∈ uIcc (0 : ℝ) p.1, f (x, p.2) ≠ 0) :
    (∫ x in (0 : ℝ)..p.1, (2 * x * f (x, p.2)) * Sq h f U V (x, p.2)) =
      -4 * NaturalAxisData.L h p.2 * p.1 ^ 2 * partialY f p := by
  have hmem (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) : (x, p.2) ∈ domain Λ :=
    domain_segment hΛ hp hx
  have hreg (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) :
      ContDiffAt ℝ 2 (fun t : ℝ => f (t, p.2)) x := by
    exact (((hs.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds (hmem x hx))).comp x
      (contDiffAt_id.prodMk contDiffAt_const))).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  calc
    _ = ∫ x in (0 : ℝ)..p.1, -4 * NaturalAxisData.L h p.2 * x *
        (x * deriv (deriv (fun t : ℝ => f (t, p.2))) x +
          2 * deriv (fun t : ℝ => f (t, p.2)) x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [Sq_eq_radial hs (hmem x hx) (hf x hx)]
      simp only [radialDifferential, partialY, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat]
      field_simp [hf x hx] ; ring
    _ = _ := angular_flux_integral (NaturalAxisData.L h p.2) p.1 hreg

theorem regularAngularLag_eq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hX : p.1 ≠ 0)
    (hf : ∀ x ∈ uIcc (0 : ℝ) p.1, f (x, p.2) ≠ 0) :
    regularAngularLag h f U V p = -2 * NaturalAxisData.L h p.2 * partialY f p / f p := by
  have hfp : f p ≠ 0 := by simpa only [Prod.eta] using hf p.1 right_mem_uIcc
  rw [regularAngularLag, angular_source_integral hs hΛ hp hf]
  field_simp ; ring

/-- The positive first coordinate is the actual scaled regular lag, not
an independently supplied slope. -/
theorem p1_eq_scaled_regularAngularLag {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hX : p.1 ≠ 0)
    (hL : NaturalAxisData.L h p.2 ≠ 0)
    (hf : ∀ x ∈ uIcc (0 : ℝ) p.1, f (x, p.2) ≠ 0) :
    p1 f p = p.1 * regularAngularLag h f U V p / NaturalAxisData.L h p.2 := by
  rw [regularAngularLag_eq hs hΛ hp hX hf]
  unfold p1
  apply (eq_div_iff hL).mpr
  ring

noncomputable def Sn (h : ℝ) (U V Pr : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -transportW h V p * (p.1 * partialY U p) -
    NaturalAxisData.A h * (1 - 2 * p.2 * U p) * U p -
    transportH h U p * partialEta U p - NaturalAxisData.d p.2 * partialEta Pr p +
    4 * NaturalAxisData.A h * p.2 * Pr p + 2 * p.2 * p.1 * partialY Pr p

noncomputable def regularAxialLag (h : ℝ) (U V Pr : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..p.1, Sn h U V Pr (x, p.2)) / p.1

theorem Sn_eq_radial {h j Λ : ℝ} {P0 a : ℝ → ℝ} {f U V Pr : ℝ × ℝ → ℝ}
    (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    Sn h U V Pr p = -2 * NaturalAxisData.L h p.2 * radialDifferential 1 U p := by
  have he := hs.axial_equation p hp
  unfold Sn
  linear_combination he

theorem axial_source_integral {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    (∫ x in (0 : ℝ)..p.1, Sn h U V Pr (x, p.2)) =
      -2 * NaturalAxisData.L h p.2 * p.1 * partialY U p := by
  have hmem (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) : (x, p.2) ∈ domain Λ :=
    domain_segment hΛ hp hx
  have hreg (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) :
      ContDiffAt ℝ 2 (fun t : ℝ => U (t, p.2)) x := by
    exact (((hs.U_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds (hmem x hx))).comp x
      (contDiffAt_id.prodMk contDiffAt_const))).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  calc
    _ = ∫ x in (0 : ℝ)..p.1, -2 * NaturalAxisData.L h p.2 *
        (x * deriv (deriv (fun t : ℝ => U (t, p.2))) x +
          deriv (fun t : ℝ => U (t, p.2)) x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [Sn_eq_radial hs (hmem x hx)]
      simp only [radialDifferential, partialY, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_one, one_mul]
    _ = _ := axial_flux_integral (NaturalAxisData.L h p.2) p.1 hreg

theorem regularAxialLag_eq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hX : p.1 ≠ 0) :
    regularAxialLag h U V Pr p = -2 * NaturalAxisData.L h p.2 * partialY U p := by
  rw [regularAxialLag, axial_source_integral hs hΛ hp]
  field_simp

theorem ns_eq_scaled_regularAxialLag {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ℝ × ℝ → ℝ} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hX : p.1 ≠ 0)
    (hL : NaturalAxisData.L h p.2 ≠ 0) :
    ns U p = regularAxialLag h U V Pr p / NaturalAxisData.L h p.2 := by
  rw [regularAxialLag_eq hs hΛ hp hX]
  unfold ns
  field_simp

/-- The constructed entrance coordinates are the dimensionless stocks
of the actual regular angular and axial primitives. -/
theorem EntranceProfile.regular_lag_coordinates {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : EntranceProfile d Λ C)
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    {p : ℝ × ℝ} (hp : rescalePoint Λ p ∈ entranceSet) (hX : 0 < p.1) :
    p1 F.profile.family.f p = p.1 * regularAngularLag h F.profile.family.f
        F.profile.family.U F.profile.family.Ubar p / NaturalAxisData.L h p.2 ∧
      p2 F.profile.family.f F.profile.family.U p =
        p.1 * regularAxialLag h F.profile.family.U F.profile.family.Ubar F.profile.family.Pi p /
          (NaturalAxisData.L h p.2 * angularVelocity F.profile.family.f p) := by
  have hL : NaturalAxisData.L h p.2 ≠ 0 := (NaturalAxisRange.L_pos hsmall hp.2).ne'
  have hdom : p ∈ domain Λ := entrance_mem_strip hp
  have hf : ∀ x ∈ uIcc (0 : ℝ) p.1, F.profile.family.f (x, p.2) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) p.1 := by simpa only [uIcc_of_le hX.le] using hx
    exact (F.profile.family.positive (x, p.2) (domain_segment hΛ hdom hx)
      (mul_nonneg hΛ.le hx'.1) ((mul_le_mul_of_nonneg_left hx'.2 hΛ.le).trans hp.1.2)).ne'
  refine ⟨p1_eq_scaled_regularAngularLag F.profile.family.natural hΛ hdom hX.ne' hL hf, ?_⟩
  have hn : ns F.profile.family.U p =
      regularAxialLag h F.profile.family.U F.profile.family.Ubar F.profile.family.Pi p /
        NaturalAxisData.L h p.2 :=
    ns_eq_scaled_regularAxialLag F.profile.family.natural hΛ hdom hX.ne' hL
  unfold p2
  rw [hn, ← mul_div_assoc, div_div]

/-- The strict entrance inequality also holds when written entirely in
terms of the source-integral stocks, with no independent stock hypotheses. -/
theorem EntranceProfile.regular_cone_at_four {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : EntranceProfile d Λ C)
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    let p : ℝ × ℝ := (4 / Λ, η)
    let q := p.1 * regularAngularLag h F.profile.family.f F.profile.family.U
      F.profile.family.Ubar p / NaturalAxisData.L h η
    let n := p.1 * regularAxialLag h F.profile.family.U F.profile.family.Ubar
      F.profile.family.Pi p / (NaturalAxisData.L h η * angularVelocity F.profile.family.f p)
    9 / 4 < q + n ^ 2 / q := by
  dsimp only
  have hpoint : rescalePoint Λ (4 / Λ, η) ∈ entranceSet := by
    have heq : Λ * (4 / Λ) = 4 := by field_simp
    change (Λ * (4 / Λ), η) ∈ entranceSet
    rw [heq]
    exact ⟨by norm_num, hη⟩
  obtain ⟨hq, hn⟩ := F.regular_lag_coordinates hsmall hΛ hpoint (by positivity)
  change p1 F.profile.family.f (4 / Λ, η) = _ at hq
  change p2 F.profile.family.f F.profile.family.U (4 / Λ, η) = _ at hn
  rw [← hq, ← hn]
  exact F.cone_margin η hη

end NavierStokes.NaturalEntrance

end
