import NavierStokes.TransitionRamp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Uniform parameter jets of the actual reference continuation -/

noncomputable section

namespace NavierStokes.ReferenceUniformJets

open Set Filter MeasureTheory ProfileHistories ReferencePath
open scoped Topology ContDiff

abbrev etaJet := TransitionRamp.parameterJet

theorem etaJet_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (n : ℕ) :
    ContDiffOn ℝ ∞ (etaJet n F) D.carrier := by
  induction n with
  | zero => exact hF
  | succ n ih => exact parameterPartial_smooth D ih

theorem etaJet_eq_iteratedDeriv (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n F p = iteratedDeriv n (fun η => F (p.1, η)) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have he : (fun η => etaJet n F (p.1, η)) =ᶠ[𝓝 p.2]
        iteratedDeriv n (fun η => F (p.1, η)) := by
      filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
        (D.isOpen.mem_nhds hp)] with η hη
      exact ih hη
    change parameterPartial (etaJet n F) p = _
    rw [iteratedDeriv_succ]
    exact (parameterPartial_hasDerivAt D (etaJet_smooth D hF n) hp).deriv.symm.trans he.deriv_eq

theorem parameterPartial_congr_on (D : RadialDomain) {F G : Field}
    (he : EqOn F G D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial F p = parameterPartial G p := by
  have hh : F =ᶠ[𝓝 p] G := by
    filter_upwards [D.isOpen.mem_nhds hp] with q hq
    exact he hq
  exact congrArg (fun A : Point →L[ℝ] ℝ => A (0, 1)) hh.fderiv_eq

theorem etaJet_congr_on (D : RadialDomain) {F G : Field}
    (he : EqOn F G D.carrier) (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n F p = etaJet n G p := by
  induction n generalizing p with
  | zero => exact he hp
  | succ n ih => exact parameterPartial_congr_on D (fun p hp => ih hp) hp

theorem etaJet_primitive (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n (primitive F) p = primitive (etaJet n F) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change parameterPartial (etaJet n (primitive F)) p = _
    rw [parameterPartial_congr_on D (fun q hq => ih hq) hp,
      parameterPartial_primitive D (etaJet_smooth D hF n) hp]
    rfl

theorem etaJet_mul_radial (D : RadialDomain) {F : Field} {c : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (hc : ContDiff ℝ ∞ c)
    (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n (fun q => c q.1 * F q) p = c p.1 * etaJet n F p := by
  have hprod : ContDiffOn ℝ ∞ (fun q : Point => c q.1 * F q) D.carrier :=
    (hc.comp contDiff_fst).contDiffOn.mul hF
  rw [etaJet_eq_iteratedDeriv D hprod n hp, etaJet_eq_iteratedDeriv D hF n hp]
  exact iteratedDeriv_const_mul (c p.1)
    (((hF.contDiffAt (D.isOpen.mem_nhds hp)).comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (TransitionRamp.nat_le_infty n))

theorem etaJet_sub (D : RadialDomain) {F G : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (hG : ContDiffOn ℝ ∞ G D.carrier)
    (n : ℕ) {p : Point} (hp : p ∈ D.carrier) :
    etaJet n (fun q => F q - G q) p = etaJet n F p - etaJet n G p := by
  rw [etaJet_eq_iteratedDeriv D (hF.sub hG) n hp,
    etaJet_eq_iteratedDeriv D hF n hp, etaJet_eq_iteratedDeriv D hG n hp]
  exact iteratedDeriv_sub
    (((hF.contDiffAt (D.isOpen.mem_nhds hp)).comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (TransitionRamp.nat_le_infty n))
    (((hG.contDiffAt (D.isOpen.mem_nhds hp)).comp p.2
      (contDiffAt_const.prodMk contDiffAt_id)).of_le (TransitionRamp.nat_le_infty n))

theorem slopeCutoff_antitone {δ : ℝ} (hδ : 0 < δ) : Antitone (slopeCutoff δ) := by
  intro s t hst
  have he := Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hst δ) hδ.le)
  unfold slopeCutoff
  linarith

theorem slopeCutoff_deriv_nonpos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    deriv (slopeCutoff δ) t ≤ 0 := (slopeCutoff_antitone hδ).deriv_nonpos

/-- The prescribed same-radius ODE has a positive averaging representation. -/
theorem continuation_parts {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {p : Point} (hp : p ∈ (earlyStrip T hT J hJ).carrier) :
    continuation δ G p = slopeCutoff δ p.1 * G p -
      primitive (fun q => deriv (slopeCutoff δ) q.1 * G q) p := by
  let D := earlyStrip T hT J hJ
  have hmem (x : ℝ) (hx : x ∈ uIcc 0 p.1) : (x, p.2) ∈ D.carrier := D.segment_mem hp hx
  have hc := slopeCutoff_smooth δ
  have hdc : Continuous (deriv (slopeCutoff δ)) := hc.continuous_deriv (by simp)
  have hg : ContinuousOn (fun x => G (x, p.2)) (uIcc 0 p.1) :=
    (radial_slice_continuous D hG p.2).mono hmem
  have hgd : ContinuousOn (fun x => radialPartial G (x, p.2)) (uIcc 0 p.1) :=
    (radial_slice_continuous D (radialPartial_smooth D hG) p.2).mono hmem
  have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hc.continuous.continuousOn hg
    (fun x _ => (hc.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun x hx => radialPartial_hasDerivAt D hG (hmem x (Ioo_subset_Icc_self hx)))
    (hdc.intervalIntegrable 0 p.1) (hgd.intervalIntegrable)
  change G (0, p.2) + (∫ x in (0 : ℝ)..p.1, slopeCutoff δ x * radialPartial G (x, p.2)) = _
  rw [he, slopeCutoff_one hδ (by linarith : (0 : ℝ) ≤ δ)]
  simp only [one_mul, primitive]
  ring

theorem continuation_etaJet_parts {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    (n : ℕ) {p : Point} (hp : p ∈ (earlyStrip T hT J hJ).carrier) :
    etaJet n (continuation δ G) p = slopeCutoff δ p.1 * etaJet n G p -
      primitive (fun q => deriv (slopeCutoff δ) q.1 * etaJet n G q) p := by
  let D := earlyStrip T hT J hJ
  have hc := slopeCutoff_smooth δ
  have hd : ContDiff ℝ ∞ (deriv (slopeCutoff δ)) := (contDiff_infty_iff_deriv.mp hc).2
  have hg : ContDiffOn ℝ ∞ (fun q : Point => deriv (slopeCutoff δ) q.1 * G q) D.carrier :=
    (hd.comp contDiff_fst).contDiffOn.mul hG
  have hprod : ContDiffOn ℝ ∞ (fun q : Point => slopeCutoff δ q.1 * G q) D.carrier := by
    simpa only [Function.comp_def] using (hc.comp contDiff_fst).contDiffOn.mul hG
  rw [etaJet_congr_on D (fun q hq => continuation_parts hT hδ hJ hG hq) n hp,
    etaJet_sub D hprod (primitive_smooth D hg) n hp,
    etaJet_mul_radial D hG hc n hp, etaJet_primitive D hg n hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact etaJet_mul_radial D hG hd n (D.segment_mem hp hx)

/-- Parameter differentiation preserves the positive-average contraction. -/
theorem continuation_etaJet_bound {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    (n : ℕ) {p : Point} (hp : p ∈ (earlyStrip T hT J hJ).carrier)
    (hp0 : 0 ≤ p.1) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ x ∈ Icc (0 : ℝ) p.1, |etaJet n G (x, p.2)| ≤ B) :
    |etaJet n (continuation δ G) p| ≤ B := by
  rw [continuation_etaJet_parts hT hδ hJ hG n hp]
  have hd := (slopeCutoff_smooth δ).continuous_deriv (by simp)
  have hi : |primitive (fun q => deriv (slopeCutoff δ) q.1 * etaJet n G q) p| ≤
      (1 - slopeCutoff δ p.1) * B := by
    have he := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hp0
      (f := fun x => deriv (slopeCutoff δ) x * etaJet n G (x, p.2))
      (g := fun x => -deriv (slopeCutoff δ) x * B)
      (Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (slopeCutoff_deriv_nonpos hδ x)]
        exact mul_le_mul_of_nonneg_left (hb x ⟨hx.1.le, hx.2⟩)
          (neg_nonneg.mpr (slopeCutoff_deriv_nonpos hδ x))))
      ((hd.neg.mul continuous_const).intervalIntegrable 0 p.1)
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => ((slopeCutoff_smooth δ).differentiable (by simp)).differentiableAt.hasDerivAt)
        (hd.intervalIntegrable 0 p.1),
      slopeCutoff_one hδ (by linarith : (0 : ℝ) ≤ δ)] at he
    simpa only [Real.norm_eq_abs, primitive, neg_sub] using he
  calc
    _ ≤ |slopeCutoff δ p.1 * etaJet n G p| +
        |primitive (fun q => deriv (slopeCutoff δ) q.1 * etaJet n G q) p| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (slopeCutoff δ p.1 * etaJet n G p)
        (primitive (fun q => deriv (slopeCutoff δ) q.1 * etaJet n G q) p)
    _ ≤ slopeCutoff δ p.1 * B + (1 - slopeCutoff δ p.1) * B := by
      apply add_le_add _ hi
      rw [abs_mul, abs_of_nonneg (slopeCutoff_mem δ p.1).1]
      exact mul_le_mul_of_nonneg_left (hb p.1 ⟨hp0, le_rfl⟩) (slopeCutoff_mem δ p.1).1
    _ = B := by ring

/-- The reference continuation preserves additive constants exactly. -/
theorem continuation_add_const (δ c : ℝ) (G : Field) (p : Point) :
    continuation δ (fun q => c + G q) p = c + continuation δ G p := by
  have hd : dampedSlope δ (fun q => c + G q) = dampedSlope δ G := by
    funext q
    simp only [dampedSlope, radialPartial, fderiv_const_add]
  simp only [continuation, hd]
  ring

/-- The bound covers the entire frozen hold, with no width-dependent constant. -/
theorem continuation_jet_bound {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hδT : 2 * δ < T) {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    (n : ℕ) {t η B : ℝ} (ht : 0 ≤ t) (hη : η ∈ J) (hB : 0 ≤ B)
    (hb : ∀ s ∈ Icc (0 : ℝ) (2 * δ),
      |iteratedDeriv n (fun ξ => G (s, ξ)) η| ≤ B) :
    |iteratedDeriv n (fun ξ => continuation δ G (t, ξ)) η| ≤ B := by
  have hs := continuation_smooth hT hδ hδT hJ hG
  have hlocal (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (2 * δ)) :
      |iteratedDeriv n (fun ξ => continuation δ G (u, ξ)) η| ≤ B := by
    rw [← etaJet_eq_iteratedDeriv (fullStrip J hJ) hs n (p := (u, η)) ⟨mem_univ _, hη⟩]
    apply continuation_etaJet_bound hT hδ hJ hG n (p := (u, η)) ⟨hu.2.trans_lt hδT, hη⟩ hu.1 hB
    intro s hs
    rw [etaJet_eq_iteratedDeriv (earlyStrip T hT J hJ) hG n (p := (s, η))
      ⟨(hs.2.trans hu.2).trans_lt hδT, hη⟩]
    exact hb s ⟨hs.1, hs.2.trans hu.2⟩
  by_cases hsmall : t ≤ 2 * δ
  · exact hlocal t ⟨ht, hsmall⟩
  · have he : (fun ξ => continuation δ G (t, ξ)) =ᶠ[𝓝 η]
        (fun ξ => continuation δ G (2 * δ, ξ)) := by
      filter_upwards [hJ.mem_nhds hη] with ξ hξ
      exact continuation_frozen hT hδ hδT hJ hG hξ (le_of_not_ge hsmall)
    rw [he.iteratedDeriv_eq n]
    exact hlocal (2 * δ) ⟨by positivity, le_rfl⟩

section NaturalReference

open NaturalProfile NaturalAxisCoefficients TransitionRamp

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

theorem short_scaled_radius {s : ℝ} (_hs0 : 0 ≤ s) (hs : s < rampLimit) :
    4 * Real.exp s ∈ Icc (0 : ℝ) (41 / 10) := by
  have he : Real.exp s < 41 / 40 := by
    simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
      Real.exp_lt_exp.mpr hs
  constructor <;> nlinarith [Real.exp_pos s]

/-- All axial parameter jets, including at the axis, use one bound chosen
before the normalization and valid for every admissible reference width. -/
theorem exists_referenceU_jets (hΛ : 0 < Λ) (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ C, ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ δ, 0 < δ → 2 * δ < rampLimit → ∀ X, 0 ≤ X → ∀ n ≤ N,
      ∀ η ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv n (fun ξ => (Input.ofNatural hΛ E.family).refU δ (X, ξ)) η| ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_naturalU_jets d hΛ N
  refine ⟨B, hB, ?_⟩
  intro C E δ hδ hδT X hX n hn η hη
  let A := Input.ofNatural hΛ E.family
  have hηJ := original_interval_interior hη
  by_cases hXi : X ≤ A.endpoint
  · have he : (fun ξ => A.refU δ (X, ξ)) = fun ξ => E.family.U (X, ξ) :=
      funext (fun ξ => A.refU_eq_natural_initial δ hXi)
    rw [he]
    apply hb C E X _ n hn η hη
    have hu := mul_le_mul_of_nonneg_left hXi hΛ.le
    have heq : Λ * A.endpoint = 4 := A.scale_endpoint
    rw [heq] at hu
    exact ⟨mul_nonneg hΛ.le hX, by linarith⟩
  · have hXp : 0 < X := A.endpoint_pos.trans (lt_of_not_ge hXi)
    have ht : 0 ≤ A.logTime X := (A.le_logTime_iff hXp).mpr
      (by simpa only [Real.exp_zero, mul_one] using (le_of_not_ge hXi))
    have he : (fun ξ => A.refU δ (X, ξ)) =ᶠ[𝓝 η]
        (fun ξ => continuation δ A.logU (A.logTime X, ξ)) := by
      filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
      exact A.refU_eq_logtime hδ hδT hξ hXp
    rw [he.iteratedDeriv_eq n]
    apply continuation_jet_bound rampLimit_pos hδ hδT parameterInterval_open A.logU_smooth
      n ht hηJ (zero_le_one.trans hB)
    intro t ht
    change |iteratedDeriv n (fun ξ => E.family.U (A.endpoint * Real.exp t, ξ)) η| ≤ B
    apply hb C E _ _ n hn η hη
    have heq : Λ * (A.endpoint * Real.exp t) = 4 * Real.exp t := by
      rw [← mul_assoc, show Λ * A.endpoint = 4 from A.scale_endpoint]
    rw [heq]
    exact short_scaled_radius ht.1 (ht.2.trans_lt hδT)

/-- The normalization cancels exactly in the logarithmic natural field. -/
theorem normalized_natural_log_identity (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C) (hC : 0 < C)
    {X η : ℝ} (hX : Λ * X ∈ Icc (0 : ℝ) (41 / 10)) (hη : η ∈ parameterInterval) :
    Real.log C + Real.log (E.family.f (X, η)) = normalizedNaturalLog d E (Λ * X) η := by
  have hphi : 0 < AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Λ * X, η) :=
    lt_trans (by norm_num) (NaturalEntrance.coefficient_phi_lower d.coefficients hσ
      (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error hX.1 hX.2 hη)
  rw [natural_normalization_identity d E hC hphi,
    Real.log_mul (inv_ne_zero hC.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  ring

noncomputable def normalizedReferenceLog {C : ℝ}
    (E : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ) (δ X η : ℝ) : ℝ :=
  Real.log C + Real.log ((Input.ofNatural hΛ E.family).refF δ (X, η))

theorem normalizedReferenceLog_smooth {C : ℝ}
    (E : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)
    {δ X : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hX : 0 ≤ X) :
    ContDiffOn ℝ ∞ (normalizedReferenceLog d E hΛ δ X) parameterInterval := by
  let A := Input.ofNatural hΛ E.family
  have hp (η : ℝ) (hη : η ∈ parameterInterval) : (X, η) ∈ A.radialDomain.carrier :=
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), hη⟩
  have hf : ContDiffOn ℝ ∞ (fun η => A.refF δ (X, η)) parameterInterval :=
    (A.refF_smooth hδ hδT).comp (contDiff_const.prodMk contDiff_id).contDiffOn hp
  exact contDiffOn_const.add (hf.log (fun η hη => (A.refF_pos δ (hp η hη) hX).ne'))

/-- Both upper and lower logarithmic bounds, in every fixed parameter jet,
are uniform before choosing `C` and over the entire allowed cutoff interval. -/
theorem exists_normalizedReferenceLog_jets (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ C, 0 < C → ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ δ, 0 < δ → 2 * δ < rampLimit → ∀ X, 0 ≤ X → ∀ n ≤ N,
      ∀ η ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv n (normalizedReferenceLog d E hΛ δ X) η| ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_normalized_natural_jets d hΛ hσ hscale N
  refine ⟨B, hB, ?_⟩
  intro C hC E δ hδ hδT X hX n hn η hη
  let A := Input.ofNatural hΛ E.family
  have hηJ := original_interval_interior hη
  by_cases hXi : X ≤ A.endpoint
  · have hY : Λ * X ∈ Icc (0 : ℝ) (41 / 10) := by
      have hu := mul_le_mul_of_nonneg_left hXi hΛ.le
      rw [show Λ * A.endpoint = 4 from A.scale_endpoint] at hu
      exact ⟨mul_nonneg hΛ.le hX, by linarith⟩
    have he : normalizedReferenceLog d E hΛ δ X =ᶠ[𝓝 η] normalizedNaturalLog d E (Λ * X) := by
      filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
      unfold normalizedReferenceLog
      rw [A.refF_eq_natural_initial δ hXi]
      exact normalized_natural_log_identity d hσ hscale E hC hY hξ
    rw [he.iteratedDeriv_eq n]
    exact hb C E (Λ * X) hY n hn η hη
  · have hXp : 0 < X := A.endpoint_pos.trans (lt_of_not_ge hXi)
    have ht : 0 ≤ A.logTime X := (A.le_logTime_iff hXp).mpr
      (by simpa only [Real.exp_zero, mul_one] using (le_of_not_ge hXi))
    let G : ProfileHistories.Field := fun p => Real.log C + A.logF p
    have hG : ContDiffOn ℝ ∞ G (earlyStrip rampLimit rampLimit_pos parameterInterval parameterInterval_open).carrier :=
      contDiffOn_const.add A.logF_smooth
    have he : normalizedReferenceLog d E hΛ δ X =ᶠ[𝓝 η]
        (fun ξ => continuation δ G (A.logTime X, ξ)) := by
      filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
      unfold normalizedReferenceLog
      rw [A.refF_eq_logtime hδ hδT hξ hXp, Real.log_exp]
      exact (continuation_add_const δ (Real.log C) A.logF _).symm
    rw [he.iteratedDeriv_eq n]
    apply continuation_jet_bound rampLimit_pos hδ hδT parameterInterval_open hG n ht hηJ
      (zero_le_one.trans hB)
    intro s hs
    have hY := short_scaled_radius hs.1 (hs.2.trans_lt hδT)
    have heq : Λ * (A.endpoint * Real.exp s) = 4 * Real.exp s := by
      rw [← mul_assoc, show Λ * A.endpoint = 4 from A.scale_endpoint]
    have he : (fun ξ => G (s, ξ)) =ᶠ[𝓝 η] normalizedNaturalLog d E (4 * Real.exp s) := by
      filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
      change Real.log C + Real.log (E.family.f (A.endpoint * Real.exp s, ξ)) = _
      rw [normalized_natural_log_identity d hσ hscale E hC (heq ▸ hY) hξ, heq]
    rw [he.iteratedDeriv_eq n]
    exact hb C E (4 * Real.exp s) hY n hn η hη


theorem normalizedReferenceF_identity {C : ℝ}
    (E : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ) (hC : 0 < C)
    (δ : ℝ) {X η : ℝ} (hX : 0 ≤ X) (hη : η ∈ parameterInterval) :
    C * (Input.ofNatural hΛ E.family).refF δ (X, η) =
      Real.exp (normalizedReferenceLog d E hΛ δ X η) := by
  let A := Input.ofNatural hΛ E.family
  have hp : (X, η) ∈ A.radialDomain.carrier :=
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), hη⟩
  rw [normalizedReferenceLog, Real.exp_add, Real.exp_log hC,
    Real.exp_log (A.refF_pos δ hp hX)]

/-- Normalized angular fields and their reciprocals have uniform all-order
parameter bounds, including on the natural part of the reference. -/
theorem exists_normalizedReferenceF_jets (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) :
    ∃ K, 1 ≤ K ∧ ∀ C, 0 < C → ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ δ, 0 < δ → 2 * δ < rampLimit → ∀ X, 0 ≤ X → ∀ n ≤ N,
      ∀ η ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv n (fun ξ => C * (Input.ofNatural hΛ E.family).refF δ (X, ξ)) η| ≤ K ∧
        |iteratedDeriv n (fun ξ => (C * (Input.ofNatural hΛ E.family).refF δ (X, ξ))⁻¹) η| ≤ K := by
  obtain ⟨B, hB, hb⟩ := exists_normalizedReferenceLog_jets d hΛ hσ hscale N
  obtain ⟨K, hK, hk⟩ := finite_majorant (fun n => n.factorial * Real.exp B * B ^ n) N
  refine ⟨K, hK, ?_⟩
  intro C hC E δ hδ hδT X hX n hn η hη
  let A := Input.ofNatural hΛ E.family
  let L := normalizedReferenceLog d E hΛ δ X
  have hηJ := original_interval_interior hη
  have hL := normalizedReferenceLog_smooth d E hΛ hδ hδT hX
  have hLb (i : ℕ) (hi : i ≤ n) : |iteratedDeriv i L η| ≤ B :=
    hb C hC E δ hδ hδT X hX i (hi.trans hn) η hη
  have he : (fun ξ => C * A.refF δ (X, ξ)) =ᶠ[𝓝 η] (fun ξ => Real.exp (L ξ)) := by
    filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
    exact normalizedReferenceF_identity d E hΛ hC δ hX hξ
  have hi : (fun ξ => (C * A.refF δ (X, ξ))⁻¹) =ᶠ[𝓝 η] (fun ξ => Real.exp (-L ξ)) := by
    filter_upwards [he] with ξ hξ
    rw [hξ, Real.exp_neg]
  constructor
  · rw [he.iteratedDeriv_eq n]
    exact (exp_jet_bound_local parameterInterval_open hL hηJ n hB hLb).trans (hk n hn)
  · rw [hi.iteratedDeriv_eq n]
    exact (exp_jet_bound_local parameterInterval_open hL.neg hηJ n hB
      (fun i hi => by simpa only [iteratedDeriv_fun_neg, abs_neg] using hLb i hi)).trans (hk n hn)

/-- The unnormalized angular field has its actual `C⁻¹` scale, uniformly
through the reference cutoff and the arbitrarily long frozen hold. -/
theorem referenceF_jet_of_normalized {C δ X η K : ℝ}
    (E : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ) (hC : 0 < C)
    (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hX : 0 ≤ X)
    (hη : η ∈ parameterInterval) (n : ℕ)
    (hb : |iteratedDeriv n (fun ξ => C * (Input.ofNatural hΛ E.family).refF δ (X, ξ)) η| ≤ K) :
    |iteratedDeriv n (fun ξ => (Input.ofNatural hΛ E.family).refF δ (X, ξ)) η| ≤ K / C := by
  let A := Input.ofNatural hΛ E.family
  have hp : (X, η) ∈ A.radialDomain.carrier :=
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), hη⟩
  have hs := ((A.refF_smooth hδ hδT).contDiffAt (A.radialDomain.isOpen.mem_nhds hp)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)
  rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hC] at hb
  exact (le_div_iff₀ hC).mpr (by simpa only [mul_comm] using hb)

end NaturalReference

end NavierStokes.ReferenceUniformJets
