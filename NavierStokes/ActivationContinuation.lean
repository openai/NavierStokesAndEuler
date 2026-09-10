import NavierStokes.ReferenceBounds
import NavierStokes.ActivationCone
import NavierStokes.TransitionRamp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The relaxed continuation after the initial activation

The comparison formulas use actual stock coordinates. The scalar barrier
uses the differential equation of the primitive-defined angular lag.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActivationContinuation

open ProfileHistories


noncomputable def shearSize (a b : ℝ) : ℝ := a * (1 + (b / a) ^ 2)
noncomputable def projection (p q a b : ℝ) : ℝ := p + q * (b / a)
noncomputable def transverse (p q a b : ℝ) : ℝ := q - p * (b / a)

structure Relaxed (a b p q : ℝ) : Prop where
  first_positive : 0 < a
  projection_positive : 2 < projection p q a b
  cone : shearSize a b < ConeAlgebra.coneBound (projection p q a b) (transverse p q a b)

noncomputable def projectionConstant (M : ℝ) : ℝ := 1 + 2 * M + M ^ 2
noncomputable def speedConstant (M : ℝ) : ℝ := M * (1 + 4 * M ^ 2)

theorem projectionConstant_pos {M : ℝ} (hM : 0 ≤ M) : 0 < projectionConstant M := by
  unfold projectionConstant
  positivity

theorem speedConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ speedConstant M := by
  unfold speedConstant
  positivity

/-- The axial shutoff factor occurs once in the limiting projection. -/
theorem projection_identity (A B p q θ R : ℝ) :
    p + q * (θ * (B / A) * R) - (A + θ * B ^ 2 / A) =
      (p - A) + (q - B) * θ * (B / A) * R + θ * B * (B / A) * (R - 1) := by
  ring

theorem projection_comparison {A B p q θ R M ε : ℝ} (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hB : |B| ≤ M) (hBA : |B / A| ≤ M)
    (hp : |p - A| ≤ ε) (hq : |q - B| ≤ ε) (hR : |R - 1| ≤ ε) :
    |p + q * (θ * (B / A) * R) - (A + θ * B ^ 2 / A)| ≤
      ε * projectionConstant M := by
  have hR2 : |R| ≤ 2 := by
    have ht := abs_sub R 1
    have he : R = (R - 1) + 1 := by ring
    have hh := abs_add_le (R - 1) 1
    rw [← he] at hh
    norm_num at hh
    linarith
  rw [projection_identity]
  calc
    _ ≤ |p - A| + |q - B| * |θ| * |B / A| * |R| +
        |θ| * |B| * |B / A| * |R - 1| := by
      exact ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)).trans_eq (by simp only [abs_mul])
    _ ≤ ε + ε * 1 * M * 2 + 1 * M * M * ε := by
      rw [abs_of_nonneg hθ.1]
      gcongr <;> first | exact hθ.1 | exact hθ.2
    _ = _ := by unfold projectionConstant; ring

theorem damped_shear_ratio {κ A : ℝ} (hκ : κ ≠ 0) (hA : A ≠ 0) (θ B R : ℝ) :
    (κ * θ * B * R) / (κ * A) = θ * (B / A) * R := by
  field_simp

theorem damped_shear_bound {κ A B θ R M : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hM : 0 ≤ M) (hAM : A ≤ M) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hBA : |B / A| ≤ M) (hR : |R| ≤ 2) :
    shearSize (κ * A) (κ * θ * B * R) ≤ κ * speedConstant M := by
  have hr : |θ * (B / A) * R| ≤ 2 * M := by
    rw [abs_mul, abs_mul, abs_of_nonneg hθ.1]
    calc
      θ * |B / A| * |R| ≤ 1 * M * 2 := by gcongr; exact hθ.2
      _ = _ := by ring
  have hrsq : (θ * (B / A) * R) ^ 2 ≤ (2 * M) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hr 2
  rw [shearSize, damped_shear_ratio hκ.ne' hA.ne']
  calc
    _ ≤ (κ * M) * (1 + (2 * M) ^ 2) := by gcongr
    _ = _ := by unfold speedConstant; ring

/-- Uniform finite-dimensional comparison for both the constant-damping
segment and the axial shutoff. No inverse power of the damping is used. -/
theorem damped_relaxed {κ A B p q θ R M ε : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hM : 0 ≤ M) (hAM : A ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hB : |B| ≤ M) (hBA : |B / A| ≤ M)
    (hp : |p - A| ≤ ε) (hq : |q - B| ≤ ε) (hR : |R - 1| ≤ ε)
    (hprojection : (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A)
    (herror : ε * projectionConstant M ≤ 1 / 8)
    (hspeed : κ * speedConstant M ≤ 1) :
    Relaxed (κ * A) (κ * θ * B * R) p q := by
  have hcmp := projection_comparison hM hε hε1 hθ hB hBA hp hq hR
  have hproj : 2 < projection p q (κ * A) (κ * θ * B * R) := by
    rw [projection, damped_shear_ratio hκ.ne' hA.ne']
    have hh := (abs_le.mp hcmp).1
    linarith
  have hR2 : |R| ≤ 2 := by
    have hh := abs_add_le (R - 1) 1
    have he : R - 1 + 1 = R := by ring
    rw [he] at hh
    norm_num at hh
    linarith
  have hv : shearSize (κ * A) (κ * θ * B * R) ≤ 2 :=
    (damped_shear_bound hκ hA hM hAM hθ hBA hR2).trans (hspeed.trans (by norm_num))
  exact ⟨mul_pos hκ hA, hproj, ConeAlgebra.relaxed_cone_of_le_two hproj hv⟩

theorem zero_axial_relaxed {a p q : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) (hp : 2 < p) :
    Relaxed a 0 p q := by
  have hproj : projection p q a 0 = p := by simp [projection]
  have hv : shearSize a 0 = a := by simp [shearSize]
  refine ⟨ha, ?_, ?_⟩
  · rwa [hproj]
  · rw [hv, hproj]
    exact ConeAlgebra.relaxed_cone_of_le_two hp ha2

theorem convex_final_shear {a θ : ℝ} (ha : 0 < a) (ha4 : a ≤ 4 / 5)
    (hθ : θ ∈ Icc (0 : ℝ) 1) :
    0 < (1 - θ) * a + θ * (4 / 5) ∧ (1 - θ) * a + θ * (4 / 5) ≤ 4 / 5 := by
  constructor
  · by_cases hz : θ = 0
    · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using ha
    · have hp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hθ.2) ha.le)
        (mul_pos hp (by norm_num))
  · have hm := mul_le_mul_of_nonneg_left ha4 (sub_nonneg.mpr hθ.2)
    linarith

/-! ## Physical cone coordinates -/

section Physical

variable {D : RadialDomain} (P : Profiles D)

noncomputable def shearA (p : Point) : ℝ := -2 * p.1 * radialPartial P.f p / P.f p
noncomputable def shearB (p : Point) : ℝ := -2 * p.1 * radialPartial P.U p / P.E p

noncomputable def IsRelaxed (h : ℝ) (p : Point) : Prop :=
  Relaxed (shearA P p) (shearB P p) (ReferenceBounds.p1 P h p) (ReferenceBounds.p2 P h p)

theorem logSlope_eq_shear (p : Point) :
    ReferenceBounds.logSlope P p = 1 - shearA P p / 2 := by
  unfold ReferenceBounds.logSlope shearA
  ring

theorem zero_axial_relaxed_profile {h : ℝ} {p : Point} (ha : 0 < shearA P p)
    (ha2 : shearA P p ≤ 2) (hu : radialPartial P.U p = 0)
    (hp : 2 < ReferenceBounds.p1 P h p) : IsRelaxed P h p := by
  unfold IsRelaxed
  rw [show shearB P p = 0 by simp [shearB, hu]]
  exact zero_axial_relaxed ha ha2 hp

end Physical

/-! ## An exact barrier for the final constant-slope hold -/

noncomputable def weightedGap (g : ℝ → ℝ) (b X : ℝ) : ℝ :=
  Real.exp ((3 / 5 : ℝ) * Real.log X) * (g X - b)

theorem weightedGap_hasDerivAt {g : ℝ → ℝ} {g' X : ℝ} (hX : 0 < X)
    (hg : HasDerivAt g g' X) (b : ℝ) :
    HasDerivAt (weightedGap g b)
      (Real.exp ((3 / 5 : ℝ) * Real.log X) / X *
        (X * g' + (3 / 5) * g X - (3 / 5) * b)) X := by
  have hd := (((Real.hasDerivAt_log hX.ne').const_mul (3 / 5 : ℝ)).exp).mul (hg.sub_const b)
  convert! hd using 1
  field_simp ; ring

theorem scalar_hold_barrier {g : ℝ → ℝ} {a X b : ℝ} (ha : 0 < a) (haX : a ≤ X)
    (hg : ∀ t ∈ Icc a X, DifferentiableAt ℝ g t)
    (heq : ∀ t ∈ Icc a X, (3 / 5 : ℝ) * b ≤ t * deriv g t + (3 / 5) * g t)
    (hinit : b < g a) : b < g X := by
  have hd (t : ℝ) (ht : t ∈ Icc a X) :=
    weightedGap_hasDerivAt (ha.trans_le ht.1) (hg t ht).hasDerivAt b
  have hm : MonotoneOn (weightedGap g b) (Icc a X) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a X)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le (ha.trans_le ht'.1).le)
        (sub_nonneg.mpr (heq t ht'))
  have hin : 0 < weightedGap g b a := mul_pos (Real.exp_pos _) (sub_pos.mpr hinit)
  have hout := hin.trans_le (hm ⟨le_rfl, haX⟩ ⟨haX, le_rfl⟩ haX)
  change 0 < Real.exp ((3 / 5 : ℝ) * Real.log X) * (g X - b) at hout
  exact sub_pos.mp (pos_of_mul_pos_right hout (Real.exp_pos _).le)

theorem actual_hold_barrier {D : RadialDomain} (P : Profiles D) {h η a X : ℝ}
    (ha : 2 ≤ a) (haX : a ≤ X) (hL : 0 < NaturalAxisData.L h η)
    (hL1 : NaturalAxisData.L h η ≤ 1)
    (hmem : ∀ t ∈ Icc a X, (t, η) ∈ D.carrier)
    (hf : ∀ t ∈ Icc a X, 0 < P.f (t, η))
    (hl : ∀ t ∈ Icc a X, ReferenceBounds.logSlope P (t, η) = 3 / 5)
    (hs : ∀ t ∈ Icc a X, 1 < ReferenceBounds.sourceQ P h (t, η))
    (hinit : 2 < ReferenceBounds.p1 P h (a, η)) :
    2 < ReferenceBounds.p1 P h (X, η) := by
  apply scalar_hold_barrier (g := fun t => ReferenceBounds.p1 P h (t, η))
    (by linarith : (0 : ℝ) < a) haX ?_ ?_ hinit
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by linarith : (0 : ℝ) < a) ht.1
    have hlag := P.angularLag_smoothAt h (hmem t ht) htpos.ne' (P.H_ne_zero htpos.ne' (hf t ht).ne')
    exact ((contDiffAt_id.mul (hlag.comp t (contDiffAt_id.prodMk contDiffAt_const))).div_const
      (NaturalAxisData.L h η)).differentiableAt (by simp)
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by linarith : (0 : ℝ) < a) ht.1
    have he := ReferenceBounds.p1_equation P (hmem t ht) htpos (hf t ht).ne' h
    rw [hl t ht] at he
    change _ = t * ReferenceBounds.sourceQ P h (t, η) / NaturalAxisData.L h η at he
    rw [he]
    apply (le_div_iff₀ hL).mpr
    have ht2 : 2 ≤ t := ha.trans ht.1
    have hst := hs t ht
    nlinarith

/-! ## The final hold source is derived from the axis model -/

open NaturalAxisCoefficients

noncomputable def holdVector (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![1, v 1, v 2, v 3, v 4]

noncomputable def holdRemainder (h j σ η : ℝ) (v : Fin 5 → ℝ) (t : ℝ) : ℝ :=
  ReferenceBounds.qRemainder h j σ (1, η) 1 (holdVector v) t (-2 / 5)

abbrev HoldParameter (B : ℝ) := Icc (-1 : ℝ) 1 × ReferenceBounds.BoundedJets B

noncomputable def holdModel (h j σ B : ℝ) (p : HoldParameter B) (t : ℝ) : ℝ :=
  holdRemainder h j σ p.1.val p.2.val t

theorem holdModel_continuous (h j B : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun p : HoldParameter B × ℝ => holdModel h j σ B p.1 p.2) := by
  let m : HoldParameter B × ℝ → ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) :=
    fun p => ((((1, p.1.1.val), 1), holdVector p.1.2.val), (p.2, -2 / 5))
  have hvj (i : Fin 5) : Continuous (fun p : HoldParameter B × ℝ => p.1.2.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hv : Continuous (fun p : HoldParameter B × ℝ => holdVector p.1.2.val) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_const
    · exact hvj 1
    · exact hvj 2
    · exact hvj 3
    · exact hvj 4
  have hm : Continuous m := by
    dsimp only [m]
    fun_prop
  simpa only [holdModel, holdRemainder, m, Function.comp_def] using
    (ReferenceBounds.qRemainder_continuous h j hσ).comp hm

theorem hold_axis_source_lower {h j η : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    (17 / 10 : ℝ) < -(3 / 5 : ℝ) * NaturalAxisData.W h j η -
      h * (1 - 2 * η * NaturalAxisData.U j η) := by
  have hW := NaturalAxisData.neg_W_lower_bound hsmall hη
  have habs : |η| ≤ 1 := abs_le.mpr hη
  have hu : |NaturalAxisData.U j η| ≤ 4001 / 1000 := by
    calc
      _ ≤ |4 * η| + |j| := abs_add_le _ _
      _ = 4 * |η| + j := by rw [abs_mul, abs_of_pos hsmall.j_pos]; norm_num
      _ ≤ _ := by linarith [hsmall.j_le]
  have hp : |η * NaturalAxisData.U j η| ≤ 4001 / 1000 := by
    rw [abs_mul]
    exact (mul_le_mul habs hu (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hfac : 1 - 2 * η * NaturalAxisData.U j η ≤ 4501 / 500 := by
    have hh := (abs_le.mp hp).1
    linarith
  have hm := mul_le_mul_of_nonneg_left hfac hsmall.h_pos.le
  have hh := mul_le_mul_of_nonneg_right hsmall.h_le (by norm_num : (0 : ℝ) ≤ 4501 / 500)
  linarith

theorem holdModel_chi_zero (h j B : ℝ) {σ : ℝ} (hσ : 0 < σ) (p : HoldParameter B)
    (hchi : NaturalAxisData.chi h j σ p.1.val = 0) :
    holdModel h j σ B p 0 = -(3 / 5 : ℝ) * NaturalAxisData.W h j p.1.val -
      h * (1 - 2 * p.1.val * NaturalAxisData.U j p.1.val) := by
  have hH := NaturalEntrance.chi_zero_imp_H_zero h j hσ hchi
  have hk := NaturalEntrance.gradient_zero_of_chi_zero h j hσ hchi
  norm_num [holdModel, holdRemainder, holdVector, ReferenceBounds.qRemainder, hH, hk]
  ring

theorem holdModel_uniform_lower {h j σ : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (B : ℝ) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ p : HoldParameter B,
      (5 / 4 : ℝ) < NaturalAxisData.L h p.1.val * Λ * NaturalAxisData.chi h j σ p.1.val +
        holdModel h j σ B p (1 / Λ) := by
  have he : Continuous (fun p : HoldParameter B => p.1.val) := by fun_prop
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  have hcoef : Continuous (fun p : HoldParameter B =>
      NaturalAxisData.L h p.1.val * NaturalAxisData.chi h j σ p.1.val) :=
    (hL.comp he).mul ((NaturalEntrance.chi_continuous h j hσ).comp he)
  have hbase : Continuous (fun p : HoldParameter B => holdModel h j σ B p 0) := by
    simpa only [Function.comp_def, id_eq] using (holdModel_continuous h j B hσ).comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))
  obtain ⟨M0, hM0, habsorb⟩ := NaturalEntrance.compact_absorption _ _ hcoef hbase
    (fun p => mul_nonneg (NaturalAxisData.L_pos hsmall p.1.property).le
      (NaturalAxisData.chi_bounds h j hσ p.1.val).1) (3 / 2 : ℝ) (by
        intro p hz
        have hchi := (mul_eq_zero.mp hz).resolve_left (NaturalAxisData.L_pos hsmall p.1.property).ne'
        rw [holdModel_chi_zero h j B hσ p hchi]
        linarith [hold_axis_source_lower hsmall p.1.property])
  obtain ⟨τ, hτ, hpert⟩ := NaturalEntrance.compact_small_perturbation _
    (holdModel_continuous h j B hσ) (by norm_num : (0 : ℝ) < 1 / 4)
  let M := max M0 (1 + 1 / τ)
  refine ⟨M, hM0.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ p
  have hΛ0 : 0 < Λ := hM0.trans_le ((le_max_left _ _).trans hΛ)
  have hscale := (le_max_right M0 (1 + 1 / τ)).trans hΛ
  have hnorm : ‖1 / Λ‖ < τ := by
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    have hm := (div_lt_iff₀ hτ).mp (show 1 / τ < Λ by linarith)
    nlinarith
  have hp := (abs_lt.mp (hpert p (1 / Λ) hnorm)).1
  have hm := habsorb Λ ((le_max_left _ _).trans hΛ) p
  nlinarith

theorem hold_source_identity {D : RadialDomain} (P : Profiles D) (h j σ : ℝ)
    {Λ : ℝ} (hΛ : Λ ≠ 0) (p : Point)
    (hl : ReferenceBounds.logSlope P p = 3 / 5) :
    ReferenceBounds.sourceQ P h p = NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
      holdRemainder h j σ p.2 (ReferenceBounds.qJets P j σ h Λ 1 p) (1 / Λ) := by
  have hrad : p.1 * radialPartial P.f p / P.f p = (1 : ℝ) * 1 * (-2 / 5) / 1 := by
    unfold ReferenceBounds.logSlope at hl
    linarith
  have hv : holdVector (ReferenceBounds.qJets P j σ h Λ 1 p) = ReferenceBounds.qJets P j σ h Λ 1 p := by
    ext i
    fin_cases i <;> rfl
  unfold holdRemainder
  rw [hv]
  exact ReferenceBounds.sourceQ_model P h j σ hΛ (by norm_num : (1 / 8 : ℝ) ≤ 1) p hrad

theorem actual_hold_source_threshold {h j σ B : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) (hB : 1 ≤ B) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
      |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
      |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
      |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
      (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p := by
  obtain ⟨M, hM, hb⟩ := holdModel_uniform_lower hsmall hσ B
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ D P p hη hl hu hv hvη hfη
  have hj := ReferenceBounds.qJets_bound P h j σ (zero_le_one.trans hB)
    (φ := 1) (by simpa only [abs_one] using hB) hu hv hvη hfη
  have hh := hb Λ hΛ (⟨p.2, hη⟩, ⟨ReferenceBounds.qJets P j σ h Λ 1 p, hj⟩)
  rw [hold_source_identity P h j σ (hM.trans_le hΛ).ne' p hl]
  exact hh

/-! ## Uniform transfer of actual field and history jets to the stocks -/

theorem compact_vector_perturbation {K E F : Type*} [MetricSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
    (G : K × E → F) (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p e, ‖e‖ < δ → ‖G (p, e) - G (p, 0)‖ < ε := by
  have hc : IsCompact ((univ : Set K) ×ˢ Metric.closedBall (0 : E) 1) :=
    isCompact_univ.prod (isCompact_closedBall 0 1)
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hG.continuousOn) ε hε
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
  simpa only [dist_eq_norm] using hb (p, e) hp (p, 0) hp0 hd

abbrev StockJet := Fin 12 → ℝ

noncomputable def stockJet {D : RadialDomain} (P : Profiles D) (p : Point) : StockJet :=
  ![P.f p, P.U p, P.M p, parameterPartial P.M p, P.I p, parameterPartial P.I p,
    P.J p, parameterPartial P.J p, P.S p, parameterPartial P.S p,
    P.pressure p, parameterPartial P.pressure p]

noncomputable def stockOneMap (h : ℝ) (p : Point) (z : StockJet) : ℝ :=
  ActivationStocks.stockOne h p.1 p.2 (z 0) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)

noncomputable def stockTwoMap (h : ℝ) (p : Point) (z : StockJet) : ℝ :=
  ActivationStocks.stockTwo h p.1 p.2 (z 0) (z 1) (z 2) (z 3) (z 8) (z 9) (z 10) (z 11)

theorem stockJet_coordinates {D : RadialDomain} (P : Profiles D) (h : ℝ)
    {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stockOneMap h p (stockJet P p) = ReferenceBounds.p1 P h p ∧
      stockTwoMap h p (stockJet P p) = ReferenceBounds.p2 P h p := by
  constructor
  · exact (ActivationStocks.profileStockOne_eq P h hp hX.ne' hf).symm
  · have he := (ActivationStocks.profileStockTwo_eq P h hp hX).symm
    change stockTwoMap h p (stockJet P p) = p.1 * P.axialLag h p /
      (NaturalAxisData.L h p.2 * P.E p) at he
    rw [he]
    unfold ReferenceBounds.p2 ReferenceBounds.ns
    ring

abbrev StockBall (B : ℝ) := Metric.closedBall (0 : StockJet) B

instance (B : ℝ) : CompactSpace (StockBall B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

noncomputable def clippedStockMap (h μ : ℝ) (p : Point) (z e : StockJet) : Fin 3 → ℝ :=
  let w := z + e
  let f := max μ (w 0)
  ![ActivationStocks.stockOne h p.1 p.2 f (w 2) (w 3) (w 4) (w 5) (w 6) (w 7),
    ActivationStocks.stockTwo h p.1 p.2 f (w 1) (w 2) (w 3) (w 8) (w 9) (w 10) (w 11),
    z 0 / f]

theorem clippedStockMap_continuous {h j μ B : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hμ : 0 < μ) {S : Set Point}
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    Continuous (fun q : (S × StockBall B) × StockJet =>
      clippedStockMap h μ q.1.1.val q.1.2.val q.2) := by
  have hx : ∀ q : (S × StockBall B) × StockJet, q.1.1.val.1 ≠ 0 :=
    fun q => (hX q.1.1.val q.1.1.property).ne'
  have hl : ∀ q : (S × StockBall B) × StockJet, NaturalAxisData.L h q.1.1.val.2 ≠ 0 :=
    fun q => (NaturalAxisData.L_pos hsmall (hη q.1.1.val q.1.1.property)).ne'
  have hf : ∀ q : (S × StockBall B) × StockJet, max μ ((q.1.2.val + q.2) 0) ≠ 0 :=
    fun q => (hμ.trans_le (le_max_left _ _)).ne'
  have hs : ∀ q : (S × StockBall B) × StockJet, Real.sqrt (2 * q.1.1.val.1) ≠ 0 :=
    fun q => (Real.sqrt_pos.mpr (mul_pos (by norm_num) (hX q.1.1.val q.1.1.property))).ne'
  have hz : Continuous (fun q : (S × StockBall B) × StockJet => q.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hw := hz.add (continuous_snd : Continuous (fun q : (S × StockBall B) × StockJet => q.2))
  have hj (i : Fin 12) : Continuous (fun q : (S × StockBall B) × StockJet => (q.1.2.val + q.2) i) :=
    (continuous_apply i).comp hw
  have hz0 := (continuous_apply (0 : Fin 12)).comp hz
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun q : (S × StockBall B) × StockJet =>
      ActivationStocks.stockOne h q.1.1.val.1 q.1.1.val.2 (max μ ((q.1.2.val + q.2) 0))
        ((q.1.2.val + q.2) 2) ((q.1.2.val + q.2) 3) ((q.1.2.val + q.2) 4)
        ((q.1.2.val + q.2) 5) ((q.1.2.val + q.2) 6) ((q.1.2.val + q.2) 7))
    unfold ActivationStocks.stockOne ActivationStocks.massFlux ActivationStocks.angularRemainder
    unfold NaturalAxisData.L NaturalAxisData.D NaturalAxisData.d
    fun_prop (disch := first | exact hl | exact fun q => mul_ne_zero (mul_ne_zero (by norm_num) (hx q)) (hf q))
  · change Continuous (fun q : (S × StockBall B) × StockJet =>
      ActivationStocks.stockTwo h q.1.1.val.1 q.1.1.val.2 (max μ ((q.1.2.val + q.2) 0))
        ((q.1.2.val + q.2) 1) ((q.1.2.val + q.2) 2) ((q.1.2.val + q.2) 3)
        ((q.1.2.val + q.2) 8) ((q.1.2.val + q.2) 9) ((q.1.2.val + q.2) 10) ((q.1.2.val + q.2) 11))
    unfold ActivationStocks.stockTwo ActivationStocks.massFlux
    unfold NaturalAxisData.L NaturalAxisData.D NaturalAxisData.d NaturalAxisData.A
    fun_prop (disch := exact fun q => mul_ne_zero (mul_ne_zero (hl q) (hs q)) (hf q))
  · change Continuous (fun q : (S × StockBall B) × StockJet => q.1.2.val 0 / max μ ((q.1.2.val + q.2) 0))
    fun_prop (disch := exact hf)

/-- Uniform stock continuity on a bounded set of actual profile/history
jets. The threshold is independent of the particular reference member. -/
theorem uniform_stock_transfer {h j μ B ε : ℝ}
    (hsmall : NaturalAxisData.SmallParameters h j) (hμ : 0 < μ) (hε : 0 < ε)
    {S : Set Point} (hS : IsCompact S)
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    ∃ τ > 0, ∀ p ∈ S, ∀ z w : StockJet, ‖z‖ ≤ B → 2 * μ ≤ z 0 → ‖w - z‖ < τ →
      μ < w 0 ∧ |stockOneMap h p w - stockOneMap h p z| < ε ∧
        |stockTwoMap h p w - stockTwoMap h p z| < ε ∧ |z 0 / w 0 - 1| < ε := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨r, hr, hb⟩ := compact_vector_perturbation
    (fun q : (S × StockBall B) × StockJet => clippedStockMap h μ q.1.1.val q.1.2.val q.2)
    (clippedStockMap_continuous hsmall hμ hX hη) hε
  refine ⟨min r μ, lt_min hr hμ, ?_⟩
  intro p hp z w hz hz0 he
  have he0 : |w 0 - z 0| < μ := by
    have hh := norm_le_pi_norm (w - z) 0
    rw [Real.norm_eq_abs] at hh
    exact hh.trans_lt (he.trans_le (min_le_right _ _))
  have hw0 : μ < w 0 := by have hh := (abs_lt.mp he0).1; linarith
  have hzμ : μ ≤ z 0 := by linarith
  have hzmem : z ∈ Metric.closedBall (0 : StockJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb (⟨p, hp⟩, ⟨z, hzmem⟩) (w - z) (he.trans_le (min_le_left _ _))
  have heq : z + (w - z) = w := by abel
  have hzero : z + (0 : StockJet) = z := add_zero _
  have hcoord (i : Fin 3) := (norm_le_pi_norm
    (clippedStockMap h μ p z (w - z) - clippedStockMap h μ p z 0) i).trans_lt hh
  refine ⟨hw0, ?_, ?_, ?_⟩
  · simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val_zero, Real.norm_eq_abs, stockOneMap] using hcoord 0
  · simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs, stockTwoMap] using hcoord 1
  · have hzn : z 0 ≠ 0 := (hμ.trans_le hzμ).ne'
    simpa only [clippedStockMap, heq, hzero, max_eq_right hw0.le, max_eq_right hzμ,
      Pi.sub_apply, Matrix.cons_val, Matrix.cons_val_zero, Real.norm_eq_abs, div_self hzn] using hcoord 2

/-! ## The five history rows follow from actual first parameter jets -/

open StressActivation

abbrev FieldJet := Fin 4 → ℝ

noncomputable def fieldJet {D : RadialDomain} (P : Profiles D) (p : Point) : FieldJet :=
  ![P.f p, P.U p, parameterPartial P.f p, parameterPartial P.U p]

noncomputable def densityJet (X : ℝ) (z : FieldJet) : Fin 10 → ℝ :=
  ![z 1, z 3, 2 * X * z 0, 2 * X * z 2,
    z 1 * (2 * X * z 0), z 3 * (2 * X * z 0) + z 1 * (2 * X * z 2),
    z 1 ^ 2 - X * z 0 ^ 2, 2 * z 1 * z 3 - 2 * X * z 0 * z 2,
    z 0 ^ 2, 2 * z 0 * z 2]

theorem densityJet_continuous : Continuous (fun p : ℝ × FieldJet => densityJet p.1 p.2) := by
  unfold densityJet
  repeat' apply Continuous.matrixVecCons
  all_goals fun_prop

noncomputable def valueIndex (r : HistoryRow) : Fin 10 :=
  HistoryRow.rec (motive := fun _ => Fin 10) 0 2 4 6 8 r

noncomputable def derivativeIndex (r : HistoryRow) : Fin 10 :=
  HistoryRow.rec (motive := fun _ => Fin 10) 1 3 5 7 9 r

theorem densityJet_value {D : RadialDomain} (P : Profiles D) (r : HistoryRow) (p : Point) :
    densityJet p.1 (fieldJet P p) (valueIndex r) = profileDensity P r p := by
  cases r <;> rfl

theorem densityJet_derivative {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) :
    densityJet p.1 (fieldJet P p) (derivativeIndex r) = parameterPartial (profileDensity P r) p := by
  cases r with
  | mass => rfl
  | angular => exact (P.parameterPartial_H hp).symm
  | transport =>
    change _ = parameterPartial P.transportDensity p
    rw [P.parameterPartial_transportDensity hp, P.parameterPartial_H hp]
    rfl
  | energy => exact (P.parameterPartial_energyDensity hp).symm
  | pressure => exact (ReferenceBounds.parameterPartial_square P hp).symm

theorem profileHistory_parameter_formula {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (profileHistory P r) p = deriv (profileInitial P r) p.2 +
      primitive (parameterPartial (profileDensity P r)) p := by
  cases r with
  | mass =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.U_smooth hp
  | angular =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.H_smooth hp
  | transport =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.transportDensity_smooth hp
  | energy =>
    simp only [profileHistory, profileInitial, deriv_const, zero_add]
    exact parameterPartial_primitive D P.energyDensity_smooth hp
  | pressure =>
    change parameterPartial P.pressure p = _
    rw [P.parameterPartial_pressure hp, parameterPartial_primitive D (P.f_smooth.pow 2) hp]
    rfl

theorem profileHistory_difference {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h0 : P.pressure0 = Q.pressure0) (r : HistoryRow) {p : Point}
    (hp : p ∈ D.carrier) (hq : p ∈ E.carrier) :
    profileHistory P r p - profileHistory Q r p =
      ∫ t in (0 : ℝ)..p.1, profileDensity P r (t, p.2) - profileDensity Q r (t, p.2) := by
  have hi : profileInitial P r = profileInitial Q r := by cases r <;> first | rfl | exact h0
  rw [profileHistory_eq_initial_add_primitive, profileHistory_eq_initial_add_primitive, hi]
  rw [add_sub_add_left_eq_sub]
  exact (intervalIntegral.integral_sub
    (radial_slice_intervalIntegrable D (profileDensity_smooth P r) hp)
    (radial_slice_intervalIntegrable E (profileDensity_smooth Q r) hq)).symm

theorem profileHistory_parameter_difference {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h0 : P.pressure0 = Q.pressure0) (r : HistoryRow) {p : Point}
    (hp : p ∈ D.carrier) (hq : p ∈ E.carrier) :
    parameterPartial (profileHistory P r) p - parameterPartial (profileHistory Q r) p =
      ∫ t in (0 : ℝ)..p.1, parameterPartial (profileDensity P r) (t, p.2) -
        parameterPartial (profileDensity Q r) (t, p.2) := by
  have hi : profileInitial P r = profileInitial Q r := by cases r <;> first | rfl | exact h0
  rw [profileHistory_parameter_formula P r hp, profileHistory_parameter_formula Q r hq, hi]
  rw [add_sub_add_left_eq_sub]
  exact (intervalIntegral.integral_sub
    (radial_slice_intervalIntegrable D (parameterPartial_smooth D (profileDensity_smooth P r)) hp)
    (radial_slice_intervalIntegrable E (parameterPartial_smooth E (profileDensity_smooth Q r)) hq)).symm

abbrev FieldBall (B : ℝ) := Metric.closedBall (0 : FieldJet) B

instance (B : ℝ) : CompactSpace (FieldBall B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

theorem uniform_density_transfer (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ X ∈ Icc (0 : ℝ) 110, ∀ z w : FieldJet,
      ‖z‖ ≤ B → ‖w - z‖ < τ → ‖densityJet X w - densityJet X z‖ < ε := by
  let G : ((Icc (0 : ℝ) 110) × FieldBall B) × FieldJet → Fin 10 → ℝ :=
    fun q => densityJet q.1.1.val (q.1.2.val + q.2)
  have hc : Continuous G := by
    have hm : Continuous (fun q : ((Icc (0 : ℝ) 110) × FieldBall B) × FieldJet =>
        (q.1.1.val, q.1.2.val + q.2)) := by fun_prop
    exact densityJet_continuous.comp hm
  obtain ⟨τ, hτ, hb⟩ := compact_vector_perturbation G hc hε
  refine ⟨τ, hτ, ?_⟩
  intro X hX z w hz he
  have hz' : z ∈ Metric.closedBall (0 : FieldJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb (⟨X, hX⟩, ⟨z, hz'⟩) (w - z) he
  have heq : z + (w - z) = w := by abel
  simpa only [G, heq, add_zero] using hh

theorem short_integral_bound {f : ℝ → ℝ} {X ε : ℝ}
    (hX : X ∈ Icc (0 : ℝ) 110) (hε : 0 < ε)
    (hf : ∀ t ∈ Icc (0 : ℝ) X, |f t| ≤ ε / 111) :
    |∫ t in (0 : ℝ)..X, f t| < ε := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := X) (C := ε / 111) (f := f) (fun t ht => by
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Ioc (0 : ℝ) X := (uIoc_of_le hX.1 ▸ ht)
      exact hf t ⟨ht'.1.le, ht'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX.1] at hb
  have hm := mul_le_mul_of_nonneg_left hX.2 (show 0 ≤ ε / 111 by positivity)
  have hn : ε / 111 * 110 < ε := by linarith
  exact (hb.trans hm).trans_lt hn

/-- Uniform first-jet closeness of actual fields gives uniform closeness of
all five actual history rows and their first parameter derivatives. -/
theorem field_to_stockJet_transfer (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ {D E : RadialDomain} (P : Profiles D) (Q : Profiles E),
      P.pressure0 = Q.pressure0 → ∀ p : Point, p ∈ D.carrier → p ∈ E.carrier →
      p.1 ∈ Icc (0 : ℝ) 110 →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet Q (t, p.2)‖ ≤ B) →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet P (t, p.2) - fieldJet Q (t, p.2)‖ < τ) →
      ‖stockJet P p - stockJet Q p‖ < ε := by
  obtain ⟨r, hr, hmap⟩ := uniform_density_transfer B (ε := ε / 111) (by positivity)
  refine ⟨min ε r, lt_min hε hr, ?_⟩
  intro D E P Q h0 p hp hq hX hB he
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) :
      ‖densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))‖ < ε / 111 :=
    hmap t ⟨ht.1, ht.2.trans hX.2⟩ _ _ (hB t ht) ((he t ht).trans_le (min_le_right _ _))
  have hhist (r : HistoryRow) :
      |profileHistory P r p - profileHistory Q r p| < ε ∧
      |parameterPartial (profileHistory P r) p - parameterPartial (profileHistory Q r) p| < ε := by
    constructor
    · rw [profileHistory_difference P Q h0 r hp hq]
      apply short_integral_bound hX hε
      intro t ht
      have hh := (norm_le_pi_norm
        (densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))) (valueIndex r)).trans_lt (hd t ht)
      simpa only [Real.norm_eq_abs, Pi.sub_apply, densityJet_value P r (t, p.2),
        densityJet_value Q r (t, p.2)] using hh.le
    · rw [profileHistory_parameter_difference P Q h0 r hp hq]
      apply short_integral_bound hX hε
      intro t ht
      have htp := D.segment_mem hp (uIcc_of_le hX.1 ▸ ht)
      have htq := E.segment_mem hq (uIcc_of_le hX.1 ▸ ht)
      have hh := (norm_le_pi_norm
        (densityJet t (fieldJet P (t, p.2)) - densityJet t (fieldJet Q (t, p.2))) (derivativeIndex r)).trans_lt (hd t ht)
      simpa only [Real.norm_eq_abs, Pi.sub_apply, densityJet_derivative P r htp,
        densityJet_derivative Q r htq] using hh.le
  have hfield : ‖fieldJet P p - fieldJet Q p‖ < ε := by
    exact (he p.1 ⟨hX.1, le_rfl⟩).trans_le (min_le_left _ _)
  apply (pi_norm_lt_iff hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (norm_le_pi_norm (fieldJet P p - fieldJet Q p) 0).trans_lt hfield
  · exact (norm_le_pi_norm (fieldJet P p - fieldJet Q p) 1).trans_lt hfield
  · exact (hhist .mass).1
  · exact (hhist .mass).2
  · exact (hhist .angular).1
  · exact (hhist .angular).2
  · exact (hhist .transport).1
  · exact (hhist .transport).2
  · exact (hhist .energy).1
  · exact (hhist .energy).2
  · exact (hhist .pressure).1
  · exact (hhist .pressure).2

theorem uniform_density_bound (B : ℝ) :
    ∃ K ≥ 0, ∀ X ∈ Icc (0 : ℝ) 110, ∀ z : FieldJet, ‖z‖ ≤ B → ‖densityJet X z‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : FieldJet) B)).exists_bound_of_continuousOn
    densityJet_continuous.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro X hX z hz
  exact (hK (X, z) ⟨hX, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz⟩).trans (le_max_left _ _)

theorem integral_bounded_length {f : ℝ → ℝ} {X K : ℝ} (hX : X ∈ Icc (0 : ℝ) 110)
    (hK : 0 ≤ K) (hf : ∀ t ∈ Icc (0 : ℝ) X, |f t| ≤ K) :
    |∫ t in (0 : ℝ)..X, f t| ≤ 110 * K := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := X) (C := K) (f := f) (fun t ht => by
      rw [Real.norm_eq_abs]
      have ht' : t ∈ Ioc (0 : ℝ) X := (uIoc_of_le hX.1 ▸ ht)
      exact hf t ⟨ht'.1.le, ht'.2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX.1] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left hX.2 hK).trans_eq (mul_comm K 110))

/-- A bounded actual first field jet gives a uniform bound for every stock
input, including both pressure entries. This bound precedes the small ramps. -/
theorem stockJet_uniform_bound {B B0 : ℝ} (hB : 0 ≤ B) (hB0 : 0 ≤ B0) :
    ∃ K > 0, ∀ {D : RadialDomain} (P : Profiles D) (p : Point), p ∈ D.carrier →
      p.1 ∈ Icc (0 : ℝ) 110 → |P.pressure0 p.2| ≤ B0 → |deriv P.pressure0 p.2| ≤ B0 →
      (∀ t ∈ Icc (0 : ℝ) p.1, ‖fieldJet P (t, p.2)‖ ≤ B) → ‖stockJet P p‖ ≤ K := by
  obtain ⟨K0, hK0, hb⟩ := uniform_density_bound B
  let K := 1 + B + B0 + 110 * K0
  have hK : 0 < K := by dsimp [K]; positivity
  have hBK : B ≤ K := by dsimp [K]; nlinarith
  have hHK : B0 + 110 * K0 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro D P p hp hX hp0 hp0' hfield
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) := hb t ⟨ht.1, ht.2.trans hX.2⟩ _ (hfield t ht)
  have hhist (r : HistoryRow) :
      |profileHistory P r p| ≤ K ∧ |parameterPartial (profileHistory P r) p| ≤ K := by
    have hini : |profileInitial P r p.2| ≤ B0 := by
      cases r <;> simpa only [profileInitial, abs_zero] using (by assumption)
    have hini' : |deriv (profileInitial P r) p.2| ≤ B0 := by
      cases r <;> simpa only [profileInitial, deriv_const, abs_zero] using (by assumption)
    have hv : |primitive (profileDensity P r) p| ≤ 110 * K0 := by
      apply integral_bounded_length hX hK0
      intro t ht
      have hh := (norm_le_pi_norm (densityJet t (fieldJet P (t, p.2))) (valueIndex r)).trans (hd t ht)
      simpa only [Real.norm_eq_abs, densityJet_value P r (t, p.2)] using hh
    have he : |primitive (parameterPartial (profileDensity P r)) p| ≤ 110 * K0 := by
      apply integral_bounded_length hX hK0
      intro t ht
      have htp := D.segment_mem hp (uIcc_of_le hX.1 ▸ ht)
      have hh := (norm_le_pi_norm (densityJet t (fieldJet P (t, p.2))) (derivativeIndex r)).trans (hd t ht)
      simpa only [Real.norm_eq_abs, densityJet_derivative P r htp] using hh
    constructor
    · rw [profileHistory_eq_initial_add_primitive]
      exact ((abs_add_le _ _).trans (add_le_add hini hv)).trans hHK
    · rw [profileHistory_parameter_formula P r hp]
      exact ((abs_add_le _ _).trans (add_le_add hini' he)).trans hHK
  have hpfield : ‖fieldJet P p‖ ≤ B := hfield p.1 ⟨hX.1, le_rfl⟩
  apply (pi_norm_le_iff_of_nonneg hK.le).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (norm_le_pi_norm (fieldJet P p) 0).trans (hpfield.trans hBK)
  · exact (norm_le_pi_norm (fieldJet P p) 1).trans (hpfield.trans hBK)
  · exact (hhist .mass).1
  · exact (hhist .mass).2
  · exact (hhist .angular).1
  · exact (hhist .angular).2
  · exact (hhist .transport).1
  · exact (hhist .transport).2
  · exact (hhist .energy).1
  · exact (hhist .energy).2
  · exact (hhist .pressure).1
  · exact (hhist .pressure).2

theorem uniform_stock_bound {h j μ B : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hμ : 0 < μ) {S : Set Point} (hS : IsCompact S)
    (hX : ∀ p ∈ S, 0 < p.1) (hη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1) :
    ∃ M > 0, ∀ p ∈ S, ∀ z : StockJet, ‖z‖ ≤ B → μ ≤ z 0 →
      |stockOneMap h p z| ≤ M ∧ |stockTwoMap h p z| ≤ M := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hc : Continuous (fun q : S × StockBall B => clippedStockMap h μ q.1.val q.2.val 0) := by
    simpa only [Function.comp_def, id_eq] using (clippedStockMap_continuous hsmall hμ hX hη).comp
      (continuous_id.prodMk (continuous_const (y := (0 : StockJet))))
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1 + |M|, by positivity, ?_⟩
  intro p hp z hz hf
  have hz' : z ∈ Metric.closedBall (0 : StockJet) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hM (⟨p, hp⟩, ⟨z, hz'⟩) (mem_univ _)
  have hh0 := (norm_le_pi_norm (clippedStockMap h μ p z 0) 0).trans hh
  have hh1 := (norm_le_pi_norm (clippedStockMap h μ p z 0) 1).trans hh
  constructor
  · have he : |stockOneMap h p z| ≤ M := by
      simpa only [clippedStockMap, add_zero, max_eq_right hf, Matrix.cons_val_zero,
        stockOneMap, Real.norm_eq_abs] using hh0
    linarith [le_abs_self M]
  · have he : |stockTwoMap h p z| ≤ M := by
      simpa only [clippedStockMap, add_zero, max_eq_right hf, Matrix.cons_val_one, Matrix.cons_val_zero,
        stockTwoMap, Real.norm_eq_abs] using hh1
    linarith [le_abs_self M]

/-! ## Uniform comparison constants from the concrete reference -/

theorem reference_first_lower {h j σ Λ C δ : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    (hb : ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) (hX : 0 < p.1) :
    (6 / 5 : ℝ) * p.1 ≤ ReferenceBounds.p1 (ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0) h p := by
  let P := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  have hL := NaturalAxisData.L_pos hsmall hp.2
  have hL1 := NaturalEntrance.L_le_one (NaturalAxisRange.ofSmall hsmall) p.2
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) p.1) :
      (12 / 5 : ℝ) ≤ ReferenceBounds.sourceQ P h (t, p.2) := by
    have hm := hb.source_lower (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩
    have hn : 0 ≤ (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le)
        (NaturalAxisData.chi_bounds h j hσ p.2).1
    change _ < ReferenceBounds.sourceQ P h (t, p.2) at hm
    linarith
  have hlow := ReferenceBounds.p1_lower_from_source P
    (ReferenceBounds.reference_mem E.profile hΛ hp.1.1 hp.2) hX h hL
    (by norm_num : (0 : ℝ) ≤ 12 / 5)
    (fun t ht => N.refF_pos δ (ReferenceBounds.reference_mem E.profile hΛ (p := (t, p.2)) ht.1 hp.2) ht.1)
    (ReferenceBounds.reference_antitone E hΛ hδ hδT hP0 hX.le hp.2) hsource
  apply le_trans _ hlow
  apply (le_div_iff₀ (mul_pos (by norm_num) hL)).mpr
  nlinarith

noncomputable def expJet (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp p.1, Real.exp p.1 * p.2)

theorem expJet_continuous : Continuous expJet := by unfold expJet; fun_prop

theorem expJet_uniform (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ z w : ℝ × ℝ, ‖z‖ ≤ B → ‖w - z‖ < τ → ‖expJet w - expJet z‖ < ε := by
  let : CompactSpace (Metric.closedBall (0 : ℝ × ℝ) B) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hc : Continuous (fun q : Metric.closedBall (0 : ℝ × ℝ) B × (ℝ × ℝ) => expJet (q.1.val + q.2)) :=
    expJet_continuous.comp ((continuous_subtype_val.comp continuous_fst).add continuous_snd)
  obtain ⟨τ, hτ, hb⟩ := compact_vector_perturbation _ hc hε
  refine ⟨τ, hτ, ?_⟩
  intro z w hz he
  have hz' : z ∈ Metric.closedBall (0 : ℝ × ℝ) B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hh := hb ⟨z, hz'⟩ (w - z) he
  simpa only [add_sub_cancel, add_zero] using hh

theorem comparison_tolerances {M : ℝ} (hM : 0 ≤ M) :
    ∃ ε κstar : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < κstar ∧ κstar < 1 ∧
      ε * projectionConstant M ≤ 1 / 8 ∧
      κstar * speedConstant M ≤ 1 ∧ κstar * M ≤ 4 / 5 := by
  let ε := min 1 (1 / (8 * projectionConstant M))
  let κstar := 1 / (2 * (1 + speedConstant M + M))
  have hp := projectionConstant_pos hM
  have hv := speedConstant_nonneg hM
  have hkden : 0 < 2 * (1 + speedConstant M + M) := by linarith
  have hk : 0 < κstar := one_div_pos.mpr hkden
  have hkeq : κstar * (2 * (1 + speedConstant M + M)) = 1 := by
    dsimp [κstar]
    exact one_div_mul_cancel hkden.ne'
  refine ⟨ε, κstar, lt_min zero_lt_one (one_div_pos.mpr (mul_pos (by norm_num) hp)),
    min_le_left _ _, hk, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hk.le hv, mul_nonneg hk.le hM]
  · have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hp)).mp (min_le_right 1 (1 / (8 * projectionConstant M)))
    dsimp [ε]
    nlinarith
  · nlinarith [mul_nonneg hk.le hM]
  · nlinarith [mul_nonneg hk.le hv]

theorem reference_fieldJet_bound {D : RadialDomain} (P : Profiles D)
    {h j σ Λ C B K : ℝ} (hsmall : NaturalAxisData.SmallParameters h j)
    (hΛ : 1 ≤ Λ) (hC : 1 ≤ C) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K P.f P.U)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) :
    ‖fieldJet P p‖ ≤ K + B + 6 := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hf : K / C ≤ K := (div_le_iff₀ hC0).mpr (by nlinarith)
  have hu := hj.axial_value p hp
  have huη := hj.axial_parameter p hp
  rw [abs_mul, abs_of_pos hΛ0] at hu huη
  have hdu : |P.U p - NaturalAxisData.U j p.2| ≤ B := by
    nlinarith [abs_nonneg (P.U p - NaturalAxisData.U j p.2)]
  have hduη : |parameterPartial P.U p - 4| ≤ B := by
    nlinarith [abs_nonneg (parameterPartial P.U p - 4)]
  have hη : |p.2| ≤ 1 := abs_le.mpr hp.2
  have hstar : |NaturalAxisData.U j p.2| ≤ 5 := by
    calc
      _ ≤ |4 * p.2| + |j| := abs_add_le _ _
      _ = 4 * |p.2| + j := by rw [abs_mul, abs_of_pos hsmall.j_pos]; norm_num
      _ ≤ 5 := by linarith [hsmall.j_le]
  have huabs : |P.U p| ≤ B + 5 := by
    have hh := abs_add_le (P.U p - NaturalAxisData.U j p.2) (NaturalAxisData.U j p.2)
    rw [sub_add_cancel] at hh
    linarith
  have hueabs : |parameterPartial P.U p| ≤ B + 4 := by
    have hh := abs_add_le (parameterPartial P.U p - 4) (4 : ℝ)
    rw [sub_add_cancel] at hh
    norm_num at hh
    linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ K + B + 6)).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact (hj.angular_value p hp).trans (hf.trans (by linarith))
  · exact huabs.trans (by linarith)
  · exact (hj.angular_parameter p hp).trans (hf.trans (by linarith))
  · exact hueabs.trans (by linarith)

theorem pressure_initial_bound {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0) :
    ∃ B0 > 0, ∀ η ∈ Icc (-1 : ℝ) 1, |P0 η| ≤ B0 ∧ |deriv P0 η| ≤ B0 := by
  have hc : Continuous (fun η => (P0 η, deriv P0 η)) :=
    hP0.continuous.prodMk (hP0.continuous_deriv (by simp))
  obtain ⟨B0, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨1 + |B0|, by positivity, ?_⟩
  intro η hη
  have hh := hb η hη
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hh
  exact ⟨hh.1.trans (by linarith [le_abs_self B0]), hh.2.trans (by linarith [le_abs_self B0])⟩

section ReferenceEndpoint

open ReferencePath
variable (N : ReferencePath.Input)

theorem endpoint_field_continuous :
    ContinuousOn (fun η => N.f (N.endpoint, η)) (Icc (-1 : ℝ) 1) := by
  intro η hη
  exact ((N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
    (ReferenceJetBounds.endpoint_mem N hη))).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt

noncomputable def endpointLogJet (η : ℝ) : ℝ × ℝ :=
  (Real.log (N.f (N.endpoint, η)), parameterPartial N.f (N.endpoint, η) / N.f (N.endpoint, η))

theorem endpointLogJet_bound : ∃ B0 ≥ 0, ∀ η ∈ Icc (-1 : ℝ) 1, ‖endpointLogJet N η‖ ≤ B0 := by
  have hpart : ContDiffOn ℝ ∞ (parameterPartial N.f) (NaturalProfile.domain N.scale) :=
    (N.f_smooth.fderiv_of_isOpen (NaturalProfile.domain_isOpen N.scale) (by simp)).clm_apply contDiffOn_const
  have hc : ContinuousOn (endpointLogJet N) (Icc (-1 : ℝ) 1) := by
    intro η hη
    have hm := ReferenceJetBounds.endpoint_mem N hη
    have hf := (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hm)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
    have hg := (hpart.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hm)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
    have hn := (N.endpoint_f_pos (original_interval_interior hη)).ne'
    exact ((hf.log hn).prodMk (hg.div hf hn)).continuousWithinAt
  obtain ⟨B0, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max B0 0, le_max_right _ _, fun η hη => (hb η hη).trans (le_max_left _ _)⟩

theorem reference_positive_uniform :
    ∃ μ r : ℝ, 0 < μ ∧ 0 < r ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 → 2 * μ ≤ N.refF δ p := by
  obtain ⟨α, hα, hmin⟩ := UniformCone.positive_uniform_margin isCompact_Icc
    (endpoint_field_continuous N) (fun η hη => N.endpoint_f_pos (original_interval_interior hη))
  obtain ⟨r, hr, hb⟩ := N.ref_relative_error_jet_close isCompact_Icc original_interval_interior 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨α / 4, r, by positivity, hr, ?_⟩
  intro δ hδ hδr p hx hη
  have hh := hb δ hδ hδr p.1 hx p.2 hη
  rw [iteratedDeriv_zero] at hh
  have hp := N.endpoint_f_pos (original_interval_interior hη)
  have hl : (1 / 2 : ℝ) < N.refF δ p / N.f (N.endpoint, p.2) := by
    have hs := (abs_lt.mp hh).1
    change _ < N.refF δ p / N.f (N.endpoint, p.2) - 1 at hs
    linarith
  have hf := (lt_div_iff₀ hp).mp hl
  have hm := hmin p.2 hη
  linarith

theorem reference_endpoint_control {εU εF εL : ℝ} (hU : 0 < εU) (hF : 0 < εF) (hL : 0 < εL) :
    ∃ r > 0, ∀ δ : ℝ, 0 < δ → δ < r →
      ReferenceJetBounds.TransitionControl N δ εU εF ∧
      ∀ p : Point, N.endpoint ≤ p.1 → p.2 ∈ Icc (-1 : ℝ) 1 →
        |parameterPartial (N.refF δ) p / N.refF δ p -
          parameterPartial N.f (N.endpoint, p.2) / N.f (N.endpoint, p.2)| < εL := by
  obtain ⟨r0, hr0, hc⟩ := ReferenceJetBounds.exists_transition_control N hU hF
  obtain ⟨r1, hr1, hl⟩ := N.ref_log_error_jet_close isCompact_Icc original_interval_interior 1 hL
  refine ⟨min r0 r1, lt_min hr0 hr1, ?_⟩
  intro δ hδ hr
  have ht := hc δ hδ (hr.trans_le (min_le_left _ _))
  refine ⟨ht, ?_⟩
  intro p hx hη
  have hp := ReferenceJetBounds.reference_mem N (N.endpoint_pos.le.trans hx) hη
  have hpn := ReferenceJetBounds.endpoint_mem N hη
  have hh := hl δ hδ (hr.trans_le (min_le_right _ _)) p.1 hx p.2 hη
  rw [ReferenceJetBounds.first_log_difference
    ((N.refF_smooth hδ ht.length_bound).contDiffAt (N.radialDomain.isOpen.mem_nhds hp))
    (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hpn))
    (N.refF_pos δ hp (N.endpoint_pos.le.trans hx)).ne'
    (N.endpoint_f_pos (original_interval_interior hη)).ne'] at hh
  exact hh

end ReferenceEndpoint

/-! ## Ordered preparation and transfer of normalized source jets -/

/-- The scale and pressure normalization are chosen before any small
activation parameter.  Both estimates concern the same actual REF fields. -/
theorem ordered_reference_preparation {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ B M : ℝ, 1 < B ∧ 1 ≤ M ∧
      ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
        (∀ {D : RadialDomain} (P : Profiles D) (p : Point),
          p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
          |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 2 →
          |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 →
          |Λ * (average (parameterPartial P.U) p - 4)| ≤ B + 2 →
          |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B + 2 →
          (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p) ∧
        ∃ C0 K : ℝ, 1 ≤ C0 ∧ 0 < K ∧
          ∀ C : ℝ, C0 ≤ C → ∃ E : NaturalEntrance.EntranceProfile d Λ C,
            ∃ r > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r →
              ∃ hδT : 2 * δ < ReferencePath.rampLimit,
                ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 ∧
                ReferenceJetBounds.JetBounds h j σ Λ C B K
                  ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
                  ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ) := by
  obtain ⟨B, Mj, Kerr, hB, hMj, hKerr, hjets⟩ := ReferenceJetBounds.ordered_reference_bounds d hσ
  obtain ⟨Mh, hMh, hhold⟩ := actual_hold_source_threshold hsmall hσ (B := B + 2) (by linarith)
  obtain ⟨Mr, hMr, href⟩ := ReferenceBounds.exists_reference_bounds d hsmall hσ hP0 hν hcut
  let M := max 1 (max Mj (max Mh Mr))
  refine ⟨B, M, hB, le_max_left _ _, ?_⟩
  intro Λ hΛ hM
  have hMjΛ : Mj ≤ Λ := (le_trans (le_max_left _ _) (le_max_right 1 _)).trans hM
  have hMhΛ : Mh ≤ Λ := (le_trans (le_max_left Mh Mr)
    (le_trans (le_max_right Mj _) (le_max_right 1 _))).trans hM
  have hMrΛ : Mr ≤ Λ := (le_trans (le_max_right Mh Mr)
    (le_trans (le_max_right Mj _) (le_max_right 1 _))).trans hM
  refine ⟨hhold Λ hMhΛ, ?_⟩
  obtain ⟨K, hK, hj⟩ := hjets Λ hΛ hMjΛ
  obtain ⟨Cr, hCr, hr⟩ := href Λ hΛ hMrΛ
  let C0 := max 1 (max Cr (d.normalizationThreshold Λ))
  refine ⟨C0, K, le_max_left _ _, hK, ?_⟩
  intro C hC
  have hCrC : Cr ≤ C := (le_trans (le_max_left _ _) (le_max_right 1 _)).trans hC
  have hnC : d.normalizationThreshold Λ ≤ C :=
    (le_trans (le_max_right _ _) (le_max_right 1 _)).trans hC
  obtain ⟨E, r0, hr0, he⟩ := hr C hCrC
  obtain ⟨r1, hr1, hj1⟩ := hj C hnC E.profile
  refine ⟨E, min r0 r1, lt_min hr0 hr1, ?_⟩
  intro δ hδ hdr
  obtain ⟨hδT, hb⟩ := he δ hδ (hdr.trans_le (min_le_left _ _))
  exact ⟨hδT, hb, (hj1 δ hδ (hdr.trans_le (min_le_right _ _))).2.1⟩

/-- First parameter derivatives are sufficient for all source histories. -/
theorem nearby_axial_bounds {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {h j σ Λ C B K : ℝ} (hΛ : 0 < Λ)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K Q.f Q.U)
    (hu : ∀ p ∈ ReferenceBounds.holdRegion, |P.U p - Q.U p| ≤ 1 / Λ)
    (huη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ) :
    (∀ p ∈ ReferenceBounds.holdRegion, |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 1) ∧
    (∀ p ∈ ReferenceBounds.holdRegion, |Λ * (parameterPartial P.U p - 4)| ≤ B + 1) := by
  have step_bound {x y z : ℝ} (he : |x - y| ≤ 1 / Λ) (hb : |Λ * (y - z)| ≤ B) :
      |Λ * (x - z)| ≤ B + 1 := by
    have he1 : Λ * |x - y| ≤ 1 := by
      have ht := mul_le_mul_of_nonneg_left he hΛ.le
      rwa [mul_one_div_cancel hΛ.ne'] at ht
    calc
      _ = |Λ * (x - y) + Λ * (y - z)| := by congr 1; ring
      _ ≤ |Λ * (x - y)| + |Λ * (y - z)| := abs_add_le _ _
      _ ≤ 1 + B := by rw [abs_mul, abs_of_pos hΛ]; linarith
      _ = _ := by ring
  exact ⟨fun p hp => step_bound (hu p hp) (hj.axial_value p hp),
    fun p hp => step_bound (huη p hp) (hj.axial_parameter p hp)⟩

theorem nearby_source_jets {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {h j σ Λ C B K : ℝ} (hΛ : 0 < Λ)
    (hj : ReferenceJetBounds.JetBounds h j σ Λ C B K Q.f Q.U)
    (hu : ∀ p ∈ ReferenceBounds.holdRegion, |P.U p - Q.U p| ≤ 1 / Λ)
    (huη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ)
    (hfη : ∀ p ∈ ReferenceBounds.holdRegion,
      |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| ≤ 1)
    {p : Point} (hp : p ∈ ReferenceBounds.holdRegion) (hpD : p ∈ D.carrier) :
    |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (average (parameterPartial P.U) p - 4)| ≤ B + 2 ∧
    |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B + 2 := by
  obtain ⟨hU, hUη⟩ := nearby_axial_bounds P Q hΛ hj hu huη
  have hh := ReferenceBounds.normalized_history_bounds P hU hUη hp hpD
  refine ⟨(hU p hp).trans (by linarith), hh.1.trans (by linarith), hh.2.trans (by linarith), ?_⟩
  calc
    _ ≤ |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| +
        |parameterPartial Q.f p / Q.f p - Λ * realGradient h j σ p.2| := abs_sub_le _ _ _
    _ ≤ 1 + B := add_le_add (hfη p hp) (hj.log_parameter p hp)
    _ ≤ _ := by linarith

/-- A radius interval starting at the natural entrance. -/
noncomputable def continuationRegion (X0 : ℝ) : Set Point := Icc X0 110 ×ˢ Icc (-1 : ℝ) 1

structure StockControl {D : RadialDomain} (P : Profiles D) (h M : ℝ) (S : Set Point) : Prop where
  first_positive : ∀ p ∈ S, 0 < ReferenceBounds.p1 P h p
  first_bound : ∀ p ∈ S, ReferenceBounds.p1 P h p ≤ M
  second_bound : ∀ p ∈ S, |ReferenceBounds.p2 P h p| ≤ M
  ratio_bound : ∀ p ∈ S, |ReferenceBounds.p2 P h p / ReferenceBounds.p1 P h p| ≤ M

structure StockClose {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    (h ε : ℝ) (p : Point) : Prop where
  first : |ReferenceBounds.p1 P h p - ReferenceBounds.p1 Q h p| < ε
  second : |ReferenceBounds.p2 P h p - ReferenceBounds.p2 Q h p| < ε
  ratio : |Q.f p / P.f p - 1| < ε

/-- All constants in this record are selected before the REF cutoff. -/
structure ComparisonScales where
  bound : ℝ
  error : ℝ
  damping : ℝ
  fieldTolerance : ℝ
  referenceRadius : ℝ
  bound_pos : 0 < bound
  error_pos : 0 < error
  error_le_one : error ≤ 1
  damping_pos : 0 < damping
  damping_lt_one : damping < 1
  fieldTolerance_pos : 0 < fieldTolerance
  referenceRadius_pos : 0 < referenceRadius
  projection_error : error * projectionConstant bound ≤ 1 / 8
  speed_bound : damping * speedConstant bound ≤ 1
  angular_bound : damping * bound ≤ 4 / 5

/-- Compactness is applied to one bounded family of actual field/history
jets.  It does not select a cutoff first and then ask that cutoff to be
smaller than its own continuity threshold. -/
theorem prepare_stock_comparison {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hΛ1 : 1 ≤ Λ) (hC : 1 ≤ C)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ c : ComparisonScales, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < c.referenceRadius →
      ∀ hδT : 2 * δ < ReferencePath.rampLimit,
      ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 →
      ReferenceJetBounds.JetBounds h j σ Λ C B K
        ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
        ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ) →
      let Q := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
      StockControl Q h c.bound (continuationRegion (4 / Λ)) ∧
        ∀ {D : RadialDomain} (P : Profiles D), P.pressure0 = Q.pressure0 →
          ∀ p ∈ continuationRegion (4 / Λ), p ∈ D.carrier →
            (∀ t ∈ Icc (0 : ℝ) p.1,
              ‖fieldJet P (t, p.2) - fieldJet Q (t, p.2)‖ < c.fieldTolerance) →
              StockClose P Q h c.error p := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let S := continuationRegion (4 / Λ)
  have hX0 : 0 < 4 / Λ := div_pos (by norm_num) hΛ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hSX : ∀ p ∈ S, 0 < p.1 := fun p hp => hX0.trans_le hp.1.1
  have hSη : ∀ p ∈ S, p.2 ∈ Icc (-1 : ℝ) 1 := fun _ hp => hp.2
  obtain ⟨μ, r, hμ, hr, hfloor⟩ := reference_positive_uniform N
  obtain ⟨B0, hB0, hp0⟩ := pressure_initial_bound hP0
  let BF := K + B + 6
  have hBF : 0 ≤ BF := by dsimp [BF]; positivity
  obtain ⟨BS, hBS, hstate⟩ := stockJet_uniform_bound hBF hB0.le
  obtain ⟨M0, hM0, hstock⟩ := uniform_stock_bound (B := BS) hsmall hμ hS hSX hSη
  let α : ℝ := (6 / 5 : ℝ) * (4 / Λ)
  have hα : 0 < α := mul_pos (by norm_num) hX0
  let M := 1 + M0 + M0 / α
  have hM : 0 < M := by dsimp [M]; positivity
  have hM0M : M0 ≤ M := by dsimp [M]; linarith [div_nonneg hM0.le hα.le]
  have hratioM : M0 / α ≤ M := by dsimp [M]; linarith
  obtain ⟨ε, κs, hε, hε1, hκs, hκs1, he, hv, ha⟩ := comparison_tolerances hM.le
  obtain ⟨τ, hτ, htransfer⟩ := uniform_stock_transfer (B := BS) hsmall hμ hε hS hSX hSη
  obtain ⟨ρ, hρ, hfield⟩ := field_to_stockJet_transfer BF hτ
  let c : ComparisonScales := ⟨M, ε, κs, ρ, r, hM, hε, hε1, hκs, hκs1, hρ, hr, he, hv, ha⟩
  refine ⟨c, ?_⟩
  intro δ hδ hdr hδT href hj
  let Q := ReferenceBounds.referenceProfiles E.profile hΛ hδ hδT hP0
  have hqfield : ∀ p ∈ ReferenceBounds.holdRegion, ‖fieldJet Q p‖ ≤ BF := by
    intro p hp
    exact reference_fieldJet_bound Q hsmall hΛ1 hC hB hK hj hp
  have hqstate (p : Point) (hp : p ∈ S) : ‖stockJet Q p‖ ≤ BS := by
    apply hstate Q p (ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2)
      ⟨(hSX p hp).le, hp.1.2⟩ (hp0 p.2 hp.2).1 (hp0 p.2 hp.2).2
    intro t ht
    exact hqfield (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩
  have hqfloor (p : Point) (hp : p ∈ S) : 2 * μ ≤ Q.f p := hfloor δ hδ hdr p hp.1.1 hp.2
  have hqpositive (p : Point) (hp : p ∈ S) : 0 < Q.f p := by linarith [hqfloor p hp]
  have hqcoords (p : Point) (hp : p ∈ S) := stockJet_coordinates Q h
    (ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2) (hSX p hp) (hqpositive p hp).ne'
  have hlow (p : Point) (hp : p ∈ S) : α ≤ ReferenceBounds.p1 Q h p := by
    exact (mul_le_mul_of_nonneg_left hp.1.1 (by norm_num : (0 : ℝ) ≤ 6 / 5)).trans
      (reference_first_lower E hΛ hδ hδT hP0 hsmall hσ href
        ⟨⟨(hSX p hp).le, hp.1.2⟩, hp.2⟩ (hSX p hp))
  have hbnd (p : Point) (hp : p ∈ S) :
      |ReferenceBounds.p1 Q h p| ≤ M0 ∧ |ReferenceBounds.p2 Q h p| ≤ M0 := by
    have hh := hstock p hp (stockJet Q p) (hqstate p hp) (by change μ ≤ Q.f p; linarith [hqfloor p hp])
    rwa [(hqcoords p hp).1, (hqcoords p hp).2] at hh
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    exact hα.trans_le (hlow p hp)
  · intro p hp
    exact (le_abs_self _).trans ((hbnd p hp).1.trans hM0M)
  · intro p hp
    exact (hbnd p hp).2.trans hM0M
  · intro p hp
    have hpos := hα.trans_le (hlow p hp)
    calc
      _ = |ReferenceBounds.p2 Q h p| / ReferenceBounds.p1 Q h p := by rw [abs_div, abs_of_pos hpos]
      _ ≤ M0 / α := by gcongr; exact (hbnd p hp).2; exact hlow p hp
      _ ≤ M := hratioM
  · intro D P hp0eq p hp hpD hclose
    have hpQ := ReferenceBounds.reference_mem E.profile hΛ (hSX p hp).le hp.2
    have hhstate := hfield P Q hp0eq p hpD hpQ ⟨(hSX p hp).le, hp.1.2⟩
      (fun t ht => hqfield (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩) hclose
    have hh := htransfer p hp (stockJet Q p) (stockJet P p) (hqstate p hp) (hqfloor p hp) hhstate
    have hPf0 : μ < P.f p := hh.1
    have hPf : 0 < P.f p := hμ.trans hPf0
    have hpc := stockJet_coordinates P h hpD (hSX p hp) hPf.ne'
    refine ⟨?_, ?_, hh.2.2.2⟩
    · simpa only [hpc.1, (hqcoords p hp).1] using hh.2.1
    · simpa only [hpc.2, (hqcoords p hp).2] using hh.2.2.1

/-! ## The two terminal ramps preserve the actual relaxed inequality -/

theorem two_ramp_relaxed (c : ComparisonScales) {κ A B p q R b w₁ w₂ y : ℝ}
    (hκ : 0 < κ) (hκc : κ ≤ c.damping) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hA : 0 < A) (hAM : A ≤ c.bound) (hB : |B| ≤ c.bound)
    (hBA : |B / A| ≤ c.bound)
    (hp : |p - A| < c.error) (hq : |q - B| < c.error) (hR : |R - 1| < c.error)
    (hc : (9 / 4 : ℝ) ≤ A + B ^ 2 / A) (hbig : b ≤ y → 3 ≤ A) :
    Relaxed
      ((1 - TransitionRamp.step (b + w₁) w₂ y) * κ * A +
        (4 / 5 : ℝ) * TransitionRamp.step (b + w₁) w₂ y)
      (κ * (1 - TransitionRamp.step b w₁ y) * B * R) p q := by
  let θ := 1 - TransitionRamp.step b w₁ y
  have hθ : θ ∈ Icc (0 : ℝ) 1 := by
    have hh := TransitionRamp.step_mem b w₁ y
    constructor <;> dsimp [θ] <;> linarith [hh.1, hh.2]
  have hv : κ * speedConstant c.bound ≤ 1 :=
    (mul_le_mul_of_nonneg_right hκc (speedConstant_nonneg c.bound_pos.le)).trans c.speed_bound
  by_cases hy : y ≤ b + w₁
  · rw [TransitionRamp.step_zero hw₂ hy]
    simp only [sub_zero, one_mul, mul_zero, add_zero]
    apply damped_relaxed hκ hA c.bound_pos.le hAM c.error_pos.le c.error_le_one hθ
      hB hBA hp.le hq.le hR.le ?_ c.projection_error hv
    by_cases hyb : y ≤ b
    · have hz : θ = 1 := by dsimp [θ]; rw [TransitionRamp.step_zero hw₁ hyb]; norm_num
      change (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A
      simpa only [hz, one_mul] using hc
    · have hAg := hbig (le_of_not_ge hyb)
      have hn : 0 ≤ θ * B ^ 2 / A := div_nonneg (mul_nonneg hθ.1 (sq_nonneg B)) hA.le
      change (9 / 4 : ℝ) ≤ A + θ * B ^ 2 / A
      linarith
  · have hyb : b ≤ y := by linarith [lt_of_not_ge hy]
    have hz := TransitionRamp.step_one hw₁ (le_of_not_ge hy)
    rw [hz]
    simp only [sub_self, mul_zero, zero_mul]
    have ha4 : κ * A ≤ 4 / 5 :=
      (mul_le_mul hκc hAM hA.le c.damping_pos.le).trans c.angular_bound
    have ha := convex_final_shear (mul_pos hκ hA) ha4 (TransitionRamp.step_mem (b + w₁) w₂ y)
    have hae : (1 - TransitionRamp.step (b + w₁) w₂ y) * κ * A +
        (4 / 5 : ℝ) * TransitionRamp.step (b + w₁) w₂ y =
      (1 - TransitionRamp.step (b + w₁) w₂ y) * (κ * A) +
        TransitionRamp.step (b + w₁) w₂ y * (4 / 5) := by ring
    rw [hae]
    apply zero_axial_relaxed ha.1 (ha.2.trans (by norm_num))
    have hh := (abs_lt.mp hp).1
    have hAg := hbig hyb
    linarith [c.error_le_one]

/-! ## Binding the constructed physical ramp to the cone coordinates -/

section PhysicalRamp

open ReferencePath TransitionRamp

variable {h j σ Λ C δ T κ w₁ w₂ : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalProfile.ProfileFamily d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)
    (hT : 0 < T) (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)

theorem physical_shear_equations {p : Point} (hp : p.2 ∈ parameterInterval) (hX : 0 < p.1)
    (ht : T ≤ (ofNatural F hΛ hsmall hδ hδT hP0).logTime p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    shearA P p = (1 - step (R.bigTime + w₁) w₂ (R.logTime p.1)) * κ *
        ReferenceBounds.p1 R.profiles h p + (4 / 5 : ℝ) * step (R.bigTime + w₁) w₂ (R.logTime p.1) ∧
    shearB P p = κ * (1 - step R.bigTime w₁ (R.logTime p.1)) *
      ReferenceBounds.p2 R.profiles h p * (R.profiles.f p / P.f p) := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hd := physical_radial_equations F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂ hp hX
  change (p.1 * radialPartial P.f p / P.f p =
      angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p)) ∧
    (p.1 * radialPartial P.U p = axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p)) at hd
  have hc : R.chart (R.logPoint p) = p := by
    exact R.chart_logTime hX
  have ha : R.angularStock (R.logPoint p) = ReferenceBounds.p1 R.profiles h p := by
    change ActivationStocks.profileStockOne R.profiles h (R.chart (R.logPoint p)) = _
    rw [hc]
    rfl
  have hu : R.axialStock (R.logPoint p) = p.1 * ReferenceBounds.ns R.profiles h p := by
    change (R.chart (R.logPoint p)).1 * R.profiles.axialLag h (R.chart (R.logPoint p)) /
      NaturalAxisData.L h p.2 = _
    rw [hc]
    unfold ReferenceBounds.ns
    ring
  have hpf : 0 < P.f p := physicalF_positive F hΛ hsmall hδ hδT hP0 T κ w₁ w₂
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX.le), hp⟩ hX.le
  have hrf : 0 < R.profiles.f p := by
    have hh := R.f_pos (R.logTime p.1) p.2 hp
    change 0 < R.profiles.f (R.chart (R.logPoint p)) at hh
    rwa [hc] at hh
  have hs : Real.sqrt (2 * p.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2 * p.1)).ne'
  constructor
  · change shearA P p = _
    calc
      _ = -2 * (p.1 * radialPartial P.f p / P.f p) := by unfold shearA; ring
      _ = -2 * angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p) := by rw [hd.1]
      _ = _ := by
        unfold angularSlope baseSlope
        rw [show damping T κ (R.logPoint p).1 = κ from damping_eq_constant hT κ ht, ha]
        dsimp only [StockReference.logPoint]
        ring
  · change shearB P p = _
    calc
      _ = -2 * (p.1 * radialPartial P.U p) / P.E p := by unfold shearB; ring
      _ = -2 * axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p) / P.E p := by rw [hd.2]
      _ = κ * (1 - step R.bigTime w₁ (R.logTime p.1)) * (p.1 * ReferenceBounds.ns R.profiles h p) /
          P.E p := by
        unfold axialSlope baseSlope
        rw [show damping T κ (R.logPoint p).1 = κ from damping_eq_constant hT κ ht, hu]
        dsimp only [StockReference.logPoint]
        ring
      _ = _ := by
        unfold ReferenceBounds.p2 Profiles.E
        dsimp only [R, P] at hpf hrf ⊢
        field_simp [hs, hpf.ne', hrf.ne']

/-- The whole incoming field jet is exactly preserved, including the
join at the natural endpoint. -/
theorem physical_fieldJet_before {p : Point}
    (hp : p ∈ (Input.ofNatural hΛ F).radialDomain.carrier)
    (hx : p.1 ≤ (Input.ofNatural hΛ F).endpoint) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    fieldJet P p = fieldJet R.profiles p := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hf : (fun η => P.f (p.1, η)) = (fun η => R.profiles.f (p.1, η)) := by
    funext η
    exact R.physicalF_before T κ w₁ w₂ hx
  have hu : (fun η => P.U (p.1, η)) = (fun η => R.profiles.U (p.1, η)) := by
    funext η
    exact R.physicalU_before T κ w₁ hx
  have hfη : parameterPartial P.f p = parameterPartial R.profiles.f p := by
    have hd := parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain P.f_smooth hp
    rw [hf] at hd
    exact hd.unique (parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain R.profiles.f_smooth hp)
  have huη : parameterPartial P.U p = parameterPartial R.profiles.U p := by
    have hd := parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain P.U_smooth hp
    rw [hu] at hd
    exact hd.unique (parameterPartial_hasDerivAt (Input.ofNatural hΛ F).radialDomain R.profiles.U_smooth hp)
  change fieldJet P p = fieldJet R.profiles p
  unfold fieldJet
  rw [show P.f p = R.profiles.f p from congrFun hf p.2,
    show P.U p = R.profiles.U p from congrFun hu p.2, hfη, huη]

/-- Rewrite the endpoint in the physical error estimates as the original
natural endpoint, whose bounds were fixed before the reference cutoff. -/
theorem physical_endpoint_control {ε : ℝ}
    (hc : (ofNatural F hΛ hsmall hδ hδT hP0).SmallPhysicalControl
      (Icc (-1 : ℝ) 1) 1 ε T κ w₁ w₂)
    {p : Point} (hp : p ∈ continuationRegion (4 / Λ)) :
    let N := Input.ofNatural hΛ F
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    |P.U p - N.U (N.endpoint, p.2)| < ε ∧
    |parameterPartial P.U p - parameterPartial N.U (N.endpoint, p.2)| < ε ∧
    |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
      N.f (N.endpoint, p.2)| < ε := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hm := ReferenceJetBounds.reference_mem N ((N.endpoint_pos).le.trans hp.1.1) hp.2
  have hme := ReferenceJetBounds.endpoint_mem N hp.2
  have hUi : R.initialU = fun η => N.U (N.endpoint, η) := by
    funext η
    exact N.refU_eq_natural_initial δ le_rfl
  have hLi : R.initialLog = fun η => Real.log (N.f (N.endpoint, η)) := by
    funext η
    exact congrArg Real.log (N.refF_eq_natural_initial δ le_rfl)
  have hu0 := hc.axial_jets p.1 hp.1 p.2 hp.2 0 (by norm_num)
  have hu1 := hc.axial_jets p.1 hp.1 p.2 hp.2 1 le_rfl
  have hl1 := hc.positive_log_jets p.1 hp.1 p.2 hp.2 1 le_rfl (by norm_num)
  change |iteratedDeriv 0 (fun η => P.U (p.1, η) - R.initialU η) p.2| < ε at hu0
  change |iteratedDeriv 1 (fun η => P.U (p.1, η) - R.initialU η) p.2| < ε at hu1
  change |iteratedDeriv 1 (fun η => Real.log (P.f (p.1, η)) - R.initialLog η) p.2| < ε at hl1
  rw [hUi, iteratedDeriv_zero] at hu0
  rw [hUi, ReferenceJetBounds.first_parameter_difference
    (P.U_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds hm))
    (N.U_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hme))] at hu1
  have hPf : 0 < P.f p := physicalF_positive F hΛ hsmall hδ hδT hP0 T κ w₁ w₂ hm
    (N.endpoint_pos.le.trans hp.1.1)
  rw [hLi, ReferenceJetBounds.first_log_difference
    (P.f_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds hm))
    (N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds hme))
    hPf.ne' (N.endpoint_f_pos (original_interval_interior hp.2)).ne'] at hl1
  exact ⟨hu0, hu1, hl1⟩

theorem physical_endpoint_log_value {ε : ℝ}
    (hc : (ofNatural F hΛ hsmall hδ hδT hP0).SmallPhysicalControl
      (Icc (-1 : ℝ) 1) 1 ε T κ w₁ w₂)
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hx : p.1 ∈ Icc (4 / Λ)
      (radius (4 / Λ) ((ofNatural F hΛ hsmall hδ hδT hP0).bigTime + w₁ + w₂))) :
    let N := Input.ofNatural hΛ F
    let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
    |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < ε := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let P := physicalProfiles F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂
  have hh := hc.log_value p.1 hx p.2 hη
  change |Real.log (P.f p) - R.initialLog p.2| < ε at hh
  have he : R.initialLog p.2 = Real.log (N.f (N.endpoint, p.2)) :=
    congrArg Real.log (N.refF_eq_natural_initial δ le_rfl)
  rwa [he] at hh

end PhysicalRamp

/-! ## Uniform logarithmic-to-physical jet conversion -/

theorem angular_endpoint_transfer (N : ReferencePath.Input) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      p.2 ∈ Icc (-1 : ℝ) 1 → 0 < P.f p →
      |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < τ →
      |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
        N.f (N.endpoint, p.2)| < τ →
      |P.f p - N.f (N.endpoint, p.2)| < ε ∧
      |parameterPartial P.f p - parameterPartial N.f (N.endpoint, p.2)| < ε := by
  obtain ⟨B, hB, hb⟩ := endpointLogJet_bound N
  obtain ⟨τ, hτ, ht⟩ := expJet_uniform B hε
  refine ⟨τ, hτ, ?_⟩
  intro D P p hp hPf hv hd
  let z := endpointLogJet N p.2
  let w : ℝ × ℝ := (Real.log (P.f p), parameterPartial P.f p / P.f p)
  have he : ‖w - z‖ < τ := by
    rw [Prod.norm_def, max_lt_iff]
    exact ⟨hv, hd⟩
  have hh := ht z w (hb p.2 hp) he
  have hNf := N.endpoint_f_pos (original_interval_interior hp)
  have hw : expJet w = (P.f p, parameterPartial P.f p) := by
    dsimp [expJet, w]
    rw [Real.exp_log hPf, mul_div_cancel₀ _ hPf.ne']
  have hz : expJet z = (N.f (N.endpoint, p.2), parameterPartial N.f (N.endpoint, p.2)) := by
    dsimp [expJet, z, endpointLogJet]
    rw [Real.exp_log hNf, mul_div_cancel₀ _ hNf.ne']
  rw [hw, hz, Prod.norm_def, max_lt_iff] at hh
  exact hh

theorem fieldJet_close {D E : RadialDomain} (P : Profiles D) (Q : Profiles E)
    {p : Point} {ε : ℝ} (hε : 0 < ε)
    (hf : |P.f p - Q.f p| < ε) (hu : |P.U p - Q.U p| < ε)
    (hfη : |parameterPartial P.f p - parameterPartial Q.f p| < ε)
    (huη : |parameterPartial P.U p - parameterPartial Q.U p| < ε) :
    ‖fieldJet P p - fieldJet Q p‖ < ε := by
  apply (pi_norm_lt_iff hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hf
  · exact hu
  · exact hfη
  · exact huη

theorem abs_sub_of_common_center {x y z a b : ℝ}
    (hx : |x - z| < a) (hy : |y - z| < b) : |x - y| < a + b := by
  calc
    _ ≤ |x - z| + |y - z| := abs_sub_le _ _ _ |>.trans_eq (by rw [abs_sub_comm z y])
    _ < a + b := add_lt_add hx hy

theorem physical_control_mono {J K : Set ℝ} (R : TransitionRamp.StockReference J)
    {N n : ℕ} {ε ε' T κ w₁ w₂ : ℝ} (hn : n ≤ N) (he : ε ≤ ε')
    (hc : R.SmallPhysicalControl K N ε T κ w₁ w₂) :
    R.SmallPhysicalControl K n ε' T κ w₁ w₂ := by
  refine ⟨hc.finish_before, ?_, ?_, ?_⟩
  · intro X hX η hη k hk
    exact (hc.axial_jets X hX η hη k (hk.trans hn)).trans_le he
  · intro X hX η hη k hk hk0
    exact (hc.positive_log_jets X hX η hη k (hk.trans hn) hk0).trans_le he
  · intro X hX η hη
    exact (hc.log_value X hX η hη).trans_le he

/-! ## Parameters and actual profiles of one common continuation -/

structure RampParameters {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalProfile.ProfileFamily d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) where
  refTime : ℝ
  actTime : ℝ
  kappa : ℝ
  widthU : ℝ
  widthA : ℝ
  refTime_pos : 0 < refTime
  refTime_bound : 2 * refTime < ReferencePath.rampLimit
  actTime_pos : 0 < actTime
  actTime_le : actTime ≤ refTime
  kappa_pos : 0 < kappa
  kappa_lt_one : kappa < 1
  widthU_pos : 0 < widthU
  widthA_pos : 0 < widthA
  before_big : refTime ≤
    (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).bigTime
  finish_before :
    (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).bigTime + widthU + widthA <
      (TransitionRamp.ofNatural F hΛ hsmall refTime_pos refTime_bound hP0).finalTime

namespace RampParameters

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0)

noncomputable def reference : TransitionRamp.StockReference ReferencePath.parameterInterval :=
  TransitionRamp.ofNatural F hΛ hsmall r.refTime_pos r.refTime_bound hP0

noncomputable def profiles : Profiles (ReferencePath.Input.ofNatural hΛ F).radialDomain :=
  TransitionRamp.physicalProfiles F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    (κ := r.kappa) r.actTime_pos r.before_big r.widthU_pos r.widthA_pos

noncomputable def startRadius : ℝ := radius r.reference.radius0 r.actTime
noncomputable def holdTime : ℝ := r.reference.bigTime + r.widthU + r.widthA
noncomputable def holdRadius : ℝ := radius r.reference.radius0 r.holdTime

theorem radius0_eq : r.reference.radius0 = 4 / Λ := rfl

theorem profiles_positive {p : Point} (hp : p.2 ∈ ReferencePath.parameterInterval) (hX : 0 ≤ p.1) :
    0 < r.profiles.f p :=
  TransitionRamp.physicalF_positive F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime r.kappa r.widthU r.widthA
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX), hp⟩ hX

theorem profiles_mem {p : Point} (hp : p.2 ∈ Icc (-1 : ℝ) 1) (hX : 0 ≤ p.1) :
    p ∈ r.reference.domain.carrier :=
  ReferenceJetBounds.reference_mem _ hX hp

theorem bigTime_pos : 0 < r.reference.bigTime := r.refTime_pos.trans_le r.before_big

theorem holdTime_pos : 0 < r.holdTime := by
  dsimp [holdTime]
  linarith [r.bigTime_pos, r.widthU_pos, r.widthA_pos]

theorem startRadius_pos : 0 < r.startRadius :=
  mul_pos r.reference.radius0_pos (Real.exp_pos _)

theorem holdRadius_pos : 0 < r.holdRadius :=
  mul_pos r.reference.radius0_pos (Real.exp_pos _)

theorem radius0_lt_start : r.reference.radius0 < r.startRadius := by
  change r.reference.radius0 < r.reference.radius0 * Real.exp r.actTime
  have he : 1 < Real.exp r.actTime := (Real.one_lt_exp_iff).mpr r.actTime_pos
  nlinarith [r.reference.radius0_pos]

theorem hundred_lt_hold : (100 : ℝ) < r.holdRadius := by
  have he : r.reference.bigTime < r.holdTime := by dsimp [holdTime]; linarith [r.widthU_pos, r.widthA_pos]
  have hm := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr he) r.reference.radius0_pos
  have hx : r.reference.radius0 * Real.exp r.reference.bigTime = 100 := by
    rw [TransitionRamp.StockReference.bigTime, Real.exp_log (div_pos (by norm_num) r.reference.radius0_pos)]
    field_simp [r.reference.radius0_pos.ne']
  rwa [hx] at hm

theorem hold_lt_final : r.holdRadius < (110 : ℝ) := by
  have hfit : r.holdTime < r.reference.finalTime := r.finish_before
  have hm := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hfit) r.reference.radius0_pos
  have hx : r.reference.radius0 * Real.exp r.reference.finalTime = 110 := by
    rw [TransitionRamp.StockReference.finalTime, Real.exp_log (div_pos (by norm_num) r.reference.radius0_pos)]
    field_simp [r.reference.radius0_pos.ne']
  rwa [hx] at hm

theorem start_le_hold : r.startRadius ≤ r.holdRadius := by
  apply mul_le_mul_of_nonneg_left _ r.reference.radius0_pos.le
  apply Real.exp_le_exp.mpr
  have hb : r.refTime ≤ r.reference.bigTime := r.before_big
  dsimp [holdTime]
  linarith [r.actTime_le, r.widthU_pos, r.widthA_pos]

theorem logTime_start {X : ℝ} (hx : r.startRadius ≤ X) : r.actTime ≤ r.reference.logTime X := by
  exact ((ReferencePath.Input.ofNatural hΛ F).le_logTime_iff (r.startRadius_pos.trans_le hx)).mpr hx

theorem logTime_hold {X : ℝ} (hx : r.holdRadius ≤ X) : r.holdTime ≤ r.reference.logTime X := by
  exact ((ReferencePath.Input.ofNatural hΛ F).le_logTime_iff (r.holdRadius_pos.trans_le hx)).mpr hx

theorem physical_shears {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.startRadius ≤ p.1) :
    shearA r.profiles p =
      (1 - TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA (r.reference.logTime p.1)) *
        r.kappa * ReferenceBounds.p1 r.reference.profiles h p +
      (4 / 5 : ℝ) * TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA (r.reference.logTime p.1) ∧
    shearB r.profiles p = r.kappa * (1 - TransitionRamp.step r.reference.bigTime r.widthU
      (r.reference.logTime p.1)) * ReferenceBounds.p2 r.reference.profiles h p *
        (r.reference.profiles.f p / r.profiles.f p) :=
  physical_shear_equations F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime_pos r.before_big r.widthU_pos r.widthA_pos
      (original_interval_interior hη) (r.startRadius_pos.trans_le hx) (r.logTime_start hx)

theorem final_shears {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.holdRadius ≤ p.1) :
    shearA r.profiles p = 4 / 5 ∧ shearB r.profiles p = 0 := by
  have hy := r.logTime_hold hx
  have hh := r.physical_shears hη (r.start_le_hold.trans hx)
  have hA : TransitionRamp.step (r.reference.bigTime + r.widthU) r.widthA (r.reference.logTime p.1) = 1 :=
    TransitionRamp.step_one r.widthA_pos hy
  have hU : TransitionRamp.step r.reference.bigTime r.widthU (r.reference.logTime p.1) = 1 :=
    TransitionRamp.step_one r.widthU_pos (by dsimp [holdTime] at hy; linarith [r.widthA_pos])
  simpa only [hA, hU, sub_self, zero_mul, mul_zero, mul_one, zero_add] using hh

theorem final_logSlope {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hx : r.holdRadius ≤ p.1) :
    ReferenceBounds.logSlope r.profiles p = 3 / 5 := by
  rw [logSlope_eq_shear, (r.final_shears hη hx).1]
  norm_num

end RampParameters

/-- The initial collar estimate is retained for the very same chosen
activation width and damping, not for a separately chosen profile. -/
noncomputable def InitialActivationBound {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0) : Prop :=
  let N := ReferencePath.Input.ofNatural hΛ F
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
  ∃ θ > 0, θ ≤ 1 ∧ ∀ y ∈ Ioc (0 : ℝ) r.actTime, ∀ η ∈ Icc (-1 : ℝ) 1,
    activation r.actTime r.kappa y ≤
      ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) -
        StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) ∧
    2 + 1 / 32 < ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) ∧
    (StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) - 2) *
        ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, η) ^ 2 <
      2 * (ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η) -
        StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η)) ^ 2 ∧
    StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η) <
      ConeAlgebra.coneBound
        (ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, η))
        (ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, η)) ∧
    (y ≤ θ * r.actTime → 2 + 1 / 16 <
      StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, η))

/-- Quantitative facts established for one actual constructed ramp.  The
existence theorem below supplies every field, including the stock errors. -/
structure ComparableRamp {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters E.profile.family hΛ hsmall hP0)
    (c : ComparisonScales) : Prop where
  reference_bounds : ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ r.refTime_pos r.refTime_bound hP0
  reference_jets : ReferenceJetBounds.JetBounds h j σ Λ C B K r.reference.profiles.f r.reference.profiles.U
  damping_le : r.kappa ≤ c.damping
  stock_bounds : StockControl r.reference.profiles h c.bound (continuationRegion (4 / Λ))
  stock_close : ∀ p ∈ continuationRegion (4 / Λ), p.1 ≤ r.holdRadius →
    StockClose r.profiles r.reference.profiles h c.error p
  source_jets : ∀ p ∈ ReferenceBounds.holdRegion,
    |Λ * (r.profiles.U p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (r.profiles.Ubar p - NaturalAxisData.U j p.2)| ≤ B + 2 ∧
    |Λ * (average (parameterPartial r.profiles.U) p - 4)| ≤ B + 2 ∧
    |parameterPartial r.profiles.f p / r.profiles.f p - Λ * realGradient h j σ p.2| ≤ B + 2

theorem log_control_mono {J K : Set ℝ} (R : TransitionRamp.StockReference J)
    {N n : ℕ} {ε ε' T κ w₁ w₂ : ℝ} (hn : n ≤ N) (he : ε ≤ ε')
    (hc : R.SmallLogControl K N ε T κ w₁ w₂) :
    R.SmallLogControl K n ε' T κ w₁ w₂ := by
  refine ⟨hc.finish_before, ?_, ?_, ?_⟩
  · intro y hy η hη k hk
    exact (hc.axial_jets y hy η hη k (hk.trans hn)).trans_le he
  · intro y hy η hη k hk hk0
    exact (hc.positive_log_jets y hy η hη k (hk.trans hn) hk0).trans_le he
  · intro y hy η hη
    exact (hc.log_value y hy η hη).trans_le he

/-- Construct one shared cutoff, activation and two-ramp schedule.  The
extra finite-jet tolerance is intersected with the cone tolerances, so later
matching does not need to replace this witness. -/
theorem exists_comparable_ramp {h j σ Λ C B K r0 : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hΛ1 : 1 ≤ Λ) (hC : 1 ≤ C) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0)
    (hr0 : 0 < r0)
    (href : ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r0 →
      ∃ hδT : 2 * δ < ReferencePath.rampLimit,
        ReferenceBounds.ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 ∧
        ReferenceJetBounds.JetBounds h j σ Λ C B K
          ((ReferencePath.Input.ofNatural hΛ E.profile.family).refF δ)
          ((ReferencePath.Input.ofNatural hΛ E.profile.family).refU δ))
    (Nextra : ℕ) {εextra : ℝ} (hεextra : 0 < εextra) :
    ∃ r : RampParameters E.profile.family hΛ hsmall hP0, ∃ c : ComparisonScales,
      ComparableRamp (B := B) (K := K) E r c ∧ InitialActivationBound r ∧
      r.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) Nextra εextra
        r.actTime r.kappa r.widthU r.widthA ∧
      r.reference.SmallLogControl (Icc (-1 : ℝ) 1) Nextra εextra
        r.actTime r.kappa r.widthU r.widthA := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  obtain ⟨c, hcompare⟩ := prepare_stock_comparison E hΛ hΛ1 hC hB hK hsmall hσ hP0
  let εF := c.fieldTolerance / 4
  have hεF : 0 < εF := div_pos c.fieldTolerance_pos (by norm_num)
  let εU := min εF (1 / (4 * Λ))
  have hεU : 0 < εU := lt_min hεF (one_div_pos.mpr (mul_pos (by norm_num) hΛ))
  obtain ⟨τ, hτ, hang⟩ := angular_endpoint_transfer N hεF
  let εA := min εU (min τ (1 / 4 : ℝ))
  have hεA : 0 < εA := lt_min hεU (lt_min hτ (by norm_num))
  have hAU : εA ≤ εU := min_le_left _ _
  have hAτ : εA ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hA4 : εA ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨rE, hrE, hend⟩ := reference_endpoint_control N hεU hεF (by norm_num : (0 : ℝ) < 1 / 4)
  let rmin := min r0 (min c.referenceRadius rE)
  have hrmin : 0 < rmin := lt_min hr0 (lt_min c.referenceRadius_pos hrE)
  let δ := rmin / 2
  have hδ : 0 < δ := div_pos hrmin (by norm_num)
  have hδmin : δ < rmin := by dsimp [δ]; linarith
  have hdr0 : δ < r0 := hδmin.trans_le (min_le_left _ _)
  have hdrc : δ < c.referenceRadius := hδmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdrE : δ < rE := hδmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hδT, hRef, hJet⟩ := href δ hδ hdr0
  obtain ⟨hEnd, hEndLog⟩ := hend δ hδ hdrE
  obtain ⟨hStocks, hTransfer⟩ := hcompare δ hδ hdrc hδT hRef hJet
  let R := TransitionRamp.ofNatural E.profile.family hΛ hsmall hδ hδT hP0
  have hb : δ ≤ R.bigTime := by
    have hf := N.freeze_before_Xbig hΛ1 hδT
    have hm : N.endpoint * Real.exp δ ≤ 100 := by
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : δ ≤ 2 * δ))
        N.endpoint_pos.le).trans hf.le
    exact (N.le_logTime_iff (by norm_num : (0 : ℝ) < 100)).mpr hm
  obtain ⟨Tstar, θ, hTstar, hTstarδ, hθ, hθ1, hInitial⟩ :=
    ActivationCone.natural_initial_activation hΛ E hP0 hsmall hδ hδT
  let εall := min εA εextra
  have hεall : 0 < εall := lt_min hεA hεextra
  obtain ⟨T0, hT0, κ0, hκ0, w0, hw0, hT0δ, hκ01, hwgap, hControls⟩ :=
    TransitionRamp.exists_joint_small_control E.profile.family hΛ hsmall hδ hδT hP0
      isCompact_Icc original_interval_interior (max Nextra 1) hεall hb
  let T := min T0 Tstar / 2
  have hT : 0 < T := div_pos (lt_min hT0 hTstar) (by norm_num)
  have hTmin : T < min T0 Tstar := by dsimp [T]; linarith [lt_min hT0 hTstar]
  have hTT0 : T < T0 := hTmin.trans_le (min_le_left _ _)
  have hTTstar : T ≤ Tstar := (hTmin.trans_le (min_le_right _ _)).le
  let κ := min κ0 c.damping / 2
  have hκ : 0 < κ := div_pos (lt_min hκ0 c.damping_pos) (by norm_num)
  have hκmin : κ < min κ0 c.damping := by dsimp [κ]; linarith [lt_min hκ0 c.damping_pos]
  have hκκ0 : κ < κ0 := hκmin.trans_le (min_le_left _ _)
  have hκc : κ ≤ c.damping := (hκmin.trans_le (min_le_right _ _)).le
  have hκ1 : κ < 1 := hκκ0.trans hκ01
  let w := w0 / 2
  have hw : 0 < w := div_pos hw0 (by norm_num)
  have hww0 : w < w0 := by dsimp [w]; linarith
  have hJoint := hControls T ⟨hT, hTT0⟩ κ ⟨hκ.le, hκκ0⟩ w ⟨hw, hww0⟩ w ⟨hw, hww0⟩
  have hAll : R.SmallPhysicalControl (Icc (-1 : ℝ) 1) (max Nextra 1) εall T κ w w := hJoint.2
  have hOne : R.SmallPhysicalControl (Icc (-1 : ℝ) 1) 1 εA T κ w w :=
    physical_control_mono R (le_max_right _ _) (min_le_left _ _) hAll
  let r : RampParameters E.profile.family hΛ hsmall hP0 := {
    refTime := δ, actTime := T, kappa := κ, widthU := w, widthA := w
    refTime_pos := hδ, refTime_bound := hδT, actTime_pos := hT
    actTime_le := hTT0.le.trans hT0δ, kappa_pos := hκ, kappa_lt_one := hκ1
    widthU_pos := hw, widthA_pos := hw, before_big := hb, finish_before := hAll.finish_before }
  let P := r.profiles
  let Q := r.reference.profiles
  have hInit : InitialActivationBound r := by
    refine ⟨θ, hθ, hθ1, ?_⟩
    intro y hy η hη
    exact hInitial T ⟨hT, hTTstar⟩ κ ⟨hκ, hκ1⟩ y hy η hη
  have hExtra : r.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) Nextra εextra
      r.actTime r.kappa r.widthU r.widthA :=
    physical_control_mono R (le_max_left _ _) (min_le_right _ _) hAll
  have hLogExtra : r.reference.SmallLogControl (Icc (-1 : ℝ) 1) Nextra εextra
      r.actTime r.kappa r.widthU r.widthA :=
    log_control_mono R (le_max_left _ _) (min_le_right _ _) hJoint.1
  have hUscale : εU + εU ≤ 1 / Λ := by
    have hu : εU ≤ 1 / (4 * Λ) := min_le_right _ _
    have hid : 1 / (4 * Λ) = (1 / Λ) / 4 := by ring
    rw [hid] at hu
    nlinarith [one_div_pos.mpr hΛ]
  have hUraw : εU + εU < c.fieldTolerance := by
    have hu : εU ≤ εF := min_le_left _ _
    dsimp [εF] at hu
    linarith [c.fieldTolerance_pos]
  have hFraw : εF + εF < c.fieldTolerance := by dsimp [εF]; linarith [c.fieldTolerance_pos]
  have hAct (p : Point) (hp : p ∈ continuationRegion (4 / Λ)) :
      |P.U p - N.U (N.endpoint, p.2)| < εA ∧
      |parameterPartial P.U p - parameterPartial N.U (N.endpoint, p.2)| < εA ∧
      |parameterPartial P.f p / P.f p - parameterPartial N.f (N.endpoint, p.2) /
        N.f (N.endpoint, p.2)| < εA :=
    physical_endpoint_control E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw hOne hp
  have hBefore (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) (hx : p.1 ≤ 4 / Λ) :
      fieldJet P p = fieldJet Q p :=
    physical_fieldJet_before E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw
      (r.profiles_mem hp.2 hp.1.1) hx
  have hGlobal (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) :
      |P.U p - Q.U p| ≤ 1 / Λ ∧
      |parameterPartial P.U p - parameterPartial Q.U p| ≤ 1 / Λ ∧
      |parameterPartial P.f p / P.f p - parameterPartial Q.f p / Q.f p| ≤ 1 := by
    by_cases hx : p.1 ≤ 4 / Λ
    · have hh := hBefore p hp hx
      have hU : P.U p = Q.U p := congrFun hh 1
      have hUη : parameterPartial P.U p = parameterPartial Q.U p := congrFun hh 3
      have hF : P.f p = Q.f p := congrFun hh 0
      have hFη : parameterPartial P.f p = parameterPartial Q.f p := congrFun hh 2
      rw [hU, hUη, hF, hFη]
      simp only [sub_self, abs_zero]
      exact ⟨(one_div_pos.mpr hΛ).le, (one_div_pos.mpr hΛ).le, zero_le_one⟩
    · have hps : p ∈ continuationRegion (4 / Λ) := ⟨⟨(le_of_not_ge hx), hp.1.2⟩, hp.2⟩
      have ha := hAct p hps
      have hu : |Q.U p - N.U (N.endpoint, p.2)| < εU := hEnd.U_value p hps.1.1 hp.2
      have huη : |parameterPartial Q.U p - parameterPartial N.U (N.endpoint, p.2)| < εU :=
        hEnd.U_parameter p hps.1.1 hp.2
      have hg : |parameterPartial Q.f p / Q.f p - parameterPartial N.f (N.endpoint, p.2) /
          N.f (N.endpoint, p.2)| < 1 / 4 := hEndLog p hps.1.1 hp.2
      refine ⟨(abs_sub_of_common_center (ha.1.trans_le hAU) hu).le.trans hUscale,
        (abs_sub_of_common_center (ha.2.1.trans_le hAU) huη).le.trans hUscale, ?_⟩
      exact (abs_sub_of_common_center (ha.2.2.trans_le hA4) hg).le.trans (by norm_num)
  have hPrefix (p : Point) (hp : p ∈ ReferenceBounds.holdRegion) (hxend : p.1 ≤ r.holdRadius) :
      ‖fieldJet P p - fieldJet Q p‖ < c.fieldTolerance := by
    by_cases hx : p.1 ≤ 4 / Λ
    · rw [hBefore p hp hx, sub_self, norm_zero]
      exact c.fieldTolerance_pos
    · have hps : p ∈ continuationRegion (4 / Λ) := ⟨⟨le_of_not_ge hx, hp.1.2⟩, hp.2⟩
      have ha := hAct p hps
      have hl : |Real.log (P.f p) - Real.log (N.f (N.endpoint, p.2))| < εA :=
        physical_endpoint_log_value E.profile.family hΛ hsmall hδ hδT hP0 hT hb hw hw hOne hp.2
          ⟨hps.1.1, hxend⟩
      have hf := hang P p hp.2 (r.profiles_positive (original_interval_interior hp.2) hp.1.1)
        (hl.trans_le hAτ) (ha.2.2.trans_le hAτ)
      have hfu : |Q.f p - N.f (N.endpoint, p.2)| < εF := hEnd.f_value p hps.1.1 hp.2
      have hfη : |parameterPartial Q.f p - parameterPartial N.f (N.endpoint, p.2)| < εF :=
        hEnd.f_parameter p hps.1.1 hp.2
      have hu : |Q.U p - N.U (N.endpoint, p.2)| < εU := hEnd.U_value p hps.1.1 hp.2
      have huη : |parameterPartial Q.U p - parameterPartial N.U (N.endpoint, p.2)| < εU :=
        hEnd.U_parameter p hps.1.1 hp.2
      exact fieldJet_close P Q c.fieldTolerance_pos
        ((abs_sub_of_common_center hf.1 hfu).trans hFraw)
        ((abs_sub_of_common_center (ha.1.trans_le hAU) hu).trans hUraw)
        ((abs_sub_of_common_center hf.2 hfη).trans hFraw)
        ((abs_sub_of_common_center (ha.2.1.trans_le hAU) huη).trans hUraw)
  refine ⟨r, c, ⟨hRef, hJet, hκc, hStocks, ?_, ?_⟩, hInit, hExtra, hLogExtra⟩
  · intro p hp hendp
    apply hTransfer P rfl p hp (r.profiles_mem hp.2 ((div_pos (by norm_num) hΛ).le.trans hp.1.1))
    intro t ht
    exact hPrefix (t, p.2) ⟨⟨ht.1, ht.2.trans hp.1.2⟩, hp.2⟩ (ht.2.trans hendp)
  · intro p hp
    exact nearby_source_jets P Q hΛ hJet (fun q hq => (hGlobal q hq).1)
      (fun q hq => (hGlobal q hq).2.1) (fun q hq => (hGlobal q hq).2.2)
      hp (r.profiles_mem hp.2 hp.1.1)

/-! ## Cone comparison followed by the actual lag barrier -/

theorem comparable_relaxed_before_hold {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c) {p : Point}
    (hp : p ∈ continuationRegion (4 / Λ))
    (hstart : r.startRadius ≤ p.1) (hend : p.1 ≤ r.holdRadius) :
    IsRelaxed r.profiles h p := by
  have hX := r.startRadius_pos.trans_le hstart
  have hpH : p ∈ ReferenceBounds.holdRegion := ⟨⟨hX.le, hp.1.2⟩, hp.2⟩
  have hs := r.physical_shears hp.2 hstart
  have hclose := hc.stock_close p hp hend
  have hrefcone : (9 / 4 : ℝ) < ReferenceBounds.p1 r.reference.profiles h p +
      ReferenceBounds.p2 r.reference.profiles h p ^ 2 / ReferenceBounds.p1 r.reference.profiles h p :=
    hc.reference_bounds.cone_margin p hpH hp.1.1
  have hlarge : r.reference.bigTime ≤ r.reference.logTime p.1 →
      3 ≤ ReferenceBounds.p1 r.reference.profiles h p := by
    intro hy
    change Real.log (100 / r.reference.radius0) ≤ Real.log (p.1 / r.reference.radius0) at hy
    have hd := (Real.log_le_log_iff (div_pos (by norm_num) r.reference.radius0_pos)
      (div_pos hX r.reference.radius0_pos)).mp hy
    have h100 : (100 : ℝ) ≤ p.1 := (div_le_div_iff_of_pos_right r.reference.radius0_pos).mp hd
    have hh := reference_first_lower E hΛ r.refTime_pos r.refTime_bound hP0 hsmall hσ
      hc.reference_bounds hpH hX
    change (6 / 5 : ℝ) * p.1 ≤ ReferenceBounds.p1 r.reference.profiles h p at hh
    linarith
  unfold IsRelaxed
  rw [hs.1, hs.2]
  exact two_ramp_relaxed c r.kappa_pos hc.damping_le r.widthU_pos r.widthA_pos
    (hc.stock_bounds.first_positive p hp) (hc.stock_bounds.first_bound p hp)
    (hc.stock_bounds.second_bound p hp) (hc.stock_bounds.ratio_bound p hp)
    hclose.first hclose.second hclose.ratio hrefcone.le hlarge

/-- A reusable statement of the source estimate already proved by compact
absorption before the scale is chosen. -/
noncomputable def HoldSourceControl (h j σ Λ B : ℝ) : Prop :=
  ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
    p.2 ∈ Icc (-1 : ℝ) 1 → ReferenceBounds.logSlope P p = 3 / 5 →
    |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
    |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
    |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
    (5 / 4 : ℝ) < ReferenceBounds.sourceQ P h p

theorem comparable_final_first {h j σ Λ C B K X η : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c)
    (hsource : HoldSourceControl h j σ Λ (B + 2))
    (hη : η ∈ Icc (-1 : ℝ) 1) (hX : X ∈ Icc r.holdRadius (110 : ℝ)) :
    2 < ReferenceBounds.p1 r.profiles h (X, η) := by
  have hr0 : 4 / Λ ≤ r.holdRadius := by
    have h0 := r.radius0_lt_start.le.trans r.start_le_hold
    simpa only [r.radius0_eq] using h0
  have hp0 : (r.holdRadius, η) ∈ continuationRegion (4 / Λ) :=
    ⟨⟨hr0, r.hold_lt_final.le⟩, hη⟩
  have hi := comparable_relaxed_before_hold E hσ r c hc hp0 r.start_le_hold le_rfl
  have hinit : 2 < ReferenceBounds.p1 r.profiles h (r.holdRadius, η) := by
    have hp := hi.projection_positive
    change 2 < projection _ _ _ _ at hp
    rw [(r.final_shears hη (le_rfl : r.holdRadius ≤ r.holdRadius)).2] at hp
    simpa only [projection, zero_div, mul_zero, add_zero] using hp
  apply actual_hold_barrier r.profiles (by linarith [r.hundred_lt_hold]) hX.1
    (NaturalAxisData.L_pos hsmall hη) (NaturalEntrance.L_le_one (NaturalAxisRange.ofSmall hsmall) η)
    (fun t ht => r.profiles_mem hη (r.holdRadius_pos.le.trans ht.1))
    (fun t ht => r.profiles_positive (original_interval_interior hη) (r.holdRadius_pos.le.trans ht.1))
    (fun t ht => r.final_logSlope hη ht.1) ?_ hinit
  intro t ht
  have hp : (t, η) ∈ ReferenceBounds.holdRegion :=
    ⟨⟨r.holdRadius_pos.le.trans ht.1, ht.2.trans hX.2⟩, hη⟩
  obtain ⟨hu, hv, hvη, hg⟩ := hc.source_jets (t, η) hp
  have hq := hsource r.profiles (t, η) hη (r.final_logSlope hη ht.1) hu hv hvη hg
  linarith

theorem comparable_relaxed {h j σ Λ C B K : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (hσ : 0 < σ)
    (r : RampParameters E.profile.family hΛ hsmall hP0) (c : ComparisonScales)
    (hc : ComparableRamp (B := B) (K := K) E r c)
    (hsource : HoldSourceControl h j σ Λ (B + 2))
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hX : p.1 ∈ Icc r.startRadius (110 : ℝ)) :
    IsRelaxed r.profiles h p := by
  by_cases hend : p.1 ≤ r.holdRadius
  · have hx0 : 4 / Λ ≤ p.1 := by
      have hh := r.radius0_lt_start.le.trans hX.1
      simpa only [r.radius0_eq] using hh
    exact comparable_relaxed_before_hold E hσ r c hc ⟨⟨hx0, hX.2⟩, hη⟩ hX.1 hend
  · have hhold : r.holdRadius ≤ p.1 := (lt_of_not_ge hend).le
    have hfirst := comparable_final_first E hσ r c hc hsource hη ⟨hhold, hX.2⟩
    have hs := r.final_shears hη hhold
    unfold IsRelaxed
    rw [hs.1, hs.2]
    exact zero_axial_relaxed (by norm_num) (by norm_num) hfirst

/-! ## The complete ordered existence statement -/

structure ContinuationWitness {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) (N : ℕ) (ε : ℝ) where
  parameters : RampParameters E.profile.family hΛ hsmall hP0
  initial_activation : InitialActivationBound parameters
  relaxed : ∀ p : Point, p.2 ∈ Icc (-1 : ℝ) 1 →
    p.1 ∈ Icc parameters.startRadius (110 : ℝ) → IsRelaxed parameters.profiles h p
  final_first : ∀ X ∈ Icc parameters.holdRadius (110 : ℝ), ∀ η ∈ Icc (-1 : ℝ) 1,
    2 < ReferenceBounds.p1 parameters.profiles h (X, η)
  final_source : ∀ X ∈ Icc parameters.holdRadius (110 : ℝ), ∀ η ∈ Icc (-1 : ℝ) 1,
    (5 / 4 : ℝ) < ReferenceBounds.sourceQ parameters.profiles h (X, η)
  physical_control : parameters.reference.SmallPhysicalControl (Icc (-1 : ℝ) 1) N ε
    parameters.actTime parameters.kappa parameters.widthU parameters.widthA
  logarithmic_control : parameters.reference.SmallLogControl (Icc (-1 : ℝ) 1) N ε
    parameters.actTime parameters.kappa parameters.widthU parameters.widthA

/-- The actual relaxed continuation through `X = 110`, with the order
`Λ`, then `C`, then the small cutoff/activation/ramp parameters.  No source,
stock closeness or cone inequality is an input to this theorem. -/
theorem exists_activation_continuation {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
      ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
        ∃ E : NaturalEntrance.EntranceProfile d Λ C,
          ∀ N : ℕ, ∀ ε : ℝ, 0 < ε → Nonempty (ContinuationWitness E hΛ hsmall hP0 N ε) := by
  obtain ⟨B, M, hB, hM, hprep⟩ := ordered_reference_preparation d hsmall hσ hP0 hν hcut
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ hMΛ
  obtain ⟨hsource, C0, K, hC0, hK, hprofiles⟩ := hprep Λ hΛ hMΛ
  refine ⟨C0, hC0, ?_⟩
  intro C hC
  obtain ⟨E, r0, hr0, href⟩ := hprofiles C hC
  refine ⟨E, ?_⟩
  intro N ε hε
  obtain ⟨r, c, hc, hinit, hphysical, hlog⟩ := exists_comparable_ramp E hΛ (hM.trans hMΛ)
    (hC0.trans hC) (zero_lt_one.trans hB).le hK.le hsmall hσ hP0 hr0 href N hε
  refine ⟨{
    parameters := r
    initial_activation := hinit
    relaxed := fun p hη hX => comparable_relaxed E hσ r c hc hsource hη hX
    final_first := fun X hX η hη => comparable_final_first E hσ r c hc hsource hη hX
    final_source := ?_
    physical_control := hphysical
    logarithmic_control := hlog }⟩
  intro X hX η hη
  have hp : (X, η) ∈ ReferenceBounds.holdRegion :=
    ⟨⟨r.holdRadius_pos.le.trans hX.1, hX.2⟩, hη⟩
  obtain ⟨hu, hv, hvη, hg⟩ := hc.source_jets (X, η) hp
  exact hsource r.profiles (X, η) hη (r.final_logSlope hη hX.1) hu hv hvη hg

/-! ## Exact data passed to the shape transition -/

namespace RampParameters

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} {F : NaturalProfile.ProfileFamily d Λ C}
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} (r : RampParameters F hΛ hsmall hP0)

noncomputable def endpointAxial : ℝ → ℝ :=
  r.reference.endpointU r.actTime r.kappa r.widthU

noncomputable def endpointLogarithm : ℝ → ℝ :=
  r.reference.endpointLog r.actTime r.kappa r.widthU r.widthA C

theorem endpointAxial_smooth :
    ContDiffOn ℝ ∞ r.endpointAxial ReferencePath.parameterInterval :=
  r.reference.endpointU_smooth ReferencePath.parameterInterval_open _ _ _

theorem endpointLogarithm_smooth :
    ContDiffOn ℝ ∞ r.endpointLogarithm ReferencePath.parameterInterval :=
  r.reference.endpointLog_smooth ReferencePath.parameterInterval_open _ _ _ _ _

theorem initial_fields {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hX : p.1 ≤ (ReferencePath.Input.ofNatural hΛ F).endpoint * Real.exp r.refTime) :
    r.profiles.f p = StressActivation.FromReference.f (ReferencePath.Input.ofNatural hΛ F)
      r.actTime r.kappa r.refTime p ∧
    r.profiles.U p = StressActivation.FromReference.U (ReferencePath.Input.ofNatural hΛ F)
      r.actTime r.kappa r.refTime p :=
  TransitionRamp.physical_fields_eq_activation F hΛ hsmall r.refTime_pos r.refTime_bound hP0
    r.actTime_pos r.before_big r.widthU_pos r.widthA_pos hη hX

theorem terminal_fields (hC : 0 < C) {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hX : 110 ≤ p.1) :
    r.profiles.f p = C⁻¹ * Real.exp (Real.log (p.1 / 110) / 10 + r.endpointLogarithm p.2) /
        Real.sqrt (2 * p.1) ∧ r.profiles.U p = r.endpointAxial p.2 := by
  have hR : r.reference.radius0 < 110 := (r.reference.radius0_lt_100 r.bigTime_pos).trans (by norm_num)
  have hfit : r.reference.bigTime + r.widthU + r.widthA ≤ r.reference.finalTime := r.finish_before.le
  refine ⟨r.reference.physicalF_held ReferencePath.parameterInterval_open r.widthA_pos
    hfit hR hC hX hη, ?_⟩
  exact r.reference.physicalU_held ReferencePath.parameterInterval_open r.widthU_pos
    (by linarith [r.widthA_pos]) hR hX hη

theorem endpointLogarithm_eq_actual (hC : 0 < C) {η : ℝ}
    (hη : η ∈ ReferencePath.parameterInterval) :
    r.endpointLogarithm η = Real.log (C * r.profiles.E (110, η)) := by
  have hR : r.reference.radius0 < 110 := (r.reference.radius0_lt_100 r.bigTime_pos).trans (by norm_num)
  exact r.reference.endpointLog_eq_actual ReferencePath.parameterInterval_open r.widthA_pos
    r.finish_before.le hR hC hη

end RampParameters

end NavierStokes.ActivationContinuation
