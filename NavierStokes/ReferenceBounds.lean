import NavierStokes.ProfileHistories
import NavierStokes.NaturalProfile
import NavierStokes.NaturalEntrance
import NavierStokes.ReferencePath
import NavierStokes.ReferenceJetBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounds for the actual reference continuation

The history estimates below use the primitive-defined lags and pressure of
`ProfileHistories`. The reference source estimates and the ordered parameter
choices are derived from the constructed natural and reference profiles.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ReferenceBounds


open ProfileHistories

section Histories

variable {D : RadialDomain} (P : Profiles D)

noncomputable def logSlope (p : Point) : ℝ :=
  1 + p.1 * radialPartial P.f p / P.f p

noncomputable def sourceQ (h : ℝ) (p : Point) : ℝ :=
  -P.W h p * logSlope P p - h * (1 - 2 * p.2 * P.U p) -
    (StressAlgebra.axialExponent h * p.2 + StressAlgebra.coordinateFactor p.2 * P.U p) *
      (parameterPartial P.f p / P.f p)

noncomputable def p1 (h : ℝ) (p : Point) : ℝ :=
  p.1 * P.angularLag h p / NaturalAxisData.L h p.2

noncomputable def ns (h : ℝ) (p : Point) : ℝ :=
  P.axialLag h p / NaturalAxisData.L h p.2

noncomputable def p2 (h : ℝ) (p : Point) : ℝ := p.1 * ns P h p / P.E p

noncomputable def coneSize (h : ℝ) (p : Point) : ℝ :=
  p1 P h p + p2 P h p ^ 2 / p1 P h p

theorem H_radialPartial {p : Point} (hp : p ∈ D.carrier) :
    radialPartial P.H p = 2 * P.f p + 2 * p.1 * radialPartial P.f p := by
  have h := ((hasDerivAt_id p.1).const_mul 2).mul
    (radialPartial_hasDerivAt D P.f_smooth hp)
  have he := (radialPartial_hasDerivAt D P.H_smooth hp).unique h
  simpa only [one_mul, mul_one, id_eq, Prod.eta] using he

theorem angularSource_eq {p : Point} (hp : p ∈ D.carrier) (hf : P.f p ≠ 0) (h : ℝ) :
    P.angularSource h p = P.H p * sourceQ P h p := by
  rw [Profiles.angularSource, H_radialPartial P hp, P.parameterPartial_H hp]
  unfold StressAlgebra.angularSource sourceQ logSlope Profiles.H
  field_simp

theorem p1_primitive {p : Point} (hX : p.1 ≠ 0) (h : ℝ) :
    p1 P h p = primitive (P.angularSource h) p /
      (NaturalAxisData.L h p.2 * P.H p) := by
  unfold p1 Profiles.angularLag
  calc
    _ = ((p.1 * primitive (P.angularSource h) p) / (p.1 * P.H p)) /
        NaturalAxisData.L h p.2 := by ring
    _ = (primitive (P.angularSource h) p / P.H p) / NaturalAxisData.L h p.2 := by
      rw [mul_div_mul_left _ _ hX]
    _ = _ := by ring

theorem ns_primitive (p : Point) (h : ℝ) :
    ns P h p = primitive (P.axialSource h) p /
      (NaturalAxisData.L h p.2 * p.1) := by
  unfold ns Profiles.axialLag
  ring

theorem parameterPartial_square {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (fun q => P.f q ^ 2) p = 2 * P.f p * parameterPartial P.f p := by
  exact (parameterPartial_hasDerivAt D (P.f_smooth.pow 2) hp).unique
    (by simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub, Prod.eta] using
      (parameterPartial_hasDerivAt D P.f_smooth hp).fun_pow 2)

theorem pressure_parameter_increment {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.pressure p - deriv P.pressure0 p.2 =
      ∫ s in (0 : ℝ)..p.1, 2 * P.f (s, p.2) * parameterPartial P.f (s, p.2) := by
  rw [P.parameterPartial_pressure hp, add_sub_cancel_left,
    parameterPartial_primitive D (P.f_smooth.pow 2) hp]
  unfold primitive
  apply intervalIntegral.integral_congr
  intro s hs
  exact parameterPartial_square P (D.segment_mem hp hs)

theorem pressure_increment_bound {p : Point} (_ : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (_ : 0 ≤ K) (_ : 0 < C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C) :
    |P.pressure p - P.pressure0 p.2| ≤ p.1 * K ^ 2 / C ^ 2 := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := (K / C) ^ 2)
    (f := fun s => P.f (s, p.2) ^ 2) ?_
  · simp only [Profiles.pressure, add_sub_cancel_left, primitive]
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX] at hbound
    convert! hbound using 1 ; ring
  · intro s hs
    have hsi : s ∈ Icc (0 : ℝ) p.1 :=
      ⟨(uIoc_of_le hX ▸ hs).1.le, (uIoc_of_le hX ▸ hs).2⟩
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hf s hsi) 2

theorem pressure_parameter_increment_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (hK : 0 ≤ K) (hC : 0 < C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C)
    (hfη : ∀ s ∈ Icc (0 : ℝ) p.1, |parameterPartial P.f (s, p.2)| ≤ K / C) :
    |parameterPartial P.pressure p - deriv P.pressure0 p.2| ≤ 2 * p.1 * K ^ 2 / C ^ 2 := by
  rw [pressure_parameter_increment P hp]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := 2 * (K / C) ^ 2)
    (f := fun s => 2 * P.f (s, p.2) * parameterPartial P.f (s, p.2)) ?_
  · rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hX] at hbound
    convert! hbound using 1 ; ring
  · intro s hs
    have hsi : s ∈ Icc (0 : ℝ) p.1 :=
      ⟨(uIoc_of_le hX ▸ hs).1.le, (uIoc_of_le hX ▸ hs).2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (2 * (K / C)) * (K / C) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hf s hsi) (by norm_num))
          (hfη s hsi) (abs_nonneg _) (mul_nonneg (by norm_num) (div_nonneg hK hC.le))
      _ = _ := by ring

theorem pressure_dot_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 ≤ p.1)
    {K C : ℝ} (hf : |P.f p| ≤ K / C) :
    |p.1 * radialPartial P.pressure p| ≤ p.1 * K ^ 2 / C ^ 2 := by
  rw [P.radialPartial_pressure hp, abs_mul, abs_of_nonneg hX, abs_pow]
  have h := pow_le_pow_left₀ (abs_nonneg _) hf 2
  have hm := mul_le_mul_of_nonneg_left h hX
  convert! hm using 1 ; ring

theorem p1_lower_from_source {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {q : ℝ} (hq : 0 ≤ q)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc (0 : ℝ) p.1, q ≤ sourceQ P h (s, p.2)) :
    q * p.1 / (2 * NaturalAxisData.L h p.2) ≤ p1 P h p := by
  have hfX := hf p.1 ⟨hX.le, le_rfl⟩
  have hHp : 0 < P.H p := by change 0 < 2 * p.1 * P.f p; positivity
  rw [p1_primitive P hX.ne' h]
  apply (le_div_iff₀ (mul_pos hL hHp)).mpr
  have hsourceInt : (∫ s in (0 : ℝ)..p.1, 2 * P.f p * q * s) ≤
      primitive (P.angularSource h) p := by
    apply intervalIntegral.integral_mono_on (μ := volume) hX.le
      ((continuous_const.fun_mul continuous_id).intervalIntegrable 0 p.1)
      (radial_slice_intervalIntegrable D (P.angularSource_smooth h) hp)
    intro s hs
    have hsD : (s, p.2) ∈ D.carrier := D.segment_mem hp (uIcc_of_le hX.le ▸ hs)
    rw [angularSource_eq P hsD (hf s hs).ne']
    have hm := hmono hs ⟨hX.le, le_rfl⟩ hs.2
    have hHs : 0 ≤ P.H (s, p.2) := by
      change 0 ≤ 2 * s * P.f (s, p.2)
      exact mul_nonneg (mul_nonneg (by norm_num) hs.1) (hf s hs).le
    calc
      _ = (2 * s * P.f p) * q := by (try simp only [id_eq]); ring
      _ ≤ P.H (s, p.2) * q := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hs.1)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsource s hs) hHs
  rw [intervalIntegral.integral_const_mul, integral_id] at hsourceInt
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at hsourceInt
  have heq : (q * p.1 / (2 * NaturalAxisData.L h p.2)) *
      (NaturalAxisData.L h p.2 * P.H p) = (2 * P.f p * q) * (p.1 ^ 2 / 2) := by
    unfold Profiles.H
    field_simp
  rwa [heq]

theorem ns_deviation_bound {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {Z ε : ℝ}
    (hsource : ∀ s ∈ Icc (0 : ℝ) p.1, |P.axialSource h (s, p.2) - Z| ≤ ε) :
    |ns P h p - Z / NaturalAxisData.L h p.2| ≤ ε / NaturalAxisData.L h p.2 := by
  have heq : ns P h p - Z / NaturalAxisData.L h p.2 =
      (∫ s in (0 : ℝ)..p.1, P.axialSource h (s, p.2) - Z) /
        (NaturalAxisData.L h p.2 * p.1) := by
    rw [intervalIntegral.integral_sub (radial_slice_intervalIntegrable D (P.axialSource_smooth h) hp)
      intervalIntegrable_const, intervalIntegral.integral_const]
    rw [ns_primitive]
    unfold primitive
    simp only [sub_zero, smul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos hL hX)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := p.1) (C := ε) (f := fun s => P.axialSource h (s, p.2) - Z)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact hsource s ⟨(uIoc_of_le hX.le ▸ hs).1.le, (uIoc_of_le hX.le ▸ hs).2⟩)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hX] at hb
  apply (div_le_iff₀ (mul_pos hL hX)).mpr
  have he : ε / NaturalAxisData.L h p.2 * (NaturalAxisData.L h p.2 * p.1) = ε * p.1 := by
    field_simp
  rwa [he]

theorem p1_lower_from_initial {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {a b q : ℝ}
    (ha : 0 < a) (haX : a ≤ p.1) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc a p.1, q ≤ sourceQ P h (s, p.2))
    (hinit : b ≤ p1 P h (a, p.2)) :
    b * a / p.1 + q / (2 * NaturalAxisData.L h p.2) * (p.1 - a ^ 2 / p.1) ≤ p1 P h p := by
  have hfX := hf p.1 ⟨hX.le, le_rfl⟩
  have hfa := hf a ⟨ha.le, haX⟩
  have hHa : 0 < P.H (a, p.2) := by change 0 < 2 * a * P.f (a, p.2); positivity
  have hHX : 0 < P.H p := by change 0 < 2 * p.1 * P.f p; positivity
  have hfun : ContinuousOn (fun s => P.angularSource h (s, p.2)) (Icc 0 p.1) :=
    (radial_slice_continuous D (P.angularSource_smooth h) p.2).mono
      (fun s hs => D.segment_mem hp (uIcc_of_le hX.le ▸ hs))
  have h0a : IntervalIntegrable (fun s => P.angularSource h (s, p.2)) volume 0 a :=
    ContinuousOn.intervalIntegrable_of_Icc ha.le
      (hfun.mono (fun s hs => ⟨hs.1, hs.2.trans haX⟩))
  have haXint : IntervalIntegrable (fun s => P.angularSource h (s, p.2)) volume a p.1 :=
    ContinuousOn.intervalIntegrable_of_Icc haX
      (hfun.mono (fun s hs => ⟨ha.le.trans hs.1, hs.2⟩))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0a haXint
  have hlow : (2 * P.f p * q) * ((p.1 ^ 2 - a ^ 2) / 2) ≤
      ∫ s in a..p.1, P.angularSource h (s, p.2) := by
    have hcmp := intervalIntegral.integral_mono_on (μ := volume) haX
      ((continuous_const.fun_mul continuous_id).intervalIntegrable a p.1) haXint
      (f := fun s => (2 * P.f p * q) * s) (g := fun s => P.angularSource h (s, p.2)) ?_
    · rw [intervalIntegral.integral_const_mul, integral_id] at hcmp
      exact hcmp
    · intro s hs
      have hs0 : s ∈ Icc (0 : ℝ) p.1 := ⟨ha.le.trans hs.1, hs.2⟩
      have hsD := D.segment_mem hp (uIcc_of_le hX.le ▸ hs0)
      rw [angularSource_eq P hsD (hf s hs0).ne']
      have hm := hmono hs0 ⟨hX.le, le_rfl⟩ hs.2
      have hHs : 0 ≤ P.H (s, p.2) := by
        change 0 ≤ 2 * s * P.f (s, p.2)
        exact mul_nonneg (mul_nonneg (by norm_num) hs0.1) (hf s hs0).le
      calc
        _ = (2 * s * P.f p) * q := by ring
        _ ≤ P.H (s, p.2) * q := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hs0.1)) hq
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsource s hs) hHs
  rw [p1_primitive P ha.ne' h] at hinit
  have hinit' := (le_div_iff₀ (mul_pos hL hHa)).mp hinit
  have hmonoA := hmono ⟨ha.le, haX⟩ ⟨hX.le, le_rfl⟩ haX
  have hinit0 : b * (NaturalAxisData.L h p.2 * (2 * a * P.f p)) ≤
      primitive (P.angularSource h) (a, p.2) := by
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmonoA (by positivity : 0 ≤ 2 * a)) hL.le) hb).trans hinit'
  rw [p1_primitive P hX.ne' h]
  apply (le_div_iff₀ (mul_pos hL hHX)).mpr
  have htotal := add_le_add hinit0 hlow
  change _ ≤ primitive (P.angularSource h) (a, p.2) + _ at htotal
  unfold primitive at htotal ⊢
  rw [hsplit] at htotal
  convert! htotal using 1
  unfold Profiles.H
  field_simp [hL.ne', hX.ne']

theorem p1_equation {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (hf : P.f p ≠ 0) (h : ℝ) :
    p.1 * deriv (fun x => p1 P h (x, p.2)) p.1 + logSlope P p * p1 P h p =
      p.1 * sourceQ P h p / NaturalAxisData.L h p.2 := by
  have hH := P.H_ne_zero hX.ne' hf
  have hQ := P.angularLag_equation h hp hX.ne' hH
  have hQd := P.angularLag_hasDerivAt h hp hX.ne' hH
  have hd := ((hasDerivAt_id p.1).fun_mul hQd).div_const (NaturalAxisData.L h p.2)
  rw [show deriv (fun x => p1 P h (x, p.2)) p.1 =
    (P.angularLag h p + p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1) /
      NaturalAxisData.L h p.2 by
        simpa only [p1, one_mul, Prod.eta, id_eq, ← hQd.deriv] using hd.deriv]
  rw [angularSource_eq P hp hf, mul_div_cancel_left₀ _ hH] at hQ
  have hs : p.1 * radialPartial P.H p / P.H p = logSlope P p := by
    rw [H_radialPartial P hp]
    unfold Profiles.H logSlope
    field_simp
  rw [hs] at hQ
  unfold p1
  calc
    _ = p.1 * (p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1 +
        (1 + logSlope P p) * P.angularLag h p) / NaturalAxisData.L h p.2 := by ring
    _ = _ := by rw [hQ]

theorem ns_equation {p : Point} (hp : p ∈ D.carrier) (hX : p.1 ≠ 0) (h : ℝ) :
    p.1 * deriv (fun x => ns P h (x, p.2)) p.1 + ns P h p =
      P.axialSource h p / NaturalAxisData.L h p.2 := by
  have hN := P.axialLag_equation h hp hX
  have hNd := P.axialLag_hasDerivAt h hp hX
  have hd := hNd.div_const (NaturalAxisData.L h p.2)
  rw [show deriv (fun x => ns P h (x, p.2)) p.1 =
    deriv (fun x => P.axialLag h (x, p.2)) p.1 / NaturalAxisData.L h p.2 by
      simpa only [ns, ← hNd.deriv] using hd.deriv]
  unfold ns
  calc
    _ = (p.1 * deriv (fun x => P.axialLag h (x, p.2)) p.1 + P.axialLag h p) /
        NaturalAxisData.L h p.2 := by ring
    _ = _ := by rw [hN]

theorem lower_comparison_preserves {X a L b q : ℝ}
    (ha : 0 < a) (haX : a ≤ X) (hL : 0 < L) (hq : 0 ≤ q) (hqa : b * L ≤ q * a) :
    b ≤ b * a / X + q / (2 * L) * (X - a ^ 2 / X) := by
  have hX : 0 < X := ha.trans_le haX
  have hfac : 0 ≤ q * (X + a) - 2 * b * L := by
    have hm := mul_le_mul_of_nonneg_left haX hq
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr haX) hfac
  have heq : b * a / X + q / (2 * L) * (X - a ^ 2 / X) =
      (2 * L * b * a + q * (X ^ 2 - a ^ 2)) / (2 * L * X) := by
    field_simp
  rw [heq]
  apply (le_div_iff₀ (by positivity : 0 < 2 * L * X)).mpr
  nlinarith

theorem p1_preserves_lower {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1)
    (h : ℝ) (hL : 0 < NaturalAxisData.L h p.2) {a b q : ℝ}
    (ha : 0 < a) (haX : a ≤ p.1) (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hqa : b * NaturalAxisData.L h p.2 ≤ q * a)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, 0 < P.f (s, p.2))
    (hmono : AntitoneOn (fun s => P.f (s, p.2)) (Icc (0 : ℝ) p.1))
    (hsource : ∀ s ∈ Icc a p.1, q ≤ sourceQ P h (s, p.2))
    (hinit : b ≤ p1 P h (a, p.2)) : b ≤ p1 P h p :=
  (lower_comparison_preserves ha haX hL hq hqa).trans
    (p1_lower_from_initial P hp hX h hL ha haX hb hq hf hmono hsource hinit)

theorem p1_at_hundred_gt_three {η h : ℝ} (hp : (100, η) ∈ D.carrier)
    (hL : 0 < NaturalAxisData.L h η) (hL1 : NaturalAxisData.L h η ≤ 1)
    (hf : ∀ s ∈ Icc (0 : ℝ) 100, 0 < P.f (s, η))
    (hmono : AntitoneOn (fun s => P.f (s, η)) (Icc (0 : ℝ) 100))
    (hsource : ∀ s ∈ Icc (0 : ℝ) 100, (12 / 5 : ℝ) ≤ sourceQ P h (s, η)) :
    3 < p1 P h (100, η) := by
  have hb := p1_lower_from_source P hp (by norm_num : (0 : ℝ) < 100) h hL
    (by norm_num : (0 : ℝ) ≤ 12 / 5) hf hmono hsource
  have hn : (3 : ℝ) < (12 / 5) * 100 / (2 * NaturalAxisData.L h η) := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hL)).mpr
    nlinarith
  exact hn.trans_le hb

theorem p2_large_of_small_f {p : Point} (hX : 0 < p.1) (hX110 : p.1 ≤ 110)
    (h : ℝ) {a K C ν : ℝ} (ha : 0 < a) (haX : a ≤ p.1)
    (_ : 0 < K) (hC : 0 < C) (hν : 0 < ν)
    (hf : 0 < P.f p) (hfbound : P.f p ≤ K / C)
    (hn : ν ≤ |ns P h p|) (hlarge : 18 * K / (a * ν) < C) :
    (6 / 5 : ℝ) < |p2 P h p| := by
  have hs : Real.sqrt (2 * p.1) ≤ 15 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
  have hE : 0 < P.E p := mul_pos (Real.sqrt_pos.mpr (by positivity)) hf
  have hEb : P.E p ≤ 15 * K / C := by
    change Real.sqrt (2 * p.1) * P.f p ≤ _
    calc
      _ ≤ 15 * (K / C) := mul_le_mul hs hfbound hf.le (by norm_num)
      _ = _ := by ring
  have hc : 18 * K / C < a * ν := by
    apply (div_lt_iff₀ hC).mpr
    have hh := (div_lt_iff₀ (mul_pos ha hν)).mp hlarge
    nlinarith
  have hnprod : a * ν ≤ p.1 * |ns P h p| :=
    mul_le_mul haX hn hν.le hX.le
  rw [p2, abs_div, abs_mul, abs_of_pos hX, abs_of_pos hE]
  apply (lt_div_iff₀ hE).mpr
  have hmult := mul_le_mul_of_nonneg_left hEb (by norm_num : (0 : ℝ) ≤ 6 / 5)
  have hid : (6 / 5 : ℝ) * (15 * K / C) = 18 * K / C := by ring
  rw [hid] at hmult
  linarith

theorem cone_margin_of_dichotomy {a b : ℝ} (ha : 0 < a)
    (hlarge : (23 / 10 : ℝ) ≤ a ∨ (6 / 5 : ℝ) < |b|) :
    (9 / 4 : ℝ) < a + b ^ 2 / a := by
  rcases hlarge with hfirst | hsecond
  · have hpos : 0 ≤ b ^ 2 / a := div_nonneg (sq_nonneg _) ha.le
    linarith
  · have hs : (6 / 5 : ℝ) ^ 2 < b ^ 2 := by
      have habs := sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 6 / 5) (abs_nonneg b) |>.mpr hsecond
      simpa only [sq_abs] using habs
    have hm : (12 / 5 : ℝ) * a < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - 6 / 5)]
    have hd : (12 / 5 : ℝ) < a + b ^ 2 / a := by
      calc
        (12 / 5 : ℝ) < (a ^ 2 + b ^ 2) / a := (lt_div_iff₀ ha).mpr hm
        _ = _ := by field_simp
    linarith

end Histories

/-! ## Uniform source estimates from bounded low-level jets

The compact variables below are the normalized axial value and average jets,
the positive natural angular value, and the bounded remainder of its parameter
logarithmic derivative. They are not source or cone assumptions.
-/

open NaturalAxisCoefficients

abbrev BoundedJets (B : ℝ) := Metric.closedBall (0 : Fin 5 → ℝ) B

instance (B : ℝ) : CompactSpace (BoundedJets B) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

abbrev SourceParameter (B : ℝ) :=
  NaturalEntrance.entranceSet × (Icc (0 : ℝ) 1 × BoundedJets B)

/-- `v 0` is the natural positive angular factor, `v 1` the normalized
axial value, `v 2, v 3` the normalized radial-average jets, and `v 4` the
bounded parameter-log-gradient remainder. -/
noncomputable def qRemainder (h j σ : ℝ) (p : Point) (θ : ℝ)
    (v : Fin 5 → ℝ) (t r : ℝ) : ℝ :=
  let W := NaturalAxisData.W h j p.2 -
    t * (2 * NaturalAxisData.D h * p.2 * v 2 + NaturalAxisData.d p.2 * v 3)
  let U := NaturalAxisData.U j p.2 + t * v 1
  let H := NaturalAxisData.H h j p.2 + t * NaturalAxisData.d p.2 * v 1
  show ℝ from -W * (1 + θ * p.1 * r / max (1 / 8 : ℝ) (v 0)) - h * (1 - 2 * p.2 * U) -
    H * v 4 - NaturalAxisData.d p.2 * v 1 * realGradient h j σ p.2

theorem qRemainder_continuous (h j : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun z : ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) =>
      qRemainder h j σ z.1.1.1 z.1.1.2 z.1.2 z.2.1 z.2.2) := by
  have hc := NaturalEntrance.realGradient_continuous h j hσ
  have hn : ∀ v : Fin 5 → ℝ, max (1 / 8 : ℝ) (v 0) ≠ 0 := by
    intro v
    have hb := le_max_left (1 / 8 : ℝ) (v 0)
    linarith
  dsimp only [qRemainder, NaturalAxisData.W, NaturalAxisData.H,
    NaturalAxisData.U, NaturalAxisData.d, NaturalAxisData.D]
  fun_prop (disch := first | exact fun x => hn x.1.2 | exact hn _)

noncomputable def qModel {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (p : SourceParameter B) (z : ℝ × ℝ) : ℝ :=
  qRemainder h j σ p.1.val p.2.1.val p.2.2.val z.1
    (NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1 1 + z.2)

theorem qModel_continuous {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (hσ : 0 < σ) :
    Continuous (fun p : SourceParameter B × (ℝ × ℝ) => qModel v B p.1 p.2) := by
  have hr : Continuous (fun p : SourceParameter B × (ℝ × ℝ) =>
      NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1.1 1) :=
    (continuous_apply 1).comp
      ((NaturalEntrance.sourceJets_continuous v.epsilon_pos (NaturalEntrance.referencePair v)).comp
        (continuous_fst.comp continuous_fst))
  let m : SourceParameter B × (ℝ × ℝ) → ((Point × ℝ) × (Fin 5 → ℝ)) × (ℝ × ℝ) :=
    fun p => (((p.1.1.val, p.1.2.1.val), p.1.2.2.val),
      (p.2.1, NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) p.1.1 1 + p.2.2))
  have hm : Continuous m := by
    dsimp [m]
    fun_prop
  simpa only [qModel, m, Function.comp_def] using (qRemainder_continuous h j hσ).comp hm

theorem qModel_at_chi_zero {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (B : ℝ) (hσ : 0 < σ) (p : SourceParameter B)
    (hchi : NaturalAxisData.chi h j σ p.1.val.2 = 0) :
    qModel v B p 0 = -NaturalAxisData.W h j p.1.val.2 -
      h * (1 - 2 * p.1.val.2 * NaturalAxisData.U j p.1.val.2) := by
  have hH := NaturalEntrance.chi_zero_imp_H_zero h j hσ hchi
  have hk := NaturalEntrance.gradient_zero_of_chi_zero h j hσ hchi
  have hr := NaturalEntrance.reference_phiY_zero v p.1 hchi
  simp only [qModel, qRemainder, Prod.fst_zero, Prod.snd_zero, hr, hH, hk, add_zero, zero_mul, mul_zero, zero_div, sub_zero, mul_one]

/-- Uniformity in all bounded reference jets is proved before the scale
and normalization are chosen. The growing term supplies no help at `χ=0`;
there the concrete axis source supplies the positive margin. -/
theorem qModel_uniform_lower {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (B : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∀ Λ : ℝ, M ≤ Λ → ∀ p : SourceParameter B,
      ∀ e : ℝ, |e| ≤ K / Λ →
        (47 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 * Λ *
            NaturalAxisData.chi h j σ p.1.val.2 + 12 / 5 <
          NaturalAxisData.L h p.1.val.2 * Λ * NaturalAxisData.chi h j σ p.1.val.2 +
            qModel v B p (1 / Λ, e) := by
  have hL : Continuous (NaturalAxisData.L h) := by unfold NaturalAxisData.L; fun_prop
  have hp : Continuous (fun p : SourceParameter B => p.1.val.2) := by fun_prop
  have hcoef : Continuous (fun p : SourceParameter B =>
      (3 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 * NaturalAxisData.chi h j σ p.1.val.2) :=
    ((continuous_const.mul (hL.comp hp)).mul
      ((NaturalEntrance.chi_continuous h j hσ).comp hp))
  have hbase : Continuous (fun p : SourceParameter B => qModel v B p 0) := by
    have hc := (qModel_continuous v B hσ).comp
      (continuous_id.prodMk (continuous_const (y := (0 : ℝ × ℝ))))
    simpa only [Function.comp_def, id_eq] using hc
  obtain ⟨M₀, hM₀, hmain⟩ := NaturalEntrance.compact_absorption _ _ hcoef hbase
    (fun p => mul_nonneg (mul_nonneg (by norm_num)
      (NaturalAxisData.L_pos hsmall p.1.property.2).le)
      (NaturalAxisData.chi_bounds h j hσ p.1.val.2).1) (5 / 2 : ℝ) (by
        intro p hz
        have hf : (3 / 50 : ℝ) * NaturalAxisData.L h p.1.val.2 ≠ 0 :=
          mul_ne_zero (by norm_num) (NaturalAxisData.L_pos hsmall p.1.property.2).ne'
        have hchi := (mul_eq_zero.mp hz).resolve_left hf
        rw [qModel_at_chi_zero v B hσ p hchi]
        linarith [NaturalEntrance.base_source_lower (NaturalAxisRange.ofSmall hsmall) p.1.property.2])
  obtain ⟨δ, hδ, hpert⟩ := NaturalEntrance.compact_small_perturbation _
    (qModel_continuous v B hσ) (by norm_num : (0 : ℝ) < 1 / 10)
  let M := max M₀ (1 + (1 + K) / δ)
  refine ⟨M, hM₀.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ p e he
  have hΛ0 : 0 < Λ := hM₀.trans_le ((le_max_left _ _).trans hΛ)
  have hΛ' : (1 + K) / δ < Λ := by
    have hm := (le_max_right M₀ (1 + (1 + K) / δ)).trans hΛ
    linarith
  have hmul := (div_lt_iff₀ hδ).mp hΛ'
  have ht : |1 / Λ| < δ := by
    rw [abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    nlinarith
  have he' : |e| < δ := he.trans_lt (by
    apply (div_lt_iff₀ hΛ0).mpr
    nlinarith)
  have hnorm : ‖((1 / Λ), e)‖ < δ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using And.intro ht he'
  have herror := (abs_lt.mp (hpert p ((1 / Λ), e) hnorm)).1
  have hb := hmain Λ ((le_max_left _ _).trans hΛ) p
  nlinarith

abbrev AxialSourceParameter (B : ℝ) := Icc (-1 : ℝ) 1 × BoundedJets B

/-- The axial source written in normalized axial jets and the actual three
pressure increments. Its zero-perturbation value is exactly `Z*`. -/
noncomputable def nModel (h j : ℝ) (P0 : ℝ → ℝ) (B : ℝ)
    (p : AxialSourceParameter B) (z : Fin 4 → ℝ) : ℝ :=
  let η := p.1.val
  let v := p.2.val
  let t := z 0
  let U := NaturalAxisData.U j η + t * v 0
  let W := NaturalAxisData.W h j η -
    t * (2 * NaturalAxisData.D h * η * v 2 + NaturalAxisData.d η * v 3)
  show ℝ from -W * (t * v 4) - NaturalAxisData.A h * (1 - 2 * η * U) * U -
    (NaturalAxisData.D h * η + NaturalAxisData.d η * U) * (4 + t * v 1) -
    NaturalAxisData.d η * (deriv P0 η + z 2) +
    4 * NaturalAxisData.A h * η * (P0 η + z 1) + 2 * η * z 3

theorem nModel_continuous (h j : ℝ) {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0) (B : ℝ) :
    Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => nModel h j P0 B p.1 p.2) := by
  have hp := hP0.continuous
  have hd : Continuous (deriv P0) := hP0.continuous_deriv (by simp)
  have he : Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.1.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hv : ∀ i : Fin 5, Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.1.2.val i) :=
    fun i => (continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  have hz : ∀ i : Fin 4, Continuous (fun p : AxialSourceParameter B × (Fin 4 → ℝ) => p.2 i) :=
    fun i => (continuous_apply i).comp continuous_snd
  have hp' := hp.comp he
  have hd' := hd.comp he
  dsimp only [nModel, NaturalAxisData.U, NaturalAxisData.W, NaturalAxisData.D,
    NaturalAxisData.A, NaturalAxisData.d]
  fun_prop

theorem nModel_zero (h j : ℝ) (P0 : ℝ → ℝ) (B : ℝ) (p : AxialSourceParameter B) :
    nModel h j P0 B p 0 = NaturalAxisData.Z h j P0 p.1 := by
  simp only [nModel, Pi.zero_apply, zero_mul, mul_zero, add_zero,
    NaturalAxisData.Z, NaturalAxisData.H, zero_sub]
  ring

theorem nModel_uniform_error (h j : ℝ) {P0 : ℝ → ℝ} (hP0 : ContDiff ℝ ∞ P0)
    (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : AxialSourceParameter B, ∀ z : Fin 4 → ℝ,
      ‖z‖ < δ → |nModel h j P0 B p z - NaturalAxisData.Z h j P0 p.1| < ε := by
  obtain ⟨δ, hδ, he⟩ := NaturalEntrance.compact_small_perturbation _
    (nModel_continuous h j hP0 B) hε
  refine ⟨δ, hδ, fun p z hz => ?_⟩
  simpa only [nModel_zero] using he p z hz

/-! ## The compact models are the actual profile sources -/

section ActualModels

variable {D : RadialDomain} (P : Profiles D)

theorem average_error_bound {F : ProfileHistories.Field} (hF : ContDiffOn ℝ ∞ F D.carrier)
    {p : Point} (hp : p ∈ D.carrier) {Λ b B : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |Λ * (F (t * p.1, p.2) - b)| ≤ B) :
    |Λ * (average F p - b)| ≤ B := by
  have hi : IntervalIntegrable (fun t : ℝ => F (t * p.1, p.2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hF.continuousOn.comp (by fun_prop) (fun t ht => D.scale_mem p hp t ht)
  have he : Λ * (average F p - b) =
      ∫ t in (0 : ℝ)..1, Λ * (F (t * p.1, p.2) - b) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [sub_zero, one_smul, ProfileHistories.average]
  rw [he]
  have hbt : ∀ t ∈ uIoc (0 : ℝ) 1, ‖Λ * (F (t * p.1, p.2) - b)‖ ≤ B := by
    intro t ht
    have ht' : t ∈ Ioc (0 : ℝ) 1 := (uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)
    simpa only [Real.norm_eq_abs] using hbound t ⟨ht'.1.le, ht'.2⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := B)
    (f := fun t => Λ * (F (t * p.1, p.2) - b)) hbt
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

noncomputable def qJets (j σ h Λ φ : ℝ) (p : Point) : Fin 5 → ℝ :=
  ![φ, Λ * (P.U p - NaturalAxisData.U j p.2),
    Λ * (P.Ubar p - NaturalAxisData.U j p.2),
    Λ * (average (parameterPartial P.U) p - 4),
    parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2]

noncomputable def nJets (j Λ : ℝ) (p : Point) : Fin 5 → ℝ :=
  ![Λ * (P.U p - NaturalAxisData.U j p.2),
    Λ * (parameterPartial P.U p - 4),
    Λ * (P.Ubar p - NaturalAxisData.U j p.2),
    Λ * (average (parameterPartial P.U) p - 4),
    Λ * (p.1 * radialPartial P.U p)]

noncomputable def pressureJets (Λ : ℝ) (p : Point) : Fin 4 → ℝ :=
  ![1 / Λ, P.pressure p - P.pressure0 p.2,
    parameterPartial P.pressure p - deriv P.pressure0 p.2,
    p.1 * P.f p ^ 2]

theorem sourceQ_model (h j σ : ℝ) {Λ φ Y θ r : ℝ} (hΛ : Λ ≠ 0)
    (hφ : (1 / 8 : ℝ) ≤ φ) (p : Point)
    (hrad : p.1 * radialPartial P.f p / P.f p = θ * Y * r / φ) :
    sourceQ P h p = NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 +
      qRemainder h j σ (Y, p.2) θ (qJets P j σ h Λ φ p) (1 / Λ) r := by
  have hg := NaturalProfile.gradient_identity h j σ p.2
  simp only [qRemainder, qJets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue, max_eq_right hφ]
  rw [← hrad]
  unfold sourceQ logSlope Profiles.W
  unfold NaturalAxisData.W NaturalAxisData.H at hg ⊢
  change _ = _
  simp only [NaturalAxisData.D, NaturalAxisData.d, StressAlgebra.axialExponent,
    StressAlgebra.coordinateFactor] at hg ⊢
  field_simp [hΛ]
  linear_combination -(2 * Λ) * hg

theorem sourceN_model (h j : ℝ) {Λ B : ℝ} (hΛ : Λ ≠ 0)
    (p : Point) (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hv : nJets P j Λ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B) :
    P.axialSource h p = nModel h j P.pressure0 B
      (⟨p.2, hη⟩, ⟨nJets P j Λ p, hv⟩) (pressureJets P Λ p) := by
  simp only [nModel, nJets, pressureJets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue]
  unfold Profiles.axialSource StressAlgebra.axialSource Profiles.W
  unfold NaturalAxisData.W NaturalAxisData.d NaturalAxisData.D NaturalAxisData.A
  unfold StressAlgebra.axialExponent StressAlgebra.velocityExponent StressAlgebra.coordinateFactor
  field_simp [hΛ] ; ring

theorem qJets_bound (h j σ : ℝ) {Λ B φ : ℝ} (hB : 0 ≤ B) {p : Point}
    (hφ : |φ| ≤ B)
    (hu : |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (hv : |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B)
    (hvη : |Λ * (average (parameterPartial P.U) p - 4)| ≤ B)
    (hfη : |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B) :
    qJets P j σ h Λ φ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hφ
  · exact hu
  · exact hv
  · exact hvη
  · exact hfη

theorem nJets_bound (j : ℝ) {Λ B : ℝ} (hB : 0 ≤ B) {p : Point}
    (hu : |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (huη : |Λ * (parameterPartial P.U p - 4)| ≤ B)
    (hv : |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B)
    (hvη : |Λ * (average (parameterPartial P.U) p - 4)| ≤ B)
    (huX : |Λ * (p.1 * radialPartial P.U p)| ≤ B) :
    nJets P j Λ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B := by
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB]
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hu
  · exact huη
  · exact hv
  · exact hvη
  · exact huX

end ActualModels

/-! ## Exact agreement with the natural entrance histories -/

section NaturalAgreement

open NaturalAxisBridge NaturalProfile ReferencePath

theorem radialPartial_natural {F : ProfileHistories.Field} {p : Point}
    (hF : ContDiffAt ℝ ∞ F p) : radialPartial F p = partialY F p := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.deriv.symm

theorem parameterPartial_natural {F : ProfileHistories.Field} {p : Point}
    (hF : ContDiffAt ℝ ∞ F p) : parameterPartial F p = partialEta F p := by
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.deriv.symm

theorem natural_average_eq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : Point} (hp : p ∈ domain Λ) : ProfileHistories.average U p = V p := by
  by_cases hx : p.1 = 0
  · have he : p = (0, p.2) := Prod.ext hx rfl
    rw [he, average_at_axis, hs.U_axis p.2 hp.2, hs.average_axis p.2 hp.2]
  · rw [average_eq_quotient U hx]
    change (∫ X in (0 : ℝ)..p.1, U (X, p.2)) / p.1 = V p
    rw [← hs.average_integral p hp, mul_div_cancel_left₀ _ hx]

theorem natural_average_eventuallyEq {h j Λ : ℝ} {P0 a : ℝ → ℝ}
    {f U V Pr : ProfileHistories.Field} (hs : IsNaturalSolution h j Λ P0 a f U V Pr)
    {p : Point} (hp : p ∈ domain Λ) : ProfileHistories.average U =ᶠ[𝓝 p] V := by
  filter_upwards [(domain_isOpen Λ).mem_nhds hp] with q hq
  exact natural_average_eq hs hq

variable (N : ReferencePath.Input)

theorem ref_natural_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 < N.endpoint * Real.exp δ) :
    N.refF δ =ᶠ[𝓝 p] N.f ∧ N.refU δ =ᶠ[𝓝 p] N.U := by
  have he : {q : Point | q.1 < N.endpoint * Real.exp δ ∧ q.2 ∈ parameterInterval} ∈ 𝓝 p :=
    ((isOpen_lt continuous_fst continuous_const).inter
      (parameterInterval_open.preimage continuous_snd)).mem_nhds ⟨hX, hη⟩
  constructor
  · filter_upwards [he] with q hq
    exact N.refF_eq_natural hδ hδT hq.2 hq.1.le
  · filter_upwards [he] with q hq
    exact N.refU_eq_natural hδ hδT hq.2 hq.1.le

theorem average_refU_eq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 ≤ N.endpoint * Real.exp δ) :
    ProfileHistories.average (N.refU δ) p = ProfileHistories.average N.U p := by
  unfold ProfileHistories.average
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := (uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht)
  dsimp only
  apply N.refU_eq_natural hδ hδT (p := (t * p.1, p.2)) hη
  have hpos : 0 < N.endpoint * Real.exp δ := mul_pos N.endpoint_pos (Real.exp_pos _)
  calc
    t * p.1 ≤ t * (N.endpoint * Real.exp δ) := mul_le_mul_of_nonneg_left hX ht'.1
    _ ≤ N.endpoint * Real.exp δ := mul_le_of_le_one_left hpos.le ht'.2

theorem average_refU_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 < N.endpoint * Real.exp δ) :
    ProfileHistories.average (N.refU δ) =ᶠ[𝓝 p] ProfileHistories.average N.U := by
  have he : {q : Point | q.1 < N.endpoint * Real.exp δ ∧ q.2 ∈ parameterInterval} ∈ 𝓝 p :=
    ((isOpen_lt continuous_fst continuous_const).inter
      (parameterInterval_open.preimage continuous_snd)).mem_nhds ⟨hX, hη⟩
  filter_upwards [he] with q hq
  exact average_refU_eq N hδ hδT hq.2 hq.1.le

end NaturalAgreement

section ReferenceHistories

open NaturalAxisBridge NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (F : NaturalEntrance.CoefficientProfile d Λ C) (hΛ : 0 < Λ)

/-- All pressure and stock fields of this profile are the literal histories
of the constructed reference continuation. -/
noncomputable def referenceProfiles {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) : Profiles (Input.ofNatural hΛ F.family).radialDomain :=
  (Input.ofNatural hΛ F.family).histories hδ hδT P0 hP0

theorem reference_mem {p : Point} (hX : 0 ≤ p.1) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    p ∈ (Input.ofNatural hΛ F.family).radialDomain.carrier := by
  refine ⟨?_, NaturalAxisCoefficients.original_interval_interior hη⟩
  change -20 < Λ * p.1
  exact lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX)

theorem endpoint_strict_collar {δ : ℝ} (hδ : 0 < δ) :
    (4 / Λ : ℝ) < (Input.ofNatural hΛ F.family).endpoint * Real.exp δ := by
  have he : 1 < Real.exp δ := Real.one_lt_exp_iff.mpr hδ
  change 4 / Λ < (4 / Λ) * Real.exp δ
  nlinarith [show (0 : ℝ) < 4 / Λ by positivity]

theorem reference_sourceQ_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hp : p ∈ domain Λ) (hX : p.1 ≤ 4 / Λ) :
    sourceQ (referenceProfiles F hΛ hδ hδT hP0) h p =
      NaturalEntrance.Sq h F.family.f F.family.U F.family.Ubar p := by
  let N := Input.ofNatural hΛ F.family
  let P := referenceProfiles F hΛ hδ hδT hP0
  have hpN : p ∈ N.radialDomain.carrier := ⟨hp.1.1, hp.2⟩
  have hc : p.1 < N.endpoint * Real.exp δ := hX.trans_lt (endpoint_strict_collar F hΛ hδ)
  obtain ⟨hf, hu⟩ := ref_natural_eventuallyEq N hδ hδT (p := p) hp.2 hc
  have hav := (average_refU_eventuallyEq N hδ hδT (p := p) hp.2 hc).trans
    (natural_average_eventuallyEq F.family.natural (p := p) hp)
  have hfv : P.f p = F.family.f p := hf.eq_of_nhds
  have huv : P.U p = F.family.U p := hu.eq_of_nhds
  have hvv : P.Ubar p = F.family.Ubar p := hav.eq_of_nhds
  have hfD : fderiv ℝ P.f p = fderiv ℝ F.family.f p := hf.fderiv_eq
  have hvD : fderiv ℝ P.Ubar p = fderiv ℝ F.family.Ubar p := hav.fderiv_eq
  have hfx : radialPartial P.f p = partialY F.family.f p := by
    unfold radialPartial
    rw [hfD]
    exact radialPartial_natural (F.family.natural.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds hp))
  have hfe : parameterPartial P.f p = partialEta F.family.f p := by
    unfold parameterPartial
    rw [hfD]
    exact parameterPartial_natural (F.family.natural.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds hp))
  have hve : parameterPartial P.Ubar p = partialEta F.family.Ubar p := by
    unfold parameterPartial
    rw [hvD]
    exact parameterPartial_natural (F.family.natural.average_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds hp))
  change sourceQ P h p = _
  rw [sourceQ, logSlope, P.W_formula h hpN, hfv, huv, hvv, hfx, hfe, hve]
  rfl

theorem reference_p1_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {p : Point} (hη : p.2 ∈ Icc (-1 : ℝ) 1) (hX : 0 < p.1) (ha : p.1 ≤ 4 / Λ) :
    p1 (referenceProfiles F hΛ hδ hδT hP0) h p = NaturalEntrance.p1 F.family.f p := by
  let N := Input.ofNatural hΛ F.family
  let P := referenceProfiles F hΛ hδ hδT hP0
  have hY : Λ * p.1 ≤ 4 := by nlinarith [(le_div_iff₀ hΛ).mp ha]
  have hpoint : rescalePoint Λ p ∈ NaturalEntrance.entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hX.le, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hη⟩
  have hp := NaturalEntrance.entrance_mem_strip hpoint
  have hpN := reference_mem F hΛ hX.le hη
  have hfp : P.f p = F.family.f p := N.refF_eq_natural_initial δ ha
  have hsegment (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) p.1) :
      (x, p.2) ∈ domain Λ ∧ x ≤ 4 / Λ ∧ 0 ≤ x := by
    have hx' : x ∈ Icc (0 : ℝ) p.1 := (uIcc_of_le hX.le ▸ hx)
    exact ⟨NaturalProfile.domain_segment hΛ hp hx, hx'.2.trans ha, hx'.1⟩
  have hfun : primitive (P.angularSource h) p =
      ∫ x in (0 : ℝ)..p.1, (2 * x * F.family.f (x, p.2)) *
        NaturalEntrance.Sq h F.family.f F.family.U F.family.Ubar (x, p.2) := by
    unfold primitive
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    obtain ⟨hxn, hxa, hx0⟩ := hsegment x hx
    have hxnN := reference_mem F hΛ (p := (x, p.2)) hx0 hη
    have hpos := N.refF_pos δ hxnN hx0
    rw [angularSource_eq P hxnN hpos.ne', reference_sourceQ_natural F hΛ hδ hδT hP0 hxn hxa]
    change (2 * x * N.refF δ (x, p.2)) * _ = _
    rw [N.refF_eq_natural_initial δ hxa]
    rfl
  have hfn : ∀ x ∈ uIcc (0 : ℝ) p.1, F.family.f (x, p.2) ≠ 0 := by
    intro x hx
    obtain ⟨hxn, hxa, hx0⟩ := hsegment x hx
    exact (F.family.positive (x, p.2) hxn (mul_nonneg hΛ.le hx0)
      (by have hh := (le_div_iff₀ hΛ).mp hxa; linarith)).ne'
  have hreg := NaturalEntrance.p1_eq_scaled_regularAngularLag F.family.natural hΛ hp
    hX.ne' (NaturalAxisData.L_pos hsmall hη).ne' hfn
  change NaturalEntrance.p1 F.family.f p = p.1 * NaturalEntrance.regularAngularLag h
    F.family.f F.family.U F.family.Ubar p / NaturalAxisData.L h p.2 at hreg
  rw [hreg]
  change p.1 * (primitive (P.angularSource h) p / (p.1 * (2 * p.1 * P.f p))) /
      NaturalAxisData.L h p.2 = _
  rw [hfun, hfp]
  rfl

end ReferenceHistories

section ReferenceMonotonicity

open NaturalAxisBridge NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (E : NaturalEntrance.EntranceProfile d Λ C) (hΛ : 0 < Λ)

theorem natural_entrance_of_logTime {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (ht : (Input.ofNatural hΛ E.profile.family).logTime p.1 < rampLimit) :
    rescalePoint Λ p ∈ NaturalEntrance.entranceSet := by
  let N := Input.ofNatural hΛ E.profile.family
  have he : Real.exp (N.logTime p.1) < 41 / 40 := by
    simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
      Real.exp_lt_exp.mpr ht
  have hr := N.fromLog_scaled (N.logTime p.1, p.2)
  rw [N.fromLog_logTime hX] at hr
  change Λ * p.1 = 4 * Real.exp (N.logTime p.1) at hr
  exact ⟨⟨mul_nonneg hΛ.le hX.le, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hη⟩

theorem reference_radial_nonpos {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    radialPartial (referenceProfiles E.profile hΛ hδ hδT hP0).f p ≤ 0 := by
  let N := Input.ofNatural hΛ E.profile.family
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  have hp := reference_mem E.profile hΛ hX.le hη
  have hf : 0 < P.f p := N.refF_pos δ hp hX.le
  have hd := (radialPartial_hasDerivAt N.radialDomain P.f_smooth hp).log hf.ne'
  have hderiv : deriv (fun X => Real.log (N.refF δ (X, p.2))) p.1 =
      radialPartial P.f p / P.f p := hd.deriv
  have hdot : p.1 * radialPartial P.f p / P.f p ≤ 0 := by
    by_cases ht : N.logTime p.1 < rampLimit
    · have hs := N.same_radius_log_slope hδ hδT (p := p)
        (original_interval_interior hη) hX ht
      rw [hderiv] at hs
      have hen := natural_entrance_of_logTime E hΛ hX hη ht
      have hn := E.slope_positive p hen hX
      have hnat := radialPartial_natural
        (E.profile.family.natural.f_smooth.contDiffAt
          ((domain_isOpen Λ).mem_nhds (NaturalEntrance.entrance_mem_strip hen)))
      change radialPartial E.profile.family.f p = partialY E.profile.family.f p at hnat
      have hnonpos : p.1 * radialPartial N.f p / N.f p ≤ 0 := by
        change p.1 * radialPartial E.profile.family.f p / E.profile.family.f p ≤ 0
        rw [hnat]
        change 0 < -2 * p.1 * partialY E.profile.family.f p / E.profile.family.f p at hn
        have he : -2 * p.1 * partialY E.profile.family.f p / E.profile.family.f p =
            -2 * (p.1 * partialY E.profile.family.f p / E.profile.family.f p) := by ring
        rw [he] at hn
        linarith
      have hh := mul_nonpos_of_nonneg_of_nonpos (slopeCutoff_mem δ (N.logTime p.1)).1 hnonpos
      calc
        _ = p.1 * (radialPartial P.f p / P.f p) := by ring
        _ = _ := hs
        _ ≤ 0 := hh
    · have hc := slopeCutoff_zero hδ (hδT.le.trans (le_of_not_gt ht))
      have hz := (N.log_refF_hasDerivAt hδ hδT (p := p) (original_interval_interior hη) hX).deriv
      rw [hc, zero_mul, zero_div, hderiv] at hz
      rw [mul_div_assoc, hz, mul_zero]
  have hm : p.1 * radialPartial P.f p ≤ p.1 * 0 := by
    simpa only [zero_mul, mul_zero] using (div_le_iff₀ hf).mp hdot
  exact (mul_le_mul_iff_right₀ hX).mp hm

theorem reference_logSlope_le_one {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    logSlope (referenceProfiles E.profile hΛ hδ hδT hP0) p ≤ 1 := by
  by_cases hz : p.1 = 0
  · simp only [logSlope, hz, zero_mul, zero_div, add_zero, le_rfl]
  · have hx : 0 < p.1 := lt_of_le_of_ne hX (Ne.symm hz)
    have hd := reference_radial_nonpos E hΛ hδ hδT hP0 hx hη
    have hp := reference_mem E.profile hΛ hX hη
    have hf := (Input.ofNatural hΛ E.profile.family).refF_pos δ hp hX
    have hn := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hX hd) hf.le
    change p.1 * radialPartial (referenceProfiles E.profile hΛ hδ hδT hP0).f p /
      (referenceProfiles E.profile hΛ hδ hδT hP0).f p ≤ 0 at hn
    unfold logSlope
    linarith

theorem reference_antitone {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) {R η : ℝ} (_ : 0 ≤ R)
    (hη : η ∈ Icc (-1 : ℝ) 1) :
    AntitoneOn (fun X => (referenceProfiles E.profile hΛ hδ hδT hP0).f (X, η)) (Icc 0 R) := by
  let N := Input.ofNatural hΛ E.profile.family
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  have hp (X : ℝ) (hx : X ∈ Icc (0 : ℝ) R) : (X, η) ∈ N.radialDomain.carrier :=
    reference_mem E.profile hΛ (p := (X, η)) hx.1 hη
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R)
  · exact (radial_slice_continuous N.radialDomain P.f_smooth η).mono (fun X hx => hp X hx)
  · intro X hx
    exact (radialPartial_hasDerivAt N.radialDomain P.f_smooth (hp X (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro X hx
    have hXi : X ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hx
    rw [(radialPartial_hasDerivAt N.radialDomain P.f_smooth (hp X (interior_subset hx))).deriv]
    exact reference_radial_nonpos E hΛ hδ hδT hP0 (p := (X, η)) hXi.1 hη

end ReferenceMonotonicity

/-! ## A normalization chosen before the cutoff time controls pressure -/

section SmallPressure

variable {D : RadialDomain} (P : Profiles D)

theorem pressureJets_small {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ∈ Icc (0 : ℝ) 110) {Λ C K ε : ℝ} (hε : 0 < ε) (hK : 0 ≤ K)
    (hΛ : 1 + 1 / ε ≤ Λ) (hC : 1 + 220 * K ^ 2 / ε ≤ C)
    (hf : ∀ s ∈ Icc (0 : ℝ) p.1, |P.f (s, p.2)| ≤ K / C)
    (hfη : ∀ s ∈ Icc (0 : ℝ) p.1, |parameterPartial P.f (s, p.2)| ≤ K / C) :
    ‖pressureJets P Λ p‖ < ε := by
  have hΛ0 : 0 < Λ := by linarith [one_div_pos.mpr hε]
  have hC1 : 1 ≤ C := by
    have hn : 0 ≤ 220 * K ^ 2 / ε := by positivity
    linarith
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hinv : |1 / Λ| < ε := by
    rw [abs_of_pos (one_div_pos.mpr hΛ0), div_lt_iff₀ hΛ0]
    have hmul := (div_lt_iff₀ hε).mp (show 1 / ε < Λ by linarith)
    nlinarith
  have hsize : 220 * K ^ 2 / C ^ 2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hC0)).mpr
    have hb := (div_lt_iff₀ hε).mp (show 220 * K ^ 2 / ε < C by linarith)
    have hh : C ≤ C ^ 2 := by nlinarith
    nlinarith
  have hvnum : p.1 * K ^ 2 ≤ 220 * K ^ 2 :=
    mul_le_mul_of_nonneg_right (hX.2.trans (by norm_num)) (sq_nonneg K)
  have hpnum : (2 * p.1) * K ^ 2 ≤ 220 * K ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hX.2]) (sq_nonneg K)
  have hval : |P.pressure p - P.pressure0 p.2| < ε := by
    apply (pressure_increment_bound P hp hX.1 hK hC0 hf).trans_lt
    exact (div_le_div_of_nonneg_right hvnum (sq_nonneg C)).trans_lt hsize
  have hpar : |parameterPartial P.pressure p - deriv P.pressure0 p.2| < ε := by
    apply (pressure_parameter_increment_bound P hp hX.1 hK hC0 hf hfη).trans_lt
    exact (div_le_div_of_nonneg_right hpnum (sq_nonneg C)).trans_lt hsize
  have hdot : |p.1 * P.f p ^ 2| < ε := by
    have hd := pressure_dot_bound P hp hX.1 (by simpa only [Prod.eta] using hf p.1 ⟨hX.1, le_rfl⟩)
    rw [P.radialPartial_pressure hp] at hd
    exact hd.trans_lt ((div_le_div_of_nonneg_right hvnum (sq_nonneg C)).trans_lt hsize)
  apply (pi_norm_lt_iff (x := pressureJets P Λ p) hε).2
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hinv
  · exact hval
  · exact hpar
  · exact hdot

end SmallPressure

/-! ## Cone comparison for the actual reference histories -/

noncomputable def holdRegion : Set Point := Icc (0 : ℝ) 110 ×ˢ Icc (-1 : ℝ) 1

structure ReferenceBoundsOnHold {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : NaturalEntrance.CoefficientProfile d Λ C)
    (hΛ : 0 < Λ) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < ReferencePath.rampLimit)
    (hP0 : ContDiff ℝ ∞ P0) : Prop where
  source_lower : ∀ p ∈ holdRegion,
    (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
      sourceQ (referenceProfiles F hΛ hδ hδT hP0) h p
  logarithmic_slope : ∀ p ∈ holdRegion,
    logSlope (referenceProfiles F hΛ hδ hδT hP0) p ≤ 1
  first_positive : ∀ p ∈ holdRegion, 0 < p.1 →
    0 < p1 (referenceProfiles F hΛ hδ hδT hP0) h p
  cone_margin : ∀ p ∈ holdRegion, 4 / Λ ≤ p.1 →
    (9 / 4 : ℝ) < coneSize (referenceProfiles F hΛ hδ hδT hP0) h p
  at_hundred : ∀ η ∈ Icc (-1 : ℝ) 1,
    3 < p1 (referenceProfiles F hΛ hδ hδT hP0) h (100, η)

section ConeComparison

open NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
variable (E : NaturalEntrance.EntranceProfile d Λ C) (hΛ : 0 < Λ)
variable {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)
variable (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)

/-- This comparison uses only the actual primitive-defined stocks. The source
bounds are supplied below by the compact model and the concrete jet theorem. -/
theorem bounds_from_sources (hsmall : NaturalAxisData.SmallParameters h j) (hσ : 0 < σ)
    {K ν : ℝ} (hK : 0 < K) (hν : 0 < ν) (hC : 0 < C)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η)
    (hCbig : 18 * K / ((4 / Λ) * (ν / 2)) < C)
    (hq : ∀ p ∈ holdRegion,
      (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
        sourceQ (referenceProfiles E.profile hΛ hδ hδT hP0) h p)
    (hn : ∀ p ∈ holdRegion,
      |(referenceProfiles E.profile hΛ hδ hδT hP0).axialSource h p - NaturalAxisData.Z h j P0 p.2| < ν / 2)
    (hfbound : ∀ p ∈ holdRegion, |(referenceProfiles E.profile hΛ hδ hδT hP0).f p| ≤ K / C) :
    ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 := by
  let P := referenceProfiles E.profile hΛ hδ hδT hP0
  let N := Input.ofNatural hΛ E.profile.family
  have hq0 (p : Point) (hp : p ∈ holdRegion) : (12 / 5 : ℝ) ≤ sourceQ P h p := by
    have hg : 0 ≤ (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (NaturalAxisData.L_pos hsmall hp.2).le) hΛ.le) (NaturalAxisData.chi_bounds h j hσ p.2).1
    have hs := hq p hp
    change _ < sourceQ P h p at hs
    linarith
  have hpos (p : Point) (hp : p ∈ holdRegion) (hX : 0 < p.1) : 0 < p1 P h p := by
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hs := p1_lower_from_source P hdom hX h (NaturalAxisData.L_pos hsmall hp.2)
      (by norm_num : (0 : ℝ) ≤ 12 / 5)
      (fun s hsp => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, p.2)) hsp.1 hp.2) hsp.1)
      (reference_antitone E hΛ hδ hδT hP0 hX.le hp.2)
      (fun s hsp => hq0 (s, p.2) ⟨⟨hsp.1, hsp.2.trans hp.1.2⟩, hp.2⟩)
    exact (div_pos (mul_pos (by norm_num) hX)
      (mul_pos (by norm_num) (NaturalAxisData.L_pos hsmall hp.2))).trans_le hs
  refine ⟨hq, ?_, hpos, ?_, ?_⟩
  · intro p hp
    exact reference_logSlope_le_one E hΛ hδ hδT hP0 hp.1.1 hp.2
  · intro p hp haX
    have ha : (0 : ℝ) < 4 / Λ := by positivity
    have hX := ha.trans_le haX
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hL := NaturalAxisData.L_pos hsmall hp.2
    have hL1 := NaturalEntrance.L_le_one (NaturalAxisRange.ofSmall hsmall) p.2
    apply cone_margin_of_dichotomy (hpos p hp hX)
    by_cases hchi : 99 / 100 ≤ NaturalAxisData.chi h j σ p.2
    · left
      let q : ℝ := (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2
      have hqpos : 0 ≤ q := by
        dsimp [q]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le)
          (NaturalAxisData.chi_bounds h j hσ p.2).1
      have hqa : (23 / 10 : ℝ) * NaturalAxisData.L h p.2 ≤ q * (4 / Λ) := by
        have he : q * (4 / Λ) = (94 / 25 : ℝ) * NaturalAxisData.L h p.2 *
            NaturalAxisData.chi h j σ p.2 := by dsimp [q]; field_simp ; ring
        rw [he]
        nlinarith
      apply p1_preserves_lower P hdom hX h hL ha haX (by norm_num : (0 : ℝ) ≤ 23 / 10)
        hqpos hqa
        (fun s hsp => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, p.2)) hsp.1 hp.2) hsp.1)
        (reference_antitone E hΛ hδ hδT hP0 hX.le hp.2)
      · intro s hs
        have hsp : (s, p.2) ∈ holdRegion := ⟨⟨ha.le.trans hs.1, hs.2.trans hp.1.2⟩, hp.2⟩
        have hh := hq (s, p.2) hsp
        change q + 12 / 5 < sourceQ P h (s, p.2) at hh
        linarith
      · rw [reference_p1_natural E.profile hΛ hδ hδT hP0 hsmall (p := (4 / Λ, p.2)) hp.2 ha le_rfl]
        exact (E.profile.family.slope p.2 (original_interval_interior hp.2) hchi).le
    · right
      have hZ : ν < |NaturalAxisData.Z h j P0 p.2| := by
        by_contra hh
        exact hchi (hcut p.2 hp.2 (le_of_not_gt hh)).le
      have hdev := ns_deviation_bound P hdom hX h hL
        (Z := NaturalAxisData.Z h j P0 p.2) (ε := ν / 2)
        (fun s hsp => (hn (s, p.2) ⟨⟨hsp.1, hsp.2.trans hp.1.2⟩, hp.2⟩).le)
      have htri : |NaturalAxisData.Z h j P0 p.2| / NaturalAxisData.L h p.2 ≤
          |ns P h p| + (ν / 2) / NaturalAxisData.L h p.2 := by
        have ht := abs_sub (ns P h p) (ns P h p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2)
        have he : ns P h p - (ns P h p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2) =
            NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2 := by ring
        rw [he, abs_div, abs_of_pos hL] at ht
        linarith
      have hdiv : (|NaturalAxisData.Z h j P0 p.2| - ν / 2) / NaturalAxisData.L h p.2 ≤ |ns P h p| := by
        rw [sub_div]
        linarith
      have hns : ν / 2 ≤ |ns P h p| := by
        have hm := (div_le_iff₀ hL).mp hdiv
        have hu := mul_le_of_le_one_right (abs_nonneg (ns P h p)) hL1
        linarith
      exact p2_large_of_small_f P hX hp.1.2 h ha haX hK hC (div_pos hν (by norm_num))
        (N.refF_pos δ hdom hp.1.1) ((le_abs_self (P.f p)).trans (hfbound p hp)) hns hCbig
  · intro η hη
    apply p1_at_hundred_gt_three P (reference_mem E.profile hΛ (p := (100, η)) (by norm_num) hη)
      (NaturalAxisData.L_pos hsmall hη) (NaturalEntrance.L_le_one (NaturalAxisRange.ofSmall hsmall) η)
      (fun s hs => N.refF_pos δ (reference_mem E.profile hΛ (p := (s, η)) hs.1 hη) hs.1)
      (reference_antitone E hΛ hδ hδT hP0 (by norm_num : (0 : ℝ) ≤ 100) hη)
    intro s hs
    exact hq0 (s, η) ⟨⟨hs.1, hs.2.trans (by norm_num)⟩, hη⟩

end ConeComparison

/-! ## Passing from the bounded concrete jets to the sources -/

theorem holdRegion_scale {p : Point} (hp : p ∈ holdRegion) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (t * p.1, p.2) ∈ holdRegion := by
  refine ⟨⟨mul_nonneg ht.1 hp.1.1, ?_⟩, hp.2⟩
  exact (mul_le_of_le_one_left hp.1.1 ht.2).trans hp.1.2

theorem normalized_history_bounds {D : RadialDomain} (P : Profiles D)
    {Λ B j : ℝ}
    (hU : ∀ p ∈ holdRegion, |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B)
    (hUη : ∀ p ∈ holdRegion, |Λ * (parameterPartial P.U p - 4)| ≤ B)
    {p : Point} (hp : p ∈ holdRegion) (hpD : p ∈ D.carrier) :
    |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B ∧
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B := by
  constructor
  · exact average_error_bound P.U_smooth hpD (fun t ht => hU (t * p.1, p.2) (holdRegion_scale hp ht))
  · exact average_error_bound (parameterPartial_smooth D P.U_smooth) hpD
      (fun t ht => hUη (t * p.1, p.2) (holdRegion_scale hp ht))

/-- The source threshold is fixed before Λ and C. Every occurrence of a
history or derivative on the right is an actual operation on `P`. -/
theorem sourceQ_uniform_threshold {h j σ : ℝ} {P0 : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ M > 0, ∀ Λ : ℝ, M ≤ Λ → ∀ {D : RadialDomain} (P : Profiles D) (p : Point),
      ∀ Y θ φ e : ℝ,
        (Y, p.2) ∈ NaturalEntrance.entranceSet → θ ∈ Icc (0 : ℝ) 1 →
        (1 / 8 : ℝ) ≤ φ → φ ≤ B → |e| ≤ K / Λ →
        |Λ * (P.U p - NaturalAxisData.U j p.2)| ≤ B →
        |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B →
        |Λ * (average (parameterPartial P.U) p - 4)| ≤ B →
        |parameterPartial P.f p / P.f p - Λ * realGradient h j σ p.2| ≤ B →
        p.1 * radialPartial P.f p / P.f p = θ * Y *
          (NaturalEntrance.sourceJets v.epsilon_pos (NaturalEntrance.referencePair v) (Y, p.2) 1 + e) / φ →
        (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
          sourceQ P h p := by
  obtain ⟨M, hM, he⟩ := qModel_uniform_lower v hsmall hσ B hK
  refine ⟨M, hM, ?_⟩
  intro Λ hΛ D P p Y θ φ e hY hθ hφ hφB herr hu hv hvη hfη hslope
  have hΛ0 := hM.trans_le hΛ
  have hj : qJets P j σ h Λ φ p ∈ Metric.closedBall (0 : Fin 5 → ℝ) B :=
    qJets_bound P h j σ hB (by rw [abs_of_nonneg (by linarith)]; exact hφB) hu hv hvη hfη
  let sample : SourceParameter B := (⟨(Y, p.2), hY⟩, (⟨θ, hθ⟩, ⟨qJets P j σ h Λ φ p, hj⟩))
  have hh := he Λ hΛ sample e herr
  rw [sourceQ_model P h j σ hΛ0.ne' hφ p hslope]
  exact hh

/-! ## The ordered, constructed reference continuation -/

/-- Lemma 5.2 for the actual reference path and its literal histories.
The bounded jet constants and the scale threshold precede Λ; the pressure
normalization threshold precedes C; the short cutoff time is chosen last.
No source estimate, stock estimate, or cone condition is an input. -/
theorem exists_reference_bounds {h j σ ν : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) (hν : 0 < ν)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ ν →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    ∃ M > 0, ∀ Λ : ℝ, ∀ hΛ : 0 < Λ, M ≤ Λ →
      ∃ C₀ > 0, ∀ C : ℝ, C₀ ≤ C →
        ∃ E : NaturalEntrance.EntranceProfile d Λ C,
          ∃ r > 0, ∀ δ : ℝ, ∀ hδ : 0 < δ, δ < r →
            ∃ hδT : 2 * δ < ReferencePath.rampLimit,
              ReferenceBoundsOnHold E.profile hΛ hδ hδT hP0 := by
  obtain ⟨B, Mj, Kerr, hB, hMj, hKerr, hjets⟩ := ReferenceJetBounds.ordered_reference_bounds d hσ
  obtain ⟨Mq, hMq, hqmodel⟩ := sourceQ_uniform_threshold d.coefficients hsmall hσ
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hB.le) hKerr
  obtain ⟨Me, hMe, hentrance⟩ := NaturalEntrance.exists_entranceProfile d hsmall hσ hP0 hν hcut
  obtain ⟨τ, hτ, hnmodel⟩ := nModel_uniform_error h j hP0 B (ε := ν / 2) (div_pos hν (by norm_num))
  let M := max Mj (max Mq (max Me (1 + 1 / τ)))
  refine ⟨M, hMj.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ hM
  have hscalej : Mj ≤ Λ := (le_max_left _ _).trans hM
  have hrest : max Mq (max Me (1 + 1 / τ)) ≤ Λ := (le_max_right _ _).trans hM
  have hscaleq : Mq ≤ Λ := (le_max_left _ _).trans hrest
  have hrest' : max Me (1 + 1 / τ) ≤ Λ := (le_max_right _ _).trans hrest
  have hscalee : Me ≤ Λ := (le_max_left _ _).trans hrest'
  have hscalen : 1 + 1 / τ ≤ Λ := (le_max_right _ _).trans hrest'
  obtain ⟨K, hK, hjetΛ⟩ := hjets Λ hΛ hscalej
  let C₀ := max (d.normalizationThreshold Λ)
    (max (NaturalEntrance.entranceNormalization d Λ ν)
      (max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2)))))
  have hC₀ : 0 < C₀ := (Real.exp_pos _).trans_le (le_max_left _ _)
  refine ⟨C₀, hC₀, ?_⟩
  intro C hC
  have hnormal : d.normalizationThreshold Λ ≤ C := (le_max_left _ _).trans hC
  have htail : max (NaturalEntrance.entranceNormalization d Λ ν)
      (max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2)))) ≤ C :=
    (le_max_right _ _).trans hC
  have hentry : NaturalEntrance.entranceNormalization d Λ ν ≤ C := (le_max_left _ _).trans htail
  have hlast : max (1 + 220 * K ^ 2 / τ) (1 + 18 * K / ((4 / Λ) * (ν / 2))) ≤ C :=
    (le_max_right _ _).trans htail
  have hpressure : 1 + 220 * K ^ 2 / τ ≤ C := (le_max_left _ _).trans hlast
  have hcone : 18 * K / ((4 / Λ) * (ν / 2)) < C := by
    have hh := (le_max_right _ _).trans hlast
    linarith
  have hCpos : 0 < C := hC₀.trans_le hC
  obtain ⟨E⟩ := hentrance Λ hscalee C hentry
  obtain ⟨r, hr, hlastChoice⟩ := hjetΛ C hnormal E.profile
  refine ⟨E, r, hr, ?_⟩
  intro δ hδ hδr
  obtain ⟨hc, hj, hsamples⟩ := hlastChoice δ hδ hδr
  refine ⟨hc.length_bound, ?_⟩
  let P := referenceProfiles E.profile hΛ hδ hc.length_bound hP0
  have hJ : ReferenceJetBounds.JetBounds h j σ Λ C B K P.f P.U := hj
  have hB0 : 0 ≤ B := by linarith
  have hhistory (p : Point) (hp : p ∈ holdRegion) :
      |Λ * (P.Ubar p - NaturalAxisData.U j p.2)| ≤ B ∧
      |Λ * (average (parameterPartial P.U) p - 4)| ≤ B :=
    normalized_history_bounds P hJ.axial_value hJ.axial_parameter hp
      (reference_mem E.profile hΛ hp.1.1 hp.2)
  have hsourceq (p : Point) (hp : p ∈ holdRegion) :
      (47 / 50 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 12 / 5 <
        sourceQ P h p := by
    by_cases hnat : p.1 ≤ 4 / Λ
    · have hY : Λ * p.1 ≤ 4 := by nlinarith [(le_div_iff₀ hΛ).mp hnat]
      have hpoint : NaturalProfile.rescalePoint Λ p ∈ NaturalEntrance.entranceSet :=
        ⟨⟨mul_nonneg hΛ.le hp.1.1, by change Λ * p.1 ≤ 41 / 10; linarith⟩, hp.2⟩
      have he := reference_sourceQ_natural E.profile hΛ hδ hc.length_bound hP0
        (NaturalEntrance.entrance_mem_strip hpoint) hnat
      change sourceQ P h p = _ at he
      rw [he]
      have hh := E.source_lower p hpoint
      have hnonneg : 0 ≤ NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 :=
        mul_nonneg (mul_nonneg (NaturalAxisData.L_pos hsmall hp.2).le hΛ.le)
          (NaturalAxisData.chi_bounds h j hσ p.2).1
      nlinarith
    · obtain ⟨s⟩ := hsamples p hp (le_of_lt (lt_of_not_ge hnat))
      exact hqmodel Λ hscaleq P p s.Y s.theta s.phi s.error s.point_mem s.theta_mem
        s.phi_lower s.phi_upper s.error_bound (hJ.axial_value p hp)
        (hhistory p hp).1 (hhistory p hp).2 (hJ.log_parameter p hp) s.slope_eq
  have hsourcen (p : Point) (hp : p ∈ holdRegion) :
      |P.axialSource h p - NaturalAxisData.Z h j P0 p.2| < ν / 2 := by
    have hdom := reference_mem E.profile hΛ hp.1.1 hp.2
    have hx : |Λ * (p.1 * radialPartial P.U p)| ≤ B := by
      simpa only [mul_assoc] using hJ.axial_radial p hp
    have hv := nJets_bound P j hB0 (hJ.axial_value p hp) (hJ.axial_parameter p hp)
      (hhistory p hp).1 (hhistory p hp).2 hx
    have hz : ‖pressureJets P Λ p‖ < τ :=
      pressureJets_small P hdom hp.1 hτ hK.le hscalen hpressure
        (fun s hs => hJ.angular_value (s, p.2) ⟨⟨hs.1, hs.2.trans hp.1.2⟩, hp.2⟩)
        (fun s hs => hJ.angular_parameter (s, p.2) ⟨⟨hs.1, hs.2.trans hp.1.2⟩, hp.2⟩)
    rw [sourceN_model P h j hΛ.ne' p hp.2 hv]
    exact hnmodel (⟨p.2, hp.2⟩, ⟨nJets P j Λ p, hv⟩) (pressureJets P Λ p) hz
  exact bounds_from_sources E hΛ hδ hc.length_bound hP0 hsmall hσ hK hν hCpos hcut hcone
    hsourceq hsourcen hJ.angular_value

end NavierStokes.ReferenceBounds
