import NavierStokes.NaturalExitParameterJets

noncomputable section

namespace NavierStokes.NaturalExitBounds

open Set NaturalProfile NaturalAxisCoefficients NaturalAxisBridge NaturalEntrance
open scoped ContDiff Topology

/-- A uniformly positive regular source supplies a quantitative derivative
bound even at arbitrarily small positive radii. -/
theorem derivative_le_of_regular_source {f : ℝ → ℝ} {R L s μ : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hL1 : L ≤ 1) (hs : 0 < s) (hμ : 0 < μ)
    (hf : ∀ x ∈ Icc (0 : ℝ) R, ContDiffAt ℝ 2 f x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) R, μ ≤ f x)
    (hsource : ∀ x ∈ Ioo (0 : ℝ) R,
      s ≤ -2 * L * (x * deriv (deriv f) x + 2 * deriv f x) / f x) :
    deriv f R ≤ -(s * μ) / 4 := by
  let H : ℝ → ℝ := fun x => x ^ 2 * deriv f x + (s * μ / 4) * x ^ 2
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) R) :
      HasDerivAt H (x * (x * deriv (deriv f) x + 2 * deriv f x) + (s * μ / 2) * x) x := by
    convert! (radial_flux_hasDerivAt (hf x hx)).add
      (((hasDerivAt_id x).fun_pow 2).const_mul (s * μ / 4)) using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]
    ring
  have ha : AntitoneOn H (Icc (0 : ℝ) R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi : x ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using hx
      have hxc : x ∈ Icc (0 : ℝ) R := ⟨hxi.1.le, hxi.2.le⟩
      rw [(hd x hxc).deriv]
      have hfx : 0 < f x := hμ.trans_le (hpos x hxc)
      have hnum := (le_div_iff₀ hfx).mp (hsource x hxi)
      have hsm := mul_le_mul_of_nonneg_left (hpos x hxc) hs.le
      have hneg : x * deriv (deriv f) x + 2 * deriv f x ≤ 0 := by
        nlinarith [mul_pos hs hfx]
      have hweight := mul_nonneg (sub_nonneg.mpr hL1) (neg_nonneg.mpr hneg)
      have hb : x * deriv (deriv f) x + 2 * deriv f x + s * μ / 2 ≤ 0 := by
        nlinarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hxi.1.le hb]
  have hv := ha (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl, hR.le⟩)
    (show R ∈ Icc 0 R from ⟨hR.le, le_rfl⟩) hR.le
  dsimp only [H] at hv
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, zero_add] at hv
  have hsq : 0 < R ^ 2 := sq_pos_of_pos hR
  nlinarith

variable {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

def lowerConstant : ℝ := 5 / (32 * profileBound d.coefficients)

theorem lowerConstant_pos : 0 < lowerConstant d := by
  unfold lowerConstant
  exact div_pos (by norm_num) (mul_pos (by norm_num) (profileBound_pos d.coefficients))

theorem p1_div_radius_lower (hsmall : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    {Λ C : ℝ} (hΛ : 0 < Λ) (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (E : EntranceProfile d Λ C) {X η : ℝ} (hX : 0 < X)
    (hY : Λ * X ≤ 41 / 10) (hη : η ∈ Icc (-1 : ℝ) 1) :
    lowerConstant d ≤ p1 E.profile.family.f (X, η) / X := by
  let F := E.profile
  let a := realAmplitude h j σ Λ C η
  have ha : 0 < a := realAmplitude_pos h j σ Λ hC η
  have hseg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) X) :
      rescalePoint Λ (x, η) ∈ entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hx.1, (mul_le_mul_of_nonneg_left hx.2 hΛ.le).trans hY⟩, hη⟩
  have hreg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) X) :
      ContDiffAt ℝ 2 (fun y => F.family.f (y, η)) x :=
    (((F.family.natural.f_smooth.contDiffAt ((domain_isOpen Λ).mem_nhds
      (entrance_mem_strip (hseg x hx)))).comp x
        (contDiffAt_id.prodMk contDiffAt_const))).of_le (TransitionRamp.nat_le_infty 2)
  have hlo (x : ℝ) (hx : x ∈ Icc (0 : ℝ) X) : a / 8 ≤ F.family.f (x, η) := by
    have hv := NaturalExitParameterJets.phi_lower d hσ hscale F (hseg x hx).1
      (original_interval_interior hη)
    change 1 / 8 < NaturalExitParameterJets.phi d F (Λ * x) η at hv
    rw [F.f_eq]
    change a / 8 ≤ a * NaturalExitParameterJets.phi d F (Λ * x) η
    nlinarith
  have hL := NaturalAxisRange.L_pos hsmall hη
  have hs (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) X) :
      (5 / 2 : ℝ) ≤ -2 * NaturalAxisData.L h η *
        (x * deriv (deriv (fun y => F.family.f (y, η))) x +
          2 * deriv (fun y => F.family.f (y, η)) x) / F.family.f (x, η) := by
    have hxc : x ∈ Icc (0 : ℝ) X := ⟨hx.1.le, hx.2.le⟩
    have hsrc := E.source_lower (x, η) (hseg x hxc)
    have hχ : 0 ≤ NaturalAxisData.chi h j σ η := by
      unfold NaturalAxisData.chi
      positivity
    have hn : 0 ≤ (19 / 20 : ℝ) * NaturalAxisData.L h η * Λ * NaturalAxisData.chi h j σ η :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL.le) hΛ.le) hχ
    have hb : (5 / 2 : ℝ) ≤ Sq h F.family.f F.family.U F.family.Ubar (x, η) := by
      change _ < Sq h F.family.f F.family.U F.family.Ubar (x, η) at hsrc
      linarith
    have he : Sq h F.family.f F.family.U F.family.Ubar (x, η) =
        -2 * NaturalAxisData.L h η * radialDifferential 2 F.family.f (x, η) /
          F.family.f (x, η) := Sq_eq_radial F.family.natural
      (entrance_mem_strip (hseg x hxc))
      (lt_of_lt_of_le (by positivity : 0 < a / 8) (hlo x hxc)).ne'
    rw [he] at hb
    simpa only [radialDifferential, partialY, iteratedDeriv_succ, iteratedDeriv_zero,
      Nat.cast_ofNat] using hb
  have hd := derivative_le_of_regular_source hX hL (L_le_one hsmall η)
    (by norm_num : (0 : ℝ) < 5 / 2) (by positivity : 0 < a / 8) hreg hlo hs
  have hfx : 0 < F.family.f (X, η) :=
    lt_of_lt_of_le (by positivity : 0 < a / 8) (hlo X ⟨hX.le, le_rfl⟩)
  have hB := profileBound_pos d.coefficients
  have hu : F.family.f (X, η) ≤ a * profileBound d.coefficients := by
    have hv := coefficient_profile_le d.coefficients F.coefficients F.norm_ball
      (p := rescalePoint Λ (X, η)) (entrance_abs_le_five (hseg X ⟨hX.le, le_rfl⟩))
    rw [F.f_eq]
    change a * _ ≤ a * profileBound d.coefficients
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hv) ha.le
  have he : p1 F.family.f (X, η) / X =
      -2 * deriv (fun y => F.family.f (y, η)) X / F.family.f (X, η) := by
    unfold p1 partialY
    field_simp
  change lowerConstant d ≤ p1 F.family.f (X, η) / X
  rw [he]
  apply (le_div_iff₀ hfx).mpr
  unfold lowerConstant
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 32 * profileBound d.coefficients)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hd hB.le]

/-- The complete quantitative natural-exit conclusions, with the parameter
jet constants kept outside the choices of scale and normalization. -/
structure Estimates {Λ C : ℝ} (E : EntranceProfile d Λ C) (B : ℕ → ℝ) : Prop where
  phi_lower : ∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ η ∈ Icc (-1 : ℝ) 1,
    1 / 8 < E.profile.family.phi (Y, η)
  source_lower : ∀ p, rescalePoint Λ p ∈ entranceSet →
    (19 / 20 : ℝ) * NaturalAxisData.L h p.2 * Λ * NaturalAxisData.chi h j σ p.2 + 5 / 2 <
      Sq h E.profile.family.f E.profile.family.U E.profile.family.Ubar p
  p1_lower : ∀ X η, 0 < X → Λ * X ≤ 41 / 10 → η ∈ Icc (-1 : ℝ) 1 →
    lowerConstant d ≤ p1 E.profile.family.f (X, η) / X
  p1_positive_upper : ∀ X η, 0 < X → Λ * X ≤ 41 / 10 → η ∈ Icc (-1 : ℝ) 1 →
    0 < p1 E.profile.family.f (X, η) ∧ p1 E.profile.family.f (X, η) ≤ B 0
  ns_error : ∀ p, rescalePoint Λ p ∈ entranceSet →
    |ns E.profile.family.U p - NaturalAxisData.Z h j P0 p.2 / NaturalAxisData.L h p.2| ≤
      AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 * profileErrorConstant d / Λ
  cone_margin : ∀ η ∈ Icc (-1 : ℝ) 1,
    2 + 1 / 4 < coneSize E.profile.family.f E.profile.family.U (4 / Λ, η)
  parameter_jets : ∀ m X, Λ * X ∈ Icc (0 : ℝ) (41 / 10) → ∀ η ∈ Icc (-1 : ℝ) 1,
    |iteratedDeriv m (fun ξ => E.profile.family.phi (Λ * X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => Real.log (E.profile.family.phi (Λ * X, ξ))) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => E.profile.family.u (Λ * X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => p1 E.profile.family.f (X, ξ)) η| ≤ B m ∧
    |iteratedDeriv m (fun ξ => ns E.profile.family.U (X, ξ)) η| ≤ B m

/-- Proposition `axis:exit` on the full printed h,j range. The lower slope
constant and every fixed parameter-jet constant are chosen before Λ and C;
the normalization threshold retains the existing constructive entrance order. -/
theorem exists_exit (hsmall : NaturalAxisRange.Parameters h j) (hσ : 0 < σ)
    (hP0 : ContDiff ℝ ∞ P0) {δ : ℝ} (hδ : 0 < δ)
    (hcut : ∀ η ∈ Icc (-1 : ℝ) 1, |NaturalAxisData.Z h j P0 η| ≤ δ →
      99 / 100 < NaturalAxisData.chi h j σ η) :
    0 < lowerConstant d ∧ ∃ B : ℕ → ℝ, (∀ m, 1 ≤ B m) ∧
      ∃ M > 0, ∀ Λ ≥ M, ∀ C, entranceNormalization d Λ δ ≤ C →
        ∃ E : EntranceProfile d Λ C, Estimates d E B := by
  classical
  have hall := fun m => NaturalExitParameterJets.exists_exit_jets d hσ m
  choose B hB hb using hall
  obtain ⟨M, hM, hE⟩ := exists_entranceProfile d hsmall hσ hP0 hδ hcut
  refine ⟨lowerConstant_pos d, B, hB,
    max M (AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d)),
    hM.trans_le (le_max_left _ _), ?_⟩
  intro Λ hΛ C hC
  have hΛM : M ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛpos : 0 < Λ := hM.trans_le hΛM
  have hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have hCnormal : d.normalizationThreshold Λ ≤ C :=
    (entranceNormalization_ge d hΛpos hδ).trans hC
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hCnormal
  obtain ⟨E⟩ := hE Λ hΛM C hC
  refine ⟨E, ?_⟩
  refine ⟨?_, E.source_lower, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y hY η hη
    rw [E.profile.phi_eq]
    exact NaturalExitParameterJets.phi_lower d hσ hscale E.profile hY (original_interval_interior hη)
  · intro X η hX hY hη
    exact p1_div_radius_lower d hsmall hσ hΛpos hCpos hscale E hX hY hη
  · intro X η hX hY hη
    have hp : rescalePoint Λ (X, η) ∈ entranceSet :=
      ⟨⟨mul_nonneg hΛpos.le hX.le, hY⟩, hη⟩
    have hj := (hb 0 Λ hΛpos hscale C hCpos E.profile X hp.1 0 le_rfl
      η (original_interval_interior hη)).2.2.2.1
    exact ⟨E.slope_positive (X, η) hp hX, (le_abs_self _).trans hj⟩
  · intro p hp
    rw [E.profile.U_eq]
    exact NaturalEntrance.ns_error d.coefficients hΛpos (profileErrorConstant_nonneg d)
      E.profile.coefficients E.profile.norm_error hp (NaturalAxisRange.L_pos hsmall hp.2).ne'
  · intro η hη
    convert E.cone_margin η hη using 1
    norm_num
  · intro m X hY η hη
    exact hb m Λ hΛpos hscale C hCpos E.profile X hY m le_rfl
      η (original_interval_interior hη)

/-- The bounds in the paper's original regular-integral coordinates. -/
theorem Estimates.regular_lag_bounds {Λ C : ℝ} {E : EntranceProfile d Λ C} {B : ℕ → ℝ}
    (H : Estimates d E B) (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    {X η : ℝ} (hX : 0 < X) (hY : X ≤ (41 / 10) / Λ) (hη : η ∈ Icc (-1 : ℝ) 1) :
    let Q := regularAngularLag h E.profile.family.f E.profile.family.U E.profile.family.Ubar (X, η)
    let N := regularAxialLag h E.profile.family.U E.profile.family.Ubar E.profile.family.Pi (X, η)
    lowerConstant d ≤ (X * Q / NaturalAxisData.L h η) / X ∧
    0 < X * Q / NaturalAxisData.L h η ∧ X * Q / NaturalAxisData.L h η ≤ B 0 ∧
    |N / NaturalAxisData.L h η - NaturalAxisData.Z h j P0 η / NaturalAxisData.L h η| ≤
      AxisEvaluation.jetBound d.coefficients.epsilon 5 1 0 * profileErrorConstant d / Λ := by
  dsimp only
  have hYX : Λ * X ≤ 41 / 10 := by
    simpa only [mul_comm] using (le_div_iff₀ hΛ).mp hY
  have hp : rescalePoint Λ (X, η) ∈ entranceSet :=
    ⟨⟨mul_nonneg hΛ.le hX.le, hYX⟩, hη⟩
  have he := (E.regular_lag_coordinates hsmall hΛ hp hX).1
  have hn : ns E.profile.family.U (X, η) =
      regularAxialLag h E.profile.family.U E.profile.family.Ubar E.profile.family.Pi (X, η) /
        NaturalAxisData.L h η := ns_eq_scaled_regularAxialLag E.profile.family.natural hΛ
      (entrance_mem_strip hp) hX.ne' (NaturalAxisRange.L_pos hsmall hη).ne'
  change p1 E.profile.family.f (X, η) = X * regularAngularLag h E.profile.family.f
    E.profile.family.U E.profile.family.Ubar (X, η) / NaturalAxisData.L h η at he
  rw [← he, ← hn]
  exact ⟨H.p1_lower X η hX hYX hη, (H.p1_positive_upper X η hX hYX hη).1,
    (H.p1_positive_upper X η hX hYX hη).2, H.ns_error (X, η) hp⟩

/-- The analytic inputs and cutoff are constructed from the ideal-prefix
pressure datum; no separate analytic-family or exit estimate is assumed. -/
theorem ideal_prefix_exit {h j : ℝ} (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap amplitude : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hA : 2 ≤ amplitude)
    (hg : ∀ y ≤ 0, g y = amplitude ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      ∃ d : AnalyticInputs h j σ (PressureDatum.pressure g a),
        0 < lowerConstant d ∧ ∃ B : ℕ → ℝ, (∀ m, 1 ≤ B m) ∧
          ∃ M > 0, ∀ Λ ≥ M, ∀ C, entranceNormalization d Λ δ ≤ C →
            ∃ E : EntranceProfile d Λ C, Estimates d E B := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ := ideal_prefix_analytic_inputs hsmall hp hA hg ha
  exact ⟨δ, σ, hδ, hσ, d,
    exists_exit d hsmall hσ (PressureDatum.pressure_contDiff hp) hδ hcut⟩

end NavierStokes.NaturalExitBounds
