import NavierStokes.TransitionRamp
import NavierStokes.SharpPhaseJetAlgebra

noncomputable section

namespace NavierStokes.NaturalExitParameterJets

open Set NaturalProfile NaturalAxisCoefficients NaturalAxisBridge NaturalEntrance ReferencePath
open scoped ContDiff Topology

variable {h j σ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

def phi {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y, η)

def u {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.2 (Y, η)

def phiY {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.1 1 0 (Y, η)

def uY {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.2 1 0 (Y, η)

def scaledP1 {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  -2 * Y * (phiY d E Y η * (phi d E Y η)⁻¹)

def scaledNs {Λ C : ℝ} (E : CoefficientProfile d Λ C) (Y η : ℝ) : ℝ :=
  -2 * uY d E Y η

theorem radial_mem {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) :
    Y ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]

theorem radial_abs {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) : |Y| ≤ 5 := by
  exact abs_le.mpr ⟨by linarith [hY.1], by linarith [hY.2]⟩

theorem mixed_smooth (A : AxisCoefficientSpace.AxisSpace window d.coefficients.epsilon)
    (k : ℕ) {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) :
    ContDiffOn ℝ ∞ (fun η => AxisEvaluation.mixedSeries window d.coefficients.epsilon A k 0 (Y, η))
      parameterInterval := by
  intro η hη
  have hp : (Y, η) ∈ AxisEvaluation.strip window 20 := ⟨radial_mem hY, hη⟩
  exact ((AxisEvaluation.mixedSeries_smooth window d.coefficients.epsilon_pos A k 0
    hp).comp η (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

theorem phi_smooth {Λ C : ℝ} (E : CoefficientProfile d Λ C) {Y : ℝ}
    (hY : Y ∈ Icc (0 : ℝ) (41 / 10)) : ContDiffOn ℝ ∞ (phi d E Y) parameterInterval := by
  change ContDiffOn ℝ ∞ (fun η => AxisEvaluation.profile window d.coefficients.epsilon
    E.coefficients.1 (Y, η)) parameterInterval
  simpa only [AxisEvaluation.mixedSeries_zero] using mixed_smooth d E.coefficients.1 0 hY

theorem phi_lower (hσ : 0 < σ) {Λ C : ℝ}
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (E : CoefficientProfile d Λ C) {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10))
    {η : ℝ} (hη : η ∈ parameterInterval) : 1 / 8 < phi d E Y η :=
  coefficient_phi_lower d.coefficients hσ (profileErrorConstant_nonneg d) hscale
    E.coefficients E.norm_error hY.1 hY.2 hη

/-- Coefficient norm control gives a single constant before either large parameter. -/
theorem exists_mixed_jets (k N : ℕ) : ∃ B, 1 ≤ B ∧
    ∀ Λ C, ∀ E : CoefficientProfile d Λ C, ∀ Y ∈ Icc (0 : ℝ) (41 / 10),
      ∀ n ≤ N, ∀ η ∈ parameterInterval,
        |iteratedDeriv n (fun ξ => AxisEvaluation.mixedSeries window d.coefficients.epsilon
          E.coefficients.1 k 0 (Y, ξ)) η| ≤ B ∧
        |iteratedDeriv n (fun ξ => AxisEvaluation.mixedSeries window d.coefficients.epsilon
          E.coefficients.2 k 0 (Y, ξ)) η| ≤ B := by
  obtain ⟨B, hB, hb⟩ := TransitionRamp.finite_majorant
    (ReferenceJetBounds.jetConstant d.coefficients k) N
  refine ⟨B, hB, ?_⟩
  intro Λ C E Y hY n hn η hη
  simp_rw [AxisEvaluation.iteratedDeriv_eta window d.coefficients.epsilon_pos _ k 0 n
    (radial_mem hY) hη, Nat.zero_add]
  obtain ⟨h₁, h₂⟩ := ReferenceJetBounds.coefficient_jet_bound d.coefficients E.coefficients
    E.norm_ball k n (p := (Y, η)) (radial_abs hY)
  exact ⟨h₁.trans (hb n hn), h₂.trans (hb n hn)⟩

/-- Smooth functions of the positive normalized profile have parameter jets
bounded before choosing Λ or the amplitude C. -/
theorem exists_composed_jets (hσ : 0 < σ) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ))) (N : ℕ) :
    ∃ B ≥ 0, ∀ Λ,
      AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ →
      ∀ C, ∀ E : CoefficientProfile d Λ C, ∀ Y ∈ Icc (0 : ℝ) (41 / 10),
      ∀ n ≤ N, ∀ η ∈ parameterInterval,
        |iteratedDeriv n (fun ξ => g (phi d E Y ξ)) η| ≤ B := by
  obtain ⟨D, hD, hd⟩ := exists_mixed_jets d 0 N
  obtain ⟨B, hB, hb⟩ := TransitionRamp.compact_scalar_jets isOpen_Ioi
    (isCompact_Icc : IsCompact (Icc (1 / 8 : ℝ) D))
    (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1) hg N
  obtain ⟨M, hM, hm⟩ := TransitionRamp.finite_majorant (fun n => n.factorial * B * D ^ n) N
  refine ⟨M, zero_le_one.trans hM, ?_⟩
  intro Λ hscale C E Y hY n hn η hη
  have hj (i : ℕ) (hi : i ≤ N) : |iteratedDeriv i (phi d E Y) η| ≤ D := by
    change |iteratedDeriv i (fun η => AxisEvaluation.profile window d.coefficients.epsilon
      E.coefficients.1 (Y, η)) η| ≤ D
    simpa only [AxisEvaluation.mixedSeries_zero] using (hd Λ C E Y hY i hi η hη).1
  have hv : phi d E Y η ∈ Icc (1 / 8 : ℝ) D :=
    ⟨(phi_lower d hσ hscale E hY hη).le,
      (le_abs_self _).trans (hj 0 (Nat.zero_le N))⟩
  exact (TransitionRamp.local_composition_jet_bound parameterInterval_open isOpen_Ioi
    (phi_smooth d E hY) hg
    (fun ξ hξ => lt_trans (by norm_num) (phi_lower d hσ hscale E hY hξ)) hη n
    (fun i hi => hb i (hi.trans hn) _ hv)
    (fun i hi hin => (hj i (hin.trans hn)).trans (le_self_pow₀ hD (by omega)))).trans (hm n hn)

theorem inverse_smooth : ContDiffOn ℝ ∞ (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) :=
  contDiffOn_id.inv (fun _ hx => ne_of_gt hx)

theorem product_jets {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f parameterInterval)
    (hg : ContDiffOn ℝ ∞ g parameterInterval) {η : ℝ} (hη : η ∈ parameterInterval)
    (n : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i ≤ n, |iteratedDeriv i f η| ≤ A)
    (hb : ∀ i ≤ n, |iteratedDeriv i g η| ≤ B) :
    |iteratedDeriv n (fun ξ => f ξ * g ξ) η| ≤ 2 ^ n * A * B := by
  have he := SharpPhaseJetAlgebra.product_geometric_on parameterInterval_open hf hg hη n
    hA hB (by norm_num : (0 : ℝ) ≤ 1)
    (fun i hi => by simpa only [one_pow, mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] using ha i hi)
    (fun i hi => by simpa only [one_pow, mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      Real.norm_eq_abs] using hb i hi)
  simpa only [one_pow, mul_one, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using he

theorem exists_quotient_jets (hσ : 0 < σ) (N : ℕ) :
    ∃ B ≥ 0, ∀ Λ,
      AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ →
      ∀ C, ∀ E : CoefficientProfile d Λ C, ∀ Y ∈ Icc (0 : ℝ) (41 / 10),
      ∀ n ≤ N, ∀ η ∈ parameterInterval,
        |iteratedDeriv n (scaledP1 d E Y) η| ≤ B ∧
        |iteratedDeriv n (scaledNs d E Y) η| ≤ B := by
  obtain ⟨A, hA, ha⟩ := exists_mixed_jets d 1 N
  obtain ⟨B, hB, hb⟩ := exists_composed_jets d hσ inverse_smooth N
  obtain ⟨M, hM, hm⟩ := TransitionRamp.finite_majorant (fun n => 2 ^ n * A * B) N
  refine ⟨10 * M + 2 * A, by positivity, ?_⟩
  intro Λ hscale C E Y hY n hn η hη
  have hf := mixed_smooth d E.coefficients.1 1 hY
  have hg : ContDiffOn ℝ ∞ (fun ξ => (phi d E Y ξ)⁻¹) parameterInterval :=
    (phi_smooth d E hY).inv (fun ξ hξ =>
      (lt_trans (by norm_num) (phi_lower d hσ hscale E hY hξ)).ne')
  have hprod : |iteratedDeriv n (fun ξ => phiY d E Y ξ * (phi d E Y ξ)⁻¹) η| ≤ M :=
    (product_jets hf hg hη n (zero_le_one.trans hA) hB
      (fun i hi => (ha Λ C E Y hY i (hi.trans hn) η hη).1)
      (fun i hi => hb Λ hscale C E Y hY i (hi.trans hn) η hη)).trans (hm n hn)
  have hconst : |-2 * Y| ≤ (10 : ℝ) := by
    rw [abs_mul, abs_of_nonneg hY.1]
    norm_num
    linarith [hY.2]
  constructor
  · change |iteratedDeriv n (fun ξ => -2 * Y * (phiY d E Y ξ * (phi d E Y ξ)⁻¹)) η| ≤ _
    rw [iteratedDeriv_const_mul_field, abs_mul]
    exact (mul_le_mul hconst hprod (abs_nonneg _) (by norm_num)).trans (by linarith)
  · change |iteratedDeriv n (fun ξ => -2 * uY d E Y ξ) η| ≤ _
    rw [iteratedDeriv_const_mul_field, abs_mul]
    have hv := (ha Λ C E Y hY n hn η hη).2
    change |iteratedDeriv n (uY d E Y) η| ≤ A at hv
    norm_num
    nlinarith

theorem p1_eq_scaled (hσ : 0 < σ) {Λ C : ℝ} (hC : 0 < C)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (E : CoefficientProfile d Λ C) {X η : ℝ}
    (hY : Λ * X ∈ Icc (0 : ℝ) (41 / 10)) (hη : η ∈ parameterInterval) :
    p1 E.family.f (X, η) = scaledP1 d E (Λ * X) η := by
  have hp : (X, η) ∈ domain Λ := ⟨radial_mem hY, hη⟩
  have hφ : AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1
      (rescalePoint Λ (X, η)) ≠ 0 :=
    (lt_trans (by norm_num) (phi_lower d hσ hscale E hY hη)).ne'
  have he := angularProfile_radial_log_derivative
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos E.coefficients.1)
    hp (realAmplitude_pos h j σ Λ hC η).ne' hφ
  rw [partialY_profile window d.coefficients.epsilon_pos _ hp] at he
  rw [E.f_eq]
  change -2 * X * partialY (angularProfile (realAmplitude h j σ Λ C) Λ
    (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1)) (X, η) /
      angularProfile (realAmplitude h j σ Λ C) Λ
        (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1) (X, η) = _
  rw [show -2 * X * partialY (angularProfile (realAmplitude h j σ Λ C) Λ
    (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1)) (X, η) /
      angularProfile (realAmplitude h j σ Λ C) Λ
        (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1) (X, η) =
      -2 * (X * partialY (angularProfile (realAmplitude h j σ Λ C) Λ
        (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1)) (X, η) /
        angularProfile (realAmplitude h j σ Λ C) Λ
          (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1) (X, η)) by ring]
  rw [he]
  simp only [scaledP1, phiY, phi, rescalePoint, div_eq_mul_inv]
  ring

theorem ns_eq_scaled {Λ C : ℝ} (hΛ : Λ ≠ 0) (E : CoefficientProfile d Λ C) {X η : ℝ}
    (hY : Λ * X ∈ Icc (0 : ℝ) (41 / 10)) (hη : η ∈ parameterInterval) :
    ns E.family.U (X, η) = scaledNs d E (Λ * X) η := by
  have hp : (X, η) ∈ domain Λ := ⟨radial_mem hY, hη⟩
  rw [E.U_eq, ns, axialField_partialY d.coefficients.epsilon_pos hΛ E.coefficients hp,
    partialY_profile window d.coefficients.epsilon_pos _ hp]
  rfl

/-- All five normalized entrance quantities have every fixed parameter jet
bounded by constants chosen before both Λ and C, on the full rectangle. -/
theorem exists_exit_jets (hσ : 0 < σ) (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ Λ, 0 < Λ →
      AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ →
      ∀ C, 0 < C → ∀ E : CoefficientProfile d Λ C,
      ∀ X, Λ * X ∈ Icc (0 : ℝ) (41 / 10) → ∀ n ≤ N, ∀ η ∈ parameterInterval,
        |iteratedDeriv n (fun ξ => E.family.phi (Λ * X, ξ)) η| ≤ B ∧
        |iteratedDeriv n (fun ξ => Real.log (E.family.phi (Λ * X, ξ))) η| ≤ B ∧
        |iteratedDeriv n (fun ξ => E.family.u (Λ * X, ξ)) η| ≤ B ∧
        |iteratedDeriv n (fun ξ => p1 E.family.f (X, ξ)) η| ≤ B ∧
        |iteratedDeriv n (fun ξ => ns E.family.U (X, ξ)) η| ≤ B := by
  obtain ⟨A, hA, ha⟩ := exists_mixed_jets d 0 N
  obtain ⟨B, hB, hb⟩ := exists_composed_jets d hσ TransitionRamp.log_smooth_positive N
  obtain ⟨D, hD, hd⟩ := exists_quotient_jets d hσ N
  refine ⟨A + B + D, by linarith, ?_⟩
  intro Λ hΛ hscale C hC E X hY n hn η hη
  obtain ⟨hp, hu⟩ := ha Λ C E (Λ * X) hY n hn η hη
  simp only [AxisEvaluation.mixedSeries_zero, ← E.phi_eq, ← E.u_eq] at hp hu
  have hl := hb Λ hscale C E (Λ * X) hY n hn η hη
  change |iteratedDeriv n (fun ξ => Real.log
    (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Λ * X, ξ))) η| ≤ B at hl
  rw [← E.phi_eq] at hl
  obtain ⟨h₁, h₂⟩ := hd Λ hscale C E (Λ * X) hY n hn η hη
  have he₁ : (fun ξ => p1 E.family.f (X, ξ)) =ᶠ[𝓝 η] scaledP1 d E (Λ * X) :=
    Filter.eventually_of_mem (parameterInterval_open.mem_nhds hη)
      (fun ξ hξ => p1_eq_scaled d hσ hC hscale E hY hξ)
  have he₂ : (fun ξ => ns E.family.U (X, ξ)) =ᶠ[𝓝 η] scaledNs d E (Λ * X) :=
    Filter.eventually_of_mem (parameterInterval_open.mem_nhds hη)
      (fun ξ hξ => ns_eq_scaled d hΛ.ne' E hY hξ)
  rw [he₁.iteratedDeriv_eq n, he₂.iteratedDeriv_eq n]
  exact ⟨hp.trans (by linarith), hl.trans (by linarith), hu.trans (by linarith),
    h₁.trans (by linarith), h₂.trans (by linarith)⟩

end NavierStokes.NaturalExitParameterJets
