import NavierStokes.AxisJointAnalytic
import NavierStokes.NaturalEntrance

/-! # Joint analyticity of the constructed natural-axis solution

The coefficient witness retained by `CoefficientProfile` identifies the actual
nonlinear solution with convergent analytic radial sums. Its pressure integral
identifies the same analytic primitive, so no analyticity of the output is assumed.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace NavierStokes.NaturalEntrance

open AxisCoefficientSpace NaturalProfile NaturalAxisBridge NaturalAxisCoefficients

/-- All four scaled profiles of the actual nonlinear fixed point are jointly
real analytic on the common open axis rectangle. -/
theorem CoefficientProfile.scaled_analytic {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hΛ : 0 ≤ Λ) (hC : d.normalizationThreshold Λ ≤ C) :
    AnalyticOnNhd ℝ F.family.phi (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.u (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.average (AxisEvaluation.strip window 20) ∧
    AnalyticOnNhd ℝ F.family.pressure (AxisEvaluation.strip window 20) := by
  have hφ : AnalyticOnNhd ℝ F.family.phi (AxisEvaluation.strip window 20) := by
    rw [F.phi_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  have hu : AnalyticOnNhd ℝ F.family.u (AxisEvaluation.strip window 20) := by
    rw [F.u_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  have hB : AnalyticOnNhd ℝ F.family.average (AxisEvaluation.strip window 20) := by
    rw [F.average_eq]
    exact AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _
  refine ⟨hφ, hu, hB, ?_⟩
  obtain ⟨a, _, harad, havalue⟩ := d.uniformAmplitude Λ hΛ C hC
  have heq : (AxisEvaluation.strip window 20).EqOn
      (AxisEvaluation.profile window d.coefficients.epsilon
        (pressureCoefficient window d.coefficients.epsilon_pos a F.coefficients.1))
      F.family.pressure := by
    intro p hp
    rw [pressure_integral window d.coefficients.epsilon_pos a F.coefficients.1 harad hp,
      F.scaled.pressure_integral p hp, F.phi_eq,
      havalue p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  exact (analyticOnNhd_congr (AxisEvaluation.strip_isOpen window 20) heq).mp
    (AxisJointAnalytic.profile_analyticOnNhd window d.coefficients.epsilon_pos _)

theorem amplitude_analytic {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) :
    AnalyticOnNhd ℝ (realAmplitude h j σ Λ C) (Ioo window.left window.right) := by
  intro η hη
  have hc := d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)
  have hr : AnalyticAt ℝ (realPhase h j σ) η := by
    have ht : AnalyticAt ℝ (fun x : ℝ => (axisPhase h j σ (x : ℂ)).re) η :=
      (Complex.reCLM.analyticAt _).comp_of_eq
        (hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt η)) rfl
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using ht
  exact ((analyticAt_const.mul hr).rexp).mul analyticAt_const

theorem pullback_analytic {F : ℝ × ℝ → ℝ}
    (hF : AnalyticOnNhd ℝ F (AxisEvaluation.strip window 20)) (Λ : ℝ) :
    AnalyticOnNhd ℝ (pullback Λ F) (domain Λ) := by
  intro p hp
  exact (hF (rescalePoint Λ p) hp).comp
    ((analyticAt_const.mul analyticAt_fst).prod analyticAt_snd)

theorem affineProfile_analytic {b : ℝ → ℝ}
    (hb : AnalyticOnNhd ℝ b (Ioo window.left window.right))
    {F : ℝ × ℝ → ℝ} (hF : AnalyticOnNhd ℝ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) : AnalyticOnNhd ℝ (affineProfile b c Λ F) (domain Λ) := by
  intro p hp
  exact ((hb p.2 hp.2).comp analyticAt_snd).add
    (analyticAt_const.mul (pullback_analytic hF Λ p hp))

theorem angularProfile_analytic {a : ℝ → ℝ}
    (ha : AnalyticOnNhd ℝ a (Ioo window.left window.right))
    {Φ : ℝ × ℝ → ℝ} (hΦ : AnalyticOnNhd ℝ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) : AnalyticOnNhd ℝ (angularProfile a Λ Φ) (domain Λ) := by
  intro p hp
  exact ((ha p.2 hp.2).comp analyticAt_snd).mul (pullback_analytic hΦ Λ p hp)

/-- The unscaled angular velocity, axial velocity, average and pressure of
the actual nonlinear solution are jointly analytic in `(X,η)`. -/
theorem CoefficientProfile.natural_analytic {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (F : CoefficientProfile d Λ C)
    (hΛ : 0 ≤ Λ) (hC : d.normalizationThreshold Λ ≤ C)
    (hP0 : AnalyticOnNhd ℝ P0 (Ioo window.left window.right)) :
    AnalyticOnNhd ℝ F.family.f (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.U (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.Ubar (domain Λ) ∧
    AnalyticOnNhd ℝ F.family.Pi (domain Λ) := by
  obtain ⟨hφ, hu, hB, hP⟩ := F.scaled_analytic hΛ hC
  have hU : AnalyticOnNhd ℝ (NaturalAxisData.U j) (Ioo window.left window.right) := by
    intro η _
    exact (analyticAt_const.mul analyticAt_id).add analyticAt_const
  exact ⟨angularProfile_analytic (amplitude_analytic d Λ C) hφ Λ,
    affineProfile_analytic hU hu (1 / Λ) Λ,
    affineProfile_analytic hU hB (1 / Λ) Λ,
    affineProfile_analytic hP0 hP (1 / Λ) Λ⟩

/-- Actual pressure data supplies its analyticity; it is not an additional
hypothesis of the end-to-end natural-axis theorem. -/
theorem pressureDatum_analytic {g a : ℝ → ℝ} {cap : ℝ} (hp : PressureDatum.Admissible g a cap) :
    AnalyticOnNhd ℝ (PressureDatum.pressure g a) univ := by
  intro η _
  have hc := PressureDatum.complexPressure_analytic hp (η : ℂ) (PressureDatum.real_mem_strip η)
  have hr : AnalyticAt ℝ (fun x : ℝ => (PressureDatum.complexPressure g a (x : ℂ)).re) η :=
    (Complex.reCLM.analyticAt _).comp_of_eq
      (hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt η)) rfl
  simpa only [PressureDatum.complexPressure_ofReal, Complex.ofReal_re] using hr

/-- One common neighborhood of the printed closed scaled rectangle works
for every scale and amplitude covered by the natural-axis construction. -/
theorem printed_rectangle_subset_strip :
    Icc (0 : ℝ) (41 / 10) ×ˢ Icc (-1 : ℝ) 1 ⊆ AxisEvaluation.strip window 20 := by
  intro p hp
  exact ⟨by constructor <;> linarith [hp.1.1, hp.1.2], original_interval_interior hp.2⟩

/-- The literal common-neighborhood assertion for the printed natural-axis
construction. All input data, the cutoff and the nonlinear coefficient
solution are constructed. The same open scaled rectangle works for every
sufficiently large scale and every allowed amplitude normalization. -/
theorem exists_common_joint_analytic_profiles {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ : ℝ, 0 < δ ∧ 0 < σ ∧
      (∀ η ∈ Icc (-1 : ℝ) 1,
        |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
          99 / 100 < NaturalAxisData.chi h j σ η) ∧
      ∃ d : AnalyticInputs h j σ (PressureDatum.pressure g a),
        ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∃ Ω : Set (ℝ × ℝ), IsOpen Ω ∧
          Icc (0 : ℝ) (41 / 10) ×ˢ Icc (-1 : ℝ) 1 ⊆ Ω ∧
          ∀ Λ : ℝ, Λ₀ ≤ Λ → ∀ C : ℝ, d.normalizationThreshold Λ ≤ C →
            ∃ F : CoefficientProfile d Λ C,
              AnalyticOnNhd ℝ F.family.phi Ω ∧
              AnalyticOnNhd ℝ F.family.u Ω ∧
              AnalyticOnNhd ℝ F.family.average Ω ∧
              AnalyticOnNhd ℝ F.family.pressure Ω ∧
              AnalyticOnNhd ℝ F.family.f (domain Λ) ∧
              AnalyticOnNhd ℝ F.family.U (domain Λ) ∧
              AnalyticOnNhd ℝ F.family.Ubar (domain Λ) ∧
              AnalyticOnNhd ℝ F.family.Pi (domain Λ) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ :=
    ideal_prefix_analytic_inputs hsmall hp hB hg ha
  obtain ⟨Λ₀, hΛ₀, hexists⟩ :=
    exists_coefficientProfile d hsmall hσ (PressureDatum.pressure_contDiff hp)
  refine ⟨δ, σ, hδ, hσ, hcut, d, Λ₀, hΛ₀, AxisEvaluation.strip window 20,
    AxisEvaluation.strip_isOpen window 20, printed_rectangle_subset_strip, ?_⟩
  intro Λ hΛ C hC
  obtain ⟨F⟩ := hexists Λ hΛ C hC
  have hΛpos : 0 < Λ := hΛ₀.trans_le hΛ
  obtain ⟨hφ, hu, hB, hP⟩ := F.scaled_analytic hΛpos.le hC
  obtain ⟨hf, hU, hV, hPr⟩ := F.natural_analytic hΛpos.le hC
    ((pressureDatum_analytic hp).mono (subset_univ _))
  exact ⟨F, hφ, hu, hB, hP, hf, hU, hV, hPr⟩

end NavierStokes.NaturalEntrance
