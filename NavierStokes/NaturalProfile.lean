import NavierStokes.NaturalAxisCoefficients
import NavierStokes.AxisReference
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual natural profiles in the original radial variable

This module reconstructs the unscaled natural profiles from the actual smooth
solutions of the coefficient-space problem. Derivative identities refer to
ordinary derivatives of the reconstructed real functions.
-/

noncomputable section

namespace NavierStokes.NaturalProfile

open Set Filter NaturalAxisBridge NaturalAxisCoefficients
open scoped Topology ContDiff


def rescalePoint (Λ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Λ * p.1, p.2)

def domain (Λ : ℝ) : Set (ℝ × ℝ) :=
  rescalePoint Λ ⁻¹' AxisEvaluation.strip window 20

def pullback (Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := F (rescalePoint Λ p)

def affineProfile (b : ℝ → ℝ) (c Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  b p.2 + c * pullback Λ F p

def angularProfile (a : ℝ → ℝ) (Λ : ℝ) (Φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  a p.2 * pullback Λ Φ p

theorem contDiff_rescalePoint (Λ : ℝ) : ContDiff ℝ ∞ (rescalePoint Λ) := by
  exact (contDiff_const.mul contDiff_fst).prodMk contDiff_snd

theorem domain_isOpen (Λ : ℝ) : IsOpen (domain Λ) :=
  (AxisEvaluation.strip_isOpen window 20).preimage (contDiff_rescalePoint Λ).continuous

theorem pullback_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20)) (Λ : ℝ) :
    ContDiffOn ℝ ∞ (pullback Λ F) (domain Λ) :=
  hF.comp (contDiff_rescalePoint Λ).contDiffOn (fun _ hp => hp)

theorem affineProfile_smooth {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ ∞ b (Ioo window.left window.right))
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) : ContDiffOn ℝ ∞ (affineProfile b c Λ F) (domain Λ) := by
  exact (hb.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).add
    (contDiffOn_const.mul (pullback_smooth hF Λ))

theorem angularProfile_smooth {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo window.left window.right))
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) : ContDiffOn ℝ ∞ (angularProfile a Λ Φ) (domain Λ) := by
  exact (ha.comp contDiff_snd.contDiffOn (fun _ hp => hp.2)).mul (pullback_smooth hΦ Λ)

theorem sliceY_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun Y : ℝ => F (Y, p.2)) p.1 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)

theorem sliceEta_smooth {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ AxisEvaluation.strip window 20) :
    ContDiffAt ℝ ∞ (fun η : ℝ => F (p.1, η)) p.2 := by
  exact (hF.contDiffAt ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)).comp p.2
    (contDiffAt_const.prodMk contDiffAt_id)

theorem pullback_hasDerivAt_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    HasDerivAt (fun X : ℝ => pullback Λ F (X, p.2))
      (Λ * partialY F (rescalePoint Λ p)) p.1 := by
  have hf := (sliceY_smooth hF hp).differentiableAt (by norm_num)
  have hd := hf.hasDerivAt.comp p.1 ((hasDerivAt_id p.1).const_mul Λ)
  simp only [Function.comp_def, mul_one] at hd
  convert! hd using 1 ; simp only [rescalePoint, partialY, mul_comm]

theorem pullback_partialY {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (pullback Λ F) p = Λ * partialY F (rescalePoint Λ p) :=
  (pullback_hasDerivAt_Y hF Λ hp).deriv

theorem pullback_partialEta (Λ : ℝ) (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    partialEta (pullback Λ F) p = partialEta F (rescalePoint Λ p) := rfl

theorem pullback_second_Y {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    iteratedDeriv 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 =
      Λ ^ 2 * iteratedDeriv 2 (fun Y : ℝ => F (Y, p.2)) (Λ * p.1) := by
  have hs := sliceY_smooth hF hp
  have hs' : ContDiffAt ℝ 1 (deriv (fun Y : ℝ => F (Y, p.2))) (Λ * p.1) := by
    exact (hs.fderiv_right (m := 1)
        (by simp)).clm_apply
        contDiffAt_const
  have hd := ((hs'.differentiableAt (by norm_num)).hasDerivAt.comp p.1
    ((hasDerivAt_id p.1).const_mul Λ)).const_mul Λ
  have heq : deriv (fun X : ℝ => pullback Λ F (X, p.2)) =ᶠ[𝓝 p.1]
      (fun X : ℝ => Λ * deriv (fun Y : ℝ => F (Y, p.2)) (Λ * X)) := by
    have hc : Continuous (fun X : ℝ => (Λ * X, p.2)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds hp)] with X hX
    exact (pullback_hasDerivAt_Y hF Λ (p := (X, p.2)) hX).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  convert! hd.deriv using 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem pullback_radialDifferential {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (pullback Λ F) p =
      Λ * radialDifferential r F (rescalePoint Λ p) := by
  unfold radialDifferential
  rw [pullback_second_Y hF Λ hp, pullback_partialY hF Λ hp]
  dsimp [rescalePoint]
  ring

theorem affineProfile_partialY {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (affineProfile b c Λ F) p = c * Λ * partialY F (rescalePoint Λ p) := by
  simpa only [affineProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hF Λ hp).const_mul c).const_add (b p.2) |>.deriv

theorem affineProfile_partialEta {b : ℝ → ℝ} {b' : ℝ}
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (c Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (hb : HasDerivAt b b' p.2) :
    partialEta (affineProfile b c Λ F) p = b' + c * partialEta F (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hF hp).differentiableAt (by norm_num)
  exact (hb.add (hf.hasDerivAt.const_mul c)).deriv

theorem affineProfile_radialDifferential {F : ℝ × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (AxisEvaluation.strip window 20))
    (b : ℝ → ℝ) (c Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (affineProfile b c Λ F) p =
      c * Λ * radialDifferential r F (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ F (X, p.2)) p.1 := by
    exact ((sliceY_smooth hF hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [affineProfile_partialY hF b c Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => b p.2 + c * pullback Λ F (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ)),
    iteratedDeriv_const_mul c hs, pullback_second_Y hF Λ hp]
  dsimp [rescalePoint]
  ring

theorem angularProfile_partialY {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    partialY (angularProfile a Λ Φ) p = a p.2 * Λ * partialY Φ (rescalePoint Λ p) := by
  simpa only [angularProfile, partialY, mul_assoc] using
    ((pullback_hasDerivAt_Y hΦ Λ hp).const_mul (a p.2)).deriv

theorem angularProfile_partialEta {a : ℝ → ℝ} {a' : ℝ}
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (Λ : ℝ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) (ha : HasDerivAt a a' p.2) :
    partialEta (angularProfile a Λ Φ) p =
      a' * Φ (rescalePoint Λ p) + a p.2 * partialEta Φ (rescalePoint Λ p) := by
  have hf := (sliceEta_smooth hΦ hp).differentiableAt (by norm_num)
  exact (ha.mul hf.hasDerivAt).deriv

theorem angularProfile_radialDifferential {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    (a : ℝ → ℝ) (Λ : ℝ) (r : ℕ) {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    radialDifferential r (angularProfile a Λ Φ) p =
      a p.2 * Λ * radialDifferential r Φ (rescalePoint Λ p) := by
  have hs : ContDiffAt ℝ 2 (fun X : ℝ => pullback Λ Φ (X, p.2)) p.1 := by
    exact ((sliceY_smooth hΦ hp).comp p.1 (contDiffAt_const.mul contDiffAt_id)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  unfold radialDifferential
  rw [angularProfile_partialY hΦ a Λ hp]
  change p.1 * iteratedDeriv 2 (fun X => a p.2 * pullback Λ Φ (X, p.2)) p.1 + _ = _
  rw [iteratedDeriv_const_mul (a p.2) hs, pullback_second_Y hΦ Λ hp]
  dsimp [rescalePoint]
  ring

/-- The fixed polynomial and pressure fields, interpreted as real functions. -/
def actualData (h j σ : ℝ) (P0 : ℝ → ℝ) : ParameterData where
  A := NaturalAxisData.A h
  D := NaturalAxisData.D h
  h := h
  chi := NaturalAxisData.chi h j σ
  d := NaturalAxisData.d
  inverseL := fun η => (NaturalAxisData.L h η)⁻¹
  uStar := NaturalAxisData.U j
  uStarEta := fun _ => 4
  wStar := NaturalAxisData.W h j
  hStar := NaturalAxisData.H h j
  kappa := realGradient h j σ
  zStar := NaturalAxisData.Z h j P0

/-- Replace all coefficient evaluations by their proved concrete values. -/
theorem materialize_scaled {h j σ t : ℝ} {P0 a₀ : ℝ → ℝ}
    (v : CoefficientFamily h j σ P0) (a : AxisCoefficientSpace.AxisSpace window v.epsilon)
    (ha : ∀ η ∈ window.interval, inputValue window v.epsilon a η = a₀ η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window
      (parameters window v.epsilon (v.elements .chi) v.axisData) t
      (inputValue window v.epsilon a) Φ u B P) :
    IsScaledSolution window (actualData h j σ P0) t a₀ Φ u B P := by
  refine {
    phi_smooth := hs.phi_smooth
    u_smooth := hs.u_smooth
    average_smooth := hs.average_smooth
    pressure_smooth := hs.pressure_smooth
    phi_axis := hs.phi_axis
    u_axis := hs.u_axis
    average_axis := hs.average_axis
    pressure_axis := hs.pressure_axis
    average_equation := hs.average_equation
    average_integral := hs.average_integral
    pressure_equation := ?_
    pressure_integral := ?_
    angular_equation := ?_
    axial_equation := ?_
  }
  · intro p hp
    rw [hs.pressure_equation p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    rw [hs.pressure_integral p hp, ha p.2 ⟨hp.2.1.le, hp.2.2.le⟩]
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [angularRemainder, reconstructedW, reconstructedU, reconstructedH,
      actualData, parameters, CoefficientFamily.axisData, hv, realField] using
      hs.angular_equation p hp
  · intro p hp
    have hv : ∀ k, inputValue window v.epsilon (v.elements k) p.2 =
        realField h j σ P0 k p.2 := fun k => v.value k ⟨hp.2.1.le, hp.2.2.le⟩
    simpa only [axialRemainder, reconstructedW, actualData, parameters,
      CoefficientFamily.axisData, hv, realField] using hs.axial_equation p hp

theorem amplitude_smooth {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) :
    ContDiffOn ℝ ∞ (realAmplitude h j σ Λ C) (Ioo window.left window.right) := by
  intro η hη
  have hc : ContDiffAt ℂ ∞ (axisPhase h j σ) (η : ℂ) :=
    (d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)).contDiffAt
  have hr : ContDiffAt ℝ ∞ (realPhase h j σ) η := by
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using hc.real_of_complex
  exact (((contDiffAt_const.mul hr).exp).mul contDiffAt_const).contDiffWithinAt

theorem uStar_hasDerivAt (j η : ℝ) : HasDerivAt (NaturalAxisData.U j) 4 η := by
  change HasDerivAt (fun x : ℝ => 4 * x + j) 4 η
  simpa only [mul_one, id_eq] using ((hasDerivAt_id η).const_mul 4).add_const j

theorem uStar_smooth (j : ℝ) : ContDiff ℝ ∞ (NaturalAxisData.U j) := by
  exact (contDiff_const.mul contDiff_id).add contDiff_const

/-- The natural transport coefficient recovered from the true radial average. -/
def transportW (h : ℝ) (V : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  1 - 2 * NaturalAxisData.D h * p.2 * V p - NaturalAxisData.d p.2 * partialEta V p

def transportH (h : ℝ) (U : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  NaturalAxisData.D h * p.2 + NaturalAxisData.d p.2 * U p

theorem transportW_reconstruct {h j σ Λ : ℝ} (P0 : ℝ → ℝ) {B : ℝ × ℝ → ℝ}
    (hB : ContDiffOn ℝ ∞ B (AxisEvaluation.strip window 20))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p =
      reconstructedW (actualData h j σ P0) (1 / Λ) B (rescalePoint Λ p) := by
  unfold transportW
  rw [affineProfile_partialEta hB (1 / Λ) Λ hp (uStar_hasDerivAt j p.2)]
  simp only [affineProfile, pullback, reconstructedW, actualData, rescalePoint,
    NaturalAxisData.W]
  ring

theorem transportH_reconstruct (h j σ Λ : ℝ) (P0 : ℝ → ℝ) (u : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) :
    transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p) := by
  simp only [transportH, affineProfile, pullback, reconstructedH, actualData,
    rescalePoint, NaturalAxisData.H]
  ring

theorem gradient_identity (h j σ η : ℝ) :
    NaturalAxisData.H h j η * realGradient h j σ η =
      -NaturalAxisData.L h η * NaturalAxisData.chi h j σ η := by
  unfold realGradient NaturalAxisData.chi
  ring

/-- The actual unscaled system, with all derivatives taken on real functions. -/
structure IsNaturalSolution (h j Λ : ℝ) (P0 a₀ : ℝ → ℝ)
    (f U V Pr : ℝ × ℝ → ℝ) : Prop where
  f_smooth : ContDiffOn ℝ ∞ f (domain Λ)
  U_smooth : ContDiffOn ℝ ∞ U (domain Λ)
  average_smooth : ContDiffOn ℝ ∞ V (domain Λ)
  pressure_smooth : ContDiffOn ℝ ∞ Pr (domain Λ)
  f_axis : ∀ η ∈ Ioo window.left window.right, f (0, η) = a₀ η
  U_axis : ∀ η ∈ Ioo window.left window.right, U (0, η) = NaturalAxisData.U j η
  average_axis : ∀ η ∈ Ioo window.left window.right, V (0, η) = NaturalAxisData.U j η
  pressure_axis : ∀ η ∈ Ioo window.left window.right, Pr (0, η) = P0 η
  average_equation : ∀ p ∈ domain Λ, V p + p.1 * partialY V p = U p
  pressure_equation : ∀ p ∈ domain Λ, partialY Pr p = (f p) ^ 2
  average_integral : ∀ p ∈ domain Λ,
    p.1 * V p = ∫ X in (0 : ℝ)..p.1, U (X, p.2)
  pressure_integral : ∀ p ∈ domain Λ,
    Pr p - P0 p.2 = ∫ X in (0 : ℝ)..p.1, (f (X, p.2)) ^ 2
  angular_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 f p =
      transportW h V p * (p.1 * partialY f p + f p) +
      h * (1 - 2 * p.2 * U p) * f p + transportH h U p * partialEta f p
  axial_equation : ∀ p ∈ domain Λ,
    2 * NaturalAxisData.L h p.2 * radialDifferential 1 U p =
      transportW h V p * (p.1 * partialY U p) +
      NaturalAxisData.A h * (1 - 2 * p.2 * U p) * U p +
      transportH h U p * partialEta U p + NaturalAxisData.d p.2 * partialEta Pr p -
      4 * NaturalAxisData.A h * p.2 * Pr p - 2 * p.2 * p.1 * partialY Pr p

private theorem angular_rescale_identity
    {Λ L X η h d u U W H Hs κ χ a φ φY φEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0) (hχ : Hs * κ = -L * χ)
    (hH : H = Hs + (1 / Λ) * d * u)
    (heq : 2 * R = -χ * φ + (1 / Λ) * L⁻¹ *
      ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
        W * (Λ * X * φY) + H * φEta)) :
    2 * L * (a * Λ * R) = W * (X * (a * Λ * φY) + a * φ) +
      h * (1 - 2 * η * U) * (a * φ) + H * ((Λ * κ) * a * φ + a * φEta) := by
  calc
    _ = a * Λ * L * (2 * R) := by ring
    _ = a * Λ * L * (-χ * φ + (1 / Λ) * L⁻¹ *
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by rw [heq]
    _ = a * (Λ * (Hs * κ) * φ +
        ((W + h * (1 - 2 * η * U) + d * u * κ) * φ +
          W * (Λ * X * φY) + H * φEta)) := by
      rw [hχ]
      field_simp
    _ = _ := by
      rw [hH]
      field_simp ; ring

private theorem axial_rescale_identity
    {Λ L X η A d Us UsEta Hs W u uY uEta P0 P0Eta P PY PEta R : ℝ}
    (hΛ : Λ ≠ 0) (hL : L ≠ 0)
    (heq : 2 * R = -L⁻¹ *
      (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
      (1 / Λ) * L⁻¹ *
        (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
          W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
          (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta - 2 * η * (Λ * X * PY))) :
    2 * L * R = W * (X * uY) +
      A * (1 - 2 * η * (Us + (1 / Λ) * u)) * (Us + (1 / Λ) * u) +
      (Hs + (1 / Λ) * d * u) * (UsEta + (1 / Λ) * uEta) +
      d * (P0Eta + (1 / Λ) * PEta) - 4 * A * η * (P0 + (1 / Λ) * P) -
      2 * η * X * PY := by
  calc
    _ = L * (2 * R) := by ring
    _ = L * (-L⁻¹ *
        (-A * (1 - 2 * η * Us) * Us - Hs * UsEta - d * P0Eta + 4 * A * η * P0) +
        (1 / Λ) * L⁻¹ *
          (A * (1 - 4 * η * Us) * u - 2 * A * η * (1 / Λ) * u ^ 2 +
            W * (Λ * X * uY) + Hs * uEta + d * UsEta * u +
            (1 / Λ) * d * u * uEta - 4 * A * η * P + d * PEta -
            2 * η * (Λ * X * PY))) := by rw [heq]
    _ = _ := by
      field_simp ; ring

theorem angular_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : Λ ≠ 0)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    (ha : HasDerivAt a₀ ((Λ * realGradient h j σ p.2) * a₀ p.2) p.2) :
    2 * NaturalAxisData.L h p.2 * radialDifferential 2 (angularProfile a₀ Λ Φ) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (angularProfile a₀ Λ Φ) p + angularProfile a₀ Λ Φ p) +
      h * (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        angularProfile a₀ Λ Φ p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (angularProfile a₀ Λ Φ) p := by
  rw [angularProfile_radialDifferential hs.phi_smooth a₀ Λ 2 hp,
    angularProfile_partialY hs.phi_smooth a₀ Λ hp,
    angularProfile_partialEta hs.phi_smooth Λ hp ha,
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  have hL : NaturalAxisData.L h p.2 ≠ 0 :=
    (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
  apply angular_rescale_identity hΛ hL (gradient_identity h j σ p.2)
    (H := reconstructedH (actualData h j σ P0) (1 / Λ) u (rescalePoint Λ p))
    (Hs := NaturalAxisData.H h j p.2)
  · rfl
  · simpa only [angularRemainder, actualData, reconstructedU, rescalePoint,
      affineProfile, pullback, mul_assoc] using hs.angular_equation (rescalePoint Λ p) hp

theorem axial_equation_reconstruct {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : Λ ≠ 0)
    (hP0 : ContDiff ℝ ∞ P0) {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P)
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    2 * NaturalAxisData.L h p.2 *
        radialDifferential 1 (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p =
      transportW h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B) p *
        (p.1 * partialY (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p) +
      NaturalAxisData.A h *
        (1 - 2 * p.2 * affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p) *
        affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u p +
      transportH h (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p *
        partialEta (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u) p +
      NaturalAxisData.d p.2 * partialEta (affineProfile P0 (1 / Λ) Λ P) p -
      4 * NaturalAxisData.A h * p.2 * affineProfile P0 (1 / Λ) Λ P p -
      2 * p.2 * p.1 * partialY (affineProfile P0 (1 / Λ) Λ P) p := by
  rw [affineProfile_radialDifferential hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ 1 hp,
    affineProfile_partialY hs.u_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
    affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
    affineProfile_partialEta hs.u_smooth (1 / Λ) Λ hp (uStar_hasDerivAt j p.2),
    affineProfile_partialEta hs.pressure_smooth (1 / Λ) Λ hp
      ((hP0.differentiable (by norm_num)).differentiableAt.hasDerivAt),
    transportW_reconstruct P0 hs.average_smooth hp,
    transportH_reconstruct h j σ Λ P0 u p]
  simp only [one_div_mul_cancel hΛ, one_mul]
  have hL : NaturalAxisData.L h p.2 ≠ 0 :=
    (L_pos_on_window hsmall ⟨hp.2.1.le, hp.2.2.le⟩).ne'
  apply axial_rescale_identity hΛ hL
  simpa only [axialRemainder, actualData, NaturalAxisData.Z, reconstructedH,
    rescalePoint, affineProfile, pullback, mul_assoc] using
      hs.axial_equation (rescalePoint Λ p) hp

theorem domain_segment {Λ : ℝ} (hΛ : 0 < Λ) {p : ℝ × ℝ} (hp : p ∈ domain Λ)
    {X : ℝ} (hX : X ∈ uIcc (0 : ℝ) p.1) : (X, p.2) ∈ domain Λ := by
  change (-20 < Λ * X ∧ Λ * X < 20) ∧ p.2 ∈ Ioo window.left window.right
  change (-20 < Λ * p.1 ∧ Λ * p.1 < 20) ∧ _ at hp
  refine ⟨?_, hp.2⟩
  rcases le_total 0 p.1 with hpos | hneg
  · rw [uIcc_of_le hpos] at hX
    constructor
    · have := mul_nonneg hΛ.le hX.1
      linarith
    · exact (mul_le_mul_of_nonneg_left hX.2 hΛ.le).trans_lt hp.1.2
  · rw [uIcc_of_ge hneg] at hX
    constructor
    · exact hp.1.1.trans_le (mul_le_mul_of_nonneg_left hX.1 hΛ.le)
    · have := mul_nonpos_of_nonneg_of_nonpos hΛ.le hX.2
      linarith

theorem average_integral_reconstruct {Λ : ℝ} (hΛ : 0 < Λ)
    (b : ℝ → ℝ) (c : ℝ) {u B : ℝ × ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ u (AxisEvaluation.strip window 20))
    (havg : ∀ q ∈ AxisEvaluation.strip window 20,
      q.1 * B q = ∫ Y in (0 : ℝ)..q.1, u (Y, q.2))
    {p : ℝ × ℝ} (hp : p ∈ domain Λ) :
    p.1 * affineProfile b c Λ B p =
      ∫ X in (0 : ℝ)..p.1, affineProfile b c Λ u (X, p.2) := by
  have hi : IntervalIntegrable (fun X : ℝ => pullback Λ u (X, p.2))
      MeasureTheory.volume 0 p.1 := by
    apply ContinuousOn.intervalIntegrable
    exact (pullback_smooth hu Λ).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx => domain_segment hΛ hp hx)
  have hchange := intervalIntegral.integral_comp_mul_left
    (fun Y : ℝ => u (Y, p.2)) hΛ.ne' (a := 0) (b := p.1)
  change p.1 * (b p.2 + c * B (rescalePoint Λ p)) =
    ∫ X in (0 : ℝ)..p.1, b p.2 + c * pullback Λ u (X, p.2)
  rw [intervalIntegral.integral_add intervalIntegrable_const (hi.const_mul c),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  change _ = (p.1 - 0) * b p.2 + c * ∫ X in (0 : ℝ)..p.1, u (Λ * X, p.2)
  rw [hchange]
  simp only [mul_zero, smul_eq_mul, sub_zero]
  have hav := havg (rescalePoint Λ p) hp
  dsimp only [rescalePoint] at hav
  rw [← hav]
  dsimp [rescalePoint]
  field_simp

/-- Reconstruction preserves the full differential and integral system. -/
theorem reconstruct_solution {h j σ Λ : ℝ} {P0 a₀ : ℝ → ℝ}
    (hsmall : NaturalAxisRange.Parameters h j) (hΛ : 0 < Λ)
    (hP0 : ContDiff ℝ ∞ P0)
    (haSmooth : ContDiffOn ℝ ∞ a₀ (Ioo window.left window.right))
    (ha : ∀ η ∈ Ioo window.left window.right,
      HasDerivAt a₀ ((Λ * realGradient h j σ η) * a₀ η) η)
    {Φ u B P : ℝ × ℝ → ℝ}
    (hs : IsScaledSolution window (actualData h j σ P0) (1 / Λ) a₀ Φ u B P) :
    IsNaturalSolution h j Λ P0 a₀ (angularProfile a₀ Λ Φ)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
      (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ B)
      (affineProfile P0 (1 / Λ) Λ P) := by
  refine {
    f_smooth := angularProfile_smooth haSmooth hs.phi_smooth Λ
    U_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.u_smooth (1 / Λ) Λ
    average_smooth := affineProfile_smooth (uStar_smooth j).contDiffOn hs.average_smooth (1 / Λ) Λ
    pressure_smooth := affineProfile_smooth hP0.contDiffOn hs.pressure_smooth (1 / Λ) Λ
    f_axis := ?_
    U_axis := ?_
    average_axis := ?_
    pressure_axis := ?_
    average_equation := ?_
    pressure_equation := ?_
    average_integral := fun p hp => average_integral_reconstruct hΛ (NaturalAxisData.U j)
      (1 / Λ) hs.u_smooth hs.average_integral hp
    pressure_integral := ?_
    angular_equation := fun p hp => angular_equation_reconstruct hsmall hΛ.ne' hs hp (ha p.2 hp.2)
    axial_equation := fun p hp => axial_equation_reconstruct hsmall hΛ.ne' hP0 hs hp
  }
  · intro η hη
    simp only [angularProfile, pullback, rescalePoint, mul_zero, hs.phi_axis η hη, mul_one]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.average_axis η hη,
      hs.u_axis η hη, add_zero]
  · intro η hη
    simp only [affineProfile, pullback, rescalePoint, mul_zero, hs.pressure_axis η hη, add_zero]
  · intro p hp
    rw [affineProfile_partialY hs.average_smooth (NaturalAxisData.U j) (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul]
    change NaturalAxisData.U j p.2 + (1 / Λ) * B (rescalePoint Λ p) +
      p.1 * partialY B (rescalePoint Λ p) =
        NaturalAxisData.U j p.2 + (1 / Λ) * u (rescalePoint Λ p)
    have he := hs.average_equation (rescalePoint Λ p) hp
    dsimp [rescalePoint] at he ⊢
    apply (mul_left_cancel₀ hΛ.ne')
    field_simp
    linear_combination he
  · intro p hp
    rw [affineProfile_partialY hs.pressure_smooth P0 (1 / Λ) Λ hp,
      one_div_mul_cancel hΛ.ne', one_mul, hs.pressure_equation (rescalePoint Λ p) hp]
    simp only [angularProfile, pullback, rescalePoint, mul_pow]
  · intro p hp
    change P0 p.2 + (1 / Λ) * P (rescalePoint Λ p) - P0 p.2 = _
    rw [add_sub_cancel_left, hs.pressure_integral (rescalePoint Λ p) hp]
    have he := intervalIntegral.integral_comp_mul_left
      (fun Y : ℝ => (a₀ p.2) ^ 2 * (Φ (Y, p.2)) ^ 2) hΛ.ne' (a := 0) (b := p.1)
    simpa only [angularProfile, pullback, rescalePoint, mul_zero, smul_eq_mul, mul_pow,
      one_div] using he.symm

theorem angularProfile_log_slope_at_four {Λ : ℝ} (hΛ : 0 < Λ)
    {a : ℝ → ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (AxisEvaluation.strip window 20))
    {η : ℝ} (hη : η ∈ Ioo window.left window.right)
    (ha : 0 < a η) (hval : 0 < Φ (4, η)) :
    -2 * (4 / Λ) * partialY (angularProfile a Λ Φ) (4 / Λ, η) /
        angularProfile a Λ Φ (4 / Λ, η) =
      -8 * partialY Φ (4, η) / Φ (4, η) := by
  have hrad : Λ * (4 / Λ) = 4 := by field_simp
  have hp : (4 / Λ, η) ∈ domain Λ := by
    change (Λ * (4 / Λ), η) ∈ AxisEvaluation.strip window 20
    rw [hrad]
    exact ⟨by norm_num, hη⟩
  rw [angularProfile_partialY hΦ a Λ hp]
  simp only [angularProfile, pullback, rescalePoint, hrad]
  field_simp ; ring

def profileErrorConstant {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) : ℝ :=
  errorConstant window d.coefficients.epsilon_pos (d.coefficients.elements .chi)
    d.coefficients.axisData d.amplitudeBound d.amplitudeBound_nonneg

/-- The functions and estimates obtained from one actual coefficient-space
fixed point. All unscaled functions are explicit expressions in these fields. -/
structure ProfileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (Λ C : ℝ) where
  phi : ℝ × ℝ → ℝ
  u : ℝ × ℝ → ℝ
  average : ℝ × ℝ → ℝ
  pressure : ℝ × ℝ → ℝ
  natural : IsNaturalSolution h j Λ P0 (realAmplitude h j σ Λ C)
    (angularProfile (realAmplitude h j σ Λ C) Λ phi)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ u)
    (affineProfile (NaturalAxisData.U j) (1 / Λ) Λ average)
    (affineProfile P0 (1 / Λ) Λ pressure)
  mixed_error : UniformMixedError window d.coefficients.epsilon
    (profileErrorConstant d / (2 * Λ)) phi u
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).1)
    (AxisEvaluation.profile window d.coefficients.epsilon
      (referenceCoefficients window d.coefficients.epsilon_pos
        (d.coefficients.elements .chi) d.coefficients.axisData).2)
  positive : ∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 →
    0 < angularProfile (realAmplitude h j σ Λ C) Λ phi p
  slope : ∀ η ∈ Ioo window.left window.right, 99 / 100 ≤ NaturalAxisData.chi h j σ η →
    23 / 10 <
      -2 * (4 / Λ) * partialY (angularProfile (realAmplitude h j σ Λ C) Λ phi) (4 / Λ, η) /
        angularProfile (realAmplitude h j σ Λ C) Λ phi (4 / Λ, η)

def ProfileFamily.f {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  angularProfile (realAmplitude h j σ Λ C) Λ F.phi

def ProfileFamily.U {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.u

def ProfileFamily.Ubar {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile (NaturalAxisData.U j) (1 / Λ) Λ F.average

def ProfileFamily.Pi {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) : ℝ × ℝ → ℝ :=
  affineProfile P0 (1 / Λ) Λ F.pressure

/-- The scale threshold is uniform over every normalization above the actual
compact-domain exponential threshold. -/
theorem exists_profileFamily {h j σ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hsmall : NaturalAxisRange.Parameters h j)
    (hσ : 0 < σ) (hP0 : ContDiff ℝ ∞ P0) :
    ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
      ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  have hchi : ∀ η ∈ window.interval,
      0 ≤ inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ∧
        inputValue window d.coefficients.epsilon (d.coefficients.elements .chi) η ≤ 1 := by
    intro η hη
    rw [d.coefficients.value .chi hη]
    exact ⟨(NaturalAxisData.chi_bounds h j hσ η).1, (NaturalAxisData.chi_bounds h j hσ η).2.le⟩
  obtain ⟨Λ₀, hΛ₀, hexists⟩ := AxisReference.exists_positive_scaled_profiles window
    d.coefficients.epsilon_pos (d.coefficients.elements .chi) d.coefficients.axisData
    d.coefficients.compatible hchi d.amplitudeBound d.amplitudeBound_nonneg
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ C hC
  have hΛpos : 0 < Λ := hΛ₀.trans_le hΛ
  have hCpos : 0 < C := (Real.exp_pos _).trans_le hC
  obtain ⟨a, ha, harad, havalue⟩ := d.uniformAmplitude Λ hΛpos.le C hC
  obtain ⟨Φ, u, B, P, hs, herr, hpositive, hslope⟩ := hexists Λ hΛ a ha harad
  have hs' := materialize_scaled d.coefficients a havalue hs
  refine ⟨{
    phi := Φ
    u := u
    average := B
    pressure := P
    natural := reconstruct_solution hsmall hΛpos hP0 (amplitude_smooth d Λ C)
      (fun η hη => d.realAmplitude_hasDerivAt Λ C ⟨hη.1.le, hη.2.le⟩) hs'
    mixed_error := herr
    positive := ?_
    slope := ?_
  }⟩
  · intro p hp hY0 hY1
    exact mul_pos (realAmplitude_pos h j σ Λ hCpos p.2)
      (lt_trans (by norm_num) (hpositive (Λ * p.1) ⟨hY0, hY1⟩ p.2 hp.2))
  · intro η hη hchiη
    rw [angularProfile_log_slope_at_four hΛpos hs.phi_smooth hη
      (realAmplitude_pos h j σ Λ hCpos η)
      (lt_trans (by norm_num) (hpositive 4 (by norm_num) η hη))]
    apply hslope η hη
    rw [d.coefficients.value .chi ⟨hη.1.le, hη.2.le⟩]
    exact hchiη

/-- The pressure integral and ideal prefix yield actual unscaled natural
profiles after selecting the cutoff and common analytic coefficient radius. -/
theorem ideal_prefix_profileFamily {h j : ℝ}
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
        ∃ Λ₀ : ℝ, 0 < Λ₀ ∧ ∀ Λ : ℝ, Λ₀ ≤ Λ →
          ∀ C : ℝ, d.normalizationThreshold Λ ≤ C → Nonempty (ProfileFamily d Λ C) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, ⟨d⟩⟩ :=
    ideal_prefix_analytic_inputs hsmall hp hB hg ha
  refine ⟨δ, σ, hδ, hσ, hcut, d, ?_⟩
  exact exists_profileFamily d hsmall hσ (PressureDatum.pressure_contDiff hp)

/-- A direct existence theorem for the unscaled real functions. The cutoff,
analytic input family, large scale, and normalization are all constructed
from the stated pressure assumptions. -/
theorem exists_natural_profiles {h j : ℝ}
    (hsmall : NaturalAxisRange.Parameters h j)
    {g a : ℝ → ℝ} {cap B : ℝ}
    (hp : PressureDatum.Admissible g a cap) (hB : 2 ≤ B)
    (hg : ∀ y ≤ 0, g y = B ^ 2 * Real.exp ((1 / 5 : ℝ) * y))
    (ha : ∀ y ≤ 0, a y = 1) :
    ∃ δ σ Λ C : ℝ, 0 < δ ∧ 0 < σ ∧ 0 < Λ ∧ 0 < C ∧
      ∃ f U V Pr : ℝ × ℝ → ℝ,
        IsNaturalSolution h j Λ (PressureDatum.pressure g a)
          (realAmplitude h j σ Λ C) f U V Pr ∧
        (∀ p ∈ domain Λ, 0 ≤ Λ * p.1 → Λ * p.1 ≤ 41 / 10 → 0 < f p) ∧
        (∀ η ∈ Icc (-1 : ℝ) 1,
          |NaturalAxisData.Z h j (PressureDatum.pressure g a) η| ≤ δ →
            23 / 10 < -2 * (4 / Λ) * partialY f (4 / Λ, η) / f (4 / Λ, η)) := by
  obtain ⟨δ, σ, hδ, hσ, hcut, d, Λ, hΛ, hexists⟩ :=
    ideal_prefix_profileFamily hsmall hp hB hg ha
  let C := d.normalizationThreshold Λ
  obtain ⟨F⟩ := hexists Λ le_rfl C le_rfl
  refine ⟨δ, σ, Λ, C, hδ, hσ, hΛ, Real.exp_pos _,
    F.f, F.U, F.Ubar, F.Pi, F.natural, F.positive, ?_⟩
  intro η hη hZ
  exact F.slope η (original_interval_interior hη) (hcut η hη hZ).le

end NavierStokes.NaturalProfile

end
