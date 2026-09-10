import NavierStokes.LocalPaperTheorem
import NavierStokes.LocalHeatFormula
import NavierStokes.LocalHeatPressure

/-!
# The local theorem's literal radial heat formulas

These consequences use the same fields and normalization as `local_theorem`.
They express the heat exterior in the manuscript's radius coordinate, including
the genuinely integrable pressure tail.
-/

noncomputable section

namespace NavierStokes.LocalPaper

open Set MeasureTheory ProblemStatement
open scoped ContDiff

variable {h qstar Xa Xext C : ℝ} {A D u : VelocityField} {p : PressureField}

theorem Properties.exterior_profile_smooth
    (hp : Properties h qstar Xa Xext C A D u p) :
    ContDiffOn ℝ ∞ (LocalHeatFormula.exteriorProfile C h) (Ici 0) :=
  LocalHeatFormula.exteriorProfile_smooth C hp.exponent_small.1

theorem Properties.exterior_profile_derivatives_bounded
    (hp : Properties h qstar Xa Xext C A D u p) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Ici (0 : ℝ),
      |iteratedDerivWithin n (LocalHeatFormula.exteriorProfile C h) (Ici 0) y| ≤ M :=
  LocalHeatFormula.exteriorProfile_all_derivatives_bounded C hp.exponent_small.1 n

/-- The exterior angular magnitude is exactly `r^(-1-2h) H_ext(τ/r²)`. -/
theorem Properties.exterior_amplitude_formula
    (_hp : Properties h qstar Xa Xext C A D u p) (τ : ℝ) {r : ℝ} (hr : 0 < r) :
    LocalHeatFormula.amplitude C h τ r =
      r ^ (-1 - 2 * h) * LocalHeatFormula.exteriorProfile C h (τ / r ^ 2) :=
  LocalHeatFormula.amplitude_formula C h τ hr

theorem Properties.exterior_heat_equation
    (hp : Properties h qstar Xa Xext C A D u p) {τ r : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) :
    -deriv (fun τ => LocalHeatFormula.amplitude C h τ r) τ =
      iteratedDeriv 2 (LocalHeatFormula.amplitude C h τ) r +
        deriv (LocalHeatFormula.amplitude C h τ) r / r -
        LocalHeatFormula.amplitude C h τ r / r ^ 2 :=
  LocalHeatFormula.amplitude_heat_equation C hp.exponent_small.1 hτ hr

/-- The same exterior direct field is `K eθ`, and its pressure is the
literal radius integral `-∫ K²/ρ`; the integrability assertion is explicit. -/
theorem Properties.exterior_radial_form
    (hp : Properties h qstar Xa Xext C A D u p) {w : SpaceTime}
    (ht : w.1 < 1) (hq : PhysicalWaveSum.physicalQ h w < qstar)
    (hX : Xext ≤ AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w) :
    let r := Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2)
    0 < r ∧
      D w = (LocalHeatFormula.amplitude C h (1 - w.1) r / r) • BaseResidual.angularVector w ∧
      p w = -(∫ ρ in Ioi r, LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) ∧
      IntegrableOn (fun ρ => LocalHeatFormula.amplitude C h (1 - w.1) ρ ^ 2 / ρ) (Ioi r) := by
  have hh1 : h < 1 / 2 := by linarith [hp.exponent_small.2]
  have hq0 := PhysicalWaveSum.physicalQ_pos hp.exponent_small.1 hh1 ht
  have hXe : 0 < Xext := hp.edges_ordered.1.trans hp.edges_ordered.2
  have hs : 0 < AxisymmetricFields.radialEnergy w.2 :=
    (mul_pos hXe hq0).trans_le ((le_div_iff₀ hq0).mp hX)
  have hr : 0 < Real.sqrt (2 * AxisymmetricFields.radialEnergy w.2) := by positivity
  obtain ⟨_, hD, hP, _⟩ := hp.exterior w ht hq hX
  refine ⟨hr, hD.trans (LocalHeatFormula.heatVelocity_formula C h hs), ?_, ?_⟩
  · rw [hP]
    have he := LocalHeatPressure.heatPressure_radius_integral C h w.1 (w.2 2) hr
    rw [TerminalStress.radiusPoint_profilePoint hs.le] at he
    exact he
  · exact LocalHeatPressure.heatAmplitude_sq_div_integrable C hp.exponent_small.1 hh1 ht hr

end NavierStokes.LocalPaper
