import NavierStokes.ActualBaseVelocityBounds
import NavierStokes.WholeDomainHeatBounds

/-! Fixed polynomial losses for the actual slow pressure. -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace NavierStokes.ActualBasePressureBounds

open ProblemStatement SlowBorelBase BaseResidual DiagonalResidual ActualBaseVelocityBounds

def pressureLoss (m : ℕ) : ℝ := 4 * ((m : ℝ) + 1)

theorem pressureLoss_nonneg (m : ℕ) : 0 ≤ pressureLoss m := by
  unfold pressureLoss
  positivity

theorem pressureLoss_controls_core {h : ℝ} (hh1 : h < 1 / 2) (m : ℕ) :
    -pressureLoss m ≤ -2 * CoordinateAlgebra.A h - 2 * m := by
  unfold pressureLoss CoordinateAlgebra.A
  have hm : 0 ≤ (m : ℝ) := by positivity
  linarith

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

theorem actual_bounded_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint)
    (hbox : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-2 * CoordinateAlgebra.A F.data.h - 2 * m) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl (FinalSlowBase.boxRadius W upper) hbox
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ hz => ⟨hz, mem_univ _⟩)
  have hq := A.positive_small F.data.h_pos F.data.h_lt_half
  have hd := FinalSlowBase.coefficients_smooth H v
  have ha := FinalSlowBase.scales_admissible H v upper B
  have hr := pressure_prefix_rate F.data.h_pos F.data.h_lt_half A hd ha m m (by omega)
  have hs := cartesian_prefix_growth F.data.h_pos F.data.h_lt_half A
    (bundleComponent_smooth hd W.axis.normalization 2) (-2 * CoordinateAlgebra.A F.data.h) m m
  have hr' := finiteRate_weaken hr hq (show -2 * CoordinateAlgebra.A F.data.h - 2 * m ≤
      F.data.h * ((m : ℝ) + 1) - 2 * CoordinateAlgebra.A F.data.h - 2 * m by
    have hm : 0 ≤ F.data.h * ((m : ℝ) + 1) := mul_nonneg F.data.h_pos.le (by positivity)
    linarith)
  have hs' := finiteRate_weaken hs hq (show -2 * CoordinateAlgebra.A F.data.h - 2 * m ≤
      -2 * CoordinateAlgebra.A F.data.h - m by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith)
  have hps := cartesianUncutPrefix_smooth (b := -2 * CoordinateAlgebra.A F.data.h)
    F.data.h_pos F.data.h_lt_half
    (bundleComponent_smooth hd W.axis.normalization 2) m
  have hsum := finiteRate_add hr' hs' past_isOpen hp
    ((FinalSlowBase.pressure_smooth H v upper B).sub hps) hps
  simp only [prefixPressure, sub_add_cancel] at hsum
  exact hsum

theorem actual_leading_eq (upper : ℝ) (B : ℕ) :
    EqOn (FinalSlowBase.pressure H v upper B)
      (cartesianMonomial F.data.h (-2 * CoordinateAlgebra.A F.data.h)
        ((FinalSlowBase.coefficients H v).pressure 0))
      (BaseExterior.cartesianExterior F.data.h (AssembledSlowBase.nominalOuterX W)) := by
  intro z hz
  exact BaseExterior.exterior_pressure_eq_leading F.data.h_pos F.data.h_lt_half
    (actual_exterior_coefficients H v) hz

theorem actual_middle_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint) {R : ℝ}
    (hR : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ R)
    (houter : ∀ᶠ z in l, AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-2 * CoordinateAlgebra.A F.data.h - m) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl R hR
  have hr := monomial_rate F.data.h_pos F.data.h_lt_half A
    ((FinalSlowBase.coefficients_smooth H v).pressure 0) (-2 * CoordinateAlgebra.A F.data.h) m
  exact finiteRate_congr_on hr
    (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
    ((endpoint_past.filter_mono hl).and houter) (actual_leading_eq H v upper B).symm

/-- Separate the finite coefficient region from the literal heat exterior.
The heat estimate is consumed at its actual exponent without changing the
Borel schedule or imposing a bound on similarity radius. -/
theorem pressure_rate_of_heat (upper : ℝ) (B m : ℕ)
    (hheat : ∀ (l : Filter SpaceTime), l ≤ endpoint →
      (∀ᶠ z in l, BaseExterior.nominalExteriorRadius W < (cartesianChart F.data.h z).2.1) →
      JetRate l (PhysicalWaveSum.physicalQ F.data.h)
        (BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h)
        m (-pressureLoss m)) :
    JetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-pressureLoss m) := by
  let S : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper}
  have hq := endpoint_q_small F.data.h_pos F.data.h_lt_half
  apply rate_glue (S := S) (hq.mono (fun _ hz => hz.1))
  · have hr := actual_bounded_rate H v upper B
      (show endpoint ⊓ 𝓟 S ≤ endpoint from inf_le_left)
      (show ∀ᶠ z in endpoint ⊓ 𝓟 S,
        (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper from restricted_mem endpoint S) m
    exact (finiteRate_at hr le_rfl).weaken (hq.filter_mono inf_le_left)
      (pressureLoss_controls_core F.data.h_lt_half m)
  · let l := endpoint ⊓ 𝓟 Sᶜ
    have hl : l ≤ endpoint := inf_le_left
    have ho : ∀ᶠ z in l,
        AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1 :=
      (restricted_mem endpoint Sᶜ).mono (fun _ hz =>
        (outer_lt_box (W := W) upper).trans (lt_of_not_ge hz))
    let T : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤ BaseExterior.nominalExteriorRadius W}
    apply rate_glue (S := T) ((hq.filter_mono hl).mono (fun _ hz => hz.1))
    · have hr := actual_middle_rate H v upper B (show l ⊓ 𝓟 T ≤ endpoint from inf_le_left.trans hl)
        (show ∀ᶠ z in l ⊓ 𝓟 T,
          (cartesianChart F.data.h z).2.1 ≤ BaseExterior.nominalExteriorRadius W from restricted_mem l T)
        (ho.filter_mono inf_le_left) m
      apply (finiteRate_at hr le_rfl).weaken (hq.filter_mono (inf_le_left.trans hl))
      have hc := pressureLoss_controls_core F.data.h_lt_half m
      have hm : 0 ≤ (m : ℝ) := by positivity
      linarith
    · have hl' : l ⊓ 𝓟 Tᶜ ≤ endpoint := inf_le_left.trans hl
      have hR : ∀ᶠ z in l ⊓ 𝓟 Tᶜ,
          BaseExterior.nominalExteriorRadius W < (cartesianChart F.data.h z).2.1 :=
        (restricted_mem l Tᶜ).mono (fun _ hz => lt_of_not_ge hz)
      exact (hheat _ hl' hR).congr_on
        (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
        ((endpoint_past.filter_mono hl').and hR) (FinalSlowBase.exterior_fields_eq_heat H v upper B).2.symm

/-- The actual pressure has one fixed-order polynomial bound on the full
origin endpoint filter, including arbitrary similarity radii. -/
theorem pressure_rate (upper : ℝ) (B m : ℕ) :
    JetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.pressure H v upper B)
      m (-pressureLoss m) := by
  apply pressure_rate_of_heat H v upper B m
  intro l hl hR
  obtain ⟨C, hC, hb⟩ := WholeDomainHeatBounds.heat_pressure_bound
    (BaseExterior.nominalHeatNormalization W) F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius_pos W) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_past.filter_mono hl,
    (endpoint_q_small F.data.h_pos F.data.h_lt_half).filter_mono hl, hR] with w hw hq hRw
  exact (hb w hw hq.2 hRw).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq.1 hq.2 (by
      unfold pressureLoss WholeDomainHeatBounds.heatLoss
      have hm : 0 ≤ (m : ℝ) := by positivity
      linarith)) hC)

end Actual

end NavierStokes.ActualBasePressureBounds
