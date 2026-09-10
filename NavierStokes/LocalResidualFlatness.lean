import NavierStokes.ActualCandidateAssembly

/-!
# All quantitative residual orders for one actual diagonal schedule

The schedule is chosen once from the genuine finite-stage estimates, retaining
the three cut bounds. Those same bounds imply every derivative and every
nonnegative power of the physical scale for the raw mixed residual. The
existential choice is outside both derivative-order and decay-order quantifiers.
-/

noncomputable section

namespace NavierStokes.LocalResidualFlatness

open Set Filter ProblemStatement DiagonalResidual MixedCandidateAssembly
open scoped Topology ContDiff

/-- All orders of quantitative flatness of the actual unlocalized mixed
Navier--Stokes residual at the singular spacetime point. -/
def AllResidualJetRates (h : ℝ) (A B : ℕ → VelocityField) (P : ℕ → PressureField)
    (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∀ r : ℝ, 0 ≤ r →
    JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h)
      (MixedDiagonalResidual.residual (fun j => (a j : ℝ))
        (PhysicalWaveSum.physicalQ h) A B P) m r

theorem allResidualJetRates_of_cutBounds {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) {a : ℕ → ℕ} (ha : Tendsto (fun j => (a j : ℝ)) atTop atTop)
    (hb : MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => E.gain j / 2)
      (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
      PhysicalWaveSum.preterminal) : AllResidualJetRates h A B P a := by
  let U := PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig
  have hU : IsOpen U := PhysicalWaveSum.preterminal_open.inter
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig)
  have hUp : U ⊆ PhysicalWaveSum.preterminal := inter_subset_left
  have hqzero := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  have hlU : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U := by
    filter_upwards [self_mem_nhdsWithin, hqzero.eventually (gt_mem_nhds hqbig)] with z hz hqz
    exact ⟨hz.1, hz.1, hqz⟩
  have hlq : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      0 < PhysicalWaveSum.physicalQ h z ∧ PhysicalWaveSum.physicalQ h z ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with z hz hqz
    exact ⟨PhysicalWaveSum.physicalQ_pos hh hh1 hz.1, hqz.le⟩
  have hhalfmono : Monotone (fun j => E.gain j / 2) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (E.gain_mono hij) (by norm_num)
  have hhalftop : Tendsto (fun j => E.gain j / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [E.gain_top.eventually (eventually_ge_atTop (2 * r))] with j hj
    linarith
  have hqpos : ∀ z ∈ U, 0 < PhysicalWaveSum.physicalQ h z :=
    fun z hz => PhysicalWaveSum.physicalQ_pos hh hh1 (hUp hz)
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) U :=
    fun z hz => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 (hUp hz)).contDiffWithinAt
  have hres (J m : ℕ) :
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))) (PhysicalWaveSum.physicalQ h)
        (fun z => navierStokesResidual (MixedDiagonalResidual.uncutVelocity A B J)
          (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2)
        m (E.gain J / 2 - E.residualLoss m) := by
    have hn : 0 ≤ E.gain J := E.gain_zero.trans (E.gain_mono (Nat.zero_le J))
    exact (E.finite_residual J m).weaken hlq (by linarith)
  intro m r hr
  exact MixedDiagonalResidual.residual_jetRate ha hU hqpos hq
    (fun j => (E.potential_smooth j).mono inter_subset_right)
    (fun j => (E.direct_smooth j).mono inter_subset_right)
    (fun j => (E.pressure_smooth j).mono inter_subset_right) hhalfmono hhalftop
    (fun j hj m hm z hz => hb.potential j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.direct j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.pressure j hj m hm z hz.1)
    hlU hqzero E.finite_background hres m r hr

/-- One schedule simultaneously has smooth sums, all three cut bounds,
vanishing endpoint jets, and every quantitative residual rate. -/
theorem exists_schedule_all_jetRates {h qbig : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (E : StageEstimates h qbig A B P) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule h qbig A B P a ∧
      MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => E.gain j / 2)
        (MixedDiagonalSchedule.commonLoss E.potentialLoss E.directLoss E.pressureLoss)
        PhysicalWaveSum.preterminal ∧
      AllResidualJetRates h A B P a := by
  have hS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      z ∈ PhysicalWaveSum.preterminal := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact hz.1
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, hb, hs, hz⟩ :=
    MixedDiagonalResidual.exists_physical_schedule_residual_zero hh hh1 hqbig
      PhysicalWaveSum.preterminal_open (Subset.refl _) hS
      E.potential_smooth E.direct_smooth E.pressure_smooth
      E.gain E.potentialLoss E.directLoss E.pressureLoss E.backgroundLoss E.residualLoss
      E.potentialConstant E.directConstant E.pressureConstant E.potentialLog E.directLog E.pressureLog
      E.potential_bound E.direct_bound E.pressure_bound
      E.gain_zero E.gain_pos E.gain_mono E.gain_top E.finite_background E.finite_residual 1
  exact ⟨a, ⟨hal, hap, had, ham, hat, hrecip, hs, hz⟩, hb,
    allResidualJetRates_of_cutBounds E hh hh1 hqbig hat hb⟩

/-- The actual finite-stage estimates with the repository's fixed budget and
geometric threshold, before any schedule information is discarded. -/
def selectedEstimates :=
  ActualCandidateAssembly.estimates ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry

/-- Closed all-order flatness for one common actual schedule. No raw-stage,
finite-stage, smoothness, or rate assumption remains. -/
theorem selected_schedule :
    ∃ a : ℕ → ℕ,
      MixedCandidateWitness.SelectedSchedule CorrectionInitialization.ActualPrimary.h
        ActualCandidateConstruction.selectedQbig ActualCandidateAssembly.selectedPotentialStages
        ActualCandidateAssembly.selectedDirectStages ActualCandidateAssembly.selectedPressureStages a ∧
      MixedDiagonalSchedule.ThreeCutBounds a CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages (fun j => selectedEstimates.gain j / 2)
        (MixedDiagonalSchedule.commonLoss selectedEstimates.potentialLoss selectedEstimates.directLoss
          selectedEstimates.pressureLoss) PhysicalWaveSum.preterminal ∧
      AllResidualJetRates CorrectionInitialization.ActualPrimary.h
        ActualCandidateAssembly.selectedPotentialStages ActualCandidateAssembly.selectedDirectStages
        ActualCandidateAssembly.selectedPressureStages a :=
  exists_schedule_all_jetRates selectedEstimates
    CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
    CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
    (ActualCandidateConstruction.qbig_pos _ _)

end NavierStokes.LocalResidualFlatness
