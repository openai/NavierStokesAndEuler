import NavierStokes.ActualCandidateAssembly
import NavierStokes.R3.ActualCandidate

/-!
# Endpoint extensions for every admissible diagonal schedule

All statements retain the supplied schedule. This allows the local paper
construction to select a schedule with extra quantitative residual bounds
without losing the endpoint extension and global candidate conclusions.
-/

noncomputable section

namespace NavierStokes.LocalScheduleWitness

open Set Filter ProblemStatement ActualCandidateAssembly
open CorrectionInitialization.ActualPrimary
open JointResidualLimits (OneSidedExtension AwayExtensions)
open scoped Topology ContDiff

/-- The literal potential sum for the fixed selected stage sequence. -/
def potentialSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPotentialStages

/-- The literal direct angular sum for the fixed selected stage sequence. -/
def directSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedDirectStages

/-- The literal pressure sum for the fixed selected stage sequence. -/
def pressureSum (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPressureStages

/-- The standard schedule obligations for the selected actual stage fields. -/
abbrev Selected (a : ℕ → ℕ) : Prop :=
  MixedCandidateWitness.SelectedSchedule h
    (ActualCandidateConstruction.qbig ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    selectedPotentialStages selectedDirectStages selectedPressureStages a

/-- Every admissible schedule preserves the three away-from-origin endpoint
extensions; no reselection of the supplied schedule occurs. -/
theorem awayExtensions_of_schedule (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) {a : ℕ → ℕ}
    (ha : MixedCandidateWitness.SelectedSchedule h (ActualCandidateConstruction.qbig B N0)
      (potentialStages B N0 hN) (directStages B N0 hN) (pressureStages B N0 hN) a) :
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (potentialStages B N0 hN)) ∧
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (directStages B N0 hN)) ∧
    AwayExtensions (SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ))
      (PhysicalWaveSum.physicalQ h) (pressureStages B N0 hN)) := by
  obtain ⟨_, hap, _, ham, hat, hgap, _, _⟩ := ha
  have hqbig := ActualCandidateConstruction.qbig_pos B N0
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hA0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (potentialStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig (initialPotential_support B N0) hx hxz
      (Classical.choice (TailGaugePotential.finalPotential_awayExtensions
        certificate modulation upper B x hx))
  have hP0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (pressureStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.initial_add_extension outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig (initialPressure_support B N0) hx hxz
      (Classical.choice ((SlowBaseEndpoint.final_fields_awayExtensions
        certificate modulation upper B).2 x hx))
  have hB0 : ∀ x : Space, x ≠ 0 → x 2 = 0 →
      Nonempty (OneSidedExtension (directStages B N0 hN 0) x) := by
    intro x hx hxz
    exact MixedDiagonalExtensions.extension_of_eventually_zero
      ((directStages_support B N0 hN 0).eventually_zero outgoing.data.h_pos
        outgoing.data.h_lt_half hqbig hx hxz)
  have hAsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (potentialStages B N0 hN j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact positivePotential_support B N0 hN j
  have hPsupport (j : ℕ) (hj : j ≠ 0) :
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        (ActualCandidateConstruction.qbig B N0) (pressureStages B N0 hN j) := by
    cases j with
    | zero => exact (hj rfl).elim
    | succ j => exact positivePressure_support B N0 hN j
  exact ⟨MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hAsupport hA0
      (endpoints B N0 hN).potential,
    MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0)
      (fun j _ => directStages_support B N0 hN j) hB0 (endpoints B N0 hN).direct,
    MixedDiagonalExtensions.diagonal_awayExtensions_local outgoing.data.h_pos
      outgoing.data.h_lt_half hqbig hat ha0 hamin (hgap 0) hPsupport hP0
      (endpoints B N0 hN).pressure⟩

/-- The three endpoint extensions for any schedule of the selected stages. -/
theorem selected_awayExtensions {a : ℕ → ℕ} (ha : Selected a) :
    AwayExtensions (potentialSum a) ∧ AwayExtensions (directSum a) ∧
      AwayExtensions (pressureSum a) :=
  awayExtensions_of_schedule ActualCandidateConstruction.selectedBudget
    ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry ha

/-- The original axial blowup mechanism holds for the same supplied schedule. -/
theorem selected_origin_blowup {a : ℕ → ℕ} (ha : Selected a) :
    Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity
      (potentialSum a) (directSum a) (t, 0)‖) (𝓝[<] (1 : ℝ)) atTop := by
  obtain ⟨_, _, _, _, hat, _, _, _⟩ := ha
  exact GermCandidateAssembly.origin_blowup certificate modulation upper
    ActualCandidateConstruction.selectedBudget
    (ActualCandidateConstruction.qbig_pos ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (initialPotential ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (positivePotential ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    (initialPotential_axisZeroOn ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    (positivePotential_axisZeroOn ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry) hat

/-- The prescribed schedule supports the complete smooth forcing assembly,
with its actual three sums retained in the output. -/
theorem selected_periodic_candidate {a : ℕ → ℕ} (ha : Selected a) :
    ∃ forcing : VelocityField,
      CandidateProperties
        (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity
          (potentialSum a) (directSum a)))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure (pressureSum a)))
        forcing ∧ ContDiff ℝ ∞ forcing := by
  have he := selected_awayExtensions ha
  have haxis := selected_origin_blowup ha
  obtain ⟨_, hap, _, ham, hat, hgap, hs, hz⟩ := ha
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  have hcut := LocalAngularDiagonal.spatialCut_angularSum_divergence
    outgoing.data.h_pos outgoing.data.h_lt_half
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    hat ha0 hamin (hgap 0)
  obtain ⟨forcing, hc, hf, _⟩ := MixedPeriodicAssembly.exists_candidate_force
    (hs.potential.mono (fun _ hx => hx.1)) (hs.direct.mono (fun _ hx => hx.1))
    (hs.pressure.mono (fun _ hx => hx.1)) hcut hz he.1 he.2.1 he.2.2 haxis
  exact ⟨forcing, hc, hf⟩

/-- A full whole-space candidate, including a single kinetic-energy bound,
can be assembled from any selected schedule of these same actual sums. -/
theorem selected_compact_candidate {a : ℕ → ℕ} (ha : Selected a) :
    ∃ forcing : VelocityField,
      NavierStokesR3.ProblemStatement.CandidateProperties 1
        (R3CompactCandidate.velocity (potentialSum a) (directSum a))
        (R3CompactCandidate.pressure (pressureSum a)) forcing
        SpatialLocalization.supportCylinder := by
  obtain ⟨forcing, hc, hf⟩ := selected_periodic_candidate ha
  exact ⟨_, NavierStokesR3.ActualCandidate.of_localized_fields hc hf⟩

end NavierStokes.LocalScheduleWitness
