import NavierStokes.ActualCandidateAssembly

/-!
# Solenoidality for every admissible actual schedule

The literal direct angular sum, its spatial localization, and the mixed
velocity retain their divergence equation for any selected schedule.
-/

noncomputable section

namespace NavierStokes.LocalScheduleAngular

open Set Filter ProblemStatement ActualCandidateAssembly
open CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

abbrev Schedule (a : ℕ → ℕ) : Prop :=
  MixedCandidateWitness.SelectedSchedule h
    (ActualCandidateConstruction.qbig ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold)
    selectedPotentialStages selectedDirectStages selectedPressureStages a

abbrev potentialSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPotentialStages

abbrev directSum (a : ℕ → ℕ) : VelocityField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedDirectStages

abbrev pressureSum (a : ℕ → ℕ) : PressureField :=
  SolenoidalDiagonal.potentialSum (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h)
    selectedPressureStages

theorem directSum_divergence {a : ℕ → ℕ} (ha : Schedule a)
    {w : SpaceTime} (ht : w.1 < 1) : spatialDivergence (directSum a) w.1 w.2 = 0 := by
  obtain ⟨_, hap, _, ham, hat, hgap, _, _⟩ := ha
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  exact LocalAngularDiagonal.angularSum_divergence outgoing.data.h_pos
    outgoing.data.h_lt_half
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    hat ha0 hamin (hgap 0) ht

theorem cut_directSum_divergence {a : ℕ → ℕ} (ha : Schedule a)
    (t : ℝ) (ht : t < 1) (x : Space) :
    spatialDivergence (SpatialLocalization.cutPotential (directSum a)) t x = 0 := by
  obtain ⟨_, hap, _, ham, hat, hgap, _, _⟩ := ha
  have ha0 : 0 < (a 0 : ℝ) := by exact_mod_cast hap 0
  have hamin (j : ℕ) : (a 0 : ℝ) ≤ (a j : ℝ) := by
    exact_mod_cast ham.monotone (Nat.zero_le j)
  exact LocalAngularDiagonal.spatialCut_angularSum_divergence outgoing.data.h_pos
    outgoing.data.h_lt_half
    (directData ActualCandidateConstruction.selectedBudget
      ActualCandidateConstruction.selectedThreshold ActualCandidateConstruction.selectedThreshold_geometry)
    hat ha0 hamin (hgap 0) t ht x

theorem mixed_divergence {a : ℕ → ℕ} (ha : Schedule a)
    {w : SpaceTime} (ht : w.1 < 1) :
    spatialDivergence
      (fun y => SpatialCurl.spatialCurl (potentialSum a) y + directSum a y) w.1 w.2 = 0 := by
  have hs := ha.2.2.2.2.2.2.1
  have hA := hs.potential.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds ht)
  have hB := hs.direct.contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds ht)
  have hc := SpatialCurl.contDiffAt_spatialCurl hA (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  rw [MixedPeriodicAssembly.spatialDivergence_add
    ((hc.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hB.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)),
    SpatialCurl.spatialDivergence_spatialCurl _ _ _
      ((hA.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)),
    directSum_divergence ha ht, add_zero]

end NavierStokes.LocalScheduleAngular
