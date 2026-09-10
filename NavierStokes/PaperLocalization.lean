import NavierStokes.LocalPaperHeat
import NavierStokes.R3.Theorem

/-!
# Localization of the same fields as the local theorem

The local construction and the compact whole-space candidate below use one
diagonal schedule. Their velocity and pressure agree on a fixed neighborhood
of the origin for every sufficiently late presingular time, as required by
`global:localization`.
-/

noncomputable section

namespace NavierStokes.PaperLocalization

open Set Filter ProblemStatement
open scoped ContDiff

theorem compact_pressure_eq_local (P : PressureField) {t : ℝ} (ht : 3 / 4 ≤ t)
    {x : Space} (hx : x ∈ SpatialLocalization.plateau) :
    R3CompactCandidate.pressure P (t, x) = P (t, x) := by
  rw [R3CompactCandidate.pressure, TimeLocalization.activatedPressure_eq_late _ ht]
  exact (SpatialLocalization.cutPressure_eventuallyEq P (z := (t, x)) hx).self_of_nhds

/-- One local field, one localization, and one force satisfy all the
corresponding conclusions of the current manuscript simultaneously. -/
theorem local_theorem_with_compact_candidate :
    ∃ h qstar Xa Xext C : ℝ,
      ∃ A D v : VelocityField, ∃ q : PressureField,
      ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
        LocalPaper.Properties h qstar Xa Xext C A D v q ∧
        NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K ∧
        ¬ Nonempty (NavierStokesR3.ProblemStatement.GlobalFiniteEnergySolution 1 f) ∧
        (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0) ∧
        ∃ U : Set Space, IsOpen U ∧ (0 : Space) ∈ U ∧
          ∀ t ∈ Ico (3 / 4 : ℝ) 1, ∀ x ∈ U,
            u (t, x) = v (t, x) ∧ p (t, x) = q (t, x) := by
  obtain ⟨a, hs, _, hr⟩ := LocalResidualFlatness.selected_schedule
  obtain ⟨f, hc⟩ := LocalScheduleWitness.selected_compact_candidate hs
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, f, _,
    LocalPaper.properties_of_schedule hs hr, hc, hc.no_global_solution_one, ?_, ?_⟩
  · intro t ht x
    exact ⟨TimeLocalization.activatedVelocity_zero_early _ ht x,
      TimeLocalization.activatedPressure_zero_early _ ht x⟩
  · refine ⟨SpatialLocalization.plateau, SpatialLocalization.isOpen_plateau,
      SpatialLocalization.zero_mem_plateau, ?_⟩
    intro t ht x hx
    exact ⟨LocalAngularGrowth.localized_eq_raw ht.1 hx,
      compact_pressure_eq_local _ ht.1 hx⟩

end NavierStokes.PaperLocalization
