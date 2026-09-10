import NavierStokes.PeriodicComparatorSolution
import NavierStokes.CandidateConsequences

/-!
# The periodic paper theorem implies the exact comparator statement

The force in this adapter is precisely the candidate's force, with its argument
order changed from `(time, space)` to `space, time`. Neither viscosity nor time
is rescaled. The smooth periodic force's compact future time support supplies
all decay estimates required by the comparator.
-/

noncomputable section

namespace NavierStokes.ComparatorBridge

open Set ProblemStatement

/-- The force of a periodic paper candidate meets the comparator's full
periodic force condition, including all derivative decay estimates. -/
theorem forceConditionPeriodic_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K) :
    Comparator.ForceConditionPeriodic (toComparator f) :=
  forceConditionPeriodic_of_decay h.force_smooth.contDiffOn h.force_periodic
    (CandidateConsequences.futureJet_decay h.force_smooth.contDiffOn
      h.force_periodic h.force_time_support)

/-- The exact comparator conditions and exclusion hold for the same force as
the periodic paper candidate and the same viscosity. -/
theorem option_D_same_force_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K)
    (hno : ¬ Nonempty (PeriodicPaper.GlobalSmoothSolution ν f)) :
    Comparator.InitialVelocityConditionPeriodic (fun _ : Space => (0 : Space)) ∧
      Comparator.ForceConditionPeriodic (toComparator f) ∧
      ¬ (∃ v q, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν
        (fun _ => 0) (toComparator f) v q) := by
  refine ⟨zero_initial_condition, forceConditionPeriodic_of_paper_candidate h, ?_⟩
  rintro ⟨v, q, hv⟩
  exact hno ⟨periodicPaperSolution_of_comparator hv⟩

/-- A periodic paper candidate and its global-solution exclusion imply option
(D), with exactly the comparator's existential quantifiers. -/
theorem option_D_of_paper_candidate {ν : ℝ}
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : PeriodicPaper.CandidateProperties ν u p f K)
    (hno : ¬ Nonempty (PeriodicPaper.GlobalSmoothSolution ν f)) :
    ∃ (u₀ : Space → Space) (g : Space → ℝ → Space),
      Comparator.InitialVelocityConditionPeriodic u₀ ∧ Comparator.ForceConditionPeriodic g ∧
      ¬ (∃ v q, Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ g v q) :=
  ⟨fun _ => 0, toComparator f, option_D_same_force_of_paper_candidate h hno⟩

end NavierStokes.ComparatorBridge
