import NavierStokes.R3.ActualCandidate
import NavierStokes.R3.CandidateBreakdown
import NavierStokes.R3.ViscosityScaling
import NavierStokes.R3.IntegratedDissipation

/-!
# Theorem 1.1: unconditional whole-space forced Navier–Stokes blowup

The actual selected construction supplies the viscosity-one fields. Spatial
rescaling gives every positive viscosity while retaining singular time one,
compact support in strictly positive time for the force, and one kinetic-energy
bound for all times before the singularity. Whole-space comparison excludes a
global smooth finite-energy solution with the same prescribed force and datum.
-/

noncomputable section

open Set MeasureTheory

namespace NavierStokesR3

open ProblemStatement ViscosityScaling

/-- The full paper conclusion, together with the initial time interval on
which the constructed velocity is at rest. No construction hypotheses remain. -/
theorem theorem_1_1_with_initial_rest (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space,
        u (t, x) = 0 ∧ p (t, x) = 0 := by
  obtain ⟨u, p, f, K, hc, hzero⟩ := ActualCandidate.selected_candidate_one_with_initial_rest
  refine ⟨scaledVelocity ν u, scaledPressure ν p, scaledVelocity ν f,
    (fun x : Space => Real.sqrt ν • x) '' K, candidate_at_viscosity hc hν, ?_, ?_⟩
  · rintro ⟨v⟩
    exact hc.no_global_solution_one ⟨normalized_global_solution hν v⟩
  · intro t ht x
    constructor
    · change Real.sqrt ν • u (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).1, smul_zero]
    · change ν • p (t, (Real.sqrt ν)⁻¹ • x) = 0
      rw [(hzero t ht _).2, smul_zero]

/-- Theorem 1.1, with all properties of the same velocity, pressure, force,
and compact support witnessed simultaneously, for every positive viscosity. -/
theorem theorem_1_1 : ProblemStatement.breakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, hc, hg, _⟩ := theorem_1_1_with_initial_rest ν hν
  exact ⟨u, p, f, K, hc, hg⟩

/-- The primary whole-space candidate-existence assertion at any positive viscosity. -/
theorem candidateStatement (ν : ℝ) (hν : 0 < ν) :
    ProblemStatement.candidateStatement ν := by
  obtain ⟨u, p, f, K, hc, _⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc⟩

/-- The candidate construction is unconditional for every positive viscosity. -/
theorem coreBreakdownStatement : ProblemStatement.coreBreakdownStatement :=
  candidateStatement

/-- The whole-space breakdown assertion is an unconditional theorem. -/
theorem breakdownStatement : ProblemStatement.breakdownStatement := theorem_1_1

/-- Theorem 1.1 and all energy conclusions of Lemma 10.4 hold for the same
constructed fields. Total dissipation is explicitly integrable up to time one. -/
theorem theorem_1_1_with_dissipation (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧
      ¬ Nonempty (GlobalFiniteEnergySolution ν f) ∧
      IntervalIntegrable (CompactEnergy.l2Norm f) volume 0 1 ∧
      IntegrableOn (CompactEnergy.dissipation u) (Ico (0 : ℝ) 1) ∧
      (∀ T ∈ Ico (0 : ℝ) 1,
        CompactEnergy.l2Sq u T +
          2 * ν * (∫ t in (0 : ℝ)..T, CompactEnergy.dissipation u t) ≤
            (CompactEnergy.cumulativeForceNorm f T) ^ 2) ∧
      2 * ν * (∫ t in Ico (0 : ℝ) 1, CompactEnergy.dissipation u t) ≤
        (CompactEnergy.cumulativeForceNorm f 1) ^ 2 := by
  obtain ⟨u, p, f, K, hc, hg⟩ := theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, CompactEnergy.candidate_energy_estimates hν hc⟩

end NavierStokesR3
