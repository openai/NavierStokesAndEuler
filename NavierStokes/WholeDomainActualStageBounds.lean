import NavierStokes.WholeDomainStageBounds
import NavierStokes.ActualCandidateAssembly

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement CorrectionInitialization
open CorrectionInitialization.ActualPrimary ActualCandidateAssembly PhysicalWaveSum
open scoped Topology ContDiff BigOperators

/-- One common scale for every finite stage and every derivative order. -/
noncomputable def commonQ (B N0 : ℕ) : ℝ :=
  ChartScales.Q (ActualCandidateConstruction.residualBand B N0)

theorem commonQ_pos (B N0 : ℕ) : 0 < commonQ B N0 := ChartScales.Q_pos _

theorem commonQ_le_one (B N0 : ℕ) : commonQ B N0 ≤ 1 := ChartScales.Q_le_one _

theorem commonQ_lt_original (B N0 : ℕ) : commonQ B N0 < ActualCandidateConstruction.qbig B N0 := by
  have he := ActualCandidateConstruction.twice_residual_scale B N0
  have hp := commonQ_pos B N0
  change 2 * commonQ B N0 = _ at he
  linarith

noncomputable abbrev finiteVelocity (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J : ℕ) : VelocityField :=
  MixedDiagonalResidual.uncutVelocity (potentialStages B N0 hN) (directStages B N0 hN) J

noncomputable abbrev finitePressure (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J : ℕ) : PressureField :=
  DiagonalJetBounds.uncutPrefix (pressureStages B N0 hN) (J+1)

/-- The literal finite prefixes satisfy the manuscript's residual gain at
every point of one common domain. The excluded flat errors have already
been estimated at the same power and included in this bound. -/
theorem actual_finite_residual_bound (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (J m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h (commonQ B N0),
      ‖iteratedFDeriv ℝ m (fun z => navierStokesResidual
        (finiteVelocity B N0 hN J) (finitePressure B N0 hN J) z.1 z.2) w‖ ≤
      C * physicalQ h w ^ (h * ActualIterationLedger.sigma J - ActualCycleResidualBounds.fixedLoss m) := by
  obtain ⟨C,hC,hb⟩ := invariant_residual_bound
    (ActualCyclePreservation.broad_invariant (ActualCyclePreservation.state_invariant B N0 hN J)) hN
    (ActualCandidateConstruction.residualBand_four B N0)
    (ActualCandidateConstruction.cycle_base_error B N0 J) (physicalData B N0 hN J) m
  refine ⟨C,hC,?_⟩
  intro w hw
  have hq := hw.2.le.trans (commonQ_le_one B N0)
  exact (hb w hw hq).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
      hq (by nlinarith [outgoing.data.h_pos])) hC)

end NavierStokes.WholeDomainStageBounds
