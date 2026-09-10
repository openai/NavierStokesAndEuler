import NavierStokes.SharpPhysicalLogBounds
import NavierStokes.MixedFiniteBackground

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Function Filter ProblemStatement PhysicalWaveSum SharpGluedStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss is selected before the length of the finite prefix. -/
def prefixLoss (initial positive : ℕ → ℝ) (m : ℕ) : ℝ := max (initial m) (positive m)

section Prefix

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {F : ℕ → SpaceTime → V} {gain initial positive : ℕ → ℝ}

theorem prefix_log_bound (hh : 0 < h) (hh1 : h < 1/2)
    (hs : ∀ j, ContDiffOn ℝ ∞ (F j) (CutStageEstimates.physicalSublevel h qbig))
    (hgain : ∀ j, 0 ≤ gain j)
    (hzero : ∀ m, LogBound h qbig (F 0) m (-initial m))
    (hpos : ∀ j m, LogBound h qbig (F (j+1)) m (gain (j+1)-positive m))
    (J m : ℕ) :
    LogBound h qbig (DiagonalJetBounds.uncutPrefix F (J+1)) m (-prefixLoss initial positive m) := by
  apply LogBound.finset_sum (Finset.range (J+1)) hh hh1 (fun j _ => hs j)
  intro j _
  cases j with
  | zero => exact (hzero m).weaken hh hh1 (neg_le_neg (le_max_left _ _))
  | succ j =>
    apply (hpos j m).weaken hh hh1
    have hp : positive m ≤ prefixLoss initial positive m := le_max_right _ _
    linarith [hgain (j+1)]

end Prefix

theorem finite_velocity_log_bound {h qbig : ℝ} {A B : ℕ → VelocityField}
    {gain initial positive : ℕ → ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig))
    (hgain : ∀ j, 0 ≤ gain j)
    (hzero : ∀ m, LogBound h qbig (MixedDiagonalResidual.uncutVelocity A B 0) m (-initial m))
    (hpos : ∀ j m, LogBound h qbig (MixedFiniteBackground.stageVelocity A B (j+1)) m
      (gain (j+1)-positive m)) (J m : ℕ) :
    LogBound h qbig (MixedDiagonalResidual.uncutVelocity A B J) m (-prefixLoss initial positive m) := by
  have hU := CutStageEstimates.physicalSublevel_open hh hh1 qbig
  have hs : ∀ j, ContDiffOn ℝ ∞ (MixedFiniteBackground.stageVelocity A B j)
      (CutStageEstimates.physicalSublevel h qbig) := by
    intro j
    apply ContDiffOn.add _ (hB j)
    intro w hw
    exact (SpatialCurl.contDiffAt_spatialCurl ((hA j).contDiffAt (hU.mem_nhds hw))
      (by simp)).contDiffWithinAt
  have hz : ∀ m, LogBound h qbig (MixedFiniteBackground.stageVelocity A B 0) m (-initial m) := by
    intro m
    simpa only [MixedFiniteBackground.uncutVelocity_zero] using hzero m
  exact (prefix_log_bound hh hh1 hs hgain hz hpos J m).congr hh hh1
    (MixedFiniteBackground.uncutVelocity_eq_stagePrefix hU A B hA J).symm

end NavierStokes.WholeDomainStageBounds
