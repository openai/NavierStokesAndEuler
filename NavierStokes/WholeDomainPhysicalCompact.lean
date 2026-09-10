import NavierStokes.WholeDomainCompactBounds
import NavierStokes.PhysicalStageBounds

noncomputable section
namespace NavierStokes.WholeDomainStageBounds
open Set Filter Function ProblemStatement
open scoped Topology ContDiff BigOperators
open PhysicalWaveSum

/-- The sublevel has bounded axial coordinate, even though its radial
coordinate is unbounded. -/
theorem axial_abs_le_one {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ preterminal) (hq : physicalQ h w ≤ 1) :
    |w.2 2| ≤ 1 := by
  have hq0 := physicalQ_pos hh hh1 hw
  have hp : 0 < physicalQ h w ^ ((1 - 2*h)/2) := Real.rpow_pos_of_pos hq0 _
  have he := SimilarityCoordinates.coordinateEta_abs_lt_one
    (by linarith : 0 < 2*h) (by linarith : 2*h < 1)
    (p := (1-w.1,w.2 2)) (sub_pos.mpr hw)
  change |w.2 2 / physicalQ h w ^ ((1-2*h)/2)| < 1 at he
  rw [abs_div, abs_of_pos hp] at he
  have hz := (div_lt_one hp).mp he
  exact hz.le.trans (Real.rpow_le_one hq0.le hq (by linarith))

/-- A bounded similarity radius lies in one fixed compact physical ball
throughout the unit sublevel. -/
theorem in_compact_of_radial_bound {h R : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hR : 0 ≤ R) {w : SpaceTime} (hw : w ∈ preterminal) (hq : physicalQ h w ≤ 1)
    (hX : (SlowBorelBase.cartesianChart h w).2.1 ≤ R) :
    w ∈ Metric.closedBall (0 : SpaceTime) (R+2) := by
  have hq0 := physicalQ_pos hh hh1 hw
  have ht := PhysicalStageBounds.abs_time_le_one hh hh1 hw hq
  have hz := axial_abs_le_one hh hh1 hw hq
  have hr : AxisymmetricFields.radialEnergy w.2 ≤ R := by
    change AxisymmetricFields.radialEnergy w.2 / physicalQ h w ≤ R at hX
    exact ((div_le_iff₀ hq0).mp hX).trans ((mul_le_mul_of_nonneg_left hq hR).trans_eq (mul_one R))
  have hs := EuclideanSpace.real_norm_sq_eq w.2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change ‖w.2‖^2 = w.2 0^2 + (w.2 1^2 + w.2 2^2) at hs
  have hx : ‖w.2‖ ≤ R+2 := by
    have hzsq : (w.2 2)^2 ≤ 1 := by nlinarith [abs_le.mp hz]
    dsimp only [AxisymmetricFields.radialEnergy] at hr
    nlinarith [norm_nonneg w.2, sq_nonneg R]
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  exact ⟨(Real.norm_eq_abs w.1).trans_le (ht.trans (by linarith)), hx⟩

end NavierStokes.WholeDomainStageBounds
