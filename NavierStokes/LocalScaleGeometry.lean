import NavierStokes.PhysicalWaveSum

/-!
# Spatial and temporal bounds in terms of the physical similarity scale

A bound on the similarity radius, together with a small physical scale,
forces the spacetime point to approach the singular point `(1, 0)`.
-/

noncomputable section

namespace NavierStokes.LocalScaleGeometry

open PhysicalWaveSum (physicalQ)

abbrev SpaceTime := ProblemStatement.SpaceTime

/-- The equation defining the physical similarity coordinate. -/
theorem physicalQ_equation {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) :
    physicalQ h w - (w.2 2) ^ 2 * physicalQ h w ^ (2 * h) = 1 - w.1 := by
  exact (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith)
    (p := (1 - w.1, w.2 2)) (sub_pos.mpr ht)).2

/-- The time distance to the terminal time is bounded by the scale. -/
theorem time_dist_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) : |w.1 - 1| ≤ physicalQ h w := by
  have he := physicalQ_equation hh hh1 ht
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hp : 0 ≤ (w.2 2) ^ 2 * physicalQ h w ^ (2 * h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hq.le _)
  rw [abs_of_neg (sub_neg.mpr ht)]
  linarith

/-- The axial coordinate shrinks with a positive power of the scale. -/
theorem axial_sq_le {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1) :
    (w.2 2) ^ 2 ≤ physicalQ h w ^ (1 - 2 * h) := by
  have he := physicalQ_equation hh hh1 ht
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hp := Real.rpow_pos_of_pos hq (2 * h)
  have hproduct : physicalQ h w ^ (2 * h) * physicalQ h w ^ (1 - 2 * h) =
      physicalQ h w := by
    rw [← Real.rpow_add hq, show 2 * h + (1 - 2 * h) = 1 by ring, Real.rpow_one]
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [hproduct]
  linarith

/-- Bounded similarity radius and vanishing scale force the spatial norm
to vanish. No sign assumption on the radius bound is needed here. -/
theorem spatial_norm_sq_le {h X1 : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (ht : w.1 < 1)
    (hX : AxisymmetricFields.radialEnergy w.2 / physicalQ h w ≤ X1) :
    ‖w.2‖ ^ 2 ≤ 2 * X1 * physicalQ h w + physicalQ h w ^ (1 - 2 * h) := by
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hr := (div_le_iff₀ hq).mp hX
  have hz := axial_sq_le hh hh1 ht
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  dsimp only [AxisymmetricFields.radialEnergy] at hr
  nlinarith

end NavierStokes.LocalScaleGeometry
