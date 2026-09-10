import NavierStokes.LocalScaleGeometry
import NavierStokes.DiagonalResidual
import NavierStokes.SpacetimeEndpoint

/-!
# Uniform small-scale bounds at bounded similarity radius

The physical similarity scale controls distance to the singular point whenever
`X = radialEnergy / q` remains bounded. Consequently a jet estimate in the
ordinary punctured spacetime neighborhood gives a bound uniform over every
fixed finite range of `X`, for all sufficiently small positive scales.
-/

noncomputable section

namespace NavierStokes.LocalScaleApproach

open Set Filter ProblemStatement
open scoped Topology

/-- An explicit majorant for spacetime distance in the similarity region. -/
def approachMajorant (h X q : ℝ) : ℝ :=
  q + Real.sqrt (2 * X * q + q ^ (1 - 2 * h))

theorem approachMajorant_continuous {h : ℝ} (hh1 : h < 1 / 2) (X : ℝ) :
    Continuous (approachMajorant h X) := by
  have hexp : 0 ≤ 1 - 2 * h := by linarith
  exact continuous_id.add
    (((continuous_const.mul continuous_id).add (Real.continuous_rpow_const hexp)).sqrt)

@[simp] theorem approachMajorant_zero {h : ℝ} (hh1 : h < 1 / 2) (X : ℝ) :
    approachMajorant h X 0 = 0 := by
  have hexp : 1 - 2 * h ≠ 0 := by linarith
  simp [approachMajorant, Real.zero_rpow hexp]

/-- Bounded similarity radius and a small scale force a point into any given
ordinary neighborhood of `(1,0)`. -/
theorem small_scale_mem_nhds {h X : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hX : 0 ≤ X) {U : Set SpaceTime} (hU : U ∈ 𝓝 ((1 : ℝ), (0 : Space))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : SpaceTime, w.1 < 1 →
      PhysicalWaveSum.physicalQ h w < δ →
      AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
      w ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hmajor : ∀ᶠ q : ℝ in 𝓝 0, approachMajorant h X q < ε := by
    have hm := (approachMajorant_continuous hh1 X).tendsto 0
    rw [approachMajorant_zero hh1 X] at hm
    exact hm.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hmajor
  refine ⟨δ, hδ, ?_⟩
  intro w ht hq hXw
  have hqpos := PhysicalWaveSum.physicalQ_pos hh hh1 ht
  have hnear : approachMajorant h X (PhysicalWaveSum.physicalQ h w) < ε :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right,
      Real.norm_of_nonneg hqpos.le] using hq)
  have hspace := LocalScaleGeometry.spatial_norm_sq_le hh hh1 ht hXw
  have htime := LocalScaleGeometry.time_dist_le hh hh1 ht
  have hnorm : ‖w.2‖ ≤
      Real.sqrt (2 * X * PhysicalWaveSum.physicalQ h w +
        PhysicalWaveSum.physicalQ h w ^ (1 - 2 * h)) := by
    apply (Real.le_sqrt (norm_nonneg _) _).mpr hspace
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hX) hqpos.le)
      (Real.rpow_nonneg hqpos.le _)
  apply hball
  rw [Metric.mem_ball, Prod.dist_eq]
  have hqle : PhysicalWaveSum.physicalQ h w ≤
      approachMajorant h X (PhysicalWaveSum.physicalQ h w) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hsle : Real.sqrt (2 * X * PhysicalWaveSum.physicalQ h w +
      PhysicalWaveSum.physicalQ h w ^ (1 - 2 * h)) ≤
      approachMajorant h X (PhysicalWaveSum.physicalQ h w) :=
    le_add_of_nonneg_left hqpos.le
  apply max_lt
  · simpa only [Real.dist_eq] using htime.trans_lt (hqle.trans_lt hnear)
  · simpa only [dist_zero_right] using hnorm.trans_lt (hsle.trans_lt hnear)

/-- Any eventual property at the singular point holds uniformly for bounded
similarity radius once the physical scale is sufficiently small. -/
theorem uniform_small_scale_of_eventually {h X : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hX : 0 ≤ X) {P : SpaceTime → Prop}
    (hP : ∀ᶠ w in 𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space)), P w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : SpaceTime, w.1 < 1 →
      PhysicalWaveSum.physicalQ h w < δ →
      AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
      P w := by
  obtain ⟨U, hU, hx, hUP⟩ := mem_nhdsWithin.mp hP
  obtain ⟨δ, hδ, hd⟩ := small_scale_mem_nhds hh hh1 hX (hU.mem_nhds hx)
  exact ⟨δ, hδ, fun w ht hq hXw => hUP ⟨hd w ht hq hXw, ht, mem_univ _⟩⟩

/-- A joint spacetime jet rate gives the exact uniform small-`q` estimate on
every finite similarity-radius range stated in the paper's local theorem. -/
theorem jetRate_uniform_small_scale {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {f : SpaceTime → V} {m : ℕ} {r : ℝ}
    (hrate : DiagonalResidual.JetRate
      (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space)))
      (PhysicalWaveSum.physicalQ h) f m r) :
    ∀ X : ℝ, 0 ≤ X → ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ w : SpaceTime, w.1 < 1 → PhysicalWaveSum.physicalQ h w < δ →
        AxisymmetricFields.radialEnergy w.2 / PhysicalWaveSum.physicalQ h w ≤ X →
        ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  intro X hX
  obtain ⟨C, hC, hb⟩ := hrate
  obtain ⟨δ, hδ, hd⟩ := uniform_small_scale_of_eventually hh hh1 hX hb
  exact ⟨C, hC, δ, hδ, hd⟩

end NavierStokes.LocalScaleApproach
