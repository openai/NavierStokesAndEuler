import NavierStokes.ActualCurrentParticularBounds

/-! Bounds on the open profile annulus extend to its closed edges while
the physical similarity scale and the dyadic band remain fixed. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace NavierStokes.CurrentPhysicalRadialClosure

open ProblemStatement PhysicalWaveSum ActualCurrentWaveSupport

/-- Change only the transverse coordinates. -/
def radialScale (w : SpaceTime) (c : ℝ) : SpaceTime :=
  (w.1, c • w.2 + ((1 - c) * w.2 2) • EuclideanSpace.single 2 1)

theorem radialScale_continuous (w : SpaceTime) : Continuous (radialScale w) := by
  exact continuous_const.prodMk ((continuous_id.smul continuous_const).add
    (((continuous_const.sub continuous_id).mul continuous_const).smul continuous_const))

@[simp] theorem radialScale_one (w : SpaceTime) : radialScale w 1 = w := by
  simp [radialScale]

@[simp] theorem radialScale_time (w : SpaceTime) (c : ℝ) : (radialScale w c).1 = w.1 := rfl

@[simp] theorem radialScale_axial (w : SpaceTime) (c : ℝ) :
    (radialScale w c).2 2 = w.2 2 := by
  simp only [radialScale, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.single_apply, ite_eq_left, mul_one]
  ring

@[simp] theorem radialScale_q (h : ℝ) (w : SpaceTime) (c : ℝ) :
    physicalQ h (radialScale w c) = physicalQ h w := by
  simp only [physicalQ, SimilarityProfile.q, AxisymmetricFields.profilePoint,
    radialScale_time, radialScale_axial]

theorem radialScale_projection (w : SpaceTime) (c : ℝ) :
    PhysicalGraphBounds.radialProjection (radialScale w c) =
      c • PhysicalGraphBounds.radialProjection w := by
  ext <;> simp [PhysicalGraphBounds.radialProjection_apply, radialScale]

theorem radialScale_radius (h : ℝ) (w : SpaceTime) {c : ℝ} (hc : 0 < c) :
    profileRadius h (radialScale w c) = c * profileRadius h w := by
  simp only [profileRadius, AnnularEndpoint.radius, radialScale_projection,
    PolarCharts.radius_smul hc, radialScale_q]
  ring

/-- Every closed-annulus point is a limit of strict-annulus points in its
same physical-scale fiber, hence in the same open dyadic band. -/
theorem closed_mem_closure_fiber {h a b : ℝ} (ha : 0 < a) (hab : a < b)
    {n : ℕ} {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hr : profileRadius h w ∈ Icc a b) :
    w ∈ closure {y : SpaceTime | y ∈ ValidDyadicBandCover.band h n ∧
      physicalQ h y = physicalQ h w ∧ profileRadius h y ∈ Ioo a b} := by
  have hR : 0 < profileRadius h w := ha.trans_le hr.1
  let g : ℝ → SpaceTime := fun r => radialScale w (r / profileRadius h w)
  have hg : Continuous g := (radialScale_continuous w).comp
    (continuous_id.div_const _)
  have he : g (profileRadius h w) = w := by
    simp only [g, div_self hR.ne', radialScale_one]
  have hmap : MapsTo g (Ioo a b) {y : SpaceTime |
      y ∈ ValidDyadicBandCover.band h n ∧ physicalQ h y = physicalQ h w ∧
        profileRadius h y ∈ Ioo a b} := by
    intro r hrr
    have hc : 0 < r / profileRadius h w := div_pos (ha.trans hrr.1) hR
    have hband : g r ∈ ValidDyadicBandCover.band h n := by
      simpa only [ValidDyadicBandCover.band, mem_ofPred_eq, preterminal, g,
        radialScale_time, radialScale_q] using hw
    refine ⟨hband, radialScale_q _ _ _, ?_⟩
    change profileRadius h (radialScale w (r / profileRadius h w)) ∈ Ioo a b
    rwa [radialScale_radius h w hc, div_mul_cancel₀ _ hR.ne']
  have hcl : g (profileRadius h w) ∈ closure (g '' Ioo a b) := by
    apply mem_closure_image hg.continuousAt
    rw [closure_Ioo hab.ne]
    exact hr
  rw [he] at hcl
  exact closure_mono hmap.image_subset hcl

/-- A bound depending arbitrarily on the physical scale extends to both
annulus edges. No continuity assumption on the scale bound is needed. -/
theorem jet_bound_on_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b)
    {n : ℕ} {f : SpaceTime → E}
    (hf : ContDiffOn ℝ ∞ f (ValidDyadicBandCover.band h n))
    (m : ℕ) (bound : ℝ → ℝ) {qcap : ℝ}
    (hb : ∀ y ∈ ValidDyadicBandCover.band h n, physicalQ h y ≤ qcap →
      profileRadius h y ∈ Ioo a b → ‖iteratedFDeriv ℝ m f y‖ ≤ bound (physicalQ h y))
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hq : physicalQ h w ≤ qcap) (hr : profileRadius h w ∈ Icc a b) :
    ‖iteratedFDeriv ℝ m f w‖ ≤ bound (physicalQ h w) := by
  apply LocalPhysicalCopyBounds.jet_bound_at_closure
    (hf.contDiffAt ((ValidDyadicBandCover.band_open hh hh1 n).mem_nhds hw))
    (closed_mem_closure_fiber ha hab hw hr) m
  intro y hy
  simpa only [hy.2.1] using hb y hy.1 (hy.2.1 ▸ hq) hy.2.2

end NavierStokes.CurrentPhysicalRadialClosure
