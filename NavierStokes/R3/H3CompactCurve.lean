import NavierStokes.R3.H3Curve

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding H3Compact
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- A compactly supported smooth spacetime field gives a continuous curve in
the ordinary L² space, including closed time endpoints. -/
theorem continuous_compact_slices_toLp {a b : ℝ} (hab : a < b)
    {u : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    {hm : ∀ t : Icc a b, MemLp (fun x => u (t, x)) 2 volume} :
    Continuous (fun t : Icc a b => (hm t).toLp (fun x => u (t, x))) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let w : VelocityField := fun z => u z - u (t, z.2)
  have hw : ContDiffOn ℝ ∞ w (slab a b) :=
    hu.sub (((spatial_smooth hu t.property).comp contDiff_snd).contDiffOn)
  have hs : ∀ r ∈ Icc a b, tsupport (fun x => w (r, x)) ⊆ K := by
    intro r hr
    exact (tsupport_sub _ _).trans (union_subset (hsupp r hr) (hsupp t t.property))
  have hc : Continuous (fun r : Icc a b => Real.sqrt (squareEnergy (fun x => w (r, x)))) :=
    continuousOn_iff_continuous_domRestrict.mp
      (partialWord_square_continuousOn hab hK hw hs []).sqrt
  have he (r : Icc a b) :
      ‖(hm r).toLp (fun x => u (r, x)) - (hm t).toLp (fun x => u (t, x))‖ =
        Real.sqrt (squareEnergy (fun x => w (r, x))) := by
    have hp := squareEnergy_eq_norm_toLp ((hm r).sub (hm t))
    rw [MemLp.toLp_sub] at hp
    rw [show (fun x => w (r, x)) = (fun x => u (r, x)) - (fun x => u (t, x)) from rfl,
      hp, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hc0 : Real.sqrt (squareEnergy (fun x => w (t, x))) = 0 := by
    simp [w, squareEnergy]
  simp_rw [he]
  exact hc0 ▸ hc.continuousAt.tendsto

/-- Compact joint smoothness supplies all genuine weak H³ jets and the
finite product of their L² topologies. -/
def h3Curve_of_compact_slab {a b : ℝ} (hab : a < b)
    {u : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) :
    H3Curve u (Icc a b) where
  first := fun i => partialField i u
  second := fun i j => partialField i (partialField j u)
  third := fun i j k => partialField i (partialField j (partialField k u))
  spatial_continuous := fun _t ht => (spatial_smooth hu ht).continuous
  approximation := fun t ht => H3Approximation.of_contDiff_compact (spatial_smooth hu ht)
    (CompactEnergy.slice_compact hK (hsupp t ht))
  velocity_continuous := continuous_compact_slices_toLp hab hK hu hsupp
  first_continuous := fun i => continuous_compact_slices_toLp hab hK
    (partialWord_contDiffOn hab hu [i]) (partialWord_support hsupp [i])
  second_continuous := fun i j => continuous_compact_slices_toLp hab hK
    (partialWord_contDiffOn hab hu [i, j]) (partialWord_support hsupp [i, j])
  third_continuous := fun i j k => continuous_compact_slices_toLp hab hK
    (partialWord_contDiffOn hab hu [i, j, k]) (partialWord_support hsupp [i, j, k])

/-- The exact candidate is a genuine C([0,T];H³(ℝ³)) curve for each shorter
positive closed interval, with no PDE-specific assumptions needed here. -/
def candidate_h3Curve {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K)
    {T : ℝ} (hT0 : 0 < T) (hT : T < 1) : H3Curve u (Icc 0 T) :=
  h3Curve_of_compact_slab hT0 h.support_compact
    (h.velocity_smooth.mono (fun _z hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩))
    (fun t ht => h.velocity_support t ⟨ht.1, ht.2.trans_lt hT⟩)

end NavierStokesR3.H3Comparison
