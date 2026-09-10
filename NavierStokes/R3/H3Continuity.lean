import NavierStokes.R3.H3Definitions
import NavierStokes.R3.H3CompactHelpers

/-! # Continuity in the whole-space derivative H³ norm

The continuity assertion below uses the H³ norm of the difference of two
spatial fields. Thus it controls convergence of every spatial derivative
through order three in genuine Lebesgue L², rather than merely continuity of
the scalar norm of a field.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Compact
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- Continuity in the derivative H³ topology on a time set. All derivatives
through order three are square integrable at every time. -/
def H3ContinuousOn (u : VelocityField) (s : Set ℝ) : Prop :=
  (∀ t ∈ s, HasFiniteH3 (fun x => u (t, x))) ∧
    ∀ t ∈ s, Tendsto (fun r => derivativeH3Norm (fun x => u (r, x) - u (t, x)))
      (𝓝[s] t) (𝓝 0)

theorem finiteH3_of_compact_slab {a b : ℝ} (hab : a < b) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    {t : ℝ} (ht : t ∈ Icc a b) : HasFiniteH3 (fun x => u (t, x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact partialWord_square_integrable hab hK hu hsupp [] ht
  · intro i
    exact partialWord_square_integrable hab hK hu hsupp [i] ht
  · intro i j
    exact partialWord_square_integrable hab hK hu hsupp [i, j] ht
  · intro i j k
    exact partialWord_square_integrable hab hK hu hsupp [i, j, k] ht

theorem continuousOn_derivativeH3Energy_of_compact_slab {a b : ℝ} (hab : a < b)
    {u : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) :
    ContinuousOn (fun t => derivativeH3Energy (fun x => u (t, x))) (Icc a b) := by
  have hc (is : List (Fin 3)) := partialWord_square_continuousOn hab hK hu hsupp is
  have hm : ContinuousOn (fun t => mixedEnergy (fun x => u (t, x))) (Icc a b) :=
    (((((((hc []).add (hc [0])).add (hc [1])).add (hc [2])).add
      (hc [1, 0])).add (hc [2, 0])).add (hc [2, 1])).add (hc [2, 1, 0])
  apply (hm.add ?_).add ?_
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact hc [i, j]
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    apply continuousOn_finsetSum
    intro k _
    exact hc [i, j, k]

theorem continuousOn_derivativeH3Norm_of_compact_slab {a b : ℝ} (hab : a < b)
    {u : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) :
    ContinuousOn (fun t => derivativeH3Norm (fun x => u (t, x))) (Icc a b) :=
  (continuousOn_derivativeH3Energy_of_compact_slab hab hK hu hsupp).sqrt

@[simp] theorem derivativeH3Norm_zero : derivativeH3Norm (fun _ : Space => (0 : Space)) = 0 := by
  have hz (i : Fin 3) : spatialPartial i (fun _ : Space => (0 : Space)) = fun _ => 0 := by
    funext x
    simp [spatialPartial]
  simp [derivativeH3Norm, derivativeH3Energy, mixedEnergy, squareEnergy, hz]

/-- Uniform compact support and joint smoothness imply actual H³ norm
continuity, including the endpoints of a closed time interval. -/
theorem h3ContinuousOn_of_compact_slab {a b : ℝ} (hab : a < b)
    {u : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) :
    H3ContinuousOn u (Icc a b) := by
  refine ⟨fun t ht => finiteH3_of_compact_slab hab hK hu hsupp ht, ?_⟩
  intro t ht
  let w : VelocityField := fun z => u z - u (t, z.2)
  have hw : ContDiffOn ℝ ∞ w (slab a b) :=
    hu.sub (((spatial_smooth hu ht).comp contDiff_snd).contDiffOn)
  have hs : ∀ r ∈ Icc a b, tsupport (fun x => w (r, x)) ⊆ K := by
    intro r hr
    exact (tsupport_sub _ _).trans (union_subset (hsupp r hr) (hsupp t ht))
  have hc := (continuousOn_derivativeH3Norm_of_compact_slab hab hK hw hs) t ht
  simpa only [ContinuousWithinAt, w, sub_self, derivativeH3Norm_zero] using hc

/-- The paper's compact candidate belongs to C([0,T];H³(ℝ³)) for every
positive T strictly below one. -/
theorem candidate_h3ContinuousOn {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K)
    {T : ℝ} (hT0 : 0 < T) (hT : T < 1) : H3ContinuousOn u (Icc 0 T) := by
  have hsub : slab 0 T ⊆ preSingularDomain := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
  exact h3ContinuousOn_of_compact_slab hT0 h.support_compact (h.velocity_smooth.mono hsub)
    (fun t ht => h.velocity_support t ⟨ht.1, ht.2.trans_lt hT⟩)

end NavierStokesR3.H3Embedding
