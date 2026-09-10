import NavierStokes.R3.H3CompactCurve
import NavierStokes.R3.H3StrongSolution

/-! # Whole-space H³ blowup and the exclusion of H³ continuation

The obstruction is the actual Sobolev norm and its continuous topology. It
applies to weak H³ spatial fields, rather than a class requiring C∞ velocity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace NavierStokesR3.H3Embedding

open ProblemStatement H3Comparison
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

theorem candidate_spatial_norm_bound {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x : Space) :
    ‖u (t, x)‖ ≤ 3 * derivativeH3Norm (fun x => u (t, x)) := by
  let T : ℝ := (t + 1) / 2
  have hT0 : 0 < T := by dsimp [T]; linarith [ht.1]
  have hT : T < 1 := by dsimp [T]; linarith [ht.2]
  have htT : t ∈ Icc (0 : ℝ) T := by
    refine ⟨ht.1, ?_⟩
    dsimp [T]
    linarith [ht.2]
  have hu : ContDiffOn ℝ ∞ u (slab 0 T) :=
    h.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩)
  have hs := fun s (hs : s ∈ Icc (0 : ℝ) T) =>
    h.velocity_support s ⟨hs.1, hs.2.trans_lt hT⟩
  exact norm_le_three_derivativeH3Norm (spatial_smooth hu htT)
    (finiteH3_of_compact_slab hT0 h.support_compact hu hs htT) x

/-- The actual Euclidean H³ norm is unbounded in every left neighborhood of
the singular time. The norm uses genuine integrable derivatives. -/
theorem candidate_h3Norm_unbounded {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K) :
    ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ 1 - δ < t ∧
        M < derivativeH3Norm (fun x => u (t, x)) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h.speed_unbounded (3 * M) (by positivity) δ hδ
  refine ⟨t, ht, hnear, ?_⟩
  have hb := candidate_spatial_norm_bound h ⟨ht.1.le, ht.2⟩ x
  linarith

/-- Any H³-continuous extension through time one would uniformly bound the
pre-singular velocity, contradicting the proved speed blowup. -/
theorem candidate_no_h3_continuation {ν : ℝ} {u v : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties ν u p f K)
    (hv : H3Curve v (Icc (0 : ℝ) 1))
    (hagrees : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, u (t, x) = v (t, x)) : False := by
  obtain ⟨B, hB⟩ := hv.uniform_speed_bound
  have hpos : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max B 1) hpos 1 zero_lt_one
  rw [hagrees t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge ((hB t ⟨ht.1.le, ht.2.le⟩ x).trans (le_max_left B 1))) hlarge

/-- This no-continuation result applies directly to the ordinary classical
H³ solution interface. Velocity agreement, when needed for uniqueness of the
maximal lifespan, is a separate conclusion of the comparison theorem. -/
theorem candidate_no_classicalH3_extension {ν : ℝ} {u v : VelocityField}
    {p q : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) {T : ℝ} (hT : 1 < T)
    (hv : ClassicalH3Solution ν f (fun _ => 0) T v q)
    (hagrees : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, u (t, x) = v (t, x)) : False := by
  let S : ℝ := (1 + T) / 2
  have hS : 1 < S := by dsimp [S]; linarith
  have hST : S < T := by dsimp [S]; linarith
  have hs := hv.on_shorter_interval S ⟨zero_lt_one.trans hS, hST⟩
  exact candidate_no_h3_continuation h (hs.curve.restrict
    (fun t ht => ⟨ht.1, ht.2.trans hS.le⟩)) hagrees

end NavierStokesR3.H3Embedding
