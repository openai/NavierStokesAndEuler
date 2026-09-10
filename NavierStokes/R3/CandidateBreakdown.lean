import NavierStokes.R3.WholeSpaceUniqueness

/-!
# A compact singular candidate excludes a global finite-energy solution

The comparison theorem identifies the two velocities before time one. The
candidate's fixed compact spatial support then confines its unbounded speed
to a compact spacetime set on which a global smooth velocity is bounded.
-/

noncomputable section

open Set
open scoped ContDiff

namespace NavierStokesR3.ProblemStatement

theorem CandidateProperties.not_global_agreement {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) {v : VelocityField}
    (hv : ContDiffOn ℝ ∞ v futureDomain) :
    ¬ (∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v (t, x)) := by
  intro heq
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ futureDomain :=
    fun _ hz => ⟨hz.1.1, mem_univ _⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod h.support_compact).exists_bound_of_continuousOn
    (hv.continuousOn.mono hsub)
  have hpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨t, x, ht, _, hlarge⟩ := h.speed_unbounded (max M 1) hpos 1 zero_lt_one
  have hx : x ∈ K := by
    apply h.velocity_support t ⟨ht.1.le, ht.2⟩
    apply subset_tsupport
    intro hz
    change u (t, x) = 0 at hz
    rw [hz, norm_zero] at hlarge
    exact (not_lt_of_ge hpos.le) hlarge
  have hb := hM (t, x) ⟨⟨ht.1.le, ht.2.le⟩, hx⟩
  rw [heq t ⟨ht.1.le, ht.2⟩ x] at hlarge
  exact (not_lt_of_ge (hb.trans (le_max_left M 1))) hlarge

/-- The comparison class has only smoothness, the equation, zero initial
velocity, and a uniform energy bound; no support assumption is imposed on it. -/
theorem CandidateProperties.no_global_solution_one
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties 1 u p f K) :
    ¬ Nonempty (GlobalFiniteEnergySolution 1 f) := by
  rintro ⟨v⟩
  exact h.not_global_agreement v.velocity_smooth
    (WholeSpaceUniqueness.candidate_global_agrees_before_one h v)

/-- A force in the paper's support class which excludes a global solution
must be nonzero at some positive time. -/
theorem force_nonzero_of_no_global_solution {ν : ℝ} {f : VelocityField}
    (hf : CompactPositiveTimeSupport f)
    (h : ¬ Nonempty (GlobalFiniteEnergySolution ν f)) :
    ∃ t : ℝ, 0 < t ∧ ∃ x : Space, f (t, x) ≠ 0 := by
  have hne : f ≠ fun _ => 0 := by
    intro he
    subst f
    exact h (zero_force_has_global_solution ν)
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hne
  exact ⟨z.1, (hf.2 (subset_tsupport _ hz)).1, z.2, hz⟩

/-- One bound for the actual spatial square integrals, with integrability
proved separately so that the totalized integral cannot hide infinite energy. -/
theorem CandidateProperties.uniform_l2_sq_bound {ν : ℝ}
    {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (h : CandidateProperties ν u p f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      SquareIntegrableAtTime u t ∧ (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ C := by
  obtain ⟨E, hE, hb⟩ := h.energy_bounded
  refine ⟨2 * E, by positivity, ?_⟩
  intro t ht
  obtain ⟨hi, he⟩ := hb t ht
  refine ⟨hi, ?_⟩
  change (1 / 2 : ℝ) * (∫ x : Space, ‖u (t, x)‖ ^ 2) ≤ E at he
  linarith

end NavierStokesR3.ProblemStatement
