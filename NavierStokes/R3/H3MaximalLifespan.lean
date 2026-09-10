import NavierStokes.R3.H3CandidateStrong
import NavierStokes.R3.H3CandidateUniqueness
import NavierStokes.R3.H3Blowup
import NavierStokes.R3.Theorem

/-! # Exact maximal classical H³ lifespan on ℝ³

The solution class uses genuine weak H³ jets with their L² topology, actual
L² time differentiation, and the same forcing and initial velocity. No
periodicity or pressure normalization is imposed on competing solutions.
-/

noncomputable section

open Set

namespace NavierStokesR3.H3Comparison

open ProblemStatement H3Embedding

def ClassicalH3Solution.restrict {ν T S : ℝ} {f u : VelocityField} {p : PressureField}
    {initial : Space → Space} (h : ClassicalH3Solution ν f initial T u p)
    (hS : 0 < S) (hST : S ≤ T) : ClassicalH3Solution ν f initial S u p where
  lifespan_pos := hS
  initial_velocity := h.initial_velocity
  on_shorter_interval := fun R hR => h.on_shorter_interval R ⟨hR.1, hR.2.trans_le hST⟩

def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)

def HasClassicalH3Extension (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) : Prop :=
  ∃ S : ℝ, ∃ v : VelocityField, ∃ q : PressureField,
    T < S ∧ Nonempty (ClassicalH3Solution ν f initial S v q) ∧ VelocityAgreesOn T u v

def IsMaximalClassicalH3Solution (ν : ℝ) (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop :=
  Nonempty (ClassicalH3Solution ν f initial T u p) ∧ ¬HasClassicalH3Extension ν f initial T u

def admissibleH3Lifespans (ν : ℝ) (f : VelocityField) (initial : Space → Space) : Set ℝ :=
  {T | ∃ u : VelocityField, ∃ p : PressureField, Nonempty (ClassicalH3Solution ν f initial T u p)}

theorem candidate_agrees_with_classicalH3 {ν T : ℝ} {u v : VelocityField}
    {p q : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K)
    (hv : ClassicalH3Solution ν f (fun _ => 0) T v q) :
    VelocityAgreesOn (min 1 T) u v := by
  intro t ht x
  by_cases ht0 : t = 0
  · rw [ht0, h.zero_initial_velocity, hv.initial_velocity]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht1 : t < 1 := (lt_min_iff.mp ht.2).1
    have htT : t < T := (lt_min_iff.mp ht.2).2
    exact candidate_unique_on_Icc_h3 hν h ht1 (hv.on_shorter_interval t ⟨htpos, htT⟩)
      hv.initial_velocity t ⟨ht.1, le_rfl⟩ x

theorem candidate_classicalH3_lifespan_le_one {ν T : ℝ} {u v : VelocityField}
    {p q : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K)
    (hv : ClassicalH3Solution ν f (fun _ => 0) T v q) : T ≤ 1 := by
  by_contra hn
  have hT : 1 < T := lt_of_not_ge hn
  apply candidate_no_classicalH3_extension h hT hv
  simpa only [VelocityAgreesOn, min_eq_left hT.le] using candidate_agrees_with_classicalH3 hν h hv

theorem candidate_extends_shorter_classicalH3 {ν T : ℝ} {u v : VelocityField}
    {p q : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K)
    (hv : ClassicalH3Solution ν f (fun _ => 0) T v q) (hT : T < 1) :
    HasClassicalH3Extension ν f (fun _ => 0) T v := by
  refine ⟨1, u, p, hT, ⟨candidate_classicalH3Solution h⟩, ?_⟩
  intro t ht x
  exact (candidate_agrees_with_classicalH3 hν h hv t
    (by simpa only [min_eq_right hT.le] using ht) x).symm

theorem candidate_is_maximal_classicalH3 {ν : ℝ} {u : VelocityField}
    {p : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K) :
    IsMaximalClassicalH3Solution ν f (fun _ => 0) 1 u p := by
  refine ⟨⟨candidate_classicalH3Solution h⟩, ?_⟩
  rintro ⟨S, v, q, hS, ⟨hv⟩, _⟩
  exact (not_lt_of_ge (candidate_classicalH3_lifespan_le_one hν h hv)) hS

/-- Every maximal classical H³ solution for the same force and datum has
exactly the stated lifespan; a shorter maximal solution is also excluded by
actual extension using uniqueness. -/
theorem maximal_classicalH3_lifespan_eq_one {ν T : ℝ} {u v : VelocityField}
    {p q : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K)
    (hv : IsMaximalClassicalH3Solution ν f (fun _ => 0) T v q) : T = 1 := by
  obtain ⟨hvc⟩ := hv.1
  apply le_antisymm (candidate_classicalH3_lifespan_le_one hν h hvc)
  by_contra hn
  exact hv.2 (candidate_extends_shorter_classicalH3 hν h hvc (lt_of_not_ge hn))

theorem candidate_admissibleH3Lifespans {ν : ℝ} {u : VelocityField}
    {p : PressureField} {f : VelocityField} {K : Set Space}
    (hν : 0 < ν) (h : CandidateProperties ν u p f K) :
    admissibleH3Lifespans ν f (fun _ => 0) = Ioc (0 : ℝ) 1 := by
  ext T
  constructor
  · rintro ⟨v, q, ⟨hv⟩⟩
    exact ⟨hv.lifespan_pos, candidate_classicalH3_lifespan_le_one hν h hv⟩
  · intro hT
    exact ⟨u, p, ⟨(candidate_classicalH3Solution h).restrict hT.1 hT.2⟩⟩

/-- The full main theorem's actual Euclidean fields have maximal classical
H³ lifespan exactly one, for every positive viscosity. -/
theorem theorem_1_1_with_maximalH3 (ν : ℝ) (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      CandidateProperties ν u p f K ∧ ¬Nonempty (GlobalFiniteEnergySolution ν f) ∧
      IsMaximalClassicalH3Solution ν f (fun _ => 0) 1 u p ∧
      admissibleH3Lifespans ν f (fun _ => 0) = Ioc (0 : ℝ) 1 := by
  obtain ⟨u, p, f, K, hc, hg⟩ := NavierStokesR3.theorem_1_1 ν hν
  exact ⟨u, p, f, K, hc, hg, candidate_is_maximal_classicalH3 hν hc,
    candidate_admissibleH3Lifespans hν hc⟩

end NavierStokesR3.H3Comparison
