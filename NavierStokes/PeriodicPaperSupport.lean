import NavierStokes.PeriodicLocalization
import NavierStokes.R3.ProblemStatement
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Support of the periodic construction on its fundamental cube

The periodic lift is not compactly supported on all of R³. These lemmas
record the correct support statement after intersecting its topological
support with the closed fundamental cube. An extension after the singular
time is used only to make the periodizing lattice family uniformly locally finite.
-/

noncomputable section

namespace NavierStokes.PeriodicPaper

open ProblemStatement PeriodicLocalization Set Filter
open scoped Topology ContDiff

/-- The interior of the centered fundamental unit cube. -/
def fundamentalInterior : Set Space := {x | ∀ i : Fin 3, |x i| < 1 / 2}

/-- The closed centered fundamental unit cube. -/
def fundamentalCube : Set Space := {x | ∀ i : Fin 3, |x i| ≤ 1 / 2}

/-- An arbitrary zero extension after the singular time. -/
def beforeOne {V : Type*} [Zero V] (g : SpaceTime → V) (z : SpaceTime) : V :=
  if z.1 < 1 then g z else 0

theorem beforeOne_eq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 1) : beforeOne g z = g z := by
  simp only [beforeOne, ite_eq_left hz]

theorem beforeOne_eventuallyEq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 1) : beforeOne g =ᶠ[𝓝 z] g := by
  filter_upwards [continuous_fst.continuousAt.eventually_lt_const hz] with w hw
  exact beforeOne_eq g hw

theorem beforeOne_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain) :
    ContDiffOn ℝ ∞ (beforeOne g) preSingularDomain := by
  apply hg.congr
  intro z hz
  exact beforeOne_eq g hz.1.2

theorem beforeOne_supported {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {r : ℝ}
    (hg : ∀ t < (1 : ℝ), ∀ x : Space, g (t, x) ≠ 0 → ∀ i, |x i| ≤ r) :
    SupportedInCube r (beforeOne g) := by
  intro z hz
  by_cases ht : z.1 < 1
  · exact hg z.1 ht z.2 (by simpa only [beforeOne, ite_eq_left ht] using hz)
  · exact False.elim (hz (by simp only [beforeOne, ite_eq_right ht]))

/-- Lattice periodization preserves unbounded speed when the original
support is contained strictly within the fundamental cube. -/
theorem speedUnbounded_periodize {u : VelocityField} {r : ℝ}
    (hu : SupportedInCube r u) (hr : r < 1 / 2) (h : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (periodize u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h M hM δ hδ
  have hne : u (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hx : ∀ i : Fin 3, |x i| ≤ 1 / 2 :=
    fun i => (hu (t, x) hne i).trans hr.le
  exact ⟨t, x, ht, hnear, by rwa [periodize_eq_on_unitCube hu hr hx]⟩

theorem speedUnbounded_beforeOne {u : VelocityField} (h : SpeedUnboundedAtOne u) :
    SpeedUnboundedAtOne (beforeOne u) := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := h M hM δ hδ
  exact ⟨t, x, ht, hnear, by rwa [beforeOne_eq u ht.2]⟩

/-- Inside the closed fundamental cube the support of the periodized field
is contained in the original compact set, including at cube boundary points. -/
theorem periodize_tsupport_on_fundamentalCube {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {r : ℝ} {K : Set Space}
    (hg : SupportedInCube r g) (hr : r < 1 / 2) {t : ℝ}
    (hK : tsupport (fun x : Space => g (t, x)) ⊆ K) :
    tsupport (fun x : Space => periodize g (t, x)) ∩ fundamentalCube ⊆ K := by
  rintro x ⟨hx, hcube⟩
  by_contra hnot
  have hnotg : x ∉ tsupport (fun y : Space => g (t, y)) := fun h => hnot (hK h)
  have hzero := notMem_tsupport_iff_eventuallyEq.mp hnotg
  have hinner : x ∈ innerCube r := by
    intro i
    have := hcube i
    linarith
  have heq : (fun y : Space => periodize g (t, y)) =ᶠ[𝓝 x]
      (fun y : Space => g (t, y)) := by
    filter_upwards [(isOpen_innerCube r).mem_nhds hinner] with y hy
    exact periodize_eq_on_innerCube hg hy t
  exact (notMem_tsupport_iff_eventuallyEq.mpr (heq.trans hzero)) hx

/-- Compact spacetime support gives a common future time endpoint. -/
theorem compactFutureTimeSupport_of_hasCompactSupport {f : VelocityField}
    (hf : HasCompactSupport f) : CompactFutureTimeSupport f := by
  obtain ⟨B, hB⟩ := (hf.image continuous_fst).bddAbove
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro t ht x
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have hBt : t ≤ B := hB ⟨(t, x), hz, rfl⟩
  have := le_max_left B 0
  linarith

end NavierStokes.PeriodicPaper
