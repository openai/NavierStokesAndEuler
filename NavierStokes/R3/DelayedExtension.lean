import NavierStokes.R3.ProblemStatement
import Mathlib.Tactic.Linarith

/-!
# Smooth extension by zero to negative times

A field that vanishes on a time interval around zero has a smooth extension by
zero to all negative times. The agreement with zero on an open neighborhood of
the seam proves every differentiability order at once.
-/

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set Filter
open scoped ContDiff Topology

/-- Keep the original field at nonnegative times and use zero before time zero. -/
def zeroBefore {V : Type*} [Zero V] (g : SpaceTime → V) (z : SpaceTime) : V :=
  if 0 ≤ z.1 then g z else 0

theorem zeroBefore_eq_of_nonneg {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 ≤ z.1) : zeroBefore g z = g z := by
  simp only [zeroBefore, ite_eq_left hz]

theorem zeroBefore_eq_zero_of_neg {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : z.1 < 0) : zeroBefore g z = 0 := by
  simp only [zeroBefore, ite_eq_right (not_le.mpr hz)]

theorem zeroBefore_eventuallyEq_of_pos {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 < z.1) : zeroBefore g =ᶠ[𝓝 z] g := by
  filter_upwards [continuous_fst.continuousAt.eventually_const_lt hz] with y hy
  exact zeroBefore_eq_of_nonneg g hy.le

theorem zeroBefore_eventuallyEq_zero_of_neg {V : Type*} [Zero V]
    (g : SpaceTime → V) {z : SpaceTime} (hz : z.1 < 0) :
    zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [continuous_fst.continuousAt.eventually_lt_const hz] with y hy
  exact zeroBefore_eq_zero_of_neg g hy

theorem zeroBefore_eq_zero_of_le {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 3 / 8) : zeroBefore g z = 0 := by
  by_cases ht : 0 ≤ z.1
  · rw [zeroBefore_eq_of_nonneg g ht]
    exact hzero z.1 (by rwa [abs_of_nonneg ht]) z.2
  · simp only [zeroBefore, ite_eq_right ht]

theorem zeroBefore_eq_zero_of_nonpos {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 0) : zeroBefore g z = 0 := by
  exact zeroBefore_eq_zero_of_le hzero (by linarith)

theorem zeroBefore_eventuallyEq_zero {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 < 3 / 8) :
    zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [continuous_fst.continuousAt.eventually_lt_const hz] with y hy
  exact zeroBefore_eq_zero_of_le hzero hy.le

theorem zeroBefore_eventually_eq {V : Type*} [Zero V] (g : SpaceTime → V)
    {z : SpaceTime} (hz : 0 < z.1) : zeroBefore g =ᶠ[𝓝 z] g :=
  zeroBefore_eventuallyEq_of_pos g hz

theorem zeroBefore_eventually_zero {V : Type*} [Zero V] {g : SpaceTime → V}
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0)
    {z : SpaceTime} (hz : z.1 ≤ 0) : zeroBefore g =ᶠ[𝓝 z] (fun _ => 0) :=
  zeroBefore_eventuallyEq_zero hzero (by linarith)

/-- Extending by zero is smooth even at time zero, because the field vanishes
on a fixed interval there. -/
theorem zeroBefore_smooth_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g preSingularDomain)
    (hzero : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, g (t, x) = 0) :
    ContDiffOn ℝ ∞ (zeroBefore g) (Iio 1 ×ˢ univ) := by
  intro z hz
  by_cases ht : z.1 < 3 / 8
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (zeroBefore_eventuallyEq_zero hzero ht)).contDiffWithinAt
  · have htpos : 0 < z.1 := by linarith
    have hdomain : preSingularDomain ∈ 𝓝 z := by
      filter_upwards [continuous_fst.continuousAt.eventually_const_lt htpos,
        continuous_fst.continuousAt.eventually_lt_const hz.1] with y hy0 hy1
      exact ⟨⟨hy0.le, hy1⟩, mem_univ _⟩
    exact ((hg.contDiffAt hdomain).congr_of_eventuallyEq
      (zeroBefore_eventuallyEq_of_pos g htpos)).contDiffWithinAt

end NavierStokesR3.ParabolicScaling
