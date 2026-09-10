import NavierStokes.WithinPathFamily
import NavierStokes.JointODE

/-! # Joint ODE jets on closed parameter and pulse domains -/

noncomputable section

namespace NavierStokes.WithinJointODE

open Set Filter Function
open scoped Topology ContDiff

universe u

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {a b : ℝ}

theorem contDiffOn_odeFamily (hab : a ≤ b) {U : Set P} {V : Set ℝ}
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U) (hv : UniqueDiffOn ℝ V)
    (hI : Icc a b ⊆ V)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ V)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (SmoothPathFamily.odeFamily hab A x₀ f) U :=
  ParametricODE.contDiffOn_solution_family hab _ _ _
    (WithinPathFamily.contDiffOn_pathFamily U V hU hu hv hI A hA) hx₀
    (WithinPathFamily.contDiffOn_pathFamily U V hU hu hv hI f hf)

/-- Endpoint rescaling preserves within regularity in slow parameters and
gives joint regularity at every current pulse time. Only the original data
are supplied, including at the slow boundary. -/
theorem contDiffOn_reparamSolution {U : Set P}
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ univ)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (JointODE.reparamSolution a A x₀ f) (U ×ˢ univ) := by
  have hmap : MapsTo (JointODE.timeMap (P := P) a)
      ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) (U ×ˢ univ) :=
    fun _ hz => ⟨hz.1.1, mem_univ _⟩
  have hx : ContDiffOn ℝ ∞ (fun q : P × ℝ => x₀ q.1) (U ×ˢ univ) :=
    hx₀.comp contDiffOn_fst (fun _ hz => hz.1)
  have hpath := contDiffOn_odeFamily (a := 0) (b := 1) zero_le_one
    (hU.prod convex_univ) (hu.prod uniqueDiffOn_univ) uniqueDiffOn_univ
    (subset_univ _) (JointODE.rescale a A) (fun q : P × ℝ => x₀ q.1)
    (JointODE.rescale a f) (JointODE.rescale_contDiffOn A hA hmap) hx
    (JointODE.rescale_contDiffOn f hf hmap)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMap.evalCLM ℝ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1))).comp_contDiffOn hpath

/-- The actual Volterra solution has all mixed within jets on both closed
domains, including corners where slow time and pulse time are endpoints. -/
theorem contDiffOn_actualSolution (hab : a ≤ b) {U : Set P}
    (hU : Convex ℝ U) (hu : UniqueDiffOn ℝ U)
    (A : P × ℝ → E →L[ℝ] E) (x₀ : P → E) (f : P × ℝ → E)
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ univ)) (hx₀ : ContDiffOn ℝ ∞ x₀ U)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (JointODE.actualSolution hab A x₀ f) (U ×ˢ Icc a b) := by
  apply ((contDiffOn_reparamSolution hU hu A x₀ f hA hx₀ hf).mono
    (prod_mono Subset.rfl (subset_univ _))).congr
  intro z hz
  exact (JointODE.reparamSolution_eq_actualSolution hab A x₀ f
    (hA.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
    (hf.continuousOn.mono (prod_mono Subset.rfl (subset_univ _))) hz).symm

end NavierStokes.WithinJointODE

namespace NavierStokes.WithinJetClosure

open Set Filter
open scoped Topology ContDiff

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interior full derivatives converge to the genuine boundary within jet.
This applies to each fixed mixed derivative order. -/
theorem tendsto_iteratedFDeriv {S O : Set P} (hS : UniqueDiffOn ℝ S)
    (hO : IsOpen O) (hOS : O ⊆ S) {f : P → E} (hf : ContDiffOn ℝ ∞ f S)
    (n : ℕ) {x : P} (hx : x ∈ S) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[O] x)
      (𝓝 (iteratedFDerivWithin ℝ n f S x)) := by
  have hc := (hf.continuousOn_iteratedFDerivWithin
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) hS x hx).mono hOS
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact iteratedFDerivWithin_eq_iteratedFDeriv hS
    (((hf.mono hOS).contDiffAt (hO.mem_nhds hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) (hOS hy)

/-- A continuous majorant for interior jets bounds the endpoint jets with
the same constants. No estimates outside the closed domain are used. -/
theorem norm_iteratedFDerivWithin_le {S O : Set P} (hS : UniqueDiffOn ℝ S)
    (hO : IsOpen O) (hOS : O ⊆ S) {f : P → E} (hf : ContDiffOn ℝ ∞ f S)
    {B : P → ℝ} (hB : ContinuousOn B S) (n : ℕ)
    (hb : ∀ x ∈ O, ‖iteratedFDeriv ℝ n f x‖ ≤ B x)
    {x : P} (hx : x ∈ S) (hxc : x ∈ closure O) :
    ‖iteratedFDerivWithin ℝ n f S x‖ ≤ B x := by
  have : NeBot (𝓝[O] x) := mem_closure_iff_nhdsWithin_neBot.mp hxc
  exact le_of_tendsto_of_tendsto
    (tendsto_iteratedFDeriv hS hO hOS hf n hx).norm ((hB x hx).mono hOS)
    (Filter.eventually_iff.mpr (Filter.mem_of_superset self_mem_nhdsWithin (fun _ hy => hb _ hy)))

end NavierStokes.WithinJetClosure
