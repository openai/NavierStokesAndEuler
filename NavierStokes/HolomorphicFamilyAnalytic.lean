import NavierStokes.HolomorphicFamily
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.ContinuousMap.Units

/-! # Joint analyticity from analytic disk-valued families

The fixed Cauchy contour is a bounded bilinear operation. Its kernel is
analytic in the supremum norm because inversion is analytic at units of the
Banach algebra of continuous contour functions.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace NavierStokes.HolomorphicFamily

private def constantPath : ℂ →L[ℝ] C(Angles, ℂ) :=
  LinearMap.mkContinuous {
    toFun := ContinuousMap.const Angles
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  } 1 (by
    intro z
    simpa only [one_mul] using (ContinuousMap.norm_le _ (norm_nonneg z)).mpr (fun _ => le_rfl))

private def circlePath (c : ℂ) (σ : ℝ) : C(Angles, ℂ) :=
  ⟨fun θ => circleMap c σ θ, (continuous_circleMap c σ).comp continuous_subtype_val⟩

private def tangentPath (σ : ℝ) : C(Angles, ℂ) :=
  ⟨fun θ => circleMap 0 σ θ * I,
    ((continuous_circleMap 0 σ).comp continuous_subtype_val).mul continuous_const⟩

private theorem inversePath_apply {f : C(Angles, ℂ)} (hf : IsUnit f) (θ : Angles) :
    Ring.inverse f θ = (f θ)⁻¹ := by
  have h := congrArg (fun g : C(Angles, ℂ) => g θ) (Ring.mul_inverse_cancel f hf)
  change f θ * Ring.inverse f θ = 1 at h
  exact eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using h)

/-- The fixed-contour kernel is analytic as a curve in the supremum norm. -/
theorem analyticAt_kernelPath (c : ℂ) (σ : ℝ) {z : ℂ} (hz : z ∈ ball c σ) :
    AnalyticAt ℝ (kernelPath c σ) z := by
  let D : ℂ → C(Angles, ℂ) := fun w => circlePath c σ - constantPath w
  have hu : IsUnit (D z) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro θ
    exact sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)
  have hd : AnalyticAt ℝ D z := analyticAt_const.sub (constantPath.analyticAt z)
  have hi : AnalyticAt ℝ (fun w => Ring.inverse (D w)) z :=
    (analyticOnNhd_inverse (𝕜 := ℝ) (D z) hu).comp hd
  have ha : AnalyticAt ℝ (fun w => tangentPath σ * Ring.inverse (D w)) z :=
    analyticAt_const.mul hi
  apply ha.congr
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  ext θ
  have huw : IsUnit (D w) := by
    apply (ContinuousMap.isUnit_iff_forall_ne_zero _).mpr
    intro a
    exact sub_ne_zero.mpr (circleMap_ne_mem_ball hw a)
  simp only [ContinuousMap.mul_apply, inversePath_apply huw,
    kernelPath_apply c σ hw θ]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic disk data gives joint real analyticity of its Cauchy evaluation. -/
theorem analyticAt_cauchyValue (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (V : ℝ → C(CauchyRestriction.Disk c σ, E)) {p : ℝ × ℂ}
    (hV : AnalyticAt ℝ V p.1) (hz : p.2 ∈ ball c σ) :
    AnalyticAt ℝ (cauchyValue c hσ V) p := by
  have hk : AnalyticAt ℝ (fun q : ℝ × ℂ => kernelPath c σ q.2) p :=
    (analyticAt_kernelPath c σ hz).comp (analyticAt_snd (𝕜 := ℝ) (p := p))
  have hv : AnalyticAt ℝ (fun q : ℝ × ℂ => sampleCircle c hσ (V q.1)) p :=
    ((sampleCircle c hσ (E := E)).analyticAt _).comp_of_eq
      (hV.comp (analyticAt_fst (𝕜 := ℝ) (p := p))) rfl
  have hp : AnalyticAt ℝ (fun q : ℝ × ℂ => pathAction (E := E)
      (kernelPath c σ q.2) (sampleCircle c hσ (V q.1))) p :=
    ((pathAction (E := E)).analyticAt_bilinear _).comp_of_eq (hk.prod hv) rfl
  exact (((angleIntegral (E := E)).analyticAt _).comp_of_eq hp rfl).const_smul
    (c := (2 * Real.pi * I : ℂ)⁻¹)

variable [CompleteSpace E]

/-- Joint real analyticity follows from analytic disk data and holomorphic
slices, by equality with the actual fixed-contour Cauchy expression. -/
theorem analyticOnNhd_of_disk_family (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    {S : Set ℝ} (hS : IsOpen S) (V : ℝ → C(CauchyRestriction.Disk c σ, E))
    (F : ℝ → ℂ → E) (hV : AnalyticOnNhd ℝ V S)
    (hF : ∀ r ∈ S, DifferentiableOn ℂ (F r) (ball c σ))
    (hvalues : ∀ r ∈ S, ∀ z : CauchyRestriction.Disk c σ, V r z = F r z) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℂ => F p.1 p.2) (S ×ˢ ball c σ) := by
  intro p hp
  apply (analyticAt_cauchyValue c hσ V (hV p.1 hp.1) hp.2).congr
  filter_upwards [(hS.prod isOpen_ball).mem_nhds hp] with q hq
  exact cauchyValue_eq c hσ V F (hF q.1 hq.1) (hvalues q.1 hq.1) hq.2

end NavierStokes.HolomorphicFamily
