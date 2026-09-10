import NavierStokes.HolomorphicFamily

noncomputable section

namespace NavierStokes.CompactHolomorphicFamily

open Set Filter Metric Complex MeasureTheory
open scoped Topology Interval NNReal

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Evaluation commutes with a genuine circle integral of continuous paths. -/
theorem eval_circleIntegral {F : ℂ → C(K, E)} {c : ℂ} {R : ℝ}
    (hF : CircleIntegrable F c R) (x : K) :
    (∮ z in C(c, R), F z) x = ∮ z in C(c, R), F z x := by
  let L : C(K, E) →L[ℂ] E := ContinuousMap.evalCLM ℂ x
  change L (∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap c R) θ •
    F (circleMap c R θ)) = _
  rw [← L.intervalIntegral_comp_comm hF.out]
  simp only [map_smul]
  rfl

/-- A continuous compact-valued family with holomorphic evaluations is
holomorphic in the supremum norm. Local uniform bounds follow from compactness. -/
theorem differentiableOn_of_evaluations {F : ℂ → C(K, E)} {U : Set ℂ}
    (hU : IsOpen U) (hF : ContinuousOn F U)
    (hhol : ∀ x : K, DifferentiableOn ℂ (fun z => F z x) U) :
    DifferentiableOn ℂ F U := by
  intro z hz
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let ρ : ℝ≥0 := ⟨δ / 2, by positivity⟩
  have hρ : 0 < ρ := by change (0 : ℝ) < δ / 2; positivity
  have hDisk : closedBall z (ρ : ℝ) ⊆ U := fun w hw =>
    hδU (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hw).trans_lt (by
      change δ / 2 < δ; linarith)))
  have hc : ContinuousOn F (closedBall z (ρ : ℝ)) := hF.mono hDisk
  have hi : CircleIntegrable F z ρ :=
    (hc.mono sphere_subset_closedBall).circleIntegrable ρ.2
  have heq : (fun w => (2 * Real.pi * I : ℂ)⁻¹ •
      ∮ v in C(z, (ρ : ℝ)), (v - w)⁻¹ • F v) =ᶠ[𝓝 z] F := by
    filter_upwards [Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (show 0 < (ρ : ℝ) from hρ))] with w hw
    ext x
    have hkernel : ContinuousOn (fun v : ℂ => (v - w)⁻¹) (sphere z (ρ : ℝ)) :=
      (continuous_id.sub continuous_const).continuousOn.inv₀ (fun v hv =>
        sub_ne_zero.mpr (by
          intro he
          change v = w at he
          subst v
          exact (Metric.mem_ball.mp hw).ne (Metric.mem_sphere.mp hv)))
    have hk : CircleIntegrable (fun v => (v - w)⁻¹ • F v) z ρ :=
      (hkernel.smul (hc.mono sphere_subset_closedBall)).circleIntegrable ρ.2
    change (2 * Real.pi * I : ℂ)⁻¹ • (∮ v in C(z, (ρ : ℝ)), (v - w)⁻¹ • F v) x = _
    rw [eval_circleIntegral hk]
    have hDC := ((hhol x).mono (closure_ball_subset_closedBall.trans hDisk)).diffContOnCl
    exact hDC.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hd := (hasFPowerSeriesOn_cauchy_integral hi hρ).analyticAt.differentiableAt
  exact (hd.congr_of_eventuallyEq heq.symm).differentiableWithinAt

end NavierStokes.CompactHolomorphicFamily
