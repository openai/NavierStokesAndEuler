import NavierStokes.R3.H3Energy
import NavierStokes.R3.H3StrongSolution

/-! # Weak–strong comparison in the ordinary H³ class -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

namespace NavierStokesR3.H3Comparison

open ProblemStatement
open NavierStokes.ProblemStatement (pressureGradient)

private theorem advection_sub (u v : Space → Space) (du dv : Fin 3 → Space → Space) (x : Space) :
    weakAdvection u du x - weakAdvection v dv x =
      weakAdvection (fun x => u x - v x) du x +
        weakAdvection v (fun i x => du i x - dv i x) x := by
  simp only [weakAdvection, PiLp.sub_apply, sub_smul, smul_sub,
    Finset.sum_sub_distrib]
  abel

/-- Comparison with a reference whose spatial derivative is uniformly
bounded. All competitor derivatives remain weak H³ jets. The pressure
pairing premise is the sole hook for the separate arbitrary-pressure
orthogonality theorem; no energy inequality is assumed. -/
theorem strong_unique_of_pressure_pairing {ν T : ℝ} (hν : 0 ≤ ν)
    {f u v : VelocityField} {p q : PressureField}
    (hu : StrongSolutionOnIcc ν f 0 T u p) (hv : StrongSolutionOnIcc ν f 0 T v q)
    (A : ℝ → Space → Space →L[ℝ] Space) {G : ℝ} (hG : 0 ≤ G)
    (hAm : ∀ t ∈ Ioo (0 : ℝ) T, AEStronglyMeasurable (A t) volume)
    (hAb : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, ‖A t x‖ ≤ G)
    (hAe : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᵐ x ∂volume, ∀ z : Space,
      A t x z = ∑ i : Fin 3, z i • hu.curve.first i (t, x))
    (hpg : ∀ t ∈ Ioo (0 : ℝ) T,
      MemLp (fun x => pressureGradient p t x - pressureGradient q t x) 2 volume)
    (hpressure : ∀ t ∈ Ioo (0 : ℝ) T,
      (∫ x, ⟪u (t, x) - v (t, x), pressureGradient p t x - pressureGradient q t x⟫_ℝ) = 0)
    (hinitial : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  let W : ℝ → Lp Space 2 (volume : Measure Space) :=
    fun t => hu.curve.velocityLp t - hv.curve.velocityLp t
  let D : ℝ → Lp Space 2 (volume : Measure Space) := fun t =>
    if ht : t ∈ Ioo (0 : ℝ) T then
      ((hu.timeDerivative_memLp t ht).sub (hv.timeDerivative_memLp t ht)).toLp
        (fun x => hu.timeDerivative (t, x) - hv.timeDerivative (t, x)) else 0
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : HasDerivAt W (D t) t := by
    dsimp only [D]
    rw [dite_eq_left ht]
    exact (hu.hasDerivAt_velocity t ht).sub (hv.hasDerivAt_velocity t ht)
  have hzero : W 0 = 0 := by
    have hz : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hu.time_lt.le⟩
    dsimp only [W]
    rw [hu.curve.velocityLp_eq hz, hv.curve.velocityLp_eq hz]
    apply sub_eq_zero.mpr
    apply Lp.ext
    filter_upwards [(hu.curve.approximation 0 hz).memLp.coeFn_toLp,
      (hv.curve.approximation 0 hz).memLp.coeFn_toLp] with x hx hy
    rw [hx, hy, hinitial]
  have hrate (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : 2 * ⟪W t, D t⟫_ℝ ≤ 2 * G * ‖W t‖ ^ 2 := by
    have htc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
    let hU := hu.curve.approximation t htc
    let hV := hv.curve.approximation t htc
    let hW := hU.sub hV
    have heW : W t = hW.memLp.toLp (fun x => u (t, x) - v (t, x)) := by
      dsimp only [W]
      rw [hu.curve.velocityLp_eq htc, hv.curve.velocityLp_eq htc]
      rfl
    have heD : D t = ((hu.timeDerivative_memLp t ht).sub (hv.timeDerivative_memLp t ht)).toLp
        (fun x => hu.timeDerivative (t, x) - hv.timeDerivative (t, x)) := dite_eq_left ht
    have heNS : ∀ᵐ x ∂volume,
        hu.timeDerivative (t, x) - hv.timeDerivative (t, x) =
        ν • (∑ i : Fin 3, (hu.curve.second i i (t, x) - hv.curve.second i i (t, x))) -
          A t x (u (t, x) - v (t, x)) -
          (∑ i : Fin 3, v (t, x) i • (hu.curve.first i (t, x) - hv.curve.first i (t, x))) -
          (pressureGradient p t x - pressureGradient q t x) := by
      filter_upwards [hu.navier_stokes t ht, hv.navier_stokes t ht, hAe t ht] with x hux hvx hAx
      have hut : hu.timeDerivative (t, x) = f (t, x) -
          weakAdvection (fun y => u (t, y)) (fun i y => hu.curve.first i (t, y)) x +
          ν • weakLaplacian (fun i j y => hu.curve.second i j (t, y)) x - pressureGradient p t x := by
        rw [← hux]
        abel
      have hvt : hv.timeDerivative (t, x) = f (t, x) -
          weakAdvection (fun y => v (t, y)) (fun i y => hv.curve.first i (t, y)) x +
          ν • weakLaplacian (fun i j y => hv.curve.second i j (t, y)) x - pressureGradient q t x := by
        rw [← hvx]
        abel
      have ha := advection_sub (fun y => u (t, y)) (fun y => v (t, y))
        (fun i y => hu.curve.first i (t, y)) (fun i y => hv.curve.first i (t, y)) x
      change _ = (∑ i : Fin 3, (u (t, x) - v (t, x)) i • hu.curve.first i (t, x)) + _ at ha
      rw [← hAx] at ha
      rw [hut, hvt, Finset.sum_sub_distrib, smul_sub]
      dsimp only [weakLaplacian] at *
      have ha' := (sub_eq_iff_eq_add).mp ha
      rw [ha']
      dsimp only [weakAdvection]
      abel
    have hh := difference_rate_le hW hV
      ((hu.curve.spatial_continuous t htc).sub (hv.curve.spatial_continuous t htc))
      (hv.curve.spatial_continuous t htc) (hpg t ht) hν (A t) (hAm t ht) (hAb t ht)
      (hv.divergence_free t ht) (hpressure t ht) heNS
    rw [heW, heD, inner_toLp, ← integral_norm_sq_eq_toLp]
    exact hh
  have hz := hilbert_curve_zero hu.time_lt.le hG
    (hu.curve.continuousOn_velocityLp.sub hv.curve.continuousOn_velocityLp) hzero hd hrate
  intro t ht x
  have he : (hu.curve.approximation t ht).memLp.toLp (fun y => u (t, y)) =
      (hv.curve.approximation t ht).memLp.toLp (fun y => v (t, y)) := by
    apply sub_eq_zero.mp
    simpa only [W, Pi.sub_apply, hu.curve.velocityLp_eq ht, hv.curve.velocityLp_eq ht] using! hz t ht
  exact congrFun (eq_of_toLp_eq (hu.curve.approximation t ht).memLp (hv.curve.approximation t ht).memLp
    (hu.curve.spatial_continuous t ht) (hv.curve.spatial_continuous t ht) he) x

end NavierStokesR3.H3Comparison
