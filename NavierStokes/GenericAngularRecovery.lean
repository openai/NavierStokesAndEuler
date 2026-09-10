import NavierStokes.GenericSolenoidalRealization

noncomputable section

namespace NavierStokes.GenericSolenoidalRealization

open Set Filter ProblemStatement AxisymmetricFields DirectAngularDiagonal
open scoped Topology ContDiff BigOperators

private def radialFactor (w : SpaceTime) (p : ProfilePoint) : ℝ :=
  Real.sqrt (p.2.1 / radialEnergy w.2)

/-- A local section of the cylindrical coordinate map through the given
off-axis Cartesian point, retaining its angular direction. -/
private def radialSection (w : SpaceTime) (p : ProfilePoint) : SpaceTime :=
  (p.1, AxisymmetricResidual.pack (radialFactor w p * w.2 0)
    (radialFactor w p * w.2 1) p.2.2)

private theorem radialFactor_at {w : SpaceTime} (hw : 0 < radialEnergy w.2) :
    radialFactor w (profilePoint w.1 w.2) = 1 := by
  simp only [radialFactor, profilePoint, div_self hw.ne', Real.sqrt_one]

private theorem radialSection_at {w : SpaceTime} (hw : 0 < radialEnergy w.2) :
    radialSection w (profilePoint w.1 w.2) = w := by
  refine Prod.ext ?_ ?_
  · rfl
  ext i
  fin_cases i <;> simp [radialSection, radialFactor, profilePoint, div_self hw.ne']

private theorem profile_radialSection {w : SpaceTime} (hw : 0 < radialEnergy w.2)
    {p : ProfilePoint} (hp : 0 < p.2.1) :
    profilePoint (radialSection w p).1 (radialSection w p).2 = p := by
  have hs : radialFactor w p ^ 2 = p.2.1 / radialEnergy w.2 :=
    Real.sq_sqrt (div_pos hp hw).le
  have he : radialEnergy (radialSection w p).2 = p.2.1 := by
    simp only [radialEnergy, radialSection, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
    calc
      _ = radialFactor w p ^ 2 * radialEnergy w.2 := by unfold radialEnergy; ring
      _ = p.2.1 := by rw [hs, div_mul_cancel₀ _ hw.ne']
  refine Prod.ext ?_ ?_
  · rfl
  exact Prod.ext he (AxisymmetricResidual.pack_two _ _ _)

private theorem radialFactor_smoothAt {w : SpaceTime} (hw : 0 < radialEnergy w.2) :
    ContDiffAt ℝ ∞ (radialFactor w) (profilePoint w.1 w.2) := by
  apply (contDiffAt_snd.fst.div_const (radialEnergy w.2)).sqrt
  change (profilePoint w.1 w.2).2.1 / radialEnergy w.2 ≠ 0
  norm_num [profilePoint, div_self hw.ne']

private theorem radialSection_smoothAt {w : SpaceTime} (hw : 0 < radialEnergy w.2) :
    ContDiffAt ℝ ∞ (radialSection w) (profilePoint w.1 w.2) := by
  have hs := radialFactor_smoothAt hw
  have hv : ContDiffAt ℝ ∞ (fun p : ProfilePoint => AxisymmetricResidual.pack
      (radialFactor w p * w.2 0) (radialFactor w p * w.2 1) p.2.2)
      (profilePoint w.1 w.2) := by
    unfold AxisymmetricResidual.pack
    exact (((hs.mul contDiffAt_const).smul contDiffAt_const).add
      ((hs.mul contDiffAt_const).smul contDiffAt_const)).add
        (contDiffAt_snd.snd.smul contDiffAt_const)
  exact contDiffAt_fst.prodMk hv

/-- Off the axis, smoothness of a Cartesian rotational field implies
smoothness of its cylindrical rate. No regularity of that rate is assumed. -/
theorem rotation_rate_smooth_of_cartesian {F : Profile} {w : SpaceTime}
    (hB : ContDiffAt ℝ ∞ (rotationField F) w) (hw : 0 < radialEnergy w.2) :
    ContDiffAt ℝ ∞ F (profilePoint w.1 w.2) := by
  let p0 := profilePoint w.1 w.2
  let s := radialSection w
  let c := radialFactor w
  let S := w.2 0 ^ 2 + w.2 1 ^ 2
  have hS : 0 < S := by dsimp [S, radialEnergy] at *; linarith
  have hBs : ContDiffAt ℝ ∞ (fun p => rotationField F (s p)) p0 := by
    have hb : ContDiffAt ℝ ∞ (rotationField F) (s p0) := by
      change ContDiffAt ℝ ∞ (rotationField F) (radialSection w (profilePoint w.1 w.2))
      rw [radialSection_at hw]
      exact hB
    exact hb.comp p0 (radialSection_smoothAt hw)
  have h0 : ContDiffAt ℝ ∞ (fun p => rotationField F (s p) 0) p0 :=
    (projection 0).contDiff.contDiffAt.comp p0 hBs
  have h1 : ContDiffAt ℝ ∞ (fun p => rotationField F (s p) 1) p0 :=
    (projection 1).contDiff.contDiffAt.comp p0 hBs
  let recover : ProfilePoint → ℝ := fun p =>
    ((-w.2 1) * rotationField F (s p) 0 + w.2 0 * rotationField F (s p) 1) / (c p * S)
  have hr : ContDiffAt ℝ ∞ recover p0 := by
    apply ((contDiffAt_const.mul h0).add (contDiffAt_const.mul h1)).div
      ((radialFactor_smoothAt hw).mul contDiffAt_const)
    change radialFactor w (profilePoint w.1 w.2) * S ≠ 0
    rw [radialFactor_at hw, one_mul]
    exact hS.ne'
  have he : F =ᶠ[𝓝 p0] recover := by
    have hpos : ∀ᶠ p : ProfilePoint in 𝓝 p0, 0 < p.2.1 :=
      continuous_snd.fst.continuousAt (lt_mem_nhds hw)
    filter_upwards [hpos] with p hp
    have hc : 0 < c p := Real.sqrt_pos.mpr (div_pos hp hw)
    have hcoord := profile_radialSection hw hp
    dsimp only [recover]
    apply (eq_div_iff (mul_pos hc hS).ne').mpr
    simp only [rotationField, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
    change F p * (c p * S) =
      -w.2 1 * (-(s p).2 1 * F (profilePoint (s p).1 (s p).2)) +
        w.2 0 * ((s p).2 0 * F (profilePoint (s p).1 (s p).2))
    rw [show profilePoint (s p).1 (s p).2 = p from hcoord]
    simp only [s, radialSection, AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one]
    dsimp only [c, S]
    ring
  exact hr.congr_of_eventuallyEq he

/-- The literal smooth Cartesian angular representative supplies every
off-axis cylindrical derivative needed by the divergence calculation. -/
theorem angular_rate_smooth_of_cartesian (b : Coefficient) {w : SpaceTime}
    (hB : ContDiffAt ℝ ∞ (angularField b) w) (hr : 0 < radius w) :
    ContDiffAt ℝ ∞ (rate b) (profilePoint w.1 w.2) := by
  have hE : 0 < radialEnergy w.2 := by
    have hs : 0 < w.2 0 ^ 2 + w.2 1 ^ 2 := Real.sqrt_pos.mp hr
    exact div_pos hs (by norm_num)
  rw [angularField_eq_rotationField] at hB
  exact rotation_rate_smooth_of_cartesian hB hE

/-- Cartesian smoothness alone suffices, including at the axis. -/
theorem angular_divergence_of_cartesian (b : Coefficient) {w : SpaceTime}
    (hB : ContDiffAt ℝ ∞ (angularField b) w) :
    spatialDivergence (angularField b) w.1 w.2 = 0 := by
  apply angular_divergence b
  · exact (hB.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  · intro hr
    exact (angular_rate_smooth_of_cartesian b hB hr).differentiableAt (by simp)

theorem axial_scale_horizontal_derivative (Q : ℝ × ℝ → ℝ) {t : ℝ} {x : Space}
    (hq : DifferentiableAt ℝ (fun y : Space => Q (t, y 2)) x)
    (i : Fin 3) (hi : i ≠ 2) :
    fderiv ℝ (fun y : Space => Q (t, y 2)) x (coordinateVector i) = 0 := by
  have hl : HasDerivAt (fun r : ℝ => x + r • coordinateVector i) (coordinateVector i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add x using 1
    simp
  have hq' : HasFDerivAt (fun y : Space => Q (t, y 2))
      (fderiv ℝ (fun y : Space => Q (t, y 2)) x) (x + (0 : ℝ) • coordinateVector i) := by
    simpa only [zero_smul, add_zero] using hq.hasFDerivAt
  have hd := (hq'.comp_hasDerivAt (0 : ℝ) hl).deriv
  have he : (fun r : ℝ => Q (t, (x + r • coordinateVector i) 2)) = (fun _ => Q (t, x 2)) := by
    funext r
    fin_cases i <;> simp_all [coordinateVector, PiLp.add_apply, PiLp.smul_apply]
  change deriv (fun r : ℝ => Q (t, (x + r • coordinateVector i) 2)) 0 =
    fderiv ℝ (fun y : Space => Q (t, y 2)) x (coordinateVector i) at hd
  rw [he] at hd
  simpa using hd.symm

/-- The exact angular and axial-scale assumptions of the manuscript imply
both premises required by the general solenoidal diagonal construction. -/
theorem angular_admissibility (Q : ℝ × ℝ → ℝ) (b : Coefficient) {w : SpaceTime}
    (hq : ContDiffAt ℝ ∞ (fun z : SpaceTime => Q (z.1, z.2 2)) w)
    (hB : ContDiffAt ℝ ∞ (angularField b) w) :
    spatialDivergence (angularField b) w.1 w.2 = 0 ∧
      ∑ i : Fin 3, fderiv ℝ (fun x : Space => Q (w.1, x 2)) w.2 (coordinateVector i) *
        angularField b w i = 0 := by
  refine ⟨angular_divergence_of_cartesian b hB, ?_⟩
  have hd := (hq.comp w.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  apply tangent_of_axial_scale (q := fun z => Q (z.1, z.2 2))
    (axial_scale_horizontal_derivative Q hd 0 (by decide))
    (axial_scale_horizontal_derivative Q hd 1 (by decide))
  simp [angularField, coordinateVector, PiLp.add_apply, PiLp.smul_apply]

end NavierStokes.GenericSolenoidalRealization
