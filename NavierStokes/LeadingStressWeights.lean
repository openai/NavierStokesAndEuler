import NavierStokes.ActiveAnnulusWeight
import NavierStokes.ModulatedProfileAssembly
import NavierStokes.LeadingStress

/-!
# Weighted bounds for the actual leading stress

The stress consists of the two genuine coefficients in `LeadingStress`.
Its edge factors are transported through the literal finite modulation and
the five restored profile histories.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff

namespace NavierStokes.LeadingStressWeights

open ProfileHistories


noncomputable def stress {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) : ℝ × ℝ :=
  (LeadingStress.theta P h p, LeadingStress.axial P h p)

theorem stress_eq {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    stress P h p = P.f p •
      (ReferenceBounds.p1 P h p - ActivationContinuation.shearA P p,
        ReferenceBounds.p2 P h p - ActivationContinuation.shearB P p) := by
  apply Prod.ext
  · exact LeadingStress.theta_eq_lag_minus_slope P h hf
  · have he := LeadingStress.axial_eq_lag_plus_slope P h hX hf
    dsimp only [stress, Prod.smul_snd, smul_eq_mul]
    rw [he]
    dsimp only [ReferenceBounds.p2, ReferenceBounds.ns, LeadingStress.slopeB,
      ActivationContinuation.shearB, SimilarityProfile.partialX, radialPartial,
      CoordinateAlgebra.L, NaturalAxisData.L]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem stress_contDiffAt {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0)
    (hL : NaturalAxisData.L h p.2 ≠ 0) : ContDiffAt ℝ ∞ (stress P h) p :=
  (LeadingStress.theta_smoothAt P h hp hX.ne' hf hL).prodMk
    (LeadingStress.axial_smoothAt P h hp hX.ne' hL)

noncomputable def stressDomain {D : RadialDomain} (P : Profiles D) (h : ℝ) : Set Point :=
  {p | p ∈ D.carrier ∧ 0 < p.1 ∧ P.f p ≠ 0 ∧ NaturalAxisData.L h p.2 ≠ 0}

theorem stressDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (stressDomain P h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hpf := (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp.1)).continuousAt
  have hL : Continuous (fun q : Point => NaturalAxisData.L h q.2) := by
    unfold NaturalAxisData.L
    fun_prop
  filter_upwards [D.isOpen.mem_nhds hp.1, continuousAt_fst.eventually (Ioi_mem_nhds hp.2.1),
    hpf.eventually_ne hp.2.2.1, (hL.continuousAt).eventually_ne hp.2.2.2] with q hq hx hf hl
  exact ⟨hq, hx, hf, hl⟩

theorem stress_smooth {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    ContDiffOn ℝ ∞ (stress P h) (stressDomain P h) :=
  fun _ hp => (stress_contDiffAt P h hp.1 hp.2.1 hp.2.2.1 hp.2.2.2).contDiffWithinAt

noncomputable def logPoint (p : ℝ × ℝ) : Point := (Real.exp p.2, p.1)

theorem logPoint_smooth : ContDiff ℝ ∞ logPoint := contDiff_snd.exp.prodMk contDiff_fst

noncomputable def logStress {D : RadialDomain} (P : Profiles D) (h : ℝ) : (ℝ × ℝ) → ℝ × ℝ :=
  stress P h ∘ logPoint

noncomputable def logStressDomain {D : RadialDomain} (P : Profiles D) (h : ℝ) : Set (ℝ × ℝ) :=
  logPoint ⁻¹' stressDomain P h

theorem logStressDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (logStressDomain P h) := (stressDomain_open P h).preimage logPoint_smooth.continuous

theorem logStress_smooth {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    ContDiffOn ℝ ∞ (logStress P h) (logStressDomain P h) :=
  (stress_smooth P h).comp logPoint_smooth.contDiffOn (fun _ hp => hp)

theorem stress_eq_of_coordinates {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (h : ℝ) {p : Point} (hX : 0 < p.1) (hQ : Q.f p ≠ 0) (hf : P.f p = Q.f p)
    (ha : ActivationContinuation.shearA P p = ActivationContinuation.shearA Q p)
    (hb : ActivationContinuation.shearB P p = ActivationContinuation.shearB Q p)
    (hp1 : ReferenceBounds.p1 P h p = ReferenceBounds.p1 Q h p)
    (hp2 : ReferenceBounds.p2 P h p = ReferenceBounds.p2 Q h p) :
    stress P h p = stress Q h p := by
  rw [stress_eq P h hX (hf ▸ hQ), stress_eq Q h hX hQ, hf, ha, hb, hp1, hp2]

section Modulation

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

theorem stress_outside {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hout : p.1 < d.modulation.left ∨ (ModulatedProfileAssembly.repairPatch W).right < p.1) :
    stress v.profiles F.data.h p = stress W.profiles F.data.h p := by
  have hnot : p.1 ∉ Ioo d.modulation.left (ModulatedProfileAssembly.repairPatch W).right := by
    intro hp
    rcases hout with hl | hr
    · linarith [hp.1]
    · linarith [hp.2]
  have hf := (v.fields_outside hnot).1
  have hW := (NominalConeAssembly.Witness.f_positive W hX hη).ne'
  have hv := hf ▸ hW
  have hst := v.stocks_outside hX (d.parameters_contains hη) hnot hW
  have hsh := v.shears_outside hout
  have hvs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative hX.le (d.parameters_contains hη)) hX hv
  have hws := NominalConeAssembly.modulated_shears_eq W.profiles (W.domain_contains hX.le hη) hX hW
  apply stress_eq_of_coordinates v.profiles W.profiles F.data.h hX hW hf
  · exact hvs.1.symm.trans (hsh.1.trans hws.1)
  · exact hvs.2.symm.trans (hsh.2.trans hws.2)
  · exact hst.1
  · rw [NominalConeAssembly.p2_eq_stock, NominalConeAssembly.p2_eq_stock]
    exact hst.2

theorem logStress_mem {p : ℝ × ℝ} (hη : p.1 ∈ Icc (-1 : ℝ) 1) :
    p ∈ logStressDomain v.profiles F.data.h := by
  have hx : 0 < (logPoint p).1 := Real.exp_pos _
  exact ⟨d.domain_nonnegative hx.le (d.parameters_contains hη), hx,
    (v.positive_f hx hη).ne', (NaturalAxisData.L_pos W.axis.small hη).ne'⟩

end Modulation

section Activation

open StressActivation

variable (N : ReferencePath.Input) {T delta : ℝ} (hT : 0 < T) (hd : 0 < delta)
    (hdlim : 2 * delta < ReferencePath.rampLimit) (kappa h : ℝ)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0)

theorem activation_shears (y : ℝ) {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) :
    let P := FromReference.histories N hT hd hdlim kappa P0 hP0
    ActivationContinuation.shearA P (radius N.endpoint y, eta) =
      actualP1 T kappa (FromReference.refLog N delta) (y, eta) ∧
    ActivationContinuation.shearB P (radius N.endpoint y, eta) =
      actualP2 T kappa N.endpoint (FromReference.refLog N delta)
        (FromReference.refAxial N delta) (y, eta) := by
  let P := FromReference.histories N hT hd hdlim kappa P0 hP0
  have hp := FromReference.log_radius_mem N y hη
  have hx : 0 < radius N.endpoint y := mul_pos N.endpoint_pos (Real.exp_pos _)
  have hfp : P.f (radius N.endpoint y, eta) ≠ 0 :=
    (FromReference.f_pos N T kappa delta hp hx.le).ne'
  have hchart : HasDerivAt (radius N.endpoint) (radius N.endpoint y) y :=
    (Real.hasDerivAt_exp y).const_mul N.endpoint
  have hdf := (radialPartial_hasDerivAt N.radialDomain P.f_smooth hp).comp y hchart
  have hdu := (radialPartial_hasDerivAt N.radialDomain P.U_smooth hp).comp y hchart
  have hfe : (fun s => P.f (radius N.endpoint s, eta)) =
      fun s => activatedAngular T kappa (FromReference.refLog N delta) (s, eta) := by
    funext s
    exact FromReference.f_logPullback N hT hd hdlim kappa s hη
  have hue : (fun s => P.U (radius N.endpoint s, eta)) =
      fun s => controlled T kappa (FromReference.refAxial N delta) (s, eta) := by
    funext s
    exact FromReference.U_logPullback N hT hd hdlim kappa s hη
  have hlog := hdf.log hfp
  dsimp only [Function.comp_def] at hlog hdu
  have hfv := congrFun hfe y
  have hle : (fun s => Real.log (P.f (radius N.endpoint s, eta))) =
      fun s => Real.log (activatedAngular T kappa (FromReference.refLog N delta) (s, eta)) := by
    funext s
    rw [congrFun hfe s]
  have hEL : P.E (radius N.endpoint y, eta) =
      velocity N.endpoint (activatedAngular T kappa (FromReference.refLog N delta)) (y, eta) := by
    unfold Profiles.E velocity
    rw [hfv]
  constructor
  · change -2 * radius N.endpoint y * radialPartial P.f (radius N.endpoint y, eta) /
      P.f (radius N.endpoint y, eta) = _
    unfold actualP1
    rw [← hle, hlog.deriv]
    ring
  · change -2 * radius N.endpoint y * radialPartial P.U (radius N.endpoint y, eta) /
      P.E (radius N.endpoint y, eta) = _
    unfold actualP2
    rw [← hue, hdu.deriv, hEL]
    ring

theorem activation_stress (y : ℝ) {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) :
    let P := FromReference.histories N hT hd hdlim kappa P0 hP0
    stress P h (radius N.endpoint y, eta) =
      ActivationCone.activatedStress h N.endpoint
        (ActivationStocks.FromReference.initial N hd hdlim P0 hP0)
        (FromReference.refLog N delta) (FromReference.refAxial N delta) T kappa (y, eta) := by
  let P := FromReference.histories N hT hd hdlim kappa P0 hP0
  have hp := FromReference.log_radius_mem N y hη
  have hx : 0 < radius N.endpoint y := mul_pos N.endpoint_pos (Real.exp_pos _)
  have hfp : P.f (radius N.endpoint y, eta) ≠ 0 :=
    (FromReference.f_pos N T kappa delta hp hx.le).ne'
  have hs := activation_shears N hT hd hdlim kappa P0 hP0 y hη
  have hq := ActivationStocks.FromReference.actual_stockOne_logView N hT hd hdlim kappa h P0 hP0 y hη
  have hn := ActivationStocks.FromReference.actual_stockTwo_logView N hT hd hdlim kappa h P0 hP0 y hη
  change stress P h _ = _
  rw [stress_eq P h hx hfp, hs.1, hs.2, NominalConeAssembly.p1_eq_stock,
    NominalConeAssembly.p2_eq_stock, hq, hn]
  have hf : P.f (radius N.endpoint y, eta) =
      activatedAngular T kappa (FromReference.refLog N delta) (y, eta) :=
    FromReference.f_logPullback N hT hd hdlim kappa y hη
  rw [hf]
  rfl

end Activation

section InnerCollar

open StressActivation

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def activationProfiles : Profiles W.axis.referenceInput.radialDomain :=
  FromReference.histories W.axis.referenceInput W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
    F.axisDatum F.axisDatum_contDiff

noncomputable def activationStress : Point → ℝ × ℝ :=
  ActivationCone.activatedStress F.data.h W.axis.referenceInput.endpoint
    (ActivationStocks.FromReference.initial W.axis.referenceInput W.controls.referenceWidth_pos
      W.controls.referenceWidth_small F.axisDatum F.axisDatum_contDiff)
    (FromReference.refLog W.axis.referenceInput W.controls.referenceWidth)
    (FromReference.refAxial W.axis.referenceInput W.controls.referenceWidth)
    W.controls.activationTime W.controls.kappa

theorem nominal_activation_stress {y eta : ℝ} (hy : y ≤ W.controls.referenceWidth)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    stress W.profiles F.data.h (NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)) =
      activationStress W (y, eta) := by
  let p := NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hx : 0 < p.1 := NominalConeAssembly.chart_positive (NominalConeAssembly.activeLeft_pos W) _
  have hR : p.1 ≤ (4 / W.axis.scale) * Real.exp W.controls.referenceWidth :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) (NominalConeAssembly.activeLeft_pos W).le
  have hXi : p.1 ≤ NominalProfile.Xi := hR.trans W.controls.activation_collar_le_Xi
  have hseed := NominalConeAssembly.Witness.seed_coordinates W hx hXi hη
  have hseedf : W.controls.seedProfiles.f p ≠ 0 := (W.controls.seedF_positive (p := p) hηJ hx.le).ne'
  have hfirst : stress W.profiles F.data.h p = stress W.controls.seedProfiles F.data.h p :=
    stress_eq_of_coordinates W.profiles W.controls.seedProfiles F.data.h hx hseedf
      (W.seed_agreement hx.le hXi).1 hseed.1 hseed.2.1 hseed.2.2.1 hseed.2.2.2
  have hp : p ∈ W.axis.referenceInput.radialDomain.carrier :=
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg W.axis.scale_pos.le hx.le), hηJ⟩
  have hAf : (activationProfiles W).f p ≠ 0 :=
    (FromReference.f_pos W.axis.referenceInput W.controls.activationTime W.controls.kappa
      W.controls.referenceWidth hp hx.le).ne'
  have he := NominalConeAssembly.coordinates_of_prefix W.controls.seedProfiles (activationProfiles W)
    F.data.h ReferencePath.parameterInterval_open (R := (4 / W.axis.scale) * Real.exp W.controls.referenceWidth)
    rfl (fun q hq hqr => (W.controls.seed_activation hq hqr).1)
      (fun q hq hqr => (W.controls.seed_activation hq hqr).2) hp hp hx hR hηJ hAf
  have hsecond : stress W.controls.seedProfiles F.data.h p = stress (activationProfiles W) F.data.h p :=
    stress_eq_of_coordinates W.controls.seedProfiles (activationProfiles W) F.data.h hx hAf
      (W.controls.seed_activation (p := p) hηJ hR).1 he.1 he.2.1 he.2.2.1 he.2.2.2
  exact hfirst.trans (hsecond.trans (activation_stress W.axis.referenceInput
    W.controls.activationTime_pos W.controls.referenceWidth_pos W.controls.referenceWidth_small
    W.controls.kappa F.data.h F.axisDatum F.axisDatum_contDiff y hηJ))

variable {W} {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

noncomputable def innerWidth (_v : ModulatedProfileAssembly.Witness d) : ℝ :=
  min W.controls.referenceWidth (Real.log (d.modulation.left / NominalConeAssembly.activeLeft W))

theorem innerWidth_pos : 0 < innerWidth v := by
  have ha := NominalConeAssembly.activeLeft_pos W
  have hl : 1 < d.modulation.left / NominalConeAssembly.activeLeft W :=
    (one_lt_div ha).mpr d.after_initial
  exact lt_min W.controls.referenceWidth_pos (Real.log_pos hl)

theorem inner_chart_before {x : ℝ} (hx : x < innerWidth v) :
    NominalConeAssembly.activeLeft W * Real.exp x < d.modulation.left := by
  have hlog := hx.trans_le (min_le_right _ _)
  have hlp := (NominalConeAssembly.activeLeft_pos W).trans d.after_initial
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (div_pos hlp (NominalConeAssembly.activeLeft_pos W))] at he
  exact (by simpa only [mul_comm] using (lt_div_iff₀ (NominalConeAssembly.activeLeft_pos W)).mp he)

theorem modulated_activation_stress {x eta : ℝ} (hx : x < innerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    ActiveAnnulusWeight.leftChart (Real.log (NominalConeAssembly.activeLeft W))
      (logStress v.profiles F.data.h) (eta, x) = activationStress W (x, eta) := by
  have hxR : x ≤ W.controls.referenceWidth := hx.le.trans (min_le_left _ _)
  have hp := inner_chart_before v hx
  dsimp only [ActiveAnnulusWeight.leftChart, logStress, logPoint, Function.comp_apply]
  rw [Real.exp_add, Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
  exact (stress_outside v (mul_pos (NominalConeAssembly.activeLeft_pos W) (Real.exp_pos _)) hη
    (Or.inl hp)).trans (nominal_activation_stress W hxR hη)

end InnerCollar

section OuterCollar

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def leftEdge : ℝ := Real.log (NominalConeAssembly.activeLeft W)
noncomputable def rightEdge : ℝ := Real.log (NominalConeAssembly.activeRight W)

theorem rightEdge_eq : rightEdge W = Real.log W.controls.radius + OutgoingTail.tailEnd F.data := by
  unfold rightEdge NominalConeAssembly.activeRight
  rw [Real.log_mul W.controls.radius_pos.ne' (Real.exp_pos _).ne', Real.log_exp]

theorem rightEdge_shift : rightEdge W = TerminalHistoryBridge.shift F W.controls.radius + 3 := by
  rw [rightEdge_eq]
  unfold TerminalHistoryBridge.shift
  rw [OutgoingDilation.switchRadius_eq,
    Real.log_mul W.controls.radius_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  unfold OutgoingTail.tailEnd
  ring

theorem edges_ordered : leftEdge W < rightEdge W := by
  have hR : W.controls.radius < NominalConeAssembly.activeRight W := by
    change W.controls.radius < W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data)
    have hh := mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.mpr
      ((SchedulePressure.endpoint_pos F.data).trans_le F.tailEnd_after_endpoint)) W.controls.radius_pos
    simpa only [mul_one] using hh
  apply Real.log_lt_log (NominalConeAssembly.activeLeft_pos W)
  exact (NominalConeAssembly.activeLeft_lt_Xi W).trans
    ((W.controls.Xi_lt_heatJoin W.separated).trans
      (W.controls.heatJoin_lt_radius.trans hR))

theorem nominal_terminal_stress {y eta : ℝ} (hy : TerminalCone.terminalStart F.data ≤ y)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    stress W.profiles F.data.h (NominalConeAssembly.chart W.controls.radius (y, eta)) =
      TerminalEdgeFactor.profileStress (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) (eta, OutgoingTail.tailEnd F.data - y) := by
  let p := NominalConeAssembly.chart W.controls.radius (y, eta)
  have hend : F.data.core.endpoint < y := (TerminalHistoryBridge.terminalStart_after_endpoint F).trans_le hy
  have hy0 : 0 ≤ y := (SchedulePressure.endpoint_pos F.data).le.trans hend.le
  have hx : 0 < p.1 := NominalConeAssembly.chart_positive W.controls.radius_pos _
  have hp := NominalConeAssembly.Witness.chart_after_match W (p := (y, eta)) hy0
  have hf := (NominalConeAssembly.Witness.f_positive W hx hη).ne'
  have he := NominalConeAssembly.Witness.log_fields W hp hη
  have hs := NominalConeAssembly.Witness.log_stocks W hp hη
  have ha := NominalConeAssembly.Witness.log_shears W hp hη
  have hb := TerminalHistoryBridge.radialB_after_endpoint F W.controls.radius W.heat.coefficients
    (p := (y, eta)) hend
  have hroot : Real.sqrt (2 * W.controls.radius * Real.exp y) ≠ 0 := by
    exact (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) W.controls.radius_pos)
      (Real.exp_pos _))).ne'
  have hef : W.profiles.f p = HeatSwitchCone.logE F W.controls.radius W.heat.coefficients (y, eta) /
      Real.sqrt (2 * W.controls.radius * Real.exp y) := by
    rw [← he.2.1]
    change W.profiles.f p = (Real.sqrt (2 * p.1) * W.profiles.f p) /
      Real.sqrt (2 * W.controls.radius * Real.exp y)
    have hr : 2 * p.1 = 2 * W.controls.radius * Real.exp y := by dsimp [p, NominalConeAssembly.chart]; ring
    rw [hr, mul_div_cancel_left₀ _ hroot]
  have hE : HeatSwitchCone.logE F W.controls.radius W.heat.coefficients (y, eta) ≠ 0 := by
    rw [← he.2.1]
    exact W.profiles.E_ne_zero hx hf
  have hL : NaturalAxisData.L F.data.h eta ≠ 0 := (NaturalAxisData.L_pos W.axis.small hη).ne'
  have hforward : stress W.profiles F.data.h p =
      (TerminalHistoryBridge.forwardTheta F W.controls.radius W.heat.coefficients (y, eta),
       TerminalHistoryBridge.forwardAxial F W.controls.radius W.heat.coefficients (y, eta)) := by
    rw [stress_eq W.profiles F.data.h hx hf, hef, hs.1, hs.2, ha.1, ha.2, hb]
    apply Prod.ext
    · rfl
    · dsimp only [Prod.smul_snd, smul_eq_mul, neg_zero, sub_zero,
        TerminalHistoryBridge.forwardAxial]
      change _ = W.controls.radius * Real.exp y *
        HeatSwitchCone.Ns F W.controls.radius W.heat.coefficients (y, eta) /
          (NaturalAxisData.L F.data.h eta * Real.sqrt (2 * W.controls.radius * Real.exp y))
      simp only [neg_zero, sub_zero]
      rw [div_mul_div_comm]
      have halg (A B C D : ℝ) (hA : A ≠ 0) :
          A * B / (C * (D * A)) = B / (D * C) := by
        calc
          A * B / (C * (D * A)) = B * A / ((D * C) * A) := by ring
          _ = B / (D * C) := mul_div_mul_right B (D * C) hA
      exact halg _ _ _ _ hE
  have ht := TerminalHistoryBridge.forward_stresses_eq_profile F W.outgoing_specification
    W.heat.physical hy hη
  exact hforward.trans (Prod.ext ht.1 ht.2.1)

theorem activeRight_pos : 0 < NominalConeAssembly.activeRight W :=
  mul_pos W.controls.radius_pos (Real.exp_pos _)

theorem right_chart_eq (x : ℝ) :
    Real.exp (rightEdge W - x) =
      W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data - x) := by
  rw [rightEdge_eq, add_sub_assoc, Real.exp_add, Real.exp_log W.controls.radius_pos]

variable {W} {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

noncomputable def outerWidth (_v : ModulatedProfileAssembly.Witness d) : ℝ :=
  min 1 (Real.log (NominalConeAssembly.activeRight W /
    (ModulatedProfileAssembly.repairPatch W).right))

theorem outerWidth_pos : 0 < outerWidth v := by
  have hp : 0 < (ModulatedProfileAssembly.repairPatch W).right :=
    (ModulatedProfileAssembly.repairPatch W).left_pos.trans
      (ModulatedProfileAssembly.repairPatch W).ordered
  exact lt_min zero_lt_one (Real.log_pos ((one_lt_div hp).mpr
    (ModulatedProfileAssembly.repairPatch_before_activeRight W)))

theorem outer_chart_after {x : ℝ} (hx : x < outerWidth v) :
    (ModulatedProfileAssembly.repairPatch W).right < Real.exp (rightEdge W - x) := by
  have hp : 0 < (ModulatedProfileAssembly.repairPatch W).right :=
    (ModulatedProfileAssembly.repairPatch W).left_pos.trans
      (ModulatedProfileAssembly.repairPatch W).ordered
  have hx' := hx.trans_le (min_le_right (1 : ℝ) _)
  change x < Real.log (NominalConeAssembly.activeRight W /
    (ModulatedProfileAssembly.repairPatch W).right) at hx'
  rw [Real.log_div (activeRight_pos W).ne' hp.ne'] at hx'
  have he : Real.log (ModulatedProfileAssembly.repairPatch W).right < rightEdge W - x := by
    unfold rightEdge
    linarith
  have hh := Real.exp_lt_exp.mpr he
  rwa [Real.exp_log hp] at hh

theorem modulated_terminal_stress {x eta : ℝ} (hx : x < outerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    ActiveAnnulusWeight.rightChart (rightEdge W) (logStress v.profiles F.data.h) (eta, x) =
      TerminalEdgeFactor.profileStress (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) (eta, x) := by
  have hx1 : x < 1 := hx.trans_le (min_le_left _ _)
  have hy : TerminalCone.terminalStart F.data ≤ OutgoingTail.tailEnd F.data - x := by
    unfold TerminalCone.terminalStart OutgoingTail.tailEnd
    linarith
  have hout := outer_chart_after v hx
  rw [right_chart_eq] at hout
  dsimp only [ActiveAnnulusWeight.rightChart, logStress, logPoint, Function.comp_apply]
  rw [right_chart_eq]
  have hs := (stress_outside v
    (mul_pos W.controls.radius_pos (Real.exp_pos _)) hη (Or.inr hout)).trans
      (nominal_terminal_stress W hy hη)
  simp only [sub_sub_cancel] at hs
  exact hs

/-- The actual two leading stresses vanish on the whole terminal exterior,
including the edge. All five histories, not just the velocity, are retained. -/
theorem stress_zero_after {p : Point} (hX : NominalConeAssembly.activeRight W ≤ p.1)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) : stress v.profiles F.data.h p = 0 := by
  have hp : 0 < p.1 := (activeRight_pos W).trans_le hX
  have hl : rightEdge W ≤ Real.log p.1 := Real.log_le_log (activeRight_pos W) hX
  have hx : rightEdge W - Real.log p.1 < outerWidth v :=
    (sub_nonpos.mpr hl).trans_lt (outerWidth_pos v)
  have he := modulated_terminal_stress v hx hη
  have hh : ActiveAnnulusWeight.rightChart (rightEdge W) (logStress v.profiles F.data.h)
      (p.2, rightEdge W - Real.log p.1) = stress v.profiles F.data.h p := by
    simp only [ActiveAnnulusWeight.rightChart, logStress, logPoint, Function.comp_apply,
      sub_sub_cancel, Real.exp_log hp, Prod.mk.eta]
  rw [hh] at he
  exact he.trans (TerminalEdgeFactor.profileStress_of_nonpos _ _ _ (sub_nonpos.mpr hl))

end OuterCollar

section WholeAnnulus

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

/-- The actual full-annulus cone delivered by the finite modulation theorem. -/
noncomputable def FullTrueCone : Prop := ∀ p : Point,
    NominalConeAssembly.activeLeft W < p.1 → p.1 < NominalConeAssembly.activeRight W →
    p.2 ∈ Icc (-1 : ℝ) 1 →
    TrueConeLoop.InTrueCone
      (ActivationStocks.profileStockOne v.profiles F.data.h p)
      (ActivationStocks.profileStockTwo v.profiles F.data.h p)
      (ModulatedCone.angularShear v.profiles.E p)
      (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p)

theorem stress_ne_zero (hcone : FullTrueCone v) {p : Point}
    (hl : NominalConeAssembly.activeLeft W < p.1)
    (hr : p.1 < NominalConeAssembly.activeRight W) (hη : p.2 ∈ Icc (-1 : ℝ) 1) :
    stress v.profiles F.data.h p ≠ 0 := by
  have hx := (NominalConeAssembly.activeLeft_pos W).trans hl
  have hf := (v.positive_f hx hη).ne'
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative hx.le (d.parameters_contains hη)) hx hf
  have hc := hcone p hl hr hη
  intro hz
  rw [stress_eq v.profiles F.data.h hx hf, NominalConeAssembly.p1_eq_stock,
    NominalConeAssembly.p2_eq_stock, ← hs.1, ← hs.2] at hz
  have hpair := (smul_eq_zero.mp hz).resolve_left hf
  have hp1 := sub_eq_zero.mp (congrArg Prod.fst hpair)
  have hp2 := sub_eq_zero.mp (congrArg Prod.snd hpair)
  have hlt := ((ConeAlgebra.true_cone_iff hc.2.1).mp hc.2.2).1
  rw [hp1, hp2] at hlt
  have hid (a c : ℝ) (ha : a ≠ 0) : a * (1 + (c / a)^2) = a + c * (c / a) := by
    field_simp
  rw [hid _ _ hc.1.ne'] at hlt
  exact lt_irrefl _ hlt

theorem logStress_ne_zero (hcone : FullTrueCone v) {eta y : ℝ}
    (hη : eta ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Ioo (leftEdge W) (rightEdge W)) :
    logStress v.profiles F.data.h (eta, y) ≠ 0 := by
  apply stress_ne_zero v hcone
  · change NominalConeAssembly.activeLeft W < Real.exp y
    exact (Real.log_lt_iff_lt_exp (NominalConeAssembly.activeLeft_pos W)).mp hy.1
  · change Real.exp y < NominalConeAssembly.activeRight W
    exact (Real.lt_log_iff_exp_lt (activeRight_pos W)).mp hy.2
  · exact hη

/-- A full true cone rules out the inactive value `kappa = 1`. This is
derived for the supplied final witness, without choosing new controls. -/
theorem kappa_lt_one (hcone : FullTrueCone v) : W.controls.kappa < 1 := by
  by_contra hnot
  have hk : W.controls.kappa = 1 := le_antisymm W.controls.kappa_le_one (le_of_not_gt hnot)
  let x : ℝ := min (innerWidth v / 2) ((rightEdge W - leftEdge W) / 2)
  have hx : 0 < x := lt_min (half_pos (innerWidth_pos v))
    (half_pos (sub_pos.mpr (edges_ordered W)))
  have hxi : x < innerWidth v := (min_le_left _ _).trans_lt (half_lt_self (innerWidth_pos v))
  have hxa : leftEdge W + x ∈ Ioo (leftEdge W) (rightEdge W) := by
    constructor
    · linarith
    · have hb : x ≤ (rightEdge W - leftEdge W) / 2 := min_le_right _ _
      linarith [edges_ordered W]
  have hn := logStress_ne_zero v hcone (eta := 0) (by norm_num) hxa
  have he := modulated_activation_stress v hxi (eta := 0) (by norm_num)
  obtain ⟨D, eps, _, _, _, hfactor⟩ := ActivationCone.natural_activation_direction
    W.axis.scale_pos W.axis.natural F.axisDatum_contDiff W.axis.small
      W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hTx : W.controls.activationTime * (x / W.controls.activationTime) = x := by
    field_simp [W.controls.activationTime_pos.ne']
  have hxd : x ≤ W.controls.referenceWidth := hxi.le.trans (min_le_left _ _)
  have hf := hfactor W.controls.activationTime W.controls.activationTime_pos W.controls.kappa
    (x / W.controls.activationTime) 0 (by rw [hTx]; exact ⟨hx.le, hxd⟩) (by norm_num)
  rw [hTx] at hf
  change activationStress W (x, 0) = _ at hf
  rw [hk] at hf
  simp only [StressActivation.activation, sub_self, zero_mul] at hf
  apply hn
  exact he.trans hf

/-- Equation (20) for the same final finite-modulation witness. The tensor
bounds contain every mixed profile derivative, in both logarithmic and
physical radial charts. -/
theorem weighted_bounds (hcone : FullTrueCone v) :
    ActiveAnnulusWeight.WeightedBounds (Icc (-1 : ℝ) 1)
      (W.controls.activationTime ^ 2) (leftEdge W) (rightEdge W)
      (logStress v.profiles F.data.h) := by
  apply ActiveAnnulusWeight.actual_edge_join W.axis.scale_pos W.axis.natural
    F.axisDatum_contDiff W.axis.small W.controls.referenceWidth_pos
      W.controls.referenceWidth_small W.controls.activationTime_pos (kappa_lt_one v hcone)
      (TerminalCone.normalization_pos F W.controls.radius_pos) F.data
        (TerminalHistoryBridge.shift F W.controls.radius) (edges_ordered W)
        (logStressDomain_open v.profiles F.data.h) (logStress_smooth v.profiles F.data.h)
        (fun _ hp => logStress_mem v hp.1) (fun _ hη _ hy => logStress_ne_zero v hcone hη hy)
          (innerWidth_pos v) (outerWidth_pos v)
  · exact fun _ hη _ _ hx => modulated_activation_stress v hx hη
  · exact fun _ hη _ _ hx => modulated_terminal_stress v hx hη

end WholeAnnulus

section ShearIdentities

noncomputable def logShearA {D : RadialDomain} (P : Profiles D) (p : ℝ × ℝ) : ℝ :=
  ActivationContinuation.shearA P (logPoint p)

noncomputable def logShearB {D : RadialDomain} (P : Profiles D) (p : ℝ × ℝ) : ℝ :=
  ActivationContinuation.shearB P (logPoint p)

noncomputable def logSpeed {D : RadialDomain} (P : Profiles D) (p : ℝ × ℝ) : ℝ :=
  ActivationContinuation.shearSize (logShearA P p) (logShearB P p)

noncomputable def logSlope {D : RadialDomain} (P : Profiles D) (p : ℝ × ℝ) : ℝ :=
  logShearB P p / logShearA P p

theorem shearSize_eq (a b : ℝ) : ActivationContinuation.shearSize a b = a + b ^ 2 / a := by
  by_cases ha : a = 0
  · simp [ActivationContinuation.shearSize, ha]
  · unfold ActivationContinuation.shearSize
    field_simp

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

theorem shears_outside {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ Icc (-1 : ℝ) 1)
    (hout : p.1 < d.modulation.left ∨ (ModulatedProfileAssembly.repairPatch W).right < p.1) :
    ActivationContinuation.shearA v.profiles p = ActivationContinuation.shearA W.profiles p ∧
    ActivationContinuation.shearB v.profiles p = ActivationContinuation.shearB W.profiles p := by
  have hvs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative hX.le (d.parameters_contains hη)) hX (v.positive_f hX hη).ne'
  have hws := NominalConeAssembly.modulated_shears_eq W.profiles
    (W.domain_contains hX.le hη) hX (NominalConeAssembly.Witness.f_positive W hX hη).ne'
  have hs := v.shears_outside hout
  exact ⟨hvs.1.symm.trans (hs.1.trans hws.1), hvs.2.symm.trans (hs.2.trans hws.2)⟩

theorem nominal_activation_shears {y eta : ℝ} (hy : y ≤ W.controls.referenceWidth)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    let N := W.axis.referenceInput
    let L := StressActivation.FromReference.refLog N W.controls.referenceWidth
    let U := StressActivation.FromReference.refAxial N W.controls.referenceWidth
    let p := NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)
    ActivationContinuation.shearA W.profiles p =
      StressActivation.actualP1 W.controls.activationTime W.controls.kappa L (y, eta) ∧
    ActivationContinuation.shearB W.profiles p =
      StressActivation.actualP2 W.controls.activationTime W.controls.kappa N.endpoint L U (y, eta) := by
  let p := NominalConeAssembly.chart (NominalConeAssembly.activeLeft W) (y, eta)
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hx : 0 < p.1 := NominalConeAssembly.chart_positive (NominalConeAssembly.activeLeft_pos W) _
  have hR : p.1 ≤ (4 / W.axis.scale) * Real.exp W.controls.referenceWidth :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) (NominalConeAssembly.activeLeft_pos W).le
  have hseed := NominalConeAssembly.Witness.seed_coordinates W hx
    (hR.trans W.controls.activation_collar_le_Xi) hη
  have hp : p ∈ W.axis.referenceInput.radialDomain.carrier :=
    ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg W.axis.scale_pos.le hx.le), hηJ⟩
  have hAf : (activationProfiles W).f p ≠ 0 :=
    (StressActivation.FromReference.f_pos W.axis.referenceInput W.controls.activationTime W.controls.kappa
      W.controls.referenceWidth hp hx.le).ne'
  have he := NominalConeAssembly.coordinates_of_prefix W.controls.seedProfiles (activationProfiles W)
    F.data.h ReferencePath.parameterInterval_open (R := (4 / W.axis.scale) * Real.exp W.controls.referenceWidth)
    rfl (fun q hq hqr => (W.controls.seed_activation hq hqr).1)
      (fun q hq hqr => (W.controls.seed_activation hq hqr).2) hp hp hx hR hηJ hAf
  have ha := activation_shears W.axis.referenceInput W.controls.activationTime_pos
    W.controls.referenceWidth_pos W.controls.referenceWidth_small W.controls.kappa
      F.axisDatum F.axisDatum_contDiff y hηJ
  exact ⟨hseed.1.trans (he.1.trans ha.1), hseed.2.1.trans (he.2.1.trans ha.2)⟩

theorem modulated_activation_shears {x eta : ℝ} (hx : x < innerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    let N := W.axis.referenceInput
    let L := StressActivation.FromReference.refLog N W.controls.referenceWidth
    let U := StressActivation.FromReference.refAxial N W.controls.referenceWidth
    logShearA v.profiles (eta, leftEdge W + x) =
      StressActivation.actualP1 W.controls.activationTime W.controls.kappa L (x, eta) ∧
    logShearB v.profiles (eta, leftEdge W + x) =
      StressActivation.actualP2 W.controls.activationTime W.controls.kappa N.endpoint L U (x, eta) := by
  have hxR : x ≤ W.controls.referenceWidth := hx.le.trans (min_le_left _ _)
  have hq := shears_outside v
    (p := (NominalConeAssembly.activeLeft W * Real.exp x, eta))
    (mul_pos (NominalConeAssembly.activeLeft_pos W) (Real.exp_pos _))
    hη (Or.inl (inner_chart_before v hx))
  have ha := nominal_activation_shears (W := W) hxR hη
  dsimp only [logShearA, logShearB, logPoint, leftEdge]
  rw [Real.exp_add, Real.exp_log (NominalConeAssembly.activeLeft_pos W)]
  exact ⟨hq.1.trans ha.1, hq.2.trans ha.2⟩

theorem modulated_activation_speed_slope {x eta : ℝ} (hx : x < innerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    let N := W.axis.referenceInput
    let L := StressActivation.FromReference.refLog N W.controls.referenceWidth
    let U := StressActivation.FromReference.refAxial N W.controls.referenceWidth
    ActiveAnnulusWeight.leftChart (leftEdge W) (logSpeed v.profiles) (eta, x) =
      StressActivation.shearSize W.controls.activationTime W.controls.kappa N.endpoint L U (x, eta) ∧
    ActiveAnnulusWeight.leftChart (leftEdge W) (logSlope v.profiles) (eta, x) =
      StressActivation.shearSlope W.controls.activationTime W.controls.kappa N.endpoint L U (x, eta) := by
  have hs := modulated_activation_shears v hx hη
  dsimp only [ActiveAnnulusWeight.leftChart, logSpeed, logSlope]
  rw [hs.1, hs.2, shearSize_eq]
  exact ⟨rfl, rfl⟩

theorem nominal_terminal_shears {y eta : ℝ} (hy : TerminalCone.terminalStart F.data ≤ y)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    let p := NominalConeAssembly.chart W.controls.radius (y, eta)
    ActivationContinuation.shearA W.profiles p =
      TerminalEdgeFactor.profileSpeed (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) (eta, OutgoingTail.tailEnd F.data - y) ∧
    ActivationContinuation.shearB W.profiles p = 0 := by
  have hend := (TerminalHistoryBridge.terminalStart_after_endpoint F).trans_le hy
  have hp := NominalConeAssembly.Witness.chart_after_match W (p := (y, eta))
    ((SchedulePressure.endpoint_pos F.data).le.trans hend.le)
  have hs := NominalConeAssembly.Witness.log_shears W hp hη
  have ht := TerminalHistoryBridge.forward_stresses_eq_profile F W.outgoing_specification
    W.heat.physical hy hη
  have hb := TerminalHistoryBridge.radialB_after_endpoint F W.controls.radius W.heat.coefficients
    (p := (y, eta)) hend
  exact ⟨hs.1.trans ht.2.2, by simpa only [hb, neg_zero] using hs.2⟩

theorem modulated_terminal_shears {x eta : ℝ} (hx : x < outerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    logShearA v.profiles (eta, rightEdge W - x) =
      TerminalEdgeFactor.profileSpeed (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) (eta, x) ∧
    logShearB v.profiles (eta, rightEdge W - x) = 0 := by
  have hx1 : x < 1 := hx.trans_le (min_le_left _ _)
  have hy : TerminalCone.terminalStart F.data ≤ OutgoingTail.tailEnd F.data - x := by
    unfold TerminalCone.terminalStart OutgoingTail.tailEnd
    linarith
  have hout := outer_chart_after v hx
  rw [right_chart_eq] at hout
  have hq := shears_outside v
    (p := (W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data - x), eta))
    (mul_pos W.controls.radius_pos (Real.exp_pos _)) hη (Or.inr hout)
  have ha := nominal_terminal_shears (W := W) hy hη
  dsimp only [logShearA, logShearB, logPoint]
  rw [right_chart_eq]
  simpa only [sub_sub_cancel] using And.intro (hq.1.trans ha.1) (hq.2.trans ha.2)

theorem modulated_terminal_speed_slope {x eta : ℝ} (hx : x < outerWidth v)
    (hη : eta ∈ Icc (-1 : ℝ) 1) :
    ActiveAnnulusWeight.rightChart (rightEdge W) (logSpeed v.profiles) (eta, x) =
      TerminalEdgeFactor.profileSpeed (TerminalHistoryBridge.normalization F W.controls.radius)
        F.data (TerminalHistoryBridge.shift F W.controls.radius) (eta, x) ∧
    ActiveAnnulusWeight.rightChart (rightEdge W) (logSlope v.profiles) (eta, x) = 0 := by
  have hs := modulated_terminal_shears v hx hη
  dsimp only [ActiveAnnulusWeight.rightChart, logSpeed, logSlope]
  rw [hs.1, hs.2]
  simp only [ActivationContinuation.shearSize, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, mul_one, and_self]

end ShearIdentities

section DirectionTransfer

open ActiveAnnulusWeight

/-- Transfer a genuine smooth directional extension through exact local
stress and shear identities. Shrinking keeps all closed collar endpoints. -/
theorem trueDirection_transfer {K : Set ℝ} {T S B : ℝ × ℝ → ℝ × ℝ}
    {u s u' s' : ℝ × ℝ → ℝ} {w w' : ℝ}
    (hdir : HasTrueDirectionCollar K T B u s w) (hw' : 0 < w')
    (hT : ∀ eta ∈ K, ∀ x : ℝ, 0 < x → x < w' → S (eta, x) = T (eta, x))
    (hu : ∀ eta ∈ K, ∀ x : ℝ, 0 ≤ x → x < w' → u' (eta, x) = u (eta, x))
    (hs : ∀ eta ∈ K, ∀ x : ℝ, 0 ≤ x → x < w' → s' (eta, x) = s (eta, x)) :
    HasTrueDirectionCollar K S B u' s' w' := by
  constructor
  · obtain ⟨d, eps, O, hd, hdw, heps, hO, hKO, hsm, hbound, hactual⟩ := hdir.1
    let d' := min d (w' / 2)
    have hd' : 0 < d' := lt_min hd (half_pos hw')
    have hdd : d' ≤ d := min_le_left _ _
    have hdw' : d' < w' := (min_le_right _ _).trans_lt (half_lt_self hw')
    refine ⟨d', eps, O, hd', hdw', heps, hO, ?_, hsm, ?_, ?_⟩
    · exact fun q hq => hKO ⟨hq.1, hq.2.1, hq.2.2.trans hdd⟩
    · intro eta heta x hx
      rw [hu eta heta x hx.1 (hx.2.trans_lt hdw'), hs eta heta x hx.1 (hx.2.trans_lt hdw')]
      exact hbound eta heta x ⟨hx.1, hx.2.trans hdd⟩
    · intro eta heta x hx hxd
      rw [hT eta heta x hx (hxd.trans_lt hdw'), hu eta heta x hx.le (hxd.trans_lt hdw'),
        hs eta heta x hx.le (hxd.trans_lt hdw')]
      exact hactual eta heta x hx (hxd.trans hdd)
  · obtain ⟨d, eps, hd, hdw, heps, hbound⟩ := hdir.2
    let d' := min d (w' / 2)
    have hd' : 0 < d' := lt_min hd (half_pos hw')
    have hdd : d' ≤ d := min_le_left _ _
    have hdw' : d' < w' := (min_le_right _ _).trans_lt (half_lt_self hw')
    refine ⟨d', eps, hd', hdw', heps, ?_⟩
    intro eta heta x hx hxd
    rw [hT eta heta x hx (hxd.trans_lt hdw'), hu eta heta x hx.le (hxd.trans_lt hdw'),
      hs eta heta x hx.le (hxd.trans_lt hdw')]
    exact hbound eta heta x hx (hxd.trans hdd)

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

/-- The actual stress has the inner flat factor and a smooth unit
direction with strict margins for the actual modulated shear. -/
theorem inner_direction (hcone : FullTrueCone v) :
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
        (leftChart (leftEdge W) (logStress v.profiles F.data.h)),
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
        (leftChart (leftEdge W) (logStress v.profiles F.data.h)) G.coefficient
        (leftChart (leftEdge W) (logSpeed v.profiles))
        (leftChart (leftEdge W) (logSlope v.profiles)) G.width := by
  obtain ⟨G, hG⟩ := natural_activation_true_direction W.axis.scale_pos W.axis.natural
    F.axisDatum_contDiff W.axis.small W.controls.referenceWidth_pos W.controls.referenceWidth_small
      W.controls.activationTime_pos (kappa_lt_one v hcone)
  let G' := G.transfer (lt_min (innerWidth_pos v) G.width_pos)
    (min_le_right (innerWidth v) G.width)
      (fun eta heta x _ hx => modulated_activation_stress v (hx.trans_le (min_le_left _ _)) heta)
  refine ⟨G', ?_⟩
  apply trueDirection_transfer hG (lt_min (innerWidth_pos v) G.width_pos)
  · exact fun eta heta x _ hx => modulated_activation_stress v (hx.trans_le (min_le_left _ _)) heta
  · exact fun eta heta x _ hx =>
      (modulated_activation_speed_slope v (hx.trans_le (min_le_left _ _)) heta).1
  · exact fun eta heta x _ hx =>
      (modulated_activation_speed_slope v (hx.trans_le (min_le_left _ _)) heta).2

/-- The inverse-cubic terminal factor has a smooth nonzero direction,
with strict cone margin through the true terminal edge. -/
theorem outer_direction :
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) 4
        (rightChart (rightEdge W) (logStress v.profiles F.data.h)),
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
        (rightChart (rightEdge W) (logStress v.profiles F.data.h)) G.coefficient
        (rightChart (rightEdge W) (logSpeed v.profiles))
        (rightChart (rightEdge W) (logSlope v.profiles)) G.width := by
  have hC := TerminalCone.normalization_pos F W.controls.radius_pos
  let G := terminalEdgeFactor hC F.data (TerminalHistoryBridge.shift F W.controls.radius)
    (outerWidth v) (outerWidth_pos v)
  let G' := G.transfer (outerWidth_pos v) le_rfl
    (fun eta heta x _ hx => modulated_terminal_stress v hx heta)
  refine ⟨G', ?_⟩
  apply trueDirection_transfer
    (terminal_true_direction hC F.data (TerminalHistoryBridge.shift F W.controls.radius))
    (outerWidth_pos v)
  · exact fun eta heta x _ hx => modulated_terminal_stress v hx heta
  · exact fun eta heta x _ hx => (modulated_terminal_speed_slope v hx heta).1
  · exact fun eta heta x _ hx => (modulated_terminal_speed_slope v hx heta).2

end DirectionTransfer

section EdgePositivity

open ActiveAnnulusWeight

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

theorem inner_shear_edge {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    0 < logShearA v.profiles (eta, leftEdge W) ∧ 2 < logSpeed v.profiles (eta, leftEdge W) := by
  let N := W.axis.referenceInput
  have hL := StressActivation.FromReference.refLog_smooth N
    W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hU := StressActivation.FromReference.refAxial_smooth N
    W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hz := actual_shear_coordinates_zero W.controls.activationTime_pos W.controls.kappa
    N.endpoint_pos ReferencePath.parameterInterval_open hL hU
      (NaturalAxisCoefficients.original_interval_interior hη)
  have ha := modulated_activation_shears v (x := 0) (innerWidth_pos v) hη
  simp only [add_zero] at ha
  obtain ⟨t, a, M, ht, _, hapos, _, hb⟩ := ActivationCone.natural_reference_bounds
    W.axis.scale_pos W.axis.natural W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hbd := hb 0 ⟨le_rfl, ht.le⟩ eta hη
  constructor
  · rw [ha.1, hz.1]
    exact hapos.trans_le hbd.1
  · unfold logSpeed
    rw [ha.1, ha.2, hz.1, hz.2, shearSize_eq]
    exact (show (2 : ℝ) < 2 + 1 / 8 by norm_num).trans hbd.2.1

theorem outer_shear_edge {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    0 < logShearA v.profiles (eta, rightEdge W) ∧ 2 < logSpeed v.profiles (eta, rightEdge W) := by
  have ha := modulated_terminal_shears v (x := 0) (outerWidth_pos v) hη
  have hv := modulated_terminal_speed_slope v (x := 0) (outerWidth_pos v) hη
  simp only [sub_zero] at ha
  dsimp only [rightChart] at hv
  simp only [sub_zero] at hv
  have hp := TerminalEdgeFactor.profileSpeed_zero_gt_two
    (TerminalCone.normalization_pos F W.controls.radius_pos) F.data
      (TerminalHistoryBridge.shift F W.controls.radius) hη
  exact ⟨by rw [ha.1]; exact (show (0 : ℝ) < 2 by norm_num).trans hp, by rw [hv.1]; exact hp⟩

/-- The reference shear remains strictly admissible also at the two closed
annulus endpoints; the strict interior is the actual modulation theorem. -/
theorem closed_shear_positive (hcone : FullTrueCone v) {eta y : ℝ}
    (hη : eta ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (leftEdge W) (rightEdge W)) :
    0 < logShearA v.profiles (eta, y) ∧ 2 < logSpeed v.profiles (eta, y) := by
  rcases eq_or_lt_of_le hy.1 with he | hl
  · subst y
    exact inner_shear_edge v hη
  rcases eq_or_lt_of_le hy.2 with he | hr
  · subst y
    exact outer_shear_edge v hη
  have hpl : NominalConeAssembly.activeLeft W < Real.exp y :=
    (Real.log_lt_iff_lt_exp (NominalConeAssembly.activeLeft_pos W)).mp hl
  have hpr : Real.exp y < NominalConeAssembly.activeRight W :=
    (Real.lt_log_iff_exp_lt (activeRight_pos W)).mp hr
  have hc := hcone (Real.exp y, eta) hpl hpr hη
  have hs := NominalConeAssembly.modulated_shears_eq v.profiles
    (d.domain_nonnegative (Real.exp_pos y).le (d.parameters_contains hη))
      (Real.exp_pos y) (v.positive_f (p := (Real.exp y, eta)) (Real.exp_pos y) hη).ne'
  dsimp only [logSpeed, logShearA, logShearB, logPoint]
  rw [← hs.1, ← hs.2]
  exact ⟨hc.1, hc.2.1⟩

theorem inner_angular_positive (hcone : FullTrueCone v) :
    ∃ r : ℝ, 0 < r ∧ r < innerWidth v ∧
      ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x ≤ r →
        0 < (leftChart (leftEdge W) (logStress v.profiles F.data.h) (eta, x)).1 := by
  obtain ⟨G, hGpos, _⟩ := exists_natural_activation_factor_aligned W.axis.scale_pos W.axis.natural
    F.axisDatum_contDiff W.axis.small W.controls.referenceWidth_pos W.controls.referenceWidth_small
      W.controls.activationTime_pos (kappa_lt_one v hcone)
  let G' := G.transfer (lt_min (innerWidth_pos v) G.width_pos)
    (min_le_right (innerWidth v) G.width)
      (fun eta heta x _ hx => modulated_activation_stress v (hx.trans_le (min_le_left _ _)) heta)
  obtain ⟨r, O, hr, hrw, _, _, _, _, hpos⟩ := G'.direction_collar isCompact_Icc hGpos
  exact ⟨r, hr, hrw.trans_le (min_le_left _ _), hpos⟩

theorem outer_angular_positive :
    ∃ r : ℝ, 0 < r ∧ r < outerWidth v ∧
      ∀ eta ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x ≤ r →
        0 < (rightChart (rightEdge W) (logStress v.profiles F.data.h) (eta, x)).1 := by
  have hC := TerminalCone.normalization_pos F W.controls.radius_pos
  let G := terminalEdgeFactor hC F.data (TerminalHistoryBridge.shift F W.controls.radius)
    (outerWidth v) (outerWidth_pos v)
  let G' := G.transfer (outerWidth_pos v) le_rfl
    (fun eta heta x _ hx => modulated_terminal_stress v hx heta)
  have hGpos : ∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G'.coefficient (eta, 0)).1 :=
    fun eta heta => TerminalEdgeFactor.profileAngularFactor_zero_pos hC F.data
      (TerminalHistoryBridge.shift F W.controls.radius) heta
  obtain ⟨r, O, hr, hrw, _, _, _, _, hpos⟩ := G'.direction_collar isCompact_Icc hGpos
  exact ⟨r, hr, hrw, hpos⟩

end EdgePositivity

section OrientedFactors

open ActiveAnnulusWeight StressActivation

variable {F : OutgoingProfile.Profile}

noncomputable def activationSpeed (W : NominalProfile.Witness F) (q : ℝ × ℝ) : ℝ :=
  shearSize W.controls.activationTime W.controls.kappa W.axis.referenceInput.endpoint
    (FromReference.refLog W.axis.referenceInput W.controls.referenceWidth)
    (FromReference.refAxial W.axis.referenceInput W.controls.referenceWidth) (q.2, q.1)

noncomputable def activationSlope (W : NominalProfile.Witness F) (q : ℝ × ℝ) : ℝ :=
  shearSlope W.controls.activationTime W.controls.kappa W.axis.referenceInput.endpoint
    (FromReference.refLog W.axis.referenceInput W.controls.referenceWidth)
    (FromReference.refAxial W.axis.referenceInput W.controls.referenceWidth) (q.2, q.1)

theorem activation_direction_positive (W : NominalProfile.Witness F) (hκ : W.controls.kappa < 1) :
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
        (fun q : ℝ × ℝ => activationStress W (q.2, q.1)),
      (∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (eta, 0)).1) ∧
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
        (fun q : ℝ × ℝ => activationStress W (q.2, q.1)) G.coefficient
        (activationSpeed W) (activationSlope W) G.width := by
  let N := W.axis.referenceInput
  have hL := FromReference.refLog_smooth N W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hU := FromReference.refAxial_smooth N W.controls.referenceWidth_pos W.controls.referenceWidth_small
  obtain ⟨G, hpos, halign⟩ := exists_natural_activation_factor_aligned W.axis.scale_pos W.axis.natural
    F.axisDatum_contDiff W.axis.small W.controls.referenceWidth_pos W.controls.referenceWidth_small
      W.controls.activationTime_pos hκ
  obtain ⟨t, a, M, ht, _, hapos, _, hb⟩ := ActivationCone.natural_reference_bounds
    W.axis.scale_pos W.axis.natural W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hA0 : ∀ eta ∈ Icc (-1 : ℝ) 1,
      0 < referenceP1 (FromReference.refLog N W.controls.referenceWidth) (0, eta) := by
    intro eta heta
    exact hapos.trans_le (hb 0 ⟨le_rfl, ht.le⟩ eta heta).1
  obtain ⟨O, hO, hKO, hv, hs⟩ := actual_shear_domain W.controls.activationTime_pos W.controls.kappa
    N.endpoint_pos ReferencePath.parameterInterval_open
      NaturalAxisCoefficients.original_interval_interior hL hU hA0
  have hdir : HasStrictDirectionCollar (Icc (-1 : ℝ) 1)
      (fun q : ℝ × ℝ => activationStress W (q.2, q.1)) G.coefficient
      (activationSpeed W) (activationSlope W) G.width := by
    apply G.aligned_collar isCompact_Icc hpos hO hKO hv.continuousOn hs.continuousOn
    intro eta heta
    have hz := actual_shear_coordinates_zero W.controls.activationTime_pos W.controls.kappa
      N.endpoint_pos ReferencePath.parameterInterval_open hL hU
        (NaturalAxisCoefficients.original_interval_interior heta)
    change tilt (G.coefficient (eta, 0)) =
      actualP2 W.controls.activationTime W.controls.kappa N.endpoint
        (FromReference.refLog N W.controls.referenceWidth) (FromReference.refAxial N W.controls.referenceWidth)
        (0, eta) / actualP1 W.controls.activationTime W.controls.kappa
          (FromReference.refLog N W.controls.referenceWidth) (0, eta)
    rw [hz.1, hz.2]
    exact halign eta heta
  refine ⟨G, hpos, hdir.true_of_speed isCompact_Icc hO hKO hv.continuousOn ?_⟩
  intro eta heta
  have hz := actual_shear_coordinates_zero W.controls.activationTime_pos W.controls.kappa
    N.endpoint_pos ReferencePath.parameterInterval_open hL hU
      (NaturalAxisCoefficients.original_interval_interior heta)
  change 2 < shearSize W.controls.activationTime W.controls.kappa N.endpoint
    (FromReference.refLog N W.controls.referenceWidth) (FromReference.refAxial N W.controls.referenceWidth) (0, eta)
  unfold shearSize
  rw [hz.1, hz.2]
  exact (show (2 : ℝ) < 2 + 1 / 8 by norm_num).trans (hb 0 ⟨le_rfl, ht.le⟩ eta heta).2.1

variable {W : NominalProfile.Witness F} {d : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness d)

/-- A single actual inner factor carries both the positive angular
orientation and the strict directional certificate. -/
theorem inner_direction_positive (hcone : FullTrueCone v) :
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
        (leftChart (leftEdge W) (logStress v.profiles F.data.h)),
      (∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (eta, 0)).1) ∧
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
        (leftChart (leftEdge W) (logStress v.profiles F.data.h)) G.coefficient
        (leftChart (leftEdge W) (logSpeed v.profiles))
        (leftChart (leftEdge W) (logSlope v.profiles)) G.width := by
  obtain ⟨G, hpos, hdir⟩ := activation_direction_positive W (kappa_lt_one v hcone)
  let G' := G.transfer (lt_min (innerWidth_pos v) G.width_pos)
    (min_le_right (innerWidth v) G.width)
      (fun eta heta x _ hx => modulated_activation_stress v (hx.trans_le (min_le_left _ _)) heta)
  refine ⟨G', hpos, ?_⟩
  apply trueDirection_transfer hdir (lt_min (innerWidth_pos v) G.width_pos)
  · exact fun eta heta x _ hx => modulated_activation_stress v (hx.trans_le (min_le_left _ _)) heta
  · exact fun eta heta x _ hx =>
      (modulated_activation_speed_slope v (hx.trans_le (min_le_left _ _)) heta).1
  · exact fun eta heta x _ hx =>
      (modulated_activation_speed_slope v (hx.trans_le (min_le_left _ _)) heta).2

/-- The actual terminal inverse-cubic factor, with its positive angular
orientation and strict directional certificate on the same factor. -/
theorem outer_direction_positive :
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) 4
        (rightChart (rightEdge W) (logStress v.profiles F.data.h)),
      (∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (eta, 0)).1) ∧
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
        (rightChart (rightEdge W) (logStress v.profiles F.data.h)) G.coefficient
        (rightChart (rightEdge W) (logSpeed v.profiles))
        (rightChart (rightEdge W) (logSlope v.profiles)) G.width := by
  have hC := TerminalCone.normalization_pos F W.controls.radius_pos
  let G := terminalEdgeFactor hC F.data (TerminalHistoryBridge.shift F W.controls.radius)
    (outerWidth v) (outerWidth_pos v)
  let G' := G.transfer (outerWidth_pos v) le_rfl
    (fun eta heta x _ hx => modulated_terminal_stress v hx heta)
  refine ⟨G', fun eta heta => TerminalEdgeFactor.profileAngularFactor_zero_pos hC F.data
    (TerminalHistoryBridge.shift F W.controls.radius) heta, ?_⟩
  apply trueDirection_transfer
    (terminal_true_direction hC F.data (TerminalHistoryBridge.shift F W.controls.radius)) (outerWidth_pos v)
  · exact fun eta heta x _ hx => modulated_terminal_stress v hx heta
  · exact fun eta heta x _ hx => (modulated_terminal_speed_slope v hx heta).1
  · exact fun eta heta x _ hx => (modulated_terminal_speed_slope v hx heta).2

end OrientedFactors

section InnerExterior

open StressActivation

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

theorem activationStress_zero_of_nonpos {x eta : ℝ} (hx : x ≤ 0)
    (hη : eta ∈ Icc (-1 : ℝ) 1) : activationStress W (x, eta) = 0 := by
  let N := W.axis.referenceInput
  let L := FromReference.refLog N W.controls.referenceWidth
  let U := FromReference.refAxial N W.controls.referenceWidth
  let I := ActivationStocks.FromReference.initial N W.controls.referenceWidth_pos
    W.controls.referenceWidth_small F.axisDatum F.axisDatum_contDiff
  have hL := FromReference.refLog_smooth N W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hU := FromReference.refAxial_smooth N W.controls.referenceWidth_pos W.controls.referenceWidth_small
  have hi := ActivationStocks.FromReference.initial_smooth N W.controls.referenceWidth_pos
    W.controls.referenceWidth_small F.axisDatum F.axisDatum_contDiff
  have hcoef : ∀ eta ∈ ReferencePath.parameterInterval, NaturalAxisData.L F.data.h eta ≠ 0 := by
    intro eta heta
    exact (NaturalAxisCoefficients.L_pos_on_window (NaturalAxisRange.ofSmall W.axis.small) ⟨heta.1.le, heta.2.le⟩).ne'
  obtain ⟨P, Q, _, _, hfactor⟩ := ActivationStocks.exists_log_stock_factors F.data.h
    N.endpoint_pos I ReferencePath.parameterInterval_open hL hU hi hcoef
  have hηJ := NaturalAxisCoefficients.original_interval_interior hη
  have hf := hfactor W.controls.activationTime W.controls.activationTime_pos.ne' W.controls.kappa
    (x / W.controls.activationTime) eta hηJ
  have hTx : W.controls.activationTime * (x / W.controls.activationTime) = x := by
    field_simp [W.controls.activationTime_pos.ne']
  have hzero : ActivationBounds.scaledDistance
      ((W.controls.kappa, W.controls.activationTime), (x / W.controls.activationTime, eta)) = 0 := by
    unfold ActivationBounds.scaledDistance
    rw [activation_zero (by norm_num : (0 : ℝ) < 1) W.controls.kappa
      (div_nonpos_of_nonpos_of_nonneg hx W.controls.activationTime_pos.le), mul_zero]
  rw [hTx, hzero, zero_mul, zero_mul] at hf
  have hm := ActivationCone.natural_reference_log_match W.axis.scale_pos W.axis.natural.profile.family
    F.axisDatum_contDiff W.axis.small W.controls.referenceWidth_pos W.controls.referenceWidth_small
      (hx.trans W.controls.referenceWidth_pos.le) hη
  have hs1 : ActivationCone.activatedStockOne F.data.h N.endpoint I L U
      W.controls.activationTime W.controls.kappa (x, eta) = referenceP1 L (x, eta) :=
    (sub_eq_zero.mp hf.1).trans hm.1
  have hs2 : ActivationCone.activatedStockTwo F.data.h N.endpoint I L U
      W.controls.activationTime W.controls.kappa (x, eta) = referenceP2 N.endpoint L U (x, eta) :=
    (sub_eq_zero.mp hf.2).trans hm.2
  have hd : damping W.controls.activationTime W.controls.kappa x = 1 := by
    rw [damping, activation_zero W.controls.activationTime_pos W.controls.kappa hx, sub_zero]
  have hangular : activatedAngular W.controls.activationTime W.controls.kappa L (x, eta) =
      referenceAngular L (x, eta) := by
    unfold activatedAngular referenceAngular
    rw [controlled_eq_reference_before W.controls.activationTime_pos W.controls.kappa
      ReferencePath.parameterInterval_open hL hx hηJ]
  have ha := actualP1_eq W.controls.activationTime W.controls.kappa
    ReferencePath.parameterInterval_open hL x hηJ
  have hb := actualP2_eq W.controls.activationTime W.controls.kappa N.endpoint_pos
    (L := L) ReferencePath.parameterInterval_open hU x hηJ
  have hrf : referenceAngular L (x, eta) ≠ 0 := (Real.exp_pos _).ne'
  rw [hd, one_mul] at ha
  rw [hd, one_mul, hangular, div_self hrf, mul_one] at hb
  change ActivationCone.activatedStress F.data.h N.endpoint I L U
    W.controls.activationTime W.controls.kappa (x, eta) = 0
  unfold ActivationCone.activatedStress
  rw [hs1, hs2, ha, hb]
  simp only [L, U, sub_self, mul_zero, Prod.mk_zero_zero]

variable {W} {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

theorem logStress_zero_before {eta y : ℝ} (hy : y ≤ leftEdge W)
    (hη : eta ∈ Icc (-1 : ℝ) 1) : logStress v.profiles F.data.h (eta, y) = 0 := by
  have hx : y - leftEdge W ≤ 0 := sub_nonpos.mpr hy
  have he := modulated_activation_stress v (hx.trans_lt (innerWidth_pos v)) hη
  have hz := activationStress_zero_of_nonpos W hx hη
  have hc : ActiveAnnulusWeight.leftChart (leftEdge W) (logStress v.profiles F.data.h)
      (eta, y - leftEdge W) = logStress v.profiles F.data.h (eta, y) := by
    simp only [ActiveAnnulusWeight.leftChart, add_sub_cancel]
  exact hc.symm.trans (he.trans hz)

/-- Both actual leading stress components are zero on the entire inner
physical region, with the axis included by their literal formulas. -/
theorem stress_zero_before {p : Point} (hX : 0 ≤ p.1)
    (hbefore : p.1 ≤ NominalConeAssembly.activeLeft W)
    (hη : p.2 ∈ Icc (-1 : ℝ) 1) : stress v.profiles F.data.h p = 0 := by
  rcases hX.eq_or_lt with hz | hx
  · have hzero : p.1 = 0 := hz.symm
    simp only [stress, LeadingStress.theta, LeadingStress.axial, hzero, mul_zero, zero_mul,
      Real.sqrt_zero, zero_div, add_zero, Prod.mk_zero_zero]
  · have hy : Real.log p.1 ≤ leftEdge W := Real.log_le_log hx hbefore
    have hh := logStress_zero_before v hy hη
    simpa only [logStress, logPoint, Function.comp_apply, Real.exp_log hx, Prod.mk.eta] using hh

end InnerExterior

section FinalPackage

open ActiveAnnulusWeight

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness d)

/-- The actual product weight, with the two fixed physical attachment
points and the same activation time used to construct the profile. -/
noncomputable def zeta (_v : ModulatedProfileAssembly.Witness d) (X : ℝ) : ℝ :=
  radialWeight (W.controls.activationTime ^ 2) (leftEdge W) (rightEdge W) X

noncomputable def distance (_v : ModulatedProfileAssembly.Witness d) (X : ℝ) : ℝ :=
  edgeDistance (leftEdge W) (rightEdge W) (Real.log X)

theorem zeta_positive {X : ℝ}
    (hX : X ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W)) :
    0 < zeta v X := by
  apply radialWeight_pos
  simpa only [leftEdge, rightEdge, Real.exp_log (NominalConeAssembly.activeLeft_pos W),
    Real.exp_log (activeRight_pos W)] using hX

theorem radialPullback_eq {D : RadialDomain} (P : Profiles D) (h : ℝ) {q : ℝ × ℝ}
    (hX : 0 < q.2) : radialPullback (logStress P h) q = stress P h (q.2, q.1) := by
  simp only [radialPullback, logChart, logStress, logPoint, Function.comp_apply, Real.exp_log hX]

theorem radialPullback_jet_eq {D : RadialDomain} (P : Profiles D) (h : ℝ) {q : ℝ × ℝ}
    (hX : 0 < q.2) (n : ℕ) :
    iteratedFDeriv ℝ n (radialPullback (logStress P h)) q =
      iteratedFDeriv ℝ n (fun p : ℝ × ℝ => stress P h (p.2, p.1)) q := by
  have he : radialPullback (logStress P h) =ᶠ[𝓝 q]
      (fun p : ℝ × ℝ => stress P h (p.2, p.1)) := by
    filter_upwards [continuousAt_snd.eventually (Ioi_mem_nhds hX)] with p hp
    exact radialPullback_eq P h hp
  have he' : radialPullback (logStress P h) =ᶠ[𝓝[univ] q]
      (fun p : ℝ × ℝ => stress P h (p.2, p.1)) := by simpa using he
  simpa only [iteratedFDerivWithin_univ] using
    (he'.iteratedFDerivWithin_eq (radialPullback_eq P h hX) n (𝕜 := ℝ))

/-- A positive multiple of the actual radial product weight is below the
norm of the literal two leading stress components. -/
theorem stress_lower_bound (hcone : FullTrueCone v) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : Point,
      p.1 ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W) →
      p.2 ∈ Icc (-1 : ℝ) 1 → c * zeta v p.1 ≤ ‖stress v.profiles F.data.h p‖ := by
  obtain ⟨c, hc, hb⟩ := (weighted_bounds v hcone).1
  refine ⟨c, hc, ?_⟩
  intro p hp heta
  have hX : p.1 ∈ Ioo (Real.exp (leftEdge W)) (Real.exp (rightEdge W)) := by
    simpa only [leftEdge, rightEdge, Real.exp_log (NominalConeAssembly.activeLeft_pos W),
      Real.exp_log (activeRight_pos W)] using hp
  have hh := radial_lower_bound hb heta hX
  rw [radialPullback_eq _ _ ((NominalConeAssembly.activeLeft_pos W).trans hp.1)] at hh
  exact hh

/-- Every actual mixed physical profile tensor has the same flat product
weight, with a finite derivative-dependent inverse-distance loss. -/
theorem physical_jet_bound (hcone : FullTrueCone v) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ eta ∈ Icc (-1 : ℝ) 1,
      ∀ X ∈ Ioo (NominalConeAssembly.activeLeft W) (NominalConeAssembly.activeRight W),
        ‖iteratedFDeriv ℝ n (fun p : ℝ × ℝ => stress v.profiles F.data.h (p.2, p.1)) (eta, X)‖ ≤
          C * zeta v X / distance v X ^ N := by
  obtain ⟨C, hC, N, hb⟩ := (weighted_bounds v hcone).2.2 n
  refine ⟨C, hC, N, ?_⟩
  intro eta heta X hX
  have hx : X ∈ Ioo (Real.exp (leftEdge W)) (Real.exp (rightEdge W)) := by
    simpa only [leftEdge, rightEdge, Real.exp_log (NominalConeAssembly.activeLeft_pos W),
      Real.exp_log (activeRight_pos W)] using hX
  have hh := hb eta heta X hx
  rw [radialPullback_jet_eq _ _ ((NominalConeAssembly.activeLeft_pos W).trans hX.1)] at hh
  exact hh

/-- One no-input instance of the complete actual weighted profile and its
two oriented strict edge-direction certificates. -/
theorem exists_weighted_profile :
    ∃ (F : OutgoingProfile.Profile) (W : NominalProfile.Witness F)
      (d : ModulatedProfileAssembly.LoopData W) (v : ModulatedProfileAssembly.Witness d),
      FullTrueCone v ∧
      WeightedBounds (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
        (leftEdge W) (rightEdge W) (logStress v.profiles F.data.h) ∧
      (∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (W.controls.activationTime ^ 2)
          (leftChart (leftEdge W) (logStress v.profiles F.data.h)),
        (∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (eta, 0)).1) ∧
        HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
          (leftChart (leftEdge W) (logStress v.profiles F.data.h)) G.coefficient
          (leftChart (leftEdge W) (logSpeed v.profiles))
          (leftChart (leftEdge W) (logSlope v.profiles)) G.width) ∧
      (∃ G : EdgeFactor (Icc (-1 : ℝ) 1) 4
          (rightChart (rightEdge W) (logStress v.profiles F.data.h)),
        (∀ eta ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (eta, 0)).1) ∧
        HasTrueDirectionCollar (Icc (-1 : ℝ) 1)
          (rightChart (rightEdge W) (logStress v.profiles F.data.h)) G.coefficient
          (rightChart (rightEdge W) (logSpeed v.profiles))
          (rightChart (rightEdge W) (logSlope v.profiles)) G.width) := by
  obtain ⟨F, W, d, v, hv⟩ := ModulatedProfileAssembly.exists_modulated_profile
  exact ⟨F, W, d, v, hv, weighted_bounds v hv, inner_direction_positive v hv, outer_direction_positive v⟩

end FinalPackage

end NavierStokes.LeadingStressWeights

end
