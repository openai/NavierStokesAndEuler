import NavierStokes.OutgoingDilation
import NavierStokes.OutgoingHistories
import NavierStokes.NaturalEntrance
import NavierStokes.ReferencePath
import NavierStokes.ShapeTransition
import NavierStokes.FiveProfileMoments
import NavierStokes.TransitionRamp
import NavierStokes.HeatedOutgoing
import NavierStokes.ActivationContinuation
import NavierStokes.ExtendedHeatedOutgoing

/-!
# A common witness for nominal-profile assembly

The outgoing schedule, angular reset, corrected amplitude, and pressure datum
are fixed first.  The natural-axis construction below uses exactly that datum
and that value of `h`.  The five-row correction is a fixed, constructed local
inverse applied to the actual debt of the assembled prefix.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators
open NavierStokes.OutgoingProfile

namespace NavierStokes.NominalProfile

abbrev Point := ℝ × ℝ
abbrev Field := Point → ℝ
abbrev Debt := FiveProfileMoments.Debt
abbrev Coeff := FiveProfileMoments.Coeff

/-- The axis choices are made after fixing this particular outgoing profile. -/
structure AxisPreparation (F : Profile) (j : ℝ) where
  delta : ℝ
  sigma : ℝ
  delta_pos : 0 < delta
  sigma_pos : 0 < sigma
  inputs : NaturalAxisCoefficients.AnalyticInputs F.data.h j sigma F.axisDatum
  scaleBound : ℝ
  scaleBound_pos : 0 < scaleBound
  entrances : ∀ Λ : ℝ, scaleBound ≤ Λ → ∀ C : ℝ,
    NaturalEntrance.entranceNormalization inputs Λ delta ≤ C →
      Nonempty (NaturalEntrance.EntranceProfile inputs Λ C)

theorem prepare_axis (F : Profile) (hP : 2 ≤ F.data.core.P) {j : ℝ}
    (hj : NaturalAxisData.SmallParameters F.data.h j) : Nonempty (AxisPreparation F j) := by
  have he := NaturalEntrance.ideal_prefix_entranceProfile (NaturalAxisRange.ofSmall hj)
    (SchedulePressure.admissible F.data) hP
    (fun y hy => SchedulePressure.clockWeight_ideal F.data hy)
    (fun y hy => SchedulePressure.shapeExponent_ideal F.data hy)
  have hd : F.axisDatum = PressureDatum.pressure
      (SchedulePressure.clockWeight F.data) (SchedulePressure.shapeExponent F.data) :=
    F.axisDatum_eq.trans (SchedulePressure.axisPressure_eq F.data)
  rw [← hd] at he
  obtain ⟨delta, sigma, hdelta, hsigma, inputs, bound, hbound, entrances⟩ := he
  exact ⟨⟨delta, sigma, hdelta, hsigma, inputs, bound, hbound, entrances⟩⟩

/-- The scale is selected before the normalization; both retain the same
outgoing profile and the same analytic axis data. -/
structure AxisStage (F : Profile) where
  j : ℝ
  small : NaturalAxisData.SmallParameters F.data.h j
  preparation : AxisPreparation F j
  scale : ℝ
  normalization : ℝ
  scale_large : preparation.scaleBound ≤ scale
  normalization_large :
    NaturalEntrance.entranceNormalization preparation.inputs scale preparation.delta ≤ normalization
  chosenNatural : NaturalEntrance.EntranceProfile preparation.inputs scale normalization

namespace AxisStage

variable {F : Profile} (A : AxisStage F)

theorem scale_pos : 0 < A.scale := A.preparation.scaleBound_pos.trans_le A.scale_large

theorem normalization_pos : 0 < A.normalization :=
  (Real.exp_pos _).trans_le ((NaturalEntrance.entranceNormalization_ge A.preparation.inputs
    A.scale_pos A.preparation.delta_pos).trans A.normalization_large)

noncomputable def natural : NaturalEntrance.EntranceProfile A.preparation.inputs A.scale A.normalization :=
  A.chosenNatural

noncomputable def referenceInput : ReferencePath.Input :=
  ReferencePath.Input.ofNatural A.scale_pos A.natural.profile.family

theorem reference_scale : A.referenceInput.scale = A.scale := rfl
theorem reference_f : A.referenceInput.f = A.natural.profile.family.f := rfl
theorem reference_U : A.referenceInput.U = A.natural.profile.family.U := rfl

noncomputable def reference (δ : ℝ) (hδ : 0 < δ) (hδsmall : 2 * δ < ReferencePath.rampLimit) :
    ProfileHistories.Profiles A.referenceInput.radialDomain :=
  A.referenceInput.histories hδ hδsmall F.axisDatum F.axisDatum_contDiff

theorem reference_pressure0 (δ : ℝ) (hδ : 0 < δ) (hδsmall : 2 * δ < ReferencePath.rampLimit) :
    (A.reference δ hδ hδsmall).pressure0 = F.axisDatum := rfl

/-- The stocks used in ACT come from this exact REF profile. -/
noncomputable def activation (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2 * δ < ReferencePath.rampLimit) :
    TransitionRamp.StockReference ReferencePath.parameterInterval :=
  TransitionRamp.ofNatural A.natural.profile.family A.scale_pos A.small hδ hδsmall
    F.axisDatum_contDiff

theorem activation_profiles (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2 * δ < ReferencePath.rampLimit) :
    (A.activation δ hδ hδsmall).profiles = A.reference δ hδ hδsmall := rfl

theorem activation_radius (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2 * δ < ReferencePath.rampLimit) :
    (A.activation δ hδ hδsmall).radius0 = 4 / A.scale := rfl

theorem activation_initial (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : 2 * δ < ReferencePath.rampLimit) (T κ w₁ w₂ : ℝ) {p : Point}
    (hp : p.1 ≤ 4 / A.scale) :
    (A.activation δ hδ hδsmall).physicalF T κ w₁ w₂ p = A.natural.profile.family.f p ∧
      (A.activation δ hδ hδsmall).physicalU T κ w₁ p = A.natural.profile.family.U p := by
  constructor
  · rw [TransitionRamp.StockReference.physicalF_before _ _ _ _ _ hp]
    exact A.referenceInput.refF_eq_natural_initial δ hp
  · rw [TransitionRamp.StockReference.physicalU_before _ _ _ _ hp]
    exact A.referenceInput.refU_eq_natural_initial δ hp

end AxisStage

theorem exists_axis_stage (F : Profile) (hP : 2 ≤ F.data.core.P) {j : ℝ}
    (hj : NaturalAxisData.SmallParameters F.data.h j) (scaleFloor normFloor : ℝ) :
    ∃ A : AxisStage F, A.j = j ∧ scaleFloor ≤ A.scale ∧ normFloor ≤ A.normalization := by
  obtain ⟨prep⟩ := prepare_axis F hP hj
  let Λ := max prep.scaleBound scaleFloor
  let C := max (NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta) normFloor
  exact ⟨⟨j, hj, prep, Λ, C, le_max_left _ _, le_max_left _ _,
      Classical.choice (prep.entrances Λ (le_max_left _ _) C (le_max_left _ _))⟩,
    rfl, le_max_right _ _, le_max_right _ _⟩

/-! ## Matching geometry: the radius is derived from the same normalization -/

noncomputable def Xi : ℝ := 110
noncomputable def matchingRadius (F : Profile) (C : ℝ) : ℝ :=
  ShapeTransition.resetRadius Xi C F.data.core.P
noncomputable def matchFraction : ℝ := Real.exp (-5)
noncomputable def matchRadius (F : Profile) (C : ℝ) : ℝ := matchingRadius F C * matchFraction

theorem Xi_pos : 0 < Xi := by norm_num [Xi]
theorem matchingRadius_pos (F : Profile) {C : ℝ} (hC : 0 < C) : 0 < matchingRadius F C :=
  mul_pos Xi_pos (pow_pos (mul_pos hC F.data.core.P_pos) 10)
theorem matchFraction_pos : 0 < matchFraction := Real.exp_pos _
theorem matchFraction_lt_one : matchFraction < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

theorem matchingRadius_tendsto (F : Profile) : Tendsto (matchingRadius F) atTop atTop := by
  have hcp : Tendsto (fun C : ℝ => C * F.data.core.P) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos F.data.core.P_pos).mpr tendsto_id
  exact (tendsto_const_mul_atTop_of_pos Xi_pos).mpr ((tendsto_pow_atTop (by decide : 10 ≠ 0)).comp hcp)

/-- Any fixed outgoing radius bound and shape-separation test can be met by
the later choice of `C`; no outgoing parameter is reselected. -/
theorem eventually_matching_geometry (F : Profile) (T radiusFloor normFloor : ℝ) :
    ∀ᶠ C : ℝ in atTop, 0 < C ∧ normFloor ≤ C ∧ radiusFloor < matchingRadius F C ∧
      ShapeTransition.separation T C F.data.core.P < Real.exp (-8) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop normFloor,
    (matchingRadius_tendsto F).eventually (eventually_gt_atTop radiusFloor),
    ShapeTransition.separation_eventually_before T F.data.core.P_pos (-8)] with C hC hn hr hs
  exact ⟨hC, hn, hr, hs⟩

noncomputable def resetPatch : FiveProfileMoments.Patch where
  left := Real.exp (-6)
  right := Real.exp (-5)
  left_pos := Real.exp_pos _
  ordered := Real.exp_lt_exp.mpr (by norm_num)

noncomputable def idealAmplitude (F : Profile) (eta : ℝ) : ℝ :=
  F.data.core.P * OutgoingSchedule.shape eta
noncomputable def idealU (eta : ℝ) : ℝ := 4 * eta
noncomputable def idealE (F : Profile) (p : Point) : ℝ :=
  idealAmplitude F p.2 * p.1 ^ (1 / 10 : ℝ)

theorem idealAmplitude_pos (F : Profile) (eta : ℝ) : 0 < idealAmplitude F eta :=
  mul_pos F.data.core.P_pos (OutgoingSchedule.shape_pos eta)
theorem idealAmplitude_smooth (F : Profile) : ContDiff ℝ ∞ (idealAmplitude F) :=
  contDiff_const.mul OutgoingSchedule.shape_contDiff
theorem idealU_smooth : ContDiff ℝ ∞ idealU := contDiff_const.mul contDiff_id

/-- One normalized inverse is fixed before the prefix debt is supplied. -/
structure ResetSolver where
  solve : Coeff → Coeff
  radius : ℝ
  bound : ℝ
  radius_pos : 0 < radius
  bound_pos : 0 < bound
  smooth : ContDiffOn ℝ ∞ solve (Metric.ball 0 radius)
  at_zero : solve 0 = 0
  equation : ∀ q ∈ Metric.ball (0 : Coeff) radius,
    FiveProfileMoments.normalizedMap resetPatch (1 / 10) (solve q) = q
  positive : ∀ q ∈ Metric.ball (0 : Coeff) radius, ∀ x : ℝ, 0 < x →
    0 < x ^ (1 / 10 : ℝ) + FiveProfileMoments.e resetPatch (solve q) x
  norm_bound : ∀ q ∈ Metric.ball (0 : Coeff) radius, ‖solve q‖ ≤ bound * ‖q‖

theorem resetSolver_exists : Nonempty ResetSolver := by
  obtain ⟨g, r, C, hr, hC, hg, hg0, he⟩ :=
    FiveProfileMoments.exists_normalized_repair resetPatch (1 / 10) FiveProfileMoments.good_initial
  exact ⟨⟨g, r, C, hr, hC, hg, hg0, fun q hq => (he q hq).1,
    fun q hq => (he q hq).2.2.2, fun q hq => (he q hq).2.1⟩⟩

noncomputable def resetSolver : ResetSolver := Classical.choice resetSolver_exists

noncomputable def normalizedDebt (F : Profile) (debt : ℝ → Debt) (eta : ℝ) : Coeff :=
  FiveProfileMoments.normalizedDebt (idealAmplitude F eta) (idealU eta) (debt eta)

noncomputable def resetCoefficients (F : Profile) (debt : ℝ → Debt) (eta : ℝ) : Coeff :=
  resetSolver.solve (normalizedDebt F debt eta)

def SmallDebt (F : Profile) (debt : ℝ → Debt) (eta : ℝ) : Prop :=
  ‖normalizedDebt F debt eta‖ < resetSolver.radius

theorem smallDebt_mem {F : Profile} {debt : ℝ → Debt} {eta : ℝ} (h : SmallDebt F debt eta) :
    normalizedDebt F debt eta ∈ Metric.ball (0 : Coeff) resetSolver.radius := by
  rw [Metric.mem_ball, dist_zero_right]
  exact h

theorem resetCoefficients_equation (F : Profile) (debt : ℝ → Debt) (eta : ℝ)
    (hs : SmallDebt F debt eta) :
    FiveProfileMoments.physicalMoments resetPatch (1 / 10)
      (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) = debt eta := by
  rw [FiveProfileMoments.physicalMoments_eq resetPatch (1 / 10) _ _ (idealAmplitude_pos F eta).ne']
  rw [resetCoefficients, resetSolver.equation _ (smallDebt_mem hs)]
  exact FiveProfileMoments.physical_normalized_debt _ _ (idealAmplitude_pos F eta).ne' _

theorem resetCoefficients_smooth (F : Profile) {debt : ℝ → Debt} {V : Set ℝ}
    (hd : ContDiffOn ℝ ∞ debt V) (hs : ∀ eta ∈ V, SmallDebt F debt eta) :
    ContDiffOn ℝ ∞ (resetCoefficients F debt) V := by
  apply resetSolver.smooth.comp
    (FiveProfileMoments.normalizedDebt_contDiffOn (idealAmplitude_smooth F).contDiffOn
      idealU_smooth.contDiffOn hd (fun eta _ => (idealAmplitude_pos F eta).ne'))
  exact fun eta heta => smallDebt_mem (hs eta heta)

/-! ## Literal row densities and compact edits -/

noncomputable def density (U E : ℝ → ℝ) (x : ℝ) : Debt :=
  ![U x, Real.sqrt (2 * x) * E x, U x * Real.sqrt (2 * x) * E x,
    U x ^ 2 - E x ^ 2 / 2, E x ^ 2 / (2 * x)]

noncomputable def moments (U E : Field) (r eta : ℝ) : Debt :=
  fun i => ∫ x in Ioc 0 r, density (fun x => U (x, eta)) (fun x => E (x, eta)) x i

noncomputable def correctedU (F : Profile) (U : Field) (debt : ℝ → Debt) (p : Point) : ℝ :=
  U p + idealAmplitude F p.2 * FiveProfileMoments.u resetPatch (resetCoefficients F debt p.2) p.1
noncomputable def correctedE (F : Profile) (E : Field) (debt : ℝ → Debt) (p : Point) : ℝ :=
  E p + idealAmplitude F p.2 * FiveProfileMoments.e resetPatch (resetCoefficients F debt p.2) p.1

theorem corrected_unchanged (F : Profile) (U E : Field) (debt : ℝ → Debt) (p : Point)
    (hp : p.1 ∉ Ioo resetPatch.left resetPatch.right) :
    correctedU F U debt p = U p ∧ correctedE F E debt p = E p := by
  simp [correctedU, correctedE, FiveProfileMoments.u_zero_outside resetPatch _ hp,
    FiveProfileMoments.e_zero_outside resetPatch _ hp]

theorem density_change (U E dU dE : ℝ → ℝ) (x : ℝ) (i : Fin 5) :
    density (fun t => U t + dU t) (fun t => E t + dE t) x i =
      density U E x i + FiveProfileMoments.profileChangeDensity U E dU dE x i := by
  fin_cases i <;> simp [density, FiveProfileMoments.profileChangeDensity] <;> ring

theorem corrected_density (F : Profile) (U E : Field) (debt : ℝ → Debt) (eta x : ℝ)
    (hU : ∀ x ∈ Ioo resetPatch.left resetPatch.right, U (x, eta) = idealU eta)
    (hE : ∀ x ∈ Ioo resetPatch.left resetPatch.right, E (x, eta) = idealE F (x, eta)) (i : Fin 5) :
    density (fun t => correctedU F U debt (t, eta)) (fun t => correctedE F E debt (t, eta)) x i =
      density (fun t => U (t, eta)) (fun t => E (t, eta)) x i +
        FiveProfileMoments.physicalDensity resetPatch (1 / 10)
          (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) x i := by
  unfold correctedU correctedE
  rw [density_change, FiveProfileMoments.local_profile_change resetPatch (1 / 10)
    (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) _ _ hU hE]

theorem physicalDensity_integral_prefix (F : Profile) (debt : ℝ → Debt) (eta r : ℝ)
    (hr : resetPatch.right ≤ r) (i : Fin 5) :
    (∫ x in Ioc 0 r, FiveProfileMoments.physicalDensity resetPatch (1 / 10)
      (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) x i) =
      FiveProfileMoments.physicalMoments resetPatch (1 / 10)
        (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) i := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hpatch : x ∉ Ioo resetPatch.left resetPatch.right := by
    intro hp
    exact hx ⟨resetPatch.left_pos.trans hp.1, hp.2.le.trans hr⟩
  rw [FiveProfileMoments.physicalDensity_zero_outside resetPatch (1 / 10)
    (idealAmplitude F eta) (idealU eta) (resetCoefficients F debt eta) hpatch]
  rfl

theorem corrected_moments (F : Profile) (U E : Field) (debt : ℝ → Debt) (eta r : ℝ)
    (hr : resetPatch.right ≤ r) (hs : SmallDebt F debt eta)
    (hU : ∀ x ∈ Ioo resetPatch.left resetPatch.right, U (x, eta) = idealU eta)
    (hE : ∀ x ∈ Ioo resetPatch.left resetPatch.right, E (x, eta) = idealE F (x, eta))
    (hint : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x i) (Ioc 0 r)) :
    moments (correctedU F U debt) (correctedE F E debt) r eta = moments U E r eta + debt eta := by
  ext i
  unfold moments
  simp_rw [corrected_density F U E debt eta _ hU hE i]
  rw [integral_add (hint i)
    ((FiveProfileMoments.physicalDensity_integrable resetPatch (1 / 10)
      (idealAmplitude F eta) (idealU eta) (idealAmplitude_pos F eta).ne'
      (resetCoefficients F debt eta) i).integrableOn),
    physicalDensity_integral_prefix F debt eta r hr]
  exact congrArg (fun z : Debt => _ + z i) (resetCoefficients_equation F debt eta hs)

/-! ## Shape restoration in the same physical radius -/

noncomputable def restoredU (XR : ℝ) (old : Field) (p : Point) : ℝ :=
  let s := ShapeTransition.radialSwitch (XR * Real.exp (-8)) 1 p.1
  (1 - s) * old p + s * idealU p.2

theorem restoredU_before {XR X : ℝ} (hXR : 0 < XR)
    (hX : X ≤ XR * Real.exp (-8)) (old : Field) (eta : ℝ) :
    restoredU XR old (X, eta) = old (X, eta) := by
  simp only [restoredU, ShapeTransition.radialSwitch_zero
    (mul_pos hXR (Real.exp_pos _)) (by norm_num : (0 : ℝ) < 1) hX]
  ring

theorem restoredU_scaled {XR x : ℝ} (hXR : 0 < XR) (hx : 0 < x)
    (old : Field) (eta : ℝ) :
    restoredU XR old (XR * x, eta) =
      (1 - OutgoingSchedule.sigma (Real.log x + 8)) * old (XR * x, eta) +
        OutgoingSchedule.sigma (Real.log x + 8) * idealU eta := by
  have hdiv : XR * x / (XR * Real.exp (-8)) = x / Real.exp (-8) := by
    field_simp
  simp only [restoredU, ShapeTransition.radialSwitch_eq
    (mul_pos hXR (Real.exp_pos _)) (by norm_num : (0 : ℝ) < 1) (mul_pos hXR hx),
    hdiv, div_one, Real.log_div hx.ne' (Real.exp_pos _).ne', Real.log_exp, sub_neg_eq_add]

theorem restoredU_after {XR x : ℝ} (hXR : 0 < XR) (hx : Real.exp (-7) ≤ x)
    (old : Field) (eta : ℝ) : restoredU XR old (XR * x, eta) = idealU eta := by
  have hx0 := (Real.exp_pos (-7)).trans_le hx
  have hlog : -7 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  rw [restoredU_scaled hXR hx0 old eta,
    OutgoingSchedule.sigma_one (by linarith : 1 ≤ Real.log x + 8)]
  ring

noncomputable def preparedE (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf : Field)
    (p : Point) : ℝ :=
  Real.sqrt (2 * (matchingRadius F C * p.1)) *
    ShapeTransition.shapeField Xi T li oldf (matchingRadius F C * p.1, p.2)

noncomputable def preparedU (F : Profile) (C : ℝ) (oldU : Field) (p : Point) : ℝ :=
  restoredU (matchingRadius F C) oldU (matchingRadius F C * p.1, p.2)

theorem matching_clock (F : Profile) {C x : ℝ} (hC : 0 < C) (hx : 0 < x) :
    ShapeTransition.resetClock C F.data.core.P
      (Real.log (matchingRadius F C * x / Xi)) = Real.log x := by
  have hcp := mul_pos hC F.data.core.P_pos
  have hdiv : matchingRadius F C * x / Xi = (C * F.data.core.P) ^ 10 * x := by
    unfold matchingRadius ShapeTransition.resetRadius Xi
    ring
  rw [hdiv, Real.log_mul (pow_pos hcp 10).ne' hx.ne', Real.log_pow]
  unfold ShapeTransition.resetClock
  push_cast
  ring

theorem separation_clock (F : Profile) {C T x : ℝ} (hC : 0 < C)
    (hx : ShapeTransition.separation T C F.data.core.P ≤ x) :
    T ≤ Real.log (matchingRadius F C * x / Xi) := by
  have hp := pow_pos (mul_pos hC F.data.core.P_pos) 10
  have hx0 := (ShapeTransition.separation_pos T hC F.data.core.P_pos).trans_le hx
  have hdiv : matchingRadius F C * x / Xi = (C * F.data.core.P) ^ 10 * x := by
    unfold matchingRadius ShapeTransition.resetRadius Xi
    ring
  rw [hdiv]
  apply (Real.le_log_iff_exp_le (mul_pos hp hx0)).mpr
  exact (div_le_iff₀ hp).mp hx |>.trans_eq (mul_comm _ _)

theorem preparedE_ideal (F : Profile) {C T x : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hx : ShapeTransition.separation T C F.data.core.P ≤ x)
    (li : ℝ → ℝ) (oldf : Field) (eta : ℝ)
    (hold : oldf (matchingRadius F C * x, eta) =
      C⁻¹ * Real.exp (Real.log (matchingRadius F C * x / Xi) / 10 + li eta) /
        Real.sqrt (2 * (matchingRadius F C * x))) :
    preparedE F C T li oldf (x, eta) = idealE F (x, eta) := by
  have hx0 := (ShapeTransition.separation_pos T hC F.data.core.P_pos).trans_le hx
  have hX := mul_pos (matchingRadius_pos F hC) hx0
  unfold preparedE
  rw [ShapeTransition.shapeField_eq_profile Xi_pos hC hT hX li oldf eta hold,
    mul_div_cancel₀ _ (Real.sqrt_pos.2 (mul_pos (by norm_num : (0 : ℝ) < 2) hX)).ne',
    ShapeTransition.angular_after_reset_clock hC F.data.core.P_pos hT
      (separation_clock F hC hx) li eta, matching_clock F hC hx0]
  simp only [ShapeTransition.idealAngular, idealE, idealAmplitude,
    Real.rpow_def_of_pos hx0]
  congr 1
  congr 1
  ring

theorem preparedU_ideal (F : Profile) {C x : ℝ} (hC : 0 < C)
    (hx : Real.exp (-7) ≤ x) (oldU : Field) (eta : ℝ) :
    preparedU F C oldU (x, eta) = idealU eta :=
  restoredU_after (matchingRadius_pos F hC) hx oldU eta

/-! ## Splicing and the actual five-row debt -/

noncomputable def splice (r : ℝ) (inner outer : Field) (p : Point) : ℝ :=
  if p.1 ≤ r then inner p else outer p

theorem splice_inner {r : ℝ} (inner outer : Field) {p : Point} (hp : p.1 ≤ r) :
    splice r inner outer p = inner p := ite_eq_left hp

theorem splice_outer {r : ℝ} (inner outer : Field) {p : Point} (hp : r < p.1) :
    splice r inner outer p = outer p := ite_eq_right (not_le.mpr hp)

noncomputable def baseU (F : Profile) (C : ℝ) (oldU : Field) : Field :=
  splice matchFraction (preparedU F C oldU) F.U
noncomputable def baseE (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf : Field) : Field :=
  splice matchFraction (preparedE F C T li oldf) F.E

/-- This is the literal discrepancy of the five histories at the join. -/
noncomputable def actualDebt (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf oldU : Field)
    (eta : ℝ) : Debt :=
  moments F.U F.E matchFraction eta -
    moments (baseU F C oldU) (baseE F C T li oldf) matchFraction eta

noncomputable def joinedU (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf oldU : Field) : Field :=
  correctedU F (baseU F C oldU) (actualDebt F C T li oldf oldU)
noncomputable def joinedE (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf oldU : Field) : Field :=
  correctedE F (baseE F C T li oldf) (actualDebt F C T li oldf oldU)

theorem baseU_ideal (F : Profile) {C x : ℝ} (hC : 0 < C)
    (hx : x ∈ Ioo resetPatch.left resetPatch.right) (oldU : Field) (eta : ℝ) :
    baseU F C oldU (x, eta) = idealU eta := by
  rw [baseU, splice_inner _ _ hx.2.le]
  apply preparedU_ideal F hC _ oldU eta
  exact (Real.exp_le_exp.mpr (by norm_num : (-7 : ℝ) ≤ -6)).trans hx.1.le

theorem baseE_ideal (F : Profile) {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hsep : ShapeTransition.separation T C F.data.core.P ≤ Real.exp (-8))
    (li : ℝ → ℝ) (oldf : Field) (eta : ℝ)
    (hold : ∀ x ∈ Ioo resetPatch.left resetPatch.right,
      oldf (matchingRadius F C * x, eta) =
        C⁻¹ * Real.exp (Real.log (matchingRadius F C * x / Xi) / 10 + li eta) /
          Real.sqrt (2 * (matchingRadius F C * x))) :
    ∀ x ∈ Ioo resetPatch.left resetPatch.right,
      baseE F C T li oldf (x, eta) = idealE F (x, eta) := by
  intro x hx
  rw [baseE, splice_inner _ _ hx.2.le]
  exact preparedE_ideal F hC hT (hsep.trans
    ((Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -6)).trans hx.1.le)) li oldf eta (hold x hx)

theorem joined_moments_at_match (F : Profile) {C T : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hsep : ShapeTransition.separation T C F.data.core.P ≤ Real.exp (-8))
    (li : ℝ → ℝ) (oldf oldU : Field) (eta : ℝ)
    (hs : SmallDebt F (actualDebt F C T li oldf oldU) eta)
    (hold : ∀ x ∈ Ioo resetPatch.left resetPatch.right,
      oldf (matchingRadius F C * x, eta) =
        C⁻¹ * Real.exp (Real.log (matchingRadius F C * x / Xi) / 10 + li eta) /
          Real.sqrt (2 * (matchingRadius F C * x)))
    (hint : ∀ i : Fin 5, IntegrableOn (fun x => density
      (fun t => baseU F C oldU (t, eta)) (fun t => baseE F C T li oldf (t, eta)) x i)
        (Ioc 0 matchFraction)) :
    moments (joinedU F C T li oldf oldU) (joinedE F C T li oldf oldU) matchFraction eta =
      moments F.U F.E matchFraction eta := by
  rw [joinedU, joinedE, corrected_moments F _ _ _ eta matchFraction le_rfl hs
    (fun x hx => baseU_ideal F hC hx oldU eta) (baseE_ideal F hC hT hsep li oldf eta hold) hint]
  unfold actualDebt
  abel

theorem joined_after_match (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf oldU : Field)
    {p : Point} (hp : matchFraction < p.1) :
    joinedU F C T li oldf oldU p = F.U p ∧ joinedE F C T li oldf oldU p = F.E p := by
  have hn : p.1 ∉ Ioo resetPatch.left resetPatch.right := fun h => (not_le.mpr hp) h.2.le
  rcases corrected_unchanged F (baseU F C oldU) (baseE F C T li oldf)
    (actualDebt F C T li oldf oldU) p hn with ⟨hU, hE⟩
  exact ⟨hU.trans (splice_outer _ _ hp), hE.trans (splice_outer _ _ hp)⟩

/-- Equality of one prefix integral propagates along an identical exterior. -/
theorem prefix_integral_propagate {f g : ℝ → ℝ} {a r : ℝ} (har : a ≤ r)
    (hf : IntegrableOn f (Ioc 0 r)) (hg : IntegrableOn g (Ioc 0 r))
    (head : (∫ x in Ioc 0 a, f x) = ∫ x in Ioc 0 a, g x)
    (tail : ∀ x, a < x → f x = g x) :
    (∫ x in Ioc 0 r, f x) = ∫ x in Ioc 0 r, g x := by
  have hsub : Ioc (0 : ℝ) a ⊆ Ioc 0 r := Ioc_subset_Ioc_right har
  have he := MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := fun x => f x - g x) (μ := volume) measurableSet_Ioc hsub (by
      intro x hx
      have hax : a < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1.1, h⟩)
      change f x - g x = 0
      rw [tail x hax, sub_self])
  rw [integral_sub hf hg, integral_sub (hf.mono_set hsub) (hg.mono_set hsub), head,
    sub_self, sub_eq_zero] at he
  exact he

theorem moments_propagate {U E V G : Field} {a r eta : ℝ} (har : a ≤ r)
    (hU : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x i) (Ioc 0 r))
    (hV : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => V (t, eta)) (fun t => G (t, eta)) x i) (Ioc 0 r))
    (head : moments U E a eta = moments V G a eta)
    (tail : ∀ x, a < x → U (x, eta) = V (x, eta) ∧ E (x, eta) = G (x, eta)) :
    moments U E r eta = moments V G r eta := by
  ext i
  apply prefix_integral_propagate har (hU i) (hV i) (congrArg (fun z : Debt => z i) head)
  intro x hx
  rcases tail x hx with ⟨hUx, hEx⟩
  simp only [density, hUx, hEx]

theorem corrected_density_integrable (F : Profile) (U E : Field) (debt : ℝ → Debt)
    (eta r : ℝ)
    (hU : ∀ x ∈ Ioo resetPatch.left resetPatch.right, U (x, eta) = idealU eta)
    (hE : ∀ x ∈ Ioo resetPatch.left resetPatch.right, E (x, eta) = idealE F (x, eta))
    (hint : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x i) (Ioc 0 r))
    (i : Fin 5) : IntegrableOn (fun x => density
      (fun t => correctedU F U debt (t, eta)) (fun t => correctedE F E debt (t, eta)) x i)
        (Ioc 0 r) := by
  apply IntegrableOn.congr_fun ((hint i).add ((FiveProfileMoments.physicalDensity_integrable resetPatch (1 / 10)
    (idealAmplitude F eta) (idealU eta) (idealAmplitude_pos F eta).ne'
    (resetCoefficients F debt eta) i).integrableOn)) _ measurableSet_Ioc
  intro x _
  exact (corrected_density F U E debt eta x hU hE i).symm

theorem joined_moments (F : Profile) {C T r : ℝ} (hC : 0 < C) (hT : 0 < T)
    (hr : matchFraction ≤ r)
    (hsep : ShapeTransition.separation T C F.data.core.P ≤ Real.exp (-8))
    (li : ℝ → ℝ) (oldf oldU : Field) (eta : ℝ)
    (hs : SmallDebt F (actualDebt F C T li oldf oldU) eta)
    (hold : ∀ x ∈ Ioo resetPatch.left resetPatch.right,
      oldf (matchingRadius F C * x, eta) =
        C⁻¹ * Real.exp (Real.log (matchingRadius F C * x / Xi) / 10 + li eta) /
          Real.sqrt (2 * (matchingRadius F C * x)))
    (hint : ∀ i : Fin 5, IntegrableOn (fun x => density
      (fun t => baseU F C oldU (t, eta)) (fun t => baseE F C T li oldf (t, eta)) x i) (Ioc 0 r))
    (hout : ∀ i : Fin 5, IntegrableOn (fun x => density
      (fun t => F.U (t, eta)) (fun t => F.E (t, eta)) x i) (Ioc 0 r)) :
    moments (joinedU F C T li oldf oldU) (joinedE F C T li oldf oldU) r eta =
      moments F.U F.E r eta := by
  apply moments_propagate hr
    (corrected_density_integrable F _ _ _ eta r (fun x hx => baseU_ideal F hC hx oldU eta)
      (baseE_ideal F hC hT hsep li oldf eta hold) hint) hout
  · exact joined_moments_at_match F hC hT hsep li oldf oldU eta hs hold
      (fun i => (hint i).mono_set (Ioc_subset_Ioc_right hr))
  · exact fun x hx => joined_after_match F C T li oldf oldU hx

theorem joined_before_patch (F : Profile) (C T : ℝ) (li : ℝ → ℝ) (oldf oldU : Field)
    {p : Point} (hp : p.1 ≤ resetPatch.left) :
    joinedU F C T li oldf oldU p = preparedU F C oldU p ∧
      joinedE F C T li oldf oldU p = preparedE F C T li oldf p := by
  have hn : p.1 ∉ Ioo resetPatch.left resetPatch.right := fun h => (not_lt.mpr hp) h.1
  have hm : p.1 ≤ matchFraction := hp.trans resetPatch.ordered.le
  rcases corrected_unchanged F (baseU F C oldU) (baseE F C T li oldf)
    (actualDebt F C T li oldf oldU) p hn with ⟨hU, hE⟩
  exact ⟨hU.trans (splice_inner _ _ hm), hE.trans (splice_inner _ _ hm)⟩

/-! ## A concrete continuation of this axis witness -/

/-- These are only scalar clock choices.  No cone inequality or moment
compatibility is included in the data. -/
structure Controls {F : Profile} (A : AxisStage F) where
  referenceWidth : ℝ
  referenceWidth_pos : 0 < referenceWidth
  referenceWidth_small : 2 * referenceWidth < ReferencePath.rampLimit
  activationTime : ℝ
  activationTime_pos : 0 < activationTime
  activationTime_le : activationTime ≤ referenceWidth
  kappa : ℝ
  kappa_pos : 0 < kappa
  kappa_le_one : kappa ≤ 1
  axialWidth : ℝ
  axialWidth_pos : 0 < axialWidth
  angularWidth : ℝ
  angularWidth_pos : 0 < angularWidth
  before_big : referenceWidth ≤
    (A.activation referenceWidth referenceWidth_pos referenceWidth_small).bigTime
  finish : (A.activation referenceWidth referenceWidth_pos referenceWidth_small).bigTime +
    axialWidth + angularWidth ≤
      (A.activation referenceWidth referenceWidth_pos referenceWidth_small).finalTime
  shapeTime : ℝ
  shapeTime_pos : 0 < shapeTime

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def reference : TransitionRamp.StockReference ReferencePath.parameterInterval :=
  A.activation c.referenceWidth c.referenceWidth_pos c.referenceWidth_small

noncomputable def seedF : Field :=
  c.reference.physicalF c.activationTime c.kappa c.axialWidth c.angularWidth
noncomputable def seedU : Field :=
  c.reference.physicalU c.activationTime c.kappa c.axialWidth
noncomputable def initialShape : ℝ → ℝ :=
  c.reference.endpointLog c.activationTime c.kappa c.axialWidth c.angularWidth A.normalization
noncomputable def initialAxial : ℝ → ℝ :=
  c.reference.endpointU c.activationTime c.kappa c.axialWidth

theorem reference_radius : c.reference.radius0 = 4 / A.scale := rfl
theorem reference_profiles : c.reference.profiles =
    A.reference c.referenceWidth c.referenceWidth_pos c.referenceWidth_small := rfl
theorem reference_pressure : c.reference.profiles.pressure0 = F.axisDatum := rfl
theorem reference_before_big : 0 < c.reference.bigTime :=
  c.referenceWidth_pos.trans_le c.before_big
theorem radius_before_Xi : c.reference.radius0 < 110 :=
  (c.reference.radius0_lt_100 c.reference_before_big).trans (by norm_num)

theorem seedF_smooth : ContDiffOn ℝ ∞ c.seedF A.referenceInput.radialDomain.carrier :=
  TransitionRamp.physicalF_smooth A.natural.profile.family A.scale_pos A.small
    c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff
    c.activationTime_pos c.before_big c.axialWidth_pos c.angularWidth_pos

theorem seedU_smooth : ContDiffOn ℝ ∞ c.seedU A.referenceInput.radialDomain.carrier :=
  TransitionRamp.physicalU_smooth A.natural.profile.family A.scale_pos A.small
    c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff
    c.activationTime_pos c.before_big c.axialWidth_pos c.angularWidth_pos

theorem seedF_positive {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval) (hX : 0 ≤ p.1) :
    0 < c.seedF p := by
  apply TransitionRamp.physicalF_positive A.natural.profile.family A.scale_pos A.small
    c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff
    c.activationTime c.kappa c.axialWidth c.angularWidth _ hX
  exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le hX), hη⟩

theorem seed_initial {p : Point} (hp : p.1 ≤ 4 / A.scale) :
    c.seedF p = A.natural.profile.family.f p ∧ c.seedU p = A.natural.profile.family.U p :=
  A.activation_initial c.referenceWidth c.referenceWidth_pos c.referenceWidth_small
    c.activationTime c.kappa c.axialWidth c.angularWidth hp

theorem seed_activation {p : Point} (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hp : p.1 ≤ (4 / A.scale) * Real.exp c.referenceWidth) :
    c.seedF p = StressActivation.FromReference.f A.referenceInput
      c.activationTime c.kappa c.referenceWidth p ∧
    c.seedU p = StressActivation.FromReference.U A.referenceInput
      c.activationTime c.kappa c.referenceWidth p :=
  TransitionRamp.physical_fields_eq_activation A.natural.profile.family A.scale_pos A.small
    c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff
    c.activationTime_pos c.before_big c.axialWidth_pos c.angularWidth_pos hη hp

theorem initialShape_smooth : ContDiffOn ℝ ∞ c.initialShape ReferencePath.parameterInterval :=
  c.reference.endpointLog_smooth ReferencePath.parameterInterval_open _ _ _ _ _

theorem initialAxial_smooth : ContDiffOn ℝ ∞ c.initialAxial ReferencePath.parameterInterval :=
  c.reference.endpointU_smooth ReferencePath.parameterInterval_open _ _ _

theorem seedF_held {X eta : ℝ} (hX : Xi ≤ X) (hη : eta ∈ ReferencePath.parameterInterval) :
    c.seedF (X, eta) = A.normalization⁻¹ *
      Real.exp (Real.log (X / Xi) / 10 + c.initialShape eta) / Real.sqrt (2 * X) :=
  c.reference.physicalF_held ReferencePath.parameterInterval_open c.angularWidth_pos c.finish
    c.radius_before_Xi A.normalization_pos hX hη

theorem seedU_held {X eta : ℝ} (hX : Xi ≤ X) (hη : eta ∈ ReferencePath.parameterInterval) :
    c.seedU (X, eta) = c.initialAxial eta :=
  c.reference.physicalU_held ReferencePath.parameterInterval_open c.axialWidth_pos
    (by
      have hf : c.reference.bigTime + c.axialWidth + c.angularWidth ≤ c.reference.finalTime := c.finish
      linarith [c.angularWidth_pos]) c.radius_before_Xi hX hη

theorem initialShape_value {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) :
    c.initialShape eta = Real.log (A.normalization * (Real.sqrt (2 * Xi) * c.seedF (Xi, eta))) :=
  c.reference.endpointLog_eq_actual ReferencePath.parameterInterval_open c.angularWidth_pos
    c.finish c.radius_before_Xi A.normalization_pos hη

/-- The nominal fields are functions of the actual stock-controlled seed. -/
noncomputable def debt : ℝ → Debt :=
  actualDebt F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
noncomputable def normalizedE : Field :=
  joinedE F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
noncomputable def normalizedU : Field :=
  joinedU F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
noncomputable def radius (_c : Controls A) : ℝ := matchingRadius F A.normalization
noncomputable def E (p : Point) : ℝ := c.normalizedE (p.1 / c.radius, p.2)
noncomputable def U (p : Point) : ℝ := c.normalizedU (p.1 / c.radius, p.2)
noncomputable def H (p : Point) : ℝ := Real.sqrt (2 * p.1) * c.E p
noncomputable def Pi (p : Point) : ℝ :=
  F.axisDatum p.2 + moments c.U c.E p.1 p.2 4

theorem radius_pos : 0 < c.radius := matchingRadius_pos F A.normalization_pos

theorem normalized_after_match {p : Point} (hp : matchFraction < p.1) :
    c.normalizedU p = F.U p ∧ c.normalizedE p = F.E p :=
  joined_after_match F A.normalization c.shapeTime c.initialShape c.seedF c.seedU hp

theorem physical_after_match {p : Point} (hp : c.radius * matchFraction < p.1) :
    c.U p = OutgoingDilation.U F c.radius p ∧ c.E p = OutgoingDilation.E F c.radius p :=
  c.normalized_after_match ((lt_div_iff₀ c.radius_pos).mpr (by simpa only [mul_comm] using hp))

theorem shape_clock_after_Xi {x : ℝ}
    (hx : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ x) :
    Xi ≤ c.radius * x := by
  have he : 1 ≤ Real.exp c.shapeTime := Real.one_le_exp_iff.mpr c.shapeTime_pos.le
  have hs : c.radius * ShapeTransition.separation c.shapeTime A.normalization F.data.core.P =
      Xi * Real.exp c.shapeTime :=
    ShapeTransition.resetRadius_mul_separation Xi c.shapeTime A.normalization F.data.core.P
      (mul_pos A.normalization_pos F.data.core.P_pos).ne'
  calc
    Xi ≤ Xi * Real.exp c.shapeTime := le_mul_of_one_le_right Xi_pos.le he
    _ = c.radius * ShapeTransition.separation c.shapeTime A.normalization F.data.core.P := hs.symm
    _ ≤ c.radius * x := mul_le_mul_of_nonneg_left hx c.radius_pos.le

theorem held_on_patch
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) :
    ∀ x ∈ Ioo resetPatch.left resetPatch.right,
      c.seedF (c.radius * x, eta) = A.normalization⁻¹ *
        Real.exp (Real.log (c.radius * x / Xi) / 10 + c.initialShape eta) /
          Real.sqrt (2 * (c.radius * x)) := by
  intro x hx
  apply c.seedF_held _ hη
  exact c.shape_clock_after_Xi (hsep.trans
    ((Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -6)).trans hx.1.le))

theorem physical_before_Xi
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hp : p.1 ≤ Xi) :
    c.U p = c.seedU p ∧ c.E p = Real.sqrt (2 * p.1) * c.seedF p := by
  have hi : Xi ≤ c.radius * Real.exp (-8) := c.shape_clock_after_Xi hsep
  have hx : p.1 / c.radius ≤ Real.exp (-8) := (div_le_iff₀ c.radius_pos).mpr
    (by simpa only [mul_comm] using hp.trans hi)
  have hb : p.1 / c.radius ≤ resetPatch.left := hx.trans
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -6))
  have he := joined_before_patch F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
    (p := (p.1 / c.radius, p.2)) hb
  change c.U p = c.seedU p ∧ c.E p = Real.sqrt (2 * p.1) * c.seedF p
  constructor
  · change joinedU F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
      (p.1 / c.radius, p.2) = _
    rw [he.1]
    change restoredU c.radius c.seedU (c.radius * (p.1 / c.radius), p.2) = _
    rw [mul_div_cancel₀ _ c.radius_pos.ne', restoredU_before c.radius_pos (hp.trans hi)]
  · change joinedE F A.normalization c.shapeTime c.initialShape c.seedF c.seedU
      (p.1 / c.radius, p.2) = _
    rw [he.2]
    change Real.sqrt (2 * (c.radius * (p.1 / c.radius))) *
      ShapeTransition.shapeField Xi c.shapeTime c.initialShape c.seedF
        (c.radius * (p.1 / c.radius), p.2) = _
    rw [mul_div_cancel₀ _ c.radius_pos.ne',
      ShapeTransition.shapeField_before Xi_pos c.shapeTime_pos hp]

noncomputable def f (p : Point) : ℝ :=
  if p.1 ≤ Xi then c.seedF p else c.E p / Real.sqrt (2 * p.1)

theorem f_before_Xi {p : Point} (hp : p.1 ≤ Xi) : c.f p = c.seedF p := ite_eq_left hp

theorem E_eq_sqrt_mul_f
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) : c.E p = Real.sqrt (2 * p.1) * c.f p := by
  by_cases hp : p.1 ≤ Xi
  · rw [c.f_before_Xi hp]
    exact (c.physical_before_Xi hsep hp).2
  · rw [f, ite_eq_right hp, mul_div_cancel₀ _
      (Real.sqrt_pos.2 (mul_pos (by norm_num : (0 : ℝ) < 2) hX)).ne']

theorem natural_prefix
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    (hscale : 1 ≤ A.scale) {p : Point} (hp : p.1 ≤ 4 / A.scale) :
    c.f p = A.natural.profile.family.f p ∧ c.U p = A.natural.profile.family.U p := by
  have hXi : (4 : ℝ) / A.scale ≤ Xi := by
    apply (div_le_iff₀ A.scale_pos).mpr
    have := mul_le_mul_of_nonneg_left hscale Xi_pos.le
    norm_num [Xi] at *
    linarith
  exact ⟨(c.f_before_Xi (hp.trans hXi)).trans (c.seed_initial hp).1,
    (c.physical_before_Xi hsep (hp.trans hXi)).1.trans (c.seed_initial hp).2⟩

end Controls

/-- All elementary clock constraints can be achieved with arbitrarily small
widths after the axis profile and its normalization have been fixed. -/
theorem controls_exist {F : Profile} (A : AxisStage F) (hscale : 1 ≤ A.scale)
    (T : ℝ) (hT : 0 < T) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : Controls A, c.shapeTime = T ∧ c.referenceWidth < eps ∧
      c.activationTime < eps ∧ c.kappa < eps ∧ c.axialWidth < eps ∧ c.angularWidth < eps := by
  let δ := min A.preparation.delta (min (ReferencePath.rampLimit / 4) (eps / 2))
  have hδ : 0 < δ := lt_min A.preparation.delta_pos
    (lt_min (div_pos ReferencePath.rampLimit_pos (by norm_num)) (half_pos heps))
  have hδlim : δ ≤ ReferencePath.rampLimit / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδeps : δ < eps := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self heps)
  have hδT : 2 * δ < ReferencePath.rampLimit := by linarith [ReferencePath.rampLimit_pos]
  let R := A.activation δ hδ hδT
  have hb : δ ≤ R.bigTime := by
    have hf := A.referenceInput.freeze_before_Xbig hscale hδT
    have he : Real.exp (2 * δ) < 100 / R.radius0 := by
      apply (lt_div_iff₀ R.radius0_pos).mpr
      simp only [R, AxisStage.activation, TransitionRamp.ofNatural, ReferencePath.Input.Xbig,
        mul_comm] at hf ⊢
      exact hf
    have ht : 2 * δ < R.bigTime :=
      (Real.lt_log_iff_exp_lt (div_pos (by norm_num) R.radius0_pos)).mpr he
    linarith
  let gap := R.finalTime - R.bigTime
  have hgap : 0 < gap := sub_pos.mpr R.finalTime_gt_bigTime
  let w := min (gap / 4) (eps / 2)
  have hw : 0 < w := lt_min (div_pos hgap (by norm_num)) (half_pos heps)
  have hweps : w < eps := (min_le_right _ _).trans_lt (half_lt_self heps)
  have hfinish : R.bigTime + w + w ≤ R.finalTime := by
    have h := min_le_left (gap / 4) (eps / 2)
    dsimp only [gap] at h
    change w ≤ (R.finalTime - R.bigTime) / 4 at h
    linarith [R.finalTime_gt_bigTime]
  let κ := min (1 / 2 : ℝ) (eps / 2)
  have hκ : 0 < κ := lt_min (by norm_num) (half_pos heps)
  have hκ1 : κ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hκeps : κ < eps := (min_le_right _ _).trans_lt (half_lt_self heps)
  let c : Controls A := ⟨δ, hδ, hδT, δ / 2, half_pos hδ, (half_le_self hδ.le),
    κ, hκ, hκ1, w, hw, w, hw, hb, hfinish, T, hT⟩
  exact ⟨c, rfl, hδeps, (half_lt_self hδ).trans hδeps, hκeps, hweps, hweps⟩

/-! ## Regular parameter-dependent prefix integrals -/

noncomputable def scaledDomain (D : ProfileHistories.RadialDomain) (R : ℝ) :
    ProfileHistories.RadialDomain where
  carrier := {p | (R * p.1, p.2) ∈ D.carrier}
  isOpen := D.isOpen.preimage ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  scale_mem := by
    intro p hp t ht
    have hs := D.scale_mem (R * p.1, p.2) hp t ht
    change (R * (t * p.1), p.2) ∈ D.carrier
    simpa only [mul_left_comm R t] using hs

noncomputable def regularDensity {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (p : Point) : Debt :=
  ![P.U p, P.H p, P.transportDensity p, P.energyDensity p, P.f p ^ 2]

theorem regularDensity_smooth {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (i : Fin 5) :
    ContDiffOn ℝ ∞ (fun p => regularDensity P p i) D.carrier := by
  fin_cases i
  · exact P.U_smooth
  · exact P.H_smooth
  · exact P.transportDensity_smooth
  · exact P.energyDensity_smooth
  · exact P.f_smooth.pow 2

theorem regularDensity_eq {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) {x : ℝ} (hx : 0 < x) (eta : ℝ) :
    density (fun t => P.U (t, eta)) (fun t => P.E (t, eta)) x = regularDensity P (x, eta) := by
  ext i
  fin_cases i
  · rfl
  · change Real.sqrt (2 * x) * (Real.sqrt (2 * x) * P.f (x, eta)) = 2 * x * P.f (x, eta)
    rw [← mul_assoc, Real.mul_self_sqrt (show 0 ≤ 2 * x by positivity)]
  · change P.U (x, eta) * Real.sqrt (2 * x) * (Real.sqrt (2 * x) * P.f (x, eta)) =
      P.U (x, eta) * (2 * x * P.f (x, eta))
    calc
      _ = (Real.sqrt (2 * x) * Real.sqrt (2 * x)) * (P.U (x, eta) * P.f (x, eta)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (show 0 ≤ 2 * x by positivity)]; ring
  · change P.U (x, eta) ^ 2 - (Real.sqrt (2 * x) * P.f (x, eta)) ^ 2 / 2 =
      P.U (x, eta) ^ 2 - x * P.f (x, eta) ^ 2
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ 2 * x by positivity)]
    ring
  · change (Real.sqrt (2 * x) * P.f (x, eta)) ^ 2 / (2 * x) = P.f (x, eta) ^ 2
    rw [mul_pow, Real.sq_sqrt (show 0 ≤ 2 * x by positivity),
      mul_div_cancel_left₀ _ (show 2 * x ≠ 0 by positivity)]

theorem regularDensity_integrable {D : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) {r eta : ℝ} (hp : (r, eta) ∈ D.carrier) (i : Fin 5) :
    IntegrableOn (fun x => regularDensity P (x, eta) i) (Ioc 0 r) :=
  (ProfileHistories.radial_slice_intervalIntegrable D (regularDensity_smooth P i) hp).1

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def shapedF : Field :=
  ShapeTransition.shapeField Xi c.shapeTime c.initialShape c.seedF

theorem shapedF_smooth : ContDiffOn ℝ ∞ c.shapedF A.referenceInput.radialDomain.carrier := by
  apply c.seedF_smooth.mul
  apply ContDiffOn.exp
  apply ContDiffOn.mul
  · exact ((ShapeTransition.radialSwitch_contDiff Xi_pos c.shapeTime_pos).comp contDiff_fst).contDiffOn
  · exact (ShapeTransition.logShape_contDiff.comp contDiff_snd).contDiffOn.sub
      (c.initialShape_smooth.comp contDiffOn_snd (fun _ hp => hp.2))

theorem restored_seed_smooth :
    ContDiffOn ℝ ∞ (restoredU c.radius c.seedU) A.referenceInput.radialDomain.carrier := by
  have hs : ContDiff ℝ ∞ (fun p : Point =>
      ShapeTransition.radialSwitch (c.radius * Real.exp (-8)) 1 p.1) :=
    (ShapeTransition.radialSwitch_contDiff (mul_pos c.radius_pos (Real.exp_pos _))
      (by norm_num)).comp contDiff_fst
  exact ((contDiffOn_const.sub hs.contDiffOn).mul c.seedU_smooth).add
    (hs.contDiffOn.mul (idealU_smooth.comp contDiff_snd).contDiffOn)

noncomputable def preparedDomain : ProfileHistories.RadialDomain :=
  scaledDomain A.referenceInput.radialDomain c.radius

theorem preparedDomain_nonnegative {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ ReferencePath.parameterInterval) : p ∈ c.preparedDomain.carrier := by
  exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le (mul_nonneg c.radius_pos.le hX)), hη⟩

noncomputable def preparedProfiles : ProfileHistories.Profiles c.preparedDomain where
  f := fun p => Real.sqrt c.radius * c.shapedF (c.radius * p.1, p.2)
  U := preparedU F A.normalization c.seedU
  f_smooth := contDiffOn_const.mul (c.shapedF_smooth.comp
    ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hp => hp))
  U_smooth := c.restored_seed_smooth.comp
    ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn (fun _ hp => hp)
  pressure0 := F.axisDatum
  pressure0_smooth := fun _ _ => F.axisDatum_contDiff.contDiffAt

theorem preparedProfiles_U (p : Point) :
    c.preparedProfiles.U p = preparedU F A.normalization c.seedU p := rfl

theorem preparedProfiles_E {p : Point} (hX : 0 < p.1) :
    c.preparedProfiles.E p = preparedE F A.normalization c.shapeTime c.initialShape c.seedF p := by
  change Real.sqrt (2 * p.1) *
    (Real.sqrt c.radius * c.shapedF (c.radius * p.1, p.2)) =
      Real.sqrt (2 * (c.radius * p.1)) * c.shapedF (c.radius * p.1, p.2)
  rw [← mul_assoc, ← Real.sqrt_mul (show 0 ≤ 2 * p.1 by positivity)]
  congr 2
  ring

theorem base_density_before {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) matchFraction) (eta : ℝ) :
    density (fun t => baseU F A.normalization c.seedU (t, eta))
      (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x =
        regularDensity c.preparedProfiles (x, eta) := by
  have hU : baseU F A.normalization c.seedU (x, eta) = c.preparedProfiles.U (x, eta) :=
    splice_inner _ _ hx.2
  have hE : baseE F A.normalization c.shapeTime c.initialShape c.seedF (x, eta) =
      c.preparedProfiles.E (x, eta) :=
    (splice_inner _ _ hx.2).trans (c.preparedProfiles_E hx.1).symm
  calc
    _ = density (fun t => c.preparedProfiles.U (t, eta))
        (fun t => c.preparedProfiles.E (t, eta)) x := by simp only [density, hU, hE]
    _ = _ := regularDensity_eq c.preparedProfiles hx.1 eta

theorem base_density_integrable_before {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval)
    (i : Fin 5) : IntegrableOn (fun x => density
      (fun t => baseU F A.normalization c.seedU (t, eta))
      (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x i)
        (Ioc 0 matchFraction) := by
  apply IntegrableOn.congr_fun (regularDensity_integrable c.preparedProfiles
    (c.preparedDomain_nonnegative matchFraction_pos.le hη) i) _ measurableSet_Ioc
  exact fun x hx => congrArg (fun q : Debt => q i) (c.base_density_before hx eta).symm

theorem base_moments_before (eta : ℝ) :
    moments (baseU F A.normalization c.seedU)
      (baseE F A.normalization c.shapeTime c.initialShape c.seedF) matchFraction eta =
        fun i => ProfileHistories.primitive (fun p => regularDensity c.preparedProfiles p i)
          (matchFraction, eta) := by
  ext i
  rw [ProfileHistories.primitive, intervalIntegral.integral_of_le matchFraction_pos.le]
  apply setIntegral_congr_fun measurableSet_Ioc
  exact fun x hx => congrArg (fun q : Debt => q i) (c.base_density_before hx eta)

theorem base_moments_smooth : ContDiffOn ℝ ∞ (fun eta =>
    moments (baseU F A.normalization c.seedU)
      (baseE F A.normalization c.shapeTime c.initialShape c.seedF) matchFraction eta)
        ReferencePath.parameterInterval := by
  have he : (fun eta => moments (baseU F A.normalization c.seedU)
      (baseE F A.normalization c.shapeTime c.initialShape c.seedF) matchFraction eta) =
      fun eta i => ProfileHistories.primitive (fun p => regularDensity c.preparedProfiles p i)
        (matchFraction, eta) := funext c.base_moments_before
  rw [he]
  apply contDiffOn_pi.mpr
  intro i
  exact (ProfileHistories.primitive_smooth c.preparedDomain
    (regularDensity_smooth c.preparedProfiles i)).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hη => c.preparedDomain_nonnegative matchFraction_pos.le hη)

end Controls

noncomputable def idealPrefixRows (F : Profile) (r eta : ℝ) : Debt :=
  let a := idealAmplitude F eta
  let u := idealU eta
  let c0 := ∫ _x in Ioc (0 : ℝ) r, (1 : ℝ)
  let c1 := ∫ x in Ioc (0 : ℝ) r, Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)
  let c2 := ∫ x in Ioc (0 : ℝ) r, (x ^ (1 / 10 : ℝ)) ^ 2
  let c3 := ∫ x in Ioc (0 : ℝ) r, (x ^ (1 / 10 : ℝ)) ^ 2 / x
  ![u * c0, a * c1, (u * a) * c1, u ^ 2 * c0 - (a ^ 2 / 2) * c2, (a ^ 2 / 2) * c3]

theorem outgoing_moments_ideal (F : Profile) {r : ℝ} (hr : r ≤ 1) (eta : ℝ) :
    moments F.U F.E r eta = idealPrefixRows F r eta := by
  have hvals : ∀ x ∈ Ioc (0 : ℝ) r,
      F.U (x, eta) = idealU eta ∧ F.E (x, eta) = idealAmplitude F eta * x ^ (1 / 10 : ℝ) :=
    fun x hx => ⟨F.U_ideal eta hx.1 (hx.2.trans hr), F.E_ideal eta hx.1 (hx.2.trans hr)⟩
  have hrows : moments F.U F.E r eta = fun i => ∫ x in Ioc (0 : ℝ) r,
      ![idealU eta * 1,
        idealAmplitude F eta * (Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)),
        (idealU eta * idealAmplitude F eta) * (Real.sqrt (2 * x) * x ^ (1 / 10 : ℝ)),
        (idealU eta) ^ 2 * 1 - ((idealAmplitude F eta) ^ 2 / 2) * (x ^ (1 / 10 : ℝ)) ^ 2,
        ((idealAmplitude F eta) ^ 2 / 2) * ((x ^ (1 / 10 : ℝ)) ^ 2 / x)] i := by
    ext i
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    rcases hvals x hx with ⟨hU, hE⟩
    fin_cases i <;> simp [density, hU, hE] <;> ring
  rw [hrows]
  have hc0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 r) := continuous_const.integrableOn_Ioc
  have hc2 : IntegrableOn (fun x : ℝ => (x ^ (1 / 10 : ℝ)) ^ 2) (Ioc 0 r) :=
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 10)).pow 2).integrableOn_Ioc
  ext i
  fin_cases i <;> simp only [idealPrefixRows]
  · exact integral_const_mul _ _
  · exact integral_const_mul _ _
  · exact integral_const_mul _ _
  · change (∫ x in Ioc (0 : ℝ) r,
        idealU eta ^ 2 * 1 - (idealAmplitude F eta ^ 2 / 2) * (x ^ (1 / 10 : ℝ)) ^ 2) =
      idealU eta ^ 2 * (∫ _x in Ioc (0 : ℝ) r, (1 : ℝ)) -
        (idealAmplitude F eta ^ 2 / 2) * (∫ x in Ioc (0 : ℝ) r, (x ^ (1 / 10 : ℝ)) ^ 2)
    rw [integral_sub (hc0.const_mul _) (hc2.const_mul _), integral_const_mul, integral_const_mul]
  · exact integral_const_mul _ _

theorem outgoing_prefix_smooth (F : Profile) {r : ℝ} (hr : r ≤ 1) :
    ContDiff ℝ ∞ (fun eta => moments F.U F.E r eta) := by
  have he : (fun eta => moments F.U F.E r eta) = idealPrefixRows F r :=
    funext (outgoing_moments_ideal F hr)
  rw [he]
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact idealU_smooth.mul contDiff_const
  · exact (idealAmplitude_smooth F).mul contDiff_const
  · exact (idealU_smooth.mul (idealAmplitude_smooth F)).mul contDiff_const
  · exact ((idealU_smooth.pow 2).mul contDiff_const).sub
      (((idealAmplitude_smooth F).pow 2).div_const 2 |>.mul contDiff_const)
  · exact (((idealAmplitude_smooth F).pow 2).div_const 2).mul contDiff_const

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem debt_smooth : ContDiffOn ℝ ∞ c.debt ReferencePath.parameterInterval :=
  (outgoing_prefix_smooth F matchFraction_lt_one.le).contDiffOn.sub c.base_moments_smooth

theorem repair_coefficients_smooth
    (hs : ∀ eta ∈ ReferencePath.parameterInterval, SmallDebt F c.debt eta) :
    ContDiffOn ℝ ∞ (resetCoefficients F c.debt) ReferencePath.parameterInterval :=
  resetCoefficients_smooth F c.debt_smooth hs

theorem moments_at_match
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) (hs : SmallDebt F c.debt eta) :
    moments c.normalizedU c.normalizedE matchFraction eta = moments F.U F.E matchFraction eta :=
  joined_moments_at_match F A.normalization_pos c.shapeTime_pos hsep c.initialShape c.seedF c.seedU
    eta hs (c.held_on_patch hsep hη) (c.base_density_integrable_before hη)

end Controls

/-! ## Smooth gluing on a genuine overlap -/

theorem splice_smoothOn {V : Set Point} (hV : IsOpen V) {r b : ℝ} (hr : 0 < r)
    (hrb : r < b) {inner outer : Field} (hi : ContDiffOn ℝ ∞ inner V)
    (ho : ContDiffOn ℝ ∞ outer (V ∩ {p : Point | 0 < p.1}))
    (he : ∀ p ∈ V, r < p.1 → p.1 < b → inner p = outer p) :
    ContDiffOn ℝ ∞ (splice r inner outer) V := by
  intro p hp
  by_cases hb : p.1 < b
  · apply ((hi.contDiffAt (hV.mem_nhds hp)).congr_of_eventuallyEq _).contDiffWithinAt
    filter_upwards [hV.mem_nhds hp, continuousAt_fst.eventually (Iio_mem_nhds hb)] with q hq hqb
    by_cases hqr : q.1 ≤ r
    · exact splice_inner _ _ hqr
    · exact (splice_outer _ _ (lt_of_not_ge hqr)).trans (he q hq (lt_of_not_ge hqr) hqb).symm
  · have hpr : r < p.1 := hrb.trans_le (le_of_not_gt hb)
    have hop : IsOpen (V ∩ {q : Point | 0 < q.1}) :=
      hV.inter (isOpen_lt continuous_const continuous_fst)
    apply ((ho.contDiffAt (hop.mem_nhds ⟨hp, hr.trans hpr⟩)).congr_of_eventuallyEq _).contDiffWithinAt
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hpr)] with q hq
    exact splice_outer _ _ hq

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem prepared_overlap
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {x eta : ℝ} (hx : matchFraction ≤ x) (hx1 : x ≤ 1)
    (hη : eta ∈ ReferencePath.parameterInterval) :
    c.preparedProfiles.U (x, eta) = F.U (x, eta) ∧
      c.preparedProfiles.E (x, eta) = F.E (x, eta) := by
  have hx0 := matchFraction_pos.trans_le hx
  have hxs : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ x :=
    hsep.trans ((Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5)).trans hx)
  constructor
  · rw [c.preparedProfiles_U, preparedU_ideal F A.normalization_pos
      ((Real.exp_le_exp.mpr (by norm_num : (-7 : ℝ) ≤ -5)).trans hx)]
    exact (F.U_ideal eta hx0 hx1).symm
  · rw [c.preparedProfiles_E hx0, preparedE_ideal F A.normalization_pos c.shapeTime_pos hxs
      c.initialShape c.seedF eta (c.seedF_held (c.shape_clock_after_Xi hxs) hη)]
    exact (F.E_ideal eta hx0 hx1).symm

noncomputable def baseRegularF : Field :=
  splice matchFraction c.preparedProfiles.f (fun p => F.E p / Real.sqrt (2 * p.1))

theorem baseRegularF_smooth
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8)) :
    ContDiffOn ℝ ∞ c.baseRegularF c.preparedDomain.carrier := by
  apply splice_smoothOn c.preparedDomain.isOpen matchFraction_pos
    (Real.exp_lt_exp.mpr (by norm_num : (-5 : ℝ) < -4)) c.preparedProfiles.f_smooth
  · exact (F.E_contDiffOn.mono (fun _ hp => ⟨hp.2, mem_univ _⟩)).div
      ((contDiffOn_const.mul contDiffOn_fst).sqrt
        (fun p hp => (mul_pos (by norm_num : (0 : ℝ) < 2) hp.2).ne'))
      (fun p hp => (Real.sqrt_pos.2 (mul_pos (by norm_num : (0 : ℝ) < 2) hp.2)).ne')
  · intro p hp hpr hpb
    have hx := matchFraction_pos.trans hpr
    have hp1 : p.1 ≤ 1 := hpb.le.trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-4 : ℝ) ≤ 0))
    apply (eq_div_iff (Real.sqrt_pos.2 (show 0 < 2 * p.1 by positivity)).ne').mpr
    simpa only [ProfileHistories.Profiles.E, mul_comm] using
      (c.prepared_overlap hsep hpr.le hp1 hp.2).2

theorem baseU_smooth
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8)) :
    ContDiffOn ℝ ∞ (baseU F A.normalization c.seedU) c.preparedDomain.carrier := by
  apply splice_smoothOn c.preparedDomain.isOpen matchFraction_pos
    (Real.exp_lt_exp.mpr (by norm_num : (-5 : ℝ) < -4)) c.preparedProfiles.U_smooth
  · exact F.U_contDiffOn.mono (fun _ hp => ⟨hp.2, mem_univ _⟩)
  · intro p hp hpr hpb
    exact (c.prepared_overlap hsep hpr.le
      (hpb.le.trans (Real.exp_le_one_iff.mpr (by norm_num : (-4 : ℝ) ≤ 0))) hp.2).1

noncomputable def baseProfiles
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8)) :
    ProfileHistories.Profiles c.preparedDomain where
  f := c.baseRegularF
  U := baseU F A.normalization c.seedU
  f_smooth := c.baseRegularF_smooth hsep
  U_smooth := c.baseU_smooth hsep
  pressure0 := F.axisDatum
  pressure0_smooth := fun _ _ => F.axisDatum_contDiff.contDiffAt

theorem baseProfiles_E
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) :
    (c.baseProfiles hsep).E p = baseE F A.normalization c.shapeTime c.initialShape c.seedF p := by
  by_cases hp : p.1 ≤ matchFraction
  · change Real.sqrt (2 * p.1) * c.baseRegularF p = _
    rw [baseRegularF, splice_inner _ _ hp]
    exact (c.preparedProfiles_E hX).trans (splice_inner _ _ hp).symm
  · change Real.sqrt (2 * p.1) * c.baseRegularF p = _
    rw [baseRegularF, splice_outer _ _ (lt_of_not_ge hp), baseE,
      splice_outer _ _ (lt_of_not_ge hp), mul_div_cancel₀ _
      (Real.sqrt_pos.2 (show 0 < 2 * p.1 by positivity)).ne']

theorem base_density_eq
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {x : ℝ} (hx : 0 < x) (eta : ℝ) :
    density (fun t => baseU F A.normalization c.seedU (t, eta))
      (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x =
        regularDensity (c.baseProfiles hsep) (x, eta) := by
  have he := regularDensity_eq (c.baseProfiles hsep) hx eta
  simp only [density, c.baseProfiles_E hsep (p := (x, eta)) hx] at he ⊢
  exact he

theorem base_density_integrable
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {r eta : ℝ} (hr : 0 ≤ r) (hη : eta ∈ ReferencePath.parameterInterval) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => baseU F A.normalization c.seedU (t, eta))
      (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x i) (Ioc 0 r) := by
  apply IntegrableOn.congr_fun (regularDensity_integrable (c.baseProfiles hsep)
    (c.preparedDomain_nonnegative hr hη) i) _ measurableSet_Ioc
  exact fun x hx => congrArg (fun q : Debt => q i) (c.base_density_eq hsep hx.1 eta).symm

theorem baseE_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval) :
    ContDiffAt ℝ ∞ (baseE F A.normalization c.shapeTime c.initialShape c.seedF) p := by
  have hs := (c.baseRegularF_smooth hsep).contDiffAt
    (c.preparedDomain.isOpen.mem_nhds (c.preparedDomain_nonnegative hX.le hη))
  have hf : ContDiffAt ℝ ∞ (c.baseProfiles hsep).E p :=
    ((contDiffAt_const.mul contDiffAt_fst).sqrt (show 2 * p.1 ≠ 0 by positivity)).mul hs
  apply hf.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with q hq
  exact (c.baseProfiles_E hsep hq).symm

theorem coefficients_smoothAt {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) : ContDiffAt ℝ ∞ (resetCoefficients F c.debt) eta := by
  have hn := (FiveProfileMoments.normalizedDebt_contDiffOn (idealAmplitude_smooth F).contDiffOn
    idealU_smooth.contDiffOn c.debt_smooth (fun e _ => (idealAmplitude_pos F e).ne')).contDiffAt
      (ReferencePath.parameterInterval_open.mem_nhds hη)
  exact (resetSolver.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds (smallDebt_mem hs))).comp eta hn

end Controls

theorem correction_smoothAt {n : ℕ} (P : FiveProfileMoments.Patch)
    {coef : ℝ → Fin n → ℝ} {p : Point} (hc : ContDiffAt ℝ ∞ coef p.2) :
    ContDiffAt ℝ ∞ (fun q : Point => FiveProfileMoments.correction P (coef q.2) q.1) p := by
  apply ContDiffAt.sum
  intro i _
  exact ((contDiffAt_pi.mp hc i).comp p contDiffAt_snd).mul
    ((FiveProfileMoments.bump_contDiff P i).contDiffAt.comp p contDiffAt_fst)

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem normalizedU_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hp : p ∈ c.preparedDomain.carrier) (hs : SmallDebt F c.debt p.2) :
    ContDiffAt ℝ ∞ c.normalizedU p := by
  have hb := (c.baseU_smooth hsep).contDiffAt (c.preparedDomain.isOpen.mem_nhds hp)
  have hc := c.coefficients_smoothAt hp.2 hs
  exact hb.add (((idealAmplitude_smooth F).contDiffAt.comp p contDiffAt_snd).mul
    (correction_smoothAt resetPatch.leftHalf (p := p) hc.fst))

theorem normalizedE_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt p.2) : ContDiffAt ℝ ∞ c.normalizedE p := by
  have hc := c.coefficients_smoothAt hη hs
  exact (c.baseE_smoothAt hsep hX hη).add
    (((idealAmplitude_smooth F).contDiffAt.comp p contDiffAt_snd).mul
      (correction_smoothAt resetPatch.rightHalf (p := p) hc.snd))

theorem U_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hp : p ∈ A.referenceInput.radialDomain.carrier) (hs : SmallDebt F c.debt p.2) :
    ContDiffAt ℝ ∞ c.U p := by
  have hq : (p.1 / c.radius, p.2) ∈ c.preparedDomain.carrier := by
    change (c.radius * (p.1 / c.radius), p.2) ∈ A.referenceInput.radialDomain.carrier
    simpa only [mul_div_cancel₀ _ c.radius_pos.ne', Prod.eta] using hp
  exact (c.normalizedU_smoothAt hsep hq hs).comp p
    ((contDiffAt_fst.div_const c.radius).prodMk contDiffAt_snd)

theorem E_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt p.2) : ContDiffAt ℝ ∞ c.E p :=
  (c.normalizedE_smoothAt hsep (p := (p.1 / c.radius, p.2)) (div_pos hX c.radius_pos) hη hs).comp p
    ((contDiffAt_fst.div_const c.radius).prodMk contDiffAt_snd)

theorem f_smoothAt
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hp : p ∈ A.referenceInput.radialDomain.carrier) (hs : SmallDebt F c.debt p.2) :
    ContDiffAt ℝ ∞ c.f p := by
  by_cases hX : 0 < p.1
  · have hroot : ContDiffAt ℝ ∞ (fun q : Point => Real.sqrt (2 * q.1)) p :=
      (contDiffAt_const.mul contDiffAt_fst).sqrt (show 2 * p.1 ≠ 0 by positivity)
    apply ((c.E_smoothAt hsep hX hp.2 hs).div hroot
      (Real.sqrt_pos.2 (show 0 < 2 * p.1 by positivity)).ne').congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with q hq
    apply (eq_div_iff (Real.sqrt_pos.2 (show 0 < 2 * q.1 by positivity)).ne').mpr
    simpa only [mul_comm] using (c.E_eq_sqrt_mul_f hsep hq).symm
  · have hpXi : p.1 < Xi := (le_of_not_gt hX).trans_lt Xi_pos
    apply (c.seedF_smooth.contDiffAt (A.referenceInput.radialDomain.isOpen.mem_nhds hp)).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hpXi)] with q hq
    exact c.f_before_Xi hq.le

theorem preparedE_positive {p : Point} (hX : 0 < p.1)
    (hη : p.2 ∈ ReferencePath.parameterInterval) :
    0 < preparedE F A.normalization c.shapeTime c.initialShape c.seedF p := by
  have hRX := mul_pos c.radius_pos hX
  have hf : 0 < c.shapedF (c.radius * p.1, p.2) :=
    mul_pos (c.seedF_positive hη hRX.le) (Real.exp_pos _)
  exact mul_pos (Real.sqrt_pos.2 (mul_pos (by norm_num : (0 : ℝ) < 2) hRX)) hf

theorem normalizedE_positive
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt p.2) : 0 < c.normalizedE p := by
  by_cases hpatch : p.1 ∈ Ioo resetPatch.left resetPatch.right
  · have hb := baseE_ideal F A.normalization_pos c.shapeTime_pos hsep c.initialShape c.seedF p.2
      (c.held_on_patch hsep hη) p.1 hpatch
    have hpos := resetSolver.positive _ (smallDebt_mem hs) p.1 hX
    change 0 < baseE F A.normalization c.shapeTime c.initialShape c.seedF p +
      idealAmplitude F p.2 * FiveProfileMoments.e resetPatch (resetCoefficients F c.debt p.2) p.1
    rw [show baseE F A.normalization c.shapeTime c.initialShape c.seedF p =
        idealAmplitude F p.2 * p.1 ^ (1 / 10 : ℝ) from hb]
    rw [← mul_add]
    exact mul_pos (idealAmplitude_pos F p.2) hpos
  · have he := (corrected_unchanged F (baseU F A.normalization c.seedU)
      (baseE F A.normalization c.shapeTime c.initialShape c.seedF) c.debt p hpatch).2
    change 0 < correctedE F (baseE F A.normalization c.shapeTime c.initialShape c.seedF) c.debt p
    rw [he]
    by_cases hcut : p.1 ≤ matchFraction
    · rw [baseE, splice_inner _ _ hcut]
      exact c.preparedE_positive hX hη
    · rw [baseE, splice_outer _ _ (lt_of_not_ge hcut)]
      exact F.E_pos p

theorem E_positive
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt p.2) : 0 < c.E p :=
  c.normalizedE_positive hsep (div_pos hX c.radius_pos) hη hs

end Controls

theorem outgoing_H_integrable_prefix (F : Profile) (eta r : ℝ) :
    IntegrableOn (fun x => F.H (x, eta)) (Ioc 0 r) := by
  have hsmall : ∀ r : ℝ, r ≤ 1 → IntegrableOn (fun x => F.H (x, eta)) (Ioc 0 r) := by
    intro s hs
    have hg : Continuous (fun x : ℝ => Real.sqrt (2 * x) *
        (idealAmplitude F eta * x ^ (1 / 10 : ℝ))) :=
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.mul (Real.continuous_rpow_const (by norm_num)))
    apply IntegrableOn.congr_fun hg.integrableOn_Ioc _ measurableSet_Ioc
    intro x hx
    simp only [Profile.H, F.E_ideal eta hx.1 (hx.2.trans hs), idealAmplitude]
  by_cases hr : r ≤ 1
  · exact hsmall r hr
  · have hc : ContinuousOn (fun x => F.H (x, eta)) (Icc (1 : ℝ) r) :=
      F.H_contDiffOn.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨lt_of_lt_of_le (by norm_num) hx.1, mem_univ _⟩)
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one (le_of_not_ge hr)]
    exact (hsmall 1 le_rfl).union (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)

theorem outgoing_density_integrable (F : Profile) (eta r : ℝ) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => F.U (t, eta)) (fun t => F.E (t, eta)) x i)
      (Ioc 0 r) := by
  fin_cases i
  · exact (F.mass_integrable eta).mono_set (fun _ hx => hx.1)
  · exact outgoing_H_integrable_prefix F eta r
  · apply IntegrableOn.congr_fun ((F.angular_integrable eta).mono_set (fun _ hx => hx.1))
      _ measurableSet_Ioc
    intro x _
    change (Real.sqrt (2 * x) * F.E (x, eta)) * F.U (x, eta) =
      F.U (x, eta) * Real.sqrt (2 * x) * F.E (x, eta)
    ring
  · exact (F.energy_integrable eta).mono_set (fun _ hx => hx.1)
  · apply IntegrableOn.congr_fun
      (((F.canonicalKernel_integrable eta).mono_set (fun _ hx => hx.1)).div_const 2) _ measurableSet_Ioc
    intro x _
    change (F.E (x, eta) ^ 2 / x) / 2 = F.E (x, eta) ^ 2 / (2 * x)
    rw [div_div, mul_comm x 2]

noncomputable def dilateField (R : ℝ) (f : Field) (p : Point) : ℝ := f (p.1 / R, p.2)
noncomputable def dilationFactor (R : ℝ) : Debt := ![R, R * Real.sqrt R, R * Real.sqrt R, R, 1]

theorem density_dilate (R : ℝ) (hR : 0 < R) (U E : Field) (eta : ℝ) {x : ℝ} (hx : 0 < x)
    (i : Fin 5) :
    R * density (fun t => dilateField R U (t, eta)) (fun t => dilateField R E (t, eta)) (R * x) i =
      dilationFactor R i * density (fun t => U (t, eta)) (fun t => E (t, eta)) x i := by
  have hd : R * x / R = x := mul_div_cancel_left₀ x hR.ne'
  have hs : Real.sqrt (2 * (R * x)) = Real.sqrt R * Real.sqrt (2 * x) := by
    rw [show 2 * (R * x) = R * (2 * x) by ring, Real.sqrt_mul hR.le]
  fin_cases i <;> simp [density, dilateField, dilationFactor, hd, hs]
  all_goals try field_simp [hR.ne', hx.ne']

theorem moments_dilate (R : ℝ) (hR : 0 < R) (U E : Field) (X eta : ℝ) :
    moments (dilateField R U) (dilateField R E) X eta =
      fun i => dilationFactor R i * moments U E (X / R) eta i := by
  ext i
  unfold moments
  rw [← OutgoingDilation.image_mul_Ioc R X hR]
  have hd : ∀ x ∈ Ioc (0 : ℝ) (X / R),
      HasDerivWithinAt (fun x : ℝ => R * x) R (Ioc 0 (X / R)) x := by
    intro x _
    simpa only [mul_one, id_eq] using ((hasDerivAt_id x).const_mul R).hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hd
    (fun _ _ _ _ h => mul_left_cancel₀ hR.ne' h), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simpa only [abs_of_pos hR, smul_eq_mul] using density_dilate R hR U E eta hx.1 i

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem normalized_moments
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {r eta : ℝ} (hr : matchFraction ≤ r) (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) :
    moments c.normalizedU c.normalizedE r eta = moments F.U F.E r eta :=
  joined_moments F A.normalization_pos c.shapeTime_pos hr hsep c.initialShape c.seedF c.seedU eta hs
    (c.held_on_patch hsep hη)
    (c.base_density_integrable hsep (matchFraction_pos.le.trans hr) hη)
    (outgoing_density_integrable F eta r)

theorem physical_moments
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {X eta : ℝ} (hX : c.radius * matchFraction ≤ X) (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) :
    moments c.U c.E X eta = moments (OutgoingDilation.U F c.radius) (OutgoingDilation.E F c.radius) X eta := by
  change moments (dilateField c.radius c.normalizedU) (dilateField c.radius c.normalizedE) X eta =
    moments (dilateField c.radius F.U) (dilateField c.radius F.E) X eta
  rw [moments_dilate c.radius c.radius_pos, moments_dilate c.radius c.radius_pos,
    c.normalized_moments hsep ((le_div_iff₀ c.radius_pos).mpr (by simpa only [mul_comm] using hX)) hη hs]

theorem physical_mass_after
    (hsep : ShapeTransition.separation c.shapeTime A.normalization F.data.core.P ≤ Real.exp (-8))
    {X eta : ℝ} (hX : c.radius * matchFraction ≤ X) (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) :
    (∫ x in Ioc 0 X, c.U (x, eta)) = OutgoingDilation.M F c.radius eta X :=
  congrArg (fun q : Debt => q 0) (c.physical_moments hsep hX hη hs)

end Controls

theorem prefix_integral_split {f : ℝ → ℝ} {r b : ℝ} (hr : 0 ≤ r) (hrb : r ≤ b)
    (hf : IntegrableOn f (Ioc 0 b)) :
    (∫ x in Ioc 0 b, f x) = (∫ x in Ioc 0 r, f x) + ∫ x in Ioc r b, f x := by
  rw [← Ioc_union_Ioc_eq_Ioc hr hrb]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hf.mono_set (Ioc_subset_Ioc_right hrb))
    (hf.mono_set (fun _ hx => ⟨hr.trans_lt hx.1, hx.2⟩))

theorem moment_difference_split (U E V G : Field) (eta : ℝ) {r b : ℝ} (hr : 0 ≤ r)
    (hrb : r ≤ b)
    (hU : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x i) (Ioc 0 b))
    (hV : ∀ i : Fin 5, IntegrableOn
      (fun x => density (fun t => V (t, eta)) (fun t => G (t, eta)) x i) (Ioc 0 b)) :
    moments U E b eta - moments V G b eta = moments U E r eta - moments V G r eta +
      fun i => ∫ x in Ioc r b, density (fun t => U (t, eta)) (fun t => E (t, eta)) x i -
        density (fun t => V (t, eta)) (fun t => G (t, eta)) x i := by
  ext i
  dsimp only [moments, Pi.sub_apply, Pi.add_apply]
  rw [prefix_integral_split hr hrb (hU i), prefix_integral_split hr hrb (hV i),
    integral_sub ((hU i).mono_set (fun _ hx => ⟨hr.trans_lt hx.1, hx.2⟩))
      ((hV i).mono_set (fun _ hx => ⟨hr.trans_lt hx.1, hx.2⟩))]
  ring

noncomputable def manuscriptIdealRows (F : Profile) (r eta : ℝ) : Debt :=
  ![ShapeTransition.idealM idealU r eta, ShapeTransition.idealI (idealAmplitude F) r eta,
    ShapeTransition.idealJ idealU (idealAmplitude F) r eta,
    ShapeTransition.idealS idealU (idealAmplitude F) r eta,
    ShapeTransition.idealP (idealAmplitude F) r eta]

theorem ideal_rows_moments (F : Profile) {r : ℝ} (hr : 0 ≤ r) (eta : ℝ) :
    moments (fun p => idealU p.2) (idealE F) r eta = manuscriptIdealRows F r eta := by
  rcases ShapeTransition.ideal_rows_are_integrals hr idealU (idealAmplitude F) eta with
    ⟨hM, hI, hJ, hS, hP⟩
  ext i
  fin_cases i
  · simp only [moments, density, manuscriptIdealRows, idealU,
      intervalIntegral.integral_of_le hr] at hM ⊢
    exact hM.symm
  · simp only [moments, density, manuscriptIdealRows, idealE,
      intervalIntegral.integral_of_le hr] at hI ⊢
    exact hI.symm
  · simp only [moments, density, manuscriptIdealRows, idealE,
      intervalIntegral.integral_of_le hr] at hJ ⊢
    exact hJ.symm
  · simp only [moments, density, manuscriptIdealRows, idealE,
      intervalIntegral.integral_of_le hr] at hS ⊢
    exact hS.symm
  · simp only [moments, density, manuscriptIdealRows, idealE,
      intervalIntegral.integral_of_le hr] at hP ⊢
    exact hP.symm

theorem outgoing_manuscript_rows (F : Profile) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (eta : ℝ) :
    moments F.U F.E r eta = manuscriptIdealRows F r eta := by
  rw [← ideal_rows_moments F hr eta]
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [density, F.U_ideal eta hx.1 (hx.2.trans hr1),
    F.E_ideal eta hx.1 (hx.2.trans hr1), idealU, idealE, idealAmplitude]

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def separation : ℝ := ShapeTransition.separation c.shapeTime A.normalization F.data.core.P
noncomputable def rawU : Field := ShapeTransition.scaledFamily c.radius c.seedU
noncomputable def rawF : Field := ShapeTransition.scaledFamily c.radius c.shapedF
noncomputable def rawRows (r eta : ℝ) : Debt :=
  ![ShapeTransition.rowM c.rawU r eta, ShapeTransition.rowI c.radius c.rawF r eta,
    ShapeTransition.rowJ c.radius c.rawU c.rawF r eta,
    ShapeTransition.rowS c.radius c.rawU c.rawF r eta, ShapeTransition.rowP c.radius c.rawF r eta]
noncomputable def restoreRows (r b eta : ℝ) : Debt :=
  ![ShapeTransition.restoreDebtM c.initialAxial r b eta, 0,
    ShapeTransition.restoreDebtJ c.initialAxial (idealAmplitude F) r b eta,
    ShapeTransition.restoreDebtS c.initialAxial r b eta, 0]
noncomputable def manuscriptDebt (eta : ℝ) : Debt :=
  ![ShapeTransition.resetDebtM c.rawU c.initialAxial c.separation matchFraction eta,
    ShapeTransition.resetDebtI c.radius c.rawF (idealAmplitude F) c.separation eta,
    ShapeTransition.resetDebtJ c.radius c.rawU c.rawF c.initialAxial (idealAmplitude F)
      c.separation matchFraction eta,
    ShapeTransition.resetDebtS c.radius c.rawU c.rawF c.initialAxial (idealAmplitude F)
      c.separation matchFraction eta,
    ShapeTransition.resetDebtP c.radius c.rawF (idealAmplitude F) c.separation eta]

theorem separation_pos : 0 < c.separation :=
  ShapeTransition.separation_pos c.shapeTime A.normalization_pos F.data.core.P_pos

theorem rawE_eq (p : Point) :
    ShapeTransition.scaledE c.radius c.rawF p =
      preparedE F A.normalization c.shapeTime c.initialShape c.seedF p := by
  simp only [ShapeTransition.scaledE, rawF, ShapeTransition.scaledFamily, preparedE,
    radius, shapedF, mul_assoc]

theorem rawRows_eq_moments {r : ℝ} (hr : 0 ≤ r) (eta : ℝ) :
    c.rawRows r eta = moments c.rawU (ShapeTransition.scaledE c.radius c.rawF) r eta := by
  ext i
  fin_cases i <;> simp only [rawRows, ShapeTransition.rowM, ShapeTransition.rowI,
    ShapeTransition.rowJ, ShapeTransition.rowS, ShapeTransition.rowP,
    moments, density, intervalIntegral.integral_of_le hr] <;> rfl

theorem base_prefix_before_restore {r : ℝ} (hr : 0 ≤ r) (hr8 : r ≤ Real.exp (-8)) (eta : ℝ) :
    moments (baseU F A.normalization c.seedU)
      (baseE F A.normalization c.shapeTime c.initialShape c.seedF) r eta = c.rawRows r eta := by
  rw [c.rawRows_eq_moments hr]
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxc : x ≤ matchFraction := hx.2.trans (hr8.trans
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5)))
  have hU : baseU F A.normalization c.seedU (x, eta) = c.rawU (x, eta) := by
    rw [baseU, splice_inner _ _ hxc]
    exact restoredU_before c.radius_pos
      (mul_le_mul_of_nonneg_left (hx.2.trans hr8) c.radius_pos.le) c.seedU eta
  have hE : baseE F A.normalization c.shapeTime c.initialShape c.seedF (x, eta) =
      ShapeTransition.scaledE c.radius c.rawF (x, eta) :=
    (splice_inner _ _ hxc).trans (c.rawE_eq (x, eta)).symm
  simp only [density, hU, hE]

theorem base_restore_segment {x eta : ℝ} (hx : c.separation ≤ x) (hxb : x ≤ matchFraction)
    (hη : eta ∈ ReferencePath.parameterInterval) :
    baseU F A.normalization c.seedU (x, eta) = ShapeTransition.restore c.initialAxial (Real.log x, eta) ∧
    baseE F A.normalization c.shapeTime c.initialShape c.seedF (x, eta) = idealE F (x, eta) := by
  have hx0 := c.separation_pos.trans_le hx
  have hXi := c.shape_clock_after_Xi hx
  constructor
  · rw [baseU, splice_inner _ _ hxb]
    change restoredU c.radius c.seedU (c.radius * x, eta) = _
    rw [restoredU_scaled c.radius_pos hx0, c.seedU_held hXi hη]
    rfl
  · rw [baseE, splice_inner _ _ hxb]
    exact preparedE_ideal F A.normalization_pos c.shapeTime_pos hx c.initialShape c.seedF eta
      (c.seedF_held hXi hη)

theorem base_restore_difference {x eta : ℝ} (hx : c.separation ≤ x) (hxb : x ≤ matchFraction)
    (hη : eta ∈ ReferencePath.parameterInterval) :
    density (fun t => baseU F A.normalization c.seedU (t, eta))
      (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x -
        density (fun t => F.U (t, eta)) (fun t => F.E (t, eta)) x =
      ![ShapeTransition.restoreDefect c.initialAxial (x, eta), 0,
        ShapeTransition.restoreDensityJ c.initialAxial (idealAmplitude F) (x, eta),
        ShapeTransition.restoreDensityS c.initialAxial (x, eta), 0] := by
  rcases c.base_restore_segment hx hxb hη with ⟨hU, hE⟩
  have hx0 := c.separation_pos.trans_le hx
  have hx1 := hxb.trans matchFraction_lt_one.le
  ext i
  fin_cases i <;> simp [density, hU, hE, F.U_ideal eta hx0 hx1, F.E_ideal eta hx0 hx1,
    idealE, idealAmplitude, ShapeTransition.restoreDefect, ShapeTransition.restoreDensityJ,
    ShapeTransition.restoreDensityS] <;> ring

theorem restoreRows_eq_integral {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval)
    (hsep : c.separation ≤ Real.exp (-8)) :
    c.restoreRows c.separation matchFraction eta = fun i => ∫ x in Ioc c.separation matchFraction,
      density (fun t => baseU F A.normalization c.seedU (t, eta))
        (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x i -
          density (fun t => F.U (t, eta)) (fun t => F.E (t, eta)) x i := by
  have hrb : c.separation ≤ matchFraction := hsep.trans
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5))
  have hpoint : (fun i => ∫ x in Ioc c.separation matchFraction,
      density (fun t => baseU F A.normalization c.seedU (t, eta))
        (fun t => baseE F A.normalization c.shapeTime c.initialShape c.seedF (t, eta)) x i -
          density (fun t => F.U (t, eta)) (fun t => F.E (t, eta)) x i) =
      fun i => ∫ x in Ioc c.separation matchFraction,
        ![ShapeTransition.restoreDefect c.initialAxial (x, eta), 0,
          ShapeTransition.restoreDensityJ c.initialAxial (idealAmplitude F) (x, eta),
          ShapeTransition.restoreDensityS c.initialAxial (x, eta), 0] i := by
    ext i
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact congrArg (fun q : Debt => q i) (c.base_restore_difference hx.1.le hx.2 hη)
  rw [hpoint]
  ext i
  fin_cases i <;> simp [restoreRows, ShapeTransition.restoreDebtM, ShapeTransition.restoreDebtJ,
    ShapeTransition.restoreDebtS, intervalIntegral.integral_of_le hrb]

theorem debt_eq_negative_manuscriptDebt
    (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) :
    c.debt eta = -c.manuscriptDebt eta := by
  have hrb : c.separation ≤ matchFraction := hsep.trans
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5))
  have hd := moment_difference_split (baseU F A.normalization c.seedU)
    (baseE F A.normalization c.shapeTime c.initialShape c.seedF) F.U F.E eta
    c.separation_pos.le hrb (c.base_density_integrable hsep matchFraction_pos.le hη)
    (outgoing_density_integrable F eta matchFraction)
  rw [c.base_prefix_before_restore c.separation_pos.le hsep,
    outgoing_manuscript_rows F c.separation_pos.le (hrb.trans matchFraction_lt_one.le),
    ← c.restoreRows_eq_integral hη hsep] at hd
  have hdebt : c.debt eta = -(c.rawRows c.separation eta - manuscriptIdealRows F c.separation eta +
      c.restoreRows c.separation matchFraction eta) := by
    change _ - _ = _
    rw [← hd]
    abel
  rw [hdebt]
  congr 1
  ext i
  fin_cases i <;> simp [manuscriptDebt, rawRows, manuscriptIdealRows, restoreRows,
    ShapeTransition.resetDebtM, ShapeTransition.resetDebtI, ShapeTransition.resetDebtJ,
    ShapeTransition.resetDebtS, ShapeTransition.resetDebtP] <;> rfl

end Controls

/-! ## The actual smooth profiles and their canonical pressure -/

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem normalizedDebt_smooth :
    ContDiffOn ℝ ∞ (normalizedDebt F c.debt) ReferencePath.parameterInterval :=
  FiveProfileMoments.normalizedDebt_contDiffOn (idealAmplitude_smooth F).contDiffOn
    idealU_smooth.contDiffOn c.debt_smooth (fun e _ => (idealAmplitude_pos F e).ne')

/-- Smallness is a transparent test on the already constructed debt. Its
strict sublevel set is open, so successful repair gives ordinary smoothness. -/
noncomputable def admissibleDomain : ProfileHistories.RadialDomain where
  carrier := {p | p ∈ A.referenceInput.radialDomain.carrier ∧ SmallDebt F c.debt p.2}
  isOpen := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hn : ContinuousAt (fun q : Point => ‖normalizedDebt F c.debt q.2‖) p :=
      ((c.normalizedDebt_smooth.contDiffAt
        (ReferencePath.parameterInterval_open.mem_nhds hp.1.2)).continuousAt.norm).comp continuousAt_snd
    filter_upwards [A.referenceInput.radialDomain.isOpen.mem_nhds hp.1,
      hn.eventually (Iio_mem_nhds hp.2)] with q hq hqn
    exact ⟨hq, hqn⟩
  scale_mem := by
    intro p hp t ht
    exact ⟨A.referenceInput.radialDomain.scale_mem p hp.1 t ht, hp.2⟩

theorem admissible_nonnegative {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ ReferencePath.parameterInterval) (hs : SmallDebt F c.debt p.2) :
    p ∈ c.admissibleDomain.carrier :=
  ⟨⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le hX), hη⟩, hs⟩

noncomputable def profiles
    (hsep : c.separation ≤ Real.exp (-8)) : ProfileHistories.Profiles c.admissibleDomain where
  f := c.f
  U := c.U
  f_smooth := fun _ hp => (c.f_smoothAt hsep hp.1 hp.2).contDiffWithinAt
  U_smooth := fun _ hp => (c.U_smoothAt hsep hp.1 hp.2).contDiffWithinAt
  pressure0 := F.axisDatum
  pressure0_smooth := fun _ _ => F.axisDatum_contDiff.contDiffAt

theorem profiles_E (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hX : 0 < p.1) :
    (c.profiles hsep).E p = c.E p := (c.E_eq_sqrt_mul_f hsep hX).symm

theorem physical_density_eq (hsep : c.separation ≤ Real.exp (-8))
    {x : ℝ} (hx : 0 < x) (eta : ℝ) :
    density (fun t => c.U (t, eta)) (fun t => c.E (t, eta)) x =
      regularDensity (c.profiles hsep) (x, eta) := by
  have h := regularDensity_eq (c.profiles hsep) hx eta
  simp only [density, c.profiles_E hsep (p := (x, eta)) hx] at h ⊢
  exact h

theorem physical_density_integrable (hsep : c.separation ≤ Real.exp (-8))
    {r eta : ℝ} (hr : 0 ≤ r) (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => c.U (t, eta)) (fun t => c.E (t, eta)) x i) (Ioc 0 r) := by
  apply IntegrableOn.congr_fun (regularDensity_integrable (c.profiles hsep)
    (c.admissible_nonnegative hr hη hs) i) _ measurableSet_Ioc
  exact fun x hx => congrArg (fun q : Debt => q i) (c.physical_density_eq hsep hx.1 eta).symm

theorem profiles_pressure (hsep : c.separation ≤ Real.exp (-8))
    {p : Point} (hX : 0 ≤ p.1) : (c.profiles hsep).pressure p = c.Pi p := by
  change F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.f q ^ 2) p =
    F.axisDatum p.2 + moments c.U c.E p.1 p.2 4
  congr 1
  rw [ProfileHistories.primitive, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  exact (congrArg (fun q : Debt => q 4) (c.physical_density_eq hsep hx.1 p.2)).symm

end Controls

theorem global_integral_replace {f g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IntegrableOn f (Ioc 0 a)) (hg : IntegrableOn g (Ioi 0))
    (head : (∫ x in Ioc 0 a, f x) = ∫ x in Ioc 0 a, g x)
    (tail : ∀ x, a < x → f x = g x) :
    IntegrableOn f (Ioi 0) ∧ (∫ x in Ioi 0, f x) = ∫ x in Ioi 0, g x := by
  have hft : IntegrableOn f (Ioi a) := by
    apply IntegrableOn.congr_fun (hg.mono_set (fun _ hx => ha.trans_lt hx)) _ measurableSet_Ioi
    exact fun x hx => (tail x hx).symm
  have hfa : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha]
    exact hf.union hft
  have he := MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := fun x => f x - g x) (μ := volume) measurableSet_Ioi
    (show Ioc (0 : ℝ) a ⊆ Ioi 0 from fun _ hx => hx.1) (by
      intro x hx
      have hax : a < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩)
      change f x - g x = 0
      rw [tail x hax, sub_self])
  rw [integral_sub hfa hg, integral_sub hf (hg.mono_set (fun _ hx => hx.1)), head, sub_self,
    sub_eq_zero] at he
  exact ⟨hfa, he⟩

theorem canonical_past_identity {k : ℝ → ℝ} (hk : IntegrableOn k (Ioi 0))
    {X : ℝ} (hX : 0 ≤ X) :
    -(∫ x in Ioi 0, k x) + (∫ x in Ioc 0 X, k x) = -(∫ x in Ioi X, k x) := by
  have hs := setIntegral_union (s := Ioc (0 : ℝ) X) (t := Ioi X)
    (f := k) (disjoint_left.mpr (fun _ hx ht => (not_lt.mpr hx.2) ht)) measurableSet_Ioi
    (hk.mono_set (fun _ hx => hx.1)) (hk.mono_set (fun _ hx => hX.trans_lt hx))
  rw [Ioc_union_Ioi_eq_Ioi hX] at hs
  rw [hs]
  ring

noncomputable def halfKernel (E : Field) (eta x : ℝ) : ℝ := E (x, eta) ^ 2 / (2 * x)

theorem halfKernel_eq (E : Field) (eta x : ℝ) :
    halfKernel E eta x = (E (x, eta) ^ 2 / x) / 2 := by
  unfold halfKernel
  rw [div_div, mul_comm x 2]

theorem outgoing_halfKernel_integrable (F : Profile) (R eta : ℝ) (hR : 0 < R) :
    IntegrableOn (halfKernel (OutgoingDilation.E F R) eta) (Ioi 0) := by
  have he : halfKernel (OutgoingDilation.E F R) eta =
      fun x => OutgoingDilation.canonicalKernel F R eta x / 2 :=
    funext (halfKernel_eq (OutgoingDilation.E F R) eta)
  rw [he]
  exact (OutgoingDilation.canonicalKernel_integrable F R eta hR).div_const 2

theorem outgoing_axis_halfKernel (F : Profile) (R eta : ℝ) (hR : 0 < R) :
    F.axisDatum eta = -(∫ x in Ioi 0, halfKernel (OutgoingDilation.E F R) eta x) := by
  have ha := congrFun (OutgoingDilation.axisDatum_unchanged F R hR) eta
  simp only [OutgoingDilation.axisDatum, OutgoingDilation.canonicalKernel] at ha
  simp_rw [halfKernel_eq]
  rw [integral_div]
  linarith

theorem outgoing_pressure_halfKernel (F : Profile) (R eta : ℝ) (hR : 0 < R)
    {X : ℝ} (hX : 0 < X) :
    OutgoingDilation.Pi F R (X, eta) = -(∫ x in Ioi X, halfKernel (OutgoingDilation.E F R) eta x) := by
  rw [OutgoingDilation.Pi_canonical F R eta X hR hX]
  simp_rw [halfKernel_eq]
  rw [integral_div]
  ring

theorem outgoing_pressure_prefix (F : Profile) (R eta : ℝ) (hR : 0 < R)
    {X : ℝ} (hX : 0 < X) :
    F.axisDatum eta + moments (OutgoingDilation.U F R) (OutgoingDilation.E F R) X eta 4 =
      OutgoingDilation.Pi F R (X, eta) := by
  rw [outgoing_axis_halfKernel F R eta hR, outgoing_pressure_halfKernel F R eta hR hX]
  exact canonical_past_identity (outgoing_halfKernel_integrable F R eta hR) hX.le

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem pressure_after_match (hsep : c.separation ≤ Real.exp (-8))
    {X eta : ℝ} (hX : c.radius * matchFraction ≤ X)
    (hη : eta ∈ ReferencePath.parameterInterval) (hs : SmallDebt F c.debt eta) :
    c.Pi (X, eta) = OutgoingDilation.Pi F c.radius (X, eta) := by
  change F.axisDatum eta + moments c.U c.E X eta 4 = _
  rw [c.physical_moments hsep hX hη hs]
  exact outgoing_pressure_prefix F c.radius eta c.radius_pos
    ((mul_pos c.radius_pos matchFraction_pos).trans_le hX)

theorem kernel_integral (hsep : c.separation ≤ Real.exp (-8))
    {eta : ℝ} (hη : eta ∈ ReferencePath.parameterInterval) (hs : SmallDebt F c.debt eta) :
    IntegrableOn (halfKernel c.E eta) (Ioi 0) ∧
      (∫ x in Ioi 0, halfKernel c.E eta x) =
        ∫ x in Ioi 0, halfKernel (OutgoingDilation.E F c.radius) eta x := by
  apply global_integral_replace (mul_pos c.radius_pos matchFraction_pos).le
    (c.physical_density_integrable hsep (mul_pos c.radius_pos matchFraction_pos).le hη hs 4)
    (outgoing_halfKernel_integrable F c.radius eta c.radius_pos)
  · exact congrArg (fun q : Debt => q 4) (c.physical_moments hsep le_rfl hη hs)
  · intro x hx
    change c.E (x, eta) ^ 2 / (2 * x) = OutgoingDilation.E F c.radius (x, eta) ^ 2 / (2 * x)
    rw [(c.physical_after_match (p := (x, eta)) hx).2]

theorem pressure_canonical (hsep : c.separation ≤ Real.exp (-8))
    {X eta : ℝ} (hX : 0 < X) (hη : eta ∈ ReferencePath.parameterInterval)
    (hs : SmallDebt F c.debt eta) :
    c.Pi (X, eta) = -(1 / 2 : ℝ) * ∫ x in Ioi X, c.E (x, eta) ^ 2 / x := by
  have hk := c.kernel_integral hsep hη hs
  have ha : F.axisDatum eta = -(∫ x in Ioi 0, halfKernel c.E eta x) := by
    rw [hk.2]
    exact outgoing_axis_halfKernel F c.radius eta c.radius_pos
  change F.axisDatum eta + (∫ x in Ioc 0 X, halfKernel c.E eta x) = _
  rw [ha, canonical_past_identity hk.1 hX.le]
  simp_rw [halfKernel_eq]
  rw [integral_div]
  ring

end Controls

/-! ## Keeping the actual continuation witness -/

noncomputable def AxisStage.ofEntrance {F : Profile} {j : ℝ}
    (hj : NaturalAxisData.SmallParameters F.data.h j) (prep : AxisPreparation F j)
    (Λ C : ℝ) (hΛ : prep.scaleBound ≤ Λ)
    (hC : NaturalEntrance.entranceNormalization prep.inputs Λ prep.delta ≤ C)
    (E : NaturalEntrance.EntranceProfile prep.inputs Λ C) : AxisStage F :=
  ⟨j, hj, prep, Λ, C, hΛ, hC, E⟩

noncomputable def Controls.ofContinuation {F : Profile} (A : AxisStage F) {N : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (T : ℝ) (hT : 0 < T) : Controls A where
  referenceWidth := w.parameters.refTime
  referenceWidth_pos := w.parameters.refTime_pos
  referenceWidth_small := w.parameters.refTime_bound
  activationTime := w.parameters.actTime
  activationTime_pos := w.parameters.actTime_pos
  activationTime_le := w.parameters.actTime_le
  kappa := w.parameters.kappa
  kappa_pos := w.parameters.kappa_pos
  kappa_le_one := w.parameters.kappa_lt_one.le
  axialWidth := w.parameters.widthU
  axialWidth_pos := w.parameters.widthU_pos
  angularWidth := w.parameters.widthA
  angularWidth_pos := w.parameters.widthA_pos
  before_big := w.parameters.before_big
  finish := w.parameters.finish_before.le
  shapeTime := T
  shapeTime_pos := hT

theorem Controls.ofContinuation_seed {F : Profile} (A : AxisStage F) {N : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (T : ℝ) (hT : 0 < T) :
    (Controls.ofContinuation A w T hT).seedF = w.parameters.profiles.f ∧
      (Controls.ofContinuation A w T hT).seedU = w.parameters.profiles.U := ⟨rfl, rfl⟩

theorem Controls.ofContinuation_log_control {F : Profile} (A : AxisStage F) {N : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (T : ℝ) (hT : 0 < T) :
    let c := Controls.ofContinuation A w T hT
    c.reference.SmallLogControl (Icc (-1 : ℝ) 1) N eps
      c.activationTime c.kappa c.axialWidth c.angularWidth := w.logarithmic_control

/-! ## Joining the heat completion of the same outgoing profile -/

theorem physical_band_in_parameterInterval {eta : ℝ} (hη : eta ∈ Icc (-1 : ℝ) 1) :
    eta ∈ ReferencePath.parameterInterval := by
  dsimp [ReferencePath.parameterInterval, NaturalAxisCoefficients.window]
  constructor <;> linarith [hη.1, hη.2]

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def heatJoin : ℝ := c.radius * matchFraction
noncomputable def heatBlend (X : ℝ) : ℝ := ShapeTransition.radialSwitch c.heatJoin 1 X
noncomputable def heatedE (coef : ℝ → HeatedOutgoing.Coeff) (p : Point) : ℝ :=
  c.E p + c.heatBlend p.1 * (HeatedOutgoing.E F c.radius coef p - c.E p)
noncomputable def heatedH (coef : ℝ → HeatedOutgoing.Coeff) (p : Point) : ℝ :=
  Real.sqrt (2 * p.1) * c.heatedE coef p
noncomputable def heatedPi (coef : ℝ → HeatedOutgoing.Coeff) (p : Point) : ℝ :=
  F.axisDatum p.2 + moments c.U (c.heatedE coef) p.1 p.2 4
noncomputable def heatedf (coef : ℝ → HeatedOutgoing.Coeff) (p : Point) : ℝ :=
  if p.1 ≤ Xi then c.f p else c.heatedE coef p / Real.sqrt (2 * p.1)

theorem heatJoin_pos : 0 < c.heatJoin := mul_pos c.radius_pos matchFraction_pos
theorem heatJoin_lt_radius : c.heatJoin < c.radius :=
  mul_lt_of_lt_one_right c.radius_pos matchFraction_lt_one
theorem heatBlend_smooth : ContDiff ℝ ∞ c.heatBlend :=
  ShapeTransition.radialSwitch_contDiff c.heatJoin_pos (by norm_num)

theorem heatBlend_before {X : ℝ} (hX : X ≤ c.heatJoin) : c.heatBlend X = 0 :=
  ShapeTransition.radialSwitch_zero c.heatJoin_pos (by norm_num) hX

theorem heatBlend_after {X : ℝ} (hX : c.radius ≤ X) : c.heatBlend X = 1 := by
  have hXp := c.radius_pos.trans_le hX
  have hratio : c.radius / c.heatJoin = 1 / Real.exp (-5) := by
    unfold heatJoin matchFraction
    rw [div_mul_eq_div_div, div_self c.radius_pos.ne']
  have hlog : (5 : ℝ) ≤ Real.log (X / c.heatJoin) := by
    have h := Real.log_le_log (div_pos c.radius_pos c.heatJoin_pos)
      ((div_le_div_iff_of_pos_right c.heatJoin_pos).mpr hX)
    rw [hratio, Real.log_div one_ne_zero (Real.exp_pos _).ne', Real.log_one, Real.log_exp] at h
    norm_num at h
    exact h
  unfold heatBlend
  rw [ShapeTransition.radialSwitch_eq c.heatJoin_pos (by norm_num : (0 : ℝ) < 1) hXp, div_one]
  exact OutgoingSchedule.sigma_one (by linarith)

theorem heatedE_before (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 ≤ c.heatJoin) :
    c.heatedE coef p = c.E p := by simp only [heatedE, c.heatBlend_before hp, zero_mul, add_zero]

theorem heatedE_after (coef : ℝ → HeatedOutgoing.Coeff) {p : Point}
    (hp : c.heatJoin < p.1) : c.heatedE coef p = HeatedOutgoing.E F c.radius coef p := by
  by_cases hR : p.1 ≤ c.radius
  · have hX := c.heatJoin_pos.trans hp
    have hE := (c.physical_after_match hp).2
    have hH := HeatedOutgoing.E_before_patch F c.radius coef p.2 p.1 c.radius_pos hX
      (hR.trans (HeatedOutgoing.entrance_before_patch F c.radius c.radius_pos).le)
    change c.E p + c.heatBlend p.1 * (HeatedOutgoing.E F c.radius coef p - c.E p) = _
    rw [show HeatedOutgoing.E F c.radius coef p = OutgoingDilation.E F c.radius p from hH, hE]
    ring
  · simp only [heatedE, c.heatBlend_after (le_of_not_ge hR), one_mul]
    ring

theorem heated_fields_after (coef : ℝ → HeatedOutgoing.Coeff) {p : Point}
    (hp : c.heatJoin < p.1) :
    c.U p = HeatedOutgoing.U F c.radius p ∧ c.heatedE coef p = HeatedOutgoing.E F c.radius coef p :=
  ⟨(c.physical_after_match hp).1, c.heatedE_after coef hp⟩

theorem heated_natural_prefix (coef : ℝ → HeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) (hscale : 1 ≤ A.scale)
    {p : Point} (hp : p.1 ≤ 4 / A.scale) :
    c.heatedf coef p = A.natural.profile.family.f p ∧ c.U p = A.natural.profile.family.U p := by
  have hb : (4 : ℝ) / A.scale ≤ Xi := by
    apply (div_le_iff₀ A.scale_pos).mpr
    have := mul_le_mul_of_nonneg_left hscale Xi_pos.le
    norm_num [Xi] at *
    linarith
  rw [heatedf, ite_eq_left (hp.trans hb)]
  exact c.natural_prefix hsep hscale hp

theorem heatedE_smooth {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) :
    ContDiffOn ℝ ∞ (c.heatedE w.coefficients)
      {p | p ∈ HeatedOutgoing.domain ∧ SmallDebt F c.debt p.2} := by
  have hc : ContDiffOn ℝ ∞ c.E {p | p ∈ HeatedOutgoing.domain ∧ SmallDebt F c.debt p.2} := by
    intro p hp
    exact (c.E_smoothAt hsep hp.1.1 (physical_band_in_parameterInterval hp.1.2) hp.2).contDiffWithinAt
  exact hc.add (((c.heatBlend_smooth.comp contDiff_fst).contDiffOn).mul
    ((HeatedOutgoing.E_contDiffOn F c.radius c.radius_pos w.smooth).mono (fun _ hp => hp.1) |>.sub hc))

end Controls

theorem density_dilate_integrable (R : ℝ) (hR : 0 < R) (U E : Field) (r eta : ℝ)
    (i : Fin 5) (hf : IntegrableOn
      (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x i) (Ioc 0 (r / R))) :
    IntegrableOn (fun x => density (fun t => dilateField R U (t, eta))
      (fun t => dilateField R E (t, eta)) x i) (Ioc 0 r) := by
  have hi := (OutgoingDilation.integrable_dilate_Ioc _ R r hR hf).const_mul (dilationFactor R i / R)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioc
  intro x hx
  have he := density_dilate R hR U E eta (div_pos hx.1 hR) i
  rw [mul_div_cancel₀ _ hR.ne'] at he
  calc
    _ = (dilationFactor R i * density (fun t => U (t, eta)) (fun t => E (t, eta)) (x / R) i) / R := by ring
    _ = _ := (div_eq_iff hR.ne').mpr (by simpa only [mul_comm] using he.symm)

theorem heated_outgoing_density_integrable {F : Profile} {R B : ℝ}
    (w : HeatedOutgoing.CompensationWitness F R B) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (r : ℝ) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F R (t, eta))
      (fun t => HeatedOutgoing.E F R w.coefficients (t, eta)) x i) (Ioc 0 r) := by
  fin_cases i
  · exact (w.mass_integrable eta).mono_set (fun _ hx => hx.1)
  · have hb := density_dilate_integrable R w.radius_pos F.U F.E r eta 1
      (outgoing_density_integrable F eta (r / R) 1)
    apply IntegrableOn.congr_fun
      (hb.add ((w.changeRow_integrable eta 2 hη).mono_set (fun _ hx => hx.1))) _ measurableSet_Ioc
    intro x _
    change Real.sqrt (2 * x) * OutgoingDilation.E F R (x, eta) +
        Real.sqrt (2 * x) * (HeatedOutgoing.E F R w.coefficients (x, eta) - OutgoingDilation.E F R (x, eta)) =
      Real.sqrt (2 * x) * HeatedOutgoing.E F R w.coefficients (x, eta)
    ring
  · apply IntegrableOn.congr_fun ((w.angular_integrable eta).mono_set (fun _ hx => hx.1))
      _ measurableSet_Ioc
    intro x _
    change (Real.sqrt (2 * x) * HeatedOutgoing.E F R w.coefficients (x, eta)) *
        HeatedOutgoing.U F R (x, eta) =
      HeatedOutgoing.U F R (x, eta) * Real.sqrt (2 * x) * HeatedOutgoing.E F R w.coefficients (x, eta)
    ring
  · exact (w.energy_integrable eta hη).mono_set (fun _ hx => hx.1)
  · apply IntegrableOn.congr_fun
      (((w.canonicalKernel_integrable eta hη).mono_set (fun _ hx => hx.1)).div_const 2)
      _ measurableSet_Ioc
    intro x _
    change (HeatedOutgoing.E F R w.coefficients (x, eta) ^ 2 / x) / 2 =
      HeatedOutgoing.E F R w.coefficients (x, eta) ^ 2 / (2 * x)
    rw [div_div, mul_comm x 2]

theorem prefix_integrable_replace {f g : ℝ → ℝ} {a r : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hf : IntegrableOn f (Ioc 0 a)) (hg : IntegrableOn g (Ioc 0 r))
    (tail : ∀ x, a < x → f x = g x) : IntegrableOn f (Ioc 0 r) := by
  have ht : IntegrableOn f (Ioc a r) := by
    apply IntegrableOn.congr_fun (hg.mono_set (fun _ hx => ⟨ha.trans_lt hx.1, hx.2⟩))
      _ measurableSet_Ioc
    exact fun x hx => (tail x hx.1).symm
  rw [← Ioc_union_Ioc_eq_Ioc ha har]
  exact hf.union ht

theorem global_integral_replace_renormalized {f g b : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : IntegrableOn f (Ioc 0 a)) (hg : IntegrableOn g (Ioc 0 a))
    (hgb : IntegrableOn (fun x => g x - b x) (Ioi 0))
    (head : (∫ x in Ioc 0 a, f x) = ∫ x in Ioc 0 a, g x)
    (tail : ∀ x, a < x → f x = g x) :
    IntegrableOn (fun x => f x - b x) (Ioi 0) ∧
      (∫ x in Ioi 0, f x - b x) = ∫ x in Ioi 0, g x - b x := by
  have hb : IntegrableOn b (Ioc 0 a) := by
    apply IntegrableOn.congr_fun (hg.sub (hgb.mono_set (fun _ hx => hx.1))) _ measurableSet_Ioc
    intro x _
    change g x - (g x - b x) = b x
    ring
  apply global_integral_replace ha (hf.sub hb) hgb
  · change (∫ x in Ioc 0 a, f x - b x) = ∫ x in Ioc 0 a, g x - b x
    rw [integral_sub hf hb, integral_sub hg hb, head]
  · intro x hx
    change f x - b x = g x - b x
    rw [tail x hx]

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem heated_moments_at_match {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) :
    moments c.U (c.heatedE w.coefficients) c.heatJoin eta =
      moments (HeatedOutgoing.U F c.radius) (HeatedOutgoing.E F c.radius w.coefficients) c.heatJoin eta := by
  have he : moments c.U (c.heatedE w.coefficients) c.heatJoin eta = moments c.U c.E c.heatJoin eta := by
    ext i
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [density, c.heatedE_before w.coefficients (p := (x, eta)) hx.2]
  rw [he, c.physical_moments hsep (X := c.heatJoin) le_rfl (physical_band_in_parameterInterval hη) hs]
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hE := HeatedOutgoing.E_before_patch F c.radius w.coefficients eta x c.radius_pos hx.1
    (hx.2.trans (c.heatJoin_lt_radius.le.trans (HeatedOutgoing.entrance_before_patch F c.radius c.radius_pos).le))
  simp only [density, hE, HeatedOutgoing.U]

theorem heated_density_integrable_at_match {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => c.U (t, eta))
      (fun t => c.heatedE w.coefficients (t, eta)) x i) (Ioc 0 c.heatJoin) := by
  apply IntegrableOn.congr_fun
    (c.physical_density_integrable hsep c.heatJoin_pos.le (physical_band_in_parameterInterval hη) hs i)
    _ measurableSet_Ioc
  intro x hx
  simp only [density, c.heatedE_before w.coefficients (p := (x, eta)) hx.2]

theorem heated_density_integrable {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta r : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta)
    (hr : c.heatJoin ≤ r) (i : Fin 5) :
    IntegrableOn (fun x => density (fun t => c.U (t, eta))
      (fun t => c.heatedE w.coefficients (t, eta)) x i) (Ioc 0 r) := by
  apply prefix_integrable_replace c.heatJoin_pos.le hr
    (c.heated_density_integrable_at_match w hsep hη hs i)
    (heated_outgoing_density_integrable w hη r i)
  intro x hx
  rcases c.heated_fields_after w.coefficients (p := (x, eta)) hx with ⟨hU, hE⟩
  simp only [density, hU, hE]

theorem heated_moments {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta r : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) (hr : c.heatJoin ≤ r) :
    moments c.U (c.heatedE w.coefficients) r eta =
      moments (HeatedOutgoing.U F c.radius) (HeatedOutgoing.E F c.radius w.coefficients) r eta :=
  moments_propagate hr (c.heated_density_integrable w hsep hη hs hr)
    (heated_outgoing_density_integrable w hη r) (c.heated_moments_at_match w hsep hη hs)
    (fun _ hx => c.heated_fields_after w.coefficients hx)

theorem heated_row_transfer {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta)
    (i : Fin 5) (background : ℝ → ℝ)
    (hg : IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x i - background x) (Ioi 0)) :
    IntegrableOn (fun x => density (fun t => c.U (t, eta))
      (fun t => c.heatedE w.coefficients (t, eta)) x i - background x) (Ioi 0) ∧
    (∫ x in Ioi 0, density (fun t => c.U (t, eta))
      (fun t => c.heatedE w.coefficients (t, eta)) x i - background x) =
    ∫ x in Ioi 0, density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x i - background x := by
  apply global_integral_replace_renormalized c.heatJoin_pos.le
    (c.heated_density_integrable_at_match w hsep hη hs i)
    (heated_outgoing_density_integrable w hη c.heatJoin i) hg
    (congrArg (fun q : Debt => q i) (c.heated_moments_at_match w hsep hη hs))
  intro x hx
  rcases c.heated_fields_after w.coefficients (p := (x, eta)) hx with ⟨hU, hE⟩
  simp only [density, hU, hE]

end Controls

theorem heated_outgoing_halfKernel_integrable {F : Profile} {R B : ℝ}
    (w : HeatedOutgoing.CompensationWitness F R B) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    IntegrableOn (halfKernel (HeatedOutgoing.E F R w.coefficients) eta) (Ioi 0) := by
  have he : halfKernel (HeatedOutgoing.E F R w.coefficients) eta =
      fun x => HeatedOutgoing.canonicalKernel F R w.coefficients eta x / 2 :=
    funext (halfKernel_eq (HeatedOutgoing.E F R w.coefficients) eta)
  rw [he]
  exact (w.canonicalKernel_integrable eta hη).div_const 2

theorem heated_outgoing_axis_halfKernel {F : Profile} {R B : ℝ}
    (w : HeatedOutgoing.CompensationWitness F R B) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    F.axisDatum eta = -(∫ x in Ioi 0, halfKernel (HeatedOutgoing.E F R w.coefficients) eta x) := by
  have he : halfKernel (HeatedOutgoing.E F R w.coefficients) eta =
      fun x => HeatedOutgoing.canonicalKernel F R w.coefficients eta x / 2 :=
    funext (halfKernel_eq (HeatedOutgoing.E F R w.coefficients) eta)
  rw [he, integral_div]
  have ha := w.axisDatum_eq eta hη
  dsimp only [HeatedOutgoing.axisDatum] at ha
  linarith

theorem heated_outgoing_pressure_prefix {F : Profile} {R B : ℝ}
    (w : HeatedOutgoing.CompensationWitness F R B) {eta X : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hX : 0 ≤ X) :
    F.axisDatum eta + moments (HeatedOutgoing.U F R) (HeatedOutgoing.E F R w.coefficients) X eta 4 =
      HeatedOutgoing.Pi F R w.coefficients (X, eta) := by
  rw [heated_outgoing_axis_halfKernel w hη]
  change -(∫ x in Ioi 0, halfKernel _ eta x) + (∫ x in Ioc 0 X, halfKernel _ eta x) = _
  rw [canonical_past_identity (heated_outgoing_halfKernel_integrable w hη) hX]
  simp_rw [halfKernel_eq]
  rw [integral_div]
  unfold HeatedOutgoing.Pi HeatedOutgoing.canonicalKernel
  ring

/-- The five global conditions are stated for the literal final fields. -/
structure FiveMomentCertificate (U E : Field) (powerH : ℝ → ℝ) (P0 eta : ℝ) : Prop where
  mass_integrable : IntegrableOn (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x 0) (Ioi 0)
  transport_integrable : IntegrableOn (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x 2) (Ioi 0)
  energy_integrable : IntegrableOn (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x 3) (Ioi 0)
  angular_integrable : IntegrableOn (fun x => density (fun t => U (t, eta)) (fun t => E (t, eta)) x 1 - powerH x) (Ioi 0)
  pressure_integrable : IntegrableOn (halfKernel E eta) (Ioi 0)
  mass_zero : (∫ x in Ioi 0, U (x, eta)) = 0
  transport_zero : (∫ x in Ioi 0, U (x, eta) * Real.sqrt (2 * x) * E (x, eta)) = 0
  energy_zero : (∫ x in Ioi 0, U (x, eta) ^ 2 - E (x, eta) ^ 2 / 2) = 0
  angular_zero : (∫ x in Ioi 0, Real.sqrt (2 * x) * E (x, eta) - powerH x) = 0
  pressure_datum : P0 = -(∫ x in Ioi 0, halfKernel E eta x)

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

theorem heated_pressure_data {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) :
    IntegrableOn (halfKernel (c.heatedE w.coefficients) eta) (Ioi 0) ∧
      F.axisDatum eta = -(∫ x in Ioi 0, halfKernel (c.heatedE w.coefficients) eta x) := by
  have hg : IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x 4 - 0) (Ioi 0) := by
    simp only [sub_zero]
    exact heated_outgoing_halfKernel_integrable w hη
  have h := c.heated_row_transfer w hsep hη hs 4 (fun _ => 0) hg
  simp only [sub_zero] at h
  exact ⟨h.1, (heated_outgoing_axis_halfKernel w hη).trans (congrArg Neg.neg h.2).symm⟩

theorem heated_five_moments {B D : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hF : OutgoingProfile.Specification F D) (hsep : c.separation ≤ Real.exp (-8)) {eta : ℝ}
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) :
    FiveMomentCertificate c.U (c.heatedE w.coefficients) (OutgoingDilation.powerH F c.radius)
      (F.axisDatum eta) eta := by
  have h0g : IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x 0 - 0) (Ioi 0) := by
    simp only [sub_zero]
    exact w.mass_integrable eta
  have h2g : IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x 2 - 0) (Ioi 0) := by
    convert! w.angular_integrable eta using 1
    funext x
    change HeatedOutgoing.U F c.radius (x, eta) * Real.sqrt (2 * x) *
        HeatedOutgoing.E F c.radius w.coefficients (x, eta) - 0 = _
    unfold HeatedOutgoing.H
    ring
  have h3g : IntegrableOn (fun x => density (fun t => HeatedOutgoing.U F c.radius (t, eta))
      (fun t => HeatedOutgoing.E F c.radius w.coefficients (t, eta)) x 3 - 0) (Ioi 0) := by
    simp only [sub_zero]
    exact w.energy_integrable eta hη
  have h0 := c.heated_row_transfer w hsep hη hs 0 (fun _ => 0) h0g
  have h2 := c.heated_row_transfer w hsep hη hs 2 (fun _ => 0) h2g
  have h3 := c.heated_row_transfer w hsep hη hs 3 (fun _ => 0) h3g
  have h1 := c.heated_row_transfer w hsep hη hs 1 (OutgoingDilation.powerH F c.radius)
    (w.renormalized_integrable eta hη)
  have h4 := c.heated_pressure_data w hsep hη hs
  simp only [sub_zero] at h0 h2 h3
  refine ⟨h0.1, h2.1, h3.1, h1.1, h4.1, h0.2.trans (w.mass_zero eta), ?_,
    h3.2.trans (w.energy_zero hF eta hη), h1.2.trans (w.renormalized_zero eta hη), h4.2⟩
  refine h2.2.trans ?_
  convert! w.angular_zero eta using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change HeatedOutgoing.U F c.radius (x, eta) * Real.sqrt (2 * x) *
      HeatedOutgoing.E F c.radius w.coefficients (x, eta) = _
  unfold HeatedOutgoing.H
  ring

theorem heated_pressure_canonical {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {X eta : ℝ} (hX : 0 ≤ X)
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) :
    c.heatedPi w.coefficients (X, eta) =
      -(1 / 2 : ℝ) * ∫ x in Ioi X, c.heatedE w.coefficients (x, eta) ^ 2 / x := by
  have hp := c.heated_pressure_data w hsep hη hs
  change F.axisDatum eta + (∫ x in Ioc 0 X, halfKernel (c.heatedE w.coefficients) eta x) = _
  rw [hp.2, canonical_past_identity hp.1 hX]
  simp_rw [halfKernel_eq]
  rw [integral_div]
  ring

theorem heated_pressure_after {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {X eta : ℝ} (hX : c.heatJoin ≤ X)
    (hη : eta ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt eta) :
    c.heatedPi w.coefficients (X, eta) = HeatedOutgoing.Pi F c.radius w.coefficients (X, eta) := by
  change F.axisDatum eta + moments c.U (c.heatedE w.coefficients) X eta 4 = _
  rw [c.heated_moments w hsep hη hs hX]
  exact heated_outgoing_pressure_prefix w hη (c.heatJoin_pos.le.trans hX)

theorem heated_pressure_before (coef : ℝ → HeatedOutgoing.Coeff) {p : Point}
    (hp : p.1 ≤ c.heatJoin) : c.heatedPi coef p = c.Pi p := by
  change F.axisDatum p.2 + moments c.U (c.heatedE coef) p.1 p.2 4 =
    F.axisDatum p.2 + moments c.U c.E p.1 p.2 4
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simp only [density, c.heatedE_before coef (p := (x, p.2)) (hx.2.trans hp)]

end Controls

theorem Controls.ofContinuation_reference {F : Profile} (A : AxisStage F) {N : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (T : ℝ) (hT : 0 < T) :
    (Controls.ofContinuation A w T hT).reference = w.parameters.reference := rfl

theorem Controls.ofContinuation_endpoints {F : Profile} (A : AxisStage F) {N : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (T : ℝ) (hT : 0 < T) :
    (Controls.ofContinuation A w T hT).initialAxial = w.parameters.endpointAxial ∧
      (Controls.ofContinuation A w T hT).initialShape = w.parameters.endpointLogarithm := ⟨rfl, rfl⟩

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def seedProfiles : ProfileHistories.Profiles A.referenceInput.radialDomain :=
  TransitionRamp.physicalProfiles A.natural.profile.family A.scale_pos A.small
    c.referenceWidth_pos c.referenceWidth_small F.axisDatum_contDiff (κ := c.kappa)
    c.activationTime_pos c.before_big c.axialWidth_pos c.angularWidth_pos

theorem Xi_lt_heatJoin (hsep : c.separation ≤ Real.exp (-8)) : Xi < c.heatJoin :=
  (c.shape_clock_after_Xi hsep).trans_lt
    (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by norm_num : (-8 : ℝ) < -5)) c.radius_pos)

theorem activation_collar_le_Xi : (4 / A.scale) * Real.exp c.referenceWidth ≤ Xi := by
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr c.before_big) c.reference.radius0_pos.le
  have hr : c.reference.radius0 * Real.exp c.reference.bigTime = 100 := by
    rw [TransitionRamp.StockReference.bigTime,
      Real.exp_log (div_pos (by norm_num) c.reference.radius0_pos),
      mul_div_cancel₀ _ c.reference.radius0_pos.ne']
  change c.reference.radius0 * Real.exp c.referenceWidth ≤ Xi
  exact (h.trans_eq hr).trans (by norm_num [Xi])

theorem heated_seed_fields (coef : ℝ → HeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hp : p.1 ≤ Xi) :
    c.heatedf coef p = c.seedProfiles.f p ∧ c.U p = c.seedProfiles.U p ∧
      c.heatedE coef p = c.seedProfiles.E p := by
  have hc := c.physical_before_Xi hsep hp
  refine ⟨?_, hc.1, ?_⟩
  · rw [heatedf, ite_eq_left hp, c.f_before_Xi hp]
    rfl
  · rw [c.heatedE_before coef (hp.trans (c.Xi_lt_heatJoin hsep).le), hc.2]
    rfl

theorem heated_seed_moments (coef : ℝ → HeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {X : ℝ} (hX : X ≤ Xi) (eta : ℝ) :
    moments c.U (c.heatedE coef) X eta = moments c.seedProfiles.U c.seedProfiles.E X eta := by
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  rcases c.heated_seed_fields coef hsep (p := (x, eta)) (hx.2.trans hX) with ⟨_, hU, hE⟩
  simp only [density, hU, hE]

theorem heated_seed_pressure (coef : ℝ → HeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hX : 0 ≤ p.1) (hp : p.1 ≤ Xi) :
    c.heatedPi coef p = c.seedProfiles.pressure p := by
  change F.axisDatum p.2 + moments c.U (c.heatedE coef) p.1 p.2 4 = _
  rw [c.heated_seed_moments coef hsep hp]
  change F.axisDatum p.2 + moments c.seedProfiles.U c.seedProfiles.E p.1 p.2 4 =
    F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.seedProfiles.f q ^ 2) p
  congr 1
  rw [ProfileHistories.primitive, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  exact congrArg (fun q : Debt => q 4) (regularDensity_eq c.seedProfiles hx.1 p.2)

theorem Pi_smoothAt (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hX : 0 < p.1) (hη : p.2 ∈ ReferencePath.parameterInterval) (hs : SmallDebt F c.debt p.2) :
    ContDiffAt ℝ ∞ c.Pi p := by
  have hp := c.admissible_nonnegative hX.le hη hs
  apply ((c.profiles hsep).pressure_smooth.contDiffAt (c.admissibleDomain.isOpen.mem_nhds hp)).congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with q hq
  exact (c.profiles_pressure hsep hq.le).symm

theorem heated_pressure_blend {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hX : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt p.2) :
    c.heatedPi w.coefficients p = c.Pi p + c.heatBlend p.1 *
      (HeatedOutgoing.Pi F c.radius w.coefficients p - c.Pi p) := by
  by_cases ha : p.1 ≤ c.heatJoin
  · rw [c.heated_pressure_before w.coefficients ha, c.heatBlend_before ha]
    ring
  · have hhot := c.heated_pressure_after w hsep (X := p.1) (eta := p.2) (le_of_not_ge ha) hη hs
    change c.heatedPi w.coefficients (p.1, p.2) = _
    rw [hhot]
    by_cases hR : p.1 ≤ c.radius
    · have hi := c.pressure_after_match hsep (X := p.1) (eta := p.2) (le_of_not_ge ha)
        (physical_band_in_parameterInterval hη) hs
      have ho := w.Pi_before_patch p.2 p.1 hη hX
        (hR.trans (HeatedOutgoing.entrance_before_patch F c.radius c.radius_pos).le)
      change HeatedOutgoing.Pi F c.radius w.coefficients p = _
      rw [show c.Pi p = OutgoingDilation.Pi F c.radius p from hi,
        show HeatedOutgoing.Pi F c.radius w.coefficients p = OutgoingDilation.Pi F c.radius p from ho]
      ring
    · rw [c.heatBlend_after (le_of_not_ge hR)]
      ring

theorem heatedPi_smooth {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) :
    ContDiffOn ℝ ∞ (c.heatedPi w.coefficients)
      {p | p ∈ HeatedOutgoing.domain ∧ SmallDebt F c.debt p.2} := by
  have hc : ContDiffOn ℝ ∞ c.Pi {p | p ∈ HeatedOutgoing.domain ∧ SmallDebt F c.debt p.2} := by
    intro p hp
    exact (c.Pi_smoothAt hsep hp.1.1 (physical_band_in_parameterInterval hp.1.2) hp.2).contDiffWithinAt
  apply (hc.add (((c.heatBlend_smooth.comp contDiff_fst).contDiffOn).mul
    ((w.Pi_contDiffOn.mono (fun _ hp => hp.1)).sub hc))).congr
  intro p hp
  exact c.heated_pressure_blend w hsep hp.1.1 hp.1.2 hp.2

theorem heatedE_positive {B : ℝ} (w : HeatedOutgoing.CompensationWitness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hX : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) (hs : SmallDebt F c.debt p.2) :
    0 < c.heatedE w.coefficients p := by
  by_cases hp : p.1 ≤ c.heatJoin
  · rw [c.heatedE_before w.coefficients hp]
    exact c.E_positive hsep hX (physical_band_in_parameterInterval hη) hs
  · rw [c.heatedE_after w.coefficients (lt_of_not_ge hp)]
    exact w.positive p.2 p.1 hη hX

end Controls

/-! ## One ordinary smooth extension of the same physical nominal profile -/

namespace Controls

variable {F : Profile} {A : AxisStage F} (c : Controls A)

noncomputable def extendedE (coef : ℝ → ExtendedHeatedOutgoing.Coeff) (p : Point) : ℝ :=
  c.E p + c.heatBlend p.1 * (ExtendedHeatedOutgoing.E F c.radius coef p - c.E p)
noncomputable def extendedf (coef : ℝ → ExtendedHeatedOutgoing.Coeff) (p : Point) : ℝ :=
  if p.1 ≤ Xi then c.f p else c.extendedE coef p / Real.sqrt (2 * p.1)
noncomputable def extendedPi (coef : ℝ → ExtendedHeatedOutgoing.Coeff) (p : Point) : ℝ :=
  F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.extendedf coef q ^ 2) p

noncomputable def extendedDomain : ProfileHistories.RadialDomain where
  carrier := {p | p ∈ c.admissibleDomain.carrier ∧ p.2 ∈ ExtendedHeatedOutgoing.parameterDomain}
  isOpen := c.admissibleDomain.isOpen.inter (ExtendedHeatedOutgoing.parameterDomain_open.preimage continuous_snd)
  scale_mem := by
    intro p hp t ht
    exact ⟨c.admissibleDomain.scale_mem p hp.1 t ht, hp.2⟩

theorem extendedDomain_nonnegative {p : Point} (hX : 0 ≤ p.1)
    (hη : p.2 ∈ ReferencePath.parameterInterval) (he : p.2 ∈ ExtendedHeatedOutgoing.parameterDomain)
    (hs : SmallDebt F c.debt p.2) : p ∈ c.extendedDomain.carrier :=
  ⟨c.admissible_nonnegative hX hη hs, he⟩

theorem extendedE_before (coef : ℝ → ExtendedHeatedOutgoing.Coeff) {p : Point}
    (hp : p.1 ≤ c.heatJoin) : c.extendedE coef p = c.E p := by
  simp only [extendedE, c.heatBlend_before hp, zero_mul, add_zero]

theorem extendedE_eq_sqrt_f (coef : ℝ → ExtendedHeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hX : 0 < p.1) :
    c.extendedE coef p = Real.sqrt (2 * p.1) * c.extendedf coef p := by
  by_cases hp : p.1 ≤ Xi
  · rw [extendedf, ite_eq_left hp, c.extendedE_before coef (hp.trans (c.Xi_lt_heatJoin hsep).le)]
    exact c.E_eq_sqrt_mul_f hsep hX
  · rw [extendedf, ite_eq_right hp, mul_div_cancel₀ _
      (Real.sqrt_pos.2 (show 0 < 2 * p.1 by positivity)).ne']

theorem extendedE_smoothAt {B : ℝ} (w : ExtendedHeatedOutgoing.Witness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hX : 0 < p.1)
    (hp : p ∈ c.extendedDomain.carrier) : ContDiffAt ℝ ∞ (c.extendedE w.coefficients) p := by
  have hc := c.E_smoothAt hsep hX hp.1.1.2 hp.1.2
  exact hc.add (((c.heatBlend_smooth.comp contDiff_fst).contDiffAt).mul
    ((w.fields_contDiffAt ⟨hX, hp.2⟩).1.sub hc))

theorem extendedf_smoothAt {B : ℝ} (w : ExtendedHeatedOutgoing.Witness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hp : p ∈ c.extendedDomain.carrier) :
    ContDiffAt ℝ ∞ (c.extendedf w.coefficients) p := by
  by_cases hX : 0 < p.1
  · have hroot : ContDiffAt ℝ ∞ (fun q : Point => Real.sqrt (2 * q.1)) p :=
      (contDiffAt_const.mul contDiffAt_fst).sqrt (show 2 * p.1 ≠ 0 by positivity)
    apply ((c.extendedE_smoothAt w hsep hX hp).div hroot
      (Real.sqrt_pos.2 (show 0 < 2 * p.1 by positivity)).ne').congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX)] with q hq
    apply (eq_div_iff (Real.sqrt_pos.2 (show 0 < 2 * q.1 by positivity)).ne').mpr
    simpa only [mul_comm] using (c.extendedE_eq_sqrt_f w.coefficients hsep hq).symm
  · have hb : p.1 < Xi := (le_of_not_gt hX).trans_lt Xi_pos
    apply (c.f_smoothAt hsep hp.1.1 hp.1.2).congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hb)] with q hq
    exact ite_eq_left hq.le

noncomputable def extendedProfiles {B : ℝ} (w : ExtendedHeatedOutgoing.Witness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) : ProfileHistories.Profiles c.extendedDomain where
  f := c.extendedf w.coefficients
  U := c.U
  f_smooth := fun _ hp => (c.extendedf_smoothAt w hsep hp).contDiffWithinAt
  U_smooth := fun _ hp => (c.U_smoothAt hsep hp.1.1 hp.1.2).contDiffWithinAt
  pressure0 := F.axisDatum
  pressure0_smooth := fun _ _ => F.axisDatum_contDiff.contDiffAt

theorem extended_fields_smoothAt {B : ℝ} (w : ExtendedHeatedOutgoing.Witness F c.radius B)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hp : p ∈ c.extendedDomain.carrier) :
    ContDiffAt ℝ ∞ (c.extendedf w.coefficients) p ∧ ContDiffAt ℝ ∞ c.U p ∧
      ContDiffAt ℝ ∞ (c.extendedPi w.coefficients) p :=
  ⟨c.extendedf_smoothAt w hsep hp, c.U_smoothAt hsep hp.1.1 hp.1.2,
    (c.extendedProfiles w hsep).pressure_smooth.contDiffAt (c.extendedDomain.isOpen.mem_nhds hp)⟩

theorem extendedE_physical (coef : ℝ → ExtendedHeatedOutgoing.Coeff) {p : Point}
    (hX : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    c.extendedE coef p = c.heatedE coef p := by
  unfold extendedE heatedE
  rw [show ExtendedHeatedOutgoing.E F c.radius coef p = HeatedOutgoing.E F c.radius coef p from
    ExtendedHeatedOutgoing.E_eq_physical F c.radius coef p.2 p.1 hη hX]

theorem extendedf_physical (coef : ℝ → ExtendedHeatedOutgoing.Coeff) {p : Point}
    (hX : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    c.extendedf coef p = c.heatedf coef p := by
  unfold extendedf heatedf
  split_ifs
  · rfl
  · rw [c.extendedE_physical coef hX hη]

theorem extendedPi_physical (coef : ℝ → ExtendedHeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hX : 0 ≤ p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    c.extendedPi coef p = c.heatedPi coef p := by
  unfold extendedPi heatedPi
  congr 1
  rw [ProfileHistories.primitive, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change c.extendedf coef (x, p.2) ^ 2 = c.heatedE coef (x, p.2) ^ 2 / (2 * x)
  rw [← c.extendedE_physical coef (p := (x, p.2)) hx.1 hη,
    c.extendedE_eq_sqrt_f coef hsep hx.1, mul_pow,
    Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.1.le),
    mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hx.1.ne')]

theorem extended_seed_fields (coef : ℝ → ExtendedHeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hp : p.1 ≤ Xi) :
    c.extendedf coef p = c.seedProfiles.f p ∧ c.U p = c.seedProfiles.U p := by
  rw [extendedf, ite_eq_left hp, c.f_before_Xi hp]
  exact ⟨rfl, (c.physical_before_Xi hsep hp).1⟩

theorem extended_seed_pressure (coef : ℝ → ExtendedHeatedOutgoing.Coeff)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point} (hX : 0 ≤ p.1) (hp : p.1 ≤ Xi) :
    c.extendedPi coef p = c.seedProfiles.pressure p := by
  unfold extendedPi
  change F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.extendedf coef q ^ 2) p =
    F.axisDatum p.2 + ProfileHistories.primitive (fun q => c.seedProfiles.f q ^ 2) p
  congr 1
  rw [ProfileHistories.primitive, ProfileHistories.primitive,
    intervalIntegral.integral_of_le hX, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change c.extendedf coef (x, p.2) ^ 2 = c.seedProfiles.f (x, p.2) ^ 2
  rw [(c.extended_seed_fields coef hsep (p := (x, p.2)) (hx.2.trans hp)).1]

end Controls

theorem FiveMomentCertificate.congr {U E V G : Field} {powerH : ℝ → ℝ} {P0 eta : ℝ}
    (h : FiveMomentCertificate U E powerH P0 eta)
    (he : ∀ x : ℝ, 0 < x → V (x, eta) = U (x, eta) ∧ G (x, eta) = E (x, eta)) :
    FiveMomentCertificate V G powerH P0 eta := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply IntegrableOn.congr_fun h.mass_integrable _ measurableSet_Ioi
    intro x hx
    simp only [density, (he x hx).1, (he x hx).2]
  · apply IntegrableOn.congr_fun h.transport_integrable _ measurableSet_Ioi
    intro x hx
    simp only [density, (he x hx).1, (he x hx).2]
  · apply IntegrableOn.congr_fun h.energy_integrable _ measurableSet_Ioi
    intro x hx
    simp only [density, (he x hx).1, (he x hx).2]
  · apply IntegrableOn.congr_fun h.angular_integrable _ measurableSet_Ioi
    intro x hx
    simp only [density, (he x hx).1, (he x hx).2]
  · apply IntegrableOn.congr_fun h.pressure_integrable _ measurableSet_Ioi
    intro x hx
    simp only [halfKernel, (he x hx).2]
  · calc
      (∫ x in Ioi 0, V (x, eta)) = ∫ x in Ioi 0, U (x, eta) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => (he x hx).1)
      _ = 0 := h.mass_zero
  · calc
      (∫ x in Ioi 0, V (x, eta) * Real.sqrt (2 * x) * G (x, eta)) =
          ∫ x in Ioi 0, U (x, eta) * Real.sqrt (2 * x) * E (x, eta) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [(he x hx).1, (he x hx).2]
      _ = 0 := h.transport_zero
  · calc
      (∫ x in Ioi 0, V (x, eta) ^ 2 - G (x, eta) ^ 2 / 2) =
          ∫ x in Ioi 0, U (x, eta) ^ 2 - E (x, eta) ^ 2 / 2 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [(he x hx).1, (he x hx).2]
      _ = 0 := h.energy_zero
  · calc
      (∫ x in Ioi 0, Real.sqrt (2 * x) * G (x, eta) - powerH x) =
          ∫ x in Ioi 0, Real.sqrt (2 * x) * E (x, eta) - powerH x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [(he x hx).2]
      _ = 0 := h.angular_zero
  · rw [h.pressure_datum]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [halfKernel, (he x hx).2]

/-- One common nominal profile. All functions below are computed from these
retained witnesses; the debt condition is the explicit normalized IFT test. -/
structure Witness (F : Profile) where
  axis : AxisStage F
  controls : Controls axis
  outgoingBound : ℝ
  outgoing_specification : OutgoingProfile.Specification F outgoingBound
  heatBound : ℝ
  heat : ExtendedHeatedOutgoing.Witness F controls.radius heatBound
  separated : controls.separation ≤ Real.exp (-8)
  debt_small : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F controls.debt eta

namespace Witness

variable {F : Profile} (W : Witness F)

noncomputable def f : Field := W.controls.extendedf W.heat.coefficients
noncomputable def U : Field := W.controls.U
noncomputable def E : Field := W.controls.extendedE W.heat.coefficients
noncomputable def H (p : Point) : ℝ := Real.sqrt (2 * p.1) * W.E p
noncomputable def Pi : Field := W.controls.extendedPi W.heat.coefficients
noncomputable def domain : ProfileHistories.RadialDomain := W.controls.extendedDomain
noncomputable def profiles : ProfileHistories.Profiles W.domain :=
  W.controls.extendedProfiles W.heat W.separated

theorem domain_contains {p : Point} (hX : 0 ≤ p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    p ∈ W.domain.carrier := W.controls.extendedDomain_nonnegative hX
  (physical_band_in_parameterInterval hη) (ExtendedHeatedOutgoing.physicalBand_subset hη)
    (W.debt_small p.2 hη)

/-- Compactness of the physical band gives one common open parameter interval
for all nonnegative radii, with the same fields and repair coefficients. -/
theorem exists_parameter_interval :
    ∃ a : ℝ, 1 < a ∧ a < 3 / 2 ∧ ∀ X : ℝ, 0 ≤ X →
      ∀ eta ∈ Ioo (-a) a, (X, eta) ∈ W.domain.carrier := by
  let V : Set ℝ := {eta | (0, eta) ∈ W.domain.carrier}
  have hv : IsOpen V := W.domain.isOpen.preimage (continuous_const.prodMk continuous_id)
  have hb : HeatedOutgoing.parameterDomain ⊆ V := fun _ hη => W.domain_contains le_rfl hη
  obtain ⟨a, ha, ha', hV⟩ := ExtendedHeatedOutgoing.exists_symmetric_neighborhood hv hb
  refine ⟨a, ha, ha', ?_⟩
  intro X hX eta hη
  have hp := hV hη
  exact W.controls.extendedDomain_nonnegative hX hp.1.1.2 hp.2 hp.1.2

theorem fields_smooth {p : Point} (hp : p ∈ W.domain.carrier) :
    ContDiffAt ℝ ∞ W.f p ∧ ContDiffAt ℝ ∞ W.U p ∧ ContDiffAt ℝ ∞ W.Pi p :=
  W.controls.extended_fields_smoothAt W.heat W.separated hp

theorem E_eq_sqrt_f {p : Point} (hX : 0 < p.1) : W.E p = Real.sqrt (2 * p.1) * W.f p :=
  W.controls.extendedE_eq_sqrt_f W.heat.coefficients W.separated hX

theorem E_positive {p : Point} (hX : 0 < p.1) (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    0 < W.E p := by
  change 0 < W.controls.extendedE W.heat.coefficients p
  rw [W.controls.extendedE_physical W.heat.coefficients hX hη]
  exact W.controls.heatedE_positive W.heat.physical W.separated hX hη (W.debt_small p.2 hη)

theorem five_moments {eta : ℝ} (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    FiveMomentCertificate W.U W.E (OutgoingDilation.powerH F W.controls.radius) (F.axisDatum eta) eta := by
  apply (W.controls.heated_five_moments W.heat.physical W.outgoing_specification W.separated hη
    (W.debt_small eta hη)).congr
  intro x hx
  exact ⟨rfl, W.controls.extendedE_physical W.heat.coefficients hx hη⟩

theorem pressure_canonical {X eta : ℝ} (hX : 0 ≤ X) (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    W.Pi (X, eta) = -(1 / 2 : ℝ) * ∫ x in Ioi X, W.E (x, eta) ^ 2 / x := by
  change W.controls.extendedPi W.heat.coefficients (X, eta) = _
  rw [W.controls.extendedPi_physical W.heat.coefficients W.separated hX hη]
  have hc := W.controls.heated_pressure_canonical W.heat.physical W.separated hX hη (W.debt_small eta hη)
  rw [show W.heat.physical.coefficients = W.heat.coefficients from rfl] at hc
  rw [hc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change W.controls.heatedE W.heat.coefficients (x, eta) ^ 2 / x = W.E (x, eta) ^ 2 / x
  rw [show W.E (x, eta) = W.controls.heatedE W.heat.coefficients (x, eta) from
    W.controls.extendedE_physical W.heat.coefficients (hX.trans_lt hx) hη]

theorem seed_agreement {p : Point} (hX : 0 ≤ p.1) (hp : p.1 ≤ Xi) :
    W.f p = W.controls.seedProfiles.f p ∧ W.U p = W.controls.seedProfiles.U p ∧
      W.Pi p = W.controls.seedProfiles.pressure p :=
  ⟨(W.controls.extended_seed_fields W.heat.coefficients W.separated hp).1,
    (W.controls.extended_seed_fields W.heat.coefficients W.separated hp).2,
    W.controls.extended_seed_pressure W.heat.coefficients W.separated hX hp⟩

theorem heat_agreement {p : Point} (hX : W.controls.heatJoin < p.1)
    (hη : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.U p = HeatedOutgoing.U F W.controls.radius p ∧
    W.E p = HeatedOutgoing.E F W.controls.radius W.heat.physical.coefficients p ∧
    W.Pi p = HeatedOutgoing.Pi F W.controls.radius W.heat.physical.coefficients p := by
  have hx := W.controls.heatJoin_pos.trans hX
  refine ⟨(W.controls.heated_fields_after W.heat.coefficients hX).1, ?_, ?_⟩
  · exact (W.controls.extendedE_physical W.heat.coefficients hx hη).trans
      (W.controls.heatedE_after W.heat.coefficients hX)
  · exact (W.controls.extendedPi_physical W.heat.coefficients W.separated hx.le hη).trans
      (W.controls.heated_pressure_after W.heat.physical W.separated hX.le hη (W.debt_small p.2 hη))

theorem moments_after {r eta : ℝ} (hr : W.controls.heatJoin ≤ r)
    (hη : eta ∈ HeatedOutgoing.parameterDomain) :
    moments W.U W.E r eta =
      moments (HeatedOutgoing.U F W.controls.radius)
        (HeatedOutgoing.E F W.controls.radius W.heat.physical.coefficients) r eta := by
  rw [← W.controls.heated_moments W.heat.physical W.separated hη (W.debt_small eta hη) hr]
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have he := W.controls.extendedE_physical W.heat.coefficients (p := (x, eta)) hx.1 hη
  simp only [density, E, U, he, show W.heat.physical.coefficients = W.heat.coefficients from rfl]

/-- The axial field is unchanged after the matching patch, at every parameter. -/
theorem U_outgoing {p : Point} (hp : W.controls.heatJoin < p.1) :
    W.U p = OutgoingDilation.U F W.controls.radius p :=
  (W.controls.physical_after_match hp).1

/-- The true mass history agrees on the ordinary open parameter domain. -/
theorem mass_outgoing {r eta : ℝ} (hr : W.controls.heatJoin ≤ r)
    (hp : (r, eta) ∈ W.domain.carrier) :
    (∫ x in Ioc 0 r, W.U (x, eta)) = OutgoingDilation.M F W.controls.radius eta r :=
  W.controls.physical_mass_after W.separated hr hp.1.1.2 hp.1.2

theorem after_pulse_open {r eta : ℝ} (hr : W.controls.heatJoin < r)
    (hp : (r, eta) ∈ W.domain.carrier)
    (hfar : OutgoingDilation.pulseEndRadius F W.controls.radius ≤ r) :
    W.U (r, eta) = 0 ∧ (∫ x in Ioc 0 r, W.U (x, eta)) = 0 := by
  have ho := OutgoingDilation.after_pulse F W.controls.radius eta r W.controls.radius_pos
    (W.controls.heatJoin_pos.trans hr) hfar
  exact ⟨(W.U_outgoing hr).trans ho.1, (W.mass_outgoing hr.le hp).trans ho.2.1⟩

/-- Past the matching radius the extension is the same extended heat field;
this equality has no restriction to the closed physical parameter band. -/
theorem E_extended_after_radius {p : Point} (hp : W.controls.radius ≤ p.1) :
    W.E p = ExtendedHeatedOutgoing.E F W.controls.radius W.heat.coefficients p := by
  change W.controls.E p + W.controls.heatBlend p.1 *
    (ExtendedHeatedOutgoing.E F W.controls.radius W.heat.coefficients p - W.controls.E p) = _
  rw [W.controls.heatBlend_after hp]
  ring

theorem E_outgoing_before_patch {X eta : ℝ} (hR : W.controls.radius ≤ X)
    (hp : X ≤ OutgoingDilation.patchRadius F W.controls.radius) :
    W.E (X, eta) = OutgoingDilation.E F W.controls.radius (X, eta) := by
  rw [W.E_extended_after_radius hR]
  exact ExtendedHeatedOutgoing.E_before_patch F W.controls.radius W.heat.coefficients eta X
    W.controls.radius_pos (W.controls.radius_pos.trans_le hR) hp

theorem E_outgoing_between_patch_and_switch {X eta : ℝ} (hR : W.controls.radius ≤ X)
    (hp : OutgoingDilation.patchRadius F W.controls.radius *
      OutgoingDilation.compensationPatch.right ≤ X)
    (hK : X ≤ OutgoingDilation.switchRadius F W.controls.radius) :
    W.E (X, eta) = OutgoingDilation.E F W.controls.radius (X, eta) := by
  rw [W.E_extended_after_radius hR]
  exact ExtendedHeatedOutgoing.E_between_patch_and_switch F W.controls.radius W.heat.coefficients eta X
    W.controls.radius_pos (W.controls.radius_pos.trans_le hR) hp hK

end Witness

/-- Heat completion imposes a late radius bound on the already selected
outgoing profile. Any matched continuation beyond that bound gives one
actual nominal witness, retaining its entrance and ramp parameters. -/
theorem exists_assembly_threshold {F : Profile} {D : ℝ} (hF : OutgoingProfile.Specification F D) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ (A : AxisStage F) (c : Controls A), R0 ≤ c.radius →
      c.separation ≤ Real.exp (-8) →
      (∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) → Nonempty (Witness F) := by
  obtain ⟨R0, B, hR0, _hB, hw⟩ := ExtendedHeatedOutgoing.exists_witness F
  refine ⟨R0, hR0, ?_⟩
  intro A c hr hsep hs
  obtain ⟨w⟩ := hw c.radius hr
  exact ⟨⟨A, c, D, hF, B, w, hsep, hs⟩⟩

theorem exists_assembly_threshold_preserving {F : Profile} {D : ℝ}
    (hF : OutgoingProfile.Specification F D) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ (A : AxisStage F) (c : Controls A), R0 ≤ c.radius →
      c.separation ≤ Real.exp (-8) →
      (∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) →
        ∃ W : Witness F, W.axis = A ∧ HEq W.controls c := by
  obtain ⟨R0, B, hR0, _hB, hw⟩ := ExtendedHeatedOutgoing.exists_witness F
  refine ⟨R0, hR0, ?_⟩
  intro A c hr hsep hs
  obtain ⟨w⟩ := hw c.radius hr
  exact ⟨⟨A, c, D, hF, B, w, hsep, hs⟩, rfl, HEq.rfl⟩

/-- Retain the cutoff margin from the same analytic input construction;
later ACT existence uses this margin without rechoosing the axis data. -/
theorem prepare_axis_with_cutoff (F : Profile) (hP : 2 ≤ F.data.core.P) {j : ℝ}
    (hj : NaturalAxisData.SmallParameters F.data.h j) :
    ∃ prep : AxisPreparation F j, ∀ eta ∈ Icc (-1 : ℝ) 1,
      |NaturalAxisData.Z F.data.h j F.axisDatum eta| ≤ prep.delta →
        99 / 100 < NaturalAxisData.chi F.data.h j prep.sigma eta := by
  have he := NaturalAxisCoefficients.ideal_prefix_analytic_inputs (NaturalAxisRange.ofSmall hj)
    (SchedulePressure.admissible F.data) hP
    (fun y hy => SchedulePressure.clockWeight_ideal F.data hy)
    (fun y hy => SchedulePressure.shapeExponent_ideal F.data hy)
  have hd : F.axisDatum = PressureDatum.pressure
      (SchedulePressure.clockWeight F.data) (SchedulePressure.shapeExponent F.data) :=
    F.axisDatum_eq.trans (SchedulePressure.axisPressure_eq F.data)
  rw [← hd] at he
  obtain ⟨delta, sigma, hdelta, hsigma, hcut, ⟨inputs⟩⟩ := he
  obtain ⟨bound, hbound, entrances⟩ := NaturalEntrance.exists_entranceProfile inputs hj hsigma
    F.axisDatum_contDiff hdelta hcut
  exact ⟨⟨delta, sigma, hdelta, hsigma, inputs, bound, hbound, entrances⟩, hcut⟩

end NavierStokes.NominalProfile
