import NavierStokes.WholeDomainHeatBounds
import NavierStokes.ActualBaseVelocityBounds
import NavierStokes.ActualBasePressureBounds

/-! # Whole-domain bounds for the uncut, actual slow base -/

noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.WholeDomainBaseBounds

open ProblemStatement PhysicalWaveSum WholeDomainStageBounds

def unitDomain (h : ℝ) : Set SpaceTime :=
  {w | w ∈ preterminal ∧ physicalQ h w ≤ 1}

theorem unitDomain_past (h : ℝ) : unitDomain h ⊆ SpacetimeEndpoint.openPast 1 :=
  fun _ hw => ⟨hw.1,mem_univ _⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem rate_of_jet_limit_of_small_scale {h L : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hL : 0 ≤ L) {f : SpaceTime → V} {m : ℕ} {w : SpaceTime}
    {J : SpaceTime [×m]→L[ℝ] V}
    (hJ : Tendsto (iteratedFDeriv ℝ m f) (𝓝[unitDomain h] w) (𝓝 J)) :
    DiagonalResidual.JetRate (𝓝[unitDomain h] w) (physicalQ h) f m (-L) := by
  refine ⟨‖J‖+1,by positivity,?_⟩
  have hb := hJ.norm.eventually (gt_mem_nhds (lt_add_one ‖J‖))
  filter_upwards [hb,self_mem_nhdsWithin] with y hy hyS
  have hq := physicalQ_pos hh hh1 hyS.1
  have hp : 1 ≤ physicalQ h y ^ (-L) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hq hyS.2 (neg_nonpos.mpr hL)
  exact hy.le.trans (le_mul_of_one_le_right (by positivity) hp)

theorem local_rate {h L : ℝ} (hh : 0 < h) (hh1 : h < 1/2) (hL : 0 ≤ L)
    {f : SpaceTime → V} (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (ha : JointResidualLimits.AwayExtensions f) (m : ℕ)
    (ho : DiagonalResidual.JetRate ActualBaseVelocityBounds.endpoint (physicalQ h) f m (-L))
    (w : SpaceTime) :
    DiagonalResidual.JetRate (𝓝[unitDomain h] w) (physicalQ h) f m (-L) := by
  rcases w with ⟨t,x⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · have hs := hf.contDiffAt ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds
      (show (t,x) ∈ SpacetimeEndpoint.openPast 1 from ⟨ht,mem_univ _⟩))
    have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ m f) (t,x) :=
      hs.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (m : ℕ∞) ≤ ⊤))
    exact rate_of_jet_limit_of_small_scale hh hh1 hL
      (hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  · subst t
    have hl : 𝓝[unitDomain h] (1,x) ≤ 𝓝[SpacetimeEndpoint.openPast 1] (1,x) :=
      nhdsWithin_mono _ (unitDomain_past h)
    by_cases hx : x = 0
    · subst x
      obtain ⟨C,hC,hb⟩ := ho
      exact ⟨C,hC,hb.filter_mono hl⟩
    · obtain ⟨U⟩ := ha x hx
      exact rate_of_jet_limit_of_small_scale hh hh1 hL ((U.jet_tendsto m).mono_left hl)
  · refine ⟨0,le_rfl,?_⟩
    have hn : {y : SpaceTime | 1 < y.1} ∈ 𝓝 (t,x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with y hy hyS
    exact False.elim (not_lt_of_ge hy.le hyS.1)

theorem bound_of_origin_and_exterior {h L R : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (hL : 0 ≤ L) (hR : 0 ≤ R) {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (ha : JointResidualLimits.AwayExtensions f) (m : ℕ)
    (ho : DiagonalResidual.JetRate ActualBaseVelocityBounds.endpoint (physicalQ h) f m (-L))
    (he : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      R < (SlowBorelBase.cartesianChart h w).2.1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-L)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * physicalQ h w ^ (-L) := by
  let K := Metric.closedBall (0 : SpaceTime) (R+2)
  obtain ⟨A,hA,hAb⟩ := compact_bound_of_local_rates (S := unitDomain h)
    (isCompact_closedBall (0 : SpaceTime) (R+2))
    (fun _ hw => physicalQ_pos hh hh1 hw.1)
    (fun _ _ => local_rate hh hh1 hL hf ha m ho _)
  obtain ⟨B,hB,hBb⟩ := he
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro w hw hq
  by_cases hk : w ∈ K
  · exact (hAb w ⟨hk,hw,hq⟩).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB)
        (Real.rpow_nonneg (physicalQ_pos hh hh1 hw).le _))
  · have hX : R < (SlowBorelBase.cartesianChart h w).2.1 := by
      by_contra hX
      exact hk (in_compact_of_radial_bound hh hh1 hR hw hq (le_of_not_gt hX))
    exact (hBb w hw hq hX).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA)
        (Real.rpow_nonneg (physicalQ_pos hh hh1 hw).le _))

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
    (v : ModulatedProfileAssembly.Witness ld)

theorem velocity_bound (upper : ℝ) (B m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ F.data.h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (FinalSlowBase.velocity H v upper B) w‖ ≤
        C * physicalQ F.data.h w ^ (-ActualBaseVelocityBounds.heatLoss m) := by
  apply bound_of_origin_and_exterior F.data.h_pos F.data.h_lt_half
    (ActualBaseVelocityBounds.heatLoss_nonneg m) (BaseExterior.nominalExteriorRadius_pos W).le
    (FinalSlowBase.velocity_smooth H v upper B)
    (SlowBaseEndpoint.final_fields_awayExtensions H v upper B).1 m
    (ActualBaseVelocityBounds.velocity_rate H v upper B m)
  obtain ⟨C,hC,hb⟩ := WholeDomainHeatBounds.heat_velocity_bound
    (BaseExterior.nominalHeatNormalization W) F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius_pos W) m
  refine ⟨C,hC,?_⟩
  intro w hw hq hX
  have he : FinalSlowBase.velocity H v upper B =ᶠ[𝓝 w]
      BaseExterior.heatVelocity (BaseExterior.nominalHeatNormalization W) F.data.h :=
    Filter.eventuallyEq_of_mem
      ((BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _).mem_nhds ⟨hw,hX⟩)
      (FinalSlowBase.exterior_fields_eq_heat H v upper B).1
  rw [iteratedFDeriv_eq_of_eventuallyEq he m]
  refine (hb w hw hq hX).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos F.data.h_pos F.data.h_lt_half hw) hq ?_) hC)
  rw [ActualBaseVelocityBounds.heatLoss_eq]
  unfold WholeDomainHeatBounds.heatLoss
  have hm : 0 ≤ (m : ℝ) := by positivity
  nlinarith [sq_nonneg (m : ℝ)]

theorem pressure_bound (upper : ℝ) (B m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ F.data.h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (FinalSlowBase.pressure H v upper B) w‖ ≤
        C * physicalQ F.data.h w ^ (-ActualBasePressureBounds.pressureLoss m) := by
  apply bound_of_origin_and_exterior F.data.h_pos F.data.h_lt_half
    (ActualBasePressureBounds.pressureLoss_nonneg m) (BaseExterior.nominalExteriorRadius_pos W).le
    (FinalSlowBase.pressure_smooth H v upper B)
    (SlowBaseEndpoint.final_fields_awayExtensions H v upper B).2 m
    (ActualBasePressureBounds.pressure_rate H v upper B m)
  obtain ⟨C,hC,hb⟩ := WholeDomainHeatBounds.heat_pressure_bound
    (BaseExterior.nominalHeatNormalization W) F.data.h_pos F.data.h_lt_half
    (BaseExterior.nominalExteriorRadius_pos W) m
  refine ⟨C,hC,?_⟩
  intro w hw hq hX
  have he : FinalSlowBase.pressure H v upper B =ᶠ[𝓝 w]
      BaseExterior.heatPressureField (BaseExterior.nominalHeatNormalization W) F.data.h :=
    Filter.eventuallyEq_of_mem
      ((BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _).mem_nhds ⟨hw,hX⟩)
      (FinalSlowBase.exterior_fields_eq_heat H v upper B).2
  rw [iteratedFDeriv_eq_of_eventuallyEq he m]
  refine (hb w hw hq hX).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (physicalQ_pos F.data.h_pos F.data.h_lt_half hw) hq ?_) hC)
  unfold WholeDomainHeatBounds.heatLoss ActualBasePressureBounds.pressureLoss
  have hm : 0 ≤ (m : ℝ) := by positivity
  linarith

def baseLoss (m : ℕ) : ℝ :=
  ActualBaseVelocityBounds.heatLoss m + ActualBasePressureBounds.pressureLoss m

theorem baseLoss_nonneg (m : ℕ) : 0 ≤ baseLoss m :=
  add_nonneg (ActualBaseVelocityBounds.heatLoss_nonneg m)
    (ActualBasePressureBounds.pressureLoss_nonneg m)

/-- One derivative-order loss controls both actual base fields throughout
the same unbounded physical domain, independently of the Borel index. -/
theorem velocity_pressure_bound (upper : ℝ) (B m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ F.data.h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (FinalSlowBase.velocity H v upper B) w‖ +
        ‖iteratedFDeriv ℝ m (FinalSlowBase.pressure H v upper B) w‖ ≤
          C * physicalQ F.data.h w ^ (-baseLoss m) := by
  obtain ⟨A,hA,hAb⟩ := velocity_bound H v upper B m
  obtain ⟨C,hC,hCb⟩ := pressure_bound H v upper B m
  refine ⟨A+C,add_nonneg hA hC,?_⟩
  intro w hw hq
  have hq0 := physicalQ_pos F.data.h_pos F.data.h_lt_half hw
  have hv : ‖iteratedFDeriv ℝ m (FinalSlowBase.velocity H v upper B) w‖ ≤
      A * physicalQ F.data.h w ^ (-baseLoss m) :=
    (hAb w hw hq).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq0 hq (by
        unfold baseLoss
        linarith [ActualBasePressureBounds.pressureLoss_nonneg m])) hA)
  have hp : ‖iteratedFDeriv ℝ m (FinalSlowBase.pressure H v upper B) w‖ ≤
      C * physicalQ F.data.h w ^ (-baseLoss m) :=
    (hCb w hw hq).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq0 hq (by
        unfold baseLoss
        linarith [ActualBaseVelocityBounds.heatLoss_nonneg m])) hC)
  simpa only [add_mul] using add_le_add hv hp

end Actual

end NavierStokes.WholeDomainBaseBounds
