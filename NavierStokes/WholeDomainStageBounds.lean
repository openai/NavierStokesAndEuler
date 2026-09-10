import NavierStokes.WholeDomainPhysicalCompact
import NavierStokes.ActualCycleResidualBounds
import NavierStokes.PhysicalStageBounds
import NavierStokes.AnnularEndpoint

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Filter Function ProblemStatement
open scoped Topology ContDiff BigOperators

open PhysicalWaveSum

section BaseResidual

open CorrectionInitialization CorrectionInitialization.ActualPrimary ActualCycleResidualBounds

private abbrev baseResidual (B : ℕ) : VelocityField :=
  PhysicalResidualJetBounds.residual (FinalSlowBase.velocity certificate modulation upper B)
    (FinalSlowBase.pressure certificate modulation upper B)

private def exteriorDomain : Set SpaceTime :=
  {w | w ∈ preterminal ∧ physicalQ h w ≤ 1 ∧ w ∉ active}

private theorem exteriorDomain_past : exteriorDomain ⊆ SpacetimeEndpoint.openPast 1 :=
  fun _ hw => ⟨hw.1, Set.mem_univ _⟩

private theorem baseResidual_smooth (B : ℕ) :
    ContDiffOn ℝ ∞ (baseResidual B) (SpacetimeEndpoint.openPast 1) :=
  ResidualRegularity.contDiffOn_residual (SpacetimeEndpoint.openPast_isOpen 1)
    (FinalSlowBase.velocity_smooth certificate modulation upper B)
    (FinalSlowBase.pressure_smooth certificate modulation upper B)

/-- At nonzero limiting axial coordinate the genuine endpoint chart has
a positive limiting scale. -/
theorem physicalQ_tendsto_offplane {x : Space} (hx : x 2 ≠ 0) :
    Tendsto (physicalQ h) (𝓝[SpacetimeEndpoint.openPast 1] (1,x))
      (𝓝 ((EndpointCoordinates.cartesianExtension h (1,x)).1)) := by
  have hc := (EndpointCoordinates.cartesianExtension_smoothAt outgoing.data.h_pos
    outgoing.data.h_lt_half (EndpointCoordinates.cartesian_endpoint_mem
      outgoing.data.h_pos outgoing.data.h_lt_half hx)).continuousAt.fst
  apply (hc.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact congrArg Prod.fst (EndpointCoordinates.cartesianExtension_eq_physical
    outgoing.data.h_pos outgoing.data.h_lt_half hw.1)

private theorem baseResidual_local_rate (B m : ℕ) (r : ℝ) (w : SpaceTime) :
    DiagonalResidual.JetRate (𝓝[exteriorDomain] w) (physicalQ h) (baseResidual B) m r := by
  rcases w with ⟨t,x⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · have hs := (baseResidual_smooth B).contDiffAt
      ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds
        (show (t,x) ∈ SpacetimeEndpoint.openPast 1 from ⟨ht, mem_univ x⟩))
    have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ m (baseResidual B)) (t,x) :=
      hs.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (m : ℕ∞) ≤ ⊤))
    exact rate_of_jet_limit (hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((physicalQ_smoothAt outgoing.data.h_pos outgoing.data.h_lt_half ht).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds) (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht) r
  · subst t
    have hmono : 𝓝[exteriorDomain] ((1:ℝ),x) ≤
        𝓝[SpacetimeEndpoint.openPast 1] ((1:ℝ),x) := nhdsWithin_mono _ exteriorDomain_past
    by_cases hz : x 2 = 0
    · have hcarrier : ∀ᶠ y in 𝓝[exteriorDomain] ((1:ℝ),x),
          y ∈ Metric.closedBall ((1:ℝ),x) 1 :=
        nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ zero_lt_one)
      have hpast : ∀ᶠ y in 𝓝[exteriorDomain] ((1:ℝ),x), y.1 < 1 := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hy.1
      have hscale := (AnnularEndpoint.physicalQ_tendsto_zero outgoing.data.h_pos
        outgoing.data.h_lt_half hz).mono_left hmono
      obtain ⟨C,hC,hb⟩ := GlobalBaseError.error_jetRate certificate modulation upper B
        actual_upper_covers_exterior (isCompact_closedBall _ _) hcarrier hpast hscale
        m (max r 0) (le_max_right _ _)
      refine ⟨C,hC,?_⟩
      filter_upwards [hb,self_mem_nhdsWithin] with y hy hyS
      rw [iteratedFDeriv_eq_of_eventuallyEq
        (base_residual_germ B hyS.1 hyS.2.2) m]
      exact hy.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge
          (physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hyS.1)
          hyS.2.1 (le_max_left _ _)) hC)
    · let U := SlowBaseEndpoint.finalVelocityNonzeroAxial certificate modulation upper B hz
      let P := SlowBaseEndpoint.finalPressureNonzeroAxial certificate modulation upper B hz
      have hp := EndpointCoordinates.cartesianExtension_pos
        (EndpointCoordinates.cartesian_endpoint_mem outgoing.data.h_pos outgoing.data.h_lt_half hz)
      exact rate_of_jet_limit ((residualExtension U P).jet_tendsto m |>.mono_left hmono)
        ((physicalQ_tendsto_offplane hz).mono_left hmono) hp r
  · refine ⟨0,le_rfl,?_⟩
    have hn : {y : SpaceTime | 1 < y.1} ∈ 𝓝 ((t:ℝ),x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with y hy hyS
    exact False.elim (not_lt_of_ge hy.le hyS.1)

/-- Every exterior base residual jet has every power bound on the whole
unit sublevel. Its constant may depend on the order and power, but its
domain does not. -/
theorem base_exterior_bound (B m : ℕ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 → w ∉ active →
      ‖iteratedFDeriv ℝ m (baseResidual B) w‖ ≤ C * physicalQ h w ^ r := by
  let R := max (BaseExterior.nominalExteriorRadius nominal) 0
  have hR : 0 ≤ R := le_max_right _ _
  obtain ⟨C,hC,hb⟩ := bound_of_local_rates_and_zero
    (S := exteriorDomain) (K := Metric.closedBall (0 : SpaceTime) (R+2))
    (isCompact_closedBall _ _)
    (fun w hw => physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1)
    (fun w _ => baseResidual_local_rate B m r w) (by
      intro w hw hn
      have hX : R < (SlowBorelBase.cartesianChart h w).2.1 := by
        by_contra hX
        exact hn (in_compact_of_radial_bound outgoing.data.h_pos outgoing.data.h_lt_half
          hR hw.1 hw.2.1 (le_of_not_gt hX))
      exact FinalSlowBase.exterior_residual_jets_zero certificate modulation upper B m
        ⟨hw.1, (le_max_left _ _).trans_lt hX⟩)
  exact ⟨C,hC,fun w hw hq ha => hb w ⟨hw,hq,ha⟩⟩

end BaseResidual

section ResidualAssembly

open ActualCycleResidualBounds PhysicalResidualJetBounds CorrectionInitialization

/-- Annular estimates and exterior germs give a bound at every point of
the same sublevel. This is an actual pointwise bound, not a filter rate. -/
theorem selected_residual_bound {a b h gain β : ℝ} {N Δ : ℕ} {gap : ℕ → ℕ}
    {U V : Set ActualCycleResidualBounds.Cylinder} {S : Set SpaceTime}
    {c : CorrectionState.Context ActualCycleResidualBounds.Point}
    {s : CorrectionState.State ActualCycleResidualBounds.Point}
    {p₀ : ℕ → ActualCycleResidualBounds.Cylinder → ℝ} {u u₀ : VelocityField} {P P₀ : PressureField}
    (r : StateRealization h N gap U c s p₀ u P)
    (g : SelectedGeometry a b h N Δ gap U V S)
    (hh : 0 < h) (hh1 : h < 1/2) (ha : 0 < a) (hN : 4 ≤ N)
    (hf : NativeBounds N V gain (fun m => β * m)
      (fun (_ : Unit) => LiftedMeanResidual.fullResidual c s))
    (houtside : ∀ w, w ∈ preterminal → physicalQ h w < ChartScales.Q N → w ∉ S →
      u =ᶠ[𝓝 w] u₀ ∧ P =ᶠ[𝓝 w] P₀) (m : ℕ)
    (hbase : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ preterminal, physicalQ h w ≤ 1 → w ∉ S →
      ‖iteratedFDeriv ℝ m (residual u₀ P₀) w‖ ≤
        C * physicalQ h w ^ (gain - physicalLoss h β m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h (ChartScales.Q N),
      physicalQ h w ≤ 1 → ‖iteratedFDeriv ℝ m (residual u P) w‖ ≤
        C * physicalQ h w ^ (gain - physicalLoss h β m) := by
  obtain ⟨C,hC,hb⟩ := selected_residual_jet_bound r g hh hh1 ha hN hf m
  obtain ⟨B,hB,hbase⟩ := hbase
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro w hw hq
  have hq0 := physicalQ_pos hh hh1 hw.1
  by_cases hs : w ∈ S
  · exact (hb w hw.1 (PhysicalStageBounds.abs_time_le_one hh hh1 hw.1 hq) hw.2.le hs).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (Real.rpow_nonneg hq0.le _))
  · obtain ⟨hu,hp⟩ := houtside w hw.1 hw.2 hs
    have he : residual u P =ᶠ[𝓝 w] residual u₀ P₀ :=
      ResidualRegularity.residual_eventuallyEq hu hp
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    exact (hbase w hw.1 hq hs).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (Real.rpow_nonneg hq0.le _))

/-- The actual invariant controls the complete residual on a whole fixed
sublevel, including points outside the perturbation annulus. -/
theorem invariant_residual_bound {B N0 N : ℕ} {σ : ℝ}
    {x : CorrectionStep.CycleState (ActualCycleResidualBounds.Index B N0)}
    (H : ActualCycleResidualBounds.Invariant σ x) {u : VelocityField} {P : PressureField}
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (hN : 4 ≤ N)
    (hbase : x.state.errors.base = ActualInitialization.baseError B)
    (d : PhysicalData B N x.state u P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel ActualPrimary.h (ChartScales.Q N),
      physicalQ ActualPrimary.h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (residual u P) w‖ ≤
        C * physicalQ ActualPrimary.h w ^ (ActualPrimary.h * (1/2+σ) - fixedLoss m) := by
  have hr := H.stateRealization ActualPolarCoverage.nativeDomain_open
    (fun z hz => ActualPolarCoverage.nativeDomain_radius_pos hz)
    (fun z hz => hz.1.1) hbase d
  exact selected_residual_bound hr (actual_selectedGeometry N)
    ActualPrimary.outgoing.data.h_pos ActualPrimary.outgoing.data.h_lt_half
    ActualPolarCoverage.inner_pos hN
    (native_restrict (H.native_residual hGeom hbase) hN (Subset.refl _))
    (fun _ hw hq hout => d.exterior_germs hw hq hout) m (base_exterior_bound B m _)

end ResidualAssembly

end NavierStokes.WholeDomainStageBounds
