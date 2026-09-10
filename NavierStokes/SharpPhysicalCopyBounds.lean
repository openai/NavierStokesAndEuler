import NavierStokes.LocalPhysicalCopyBounds
import NavierStokes.SharpPhysicalLoss

noncomputable section
namespace NavierStokes.SharpPhysicalCopyBounds
open Set Function Filter ProblemStatement PhysicalWaveSum PhysicalCopyBounds LocalPhysicalCopyBounds
open SharpPhysicalPhase SharpPhysicalCarrier
open scoped Topology ContDiff BigOperators

theorem common_carrier_log_bound {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (_hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (_hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ c.F → ContDiff ℝ ∞ c.G → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G
        (PhysicalGraphBounds.slotMap (PolarCharts.chart a c.chart)
          (ChartScales.timeCoefficient h n) c.center r0 (PhysicalGraphBounds.physicalLift h n w)).1‖ ≤
            B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log q|)^N := by
  have hK : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨C,hC,hb⟩ := SharpPhysicalCarrier.native_carrier_bound (b := b) hh ha hr0 hP hB heBase
    m g eAmp (A*coverBound Δ^m) H (by positivity) hH
  obtain ⟨D,hD,N,hweight⟩ := SharpLogWeights.chart_weight_bound
    (g-(m:ℝ)*derivativeCost h) (eAmp+(eBase+1)*(m:ℝ))
  refine ⟨C*D,mul_nonneg hC hD.le,N,?_⟩
  intro n hn d hd w hw ht hz q hq hlo hhi c amp j hp hpz hx0 hslot hamp hF hG hj hab hFb hGb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have ha : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (amp ∘ downLift d) (PhysicalGraphBounds.physicalLift h n w)‖ ≤
      (A*coverBound Δ^m)*ChartScales.Q n^g*ChartScales.S n^eAmp := by
    intro i hi
    exact (downLift_jet_bound hamp hd (PhysicalGraphBounds.physicalLift h n w)
      (B := A*ChartScales.Q n^g*ChartScales.S n^eAmp) (by positivity) hab i hi).trans_eq (by ring)
  have hF' : ∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F (slowMap (PolarCharts.chart a c.chart) h n w)‖ ≤
      B*ChartScales.S n^eBase := by
    intro i hi
    rw [slowMap_eq_slot _ _ _ c.center r0]
    exact hFb i hi
  have hG' : ∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G (slowMap (PolarCharts.chart a c.chart) h n w)‖ ≤
      B*ChartScales.S n^eBase := by
    intro i hi
    rw [slowMap_eq_slot _ _ _ c.center r0]
    exact hGb i hi
  have he := hb n hn w hw ht c.chart c.center c.angular c.axial c.radial hp hpz hx0 hslot
    (amp ∘ downLift d) c.F c.G j (hamp.comp (downLift d).contDiff) hF hG hj ha hF' hG'
  apply he.trans
  calc
    _ = C*(ChartScales.Q n^(g-(m:ℝ)*derivativeCost h)*ChartScales.S n^(eAmp+(eBase+1)*(m:ℝ))) := by ring
    _ ≤ C*(D*q^(g-(m:ℝ)*derivativeCost h)*(1+|Real.log q|)^N) :=
      mul_le_mul_of_nonneg_left (hweight n (by omega) q hq hlo hhi) hC
    _ = _ := by ring

theorem common_carrier_log_bound_local {h a b Z r0 P B eBase : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (Δ m : ℕ) (g eAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b →
      |w.1| ≤ 1 → ‖PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)‖ ≤ Z →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ (c : CarrierData) (amp : LiftPoint → ℂ) (j : ℤ),
      |c.angular| ≤ P → |c.axial| ≤ P → |c.radial| ≤ P →
      |PhysicalGraphBounds.etaCoordinate (PhysicalGraphBounds.nativeGraph h n w - c.center)| ≤ r0 →
      SmoothNear amp (commonLift h n d w) → SmoothNear c.F (slotSlow c a h n r0 w) →
      SmoothNear c.G (slotSlow c a h n r0 w) → |(j : ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ eAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.F (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i c.G (slotSlow c a h n r0 w)‖ ≤
        B * ChartScales.S n ^ eBase) →
      ‖iteratedFDeriv ℝ m (commonWave a h n d r0 c amp j) w‖ ≤
        C * q ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log q|)^N := by
  obtain ⟨C, hC, N, hb⟩ := common_carrier_log_bound (b := b)
    hh hh1 ha hZ hr0 hP hB heBase Δ m g eAmp A H hA hH
  refine ⟨C, hC, N, ?_⟩
  intro n hn d hd w hann ht hz q hq hlo hhi c amp j hp hpz hpx hslot haNear hFNear hGNear hj hab hFb hGb
  obtain ⟨amp', ha', hea⟩ := haNear.exists_global_germ
  obtain ⟨F, hF', heF⟩ := hFNear.exists_global_germ
  obtain ⟨G, hG', heG⟩ := hGNear.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hann)
  rw [iteratedFDeriv_eq_of_eventuallyEq (commonWave_germ ha h n d r0 c j haxis hea heF heG) m]
  apply hb n hn d hd w hann ht hz q hq hlo hhi (replaceProfiles c F G) amp' j
    hp hpz hpx hslot ha' hF' hG' hj
  · intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq hea i]
    exact hab i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i F (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heF i]
    exact hFb i hi
  · intro i hi
    change ‖iteratedFDeriv ℝ i G (slotSlow c a h n r0 w)‖ ≤ _
    rw [← iteratedFDeriv_eq_of_eventuallyEq heG i]
    exact hGb i hi

theorem physical_sum_log_bound {K : Type*} {h a b Z r0 P B eBase : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a)
    (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B) (heBase : 0 ≤ eBase)
    (H Δ m : ℕ) (g eAmp A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ f : CopyFamily H K,
      SupportData f a b h r0 Z Δ → SmoothData f a h r0 → ∀ hc : SupportCells f,
      JetData f hc a b h r0 P A B g eAmp eBase m →
      ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) w‖ ≤
        C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N := by
  obtain ⟨C, hC, N, hpoint⟩ := common_carrier_log_bound_local (b := b) hh.le hh1.le ha
    hZ hr0 hP hB heBase Δ m g eAmp A (H : ℝ) hA (Nat.cast_nonneg H)
  refine ⟨((2250 * (2 * H + 1) : ℕ) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC, N, ?_⟩
  intro f hr hs hc hb w hw ht
  have hq := physicalQ_pos hh hh1 hw
  have hcopy : ∀ (I : WaveIndex H),
      physicalParams h w ∈ labelRegion (CoordinateAlgebra.D h) I.1.val → ∀ k,
      ‖iteratedFDeriv ℝ m (f.term a h r0 I k) w‖ ≤
        C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N := by
    intro I hregion k
    by_cases hts : w ∈ tsupport (f.term a h r0 I k)
    · have hgeo := hr.tsupport_geometry I k hts
      have hcell := hc.term_tsupport_mem ha I k hgeo.1 hts
      obtain ⟨mode, hmode⟩ := hr.angular_integer k I.1
      let chart := chooseChart a (PhysicalGraphBounds.scaledRadial I.1.val.1 w)
      have hchart : PhysicalGraphBounds.scaledRadial I.1.val.1 w ∈ PolarCharts.chartDomain a chart :=
        chooseChart_valid ha hgeo.1
      have he := globalWave_eventually_common (r0 := r0) ha I.1.val.1 (f.gap I.1)
        (f.carrier k I.1) (f.amplitude k I) I.2.val mode hmode
        (fun y hy => (hr.geometry_support k I y hy).1) chart hchart
      change ‖iteratedFDeriv ℝ m (globalWave a h I.1.val.1 (f.gap I.1) r0
        (f.carrier k I.1) (f.amplitude k I) I.2.val) w‖ ≤ _
      rw [iteratedFDeriv_eq_of_eventuallyEq he m]
      have hband := labelRegion_active_relation hregion
      have hp := hs.profiles k I w hw hts chart hchart
      have hjets := hb.jets k I w hw hregion hgeo.1 hcell hts
      exact hpoint I.1.val.1 I.1.property (f.gap I.1) (hr.gap_le I.1)
        w hgeo.1 ht hgeo.2.1 (physicalQ h w) hq hband.1 hband.2
        ((f.carrier k I.1).withChart chart) (f.amplitude k I) I.2.val
        (hb.parameters k I.1).1 (hb.parameters k I.1).2.1 (hb.parameters k I.1).2.2 hgeo.2.2
        (hs.amplitude k I w hw hts) hp.1 hp.2 (harmonic_bound I.2)
        hjets.1 (hjets.2 chart hchart).1 (hjets.2 chart hchart).2
    · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
      positivity
  have hsum := masked_finsum_jet_bound hh hh1 (f.periodized a h r0)
    (hr.periodized_smoothAt hs hc ha) hr.periodized_support hw m
    (B := C * physicalQ h w ^ (g - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h w)|)^N) (by positivity)
  refine (hsum ?_).trans_eq (by ring)
  intro I hregion
  rcases hr.periodized_germ_cover hc ha I w with ⟨k, _, hg⟩ | hg
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    exact hcopy I hregion k
  · rw [iteratedFDeriv_eq_of_eventuallyEq hg m]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    positivity



section WeightedInputs
open WeightedClasses
variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {ι K : Type*}
  {h a b r0 Z : ℝ} {H Δ : ℕ} {f : CopyFamily H K}

theorem physical_sum_log_bound_of_weighted {s : StripData D} {α σ P : ℝ}
    {w : ι → ℕ → D → ℝ} {source : ι → ℕ → D → ℂ}
    (hsource : LocalSourceBounds s h α w source) {hc : SupportCells f}
    (hchart : CommonChart f hc a b h r0 σ source)
    (hmap : ∀ k I, MapsTo (hchart.map k I) (hchart.domain k I) s.domain)
    (hb : PhysicalCopyBounds.CarrierBounds f hc a b h r0)
    (hr : SupportData f a b h r0 Z Δ) (hs : SmoothData f a h r0)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ k L, |(f.carrier k L).angular| ≤ P ∧
      |(f.carrier k L).axial| ≤ P ∧ |(f.carrier k L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ z : SpaceTime,
      z ∈ preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (f.sum a h r0) z‖ ≤
        C * physicalQ h z ^ (h * α + σ - (m:ℝ)*derivativeCost h) * (1+|Real.log (physicalQ h z)|)^N := by
  obtain ⟨A, hA, B, hB, p, q, hclass⟩ := localStrippedClass_of_weighted hsource hchart hmap hb hs hp m
  obtain ⟨C, hC, N, hbound⟩ := physical_sum_log_bound (K := K)
    (b := b) hh hh1 ha hZ hr0 hP hB (Nat.cast_nonneg q) H Δ m
      (h * α + σ) p A hA
  refine ⟨C, hC, N, ?_⟩
  intro z hz ht
  exact hbound f hr hs hc hclass z hz ht

end WeightedInputs
end NavierStokes.SharpPhysicalCopyBounds
