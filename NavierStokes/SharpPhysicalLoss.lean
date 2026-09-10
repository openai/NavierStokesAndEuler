import NavierStokes.SharpLogWeights

noncomputable section
namespace NavierStokes.SharpPhysicalLoss
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhysicalPhase SharpPhysicalCarrier
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Physical rescaling and any derivative order up to the recovery order
fit the exact loss printed in the manuscript. -/
theorem rescale_with_common_loss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h σ g e C : ℝ} (hh : 0 ≤ h) (hσ : -(2*CoordinateAlgebra.A h) ≤ σ) (hC : 0 ≤ C)
    (n m k : ℕ) (hkm : k ≤ m+1) {f : SpaceTime → E} {w : SpaceTime}
    (hf : ContDiffAt ℝ ∞ f w)
    (hb : ‖iteratedFDeriv ℝ k f w‖ ≤ C*ChartScales.Q n^(g-(k:ℝ)*derivativeCost h)*ChartScales.S n^e) :
    ‖iteratedFDeriv ℝ k (fun z => ChartScales.Q n^σ • f z) w‖ ≤
      C*ChartScales.Q n^(g-physicalLoss h m)*ChartScales.S n^e := by
  have hQ := ChartScales.Q_pos n
  have hS : 0 ≤ ChartScales.S n := sq_nonneg (n:ℝ)
  have hcost : 0 ≤ derivativeCost h := by unfold derivativeCost; linarith
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have hexp : g-physicalLoss h m ≤ σ+(g-(k:ℝ)*derivativeCost h) := by
    unfold physicalLoss
    nlinarith
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (nat_le_infty k)), norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]
  calc
    _ ≤ ChartScales.Q n^σ * (C*ChartScales.Q n^(g-(k:ℝ)*derivativeCost h)*ChartScales.S n^e) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ.le _)
    _ = C*ChartScales.Q n^(σ+(g-(k:ℝ)*derivativeCost h))*ChartScales.S n^e := by
      rw [Real.rpow_add hQ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) hexp) hC)
      (Real.rpow_nonneg hS _)

/-- All four physical prefactors listed in the paper satisfy the common
rescaling hypothesis. -/
theorem physical_prefactors (h : ℝ) (hh : 0 ≤ h) :
    -(2*CoordinateAlgebra.A h) ≤ -CoordinateAlgebra.A h ∧
    -(2*CoordinateAlgebra.A h) ≤ -(2*CoordinateAlgebra.A h) ∧
    -(2*CoordinateAlgebra.A h) ≤ 1/2-CoordinateAlgebra.A h := by
  unfold CoordinateAlgebra.A
  constructor
  · linarith
  constructor
  · rfl
  · linarith

/-- Actual rescaled native carriers obey the printed `ell_m` with a genuine
logarithmic factor. The extra derivative needed for velocity recovery is
already included on the left. All constants are uniform in band and label. -/
theorem native_rescaled_log_bound {h a b r0 P B dBase : ℝ}
    (hh : 0 ≤ h) (ha : 0 < a) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B)
    (hdBase : 0 ≤ dBase) (m : ℕ) (σ g dAmp A H : ℝ)
    (hσ : -(2*CoordinateAlgebra.A h) ≤ σ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q/2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2*q →
      ∀ (chart : PolarCharts.Index) (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P →
      |etaCoordinate (nativeGraph h n w-center)| ≤ r0 →
      ∀ (amp : LiftPoint → ℂ) (F G : Slow → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → |(j:ℝ)| ≤ H →
      (∀ i ≤ m+1, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^dAmp) →
      (∀ i ≤ m+1, ‖iteratedFDeriv ℝ i F
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      (∀ i ≤ m+1, ‖iteratedFDeriv ℝ i G
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      ‖iteratedFDeriv ℝ (m+1) (fun z => ChartScales.Q n^σ •
        ((fun y => amp y * character ((ChartScales.carrier h n:ℝ)*(j:ℝ))
          (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘
            physicalLift h n) z) w‖ ≤
      C*q^(g-physicalLoss h m)*(1+|Real.log q|)^N := by
  obtain ⟨C,hC,hbound⟩ := native_carrier_bound (b := b) hh ha hr0 hP hB hdBase
    (m+1) g dAmp A H hA hH
  obtain ⟨D,hD,N,hlog⟩ := SharpLogWeights.chart_weight_bound
    (g-physicalLoss h m) (dAmp+(dBase+1)*((m+1:ℕ):ℝ))
  refine ⟨C*D, mul_nonneg hC hD.le, N, ?_⟩
  intro n hn w hw ht q hq hlo hhi chart center p pz x0 hp hpz hx0 hslot
    amp F G j hamp hF hG hj hab hFb hGb
  have hb := hbound n hn w hw ht chart center p pz x0 hp hpz hx0 hslot amp F G j
    hamp hF hG hj hab hFb hGb
  let W : Set SpaceTime := {z | radialProjection z ≠ 0}
  have hW : IsOpen W := axisFree_open.preimage radialProjection.continuous
  have hwW : w ∈ W := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hκ := PolarCharts.chart_contDiff ha chart
  have houter : ContDiff ℝ ∞ (fun y => amp y * character ((ChartScales.carrier h n:ℝ)*(j:ℝ))
      (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) :=
    hamp.mul ((character_smooth _).comp (liftedPhase_smooth hκ h n center r0 p pz x0 hF hG))
  have hcomp : ContDiffAt ℝ ∞ ((fun y => amp y * character ((ChartScales.carrier h n:ℝ)*(j:ℝ))
      (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘ physicalLift h n) w :=
    houter.contDiffAt.comp w ((physicalLift_smooth h n).contDiffAt (hW.mem_nhds hwW))
  apply (rescale_with_common_loss hh hσ hC n m (m+1) le_rfl hcomp hb).trans
  calc
    _ = C*(ChartScales.Q n^(g-physicalLoss h m)*
        ChartScales.S n^(dAmp+(dBase+1)*((m+1:ℕ):ℝ))) := by ring
    _ ≤ C*(D*q^(g-physicalLoss h m)*(1+|Real.log q|)^N) :=
      mul_le_mul_of_nonneg_left (hlog n (by omega) q hq hlo hhi) hC
    _ = _ := by ring

end NavierStokes.SharpPhysicalLoss
