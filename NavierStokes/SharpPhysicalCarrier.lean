import NavierStokes.SharpPhysicalPhase

noncomputable section
namespace NavierStokes.SharpPhysicalCarrier
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhaseJetAlgebra SharpPhysicalPhase
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- The manuscript's common Cartesian derivative cost for an oscillatory factor. -/
def derivativeCost (h : ℝ) : ℝ := 1 + 3*h/2

/-- The printed physical loss includes one derivative for potential recovery. -/
def physicalLoss (h : ℝ) (m : ℕ) : ℝ :=
  2*CoordinateAlgebra.A h + ((m:ℝ)+1)*derivativeCost h

/-- A real physical phase with sharp positive jets gives the exact linear
carrier loss. Slow powers remain explicit, and are not absorbed into `Q`. -/
theorem carrier_geometric_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) (g d e A B H : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (he : 0 ≤ e) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ∀ (amp : LiftPoint → ℂ) (Φ : SpaceTime → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ Φ → |(j:ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ d) →
      (∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ w‖ ≤
        (B * ChartScales.S n ^ e * ChartScales.Q n ^ (-(1+h))) ^ i) →
      ‖iteratedFDeriv ℝ m (fun z => amp (physicalLift h n z) *
        character ((ChartScales.carrier h n:ℝ)*(j:ℝ)) (Φ z)) w‖ ≤
        C * ChartScales.Q n ^ (g-(m:ℝ)*derivativeCost h) *
          ChartScales.S n ^ (d+e*(m:ℝ)) := by
  obtain ⟨K, hK, hgraph⟩ := SharpGraphBounds.physicalLift_positive_jet_bound (b := b) hh ha m
  let C := (2:ℝ)^m*(m.factorial:ℝ)^2*A*(1+2*H)^m*(K+B)^m
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro n hn w hw ht amp Φ j hamp hΦ hj hab hph
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hS1 := S_ge_one (show 1 ≤ n by omega)
  have hSe : 1 ≤ ChartScales.S n ^ e := Real.one_le_rpow hS1 he
  let U := (K+B)*ChartScales.S n^e*ChartScales.Q n^(-(1+h))
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hscale : 1 ≤ ChartScales.Q n ^ (-h/2) := by
    have hb := Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) (show -h/2 ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hb
  let M := (1+2*H)*ChartScales.Q n^(-h/2)
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (by linarith) hscale
  have hM0 : 0 ≤ M := by linarith
  have hc : |(ChartScales.carrier h n:ℝ)*(j:ℝ)| ≤ M := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (2*ChartScales.Q n^(-h/2))*H :=
        mul_le_mul (carrier_upper hh n) hj (abs_nonneg _) (by positivity)
      _ ≤ M := by dsimp [M]; nlinarith [Real.rpow_nonneg hQ.le (-h/2)]
  let W : Set SpaceTime := {z | radialProjection z ≠ 0}
  have hW : IsOpen W := axisFree_open.preimage radialProjection.continuous
  have hwW : w ∈ W := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hgraphU : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i (physicalLift h n) w‖ ≤ U^i := by
    intro i hi him
    apply (hgraph n hn w hw ht i hi him).trans
    have hqpow : ChartScales.Q n^(-(i:ℝ)*(1+h)) = (ChartScales.Q n^(-(1+h)))^i := by
      rw [← Real.rpow_mul_natCast hQ.le]
      congr 1
      ring
    rw [hqpow]
    calc
      _ ≤ K^i*(ChartScales.Q n^(-(1+h)))^i :=
        mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hK hi) (by positivity)
      _ = (K*ChartScales.Q n^(-(1+h)))^i := (mul_pow _ _ _).symm
      _ ≤ U^i := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [U]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
        exact (show K ≤ K+B by linarith).trans (le_mul_of_one_le_right (by linarith) hSe)
  have hphaseU : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ w‖ ≤ U^i := by
    intro i hi him
    apply (hph i hi him).trans
    apply pow_le_pow_left₀ (by positivity)
    dsimp [U]
    gcongr
    linarith
  have hampj := composition_geometric_on hW (physicalLift_smooth h n) hamp hwW m
    (show 0 ≤ A*ChartScales.Q n^g*ChartScales.S n^d by positivity) hU hab hgraphU
  have hcharj := composition_geometric hΦ (character_smooth ((ChartScales.carrier h n:ℝ)*(j:ℝ)))
    w m (pow_nonneg hM0 m) hU
    (fun i hi => by
      rw [norm_character_jet]
      exact (pow_le_pow_left₀ (abs_nonneg _) hc i).trans (pow_le_pow_right₀ hM hi)) hphaseU
  have hampW : ContDiffOn ℝ ∞ (amp ∘ physicalLift h n) W :=
    hamp.contDiffOn.comp (physicalLift_smooth h n) (mapsTo_univ _ _)
  have hprod := product_geometric_on hW hampW
    ((character_smooth _).comp hΦ).contDiffOn hwW m
    (show 0 ≤ (m.factorial:ℝ)*(A*ChartScales.Q n^g*ChartScales.S n^d) by positivity)
    (show 0 ≤ (m.factorial:ℝ)*M^m by positivity) hU hampj hcharj
  apply hprod.trans_eq
  have hqpow : ChartScales.Q n^g * (ChartScales.Q n^(-h/2))^m *
      (ChartScales.Q n^(-(1+h)))^m = ChartScales.Q n^(g-(m:ℝ)*derivativeCost h) := by
    rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_mul_natCast hQ.le,
      ← Real.rpow_add hQ, ← Real.rpow_add hQ]
    congr 1
    unfold derivativeCost
    ring
  have hspow : ChartScales.S n^d * (ChartScales.S n^e)^m = ChartScales.S n^(d+e*(m:ℝ)) := by
    rw [← Real.rpow_mul_natCast hS.le, ← Real.rpow_add hS]
  dsimp [M, U, C]
  rw [mul_pow, mul_pow, mul_pow]
  calc
    _ = (2:ℝ)^m*(m.factorial:ℝ)^2*A*(1+2*H)^m*(K+B)^m *
        (ChartScales.Q n^g*(ChartScales.Q n^(-h/2))^m*(ChartScales.Q n^(-(1+h)))^m) *
        (ChartScales.S n^d*(ChartScales.S n^e)^m) := by ring
    _ = _ := by rw [hqpow,hspow]



/-- The exact native carrier, with genuine base-profile hypotheses and all
polar branches covered, has the printed cost per Cartesian derivative. -/
theorem native_carrier_bound {h a b r0 P B dBase : ℝ}
    (hh : 0 ≤ h) (ha : 0 < a) (hr0 : 0 ≤ r0) (hP : 1 ≤ P) (hB : 1 ≤ B)
    (hdBase : 0 ≤ dBase) (m : ℕ) (g dAmp A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      ∀ (chart : PolarCharts.Index) (center : Plane) (p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P →
      |etaCoordinate (nativeGraph h n w - center)| ≤ r0 →
      ∀ (amp : LiftPoint → ℂ) (F G : Slow → ℝ) (j : ℤ),
      ContDiff ℝ ∞ amp → ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → |(j:ℝ)| ≤ H →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i amp (physicalLift h n w)‖ ≤
        A * ChartScales.Q n^g * ChartScales.S n^dAmp) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G
        (slowMap (PolarCharts.chart a chart) h n w)‖ ≤ B*ChartScales.S n^dBase) →
      ‖iteratedFDeriv ℝ m ((fun y => amp y *
        character ((ChartScales.carrier h n:ℝ)*(j:ℝ))
          (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G y)) ∘
            physicalLift h n) w‖ ≤
      C*ChartScales.Q n^(g-(m:ℝ)*derivativeCost h)*
        ChartScales.S n^(dAmp+(dBase+1)*(m:ℝ)) := by
  obtain ⟨K, hK, hpolar⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  let V := 1+2*r0*ChartScales.Tg
  have hV : 1 ≤ V := by dsimp [V]; nlinarith [ChartScales.Tg_pos]
  obtain ⟨BP, hBP, hphase⟩ := SharpPhysicalPhase.physicalPhase_geometric_bound hh hK hV hP hB hdBase m
  obtain ⟨C, hC, hbound⟩ := carrier_geometric_bound (b := b) hh ha m
    g dAmp (dBase+1) A BP H hA hBP (by linarith) hH
  refine ⟨C,hC,?_⟩
  intro n hn w hw ht chart center p pz x0 hp hpz hx0 hslot amp F G j hamp hF hG hj hab hFb hGb
  have hκ := PolarCharts.chart_contDiff ha chart
  have hκb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (PolarCharts.chart a chart) (scaledRadial n w)‖ ≤ K :=
    fun i hi => hpolar chart i hi _ hw.1
  have hv : |slotTime h n center r0 w| ≤ V*ChartScales.S n := by
    unfold slotTime
    rw [abs_div, abs_of_pos (ChartScales.timeCoefficient_pos h n), div_eq_mul_inv]
    have hnum : |etaCoordinate (nativeGraph h n w-center)+r0| ≤ 2*r0 := by
      have ht := abs_add_le (etaCoordinate (nativeGraph h n w-center)) r0
      rw [abs_of_nonneg hr0] at ht
      linarith
    calc
      _ ≤ (2*r0)*(ChartScales.Tg*ChartScales.S n) :=
        mul_le_mul hnum (ChartScales.timeCoefficient_inv_upper h hh hn)
          (inv_nonneg.mpr (ChartScales.timeCoefficient_pos h n).le) (by positivity)
      _ ≤ _ := by dsimp [V]; nlinarith [ChartScales.S_pos (show 1 ≤ n by omega)]
  exact hbound n hn w hw ht amp
    (liftedPhase (PolarCharts.chart a chart) h n center r0 p pz x0 F G ∘ physicalLift h n) j
    hamp (SharpPhysicalPhase.physicalPhase_smooth hκ h n center r0 p pz x0 hF hG) hj hab
    (hphase _ hκ n hn center r0 p pz x0 hp hpz hx0 F G hF hG w hκb hv hFb hGb)

end NavierStokes.SharpPhysicalCarrier
