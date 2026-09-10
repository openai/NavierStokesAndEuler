import NavierStokes.SharpCurrentPhysicalPhase

noncomputable section
namespace NavierStokes.SharpCurrentModeJets
open Set Function Filter ProblemStatement CorrectionInitialization
open LocalPhysicalCopyBounds SharpCurrentPhysicalPhase
open scoped ContDiff Topology

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem commonLift_smoothNear (n d : ℕ) {w : SpaceTime}
    (hw : PhysicalGraphBounds.radialProjection w ≠ 0) :
    SmoothNear (PhysicalWaveSum.commonLift h n d) w :=
  ⟨_, PhysicalGraphBounds.axisFree_open.preimage PhysicalGraphBounds.radialProjection.continuous,
    hw, (PhysicalWaveSum.downLift d).contDiff.comp_contDiffOn (PhysicalGraphBounds.physicalLift_smooth h n)⟩

theorem lift_mode_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : PhysicalWaveSum.LiftPoint → E, SmoothNear f (PhysicalWaveSum.commonLift h n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (PhysicalWaveSum.commonLift h n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          f (PhysicalWaveSum.commonLift h n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨K,hK,hk⟩ := SharpCommonGraphJets.common_jets (E := E) (b := b)
    ActualPrimary.outgoing.data.h_pos.le ha Δ m
  obtain ⟨D,hD,p,hp⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) (b := b) ha Δ m
  let M := 1+|(j:ℝ)|
  have hM : 1 ≤ M := le_add_of_nonneg_right (abs_nonneg _)
  let C := (2:ℝ)^m*(m.factorial:ℝ)*M^m*D^m*K*A
  refine ⟨C,by dsimp [C]; positivity,e+p*m,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hw)
  let V := ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h)
  have hV : 0 ≤ V := (Real.rpow_pos_of_pos hQ _).le
  have hDb : 1 ≤ D*ChartScales.S n^p := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hS)
  have hfb' : ∀ r ≤ m, ‖iteratedFDeriv ℝ r (f ∘ PhysicalWaveSum.commonLift h n d) w‖ ≤
      (K*A*ChartScales.Q n^g*ChartScales.S n^e)*V^r := by
    intro r hr
    apply (hk n hn d hd w hw ht f hf _ (by positivity) hfb r hr).trans
    dsimp [V]
    rw [← Real.rpow_mul_natCast hQ.le]
    have hcost : -(SharpPhysicalCarrier.derivativeCost h)*(r:ℝ) ≤ -(r:ℝ)*(1+h) := by
      have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
      have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
      unfold SharpPhysicalCarrier.derivativeCost
      nlinarith
    calc
      _ ≤ K*(A*ChartScales.Q n^g*ChartScales.S n^e)*
          ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h*(r:ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) hcost)
          (by positivity)
      _ = _ := by ring
  have hph : ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w‖ ≤
        (D*ChartScales.S n^p)*V^r := by
    intro r hr hrm
    apply (hp n hn d hd c i w hw ht hi r hr hrm).trans_eq
    dsimp [V]
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 2
    ring
  have hb := SharpGeometricModeJets.modulated (c := (j:ℝ))
    (smoothNear_comp hf (commonLift_smoothNear n d haxis))
    (weightedPhase_smoothNear ha c n d haxis hi) m
    (by positivity) hDb hV hM (by dsimp [M]; linarith [abs_nonneg (j:ℝ)]) hfb' hph
  apply hb.trans_eq
  dsimp [V,C]
  rw [mul_pow, ← pow_mul, pow_add, ← Real.rpow_mul_natCast hQ.le,
    Real.rpow_sub hQ]
  have hpow : ChartScales.Q n^(-SharpPhysicalCarrier.derivativeCost h*(m:ℝ)) =
      (ChartScales.Q n^((m:ℝ)*SharpPhysicalCarrier.derivativeCost h))⁻¹ := by
    rw [← Real.rpow_neg hQ.le]
    congr 1
    ring
  rw [hpow]
  ring

theorem native_mode_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : Native → E, SmoothNear f (nativeMap a c n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (nativeMap a c n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          f (nativeMap a c n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.composition_jets (E := E) (b := b) ha m
  obtain ⟨C,hC,p,hc⟩ := lift_mode_bound (E := E) (B := B) (N0 := N0) (b := b)
    ha Δ m g (M*A) e (by positivity) j
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  apply hc n hn d hd c i w hw ht hi (f ∘ CurrentPhysicalChartJets.chartMap a c)
    (CurrentPhysicalChartJets.composition_smoothNear ha hf)
  intro r hr
  exact (hm c _ (PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw)
    f hf _ (by positivity) hfb r hr).trans_eq (by ring)

theorem rotated_mode_bound {a b : ℝ} (ha : 0 < a) (Δ m : ℕ)
    (g A : ℝ) (e : ℕ) (hA : 0 ≤ A) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ f : Native → HarmonicCalculus.ComplexVector, SmoothNear f (nativeMap a c n d w) →
      (∀ r ≤ m, ‖iteratedFDeriv ℝ r f (nativeMap a c n d w)‖ ≤
        A*ChartScales.Q n^g*ChartScales.S n^e) →
      ‖iteratedFDeriv ℝ m (fun y => PhysicalGraphBounds.character (j:ℝ)
        (ActualCurrentCarrierJets.weightedPhase i.1 n (nativeMap a c n d y)) •
          CurrentPhysicalChartJets.rotated a c f (PhysicalWaveSum.commonLift h n d y)) w‖ ≤
        C*ChartScales.Q n^(g-(m:ℝ)*SharpPhysicalCarrier.derivativeCost h)*ChartScales.S n^p := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.rotated_composition_jets (b := b) ha m
  obtain ⟨C,hC,p,hc⟩ := lift_mode_bound (E := HarmonicCalculus.ComplexVector)
    (B := B) (N0 := N0) (b := b) ha Δ m g (M*A) e (by positivity) j
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd c i w hw ht hi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw
  apply hc n hn d hd c i w hw ht hi (CurrentPhysicalChartJets.rotated a c f)
    (CurrentPhysicalChartJets.rotated_smoothNear ha hx hf)
  intro r hr
  exact (hm c _ hx f hf _ (by positivity) hfb r hr).trans_eq (by ring)


theorem modulated_smoothNear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {a : E → F} {Φ : E → ℝ} {x : E} (ha : SmoothNear a x) (hΦ : SmoothNear Φ x) (c : ℝ) :
    SmoothNear (fun y => PhysicalGraphBounds.character c (Φ y) • a y) x := by
  obtain ⟨U,hU,hxU,ha⟩ := ha
  obtain ⟨V,hV,hxV,hΦ⟩ := hΦ
  exact ⟨U∩V,hU.inter hV,⟨hxU,hxV⟩,
    ((PhysicalGraphBounds.character_smooth c).comp_contDiffOn (hΦ.mono inter_subset_right)).smul
      (ha.mono inter_subset_left)⟩

theorem rotationMap_complex_smul (z : PhysicalGraphBounds.Plane)
    (v : HarmonicCalculus.ComplexVector) (c : ℂ) :
    CartesianCopySource.rotationMap z (c • v) = c • CartesianCopySource.rotationMap z v := by
  ext i
  fin_cases i <;> simp [CartesianCopySource.rotationMap_apply, Pi.smul_apply, Complex.real_smul] <;> ring

theorem rescaled_log_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (g degree A K : ℝ) (p : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 < q →
      q/2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2*q →
      ∀ w : SpaceTime, ∀ f : SpaceTime → E, SmoothNear f w →
      ‖iteratedFDeriv ℝ m f w‖ ≤ A*ChartScales.Q n^g*ChartScales.S n^p →
      ∀ L : E →L[ℝ] F, ‖L‖ ≤ K →
      ‖iteratedFDeriv ℝ m (fun y => ChartScales.Q n^(-degree) • L (f y)) w‖ ≤
        C*q^(g-degree)*(1+|Real.log q|)^P := by
  obtain ⟨D,hD,P,hd⟩ := SharpLogWeights.chart_weight_bound (g-degree) p
  refine ⟨K*A*D,by positivity,P,?_⟩
  intro n hn q hq hlo hhi w f hf hfb L hL
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one hn
  have hLf : ContDiffAt ℝ m (L ∘ f) w :=
    L.contDiff.contDiffAt.comp w (hf.contDiffAt.of_le (nat_le_infty m))
  change ‖iteratedFDeriv ℝ m (fun y => (ChartScales.Q n^(-degree):ℝ) • (L ∘ f) y) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hLf,
    norm_smul (ChartScales.Q n^(-degree):ℝ) (iteratedFDeriv ℝ m (L ∘ f) w),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ _).le,
    L.iteratedFDeriv_comp_left (hf.contDiffAt.of_le (nat_le_infty m)) le_rfl]
  have hj := (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul hL hfb (norm_nonneg _) hK)
  apply (mul_le_mul_of_nonneg_left hj (Real.rpow_pos_of_pos hQ _).le).trans
  have he : ChartScales.Q n^(-degree)*ChartScales.Q n^g = ChartScales.Q n^(g-degree) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    _ = (K*A)*(ChartScales.Q n^(g-degree)*ChartScales.S n^(p:ℝ)) := by
      rw [Real.rpow_natCast, ← he]
      ring
    _ ≤ (K*A)*(D*q^(g-degree)*(1+|Real.log q|)^P) :=
      mul_le_mul_of_nonneg_left (hd n hn q hq hlo hhi) (mul_nonneg hK hA)
    _ = _ := by ring

end NavierStokes.SharpCurrentModeJets
