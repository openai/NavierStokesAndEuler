import NavierStokes.ActualCurrentParticularBounds
import NavierStokes.SharpCommonGraphJets
import NavierStokes.SharpGeometricModeJets

noncomputable section
namespace NavierStokes.SharpCurrentPhysicalPhase
open Set Function Filter ProblemStatement CorrectionInitialization
open PhysicalGraphBounds PhysicalWaveSum LocalPhysicalCopyBounds
open scoped ContDiff Topology

abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
abbrev Native := ActualParticularBackground.Native

abbrev h : ℝ := ActualPrimary.h

noncomputable def nativeMap (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) : SpaceTime → Native :=
  CurrentPhysicalChartJets.chartMap a c ∘ commonLift h n d

noncomputable def fullMap (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) :
    SpaceTime → ActualPrimary.FullPoint := ActualParticularBackground.nativeToFull ∘ nativeMap a c n d

theorem fullMap_angle (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) (w : SpaceTime) :
    (fullMap a c n d w).2 = (PolarCharts.chart a c (scaledRadial n w)).2 := by
  change (PolarCharts.chart a c (liftXY (commonLift h n d w))).2 = _
  rw [CurrentPhysicalModeGerms.liftXY_common]

theorem slot_axial (l : Label B N0) (a : ℝ) (c : PolarCharts.Index) (n d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.nativeZ (ActualPrimaryBounds.slotLinear l n (fullMap a c n d w)) =
      ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-CoordinateAlgebra.D h) * w.2 2 := by
  change PhysicalParticularWave.ratioPower (ChartScales.Q n)
    (ChartScales.Q (BaseChartJets.cellBand l.2)) (CoordinateAlgebra.D h) *
      (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2 + 0) = _
  rw [add_zero, ← mul_assoc, PhysicalParticularWave.ratioPower_cancel
    (ChartScales.Q_pos n) (ChartScales.Q_pos _)]

theorem phaseLinear_physical (l : Label B N0) (a : ℝ) (c : PolarCharts.Index)
    (n d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.phaseLinear l n (fullMap a c n d w) =
      (ActualPrimary.phases B N0 l.1).phase.p l.2 * (PolarCharts.chart a c (scaledRadial n w)).2 +
      (ActualPrimary.phases B N0 l.1).phase.pz l.2 *
        ChartScales.Q (BaseChartJets.cellBand l.2) ^ (-(1 / 2 : ℝ)) * w.2 2 := by
  simp only [ActualPhaseJetBounds.phaseLinear, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.comp_apply, smul_eq_mul,
    fullMap_angle, slot_axial]
  congr 1
  rw [div_eq_mul_inv, mul_assoc, ← mul_assoc
    (ChartScales.epsilon ActualPrimary.h (BaseChartJets.cellBand l.2))⁻¹]
  change _ * (((ChartScales.epsilon h _)⁻¹ * ChartScales.Q _ ^ (-CoordinateAlgebra.D h)) * _) = _
  rw [SharpPhysicalPhase.axial_scale]
  ring

theorem power_window (l : Label B N0) {n : ℕ} (hn : ActualPrimaryBounds.near l n) (s : ℝ) :
    ChartScales.Q (BaseChartJets.cellBand l.2) ^ s ≤
      ActualSignedGeometry.powerBound (-s) * ChartScales.Q n ^ s := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (ChartScales.Q_pos n) s)).mp
  have he := PhysicalParticularWave.ratioPower_neg_div (ChartScales.Q_pos n)
    (ChartScales.Q_pos (BaseChartJets.cellBand l.2)) (-s)
  simp only [neg_neg] at he
  rw [he]
  exact ActualSignedGeometry.dyadic_ratioPower_le
    (ActualPrimaryBounds.near_distance hn).1 (ActualPrimaryBounds.near_distance hn).2 (-s)


private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem smoothNear_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {g : E → F} {x : E} (hf : SmoothNear f (g x)) (hg : SmoothNear g x) :
    SmoothNear (f ∘ g) x := by
  obtain ⟨V,hV,hgx,hf⟩ := hf
  obtain ⟨U,hU,hx,hg⟩ := hg
  obtain ⟨W,hWV,hW,hxW⟩ := mem_nhds_iff.mp
    ((hg.contDiffAt (hU.mem_nhds hx)).continuousAt.preimage_mem_nhds (hV.mem_nhds hgx))
  refine ⟨U ∩ W,hU.inter hW,⟨hx,hxW⟩,?_⟩
  exact hf.comp (hg.mono inter_subset_left) (fun y hy => hWV hy.2)

theorem nativeMap_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : radialProjection w ≠ 0) : SmoothNear (nativeMap a c n d) w := by
  let U : Set SpaceTime := {w | radialProjection w ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  refine ⟨U,hU,hw,?_⟩
  exact (CurrentPhysicalChartJets.chartMap_smooth ha c).comp_contDiffOn
    ((downLift d).contDiff.comp_contDiffOn (physicalLift_smooth h n))

theorem fullMap_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {w : SpaceTime} (hw : radialProjection w ≠ 0) : SmoothNear (fullMap a c n d) w := by
  obtain ⟨U,hU,hx,hs⟩ := nativeMap_smoothNear ha c n d hw
  exact ⟨U,hU,hx,ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.comp_contDiffOn hs⟩

theorem native_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ c : PolarCharts.Index,
      ∀ f : Native → E, SmoothNear f (nativeMap a c n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (nativeMap a c n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ nativeMap a c n d) w‖ ≤
        C*A*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨M,hM,hm⟩ := CurrentPhysicalChartJets.composition_jets (E := E) (b := b) ha m
  obtain ⟨C,hC,hc⟩ := SharpCommonGraphJets.common_jets (E := E) (b := b)
    ActualPrimary.outgoing.data.h_pos.le ha Δ m
  refine ⟨C*M,one_le_mul_of_one_le_of_one_le hC hM,?_⟩
  intro n hn d hd w hw ht c f hf A hA hfb k hk
  exact (hc n hn d hd w hw ht (f ∘ CurrentPhysicalChartJets.chartMap a c)
    (CurrentPhysicalChartJets.composition_smoothNear ha hf) (M*A) (by positivity)
    (hm c _ (PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hw)
      f hf A hA hfb) k hk).trans_eq (by dsimp [h, ActualPrimary.h]; ring)

theorem full_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ → ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 → ∀ c : PolarCharts.Index,
      ∀ f : ActualPrimary.FullPoint → E, SmoothNear f (fullMap a c n d w) → ∀ A : ℝ, 0 ≤ A →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (fullMap a c n d w)‖ ≤ A) →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (f ∘ fullMap a c n d) w‖ ≤
        C*A*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨C,hC,hc⟩ := native_jets (E := E) (b := b) ha Δ m
  refine ⟨C,hC,?_⟩
  intro n hn d hd w hw ht c f hf A hA hfb k hk
  have he : SmoothNear (f ∘ ActualParticularBackground.nativeToFull) (nativeMap a c n d w) := by
    obtain ⟨U,hU,hx,hs⟩ := hf
    exact ⟨_,hU.preimage ActualParticularBackground.nativeToFull.continuous,hx,
      hs.comp ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.contDiffOn
        (fun _ hy => hy)⟩
  apply hc n hn d hd w hw ht c (f ∘ ActualParticularBackground.nativeToFull) he A hA _ k hk
  intro i hi
  rw [show f ∘ ActualParticularBackground.nativeToFull =
    fun z => f (ActualParticularBackground.nativeToFull z) from rfl,
    StateReindex.norm_iteratedFDeriv_pull]
  exact hfb i hi

noncomputable def remainder (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0)
    (x : ActualPrimary.FullPoint) : ℝ := ActualPhaseJetBounds.nativeRemainder i.1
      ((ActualPrimaryBounds.fullCopy i.1 n i.2 x).1,(ActualPrimaryBounds.fullCopy i.1 n i.2 x).2.2)

theorem remainder_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {x : ActualPrimary.FullPoint} (hx : x ∈ ActualPhaseJetBounds.phaseCell n i) :
    SmoothNear (remainder n i) x := by
  let g : ActualPrimary.FullPoint → PhaseCalculus.Slow × ℝ := fun y =>
    ActualPrimaryBounds.slotLinear i.1 n y +
      ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0)
  have hg : ContDiff ℝ ∞ g := (ActualPrimaryBounds.slotLinear i.1 n).contDiff.add contDiff_const
  have hxg : g x ∈ ActualPhaseJetBounds.jetDomain.carrier i.1 := by
    simpa only [g, ← ActualPrimaryBounds.slotCopy_affine] using ActualPhaseJetBounds.phaseCell_maps hx
  refine ⟨g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1,
    (ActualPhaseJetBounds.jetDomain.isOpen i.1).preimage hg.continuous,hxg,?_⟩
  have hb := (ActualPhaseJetBounds.nativeRemainder_polynomial.smooth i.1).comp
    hg.contDiffOn (fun _ hy => hy)
  change ContDiffOn ℝ ∞ (remainder n i) (g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1)
  apply hb.congr
  intro y _
  dsimp [remainder, Function.comp_def, g]
  rw [← ActualPrimaryBounds.slotCopy_affine]

theorem localPhase_physical (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0)
    (a : ℝ) (c : PolarCharts.Index) (d : ℕ) (w : SpaceTime) :
    ActualPhaseJetBounds.localPhase n i (fullMap a c n d w) =
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n w)).2 +
      ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
        ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ))*w.2 2 +
        ActualPhaseJetBounds.phaseOffset n i) + remainder n i (fullMap a c n d w) := by
  rw [ActualPhaseJetBounds.localPhase_decomposition,phaseLinear_physical]
  dsimp [remainder]
  ring

theorem localPhase_positive_jets {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) w‖ ≤
        C*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
  obtain ⟨K,hK,hpolar⟩ := PolarCharts.chart_finiteJets_uniform ha b m
  obtain ⟨R,hR,p,hr⟩ := ActualPhaseJetBounds.polynomial_copy_bound
    (ActualPhaseJetBounds.nativeRemainder_polynomial (B := B) (N0 := N0)) m
  obtain ⟨D,hD,hd⟩ := full_jets (E := ℝ) (b := b) ha Δ m
  let M := ActualPhaseJetBounds.phaseSize B N0
  let W := ActualSignedGeometry.powerBound (1/2)
  have hM : 1 ≤ M := ActualPhaseJetBounds.one_le_phaseSize
  have hW : 1 ≤ W := ActualSignedGeometry.powerBound_one _
  let C := M*K+M*W+D*R
  have hC : 1 ≤ C := by
    have hMK := one_le_mul_of_one_le_of_one_le hM hK
    have hMW := one_le_mul_of_one_le_of_one_le hM hW
    have hDR := one_le_mul_of_one_le_of_one_le hD hR
    dsimp [C]
    linarith
  refine ⟨C,hC,p,?_⟩
  intro n hn d hd' c i w hw ht hi k hk hkm
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have hSp : 1 ≤ ChartScales.S n^p := one_le_pow₀ hS
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hfull := fullMap_smoothNear ha c n d haxis
  have hrnear := smoothNear_comp (remainder_smoothNear hi) hfull
  have hpolars := (PolarCharts.chart_contDiff ha c).comp (scaledRadial n).contDiff
  have hangle : ‖iteratedFDeriv ℝ k
      (fun y => (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2) w‖ ≤
      M*K*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
    have hangleSmooth : ContDiff ℝ ∞
        (fun y => (PolarCharts.chart a c (scaledRadial n y)).2) := hpolars.snd
    rw [norm_jet_const_mul hangleSmooth w ((ActualPrimary.phases B N0 i.1.1).phase.p i.1.2) k]
    have hp := SharpPhysicalPhase.polarMap_jets (PolarCharts.chart_contDiff ha c)
      ActualPrimary.outgoing.data.h_pos.le (zero_le_one.trans hK) n m w
      (fun j hj => hpolar c j hj _ hw.1) k hkm
    have hs := norm_jet_linear_comp hpolars (ContinuousLinearMap.snd ℝ ℝ ℝ) w k
    have hs' := hs.trans ((mul_le_mul (norm_sndCLM_le ℝ ℝ) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hb := mul_le_mul (ActualPhaseJetBounds.phase_constants_bound i.1).1 hs'
      (norm_nonneg _) (zero_le_one.trans hM)
    apply hb.trans_eq
    rw [← Real.rpow_mul_natCast hQ.le]
    rw [show -(1+ActualPrimary.h)*(k:ℝ) = -(k:ℝ)*(1+h) by dsimp [h]; ring]
    ring
  let L : SpaceTime →L[ℝ] ℝ :=
    ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
      ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ))) • coordinateProjection 2
  have hlin : ‖iteratedFDeriv ℝ k (fun y => L y+ActualPhaseJetBounds.phaseOffset n i) w‖ ≤
      M*W*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
    apply (ActualPhaseJetBounds.norm_positive_jet_affine L _ w hk).trans
    have hL : ‖L‖ ≤ M*ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ)) := by
      dsimp [L]
      rw [norm_smul ((ActualPrimary.phases B N0 i.1.1).phase.pz i.1.2 *
        ChartScales.Q (BaseChartJets.cellBand i.1.2)^(-(1/2:ℝ)) : ℝ) (coordinateProjection 2)]
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _)]
      exact (mul_le_mul (mul_le_mul_of_nonneg_right
        (ActualPhaseJetBounds.phase_constants_bound i.1).2.1 (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _).le)
        ((show ‖coordinateProjection 2‖ ≤ 1 from by
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro v
          exact (PiLp.norm_apply_le v.2 2).trans (by simpa only [one_mul] using norm_snd_le v))) (norm_nonneg _) (mul_nonneg (zero_le_one.trans hM) (Real.rpow_pos_of_pos (ChartScales.Q_pos _) _).le)).trans_eq (mul_one _)
    apply hL.trans
    calc
      _ ≤ M*(W*ChartScales.Q n^(-(1/2:ℝ))) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [neg_neg, W] using power_window i.1 hi.1 (-(1/2))) (zero_le_one.trans hM)
      _ ≤ M*(W*ChartScales.Q n^(-(k:ℝ)*(1+h))) := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hM)
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hW)
        apply Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n)
        have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
        have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
        nlinarith
      _ = _ := by ring
  have hrem := hd n hn d hd' w hw ht c (remainder n i) (remainder_smoothNear hi)
    (R*ChartScales.S n^p) (by positivity) (hr n i _ hi) k hkm
  have he : ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d = fun y =>
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2 +
      (L y + ActualPhaseJetBounds.phaseOffset n i) + remainder n i (fullMap a c n d y) :=
    funext (localPhase_physical n i a c d)
  have hangleSmooth : ContDiffAt ℝ k (fun y =>
      (ActualPrimary.phases B N0 i.1.1).phase.p i.1.2 *
        (PolarCharts.chart a c (scaledRadial n y)).2) w :=
    ((contDiff_const.mul hpolars.snd).contDiffAt).of_le (nat_le_infty k)
  have hlinearSmooth : ContDiffAt ℝ k (fun y => L y + ActualPhaseJetBounds.phaseOffset n i) w :=
    ((L.contDiff.add contDiff_const).contDiffAt).of_le (nat_le_infty k)
  have hremSmooth : ContDiffAt ℝ k (fun y => remainder n i (fullMap a c n d y)) w :=
    hrnear.contDiffAt.of_le (nat_le_infty k)
  rw [he, fun_iteratedFDeriv_add_apply (hangleSmooth.add hlinearSmooth) hremSmooth,
    fun_iteratedFDeriv_add_apply hangleSmooth hlinearSmooth]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  calc
    _ ≤ M*K*ChartScales.Q n^(-(k:ℝ)*(1+h)) + M*W*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        D*(R*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) :=
      add_le_add (add_le_add hangle hlin) hrem
    _ ≤ (M*K*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        (M*W*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) +
        D*(R*ChartScales.S n^p)*ChartScales.Q n^(-(k:ℝ)*(1+h)) := by
      apply add_le_add _ (le_refl _)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity : 0 ≤ M*K) hSp) (by positivity)
      · exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity : 0 ≤ M*W) hSp) (by positivity)
    _ = _ := by dsimp [C]; ring


theorem weightedPhase_positive_jets {a b : ℝ} (ha : 0 < a) (Δ m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ c : PolarCharts.Index, ∀ i : ActualPhaseJetBounds.CopyIndex B N0, ∀ w : SpaceTime,
      scaledRadial n w ∈ annulus a b → |w.1| ≤ 1 →
      fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i →
      ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w‖ ≤
        C*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*SharpPhysicalCarrier.derivativeCost h) := by
  obtain ⟨L,hL,p,hl⟩ := localPhase_positive_jets (B := B) (N0 := N0) (b := b) ha Δ m
  let W := ActualSignedGeometry.powerBound (h/2)
  have hW : 1 ≤ W := ActualSignedGeometry.powerBound_one _
  have hh : 0 ≤ h := ActualPrimary.outgoing.data.h_pos.le
  refine ⟨2*W*L,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by norm_num) hW) hL,p,?_⟩
  intro n hn d hd c i w hw ht hi k hk hkm
  have hQ := ChartScales.Q_pos n
  have hS := PhysicalGraphBounds.S_ge_one (show 1 ≤ n by omega)
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hw)
  have hfull := fullMap_smoothNear ha c n d haxis
  have he := (ActualPhaseJetBounds.weightedPhase_germ hi).comp_tendsto hfull.contDiffAt.continuousAt
  change ‖iteratedFDeriv ℝ k (ActualPhaseJetBounds.weightedPhase i.1 n ∘ fullMap a c n d) w‖ ≤ _
  rw [iteratedFDeriv_eq_of_eventuallyEq he k]
  have hlocal := (ActualPhaseJetBounds.localPhase_smooth hi).comp w hfull.contDiffAt
  change ‖iteratedFDeriv ℝ k (fun y =>
    (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ) •
      (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) y) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hlocal.of_le (nat_le_infty k)),
    norm_smul (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ)
      (iteratedFDeriv ℝ k (ActualPhaseJetBounds.localPhase n i ∘ fullMap a c n d) w),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hcar : (ChartScales.carrier h (BaseChartJets.cellBand i.1.2):ℝ) ≤
      2*W*ChartScales.Q n^(-h/2) := by
    apply (carrier_upper hh _).trans
    have hb := power_window i.1 hi.1 (-h/2)
    have he : -(-h/2) = h/2 := by ring
    rw [he] at hb
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (show (0:ℝ) ≤ 2 by norm_num)
  calc
    _ ≤ (2*W*ChartScales.Q n^(-h/2)) *
        (L*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h))) :=
      mul_le_mul hcar (hl n hn d hd c i w hw ht hi k hk hkm) (norm_nonneg _) (by positivity)
    _ = (2*W*L)*ChartScales.S n^p*ChartScales.Q n^(-h/2-(k:ℝ)*(1+h)) := by
      rw [show (2*W*ChartScales.Q n^(-h/2)) *
          (L*ChartScales.S n^p*ChartScales.Q n^(-(k:ℝ)*(1+h))) =
        (2*W*L)*ChartScales.S n^p*(ChartScales.Q n^(-h/2)*ChartScales.Q n^(-(k:ℝ)*(1+h))) by ring,
        ← Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n)
      have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
      unfold SharpPhysicalCarrier.derivativeCost
      nlinarith

theorem weightedPhase_smoothNear {a : ℝ} (ha : 0 < a) (c : PolarCharts.Index) (n d : ℕ)
    {i : ActualPhaseJetBounds.CopyIndex B N0} {w : SpaceTime} (hw : radialProjection w ≠ 0)
    (hi : fullMap a c n d w ∈ ActualPhaseJetBounds.phaseCell n i) :
    SmoothNear (ActualCurrentCarrierJets.weightedPhase i.1 n ∘ nativeMap a c n d) w := by
  change SmoothNear (ActualPhaseJetBounds.weightedPhase i.1 n ∘ fullMap a c n d) w
  exact smoothNear_comp (ActualCurrentCarrierJets.full_weightedPhase_smoothNear hi)
    (fullMap_smoothNear ha c n d hw)

end NavierStokes.SharpCurrentPhysicalPhase
