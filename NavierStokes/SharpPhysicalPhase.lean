import NavierStokes.SharpGraphBounds
import NavierStokes.SharpPhaseJetAlgebra

noncomputable section
namespace NavierStokes.SharpPhysicalPhase
open Set Function
open ProblemStatement PhysicalGraphBounds SharpPhaseJetAlgebra
open scoped ContDiff

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

noncomputable def polarMap (κ : Plane → Plane) (n : ℕ) : SpaceTime → Plane :=
  κ ∘ scaledRadial n

noncomputable def slowMap (κ : Plane → Plane) (h : ℝ) (n : ℕ) (w : SpaceTime) : Slow :=
  ((polarMap κ n w).1, liftZT (physicalLift h n w))

theorem slowMap_formula (κ : Plane → Plane) (h : ℝ) (n : ℕ) (w : SpaceTime) :
    slowMap κ h n w = ((κ (scaledRadial n w)).1,
      (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2, (1-w.1)/ChartScales.Q n)) := by
  ext <;> simp [slowMap, polarMap, liftZT, physicalLift, physicalChart,
    chartLinear_apply, Real.rpow_neg_one, div_eq_mul_inv]
  ring

theorem slowMap_eq_slot (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 : ℝ) (w : SpaceTime) :
    slowMap κ h n w =
      (slotMap κ (ChartScales.timeCoefficient h n) center r0 (physicalLift h n w)).1 := by
  rw [slotMap_physical, slowMap_formula]

theorem polarMap_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ) (n : ℕ) :
    ContDiff ℝ ∞ (polarMap κ n) := hκ.comp (scaledRadial n).contDiff

theorem slowMap_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ) (h : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (slowMap κ h n) := by
  have he : slowMap κ h n = fun w => ((κ (scaledRadial n w)).1,
      ((physicalChart h n w).2.2.2, (physicalChart h n w).1)) := rfl
  rw [he]
  exact (hκ.comp (scaledRadial n).contDiff).fst.prodMk
    ((physicalChart_smooth h n).snd.snd.snd.prodMk (physicalChart_smooth h n).fst)

theorem slotTime_smooth (h : ℝ) (n : ℕ) (center : Plane) (r0 : ℝ) :
    ContDiff ℝ ∞ (slotTime h n center r0) := by
  have he : slotTime h n center r0 = fun w : SpaceTime =>
      ChartScales.Q n ^ (-1-h) * w.1 +
        (r0-etaCoordinate center)/ChartScales.timeCoefficient h n := by
    funext w
    exact slotTime_affine h n center r0 w
  rw [he]
  exact (contDiff_const.mul contDiff_fst).add contDiff_const

/-- The axial factor `epsilon⁻¹` cancels the axial chart scaling exactly. -/
theorem axial_scale (h : ℝ) (n : ℕ) :
    (ChartScales.epsilon h n)⁻¹ * ChartScales.Q n ^ (-CoordinateAlgebra.D h) =
      ChartScales.Q n ^ (-(1/2 : ℝ)) := by
  rw [ChartScales.epsilon, ← Real.rpow_neg (ChartScales.Q_pos n).le,
    ← Real.rpow_add (ChartScales.Q_pos n)]
  congr 1
  unfold CoordinateAlgebra.D
  ring

theorem phase_formula (κ : Plane → Plane) (h : ℝ) (n : ℕ)
    (center : Plane) (r0 p pz x0 : ℝ) (F G : Slow → ℝ) (w : SpaceTime) :
    liftedPhase κ h n center r0 p pz x0 F G (physicalLift h n w) =
      p * (polarMap κ n w).2 + pz * ChartScales.Q n ^ (-(1/2 : ℝ)) * w.2 2 +
        x0 * (polarMap κ n w).1 -
      slotTime h n center r0 w * (p * F (slowMap κ h n w) + pz * G (slowMap κ h n w)) := by
  unfold liftedPhase
  rw [comp_apply, PhaseCalculus.phase, slotMap_physical, slowMap_formula]
  simp only [polarMap, comp_apply]
  rw [div_eq_mul_inv]
  have he := axial_scale h n
  rw [show pz * (ChartScales.epsilon h n)⁻¹ * (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * w.2 2) =
      pz * ((ChartScales.epsilon h n)⁻¹ * ChartScales.Q n ^ (-CoordinateAlgebra.D h)) * w.2 2 by ring, he]

private theorem pow_scale {h : ℝ} (hh : 0 ≤ h) (n k : ℕ) :
    (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ k ≤
      (ChartScales.Q n ^ (-(1 + h))) ^ k := by
  apply pow_le_pow_left₀ (Real.rpow_nonneg (ChartScales.Q_pos n).le _)
  exact Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n)
    (by linarith)

private theorem scale_one {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    1 ≤ ChartScales.Q n ^ (-(1+h)) := by
  have he := Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n)
    (ChartScales.Q_le_one n) (show -(1+h) ≤ 0 by linarith)
  simpa only [Real.rpow_zero] using he

theorem polarMap_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K) (n m : ℕ) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k (polarMap κ n) w‖ ≤
      K * (ChartScales.Q n ^ (-(1+h))) ^ k := by
  intro k hk
  apply (norm_jet_comp_linear isOpen_univ hκ.contDiffOn (scaledRadial n)
    (mem_univ _) k).trans
  apply mul_le_mul (hκb k hk) _ (by positivity) hK
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_scaledRadial_le n) k).trans (pow_scale hh n k)

theorem slowMap_positive_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (n m : ℕ) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K) :
    ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k (slowMap κ h n) w‖ ≤
      (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  intro k hk hkm
  have hQ := ChartScales.Q_pos n
  have hK0 : 0 ≤ K := by linarith
  have hp := polarMap_jets hκ hh (by linarith : 0 ≤ K) n m w hκb k hkm
  have hpolar := norm_jet_linear_comp (polarMap_smooth hκ n)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) w k
  have hp' : ‖iteratedFDeriv ℝ k (fun z => (polarMap κ n z).1) w‖ ≤
      K * (ChartScales.Q n ^ (-(1+h))) ^ k := by
    exact hpolar.trans ((mul_le_mul (norm_fstCLM_le ℝ ℝ) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hzt : ‖iteratedFDeriv ℝ k (fun z : SpaceTime =>
      ((physicalChart h n z).2.2.2, (physicalChart h n z).1)) w‖ ≤
      ChartScales.Q n ^ (-1 : ℝ) := by
    let L : ChartPoint →L[ℝ] Plane :=
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ ℝ Plane).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × Plane)))).prod
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × Plane))
    have hL : ‖L‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro x
      change max ‖x.2.2.2‖ ‖x.1‖ ≤ 1 * ‖x‖
      rw [one_mul]
      exact max_le ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
        (le_max_left _ _)
    exact (norm_jet_linear_comp (physicalChart_smooth h n) L w k).trans
      ((mul_le_mul hL (physicalChart_jet_bound hh n w hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  change ‖iteratedFDeriv ℝ k (fun z => ((polarMap κ n z).1,
    ((physicalChart h n z).2.2.2, (physicalChart h n z).1))) w‖ ≤ _
  rw [iteratedFDeriv_pair
    (((polarMap_smooth hκ n).fst.contDiffAt).of_le (nat_le_infty k))
    ((((physicalChart_smooth h n).snd.snd.snd.prodMk
      (physicalChart_smooth h n).fst).contDiffAt).of_le (nat_le_infty k)),
    ContinuousMultilinearMap.opNorm_prod, mul_pow]
  apply max_le
  · apply hp'.trans
    exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hK hk)
      (by positivity)
  · apply hzt.trans
    have h1 : ChartScales.Q n ^ (-1 : ℝ) ≤ ChartScales.Q n ^ (-(1+h)) :=
      Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by linarith)
    apply (h1.trans (by simpa only [pow_one] using pow_le_pow_right₀ (scale_one hh n) hk)).trans
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK)



private theorem norm_jet_add_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f z + g z) w‖ ≤
      ‖iteratedFDeriv ℝ k f w‖ + ‖iteratedFDeriv ℝ k g w‖ := by
  rw [fun_iteratedFDeriv_add_apply (hf.contDiffAt.of_le (nat_le_infty k))
    (hg.contDiffAt.of_le (nat_le_infty k))]
  exact norm_add_le _ _

private theorem norm_jet_sub_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f z - g z) w‖ ≤
      ‖iteratedFDeriv ℝ k f w‖ + ‖iteratedFDeriv ℝ k g w‖ := by
  rw [fun_iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (nat_le_infty k))
    (hg.contDiffAt.of_le (nat_le_infty k))]
  exact norm_sub_le _ _

theorem slotTime_jets {h K V : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V)
    (n : ℕ) (center : Plane) (r0 : ℝ) (w : SpaceTime)
    (hv : |slotTime h n center r0 w| ≤ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (slotTime h n center r0) w‖ ≤
      V * (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  have hQ := ChartScales.Q_pos n
  have hU : 1 ≤ K * ChartScales.Q n ^ (-(1+h)) := one_le_mul_of_one_le_of_one_le hK (scale_one hh n)
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using hv
  | succ k =>
    let L := ChartScales.Q n ^ (-(1+h)) • ContinuousLinearMap.fst ℝ ℝ Space
    have he : slotTime h n center r0 = fun w => L w +
        (r0-etaCoordinate center)/ChartScales.timeCoefficient h n := by
      funext w
      rw [slotTime_affine]
      dsimp [L]
      rw [show -1-h = -(1+h) by ring]
      rfl
    have hL : ‖L‖ ≤ ChartScales.Q n ^ (-(1+h)) := by
      dsimp [L]
      rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hQ.le _) (norm_fstCLM_le _ _)
    rw [he]
    apply ((positive_jet_affine_bound L _ w (by omega)).trans hL).trans
    apply (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK).trans
    apply (show K * ChartScales.Q n ^ (-(1+h)) ≤
        (K * ChartScales.Q n ^ (-(1+h))) ^ (k+1) from by
      simpa only [pow_one] using pow_le_pow_right₀ hU (show 1 ≤ k+1 by omega)).trans
    exact le_mul_of_one_le_left (by positivity) hV

/-- A sharp bound on the actual phase after graph restriction. The pulse
coordinate is differentiated as its exact affine physical function. -/
theorem physicalPhase_positive_jets {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    {h K V B : ℝ} (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V) (hB : 0 ≤ B)
    (n m : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (w : SpaceTime)
    (hκb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k κ (scaledRadial n w)‖ ≤ K)
    (hv : |slotTime h n center r0 w| ≤ V)
    (hFb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k F (slowMap κ h n w)‖ ≤ B)
    (hGb : ∀ k ≤ m, ‖iteratedFDeriv ℝ k G (slowMap κ h n w)‖ ≤ B) :
    ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k
        (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) w‖ ≤
      ((|p|+|x0|)*K + |pz| + (2:ℝ)^m * V * ((|p|+|pz|)*(m.factorial:ℝ)*B)) *
        (K * ChartScales.Q n ^ (-(1+h))) ^ k := by
  let U := K * ChartScales.Q n ^ (-(1+h))
  have hQ := ChartScales.Q_pos n
  have hK0 : 0 ≤ K := by linarith
  have hU : 1 ≤ U := one_le_mul_of_one_le_of_one_le hK (scale_one hh n)
  have hUs : 0 ≤ U := by linarith
  have hslow := slowMap_smooth hκ h n
  have hf := hF.comp hslow
  have hg := hG.comp hslow
  have hpos := slowMap_positive_jets hκ hh hK n m w hκb
  have hfj := composition_geometric hslow hF w m hB hUs hFb hpos
  have hgj := composition_geometric hslow hG w m hB hUs hGb hpos
  let base : SpaceTime → ℝ := fun z => p * F (slowMap κ h n z) + pz * G (slowMap κ h n z)
  have hbase : ContDiff ℝ ∞ base := (contDiff_const.mul hf).add (contDiff_const.mul hg)
  have hbasej : ∀ k ≤ m, ‖iteratedFDeriv ℝ k base w‖ ≤
      ((|p|+|pz|)*(m.factorial:ℝ)*B) * U ^ k := by
    intro k hk
    apply (norm_jet_add_le (contDiff_const.mul hf) (contDiff_const.mul hg) w k).trans
    rw [norm_jet_const_mul hf w p k, norm_jet_const_mul hg w pz k]
    calc
      _ ≤ |p| * ((m.factorial:ℝ)*B*U^k) + |pz| * ((m.factorial:ℝ)*B*U^k) :=
        add_le_add (mul_le_mul_of_nonneg_left (hfj k hk) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hgj k hk) (abs_nonneg _))
      _ = _ := by ring
  have hpolar := polarMap_smooth hκ n
  have hpj := polarMap_jets hκ hh hK0 n m w hκb
  have hproj (L : Plane →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (k : ℕ) (hk : k ≤ m) :
      ‖iteratedFDeriv ℝ k (L ∘ polarMap κ n) w‖ ≤ K * U ^ k := by
    apply (norm_jet_linear_comp hpolar L w k).trans
    apply ((mul_le_mul hL (hpj k hk) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)).trans
    apply mul_le_mul_of_nonneg_left _ hK0
    exact pow_le_pow_left₀ (Real.rpow_nonneg hQ.le _)
      (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK) k
  let polar : SpaceTime → ℝ := fun z => p*(polarMap κ n z).2+x0*(polarMap κ n z).1
  have hpol : ContDiff ℝ ∞ polar := (contDiff_const.mul hpolar.snd).add (contDiff_const.mul hpolar.fst)
  have hpolj (k : ℕ) (hk : k ≤ m) : ‖iteratedFDeriv ℝ k polar w‖ ≤
      ((|p|+|x0|)*K)*U^k := by
    apply (norm_jet_add_le (contDiff_const.mul hpolar.snd) (contDiff_const.mul hpolar.fst) w k).trans
    rw [norm_jet_const_mul hpolar.snd w p k, norm_jet_const_mul hpolar.fst w x0 k]
    calc
      _ ≤ |p| * (K*U^k)+|x0| * (K*U^k) := add_le_add
        (mul_le_mul_of_nonneg_left (hproj _ (norm_sndCLM_le _ _) k hk) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hproj _ (norm_fstCLM_le _ _) k hk) (abs_nonneg _))
      _ = _ := by ring
  let ax : SpaceTime → ℝ := fun z => pz * ChartScales.Q n ^ (-(1/2:ℝ)) * z.2 2
  have hax : ContDiff ℝ ∞ ax := contDiff_const.mul (coordinateProjection 2).contDiff
  have haxj (k : ℕ) (hk : 1 ≤ k) : ‖iteratedFDeriv ℝ k ax w‖ ≤ |pz| * U^k := by
    change ‖iteratedFDeriv ℝ k (fun z => (pz * ChartScales.Q n ^ (-(1/2:ℝ))) * coordinateProjection 2 z) w‖ ≤ _
    rw [norm_jet_const_mul (coordinateProjection 2).contDiff w _ k, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hQ _)]
    have hc : ‖coordinateProjection 2‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
      intro z
      exact (PiLp.norm_apply_le z.2 2).trans (by simpa only [one_mul, Prod.norm_def] using le_max_right ‖z.1‖ ‖z.2‖)
    have hqscale : ChartScales.Q n ^ (-(1/2:ℝ)) ≤ U :=
      (Real.rpow_le_rpow_of_exponent_ge hQ (ChartScales.Q_le_one n) (by linarith)).trans
        (le_mul_of_one_le_left (Real.rpow_nonneg hQ.le _) hK)
    have hqpow : ChartScales.Q n ^ (-(1/2:ℝ)) ≤ U^k :=
      hqscale.trans (by simpa only [pow_one] using pow_le_pow_right₀ hU hk)
    exact ((mul_le_mul_of_nonneg_left ((norm_positive_jet_linear_le (coordinateProjection 2) w hk).trans hc)
      (by positivity)).trans_eq (mul_one _)).trans
      (mul_le_mul_of_nonneg_left hqpow (abs_nonneg _))
  have he : liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n =
      fun z => polar z + ax z - slotTime h n center r0 z * base z := by
    funext z
    rw [comp_apply, phase_formula]
    dsimp [polar, ax, base]
    ring
  intro k hk hkm
  rw [he]
  apply (norm_jet_sub_le (hpol.add hax) ((slotTime_smooth h n center r0).mul hbase) w k).trans
  have ht := product_geometric (slotTime_smooth h n center r0) hbase w k
    (show 0 ≤ V by linarith) (show 0 ≤ (|p|+|pz|)*(m.factorial:ℝ)*B by positivity) hUs
    (fun i _ => slotTime_jets hh hK hV n center r0 w hv i)
    (fun i hi => hbasej i (hi.trans hkm))
  have ht' := ht.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hkm) (show 0≤V by linarith))
      (show 0 ≤ (|p|+|pz|)*(m.factorial:ℝ)*B by positivity)) (pow_nonneg hUs _))
  apply (add_le_add ((norm_jet_add_le hpol hax w k).trans
    (add_le_add (hpolj k hkm) (haxj k hk))) ht').trans_eq
  dsimp [U]
  ring



theorem physicalPhase_smooth {κ : Plane → Plane} (hκ : ContDiff ℝ ∞ κ)
    (h : ℝ) (n : ℕ) (center : Plane) (r0 p pz x0 : ℝ) {F G : Slow → ℝ}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) := by
  have he : liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n =
      fun w => p * (polarMap κ n w).2 + pz * ChartScales.Q n ^ (-(1/2:ℝ)) * w.2 2 +
        x0 * (polarMap κ n w).1 -
      slotTime h n center r0 w * (p * F (slowMap κ h n w) + pz * G (slowMap κ h n w)) := by
    funext w
    exact phase_formula κ h n center r0 p pz x0 F G w
  rw [he]
  have hp := polarMap_smooth hκ n
  have hs := slowMap_smooth hκ h n
  exact (((contDiff_const.mul hp.snd).add (contDiff_const.mul (coordinateProjection 2).contDiff)).add
    (contDiff_const.mul hp.fst)).sub ((slotTime_smooth h n center r0).mul
      ((contDiff_const.mul (hF.comp hs)).add (contDiff_const.mul (hG.comp hs))))

/-- Uniform phase bounds keep all slow factors polynomial in `S`, with no
additional power loss in `Q`. -/
theorem physicalPhase_geometric_bound {h K V P B d : ℝ}
    (hh : 0 ≤ h) (hK : 1 ≤ K) (hV : 1 ≤ V) (hP : 1 ≤ P) (hB : 1 ≤ B)
    (hd : 0 ≤ d) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ κ : Plane → Plane, ContDiff ℝ ∞ κ →
      ∀ n : ℕ, 4 ≤ n → ∀ (center : Plane) (r0 p pz x0 : ℝ),
      |p| ≤ P → |pz| ≤ P → |x0| ≤ P → ∀ F G : Slow → ℝ,
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → ∀ w : SpaceTime,
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i κ (scaledRadial n w)‖ ≤ K) →
      |slotTime h n center r0 w| ≤ V * ChartScales.S n →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i F (slowMap κ h n w)‖ ≤ B * ChartScales.S n ^ d) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i G (slowMap κ h n w)‖ ≤ B * ChartScales.S n ^ d) →
      ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i
        (liftedPhase κ h n center r0 p pz x0 F G ∘ physicalLift h n) w‖ ≤
        (C * ChartScales.S n ^ (d+1) * ChartScales.Q n ^ (-(1+h))) ^ i := by
  let C0 := 2*P*K+P+(2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B)+1
  have hC0 : 1 ≤ C0 := by
    have ht : 0 ≤ 2*P*K+P+(2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B) := by positivity
    dsimp [C0]
    linarith
  refine ⟨C0*K, one_le_mul_of_one_le_of_one_le hC0 hK, ?_⟩
  intro κ hκ n hn center r0 p pz x0 hp hpz hx0 F G hF hG w hκb hv hFb hGb i hi him
  have hS := S_ge_one (show 1 ≤ n by omega)
  have hS0 := ChartScales.S_pos (show 1 ≤ n by omega)
  have hQ := ChartScales.Q_pos n
  have hSd : 1 ≤ ChartScales.S n ^ d := Real.one_le_rpow hS hd
  have hSe : ChartScales.S n ^ (d+1) = ChartScales.S n * ChartScales.S n ^ d := by
    rw [Real.rpow_add hS0, Real.rpow_one, mul_comm]
  have hE : 1 ≤ ChartScales.S n ^ (d+1) := Real.one_le_rpow hS (by linarith)
  have hVS : 1 ≤ V * ChartScales.S n := one_le_mul_of_one_le_of_one_le hV hS
  have hBS : 0 ≤ B * ChartScales.S n ^ d := by positivity
  have hbound := physicalPhase_positive_jets hκ hh hK hVS hBS n m center r0 p pz x0
    hF hG w hκb hv hFb hGb i hi him
  have hcoef : (|p|+|x0|)*K + |pz| + (2:ℝ)^m * (V*ChartScales.S n) *
      ((|p|+|pz|)*(m.factorial:ℝ)*(B*ChartScales.S n^d)) ≤ C0*ChartScales.S n^(d+1) := by
    have hP0 : 0 ≤ P := by linarith
    have hK0 : 0 ≤ K := by linarith
    have hp1 : |p|+|x0| ≤ 2*P := by linarith
    have hp2 : |p|+|pz| ≤ 2*P := by linarith
    calc
      _ ≤ (2*P)*K+P+(2:ℝ)^m*(V*ChartScales.S n)*(2*P*(m.factorial:ℝ)*(B*ChartScales.S n^d)) := by
        gcongr
      _ = (2*P*K+P)+((2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B))*ChartScales.S n^(d+1) := by
        rw [hSe]
        ring
      _ ≤ (2*P*K+P)*ChartScales.S n^(d+1)+
          ((2:ℝ)^m*V*(2*P*(m.factorial:ℝ)*B))*ChartScales.S n^(d+1) :=
        add_le_add (le_mul_of_one_le_right (show 0 ≤ 2*P*K+P by positivity) hE) le_rfl
      _ ≤ _ := by dsimp [C0]; nlinarith [Real.rpow_nonneg hS0.le (d+1)]
  have hmajor : 1 ≤ C0*ChartScales.S n^(d+1) := one_le_mul_of_one_le_of_one_le hC0 hE
  apply hbound.trans
  calc
    _ ≤ (C0*ChartScales.S n^(d+1)) * (K*ChartScales.Q n^(-(1+h)))^i :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (C0*ChartScales.S n^(d+1))^i * (K*ChartScales.Q n^(-(1+h)))^i :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hmajor hi) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end NavierStokes.SharpPhysicalPhase
