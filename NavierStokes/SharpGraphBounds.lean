import NavierStokes.PhysicalGraphBounds

/-!
# Linear derivative loss for the physical graph

The normalized radial coefficient costs only `Q^(-h κ)`, while a transverse
derivative costs `Q^(-1/2)`. Every positive order `k` of the actual physical
lift therefore costs at most `Q^(-k(1+h))`. Keeping the order in this bound
gives the manuscript's linear, rather than quadratic, graph restriction loss.
-/

noncomputable section

namespace NavierStokes.SharpGraphBounds

open Set Function
open ProblemStatement PhysicalGraphBounds
open scoped ContDiff Topology

private theorem nat_le_infty (k : ℕ) : (k : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

theorem native_time_power_le {h : ℝ} (hh : 0 ≤ h)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.Tg ^ ChartScales.nativeIndex h n ≤
      ChartScales.Q n ^ (-(1 + h)) := by
  calc
    _ ≤ ChartScales.Q n ^ (-1 - h) / ChartScales.S n :=
      (ChartScales.native_power_bounds h hh hn).1
    _ ≤ ChartScales.Q n ^ (-1 - h) := div_le_self
      (Real.rpow_nonneg (ChartScales.Q_pos n).le _) (S_ge_one (by omega))
    _ = _ := by congr 1; ring

theorem native_radial_power_le {h : ℝ} (hh : 0 ≤ h)
    {n : ℕ} (hn : 4 ≤ n) :
    ChartScales.radialCoefficient h n ≤ ChartScales.Q n ^ (-h * ChartScales.kappa) := by
  have hs : ChartScales.S n ^ (-ChartScales.rho) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (S_ge_one (by omega))
      (neg_nonpos.mpr ChartScales.rho_pos.le)
  calc
    _ ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) *
        ChartScales.S n ^ (-ChartScales.rho) :=
      (ChartScales.radialCoefficient_bounds h hh hn).2
    _ ≤ ChartScales.epsilon h n ^ (-ChartScales.kappa) :=
      mul_le_of_le_one_right (Real.rpow_nonneg (ChartScales.epsilon_pos h n).le _) hs
    _ = _ := by
      unfold ChartScales.epsilon
      rw [← Real.rpow_mul (ChartScales.Q_pos n).le]
      congr 1
      ring

theorem nativeGraph_positive_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (nativeGraph h n) p‖ ≤
        C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := compact_jet_bound axisFree_open
    (contDiffOn_radialProfile (ChartScales.radialExponent h)) (isCompact_annulus a b)
    (annulus_axisFree ha) m
  refine ⟨C + ‖timeDirection‖, by linarith [norm_nonneg timeDirection], ?_⟩
  intro n hn p hp ht k hk hkm
  have hq := ChartScales.Q_pos n
  have hq1 := ChartScales.Q_le_one n
  have hC0 : 0 ≤ C := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have haxis := annulus_axisFree ha hp
  have hr : ContDiffAt ℝ k
      (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p :=
    (((contDiffOn_radialProfile (ChartScales.radialExponent h)).contDiffAt
      (axisFree_open.mem_nhds haxis)).comp p (scaledRadial n).contDiff.contDiffAt).of_le
        (nat_le_infty k)
  have he : nativeGraph h n = fun z =>
      ChartScales.radialCoefficient h n •
        (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) z +
      ChartScales.Tg ^ ChartScales.nativeIndex h n • timeProfile z := by
    funext z
    exact nativeGraph_normalized h n z
  rw [he, fun_iteratedFDeriv_add_apply (hr.const_smul _)
    ((timeProfile.contDiff.contDiffAt (x := p)).const_smul _),
    iteratedFDeriv_const_smul_apply' hr,
    iteratedFDeriv_const_smul_apply' timeProfile.contDiff.contDiffAt]
  apply (norm_add_le _ _).trans
  have hrad : ‖ChartScales.radialCoefficient h n •
      iteratedFDeriv ℝ k (radialProfile (ChartScales.radialExponent h) ∘ scaledRadial n) p‖ ≤
      C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
    rw [norm_smul, Real.norm_of_nonneg (ChartScales.radialCoefficient_pos h n).le]
    have hj := norm_jet_comp_linear axisFree_open
      (contDiffOn_radialProfile (ChartScales.radialExponent h)) (scaledRadial n) haxis k
    have hl := pow_le_pow_left₀ (norm_nonneg (scaledRadial n)) (norm_scaledRadial_le n) k
    have hfull := mul_le_mul_of_nonneg_left
      (hj.trans (mul_le_mul (hbound k hkm _ hp) hl (by positivity) hC0))
      (ChartScales.radialCoefficient_pos h n).le
    have hprod := hfull.trans (mul_le_mul_of_nonneg_right
      (native_radial_power_le hh hn) (by positivity))
    have hpow : ChartScales.Q n ^ (-h * ChartScales.kappa) *
        (C * (ChartScales.Q n ^ (-(1 / 2 : ℝ))) ^ k) =
        C * ChartScales.Q n ^ (-h * ChartScales.kappa - (k : ℝ) / 2) := by
      rw [← Real.rpow_mul_natCast hq.le, mul_left_comm, ← Real.rpow_add hq]
      congr 2
      ring
    rw [hpow] at hprod
    apply hprod.trans
    apply mul_le_mul_of_nonneg_left _ hC0
    apply Real.rpow_le_rpow_of_exponent_ge hq hq1
    have hkh : h ≤ (k : ℝ) * h := by nlinarith
    unfold ChartScales.kappa
    nlinarith
  have htime : ‖ChartScales.Tg ^ ChartScales.nativeIndex h n •
      iteratedFDeriv ℝ k timeProfile p‖ ≤
      ‖timeDirection‖ * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg ChartScales.Tg_pos.le _)]
    calc
      _ ≤ ChartScales.Q n ^ (-(1 + h)) * ‖timeDirection‖ :=
        mul_le_mul (native_time_power_le hh hn) (timeProfile_jet_bound p ht k)
          (norm_nonneg _) (Real.rpow_nonneg hq.le _)
      _ ≤ ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) * ‖timeDirection‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hq hq1 (by
          nlinarith)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) +
        ‖timeDirection‖ * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := add_le_add hrad htime
    _ = _ := by ring

theorem physicalLift_positive_jet_bound {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 → ∀ k, 1 ≤ k → k ≤ m →
      ‖iteratedFDeriv ℝ k (physicalLift h n) p‖ ≤
        C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := nativeGraph_positive_jet_bound hh ha m
  refine ⟨C, hC, ?_⟩
  intro n hn p hp ht k hk hkm
  have haxis := scaledRadial_ne_zero (annulus_axisFree ha hp)
  change ‖iteratedFDeriv ℝ k (fun z => (physicalChart h n z, nativeGraph h n z)) p‖ ≤ _
  rw [iteratedFDeriv_pair
    ((physicalChart_smooth h n).contDiffAt.of_le (nat_le_infty k))
    ((contDiffAt_nativeGraph h n haxis).of_le (nat_le_infty k)),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · calc
      _ ≤ ChartScales.Q n ^ (-1 : ℝ) := physicalChart_jet_bound hh n p hk
      _ ≤ ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) :=
        Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) (by
          have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith)
      _ ≤ C * ChartScales.Q n ^ (-(k : ℝ) * (1 + h)) :=
        le_mul_of_one_le_left (Real.rpow_nonneg (ChartScales.Q_pos n).le _) hC
  · exact hbound n hn p hp ht k hk hkm

theorem graphRestriction_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (ha : 0 < a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 4 ≤ n → ∀ p : SpaceTime,
      scaledRadial n p ∈ annulus a b → |p.1| ≤ 1 →
      ∀ F : LiftPoint → E, ContDiff ℝ ∞ F → ∀ B : ℝ, 0 ≤ B →
      (∀ k ≤ m, ‖iteratedFDeriv ℝ k F (physicalLift h n p)‖ ≤ B) →
      ‖iteratedFDeriv ℝ m (F ∘ physicalLift h n) p‖ ≤
        C * B * ChartScales.Q n ^ (-(m : ℝ) * (1 + h)) := by
  obtain ⟨C, hC, hbound⟩ := physicalLift_positive_jet_bound hh ha m
  refine ⟨(m.factorial : ℝ) * C ^ m, mul_pos (by positivity) (pow_pos (by linarith) _), ?_⟩
  intro n hn p hp ht F hF B hB hFB
  let U : Set SpaceTime := {p | radialProjection p ≠ 0}
  have hU : IsOpen U := axisFree_open.preimage radialProjection.continuous
  have hx : p ∈ U := scaledRadial_ne_zero (annulus_axisFree ha hp)
  let D := C * ChartScales.Q n ^ (-(1 + h))
  have hj := norm_iteratedFDerivWithin_comp_le hF.contDiffOn (physicalLift_smooth h n)
    (nat_le_infty m) uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
    (C := B) (D := D)
    (fun k hk => by simpa only [iteratedFDerivWithin_univ] using hFB k hk)
    (fun k hk hkm => by
      rw [iteratedFDerivWithin_of_isOpen k hU hx]
      apply (hbound n hn p hp ht k hk hkm).trans
      dsimp [D]
      rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
      have he : -(1 + h) * (k : ℝ) = -(k : ℝ) * (1 + h) := by ring
      rw [he]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (ChartScales.Q_pos n).le _)
      simpa only [pow_one] using (pow_le_pow_right₀ hC hk))
  rw [iteratedFDerivWithin_of_isOpen m hU hx] at hj
  apply hj.trans_eq
  dsimp [D]
  rw [mul_pow, ← Real.rpow_mul_natCast (ChartScales.Q_pos n).le]
  have he : -(1 + h) * (m : ℝ) = -(m : ℝ) * (1 + h) := by ring
  rw [he]
  ring

end NavierStokes.SharpGraphBounds
