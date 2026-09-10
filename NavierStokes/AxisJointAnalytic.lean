import NavierStokes.AxisAnalyticRadialSeries
import NavierStokes.HolomorphicFamilyAnalytic

/-! # Joint real analyticity of the actual evaluated axis profiles

A geometrically convergent radial series takes values in the Banach space of
holomorphic parameter-disk functions. Fixed-contour Cauchy evaluation gives
joint analyticity; termwise real agreement identifies the constructed profile.
-/

noncomputable section

open Set Metric Filter Complex
open scoped Topology
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisWeightEstimates
open NavierStokes.AxisEvaluation NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisJointAnalytic

private theorem ratio_lt_one {R s : ℝ} (hR : 1 ≤ R) (hs : R / 20 < s) :
    R * (1 / 20 / s) < 1 := by
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  calc
    R * (1 / 20 / s) = R / 20 / s := by ring
    _ < 1 := (div_lt_one hs0).mpr hs

private theorem term_bound {R s C : ℝ} (hR : 0 ≤ R) (_hC : 0 ≤ C) (_hs : 0 < s)
    {Y z : ℂ} (hY : ‖Y‖ ≤ R) (n : ℕ)
    (hz : ‖z‖ ≤ C * (1 / 20 / s) ^ n) :
    ‖Y ^ n * z‖ ≤ C * (R * (1 / 20 / s)) ^ n := by
  rw [norm_mul, norm_pow]
  calc
    _ ≤ R ^ n * (C * (1 / 20 / s) ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg Y) hY n) hz (norm_nonneg z) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- The parameter slices of the radial sum are holomorphic on a common strip. -/
theorem radialExtension_analytic_parameter (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    {Y : ℝ} (hY : |Y| ≤ R) :
    AnalyticOnNhd ℂ (radialExtension I ε A Y) (parameterStrip I (ε * (1 - s))) := by
  change AnalyticOnNhd ℂ (fun z : ℂ => ∑' n : ℕ, (Y : ℂ) ^ n * complexCoefficient I ε A n z) _
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hs' : (1 : ℝ) / 20 < s := (div_le_div_of_nonneg_right hR (by norm_num)).trans_lt hs
  have hC : 0 ≤ 2 * ‖A‖ / (1 - s) := by positivity
  have hq := ratio_lt_one hR hs
  have hqn : ‖(R * (1 / 20 / s) : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (zero_le_one.trans hR) (by positivity))]
    exact hq
  have hg : Summable (fun n : ℕ => (2 * ‖A‖ / (1 - s)) * (R * (1 / 20 / s)) ^ n) :=
    (summable_geometric_of_norm_lt_one hqn).mul_left (2 * ‖A‖ / (1 - s))
  have ht (n : ℕ) : DifferentiableOn ℂ
      (fun z : ℂ => (Y : ℂ) ^ n * complexCoefficient I ε A n z)
      (parameterStrip I (ε * (1 - s))) :=
    (complexCoefficient_analytic I hε hs' hs1 A n).differentiableOn.const_mul _
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ parameterStrip I (ε * (1 - s))) :
      ‖(Y : ℂ) ^ n * complexCoefficient I ε A n z‖ ≤
        (2 * ‖A‖ / (1 - s)) * (R * (1 / 20 / s)) ^ n := by
    apply term_bound (by positivity) hC hs0 _ n
      (complexCoefficient_bound I hε hs' hs1 A n hz)
    simpa only [norm_real, Real.norm_eq_abs] using hY
  exact (Complex.differentiableOn_tsum_of_summable_norm hg ht
    (parameterStrip_isOpen I (ε * (1 - s))) hb).analyticOnNhd
      (parameterStrip_isOpen I (ε * (1 - s)))

/-- The constructed complex extension is jointly real analytic on each
parameter disk, with an open radial interval independent of the coefficient vector. -/
theorem radialExtension_joint_disk (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) {σ : ℝ} (hσ : 0 < σ)
    (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s))) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℂ => radialExtension I ε A p.1 p.2)
      (Ioo (-R) R ×ˢ ball c σ) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hs0 : 0 < s := lt_trans (by positivity : 0 < R / 20) hs
  have hs' : (1 : ℝ) / 20 < s := (div_le_div_of_nonneg_right hR (by norm_num)).trans_lt hs
  let a : ℕ → C(Disk c σ, ℂ) := diskCoefficient I hε hs' hs1 A c σ hK
  let V : ℝ → C(Disk c σ, ℂ) := fun Y => ∑' n : ℕ, (Y : ℂ) ^ n • a n
  have hC : 0 ≤ 2 * ‖A‖ / (1 - s) := by positivity
  have hρ : 0 ≤ (1 : ℝ) / 20 / s := by positivity
  have hb (n : ℕ) : ‖a n‖ ≤ (2 * ‖A‖ / (1 - s)) * (1 / 20 / s) ^ n :=
    diskCoefficient_bound I hε hs' hs1 A c σ hK n
  have hVc := geometricSeries_analytic hC hρ hR0 (ratio_lt_one hR hs) hb
  apply HolomorphicFamily.analyticOnNhd_of_disk_family c hσ isOpen_Ioo V (radialExtension I ε A)
  · intro Y hY
    have hYc : (Y : ℂ) ∈ ball 0 R := by
      simpa only [mem_ball_zero_iff, norm_real, Real.norm_eq_abs] using abs_lt.mpr hY
    exact (hVc (Y : ℂ) hYc).restrictScalars.comp (Complex.ofRealCLM.analyticAt Y)
  · intro Y hY
    exact (radialExtension_analytic_parameter I hε hR hs hs1 A (abs_lt.mpr hY).le).differentiableOn.mono
      (ball_subset_closedBall.trans hK)
  · intro Y hY z
    have hsum := geometricSeries_summable hC hρ hR0 (ratio_lt_one hR hs) hb
      (z := (Y : ℂ)) (by simpa only [norm_real, Real.norm_eq_abs] using (abs_lt.mpr hY).le)
    change (ContinuousMap.evalCLM (R := ℂ) z) (∑' n : ℕ, (Y : ℂ) ^ n • a n) = _
    rw [(ContinuousMap.evalCLM (R := ℂ) z).map_tsum hsum]
    rfl

/-- Every genuine axis coefficient vector evaluates to a function analytic
jointly in the two real variables throughout the natural open strip. -/
theorem profile_analyticOnNhd (I : Window) {ε : ℝ} (hε : 0 < ε) (A : AxisSpace I ε) :
    AnalyticOnNhd ℝ (profile I ε A) (strip I 20) := by
  intro p hp
  have hY20 : |p.1| < 20 := abs_lt.mpr hp.1
  obtain ⟨R, hRp, hR20⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 20) hY20)
  have hR : 1 ≤ R := (le_max_left 1 |p.1|).trans hRp.le
  have hYR : |p.1| < R := (le_max_right 1 |p.1|).trans_lt hRp
  obtain ⟨s, hs, hs1⟩ := exists_between (show R / 20 < 1 by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  have hc : (p.2 : ℂ) ∈ parameterStrip I (ε * (1 - s)) := by
    exact ⟨hp.2, by simpa only [ofReal_im, abs_zero] using (half_pos ha)⟩
  obtain ⟨σ, hσ, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parameterStrip_isOpen I (ε * (1 - s))).mem_nhds hc)
  have hj := radialExtension_joint_disk I hε hR hs hs1 A (p.2 : ℂ) hσ hK
  let J : ℝ × ℝ → ℝ × ℂ := fun q => (q.1, (q.2 : ℂ))
  have hJ : AnalyticAt ℝ J p :=
    analyticAt_fst.prod (Complex.ofRealCLM.analyticAt _ |>.comp analyticAt_snd)
  have hpJ : J p ∈ Ioo (-R) R ×ˢ ball (p.2 : ℂ) σ := ⟨abs_lt.mp hYR, mem_ball_self hσ⟩
  have hcomp : AnalyticAt ℝ (fun q : ℝ × ℝ => (radialExtension I ε A q.1 (q.2 : ℂ)).re) p :=
    Complex.reCLM.analyticAt _ |>.comp_of_eq ((hj (J p) hpJ).comp hJ) rfl
  apply hcomp.congr
  filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp] with q hq
  rw [radialExtension_ofReal I hε A (abs_lt.mpr hq.1), ofReal_re]

end NavierStokes.AxisJointAnalytic
