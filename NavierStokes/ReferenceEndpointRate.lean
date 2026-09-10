import NavierStokes.ReferenceUniformStocks
import NavierStokes.AppendixJoiningResults

/-! # The literal linear joining-width estimate at the actual held endpoint -/

noncomputable section

namespace NavierStokes.ReferenceEndpointRate

open Set Filter ProfileHistories ReferencePath NaturalProfile NaturalAxisCoefficients
open ReferenceUniformStocks ReferenceUniformJets TransitionRamp ClosedIntervalJetAlgebra StressActivation
open scoped Topology ContDiff

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ}
    (d : AnalyticInputs h j σ P0) (hΛ : 0 < Λ) (hP0 : ContDiff ℝ ∞ P0)
    (hs : NaturalAxisRange.Parameters h j)

/-- The same stock-driven continuation, on the full printed numerical range. -/
def reference (q : Choice d Λ) : StockReference parameterInterval where
  exponent := h
  radius0 := (q.input hΛ).endpoint
  radius0_pos := (q.input hΛ).endpoint_pos
  domain := (q.input hΛ).radialDomain
  profiles := q.profiles hΛ hP0
  log_mem := fun y _ hη => StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη
  f_pos := fun y _ hη => (q.input hΛ).refF_pos q.δ
    (StressActivation.FromReference.log_radius_mem (q.input hΛ) y hη)
    (mul_pos (q.input hΛ).endpoint_pos (Real.exp_pos _)).le
  L_ne_zero := fun η hη => (lt_of_lt_of_le (by norm_num : (0:ℝ)<4879/5000)
    (AppendixJoiningResults.axis_L_lower_bound_window hs.h_pos.le hs.h_le
      ⟨hη.1.le,hη.2.le⟩)).ne'

theorem reference_eq_ofNatural (hs' : NaturalAxisData.SmallParameters h j) (q : Choice d Λ) :
    reference d hΛ hP0 hs q =
      ofNatural q.profile.family hΛ hs' q.δ_pos q.δ_lt hP0 := rfl

theorem reference_radius (q : Choice d Λ) :
    (reference d hΛ hP0 hs q).radius0 = 4/Λ := rfl

theorem reference_finalTime (q : Choice d Λ) :
    (reference d hΛ hP0 hs q).finalTime = Real.log (110/(4/Λ)) := rfl

theorem reference_initialU (q : Choice d Λ) :
    (reference d hΛ hP0 hs q).initialU = fun η => q.profile.family.U (4/Λ,η) := by
  funext η
  exact (q.input hΛ).refU_eq_natural_initial q.δ le_rfl

theorem reference_initialU_error (q : Choice d Λ) (n : ℕ) {η : ℝ} (hη : η ∈ J) :
    |iteratedDeriv n (fun ξ => (reference d hΛ hP0 hs q).initialU ξ - NaturalAxisData.U j ξ) η| ≤
      ReferenceJetBounds.jetConstant d.coefficients 0 n / Λ := by
  rw [reference_initialU]
  have hY : Λ*(4/Λ) = 4 := by field_simp
  rw [naturalU_error_jet d q.profile (by rw [hY]; norm_num) (original_interval_interior hη) n,
    abs_mul, abs_of_pos (one_div_pos.mpr hΛ)]
  have hb := (ReferenceJetBounds.coefficient_jet_bound d.coefficients q.profile.coefficients
    q.profile.norm_ball 0 n (p := (Λ*(4/Λ),η)) (by rw [hY]; norm_num)).2
  convert! mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hΛ.le) using 1
  ring

theorem radius_final_interval {J' : Set ℝ} (R : StockReference J') {t : ℝ}
    (ht : t ≤ R.finalTime) : radius R.radius0 t ∈ Ioc (0:ℝ) 110 := by
  refine ⟨mul_pos R.radius0_pos (Real.exp_pos t),?_⟩
  have he := Real.exp_le_exp.mpr ht
  rw [StockReference.finalTime, Real.exp_log (div_pos (by norm_num) R.radius0_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he R.radius0_pos.le
  simpa only [radius,mul_div_cancel₀ _ R.radius0_pos.ne'] using hm

/-- One stock bound is chosen before every admissible amplitude and reference width. -/
theorem exists_reference_axialStock_bound (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) : ∃ B, 0 ≤ B ∧ ∀ q : Choice d Λ, ∀ n ≤ N,
      ∀ t ≤ (reference d hΛ hP0 hs q).finalTime, ∀ η ∈ J,
      |parameterJet n (reference d hΛ hP0 hs q).axialStock (t,η)| ≤ B := by
  obtain ⟨B,hB,hb⟩ := (uniform_axialFormula d hΛ hP0 hs hσ hscale N
    (by norm_num : (0:ℝ)≤110)).2
  refine ⟨B,hB,?_⟩
  intro q n hn t ht η hη
  let R := reference d hΛ hP0 hs q
  let X := radius R.radius0 t
  have hX := radius_final_interval R ht
  have hm (ξ : ℝ) (hξ : ξ ∈ parameterInterval) : (X,ξ) ∈ R.domain.carrier := R.log_mem t ξ hξ
  have he : (fun ξ => R.axialStock (t,ξ)) =ᶠ[𝓝 η]
      (fun ξ => axialFormula R.profiles h (X,ξ)) := by
    filter_upwards [parameterInterval_open.mem_nhds (original_interval_interior hη)] with ξ hξ
    exact (axialFormula_eq R.profiles h (hm ξ hξ) hX.1).symm
  rw [parameterJet_eq_iteratedDeriv parameterInterval_open (R.axialStock_smooth parameterInterval_open)
    n (original_interval_interior hη), he.iteratedDeriv_eq n]
  have hsl : ∀ ξ ∈ J, ContDiffAt ℝ ∞ (fun ξ => axialFormula R.profiles h (X,ξ)) ξ := by
    intro ξ hξ
    have he' : (fun z => axialFormula R.profiles h (X,z)) =ᶠ[𝓝 ξ]
        (fun z => R.axialStock (t,z)) := by
      filter_upwards [parameterInterval_open.mem_nhds (original_interval_interior hξ)] with z hz
      exact axialFormula_eq R.profiles h (hm z hz) hX.1
    exact (slice_smoothAt (logDomain parameterInterval parameterInterval_open)
      (R.axialStock_smooth parameterInterval_open) ⟨mem_univ _,original_interval_interior hξ⟩).congr_of_eventuallyEq he'
  exact (bound_iff_jets hsl).mp (hb (q,⟨X,hX.1.le,hX.2⟩)) n hn η hη

/-- The endpoint integral has a linear control cost for any actual stock reference. -/
theorem endpoint_error_from_stock {J' : Set ℝ} (hJ : IsOpen J')
    (R : StockReference J') {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g J')
    {T κ w η M I : ℝ} (hT : 0 < T) (hκ : κ ∈ Icc (0:ℝ) 1)
    (hfinal : 0 ≤ R.finalTime) (hη : η ∈ J') (hM : 0 ≤ M) (n : ℕ)
    (hi : |iteratedDeriv n (fun ξ => R.initialU ξ-g ξ) η| ≤ I)
    (hb : ∀ t ∈ Icc (0:ℝ) R.finalTime, |parameterJet n R.axialStock (t,η)| ≤ M) :
    |iteratedDeriv n (fun ξ => R.endpointU T κ w ξ-g ξ) η| ≤ I+M*(T+κ*R.finalTime) := by
  apply jet_transfer n
    (((R.endpointU_smooth hJ T κ w).contDiffAt (hJ.mem_nhds hη)).sub
      (hg.contDiffAt (hJ.mem_nhds hη)))
    (((R.initialU_smooth hJ).contDiffAt (hJ.mem_nhds hη)).sub
      (hg.contDiffAt (hJ.mem_nhds hη)))
  · have he : (fun ξ => (R.endpointU T κ w ξ-g ξ)-(R.initialU ξ-g ξ)) =
        fun ξ => R.axialVelocity T κ w (R.finalTime,ξ)-R.initialU ξ := by
      funext ξ
      simp only [StockReference.endpointU]
      ring
    rw [he]
    exact axialField_jet_error_bound hJ (R.axialStock_smooth hJ) R.initialU
      hT hκ hfinal hη hM n hb
  · exact hi

/-- The joining constant is chosen before amplitude and before all smaller widths.
The natural coefficient constant displayed on the right does not depend on `Λ`. -/
theorem exists_linear_jet_constant (hΛ1 : 1 ≤ Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) : ∃ Cjoin, 0 ≤ Cjoin ∧ ∀ q : Choice d Λ,
      ∀ T, 0 < T → ∀ κ ∈ Icc (0:ℝ) 1, ∀ w₁, 0 ≤ w₁ → ∀ w₂, 0 ≤ w₂ →
      ∀ n ≤ N, ∀ η ∈ J,
      |iteratedDeriv n (fun ξ => (reference d hΛ hP0 hs q).endpointU T κ w₁ ξ-
        NaturalAxisData.U j ξ) η| ≤ ReferenceJetBounds.jetConstant d.coefficients 0 n/Λ +
          Cjoin*(T+κ+w₁+w₂) := by
  obtain ⟨B,hB,hb⟩ := exists_reference_axialStock_bound d hΛ hP0 hs hσ hscale N
  let Y := Real.log (110/(4/Λ))
  refine ⟨B*(1+|Y|), mul_nonneg hB (by positivity),?_⟩
  intro q T hT κ hκ w₁ hw₁ w₂ hw₂ n hn η hη
  let R := reference d hΛ hP0 hs q
  have hR4 : R.radius0 ≤ 4 := by
    change 4/Λ ≤ 4
    exact (div_le_iff₀ hΛ).mpr (by nlinarith)
  have hfinal : 0 ≤ R.finalTime := by
    apply Real.log_nonneg
    exact (le_div_iff₀ R.radius0_pos).mpr (by linarith)
  have hres := endpoint_error_from_stock parameterInterval_open R (uStar_smooth j).contDiffOn (w := w₁)
    hT hκ hfinal (original_interval_interior hη) hB n
    (reference_initialU_error d hΛ hP0 hs q n hη)
    (fun t ht => hb q n hn t ht.2 η hη)
  have hsum : T+κ*Y ≤ (1+|Y|)*(T+κ+w₁+w₂) := by
    have h1 := mul_nonneg (abs_nonneg Y) hT.le
    have h2 := mul_le_mul_of_nonneg_left (le_abs_self Y) hκ.1
    have h3 := mul_nonneg (by positivity : 0 ≤ 1+|Y|) (add_nonneg hw₁ hw₂)
    nlinarith [hκ.1]
  apply hres.trans
  exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hsum hB).trans_eq (by ring))

/-- All orders through `N` share one natural constant chosen before `Λ`, and
one joining constant chosen before amplitude and the transition widths. -/
theorem exists_linear_Ck_constants (hσ : 0 < σ) (N : ℕ) :
    ∃ Cnat, 0 ≤ Cnat ∧ ∀ Λ, ∀ hΛ : 0 < Λ, 1 ≤ Λ →
      AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ →
      ∃ Cjoin, 0 ≤ Cjoin ∧ ∀ q : Choice d Λ,
      ∀ T, 0 < T → ∀ κ ∈ Icc (0:ℝ) 1, ∀ w₁, 0 ≤ w₁ → ∀ w₂, 0 ≤ w₂ →
      ∀ n ≤ N, ∀ η ∈ J,
      |iteratedDeriv n (fun ξ => (reference d hΛ hP0 hs q).endpointU T κ w₁ ξ-
        NaturalAxisData.U j ξ) η| ≤ Cnat/Λ+Cjoin*(T+κ+w₁+w₂) := by
  obtain ⟨Cnat,hCnat,hcn⟩ := finite_majorant
    (fun n => ReferenceJetBounds.jetConstant d.coefficients 0 n) N
  refine ⟨Cnat,zero_le_one.trans hCnat,?_⟩
  intro Λ hΛ hΛ1 hscale
  obtain ⟨Cjoin,hCjoin,hcj⟩ := exists_linear_jet_constant d hΛ hP0 hs hΛ1 hσ hscale N
  refine ⟨Cjoin,hCjoin,?_⟩
  intro q T hT κ hκ w₁ hw₁ w₂ hw₂ n hn η hη
  exact (hcj q T hT κ hκ w₁ hw₁ w₂ hw₂ n hn η hη).trans
    (add_le_add (div_le_div_of_nonneg_right (hcn n hn) hΛ.le) le_rfl)

theorem exists_reference_angularStock_bound (hΛ1 : 1 ≤ Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) : ∃ B, 0 ≤ B ∧ ∀ q : Choice d Λ, ∀ n ≤ N,
      ∀ t ∈ Icc (0:ℝ) (reference d hΛ hP0 hs q).finalTime, ∀ η ∈ J,
      |parameterJet n (reference d hΛ hP0 hs q).angularStock (t,η)| ≤ B := by
  have ha : 0 < 4/Λ := div_pos (by norm_num) hΛ
  have haR : 4/Λ ≤ (110:ℝ) := (div_le_iff₀ hΛ).mpr (by nlinarith)
  obtain ⟨B,hB,hb⟩ := (uniform_reference_quantities d hΛ hP0 hs hσ hscale N ha haR).2.2.1.2
  refine ⟨B,hB,?_⟩
  intro q n hn t ht η hη
  let R := reference d hΛ hP0 hs q
  let X := radius R.radius0 t
  have hX := radius_final_interval R ht.2
  have hXa : 4/Λ ≤ X := by
    have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp ht.1) R.radius0_pos.le
    change R.radius0 ≤ R.radius0*Real.exp t
    simpa only [mul_one] using hm
  rw [parameterJet_eq_iteratedDeriv parameterInterval_open (R.angularStock_smooth parameterInterval_open)
    n (original_interval_interior hη)]
  have hj := (bound_iff_jets (k := N) (B := B) (fun ξ hξ => slice_smoothAt
    (logDomain parameterInterval parameterInterval_open) (R.angularStock_smooth parameterInterval_open)
    (X := t) (η := ξ) ⟨mem_univ _,original_interval_interior hξ⟩)).mp
  exact hj (hb (q,⟨X,hXa,hX.2⟩)) n hn η hη

/-- A uniform stock bound controls every logarithmic endpoint jet, including order zero. -/
theorem logarithmic_error_from_stock {J' : Set ℝ} (hJ : IsOpen J')
    (R : StockReference J') {T κ w₁ w₂ η M : ℝ} (hκ : κ ∈ Icc (0:ℝ) 1)
    (hfinal : 0 ≤ R.finalTime) (hη : η ∈ J') (hM : 0 ≤ M) (n : ℕ)
    (hb : ∀ t ∈ Icc (0:ℝ) R.finalTime, |parameterJet n R.angularStock (t,η)| ≤ M) :
    |iteratedDeriv n (fun ξ => R.logAmplitude T κ w₁ w₂ (R.finalTime,ξ)-R.initialLog ξ) η| ≤
      (M+1)*R.finalTime := by
  rw [StockReference.logAmplitude,logField,integrate_error_jet hJ R.initialLog
    (angularSlope_smooth T κ R.bigTime w₁ w₂ hJ (R.angularStock_smooth hJ)) n R.finalTime hη]
  have hi := integral_norm_bound hfinal (F := fun t =>
    parameterJet n (angularSlope T κ R.bigTime w₁ w₂ R.angularStock) (t,η)) (M := M+1) (by
      intro t ht
      rw [parameterJet_angularSlope hJ (R.angularStock_smooth hJ) T κ R.bigTime w₁ w₂ n hη]
      have hs := step_mem (R.bigTime+w₁) w₂ t
      have hd := damping_mem T hκ t
      have hz := (controlled_product_bound (a := 1-step (R.bigTime+w₁) w₂ t)
        (by constructor <;> linarith [hs.1,hs.2])
        hd.1 hM (hb t ht)).trans (mul_le_of_le_one_left hM hd.2)
      have hf : |if n=0 then (2/5:ℝ)*step (R.bigTime+w₁) w₂ t else 0| ≤ 1 := by
        split_ifs
        · rw [abs_of_nonneg (mul_nonneg (by norm_num) hs.1)]
          linarith [hs.2]
        · norm_num
      exact (abs_sub _ _).trans (add_le_add hz hf))
  simpa only [sub_zero] using hi

/-- The normalized logarithmic endpoint envelope is uniform before amplitude and
all transition widths, without requiring a separately assumed small-control bound. -/
theorem exists_endpointLog_bound (hΛ1 : 1 ≤ Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) : ∃ B, 0 ≤ B ∧ ∀ q : Choice d Λ, ∀ T κ w₁ w₂ : ℝ,
      κ ∈ Icc (0:ℝ) 1 → ∀ n ≤ N, ∀ η ∈ J,
      |iteratedDeriv n ((reference d hΛ hP0 hs q).endpointLog T κ w₁ w₂ q.C) η| ≤ B := by
  obtain ⟨M,hM,hm⟩ := exists_reference_angularStock_bound d hΛ hP0 hs hΛ1 hσ hscale N
  obtain ⟨B,hB,hb⟩ := exists_normalizedReferenceLog_jets d hΛ hσ hscale N
  let Y := Real.log (110/(4/Λ))
  let c := Real.log 220/2
  refine ⟨B+(|c|+(M+1)*|Y|),by positivity,?_⟩
  intro q T κ w₁ w₂ hκ n hn η hη
  let R := reference d hΛ hP0 hs q
  let L := fun ξ => Real.log q.C+R.initialLog ξ
  have hL : ContDiffOn ℝ ∞ L parameterInterval :=
    contDiffOn_const.add (R.initialLog_smooth parameterInterval_open)
  have hLbound : |iteratedDeriv n L η| ≤ B :=
    hb q.C q.C_pos q.profile q.δ q.δ_pos q.δ_lt (4/Λ)
      (div_nonneg (by norm_num) hΛ.le) n hn η hη
  have hR4 : R.radius0 ≤ 4 := by
    change 4/Λ ≤ 4
    exact (div_le_iff₀ hΛ).mpr (by nlinarith)
  have hfinal : 0 ≤ R.finalTime := by
    apply Real.log_nonneg
    exact (le_div_iff₀ R.radius0_pos).mpr (by linarith)
  have herr := logarithmic_error_from_stock parameterInterval_open R
    (T := T) (w₁ := w₁) (w₂ := w₂) hκ hfinal (original_interval_interior hη) hM n
    (fun t ht => hm q n hn t ht η hη)
  apply jet_transfer n
    ((R.endpointLog_smooth parameterInterval_open T κ w₁ w₂ q.C).contDiffAt
      (parameterInterval_open.mem_nhds (original_interval_interior hη)))
    (hL.contDiffAt (parameterInterval_open.mem_nhds (original_interval_interior hη)))
  · have he : (fun ξ => R.endpointLog T κ w₁ w₂ q.C ξ-L ξ) =
        fun ξ => c+(R.logAmplitude T κ w₁ w₂ (R.finalTime,ξ)-R.initialLog ξ) := by
      funext ξ
      dsimp [StockReference.endpointLog,L,c]
      ring
    rw [he]
    have herr' : |iteratedDeriv n (fun ξ => R.logAmplitude T κ w₁ w₂ (R.finalTime,ξ)-R.initialLog ξ) η|
        ≤ (M+1)*|Y| := herr.trans (mul_le_mul_of_nonneg_left (le_abs_self Y) (by positivity))
    by_cases hn0 : n=0
    · subst n
      simp only [iteratedDeriv_zero] at herr' ⊢
      exact (abs_add_le _ _).trans (add_le_add le_rfl herr')
    · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn0)]
      exact herr'.trans (le_add_of_nonneg_left (abs_nonneg c))
  · exact hLbound

/-- The two conclusions of the current `join:scale-envelope` hold together for
one actual stock-driven continuation and one choice of constants in the printed order. -/
theorem exists_entrance_envelope (hσ : 0 < σ) (N : ℕ) :
    ∃ Cnat, 0 ≤ Cnat ∧ ∀ Λ, ∀ hΛ : 0 < Λ, 1 ≤ Λ →
      AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ →
      ∃ B Cjoin, 0 ≤ B ∧ 0 ≤ Cjoin ∧ ∀ q : Choice d Λ,
      ∀ T, 0 < T → ∀ κ ∈ Icc (0:ℝ) 1, ∀ w₁, 0 ≤ w₁ → ∀ w₂, 0 ≤ w₂ →
      ∀ n ≤ N, ∀ η ∈ J,
      |iteratedDeriv n ((reference d hΛ hP0 hs q).endpointLog T κ w₁ w₂ q.C) η| ≤ B ∧
      |iteratedDeriv n (fun ξ => (reference d hΛ hP0 hs q).endpointU T κ w₁ ξ-
        NaturalAxisData.U j ξ) η| ≤ Cnat/Λ+Cjoin*(T+κ+w₁+w₂) := by
  obtain ⟨Cnat,hCnat,hcn⟩ := exists_linear_Ck_constants d hP0 hs hσ N
  refine ⟨Cnat,hCnat,?_⟩
  intro Λ hΛ hΛ1 hscale
  obtain ⟨Cjoin,hCjoin,hcj⟩ := hcn Λ hΛ hΛ1 hscale
  obtain ⟨B,hB,hb⟩ := exists_endpointLog_bound d hΛ hP0 hs hΛ1 hσ hscale N
  exact ⟨B,Cjoin,hB,hCjoin,fun q T hT κ hκ w₁ hw₁ w₂ hw₂ n hn η hη =>
    ⟨hb q T κ w₁ w₂ hκ n hn η hη,hcj q T hT κ hκ w₁ hw₁ w₂ hw₂ n hn η hη⟩⟩

/-- These endpoint functions are exactly the physical fields at `X_i = 110`. -/
theorem endpointU_eq_physical {J' : Set ℝ} (R : StockReference J')
    (hR : R.radius0 < 110) (T κ w η : ℝ) :
    R.endpointU T κ w η = R.physicalU T κ w (110,η) := by
  rw [StockReference.physicalU,ite_eq_right (not_le.mpr hR)]
  rfl

theorem endpointLog_eq_physical {J' : Set ℝ} (R : StockReference J')
    (hR : R.radius0 < 110) (T κ w₁ w₂ : ℝ) {C : ℝ} (hC : 0 < C) (η : ℝ) :
    R.endpointLog T κ w₁ w₂ C η =
      Real.log (C*(Real.sqrt 220*R.physicalF T κ w₁ w₂ (110,η))) := by
  rw [StockReference.physicalF,ite_eq_right (not_le.mpr hR)]
  rw [Real.log_mul hC.ne' (mul_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne' (Real.exp_pos _).ne'),
    Real.log_mul (Real.sqrt_pos.mpr (by norm_num)).ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_sqrt (by norm_num)]
  simp only [StockReference.endpointLog,StockReference.logPoint,StockReference.logTime,
    StockReference.finalTime,add_assoc]

end NavierStokes.ReferenceEndpointRate
