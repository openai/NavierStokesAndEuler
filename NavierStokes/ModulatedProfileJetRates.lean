import NavierStokes.ModulatedCone

noncomputable section

namespace NavierStokes.ModulatedProfileJetRates

open Set Filter Function ModulatedHistories
open scoped Topology ContDiff BigOperators

/-- One coefficient family and one local inverse branch serve all derivative
orders. Only the asymptotic threshold and constant may depend on the order. -/
structure SmoothRepairFamily (P : FiveProfileMoments.Patch) (b : ℝ)
    (A G : ℝ → ℝ) (d : ℝ → ℝ → Debt) (S : Set ℝ) where
  coefficients : ℝ → ℝ → Coeff
  smooth : ∀ N, ContDiff ℝ ∞ (coefficients N)
  region : ℝ → Set ℝ
  region_open : ∀ N, IsOpen (region N)
  threshold : ℝ
  threshold_ge_one : 1 ≤ threshold
  contains : ∀ N, threshold ≤ N → S ⊆ region N
  solves : ∀ N eta, eta ∈ region N →
    FiveProfileMoments.physicalMoments P b (A eta) (G eta) (coefficients N eta) = d N eta
  positive : ∀ N eta, eta ∈ region N → ∀ X, 0 < X →
    0 < FiveProfileMoments.physicalE P b (A eta) (coefficients N eta) X
  rates : ∀ q : ℕ, ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N →
    JetBounds.FiniteJetBound q (coefficients N) S (C / N)

/-- Finite-jet estimates for composition with a single fixed smooth solver.
The solver is chosen before the derivative order, frequency, and constant. -/
theorem fixed_solver_all_rates {g : Coeff → Coeff} {r C : ℝ}
    (hr : 0 < r) (hC : 0 < C) (hg : ContDiff ℝ ∞ g)
    (hvalue : ∀ z ∈ Metric.ball (0 : Coeff) r, ‖g z‖ ≤ C * ‖z‖)
    {S : Set ℝ} (v : ℝ → ℝ → Coeff) (hv : ∀ N, ContDiff ℝ ∞ (v N))
    (hvr : ∀ q : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
      JetBounds.FiniteJetBound q (v N) S (D / N)) :
    ∀ q : ℕ, ∃ Nq K : ℝ, 1 ≤ Nq ∧ 0 < K ∧ ∀ N : ℝ, Nq ≤ N →
      JetBounds.FiniteJetBound q (g ∘ v N) S (K / N) := by
  intro q
  obtain ⟨D, hD, hvb⟩ := hvr q
  obtain ⟨J, hJ, hj⟩ := smooth_solver_linear_jets hr hC hg.contDiffOn hvalue q
  let delta : ℝ := min 1 (r / 2)
  have hd : 0 < delta := lt_min zero_lt_one (by positivity)
  refine ⟨max 1 (D / delta), J * D, le_max_left _ _, mul_pos hJ hD, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have he : D / N ≤ delta := by
    apply (div_le_iff₀ hNp).mpr
    have ht := (div_le_iff₀ hd).mp ((le_max_right _ _).trans hN)
    nlinarith
  intro k hk eta heta
  have hb := hj (v N) (hv N) (D / N) eta (div_pos hD hNp) he
    (fun i hi => hvb N hN1 i hi eta heta) k hk
  convert hb using 1
  ring

theorem exists_smooth_repair_family (P : FiveProfileMoments.Patch) (b : ℝ)
    (hb : FiveProfileMoments.GoodExponent b) (S : Set ℝ) (hS : IsCompact S)
    (A G : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G)
    (hApos : ∀ eta, 0 < A eta) (d : ℝ → ℝ → Debt)
    (hd : ∀ N, ContDiff ℝ ∞ (d N))
    (hdr : ∀ q : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
      JetBounds.FiniteJetBound q (d N) S (D / N)) :
    Nonempty (SmoothRepairFamily P b A G d S) := by
  obtain ⟨g, r, C0, hr, hC0, hg, _, hbranch⟩ := FiveProfileMoments.exists_normalized_repair P b hb
  obtain ⟨gext, hgext, hext⟩ := smooth_extension_ball hr hg
  let v : ℝ → ℝ → Coeff := fun N eta => FiveProfileMoments.normalizedDebt (A eta) (G eta) (d N eta)
  have hv : ∀ N, ContDiff ℝ ∞ (v N) := fun N =>
    FiveProfileMoments.normalizedDebt_contDiff hA hG (hd N) (fun eta => (hApos eta).ne')
  have hvr : ∀ q : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
      JetBounds.FiniteJetBound q (v N) S (D / N) := by
    intro q
    obtain ⟨D, hD, hdb⟩ := hdr q
    obtain ⟨B0, hB0, hnormal⟩ := FiveProfileMoments.compact_normalizedDebt_jets
      S hS hA hG (fun eta => (hApos eta).ne') q
    refine ⟨B0 * D, mul_pos hB0 hD, ?_⟩
    intro N hN
    convert hnormal (d N) (hd N) (D / N) (div_nonneg hD.le (zero_lt_one.trans_le hN).le)
      (hdb N hN) using 1
    ring
  have hvalue : ∀ z ∈ Metric.ball (0 : Coeff) (r / 2), ‖gext z‖ ≤ C0 * ‖z‖ := by
    intro z hz
    rw [hext hz]
    exact (hbranch z ((Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) hz)).2.1
  obtain ⟨D0, hD0, hv0⟩ := hvr 0
  let N0 := max 1 (4 * D0 / r)
  let V : ℝ → Set ℝ := fun N => v N ⁻¹' Metric.ball 0 (r / 2)
  have hSV : ∀ N, N0 ≤ N → S ⊆ V N := by
    intro N hN eta heta
    have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hNp : 0 < N := zero_lt_one.trans_le hN1
    have hsmall : D0 / N ≤ r / 4 := by
      apply (div_le_iff₀ hNp).mpr
      have he := (div_le_iff₀ hr).mp ((le_max_right _ _).trans hN)
      nlinarith
    change ‖v N eta - 0‖ < r / 2
    rw [sub_zero]
    exact ((hv0 N hN1).norm_le heta).trans_lt (hsmall.trans_lt (by linarith))
  refine ⟨⟨fun N => gext ∘ v N, fun N => hgext.comp (hv N), V,
    fun N => Metric.isOpen_ball.preimage (hv N).continuous, N0, le_max_left _ _, hSV,
    ?_, ?_, fixed_solver_all_rates (by positivity : 0 < r / 2) hC0 hgext hvalue v hv hvr⟩⟩
  · intro N eta heta
    have hlocal := hbranch (v N eta) ((Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) heta)
    change FiveProfileMoments.physicalMoments P b (A eta) (G eta) (gext (v N eta)) = _
    rw [hext heta, FiveProfileMoments.physicalMoments_eq P b (A eta) (G eta) (hApos eta).ne', hlocal.1]
    exact FiveProfileMoments.physical_normalized_debt (A eta) (G eta) (hApos eta).ne' (d N eta)
  · intro N eta heta X hX
    have hlocal := hbranch (v N eta) ((Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) heta)
    change 0 < A eta * (X ^ b + FiveProfileMoments.e P (gext (v N eta)) X)
    rw [hext heta]
    exact mul_pos (hApos eta) (hlocal.2.2.2 X hX)

variable {a m p₁ p₂ : Point → ℝ} {K B : Set Point}

/-- Applied to the actual integral debt, this selects one repaired-profile
sequence with all fixed parameter derivative rates. -/
theorem exists_actual_repair_family_all_jets (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (P : FiveProfileMoments.Patch) (b : ℝ) (hb : FiveProfileMoments.GoodExponent b)
    (S : Set ℝ) (hS : IsCompact S) (A G : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ eta, 0 < A eta) :
    Nonempty (SmoothRepairFamily P b A G (repairDebt W r f E U) S) := by
  apply exists_smooth_repair_family P b hb S hS A G hA hG hApos (repairDebt W r f E U)
    (fun N => (historyDifference_smooth W r f E U ha hm hp₂ hf hE hU N W.right).neg)
  intro q
  obtain ⟨D, hD, hdb⟩ := historyDifference_jets W r f E U ha hm hp₂ hf hE hU S hS q
  refine ⟨D, hD, ?_⟩
  intro N hN j hj eta heta
  change ‖iteratedFDeriv ℝ j (-(historyDifference W r f E U N W.right)) eta‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hdb N hN W.right j hj eta heta

theorem localized_profile_eta_rates (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (S : Set ℝ) (hS : IsCompact S) (q : ℕ) :
    ∃ CF CU : ℝ, 0 ≤ CF ∧ 0 ≤ CU ∧ ∀ N : ℝ, 1 ≤ N → ∀ X eta : ℝ, eta ∈ S →
      |iteratedDeriv q (fun e => localizedF W r f N (X, e)) eta -
        iteratedDeriv q (fun e => f (X, e)) eta| ≤ CF / N ∧
      |iteratedDeriv q (fun e => localizedU W r E U N (X, e)) eta -
        iteratedDeriv q (fun e => U (X, e)) eta| ≤ CU / N := by
  obtain ⟨CF, _, hCF, _, hbF⟩ := ParametricModulation.realized_profiles_uniform_eta_jets
    r f U ha hm hp₂ hf hU (Icc W.left W.right) S isCompact_Icc hS q
  obtain ⟨_, CU, _, hCU, hbU⟩ := ParametricModulation.realized_profiles_uniform_eta_jets
    r E U ha hm hp₂ hE hU (Icc W.left W.right) S isCompact_Icc hS q
  refine ⟨CF, CU, hCF, hCU, ?_⟩
  intro N hN X eta heta
  by_cases hX : X ∈ Ioc W.left W.right
  · have heF : (fun e => localizedF W r f N (X, e)) = ParametricModulation.realizedE r f N X := by
      funext e
      simp only [localizedF, splice, hX, ite_true, rawF]
    have heU : (fun e => localizedU W r E U N (X, e)) = ParametricModulation.realizedU r E U N X := by
      funext e
      simp only [localizedU, splice, hX, ite_true, rawU]
    rw [heF, heU]
    exact ⟨(hbF N hN X ⟨hX.1.le, hX.2⟩ eta heta).1, (hbU N hN X ⟨hX.1.le, hX.2⟩ eta heta).2⟩
  · have heF : (fun e => localizedF W r f N (X, e)) = (fun e => f (X, e)) := by
      funext e
      simp only [localizedF, splice, hX, ite_false]
    have heU : (fun e => localizedU W r E U N (X, e)) = (fun e => U (X, e)) := by
      funext e
      simp only [localizedU, splice, hX, ite_false]
    rw [heF, heU]
    simpa only [sub_self, abs_zero] using
      And.intro (div_nonneg hCF (zero_lt_one.trans_le hN).le) (div_nonneg hCU (zero_lt_one.trans_le hN).le)

theorem localized_profile_eta_smooth (W : Window)
    (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (N X : ℝ) :
    ContDiff ℝ ∞ (fun e => localizedF W r f N (X, e)) ∧
      ContDiff ℝ ∞ (fun e => localizedU W r E U N (X, e)) := by
  have hbase : ContDiff ℝ ∞ (fun e : ℝ => (X, e)) := contDiff_const.prodMk contDiff_id
  by_cases hX : X ∈ Ioc W.left W.right
  · have heF : (fun e => localizedF W r f N (X, e)) = fun e =>
        f (X, e) * Real.exp (r.angularPrimitive ((X, e), N * Real.log X) / N) := by
      funext e
      simp only [localizedF, splice, hX, ite_true, rawF, ParametricModulation.realizedE,
        RadialModulation.modulatedE, RadialModulation.phasePoint, ParametricModulation.asRadialPrimitive]
    have heU : (fun e => localizedU W r E U N (X, e)) = fun e =>
        U (X, e) + r.axialPrimitive E ((X, e), N * Real.log X) / N := by
      funext e
      simp only [localizedU, splice, hX, ite_true, rawU, ParametricModulation.realizedU,
        RadialModulation.modulatedU, RadialModulation.phasePoint, ParametricModulation.asRadialPrimitive]
    rw [heF, heU]
    have hp := r.primitives_smooth E ha hm hp₂ hE
    have hz : ContDiff ℝ ∞ (fun e : ℝ => ((X, e), N * Real.log X)) := hbase.prodMk contDiff_const
    exact ⟨(hf.comp hbase).mul (((hp.1.comp hz).div_const N).exp),
      (hU.comp hbase).add ((hp.2.comp hz).div_const N)⟩
  · have heF : (fun e => localizedF W r f N (X, e)) = fun e => f (X, e) := by
      funext e
      simp only [localizedF, splice, hX, ite_false]
    have heU : (fun e => localizedU W r E U N (X, e)) = fun e => U (X, e) := by
      funext e
      simp only [localizedU, splice, hX, ite_false]
    rw [heF, heU]
    exact ⟨hf.comp hbase, hU.comp hbase⟩

/-- Every fixed parameter derivative of the actual repaired profiles has
the same inverse-frequency rate, for one previously selected repair family. -/
theorem SmoothRepairFamily.profile_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {P : FiveProfileMoments.Patch} {b : ℝ} {A G : ℝ → ℝ} {d : ℝ → ℝ → Debt} {S : Set ℝ}
    (H : SmoothRepairFamily P b A G d S) (hS : IsCompact S) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N → ∀ X eta : ℝ, eta ∈ S →
      |iteratedDeriv q (fun e => applyRepairF P A (H.coefficients N) (localizedF W r f N) (X, e)) eta -
        iteratedDeriv q (fun e => f (X, e)) eta| ≤ C / N ∧
      |iteratedDeriv q (fun e => applyRepairU P A (H.coefficients N) (localizedU W r E U N) (X, e)) eta -
        iteratedDeriv q (fun e => U (X, e)) eta| ≤ C / N := by
  obtain ⟨Nq, Cc, hNq, hCc, hcb⟩ := H.rates q
  obtain ⟨CF, CU, hCF, hCU, hmod⟩ := localized_profile_eta_rates W r f E U ha hm hp₂ hf hE hU S hS q
  obtain ⟨Ce, hCe, hedit⟩ := normalized_edits_eta_bound P S hS A hA q
  refine ⟨Nq, 1 + CF + CU + Ce * Cc, hNq, by positivity, ?_⟩
  intro N hN X eta heta
  have hN1 := hNq.trans hN
  have hNp := zero_lt_one.trans_le hN1
  have hmodb := hmod N hN1 X eta heta
  have heditb := hedit (H.coefficients N) (H.smooth N) (Cc / N) (div_nonneg hCc.le hNp.le)
    (hcb N hN) eta heta q le_rfl X
  have hs := localized_profile_eta_smooth W r f E U ha hm hp₂ hf hE hU N X
  have heF : ContDiff ℝ ∞ (fun e => editF P A (H.coefficients N) (X, e)) :=
    (editF_contDiff P A (H.coefficients N) hA (H.smooth N)).comp (contDiff_const.prodMk contDiff_id)
  have heU : ContDiff ℝ ∞ (fun e => editU P A (H.coefficients N) (X, e)) :=
    (editU_contDiff P A (H.coefficients N) hA (H.smooth N)).comp (contDiff_const.prodMk contDiff_id)
  have horder : (q : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  constructor
  · change |iteratedDeriv q (fun e => localizedF W r f N (X, e) + editF P A (H.coefficients N) (X, e)) eta - _| ≤ _
    rw [iteratedDeriv_fun_add (hs.1.of_le horder).contDiffAt (heF.of_le horder).contDiffAt]
    calc
      _ = |(iteratedDeriv q (fun e => localizedF W r f N (X, e)) eta -
          iteratedDeriv q (fun e => f (X, e)) eta) + iteratedDeriv q (fun e => editF P A (H.coefficients N) (X, e)) eta| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hmodb.1 heditb.1).trans (by
        calc
          CF / N + Ce * (Cc / N) = (CF + Ce * Cc) / N := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hNp.le))
  · change |iteratedDeriv q (fun e => localizedU W r E U N (X, e) + editU P A (H.coefficients N) (X, e)) eta - _| ≤ _
    rw [iteratedDeriv_fun_add (hs.2.of_le horder).contDiffAt (heU.of_le horder).contDiffAt]
    calc
      _ = |(iteratedDeriv q (fun e => localizedU W r E U N (X, e)) eta -
          iteratedDeriv q (fun e => U (X, e)) eta) + iteratedDeriv q (fun e => editU P A (H.coefficients N) (X, e)) eta| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hmodb.2 heditb.2).trans (by
        calc
          CU / N + Ce * (Cc / N) = (CU + Ce * Cc) / N := by ring
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hNp.le))

/-- All five actual integral histories share that same repaired family and
the same inverse-frequency rate, uniformly in every upper radial endpoint. -/
theorem SmoothRepairFamily.history_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {P : FiveProfileMoments.Patch} (hWP : W.right < P.left) {b : ℝ} {A G : ℝ → ℝ}
    {d : ℝ → ℝ → Debt} {S : Set ℝ} (H : SmoothRepairFamily P b A G d S)
    (hS : IsCompact S) (hA : ContDiff ℝ ∞ A) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N → ∀ X : ℝ, 0 ≤ X →
      JetBounds.FiniteJetBound q (fun eta =>
        axisHistory (applyRepairF P A (H.coefficients N) (localizedF W r f N))
          (applyRepairU P A (H.coefficients N) (localizedU W r E U N)) (X, eta) - axisHistory f U (X, eta))
        S (C / N) := by
  obtain ⟨Nc, Cc, hNc, hCc, hcb⟩ := H.rates q
  obtain ⟨delta, C1, C2, hd, hC1, hC2, hb⟩ := repaired_axisHistory_jets
    W r f E U ha hm hp₂ hf hE hU P hWP A hA S hS q
  refine ⟨max Nc (Cc / delta), C1 + C2 * Cc, hNc.trans (le_max_left _ _), by positivity, ?_⟩
  intro N hN X hX
  have hnc : Nc ≤ N := (le_max_left _ _).trans hN
  have hN1 := hNc.trans hnc
  have hNp := zero_lt_one.trans_le hN1
  have he : Cc / N ≤ delta := by
    apply (div_le_iff₀ hNp).mpr
    have ht := (div_le_iff₀ hd).mp ((le_max_right _ _).trans hN)
    nlinarith
  convert hb N hN1 (H.coefficients N) (H.smooth N) (Cc / N)
    (div_nonneg hCc.le hNp.le) he (hcb N hnc) X hX using 1
  ring

/-- The parameter estimates apply to the physical angular field, axial field,
and all five profile rows (including pressure) of the same repaired profiles. -/
theorem SmoothRepairFamily.repaired_profiles_eta_rates
    (W : Window) (r : ParametricModulation.TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    {patch : FiveProfileMoments.Patch} (hgap : W.right < patch.left)
    {b : ℝ} {A G : ℝ → ℝ} {d : ℝ → ℝ → Debt} {S : Set ℝ}
    (H : SmoothRepairFamily patch b A G d S) (hS : IsCompact S) (hA : ContDiff ℝ ∞ A)
    {D D' : ProfileHistories.RadialDomain}
    (R : ℝ → ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    (hRf : ∀ N, (R N).f = applyRepairF patch A (H.coefficients N) (localizedF W r f N))
    (hRU : ∀ N, (R N).U = applyRepairU patch A (H.coefficients N) (localizedU W r E U N))
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ N, (R N).pressure0 = Q.pressure0)
    (Xmax : ℝ) (q : ℕ) :
    ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ N : ℝ, Nq ≤ N →
      (∀ X eta : ℝ, X ≤ Xmax → eta ∈ S →
        |iteratedDeriv q (fun e => (R N).E (X, e)) eta -
          iteratedDeriv q (fun e => Q.E (X, e)) eta| ≤ C / N ∧
        |iteratedDeriv q (fun e => (R N).U (X, e)) eta -
          iteratedDeriv q (fun e => Q.U (X, e)) eta| ≤ C / N) ∧
      (∀ X : ℝ, 0 ≤ X → JetBounds.FiniteJetBound q
        (fun eta => profileRows (R N) (X, eta) - profileRows Q (X, eta)) S (C / N)) := by
  obtain ⟨Np, Cp, hNp, hCp, hp⟩ := H.profile_eta_rates W r f E U ha hm hp₂ hf hE hU hS hA q
  obtain ⟨Nh, Ch, hNh, hCh, hh⟩ := H.history_eta_rates W r f E U ha hm hp₂ hf hE hU hgap hS hA q
  let C := (1 + Real.sqrt (2 * Xmax)) * Cp + Ch
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max Np Nh, C, hNp.trans (le_max_left _ _), hC, ?_⟩
  intro N hN
  have hnp := (le_max_left _ _).trans hN
  have hnh := (le_max_right _ _).trans hN
  have hNpos := zero_lt_one.trans_le (hNp.trans hnp)
  have hCpC : Cp ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (2 * Xmax)]
  have hChC : Ch ≤ C := by dsimp [C]; nlinarith [Real.sqrt_nonneg (2 * Xmax)]
  constructor
  · intro X eta hX heta
    have hb := hp N hnp X eta heta
    constructor
    · simp only [ProfileHistories.Profiles.E, hRf N, hQf,
        iteratedDeriv_const_mul_field, ← mul_sub, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg (2 * X))]
      calc
        _ ≤ Real.sqrt (2 * X) * (Cp / N) := mul_le_mul_of_nonneg_left hb.1 (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (2 * Xmax) * (Cp / N) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (div_nonneg hCp.le hNpos.le)
        _ = (Real.sqrt (2 * Xmax) * Cp) / N := by ring
        _ ≤ C / N := div_le_div_of_nonneg_right (by dsimp [C]; nlinarith) hNpos.le
    · rw [hRU N, hQU]
      exact hb.2.trans (div_le_div_of_nonneg_right hCpC hNpos.le)
  · intro X hX
    have heq : (fun eta => profileRows (R N) (X, eta) - profileRows Q (X, eta)) =
        (fun eta => axisHistory (applyRepairF patch A (H.coefficients N) (localizedF W r f N))
          (applyRepairU patch A (H.coefficients N) (localizedU W r E U N)) (X, eta) -
          axisHistory f U (X, eta)) := by
      funext eta
      rw [profileRows_sub (R N) Q (hP0 N), hRf N, hRU N, hQf, hQU]
    rw [heq]
    intro eta heta j hj
    exact (hh N hnh X hX eta heta j hj).trans (div_le_div_of_nonneg_right hChC hNpos.le)

open ProfileHistories (RadialDomain Profiles)
open ParametricModulation ModulatedCone ModulatedCone.Repaired

/-- One actual smooth repaired family satisfies the true cone and exact exterior
restoration for all sufficiently large integer frequencies; every fixed parameter
jet of this same family has the inverse-frequency bound. -/
theorem exists_with_moment_repair_all_jets {D D' : RadialDomain}
    (W : ModulatedHistories.Window) (r : TrueConeRealization a m p₁ p₂ K B) (f E U : Field)
    (hK : IsCompact K) (hKW : ∀ p ∈ K, p.1 ∈ Icc W.left W.right)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hf : ContDiff ℝ ∞ f) (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ K, 0 < a p)
    (S : Set Point) (hS : IsCompact S) (hSW : ∀ p ∈ S, W.right ≤ p.1)
    (haNom : ∀ p ∈ K ∪ S, a p = angularShear E p)
    (hbNom : ∀ p ∈ K ∪ S, a p * m p = signedAxialShear E U p)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (hScone : ∀ p ∈ S, TrueConeLoop.InTrueCone (p₁ p) (p₂ p) (a p) (a p * m p))
    (P : ℝ → Profiles D) (Q : Profiles D')
    (hPf : ∀ n, (P n).f = ModulatedHistories.localizedF W r f n)
    (hPU : ∀ n, (P n).U = ModulatedHistories.localizedU W r E U n)
    (hQf : Q.f = f) (hQU : Q.U = U) (hP0 : ∀ n, (P n).pressure0 = Q.pressure0)
    (J : Set ℝ) (hJ : IsCompact J) (hTJ : ∀ p ∈ K ∪ S, p.2 ∈ J)
    (hTD : K ∪ S ⊆ D.carrier) (hTD' : K ∪ S ⊆ D'.carrier)
    (h : ℝ) (hL : ∀ p ∈ K ∪ S, NaturalAxisData.L h p.2 ≠ 0)
    (hpos : ∀ p ∈ K ∪ S, 0 < Q.f p)
    (hstock₁ : ∀ p ∈ K ∪ S, p₁ p = ActivationStocks.profileStockOne Q h p)
    (hstock₂ : ∀ p ∈ K ∪ S, p₂ p = ActivationStocks.profileStockTwo Q h p)
    (hBK : B ⊆ K) (hends : ∀ η ∈ J, (W.left, η) ∈ B ∧ (W.right, η) ∈ B)
    (hphys : ∀ p ∈ K ∪ S, E =ᶠ[𝓝 p] fun q => Real.sqrt (2 * q.1) * f q)
    (patch : FiveProfileMoments.Patch) (hgap : W.right < patch.left)
    (A G : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G) (hApos : ∀ η, 0 < A η)
    (hwindow : Icc W.left W.right ×ˢ J ⊆ K)
    (hfollowing : Icc W.right patch.right ×ˢ J ⊆ S)
    (b : ℝ) (hb : FiveProfileMoments.GoodExponent b)
    (hpatchU : ∀ η ∈ J, ∀ X ∈ Ioo patch.left patch.right, U (X, η) = G η)
    (hpatchE : ∀ η ∈ J, ∀ X ∈ Ioo patch.left patch.right,
      Real.sqrt (2 * X) * f (X, η) = A η * X ^ b) :
    ∃ H : SmoothRepairFamily patch b A G (repairDebt W r f E U) J,
      ∃ N : ℕ, 0 < N ∧
      (∀ n : ℕ, N ≤ n →
        let R := profileRepair (P n) patch A (H.coefficients n) hA (H.smooth n)
        (∀ p ∈ Icc W.left patch.right ×ˢ J, 0 < R.f p ∧
          TrueConeLoop.InTrueCone (ActivationStocks.profileStockOne R h p)
            (ActivationStocks.profileStockTwo R h p) (angularShear R.E p) (signedAxialShear R.E R.U p)) ∧
        (∀ eta ∈ J, ∀ X : ℝ, patch.right ≤ X → profileRows R (X, eta) = profileRows Q (X, eta)) ∧
        (∀ p : Point, p.1 ∉ Ioo patch.left patch.right →
          R.E p = (P n).E p ∧ R.U p = (P n).U p ∧
          angularShear R.E p = angularShear (P n).E p ∧
          signedAxialShear R.E R.U p = signedAxialShear (P n).E (P n).U p ∧
          ((fun X => R.E (X, p.2)) =ᶠ[𝓝 p.1] fun X => (P n).E (X, p.2)) ∧
          ((fun X => R.U (X, p.2)) =ᶠ[𝓝 p.1] fun X => (P n).U (X, p.2)))) ∧
      (∀ q : ℕ, ∃ Nq C : ℝ, 1 ≤ Nq ∧ 0 < C ∧ ∀ n : ℝ, Nq ≤ n →
        let R := profileRepair (P n) patch A (H.coefficients n) hA (H.smooth n)
        (∀ X eta : ℝ, X ≤ patch.right → eta ∈ J →
          |iteratedDeriv q (fun e => R.E (X, e)) eta - iteratedDeriv q (fun e => Q.E (X, e)) eta| ≤ C / n ∧
          |iteratedDeriv q (fun e => R.U (X, e)) eta - iteratedDeriv q (fun e => Q.U (X, e)) eta| ≤ C / n) ∧
        (∀ X : ℝ, 0 ≤ X → JetBounds.FiniteJetBound q
          (fun eta => profileRows R (X, eta) - profileRows Q (X, eta)) J (C / n))) := by
  classical
  obtain ⟨H⟩ := exists_actual_repair_family_all_jets W r f E U ha hm hp₂ hf hE hU
    patch b hb J hJ A G hA hG hApos
  obtain ⟨N₀, Cc, hN₀, hCc, hcoeff⟩ := H.rates 1
  obtain ⟨Nc, hNc, hcone⟩ := profiles_trueCone W r f E U hK hKW ha hm hp₁ hp₂ hf hE hU haK
    S hS hSW haNom hbNom hrelaxed hScone P Q hPf hPU hQf hQU hP0 J hJ hTJ hTD hTD'
    h hL hpos hstock₁ hstock₂ hBK hends hphys patch hgap A hA H.coefficients H.smooth
    N₀ Cc hCc.le (fun n hn _ => hcoeff n hn)
  obtain ⟨Nr, hNr⟩ := exists_nat_gt H.threshold
  refine ⟨H, max Nc Nr, hNc.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro n hn
    have hcn : Nc ≤ n := (le_max_left _ _).trans hn
    have hrn : H.threshold ≤ (n : ℝ) := hNr.le.trans (by exact_mod_cast (le_trans (le_max_right Nc Nr) hn))
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      have hpt : p ∈ K ∪ S := by
        by_cases hr : p.1 ≤ W.right
        · exact Or.inl (hwindow ⟨⟨hp.1.1, hr⟩, hp.2⟩)
        · exact Or.inr (hfollowing ⟨⟨(lt_of_not_ge hr).le, hp.1.2⟩, hp.2⟩)
      exact hcone n hcn p hpt
    · intro eta heta X hX
      have hmom := H.solves n eta (H.contains n hrn heta)
      have hs := actual_histories_restored W r f E U ha hm hp₂ hf hE hU
        patch hgap b A G (H.coefficients n) n eta X hX (hApos eta).ne'
        (hpatchU eta heta) (hpatchE eta heta) hmom
      apply sub_eq_zero.mp
      rw [profileRows_sub (profileRepair (P n) patch A (H.coefficients n) hA (H.smooth n)) Q (hP0 n)]
      change axisHistory (applyRepairF patch A (H.coefficients n) (P n).f)
        (applyRepairU patch A (H.coefficients n) (P n).U) (X, eta) - axisHistory Q.f Q.U (X, eta) = 0
      rw [hPf n, hPU n, hQf, hQU, hs, sub_self]
    · intro p hp
      have hs := shears_unchanged_outside
        (profileRepair (P n) patch A (H.coefficients n) hA (H.smooth n))
        (P n) patch A (H.coefficients n) rfl rfl hp
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2,
        profileRepair_radial_germs (P n) patch A (H.coefficients n) hA (H.smooth n) hp⟩
  · intro q
    exact H.repaired_profiles_eta_rates W r f E U ha hm hp₂ hf hE hU hgap hJ hA
      (fun n => profileRepair (P n) patch A (H.coefficients n) hA (H.smooth n)) Q
      (fun n => by simp only [profileRepair, hPf n])
      (fun n => by simp only [profileRepair, hPU n]) hQf hQU hP0 patch.right q

end NavierStokes.ModulatedProfileJetRates
