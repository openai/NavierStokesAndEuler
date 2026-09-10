import NavierStokes.LocalMeanPhysicalBounds
import NavierStokes.SharpPhysicalLoss

noncomputable section
namespace NavierStokes.SharpMeanJetBounds
open Set Function Filter ProblemStatement PhysicalWaveSum LocalPhysicalCopyBounds
open PhysicalMeanJetBounds LocalMeanPhysicalBounds
open scoped Topology ContDiff BigOperators

theorem common_stripped_log_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h a b : ℝ} (hh : 0 ≤ h) (_hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, ContDiff ℝ ∞ f →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P := by
  have hcover : 0 ≤ coverBound Δ := zero_le_one.trans (coverBound_ge_one Δ)
  obtain ⟨K,hK,hgraph⟩ := SharpGraphBounds.graphRestriction_jet_bound (E := E) (b := b) hh ha m
  obtain ⟨D,hD,P,hweight⟩ := SharpLogWeights.chart_weight_bound (g-(m:ℝ)*(1+h)) e
  let A' := A*coverBound Δ^m
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  refine ⟨K*A'*D, by positivity, P, ?_⟩
  intro n hn d hd w hw ht q hq hlo hhi f hf hfb
  have hQ := ChartScales.Q_pos n
  have hS := ChartScales.S_pos (show 1 ≤ n by omega)
  have hjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (f ∘ downLift d) (PhysicalGraphBounds.physicalLift h n w)‖ ≤
      A'*ChartScales.Q n^g*ChartScales.S n^e := by
    intro i hi
    exact (downLift_jet_bound hf hd (PhysicalGraphBounds.physicalLift h n w)
      (B := A*ChartScales.Q n^g*ChartScales.S n^e) (by positivity) hfb i hi).trans_eq (by dsimp [A']; ring)
  have hb := hgraph n hn w hw ht (f ∘ downLift d) (hf.comp (downLift d).contDiff)
    _ (by positivity) hjet
  apply hb.trans
  have hpow : ChartScales.Q n^g*ChartScales.Q n^(-(m:ℝ)*(1+h)) = ChartScales.Q n^(g-(m:ℝ)*(1+h)) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    _ = (K*A')*(ChartScales.Q n^(g-(m:ℝ)*(1+h))*ChartScales.S n^e) := by
      rw [← hpow]
      ring
    _ ≤ (K*A')*(D*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P) :=
      mul_le_mul_of_nonneg_left (hweight n (by omega) q hq hlo hhi) (mul_nonneg hK.le hA')
    _ = _ := by ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem common_stripped_log_bound_local {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (g e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : LiftPoint → E, SmoothNear f (commonLift h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (commonLift h n d w)‖ ≤
        A * ChartScales.Q n ^ g * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (f ∘ commonLift h n d) w‖ ≤
        C*q^(g-(m:ℝ)*(1+h))*(1+|Real.log q|)^P := by
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound (E := E) (b := b)
    hh hh1 ha Δ m g e A hA
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have haxis := PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hann)
  have he' := he.comp_tendsto (commonLift_smoothAt h n d haxis).continuousAt
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  apply hb n hn d hd w hann ht q hq hlo hhi F hF
  intro i hi
  rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
  exact hjet i hi

noncomputable def meanLoss (h degree : ℝ) (m : ℕ) : ℝ := (m:ℝ)*(1+h)+degree

theorem bandField_log_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → E, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandField h n d degree f) w‖ ≤
        C*q^(gain-meanLoss h degree m)*(1+|Real.log q|)^P := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  let A' : ℝ := (m.factorial : ℝ) * A * B ^ m
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound_local (E := E) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let u : LiftPoint → E := fun x => (ChartScales.Q n ^ (-degree)) • F (PhysicalClassBounds.cylindricalMap x)
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hg.const_smul _) hx
  have he' : bandField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    exact congrArg (fun v => (ChartScales.Q n ^ (-degree)) • v) hz
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hg.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) •
      (F ∘ PhysicalClassBounds.cylindricalMap) x) (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree))
        (iteratedFDeriv ℝ i (F ∘ PhysicalClassBounds.cylindricalMap) (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) :=
        mul_le_mul_of_nonneg_left (hcomp i hi) (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  have hexp : gain-degree-(m:ℝ)*(1+h) = gain-meanLoss h degree m := by
    unfold meanLoss
    ring
  simpa only [hexp] using hbound huc

theorem bandAngularField_log_bound {h a b : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 2) (ha : 0 < a)
    (Δ m : ℕ) (gain degree e A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ n : ℕ, 4 ≤ n → ∀ d : ℕ, d ≤ Δ →
      ∀ w : SpaceTime, PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b → |w.1| ≤ 1 →
      ∀ q : ℝ, 0 < q → q / 2 ≤ ChartScales.Q n → ChartScales.Q n ≤ 2 * q →
      ∀ f : Point → ℝ, SmoothNear f (graph h n d w) →
      (∀ i ≤ m, ‖iteratedFDeriv ℝ i f (graph h n d w)‖ ≤
        A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) →
      ‖iteratedFDeriv ℝ m (bandAngularField h n d degree f) w‖ ≤
        C*q^(gain-meanLoss h degree m)*(1+|Real.log q|)^P := by
  obtain ⟨B, hB, hBj⟩ := PhysicalClassBounds.cylindricalMap_positiveJets (b := b) ha m
  obtain ⟨V, hV, hVj⟩ := angularVector_lift_jet_bound (b := b) ha m
  let A' : ℝ := (2 : ℝ) ^ m * ((m.factorial : ℝ) * A * B ^ m) * V
  have hA' : 0 ≤ A' := by dsimp [A']; positivity
  obtain ⟨C, hC, P, hb⟩ := common_stripped_log_bound_local (E := Space) (b := b)
    hh hh1 ha Δ m (gain - degree) e A' hA'
  refine ⟨C, hC, P, ?_⟩
  intro n hn d hd w hann ht q hq hlo hhi f hf hjet
  obtain ⟨F, hF, he⟩ := hf.exists_global_germ
  have hx := PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n d w hann
  have hg : ContDiffOn ℝ ∞ (F ∘ PhysicalClassBounds.cylindricalMap)
      (PhysicalClassBounds.cylindricalDomain a b) :=
    hF.comp_contDiffOn (PhysicalClassBounds.cylindricalMap_smooth ha)
  let v : LiftPoint → Space := fun x => F (PhysicalClassBounds.cylindricalMap x) •
    angularVector (PhysicalGraphBounds.liftXY x)
  have hv : ContDiffOn ℝ ∞ v (PhysicalClassBounds.cylindricalDomain a b) :=
    hg.smul (angularVector_lift_smooth ha)
  let u : LiftPoint → Space := fun x => (ChartScales.Q n ^ (-degree)) • v x
  have hu : SmoothNear u (commonLift h n d w) :=
    SmoothNear.of_open (PhysicalClassBounds.cylindricalDomain_open a b)
      (hv.const_smul _) hx
  have he' : bandAngularField h n d degree f =ᶠ[𝓝 w] u ∘ commonLift h n d := by
    filter_upwards [he.comp_tendsto (graph_smoothAt ha h n d hann).continuousAt] with z hz
    change (ChartScales.Q n ^ (-degree) * f (graph h n d z)) •
      angularVector (PhysicalGraphBounds.radialProjection z) =
        ChartScales.Q n ^ (-degree) • (F (graph h n d z) •
          angularVector (PhysicalGraphBounds.liftXY (commonLift h n d z)))
    rw [PhysicalClassBounds.liftXY_commonLift, angularVector_scaledRadial]
    change f (graph h n d z) = F (graph h n d z) at hz
    simp only [hz, smul_smul]
  rw [iteratedFDeriv_eq_of_eventuallyEq he' m]
  have hbound := hb n hn d hd w hann ht q hq hlo hhi u hu
  have hqN := ChartScales.Q_pos n
  have hSN := ChartScales.S_pos (show 1 ≤ n by omega)
  have hab : 0 ≤ A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by positivity
  have hFjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F (graph h n d w)‖ ≤
      A * ChartScales.Q n ^ gain * ChartScales.S n ^ e := by
    intro i hi
    rw [← iteratedFDeriv_eq_of_eventuallyEq he i]
    exact hjet i hi
  have hcomp := PhysicalClassBounds.composition_jet_bound hF
    (PhysicalClassBounds.cylindricalDomain_open a b) (PhysicalClassBounds.cylindricalMap_smooth ha)
    hx m hab hB hFjet (hBj _ hx)
  have huc : ∀ i ≤ m, ‖iteratedFDeriv ℝ i u (commonLift h n d w)‖ ≤
      A' * ChartScales.Q n ^ (gain - degree) * ChartScales.S n ^ e := by
    intro i hi
    have hnear := hv.contDiffAt ((PhysicalClassBounds.cylindricalDomain_open a b).mem_nhds hx)
    change ‖iteratedFDeriv ℝ i (fun x => (ChartScales.Q n ^ (-degree)) • v x)
      (commonLift h n d w)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hnear.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)),
      norm_smul (ChartScales.Q n ^ (-degree)) (iteratedFDeriv ℝ i v (commonLift h n d w)),
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hqN (-degree)).le]
    have hprod := smul_jet_bound (PhysicalClassBounds.cylindricalDomain_open a b)
      hg (angularVector_lift_smooth ha) hx hi
      (by positivity : 0 ≤ (m.factorial : ℝ) *
        (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m)
      (zero_le_one.trans hV) hcomp (hVj _ hx)
    calc
      _ ≤ ChartScales.Q n ^ (-degree) * ((2 : ℝ) ^ m * ((m.factorial : ℝ) *
          (A * ChartScales.Q n ^ gain * ChartScales.S n ^ e) * B ^ m) * V) :=
        mul_le_mul_of_nonneg_left hprod (Real.rpow_pos_of_pos hqN _).le
      _ = _ := by dsimp [A']; rw [Real.rpow_sub hqN, Real.rpow_neg hqN.le]; ring
  have hexp : gain-degree-(m:ℝ)*(1+h) = gain-meanLoss h degree m := by
    unfold meanLoss
    ring
  simpa only [hexp] using hbound huc

variable {h degree a b : ℝ} {N Δ : ℕ} {U : Set PhysicalGraphBounds.Plane}

theorem field_log_bound (D : CoherentFamily h degree N Δ U E)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.field w‖ ≤ C*physicalQ h w^(gain-meanLoss h degree m)*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, P, hb⟩ := bandField_log_bound (E := E) (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, P, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_field_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _ hts, norm_zero]
    positivity

theorem angularField_log_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ preterminal → |w.1| ≤ 1 →
      physicalQ h w ≤ ChartScales.Q N →
      ‖iteratedFDeriv ℝ m D.angularField w‖ ≤ C*physicalQ h w^(gain-meanLoss h degree m)*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨A, hA, e, hjet⟩ := hj m
  obtain ⟨C, hC, P, hb⟩ := bandAngularField_log_bound (b := 2 * b)
    hh.le hh1.le (div_pos ha (by norm_num : (0 : ℝ) < 4)) Δ m gain degree e A hA
  refine ⟨C, hC, P, ?_⟩
  intro w hw ht hsmall
  have hq := physicalQ_pos hh hh1 hw
  by_cases hts : w ∈ tsupport D.field
  · obtain ⟨n, hn, hqn, hnq, hu, he⟩ := exists_angularField_germ D hh hh1 hU hcover hw hsmall
    have hlo : physicalQ h w / 2 ≤ ChartScales.Q n := by linarith
    have hann := D.annulus_on_tsupport hh hh1 ha hab hU hs n hn hw hu hlo hnq.le hts
    rw [iteratedFDeriv_eq_of_eventuallyEq he m]
    apply hb n (hN.trans hn) (D.gap n) (D.gap_le n hn) w hann ht
      (physicalQ h w) hq hlo hnq.le (D.native n)
    · exact SmoothNear.of_open (PhysicalMeanDomain.slowDomain_open hU) (hsm n hn) hu
    · intro j hjm
      simpa only [Real.rpow_natCast] using hjet n hn _ hu j hjm
  · rw [jet_zero_off_tsupport _ _
      (notMem_tsupport_iff_eventuallyEq.mpr (D.angularField_zero_germ hts)), norm_zero]
    positivity


theorem curl_angularField_log_bound (D : CoherentFamily h degree N Δ U ℝ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hN : 4 ≤ N)
    (hU : IsOpen U)
    (hcover : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2 ⊆ U)
    (hsm : ∀ n ≥ N, ContDiffOn ℝ ∞ (D.native n) (PhysicalMeanDomain.slowDomain U))
    (hs : NativeSupport h a b N U D.native) {gain : ℝ} (hj : NativeJets N U gain D.native)
    (m : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ P : ℕ, ∀ w : SpaceTime, w ∈ physicalDomain h N → |w.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl D.angularField) w‖ ≤
        C*physicalQ h w^(gain-meanLoss h degree (m+1))*(1+|Real.log (physicalQ h w)|)^P := by
  obtain ⟨C, hC, P, hb⟩ := angularField_log_bound D hh hh1 ha hab hN hU hcover hsm hs hj (m + 1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖ * C,
    mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC, P, ?_⟩
  intro w hw ht
  exact (PhysicalClassBounds.spatialCurl_jet_bound (physicalDomain_open hh hh1 N)
    (angularField_smooth D hh hh1 ha hab hU hcover hsm hs) hw m).trans
    ((mul_le_mul_of_nonneg_left (hb w hw.1 ht hw.2.le)
      (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

end NavierStokes.SharpMeanJetBounds
