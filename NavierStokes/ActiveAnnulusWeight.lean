import NavierStokes.ActivationCone
import NavierStokes.FlatCutoff
import NavierStokes.UniformCone
import NavierStokes.EdgeWeightJets
import NavierStokes.TerminalEdgeFactor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# One flat weight on the active annulus

The logarithmic edge distances carry their actual exponential coefficients.
The global estimates are obtained from smooth edge factors and compactness.
-/

noncomputable section

namespace NavierStokes.ActiveAnnulusWeight

open Set Filter Metric
open scoped Topology ContDiff

noncomputable def weight (c a b y : ℝ) : ℝ := FlatCutoff.edge c (y-a) * FlatCutoff.edge 4 (b-y)

noncomputable def edgeDistance (a b y : ℝ) : ℝ := min 1 (min (y-a) (b-y))

noncomputable def radialWeight (c a b X : ℝ) : ℝ := if 0 < X then weight c a b (Real.log X) else 0

theorem edge_le_one {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : FlatCutoff.edge c x ≤ 1 := by
  by_cases hx : x ≤ 0
  · simp [FlatCutoff.edge_of_nonpos c hx]
  · rw [FlatCutoff.edge_of_pos c (lt_of_not_ge hx)]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg x)

theorem edge_mono_pos {c x y : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hxy : x ≤ y) :
    FlatCutoff.edge c x ≤ FlatCutoff.edge c y := by
  rw [FlatCutoff.edge_of_pos c hx,FlatCutoff.edge_of_pos c (hx.trans_le hxy)]
  apply Real.exp_le_exp.mpr
  have hs : x^2 ≤ y^2 := by nlinarith
  have hd := div_le_div_of_nonneg_left hc (sq_pos_of_pos hx) hs
  simpa only [neg_div] using neg_le_neg hd

theorem weight_nonneg (c a b y : ℝ) : 0 ≤ weight c a b y :=
  mul_nonneg (FlatCutoff.edge_nonneg _ _) (FlatCutoff.edge_nonneg _ _)

theorem weight_pos {c a b y : ℝ} (hy : y ∈ Ioo a b) : 0 < weight c a b y :=
  mul_pos (FlatCutoff.edge_pos _ (sub_pos.mpr hy.1)) (FlatCutoff.edge_pos _ (sub_pos.mpr hy.2))

theorem weight_zero_left (c b : ℝ) {a y : ℝ} (hy : y ≤ a) : weight c a b y = 0 := by
  simp only [weight,FlatCutoff.edge_of_nonpos c (sub_nonpos.mpr hy),zero_mul]

theorem weight_zero_right (c a : ℝ) {b y : ℝ} (hy : b ≤ y) : weight c a b y = 0 := by
  simp only [weight,FlatCutoff.edge_of_nonpos 4 (sub_nonpos.mpr hy),mul_zero]

theorem weight_le_left (c a b y : ℝ) : weight c a b y ≤ FlatCutoff.edge c (y-a) :=
  mul_le_of_le_one_right (FlatCutoff.edge_nonneg _ _) (edge_le_one (by norm_num) _)

theorem weight_le_right {c : ℝ} (hc : 0 ≤ c) (a b y : ℝ) :
    weight c a b y ≤ FlatCutoff.edge 4 (b-y) :=
  mul_le_of_le_one_left (FlatCutoff.edge_nonneg _ _) (edge_le_one hc _)

theorem weight_le_one {c : ℝ} (hc : 0 ≤ c) (a b y : ℝ) : weight c a b y ≤ 1 :=
  (weight_le_left c a b y).trans (edge_le_one hc _)

theorem weight_smooth {c : ℝ} (hc : 0 < c) (a b : ℝ) : ContDiff ℝ ∞ (weight c a b) :=
  ((FlatCutoff.edge_contDiff hc).comp (contDiff_id.sub contDiff_const)).mul
    ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 4)).comp (contDiff_const.sub contDiff_id))

theorem edgeDistance_pos {a b y : ℝ} (hy : y ∈ Ioo a b) : 0 < edgeDistance a b y :=
  lt_min zero_lt_one (lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2))

theorem edgeDistance_le_one (a b y : ℝ) : edgeDistance a b y ≤ 1 := min_le_left _ _
theorem edgeDistance_le_left (a b y : ℝ) : edgeDistance a b y ≤ y-a :=
  (min_le_right _ _).trans (min_le_left _ _)
theorem edgeDistance_le_right (a b y : ℝ) : edgeDistance a b y ≤ b-y :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem iteratedDeriv_zero_function (n : ℕ) : iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedDeriv_succ,ih,deriv_const']

theorem flat_left_of_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a : ℝ}
    (hz : ∀ x < a, f x = 0) (n : ℕ) : iteratedDeriv n f a = 0 := by
  have heq : EqOn (iteratedDeriv n f) (fun _ => 0) (Iio a) := by
    intro x hx
    have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact hz y hy
    rw [he.iteratedDeriv_eq n,iteratedDeriv_zero_function]
  have hc := heq.closure (hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)) continuous_const
  exact hc (by simp)

theorem flat_right_of_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {b : ℝ}
    (hz : ∀ x, b < x → f x = 0) (n : ℕ) : iteratedDeriv n f b = 0 := by
  have heq : EqOn (iteratedDeriv n f) (fun _ => 0) (Ioi b) := by
    intro x hx
    have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hz y hy
    rw [he.iteratedDeriv_eq n,iteratedDeriv_zero_function]
  have hc := heq.closure (hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)) continuous_const
  exact hc (by simp)

theorem weight_flat_left {c : ℝ} (hc : 0 < c) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (weight c a b) a = 0 :=
  flat_left_of_zero (weight_smooth hc a b) (fun _ hx => weight_zero_left c b hx.le) n

theorem weight_flat_right {c : ℝ} (hc : 0 < c) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (weight c a b) b = 0 :=
  flat_right_of_zero (weight_smooth hc a b) (fun _ hx => weight_zero_right c a hx.le) n

theorem radialWeight_zero_left (c b : ℝ) {a X : ℝ} (hX : X ≤ Real.exp a) : radialWeight c a b X = 0 := by
  by_cases hx : 0 < X
  · rw [radialWeight,ite_eq_left hx]
    exact weight_zero_left c b ((Real.log_le_iff_le_exp hx).2 hX)
  · exact ite_eq_right hx

theorem radialWeight_zero_right (c a : ℝ) {b X : ℝ} (hX : Real.exp b ≤ X) : radialWeight c a b X = 0 := by
  have hx : 0 < X := (Real.exp_pos b).trans_le hX
  rw [radialWeight,ite_eq_left hx]
  exact weight_zero_right c a ((Real.le_log_iff_exp_le hx).2 hX)

theorem radialWeight_pos {c a b X : ℝ} (hX : X ∈ Ioo (Real.exp a) (Real.exp b)) :
    0 < radialWeight c a b X := by
  have hx : 0 < X := (Real.exp_pos a).trans hX.1
  rw [radialWeight,ite_eq_left hx]
  exact weight_pos ⟨(Real.lt_log_iff_exp_lt hx).2 hX.1,(Real.log_lt_iff_lt_exp hx).2 hX.2⟩

theorem radialWeight_smooth {c : ℝ} (hc : 0 < c) (a b : ℝ) : ContDiff ℝ ∞ (radialWeight c a b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro X
  by_cases hx : 0 < X
  · have hs := (weight_smooth hc a b).contDiffAt.comp X (Real.contDiffAt_log.mpr hx.ne')
    have he : radialWeight c a b =ᶠ[𝓝 X] (fun x => weight c a b (Real.log x)) := by
      filter_upwards [Ioi_mem_nhds hx] with x hxp
      exact ite_eq_left hxp
    exact hs.congr_of_eventuallyEq he
  · have hlow : X < Real.exp a := (le_of_not_gt hx).trans_lt (Real.exp_pos a)
    have he : radialWeight c a b =ᶠ[𝓝 X] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds hlow] with x hxp
      exact radialWeight_zero_left c b hxp.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem radialWeight_flat_left {c : ℝ} (hc : 0 < c) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (radialWeight c a b) (Real.exp a) = 0 :=
  flat_left_of_zero (radialWeight_smooth hc a b) (fun _ hx => radialWeight_zero_left c b hx.le) n

theorem radialWeight_flat_right {c : ℝ} (hc : 0 < c) (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (radialWeight c a b) (Real.exp b) = 0 :=
  flat_right_of_zero (radialWeight_smooth hc a b) (fun _ hx => radialWeight_zero_right c a hx.le) n

theorem weight_lower_middle {c a b d y : ℝ} (hc : 0 ≤ c) (hd : 0 < d)
    (hy : y ∈ Icc (a+d) (b-d)) :
    FlatCutoff.edge c d * FlatCutoff.edge 4 d ≤ weight c a b y := by
  apply mul_le_mul
  · exact edge_mono_pos hc hd (by linarith [hy.1])
  · exact edge_mono_pos (by norm_num) hd (by linarith [hy.2])
  · exact FlatCutoff.edge_nonneg _ _
  · exact FlatCutoff.edge_nonneg _ _

theorem weight_compare_left {c a b d y : ℝ} (hd : 0 < b-a-d) (hy : y ≤ a+d) :
    FlatCutoff.edge c (y-a) ≤ weight c a b y / FlatCutoff.edge 4 (b-a-d) := by
  apply (le_div_iff₀ (FlatCutoff.edge_pos 4 hd)).2
  change FlatCutoff.edge c (y-a) * FlatCutoff.edge 4 (b-a-d) ≤
    FlatCutoff.edge c (y-a) * FlatCutoff.edge 4 (b-y)
  exact mul_le_mul_of_nonneg_left
    (edge_mono_pos (c := 4) (by norm_num) hd (by linarith)) (FlatCutoff.edge_nonneg _ _)

theorem weight_compare_right {c a b d y : ℝ} (hc : 0 ≤ c) (hd : 0 < b-a-d) (hy : b-d ≤ y) :
    FlatCutoff.edge 4 (b-y) ≤ weight c a b y / FlatCutoff.edge c (b-a-d) := by
  apply (le_div_iff₀ (FlatCutoff.edge_pos c hd)).2
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right
    (edge_mono_pos hc hd (by linarith)) (FlatCutoff.edge_nonneg _ _)

theorem distance_power_le_left {a b y : ℝ} (hy : y ∈ Ioo a b) {n N : ℕ} (hn : n ≤ N) :
    edgeDistance a b y ^ N ≤ (y-a)^n := by
  calc
    _ ≤ edgeDistance a b y ^ n :=
      pow_le_pow_of_le_one (edgeDistance_pos hy).le (edgeDistance_le_one _ _ _) hn
    _ ≤ _ := pow_le_pow_left₀ (edgeDistance_pos hy).le (edgeDistance_le_left _ _ _) n

theorem distance_power_le_right {a b y : ℝ} (hy : y ∈ Ioo a b) {n N : ℕ} (hn : n ≤ N) :
    edgeDistance a b y ^ N ≤ (b-y)^n := by
  calc
    _ ≤ edgeDistance a b y ^ n :=
      pow_le_pow_of_le_one (edgeDistance_pos hy).le (edgeDistance_le_one _ _ _) hn
    _ ≤ _ := pow_le_pow_left₀ (edgeDistance_pos hy).le (edgeDistance_le_right _ _ _) n

theorem left_bound_to_weight {c a b d y C : ℝ} (hC : 0 ≤ C)
    (hd : 0 < b-a-d) (hy : y ∈ Ioo a b) (hyl : y ≤ a+d)
    {n N : ℕ} (hn : n ≤ N) :
    C * FlatCutoff.edge c (y-a) / (y-a)^n ≤
      (C / FlatCutoff.edge 4 (b-a-d)) * weight c a b y / edgeDistance a b y ^ N := by
  calc
    _ ≤ C * FlatCutoff.edge c (y-a) / edgeDistance a b y ^ N :=
      div_le_div_of_nonneg_left (mul_nonneg hC (FlatCutoff.edge_nonneg _ _))
        (pow_pos (edgeDistance_pos hy) _) (distance_power_le_left hy hn)
    _ ≤ _ := div_le_div_of_nonneg_right (by
      calc
        C * FlatCutoff.edge c (y-a) ≤ C * (weight c a b y / FlatCutoff.edge 4 (b-a-d)) :=
          mul_le_mul_of_nonneg_left (weight_compare_left hd hyl) hC
        _ = _ := by ring) (pow_nonneg (edgeDistance_pos hy).le _)

theorem right_bound_to_weight {c a b d y C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hd : 0 < b-a-d) (hy : y ∈ Ioo a b) (hyr : b-d ≤ y)
    {n N : ℕ} (hn : n ≤ N) :
    C * FlatCutoff.edge 4 (b-y) / (b-y)^n ≤
      (C / FlatCutoff.edge c (b-a-d)) * weight c a b y / edgeDistance a b y ^ N := by
  calc
    _ ≤ C * FlatCutoff.edge 4 (b-y) / edgeDistance a b y ^ N :=
      div_le_div_of_nonneg_left (mul_nonneg hC (FlatCutoff.edge_nonneg _ _))
        (pow_pos (edgeDistance_pos hy) _) (distance_power_le_right hy hn)
    _ ≤ _ := div_le_div_of_nonneg_right (by
      calc
        C * FlatCutoff.edge 4 (b-y) ≤ C * (weight c a b y / FlatCutoff.edge c (b-a-d)) :=
          mul_le_mul_of_nonneg_left (weight_compare_right hc hd hyr) hC
        _ = _ := by ring) (pow_nonneg (edgeDistance_pos hy).le _)

theorem interior_bound_to_weight {c a b d y C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hd : 0 < d) (hy : y ∈ Ioo a b) (hym : y ∈ Icc (a+d) (b-d)) (N : ℕ) :
    C ≤ (C / (FlatCutoff.edge c d * FlatCutoff.edge 4 d)) *
      weight c a b y / edgeDistance a b y ^ N := by
  have he : 0 < FlatCutoff.edge c d * FlatCutoff.edge 4 d :=
    mul_pos (FlatCutoff.edge_pos _ hd) (FlatCutoff.edge_pos _ hd)
  have hfirst : C ≤ C / (FlatCutoff.edge c d * FlatCutoff.edge 4 d) * weight c a b y := by
    calc
      C = (C / (FlatCutoff.edge c d * FlatCutoff.edge 4 d)) *
          (FlatCutoff.edge c d * FlatCutoff.edge 4 d) := by
            symm
            exact div_mul_cancel₀ C he.ne'
      _ ≤ _ := mul_le_mul_of_nonneg_left (weight_lower_middle hc hd hym) (div_nonneg hC he.le)
  exact hfirst.trans ((le_div_iff₀ (pow_pos (edgeDistance_pos hy) N)).2
    (mul_le_of_le_one_right
      (mul_nonneg (div_nonneg hC he.le) (weight_nonneg _ _ _ _))
      (pow_le_one₀ (edgeDistance_pos hy).le (edgeDistance_le_one _ _ _))))

section CompactFamilies

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An actual local edge identity and a smooth coefficient. No weighted
derivative bound is included in these data. -/
structure EdgeFactor (K : Set E) (c : ℝ) (T : E × ℝ → V) where
  coefficient : E × ℝ → V
  order : ℕ
  width : ℝ
  width_pos : 0 < width
  domain : Set (E × ℝ)
  domain_open : IsOpen domain
  boundary_mem : K ×ˢ ({0} : Set ℝ) ⊆ domain
  smooth : ContDiffOn ℝ ∞ coefficient domain
  boundary_ne_zero : ∀ p ∈ K, coefficient (p,0) ≠ 0
  identity : ∀ p ∈ K, ∀ x : ℝ, 0 < x → x < width →
    T (p,x) = (FlatCutoff.edge c x / x ^ order) • coefficient (p,x)

/-- Exact local equality transports an edge model to a joined stress. -/
noncomputable def EdgeFactor.transfer {K : Set E} {c : ℝ} {T S : E × ℝ → V}
    (F : EdgeFactor K c T) {w : ℝ} (hw : 0 < w) (hww : w ≤ F.width)
    (he : ∀ p ∈ K, ∀ x : ℝ, 0 < x → x < w → S (p,x) = T (p,x)) :
    EdgeFactor K c S where
  coefficient := F.coefficient
  order := F.order
  width := w
  width_pos := hw
  domain := F.domain
  domain_open := F.domain_open
  boundary_mem := F.boundary_mem
  smooth := F.smooth
  boundary_ne_zero := F.boundary_ne_zero
  identity := fun p hp x hx hxw => (he p hp x hx hxw).trans
    (F.identity p hp x hx (hxw.trans_le hww))

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem compact_nonzero_collar {K : Set E} (hK : IsCompact K) {B : E × ℝ → V}
    {O : Set (E × ℝ)} (hO : IsOpen O) (hB : ContinuousOn B O)
    (hK0 : K ×ˢ ({0} : Set ℝ) ⊆ O) (hne : ∀ p ∈ K, B (p,0) ≠ 0) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ K ×ˢ Icc (0 : ℝ) d ⊆ O ∧
      ∀ p ∈ K, ∀ x ∈ Icc (0 : ℝ) d, c ≤ ‖B (p,x)‖ := by
  have hnorm : ContinuousOn (fun p => ‖B (p,0)‖) K :=
    hB.norm.comp (continuous_id.prodMk continuous_const).continuousOn (fun p hp => hK0 ⟨hp,rfl⟩)
  obtain ⟨m,hm,hmb⟩ := UniformCone.positive_uniform_margin hK hnorm
    (fun p hp => norm_pos_iff.mpr (hne p hp))
  let W : Set (E × ℝ) := {q | q ∈ O ∧ m/2 < ‖B q‖}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    filter_upwards [hO.mem_nhds hq.1,
      (hB.continuousAt (hO.mem_nhds hq.1)).norm.eventually (Ioi_mem_nhds hq.2)] with r hr hrr
    exact ⟨hr,hrr⟩
  have hKW : K ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    have hx0 : x = 0 := hx
    subst x
    exact ⟨hK0 ⟨hp,rfl⟩,lt_of_lt_of_le (by linarith) (hmb p hp)⟩
  obtain ⟨d,hd,hdW⟩ := (hK.prod isCompact_singleton).exists_cthickening_subset_open hW hKW
  have hin (p : E) (hp : p ∈ K) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (d/2)) : (p,x) ∈ W := by
    apply hdW
    apply closedBall_subset_cthickening (show (p,(0 : ℝ)) ∈ K ×ˢ ({0} : Set ℝ) from ⟨hp,rfl⟩) d
    change dist (p,x) (p,(0 : ℝ)) ≤ d
    simp only [Prod.dist_eq,dist_self,Real.dist_eq,sub_zero,abs_of_nonneg hx.1,max_eq_right hx.1]
    linarith [hx.2]
  exact ⟨d/2,m/2,by positivity,by positivity,
    fun q hq => (hin q.1 hq.1 q.2 hq.2).1,
    fun p hp x hx => (hin p hp x hx).2.le⟩

theorem EdgeFactor.collar {K : Set E} (hK : IsCompact K) {c : ℝ} {T : E × ℝ → V}
    (F : EdgeFactor K c T) :
    ∃ d m : ℝ, 0 < d ∧ d < F.width ∧ d ≤ 1 ∧ 0 < m ∧
      K ×ˢ Icc (0 : ℝ) d ⊆ F.domain ∧
      ∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d → m * FlatCutoff.edge c x ≤ ‖T (p,x)‖ := by
  obtain ⟨d0,m,hd0,hm,hdom,hbound⟩ := compact_nonzero_collar hK F.domain_open F.smooth.continuousOn
    F.boundary_mem F.boundary_ne_zero
  let d := min d0 (min (F.width/2) 1)
  have hd : 0 < d := lt_min hd0 (lt_min (half_pos F.width_pos) zero_lt_one)
  have hd0' : d ≤ d0 := min_le_left _ _
  have hdw : d < F.width := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    (half_lt_self F.width_pos)
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨d,m,hd,hdw,hd1,hm,?_,?_⟩
  · exact Set.prod_mono Subset.rfl (Icc_subset_Icc_right hd0') |>.trans hdom
  · intro p hp x hx hxd
    have hx1 : x ≤ 1 := hxd.trans hd1
    have he := FlatCutoff.edge_nonneg c x
    have hpw : 0 < x ^ F.order := pow_pos hx _
    have hpp : x ^ F.order ≤ 1 := pow_le_one₀ hx.le hx1
    have hdiv : FlatCutoff.edge c x ≤ FlatCutoff.edge c x / x ^ F.order :=
      (le_div_iff₀ hpw).2 (mul_le_of_le_one_right he hpp)
    rw [F.identity p hp x hx (hxd.trans_lt hdw),norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg he hpw.le)]
    calc
      m * FlatCutoff.edge c x ≤ ‖F.coefficient (p,x)‖ * FlatCutoff.edge c x :=
        mul_le_mul_of_nonneg_right (hbound p hp x ⟨hx.le,hxd.trans hd0'⟩) he
      _ ≤ ‖F.coefficient (p,x)‖ * (FlatCutoff.edge c x / x ^ F.order) :=
        mul_le_mul_of_nonneg_left hdiv (norm_nonneg _)
      _ = _ := mul_comm _ _

noncomputable def leftChart (a : ℝ) (T : E × ℝ → V) (q : E × ℝ) : V := T (q.1,a+q.2)
noncomputable def rightChart (b : ℝ) (T : E × ℝ → V) (q : E × ℝ) : V := T (q.1,b-q.2)

noncomputable def radialReflection : (E × ℝ) ≃ₗᵢ[ℝ] (E × ℝ) :=
  { (LinearEquiv.refl ℝ E).prodCongr (LinearEquiv.neg ℝ) with
    norm_map' := by intro q; simp [Prod.norm_def] }

theorem iteratedFDeriv_leftChart (a : ℝ) (T : E × ℝ → V) (n : ℕ) (q : E × ℝ) :
    iteratedFDeriv ℝ n (leftChart a T) q = iteratedFDeriv ℝ n T (q.1,a+q.2) := by
  have he : leftChart a T = fun q => T (q + (0,a)) := by
    ext ⟨p,x⟩
    simp [leftChart,add_comm]
  rw [he,iteratedFDeriv_comp_add_right]
  rcases q with ⟨p,x⟩
  simp only [Prod.mk_add_mk,add_zero,add_comm x a]

theorem norm_iteratedFDeriv_rightChart (b : ℝ) (T : E × ℝ → V) (n : ℕ) (q : E × ℝ) :
    ‖iteratedFDeriv ℝ n (rightChart b T) q‖ = ‖iteratedFDeriv ℝ n T (q.1,b-q.2)‖ := by
  let G : E × ℝ → V := fun q => T (q + (0,b))
  have he : rightChart b T = G ∘ radialReflection := by
    ext q
    simp [rightChart,G,radialReflection,sub_eq_add_neg,add_comm]
  rw [he,(radialReflection (E := E)).norm_iteratedFDeriv_comp_right G q n]
  rcases q with ⟨p,x⟩
  simp [G,iteratedFDeriv_comp_add_right,radialReflection,sub_eq_add_neg,add_comm]

theorem iteratedFDeriv_eq_of_eqOn {S : Set (E × ℝ)} (hS : UniqueDiffOn ℝ S)
    {f g : E × ℝ → V} (he : EqOn f g S) {q : E × ℝ} (hq : q ∈ S)
    (hf : ContDiffAt ℝ ∞ f q) (hg : ContDiffAt ℝ ∞ g q) (n : ℕ) :
    iteratedFDeriv ℝ n f q = iteratedFDeriv ℝ n g q := by
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hS (hf.of_le (EdgeWeightJets.nat_le_infty n)) hq,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hS (hg.of_le (EdgeWeightJets.nat_le_infty n)) hq]
  exact iteratedFDerivWithin_congr he hq n

/-- The local derivative estimates are consequences of the actual factor
identity. Unique differentiability of the compact parameter set also covers
its endpoints. -/
theorem EdgeFactor.derivative_bound {K : Set E} (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) {c : ℝ} (hc : 0 < c) {T : E × ℝ → V}
    (F : EdgeFactor K c T) (n : ℕ) {d : ℝ} (hd : 0 < d) (hdw : d < F.width)
    (hdom : K ×ˢ Icc (0 : ℝ) d ⊆ F.domain)
    (hT : ∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d → ContDiffAt ℝ ∞ T (p,x)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ K,
      ∀ x : ℝ, 0 < x → x ≤ d →
        ‖iteratedFDeriv ℝ i T (p,x)‖ ≤ C * FlatCutoff.edge c x / x^N := by
  obtain ⟨C,hC,N,hbound⟩ := EdgeWeightJets.edge_smul_iteratedFDeriv_bound_on hc F.order
    F.domain_open F.smooth hK n hd hdom
  refine ⟨C,hC,N,?_⟩
  intro i hi p hp x hx hxd
  let G : E × ℝ → V := fun q => (FlatCutoff.edge c q.2 / q.2^F.order) • F.coefficient q
  have he : EqOn T G (K ×ˢ Ioo (0 : ℝ) F.width) := by
    rintro ⟨q,y⟩ ⟨hq,hy⟩
    exact F.identity q hq y hy.1 hy.2
  have hG : ContDiffAt ℝ ∞ G (p,x) :=
    (((FlatCutoff.edge_div_pow_contDiff hc F.order).comp contDiff_snd).contDiffAt).smul
      (F.smooth.contDiffAt (F.domain_open.mem_nhds (hdom ⟨hp,hx.le,hxd⟩)))
  rw [iteratedFDeriv_eq_of_eqOn (hKd.prod isOpen_Ioo.uniqueDiffOn) he
    ⟨hp,hx,hxd.trans_lt hdw⟩ (hT p hp x hx hxd) hG i]
  exact hbound i hi p hp x hx hxd

theorem compact_jets_bound {O S : Set (E × ℝ)} (hO : IsOpen O)
    {T : E × ℝ → V} (hT : ContDiffOn ℝ ∞ T O) (hS : IsCompact S)
    (hSO : S ⊆ O) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i ≤ n, ∀ q ∈ S, ‖iteratedFDeriv ℝ i T q‖ ≤ C := by
  have hb : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ S, ‖iteratedFDeriv ℝ i T q‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (iteratedFDeriv ℝ i T) O := by
      intro q hq
      have hi : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ i T) q :=
        (hT.contDiffAt (hO.mem_nhds hq)).iteratedFDeriv_right (WithTop.coe_le_coe.mpr le_top)
      exact hi.continuousAt.continuousWithinAt
    obtain ⟨C,hC⟩ := hS.exists_bound_of_continuousOn (hcont.mono hSO)
    exact ⟨max C 0,le_max_right _ _,fun q hq => (hC q hq).trans (le_max_left _ _)⟩
  choose C hC hb using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1),C i,?_,?_⟩
  · have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun i _ => hC i)
    linarith
  · intro i hi q hq
    have hs := Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact (hb i q hq).trans (by linarith)

/-- Positivity inside and genuine nonzero edge factors give one global
positive lower constant for the explicit product weight. -/
theorem exists_global_lower_bound {K : Set E} (hK : IsCompact K)
    {a b c : ℝ} (hab : a < b) (hc : 0 < c) {T : E × ℝ → V}
    (hT : ContinuousOn T (K ×ˢ Icc a b))
    (hinterior : ∀ p ∈ K, ∀ y ∈ Ioo a b, T (p,y) ≠ 0)
    (FL : EdgeFactor K c (leftChart a T)) (FR : EdgeFactor K 4 (rightChart b T)) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ y ∈ Ioo a b, m * weight c a b y ≤ ‖T (p,y)‖ := by
  obtain ⟨dl,ml,hdl,hdlwidth,hdl1,hml,hdldom,hl⟩ := FL.collar hK
  obtain ⟨dr,mr,hdr,hdrwidth,hdr1,hmr,hdrdom,hr⟩ := FR.collar hK
  let d := min dl (min dr ((b-a)/3))
  have hd : 0 < d := lt_min hdl (lt_min hdr (div_pos (sub_pos.mpr hab) (by norm_num)))
  have hdl' : d ≤ dl := min_le_left _ _
  have hdr' : d ≤ dr := (min_le_right _ _).trans (min_le_left _ _)
  have hmid : K ×ˢ Icc (a+d) (b-d) ⊆ K ×ˢ Icc a b := by
    intro q hq
    exact ⟨hq.1,by constructor <;> linarith [hq.2.1,hq.2.2]⟩
  obtain ⟨mm,hmm,hmb⟩ := UniformCone.positive_uniform_margin (hK.prod isCompact_Icc)
    ((hT.mono hmid).norm) (by
      rintro ⟨p,y⟩ ⟨hp,hy⟩
      exact norm_pos_iff.mpr (hinterior p hp y ⟨by linarith [hy.1],by linarith [hy.2]⟩))
  let m := min ml (min mr mm)
  have hm : 0 < m := lt_min hml (lt_min hmr hmm)
  have hml' : m ≤ ml := min_le_left _ _
  have hmr' : m ≤ mr := (min_le_right _ _).trans (min_le_left _ _)
  have hmm' : m ≤ mm := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨m,hm,?_⟩
  intro p hp y hy
  by_cases hleft : y-a ≤ d
  · have hh := hl p hp (y-a) (sub_pos.mpr hy.1) (hleft.trans hdl')
    have he : leftChart a T (p,y-a) = T (p,y) := by unfold leftChart; congr 1; simp
    rw [he] at hh
    exact ((mul_le_mul_of_nonneg_left (weight_le_left c a b y) hm.le).trans
      (mul_le_mul_of_nonneg_right hml' (FlatCutoff.edge_nonneg c (y-a)))).trans hh
  · by_cases hright : b-y ≤ d
    · have hh := hr p hp (b-y) (sub_pos.mpr hy.2) (hright.trans hdr')
      have he : rightChart b T (p,b-y) = T (p,y) := by unfold rightChart; congr 1; simp
      rw [he] at hh
      exact ((mul_le_mul_of_nonneg_left (weight_le_right hc.le a b y) hm.le).trans
        (mul_le_mul_of_nonneg_right hmr' (FlatCutoff.edge_nonneg 4 (b-y)))).trans hh
    · have hyM : y ∈ Icc (a+d) (b-d) := by constructor <;> linarith [lt_of_not_ge hleft,lt_of_not_ge hright]
      exact (mul_le_of_le_one_right hm.le (weight_le_one hc.le a b y)).trans
        (hmm'.trans (hmb (p,y) ⟨hp,hyM⟩))

/-- All fixed full derivative tensors share the same explicit flat weight.
The constants come from actual smooth coefficient jets and compactness. -/
theorem exists_global_derivative_bound {K : Set E} (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    {T : E × ℝ → V} {O : Set (E × ℝ)} (hO : IsOpen O)
    (hT : ContDiffOn ℝ ∞ T O) (hKO : K ×ˢ Icc a b ⊆ O)
    (FL : EdgeFactor K c (leftChart a T)) (FR : EdgeFactor K 4 (rightChart b T))
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ K,
      ∀ y ∈ Ioo a b, ‖iteratedFDeriv ℝ i T (p,y)‖ ≤
        C * weight c a b y / edgeDistance a b y ^ N := by
  obtain ⟨dl,ml,hdl,hdlw,hdl1,hml,hdlo,hlower⟩ := FL.collar hK
  obtain ⟨dr,mr,hdr,hdrw,hdr1,hmr,hdro,hrlower⟩ := FR.collar hK
  let d := min dl (min dr ((b-a)/3))
  have hd : 0 < d := lt_min hdl (lt_min hdr (div_pos (sub_pos.mpr hab) (by norm_num)))
  have hdl' : d ≤ dl := min_le_left _ _
  have hdr' : d ≤ dr := (min_le_right _ _).trans (min_le_left _ _)
  have hdgap : d ≤ (b-a)/3 := (min_le_right _ _).trans (min_le_right _ _)
  have hgap : 0 < b-a-d := by linarith
  have hleftSmooth : ∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
      ContDiffAt ℝ ∞ (leftChart a T) (p,x) := by
    intro p hp x hx hxd
    have hh : (p,a+x) ∈ O := hKO ⟨hp,by change a ≤ a+x ∧ a+x ≤ b; constructor <;> linarith⟩
    have hm : ContDiffAt ℝ ∞ (fun q : E × ℝ => (q.1,a+q.2)) (p,x) :=
      contDiffAt_fst.prodMk (contDiffAt_const.add contDiffAt_snd)
    exact (hT.contDiffAt (hO.mem_nhds hh)).comp (p,x) hm
  have hrightSmooth : ∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
      ContDiffAt ℝ ∞ (rightChart b T) (p,x) := by
    intro p hp x hx hxd
    have hh : (p,b-x) ∈ O := hKO ⟨hp,by change a ≤ b-x ∧ b-x ≤ b; constructor <;> linarith⟩
    have hm : ContDiffAt ℝ ∞ (fun q : E × ℝ => (q.1,b-q.2)) (p,x) :=
      contDiffAt_fst.prodMk (contDiffAt_const.sub contDiffAt_snd)
    exact (hT.contDiffAt (hO.mem_nhds hh)).comp (p,x) hm
  obtain ⟨CL,hCL,NL,hL⟩ := FL.derivative_bound hK hKd hc n hd (hdl'.trans_lt hdlw)
    ((Set.prod_mono Subset.rfl (Icc_subset_Icc_right hdl')).trans hdlo) hleftSmooth
  obtain ⟨CR,hCR,NR,hR⟩ := FR.derivative_bound hK hKd (by norm_num) n hd (hdr'.trans_lt hdrw)
    ((Set.prod_mono Subset.rfl (Icc_subset_Icc_right hdr')).trans hdro) hrightSmooth
  have hmiddle : K ×ˢ Icc (a+d) (b-d) ⊆ O := by
    intro q hq
    apply hKO
    exact ⟨hq.1,by constructor <;> linarith [hq.2.1,hq.2.2]⟩
  obtain ⟨CM,hCM,hM⟩ := compact_jets_bound hO hT (hK.prod isCompact_Icc) hmiddle n
  let AL := CL / FlatCutoff.edge 4 (b-a-d)
  let AR := CR / FlatCutoff.edge c (b-a-d)
  let AM := CM / (FlatCutoff.edge c d * FlatCutoff.edge 4 d)
  have hAL : 0 < AL := div_pos hCL (FlatCutoff.edge_pos _ hgap)
  have hAR : 0 < AR := div_pos hCR (FlatCutoff.edge_pos _ hgap)
  have hAM : 0 < AM := div_pos hCM (mul_pos (FlatCutoff.edge_pos _ hd) (FlatCutoff.edge_pos _ hd))
  let C := AL + AR + AM
  have hC : 0 < C := by dsimp [C]; positivity
  have hALC : AL ≤ C := by dsimp [C]; linarith
  have hARC : AR ≤ C := by dsimp [C]; linarith
  have hAMC : AM ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,NL+NR,?_⟩
  intro i hi p hp y hy
  have hmono (B : ℝ) (hB : B ≤ C) :
      B * weight c a b y / edgeDistance a b y ^ (NL+NR) ≤
        C * weight c a b y / edgeDistance a b y ^ (NL+NR) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB (weight_nonneg _ _ _ _))
      (pow_nonneg (edgeDistance_pos hy).le _)
  by_cases hleft : y-a ≤ d
  · have hh := hL i hi p hp (y-a) (sub_pos.mpr hy.1) hleft
    rw [iteratedFDeriv_leftChart,show a+(y-a)=y by ring] at hh
    exact hh.trans ((left_bound_to_weight hCL.le hgap hy (by linarith) (Nat.le_add_right _ _)).trans
      (hmono AL hALC))
  · by_cases hright : b-y ≤ d
    · have hh := hR i hi p hp (b-y) (sub_pos.mpr hy.2) hright
      rw [norm_iteratedFDeriv_rightChart,show b-(b-y)=y by ring] at hh
      exact hh.trans ((right_bound_to_weight hc.le hCR.le hgap hy (by linarith)
        (Nat.le_add_left _ _)).trans (hmono AR hARC))
    · have hym : y ∈ Icc (a+d) (b-d) := by
        constructor <;> linarith [lt_of_not_ge hleft,lt_of_not_ge hright]
      exact (hM i hi (p,y) ⟨hp,hym⟩).trans
        ((interior_bound_to_weight hc.le hCM.le hd hy hym (NL+NR)).trans (hmono AM hAMC))

/-- Equation (20), for actual derivative tensors in the fixed logarithmic
profile chart. The lower constant and the weight are independent of order. -/
theorem global_weighted_bounds {K : Set E} (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    {T : E × ℝ → V} {O : Set (E × ℝ)} (hO : IsOpen O)
    (hT : ContDiffOn ℝ ∞ T O) (hKO : K ×ˢ Icc a b ⊆ O)
    (hinterior : ∀ p ∈ K, ∀ y ∈ Ioo a b, T (p,y) ≠ 0)
    (FL : EdgeFactor K c (leftChart a T)) (FR : EdgeFactor K 4 (rightChart b T)) :
    (∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ y ∈ Ioo a b, m * weight c a b y ≤ ‖T (p,y)‖) ∧
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ K,
      ∀ y ∈ Ioo a b, ‖iteratedFDeriv ℝ i T (p,y)‖ ≤
        C * weight c a b y / edgeDistance a b y ^ N :=
  ⟨exists_global_lower_bound hK hab hc (hT.continuousOn.mono hKO) hinterior FL FR,
    exists_global_derivative_bound hK hKd hab hc hO hT hKO FL FR⟩

end CompactFamilies

section RadialChart

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def logChart (q : E × ℝ) : E × ℝ := (q.1,Real.log q.2)
noncomputable def radialPullback (T : E × ℝ → V) (q : E × ℝ) : V := T (logChart q)

theorem logChart_smooth : ContDiffOn ℝ ∞ (logChart (E := E))
    ((univ : Set E) ×ˢ Ioi (0 : ℝ)) := by
  intro q hq
  exact (contDiffAt_fst.prodMk (contDiffAt_snd.log hq.2.ne')).contDiffWithinAt

/-- The same weight controls genuine derivatives in `X`, not just in `log X`.
The change-of-variable constants are bounded on the fixed positive annulus. -/
theorem exists_radial_derivative_bound {K : Set E} (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    {T : E × ℝ → V} {O : Set (E × ℝ)} (hO : IsOpen O)
    (hT : ContDiffOn ℝ ∞ T O) (hKO : K ×ˢ Icc a b ⊆ O)
    (FL : EdgeFactor K c (leftChart a T)) (FR : EdgeFactor K 4 (rightChart b T))
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p ∈ K,
      ∀ X ∈ Ioo (Real.exp a) (Real.exp b),
        ‖iteratedFDeriv ℝ n (radialPullback T) (p,X)‖ ≤
          C * radialWeight c a b X / edgeDistance a b (Real.log X)^N := by
  obtain ⟨A,hA,N,hbound⟩ := exists_global_derivative_bound hK hKd hab hc hO hT hKO FL FR n
  let P := (univ : Set E) ×ˢ Ioi (0 : ℝ)
  have hP : IsOpen P := isOpen_univ.prod isOpen_Ioi
  have hlog : ContDiffOn ℝ ∞ (logChart (E := E)) P := logChart_smooth
  have hpos : K ×ˢ Icc (Real.exp a) (Real.exp b) ⊆ P := by
    intro q hq
    exact ⟨mem_univ _,(Real.exp_pos a).trans_le hq.2.1⟩
  obtain ⟨B,hB,hjets⟩ := compact_jets_bound hP hlog (hK.prod isCompact_Icc) hpos n
  let D := max 1 B
  have hD : 1 ≤ D := le_max_left _ _
  have hBD : B ≤ D := le_max_right _ _
  let C := (n.factorial : ℝ) * A * D^n
  have hC : 0 < C := mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) hA)
    (pow_pos (zero_lt_one.trans_le hD) _)
  let Q := P ∩ (logChart (E := E)) ⁻¹' O
  have hQ : IsOpen Q := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    filter_upwards [hP.mem_nhds hq.1,
      (hlog.contDiffAt (hP.mem_nhds hq.1)).continuousAt.eventually (hO.mem_nhds hq.2)] with r hr hrO
    exact ⟨hr,hrO⟩
  have hmap : MapsTo (logChart (E := E)) Q O := fun _ hq => hq.2
  refine ⟨C,hC,N,?_⟩
  intro p hp X hX
  have hXp : 0 < X := (Real.exp_pos a).trans hX.1
  have hy : Real.log X ∈ Ioo a b :=
    ⟨(Real.lt_log_iff_exp_lt hXp).2 hX.1,(Real.log_lt_iff_lt_exp hXp).2 hX.2⟩
  have hqx : (p,X) ∈ Q := ⟨⟨mem_univ _,hXp⟩,hKO ⟨hp,hy.1.le,hy.2.le⟩⟩
  have houter : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i T O (logChart (p,X))‖ ≤
        A * weight c a b (Real.log X) / edgeDistance a b (Real.log X)^N := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hO (hmap hqx)]
    exact hbound i hi p hp (Real.log X) hy
  have hinner : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (logChart (E := E)) Q (p,X)‖ ≤ D^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hQ hqx]
    exact (hjets i hin (p,X) ⟨hp,hX.1.le,hX.2.le⟩).trans
      (hBD.trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hi))
  have hh := norm_iteratedFDerivWithin_comp_le hT (hlog.mono inter_subset_left)
    (EdgeWeightJets.nat_le_infty n) hO.uniqueDiffOn hQ.uniqueDiffOn hmap hqx houter hinner
  rw [iteratedFDerivWithin_of_isOpen n hQ hqx] at hh
  calc
    ‖iteratedFDeriv ℝ n (radialPullback T) (p,X)‖ ≤
        (n.factorial : ℝ) * (A * weight c a b (Real.log X) /
          edgeDistance a b (Real.log X)^N) * D^n := hh
    _ = C * radialWeight c a b X / edgeDistance a b (Real.log X)^N := by
      rw [radialWeight,ite_eq_left hXp]
      dsimp [C]
      ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem radial_lower_bound {K : Set E} {a b c m : ℝ} {T : E × ℝ → V}
    (hlower : ∀ p ∈ K, ∀ y ∈ Ioo a b, m * weight c a b y ≤ ‖T (p,y)‖)
    {p : E} (hp : p ∈ K) {X : ℝ} (hX : X ∈ Ioo (Real.exp a) (Real.exp b)) :
    m * radialWeight c a b X ≤ ‖radialPullback T (p,X)‖ := by
  have hXp : 0 < X := (Real.exp_pos a).trans hX.1
  rw [radialWeight,ite_eq_left hXp]
  exact hlower p hp (Real.log X)
    ⟨(Real.lt_log_iff_exp_lt hXp).2 hX.1,(Real.log_lt_iff_lt_exp hXp).2 hX.2⟩

/-- The complete estimates in both fixed profile charts. -/
noncomputable def WeightedBounds (K : Set E) (c a b : ℝ) (T : E × ℝ → V) : Prop :=
  (∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ y ∈ Ioo a b, m * weight c a b y ≤ ‖T (p,y)‖) ∧
  (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ i ≤ n, ∀ p ∈ K,
    ∀ y ∈ Ioo a b, ‖iteratedFDeriv ℝ i T (p,y)‖ ≤
      C * weight c a b y / edgeDistance a b y ^ N) ∧
  (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p ∈ K,
    ∀ X ∈ Ioo (Real.exp a) (Real.exp b),
      ‖iteratedFDeriv ℝ n (radialPullback T) (p,X)‖ ≤
        C * radialWeight c a b X / edgeDistance a b (Real.log X)^N)

theorem weightedBounds_of_edge_factors {K : Set E} (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) {a b c : ℝ} (hab : a < b) (hc : 0 < c)
    {T : E × ℝ → V} {O : Set (E × ℝ)} (hO : IsOpen O)
    (hT : ContDiffOn ℝ ∞ T O) (hKO : K ×ˢ Icc a b ⊆ O)
    (hinterior : ∀ p ∈ K, ∀ y ∈ Ioo a b, T (p,y) ≠ 0)
    (FL : EdgeFactor K c (leftChart a T)) (FR : EdgeFactor K 4 (rightChart b T)) :
    WeightedBounds K c a b T :=
  ⟨exists_global_lower_bound hK hab hc (hT.continuousOn.mono hKO) hinterior FL FR,
    exists_global_derivative_bound hK hKd hab hc hO hT hKO FL FR,
    exists_radial_derivative_bound hK hKd hab hc hO hT hKO FL FR⟩

end RadialChart

section Directions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def tilt (v : ℝ × ℝ) : ℝ := v.2 / v.1

noncomputable def unitOfTilt (t : ℝ) : ℝ × ℝ :=
  ((Real.sqrt (1+t^2))⁻¹,t / Real.sqrt (1+t^2))

/-- Euclidean unit direction with positive angular component. -/
noncomputable def direction (v : ℝ × ℝ) : ℝ × ℝ := unitOfTilt (tilt v)

theorem unitOfTilt_smooth : ContDiff ℝ ∞ unitOfTilt := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (1+t^2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun t => by positivity)
  have hne (t : ℝ) : Real.sqrt (1+t^2) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  exact (hs.inv hne).prodMk (contDiff_id.div hs hne)

theorem unitOfTilt_normSq (t : ℝ) : (unitOfTilt t).1^2 + (unitOfTilt t).2^2 = 1 := by
  have hs : 0 < Real.sqrt (1+t^2) := Real.sqrt_pos.2 (by positivity)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1+t^2)
  dsimp [unitOfTilt]
  field_simp
  exact hsq.symm

theorem tilt_smul {r : ℝ} (hr : r ≠ 0) (v : ℝ × ℝ) : tilt (r • v) = tilt v := by
  simp only [tilt,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  exact mul_div_mul_left _ _ hr

theorem direction_smul {r : ℝ} (hr : r ≠ 0) (v : ℝ × ℝ) : direction (r • v) = direction v := by
  simp only [direction,tilt_smul hr]

theorem direction_smooth {O : Set (E × ℝ)} {B : E × ℝ → ℝ × ℝ}
    (hB : ContDiffOn ℝ ∞ B O) (hne : ∀ q ∈ O, (B q).1 ≠ 0) :
    ContDiffOn ℝ ∞ (fun q => direction (B q)) O :=
  unitOfTilt_smooth.comp_contDiffOn (hB.snd.div hB.fst hne)

omit [NormedSpace ℝ E] in
theorem positive_domain_open {O : Set (E × ℝ)} (hO : IsOpen O) {g : E × ℝ → ℝ}
    (hg : ContinuousOn g O) : IsOpen {q | q ∈ O ∧ 0 < g q} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  filter_upwards [hO.mem_nhds hq.1,
    (hg.continuousAt (hO.mem_nhds hq.1)).eventually (Ioi_mem_nhds hq.2)] with p hp hgp
  exact ⟨hp,hgp⟩

omit [NormedSpace ℝ E] in
theorem compact_positive_collar {K : Set E} (hK : IsCompact K)
    {O : Set (E × ℝ)} (hO : IsOpen O) {g : E × ℝ → ℝ} (hg : ContinuousOn g O)
    (hK0 : K ×ˢ ({0} : Set ℝ) ⊆ O) (hpos : ∀ p ∈ K, 0 < g (p,0)) :
    ∃ d ε : ℝ, 0 < d ∧ 0 < ε ∧ K ×ˢ Icc (0 : ℝ) d ⊆ O ∧
      ∀ p ∈ K, ∀ x ∈ Icc (0 : ℝ) d, ε ≤ g (p,x) := by
  let W := {q | q ∈ O ∧ 0 < g q}
  have hW : IsOpen W := positive_domain_open hO hg
  have hKW : K ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    have hx0 : x = 0 := hx
    subst x
    exact ⟨hK0 ⟨hp,rfl⟩,hpos p hp⟩
  obtain ⟨d,ε,hd,hε,hdom,hbound⟩ := compact_nonzero_collar hK hW
    (hg.mono (fun _ hq => hq.1)) hKW (fun p hp => (hpos p hp).ne')
  refine ⟨d,ε,hd,hε,fun q hq => (hdom hq).1,?_⟩
  intro p hp x hx
  have hh := hbound p hp x hx
  have hpos : 0 < g (p,x) := (hdom (show (p,x) ∈ K ×ˢ Icc (0 : ℝ) d from ⟨hp,hx⟩)).2
  simpa only [Real.norm_eq_abs,abs_of_pos hpos] using hh

/-- A positive angular edge factor yields a genuine smooth unit direction
for the stress, even where the stress itself vanishes at the edge. -/
theorem EdgeFactor.direction_collar {K : Set E} (hK : IsCompact K) {c : ℝ}
    {T : E × ℝ → ℝ × ℝ} (F : EdgeFactor K c T)
    (hfirst : ∀ p ∈ K, 0 < (F.coefficient (p,0)).1) :
    ∃ d : ℝ, ∃ W : Set (E × ℝ), 0 < d ∧ d < F.width ∧ IsOpen W ∧
      K ×ˢ Icc (0 : ℝ) d ⊆ W ∧
      ContDiffOn ℝ ∞ (fun q => direction (F.coefficient q)) W ∧
      (∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
        direction (T (p,x)) = direction (F.coefficient (p,x))) ∧
      (∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d → 0 < (T (p,x)).1) := by
  obtain ⟨d0,ε,hd0,hε,hdom,hbound⟩ := compact_positive_collar hK F.domain_open
    F.smooth.fst.continuousOn F.boundary_mem hfirst
  let W := {q | q ∈ F.domain ∧ 0 < (F.coefficient q).1}
  let d := min d0 (F.width/2)
  have hd : 0 < d := lt_min hd0 (half_pos F.width_pos)
  have hdd : d ≤ d0 := min_le_left _ _
  have hdw : d < F.width := (min_le_right _ _).trans_lt (half_lt_self F.width_pos)
  have hpos (p : E) (hp : p ∈ K) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      0 < (F.coefficient (p,x)).1 := hε.trans_le (hbound p hp x ⟨hx.1,hx.2.trans hdd⟩)
  refine ⟨d,W,hd,hdw,positive_domain_open F.domain_open F.smooth.fst.continuousOn,?_,?_,?_,?_⟩
  · exact fun q hq => ⟨hdom ⟨hq.1,hq.2.1,hq.2.2.trans hdd⟩,hpos q.1 hq.1 q.2 hq.2⟩
  · exact direction_smooth (F.smooth.mono (fun _ hq => hq.1)) (fun _ hq => hq.2.ne')
  · intro p hp x hx hxd
    rw [F.identity p hp x hx (hxd.trans_lt hdw)]
    exact direction_smul (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _)).ne' _
  · intro p hp x hx hxd
    rw [F.identity p hp x hx (hxd.trans_lt hdw),Prod.smul_fst,smul_eq_mul]
    exact mul_pos (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _)) (hpos p hp x ⟨hx.le,hxd⟩)

noncomputable def directionProjection (s t : ℝ) : ℝ := 1+s*t
noncomputable def directionGap (v s t : ℝ) : ℝ := 2*(directionProjection s t)^2 - (v-2)*(t-s)^2

theorem aligned_direction_margin (v s : ℝ) :
    0 < directionProjection s s ∧ 0 < directionGap v s s := by
  have hs : 0 < 1+s*s := by nlinarith [sq_nonneg s]
  constructor
  · exact hs
  · simpa only [directionGap,directionProjection,sub_self,zero_pow (by norm_num : 2 ≠ 0),
      mul_zero,sub_zero] using mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hs)

omit [NormedSpace ℝ E] in
/-- Equality of the boundary direction with the shear direction gives a
strict cone margin on one uniform collar by continuity and compactness. -/
theorem aligned_direction_collar {K : Set E} (hK : IsCompact K)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hK0 : K ×ˢ ({0} : Set ℝ) ⊆ O)
    {v s t : E × ℝ → ℝ} (hv : ContinuousOn v O) (hs : ContinuousOn s O)
    (ht : ContinuousOn t O) (halign : ∀ p ∈ K, t (p,0) = s (p,0)) :
    ∃ d ε : ℝ, 0 < d ∧ 0 < ε ∧ K ×ˢ Icc (0 : ℝ) d ⊆ O ∧
      ∀ p ∈ K, ∀ x ∈ Icc (0 : ℝ) d,
        ε ≤ directionProjection (s (p,x)) (t (p,x)) ∧
        ε ≤ directionGap (v (p,x)) (s (p,x)) (t (p,x)) := by
  have hp : ContinuousOn (fun q => directionProjection (s q) (t q)) O :=
    continuousOn_const.add (hs.mul ht)
  have hg : ContinuousOn (fun q => directionGap (v q) (s q) (t q)) O :=
    (continuousOn_const.mul (hp.pow 2)).sub ((hv.sub continuousOn_const).mul ((ht.sub hs).pow 2))
  obtain ⟨dp,ep,hdp,hep,hop,hpbound⟩ := compact_positive_collar hK hO hp hK0 (by
    intro p hp
    rw [halign p hp]
    exact (aligned_direction_margin (v (p,0)) (s (p,0))).1)
  obtain ⟨dg,eg,hdg,heg,hog,hgbound⟩ := compact_positive_collar hK hO hg hK0 (by
    intro p hp
    rw [halign p hp]
    exact (aligned_direction_margin (v (p,0)) (s (p,0))).2)
  refine ⟨min dp dg,min ep eg,lt_min hdp hdg,lt_min hep heg,?_,?_⟩
  · exact fun q hq => hop ⟨hq.1,hq.2.1,hq.2.2.trans (min_le_left _ _)⟩
  · intro p hp x hx
    exact ⟨(min_le_left _ _).trans (hpbound p hp x ⟨hx.1,hx.2.trans (min_le_left _ _)⟩),
      (min_le_right _ _).trans (hgbound p hp x ⟨hx.1,hx.2.trans (min_le_right _ _)⟩)⟩

/-- The actual stress direction has a smooth extension and a uniform strict
cone margin when the genuine edge factor is aligned with the limiting shear. -/
theorem EdgeFactor.aligned_collar {K : Set E} (hK : IsCompact K) {c : ℝ}
    {T : E × ℝ → ℝ × ℝ} (F : EdgeFactor K c T)
    (hfirst : ∀ p ∈ K, 0 < (F.coefficient (p,0)).1)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hK0 : K ×ˢ ({0} : Set ℝ) ⊆ O)
    {v s : E × ℝ → ℝ} (hv : ContinuousOn v O) (hs : ContinuousOn s O)
    (halign : ∀ p ∈ K, tilt (F.coefficient (p,0)) = s (p,0)) :
    ∃ d ε : ℝ, ∃ W : Set (E × ℝ), 0 < d ∧ d < F.width ∧ 0 < ε ∧ IsOpen W ∧
      K ×ˢ Icc (0 : ℝ) d ⊆ W ∧
      ContDiffOn ℝ ∞ (fun q => direction (F.coefficient q)) W ∧
      (∀ p ∈ K, ∀ x ∈ Icc (0 : ℝ) d,
        ε ≤ directionProjection (s (p,x)) (tilt (F.coefficient (p,x))) ∧
        ε ≤ directionGap (v (p,x)) (s (p,x)) (tilt (F.coefficient (p,x)))) ∧
      (∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
        direction (T (p,x)) = direction (F.coefficient (p,x)) ∧
        ε ≤ directionProjection (s (p,x)) (tilt (T (p,x))) ∧
        ε ≤ directionGap (v (p,x)) (s (p,x)) (tilt (T (p,x)))) := by
  let W := {q | q ∈ F.domain ∩ O ∧ 0 < (F.coefficient q).1}
  have hW : IsOpen W := positive_domain_open (F.domain_open.inter hO)
    (F.smooth.fst.continuousOn.mono inter_subset_left)
  have hKW : K ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    have hx0 : x = 0 := hx
    subst x
    exact ⟨⟨F.boundary_mem ⟨hp,rfl⟩,hK0 ⟨hp,rfl⟩⟩,hfirst p hp⟩
  have hBW : ContDiffOn ℝ ∞ F.coefficient W := F.smooth.mono (fun _ hq => hq.1.1)
  have ht : ContinuousOn (fun q => tilt (F.coefficient q)) W :=
    (hBW.snd.div hBW.fst (fun _ hq => hq.2.ne')).continuousOn
  obtain ⟨d0,ε,hd0,hε,hdom,hmargin⟩ := aligned_direction_collar hK hW hKW
    (hv.mono (fun _ hq => hq.1.2)) (hs.mono (fun _ hq => hq.1.2)) ht halign
  let d := min d0 (F.width/2)
  have hd : 0 < d := lt_min hd0 (half_pos F.width_pos)
  have hdd : d ≤ d0 := min_le_left _ _
  have hdw : d < F.width := (min_le_right _ _).trans_lt (half_lt_self F.width_pos)
  refine ⟨d,ε,W,hd,hdw,hε,hW,?_,direction_smooth hBW (fun _ hq => hq.2.ne'),?_,?_⟩
  · exact fun q hq => hdom ⟨hq.1,hq.2.1,hq.2.2.trans hdd⟩
  · exact fun p hp x hx => hmargin p hp x ⟨hx.1,hx.2.trans hdd⟩
  · intro p hp x hx hxd
    have he : tilt (T (p,x)) = tilt (F.coefficient (p,x)) := by
      rw [F.identity p hp x hx (hxd.trans_lt hdw)]
      exact tilt_smul (div_pos (FlatCutoff.edge_pos _ hx) (pow_pos hx _)).ne' _
    refine ⟨?_,?_⟩
    · exact congrArg unitOfTilt he
    · rw [he]
      exact hmargin p hp x ⟨hx.le,hxd.trans hdd⟩

/-- A smooth extension of the actual unit direction, with strict margins
for the true homogeneous cone inequalities on a full closed edge collar. -/
noncomputable def HasStrictDirectionCollar (K : Set E) (T B : E × ℝ → ℝ × ℝ)
    (v s : E × ℝ → ℝ) (width : ℝ) : Prop :=
  ∃ d ε : ℝ, ∃ W : Set (E × ℝ), 0 < d ∧ d < width ∧ 0 < ε ∧ IsOpen W ∧
    K ×ˢ Icc (0 : ℝ) d ⊆ W ∧
    ContDiffOn ℝ ∞ (fun q => direction (B q)) W ∧
    (∀ p ∈ K, ∀ x ∈ Icc (0 : ℝ) d,
      ε ≤ directionProjection (s (p,x)) (tilt (B (p,x))) ∧
      ε ≤ directionGap (v (p,x)) (s (p,x)) (tilt (B (p,x)))) ∧
    (∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
      direction (T (p,x)) = direction (B (p,x)) ∧
      ε ≤ directionProjection (s (p,x)) (tilt (T (p,x))) ∧
      ε ≤ directionGap (v (p,x)) (s (p,x)) (tilt (T (p,x))))

/-- The directional certificate together with the speed condition `v_s > 2`
on one common positive-width collar. -/
noncomputable def HasTrueDirectionCollar (K : Set E) (T B : E × ℝ → ℝ × ℝ)
    (v s : E × ℝ → ℝ) (width : ℝ) : Prop :=
  HasStrictDirectionCollar K T B v s width ∧
  ∃ d ε : ℝ, 0 < d ∧ d < width ∧ 0 < ε ∧
    ∀ p ∈ K, ∀ x : ℝ, 0 < x → x ≤ d →
      ε ≤ v (p,x)-2 ∧
      ε ≤ directionProjection (s (p,x)) (tilt (T (p,x))) ∧
      ε ≤ directionGap (v (p,x)) (s (p,x)) (tilt (T (p,x)))

theorem HasStrictDirectionCollar.true_of_speed {K : Set E} (hK : IsCompact K)
    {T B : E × ℝ → ℝ × ℝ} {v s : E × ℝ → ℝ} {width : ℝ}
    (hdir : HasStrictDirectionCollar K T B v s width)
    {O : Set (E × ℝ)} (hO : IsOpen O) (hK0 : K ×ˢ ({0} : Set ℝ) ⊆ O)
    (hv : ContinuousOn v O) (hvs : ∀ p ∈ K, 2 < v (p,0)) :
    HasTrueDirectionCollar K T B v s width := by
  refine ⟨hdir,?_⟩
  obtain ⟨d1,e1,W,hd1,hdw,he1,hW,hKW,hsm,hbd,hactual⟩ := hdir
  obtain ⟨d2,e2,hd2,he2,hKO,hvbd⟩ := compact_positive_collar hK hO
    (hv.sub continuousOn_const) hK0 (fun p hp => sub_pos.mpr (hvs p hp))
  refine ⟨min d1 d2,min e1 e2,lt_min hd1 hd2,(min_le_left _ _).trans_lt hdw,
    lt_min he1 he2,?_⟩
  intro p hp x hx hxd
  obtain ⟨_,hproj,hgap⟩ := hactual p hp x hx (hxd.trans (min_le_left _ _))
  exact ⟨(min_le_right _ _).trans (hvbd p hp x ⟨hx.le,hxd.trans (min_le_right _ _)⟩),
    (min_le_left _ _).trans hproj,(min_le_left _ _).trans hgap⟩

end Directions

section ActualActivation

open ProfileHistories StressActivation ActivationCone

theorem actual_shear_coordinates_smooth (T κ : ℝ) {X0 : ℝ} (hX0 : 0 < X0)
    {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (actualP1 T κ L) (logDomain J hJ).carrier ∧
    ContDiffOn ℝ ∞ (actualP2 T κ X0 L U) (logDomain J hJ).carrier := by
  obtain ⟨hA,hB⟩ := reference_coordinates_smooth hX0 hJ hL hU
  have hD : ContDiffOn ℝ ∞ (fun p : Point => damping T κ p.1) (logDomain J hJ).carrier :=
    ((damping_smooth T κ).comp contDiff_fst).contDiffOn
  have hR := hL.exp.div (activatedAngular_smooth T κ hJ hL)
    (fun q _ => (activatedAngular_pos T κ L q).ne')
  refine ⟨(hD.mul hA).congr ?_,((hD.mul hB).mul hR).congr ?_⟩
  · rintro ⟨y,η⟩ hη
    exact actualP1_eq T κ hJ hL y hη.2
  · rintro ⟨y,η⟩ hη
    exact actualP2_eq T κ hX0 hJ hU y hη.2

theorem actual_shear_coordinates_zero {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {X0 : ℝ} (hX0 : 0 < X0) {J : Set ℝ} (hJ : IsOpen J) {L U : Field}
    (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier) {η : ℝ} (hη : η ∈ J) :
    actualP1 T κ L (0,η) = referenceP1 L (0,η) ∧
    actualP2 T κ X0 L U (0,η) = referenceP2 X0 L U (0,η) := by
  have hD : damping T κ 0 = 1 := by rw [damping,activation_zero hT κ le_rfl]; ring
  have hF : activatedAngular T κ L (0,η) = referenceAngular L (0,η) := by
    simp [activatedAngular,controlled,primitive,referenceAngular]
  rw [actualP1_eq T κ hJ hL 0 hη,actualP2_eq T κ hX0 hJ hU 0 hη,hD,hF]
  simp [(Real.exp_pos (L (0,η))).ne',referenceAngular]

theorem actual_shear_domain {T : ℝ} (hT : 0 < T) (κ : ℝ)
    {X0 : ℝ} (hX0 : 0 < X0) {J K : Set ℝ} (hJ : IsOpen J) (hKJ : K ⊆ J)
    {L U : Field} (hL : ContDiffOn ℝ ∞ L (logDomain J hJ).carrier)
    (hU : ContDiffOn ℝ ∞ U (logDomain J hJ).carrier)
    (hA0 : ∀ η ∈ K, 0 < referenceP1 L (0,η)) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ K ×ˢ ({0} : Set ℝ) ⊆ O ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => shearSize T κ X0 L U (q.2,q.1)) O ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => shearSlope T κ X0 L U (q.2,q.1)) O := by
  obtain ⟨hA,hB⟩ := actual_shear_coordinates_smooth T κ hX0 hJ hL hU
  have hm : MapsTo (fun q : ℝ × ℝ => (q.2,q.1)) (J ×ˢ (univ : Set ℝ))
      (logDomain J hJ).carrier := fun q hq => ⟨mem_univ _,hq.1⟩
  have hAs := hA.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn hm
  have hBs := hB.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn hm
  let O := {q : ℝ × ℝ | q ∈ J ×ˢ (univ : Set ℝ) ∧ 0 < actualP1 T κ L (q.2,q.1)}
  have hO : IsOpen O := positive_domain_open (hJ.prod isOpen_univ) hAs.continuousOn
  have hAO := hAs.mono (show O ⊆ J ×ˢ (univ : Set ℝ) from fun _ hq => hq.1)
  have hBO := hBs.mono (show O ⊆ J ×ˢ (univ : Set ℝ) from fun _ hq => hq.1)
  have hn : ∀ q ∈ O, actualP1 T κ L (q.2,q.1) ≠ 0 := fun q hq => hq.2.ne'
  refine ⟨O,hO,?_,hAO.add ((hBO.pow 2).div hAO hn),hBO.div hAO hn⟩
  rintro ⟨η,x⟩ ⟨hη,hx⟩
  have hx0 : x = 0 := hx
  subst x
  refine ⟨⟨hKJ hη,mem_univ _⟩,?_⟩
  rw [(actual_shear_coordinates_zero hT κ hX0 hJ hL hU (hKJ hη)).1]
  exact hA0 η hη

/-- Fixed activation parameters expose the actual Gaussian coefficient `T²`.
The coefficient is smooth through the attachment. -/
noncomputable def activationCoefficient (T κ : ℝ) (D : ActivationBounds.ScaledPoint → ℝ × ℝ)
    (q : ℝ × ℝ) : ℝ × ℝ :=
  ((1-κ) / stepDenominator T q.2) • D ((κ,T),(q.2/T,q.1))

theorem activationCoefficient_smooth {J : Set ℝ} (T κ : ℝ)
    {D : ActivationBounds.ScaledPoint → ℝ × ℝ}
    (hD : ContDiffOn ℝ ∞ D (ActivationBounds.scaledDomain J)) :
    ContDiffOn ℝ ∞ (activationCoefficient T κ D) (J ×ˢ (univ : Set ℝ)) := by
  have hm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((κ,T),(q.2/T,q.1))) :=
    contDiff_const.prodMk ((contDiff_snd.div_const T).prodMk contDiff_fst)
  have hmap : MapsTo (fun q : ℝ × ℝ => ((κ,T),(q.2/T,q.1)))
      (J ×ˢ (univ : Set ℝ)) (ActivationBounds.scaledDomain J) :=
    fun q hq => ⟨mem_univ _,mem_univ _,hq.1⟩
  have hb := hD.comp hm.contDiffOn hmap
  exact (contDiffOn_const.div ((stepDenominator_smooth T).comp contDiff_snd).contDiffOn
    (fun q _ => (stepDenominator_pos T q.2).ne')).smul hb

theorem activationCoefficient_edge {T κ : ℝ}
    {D : ActivationBounds.ScaledPoint → ℝ × ℝ} (η : ℝ) :
    activationCoefficient T κ D (η,0) = ((1-κ) / stepDenominator T 0) • D ((κ,T),(0,η)) := by
  simp only [activationCoefficient,zero_div]

/-- This is the factor in the actual activation stress identity, after its
scaled coordinate is converted back to the logarithmic edge distance. -/
noncomputable def activationEdgeFactor {J K : Set ℝ} (hJ : IsOpen J) (hKJ : K ⊆ J)
    {T κ d : ℝ} (hT : 0 < T) (hκ : κ < 1) (hd : 0 < d)
    {D : ActivationBounds.ScaledPoint → ℝ × ℝ}
    (hD : ContDiffOn ℝ ∞ D (ActivationBounds.scaledDomain J))
    (hD0 : ∀ η ∈ K, D ((κ,T),(0,η)) ≠ 0) {S : ℝ × ℝ → ℝ × ℝ}
    (hfactor : ∀ u η : ℝ, T*u ∈ Icc (0 : ℝ) d → η ∈ K →
      S (T*u,η) = (activation 1 κ u * (D ((κ,T),(u,η))).1,
        activation 1 κ u * (D ((κ,T),(u,η))).2)) :
    EdgeFactor K (T^2) (fun q => S (q.2,q.1)) where
  coefficient := activationCoefficient T κ D
  order := 0
  width := d
  width_pos := hd
  domain := J ×ˢ (univ : Set ℝ)
  domain_open := hJ.prod isOpen_univ
  boundary_mem := fun q hq => ⟨hKJ hq.1,mem_univ _⟩
  smooth := activationCoefficient_smooth T κ hD
  boundary_ne_zero := by
    intro η hη
    rw [activationCoefficient_edge]
    exact smul_ne_zero (div_pos (sub_pos.mpr hκ) (stepDenominator_pos T 0)).ne' (hD0 η hη)
  identity := by
    intro η hη x hx hxd
    have hTx : T*(x/T)=x := by field_simp
    have hf := hfactor (x/T) η (by rw [hTx]; exact ⟨hx.le,hxd.le⟩) hη
    rw [hTx] at hf
    have ha : activation 1 κ (x/T) = activation T κ x := by
      rw [← ActivationBounds.activation_scaled hT.ne',hTx]
    rw [ha,activation_flat_form hT] at hf
    rw [hf]
    ext <;> simp only [activationCoefficient,pow_zero,div_one,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      <;> ring

theorem exists_natural_activation_factor {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2*δ < ReferencePath.rampLimit)
    {T κ : ℝ} (hT : 0 < T) (hκ : κ < 1) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    Nonempty (EdgeFactor (Icc (-1 : ℝ) 1) (T^2)
      (fun q => activatedStress h N.endpoint I L U T κ (q.2,q.1))) := by
  dsimp only
  obtain ⟨D,ε,hD,hε,hbound,hfactor⟩ := natural_activation_direction hΛ F hP0 hsmall hδ hδlim
  refine ⟨activationEdgeFactor ReferencePath.parameterInterval_open
    NaturalAxisCoefficients.original_interval_interior hT hκ hδ hD ?_ (hfactor T hT κ)⟩
  intro η hη he
  have hh := (hbound κ T η hη).1
  rw [he] at hh
  change ε ≤ 0 at hh
  linarith

/-- The coefficient is constructed from the actual reference histories. Its
boundary tilt is exactly the reference shear tilt, rather than an assumed
directional estimate. -/
theorem exists_natural_activation_factor_aligned {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2*δ < ReferencePath.rampLimit)
    {T κ : ℝ} (hT : 0 < T) (hκ : κ < 1) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (T^2)
        (fun q => activatedStress h N.endpoint I L U T κ (q.2,q.1)),
      (∀ η ∈ Icc (-1 : ℝ) 1, 0 < (G.coefficient (η,0)).1) ∧
      ∀ η ∈ Icc (-1 : ℝ) 1, tilt (G.coefficient (η,0)) =
        referenceP2 N.endpoint L U (0,η) / referenceP1 L (0,η) := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let L := FromReference.refLog N δ
  let U := FromReference.refAxial N δ
  let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
  have hL := FromReference.refLog_smooth N hδ hδlim
  have hU := FromReference.refAxial_smooth N hδ hδlim
  have hi := ActivationStocks.FromReference.initial_smooth N hδ hδlim P0 hP0
  have hKJ : Icc (-1 : ℝ) 1 ⊆ ReferencePath.parameterInterval :=
    NaturalAxisCoefficients.original_interval_interior
  have hcoef : ∀ η ∈ ReferencePath.parameterInterval, NaturalAxisData.L h η ≠ 0 := by
    intro η hη
    exact (NaturalAxisCoefficients.L_pos_on_window (NaturalAxisRange.ofSmall hsmall) ⟨hη.1.le,hη.2.le⟩).ne'
  have hm : ∀ y ∈ Icc (0 : ℝ) δ, ∀ η ∈ Icc (-1 : ℝ) 1,
      ActivationStocks.logViewOne h N.endpoint (referenceAngular L)
        (logHistory N.endpoint I (referenceAngular L) U) (y,η) = referenceP1 L (y,η) ∧
      ActivationStocks.logViewTwo h N.endpoint (referenceAngular L) U
        (logHistory N.endpoint I (referenceAngular L) U) (y,η) = referenceP2 N.endpoint L U (y,η) := by
    intro y hy η hη
    exact natural_reference_log_match hΛ F.profile.family hP0 hsmall hδ hδlim hy.2 hη
  obtain ⟨D,hD,hedge,hfactor⟩ := exists_actual_stress_direction h N.endpoint_pos I
    ReferencePath.parameterInterval_open hKJ hL hU hi hcoef hm
  obtain ⟨τ,α,M,hτ,_,hα,_,hb⟩ := natural_reference_bounds hΛ F hδ hδlim
  have hApos : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < referenceP1 L (0,η) := by
    intro η hη
    exact hα.trans_le (hb 0 ⟨le_rfl,hτ.le⟩ η hη).1
  have hDfirst : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < (D ((κ,T),(0,η))).1 := by
    intro η hη
    rw [hedge]
    exact mul_pos (Real.exp_pos _) (hApos η hη)
  have hD0 : ∀ η ∈ Icc (-1 : ℝ) 1, D ((κ,T),(0,η)) ≠ 0 := by
    intro η hη he
    have hh := hDfirst η hη
    rw [he] at hh
    exact lt_irrefl 0 hh
  let G := activationEdgeFactor ReferencePath.parameterInterval_open hKJ hT hκ hδ hD hD0
    (hfactor T hT κ)
  refine ⟨G,?_,?_⟩
  · intro η hη
    change 0 < (activationCoefficient T κ D (η,0)).1
    rw [activationCoefficient_edge,Prod.smul_fst,smul_eq_mul]
    exact mul_pos (div_pos (sub_pos.mpr hκ) (stepDenominator_pos T 0)) (hDfirst η hη)
  · intro η hη
    change tilt (activationCoefficient T κ D (η,0)) = _
    rw [activationCoefficient_edge,tilt_smul
      (div_pos (sub_pos.mpr hκ) (stepDenominator_pos T 0)).ne',hedge]
    exact mul_div_mul_left _ _ (Real.exp_pos _).ne'

/-- The initial ACT stress has a genuine smooth unit-direction extension and
a strict cone margin relative to its actual shear. -/
theorem natural_activation_strict_direction {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2*δ < ReferencePath.rampLimit)
    {T κ : ℝ} (hT : 0 < T) (hκ : κ < 1) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    let S := fun q : ℝ × ℝ => activatedStress h N.endpoint I L U T κ (q.2,q.1)
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (T^2) S,
      HasStrictDirectionCollar (Icc (-1 : ℝ) 1) S G.coefficient
        (fun q => shearSize T κ N.endpoint L U (q.2,q.1))
        (fun q => shearSlope T κ N.endpoint L U (q.2,q.1)) G.width := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let L := FromReference.refLog N δ
  let U := FromReference.refAxial N δ
  have hL := FromReference.refLog_smooth N hδ hδlim
  have hU := FromReference.refAxial_smooth N hδ hδlim
  have hKJ : Icc (-1 : ℝ) 1 ⊆ ReferencePath.parameterInterval :=
    NaturalAxisCoefficients.original_interval_interior
  obtain ⟨G,hGfirst,hGalign⟩ := exists_natural_activation_factor_aligned hΛ F hP0 hsmall hδ hδlim hT hκ
  obtain ⟨τ,α,M,hτ,_,hα,_,hb⟩ := natural_reference_bounds hΛ F hδ hδlim
  have hA0 : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < referenceP1 L (0,η) := by
    intro η hη
    exact hα.trans_le (hb 0 ⟨le_rfl,hτ.le⟩ η hη).1
  obtain ⟨O,hO,hKO,hv,hs⟩ := actual_shear_domain hT κ N.endpoint_pos
    ReferencePath.parameterInterval_open hKJ hL hU hA0
  refine ⟨G,G.aligned_collar isCompact_Icc hGfirst hO hKO hv.continuousOn hs.continuousOn ?_⟩
  intro η hη
  obtain ⟨hAz,hBz⟩ := actual_shear_coordinates_zero hT κ N.endpoint_pos
    ReferencePath.parameterInterval_open hL hU (hKJ hη)
  rw [hGalign η hη]
  change referenceP2 N.endpoint L U (0,η) / referenceP1 L (0,η) =
    actualP2 T κ N.endpoint L U (0,η) / actualP1 T κ L (0,η)
  rw [hAz,hBz]

theorem natural_activation_true_direction {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2*δ < ReferencePath.rampLimit)
    {T κ : ℝ} (hT : 0 < T) (hκ : κ < 1) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    let S := fun q : ℝ × ℝ => activatedStress h N.endpoint I L U T κ (q.2,q.1)
    ∃ G : EdgeFactor (Icc (-1 : ℝ) 1) (T^2) S,
      HasTrueDirectionCollar (Icc (-1 : ℝ) 1) S G.coefficient
        (fun q => shearSize T κ N.endpoint L U (q.2,q.1))
        (fun q => shearSlope T κ N.endpoint L U (q.2,q.1)) G.width := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let L := FromReference.refLog N δ
  let U := FromReference.refAxial N δ
  have hL := FromReference.refLog_smooth N hδ hδlim
  have hU := FromReference.refAxial_smooth N hδ hδlim
  have hKJ : Icc (-1 : ℝ) 1 ⊆ ReferencePath.parameterInterval :=
    NaturalAxisCoefficients.original_interval_interior
  obtain ⟨G,hdir⟩ := natural_activation_strict_direction hΛ F hP0 hsmall hδ hδlim hT hκ
  obtain ⟨τ,α,M,hτ,_,hα,_,hb⟩ := natural_reference_bounds hΛ F hδ hδlim
  have hA0 : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < referenceP1 L (0,η) := by
    intro η hη
    exact hα.trans_le (hb 0 ⟨le_rfl,hτ.le⟩ η hη).1
  obtain ⟨O,hO,hKO,hv,hs⟩ := actual_shear_domain hT κ N.endpoint_pos
    ReferencePath.parameterInterval_open hKJ hL hU hA0
  refine ⟨G,hdir.true_of_speed isCompact_Icc hO hKO hv.continuousOn ?_⟩
  intro η hη
  obtain ⟨hAz,hBz⟩ := actual_shear_coordinates_zero hT κ N.endpoint_pos
    ReferencePath.parameterInterval_open hL hU (hKJ hη)
  change 2 < shearSize T κ N.endpoint L U (0,η)
  unfold shearSize
  rw [hAz,hBz]
  have hh := (hb 0 ⟨le_rfl,hτ.le⟩ η hη).2.1
  linarith

end ActualActivation

section ActualTerminal

open TerminalEdgeFactor OutgoingTail

/-- The actual terminal stress uses coefficient `4` and inverse-cubic order.
The smooth factor is defined through the closed parameter endpoints. -/
noncomputable def terminalEdgeFactor {C : ℝ} (hC : 0 < C) (d : TailData) (y0 w : ℝ) (hw : 0 < w) :
    EdgeFactor (Icc (-1 : ℝ) 1) 4 (profileStress C d y0) where
  coefficient := profileStressFactor C d y0
  order := 3
  width := w
  width_pos := hw
  domain := univ
  domain_open := isOpen_univ
  boundary_mem := subset_univ _
  smooth := (profileStressFactor_contDiff C d y0).contDiffOn
  boundary_ne_zero := fun _ hη => profileStressFactor_zero_ne hC d y0 hη
  identity := fun η _ x _ _ => profileStress_factorization C d y0 (η,x)

theorem terminal_strict_direction {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    HasStrictDirectionCollar (Icc (-1 : ℝ) 1) (profileStress C d y0)
      (profileStressFactor C d y0) (profileSpeed C d y0) (fun _ => 0) 1 := by
  let F := terminalEdgeFactor hC d y0 1 zero_lt_one
  have hfirst : ∀ η ∈ Icc (-1 : ℝ) 1, 0 < (F.coefficient (η,0)).1 := by
    intro η hη
    exact profileAngularFactor_zero_pos hC d y0 hη
  have hK0 : Icc (-1 : ℝ) 1 ×ˢ ({0} : Set ℝ) ⊆ profileDomain C d y0 :=
    fun q hq => profileDomain_contains_closed hC d y0 ⟨hq.1,mem_univ _⟩
  apply F.aligned_collar isCompact_Icc hfirst (profileDomain_open C d y0) hK0
    (profileSpeed_contDiffOn C d y0).continuousOn continuousOn_const
  intro η hη
  change tilt (profileStressFactor C d y0 (η,0)) = 0
  rw [profileStressFactor_zero]
  exact zero_div _

theorem terminal_true_direction {C : ℝ} (hC : 0 < C) (d : TailData) (y0 : ℝ) :
    HasTrueDirectionCollar (Icc (-1 : ℝ) 1) (profileStress C d y0)
      (profileStressFactor C d y0) (profileSpeed C d y0) (fun _ => 0) 1 :=
  (terminal_strict_direction hC d y0).true_of_speed isCompact_Icc (profileDomain_open C d y0)
    (fun _ hq => profileDomain_contains_closed hC d y0 ⟨hq.1,mem_univ _⟩)
    (profileSpeed_contDiffOn C d y0).continuousOn
    (fun _ hη => profileSpeed_zero_gt_two hC d y0 hη)

end ActualTerminal

section ActualJoin

open ProfileHistories StressActivation ActivationCone TerminalEdgeFactor OutgoingTail

/-- Equation (20) for a joined nominal stress with exact ACT and terminal
edge identities. The only remaining global inputs are genuine smoothness
and interior nonvanishing of that joined stress. -/
theorem actual_edge_join {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    (hP0 : ContDiff ℝ ∞ P0) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2*δ < ReferencePath.rampLimit)
    {T κ : ℝ} (hT : 0 < T) (hκ : κ < 1)
    {Ct : ℝ} (hCt : 0 < Ct) (dt : TailData) (y0 : ℝ)
    {a b : ℝ} (hab : a < b) {S : ℝ × ℝ → ℝ × ℝ} {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hS : ContDiffOn ℝ ∞ S O)
    (hSO : Icc (-1 : ℝ) 1 ×ˢ Icc a b ⊆ O)
    (hinterior : ∀ η ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Ioo a b, S (η,y) ≠ 0)
    {wL wR : ℝ} (hwL : 0 < wL) (hwR : 0 < wR) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let L := FromReference.refLog N δ
    let U := FromReference.refAxial N δ
    let I := ActivationStocks.FromReference.initial N hδ hδlim P0 hP0
    (∀ η ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x < wL →
      leftChart a S (η,x) = activatedStress h N.endpoint I L U T κ (x,η)) →
    (∀ η ∈ Icc (-1 : ℝ) 1, ∀ x : ℝ, 0 < x → x < wR →
      rightChart b S (η,x) = profileStress Ct dt y0 (η,x)) →
    WeightedBounds (Icc (-1 : ℝ) 1) (T^2) a b S := by
  dsimp only
  intro hleft hright
  obtain ⟨FL0⟩ := exists_natural_activation_factor hΛ F hP0 hsmall hδ hδlim hT hκ
  let FL : EdgeFactor (Icc (-1 : ℝ) 1) (T^2) (leftChart a S) :=
    FL0.transfer (lt_min hwL FL0.width_pos) (min_le_right wL FL0.width)
      (fun η hη x hx hxw => hleft η hη x hx (hxw.trans_le (min_le_left _ _)))
  let FR0 := terminalEdgeFactor hCt dt y0 wR hwR
  let FR : EdgeFactor (Icc (-1 : ℝ) 1) 4 (rightChart b S) := FR0.transfer hwR le_rfl hright
  exact weightedBounds_of_edge_factors isCompact_Icc (uniqueDiffOn_Icc (by norm_num))
    hab (sq_pos_of_pos hT) hO hS hSO hinterior FL FR

end ActualJoin

end NavierStokes.ActiveAnnulusWeight

end
