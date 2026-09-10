import NavierStokes.GenericSupportedPolynomial

/-! # Differential polynomials with coefficients smooth only on factor supports

The literal coefficient is retained. At points outside the common factor
region the monomial has a zero germ, making its product smooth with every
jet zero even when the coefficient itself is singular or nonsmooth there.
-/

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {l : Filter D} {q : D → ℝ} {U S : Set D}

theorem norm_jet_mul_at {f g : D → ℝ} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ)
    {A B : ℝ} (hA : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hB : ∀ k ≤ m, ‖iteratedFDeriv ℝ k g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => f y * g y) x‖ ≤ 2 ^ m * A * B := by
  obtain ⟨V, hV, hxV, hfV⟩ := hf.contDiffOn' (m := (m : WithTop ℕ∞)) (by simp) (by simp)
  obtain ⟨W, hW, hxW, hgW⟩ := hg.contDiffOn' (m := (m : WithTop ℕ∞)) (by simp) (by simp)
  simp only [Set.insert_eq_of_mem (Set.mem_univ x), univ_inter] at hfV hgW
  have hfs : ContDiffOn ℝ m f (V ∩ W) := hfV.mono inter_subset_left
  have hgs : ContDiffOn ℝ m g (V ∩ W) := hgW.mono inter_subset_right
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  apply (JetBounds.norm_iteratedFDeriv_mul_le_on (hV.inter hW) hfs hgs
    ⟨hxV, hxW⟩ (le_refl (m : WithTop ℕ∞))).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hA i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hB (m - i) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA0)
    _ = 2 ^ m * A * B := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose m

/-- The product estimate only needs smoothness at the points in the filter. -/
theorem rate_mul_at {f g : D → ℝ}
    (hq : ∀ᶠ x in l, 0 < q x)
    (hf : ∀ᶠ x in l, ContDiffAt ℝ ∞ f x)
    (hg : ∀ᶠ x in l, ContDiffAt ℝ ∞ g x)
    {m : ℕ} {r s : ℝ} (hr : FiniteJetRate l q f m r)
    (hs : FiniteJetRate l q g m s) :
    JetRate l q (fun x => f x * g x) m (r + s) := by
  obtain ⟨A, hA, hbA⟩ := hr
  obtain ⟨B, hB, hbB⟩ := hs
  refine ⟨2 ^ m * A * B, by positivity, ?_⟩
  filter_upwards [hq, hf, hg, hbA, hbB] with x hqx hfx hgx hAx hBx
  calc
    _ ≤ 2 ^ m * (A * q x ^ r) * (B * q x ^ s) := norm_jet_mul_at hfx hgx m hAx hBx
    _ = (2 ^ m * A * B) * q x ^ (r + s) := by rw [Real.rpow_add hqx]; ring

omit [NormedSpace ℝ D] in
theorem mul_zero_germ {c f : D → ℝ} {x : D}
    (hzero : f =ᶠ[𝓝 x] (fun _ => 0)) :
    (fun y => c y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hzero] with y hy
  simp only [hy, mul_zero]

theorem iteratedFDeriv_mul_eq_zero_of_zero_germ {c f : D → ℝ} {x : D}
    (hzero : f =ᶠ[𝓝 x] (fun _ => 0)) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => c y * f y) x = 0 := by
  have heq := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (mul_zero_germ (c := c) hzero) m).self_of_nhds
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using heq

theorem smooth_mul_of_support_local {c f : D → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hc : ∀ x ∈ U, x ∈ S → ContDiffAt ℝ ∞ c x)
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0)) :
    ContDiffOn ℝ ∞ (fun x => c x * f x) U := by
  intro x hx
  by_cases hs : x ∈ S
  · exact ((hc x hx hs).mul (hf.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (mul_zero_germ (c := c) (hzero x hx hs))).contDiffWithinAt

/-- In particular a reciprocal coefficient may be singular on the axis or
any zero set outside the common factor region. Its actual product is smooth. -/
theorem smooth_mul_inv_of_support_local {r f : D → ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hr : ∀ x ∈ U, x ∈ S → ContDiffAt ℝ ∞ r x)
    (hpos : ∀ x ∈ U, x ∈ S → r x ≠ 0)
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0)) :
    ContDiffOn ℝ ∞ (fun x => (r x)⁻¹ * f x) U :=
  smooth_mul_of_support_local hU hf (fun x hx hs => (hr x hx hs).inv (hpos x hx hs)) hzero

def ApproximationRates.mul_coefficient_support_local
    {gain : ℕ → ℝ} {f c : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hc : ∀ x ∈ U, x ∈ S → ContDiffAt ℝ ∞ c x) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q c m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S → fs J =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => c x * f x) (fun J x => c x * fs J x) := by
  let M : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup a.threshold
  refine ⟨fun m => maxJetLoss Lc m + maxJetLoss a.tailLoss m, M, ?_⟩
  intro m J hJ
  have hqr : ∀ᶠ x in l ⊓ 𝓟 S, 0 < q x ∧ q x ≤ 1 := hq.filter_mono inf_le_left
  have hlr : ∀ᶠ x in l ⊓ 𝓟 S, x ∈ U := hlU.filter_mono inf_le_left
  have hregion : ∀ᶠ x in l ⊓ 𝓟 S, x ∈ S :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  have hcr : FiniteJetRate (l ⊓ 𝓟 S) q c m (-maxJetLoss Lc m) := by
    apply finiteJetRate_of_jetRate (hqr.mono fun _ hx => hx.1)
    intro k hk
    exact (hcg k).weaken hqr (neg_le_neg (le_maxJetLoss Lc hk))
  have htr : FiniteJetRate (l ⊓ 𝓟 S) q (fun x => f x - fs J x) m
      (gain J - maxJetLoss a.tailLoss m) := by
    apply finiteJetRate_of_jetRate (hqr.mono fun _ hx => hx.1)
    intro k hk
    have ht : a.threshold k ≤ J :=
      (Finset.le_sup (f := a.threshold) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).trans hJ
    exact (rate_filter_mono inf_le_left (a.tail_rate k J ht)).weaken hqr
      (sub_le_sub_left (le_maxJetLoss a.tailLoss hk) _)
  have hca : ∀ᶠ x in l ⊓ 𝓟 S, ContDiffAt ℝ ∞ c x := by
    filter_upwards [hlr, hregion] with x hx hs
    exact hc x hx hs
  have hr := rate_mul_at (hqr.mono fun _ hx => hx.1) hca
    (hlr.mono fun x hx => (hf.sub (hfs J)).contDiffAt (hU.mem_nhds hx)) hcr htr
  have hr' : JetRate (l ⊓ 𝓟 S) q (fun x => c x * f x - c x * fs J x) m
      (gain J - (maxJetLoss Lc m + maxJetLoss a.tailLoss m)) := by
    convert hr.congr_on hU hlr
      (show EqOn (fun x => c x * (f x - fs J x))
        (fun x => c x * f x - c x * fs J x) U from fun x _ => mul_sub _ _ _) using 1
    ring
  apply rate_of_restricted_support (hq.mono fun _ hx => hx.1) hlU hr'
  intro x hxU hx
  filter_upwards [hzero x hxU hx, hszero J x hxU hx] with y hy hsy
  simp only [hy, hsy, mul_zero, sub_self]

namespace SupportedPolynomial

variable {ι : Type*}

theorem smooth_evalTerms_of_products (terms : List ((D → ℝ) × Expression D ι Empty))
    {u : ι → D → ℝ}
    (ht : ∀ t ∈ terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U) :
    ContDiffOn ℝ ∞ (evalTerms u terms) U := by
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih =>
      exact (ht t (by simp)).add (ih (fun v hv => ht v (by simp [hv])))

def termsTail_of_products {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (terms : List ((D → ℝ) × Expression D ι Empty))
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ t ∈ terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U)
    (hus : ∀ t ∈ terms, ∀ J, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) U)
    (ht : ∀ t ∈ terms,
      TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
        (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x)) :
    TailRates l q gain (evalTerms u terms) (fun J => evalTerms (us J) terms) := by
  induction terms with
  | nil => exact TailRates.fixed (fun _ => 0)
  | cons t ts ih =>
      exact (ht t (by simp)).add
        (ih (fun v hv => hu v (by simp [hv])) (fun v hv => hus v (by simp [hv]))
          (fun v hv => ht v (by simp [hv]))) hU hlU hq
        (hu t (by simp)) (smooth_evalTerms_of_products ts (fun v hv => hu v (by simp [hv])))
        (hus t (by simp))
        (fun J => smooth_evalTerms_of_products ts (fun v hv => hus v (by simp [hv]) J))

/-- Full residual transfer with smoothness, as well as all coefficient
growth bounds, required only at points of each common factor region. The
conclusion evaluates the original polynomial with its original coefficients. -/
theorem flat_of_support_local_coefficients (P : SupportedPolynomial D ι)
    {gain rho : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (region : ((D → ℝ) × Expression D ι Empty) → Set D)
    (hc : ∀ t ∈ P.terms, ∀ x ∈ U, x ∈ region t → ContDiffAt ℝ ∞ t.1 x)
    (Lc : ((D → ℝ) × Expression D ι Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (l ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0))
    (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate l q (P.eval (us J)) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q (P.eval u) m n := by
  have hprod : ∀ t ∈ P.terms, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x) U := by
    intro t ht
    exact smooth_mul_of_support_local hU (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
      (hc t ht) (hzero t ht)
  have hsprod : ∀ t ∈ P.terms, ∀ J, ContDiffOn ℝ ∞
      (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) U := by
    intro t ht J
    exact smooth_mul_of_support_local hU (t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
      (hc t ht) (hszero t ht J)
  let ht := termsTail_of_products P.terms hU hlU hq hprod hsprod (fun t ht =>
    (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain
      (fun k => Empty.elim k) (fun k => Empty.elim k) ha).mul_coefficient_support_local
        hU hlU hq (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
        (fun J => t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
        (hc t ht) (Lc t) (hcg t ht) (hzero t ht) (hszero t ht))
  have hs := smooth_evalTerms_of_products P.terms hprod
  have hss := fun J => smooth_evalTerms_of_products P.terms (fun t ht => hsprod t ht J)
  let hp := (TailRates.fixed P.constant).add ht hU hlU hq hconst hs (fun _ => hconst) hss
  exact hp.flat_of_residuals hU hlU hq (hconst.add hs)
    (fun J => hconst.add (hss J)) hgain hrho Lres hres m n

end SupportedPolynomial

end NavierStokes.GenericDifferentialPolynomial
