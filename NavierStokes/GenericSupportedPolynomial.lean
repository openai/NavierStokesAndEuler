import NavierStokes.GenericDifferentialPolynomial
import NavierStokes.GenericRealizationBounds

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff BigOperators

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {l : Filter D} {q : D → ℝ} {U S : Set D}

theorem rate_filter_mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l' : Filter D} (hl : l' ≤ l) {f : D → V} {m : ℕ} {r : ℝ}
    (hf : JetRate l q f m r) : JetRate l' q f m r := by
  obtain ⟨C, hC, hb⟩ := hf
  exact ⟨C, hC, hb.filter_mono hl⟩

def ApproximationRates.filter_mono {f : D → ℝ} {fs : ℕ → D → ℝ} {gain : ℕ → ℝ}
    (h : ApproximationRates l q gain f fs) {l' : Filter D} (hl : l' ≤ l) :
    ApproximationRates l' q gain f fs where
  growthLoss := h.growthLoss
  tailLoss := h.tailLoss
  threshold := h.threshold
  stage_growth J m := rate_filter_mono hl (h.stage_growth J m)
  tail_rate m J hJ := rate_filter_mono hl (h.tail_rate m J hJ)

/-- Restrict coefficient growth to the common support region. Outside that
region the field factor vanishes on a neighborhood, so every derivative of
its product with the coefficient is zero. -/
theorem rate_of_restricted_support {f : D → ℝ} {m : ℕ} {r : ℝ}
    (hq : ∀ᶠ x in l, 0 < q x) (hlU : ∀ᶠ x in l, x ∈ U)
    (hr : JetRate (l ⊓ 𝓟 S) q f m r)
    (hsupport : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0)) : JetRate l q f m r := by
  obtain ⟨C, hC, hb⟩ := hr
  have hb' : ∀ᶠ x in l, x ∈ S → ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r :=
    eventually_inf_principal.mp hb
  refine ⟨C, hC, ?_⟩
  filter_upwards [hq, hb', hlU] with x hx hbx hxU
  by_cases hs : x ∈ S
  · exact hbx hs
  · have heq := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (hsupport x hxU hs) m).self_of_nhds
    rw [heq]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      mul_nonneg hC (Real.rpow_nonneg hx.le r)

/-- Tail data suffice for residual transfer; a coefficient independent of the
fields cancels exactly and therefore needs no growth bound in this step. -/
structure TailRates (l : Filter D) (q : D → ℝ) (gain : ℕ → ℝ)
    (f : D → ℝ) (stage : ℕ → D → ℝ) where
  loss : ℕ → ℝ
  threshold : ℕ → ℕ
  rate : ∀ m J, threshold m ≤ J →
    JetRate l q (fun x => f x - stage J x) m (gain J - loss m)

def ApproximationRates.tail {gain : ℕ → ℝ} {f : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs) : TailRates l q gain f fs :=
  ⟨a.tailLoss, a.threshold, a.tail_rate⟩

/-- Only common-support coefficient bounds are assumed. In particular, the
coefficient may grow arbitrarily fast away from the supports. -/
def ApproximationRates.mul_coefficient_local
    {gain : ℕ → ℝ} {f c : D → ℝ} {fs : ℕ → D → ℝ}
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hc : ContDiffOn ℝ ∞ c U) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q c m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → f =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S → fs J =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => c x * f x) (fun J x => c x * fs J x) := by
  let b := a.filter_mono (show l ⊓ 𝓟 S ≤ l from inf_le_left)
  let M : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup a.threshold
  refine ⟨fun m => maxJetLoss Lc m + maxJetLoss a.tailLoss m, M, ?_⟩
  intro m J hJ
  have hqr : ∀ᶠ x in l ⊓ 𝓟 S, 0 < q x ∧ q x ≤ 1 := hq.filter_mono inf_le_left
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
  have hr := rate_mul hU (hlU.filter_mono inf_le_left) hqr hc (hf.sub (hfs J)) hcr htr
  have hr' : JetRate (l ⊓ 𝓟 S) q (fun x => c x * f x - c x * fs J x) m
      (gain J - (maxJetLoss Lc m + maxJetLoss a.tailLoss m)) := by
    convert hr.congr_on hU (hlU.filter_mono inf_le_left)
      (show EqOn (fun x => c x * (f x - fs J x))
        (fun x => c x * f x - c x * fs J x) U from fun x _ => mul_sub _ _ _) using 1
    ring
  apply rate_of_restricted_support (hq.mono fun _ hx => hx.1) hlU hr'
  intro x hxU hx
  filter_upwards [hzero x hxU hx, hszero J x hxU hx] with y hy hsy
  simp only [hy, hsy, mul_zero, sub_self]

/-- Finite sums preserve a stage-independent loss and threshold. -/
def TailRates.add {gain : ℕ → ℝ} {f g : D → ℝ} {fs gs : ℕ → D → ℝ}
    (a : TailRates l q gain f fs) (b : TailRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U) (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U) :
    TailRates l q gain (fun x => f x + g x) (fun J x => fs J x + gs J x) where
  loss m := max (a.loss m) (b.loss m)
  threshold m := max (a.threshold m) (b.threshold m)
  rate m J hJ := by
    have ha := (a.rate m J ((le_max_left _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_left (a.loss m) (b.loss m)) _)
    have hb := (b.rate m J ((le_max_right _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_right (a.loss m) (b.loss m)) _)
    exact (ha.add hb hU hlU (hf.sub (hfs J)) (hg.sub (hgs J))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def TailRates.fixed {gain : ℕ → ℝ} (c : D → ℝ) :
    TailRates l q gain c (fun _ => c) where
  loss := 0
  threshold := 0
  rate m J _ := by simpa only [sub_self] using (rate_zero (l := l) (q := q)
    (m := m) (r := gain J - (0 : ℕ → ℝ) m))

/-- The finite residual decay order and the correction decay order are
independent sequences. Both may grow arbitrarily slowly. -/
theorem TailRates.flat_of_residuals {gain rho : ℕ → ℝ} {f : D → ℝ} {fs : ℕ → D → ℝ}
    (a : TailRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (Lres : ℕ → ℝ) (hres : ∀ J m, JetRate l q (fs J) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q f m n := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    ((hgain.eventually (eventually_ge_atTop (n + a.loss m))).and
      (hrho.eventually (eventually_ge_atTop (n + Lres m))))
  let J := max (a.threshold m) J₀
  have hj := hJ₀ J (le_max_right _ _)
  have ht := (a.rate m J (le_max_left _ _)).weaken hq (by linarith [hj.1] : n ≤ gain J - a.loss m)
  have hr := (hres J m).weaken hq (by linarith [hj.2] : n ≤ rho J - Lres m)
  exact (hr.add ht hU hlU (hfs J) (hf.sub (hfs J))).congr_on hU hlU
    (fun x _ => by dsimp; ring)

/-- A field-only differential expression inherits a common zero germ from all
its input components, including after any fixed number of derivatives. -/
theorem Expression.zero_germ {ι : Type*} (e : Expression D ι Empty)
    {u : ι → D → ℝ} {x : D}
    (hu : ∀ i, u i =ᶠ[𝓝 x] (fun _ => 0)) :
    e.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0) := by
  induction e with
  | input i => exact hu i
  | coeff k => exact Empty.elim k
  | add a b ha hb =>
      filter_upwards [ha, hb] with y hy hz
      simp only [Expression.eval, hy, hz, add_zero]
  | mul a b ha hb =>
      filter_upwards [ha, hb] with y hy hz
      simp only [Expression.eval, hy, hz, mul_zero]
  | directional v a ha =>
      have hd := ha.fderiv (𝕜 := ℝ)
      filter_upwards [hd] with y hy
      change fderiv ℝ (a.eval (fun k => Empty.elim k) u) y v = 0
      rw [hy]
      simp

/-- A finite differential polynomial in normal form, allowing coefficients
whose growth bounds are local to a different common support for every term. -/
structure SupportedPolynomial (D ι : Type*) where
  constant : D → ℝ
  terms : List ((D → ℝ) × Expression D ι Empty)

namespace SupportedPolynomial

variable {ι : Type*}

def evalTerms (u : ι → D → ℝ) : List ((D → ℝ) × Expression D ι Empty) → D → ℝ
  | [] => fun _ => 0
  | (c, e) :: es => fun x => c x * e.eval (fun k => Empty.elim k) u x + evalTerms u es x

def eval (P : SupportedPolynomial D ι) (u : ι → D → ℝ) : D → ℝ :=
  fun x => P.constant x + evalTerms u P.terms x

theorem smooth_evalTerms (terms : List ((D → ℝ) × Expression D ι Empty))
    {u : ι → D → ℝ} (hU : IsOpen U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hc : ∀ t ∈ terms, ContDiffOn ℝ ∞ t.1 U) :
    ContDiffOn ℝ ∞ (evalTerms u terms) U := by
  induction terms with
  | nil => exact contDiffOn_const
  | cons t ts ih =>
      exact ((hc t (by simp)).mul
        (t.2.smooth_eval hU (fun k => Empty.elim k) hu)).add
          (ih (fun v hv => hc v (by simp [hv])))

theorem smooth_eval (P : SupportedPolynomial D ι) {u : ι → D → ℝ}
    (hU : IsOpen U) (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U) :
    ContDiffOn ℝ ∞ (P.eval u) U :=
  hconst.add (smooth_evalTerms P.terms hU hu hc)

/-- The support condition quantifies over one common neighborhood for all
field components in a monomial, uniformly in the truncation. Coefficients
are required to have controlled growth only on that monomial's region. -/
def termTail {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (t : (D → ℝ) × Expression D ι Empty)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hc : ContDiffOn ℝ ∞ t.1 U) (S : Set D) (Lc : ℕ → ℝ)
    (hcg : ∀ m, JetRate (l ⊓ 𝓟 S) q t.1 m (-Lc m))
    (hzero : ∀ x ∈ U, x ∉ S → t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ J x, x ∈ U → x ∉ S →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0)) :
    TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
      (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x) :=
  (t.2.approximation_eval hU hlU hq (fun k => Empty.elim k) hu hus hgain
    (fun k => Empty.elim k) (fun k => Empty.elim k) ha).mul_coefficient_local
      hU hlU hq (t.2.smooth_eval hU (fun k => Empty.elim k) hu)
      (fun J => t.2.smooth_eval hU (fun k => Empty.elim k) (hus J))
      hc Lc hcg hzero hszero

def termsTail {gain : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (terms : List ((D → ℝ) × Expression D ι Empty))
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hc : ∀ t ∈ terms, ContDiffOn ℝ ∞ t.1 U)
    (ht : ∀ t ∈ terms,
      TailRates l q gain (fun x => t.1 x * t.2.eval (fun k => Empty.elim k) u x)
        (fun J x => t.1 x * t.2.eval (fun k => Empty.elim k) (us J) x)) :
    TailRates l q gain (evalTerms u terms) (fun J => evalTerms (us J) terms) := by
  induction terms with
  | nil => exact TailRates.fixed (fun _ => 0)
  | cons t ts ih =>
      exact (ht t (by simp)).add
        (ih (fun v hv => hc v (by simp [hv])) (fun v hv => ht v (by simp [hv])))
        hU hlU hq
        ((hc t (by simp)).mul (t.2.smooth_eval hU (fun k => Empty.elim k) hu))
        (smooth_evalTerms ts hU hu (fun v hv => hc v (by simp [hv])))
        (fun J => (hc t (by simp)).mul (t.2.smooth_eval hU (fun k => Empty.elim k) (hus J)))
        (fun J => smooth_evalTerms ts hU (hus J) (fun v hv => hc v (by simp [hv])))

/-- Full finite-polynomial residual transfer, with the term independent of
fields retained in the residual hypothesis and canceled in the comparison. -/
theorem flat_of_local_coefficients (P : SupportedPolynomial D ι)
    {gain rho : ℕ → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop) (hrho : Tendsto rho atTop atTop)
    (ha : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i))
    (hconst : ContDiffOn ℝ ∞ P.constant U)
    (hc : ∀ t ∈ P.terms, ContDiffOn ℝ ∞ t.1 U)
    (region : ((D → ℝ) × Expression D ι Empty) → Set D)
    (Lc : ((D → ℝ) × Expression D ι Empty) → ℕ → ℝ)
    (hcg : ∀ t ∈ P.terms, ∀ m, JetRate (l ⊓ 𝓟 (region t)) q t.1 m (-Lc t m))
    (hzero : ∀ t ∈ P.terms, ∀ x ∈ U, x ∉ region t →
      t.2.eval (fun k => Empty.elim k) u =ᶠ[𝓝 x] (fun _ => 0))
    (hszero : ∀ t ∈ P.terms, ∀ J x, x ∈ U → x ∉ region t →
      t.2.eval (fun k => Empty.elim k) (us J) =ᶠ[𝓝 x] (fun _ => 0))
    (Lres : ℕ → ℝ)
    (hres : ∀ J m, JetRate l q (P.eval (us J)) m (rho J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q (P.eval u) m n := by
  let ht := termsTail P.terms hU hlU hq hu hus hc (fun t ht =>
    termTail t hU hlU hq hu hus hgain ha (hc t ht) (region t) (Lc t)
      (hcg t ht) (hzero t ht) (hszero t ht))
  let hp := (TailRates.fixed P.constant).add ht hU hlU hq hconst
    (smooth_evalTerms P.terms hU hu hc) (fun _ => hconst)
      (fun J => smooth_evalTerms P.terms hU (hus J) hc)
  exact hp.flat_of_residuals hU hlU hq (P.smooth_eval hU hu hconst hc)
    (fun J => P.smooth_eval hU (hus J) hconst hc) hgain hrho Lres hres m n

end SupportedPolynomial

end NavierStokes.GenericDifferentialPolynomial
