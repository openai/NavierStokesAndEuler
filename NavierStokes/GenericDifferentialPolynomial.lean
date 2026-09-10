import NavierStokes.GenericJetRateAlgebra

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Quantitative approximation data. Constants may depend on the stage, while
the power losses and derivative thresholds are fixed functions of the jet order. -/
structure ApproximationRates (l : Filter D) (q : D → ℝ) (gain : ℕ → ℝ)
    (f : D → ℝ) (stage : ℕ → D → ℝ) where
  growthLoss : ℕ → ℝ
  tailLoss : ℕ → ℝ
  threshold : ℕ → ℕ
  stage_growth : ∀ J m, JetRate l q (stage J) m (-growthLoss m)
  tail_rate : ∀ m J, threshold m ≤ J →
    JetRate l q (fun x => f x - stage J x) m (gain J - tailLoss m)

private def maxThreshold (M : ℕ → ℕ) (m : ℕ) : ℕ :=
  (Finset.range (m + 1)).sup M

private theorem le_maxThreshold (M : ℕ → ℕ) {k m : ℕ} (hk : k ≤ m) :
    M k ≤ maxThreshold M m :=
  Finset.le_sup (f := M) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

variable {l : Filter D} {q : D → ℝ} {gain : ℕ → ℝ} {U : Set D}
variable {f g : D → ℝ} {fs gs : ℕ → D → ℝ}

theorem ApproximationRates.full_growth
    (h : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hg : Tendsto gain atTop atTop) (m : ℕ) :
    JetRate l q f m (-max 0 (h.growthLoss m)) := by
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hg.eventually (eventually_ge_atTop (h.tailLoss m)))
  let J := max (h.threshold m) J₀
  have htail := (h.tail_rate m J (le_max_left _ _)).weaken hq
    (show -max 0 (h.growthLoss m) ≤ gain J - h.tailLoss m by
      have := hJ₀ J (le_max_right _ _)
      have := le_max_left 0 (h.growthLoss m)
      linarith)
  have hstage := (h.stage_growth J m).weaken hq
    (neg_le_neg (le_max_right 0 (h.growthLoss m)))
  exact (hstage.add htail hU hlU (hfs J) (hf.sub (hfs J))).congr_on hU hlU
    (fun x _ => by dsimp; ring)

theorem ApproximationRates.stage_finite_growth
    (h : ApproximationRates l q gain f fs)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (J m : ℕ) :
    FiniteJetRate l q (fs J) m (-maxJetLoss h.growthLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.stage_growth J k).weaken hq (neg_le_neg (le_maxJetLoss _ hk))

theorem ApproximationRates.full_finite_growth
    (h : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hg : Tendsto gain atTop atTop) (m : ℕ) :
    FiniteJetRate l q f m (-maxJetLoss h.growthLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.full_growth hU hlU hq hf hfs hg k).weaken hq
    (neg_le_neg (max_le (maxJetLoss_nonneg _ _) (le_maxJetLoss _ hk)))

theorem ApproximationRates.tail_finite_rate
    (h : ApproximationRates l q gain f fs)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1) (m J : ℕ)
    (hJ : maxThreshold h.threshold m ≤ J) :
    FiniteJetRate l q (fun x => f x - fs J x) m
      (gain J - maxJetLoss h.tailLoss m) := by
  apply finiteJetRate_of_jetRate (hq.mono fun _ hx => hx.1)
  intro k hk
  exact (h.tail_rate k J ((le_maxThreshold _ hk).trans hJ)).weaken hq
    (sub_le_sub_left (le_maxJetLoss _ hk) _)

def ApproximationRates.add
    (a : ApproximationRates l q gain f fs) (b : ApproximationRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U) :
    ApproximationRates l q gain (fun x => f x + g x)
      (fun J x => fs J x + gs J x) where
  growthLoss m := max (a.growthLoss m) (b.growthLoss m)
  tailLoss m := max (a.tailLoss m) (b.tailLoss m)
  threshold m := max (a.threshold m) (b.threshold m)
  stage_growth J m :=
    ((a.stage_growth J m).weaken hq (neg_le_neg (le_max_left _ _))).add
      ((b.stage_growth J m).weaken hq (neg_le_neg (le_max_right _ _)))
      hU hlU (hfs J) (hgs J)
  tail_rate m J hJ := by
    have ha := (a.tail_rate m J ((le_max_left _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_left (a.tailLoss m) (b.tailLoss m)) _)
    have hb := (b.tail_rate m J ((le_max_right _ _).trans hJ)).weaken hq
      (sub_le_sub_left (le_max_right (a.tailLoss m) (b.tailLoss m)) _)
    exact (ha.add hb hU hlU (hf.sub (hfs J)) (hg.sub (hgs J))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def ApproximationRates.mul
    (a : ApproximationRates l q gain f fs) (b : ApproximationRates l q gain g gs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U)
    (hgs : ∀ J, ContDiffOn ℝ ∞ (gs J) U)
    (hgain : Tendsto gain atTop atTop) :
    ApproximationRates l q gain (fun x => f x * g x)
      (fun J x => fs J x * gs J x) where
  growthLoss m := maxJetLoss a.growthLoss m + maxJetLoss b.growthLoss m
  tailLoss m := max
    (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
    (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
  threshold m := max (maxThreshold a.threshold m) (maxThreshold b.threshold m)
  stage_growth J m := by
    have h := rate_mul hU hlU hq (hfs J) (hgs J)
      (a.stage_finite_growth hq J m) (b.stage_finite_growth hq J m)
    simpa only [neg_add] using h
  tail_rate m J hJ := by
    have ha := rate_mul hU hlU hq (hf.sub (hfs J)) hg
      (a.tail_finite_rate hq m J ((le_max_left _ _).trans hJ))
      (b.full_finite_growth hU hlU hq hg hgs hgain m)
    have hb := rate_mul hU hlU hq (hfs J) (hg.sub (hgs J))
      (a.stage_finite_growth hq J m)
      (b.tail_finite_rate hq m J ((le_max_right _ _).trans hJ))
    have ha' := ha.weaken hq
      (show gain J - max
        (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
        (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m) ≤
        (gain J - maxJetLoss a.tailLoss m) + -maxJetLoss b.growthLoss m by
        have := le_max_left
          (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
          (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
        linarith)
    have hb' := hb.weaken hq
      (show gain J - max
        (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
        (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m) ≤
        -maxJetLoss a.growthLoss m + (gain J - maxJetLoss b.tailLoss m) by
        have := le_max_right
          (maxJetLoss a.tailLoss m + maxJetLoss b.growthLoss m)
          (maxJetLoss b.tailLoss m + maxJetLoss a.growthLoss m)
        linarith)
    exact (ha'.add hb' hU hlU ((hf.sub (hfs J)).mul hg)
      ((hfs J).mul (hg.sub (hgs J)))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

def ApproximationRates.directional
    (a : ApproximationRates l q gain f fs)
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hfs : ∀ J, ContDiffOn ℝ ∞ (fs J) U) (v : D) :
    ApproximationRates l q gain (fun x => fderiv ℝ f x v)
      (fun J x => fderiv ℝ (fs J) x v) where
  growthLoss m := a.growthLoss (m + 1)
  tailLoss m := a.tailLoss (m + 1)
  threshold m := a.threshold (m + 1)
  stage_growth J m := rate_directional hU hlU (hfs J) v (a.stage_growth J (m + 1))
  tail_rate m J hJ := by
    have h := rate_directional hU hlU (hf.sub (hfs J)) v
      (a.tail_rate (m + 1) J hJ)
    exact h.congr_on hU hlU (directional_sub_eqOn hU hf (hfs J) v)

def ApproximationRates.fixed {c : D → ℝ} {L : ℕ → ℝ}
    (hc : ∀ m, JetRate l q c m (-L m)) :
    ApproximationRates l q gain c (fun _ => c) where
  growthLoss := L
  tailLoss := 0
  threshold := 0
  stage_growth _ m := hc m
  tail_rate m J _ := by
    simpa only [sub_self] using (rate_zero (l := l) (q := q) (m := m)
      (r := gain J - (0 : ℕ → ℝ) m))

/-- A finite differential expression in scalar components with fixed variable
coefficients. Products, sums, and arbitrary fixed directional derivatives are
allowed at every node; consequently the order and polynomial degree are finite. -/
inductive Expression (D ι κ : Type*) where
  | input : ι → Expression D ι κ
  | coeff : κ → Expression D ι κ
  | add : Expression D ι κ → Expression D ι κ → Expression D ι κ
  | mul : Expression D ι κ → Expression D ι κ → Expression D ι κ
  | directional : D → Expression D ι κ → Expression D ι κ

namespace Expression

variable {ι κ : Type*}

/-- Evaluation uses actual Fréchet derivatives, including at derivative nodes. -/
def eval (c : κ → D → ℝ) (u : ι → D → ℝ) : Expression D ι κ → D → ℝ
  | .input i => u i
  | .coeff i => c i
  | .add a b => fun x => eval c u a x + eval c u b x
  | .mul a b => fun x => eval c u a x * eval c u b x
  | .directional v a => fun x => fderiv ℝ (eval c u a) x v

theorem smooth_eval (e : Expression D ι κ)
    {c : κ → D → ℝ} {u : ι → D → ℝ} (hU : IsOpen U)
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U) : ContDiffOn ℝ ∞ (eval c u e) U := by
  induction e with
  | input i => exact hu i
  | coeff i => exact hc i
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | directional v a ha => exact smooth_directional hU ha v

/-- Stability of every finite differential polynomial, with explicitly
constructed losses independent of the approximation stage. -/
def approximation_eval (e : Expression D ι κ)
    {c : κ → D → ℝ} {u : ι → D → ℝ} {us : ℕ → ι → D → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop)
    (Lc : κ → ℕ → ℝ) (hcg : ∀ i m, JetRate l q (c i) m (-Lc i m))
    (happrox : ∀ i, ApproximationRates l q gain (u i) (fun J => us J i)) :
    ApproximationRates l q gain (eval c u e) (fun J => eval c (us J) e) := by
  induction e with
  | input i => exact happrox i
  | coeff i => exact ApproximationRates.fixed (hcg i)
  | add a b ha hb =>
      exact ha.add hb hU hlU hq (a.smooth_eval hU hc hu) (b.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) (fun J => b.smooth_eval hU hc (hus J))
  | mul a b ha hb =>
      exact ha.mul hb hU hlU hq (a.smooth_eval hU hc hu) (b.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) (fun J => b.smooth_eval hU hc (hus J)) hgain
  | directional v a ha =>
      exact ha.directional hU hlU (a.smooth_eval hU hc hu)
        (fun J => a.smooth_eval hU hc (hus J)) v

end Expression

/-- If the approximating residuals have unbounded order, so does the residual
of the realized field. This is a theorem about arbitrary finite differential
polynomials, proved from input jet estimates and the ordinary Leibniz rule.
It applies componentwise to any finite collection of output expressions. -/
theorem polynomial_jetRate_of_stages {ι κ : Type*}
    (e : Expression D ι κ) {c : κ → D → ℝ} {u : ι → D → ℝ}
    {us : ℕ → ι → D → ℝ} {Lbg Ltail : ι → ℕ → ℝ}
    {Lc : κ → ℕ → ℝ} {Lres : ℕ → ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hc : ∀ i, ContDiffOn ℝ ∞ (c i) U)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) U)
    (hus : ∀ J i, ContDiffOn ℝ ∞ (us J i) U)
    (hgain : Tendsto gain atTop atTop)
    (hcg : ∀ i m, JetRate l q (c i) m (-Lc i m))
    (hbg : ∀ J i m, JetRate l q (us J i) m (-Lbg i m))
    (htail : ∀ J i m, m ≤ J →
      JetRate l q (fun x => u i x - us J i x) m (gain J - Ltail i m))
    (hres : ∀ J m, JetRate l q (e.eval c (us J)) m (gain J - Lres m))
    (m : ℕ) (n : ℝ) : JetRate l q (e.eval c u) m n := by
  let a : ApproximationRates l q gain (e.eval c u) (fun J => e.eval c (us J)) :=
    e.approximation_eval hU hlU hq hc hu hus hgain Lc hcg
      (fun i => ⟨Lbg i, Ltail i, id, fun J m => hbg J i m,
        fun m J hJ => htail J i m hJ⟩)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1
    (hgain.eventually (eventually_ge_atTop (max (n + a.tailLoss m) (n + Lres m))))
  let J := max (a.threshold m) J₀
  have hJgain := hJ₀ J (le_max_right _ _)
  have htail := (a.tail_rate m J (le_max_left _ _)).weaken hq
    (show n ≤ gain J - a.tailLoss m by
      have := le_max_left (n + a.tailLoss m) (n + Lres m)
      linarith)
  have hstage := (hres J m).weaken hq
    (show n ≤ gain J - Lres m by
      have := le_max_right (n + a.tailLoss m) (n + Lres m)
      linarith)
  exact (hstage.add htail hU hlU (e.smooth_eval hU hc (hus J))
    ((e.smooth_eval hU hc hu).sub (e.smooth_eval hU hc (hus J)))).congr_on hU hlU
      (fun x _ => by dsimp; ring)

end NavierStokes.GenericDifferentialPolynomial
