import NavierStokes.ClosedIntervalJetAlgebra
import NavierStokes.NaturalAxisData
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Parameter-jet comparison for the actual five cumulative seed histories

The comparison is on the closed parameter interval, using one-sided derivatives
at its endpoints. Profiles need not be regular at the axis. The constants are
uniform over all profiles with the stated positivity and finite jet bounds.
-/

noncomputable section

namespace NavierStokes.SeedHandbackJets

open Set ClosedIntervalJetAlgebra
open scoped ContDiff

abbrev Curves := Fin 7 → ℝ → ℝ
abbrev Packet := Fin 12 → ℝ → ℝ
abbrev Basis := Fin 19 → ℝ → ℝ

/-- `E,U,M,I,J,S,Cp`, followed by the first parameter derivatives needed by the lags. -/
def packet (P₀ : ℝ → ℝ) (f : Curves) : Packet :=
  ![f 0, f 1, f 2, derivWithin (f 2) J,
    f 3, derivWithin (f 3) J, f 4, derivWithin (f 4) J,
    f 5, derivWithin (f 5) J, (fun η => P₀ η + f 6 η),
    derivWithin (fun η => P₀ η + f 6 η) J]

theorem packet_pairBound {k : ℕ} {f g : Curves} {P₀ : ℝ → ℝ} {B B₀ ε : ℝ}
    (h : ∀ i, PairBound (k+1) (f i) (g i) B 1 ε)
    (hP : ContDiffOn ℝ ∞ P₀ J) (hb : Bound (k+1) P₀ B₀) :
    ∀ i, PairBound k (packet P₀ f i) (packet P₀ g i) (B+B₀) 1 ε := by
  have hm (i : Fin 7) : PairBound (k+1) (f i) (g i) (B+B₀) 1 ε :=
    ⟨(h i).smooth_left, (h i).smooth_right,
      (h i).left.mono (le_add_of_nonneg_right hb.nonneg),
      (h i).right.mono (le_add_of_nonneg_right hb.nonneg), (h i).difference⟩
  have hp := (PairBound.same hP hb ε).add (h 6)
  have hp' : PairBound (k+1) (fun η => P₀ η + f 6 η) (fun η => P₀ η + g 6 η)
      (B+B₀) 1 ε := by simpa only [zero_add, add_comm B₀ B] using hp
  intro i
  fin_cases i
  · exact (hm 0).of_le (by omega)
  · exact (hm 1).of_le (by omega)
  · exact (hm 2).of_le (by omega)
  · exact (hm 2).derivWithin
  · exact (hm 3).of_le (by omega)
  · exact (hm 3).derivWithin
  · exact (hm 4).of_le (by omega)
  · exact (hm 4).derivWithin
  · exact (hm 5).of_le (by omega)
  · exact (hm 5).derivWithin
  · exact hp'.of_le (by omega)
  · exact hp'.derivWithin

def basis (h X : ℝ) (p : Packet) : Basis :=
  ![p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, p 8, p 9, p 10, p 11,
    (fun η => η), (fun _ => X), (fun _ => X⁻¹),
    (fun _ => (Real.sqrt (2*X))⁻¹), (fun η => (p 0 η)⁻¹),
    (fun η => (NaturalAxisData.L h η)⁻¹), NaturalAxisData.d]

abbrev Expr := PolynomialExpression (Fin 19)

private def v (i : Fin 19) : Expr := .input i
private def c (x : ℝ) : Expr := .constant x
def massExpression (h : ℝ) : Expr :=
  .mul (.sub (.sub (v 13) (.mul (.mul (c (2*NaturalAxisData.D h)) (v 12)) (v 2)))
    (.mul (v 18) (v 3))) (v 14)

def angularExpression (h : ℝ) : Expr :=
  .add (.sub (c 0) (massExpression h))
    (.mul (.mul (.mul
      (.add (.sub (.sub (.mul (c (1-h)) (v 4))
        (.mul (.mul (c (NaturalAxisData.D h)) (v 12)) (v 5))) (.mul (v 18) (v 7)))
        (.mul (.mul (c (2*(h-NaturalAxisData.D h))) (v 12)) (v 6))) (v 14)) (v 15)) (v 16))

def axialExpression (h : ℝ) : Expr :=
  .sub (.add (.add (.sub (c 0) (.mul (massExpression h) (v 1)))
    (.mul (.sub (.add (.mul (c (NaturalAxisData.D h)) (.sub (v 2) (.mul (v 12) (v 3))))
      (.mul (.mul (c (4*h)) (v 12)) (v 8))) (.mul (v 18) (v 9))) (v 14)))
    (.mul (.mul (c (4*NaturalAxisData.A h)) (v 12)) (v 10))) (.mul (v 18) (v 11))

/-- The four components are `Q_s,N_s,p_{s,1},p_{s,2}`. -/
def outputExpression (h : ℝ) : Fin 4 → Expr :=
  ![angularExpression h, axialExpression h,
    .mul (.mul (v 13) (v 17)) (angularExpression h),
    .mul (.mul (.mul (v 13) (v 17)) (v 16)) (axialExpression h)]

def stocks (h X : ℝ) (P₀ : ℝ → ℝ) (f : Curves) (i : Fin 4) : ℝ → ℝ :=
  (outputExpression h i).eval (basis h X (packet P₀ f))

/-- These are the literal integrated lags, without invoking a regular-axis solution class. -/
theorem stocks_formulas (h X : ℝ) (P₀ : ℝ → ℝ) (f : Curves) (η : ℝ) :
    let p := packet P₀ f
    let W := (X-2*NaturalAxisData.D h*η*p 2 η-NaturalAxisData.d η*p 3 η)/X
    stocks h X P₀ f 0 η = -W+
      ((1-h)*p 4 η-NaturalAxisData.D h*η*p 5 η-NaturalAxisData.d η*p 7 η+
        2*(h-NaturalAxisData.D h)*η*p 6 η)/(X*Real.sqrt (2*X)*p 0 η) ∧
    stocks h X P₀ f 1 η = -W*p 1 η+
      (NaturalAxisData.D h*(p 2 η-η*p 3 η)+4*h*η*p 8 η-NaturalAxisData.d η*p 9 η)/X+
      4*NaturalAxisData.A h*η*p 10 η-NaturalAxisData.d η*p 11 η ∧
    stocks h X P₀ f 2 η = X/NaturalAxisData.L h η*stocks h X P₀ f 0 η ∧
    stocks h X P₀ f 3 η = X/(NaturalAxisData.L h η*p 0 η)*stocks h X P₀ f 1 η := by
  simp [stocks, outputExpression, angularExpression, axialExpression, massExpression,
    PolynomialExpression.eval, v, c, basis, div_eq_mul_inv, mul_inv_rev]
  repeat' constructor <;> ring_nf
  simp

private def inputBounds (k : ℕ) (D X₀ X₁ T L : ℝ) : Fin 19 → ℝ :=
  ![D,D,D,D,D,D,D,D,D,D,D,D,1,X₁,X₀⁻¹,(Real.sqrt (2*X₀))⁻¹,T,L,1+(2:ℝ)^k]

private def differenceBounds (CI : ℝ) : Fin 19 → ℝ :=
  ![1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,CI,0,0]

private theorem L_lower {h : ℝ} (hh : 0 ≤ h) {η : ℝ} (hη : η ∈ J) :
    1-2*h ≤ NaturalAxisData.L h η := by
  have hs : η^2 ≤ 1 := by nlinarith [hη.1, hη.2]
  dsimp [NaturalAxisData.L]
  nlinarith

private theorem fixed_L_bound (k : ℕ) (h : ℝ) :
    Bound k (NaturalAxisData.L h) (1+(2:ℝ)^k*(|2*h| *((2:ℝ)^k))) := by
  have he := (Bound.id k).mul contDiffOn_id contDiffOn_id (Bound.id k)
  have hc := (Bound.const k (2*h)).mul contDiffOn_const (contDiffOn_id.mul contDiffOn_id) he
  have hb := (Bound.const k 1).sub contDiffOn_const
    (contDiffOn_const.mul (contDiffOn_id.mul contDiffOn_id)) hc
  convert hb using 1
  · ext η; simp only [NaturalAxisData.L, id_eq]; ring
  · simp only [abs_one, mul_one]; ring

private theorem fixed_d_bound (k : ℕ) : Bound k NaturalAxisData.d (1+(2:ℝ)^k) := by
  have he := (Bound.id k).mul contDiffOn_id contDiffOn_id (Bound.id k)
  have hb := (Bound.const k 1).sub contDiffOn_const (contDiffOn_id.mul contDiffOn_id) he
  convert hb using 1
  · ext η; simp only [NaturalAxisData.d, id_eq]; ring
  · simp



private theorem basis_pairBound {k : ℕ} {h X₀ X₁ X μ D T L ε : ℝ}
    (hh : 0 ≤ h) (hh' : h < 1/2) (hX₀ : 0 < X₀) (hX : X ∈ Icc X₀ X₁)
    (hμ : 0 < μ) {p q : Packet}
    (hpq : ∀ i, PairBound k (p i) (q i) D 1 ε)
    (hp : ∀ η ∈ J, μ ≤ p 0 η) (hq : ∀ η ∈ J, μ ≤ q 0 η)
    (hT : ∀ z : ℝ → ℝ, ContDiffOn ℝ ∞ z J →
      (∀ η ∈ J, μ ≤ z η) → Bound k z D → Bound k (fun η => (z η)⁻¹) T)
    (hL : Bound k (fun η => (NaturalAxisData.L h η)⁻¹) L) :
    ∀ i, PairBound k (basis h X p i) (basis h X q i)
      (inputBounds k D X₀ X₁ T L i)
      (differenceBounds ((2:ℝ)^k*((2:ℝ)^k*1*T)*T) i) ε := by
  have hXp : 0 < X := hX₀.trans_le hX.1
  have hX₁ : 0 < X₁ := hXp.trans_le hX.2
  have hXs : Bound k (fun _ : ℝ => X) X₁ :=
    (Bound.const k X).mono (by simpa only [abs_of_pos hXp] using hX.2)
  have hXi : Bound k (fun _ : ℝ => X⁻¹) X₀⁻¹ :=
    (Bound.const k X⁻¹).mono (by rw [abs_of_pos (inv_pos.mpr hXp)]; exact inv_anti₀ hX₀ hX.1)
  have hroot0 : 0 < Real.sqrt (2*X₀) := Real.sqrt_pos.mpr (by positivity)
  have hroot : 0 < Real.sqrt (2*X) := Real.sqrt_pos.mpr (by positivity)
  have hXsroot : Bound k (fun _ : ℝ => (Real.sqrt (2*X))⁻¹) (Real.sqrt (2*X₀))⁻¹ :=
    (Bound.const k (Real.sqrt (2*X))⁻¹).mono (by
      rw [abs_of_pos (inv_pos.mpr hroot)]
      exact inv_anti₀ hroot0 (Real.sqrt_le_sqrt (by linarith [hX.1])))
  have hLs : ContDiffOn ℝ ∞ (NaturalAxisData.L h) J := by
    unfold NaturalAxisData.L
    fun_prop
  have hds : ContDiffOn ℝ ∞ NaturalAxisData.d J := by
    unfold NaturalAxisData.d
    fun_prop
  have hLp : ∀ η ∈ J, NaturalAxisData.L h η ≠ 0 :=
    fun η hη => (lt_of_lt_of_le (by linarith : 0 < 1-2*h) (L_lower hh hη)).ne'
  intro i
  fin_cases i
  · exact hpq 0
  · exact hpq 1
  · exact hpq 2
  · exact hpq 3
  · exact hpq 4
  · exact hpq 5
  · exact hpq 6
  · exact hpq 7
  · exact hpq 8
  · exact hpq 9
  · exact hpq 10
  · exact hpq 11
  · exact PairBound.same contDiffOn_id (Bound.id k) ε
  · exact PairBound.same contDiffOn_const hXs ε
  · exact PairBound.same contDiffOn_const hXi ε
  · exact PairBound.same contDiffOn_const hXsroot ε
  · exact (hpq 0).inverse hμ hp hq hT
  · exact PairBound.same (hLs.inv hLp) hL ε
  · exact PairBound.same hds (fixed_d_bound k) ε

/-- Arbitrary-order lag/stock stability. `C` precedes both profiles and the radius;
there is no closeness restriction on their difference and no radial derivative input. -/
theorem stocks_comparison (k : ℕ) (h X₀ X₁ μ B B₀ : ℝ)
    (hh : 0 < h) (hh' : h < 1/2) (hX₀ : 0 < X₀) (hXX : X₀ ≤ X₁)
    (hμ : 0 < μ) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ Icc X₀ X₁, ∀ P₀ : ℝ → ℝ,
      ContDiffOn ℝ ∞ P₀ J → Bound (k+1) P₀ B₀ →
      ∀ f g : Curves, ∀ ε : ℝ, 0 ≤ ε →
      (∀ i, PairBound (k+1) (f i) (g i) B 1 ε) →
      (∀ η ∈ J, μ ≤ f 0 η) → (∀ η ∈ J, μ ≤ g 0 η) →
      ∀ i, Bound k (fun η => stocks h X P₀ g i η - stocks h X P₀ f i η) (C*ε) := by
  let D := B+B₀
  have hD : 0 ≤ D := add_nonneg hB hB₀
  obtain ⟨T, hT0, hT⟩ := inverse_bound k μ D hμ
  let LB := 1+(2:ℝ)^k*(|2*h| *((2:ℝ)^k))
  obtain ⟨L, hL0, hL⟩ := inverse_bound k (1-2*h) LB (by linarith)
  have hLs : ContDiffOn ℝ ∞ (NaturalAxisData.L h) J := by
    unfold NaturalAxisData.L
    fun_prop
  have hLb := hL (NaturalAxisData.L h) hLs (fun η hη => L_lower hh.le hη) (fixed_L_bound k h)
  let BB := inputBounds k D X₀ X₁ T L
  let CC := differenceBounds ((2:ℝ)^k*((2:ℝ)^k*1*T)*T)
  have hBB : ∀ i, 0 ≤ BB i := by
    intro i
    fin_cases i <;> norm_num [BB, inputBounds]
    all_goals first | exact hD | exact hT0 | exact hL0 | exact hX₀.le.trans hXX | positivity
  have hCC : ∀ i, 0 ≤ CC i := by
    intro i
    fin_cases i <;> norm_num [CC, differenceBounds]
    all_goals positivity
  let C := ∑ i : Fin 4, ((outputExpression h i).bounds k BB CC).2
  have hCn (i : Fin 4) : 0 ≤ ((outputExpression h i).bounds k BB CC).2 :=
    (PolynomialExpression.bounds_nonneg k hBB hCC _).2
  refine ⟨C, Finset.sum_nonneg (fun i _ => hCn i), ?_⟩
  intro X hX P₀ hP hPbound f g ε hε hfg hf hg i
  have hpacket := packet_pairBound hfg hP hPbound
  have hbas := basis_pairBound hh.le hh' hX₀ hX hμ hpacket hf hg hT hLb
  have hresult := PolynomialExpression.eval_pairBound hbas (outputExpression h i)
  apply hresult.difference.mono
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hCn j) (Finset.mem_univ i)) hε

/-- An arbitrary positive-radius comparison profile; no regular-axis representation is required. -/
structure Profile where
  E : (ℝ × ℝ) → ℝ
  U : (ℝ × ℝ) → ℝ

namespace Profile

def density (P : Profile) (i : Fin 5) (x η : ℝ) : ℝ :=
  ![P.U (x,η), Real.sqrt (2*x)*P.E (x,η),
    P.U (x,η)*(Real.sqrt (2*x)*P.E (x,η)),
    P.U (x,η)^2-P.E (x,η)^2/2, P.E (x,η)^2/(2*x)] i

/-- The manuscript's actual cumulative Lebesgue integrals `M,I,J,S,Cp`. -/
def history (P : Profile) (i : Fin 5) (X η : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..X, P.density i x η

def curves (P : Profile) (X : ℝ) : Curves :=
  ![(fun η => P.E (X,η)), (fun η => P.U (X,η)),
    P.history 0 X, P.history 1 X, P.history 2 X, P.history 3 X, P.history 4 X]

def outputs (P : Profile) (h : ℝ) (P₀ : ℝ → ℝ) (X : ℝ) : Fin 4 → ℝ → ℝ :=
  stocks h X P₀ (P.curves X)

def SmoothOnBand (P : Profile) (X₀ X₁ : ℝ) : Prop :=
  ∀ X ∈ Icc X₀ X₁, ∀ i, ContDiffOn ℝ ∞ (P.curves X i) J

def JetBound (P : Profile) (k : ℕ) (X₀ X₁ B : ℝ) : Prop :=
  ∀ X ∈ Icc X₀ X₁, ∀ i, Bound k (P.curves X i) B

end Profile

/-- The printed comparison, with separate field and actual-history difference bounds.
The same pressure integration constant is used for both profiles. -/
theorem profile_comparison (k : ℕ) (h X₀ X₁ μ B B₀ : ℝ)
    (hh : 0 < h) (hh' : h < 1/2) (hX₀ : 0 < X₀) (hXX : X₀ ≤ X₁)
    (hμ : 0 < μ) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P Q : Profile,
      P.SmoothOnBand X₀ X₁ → Q.SmoothOnBand X₀ X₁ →
      P.JetBound (k+1) X₀ X₁ B → Q.JetBound (k+1) X₀ X₁ B →
      (∀ X ∈ Icc X₀ X₁, ∀ η ∈ J, μ ≤ P.E (X,η)) →
      (∀ X ∈ Icc X₀ X₁, ∀ η ∈ J, μ ≤ Q.E (X,η)) →
      ∀ P₀ : ℝ → ℝ, ContDiffOn ℝ ∞ P₀ J → Bound (k+1) P₀ B₀ →
      ∀ εf εm : ℝ, 0 ≤ εf → 0 ≤ εm →
      (∀ X ∈ Icc X₀ X₁,
        Bound (k+1) (fun η => Q.E (X,η)-P.E (X,η)) εf ∧
        Bound (k+1) (fun η => Q.U (X,η)-P.U (X,η)) εf) →
      (∀ X ∈ Icc X₀ X₁, ∀ i,
        Bound (k+1) (fun η => Q.history i X η-P.history i X η) εm) →
      ∀ X ∈ Icc X₀ X₁, ∀ i,
        Bound k (fun η => Q.outputs h P₀ X i η-P.outputs h P₀ X i η) (C*(εf+εm)) := by
  obtain ⟨C,hC,hbound⟩ := stocks_comparison k h X₀ X₁ μ B B₀ hh hh' hX₀ hXX hμ hB hB₀
  refine ⟨C,hC,?_⟩
  intro P Q hPs hQs hPb hQb hPpos hQpos P₀ hP₀ hP₀b εf εm hεf hεm hfields hhist X hX i
  apply hbound X hX P₀ hP₀ hP₀b (P.curves X) (Q.curves X) (εf+εm)
    (add_nonneg hεf hεm) _ (hPpos X hX) (hQpos X hX) i
  intro j
  refine ⟨hPs X hX j, hQs X hX j, hPb X hX j, hQb X hX j, ?_⟩
  rw [one_mul]
  fin_cases j
  · exact (hfields X hX).1.mono (le_add_of_nonneg_right hεm)
  · exact (hfields X hX).2.mono (le_add_of_nonneg_right hεm)
  · exact (hhist X hX 0).mono (le_add_of_nonneg_left hεf)
  · exact (hhist X hX 1).mono (le_add_of_nonneg_left hεf)
  · exact (hhist X hX 2).mono (le_add_of_nonneg_left hεf)
  · exact (hhist X hX 3).mono (le_add_of_nonneg_left hεf)
  · exact (hhist X hX 4).mono (le_add_of_nonneg_left hεf)



/-- Values of all component parameter derivatives through order `k`, including zero. -/
def jetValues {m : ℕ} (k : ℕ) (X₀ X₁ : ℝ) (f : Fin m → ℝ → ℝ → ℝ) : Set ℝ :=
  {z | z = 0 ∨ ∃ i X, X ∈ Icc X₀ X₁ ∧ ∃ n, n ≤ k ∧ ∃ η, η ∈ J ∧
    z = ‖iteratedFDerivWithin ℝ n (f i X) J η‖}

/-- The maximum-component `C^k` norm in the parameter on the closed rectangle. -/
def parameterNorm {m : ℕ} (k : ℕ) (X₀ X₁ : ℝ) (f : Fin m → ℝ → ℝ → ℝ) : ℝ :=
  sSup (jetValues k X₀ X₁ f)

private theorem jetValues_nonempty {m k : ℕ} {X₀ X₁ : ℝ} {f : Fin m → ℝ → ℝ → ℝ} :
    (jetValues k X₀ X₁ f).Nonempty := ⟨0, Or.inl rfl⟩

private theorem jetValues_bddAbove {m k : ℕ} {X₀ X₁ B : ℝ} {f : Fin m → ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hb : ∀ i X, X ∈ Icc X₀ X₁ → Bound k (f i X) B) :
    BddAbove (jetValues k X₀ X₁ f) := by
  refine ⟨B, ?_⟩
  intro z hz
  rcases hz with rfl | ⟨i,X,hX,n,hn,η,hη,rfl⟩
  · exact hB
  · exact hb i X hX n hn η hη

theorem parameterNorm_le {m k : ℕ} {X₀ X₁ B : ℝ} {f : Fin m → ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hb : ∀ i X, X ∈ Icc X₀ X₁ → Bound k (f i X) B) :
    parameterNorm k X₀ X₁ f ≤ B := by
  apply csSup_le jetValues_nonempty
  intro z hz
  rcases hz with rfl | ⟨i,X,hX,n,hn,η,hη,rfl⟩
  · exact hB
  · exact hb i X hX n hn η hη

theorem parameterNorm_bounds {m k : ℕ} {X₀ X₁ B : ℝ} {f : Fin m → ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hb : ∀ i X, X ∈ Icc X₀ X₁ → Bound k (f i X) B) :
    0 ≤ parameterNorm k X₀ X₁ f ∧
      ∀ i X, X ∈ Icc X₀ X₁ → Bound k (f i X) (parameterNorm k X₀ X₁ f) := by
  have hbounded := jetValues_bddAbove hB hb
  refine ⟨le_csSup hbounded (Or.inl rfl), ?_⟩
  intro i X hX n hn η hη
  exact le_csSup hbounded (Or.inr ⟨i,X,hX,n,hn,η,hη,rfl⟩)

def fieldDifference (P Q : Profile) : Fin 2 → ℝ → ℝ → ℝ :=
  ![(fun X η => Q.E (X,η)-P.E (X,η)), (fun X η => Q.U (X,η)-P.U (X,η))]

def historyDifference (P Q : Profile) (i : Fin 5) (X η : ℝ) : ℝ :=
  Q.history i X η-P.history i X η

def outputDifference (h : ℝ) (P₀ : ℝ → ℝ) (P Q : Profile) (i : Fin 4) (X η : ℝ) : ℝ :=
  Q.outputs h P₀ X i η-P.outputs h P₀ X i η

/-- Literal maximum-component norm form of `seed:profile-comparison`, for every `k`. -/
theorem profile_comparison_norm (k : ℕ) (h X₀ X₁ μ B B₀ : ℝ)
    (hh : 0 < h) (hh' : h < 1/2) (hX₀ : 0 < X₀) (hXX : X₀ ≤ X₁)
    (hμ : 0 < μ) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P Q : Profile,
      P.SmoothOnBand X₀ X₁ → Q.SmoothOnBand X₀ X₁ →
      P.JetBound (k+1) X₀ X₁ B → Q.JetBound (k+1) X₀ X₁ B →
      (∀ X ∈ Icc X₀ X₁, ∀ η ∈ J, μ ≤ P.E (X,η)) →
      (∀ X ∈ Icc X₀ X₁, ∀ η ∈ J, μ ≤ Q.E (X,η)) →
      ∀ P₀ : ℝ → ℝ, ContDiffOn ℝ ∞ P₀ J → Bound (k+1) P₀ B₀ →
      parameterNorm k X₀ X₁ (outputDifference h P₀ P Q) ≤ C *
        (parameterNorm (k+1) X₀ X₁ (fieldDifference P Q)+
          parameterNorm (k+1) X₀ X₁ (historyDifference P Q)) := by
  obtain ⟨C,hC,hbound⟩ := profile_comparison k h X₀ X₁ μ B B₀ hh hh' hX₀ hXX hμ hB hB₀
  refine ⟨C,hC,?_⟩
  intro P Q hPs hQs hPb hQb hPpos hQpos P₀ hP₀ hP₀b
  have hd (X : ℝ) (hX : X ∈ Icc X₀ X₁) (i : Fin 7) :
      Bound (k+1) (fun η => Q.curves X i η-P.curves X i η) (B+B) :=
    (hQb X hX i).sub (hQs X hX i) (hPs X hX i) (hPb X hX i)
  have hf : ∀ i X, X ∈ Icc X₀ X₁ → Bound (k+1) (fieldDifference P Q i X) (B+B) := by
    intro i X hX
    fin_cases i
    · exact hd X hX 0
    · exact hd X hX 1
  have hm : ∀ i X, X ∈ Icc X₀ X₁ → Bound (k+1) (historyDifference P Q i X) (B+B) := by
    intro i X hX
    fin_cases i
    · exact hd X hX 2
    · exact hd X hX 3
    · exact hd X hX 4
    · exact hd X hX 5
    · exact hd X hX 6
  obtain ⟨hfn,hfb⟩ := parameterNorm_bounds (add_nonneg hB hB) hf
  obtain ⟨hmn,hmb⟩ := parameterNorm_bounds (add_nonneg hB hB) hm
  apply parameterNorm_le (mul_nonneg hC (add_nonneg hfn hmn))
  intro i X hX
  exact hbound P Q hPs hQs hPb hQb hPpos hQpos P₀ hP₀ hP₀b _ _ hfn hmn
    (fun X hX => ⟨hfb 0 X hX,hfb 1 X hX⟩) (fun X hX i => hmb i X hX) X hX i

end NavierStokes.SeedHandbackJets
