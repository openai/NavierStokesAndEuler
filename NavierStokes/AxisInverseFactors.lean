import NavierStokes.AxisOperators

/-! Inserting undifferentiated factors inside the regular radial inverse. -/

noncomputable section

namespace NavierStokes.AxisInverseFactors

open Finset Finset.Nat Set AxisWeightEstimates AxisCoefficientSpace AxisOperators
open scoped BigOperators Topology BoundedContinuousFunction

private local instance (I : Window) (ε : ℝ) : NormedAddCommGroup (AxisSpace I ε) := inferInstance
private local instance (I : Window) (ε : ℝ) : NormedSpace ℝ (AxisSpace I ε) := inferInstance

def degreeMultiplier (r n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + r - 1)

theorem degreeMultiplier_nonneg {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    0 ≤ degreeMultiplier r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : 0 ≤ (n : ℝ) := by positivity
  unfold degreeMultiplier
  exact mul_nonneg hn (by linarith)

theorem degreeMultiplier_mono {r : ℕ} (hr : 1 ≤ r) : Monotone (degreeMultiplier r) := by
  intro i n hin
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hi : 0 ≤ (i : ℝ) := by positivity
  have hn : (i : ℝ) ≤ n := by exact_mod_cast hin
  unfold degreeMultiplier
  nlinarith

theorem degreeMultiplier_pos {r n : ℕ} (hr : 1 ≤ r) (hn : 0 < n) :
    0 < degreeMultiplier r n := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold degreeMultiplier
  exact mul_pos hn' (by linarith)

@[simp] theorem degreeMultiplier_zero (r : ℕ) : degreeMultiplier r 0 = 0 := by
  simp [degreeMultiplier]

@[simp] theorem degreeMultiplier_succ (r n : ℕ) :
    degreeMultiplier r (n+1) = radialDivisor r n := by
  simp only [degreeMultiplier, radialDivisor, Nat.cast_add, Nat.cast_one]
  ring

/-- The harmless cutoff only makes the coefficient ratio bounded for
indices outside the convolution range. -/
def ratio (r n i : ℕ) : ℝ := degreeMultiplier r (min i n) / degreeMultiplier r n

theorem ratio_mem_Icc {r : ℕ} (hr : 1 ≤ r) (n i : ℕ) : ratio r n i ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (degreeMultiplier_nonneg hr _) (degreeMultiplier_nonneg hr _), ?_⟩
  by_cases hn : n = 0
  · simp [ratio, hn]
  · exact (div_le_one (degreeMultiplier_pos hr (Nat.pos_of_ne_zero hn))).mpr
      (degreeMultiplier_mono hr (min_le_right _ _))

theorem ratio_of_le (r n i : ℕ) (hi : i ≤ n) :
    ratio r n i = degreeMultiplier r i / degreeMultiplier r n := by
  simp only [ratio, min_eq_left hi]

def insertFamily (I : Window) (ε : ℝ) (r : ℕ) (A B : AxisSpace I ε)
    (n m : ℕ) (x : ℝ) : ℝ :=
  jetProduct (fun i k => ratio r n i * inputJet I ε A i k x)
    (fun j l => inputJet I ε B j l x) n m

theorem insertFamily_continuous (I : Window) (ε : ℝ) (r : ℕ)
    (A B : AxisSpace I ε) (n m : ℕ) :
    ContinuousOn (insertFamily I ε r A B n m) I.interval := by
  change ContinuousOn (fun x => ∑ ij ∈ antidiagonal n,
    leibnizSum (fun k => ratio r n ij.1 * inputJet I ε A ij.1 k x)
      (fun l => inputJet I ε B ij.2 l x) m) I.interval
  apply continuousOn_finsetSum
  intro ij _
  apply continuousOn_leibnizSum I
  · intro k
    exact continuousOn_const.mul (continuous_jet I (weight ε) A.1 ij.1 k).continuousOn
  · intro k
    exact (continuous_jet I (weight ε) B.1 ij.2 k).continuousOn

theorem insertFamily_deriv (I : Window) (ε : ℝ) (r : ℕ)
    (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) (hx : x ∈ I.interval) :
    HasDerivWithinAt (insertFamily I ε r A B n m)
      (insertFamily I ε r A B n (m+1) x) I.interval x := by
  exact HasDerivWithinAt.fun_sum (u := antidiagonal n) (fun ij _ =>
    hasDerivWithinAt_leibnizSum I _ _
      (fun k y hy => (hasDerivWithinAt_jet I (weight ε) A ij.1 k hy).const_mul (ratio r n ij.1))
      (fun k y hy => hasDerivWithinAt_jet I (weight ε) B ij.2 k hy) m hx)

theorem insertFamily_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : 1 ≤ r) (A B : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    |insertFamily I ε r A B n m x| ≤ (64 * ‖A‖ * ‖B‖) * weight ε n m := by
  apply jetProduct_bound hε (norm_nonneg A) (norm_nonneg B)
  · intro i k
    rw [abs_mul, abs_of_nonneg (ratio_mem_Icc hr n i).1]
    exact (mul_le_mul_of_nonneg_left (inputJet_bound I hε A i k x)
      (ratio_mem_Icc hr n i).1).trans
      (mul_le_of_le_one_left (mul_nonneg (norm_nonneg A) (weight_pos hε i k).le)
        (ratio_mem_Icc hr n i).2)
  · intro j k
    exact inputJet_bound I hε B j k x

/-- The first argument is an already inverted source. The second is
inserted before that inverse, with one algebra constant. -/
def insert (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) : AxisSpace I ε :=
  ofJetFamily I (weight ε) (weight_pos hε) (insertFamily I ε r A B)
    (insertFamily_continuous I ε r A B) (insertFamily_deriv I ε r A B)
    (64 * ‖A‖ * ‖B‖) (by positivity)
    (fun n m x _ => insertFamily_bound I hε hr A B n m x)

theorem norm_insert_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) : ‖insert I hε r hr A B‖ ≤ 64 * ‖A‖ * ‖B‖ :=
  norm_ofJetFamily_le _ _ _ _ _ _ _ _ _

theorem jet_insert (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n m : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    inputJet I ε (insert I hε r hr A B) n m x = insertFamily I ε r A B n m x := by
  unfold insert inputJet
  exact jet_ofJetFamily I (weight ε) (weight_pos hε) _ _ _ _ _ _ _ _ hx

theorem coefficient_insert (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (weight ε) (insert I hε r hr A B) n x =
      ∑ ij ∈ antidiagonal n, ratio r n ij.1 *
        coefficient I (weight ε) A ij.1 x * coefficient I (weight ε) B ij.2 x := by
  simpa only [insertFamily, jetProduct, antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, one_mul, coefficient] using
      jet_insert I hε r hr A B n 0 hx

/-- This operator really inserts the factor inside the inverse. -/
theorem insert_regularInverse (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (F B : AxisSpace I ε) :
    insert I hε r hr (regularInverse I hε r hr F) B =
      regularInverse I hε r hr (product I hε F B) := by
  apply coefficient_ext I (weight ε) (fun n m => (weight_pos hε n m).ne')
  intro n x hx
  rw [coefficient_insert I hε r hr _ _ n hx]
  cases n with
  | zero =>
      change _ = inputJet I ε (regularInverse I hε r hr (product I hε F B)) 0 0 x
      rw [jet_regularInverse_zero I hε r hr _ _ hx]
      simp [ratio]
  | succ n =>
      change _ = inputJet I ε (regularInverse I hε r hr (product I hε F B)) (n+1) 0 x
      rw [jet_regularInverse_succ I hε r hr _ _ _ hx]
      change _ = coefficient I (weight ε) (product I hε F B) n x / radialDivisor r n
      rw [coefficient_product I hε F B n hx, sum_antidiagonal_succ]
      simp only [ratio, Nat.zero_min, degreeMultiplier_zero, zero_div, zero_mul, zero_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ij hij
      have hi : ij.1+1 ≤ n+1 := Nat.succ_le_succ (Nat.le.intro (mem_antidiagonal.mp hij))
      rw [min_eq_left hi, degreeMultiplier_succ, degreeMultiplier_succ]
      change (radialDivisor r ij.1 / radialDivisor r n) *
        inputJet I ε (regularInverse I hε r hr F) (ij.1+1) 0 x * _ = _
      rw [jet_regularInverse_succ I hε r hr _ _ _ hx]
      have hd := radialDivisor_pos hr ij.1
      field_simp [hd.ne']
      simp only [coefficient]
      ring

/-- Repeat insertion for any finite list of factors. -/
def insertFactors (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) : List (AxisSpace I ε) → AxisSpace I ε
  | [] => A
  | B :: Bs => insertFactors I hε r hr (insert I hε r hr A B) Bs

theorem norm_insertFactors_le (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) (Bs : List (AxisSpace I ε)) :
    ‖insertFactors I hε r hr A Bs‖ ≤ 64 ^ Bs.length * ‖A‖ * (Bs.map norm).prod := by
  induction Bs generalizing A with
  | nil => simp [insertFactors]
  | cons B Bs ih =>
      apply (ih (insert I hε r hr A B)).trans
      have hp : 0 ≤ (Bs.map norm).prod := by
        apply List.prod_nonneg
        intro a ha
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
        exact norm_nonneg v
      calc
        _ ≤ 64 ^ Bs.length * (64 * ‖A‖ * ‖B‖) * (Bs.map norm).prod :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (norm_insert_le I hε r hr A B) (by positivity)) hp
        _ = _ := by simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]; ring

/-- Recover the source coefficients by applying the radial differential
operator to a zero-constant inverse. These coefficients need not themselves
belong to the bounded axis space. -/
def recoveredSource (I : Window) (ε : ℝ) (r : ℕ) (A : AxisSpace I ε)
    (n : ℕ) (x : ℝ) : ℝ := radialDivisor r n * coefficient I (weight ε) A (n+1) x

theorem recoveredSource_insert (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    recoveredSource I ε r (insert I hε r hr A B) n x =
      ∑ ij ∈ antidiagonal n, recoveredSource I ε r A ij.1 x *
        coefficient I (weight ε) B ij.2 x := by
  unfold recoveredSource
  rw [coefficient_insert I hε r hr A B _ hx, sum_antidiagonal_succ]
  simp only [ratio, Nat.zero_min, degreeMultiplier_zero, zero_div, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hi : ij.1+1 ≤ n+1 := Nat.succ_le_succ (Nat.le.intro (mem_antidiagonal.mp hij))
  rw [min_eq_left hi, degreeMultiplier_succ, degreeMultiplier_succ]
  field_simp [(radialDivisor_pos hr n).ne']

/-- Arbitrarily many undifferentiated factors cost exactly one additional
algebra constant apiece in the mixed derivative estimate. -/
theorem norm_mixed_extra_factors (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (F G : AxisSpace I ε) (Bs : List (AxisSpace I ε)) :
    ‖insertFactors I hε r hr (inverseMixed I hε r hr F G) Bs‖ ≤
      64 ^ Bs.length * (5120 / ε * ‖F‖ * ‖G‖) * (Bs.map norm).prod := by
  apply (norm_insertFactors_le I hε r hr _ Bs).trans
  have hb : ‖inverseMixed I hε r hr F G‖ ≤ 5120 / ε * ‖F‖ * ‖G‖ := by
    have ht := norm_bilinearValue_le I hε (inverseMixedData I hε r hr) F G
    change ‖inverseMixed I hε r hr F G‖ ≤ (64 * (80 / ε)) * ‖F‖ * ‖G‖ at ht
    convert ht using 1
    ring
  have hp : 0 ≤ (Bs.map norm).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg v
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by positivity)) hp

theorem coefficient_insert_zero (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A B : AxisSpace I ε) {x : ℝ} (hx : x ∈ I.interval) :
    coefficient I (weight ε) (insert I hε r hr A B) 0 x = 0 := by
  rw [coefficient_insert I hε r hr A B 0 hx]
  simp [ratio]

/-- The recovered mixed source is the actual coefficient convolution of
the parameter derivative of F with the logarithmic radial derivative of G. -/
theorem recoveredSource_mixed (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (F G : AxisSpace I ε) (n : ℕ) {x : ℝ} (hx : x ∈ I.interval) :
    recoveredSource I ε r (inverseMixed I hε r hr F G) n x =
      ∑ ij ∈ antidiagonal n, inputJet I ε F ij.1 1 x *
        ((ij.2 : ℝ) * coefficient I (weight ε) G ij.2 x) := by
  unfold recoveredSource
  change radialDivisor r n * inputJet I ε (inverseMixed I hε r hr F G) (n+1) 0 x = _
  rw [jet_inverseMixed I hε r hr F G (n+1) 0 hx]
  simp only [differentialFamily, antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [coefficient]
  field_simp [(radialDivisor_pos hr n).ne']

/-- Any established norm estimate, including omission of either derivative
or radial averaging, acquires the same one-constant-per-factor bound. -/
theorem norm_extra_factors_of_bound (I : Window) {ε : ℝ} (hε : 0 < ε) (r : ℕ) (hr : 1 ≤ r)
    (A : AxisSpace I ε) (Bs : List (AxisSpace I ε)) {K : ℝ} (hK : ‖A‖ ≤ K) :
    ‖insertFactors I hε r hr A Bs‖ ≤ 64 ^ Bs.length * K * (Bs.map norm).prod := by
  apply (norm_insertFactors_le I hε r hr A Bs).trans
  have hp : 0 ≤ (Bs.map norm).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    exact norm_nonneg v
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (by positivity)) hp

end NavierStokes.AxisInverseFactors
