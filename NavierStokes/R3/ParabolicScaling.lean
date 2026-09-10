import NavierStokes.R3.ParabolicCalculus
import NavierStokes.R3.ParabolicEnergy
import NavierStokes.R3.ParabolicSupport

/-!
# Parabolic compression with singular time fixed at one

The clock is `l²(t-1)+1`. Extension by zero before the original initial time
makes the compressed solution start from rest, while the spatial support is
divided by the arbitrary factor `l > 1`. Viscosity remains unchanged.
-/

noncomputable section

namespace NavierStokesR3.ParabolicScaling

open NavierStokes.ProblemStatement Set
open scoped ContDiff

theorem pull_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiff ℝ ∞ g) (a l : ℝ) :
    ContDiff ℝ ∞ (pull a l g) := by
  exact (hg.comp (((contDiff_fst.sub contDiff_const).const_smul (l ^ 2)).add
    contDiff_const |>.prodMk (contDiff_snd.const_smul l))).const_smul a

theorem pull_smooth_on {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : SpaceTime → V} (hg : ContDiffOn ℝ ∞ g (Iio 1 ×ˢ univ))
    (a : ℝ) {l : ℝ} (hl : 0 < l) :
    ContDiffOn ℝ ∞ (pull a l g) (Iio 1 ×ˢ univ) := by
  apply (hg.comp ?_ ?_).const_smul a
  · exact (((contDiff_fst.sub contDiff_const).const_smul (l ^ 2)).add
      contDiff_const |>.prodMk (contDiff_snd.const_smul l)).contDiffOn
  · intro z hz
    exact ⟨clock_lt_one hl hz.1, mem_univ _⟩

theorem velocity_smooth {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ContDiffOn ℝ ∞ (velocity l u) (Iio 1 ×ˢ univ) :=
  pull_smooth_on (zeroBefore_smooth_on hc.velocity_smooth
    (fun t ht x => (hrest t ht x).1)) l (by linarith)

theorem pressure_smooth {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ContDiffOn ℝ ∞ (pressure l p) (Iio 1 ×ˢ univ) :=
  pull_smooth_on (zeroBefore_smooth_on hc.pressure_smooth
    (fun t ht x => (hrest t ht x).2)) (l ^ 2) (by linarith)

theorem zeroBefore_support {V : Type*} [Zero V] {g : SpaceTime → V} {K : Set Space}
    (hg : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => g (t, x)) ⊆ K)
    {t : ℝ} (ht : t < 1) : tsupport (fun x => zeroBefore g (t, x)) ⊆ K := by
  by_cases ht0 : 0 ≤ t
  · simpa only [zeroBefore, ite_eq_left ht0] using hg t ⟨ht0, ht⟩
  · simp [zeroBefore, ht0]

theorem pull_zeroBefore_support {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    {g : SpaceTime → V} {K : Set Space}
    (hg : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => g (t, x)) ⊆ K)
    (a : ℝ) {l : ℝ} (hl : 0 < l) {t : ℝ} (ht : t < 1) :
    tsupport (fun x => pull a l (zeroBefore g) (t, x)) ⊆
      (fun x : Space => l⁻¹ • x) '' K :=
  ProblemStatement.tsupport_spatialScale_subset
    (zeroBefore_support hg (clock_lt_one hl ht)) a l hl.ne'

theorem velocity_support_before_one {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hc : ProblemStatement.CandidateProperties ν u p f K)
    {l t : ℝ} (hl : 1 < l) (ht : t < 1) :
    tsupport (fun x => velocity l u (t, x)) ⊆ (fun x : Space => l⁻¹ • x) '' K :=
  pull_zeroBefore_support hc.velocity_support l (by linarith) ht

theorem pressure_support_before_one {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hc : ProblemStatement.CandidateProperties ν u p f K)
    {l t : ℝ} (hl : 1 < l) (ht : t < 1) :
    tsupport (fun x => pressure l p (t, x)) ⊆ (fun x : Space => l⁻¹ • x) '' K :=
  pull_zeroBefore_support hc.pressure_support (l ^ 2) (by linarith) ht

theorem force_support {f : VelocityField} (hf : ProblemStatement.CompactPositiveTimeSupport f)
    {l : ℝ} (hl : 1 < l) : ProblemStatement.CompactPositiveTimeSupport (force l f) := by
  have hl0 : 0 < l := by linarith
  have hd : 1 - l ^ 2 ≤ 0 := by nlinarith
  have h := hf.affineScale (l ^ 3) l (l ^ 2) (1 - l ^ 2) hl0.ne'
    (sq_pos_of_pos hl0) hd
  have he : force l f = (fun z : SpaceTime => l ^ 3 • f (l ^ 2 * z.1 + (1 - l ^ 2), l • z.2)) := by
    funext z
    apply congrArg (fun s : ℝ => l ^ 3 • f (s, l • z.2))
    dsimp [clock]
    ring
  rw [he]
  exact h

/-- The precise delayed parabolic scaling used in the periodic corollary. -/
theorem compressedCandidate {ν : ℝ} {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hc : ProblemStatement.CandidateProperties ν u p f K)
    (hrest : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x : Space, u (t, x) = 0 ∧ p (t, x) = 0)
    {l : ℝ} (hl : 1 < l) :
    ProblemStatement.CandidateProperties ν (velocity l u) (pressure l p) (force l f)
      ((fun x : Space => l⁻¹ • x) '' K) := by
  have hl0 : 0 < l := by linarith
  have hu := zeroBefore_smooth_on hc.velocity_smooth (fun t ht x => (hrest t ht x).1)
  refine {
    velocity_smooth := (velocity_smooth hc hrest hl).mono (fun z hz => ⟨hz.1.2, hz.2⟩)
    pressure_smooth := (pressure_smooth hc hrest hl).mono (fun z hz => ⟨hz.1.2, hz.2⟩)
    support_compact := ProblemStatement.isCompact_spatialScale_image hc.support_compact l
    velocity_support := fun t ht => velocity_support_before_one hc hl ht.2
    pressure_support := fun t ht => pressure_support_before_one hc hl ht.2
    force_smooth := pull_smooth hc.force_smooth _ _
    force_support := force_support hc.force_support hl
    zero_initial_velocity := ?_
    divergence_free := ?_
    navier_stokes := ?_
    energy_bounded := velocity_energy_bounded hc.energy_bounded hl
    speed_unbounded := velocity_speed_unbounded hc.speed_unbounded hl
  }
  · intro x
    change l • zeroBefore u (clock l 0, l • x) = 0
    rw [zeroBefore_eq_zero_of_nonpos (z := (clock l 0, l • x))
      (fun t ht y => (hrest t ht y).1) (clock_zero_nonpos hl.le), smul_zero]
  · intro t ht x
    rw [velocity, pull_divergence]
    by_cases hs : 0 ≤ clock l t
    · have he : (fun y => zeroBefore u (clock l t, y)) = fun y => u (clock l t, y) := by
        funext y; exact zeroBefore_eq_of_nonneg u hs
      simp only [spatialDivergence, spatialDerivative, he]
      change (l * l) * spatialDivergence u (clock l t) (l • x) = 0
      rw [hc.divergence_free _ ⟨hs, clock_lt_one hl0 ht.2⟩, mul_zero]
    · have he : (fun y => zeroBefore u (clock l t, y)) = fun _ => 0 := by
        funext y; exact zeroBefore_eq_zero_of_neg u (lt_of_not_ge hs)
      simp [spatialDivergence, spatialDerivative, he]
  · intro t ht x
    have htime : DifferentiableAt ℝ (fun s => zeroBefore u (s, l • x)) (clock l t) := by
      have hat := hu.contDiffAt (x := (clock l t, l • x)) ((isOpen_Iio.prod isOpen_univ).mem_nhds
        ⟨clock_lt_one hl0 ht.2, mem_univ (l • x)⟩)
      exact (hat.comp (clock l t) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    rw [velocity, pressure, pull_residual ν l _ _ t x htime,
      zeroBefore_residual hc hrest (clock_lt_one hl0 ht.2)]
    rfl

end NavierStokesR3.ParabolicScaling
