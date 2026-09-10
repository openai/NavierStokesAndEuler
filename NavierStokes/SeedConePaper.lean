import NavierStokes.UniformCone

/-!
# The compact large-lag assertion of the seed cone lemma

The coordinates here are the literal coordinates in `seed:cone-coordinates`.
The threshold is positive, includes its endpoint, and is common to every
point of the compact set, even when the shear magnitude crosses two.
-/

noncomputable section

open Set

namespace NavierStokes.SeedConePaper

/-- The squared shear parameter in the manuscript. -/
def shearMagnitude (a b : ℝ) : ℝ := a * (1 + (-b / a) ^ 2)

/-- The component of the stress in the unnormalized shear direction. -/
def parallelStress (a b p₁ p₂ : ℝ) : ℝ := p₁ + (-b / a) * p₂

/-- The component of the stress in the orthogonal unnormalized direction. -/
def transverseStress (a b p₁ p₂ : ℝ) : ℝ := p₂ - (-b / a) * p₁

/-- The two relaxed inequalities, including the positive radial shear. -/
def RelaxedCone (a b p₁ p₂ : ℝ) : Prop :=
  0 < a ∧ 2 < parallelStress a b p₁ p₂ ∧
    shearMagnitude a b < ConeAlgebra.coneBound
      (parallelStress a b p₁ p₂) (transverseStress a b p₁ p₂)

/-- The relaxed cone with the additional lower bound required by the waves. -/
def AdmissibleCone (a b p₁ p₂ : ℝ) : Prop :=
  RelaxedCone a b p₁ p₂ ∧ 2 < shearMagnitude a b

/-- The first assertion of `seed:cone-test`, in its original coordinates. -/
theorem admissible_iff {a b p₁ p₂ : ℝ} (ha : 0 < a)
    (hv : 2 < shearMagnitude a b) :
    AdmissibleCone a b p₁ p₂ ↔
      shearMagnitude a b < parallelStress a b p₁ p₂ ∧
        (shearMagnitude a b - 2) * transverseStress a b p₁ p₂ ^ 2 <
          2 * (parallelStress a b p₁ p₂ - shearMagnitude a b) ^ 2 := by
  simp only [AdmissibleCone, RelaxedCone, ha, hv, true_and, and_true]
  exact ConeAlgebra.true_cone_iff hv

/-- The compact large-lag assertion of `seed:cone-test`. The conclusion has
no lower bound on the shear magnitude. The theorem also covers an empty set. -/
theorem compact_large_lag {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K)
    (ha : ∀ z ∈ K, 0 < z.1)
    (hfirst : ∀ z ∈ K, 0 < z.1 - z.2.1 * z.2.2)
    (hsecond : ∀ z ∈ K,
      2 * z.2.1 * z.2.2 + z.2.1 ^ 2 / z.1 + (z.1 - 2) * z.2.2 ^ 2 < 2) :
    ∃ P : ℝ, 0 < P ∧ ∀ z ∈ K, ∀ p₁ : ℝ, P ≤ p₁ →
      RelaxedCone z.1 z.2.1 p₁ (z.2.2 * p₁) := by
  obtain ⟨_, p₀, _, hp₀, _, hlarge⟩ :=
    UniformCone.compact_equation_eleven hK
      continuous_fst.continuousOn
      (continuous_fst.comp continuous_snd).continuousOn
      (continuous_snd.comp continuous_snd).continuousOn ha hfirst hsecond
  refine ⟨p₀ + 1, by linarith, ?_⟩
  intro z hz p hp
  obtain ⟨hP, hv⟩ := hlarge p (by linarith) z hz
  have hparallel : parallelStress z.1 z.2.1 p (z.2.2 * p) =
      p * (1 - z.2.1 * z.2.2 / z.1) := by
    unfold parallelStress
    ring
  have htransverse : transverseStress z.1 z.2.1 p (z.2.2 * p) =
      p * (z.2.2 + z.2.1 / z.1) := by
    unfold transverseStress
    ring
  have hshear : shearMagnitude z.1 z.2.1 =
      z.1 * (1 + (z.2.1 / z.1) ^ 2) := by
    simp only [shearMagnitude, neg_div, neg_sq]
  exact ⟨ha z hz, by rwa [hparallel], by rwa [hshear, hparallel, htransverse]⟩

/-- The same compact threshold gives admissibility at every point where
the extra strict shear inequality holds. -/
theorem compact_large_lag_with_admissibility {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) (ha : ∀ z ∈ K, 0 < z.1)
    (hfirst : ∀ z ∈ K, 0 < z.1 - z.2.1 * z.2.2)
    (hsecond : ∀ z ∈ K,
      2 * z.2.1 * z.2.2 + z.2.1 ^ 2 / z.1 + (z.1 - 2) * z.2.2 ^ 2 < 2) :
    ∃ P : ℝ, 0 < P ∧ ∀ z ∈ K, ∀ p₁ : ℝ, P ≤ p₁ →
      RelaxedCone z.1 z.2.1 p₁ (z.2.2 * p₁) ∧
        (2 < shearMagnitude z.1 z.2.1 →
          AdmissibleCone z.1 z.2.1 p₁ (z.2.2 * p₁)) := by
  obtain ⟨P, hP, hcone⟩ := compact_large_lag hK ha hfirst hsecond
  exact ⟨P, hP, fun z hz p hp => ⟨hcone z hz p hp,
    fun hv => ⟨hcone z hz p hp, hv⟩⟩⟩

end NavierStokes.SeedConePaper
