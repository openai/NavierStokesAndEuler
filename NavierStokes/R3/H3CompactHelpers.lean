import NavierStokes.R3.ViscousEnergyBalance

noncomputable section

open Set Filter MeasureTheory Function
open scoped Topology BigOperators ContDiff

namespace NavierStokesR3.H3Compact

open ProblemStatement
open NavierStokes.ProblemStatement (coordinateVector)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)

/-- Coordinate derivatives are genuine spatial derivatives, including at a
closed time interval's endpoints. -/
def partialField (i : Fin 3) (u : VelocityField) : VelocityField :=
  fun z => spatialPartial i (fun y => u (z.1, y)) z.2

private theorem infinity_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

theorem partialField_contDiffOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (i : Fin 3) :
    ContDiffOn ℝ ∞ (partialField i u) (slab a b) := by
  have hs : UniqueDiffOn ℝ (slab a b) :=
    (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hc := (hu.fderivWithin hs infinity_add_one_le).clm_apply
    (show ContDiffOn ℝ ∞ (fun _ : SpaceTime => ((0 : ℝ), coordinateVector i))
      (slab a b) from contDiffOn_const)
  apply hc.congr
  intro z hz
  change NavierStokes.ProblemStatement.spatialDerivative u z.1 z.2 (coordinateVector i) = _
  rw [NavierStokes.PeriodicUniqueness.spatialDerivative_eq_within_comp hu hz.1 z.2]
  rfl

theorem partialField_support {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K) (i : Fin 3) :
    ∀ t ∈ Icc a b, tsupport (fun x => partialField i u (t, x)) ⊆ K := by
  intro t ht
  change tsupport (fun x => fderiv ℝ (fun y => u (t, y)) x (coordinateVector i)) ⊆ K
  exact (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans (hsupp t ht)

/-- An arbitrary ordered word of ordinary coordinate derivatives. -/
def partialWord : List (Fin 3) → VelocityField → VelocityField
  | [], u => u
  | i :: is, u => partialField i (partialWord is u)

theorem partialWord_contDiffOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (is : List (Fin 3)) :
    ContDiffOn ℝ ∞ (partialWord is u) (slab a b) := by
  induction is with
  | nil => exact hu
  | cons i is ih => exact partialField_contDiffOn hab ih i

theorem partialWord_support {a b : ℝ} {u : VelocityField} {K : Set Space}
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    (is : List (Fin 3)) :
    ∀ t ∈ Icc a b, tsupport (fun x => partialWord is u (t, x)) ⊆ K := by
  induction is with
  | nil => exact hsupp
  | cons i is ih => exact partialField_support ih i

theorem partialWord_square_integrable {a b : ℝ} (hab : a < b) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    (is : List (Fin 3)) {t : ℝ} (ht : t ∈ Icc a b) :
    Integrable (fun x : Space => ‖partialWord is u (t, x)‖ ^ 2) := by
  exact CompactEnergy.integrable_norm_sq
    (spatial_smooth (partialWord_contDiffOn hab hu is) ht).continuous
    (CompactEnergy.slice_compact hK (partialWord_support hsupp is t ht))

theorem partialWord_square_continuousOn {a b : ℝ} (hab : a < b) {u : VelocityField}
    {K : Set Space} (hK : IsCompact K) (hu : ContDiffOn ℝ ∞ u (slab a b))
    (hsupp : ∀ t ∈ Icc a b, tsupport (fun x => u (t, x)) ⊆ K)
    (is : List (Fin 3)) :
    ContinuousOn (fun t => ∫ x : Space, ‖partialWord is u (t, x)‖ ^ 2) (Icc a b) := by
  apply CompactTimeIntegral.continuousOn_integral hK
    ((partialWord_contDiffOn hab hu is).continuousOn.norm.pow 2)
  intro t ht x hx
  change ‖partialWord is u (t, x)‖ ^ 2 = 0
  rw [CompactEnergy.zero_outside (partialWord_support hsupp is t ht) hx]
  simp

end NavierStokesR3.H3Compact
