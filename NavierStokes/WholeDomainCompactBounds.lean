import NavierStokes.JointResidualLimits
import NavierStokes.DiagonalResidual
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Uniform bounds on the common finite-stage domain

Local endpoint estimates are upgraded on a fixed compact set without changing
the domain with the requested derivative order. The compactness argument uses
the actual derivatives, and allows a different local constant at every point.
-/

noncomputable section

namespace NavierStokes.WholeDomainStageBounds

open Set Filter Function ProblemStatement
open scoped Topology ContDiff BigOperators

section CompactBounds

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pointwise local rates on a compact cover imply one bound on the whole
covered part of the domain. No common neighborhood is assumed. -/
theorem compact_bound_of_local_rates {K S : Set D} (hK : IsCompact K)
    {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (hq : ∀ x ∈ S, 0 < q x)
    (hloc : ∀ x ∈ K, DiagonalResidual.JetRate (𝓝[S] x) q f m r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K ∩ S,
      ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r := by
  choose C hC hb using hloc
  let U : ∀ x ∈ K, Set D := fun x hx =>
    {y | y ∈ S → ‖iteratedFDeriv ℝ m f y‖ ≤ C x hx * q y ^ r}
  have hU : ∀ x (hx : x ∈ K), U x hx ∈ 𝓝 x := by
    intro x hx
    exact eventually_nhdsWithin_iff.mp (hb x hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hU
  refine ⟨∑ x ∈ t, C x x.2, Finset.sum_nonneg (fun x _ => hC x x.2), ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.mp (ht hy.1)
  have hCy : C x x.2 ≤ ∑ z ∈ t, C z z.2 :=
    Finset.single_le_sum (f := fun z : K => C z z.2) (fun z _ => hC z z.2) hxt
  exact (hyU hy.2).trans (mul_le_mul_of_nonneg_right hCy
    (Real.rpow_nonneg (hq y hy.2).le r))

/-- A globally supported family needs compactness only on the support.
This keeps the bound uniform over the unbounded ambient domain. -/
theorem bound_of_local_rates_and_zero {K S : Set D} (hK : IsCompact K)
    {q : D → ℝ} {f : D → V} {m : ℕ} {r : ℝ}
    (hq : ∀ x ∈ S, 0 < q x)
    (hloc : ∀ x ∈ K, DiagonalResidual.JetRate (𝓝[S] x) q f m r)
    (hz : ∀ x ∈ S, x ∉ K → iteratedFDeriv ℝ m f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S,
      ‖iteratedFDeriv ℝ m f x‖ ≤ C * q x ^ r := by
  obtain ⟨C, hC, hb⟩ := compact_bound_of_local_rates hK hq hloc
  refine ⟨C, hC, fun x hx => ?_⟩
  by_cases hKx : x ∈ K
  · exact hb x ⟨hKx, hx⟩
  · rw [hz x hx hKx, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (hq x hx).le r)

end CompactBounds

section LocalRates

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite jet limit at a positive limiting scale gives every power rate. -/
theorem rate_of_jet_limit {l : Filter D} {f : D → V} {q : D → ℝ} {m : ℕ}
    {J : D [×m]→L[ℝ] V} {q₀ : ℝ} (hJ : Tendsto (iteratedFDeriv ℝ m f) l (𝓝 J))
    (hq : Tendsto q l (𝓝 q₀)) (hq₀ : 0 < q₀) (r : ℝ) :
    DiagonalResidual.JetRate l q f m r := by
  have hb := (hJ.norm.mul (hq.rpow_const (Or.inl hq₀.ne'))).eventually
    (gt_mem_nhds (lt_add_one (‖J‖ * q₀ ^ (-r))))
  refine ⟨‖J‖ * q₀ ^ (-r) + 1, by positivity, ?_⟩
  filter_upwards [hb, hq.eventually (lt_mem_nhds hq₀)] with x hx hqx
  have he : (‖iteratedFDeriv ℝ m f x‖ * q x ^ (-r)) * q x ^ r =
      ‖iteratedFDeriv ℝ m f x‖ := by
    rw [mul_assoc, ← Real.rpow_add hqx, neg_add_cancel, Real.rpow_zero, mul_one]
  exact he ▸ mul_le_mul_of_nonneg_right hx.le (Real.rpow_nonneg hqx.le r)

end LocalRates

/-- Smooth one-sided velocity and pressure extensions extend the actual
residual, including the derivatives occurring in its definition. -/
noncomputable def residualExtension {u : VelocityField} {p : PressureField} {x : Space}
    (U : JointResidualLimits.OneSidedExtension u x)
    (P : JointResidualLimits.OneSidedExtension p x) :
    JointResidualLimits.OneSidedExtension
      (fun w => navierStokesResidual u p w.1 w.2) x where
  value := fun w => navierStokesResidual U.value P.value w.1 w.2
  domain := U.domain ∩ P.domain
  isOpen := U.isOpen.inter P.isOpen
  mem := ⟨U.mem, P.mem⟩
  smooth := ResidualRegularity.contDiffOn_residual (U.isOpen.inter P.isOpen)
    (U.smooth.mono inter_subset_left) (P.smooth.mono inter_subset_right)
  agrees := by
    intro w hw
    have hU : U.value =ᶠ[𝓝 w] u :=
      Filter.eventuallyEq_of_mem ((U.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds
        ⟨hw.1.1, hw.2⟩) U.agrees
    have hP : P.value =ᶠ[𝓝 w] p :=
      Filter.eventuallyEq_of_mem ((P.isOpen.inter (SpacetimeEndpoint.openPast_isOpen 1)).mem_nhds
        ⟨hw.1.2, hw.2⟩) P.agrees
    exact (ResidualRegularity.residual_eventuallyEq hU hP).self_of_nhds

end NavierStokes.WholeDomainStageBounds
