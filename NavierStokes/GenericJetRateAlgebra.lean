import NavierStokes.DiagonalResidual

noncomputable section

namespace NavierStokes.GenericDifferentialPolynomial

open Set Filter DiagonalResidual
open scoped Topology ContDiff

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
private local instance : NormedAddCommGroup ((D →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance
private local instance : NormedSpace ℝ ((D →L[ℝ] ℝ) →L[ℝ] ℝ) := inferInstance

variable {l : Filter D} {q : D → ℝ} {U : Set D} {f g : D → ℝ}

theorem rate_zero {m : ℕ} {r : ℝ} : JetRate l q (fun _ : D => (0 : ℝ)) m r := by
  exact ⟨0, le_rfl, Eventually.of_forall (fun _ => by simp)⟩

theorem rate_mul (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {m : ℕ} {r s : ℝ} (hr : FiniteJetRate l q f m r)
    (hs : FiniteJetRate l q g m s) :
    JetRate l q (fun x => f x * g x) m (r + s) := by
  obtain ⟨A, hA, hbA⟩ := hr
  obtain ⟨B, hB, hbB⟩ := hs
  let L := ContinuousLinearMap.mul ℝ ℝ
  refine ⟨‖L‖ * 2 ^ m * A * B, by positivity, ?_⟩
  filter_upwards [hlU, hq, hbA, hbB] with x hx hqx hAx hBx
  calc
    _ ≤ ‖L‖ * 2 ^ m * (A * q x ^ r) * (B * q x ^ s) :=
      ResidualStability.norm_jet_bilinear_bound L hU hf hg hx m hAx hBx
    _ = (‖L‖ * 2 ^ m * A * B) * q x ^ (r + s) := by
      rw [Real.rpow_add hqx.1]
      ring

theorem smooth_directional (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (v : D) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem rate_directional (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (v : D) {m : ℕ} {r : ℝ}
    (hr : JetRate l q f (m + 1) r) :
    JetRate l q (fun x => fderiv ℝ f x v) m r := by
  obtain ⟨C, hC, hb⟩ := hr
  let L := ContinuousLinearMap.apply ℝ ℝ v
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hlU, hb] with x hx hbx
  exact (ResidualStability.norm_jet_linear_map_fderiv L hU hf hx m).trans
    ((mul_le_mul_of_nonneg_left hbx (norm_nonneg L)).trans_eq (mul_assoc _ _ _).symm)

theorem directional_sub_eqOn (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) (v : D) :
    EqOn (fun x => fderiv ℝ (fun y => f y - g y) x v)
      (fun x => fderiv ℝ f x v - fderiv ℝ g x v) U := by
  intro x hx
  change fderiv ℝ (f - g) x v = _
  rw [fderiv_sub ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  rfl

end NavierStokes.GenericDifferentialPolynomial
