import NavierStokes.PhysicalStageBounds
import NavierStokes.SharpPhysicalCopyBounds

noncomputable section
namespace NavierStokes.PhysicalStageBounds.WaveData
open Set Function Filter ProblemStatement
open SharpPhysicalCarrier
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K J : Type*}

/-- Exact linear derivative loss for a genuine wave stage, derived from
its weighted native source, common-chart maps and phase profiles. -/
theorem scalar_log_bound (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1/2) (i : J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (W.scalar i) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := SharpPhysicalCopyBounds.physical_sum_log_bound_of_weighted
    W.source_bounds (W.chart i) (W.chart_maps i) (W.carrier i) (W.support i) (W.smooth i)
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le (W.frequencies i) m
  exact ⟨C,hC,N,fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

theorem vector_log_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  classical
  have hb := fun i => W.scalar_log_bound hh hh1 i m
  choose C hC N hbound using hb
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  refine ⟨3*∑ i, C i, mul_nonneg (by norm_num) hsum, ∑ i, N i, ?_⟩
  intro w hw hq
  have hq0 := PhysicalWaveSum.physicalQ_pos hh hh1 hw
  have hL : 1 ≤ 1+|Real.log (PhysicalWaveSum.physicalQ h w)| := by linarith [abs_nonneg (Real.log (PhysicalWaveSum.physicalQ h w))]
  have hci (i : Fin 3) : C i ≤ ∑ j, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have hni (i : Fin 3) : N i ≤ ∑ j, N j := Finset.single_le_sum (by intros; omega) (Finset.mem_univ i)
  have he := LocalPhysicalCopyBounds.vectorSum_jet_bound W.support W.smooth W.cells W.lower_pos hh hh1 hw m
    (B := (∑ i, C i)*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
      (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^(∑ i,N i))
    (fun i => (hbound i w hw hq).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (hci i) (Real.rpow_nonneg hq0.le _))
      (pow_le_pow_right₀ hL (hni i)) (by positivity) (by positivity)))
  exact he.trans_eq (by ring)

theorem pressure_log_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-(m:ℝ)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.scalar_log_bound hh hh1 () m
  refine ⟨‖Complex.reCLM‖*C, mul_nonneg (norm_nonneg _) hC,N,?_⟩
  intro w hw hq
  have hs := ((W.scalar_smooth hh hh1 ()).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)).of_le (nat_le_infty m)
  have he := PhysicalWaveSum.norm_jet_linear_comp_at hs Complex.reCLM
  exact he.trans ((mul_le_mul_of_nonneg_left (hb w hw hq) (norm_nonneg _)).trans_eq (by ring))

theorem curl_log_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl W.vector) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha+W.shift-((m:ℝ)+1)*derivativeCost h)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.vector_log_bound hh hh1 (m+1)
  refine ⟨‖PhysicalClassBounds.jointCurl‖*C, mul_nonneg (norm_nonneg PhysicalClassBounds.jointCurl) hC,N,?_⟩
  intro w hw hq
  have he := PhysicalClassBounds.spatialCurl_jet_bound PhysicalWaveSum.preterminal_open
    (W.vector_smooth hh hh1) hw m
  have hb' := hb w hw hq
  simp only [Nat.cast_add,Nat.cast_one] at hb'
  exact he.trans ((mul_le_mul_of_nonneg_left hb' (norm_nonneg PhysicalClassBounds.jointCurl)).trans_eq (by ring))

private theorem common_loss_bound {α σ q C : ℝ} {m k : ℕ}
    (hh : 0 ≤ h) (hσ : -(2*CoordinateAlgebra.A h) ≤ σ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : 0 ≤ C) (hkm : k ≤ m+1) (N : ℕ) :
    C*q^(h*α+σ-(k:ℝ)*derivativeCost h)*(1+|Real.log q|)^N ≤
      C*q^(h*α-physicalLoss h m)*(1+|Real.log q|)^N := by
  have hcost : 0 ≤ derivativeCost h := by unfold derivativeCost; linarith
  have hk : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have he : h*α-physicalLoss h m ≤ h*α+σ-(k:ℝ)*derivativeCost h := by
    unfold physicalLoss
    nlinarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hq hq1 he) hC) (by positivity)

/-- The full physical wave vector obeys the manuscript's common `ell_m`. -/
theorem vector_printed_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.vector_log_bound hh hh1 m
  exact ⟨C,hC,N,fun w hw hq => (hb w hw hq).trans
    (common_loss_bound hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC (by omega) N)⟩

/-- Pressure has the same printed loss, including the permitted `Q⁻²ᴬ` prefactor. -/
theorem pressure_printed_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.pressure_log_bound hh hh1 m
  exact ⟨C,hC,N,fun w hw hq => (hb w hw hq).trans
    (common_loss_bound hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC (by omega) N)⟩

/-- Recovering velocity by the actual spatial curl is included in `ell_m`. -/
theorem curl_printed_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1/2) (hshift : -(2*CoordinateAlgebra.A h) ≤ W.shift) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl W.vector) w‖ ≤
        C*PhysicalWaveSum.physicalQ h w^(h*W.alpha-physicalLoss h m)*
          (1+|Real.log (PhysicalWaveSum.physicalQ h w)|)^N := by
  obtain ⟨C,hC,N,hb⟩ := W.curl_log_bound hh hh1 m
  refine ⟨C,hC,N,?_⟩
  intro w hw hq
  apply (hb w hw hq).trans
  simpa only [Nat.cast_add,Nat.cast_one] using
    common_loss_bound (α := W.alpha) hh.le hshift (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq hC
      (show m+1 ≤ m+1 from le_rfl) N

end NavierStokes.PhysicalStageBounds.WaveData
