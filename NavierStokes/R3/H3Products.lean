import NavierStokes.R3.H3Comparison

/-! # L² product limits used in Sobolev energy comparison -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace NavierStokesR3.H3Comparison

open NavierStokes.ProblemStatement

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinear_norm_le (B : E →L[ℝ] F →L[ℝ] G) (x : E) (y : F) :
    ‖B x y‖ ≤ ‖B‖ * ‖x‖ * ‖y‖ :=
  ((B x).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

/-- A bounded factor times an L² factor remains in L². -/
theorem memLp_bilinear_bounded (B : E →L[ℝ] F →L[ℝ] G)
    {f : Space → E} {g : Space → F} (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g 2 volume) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    MemLp (fun x => B (f x) (g x)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun x => B (f x) (g x)) volume :=
    ((B.continuous.comp continuous_fst).clm_apply continuous_snd).comp_aestronglyMeasurable
      (hf.prodMk hg.1)
  apply hg.of_le_mul hmeas
  exact Filter.Eventually.of_forall (fun x =>
    (bilinear_norm_le B (f x) (g x)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg B)) (norm_nonneg (g x))))

theorem norm_toLp_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {f : Space → E} {g : Space → F} (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g 2 volume) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    ‖(memLp_bilinear_bounded B hf hg hC).toLp (fun x => B (f x) (g x))‖ ≤
      (‖B‖ * C) * ‖hg.toLp g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(memLp_bilinear_bounded B hf hg hC).coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  exact (bilinear_norm_le B (f x) (g x)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg B)) (norm_nonneg (g x)))

/-- Uniform convergence in one factor and L² convergence in the other give
L² convergence of the product. The uniform error is an actual pointwise
bound tending to zero, not a derivative or energy identity assumption. -/
theorem tendsto_toLp_bilinear (B : E →L[ℝ] F →L[ℝ] G)
    {f : ℕ → Space → E} {g : ℕ → Space → F} {f₀ : Space → E} {g₀ : Space → F}
    (hf : ∀ n, AEStronglyMeasurable (f n) volume) (hf₀ : AEStronglyMeasurable f₀ volume)
    (hg : ∀ n, MemLp (g n) 2 volume) (hg₀ : MemLp g₀ 2 volume)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    (hfa : ∀ n x, ‖f n x - f₀ x‖ ≤ a n) {C : ℝ} (hC : ∀ x, ‖f₀ x‖ ≤ C)
    (hglim : Tendsto (fun n => (hg n).toLp (g n)) atTop (𝓝 (hg₀.toLp g₀))) :
    ∃ hp : ∀ n, MemLp (fun x => B (f n x) (g n x)) 2 volume,
      Tendsto (fun n => (hp n).toLp (fun x => B (f n x) (g n x))) atTop
        (𝓝 ((memLp_bilinear_bounded B hf₀ hg₀ hC).toLp (fun x => B (f₀ x) (g₀ x)))) := by
  have hfn (n : ℕ) (x : Space) : ‖f n x‖ ≤ C + a n := by
    calc
      ‖f n x‖ ≤ ‖f n x - f₀ x‖ + ‖f₀ x‖ := norm_le_norm_sub_add _ _
      _ ≤ a n + C := add_le_add (hfa n x) (hC x)
      _ = C + a n := add_comm _ _
  let hp (n : ℕ) := memLp_bilinear_bounded B (hf n) (hg n) (hfn n)
  let hp₀ := memLp_bilinear_bounded B hf₀ hg₀ hC
  let hA (n : ℕ) : MemLp (fun x => B (f n x - f₀ x) (g n x)) 2 volume :=
    memLp_bilinear_bounded B ((hf n).sub hf₀) (hg n) (hfa n)
  let hD (n : ℕ) : MemLp (fun x => B (f₀ x) (g n x - g₀ x)) 2 volume :=
    memLp_bilinear_bounded B hf₀ ((hg n).sub hg₀) hC
  refine ⟨hp, ?_⟩
  have hsplit (n : ℕ) : (hp n).toLp (fun x => B (f n x) (g n x)) -
      hp₀.toLp (fun x => B (f₀ x) (g₀ x)) =
      (hA n).toLp (fun x => B (f n x - f₀ x) (g n x)) +
        (hD n).toLp (fun x => B (f₀ x) (g n x - g₀ x)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub ((hp n).toLp _) (hp₀.toLp _),
      Lp.coeFn_add ((hA n).toLp _) ((hD n).toLp _),
      (hp n).coeFn_toLp, hp₀.coeFn_toLp, (hA n).coeFn_toLp, (hD n).coeFn_toLp]
      with x hsub hadd hx hy hz ht
    simp only [Pi.sub_apply, Pi.add_apply] at hsub hadd hx hy hz ht
    rw [hsub, hadd, hx, hy, hz, ht]
    simp only [map_sub, _root_.sub_apply]
    abel
  have hbound (n : ℕ) :
      ‖(hp n).toLp (fun x => B (f n x) (g n x)) - hp₀.toLp (fun x => B (f₀ x) (g₀ x))‖ ≤
        (‖B‖ * a n) * ‖(hg n).toLp (g n)‖ + (‖B‖ * C) * ‖(hg n).toLp (g n) - hg₀.toLp g₀‖ := by
    rw [hsplit]
    apply (norm_add_le _ _).trans
    apply add_le_add (norm_toLp_bilinear_le B ((hf n).sub hf₀) (hg n) (hfa n))
    simpa only [MemLp.toLp_sub] using! norm_toLp_bilinear_le B hf₀ ((hg n).sub hg₀) hC
  have hz : Tendsto (fun n => (‖B‖ * a n) * ‖(hg n).toLp (g n)‖ +
      (‖B‖ * C) * ‖(hg n).toLp (g n) - hg₀.toLp g₀‖) atTop (𝓝 0) := by
    have h1 := (ha.const_mul ‖B‖).mul hglim.norm
    have h2 := (hglim.sub (tendsto_const_nhds (x := hg₀.toLp g₀))).norm.const_mul (‖B‖ * C)
    simpa only [mul_zero, zero_mul, sub_self, norm_zero, add_zero] using h1.add h2
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hz)

end NavierStokesR3.H3Comparison
