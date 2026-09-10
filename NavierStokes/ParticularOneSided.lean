import NavierStokes.ParticularWithinPressure
import NavierStokes.ParticularWithinBounds
import NavierStokes.GenericEndpointExtension

/-! # The slow-time-zero clause of the common-torus particular inverse

Uniform interior jets determine genuine closed-side smoothness. The actual
common-torus velocity and pressure inherit these one-sided jets, uniformly
on compact parameter sets. No analytic regularity or open extension of an
arbitrary source is required.
-/

noncomputable section

namespace NavierStokes.ParticularOneSided

open Set Filter
open scoped ContDiff Topology
open CommonCoverSolve TorusInverse ParticularWaveBounds

section InputTraces

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniform bounds on every actual interior derivative and the continuous
zeroth trace imply genuine joint within smoothness on the closure. Thus
one-sided input jets can be supplied as limits, without an open extension.
-/
theorem contDiffOn_closure_of_uniform_jets {O : Set Y} (hO : IsOpen O)
    (hc : Convex ℝ O) {f : Y → E} (hf : ContDiffOn ℝ ∞ f O)
    (htrace : ContinuousOn f (closure O))
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ O, ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ContDiffOn ℝ ∞ f (closure O) := by
  have he := GenericEndpointExtension.closedField_contDiffOn hO hc hf hb
  have hi : EqOn (GenericEndpointExtension.closedField O f) f O :=
    fun _ hx => GenericEndpointExtension.closedField_eq hO hf hx
  have heq : EqOn (GenericEndpointExtension.closedField O f) f (closure O) :=
    hi.of_subset_closure he.continuousOn htrace subset_closure Subset.rfl
  exact he.congr (fun _ hx => (heq hx).symm)

end InputTraces

section UniformJets

variable {Y E : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact-set uniformity for all mixed boundary jets follows from the
proved joint within smoothness, at each fixed derivative order. -/
theorem uniformContinuousOn_jets {S : Set Y} (hS : UniqueDiffOn ℝ S)
    {f : Y → E} (hf : ContDiffOn ℝ ∞ f S)
    {K : Set Y} (hK : IsCompact K) (hKS : K ⊆ S) (n : ℕ) :
    UniformContinuousOn (iteratedFDerivWithin ℝ n f S) K :=
  hK.uniformContinuousOn_of_continuous
    ((hf.continuousOn_iteratedFDerivWithin
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) hS).mono hKS)

omit [NormedSpace ℝ Y] [NormedSpace ℝ E] in
theorem tendstoUniformlyOn_of_joint_continuous {s : Set ℝ} {K : Set Y}
    {F : ℝ → Y → E} (hK : IsCompact K)
    (hF : ContinuousOn F.uncurry (s ×ˢ K)) {t : ℝ} (ht : t ∈ s) :
    TendstoUniformlyOn F (F t) (𝓝[s] t) K := by
  intro u hu
  obtain ⟨v, hv, hnear⟩ := hK.mem_uniformity_of_prod hF ht (symmetrize_mem_uniformity hu)
  filter_upwards [hv] with r hr y hy
  exact (hnear r hr y hy).2

end UniformJets

section CommonTorus

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def slowDomain (W : Set X) : Set (ℝ × X) := Ici (0 : ℝ) ×ˢ W
def positiveDomain (W : Set X) : Set (ℝ × X) := Ioi (0 : ℝ) ×ˢ W

theorem slowDomain_convex {W : Set X} (hW : Convex ℝ W) :
    Convex ℝ (slowDomain W) := (convex_Ici 0).prod hW

theorem slowDomain_uniqueDiff {W : Set X} (hW : IsOpen W) :
    UniqueDiffOn ℝ (slowDomain W) := (uniqueDiffOn_Ici 0).prod hW.uniqueDiffOn

/-- The same construction is local in slow time; no values for τ≥T need
be smooth. This is the form used on compact sets with q>0. -/
theorem commonCoefficients_local_oneSided (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b T : ℝ} (hab : a ≤ b) {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hn : ∀ x ∈ (Ico 0 T ×ˢ W) ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (commonVelocity t f g hab κ) ((Ico 0 T ×ˢ W) ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (commonPressure t f g hab κ frequency) ((Ico 0 T ×ˢ W) ×ˢ univ) :=
  commonCoefficients_contDiffOn_within t f g hab ((convex_Ico 0 T).prod hcW)
    ((uniqueDiffOn_Ico 0 T).prod hW.uniqueDiffOn) hN hNd hK hδ hf hn hκ hcκ hsupp frequency

/-- Uniform convergence of the actual interior mixed jets to the genuine
one-sided boundary jets on any compact transverse parameter set. -/
theorem uniform_endpoint_jets {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 < T) {W : Set X} (hW : IsOpen W)
    {F : (ℝ × X) × Plane → E}
    (hF : ContDiffOn ℝ ∞ F ((Ico 0 T ×ˢ W) ×ˢ univ))
    {K : Set (X × Plane)} (hK : IsCompact K) (hKW : K ⊆ W ×ˢ univ) (n : ℕ) :
    TendstoUniformlyOn (fun τ z => iteratedFDeriv ℝ n F ((τ, z.1), z.2))
      (fun z => iteratedFDerivWithin ℝ n F ((Ico 0 T ×ˢ W) ×ˢ univ) ((0, z.1), z.2))
      (𝓝[>] (0 : ℝ)) K := by
  let S : Set ((ℝ × X) × Plane) := (Ico 0 T ×ˢ W) ×ˢ univ
  let J := iteratedFDerivWithin ℝ n F S
  have hS : UniqueDiffOn ℝ S := ((uniqueDiffOn_Ico 0 T).prod hW.uniqueDiffOn).prod uniqueDiffOn_univ
  have hJ : ContinuousOn J S := hF.continuousOn_iteratedFDerivWithin
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) hS
  have hjoint : ContinuousOn (fun z : ℝ × (X × Plane) => J ((z.1, z.2.1), z.2.2))
      (Ico 0 T ×ˢ K) :=
    hJ.comp ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd).continuousOn
      (fun _ hz => ⟨⟨hz.1, (hKW hz.2).1⟩, mem_univ _⟩)
  have hlim := tendstoUniformlyOn_of_joint_continuous
    (F := fun (τ : ℝ) (z : X × Plane) => J ((τ, z.1), z.2)) (s := Ico 0 T) hK hjoint
    (show (0 : ℝ) ∈ Ico 0 T from ⟨le_rfl, hT⟩)
  have hlim' : TendstoUniformlyOn (fun τ z => J ((τ, z.1), z.2))
      (fun z => J ((0, z.1), z.2)) (𝓝[Ioo 0 T] (0 : ℝ)) K :=
    fun u hu => (hlim u hu).filter_mono (nhdsWithin_mono _ Ioo_subset_Ico_self)
  rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
  apply hlim'.congr
  filter_upwards [self_mem_nhdsWithin] with τ hτ z hz
  have hpoint : ((τ, z.1), z.2) ∈ (Ioo 0 T ×ˢ W) ×ˢ (univ : Set Plane) :=
    ⟨⟨hτ, (hKW hz).1⟩, mem_univ _⟩
  have hsub : (Ioo 0 T ×ˢ W) ×ˢ (univ : Set Plane) ⊆ S :=
    Set.prod_mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl) Subset.rfl
  exact iteratedFDerivWithin_eq_iteratedFDeriv hS
    (((hF.mono hsub).contDiffAt (((isOpen_Ioo.prod hW).prod isOpen_univ).mem_nhds hpoint)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)) (hsub hpoint)

/-- The uniform one-sided endpoint clause for the actual common-torus
particular inverse, including pressure and every fixed mixed derivative. -/
theorem commonCoefficients_uniform_endpoint_jets
    (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b T : ℝ} (hab : a ≤ b) (hT : 0 < T)
    {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f ((Ico 0 T ×ˢ W) ×ˢ univ))
    (hn : ∀ x ∈ (Ico 0 T ×ˢ W) ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ)
    {C : Set (X × Plane)} (hC : IsCompact C) (hCW : C ⊆ W ×ˢ univ) (n : ℕ) :
    TendstoUniformlyOn
        (fun τ z => iteratedFDeriv ℝ n (commonVelocity t f g hab κ) ((τ, z.1), z.2))
        (fun z => iteratedFDerivWithin ℝ n (commonVelocity t f g hab κ)
          ((Ico 0 T ×ˢ W) ×ˢ univ) ((0, z.1), z.2)) (𝓝[>] (0 : ℝ)) C ∧
      TendstoUniformlyOn
        (fun τ z => iteratedFDeriv ℝ n (commonPressure t f g hab κ frequency) ((τ, z.1), z.2))
        (fun z => iteratedFDerivWithin ℝ n (commonPressure t f g hab κ frequency)
          ((Ico 0 T ×ˢ W) ×ˢ univ) ((0, z.1), z.2)) (𝓝[>] (0 : ℝ)) C := by
  obtain ⟨hv, hp⟩ := commonCoefficients_local_oneSided t f g hab hW hcW hN hNd hK hδ hf hn
    hκ hcκ hsupp frequency
  exact ⟨uniform_endpoint_jets hT hW hv hC hCW n, uniform_endpoint_jets hT hW hp hC hCW n⟩

/-- The paper's actual complex common-torus inverse, for arbitrary source
coefficients with one-sided slow regularity at τ=0. Primitive geometry and
source are the only smoothness inputs. -/
theorem commonCoefficients_oneSided (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal (slowDomain W ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (slowDomain W ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (slowDomain W ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (slowDomain W ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (slowDomain W ×ˢ univ))
    (hn : ∀ x ∈ slowDomain W ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ) :
    ContDiffOn ℝ ∞ (commonVelocity t f g hab κ) (slowDomain W ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (commonPressure t f g hab κ frequency) (slowDomain W ×ˢ univ) :=
  commonCoefficients_contDiffOn_within t f g hab (slowDomain_convex hcW)
    (slowDomain_uniqueDiff hW) hN hNd hK hδ hf hn hκ hcκ hsupp frequency

/-- Each actual interior joint derivative tends to its one-sided endpoint
jet, for velocity and pressure simultaneously. -/
theorem commonCoefficients_endpoint_jets (t : TangentData (ℝ × X) ProblemStatement.Space)
    (f : (ℝ × X) × Plane → HarmonicCalculus.ComplexVector) (g : Geometry)
    {a b : ℝ} (hab : a ≤ b) {W : Set X} (hW : IsOpen W) (hcW : Convex ℝ W)
    (hN : ContDiffOn ℝ ∞ t.normal (slowDomain W ×ˢ univ))
    (hNd : ContDiffOn ℝ ∞ t.normalDot (slowDomain W ×ˢ univ))
    (hK : ContDiffOn ℝ ∞ t.action (slowDomain W ×ˢ univ))
    (hδ : ContDiffOn ℝ ∞ t.damping (slowDomain W ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ f (slowDomain W ×ˢ univ))
    (hn : ∀ x ∈ slowDomain W ×ˢ univ, t.normal x ≠ 0)
    {κ : Plane → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsupp : tsupport κ ⊆ univ ×ˢ Ioo a b) (frequency : ℝ)
    {x : X} (hx : x ∈ W) (Y : Plane) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n (commonVelocity t f g hab κ))
        (𝓝[positiveDomain W ×ˢ univ] ((0, x), Y))
        (𝓝 (iteratedFDerivWithin ℝ n (commonVelocity t f g hab κ)
          (slowDomain W ×ˢ univ) ((0, x), Y))) ∧
      Tendsto (iteratedFDeriv ℝ n (commonPressure t f g hab κ frequency))
        (𝓝[positiveDomain W ×ˢ univ] ((0, x), Y))
        (𝓝 (iteratedFDerivWithin ℝ n (commonPressure t f g hab κ frequency)
          (slowDomain W ×ˢ univ) ((0, x), Y))) := by
  obtain ⟨hv, hp⟩ := commonCoefficients_oneSided t f g hab hW hcW hN hNd hK hδ hf hn
    hκ hcκ hsupp frequency
  have hOS : positiveDomain W ×ˢ (univ : Set Plane) ⊆ slowDomain W ×ˢ univ := by
    intro z hz
    have ht : 0 < z.1.1 := hz.1.1
    exact ⟨⟨ht.le, hz.1.2⟩, hz.2⟩
  have he : (((0 : ℝ), x), Y) ∈ slowDomain W ×ˢ (univ : Set Plane) := by
    change (0 ≤ (0 : ℝ) ∧ x ∈ W) ∧ Y ∈ (univ : Set Plane)
    exact ⟨⟨le_rfl, hx⟩, mem_univ _⟩
  exact ⟨WithinJetClosure.tendsto_iteratedFDeriv
      ((slowDomain_uniqueDiff hW).prod uniqueDiffOn_univ)
      ((isOpen_Ioi.prod hW).prod isOpen_univ) hOS hv n he,
    WithinJetClosure.tendsto_iteratedFDeriv
      ((slowDomain_uniqueDiff hW).prod uniqueDiffOn_univ)
      ((isOpen_Ioi.prod hW).prod isOpen_univ) hOS hp n he⟩

end CommonTorus

end NavierStokes.ParticularOneSided
