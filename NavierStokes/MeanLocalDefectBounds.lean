import NavierStokes.MeanLocalCoefficient
import NavierStokes.MovingMomentBounds
import NavierStokes.RankStateBounds

/-!
# Defect gain with coefficient bounds on the correcting potential support

The base coefficient estimates below are imposed only on the topological
support of the actual azimuthal potential. This includes the intervals
between the rank solver's bump supports. Differentiating that potential
does not enlarge its support, so these estimates suffice for every base
coefficient product in the exact radial remainder.
-/

noncomputable section

namespace NavierStokes.MeanLocalDefectBounds

open Set Filter WeightedClasses MeanIncrementBounds MeanLocalCoefficient
open scoped ContDiff Topology

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Only the radial and axial base coefficients occur after subtracting
the exact leading angular term. Smoothness remains a local physical
assumption; no growth estimate outside the potential support is imposed. -/
structure LocalBaseBounds (s : StripData D) (A : ℕ → Set D) (b : Triple D) : Prop where
  radial : LocalCoefficientBounds s A 1 b.radial
  axial : LocalCoefficientBounds s A 0 b.axial
  angular_smooth : SmoothOn s.domain b.angular

theorem LocalBaseBounds.smooth {s : StripData D} {A : ℕ → Set D} {b : Triple D}
    (hb : LocalBaseBounds s A b) : SmoothTriple s.domain b :=
  ⟨hb.radial.smooth, hb.angular_smooth, hb.axial.smooth⟩

/-- Both stream components are supported in the potential support. No
support restriction on the separate angular increment is needed. -/
structure StreamSupport (s : StripData D) (A : ℕ → Set D) (h : Triple D) : Prop where
  radial : ∀ n, tsupport (h.radial n) ∩ s.domain ⊆ A n
  axial : ∀ n, tsupport (h.axial n) ∩ s.domain ⊆ A n

section Remainder

variable {s : StripData D} {A : ℕ → Set D} {o : Operators D} {κ H : ℝ}
    {b m h : Triple D} (ho : OperatorBounds s o κ) (hb : LocalBaseBounds s A b)
    (hs : StreamSupport s A h) (hm : CumulativeBounds s m)
    (hh : IncrementBounds s H h) (hH : 9 / 10 ≤ H)

include ho hb hs hm hh hH in
theorem deltaAxialRadial_mem : MeanClass s (H + 1) (deltaAxialRadial b m h) := by
  have h1 := (hb.radial.coefficient_mul hh.axial hs.axial).mono_exponent
    (show H + 1 ≤ 1 + H by linarith)
  have h2 : MeanClass s (H + 1) (h.radial * b.axial) := by
    apply class_congr ((hb.axial.coefficient_mul hh.radial hs.radial).mono_exponent
      (show H + 1 ≤ 0 + (H + 1) by simp))
    intro n x hx
    exact mul_comm _ _
  have h3 := (Class.product hm.radial hh.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ 19 / 10 + H by linarith)
  have h4 := (Class.product hh.radial hm.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + 9 / 10 by linarith)
  have h5 := (Class.product hh.radial hh.axial ho.weight_le_one).mono_exponent
    (show H + 1 ≤ (H + 1) + H by linarith)
  exact (((h1.add h2).add h3).add h4).add h5

include ho hb hs hm hh hH in
theorem deltaRadialRadial_mem : MeanClass s (H + 2) (deltaRadialRadial b m h) := by
  have h1 := Class.smul ((hb.radial.coefficient_mul hh.radial hs.radial).mono_exponent
    (show H + 2 ≤ 1 + (H + 1) by linarith)) 2
  have h2 := Class.smul ((Class.product hm.radial hh.radial ho.weight_le_one).mono_exponent
    (show H + 2 ≤ 19 / 10 + (H + 1) by linarith)) 2
  have h3 := (Class.product hh.radial hh.radial ho.weight_le_one).mono_exponent
    (show H + 2 ≤ (H + 1) + (H + 1) by linarith)
  exact (h1.add h2).add h3

include ho hb hs hm hh hH in
/-- The complete radial remainder gains the manuscript exponent using
base estimates solely where the stream potential can be nonzero. -/
theorem radialRemainder_mem :
    MeanClass s (H + 9 / 10 - 2 * κ) (radialRemainder o b m h) := by
  have h1 := (ho.time hh.radial).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ H + 1 by linarith [ho.kappa_nonneg])
  have h2 := (ho.radialDiv (deltaRadialRadial_mem ho hb hs hm hh hH) 1).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 2) - κ by linarith [ho.kappa_nonneg])
  have h3 := (ho.dz (deltaAxialRadial_mem ho hb hs hm hh hH)).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 1) + 1 by linarith [ho.kappa_nonneg])
  have h4 := (ho.inv_mul (MeanIncrementBounds.radialAngularRemainder_mem ho hm hh hH)).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ H + 9 / 10 by linarith [ho.kappa_nonneg])
  have h5 := (ho.viscosity hh.radial 1).mono_exponent
    (show H + 9 / 10 - 2 * κ ≤ (H + 1) + 1 - 2 * κ by linarith)
  exact ((Class.sub (Class.sub (Class.neg h1) h2) h3).add h4).add h5

include ho hb hs hm hh hH in
theorem gr_change_sub_leading_mem
    (W : Fin 3 → Fin 3 → MeanIncrementBounds.Field D) (hW : ∀ i j, SmoothOn s.domain (W i j)) :
    MeanClass s (H + 9 / 10 - 2 * κ)
      (gr o b (updated m h) W - gr o b m W - leadingRadial o b h) := by
  apply class_congr (radialRemainder_mem ho hb hs hm hh hH)
  intro n x hx
  have he := gr_change s.isOpen_domain o (ho.radialProfile.smooth 0)
    hb.smooth hm.smooth hh.smooth W hW n hx
  simp only [Pi.sub_apply, Pi.add_apply] at he ⊢
  linarith

end Remainder

section PotentialSupport

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem streamBeta_tsupport (w : E) (Ψ : ℝ × E → ℝ) :
    tsupport (PressureStream.streamBeta w Ψ) ⊆ tsupport Ψ := by
  apply closure_minimal _ (isClosed_tsupport Ψ)
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  exact hx (by simp [PressureStream.streamBeta, PressureStream.graphDz, hd])

theorem streamGamma_tsupport (k : ℝ → ℝ) (v : E) (Ψ : ℝ × E → ℝ) :
    tsupport (PressureStream.streamGamma k v Ψ) ⊆ tsupport Ψ := by
  apply closure_minimal _ (isClosed_tsupport Ψ)
  intro x hx
  by_contra hn
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [PressureStream.streamGamma, PressureStream.graphDr,
    PressureStream.divideRadius, hd, hz])

end PotentialSupport


open CorrectionState VariableGaugeMean LocalSignedRequest MovingMomentBounds
open DefectIncrementBounds

/-- The two actual stream increments have support in the actual rank
potential, including any nonzero primitive between the separated bumps. -/
theorem rankIncrement_streamSupport
    (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point) (s : StripData Point) :
    StreamSupport s (fun n => tsupport (rankPotential g r c u n))
      (rankIncrementState g r axial c u) := by
  constructor
  · intro n x hx
    exact streamBeta_tsupport _ _ hx.1
  · intro n x hx
    exact streamGamma_tsupport _ _ _ hx.1

section Remainders

open DefectIncrementBounds

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab in
/-- Actual equation-(32) remainders gain their full exponent under the
moving moment map. Every covariance and differentiated mean term remains
in the source before integration. -/
theorem moving_remainders_mem {A : ℕ → Set Point} {o : Operators Point} {base m h : Triple Point} {κ H : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier o)
    (hbs : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) m)
    (hhc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) h)
    (hms : SupportedTriple a b (qLength coord) U.carrier m)
    (hhs : SupportedTriple a b (qLength coord) U.carrier h)
    (W : Fin 3 → Fin 3 → CorrectionState.ScalarField Point) (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (W i j))
    (hWs : ∀ i j, Support a b (qLength coord) U.carrier (W i j))
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) o κ)
    (hb : LocalBaseBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) A base)
    (hs : StreamSupport (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) A h)
    (hm : MeanIncrementBounds.CumulativeBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) m)
    (hh : IncrementBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H h)
    (hH : 9 / 10 ≤ H) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n x => DefectIncrementBounds.remainders o base m h W n x i) := by
  obtain ⟨a₀, b₀, R₀, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed {f : CorrectionState.ScalarField Point} (hs : Support a b (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier m :=
    ⟨⟨hmc.radial, hfixed hms.radial⟩, ⟨hmc.angular, hfixed hms.angular⟩, ⟨hmc.axial, hfixed hms.axial⟩⟩
  have hhl : LocalRankDefect.LocalTriple a₀ b₀ U.carrier h :=
    ⟨⟨hhc.radial, hfixed hhs.radial⟩, ⟨hhc.angular, hfixed hhs.angular⟩, ⟨hhc.axial, hfixed hhs.axial⟩⟩
  have hwl (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (W i j) :=
    ⟨hWc i j, hfixed (hWs i j)⟩
  have hrc := gr_change_sub_leading_mem ho hb hs hm hh hH W
    (fun i j n => (hWc i j n).mono (fun x hx =>
      ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1))
  have hrl := LocalRankDefect.actualRadialError_localShell ha₀ U.isOpen hbs hml hhl hop W hwl
  have hl : ContinuousOn (qLength coord) U.carrier :=
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun x hx => U.time_pos x hx)).continuousOn
  have hrs : Support a b (qLength coord) U.carrier (actualRadialError o base m h W) :=
    ((gr_support U.isOpen hl o base (updated m h) W (hms.updated hhs) hWs).sub
      (gr_support U.isOpen hl o base m W hms hWs)).sub
      (((hhs.angular.mul_left base.angular).smul 2).mul_left o.invRadius)
  have hts : Support a b (qLength coord) U.carrier (thetaQuadratic m h) :=
    ((hms.axial.mul_right h.angular).add (hhs.axial.mul_right m.angular)).add
      (hhs.axial.mul_right h.angular)
  have hzs : Support a b (qLength coord) U.carrier (axialQuadratic m h) :=
    ((hms.axial.mul_right h.axial).smul 2).add (hhs.axial.mul_right h.axial)
  have hP := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hrl.smooth hrs hrc 0
  have hP2 := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hrl.smooth hrs hrc 2
  have hT := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (LocalRankDefect.thetaQuadratic_localShell hml hhl).smooth hts (thetaQuadratic_mem ho hm hh hH) 2
  have hZ := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (LocalRankDefect.axialQuadratic_localShell hml hhl).smooth hzs (axialQuadratic_mem ho hm hh hH) 1
  fin_cases i
  · exact hP
  · exact hT
  · exact Class.sub hZ (Class.smul hP2 (1 / 2))

end Remainders

section RankDefect

variable {coord cL cR : ℝ} (U : SlowRegion coord)
    (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)

include hell hg in
/-- The actual five-row rank stage gains the defect exponent on the
original moving strip. The row cancellation is derived from RankGeometry;
the pressure source and quadratic remainders are integrated literally. -/
theorem rankStage_defect_class {κ H : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, Support g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j))
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      c.operators κ)
    (hb : LocalBaseBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      (fun n => tsupport (rankPotential g r c u n)) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) u.mean)
    (hi : IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      H (rankIncrementState g r axial c u)) (hH : 9 / 10 ≤ H) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n x => debt c (rankStageState g r axial c u) n x i) := by
  obtain ⟨a₀, b₀, R₀, ha₀, hab₀, _, _, hleft, hright, _⟩ :=
    qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hl (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : a₀ ≤ r.length n x * r.inner := by
    have hh := hg.gauge_left n x hx
    rw [hell n] at hh
    exact (hleft x hx).trans hh
  have hr (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ b₀ := by
    have hh := hg.gauge_right n x hx
    rw [hell n] at hh
    exact hh.trans (hright x hx)
  have hfixed {f : CorrectionState.ScalarField Point}
      (hs : Support g.radial.inner g.radial.outer (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier u.mean :=
    ⟨⟨hmc.radial, hfixed hms.radial⟩, ⟨hmc.angular, hfixed hms.angular⟩,
      ⟨hmc.axial, hfixed hms.axial⟩⟩
  have hwl (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) :=
    ⟨hWc i j, hfixed (hWs i j)⟩
  have hir := hg.increment_localTriple ha₀ hab₀ U.isOpen hl hr axial
  have his : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u) := by
    have hcontain (n : ℕ) {f : Point → ℝ}
        (hs : SupportedGauge r.inner r.outer (r.length n) U.carrier f) :
        SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier f := by
      intro z hz hn
      obtain ⟨hzl, hzr⟩ := hs z hz hn
      have hgl := hg.gauge_left n z.2.1 hz
      have hgr := hg.gauge_right n z.2.1 hz
      rw [hell n] at hgl hgr
      exact ⟨hgl.trans hzl, hzr.trans hgr⟩
    exact ⟨fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).1,
      fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).2.1,
      fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).2.2⟩
  have hrem := moving_remainders_mem U ha g.radial.inner_lt_outer hcL hcR ε L hε hεone hL hop hbc hmc
    hir.smooth hms his u.covariance hWc hWs ho hb (rankIncrement_streamSupport g r axial c u _) hm hi hH i
  apply LinearWaveBounds.class_congr hrem
  intro n x hx
  exact congrArg (fun v : Fin 3 → ℝ => v i)
    (hg.debt_eq_remainders ha₀ hab₀ U.isOpen hl hr axial hop hbc hml hwl hV hG n hx).symm

include hell hg in
/-- The manuscript's moment remainder gain for its fixed shaped patch
amplitude. The input is the actual three target classes. The rank inverse
supplies the increment estimates, and coefficient growth is required only
on the topological support of its azimuthal potential. -/
theorem rankStage_gain_of_targets {κ H A B : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, Support g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i j))
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      c.operators κ)
    (hb : LocalBaseBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      (fun n => tsupport (rankPotential g r c u n)) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) u.mean)
    (hparam : RankStateBounds.NormalizedParameters coord A B r U.carrier)
    (hB : B ≠ 0) (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    (htarget : ∀ i : Fin 3,
      UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
        H (fun n x => debt c u n x i)) (hH : 9 / 10 ≤ H) :
    MeanClass (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ)
      (actualRadialError c.operators c.base u.mean (rankIncrementState g r axial c u) u.covariance) ∧
    ∀ i : Fin 3, UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n x => debt c (rankStageState g r axial c u) n x i) := by
  have hi := RankStateBounds.rankIncrementState_bounds_of_components U g r ha hcL hcR
    ε L hε hεone hL c u hg hparam hB hleft hright axial ho.epsilon htarget
  refine ⟨?_, fun i => rankStage_defect_class U g r ha hcL hcR ε L hε hεone hL hell
    axial c u hg hop hbc hmc hms hWc hWs hV hG ho hb hm hi hH i⟩
  exact gr_change_sub_leading_mem ho hb (rankIncrement_streamSupport g r axial c u _) hm hi hH
    u.covariance (fun i j n => (hWc i j n).mono (fun x hx =>
      ((movingStrip_domain U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1))

end RankDefect

end NavierStokes.MeanLocalDefectBounds
