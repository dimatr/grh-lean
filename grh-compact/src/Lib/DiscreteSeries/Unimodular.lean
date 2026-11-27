import Lib.DiscreteSeries.SubgroupIntegral
import Lib.DiscreteSeries.CircleMean

-- part: Lib.Adelic.QuotientMeasure.Packing
section
/-! General lemmas of real and complex analysis (textbook or folklore).

Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Quotient integral via weights: independence of the weight and Weil's unfolding
formula. -/

open Classical Filter MeasureTheory Metric Module ProbabilityTheory Real MeasureTheory.Measure

to_additive_name_hint Quot AddQuot

variable {H X W Y} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace W] [MeasurableSpace Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [BorelSpace W] {F : X → Y} {f : X → W}

/-- Let ν on H have a cutoff on X, σ carry ρ to ν, and (z, l) ↦ σ(l)·T(z) carry m × ρ to μ, with
m, ρ s-finite, T measurable. For measurable H-invariant F, F under `orbitMeasure` ν μ and F∘T
under m are identically distributed. -/
@[to_additive identDistrib_addOrbitMeasure_of_unfold] lemma identDistrib_orbitMeasure_of_unfold
  [SMul H X] [MeasurableSMul₂ H X] {ν μ Z L} [MeasurableSpace Z] [MeasurableSpace L] {ρ} [SFinite ρ]
  [c : HasCutoff ν X] {σ : L → H} (s : MeasurePreserving σ ρ ν) {T m} [@SFinite Z _ m] (h :
  MeasurePreserving (fun p ↦ σ p.2 • T p.1) (m.prod ρ) μ) (hF : Measurable F) (hT :
  Measurable T) (hi : ∀ (h : H) x, F (h • x) = F x) : IdentDistrib F (F ∘ T) (orbitMeasure ν μ) m :=
  (fun ⟨b, _⟩ _ ↦ ⟨by fun_prop, by fun_prop, ext_of_lintegral
  _ (by simp +contextual (disch := fun_prop) [lintegral_map, lintegral_withDensity_eq_lintegral_mul,
  *, ← h.lintegral_comp, lintegral_mul_const, lintegral_prod, Function.comp_def,
  s.lintegral_comp (b.fun_comp (measurable_smul_const _))])⟩) (epsilon_spec c.1) s.1

variable [Group H] [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν]
  {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] {β} [IsInvInvariant ν] {S : Subgroup H}

@[to_additive] instance : MeasurableSMul₂ S X := ⟨.smul (by fun_prop) measurable_snd⟩

/-- Let a group H act measurably on X, ν an s-finite measure on H, μ an s-finite H-invariant
measure on X, β : X → [0,∞] measurable. Then (x,h) ↦ hx pushes (βμ) × ν forward to μ with
density x ↦ ∫ β(h⁻¹x) dν(h). -/
@[to_additive] lemma measurePreserving_smul_prod {ν : MeasureTheory.Measure H} [@SFinite H _ ν]
    {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] {β : X → ENNReal} (m : Measurable β) :
    MeasurePreserving (fun p ↦ p.2 • p.1) ((μ.withDensity β).prod ν)
    (μ.withDensity fun x ↦ ∫⁻ h, β (h • x) ∂ν.inv) := ⟨by fun_prop,
  by ext; erw [map_apply, prod_apply_symm, withDensity_apply, lintegral_lintegral_swap,
       lintegral_map]; congr!
     rw [← (measurePreserving_smul ‹_› _).setLIntegral_comp_preimage, withDensity_apply]
     repeat measurability⟩

@[to_additive] lemma IsCutoff.measurePreserving :
    IsCutoff ν β → MeasurePreserving (fun p ↦ p.2 • p.1) ((μ.withDensity β).prod ν) μ
    | ⟨m, _⟩ => by convert measurePreserving_smul_prod m <;> simp_all

/-- Independence of the cutoff: for H acting measurably on X, ν inversion invariant on H, μ
H-invariant on X (both s-finite) and any cutoff β, an H-invariant measurable F has the same
distribution under βμ as under the quotient measure `orbitMeasure`. -/
lemma identDistrib_orbitMeasure (hβ : IsCutoff ν β) : Measurable F →
  (∀ (h : H) x, F (h • x) = F x) → IdentDistrib F F (orbitMeasure ν μ) (μ.withDensity β) :=
  (identDistrib_orbitMeasure_of_unfold (c := ⟨_, hβ⟩) (.id _) hβ.measurePreserving · measurable_id)

lemma IsCutoff.ae_lt_top : IsCutoff ν β → ∀ᵐ x ∂μ, β x < ⊤ | h@⟨_, _⟩ => by simp (disch :=
  measurability) [← h.measurePreserving.hasLaw.ae_iff, ae_prod_iff_ae_ae, MeasureTheory.ae_lt_top]

lemma IsCutoff.integral_orbitMeasure (h : IsCutoff ν β) (i : ∀ (h : H) y, f (h • y) = f y) (m :
  Measurable f := by fun_prop) : (orbitMeasure ν μ)[f] = ∫ y, (β y).toReal • f y ∂μ :=
  (identDistrib_orbitMeasure h m
  i).integral_eq.trans (integral_withDensity_eq_integral_toReal_smul h.1 h.ae_lt_top _)

variable {V} {I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : I → V} {m R A c : ℝ} (hm : 0 < m) [c : HasCutoff ν X]

/-- Unfolding: let H act measurably on X with a cutoff, ν s-finite and inversion invariant on H,
μ s-finite and H-invariant on X. Then (x, h) ↦ hx is measurable and carries βμ × ν to μ,
where βμ is `orbitMeasure` for the chosen cutoff β.

Known result: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity. -/
@[to_additive measurePreserving_addOrbitMeasure] lemma measurePreserving_orbitMeasure :
  MeasurePreserving (fun p ↦ p.2 • p.1)
  ((orbitMeasure ν μ).prod ν) μ := (epsilon_spec c.1).measurePreserving

/-- Let the action of H on X have a cutoff and let the invariant measure μ be positive on
nonempty open sets. An H-stable property that holds almost everywhere for the quotient
measure `orbitMeasure` holds on a dense subset of X. -/
lemma dense_of_ae_orbitMeasure [TopologicalSpace X] [BorelSpace X] [μ.IsOpenPosMeasure] {p : X → _}
    (i : ∀ (h : H) x, p x → p (h • x)) (e : ∀ᵐ x ∂orbitMeasure ν μ, p x) : Dense {x | p x} :=
  .of_closure
  (dense_of_ae ((measurePreserving_orbitMeasure.hasLaw.ae_iff measurableSet_closure.mem).1
  ((quasiMeasurePreserving_fst.ae e).mono (by grind [subset_closure]))))

/-- Unfolding: let H act measurably on X preserving the s-finite μ, with ν an s-finite
inversion-invariant measure on H admitting a cutoff. For measurable f : X → [0,∞],
integrating x ↦ ∫_H f(hx) dν over H\X gives ∫_X f dμ. -/
@[to_additive lintegral_addOrbitMeasure_lintegral] lemma lintegral_orbitMeasure_lintegral {f} :
    Measurable f → ∫⁻ x, ∫⁻ h, f (h • x) ∂ν ∂orbitMeasure ν μ = ∫⁻ x, f x ∂μ :=
    (.trans (lintegral_lintegral (by fun_prop)) <| measurePreserving_orbitMeasure.lintegral_comp ·)

/-- Let u ≥ 1 be measurable, ν{u ≤ R} ≤ (K R^e)^d · V for R ≥ 1, ed < A, V finite, K ≥ 0 and A ≤
c(A − ed). Then u^(−A) is integrable and ∫ u^(−A) dν ≤ K^d c V. -/
lemma integral_rpow_neg_le_of_layers {K} (A : ℝ) {e d : ℕ} {S} {_ : MeasurableSpace S} {ν :
  Measure S} {u : S → ℝ} {V} (h : ∀ s, 1 ≤ u s) (H : ∀ R ≥ 1, ν {s | u s ≤ R} ≤ .ofReal
  ((K * R ^ e) ^ d) * V) c (hV : V ≠ ⊤) (m : Measurable u := by fun_prop) (hK : 0 ≤ K := by bound)
  (hA : e * d < A := by norm_cast; lia) (hc : A ≤ c * (A - e * d) := by norm_cast; lia) :
  Integrable (u · ^ (-A)) ν ∧ ∫ s, u s ^ (-A) ∂ν ≤ K ^ d * c * V.toReal := by
  have : 0 ≤ c := by nlinarith
  suffices : lintegral .. ≤ .ofReal c * ∫⁻ _, .ofReal (1 ^ (A - e * d)) ∂(.ofReal K ^ d * V) •
    .dirac ()
  grw [Integrable, integral_eq_lintegral_of_nonneg_ae, hasFiniteIntegral_iff_ofReal, this]
  case' this => simp_rw [rpow_neg_eq_inv_rpow]
                repeat rw [lintegral_rpow_eq_lintegral_meas_le_mul]
                nth_grw 1 [hc, ENNReal.ofReal_mul, mul_assoc, setLIntegral_mono' _ fun t o ↦ ?_]
  all_goals simp [*, EventuallyLE, (h _).trans', m.aemeasurable, hA.trans_le', mul_nonneg, field,
    rpow_nonneg, (m.pow_const (-A)).aestronglyMeasurable] <;> try finiteness
  by_cases t ≤ 1 <;> simp_all [le_inv_comm₀ o.out, (h _).trans_lt', ← one_le_inv₀, mt (h _).trans]
  grw [H] <;> simp (disch := bound) [*, rpow_sub, rpow_mul, mul_pow, division_def]
  ac_nf

/-- Packing bound: in a finite-dimensional real normed space V, if the points f(i), i in S, have
pairwise distances at least m > 0 and norms at most R, with R ≥ 0, then S has at most (1 +
2R/m)^{dim V} elements. -/
lemma encard_le_of_separated (hm : 0 < m) (hR : 0 ≤ R) {S} (hf : Set.Pairwise S (m ≤ ‖f · - f ·‖))
    (hs : ∀ i ∈ S, ‖f i‖ ≤ R) : S.encard ≤ ENNReal.ofReal ((1 + 2 * R / m) ^ finrank ℝ V) := by
  borelize V
  grw [← ENNReal.mul_le_mul_iff_left, ← addHaar.addHaar_ball_mul_of_pos 0 _ (m / 2),
    ← Set.iUnion_subset fun i ↦ ball_subset (ε₁ := m / 2) _,
    ← tsum_meas_le_meas_iUnion_of_disjoint _ (by measurability) (hf.subtype.mono _)]
  any_goals simp [addHaar_ball_center, field]
  repeat grind [measure_ball_pos, measure_ball_ne_top, ball_disjoint_ball, dist_eq_norm]

/-- Let points f_i of a real normed space of dimension d have mutual distances at least m > 0,
with ‖f_i‖ ≤ R u_i, u_i ≥ 1, R ≥ 0. If A > d and A ≤ c(A − d), then ∑ u_i^(−A) converges and
is ≤ (1 + 2R/m)^d c. -/
lemma tsum_le_of_separated {c : ℝ} (hm : 0 < m) (hR : 0 ≤ R) (hf : Pairwise (m ≤ ‖f · - f ·‖)) {u :
    I → _} (h1 : ∀ i, 1 ≤ u i) (hu : ∀ i, ‖f i‖ ≤ R * u i) (hA : finrank ℝ V < A) (hc : A ≤ c * (A -
    finrank ℝ V)) : Summable (u · ^ (-A)) ∧ ∑' i, u i ^ (-A) ≤ (1 + 2 * R / m) ^ finrank ℝ V * c :=
    .elim (by simp [count, integral_sum_measure ‹_›, integrable_count_iff.1 · |>.of_norm]; tauto)
    (integral_rpow_neg_le_of_layers A (e := 1) (ν := @count I ⊤) (V := 1) h1 (by
    simp_intro .. [count_apply]; grw [encard_le_of_separated hm _ (by tauto) (by grw [hu]; bound)]
    gcongr; grind; bound) c nofun)

include hm in
/-- Let points f_i of a real normed space of finite dimension d have norms and mutual distances
at least m > 0. For an integer n ≥ d + 2, ∑ ‖f_i‖^(−n) converges and is at most (5/m)^n. -/
lemma tsum_inv_pow_le_of_separated (hf : Pairwise (m ≤ ‖f · - f ·‖)) (h0 : ∀ i, m ≤ ‖f i‖) {n}
    (hn : finrank ℝ V + 2 ≤ n) : Summable (‖f ·‖⁻¹ ^ n) ∧ ∑' i, ‖f i‖⁻¹ ^ n ≤ (5 / m) ^ n := by
  have := tsum_le_of_separated hm hm.le hf ((one_le_inv_mul₀ hm).2 <| h0 ·) (by simp [field])
    (c := 1 + n * 2⁻¹) (A := n) (mod_cast by lia) (by rify at *; nlinarith)
  simp_all [mul_pow, tsum_mul_right, summable_mul_right_iff, ne_of_gt]
  grw [div_pow, le_div_iff₀, this.2, one_add_mul_le_pow, le_of_add_le_left hn, ← mul_pow] <;> bound
end

-- part: Lib.Adelic.QuotientMeasure.Unimodular
section
/-! Known result: invariant integration on a quotient (Weil's formula), unfolding and unimodularity.
For second countable groups, the quotient integral is integration against a measurable weight of
total mass one on each orbit, so no orbit space or section is needed to define it. Two vanishing
lemmas avoid unimodularity. Source: O. Kallenberg, Invariant measures and disintegrations with
applications to Palm and related kernels, Probab. Theory Related Fields 139 (2007) 285-310, Lemma
2.1 and Theorem 2.4 (as cited in D. Gentner, G. Last, Math. Z. 267 (2011), §2); for the classical
form, N. Bourbaki, Intégration VII, 1963.

Known result: Transference theorem comparing the covering radius of a lattice with the first minimum
of its dual. It is proved here with constant n squared in place of n/2, for any subgroup of a
Euclidean space whose dual has no short vector, by projecting along a short vector. It is applied to
hermitian lattices to give short bases. Source: Lagarias-Lenstra-Schnorr, Korkin-Zolotarev bases and
successive minima of a lattice and its reciprocal lattice, Combinatorica 10 (1990), 333–348 (sharp
form in Banaszczyk, Math. Ann. 296 (1993)).

This file: Proper actions have cutoff weights; discrete subgroups; unfolding a sum over a lattice.
Covering radius of a subgroup at most n² over the first minimum of its dual. Quotient measure under
equivariant measure-preserving maps and right translation. Groups with a lattice are unimodular;
cocompact discrete subgroups have finite covolume. -/

open Module Classical ENNReal Matrix MeasureTheory NeZero ProbabilityTheory Set Submodule
  LinearMap.BilinForm MeasureTheory.Measure

variable {I H X G} [MeasurableSpace I] [MeasurableSpace H] [Countable I] [Group G]
  [MeasurableSingletonClass I] [MeasurableSingletonClass H] [MeasurableSpace X] [TopologicalSpace G]

lemma measurePreserving_count (e : I ≃ H) : MeasurePreserving e count count :=
    ⟨.of_discrete, .trans (map_sum .of_discrete) (by simp [count, ← Function.comp_def])⟩

variable [Group H] [MeasurableMul H] [TopologicalSpace H] (Γ N : Subgroup G) [DiscreteTopology Γ]

lemma integral_count_eq_tsum (f : I → ℂ) : ∫ x, f x ∂count = ∑' x, f x := by
    simpa using! integral_sum_dirac (c := 1) nofun

lemma tsum_toReal_smul_of_tsum_eq_one {I} {f : I → ℝ≥0∞} (h : ∑' x, f x = 1) (z : ℂ) : ∑' x,
  (f x).toReal • z = z := by
  simp_all [tsum_mul_right, ← Complex.ofReal_tsum, ← tsum_toReal_eq, ENNReal.ne_top_of_tsum_ne_top]

/-- Proper actions have cutoffs. -/
@[to_additive hasAddCutoff_of_proper] instance hasCutoff_of_proper [MulAction H X]
    [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν] [IsMulRightInvariant ν] [TopologicalSpace X]
    [c : SigmaCompactSpace X] [T2Space X] [OpensMeasurableSpace X] [ProperSMul H X]
    [IsFiniteMeasureOnCompacts ν] [NeZero ν] : HasCutoff ν X := have ⟨K, hK, _⟩ := c
  have p x : ∃ n, 0 < ν ((· • x) ⁻¹' K n) := by
    by_contra; simp_all [← preimage_iUnion, ← measure_iUnion_null_iff]
  have m n := measurable_measure_prodMk_right (measurable_smul (hK n).measurableSet)
  ⟨_, .find (fun n ↦ (m n).inv.indicator (hK n).measurableSet) (m · measurableSet_Ioi) p, by
  simpa [indicator, preimage, fun (x : X) n ↦ by simpa [mul_smul] using (measure_preimage_mul_right
    ν · {h | h • x ∈ K n})] using fun x ↦ (lintegral_indicator_const (measurable_smul_const x (hK
    _).measurableSet) _).trans (ENNReal.inv_mul_cancel (Nat.find_spec (p _)).ne' (by simpa using!
    (ProperSMul.isCompact_setOfPred_inter_nonempty isCompact_singleton (hK _)).measure_ne_top))⟩

@[to_additive] instance [DiscreteTopology H] : IsHaarMeasure (@count H _) := by
  refine' {..} <;> aesop (add simp isCompact_iff_finite)

/-- For a subgroup N of G, the bijection (G/N) × N → G sending (q, u) to u times the inverse of
the chosen representative of the coset q. -/
noncomputable abbrev cosetProdEquiv : (G ⧸ N) × N ≃ G := by use fun (q, u) ↦ u * q.out⁻¹,
          fun γ ↦ ⟨↑γ⁻¹, _, QuotientGroup.eq.1 ⟦γ⁻¹⟧.out_eq.symm⟩ <;> aesop_cat

instance : DiscreteTopology (Γ.subgroupOf N) := .preimage_of_continuous_injective Γ.carrier
    (by fun_prop) (by simp)

instance : DiscreteTopology ↥(Γ ⊓ N) := .of_subset ‹_› (by simp)

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {S X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
  [LocallyCompactSpace X] [SetLike S X] {N : S} {μ : Measure G} [IsHaarMeasure μ] {E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Λ : Submodule ℤ E) [Module.Finite ℝ E] {ρ : ℝ}

@[to_additive] instance : Countable Γ := countable_of_Lindelof_of_discrete

instance instSecondCountableTopologySubtypeMem_new
    : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _

instance locallyCompactSpace_of_isClosed [hN : @IsClosed X _ N] :
    LocallyCompactSpace N := hN.locallyCompactSpace

@[to_additive addCutoff] instance hasCutoff_count : HasCutoff (@count Γ _) G := inferInstance

lemma quotMeasure_bot : Subgroup.qms ⊥ μ = μ := by
    simpa using (identDistrib_orbitMeasure ⟨measurable_one, by simp⟩ measurable_id (by simp)).3

/-- Unfolding: for a discrete subgroup Γ of a second countable locally compact group G with left
Haar measure μ and f integrable, g ↦ ∑_{γ∈Γ} f(γg) is integrable on Γ\G, with integral ∫_G f
dμ.

Known result: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity. -/
lemma integral_quotMeasure_tsum {f : G → ℂ} (h : Integrable f μ) :
  Integrable (fun g ↦ ∑' γ : Γ, f (γ * g))
  (Γ.qms μ) ∧ ∫ g, ∑' γ : Γ, f (γ * g) ∂Γ.qms μ = ∫ g, f g ∂μ := by simpa [← integral_count_eq_tsum]
  using! ((measurePreserving_orbitMeasure.fubini h).imp_left (·.integral_prod_left))

/-- Minkowski's bound. If the nonzero vectors of a lattice Λ with basis b in a Euclidean space
of dimension m ≥ 1 have length at least ρ > 0, then its covolume |det b|, in orthonormal
coordinates, is at least (ρ/√m)^m. -/
lemma minkowski_pow_le_abs_det [NormedAddCommGroup S] [InnerProductSpace ℝ S] [Module.Finite ℝ S]
  {ρ : ℝ} (hρ : 0 < ρ) {m} (hm : 0 < m) {o : OrthonormalBasis (Fin m) ℝ S} {b : Basis _ ℝ S}
  (h : ∀ y ∈ span ℤ (.range b), y ≠ 0 → ρ ≤ ‖y‖) : (ρ / √m) ^ m ≤ |det (of (o.repr <| b ·))| := by
  have := @countable_of_Lindelof_of_discrete
  simpa [*, mul_pow, mul_comm, ENNReal.mul_le_mul_iff_right] using!
    (exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (ZSpan.isAddFundamentalDomain'
    (b.map o.toBasis.equivFun) volume) (by simp) (convex_ball 0 (ρ / √m))).mt (by
    simp [← ZSpan.map]; intros
    grw [h, ← o.1.norm_map, PiLp.norm_eq_of_L2, norm_le_pi_norm] <;> simp_all [field])

/-- Weak transference. Let Λ be a subgroup of a Euclidean space of dimension m ≥ 1 whose dual
has no nonzero vector shorter than ρ > 0. Then Λ has a nonzero vector shorter than 2m / ρ. -/
lemma weak_transference (hρ : 0 < ρ) (h : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 → ρ ≤ ‖y‖)
    (hm : 0 < finrank ℝ E) : ∃ b ∈ Λ, b ≠ 0 ∧ ‖b‖ < 2 * finrank ℝ E / ρ := by
  by_contra! H
  have : DiscreteTopology Λ := .of_forall_le_norm (by bound) (H _ ·.2 ∘ by simp)
  have : IsZLattice ℝ Λ := ⟨orthogonal_eq_bot_iff.1 (subsingleton_iff_eq_bot.1
    (@PreconnectedSpace.trivial_of_discrete _ _ _ (.of_forall_le_norm hρ fun u ↦
    h u (by simp [real_inner_comm, u.2 · <| subset_span ·]) ∘ by simp)))⟩
  have e := (ZLattice.rank ℝ Λ ▸ finBasis ..).ofZLatticeBasis_span ℝ
  apply (mul_le_mul (minkowski_pow_le_abs_det hρ hm (by rwa [← e,
    dualSubmodule_span_of_basis _ (by simp_all [nondegenerate_iff', isSymm_inner])] at h))
    (minkowski_pow_le_abs_det _ hm (e.symm ▸ H)) ..).not_gt
  rw [← det_transpose, ← abs_mul, ← det_mul, mul_eq_one_symm]
  simp [field, one_lt_pow₀, hm.ne', ← mul_pow]
  exact Matrix.ext fun _ _ ↦ ((stdOrthonormalBasis ..).1.inner_map_map ..).trans
    (apply_dualBasis_left (B := innerₗ E) ..)
  repeat bound

/-- Weak transference for the covering radius. Let Λ be a subgroup of a Euclidean space of
dimension m whose dual has no nonzero vector shorter than ρ > 0. Then every vector u is
within m² / ρ of Λ.

Known result: Transference theorem: covering radius of a lattice against the first minimum of its
dual. -/
lemma weak_transference_covering_radius (hρ : 0 < ρ) (h : ∀ y ∈ dualSubmodule (innerₗ E) Λ, y ≠ 0 →
  ρ ≤ ‖y‖) u : ∃ x ∈ Λ, ‖u - x‖ ≤ finrank ℝ E ^ 2 / ρ := by
  induction' c : finrank ℝ E with n ih generalizing E
  simp_all [finrank_zero_iff_forall_zero]
  choose b _ o e using weak_transference Λ hρ h (by lia)
  choose x _ g using by simpa [starProjection_singleton, sub_sub_sub_comm u, ← sub_smul]
    using (ih (Λ.map (.restrictScalars ℤ (ℝ ∙ b)ᗮ.orthogonalProjectionOnto.1)) (fun y o ↦ h y
    (fun z a ↦ by simpa using o _ ⟨z, a, rfl⟩) ∘ by simp)
    (orthogonalProjectionOnto _ u) (finrank_orthogonal_span_singleton (_i := ⟨c⟩) o))
  exact ⟨x + (round _ : ℝ) • b, .symm ⟨by grw [← sub_sub, norm_sub_le_norm_sub_add_norm_sub,
   g, ← sub_smul, norm_smul, (abs_sub_round _ : ‖_‖ ≤ _), e, c]; field; grind, mod_cast by bound⟩⟩

variable {Γ : Subgroup G} [DiscreteTopology Γ] {H X : Type*} {H' Y Z} [MeasurableSpace H]
  [MeasurableSpace X] [MeasurableSpace H'] [MeasurableSpace Y] [MeasurableSpace Z] [Group H]

/-- Let σ : (H,ν) → (H',ν'), T : (X,μ) → (Y,μ') preserve measure, T(hx) = σ(h)T(x); ν, μ
s-finite, ν inversion invariant, μ H-invariant, ν, ν' with cutoffs. For measurable
H'-invariant F, F∘T and F are identically distributed for the quotient measures. -/
@[to_additive identDistrib_addOrbitMeasure_comp] lemma identDistrib_orbitMeasure_comp [MulAction H
  X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν : Measure H} [@SFinite H _ ν] [ν.IsInvInvariant]
  {μ : MeasureTheory.Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] [HasCutoff ν X]
  [SMul H' Y] [MeasurableSMul₂ H' Y] {ν' μ'} [HasCutoff ν' Y] {σ} (hσ : MeasurePreserving σ ν ν')
  {T} (hT : MeasurePreserving T μ μ') (h : ∀ h x, T (h • x) = (σ h : H') • T x) {F : Y → Z}
  (hi : ∀ (h : H') y, F (h • y) = F y) (hF : Measurable F := by fun_prop) : IdentDistrib (F <|
  T ·) F (orbitMeasure ν μ) (orbitMeasure ν' μ') := (identDistrib_orbitMeasure_of_unfold hσ
  (by simpa [← h] using! hT.comp measurePreserving_orbitMeasure) hF hT.1 hi).symm

variable [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X] {ν} [@SFinite H _ ν]
  [ν.IsInvInvariant] {μ : MeasureTheory.Measure X} [SFinite μ] [SMulInvariantMeasure H X μ]
  [HasCutoff ν X] in
/-- Let H act on a group X, commuting with right multiplication and admitting a cutoff, with ν
inversion invariant and μ H-invariant and right invariant. For measurable H-invariant F, the
functions x ↦ F(xg) and F have the same distribution under `orbitMeasure` ν μ. -/
lemma identDistrib_orbitMeasure_mul_right [Group X] [MeasurableMul₂ X] [IsScalarTower H X X]
    [μ.IsMulRightInvariant] g {F} (hi : ∀ (h : H) y, F (h • y) = (F y : Z)) (hF : Measurable F :=
    by fun_prop) : IdentDistrib (F <| · * g) F (orbitMeasure ν μ) (orbitMeasure ν μ) :=
  identDistrib_orbitMeasure_comp (.id _) (measurePreserving_mul_right ..) (by aesop) hi

@[to_additive ne_addQuot] instance : NeZero (Γ.qms μ) :=
    ⟨(by simpa [·, ne'] using measurePreserving_orbitMeasure (ν := @count Γ _) (μ := μ).2)⟩

/-- A group with a lattice is unimodular: if Γ is discrete in the locally compact second
countable Hausdorff group G and Γ\G has finite volume for the left Haar measure μ, then μ is
right invariant. -/
lemma isMulRightInvariant_of_finite_covolume (_ : IsFiniteMeasure (Γ.qms μ)) :
    IsMulRightInvariant μ := ⟨(have := map_right_mul_eq_modularCharacterFun_smul μ ·
  have := (identDistrib_orbitMeasure_comp (.id (@count Γ _)) ⟨by fun_prop,
    this⟩ (by simp [mul_assoc]) (by simp) measurable_one).symm.lintegral_eq
  by simp_all [← coe_nnreal_smul, ne, ENNReal.mul_eq_right, -withDensity_apply])⟩

instance [CompactSpace G] : IsMulRightInvariant μ :=
  isMulRightInvariant_of_finite_covolume (quotMeasure_bot.substr inferInstance)

instance [IsMulRightInvariant μ] : IsInvInvariant μ := ⟨((haarMeasure_unique ..).congr
    (haarMeasure_unique _ (ofNonempty ⊔ .map _ continuous_inv (isOpenMap_inv G) ofNonempty))).2
    congr($(by simp [union_comm]) • _)⟩

variable (μ)

/-- A cocompact discrete subgroup has finite covolume: if Γ is discrete in a second countable
locally compact group G and a compact set meets every orbit Γg, the quotient of Haar measure
by Γ is finite. -/
@[to_additive isFiniteMeasure_addOrbitMeasure] lemma isFiniteMeasure_quotMeasure_of_cocompact :
  Γ.Cocpt → IsFiniteMeasure (Γ.qms μ) | ⟨_, c, h⟩ => ⟨by
  grw [← (measurePreserving_orbitMeasure (ν := @count Γ _) (μ := μ).measure_preimage_le _).trans_lt
    c.measure_lt_top, prod_apply_symm (c.measurableSet.preimage (by fun_prop)), lintegral_count,
    ← measure_iUnion_le, iUnion_eq_univ_iff.2 (by simpa)]⟩

/-- On a second countable locally compact group with a Haar measure μ that is also right
invariant, every s-finite right invariant measure ν is dμ for some d in [0, ∞]. -/
lemma exists_eq_smul_haar [μ.IsMulRightInvariant] {ν} [SFinite ν] (_ : ν.IsMulRightInvariant) :
  ∃ d : ENNReal, ν = d • μ := ⟨_, .symm (Measure.ext fun _ h ↦ by
    simpa [lintegral_mul_right_eq_self, h.inv, mul_comm (μ _)] using
    lintegral_orbitMeasure_lintegral (ν := μ) (μ := ν.inv) (measurable_one.indicator h.inv))⟩
end
