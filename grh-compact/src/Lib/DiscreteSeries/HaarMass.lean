import Lib.DiscreteSeries.Unimodular
import Lib.DiscreteSeries.RepresentationDefs
import Lib.DiscreteSeries.CompactDualMeasure

-- part: Lib.Adelic.QuotientMeasure.IwasawaIntegration
section
/-! Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Iwasawa integration formula; quotient integral of N-invariant functions in coordinates n
m k. -/

open MeasureTheory Measure ENNReal NeZero ProbabilityTheory Function
variable {G M} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] (w)
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M] [PolishSpace M]
  [IsTopologicalGroup M] [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] (μ : Measure G)
  [IsHaarMeasure μ] [IsMulRightInvariant μ] (ν : Measure M) [IsHaarMeasure ν] {N K Γ : Subgroup G}
  [IsMulRightInvariant ν] [CompactSpace K] (κ : Measure K) [IsHaarMeasure κ] {lam : Measure N}
  [IsHaarMeasure lam] (i : M →* G) (hN : @IsClosed G _ N) (hw : Continuous w) (h₀ : ∀ m, 0 < w m)
  (hi : Continuous i) (H : ∀ g, ∃ᵉ (n : N) (m) (k : K), g = n * i m * k)
  (L : ∀ m f, Measurable f → ∫⁻ n, f (i m * n * (i m)⁻¹) ∂lam = .ofReal (w m) * ∫⁻ n, f n ∂lam)
include hN hw h₀ hi H L

omit hw in
/-- Iwasawa integration formula. Let G = N·i(M)·K with G, M, N unimodular, N closed, K compact,
conjugation by i(m) scaling integrals over N by w(m) > 0. Then ∫∫∫ f(i(m)nk) dn dm dk = d∫f
for some d in [0, ∞] and all measurable f ≥ 0. -/
lemma lintegral_iwasawa [IsMulRightInvariant lam] : ∃ d, ∀ f, Measurable f →
    ∫⁻ k, ∫⁻ m, ∫⁻ n, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g, f g ∂μ := by
  have ⟨_, β, _, b⟩ : SFinite ν ∧ HasCutoff μ G := ⟨inferInstance, inferInstance⟩
  choose n m k t using H
  let J (f : G → _) y := ∫⁻ h, f (i h.2.1 * h.2.2 * y * h.1⁻¹) ∂κ.prod (ν.prod lam)
  have e y f (_ : Measurable f) : .ofReal (w (m y)) * J f y = J f 1 := by
    nth_rw 2 [t y]; unfold J; rw [← lintegral_mul_right_eq_self _ (k y, (m y, n y)⁻¹)]
    simp (disch := fun_prop) [lintegral_prod, ← mul_assoc, ← lintegral_const_mul' _ _ ofReal_ne_top,
      ↓← fun a b c ↦ L (m y) (f <| a * · * b * c)]
  have ⟨g, _, r⟩ : ∃ g, Measurable g ∧ ∀ y f, Measurable f → g y * J f y = β y * J f 1 := by_contra
    fun h ↦ h ⟨β, ‹_›, fun y f u ↦ congrArg _ (by_contra fun n ↦ h ⟨β * (J f 1 / J f ·), by
    fun_prop, fun x φ v ↦ by rw [Pi.mul_apply, ← e x f u, ENNReal.mul_div_cancel_right, mul_assoc,
      e x φ v] <;> exact n ∘ (by simpa [← e x f u, ·, (h₀ _).not_ge, mul_eq_top] using e y f u)⟩)⟩
  use ∫⁻ h, g ((i h.2.1 * h.2.2)⁻¹ * h.1) ∂κ.prod (ν.prod lam), fun f u ↦ ?_
  rw [← lintegral_inv_eq_self]
  trans ∫⁻ y, g y * J f y ∂μ
  simp (disch := fun_prop) [↓r, lintegral_mul_const, J, lintegral_prod, by simpa using b 1]
  simp (disch := fun_prop) [J, ← lintegral_const_mul]
  rw [lintegral_lintegral_swap, ← funext fun h ↦ (lintegral_mul_right_eq_self _
    h.1).trans (lintegral_mul_left_eq_self _ (i h.2.1 * h.2.2)⁻¹), lintegral_lintegral_swap]
  congr with x; any_goals fun_prop
  rw [t x, eq_comm, ← lintegral_mul_left_eq_self _ (k x, (m x)⁻¹, 1)]
  simp (disch := fun_prop) [mul_assoc, lintegral_prod, lintegral_mul_const, fun a b ↦ by
    simpa [mul_assoc] using L a (g <| (i a)⁻¹ * ·⁻¹ * b), ← fun a b ↦
    lintegral_mul_left_eq_self (μ := lam) (fun y ↦ g (a * (y.1⁻¹ * (n x * b)))) (n x)]

/-- In Iwasawa coordinates G = N i(M) K, let Γ be discrete, contain all i(δ_d), lie in ⋃N·i(δ_d)⁻¹,
with Γ∩N cocompact in N. For F invariant under N, Γ: ∫F over the quotient is c∫w(m)F(i(m)k), if
convergent, m over a measure unfolding ν along δ; c ≠ 0. -/
lemma integral_orbitMeasure_iwasawa (j : ∀ a, i a ∈ N → a = 1) {D} [Countable D] {δ : D → M} (hd :
  Injective δ) α [SFinite α] (hα : ∀ f, Measurable f → ∫⁻ m, f m ∂ν = ∫⁻ m, ∑' d, f (δ d * m) ∂α)
  (hΔ : ∀ d, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d, g * i (δ d) ∈ N) [DiscreteTopology Γ]
  (hv : (Γ.subgroupOf N).Cocpt) : ∃ c ≠ (0 : ℝ), ∀ F : G → ℂ, Measurable F → N.FixesLeft F →
  Γ.FixesLeft F → let Θ (p : M × K) := w p.1 * F (i p.1 * p.2)
  Integrable Θ (α.prod κ) → Integrable F (Γ.qms μ) ∧ (Γ.qms μ)[F] = c * integral (α.prod κ) Θ := by
  set S := Γ.subgroupOf N
  obtain ⟨v, m⟩ := isFiniteMeasure_quotMeasure_of_cocompact lam hv,
    hw.fst' (Y := K).measurable.ennreal_ofReal
  have ⟨c, I⟩ := have :=
      isMulRightInvariant_of_finite_covolume v; lintegral_iwasawa w μ ν κ i hN h₀ hi H L
  use update id 0 1 (c⁻¹ * S.qms lam ⊤).toReal, by grind, fun F hF F1 _ _ ↦
    have h := (identDistrib_orbitMeasure_of_unfold (μ := c • μ) (.id (@count Γ _)) ⟨by fun_prop,
      ext_of_lintegral _ fun f _ ↦ ?_⟩ ?_ ?_ (by bound)).trans (.trans (.of_ae_eq ?_ (.of_forall
      (F1 _ ·.2.2 _))) (.comp (u := fun p ↦ F (i p.1 * p.2)) (HasLaw.identDistrib ⟨?_, map_fst_prod⟩
      .id) ?_)); fun a e t ↦ by by_cases c = ∞ <;> simp_all [Integrable, -withDensity_apply,
      HasFiniteIntegral, lt_top_iff_ne_top, mul_eq_top, le_of_lt, mul_assoc, ne, toReal_eq_zero_iff,
      hF.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul, left_ne_zero_of_mul (mt
      (I 1 measurable_one).trans (by simp [ne]))] (h.integrable_iff.2 (.smul_measure
    ((integrable_withDensity_iff_integrable_smul' m (by simp)).2 (by simpa [*, le_of_lt])) v.1.ne))
    h.symm.integral_eq (enorm_integral_le_lintegral_enorm (μ := Γ.qms μ) F)
  simp (disch := fun_prop) [lintegral_prod, lintegral_map, ← I]
  rw [lintegral_withDensity_eq_lintegral_mul, lintegral_prod_symm, funext fun _ ↦ hα ..]
  congr! with k m; any_goals fun_prop
  simp (disch := fun_prop) [fun a ↦ by simpa [mul_assoc] using L m (f <| a * · * i m * k),
    Subgroup.smul_def, mul_assoc,
    ← (Equiv.ofBijective (fun p : D × S ↦ (⟨_, hΔ p.1⟩ * ⟨_, p.2.2⟩ : Γ)) ⟨fun (_, _) (_, _) h ↦ by
    simpa [hd (inv_mul_eq_one.1 (j _ (by simpa [QuotientGroup.eq] using congr(($h : G ⧸ N)))))]
      using h, fun g ↦ (hΓ _ g⁻¹.2).elim fun d h ↦ ⟨(d, ⟨⟨_, h⟩, mul_mem g⁻¹.2 (hΔ d)⟩⁻¹),
    by simp⟩⟩).tsum_eq, lintegral_tsum, ← lintegral_orbitMeasure_lintegral (ν := @count S _)]
end

-- part: Lib.Adelic.QuotientMeasure.CocompactIntegrable
section
/-! Part of: Invariant integration on a quotient (Weil's formula), unfolding, unimodularity (known
result; see Lib.Adelic.QuotientMeasure.Unimodular).

This file: Unfolding quotient integrals in stages; pushing quotient measures along surjections.
Unfolding a sum over an orbit or block to the stabiliser quotient. Quotient integral vanishes when
averaging eigenvalue differs from modulus, or nontrivial phase. Continuous invariant functions for
cocompact subgroups are integrable; cocompactness of products. -/

open Classical ENNReal Function MeasureTheory MulAction ProbabilityTheory Topology
  MeasureTheory.Measure

variable {G H V} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] {Γ : Subgroup G} [DiscreteTopology Γ] (Λ : Subgroup H)
  [DiscreteTopology Λ] (μ : Measure G) [IsHaarMeasure μ] (ν : Measure H) [IsHaarMeasure ν]

section

attribute [local simp ←] map_mul mul_assoc

/-- Let π : H → G be a continuous surjective homomorphism of locally compact groups with
bi-invariant Haar measures, Λ ⊂ H, Γ ⊂ G discrete, π(Λ) ⊂ Γ. Some real c gives ∫_{Λ\H} F∘π =
c ∫_{Γ\G} F for all measurable left Γ-invariant F. -/
lemma exists_integral_quotMeasure_push [μ.IsMulRightInvariant] [ν.IsMulRightInvariant] {π : H →* G}
    (hπ : Continuous π) (hs : Surjective π) (hΛ : Λ ≤ Γ.comap π) : ∃ c :
    ℝ, ∀ F, Measurable F → Γ.FixesLeft F → ∫ r, F (π r) ∂Λ.qms ν = (c • (Γ.qms μ)[F] : V) :=
    (exists_eq_smul_haar μ ⟨hs.forall.2 fun a ↦ ext_of_lintegral _ fun f _ ↦ by
    simp (disch := fun_prop) [lintegral_map, lintegral_prod, subgroup_smul_def]
    exact .trans (by grind) (identDistrib_orbitMeasure_mul_right a fun ⟨δ, h⟩ r ↦ .trans
      (by simp [map_mul]) (Equiv.tsum_eq (.mulRight ⟨_, hΛ h⟩) _)).lintegral_eq⟩).imp'
  (·.toReal) fun _ e F hF _ ↦ (identDistrib_orbitMeasure_of_unfold (.id (@count Γ _)) ⟨by fun_prop,
  e⟩ hF (by fun_prop) (by simpa)).integral_eq.symm.trans (by simp)

/-- Unfolding in stages. Let i : H → G be injective, Λ and Γ = i(Λ) discrete, ν Haar on H, m
s-finite, (z,h) ↦ i(h)T(z) carry m × ν to μ. For measurable Γ-invariant F integrable on Γ\G,
z ↦ ∫_{Λ\H} F(i(h)T(z)) is m-integrable with integral ∫_{Γ\G} F. -/
lemma integral_quotMeasure_stages {Z} [MeasurableSpace Z] {m μ} [@SFinite Z _ m] (T : Z → G) {i :
  H →* G} (hi : Injective i) (h : MeasurePreserving (fun p ↦ i p.2 * T p.1) (m.prod ν) μ) (hΓ :
  Λ.map i = Γ) {F : G → V} (hF : Measurable F) (hi' : Γ.FixesLeft F) (hI : Integrable F (Γ.qms μ)) :
  let f x := ∫ h, F (i h * T x) ∂Λ.qms ν
  Integrable f m ∧ (Γ.qms μ)[F] = integral m f := (fun I ↦ have J := I.integrable_snd hI
  ⟨J.integral_prod_left, I.integral_eq ▸ integral_prod _ J⟩) (identDistrib_orbitMeasure_of_unfold
  (measurePreserving_count ((Λ.equivMapOfInjective _ hi).trans (.subgroupCongr hΓ)).1)
  (by simpa [subgroup_smul_def] using! h.comp (.comp (.prod (.id _) measurePreserving_orbitMeasure)
  (measurePreserving_prodAssoc ..))) hF h.1 (by simpa))

/-- Unfolding in stages: i : L × H → G closed, L, H unimodular, Λ ⊂ H discrete, Γ = i(Λ), Re ρ ≥ 0,
nonzero near a point. Some R ≠ 0 gives ∫_{Γ\G} F = Rc for continuous integrable F whenever each g
has k in L × H with ∫_L ∫_{Λ\H} F(lakg) = ρ(g)c. -/
lemma exists_integral_stages_eq_mul {L} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [PolishSpace L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] κ [IsHaarMeasure κ]
  [κ.IsMulRightInvariant] [ν.IsMulRightInvariant] (i : L × H →* G) (hi : IsClosedEmbedding i) {g₀}
  (ρ : _ → ℂ) (h₀ : ∀ g, 0 ≤ (ρ g).re) (h₁ : ∀ᶠ g in 𝓝 g₀, (ρ g).re ≠ 0) : let Γ := Λ.map (i.comp
  (.inr ..)); ∃ R ≠ 0, ∀ F, Continuous F → Γ.FixesLeft F → Integrable F (Γ.qms μ) → ∀ c, (∀ g,
  ∃ k, ∫ l, ∫ a, F (i (l, a) * (i k * g)) ∂Λ.qms ν ∂κ = ρ g * c) → (Γ.qms μ)[F] = R * c := by
  intro Γ
  let := compHom G i
  obtain ⟨_ : SMulInvariantMeasure (L × H) G μ, _, j⟩ := ⟨by simp [compHom_smul_def]⟩,
    properSMul_of_isClosedEmbedding (X := G) i hi (by tauto), hi.1.comp (isEmbedding_prodMkRight 1)
  use update id 0 1 (orbitMeasure (κ.prod ν) μ)[ρ], by grind, fun F hF hΓ hI c h ↦ ?_
  obtain ⟨_ : DiscreteTopology Γ, _⟩ := (j.homeomorphImage Λ).discreteTopology, hi.measurable
  obtain ⟨I, J⟩ := integral_quotMeasure_stages _ _ (fun (g, y) ↦ i (y, 1) * g) j.2 (by
    simpa using! measurePreserving_orbitMeasure (c := hasCutoff_of_proper).comp
      (measurePreserving_prodAssoc _ κ ν)) rfl hF.measurable hΓ hI
  have K := I.integral_prod_left.div_const c
  have m u v g := (integral_mul_right_eq_self _ u).trans (congrArg _ (funext fun y ↦
    (identDistrib_orbitMeasure_mul_right v fun ⟨γ, h⟩ a ↦ .trans (by simp) (hΓ _ ⟨γ, h, rfl⟩ _)
    ).integral_eq) : _ = ∫ y, ∫ a, F (i (y, a) * g) ∂Λ.qms ν ∂κ)
  by_contra; simp_all [integral_prod]
  exact mem_closure_iff_frequently.1 (dense_of_ae_orbitMeasure (c :=
    hasCutoff_of_proper) (have := h <| i ·
      * ·; by aesop) ((integral_eq_zero_iff_of_nonneg h₀ K.re).1 (integral_re K ▸ by grind)) _) h₁

end

variable {Λ G : Type*} {Y} [Group Λ] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MulAction Λ Y] [Countable Y] {i : Λ →* G} (hi : (⇑i).Injective) {Γ S : Subgroup G}
  [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
  (hS : S ≤ Γ) (hC : ∀ᵉ (γ) (y ∈ C), γ • y ∈ C ↔ i γ ∈ S) (hD : ∀ y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
  {k : Y → G → ℂ} (hm : ∀ y, Measurable (k y)) (hk : ∀ γ y x, k (γ • y) (i γ * x) = k y x)

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [BorelSpace G] in
/-- For a countable family of a.e. strongly measurable complex functions k_y with ∫ Σ_y |k_y| dν
finite, the integrals ∫ k_y dν are summable with sum ∫ Σ_y k_y dν. -/
lemma hasSum_integral_of_lintegral {ν : Measure G} (h : ∫⁻ x, tsum (‖k · x‖ₑ) ∂ν < ∞) (hm : ∀ y,
    AEStronglyMeasurable (k y) ν := by fun_prop) : HasSum (ν[k ·]) (∫ x, tsum (k · x) ∂ν) := by
  rw [lintegral_tsum (by fun_prop)] at h
  rw [integral_tsum hm h.ne, (Summable.of_enorm (h.trans_le' _).ne).hasSum_iff]
  grw [enorm_integral_le_lintegral_enorm]

section

attribute [local simp] lintegral_map lintegral_prod lintegral_withDensity_eq_lintegral_mul
  subgroup_smul_def mul_smul Set.indicator mul_assoc

include hi hΓ hS hC hD hm hk in
/-- Unfolding over translates D of a block C: Λ ≅ Γ discrete, k measurable, equivariant, and for
y ∈ C, γy ∈ C iff γ ∈ S. If ∑_D|k_y| on Γ\G or ∑_C|k_y| on S\G has finite integral, ∑_C k_y
is integrable and ∫_{Γ\G}∑_D k_y = ∫_{S\G}∑_C k_y, also termwise. -/
lemma integral_tsum_block (h : ∫⁻ x, ∑' y : D, ‖k y x‖ₑ ∂Γ.qms μ < ∞ ∨ ∫⁻ x, ∑' y : C, ‖k y x‖ₑ
    ∂S.qms μ < ∞) : Integrable (∑' y : C, k y ·) (S.qms μ) ∧ ∫ x, ∑' y : D, k y x ∂Γ.qms μ = ∫ x, ∑'
    y : C, k y x ∂S.qms μ ∧ ∑' y : D, ∫ x, k y x ∂Γ.qms μ = ∫ x, ∑' y : C, k y x ∂S.qms μ := by
  let : MeasurableSpace Y := ⊤
  have := measurable_from_prod_countable_right (f := delta% k.uncurry) hm
  have I : IdentDistrib (fun (x, (y : D)) ↦ k y x) (fun (x, (y : C)) ↦ k y x) ((Γ.qms μ).prod
      count) ((S.qms μ).prod count) := ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f _ ↦ by
    obtain ⟨⟨⟩, ⟨⟩⟩ := epsilon_spec (inf_of_le_right hS ▸ hasCutoff_count (_ ⊓ _)).1, hΓ
    simp (disch := fun_prop) [← lintegral_orbitMeasure_lintegral (ν := @count i.range _) (μ := μ)]
    simp_all [(tsum_subtype · fun y ↦ f <| k y ·), ← ENNReal.tsum_mul_left, i.ofInjective_apply,
      ← ENNReal.tsum_comm.trans (tsum_congr (toPerm · |>.tsum_eq _)), ← (i.ofInjective hi).tsum_eq]
    congr!
    split
    cases ‹_›
    rw [← ((i.ofInjective hi).symm.1.trans (.mulRight ‹_›)).tsum_eq,
      ← (S.inclusion_injective hS).tsum_eq]
    repeat aesop⟩
  have ⟨J, K⟩ := (inf_eq_sup.2 I.integrable_iff.eq).ge (by simpa (disch := fun_prop) [Integrable,
    HasFiniteIntegral, Measurable.aestronglyMeasurable])
  simpa [← integral_count_eq_tsum, ← integral_prod_symm _ J, integral_prod, *,
    K.integral_prod_left] using I.integral_eq

include hi hΓ hm hk in
/-- Unfolding over the orbit D of y, for Λ ≅ Γ discrete, S the stabiliser's image, k measurable,
equivariant. If ∫_{Γ\G} Σ_{z∈Y} |k_z| < ∞ or k_y is integrable on S\G, then it is, and
∫_{S\G} k_y = ∫_{Γ\G} Σ_{z∈D} k_z, also termwise. -/
lemma integral_tsum_orbit {y} (hy : (stabilizer Λ y).map i = S) (hD : ∀ z, z ∈ D ↔ y ∈ orbit Λ z) :
  S.FixesLeft (k y) ∧ (∫⁻ x, tsum (‖k · x‖ₑ) ∂Γ.qms μ < ∞ ∨ Integrable (k y) (S.qms μ) → Integrable
    (k y) (S.qms μ) ∧ ∫ x, ∑' z : D, k z x ∂Γ.qms μ = (S.qms μ)[k y] ∧ ∑' z : D, (Γ.qms μ)[k z] =
    (S.qms μ)[k y]) := ⟨by subst hy; simp_all; grind, (by convert (integral_tsum_block hi (C := {y})
  (h := ·) ..) <;> aesop_cat) ∘ Or.imp (by grw [← ·, ← tsum_comp_le_tsum_of_injective]; simp) (·.2)⟩

end

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup V]
  [NormedSpace ℂ V] [CompleteSpace V] (μ : Measure G) [IsHaarMeasure μ] {Γ : Subgroup G}
  [DiscreteTopology Γ] {F : G → V} (hi : Γ.FixesLeft F) (hF : Continuous F) {H : Subgroup G}

/-- Let Γ ≤ H ≤ G, Γ discrete, H closed, μ left invariant, F continuous, left Γ-invariant. If ∫
F(s j(x,b) x) dκ(b) = aF(sx) for s in H (κ a probability, j(x,b) in H) and ∫_H f(h j(x,b))
dh = d∫_H f with d ≠ a, then ∫_{Γ\G} F dμ = 0. -/
lemma integral_quotMeasure_eq_zero_of_mean (hi : Γ.FixesLeft F) (hF :
  Continuous F) [@IsClosed G _ H] (le : Γ ≤ H)
  {C} [MeasurableSpace C] κ [@IsProbabilityMeasure C ‹_› κ] (j : G → C → H) (d : NNReal) (hd :
  ∀ x b, haar.map (· * j x b) = d • haar) {a : ℂ} (ha : a ≠ d) (h : ∀ s x, ∫ b, F (↑(s * j x b) *
  x) ∂κ = a • F (s * x)) (hj : ∀ x, Measurable (j x) := by fun_prop) : (Γ.qms μ)[F] = 0 := by
  have ⟨_, b, e⟩ : HasCutoff (H := H) haar.inv G := inferInstance
  contrapose ha
  borelize V
  have ⟨x, n⟩ := exists_ne_zero_of_integral_ne_zero ((integral_quotMeasure_stages _ haar id ?_ ⟨?_,
    measurePreserving_smul_prod b (μ := μ).2.trans ?_⟩
    (Subgroup.map_subgroupOf_eq_of_le le) ?_ hi (.of_integral_ne_zero ha)).2 ▸ ha)
  rw [← smul_left_inj n]
  have k {b} := identDistrib_orbitMeasure_comp (.id (@count (Γ.subgroupOf H) _)) (F :=
    (F <| · * x)) ⟨?_, hd x b⟩ ?_ ?_
  repeat first
    | fun_prop | rw [integrable_prod_iff'] | simp [k.integral_eq, k.integrable_iff,
      k.norm.integral_eq, NNReal.smul_def, (Integrable.of_integral_ne_zero n).smul_measure_nnreal] |
      rw [integral_integral_swap] | simp_all [← h, ← integral_smul a, ← coe_nnreal_smul, mul_assoc]

/-- Let Γ be a discrete subgroup of G, μ left invariant, F continuous and left Γ-invariant. If
F(uy) = cF(y) for all y, for some u in G and c with |c| = 1, c ≠ 1, then ∫_{Γ\G} F dμ = 0. -/
lemma integral_quotMeasure_eq_zero_of_twist (hi : Γ.FixesLeft F) (hF :
  Continuous F) {u} {c : ℂ} (hc : ‖c‖ = 1) (hc' : c ≠ 1) (hu : ∀ y, F (u * y) = c • F y)
  : (Γ.qms μ)[F] = 0 := let ψ s y := dist (F (s * u * y)) (c • F (s * y))
  let S := (stabilizer Gᵈᵐᵃ ψ).unop.copy ((ψ <| · * ·) ⁻¹' _) rfl
  have : @IsClosed G _ S := isClosed_singleton.preimage (by fun_prop)
  let v : S := ⟨u, funext₂ (by grind [dist_smul₀])⟩
  integral_quotMeasure_eq_zero_of_mean μ hi hF (fun _ _ ↦ funext₂ (by grind [mul_assoc])) (dirac u)
    (a := c) (fun _ _ ↦ v) _ (fun _ _ ↦ isMulLeftInvariant_eq_smul ..) (fun _ ↦ by
    simp_all [← hc]) (by simpa [ψ, v, *] using congrFun₂ ·.2 1)

variable {H : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace Λ] {Γ : Subgroup Λ}

lemma integrable_of_cocompact (h : Γ.Cocpt) [MeasurableSpace Λ] [OpensMeasurableSpace Λ] {μ}
  [@IsFiniteMeasure Λ ‹_› μ] {F : Λ → ℂ} (c : Continuous F) (i : Γ.FixesLeft F) : Integrable F μ :=
  .of_bound (by fun_prop) _
  (.of_forall ((h.choose_spec.1.image c.norm).bddAbove.some_mem <| by grind [h.choose_spec.2 ·]))

lemma cocompact_prod {Δ : Subgroup H} : Γ.Cocpt → Δ.Cocpt → (Γ.prod Δ).Cocpt
  | ⟨_, c⟩, ⟨_, d⟩ => ⟨_, c.1.prod d.1, by simp_all [Γ.mem_prod, and_and_and_comm]⟩
end

-- part: Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
section
/-! General lemmas of group theory (textbook or folklore).

Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series (known
result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Smooth functions on U(p,q) as gl_n-module by right derivatives; chain rule. -/

noncomputable section


open Complex Matrix NormedSpace Topology U Norms.L2Operator VectorField ContDiff Ring Module

section

variable {n} [Fintype.{0} n] {ε : n → ℤˣ} {J X : Matrix n n ℂ} {E M : Type*} [NormedAddCommGroup E]
  [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M] (ρ : GlModule n M)

variable (n E) in
def SmoothMat : Submodule ℂ (Matrix n n ℂ → E) := by
  use! {f | ContDiff ℝ ∞ f}, (·.out.add), contDiff_const (n := ∞); simp; fun_prop

lemma SmoothMat.differentiable (f : SmoothMat n E) : Differentiable ℝ f.1 :=
  ContDiff.differentiable (n := ∞) f.2 nofun

open SmoothMat IsHermInvolution ContinuousLinearMap

@[simp] lemma expU_zero : expU 0 = (1 : U J) := by aesop

@[fun_prop] lemma U.continuous_mat : Continuous (·.1.1 : U J → _) := by fun_prop

@[fun_prop] lemma continuous_expU [IsHermInvolution J] : Continuous (expU (J := J)) :=
  continuous_U_iff_matrix.2 ((@exp_continuous _ _ (.restrictScalars ℚ ℂ _) _).comp (by fun_prop))

lemma hasDerivAt_expU (Y : unitaryLie J) g t : let γ (t : ℝ) := (g * expU (t • Y)).1.1
        HasDerivAt γ (γ t * Y) t := by simp [mul_assoc, (hasDerivAt_exp_smul_const ..).const_mul]

variable (ε X E)

-- Smooth functions on `U(p,q)`.
/-- The space of smooth E-valued functions on U(J) for J=diag(ε), ε a vector of signs. -/
abbrev SmoothU := (.funLeft ℂ E (·.1.1 : USign ε → _) ∘ₗ (SmoothMat ..).subtype).range

attribute [local simp] mul_add add_mul det_ne_zero mul_sub sub_mul mul_assoc
attribute [local instance] LieRing.ofAssociativeRing

/-- For a linear map ι whose kernel is stable under ρ, a gl_n(ℂ)-module structure on the range
of ι, together with the proof that ι is equivariant. -/
@[irreducible] def GlModule.onRange {N} [AddCommGroup N] [Module ℂ N] (ι : M →ₗ[ℂ] N) (h : ∀ X x, ι
  x = 0 → ι (ρ X x) = 0) : {σ : GlModule n _ // ∀ X x, σ X (ι.rangeRestrict x) = ι.rangeRestrict (ρ
  X x)} := by use! fun X ↦
  ι.quotKerEquivRange.conj (ι.ker.mapQ _ _ (h X)) <;> aesop (add simp [map_bracket,
  DFunLike.ext_iff, LinearMap.codRestrict, ι.quotKerEquivRange_symm_apply_image])

/-- For signs ε, J = diag(ε) and a complex matrix X, the element ½(X − J⁻¹X*J) of the Lie
algebra of U(J). -/
def unitaryLiePart : unitaryLie (signMatrix ε) := ⟨(2⁻¹ : ℝ) • (X - (signMatrix ε)⁻¹ * Xᴴ *
  signMatrix ε), by simp [unitaryLie, isHermitian.inv.eq, isHermitian.eq]⟩

lemma eq_unitaryLiePart_add_I_smul X : X =
  unitaryLiePart ε X + I • unitaryLiePart ε (-I • X) := by ext; simp [unitaryLiePart]; grind [I_sq]

/-- The gl_n(ℂ)-module of smooth E-valued functions on all matrices: Y in the Lie algebra of
U(diag ε) differentiates along the field x ↦ xY, extended complex linearly. -/
def rightDerivMat : GlModule n (SmoothMat n E) := let r X : End ℂ (SmoothMat n E) := (by
    use! fun f ↦ ⟨_, (contDiff_infty_iff_fderiv.1 f.2).2.clm_apply ((mul ℝ _).flip
    (unitaryLiePart ε X).1).contDiff⟩ <;> aesop (add simp [fderiv_add, fderiv_const_smul,
      (SmoothMat.differentiable _ _)])); by
    refine ⟨⟨⟨fun X ↦ r X + I • r (-I • X), ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩, fun _ _ ↦ .trans ?_ (lie_def ..)⟩
    all_goals intros; ext f; simp +decide [r, lieBracket, -flip_apply, ← fderiv_apply_lieBracket
      (contDiffAt (n := ∞) f.2)]; simp [unitaryLiePart, mk_eq_add_mul_I, add_smul, smul_sub,
      mul_smul, smul_smul I, @smul_comm ℂ]; module

/-- The gl_n(ℂ)-module of smooth E-valued functions on U(diag ε) under complexified right
derivatives. -/
def rightDeriv : GlModule n (SmoothU ε E) := ((rightDerivMat ε E).onRange _ fun X f h ↦
  funext fun g ↦ by have k Y := ((SmoothMat.differentiable f _).hasFDerivAt.comp_hasDerivAt _
  (hasDerivAt_expU Y g 0)).deriv.symm.trans congr(deriv ($h ∘ _) _); simp_all [rightDerivMat]).1

variable {ε X E}

@[fun_prop] lemma SmoothU.continuous : ∀ f : SmoothU ε E, Continuous f.1
  | ⟨_, F, rfl⟩ => (SmoothMat.differentiable F).continuous.comp continuous_mat

/-- Chain rule along a curve γ in U(J): if γ'(t) = γ(t)X, then for smooth f the derivative of f
∘ γ at t is the right derivative of f along X at γ(t). -/
lemma hasDerivAt_curve f {γ : ℝ → USign ε} {t} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) :
    HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E X f).1 (γ t)) t := have ⟨_, F, rfl⟩ := f
  ((SmoothMat.differentiable ..).hasFDerivAt.comp_hasDerivAt t h).congr_deriv (by
    erw [(GlModule.onRange ..).2]; simp [rightDerivMat, unitaryLiePart,
      ← two_smul ℝ, by simpa [logDerivU, h.deriv,
      ← mul_assoc, mem_U.1, isHermitian.eq] using (conjTranspose_logDerivU h.differentiableAt 1)])

lemma hasDerivAt_rightDeriv_expU f g Y t : let γ (t : ℝ) := g * expU (t • Y)
  HasDerivAt (f.1 <| γ ·) ((rightDeriv ε E Y f).1 (γ t)) t :=
  hasDerivAt_curve f (hasDerivAt_expU ..)

lemma rightDeriv_eq_fderiv {f F g} {D : _ →L[ℂ] _} (hF : HasFDerivAt F D g.1.1) (h : ∀ g, F g.1.1 =
  f.1 g) X : (rightDeriv ε E X f).1 g = D (g * X) := eq_unitaryLiePart_add_I_smul ε X ▸ have k Y :=
    ((funext h ▸ hasDerivAt_rightDeriv_expU ..).unique
    ((hF.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 (hasDerivAt_expU Y g _) (by simp))); by aesop

lemma rightDeriv_comp_clm {f f' g} (L : E →L[ℂ] ℂ) (h : f'.1 =ᶠ[𝓝 g] L ∘ f.1) :
  (rightDeriv ε ℂ X f').1 =ᶠ[𝓝 g] L ∘ (rightDeriv ε E X f).1 :=
  h.eventually_nhds.mono fun y h ↦ have k Y := ((hasDerivAt_rightDeriv_expU ..).unique
    (((hasDerivAt_rightDeriv_expU f y Y 0).map_clm L).congr_of_eventuallyEq (Continuous.tendsto'
    (by fun_prop) 0 y (by simp) h))); eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all

lemma one_le_cast_card n [Fintype n] [Nonempty n] : (1 : ℝ) ≤
  Fintype.card n := mod_cast NeZero.one_le
end
end
end

-- part: Lib.DiscreteSeries.Haar.HaarColumnChart
section
/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Splitting a skew matrix into one column and block; Jacobian of column chart. -/


open Haar Matrix MeasureTheory Complex Fintype Module LinearMap Norms.L2Operator MatMul
variable {n} [Fintype n] (k₀ : n)
set_option synthInstance.maxSize 999

omit [Fintype n] in
@[scoped simp] lemma Haar.val_ne_and_ne_val (i : Subtype (· ≠ k₀)) : i ≠ k₀ ∧ k₀ ≠ i := by lia

/-- A volume-preserving real linear homeomorphism onto real n×n matrices, inverse to y ↦
((y_{k₀k₀}, column k₀ of `skewOfReal` y without its diagonal entry), block of y off k₀). -/
noncomputable def skewColumnEquiv := (HasGaussianIntegral.exists_measurePreserving_equiv ⟨⟨fun y ↦
  ((y k₀ k₀, (skewOfReal y ·.1 k₀ : Subtype (· ≠ k₀) → ℂ)),
  y.toBlock (· ≠ k₀) (· ≠ k₀)), by aesop⟩, by aesop⟩ (by simp [add_assoc, skewOfReal,
  div_pow, sum_eq_add_sum_subtype_ne _ k₀, ← Finset.sum_add_distrib, RCLike.norm_sq_eq_def]; grind)
  (by simp [finrank_matrix]; zify [@card_pos _ _ ⟨k₀⟩]; lia)).choose.toContinuousLinearEquiv

@[simp] lemma skewColumnEquiv_spec : MeasurePreserving (skewColumnEquiv k₀) ∧ ∀ y, (skewColumnEquiv
  k₀).symm y = ((y k₀ k₀, (skewOfReal y ·.1 k₀)), y.toBlock _ _) := by simp [skewColumnEquiv]; grind

@[simp] lemma skewOfReal_skewColumnEquiv : ∀ p, letI S := skewOfReal (skewColumnEquiv k₀ p)
  S k₀ k₀ = p.1.1 * I ∧ ∀ i, S i.1 k₀ = p.1.2 i ∧ S k₀ i = -star (p.1.2 i) ∧ ∀ j, S i j.1 =
    skewOfReal p.2 i j := by simp [↓reindex_equiv
  (skewColumnEquiv _).symm, -skewColumnEquiv_spec]; simp [skewOfReal]; grind

/-- For J = 1, the map sending θ to the k₀-th column of the Cayley chart at the point
`skewColumnEquiv` k₀ (θ, 0), whose coordinate submatrix off k₀ vanishes, is injective. -/
lemma cayleyChart_col_injective :
  (fun θ ↦ (cayleyChart 1 (skewColumnEquiv k₀ (θ, 0))).1.1.col k₀).Injective := fun _ _ ↦ by
  have a θ := (and_forall_ne k₀).2 (congrFun₂
    (mul_nonsing_inv _ (det_cayleyDenom_one_ne_zero (skewColumnEquiv k₀ (θ, 0))).isUnit) · k₀)
  simp_all [sum_eq_add_sum_subtype_ne _ k₀, mul_apply, funext_iff, -Prod.forall,
    val_cayleyChart_coe, Subtype.forall', -Subtype.forall, cayleyDenom, Subtype.val_inj]
  grind +extAll [ofReal_inj, I_ne_zero, sum_eq_zero]

/-- For the family θ ↦ Cayley chart of U(n) at `skewColumnEquiv` k₀ (θ,0), the form g⁻¹dg read in
the column coordinates has absolute determinant the Cayley weight `cayleyDensity` (J = 1) at that
point. -/
lemma abs_det_logDerivU_col_eq_cayleyDensity θ : |(fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ
  skewCoords ∘ₗ logDerivU (cayleyChart 1) (skewColumnEquiv k₀ (θ, 0)) ∘ₗ
  (skewColumnEquiv k₀).1.1 ∘ₗ inl ..).det| = cayleyDensity 1 (skewColumnEquiv _ (θ, 0)) := by
  have h := abs_det_skew_congruence (skewColumnEquiv k₀).1.symm ?D
    (coprod ?L ((skewColumnEquiv _).1.1 ∘ₗ inr ..))
  rw [← LinearMap.det_conj _ (.prodComm ..), det_eq_mul_of_block_triangular id _ (id.ext _),
    det_eq_mul_of_block_triangular (fst .. ∘ₗ (skewColumnEquiv _).symm.1.1 ∘ₗ ?L) _ (id.ext _)] at h
  simpa [cayleyDensity, pow_mul] using eq_inv_of_mul_eq_one_right (h.symm.trans (by simp))
  repeat simp [conjTranspose_nonsing_inv, Prod.mk_zero_zero,
    logDerivU_cayleyChart, -skewColumnEquiv_spec] <;> simp [entrywise, skewCoords, cayleyDenom,
    sum_eq_add_sum_subtype_ne _ k₀] <;> simp [skewOfReal] <;> grind
end

-- part: Lib.DiscreteSeries.Haar.SphereFibreIntegral
section
/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: Integrating one row and column of the Cayley density gives sphere volume. -/

open Matrix MeasureTheory Real Complex Fintype Haar Subtype

/-- For J = 1, integrating Cayley's density `cayleyDensity` over the coordinates θ of row and column
k₀, the complementary block η being fixed, gives 2πⁿ/(n−1)! times the density of η in size
n−1; both sides are divided by 2πⁿa/(n−1)!, a > 0. -/
lemma lintegral_cayleyDensity_skewColumnEquiv {n} [Fintype n] (k₀ : n) η {a} (_ : 0 < a) : ∫⁻ θ,
  .ofReal (cayleyDensity 1 (skewColumnEquiv k₀ (θ, η)) / (sphereDensity (card n) 1 * a)) =
  .ofReal (cayleyDensity 1 η / a) := by
  obtain ⟨⟨k⟩⟩ := Nat.exists_eq_add_of_lt (@card_pos _ _ ⟨k₀⟩), det_cayleyDenom_one_ne_zero η
  choose x e using (canLift.1 (star _) <| neg_eq_zero.2 <|
    IsHermitian.im_star_dotProduct_mulVec_self (skewAdjoint.negISMul ⟨_,
    conjTranspose_skewOfReal η⟩).2 ·)
  erw [lintegral_prod_symm, lintegral_eq_det_mul (ofReal 2 • _) (by simpa), lintegral_congr fun w ↦
    ?e, lintegral_mul_const, lintegral_inv_add_rpow one_pos,
    ← @doublingGamma_eq_Gamma (2 * k.succ - 1)]
  case' e => rw [lintegral_congr fun _ ↦ ?p, lintegral_mul_const (.ofReal
    (rpow ‖-I / 2 * (cayleyDenom 1 η).det‖ _ / _)), lintegral_norm_add_rpow ⟨-x w, (_ + _) * 2⟩,
    mul_rpow, rpow_neg_eq_inv_rpow, mul_left_comm, ENNReal.ofReal_mul, mul_assoc]
  case' p => erw [← ENNReal.ofReal_mul, mul_div, ← mul_rpow, ← norm_mul, ← mul_assoc]; simp [
    cayleyDensity, rpow_neg, rpow_mul, -norm_mul, -Complex.norm_mul, -Nat.cast_add]; congr
  any_goals first | fun_prop | finiteness | simp [*] <;> grind
  convert det_updateCol_sum _ k₀ (val.extend w 1) ▸ twoBlockTriangular_det₀ _ (· = k₀)
    (Subtype.forall'.2 _); aesop
  repeat simp [*, toSquareBlockProp, entrywise, mk_eq_add_mul_I,
    sum_eq_add_sum_subtype_ne _ k₀, ← Finset.mul_sum, conj_mul', mul_assoc, mul_comm (w _), default,
    cayleyDenom, sub_mul, val_inj] <;> grind [I_sq]
  simp (disch := positivity) [← ENNReal.ofReal_mul, doublingGamma, ← add_sub, rpow_add,
    ← Real.Gamma_nat_eq_factorial, *, rpow_neg, field, two_mul, mul_pow]; ring
end

-- part: Lib.DiscreteSeries.Haar.HaarMass
section
/-! Part of: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume growth
(known result; see Lib.DiscreteSeries.Haar.RegularRepL2).

This file: U(n) has total mass one; the measure on U(J) is right invariant. -/


open MeasureTheory Measure Fintype
variable {n} [Fintype.{0} n]

/-- U(n) has mass 1 (the Cayley density has integral `volU n`): one column at a time.

Known result: Haar measure of U(J) in Cayley coordinates, volume of U(n), polynomial volume
growth. -/
instance isProbabilityMeasure_haarU : @IsProbabilityMeasure (U (1 : Matrix n n ℂ)) _ volume := ⟨by
  simp [← lintegral_one, ↓lintegral_eq_cayleyChart]
  induction' hk : card n with k ih generalizing n
  rw [card_eq_zero_iff] at hk; simpa [volU] using! pi_empty_univ _
  erw [volU, Finset.prod_range_succ_comm,
    ← (skewColumnEquiv_spec ((equivFinOfCardEq hk).2 0)).1.lintegral_comp, lintegral_prod_symm,
    funext (hk ▸ lintegral_cayleyDensity_skewColumnEquiv _ · (volU_pos k) :), ih] <;> measurability⟩

instance :
  @IsProbabilityMeasure (U (@signMatrix n 1)) _ volume := by rw! [signMatrix_one]; infer_instance

instance {J} [@IsHermInvolution n _ J] : (@volume (U J) _).IsMulRightInvariant :=
  ⟨(measurePreserving_haarU 1 · 1 (.mulRight _) |>.2)⟩
end
