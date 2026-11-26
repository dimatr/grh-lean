import Lib.Adelic.ArtinDefs
import Lib.Adelic.Places
import Lib.ClassField.AdicRingHomExt

section
/-! Known result: Hilbert ramification theory for infinite Galois extensions; ideles and ideal
classes. Here places are valuation rings of an algebraic closure acted on by an abstract profinite
group, and local fields are only henselian with finite residue field. Of tame inertia, only the
prime-to-p quotients and the relation with Frobenius are proved. Source: J. Neukirch, Algebraic
Number Theory, 1999, I §9, II §§7–9, VI §1; J.-P. Serre, Local Fields, 1979, I §7, IV §2; Stacks
Project, tag 09EE.

This file: Uniformisers and the normalised rational valuation on the algebraic closure of a local
field. Frobenius exists and, with inertia, topologically generates a local Galois group. -/

open FiniteField Classical Finset Fint Ideal IsDiscreteValuationRing IsLocalRing MulAction
  MulSemiringAction Subgroup Valuation Ideal.Quotient

variable {Γ k Ω} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction
  Γ Ω] {A : ValuationSubring Ω} (L : IsLocalGalois Γ k A) {π : kˣ} (h : IsUniformiser A π.1) {x y :
  valRingBelow k A}

lemma IsUniformiser.val_lt_one {π} : IsUniformiser A π → valuationVia k A π < 1 := (· π |>.2 le_rfl)

lemma dvd_iff_valuationVia_le : x ∣ y ↔ valuationVia k A y ≤ valuationVia k A x :=
  (integer.integers _).dvd_iff_le

/-- If A ∩ k is a discrete valuation ring, then π ∈ k is a uniformiser for A if and only if π
lies in A ∩ k and is irreducible there. -/
lemma isUniformiser_iff_irreducible [IsDiscreteValuationRing (valRingBelow k A)] {π} :
    IsUniformiser A π ↔ ∃ h, Irreducible (⟨π, h⟩ : valRingBelow k A) := by
  simp [irreducible_iff_uniformizer, Ideal.ext_iff, ↓mem_maximalIdeal_iff, mem_span_singleton,
    dvd_iff_valuationVia_le, ← comap_apply, IsUniformiser]
  grind

lemma exists_val_eq_pow_index [G : IsProGalois Γ k Ω] (h : ∀ g, g ∈ decompGroup Γ A) x : ∃ c,
  valuationVia k A c = A x ^
  (stabilizer Γ x).index := have : Finite (orbit Γ x) := (isLocallyConstant_smul x).range_finite
  (G.1.3.1 _ fun g ↦ smul_prod'.trans (Equiv.prod_comp (toPerm g) ((↑) : orbit Γ x → Ω))).imp
    (by simp_all [index_stabilizer, prod_eq_pow_card, mem_orbit_iff, decompGroup.val_smul,
    valuationVia])

include L h in
lemma IsUniformiser.card_quot a (e : valuationVia k A x = valuationVia k A π ^ a) :
  .card (_ ⧸ span {x}) = residueCard k A ^ a := have := L.5; ((span _).ext
    (by simp_all [(isUniformiser_iff_irreducible.1 h).2.maximalIdeal_eq, dvd_iff_valuationVia_le,
    span_singleton_pow, mem_span_singleton, valuationVia])).substr (cardQuot_pow_of_prime this.3)

lemma IsUniformiser.exists_val_eq_zpow (L : IsLocalGalois Γ k A) (h : IsUniformiser A π.1) x (hx :
  x ≠ 0) : ∃ a : ℤ, valuationVia k A x = valuationVia k A π ^ a := have := L.5
  (exists_units_eq_smul_zpow_of_irreducible (isUniformiser_iff_irreducible.1 h).2 hx).imp fun _ ⟨u,
    e⟩ ↦ by erw [e, valuationVia, ← comap_apply, map_mul, (integer.integers _).valuation_unit]; simp

/-- Let k be a henselian local field with uniformiser π. For x ∈ Ω^×, n ∈ ℕ and a ∈ ℤ, x^n and
π^a have equal A-valuation if and only if n·ord(x) = a, ord the order normalised on k. -/
lemma IsUniformiser.val_pow_eq_iff_mul_ordRat (L : IsLocalGalois Γ k A) {π : kˣ} (h :
  IsUniformiser A π.1) {x} (n : ℕ) (a : ℤ) :
  A.valuation x.toMul ^ n = valuationVia k A π ^ a ↔ n * ordRat k A x = a := by
  have := (quotient_finite_of_isOpen _ <| L.1.6 ·)
  choose b e using fun x : Ωˣ ↦ (exists_val_eq_pow_index L.4 x).elim fun c e ↦
    e ▸ h.exists_val_eq_zpow L _ (by simpa [·, valuationVia] using e.ge)
  refine (epsilon_spec ⟨.mk' (fun x ↦ b x.toMul / (stabilizer Γ x.toMul.1).index) ?_, fun p q ↦
    (by grind [IsUniformiser] : valuationVia k A π = valuationVia k A p).rec ?_⟩ :
    Set.ofPred _ (ordRat ..)) _ h ..
  all_goals simp [field]; norm_cast; simp [← zpow_right_inj₀ _ h.val_lt_one.ne,
    ← e, pos_iff, zpow_add₀, zpow_mul, mul_comm, pow_right_comm, mul_pow]

lemma IsUniformiser.ordRat_eq_one (h : IsUniformiser A π.1) :
    _root_.ordRat k A (DiscreteUnits.ofBase Γ Ω (.ofMul π)) = 1 :=
  (one_mul _).symm.trans ((h.val_pow_eq_iff_mul_ordRat L ..).1 rfl)

namespace IsLocalGalois

lemma exists_isUniformiser (L : IsLocalGalois Γ k A) : ∃ π : kˣ, IsUniformiser A π.1 := have := L.5
  this.exists_irreducible.rec (⟨.mk0 · (by aesop), isUniformiser_iff_irreducible.2 ⟨_, ·⟩⟩)

lemma ordRat_eq_zero (L : IsLocalGalois Γ k A) {x} : ordRat k A x = 0 ↔ A x.toMul = 1 := by
  simpa using (L.exists_isUniformiser.choose_spec.val_pow_eq_iff_mul_ordRat L 1 0).symm

/-- Let Γ = Gal(Ω/K) be the absolute Galois group of a henselian local field, with valuation ring A
of Ω. An arithmetic Frobenius exists; for any such φ the products φ^n·i (n ≥ 0, i in inertia) are
dense in Γ; A is integral over A ∩ K. -/
lemma frobenius_spec {K} [Field K] [Algebra K Ω] [L : IsLocalGalois Γ K A] : (∃ φ : Γ, IsFrob A
  (residueCard K A) φ) ∧ (∀ {φ}, IsFrob A (residueCard K A) φ → DenseRange fun p : ℕ × inertiaGroup
  Γ A ↦ φ ^ p.1 * p.2.1) ∧ ∀ x : valRingBelow Ω A, IsIntegral (valRingBelow K A) x.1 := by
  let B := valRingBelow Ω A; let R := IsLocalRing.ResidueField B; let : UniformSpace B := ⊥
  let := (⟨by simp [B, mem_decompGroup_iff.1, L.4]⟩ : IsInvariantSubring Γ B.1).toMulSemiringAction
  rcases (⟨(Subtype.ext <| smul_comm · · ·.1)⟩ : SMulCommClass Γ (valRingBelow K A) B),
    continuousSMul_iff_stabilizer_isOpen (X := B).2 (isOpen_mono (by aesop_cat) <| L.1.6 ·)
  have : Algebra.IsInvariant (valRingBelow K A) B Γ :=
    ⟨fun ⟨x, _⟩ e ↦ by obtain ⟨_, ⟨⟩⟩ := L.1.1.3.1 x (congr($(e ·))); tauto⟩
  have := this.isIntegral_of_profinite
  have e {q} {g : Γ} : (∀ y : R, g • y = y ^ q) ↔ IsFrob A q g := by
    simp [IsFrob, B, R, residue_surjective.forall, L.4]
    congr!; exact residue_eq_iff_valuation_sub_lt_one
  use ⟨_, Fintype.card_eq_nat_card ▸ e.1 (congr($((stabilizerHom_surjective_of_profinite (G := Γ) _
    _ (@frobeniusAlgEquivOfAlgebraic _ _ (@.ofFinite _ L.6) R _ _ (algebra_isIntegral_of_liesOver
    ..).isAlgebraic)).choose_spec) ·))⟩, fun {φ} hφ g ↦ (@stabilizerHom_surjective_of_profinite
    (FixedPoints.subring ..) _ _ _ _ (zpowers φ).topologicalClosure _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨rfl⟩
    ⟨by tauto⟩ {toRingAut _ R g with commutes' := ?_}).rec fun s hs ↦ mul_inv_cancel_left ↑s g ▸
    map_mem_closure (f := (· * _)) (by fun_prop) ((closure_range_zpow_eq_pow φ).le s.1.2)
    fun _ ⟨n, k⟩ ↦ ⟨⟨n, _, e.1 (by simpa [mul_smul, inv_smul_eq_iff] using! (congr($hs ·).symm))⟩,
    congr($k * _)⟩, (this.1 · |>.algebraMap)
  rintro ⟨a⟩; obtain ⟨⟨⟩, e⟩ := Polynomial.splits_X_pow_nat_card_sub_X.mem_range_of_isRoot
    (i := algebraMap _ R) (X_pow_card_sub_X_ne_zero _ L.6.one_lt_card)
    (by simpa [e.2 hφ] using congr(residue _ $(a.2 ⟨_, subset_closure ⟨1, rfl⟩⟩)))
  exact e ▸ congr(⟦$(smul_algebraMap g _)⟧)
end IsLocalGalois
end

section
/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Finite extension of a local field is local, with ef equal to the degree. -/


open Nat IsLocalRing Module Algebra.TensorProduct Ideal Subtype Rat IsIntegralClosure ResidueField
variable {Γ k Ω} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [G : IsLocalGalois Γ k A]

lemma valuation_residueCard_lt_one :
  A (residueCard k A) < 1 := by simpa [↓Valuation.mem_maximalIdeal_iff]
  using! (maximalIdeal (valRingBelow k A)).toAddSubgroup.nsmul_index_mem 1

/-- A finite extension k' of a local field k is local; there are e, f with ef = [k':k], q' = q^f
and ord_{k'} = e·ord_k; and #(𝒪'/n) = #(𝒪/n)^{[k':k]} for every natural number n. -/
lemma IsLocalGalois.of_finite (V : OpenSubgroup Γ) (k' := ↥(fixedFieldOf V.1)) [Field k'] [Algebra
  k' Ω] [IsProGalois V.1 k' Ω] [Algebra k k'] [IsScalarTower k k' Ω] [FiniteDimensional k k'] :
  IsLocalGalois V.1 k' A ∧ (∃ e f, (e * f = V.index ∧ residueCard k' A = residueCard k A ^ f ∧
  ordRat k' A = e • ordRat k A) ∧ (inertiaGroup Γ A ≤ V → e = 1)) ∧ ∀ n : ℕ, Nat.card
  (_ ⧸ span {(n : valRingBelow k' A)}) = .card (_ ⧸ span {(n : valRingBelow k A)}) ^ V.index := by
  obtain ⟨⟨H, d, hf⟩, ⟨π, hπ⟩, ⟨⟨σ, s⟩, D, F⟩, -, n⟩ := id G, G.exists_isUniformiser,
    G.frobenius_spec, eq_fixingSubgroup_of_isProGalois (V := V.1)
  let O := valRingBelow k A
  let P := valRingBelow k' A
  rcases (algebraMap k Ω).charZero, IsScalarTower.algebraMap_apply k k' Ω,
    (⟨(F ⟨_, ·.2⟩ |>.tower_bot_of_field.tower_bot val_injective)⟩ : Algebra.IsIntegral O P)
  rcases isNoetherian O k k' P, isNoetherianRing O k k' P, FaithfulSMul.tower_bot O P k'
  have L : IsLocalGalois V.1 k' A :=
    ⟨(H ·), ⟨ne_bot_of_liesOver_of_ne_bot d.3 _⟩, finite_of_finite hf⟩
  obtain ⟨⟨π', hπ'⟩, hc⟩ := L.exists_isUniformiser, fun x : O ↦ by
    simpa [← IsFractionRing.finrank_eq _ k P k', card_fun, ← n] using card_congr
      ((quotIdealMapEquivQuotTensor _ (span {x})).1.trans (basis _ (finBasis _ P)).equivFun.toEquiv)
  have ⟨e, he⟩ := hπ'.exists_val_eq_zpow L (algebraMap k k' π) (by simp)
  lift e to ℕ using by simpa [zero_lt_iff, hπ'.val_lt_one, valuationVia, *] using hπ.val_lt_one.le
  use L, ⟨e, .imp (fun f h ↦ ⟨h, fun I ↦ ?_⟩) ⟨_, Nat.pow_right_injective hf.one_lt_card (by
    simpa [O, pow_mul', ← natCard_eq_pow_finrank, hπ.card_quot G 1] using (hπ'.card_quot L _
      he).symm.trans (hc ⟨_, hπ.val_lt_one.le⟩)), natCard_eq_pow_finrank, ?_⟩⟩, (mod_cast hc ·)
  rcases I ((h.2.1 ▸ s.pow f).inv_mul L.frobenius_spec.1.choose_spec), n ▸ finrank_pos
  nlinarith [f.card_fin, h.1.trans_le (card_le_card_of_surjective (⟦σ ^ Fin.val ·⟧) (Quotient.ind
    (isClosed_property (D s) ⟨@isOpen_discrete (_ ⧸ V.1) _ _ (.range _)ᶜ⟩
    (⟨@.ofNat f ⟨by lia⟩ ·.1, by simp_all [mod_def, I _, pow_sub, mul_div_le, pow_mul,
    mul_mem_cancel_right, pow_mem]⟩))))]
  ext
  simpa [*, valuationVia, ← zpow_mul, hπ'.val_pow_eq_iff_mul_ordRat L _ _, -zpow_natCast,
    ← den_mul_eq_num,
    mul_left_comm e.cast] using (hπ.val_pow_eq_iff_mul_ordRat G ..).2 (den_mul_eq_num _)

/-- For a local field k, every x in Ω^× fixed by the inertia group has integral order, for the
order normalised on k. -/
lemma IsLocalGalois.exists_ordRat_eq_intCast {x} (h : ∀ g ∈ inertiaGroup Γ A, unitsRep g x = x) :
  ∃ n : ℤ, ordRat k A x = n := (G.of_finite (id ⟨_, G.1.6 _⟩)).elim fun L ⟨⟨_, _, o⟩, _⟩ ↦
  L.exists_isUniformiser.rec fun _ p ↦ (p.exists_val_eq_zpow L ⟨_, (·.2)⟩ (x.ne_zero ∘ mk.inj)).imp
  fun _ ↦ by simpa [o, o.2 (congr($(h · ·).1)), -id_eq] using! (p.val_pow_eq_iff_mul_ordRat L 1 _).1
end

section
/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Prime induced by a p-adic embedding; extension to the completion and finite adeles.
Unique unramified character with given value at Frobenius; uniform local constancy. -/

open ComplexConjugate IntermediateField IsDenseInducing Module NNReal NormedField NumberField
  Valuation Valued

variable {E : Type*} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] {F : Type _} [NormedField F]
  [IsUltrametricDist F] [CharZero F] [PadicField F p] (σ : E →+* F) {x : 𝔸f E}

section

omit [CharZero F]

lemma norm_le_one_of_isIntegral {R} [CommRing R] (ι : R →+* F) {x} : IsIntegral ℤ x → ‖ι x‖ ≤ 1 :=
    ((integer.integers (valuation.comap ι)).mem_of_integral ·.tower_top)

omit [NumberField E] in
lemma norm_ringOfIntegers_le (x : 𝓞 E) : ‖σ x‖ ≤ 1 := norm_le_one_of_isIntegral _ x.2

/-- The prime of E above p induced by an embedding σ of E into an ultrametric normed field F
over ℚ_p: the integers x of E with ‖σ x‖ < 1. -/
noncomputable def placeOfEmb : FinPlace E := ⟨centrePrime E (valuation.comap σ).valuationSubring,
  .comap _, (NeZero.ne ↑p <| ·.le ((mem_maximalIdeal_iff ..).2 (by simpa using! norm_p_lt_one)))⟩

lemma isEquiv_placeOfEmb : (valuation.comap σ).IsEquiv ((placeOfEmb σ).valuation E) :=
    (isEquiv_valuation_valuationSubring _).trans (IsPlaceOver.of_le_centrePrime le_rfl).isEquiv

/-- An integer x of the number field E lies in the prime `placeOfEmb` σ induced by an embedding σ
of E into an ultrametric normed field over ℚ_p if and only if ‖σ x‖ < 1. -/
@[simp] lemma mem_placeOfEmb x : x ∈ (placeOfEmb σ).1 ↔ ‖σ x‖ < 1 := mem_maximalIdeal_iff ..

end

attribute [irreducible] placeOfEmb

/-- The ring homomorphism from ℂ to ℂ_p obtained by composing an isomorphism ι from ℂ onto the
algebraic closure of ℚ_p with the inclusion into ℂ_p. -/
noncomputable abbrev complexToCp (ι : ℂ ≃+* PadicAlgCl p) := (algebraMap _ ℂ_[p]).comp ι.toRingHom

/-- The prime of E above p induced by the complex embedding σ followed by the isomorphism ιℓ
from ℂ to the algebraic closure of ℚ_p. -/
noncomputable abbrev inducedPrime [PadicIso p] (σ : E →+* ℂ) := placeOfEmb (ιℓ.toRingHom.comp σ)

omit [CharZero F] in
/-- The rational prime p lies in the prime of E induced by an embedding σ of E into an
ultrametric normed field F over ℚ_p. -/
@[simp high] lemma natCast_mem_placeOfEmb : ↑p ∈ (placeOfEmb σ).1 := by simp [norm_p_lt_one]

instance instFiniteDimensionalPadicSubtypeMemIntermediateFieldAdjoinRangeCoeRingHom_new
    : FiniteDimensional ℚ_[p] (adjoin ℚ_[p] (.range σ)) := rank_lt_aleph0_iff.1 (let :=
  σ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  (σ.toRatAlgHom.fieldRange.adjoin_rank_le_of_isAlgebraic_right _).trans_lt (rank_lt_aleph0 ..))

/-- An embedding σ of E into an ultrametric normed field over ℚ_p extends to a continuous
homomorphism φ on the completion at the induced prime, with values in ℚ_p(σ(E)) and ‖φ(x)‖ ≤
‖φ(y)‖ exactly when v(x) ≤ v(y). -/
lemma exists_placeOfEmb_extension : ∃ φ : LocField (placeOfEmb σ) →+* F, Continuous φ ∧
  (∀ x, φ (algebraMap E _ x) = σ x) ∧ (∀ x, φ x ∈ adjoin ℚ_[p] (.range σ)) ∧
  (valuation.comap φ).IsEquiv v := let := FiniteDimensional.complete ℚ_[p]
  have ⟨c, hc, h⟩ := (place (algebraMap E (LocField (placeOfEmb σ)))).isEquiv_iff_exists_rpow_eq
    (w := place σ).1 (by simpa [v_algebraMap_eq_valuation] using! (isEquiv_placeOfEmb σ).symm ·)
  let := SeminormedRing.induced E _ (FinitePlace.embedding (placeOfEmb σ))
  have u := uniformContinuous_of_tendsto_zero (f := σ.codRestrict (adjoin ℚ_[p] (.range σ))
    (by aesop)) (squeeze_zero_norm h.ge (tendsto_norm_zero.rpow_const_nhds_zero hc))
  have D := (placeOfEmb σ).denseRange_algebraMap E
  have := (uniformContinuous_uniformly_extend ⟨rfl⟩ D u).continuous
  ⟨(algebraMap ..).comp (extendRingHom ⟨rfl⟩ D u), by have := D.eq ?_ this.norm (.rpow_const
    (p := c) continuous_norm (by grind)) <;> simp_all [extendRingHom, extend_eq, u.continuous,
    funext_iff, Valuation.IsEquiv, ← coe_le_coe, Real.rpow_le_rpow_iff]; fun_prop⟩

/-- The ring homomorphism from the finite adeles of E to F: the component at the prime induced
by σ : E → F, followed by a continuous extension of σ to the completion. -/
noncomputable def adeleExtension := (exists_placeOfEmb_extension σ).choose.comp (evalAt _)

@[simp] lemma adeleExtension_algebraMap (x : E) : adeleExtension σ x = σ x :=
  (exists_placeOfEmb_extension σ).choose_spec.2.1 x

@[fun_prop] lemma continuous_adeleExtension :
  Continuous (adeleExtension σ) := (exists_placeOfEmb_extension σ).choose_spec.1.comp (by fun_prop)

lemma norm_adeleExtension_eq_iff y : ‖adeleExtension σ x‖ = ‖adeleExtension σ y‖ ↔
  v (x (placeOfEmb σ)) = v (y (placeOfEmb σ)) := coe_inj.trans
  (exists_placeOfEmb_extension σ).choose_spec.2.2.2.eq_iff

lemma norm_adeleExtension_le_one : x ∈ Ô E → ‖adeleExtension σ x‖ ≤ 1 :=
    (exists_placeOfEmb_extension σ).choose_spec.2.2.2.le_one_iff_le_one.2 ∘ (mem_Ô.1 · _)

variable [IsCMField E] {Γ Ω k : Type _} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω]
  [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

omit [CharZero F] in
lemma placeOfEmb_comp_star : placeOfEmb (σ.comp conj) = star (placeOfEmb σ) := by aesop

/-- For a CM field E, the extension `adeleExtension` σ of a p-adic embedding σ to finite adeles
takes at the conjugate of x the value that the extension of σ ∘ conj takes at x. -/
lemma adeleExtension_star : ∀ x, adeleExtension σ (star x) = adeleExtension (σ.comp conj) x :=
  denseRange_algebraMap_finAdele.eq

variable {E : Type*} [Field E] [CMType E] {F : Type _} [NormedField F] [IsUltrametricDist F]
  [CharZero F] in
/-- For an infinite place v and ι : ℂ → F, the embedding x ↦ ι(Φ_v(x̄)) of E in F, with Φ the CM
type. -/
noncomputable abbrev weightEmbedding (ι : ℂ →+* F) v :=
  (ι.comp (Φ v)).comp (starRingEnd E)

/-- For a profinite group Γ, a compact space Y, a discrete space X and a continuous f : Γ × Y →
X, there is an open normal subgroup U of Γ with f(u, y) = f(1, y) for all u in U and all y. -/
lemma exists_openNormalSubgroup_apply_eq {Y X} [IsProGalois Γ k Ω] [TopologicalSpace Y]
  [CompactSpace Y]
  [TopologicalSpace X] [DiscreteTopology X] {f : Γ × Y → X} (hf : Continuous f) : ∃ U :
  OpenNormalSubgroup Γ, ∀ u ∈ U, ∀ y, f (u, y) = f (1, y) := by simpa [Set.subset_def]
  using ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isClosedMap_fst_of_compactSpace
  _ ((isClosed_discrete (.offDiag ⊤)).preimage (f := fun p ↦ (f p, f (1, p.2))) (by fun_prop))).1

/-- Let Γ be the absolute Galois group of a local field k and φ an arithmetic Frobenius. For
every r in ℚ/ℤ there is exactly one continuous character χ : Γ → ℚ/ℤ that is trivial on
inertia and has χ(φ) = r. -/
lemma existsUnique_unramified_char {φ} (hφ : IsFrob A (residueCard k A) φ) r :
    ∃! χ : QZChar Γ, (∀ g ∈ inertiaGroup Γ A, χ.1 g = 0) ∧ χ.1 φ = r := have := L.6
  let N : ℕ+ := ⟨residueCard k A ^ addOrderOf r - 1, by simp [this.one_lt_card, r.isAddTorsion]⟩
  have hN : A N = 1 := by simp [N, map_sub_eq_of_lt_right, pow_lt_one', r.isAddTorsion,
    valuation_residueCard_lt_one]
  (QZ.exists_extend (zmultiplesHom _ (Additive.ofMul (cycCharMod Ω N φ))) (zmultiplesHom _ r) (by
    simpa [Nat.dvd_iff_mod_eq_zero, Nat.sub_eq_iff_eq_add NeZero.one_le, N, this.one_lt_card.ne',
    ↓zmultiplesHom_ker_eq, Int.mem_zmultiples_iff, Int.ofNat_dvd] using! (((hφ.pow (orderOf
      (cycCharMod Ω N φ))).mem_ker_cycCharMod_iff hN).1 (by simp)).symm.dvd')).rec fun e he ↦
    .imp (fun b h ↦ ⟨h, fun ⟨_, a, _⟩ _ ↦ Subtype.ext ((L.frobenius_spec.2.1 hφ).equalizer a b.2.1
    (by ext ⟨n⟩; induction n <;> simp_all [pow_add, b.2.2]))⟩) ⟨⟨(e ∘ .ofMul) ∘ cycCharMod Ω N,
    .comp (by fun_prop) (.of_isOpen_ker _ Fact.out), by simp⟩,
    by simpa +contextual [cycCharMod_of_mem_inertiaGroup _ hN] using he 1⟩
end
