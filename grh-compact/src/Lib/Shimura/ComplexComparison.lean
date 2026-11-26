import Lib.Shimura.ThetaOrthogonality
import Lib.Shimura.ThetaFamily

section
/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Rigid objects: theta coordinates span sections; theta law over local rings.
Multiplication by nonzero a is an isogeny; counting torsion points over C. Line bundles with theta
coordinates: pull-back, product, translation, uniqueness in Appell-Humbert. -/

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {R : Type} [CommRing R]

/-- On every pull-back of x to a noetherian local ring B, global functions on the abelian scheme
are constant and the coordinates span H⁰(N) over B. -/
def ThetaObject.IsRigid (x : ThetaObject X (AlgebraicGeometry.Spec ⟨R⟩)) := ∀ ⦃B⦄ [CommRing B]
  [IsLocalRing B] [IsNoetherianRing B] ⦃y : ThetaObject X (AlgebraicGeometry.Spec ⟨B⟩)⦄ ⦃b⦄,
  y.IsPullbackAlong b x → HasConstFunctions y.groupScheme.hom ∧
  Submodule.span B (.range (coordSection y.isProjEmbedding.1)) = ⊤

lemma ThetaObject.obj_isThetaStructure (x : ThetaObject X (AlgebraicGeometry.Spec ⟨R⟩))
  [IsLocalRing R] : IsThetaStructure (D.lagrangian.addSubgroupOf _)
  (.comp x.levelPoints (AddSubgroup.inclusion D.T_le_levelTorsion)) x.isProjEmbedding.1
  (X.theta_law _ x.isGroupBaseChange).choose := Exists.choose_spec _

open Nat AddSubgroup AlgebraicGeometry CategoryTheory FractionalIdeal LinearMap NumberField
  Submodule MonoidalCategory Complex Finset LineBundle
section

variable {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]

/-- For a non-zero ideal I of O_E, the submodule of (𝔸_f / Ô)ⁿ killed by I has N(I)^|n|
elements, where N(I) is the absolute norm and |n| the size of the index set. -/
lemma card_torsionBySet_adelicTorsion {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    .card (torsionBySet (𝓞 E) (_root_.AdelicTorsion E n) I) = I.absNorm ^ Fintype.card n := by
  let J := (coeIdealHom (nonZeroDivisors _) E I)⁻¹.coeToSubmodule.subtype
  rw [← (torsionBySet ..).map_comap_eq_of_surjective frameTorsionClass_surjective,
    (_ : .comap .. = (J.compLeft n).range), ← range_comp,
    ← card_congr (quotKerEquivRange _).toEquiv, ker_comp, ker_frameTorsionClass_one]
  exact (index_pi fun _ ↦ (Submodule.comap J 1).toAddSubgroup).trans (Finset.prod_eq_pow_card fun _
    _ ↦ .trans (by simpa using! card_congr (quotientEquiv _ 1 1 _ (by aesop) (by simp [mem_inv_iff,
    *]) coeIdeal_le_one (by simpa) (by simpa)).toEquiv) ((relIndex_map_map_of_injective _ ⊤
    (AddSubgroupClass.subtype_injective _)).trans (relIndex_top_right _)))
  ext; simp [← map_smul_of_tower, ← mem_ker, ker_frameTorsionClass_one, J, range_compLeft,
    mem_inv_iff, *, Algebra.smul_def, mul_comm, @forall_comm n, -map_smul, -LinearMap.map_smulₛₗ]

end

variable {E : Type} [Field E] [CMBase E] {D : PEL E} {R : CommRingCat}
  {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} (y : ThetaObject X (Spec R)) [IsLocalRing R]

/-- On the abelian scheme of an object y over a local ring, multiplication by a non-zero element
a of O_E is finite, flat and surjective. -/
lemma ThetaObject.finite_flat_surjective_smul {a : 𝓞 E} (ha : a ≠ 0) :
  IsIsogeny (a • 𝟙 y.groupScheme) := by
  choose c e using Ideal.mem_span_singleton'.1 (Ideal.span {a}).absNorm_mem
  refine finite_flat_of_quasiFinite _ (@.of_comp _ _ _ _ (c • 𝟙 y.groupScheme).1 ?_) (@.of_comp _ _
    _ (c • 𝟙 y.groupScheme).1 _ ?_) <;> simp_all [← Over.comp_left, smul_smul, mul_comm,
    cast_smul_eq_nsmul,
    -cast_natAbs, IsAbelianScheme.nsmul_surjective, locallyQuasiFinite_of_pull_picClass
    y.isProjEmbedding _ (pull_nsmul_eq_sq_smul y.hasClassLaws.1 _)]

/-- Let A be the abelian variety of an object of the family over ℂ. Every injective O_E-linear
map (𝔸_f / Ô)ⁿ → A(ℂ) has all torsion points of A(ℂ) in its image. -/
lemma ThetaObject.exists_apply_eq_of_torsion (x : ThetaObject X (Spec ⟨ℂ⟩)) {f :
  _root_.AdelicTorsion E D.Index →ₗ[𝓞 E] 𝟙_ _ ⟶ x.groupScheme} (i : (⇑f).Injective) y : (∃ m ≠ 0,
  m • y = 0) → ∃ l, f l = y | ⟨m, hm, h⟩ => have c :=
    (x.isProjEmbedding.nonempty_uniformisation x.smoothOfRelativeDimension).some.card_torsion hm
  have := finite_of_card_ne_zero (c.trans_ne (by aesop))
  (((Subtype.map_injective (by simp_all [← map_nsmul, cast_smul_eq_nsmul])
    i).bijective_of_nat_card_le
    ((card_torsionBySet_adelicTorsion (I := Ideal.span {↑m}) (by simpa)).trans_ge (c.trans (by
    simp [↓Ideal.absNorm_span_natCast, finrank_eq_two_mul_card_infinitePlace, RingOfIntegers.rank,
      abelianDim, ↓Module.finrank_fin_fun]; ring)).le)).2 ⟨y, h⟩).rec (⟨·, congr($(·))⟩)

variable {O : Type} [CommRing O] [ValuativeArc O]
  {X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of O))} {ι κ V V' : Type}
  [FinComplexSpace V] [FinComplexSpace V'] {L : Submodule ℤ V} {B : LatticeForm L}
  {B' : LatticeForm L} {χ : V → ℂ} {χ' : V → ℂ} {θ : V → ι → ℂ} {θ' : V → κ → ℂ}
  {S : AlgebraicGeometry.Scheme} {e : V → (AlgebraicGeometry.Spec (CommRingCat.of ℂ) ⟶ S)}
  {N : LineBundle S ι} {M : LineBundle S κ} [AddObj X] (u : Uniformisation (O := O) X V)
  (h : @HasThetaCoords S ι V _ L e N B χ θ) (h' : HasThetaCoords (ι := κ) L e M B' χ' θ')

attribute [local simp, local grind] ofLinearComb IsHomogCoords atGeneric IsSection IsFrame

lemma Uniformisation.atGeneric_add a z : atGeneric u.expMap (z + a) =
  atGeneric u.expMap z ≫ (translation (u.expMap a)).1 := by simp [← Over.comp_left]

namespace HasThetaCoords

include h

lemma pull {S' L' e' f} F (he : ∀ z, e (F z) = e' z ≫ f) (hF : ∀ l ∈ L', F l ∈ L := by aesop) :
    @HasThetaCoords S' _ V' _ L' e' (N.pull f) (B.pullForm F) (χ ∘ F) (θ ∘ F) :=
  ⟨h.1.pull f, h.rec (by simp_all [isAppellHumbert_iff, riemannForm]),
  (h.3 · |>.imp (by fun_prop) (by aesop)), (he · ▸ h.4 _ :)⟩

/-- If θ gives theta coordinates of type (B, χ) for N along e, then the monomials of degree m in
θ give theta coordinates of type (mB, χ^m) for the m-th power of N. -/
lemma pow m : HasThetaCoords L e (N.pow m) (m • B) (χ ^ m) fun z i ↦ ∏ a, θ z (i a) := by
  obtain ⟨⟨⟩, ⟨⟩⟩ := forall_and.1 h.3, h
  constructor <;> simp_all [IsLinearSystem.pi, IsAppellHumbert.nsmul, thetaSpace, mul_pow,
    landsIn_iInf, LineBundle.pow, prod_eq_zero_iff, ← exp_nsmul, mul_div]; fun_prop

lemma pull_translate {f a} (he : ∀ z, e (z + a) = e z ≫ f) : HasThetaCoords L e (N.pull f) B
  (fun l ↦ χ l * B.riemannPhase l a) fun z i ↦ B.thetaShift a (θ · i) z := ⟨h.1.pull f,
  h.2.shift a, by simp [↓h.2.thetaShift_mem, h.3], (he · ▸ h.4 _ |>.smul (by simp))⟩

include h'

lemma mul : HasThetaCoords L e (N.mul M) (B + B') (χ * χ') fun z p ↦ θ z p.1 * θ' z p.2 := ⟨h.1.mul
  h'.1, h.2.add h'.2, fun _ ↦ thetaSpace.mul (h.3 _) (h'.3 _), fun _ ↦ (h.4 _).mul (h'.4 _)⟩

/-- Let e be holomorphic, and let θ, θ' be theta coordinates along e of N, M, of types (B, χ),
(B', χ') for L. A section w of N ⊗ M⁻¹, L-periodic along e, pulls back to Gθ'_a/θ_i where
θ_iθ'_a ≠ 0, for a theta function G of type (B − B', χ/χ'). -/
lemma exists_theta_of_isSection {w} (hw : (N.mul M.inv).IsSection w) (he : ∀ z,
  HolomorphicAt e z) (hL : ∀ᵉ (l ∈ L) (z) (i), w i
  _ (e (z + l)) = w i _ (e z) := by grind [atGeneric]) : ∃ G ∈ (B + -B').thetaSpace (χ * χ'⁻¹), ∀ i
  a z, θ z i ≠ 0 → θ' z a ≠ 0 → w (i, a) _ (e z) = G z * θ' z a / θ z i := by
  choose p hp using (exists_landsIn _ <| e ·)
  use! fun z ↦ w (p z) _ (e z) * θ z (p z).1 / θ' z (p z).2, fun z ↦ (he z (hw.1 _)
    (hp z)).elim fun a b ↦ ((b.differentiableAt.mul ((h.3 (p z).1).1 z)).mul (((h'.3 (p z).2).1
    z).inv ?_)).congr_of_eventuallyEq (a.mono ?_) <;> cases_type* HasThetaCoords <;>
    simp [thetaSpace, add_div, exp_add, exp_neg, neg_div, field] at * <;> grind

/-- Let N, M have theta coordinates θ, θ' of types (B, χ), (B', χ') for a full lattice L along a
holomorphic L-periodic e, and w trivialise N ⊗ M⁻¹. Then Riemann forms agree, χ = χ' on L,
and w_{ia}(e z) = c·exp((B(z,z) − B'(z,z))/2)·θ'_a(z)/θ_i(z) where both are non-zero, c
constant. -/
lemma riemannForm_eq_of_isFrame [IsFullRankLattice L] {w} (r : (N.mul M.inv).IsFrame w) (o : ∀ z,
  HolomorphicAt e z := by intro; apply (Uniformisation.immersive ..).1) (k : ∀ l ∈ L, ∀ z,
  e (z + l) = e z := by grind [atGeneric]) : B.riemannForm = B'.riemannForm ∧ (∀ l ∈ L, χ l =
  χ' l) ∧ ∃ c, ∀ i a z, θ z i ≠ 0 → θ' z a ≠ 0 → w (i, a) _ (e z) = c * exp ((B z z - B' z z) / 2) *
  θ' z a / θ z i := (h.exists_theta_of_isSection h' r.1 o).elim fun G H ↦ .imp_right
  (.imp_right (⟨G 0, ·⟩)) (by grind [by simpa using ((h.2.add h'.2.neg).eq_exp_of_ne_zero H.1 fun z
  ↦ by grind [(N.mul M.inv).exists_landsIn (e z), HasThetaCoords, landsIn_inf, mul_opens, inv_opens,
  isUnit_iff_ne_zero])])
end HasThetaCoords
end

section
/-! Part of: Theta group of an ample line bundle: span of sections, K(L), symmetric theta structures
(known result; see Lib.Shimura.ThetaGroup.RigidFibres).

Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number (known
result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Sections over a valuation ring as theta functions; lifted translations, commutators,
orbit lattices. -/


open CategoryTheory AlgebraicGeometry Over ValuativeArc Function IsSchemeTheoreticallyDominant
variable {V ι κ : Type} [FinComplexSpace V] {O} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

/-- Let A be a smooth proper scheme over a valuation ring O with fraction field ℂ, and s a family
exhausting its sections. Then A is reduced and the complex points of the s(z) are dense in A. -/
lemma isSeparatingFamily_atGeneric [Smooth A.hom] [IsProper A.hom] {Z s} (h : @Surjective Z (_ ⟶ A)
  s) : IsSeparatingFamily (atGeneric s) := ⟨isReduced (Limits.pullback.fst A.3 genericPt),
  .of_fibres (eq_const_of_subsingleton ‹ValuativeArc O›.genericPt _ ▸ genericPt.denseRange) _ fun _
  y _ ↦ (bijective_restrict_genericPt.2.comp h (homMk y)).rec (⟨·, congr($(·).1)⟩)⟩

lemma HasThetaCoords.holomorphicAt [Finite κ] {Λ s L B χ θ} (h :
  @HasThetaCoords _ κ V _ Λ (atGeneric s) L B χ θ)
  (hL : L.IsProjEmbedding A.hom) z : HolomorphicAt (atGeneric s) z := .of_isHomogCoords hL
  (analyticAt_of_eventually_differentiable <| .of_forall <| h.3 · |>.1) (.of_forall h.4)

variable [IsAbelianScheme A] {L : LineBundle _ κ} (u : Uniformisation A V) {B χ θ} (h :
  HasThetaCoords u.L (atGeneric u.expMap) L B χ θ)

/-- For an abelian scheme A over O, a valuation ring with fraction field ℂ, uniformised by u with
theta coordinates θ_i for L,
r ↦ θ_i·r_i embeds H⁰(L) O-linearly into functions on V, sending coordinates to the θ_i and lifts of
translation by u.expMap a to multiples of `RealComplexForm.thetaShift` a. -/
lemma exists_theta_evaluation {Λ s B} (h : HasThetaCoords Λ (atGeneric s) L B χ θ) : ∃ T :
  _ →ₗ[O] _, (∀ r g, T r = g ↔ ∀ i z, θ z i ≠ 0 → r.1 i _ (atGeneric s z) = g z / θ z i) ∧ (∀ i, T
  (coordSection h.1 i) = (θ · i)) ∧ ∀ u : Uniformisation A V, Λ = u.L → s = u.expMap → Injective T ∧
  ∀ a Φ, IsTranslationLift L (s a) Φ → ∃ c : ℂ, ∀ r, T (Φ r) = c • B.thetaShift a (T r) := by
  choose p n using (h.4 · |>.ne_zero)
  have := (h.4 · ·)
  let T : L.H0 O →ₗ[O] _ := .pi fun z ↦ θ z (p z) • ⟨⟨(·.1 (p z) _ (atGeneric s z)), by simp⟩,
    by simp [H0_smul, atGeneric, ValuativeArc.genericPt_eq, Algebra.smul_def]⟩
  exact have E r g := ⟨(· ▸ fun i z _ ↦ by simp [T, r.2.1.2 i (p z), field, *]), by simp_all [T,
      funext_iff, mul_div_cancel₀]⟩; ⟨T, E, by simp +contextual [*, coordSection, field], by
    rintro u rfl rfl; use fun s r _ ↦ H0_ext ((isSeparatingFamily_atGeneric
      u.4).pointFn_ext · · (by simp +contextual [(E ..).1 rfl, *])), fun a Φ ⟨w, b, e⟩ ↦
      (h.riemannForm_eq_of_isFrame (h.pull_translate (u.atGeneric_add a)) b).2.2.imp fun c K s ↦
    by ext z; simp [e _ _ (p (z + a)), *, ← u.atGeneric_add, thetaShift_apply, T, field]⟩

include h

/-- Weil pairing: let L have theta coordinates for B, and let Φ, Ψ lift to L^m the translations
by the images of a, b. Then ΦΨ = c·ΨΦ on all coordinates if and only if c = exp(2πi m
E(a,b)), E the Riemann form of B. -/
lemma lift_commutator_iff_weil_pairing {m a b c Φ Ψ} (p : IsTranslationLift (L.pow m) (u.expMap a)
  Φ) (q : IsTranslationLift _ (u.expMap b) Ψ) : (∀ l i, Φ (Ψ (coordSection
  l i)) = c • Ψ (Φ (coordSection l i))) ↔ algebraMap O ℂ c = (m • B).riemannPhase a b := by
  have ⟨T, _, G, K⟩ := exists_theta_evaluation (h.pow m)
  choose I _ e using K u rfl rfl
  suffices ∀ s, T (Φ (Ψ s)) = _ • T _ from ⟨fun E ↦ smul_left_injective ℂ (((I.comp (q.mul
    p).injective).ne_iff' (by simp)).2 (ne_zero_of_map ((G _).trans_ne (ne_iff.2 ⟨0, ((h.pow m).4
    0).ne_zero.choose_spec⟩)))) (.trans (by aesop) (this _)), (by simp [← I.eq_iff, this, ← ·])⟩
  simp [e a, e b, *, (h.pow m).2.thetaShift_comm a, funext_iff, field]

/-- Let N, an O-module of sections containing the coordinates, be stable under lifts of
translations by Λ^∨; nΛ^∨ ⊂ Λ, n a unit, B positive. Finitely many theta functions f_j, not
all zero, have multiples γf_j in N, γ ≠ 0, not all vanishing on any Λ^∨-orbit of a
field-valued point. -/
lemma exists_sections_of_translation_stable [Finite κ] [IsPosRiemann B] {n : ℕ} (hn :
  IsUnit (n : O)) {N : Submodule O _} (H : ∀ a ∈ B.dualLattice, n • a ∈ u.L ∧ ∃ Φ,
  IsTranslationLift L (u.expMap a) Φ ∧ N ≤ N.comap Φ) (hN : ∀ k, coordSection h.1 k ∈ N)
  {f : ι → _} [Finite ι] (hf : ∀ j, f j ∈ B.thetaSpace χ) i (f0 : f i ≠ 0) : ∃ γ ≠ 0, ∃ r : ι → N,
  (∀ j i z, θ z i ≠ 0 → (r j).1.1 i _ (atGeneric u.expMap z) = γ * f j z / θ z i) ∧ ∀ K [Field K] t,
  ¬∀ a ∈ B.dualLattice, ∀ j i, (r j).1.1 i ⟨K⟩ (t ≫ (translation (u.expMap a)).left) = 0 := by
  obtain ⟨⟨Q, E, G, K⟩, p, o⟩ := exists_theta_evaluation h, L.exists_landsIn (u.expMap 0).1
  obtain ⟨⟨J, K⟩, y⟩ := K u rfl rfl, ((h.4 ..).1.1 (o.comp _)).ne_zero
  choose! l Φ hΦ s using H
  choose! c hc using (K _ _ <| hΦ · ·)
  peel h.2.exists_proportional_orbit_lattice (⟨_, hf ·⟩) (⟨_, h.3 ·⟩) i p c hn l (by simpa)
    (y congr($(·).1 _)) fun a n ↦ ((hΦ a n).mul (hΦ _ (neg_mem n))).elim fun _ ⟨b, e⟩ ↦
    ⟨(b.2 (p, p) _ _ (by simpa)).unit, by simpa [↓G, ↓hc, *, h.2.thetaShift_thetaShift,
    ValuativeArc.genericPt_eq, field, coordSection, b.1.1 _ _, L.5, o.comp, atGeneric, -map_zero]
    using (e (coordSection h.1 p) p p _ _ · · ▸ (E (Φ a _) _).1 rfl p _ y :)⟩ with γ _ H
  replace H N := by
    simpa +contextual [E _ (γ • _), ← G, ← hc, J.eq_iff, -Subtype.exists,
      -Subtype.forall] using H (.map Q N)
  choose r m e using (H N s).1 hN
  use (⟨_, m ·⟩), e, fun K _ t Z ↦ (L.exists_landsIn t).elim fun i o ↦ by simpa [coordSection, L.5,
    o] using ((H ⟨⟨⟨{r | ∀ a ∈ _, ∀ i, r.1 i _ (t ≫ (translation (u.expMap a)).1) = 0}, by aesop⟩,
         by simp⟩, by grind [H0_smul]⟩ fun z e r a w k i ↦ by_cases ((hΦ z e).choose_spec.2 _
    _ _ _ _ · (L.exists_landsIn _).choose_spec |>.trans (by simpa [← comp_left, add_assoc] using
    (Or.inr (a _ (add_mem k e) _)))) ((Φ z r).2.2 i _ _)).2 (⟨_, (Z · · _), e ·⟩) i 0 · i)
end
