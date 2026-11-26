import Lib.Cohomology.CechDescent
import New.Weil.TestRings
import Lib.Cohomology.BijectiveComparisons

section
/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Commutation of cohomology with filtered limits descends along Čech covers. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

noncomputable section


open CategoryTheory Limits Function Functor AddCommGrpCat MorphismProperty colimit Arrow
  LongExactSeq H Comparison
variable {C} [Category C] {F : AbFunctor C} {J} [SmallCategory.{0} J] [IsFiltered J]
  {D : Jᵒᵖ ⥤ C ⥤ Type 1} {T} [Category* T]

/-- A cocone of abelian groups is a filtered colimit elementwise: an element mapping to 0 in the
vertex dies at a later stage, and every element of the vertex comes from some stage. -/
def IsFilteredColimit {X : J ⥤ Ab} (c : Cocone X) :=
  (∀ j x, c.ι j x = 0 → ∃ i f, @X.map j i f x = 0) ∧ ∀ y : c.pt, ∃ j x, c.ι j x = y

/-- The contravariant functor sending Φ: T → (functors from C to abelian groups) to the
contravariant functor t ↦ Ext^n(Φ(t),F) from T to abelian groups. -/
abbrev cohFunctor F n := opHom T (AbFunctor C) ⋙ (whiskeringRight ..) ⟨_, (ofHom <| map F ·.unop n),
  by aesop, fun _ _ ↦ ext (map_comp _ _)⟩

/-- For a cone over a cofiltered system D_j and a level r, the condition `BijectiveUpTo` at
level r for the canonical maps colim_j H^n(D_j,F) → H^n(vertex,F). -/
def ContinuousUpTo F (c : Cone D) := BijectiveUpTo fun n ↦
  desc _ ((cohFunctor F n ⟨freeAb⟩).mapCocone (coconeRightOpOfCone c))

attribute [local instance] preservesSmallestFilteredColimits_of_preservesFilteredColimits

/-- For a diagram X of abelian groups over a small filtered category, a cocone c satisfies the
elementwise conditions `IsFilteredColimit` if and only if the induced map from the colimit of X
to the vertex of c is bijective. -/
lemma isFilteredColimit_iff_bijective {X : J ⥤ Ab.{2}} {c} : IsFilteredColimit c ↔
  Bijective (desc X c) := by
  have z := by simpa using Concrete.from_union_surjective_of_isColimit X (isColimit _)
  simp [IsFilteredColimit, Bijective, injective_iff_map_eq_zero, Surjective, z.forall, z.exists,
    Sigma.forall, by simpa using ((isColimit X).eq_iff' (i := ·) · 0)]

/-- Take a cone over a cofiltered system of covers E_j → Y_j whose vertex is a cover. If
`ContinuousUpTo` holds at level r+1 for the E_j and at level r for all fibre powers with at least
one factor, it holds at level r+1 for the Y_j. -/
lemma ContinuousUpTo.of_cech {A : Jᵒᵖ ⥤ _} (a : Cone A) (hp : ∀ j, IsCover F (A j).hom) (hq :
  IsCover F a.pt.hom) {r} (h₀ : ContinuousUpTo F (leftFunc.mapCone a) r) (h : ∀ m,
  ContinuousUpTo F ((cechFunctor m).mapCone a) (r - 1)) :
  ContinuousUpTo F (rightFunc.mapCone a) r := let G := (whiskeringLeft ..) A.rightOp ⋙ colim
  let η : G ⟶ (evaluation ..) _ :=
    ⟨(desc _ <| ·.mapCocone (coconeRightOpOfCone a)), by simp [G, colimit.hom_ext_iff]⟩
  let k := ((toArrowFunctor ⋙ whiskeringLeft ..).flip.op ⋙ cohFunctor F ·)
  (BijectiveUpTo.congr (fun n ↦
    (colim.mapIso (isoOfAppBijective _ (hp ⟨·⟩ n))).addCommGroupIsoToAddEquiv.bijective)
    hq fun n x ↦ (η.naturality_apply ((k n).map ⟨freeAb.map (Subfunctor.range leftToRight).ι⟩)
    x).symm).2 (cech_descent_step _ (f := fun N n ↦ η (k n ⟨N⟩)) ⟨fun {S _} x ↦ by
    let L {t} := contravariant (x.map_of_exact ((whiskeringLeft ..) (toArrowFunctor t))) F
    refine LongExactSeq.Hom.four_lemma (by constructor <;> intro <;> apply η.naturality_apply :
      Hom ⟨(k · ⋙ G |>.map S.g.op |>.hom), (k · ⋙ G |>.map S.f.op |>.hom),
      fun n ↦ (G.map ⟨fun t ↦ @ofHom (L.C n) (L.A _) _ _ (L.δ n), fun _ _ f ↦ .symm (ext
      ?n)⟩).hom, (AddCommGrpCat.mono_iff_injective _).1 ((monomorphisms _).colimMap _ fun _ ↦
      ConcreteCategory.mono_of_injective _ L.injective_f), ?_, ?_, ?_⟩ L ..)
    case n => simpa only [id_pull] using! (pull_hom_contravariant (x.map_of_exact _) _ (.id F)
      (S.mapNatTrans ((whiskeringLeft ..).map _))).comm_delta n
    all_goals exact fun _ ↦ exact_of_shortComplex_exact ((exact_of_app fun _ ↦ by
      apply_rules [L.exact_f_g, L.exact_g_delta, L.exact_delta_f]).2.map G)⟩ h₀ h)
end
end

section
/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: Functorial envelope: maps from given rings to tests factor through a test ring. -/

open CategoryTheory Classical CommRingCat MvPolynomial Ideal.Quotient
variable (B) {W V J : Type} [CommRing B] [CommRing W] [CommRing V] (g : W →+* V)

namespace Envelope

/-- x solves equation o with coefficients a: x idempotent, a₀ ∣ xa₁, a₁ ∣ (1 − x)a₀ (o = 0); a₀ⁿ
∣ a_{n+1} − x for all n (o = 1); Σ_{k<n} a_k x^k = 0 (o = n + 2). -/
def IsSolution (a : ℕ → V) x | 0 => IsIdempotentElem x ∧ a 0 ∣ x * a 1 ∧ a 1 ∣ (1 - x) * a 0
                             | 1 => ∀ n, a 0 ^ n ∣ a (n + 1) - x | n + 2 => ∑ k ∈ .range n,
                               a k * x ^ k = 0

/-- Formal names for solutions over B: a term is an equation number o with a sequence of
coefficients, each a polynomial over B in finitely many earlier terms. -/
inductive SolutionName
  | op (o : ℕ) (n : ℕ → ℕ) (P : ∀ k, MvPolynomial (Fin (n k)) B) (t : ∀ k, Fin (n k) → SolutionName)

/-- g: W → V is injective, and every equation `Envelope.IsSolution` with coefficients in g(W)
that has a solution in V has one in g(W). -/
def IsSolutionClosed := (⇑g).Injective ∧ ∀ o a, (∃ x, IsSolution (g ∘ a) x o) → ∃ x,
  IsSolution (g ∘ a) (g x) o

variable {B g}

/-- Every ring map φ: B → V extends to a ring map g from the polynomial ring
over B such that the induced injection of its quotient by ker g into V satisfies the closure
condition `Envelope.IsSolutionClosed`. -/
lemma exists_isSolutionClosed φ : ∃ g : MvPolynomial (SolutionName B) B →+* V, g.comp C = φ ∧
  IsSolutionClosed g.kerLift := ⟨eval₂Hom φ
  (·.rec fun o _ P _ v ↦ epsilon (IsSolution (P · |>.eval₂ φ (v _)) · o)), by simp,
  RingHom.kerLift_injective _, fun _ ↦ mk_surjective.comp_left.forall.2 fun a h ↦ by
  choose n t _ P e using (a · |>.exists_fin_rename)
  exact ⟨mk _ (X (.op ..)), by simpa [e, eval₂_rename, Function.comp_def] using epsilon_spec h⟩⟩

lemma IsSolutionClosed.map_dvd_iff (h : IsSolutionClosed g) {x y} : g x ∣ g y ↔ x ∣ y :=
  ⟨by simpa [← h.1.eq_iff, dvd_def, IsSolution,
  Finset.sum_range, neg_add_eq_zero] using (h.2 4 ([-y].getD · x)), map_dvd g⟩

/-- If a ring map g: W → V satisfies the closure condition `Envelope.IsSolutionClosed` and V is a
test ring, then W is a test ring. -/
lemma IsSolutionClosed.isTest (h : IsSolutionClosed g) : IsTest V → IsTest W
  | ⟨a, c, _⟩ => ⟨⟨fun P m d ↦ by simpa [P.eval_eq_sum_range, ← h.1.eq_iff] using! (h.2 (_ + 3)
    _ (by simpa [P.eval₂_eq_sum_range] using! a.exists_eval₂_eq_zero g m d))⟩,
    fun x y ↦ by simpa [← h.map_dvd_iff, ← h.1.eq_iff, IsIdempotentElem] using!
    (h.2 0 ([x].getD · y) (c ..)), isReduced_of_injective g h.1⟩

/-- For any family of commutative rings R_o, there are an endofunctor E of commutative rings
with every E(A) a test ring and a natural map θ: A → E(A) such that every homomorphism from
an R_o to a test ring factors through θ at R_o. -/
lemma exists_functorial_test (R : J → _) : ∃ E, ∃ θ : 𝟭 CommRingCat ⟶ E, (∀ A, IsTest (E A)) ∧
  ∀ o (A : TestRing) φ, ∃ ψ : _ ⟶ A.1, θ (R o) ≫ ψ =
  φ := let e {S} := Pi.evalRingHom fun x : Σ q : {q : Σ o, Ideal
    (MvPolynomial (SolutionName (R o)) (R o)) // IsTest (_ ⧸ q.2)}, S ⟶ of (_ ⧸ q.1.2) ↦ _ ⧸ x.1.1.2
  ⟨.mk _ fun f ↦ ofHom (.pi (e ⟨_, f ≫ ·.2⟩)), .mk fun _ ↦ ofHom (.pi (·.2.1)),
        fun _ ↦ .pi (·.1.2), fun _ A φ ↦ (exists_isSolutionClosed φ.1).elim fun g h ↦
    ⟨ofHom (g.kerLift.comp (e ⟨⟨⟨_, _⟩, h.2.isTest A.2⟩, ofHom (algebraMap ..)⟩)), hom_ext h.1⟩⟩
end Envelope
end

section
/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Relatively representable (affine) maps of functors on rings: pullbacks, closed and open
loci. Tests are acyclic; tests and locally constant functions commute with filtered colimits. -/

open CategoryTheory CommRingCat IsLocalization Ideal Quotient
variable {X Y W V : PointFunctor} {p : X ⟶ Y} {u : W ⟶ Y} {q v R} (s : X ⟶ reprBy R) (I)

/-- The property of a map X → Y of set-valued functors on rings that its pull-back along every
point h_A → Y is representable, of the form h_B → h_A. -/
abbrev IsRelAffine : MorphismProperty PointFunctor := reprFunctor.relativelyRepresentable

lemma IsRelAffine.baseChange : IsRelAffine p → IsPullback v q p u → @IsRelAffine V W q :=
  flip IsRelAffine.of_isPullback

lemma IsRelAffine.comp : @IsRelAffine W X v → IsRelAffine p → IsRelAffine (v ≫ p) :=
  IsRelAffine.comp_mem v p

lemma unitPoints_le_range_reprMap L [CommRing L] [Algebra R L] M [IsLocalization (R := R) M L] :
  unitPoints (𝟙 _) M ≤ .range (reprMap (ofHom (algebraMap R L))) := fun _ _ _ ↦
  ⟨⟨_⟩, congr(⟨ofHom $(lift_comp (by simpa))⟩)⟩

lemma isRelAffine_of_zero_unit_locus {U} (h : ∀ {R} y, ∃ A N : Set _, ∀ B f, @Y.map R B f y ∈ U B ↔
  (∀ a ∈ A, f a = 0) ∧ ∀ a ∈ N, IsUnit (f a)) : IsRelAffine (Subfunctor.ι U) := fun _ ↦
  uliftCoyonedaEquiv.forall_congr_left.2 (h · |>.elim fun A ⟨N, h⟩ ↦ let L := Localization (.closure
    N); ⟨_, ⟨ofHom (algebraMap _ (_ ⧸ span (algebraMap _ L '' A)))⟩, pointMap ⟨_, (h ..).2
    ⟨fun _ _ ↦ eq_zero_iff_mem.2 (by aesop), (isUnit_comp _ _ ⟨·, Submonoid.subset_closure ·⟩)⟩⟩,
    isPullback_iff.2 ⟨fun _ _ ↦ (Y.map_comp_apply ..).symm, by
    rintro _ ⟨⟩ ⟨⟩ ⟨⟩; cases (h ..).1 ‹_›; obtain ⟨l, ⟨⟩⟩ := (unitPoints_le_range_reprMap L _ _
      (((IsUnit.submonoid _).comap _).closure_le.2 ‹_›)); exact ⟨⟨ofHom (lift _ _ ((RingHom.ker
      _).span_le.2 (by simpa)))⟩, ⟨rfl, SetCoe.ext (Y.map_comp_apply ..).symm⟩, fun ⟨_⟩ ⟨a, _⟩ ↦
      congrArg _ (hom_ext (ringHom_ext (ringHom_ext (.closure N) congr($a.1.1))))⟩⟩⟩)

lemma isRelAffine_zeroPoints : IsRelAffine (zeroPoints s I).ι :=
  isRelAffine_of_zero_unit_locus (⟨baseRingMap s · '' I, ∅, by simp [zeroPoints]⟩)

open Limits colimit Concrete Function Abelian.Ext LocallyConstant PrimeSpectrum Comparison ULift
  IsFiltered
variable {Λ : Ab} {J B B' T T'} (q : T ⟶ testIncl ⋙ reprBy B) {q' :
  T' ⟶ testIncl ⋙ reprBy B'} [SmallCategory J] [IsFiltered J] {L : J ⥤ CommRingCat}

lemma isFilteredColimit_locConstSpec {c : Cocone L} (s : ∀ y : c.pt, ∃ j x, c.ι j x = y) (h : ∀ j x,
  c.ι j x = 0 → ∃ i f, @L.map j i f x = 0) : IsFilteredColimit ((locConstSpec Λ).mapCocone c) :=
  ⟨fun j x l ↦ (isClopen_iff_zeroLocus.1 (x.2.isClopen_fiber 0)).elim fun e ⟨i,
  o⟩ ↦ by peel h _ e ((i.map _).eq_zero_of_isNilpotent (nilpotent_iff_mem_prime.2
  (o.le congr($l.1 ⟨·, ·⟩) rfl))) using LocallyConstant.ext fun _ ↦ o.ge (by aesop),
  fun y ↦ (locallyConstant_mem_of_indicator (fun a e k ↦ (s e).elim fun j ⟨d, r⟩ ↦ (h _ (d * d - d)
  (by aesop)).elim fun i ⟨f, _⟩ ↦ by simpa only [← r, ← c.w f] using ⟨_, ι_desc_apply
  ((locConstSpec Λ).mapCocone c) i (indicator (.const ..) (isClopen_iff.2 ⟨_, by aesop, rfl⟩))⟩) y :
  y ∈ (desc (C := Ab) ..).hom.range).elim (colimit_exists_rep _ · |>.elim (by aesop))⟩

/-- For q: T → h_B on test rings, the map from locally constant functions Spec B → Λ to Hⁿ(T,
Λ): pull-back along q for n = 0, zero for n > 0. -/
noncomputable def locConstClass : ∀ n, locConstSpec Λ B →+ H (freeAb T) (locConstCoeff Λ) n
  | 0 => .comp (.mk' mk₀ mk₀_add)
    ((Comparison.homOfValue ⟨testIncl, 𝟙 (_ ⋙ liftCoeff _)⟩ q).comp (.mk' _ (by tauto))) | _ => 0

/-- Property of q: T → h_B on tests: pull-back LC(Spec B, Λ) → H^0(T, Λ) is bijective and H^n(T,
Λ) = 0 for n > 0. -/
def IsAcyclicOver Λ := Injective (@locConstClass Λ B T q 0) ∧ ∀ n,
  Surjective (@locConstClass Λ B T q n)

variable {q}

lemma map_locConstClass {e f f'} (h : ∀ c x, (locConstSpec Λ).map (q c (e c x)).1 f = (locConstSpec
  Λ).map (q' c x).1 f') : ∀ n, .map _ (freeAb.map e) n (locConstClass q n f) = locConstClass q' n f'
  | 0 => (mk₀_comp_mk₀ ..).trans (congrArg _ (freeAb.hom_ext fun _ _ ↦ congr(⟨$(by tauto)⟩)))
  | _+1 => map_zero _

lemma bijective_const_of_isDomain {Λ} [IsDomain B] :
  Bijective (⟨.const _ ·⟩ : Λ → ULift.{1} (LocallyConstant
  (PrimeSpectrum B) Λ)) := ⟨fun _ _ ↦ (congr($(·).1 ⊥)), fun ⟨x⟩ ↦ x.eq_const ⊥ ▸ ⟨_, rfl⟩⟩

lemma IsAcyclicOver.isCohomEquiv (a : IsDomain B) (b : IsDomain B') u (h : IsAcyclicOver q Λ)
    (h' : IsAcyclicOver q' Λ) : IsCohomEquiv (locConstCoeff Λ) (@freeAb.map T' T u)
  | 0 => (bijective_iff_of_comm_sq (by exact fun _ ↦ map_locConstClass (by tauto) 0) (.comp ⟨h.1,
    h.2 0⟩ (down_bijective.comp bijective_const_of_isDomain)) (.comp ⟨h'.1,
    h'.2 0⟩ (down_bijective.comp bijective_const_of_isDomain))).1 bijective_id
  | _+1 => ⟨(h.2 _).forall₂.2 (by tauto), (h'.2 _).forall.2 fun _ ↦ ⟨_, map_zero _⟩⟩

/-- A filtered colimit of test rings is a test ring. -/
lemma IsTest.filtered_colimit (h : ∀ j, IsTest (L.obj j)) : IsTest ↑(colimit L) := by
  choose j _ hy using colimit_exists_rep L
  choose! z hz using fun s x _ ↦
    Set.mem_range.2 ⟨_, hy _ ▸ w_apply L (toSup (.image ..) ∅ (by aesop)) _⟩
  use ⟨fun P ↦ (h _).exists_root_of_coeffs_subset_range (by tauto)⟩, fun f g ↦ ((h _).2 (z _ f) (z
    {f, g} g)).imp' (ι L _) (by grind [IsIdempotentElem, → map_dvd (ι L _).hom]), fun x ⟨n, e⟩ ↦ ?_
  erw [← hy x, ← map_zero (ι L _).hom, ← map_pow, (isColimit L).eq_iff'] at *
  grind [(h _).3.1 _ ⟨n, _⟩]

seal Comparison.homOfValue

/-- If B is a test ring and q : T → h_B is bijective on points in every test ring, then H⁰(T, Λ)
is, via q, the group of locally constant functions Spec B → Λ, and Hⁿ(T, Λ) = 0 for n > 0. -/
lemma IsAcyclicOver.of_bijective (h : IsTest B) (b : ∀ {C}, Bijective (q C)) : IsAcyclicOver q Λ :=
  (isBijective_reprBy_iff.1
  (.precomp_of_bijective (isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful testIncl ⟨B,
  h⟩) bijective_id) q (Category.comp_id _) @b)).elim fun a b ↦
  ((mk₀_bijective ..).comp (a.comp up_bijective)).imp_right (Nat.rec · fun _ _ ↦ (⟨0, (b _).1 _ ·⟩))

/-- The functor restricting a set-valued functor on commutative rings to the full subcategory of
test rings, by precomposition with the inclusion. -/
abbrev onTests := restrictAlong (D := Type 1) testIncl

/-- If a test ring A is the filtered colimit, as a ring, of test rings A_j, then the
Λ-cohomology H^n(h_A) on test rings is the colimit of the H^n(h_{A_j}), for every n. -/
lemma continuousUpTo_locConstCoeff (h : ∀ j, IsTest (L j)) :
    ∀ r, ContinuousUpTo (locConstCoeff Λ) ((reprFunctor ⋙ onTests).mapCone (cocone L).op) r :=
  forall_bijective_iff_bijectiveUpTo.1 (isFilteredColimit_iff_bijective.1 ∘' by
  choose i s using (@IsAcyclicOver.of_bijective Λ · _ (𝟙 _) · bijective_id)
  rintro ⟨⟩ <;> simp [IsFilteredColimit, (s _ _ _).forall, (s _ _ _).exists, (i ..).eq_iff,
    ↓fun A B φ x ↦ @map_locConstClass Λ A B _ _ (𝟙 _) (𝟙 _) (mapOnTests (reprMap φ)) x
    ((locConstSpec _).map φ x) (by tauto),
    _root_.map_eq_zero_iff, locConstClass.eq_2, IsTest.filtered_colimit h, nonempty, *]
  exacts [isFilteredColimit_locConstSpec (colimit_exists_rep _) fun _ x ↦ by simpa using
    ((isColimit L).eq_iff' x 0).1, (⟨·, ⟨𝟙 _⟩⟩)])
end
