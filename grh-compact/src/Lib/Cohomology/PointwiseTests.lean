import Lib.Cohomology.ProperSchemes
import Lib.Cohomology.LineChernClass

section
/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Cohomology invariant under algebraically closed field extension; classes detected at
points. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory RingHom CommRingCat Ideal HV Subfunctor IsLocalRing Algebra PrimeSpectrum Set
variable {ℓ n W} [ThePrime ℓ] {R S T : CommRingCat} {s : W ⟶ reprBy R} (h : IsProperOver s) (u :
  IsUnit (ℓ : R))

lemma HV.map_eq_zero_of_factors {Λ X Z v v' x w} (e : w ≫ v = v') :
    @map Λ W X v n x = 0 → @map _ Z _ v' n x = 0 := by simp_all [← e, map_comp]

include h u

/-- Let W be proper over R, ℓ a prime invertible in R, A an absolutely integrally closed
valuation ring over R with residue field k. The restriction H^n(W_A, ℤ/ℓ) → H^n(W_k, ℤ/ℓ) is
injective. -/
lemma IsProperOver.injective_map_residue {A} [CommRing A] [IsAICLocal A] [PreValuationRing A] {a} :
  (⇑(map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom (residue A)) (a := a) rfl) n)).Injective := .of_ker
  _ fun _ ↦ (map_eq_zero_iff _ ((h.baseChange a).proper_base_change (by simpa using u.map a.1)
  n).1).1 ∘ map_eq_zero_of_factors (w := ⟨fun _ ↦ ↾fun y ↦ ⟨(_, ⟨ofHom (Ideal.Quotient.lift
  _ _ y.2)⟩), y.1.2⟩, by intros; ext; exact baseChangeOf.ext rfl (Quot.ind (by tauto))⟩) rfl

/-- Invariance under extension of algebraically closed fields: for W proper (`IsProperOver`)
over R, ℓ a prime invertible in R, and S → T algebraically closed fields over R, the map W_T
→ W_S induces bijections on all cohomology groups with coefficients ℤ/ℓ.

Known result: Proper base change; invariance under extension of algebraically closed fields. -/
lemma IsProperOver.isCohomEquiv_field_extension {a b} {φ : S ⟶ T} (e : a ≫ φ = b) (hS :
  IsField S) (hT : IsField T) (iS : IsAIC S) (iT : IsAIC T) :
  Components ⟨ZMod ℓ⟩ (baseChangeTransition s _ e) := e.rec fun n ↦ by
  algebraize [φ.1]; let := hS.toField; let := hT.toField
  rcases iS.isAlgClosed, iT.isAlgClosed; have β (t : Finset T) := (nullstellensatz_exists_le_ker
    (f := .adjoin_of_finite (R := S) t.finite_toSet) bot_ne_top).choose
  let b t : fibreProd s (reprMap a) ⟶ _ :=
    (baseChangeFunctor s).map ((Under.map a).map (β t).toUnder).op
  refine (h.isCohomContinuous.isFilteredColimit_adjoin s T a n).imp (fun p ↦ .of_ker _ fun x g ↦
    (p ∅ _ ((map_comp _ (baseChangeTransition s _ rfl) _).symm.trans g)).elim fun t ⟨_,
    e⟩ ↦ by simpa [HV.map] using! map_eq_zero_of_factors (by ext; exact baseChangeOf.ext rfl (
    congrArg _ <| (β t).2 ·) : b t ≫ _ = 𝟙 _) ((map_comp ..).trans e)) (· · |>.elim fun t ⟨x, e⟩ ↦
    .elim (image_subset_nonunits_valuationSubring (A := (adjoin ..).toSubring) _
    (ker_ne_top (β t))) fun V W ↦ let i := ofHom (R := adjoin S _) (Subring.inclusion W.1)
    ⟨map _ (b t) n x, e ▸ (map_comp (baseChangeTransition s (ofHom V.subtype) rfl)
      (baseChangeTransition s (ofHom (algebraMap S _) ≫ i) rfl) _).trans ((congrArg _
      (h.injective_map_residue u ?_)).trans (map_comp _ (baseChangeTransition s i rfl) x).symm)⟩)
  repeat erw [← map_comp]
  congr 2 with; exact baseChangeOf.ext rfl fun _ ↦ congrArg _ (Ideal.Quotient.eq.2 (
    V.coe_mem_nonunits_iff.1 (W.2 ⟨_, (sub_mem_ker_iff _).2 ((β t).2 _), rfl⟩)))

/-- Let W be proper over R, ℓ invertible in R, T a test R-algebra, x ∈ H^n(W_T, ℤ/ℓ). The primes
P of T with x zero on the fibre over κ(P) form an open set; if it is all of Spec T, then x =
0. -/
lemma IsProperOver.isOpen_zero_set_and_eq_zero (T :
  TestRing) {a x} : let z := {P : PrimeSpectrum T.1 | map ⟨ZMod ℓ⟩ (baseChangeTransition s (ofHom
    (algebraMap T.1 P.1.ResidueField)) (a := a) rfl) n x = 0}; IsOpen z ∧ (z = univ → x = 0) := by
  intro z; let q := fibreProd.snd s (reprMap a)
  have v {I b} (k : ∀ c ∈ I, _) : unitPoints q {b} ≤ unitPoints q I :=
    fun _ _ h c i ↦ isUnit_of_dvd_unit (map_dvd _ (k c i)) (h b rfl)
  have w {I b} k := map_eq_zero_of_factors (x := x) (homOfLe_ι (@v I b k))
  let J : Ideal _ :=
    ⟨⟨⟨{b | map _ (unitPoints q {b}).ι n x = 0}, @fun b c i j ↦ let ⟨e, o, _⟩ := T.2.2 b c
    have l a {d} := @v {d} ((1 - a) * d) (by simp)
    (map_eq_zero_iff _ ((mayer_vietoris_injective (l e) (l _) (.of_preimage_le
      (hasPartitions_locConstCoeff.isCohomDense_partition _ o) (by exact .mk fun _ ↦
      ↾(⟨⟨·.1.1.2.1⟩⟩)) fun _ y ↦ by apply Or.imp <;> rintro k _ rfl <;> erw [map_mul, map_sub, k]
      <;> simpa using (y.2 _ rfl)) n rfl).2 fun _ k ↦ by
      simpa [*, ← map_mul, mul_mul_mul_comm] using (k.2.1 _ rfl).mul (k.2.2 _ rfl)).1).1
      (by ext <;> apply (H.map_map ..).trans <;> [apply w _ j; apply w _ i] <;> simp [*,
      mul_add, dvd_add])⟩, hasPartitions_locConstCoeff.eq_zero_of_zero_ring
    (by simp [unitPoints]) ..⟩, fun _ _ ↦ w (by simp)⟩
  rw [← (Set.ext fun P ↦ not_subset.trans ⟨fun ⟨b, k, l⟩ ↦ map_eq_zero_of_factors (lift_ι _ (by
    rintro _ _ ⟨y, rfl⟩ _ rfl; exact (Ne.isUnit (algebraMap_residueField_eq_zero.1.mt l)).map
      y.1.2.1.1)) k, fun e ↦ ?_⟩ : (zeroLocus J)ᶜ = z)]
  simpa [HV.map, eq_top_iff_one, isClosed_zeroLocus, zeroLocus_empty_iff_eq_top] using!
    map_eq_zero_of_factors (lift_ι (𝟙 _) fun _ ↦ by simp [unitPoints])
  have ⟨_, _, _⟩ := T.2.exists_valuationSubring_atPrime P; let M := P.1.primeCompl
  exact (((h.baseChange a).isCohomContinuous.isFilteredColimit_antitoneFamily (V := unitPoints q)
    (by tauto) (fun I ↦ isRelAffine_of_zero_unit_locus (⟨∅, baseRingMap q · '' I, by simp
    [unitPoints]⟩)) (D := (monotone_image.comp Finset.coeEmb.monotone).functor) (m :=
    ⟨M, .mk fun _ ↦ ⟨⟨image_val_subset⟩⟩⟩) (· {⟨·, ·⟩} _ (by simp))).1 ∅ _
    ((map_comp _ (ι _) _).symm.trans (map_eq_zero_of_factors ((isPullback_fibreProd.of_bot (v₁₁ :=
    baseChangeTransition s (ofHom (algebraMap T.1 (Localization M))) rfl) (v₁₂ := reprMap _) rfl
    isPullback_fibreProd).lift_snd _ (ι (.preimage _ q)) ((Category.assoc ..).trans ((fromPreimage
    .. ≫ homOfLe (unitPoints_le_range_reprMap _ M)) ≫= IsIso.inv_hom_id_assoc (toRange
    (uliftCoyoneda.map _)) (ι _)))) (h.injective_map_residue u (by simpa [← map_comp]))))).elim
    fun t ⟨_, e⟩ ↦ ⟨_, w (forall_mem_image.2 fun
    _ ↦ t.dvd_prod_of_mem _) ((map_comp ..).trans e :), M.prod_mem fun c _ ↦ c.2⟩
end

section
/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Proper base change with supports: classes detected on geometric points, field-extension
invariance. -/

open AddEquiv CategoryTheory CommRingCat Function Ideal projLine MonoidalCategory

lemma isProperOver_projLinePow ι :
  IsProperOver ((zIsInitial.op.isTerminalObj uliftCoyoneda _).from (projLinePow ι)) := ⟨fun _ x y ↦
  ⟨⨆ i, span {HSub.hSub.uncurry (unimodularRow (x i) * (unimodularRow (y i)).swap)}, fun _ f ↦
  funext_iff.trans ((forall_congr' fun i ↦ ULift.up_inj.trans ((x i).1.out_eq ▸ (y i).1.out_eq ▸ by
  simp [Quotient.eq, projLineSetoid, unimodularRow])).trans iSup_le_iff.symm)⟩,
  of (FreeCommRing _), fun i ↦ ⟨⟦⟨.of (Sum.inl i), .of (.inr i)⟩⟧⟩, fun O x _ ↦ by
  choose u v e using fun i ↦ (x i).1.ind (motive := (∃ u v : O, ⟦⟨u, v⟩⟧ = ·)) fun a ↦ by
    obtain ⟨c, _⟩ | ⟨c, _⟩ := le_total (O.valuation a.2) ⟦_⟧ <;>
      [use 0, c; use c - 1, 1] <;> simp [Quotient.eq, projLineSetoid] <;> tauto
  use ofHom (FreeCommRing.lift (Sum.elim u v)), congr((⟨$(e · ▸ by simp)⟩))⟩

variable {A} [CommRing A] {D} [Category D] (g : D ⥤ TestOver A) {X} (I :
  IdealFamily (elementsProj (X ⊗ reprBy (of A)))) {ℓ : ℕ}

/-- For a test c over A and a prime P of c, the map of tests over A from c to its residue field
at P, as an object under c. -/
def residueTest (c : TestOver A) (P : PrimeSpectrum c.1) : Under c :=
  .mk (Y := ⟨.of A P.1.ResidueField, have := (c.2.exists_valuationSubring_atPrime
    P).1; isTest_of_preValuationRing⟩) ⟨CommAlg.homOfRingHom (algebraMap ..) (by tauto)⟩

/-- Each class in Extⁿ(ℤ[Hom(c, g(−))], F), c a test, vanishes at the residue fields of an open
set of primes, all primes only if zero; and maps of field tests induce bijections on these
groups. -/
def IsDetectedAtPoints F := (∀ c n x, let z := {P | H.map F (freeAb.map
    (g.whiskerLeft (reprMap (residueTest c P).hom))) n x = 0}; IsOpen z ∧ (z = .univ → x = 0)) ∧ ∀ V
  k (φ : V ⟶ k), IsField V.1 → IsField k.1 → IsCohomEquiv F (freeAb.map (g.whiskerLeft (reprMap φ)))

/-- From ideals I indexed by the points of X × Spec A in rings, the family assigning to a test B
over A and x ∈ X(B) the ideal of I at x and the structure map A → B. -/
def IdealFamily.pullToTests : IdealFamily (ringOf (testOfPoint A X)) :=
  I.whisker (sectionLift (ringOf (testOfPoint A X))
  ⟨(·.2, ⟨ofHom _⟩), fun f ↦ congr(⟨$(f.2), ⟨ofHom $(f.1.1.1.comp_algebraMap)⟩⟩)⟩)

/-- Proper base change: ℓ invertible in A, X proper over ℤ. On pairs (test over A, point of X),
if β from locally constant ℤ/ℓ-valued functions to F is bijective where I vanishes, and this
locus is dense for F, then F satisfies `IsDetectedAtPoints`. -/
lemma IdealFamily.isDetectedAtPoints_of_proper (I : IdealFamily _) [InvertsPrime A ℓ] {p} (hX :
  @IsProperOver X ⟨ℤ⟩ p) {F} (β : locConstAlong (testOfPoint A X) ⟶ F) (hβ : ∀ a,
  I.pullToTests.I a = ⊥ → Bijective (β a)) (hΓ : IsCohomDense F I.pullToTests.botLocus) :
  IsDetectedAtPoints (testOfPoint A X) F := let W : Subfunctor (baseChangeOf _ (zIsInitial.to _)) :=
    ⟨_, fun f x ↦ @I.botLocus.map ⟨x.1⟩ _ ⟨f, rfl⟩ ⟨⟩⟩
  have ⟨h, T, a, ha⟩ := hX.baseChange _
  let s := W.ι ≫ fibreProd.snd ..
  have k {C} f := @I.2 ⟨a.1⟩ (.mk (obj := C) ((baseChangeOf ..).map f a).1) ⟨f, rfl⟩
  have hs : IsProperOver s := ⟨(by convert h · ·.1 ·.1; exact Subtype.ext_iff), _, ⟨_, (k (ofHom
    _)).symm.trans (map_quotient_self _)⟩, fun O z i ↦ (ha O z.1 i).elim fun u e ↦ ⟨ofHom
    (Ideal.Quotient.lift _ _ fun _ b ↦ Subtype.ext (((k _).trans (e ▸ z.2)).le (le_comap_map b))),
    Subtype.ext ((Functor.map_comp_apply ..).symm.trans e)⟩⟩
  let κ : Comparison (locConstCoeff _) F := ⟨_ ⋙ TestOver.toTest A, β⟩
  let u c : (I.pullToTests.botLocus.preimage (toUnit (testOfPoint A X ⋙ reprBy c))).toFunctor ⟶ κ.φ
    ⋙ testIncl ⋙ baseChangeOf s (ofHom _) := ⟨fun _ ↦ ↾fun x ↦ ⟨(⟨⟨_, congr(⟨$(zIsInitial.hom_ext
    ..)⟩)⟩, x.2⟩, ⟨_⟩), congr(⟨ofHom $(x.1.1.1.1.comp_algebraMap.symm)⟩)⟩, fun _ _ f ↦
    .symm congr(↾fun _ ↦ ⟨(⟨$(baseChangeOf.ext f.2 f.1.1.1.2), _⟩, _), _⟩)⟩
  have t c := Comparison.HasUnivPoints.isBijective (u :=
    u c) fun T y ↦ let : Algebra A T.1 := y.1.1.1.1.2.1.1.toAlgebra
    ⟨.mk (obj := ⟨_, T.2⟩) _, ⟨⟨⟨CommAlgCat.ofHom ⟨_, (congr($(y.2).1.1 ·).symm)⟩⟩⟩, y.1.1.2⟩,
      𝟙 T, .symm
      (Functor.map_id_apply ..), fun _ _ f k ↦ ⟨⟨⟨CommAlg.homOfRingHom _ (congr($k.1.1.1.1.2.1.1
      ·).symm)⟩, congr($k.1.1.1.1.1).symm⟩, ⟨congr(⟨⟨⟨CommAlg.homOfRingHom $k.symm.1.2.1.1 _⟩⟩, _⟩),
      rfl⟩, fun _ e ↦ e.2 ▸ rfl⟩, .comp (hβ _ y.1.1.2) bijective_id⟩
  let e {c n} := (ofBijective _ ((hΓ.preimage _).isCohomEquiv n)).trans (ofBijective _ (t c n)).symm
  have w {c k} φ n x : HV.map _ (baseChangeTransition s ((ringOf (𝟭 _)).map φ) (hom_ext
    φ.1.1.comp_algebraMap)) n _ = e _ := (t k n).1 (.trans (κ.map_pull_eq_pull_map (a :=
    freeAbMap (u c)) (a' := freeAb.map (Subfunctor.fromPreimage _
    (Functor.whiskerLeft _ (reprMap φ)))) ..).symm (by simp [e, H.map_map, -Functor.map_comp]; rfl))
  ⟨fun c n x ↦ by simpa only [← e.map_eq_zero_iff, ← w] using!
    hs.isOpen_zero_set_and_eq_zero InvertsPrime.isUnit_prime ⟨of _, c.2⟩, fun V k φ a b n ↦
    (Comparison.bijective_iff_of_comm_sq (w φ n) e.bijective e.bijective).2
    (hs.isCohomEquiv_field_extension InvertsPrime.isUnit_prime _ a b V.2.1 k.2.1 n)⟩
end
