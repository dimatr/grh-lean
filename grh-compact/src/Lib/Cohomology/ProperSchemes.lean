import Lib.Cohomology.ValuativeDensity
import Lib.Cohomology.ReductionModP
import Lib.Shimura.ConstantFunctions

-- part: Lib.Cohomology.Etale.ProperFunctors
section
/-! Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Proper functors: fibre products, base change, dense images, cover by the space of
places. -/

namespace IsProperOver

open CategoryTheory CartesianMonoidalCategory CommRingCat Functor ResiduePlace Pi Limits
variable {Y Z D T s Λ c} (h : @IsProperOver Z D s)
include h

lemma isRelAffine_pointMap y : @IsRelAffine (reprBy T) Z (pointMap y) :=
  .of_diag (F := uliftCoyoneda) ((isRelAffine_of_zero_unit_locus fun _ ↦
  (h.1 ..).imp' _ fun _ H ↦ ⟨∅, fun _ _ ↦ (Set.ext_iff.1 Set.range_diag _).trans (by
    simpa using! H ..)⟩).baseChange (v := Subfunctor.toRange (lift (𝟙 _) (𝟙 _))) (u :=
  (tensorLeftIsoProd Z).inv Z) (.of_horiz_isIso ⟨(Iso.eq_comp_inv _).2 (prod.comp_lift ..)⟩)) _

/-- Let Z be a functor proper over D, W proper over T, Y → W with Y proper over T, and Z → W
compatible with a ring map ψ: T → D. Then the fibre product V = Z ×_W Y is proper over D. -/
lemma of_isPullback {V W b v q p u} (hb : @IsProperOver W T b) (H : @IsPullback _ _ V Z Y W q v u p)
  (ht : IsProperOver (p ≫ b)) ψ (w : u ≫ b = s ≫ reprMap ψ) : IsProperOver (q ≫ s) := by
  obtain ⟨⟨e, H⟩, ⟨S, _, a, A⟩, R, _, c, B⟩ := isPullback_iff.1 H, h, ht
  have i C x y : x = y ↔ _ := ⟨by lia, ((H C _ _ (e ..)).unique · ⟨rfl, rfl⟩)⟩
  have ⟨_, ⟨g⟩, G⟩ := hb.isRelAffine_pointMap (u _ a) (pointMap (p _ c))
  have ⟨⟨φ⟩, k, G⟩ := (uliftCoyonedaEquiv.exists_congr_left.1 G).imp fun _ ↦ isPullback_iff.1
  have ⟨x, _⟩ := H _ (Y.map g c) (Z.map φ a) (by simpa using! k _ ⟨𝟙 _⟩)
  exact ⟨fun C x y ↦ (S C (q _ x) (q _ y)).elim fun I _ ↦ (R C (v _ x) (v _ y)).imp' (· ⊔ I)
    (by simp_all), _, x, fun O z i ↦ (A O (q _ z) i).elim fun f m ↦ (B O (v _ z)
    (congr(baseRingMap b $(e ..) ·) ▸ congr(baseRingMap $w _) ▸ i _)).elim fun l n ↦
    (G _ _ _ (hb.injective_map_valuationSubring O (by
    simpa [← m, ← n] using! e _ z))).imp' (·.1) (by rintro ⟨⟩ ⟨⟨⟨⟩, ⟨⟩⟩⟩; simp_all -dsimp)⟩

/-- Properness is stable under base change: if Z is proper over D via s: Z → h_D and φ: D → T is
a ring homomorphism, then Z ×_{h_D} h_T is proper over T via its second projection to h_T. -/
lemma baseChange φ : IsProperOver (fibreProd.snd s (@reprMap _ _ D T φ)) := (fun p : ∀ {D},
  IsProperOver (𝟙 (reprBy D)) ↦ p.of_isPullback p isPullback_fibreProd h φ rfl) ⟨fun _ x y ↦
  ⟨⨆ d, .span {x.1.hom d - y.1.hom d}, fun _ _ ↦ ULift.up_inj.trans (by
  simp [ConcreteCategory.hom_ext_iff])⟩, _, ⟨𝟙 _⟩, fun O ↦ (⟨ofHom <| ·.1.1.codRestrict O ·, rfl⟩)⟩

/-- Let c: Y → Z be a map over D with Y and Z both proper in the sense of `IsProperOver`. If c
is onto on points in every algebraically closed field, its image is dense for coefficients
in locally constant Λ-valued functions. -/
lemma hasCohomDenseImage_of_surjective (h' : @IsProperOver Y D (c ≫ s)) (H : ∀ k [Field k]
  [IsAlgClosed k], (⇑(c ⟨k⟩)).Surjective) : HasCohomDenseImage Λ c := h'.2.elim fun _ ⟨a, ha⟩ ↦
  .mono ((h.isRelAffine_pointMap _).hasCohomDenseImage_of_lifts fun O y ↦ (H ..).elim fun x e ↦
  (ha O x (congr(baseRingMap s $e ·) ▸ by simp)).imp' _ fun _ _ ↦ h.injective_map_valuationSubring O
  (.trans (by aesop) e)) fun _ _ ⟨u, e⟩ ↦ e ▸ ⟨_, c.naturality_apply _ a⟩

/-- For Z proper over D there are a ring P of dimension ≤ 0 with algebraically closed residue
fields, ξ ∈ Z(P), and z ∈ Z(T), T = `ResiduePlace.prodValRing`, agreeing with ξ over ∏ κ(q), whose
space of places `ResiduePlace.placeSpace` has dense image in Z for Λ. -/
lemma exists_placeSpace_cover : ∃ P ξ z, HasCohomDenseImage Λ (@placeSpaceMap Z D P s ξ z) := by
  obtain ⟨T, a, ha⟩ := h.2
  let K (j : PrimeSpectrum T) := AlgebraicClosure j.1.ResidueField
  have (q) i := (@IsTest.exists_valuationSubring_atPrime (∀ j, K j) _ .pi q i).1
  refine (Classical.skolem.1 fun j ↦ ha (valSubring j) (Z.map (ofHom (algebraMap ..)) a)
    (by simpa using! j.base_mem)).elim fun u e ↦ ⟨⟨∀ j, K j⟩, Z.map (ofHom (algebraMap ..)) a,
    ⟨Z.map (ofHom (.pi (u · |>.1))) a, ?z, h, (⟨·⁻¹, by aesop⟩), inferInstance⟩,
    h.hasCohomDenseImage_of_surjective isProperOver_placeSpace fun L _ _ y ↦ ?_⟩
  exact h.ext_of_jointly_injective (ofHom <|
    evalRingHom _ ·) (by bound) (by simpa only [← map_comp_apply])
  choose u r using ha ⊤ y (by simp)
  choose q l e using exists_factor_residueField (u ≫ ofHom (ValuationSubring.subtype _))
  algebraize [l.1]
  let k : K q →ₐ[_] L := IsAlgClosed.lift (R := q.1.ResidueField)
  exact (exists_factor_residueField (ofHom (k.1.comp (evalRingHom ..)))).elim fun p ⟨m, i⟩ ↦ ⟨⟨⟦_⟧⟩,
    (map_comp_apply ..).trans
    (congr(Z.map (ofHom (evalRingHom PlaceField ⟨p, ⊤, by simp⟩) ≫ m) $(?z)).trans
    (by simp_rw [← r, ← map_comp_apply, ← e]; congr 3 with; exact congr($i _).trans (k.2 _)))⟩

/-- A functor of points Z that is proper over D in the sense of `IsProperOver` has the
continuity property `IsCohomContinuous` for filtered limits, with coefficients in locally
constant Λ-valued functions. -/
lemma isCohomContinuous : IsCohomContinuous Λ Z := h.2.elim fun _ ⟨a, ha⟩ ↦ .of_atlas
  (h.isRelAffine_pointMap a) ((h.isRelAffine_pointMap _).hasCohomDenseImage_of_lifts fun O _ ↦
  (ha O _ (by simp)).imp' _ fun _ ↦ (h.injective_map_valuationSubring O <| .trans (by aesop) ·))
end IsProperOver
end

-- part: Lib.Cohomology.ProperBaseChange.KummerLine
section
/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: Mayer-Vietoris for locally constant functions on two rings with a common localisation. -/

attribute [-simp] map_eq_zero IsIdempotentElem.iff_eq_zero_or_one


open PrimeSpectrum Polynomial CommRingCat Ideal.Quotient IsLocalization IsLocalRing IsAIC Submodule
  Algebra AlgebraMonoidAlgebra Pointwise IsScalarTower Subring Set Filter algebraMap
variable {ι A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [Algebra A B]
  [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D] [IsScalarTower A B D] (I : Ideal A)
  [IsScalarTower A C D] (t : B) (s : C) [Away t D] [Away s D] (hts : (t * s : D) = 1)
  (hD : ∀ x : D, IsIntegral A[(t : D), ↑s] x)

/-- If z lies in the A-span of the f(i), then for all large finite T ⊆ ι and all large finite S
⊆ A, z lies in the span of f(T) over the subring generated by S. -/
lemma eventually_mem_span_closure (f : ι → D) z (h : z ∈ span A (range f)) : ∀ᶠ (T : Finset ι)
    (S : Finset A) in atTop, z ∈ span (@closure A _ S) (f '' T) :=
    (Finsupp.mem_span_range_iff_exists_finsupp.1 h).elim fun a e ↦ .mono (mem_atTop _) fun _ l ↦
    .mono (mem_atTop _) fun _ k ↦ e ▸ sum_mem fun i h ↦ smul_mem _ (Subtype.mk _ (subset_closure
    (k (Finset.mem_image_of_mem a h)))) (subset_span ⟨i, l h, rfl⟩)

private lemma eventually_zpow_mul_mem_range (τ : Dˣ) (h : (t : D) = τ) x : ∀ᶠ j : ℤ in atTop,
  IsInteger B ((τ ^ j).1 * x) := (Away.surj t x).elim fun n ⟨a, H⟩ ↦ .mono (mem_atTop ↑n) fun _ l ↦
  (Int.le.dest l).imp' (a * t ^ ·) (by rintro _ ⟨⟩; simp [zpow_add]; grind)

include hts hD

/-- Let D = B[1/t] = C[1/s], ts = 1, be a ring integral over A[t,s]. For finite G ⊂ D there are a
subring R ⊂ A and a Noetherian R-submodule Y ⊃ G ∪ {1} such that each n has R-submodules P ⊂ im B,
Q ⊂ im C and finitely generated M with Yⁿ, PQ ⊂ M ⊂ P+Q+Y. -/
lemma exists_noetherian_fg_filtration (G : Set D) [Finite G] : ∃ (R : Subring A) (Y :
  Submodule R D), insert 1 G ⊆ Y ∧ IsNoetherian R Y ∧ ∀ n, ∃ P ≤ (toAlgHom _ B D).toLinearMap.range,
  ∃ Q ≤ (toAlgHom _ C D).toLinearMap.range, ∃ M ∈ Icc (Y ^ n) (P ⊔ Q ⊔ Y), M.FG ∧ P * Q ≤ M := by
  let τ := Units.mkOfMulEqOne _ _ hts
  let F := (Units.coeHom D).comp (zpowersHom _ τ); let T : ℤ → D := F
  have hT a b : T '' a * T '' b ⊆ T '' (a + b) := (image_mul F).ge
  obtain ⟨S, hS⟩ := fg_adjoin_of_finite ‹_› fun g _ ↦ hD g
  choose r hr using fun x : ↥(insert 1 G ∪ S * S) ↦ mem_span_finset'.1
    (mem_of_mem_of_subset x.2 (by grw [hS, span_le.1 hS.le]; simp [insert_subset]))
  have ⟨k, l, H⟩ := ((eventually_forall_ge_atTop.2 (S.eventually_all.2 fun x _ ↦
    (eventually_zpow_mul_mem_range t τ rfl x).and (eventually_zpow_mul_mem_range s τ⁻¹ rfl x))).and
    (Finset.tendsto_Icc_neg_atTop_atTop (eventually_all.2 fun p ↦
    eventually_mem_span_closure T _ (span_mono ((MonoidHom.mrange F).closure_le.2 (pair_subset
    ⟨.ofAdd 1, pow_one _⟩ ⟨.ofAdd (-1), pow_one _⟩)) ((adjoin_eq_span ..).le (↿r p).2))))).exists
  have ⟨U, H⟩ := (eventually_all.2 H).exists
  let M a b := span (@closure A _ U) (T '' Icc a b * S :)
  have ⟨o, hk⟩ := union_subset_iff.1 (Subtype.forall'.2 fun x ↦ hr x ▸ (span_mul_span ..).le
    (sum_mem fun g _ ↦ mul_mem_mul (Finset.coe_Icc _ k ▸ H (x, g)) (subset_span g.2)))
  have m a b c d : M a b * M c d ≤ M _ _
  grw [span_mul_span, mul_mul_mul_comm, ← span_mul_span, hk, span_eq, span_mul_span,
    ← mul_assoc, hT, hT, Icc_add_Icc_subset, Icc_add_Icc_subset]
  have := is_noetherian_subring_closure _ U.finite_toSet
  refine ⟨_, _, o, isNoetherian_span_of_finite _ (toFinite _), fun n ↦ (n.rec ⟨_, _, one_le.2 (o
    (by simp))⟩ fun _ ⟨i, j, h⟩ ↦ ⟨_, _, by grw [pow_succ, h, m]⟩ : ∃ i j, _ ^ n ≤ M i j).elim fun i
    ⟨j, h⟩ ↦ ⟨M k j, span_le.2 (mul_subset_iff.2 (forall_mem_image.2 (l · ·.1 · · |>.1))), M i (-k),
    by simpa [M, span_le, mul_subset_iff, ↓forall_mem_image] using! fun _ _ h ↦ (l _ (le_neg.1 h)
    · · |>.2), _, ⟨h, ?_⟩, fg_span (toFinite _), by grw [m]; simp⟩⟩
  simp [M, ← span_union, ← union_mul, ← image_union]; gcongr; simp [subset_def]; omega

lemma line_mayer_vietoris [IsDomain A] [IsDomain D] {ℓ} [ThePrime ℓ] (u : IsUnit (ℓ : A)) [IsAIC A]
  [IsAIC B] [IsAIC C] (hA : ∀ (x : B) (y : C), (x : D) = y → (x, y) ∈ range (algebraMap A _))
  (i : (∃ a, algebraMap A B a * (1 - t) = 1 ∧ (algebraMap A C a - 1) * (s - 1) = 1 ∧ Away a B ∧
  (a * (a - 1) ∈ I ∨ ∀ r ∈ I, ∃ ε, ε + r * ε ^ 2 = 1)) ∨ IsAICLocal A)
  (hI : ∀ {E} [CommRing.{0} E] (ψ : A →+* E), ∀ x ∈ I.map ψ, ∃ i ∈ I, ψ i ∣ x) {J L K h₁ h₂} (e :
  (I.map (algebraMap A B), I.map (algebraMap A C), I.map (algebraMap A D)) = (J, L, K)) :
  let r := J.quotientMap K (algebraMap ..) h₁; let q := L.quotientMap K (algebraMap ..) h₂; (∀
{x y}, IsClopen x → IsClopen y → PrimeSpectrum.comap r ⁻¹' x = PrimeSpectrum.comap q ⁻¹' y →
∃ k : A, x = basicOpen (k : B ⧸ J) ∧ y = basicOpen (k : C ⧸ L)) ∧
∀ u, ∃ a b, u = (locConstSpec ⟨ZMod ℓ⟩).map (ofHom r) a - (locConstSpec _).map (ofHom q) b := by
  intro r q
  let f := toAlgHom A B D; let g := toAlgHom A C D
  have Z {E} [CommRing.{0} E] {ψ : A →+* E} {i} := eq_zero_iff_mem.2 ∘ I.mem_map_of_mem ψ (x := i)
  use ?_, fun v ↦ (by
    have H : ∀ w, w ^ ℓ = 1 → ∃ a b W, W ^ ℓ = f a * g b ∧ mk J a = 1 ∧ mk L b = 1 ∧ w = mk K W :=
      mk_surjective.forall.2 fun w h ↦ dite _ id fun n ↦ ?_
    obtain ⟨⟨ζ, h⟩, φ, hφ⟩ := exists_root _ (cyclotomic.monic ℓ A)
      (by simp [NeZero.pos, natDegree_cyclotomic]), exists_ringHom_of_locallyConstant A (D ⧸ K)
    have P {S} [CommRing S] [IsDomain S] [Algebra A S] := (@isRoot_cyclotomic_iff S _ ℓ _
      ⟨mod_cast (u.map (algebraMap A S)).ne_zero⟩ _).1 (map_cyclotomic ℓ (algebraMap A S) ▸ h.map)
    have a {S} [CommRing S] [Algebra A S] {y : S} (k : y ^ ℓ = 1) :
      ∃ a : LocallyConstant .., ∀ p, y - ζ ^ a p ∈ asIdeal p
    · choose a l ha using fun p ↦ P.eq_pow_of_pow_eq_one (ξ := mk (asIdeal p) y) congr($k)
      use ⟨a, fun s ↦ ?_⟩, (Ideal.Quotient.eq.1 <| ha · |>.symm)
      convert (Iio ℓ \ s).toFinite.isOpen_biInter fun i _ ↦ (basicOpen (y - ζ ^ i)).2
      ext; simp [← mk_eq_mk_iff_sub_mem]; grind [IsPrimitiveRoot.pow_inj]
    let ⟨x, y, W, E, k₁, k₂, k₃⟩ := H (φ (v.map (ζ ^ ·.val))) (by
      rw [← map_pow, ← φ.map_one]; congr with _
      apply ((powMonoidHom ℓ).eqLocusM 1).pow_mem P.1)
    obtain ⟨⟨x, rfl⟩, y, rfl⟩ := exists_pow_eq ℓ x, exists_pow_eq ℓ y
    simp [← mul_pow, ← mem_nthRoots, NeZero.pos, P.nthRoots_eq rfl] at E k₁ k₂
    obtain ⟨⟨i, -, rfl⟩, ⟨a, ha⟩, b, hb⟩ := E, a k₁, a k₂
    use a.map (i + ↑·), -b.map (↑), LocallyConstant.ext fun p ↦ ?_
    obtain _ := ha (p.comap r), hb (p.comap q)
    apply_fun algebraMap _ p.1.ResidueField at k₃
    simp_all +zetaDelta [← p.1.algebraMap_residueField_eq_zero, ← pow_add, ← algebraMap_apply]
    erw [congr(residue _ $(hφ ..)), map_pow, (P.isOfFinOrder NeZero.out).pow_inj_mod] at k₃
    simpa [← add_assoc, ← ZMod.natCast_eq_natCast_iff', ← sub_neg_eq_add, ← P.eq_orderOf] using! k₃
    cases e
    have n {i} (m : i ∈ I) (k : IsUnit (i : D)) :=
      n ⟨1, 1, 1, by simp [← (k.map (algebraMap ..)).mul_right_inj, Z m]⟩
    obtain ⟨⟨a, k, q, _, i⟩ | i, ⟨u, hu⟩, ϖ, m, G, hw⟩ :=
      i, u.neg.invertible, hI _ _ (Ideal.Quotient.eq.1 h)
    · have : Away _ D := .mul_of_associated a (a - 1) t ⟨⟨_, _, by ac_nf, k⟩, by simp [sub_mul, k]⟩
      have ⟨d, j, e⟩ := this.surj _ G
      have ⟨u, v, c⟩ := @IsCoprime.pow _ _ a _ d d (.sub_one_right_of_dvd dvd_rfl)
      have ⟨ε, o⟩ := i.resolve_left (n · this.algebraMap_isUnit) _ (I.smul_mem (u * v * j) m)
      use 1 + ε • ϖ • j • v • (1 - t) ^ d, 1 + ε • ϖ • j • u • (s - 1) ^ d, w
      have := congr((f $k ^ d, g $q ^ d, $c • G, $o • G))
      simp [mul_pow, smul_def', Z m] at this e ⊢; grind
    have ⟨U, N, hG, _, H⟩ := exists_noetherian_fg_filtration t s hts hD {G}
    obtain ⟨P, hP, Q, hQ, _, ⟨hN, h'⟩, ⟨e, ⟨⟩⟩, hPQ⟩ := H _
    rw [← map_comap_eq_self hP, ← map_comap_eq_self hQ] at h'
    choose a ha b hb y hy he using fun k :
      e ↦ by simpa [Submodule.mem_sup] using h' (subset_span k.2)
    let κ := toAlgHom U D (MvPolynomial e D); let T N := span (MvPolynomial e A) (κ '' N)
    have hL {N} {v : e → D} (h : ∀ k, _) :=
      (T N).sum_smul_mem (t := .univ) .X fun k _ ↦ subset_span ⟨v k, h k, rfl⟩
    obtain ⟨o, z⟩ := by simpa using (span_le.1 (refl (T N)) ⟨·, hG ·, rfl⟩)
    let c : T N := u • ⟨_, add_mem z (hL hy)⟩
    have ⟨Φ, r, K⟩ : ∃ Φ ∈ T N ^ (ℓ + 1), (1 + ϖ • c.1) ^ ℓ * (1 + ϖ • κ G) = 1 + ϖ •
      (κ G + ℓ • c.1 + ϖ • Φ) := ℓ.rec ⟨0, by simp⟩ fun m ⟨Φ, r, ih⟩ ↦ ⟨_, add_mem (mul_mem_mul r
      (add_mem o (ϖ • c).2)) (mul_mem_mul (mul_mem_mul (pow_mem_pow _ o m) c.2) (add_mem z
      (m • c).2)), by simp [pow_succ', mul_assoc, ih]; algebra⟩
    obtain ⟨p, hF⟩ := (mem_span_image_finset_iff_exists_fun _).1 (mem_of_le_of_mem (by grw
      [span_pow, span_mul_span, ← image_mul, ← image_pow, N.pow_subset_pow, P.mul_subset_mul, hN,
      hPQ, sup_idem, ← κ.coe_toLinearMap, image_span_subset_span, span_span_of_tower])
      (sub_mem_sup r (mul_mem_mul (hL ha) (hL hb))))
    have ⟨x, H⟩ := i.multivariate_hensel (p := ϖ • p) fun k _ u ↦ n (I.mul_mem_right _ m) (u.map _)
    let ev := MvPolynomial.eval (algebraMap A D ∘ x)
    use 1 + ϖ • ∑ k, x k • a k, 1 + ϖ • ∑ k, x k • b k, w * (1 + ϖ • ev c)
    have := congr((ev $K, ev $hF, ofId A D $hu))
    simp +zetaDelta [↓mul_pow, ← he, H, smul_def', mul_assoc, mul_add,
      ← Finset.mul_sum, ← algebraMap_apply, ← (p _).eval₂_comp, Z m] at this ⊢; grind)
  simp_rw [PrimeSpectrum.isClopen_iff, mk_surjective.exists]; rintro _ _ ⟨x, a, rfl⟩ ⟨y, b, rfl⟩ h
  obtain ⟨⟨⟩, _, h⟩ := e, b.map q,
    basicOpen_injOn_isIdempotentElem (a.map _) (b.map _) (SetLike.ext' h)
  have ⟨ϖ, m, ⟨α, β⟩, p⟩ := hI (.prod (ofId A D) (ofId A D)) ((f x, g y) * (1 - (g y, f x))) ?_
  have ⟨S, F, hE, _, hN⟩ := exists_noetherian_fg_filtration t s hts hD {f x, g y, α, β}
  let φ := f.toLinearMap.coprod (-g.toLinearMap); let N := φ.range.restrictScalars S
  have ⟨E, i, hN⟩ : ∃ E, _ ∈ Icc F (N ⊔ F) := ⟨_, (iSup_eq_toSubmodule_range
    (F ^ ·)).subst ⟨le_iSup_of_le 1 (by simp), iSup_le (hN · |>.elim fun _
    ⟨c, _, d, _, ⟨a, b⟩, _⟩ ↦ by simp [N, φ, LinearMap.range_coprod]; grw [a, b, c, d]; rfl)⟩⟩
  obtain ⟨⟨k, h⟩, u, v, c, d⟩ := @WellFounded.not_rel_apply_succ _ GT.gt _
    (N.comap <| ϖ ^ · • F.subtype), by simpa [subset_def] using hE.trans i
  let n := k.succ
  obtain ⟨⟨j, l⟩, e⟩ := mul_dvd_mul (one_sub_dvd_one_sub_pow (1 - ((⟨_, u⟩, ⟨_, v⟩) : E × E) ^ n)
    n) (pow_dvd_pow_of_dvd (one_sub_dvd_one_sub_pow (⟨_, v⟩, ⟨_, u⟩) n) n)
  obtain ⟨⟨_, w, rfl⟩, z, o⟩ := mem_sup'.1 (hN (j * ⟨_, c⟩ ^ n - l * ⟨_, d⟩ ^ n).2)
  have r : φ (1 - (1 - (x, y) ^ n) ^ n - ϖ ^ n • w) = ϖ ^ n • z
  · have := congr($p ^ n)
    simp [φ, mul_pow, Prod.ext_iff, Subtype.ext_iff, smul_def'] at e o this ⊢; grind
  exact (not_lt_iff_le_imp_ge.1 h (fun _ ↦ .imp' (ϖ • ·) (by simp_all [pow_succ', mul_smul]))
    ⟨_, r⟩).elim fun v j ↦ (hA _ _ (eq_of_add_neg_eq_zero (φ.sub_mem_ker_iff (y := ϖ • v).2
    (r.trans (by simp [n, pow_succ', mul_smul, j]))))).imp (by simp +contextual [← mk_algebraMap,
    *, n, IsIdempotentElem.pow_succ_eq, smul_def'])
  exact (Ideal.ideal_prod_eq _).ge (by simp_all +zetaDelta [I.map_map,
    ← eq_zero_iff_mem, ↓Ideal.mem_prod])
end

-- part: Lib.Cohomology.ProperBaseChange.SubringSplitting
section
/-! Part of: Proper base change; invariance under extension of algebraically closed fields (known
result; see Lib.Cohomology.ProperBaseChange.ProperBaseChange).

This file: A non-valuation subring splits into two larger ones with exact Mayer-Vietoris
sequence. -/

open CategoryTheory CommRingCat Subring Ideal.Quotient IsLocalization Away PrimeSpectrum Fact
  LocallyConstant IsLocalRing Ideal LocalSubring
variable {ℓ K} [ThePrime ℓ] [Field.{0} K] [IsAlgClosed K] {S T U : Subring K} [h : Fact (S ≤ T)]
  {D : CommRingCat} (J : Ideal D) (γ : D →+* K)

/-- For a ring homomorphism γ from D to the field K, the set of absolutely integrally closed
subrings of K that contain the image of γ. -/
def aicSubrings := {B | γ.range ≤ B ∧ IsAIC B}

/-- For an ideal J of D and B in `aicSubrings` γ, the ideal of B generated by γ(J). -/
abbrev aicSubrings.extendedIdeal (B : aicSubrings γ) := J.map (γ.codRestrict _ (B.2.1 ⟨·, rfl⟩))

/-- For an ideal J of D, the functor from the ordered set `aicSubrings` γ of subrings to
commutative rings sending B to B/γ(J)B. -/
def aicSubrings.quotientFunctor : aicSubrings γ ⥤ CommRingCat := .mk (of <| _ ⧸ extendedIdeal J γ ·)
  fun l ↦ ofHom (quotientMap _ (inclusion l.le) (map_le_of_le_comap le_comap_map))

instance : Algebra S T := (inclusion h.1).toAlgebra

instance [Fact (T ≤ U)] [Fact (S ≤ U)] : IsScalarTower S T U := .of_algebraMap_eq' rfl

local instance [a : IsAIC S] : IsIntegrallyClosedIn S K :=
  isIntegrallyClosedIn_iff.2 ⟨S.subtype_injective, a.mem_range_of_isIntegralElem⟩

omit [IsAlgClosed K] in
lemma IsAIC.isLocalization_away (a : IsAIC S) (x : S) {y : K} (m : y ∈ T) (e : x * y = 1 := by grind
  [zero_mem]) (H : ∀ {U : Subring K}, IsAIC U → S ≤ U → y ∈ U → T ≤ U := by simp +contextual
  [sub_mem, *]) : Away x T := let φ := Localization.awayLift _ x (.of_mul_eq_one y e)
  .mk _ (.of_mul_eq_one ⟨y, m⟩ (Subtype.ext e)) (H ((a.of_isLocalization (.powers x)).of_surjective
  φ.rangeRestrict_surjective) (⟨_, lift_eq x _ ⟨·, ·⟩⟩) ⟨invSelf x, (lift_mk'_spec ..).2 e.symm⟩ ·.2
  |>.elim (by peel surj x ·; ext; simpa [·, φ] using! congr(φ $this))) (by rintro ⟨⟩ ⟨⟩ ⟨⟩; simp)

/-- Let K be algebraically closed, divisibility in D total, ℓ ∈ D^× prime, B in
`aicSubrings` γ not a valuation ring of K. There are B₁, B₂ ⊋ B generating B₃, all in
`aicSubrings` γ, such that every valuation ring of K containing B contains B₁ or B₂, and
the Mayer–Vietoris sequence of locally constant ℤ/ℓ-valued functions on the spectra modulo
γ(J) is short exact. -/
lemma aicSubrings.exists_split_mayer_vietoris [PreValuationRing D] (u : IsUnit (ℓ : D)) B (n : ¬∀ x,
  x ∈ B.1 ∨ x⁻¹ ∈ B.1) : ∃ (B₁ B₂ B₃ : aicSubrings γ) (l₁ : B < B₁) (l₂ : B < B₂) (h₁ : B₁ ≤
  B₃) (h₂ : B₂ ≤ B₃), B₃ = B₁.1 ⊔ B₂ ∧ (∀ V : ValuationSubring K, B ≤ V.1 → B₁ ≤ V.1 ∨ B₂ ≤ V.1) ∧
  let L {S T} (l : S ≤ T) := (quotientFunctor J γ ⋙ locConstSpec ⟨ZMod ℓ⟩).map l.hom
  (∀ l, L l₁.le l = 0 → L l₂.le l = 0 → l = 0) ∧ (∀ x y, L h₁ x = L h₂ y → ∃ l, L l₁.le l = x ∧
  L l₂.le l = y) ∧ ∀ z, ∃ x y, z = L h₁ x - L h₂ y := by
  obtain ⟨B, g, i⟩ := B
  by_contra h
  apply PLift.up at h
  choose cl o a using fun {t} ↦ (⟨_, integralClosure_subring_le_iff (S := B ⊔ closure {t}).trans
    (sup_le_iff.trans (by simp)), .of_isIntegrallyClosedIn K⟩ :
    ∃ C, (∀ {U : Subring K} [IsIntegrallyClosedIn U K], C ≤ U ↔ B ≤ U ∧ t ∈ U) ∧ IsAIC C)
  choose j k using fun {t} ↦ (o.1 (refl (@cl t))).imp_left mk
  -- no t outside B, with 1/t outside B, satisfies the case hypothesis `i` of `line_mayer_vietoris`
  have M t (ht : t ∉ B) (hu : t⁻¹ ∉ B) : ¬_
  obtain ⟨p, q⟩ := (sup_le_iff.1 (refl (@cl t ⊔ @cl t⁻¹))).imp mk mk
  obtain ⟨w⟩ := fun {V : ValuationSubring K} h ↦ have := @IsAICLocal.toIsAIC V _ _
    (and_or_left.1 ⟨h, V.2 t⟩).imp o.2 o.2, mk (j.1.trans p.1),
    a.isLocalization_away ⟨t, k⟩ (q.1 k), a.isLocalization_away ⟨t⁻¹, k⟩ (p.1 k)
  -- the spectra of B₁/γ(J)B₁ and B₂/γ(J)B₂ cover that of B/γ(J)B (proved after its use)
  have s : (Sum.elim _ _).Surjective; swap
  refine fun H ↦ h.1 ⟨⟨_, g.trans out, a⟩, ⟨_, g.trans out, a⟩, ⟨_, g.trans out,
    a.of_isLocalization _⟩, ⟨out, mt (· k) ht⟩, ⟨out, mt (· k) hu⟩,
    out, out, rfl, @w, fun _ e f ↦ ext (s.forall.2 (Sum.rec (congr($e.1 ·)) (congr($f.1 ·)))),
    .imp_left (fun w x y e ↦ ?_) (line_mayer_vietoris (extendedIdeal J γ ⟨B, g, i⟩) ⟨t, _⟩ ⟨t⁻¹, _⟩
    (Subtype.ext (mul_inv_cancel₀ (by bound))) (by exact (let U := integralClosure ..
    have m {s h} e := (@o s U.toSubring _).2 ⟨(U.2 <| algebraMap B _ ⟨·, ·⟩), U.2 ⟨⟨s, h⟩,
      Algebra.subset_adjoin e⟩⟩
    .tower_bot (subtype_injective _) <| sup_le (m (.inl rfl)) (m (.inr rfl)) ·.2)) (by
    simpa using u.map (γ.codRestrict B (by tauto))) (by
    rintro ⟨b⟩ ⟨⟩ ⟨⟩; exists ⟨b, eq_iInf_of_isIntegrallyClosedIn.ge (mem_iInf.2 (by
    cases w ·.2 <;> tauto))⟩) H (fun _ _ a ↦ (exists_map_dvd_of_mem_map ((J.map_map ..).le a)).imp'
    _ fun _ ↦ .imp_left (mem_map_of_mem _)) (by simp [J.map_map]; tauto))⟩
  choose z a b using fun {c} ↦ w (x.2.isClopen_fiber _) (y.2.isClopen_fiber _) congr($e.1 ⁻¹' {c})
  choose l o using s.forall (p := (∃ c, ∀ {k}, (c = k) = (basicOpen (mk _ (@z k))).1 ·)).2
    (Sum.rec (⟨_, congr($a ·)⟩) (⟨_, congr($b ·)⟩))
  exact ⟨⟨l, .iff_isOpen_fiber.2 fun _ ↦ (funext (o ·)).symm.subst
    (basicOpen _).2⟩, ext fun _ ↦ (o _).ge (a.le rfl), ext fun _ ↦ (o _).ge (b.le rfl)⟩
  intro p
  obtain ⟨V, h, _⟩ := (ofPrime _ (p.comap (mk _)).1).exists_le_valuationSubring
  have m {a} := (map_mem_nonunits_iff (inclusion h) _).trans
    (AtPrime.to_map_mem_maximal_iff _ (p.comap (mk _)).1 a)
  refine Sum.exists.2 ((w ((le_ofPrime ..).trans h)).imp ?_ ?_) <;> exact fun h ↦ ⟨.comap
    (quotientMap (maximalIdeal V) (inclusion h) (map_le_of_le_comap fun a n ↦ m.2 (ker_le_comap
    _ (mk_ker.ge (mem_map_of_mem _ n))))) ⊥, by ext ⟨⟩; exact eq_zero_iff_mem.trans m⟩
  have U b c (e : ¬(IsUnit b ∨ IsUnit (1 - b))) := M (1 - b.1⁻¹) ?_ ?_ (.inl ⟨b, ?_, ?_,
    i.isLocalization_away _ (sub_mem (one_mem _) k) ?_, c⟩)
  refine n fun t ↦ by_contra (not_or.1 · |>.elim (M t) (.inr ⟨(eq_sub_of_add_eq' · ▸ by_contra (U _
    (.inr fun r _ ↦ (i.exists_pow_sub_mul_eq 2 1 r).elim fun ρ o ↦ (by_contra (U ρ
    (.inl ?_))).elim (·.exists_right_inv.imp ?_) (·.exists_right_inv.imp ?_))))⟩)) <;> grind
  all_goals clear * - e; push_cast [Submonoid.isUnit_iff_and, Subtype.ext_iff, algebraMap,
    coe_inclusion] at *; grind [→ sub_mem B.one_mem]
end

-- part: Lib.Cohomology.ProperBaseChange.ProperBaseChange
section
/-! Known result: Proper base change and invariance under extension of algebraically closed fields.
Here the coefficients are constant F_ℓ, the base is an absolutely integrally closed valuation ring,
and properness of a functor is expressed by valuative lifting. The proof reduces to spaces of places
of a field, then uses Zorn's lemma on subrings with a Mayer–Vietoris splitting and Kummer theory.
Source: Artin, SGA 4 Exp. XII 5.1, 5.4, 5.5 (1973); Stacks Project Tag 095S; reduction to spaces of
places as in Scholze, Étale cohomology of diamonds (2017), Thm 19.2 and Lemma 19.4, after Huber,
Math. Ann. 295 (1993).

This file: Proper base change: closed fibre over an absolutely integrally closed valuation ring, F_l
coefficients. -/

open CategoryTheory CommRingCat Subfunctor IsLocalRing Ideal Quotient ResiduePlace aicSubrings
  Filter Comparison ULift Functor Subring RingHom

/-- Proper base change: for a functor Y proper over an absolutely integrally closed valuation
ring A and ℓ a prime invertible in A, restriction from Y to its closed fibre is bijective on
all cohomology groups with coefficients ℤ/ℓ.

Known result: Proper base change; invariance under extension of algebraically closed fields. -/
lemma IsProperOver.proper_base_change {ℓ} [ThePrime ℓ] {Y A} [CommRing A] [IsAICLocal A]
  [PreValuationRing A] {s} (h : @IsProperOver Y ⟨A⟩ s) (u : IsUnit (ℓ : A)) :
  Components ⟨ZMod ℓ⟩ (zeroPoints s (maximalIdeal A)).ι :=
  (show IsBijective _ (freeAbMap (Y := _ ⋙ Y) _) from forall_bijective_iff_bijectiveUpTo.2 (by
  induction' · with _ ih generalizing Y; tauto
  refine h.exists_placeSpace_cover.elim fun P ⟨ξ, z, d⟩ ↦ have := z.isAlgClosed_residueField
    bijectiveUpTo_of_cech_pred (p' := mapOnTests (fromPreimage _ (placeSpaceMap z))) (v :=
      mapOnTests (ι _)) rfl d.isCohomEquiv (d.of_preimage_le (mapOnTests (ι _)) (by
               rintro _ ⟨⟩ ⟨_, ⟨⟩⟩; tauto)).isCohomEquiv ?_ fun m ↦ (bijectiveUpTo_congr (p := 𝟙 _)
      ((whisker (zeroPoints ..) testIncl).lift_ι _ fun _ _ ⟨x, e⟩ ↦ e ▸ (x.1 0).2) (.of_isIso _)
      (.of_bijective fun _ ↦ (Equiv.mk _ fun x ↦ ⟨fun i ↦ ⟨_, (x.1.2 0 i ▸ x.2 : _ ∈ zeroPoints s _
      _)⟩, (congr(⟨$(x.1.2 · ·), _⟩))⟩).bijective)).1 (@ih _ (cech.proj (placeSpaceMap z) m 0 ≫ _ ≫
      s) (m.rec (isProperOver_placeSpace.of_isPullback isProperOver_placeSpace (.of_vert_isIso
      (g := 𝟙 _) ⟨rfl⟩) isProperOver_placeSpace (𝟙 _) rfl) fun _ ↦
      (isProperOver_placeSpace.of_isPullback h isPullback_cech · (𝟙 _) rfl)))
  refine (Components.isCohomEquiv_of_connected
    (isProperOver_placeSpace.isCohomContinuous.of_isRelAffine ((isRelAffine_zeroPoints ..).preimage
    _)) isProperOver_placeSpace.isCohomContinuous _ (by tauto) isRelAffine_killingPlaces (placeGraph
    · |>.toAddSubmonoid.comap (.inl .. : _ →+ _)) .rfl (⟨eq_of_zero_eq_one <| placeGraph_unique ·
    (one_mem _)⟩) (fun e i ↦ .of_affine_cover (isRelAffine_killingPlaces <|
    span {cond · e (1 - e)}) fun _ x ↦ (exists_place_of_isLocalRing x).elim
    fun j ⟨_, _, H⟩ ↦ have := H _ _ le_rfl ▸ projRing_mem_killingPlaces j _; by
      cases @j.prime.2.2 e (1 - e) (by simp [i]) <;>
        [use ⊤; use ⊥] <;> rw [← span_singleton_le_iff_mem] at * <;> tauto) fun q T g ↦ ?_).bij
  have M := isMaximal_iff.2 ⟨q.ne_top_iff_one.1 T, fun J t ↦ by grind [z.absolutely_flat t,
    IsIdempotentElem, mul_mem_right, mul_mem_left, J.sub_mem_iff_left, IsConcreteLE.le_iff]⟩
  let γ := (algebraMap P q.ResidueField).comp (baseRingMap s ξ).hom
  let φ {C} (y : killingPlaces z q C) : finiteSubring z y →+* C :=
    .liftOfSurjective _ (rangeRestrict_surjective _) ⟨.domRestrict (snd ..) _, fun v k ↦
    placeGraph_unique v.2 (y.2 _ ((ker_algebraMap_residueField _).le congr($k.1)))⟩
  have hφ {C y} v : @φ C y ⟨_, v, rfl⟩ = v.1.2 := liftOfSurjective_comp_apply ..
  let ς {J} B : (placesFiniteOn z J B.1).toFunctor ⟶ reprBy (quotientFunctor J γ B) :=
    ⟨fun C ↦ ↾fun x ↦ ⟨ofHom (lift _ ((φ _).comp (B.1.inclusion x.2.2)) (map_le_of_le_comap (K :=
    ker _) fun a ↦ (hφ ⟨_, baseRingMap_mem_placeGraph a⟩).trans ∘ x.2.1 a))⟩, by
    intros; ext x; congrm ⟨?_⟩; ext ⟨_, h⟩; obtain ⟨v, rfl⟩ := x.2.2 h
    exact hφ ⟨(_, _), placeGraph_map (hφ v ▸ v.2)⟩⟩
  let σ {J} B : ((placesFiniteOn ..).whisker testIncl).toFunctor ⟶ _ := mapOnTests (@ς J B)
  have G J [p : IsPrime J] B : IsAcyclicOver (@σ J B) _
  have a : Antitone (placesFiniteOn z J ·.1 : aicSubrings γ → _) := antitone_const.inf (by tauto)
  have hκ n {B B'} l x : (HV.antitoneFamily a ..).map l (locConstClass (σ B) n x) =
    locConstClass (σ B') n ((_ ⋙ locConstSpec ⟨ZMod
    ℓ⟩).map l x) := map_locConstClass (by intros; erw [← map_comp_apply]; congr 3 with ⟨⟩; rfl) n
  have V B {Λ} : _ ∨
    IsAcyclicOver (σ B) Λ := let π := ofHom (Ideal.Quotient.mk (extendedIdeal J γ B))
    (em' _).imp (exists_split_mayer_vietoris J γ u B)
      fun n ↦ let j := ResiduePlace.mk ⟨q, _⟩ ⟨_, n⟩ (B.2.1 ⟨·, rfl⟩)
      .of_bijective (.quotient (@isTest_of_preValuationRing j.valSubring _ _ _ _)
        ((Ideal.isRadical_iff_pow_one_lt 2 .refl).2 fun x i ↦
        (exists_map_dvd_of_mem_map i).rec fun i ⟨m, k⟩ ↦ (IsAIC.exists_pow_eq 2 i).rec fun c e ↦
        mem_of_dvd _ (by simpa [← e] using k) (mem_map_of_mem _ (p.isRadical ⟨_, e ▸ m⟩)))) <|
        have c {C x φ} (e : x.1.1 = ⟨⟦j.projRing ≫ φ⟧⟩) : π ≫ @baseRingMap _ _ (ς B) C x = φ := by
          ext ⟨_, h⟩; obtain ⟨v, rfl⟩ :=
            x.2.2 h; exact hφ ⟨_, e.substr (mem_fractionGraph_projRing ..)⟩
        Equiv.bijective ⟨_, ((placesFiniteOn ..).toFunctor.map ·.1 ⟨⟨_,
          projRing_mem_killingPlaces j π⟩, fun a i ↦ (placeGraph_unique
        (baseRingMap_mem_placeGraph a) (by apply mem_fractionGraph_projRing)).trans
          (mk_ker.ge (mem_map_of_mem _ i)), q.algebraMap_residueField_surjective.forall.2
          (⟨⟨_, j.mem_fractionGraph_projRing · ·⟩, rfl⟩)⟩), fun x ↦ SetCoe.ext
        (SetCoe.ext (isProperOver_placeSpace.ext_of_jointly_injective (ofHom <| algebraMap _ <|
          Localization.AtPrime <| MaximalSpectrum.asIdeal ·) (eq_zero_of_localization · fun _
          k ↦ · ⟨_, k⟩) fun _ ↦ let y := (placesFiniteOn ..).toFunctor.map _ x
          (((finiteSubring_total_and_exists_place y.1.2).2 j.valSubring _ y.2.2).elim fun φ e ↦
            .symm (by rwa [← c e, baseRingMap_map] at e)
        : _ = y.1.1))), fun φ ↦ down_injective (hom_ext (ringHom_ext congr($(c rfl).1)))⟩
  have K n := zorn_injective_and_surjective (G :=
    quotientFunctor .. ⋙ locConstSpec _) (hκ n) @fun c hc ⟨o⟩ ↦ let φ (a : c) := a.1.1
    have E (x : ↥(iSup φ)) : ∀ᶠ b in atTop, x.1 ∈ φ b := mem_atTop_sets.2 (.imp (by tauto)
    ((mem_iSup_of_directed hc.1).1 x.2)); ⟨⟨⟨_, le_iSup_of_le o o.1.2.1, ⟨fun P ↦
    (P.coeffs.eventually_all.2 fun y _ ↦ E y).exists.rec fun b k ↦
      b.1.2.2.exists_root_of_coeffs_subset_range (f := inclusion (le_iSup φ b)) (⟨⟨_, k · ·⟩,
      rfl⟩)⟩⟩, .mk (⟨⟨le_iSup φ ·⟩⟩)⟩, isFilteredColimit_locConstSpec (c :=
      (quotientFunctor ..).mapCocone _) (Quot.ind (E · |>.exists.imp fun _ ↦ (⟨⟦⟨_, ·⟩⟧, rfl⟩))) (by
    rintro j ⟨⟩ k
    obtain ⟨o, i, f, e⟩ := exists_map_dvd_of_mem_map (eq_zero_iff_mem.1 k)
    exact ((E f).and (mem_atTop j)).exists.imp fun b ⟨h, l⟩ ↦ ⟨l.hom, eq_zero_iff_mem.2
      (mem_of_dvd _ ⟨⟨_, h⟩, by congrm ⟨$e.1, _⟩⟩ (mem_map_of_mem _ i))⟩),
      (isProperOver_placeSpace.isCohomContinuous.of_isRelAffine
    (isRelAffine_killingPlaces _)).isFilteredColimit_antitoneFamily a (fun _ ↦
      isRelAffine_placesFiniteOn) (by simp [placesFiniteOn, forall_and]; tauto)⟩
  have i := (K 0).1 fun B _ _ _ ↦ (V B).elim (by tauto) (·.1 (by simpa))
  refine ⟨i B, (·.strongRecOn (fun m ih ↦ (K m).2 fun B y g ↦ (V B).rec ?_ (·.2 ..)) B)⟩
  rintro ⟨B₁, B₂, C, l₁, l₂, _, _, u, v, _, k, o⟩; obtain ⟨⟨x₁, e₁⟩, x₂, e₂⟩ := g _ l₁, g _ l₂
  have t := (HV.mayer_vietoris_injective (a l₁.le) (a l₂.le) (.of_affine_cover
    (isRelAffine_placesFiniteOn (B := cond · B₁.1 B₂.1) |>.preimage (placesFiniteOn ..).ι) fun _ ⟨_,
    i, j⟩ ↦ (v ⟨_, (finiteSubring_total_and_exists_place _).1⟩ j).elim (⟨⊤, by tauto, i, ·⟩) (⟨⊥, by
    tauto, i, ·⟩)) m (T := placesFiniteOn z J C) (by ext; simp [placesFiniteOn, u]; tauto)).1
    (ih · · _ |>.forall.2 (o · |>.rec fun _ ⟨_, e⟩ ↦ by erw [e, _root_.map_sub, ← hκ, ← hκ]; tauto))
  cases m <;> [(obtain ⟨x, rfl, rfl⟩ := k x₁ x₂ (i _ (by
    erw [← hκ, ← hκ, e₁, e₂, ← map_comp_apply, ← map_comp_apply]; rfl)); use x);
    use 0] <;> exact t (Prod.ext ((hκ _ l₁.le.hom _).trans e₁) ((hκ _ l₂.le.hom _).trans e₂))
  have S := γ.rangeRestrict_surjective
  let B : aicSubrings γ := ⟨_, le_rfl, .of_surjective S⟩
  have T A x : x ∈ placesFiniteOn z ⊥ B.1 A := ⟨by simp [zeroPoints], fun _ ⟨a, e⟩ ↦
    ⟨⟨_, baseRingMap_mem_placeGraph a⟩, e⟩⟩
  exact (isCohomEquiv_iff_range (hg := mono_of_app_injective (by rintro _ ⟨⟨⟩⟩ ⟨⟩ ⟨⟩; rfl)) (U :=
    (placesFiniteOn ..).whisker _) (by ext _ ⟨⟩; exact ⟨fun ⟨y, e⟩ ↦ ⟨e ▸ y.1.2, (T ..).2⟩, (⟨⟨⟨_,
    ·.1⟩, ‹_›⟩, rfl⟩)⟩)).2 (by simpa [← map_comp] using! (((G ⊥ B).isCohomEquiv (isDomain (hI := by
    simp [isPrime_bot])) (isDomain (hI := map_isPrime_of_surjective S (le_maximalIdeal (ker_ne_top
    _)))) (homOfLe (by tauto)) (G _ B)).comp_iff.2 (IsCohomDense.isCohomEquiv .of_top_le))))).eqv
end

-- part: Lib.General.Geometry.ProperSchemes
section
/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Descent of torsion étale cohomology along v-covers; excision, transfer, limits (known
result; see Lib.Cohomology.Etale.ContinuityAtlas).

This file: A proper scheme has closed diagonal and valuative lifting from one affine atlas. -/

open CategoryTheory Limits AlgebraicGeometry CommRingCat Scheme Spec terminal Ideal TopologicalSpace
  PrimeSpectrum Set Cofan.IsColimit IsOpenImmersion Fintype prod
variable {X R} (s : X ⟶ Spec R)

/-- For X proper over Spec R there is a morphism a: Spec T → X, locally of finite type, through
which every morphism Spec O → X factors, for all rings O satisfying `IsComparableRing`. -/
lemma exists_finiteType_atlas [IsProper s] : ∃ T a, @LocallyOfFiniteType _ X a ∧ ∀ O,
    IsComparableRing (@id (carrier O)) → ∀ z, ∃ u, @map T O u ≫ a = z :=
  let U := X.affineCover.finiteSubcover (H := QuasiCompact.compactSpace_of_compactSpace s)
  ⟨_, inv (toSpecΓ _) ≫ Sigma.desc U.f, locallyOfFiniteType_comp (hg :=
    HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc inferInstance) .., fun O h z ↦ by
  choose m M l using fun x : Spec O ↦ exists_le_maximal _ x.2.1
  choose g n k using (exists_range_iff.1 <| isTopologicalBasis_basic_opens.isOpen_iff.1
    (z ⁻¹ᵁ Hom.opensRange _).2 ⟨_, M · |>.isPrime⟩ (U.covers _))
  choose e n h d using (exists_idempotent_dvd_of_notMem h (M _) <| n ·)
  let C x : Clopens (Spec O) := isIdempotentElemEquivClopens ⟨_, h x⟩
  have ⟨t, _⟩ := finite_cover_nhds (C · |>.isOpen.mem_nhds (by tauto))
  choose g l _ D using exists_disjointed_le (t.restrict C)
  have ⟨c⟩ := nonempty_isColimit_cofanMk_of (Opens.ι <| g · |>.toOpens)
    (by simp_all [Clopens.ext_iff, iUnion_subtype]) (D.mono (by simp [← Opens.coe_disjoint]))
  use preimage (desc c (fun x ↦ lift _ (Opens.ι _ ≫ z) (range_subset_iff.2 (k _ <| l x ·.2 ∘
    mem_of_dvd _ (d x))) ≫ Sigma.ι ..) ≫ toSpecΓ _), hom_ext c _ _ (by simp [-cofan_mk_inj]; simp)⟩

/-- If s: X → Spec R is a proper morphism of schemes, then the functor of points of X over R is
proper in the sense of `IsProperOver`. -/
lemma isProperOver_pointsToBase [IsProper s] :
  IsProperOver (pointsToBase s) := have := X.isSeparated_iff.2 (comp_from s ▸ {})
  ⟨fun C ⟨x⟩ ⟨y⟩ ↦ (exists_ideal_le_ker_iff_factors (diag X) (lift ..)).imp (by
    intros; simp_all [prod.hom_ext_iff, lift_fst, lift_snd]; exact ULift.up_inj),
                                    (exists_finiteType_atlas s).imp fun _ ⟨a, _, H⟩ ↦
    ⟨⟨a⟩, fun O z h ↦ ((IsProper.eq_valuativeCriterion.le _ _ s ‹_›).1.1.1 ⟨O, _, z.1,
    map (ofHom (.codRestrict _ _ h)), ⟨homEquiv.injective (by aesop)⟩⟩).elim fun ⟨⟨l⟩, _⟩ ↦
    (H _ isTest_of_preValuationRing.2 l.1).imp (by intros; simp_all; congrm ⟨$(l.2)⟩)⟩⟩
end
