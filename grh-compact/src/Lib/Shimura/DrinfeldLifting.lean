import Lib.Shimura.ComplexComparison

section
/-! Part of: Eichler–Shimura congruence relation for GU(1,n−1) at a split place: the pointwise step
(known result; see Lib.Shimura.CongruenceRelation.CongruenceStep).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Cartier's theorem; finite flat kernel is closure of its generic points. Arithmetic
consequences of a good prime: characteristic, uniformiser, coprimality. Reduced isogeny kernels on
one-dimensional torsion are cut by powers of one parameter. -/

open CategoryTheory AlgebraicGeometry TrivSqZeroExt DualNumber Algebra TensorProduct specOver Over
  Module

attribute [-simp] TensorProduct.algebraMap_apply

attribute [local simp] lift_apply_apply algebraMap_eq_inl' map_comp_assoc Commute.all

variable {V} [CommRing V] {A B : Over (Spec ⟨V⟩)} [AddObj A] [AddObj B]

/-- Cartier's theorem: let V embed in an algebraically closed field K of characteristic 0, and
Spec S, finite flat over V, be a subobject of a commutative group V-scheme stable under x −
y + z. Then V-algebra maps S → K detect non-zero elements. -/
lemma cartier K [Field.{0} K] [IsAlgClosed K] [CharZero K] [Algebra V K] [FaithfulSMul V K] {S}
  [CommRing S] [Algebra V S] [Module.Finite V S] [Flat V S] {ι : specOver V S ⟶ A} (_ : Mono ι)
  (h : ∀ {T} (x y z : T ⟶ _), ∃ w, w ≫ ι = x ≫ ι - y ≫ ι + z ≫ ι) {s} (n : s ≠ 0) :
  ∃ o : S →ₐ[V] K, o s ≠ 0 := (nullstellensatz_exists_le_ker ((Ideal.torsionOf_eq_top_iff ..).not.2
  ((map_ne_zero_iff _ (Flat.tensorProduct_mk_injective ..)).2 n))).imp'
  (liftEquivRight ..).symm fun c j z ↦ (exists_mem_colon_of_tangent rfl bot_le fun v l _ f ↦ by
  let t := (liftEquivRight V K S (K ⊗[V] S)[ε]).symm.trans (.ofBijective _ map_bijective)
  let μ := lift ⟨((ofId K K[ε]).comp c, ε), by simp⟩; let g := f - c f • 1
  choose ρ hz using (reindex_equiv t).2.1.1 (h (t (inlAlgHom ..)) (t ((ofId ..).comp c))
    (t ((lift ⟨(ofId .., ε), by simp⟩).comp v)))
  obtain ⟨⟨n, y, e⟩, H, G⟩ := (IsArtinianRing.of_finite K _).exists_pow_succ_smul_dvd g 1,
    map (fstHom ..) ≫= hz.trans (sub_add ..), specOver.map (μ.restrictScalars V) ≫= hz
  simp [t, μ, sub_eq_zero_of_eq, cancel_mono, map_bijective.1.eq_iff, AlgHom.ext_iff, *] at H G e
  simpa +zetaDelta [(by aesop : v = μ.comp ρ)] using (n.rec (by simp)
    fun n h s e ↦ by simpa [-nsmul_eq_mul] using h (n.succ •
    s * s * (ρ g).snd) (by grind [by simpa [by simpa using AlgHom.congr_fun (by aesop
    : (fstHom ..).comp ρ = 1)] using congr((ρ $e).snd)]) : ∀ s, s * g ^ n = 0 → c (s * (ρ g).snd) =
    0) (1 - g * y) (by grind)).choose_spec.elim (absurd <| j <| · ⟨_, z, rfl⟩)

/-- Let V be a valuation ring with fraction field ℂ, ψ: A → B a finite flat homomorphism over V,
B separated. If r: A → Y maps every torsion ℂ-point of ker ψ into a closed subscheme Z, it
maps every T-point of ker ψ into Z. -/
lemma ker_factors_of_points [ValuativeArc V] [IsSeparated B.hom] (ψ : A ⟶ B) [IsAdditive ψ]
  [IsFinite ψ.1] [Flat ψ.1] {Y Z j} [@IsClosedImmersion Z Y j] r (hr : ∀ s : specOver V ℂ ⟶ A,
  IsOfFinAddOrder s → s ≫ ψ = 0 → ∃ l, l ≫ j = s.1 ≫ r) ⦃T⦄ (z : T ⟶ A) (o : z ≫ ψ = 0) : ∃ l,
  l ≫ j = z.1 ≫ r := (exists_finite_kernel_ring ‹_›).elim fun _ ⟨ι, _, _, _, _, h⟩ ↦
  (h z o).elim fun z _ ↦ (exists_ideal_le_ker_iff_factors j (ι.1 ≫ r)).elim fun _ ⟨_, H⟩ ↦
  ((H (.id _)).1 fun _ s ↦ by_contra (cartier ℂ (mono_of_mono_left ι) (by aesop) · |>.choose_spec
  ((H _).2 (hr (specOver.map _ ≫ ι) (finite_multiples.1 ((Set.finite_range _).subset fun _
  ⟨_, e⟩ ↦ map_bijective.2.exists.1 (h _ (by aesop)))) (by simp [*])) s))).imp' (z.1 ≫ ·) (by aesop)

open Ideal CharP RingHom Pointwise CartesianMonoidalCategory NumberField Category Submodule
  CommRingCat Finset AddMonObj Fint Matrix

lemma isGoodAt_ker_spec {E} [Field E] [CMBase E] {D : PEL E} {k} [Field k] {ρ : _ →+* k} (h :
  D.IsGoodAt (ker ρ)) : Fact (ringChar k).Prime ∧ (ker ρ ≠ ⊥ ∧ ∃ c, ρ c = 0 ∧ c ≠ 0 ∧ ∃ t,
  t - 1 ∈ ker ρ ∧ t • ker ρ ≤ Ideal.span {c}) ∧ ∃ b : ℤ, ρ (D.β - b) = 0 ∧
  IsCoprime (D.β - b) (Star.star D.β - b) ∧ Ideal.span {D.𝔑} ⊔ ker ρ * Ideal.span {↑(ringChar k),
  Star.star D.β - b} = ⊤ := .imp_right (.imp_left fun h ↦ ⟨h, (IsDedekindDomain.exists_sup_span_eq
  (ker ρ).smul_le_right (mul_ne_zero h h)).imp fun _ e ↦ ⟨e.le (Ideal.mem_sup_right (by simp)),
  fun _ ↦ by simp_all [ker_ne_top], Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
  .of_finite le_rfl (by order)⟩⟩) (by grind [PEL.IsGoodAt, Fact, ringChar_of_prime_eq_zero,
  mem_ker, map_natCast, Ideal.mem_bot, Nat.cast_eq_zero, Nat.not_prime_zero])

variable {E} [Field E] [CMBase E] {D : PEL E} {V : ValuationSubring ℂ} {k} [Field k] {φ : V →+* k}
  {Z τ} {X : ThetaFamily D Z τ} {x : ThetaObject X _} (hw : D.IsGoodAt (ker x.baseHom)) {y :
  ThetaObject X _} (e : y.FullStructure) (ho : x.IsPullbackAlong (specMap φ) y) {C C'} [CommRing C]
  [Algebra k C] [CommRing C'] [Algebra k C'] (G : C →ₐ[k] C')

variable (x C) in
/-- For an object x over a field k and a k-algebra C, the O_E-module of C-points of its abelian
scheme killed by the kernel of O_E → k. -/
noncomputable abbrev placeTorsion :=
  torsionBySet (𝓞 E) (specOver k C ⟶ x.groupScheme) (ker x.baseHom)

/-- For a k-algebra map G: C → C', the induced O_E-linear map from C-points to C'-points of the
abelian scheme killed by the kernel of O_E → k. -/
noncomputable def placeTorsionMap : placeTorsion x C →ₗ[𝓞 E] placeTorsion x C' :=
  ⟨⟨fun ⟨y, _⟩ ↦ ⟨specOver.map G ≫ y, by simp_all [← ModuleObj.comp_smul]⟩, by simp⟩, by simp⟩

@[simp] lemma placeTorsionMap_comp {C''} [CommRing C''] [Algebra k C''] ψ (y : placeTorsion x C'') :
    placeTorsionMap (G.comp ψ) y = placeTorsionMap G (placeTorsionMap ψ y) :=
  Subtype.ext (map_comp_assoc ..).symm

/-- Let y be a full object over a valuation subring V of ℂ and ψ an isogeny from A_y to an
abelian scheme. If r: A_y → Y maps every torsion section of the full structure killed by ψ
into a closed subscheme Z, then it maps every point of ker ψ into Z. -/
lemma ker_factors_of_torsionPoint {B} [IsAbelianScheme B] (ψ : y.groupScheme ⟶ B) [IsIsogeny ψ]
  {Y Z j} (r : y.groupScheme ⟶ Y) [@IsClosedImmersion Z _ j] (hr : ∀ s, e.torsionPoint s ≫ ψ = 0 →
  ∃ l, l ≫ j = (e.torsionPoint s ≫ r).left) : ∀ ⦃T⦄ (z : T ⟶ y.groupScheme), z ≫ ψ = 0 → ∃ l,
  l ≫ j = (z ≫ r).left := have ⟨x, H⟩ := y.exists_isPullbackAlong ValuativeArc.genericPt
  let p := H.isGroupBaseChange.pointEquiv.symm
  ker_factors_of_points ψ r.1 fun s f ↦
    (x.exists_apply_eq_of_torsion (f := H.isGroupBaseChange.pullSection ∘ₗ e.torsionPoint)
    (p.injective.comp (bijective_restrict_genericPt.1.comp e.injective)) (p s)
    (f.exists_nsmul_eq_zero.imp fun _ ↦ by erw [← map_nsmul]; aesop)).rec fun t ↦ (p.injective · ▸
    fun h ↦ (hr t (bijective_restrict_genericPt.1 h)).imp' (ValuativeArc.genericPt ≫ ·) (by aesop))

attribute [local simp ←] Spec.map_comp Spec.map_comp_assoc map_smul Algebra.smul_def

attribute [local simp] algebraMap_eq_inl' cancel_mono Spec.map_inj CommRingCat.hom_ext_iff
  RingHom.ext_iff TrivSqZeroExt.ext_iff entrywise fst_sum snd_sum sub_eq_zero_of_eq vecMulVec
  Function.Embedding.punit specMap

/-- Let x be an object over a local ring R, and ρ: O_E → R → k kill β − b. The tangent vectors
at 0 of A_x over k contain a line on which O_E acts through ρ, and β̄ − b maps all tangent
vectors into it. -/
lemma exists_lie_line {R} [CommRing R] [IsLocalRing R] [Algebra R k] (x : ThetaObject X _) {ρ} (hρ :
    ρ = (algebraMap R k).comp x.baseHom) {b : ℤ} (hb :
  ρ (D.β - b) = 0) : let r := specOver.map (fstHom R k k)
  ∃ Z : k →+ (_ ⟶ x.groupScheme), Z 1 ≠ 0 ∧ (∀ m, r ≫ Z m = 0) ∧ (∀ a m, a • Z m = Z (ρ a * m)) ∧
    (∀ m, specOver.map ((TrivSqZeroExt.map (m • .id)).restrictScalars R) ≫ Z 1 = Z m) ∧ ∀ v,
    r ≫ v = 0 → ∃ m,
    (star D.β - b) • v = Z m := (X.signature b x).rec fun V ⟨z, m, ⟨J, M⟩, Y, ξ, l, u, E₁, E₂⟩ ↦ by
  intro r
  let p := x.isGroupBaseChange.pointEquiv (T := specOver R k[ε])
  have T {v} : IsInfinitesimal (ofHom (fstHom k k k).1) (p v) ↔ r ≫ v = 0 := .trans
    (x.isGroupBaseChange.pointEquiv.map_eq_zero_iff : _ ↔ IsInfinitesimal _ v)
    (eq_zero_iff_factors_zero_section.trans (.symm eq_zero_iff_factors_zero_section))
  let ⟨i, M⟩ := (M (φ := ofHom (algebraMap R k[ε])) rfl).imp_right (@· _ _ isSqZeroExt_fstHom)
  choose Z N e Q using by simpa [↓T, ExistsUnique, funext_iff, and_assoc] using fun a ↦
    p.bijective.existsUnique_iff.1 (J.existsUnique_tangentCoords_eq i isSqZeroExt_fstHom
    (Y · • inr a) (by simp))
  use .mk' Z fun a c ↦ by rw [← Q] <;> simp [*, ↓T],
    ne_of_apply_ne ((tangentCoords z · l) ∘ p) (by simp [e, u]), N, fun c a ↦ by
    apply Q; simp [*]
    simpa [*, -Q, ↓T, smul_smul, sum_smul, map_smul, mul_comm (Y _)] using! (congr($(E₁
      c) · • a)), fun a ↦ Q _ _ ((map_comp_assoc ..).trans (by convert N 1 <;> ext <;> simp))
    (by erw [J.tangentCoords_comp i (T.2 (N 1)) ((Over.map x).map (specOver.map _)) rfl]; simp [e]),
    fun v h ↦ ⟨∑ j, ξ j • snd (tangentCoords z (p v) j), by apply Q <;> simp [M, h, ↓T, map_smul,
    apply_ite, smul_sum, by simpa using J.map_tangentCoords_eq_zero i (T.2 h),
    eq_add_of_sub_eq E₂, by simpa [hρ, ThetaObject.baseHom] using hb]⟩

include ho

attribute [local simp] OverMorphism.ext_iff sub_smul pow_succ' specOver.map in
/-- Let y be full over V, reducing along V → k above a prime w ∋ β − b with β − b coprime to β̄
− b, and z a (β − b)^M-torsion point over a local k-algebra B with k-point π. One τ in ker π
serves all isogenies ψ from A_y to abelian schemes, injective families c of w-torsion
sections and ring maps G: B → B', with e the number of c_i through π(z): if υu = z, υ times
each torsion section in ker ψ is a c_i, and ψ(u) vanishes along G, then G(τ)^e = 0; if all
c_i lie in ker ψ and G(τ)^e = 0, then ψ(z) vanishes along G. -/
lemma exists_ker_parameter {b : ℤ} (hb : x.baseHom (D.β - b) = 0) (co : IsCoprime (D.β - b) (star
  D.β - b)) M {B} [CommRing B] [IsLocalRing B] [Algebra k B] (z : _ ⟶ y.groupScheme) (hz : (D.β -
  b) ^ M • z = 0) (π : B →ₐ[k] k) : ∃ τ, π τ = 0 ∧ ∀ ⦃A⦄ [IsAbelianScheme A] (ψ : y.groupScheme ⟶ A)
  [IsIsogeny ψ] ⦃C : Type⦄ (c : C ↪ torsionBySet (𝓞 E) _ (ker x.baseHom)) ⦃B'⦄ [CommRing B']
    (G : B →+* B') ⦃s :
  Spec ⟨B'⟩ ⟶ _⦄ (a : Over.mk s ⟶ (Over.map (specMap φ)).obj (specOver k B)),
    a.1 = specMap G → let t := G τ ^ Nat.card {s // toUnit _ ≫
    e.torsionPoint (c s).1 = (Over.map (specMap φ)).map (specOver.map π) ≫ z}; (∀ (υ : 𝓞 E) u,
    υ • u = z → (∀ s, e.torsionPoint s ≫ ψ = 0 → ∃ i, (c i).1 = υ • s) → (a ≫ u) ≫ ψ = 0 → t = 0) ∧
    ((∀ s, e.torsionPoint (c s).1 ≫ ψ = 0) → t = 0 → a ≫ z ≫ ψ = 0) := by
  algebraize [φ]; obtain ⟨F, ⟨Z, -, -, _, hs, H⟩, r, c, hc⟩ := y.finite_flat_surjective_smul
    (pow_ne_zero M.succ (co.ne_zero_or_ne_zero.rec _root_.id (by aesop))),
    exists_lie_line y ho.baseHom_eq_comp hb, co.pow_left (m := M.succ)
  choose S ι _ _ _ h₀ hι using exists_finite_kernel_ring F.2
  obtain ⟨⟨z', rfl⟩, _⟩ := hι z (by simp [mul_smul, *]), @free_of_flat_of_isLocalRing V S
  obtain ⟨γ, W, w⟩ := by simpa [Spec.map_surjective.exists] using homMk_surjective z'
  let o : S →ₐ[V] k := ⟨.comp π γ.hom, by simp [W, algebraMap_toAlgebra]⟩
  let p := specOver.map ((inlAlgHom V k k).comp o) ≫ ι
  have f T (v : T ⟶ _) := by simpa [-OverMorphism.ext_iff] using v ≫= h₀
  choose v₀ hu using specOver.map_bijective.2.exists.1 (hι (Z 1 + p) (by simp [p, *]))
  choose T K using forall_imp_iff_exists_imp.1 (@_root_.id (∀ T, (v₀ T).snd = 0))
  let τ := algebraMap k _ (o T) - γ T
  use τ, by simp +zetaDelta, fun A _ ψ _ C κ _ _ G s a ha ↦ ?_
  choose x Y using fun s ↦ by simpa using specOver.map_bijective.2.exists.1 (hι
    (toUnit (specOver V V) ≫ e.torsionPoint (κ s)) ((κ s).rec (by simp_all)))
  have hi : x.Injective := fun s t h ↦ κ.2 (Subtype.ext (e.injective (by simp [← Y, h])))
  let ϖ j a := algebraMap V S (x j a) - a
  have U a h := ((IsLocalHom.of_surjective π (⟨_, π.2 ·⟩)).1 (γ a) h).map G; let χ := G.comp γ.hom
  obtain ⟨⟨_, -, hJ⟩, _⟩ := exists_ideal_le_ker_iff_factors ζ[A].1 (ι ≫ ψ).1,
    Finite.of_injective x hi, @IsClosedImmersion.spec_of_quotient_mk ⟨S⟩
  use fun υ u hz C' h ↦ ?_, ?_ <;> simp [← Y, w, ha, ↓eq_zero_iff_factors_zero_section]
  · choose c f using fun j ↦ show ∃ a, χ (ϖ j a) ∣ if ∀ a, φ (x j a) = o a then G τ else 1
      by split; exacts [⟨T, by simp +zetaDelta [*]⟩, (not_forall.1 ‹_›).imp fun _ _ ↦
      (U _ (by simpa [ϖ, W])).dvd]
    simpa [prod_ite, Fintype.card_subtype, ← map_prod, show χ (∏ j, ϖ j (c j)) = 0 from
      le_ker_iff_factors.2 ((ker_factors_of_torsionPoint e ψ (υ • 𝟙 _) (C' · · |>.rec fun i g ↦
      ((le_ker_iff_factors (γ := x i)).1 (by simp [prod_eq_zero (mem_univ i), ϖ])).imp (by simp_all
      [← assoc, map_smul])) _ h).imp fun _ h ↦ (cancel_mono ι.1).1 (by simpa [w, ha, hz, χ] using
      h)) (Submodule.mem_span_singleton_self _)] using! univ.prod_dvd_prod_of_dvd _ _ (fun _ ↦ f ·)
  refine fun hC h0 ↦ (hJ χ).1 fun a ha ↦ zero_dvd_iff.1 (h0 ▸ univ.induction_on (motive := fun s ↦
    ∀ a, (∀ j ∈ s, x j.1 a = 0) → _ ^ #s ∣ χ a) (by simp) (fun j s n ih a h ↦ ?_) a
    fun j _ ↦ by exact (hJ _).2 (hC j) ha)
  choose ρ H u using by simpa [mem_colon, Ideal.mem_span_singleton] using
    (exists_mem_colon_of_tangent
    (o := o) (I := .span {ϖ j T}) (AlgHom.ext j.2) (by simp [ϖ]) fun v l n ↦ by
    choose a h using H (c • (specOver.map v ≫ ι - p)) (by simp [p, l])
    rw [← hs, smul_smul, mul_comm, eq_sub_of_add_eq' hc, ← add_left_inj, ← comp_add, ← hu] at h
    simp [by simpa [mul_smul, smul_sub, f, p, sub_add] using h, ϖ] at n ⊢
    tauto)
  choose b e using H a (by simp [h])
  erw [← (U ρ (by simpa)).dvd_mul_left, ← χ.map_mul, e]
  simpa [n] using mul_dvd_mul (by simp +zetaDelta [j.2, W]) (ih b fun i f ↦ by_contra
    fun hc ↦ n (j.ext (hi (by ext c; simpa [ϖ, h, f, hc, ne_zero_of_map (i.2 _ ▸ u)]
    using (map_dvd (x i) (e ▸ mul_dvd_mul_right (H (ϖ j c) (by simp [ϖ])) b)))) ▸ f :))

include hw

/-- Let x over k reduce a full y, w = ker(O_E → k) good, T = (E/O_E)ⁿ[w]. Some non-zero t in T
reduces to 0. For some additive ν: T → A_x[w](k), each z in A_x[w](B), B local, π: B → k,
has τ in ker π with τ^{#ν⁻¹(πz)} = 0 and, if πz = 0, z ≡ 0 mod τ. -/
lemma exists_param_pow_card_eq_zero : let T := torsionBySet (𝓞 E) _ (ker x.baseHom); ∃ ν :
    T →+ placeTorsion x k, (∃ t ∈ T, t ≠ 0 ∧ toUnit (Over.map (specMap φ) (specOver k k)) ≫
    e.torsionPoint t = 0) ∧ ∀ B [CommRing B] [IsLocalRing B] [Algebra k B] z (π : B →ₐ[k] k), ∃ τ,
    π τ = 0 ∧ τ ^ Nat.card {s // ν s = placeTorsionMap π z} = 0 ∧ (placeTorsionMap π z = 0 →
    ∀ C [CommRing C] [Algebra k C] (G : B →ₐ[k] C), G τ = 0 → placeTorsionMap G z = 0) := by
  obtain ⟨⟨-, ⟨-, c, hc, h0, t, ht, H⟩, b, hb, ⟨co⟩⟩, hp⟩ :=
    isGoodAt_ker_spec hw, ho.isGroupBaseChange
  obtain ⟨⟨Z, o, u, ⟨⟩⟩⟩ := exists_lie_line x rfl hb, y.finite_flat_surjective_smul h0
  use .mk' (fun ⟨s, h⟩ ↦ ⟨hp.pointEquiv.2 (toUnit _ ≫ e.torsionPoint s), by simp; simp_all
    [← ModuleObj.comp_smul]⟩) ?_ <;> simp [placeTorsionMap, hp.pointEquiv.symm_apply_eq]
  refine (iff_and_self.2 fun K ↦ o.imp_symm fun H ↦ (K _ (Z 1) (by simp_all) (fstHom ..)).rec
    fun τ ⟨_, h, K⟩ ↦ by simpa using K (u 1) _ (.id ..) (by rwa [u, Nat.card_eq_one_iff_exists.2
    ⟨⟨0, by simp⟩, by simpa [not_imp_not] using H⟩, pow_one] at h)).1 fun B _ _ _ z hz π ↦ ?_
  peel exists_ker_parameter e ho hb co 1 (hp.pointEquiv z) (by simp [*]) π with τ _ K
  use (K (c • 𝟙 _) (.refl _) (.id _) (𝟙 _) (by simp)).1 t (hp.pointEquiv z)
    (by simpa [sub_smul] using hz _ ht) (fun s hs ↦ by simpa [mul_smul] using ((Ideal.torsionOf _ _
    s).span_singleton_le_iff_mem.2 (e.injective (by simpa [map_smul] using hs)) <|
    H ⟨·, ·, mul_comm ..⟩)) (by simp [*]), fun h _ _ _ G g ↦
    hp.pointEquiv.map_eq_zero_iff.1 ((K (𝟙 _) (.punit 0) G ((Over.map _).map (specOver.map G))
    rfl).2 (by simp) (by simp [← hp.2.map_zero, IsGroupBaseChange.pointEquiv, ← h, g]))
end

section
/-! Part of: Deformations of the PEL object have at most n-1 parameters (known result; see
Lib.Shimura.Deformation.TangentBound).

This file: Linear functions on w-torsion with zero differential span at most n-1 dimensions.
Absolute Frobenius of a scheme; pull-back of line bundles is a power. Drinfeld's lifting lemma for
first-order deformations of the abelian object. -/

open Algebra Polynomial AlgebraicGeometry CategoryTheory Fintype IsAlgClosed LinearMap minpoly
  specOver Module Submodule RingHom TrivSqZeroExt Ideal Quotient FiniteField IsLocalRing
  CartesianMonoidalCategory CommRingCat LineBundle Spec
variable {E} [Field E] [CMBase E] {D : PEL E} {k} [Field k] [IsAlgClosed k] {Z σ} {Y :
  ThetaFamily D Z σ} {x : ThetaObject Y (Spec ⟨k⟩)}

open Fint in /-- If `x ↦ x ^ i` is `F`-linear on an algebraically closed extension of a field `F`
with `q` elements, then `i` is a power of `q`: the fixed points of
`x ^ (q i)` form an `F`-space. -/

lemma mem_powers_card_of_isLinearMap_pow F {i} [Field F] [Finite F] [Algebra F k]
    (h : IsLinearMap F (· ^ i : k → k)) : i ∈ Submonoid.powers (.card F) :=
  have s := galois_poly_separable _ (Fintype.card F * i) (ringChar.dvd (by simp))
  have e := ((card_rootSet_eq_natDegree s (splits _)).trans (X_pow_card_sub_X_natDegree_eq F
    ((Nat.two_le_iff _).2 (by simpa [one_lt_card.ne'] using h.map_zero)))).symm.trans
    (@card_eq_pow_finrank F ((h.mk' ∘ₗ frobeniusAlgHom F k).fixedSubmodule.copy (rootSet _ k) (by
    simp [Set.ext_iff, mem_rootSet, s.ne_zero, ← pow_mul])) _ _ _ _ (_))
  ⟨_, by simpa using (mul_pow_sub_one (fun _ ↦ by simp_all [one_lt_card.ne']) _).trans e.symm⟩

attribute [local simp ←] torsionBySet_eq_torsionBySet_span

/-- For x reducing a full y at a good place w, let f be natural semilinear maps A_x[w](C) → Hom_k(W,
C), C local k-algebras, vanishing on tangent vectors at 0. If no nonzero l ∈ W is killed for all
finite C, then dim W ≤ n − 1. -/
lemma finrank_le_of_placeTorsion (hw : D.IsGoodAt (ker x.baseHom)) {V : ValuationSubring ℂ} {φ :
  V →+* k} {y} (hy : x.IsPullbackAlong (specMap φ) y) (e : y.FullStructure) {W} [AddCommGroup W]
  [Module k W] (f : ∀ C [CommRing C] [Algebra k C] [IsLocalRing C], placeTorsion x C →ₛₗ[x.baseHom]
  W →ₗ[k] C) (hf : ∀ {C C'} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] [IsLocalRing C]
  [IsLocalRing C'] φ y l, f C' (placeTorsionMap φ y) l = φ (f C y l)) (hf₂ : ∀ y, specOver.map
  (fstHom k k k) ≫ y.1 = 0 → f _ y = 0) (H : ∀ l, (∀ C [CommRing C] [Algebra k C] [IsLocalRing C]
  [Module.Finite k C] y, f C y l = 0) → l = 0) : finrank k W ≤ card D.Index - 1 := by
  obtain ⟨⟨-, ⟨h0, p, i, ⟨hp⟩⟩, _, ⟨g⟩⟩, ν, -, hτ⟩ := isGoodAt_ker_spec hw,
    exists_param_pow_card_eq_zero hw e hy
  obtain ⟨⟨c, hc'⟩, Z, hZ, hX, h₁, ⟨h₃⟩⟩ :=
    IsDedekindDomain.exists_eq_span_pair (mem_ker.2 i) hp, exists_lie_line x rfl g
  obtain ⟨Γ, ι₀, _, _, _, k₀, hι₀⟩ :=
    exists_finite_kernel_ring (@IsFinite.of_comp _ _ _ (lift (p • 𝟙 x.groupScheme) (c • 𝟙 _)).1 (fst
    _ x.groupScheme).1 (by simp [↓← Over.comp_left, (x.finite_flat_surjective_smul hp).2]) _)
  simp [CartesianMonoidalCategory.hom_ext_iff] at k₀ hι₀
  let v : placeTorsion .. := ⟨ι₀, by simp [placeTorsion, *]⟩
  have U C [CommRing C] [Algebra k C] : (placeTorsionMap (C' := C) · v).Bijective := ⟨fun _ _ h ↦
    map_bijective.1 ((Over.mono_of_mono_left ι₀).1 _ _ congr($h)), by simpa [placeTorsionMap,
    placeTorsion, *, map_bijective.2.exists, Function.Surjective] using @hι₀ (specOver k C)⟩
  obtain ⟨⟨o, ho⟩, _⟩ := (U k).2 0, Finite.of_surjective _ (U k).2, (ker_isPrime _).isMaximal h0
  let u := placeTorsionMap (algHom k Γ (Localization.AtPrime (comap o ⊥))) v
  have inj {C} [CommRing C] [Algebra k C] : (placeTorsionMap (C' := C) · u).Injective :=
    fun _ _ _ ↦ Localization.algHom_ext _ ((U _).1 (by simpa))
  have fac {C} [CommRing C] [Algebra k C] [IsLocalRing C] (π : C →ₐ[k] k) : ∀ y,
    placeTorsionMap π y = 0 → ∃ φ, placeTorsionMap φ u = y := (U _).2.forall.2 fun φ _ ↦
    ⟨IsLocalization.liftAlgHom fun g : primeCompl (comap o ⊥) ↦ (IsLocalHom.of_surjective π (⟨_,
    π.2 ·⟩)).1 _ (congr($(@(U _).1 (π.comp φ) _ (by simp [*])) g).trans_ne g.2).isUnit, by simp [u,
    ← placeTorsionMap_comp, (U _).1.eq_iff, AlgHom.ext_iff, algHom]⟩
  have N : placeTorsionMap _ ⟨Z 1, by simp +contextual [h₁]⟩ = 0 := Subtype.ext (hX 1)
  obtain ⟨s, hΔ⟩ := fac _ _ N
  have hs a := congr((placeTorsionMap _ $hΔ).1).trans (h₃ a)
  let z := (fstHom ..).comp s
  obtain ⟨τ, hτ₀, hN, K⟩ := hτ _ u z
  choose! γ hγ using fun i h ↦ (mulLeft k (τ ^ i)).range_dualMap_eq_dualAnnihilator_ker.ge
    ((mem_dualAnnihilator z).2 fun a e ↦ (ker_eq_maximalIdeal z (⟨_, z.2 ·⟩)).ge
    (h ∘ (·.mul_left_eq_zero.1 e)))
  simp [DFunLike.ext_iff, z, *] at hγ hτ₀ hN K
  have hdiv a (ha : (s a).fst = 0) := by simpa [z, *, eq_zero_iff_dvd] using (congr($(
    @inj _ _ _ (mkₐ k (span {τ})) (.comp (ofId ..) z) (by simp [z, *])) a))
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow prime_X _).1 (dvd k τ (by simpa))
  let pb := PowerBasis.ofAdjoinEqTop (id ⟨_, monic_X_pow _, by simpa⟩) (by simpa [SetLike.ext_iff]
    using (antitone_nat_of_succ_le (f := (∀ s, τ ^ · * s ∈ k[τ])) (fun m h s ↦ (hdiv
    (s - z s • 1) (by simp [z])).rec fun d e ↦ eq_add_of_sub_eq e ▸ by simp [mul_add, h, pow_mem,
    ← mul_assoc, ← pow_succ, add_mem_cancel_left, k[τ].smul_mem]) bot_le fun _ ↦ by rw [hN]; simp))
  have hδ := by simpa [*] using K _ s ∘ ext hτ₀
  choose ρ hρ using fun a ↦ (⟨placeTorsionMap (pb.lift (a • τ) (hm.dvd'.rec (by simp +contextual
    [pb, _root_.smul_pow, by simpa [dvd_iff] using hm.dvd]))) u, by simpa [← placeTorsionMap_comp,
    ← hs, inj.eq_iff] using (pb.algHom_ext (by simp; ext <;> simp [pb, *]))⟩ : ∃ y,
    (placeTorsionMap s y).1 = Z a)
  let F := _ ⧸ ker x.baseHom
  let := Quotient.field (ker x.baseHom)
  algebraize [x.baseHom.kerLift]
  have lt {i} (h : τ ^ Nat.card F ^ i ≠ 0) : i < card D.Index - finrank F (placeTorsion x k) := by
    erw [lt_tsub_iff_right, ← pow_lt_pow_iff_right₀ (@Finite.one_lt_card F _ _), pow_add, ←
      natCard_eq_pow_finrank, ← card_torsionBySet_adelicTorsion h0, ← ν.ker.card_mul_index]
    simpa [AddSubgroup.index_ker, ν.range_eq_top.2 (hτ k · (.id ..) |>.rec (by simp +contextual
      [placeTorsionMap, Nat.card_ne_zero]))] using h ∘ (pow_eq_zero_of_le · hN)
  have := @lt 0 (hδ ∘ by simp +contextual)
  refine (((⟨_, Quot.ind (f k).2⟩ : _ →ₗ[F] _).flip.prod (.pi fun j : Set.Ioi (Fin.mk 0 this) ↦
    γ (Nat.card F ^ j.1.1) ∘ₗ f _ u)).finrank_le_finrank_of_injective (.of_ker _
    fun l h₀ ↦ H l fun C _ _ _ _ x ↦ ?_)).trans (by simp [finrank_linearMap, -card_fin]; omega)
  have h₁ : f _ u l = 0 := zero_dvd_iff.1 (hN ▸ (Nat.card _).rec (by simp) fun i ⟨g, h⟩ ↦ (em (τ ^ i
    = 0)).rec (by simp [h, ·]) fun hi ↦ h ▸ mul_dvd_mul_left _ (hdiv _ (by_contra fun hg ↦ by
    have key {y a} (hy : (placeTorsionMap s y).1 = Z a) : a ^ i = γ i (f _ y l) / (s g).fst := by
      obtain ⟨φ, rfl⟩ := fac z y ((placeTorsionMap_comp ..).trans (Subtype.ext (hy ▸ hX a :)))
      simp [← placeTorsionMap_comp, inj.eq_iff, ← hs, AlgHom.ext_iff] at hy
      cases hdiv (φ τ) (by simp [*])
      simp [*, mul_pow, mul_assoc, by simpa [*, mul_comm] using congr($(hy τ).snd)]
    obtain ⟨j, rfl⟩ := mem_powers_card_of_isLinearMap_pow F ⟨fun a b ↦ (@key (ρ a +
      ρ b) _ (by simp [*])).trans (by simp [key (hρ _), add_div]), Quot.ind fun a b ↦ by
      simpa [key (hρ _), ← mul_div] using! @key (a • ρ b) _ (by simp [*]; rfl)⟩
    simpa [h, hγ, hi, hg] using congr($h₀.2 ⟨⟨_, lt hi⟩, j.pos_of_ne_zero (by
      simpa [·, *] using congrArg snd (hf s u l))⟩))))
  let π := lift.comp (C := k) (mkₐ k (maximalIdeal C))
  obtain ⟨φ, e⟩ := fac π (x - placeTorsionMap (ofId ..) (placeTorsionMap π x))
    (by simp [↓← placeTorsionMap_comp, ↓map_sub])
  simpa [hf, h₁, hf π x l ▸ congr($h₀.1 _)] using congr(f C $e l).symm

variable {k : _} {l} [Field k] [CharP k l] [Fact l.Prime] (f : ℕ) (X Y : Over (Spec ⟨k⟩))

/-- If Spec B is a scheme over a field k of prime characteristic l, then l = 0 in B. -/
lemma natCast_eq_zero_of_over_charP {l B} [CharP k l] (s : Spec B ⟶ Spec ⟨k⟩) :
  (l : B) = 0 := by simp [CharP.cast_eq_zero, ← map_natCast (preimage s).1]

/-- For a scheme X over a field k of prime characteristic l, the absolute l^f-Frobenius X → X,
acting on B-valued points through x ↦ x^{l^f} on B. -/
noncomputable def absFrobenius := (exists_hom_of_cover LineBundle.one (fun _ _ t _ ↦ specMap
  (frobPow (natCast_eq_zero_of_over_charP (t ≫ X.hom)) f) ≫ t)
  (by simp_rw [← Spec.map_comp_assoc]; congr! 2; aesop)).choose

lemma comp_absFrobenius {B} t : t ≫ absFrobenius f X =
  specMap (frobPow (natCast_eq_zero_of_over_charP (B := B) (t ≫ X.hom)) f) ≫ t :=
  Classical.some_spec₂ (t ≫ · = _) (by tauto)

lemma absFrobenius_comm g : absFrobenius f X ≫ g = g ≫ absFrobenius f Y :=
  hom_ext_of_cover LineBundle.one (by simp [← Category.assoc, comp_absFrobenius])

lemma absFrobenius_apply x : absFrobenius f X x = x := by simpa [X.1.fromSpecResidueField_apply]
  using (congr($(comp_absFrobenius f X (X.1.fromSpecResidueField x)) default))

lemma picClass_pull_absFrobenius {ι L} (h : @IsLinearSystem _ ι L) : l ^ f • L.picClass =
  (L.pull (absFrobenius f X)).picClass := picClass_pow
  _ ▸ by apply picClass_eq_of_le (fun _ ↦ ·) <;> simp_all [LineBundle.pow, comp_absFrobenius,
  IsLinearSystem, PointFn.IsRegularOn, of_carrier, LandsIn, LE.le, absFrobenius_apply]

open Over Ideal.Quotient Scheme DualNumber NumberField ThetaObject Obj IsGroupBaseChange
variable {E k : _} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ : _} {Y :
  ThetaFamily D Z σ} {x₀ : ThetaObject Y _} {x : _} {x'} (hq :
  IsPullbackAlong (sqZeroReduction k k) x₀ x) (hq' : IsPullbackAlong (sqZeroReduction k k) x₀ x')

/-- The T-points y, y' of the lifts x, x' of x₀ to k[ε] have equal images in the abelian scheme
of Y on affine T-schemes where ε = 0. -/
@[local simp] def AgreeModEps T y y' := ∀ B (b : Spec B ⟶ _) (t :
  (Over.mk b).map (sqZeroReduction ..) ⟶ T), x.isGroupBaseChange.pointEquiv (t ≫ y) =
  homMk (𝟙 (Spec B)) ≫ x'.isGroupBaseChange.pointEquiv (t ≫ y')

lemma exists_isSqZeroExt_mod_eps {C} (s : Spec C ⟶ _) : ∃ B ψ b, Spec.map ψ ≫ s =
  b ≫ sqZeroReduction k k ∧ @IsSqZeroExt C B ψ ∧ (∀ a, ψ a = 0 ↔ preimage s ε ∣ a) ∧ ∀ {B t b},
  t ≫ s = b ≫ sqZeroReduction k k → ∃ l : Spec B ⟶ _, l ≫ Spec.map ψ = t := ⟨_, ofHom _, Spec.map
  _ ≫ s ≫ specMap _, homEquiv.injective (by aesop), ⟨Ideal.Quotient.mk_surjective, by simp_all
  [eq_zero_iff_dvd, dvd_def, mul_mul_mul_comm _ _ (preimage s ε), ← map_mul]⟩, eq_zero_iff_dvd _,
  fun {_ t _} w ↦ map_preimage t ▸ le_ker_iff_factors.1 (by simpa using! congr(preimage $w ε))⟩

lemma AgreeModEps.ringChar_smul_and_smul_eq_zero {T y} (h : AgreeModEps hq hq T y 0) :
  ringChar k • y = 0 ∧ ∀ {ψ}, x.baseHom = .comp ψ x₀.baseHom →
  ∀ ⦃b : ℤ⦄ ⦃c⦄, x₀.baseHom (D.β - b) = 0 → x₀.baseHom c = 0 → ((star D.β - b) * c) • y = 0 := by
  constructor <;> intros <;> ext <;> apply hom_ext_of_cover .one fun _ _ t _ ↦ ?_
    <;> let s := t ≫ T.hom <;> choose _ ψ _ w _ _ using exists_isSqZeroExt_mod_eps s <;> let τ :=
    (Over.mk s).homMk t <;> have v : IsInfinitesimal ψ (τ ≫ y) :=
    (by simpa [IsInfinitesimal, eq_zero_iff_factors_zero_section] using h _ _ (homMk _ w ≫ τ))
    <;> exact congr($((by simp [v.nsmul_injective_and_eq_zero x.smoothOfRelativeDimension
    (mkIdTerminal.from _), mul_smul, v.smul, *, natCast_eq_zero_of_over_charP
    (s ≫ (specOver k _).hom), (x.exists_tangent_log _).choose_spec (ψ := ψ)] : τ ≫ _ = τ ≫ 0)).1)

/-- Drinfeld's lifting lemma. Let x, x' deform x₀ over k[ε], and let c in O_E kill all
infinitesimal points of A_x'. Then some homomorphism F: A_x → A_x' reduces to c, and F(y) =
c·y' whenever y and y' agree modulo ε. -/
lemma drinfeld_lift {c : 𝓞 E} (hc : ∀ T y, AgreeModEps hq' hq' T y 0 → c • y = 0) : ∃ F,
  IsAdditive F ∧
  hq.schemeMap ≫ F = c • hq'.schemeMap ∧ ∀ T y' y, AgreeModEps hq' hq T y' y → y ≫ F = c • y' := by
  choose V z ha hV using (exists_isEtaleChart · Y.relative_dim)
  choose C j _ _ hj using
    (@exists_affine_mem_range_and_range_subset _ · (x.toFamily.1 ⁻¹ᵁ _) (ha _))
  choose F h K using by simpa using (exists_hom_of_rel (c • 𝟙 _) (AgreeModEps hq' hq _) (fun a h ↦
    (h · · <| · ≫ a)) (by aesop) (by aesop) (.ofArrows _ j) (zariskiPrecoverage_le_fpqcPrecoverage _
    (by aesop)) fun _ _ ⟨a⟩ ↦ (exists_isSqZeroExt_mod_eps (j a ≫ _)).elim fun _ ⟨ψ, _, e, hψ, _,
    H⟩ ↦ (hV _ (Spec.map ψ ≫ j a ≫ x.toFamily.1) _ (fun _ _ ↦ hj a ⟨_, rfl⟩) (by simp [reassoc_of%
    e, *]) (hψ.1.1.comp_left _).choose_spec).imp' x'.isGroupBaseChange.pointEquiv.2
    fun _ w _ _ t ↦ (H t.w).rec fun _ ↦ (by ext; simp [pointEquiv, ← ·, w.1]))
  use F, h, K _ _ _ fun _ _ _ ↦ by ext; simp [pointEquiv, IsPullbackAlong.comp_toFamily], K
end
