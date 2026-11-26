import Lib.Shimura.NormalGeneration
import Lib.Shimura.ThetaStructure
import Lib.Shimura.ComplexComparison
import Lib.Shimura.UniformisationExists
import Lib.Shimura.ThetaTorus
import Lib.Shimura.ThetaFamily

section
/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Serre: sections of high powers of a very ample bundle are forms. -/


open MvPolynomial AlgebraicGeometry Scheme CategoryTheory MorphismProperty Filter Set Submodule
  LineBundle Spec Limits.pullback
attribute [-simp] pull_opens pull_transition
variable {k F ι} [CommRing k] [IsNoetherianRing k] [Finite ι]

/-- Saturation: let x be a finite family in a commutative k-algebra F, k noetherian, with x_r = 1.
For all large D, if for each i some f·x_i^N is a form of degree D + N in x, then f is a form
of degree D. -/
lemma eventually_mem_formSpan_of_mul_pow [CommRing F] [Algebra k F] (x : ι → F) {r} (hr : x r = 1) :
  ∀ᶠ D in atTop, ∀ f, (∀ i, ∃ N, f * x i ^ N ∈ formSpan k x (D + N)) →
  f ∈ formSpan k x D := let T := formSpan k x
  have M j {m f} : f ∈ T m → _ ∈ T m.succ := (mul_mem_mul · (subset_span ⟨j, rfl⟩))
  let φ := aeval (R := k) ((Polynomial.X * ·) ∘ .C ∘ x)
  let I c : Ideal _ := ⟨⟨⟨{p | ∀ n, (∀ i, (φ p).coeff n * x i ∈ T n) ∧ (c < n → (φ p).coeff
    n ∈ T n.pred)}, by simp_all [add_mul, add_mem]⟩, by simp⟩, fun q p h ↦ by
    apply q.induction_on <;> (try rintro _ _ _ ⟨⟩) <;>
    simp_all [φ, mul_right_comm _ _ p, ← mul_assoc, add_mul, add_mem, smul_mem, C_mul']⟩
  mem_atTop_sets.2 ((WellFoundedGT.monotone_chain_condition ⟨I, fun _ _ _ _ ↦
    forall_imp (by lia)⟩).imp fun c hc D e f ↦ by
  choose N h
  induction' N using WellFoundedLT.fix with N ih generalizing D f
  have H j : f * x j ∈ T D.succ := by
    cases z : N j; simpa [z] using M j (h j)
    exact ih _ (update_lt_self_iff.2 z.ge) _ e.step _ (by grind [M j <| h ·])
  have ⟨p, g, E⟩ := (map_homogeneousSubmodule_eq_formSpan ..).ge (H r)
  have : φ p = _ :=
    (eval₂_mul_of_isHomogeneous g ..).trans congr(_ * $(E ▸ aeval_algebraMap_apply ..))
  simpa [*] using (hc _ e.step).ge (by aesop : p ∈ _) D.succ)

/-- Serre's theorem: let N be a projective embedding of an integral scheme A over a field, p :
A' → A a base change to a noetherian ring k. For large m, the degree m monomials in the
coordinates span H⁰((p^*N)^m) over k. -/
lemma eventually_span_coordSection [Field F] {A : Over (Spec ⟨F⟩)} [IsIntegral A.1] {N :
  LineBundle _ ι}
  (A' : Over (Spec ⟨k⟩)) (hN : N.IsProjEmbedding A.hom) {p b} (Q : IsPullback p A'.hom A.hom b) :
  ∀ᶠ m in atTop, ∀ h : ((N.pull p).pow m).IsLinearSystem, span k (range (coordSection h)) = ⊤ := by
  let ζ := A.1.fromSpecResidueField (genericPoint _)
  obtain ⟨_, ⟨_, _, ξ, E⟩, _ : Flat p, i, I⟩ := (isSchemeTheoreticallyDominant_iff_isDominant ζ).2
    ⟨fun _ ↦ by simp [ζ, range_fromSpecResidueField]⟩, @exists_isPullback_SpecMap _ _ p
    (of_isPullback Q.flip inferInstance) _ ζ, of_isPullback Q.flip inferInstance, N.exists_landsIn ζ
  algebraize [(Spec.preimage (ξ ≫ A'.hom)).1]
  let v : PointFn _ →ₐ[k] _ := by use! (· _ ξ) <;> tauto
  have Y j : v ((N.pull p).transition i j) = _ := E.w ▸ (hN.1.1 ..).1 _ _ I
  obtain ⟨hN, hi : LandsIn ξ ((N.pull p).opens i)⟩ := hN.of_isPullback Q, (E.w ▸ I.comp _ :)
  refine (eventually_mem_formSpan_of_mul_pow (v ∘ _) (transition_self _ _ _ _ hi)).mono fun m H h ↦
    top_unique fun ⟨t, ⟨u, w⟩, _⟩ _ ↦ (apply_mem_span_image_iff_mem_span (f :=
    v.toLinearMap ∘ₗ .domRestrict (.proj fun _ ↦ i) _) (.of_ker _ fun ⟨s, ⟨a, d⟩, _⟩ e ↦
    H0_ext fun {l} ↦ (·.ext_of_dominant (E.isoPullback.1 ≫ fst ..) · .one (by simp +contextual [hi,
    map_surjective.forall, a _ _, d l fun _ ↦ i, landsIn_iInf, hi.comp, pow,
    (id e : s .. = 0)])))).1 (span_mono (by simp [subset_def, mem_pow_iff_prod,
    @Classical.skolem (Fin m), ← funext_iff, ← map_prod]; tauto) ((span_pow ..).le
    (H (t ..) fun j ↦ if z : IsUnit (N.transition i j _ ζ) then ?_ else ⟨1, by aesop⟩)))
  obtain ⟨hj, -, _, s, -, V⟩ := (hN.1.2 hi _).1.2 (Y j ▸ z.map _), hN.exists_affine_chart j
  choose P e using s.exists.1 ((u _).mono le_iInf_const).exists_ofSection
  rw [w _ fun _ ↦ j] <;> simp [landsIn_iInf, hi, hj, ← e, pow, V]
  exact ⟨_, (map_homogeneousSubmodule_eq_formSpan ..).le
    ((exists_homogenization (isHomogeneous_X _ j) P le_add_self).imp
    fun Q ⟨q, E⟩ ↦ ⟨q, congr(Q.eval₂ _ $(funext (hN.1.isSection · |>.2 _ _ _ _ hi hj))).trans (by
    simp [eval₂_mul_of_isHomogeneous q, ← aeval_def, E, transition_self, hj]; ring!)⟩)⟩
end

section
/-! Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre.
The form here holds over any valuation ring of the complex numbers (not noetherian, any rank), but
only for maps of complex tori that multiply a theta polarisation, whose kernel is killed by a unit
of the ring, by an integer. The map and the identity of bundle classes extend together, and points
extend by properness. Source: S. Bosch, W. Lütkebohmert, M. Raynaud, Néron Models (1990), 1.2/8 and
4.4/1; G. Faltings, C.-L. Chai, Degeneration of Abelian Varieties (1990), I.2.7; L. Moret-Bailly,
Pinceaux de variétés abéliennes, Astérisque 129 (1985), II.3.5.

This file: Polarisation-multiplying isogenies of complex tori extend to abelian schemes over
valuation rings. -/


open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Over Category LineBundle PointFn
variable {V ι κ O} [FinComplexSpace V] [CommRing O] [ValuativeArc O] {A A' :
  Over (Spec ⟨O⟩)} [AddObj A'] {s' : V →+ (_ ⟶ A')} [Finite κ] [IsAbelianScheme A] [Finite ι] (u :
  Uniformisation A V) {N : LineBundle _ ι} {B χ θ} (h : HasThetaCoords u.L (atGeneric
  u.expMap) N B χ θ) [IsPosRiemann B] (k₀ : ∀ l ∈ u.L, s' l = 0) {n : ℕ} (hn : IsUnit (n : O)) (H :
  ∀ a ∈ B.dualLattice, n • a ∈ u.L ∧ ∃ Φ, IsTranslationLift N (u.expMap a) Φ) [IsProper A'.hom] {M :
  LineBundle _ κ} (hM : M.IsProjEmbedding A'.hom)
include h k₀ hn H hM
attribute [local simp ←] comp_left Pic.pull_picClass Pic.pull_comp

attribute [local simp] IsSection IsLinearSystem IsRegularOn landsIn_iInf pow in
/-- Let the homomorphism π: A' → A carry s' (zero on L) to u; N and the embedding M have one
positive theta type; ν*π*N ⊗ M^{n²} ≅ ν*M ⊗ π*N^{n²} (ν = n, a unit); nL^∨ ⊂ L; translations
by u(L^∨) fix N. Then π has a section e with e∘u = s', e*M ≅ N. -/
lemma exists_section_of_hasThetaCoords π [IsAdditive π] {f ν m} (m0 : n ^ 2 = m) (F : ∀ z, s' z ≫
  π = u.expMap z) (t : HasThetaCoords _ (atGeneric s') M B χ f) (g : (n • 𝟙 A').left = ν) (hw :
  (((N.pull π.left).pull ν).mul (M.pow m)).picClass =
  ((M.pull ν).mul ((N.pull π.left).pow m)).picClass) :
  ∃ e, (∀ z, u.expMap z ≫ e = s' z) ∧ (M.pull e.left).picClass = N.picClass ∧ e ≫ π = 𝟙 A := by
  have ⟨hν, F'⟩ : (∀ z, atGeneric s' ((n : V →L[ℂ] V) z) = atGeneric s' z ≫ ν) ∧ ∀ z,
    atGeneric u.expMap z = atGeneric s' z ≫ π.1 := by simp [atGeneric, F, ← g]
  obtain ⟨⟨w, hw⟩, ⟨Γ, p, P, _, hP, D⟩, d, v, m0 : m ≠ 0⟩ := picClass_eq_iff.1 hw,
    exists_reduced_closure
    (atGeneric s'), isSeparatingFamily_atGeneric u.4, h.pull 1 F' fun _ ↦ id, by aesop
  obtain ⟨⟨γ, γ0, r, e, Z⟩, _, -, -, κ, G⟩ := exists_sections_of_translation_stable (N := ⊤) u h hn
    (by simp_all) (by simp) t.3 _ (ne_of_apply_ne (· 0) (t.4 0).ne_zero.choose_spec),
    d.2.surjective (p ≫ π.1) P (by grind), ((v.pull _ hν).mul (t.pow _)).riemannForm_eq_of_isFrame
    ((t.pull _ hν).mul (v.pow _)) hw (t.holomorphicAt hM)
  have ⟨W, c, I⟩ := exists_picClass_eq_pull_hyperplane (p ≫ π.1) (r · |>.1.2.1) fun i K _ ζ o ↦
    by_contra fun z ↦ Z K (ζ ≫ p ≫ π.1) fun z₀ hz j a ↦ by_cases ((r j).1.2.2 a _ _) fun ha ↦ by
    have ⟨T, E, c, C⟩ : ∃ T, T ≫ ν = ν ∧ (∀ x, atGeneric s' x ≫ T = atGeneric s' (x + z₀)) ∧
      π.1 ≫ (translation (u.expMap z₀)).1 = T ≫ π.1 :=
      ⟨(translation (s' z₀)).1, by simp [atGeneric, ← g, ← comp_nsmul _, ← map_nsmul, *, -g]⟩
    let Q := M.mul (N.pull π.1)
    obtain ⟨⟨⟨b, b₁, b', i'⟩, _⟩, u, ⟨_, Y, J, X'⟩, _⟩ := (M.mul ((M.pull T).mul (Q.pull ν))
      ).exists_landsIn (ζ ≫ p), (hw.2 · ⟨K⟩), t, (r · |>.1.2.1)
    let φ b i j := w ((i', fun _ ↦ b), b', fun _ ↦ i) * ((r j).1.1 i ^ m).pull π.1
    simp [IsHomogCoords, C, Q, IsFrame] at *
    refine .mp ?_ (@D.pointFn_ext _ _ _ (p ⁻¹ᵁ (Q.opens (b, i) ⊓ T ⁻¹ᵁ Q.opens (b₁,
      a) ⊓ ν ⁻¹ᵁ Q.opens (b', i'))) ((φ b i b * (M.transition b₁ j ^ m).pull T).pull p)
      ((φ b₁ a j).pull (p ≫ T)) ?_ ?_ (by simp +contextual [
      Q, φ, G, e, ← assoc, hP, c, ← hν, h.4 .., X', ← F', (h.3 _).2, (J _).2, H _ hz, Y.ne_zero,
      mul_pow, div_pow, field]) _ ζ ?_) <;> simp +contextual [Q, φ, *, reassoc_of% E]
  exact (d.exists_map_of_coords (ProjSpace.isLinearSystem_hyperplaneBundle.pull W) hM
    (h.4 · |>.ne_zero.elim fun i x ↦ by
    simpa [IsHomogCoords, *, -F', field] using! I i _ _ ((h.4 ..).1.2 x.isUnit)) t.4).imp
    fun e ⟨h, E⟩ ↦ ⟨(bijective_restrict_genericPt.1 <| h ·), E ▸ c.symm, d.hom_ext (by grind)⟩

attribute [-simp] lift_left
attribute [local simp ←] fst_left snd_left

/-- Let A = V/Λ over O and s': V → A'(O) additive killing Λ, with embeddings N, M obeying the
parallelogram law and theta coordinates of positive type (B, χ), resp. (μB, χ^μ). If Λ^∨ maps into
K(N) and nΛ^∨ ⊂ Λ, n a unit, then s' comes from a homomorphism ψ with ψ^*[M] = μ[N].

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. -/
lemma exists_hom_of_hasThetaCoords (hN : N.IsProjEmbedding A.hom) (c : N.picClass.ParallelogramLaw)
  (c' : M.picClass.ParallelogramLaw) {μ θ'} (h' : HasThetaCoords _ (atGeneric s') M
  (μ • B) (χ ^ μ) θ') : ∃ ψ, IsAdditive ψ ∧ (∀ z, u.expMap z ≫ ψ = s' z) ∧ M.picClass.pull ψ.left =
  μ • N.picClass := by
  have ⟨k, hm⟩ : ∃ k, IsUnit (↑(μ + .succ k) : O) := by
    by_contra! H; simpa using (IsLocalRing.maximalIdeal O).sub_mem (H μ.succ) (H μ)
  have ⟨e, he, C, i⟩ := exists_section_of_hasThetaCoords (s' :=
    .mk' (fun z ↦ lift (u.expMap z) (s' z)) (by bound)) u (h.pow _)
    (by aesop) (mod_cast hm.mul hn) ?_ ((hM.of_isPullback (.flip (.of_hasPullback ..))).mul (hN.pow
    ?_)) (fst ..) rfl ?_ (add_smul μ _ B ▸ pow_add χ .. ▸ (h'.pull 1 ?_).mul ((h.pow k.succ).pull 1
    ?_)) rfl (by linear_combination (norm := (simp; module)) (μ • congr($(pull_nsmul_eq_sq_smul c _
    ).pull (fst _ A').1) - congr($(pull_nsmul_eq_sq_smul c' _).pull (snd A _).1)))
  use e ≫ snd .., isAdditive_of_universal ((@isSeparatingFamily_atGeneric _ _ _ _
    (by simp [-fst_left]; infer_instance) _ _ _
    (homEquivToProd.symm.surjective.comp (u.4.prodMap u.4))).hom_ext ?_), ?_, (by simp_all
    [add_smul]) <;> simp [reassoc_of% comp_add, ← comp_add _, ← map_add, reassoc_of% he]
  all_goals simp_all [atGeneric, exists_isTranslationLift_iff, mem_dualLattice_nsmul, mul_nsmul,
    c.nsmul_class_pairing, ← comp_nsmul, ← map_nsmul]
end

section
/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family) (known
result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Schematic density of points passes to stalks and to fibre products. Coordinates locally
regular combinations of a linear system form a system of same class. Closure of theta points over
the base is flat with reduced fibres. -/

section

open CategoryTheory AlgebraicGeometry Limits pullback Set Scheme Spec Pullback Over PointFn Filter
variable {S} [IsReduced S] {A B : Over S} {V W J} [Finite J] {ξ : J → (_ ⟶ S)}
  {η : W → (Spec ⟨ℂ⟩ ⟶ S)} [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]

omit [IsReduced S] in
/-- Let A be reduced, z: A → S, s ∈ S, and x_w dense complex points of A with finitely many images
in S. Then A ×_S Spec O_{S,s} is reduced, and the lifts of the x_w to it are dense. -/
lemma isSeparatingFamily_stalk {A z x} [IsReduced A] (d : @IsDenseFamily W A x) (hx : (range (x · ≫
  z)).Finite) s : IsSeparatingFamily fun n : Σ' w ψ, map ψ ≫ S.fromSpecStalk s = x w ≫ z ↦ lift _ _
  n.2.2.symm := ⟨@isReduced_of_isReduced_stalk _ (⟨(fst z _).stalkMap_surjective · |>.forall.2
  (by simp [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩), (fst z _).isEmbedding.dense_iff.2
  fun y ↦ (((mem_closure_iff_frequently.1 (d _)).and_eventually (z.continuous.tendsto _
  (range_fromSpecStalk.le ((range_fst ..).le ⟨y, rfl⟩) (hx.eventually_all.2 fun p _ ↦
  eventually_imp_distrib_right.2 (specializes_iff_mem_closure (x := p _).2 ·.mem_closure))))).mono
  fun | _, ⟨⟨w, rfl⟩, b⟩ => ⟨_, ⟨⟨w, S.presheaf.stalkSpecializes (b _ ⟨w, rfl⟩ rfl) ≫ _, by
  simpa [-Hom.comp_base] using Spec_stalkClosedPointTo_fromSpecStalk _⟩, rfl⟩, by
  erw [← Hom.comp_apply, lift_fst]⟩).mem_closure⟩

lemma stalk_eq_zero_of_dense (hξ : IsDenseFamily ξ) {x} a (h : ∀ n : Σ' i ψ,
  map ψ ≫ S.fromSpecStalk x = ξ i, n.2.1 a = 0) : a = 0 := by simpa using ((isSeparatingFamily_stalk
  hξ (toFinite _) x).pointFn_ext (f := fun _ y ↦ preimage (y ≫ snd ..) a) (by simp [IsRegularOn])
  (isRegularOn_ofSection 0) (by simpa [lift_snd]) _ (inv (snd (𝟙 _) _)) landsIn_top)

open MonoidalCategory IsSchemeTheoreticallyDominant LocallyOfFiniteType CartesianMonoidalCategory

/-- Let S be reduced, locally noetherian, with a dense finite set of complex points; A, B flat,
locally of finite type, A reduced. If y_w : T_w → B separate B and e_w(v) : T_w → A separate
A ×_S T_w, the (e_w(v), y_w) separate A ×_S B (`IsSeparatingFamily`). -/
lemma IsSeparatingFamily.prod [IsLocallyNoetherian S] [Flat A.hom] [Flat B.hom] {y : ∀ w,
  .mk (η w) ⟶ B} {e : ∀ _, V → (_ ⟶ A)} (k : IsSeparatingFamily (y · |>.1)) (hξ :
  IsDenseFamily ξ) (r : IsReduced A.left) (h : ∀ w, IsSeparatingFamily fun
  v ↦ lift _ (𝟙 _) (e w v).w) : IsSeparatingFamily fun z : W × V ↦ (lift (e _ z.2) (y z.1)).1 := by
  let j := A.hom.smoothLocus.ι
  obtain _ := k.1, isLocallyNoetherian A.hom, isLocallyNoetherian B.hom,
    (j ≫ A.hom).smoothLocus_eq_top_iff.1 (by simp [j, ← j.preimage_smoothLocus_eq]), @of_isDominant
    _ _ j ⟨((dense_iff_closure_eq.2 genericPoints.closure).mono ((fun k ↦ @.of_perfectField _ _
    k.toField (IsLocalHom.isField (stalkMap_injective_of_flat ..) k).toField (_) (@.ofCharZero _ (_)
    (not_forall.1 (one_ne_zero ∘ stalk_eq_zero_of_dense hξ 1)).choose.2.1.1.charZero)
    (stalkMap ..)) ∘ isField_stalk_of_closure_mem_irreducibleComponents _ ·)).denseRange_val⟩ _
  use isReduced ((pullbackRightPullbackFstIso _ _ j).inv ≫ snd ..), (k.2.preimage (Hom.isOpenMap
    _)).induction (fun t ⟨w, a⟩ ↦ (by simpa [range_map, whiskerLeft_left] using ⟨_, a⟩ : t ∈ range
    (A ◁ y w).1).choose_spec ▸ map_mem_closure (by fun_prop) ((h w).2 _) fun _ ⟨q, o⟩ ↦ o ▸
    ⟨⟨w, q⟩, congr($(lift_whiskerLeft (e ..) (𝟙 _) _).1 _).symm⟩) (by simp)

end

open CategoryTheory PointFn LineBundle AlgebraicGeometry Limits MvPolynomial Scheme RingHom Flat
  pullback Over

/-- Let w false, w true be vectors at dense complex points ξ of reduced Z, each entry locally a
regular function times a Q-indexed sum of the other's entries. If w false coordinatises a
linear system M, w true coordinatises one of the same class. -/
lemma exists_isLinearSystem {Z J Q X M} [Fintype J] [Fintype Q] {ξ : X → (_ ⟶ Z)} (w : _ → X →
  J → ℂ) (sep : IsSeparatingFamily ξ) (hM : IsLinearSystem M) (blk : ∀ a,
  M.IsHomogCoords (ξ a) (w false a)) (h : ∀ b j s, ∃ U, s ∈ U ∧ ∃ e : Q → _, ∃ c, IsRegularOn c U ∧
  ∀ a, LandsIn (ξ a) U → c _ (ξ a) * ∑ q, w (!b) a (e q) = w b a j) :
  ∃ N, IsLinearSystem N ∧ (∀ a, N.IsHomogCoords (ξ a) (w true a)) ∧ N.picClass = M.picClass := by
  choose U _ e c _ _ using h true
  let σ j (k : J × (J → Z)) := c j (k.2 j) * ∑ q, M.transition k.1 (e j (k.2 j) q)
  refine ((M.mul (LineBundle.pi (LineBundle.mk (opens := U ·) 1
    (by aesop)) ∅)).exists_picClass_eq_pull_hyperplane (𝟙 _) (s := σ) (fun j ↦ ⟨?_, fun i k _ _ ↦
    (sep.pointFn_ext (g := _ * _) ?_ ?_ ?_ _ _ <| landsIn_inf.2 ⟨·, ·⟩)⟩) fun k _ _ _ n ↦ (h false
    k.1 _).elim fun _ ⟨v, e, c, _⟩ ↦ Function.mtr (by simp_all) (sep.pointFn_ext (g := 1) (f := c *
    ∑ q, σ (e q) k) ?_ ?_ ?_ _ _ (landsIn_inf.2 ⟨n, landsIn_iff_mem.2 v⟩))).elim fun f r ↦ ⟨_,
    ProjSpace.isLinearSystem_hyperplaneBundle.pull f, (ξ · |> exists_landsIn _ |>.elim
    (forall_imp ?_ <| r.2 · _ _)), ?_⟩ <;> simp_all [σ, IsRegularOn, IsLinearSystem, IsHomogCoords,
    ← mul_assoc, ← Finset.sum_mul, landsIn_iInf]; grind

attribute [local simp] lift_fst lift_snd specMap

/-- At the K-point t, in every chart c, the vanishing ideal of the part of Z ⊂ K^J with v_c ≠ 0,
scaled to v_c = 1, satisfies `IsCutOut` for the points P(t). -/
def IsCutOutAt {J I K} [Field K] {S} r i σ (P : I → LineBundle S J) t (Z : Set (J → K)) := ∀ l : I →
  _, (∀ a, LandsIn t ((P a).opens (l a))) → ∀ c, IsCutOut r i σ c (fun a j ↦
  (P a).transition (l a) j ⟨K⟩ t) (⨅ v ∈ {v ∈ Z | v c ≠ 0}, ker (eval (v · / v c)))

/-- Let S be reduced, finitely many of the η n dense, r > 1; assume `IsCutDegree`,
and `IsCutOutAt` at η n for the image of θ n and at a geometric specialisation of
every point. Then some flat closed A ⊂ ℙ^J_S has reduced fibres over η n, in which the θ n z
are dense, and at such specialisations. -/
lemma exists_flat_closure {J W ι I κ S r i σ} [Finite J] [Finite ι] [IsReduced S] (j : ι → κ) {η :
  κ → _} (D : IsDenseFamily fun n ↦ η (j n)) {P : I → _} (B : ∀ a,
  (P a).IsLinearSystem) (H : 1 < r) (Y : IsCutDegree J i r σ) {θ : κ → W → J → ℂ} (hθ : ∀ n z,
  θ n z ≠ 0) (h : ∀ n, IsCutOutAt r i σ P (η n) (.range (θ n))) (cl : AllSpecializeTo S
  fun t ↦ ∃ Z, IsCutOutAt r i σ P t Z) : ∃ A N, ∃ e : ∀ n, W → (mk (η n) ⟶ A),
  IsProjEmbedding N A.hom ∧ Flat A.hom ∧ (∀ n z, IsHomogCoords N (e n z).left (θ n z)) ∧
  (∀ n, IsSeparatingFamily fun v ↦ (lift _ (𝟙 _) (e n v).w :)) ∧ AllSpecializeTo S (fun t ↦
  IsReduced (pullback A.hom t)) ∧ IsSeparatingFamily fun s : κ × W ↦ (e s.1 s.2).left := by
  choose χ ν using (Function.ne_iff.1 <| hθ · ·)
  choose p o g using fun w : ι × W ↦
    ProjSpace.exists_isHomogCoords (η (j w.1)) (ν (j w.1) w.2).isUnit
  choose Z ε x₀ _ E b d using exists_reduced_closure p
  simp [← E, ← IsHomogCoords.pull_iff, -Prod.forall] at o g
  generalize ε ≫ _ = z, pull _ ε = N, (isProjEmbedding_projSpace).comp ε = M at *
  choose T u Q F V using fun {R b c} ↦
    (M.of_isPullback (.of_hasPullback z b)).exists_affine_chart (R := R) c
  let O {R} b := (AffineOpenCover.ofIsOpenCover _ (cover _) (@T R b)).openCover
  have L {R b c A} [CommRing A] {φ : _ →+* A} : ker (@u R b c) ≤ RingHom.ker φ ↔ ∃ y,
    LandsIn y (N.opens c)
    ∧ y ≫ z = specMap (φ.comp C) ≫ b ∧ ∀ j, N.transition c j _ y = φ (X j) := ⟨fun h ↦ by
    obtain ⟨ψ, ⟨⟩⟩ := (u.liftOfSurjective Q).symm.surjective ⟨φ, h⟩
    exact landsIn_fromSpec T (specMap ψ) |> fun i ↦ ⟨_, landsIn_preimage.1 i, by simp [ext (f :=
      ψ.comp _) (ofSection_map_fromSpec .. ▸ V i ·), condition]⟩, fun ⟨y, a, k, h⟩ f _ ↦
    by simpa [*, mem_ker.1, ← hom_eval₂] using (V (lift_fst _ _ k ▸ a :) f).symm⟩
  choose G k R using fun {k} [Field k] {t 𝔭} (h₀ : IsCutOutAt (K := k) r i σ P t 𝔭) ↦ show _ ∧ _ ∧
    _ by
    have a := Spec_stalkClosedPointTo_fromSpecStalk t
    set c := fromSpecStalk ..
    choose _ q using (P · |>.exists_landsIn c)
    have v F ψ := funext₂ fun a j ↦ @((B a).1 _ j).1 _ F ψ _ (q a)
    have K m := map_eq_and_flat_of_isCutOut _ (ker (@u _ c m)) (stalk_eq_zero_of_dense D) H Y
      (v .. ▸ (a ▸ h₀) _ (q · |>.comp _) m) (fun n ↦ v .. ▸ (n.2.2 ▸ h _) _ (q · |>.comp _) m)
      fun f ↦ .trans ⟨by tauto, fun h ↦ (ofSection_map_fromSpec T _ (𝟙 _)).symm.trans
      (((isSeparatingFamily_stalk d ((Set.finite_range (η ∘ j)).subset (by simp_all)) _).pointFn_ext
      (isRegularOn_ofSection _) (isRegularOn_ofSection 0) h _ _ (landsIn_fromSpec T _)).trans
      (by simp))⟩ (by simp +contextual [*, g .., division_def, PSigma.forall, @forall_comm W])
    have e m := (K m).1.trans (eq_of_forall_ge_iff (b := ker (@u _ t m)) (·.mk_ker ▸ by
      simp [↓Ideal.map_le_iff_le_comap, ↓comap_ker, ↓L, comp_assoc, a]))
    use fun y ↦ (comp_iff_of_bijective_left ⟨stalkMap_injective_of_flat .., Hom.stalkMap_surjective
      _ y⟩).1 (Hom.stalkMap_comp .. ▸ @stalkMap _ _ _ (condition.symm.subst (.comp (hf :=
      HasRingHomProperty.instIsZariskiLocalAtSource.of_openCover (O c) fun m ↦ F ▸ SpecMap_iff.2
      (respectsIso.1 _ (quotientKerEquivOfSurjective Q) (flat_algebraMap_iff.2 (K m).2))) ..)) y),
      e, @IsReduced.of_openCover _ (O t) fun c ↦ (affine_isReduced_iff _).2
      ((ker_isRadical_iff_reduced_of_surjective Q).1 (e c ▸ fun _ h ↦ h.elim (by simp_all)))
  choose x q using fun n v ↦ ((L.1 ((k (h n) _).ge.trans (iInf₂_le _ ⟨⟨v, rfl⟩, ν n v⟩))).elim
    fun y ⟨b, e, E⟩ ↦ ⟨homMk y (by simp [e, MvPolynomial.eval]), by grind [M.1.2 b, IsHomogCoords,
    eval_X, homMk_left]⟩ : ∃ x : mk (η n) ⟶ mk z, N.IsHomogCoords x.1 (θ n v))
  exact ⟨_, N, x, M, .of_stalkMap _ fun x ↦ (cl (z x)).elim fun _ ⟨_, _, _, s, _, h⟩ ↦
    ((Pullback.range_fst ..).ge (range_fromSpecStalk.ge s)).choose_spec ▸ G h _, q, fun n ↦ ⟨R (h
    n), fun y ↦ by_contra fun H ↦ have ⟨c, a⟩ := TopologicalSpace.IsOpenCover.exists_mem (cover _) y
    have ⟨f, F, Y⟩ := Q.exists.1 (T.exists_basicOpen_le (V := ⟨_, isClosed_closure.1⟩) ⟨y, H⟩ a)
    by simpa using ((k (h n) c).le (by simpa using fun v _ ↦ by_contra fun _ ↦ F (landsIn_iff_mem.1
      (by rw [landsIn_basicOpen]; simpa [q .., *]; simp [q .., *])) (subset_closure ⟨v, rfl⟩)) ▸
      Y :)⟩, by peel 6 cl; tauto, b,
    d.mono (by simp [fun w ↦ M.eq_of_isHomogCoords ((x ..).w ▸ o w) (g w) (q _ _)])⟩
end

section
/-! Known result: Normal generation of sections on abelian varieties, kept under good reduction.
Only degrees that are powers of one integer r are treated here, over a rank-one valuation ring of
the complex numbers. Powers of the sup-norm ball of theta functions are the balls, reduction keeps
the ranks, and no cohomology or vanishing theorem is used. Source: S. Koizumi, Theta relations and
projective normality of abelian varieties, Amer. J. Math. 98 (1976); T. Sekiguchi, J. Math. Soc.
Japan 29 (1977) for characteristic p; G. Kempf, Multiplication over abelian varieties, Amer. J.
Math. 110 (1988).

Known result: Riemann's theta relations. They are stated here in one variable for the theta
coordinates of a PEL torus, with multipliers in the ring of integers of a CM field in place of the
matrix with entries ±1/2. The proof uses Schur orthogonality for the theta group. Source: C.-L.
Chai, Riemann's theta formula (2014), Theorem 1.2; A. Nagano, On Riemann type relations for theta
functions on bounded symmetric domains of type I, arXiv 2301.09243 (2023), Theorem 1.1; D. Mumford,
On the equations defining abelian varieties I, Invent. Math. 1 (1966) §3; G. Kempf, Linear systems
on abelian varieties, Amer. J. Math. 111 (1989) 65–94.

This file: Riemann's theta relation; largest theta constants; reduction cut out by level points. -/

open Complex Finite LatticeForm Finset Fint Function Module MvPolynomial NNReal NumberField
  PeriodMap Submodule thetaSpace

variable {V E k K : Type} [FinComplexSpace V] {v} [Field E] [CMBase E] {D : PEL E} {g ℓ} (x :
  ThetaTorus D g ℓ V) [Fintype K] (a : K → 𝓞 E) {μ μ' : K → D.T} {w t} (p : K → 𝓞 E × 𝓞 E)

namespace ThetaTorus

attribute [-simp] iInf_neg map_eq_zero map_smul nsmul_eq_mul

noncomputable instance : Module (𝓞 E) D.T := module ⟨_, by
  rintro a ⟨y⟩ h; exact (D.mem_T _).2 fun z k ↦ by simpa [xiForm, ↓star_smul] using
    ((D.mem_T y).1 h (algebraMap E (𝔸f E) (star a) • z) (torsionClass.ker.smul_mem (star a) k))⟩

/-- For pairs p_l = (a_l, b_l) in O_E: ∑ ā_l a_l = r and ∑ ā_l b_l = 0, with r the degree in the
data D. -/
def IsRiemannTuple (D : PEL E) := ∑ l, star (p l).1 * (p l).1 = D.r ∧ ∑ l,
  star (p l).1 * (p l).2 = 0

/-- The family of coefficient pairs, on two copies of the index set, made of (0, second entry of
k_l) on the first copy and of p_l on the second. -/
def doubledCoeffs (k : K → 𝓞 E × _) := Sum.elim (0, k · |>.2) p

/-- For pairs p_k = (a_k, b_k) in O_E, μ_k in T and w in V, the function z ↦ ∏_k θ_{μ_k}(a_k z +
b_k w) on V. -/
noncomputable def thetaProduct (μ : K → _) w z := ∏ k,
  x.thetaCoord (μ k) (x.intAction (p k).1 z + x.intAction (p k).2 w)

attribute [local simp] thetaShift_apply exp_add exp_neg Ideal.Quotient.eq_zero_iff_mem map_eval
  PeriodMap.torsionLift bicharacter thetaCoord_ne_zero periodPoint
  PeriodMap.sub_mem_periodLattice_iff adjoint thetaProduct Valuation.pos_iff canonicalMultiplier
  div_eq_inv_mul mul_pow thetaNorm_pow thetaRanks

/-- Let ∑ ā_k a_k = r, ∑ ā_k b_k = 0, ∑ ā_k μ_k = t, y over T. If U_{a_k u} θ_{μ_k} = χ(a_k u)
e(⟨a_k y, μ_k⟩) θ_{μ'_k} for all k, then U_u P_μ = χ(u)^r e(⟨y, t⟩) P_{μ'} in degree rB, P =
`ThetaTorus.thetaProduct`. -/
lemma thetaShift_thetaProduct {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {u y}
    (k : y ∈ x.latticeOver D.T) (h : ∀ k, x.B.thetaShift (x.intAction (p k).1 u) (x.thetaCoord
  (μ k)) = (x.multiplier (x.intAction (p k).1 u) * x.B.riemannPhase (x.intAction (p k).1 y)
  (x.torsionLift (μ k))) • x.thetaCoord (μ' k)) z : (D.r • x.B).thetaShift u (x.thetaProduct p μ w)
  z = x.multiplier u ^ D.r * x.B.riemannPhase y (x.torsionLift t) * x.thetaProduct p μ' w z := by
  obtain ⟨⟨⟩⟩ := x.dualLattice_periodLattice.ge k (∑ k, x.intAction _ (x.torsionLift _) -
    x.torsionLift t) (by simp [intAction, ← toRealVectors_smul, ← map_sum]; simp [← ht]; rfl),
    (congr(x.B u <| x.intAction $(hp.1) ·)), congr(x.B u (x.intAction $(hp.2)
    w)), congr(x.B.riemannForm (x.intAction (D.rescaledBeta * $(hp.1)) u) u)
  simp [← ofReal_inj, sub_eq_iff_eq_add', map_sub, riemannForm_def,
    mul_sum, ↓mul_left_comm D.rescaledBeta] at *
  simpa [*, ← exp_sum, add_right_comm, mul_add, ← zsmul_eq_mul', ← mul_sum, ← exp_nsmul,
    mul_left_comm D.r.cast,
    nsmul_eq_mul] using congr(∏ k, $(h k) (x.intAction (p k).1 z + x.intAction (p k).2 w))

/-- Riemann's theta relation. For P, P' the products `ThetaTorus.thetaProduct` of pairs p, q
satisfying `ThetaTorus.IsRiemannTuple`, with one w and ∑ āμ = ∑ ā'μ': |T| P'_{μ'}(0) P_μ(z) = ⌊√[T :
T[r]]⌋ ∑_{s∈T} P_{μ−as}(0) P'_{μ'+a's}(z).

Known result: Riemann's theta relations. -/
lemma riemann_relation {p} (hp : IsRiemannTuple p D) (ht : ∑ k, star (p k).1 • μ k = t) {q} (hq :
  IsRiemannTuple q D) (h : ∑ k, star (q k).1 • μ' k = t) [Fintype D.T] z : Fintype.card D.T *
  x.thetaProduct q μ' w 0 * x.thetaProduct p μ w z = (D.rTorsion.relIndex D.T).sqrt * ∑ s,
  x.thetaProduct p (μ - (·.1 • s) ∘ p) w 0 * x.thetaProduct q (μ' + (·.1 • s) ∘ q) w z := by
  obtain ⟨m, r, _⟩ := x.latticeOver_mono (S := D.rTorsion) D.torsion_mem_lagrangian,
    x.hasGoodReduction_trivial.4.ne_bot, (x.thetaCoord_mem_thetaSpace · |>.1)
  obtain ⟨_, d⟩ := x.discreteTopology_latticeOver_lagrangian.of_subset m,
    ((dualLattice_nsmul_le r fun _ ↦ (x.nsmul_mem_latticeOver r).1).antisymm fun _ h
    _ ↦ by simpa using h _ ∘ (x.nsmul_mem_latticeOver r).2).trans x.dualLattice_periodLattice
  rw [← x.relIndex_latticeOver, ← (((x.isAppellHumbert_of_le m).nsmul _).shift _
    _).sum_shift_mul_shift (hp := x.isPosRiemann.nsmul r) _ (⟨_, d.ge <| x.torsionLift_mem ·⟩)
    (d.le ·.2 |>.elim fun y ⟨h, e⟩ ↦ ⟨.addLeft ⟨_, h⟩, by simp [← e, ← map_add, ← map_sub]; simp⟩)
    ⟨_, ?_⟩ ⟨_, ?_⟩] <;> try exact ⟨by fun_prop [thetaProduct], fun l
    h z ↦ by erw [mul_right_comm, ← x.thetaShift_thetaProduct ‹_› ‹_› (x.latticeOver_mono
    D.lagrangian_le_T (m h)) fun k ↦ thetaShift_of_mem (x.thetaCoord_mem_thetaSpace_lagrangian _) (m
    (by grind [=_ nsmul_mem_latticeOver, PEL.rTorsion, intAction_mem_periodLattice, =_
    map_nsmul]))]; simp [field]⟩
  congr with s; have d := congr($(x.riemannPhase_rescaledBeta_eq (x.torsionLift_mem s)
    (x.torsionLift_mem s) rfl) ^ D.r)
  have L y h p μ := (x.thetaShift_thetaProduct (p := p) (K := K) (w := w) (μ' := μ +
    (·.1 • ⟨frameTorsionClass g y, h⟩) ∘ p) · rfl (x.intAction_rescaledBeta_mem_latticeOver le_rfl
    (by tauto)) (u := x.Q _) fun k ↦ by simpa [intAction, smul_comm (cmEmbedding (p k).1.val),
    add_comm] using (x.thetaShift_thetaCoord (s := (p k).1 • ⟨_, h⟩) (map_smul ..) _))
  erw [← map_neg, ← map_neg, L] <;> simp [*, two_mul, add_mul, field, sub_eq_add_neg] at *
  simp [← smul_neg, sq_eq_one_iff.2 d]; ring!

/-- Under good reduction and v(|T|) = 1, every s in T is u + (s − u) with v(θ_u(0))
v(θ_{s−u}(0)) ≥ v(θ_t(0))² for all t: both theta constants have the largest valuation. -/
lemma exists_peak (G : HasGoodReduction x.B x.multiplier v D.r) (hv : v (Nat.card D.T) = 1) s :
    ∃ u, ∀ w ∈ [u, -u, s - u], ∀ t, v (x.thetaCoord t 0) ≤ v (x.thetaCoord w 0) := by
  obtain ⟨T, ⟨o, ho⟩, ⟨η, H⟩, ⟨r, e⟩, u, hu⟩ :=
    (sizes.of_mem_thetaSpace G.1 <| x.thetaCoord_mem_thetaSpace ·), exists_max (v <|
    x.thetaCoord · 0), x.exists_thetaCoord_sign_smul (-1), Nat.exists_eq_add_of_lt D.three_le_r,
    exists_max fun u ↦ v (x.thetaCoord (s - u) 0) ⊓ _
  obtain ⟨N, le⟩ := G.hasMultiplicativeNorm (φ :=
    _ * _) (by simpa using! mul_shift_mem_sizes (T s) (T (D.r • o - s)) 0)
    ⟨G.nsmul r.succ_ne_zero, pow (x.thetaCoord_mem_thetaSpace 0) _⟩, (size_le_iSup <| T ·)
  simp [-Subtype.forall, sizeAt, field, thetaNorm_thetaCoord,
    G.hasMultiplicativeNorm (T _) (T _)] at le N hv H
  have A := not_lt.1 fun q ↦ q.not_ge ((le_of_mul_le_mul_right (congr(v (x.thetaCoord
    o 0) * $N).ge.trans (mul_iSup_le fun z ↦ ?_)) (by simp [G.thetaNorm_pos])).trans (hu u))
  · use u, List.forall_mem_cons.2 ⟨fun _ ↦ by grw [← neg_zero, H, H, map_mul, ho, map_mul, A,
      inf_le_right], by simp [(ho _).trans, A.trans]⟩
  have := congr(v $(x.riemann_relation (w := 0) (p := const _ (1, 0)) (μ' := const _ o) (μ :=
    Option.elim'
    (D.r • o - s) (Sum.elim ![s, 0] (0 : Fin r → _))) ?S ?_ ?S rfl z)).trans_le ((v.leSubmodule
    _).smul_mem (Nat.cast _) (sum_mem fun t ↦ by simp; grw [ho, ← min_mul_max _ (v _), hu, ho (s -
    t), ho (-t), le])) <;> simp [IsRiemannTuple, ↓sizeAt_pow, sizeAt, *, field, pow_add, q.pos] at *
  linarith

/-- Let the theta torus x satisfy `HasGoodReduction` for v, with residue field k. If the N_l have at
t the reduced theta vectors of the level points as coordinates, then `IsCutOutAt`
holds at t for the reductions of all theta vectors (θ_s(z))_s. -/
lemma isCutOutAt_reduction [Field k] {φ : v.valuationSubring →+* k} (hφ : Surjective φ) (G :
  HasGoodReduction x.B x.multiplier v D.r) {q p : _ → _} (hq : ∀ z, IsIntegralCoords (x.thetaCoord
  · z) (q z)) (hp : ∀ l : D.levelTorsion, IsIntegralCoords (x.thetaCoord · (x.torsionLift l)) (p l))
  {S t} {N : _ → LineBundle S _} (hx : ∀ l, (N l).IsHomogCoords t (φ <| p l ·)) :
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) N t (.range (φ ∘ q ·)) := fun l hl c ↦ by
  obtain ⟨T, R, H, Y, U⟩ := pow (x.thetaCoord_mem_thetaSpace c), G.pow, @eval₂_mul_of_isHomogeneous,
    @isHomogeneous_X_pow, (x.formSpan_eq_normBall G c · ▸ (LinearMap.range_domRestrict ..).trans
    (map_homogeneousSubmodule_eq_formSpan ..))
  choose e _ E using (lt_iff_exists_add.1 <| @Nat.pow_lt_pow_succ _ · G.one_lt)
  have W j := ext fun _ ↦ mem_dualLattice_nsmul.trans
    (x.dualLattice_periodLattice ▸ x.nsmul_mem_latticeOver (pow_ne_zero j G.one_lt.ne_bot))
  have P j {I} {a p : I → _} k (h : ∀ b, IsIntegralCoords (x.thetaCoord · (a b)) (p b)) :=
    (R j).thetaNorm_lt_iff_coords (T _) (by simp) (p :=
    fun l ↦ (·.1.eval (p l))) (U j) k (h · |>.imp' _ fun s ⟨e, t, h⟩ ↦ ⟨fun f ↦ by simpa
    [eval_eq, aeval_def, eval₂_eq, e] using (H f.2 (algebraMap ..) s⁻¹ _), ⟨_, Y t _⟩, by simp [h]⟩)
  have Q j (f : homogeneousSubmodule ..) := P _ (⟨·.1, by simp⟩) hq ⟨_, E j ▸ f.2.mul (Y c _)⟩
  simp [*, G.hasMultiplicativeNorm (.of_mem_thetaSpace (f :=
    aeval _ (Subtype.val _)) (R _).1 ((U _).le ⟨_, rfl⟩).1) ⟨G.nsmul _,
    _⟩, -Subtype.forall, add_smul, ↓thetaNorm_pow, pow_add, G.thetaNorm_pos
    (x.thetaCoord_mem_thetaSpace c) (x.thetaCoord_ne_zero c), LatticeForm.thetaNorm, ne_of_gt,
    or_iff_not_imp_right, ↓← v.mem_maximalIdeal_iff, ← IsLocalRing.ker_eq_maximalIdeal φ hφ] at P Q
  have L d : Surjective fun f : homogeneousSubmodule D.T _ d ↦ (⟨_, f.2.map φ⟩ :
      homogeneousSubmodule ..) | ⟨g, h⟩ => ⟨⟨_, sum_mem fun m a ↦ isHomogeneous_monomial
    (surjInv hφ (g.coeff m)) (h.degree_eq_sum_deg_support a).symm⟩, by simp [surjInv_eq]⟩
  use by simp +contextual, fun j ↦ ?_, fun _ a ↦ Subtype.forall'.2 ((L _).forall.2 fun f ↦ by
   simpa +contextual [Q, hx .., ((hx ..).1.1 (hl _)).ne_zero, H f.2, mul_comm (φ _)] using! P
    _ (W _ ▸ fun ⟨_, y, h, rfl⟩ ↦ ⟨⟨_, D.degree_spec.2 _ a _ h⟩, by simp⟩) hp f)
  erw [← (imageMod ..).span_eq, map_coe, Set.image_eq_range, ← (L _).range_comp, (R
    _).finrank_reduction_eq (T _) (by simp) (U _) hφ (y := ⟨⟨_, by simp⟩, by
    simp [Algebra.smul_def]; tauto⟩) fun f ↦ by simp +contextual [Q, H f.2], ← (finrank
    ..).sqrt_eq', (R _).finrank_sq_eq_relIndex (hp := (R _).isPosRiemann).2.1, W,
    relIndex_latticeOver]; simp

/-- The family of pairs in O_E consisting of (1, 0) twice, (c, 1), (1, −c̄), and (a_l, 0) for
every l. -/
noncomputable def _root_.paddingTuple bicharacter := @Sum.elim Bool _ _ (fun _ ↦ (1, 0))
    (Sum.elim (cond · (bicharacter, 1) (1, -star bicharacter)) (a ·, 0))
end ThetaTorus
end

section
/-! Known result: complex uniformisation of PEL abelian varieties, Appell–Humbert and finite class
number. Here the signature is (1,n-1) at one place and definite elsewhere. The torus comes from the
exponential of a compact commutative complex Lie group, and Appell–Humbert is proved only for a very
ample class obeying the parallelogram law. Source: J. S. Milne, Introduction to Shimura Varieties
(2005/2017), Theorem 8.17 and Lemma 5.12; R. Kottwitz, Points on some Shimura varieties over finite
fields, J. AMS 5 (1992) §8; G. Shimura, On analytic families of polarized abelian varieties and
automorphic functions, Ann. Math. 78 (1963); A. Borel, Some finiteness properties of adele groups
over number fields, Publ. IHES 16 (1963); D. Mumford, Abelian Varieties §§1–2; L. Breen, Fonctions
thêta et théorème du cube, LNM 980 (1983). -/
seal Finset.univ Finset.sum Finset.prod

open CategoryTheory CartesianMonoidalCategory Complex Over LineBundle PointFn NormedAddGroup
attribute [-simp] lift_left fst_left snd_left
attribute [local simp] fieldEq DFunLike.ext_iff funext_iff exp_add norm_smul pow
attribute [local simp ←] comp_left exp_nat_mul Pic.pull_picClass

/-- Appell–Humbert theorem: if V/L ≅ A(ℂ) is a uniformisation and N a projective embedding of A
whose class is symmetric and satisfies the parallelogram law `Pic.ParallelogramLaw`, the coordinates
of N are theta functions for L of some type (B, χ) with positive Riemann form.

Known result: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class
number. -/
lemma Uniformisation.appell_humbert {A} [AddObj A] {ι V} [Finite ι] [FinComplexSpace V] (u :
  Uniformisation (O := ℂ) A V) {N} (hN :
  @IsProjEmbedding _ _ ι N A.hom) (c : N.picClass.ParallelogramLaw) : ∃ B χ θ,
  HasThetaCoords u.L (atGeneric u.expMap) N B χ θ ∧ IsPosRiemann B := by
  obtain ⟨e, L, s, hL, O⟩ := u; dsimp at O ⊢
  let X := (((N.pull (fst A A).1).mul (N.pull (snd A A).1)).pow 2).mul
    ((N.pull (fst A A + snd A A).1).mul (N.pull (fst A A - snd A A).1)).inv
  have ⟨w, (⟨o, n⟩ : X.IsFrame w)⟩ := picClass_eq_iff.1 (by simpa using! (c _ _).symm)
  choose J K using fun x : ComplexPoint A ↦ N.exists_landsIn x.1; have T {x} := hN.1.2 (K x)
  have h0 {x y} : LandsIn (lift x y).1 (X.opens (fun _ ↦ (J x, J y), J (x + y), J (x - y))) := by
    simp [X, K]
  let Φ z w := N.transition (J (e w)) (J (e z)) _ (e w).1
  have {z} : Φ z z = 1 := N.5 _ _ _ (K _)
  have Z {z} : ∀ᶠ w in _, Φ z w ≠ 0 :=
    ((O z).1 (isRegularOn_ofSection 0) (K _)).1.mono (by simp [Φ, T _])
  have hf j {z} := ((O z).1 (hN.1.1 ..).1 (K _)).2.congr (Z.mono fun _ ↦ ((T _).2 j ·.isUnit))
  choose C h using (n _ _ _ <| @h0 · ·)
  replace h {a b} : AnalyticAt ℂ (fun (x, y) ↦ C (e x) (e y) * Φ (a - b) (x - y) *
      Φ (a + b) (x + y) / (Φ a x * Φ b y) ^ 2 / C 0 0) (a, b) := .div_const ((((O _).1.comp
    analyticAt_fst).lift hN ((O _).1.comp analyticAt_snd) (o.1 _) h0).elim (·.mono (fun z
    hz ↦ by simp +zetaDelta [o.2 _ _ _ _ hz h0, eq_inv_of_mul_eq_one_left ((N.transition_trans _ _ _
    _ _ _ (K _) _).trans (N.transition_self ..)), by simpa [X] using hz, *]) |> ·.congr))
  let d : V →L[ℂ] V := (⅟2 : ℂ) • 1
  have hh z : d z + d z = z := by simp [d]; module
  have ⟨P, hP⟩ := (h.comp₂ analyticAt_id analyticAt_id).clog (x := 0) (by simp [*])
  let G : FormalMultilinearSeries .. := fun n ↦ (2 ^ n - 4 : ℝ)⁻¹ • P n
  let q := (-P 2).curryRight.curryRight 0
  choose r _ R S H using nhds_zero_basis_norm_lt.eventually_iff.1 (Z.and (hP.eventually_hasSum.and
    (Metric.eball_mem_nhds _ (hP.radius_pos.trans_le (G.radius_le_of_le fun n ↦ by simpa [G] using
    (mul_le_of_le_one_left (norm_nonneg _) (2 ^ n - 4 : ℤ).natAbs.cast_inv_le_one))))))
  have w := (@measure V (⌊‖·‖ / r⌋₊)).2
  have lt {z} (h : ¬‖z‖ < r) : ⌊‖d z‖ / r⌋₊ < ⌊‖z‖ / r⌋₊ := by
    grw [Nat.floor_lt, ← Nat.div_two_lt_floor] <;> simp_all [d, field]
  let c z := (q z z).exp * C (e z) (e z) / C 0 0
  have F := w.fix_eq fun z f ↦ if h : _ then (G.sum z).exp / Φ 0 z else f _ (lt h) ^ 4 * c (d z)
  set σ := w.fix _
  have hd z : σ (z + z) = σ z ^ 4 * c z := (F _).trans (dite_eq_iff'.2 ⟨fun h ↦ by
    have a : ‖z‖ < r := by bound [(SameRay.refl z).norm_add]
    simp [exp_log, q, eq_add_of_sub_eq (((G.hasSum (H h)).sub (((G.hasSum (H a)).mul_left 4).add
      (S a))).unique (hasSum_single 2 fun n k ↦ by
      have : (2 : ℂ) ^ n ≠ 4 := mod_cast (Nat.pow_right_injective le_rfl).ne k
      simp [← two_smul ℂ, (P _).map_smul_univ, G, *])), *]
    norm_num [G, Matrix.cons_fin_one, Matrix.vecCons_const], by simp [hh]⟩)
  choose h0 hP using @id (∀ {z}, σ z ≠ 0 ∧ AnalyticAt ℂ (σ * Φ z) z) @(w.fix fun z ih ↦
    if k : _ < r then ⟨by simp [*], ((G.analyticOnNhd _ (H k)).cexp.div (hf _) (by
    simpa [transition_self, K] using R k)).congr (.mono (tendsto_norm (gt_mem_nhds k))
    (by simp +contextual [F, Φ]))⟩ else (ih _ (lt k)).imp (by simp [F z, k]) fun a ↦
    (((a.pow 4).mul ((h.mul (q.analyticAt_bilinear _).cexp).comp₂ analyticAt_id analyticAt_id)).comp
    (d.analyticAt z)).congr (.mono (d.2.tendsto z Z) (by simp +contextual [hh · ▸ hd _, *, -F])))
  replace F := (hL · |>.1)
  let W := fun (x, y) ↦ (σ x * σ y) ^ 2 * C (e x) (e y) / σ (x - y) / σ (x + y) / C 0 0
  have hW {u} : AnalyticAt ℂ W u := by
    apply ((h.mul (((hP.comp analyticAt_fst).mul (hP.comp analyticAt_snd)).pow 2)).div ((hP.comp
      (analyticAt_fst.sub analyticAt_snd)).mul (hP.comp (analyticAt_fst.add analyticAt_snd))) _
      ).congr ((h.continuousAt.eventually_ne (y := 0) _).mono _) <;> simp +contextual [*]
  let P w := (W w)⁻¹ • fderiv ℂ W w ∘L .inr ..
  have E x {y} := hW.differentiableAt.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
  have := eq_fderiv_of_double P (by fun_prop (disch := simp [*])) fun (x, y) ↦ by
    have D y := (((hasFDerivAt_inv (by simp [*])).comp y (E x)).pow 4).mul
      ((E (x + x)).comp y (1 + 1 : V →L[ℂ] V).hasFDerivAt)
    have := funext ((by simp [isAppellHumbert_iff] : @IsAppellHumbert V _ L 0 1).eq_exp_of_ne_zero
      ⟨(⟨_, D ·⟩), by simp +contextual [add_add_add_comm x x, add_sub_add_comm, exp_sub, *]⟩
      (by simp [*])).2.2 ▸ (D y).fderiv
    simp [P, *] at this ⊢; clear * - this; grind
  have ⟨B, hB, hs⟩ := exists_factor_of_automorphy (L := L) @h0 (by
    rintro ⟨l⟩ g
    use (g 0)⁻¹ • fderiv ℂ g 0 + -P (l, 0), (hh · ▸ (hasFDerivAt_comp_add_left _).1 ?_)
    set x := d _; convert! ((E x).mul ((hasFDerivAt_inv _).comp x ((E (l + x)).mul (.comp x ((((@hP
      (l + (x - x))).comp (by fun_prop)).div hP _).congr (g := g) (Z.mono _)
      ).differentiableAt.hasFDerivAt (by fun_prop))))).mul_const (g x ^ 2) using 1 <;>
      simp [g, Φ, transition_self, add_assoc, ← add_sub, (inv_smul_eq_iff₀ _).1 (this _),
      by simpa using map_add (fderiv ℂ P 0) (l, 0) (x, x), *, -hL])
  refine ⟨B, fun l ↦ σ l / σ 0 / (B l l / 2).exp, _, (fun h ↦ ⟨h, ⟨fun v ↦ not_le.1 ∘ mt fun k ↦
    ContinuousLinearMap.toSpanSingletonCLE.map_eq_zero_iff.1 (linear_ext ⟨e, L, s, hL, O, ‹_›⟩ fun
    t ↦ OverMorphism.ext
    (hN.eq_of_isHomogCoords ?_ (funext (h.2.apply_smul_of_nonpos (hf := h.3 ·) v k t) ▸ h.4 _) ((h.4
    0).smul ?_)))⟩⟩) ⟨hN.1, ⟨hs, fun l _ ↦ have := congr($(hd (l + l)) * $(hd 0) ^ 3 / $(hd l) ^ 4)
    norm_eq_one_of_pow_eq_one ?_ four_ne_zero, ?_⟩, fun i ↦ ⟨fun _ ↦ ((hP.mul (hf i)).congr (Z.mono
    (by simp +contextual))).differentiableAt, by simp +contextual [*]⟩, fun _ ↦ T.smul ?_⟩⟩
    <;> simp +contextual [← exp_add, by simpa [add_mem, *, -hd, -hL] using this, *] <;> congr! 1 <;>
    apply ext <;> simp [riemannForm, *, -ofReal_div] <;> ring
end

section
/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Linear maps to the torsion module come from finite-adelic matrices. Objects modelled on
theta tori: uniformisation, torsion points, Weil pairing, multiplier. Isogenies of modelled PEL
abelian varieties correspond to rational matrices. Analytic families of period maps; theta
coordinates vary holomorphically after scaling. Uniformisation of the generic fibre extends over a
valuation ring by properness. -/

open Set Matrix NumberField CategoryTheory Complex LinearMap Submodule LineBundle AlgebraicGeometry
  Polynomial AddChar IsIntegrallyClosed Category Function ValuativeArc
variable {E n} [Field E] [NumberField E] [Fintype n] (φ : (n → E) →ₗ[𝓞 E] AdelicTorsion E n)

lemma exists_matrix_torsionClass_eq : ∃ h, ∀ y, torsionClass (h *ᵥ frameCoords 1 y) = φ y := by
  choose r hr using
    (_root_.id <| Quot.exists_rep <| φ <| Pi.single · · : ∀ _ _, ∃ y, torsionClass y = _)
  choose a _ h using fun j ↦ ((isCompact_pi_infinite fun _ ↦ isCompact_Ô).vadd
    (r j 1)).inter_iInter_nonempty _ (fun x ↦ (isOpen_preimage_torsionClass
    {torsionClass (r j x)}ᶜ).isClosed_compl.preimage_of_continuous (f := (x • ·))) fun u ↦ by
    choose m b e using IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) u _root_.id
    use m.1 • r j m.1⁻¹, ⟨_, torsionClass_eq_iff.1 ?_, add_sub_cancel ..⟩, mem_biInter fun x h ↦ ?_
    repeat (try erw [mem_preimage, smul_comm, ← smul_assoc, ← e _ h]); simp; simp_all
      [← map_smul, ← Pi.single_smul, Algebra.smul_def, ← division_def]
  use aᵀ; simp_all [mulVec_eq_sum, frameCoords, transpose_transpose a, ← map_sum φ,
    Finset.univ_sum_single]

variable {E : _} [Field E] [CMBase E] {D : PEL E} {Z τ} {X :
  ThetaFamily D Z τ} {O} [CommRing O] [ValuativeArc O] (y
  : ThetaObject X (Spec ⟨O⟩)) {g ℓ V} [FinComplexSpace V] (Y : PeriodMap D g ℓ V)

/-- A model of y on (g, ℓ): a polarised period map and an O_E-linear uniformisation with the
period lattice as kernel, giving theta coordinates and the level points; O_E → ℂ is Φ_{v₀}. -/
structure ThetaObject.TorusModel where
  baseHom_eq c : algebraMap O ℂ (y.baseHom c) = Φ v₀ c.val
  uniformisation : Uniformisation y.groupScheme V
  (χ θ) hasThetaCoords :
    HasThetaCoords uniformisation.L (atGeneric uniformisation.expMap) y.lineBundle Y.B χ θ
  equivariant (c : 𝓞 E) w : uniformisation.expMap (Y.Q (cmEmbedding c.val • w)) =
    c • uniformisation.expMap (Y.Q w)
  level_eq l : y.levelPoints l = uniformisation.expMap (Y.torsionLift l)
  lattice_eq : uniformisation.L = Y.periodLattice

/-- Let A/ℂ be abelian of dimension d, embedded by N obeying the parallelogram law. A dense
homomorphism V → A(ℂ) killing the lattice of Y, with the theta functions of Y as
coordinates, is a uniformisation with exactly that kernel, and d = n[E⁺:ℚ]. -/
lemma PeriodMap.exists_uniformisation_of_dense {A N} [IsAbelianScheme A] d (h :
  SmoothOfRelativeDimension d A.hom) (hN : IsProjEmbedding N A.hom) (w :
  N.picClass.ParallelogramLaw) (e : V →+ ComplexPoint A) (hd : IsSeparatingFamily (atGeneric e))
  (hl : ∀ z, N.IsHomogCoords (e z).left (Y.thetaCoord · z)) (hL : ∀ l ∈ Y.periodLattice, e l = 0) :
  ∃ u : Uniformisation A V, HasThetaCoords u.L (atGeneric u.expMap) N Y.B Y.multiplier
  (flip Y.thetaCoord) ∧ u.expMap = e ∧ u.L = Y.periodLattice ∧ d = abelianDim E D.Index := by
  obtain ⟨⟨u⟩, o⟩ := hN.nonempty_uniformisation h,
    HasThetaCoords.mk hN.1 Y.isAppellHumbert_periodLattice Y.thetaCoord_mem_thetaSpace hl
  obtain ⟨⟨B', _, _, h', hp'⟩, ⟨F, hF⟩, T, U, C, -⟩ := u.appell_humbert hN w,
    u.universal e (o.holomorphicAt hN 0), exists_theta_evaluation o
  have P {M χ θ} (t : HasThetaCoords (ι := D.T) _ (atGeneric _) M B' χ θ) :
    HasThetaCoords Y.periodLattice _ M .. := t.pull _ (f := 𝟙 _) (congr($(hF ·).1))
  have ⟨ρ, _⟩ :=
    (P h').riemannForm_eq_of_isFrame o (picClass_eq_iff.1 rfl).choose_spec (o.holomorphicAt hN)
  have key b (hb : ∀ l ∈ Y.periodLattice, B'.riemannPhase (F l) b = 1) l (hl' : l ∈ u.L) :
      B'.riemannPhase l b = 1 := (fun M (t : HasThetaCoords _ _ M ..) ↦ by
    choose σ v using fun a ↦ Y.isAppellHumbert_periodLattice.thetaSpace_le_of_thetaShift_mem
      (Y.thetaCoord_mem_thetaSpace 0) (Y.thetaCoord_ne_zero _) T.range (Y.dualLattice_periodLattice
      ▸ fun _ ⟨_, a, j⟩ ↦ j ▸ Y.thetaShift_thetaCoord (s := ⟨_, a⟩) rfl 0 ▸ smul_mem _ _ ⟨_, C _⟩)
      ((P t).2.of_riemannForm_eq Y.isAppellHumbert_periodLattice ρ (by aesop) ((P t).3 a))
    simp [U] at v
    have r q : PointFn.IsRegularOn _ ((N.mul M.inv).opens q) := ((σ q.2).2.1.1 _).mono inf_le_left
    have ⟨G, hG, H⟩ := h'.exists_theta_of_isSection t ⟨r, fun p q _ _ a b ↦
      hd.pointFn_ext ((r p).mono (by order)) (.mul (regular ..) (r q))
      (by simp +contextual [hl .., *, (P t).4 .., field]) _ _ (by simp_all)⟩ (h'.holomorphicAt hN)
    have H0 z : G (F z) ≠ 0 := (hl z).ne_zero.elim fun i k ↦ ((P t).4 z).ne_zero.elim fun a m h ↦
      m (by simpa [*] using H _ a _ (((P h').4 ..).1.1 ((hl ..).1.2 k.isUnit)).ne_zero)
    simpa [F.map_zero ▸ H0 0, h'.2.ne_zero hl', field, eq_comm, one_smul ℂ l ▸
      (h'.2.add t.2.neg).apply_smul_of_nonpos hG l (by simp) 1] using
      hG.2 _ hl' 0) _ (h'.pull_translate (u.atGeneric_add b))
  let G := LinearEquiv.ofBijective F.1 (.of_comp_left (f :=
    (B'.riemannForm ∘ₗ F.1.restrictScalars ℝ).flip) (BilinForm.toDual _
    (ρ ▸ Y.isPosRiemann.nondegenerate :).flip).bijective (ker_eq_bot.1 (bot_unique
    (hp'.nondegenerate.flip.ker_eq_bot ▸ le_ker_iff_comp_subtype_eq_zero.2 (flip_inj (ext_on u.3.2.1
    (eq_zero_of_exp_eq_one _ fun ⟨b, h⟩ ↦ key b (by simp_all [LinearMap.ext_iff]) · ·)))))))
  exact ⟨⟨e, Y.periodLattice, funext hF ▸ u.surjective.comp G.surjective,
    (⟨hL ·, fun h ↦ Y.isPosRiemann.isDualFamily.5 _ fun y ↦ ρ ▸ key _ (by simpa [← ρ] using!
    ((Y.isPosRiemann.isDualFamily.1 y).2 · · 0)) (F _) (by simp [*])⟩), (⟨o.holomorphicAt hN ·,
    fun _ h ↦ G.ker.le ((u.immersive _).2 _ ((isJet_comp_iff F.hasFDerivAt (u.immersive _).1).1
    (by aesop)))⟩), (u.universal · · |>.imp' (G.symm.toContinuousLinearEquiv ∘L ·) fun _ ↦ (· · ▸
    hF _ ▸ congrArg _ (G.4 _)))⟩, o, by simp [← Y.isPeriodMap.finrank_eq_abelianDim, G.finrank_eq]⟩

namespace ThetaObject.TorusModel

variable {y Y} (m : y.TorusModel Y)

/-- The map π of a model m, from (E ⊗ ℝ)ⁿ to the sections of A over O: the period map Q followed
by the uniformisation. -/
noncomputable def π w := m.uniformisation.expMap (Y.Q w)

/-- Let O be a valuation ring with fraction field ℂ and φ : O → ℂ a ring homomorphism. For some
unit ε of Ẑ, every value ψ_f(t) lies in O and φ sends it to ψ_f(εt). -/
lemma exists_unit_on_roots_of_unity (φ : O →+* ℂ) : ∃ ε : (Ô ℚ)ˣ, ∀ t, ∃ c, algebraMap O ℂ c =
  ψf E t ∧ φ c = ψf E (t * finAdeleIncl ℚ E ε) := by
  choose! ζ J using fun (z : ℂ) h ↦ isIntegral_iff (R := O).1
    ((IsPrimitiveRoot.orderOf z).isIntegral (orderOf_pos_iff.2 h)).tower_top
  refine .elim ((isCompact_Ô.prod isCompact_Ô).inter_iInter_nonempty (fun t ↦ {p | φ (ζ (ψf E t)) =
    ψf _ (t * finAdeleIncl _ _ p.1) ∧ (ψf E (t * finAdeleIncl _ _ (p.1 * p.2))).1 = ψf _ t})
    (fun _ ↦ by apply_rules [IsClosed.and, isClosed_eq, Continuous.subtype_val] <;> fun_prop)
    fun U ↦ ?_) fun _ ⟨⟨a, c⟩, H⟩ ↦ ⟨.mkOfMulEqOne ⟨_, a⟩ ⟨_, c⟩ (Subtype.ext (adeleMap_injective
    (algebraMap _ E) (eq_of_ψf (by aesop)))), (⟨_, J _ <| isOfFinOrder_ψf ·, by aesop⟩)⟩
  choose N hN _ using exists_forall_mul_mem_Ô (U.restrict id)
  obtain ⟨P, _, I⟩ := isPrimitiveRoot_exp N hN, NeZero.mk hN, IsFractionRing.injective O ℂ
  have Q := (J _ (P.isOfFinOrder hN) ▸ P).of_map_of_injective I
  have P' := isRoot_cyclotomic_iff.1 (map_cyclotomic _ φ ▸ (Q.isRoot_cyclotomic hN.pos).map)
  obtain ⟨⟨k, _⟩, l, _⟩ := P.eq_pow_of_pow_eq_one P'.1, P'.eq_pow_of_pow_eq_one P.1
  refine ⟨(k, l), by simp, mem_biInter fun t _ ↦ (Q.eq_pow_of_pow_eq_one (ξ := ζ (ψf E t)) (I
    (by simp_all [isOfFinOrder_ψf, ← Circle.coe_pow, ← map_nsmul_eq_pow, ψf_of_mem]))).elim ?_⟩
  simp [-nsmul_eq_mul, ← nsmul_eq_mul', map_nsmul_eq_pow]
  grind [isOfFinOrder_ψf, P.isOfFinOrder, pow_right_comm]

/-- The full structure of a model: the class of g⁻¹a in (𝔸_f / Ô)ⁿ, for a in Eⁿ, is sent to the
torsion section π(a). -/
noncomputable def fullStructure :
  y.FullStructure := have K := by simpa [← m.lattice_eq] using @Y.sub_mem_periodLattice_iff
  by refine ⟨⟨⟨(m.uniformisation.expMap <| Y.periodPoint <| ratLift g ·), ?_⟩, ?_⟩, fun _ ↦ ?_,
    m.level_eq, fun ι ↦ Y.isFrameFor.elim fun a F ↦ (exists_unit_on_roots_of_unity ι).imp' (a * ·)
    fun ε H k s t _ _ ↦ (H _).imp fun _ h ↦ ⟨by simpa [mul_right_comm]
    using h.2, fun _ _ ↦ (lift_commutator_iff_weil_pairing _ m.hasThetaCoords · · |>.2 (by
    simpa [*, mul_add, map_add_eq_mul, (ψf_unit_eq_one _).2, (D.mem_T _).1,
      Y.riemannForm_eq, -nsmul_eq_mul, ← frameTorsionClass_apply, show ∀ ξ a b,
      xiForm ξ (frameCoords g a) (k • b) = k * xiForm ξ s t + xiForm ξ (k • s) (b - t) +
    xiForm ξ (frameCoords g a - s) (k • b) by simp [star_trivial, xiForm, -nsmul_eq_mul]; grind,
      Circle.ext_iff] using (fourierChar_polarisationForm F (ratLift g (torsionClass s))
      (k • ratLift g (torsionClass t))).symm))⟩⟩ <;>
    simp [← equivariant, ← toRealVectors_smul, K, ← map_add, map_add (frameTorsionClass g)]

/-- For a model m of y on (g, ℓ) and z in Eⁿ, the full level structure `m.fullStructure` sends the
torsion class of g⁻¹z to the uniformised section at Q(Φ(z)), Q the period map, Φ the CM-type
embedding. -/
lemma torsionPoint_frameTorsionClass z : m.fullStructure.torsionPoint (frameTorsionClass g z) =
  m.uniformisation.expMap (Y.periodPoint
  z) := by simpa [← m.lattice_eq] using! Y.sub_mem_periodLattice_iff.2 (frameTorsionClass_ratLift _)

/-- In a model with lattice L, every b in the dual lattice L^∨ has |T|·b in L, and translation
by the section of b has a lift to N that preserves the O-span of the coordinates. -/
lemma exists_isTranslationLift_of_dualLattice : ∀ b ∈ Y.B.dualLattice (L := m.uniformisation.L),
  Nat.card D.T • b ∈ m.uniformisation.L ∧ ∃ Φ, IsTranslationLift _ (m.uniformisation.expMap b) Φ ∧
  span O (range (coordSection y.isProjEmbedding.1)) ∈ Φ.invtSubmodule := m.lattice_eq ▸
  Y.dualLattice_periodLattice ▸ fun b H@⟨w, a, h⟩ ↦ ⟨Y.card_nsmul_mem_periodLattice H,
  (y.obj_isThetaStructure.theta_law 1 ⟨_, a⟩).imp fun _ k ↦
  ⟨h ▸ by simpa [← torsionPoint_frameTorsionClass, m.level_eq] using! k.1, span_le.2 (by aesop)⟩⟩

/-- On the lattice of a model the multiplier is χ(l) = exp(πi·e(βl, l)), where e is the Riemann
form of B. -/
lemma multiplier_eq_canonicalMultiplier l (h : l ∈ m.uniformisation.L) : m.χ l =
  canonicalMultiplier Y.B (Y.intAction D.β) l := by
  have P c := m.hasThetaCoords.pull _ (e' := atGeneric m.uniformisation.expMap) (f :=
    (c • 𝟙 y.groupScheme).1) (by simp [PeriodMap.intAction, equivariant, atGeneric,
    ← Over.comp_left]) (m.lattice_eq ▸ Y.intAction_mem_periodLattice c)
  simpa [add_comm _ l, m.hasThetaCoords.2.semicharacter, m.hasThetaCoords.2.ne_zero, field,
    (m.lattice_eq ▸ Y.intAction_mem_periodLattice _) l h, h] using! (((m.hasThetaCoords.mul
    m.hasThetaCoords).mul (P _)).riemannForm_eq_of_isFrame (P (D.β + 1)) (picClass_eq_iff.1 (by
    simpa [Pic.pairing, add_smul, eq_sub_iff_add_eq] using!
      y.hasClassLaws.2 0 (𝟙 _))).choose_spec).2.1 l h

variable {V : _} {V'} [FinComplexSpace V] [FinComplexSpace V'] {D : PEL E} {g : _} {g'} {ℓ :
  _} {ℓ'} {Z τ : _} {X : ThetaFamily D Z τ} {O : _} [CommRing O] [ValuativeArc O] {x x' :
  ThetaObject X (Spec ⟨O⟩)} {Y : PeriodMap D g ℓ V} {Y' : PeriodMap D g' ℓ' V'}
  (z : GL D.Index E) (hz : ratConj z ℓ = ℓ') (m : x.TorusModel Y) (m' : x'.TorusModel Y')

attribute [local simp] PeriodMap.intAction riemannForm_pullForm polarisationForm star_mulVec
  dotProduct_mulVec π ext_iff₂

/-- Let x, x' be modelled on frames g, g' by π, π'. If ψ: x → x' satisfies ψπ = π'z for z in
GL_n(E), then on the torsion points given by the models ψ acts by the adelic matrix g'⁻¹zg. -/
lemma torsionPoint_comp {z ψ} (h : ∀ w, m.π w ≫ ψ = m'.π (realVecAction z.1 w)) y :
  m.fullStructure.torsionPoint (torsionClass y) ≫ ψ = m'.fullStructure.torsionPoint (torsionClass
  ((g'⁻¹ * toFinGL z * g).1 *ᵥ y)) :=
  denseRange_frameCoords (g := g).induction_on y ⟨IsLocallyConstant.comp₂
  isOpen_preimage_torsionClass (.comp_continuous isOpen_preimage_torsionClass (by fun_prop))
  (m.fullStructure.torsionPoint · ≫ ψ = m'.fullStructure.torsionPoint ·) Not⟩ (by
  simpa [← torsionPoint_frameTorsionClass, frameTorsionClass_apply, frameCoords, LinearMap.compLeft,
    comp_def, RingHom.map_mulVec] using h <| toRealVectors ·)

/-- Let π, π' model x, x' on (g, ℓ), (g', ℓ') over an arc. An O_E-linear ψ: x → x' with ψ*[N'] =
μ[N], μ ≠ 0, comes from z in GL_n(E): ψπ = π'z, zℓz⁻¹ = ℓ', z multiplying the Riemann form
by μ. -/
lemma exists_matrix_of_hom ψ [hψ : IsLinear ψ] {μ : ℕ} (hμ : μ ≠ 0) (H : x'.lineBundle.picClass.pull
    ψ.left = μ • x.lineBundle.picClass) : ∃ z : GL D.Index E,
  (∀ w, m.π w ≫ ψ = m'.π (realVecAction z w)) ∧ (∀ y w, μ * polarisationForm D
  Y.β y w = polarisationForm D (z.1ᴴ * Y'.β * z) y w) ∧ ratConj z ℓ = ℓ' := by
  have ⟨F, hF⟩ := m'.uniformisation.universal ((IsAddMonHom.addMonoidHom ψ _).comp _)
    ((m.uniformisation.immersive 0).1.comp_hom _)
  have R := (m.hasThetaCoords.pow μ).riemannForm_eq_of_isFrame (m'.hasThetaCoords.pull _
    (congr(_ ≫ $(hF ·).1)) (by simp_all)) (picClass_eq_iff.1 (by aesop)).choose_spec
  choose f _ v using fun y ↦ (exists_nsmul_adelicTorsion_eq_zero
    (frameTorsionClass g y)).choose_spec |> (Y'.nsmul_mem_latticeOver ·.1 (S := ⊥)
    (u := F (Y.Q (toRealVectors y))) |>.1 (by simp [← m'.lattice_eq,
    ← torsionPoint_frameTorsionClass, ← nsmul_comp, ← map_nsmul m.fullStructure.torsionPoint, *]))
  have L c : F ∘L Y.intAction c = Y'.intAction c ∘L F :=
    m'.uniformisation.linear_ext (by simp [equivariant, *])
  simp [DFunLike.ext_iff, reindex_equiv Y.Q, ← Y'.Q.eq_symm_apply] at L v hF
  have ⟨z, h⟩ : ∃ z, ∀ w, F (Y.Q w) = Y'.Q (realVecAction z w) :=
    ⟨toMatrix' (.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E (by use! f <;> simp [*,
    ← toRealVectors_injective.eq_iff])), denseRange_toRealVectors.eq⟩
  obtain ⟨z, rfl⟩ := z.mulVec_injective_iff_isUnit.1 fun a b k ↦
    toRealVectors_injective (Y.Q.injective (sub_eq_zero.1
    ((R.1 ▸ (Y.isPosRiemann.nsmul hμ).nondegenerate (L := Y.periodLattice)).1 _ (by simp [*]))))
  use z, ?_, ?_, Y.isPeriodMap.ratConj_eq Y'.isPeriodMap F h <;> simp_all [↓← Y.riemannForm_eq,
    Y'.riemannForm_eq, ↓map_conjTranspose_mul_mul]

include hz

/-- For models π, π' of x, x' on (g, ℓ), (g', ℓ'): if zℓz⁻¹ = ℓ' and k = g'⁻¹zg is integral, kᴴk
∈ μẐ^×, then an O_E-linear isogeny ψ has ψ*[N'] = μ[N], ψπ = π'z, acts by k on torsion;
structure maps agree. -/
lemma exists_isogeny {k} {μ : ℕ} (hk : g'⁻¹ * toFinGL z * g = k) (hi : ∀ i j, k i j ∈ Ô E) (hμ :
  IsScalarFrame k⁻¹ μ) : x'.baseHom = x.baseHom ∧ ∃ ψ, IsIsogeny ψ ∧ IsLinear ψ ∧
  x'.lineBundle.picClass.pull ψ.left = μ • x.lineBundle.picClass ∧
  (∀ y, m.fullStructure.torsionPoint (torsionClass y) ≫ ψ = m'.fullStructure.torsionPoint
  (torsionClass (k *ᵥ y))) ∧ ∀ w, m.π w ≫ ψ = m'.π (realVecAction z w) := by
  obtain ⟨_, S, rfl⟩ := (z.map _).mul_inv_eq_iff_eq_mul.1 hz, Y.Q.surjective, hk
  let F : V →L[ℂ] V' := {Y.Q.arrowCongr Y'.Q (realVecAction z.1).toContinuousLinearMap with
    map_smul' a := by simp_all [↓S.forall, ← Y'.Q.symm.injective.eq_iff, smul_re_im a,
      ← PeriodMap.isPeriodMap _ _, funext_iff]}
  -- L: F maps the lattice into the lattice; R: F multiplies the Riemann form by μ
  have ⟨ψ, a, G, c⟩ := (fun L R ↦ have P := m'.hasThetaCoords.pull F (fun _ ↦ .symm (comp_id _)) L
    exists_hom_of_hasThetaCoords (s' := m'.uniformisation.expMap.comp F) _ m.hasThetaCoords
      (by simp_all) x.obj_isThetaStructure.4 (by grind [exists_isTranslationLift_of_dualLattice])
      x'.isProjEmbedding x.isProjEmbedding x.hasClassLaws.1 x'.hasClassLaws.1 ⟨P.1,
      m.hasThetaCoords.2.nsmul μ, (P.2.of_riemannForm_eq (m.hasThetaCoords.2.nsmul μ) R
      (by simp_all [multiplier_eq_canonicalMultiplier, canonicalMultiplier, mul_left_comm, S.forall,
      F, ← Complex.exp_nat_mul, ← mulVec_smul]) <| P.3 ·), (F · |> m'.hasThetaCoords.4
    |>.smul (by simp))⟩) (by simpa [lattice_eq, F, frameLattice, mem_classLattice] using
    (realVecAction_mem_frameLattice hi (P := ·))) (by simp [F, S.forall, PeriodMap.riemannForm_eq,
    ← map_conjTranspose_mul_mul, vecMul_smul, Matrix.map_smul', Finset.mul_sum,
    Y.isSignedFrameFor.conj_eq_smul Y'.isSignedFrameFor hμ]; grind)
  use RingHom.ext (IsFractionRing.injective O ℂ <| m.baseHom_eq · ▸ m'.baseHom_eq _), ψ,
    finite_flat_of_quasiFinite _ (locallyQuasiFinite_of_pull_picClass x.isProjEmbedding (by aesop)
    c) ((isSeparatingFamily_atGeneric m'.uniformisation.surjective).2.surjective _
    (atGeneric m.π ∘ realVecAction z⁻¹ ∘ Y'.Q.symm) ?_), ⟨fun c ↦ (isSeparatingFamily_atGeneric
    (m.uniformisation.surjective.comp S)).hom_ext ?_⟩, c, m.torsionPoint_comp m' ?_ <;>
    simp [← assoc (m.uniformisation.expMap _), ← equivariant, atGeneric, ← Over.comp_left, F, *]

end ThetaObject.TorusModel

/-- A family of theta tori with fixed frame g over a domain U in ℂ^(n−1): periods analytic, with
differential injective modulo ℂ-linear maps; β and B(Q·, ·) constant; Re B positive
definite. -/
structure AnalyticFamily (D : PEL E) where
  U : TopologicalSpace.Opens (BallBase D.Index)
  isConnected : _root_.IsConnected U.1
  (frame) reflection : _ → _
  torus b : ThetaTorus D frame (reflection b) (BallFibre E D.Index)
  analyticAt : ∀ b₀ ∈ U, ∀ w, AnalyticAt ℂ (torus · |>.Q w) b₀
  eq_zero_of_linear : ∀ b ∈ U, ∀ v, let d y := fderiv ℂ (torus · |>.Q ((torus b).Q.symm y)) b v
    (∀ y, d (Complex.I • y) = Complex.I • d y) → v = 0
  form_const b' b : (torus b).β = (torus b').β ∧ ∀ w, (torus b).B ((torus b).Q w) =
    (torus b').B ((torus b').Q w)
  re_pos b : ∀ u ≠ 0, 0 < ((torus b).B u u).re

attribute [local fun_prop] ContinuousLinearMap.analyticAt analyticAt_fst analyticAt_snd

/-- For an analytic family f of theta tori and b₀ in its domain, some scalar function c(b),
non-zero near b₀, makes each theta coordinate c(b)·θ_t(b, z) jointly analytic in (b, z) at
every point (b₀, z). -/
lemma AnalyticFamily.exists_analytic_thetaCoord (f : AnalyticFamily D) {b₀} (h₀ : b₀ ∈ f.U) : ∃ c :
  _ → ℂ, (∀ z t, AnalyticAt ℂ (fun p ↦ (c p.1 • ((f.torus p.1).thetaCoord · p.2)) t) (b₀, z)) ∧ ∀ᶠ
  b in nhds b₀, IsUnit (c b) := by
  let Q b := (f.torus b₀).Q.symm.trans (f.torus b).Q
  choose _ _ S _ w hz using
    (f.torus · |>.isAppellHumbert_latticeOver_lagrangian.poincareSeries_spec <| f.re_pos _)
  choose c hc using fun b ↦ ((PeriodMap.exists_thetaSpace_lagrangian_le_span _).2.2 ⟨_,
    S b (Q b (w b₀))⟩).imp fun _ ↦ congrArg (·.1)
  have a w (z : BallFibre E D.Index) := (f.analyticAt (_, z).1 h₀ w).comp analyticAt_fst
  have hφ z := (((f.torus b₀).isAppellHumbert_latticeOver_lagrangian.summable_and_analyticAt_tsum
    (T := (Q ·)) ((f.U.2.eventually_mem h₀).mono (by solve_by_elim [Q, analyticAt]))
    (by simp_all [Q, re_pos]) _).2.comp (x := (_, z)) (f := fun p ↦ (p.1, (f.torus b₀).B (w b₀), p.2
    - Q _ (w b₀), p.2)) (by simp [Q]; fun_prop)).congr (.of_forall fun p ↦ (tsum_congr (by simp [Q,
    IsAppellHumbert.poincareTerm, f.form_const b₀, canonicalMultiplier, PeriodMap.intAction,
    PeriodMap.riemannForm_eq, mem_classLattice])).trans ((((Q p.1).subtypeEquiv (by simp [Q,
    mem_classLattice, ContinuousLinearEquiv.eq_symm_apply])).tsum_eq _).trans congr($(hc p.1)
    p.2).symm))
  use c, fun _ _ ↦ ?_, ((hφ _).curry_left.continuousAt.eventually_ne
    (by simpa [hc, Q] using hz _)).mono (by aesop)
  simp [PeriodMap.thetaCoord, normalizedShift, PeriodMap.torsionLift, thetaShift, f.form_const b₀,
    canonicalMultiplier, PeriodMap.intAction, PeriodMap.riemannForm_eq, mul_left_comm (c _)]
  refine .mul ?_ (.mul ?_ ((hφ _).comp₂ analyticAt_fst (.add ?_ (a ..)))) <;> fun_prop

/-- Let y be an object over a valuation ring O with fraction field ℂ and x its generic fibre. A
model of x on (g, ℓ) gives a model of y on (g, ℓ) whose sections π'(w) restrict to π(w) at
the generic point.

Known result: Homomorphisms and line bundles of abelian schemes extend from the generic fibre. -/
lemma ThetaObject.TorusModel.exists_model_over_arc {E V} [Field E] [CMBase E] [FinComplexSpace V]
  {D : PEL E} {g ℓ Z τ O} {X : ThetaFamily D Z τ} [CommRing O] [ValuativeArc O] {y x : ThetaObject X
  _} {Y : PeriodMap D g ℓ V} (m : x.TorusModel Y) (h : x.IsPullbackAlong (@genericPt O _ _) y) :
  ∃ m' : y.TorusModel Y, ∀ w, genericPt ≫ (m'.π w).left = (m.π w).left ≫ h.schemeMap.left := by
  let j := LinearEquiv.ofBijective h.isGroupBaseChange.pullSection
    (h.isGroupBaseChange.pointEquiv.symm.bijective.comp bijective_restrict_genericPt)
  have E w : atGeneric (j.symm ∘ m.uniformisation.expMap) w = _ :=
    h.isGroupBaseChange.pullSection_comp _ ▸ congr($(j.4 _).1 ≫ _)
  refine ⟨⟨((@genericPt_eq O .. ▸ h).baseHom_eq_comp ▸ m.baseHom_eq :),
    ⟨.comp j.symm m.uniformisation.expMap, _, by simpa using m.uniformisation.surjective, ?_,
    _root_.funext E ▸ m.uniformisation.immersive_of_isPullback h.isGroupBaseChange.1, fun γ k ↦
    (k.exists_isHomogCoords y.isProjEmbedding.1).elim fun _ ⟨a, b⟩ ↦
    (m.uniformisation.universal (.comp j γ) (.of_isHomogCoords x.isProjEmbedding a (b.mono fun _ c ↦
    h.lineBundle_eq_pull ▸ .pull_iff.2 (h.isGroupBaseChange.pullSection_comp _ ▸ c)))).imp ?_⟩, _,
    _, by simpa [_root_.funext E] using {h.lineBundle_eq_pull ▸ m.hasThetaCoords with
    isLinearSystem := y.isProjEmbedding.1}, ?_, (j.eq_symm_apply.2 <| h.levelPoints_eq_pullSection
    _ ▸ m.level_eq ·), m.lattice_eq⟩, E ∘' _⟩ <;> simp_all [equivariant]
end
