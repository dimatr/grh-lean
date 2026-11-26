import New.Weil.BlockMatrices
import Lib.GaloisRep.ShintaniLifting
import Lib.GaloisRep.BaseChangeEigenchar
import Lib.GaloisRep.EigencharCompatibility

section
/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: Parahoric types and depth-zero labels; type implies label by Frobenius reciprocity. -/


open NumberField Matrix Polynomial Fintype Function Fint Fin Set MulChar Finset
variable {E n M K ρ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {w :
  FinPlace E} [Field K] [Algebra (ResField w) K] [Fintype ρ] {s V} [AddCommGroup V] [Module ℂ V]
  {σ : Representation ℂ (GL ρ (ResField w)) V}

/-- Parahoric type: block 0 of b is the image of e; each k in GL_n(O_w), block triangular mod w
with block 0 equal to x, sends f to ∏χ_l(det k_{l+1})·ψ(det x)·F(x), k_j its block j mod w. -/
def HasParahoricType f hw (e : ρ ↪ n) b (ψ : MulChar (ResField w) ℂ) (χ : Fin s →
  MulChar (ResField w) ℂ) (F : GL ρ (ResField w) → _) := (∀ i, b i = 0 ↔ i ∈ range e) ∧ ∀ k x h,
  submatrix (reduceGL k) e e = x.1 → rightRegular ℂ _ (M → ℂ)
  (atSplit hw k.1) f = (∏ l, χ l (blockHom b l.succ ⟨reduceGL k, h⟩).det.1) • ψ x.det • F x

/-- c is monic squarefree of degree d, c(0) ≠ 0, c∏(X − x_{χ_l}) is separable, d + Σt_l = n, and
f has label Ξ_c * ∏(χ_l∘det on GL_{t_l}) at w. -/
def HasProductLabel (f : Gf E n → M → ℂ) hw T [IsFaithfulMulChar K T] d (c : (ResField w)[X])
  (χ : _ → _) (t : Fin s → ℕ) := IsLabel d c ∧ Separable (c * ∏ l, (X - C (charName T (χ l)).1)) ∧
  d + ∑ l, t l = card n ∧ HasLabel f hw (labelChar T c * ∏ l, (detChar (χ l)).rankPart (t l)).evalGL

/-- Type implies label (Frobenius reciprocity): let c be a label of degree |ρ|, c' its roots
scaled by x_ψ, the χ_l distinct, c'(x_{χ_l}) ≠ 0, and Σ conj(Ξ_c(x))F(x) ≠ 0. Then
`HasParahoricType` gives `HasProductLabel` for c', the χ_l and the block sizes. -/
lemma HasParahoricType.hasProductLabel {f hw e y b c ψ} {χ : Fin s → _} (L : V →ₗ[ℂ] Gf E n →
  M → ℂ) (hL : Injective L) (h₂ : σ.asAlgebraHom (labelIdem ρ c) y ≠ 0) (h :
  HasParahoricType f hw e b ψ χ (L <| σ · y)) (hχ : Injective χ) : let T := faithfulChar (ResField
    w); let a := c.scaleRoots (charName T ψ); (∀ l, ¬a.IsRoot
      (charName T (χ l)).1) → HasProductLabel f hw T (card ρ) a χ (card {i // b i = ·.succ}) := by
  intro T a hψ; simp [labelIdem, asAlgebraHom_eq_sum, apply_ite, ite_apply] at h₂; exact
  let ε := (Equiv.subtypeEquivRight h.1).trans e.toEquivRange.symm
  have h₁ k g := h.2 k (reindexGL ε (blockHom b 0 ⟨_, g⟩)) g rfl
  have hK k _ := .symm (by simpa [*] using h₁ 1)
  have H g x y := by simpa using hK (y⁻¹ * g * x)
  have d := h₂.1.scaleRoots _
  ⟨d, (PerfectField.separable_iff_squarefree.2 d.2.1).mul (by simpa [Units.val_inj, Injective,
    separable_prod_X_sub_C_iff]) (.symm (.prod_left (by simpa [dvd_iff_isRoot,
    (prime_X_sub_C _).coprime_iff_not_dvd]))), by simp [sum_univ_succ, card_congr ε, ← card_congr
    (.sigmaFiberEquiv b)], hK, fun z ↦ h₂.2 (hL (by
  ext; have := congrFun₂ ((sum_evalGL_prod_eq_zero_iff b (F :=
    cons _ (detChar ∘ χ)) (cases (lift_labelChar_self T d) fun _ ↦ lift_detChar T rfl) _ fun _ _ ↦
    H _ _ (surjInv reduceGL_surjective _) (by simp [surjInv_eq])).1
    (by simpa [prod_univ_succ, card_congr ε, rankPart_labelChar, d] using z) 1) ‹_› ‹_›
  simp [prod_univ_succ, mul_assoc, h₁, ← mul_sum, star_apply', ↓isUnits_det_units, surjInv_eq,
    inv_apply_eq_inv', prod_ne_zero_iff, apply_eq_zero_iff, ← labelChar_mul_det h₂.1] at *
  simp_rw [Hall.evalGL, ← simClassOf_submatrix ε.symm, ← finsum_eq_sum_of_fintype] at *
  exact .inr
    ((mul_eq_zero_iff_right (by simp)).1 ((finMean_comp_surjective ((reindexGL ε).toMonoidHom.comp
    (blockHom b 0)).toAdditive (⟨⟨extendGL e ·, fun _ ↦ by grind [one_apply_ne, extendGL_spec]⟩,
    Units.ext (extendGL_spec ..).1⟩) _).symm.trans (mul_eq_zero_of_left this _)))))⟩
end

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Base change keeps a depth-zero label at an inert place via Shintani lift. -/


open NumberField Representation Function Fint ComplexConjugate FiniteField Module SemidirectProduct
  algebraMap
variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Fintype n] {w :
  FinPlace E} (χ : GL n (ResField w) → ℂ)

/-- The function on GL_n(E_w) equal to the complex conjugate of χ(g mod w) for g in GL_n(O_w),
and 0 elsewhere. -/
noncomputable def inflateConj g := if h : _ then conj (χ (reduceGL ⟨g, h⟩)) else 0

attribute [local simp] inflateConj mem_localCongruence_zero mul_mem_cancel_left mul_mem_cancel_right
  locMap_mem_Kw atPlace_baseChangeGf atPlace_galoisGf
attribute [local simp ←] MulMemClass.mk_mul_mk algebraMap_ResField_eq_zero

lemma exists_rep_inflateConj hw {κ} : let π := ((stdSpace E n).formTranslation κ).comp (atSplit hw)
  let K := levelSpace π (localCongruence n w 0)
  ∀ W : Subrepresentation π, ∃ ρ : Representation ℂ _ ↥(K ⊓ W.1), ∀ χ v,
  let x := ρ.asAlgebraHom (groupAlgElem (conj <| χ ·)) v
  heckeFun π (localCongruence n w 0) (inflateConj χ) v = x ∧ (HasLabel v.1.1 hw χ ↔ x ≠ 0) := by
  intro π K W
  have H : K = invariants ((π.comp (Kw ..).subtype).comp reduceGL.ker.subtype) := by aesop
  refine ⟨(Units.coeHom _).comp
    (reduceGL.liftOfSurjective reduceGL_surjective ⟨(subrepresentation (π.comp
    (Kw ..).subtype) _ fun k v ↦ H ▸ .imp (le_comap_invariants _ _ _ ·) (W.2 _ ·)).asGroupHom, fun k
    h ↦ by ext v : 3; exact H.le v.2.1 ⟨k, h⟩⟩), fun X v ↦ ⟨(heckeFun_eq_sum (r := (·.1) ∘ surjInv
    reduceGL_surjective) (s := ⊤) ?_ v.2.1 ?_ ?_).2.trans ?_, (and_iff_right (congr($(H.le v.2.1
    ⟨·, ·⟩).1))).trans ?_⟩⟩ <;> simp +contextual [surjInv_eq, asAlgebraHom_eq_sum, Subtype.ext_iff,
    Set.InjOn, inv_mul_eq_one, QuotientGroup.eq, ← InvMemClass.coe_inv, -Subgroup.coe_inv] <;> rfl

lemma reduceGL_map_locMap [CMType E'] {u : FinPlace _} {ι} (e : u.comap ι = w) ψ (hψ : ∀ x, ψ
  (algebraMap _ _ x) = ↑(.mapRingHom ι x : 𝓞 E')) g a : reduceGL ⟨.map (n := n) _ g, a⟩ = (reduceGL
  ⟨g, (locMap_mem_Kw e).1 a⟩).map ψ := by
  ext
  refine (algebraMap_ResField_surjective ..).rec fun x hx ↦ ((hx ▸ hψ x).trans ?_).symm
  erw [residue_eq_iff_valuation_sub_lt_one] at *
  simpa using! (isEquiv_comap_locMap ι e).lt_one_iff_lt_one (x := (x : E) - _) |>.2 hx

variable [Algebra E E']

variable [CMOver E E'] {u : FinPlace E'} {μ} [hμ : IsStep E' μ] (hw) (hu : _ ≠ u) (h : ∀ u',
  .below E u' = w ↔ u' = u) (hD : ∀ x, μ (locIdele w x) = 1) [Algebra (ResField w) (ResField u)]
  (hR : ∀ x : 𝓞 E, ((x : ResField w) : ResField u) = (x : 𝓞 E')) (hq :
  finrank (ResField w) (ResField u) = finrank E E') {Ξ : Hall (ResField w)}
include h hD hR hq
attribute [-simp] SemidirectProduct.mk_eq_inl_mul_inr

/-- For a step E'/E inert at a split w, μ_w = 1, u split above w, and a class function S on
GL_n(k_u) ⋊ Gal(k_u/k_w) that is a Shintani lift of Ξ: for some σ ≠ 1 and φ, the inflated Ξ
and S(·, φ) match at principal level (`IsLocalMatching`). -/
lemma isLocalMatching_shintani {S : GalSemidirect (ResField w) _ n → ℂ} (c : IsClassFunction S) (L :
  DescendsTo S Ξ) : ∃ φ, IsLocalMatching μ {w} (atSplit hw) (atSplit hu) (localCongruence n w 0)
  (localCongruence n u 0) {()} (fun _ ↦ inflateConj Ξ.evalGL) fun _ ↦ inflateConj (S ⟨·, φ⟩) := by
  let φ := frobeniusAlgEquivOfAlgebraic (ResField w) (ResField u)
  obtain ⟨o : orderOf φ = _, ⟨⟩, σ, hσ⟩ := hq ▸ orderOf_frobeniusAlgEquivOfAlgebraic ..,
    (h u).2 rfl, IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(E'/E) u.1
  have hφ := (o ▸ hμ.out).ne_one ∘ orderOf_eq_one_iff.2
  replace hσ (x : 𝓞 E') : φ x = ↑(σ • x) := .symm (by
    simpa [φ, card_ResField, ← Nat.card_eq_fintype_card] using! hσ x)
  have := by simpa [hσ, AlgEquiv.ext_iff, (algebraMap_ResField_surjective u).forall] using hφ
  obtain ⟨⟨m, -, l, -, m₁⟩, hs, R⟩ := exists_baseChange_level (n := n) (σ := σ) (by bound)
    isOpen_Kf, (h _).1 (below_comap σ u), isLocalRetraction_atSplit n h hu hw
  obtain ⟨-, -, coh, -, H⟩ := l _ _ (R.2.2.symm.trans (by ext; exact forall₂_congr (m₁ _
    (h · |>.1 · ▸ ⟨⟨σ, by simpa⟩, by simp [hD]⟩) (by simp) · · ▸ .rfl)))
  have N a ha m : ∃ h, (⟨reduceGL ⟨a.atPlace u, ha⟩, φ⟩ : GalSemidirect _ _ n) ^ m =
    ⟨reduceGL ⟨(twistedNorm (galoisGf σ) m a).atPlace u,
    h⟩, φ ^ m⟩ := m.rec (by simp [twistedNorm, ← OneMemClass.one_def]; rfl) fun m ⟨h, e⟩ ↦ by
    simp [pow_succ', twistedNorm_succ', *, reduceGL_map_locMap hs φ hσ]; rfl
  refine ⟨φ, σ, by bound, Gf.atPlace _, Gf.atPlace u, ⟨fun _ ↦ by constructor <;> exact
    ⟨(finite_quotient_image_of_isCompact isOpen_localCongruence (isCompact_Kw _)).subset fun q _ ↦
    ⟨_, by aesop, q.out_eq⟩, by simp +contextual⟩, ?_⟩, ?_,
    isOpen_localCongruence.preimage_of_continuous, _, ⟨fun _ ↦ (·.1), R.2.2.ge⟩, coh, fun _ _ ↦
    ⟨show ∀ k ∈ _, ∀ δ, (_ : _ → ℂ) (k⁻¹ * δ * galoisGf σ k) = _ from ?_, fun P c ↦ by
    peel 7 H P (by revert c; gcongr <;> simp +contextual); exact this.imp (fun C _ i e ↦ dite_congr
    (by simpa using congr($(C _ i e) ≠ 0))
      (fun _ ↦ congr(conj $(L _ ((fixed_eq_range_iff_ne_one (hq ▸ hμ.out)).2 hφ) _ _ rfl
      ((N ..).2.trans (by simp [o ▸ i ▸ e, reduceGL_map_locMap _ _ hR]; rfl)))).symm) (by simp)) (by
    simp; tauto)⟩⟩ <;> simp +contextual [EmbeddingLike.map_eq_one_iff, *, SetLike.ext_iff,
    reduceGL_map_locMap hs φ hσ, reduceGL_map_locMap _ _ hR, eq_ite_iff,
    Matrix.GeneralLinearGroup.ext_iff, fun δ x ↦ show S ⟨x⁻¹ * δ * x.map φ, φ⟩ = _ from c ⟨δ,
    φ⟩ (inl _), fun a h ↦ show reduceGL ⟨_, inv_mem h⟩ = _ from reduceGL.map_inv ⟨a, h⟩]

/-- Take a step E'/E, w split with μ_w = 1, u split the only place above w, of residue degree
[E':E]. If f has as label a character Ξ with lift Ξ' (`Lift` over ℕ), some eigenform
over E', a weak base change of f off w, has label Ξ' at u. -/
lemma exists_baseChange_hasLabel [StablyUnram E'] {κ f} (hf : f ∈ (stdSpace E n).forms κ) (hΞ :
  IsChar (Ξ.evalGL (n := n))) {Ξ'} (hsh : Lift ℕ Ξ Ξ') (hl : HasLabel f hw Ξ.evalGL) :
  ∃ f' ∈ (stdSpace E' n).forms κ.baseChange, ∃ P, IsEigenform f' P ∧ IsWeakBaseChange μ {w} f f' ∧
  HasLabel f' hu Ξ'.evalGL := have ⟨_, c, L, K⟩ := hsh.exists_descendsTo n
  have C := isChar_of_mem_virtualChars c
  (isLocalMatching_shintani hw hu h hD hR hq C.isClassFunction L).elim fun φ M ↦
    (exists_isWeakBaseChange_of_matching ⟨_,
    hf⟩ M ![] 0 _ rfl (by simp) nofun (by rw [iInf_of_empty, inf_top_eq]; exact (fun V hV _ h H ↦
    (exists_rep_inflateConj _ V).rec fun ρ hρ ↦ (hρ _ ⟨_, by simpa [Subtype.ext_iff] using hl.1,
    hV⟩).2.1 hl congr($(hΞ.groupAlgElem_eq_zero_iff.2
    (by simpa [classInner, character, asAlgebraHom_eq_sum, finMean] using (congrArg _ (LinearMap.ext
    (Subtype.ext <| hρ _ · |>.1.symm))).trans H)) _)))).elim fun f' ⟨_, a, b, _, ⟨v, hv, e⟩, _⟩ ↦
    (exists_rep_inflateConj hu ⊤).rec fun ρ hρ ↦ have E := e.symm.trans (hρ _ ⟨v, hv, ⟨⟩⟩).1
    ⟨_, f'.2, _, a, b, E ▸ (hρ ..).2.2 (DescendsTo.iff_comp_inl_eq_evalGL.1 K ▸ fun H ↦
      a.1 (by simpa [*, ← mk_eq_inl_mul_inr] using (congr(ρ.asAlgebraHom
      $(((irreducible_criteria_of_isClassFunction ℤ (C.comp inl).star.isClassFunction).2.2 _ fun _ ↦
      C.star.groupAlgElem_eq_zero _ (inr φ) ∘ (C.comp inl).groupAlgElem_eq_zero_iff.1).choose_spec)
      ⟨v, hv, ⟨⟩⟩))))⟩
end

section
/-! Known result: Local-global compatibility at tame level, away from and at l. It is treated at
split places only, for sorted tame Iwahori eigencharacters and for depth-zero types induced from a
squarefree type and characters of the determinant. It is stated as polynomials killing Weil or
inertia elements, without local Langlands, and is reduced to the spherical case by cyclic base
change. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties (2001);
Taylor, Yoshida, J. Amer. Math. Soc. 20 (2007); Barnet-Lamb, Gee, Geraghty, Taylor, Local-global
compatibility for l = p, II (2014), Thm 1.1.

This file: Compatibility on inertia for squarefree depth-zero types induced with characters of the
determinant. -/

open NumberField Polynomial Ideal Finset Function Module Fin QZChar Fint
attribute [local simp] roots_prod prod_eq_zero_iff X_ne_C Polynomial.map_prod Units.ext_iff
  prod_ofFn prod_univ_add sum_univ_add Subtype.ext_iff Multiset.prod_nsmul roots_mul

/-- Let r be attached to an eigenform f (standard space, Weil data) with label c, χ_l, t_l at
split w, T injective. Above w, r has finite type, the jumps of κ, and `IsLabelledAt`
holds for c∏(X − x_{χ_l})^{t_l}, with determinants away from ℓ.

Known result: Local-global compatibility at tame level, away from and at l. -/
lemma Attached.isLabelledAt {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n} [Nonempty n] [Field E] [CMType E]
  [EmbeddedNumberField E] [Fintype n] {κ f P} {r :
  GalRep ℓ E n} {w A hw K} [Field K] [Algebra (ResField w) K] {T} [IsFaithfulMulChar K T] {s
  d c} {χ : Fin s → MulChar (ResField w) ℂ} {t} [WeilData E] (hf : f ∈ (stdSpace E n).forms κ) (he :
  IsEigenform f P) (hr : Attached P r) (h : HasProductLabel f hw T d c χ t) (hA : IsPlaceOver A w) :
  IsFiniteTypeAt r A ∧ HasJumpsAt r A (jumps κ (Fintype.card n)) ∧
  IsLabelledAt A T d.factorial (fun s Q ↦ PolyKillsAt r A s Q ∧ (A.valuation
  ℓ = 1 → (r s).1.det = Q.roots.prod)) (c * ∏ l, (X - C (charName T (χ l)).1) ^ t l) := by
  suffices ∀ ⦃σ a⦄ _, _ ∧ _ ∧ _ from .imp_right (⟨·.1, (@this · · · |>.2.2)⟩)
    (this (exists_isTameExponent T hA d).1.choose_spec)
  have (x : K) a := (h.1.root_pow_eq_one (x := x) a).1
  revert h this
  induction' d.factorial using induction_on_primes with p g hp ih generalizing E <;>
    intro ⟨h₁, h₂, h₃, h₄⟩ hq σ a Y@⟨_, hg, hσ, φ, π, _, _, k, hφ, _, hz⟩
  omega
  · obtain ⟨⟨x, v, u⟩, ψ, rfl⟩ := hA.exists_localArtin_eq (inv_mem hσ) 0,
      h₁.exists_eq_prod_of_splits T (by grind [pow_pred_eq_one_iff, card_ResField, w.one_lt_q])
    choose z hz ξ l o hξ using
      exists_sorted_of_detChar (ρ := localFormRep ..) (v_uniformizer w) isUnitary_localFormRep
      (Fintype.equivFin n) (.of_comp (f := (charName T · |>.1)) (g := append ψ χ) (by simpa [←
      separable_prod_X_sub_C_iff])) (m := append 1 t) (by simpa) (x := ⟨f, hf⟩) (by
      simpa [-Units.ext_iff] using! h₄.1) (surjInv_eq _) (by simpa [labelChar_X_sub_C] using! h₄.2)
    choose θ M using hr.exists_det_eq_avatar z.2 (he.of_mem_cyclicSpan hz l.1)
    rw [← congr(map ιℓ.toRingHom $(hξ _ v)).trans (c := Multiset.prod _)]
    simpa +contextual [M, v, hA.valuation_natCast_eq_one_iff, (θ.avatar_localArtin hA · u) ∘ .inl,
      (M.2.1 ..).1 v (.trans congr(rightRegular ℂ _ _ (atSplit hw $(by simp [reindexGL]))
      _) congr($((compactMean_eq_self _ (map_mem_levelSpace_of_commute l.2.1 fun _ ↦
      .map (by ext; simp [mul_comm]) _)).symm.trans (l.2.2 (fun _ ↦ x) monotone_const)).1)),
      torusChar, normAbsChar, Pi.monoidHomMulEquiv] using hr.local_global_of_eigencharacter l
      (he.of_mem_cyclicSpan hz l.1) o hA ⟨_, _⟩ _ 0 (inv_mem hσ) u v
    simp [aroots, Y.pow_apply_charName T v u, Multiset.map_bind, Multiset.map_nsmul]; rfl
  have := Fact.mk hp
  choose μ u _ _ hd hu hb B D G using exists_step_of_local_char hw hA hp (.mk' (.ofAdd <|
    .ofZMod p <| Valued.v ·.1 |>.log) (by simp)) (x₀ := uniformizer w) (by simp [map_eq_zero_iff])
    (by simp [← ofAdd_nsmul, ← map_nsmul]) (by simp +contextual)
  obtain ⟨⟨⟩, H⟩ := (hb u).2 rfl,
    (hA.artinAt_units_trivial_iff_unramified (symmetrise μ)).1 (by simp +contextual [G])
  let w := u.below E
  obtain ⟨a, ⟨j, hj⟩, i, e⟩ := (hA.ramification_in_tower _ B).2.1 H, exists_resField_hom w
    ((algebraMap (𝓞 (stepField μ)) (ResField u)).comp _) fun _ ↦ (algebraMap_ResField_eq_zero.2 ·),
    exists_resField_hom u (φ.comp (algebraMap ..)) (B.centrePrime_liesOver.1 ▸ fun _ ↦ (k ·))
  have hq' : w.q ^ p =
    u.q := by simp [← hd, ← u.ncard_above_mul_ef_eq_finrank, *, absNorm_pow_inertiaDeg]
  algebraize [j, i]
  obtain ⟨⟨⟩, _⟩ := by simpa [← hq', ↓card_ResField, w.one_lt_q.ne'] using
    @natCard_eq_pow_finrank (ResField w) (ResField u) _ _ _ _, IsScalarTower.of_algebraMap_eq
    ((algebraMap_ResField_surjective _).forall.2 (hφ · ▸ hj _ ▸ (e _).symm))
  choose _ n using by simpa using ((charName T).surjective <| .map j.1 <| charName T <| χ ·)
  obtain ⟨⟨f', hf', _, he', hs, hl⟩, hχ⟩ := exists_baseChange_hasLabel hw hu hb (by simp [D]) hj
    hd.symm hf (isChar_of_mem_virtualChars ((lift_labelChar_self T h₁).mul (prod_hom_rel .one fun _
    _ _ ↦ .mul (.rankPart_of_descendsTo (lift_detChar T
    rfl _)))).evalGL_mem_virtualChars) ((shintani_lift_labelChar hp T h₁).mul (prod_hom_rel .one
    fun l _ _ ↦ .mul (.rankPart_of_descendsTo (lift_detChar T (n _) _)))) h₄, h₂.map (f := j)
  simp [w, pow_mul, hq', ← (c * _).aroots_map K (S := ResField u), ← c.aeval_map_algebraMap
    (ResField u), ← n, j.algebraMap_toAlgebra, -FinPlace.q_bounds] at hg hz hq hχ ⊢
  exact (sphericalCompat_std u hf' he').1.rec fun _ r ↦
    ((hs.exists_attached_descent r he' he).2.1 hr A).rec fun a ⟨b, d⟩ ↦ .imp a (.imp (b _) ((d ⟨σ,
    H hσ, (hA.artinAt_trivial_iff_decompGroup_le _).1 D hσ.1⟩).rec fun d e ↦ .imp (e _) (d ▸ ·)))
    (ih hf' he' r B ⟨h₁.map _, hχ, h₃, hl⟩ hq ⟨B, hg.2, hσ, φ, algebraMap _ _ π, _, _, k,
    (e · ▸ rfl), by simp [w, B.isUniformiser_iff, hA.isUniformiser_iff.1, *, w.3,
    ← w.valuation_liesOver _, ramificationIdx'_eq_ramificationIdx], hz⟩)
end
