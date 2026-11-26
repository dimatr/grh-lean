import Lib.DiscreteSeries.CommonEigenvectors
import Lib.Adelic.Frames
import Lib.Shimura.KernelRing
import Lib.Weil.AdditiveCharBasic

section
/-! Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family)
(known result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Flatness over a local ring from constant Hilbert ranks, by standard monomials and
determinants. -/

noncomputable section


open AddSemigroupIdeal Finsupp Set
variable {ι κ J A k K : Type} [CommRing A] [Field k] (φ : A →+* k) {d : ℕ}
  (T : Ideal (MvPolynomial J A)) [Finite J] [IsLocalHom φ]

instance : Fintype (@degree J ℕ _ ⁻¹' {d}) := (finite_of_degree_eq d).fintype

/-- Every monomial ideal in variables J that omits at most σ i monomials of degree r^i for all i
≤ d does so for all i. -/
def IsCutDegree (J : Type) d r (σ : ℕ → ℕ) := ∀ M : AddSemigroupIdeal (J →₀ ℕ),
  (∀ i ≤ d, (degree ⁻¹' {r ^ i} \ M.1).ncard ≤ σ i) → ∀ i, (degree ⁻¹' {r ^ i} \ M.1).ncard ≤ σ i

/-- For a subgroup T of an additive group G, the integer part of the square root of the number
of y in G with r^j y in T. -/
def thetaRanks {G} [AddGroup G] (T : AddSubgroup G) (r j : ℕ) :=
  (Nat.card {y // r ^ j • y ∈ T}).sqrt

/-- For finitely many variables J and any r, σ, `IsCutDegree` holds for all large d: any monomial
ideal omitting at most σ i monomials of degree r^i for each i ≤ d does so for every i. -/
lemma eventually_isCutDegree J [Finite J] r σ : ∀ᶠ d in .atTop, IsCutDegree J d r σ := .mono (by
  induction' (⊥ : AddSemigroupIdeal (J →₀ ℕ)) using WellFoundedGT.fix with _ ih
  obtain h | ⟨i, h⟩ := forall_or_exists_not _
  · exact .of_forall fun _ _ l _ k ↦ (ncard_le_ncard (sdiff_le_sdiff_left l)).trans (h k)
  filter_upwards [(finite_of_degree_eq _).sdiff.eventually_all.2 fun m a ↦ ih _ (left_lt_sup.2
    (a.2 <| closure_le.1 · (mem_singleton m))), Filter.mem_atTop i] with d H l M _ a using
    (not_subset.1 (h <| ncard_le_ncard · |>.trans (a i l))).elim
    (H · ·.1 M (by simp_all [closure_le]) a)) fun _ (h : ∀ M ≥ ⊥, _) ↦ (h · bot_le)

open MvPolynomial Module Submodule Ideal.Quotient Classical Matrix LinearMap Finite

/-- The image of the submodule W of the polynomial ring A[X_J] in the quotient by the ideal T. -/
abbrev imageMod := Submodule.map (mkₐ A T).toLinearMap

/-- The ideal I contains X_c − 1; modulo I, forms of degree r^j span dimension σ j; for j ≤ i,
those in I are exactly those vanishing at all points p a. -/
structure IsCutOut r i (σ : ℕ → ℕ) c (p : ι → _) (I : Ideal (MvPolynomial J k)) where
  X_sub_one_mem : X c - 1 ∈ I
  rank j : finrank k (imageMod I (homogeneousSubmodule J k (r ^ j))) = σ j
  mem_iff_vanish : ∀ j ≤ i, ∀ f ∈ homogeneousSubmodule J k (r ^ j), f ∈ I ↔ ∀ a, eval (p a) f = 0

omit [Finite J] in
lemma restrictSupport_le_homogeneousSubmodule {M} : restrictSupport A (degree ⁻¹' {d} \ M) ≤
  homogeneousSubmodule J A d :=
  homogeneousSubmodule_eq_finsupp_supported _ A _ ▸ restrictSupport_mono A sdiff_le

attribute [local simp] map_eval coeff_map eq_zero_iff_mem coeff_sum Matrix.map RingHom.map_det
  Finset.prod_eq_zero_iff

instance : Module.Finite A (homogeneousSubmodule J A d) := of_fg (homogeneousSubmodule_fg ..)

/-- Let φ : A → k be local, ψ n : A → K jointly injective, r > 1. Assume `IsCutDegree`, and
`IsCutOut` for I₀ at φ(P) and I n at ψ n(P). Then T = ⋂ (ψ n)⁻¹(I n) extends along φ to I₀, and
A[X]/T is A-flat. -/
lemma map_eq_and_flat_of_isCutOut [Field K] {ψ : κ → A →+* K} {r i σ c I₀} (Z : ∀ c,
  (∀ n, ψ n c = 0) → c = 0) (hr : 1 < r) (hc : IsCutDegree J i r σ) {P : ι → _} {I : κ → _} (h₀ :
  IsCutOut r i σ c (φ ∘ P ·) I₀) (h : ∀ n, IsCutOut
  r i σ c (ψ n ∘ P ·) (I n)) (V : ∀ f, f ∈ T ↔ ∀ n, map (ψ n) f ∈ I n) (o := @MonomialOrder.lex J
  (exists_wellFoundedLT J).choose _) : I₀ = T.map (map φ) ∧ Flat A (_ ⧸ T) := by
  let U := T ⊓ I₀.comap (map φ)
  -- W: the leading exponents of the reductions of the forms in U; the other monomials span.
  let W := SubAddAction.mk {m | ∃ g ∈ U, m = o.degree (g.map φ) ∧ g.IsHomogeneous m.degree ∧ m ∈
    (g.map φ).support} fun n _ ⟨g, _, _, _⟩ ↦ ⟨monomial n 1 * g, by simp_all [U.mul_mem_left,
    -coeff_map, o.degree_mul, o.degree_monomial, IsHomogeneous.mul, isHomogeneous_monomial]⟩
  have div {d B} [CommRing B] ρ {I} (hI : ∀ f ∈ U, f.map ρ ∈ I) : imageMod I _ = imageMod .. :=
    (map_mono (@restrictSupport_le_homogeneousSubmodule J B _ d W)).antisymm' fun _ ⟨f, F, _⟩ ↦ by
    choose g hT E G s using fun m : ↥(degree ⁻¹' {d} ∩ W.1) ↦ m.2.2
    let := o.toSyn.linearOrder
    have ⟨c, e⟩ := vecMul_surjective_iff_isUnit.2 (((of (g · |>.coeff ·.1)).isUnit_iff_isUnit_det.2
      (.of_map φ _ ((φ.map_det _).trans (det_of_isLowerTriangular _ fun i _ ↦
      o.coeff_eq_zero_of_lt ∘ (congrArg _ (E i)).ge.trans_lt) ▸ by simpa using! s))).map
      ρ.mapMatrix) (f.coeff ·)
    use f - ∑ m, C (c m) * (g m).map ρ, (mem_restrictSupport_iff B).2 fun k h ↦ (fun D ↦ ⟨D, (by
      simp [← congrFun e ⟨k, D, ·⟩, vecMul_eq_sum] at h)⟩) ((sub_mem F (sum_mem fun m _ ↦ .C_mul
      ((m.2.1 ▸ G m).map ρ) _)).degree_eq_sum_deg_support h).symm, by simpa [eq_zero_iff_mem.2, *]
  have E j := (div φ (fun _ ↦ (·.2)) ▸ h₀.2 j).symm
  have M := hc _ fun j l ↦ by
    obtain ⟨e, -, li⟩ := by simpa [skolem, ← _root_.funext_iff, -Subtype.exists] using ((E j).trans
      (by rw [restrictSupport_eq_span, imageMod, ← span_image, image_image, image_eq_range,
      ← Fintype.coe_image_univ]) ▸ exists_fun_fin_finrank_span_eq .. :)
    refine (Nat.card_le_card_of_surjective e fun m ↦ ?_).trans (by simp)
    by_contra! hm
    let w R [CommRing R] j :=
      Subtype.mk _ (monomial_mem_restrictSupport R (r := 1).2 (.inl (vecCons m e j).2))
    have N {F} [Field F] {p : ι → _} {I n} (H : IsCutOut r i σ c p I) (u : Fin n → _) (v :=
      Set.inclusion restrictSupport_le_homogeneousSubmodule ∘ w F ∘ u) := (minors_eq_zero_iff (v :=
      domRestrict (.pi (p · |> aeval |>.toLinearMap)) _ ∘ v)).trans (show _ ↔ ¬LinearIndependent F
      ((mkₐ F I).toLinearMap.submoduleMap _ ∘ v) by simp [linearIndependent_iff,
      ← apply_linearCombination, _root_.funext_iff, H.3 _ l, Subtype.ext_iff])
    have ⟨a, ha⟩ := not_forall.1 ((N h₀ .succ).1 · (li.of_comp (imageMod ..).subtype))
    let g := ∑ j, ((of fun s b ↦ eval (P (a s)) (w A (.succAbove j b))).det * (-1) ^ j.1) • w A j
    have t {F} [Field F] {ρ : A →+* F} {I} (H : IsCutOut r _ σ c (ρ ∘ P ·) I) :=
      (H.3 _ l _ ((restrictSupport_le_homogeneousSubmodule
      g.2).map ρ)).2 (by simpa [det_succ_row_zero', Function.comp_def, ← C_mul', mul_rotate (det
      _), g, w] using! (N H id).2 (by simpa [H.2] using ·.fintype_card_le_finrank) <| vecCons · a)
    exact (fun s ↦ (g.2 (g.1.support_map_subset _ s)).elim fun D ↦ (· ⟨_, by simp [*, U], rfl,
      D.symm ▸ restrictSupport_le_homogeneousSubmodule g.2, s⟩)) (o.degree_mem_support
      (ne_zero_iff.2 ⟨m, by simpa [g, w, Fin.sum_univ_succ, SetCoe.ext_iff, hm] using! ha⟩))
  have K {R j} [CommRing R] {ρ N} H x a := (div ρ H).le ((exists_homogenization
    (isHomogeneous_X ..) x ((@Nat.lt_pow_self j _ hr).le.trans' a)).imp fun _ ↦ .imp_right
    (· (mkₐ R N) (by simpa [U, V, h₀.1, (h _).1, mk_eq_one_iff_sub_mem] using (H (X c - 1) :))))
  have R {F} [Field F] {I j} h (b := basisRestrictSupport F _) := have := of_basis b
    disjoint_def.1 (disjoint_ker_of_finrank_le (mkₐ F I).toLinearMap
    ((finrank_eq_nat_card_basis b).trans_le ((M j).trans_eq h)))
  have L {j s} H a := ext s 0 (Z _ fun n ↦ congr(AddMonoidAlgebra.coeff
    $((R (div _ (V · |>.1 ·.1 n) ▸ (h n).2
    j).symm) _ (Subset.trans (support_map_subset ..) a) (eq_zero_iff_mem.2 ((V _).1 H n))) ·))
  have le := T.map_le_of_le_comap fun f h ↦ (K (map_id · ▸ ·) f le_rfl).elim fun s ⟨hs, e⟩ ↦ by
    simpa [U, L ((T.sub_mem_iff_left h).1 (SModEq.sub_mem.1 e).1) hs, h] using! e.symm
  refine ⟨le.antisymm' fun f h ↦ (K (inf_le_of_left_le T.le_comap_map) f le_rfl).elim
    fun s e ↦ by simpa [(R (E _)) _ e.1 ((SModEq.mono le e.2).trans
    (eq_zero_iff_mem.2 h))] using e.2.symm, .of_forall_isTrivialRelation @fun _ b x hx ↦ ?_⟩
  choose s E F using fun l ↦ mk_out (x l) ▸ K (map_id · ▸ ·.1) _
    (le_ciSup (x · |>.out.totalDegree) l)
  exact (Flat.isTrivialRelation_of_sum_smul_eq_zero (L (by simpa [← F, ← eq_zero_iff_mem] using! hx)
    (sum_smul_mem _ b (fun _ ↦ E ·)))).imp fun _ ⟨a, y, h⟩ ↦ ⟨a, mk T ∘ y, by simp [← F, h]⟩
end
end

section
/-! Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation
(known result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: PEL datum with theta group, Lagrangian and padding; good primes; class identities. Base
change of group schemes with ring action: points, sections, homomorphisms. -/

open CategoryTheory NumberField Submodule MonoidalCategory Over

variable {E : Type} [Field.{0} E] [CMBase E] {m : Type}
  [Fintype.{0} m]

/-- For ξ in E and vectors x, y of finite adeles of E, the finite adele ξ·∑ᵢ ȳᵢxᵢ. -/
noncomputable def xiForm {E : Type} [Field.{0} E] [NumberField E] [IsCMField E] {m : Type}
    [Fintype.{0} m] ξ (x y : m → 𝔸f E) := algebraMap E _ ξ * Star.star y ⬝ᵥ x

/-- The integer c of E has a padding to r: there are a₁, …, a_{r−3} spanning O_E over ℤ with c
c̄ + 3 + ∑ a_l ā_l = r. -/
def HasPadding E [Field.{0} E] [NumberField E] [IsCMField E] r c := ∃ a :
    Fin (r - 3) → 𝓞 E, span ℤ (.range a) = ⊤ ∧ Star.star c * c + 3 + ∑ l, Star.star (a l) * a l = r

/-- PEL data: β = 1 − β̄, a level 𝔑 ≠ 0, ξ in E, r ≥ 3, a degree bound i, the group T of odd
order dual to the integral vectors under ψ_f(ξ yᴴx), a self-annihilating L containing the
r-torsion, and paddings of norms to r. -/
structure PEL (E) [Field.{0} E] [CMBase E] where
  (β 𝔑 : 𝓞 E) ξ : E
  (rank r i) (T lagrangian : AddSubgroup (_root_.AdelicTorsion E (Fin rank))) star_beta :
    Star.star β = 1 - β
  three_le_r : 3 ≤ r
  level_ne_zero : 𝔑 ≠ 0
  degree_spec : IsCutDegree T i r (thetaRanks T r) ∧ ∀ j ≤ i, ∀ y, r ^ j • y ∈ T →
    y ∈ torsionBy _ _ 𝔑
  odd_card : Odd (Nat.card T)
  mem_T y : torsionClass y ∈ T ↔ ∀ z, torsionClass z = 0 → ψf E (xiForm ξ y z) = 1
  mem_lagrangian y : torsionClass y ∈ lagrangian ↔ ∀ z, torsionClass z ∈ lagrangian →
    ψf E (xiForm ξ y z) = 1
  torsion_mem_lagrangian s : r • s = 0 → s ∈ lagrangian
  exists_padding : HasPadding E r 1 ∧ HasPadding E r β
  nonempty : Nonempty (Fin rank)
  xi_im_pos_and_re_eq_zero v : 0 < (Φ v ξ).im ∧ (Φ v ξ).re = 0
  emb_beta_eq_of_ne : ∀ v ≠ v₀, Φ v β.val = Φ v₀ (Star.star β.val)
  emb_star_beta_ne : Φ v₀ (Star.star β.val) ≠ Φ v₀ β.val

/-- The index set {0, …, rk − 1} of the entries of vectors in E^rk, where rk is the rank in the
data D. -/
abbrev PEL.Index (D : PEL E) := Fin D.rank

/-- The level module: the O_E-submodule of (𝔸_f / Ô)ⁿ of elements killed by the integer 𝔑 of E. -/
noncomputable def PEL.levelTorsion (D : PEL E) := torsionBy _ (_root_.AdelicTorsion E D.Index) D.𝔑

variable (D : PEL E) {S : AlgebraicGeometry.Scheme} {S' : AlgebraicGeometry.Scheme} {b : S' ⟶ S}
  {O : Type} [CommRing O] {A' : CategoryTheory.Over S'} {A : CategoryTheory.Over S} [@AddObj S' A']
  [@AddObj S A] [ModuleObj O A'] [ModuleObj O A] {p : (CategoryTheory.Over.map b).obj A' ⟶ A}
  (h : IsGroupBaseChange (A := A) (B := A') b p)

lemma PEL.T_le_levelTorsion : D.T ≤
  D.levelTorsion.toAddSubgroup := by simpa using! D.degree_spec.2 0

attribute [instance] PEL.nonempty

instance PEL.instFiniteSubtypeTor'FinRkMemAddSubgroupT :
    Finite D.T := by grind [odd_card, Nat.card_pos_iff]

/-- The ideal w of O_E contains neither r nor |T|; for some prime p and integer b, w and a
nonzero prime other than w contain p and β − b, β − b is coprime to β̄ − b, and 𝔑 to w·(p,
β̄ − b). -/
def PEL.IsGoodAt w := (↑D.r ∉ w ∧ ↑(Nat.card D.T) ∉ w) ∧ ∃ p b, Nat.Prime p ∧ ↑p ∈ w ∧
  D.β - (b : ℤ) ∈ w ∧ IsCoprime (D.β - b) (Star.star D.β - b) ∧ Ideal.span {D.𝔑} ⊔ w * .span
  {↑p, Star.star D.β - b} = ⊤ ∧ ∃ v : FinPlace E, v ≠ w ∧ ↑p ∈ v.1 ∧ D.β - b ∈ v.1

/-- The class c in Pic A satisfies the parallelogram law `Pic.ParallelogramLaw` and, for all
T-points x, y of A, ⟨βx, y⟩ = ⟨x, (1 − β)y⟩ and y^*c = ⟨βy, y⟩ + 0^*c, with the pairing
`Pic.pairing`. -/
def PEL.HasClassLaws [ModuleObj (𝓞 E) A] (c : Pic _) := c.ParallelogramLaw ∧ ∀ ⦃T⦄ (x y : T ⟶ A),
  c.pairing (D.β • x) y =
  c.pairing x ((1 - D.β) • y) ∧ c.atPoint y = c.pairing (D.β • y) y + c.atPoint 0

/-- For an O-compatible base change p : A' → A and an S'-scheme T, the O-linear bijection x ↦
p∘x from T-points of A' over S' to T-points of A over S. -/
@[simps! -isSimp apply] noncomputable def IsGroupBaseChange.pointEquiv {T} := LinearEquiv.mk (@h.2
  T).mk' (homMk <| h.1.lift _ _ ·.w) (by have := @h.1.hom_ext; cat_disch) (by cat_disch)

/-- For a base change A' of A along b : S' → S, the O-linear map pulling sections of A over S
back to sections of A' over S'. -/
noncomputable def IsGroupBaseChange.pullSection : (𝟙_ _ ⟶ A) →ₗ[O] 𝟙_ _ ⟶ A' :=
  h.pointEquiv.symm.1 ∘ₗ ⟨⟨_, comp_add (SemiCartesianMonoidalCategory.toUnit _)⟩, by simp⟩

@[reassoc] lemma IsGroupBaseChange.pullSection_comp z : (h.pullSection z).left ≫ p.left =
  b ≫ z.left := by simp [pullSection, pointEquiv]

/-- For a base change p : A' → A, a line bundle N on A and a T-point x of A', the pull-back of
the class of p*N along x equals the pull-back of the class of N along the point p∘x of A. -/
lemma IsGroupBaseChange.atPoint_picClass_pull {T ι N} x : @Pic.atPoint _ A' T (N.pull p.1).picClass
  x = (@LineBundle.picClass _ ι N).atPoint (h.pointEquiv x) := rfl

include h

lemma IsGroupBaseChange.smul_id_comp (m : O) : (m • 𝟙 A').left ≫ p.left = p.left ≫ (m • 𝟙 A).left :=
    congr($(h.2.2 ..).1).trans (by simp [← comp_left])

lemma IsGroupBaseChange.nsmul_id_comp (m : ℕ) : (m • 𝟙 A').left ≫ p.left =
  p.left ≫ (m • 𝟙 A).left := mod_cast h.smul_id_comp m

lemma IsGroupBaseChange.translation_comp z : (_root_.translation (h.pullSection z)).left ≫ p.left =
  p.left ≫ (_root_.translation z).left :=
  congr($(h.2.1 ..).1).trans (by simp [← comp_left, ← h.pointEquiv_apply, pullSection])

/-- Let A', B' be base changes of A, B along b, c : S' → S, and F a natural map from c- to
b-structures. An O-linear homomorphism χ : A → B induces one A' → B', acting on points
through F and χ, compatible with pulled-back sections. -/
lemma IsGroupBaseChange.exists_hom_baseChange {c B' B} [AddObj B'] [AddObj B] [ModuleObj O B']
  [ModuleObj O B] {q} (k : IsGroupBaseChange c q) (F : Over.map c ⟶ _) χ [IsLinear χ] : ∃ ψ :
  _ ⟶ B', (∀ {T} u, k.pointEquiv (u ≫ ψ) = F.1 T ≫ h.pointEquiv u ≫ χ) ∧ IsLinear ψ ∧ ∀ z,
  h.pullSection z ≫ ψ = k.pullSection (z ≫ (χ : _ ⟶ B)) := (k.pointEquiv.surjective
  (F.1 _ ≫ p ≫ χ)).imp fun _ _ ↦ have G := by simp_all [pointEquiv]
  ⟨G, by use {isAdditive_of_universal ?_ with smul_id_comp := ?_} <;> simp [pullSection,
    ← k.pointEquiv.apply_eq_iff_eq, G, ← G (𝟙 _)]⟩
end
