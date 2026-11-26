import Lib.DiscreteSeries.Bordering

section
/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Leading exponent in a row interlaces; leading coefficient is again semi-invariant. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero
open MvPolynomial Finset Finsupp Algebra MonomialOrder

namespace PolyRep

variable {Φ m R} [CommRing R] {c : m → Φ} {x l f}
attribute [local simp] borelMul coeff_map mul_assoc algHom prod single_apply mul_pow ite_apply
attribute [local simp ←] map_pow map_prod C_pow Finsupp.sum.eq_1 pow_mul

/-- Interlacing: for f in ∇ of weight l, the leading exponent γ of f in the variables of row x
(order `PolyRep.columnOrder`; γ = 0 if f = 0) satisfies γ(i) ≤ l(c x, i) − l(c x, i+1), truncated at
0, for all i. -/
lemma degree_rowExpansion_mem_interlacing (hf : f ∈ nabla R c l) :
  columnOrder.degree (rowExpansion x f) ∈ interlacing (l.curry (c x)) := by
  set γ := columnOrder.degree (rowExpansion x f); simp [interlacing, le_def]; by_contra! ⟨i, _⟩
  let θ := aeval (R := R) fun y ↦ Polynomial.CC (X y : MatrixPoly {a // a ≠ x} R) +
    .X * .CC (single (c x, i) (X (y.1, i + 1)) (c y.1, y.2))
  have {p} : (θ p).coeff 0 = .C p := by apply p.induction_on <;> aesop
  let Ψ := (aevalTower ((mapAlgHom θ).comp (algHom ..)) fun j ↦ (C .X * X (i + 1)) ^
    single i 1 j * X i ^ single (i + 1) 1 j * X j).comp (rowExpansion x).toAlgHom
  let b : Φ × _ → type_of% (Ψ f) | (τ, j, k) => single j (C (.C .X ^ single (c x, i) 1 (τ, j) * .X ^
    single (c x, i + 1) 1 (τ, j))) k - single (c x, i) (single (j + 1) 1 k) (τ, j)
  apply absurd congr((($(mem_nabla.1 hf _ b (Ψ ∘ X)).coeff (single (i + 1) (γ i) + single i
    (γ (i + 1)) + γ)).coeff (l (c x, i + 1) + γ i)).coeff (l (c x, i)))
  rw [← aeval_unique, (algHom_ext fun ⟨y, _⟩ ↦ by
    simp +zetaDelta [rowExpansion, ite_and, mul_sub]
    split_ifs <;> subst_vars <;> simp_all <;> ring : aeval _ = (mapAlgHom (.restrictScalars _
    (Polynomial.aeval (.C .X * .X)))).comp (aeval (mapAlgHom (Polynomial.aeval 0) ∘ (borelMul c b
    (Ψ ∘ X) - Ψ ∘ X) + Ψ ∘ X)))]
  simp [Ψ, aevalTower, eval₂_eq, b, -pow_ite, -Prod.mk.injEq, prod_pow_eq_pow_sum, -map_aeval,
    ↓if_mem_support, coeff_sum, Polynomial.coeff_X_pow_mul', ← Polynomial.comp_eq_aeval]
  rw [sum_eq_ite γ] <;> simp_all [X_pow_eq_monomial, Polynomial.coeff_mul_X_pow',
    Finsupp.ext_iff, apply_ite Polynomial.coeff, DFunLike.ite_apply] <;> grind [coeff_eq_zero_of_lt,
    degree_zero, coeff_degree_eq_zero_iff, columnOrder_lt_of_eq_above]

lemma HasLeadingTerm.leadingCoeff_mem_nabla (hf :
  f ∈ nabla R c ((columnOrder.degree (rowExpansion x f)).mapDomain (c x, ·) + l)) :
  columnOrder.leadingCoeff (rowExpansion x f) ∈ nabla R (c ∘ (↑)) l := by
  have H := _root_.mem_nabla.1 hf _ (C ∘ C ∘ @X R _ _) ((mapAlgHom (aeval X)).comp (rowExpansion
    x).toAlgHom ∘ @X R _ _); rw [← aeval_unique, (algHom_ext (by simp [rowExpansion]; aesop) :
    aeval _ = (aevalTower ((algHom ..).comp (aeval (borelMul (c ∘ (↑)) (C ∘ @X R _ _) X)))
    (borelMul c (C ∘ C ∘ @X R _ _) (X ·.2) ⟨x, ·⟩)).comp (rowExpansion x).toAlgHom)] at H
  refine (IsRegular.right · ((sum (fun n ↦ mul of_monomial (prod fun j ↦ by
    simpa only [pow_eq_prod_const] using! prod fun _ ↦ sum (fun _ ↦ mul of_monomial of_monomial) j
      (by grind [columnOrder_lt_of_eq_above j]))) _ ?_ ?_).2.symm.trans
      ((congrArg (AddMonoidAlgebra.coeff · _) H).trans ?_)))
    (by simpa using .monomial (.prod (by simp))) <;> simp_all [leadingCoeff, ↓prod_add_index',
    pow_add, ↓prod_mapDomain_index, ← C_mul', lt_iff_le_and_ne] <;> grind [columnOrder.le_degree]
end PolyRep
end

section
/-! Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with
character. The module here consists of the polynomials on matrices semi-invariant under a triangular
group, for several places at once. The basis is a set of products of minors built one row at a time,
not the semistandard tableaux, and its character is Weyl's quotient of alternants. Source: De
Concini, Eisenbud, Procesi, Young diagrams and determinantal varieties, Invent. Math. 56 (1980);
Akin, Buchsbaum, Weyman, Schur functors and Schur complexes, Adv. Math. 44 (1982), II.2.16, II.4.11.

This file: Products of minors form a basis over every ring, with character identity. -/

open MvPolynomial Finset MonomialOrder Submodule Finsupp Nat
attribute [local simp] zero_lt_iff single_apply sub_mem sum_smul_mem

/-- For finitely many coloured rows and finitely many columns of colours τ and heights h, there
is one family of minor products that, over every commutative ring R, is linearly independent
and whose span contains the semi-invariant module of the corresponding weight.

Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character. -/
lemma PolyRep.exists_minorProduct_basis {Φ J m} [Fintype m] [Fintype J] c τ h :
  ∃ (ι : Type) (_ : Fintype ι) (I : ι → @ColouredTableau Φ J m c τ h), (∀ R [CommRing R],
  LinearIndependent R (fun i ↦ minorProduct R (I i)) ∧ nabla R c (columnWeight τ h) ≤ span R
  (.range fun i ↦ minorProduct R (I i))) ∧ ∀ [Subsingleton Φ] t N (e : Fin N ≃ m) (x : m → ℂ), (∑ i,
  ∏ j, ∏ s, x (I i j s)) * alternant (x ∘ e) 0 = alternant (x ∘ e) (columnWeight τ h ⟨t, ·⟩) := by
  obtain ⟨_, _ | ⟨⟨y⟩⟩⟩ := columnOrder.toSyn.injective, isEmpty_or_nonempty m
  obtain ⟨⟨⟩⟩ := eq_or_ne h 0 <;> [use Unit; use Empty] <;> use .ofFinite _, nofun, fun R ↦ ⟨?_,
    (·.eq_C_of_isEmpty ▸ ?_ ∘ (mem_nabla.1 · R 0 0))⟩, fun _ ↦ rec ?_ fun _ _ ↦ (·.isEmpty.elim
    0) <;> simp_all [univ_eq_empty, Fintype.linearIndependent_iff, minorProduct, minor, alternant,
    ← C_mul', columnWeight,
    ← one_eq_span, pow_add, ← prod_finsetSum_index, funext_iff, prod_pow_eq_pow_sum, nontriviality]
  choose k K B L V using (exists_bordering h <| Subtype.prop ·)
  choose ι _ I hI W using (exists_minorProduct_basis (m := {a // a ≠ y}) _ τ <| k ·)
  use Sigma ι, inferInstance, (B _ <| I _ ·.2), fun R ↦
    have L γ a : HasLeadingTerm (rowExpansion y (sum a fun i (r : R) ↦ r • minorProduct R
      (B γ (I γ i)))) γ (a.sum fun i ↦ (· • minorProduct R (I γ i))) := by simp_all [HasLeadingTerm,
      sum, coeff_sum, degree_le_iff, not_imp_comm]
    ⟨.of_ker _ fun a _ ↦ by_contra fun H ↦ ?_, wellFounded_lt.onFun (f := columnOrder.toSyn ∘
    columnOrder.degree ∘ rowExpansion y).fix fun f ih hf ↦ ?_⟩, @fun S t ↦
    rec (nomatch ·.2 y) fun N _ f x ↦ ?_
  have ⟨x, hx⟩ := a.splitSupport.exists_max_image (columnOrder.toSyn ·) (by simpa [splitSupport])
  simp_all [← (HasLeadingTerm.sum (L · _) _ (by grind) (absurd hx.1)).2, ← map_sum, sigma_sum,
    linearIndependent_iff, mem_splitSupport_iff_nonzero, linearCombination_apply]
  exact (mem_span_range_iff_exists_finsupp.1 ((hI ..).2 (HasLeadingTerm.leadingCoeff_mem_nabla
    (K ⟨_, degree_rowExpansion_mem_interlacing hf⟩ ▸ hf)))).elim fun a ha ↦
    (sub_mem_iff_left _ (sum_smul_mem _ a fun i (_ : i ∈ a.support) ↦ subset_span (by use ⟨_,
    i⟩))).1 (by_cases (ih _ · (by simp [*, minorProduct_mem_nabla])) (by
    have H := L ⟨_, degree_rowExpansion_mem_interlacing hf⟩ a
    rw [ha, sum] at H; revert H
    generalize ∑ i ∈ a.support, a i • minorProduct R (B _ _) = g; intro H
    have : (rowExpansion y (f - g)).coeff (columnOrder.degree (rowExpansion y f)) = 0 := by
      simp [H.2, leadingCoeff]
    grind [degree_sub_le, coeff_degree_eq_zero_iff, zero_mem, EmbeddingLike.map_eq_zero_iff]))
  erw [S.1 t, alternant_succ (.curry _ _) _ (f.2 y), ← (interlacing _).sum_coe_sort,
    alternant_succ 0, mul_left_comm, Fintype.sum_sigma, univ.sum_mul]; congr with γ
  simpa [K γ, Pi.sub_def, V, interlacing, ← univ.mul_sum, mul_assoc, Prod.mk_right_injective] using
    .inl (W γ _ _ (.optionSubtype _ ⟨(finSuccEquiv' _).symm.trans f, f.4 _⟩) (x ·))
  repeat simp [Antitone, columnWeight, ite_and] <;> bound
termination_by Nat.card m
end

section
/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Universal basis, Schur matrices with functoriality and base change, Weyl character
formula. -/
seal Finset.univ Finset.sum Finset.prod


open MvPolynomial Finset Matrix PolyRep Submodule Equiv Classical Fintype Function Sigma
variable {Φ R S : Type} {F : Type _} [CommRing R] [CommRing S] [Fintype Φ] {n : Φ → Type}
  {n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ, Fintype (n' τ)] {κ : Φ → ℕ → ℕ}
  (h : FitsRanks n n' κ) (A : AddSubgroup R) (t : Φ → R) {ι : Type} {M} [Fintype ι]
  (z : ∀ τ, Matrix (n' τ) (n τ) R) (e : Φ → ℕ) (i : WeylIndexFam n' κ) {f} [FunLike F R S]
  [RingHomClass F R S] (φ : F) (g : ∀ τ, Matrix (n τ) (n τ) R) (x : ∀ τ, n τ → R)
attribute [local simp] AlgHom.map_det Matrix.map Matrix.mul_apply minor tableauPoly prod_smul
  prod_univ_sum RingHom.map_det detPow sum_smul sum_mul Fintype.prod_sigma minorProduct
  diagramWeight_apply smul_sum permArray bind₁_bind₁
attribute [local simp ←] rowSubst_rowSubst det_mul det_mul_column pow_mul
  diagramWeight_eq_columnWeight zsmul_eq_mul' C_mul'
  QuotientAddGroup.eq_zero_iff diagonal.eq_1 prod_pow_eq_pow_sum Fin.ext_iff mul_smul

omit [∀ τ, Fintype (n' τ)] in
lemma prod_tableauPoly_mem_nabla {M : Φ → ℕ} {T : ∀ τ, Tableau (n' τ) (M τ) (κ τ)} : ∏ τ,
  tableauPoly R (.mk τ) (T τ) ∈ nabla R fst (diagramWeight M κ) := diagramWeight_eq_columnWeight M
  κ ▸ Eq.subst (by simp) (minorProduct_mem_nabla (⟨⟨_, T _ _ ·.2.2 ·⟩, rfl⟩))

lemma isStdTableauSet_epsilon {k} : IsStdTableauSet (epsilon (@IsStdTableauSet ι M k)) :=
  epsilon_spec (by
  choose _ _ I h W using
    @exists_minorProduct_basis Unit (Σ _, Σ h : Fin M, Fin (k h)) ι _ _ 0 fst (·.2.1)
  use univ.map ⟨_, .of_comp (f := tableauPoly ℤ id) (by simpa using! (h ℤ).1.injective)⟩,
    fun R ↦ ⟨coe_map .. ▸ .image_of_comp _ _ (by simpa using! (h _).1), fun T ↦ by
    simpa [← Set.range_comp] using!
      (h R).2 (minorProduct_mem_nabla (⟨T _ ·.2.2 ·, rfl⟩))⟩, by simpa using W ())

/-- Over any commutative ring R, the minor products b_i indexed by families of chosen standard
fillings are linearly independent.

Known result: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character. -/
lemma linearIndependent_nablaBasis : LinearIndependent R (nablaBasis R n κ) := by
  induction' hk : card Φ with _ ih generalizing Φ R
  exacts [have := card_eq_zero_iff.1 hk; .of_subsingleton' default (by simp [nablaBasis,
      univ_eq_empty]), (card_eq_succ.1 hk).elim fun τ _ ↦ .of_comp (aeval fun (⟨σ, a⟩, j) ↦
    dite (σ = τ) (C <| X ⟨· ▸ a, j⟩) (X ⟨⟨⟨_, ·⟩, a⟩, j⟩)).toLinearMap ((linearIndependent_equiv'
    (piSplitAt ..) (by simp [funext_iff, nablaBasis, prod_eq_mul_prod_subtype_ne _ τ, @Subtype.prop
    _ (· ≠ τ)])).2 (linearIndependent_smul (isStdTableauSet_epsilon.1 R).1 (ih (by simp [*]))))]

lemma isRegular_detPow {e} : IsRegular (detPow R n e) := isRegular_iff_mem_nonZeroDivisors.2
  (mem_nonZeroDivisors_of_injective (f := (coeToMvPowerSeries.algHom _).comp (bind₁
  (permArray (rowPos n) - X))) ((coe_injective _ R).comp (Involutive.injective (by aesop_cat)))
  (MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff (by simp [map_pow, map_sub])))

omit [Fintype Φ] [∀ τ, Fintype (n' τ)] in
lemma PolyRep.rowSubst_minor τ I : rowSubst z (minor R (⟨τ, I ·⟩)) =
  det ((z τ).submatrix I (rowPos n τ).symm) •
  minor R (⟨τ, (rowPos n τ).symm ·⟩) := by simp [rowSubst, reindex_equiv (rowPos n τ).symm]; rfl

@[simp] lemma rowSubst_detPow : rowSubst g (detPow R n e) = (∏ τ,
  (g τ).det ^ e τ) • detPow R n e := by simp [-minor, rowSubst_minor, mul_pow]

/-- Every Borel semi-invariant polynomial whose weight is that of κ increased by e_τ on the
first |n_τ| columns at each place τ is an R-linear combination of the products b_i · ∏_τ
det(y_τ)^{e_τ}, b_i the basis minor products for κ. -/
lemma nabla_le_span_nablaBasis_mul_detPow : nabla R fst (diagramWeight (rankAt n) κ + ∑ τ,
  e τ • (range (rankAt n τ)).sum (.single ⟨τ, ·⟩ 1)) ≤
  (Fintype.linearCombination R (nablaBasis R n κ · * detPow R n e)).range := by
  simp_rw [← Fin.sum_const, ← Fintype.sum_sigma', diagramWeight_eq_columnWeight]
  refine (exists_minorProduct_basis _ (_ ⊕ᵥ _) (_ ⊕ᵥ _)).elim fun _ ⟨_, I, H, _⟩ ↦
    (congrArg _ (sum_sum_type _)).ge.trans ((H R).2.trans (span_le.2 fun _ ⟨i, h⟩ ↦ h ▸ ?_))
  choose T h using ((sigmaSubtype _).symm.surjective <| I i · ·)
  exact ⟨_, by simpa [← funext₂ h, -C_mul', -univ_eq_attach] using! congr((∏ τ, rename (·.map (mk τ)
    id) $(((mem_span_image_finset_iff_exists_fun _).1 ((isStdTableauSet_epsilon.1 R).2 (T <|
    .inl ⟨τ, ·, ·⟩))).choose_spec)) * ∏ τ, ∏ j, $((rowSubst_minor (R :=
    R) (fun _ ↦ 1) τ (T (.inr ⟨τ, j⟩))).symm))⟩

lemma PolyRep.nablaCombination_injective : Injective (nablaCombination (R := R) (n := n) κ) :=
  linearIndependent_nablaBasis.fintypeLinearCombination_injective

/-- Over any commutative ring R, the minor products b_i indexed by families of chosen standard
fillings span exactly the module of Borel semi-invariant polynomials whose weight is built
from κ using heights below |n_τ|. -/
lemma span_nablaBasis : (nablaCombination κ).range = nablaFam R n κ := le_antisymm
  (by simp [span_le, nablaBasis, prod_tableauPoly_mem_nabla, -tableauPoly])
  (by simpa using nabla_le_span_nablaBasis_mul_detPow 0)

lemma sum_coords_nablaBasis (h : f ∈ nablaFam R n κ) : ∑ i,
  invFun (nablaCombination κ) f i • nablaBasis R n κ i = f := invFun_eq (span_nablaBasis.ge h)

/-- Over any commutative ring R and for any exponents e_τ, the polynomials b_i · ∏_τ
det(y_τ)^{e_τ}, with b_i the basis minor products for κ, are linearly independent over R. -/
lemma PolyRep.linearIndependent_nablaBasis_mul_detPow : LinearIndependent R (nablaBasis R n κ · *
  detPow R n e) := linearIndependent_nablaBasis.map_injOn (.mulRight ..) isRegular_detPow.2.injOn

/-- If f = Σ_j x_j b_j · ∏_τ det_τ^{e_τ}, with b_j the basis minor products, and all
coefficients of f lie in an additive subgroup A of R, then every x_i lies in A. -/
lemma PolyRep.coord_mem_of_coeff_mem {x : _ → R} (H : ∑ j,
  x j • (nablaBasis R n κ j * detPow R n e) = f) (h : ∀ d, f.coeff d ∈ A) i : x i ∈ A := by
  have E (S : Type) [CommRing S] j := (nablaBasis ℤ n κ j * detPow ℤ n e).coeff_map (algebraMap ℤ S)
  subst H; simp at E h
  let φ := TrivSqZeroExt.inrHom ℤᵐᵒᵖ _ ∘ TensorProduct.mk ℤ ℤᵐᵒᵖ (R ⧸ A) 1
  simpa [φ] using congr($(linearIndependent_iff.1 (linearIndependent_nablaBasis_mul_detPow e) (φ <|
    x ·) (by ext1; simpa [φ, coeff_sum, E R, E (TrivSqZeroExt ..)] using congr(φ $(h _))) i).snd)

omit [Fintype Φ] in
@[simp] lemma FitsRanks.refl : FitsRanks n n κ := by grind

omit [Fintype Φ] in
@[simp] lemma schurDetExp_self : schurDetExp n n κ = 0 := funext (by simp [schurDetExp])

lemma PolyRep.schur_eq_of_expansion {z} (h : ∀ i, ∑ j, M i j • (nablaBasis R n κ j * detPow R n
  (schurDetExp n n' κ)) = rowSubst z (nablaBasis R n' κ i)) : schur κ z = M := funext fun i ↦
  (linearIndependent_nablaBasis_mul_detPow _).fintypeLinearCombination_injective
  (.trans (invFun_eq ⟨_, h i⟩) (h i).symm)

@[local simp] lemma schur_diagonal_eq_prod : schur κ (diagonal <| x ·) = diagonal fun i ↦ ∏ τ, ∏ h,
  ∏ j, ∏ s, x τ ((i τ).1 h j s) :=
  schur_eq_of_expansion (by simp [diagonal, nablaBasis, rowSubst, ← prod_mul_distrib])

/-- Weyl's character formula over ℂ: for diagonal matrices with entries x_τ, the trace of
S_κ(diag x) times ∏_τ of the Vandermonde determinants of x_τ equals ∏_τ
det(x_{τ,i}^{λ_τ(|n_τ|−1−j)+j}), with λ the partition `diagramWeight` of κ, indexed from 0. -/
lemma weyl_character {a : Φ → ℕ} (e : ∀ τ, Fin (a τ) ≃ n τ) (x : ∀ _, _ → ℂ) : (schur κ (diagonal <|
    x ·)).trace * ∏ τ, (vandermonde (x τ ∘ e τ)).det = ∏ τ, det (of fun i j ↦ x τ (e τ i) ^
    (diagramWeight (rankAt n) κ (τ, j.rev) +
  j)) := by simpa [← card_congr (e _), ← sum_coe_sort (epsilon _), alternant, -univ_eq_attach]
  using! congr(∏ τ, $(isStdTableauSet_epsilon (M := rankAt n τ).2 _ (e τ) _))

@[simp] lemma schur_one (h : ∀ τ, g τ = 1) : schur κ g = 1 :=
  schur_eq_of_expansion (by simp [h, rowSubst])

/-- The Schur matrix of a tuple of diagonal matrices diag(x_τ) is diagonal, with i-th entry ∏_τ
∏_a x_τ(a)^{w}, where w is the number of entries equal to a in the filling i_τ. -/
lemma schur_diagonal : schur κ (diagonal <| x ·) = diagonal (∏ τ, ∏ a, x τ a ^ tableauWeight · τ
  a) := by simp [tableauWeight, @prod_comm _ _ (n _), card_filter, -sum_boole]

include h

lemma PolyRep.diagramWeight_eq_of_fitsRanks : diagramWeight (rankAt n') κ =
  diagramWeight (rankAt n) κ + ∑ τ, schurDetExp n n' κ τ • (range (rankAt n τ)).sum
  (.single ⟨τ, ·⟩ 1) := .trans (sum_congr _ _ fun τ ↦ by grind [zero_smul, schurDetExp,
  sum_eq_ite (rankAt n τ), sum_range_add_sum_Ico _ (h τ).1]) sum_add_distrib

/-- Under the condition `FitsRanks` on n, n', κ, row i of the Schur matrix expands the
substituted basis polynomial: b'_i(zy) = Σ_j S_κ(z)_{ij} b_j(y) ∏_τ det(y_τ)^{d_τ}, with d
given by `schurDetExp`. -/
@[simp ← low] lemma sum_schur_smul_nablaBasis : ∑ j,
  schur κ z i j • (nablaBasis R n κ j * detPow R n (schurDetExp n n' κ)) =
  rowSubst z (nablaBasis R _ κ i) := invFun_eq (nabla_le_span_nablaBasis_mul_detPow _
  (diagramWeight_eq_of_fitsRanks h ▸ rowSubst_mem_nabla _ prod_tableauPoly_mem_nabla))

/-- Base change: if the sizes fit κ (`FitsRanks`), then for a ring homomorphism φ the Schur
matrix of φ(z), φ applied entrywise, is φ applied entrywise to the Schur matrix S_κ(z). -/
@[simp ←] lemma schur_map : schur κ (z · |>.map φ) = (schur κ z).map φ := schur_eq_of_expansion (by
  simpa [rowSubst, map_bind₁] using congr(map (φ : R →+* S) $(sum_schur_smul_nablaBasis h z ·)))

lemma map_schur i j : φ (schur κ z i j) = schur κ (fun τ ↦ of (φ <| z τ · ·)) i j :=
  schur_map h z φ ▸ rfl

/-- If the sizes fit κ (`FitsRanks`), then S_κ(gz) = S_κ(g) S_κ(z) for square matrices g_τ of
size n'_τ and matrices z_τ of size n'_τ×n_τ over R. -/
@[simp ←] lemma schur_mul_left (g : ∀ τ, Matrix (n' τ) (n' τ) R) : (schur κ fun τ ↦ g τ * z τ) =
    schur κ g * schur κ z := schur_eq_of_expansion fun _ ↦ by simpa [h, -C_mul'] using sum_comm

/-- If the sizes fit κ (`FitsRanks`), then S_κ(zg) = ∏_τ det(g_τ)^{d_τ} · S_κ(z) S_κ(g) for z_τ
of size n'_τ×n_τ and g_τ square of size n_τ, with exponents d_τ given by `schurDetExp`. -/
lemma schur_mul_right : schur κ (fun τ ↦ z τ * g τ) =
  (∏ τ, (g τ).det ^ schurDetExp n n' κ τ) • (schur κ z * schur κ g) := schur_eq_of_expansion
  fun _ ↦ by simpa [h, -detPow, -C_mul', mul_sum, mul_left_comm] using sum_comm

/-- If the sizes fit κ (`FitsRanks`), the (i,j) entry of S_κ(z) is the product over places τ of
the (i_τ, j_τ) entries of the one-place Schur matrices S_{κ_τ}(z_τ). -/
lemma schur_apply_eq_prod j : schur κ z i j = ∏ τ, schur (fun () ↦ κ τ) (fun _ ↦ z τ) (fun _ ↦ i τ)
    fun _ ↦ j τ := congrFun₂ (schur_eq_of_expansion fun i ↦ by simpa [nablaBasis, rowSubst, -C_mul']
  using! (congr(∏ τ, rename (·.map (mk τ ·.2) id) $(((piUnique _).symm.sum_comp _).trans
                 (sum_schur_smul_nablaBasis (const Unit (h τ)) (fun _ ↦ z τ) fun _ ↦ i τ))))) ..

lemma schur_smul : (schur κ fun τ ↦ t τ • z τ) = (∏ τ, t τ ^ ∑ i ∈ range (rankAt n' τ), i * κ τ i) •
    schur κ z := by simp [smul_eq_diagonal_mul, schur_mul_left h, sum_range]
end

section
/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Rational representation of a product of GL_n on Weyl's lattice, twisted by
determinants. -/

/-- The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ. -/
noncomputable def weylRep {Φ R} [CommRing R] [Fintype Φ] {n : Φ → _}
    [∀ τ, Fintype (n τ)] κ (e : Φ → ℤ) := MonoidHom.mk ⟨fun g : ∀ τ, GL (n τ) R ↦
  (∏ τ, (g τ).det ^ e τ) • schur κ (g · |>.1), by simp⟩ (by simp [mul_zpow, smul_mul_smul])
end
