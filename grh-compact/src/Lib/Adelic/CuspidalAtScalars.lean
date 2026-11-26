import Lib.Adelic.CuspidalFunction
import Lib.Adelic.ValuedMatrix

section
/-! Definitions for Green's characters of GL_n(k): τ_P, Ξ_c, labels, χ∘det, the reflection sum and
the idempotents e_c. Then general lemmas on powers and Frobenius orbits of roots (textbook or
folklore).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Definitions: labels, cuspidal Green characters, their products, determinant characters,
idempotents. Roots of an irreducible polynomial over a finite field form a Frobenius orbit. -/

noncomputable section

open Polynomial Classical Fint Function Real UniqueFactorizationMonoid FiniteField Nat Multiset
variable {k} [Field k] [Finite k] {K} [Field K] [Algebra k K] (T : MulChar K ℂ) {n} [Fintype n]
  (Q r : ℕ) (P c : k[X]) (χ : MulChar k ℂ)

/-- The finite set of monic polynomials of degree r over the finite field k. -/
def monicsOfDegree k [Field k] [Finite k] r := @Set.toFinset k[X] {_c | _}
    (.ofEquiv _ ((monicEquivDegreeLT r).trans (degreeLTEquiv ..).toEquiv).symm)

/-- A chosen injective multiplicative character from the algebraic closure of k to ℂ (arbitrary
if there is none). -/
def faithfulChar k [Field k] : MulChar (AlgebraicClosure k) ℂ := epsilon (Injective ·)

/-- The field K is algebraically closed and the multiplicative character T : K → ℂ is injective,
so it embeds K^× in ℂ^×. -/
class IsFaithfulMulChar K [Field K] (T :
  outParam (MulChar K ℂ)) extends IsAlgClosed K where injective : Injective T

/-- The character θ_x = T^a of K, where a is a chosen natural number with T(x) =
exp(2πi/(Q−1))^a. -/
def thetaChar x := T ^ epsilon (T x = .exp (2 * π * .I / (Q - 1 :)) ^ ·)

/-- Green's class function τ_P: (−1)^d times the rank d part of C_{θ_x}, where d = deg P, x is a
chosen root of P in K, and θ_x is taken for Q = |k|^d. -/
def greenTau := (-1 : ℂ) ^ P.natDegree • (Hall.greenCuspidal k
  (thetaChar T (.card k ^ P.natDegree) (epsilon (P.aeval · = 0)))).rankPart P.natDegree

/-- The multiplicative map c ↦ Ξ_c: the product, by parabolic induction, of τ_P over the monic
irreducible factors P of c with multiplicity; Ξ_0 = 0. -/
def labelChar : k[X] →* Hall k :=
    ⟨⟨fun c ↦ ite (c = 0) 0 ((normalizedFactors c).map (greenTau T)).prod, by simp⟩, by aesop⟩

/-- c is a label of degree r: a monic squarefree polynomial over k of degree r with nonzero
constant term. -/
def IsLabel := c.Monic ∧ Squarefree c ∧ c.natDegree = r ∧ c.coeff 0 ≠ 0

/-- The class function χ∘det on endomorphisms of every dimension, written through the constant
term of the characteristic polynomial. -/
def detChar : Hall k := fun c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)

/-- The element ∑ χ(det h)⁻¹ h of ℂ[GL_n(k)], summed over the invertible h of the form 1 + u lᵀ,
u a column vector. -/
def reflectionSum l := groupAlgElem fun h : GL n k ↦
  ite (∃ u, h.1 = 1 + .vecMulVec u l) (χ⁻¹ h.1.det) 0

/-- The element e_c = ∑ (Ξ_c(1)/|G|)·conj Ξ_c(g)·g of ℂ[G], G = GL_n(k), Ξ_c formed with
`faithfulChar`, if c is a label of degree |n|; zero otherwise. -/
def labelIdem n [Fintype n] (c : k[X]) := let Ξ := (labelChar (faithfulChar k) c).evalGL (n := n)
  ite (IsLabel (Fintype.card n) c) (groupAlgElem fun g ↦
    Ξ 1 / Nat.card (GL n k) * starRingEnd ℂ (Ξ g)) 0

variable {k K : _} [Field k] [Finite k] [Field K] [Algebra k K] {P : k[X]} (hP : Irreducible P) {x :
  K} (hx : aeval x P = 0)

@[simp] lemma pow_pred_eq_one_iff {Q} (hQ : 2 ≤ Q) : x ^ (Q - 1) = 1 ↔ x ≠ 0 ∧ x ^ Q = x := by
  grind [pow_sub₀, zero_pow]

@[simp] lemma algebraMap_pow_card_pred_eq_one (a : kˣ) : algebraMap k K a ^ (.card k - 1) = 1 :=
  card_units k ▸ mod_cast by simp

include hP hx

lemma root_pow_card_pow_eq_self_iff {n} : x ^ .card k ^ n = x ↔ P.natDegree ∣ n := by
  simp [hP.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← hP.dvd_iff_aeval_eq_zero hx]

lemma root_pow_card_pow_eq_iff_modEq {a b} : x ^ .card k ^ a = x ^ .card k ^ b ↔
  a ≡ b [MOD P.natDegree] := by
  have := @(frobeniusAlgHom k K).injective.eq_iff
  induction a, b using Nat.recDiagAux <;> simp_all [pow_succ, pow_mul, eq_comm, modEq_iff_dvd',
    ← root_pow_card_pow_eq_self_iff hP hx, modEq_zero_iff_dvd]

lemma aroots_eq_frobenius_orbit : P.aroots K = .map (x ^ .card k ^ ·) (range P.natDegree) := by
  have := (aeval_algHom <| frobeniusAlgHom k K ^ ·)
  apply roots_eq_of_degree_le_card_of_ne_zero (S := ⟨_, (nodup_range _).map_on _⟩) <;> simp_all
    [hP.ne_zero, coe_frobeniusAlgHom, ↓root_pow_card_pow_eq_iff_modEq hP, ModEq, mod_eq_of_lt]

lemma aroots_pow_eq_frobenius_orbit {j} : (P ^ j).aroots K =
  .map (x ^ .card k ^ ·) (range (P ^ j).natDegree) ∧ x ^ .card k ^ (P ^ j).natDegree =
  x := by induction j <;> simp_all [aroots_eq_frobenius_orbit _ hx, @pow_add ℕ, add_mul, add_smul,
  range_add, pow_mul, root_pow_card_pow_eq_self_iff hP, -card_eq_fintype_card]

lemma exists_pow_card_pow_eq_of_root {y} : aeval y P = 0 → ∃ i < P.natDegree, x ^ .card k ^ i = y :=
  by simpa [hP.ne_zero] using congr(y ∈ $(aroots_eq_frobenius_orbit hP hx)).mp
end
end

section
/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Cuspidal class functions vanish unless the characteristic polynomial is a prime power. -/

open Hall LinearMap Module Polynomial StableSubspace Submodule

variable {k V} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {g : End k V}

omit [Finite k] in
lemma charpoly_eq_pow_of_isNilpotent {P} (hP : Irreducible P) (hm : Monic P) (h :
  IsNilpotent (aeval g P)) : charpoly g = P ^ (finrank k V / P.natDegree) := by
  have := charpoly_dvd_charpoly_aeval_comp (Y := g.toMatrixAlgEquiv (finBasis ..)) P
  simp_all [↓aeval_algHom_apply, toMatrixAlgEquiv, h.charpoly_eq_X_pow_finrank]
  grind [charpoly_natDegree, natDegree_pow, Nat.mul_div_left, dvd_prime_pow hP.prime,
    eq_of_monic_of_associated, charpoly_monic, Monic.pow]

/-- Over a finite field k, if F is cuspidal (`Hall.IsCuspidal`) and does not vanish at the class
of an endomorphism g, then the characteristic polynomial of g is a power of an irreducible
polynomial. -/
lemma Hall.IsCuspidal.exists_charpoly_eq_pow {F} (h : IsCuspidal F) (hF : F (simClassOf g) ≠ 0) :
  ∃ P j, Irreducible P ∧ charpoly g =
  P ^ j := by_cases (⟨X, 0, irreducible_X, g.charpoly_monic.eq_one_of_isUnit ·⟩) fun u ↦ by
  have ⟨P, m, i, d⟩ := (g.toMatrixAlgEquiv _).charpoly.exists_monic_irreducible_factor u
  have ⟨N, I, n⟩ := ((aeval g P).eventually_isCompl_ker_pow_range_pow.and Nat.eventually_pos).exists
  have c Y h := DFunLike.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute
    ((P ^ N).aeval_mem_adjoin_singleton k g) ((Y * g).ext h))
  simp_all [aeval_algHom_apply, i.dvd_iff_not_isCoprime,
    ← isUnit_aeval_iff_isCoprime.trans isCoprime_comm]
  let C : StableSubspace g := ⟨ker (aeval g P ^ N), by simp_all [← c]⟩
  have E : ∀ x, simClassOf (blockTriangularEnd C.endOnSub C.endOnQuot x) = simClassOf g :=
    (surjective_of_injective (.of_ker (C.endOnSub.compRight k - C.endOnQuot.lcomp ..) fun y e ↦
    y.ext ((reindex_equiv (quotientEquivOfIsCompl _ _ I).symm).1.2 fun ⟨_, v, rfl⟩ ↦ Subtype.ext
    ((c (C.1.subtype ∘ₗ y ∘ₗ mkQ _) (congr($(sub_eq_zero.1 e) ⟦·⟧ |>.1).symm) v).trans
    (y _).2)))).forall.2 fun y ↦ simClassOf_eq_of_equiv (.skewProd (quotKerEquivRange _) 1 y ≪≫ₗ
    prodEquivOfIsCompl _ _ I.symm)
    (by simp [Submodule.Quotient.forall, endOnSub, endOnQuot, C]; grind)
  exact ⟨P, i, _, charpoly_eq_pow_of_isNilpotent i m
    ⟨N, by simpa [*, C, blockAverage_simClassOf, n.ne', ← isUnit_iff_ker_eq_bot,
    finrank_zero_iff, ↓finrank_eq_zero] using h (simClassOf C.endOnSub) (simClassOf C.endOnQuot)⟩⟩

lemma greenCuspidal_congr {K} [Field K] [Algebra k K] η η' {a} (h : ∀ z, g.charpoly.aroots K =
  .map (z ^ .card k ^ ·) (.range (finrank k V)) ∧ z ^ .card k ^ finrank k V = z → a * η z = η' z) :
  greenCuspidal k η' (simClassOf g) = a * greenCuspidal k η (simClassOf g) := by_contra (· <| by
  simp [greenCuspidal, mul_simClassOf, mulMu, Finset.mul_sum, ← mul_assoc,
    ← Multiset.sum_map_mul_left]
  congr! with W _ z; grind +splitImp [isCuspidal_greenCuspidal, → IsCuspidal.exists_charpoly_eq_pow,
    aroots_pow_eq_frobenius_orbit, mem_aroots,
    pow_ne_zero, congr(aeval z $(charpoly_endOnSub_mul_endOnQuot _ W)), charpoly_natDegree])
end

section
/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Values of Steinberg and cuspidal class functions at field elements, by generating
series. -/

open Module Algebra Finset Fint Hall Lagrange Matrix Polynomial Submodule minpoly

variable {k K F V} [Field k] [Finite k] [Field K] [Algebra k K] [Field F] [Finite F] [Algebra k F]
  (z : PowerBasis k F) [AddCommGroup V] [Module k V] [Module F V] [IsScalarTower k F V]
  [Module.Finite k V] [Module.Finite F V]

/-- For a finite field k with q elements, the order of GL_n(k) is the product of q^i(q^{i+1} −
1) over 0 ≤ i < n, as an identity in any field R. -/
lemma card_GL_eq_prod {n R} [Fintype n] [Field R] : Nat.card (GL n k) =
  ∏ i ∈ range (Fintype.card n), (Nat.card k ^ i * (Nat.card k ^ (i + 1) - 1) : R) := by open Calc in
  simp [↓Nat.card_congr (Units.mapEquiv (reindexRingEquiv k (Fintype.equivFin n)).toMulEquiv).1,
    ↓card_GL_field, Nat.pow_le_pow_right Fintype.card_pos]; induction Fintype.card n <;> simp_all
    [Fin.prod_univ_succ, prod_range_succ, pow_succ, ← sub_mul] <;> ring

attribute [local simp] mul_simClassOf finrank_zero_iff eval_finsetSum mul_smul add_smul

/-- Let F = k[z] have Q elements, g be multiplication by z on an F-space V of dimension m, and N
= ∏_{i<m}(X − Q^i). Then 𝟙⁻¹(g) = N(0), and C_η(g) (`Hall.greenCuspidal`) is −N'(1) times the
sum of η over the roots in K of the minimal polynomial of z. -/
lemma moebius_and_greenCuspidal_lsmul η : let N : ℂ[X] := nodal (range (finrank F V)) fun x ↦
    ↑(Nat.card F ^ x)
  let g := lsmul k k V z.gen; moebius (simClassOf g) = N.eval 0 ∧ greenCuspidal k η (simClassOf g) =
  -(((minpoly k z.gen).aroots K).map η).sum * N.derivative.eval 1 := by
  intro N g; have := @finite_of_finite k V
  let S (W : StableSubspace g) : Submodule F V := ⟨W.1.1, fun c _ ↦ (z.exists_eq_aeval'
    c).choose_spec ▸ (aeval_apply_smul_mem_of_le_comap' · _ _ W.2)⟩
  rw [← one_mul moebius, (eq_of_degree_sub_lt_of_eval_index_eq _ (Nat.cast_injective.comp
    (Nat.pow_right_injective Finite.one_lt_card)).injOn ((degree_lt_iff_coeff_zero ..).2
    fun n h ↦ ?_) fun j h ↦ (eval_nodal_at_node h).trans ?_ : N = ∑ W, monomial (finrank F (S W))
    (moebius (simClassOf W.endOnQuot)))]
  simp [(by grind [mu_mul_constOne, greenCuspidal_mul_constOne η] : greenCuspidal k η = -brauerLift
    k η * moebius), z.finrank, ← finrank_mul_finrank k F, z.dim_pos.ne', zero_pow_eq, mul_sum,
    derivative_monomial, fun W ↦ show simClassOf W.endOnSub = simClassOf
    (lsmul k k (S W) z.gen) from rfl, monic z.isIntegral_gen, charpoly_eq_pow_of_isNilpotent
    (irreducible z.isIntegral_gen), Multiset.map_nsmul, Multiset.sum_nsmul]; ac_rfl
  erw [coeff_sub, ← (isMonicOfDegree_monomial_one _).coeff_eq ⟨by simp, nodal_monic⟩ h,
    finsetSum_coeff, Fintype.sum_eq_single ⟨⊤, by simp⟩, finrank_top] <;> simp_all
    [coeff_monomial]; intro a b n; bound [(S ⟨a, b⟩).finrank_lt (n <| top_unique ·.ge)]
  simp; simp_rw [pow_right_comm _ j, ← Nat.cast_pow, ← card_eq_pow_finrank, Nat.cast_pow,
    Fintype.card_subtype, ← sum_boole, Fintype.sum_pow, Fintype.prod_boole, mul_sum,
    ← SetLike.mem_coe, ← Set.range_subset_iff, ← span_le]; rw [sum_comm, sum_eq_zero]
  intro v _; let U : StableSubspace g := ⟨(span F (.range v)).restrictScalars k, by aesop⟩
  simpa [sum_filter, U, mt finrank_le_of_span_eq_top, mem_range.1 h, sum_inverse_constOne] using!
    ((StableSubspace.sum_comap U.1.mkQ (g' := U.endOnQuot) (by bound) _).trans
    (by simp)).trans congr($(mul_comm constOne moebius) (simClassOf U.endOnQuot))

lemma mulMu_greenCuspidal_lsmul η [Nontrivial V] : (greenCuspidal k η).mulMu (simClassOf
  (lsmul k k V z.gen)) * (.card V - 1 : ℕ) = (((minpoly k z.gen).aroots K).map η).sum * Nat.card
  {e : V ≃ₗ[k] V // ∀ x, e (z.gen • x) = z.gen • e x} := by
  simp_rw [mulMu, moebius_and_greenCuspidal_lsmul z η]; rw [@natCard_eq_pow_finrank F V, eq_comm,
    ← Nat.card_congr ((GeneralLinearGroup.toLin' (finBasis F V)).1.trans ?_), card_GL_eq_prod,
    ← Nat.sub_add_cancel finrank_pos, nodal, prod_range_succ']; simp [eval_prod, pow_succ,
    prod_range_succ, ← neg_sub (1 : ℂ), -neg_sub, -Nat.card_eq_fintype_card, prod_neg]; ring
  exact .mk (⟨·.toLinearEquiv.restrictScalars k, by simp⟩) fun ⟨f, _⟩ ↦ .ofLinearEquiv {f with
    map_smul' c := by induction eq_top_iff.1 z.adjoin_gen_eq_top c using adjoin_induction <;> aesop}
end
