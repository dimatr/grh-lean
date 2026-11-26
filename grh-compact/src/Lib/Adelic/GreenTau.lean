import Lib.Adelic.CuspidalAtScalars

section
/-! Known result: The Brauer lift is a virtual character, and cuspidal times Steinberg is induced
from a torus. Without Brauer induction, the character induced from the Coxeter torus is divided by
the Steinberg character, taken as a Möbius function on semisimple classes, compatibly with the
Galois action. Only the vanishing half of Crapo's theorem appears. Source: Green 1955, Thm 1; T. A.
Springer, Sém. Bourbaki 441 (1973/74), 1.1-1.7; for Steinberg times torus character, R. Carter,
Finite groups of Lie type (1985), 7.4.5, as cited by Hiss-Zalesski; for the vanishing of the Möbius
number off semisimple modules, P. Hall's lemma, D. Krasula, arXiv 2403.05656, Lemma 23, and H.
Crapo's complementation theorem (1966).

Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Naming characters of F_Q^× by field elements; multiplicativity and norm compatibility.
Cuspidal character times Steinberg is induced from the Coxeter torus. -/

open IntermediateField Complex ComplexConjugate Finset Hall IsGalois LinearEquiv Module MulChar
  Polynomial Units LinearMap.GeneralLinearGroup

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K] (T) [IsFaithfulMulChar K T]
  {Q m} {x y z : K} (hQ : 2 ≤ Q) (hx : x ^ (Q - 1) = 1) (η : K → ℂ)

include hQ hx

omit [IsFaithfulMulChar K T] in
/-- Let T be a multiplicative character K → ℂ, Q ≥ 2, and x^(Q−1) = 1. Then there is a natural
number e with θ_x = T^e (θ_x taken for Q) and T(x) = exp(2πi/(Q−1))^e. -/
lemma thetaChar_spec : ∃ e, thetaChar T Q x = T ^ e ∧ T x = exp (2 * Real.pi * I / (Q - 1 :)) ^ e :=
  have : NeZero (Q - 1) := ⟨by lia⟩; ⟨_, rfl, @Classical.epsilon_spec _ (_ = _ ^ ·) (by
    grind [(isPrimitiveRoot_exp _ this.1).eq_pow_of_pow_eq_one, congr(T $hx)])⟩

omit [IsFaithfulMulChar K T] in
/-- Let Q ≥ 2, N ≠ 0 with N = (Q − 1)m, and x^{Q−1} = 1. If T(z) = exp(2πi/N)^a, then
θ_x(z^m) = T(x)^a, where θ_x is formed with Q. -/
lemma thetaChar_apply_pow {m a N} (hN : N ≠ 0) (hm : N = (Q - 1) * m)
    (h : T z = exp (2 * Real.pi * I / N) ^ a) : thetaChar T Q x (z ^ m) = (T ^ a) x := by
  obtain ⟨⟨x, rfl⟩, ⟨z, rfl⟩, _, _⟩ := IsUnit.of_pow_eq_one hx (by lia),
    T.apply_ne_zero_iff.1 (h.trans_ne (by simp)), thetaChar_spec T hQ hx
  simp_all [← exp_nsmul, pow_apply_coe]; grind [Nat.cast_eq_zero]

omit [IsFaithfulMulChar K T] in
lemma thetaChar_mul : y ^ (Q - 1) = 1 → z ^ (Q - 1) = 1 → thetaChar T Q (x * y) z =
  thetaChar T Q x z * thetaChar T Q y z := by grind [thetaChar_spec T,
  @thetaChar_apply_pow (m := 1), mul_pow, map_mul (thetaChar T Q z) x y]

omit [IsFaithfulMulChar K T] in
lemma thetaChar_eq_apply_norm_pow {m r a} (h : 2 ≤ m) (e : m = Q ^ r) (o : x ^ a = y) :
  z ^ (m - 1) = 1 → thetaChar T m y z = thetaChar T Q x (z ^ ∑ i ∈ .range r,
  Q ^ i) ^ a := by grind [thetaChar_spec T, thetaChar_apply_pow T, @thetaChar_apply_pow
  (m := 1), map_pow (thetaChar T m z) x a, pow_mul, one_pow, pow_right_comm, geom_sum_mul_of_one_le]

/-- For T injective, the group isomorphism χ ↦ x_χ from the multiplicative characters of k to
k^×, inverse to a ↦ θ_a restricted to k, with θ_a taken for Q = |k|. -/
noncomputable def charName : MulChar k ℂ ≃* kˣ := .symm (.ofBijective (F := _ →* _)
    (.mk' (fun a ↦ ⟨(thetaChar T (.card k) (algebraMap k K a)).comp (algebraMap k K), by simp⟩) (by
    simp [MulChar.ext_iff, thetaChar_mul T Finite.one_lt_card])) (((injective_iff_map_eq_one
  _).2 fun a h ↦ (thetaChar_spec T Finite.one_lt_card (algebraMap_pow_card_pred_eq_one a)).elim
  fun e ⟨p, q⟩ ↦ by rw [← Nat.card_units, ← IsCyclic.exponent_eq_card, ((isPrimitiveRoot_exp _
  NeZero.out).pow_eq_one_iff_dvd e).2 (Monoid.exponent_dvd_of_forall_pow_eq_one _)] at q <;> cases e
  <;> simp_all [pow_apply', ← map_pow, IsFaithfulMulChar.injective, map_eq_one_iff, MulChar.ext_iff,
  ← val_eq_one]).bijective_of_nat_card_le (card_eq_card_units_of_hasEnoughRootsOfUnity ..).le))

omit hQ hx

/-- For T injective, every multiplicative character χ of k is the restriction to k of θ_{x_χ},
formed with Q = |k|: θ_{x_χ}(y) = χ(y) for all y ∈ k. -/
lemma thetaChar_charName χ y : thetaChar T (.card k) (algebraMap k K (charName T χ))
  (algebraMap k K y) = χ y := congr($((charName T).1.3 χ) y)

lemma charName_pow_eq_one {T} [IsFaithfulMulChar K T] {χ M} (h : χ ^ M = 1) :
    (charName T χ).1 ^ M = (1 : k) := mod_cast by simp [← map_pow, h]

open Fint

/-- For a finite extension L of k embedded by φ in K, the inner product on GL_{[L:k]}(k) of C_η with
B·μ is the mean over z ∈ L^× of conj η(φz) times B at multiplication by z.

Known result: The Brauer lift is a virtual character; cuspidal times Steinberg is induced from a
torus. -/
lemma rankInner_greenCuspidal_mulMu {L} [Field L] [Finite L] [Algebra k L] (φ : L →ₐ[k] K) (B :
  Hall k) : rankInner (finrank k L) (greenCuspidal k η) B.mulMu = finMean fun z :
  Lˣ ↦ conj (η (φ z)) * B (simClassOf (LinearMap.mulLeft k z.1)) :=
  let ρ (e : L ≃ₗ[k] L) := (e.conjAlgEquiv k).toAlgHom.comp (Algebra.lmul ..); let := φ.toAlgebra
    have H e z : simClassOf (ρ e z) = simClassOf (LinearMap.mulLeft k z) :=
      simClassOf_eq_of_equiv e⁻¹
    have E g : (greenCuspidal k η).mulMu (simClassOf g) =
        (∑ z, η (φ z) * Nat.card {e // ρ (generalLinearEquiv k L e) z = g}) / Nat.card Lˣ := by
      obtain h | ⟨a, y, rfl⟩ := em' (∃ a y, ρ a y = g); simp_all; by_contra! ⟨h0, h1⟩
      have ⟨P, j, p, e⟩ := (isCuspidal_greenCuspidal η).exists_charpoly_eq_pow h0; let V :=
        AEval' g; let A := AdjoinRoot P
      let : Module A V := IsTorsionBy.module (congr($(minpoly.dvd_iff.1 ((isSemisimple_of_mu_ne_zero
        h1).minpoly_squarefree.isRadical _ _ (e ▸ g.minpoly_dvd_charpoly))) ·))
      rcases Fact.mk p, ‹Finite V›, show IsScalarTower k A V from IsTorsionBySet.isScalarTower _
      have r := finrank_mul_finrank k A
      let := (FiniteField.nonempty_algHom_of_finrank_dvd (L := L) ⟨_, (r V).symm⟩).some.toAlgebra
      let t := ofFinrankEq _ _ (mul_left_cancel₀ (by grind [r L, finrank_pos]) (r L ▸ r V))
      exact h (t.symm.restrictScalars k) _ (.trans
        (.symm (LinearMap.ext (t.eq_symm_apply.2 <| t.map_smul (.root P) ·))) (aeval_X _))
      erw [eq_div_iff (by simp), H, Nat.card_units, mulMu_greenCuspidal_lsmul (adjoin.powerBasis
        (integral k y)), minpoly_gen, ← (splits _ y).map_aroots_algebraMap, Multiset.map_map,
        ← sum_mk _ (nodup_roots (.map (separable ..))), sum_mul]
      apply sum_subset_zero_on_sdiff le_top <;> intro z h; simp [(show ρ · z ≠ ρ a y from
        ne_of_apply_ne (aeval · (minpoly k y)) (by simp_all [aeval_algHom_apply,
        minpoly.ne_zero_of_finite]))]
      obtain ⟨c, rfl⟩ := minpoly.exists_algEquiv_of_root (.of_finite ..) (mem_aroots.1 h).2
      exact congr(_ * $(Nat.card_congr (((Equiv.mulLeft a * .mulRight c).trans (generalLinearEquiv
        ..).1.symm).subtypeEquiv fun e ↦ ((a * e).forall_congr
        (by simp [ρ, Algebra.smul_def, mul_eq_trans])).trans LinearMap.ext_iff.symm)))
    star_injective (by simp [*, rankInner_eq_classInner_simClassOf, classInner, finMean,
      Fintype.sum_eq_add_sum_subtype_ne _ (0 : L),
      mul_left_comm, fun e (z : Lˣ) g ↦ (.symm Units.ext_iff : ρ e z = g.1 ↔ z.map (ρ e) = g),
      Ne.symm, mul_div, reindex_equiv unitsEquivNeZero, Fintype.card_subtype, ← sum_boole,
      ← sum_comm_cycle, ← sum_div, mul_sum, field, mul_comm _ (η _)])

instance : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
end

section
/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Cuspidality, independence of choices and orthogonality of the characters of irreducible
polynomials. -/


open Polynomial Hall IsAlgClosed Classical FiniteField LinearMap Finset minpoly Multiset Module
  UniqueFactorizationMonoid ComplexConjugate AdjoinRoot
variable {k K : Type _} [Field k] [Finite k] [Field K] [Algebra k K] {T : MulChar K ℂ}
  {P : k[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0) {x : K}
  (hx : P.aeval x = 0)

@[simp] lemma labelChar_eq_greenTau (T : MulChar K ℂ) (hP : Irreducible P) (hm : P.Monic) :
  labelChar T P = greenTau T P
  := by simp [labelChar, normalizedFactors_irreducible hP, hm.normalize_eq_self, hP.ne_zero]

attribute [local simp] greenTau rankInner Hall.ext_iff charpoly_natDegree thetaChar_charName
  blockAverage Finite.one_lt_card aeval_algHom_apply coe_frobeniusAlgHom

/-- For every polynomial P and multiplicative character T of K, τ_P is cuspidal: its mean over block
triangular matrices with given diagonal blocks vanishes whenever both blocks have nonzero
dimension. -/
lemma isCuspidal_greenTau : (greenTau T P).IsCuspidal := fun _ ↦ by
  simp_intro ..; split <;> simp; apply_rules [isCuspidal_greenCuspidal]

lemma greenTau_eq_zero_of_dim_ne c : c.dim ≠ P.natDegree → greenTau T P c = 0 := by aesop

variable [IsFaithfulMulChar K T]

/-- If the endomorphism σ of L is y ↦ y^(q^i) with q = |k|, then the roots of σP in the
algebraically closed field K are the q^i-th powers of the roots of P, with multiplicity. -/
lemma aroots_map_frobenius_pow [IsAlgClosed K] {L} [Field L] [Algebra L K] {i} (σ : L →+* L)
    (h : ∀ y, σ y = y ^ .card k ^ i) (P : L[X]) :
    (P.map σ).aroots K = (P.aroots K).map (· ^ .card k ^ i) := by
  open Fint in convert (splits _).roots_map (frobeniusAlgHom k K ^ i).1 <;> aesop

include hP h0 hx

lemma root_pow_card_pow_pred_eq_one : x ^ (.card k ^ P.natDegree - 1) = 1 ∧ 2 ≤
  .card k ^ P.natDegree := by aesop (add simp [(root_pow_card_pow_eq_self_iff hP), Nat.succ_le_iff,
  hP.natDegree_pos.ne', aeval_def])

omit [IsFaithfulMulChar K T] in
lemma rankPart_greenCuspidal_pow {a} [NeZero a] : let d := P.natDegree; (greenCuspidal k
    (thetaChar T (.card k ^ d) (x ^ a))).rankPart d = (greenCuspidal k (thetaChar T (.card k ^ d)
    x <| · ^ a)).rankPart d := by
  simp [Hall.ext_iff]; intros; split_ifs <;> [subst_vars; rfl]
  rw [greenCuspidal_congr, one_mul]; intro z; by_cases z =
  0 <;> simp_all [thetaChar_eq_apply_norm_pow T _ _ _ (pow_one _).symm rfl,
  root_pow_card_pow_pred_eq_one hP h0 hx, MulChar.map_zero, NeZero.ne]

/-- For T injective, P irreducible of degree d over the finite field k with P(0) ≠ 0, and any
root x of P in the algebraically closed field K: τ_P = (−1)^d times the rank d part of
C_{θ_x}, θ_x taken for Q = |k|^d. -/
lemma greenTau_eq : let d := P.natDegree
  greenTau T P = (-1 : ℂ) ^ d • (greenCuspidal k (thetaChar T (.card k ^ d) x)).rankPart d := by
  rw [greenTau, ← (exists_pow_card_pow_eq_of_root hP hx (@epsilon_spec _ (P.aeval · = 0) ⟨x,
    hx⟩)).choose_spec.2, rankPart_greenCuspidal_pow hP h0 hx]
  delta greenCuspidal brauerLift; congr! 6
  open Fint in erw [← Multiset.map_map, ← aroots_map_frobenius_pow (.id k)] <;> simp [pow_card_pow]

omit hx
seal rankInner finrank

/-- Let T be injective, P monic irreducible, P(0) ≠ 0. On GL_{deg P}(k), ⟨τ_P,τ_S⟩ is 1 if P =
S, else 0, for S monic irreducible with S(0) ≠ 0; if P(1) ≠ 0, `Hall.skew` of τ_P in
degree deg P kills the constant function 1. -/
lemma rankInner_greenTau (hm : P.Monic) : (∀ S, Irreducible S → S.Monic → S.coeff 0 ≠ 0 →
  rankInner P.natDegree (greenTau T P) (greenTau T S) = ite (P = S) 1 0) ∧
  (P.eval 1 ≠ 0 → skew P.natDegree (greenTau T P) constOne = 0) := by
  have := NeZero.of_pos hP.natDegree_pos; let L := Extension k _ P.natDegree
  let := (lift : L →ₐ[k] K).toAlgebra; have r : _ = finrank k L := (finrank_extension ..).symm
  let j χ := algebraMap L K (charName T χ).1
  have R {S : k[X]} (i : Fact (Irreducible S)) (z : S.coeff 0 ≠ 0) h : ∃ χ, S.aeval (j χ) = 0 :=
    ⟨(charName T).symm (.map (algEquivExtension k _ _ _ (finrank_quotient_span_eq_natDegree.trans
    h)).toMonoidHom (.mk0 (root S) (z <| by simpa [·] using eval₂_root S))), by simp [j]⟩
  have ⟨χ, a⟩ := R ⟨hP⟩ h0 rfl
  have o ξ : @finMean Lˣ (fun z ↦ conj (χ z) * ξ z) = ite (j χ = j ξ) 1 0 := by
    open Fint in simpa [finMean, field, ← χ.star_apply', ← @inv_mul_eq_one _ _ χ, j, Units.val_inj,
      MulChar.ext_iff, MonoidHom.ext_iff] using sum_hom_units ((χ⁻¹ * ξ).comp (Units.coeHom L))
  have p B := rankInner_greenCuspidal_mulMu (thetaChar T (.card L) (j χ)) (IsScalarTower.toAlgHom k
    L _) B ▸ rankInner_mul_of_isCuspidal
    (H := constOne) (isCuspidal_greenCuspidal _) finrank_pos.ne'
  rw [greenTau_eq hP h0 a, r, ← natCard_eq_pow_finrank]
  use fun S i m z ↦ byCases (R ⟨i⟩ z · |>.rec fun ξ b ↦ by
    rw [show ite .. = ↑(count (j χ) (S.aroots K)) by simp [eq_comm, i.ne_zero, ↓mem_aroots, *,
      ↓count_eq_of_nodup (nodup_roots (PerfectField.ofFinite.1 i).map),
      eq_iff_aeval_eq_zero, eq_of_irreducible_of_monic hP a hm], greenTau_eq i z b]
    simpa [fun (u : L) i ↦ charpoly_eq_pow_of_isNilpotent (g := mulLeft k u) (irreducible (x :=
      u) i) (monic i) (aeval_algHom k (Algebra.lmul k L) u ▸ .zero) ▸ aroots_pow_eq_frobenius_orbit
      (irreducible i) (x := algebraMap L K u) (by simp), IsIntegral.of_finite,
      aroots_eq_frobenius_orbit i b, *, mulMu, j, mul_sum, eq_one_of_monic_natDegree_zero,
      ← range_val, finMean_sum, ← mul_pow, ← ξ.pow_apply_coe, count_map,
      mul_mul_mul_comm _ (conj _), ← natCard_eq_pow_finrank, charpoly_monic] using! p (brauerLift k
      (thetaChar T (.card L) (j ξ)))) (by aesop), fun h ↦ by simpa [by simpa using (o 1).trans (by
       aesop (add simp aeval_def)), mulMu.eq_unfold, mu_mul_constOne, skew, j,
    finrank_pos.ne'] using (p constOne).symm
end
