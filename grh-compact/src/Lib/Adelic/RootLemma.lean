import Lib.DiscreteSeries.ZerosCostDegree

section
/-! Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Frobenius-twisted circle of letters: action, depth, excess, weight conditions, basic
properties. -/

noncomputable section


open Fintype Finset MvPolynomial Matrix IsLocalRing Ideal
variable (k N) (W R R' : Type) [CommRing W] [IsLocalRing W] [CommRing R] [CommRing R']
  (φ : R →+* R')
attribute [local simp ←] prod_pow_eq_pow_sum add_assoc coeff_map Quotient.eq_zero_iff_dvd
attribute [local simp] polyOfCoeffs exponentOf Finsupp.weight_eq_sum prod_prod_type_right
  Fintype.prod_ite_zero prod_univ_sum sum_prod_type_right diagonal_apply linSubst_mul map_bind₁
  AlgHom.ext_iff smul_eq_C_mul

/-- For natural r, the labelling of indices b in {0,…,k−1} equal to 0 if b < r and 1 otherwise. -/
def twoBlock r (b : Fin k) := ite (b.1 < r) 0 1

/-- Twisting data: p prime, P = p^o₀ ≥ 5, W with P^N residues, alternately even and odd ring maps
ι_s: W → R (s in ℤ/N, the letters), ι_{s+1} ≡ ι_s^P mod p, and w² = p in R. -/
structure TwistingData where
  (p o₀ : ℕ) ι : ZMod N → W →+* R
  isEven : ZMod N → _
  w : R
  prime : p.Prime
  five_le_P : 5 ≤ p ^ o₀
  w_sq : w ^ 2 = p
  frobenius_congr s x : ↑p ∣ ι (s + 1) x - ι s x ^ p ^ o₀
  isEven_succ s : isEven (s + 1) = !isEven s
  card_residueField : .card (ResidueField W) = (p ^ o₀) ^ N

namespace TwistingData

variable {k N W R R'} [NeZero N] (T : TwistingData N W R) (n r : ℕ) (i) (a a' :
  Fin k) {τ} (g : GL (Fin k) W) (s : ZMod N) (x : Fin k × _)

/-- The prime power P = p^o₀ of the twisting data. -/
abbrev P := T.p ^ T.o₀

/-- The number q = P^N = p^{o₀N} of elements of the residue field of W. -/
abbrev q := T.P ^ N

/-- For twisting data over R and a ring map φ: R→R', the twisting data over R' obtained by
composing each ι_s with φ and replacing w by φ(w). -/
def map := {T with
  ι := φ.comp ∘ T.ι, w := φ T.w, w_sq := by simp [← map_pow, w_sq]
  frobenius_congr := by simpa using (map_dvd φ <| T.frobenius_congr · ·)}

/-- The homomorphism sending g in GL_k(W) to the matrix g_s over R: ι_s(g) if the letter s is
even, ι_s of the inverse transpose if s is odd. -/
@[simps -isSimp] def letterMatrix := MonoidHom.mk ⟨fun g : GL (Fin k) W ↦
  (ite (T.isEven s) ↑g g⁻¹.1ᵀ).map (T.ι s), by simp⟩ (by bound)

/-- The action of GL_k(W) on polynomials in the variables x_{bs}: g sends x_{bs} to ∑_c
(g_s)_{cb} x_{cs}, with g_s = `TwistingData.letterMatrix` s g. -/
def polyAction := MonoidHom.mk ⟨fun g ↦ linSubst (blockDiagonal (T.letterMatrix (k := k) · g)),
  by simp [← Pi.one_def]⟩ (by simp)

/-- The matrix ρ(g) of g in GL_k(W) on forms of degree n in each letter: the Kronecker product
over s of the n-th symmetric powers of `TwistingData.letterMatrix` s g. -/
@[simps -isSimp] def letterRep := MonoidHom.mk ⟨fun g ↦
  kroneckerPi (symPowMatrix n <| T.letterMatrix (k := k) · g), by simp⟩ (by simp [kroneckerPi_mul])

/-- The indicator of the deep variables (b,s), b counted from 0: 1 if s is even and b ≥ r, or s
is odd and b < r; else 0. -/
def deepIndicator := if T.isEven x.2 ↔ r ≤ x.1 then 1 else 0

/-- The depth of a family β of degree-n exponents: the total degree of the monomial x^β in the
variables that are deep for r (`TwistingData.deepIndicator`). -/
def depth k n r β := (exponentOf (a := n) β).weight (T.deepIndicator (k := k) r)

/-- For indices a,a' and letter s, the variable index (a',s) if s is even and (a,s) if s is odd. -/
@[simps] def rootVar := (ite (T.isEven s) a' a, s)

/-- The weight on variables defining the excess at letter i: ±P^{(s−i) mod N}/q at u_s =
`TwistingData.rootVar` a a' s, ū_s = `TwistingData.rootVar` a' a s, plus 1−1/q at u_i. -/
def excessWeight := (ite (x = T.rootVar a a' x.2) (T.P ^ (1 + (x.2 - 1 - i).val)) 0 -
  ite (x = T.rootVar a' a x.2) (T.P ^ (x.2 - i).val) 0 : ℝ) / T.q

/-- The submodule of vectors F with (ρ(g)F)_β in the ideal I for all β in B and all g in the
Levi subgroup of τ, ρ acting in degree n. -/
def translatesIn τ (I : Ideal R) (B : Set _) := (⟨⟨⟨{F | ∀ g ∈ @levi k W _ τ, ∀ β ∈ B,
  (T.letterRep n g *ᵥ F) β ∈ I}, by aesop⟩, by simp⟩, by simp_all [mul_mem_left]⟩ : Submodule R _)

/-- Columns F such that (ρ(g)F)_β lies in I whenever g is block diagonal with blocks a', k−a'
and β has excess (`TwistingData.excessWeight`) above h at some letter. -/
abbrev excessCond I h :=
  T.translatesIn n (twoBlock k a') I {β | ∃ i, h < (exponentOf β).weight (T.excessWeight i a a')}

/-- The space V_d of forms F of degree n in each letter such that, for all g in GL_k(W), ρ(g)F
has only monomials of depth at least d. -/
abbrev deepForms k n r d := T.translatesIn n 0 ⊥ {β | T.depth k n r β < d}

attribute [local simp] symPowMatrix linSubst polyAction kroneckerPi letterRep pow_mul' excessWeight
  depth blockDiagonal mulVec_eq_sum
attribute [local grind!] TwistingData le_self_pow NeZero

omit [NeZero N] in
lemma one_lt_P : (1 : ℝ) < T.P := mod_cast by lia

lemma one_lt_q : (1 : ℝ) < T.q := mod_cast by grind

omit [NeZero N] in
lemma frobenius_pow_congr x : ↑T.p ∣ T.ι (s + n) x - T.ι s x ^ T.P ^ n := have := T.frobenius_congr
             by induction n <;> simp_all [pow_succ']

variable {n r i a a' g x}

omit [NeZero N] in
lemma w_ne_zero [CharZero R] : T.w ≠ 0 := by grind [Nat.cast_inj, T.prime.pos]

omit [NeZero N] in
include T in lemma finite_residueField : Finite (ResidueField W) := by grind [Nat.card_pos_iff]

lemma p_dvd_letterMatrix_of_mem_parahoric (hg : g ∈ parahoric W τ) i j (h : ite (T.isEven s)
  (τ i < τ j) (τ j < τ i)) : ↑T.p ∣ T.letterMatrix s g i j := ((isUnit_one_sub_self_of_mem_nonunits
  _ (pow_mem_of_mem _ ((residue_eq_zero_iff (ite (T.isEven s) _ g⁻¹.1ᵀ i j)).1 (by
  split_ifs at * <;> apply_rules [inv_mem hg])) (T.q - 1) (by grind))).map (T.ι s)).dvd_mul_right.1
  (by simpa [letterMatrix, mul_sub, mul_pow_sub_one, T.prime.ne_zero] using
  T.frobenius_pow_congr N ..)

/-- An element g of GL_k(W) sends the variable x = x_{cs} to ∑_b (g_s)_{bc} x_{bs}, where g_s =
`TwistingData.letterMatrix` s g. -/
lemma polyAction_X : T.polyAction g (X x) = ∑ b,
  C (T.letterMatrix x.2 g b x.1) * X (b, x.2) := by simp

lemma diagonal_pow_depth (x : R) : diagonal (x ^ T.depth k n r ·) = kroneckerPi fun s ↦
  symPowMatrix n (diagonal (n := Fin k) (x ^ T.deepIndicator r ⟨·, s⟩)) := by ext; simp [apply_ite,
  -aeval_eq_bind₁, aeval_monomial, C_mul_X_eq_monomial, monomial_pow, ← monomial_sum_prod]; grind

/-- For a coefficient vector F, g sends ∑_β F(β) x^β to ∑_β (ρ(g)F)(β) x^β: the matrix ρ(g) =
`TwistingData.letterRep` n g represents the action on forms of degree n in each letter. -/
lemma polyAction_polyOfCoeffs F : T.polyAction g (polyOfCoeffs F) =
  polyOfCoeffs (T.letterRep n g *ᵥ F) := by
  simpa [monomial_eq, coeff_map, -univ_eq_attach] using congr(∑ α, F α • ∏ s, rename (·, s)
    $(sum_monomials_eq_of_isHomogeneous ((α s).isHomogeneous_linSubst (T.letterMatrix s g)))).symm

lemma letterRep_map : (T.map φ).letterRep n g = (T.letterRep n g).map φ := by aesop

@[simp] lemma one_add_val_sub_one_sub : 1 + (s - 1 - i).val = ite (s = i) N (s - i).val := by
  zify; simp [sub_right_comm, ZMod.cast_sub_one]

lemma five_mul_P_pow_le_q : 5 * T.P ^ s.val ≤
  T.q := by grw [T.five_le_P, ← pow_succ', q]; gcongr <;> grind

lemma excessWeight_mem_Icc : T.excessWeight i a a' x ∈ Set.Icc (-5⁻¹) 1 :=
  (unitInterval.div_mem (by simp) (by simp)
  (Nat.mono_cast (T.five_mul_P_pow_le_q (x.2 - i)))).elim (by simp [sub_div, ite_div]; grind)
end TwistingData
end
end

section
/-! Part of: Dimension bounds mod p from flags and a cone volume (see New.TwistedHecke.Counting).

This file: A form deep in every frame has a monomial of large cost. -/

open Finset Finsupp Fintype Ideal MatMul Matrix MvPolynomial

variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T : TwistingData N W K)

/-- For every r and every index b, the variable (b,s) is deep for exactly half of the letters s
in ℤ/N: the sum over s of `TwistingData.deepIndicator` at (b,s) is N/2. -/
lemma TwistingData.sum_deepIndicator r (b : Fin k) : ∑ s, T.deepIndicator r (b, s) = N / 2 :=
  Nat.eq_div_of_mul_eq_right
  nofun (by nth_rw 1 [two_mul, ← sum_translate (-1), ← sum_add_distrib, sum_const_nat,
  mul_one] <;> simp; grind [deepIndicator, isEven_succ])

/-- Let char K = p, 2r ≤ k, 2r < N. A non-zero F in `TwistingData.deepForms` has a monomial of
weight ≥ τ, deep variables (b,s) weighing P^{−2r} if b ≥ 2r (b from 0), 1/P otherwise, the others
0. -/
lemma TwistingData.exists_le_weight_of_mem_deepForms [CharP K T.p] {n r τ F} (hk : 2 * r ≤
  k) (hN : 2 * r < N) (hF : F ∈ T.deepForms k n r τ) (F0 : F ≠ 0) : ∃ β, F β ≠ 0 ∧ τ ≤
  (exponentOf β).weight fun x ↦ (T.deepIndicator r x / T.P ^ ite (2 * r ≤ x.1) (2 * r) 1 : ℝ) := by
  choose J hJ using fun i b ↦ show ∃ j : ℕ, j / 2 = b ∧ T.isEven (i - j) by by_contra! h; grind
    [T.isEven_succ (i - 2 * b - 1), sub_add_cancel, sub_sub, h (2 * b), h (2 * b + 1)]
  obtain ⟨p, _, _, m, e⟩ := T.prime.pos, @ofFinite _ T.finite_residueField, Fact.mk T.prime, hk.dest
  -- `x` maps to the field of rational functions; the variable `v` costs `1 / κ v` there.
  let R := MvPolynomial (Fin k × ZMod N) K
  let x := algebraMap R (FractionRing R)
  let κ v := T.P ^ (T.deepIndicator (k := k) r v * ite (2 * r ≤ v.1) (2 * r) 1)
  -- Points: the entries of `A` sit at the places `(ρ t, σ t)`, and `z y` is the point of `A = y`.
  let I := Fin r ×ₗ Fin (m + 1)
  let ρ (t : I) : Fin k := ⟨t.1, by lia⟩
  let σ (t : I) : Fin k := ⟨ite (t.2 = 0) (t.1 + r) (k - t.2), by lia⟩
  let c v t : R := ite (T.rootVar (ρ t) (σ t) v.2 =
    v) (X (T.rootVar (σ t) (ρ t) v.2)) 0 * ite (T.isEven v.2) 1 (-1)
  let a i (y : I → IsLocalRing.ResidueField W) t := x (C (T.ι i (y t).out))
  let z y v := a v.2 y ⬝ᵥ x ∘ c v
  have hz v (j : ℕ) y : x ∘ c v ^ T.P ^ j ⬝ᵥ a (v.2 + j) y = z y v ^ T.P ^ j := by
    erw [dotProduct_comm, ← pow_mul, sum_pow_char_pow]; simp [a, dotProduct, pow_mul, mul_pow,
      by simpa [CharP.cast_eq_zero] using T.frobenius_pow_congr j v.2]
  -- Equations: each linear form in `A` is the value of a polynomial with terms of cost below `1`.
  have entry i u : ∃ g, (∀ α ∈ g.support, weight (κ · : _ → ℝ)⁻¹ α < 1) ∧
      ∀ y, eval (z y) g = u ⬝ᵥ a i y := by
    let j (t : I) := ite (t.2 = 0) 0 (J i t.1)
    let v t := T.rootVar (ρ t) (σ t) (i - j t)
    -- the system is invertible, as a specialisation makes it triangular
    obtain ⟨w, rfl⟩ := (x.mapMatrix (of fun t ↦ c (v t) ^ T.P ^ j t)).vecMul_surjective_iff_isUnit.2
      (by clear * - p hJ hN
          simp [↓isUnit_iff_isUnit_det, ↓← x.map_det, x, R]
          apply ne_of_apply_ne (eval fun v ↦ 0 ^ ((i - v.2).val / 2 - v.1))
          rw [RingHom.map_det, det_of_isUpperTriangular fun _ _ ↦ ?_ ∘ Prod.lex_def.1] <;> simp [c,
            v, rootVar, univ.prod_eq_zero_iff, apply_ite (eval _),
            @Nat.mod_eq_of_lt (j _) N (by grind)] <;> grind [pow_eq_zero_iff']) u
    use ∑ t, w t • X (v t) ^ T.P ^ j t, fun α h ↦ ?_, fun y ↦ by
      simpa [← hz, v, Matrix.map] using! dotProduct_mulVec ..
    obtain ⟨t, rfl, -⟩ := by simpa [coeff_X_pow] using support_sum h
    simp [weight_single, field, κ, -mul_ite]; clear * - hJ; gcongr <;> grind [rootVar,
      deepIndicator, one_lt_P]
  -- Read the forms over that field, as polynomials in the deep variables.
  let ι := eval₂Hom (C.comp (x.comp C)) fun v ↦ ite (T.deepIndicator r v = 0) (C (x (X v))) (X v)
  have ⟨α, h, H⟩ := exists_le_cost_of_vanishing κ (by bound) z (fun y y' h ↦ funext fun t ↦
    (entry 0 (Pi.single t 1)).elim fun _ hf ↦ (y t).out_eq ▸ (y' t).out_eq ▸ Ideal.Quotient.eq.2
    (mt (·.map (T.ι 0)) (by simpa [← h, hf, a, x, R] using hf.2 y'))) ?_ (fun _ ↦ by simp only [κ,
    ← hz, entry]) τ (ι (polyOfCoeffs F)) (fun h ↦
    F0 (by ext β; simpa [polyOfCoeffs, coeff_sum] using congrArg (·.coeff (exponentOf β)) (by
           simpa [h, x] using congr(($(show x = .comp (eval (x ∘ X)) ι by
           ext <;> simp [ι, apply_ite])) (polyOfCoeffs F)) : polyOfCoeffs F = 0))) fun y ↦ ?_
  -- A costly monomial of `ι F` comes from a costly monomial of `F`.
  simp [polyOfCoeffs, coeff_sum, ι, prod_fintype, prod_ite, ← map_pow, ← map_prod,
    coeff_prod_X_pow] at h
  obtain ⟨β, rfl, h, -⟩ := by simpa [x] using exists_ne_zero_of_sum_ne_zero h
  use β, h, H.trans (by simp [weight_eq_sum, κ, deepIndicator]; bound)
  -- The number of points.
  subst e
  grw [card_fun, card_eq_nat_card, T.card_residueField, ← pow_mul, ← N.div_mul_le_self 2,
    prod_pow_eq_pow_sum, pow_le_pow_right₀] <;> simp [I, ↓sum_prod_type, ← univ.sum_mul,
    sum_deepIndicator, Fin.sum_univ_add, ← Nat.not_lt, -not_lt] <;> lia
  -- The order of vanishing: `F` is the translate of `g F` by `g⁻¹ = 1 - A`.
  let A := ∑ t, Matrix.single (ρ t) (σ t) (y t).out
  let g : GL _ W := by use 1 + A, 1 + -A <;> simp (disch := lia) [A, univ.sum_mul_sum]
  rw [show F = T.letterRep n g⁻¹ *ᵥ T.letterRep n g *ᵥ F by simp [← map_mul],
    ← polyAction_polyOfCoeffs]
  simp [polyOfCoeffs, monomial_eq]
  refine sum_mem fun β _ ↦ (le_or_gt ..).elim
    (pow_le_pow_right · (mul_mem_left _ _ ?_)) (hF g nofun β · ▸ by simp)
  simp [depth, weight_eq_sum, ← prod_pow_eq_pow_sum, pow_mul']
  refine prod_mem_prod fun v _ ↦ pow_mem_pow ?_ _
  by_cases T.isEven v.2 <;> by_cases r ≤ v.1 <;> simp [polyAction_X, letterMatrix_apply, g, A, c,
    rootVar, ι, z, a, add_mul, univ.sum_mul, Matrix.sum_apply, Matrix.single, ite_and,
    @Finset.sum_comm I, deepIndicator, *, dotProduct,
    apply_ite (DFunLike.coe _), -coe_eval₂Hom, show ∀ t, ¬r ≤ ρ t ∧ r ≤ σ t by lia, Prod.ext_iff]
end

section
/-! General lemmas of commutative and general algebra (textbook or folklore).

Part of: An approximate projector from averages over generic matrices (see
New.TwistedHecke.ElementaryDivisors).

This file: Integral conjugation-invariant means on generic Levi matrices splitting evaluation at 1
by weight. -/

open IsLocalRing Module Nat Finset Finsupp LinearMap Matrix MvPolynomial Submodule

attribute [-simp] coe_units_inv mulVec_single

attribute [local simp] Finset.mul_sum Fintype.sum_prod_type LinearMap.ext_iff restrict_apply mulVec
  Matrix.mul_apply Matrix.trace coeff_sum eval_monomial map_eval RingHom.map_det _root_.funext_iff

variable {k D : ℕ} {W O σ : Type} [CommRing W] [IsLocalRing W] [CommRing O] (τ : Fin k → ℕ)
  (ι : W →+* O) [Fintype σ]

/-- For ι: W → O and a in GL_k(W), the O-algebra endomorphism of polynomials in the entries of a
generic k×k matrix x given by substituting ι(a⁻¹) x ι(a) for x. -/
noncomputable def ClassMean.conjSubst (a : GL (Fin k) W) :=
  linSubst (a⁻¹.1ᵀ.kroneckerMap (ι · * ι ·) a.1)

lemma ClassMean.map_C_mul_mul_C {ν} (A B : Matrix σ σ O) (X : Matrix σ σ (MvPolynomial ν O))
    (l : Dual O _) : (A.map C * X * B.map C).map l = A * X.map l * B := ext
    (by simp [mul_comm (∑ _, _), C_mul', mul_left_comm])

attribute [local simp ←] ClassMean.map_C_mul_mul_C Matrix.map_map Matrix.map_mul monomial_sum_prod
  cast_prod cast_sum kroneckerPi_map kroneckerPi_mul mul_assoc

/-- Zariski density: if n + e ≤ #(residue field of W) (0 if infinite) and a form d of degree e
takes a unit value, the vectors (ι(b^γ)) over monomials γ of degree n, for b with d(b) a
unit, span everything over O. -/
lemma ClassMean.eq_top_of_eval_monomial n {e d} (hd : d.IsHomogeneous e) (hW : n + e ≤ .card
    (ResidueField W)) {b} (hb : IsUnit (eval b d)) {p : Submodule O (Monomials σ n → O)}
    (hp : ∀ b, IsUnit (eval b d) → (ι <| eval b <| monomial ·.1 1) ∈ p) : p = ⊤ := by
  let q := p.comap (σ₁₂ := ι) ⟨⟨(ι ∘ ·), by simp⟩, by simp⟩
  simpa [q, Pi.single, Function.comp_update, eq_top_iff_forall_basis_mem (Pi.basisFun ..)] using
    subsingleton_tensorProduct.1
    ((subsingleton_dual_iff _).1 ((liftBaseChangeEquiv _).subsingleton_congr.1
    (subsingleton_of_forall_eq 0 fun e ↦ (by ext γ; simpa using congrArg (·.coeff γ) ·)
    ((mul_eq_zero_iff_right (by simpa [·] using hb.map (residue W))).1 (((IsHomogeneous.sum univ _ _
    fun γ _ ↦ isHomogeneous_monomial (e (q.mkQ (Pi.single γ 1))) γ.degree_eq).mul (hd.map
    (residue W))).eq_zero_of_forall_eval_eq_zero_of_le_card (by
    simpa [residue_surjective.comp_left.forall, mul_comm (e _),
      Algebra.smul_def _ (e _), or_iff_not_imp_right, ← residue_ne_zero_iff_isUnit] using
      fun b h ↦ congr(e $(q.ker_mkQ.ge ((pi_eq_sum_univ' _).subst (hp b h)))))
    ((Cardinal.natCast_toNat_le _).trans' (mod_cast hW)))))))

variable (σ) [IsDomain O] [CharZero O] [ValuationRing O]

/-- Let k be a prime, non-unit in a valuation domain O of characteristic zero. There are q_γ in O
with multinomial(γ)·q_γ = k^{|σ|f} when deg γ < k^f, and coeff_α(A·x^β)q_α = q_β·coeff_β(Aᵀ·x^α) for
all square matrices A acting by `linSubst`. -/
lemma ClassMean.exists_invariant_diagonal_form (pp : k.Prime) (hp : ¬IsUnit (k : O)) f : ∃ q :
    _ → O, (∀ γ : σ →₀ ℕ, γ.degree < k ^ f → k ^ (Fintype.card σ * f) = γ.multinomial * q γ) ∧ ∀ A α
    β, (linSubst A (monomial β 1)).coeff α * q α = q β * (linSubst Aᵀ (monomial α 1)).coeff β := by
  have M s α (h : s.sum α < k ^ f) : (@multinomial σ s α : O) ∣ k ^ (#s * f) := by
    induction s using cons_induction <;> simp_all [multinomial_insert, pow_mul', _root_.pow_succ']
    gcongr
    grw [← (Nat.choose ..).ordProj_mul_ordCompl_eq_self, cast_mul, cast_pow, (notMem_maximalIdeal.1
      (Ideal.IsPrime.notMem_of_isCoprime_of_mem (coprime_ordCompl pp (choose_ne_zero
      le_self_add)).cast hp)).mul_right_dvd, factorization_choose_le_log, h, log_pow pp.one_lt]; lia
  choose q hq using fun γ ↦ iteInduction (M univ γ) fun _ ↦ dvd_zero _
  use (q ·), by grind [multinomial_eq_of_support_subset, degree_eq_sum], fun A α β ↦
    nsmul_right_injective α.degree.factorial_ne_zero
    (by grind [degree_eq_sum, by simpa [fockPairing, jet_eq_sum, prod_fintype, -coe_monomial] using
    (fockPairing_linSubst A (monomial α 1) (monomial β 1)), !congr(($(multinomial_spec ..) : O)),
    (Monomials.isHomogeneous_linSubst _ ⟨α, by aesop⟩).coeff_eq_zero])

/-- Let O be a valuation domain of characteristic 0, the prime p a non-unit, W local, D < p^f,
D + k < #residue field of W. For any property P of x-weights, some Levi-conjugation invariant linear
form κ on polynomials in a generic matrix kills monomials with row weight ≠ column weight, sends
monomials with row weight in P to p^{k²f}·(value at 1) (0 in degree > D), and is a combination of
Levi conjugates of forms killing the monomials with row weight outside P.

An approximate projector from averages over generic matrices. -/
lemma ClassMean.exists_mean {p : ℕ} (pp : p.Prime) (hp : ¬IsUnit (p : O)) f (hD : D < p ^ f)
    (hW : D + k < .card (ResidueField W)) (x : _ → ℝ) (P : ℝ → _) : ∃ κ : Dual O _,
  (∀ a ∈ levi W τ, ∀ g, κ (conjSubst ι a g) = κ g) ∧ (∀ α, weight (x ·.1) α ≠ weight (x ·.2) α
  → κ (monomial α 1) = 0) ∧ (∀ α, P (weight (x ·.1) α) → κ (monomial α 1) = if degree α ≤ D then p ^
  (k ^ 2 * f) • eval (vec 1) (monomial α 1) else 0) ∧ κ ∈ span O {l ∘ₗ (conjSubst ι u).toLinearMap |
  (u ∈ levi W τ) (l : Dual O _) (_ : ∀ α, ¬P (weight (x ·.1) α) → l (monomial α 1) = 0)} := by
  simp_rw [le_iff_lt_add_one]
  refine Fin.val_last (D + 1) ▸ (Fin.last _).induction ⟨0, by simp⟩ fun d ⟨κ, _, _, u, w⟩ ↦ ?_
  let Y := of fun i j ↦ C (@ite W (τ i = τ j) _ 1 0) * X (j, i)
  let g := kroneckerPi fun _ : Fin d ↦ Y.map (·.map ι)
  have H m t α w : (g m t).coeff α ≠ 0 → α.weight w = ∑ l, (w (t l, m l) : ℝ) := by simp +contextual
    [g, Y, kroneckerPi, ↓C_mul_X_eq_monomial, weight, eq_comm]
  let S := (Pi.basisFun O (Monomials _ d)).constr O fun γ ↦ g.map (·.coeff γ.1)
  have E (l : Dual ..) : S (l <| monomial · 1) = g.map l := ext fun m t ↦ by simp [Matrix.sum_apply,
    S, mul_comm,
    ← congr(l $(sum_monomials_eq_of_isHomogeneous (by simpa [weight_eq_sum] using H m t · 1)))]
  have hv b : _ = kroneckerPi fun _ ↦ (Y.map (eval b)).map ι :=
    (E (aeval (ι ∘ b)).toLinearMap).trans (ext (by simp [g, kroneckerPi]))
  have L (a : levi W τ) : Y.map (eval (vec a.1)) = a.1 :=
    ext (by simp_all [Y, apply_ite, ite_apply, a.2 _])
  choose ev he using (mem_range.2 ⟨_, L · ▸ hv _⟩)
  have sp p (hp' : ∀ {c} a, S c = S (ev a) → c ∈ p) := eq_top_of_eval_monomial ι d (Y.det_apply' ▸
    IsHomogeneous.sum _ _ _ fun _ _ ↦ .C_mul
      (.prod _ _ 1 (by solve_by_elim [isHomogeneous_C_mul_X]))
    _) (by simp; lia) (by simpa using L 1 ▸ isUnits_det_units 1) (by simpa using! fun b h ↦ (hp' _
    ((hv b).trans (he ⟨.mk'' _ h, by clear * -; simp_all [Y, levi]⟩).symm)))
  let N := ⨆ t, (toLin'.1.flip (Pi.single t (ite (P (∑ l, x (t l))) 1 0)) ∘ₗ S).range
  obtain ⟨m, _, q, _, hq'⟩ := iSup_le_iff.1 (le_refl N), @free_of_flat_of_isLocalRing O N _ _ _ _ _
    (Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (isTorsionFree_iff_torsion_eq_bot.1 inferInstance)),
    exists_invariant_diagonal_form (Fin k × Fin k) pp hp f
  let K := pi fun γ : Monomials _ d ↦ (lcoeff O γ.1).smulRight (q γ.1)
  have hK α : S (K (monomial α 1)) = _ := congr(S $(by simp [K]; lia)).trans (E (q α • lcoeff O α))
  have adj := by simpa using fun a ↦ (linearMap_ext fun α ↦ ext_ring (by
    erw [congrArg S (funext (hq' _ · α)), E ((q α • lcoeff O α) ∘ₗ (linSubst _).toLinearMap)]
    simp [*, g, -LinearMap.coe_smul]; congr!
    simp [← ext_iff, -prod_mul_distrib, univ.sum_mul, Y, linSubst, ← C_mul', kroneckerPi, -ite_mul]
    congr! 3; grind [a.2 _, inv_mem a.2 _]) :
    S ∘ₗ K ∘ₗ conjSubst ι a.1 = mulLeftRight O (S (ev a), S (ev a⁻¹)) ∘ₗ S ∘ₗ K)
  let ρ : _ →ₗ[O] End O N := ⟨⟨(S · |>.toLin'.restrict (id ((sp ((N.compatibleMaps N).comap
    (toLin'.1 ∘ₗ S)) fun a _ ↦ iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun b _ ↦
    m v ⟨ev (a * b), by simp [*]⟩)).ge ⟨⟩))), by simp⟩, by simp⟩
  let b := finBasis O N
  use κ + trace O N ∘ₗ ρ ∘ₗ K, fun a h f ↦ by simp [*]; convert ((ρ (ev ⟨a, h⟩)).trace_mul_cycle O
    (ρ (K f)) (ρ (ev ⟨a, h⟩⁻¹))) <;> simp [*, ρ], fun α h ↦ by simpa [*, ρ] using
    (LinearMap.isNilpotent_trace_of_isNilpotent (End.isNilpotent.restrict _ (.map ⟨2, (sq _).trans
    (ext fun _ _ ↦ sum_eq_zero (by simp; grind))⟩ toLinAlgEquiv'))).eq_zero, fun α h ↦
    congr($(u α h) + $((trace_comp_comm' _ (codRestrict N _ ((range_toLin' _).trans_le (span_le.2
    (Set.range_subset_iff.2 (m · ⟨K (monomial α 1), by simp [*]; grind⟩))) ⟨·, rfl⟩))).trans
      (.trans (by simp [*, g, Y, kroneckerPi, sum_pow']; congr!) congr(_ *
    $(coeff_linearCombination_X_pow_of_fintype
    (vec 1) α d))))).trans (by simp [sum] at *; grind [degree_apply])
  convert add_mem w (sum_mem (t := univ) fun j ↦ by
    simpa using (iSup_le fun v ↦ range_le_iff_comap.2 (sp _ fun {c} a _ ↦ by
      exists ⟨_, m v ⟨c, rfl⟩⟩, subset_span ⟨_, a⁻¹.2, (b.coord j ∘ₗ ρ c) ∘ₗ codRestrict N _
      (m v ⟨·, rfl⟩) ∘ₗ K, fun α h ↦ ker_le_ker_comp _ _ (by simp [*]; grind), by simp [ρ, *]⟩) :
      N ≤ (comap ((ρ ∘ₗ K).flip.compr₂ (b.coord j)) _).map N.subtype) (b j).2)
  simp [trace_eq_matrix_trace O b, toMatrix_apply]
end

section
/-! A term least in all frames obeys Frobenius inequalities. When a Levi group acts on polynomials
in a circle of variable sets by Frobenius twists and inverse transposes in turn, a term least for
valuation plus a suitable weight among all translates has exponents obeying linear inequalities
(Stepanov's count of zeros against degree), which are used to bound the Hecke operator's divisors.
Twisted Dickson forms on Frobenius twists of symmetric powers, weight inequalities via the Lang map
and counts of zeros against degree are known. Related work: Ghate–Jana, Modular representations of
GL2(F_q) using calculus, 2025; Imai–Koskivirta, Automorphic vector bundles on the stack of G-zips,
2021; Bombieri, Counting points on curves over finite fields, Sém. Bourbaki 430, 1973.

General lemmas of commutative and general algebra (textbook or folklore).

This file: Root lemma: a term least in all frames obeys Frobenius inequalities; Gauss
filtrations. -/

attribute [-instance] IsAddTorsionFree.of_isDomain_charZero instCharZeroOfIsSemireal


variable {σ R A N k W} [CommRing R] [CommRing A] [Algebra R A] (F : ℝ → AddSubgroup R) (c : σ → ℝ)
  (w : R) (t : ℝ) (χ : MvPolynomial σ R →ₐ[R] A) [NeZero N] [CommRing W] [IsLocalRing W]
  (T : TwistingData N W R)

open Polynomial IsLocalRing Function in
/-- Stepanov's count. Let W be local with q residue classes and ι: W → R a ring map. If a
non-zero polynomial Φ over R is divisible by (X − ι(x))^E for every x in W, then Eq ≤ deg Φ. -/
lemma stepanov_count (ι : W →+* R) {Φ} E (h0 : Φ ≠ 0) (h : ∀ x, X ^ E ∣ taylor (ι x) Φ) :
    E * .card (ResidueField W) ≤ Φ.natDegree := by
  cases fintypeOrInfinite (ResidueField W) <;> simp [Nat.card]
  simpa [Nontrivial.of_polynomial_ne h0, Monic.natDegree_pow, monic_prod_X_sub_C, Finset.prod_pow,
    Monic.pow] using (Monic.not_dvd_of_natDegree_lt · h0 · (Fintype.prod_dvd_of_coprime
    (fun x y h ↦ .pow (isCoprime_X_sub_C_of_isUnit_sub (map_sub ι .. ▸ .map ι (by simpa
    [← residue_ne_zero_iff_isUnit, surjInv_eq]))))
    (X_sub_C_pow_dvd_iff.2 <| h <| surjInv residue_surjective ·)))

/-- A decreasing multiplicative filtration of a commutative ring by additive subgroups F_t, t
real: 1 ∈ F_0, F_s·F_t ⊆ F_{s+t}, and F_t ⊆ F_s for s ≤ t. -/
class IsRealFiltration extends SetLike.GradedMonoid F where antitone : Antitone F

open MvPolynomial Matrix Finsupp SetLike Nat Ideal.Quotient IsRealFiltration AddSubgroup

/-- For a ring element w and real t, the additive subgroup of elements divisible by w to the
power max(⌈t⌉,0). -/
@[simp] def adicFiltration := mk ⟨⟨{x | w ^ ⌈t⌉₊ ∣ x}, .add⟩, by simp⟩ .neg_right

instance : IsRealFiltration (adicFiltration w) where
  one_mem := by simp
  mul_mem _ _ _ _ a b := by simp_all; grw [ceil_add_le, pow_add, a, b]
  antitone _ _ _ _ := .trans (by gcongr)

/-- The Gauss filtration: for subgroups F_t of R and variable weights c, the additive group of
polynomials whose coefficient at each x^α lies in F_{t − c·α}. -/
def gaussFiltration := mk ⟨⟨{f : MvPolynomial σ R | ∀ α, f.coeff α ∈ F (t - weight c α)},
  by aesop⟩, by simp⟩ (by simp)

variable {c t F w} {a a' : Fin k}

lemma mem_adicFiltration_of_nonpos {x} (h : x ≠ 0 → t ≤ 0) : x ∈ adicFiltration w t := by
  by_cases x = 0 <;> simp_all [ceil_eq_zero.2]

lemma monomial_mem_gaussFiltration {α x} : x ∈ F (t - weight c α) →
  monomial α x ∈ gaussFiltration F c t := fun _ _ ↦ by aesop

instance [IsRealFiltration F] : IsRealFiltration (gaussFiltration F c) where
  one_mem := monomial_mem_gaussFiltration (by simp [one_mem_graded])
  mul_mem _ _ f _ h h' _ := f.coeff_mul .. ▸ sum_mem fun (a, b) ↦ by
    simp; grind [mul_mem_graded (h a) (h' b)]
  antitone _ _ _ _ := (antitone (by grind) <| · ·)

lemma aeval_sub_mem_of_gaussFiltration G [IsRealFiltration G] {f} (h :
  f ∈ gaussFiltration F c t) (u : ∀ i, χ (X i) ∈ G (c i)) (ψ := χ) (v :
  ∀ i, ψ (X i) - χ (X i) ∈ G (c i + 20⁻¹) := by simp) (y : ∀ {t x}, x ∈ F t → algebraMap R A x ∈ G
  t := by intros; (repeat apply monomial_mem_gaussFiltration); simpa) : ψ f ∈ G t ∧
  ψ f - χ f ∈ G (t + 20⁻¹) := by
  induction' f using induction_on'' with _ α x f e _ _ _ p i I generalizing t
  simpa using y (h 0)
  simp_all [add_sub_add_comm, add_mem_cancel_left,
    monomial_mem_gaussFiltration (by simpa [f.notMem_support_iff.1 e] using h α)]
  have ⟨a, b⟩ := @I (t - c i) (by grind [weight_single, coeff_mul_X, h <| · + single i 1])
  grind [mul_mem_graded a (add_mem (u i) (antitone (by simp) (v i))),
    add_mem (mul_mem_graded b (u i)) (antitone (by grind) (mul_mem_graded a (v i)))]

/-- Root lemma. Let a ≠ a', τ(a) = τ(a'), and c(u_s) − c(ū_s) ∈ [2/5, 8/5] for all s, with u_s, ū_s
as in `TwistingData.excessWeight`. If all terms of all τ-Levi translates of f have w-order plus
c-weight ≥ l + c·α and w^{l+1} ∤ f_α, then α has excess ≤ 0 at letter i.

A term least in all frames obeys Frobenius inequalities. -/
lemma TwistingData.root_lemma i (ha : a ≠ a') τ c {f α} (l : ℕ) (h : ∀ g ∈ levi W τ,
  T.polyAction g⁻¹ f ∈ gaussFiltration (adicFiltration T.w)
  c (l + weight c α)) (h0 : ¬T.w ^ (l + 1) ∣ f.coeff α) (hτ : τ a = τ a') (hc : ∀ s, c (T.rootVar a
  a' s) - c (T.rootVar a' a s) ∈ Set.Icc 0.4 1.6) : weight (T.excessWeight i a a') α ≤ 0 := by
  set y := T.rootVar a _; set x := T.rootVar _ a; let π z := ite (z = y i) (x i) z
  have hm β : mapDomain π β + single (y i) (β (y i) : ℕ) = β + single (x i) (β (y i)) := by
    induction β using induction_linear <;> simp [mapDomain_add] <;> grind
  let g r := .swap W a a' * transvectionGL ha (ite (T.isEven i) (-r) r)
  let σ z := Equiv.swap (x z.2) (y z.2) z
  obtain ⟨_, f1, _, hs, ω, _⟩ := T.one_lt_q, h 1, hc i, T.five_mul_P_pow_le_q,
    mul_left_surjective₀ (one_pos.trans T.one_lt_q).ne' (c (y i) - c (x i))
  simp at *; have : 0 < ω := by nlinarith
  have _ s t : y s ≠ x t ∧ x s ≠ y t := by grind [rootVar]
  let ε z := ite (z = y z.2) (ite (T.isEven z.2 = T.isEven i) (-1) 1) 0
  have cs z : ∃ s, (s = i ∨ s ≠ i ∧ y s ≠ y i ∧ 5 ≤ T.P ^ (s - i).val) ∧ (z = y s ∨ z = x s ∨
    ∀ t, z ≠ y t ∧ z ≠ x t) := by grind [TwistingData, le_pow, ZMod.val_pos, rootVar]
  rify at cs hs
  let m z := ite (z = x z.2) (T.P ^ (z.2 - i).val) 0 * T.q
  let e z := ite (z = y z.2) (T.P ^ (1 + (z.2 - 1 - i).val)) 0
  let χ z := monomial (single (π z) 1) (monomial (single () (m z)) (1 : R))
  let η z := monomial (single (σ z) 1)
    (monomial (single () (e (σ z))) (ite (z.2 = i) 0 (ε z + ε (σ z)) : R))
  let d u (v : _ → ℕ) z := c z - v z * u
  let G u v := gaussFiltration (gaussFiltration (adicFiltration T.w) fun () ↦ u) (d u v)
  have ag r z : T.polyAction (g r) (X z) = X (σ z) + C (ε z * T.ι z.2 r) * X z := by
    simp +zetaDelta [polyAction_X, letterMatrix_apply, transvectionGL, swap,
      GeneralLinearGroup.swap, Equiv.swap_apply_eq_iff]
    split <;> simp [transvection, Matrix.single, add_mul, ite_and,
      apply_ite (DFunLike.coe _)] <;> grind [rootVar]
  have ⟨A, D⟩ :=
    aeval_sub_mem_of_gaussFiltration (aeval χ) (G (-ω) m) f1 ?_ (aeval (χ - η)) ?_ <;> intros
  have l2 z r (m : ℕ) : monomial (single z 1) (C (T.ι (i + m) r) + X () ^ T.P ^ m - (X () + C (T.ι i
      r)) ^ T.P ^ m) ∈ G ω e (d ω e z + 2) := monomial_mem_gaussFiltration
    (.trans (pow_dvd_pow _ (by simp [↓weight_single, weight_eq_sum, *])) <|
    (C_dvd_iff_dvd_coeff (_ ^ 2) _).1 (by simpa [w_sq, prime, ← pow_mul, add_pow_prime_pow_eq',
    ← sub_sub, dvd_sub_left] using (map_dvd C (T.frobenius_pow_congr ..))) ·)
  let u := uniqueAlgEquiv R Unit
  have S {r} := aeval_sub_mem_of_gaussFiltration ((mapAlgHom ((u.arrowCongr u).symm
    (Polynomial.taylorAlgHom (T.ι i r)))).comp (.comp (aeval (χ - η)) (T.polyAction (g r)))) _
    (h (g r) (by apply mul_mem <;> simp [levi, swap, transvection] <;> grind)) fun z ↦
    Eq.subst ?_ (sub_mem (?_ : (χ - η) (σ z) ∈ _) (sub_mem (antitone ?_ (l2 (σ z) (|ε z| * r)
    (N + (z.2 - i).val))) (zsmul_mem (antitone ?_ (l2 z r (z.2 - i).val)) (ε z))))
  any_goals simp [*]
  any_goals apply_rules only [sub_mem, monomial_mem_gaussFiltration, mem_adicFiltration_of_nonpos]
  any_goals obtain ⟨s, _ | _, rfl | rfl | _⟩ := cs ‹_› <;> simp +zetaDelta [*, ↓weight_single,
    monomial_eq, Equiv.swap_apply_def] <;> (try split <;> simp) <;> intros <;>
    first | ring1 | nlinarith [hc s, hs (s - i)]
  have V {t v s g} (j : ℕ) (h : g ∈ G t v s) (K : ∀ z, d t v (π z) = d t v z := by simp +zetaDelta
    [↓apply_ite (d _ _), *]) (hj : l < s - (weight c α - weight v α * t) - j * t := by
    rify at *; nlinarith) := ((u _).coeff_map _ j).trans ((eq_zero_iff_dvd ..).2 (trans
    ((pow_dvd_pow _ (by simpa [lt_ceil, weight_apply, ↓sum_mapDomain_index, add_smul, ↓K, d,
    mul_sub, sum_mul, mul_assoc] using hj : l < _)).trans (h (mapDomain π α) _))
    (coeff_uniqueAlgEquiv ..).symm))
  have : _ ≤ weight m α := (stepanov_count (.comp ..) (weight e α) (fun H ↦ h0 ?_) fun r ↦
    Polynomial.X_pow_dvd_iff.2 fun _ _ ↦ by simpa [← AlgHom.mul_apply, ← map_mul, -map_aeval,
    coeff_map] using (V _ S.1)).trans (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun _ _ ↦ V _ A)
  simpa +zetaDelta [weight_eq_sum, excessWeight, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul,
    mul_sub, field, T.card_residueField, ← @cast_le ℝ, -ite_mul]
  convert by simpa [H, eq_zero_iff_dvd] using V (weight m α) D
  exact f.induction_on' (fun β r ↦ by
    simp [χ, aeval_monomial, monomial_pow, u, Finsupp.prod, ← monomial_sum_prod, ← single_finsetSum,
      ↓coeff_uniqueAlgEquiv, apply_ite AddMonoidAlgebra.coeff,
      DFunLike.ite_apply, ← ite_and, -single_mul]; congr!
    use by bound, fun _ : mapDomain .. = _ ∧ weight m β = _ ↦ by
      simpa +zetaDelta [*, by
        simpa +zetaDelta [*, add_comm, weight_single, T.prime.ne_zero,
        -ite_mul] using congr(($(hm α) + $((hm β).symm)).weight m)] using (hm β).symm) (by simp_all)
end
