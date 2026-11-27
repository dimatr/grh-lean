import Lib.GaloisRep.HeckeOnLineStabiliser
import Lib.GaloisRep.LocalTranslates
import New.Weil.RallisFormula

-- part: Lib.LocalGL.Tadic.ChainLemma
section
/-! Known result: Satake parameters of unitary unramified representations of GL_n come in strings.
There is no classification here, and for a spherical Hecke eigenvector in a smooth unitary
representation, a root c with cq not a root has |c|² ≥ q^(N-2), so |c|² q^k = q^N forces c, …,
cq^(k-1) to be roots. The same count makes the vector orthogonal to the image of a polynomial in U
when a string divides. Source: Tadić, Classification of unitary representations in irreducible
representations of general linear group (non-archimedean case), Ann. ENS 19 (1986); Bernstein,
P-invariant distributions on GL(N), LNM 1041 (1983) for the inequality at the ends of segments.

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level, and conjugacy in
I t I. The setting here is GL_n at pro-p Iwahori level with tame characters, and eigenforms of the
operators U_t on fixed vectors replace Jacquet modules. No regularity is assumed, ties between roots
are allowed, and conjugacy is twisted by an isometric automorphism of the field. Source: Casselman,
The unramified principal series of p-adic groups I, Compositio 40 (1980), Prop. 2.4, 2.5, 3.6;
Haines–Kottwitz–Prasad, Iwahori–Hecke algebras (arXiv math/0309168) §1;
Görtz–Haines–Kottwitz–Reuman, Compositio 146 (2010), Thm 1.1.5 (conjugacy in I t I).

This file: An unramified exponent with sorted roots is non-zero on spherical vectors. Chain lemma:
spherical vector orthogonal to a polynomial in U; strings of Satake roots. -/

open WithZero Valued Finset Equiv Pi Function Complex ComplexOrder Module Polynomial

attribute [local simp] mulSingle_apply normAbsChar mulSingle_comp_equiv update_apply

/-- Let (`torusChar` θ, l) be an exponent of a smooth ρ with l ≠ 0, all θ_i unramified and |θ_i(ϖ)|
non-increasing in i, ϖ a uniformiser. Then l does not vanish identically on the vectors fixed by
GL_N(𝒪[F]).

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t
I. -/
lemma IsExponent.eq_zero_of_eq_zero_on_spherical {F} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N}
  {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ θ l x} (hϖ : v ϖ.1 = WithZero.exp (-1)) (hl :
  IsExponent ρ (torusChar θ) l) (hu : ∀ y, v y.1 = 1 → ∀ i, (θ i y).1 = 1) (hs :
  Antitone fun i ↦ ‖(θ i ϖ).1‖) (H : ∀ y ∈ levelSpace ρ.ρ (intGL _ 𝒪[F]), l y = 0) : l x = 0 :=
  have L k (hk : k ∈ blockParahoric (min N)) z : l (ρ k z) = l z := by
    have u i : v (k i i) = 1 ∧
      k i i ≠ 0 := by grind [exists_v_entry_eq_one_of_mem_intGL hk.1 i, inv_mem hk, one_pos]
    simpa [hl.apply_diagGL_unit, torusChar, monoidHomMulEquiv, *] using
      hl.apply_proIwahori (diagGL (fun i ↦ (.mk0 _ (u i).2)⁻¹) * k)
      (by simp_all [mem_intGL_iff_det, mem_proIwahori_iff_blockParahoric, mem_blockParahoric]) z
  map_compactMean_of_const l (L · · x) ▸ @Fin.induction N (fun m ↦ ∀ y,
    l (compactMean ρ.ρ (blockParahoric (min m)) y) = 0) (by simp_all [mem_blockParahoric]) (fun m h
    y ↦ by simpa [← Perm.one_def] using (@Fin.induction N (fun j ↦ ∀ x,
    (∀ p ∈ blockParahoric (min m), (∀ r ≠ m, v (p r m) < 1) → ρ p x = x) → (∀ i, j ≤ i.castSucc →
    l (ρ (permGL (swap m i)) x) = 0) → l (ρ _ x) = 0) (fun _ _ ↦ (· m bot_le)) (fun j ih x X H ↦ by
    by_contra
    have ⟨y, z, hz, D, B⟩ := exists_line_orbit_sums X L
    let q : ℂ := Nat.card 𝓀[F]
    have A (i : Fin N) := by simpa [↓diagGL_mul_permGL] using
      (hl.apply_monomial_translate hϖ hz (·.1)
      (swap m i) (t := mulSingle i ϖ⁻¹) (by simp +decide [apply_ite, ite_apply, *]; grind))
    have := ih ((θ j ϖ).1 • ρ (diagGL (mulSingle m ϖ⁻¹)) z - q ^ N • (1 - q⁻¹) • x) (fun p h e ↦ by
      simpa [X p h e] using hz ⟨_, (conj_monomial_mem_blockParahoric (mulSingle m ϖ⁻¹) 1 .univ (d :=
        Function.update (min · m + 1) m 0) (by clear * - e h; grind) (by
      simp [@apply_ite Fˣ, apply_ite v, apply_ite WithZero.log, hϖ]; lia)).1⟩) fun i c ↦ by
      simp [-sub_eq_zero, A]
      rw [B, sum_eq_zero]; cases j.eq_or_lt_of_le c <;> simp [-sub_eq_zero, field, *]; repeat grind
    simp [*, -swap_self] at *
    simpa [(by grind [NeZero.ne (q ^ _), Nat.cast_eq_one, Finite.one_lt_card,
      sum_Ioi_add_eq_sum_Ici] : θ j ϖ = q * θ m ϖ), q, Finite.one_lt_card.not_ge] using
      @hs m j (by grind)) (.last N) _ (by grind [_root_.apply_compactMean]) (by simp))) ⊤ x

/-- P(dX) equals (X − 1)(X − q)⋯(X − q^{t−1}) times a divisor of the polynomial e. -/
def HasRootString (P e : ℂ[X]) q d t := ∃ S, P.comp (C d * X) =
  (∏ i ∈ range t, (X - C (q ^ i))) * S ∧ S ∣ e

variable {E} [Field E] [NumberField E] {w : FinPlace E} {N} [NeZero N] {ρ : Rep ℂ (GL (Fin N)
  (LocField w))} [IsSmoothRep ρ.ρ] {B x P} {t : ℕ → ℂ} (hB : IsUnitary ρ.ρ B) (hx : x ∈ levelSpace
  ρ.ρ (Kw ..)) (h0 : x ≠ 0) (e : P = heckePoly w.q N t) (ht : ∀ j, heckeGL ρ.ρ j x = t j • x)
include hB hx h0 e ht

/-- Chain lemma. Let x ≠ 0 be a spherical eigenvector with Hecke polynomial P in a smooth
unitary representation of GL_N(E_w), U the operator of diag(ϖ,1,…,1). A root c with P(qc) ≠
0 has |c|² ≥ q^(N−2); if P = ∏_{i≤k}(X − cq^i)·R, c ≠ 0, then x ⊥ (U − cq^k)R(U)y for
pro-p-Iwahori-fixed y.

Known result: Satake parameters of unitary unramified representations of GL_n come in strings. -/
lemma chain_lemma {ϖ} (hϖ : v ϖ.1 = .exp (-1)) : (∀ c, P.IsRoot c → ¬P.IsRoot (w.q * c) →
  w.q ^ N / w.q ^ 2 ≤ ‖c‖ ^ 2) ∧ ∀ d ≠ 0, ∀ k R, HasRootString P R w.q d⁻¹ (k + 1) →
  ∀ y ∈ levelSpace ρ.ρ proIwahori, B x (aeval (heckeCoset ρ.ρ proIwahori (diagGL (mulSingle 0 ϖ)))
  (((X - C (w.q ^ k : ℂ)) * R).comp (C d * X)) y) = 0 := by
  cases' N with n; nomatch ‹NeZero 0›
  -- the adjoint of `G(U)`
  have A {U U' : End ℂ ρ} (S : Set ρ) (a : ∀ y ∈ S, U y ∈ S ∧ ∀ x, B (U' x) y = B x (U y)) ⦃G
      x⦄ : ∀ y ∈ S, B (aeval U' (.map (starRingEnd ℂ) G) x) y = B x (aeval U G y) := by
    induction G using recOnHorner <;> simp_all [mul_comm]
  have S j := compactMean_eq_self (partialHecke ρ.ρ 1 j x)
    (levelSpace_anti proIwahori_le_blockParahoric (partialHecke_mem_levelSpace hx))
  -- the dual count is the same count for the dual lattices
  let y (a : Fin n.succ) := ite (a = 0) 1 ϖ⁻¹
  have h : x ∈ levelSpace (ρ.ρ.comp invTransposeGL.toMonoidHom) (Kw ..) := by simp_all
  have R i (e : i < n) := by simpa (disch := omega) only [Fin.val_zero, partialHecke_dual hϖ hx
                               i.succ, partialHecke_dual hϖ hx i] using
    partialHecke_hyperplane_count hϖ h 0 (ψ := compactMean ρ.ρ _ * ρ (diagGL y⁻¹)) (fun k o hk z ↦
    .trans (by simp) (compactMean_apply (mem_proIwahori_iff_blockParahoric.2
    (conj_monomial_mem_blockParahoric y 1 _ (d := 0) ⟨⟨(invTransposeGL_mem_intGL _).2 hk.1, nofun⟩,
    (inv_mem hk).2.2⟩ (by simp [y, invTransposeGL, transposeGL, Fin.forall_fin_succ, hϖ]; clear * -
                            o; grind))) _)) (n - i.succ)
  -- `U` and its adjoint `U'`, with the count and its dual read on them
  let u g := (w.q : ℂ) ^ n • (compactMean ρ.ρ proIwahori * ρ g * compactMean ρ.ρ proIwahori)
  have G g {y} (h : _ = y) : u g y = _ := congr((_ : ℂ) • compactMean _ _ (ρ _ $h))
  have I g x y : B (u g⁻¹ x) y =
    B x (u g y) := by simp [u, hB.adjoint_eq_inv, hB.compactMean_adjoint]
  obtain ⟨t0, s, hq, h1, D⟩ := ht 0 ▸ heckeGL_zero hx, S 0, (by simp : (1 : ℂ) < w.q),
    partialHecke_hyperplane_count hϖ hx 0 fun _ _ ↦ compactMean_apply,
    partialHecke_zero_right h ▸ partialHecke_dual hϖ hx _ n.succ.zero_add
  have L := congr(ρ (diagGL y⁻¹) $(D.symm.trans
    (partialHecke_zero_right h ▸ partialHecke_dual hϖ hx n (add_comm ..))))
  set β := diagGL (mulSingle (0 : Fin n.succ) ϖ)
  simp [partialHecke_zero_right hx, ht, S, partialHecke_zero_eq_heckeGL, y,
    (by simp [β, y, Units.ext_iff, diagGL, invTransposeGL, transposeGL,
    -Matrix.coe_units_inv, Fin.forall_fin_succ] : diagGL (fun _ ↦ ϖ⁻¹) = diagGL y * β⁻¹ ∧
    invTransposeGL β = diagGL y * β⁻¹ * diagGL y⁻¹)] at s L D h1 R
  obtain ⟨tn, adj, J, Q, Z, L', K⟩ := left_ne_zero_of_smul (h0 ∘ D.trans), I β, I β⁻¹, one_lt_pow₀
    hq n.succ_ne_zero, by simpa [← L] using (h1 n).symm, G β⁻¹ s,
    @A (heckeCoset ρ.ρ proIwahori β) (u β⁻¹)
    (levelSpace ρ.ρ proIwahori) (by simp +contextual [↓I, u, β, heckeCoset_mulSingle_zero_eq hϖ])
  simp [← G, S, (eq_inv_smul_iff₀ tn).2 L] at R h1 L'
  generalize u β = U, u β⁻¹ = U' at *; clear! u h D; let p := (heckePoly w.q · t)
  have a m : (p m).aeval U x = ((-1) ^ m * w.q ^ m.choose 2 : ℂ) • partialHecke ρ.ρ 1 m x ∧ ∀ c,
    m - 1 ≤ n → ∃ D, (X - C c) * D = p m - C ((p m).eval c) ∧ c • U' (aeval U D x) = ((p m).eval
    (w.q * c) / w.q ^ m) • U' x + (w.q ^ n / w.q : ℂ) • aeval U D x - U' (aeval U (p m) x) := by
    induction' m with m a; simpa [p, heckePoly, partialHecke_zero_right hx]
    rw [(by ext ⟨⟩ <;> simp [p, coeff_one] : p m.succ = X * p m + coeff (p m.succ) 0 • 1),
      coeff_heckePoly]
    use by simp [*, Nat.choose]; module, fun c (h : m ≤ n) ↦ (a.2 c (by omega)).elim fun D b ↦
      ⟨c • D + p m, by simp [smul_eq_C_mul]; linear_combination C c * b.1, ?_⟩
    obtain ⟨⟨⟩⟩ := h.eq_or_lt <;> simp [*, Nat.choose, pow_sub₀] <;> match_scalars <;> field
  choose hP D f d using by simpa [p, ← e, Z] using a n.succ
  -- a polynomial in `U` that kills `x` kills its cyclic module, which `U'` keeps
  have M {y} {V F : ℂ[X]} (N : V.aeval U x = 0) : ∀ j ≤ n, B y (V.aeval U (F.aeval U' (partialHecke
    ρ.ρ 1 j x))) = 0 := have m j := by simpa [*] using congr(aeval U $(mul_comm V (p j)) x)
    by induction F using recOnHorner <;> rintro ⟨⟩ <;> simp +contextual [*, le_of_lt,
                congr(U' $(partialHecke_zero_right hx)).trans L']
  have u c := congr(aeval U $(f c) x); simp [hP, sub_eq_iff_eq_add] at d u
  have k c := by simpa [← adj, L', Z, h1, field, u, ← J, tn] using congr(B x (U $(d c)))
  use fun c h o ↦ have g := congr(B $(d c) (aeval U (D c) x)); real_le_real.1 (sub_pos.1
    (pos_of_mul_pos_left ((hB.1 _ (smul_ne_zero o h0)).trans_eq (by
      simp [adj, u, ← mul_conj', field] at g h ⊢; clear * - g h k s Q;
      grind)) (mul_nonneg (sub_pos.2
      (lt_mul_self Q)).le ((em' _).elim (hB.1 (aeval U (D c) x) · |>.le) (by simp [·]))))).le
  -- if `c` and `q c` are roots, `(P / (X - c))(U) x` is zero, so these roots cancel
  have Y c F (E : (X - C c) * F = P) (r : P.IsRoot (w.q * c)) (o : c ≠ 0) : aeval U F x = 0 := by
    cases (by simpa [← E, X_ne_C] using f c); simp [f] at E r
    refine by_contra (hB.1 _ · |>.ne' ((recOnHorner · ?_ ?_ ?_ : ∀ G, B (aeval U G x) _ = 0)
      _)) <;> simp +contextual [J, r, ← X_mul, (eq_inv_smul_iff₀ o).2 (d c)]
    clear * - k E r s o Q; grind [Q.ne']
  rintro c hc l _ ⟨W, h, F, rfl⟩ y m
  replace h := (funext (by simp [hc]) : P = _).trans (congrArg (Polynomial.comp · (C c * X)) h)
  rw [← mul_assoc, mul_comm, ← partialHecke_zero_right hx, ← K y m,
    Not.imp_symm (hB.1 _) ((A ⊤ (by tauto) _ ⟨⟩).trans (M ?_ 0 bot_le)).not_gt, B.map_zero₂]
  induction' l with l ih generalizing W F; simp [by simpa [h] using hP]
  rw [prod_range_succ, mul_assoc] at h; set V := _ * W
  specialize Y (w.q ^ l / c) (c • (_ * V).comp (C c * X)) (.symm (funext (by
    simp [h, field, prod_range_succ]))) (by simp [h, V, field, pow_succ])
  simp [by simpa [hc, eval_prod, prod_eq_zero_iff, End.aeval_apply_of_mem_apply_eq_smul (by
    simpa [← eq_inv_smul_iff₀ hc, smul_smul, -map_pow] using ih _ 1 h),
    (pow_right_strictMono₀ hq).injective.eq_iff] using Y]

/-- Let x ≠ 0 be a spherical Hecke eigenvector in a smooth unitary representation of GL_N(E_w),
with Hecke polynomial P. If P(c) = 0 and |c|² q^k = q^N, then c, cq, …, cq^(k−1) are all
roots of P.

Known result: Satake parameters of unitary unramified representations of GL_n come in strings. -/
lemma isRoot_string_of_norm {c k} (hc : P.IsRoot c) (h : ‖c‖ ^ 2 * w.q ^ k = w.q ^ N) {i} (hi :
  i < k) : P.IsRoot (c * w.q ^ i) := by
  induction' i using Nat.strongRec with i ih
  obtain ⟨j, ⟨⟩⟩ := hi.dest
  by_contra; refine this (star_eq_zero.1 (.trans ?_ (mul_eq_zero_of_right ((-star c * w.q ^ i) ^ N *
    B (ρ (.scalar _ (uniformizer w)) x) x / B x x / w.q ^ N.choose 2) (ih j ?_ (by lia)))))
  simp [e, heckePoly, eval_finsetSum, mul_sum]; convert sum_flip _ with d
  cases' exists_add_of_le (mem_range_succ_iff.1 ‹_›) with b hd
  field [(hB.1 x h0).ne']
  linear_combination (norm := (simp [-sub_eq_zero, hd, ← mul_conj', ← heckeGL.eq_1, ht]; ring; simp
    [field])) -congr((star c * w.q ^ i) ^ b * w.q ^ $(show b.choose 2 + N * d = N.choose 2 +
    d.choose 2 + d by qify [*, Nat.cast_choose_two]; ring) * (-$h / w.q ^ N.succ) ^ d *
    $((heckeGL_dual hx (v_uniformizer w) (by simpa) ▸ hB.2 _ x _).trans (by simpa [Set.indicator]
    using ((isBiInvariant_basicDoubleCoset _).heckeFun_adjoint B hx hB.2 hx).2.symm)))
  cases i; lia; simpa +arith [eq_div_of_mul_eq _ h, field, ← pow_mul, ← pow_add,
    pow_le_pow_iff_right₀] using
    (chain_lemma hB hx h0 e ht (v_uniformizer w)).1 _ (ih _ .refl hi.le) (by grind)
end

-- part: Lib.GaloisRep.EvenRank.ThetaLift
section
/-! Known result: the theta lift to larger rank, the step that reduces even rank to odd rank. Here a
non-zero theta lift in the convergent range from definite U(n) to U(n+s), s > n, replaces endoscopic
transfer. It keeps spherical places, and its Hecke polynomials are twisted and gain the string of a
character of U(1). Source: Blasius, Rogawski, Motives for Hilbert modular forms, Invent. Math. 114
(1993) and Shin, Ann. of Math. 173 (2011) for the idea (endoscopic transfer to odd rank); Harris,
Soudry, Taylor, Invent. Math. 112 (1993) for theta lifts with a varying character.

This file: Nonzero theta lift to larger rank; Hecke polynomials twisted and gaining a string. -/
seal Finset.univ Finset.sum Finset.prod

open AutChar Algebra Filter Fintype G Gf Matrix Polynomial Set Space Valued

attribute [local simp] onHom_snd stdLattice.mem_stdLattice mul_mem projOn_finHeisOp
  dataInner_finHeisOp finHeisOp_finHeisOp add_mem_cancel_right
  ite_mem mem_integralBox sum_mem matToVec

/-- Theta lift: for f ≠ 0 of rank n ≥ 1, weight (κ, e), s > n, b unramified of weight c ≤ e,
some F ≠ 0 of weight κ' on I_{n+s} is spherical where f is; its rescaled Hecke polynomial is
P·∏_{l<s}(X − θ_l(ϖ)), with θ_l given by `AutChar.HasWeight.toAlgebraic`.

Known result: Theta lift to larger rank, the step that reduces even rank to odd rank. -/
lemma exists_theta_lift_heckePoly {E n} [Field E] [CMType E] [WeilData E] [Fintype n] [Nonempty n]
  {κ κ' e s c}
  {b : AutChar E} (hb : b.HasWeight c 1) (hc : c ≤ e) (hκ : κ' = fun v h ↦ ite (h < card n) (κ v h)
  (ite (h = card n) (e v - c v).toNat 0)) (f : AlgForm n κ e) (h₀ : f.1 ≠ 0) (hs : card n < s) : ∃ F
  ∈ (stdSpace E (Fin (card n + s))).forms (κ', 0), F ≠ 0 ∧ ∀ {w}, f.1 ∈ sphericalAt
  (rightRegular ℂ ..) w → F ∈ sphericalAt (rightRegular ℂ ..) w ∧ ∀ {hw P}, HasHeckePolyAt f.1 w hw
  P → ∃ Q, HasHeckePolyAt F w hw Q ∧ Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s).1.1 ∅ w) =
  P * ∏ l : Fin s, (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)).1.1 ∅ w)) := by
  let W := stdSpace E (Fin (card n + s))
  let H : OpenSubgroup _ := ⟨rightStab f.1, f.2.1⟩
  obtain ⟨⟨x, _, _, ρ, _⟩, ⟨B, o, h₂⟩, N, _, h₃⟩ :=
    @exists_integral_isotropic_frame E n (Fin (card n + s)) _ _ _ _ _ (by simp; lia),
    exists_inf_trivialOn_le H.2, exists_principalLevel_subset H.mem_nhds_one
  let z := (N : E)⁻¹ • idem (SetLike.coe B).conjClosure
  -- a sharp datum for a level inside the stabiliser `H` of `f`, off the poles of `z`
  have ⟨_, _, _, L⟩ : ∃ F J c,
    IsSharp (S := stdSpace E n) (T := W) b {w | 1 < v (z w)} F (H.1 ⊓ J) c := by
    refine ⟨_, (MulAction.stabilizer ..).comap ((pairWeil (stdSpace ..) W ..).comp (.prod (.inr ..)
      1)).toHomUnits, _, by simp,
      finHeisOp_mem_finitePart (matToVec (z • x)) vacElem_mem_finitePart, fun A _ a ↦ by
      simp [← mul_assoc, *, (@idem_mul_mem_Ô _ _ _ A.conjClosure z).2 (by
      rintro _ (h | h) <;> simpa [← v_star_apply, z] using a.le_compl_left h)],
      fun g c ↦ .symm (ite_eq_iff'.2 ⟨(congrArg _ ·.1.2.symm), fun r ↦ ?_⟩), rfl, by tauto⟩
    set D := g⁻¹.1.1 - 1 with ← e; simp [sub_eq_iff_eq_add] at e
    erw [weilMatrixCoeff, pairWeil_apply, onHom_fin, omega_finHeisOp, omega_vacElem,
      ← dataInner_finHeisOp _ (-matToVec (z • x))]; simp
    erw [← projOn_vacElem, dataInner_projOn, map_projOn_eq_const _ (projOn _ ⊤ ∘L finHeisOp .. ∘L
      _), map_zero] <;> simp [rep_apply_apply]; intro u _ q; have q p := q (ρ p)
    simp [*, mulVec_eq_sum, sum_prod_type, mul_add, ← add_assoc] at q
    have K i j := mem_Ô.2 fun w ↦ (Finite.exists_max (v <| D · j w)).rec fun p a ↦ (a i).trans
      (not_lt.1 fun h ↦ h.not_ge (v.map_sub_le ((c w (by simpa [h.pos] using ((((v.comap (evalAt
      w)).leAddSubgroup _).add_mem_cancel_right (sum_mem (by simp [mul_le_of_le_one_of_le, *,
      mem_Ô.1]))).1 ((mem_Ô.1 (q p j) w).trans h.le)))).isIntMatrix_inv ..) (mem_Ô.1 (by simp) w)))
    simp (disch := simp [*]) at q; have k := inv_mem_iff (x := g).1 (mem_Kf.2 (by simp [*]))
    cases r ⟨⟨(mul_mem_cancel_left (h₃ ⟨componentOn_mem_Kf (inv_mem k), (⟨_, q · ·, by
      erw [← smul_def (N : E)]; simp [z, *, componentOn, U.cutAt, cutGL, sub_smul]; rfl⟩)⟩)).1
      (h₂ (by simp_all [componentOn_mem_Kf])), (pairWeil_apply ..).trans (.trans (by
      erw [omega_finHeisOp, ← map_smul, kronecker_mulVec_eq_matToVec, ← pairWeil_apply,
        pairWeil_eq_smul_of_projOn_eq ⊤] <;> simp [hb.apply_det_eq_one, *,
      x.mul_add, Dᴴ.mul_assoc, ↓vecToMat_matToVec, add_comm]) (congrArg _ (finHeisOp_vacElem (y :=
      matToVec (x * z • D)) fun _ ↦ sum_mem (by simp [*]))))⟩, k⟩
  obtain ⟨⟨_, h⟩, g⟩ := Exists.intro _ (isHCParam_hcParameter n κ e),
    isHCParam_hcParameter (Fin (card n + s)) κ' 0
  have p := ((IsHCParam.paramsCorrespond_iff (eb :=
    c) (by delta IsHCParam hcParameter diagramWeight at *; convert h <;> grind
    [Pi.le_def]) ⟨by grind [card_fin], by simp [hs.pos], rfl⟩).2 g).isEdge_jointHarmonic
  obtain ⟨A, y, rfl⟩ := (p.isArrow 1 b L.mem_finitePart).1, (toAlgForm (stdSpace ..) h).surjective f
  refine have Z z := h₀ (by simp [((rallis_inner_product_euler p (by simp; omega)).choose_spec.2 1 b
      L y fun _ ↦ (by simp [← ofAlgForm_toAlgForm h, algFormCoeff, ·.1 _])).1 (by aesop)]); ⟨_,
      (toAlgForm _ g _).2, Z, fun {w}
      W ↦ have K := L.vacuum_off {w} _ (by simp [z, smul_def, o w (by simpa [funext_iff, LE.le,
        H] using W)]); ⟨fun k ↦ congr($(toAlgForm_formRep ..).1).symm.trans (by
    rw [A.formRep_formLift 1, pairWeil_eq_smul_of_projOn_eq _ K] <;> simp),
        fun ⟨_, r, e, u⟩ ↦ have G := (isSphericalWith_toAlgForm_iff ..).2 (isSphericalWith_formLift
          (card_fin _) (by simp [CharUnramifiedAt]) (hb.charUnramifiedAt rfl rfl) ‹_› K A
          ((isSphericalWith_toAlgForm_iff ..).1 (isSphericalWith_of_heckeSplit W
          u))); have a := (exists_heckeSplit_eq_smul ..).choose_spec _ G; (fun K ↦
            ⟨_, K, eq_of_infinite_eval_eq _ _ (infinite_of_finite_compl
            ((eventually_cofinite_ne 0).mono fun x z ↦ ?_))⟩) ⟨G.1, _, rfl, a⟩⟩⟩
  rw [e, eval_mul, eval_heckePoly, ← mul_div_cancel₀ x, scaleRoots_eval_mul, (K.isMonicOfDegree
    Z).1, eval_heckePoly, ← mul_assoc, ← mul_pow,
    ((smul_left_inj Z).1 ((isSphericalWith_of_heckeSplit G.1 a).2 _ ▸ G.2 _ :)).trans (mul_comm ..),
    eval_prod, card_fin, pow_add, ← Fin.prod_const s, trivialHecke, mul_mul_mul_comm,
    Finset.prod_range, ← Finset.prod_mul_distrib] <;> congr! 3 <;> simp [frobValue, field,
    HasWeight.toAlgebraic, w.q_eq_sqrt_sq, HeckeChar.atUnif, heckeCoeff, AutChar.spaceChar,
    zpow_add₀, zpow_sub₀, zpow_mul (_ : ℂ), z]; ring
end
