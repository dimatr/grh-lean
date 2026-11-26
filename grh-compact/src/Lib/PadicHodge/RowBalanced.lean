import Lib.PadicHodge.Valuation
import Lib.GaloisRep.WeightCongruence
import Lib.PadicHodge.TiltingLemma
import Lib.PadicHodge.ValueFamilies
import Lib.PadicHodge.ExponentTheorems
import Lib.PadicHodge.CrystallineRank

section
/-! Roots of unity keeping polynomial valuations low, in any degree. One polynomial in the values of
a twist on tame inertia bounds the twisted Selmer length at all points and is sharp at a chosen one,
and finitely many integral polynomials of any degree that are little divisible at points near 1 stay
so at powers of one tuple of ℓ-power roots of unity, which then defines the twist. A degree-free
bound at some ℓ-power root of unity for one element is known and the determinant step is base change
of Fitting ideals. Related work: Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Serban, An
infinitesimal p-adic multiplicative Manin–Mumford conjecture, 2018; Kurihara, The structure of
Selmer groups of elliptic curves and modular symbols, 2014.

This file: ℓ-power roots of unity keep valuations of polynomials of any degree low. -/
seal Finset.univ Finset.sum Finset.prod

open Polynomial Filter Finset Real IsUltrametricDist NeZero Function Fint CoeffRing
variable {ℓ} [p : ThePrime ℓ] {κ : Type}

/-- Fix 0 < r < 1 with |ℓ| < r^{ℓ−1} and finitely many y_k > 0. For large N, then large O:
polynomials F_k over O of any degree with Gauss norm of radius r at least y_k have all
|F_k(ζ − 1)| ≥ r y_k for one ζ ∈ O, ζ^{ℓ^N} = 1. -/
lemma exists_root_of_unity_eval_large [Fintype κ] (y : κ → ℝ) {r} (hy :
  ∀ k, 0 < y k) (h0 : 0 < r) (h1 : r < 1)
  (e : ‖(ℓ : PadicAlgCl ℓ)‖ < r ^ (ℓ - 1)) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ F : κ →
  O.1[X], (∀ k, ∃ i, y k ≤ ‖((F k).coeff i).1‖ * r ^ i) → ∃ ζ : ↑O, ζ ^ ℓ ^ N = 1 ∧ ∀ k, r * y k ≤
  ‖((F k).eval (ζ - 1)).1‖ := (exists_pow_lt_of_lt_one (by simp [ne] : 0 < ‖(ℓ : PadicAlgCl ℓ)‖)
  h1).rec fun a ha ↦ ((tendsto_sum_range_one_div_nat_succ_atTop.atTop_mul_const_of_neg (log_neg
  h0 h1)).eventually_lt_atBot _).mono fun N J ↦ .mono (.all fun j : range N ↦
  eventually_primitiveRoot (ℓ ^ j.1.succ)) fun O η F h ↦ by
  contrapose! J
  let ρ j := r ^ (↑(ℓ ^ j) : ℝ)⁻¹
  let ⟨m, ρ1⟩ : Monotone ρ ∧ ∀ j, ρ j ≤ 1 := by
    simp [ρ, Monotone, rpow_le_one_iff_of_pos, *]; bound [pos ℓ]
  let g j := (@gaussNorm_isAbsoluteValue (ρ j) O _ (.comp (NormedField.toAbsoluteValue _)
    O.1.subtype_injective) isNonarchimedean_norm (by bound)).toAbsoluteValue
  have U {j F x} : g j F ≤ x ↔ ∀ i, ‖(F.coeff i).1‖ * _ ≤ x := ⟨swap (F.le_gaussNorm _
    (by bound) · |>.trans), (exists_eq_gaussNorm ..).choose_spec.trans_le ∘ (· _)⟩
  have G k t : y k ≤ g t (F k) := (h k).rec (by grw [← U.1 le_rfl ·, ← m bot_le]; simp [ρ])
  choose Q hQ using (dvd_prod_of_mem F <| mem_univ ·)
  have Z t : 0 < ∏ k, g t (F k) := prod_pos (by grind)
  grw [sum_mul, ← sum_le_sum fun j _ ↦ ?_, sum_range_sub' fun j ↦ a * (∏ k, g j (F k)).log, ← G,
    U.2 (by bound)] <;> simp [prod_pos, le_of_lt, *]
  choose η hη using η ⟨j, ‹_›⟩
  choose k u using fun i ↦ J (η ^ i) (by grind [hη.pow_eq_one_iff_dvd, pow_dvd_pow, =_ pow_mul])
  have W := congr(($(X_pow_sub_C_eq_prod hη one_le (one_pow _)).comp (X - C (-1))).derivative).symm
  choose S s using (range (ℓ ^ j.succ)).dvd_sum fun i hi ↦ prod_erase_mul _ (fun i ↦ X - C (η ^ i -
    1)) hi ▸ mul_dvd_mul_left _ ((sub_mul _ (F (k i)) _ ▸ (dvd_modByMonic_sub ..).mul_right
    (Q (k i))).trans (sub_dvd_pow_sub_pow _ _ (a * j.succ)))
  simp [-map_neg, -map_sub, -map_pow, Polynomial.prod_comp, sub_sub, ← map_add, ← hQ, mul_sub,
    derivative_prod_finset, derivative_pow, neg_add_eq_sub, ← sum_mul] at W s
  have K t (ht : j ≤ t) := (by
    have n : IsNonarchimedean (g t) := isNonarchimedean_gaussNorm _ isNonarchimedean_norm (by bound)
    have l b : g t (X - C b) = ‖b.1‖ ⊔ ρ t ∧ g t (C b) = ‖b.1‖ := ⟨eq_of_forall_ge_iff (by
      simp [U, ← Nat.and_forall_add_one, coeff_X]; bound [norm_nonneg b.1]), gaussNorm_C ..⟩
    have z i := (norm_pow_sub_one_le_norm_sub_one (norm_le_one η) i).trans
      ((lt_of_pow_lt_pow_left₀ _ (by bound) (by rwa [norm_zeta_sub_one_pow (by simpa),
      Nat.totient_prime_pow_succ p.out, pow_mul, rpow_inv_natCast_pow h0.le out])).le.trans (m ht))
    have V a b := congr(g t $s) ▸ n.add_eq_right_of_lt (map_neg_eq_map _)
      ((n.apply_sum_le_sup a).trans_lt b)
    simp [map_neg_eq_map, -map_neg, -map_sub, -map_natCast, ne, *] at V
    use (eq_inv_mul_iff_mul_eq₀ (by positivity)).2 (V fun _ _ ↦ by
      grw [ρ1, (u _).le, G, mul_assoc, ← map_mul, ← hQ, mul_pow, pow_mul, ha] <;> simp [*]))
  have V := log_le_log (by simp [ne, field, *]) ((@U j S _).2 (by grw [m j.le_succ, ← U]))
  simp [log_mul, rpow_def_of_pos, ρ, pow_add, field, ne_of_gt, ne, *] at V ⊢
  grind [nsmul_le_nsmul_left_of_nonpos (log_neg h0 h1).le p.out.two_le]

/-- Fix δ > 0, m, L, a, q and finitely many bounds B_k. For large N, then large O: given F_{k,d}
(1 ≤ d ≤ m) in ≤ q variables with valuation ≤ B_k at points u_{k,d}, ℓ ∣ (u − 1)^a coordinatewise,
and monic D_n of total degree ≤ L, some tuple ζ in O of ℓ^N-th roots of unity has
v(F_{k,d}(ζ^d)) ≤ δ + B_k and all v(D_n(ζ_j)) ≤ δ.

Roots of unity keeping polynomial valuations low, in any degree. -/
lemma exists_roots_of_unity_ellVal_le [Finite κ] {δ : NNReal} (hδ : 0 < δ) (m L a q : ℕ) (B : κ →
  NNReal) : ∀ᶠ N in atTop, ∀ᶠ O : CoeffRing ℓ in atTop, ∀ (σ T : Type) [Fintype σ] [Fintype T],
  Fintype.card σ ≤ q → ∀ (D : T → O.1[X]) (F : κ × Set.Icc 1 m → MvPolynomial σ _) (u : _ → _ → ↑O),
  (∀ n, (D n).Monic) → ∑ n, (D n).natDegree ≤ L → (∀ k j, ↑ℓ ∣ (u k j - 1) ^ a) → (∀ k,
  ellVal ((F k).eval (u k)).1 ≤ B k.1) → ∃ ζ : σ → ↑O, (∀ k, ellVal ((F k).eval (ζ · ^ k.2.1)).1 ≤
  ↑(δ + B k.1)) ∧ ∀ j, ζ j ^ ℓ ^ N = 1 ∧ ∀ n, ellVal ((D n).eval (ζ j)).1 ≤ δ := by
  choose r r0 e r1 using exists_pow_btwn (x := ‖(ℓ : PadicAlgCl ℓ)‖ ⊔ ℓ ^ (-δ.toReal)) (q + L + ℓ +
    m * a).succ_ne_zero (by simp [norm_p_lt_one, rpow_lt_one_iff, Fact.out, *]) one_pos
  simp [pow_lt_one_iff_of_nonneg r0.le] at r1
  have R n (h : n ≤ _ := by grind) := max_lt_iff.1 (e.trans_le (pow_le_pow_of_le_one r0.le r1.le h))
  refine .mono (.all fun n : Set.Iic q ↦ exists_root_of_unity_eval_large (Option.rec (r ^ L) fun k :
    κ × Set.Icc 1 m ↦ ℓ ^ (-B k.1 : ℝ) * r ^ n.1) (by rintro ⟨⟩ <;> bound [pos ℓ]) r0 r1 (R _).1)
    fun N Y ↦ .mono (.all Y) fun O Y σ T _ _ hq D F u hD hL hu hB ↦ (univ.induction_on (motive :=
    (fun T s ↦ ∃ ζ, (∀ k, ℓ ^ (-B k.1 : ℝ) * r ^ #s ≤ ‖((F k).eval (s.piecewise (ζ · ^ k.2.1) (u
    k))).1‖) ∧ ∀ j ∈ s, T ζ j) (_ : _ → Set σ)) ⟨1, by simp [← ellVal_le_iff, *]⟩ fun j s _ ⟨ζ, H,
    h⟩ ↦ ?_).imp fun ζ ↦
    .imp (by grw [← (R _).2.le]; simp [rpow_add, pos, ↓ellVal_le_iff]) (· · (by simp))
  have p d x y (h : x ^ d = (y j).1) G : (MvPolynomial.eval y G : ↑O).1 = aeval (x - 1)
    (G.aeval fun i ↦ ite (i = j) ((1 + X) ^ d) (C (y i)))
  apply G.induction_on <;> simp +contextual [*, apply_ite]
  choose z Z W using Y ⟨_, s.card_le_univ.trans hq⟩ (Option.rec (taylor 1 (univ.prod D)) _) (·.rec
    ⟨(univ.prod D).natDegree, by simp [leadingCoeff_prod, natDegree_prod_le, hL.trans',
    pow_le_pow_iff_right_of_lt_one₀, *]⟩ fun k ↦ (not_forall₂.1 (mt (pow_le_norm_aeval ((X ^ k.2.1 -
    C (u k j).1) ^ a) (O.1.val 1) r0.le) (by simpa [leadingCoeff_X_pow_sub_C k.2.2.1, norm_sub_rev]
    using ((dvd_iff_norm_le ..).1 (hu ..)).trans_lt (R _ (by grw [k.2.2.2]; lia)).1))).rec
    fun w ⟨hw, W⟩ ↦ (exists_norm_finsetSum_le ..).imp fun i h ↦ by
      simp [norm_sub_rev] at hw W ⊢
      grw [H, p k.2 w, aeval_eq_sum_range, h.2, O.1.smul_def] <;> simp [*]
      gcongr)
  have V n := ellVal_le_iff.2 <| ((dvd_iff_norm_le ..).1 (eval_dvd (dvd_prod_of_mem D
    (mem_univ n)))).trans' (by grw [(R L.succ).2, pow_succ', W none, taylor_eval_sub])
  refine ⟨update ζ j z, fun k ↦ ?_, by grind⟩
  simpa +contextual [pow_succ, mul_rotate' r, p k.2 z, piecewise, *] using
    (W k).trans congr(‖$(aeval_algebraMap_apply _ (z - 1) _)‖).ge
end

section
/-! Tied conditions at new primes shrink Selmer groups. At new split primes a slope ties a cocycle's
value on tame inertia to its value at Frobenius, as the twist chosen later nearly imposes, and by
reciprocity a good prime and a generic slope shorten a long tied Selmer group, so boundedly many
primes make all these groups short. Lowering Selmer groups mod ℓ^n by new local conditions at
Chebotarev primes with trivial Frobenius is known. Related work: Fakhruddin–Khare–Patrikis, Relative
deformation theory and lifting irreducible Galois representations, 2021; Mazur–Rubin, Diophantine
stability, 2018; Darmon–Diamond–Taylor, Fermat's Last Theorem, 1995.

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

This file: Boundedly many tied primes shorten Selmer groups; one anticyclotomic twist then does,
controlling L-values. -/

open Module Fintype NeZero Finset Fint
variable {ℓ} [ThePrime ℓ] {E ι : Type} [Field E] [UnramCMField E] [Finite ι] {n : ι → Type} [∀ i,
  Fintype (n i)] {S₀ S : Finset (FinPlace E)} {z M} {γ β : ι → _} (hS : S ⊆ S₀) (hz :
  z ∈ inertiaAbove (S₀ \ placesDividing E ℓ))
include hS hz
attribute [-simp] Set.insert_eq_of_mem

open IsLocalRing Ideal LinearMap Order Matrix.Module Function Ideal.Quotient in
/-- Let ρ_i over O (`PadicIntegerRing`) be balanced up to β_i, S ⊆ S₀, W a neighbourhood of z
inertial at S₀ off ℓ, a ∣ ℓ^M. For some J₀ and every N, some set of at most J₀ primes as in
`IsPencil` makes each tied Selmer module mod a, zero at γ_i, of length ≤ β_i.

Tied conditions at new primes shrink Selmer groups. -/
lemma exists_isPencil {O W} [CommRing O] [PadicIntegerRing O ℓ] {ρ : ∀ i, _ →* Matrix _ (n i) O}
  {L : ∀ _, Set _} (h : ∀ i, IsBalanced ℓ S (ρ i) (L i) (γ i) (β i) M) (hW : W ∈ nhds z) {a : O} :
  a ∣ ℓ ^ M → ∃ J₀, ∀ N, let X T J x i a := selmerModule (ρ i) (unionWithConj S T) (L i ∪
    tieRelations J x i ∪ {.single (γ i) 1}) (QuotSpan a)
  let Q := IsPencil ℓ S₀ (fun i g ↦ reduceModPow ℓ M (ρ i) g = 1) W N
  ∃ P₀ J x, Q P₀ J x ∧ #J ≤ J₀ ∧ ∀ i, length O (X J J x i a) ≤ β i := by
  refine WfDvdMonoid.induction_on_irreducible a (by simp [ne] at ·) (fun a u _ ↦
    ⟨1, (exists_isAnticyclotomicAt · ∅ S₀.finite_toSet (Subgroup.subset_normalClosure (by simpa))
    hW |>.imp fun P₀ ⟨_, _, A, _⟩ ↦ ⟨{P₀}, fun _ ↦ (A, 0), by constructor <;> simp_all [IsAuxiliary,
    isSplit_of_q_prime], by simp [(length_mono le_top).trans, u]⟩)⟩) fun a ϖ z hϖ ih ha ↦ ?_
  obtain _ := NeZero.mk z, NeZero.mk hϖ.ne_zero, dvd_of_mul_left_dvd ha
  have F i J R : Finite (selmerModule ..) := let := IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha)
    have ⟨_, _, _, _, _, H⟩ :=
      exists_corepresenting_coords _ (ρ i) ((h i).1.eventually_eq 1) (finite_toSet J) R
    .of_injective _ (H _ (nsmul_quot_eq_zero ha) fun g e b ↦ congr($e • b).trans
      (by simp)).2.1.injective
  let f : {f // ker f = ⊥} := ⟨_, (span {a}).ker_liftQ_eq_bot' ((span {ϖ * a}).mkQ ∘ₗ (ϖ • 1)) (ext
    (by simp [ker_comp, mem_span_singleton, mul_dvd_mul_iff_left, ne]))⟩
  apply (ih ‹_›).imp'
  intro J₁ ih N X Q
  choose P₀ J x q d b using ih N
  have I {J x} (hp : Q P₀ J x) T ⦃k : O⦄ (hk : k ∣ ℓ ^ M) {i R K} l : selmerModule (ρ i)
    (unionWithConj S J) R (QuotSpan k) ⊓ ker (pi fun v : ↥(J \ T) ↦ evalConjPair (x v).1.γ) ≤
    selmerModule _ (unionWithConj S T) K _ := fun c ⟨a, z'⟩ ↦ selmerModule_mono
    a l fun v o ↦ have ⟨w, j, e⟩ : ∃ w ∈ J \ T, v = w ∨ v = star w := by clear * - o; grind
    (hp.3 w (sdiff_subset j) |> fun p ↦ exists_conj_side_detects (nsmul_quot_eq_zero hk) _ p.6.2.2
      p.5 (by clear * - o h; grind [inertiaAbove, IsBalanced]) e).elim fun b ⟨_, _, H⟩ ↦
    (H c a congr(($z' ⟨w, j⟩ ⟨b, ·⟩))).1
  let g (s : _ × _) k i := length O (X s.1 s.1 s.2 i k)
  obtain ⟨⟨J, x⟩, ⟨h₀, B, d⟩, W⟩ := (InvImage.wf (univ.sum <| g · (ϖ * a)) wellFounded_lt).has_min
    {t | Q P₀ t.1 t.2 ∧ g t a ≤ β ∧ #t.1 + univ.sum (g t (ϖ * a)) ≤ ?f J₁} ⟨(J, x), q, b, by
    grw [ENat.natCast_toNat, d, sum_le_sum fun i _ ↦ by grw [← relLength_add_length_inf,
      length_mono (I q ∅ ha bot_le), relLength_ker, length_mono le_top, length_top, length_pi,
      (by simpa : ENat.card _ ≤ .card (Fin J₁)), ← length_finsupp]]
    simp [length_ne_top, -length_finsupp]⟩
  refine ⟨_, _, _, h₀, Nat.cast_le.1 (le_of_add_le_left d), fun i ↦
    by_cases (h₀.length_le_of_unseen_class (h i) rfl hS ha · fun P q Z r ↦
    relLength_eq_zero.1 (not_bot_lt_iff.1 fun y ↦ ?_)) fun u ↦ (B i).trans' (length_le_of_le_map
    ((f.1.compLeft _).compLeft _) _ (mk_surjective.comp_left.comp_left.forall.2 fun s v ↦ by
    choose a e using (mem_span_singleton.1 <| hϖ.maximalIdeal_eq.le fun h ↦ u ⟨_, v, ·, ·, h.map _⟩)
    cases funext₂ e
    exact ⟨(a · ·), v.imp (fun h ↦ (comp_mem_obeying_iff .id).2 (f.2.le <|
      (comp_mem_obeying_iff _).1 h · · ·)) (.desc _ _ · (ker_eq_bot.1 f.2).comp_left), rfl⟩))⟩
  have K := by simpa [q, ker_pi, iInf_subtype] using I (r 0) J
  choose b c H using fun k [NeZero k] ↦
    tilting (evalConjPair Z.γ) (evalConjPair Z.φ) (X (insert P J) J x i k)
  obtain ⟨t, v, ht, hu⟩ := by simpa [residue_surjective.exists] using
    Cardinal.exists_notMem_of_length_lt (0 :: b (ϖ * a) ++ b a) (.trans_le (mod_cast
    (h i).5.trans_le' (by clear * - c; grind [card_prod, card_bool])) (Cardinal.natCast_toNat_le _))
  let u := (insert P J, update x P (Z, Pi.single i v.unit.inv))
  have A j k : X u.1 u.1 u.2 j k ≤ X u.1 J x .. ⊓ ker (evalConjPair Z.γ - (u.2 P).2 j • evalConjPair
    Z.φ) := fun c ↦ by simp +contextual [-Pi.single_apply, X, u, selmerModule, mem_obeying,
    funext_iff, tieRelations, evalConjPair, or_imp, forall_and, (ne_of_mem_of_not_mem · q)]
  have U {k} [NeZero k] hk h := (forall_update_iff ⊥ fun j r ↦ r + g u k j ≤ g (J, x) ..).2 ⟨by
    unfold g
    grw [length_mono, H k t h, length_mono, relLength_add_length_inf]
    grw [K hk .rfl]
    grw [A]
    simp +contextual [u, smul_smul, IsConcreteLE.le_iff],
    fun j e ↦ by simpa [bot_eq_zero'] using length_mono ((A ..).trans (by simp [u, X, *]))⟩
  have L := lt_of_le_of_lt' (by simpa [bot_eq_zero', sum_update_of_mem, X] using sum_mono (U ha
    ht)) (ENat.lt_add_left (by simp [g, length_ne_top]) y)
  exact W u ⟨r _, B.trans' (le_of_add_le_right (U ‹_› hu)), by
    grw [card_insert_le, Nat.cast_succ, add_right_comm, add_assoc, add_one_le_of_lt L, d]⟩ L

open Matrix Filter MvPolynomial ENNReal NNReal CoeffRing IsDiscreteValuationRing Subalgebra

/-- Let ρ_i be balanced up to β_i, val_k families, z inertial at S₀ off ℓ, v(μ(z) − 1) ≤ c, β_i + v
det(ρ_i z − 1) + v det(ρ_i z^{−c} − 1) ≤ B_i < ∞, η > 0. Some I, ψ make ψ^d, 1 ≤ d ≤ m, twists
(`IsAuxTwist`) raising v(val_k) by ≤ 8c + η, with ψ^dρ_i of Selmer length ≤ B_i + η.

One anticyclotomic twist makes all Selmer groups short. -/
lemma exists_anticyclotomic_twist {κ T : Type} [Finite κ] [Finite T] {O : CoeffRing ℓ} {ρ : ∀ i,
  _ →* Matrix _ (n i) O} {μ : κ → T → _} {L : ∀ _, _} {B : ι → _} (hρ : ∀ i, IsBalanced ℓ S (ρ i)
  (L i) (γ i) (β i) M) {val : κ → _} (hf : ∀ k, IsFamily S₀ (μ k) (val k)) (hB : ∀ i, B i ≠ ⊤) (hβ :
  ∀ i, O.normLength (β i + ∑ b, addVal _ (ρ i (idOrConjInv b z) - 1).det) ≤ B i) {c η : ℝ≥0} (hc :
  ∀ k t, ellVal ((μ k t z).1 - 1) ≤ c) (hη : 0 < η) m : ∃ I ψ, ∀ d ∈ Set.Icc 1 m,
  (∀ k, ellVal (val k I (ψ ^ d)) ≤ ellVal (val k ∅ 1) + 8 * c + η) ∧ IsAuxTwist S₀ I (ψ ^ d) η ∧
  ∀ i, ∀ᶠ O' in atTop, ∃ hO : O ≤ O', ∃ ψ', (∀ g, (ψ' g).1 = (ψ ^ d) g) ∧
  O'.normLength (length O' (selmerModule (twistRep (inclusion hO).1 ψ' (ρ i)) (unionWithConj S I)
  (mapRel (inclusion hO).1 '' (L i ∪ {.single (γ i) 1})) (QuotSpan (ℓ ^ M : ↑O')))) ≤ B i + η := by
  choose J₀ hJ using exists_isPencil hS hz hρ ((Eventually.all fun k ↦ .all fun t ↦
    ((IsUltrametricDist.isClosed_ball ..).preimage (Units.continuous_val.comp ((hf _).1
    _))).compl_mem_nhds (ellVal_le_iff.1 (hc k t)).not_gt).and (.all fun i ↦ (((hρ
    i).1.comp_continuous continuous_conjGal.inv).prodMk (hρ i).1).eventually_eq z)) dvd_rfl
  choose δ hδ _ using exists_pos_mul_lt hη (J₀ * 8 + 2)
  lift B ⊕ᵥ fun k ↦ ellVal (val k ∅ 1) + 8 * c to ι ⊕ κ → ℝ≥0 using by
    simp [ellVal, mul_eq_top, (hf _).4, *] with b W
  choose k hk using (exists_roots_of_unity_ellVal_le hδ 1 _ 1 _ b).exists
  choose N hN l using ((exists_roots_of_unity_ellVal_le hδ m _ _ J₀ (δ + b · + J₀ * 8 * δ)).and
    (Ici_mem_atTop _)).exists
  choose P₀ J x hp hJ hl using hJ N
  let θ (j : J) := (x j).1.h
  obtain ⟨A, o, q, a⟩ := hp.1, hp.2, J.erase_subset P₀, fun j : J ↦ hp.3 _ j.2
  have Q {y hy I} (_ : ∀ j, ↑j ∉ I → y j = (1 : PadicAlgCl ℓ) := by simp +contextual [t]) :
      IsFromU1 (placesDividing E ℓ) I (pointChar θ y hy) := by
    choose φ e b d using (a · |>.exists_ideleChar)
    use (LocallyConstant.unflip (⟨θ ·, (a _).isLocallyConstant⟩)).2.comp
      (pointChar (Pi.evalMonoidHom _) y hy), pointChar φ y hy, by simp [e], fun u h k ↦
      prod_eq_one _ fun j ↦ by by_cases j.1 ∈ I <;> simp +contextual [*], (by simp [θ, d _ · · ·])
  have U {I} : I ⊆ J → IsAuxiliary S₀ I := by clear * - A; grind
  have K {k} I (v : J) s := ((hf k).3 I v · (U s) · · _ _ (a v).3 (a v).4)
  choose O' hN hk hO hm V hV using (hN.and (hk.and (.and (Ici_mem_atTop O) (.and (.all fun p :
    (κ × T) × J × ℤˣ ↦ eventually_mem (norm_eq_one_of_continuous ((hf p.1.1).1 p.1.2) ((x
    p.2.1).1.φ ^ p.2.2.1)).le) (.all fun p : κ × Set.Iic J ↦ (
    let ⟨_, _, g, c, a, b⟩ := (hf p.1).2 _ (U p.2.2); .mono (.all (eventually_mem <| a ·)) fun O H ↦
    ⟨∑ i, C ⟨_, H i⟩ * ∏ j, X j ^ (θ j (g i)).toAdd.val, by simp [b]⟩ : ∀ᶠ O : CoeffRing ℓ in _,
    ∃ F, ∀ {y} hy, (eval y F : O.1).1 = val p.1 p.2 (pointChar θ (y ·) hy))))))).exists
  let e := (inclusion hO).1
  have r i := hp.length_le_of_drop_ties i (by simp [reduceModPow,
    (hρ i).2 · <| ·.imp fun _ ↦ by gcongr]) k l fun _ ↦ id
  let t (s : ι ⊕ κ) (j : J) := ite (↑j = P₀) 1 (s.elim (e ∘ (x j).2) 0)
  choose G g g' using fun i ↦ exists_sharp_fitting_poly (.id _) _ (a · |>.isLocallyConstant)
    (hρ i).1 (L i ∪ {.single (γ i) 1} ∪ tieRelations (J.erase P₀) x i) _
  -- First along a line.
  choose u f₃ p s using hk (Fin 1) (J × ι × Bool ⊕ _) le_rfl ((fun (v, i, b) ↦ ((ρ i (idOrConjInv b
    (x v).1.φ)⁻¹).map e).charpoly) ⊕ᵥ (.X - .C ⟨_, hm ·⟩)) (fun s ↦ eval₂ C (fun j ↦ 1 + C (t s.1 j)
    * (X 0 - 1)) (s.1.elim (.map e ∘ G) (V ⟨·, {P₀}, by simpa⟩))) 1 (by simp [↓charpoly_monic,
    Polynomial.Monic]) (by simp [↓sum_prod_type]; grw [hJ]) (by simp) (by
    rintro ⟨i | k', _⟩ <;> simp [← eval_assoc, congrFun W, hV]
    · grw [← hβ, ← hl]
      convert normLength_mono ((g i).trans (r i _ _ (one_pow _) {P₀} (idOrConjInv ·.2 z) (by simpa)
        (by simp) (by simpa using! hp.5.2 i))) <;> simp [e, eval₂_eq', eval_eq' _ (G i),
        sum_prod_type, mapRel.eq_def, twistAtPoint, funext_iff] <;> clear * - o <;> refine ?u
      ext; simp [tieRelations]; grind
    convert! K ∅ ⟨_, o⟩ (by simpa) nofun 1 ⟨.const _, 1, by simp⟩ c (by
      simpa [ellVal_le_iff, dist_eq_norm'] using hp.5.1 k')
    ext; simp)
  choose F f ϕ using fun i ↦ exists_sharp_fitting_poly e _ (a · |>.isLocallyConstant) (hρ i).1 ..
  simp [← eval_assoc, Function.comp_def] at f₃ p
  -- Then to common roots of unity.
  choose ζ f hζ w using hN J (Set.Icc 1 m) (by simpa) _ (·.1.elim F (V ⟨·, J, by simp⟩)) _
    (Polynomial.monic_X_pow_sub_C 1 <| ne_of_gt ·.2.1) (by simp [-map_one]; rfl) (fun s j ↦
    (dvd_one_add_mul_pow_sub_one (t s.1 j) p 0 .refl).1) (by
    rintro ⟨i | k', _⟩ <;> simp
    · grw (transparency := default) [← normLength_addVal, (f i).trans (r i _ e p _ _ q (by simp)
        fun _ ↦ rfl), g' i _ e, map_add, normLength_addVal, f₃.1, map_sum, sum_le_sum fun z _ ↦
        normLength_addVal _ ▸ (ellVal_le_ellVal ((dvd_iff_norm_le ..).1 ⟨det _, by
          erw [eval_charpoly, ← det_mul, sub_one_mul]; congr
          simp [← Matrix.map_mul, ← map_mul, smul_one_eq_diagonal]⟩)).trans
        (s 0 (.inl (⟨_, q z.1.2⟩, i, z.2))), ← hJ]
      simp; gcongr; norm_num
    have y j : (1 + t (.inr k') j * (u 0 - 1)).1 ^ ℓ ^ N = 1 := mod_cast l.dest.choose_spec ▸ by
      simp [pow_add, pow_mul, t, add_ite, *]
    grw [← f₃.2, hV _ y, hV _ y, ← hJ, ← q,
      ← @Finset.induction_on' _ (fun I ↦ ellVal (val k' (insert
      P₀ I) (pointChar θ _ y)) ≤ _ + #I * 8 * _) _ _ (by simp) fun v I a b w i ↦ ?_, insert_erase o]
    lift v to J using q a
    simp at a
    grw [I.insert_comm, K _ v (by grw [b]; simp [*]) (by simp [*]) _ Q δ fun z t ↦ (ellVal_le_ellVal
      ((hp.pointChar_idOrConjInv y v true).2 a ▸ by fin_cases t <;> simp [t,
      (isUnit_iff_norm_eq_one _).1 (.of_pow_eq_one p out),
      norm_eq_one_of_continuous, (hf _).1, sub_div', inv_eq_one_div, norm_pos_iff.1, norm_sub_rev,
      mul_comm (u 0).1, mul_one_div, -one_div])).trans (s 0 (.inr ((k', z), v, -t))), i]
    simp [w, add_mul, add_assoc])
  replace f s := (f s).trans (.trans_eq (coe_le_coe.2 (by linarith)) congr($W _ + η))
  have hd d j : (ζ j ^ d).1 ^ ℓ ^ N = 1 := mod_cast by simp [pow_right_comm _ d, hζ]
  use J, pointChar θ _ (hd 1), fun d e ↦ ?_
  rw [show _ ^ d = pointChar θ _ (hd d) by ext; simp [← prod_pow, pow_right_comm]]
  exact ⟨(hV .. ▸ f ⟨.inr ·, d, e⟩ :), ⟨A, Q, _, fun v ↦ ⟨(a v).5, map_one _, _, _, (a v).6.2.2⟩,
    (sum_le_card_nsmul _ _ ↑δ fun v _ ↦
    (hp.pointChar_idOrConjInv (hd d) v true).1 ▸ by simpa using w v ⟨d, e⟩).trans
    (by simp; grw [hJ]; norm_cast; bound)⟩, fun i ↦ mem_atTop_sets.2 ⟨O', fun R h ↦ ⟨hO.trans h,
    pointChar θ (inclusion h ∘ ζ ^ d) (Subtype.ext <| hd d ·), by simp, (normLength_mono
    (ϕ i _ (inclusion h).1 _)).trans (by simpa [eval₂_eq', eval_eq'] using f ⟨.inl i, d, e⟩)⟩⟩⟩
end

section
/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

This file: Roots of unity give a tame class; lattices in columns read above ℓ. Local duality bounds
Ribet cocycles' distance from crystalline by the dual lattice's defect. Rows are balanced: local
conditions and mirror scalar within explicit bound. -/

open Lift Polynomial Multiset minpoly Pi Filter Function
variable {P} {D : Data P} {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {n} [Fintype n]

/-- Let M consist of at most N elements of ℚ̄_ℓ, each killed by y^(ℓ^a − 1) − 1 for some 1 ≤ a ≤
r. A class of polynomials over O containing all those vanishing on M is tame
(`Lift.IsTameType`) for r and degree Nr. -/
lemma isTameType_of_roots {N r K M} (b : card M ≤ N) (k : ∀ y ∈ M, ∃ a ∈ Set.Icc 1 r,
  y ^ (ℓ ^ a - 1) = 1) (h : ∀ Q : O[X], (∀ y ∈ M, Q.aeval (y : PadicAlgCl ℓ) = 0) → K Q) :
  Lift.IsTameType ℓ r (N * r) K :=
  have H y c : (minpoly _ y).Monic ∧ (minpoly ℤ_[ℓ] y).natDegree ≤ r := by
    choose f hf hx using k y c
    obtain ⟨a, rfl : wittToQpBar _ = _⟩ := exists_flatFq_root (f := f.toPNat hf.1) _ _ fun _ ↦ hx
    grw [algHom_eq _ wittToQpBar_injective, natDegree_le,
      KummerChart.JumpLattice.finrank_wittFq]; use monic (.of_finite ..), hf.2
  ⟨h _ (k · · |>.elim fun a h ↦ by rw [(Finset.dvd_lcm (mem_Icc.2 h.1)).choose_spec]; simp [pow_mul,
    h]), _, monic_multiset_prod_of_monic _ _ (H · · |>.1), by grw [natDegree_multiset_prod_le,
    sum_le_card_nsmul, ← b] <;> aesop, h _ (by aesop (add simp map_multiset_prod))⟩

variable [PadicIso ℓ] {τ} {u : AbsGal D →* Matrix n n O}

lemma IsColumn.eq_one_of_mem_inertiaAbove {t S R} (h : IsColumn (n := n) D t τ S R) :
  ∀ g ∈ inertiaAbove (placesDividing _ ℓ ∪ placesAboveG D ∪ S)ᶜ, R g = 1 := by grind [IsColumn,
  IsGoodAt, IsPlaceOver.valuation_natCast_eq_one_iff, placesDividing, inertiaAbove]

/-- Let u be a lattice in a column R ∈ 𝓡, and w ∣ ℓ. At w, u has jumps τ and is potentially
crystalline, crystalline unless w ∣ g; if w ∣ g, inertial s is killed by each Q vanishing,
for every R' ∈ 𝓡, at the roots of some polynomial killing s on R'. -/
lemma inClass_of_isLatticeIn {R t S} w {𝓡 : _ → Prop} (h : IsColumn D t τ S R) (m : 𝓡 R) :
  let v := matrixLattice (u.comp (decompGroup _ (placeOver w.1)).subtype)
  let J g := τ (complexEmbOf ((localChart ℓ _ w).e.comp (algebraMap ..)) g)
  IsLatticeIn R u → (∀ g, HasJumps v.ρ (coeffEmb O g) (J g)) ∧ InClass (⨅ _ : ↑w ∈ placesAboveG
    D, ⊥) (fun s Q ↦ w.1 ∈ placesAboveG D ∧ ∀ R, 𝓡 R → ∃ P, PolyKillsAt R (placeOver w.1) s.1 P ∧
    ∀ y, P.IsRoot y → Q.aeval y = 0) (toFinset ∘ J ∘ surjInv coeffEmb_surjective) v := by
  let ⟨⟨_, c⟩, d, z⟩ := h.local_conditions _ (by simp) w.1.isPlaceOver_placeOver
  intro v J ⟨P, hP⟩
  let L := P.toLin.toLinearEquiv
  let F := L.1.restrictScalars _ ∘ₗ O.1.val.toLinearMap.compLeft n
  have hf g x : F (v.ρ g x) = decompRep R _ g (F x) := congr(L $(funext
    (O.1.val.1.map_mulVec _ x))).trans (hP g ▸ by simp [L, F, mul_assoc]; rfl)
  suffices _ from ⟨this,
    .of_jointly_injective le_sup_left (by by_cases ↑w ∈ placesAboveG D <;> simp [*, (z _).2]) _
    (fun _ ↦ .of_forall hf) ?I, by simp [← count_ne_zero, ← this .., surjInv_eq], fun s Q k hs ↦
    (k.2 R m).rec fun _ ⟨a, _⟩ ↦ .of_jointly_injective hs _ (by tauto) ?I le_top (fun _ ↦ ⟨c,
    map_eq_zero_of_roots (eval₂RingHom' _ _ (commute_coefEnd_linearFrob c hs))
    ((((mapClusterPt_one_atTop_pow _).frequently (mem_comap'.1 c.eventually_linearFrob_eq_one)).mono
    (by simpa [← linearFrob_pow c hs ·] using · (map_pow ..) (hs.pow _))).forall_exists_of_atTop 1)
    (a.2 hs).2 (by simpa [eval_map])⟩) rfl fun () _ _ ↦ L.map_smul ..⟩
  any_goals intro g _; rw [coeffEmb, ← jump_baseChange ⟨F.1, fun _ _ ↦ L.map_smul
    ..⟩ (basisFun ..) ((basisFun ..).map L) (fun _ ↦ congr(L $(by ext; simp [apply_ite])))
    (.of_forall hf), ← @d _ _ g]
  all_goals simp [F, v, J, funext_iff]; tauto

open DistribSMul LinearMap NeZero Submodule crysCocycles Ideal.Quotient Matrix.Module

/-- Let j be an open embedding and the lattices u_x∘η, L = ρ∘η lie in `Lift.InClass` F K U. The
cocycles `obeyingCocycles` mod ℓ^m, modulo those obeying along η the relations of Z_f(L), are
no longer than Z_f(L^∨(1)) modulo `Lift.cupOrthogonal` of this class. -/
lemma relLength_obeyingCocycles_le {ℓ} [ThePrime ℓ] {X n R Γ G d : Type} [Fintype X] [Fintype n]
  [CommRing R] [PadicIntegerRing R ℓ] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group G] [Fintype d] [𝒥 : OverGp Γ ℓ] (hj : Topology.IsOpenEmbedding 𝒥.toGp) {η : Γ →* _} {u :
  X → G →* Matrix n n R} {ρ : G →* Matrix d d R} {F K U} (hZ : ∀ x, InClass F K U (matrixLattice ((u
  x).comp η))) m : let L := matrixLattice (ρ.comp η); InClass F K U L → relLength (obeyingCocycles u
    ρ (ℓ ^ m)) ((obeying (relationsOn (crysCocycles L.ρ)) _).comap (.funLeft R _ η)) ≤
    relLength (crysCocycles L.tateDual.ρ) (cupOrthogonal (InClass F K U) _) := by
  intro L H
  let τ := (mkQ (R ∙ (ℓ : R) ^ m)).compLeft d
  obtain ⟨⟨f, b⟩, o : Function.Surjective τ, ⟨⟩⟩ := exists_perfect_pairing (L := L),
    mk_surjective.comp_left, PSigma.mk _ (discreteTopology_bot (QuotSpan (ℓ ^ m : R)))
  have hτ : τ.toAddMonoidHom.ker = pPowMultiples L m := by ext; simp [τ, L, Algebra.smul_def,
              funext_iff, eq_zero_iff_mem, mem_span_singleton, Classical.skolem, mul_comm]
  have e g x : τ (L.ρ g x) = ρ (η g) • τ x := by ext; apply map_sum (mkQ _)
  have C y := _root_.funext (nsmul_quot_eq_zero dvd_rfl <| τ y ·)
  grw [relLength_comap, relLength_mono le_rfl (Submodule.map_le_iff_le_comap (f := τ.compLeft Γ).2
    (comp_mem_obeying ·))]
  refine (length_le_of_card_dvd_or_le ℓ ∘ .inl : (toAddSubgroup _).relIndex (toAddSubgroup _) ∣
    (toAddSubgroup _).relIndex (toAddSubgroup _) → relLength .. ≤
    relLength ..) (H.isPotCrys.relIndex_dvd_of_orthogonal hj H.dual.isPotCrys
    (.ofBijective _ b) (by simp) ⟨by simp, by simp⟩ e o hτ (V := .of (actionRep _ _ (ρ.comp η))
    (by simpa [o.forall, e, continuous_prod_of_discrete_right] using fun x ↦ (continuous_comp hj
    H.isPotCrys τ C (coboundary_mem x)).add_const (τ x))) |> (forall₂_and.1 fun s hs ↦ ?_).elim)
  choose y hY t q a ha E using show ∃ y, InClass F K U y ∧ ∃ t : y →ₗ[R] _, (∀ g x, t (y.ρ g x) =
    ρ (η g) • t x) ∧ s ∈ (crysCocycles y.ρ).map (t.compLeft Γ) from hs.elim (by tauto) fun ⟨w, hw,
    s⟩ ↦ by
    choose k Y i hx using obeyingCocycles.exists_graph_subrepresentation _ _ hw
    have := i.moduleIsTorsionFree (R := R) _ (by simp)
    use ⟨_, Y.toRepresentation.comp η⟩, .of_jointly_injective (hZ <| Prod.fst ·) (fun a ↦ ⟨⟨(·.1.1
      a.1 · a.2), by tauto⟩, by tauto⟩) (by tauto) fun _ h ↦ i (by ext; apply congrFun (h (_, _))),
      domRestrict (snd ..) _, by tauto, (⟨_, hx · 0⟩) ∘ η, of_smul (a := (ℓ ^ m) ^ k) out
      ((_root_.funext fun _ ↦ i (by ext; simp [mul_sub, Subrepresentation.toRepresentation,
      ← algebraMap_smul R])).subst (coboundary_mem ⟨_, hx 1 1⟩)), s
  -- the form given by a lift `p` of the map to `L / ℓ^m`, and its coboundary divided by `ℓ^m`
  choose p P using Module.projective_lifting_property τ t o; subst P E
  simp at q
  let ψ p : (y.tensor L.tateDual).tateDual := TensorProduct.lift (dualMap p).flip
  have E g : (?_ : ℤ_[ℓ]) • ψ ?_ = GalLattice.ρ _ g (ψ p) - ψ p := by
    ext x l; simpa [ψ] using congr(l $((y.ρ.linHom L.ρ g p - p).codRestrictOfInjective_comp_apply
      (toLinearMap ..) (smul_right_injective _ out) (fun _ ↦ hτ.le (by simp [e, ← q])) x))
  exact ⟨⟨continuous_comp hj hY.isPotCrys (τ ∘ₗ p).toAddMonoidHom (C <| p ·) ha, by simp [*,
    apply_mul ha]⟩, _, rfl, fun _ ↦ (· y ⟨m, ψ p, f,
    ⟨_, of_smul out (_root_.funext E ▸ coboundary_mem _)⟩, mod_cast E⟩ hY a ha)⟩

open Finset Fintype IsLocalRing Matrix
variable {P : _} {D : Data P} {ℓ : _} [ThePrime ℓ] [PadicIso ℓ] {n : Type} [Fintype n]

/-- For a row R of rank n, a chosen place w off ℓ and all large O, some lattice u is balanced
(`IsBalanced`) for Z_f above ℓ, and β plus v(det(u(σ) − 1)) for σ = σ_w, σ_w^{−c}
(σ_w a tame generator at w) has
normalised length ≤ 10fn·cr_ℓ. -/
lemma IsRow.eventually_isBalanced {t J R w} (r : IsRow D t J R) (hG : D.IsChosen w) (hℓ :
  w ∈ placesAboveG D \ placesDividing _ ℓ) M (h := (Finset.finite_toSet _).subset
  (placesDividing_union_subset_badPlaces D ℓ)) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ u :
  _ →* Matrix n n O, ∃ γ β, IsLatticeIn R u ∧ O.normLength (β + ∑ b, IsDiscreteValuationRing.addVal
  _ (u (idOrConjInv b w.isPlaceOver_placeOver.tameGenerator) - 1).det)
  ≤ 10 * D.f * Fintype.card n * crudeUnit ℓ D ∧ IsBalanced ℓ h.toFinset u (crysRels u) γ β M := by
  filter_upwards [r.span_and_scalar, eventually_exists_isLatticeIn r.continuous] with O hs ⟨u, hu⟩
  obtain ⟨⟨hs, g, l, α, c, hg⟩, ⟨Φ, I, f, d⟩, ⟨i⟩, S, ⟨⟨a, b⟩⟩, h2, g₀, o, y, q, hy⟩ := hs u hu,
    hu.exists_algHom, card_pos_iff.1 r.2.1.1, Set.union_sdiff_left ▸ h.sdiff, r.2,
    sum_mono r.card_neg_le, r.5
  cases by simpa [q] using congr($(hu.choose_spec g₀) i i)
  replace q : u _ = u _ .. • 1 := I (by simpa [f])
  have Y j h := (O.isUnit_iff_norm_eq_one (_ ^ j - 1)).2 (by simpa using hy 0 j h)
  choose! γ m Z F G H using (r.inertia_above_g · · (FinPlace.isPlaceOver_placeOver _))
  simp_rw [← f, ← map_one Φ, ← map_sub, d, ← S.mem_toFinset] at *
  choose L K using (inClass_of_isLatticeIn · r.1 r hu)
  have C {g y} (e : u g = y • 1) : IsUnit y ∧ u (conjGal g)⁻¹ = (cycInv ℓ _ O g⁻¹ ^ (t - 1) * y) •
    1 := ⟨by simpa [e, Nat.ne_of_gt a] using isUnits_det_units (u.toHomUnits g), (by exact fun _ _ ↦
    ext_iff_trace_mul_left.2 ∘ DFunLike.ext_iff.1 : (traceLinearMap .. ∘ₗ mulRight O ·).Injective)
    (ext_on_range hs fun k ↦ by ext; simp [cycInv,
    e, by simpa [↓← hu.trace_eq] using
    And.intro (r.trace_conj (conjGal k * g⁻¹)) (r.trace_conj (conjGal k))]; ring)⟩
  refine ⟨u, _, _, hu, ?_, (isOpen_discrete · |>.preimage ((hu.continuous r.continuous).matrix_map
    continuous_quot_mk)), fun _ ↦ hu.eq_one ∘ r.eq_one_of_mem_inertiaAbove _ ∘ by simp, hs,
    ⟨by simpa, _, ⟨by simp [C q, cycInv, cycChar_eq_one_of_mem_inertiaAbove (o.imp fun _ ↦
    .imp_left (·.2))], q⟩, by simpa [sq, mul_self_sub_one] using Y 2⟩, orderOf_le_card.trans_lt' (by
    simpa using (Y _ ⟨((C q).1.map (residue O)).isOfFinOrder.orderOf_pos, ·⟩ |>.map (residue O))),
    fun x b ↦ Quotient.induction_on_pi b fun b ↦ by simpa [obeying_crysRels, entrywise] using! (fun
    v _ ↦ comp_mem_obeying (Z := ZfAt _ u) _ (crysCocycles.coboundary_mem b)), _, _, _,
    ⟨hg, (C hg).2⟩, fun x hx ↦ by
    grw [iInf_le _ ⟨_, FinPlace.isPlaceOver_placeOver _⟩,
      (by simp [← Finset.coe_inj] : h.toFinset = (placesDividing _
      ℓ).toFinset ∪ S.toFinset), sum_union (by simp [Finset.disjoint_right]), ← sum_set_coe]
    refine .trans (add_le_add_three (sum_le_sum fun v _ ↦ .trans (length_mono (by
     rintro _ ⟨_, h, ⟨⟩⟩; simp [mem_selmerModule_iff, obeying_crysRels] at h; tauto))
      (length_obeying_relationsOn_le (crysCocycles.fg (K _).isPotCrys) i)) (sum_le_sum fun v
      c ↦ have p := v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 (S.mem_toFinset.1 c).2
      length_localCocycles_le (nsmul_quot_eq_zero hx) v.isPlaceOver_placeOver (hu.eq_one ∘ G v c ·)
        (((r.local_conditions v (·.1) v.isPlaceOver_placeOver).1.1
        p).mono fun _ ↦ (hu.eq_one ∘ ·)) (γ v) (by simp [*])) le_rfl) ?_
    simp_rw [← sum_mul, finrank_crysCocycles_eq_add_neg_jumps (localChart ..).inducesPlace.2
      (K _).isPotCrys (L _), ← Nat.cast_sum, sum_add_distrib]
    simp [NumberField.Embeddings.card, finrank_eq_two_mul_card_infinitePlace, ← two_mul, mul_assoc,
      star_involutive.bijective.sum_comp (J · |>.countP (· < 0))] at h2
    grw [sum_complexEmbOf_le, h2, length_ker_le_addVal_det, ← add_assoc, add_assoc]
    gcongr; simp [Finset.disjoint_right]; ring; rfl⟩
  simp [-univ_bool, ← Z w hℓ hG]
  grw [H w hℓ, sum_le_sum (by exact (H · · true)), sum_const, card_le_of_subset_placesAboveG,
    ellVal_le_ellVal, ellVal_le_crudeUnit D ℓ l ⟨mul_pos a (t - 1).succ_pos,
    mul_le_mul' b (D.t_odd.rec (by omega))⟩] <;> simp [← add_mul, cycInv, c, ← mul_assoc, pow_succ',
    ← one_sub_mul, pow_mul, norm_sub_rev, (O.isUnit_iff_norm_eq_one _).1 (C hg).1]
  gcongr; norm_cast; nlinarith [D.f.pos_of_neZero]
end
