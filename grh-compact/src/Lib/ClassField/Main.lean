import Lib.ClassField.PrimeError
import Lib.ClassField.ZeroFreeTwist
import New.Weil.IndexTypes
import Statements
import Lib.PadicHodge.LongForms

-- part: New.Endgame.OneSidedCriterion
section
/-! A good second scale in every long window. If E and E' are O(e^v) and their transforms
∫E(v)e^((1−s)v)dv continue with no pole in Re s ≥ 1, then for large t and any X in [0, e^t] some u
in [t, t²] has E(u) − X E'(u) ≤ e^(−t), which replaces a pointwise prime number theorem in
progressions when the second scale of (⋆) is chosen. Localised one-sided bounds and sign changes for
prime-sum errors are known. Related work: Pintz, On the sign changes of π(x) − li(x), 1976–78;
Kaczorowski, On sign-changes in the remainder-term of the prime-number formula, 1984.

One-sided bound for non-split primes gives a zero-free half-plane. If β > 1/2 and, for every prime d
of a unit class mod M forcing d ≡ 7 mod 8, the normalised error at x in the weighted count of
primes ≡ 1 mod M not split in Q(√−d) is eventually ≤ x^(β−1), then L(s,χ) has no zero in Re s > β
for χ mod M, and this takes (⋆) to GRH. It is known that a one-sided bound for a weighted sum over
primes 1 mod q gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On
variants of Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative
Number Theory I, §15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.

This file: One-sided bound gives a zero-free half-plane; small value in every long window. -/

open Complex Filter Nat Real Set MeasureTheory Topology

/-- One-sided criterion: let β > 1/2 and a be a unit mod M such that every prime d ≡ a is ≡ 7 mod 8,
prime to M, with R_M(x) ≤ x^{β−1} for large x (`primeError`). Then `entireL` χ has no zero in Re
s > β for any χ mod M.

One-sided bound for non-split primes gives a zero-free half-plane. -/
lemma entireL_ne_zero_of_primeError_le {M} [NeZero M] {a : ZMod M} {β} (hβ : 1 / 2 < β)
  (ha : IsUnit a) (h : ∀ d : Primes, d = a → (d.1 % 8 = 7 ∧ M.Coprime d) ∧ ∀ᶠ x in atTop, primeError
  d M x ≤ x ^ (β - 1)) ρ (hρ : β < ρ.re) (χ : DirichletCharacter ℂ M) : entireL χ ρ ≠ 0 := by
  let ⟨d, e, hZ⟩ := exists_entireL_quadTwist_ne_zero |ρ.im| hβ ha (by grind)
  use by_cases (entireL_ne_zero χ) (flip ?_ (((h d e).1.elim isPolar_primeError).landau (by bound)
    (le_total · 1 |>.rec ?_ ?_) (.mono (tendsto_exp_atTop (h d e).2) (by simp [exp_mul, mul_comm]))
    hρ)) <;> simp +contextual (maxDischargeDepth := 3) [le_of_lt, div_re,
    (tendsto_sub_mul_logDeriv_entireL _).1.2, *, normSq, entireL_ne_zero, (hβ.trans hρ).trans',
    ← cast_sum, tendsto_sub_mul_logDeriv_entireL, ne_of_apply_ne re, ne_of_gt]; bound

/-- For polar E, all R > 3 close to 3 and then all large t: |E(v)| ≤ t e^v for v ≥ 0, and for
every k the function v^k e^{−3v} E(v) is integrable on (0, ∞) with integral of modulus ≤ k!
t / R^k. -/
lemma IsPolar.eventually_moment_le {E r} (h : IsPolar E r) : ∀ᶠ R in 𝓝[>] 3, ∀ᶠ t in atTop,
    (∀ v ≥ 0, |E v| ≤ t * v.exp) ∧ ∀ k, let F v := v ^ k * (-3 * v).exp * E v
  IntegrableOn F (Ioi 0) ∧ |∫ v in Ioi 0, F v| ≤ k ! * t / R ^ k := h.elim fun m ⟨C, Φ, _, hC, e,
      A, _⟩ ↦ ((isCompact_closedBall (1 + 3) 3).exists_thickening_subset_open (isOpen_analyticAt ..)
      (A · <| by simpa using (re_le_norm _).trans ·)).elim fun ε ⟨o, D⟩ ↦ by
  filter_upwards [Ioo_mem_nhdsGT (by bound : 3 < ε + 3)] with R ⟨a, b⟩
  simp [o] at D
  -- differentiation under the integral sign
  have J k : ∀ s, 2 < re s → let F v := (-v) ^ k * E v * ((1 - s) * v).exp
    IntegrableOn F (Ioi 0) ∧ iteratedDeriv k Φ s = ∫ v in Ioi 0, F v := by
    induction' k with k ih <;> intro s hs; simp [integrableOn_laplace_of_abs_le m hC, *]
    obtain ⟨⟨ε, o, q⟩, n⟩ := exists_pos_mul_lt (sub_pos.2 hs) 2, (isOpen_re_gt _).mem_nhds hs
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le ((isOpen_re_gt _).mem_nhds
      (lt_tsub_iff_right.1 q)) (.mono n (ih · · |>.1.1)) (ih s hs).1 (by fun_prop) (.mono
      (self_mem_ae_restrict (by simp)) fun v u z j ↦ ?_) ((ih (ε + 2) (by simpa)).1.norm.div_const
      ε) (.of_forall fun v z _ ↦ ((hasDerivAt_mul_const _).cexp.const_mul _).comp_const_sub ..)
    · simpa [iteratedDeriv_succ, pow_succ, ← mul_assoc, mul_right_comm] using! this.imp id
        (·.congr_of_eventuallyEq (.mono n (ih · · |>.2)) |>.deriv)
    simp [abs_of_pos, le_div_iff₀, mul_assoc, *]
    grw [← j.out, lt_add_one (v * ε), add_one_le_exp, ← Real.exp_add]; bound
  filter_upwards [mem_atTop C, mem_atTop (tsum _)] with t c d
  use (by grw [hC · ·, c]), fun k ↦ (J k 4 (by norm_num)).rec fun i j ↦ (?_ : _ ∧ _)
  grw [← d,
    ← (summable_taylor_of_removable (1 + 3 + R) D (by simp; grind)).norm.le_tsum k (by bound)]
  norm_num [j, neg_pow (ofReal _), mul_assoc, integrable_const_mul_iff, IntegrableOn,
    mul_comm (ofReal _)] at i ⊢
  use mod_cast i.re, mod_cast by simp [field]; bound

/-- If E and E' are polar (`IsPolar`), then for all large t and every X in [0, e^t] there is u in
[t, t²] with E(u) − X E'(u) ≤ e^{−t}.

A good second scale in every long window. -/
lemma IsPolar.exists_window_sub_mul_le {E r E' r'} (h : IsPolar E r) (h' :
  IsPolar E' r') : ∀ᶠ t in atTop, ∀ X ∈ Icc 0
  t.exp, ∃ u ∈ Icc t (t ^ 2), E u - X * E' u ≤ (-t).exp := (h.eventually_moment_le.and
  (h'.eventually_moment_le.and (Ioo_mem_nhdsGT (lt_add_one _)))).exists.elim fun R ⟨c, d, p, q⟩ ↦ by
  simp_rw [IntegrableOn, abs_le, forall_and] at *
  filter_upwards [c, d, mem_atTop (99 / (R.log - .log 3)), mem_atTop 9]
    with t ⟨c, _, a⟩ ⟨d, _, b⟩ u _ X ⟨_, _⟩
  let k := ⌈t ^ 2 / 9⌉₊
  obtain ⟨w, I, K : t + t * X + 1 ≤ t.exp * t.exp⟩ := three_pos.trans p,
    mod_cast fun R : ℝ ↦ (@laplace_pow R · k), by nlinarith [t.add_one_le_exp]
  have J R o := Integrable.of_integral_ne_zero ((I R o).trans_ne (by simp; grind))
  by_contra! N
  -- `E - X E' - e^{-t}` plus two exponentials, which dominate outside the window, is `≥ 0`
  have : 0 ≤ ∫ v in Ioi 0, v ^ k * ((-R * v).exp * (7 * t).exp + (-1 * v).exp *
    (2 * t - t ^ 2).exp + (-3 * v).exp * (E v - _ * X - (-t).exp)) := setIntegral_nonneg
    (by simp) fun v (l : 0 < v) ↦ mul_nonneg (by bound) (by_cases (by bound [N v ·]) fun x ↦ ?_)
  -- but in the mean with `k ≈ t²/9` three terms are each at most a third of the negative one
  · simp (disch := first | fun_prop (disch := simp [w]) | simp [*]) [mul_add, mul_sub, ← mul_assoc,
      integral_add, integral_sub, I, -neg_mul] at this
    grw [a.2, ← b.1, (by ring : _ - _ * X = k ! * (t + t * X) / R ^ k), lt_add_one (t + _), K,
      add_sub, sub_pos] at this
    apply this.not_ge ((add_le_add_three ..).trans_eq (add_thirds _)) <;>
    simp (disch := positivity) [← log_le_log_iff] <;> nlinarith [log_three_lt_d9,
      abs_le.1 (abs_sub_ceil_le (by bound : 0 ≤ t ^ 2 / 9)), (div_le_iff₀ (by bound)).1 u]
  grw [← neg_le_iff_add_nonneg, ← c.1, d.2, (by grind : -t ≤ v), (by ring : -_ = (-3 * v).exp *
    v.exp * (t + t * X + 1)), K, ← max_le_add_of_nonneg] <;> simp [← Real.exp_add, exp_nonneg, l.le]
  contrapose! x; use ?_ <;> nlinarith
end

-- part: New.Data.DataExist
section
/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Known result: Behrend's construction for several equations at once. Here all ratios up to a given
bound are avoided at once, in a coset of a cyclic group seen through a homomorphism, with the
explicit count of points on a sphere. Source: Shapira, Behrend-type constructions for sets of linear
equations, Acta Arith. 2006, Thm 1 (after Behrend, PNAS 32, 1946).

This file: Admissible data exist for large x; Behrend sets and class-group pigeonhole as inputs. -/


open Finset Behrend Real Filter NumberField ClassGroup NeZero QuadField

/-- Behrend: let φ : G → H map commutative groups, L > 0, (LM)ⁿ ≤ ord φ(g). Some finite T ⊆
{cgᵉ} has |T| ≥ Mⁿ/(nM²), and σ, σy, σz ∈ T, φ(y)ʲ = φ(z)ⁱ, 0 < i < j ≤ L force φ(y) = 1.

Known result: Behrend's construction for several equations at once. -/
lemma exists_three_term_free {G H} [CommGroup G] [CommGroup H] (φ : G →* H) c g (n M L : ℕ)
    (hL : 0 < L) (h : (L * M) ^ n ≤ orderOf (φ g)) : ∃ T, (∀ σ ∈ T, ∃ e, σ = c * g ^ e) ∧
    (M ^ n / (n * M ^ 2) : ℝ) ≤ #T ∧ ∀ i j, 0 < i → i < j → j ≤ L → ∀ σ ∈ T, ∀ τ ∈ T, ∀ ρ ∈ T, φ
    (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1 := (exists_large_sphere n M).elim fun k _ ↦ by
  have := pow_injOn_Iio_orderOf.comp map_injOn fun _ k ↦ h.trans' (finFunctionFinEquiv (⟨_, k ·⟩)).2
  use image (c * g ^ map (L * M) ·) (sphere n M k)
  rw [card_image_iff.2 fun _ a _ b _ ↦ this.mono (fun v k ↦ show ∀ i, _ from fun i ↦ ?_)
    a b ?_] <;> simp_all
    [← map_pow, sphere, Behrend.box, -map_apply, ↓forall_mem_image] <;> try nlinarith [k.1 i]
  intro i j _ o _ u hu _ v hv _ w hw _ H
  obtain ⟨a, ha, rfl⟩ := lt_iff_exists_add.1 o
  have e := @this ((i + a) • v) (by simp; nlinarith [hv ·]) (i • w + a • u)
    (by simp; nlinarith [hu ·, hw ‹_›]) (by simpa [pow_add, pow_mul', ↓div_pow,
    div_eq_iff_eq_mul, ← mul_assoc, -map_apply, -nsmul_eq_mul] using H)
  simp [by simpa [← mul_sum, *, ← add_mul, ha.ne', mul_left_comm i] using show
    ∑ l, (i + a) * (a * Int.natAbs (u l - v l) ^ 2 + i * v l ^ 2) =
    ∑ l, i * (i * w l ^ 2 + a * u l ^ 2) by simp [funext_iff] at e; zify at *; grind]

/-- Pigeonhole in the class group: among h + 1 pairs of prime ideals (I_i, J_i) of a number
field of class number h, with every I_i J_i principal, there are i ≠ j with I_i J_j
principal. -/
lemma exists_mul_principal {K} [Field K] [NumberField K] {I J : Fin (classNumber K + 1) → FinPlace
  K} (H : ∀ i, ((I i).1 * (J i).1).IsPrincipal) : ∃ i j, i ≠ j ∧ ((I i).1 * (J j).1).IsPrincipal :=
  let c (v : FinPlace K) := mk0 ⟨_, mem_nonZeroDivisors_of_ne_zero v.3⟩
  have e v w : _ ↔ c v * c w = 1 := by rw [← map_mul, mk0_eq_one_iff]
  by simp_all; grind [Fintype.exists_ne_map_eq_of_card_lt (c ∘ I) (card_fin _).ge]

/-- Let 0 < ε < 1/100. For all large x there are admissible data with scale x, log x₁ = x^{ε/6}
≥ (10⁶ log x)², log log b = ε log x, and at least 3^c 2^s / log b thick places. -/
lemma exists_data P {ε : ℝ} (e0 : 0 < ε / 6) (e1 : ε < 1 / 100) : ∀ᶠ x in atTop, ∃ D : Data P,
    D.x = x ∧ log D.x₁ = x ^ (ε / 6) ∧ (1e6 * log x) ^ 2 ≤ log D.x₁ ∧
    log (log D.b) = ε * log x ∧ towerDeg D.s / log D.b ≤ #D.thick := by
  have ⟨n, h⟩ := exists_nat_gt (99 * P.N₀ * P.d / (ε / 6) ⊔ 6)
  have E (k : ℕ) := tendsto_exp_mul_div_rpow_atTop k _ e0
  have ev k c := E k (mem_atTop c)
  rw [← map_exp_atTop, eventually_map]
  filter_upwards [E 0 (exists_prime_modEq_one_log_mem (P.N₀ * P.d) n (by grind [Parameters])),
    ev 2 1e12, ev (n + 1)
    ((P.N₀ * 8019 + 2) * 10368 ^ n), mem_atTop 1, ev 0 (2 * classNumber P.K + 1e6), Ioi_mem_atTop 0,
    mem_atTop 2, ev 0 (1e12 * P.c).exp, ev 1 (8019 * 2 ^ n * n)] with x hg h3 hL lx h5 x0 _ hf hC
  simp_all [↓rpow_natCast, le_div_iff₀, div_lt_iff₀, ← exp_mul, mul_comm x]
  have N (x y : ℝ) (e : 1 ≤ x := by simp; bound) (h : 1 < y := by simp) := exists_nat_pow_near e h
  obtain ⟨⟨h, n0⟩, ⟨o, m1, m2⟩, e, r1, r2⟩ := h, N (x / 2).exp 2, N (5 * x).exp 3
  let s := (o + 1) * 22
  have s8 : s ≤ 32 * x := by simp [s, pow_le_iff_le_log, exp_pos] at *; nlinarith [log_two_gt_d9]
  have W0 := exp_pos (ε / 6 * x)
  have ⟨k, k1, k2⟩ := N (2 ^ s / _) (2 ^ n) ((one_le_div W0).2 (by
    grw [pow_mul, ← le_self_pow₀, ← m2, e1] <;> bound)) (mod_cast by grind)
  set W := exp (_ * x)
  have Y i j (h : i ≤ j := by lia) : W ^ i ≤ W ^ j := by bound
  have s6 := @pow_le_of_le_log ((P.N₀ * P.d) ^ ((s + 6) * 2)) W n W0 (by
    grw [log_pow, log_exp, ← mul_assoc, ← h, log_le_self] <;> simp [field]; grind)
  have s5 : 2 ^ s ≤ W ^ n := s6.trans' (mod_cast by gcongr <;> nlinarith only [P.lt_d, pos P.N₀])
  obtain ⟨hg, w2⟩ := hg _ (by lia) s6, Y 2 6
  simp [pow_mul, field] at hg k2
  choose i1 p hp hm l u using fun i : Fin (classNumber P.K + 1) ↦ have : 0 ≤ i * W ∧ (i + 1) * W * 2
    ≤ W ^ 2 := ⟨by bound, by grw [i.is_le]; nlinarith only [h5]⟩; And.intro this (hg (10 * W ^ 6
    + 2 * i * W) (by bound) (by nlinarith only [this, Y 7 n, w2, h5]))
  have hN i := (hm i).of_dvd (P.N₁_mul_d_dvd_M_omega.pow out)
  choose I J nI nJ eJ using fun i ↦ have := Fact.mk (hp i); (FinPlace.exists_natCast_mem P.K
      (p i)).imp fun w h ↦ (prime_inert_or_eq_mul w h).imp fun _ ↦
      (·.2.resolve_left (by simp [(q_eq_iff_legendreSym_ne_neg_one w h).2, sq,
      P.chiK_eq_one_of_modEq_one (hN i), (hp i).ne_one]))
  have ⟨i, j, ne, α, hα⟩ := exists_mul_principal (⟨_, eJ · |>.symm⟩)
  let M := P.N₀ * 3 ^ (Nat.log 3 s + 5)
  have := @Parameters.placeClass_placeOfInt P s (M + 1) (mod_cast by simp [M])
  have ⟨T, t1, t2, t⟩ := exists_three_term_free (P.placeClass P.two_pow_dvd_N₁) (P.placeOfInt s
    (-1)) (P.placeOfInt s (M + 1)) n (2 ^ k) (324 * s) (by lia) (le_of_mul_le_mul_left (.trans (by
    unfold M; norm_cast; grw [pow_add, Nat.pow_log_le_add_one]; rify
    grw [← (le_div_iff₀ W0).1 k1, lx, ← hL, s8, s8]; ring; rfl)
    (@two_pow_le_of_pow_eq_one (M + 1) (mod_cast by
    simp) _ s (orderOf_pos _) (this ▸ Units.ext_iff.1 (pow_orderOf_eq_one _)))) (pos _))
  refine ⟨⟨_, W ^ 6, W, s, _, _, s8, T, p ∘ ![i, j], α, ?_, ?_, ?_, ⟨o, rfl, rfl⟩, ⟨e, rfl⟩,
    fun _ k ↦ (by cases t1 · ·; simp [*, P.placeClass_placeOfInt isCoprime_one_left.neg_left,
    Units.ext_iff, (ZMod.natCast_eq_zero_iff M _).2 k]), t, ?_, ?_, fun _ ↦ (hm _).symm.dvd',
    (Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    rify; grw [← log_lt_log_iff, u, ← l] <;> simp [(hp _).pos]; bound).injective.comp
    (by simpa), by
    simp [pow_le_iff_le_log, le_pow_iff_log_le, (hp _).pos, exp_pos]; grind, ?_, ?_⟩, ?_⟩ <;>
    simp [m2.le, r2.le, ← absNorm_span_eq_mul_star, ← hα, nI, nJ, hp, hN]
  simp [W]; and_intros <;> nlinarith only [e0, e1, w2, lx, h3, hf, h5]
  iterate 2 simpa [pow_succ']
  grw [← le_sqrt_of_sq_le w2]; intros
  apply hg <;> grind
  use by bound, by simp [W, field]
  grw [← t2, towerDeg, pow_add, Nat.pow_log_le_add_one]; simp; grw [k2, s8, pow_succ,
    pow_right_comm]
  field; grw [(lt_of_pow_lt_pow_left₀ n W0.le (by grw [← s5, pow_right_comm, k1]; bound) :), lx]
  nlinarith only [hC, Y 3 5]
end

-- part: New.Main
section
/-! The inequality (⋆), an upper bound for weighted non-split primes. For admissible data with
scales x and x₁, the product formula and height bounds for twisted volumes show that the normalised
error of the weighted count of non-split primes ≡ 1 mod N₀ at x, minus that at x₁, plus a weight
times the error over all classes at x₁, is at most x^(−1/2+O(ε)), and a good choice of x₁ gives the
one-sided bound x^(8ε−1/2) for the error at x alone. Prime sums bounded by size against divisibility
are known (Chebyshev-order bounds, conditional CM heights, curves over F_q). Related work: Pritsker,
The Gelfond–Schnirelman method in prime number theory, 2005; Granville–Stark, ABC implies no Siegel
zeros, 2000; Bombieri, Counting points on curves over finite fields, Sém. Bourbaki 430, 1973; van
Frankenhuijsen, The Riemann hypothesis for function fields over a finite field, 2008.

No Dirichlet L-function vanishes in Re s > 1/2. For every Dirichlet character χ of any modulus,
L(s,χ) ≠ 0 when Re s > 1/2 (with s ≠ 1 if χ is principal), so by the functional equation the
non-trivial zeros of ζ and of all Dirichlet L-functions lie on Re s = 1/2, which is the Riemann
hypothesis and its generalisation and the final result of the argument. Related work: Bombieri,
Counting points on curves over finite fields, Sém. Bourbaki 430, 1973; Weil, Sur les courbes
algébriques, 1948.

This file: The inequality (⋆) from Theorems A to C; the one-sided bound; GRH. Zeros lie on the
critical line, given non-vanishing right of one half. -/

open DirichletCharacter Real Finset Filter Data Parameters ZMod Module

/- **The spine of the proof.**

Columns are algebraic forms on a definite U(k), rows are cusp forms on an indefinite U(r) (the
target), lifts are theta lifts; tops and thick places are sets of infinite places of `E`
(`Data.tops`, `Data.thick`). One covolume is bounded from both sides. `rowDim = finrank ℂ D.rows` is
the dimension of the target
(written `D` in the docstrings of `New.Endgame.LongForms`), `h_main = m k 𝖴` (`mainHeight`,
`dirCost`) is the main amount, `remainder` is a prime sum less its expected value,
`budget = f a log³ b`. For a family of target forms let `exp V` bound the squared covolume of the
lifts at all conjugates (`covolumeSq`) and let `δ` bound the logarithm of the index (`IndexLe`). Up
to errors, for the family of `exists_family_covolumeSq_le`,

    h_main  ≤  (V + 2 δ) / rowDim  ≤  h_main - m remainder.

Inputs (name, module, content).

Upper bound:
* `short_forms`, `enough_forms` (`New.Endgame.ShortAndEnough`): short forms (Theorem A); enough
  forms (Theorem B)
* `heightPerRow_le` (`New.Endgame.ShortAndEnough`): the level `N` pays the excess of the `m` lifts
* `exists_family_covolumeSq_le` (`New.Endgame.LongForms`): A and B together

Lower bound:
* `exists_isFitFamily` (`New.Selmer.FitTwistsExist`): twists `θ ι`, one for each `ι : ℂ ≃ ℚ̄_l`,
  with the congruence bounds `IsFitFamily`
* `volume_iota_eq_prod_liftVolume` (`New.Rows.RowVolume`): volume of the chain = constant × lift
  volumes
* `heightLe_liftVolume_ratio` (`New.Rows.LiftVolumeHeight`): each lift gains `rowDim k 𝖴` on the
  trivial twist
* `heightLe_volume_ratio_sq`, `heightLe_volume_rows` (`New.Endgame.LongForms`): heights of
  `𝔷 1² / 𝔷 θ²` and of `𝔷 θ / 𝔷 1`
* `HeightLe.nonneg` (`New.Heights.Heights`): product formula: the height of `1` is `≥ 0`
* `integral_forms_long` (`New.Endgame.LongForms`): the entries above together (Theorem C); the
  height of `𝔷 θ / 𝔷 1` uses `crude_rows` (`New.Exchange.CrudeRows`: cruder forms, which complete
  the family to a basis) and `one_determinant` (`New.Heights.OneDeterminant`)

Prime sums:
* `remainder_eq` (`New.Endgame.ShortAndEnough`): `remainder` in terms of the remainders
  `primeError`
* `abs_mainHeight_add_remainder_le` (`New.Endgame.ShortAndEnough`): crude bounds for `h_main` and
  `remainder`

Analysis:
* `exists_data` (`New.Data.DataExist`): data at every large `x`
* `IsPolar.exists_window_sub_mul_le` (`New.Endgame.OneSidedCriterion`): `R_{N₀} - c R₁ ≤ e^(-t)`
  at some `log x₁ ∈ [t, t²]`
* `entireL_ne_zero_of_primeError_le` (`New.Endgame.OneSidedCriterion`): Landau's lemma

Deduction (this file): `star_inequality`, then `eventually_primeError_le_rpow`, then `grh`.

What cancels, and where:
* `𝖴` (`dirCost`), as `h_main`: upper bound against lower bound; `star_inequality`, last step
* `chowlaSelbergConst` in the period `bigOmega`, Stirling: row of length `a` against `mainAsk`;
  `heightPerRow_le`, `excess`
* `m (w̄ + G)`, the main term of `logLevelTarget`: level against the `m` excesses;
  `heightPerRow_le`, third step
* `log x`, `log x₁`, `-1 - chowlaSelbergConst`: prime sums against `mainAsk`; `remainder_eq`

Here `w̄` is the mean of `log nominalWeight` over all `f` places, `G = log (g rootDisc / 2π)`, and
`logLevelTarget = m (w̄ + G) - G - (15 / 2) log b`.

Scales (`New.Data.AdmissibleData`, `New.Data.Magnitudes`; `N₀`, `d` fixed, `x → ∞`;
`logX logX₁ logB` = `log x, log x₁, log b`):
* log b ≪ x ≪ x₁ ≪ b: (log b)¹⁰⁰ ≤ x, x^(10⁶) ≤ x₁, x₁^(10⁶) ≤ b, (log x₁)⁶ ≤ log b,
  exp (10¹² c) ≤ log b (`P.c` bounds what depends on `N₀`, `d` only); `exists_data` has
  log b = x^ε, log x₁ = x^(ε/6), and `eventually_primeError_le_rpow` lowers log x₁ into [t, t²],
  t = 10⁶ log x
* `m`, number of lifts: in [√x, 2√x]; the saving x^(-1/2) is 1/m
* `r`, `k`, ranks of target and source: r in [x⁵, 3x⁵], r + 1 = k + m
* `t`, the ranks grow in steps: t = 5 r, n_j = k + j (t + 1)
* `f`, infinite places of `E`: #tops φ(N₀); #tops = `towerDeg s`, in [x¹¹, x¹¹ (log b)^(1/5)];
  #thick ≥ #tops / log b in `exists_data`
* `a`, long order, at the tops: in [x b, x b + N₁]
* `nominalWeight`, nominal weight: a / x at the thick places, a / x₁ elsewhere
* `g`, that is `gProd`, product of two primes: in [b²⁰, b²²]
* `N`, level, a prime: log N in [`logLevelTarget`, `logLevelTarget` + √(log b)], so in
  [m log b, 30 m log b]

`D.le_of_hasLogBound : F ≤ G` compares two such monomials by their exponents on these scales
(class `HasLogBound`).

Errors per dimension, with `L = f a log⁴ b`:
* length, Theorem A (a): L
* missing dimensions, Theorem B, `abs_mainHeight_add_remainder_le`: 4 b⁻² · b² x⁹⁹
* index, Theorems A (b), B: 2 · 5 log (1 + b²) · `budget`
* covolume, Theorem C: 3 L

Their sum is at most `f a log⁵ b`. Exponents such as 99 and 999 are slack: every power of `x` that
occurs is below `b`. -/

/-- The main inequality for admissible data D: m·rem ≤ (log b)²·𝓑, where rem is the remainder
`Data.remainder` and 𝓑 = f·a·(log b)³ is `Data.budget`.

The inequality (⋆): upper bound for weighted non-split primes. -/
lemma star_inequality {P} {D : Data P} : D.m * D.remainder ≤ D.logB ^ 2 * D.budget :=
  D.exists_family_covolumeSq_le.elim fun n ⟨y, i, big, ⟨δ, index, I⟩, short⟩ ↦ by
  have d0 : (0 : ℝ) < D.rowDim := mod_cast D.finrank_rows_ne_zero.pos
  -- `d` is the dimension, `L = f a log⁴ b` the unit of error, `exp h` the bound per form
  set d := (D.rowDim : ℝ)
  set L := D.logB * D.budget
  set h := D.mainHeight - D.m * D.remainder + L with def_h
  have crude : -h ≤ D.b ^ 2 * D.x ^ 99 := by
    grw [def_h, ← abs_mainHeight_add_remainder_le, ← neg_le_abs, ← le_abs_self,
      ← (HasLogBound.pos D : 0 < L)]
    simp
  have both : d * (D.mainHeight - 3 * L) ≤ d * (D.mainHeight - D.m * D.remainder + L + 4 *
    D.x ^ 99 + 10 * log (1 + D.b ^ 2) * D.budget) := calc
    _ ≤ d * h + (d - n) * -h + 2 * δ := (integral_forms_long i big I short).trans_eq (by ring)
                    -- the missing dimensions are a share `4 / b²`, and the index is small
    _ ≤ d * h + 4 / D.b ^ 2 * d * (D.b ^ 2 * D.x ^ 99) + 2 *
      (5 * d * log (1 + D.b ^ 2) * D.budget) := by
      grw [crude, index, show d - n ≤ 4 / D.b ^ 2 * d by linarith]
      exact sub_nonneg.2 (mod_cast Fintype.card_fin n ▸ i.fintype_card_le_finrank : (n : ℝ) ≤
        D.rowDim)
    _ = _ := by rw [def_h]; field [exp_ne_zero]
  -- divide by `d`; `h_main` cancels
  calc D.m * D.remainder ≤ 4 * L + 4 * D.x ^ 99 + 10 * log (1 + D.b ^ 2) * D.budget := by
        linarith [le_of_mul_le_mul_left both d0]
    _ ≤ _ := D.le_of_hasLogBound

/-- One-sided bound: for parameters N₀, d as in `Parameters` and 0 < ε < 1/100, the remainder
R_{N₀}(x) (`primeError`) is at most x^{8ε − 1/2} for all large x. -/
lemma eventually_primeError_le_rpow (P : Parameters) {ε : ℝ} (h : 0 < ε / 6 ∧ ε < 1 / 100) :
    ∀ᶠ x in atTop, primeError P.d P.N₀ x ≤ x ^ (8 * ε + 2⁻¹ - 1) := by
  filter_upwards [h.elim (exists_data P), tendsto_log_atTop.const_mul_atTop (r := 1e6) (by bound)
    ((isPolar_primeError PrimeSevenModEight.mod_eight (P.coprime_N₁_d
    0).coprime_mul_right).exists_window_sub_mul_le (isPolar_primeError PrimeSevenModEight.mod_eight
    P.d.coprime_one_left))] with x ⟨D, _, _, l, e, H'⟩ W
  subst x; simp only [log_exp, Set.mem_preimage, ← exp_mul] at *
  obtain := D.hasLogLower_of_le H', D.scale
  -- move `log x₁` to a point `u` of the window where `R_{N₀} - (#tops / #thick) R₁ ≤ x ^ (-10⁶)`
  obtain ⟨u, ⟨a, b⟩, w⟩ := W (towerDeg D.s / #D.thick) ⟨by bound, D.le_of_hasLogBound⟩
  let D' := {D with logX₁ := u, scale := by grw [b, l] <;> grind}
  have := D'.hasLogLower_of_le H'
  calc primeError P.d P.N₀ D.x = D'.m * D'.remainder / D'.m / D'.a / #D.thick + (primeError P.d P.N₀
      D'.x₁ - towerDeg D.s / #D.thick * primeError P.d 1 D'.x₁) := by simp [remainder_eq, tops,
      card_placeClass_eq, field, HasLogBound.pos D', ne_of_gt]
    _ ≤ D'.logB ^ 2 * D'.budget / D'.m / D'.a / #D.thick + exp
      (-(1e6 * D.logX)) := by grw [star_inequality, w]
    -- the first term is `f log⁵ b / (m #thick) ≤ φ(N₀) log⁶ b / √x`, and `log b = x ^ ε`
    _ ≤ _ := D'.le_of_hasLogBound (by grind)

/-- The generalised Riemann hypothesis for Dirichlet L-functions, in half-plane form: for every
N ≥ 1 and every Dirichlet character χ mod N, L(s, χ) ≠ 0 when Re s > 1/2, the pole s = 1 of the
principal character excepted.

No Dirichlet L-function vanishes in Re s > 1/2. -/
lemma New.grh : DirichletLNonvanishingRightOfHalf := fun q _ χ ρ hρ pole zero ↦ by
  -- `51` gives `ε < 1 / 100` and `8 ε + 1 / 2 < re ρ`
  set ε := (ρ.re ⊓ 1 - 2⁻¹) / 51
  -- pass to the modulus `N₀ = 18480 q` and the class `N₀ / 2 - 1`, whose square is `1`
  have induced : entireL (χ.changeLevel (dvd_mul_left q 18480)) ρ = 0 := by
    rw [entireL]
    grind [LFunction_changeLevel, changeLevel_eq_one_iff]
  refine entireL_ne_zero_of_primeError_le (β := 8 * ε + 2⁻¹) (by grind)
    (.of_mul_eq_one (9240 * q - 1) (by grind [natCast_self (18480 * q)]) :
    IsUnit (9240 * q - 1 : ZMod (_ * q))) (fun d h ↦ ?_) ρ (by grind) _ induced
  -- each prime `d` of the class gives parameters, and `eventually_primeError_le_rpow` is the bound
  -- that is asked for
  let P := mk _ d ⟨q, rfl⟩ d.2 (by
    simp [← natCast_eq_zero_iff, h]; norm_cast; simp [↓natCast_eq_zero_iff, ← mul_assoc,
      mul_dvd_mul_iff_right])
  exact ⟨⟨P.instHeegD.2, (P.coprime_N₁_d 0).coprime_mul_right⟩,
    eventually_primeError_le_rpow P (by grind)⟩

/-- Assume h: no Dirichlet L-function vanishes in Re s > 1/2 (the pole at s = 1 excepted). Then GRH
holds: for χ of any modulus, every zero of L(s, χ) with 0 < Re s < 1 has Re s = 1/2. -/
lemma New.zeros_on_line (h : DirichletLNonvanishingRightOfHalf) : DirichletLZerosOnLine :=
  fun N _ ↦ by grind [h N, Complex.one_re, Complex.sub_re, → LFunction_one_sub_eq_zero,
  Complex.ext_iff, DirichletCharacter.gammaFactor, Complex.Gammaℝ_ne_zero_of_re_pos]

/-- Assume h: no Dirichlet L-function vanishes in Re s > 1/2 (the pole at s = 1 excepted). Then
the Riemann hypothesis holds: every zero s ≠ 1 of ζ other than −2, −4, … has Re s = 1/2. -/
lemma New.zeta_zeros_on_line (h : DirichletLNonvanishingRightOfHalf) :
    RiemannZetaZerosOnLine := fun s ↦ by
  obtain _ := h 1 1 s, h 1 1 (1 - s), @Nat.or_exists_add_one, riemannZeta_zero
  simp_all
  grind [riemannZeta_def_of_ne_zero, completedRiemannZeta_one_sub, Complex.Gammaℝ_eq_zero_iff]
end
