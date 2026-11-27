import Lib.GaloisRep.ZeroSymmetry
import Lib.ClassField.PolarLandau
import Lib.ClassField.PrimeError
import New.Weil.IndexTypes
import Statements
import Lib.PadicHodge.LongForms

-- part: Lib.Analytic.PolyaVinogradov.PolyaVinogradov
section
/-! Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character.
It is proved here for initial intervals only, with the explicit bound 2√q(1+log q) for any
non-principal character. The bound is obtained by sieving the inducing primitive character over
divisors. Source: Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory;
Montgomery–Vaughan Thm 9.18.

This file: Pólya–Vinogradov inequality for non-principal characters; modulus of primitive Gauss
sums. -/

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

attribute [simp] Real.log_mul log_div log_rpow log_sqrt norm_le_one ne pos
  norm_cpow_eq_rpow_re_of_pos


variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive character mod q has absolute value √q. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  simpa [funext hχ.fourierTransform_eq_inv_mul_gaussSum, dft_mul_const, dft_comp_neg,
    fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift, ← star_gaussSum_eq] using
    congr(√‖$(dft_dft χ) (-1)‖)

/-- Pólya–Vinogradov inequality for a non-principal character χ mod q: |∑_{1 ≤ v ≤ X} χ(v)| ≤
2√q (1 + log q) for all X.

Known result: Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. -/
lemma polya_vinogradov (h : χ ≠ 1) (X : ℕ) : ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + .log q) := by
  let ⟨M, ⟨r, hr⟩, ψ, _, hψ, E⟩ := exists_isPrimitive_changeLevel_eq χ
  have e (v : ℕ) : χ v = ∑ e ∈ (v.gcd r).divisors, μ e • ψ v := by
    rw [← sum_smul, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply, ← Int.cast_natCast]
    split <;> grind [Int.cast_natCast, apply_eq_zero_iff, changeLevel_eq_cast_of_dvd',
      coprime_mul_iff_right, isCoprime_iff_coprime]
  grw [funext e, sum_comm' (t' := r.divisors) (s' := fun e ↦ (Ioc 0 (X / e)).image (e * ·)) (by
    rintro v ⟨⟩ <;> simp [Nat.dvd_gcd_iff, le_div_iff_mul_le, dvd_def (b := v), mul_comm]
    aesop), norm_sum_le, sum_le_card_nsmul _ _ (√M * (1 + .log q)) fun d he ↦ ?_, card_le_card
    (t := Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image (r / ·)) fun d he ↦ ?_, card_union_le,
    Finset.card_image_le, congr(√$hr)] <;> clear e <;> simp [zero_lt_iff] at *
  · grw [nat_sqrt_le_real_sqrt]; grind
  -- of two complementary divisors one is at most `√r`
  · cases he.1; cases le_sqrt_of_eq_mul ‹_› <;> aesop
  -- the primitive character: its sums are at most `√M (1 + log M)`
  simp [← mul_sum, ← Int.cast_abs, ne_zero_of_dvd_ne_zero he.2 he.1]
  let f (n : ℕ) := √M * M / 2 * ((↑n)⁻¹ + (↑(M - n))⁻¹)
  grw [norm_le_one, abs_moebius_le_one, ← dft.symm_apply_apply ψ]
  simp_rw [invDFT_apply, ← nsmul_eq_mul', AddChar.map_nsmul_eq_pow, ← smul_sum, @sum_comm _ _ ℕ,
    ← sum_smul, hψ.fourierTransform_eq_inv_mul_gaussSum]
  grw [norm_smul, ← sum_erase _ (a := 0) (by simp [map_zero', ψ.level_one'.mt (by grind)]),
    norm_sum_le_of_le _ (n := (f ·.val)) fun k hk ↦ ?_, ← sum_image (val_injective M).injOn,
    (by grind : image _ _ ⊆ range (M + 1)), ← le_of_dvd _ ⟨r, hr⟩, ← harmonic_le_one_add_log]
  iterate 3 simp [harmonic, field, sum_range_succ', two_mul, f, ↓sum_flip (·⁻¹ : ℕ → ℝ), ← mul_sum]
  -- a geometric sum is at most `1 / sin (π x)`, `x = k / M`, and `sin (π x) ≥ 2 x (1 - x)`
  simp_all [norm_gaussSum_of_isPrimitive]
  obtain ⟨x, c, hx, d⟩ : ∃ x > (0 : ℝ), k.val = M * x ∧ 0 < 1 - x := ⟨k.val / M, by
    simp [field, val_lt, -natCast_val, *]⟩
  grw [← Ico_add_one_add_one_eq_Ioc, geom_sum_Ico (injective_stdAddChar.ne hk ∘ by
    simp) (by simp), norm_div, norm_sub_le, ← (?_ : 2 * (2 * x * (1 - x)) ≤ ‖(_ : ℂ) - 1‖)]
  · simp [val_le, field, ← two_mul, *]
  grw [stdAddChar_apply, toCircle_eq_circleExp, Circle.coe_exp, mul_comm _ I, hx,
    norm_exp_I_mul_ofReal_sub_one, ← le_norm_self, (by field : _ / 2 = 2 * (π / 2 * x)),
    Real.sin_two_mul, ← one_sub_mul_le_cos] <;> simp [field, pi_pos] <;> grind [le_sin_mul]
end

-- part: Lib.Analytic.DirichletTheta.MellinTheta
section
/-! Known result: the transformation formula and the Mellin transform of the theta series of a
Dirichlet character. The transformation is proved only in absolute value, so no root number appears,
first for any non-principal character against its finite Fourier transform and then for a primitive
character against itself. The Mellin formula holds for any bounded coefficients to the right of 1
and for such characters to the right of 0. Source: Davenport, Multiplicative Number Theory;
Montgomery–Vaughan ch. 10.

This file: Gaussian theta series of a character: Poisson symmetry, Mellin transform is Gamma times
L. -/

open Complex Filter HurwitzZeta MeasureTheory Real Set ZMod

/-- The function g(x) = x^j e^{−πx²} of a real variable x. -/
noncomputable def gaussianMonomial (j : Fin 2) x := x ^ j.1 * rexp (-π * x ^ 2)

/-- The theta series ∑_{n ≥ 1} c(n) g(nt) with coefficients c, where g(x) = x^j e^{−πx²}. -/
noncomputable def gaussianTheta j (c : ℕ → ℂ) t := ∑' n : ℕ+, c n * gaussianMonomial j (n * t)

/-- The integral ∫_r^∞ |θ(t)| dt/√t, where θ(t) = ∑_{n ≥ 1} c(n) g(nt), g(x) = x^j e^{−πx²}, is
the theta series `gaussianTheta` j c. -/
noncomputable abbrev thetaTailIntegral j c r := ∫ t in Ioi r, ‖gaussianTheta j c t‖ / √t

/-- The gamma factor Γ_j(s) = ∫_0^∞ g(t) t^{s−1} dt, the Mellin transform of g(t) = t^j
e^{−πt²}. -/
noncomputable def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin (gaussianMonomial j ·)

variable {j : Fin 2} {c : ℕ → ℂ} {q} {t : ℝ} {s : ℂ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- If f is measurable and |f(t)| ≤ D e^{−t} for t > 0, then its Mellin transform is holomorphic
in Re s > 0 and bounded on the strip 1/2 ≤ Re s ≤ 2. -/
lemma mellin_differentiableOn_and_bounded {D} {f : ℝ → ℂ} (b : ∀ {t}, 0 < t → ‖f t‖ ≤ D * rexp (-t))
    (m : AEStronglyMeasurable f := by fun_prop (disch := simp) [gaussianTheta, gaussianMonomial]) :
  DifferentiableOn ℂ (mellin f) {z | 0 < z.re} ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖mellin f z‖ ≤ G := by
  refine (fun o p a ↦ have c s := mellinConvergent_of_isBigO_rpow_exp (s := s) one_pos a o p
    ⟨fun _ ↦ (mellin_differentiableAt_of_isBigO_rpow_exp one_pos a o p · |>.differentiableWithinAt),
    _, fun z _ ↦ norm_integral_le_of_norm_le ((c 2⁻¹ ?_).prodMk (c 2 ?_)).norm
    (ae_restrict_of_forall_mem ?_ fun t ↦ ?_)⟩) ?_ ?_ fun _ _ ↦ (volume.finiteAt_nhdsWithin
    ..).integrableAtFilter ⟨⊤, ?_⟩ ?_ <;> simp_all [Asymptotics.isBigO_iff]
  use D, 1, by grind
  iterate 2 exact ⟨_, mem_inf_of_right fun t k ↦ (b k).trans (by grw [le_abs_self D, ← k.out])⟩
  bound [le_total t 1]

lemma norm_gaussianMonomial_le (h : 0 ≤ t) : ‖gaussianMonomial j t‖ ≤ 3 * rexp (-t) ^ 2 := by
  grw [gaussianMonomial, norm_of_nonneg (by bound), show t ^ j.1 ≤ t + 1 by fin_cases j <;> grind,
    add_one_le_exp, ← exp_one_lt_three, ← pi_gt_three]
  simp [sq, ← Real.exp_add]; grind [sq_nonneg (t - 2⁻¹)]

/-- The trivial bound: for j ∈ {0, 1}, |c(n)| ≤ 1 and t > 0, the series ∑_{n ≥ 1} c(n) g(nt),
g(x) = x^j e^{−πx²}, converges absolutely and has modulus at most 3e^{−t}/t. -/
lemma summable_and_norm_gaussianTheta_le (hc : ∀ n, ‖c n‖ ≤ 1) (ht : 0 < t) : (Summable fun n : ℕ+ ↦
  c n * gaussianMonomial j (n * t)) ∧ ‖gaussianTheta j c t‖ ≤ 3 * rexp (-t) / t := by
  have H := hasSum_pnat_iff_hasSum_succ.2 ((hasSum_nat_add_iff' 1).2
    ((hasSum_geometric_of_abs_lt_one (by simpa : |rexp (-t) ^ 2| < 1)).mul_left 3))
  refine (fun b ↦ ⟨H.summable.of_norm_bounded b, (tsum_of_norm_bounded H b).trans ?_⟩) fun n ↦ ?_
  · grw [norm_mul, hc, norm_real, norm_gaussianMonomial_le] <;> simp [← Real.exp_nat_mul, field,
      ht.le]
  simp [t.exp_neg, field, *]; nlinarith [t.add_one_le_exp]

/-- For Re s > 0, Γ_j(s) = ½ π^{−(s+j)/2} Γ((s+j)/2). -/
lemma gaussianMellin_eq (hs : 0 < s.re) : gaussianMellin j s = Gammaℝ (s + j) / 2 := by
  simpa [gaussianMellin, gaussianMonomial, field] using (mellin_cpow_smul _ s j).trans
    ((mellin_comp_rpow _ _ 2).trans (congrArg _ (@hasSum_mellin_pi_mul_sq Unit _ 1 1
    (rexp <| -π * ·) _ (by simp; bound) (by simp) .of_finite).tsum_eq.symm))

/-- Riemann's formula: if |c| ≤ 1 and Re s > 1, the Mellin transform at s of t ↦ ∑_{n ≥ 1} c(n)
g(nt), g = `gaussianMonomial` j, is Γ_j(s) ∑_{n ≥ 1} c(n) n^{−s}. -/
lemma mellin_gaussianTheta (hc : ∀ n, ‖c n‖ ≤ 1) (hs : 1 < s.re) :
    mellin (gaussianTheta j c) s = gaussianMellin j s * LSeries c s := by
  rw [gaussianMellin_eq (by bound), LSeries, ← tsum_pnat_eq_tsum_of_eq_zero rfl]
  convert (mellin_cpow_smul _ s j.1).trans ((mellin_comp_rpow _ _ 2).trans (congrArg _
    (@hasSum_mellin_pi_mul_sq ℕ+ _ (fun n ↦ c n * n ^ j.1) (·) _ _ (by simp; bound)
    (fun u (h : 0 < u) ↦ (((@summable_and_norm_gaussianTheta_le j c √u hc ?_).1.div_const
    (√u ^ j.1)).congr ?_).hasSum) ((summable_pnat_iff_summable_nat.2 (summable_nat_rpow_inv.2
    hs)).of_nonneg_of_le ?_ ?_)).tsum_eq.symm)) using 1 <;> simp [← tsum_mul_left, cpow_add,
    rpow_add, field, mellin, gaussianTheta, gaussianMonomial, mul_pow, division_def, mul_assoc,
    mul_left_comm, le_of_lt, ne_of_gt, *]

omit [NeZero q] in
/-- If Φ on ℤ/q satisfies Φ(−x) = (−1)^j Φ(x) and Φ(0) = 0, and ∑_{n ∈ ℤ} Φ(n) g(nt) converges
to S, g = `gaussianMonomial` j, then S = 2 ∑_{n ≥ 1} Φ(n) g(nt). -/
lemma two_mul_gaussianTheta t {Φ : ZMod q → ℂ} {S} (h : ∀ x, Φ (-x) = (-1) ^ j.1 * Φ x) (h0 : Φ 0 =
  0) (H : HasSum (fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t)) S) : 2 * gaussianTheta j (Φ ·) t =
  S := by rw [← H.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ H.summable] <;> fin_cases j <;>
  simp [Function.Even, gaussianMonomial, gaussianTheta, *]

/-- Poisson summation for g = `gaussianMonomial` j, j ≤ 1: for real a and t > 0, ∑_{n ∈ ℤ} g((n +
a)t) converges to some S, and ∑_{n ∈ ℤ} e^{2πian} g(n/t) converges to i^j t S. -/
lemma poisson_summation_gaussianMonomial a (ht : 0 < t) : ∃ S,
  HasSum (fun n : ℤ ↦ gaussianMonomial j ((n + a) * t)) S ∧ HasSum (fun n : ℤ ↦ cexp
  (2 * π * I * a * n) * gaussianMonomial j (n * t⁻¹)) (I ^ j.1 * t * S) := have h := pow_pos ht 2
  by fin_cases j <;> [obtain ⟨u, v⟩ := hasSum_int_evenKernel a h, hasSum_int_cosKernel a (inv_pos.2
                h); obtain ⟨u, v⟩ := (hasSum_int_oddKernel a h).mul_left t, (hasSum_int_sinKernel a
    (inv_pos.2 h)).mul_left (I / t)] <;> refine ⟨_, u.congr_fun ?_, (v.congr_fun ?_).trans_eq
    (congrArg _ ?_)⟩ <;> simp [gaussianMonomial, mul_pow, mul_assoc, evenKernel_functional_equation,
    ht.ne', oddKernel_functional_equation, ← rpow_natCast_mul ht.le, field, mul_div_cancel₀]

lemma gaussianMellin_differentiableOn_and_bdd : DifferentiableOn ℂ (gaussianMellin j) {z | 0 < z.re}
  ∧ ∃ G, ∀ z, re z ∈ Icc 2⁻¹ 2 → ‖gaussianMellin j z‖ ≤ G := mellin_differentiableOn_and_bounded
  fun h ↦ by grw [norm_real, norm_gaussianMonomial_le, _root_.sq_le] <;> simp [h.le, exp_nonneg]

/-- For j ≤ 1, |Γ_j| has a positive lower bound on every compact subset of the half-plane Re s >
0. -/
lemma exists_pos_le_norm_gaussianMellin {K} (hK : IsCompact K) (h : ∀ s ∈ K, 0 < s.re) :
    ∃ c > 0, ∀ s ∈ K, c ≤ ‖gaussianMellin j s‖ :=
  hK.exists_forall_le' (gaussianMellin_differentiableOn_and_bdd.1.continuousOn.mono h).norm
  fun s k ↦ by simp [gaussianMellin_eq, Gammaℝ_ne_zero_of_re_pos, (h s k).trans_le]

variable (h1 : χ ≠ 1) (hp : χ (-1) = (-1) ^ j.1)

include h1 hp

/-- For j ≤ 1, non-principal χ mod q with χ(−1) = (−1)^j and t > 0: t |θ_χ(t)| = |θ_φ(1/(qt))|,
where θ_c = `gaussianTheta` j c and φ(n) = q⁻¹ ∑_a χ(a) e^{2πian/q}.

Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
lemma gaussianTheta_poisson_summation (ht : 0 < t) :
  t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (𝓕⁻ χ ·) (q * t)⁻¹‖ := by
  have e (x : ZMod q) := hp ▸ neg_one_mul x ▸ map_mul χ _ x
  choose S h h' using fun a : ZMod q ↦
    @poisson_summation_gaussianMonomial j (q * t) (a.val / q) (by simpa)
  have a := two_mul_gaussianTheta t e (χ.map_zero' (h1 ∘ χ.level_one')) ((hasSum_sum fun a _ ↦
    (Function.Injective.hasSum_iff (g := fun n : ℤ ↦ a.cast + q * n) (fun _ ↦ by simp) (by
    simp_all [intCast_eq_iff, ne_comm])).1 (((hasSum_ofReal.2 (h a)).mul_left (χ a)).congr_fun
    (by simp [← mul_assoc, add_mul]; grind))).congr_fun (Fintype.sum_pi_single' ↑· _ |>.symm))
  have b := @two_mul_gaussianTheta j _ (q * t)⁻¹ (𝓕⁻ χ) _ (fun n ↦ by
    simp_rw [invDFT_apply', ← congr($(dft_comp_neg χ) (-n)), e, dft_const_mul]; ring)
    (by simp [invDFT_apply, χ.sum_eq_zero_of_ne_one h1]) (((hasSum_sum (s := ⊤) fun a _ ↦
    (h' a).mul_left (χ a)).div_const q).congr_fun fun n ↦ by
    simp_rw [invDFT_apply, ← zsmul_eq_mul', AddChar.map_zsmul_eq_zpow, stdAddChar_apply]
    simp [toCircle_apply, ← exp_int_mul, Finset.sum_mul, -natCast_val, field]; grind)
  simp_all [mul_left_comm, ← Finset.mul_sum, ← a, abs_of_pos, field]

/-- Theta functional equation in absolute value: for j ≤ 1, primitive non-principal χ mod q with
χ(−1) = (−1)^j and t > 0, √q t |θ(t)| = |θ(1/(qt))|, where θ = `gaussianTheta` j χ.

Known result: Theta series of a Dirichlet character: transformation formula and Mellin transform. -/
lemma norm_gaussianTheta_functional_equation (hχ :
  χ.IsPrimitive) (ht : 0 < t) : √q * t * ‖gaussianTheta j (χ ·) t‖ = ‖gaussianTheta j (χ ·)
  (q * t)⁻¹‖ := by rw [mul_assoc, gaussianTheta_poisson_summation, eq_comm, ← norm_star] <;>
  simp [gaussianTheta, tsum_star, invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum,
  χ.star_apply', mul_assoc, mul_left_comm, tsum_mul_left, norm_gaussSum_of_isPrimitive, *, field]

/-- For a non-principal character χ mod q with χ(−1) = (−1)^j, j ∈ {0, 1}, and t > 0: |∑_{n ≥ 1}
χ(n) g(nt)| ≤ 3q·e^{1−t}, where g(x) = x^j e^{−πx²}. -/
lemma norm_gaussianTheta_char_le (h : 0 < t) : ‖gaussianTheta j (χ ·) t‖ ≤ 3 * q * rexp 1 * rexp
  (-t) := by
  cases le_total 1 t
  · grw [(summable_and_norm_gaussianTheta_le (by simp) h).2, div_le_self,
      ← @NeZero.one_le q] <;> bound
  grw [← mul_le_mul_iff_right₀ h, gaussianTheta_poisson_summation,
    (summable_and_norm_gaussianTheta_le (fun n ↦ by grw [invDFT_apply, norm_smul,
    norm_sum_le_of_le _ (n := 1)] <;> simp) _).2, exp_le_one_iff.2] <;> simp [field, t.exp_neg, *]

/-- For j ≤ 1 and non-principal χ with χ(−1) = (−1)^j, the Mellin transform of t ↦ ∑_{n ≥ 1}
χ(n) g(nt), g = `gaussianMonomial` j, equals Γ_j(s) L(s, χ) for Re s > 0. -/
lemma mellin_gaussianTheta_char (hs : 0 < s.re) : mellin (gaussianTheta j (χ ·)) s =
  gaussianMellin j s * χ.LFunction s := have o := isOpen_re_gt
  ((mellin_differentiableOn_and_bounded (norm_gaussianTheta_char_le h1 hp)).1.analyticOnNhd
    (o 0)).eqOn_of_preconnected_of_eventuallyEq
  ((gaussianMellin_differentiableOn_and_bdd.1.mul (by fun_prop)).analyticOnNhd (o 0))
    (convex_halfSpace_re_gt 0).isPreconnected (by simp : 0 < re 2) (.mono ((o 1).mem_nhds (by simp))
  (by simp_all [mellin_gaussianTheta, χ.LFunction_eq_LSeries])) hs

/-- For j ≤ 1, primitive non-principal χ mod q with χ(−1) = (−1)^j, T > 0 and q ≤ T²: ∫_0^∞
|θ(t)| dt/√t ≤ 2 ∫_{1/T}^∞ |θ(t)| dt/√t, where θ = `gaussianTheta` j χ. -/
lemma thetaTailIntegral_zero_le_two_mul (hχ : χ.IsPrimitive) {T : ℝ} (hT : 0 < T) (h : q ≤ T ^ 2) :
    thetaTailIntegral j (χ ·) 0 ≤ 2 * thetaTailIntegral j (χ ·) T⁻¹ := by_cases (fun i ↦ by
  grw [two_mul, ← sub_le_iff_le_add, ← setIntegral_sdiff _ i, Ioi_sdiff_Ioi, thetaTailIntegral,
    ← show _ '' Ioo 0 T⁻¹ ⊆ Ioi T⁻¹ from forall_mem_image.2 fun t ⟨a, b⟩ ↦ inv_strictAnti₀
    (b := q * t) ?_ (by grw [h, b]; simp [sq]), integral_image_eq_integral_abs_deriv_smul _
    fun t k ↦ (hasDerivAt_const_mul _).hasDerivWithinAt.fun_inv (by simp [k.1.ne']),
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun]
  any_goals simp +contextual [← norm_gaussianTheta_functional_equation, abs_div, field, EqOn,
    le_of_lt, -mul_inv_rev, *]
  exacts [.of_forall fun _ ↦ by positivity, i.mono_measure (by gcongr; bound)]) (integral_undef ·
    |>.trans_le (by positivity))
end

-- part: Lib.Analytic.Primes.AuxiliaryPrimes
section
/-! Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). From a small
zero-free disc at 1, this file only finds one prime congruent to 1 modulo a power of a fixed
multiple of 4, with its logarithm in a long window. It gives no asymptotic count. Source: Montgomery
and Vaughan, Multiplicative Number Theory I, 2007, Cor. 11.19.

This file: A prime 1 modulo M^k with logarithm in a long window; zero-free disc. -/

attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono
open ArithmeticFunction DirichletCharacter Complex Set Filter MeasureTheory LSeries Finset Real
  Topology vonMangoldt Chebyshev Polynomial ZMod MulChar

/-- For 0 < r < 1/9 there is C ≥ 0 with |L(s, χ)| ≤ C q^(2r) on the disc |s − 1| ≤ r, for every
modulus q and every non-principal character χ mod q. -/
lemma exists_norm_LFunction_le {r} (h0 : 0 < r) (_ : r < 9⁻¹) : ∃ C ≥ 0, ∀ {q} [NeZero q]
    {χ : DirichletCharacter ℂ q} {s}, χ ≠ 1 → dist s 1 ≤ r → ‖χ.LFunction s‖ ≤ C * q ^ (2 * r) := by
  have p s := by simpa [← dist_eq_norm] using abs_re_le_norm (s - 1)
  choose c c0 hc using
    (@exists_pos_le_norm_gaussianMellin · _ (isCompact_closedBall 1 r) (by simp; grind))
  exact ⟨_, norm_nonneg (_ / c ·), @fun q ⟨_⟩ χ s hχ hs ↦ by
    have ⟨j, hp⟩ : ∃ j : Fin 2, χ (-1) = (-1) ^ j.1 := by simpa using! χ.even_or_odd
    grw [← norm_le_pi_norm, ← le_norm_self, div_mul_eq_mul_div, le_div_iff₀' (c0 j), hc j s hs,
      ← norm_mul, ← mellin_gaussianTheta_char hχ hp (by grind), mellin, norm_integral_le_of_norm_le
      (((GammaIntegral_convergent h0).const_mul (3 * rexp 1)).mul_const _)
      (ae_restrict_of_forall_mem (by simp) fun t (k : 0 < t) ↦ ?_), integral_mul_const]
    grw [norm_smul, le_min (summable_and_norm_gaussianTheta_le (by simp) k).2
      (norm_gaussianTheta_char_le hχ hp k), min_def]
    split <;> simp (disch := positivity) [← log_le_log_iff, abs_le] at * <;>
      nlinarith [p s, log_natCast_nonneg q]⟩

/-- Let M > 0 be a multiple of 4 and A natural. For small η > 0, all k ≥ 2 with M^k ≤ η^{−A},
all characters χ mod M^k and |s − 1| ≤ η, one has η|L̃′(s, χ)| < |L̃(s, χ)|, where L̃ is
`entireL`. -/
lemma eventually_mul_norm_deriv_entireL_lt A {M : ℕ} [NeZero M] (e : 4 ∣ M) : ∀ᶠ η : ℝ in 𝓝[>] 0,
  ∀ k > 1, ∀ χ s,
  M ^ k ≤ (η ^ A)⁻¹ → dist s 1 ≤ η → ¬‖entireL χ s‖ ≤ η * ‖deriv (@entireL (M ^ k) _ χ) s‖ := by
  obtain ⟨⟨r, h0, _⟩, m, f⟩ := exists_pos_mul_lt one_pos (20 * A + 18 : ℝ), e
  have ⟨K, _, hC⟩ := exists_norm_LFunction_le (add_pos h0 h0) (by nlinarith)
  filter_upwards [mem_inf_of_left (eventually_closedBall_subset (by
    simp; intro; and_intros <;> apply ContinuousAt.eventually_lt <;> first
      | fun_prop (disch := grind) | simp (disch := bound) [entireL_ne_zero] : ∀ᶠ x in 𝓝 (0, 1), ∀ f
    ∈ range (@entireL (M ^ 2) _), x.1 * ‖deriv f x.2‖ < ‖f x.2‖ ∧ x.1 ^ (-A * (2 * (r + r)) * 5 + 1)
    * ‖f x.2‖ ^ 3 * (3 / r) ^ 4 * K ^ 5 < 1)), Ioc_mem_nhdsGT h0] with η H ⟨hη, j⟩ k o χ s hk hs h7
  have H {s} hs χ (h : χ ^ 2 = 1) := @H (η, s) (max_le (c := η) (by simp; grind) hs) (entireL χ)
    (((χ.factorsThrough_iff_ker_unitsMap (pow_dvd_pow M o)).2 fun u hu ↦
    ((intCast_eq_intCast_iff_dvd_sub u.1.cast 1 _).1 (by simp; use congr($hu.1))).elim fun t a ↦ by
    obtain ⟨⟨c⟩⟩ := (C (M * m * t) + X ^ 2 + X).existsUnique_nilpotent_sub_and_aeval_eq_zero
      (x := 0 * u.1) ⟨k, by simp [mul_pow, natCast_pow_eq_zero_of_le]⟩ (by simp), congr($a + u.1)
    ext; simpa [show u = (1 + 2 * c) ^ 2 by simp [f, map_ofNat] at *; grind, ← pow_apply', h] using
      one_apply_coe u).2.imp fun g a ↦ by ext s; fun_cases entireL g <;> by_cases s =
    1 <;> simp [LFunction_changeLevel, Nat.primeFactors_pow, *, entireL, o.ne_zero,
    LFunctionTrivChar_eq_mul_riemannZeta] <;>
    simpa [*, Nat.primeFactors_pow] using g.LFunction_changeLevel dvd_rfl)
  have ⟨h, n, h1⟩ : χ ^ 2 ≠ 1 ∧ χ ≠ 1 ∧ dist (1 + η : ℂ) 1 ≤ η := by simp; grind [one_pow]
  have hd (z : ℂ) (b : dist z 1 ≤ η) := norm_deriv_le_of_forall_mem_sphere_norm_le h0
    (differentiable_LFunction n).diffContOnCl fun w a ↦ hC n (by grw [dist_triangle, a.le, b, j])
  apply ((H h1 1 (by simp)).2.trans_le (norm_LFunction_product_ge_one χ hη 0)).not_ge
  simp [entireL, hη.ne', abs_of_pos, rpow_add, rpow_mul hη.le, *, -neg_mul] at h7 ⊢
  nth_grw 1 [norm_le_insert' (χ.LFunction _), h7, hd, (convex_closedBall
    ..).norm_image_sub_le_of_norm_deriv_le (by fun_prop) hd hs h1, ← dist_eq_norm,
    dist_triangle_right, hs, h1, hC h, ← hk] <;> grind

/-- Let M > 0 be a multiple of 4 and A natural. For large W, all k ≥ 2 with M^k ≤ W^A and all U in
[W, W^A], there is a prime p ≡ 1 mod M^k with U ≤ log p ≤ U + W.

Known result: A prime in a long window (weak form of the Siegel-Walfisz theorem). -/
lemma exists_prime_modEq_one_log_mem (M A : ℕ) [NeZero M] (hM : 4 ∣ M) : ∀ᶠ W : ℝ in atTop, ∀ k > 1,
  M ^
  k ≤ W ^ A → ∀ U ∈ Icc W (W ^ A), ∃ p, p.Prime ∧ p ≡ 1 [MOD M ^ k] ∧ .log p ∈ Icc U (U + W) := by
  obtain ⟨t, n, C, hC⟩ := tendsto_sqrt_atTop, (hasDerivAt_term · · · |>.differentiableAt),
    (LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := 3 / 4) (by simpa [sum_filter,
    psi_sub_theta_eq_sum_not_prime, sqrt_eq_rpow] using! isBigO_psi_sub_theta_sqrt.natCast_atTop)
    (by bound) (by simp) (by bound)).norm
  filter_upwards [mem_atTop (C ⊔ 0), t (tendsto_inv_atTop_nhdsGT_zero
    (eventually_mul_norm_deriv_entireL_lt (2 * A) hM)), t (tendsto_exp_mul_div_rpow_atTop (2 *
    A * 2) 4⁻¹ (by simp) (Ioi_mem_atTop (.exp 2))), t (mem_atTop 9)] with W _ h hW g k o hq U hV
  set q := M ^ k; simp_all [← natCast_eq_natCast_iff, rpow_mul, pow_mul]
  have ⟨D, d, p, _⟩ : ∃ D > 0, 0 < W ∧ U * D = 1 := ⟨U⁻¹, by grind [inv_pos]⟩
  let a n : ℂ := @residueClass q 1 n
  let F z := (1 - z * ∑ χ, logDeriv (@entireL q _ χ) (1 + z)) / q.totient
  have e z (h : 0 < z.re) : LSeriesHasSum a (1 + z) (F z / z) := by
    convert (LSeriesHasSum.sum (S := ⊤) fun χ _ ↦ @LSeriesHasSum_mul_vonMangoldt q χ _ _ ?_).smul
      q.totient⁻¹ <;> simp [a, residueClass_eq, h, ite_div]
    field [ne_zero_of_re_pos h]
  have hb {z} (u : ‖z‖ ≤ (√W)⁻¹) : _ ∧ ‖F z‖ ≤ 2 := have h := (h k o · (1 + z) hq (by simpa))
    ⟨(norm_pos_iff.1 <| h · |>.trans_le' (by bound)), by
    grw [norm_div, mul_sum, norm_sub_le, norm_sum_le]; simp [logDeriv, mul_div]
    grw [u, h, div_self_le_one]
    simp [← card_eq_totient_of_hasEnoughRootsOfUnity ℂ, field, mul_two, NeZero.one_le]⟩
  by_contra
  apply (@norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le _ _ _ _ 0 √W⁻¹ U (fun z ↦ (F z - z *
    ∑ n ∈ range ⌈U.exp⌉₊ with .log (n : ℕ) < U, term a (1 + z) n) / (2 - U * z - √W / 4 *
    (1 + √W * z) ^ 2).exp) 0 (by simpa) (DifferentiableOn.diffContOnCl_ball (fun s b ↦
    DifferentiableAt.differentiableWithinAt (by fun_prop (disch := simp_all) [logDeriv])) le_rfl)
    fun z u ↦ ?_).not_gt
  simp [F, field, Real.exp_sub] at *
  grw [hV.2, q.totient_le, M.cast_pow, hq]; grind
  obtain := z.sq_norm_sub_sq_re, z.abs_re_le_norm, sq_sqrt p.le
  simp [div_le_iff₀, exp_pos, -sub_re, sq, abs_le] at *; set E := re _
  obtain ⟨⟨⟩ : ∃ τ ≥ 0, τ ≤ W ∧ 2 - (U + τ) * z.re ≤ E, b : re (F D / D) ≤ 2 * U⟩ :=
    ⟨W / 2 * (1 + √W * z.re), by simp [u, field, E] at *; split_ands <;> nlinarith⟩, by
    grw [re_le_norm, norm_div, (hb _).2] <;> simp [abs_of_pos d, field] <;> nlinarith
  have G := (hasSum_re (e D d)).congr_fun fun n ↦ (re_eq_norm.2 (mod_cast term_nonneg
    (by simp [a, residueClass_nonneg]) _)).symm
  have key (n : ℕ) σ (h : .log n * (σ - z.re) ≤ E) : ‖term a (1 + z) n‖ ≤ E.exp *
      ‖term a (1 + σ) n‖ := by grw [← h]; by_cases n = 0 <;>
    simp [*, ↓cpow_add, cpow_def, field, mul_sub, Real.exp_sub, ← natCast_log]
  obtain ⟨v, x | x⟩ := u ▸ inv_anti₀ (by simp) g, le_or_gt z.re D
  · grw [norm_sub_le, norm_mul, (hb u.le).2, v, norm_sum_le, key, ← mul_sum,
      sum_le_hasSum _ (by simp) G, b] <;> simp at * <;> nlinarith [E.one_le_exp (by nlinarith)]
  grw [← mul_div_cancel₀ (F z) (ne_zero_of_re_pos (d.trans x)), ← mul_sub, norm_mul, v,
    sum_filter, (HasSum.sub (e z (by bound)) (hasSum_sum_of_ne_finset_zero (by grind [Nat.lt_ceil,
    lt_exp_of_log_lt]))).norm_le_of_bounded ((hC.add G).mul_left E.exp) fun n ↦ ?_, b]
  nlinarith [exp_pos E]
  split <;> simp; bound
  by_cases U + W < .log n <;> [grw [key n D (by nlinarith)]; grw [← @norm_term_le a _ _ _
    (by simp [a, indicator]; grind), key n (-4⁻¹) (by nlinarith)]] <;> bound
end

-- part: Lib.Analytic.QuadraticTwist.ZeroFreeTwist
section
/-! Known result: Zero density for quadratic twists by mean values over real characters. This file
only finds one prime in a given class whose quadratic twists have no zero up to a given height right
of a line beyond the critical line. The proof uses a three-lines argument and a smoothed mean square
of Jacobi symbol sums. Source: Jutila, On mean values of Dirichlet polynomials with real characters,
Acta Arith. 27 (1975) 191-198.

This file: Some prime in a class has quadratic twists zero-free on a half-strip; three lines. -/
seal Finset.univ Finset.sum Finset.prod

open ArithmeticFunction DirichletCharacter Complex Moebius Finset Real ZMod vonMangoldt LSeries
  Filter jacobiSym legendreSym MeasureTheory Nat NumberTheorySymbols


variable {N : ℕ} [NeZero N] (ξ : DirichletCharacter ℂ N) (j : Fin 2) {η : ℝ}

omit [NeZero N] in
lemma norm_mul_moebius_le_one (n : ℕ) : ‖ξ n * μ n‖ ≤ 1 := by by_cases Squarefree n <;> simp [*]

open Set HadamardThreeLines in
/-- Three lines: for j ≤ 1, some C gives |Γ_j(s)|² ≤ C T^(−2η) whenever χ ≠ 1 is primitive mod q
≤ T² of parity j, L(s, χ) = 0, 1/2 + 9η ≤ re s ≤ 1, and the integrals `thetaTailIntegral` from 1/T
of the theta series of χ and μχ total at most T^(2η). -/
lemma three_lines_bound_of_LFunction_eq_zero : ∃ C,
  ∀ {η T : ℝ} {q} [NeZero q] {χ : DirichletCharacter ℂ q} {s}, 0 < η → χ.IsPrimitive → χ ≠ 1 →
  χ (-1) = (-1) ^ j.1 → 0 < T → q ≤ T ^ 2 → thetaTailIntegral j (χ ·) T⁻¹ + thetaTailIntegral j
  (fun n ↦ χ n * μ n) T⁻¹ ≤ T ^ (2 * η) → χ.LFunction s = 0 → 1 / 2 + 9 * η ≤ s.re → s.re ≤ 1 →
  ‖gaussianMellin j s‖ ^ 2 ≤ C / T ^ (2 * η) := (@gaussianMellin_differentiableOn_and_bdd j).2.imp'
  (9 + · ^ 2) fun G g η T q _ χ s _ hχ h1 hp hT hq J Z _ _ ↦ by
  have T1 := (one_le_sq_iff₀ hT.le).1 (hq.trans' (by simp [succ_le_iff]))
  obtain ⟨n, X⟩ := norm_mul_moebius_le_one χ,
    one_le_pow₀ (one_le_rpow T1 (by bound : 0 ≤ 2 * η)) (n := 2)
  -- `mellin f` is the Mellin transform of `f`, the series for `χ μ` cut at `1 / T`; `B` bounds it
  let f := (Ioi T⁻¹).indicator (gaussianTheta j fun n ↦ χ n * μ n)
  obtain ⟨⟨p, _, A⟩, b, _, B⟩ := mellin_differentiableOn_and_bounded
    (norm_gaussianTheta_char_le h1 hp), mellin_differentiableOn_and_bounded (D := 3 * T) (f := f)
    fun {t} k ↦ by
    by_cases i : T⁻¹ < t <;> simp [f, i, hT.le, exp_pos]
    grw [(summable_and_norm_gaussianTheta_le n k).2, mul_right_comm, ← div_inv_eq_mul _ T, i]
  let a := (9 + G ^ 2) * (T ^ (2 * η)) ^ 2
  have e w : mellin f w = _ := @indicator_smul .. ▸ setIntegral_indicator (by simp)
  refine .trans (.trans_eq' (norm_le_interp_of_mem_verticalClosedStrip' (z := s) (a := a) (b := a /
    T) (by bound) ⟨by bound, by bound⟩ (((gaussianMellin_differentiableOn_and_bdd.1.fun_pow
    2).fun_sub (p.fun_mul b)).mono (closure_preimage_re _ ▸ by grind [closure_Ioo])).diffContOnCl
    ⟨_, forall_mem_image.2 fun z k ↦ norm_sub_le_of_le (by simp; grw [g z k]) (norm_mul_le_of_le
    (A z k) (B z k))⟩ ?_ ?_) (by simp [mellin_gaussianTheta_char, *, show 0 < s.re by bound])) ?_
  any_goals intro z (hz : _ = _)
  -- on `re z = 1/2`: bound `mellin f` and `Γ_j L` by tail integrals; then use `J`
  · have N r g (k : 0 ≤ r) : _ ≤ thetaTailIntegral j g r := (norm_integral_le_integral_norm fun t ↦
      ofReal t ^ (z - 1) • gaussianTheta j g t).trans_eq (setIntegral_congr_fun (by simp) fun t
      i ↦ by norm_num [hz, rpow_neg, k.trans_lt i, le_of_lt, sqrt_eq_rpow]; ring)
    grw [norm_sub_le, norm_mul, norm_pow, g, e, inter_eq_right.2, N, mellin, N,
      thetaTailIntegral_zero_le_two_mul h1 hp hχ
      hT, two_mul_le_add_sq, pow_add_pow_le, J] <;> norm_num [hz] <;> first | positivity | nlinarith
  -- on `re z = 2`: `Γ_j² - Γ_j L · mellin f = Γ_j L ∫_0^{1/T} θ^μ(t) t ^ z dt / t`
  · have I := (integrableOn_exp_neg_Ioi 0).const_mul 3
    have P {c} h t k : ‖ofReal t ^ (z - 1) • gaussianTheta j c t‖ ≤ 3 * rexp (-t) :=
      (norm_mul_le_of_le
      le_rfl (summable_and_norm_gaussianTheta_le h k).2).trans_eq (by norm_num [k, hz]; field)
    erw [sq, ← mul_one (_ * _), ← mul_mu_eq_one χ, mul_mul_mul_comm, ← mellin_gaussianTheta,
      ← mellin_gaussianTheta n]
    grw [← mul_sub, e, norm_mul, mellin, norm_integral_le_of_norm_le I (ae_restrict_of_forall_mem _
      (P _)), integral_const_mul, integral_exp_neg_Ioi_zero, mellin, ← setIntegral_sdiff _
      (I.mono' (by fun_prop [gaussianTheta, gaussianMonomial]) (ae_restrict_of_forall_mem _ (P n))),
      norm_setIntegral_le_of_norm_le_const _ fun t j ↦ by grw [P n t j.1, ← j.1.out]]
    all_goals simp [hT.le, field] <;> nlinarith
  simp (disch := positivity) [← log_le_log_iff, a, field]
  nlinarith [log_nonneg T1]

/-- If m ≥ 1 and neither m nor 2m is a square, then |∑_{1 ≤ v ≤ X} (−v/m)| ≤ 2√m (1 + log m) for
all X; the factor at 2 of the Jacobi symbol is the principal character. -/
lemma norm_sum_jacobiSym_le {m} (hm : m ≠ 0) (h : ¬IsSquare m) (h' : ¬IsSquare (2 * m)) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, (J(-v | m) : ℂ)‖ ≤ 2 * √m * (1 + .log m) := by
  choose ψ E using @induction_on_primes (fun b ↦ ∃ ψ : DirichletCharacter ℂ b, b ≠ 0 → ∀ v : ℤ,
    ψ v = J(v | b)) (by simp) ⟨1, by simp [@Subsingleton.eq_one (ZMod 1)]⟩ fun p _ hp ⟨ψ, _⟩ ↦
    mul_comm _ p ▸ ⟨@quadTwist _ ψ _ ⟨hp⟩, by simp_all [quadTwist_apply, mul_right', to_jacobiSym]⟩
  grw [← @polya_vinogradov m ⟨hm⟩ (ψ m) (fun e ↦ ?_) X]
  · obtain k | k := (ψ m).even_or_odd <;> simp [← E, hm, k.eval_neg]
  obtain ⟨a, c, rfl, ha⟩ := m.sq_mul_squarefree
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, ⟨b, rfl⟩, o⟩ := a.eq_two_pow_or_exists_odd_prime_and_dvd
  exacts [h ⟨c, by ring⟩, h' ⟨2 * c, by ring⟩, by grind [squarefree_pow_iff],
    @quadTwist_ne_one b (ψ b) p ⟨hp⟩ (by grind) (by grind [Nat.squarefree_mul_iff])
    ((@changeLevel_eq_one_iff _ _ _ _ ⟨hm⟩ _ (by simp [mul_comm])).1 (MulChar.ext fun u ↦ by
    have := congr($e (u.1.cast : ℤ))
    rw [changeLevel_eq_cast_of_dvd, ← intCast_cast, quadTwist_apply]
    simp_all [to_jacobiSym, ↓E, mul_right', sq, ← Int.cast_mul]; grind [trichotomy]))]

/-- Mean value estimate. For j ≤ 1, η > 0, t ≥ 1/T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} |∑_{n
≥ 1} c(n) (−v/n) g(nt)|² ≤ C T² t^{−1−2η}, with g = `gaussianMonomial` j and C = C(j, η). -/
lemma sum_sq_gaussianTheta_jacobiSym_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ t ≥ T⁻¹,
    ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X,
    ‖gaussianTheta j (fun n ↦ c n * J(-v | n)) t‖ ^ 2 ≤ C * (T ^ 2 * t ^ (-1 - 2 * η)) := by
  have b v m : ‖(J(v | m) : ℂ)‖ ≤ 1 := mod_cast by grind [trichotomy]
  have R l (hl : 0 < l) : ∃ C > 0, ∀ x > 0, |gaussianMonomial j x| ≤ C * x ^ (-l : ℝ) :=
    ⟨3 * l ^ l, by bound, fun x hx ↦ (norm_gaussianMonomial_le hx.le).trans (by
    have := log_le_self (div_pos hx hl).le
    simp (disch := positivity) [← log_le_log_iff, le_div_iff₀] at *; linarith)⟩
  obtain ⟨⟨A, _, hA⟩, ⟨B, _, hB⟩, Z, w⟩ := R (1 / 2 + η) (by bound), R (3 / 2 + η) (by bound),
    summable_pnat_iff_summable_nat.2 (summable_nat_rpow.2 (by bound : -1 - η / 2 < _)).norm,
    (fun v ↦ v.mul_norm (v.mul_norm v)) (summable_nat_rpow.2 (by bound : 2 * -(1 / 2 + η) < _)).norm
  -- the majorant: a sum over the triples `(a, b, u)` with `k n = a b²`, `m = a u²`, and a product
  refine ((summable_sum (s := {1, 2}) fun (k : ℕ+) _ ↦ ((w.hasSum.tsum_fiberwise fun (a, b, u) ↦
    ((b * (b * a) / k).toPNat', (a * u ^ 2).toPNat')).summable.mul_left (A ^ 2 * k ^ (1 / 2 + η))
    ).norm).add ((Z.mul_norm Z).mul_left ((2 * B) ^ 2 * rexp η / η))).imp
    fun K L T hT t h X hX c hc ↦ ?_
  have ht : 0 < t := by grw [h]; bound
  -- expand the square
  refine .trans (by simpa [mul_conj'] using mod_cast le_norm_self _) ((hasSum_sum
    (s := Ioc 0 X) fun v _ ↦ (fun s ↦ s.hasSum.mul s.hasSum.star (s.norm.mul_norm s.star.norm
    ).of_norm) (@summable_and_norm_gaussianTheta_le j _ t (fun n ↦ mul_one (1 : ℝ) ▸
    norm_mul_le_of_le (hc n) (b (-v) n)) ht).1).norm_le_of_bounded (L.mul_right _) fun (n, m) ↦ ?_)
  conv_lhs => simp [mul_right_comm _ _ (ofReal _), mul_mul_mul_comm _ (Int.cast _), ← Int.cast_mul,
    ← mul_right, ← mul_sum]
  -- if `k n m` is a square, `k = 1` or `2`, the trivial bound; else Pólya–Vinogradov
  obtain ⟨k, i, r, e⟩ | k := em (∃ k ∈ ({1, 2} : Finset ℕ+), IsSquare (k * (n * m) : ℕ))
  obtain ⟨g, p, u, o, s, f, rfl⟩ := exists_coprime' (by simp : 0 < gcd (k * n) r)
  obtain ⟨a, rfl⟩ : p ∣ g := (s.pow_right 2).dvd_mul_left.1 ⟨m, Nat.mul_left_cancel o (by grind)⟩
  map_tacs [grw +useKAbstract [hc, hc, hA, hA, norm_sum_le_of_le _ fun _ _ ↦ b .., show ∑ _ ∈ _, _ ≤
    T ^ 2 by simpa, ← norm_nonneg, ← single_le_sum _ i, ← le_norm_self, ← Summable.le_tsum (by apply
    w.subtype) ⟨(a, p, u), by simp [← f, show a * u ^ 2 = m from Nat.mul_left_cancel (mul_pos o o)
    (by grind)]⟩, ← mul_rpow, ← mul_rpow, rpow_mul, show _ ^ (2 : ℝ) = (k * (n * m) : ℝ) by
    rify at e; simp; grind]; (simp at k; grw +useKAbstract [hc, hc, hB, hB,
    norm_sum_jacobiSym_le _ k.1
    k.2, show 1 + _ = (rexp 1 * (n * m)).log by simp, log_le_rpow_div (ε := η / 2), ← sum_nonneg])]
  all_goals simp (disch := positivity) [← log_le_log_iff, mul_nonneg] <;>
    linarith [T.log_inv, log_le_log (by bound) h]

/-- For j ≤ 1, η > 0, T > 0, X ≤ T² and |c| ≤ 1: ∑_{1 ≤ v ≤ X} ∫_{1/T}^∞ |∑_{n ≥ 1} c(n) (−v/n)
g(nt)| dt/√t ≤ C T^{2+η}, with g = `gaussianMonomial` j and C = C(j, η). -/
lemma sum_thetaTailIntegral_le (hη : 0 < η) : ∃ C, ∀ T > (0 : ℝ), ∀ X : ℕ, X ≤ T ^ 2 → ∀ c : ℕ → ℂ,
    (∀ n, ‖c n‖ ≤ 1) → ∑ v ∈ Ioc 0 X, thetaTailIntegral j (fun n ↦ c n * J(-v | n)) T⁻¹ ≤ C * T ^
  (2 + η) := (sum_sq_gaussianTheta_jacobiSym_le j hη).imp' (√· / η) fun C H T hT X hX c hc ↦ by
  grw [← sum_filter_of_ne fun _ _ ↦ mt integral_undef, ← integral_finsetSum,
    setIntegral_mono_of_nonneg _ (fun t ht ↦ ?_) ((integrableOn_Ioi_rpow_of_lt (a := -1 + -η)
    ..).const_mul (√C * T ^ 2)), integral_const_mul, integral_Ioi_rpow_of_lt]
  any_goals have := (inv_pos.2 hT).trans ht; nth_grw 1 [filter_subset, ← sum_div,
    le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq, show #_ ≤ T ^ 2 by simpa, H T hT t ht.le]
  all_goals simp (disch := positivity) [inv_rpow, rpow_sub, rpow_neg, two_mul, rpow_add, field, *]
  intros; positivity

/-- Zero-density bound for quadratic twists: for ξ mod N, η > 0 and real y, only O(x^{1−η/2})
primes d ≤ x, d ≡ 7 mod 8, d ∤ N, have a zero of L(s, ξ·(·/d)) with Re s ≥ 1/2 + 9η, |Im s|
≤ y.

Known result: Zero density for quadratic twists by mean values over real characters. -/
lemma zero_density_quadTwist (hη : 0 < η) (y : ℝ) : (fun x : ℕ ↦ (#{d ∈ Ioc 0 x |
    ∃ _ : Fact d.Prime, d % 8 = 7 ∧ N.Coprime d ∧ ∃ s, 1 / 2 + 9 * η ≤ re s ∧ |im s| ≤ y ∧
    entireL (quadTwist ξ d) s = 0} : ℝ)) =O[atTop] fun x ↦ (x : ℝ) ^ (1 - η / 2) := by
  obtain ⟨M, f, ψ, _, e, rfl⟩ := exists_isPrimitive_changeLevel_eq ξ
  obtain ⟨j, hp⟩ : ∃ j : Fin 2, ψ (-1) = -(-1) ^ j.1 := by simpa using! ψ.even_or_odd.symm
  obtain ⟨⟨K, hK⟩, ⟨C, hC⟩, c, c0, hc⟩ := three_lines_bound_of_LFunction_eq_zero j,
    sum_thetaTailIntegral_le j hη, @exists_pos_le_norm_gaussianMellin j
    (.Icc 2⁻¹ 1 ×ℂ .Icc (-y) y) (isCompact_Icc.reProdIm isCompact_Icc) (by grind [mem_reProdIm])
  refine .of_bound (2 * C * M ^ (1 - η / 2)) ((((tendsto_rpow_atTop hη).eventually_gt_atTop
    (K / c ^ 2)).natCast_atTop.and (Ioi_mem_atTop 0)).mono fun x ⟨hx, x0⟩ ↦ ?_)
  obtain ⟨T, T0, hT⟩ : ∃ T > 0, T ^ 2 = (M * x : ℝ) := ⟨√_, by simpa, sq_sqrt (by simp)⟩
  have hX : x ≤ T ^ 2 := by simp [succ_le_iff, *]
  rw [Real.norm_natCast, ← mul_le_mul_iff_left₀ (rpow_pos_of_pos T0 (2 * η)), ← nsmul_eq_mul,
    ← sum_const, sum_filter]
  refine .trans (sum_le_sum fun d hd ↦ ?_) ((sum_add_distrib.trans_le (add_le_add (hC T T0 x hX
    (ψ ·) (by simp)) (hC T T0 x hX _ (norm_mul_moebius_le_one ψ)))).trans_eq (by simp (disch :=
    bound) [mul_assoc, abs_of_nonneg, ← mul_rpow, ← hT, ← rpow_natCast_mul, ← rpow_add]; ring_nf))
  split <;> [obtain ⟨_, h8, co, s, s₀, s₁, z⟩ := ‹_›; positivity]
  contrapose! hx
  obtain ⟨h, r⟩ := co.of_dvd_left f, le_of_not_ge (entireL_ne_zero _ · z)
  have h1 ξ := quadTwist_ne_one ξ d (by omega) h
  simp [entireL, h1, show quadTwist (ψ.changeLevel f) d = (quadTwist ψ d).changeLevel (by gcongr) by
    simp [quadTwist, ← changeLevel_trans], LFunction_changeLevel,
    prod_euler_factor_ne_zero _ (by bound : s.re ≠ 0)] at z
  grw [hX, ← rpow_natCast_mul, le_div_comm₀, hc s ⟨⟨by bound, r⟩, abs_le.1 s₁⟩, hK hη _ (h1 ψ) (by
    simpa (disch := omega) [hp, legendreSym.at_neg_one, ↓χ₄_nat_three_mod_four] using
    quadTwist_apply ψ d (-1)) T0 (by simp [hT, mem_Ioc.1 hd])] <;> try bound
  -- reciprocity and `(2/d) = 1` give `(n/d) = (-d/n)`
  · have E {n : ℕ} (h : n ≠ 0) : quadTwist ψ d n = ψ n * J(-d | n) := by
      let ⟨k, m, hm, e⟩ := exists_eq_two_pow_mul_odd h
      simpa [hm.pos.ne', mul_left, pow_left, at_two, qrSign, mul_right', pow_right, mod_left (-d) 2,
        *, Int.odd_iff.1, jacobiSym.neg, to_jacobiSym, quadratic_reciprocity' hm, ← natCast_mod,
        odd_iff, (by omega : d % 2 = 1 ∧ d % 4 = 3)] using quadTwist_apply ψ d n
    simpa [thetaTailIntegral, gaussianTheta, E, mul_right_comm] using hx.le
  -- the twist of a primitive character by the Legendre symbol of a new prime is primitive
  clear * - e h h1
  have H B := (conductor_mul_dvd_lcm_conductor (quadTwist ψ d) B⁻¹).trans (Nat.lcm_dvd_mul ..)
  obtain := H (quadTwist 1 d), H (ψ.changeLevel ⟨d, rfl⟩), h1 1,
    (@quadTwist 1 1 d _).conductor_dvd_level, (quadTwist ψ d).conductor_dvd_level.antisymm
  simp_all [quadTwist, dvd_prime Fact.out, mul_comm, h.dvd_mul_left, eq_one_iff_conductor_eq_one,
    h.symm.dvd_mul_left, conductor_inv, h.mul_dvd_of_dvd_of_dvd, conductor_changeLevel, IsPrimitive]

/-- Let β > 1/2, y real, and a a unit mod N whose primes are ≡ 7 mod 8 and prime to N. For some
prime d ≡ a, no L̃(s, ξ·(·/d)), ξ mod N, vanishes on re s ≥ β, |im s| ≤ y; L̃ is `entireL`.

Known result: Zero density for quadratic twists by mean values over real characters. -/
lemma exists_entireL_quadTwist_ne_zero {β} y {a : ZMod N} (hβ : 1 / 2 < β) (ha : IsUnit a) (H :
  ∀ d : Primes, d = a → d.1 % 8 = 7 ∧ N.Coprime d) : ∃ d : Primes, d = a ∧ ∀ ξ s,
  β ≤ re s → |im s| ≤ y → entireL (@quadTwist
  N ξ d _) s ≠ 0 := (exists_pos_mul_lt (lt_min one_pos (sub_pos.2 hβ)) 9).elim fun η ⟨hη, h⟩ ↦ by
  by_contra!
  refine not_summable_residueClass_prime_div ha ((LSeriesSummable_logMul_of_lt_re (s := 1)
    ((LSeriesSummable_of_sum_norm_bigO (s := 1 - η / 2 / 2) (f := fun n ↦ ite (n.Prime ∧ n = a) 1 0)
    (.trans (.of_norm_le fun x ↦ ?_) (.fun_sum (s := ⊤) fun ξ _ ↦ @zero_density_quadTwist N _ ξ _ hη
    y)) (by grind) (by simpa)).abscissaOfAbsConv_le.trans_lt (mod_cast by simpa))
    ).norm.of_norm_bounded (by simp +contextual [Set.indicator, term, apply_ite, ite_and,
    ← natCast_log, vonMangoldt_apply_prime]))
  simp [apply_ite norm, ← cast_sum]
  grw [← card_biUnion_le, card_le_card]
  simp_all [Primes, subset_iff]; grind
end

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
