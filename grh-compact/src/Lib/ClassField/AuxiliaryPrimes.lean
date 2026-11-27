import Lib.GaloisRep.ZeroSymmetry
import Lib.ClassField.PolarLandau

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
