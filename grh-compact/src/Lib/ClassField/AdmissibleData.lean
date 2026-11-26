import Lib.ClassField.TightFrameExists
import Lib.ClassField.FormalParameter
import Lib.ClassField.PeriodDefs

section
/-! Tight frames and an integral standard theta function. The lattice of the standard theta function
has tight frames (substitutes for an orthonormal basis) of every large length, Fourier inversion
relates the function to products of theta functions of the CM curve, the scaled function has
integral torsion values with bounded conjugates, and jet bounds pass to its translates. Eutactic
stars, the isogeny formula for theta functions and integrality via torsion values are known. Related
work: Conway–Sloane, Low-dimensional lattices V, 1989; Finis, Divisibility of anticyclotomic
L-functions and theta functions with CM (Lemma 3.1), 2006; Mumford, On the equations defining
abelian varieties I, 1966.

Set-up for this proof: dictionaries between two encodings of the same objects.

This file: The jet series of a Weil vector is the Taylor series of its theta function. Curve theta
products along tight frames: translates, jets, integral values, relation to the vacuum. -/

open Finset CMLattice Complex ComplexConjugate Fintype MeasureTheory MvPowerSeries NormedSpace
  NumberField Space WeilData

/-- For V with all signs 1 and f in the finite part, the Taylor series at 0 of u ↦ Θ_f(u·a·v) is
obtained from T_a f by substituting v_i·u for each variable z_i. -/
lemma Space.taylor_line_eq_subst_jetSeries {E n} [Field E] [CMType E] [WeilData E] [Fintype n] {V :
  Space E n 1} {f} (hf : f ∈ V.finitePart) a v : taylorAtZero (entireTheta f <| a • · • v) =
  (V.jetSeries a f).subst (linearSeries fun _ ↦ v ·) := by
  ext k
  let L := a • ∑ p, innerSLFlip ℂ (v p) ∘SL .proj p
  rcases (hasFPowerSeriesAt_iff (p := .ofScalars ℂ _) (z₀ := 0).2
    (.of_forall fun t ↦ by simpa [mul_pow, mul_assoc, div_eq_inv_mul, mul_left_comm] using
    hasSum_integral_of_dominated_convergence (μ := realMeasure _) _ (by fun_prop [realVac]) (fun _ ↦
    .of_forall (by simp; grw [L.le_opNorm ·, norm_apply_le])) (by simp [Summable.mul_right,
    expSeries_div_summable]) (by simpa [tsum_mul_right, exp_eq_tsum_div, Real.exp_eq_exp_ℝ,
    mul_assoc] using (integrable_exp_mul_realVac (_ * _)).mul_const _) (.of_forall fun w ↦
    .mul_right
    (realVac w * f (realVec w)) (expSeries_div_hasSum_exp (t * L w))))).choose_spec.factorial_smul 1
    k, (jet_subst_linearSeries (.replicateCol _ v) (.X () ^ k) (V.jetSeries a f)).symm
  simp_all [entireTheta_eq_integral, L, mul_sum, linSubst, MvPolynomial.X_pow_eq_monomial, ↓map_pow,
    mul_assoc, ↓theta_integrated,
    holCoord_eq, iteratedDeriv, mul_left_comm, exp_eq_exp_ℂ, linearSeries]

variable {P s} {E : Type} {n} [Fintype n] {ε} (V : Space (Parameters.E P s) n ε) [i : V.IsStd]

lemma Space.eq_zero_of_jetSeries_eq_zero [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f}
  (hf : f ∈ V.finitePart) {a} (ha : a ≠ 0) (h : V.jetSeries a f = 0) : f = 0 := eq_zero_of_realVec
  fun y ↦ by simpa [entireTheta, realVac, *] using congr($(eq_of_taylorAtZero_eq (g := 0) (by
  fun_prop (disch := aesop)) (by simp) ((taylor_line_eq_subst_jetSeries hf a y).trans
  (h ▸ (subst_coe 0).trans (by aesop)))) a⁻¹)

/-- Let all signs be +, f ∈ 𝒲_f, G_i entire, and Θ_f(cz) = ∏G_i(μ_{c,i}·z) for all c, z. Then
θ(f) = ∏G_i(0), and for every c the series T_c f is the product of the Taylor series of the
G_i at the linear forms μ_{c,i}·z. -/
lemma Space.jetSeries_eq_prod [Field E] [CMType E] [WeilData E] {V : Space E n 1} {f} (hf :
  f ∈ V.finitePart) {I} [Fintype I] {G : I → _} {μ : ℂ → I → _} (hG : ∀ i, Differentiable ℂ (G i))
  (h : ∀ c z, entireTheta f (c • z) = ∏ i, G i (μ c i ⬝ᵥ z)) : V.θ f = ∏ i, G i 0 ∧ ∀ c,
  V.jetSeries c f = ∏ i, (taylorAtZero (G i)).subst (linearSeries (μ c i)) :=
  ⟨by simpa [entireTheta, realVac] using h 0 0, fun c ↦ by
  ext α
  have H {v S} (f := fun _ ↦ ()) : (truncFinset ℂ _ S).eval v = (rename f (rescale v S)).coeff
    (α.mapDomain f)
  simp [truncFinset, coeff_rename, MvPolynomial.eval_monomial]; ac_rfl
  rw [← coeff_truncFinset_of_mem, MvPolynomial.funext fun v ↦ (H.trans ?_).trans H.symm,
    coeff_truncFinset_of_mem] <;> simp
  have := (taylor_line_eq_subst_jetSeries hf c v).symm
  simp_all [← coe_substAlgHom, PowerSeries.subst, substAlgHom_comp_substAlgHom_apply, mul_comm _
    (_ ⬝ᵥ v), linearSeries, -substAlgHom_apply, substAlgHom_X, rename_eq_subst, rescale_eq_subst]
  congr; induction @univ I _ using cons_induction <;> simp (disch := fun_prop) [*, ↓prod_cons,
    smul_smul, ← sum_smul, PowerSeries.rescale_eq_subst]
  tauto⟩

attribute [local simp] Parameters.areaScale WeilData.j dotProduct funext_iff mul_assoc
  thetaShift_prod

lemma Parameters.latticeModule_cmCurve : P.cmCurve.latticeModule =
  QuadField.scaledIdeal _ (P.Ω₀, 1) := by grind [Ω₀, cmCurve]

/-- The period Ω₀ lies in the lattice of the CM datum 𝓔 (`Parameters.cmCurve`). -/
lemma Parameters.omega₀_mem_cmCurve_lattice : ↑P.Ω₀ ∈ P.cmCurve.Λ :=
  (latticeModule_cmCurve ▸ QuadField.mem_scaledIdeal).2 (by simp)

@[simp] lemma Parameters.norm_map_psi₀ {F R} [NormedField R] [FunLike F ℂ R] [MonoidHomClass F ℂ R]
  (ι : F) z : ‖ι (stdLattice.psi₀ (P.E s) z)‖ = 1 :=
  ((ι : _ →* R).isOfFinOrder (isOfFinOrder_ψf _)).norm_eq_one

/-- For V standard, (w, m) a tight frame of length M, δδ̄ = N ≠ 0, a ∈ Λ, area(C) =
|a|²M√d/(2N): a product of degree-m_i monomials at (a/δ̄)w_i†z_k comes from some F ∈ 𝒲_f,
compatibly with rational translations (theta values, Taylor series), integral-valued, with data
`Space.VacuumExpansion`.

Tight frames and an integral standard theta function. -/
lemma Parameters.exists_finitePart_of_isTightFrame {M N : ℕ} {I} [Fintype I] {w m} (δ : 𝓞 P.K) (h0 :
  N ≠ 0) (hN : δ * conj (δ : ℂ) = N) (hw : IsTightFrame w m M) (x : I × n → _) (hx : ∀ i,
  CMLattice.monomialDeg (x i) = m i.1) ⦃C : CMLattice P.d⦄ ⦃a⦄
  (ha : a ∈ C.Λ) (hA : C.area = ‖a‖ ^ 2 / N * M * √P.d / 2) : ∃ F ∈ V.finitePart,
  (∀ γ, let G i := C.twistedTranslate (m i.1) (a / conj ↑δ * -∑ τ,
    Φ τ (γ i.2) * conj (Φ τ (w i.1))) (C.monomialSection (x i))
  V.θ (V.ϱ (finVec (finiteImage γ)) F) = ∏ i, G i 0 ∧ ∀ c, V.jetSeries c (V.ϱ (finVec (finiteImage
    γ)) F) = ∏ i, (taylorAtZero (G i)).subst (linearSeries fun y ↦ if y.2 = i.2 then a / conj ↑δ /
    P.areaScale * c * conj (Φ y.1 (w i.1)) else 0)) ∧ (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ
  (F (finVec x))‖ ≤ 1) ∧ Nonempty (V.VacuumExpansion (algebraMap P.K _ δ) N F) := by
  generalize e : a / _ = b
  obtain ⟨⟨⟩, ⟨⟩⟩ := (div_eq_iff (by grind [Nat.cast_ne_zero])).1 e, i.1
  exact have hl i {y} h := mul_comm _ (b * _) ▸ C.5 (herm_mem_quadInt y h (hw.1 i)) ha
    let A (i : I × n) : _ →L[ℂ] ℂ := ∑ τ, (b / P.areaScale * conj (Φ τ (w i.1))) • .proj (τ, i.2)
    have B u v : (∑ i, (m i.1 • C.hermitianForm).pullForm (A i)) u v = star u ⬝ᵥ v := by
      have := by simpa [*] using (area_pos C.1).ne'
      convert congr(∑ k, ∑ σ, ∑ τ, conj (u (τ, k)) * v (σ, k) / M * $(hw.2 τ σ)) <;>
        simp [A, *, mul_pow, ← mul_conj', mul_sum, sum_prod_type_right, @sum_comm I]
      congr! 4
      simp [← ofReal_pow √_, field, Real.pi_nonneg, *]
    have R γ i : A i (realImage γ) = b * ∑ τ, Φ τ (γ i.2) * conj (Φ τ (w i.1)) := by
      simp [A, mul_sum, realImage, realCoord, val_scaleIdele_fst, Real.sqrt_div_self]
      have := NeZero.ne P.d; congr; simp [field, *]
    (V.exists_entireTheta_eq (b := conj (quadGen P.d) • 1) (S := ∏ i, C.monomialSection (x i) ∘ A i)
      (by simp [traceOne, quadGen, map_ofNat]) B (by exact coe_mem_Ô (algebraMap _ _ δ)) h0 ((Φ
      1).injective (by simpa)) (by rw [prod_fn]; fun_prop) fun γ hγ ↦ by simp [R, normalizedShift,
      riemannForm_pullForm, ← mul_sum, canonicalMultiplier, multiplier_eq_canonicalMultiplier,
      by simpa using (hl · <| hγ ·), ← Complex.exp_sum, hx _ ▸ thetaShift_of_mem
      (monomialSection_mem ..), ← Complex.exp_nsmul, mul_left_comm (m _ : ℂ)]).imp fun F ⟨hF, _,
      D⟩ ↦ (fun H ↦ ⟨hF, H, fun _ _ _ x ↦ (exists_finiteImage_approx hF x).elim fun γ e ↦
      (exists_forall_mul_mem_Ô (finiteImage γ)).elim fun M h ↦ by
    grw [← θ_ϱ, ← e.2, (H γ).1, map_prod, norm_prod, Finset.prod_le_one₀ (by simp) fun i _ ↦ ?_]
    grw [← hx, ← mul_zero 0, C.norm_translate_le_naiveHeight_pow (N := 0) _ _ (N * M) _ _
      (C.norm_monomialSection_le _)] <;> simp [*]
    simpa [← hN, mul_left_comm b, ← mul_sum] using! C.latticeModule.smul_mem δ (@hl _ (M * _) (by
      simpa [finiteImage, mul_left_comm] using h.2 _)), D⟩) fun γ ↦
      jetSeries_eq_prod (rho_finVec_mem_finitePart _ hF) (by fun_prop) (by
      simp [entireTheta_translate_finiteImage _ V B, *]; simp [A, sum_prod_type, mul_sum]; grind)
end

section
/-! Part of: Normal form of theta series at non-split primes (see New.Curve.FormalParameter).

This file: Theta products along tight frames: integral up to one exponential coupling partner
places. -/

open MvPowerSeries Finset ComplexConjugate LinearTopology NumberField IsLocalRing CharP


attribute [local simp] subst_comp_subst_apply subst_mul subst_smul constantCoeff_subst_eq_zero
  sum_pow_char_pow smul_sum pderiv_X sum_pow_char smul_pow Real.rpow_neg norm_p_eq_inv
variable {p Q J} [fp : Fact p.Prime] [CommRing Q] [CharP Q p] [Fintype J] (P : Parameters) (s)

/-- In characteristic p, let e = 2, or e = 1 and ρ hold; let t_i − t_i^{p^e} = L_i and t_i^{p^n}
= 0 for n ≥ B. If ∑L_i^{p^j+1} = 0 for odd j (all j if ρ), then ∑t_i^{p+1} = 0 and
∑t_i^{p+p^e} = 0. -/
lemma sum_pow_eq_zero_of_null {B e ρ} {t L : J → Q} (he : e = 1 ∧ ρ ∨ e = 2) (ht : ∀ i,
  t i - t i ^ p ^ e = L i) (t0 : ∀ i, ∀ n ≥ B, t i ^ p ^ n = 0) (hq : ∀ j, Odd j ∨ ρ → ∑ i, L i ^
  p ^ j * L i = 0) : ∑ i, t i ^ (p + 1) = 0 ∧ ∑ i, t i ^ (p + p ^ e) = 0 := by simp (disch := grind)
  [(eq_sum_pow_of_sub_pow_eq (ht _) B).trans ∘ add_eq_left.2, sum_mul_sum, ← pow_mul,
  @sum_comm _ _ J, ← pow_add p, ← pow_succ, ↓pow_add (t _), fun a b (h : Odd (a + b) ∨ ρ) ↦ (by
  induction a, b using Nat.recDiagAux <;> simp (disch := grind [fp.1.pos]) [*, pow_succ, pow_mul,
    ← mul_pow, ← sum_pow_char, mul_comm (L _)] : ∑ i, L i ^ p ^ a * L i ^ p ^ b = 0)]

/-- Over a commutative ring of prime characteristic p, let power series t_i have t_i(0) = 0, t_i
− t_i^{p²} = ∑_v r_{v,i}X_{v,c}. Then ∑_i r_{x,i}t_i^p has nonzero coefficients exactly at
the X_{y,c}^{p^j} with j odd and ∑_i r_{y,i}^{p^j}r_{x,i} ≠ 0. -/
lemma coeff_sum_frob_ne_zero_iff {Φ I} [Fintype Φ] {r : Φ → J → Q} {t : J → MvPowerSeries (Φ × I) Q}
    (t0 : ∀ i, constantCoeff (t i) = 0) x {c} (ht : ∀ i, t i - t i ^ p ^ 2 = ∑ v, C (r v i) * X
    (v, c)) d : coeff d (∑ i, t i ^ p * C (r x i)) ≠ 0 ↔ ∃ n y,
    ∑ i, r y i ^ p ^ (2 * n + 1) * r x i ≠ 0 ∧ d = .single (y, c) (p ^ (2 * n + 1)) := by
  rcases fp.1.one_lt, charP_of_injective_ringHom (@C_injective (Φ × I) Q _)
  simp (disch := grind [Nat.lt_pow_self]) [congrArg (· ^ p) (eq_sum_pow_of_sub_pow_eq (ht _)
    d.degree), add_pow_char, ← pow_mul, ← pow_succ, ← smul_eq_C_mul, sum_mul, @sum_comm _ _ J,
    coeff_X_pow, coeff_eq_zero_of_constantCoeff_nilpotent (m := 1), ← sum_product']
  use (by grind [exists_ne_zero_of_sum_ne_zero ·]), fun ⟨n, y, _⟩ ↦ by rw [sum_eq_single (n, y)] <;>
    grind [Nat.lt_pow_self, Nat.pow_right_inj, Finsupp.degree_single, Finsupp.single_eq_single_iff]

namespace Parameters

variable [PadicPlace p]

/-- The set of series ∏ι(U_{y_{j,k}}θ)(ι(b w_j†)z_k) over ℂ_p, over j and k ∈ c, with (w_j) a
tight frame of length M, |ιb| = r, nδy_{j,k} ∈ Λ, p prime to Mn;
U_y = `CMLattice.twistedTranslate` 1 y, and θ, Λ are those of `Parameters.cmCurve`. -/
def thetaProducts (δ : 𝓞 P.K) r c [Fintype c] := {Θ | ∃ J, ∃ (_ : Fintype J) (w : J → P.E s), ∃ M n
  b, ∃ y : J × c → ℂ, IsTightFrame w 1 M ∧ Θ = ∏ i, (taylorVia ιₚ (P.cmCurve.twistedTranslate 1 (y
  i) P.cmCurve.θ)).subst (linearSeries fun (τ, k) ↦ ite (k = i.2) (ιₚ (b * conj (Φ τ (w i.1)))) 0) ∧
  (p.Coprime M ∧ p.Coprime n) ∧ ‖ιₚ b‖ = r ∧ ∀ i, n * δ * y i ∈ P.cmCurve.Λ}

/-- Let (p/d) ≠ 1, (w_i) a tight frame of length M, β ∈ 𝔬. Then z_{v,i} = βι(w̄_{i,v}) ∈ 𝔬, and in
characteristic p, modulo elements of valuation ≥ (1 − (p/d))/2,
∑_i z_{v,i}^{p^j} z_{v′,i} is β^{p^j+1}M if
v′ = −p^j v, else 0 (j odd or p = d). -/
lemma exists_frame_rows_frob (hp : chiK P.d p ≠ 1) {w : J → _} {M} (hw : IsTightFrame w 1 M) β :
  ∃ z : _ → _ → valRingCp p, (∀ v i, z v i = β.1 * ιₚ (conj (Φ v (w i)))) ∧ ∀ (Q : Type)
  [CommRing Q] [CharP Q p] (g : _ →+* Q), (∀ x, ‖x.1‖ ≤ p ^ ((chiK P.d p - 1) / 2 : ℝ) → g x = 0) →
  ∀ j, Odd j ∨ p = P.d → ∀ v v', ∑ i, g (z v i) ^ p ^ j * g (z v' i) =
  ite (P.placeOfInt s (-p ^ j) * v = v') (g β ^ p ^ j * g β * M) 0 := by
  let N := P.N₁ s
  let x i := IsIntegralClosure.mk' (𝓞 (P.E s)) (N * w i) (algebraMap_mem_Ô.1 (by
    simpa [N, mul_assoc, finiteImage, WeilData.α] using mul_mem N₁_mul_α_mem (hw.1 i)))
  have hd := hp ∘ @chiK_eq_one_of_dvd P p s fp.1; obtain ⟨α, ⟨⟩⟩ : ↑N ∣ β := IsUnit.dvd (by
    simpa [← residue_ne_zero_iff_isUnit, cast_eq_zero_iff])
  let f v := ((ιₚ.comp (Φ v)).comp (algebraMap _ (P.E s))).codRestrict (valRingCp p)
    (id (norm_ringOfIntegers_le (ιₚ.comp _)))
  use fun v i ↦ f v (star (x i)) * α, by simp [f, x, field], fun Q _ _ g h j _ v v' ↦ ?_
  simpa [by simpa using (frob_ext hd (g.comp (f v)) j (.inr ⟨rfl, rfl⟩)).2 ⟨rfl, by
    obtain ⟨⟨⟨⟩, _⟩ | _⟩ := chiK_cases P.d p, h (f v (P.sqrtNegDInE s)), congr(√‖(f v (algebraMap _
      _ $(QuadField.sqrtNegDInt_sq P.d))).1‖) <;> simp_all [sqrtNegDInE, Real.sqrt_eq_rpow P.d,
      neg_div]⟩, apply_ite, sum_mul, ← iterateFrobenius_def, mul_mul_mul_comm _ (iterateFrobenius Q
    p j _), mul_right_comm _ (M : Q)] using congrArg (g · * (g α ^ p ^ j * g α)) (show
    ∑ i, f v (galOfPlaceInt (P.placeOfInt s (-p ^ j)) (x i)) * f v' (star (x i)) = ite (_ = v') (N *
    N * M) 0 by ext; simpa [f, x, ← phi_mul, mul_comm v, mul_mul_mul_comm _, mul_sum, apply_ite]
    using congr(N * N * ιₚ $(hw.2 ..)))

/-- For (p/d) ≠ 1, some ϖ, π with |ϖ| = p^{−ρ_p} (ρ_p = `nonsplitWeight`),
|π| = p^{((p/d)−1)/2} serve all r ≤ 1 and Θ in
`Parameters.thetaProducts` (δ = 1): `IsIntegralOnNullCone` holds for each B, with couplings
j ≤ log_p B, j odd or p = d. If (p/d) = −1 and r = 1, Θ(ϖz) = exp(κΨ)V with |κ| = p^{1−1/(p−1)}, Ψ,
V integral, Ψ(0) = 0, and ∂_xΨ has unit coefficients exactly at the z_y^{p^j}, j odd, −p^j y = x.

Normal form of theta series at non-split primes. -/
lemma thetaProducts_normal_form (hp : chiK P.d p ≠ 1) : ∃ ϖ π, ‖ϖ‖ = p ^ (-nonsplitWeight P.d
  p) ∧ ‖π.1‖ = p ^ ((chiK P.d p - 1) / 2 : ℝ) ∧ ∀ {I} [Fintype I], ∀ r ≤ 1, ∀ Θ ∈ P.thetaProducts
  s 1 r I, (∀ B, IsIntegralOnNullCone (fun j v ↦ P.placeOfInt s (-p ^ j) * v) {j ≤ p.log B | Odd j ∨
  p = P.d} ϖ π B Θ) ∧ (chiK P.d p = -1 → r = 1 → ∃ (κ : ℂ_[p]) (Ψ V : MvPowerSeries _
  (valRingCp p)), ‖κ‖ = p ^ (1 - 1 / (p - 1) : ℝ) ∧ constantCoeff Ψ = 0 ∧ Θ.rescale (fun _ ↦ ϖ) =
  expSubst (κ • seriesToCp Ψ) * seriesToCp V ∧ ∀ x d, (pderiv x (Ψ.map (residue _))).coeff d ≠ 0 ↔
  ∃ j y, Odd j ∧ (P.placeOfInt s (-p ^ j) * y.1, y.2) = x ∧ d = .single y (p ^ j)) := by
  obtain ⟨⟨e, ϖ, π, S, E, ⟨-, hϖ, hπ, π1, S0, ε, _⟩, H⟩, hP⟩ := P.cmCurve.exists_formal_parameter,
    fp.1
  obtain ⟨_, _, _, R, _, hπ', he, ⟨⟩, ψ0, hV⟩ := H hp (P.thirteen_le_of_chiK_ne_one hP hp)
  set ψ := _ + π • R; use ϖ, π, hϖ, hπ'; rintro I _ _ ha Θ ⟨J, _, w, M, n, b, y, hw, _, hM, ⟨⟩, hy⟩
  choose N κ hκ v ev using hV n hM.2
  obtain ⟨z, hz, hF⟩ := hπ' ▸ P.exists_frame_rows_frob s hp hw ⟨_, mul_mem hκ.1.le ha⟩
  simp [hP.coprime_iff_not_dvd] at hM S0 ψ0 hy
  let c (i : J × I) := @PowerSeries.substAlgHom (valRingCp p) _ _ (valRingCp p) _ _
    (∑ v, z v i.1 • X (v, i.2)) (by simp); let Ψ := ∑ i, c i ψ
  have cX i : c i .X = _ := substAlgHom_X ..
  refine Exists.elim ?_ fun V (⟨Ψ0, eV, cS⟩ : _ ∧ _ ∧ ∀ i, constantCoeff (c i S) = 0) ↦
    ⟨fun B τ Z Z0 hq m hm ↦ ?_, fun h _ ↦ ⟨κ, Ψ, V, by simp [*], Ψ0, eV, fun x d ↦ ?_⟩⟩
  use ∏ i, c i (v (y i) (hy _ _))
  simp (disch := simp [*]) [c, Ψ, map_subst, expSubst_sum, *, PowerSeries.substAlgHom, -map_mul]
  simp [linearSeries, *, PowerSeries.subst, Fintype.sum_prod_type, mul_smul]
  let σ := substAlgHom (R := valRingCp p) (hasSubst_of_constantCoeff_zero Z0)
  have ⟨Q, φ, K⟩ : ∃ Q : CommRingCat, ∃ φ : _ →+* Q, RingHom.ker φ = (basis τ (valRingCp p)
    ((Valuation.leIdeal _ ‖π.1‖₊).toTwoSided, m)).asIdeal := ⟨.of _, _, Ideal.mk_ker⟩
  simp [Ideal.ext_iff, basis, ← NNReal.coe_le_coe] at K
  have hT := (K (σ Ψ)).1 (by
    nontriviality
    have K0 x := by simpa [coeff_C, apply_ite, ite_apply, @forall_comm (_ ≤ m)] using (K (C x)).2
    have := of_eq_zero hP (by simpa [hπ] using K0 p)
    have t0 f e n hn := (K (f ^ p ^ n)).2 fun d h ↦ by
      rw [coeff_eq_zero_of_constantCoeff_nilpotent e (Nat.one_add_le_iff.2 (((d.degree_mono
        h).trans hm).trans_lt (p.lt_pow_of_log_lt hP.one_lt hn)))]; simp
    obtain ⟨E, hq⟩ := (congr(φ <| σ <| c · $ε)), hq φ
    simp [cX, K0, @smul_eq_C_mul τ, -Prod.forall, Fintype.sum_prod_type_right] at E t0 hq
    obtain ⟨hq⟩ := (iff_self_and.2 (sum_pow_eq_zero_of_null (he.imp_right (·.1)) E fun _ ↦ t0 _ (by
      simp [σ, cS, Z0]))).1 fun j h ↦ by
      simp [σ, ↓substAlgHom_X, mul_pow, sum_mul_sum, by simpa using hF _ (φ.comp C) K0 j h,
        mul_mul_mul_comm _ (φ _ ^ _), @sum_comm _ _ J, ← sum_mul, ← mul_sum, Fintype.sum_prod_type]
      by_cases! j ≤ p.log B <;> simp [*]
    simp [ψ, Ψ, *, ← mul_sum, @smul_eq_C_mul τ, sq]
    cases he <;> simp [by simpa using hq 0, *])
  apply_fun subst (seriesToCp <| Z ·) at eV
  simp [σ, ← map_subst, Ψ0, Z0, rescale_eq_subst, PowerSeries.subst] at eV hT
  refine eV ▸ sum_mem fun d h ↦ mul_mem ((PowerSeries.coeff_subst (by simp [*]) ..).symm.subst
    (finsum_induction _ (by simp) @(valRingCp p).add_mem fun k ↦ ?_)) (by simp)
  simp [coeff_pow, mul_sum]; refine sum_mem fun l e ↦ (?_ : ‖_‖ ≤ 1)
  simp at h e ⊢; grw [← rpow_le_norm_factorial, hT] <;> (try simp [*, hP.pos, ← Real.rpow_add,
            ← Real.rpow_mul_natCast, Real.rpow_pos_of_pos]); ring_nf; simp
  grw [← h, ← e.1, ← single_le_sum _ ‹_›] <;> simp
  obtain ⟨⟨⟩⟩ := he.resolve_left (by simp [·, chiK] at h)
  have K (x : valRingCp p) h := (residue_eq_zero_iff x).2 (π1.not_ge <|
    isUnit_integer_iff_norm_eq_one.1 · ▸ h)
  have E i := congr((fun f ↦ (f, pderiv x f)) (map (residue _) (c i $ε)))
  simp [cX, @smul_eq_C_mul (_ × I), K, ← map_natCast C, cast_eq_zero] at E
  simpa [ψ, cast_eq_zero, Ψ, *, ← mul_sum, @smul_eq_C_mul (_ × I), ← map_natCast C, Odd, ite_and,
    Fintype.sum_prod_type, Prod.ext_iff, cast_eq_zero_iff, hF _ _ K] using
    coeff_sum_frob_ne_zero_iff (by simp [cS]) x.1 (E · x.2 |>.1) d
end Parameters
end

section
/-! Known results stated on this proof's data: Galois action on CM theta functions and on the finite
Weil representation (known result; see Lib.CM.Reciprocity.SemilinearWeilLaw).

This file: Galois action on translates of a theta product; integral bounded scaled vacuum values. -/

namespace Parameters

open Real NeZero Space CMLattice Finset Submodule MvPowerSeries Fintype Set Notation

/-- The real number Ω = `Parameters.bigOmega` attached to the parameters P and the exponent s is
positive. -/
lemma bigOmega_pos {P s} : 0 < bigOmega P s := by simp [bigOmega, rootDiscr_pos, pi_pos, exp_pos]

/-- The scale per of the derivatives is non-zero, for all parameters and every s. -/
@[simp] lemma jetScale_ne_zero {P s} :
  jetScale P s ≠ 0 := by simpa [jetScale, periodFactor, ne_of_gt, rootDiscr_pos, ne] using
  (congr($(P.norm_gal_vacuumRoot s 1) / $(P.cmCurve.chowla_selberg.choose_spec.2 1) ≠ 0)).mpr

/-- Some C and, for each s, adeles b_σ serve all standard V of rank n: some c ≠ 0 makes the
values of c·vac integral, with K-conjugates ≤ e^{CN₁²n}; translates of some F ∈ 𝒲_f, θF = 1,
span 𝒲_f; and σT_per ϱ(x)F = T_t ϱ(b_σx)F′ (places permuted), some F′ ∈ 𝒲_f, |t|² = 1/Ω.
Here T_a = `Space.jetSeries` a, per = `Parameters.jetScale`, 𝒲_f = `Space.finitePart`. -/
lemma exists_isJetConjugate_generator P : ∃ C : ℕ, ∀ s, ∃ B : _ → 𝔸f (P.E s), ∀ {n} [Fintype n] {ε}
  (V : Space _ n ε) [V.IsStd], (∃ c ≠ 0, (∀ p [Fact p.Prime] [PadicPlace p] x, ‖ιₚ (c * V.vacElem
  (finVec x))‖ ≤ 1) ∧ ∀ (σ : Gal(ℂ/K P)) x, ‖σ (c * V.vacElem (finVec x))‖ ≤ rexp (C * P.N₁ s ^ 2) ^
  card n) ∧ ∃ F ∈ V.finitePart, V.θ F = 1 ∧ V.finitePart ≤ span ℂ (.range fun x ↦ V.ϱ (finVec x)
  F) ∧ ∀ σ : Gal(ℂ/K P), ∃ t, ∃ F' ∈ V.finitePart, ‖t‖ ^ 2 = (P.bigOmega s)⁻¹ ∧ ∀ x, IsJetConjugate
  σ (placePerm s σ) (P.jetScale s) t (V.ϱ (finVec x) F) (V.ϱ (finVec (B σ • x)) F') := by
  choose Ω hA e he β a hb H using (complex_multiplication_theta _ · latticeModule_cmCurve)
  refine (isAlgebraic_of_padic fun _ ↦ @norm_a₁_le_one _ _ P.cmCurve _ _ ⟨_⟩).elim fun p hp ↦
    (isCompact_iUnion fun x : p.rootSet ℂ ↓∩ .range (@a₁ P.d) ↦
    IsAppellHumbert.isCompact_range_norm_thetaShift (x.2.choose.monomialSection_mem
    (1, 0))).bddAbove.imp' (⌈·⌉₊ + 4) fun M hm s ↦ ⟨finAdeleIncl .. ∘ β, fun V _ ↦ ?_⟩
  let N := P.N₁ s
  have fr (e : ℕ+) := exists_finitePart_of_isTightFrame V (N * e) (ne ((N * e) ^ 2)) (by simp [sq])
    (P.isTightFrame_zeta_pow s N).repeat_vectors (fun _ ↦ (1, 0)) (by simp)
  obtain ⟨F, W, hF, hI, K, x, m, -, hJ, hs⟩ := fr 1 omega₀_mem_cmCurve_lattice
    (by simp [QuadField.area_eq_of_eq_scaledIdeal latticeModule_cmCurve, field, N, ne])
  have h1 := by simpa [monomialSection] using (hF 0).1
  obtain ⟨j, hj⟩ := by simpa [h1] using
    (congr(V.dataInner V.vacElem $(hs V.θ)).symm.trans (map_sum ..)).trans ∘ sum_eq_zero
  have hc := (hs ((m⁻¹ : ℂ) • V.dataInner V.vacElem ∘L V.ϱ (finVec (-x j)))).symm
  set c : ℂ := _ * _
  simp [hj, ↓rho_finVec, congr($(V.heisRep_right_rho _) _) ▸ (V.dataInner_rho_of_vacElem _).trans
    ((adelicSum ..).vac_equiv _), realVac, stdLattice.finVac, ← sum_filter] at hc
  refine have c0 := by simp [c, hj]
    (forall_and.1 fun σ ↦ ?_).imp (⟨c, c0, ?_, ·⟩) (⟨F, W, h1, ?_, ·⟩)
  refine (fr (e σ) (he σ) (by simp [hA, field, N, ne])).elim fun _ ⟨W', h', _⟩ ↦ (fun J ↦ ⟨fun _ ↦
    ?_, σ (P.periodFactor s) / Ω σ * P.areaScale, _, W', ?_,
    J⟩) (denseRange_finiteImage.induction_on · ⟨(isLocallyConstant_rho_finVec
    W).comp₂ ((isLocallyConstant_rho_finVec W').comp_continuous (by fun_prop)) (IsJetConjugate _ _ _
    _) Not⟩ fun γ ↦ ?_)
  any_goals simp_rw [← V.smul_apply, hc, ← θ_ϱ, map_sum]
  · grw [norm_sum_le, sum_le_card_nsmul _ _ (M.exp ^ _), card_le_univ, hJ]; swap
    simp_intro .. [↓rho_finVec, by simpa [rho_finVec_mem_finitePart, W, W'] using
      (congrArg constantCoeff <| J ·)]
    rw [← θ_ϱ, ← (exists_finiteImage_approx W' _).choose_spec.2, (h' _).1, norm_prod,
      ← prod_const]; gcongr
    grw [← add_one_le_exp, ← hm
      ⟨_, ⟨⟨σ • ⟨_, p.mem_rootSet.2 hp⟩, exists_galConjugate ..⟩, rfl⟩, _, rfl⟩]; bound
    simp; grw [le_exp_log N, log_le_self, Nat.le_ceil M, ← numInfPlaces, card_infinitePlace_E,
      Nat.totient_le] <;> simp [← exp_add, ← exp_nat_mul]; clear * -; grind
  convert congr($(P.norm_gal_vacuumRoot s σ) * π / $(P.cmCurve.chowla_selberg.choose_spec.2
    σ)) <;> clear * - hA <;> simp [hA, periodFactor, areaScale, bigOmega, div_pow, mul_pow,
    pi_nonneg] <;> field [ne]
  let t i j := -Algebra.trace P.K _ (γ i * star (P.ζ s ^ @Fin.val N j)) / N
  choose T g h₂ using ((hb σ).frequently ((by fun_prop :
    ContinuousAt (finAdeleIncl _ (P.E s) · • finiteImage γ) _).eventually
    ((isLocallyConstant_rho_finVec W').eventually_eq _))).forall_exists_of_atTop (image₂ t ⊤ ⊤)
  erw [← h₂, adeleMap_algebraMap, algebraMap_smul, ← map_smul]
  simp [IsJetConjugate, hF, ↓h', map_subst, PowerSeries.subst, rename_eq_subst,
    subst_comp_subst_apply]
  congr! 3 with i
  · simp [← rename_eq_subst, linearSeries, ↓smul_eq_C_mul]
    apply Fintype.sum_equiv ((placePerm s σ).prodCongr 1); rintro ⟨⟩
    simp [jetScale, starRingEnd_apply, ← map_star_complex, placePerm_spec, apply_ite σ,
      ← smul_eq_C_mul]; field_simp
  convert! H σ T (t i.2 i.1.1) (g (by simp)) using 2 <;>
    simp [t, monomialSection, coe_trace_eq_sum, -star_ζ, mul_assoc, ← mul_sum] <;> field_simp
  iterate 2 simp [IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg, ↓rho_finVec, *, finitePart,
    span_le,
    (eq_inv_smul_iff₀ c0).2 hc, finHeisOp, smul_sum, smul_smul, sum_smul_mem, mem_span_of_mem]
end Parameters
end

section
/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Record of admissible data; names for ranks, weights, the prime sum, the error budget and
the cost of one direction. -/

noncomputable section

open Set NumberField Real

/-- The constant C + 2d + 6 + N₀ + |`chowlaSelbergConst` d| + ∑_ξ |log |P₀'(ξ)||, with C chosen from
`Parameters.exists_isJetConjugate_generator` and ξ the roots of the cyclotomic polynomial P₀ of
order N₀. -/
def Parameters.c P := (exists_isJetConjugate_generator P).choose + (2 * P.d + 6) +
  (P.N₀ + |chowlaSelbergConst P.d| + ∑ w ∈ primitiveRoots
  P.N₀ ℂ, |‖(Polynomial.cyclotomic P.N₀ ℂ).derivative.eval w‖.log|)

/-- Admissible data: scales x, x₁, b; exponent s and numbers m, r; thick places with a
three-term condition; primes g₀ ≠ g₁ and an integer of K of norm g₀g₁; existence of primes ≡
1 mod M_ω² in short windows. -/
structure Data (P : Parameters) where
  /-- `logX = log x`, `logB = log b`, `logX₁ = log x₁`: the sizes are chosen on the logarithmic
  scale. -/
  (logX logB logX₁ : ℝ) (s m r : ℕ) s_le : s ≤ 32 * logX
  thick : Finset _
  g : Fin 2 → ℕ
  piG : 𝓞 P.K
  scale : 1e12 * P.c ≤ log logB ∧ 100 * log logB ≤ logX ∧ 1e6 * logX ≤ logX₁ ∧ 1e6 * logX₁ ≤ logB ∧
    6 * log logX₁ ≤ log logB
  m_mem : ↑m ∈ Icc (exp (logX / 2)) (2 * exp (logX / 2))
  r_mem : ↑r ∈ Icc (exp (5 * logX)) (3 * exp (5 * logX))
  m_pow : ∃ e, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22
  r_pow : ∃ e, r = 3 ^ (e + 1)
  thick_eq_neg_one_mod {m} (d : m ∣ P.N₁ s) : m ∣ P.N₀ * 3 ^ (.log 3 s + 5) → ∀ σ ∈ thick, P.placeClass d σ = -1
  three_term : let φ := P.placeClass P.two_pow_dvd_N₁; ∀ i j, 0 < i → i < j → j ≤ 324 * s →
         ∀ σ ∈ thick, ∀ τ ∈ thick, ∀ ρ ∈ thick, φ (τ / σ) ^ j = φ (ρ / σ) ^ i → φ (τ / σ) = 1
  g_prime i : (g i).Prime
  g_modEq_one i : g i ≡ 1 [MOD P.N₁ s * P.d]
  dvd_g_sub_one i : P.Mω s ^ 2 ∣ g i - 1
  g_injective : g.Injective
  g_mem i : ↑(g i) ∈ Icc (exp logB ^ 10) (exp logB ^ 11)
  norm_piG : piG * star piG = g 0 * g 1
  exists_prime_window : ∀ U ∈ Icc (100 * logB) (2 ^ s), ∃ p, p.Prime ∧ p ≡ 1 [MOD P.Mω s ^ 2] ∧
    log p ∈ Icc U (U + √logB)

namespace Data

variable {P} (D : Data P) (y : ℝ) (j)

/-- The scale x = exp(logX) of the data, which store its logarithm logX. -/
abbrev x := D.logX.exp

/-- The scale x₁ = exp(logX₁) of the data, which store its logarithm logX₁. -/
abbrev x₁ := D.logX₁.exp

/-- The scale b = exp(logB) of the data, which store its logarithm logB. -/
abbrev b := D.logB.exp

/-- The field E = K(ζ), ζ a primitive root of unity of order N₁ = 3^c 2^s N₀, for the exponent s
of the data. -/
@[reducible] def E := P.E D.s deriving NumberField, CharZero, IsCMField

/-- The set of infinite places of the field E of the data; it is a group, identified with
(ℤ/N₁)^× and with Gal(E/K). -/
protected abbrev Φ := InfinitePlace D.E

/-- The natural number N₁ = 3^c 2^s N₀ (`Parameters.N₁`) for the exponent s of the data. -/
abbrev N₁ := P.N₁ D.s

/-- The number of infinite places of the field E attached to the data. -/
abbrev f := numInfPlaces D.E

/-- The natural number N₁d; the field E embeds in the cyclotomic field of that order. -/
protected abbrev cycloConductor := D.N₁ * P.d

/-- The root discriminant of the number field E attached to the data. -/
abbrev rootDisc := rootDiscr D.E

/-- The rank k = r − m + 1 formed from the numbers r and m of the data, as a natural number: (r
+ 1) − m with truncated subtraction. -/
def k := D.r + 1 - D.m

/-- The natural number t = 5r, where r is the rank in the data. -/
def t := 5 * D.r

/-- The number N₁⌈y/N₁⌉, or 0 if y ≤ 0: the least natural multiple of N₁ that is at least y. -/
def roundUp := D.N₁ * ⌈y / D.N₁⌉₊

/-- The natural number h₂ = r⁸, with r the rank in the data; it is half of the gap between
successive weights. -/
def h₂ := D.r ^ 8

/-- The gap h = 2h₂, twice the half-gap h₂ = r⁸ of the data. -/
def h := 2 * D.h₂

/-- The natural number h₂ − ⌊(t+1)/2⌋, with h₂ half the gap and truncated subtraction. -/
def reducedHalfGap := D.h₂ - (D.t + 1) / 2

/-- The number a: the least multiple of N₁ that is at least xb, with x and b scales of the data. -/
def a := D.roundUp (D.x * D.b)

/-- The least multiple of N₁ that is at least a/x; it is the weight w₀⁻ (`Data.w` less h₂, at j = 0)
at thick places. -/
def b₁ := D.roundUp (D.a / D.x)

/-- The least multiple of N₁ that is at least a/x₁; the weight w₀⁻ (`Data.w` less h₂, at j = 0) at
places that are not thick. -/
def b₂ := D.roundUp (D.a / D.x₁)

/-- The infinite place of E named by the class of the integer ν modulo N₁ if ν is prime to N₁,
and the identity place otherwise. -/
abbrev placeOfInt : D.Φ := P.placeOfInt _ j

/-- The rank n_j = k + j(t + 1). -/
def n := D.k + j * (D.t + 1)

/-- The natural number k + j − 1, the number of positive basis vectors of W_j. -/
abbrev posRank := D.k + j - 1

instance : Fact (D.g j).Prime := ⟨g_prime ..⟩

/-- The product g = g₀g₁ of the two primes of the data. -/
def gProd := D.g 0 * D.g 1 deriving NeZero

/-- The tops: the infinite places of E whose class in (ℤ/N₁)^× is congruent to 1 modulo N₀. -/
def tops : Finset D.Φ := {τ | P.placeClass (P.N₀.dvd_mul_right _) τ = 1}

/-- The weight w_j(σ) = w_j⁻(σ) + h₂ at the infinite place σ, with h₂ half the gap h and
w_j⁻(σ) = b₁ + jh if σ is thick, b₂ + jh if not. -/
def w (σ : D.Φ) := ite (σ ∈ D.thick) D.b₁ D.b₂ + j * D.h + D.h₂

/-- The real weight w(σ), equal to a/x if the infinite place σ is thick and to a/x₁ otherwise. -/
def nominalWeight (σ : D.Φ) := D.a / ite (σ ∈ D.thick) D.x D.x₁

/-- For real y and a place σ, the sum over 1 ≤ ν ≤ a of Λ(ν)(1 − (ν/d))·max(y/ν − w(−ν·σ), 0), with
w = `Data.nominalWeight`. -/
def primeSum σ := ∑ ν ∈ .Icc 1 D.a,
  lambdaClass P.d 1 ν * (y / ν - D.nominalWeight (D.placeOfInt (-ν) * σ))⁺

/-- The error budget f·a·(log b)³, with f the number of infinite places of E, b a scale of the
data and a = `Data.a`. -/
abbrev budget := D.f * D.a * D.logB ^ 3

/-- For a natural number j, the real number log j! − j·log(Ω/g), with Ω = `Parameters.bigOmega` and
g = g₀g₁. -/
def jetSize := log (Nat.factorial j) - j * (P.bigOmega D.s / D.gProd).log

/-- The cost of one direction: the sum over infinite places σ of jetSize(w₀(σ)) − primeSum(w(σ), σ),
with `Data.jetSize`, `Data.primeSum` and the nominal weight w = `Data.nominalWeight`. -/
def dirCost := ∑ σ, (D.jetSize (D.w 0 σ) - D.primeSum (D.nominalWeight σ) σ)
end Data
end
end
