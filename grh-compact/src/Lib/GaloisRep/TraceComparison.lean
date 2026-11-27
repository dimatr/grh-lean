import Lib.GaloisRep.LaurentAlternants
import Lib.DiscreteSeries.SchurOrthogonality2
import Lib.GaloisRep.ChangingSigns
import Lib.GaloisRep.FiniteBesselGroup
import Lib.GaloisRep.ReproducingKernel

-- part: Lib.DiscreteSeries.Character.KTypeMultiplicity
section
/-! Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. The
character formula is stated for Schur modules of products of general linear groups at elements with
distinct eigenvalues, then carried by Schur's lemma to characters of U(p)×U(q) defined as means of
products of principal minors. The dimension is obtained as a limit at 1. Source: H. Weyl, The
Classical Groups (1939), ch. VII; Fulton and Harris, Representation Theory (1991), Lectures 24-25.

Part of: Discrete series character on the compact Cartan by orbital integrals; formal degree (known
result; see Lib.DiscreteSeries.Character.FormalDegree).

This file: Weyl character and denominator formulas for U(p)×U(q); conjugacy into the torus. K-type
multiplicities of discrete series: integer, one at lowest type, supported in cone. -/

open Finset Complex Equiv HCParam Matrix
variable {n} [Fintype n] {ε} {l ν : @HCParam n ε} (k : maxCompactU ε)

/-- The continuous class function χ_ν(g) = c_ν⁻¹ ∫_K m_ν(y⁻¹gy) dy on K = U(diag ε) ∩ U(n), with
c_ν = ∫_K |m_ν|². -/
noncomputable def HCParam.kTypeChar (ν : HCParam ε) : C(maxCompactU ε, ℂ) := ⟨fun g ↦
  (∫ y, weightMinors ν (y⁻¹ * g * y).1 ∂haarK ε) /
  ν.kTypeNormSq, (haarK ε).restrict_univ ▸ (continuous_parametric_integral_of_continuous
  (by fun_prop (disch := simp)) isCompact_univ).div_const _⟩

attribute [local simp] kTypeChar BlockTriangular blockDiagonal'_apply toBilin'_apply'
  toSquareBlock_def Orbital.torusEval Units.smul_def blockHom mem_maxCompactU mem_blockDiagAlg
  weylRep diagTorus zpow_add₀

lemma Orbital.exists_maxCompactU_of_blocks [DecidableEq ℤˣ] (g : ∀ _, Matrix _ _ ℂ) (h : ∀ τ,
  (g τ)ᴴ * g τ = 1) : let e := sigmaFiberEquiv ε
  ∃ y : maxCompactU ε, y = reindex e e (blockDiagonal' g) ∧ y.1.1.1.toSquareBlock ε = g := by
  intro e; set y := reindex e e _; have m : y ∈ blockDiagAlg ε := by aesop
  use ⟨U.of IsHermInvolution.isUnit y ?_, mem_maxCompactU.2 m⟩, rfl,
    (by aesop : (y.submatrix e e).blockDiag' = _)
  simp [↓Commute.right_comm (m _ rfl), y, ← blockDiagonal'_mul, h, ← Pi.one_def]

/-- Weyl's character formula for K. For l injective, ν K-dominant for the order −l, χ_ν =
`HCParam.kTypeChar` on the diagonal torus is a Laurent polynomial and ∏(x_a−x_b)·χ_ν(x) = Σ_{w∈W_K}
sgn(w) x^{(ν+δ)∘w}; product over ε_a = ε_b, l_b < l_a, δ_a counting such b.

Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. -/
lemma Orbital.weyl_character_kTypeChar (hl : l.Injective) (hν : IsKDominant ε (-l) ν) :
  (∃ P, ∀ x, ν.kTypeChar (diagTorusK x) = torusEval x P) ∧ ∀ x, torusEval x (l.rootProd Eq) *
  ν.kTypeChar (diagTorusK x) = torusEval x (alternant ε (ν + l.lowerCount Eq)) := by
  let := Classical.decEq ℤˣ; let m τ := {i // ε i = τ}
  choose q hq using (exists_equiv_fin_lt_iff (n := m ·) hl.injOn.injective)
  let p τ := (q τ).symm.trans Fin.revPerm
  let g τ := ((List.ofFn (ν <| q τ ·.rev)).getD · 0)
  let κ τ k := (g τ (k - 1) - g τ k).toNat; let e τ := g τ 0 - diagramWeight (rankAt m) κ (τ, 0)
  have h τ : ∀ i, ν i.1 = e τ + diagramWeight (rankAt m) κ (τ, p τ i) :=
    (reindex_equiv (p τ).symm).1.2 fun ⟨k, o⟩ ↦ by
    simp [p, IsKDominant] at *
    induction k with grind [hq τ (.rev ⟨_, o⟩) (.rev ⟨_ - 1, tsub_lt_of_lt o⟩)]
  let b : maxCompactU ε →* ∀ τ, GL (m τ) ℂ := .pi (blockHom ε · |>.comp (.mk' (⟨·,
    fun _ ↦ by aesop⟩) (by tauto))); let R := (weylRep κ e).comp b
  have ⟨v, w, M⟩ : ∃ v w, ∀ k, w ⬝ᵥ R k *ᵥ v = weightMinors ν k := ⟨_, _, fun k ↦ by
    erw [← dotProduct_mulVec (weylEval m κ _), weylRep_coeff_eq_prod_weightMinors p,
      weightMinors_eq_det_zpow_mul_prod (by simp) _ _ (neg_sum_abs_le_and_le_sum_abs _)]
    simp_rw [← h, weightMinors_eq_det_zpow_mul_prod (b k _).det_ne_zero _ _
      (neg_sum_abs_le_and_le_sum_abs ν ·), principalMinor_eq_det]
    rw [prod_mul_distrib, prod_zpow, prod_comm]; clear * -
    congr! <;> rw [BlockTriangular.det_fintype (b := ε)] <;> aesop (add 1% congr)⟩
  have : Continuous (R ·) := by
    simp [R, b]; fun_prop (disch := try exact (.inl <| b · _ |>.det_ne_zero))
  have ⟨B, hB, hL⟩ := exists_intertwining_mean (haarK ε) R R (vecMulVec v w)
  obtain ⟨a, d, z, ⟨⟩⟩ := fun k ↦ hL (traceLinearMap .. ∘ₗ .mulRight ℂ (R k)), hL ((toBilin'.1.flip
    w).flip v), scalar_of_commute_schur
    (exists_maxCompactU_of_blocks · · |>.elim fun y e ↦ by simpa [R, ← e] using! hB y)
  simp [mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, ← dotProduct_mulVec, ← map_mul,
    weightMinors_unitary_inv, M, dotProduct_comm (_ *ᵥ _), conj_mul',
    ← smul_one_eq_diagonal, by simpa using M 1, -mem_maxCompactU] at a d
  simp [a, ← (mod_cast d : ν.kTypeNormSq = z), ne_of_gt, R, b, diagonal_apply, Subtype.val_inj,
    ← diagonal.eq_1, ← prod_zpow, -UnitsInt.univ, rootProd, ↓torusEval_alternant]
  use ⟨∑ i : WeylIndexFam m κ, ∏ τ, ∏ a, .single (Pi.single a.1
    (e τ + tableauWeight i τ a)) 1, by simp [mul_sum, schur_diagonal, -UnitsInt.univ]⟩, fun x ↦ ?_
  have F τ j : ({b | τ = _ ∧ l b < l (q τ j)} : Finset n) = (Iio j).map (q τ).asEmbedding :=
    ext (by simp [← hq, reindex_equiv (q τ).symm, m]; tauto)
  rw [← Fintype.prod_fiberwise ε, Fintype.prod_congr, mul_rotate', weyl_character q,
    ← prod_mul_distrib, BlockTriangular.det_fintype (by simp; order)]; simp_rw
    [det_classical, ← fun τ ↦ det_submatrix_equiv_self (R := ℂ) (q τ), reindex_equiv (q _),
    ← det_mul_column]
  rcongr; simp [(q _ _).2, lowerCount, F, h, pow_add, p, field]
  simpa [reindex_equiv (q _), (q _ _).2, F, m, (det_classical _).symm.trans (det_vandermonde _)]
    using fun _ ↦ prod_comm' (by simp)

/-- Weyl's denominator formula for K: for l injective, the product of x_a − x_b over ε_a = ε_b,
l_b < l_a, is the sum of sgn(w) x^{δ∘w} over permutations w preserving ε, where δ_a counts
such b. -/
lemma Orbital.weyl_denominator (h : l.Injective) : l.rootProd Eq = alternant ε (l.lowerCount Eq) :=
  eq_of_torusEval_eq (by simpa [kTypeNormSq, Pi.zero_def, ↓zero_add] using
  (weyl_character_kTypeChar h (ν := 0) (by tauto)).2)

lemma Orbital.exists_conj_diagTorusK : ∃ y x, y * diagTorusK x * y⁻¹ =
  k := have ⟨X, e, _⟩ := exists_expU_eq_maxCompactU k
  have h t : ((-Complex.I • X.1).toSquareBlock ε t).IsHermitian := by
    ext ⟨i⟩ ⟨j⟩; simpa [*, signMatrix, add_eq_zero_iff_eq_neg, field] using congr($(X.2) i j)
  (exists_maxCompactU_of_blocks _ (h · |>.eigenvectorUnitary.2.1)).imp fun _ m ↦ ⟨.exp ∘ _, by
    symm; ext : 3; simp [← e, exp_eq_exp_ℂ, ← Pi.exp_def, ← exp_diagonal, ← Matrix.exp_conj]
    convert congr(NormedSpace.exp (Complex.I • (blockDiagonal'
      $(funext (h · |>.spectral_theorem))).reindexRingEquiv ℂ (sigmaFiberEquiv _)))
    simp_all [← ext_iff, sigmaFiberEquiv]; grind [Subtype.heq_iff_coe_eq, I_sq]
    simp [m, ↓maxCompactU.coe_inv, map_mul, ← diagonal_mul_diagonal, ← smul_eq_mul_diagonal]; rfl⟩

open ComplexConjugate GlModule InnerProductSpace MeasureTheory Norms.L2Operator

attribute [local simp] IsKHighest inner_sub_left mul_assoc ne_of_gt rep_apply_apply

variable {n : Type} [Fintype n] {ε : _} {ν : @HCParam n ε} {A} {l : HCParam ε}

lemma Orbital.integral_mul_conj_kTypeChar {f : maxCompactU ε → _} (hf :
  Continuous f := by fun_prop) : ∫ k, f k * conj (ν.kTypeChar k) ∂haarK ε = ∫ y, (∫ k, conj
  (weightMinors ν k.1) * f (y * k * y⁻¹) ∂haarK ε) / ν.kTypeNormSq ∂haarK ε := by simpa [kTypeChar,
  ← integral_conj, integral_div, mul_div, mul_comm] using (integral_skew_product (fun y ↦
  ((measurePreserving_mul_left _ y⁻¹).mul_right _ y).2) (integrable_of_compactSpace (f :=
  (fun y k ↦ f (y * k * y⁻¹) * conj (weightMinors ν k)).uncurry))).2

lemma Orbital.integral_conj_kTypeChar : ∫ k, 1 * conj (ν.kTypeChar k) ∂haarK ε = ite (ν = 0) 1 0 :=
  .trans integral_mul_conj_kTypeChar (by
  split_ifs with h <;> simp [*, kTypeNormSq, Pi.zero_def, integral_conj]
  contrapose! h; exact AddMonoidAlgebra.single_left_injective h
    (eq_of_torusEval_eq fun t ↦ by simpa [torusEval, diagTorus,
    h] using (integral_mul_left_eq_self (μ := haarK ε) (weightMinors ν ·) (diagTorusK t))))

/-- Multiplicity of a K-type. Let l = 2λ have gap 500n³+A, n ≥ 1, ν be K-dominant. Then g ↦ ∫_K
χ̄_ν(k)ψ_λ(g⁻¹kg)dk is integrable, and deg_λ times its integral is some m∈ℕ; m = 1 for ν =
Λ = `HCParam.lowestKType` l, and m ≠ 0 forces ν−Λ∈`HCParam.rootCone` l. -/
lemma Orbital.exists_kType_multiplicity [Nonempty n] [hg : l.HasLargeGap A] (hν :
  IsKDominant ε (-l) ν) : let R (g : USign ε) := (∫ k : maxCompactU ε, l.dsCoeff
    (g⁻¹ * k * g :) * conj (ν.kTypeChar k) ∂haarK ε); Integrable R ∧ ∃ m : ℕ, l.formalDegree *
    ∫ g, R g = m ∧ (ν = l.lowestKType → m = 1) ∧ (m ≠ 0 → ν - l.lowestKType ∈ l.rootCone) := by
  obtain ⟨⟨d, k, j⟩, _, hw, hi, s, hs⟩ := hg.toL2_spec, (@isUnitaryRep_rightRegularL2 _ _ ε).1,
    isKHighest_dsGenerator hg, hg.isUnitaryCasimirGe_dsAction.1,
    exists_nat_ge (l.casimirKValue ν - l.casimirKValue l.lowestKType : ℝ)
  have := hw.finite_filtration hi; let W := l.dsAction.filtration ε dsGenerator
  let V := .ofLinearComb {v | l.IsKHighest dsAction ν v} ⟨0, by simp⟩ (by
    simp +contextual [smul_smul, mul_comm]) ⊓ W s; let b := stdOrthonormalBasis ℂ V
  -- `key x`: `ν.kTypeNormSq⁻¹ * ∫ k, conj (weightMinors ν k) * l.dsCoeff (x * k * x⁻¹) = ∑ i, |b i
  -- x| ^ 2`
  have key x := by
    let T := innerSL ℂ (hg.toL2 dsGenerator) ∘L rightRegularL2 x
    let φ := strongIntegral (haarK ε) fun k ↦ conj (weightMinors ν k) • T ∘L rightRegularL2 k
    have F : ∀ w, φ w = _ :=
      strongIntegral_apply _ _ fun _ ↦ by simpa using integrable_of_compactSpace
    let z t := ((φ.1 ∘ₗ hg.toL2).domRestrict (W t)).adjoint 1
    have H {s t y} hy (o : s ≤ t) : ⟪(z t).1, y⟫_ℂ = φ (hg.toL2 y) :=
      (LinearMap.adjoint_inner_left _ (⟨y, filtration_mono o hy⟩ : W t) 1).trans (by simp)
    have hZ t : l.IsKHighest _ ν (z t).1 := .of_E_eq_smul fun f c e h ↦
      Subtype.mk.inj (ext_inner_right ℂ (x :=
      ⟨_, E_mem_filtration (z t).2 e⟩) (y := (_ : ℂ) • z t) fun ⟨y, hy⟩ ↦ by
      let Φ b := ∫ k, weightMinors ν (b * k⁻¹) * y.1.1 (x * k) ∂haarK ε
      have a : HasFDerivAt Φ _ 1 := (IsAnalyticFamily.analyticAt_integral _
        (by apply IsAnalyticFamily.of_analyticAt (.prodMk ..) (fun (b, p, q) ↦
        weightMinors ν (b * p) * q) <;> fun_prop (disch := simp))).differentiableAt.hasFDerivAt
      have u (j : maxCompactU ε) : φ (rightRegularL2 j (hg.toL2 y)) = Φ j := .trans (by simp [F,
        ← weightMinors_unitary_inv, T, -map_mul, k]) (integral_mul_right_eq_self _ j)
      simpa +contextual [hi.1 f, e, H (E_mem_filtration hy e.symm), ↓inner_smul_left, H hy,
        @eq_comm _ c, apply_ite conj, by simpa using u 1] using (fderiv_eq_on_blockDiagAlg a
        (φ.1 ∘ₗ hg.toL2 ∘ₗ dsAction.ρ.flip y) (fun Y h ↦ by simpa [u ⟨_, h _⟩] using
        ((d Y y).map_clm φ).deriv) (by clear * - e; grind [mem_blockDiagAlg])
        ).symm.trans <| fderiv_eq_of_borel_equivariant ε a (o := -l) (by simpa) e.symm id (by
        simp +contextual [Φ, hν.weightMinors_oppBorel_mul hg.neg.1]))
    simpa [← congr(hg.toL2 $(b.sum_repr' ⟨_, hZ s, (z s).2⟩)), H (b _).2.2, ← mul_sum, F, T,
      -map_mul, ↓fun i ↦
      (F _).trans ((b i).2.1.integral_conj_weightMinors_smul isUnitaryRep_rightRegularL2 d hν T), k,
      ← inner_conj_symm (rightRegularL2 x _), ← inv_mul_eq_iff_eq_mul₀, by
      simpa using isUnitaryRep_rightRegularL2.form_apply_eq_form_inv_apply x⁻¹]
      using hw.coeffMap_eq_zero hi (d.isCoeffMap (φ - innerSL ℂ (hg.toL2 (z s)))) (fun g a ↦
      (φ - _).le_opNorm_of_le (by simp [rightRegularL2]; rfl)) (fun t a
      o ↦ by simpa [H o] using! (congrArg conj (mem_orthogonal_filtration_of_casimirK s hi hw
      (z (s ⊔ t) - z s) (by simp [(hZ _).casimirK_eq_smul,
      smul_sub]) hs (by simp +contextual [Submodule.mem_orthogonal', @H s]) t a o))) x⁻¹
  have I y := by simpa [Pi.mul_def] using (hg.memLp y).integrable_mul (hg.memLp y).star
  have M := by simpa [← mul_sum, ← integral_finsetSum, I, show ∀ a, ‖hg.toL2 (b a)‖ = 1 from
    b.norm_eq_one] using congr(∑ i, $(j (b i) (b i) 1))
  intro R; exact (funext fun g ↦ .trans integral_mul_conj_kTypeChar (by simp [← key,
    div_eq_inv_mul]) : R = _).symm.rec ((integral_skew_product
    (Measure.map_mul_right_inv_eq_self _ ·.1⁻¹) ((integrable_finsetSum ⊤ fun j _ ↦
    I (b j)).comp_snd (haarK ε))).imp_right fun t ↦ ⟨_, .trans (by simp [↓t]) M.symm,
    have N q x := by simpa [↓dsCoeff_inv] using integral_conj_weightMinors_mul_dsCoeff hg x x⁻¹ hν q
    ⟨by rintro rfl; simpa [← key, N, by simpa using dsCoeff_schur_orthogonality hg 1 1] using M,
      Function.mtr fun q ↦ by
    simpa [← key, N, q, (mt (by simp [·, rootCone]) q : ν ≠ l.lowestKType)] using M⟩⟩)
end

-- part: Lib.DiscreteSeries.Character.SectorBound
section
/-! Part of: Discrete series character on the compact Cartan by orbital integrals; formal degree
(known result; see Lib.DiscreteSeries.Character.FormalDegree).

This file: Haar measure of U(p,q) as the measure of its open orbit on flags. Weyl's dimension
formula for U(n), as the mean square of the highest coefficient. Lower bound for products of
principal minors of conjugated positive diagonal matrices. -/
seal Finset.univ Finset.sum Finset.prod

open Matrix MeasureTheory Complex ComplexOrder Norms.L2Operator LinearMap Finset U
variable {n} [Fintype n] {o : n → ℤ} (ho : o.Injective) (ε : n → _) {b c}

/-- The set of matrices gb with g in U(diag ε) and b invertible and upper triangular for the
order o. -/
def openOrbit o := {y | ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧ y = g.1.1 * b}

include ho

lemma IsBorelMatrix.unitary_eq_of_mul_eq {g g' : USign ε} (hb : IsBorelMatrix o b) (hc :
  IsBorelMatrix o c) : g * b = g' * c ∧ (∀ i, 0 < c i i / b i i) → g = g' := by
  obtain ⟨t, rfl⟩ := mul_left_surjective g' g; simp [mul_assoc]; rintro rfl p
  cases (by simpa [hb.2] using hc.mul hb.inv :).exists_eq_diagonal_exp ho; ext : 2
  simpa [funext_iff, hb.diag_ne_zero, *] using (eq_coe_norm_of_nonneg <| p · |>.le)

/-- For o injective, b invertible and upper triangular for o with positive diagonal, J = diag ε,
J' = diag ε': the real map y ↦ co(J·lo(bJ'·sk(y)·b⁻¹)), lo = `lowerLiePart` ε 1 o,
co = `skewCoords`, sk = `skewOfReal`, has |det| = ∏
b_ii^{2r_i}, r_i = #{j : o_j < o_i} − #{j : o_i < o_j}. -/
lemma abs_det_lowerLiePart (h : IsBorelMatrix o b) (p : ∀ i, 0 < b i i) ε' :
  |(skewCoords ∘ₗ mulLeft ℝ (signMatrix ε) ∘ₗ lowerLiePart ε 1 o ∘ₗ mulLeftRight ℝ (b,
  b⁻¹) ∘ₗ mulLeft ℝ (signMatrix ε') ∘ₗ skewOfReal).det| = ‖diagChar (twoRho o ⊤) b‖ ^ 2 := by
  let := LinearOrder.lift' (fun (i, j) ↦ [|o i - o j|, o i, o j]) (by aesop_cat)
  choose d u e using (RCLike.pos_iff_exists_ofReal.1 <| p ·); let x i j := ε i * ε' i * d i / d j
  rw [← det_toMatrix (stdBasis ..)]; show ‖(?T : Matrix (n × n) _ ℝ).det‖ = _
  have z i j (y : Matrix n n ℂ) (H : ∀ k l, o i - o j < o k - o l → y k l = 0) : (b * y * b⁻¹) i j =
      b i i * y i j / b j j := by simp [entrywise, sum_mul, ← sum_product']; rw [sum_eq_single
    (j, i)] <;> grind [h.inv, h.inv_apply_diag, IsBorelMatrix, BlockTriangular]
  have E p q (H : q ≤ p) : ?T p q = ite (p = q) (ite (o p.1 < o p.2) (x p.2 p.1) (x p.1 p.2)) 0 :=
    by simp [toMatrix_apply, stdBasis, lowerLiePart, skewCoords, signMatrix]; split_ifs <;>
    (try lia) <;> (repeat rw [z]) <;> simp [skewOfReal, ← e, ite_apply] <;> grind [ofReal_zero,
    H.imp_right List.head_le_of_lt, abs_unit_intCast (α := ℝ) (ε p.1)]
  rw [det_of_isUpperTriangular fun _ ↦ by grind]; simp [E, ← e, x, sq, diagChar, twoRho, u,
    ne_of_gt, zpow_sub₀, ← prod_const, prod_filter, apply_ite norm, ← prod_div_distrib,
    Fintype.prod_prod_type]; nth_rw 2 [prod_comm]; simp_rw [← prod_mul_distrib]; rcongr; grind

/-- For o injective, B the o-upper-triangular group, G_ε = U(diag ε): G_ε' ∩ G_εB is open in
G_ε'. If real f satisfies f(yb) = |b^{2ρ}|²f(y) (y invertible, b ∈ B, 2ρ = `twoRho` of o),
then ∫ f⁺ over G_ε' ∩ G_εB is at most that over G_ε ∩ G_ε'B. -/
lemma isOpen_openOrbit_and_lintegral_le ε' : IsOpen {g : USign ε' | ↑g ∈ openOrbit ε o} ∧ ∀ f,
  (∀ (y : GL n ℂ) b, IsBorelMatrix o b → f (y * b) = ‖diagChar (twoRho o ⊤) b‖ ^ 2 * f y) → ∫⁻ g :
  USign ε', (openOrbit ε o).indicator (.ofReal ∘ f)
  g ≤ ∫⁻ g : USign ε, (openOrbit ε' o).indicator (.ofReal ∘ f) g := by
  have ⟨ψ, ⟨d, z⟩, H⟩ := exists_borel_chart 1 o (lowerLiePart ε 1 o) hasStrictFDerivAt_exp_zero
    (by simp [lowerLiePart, signMatrix]; grind)
  choose! Φ B P Q e i using (fun _ ⟨g, b, h, e⟩ ↦ let t := diagTorus ε fun i ↦ ⟨‖b i i‖ / b i i, by
    simp [Submonoid.unitSphere, h.diag_ne_zero ho]⟩; ⟨g * t⁻¹, t * b, .mul ⟨by simp [t, diagTorus],
    by simp⟩ h, by simp [t, diagTorus, h.diag_ne_zero ho], by simp [e, mul_assoc,
              h.2]⟩ : ∀ y ∈ openOrbit ε o, ∃ g : USign ε, ∃ b, IsBorelMatrix o b ∧
    (∀ i, 0 < b i i) ∧ g * b = y ∧ y * b⁻¹ = g)
  have E y h := have u := P y h; let A := ContinuousLinearMap.mulLeftRight ℝ _ (Φ y).1.1⁻¹ (B y)⁻¹
      have a : A y = 1 := (by simp_all [A, mul_assoc]); (Filter.eventually_and.1
        (((A.cont.tendsto' _ _ a).eventually (.and (.mp (by simp) H) (d.continuousAt.const_add 1
        (IsAccretive.setOf_mem_nhds (by simp [z, PosDef.one.isAccretive]))))).mono fun x ⟨⟨p, _, q⟩,
        k⟩ ↦ have r : x = (Φ y * expU ⟨_, lowerLiePart_mem_unitaryLie ..⟩).1.1 * _ :=
          (by simpa [mul_assoc, A, u.2] using congr(Φ y * $q * B y))
        (fun m ↦ And.intro m congr($((P x m).unitary_eq_of_mul_eq ho ε (p.mul u) ⟨(e x m).trans r,
          fun i ↦ by simpa [↓p.mul_apply_diag ho u, Q, h, m, lowerLiePart, lt_def, ← two_mul,
          signMatrix, mul_right_comm, ← Int.cast_mul] using
          k.diag_pos⟩).1.1)) ⟨_, _, p.mul u, r⟩)).imp_right (((a ▸ HasFDerivAt.comp 1 (by
      simpa [z] using hasFDerivAt_exp_zero) ((lowerLiePart ..).hasFDerivAt.comp _ d)).comp _
        A.hasFDerivAt).const_mul _).congr_of_eventuallyEq
  refine (fun O ↦ ⟨O, fun F hB ↦ have S := measurable_cayleyChart O.measurableSet; ?_⟩)
    (.preimage_of_continuous (isOpen_iff_mem_nhds.2 (E · · |>.1)))
  have ⟨t, h⟩ := (Haar.lintegral_chart_rotate_le (.refl ..) (.id _) (Φ :=
    (Φ <| cayleyChart (signMatrix ε') ·)) (S.inter (by measurability)) (fun _ ⟨p, u⟩ _ ⟨q, v⟩ _ ↦
    cayleyChart_injOn u v ((P _ p).inv.unitary_eq_of_mul_eq ho ε' (P _
    q).inv (by simp_all [IsBorelMatrix.inv_apply_diag ho]))) fun y ⟨p,
    q⟩ ↦ have ⟨c, j⟩ := abs_det_logDerivU_cayleyChart q; .imp_right (.trans · ((abs_mul ..).trans
      (congrArg₂ _ (abs_det_lowerLiePart ho ε (P _ p) (Q _ p) ε') j))) ?_).exists
  grw [lintegral_eq_cayleyChart, ← lintegral_mul_left_eq_self _ (circleScalar t)⁻¹, ← h,
    ← setLIntegral_indicator S]
  gcongr; exact Set.le_indicator_apply (fun p ↦ by simp_all [(openOrbit ε' o).indicator_of_mem ⟨_,
    _, (P _ p).inv, (i _ p).symm⟩, mul_left_comm, e _ p ▸ hB .., mul_assoc, ← mul_div]) (by aesop)
  have D := (E _ p).2.comp y c.hasFDerivAt
  use ⟨_, D⟩; erw [← map_mul, logDerivU, D.fderiv]; congr 2 with
  simp [conjTranspose_logDerivU c, ← congr($(i _ p)⁻¹), (P _ p).2, inv_mat]
  simp [logDerivU, ← mul_assoc, mem_U.1]

/-- Let o be injective, F continuous on GL_n(ℂ) with F(yb) = |∏ b_ii^{r_i}|²F(y) for o-triangular b,
r_i = #{j : o_j<o_i} − #{j : o_i<o_j}. Then F is integrable on G = U(diag ε), and ∫_G F is ∫_{U(n)}
F minus the part outside `openOrbit ε o`. -/
lemma integral_haar_eq_integral_openOrbit {F : _ → ℂ} (hB : ∀ (y : GL n ℂ) b, IsBorelMatrix o b →
  F (y * b) = ‖diagChar (twoRho o ⊤)
  b‖ ^ 2 * F y) (c : Continuous (F · : GL n ℂ → ℂ)) : Integrable (F · : USign ε → ℂ) ∧ ∫ g :
  USign ε, F g = (∫ k : USign 1, F k.1.1) - ∫ k in {k : USign 1 | k.1.1 ∈ openOrbit ε o}ᶜ, F k := by
  have ⟨S, L⟩ := (isOpen_openOrbit_and_lintegral_le ho ε 1).imp_left (·.measurableSet)
  have K := integrable_of_compactSpace (X := USign 1) (ν := volume) (c.comp' continuous_subtype_val)
  have E f h := (((isOpen_openOrbit_and_lintegral_le ho ..).2 f h).antisymm (L f h)).trans
    (lintegral_indicator S _)
  simp [fun g : USign ε ↦ (exists_orthonormal_mul o ⟨_, g.1.4⟩).elim (b := ↑g ∈ openOrbit 1 o)
    (⟨⟨g * ·, by simp_all [U]⟩, _, .inv ⟨·.1, by simp⟩, by simp⟩)] at E
  refine (fun i ↦ ⟨i, (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun φ ↦ ?_⟩)
    ⟨c.comp_aestronglyMeasurable (by fun_prop), by simpa [E (‖F ·‖) (by aesop), ← ofReal_norm,
    HasFiniteIntegral] using K.restrict.2⟩; simp [← φ.integral_comp_comm, φ.integrable_comp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part, K.restrict, setIntegral_compl, *]
  erw [E (φ ∘ F), E (-φ ∘ F)] <;> simp_all [← ofReal_pow, ← real_smul]

omit ho

open Nat Orbital AddCircle HCParam

/-- Weyl's dimension formula for U(n): for a parameter l = 2λ and Λ = λ−ρ, (∏_{i<n} i!) /
∫_{U(n)} |m_Λ(k)|² dk = ∏_{λ_j<λ_i} (λ_i−λ_j), for Haar measure of mass one. -/
lemma weyl_dimension_formula {n} [Fintype n] {l : @HCParam n 1} {h} (hg : l.HasGap h) :
  l.lowestKType.kTypeNormSq⁻¹ = weylDimensionPoly l := by
  have L (a : HCParam 1) := tendsto_finsetProd ⊤ fun i _ ↦ tendsto_finsetProd {j | l j < l i} fun j
    _ ↦ ((hasDerivAt_fourier 1 (a i) 0).sub (hasDerivAt_fourier 1 (a j) 0)).tendsto_slope_zero
  have E (t : ℝ) := ((weyl_character_kTypeChar hg.1 hg.isKDominant_lowestKType).2 (@toCircle 1 t ^
    l.lowerCount Eq ·)).trans (by rw [torusEval_alternant, ← det_transpose]; simp [weyl_denominator
    hg.1, torusEval_alternant, transpose, zpow_comm] :
    _ = Orbital.torusEval (@toCircle 1 t ^ (l.lowestKType + l.lowerCount Eq) ·) (l.rootProd Eq))
  simp [rootProd, Orbital.torusEval, toCircle_zsmul, ← mul_sub] at E L
  obtain ⟨t, k, e, he⟩ := tendsto_nhds_unique (((L _).mul (by fun_prop : ContinuousWithinAt ..)
    ).congr ((mul_assoc ..).trans <| congrArg _ <| E ·)) (L _), fun a ↦ congr(($(two_mul_lowestKType
    hg a) : ℂ) + $(card_lt_add_card_gt_add_one hg.1 a)), exists_equiv_fin_lt_iff hg.1
  simp [kTypeChar, diagTorus, prod_eq_zero_iff, mul_assoc, lowerCount, twoRho] at t k
  rw [weylDimensionPoly, eq_div_iff (by positivity), ← ofReal_inj, mul_comm]; push_cast
  convert t <;> try grind
  simp_rw [← map_univ_equiv e, filter_map, prod_map, prod_range, ← descFactorial_self,
    descFactorial_eq_prod_range, ← prod_range_natCast_sub]
  simp [he, filter_gt_eq_Iio, ← Iio_eq_range, ← Fin.map_valEmbedding_Iio]

variable {n : _} [Fintype n] (h : ℕ) (u : GL n ℂ) (l f : n → ℤ)

/-- The matrix u*·diag(2^{f_i})·u, for u in GL_n(ℂ) and an integer vector f. -/
@[simp] noncomputable abbrev twoPowDiagConj := u.1ᴴ * diagonal ((2 : ℂ) ^ f ·) * u

attribute [local simp] zpow_nonneg prod_eq_zero_iff PosSemidef.conjTranspose_mul_mul_same

/-- Let u be unitary, l, f integer vectors, m an integer, f_a+|m| ≤ f_c whenever l_c < l_a, and
h ≤ |l_i−l_j|, h natural. Then (|u_ij|² 2^m)^h·|m_l(D)| ≤ |m_l(u*Du)|, where D =
diag(2^{f_a}). -/
lemma le_norm_weightMinors_twoPowDiagConj i j m (hu : uᴴ = u.1⁻¹) (k : ∀ a c, l c < l a →
  f a + |m| ≤ f c) (H : h ≤ |l i - l j|) : ‖weightMinors l (twoPowDiagConj 1 f)‖ *
  (‖u i j‖ ^ 2 * 2 ^ m) ^ h ≤ ‖weightMinors l (twoPowDiagConj u f)‖ := by
  have P {f g p} [DecidablePred p] (h : f ≤
    g) : ‖principalMinor (twoPowDiagConj u f) p‖ ≤ ‖principalMinor (twoPowDiagConj u g) p‖ :=
    norm_det_le_norm_det_of_posSemidef (.submatrix (by simp) _) (.submatrix (M :=
    twoPowDiagConj u g - twoPowDiagConj u f) (by simp [← sub_mul, ← mul_sub, h _]) _)
  have V f : (twoPowDiagConj u f)⁻¹ = twoPowDiagConj u (-f) :=
    inv_eq_left_inv (by simp [mul_assoc, hu, ← mul_assoc (diagonal _)])
  wlog H : l j ≤ l i generalizing l f; convert V f ▸ this (-l) _
  simp +contextual [↓← weightMinors_neg, add_comm, k]; grind
  obtain ⟨⟨a, A⟩, b, B⟩ := @Finite.exists_min _ _ _ ⟨i⟩ _ l, Finite.exists_le l
  rw [show h = #(Ioc (l a) b ∩ Ioc (l i - h) (l i)) by simp [Ioc_inter_Ioc]; grind, ← prod_const]
  simp [weightMinors_eq_det_zpow_mul_prod _ (l a) b, ↓← prod_ite_mem, ← prod_mul_distrib, *,
    mul_zpow, field, -mul_ite]
  gcongr with t; have ⟨c, _⟩ := exists_min_image {k | l k < t} f ⟨a, by grind⟩
  let q k := t ∈ Ioc (l i - h) (l i) ∧ k = j; have := (k · c)
  grw [(?_ : ite .. ≤ ‖principalMinor (twoPowDiagConj 1 (f c)) q‖ * ‖principalMinor (twoPowDiagConj
    u (f ⊓ f c))⁻¹ q‖), jacobi_complementary_minor (by simp), norm_div, fischer_inequality (r :=
    (¬q ·)) (by simp) (fun i ↦ l i < t ∧ ¬q i) (t ≤ l ·), P inf_le_right, P inf_le_left]
  simp [principalMinor_eq_det, ← diagonal_one, ← smul_eq_mul_diagonal, hu, ← diagonal_smul, field,
    sub_ite, ← prod_mul_distrib, apply_ite norm]
  rw [mul_comm, prod_congr rfl]; any_goals grind
  nth_grw 3 [← re_le_norm]; split <;> simp [↓V, q, ‹_›, principalMinor.eq_1, diagonal, mul_apply,
    default, toSquareBlockProp, mul_right_comm _ _⁻¹, conj_mul', ↓re_eq_norm.2, sq]
  grw [← single_le_sum (by bound) (mem_univ i)]; simp [field, mul_assoc, ← zpow_add₀]
  gcongr <;> grind
end

-- part: Lib.DiscreteSeries.Character.FormalDegree
section
/-! Known result: Discrete series character on the compact Cartan by orbital integrals, and the
formal degree. The form here is only for U(p,q) and parameters with large gaps, for the explicit
coefficient of the lowest K-type. It gives the formal degree, and the stable sum of elliptic orbital
integrals as Weyl's character of the compact form, exact in the compact dual measure. Source:
Harish-Chandra, Discrete series for semisimple Lie groups II: explicit determination of the
characters, Acta Math. 116 (1966), Thm 16 (with part I, Acta Math. 113 (1965), Thm 3); Knapp,
Representation Theory of Semisimple Groups (1986), Thm 12.7.

This file: Orbital integral times denominators is an antisymmetric Laurent polynomial confined by
K-types. Orbital integral is Weyl's character minus off-orbit part, which lacks low monomials.
Formal degree equals Weyl's dimension polynomial, and (−1)^{pq} times the sum over permutations of
elliptic orbital integrals equals p!q! times the conjugate of Weyl's character. -/

open Matrix MeasureTheory Finset AddMonoidAlgebra Equiv ConjAct InnerProductSpace ContinuousMap
  CStarRing Norms.L2Operator Fintype Metric Int HCParam

section

attribute [local simp low] Finsupp.sum mul_sum inner_sum inner_smul_left inner_smul_right inner_toLp
  prod_ite integral_apply lift_apply'

variable {n} [Fintype n] {ε} (l : @HCParam n ε)

/-- P is D times a formal series with coefficient 1 at x^a, each of whose exponents occurs in
the alternant `Orbital.alternant` of some μ in a + `HCParam.rootCone` l. -/
def Orbital.IsConeSeriesMultiple a (D P : ℂ[_]) := ∃ t : _ → ℂ, (∀ γ, P.1 γ = D.1.sum fun β c ↦
  c * t (-β + γ)) ∧ t a = 1 ∧ ∀ γ, t γ ≠ 0 → ∃ μ, (alternant ε μ).1 γ ≠ 0 ∧ μ - a ∈ l.rootCone

/-- Let λ have gap 500n³+10n⁵, Θ(x) = deg_λ∫ψ_λ(g⁻¹xg)dg on the torus, V_c = ∏(x_a−x_b) over
positive compact roots, D the (4n²+1)-th power of that over negative noncompact roots. Then
V_cDΘ is a W_K-antisymmetric Laurent polynomial with coefficients D convolved with t, t(Λ+δ)
= 1, t supported on W_K(Λ+δ+`HCParam.rootCone` l), δ_a = #{b : ε_b = ε_a, λ_b < λ_a},
Λ = `HCParam.lowestKType` l. -/
lemma Orbital.exists_laurent_orbital_integral [Nonempty n] (hg :
  l.HasLargeGap (10 * card n ^ 5)) : let δ := l.lowerCount Eq
  let Vc := l.rootProd Eq; let N := 4 * card n ^ 2 + 1; let D := (-l).rootProd Ne ^ N
      ∃ P, IsWeylAntisymm ε P.1 ∧ (∀ x, torusEval x P =
        torusEval x (Vc * D) * (l.formalDegree * ∫ g, l.dsCoeff (g⁻¹ * diagTorus ε x * g :))) ∧
        IsConeSeriesMultiple l (l.lowestKType + δ) D P := by
  intro δ Vc N D; let c (y : maxCompactU ε) := mk (y * diagTorusK · * y⁻¹); let W :=
    {w : Perm n // ε ∘ w = ε}
  let ψ := (mk fun p : _ × maxCompactU ε ↦ l.dsCoeffSmooth.1 (p.1⁻¹ * p.2 * p.1)).curry
  choose s ν hν hs using exists_sign_isKDominant hg.1; choose b v bv using
    exists_conj_diagTorusK (ε := ε)
  have ac {μ} h γ := alternant_coeff_of_isKDominant hg.1 h (hν γ) ▸ hs γ
    (alternant ε (μ + δ)).1 isWeylAntisymm_alternant
  have z {μ} h :=
    alternant_coeff_of_isKDominant hg.1 h h ▸ (ac h (μ + δ)).symm; simp [ite_eq_iff] at z
  let X γ := (s γ : ℂ) • (toHCParam ε (ν γ)).kTypeChar; have : Nonempty W := ⟨1, rfl⟩
  choose Y he hA using fun γ ↦ ((weyl_character_kTypeChar hg.1 (hν γ)).elim fun ⟨P, h⟩ k ↦ ⟨s γ * P,
    fun y x ↦ by simp [X, c, ← h]; exact .inl congr($(.trans (by group) (integral_mul_left_eq_self _
    y⁻¹)) / _), eq_of_torusEval_eq fun x ↦ (hs γ (torusEval x <| alternant ε ·) (by simp +contextual
    [IsWeylAntisymm, torusEval_alternant, ← det_permute', submatrix, funext_iff])).trans
    (by simp [← k, h, field])⟩ : ∃ P, (∀ y x, X γ (c y x) = torusEval x P) ∧ alternant ε γ = Vc * P)
  let e (i : Subtype (IsKDominant ε (-l))) := X (i + δ)
  let Φ p := (coeff p).lift _ ℂ _ X; let L := toLp (E := ℂ) 2 (haarK ε) ℂ
  have hX p x : torusEval x (Vc * p.1.lift _ ℂ _ Y) = ∑ w : W,
    w.1.sign * torusEval (x ∘ w.1) p := by
    simp [← hA, torusEval_alternant, det_apply', Fintype.prod_ite_zero, ← sum_filter]
    simp [torusEval, mul_left_comm]; rw [sum_comm, sum_subtype]; simp [funext_iff]
  have key p q (H : ∀ x, _) y x : Φ p (c y x) = torusEval x q := .trans (by simp [Φ, *])
    congr(torusEval x $(mul_left_cancel₀ (by simpa [*, ·] using ac (hν 0) (ν 0 + δ))
    (eq_of_torusEval_eq fun x ↦ (hX p x).trans (H x))))
  have av p := key (Vc * p) (∑ w : W, ⟨p.1.equivMapDomain (w.1.arrowCongr 1)⟩) (by simp [Vc,
    weyl_denominator hg.1, ← torusEval_comp_perm, (torusEval_comp_eq_mul_iff _).2
    (isWeylAntisymm_alternant _ (_ : W).2), ← mul_assoc, ← cast_mul])
  have pair {d D} (hd : ∀ y x, d (c y x) = torusEval x D) γ ψ : ⟪L (X γ), L (d * ψ)⟫_ℂ =
      D.1.sum fun β a ↦ a * ⟪L (X (-β + γ)), L ψ⟫_ℂ := by
    let S : ℂ[n → ℤ] := D.1.sum fun β a ↦ .single (-β) (star a)
    have hS x : torusEval x S =
      star (torusEval x D) := by simp [S, torusEval, ← Circle.coe_inv_eq_conj]
    trans ⟪L (Φ (S * .single γ 1)), L ψ⟫_ℂ; simp [L]; congr with k
    erw [← bv k, key _ (S * Y γ) fun x ↦ ?_, hd, he]
    simp [*, field]; simp [mul_left_comm Vc, by simpa using hX (.single γ 1), hS,
      apply_comp_perm_of_conj_invariant _ (_ :
      W).2 hd]; ac_rfl; simp [Φ, S, sum_mul, sum_inner, -Finsupp.lift_apply]; simp [-Finsupp.sum]
  have xe γ μ : ⟪L (X γ), L (X μ)⟫_ℂ = (alternant ε μ).1 γ := by
    simpa [hA μ, ↓mul_comm Vc, X, L, Vc, weyl_denominator hg.1, coeff_mul_apply_left, δ,
      zero_add δ ▸ ac (by tauto), ← @integral_conj_kTypeChar _ _ ε] using pair (he μ) γ 1
  have o : Orthonormal ℂ (L ∘ e) := by simp +contextual [orthonormal_iff_ite, e, xe, ac, z]
  have hd y x : _ = torusEval x D := (av ((card W : ℂ)⁻¹ • D) y x).trans (by
    simp [D, ↓map_sum, ↓← torusEval_comp_perm,
      torusEval_rootProd_noncompact_comp hg.neg.1 (_ : W).2]); generalize Φ _ = d at hd
  have hI : Integrable (d * ψ ·) := .mono' (.const_mul (integral_decay_le _ .monoidHom_id (c := 2 *
    N) (by omega) 1).1 (2 ^ (#(oppositePairs ε) * N * 2))) (by fun_prop) (.of_forall fun x ↦
    (norm_le_of_nonempty _).2 fun k ↦ by
    let u := (b k)⁻¹ * x; let g := u⁻¹ * diagTorus ε (v k) * u
    let φ := (MulSemiringAction.toAlgHom ℂ (Matrix n n ℂ) (toConjAct u.1⁻¹)).comp (diagonalAlgHom ℂ)
    have p s : ‖φ (∏ i ∈ s, ((v k · : n → ℂ) - (v k i).1 • 1))‖ ≤ (‖g.1.1‖ + ‖g.1.1‖) ^ #s := by
      induction s using cons_induction <;> simp [*, show φ _ = g by rfl, pow_succ',
        norm_mul_le_of_le, norm_sub_le_of_le, U.one_le_norm]
    erw [← bv k, norm_mul, hd]; simp [D, ψ, pow_mul,
      torusEval_rootProd_noncompact hg.neg.1, -norm_prod]
    grw [show _ * _ = g.1.1 by simp [g, u, mul_assoc], norm_dsCoeff_le_pow hg (c := #(oppositePairs
      ε) * N), (le_div_iff₀' (by simp)).2 (?_ : ‖principalMinor (φ _) (ε · = 1)‖ ≥
      (‖u.1.1‖ / 2) ^ 2 * ‖_‖), norm_principalMinor_le_pow, Fintype.card_subtype, p {i | ε i ≠ 1}]
    · simp [div_pow, field, oppositePairs, u, norm_mem_unitary_mul, Unitary.mem_iff, star,
        ← maxCompactU.coe_inv, conjTranspose_nonsing_inv]; ring; rfl
    · grw [sq_le_norm_det_blockDiagPart]; erw [norm_det_blockDiagPart 1, principalMinor_mul,
        principalMinor_mul, U.principalMinor_coe_inv] <;> simp [principalMinor_eq_det,
        oppositePairs, prod_product, ← diagonal_one, sub_ite, diagonal_apply,
        prod_eq_zero_iff] <;> clear * - <;> grind
    grw [card_le_univ]; simp [N, field]; nlinarith [one_le_cast_card n])
  let h := l.formalDegree • ∫ g, d * ψ g
  have hh y x : h (c y x) = h (c 1 x) := by
    simp [h, *, ← integral_mul_left_eq_self (ψ · (c y x)) y.1]
    simp [c, ψ, mul_assoc]
  choose hm m hm' _ _ using (by simpa using exists_kType_multiplicity <| hν ·); let t γ : ℂ :=
    s γ * m γ
  have ha γ : ⟪L (X γ), L h⟫_ℂ = D.1.sum fun β c ↦ c * t (-β + γ) := by
    simp [h, inner_smul_right_eq_smul, ← by simpa [pair hd] using
      (innerSL ℂ (L (X γ)) ∘L L).integral_comp_comm hI]; simp [X, L, t, ψ, ← hm',
      mul_left_comm (l.formalDegree : ℂ), integral_finsetSum, ((hm _).const_mul _).const_mul]
  have ⟨Z, hZ⟩ : ∃ Z, mapRingHom _ (castRingHom ℂ) Z = D := ⟨(∏ a, ∏ b ∈ _,
    (.single (Pi.single a 1) 1 - .single (Pi.single b 1) 1)) ^ N, by simp; rfl⟩
  let a := Finsupp.ofSupportFinite (⟪L <| e ·, L h⟫_ℂ) (((o.inner_products_summable (L h)
    ).tendsto_cofinite_zero.eventually_lt_const one_pos).subset fun i ↦ by
    simp [e, ha, ← hZ, t]; exact_mod_cast one_le_abs)
  let A := innerSLFlip ℂ (L (h - a.lift _ ℂ _ e)) ∘SL L
  have k i : A (e i) = 0 := by simpa [A] using! (o.inner_right_finsupp a i).symm.trans
                                 (inner_sum ..)
  have eq := toLp_injective _ (L.sub_mem_ker_iff.1 (inner_self_eq_zero.1 (sub_mem ((mem_of_closed'
    A.isClosed_ker).2 fun r q ↦ (denseRange_torusEval.exists_dist_lt (h.comp (c 1)) q).elim fun p
    o ↦ ⟨Φ (Vc * (card W : ℝ)⁻¹ • p), by clear * - k z hν; simp_all [Φ, X, e], (dist_lt_iff q).2 (by
    erw [← bv ·, av, hh, dist_comm]; simp_rw [map_sum, ← torusEval_comp_perm,
      AlgHom.map_smul_of_tower]; exact (convex_ball ..).sum_mem (by simp) (by simp) fun w _ ↦
      apply_comp_perm_of_conj_invariant _ w.2 hh ▸ mem_ball'.2 ((dist_lt_iff q).1 o _))⟩)
    (by simp [k]))))
  refine ⟨a.lift _ ℂ _ (alternant ε <| ·.1 + δ), by simp +contextual [IsWeylAntisymm,
    isWeylAntisymm_alternant _, mul_left_comm (a _)], fun x ↦ ?_, t, by simp [↓← ha,
    e, *], by simp [t, hg.isKDominant_lowestKType, *],
    fun γ ↦ .intro (ν γ + δ) ∘ by simp +contextual [t, ↓ac, *]⟩; trans torusEval x Vc * h (c 1 x)
  simp [e, *]; ac_rfl; simp [h, hI, hd]; simp [c, ψ, field]

open Complex ComplexOrder Filter

attribute [local simp] prod_eq_zero_iff Finsupp.sum IsHermInvolution.det_ne_zero
  IsAccretive.det_ne_zero integral_div mul_zpow
  zpow_add₀ _root_.zpow_mul zpow_sub₀ zpow_sum_of_ne_zero

variable {n : Type} [Fintype n] {ε : n → _} {l : HCParam ε} {h : ℕ}

/-- For l = 2λ and J = diag ε, the Haar integral of m_{−(λ−ρ)}(k*Jk) / m_{−(λ+ρ)}(k*Ak) over the
k in U(n) outside the set `openOrbit` ε l; m is `weightMinors`. -/
noncomputable def Orbital.offOrbitIntegral (l : HCParam ε) A := ∫ k in {k :
  USign 1 | k.1.1 ∈ openOrbit ε l}ᶜ, weightMinors (-l.compactForm.lowestKType)
  (k.1.1ᴴ * signMatrix ε * k) / weightMinors (-paramAddRho l) (k.1.1ᴴ * A * k)

/-- For λ of gap h some σ, |σ| = 1, has σ∫_G ψ_λ(g⁻¹xg)dg = cχ(x) − `Orbital.offOrbitIntegral`(Jx)
for all torus points x with Jx accretive; J = diag ε, χ = `HCParam.kTypeChar` of λ−ρ for U(n), c =
∫_{U(n)}|m_{λ−ρ}|². -/
lemma Orbital.orbital_eq_char_sub_offOrbitIntegral (hg : l.HasGap h) : ∃ σ, ‖σ‖ = 1 ∧
  ∀ x, let A := signMatrix ε * diagTorus ε x; A.IsAccretive → σ * ∫ g,
    l.dsCoeff (g⁻¹ * diagTorus ε x * g :) = l.compactForm.lowestKType.kTypeNormSq *
    l.compactForm.lowestKType.kTypeChar (diagTorusK x) - offOrbitIntegral l A :=
  have K := by simpa [lowestKType_neg hg.signs_one] using hg.signs_one.neg.isKDominant_lowestKType
  ⟨weightMinors (-l.compactForm.lowestKType - l.lowestKType)
    (signMatrix ε), by simp [signMatrix], by
  intro x A hA
  have ⟨i, O⟩ := integral_haar_eq_integral_openOrbit hg.1 ε (F := fun y ↦ weightMinors
    (-l.compactForm.lowestKType) (yᴴ * signMatrix ε * y) / weightMinors (-paramAddRho l) (yᴴ
    * A * y)) (fun y b hb ↦ by simp [← mul_assoc _ y.1, mul_assoc bᴴ, hb.2, hb.diag_ne_zero hg.1,
    lowestKType, twoRho, *, IsKDominant.weightMinors_oppBorel_mul (ε := 1) hg.1,
    IsKDominant.weightMinors_mul_borel (ε := 1) hg.1, hg.isKDominant_neg_paramAddRho, diagChar,
    field,
    show IsBorelMatrix (-l) bᴴ by simp_all [IsBorelMatrix, BlockTriangular], ↓← conj_mul']) ?_
  rw [← ((maxCompactU 1).subtype.measurePreserving (by fun_prop) (μ := haarK 1) (fun _ ↦ by
    simp [mem_maxCompactU]) (by simp)).hasLaw.integral_comp (integrable_of_compactSpace ?_).1] at O
  erw [← integral_const_mul, ContinuousMap.coe_mk, congrArg (integral _) (funext fun y :
    @maxCompactU n _ 1 ↦ (?_ : _ = l.compactForm.flenstedJensen (y⁻¹ * (signMatrix ε)⁻¹ * y)
    (y⁻¹ * A * y))), integral_div, integral_integral
    (integrable_of_compactSpace ?_), ← (((measurePreserving_mul_prod_inv ..).comp
    Measure.measurePreserving_swap).fubini (integrable_of_compactSpace ?_)).2]
  any_goals fun_prop (disch := simp (disch := simp [*]) [maxCompactU.coe_inv])
  convert! (integral_skew_product (map_mul_right_eq_self _ ·.1) (integrable_of_compactSpace (ν :=
    haarK ε) (f := (ofReal <| ‖weightMinors l.lowestKType ·‖ ^ 2 /
    l.lowestKType.kTypeNormSq)).mul_prod i)).2 with _ g
  rw [dsCoeff_eq_flenstedJensen hg (mem_blockDiagAlg_iff_commute.2 rfl), flenstedJensen,
    ← integral_div, ← integral_const_mul]; congr with k
  simp [↓mem_U.1 (g * k).2, U.inv_mat, ↓A, mul_assoc, signMatrix, field, mul_conj']
  simpa [mul_assoc, U.inv_mat, A] using hA.conjTranspose_mul_mul (k := g)
  have H a h :=
    (isHolOfWeight_weightMinors hg.1 a⁻¹ (fun _ ↦ K) h).integral_mul_conj_weightMinors hg.1
  simp_all [-ofReal_pow, integral_complex_ofReal, offOrbitIntegral, weightMinors_unitary_inv,
    kTypeNormSq, mul_assoc,
    ↓← maxCompactU.coe_inv, weightMinors_neg, mul_div_cancel₀, ← mul_div (ofReal _), ne_of_gt]
  rw [← dsCoeff_of_mem_maxCompactU hg.signs_one, dsCoeff_eq_flenstedJensen
    hg.signs_one] <;> congr 1 <;> simp [A, diagTorus, mul_assoc, mem_maxCompactU,
    maxCompactU.coe_inv]
  simpa [A, diagTorus, mul_assoc, maxCompactU.coe_inv] using hA.conjTranspose_mul_mul (k := y)⟩

attribute [local fun_prop] AnalyticAt.fun_zpow

/-- Let λ have gap h∈ℕ, Laurent polynomials P(x) = Q(x)·`Orbital.offOrbitIntegral`(Jx) at torus
points with Jx accretive, o_i < o_j whenever λ_j < λ_i. If k < ⟨o,λ+ρ+β⟩+h for all exponents β of Q,
then P has no exponent γ with ⟨o,γ⟩ ≤ k. -/
lemma Orbital.coeff_eq_zero_of_low_level (hg : l.HasGap h) {P Q} (hP : ∀ x,
    let A := signMatrix ε * diagTorus ε x; A.IsAccretive → torusEval x P =
      torusEval x Q * offOrbitIntegral l A) {o} (ho : ∀ i j, l j < l i → o i
  < o j) γ (hk : ∀ β, Q.1 β ≠ 0 → o ⬝ᵥ γ < o ⬝ᵥ paramAddRho l + o ⬝ᵥ β + h) : P.1 γ = 0 := by
  by_contra; have ⟨β, m, H⟩ := P.1.support.exists_min_image (o ⬝ᵥ ·) ⟨γ, by simpa⟩
  let S e (R : ℂ[_]) m z t := ∑ γ ∈ R.1.support, R.1 γ * weightMinors γ (signMatrix ε) *
    t ^ (o ⬝ᵥ γ - (o ⬝ᵥ β - m)) * z ^ (e ⬝ᵥ γ); have z : 0 < circleMap 0 1 0 := by simp [circleMap]
  refine absurd (_root_.linearIndependent_iff'.1 ((linearIndependent_monoidHom (Multiplicative
    _) ℂ).comp (fun γ ↦ ⟨⟨fun e ↦ 2⁻¹ ^ (e.toAdd ⬝ᵥ γ), by simp⟩, by simp⟩) fun a b h ↦
    funext fun i ↦ by simpa using congr(‖$h (.ofAdd (Pi.single i 1))‖)) _ _ (funext fun e : n → ℤ ↦
    (Finset.sum_apply ..).trans (?_ : S e P 0 _ 0 = 0)) β m) (by simp_all [signMatrix])
  have ⟨C, _⟩ := Finite.exists_le (2 * |e ·|); let L := o ⬝ᵥ paramAddRho l + h
  have ⟨r, _, hr⟩ := ((isOpen_openOrbit_and_lintegral_le hg.1 ε
    1).1.isClosed_compl.isCompact.eventually_forall_of_forall_eventually (P := fun r k ↦ ∃ i j, ε
    i ≠ ε j ∧ r * ‖weightMinors (-l.compactForm.lowestKType) (k.1.1ᴴ * signMatrix ε * k)‖ < ‖k.1 i
    j ^ 2‖ ^ h / 2 ^ (C * h - e ⬝ᵥ paramAddRho l)) fun k ↦ Not.imp_symm fun y ↦
    have c := mem_blockDiagAlg_iff_commute.1 (mem_blockDiagAlg (x := k).2 fun i j p ↦ y.imp_symm
      fun _ ↦ (ContinuousAt.eventually_lt ?_ ?_ (by simp; positivity)).mono fun _ h ↦ ⟨i, j, p, h⟩);
      ⟨⟨k, by simp [U, c.right_comm, by simpa [U] using
      k.2]⟩, 1, by simp [IsBorelMatrix]⟩).exists_gt (a := 0)
  refine norm_le_zero_iff.1 (((isClosed_le ?_ ?_ : IsClosed {t : ℝ | ‖S e P 0 _ t‖ ≤ ‖S e Q L 2⁻¹ t‖
    / r}).mem_of_tendsto summable_geometric_two.tendsto_atTop_zero ((eventually_gt_atTop C.toNat
    ).mono fun s u ↦ ?_)).trans_eq (by simp [S, _root_.zero_zpow_eq]; grind [Finset.sum_eq_zero]))
  rotate_left 2; let D (z : ℂ) := diagonal (z ^ (s • o + e) ·)
  have A {z} h := (PosDef.diagonal fun _ ↦ zpow_pos h _).isAccretive.setOf_mem_nhds (z := D z)
  have E := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (f := fun z ↦ S e P 0 z (z ^ s)) (g
    := (fun z ↦ S e Q L z (z ^ s) / z ^ (s * L)) * offOrbitIntegral l ∘ D) (fun _ z ↦ ?_) (fun _ z ↦
    .mul ?_ (((isAnalyticFamily_of_differentiable (.mono (A z) fun _ _ _ ↦
    ⟨?_, ?_⟩)).analyticAt_integral _).comp (((diagonalLinearMap n
    ℂ ℂ).toContinuousLinearMap.analyticAt _).comp (.pi ?_)))) (convex_Ioi _).isPreconnected z
    (((hasDerivAt_circleMap ..).tendsto_nhdsNE (by simp)).frequently (.mono (Eventually.frequently
    ((?_ : ContinuousWithinAt (D ∘ _) ..) (A z))) fun z _ ↦ ?_)) (one_half_pos (α := ℂ))
  any_goals fun_prop (disch := first | grind | simp [ne_zero_of_re_pos z.1, *])
  simp [D] at E; simp [E]; grw [offOrbitIntegral, norm_setIntegral_le_of_norm_le_const
    (C := 2 ^ (-s * L) / r) (by simp) fun k ↦ ?_ ∘ hr k, measureReal_le_one]
  simp [field]; rintro ⟨i, j, p, q⟩
  grw [le_div_iff₀', norm_div, mul_div, q, div_le_of_le_mul₀] <;> try positivity
  have := le_norm_weightMinors_twoPowDiagConj h k (-paramAddRho l) (-(s • o + e)) i j (s - C)
    (by simp [U.inv_mat]) (by simp [hg.paramAddRho_lt_iff]; intro a c k; grind
    [Int.mul_le_mul_of_nonneg_left (ho _ _ k) s.cast_nonneg])
    (by simp; grind [paramAddRho, by exact_mod_cast hg.3 i j p])
  simp [L, mul_pow, div_pow, field, dotProduct] at *; grind
  specialize hP fun i ↦ ⟨ε i * circleMap 0 1 z ^ (s • o + e) i, by simp [Submonoid.unitSphere]⟩
  simp_all [torusEval, signMatrix, diagTorus, ← mul_assoc, ← Int.cast_mul, S, D, dotProduct,
    mul_div, ← sum_div, lift_apply', div_mul_eq_mul_div, field]

end

attribute [-instance] FiniteField.instGrindPowIdentity IsOrderedRing.toIsStrictOrderedRing
  instIsCharPOfIsLeftCancelAddOfCharP

/-- Rearrangement inequality with a gain: for integer vectors o, b with o_i < o_j whenever b_j <
b_i, ⟨o,b⟩ + |b_i−b_{w(i)}| ≤ ⟨o,b∘w⟩ for every permutation w and index i. -/
lemma Orbital.dotProduct_add_gain_le_comp_perm {n} [Fintype n] (o b : n → ℤ) (ho : ∀ i j,
  b j < b i → o i < o j) (w : Perm n) i : o ⬝ᵥ b + |b i - b (w i)| ≤ o ⬝ᵥ b ∘ w := by
  have p s : (o + Pi.single i (cond s 1 (-1))) ⬝ᵥ b ≤ _ ⬝ᵥ b ∘ w :=
    Antivary.sum_mul_le_sum_mul_comp_perm fun x y z ↦ by grind [ho y x z, Pi.add_apply]
  simp_all; grind

/-- Harish-Chandra: for λ of gap 500n³+10n⁵ and signature (p,q), deg_λ =
∏_{λ_j<λ_i}(λ_i−λ_j)/∏_{i<n} i!; for x in the torus with distinct entries, (−1)^{pq}
Σ_{σ∈S_n} ∫_G e_λ(g⁻¹(x∘σ)g) dg = p!q!·conj χ(x), χ the character of U(n) of highest weight
λ−ρ.

Known result: Discrete series character on the compact Cartan by orbital integrals; formal
degree. -/
lemma Orbital.harish_chandra_degree_and_orbital {n : Type} [Fintype n] {ε} {l : HCParam ε} [Nonempty
  n] (hg : l.HasLargeGap (10 * Fintype.card n ^ 5)) : l.formalDegree = weylDimensionPoly l ∧ ∀ x,
  x.Injective → (-1) ^ #(oppositePairs ε) * ∑ σ : Perm n, ∫ g, l.dsKernel (g⁻¹ * diagTorus ε (x ∘ σ)
  * g) = #{σ : Perm n | ε ∘ σ = ε} * star (l.compactForm.lowestKType.kTypeChar (diagTorusK x)) := by
  let h := 500 * Fintype.card n ^ 3 + 10 * Fintype.card n ^ 5; have g : l.HasGap h := by lia
  let o := (-l).compactForm.lowerCount Eq; let κ := paramAddRho l + o
  have hκ a : l a + Fintype.card n - 1 = 2 * κ a := by
    simp [κ, o, lowerCount]; grind [two_mul_paramAddRho, twoRho, card_lt_add_card_gt_add_one g.1 a]
  have k s : (toHCParam s l).lowestKType + (toHCParam s l).lowerCount Eq =
    κ - (-toHCParam s l).lowerCount Ne := by simp [κ, o, lowestKType, twoRho, lowerCount,
    filter_and, filter_not, sdiff_inter_right_comm, funext_iff]; grind
  have vt : l.rootProd Eq * l.rootProd Ne =
    l.compactForm.rootProd Eq := by simp [rootProd, prod_filter, ← prod_mul_distrib]; grind
  obtain ⟨W, G, ⟨P, aP, eP, ht⟩, σ, s1, lk⟩ := by simpa [↓k, lowerCount, Pi.sub_def] using
    (weyl_character_kTypeChar g.signs_one.1
    g.signs_one.isKDominant_lowestKType).2, by exact_mod_cast g.3, exists_laurent_orbital_integral l
    hg, orbital_eq_char_sub_offOrbitIntegral g; set N := 4 * Fintype.card n ^ 2
  set D := (-l).rootProd Ne; let δ := (-l).lowerCount Ne; let s : ℂ := (-1) ^ #(oppositePairs ε)
  have e : D = s • l.rootProd Ne := eq_of_torusEval_eq fun x ↦ by
    simp [D, s, torusEval_rootProd_noncompact, g.1, g.neg.1, ← mul_assoc,
      ← prod_neg]; left; congr! 1; grind [HasGap, oppositePairs]
  let c := l.formalDegree * l.compactForm.lowestKType.kTypeNormSq * s / σ; let E ε :=
    D ^ N * alternant ε κ; let b := κ + N • δ
  have nn r [DecidableRel r] x γ (c : (l.compactForm.rootProd r * D ^ N).1 γ ≠ 0) :
      o ⬝ᵥ (x + (-l).compactForm.lowerCount r + N • δ) < o ⬝ᵥ x + o ⬝ᵥ γ + h := by
    simp [add_assoc, ↓dotProduct_add, dotProduct, δ, o,
      lowerCount]; grw [← ((mul_mem (rootProd_mem_leadingMonomials l.compactForm r l) (pow_mem
      (rootProd_mem_leadingMonomials l Ne l) N)).2 γ (by simpa [e, smul_pow, s] using c)).1 _]
    (repeat grw [card_le_univ]); simp [N, h]; rw [← sub_pos]; ring_nf; positivity
  have m i j (p : l j < l i) : o i < o j ∧ b j < b i :=
    ⟨by grind [two_mul_paramAddRho g, Pi.add_apply], by
    simp [b, δ, lowerCount]; by_cases N * Fintype.card n < κ i - κ j; grw [card_le_univ]; lia
    apply add_lt_add_of_lt_of_le <;> (try gcongr 3) <;> grind⟩
  -- levels of `D ^ k` times a function supported in the Weyl translates of the cone
  have lev {k a} P : IsConeSeriesMultiple l a (D ^ k) P → a + k • δ = b → P.1 b = 1 ∧ ∀ γ,
    P.1 γ ≠ 0 → ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w ≤ o ⬝ᵥ b := fun ⟨t, hf, ht⟩ d ↦ by
    simp [hf]; clear * - m g ht d
    have := by simpa [leadingMonomials] using pow_mem (rootProd_mem_leadingMonomials (-l) Ne o) k
    have e γ β (c : (D ^ k).1 β * t (-β + γ) ≠ 0) : ∃ w : Perm n, ε ∘ w = ε ∧ o ⬝ᵥ γ ∘ w +
        ite (β ∘ w = k • δ) 0 1 ≤ o ⬝ᵥ b := (ht.2 _ (right_ne_zero_of_mul c)).elim fun μ ⟨j, p⟩ ↦ by
      obtain ⟨w, q, rfl⟩ := by simpa [comp_symm_eq] using inv_surjective.exists.1 (
        exists_ne_zero_of_sum_ne_zero (j ∘ (alternant_apply _).trans))
      simp [rootCone, Pi.add_comp, Pi.neg_comp, ← d] at *
      grind [(@torusEval_comp_eq_mul_iff _ _ (D ^ k) w 1).1 (by simp [D,
        torusEval_rootProd_noncompact_comp g.neg.1, ← q])]
    refine ⟨(Finset.sum_eq_single (k • δ) (fun _ _ n ↦ by_contra (e _ _ · |>.elim fun w _ ↦ ?_))
      (by grind)).trans (by grind), by grind [exists_ne_zero_of_sum_ne_zero, Finsupp.sum]⟩
    simp [imp_iff_not_or] at m; simp_all [show ⇑w = id by ext i; grind [m i (w i), m (w i) i,
      HasGap, dotProduct_add_gain_le_comp_perm o b (fun i j ↦ by grind [m j i, HasGap]) w i]]
  obtain ⟨⟨p1, p2⟩, q1, q2⟩ := lev _ ht (by grind), lev (E ε) ⟨_,
    AddMonoidAlgebra.coeff_mul_apply_left _ _, by
    rw [alternant_apply, Fintype.sum_eq_single 1] <;> simp [funext_iff, Perm.ext_iff]
    grind [HasGap], by simp [rootCone]; grind⟩ rfl
  suffices R : P = c • E ε by
    simp [*] at p1
    refine ⟨by simpa [c, s, abs_of_pos, formalDegree_pos hg, s1,
      ← weyl_dimension_formula g.signs_one, field, ne_of_gt] using congr(‖$p1‖), fun x u ↦
      star_injective (mul_left_cancel₀ (torusEval_rootProd_ne_zero l.compactForm Eq u) ?_)⟩
    have a τ := congr(Perm.sign τ * torusEval (x ∘ τ) $R)
    have := @torusEval_rootProd_ne_zero
    simp [↓eP, *, E, pow_succ', ← mul_assoc, ← Int.cast_mul, mul_comm s, field,
      s, weyl_denominator g.signs_one.1 ▸ (torusEval_comp_eq_mul_iff
      _).2 (isWeylAntisymm_alternant _ rfl)] at a
    simp [dsKernel, integral_conj, mul_sum, ← mul_assoc, *, mul_left_comm _ (#_ : ℂ)]
    simp [alternant, torusEval, mul_sum, ← sum_filter, mul_left_comm, sum_comm,
      ← by simpa [det_apply', mul_sum] using (fun w ↦
      (det_transpose _).trans (det_permute' w⁻¹ (Matrix.of fun a b ↦ (x a).1 ^ κ (w b))))]
  ext γ; by_contra z; have ⟨w, hw, u⟩ := by_cases (fun _ ↦ q2 γ <| by simp_all) (p2 γ)
  have y : (E 1).1 (γ ∘ w) = w.sign * (E ε).1 γ := .trans ?_ ((torusEval_comp_eq_mul_iff w).1
    (by simp [E, *, torusEval_rootProd_noncompact_comp g.1, (torusEval_comp_eq_mul_iff w).2,
    isWeylAntisymm_alternant w, field]) _)
  apply z; simpa [aP w, *, field] using coeff_eq_zero_of_low_level g (P :=
    P - c • E 1) (Q := -(l.formalDegree * s / σ) • _) (by
    simp_all [E]; grind [norm_zero]) (m · · · |>.1) _ (u.trans_lt ∘ nn _ _ · ∘ right_ne_zero_of_mul)
  simp [E, AddMonoidAlgebra.coeff_mul_apply_left, alternant_apply, Finsupp.sum]; congr! with β B v
  specialize nn Ne κ β; simp [rootProd, lowerCount.eq_unfold] at nn ⊢; intro; funext i
  grind [dotProduct_add_gain_le_comp_perm o κ (by grind [Pi.add_apply]) v i, dotProduct_add,
    dotProduct_neg]
end

-- part: Lib.LocalGL.TraceFormula.TraceComparison
section
/-! Known result: Comparison of simple trace formulas for unitary groups that differ only at real
places. The form here uses integrable idempotent kernels of very regular discrete series in place of
pseudo-coefficients, elliptic test functions, and a CM field containing the 5040th roots of unity
with an even number of infinite places. Convergence is obtained by packing, with no truncation and
no endoscopy. Source: Labesse, Changement de base CM et séries discrètes (2011), Thm 5.4 and its
proof; Arthur and Clozel (1989), ch. 1, Lemmas 2.4-2.6; integrable test functions as in Knightly and
Li, Traces of Hecke operators (2006).

Known result: Selberg principle, that orbital integrals of an idempotent vanish off the elliptic
set. The form here is for a minimal convolution idempotent with polynomial decay on a product of
groups U(p,q), inside the adelic orbital integral of a rational point with irreducible
characteristic polynomial. If that integral is non-zero, all eigenvalues have absolute value 1.
Source: Harish-Chandra, Discrete series II, Acta Math. 116 (1966), Thm 11; Blanc and Brylinski,
Cyclic homology and the Selberg principle, J. Funct. Anal. 109 (1992); Hochs and Wang, Orbital
integrals and K-theory classes (2019), Cor 4.8.

This file: Equal Hecke traces on unitary groups differing at real places; Selberg principle. -/

noncomputable section

open NumberField MeasureTheory Measure Matrix Polynomial Module Subgroup Complex Norms.L2Operator
  MulAction Pointwise Finset InnerProductSpace Equiv ComplexOrder ProbabilityTheory
  Fintype Real ConjAct ENNReal


variable {E n : Type} [Field E] [CMType E] [Fintype n] {s} (V : Space E n s) {B}
  (hE : Even (numInfPlaces E)) (hB : 16 * finrank ℚ E * (card n + 1) ^ 3 ≤ B) {Ω :
  Set
  (Gf E n)} (hΩ : IsCompact Ω) (hi : ∀ g ∈ Ω, ∃ w, Irreducible (g.atPlace w).1.charpoly) {k : _ → ℂ}
attribute [-simp] inv_mul_cancel₀ isConj_iff inv_mul_cancel_left₀ IsUnit.inv_mul_cancel_left
  mul_inv_cancel_left₀ IsUnit.mul_inv_cancel_left mul_inv_cancel_comm_assoc

/-- If A has irreducible characteristic polynomial, y ≠ 0 and Aʲy = Bʲy for all j ≤ n, for n × n
matrices A, B over a field, then A = B. -/
theorem eq_of_pow_mulVec_eq {F n} [Field F] [Fintype n] {A B : Matrix n n F} {y}
    (hA : Irreducible A.charpoly) (hy : y ≠ 0) (h : ∀ j ≤ card n, A ^ j *ᵥ y = B ^ j *ᵥ y) :
    A = B := toLin'.injective (LinearMap.ext_on_range (((degreeLT.basis F _).linearIndependent.map'
  (((aeval A).toLinearMap.smulRight y).domRestrict _) (bot_unique fun q l ↦ q.ext
  (eq_zero_of_dvd_of_degree_lt (hA.dvd_iff_not_isCoprime.2 (hy <| isUnit_aeval_iff_isCoprime.2
  · |>.smul_eq_zero.1 l)) (by simpa using mem_degreeLT.1 q.2)))).span_eq_top_of_card_eq_finrank'
  (by simp)) fun j ↦ by simpa [pow_succ', ← mulVec_mulVec, ← h j j.2.le] using! h _ j.2)

/-- For x in GL_n(𝔸_f) and y in GL_n(E), the GL_n(E)-orbit of (xG_f, y), with z acting by
(zxG_f, zyz⁻¹); formally the orbit of the triple (xG_f, y, 0). -/
def frameClass (a : _ × GL n E) :=
  Quotient.mk (orbitRel (GL n E) (MarkedTriple (U 1))) (⟦a.1⟧, a.2, 0)

lemma frameClass_eq_iff {x x' : GL n (𝔸f E)} {y y'} : frameClass (x, y) = frameClass (x', y') ↔ ∃ z,
  x⁻¹ * toFinGL z * x' ∈ U 1 ∧ z * y' * z⁻¹ = y := Quotient.eq.trans (exists_congr fun _ ↦ by
  erw [mul_assoc, ← QuotientGroup.eq, Prod.mk_inj, Prod.mk_inj]; tauto)

namespace Space

/-- For a rational γ in U(J)(E), seen in G, the function x ↦ k((x⁻¹γx)_∞)·1_Ω((x⁻¹γx)_f) on G,
for k a function on G_∞ and Ω a subset of G_f. -/
def geometricTerm (k : _ → ℂ) (Ω : Set _) γ x :=
  k (x⁻¹ * V.ratEmbed γ * x).1 * Ω.indicator 1 (x⁻¹ * V.ratEmbed γ * x).2

/-- The orbital integral of a class c: the sum, over the γ in U(J)(E) with `frameClass` (x_f, γ) =
c, of the integral over Γ\G of the term `Space.geometricTerm` of γ. -/
def orbitalIntegral k Ω c := ∑' γ : (frameClass ⟨V.xFin, ·.1⟩) ⁻¹' {c}, ∫ x,
  V.geometricTerm k Ω γ.1 x ∂V.quotMeasure

lemma mem_U_one_iff_gram_eq {y z β} (k : y.1ᴴ * .map β (algebraMap ..) * y.1 = 1) :
  V.xFin⁻¹ * toFinGL z * y ∈ U 1 ↔ z.1ᴴ * V.J * z.1 = β := by erw [mem_U, gram_mul_of_gram_eq
  (gram_mul_of_gram_eq (gram_inv_of_gram_eq gram_xFin) rfl) rfl, ← k, y.mul_left_inj,
  (star y).mul_right_inj, ← map_conjTranspose_mul_mul] <;> simp [← ext_iff, -Matrix.map_mul]

@[fun_prop] lemma measurable_geometricTerm (hΩ : IsCompact Ω) (hm : Measurable k) γ : Measurable
  (V.geometricTerm k Ω γ) := by fun_prop (disch := exact hΩ.measurableSet) [geometricTerm]

include hi

lemma irreducible_charpoly_of_local {γ x} : x⁻¹ * V.embFin γ * x ∈ Ω → Irreducible γ.1.1.charpoly :=
  (hi _ · |>.elim fun w h ↦ (charpoly_monic _).irreducible_of_irreducible_map (algebraMap ..) _
  (by simpa [coe_embFin, ← charpoly_map] using! (charpoly_map ..).subst h))

include hB hΩ

/-- Unfolding: B ≥ 16[E:ℚ](n+1)³, Ω compact, each point with irreducible characteristic polynomial
at some finite place, k measurable, |k(g)|(∏‖g_w‖)^B bounded. Then `Space.geometricTerm` of γ is
integrable over Γ_γ\G (Γ_γ the centraliser) with integral `Space.orbitalIntegral` of γ's class;
these sum to ∫_{Γ\G} ∑_γ `Space.geometricTerm` of γ. -/
lemma orbitalIntegral_unfold [Nonempty n] (j : ∃ C, ∀ g, ‖k g‖ * (∏ w, ‖(g w).1.1‖) ^ B ≤ C) (hm :
  Measurable k := by fun_prop) :
  (∀ γ, let S := (centralizer {γ}).map V.ratEmbed; let F := V.geometricTerm k Ω γ; S.FixesLeft F ∧
      Integrable F S.qms ∧ V.orbitalIntegral k Ω (frameClass (V.xFin, γ)) = S.qms[F]) ∧
  HasSum (V.orbitalIntegral k Ω) V.quotMeasure[(∑' γ, V.geometricTerm k Ω γ ·)] := by
  have : Countable (GL n E) := Units.val_injective.countable
  suffices _ from ⟨fun p ↦ (integral_tsum_orbit (i := V.ratEmbed.comp ofConjAct.toMonoidHom) (Γ :=
    V.Γ) V.ratEmbed_injective rfl (by fun_prop) (by simp [geometricTerm, ConjAct.smul_def,
    mul_assoc]) (congrArg _ (stabilizer_eq_centralizer _)) fun _ ↦ frameClass_eq_iff.trans
    (by simp [↓V.mem_U_one_iff_gram_eq gram_xFin, Subtype.ext_iff, mem_U, isConj_iff])).imp_right
    (· (.inl this) |>.imp_right (·.2)), (hasSum_integral_of_lintegral this).tsum_fiberwise _⟩
  rcases j, V.exists_smul_mulVec_mem_latticeBall hΩ with ⟨⟨C, hC⟩, c, hc, H⟩
  refine' (lintegral_mono fun x ↦ _).trans_lt (lintegral_const_lt_top ofReal_ne_top)
  have l := (V.move x).firstMinimum_pos.trans_le ((csInf_insert ?bdd ?ne).trans_le inf_le_right)
  let ⟨_, ⟨y, ⟨hy, y0⟩, rfl⟩, e⟩ := exists_lt_of_csInf_lt ?ne (lt_two_mul_self l)
  let g γ := x⁻¹ * V.ratEmbed γ * x
  let Z := {γ | (g γ).2 ∈ Ω}
  have o (γ : Z) := le_prod_opNorm (g γ).1
  have p (a : Z) j : (c : E) ^ j • a.1.1.1 ^ j *ᵥ y ∈ latticeBall _ ((c * _) ^ j * _) := j.rec
    (by simpa using ⟨hy, e.le⟩) fun j i ↦ by simpa [pow_succ', mul_smul]
    using (@H _ x x _ a.2 (o a).2 _ i.1).imp_right (·.trans (by grw [i.2, ← mul_assoc]))
  have b := tsum_le_of_separated l (R := c ^ _ * (2 * _)) (by positivity) (fun a b ↦ Not.imp_symm
    fun l ↦ ?_) (one_le_pow₀ <| o · |>.1) (fun a ↦ (pi_norm_le_iff_of_nonempty _).2 fun j : Fin
    (card n + 1) ↦ (p a j).2.trans (by grw [j.is_le, mul_pow, mul_right_comm]; bound [o a,
    hc.bot_lt])) (lt_two_mul_self (mod_cast finrank_pos)) (c := 2) (by grind)
  simp [mul_div_assoc, l.ne', finrank_eq_two_mul_card_infinitePlace, ← ofReal_norm] at b hB ⊢
  grw [← tsum_subtype_eq_of_support_subset (s := Z) fun _ ↦ by simp_all [geometricTerm, Z, g],
    ENNReal.tsum_le_tsum fun γ ↦ ofReal_mono ?_, ← ofReal_tsum_of_nonneg
    (fun _ ↦ by positivity) (b.1.mul_left |C|), tsum_mul_left, b.2]
  erw [geometricTerm, Ω.indicator_of_mem γ.2, mul_one, rpow_neg_eq_inv_rpow]
  norm_cast; grw [inv_pow, le_mul_inv_iff₀, ← pow_mul, (by lia : _ * _ ≤ B), hC] <;> bound [o γ]
  ext : 3; exact eq_of_pow_mulVec_eq (V.irreducible_charpoly_of_local hi a.2) y0 fun j i ↦ by_contra
    fun _ ↦ l (csInf_le_of_le ?bdd ⟨_, ⟨sub_mem (p a j).1 (p b j).1, by simpa [hc]⟩, by simp⟩
    (norm_le_pi_norm _ ⟨j, by lia⟩))
  exacts [⟨0, by aesop_cat⟩,
    have ⟨_, a, b⟩ := exists_smul_mem_baseLattice 1; .image _ ⟨_, b, by simpa [funext_iff]⟩]

attribute [-instance] Prod.isScalarTower in
/-- Let e be a cusp kernel of order B ≥ 16[E:ℚ](n+1)³, Ω ⊂ G_f compact, each point with irreducible
characteristic polynomial at some finite place. If the orbital integral of e·1_Ω at γ is nonzero, γ
has irreducible characteristic polynomial with complex roots of modulus one.

Known result: Selberg principle: orbital integrals of an idempotent vanish off the elliptic set. -/
lemma elliptic_of_integral_ne_zero [Nonempty n]
    {e} (he : IsCuspKernel B e) {γ} (hγ : ((centralizer {γ}).map
  V.ratEmbed).qms[V.geometricTerm e Ω γ] ≠ 0) : IsEllipticSimilitude 1 γ V.J := by
  obtain ⟨-, _, a⟩ := by simpa [geometricTerm] using exists_ne_zero_of_integral_ne_zero hγ
  have I := V.irreducible_charpoly_of_local hi a
  simp [IsEllipticSimilitude, I, ← mem_U, roots_eq_map_numberedRoots I.separable, mul_conj']
  intro w i
  rcases he.4, he.2, he.1.1.measurable, (isConj_diagonal_of_isRoot_charpoly (g := ((V.ratEmbed γ).1
    w).1.1) (by erw [charpoly_map]; simpa [← charpoly_map] using!
    isRoot_numberedRoots I.separable _)).symm with ⟨⟨C, dec⟩, J, _, k, d⟩
  let N (y : GInf E s) := ∏ w, ‖(y w).1.1‖
  let Q := diagonal (Pi.single i 1) * k.1
  have L0 : Q ≠ 0 ∧ (∀ y, 0 < N y) ∧ ∀ y, 1 ≤ N y := by simp [Q, N, prod_pos, le_prod_opNorm]
  let H (y : GInf E s) := ‖Q * (y w).1‖.log
  have hH {t} {m : ℂ} (e : Q * (t w).1.1 = m • Q) : m ≠ 0 ∧ ∀ y, H (t * y) = ‖m‖.log + H y := by
    by_cases m = 0 <;> simp_all [H, ← mul_assoc, norm_smul, Real.log_mul]
  have hQ {t} (e : Commute t _) : Q * t = (k * t * k⁻¹.1) i i • Q := k⁻¹.mul_left_inj.1 (by
    ext a b; have := congr($((d.mul_left e).mul_left d.units_inv_symm_left) i b)
    simp_all [Q, mul_assoc, diagonal_apply]; grind)
  have g := by simpa [d.eq] using hH (hQ rfl)
  have lip a b : |H (a * b) - H a| ≤ N b := .trans (by
    refine abs_sub_le_iff.2 ⟨?_, .trans_eq ?_ (U.norm_inv _)⟩ <;> grw [← log_div, log_le_self,
      div_le_iff₀', ← norm_mul_le] <;> simp [← mul_assoc, *, field]) ((le_prod_opNorm b).2 w)
  let v := @volume (GInf E s) _
  let m := ((centralizer {γ}).map V.ratEmbed).qms.prod (v.prod v)
  let c x := x⁻¹ * V.ratEmbed γ * x
  have mul a b : N (a * b) ≤ N a * N b := by simp [N]; grw [norm_mul_le]; simp
  have I {a : _ → ℝ} (ha : ∀ p, |a p| ≤ N p.2.1 * N p.2.2) (A : Measurable a := by fun_prop) :
    Integrable (fun p ↦ a p * (e p.2.1 * (e p.2.2 * e (p.2.2⁻¹ * (p.2.1⁻¹ * (c p.1).1))) *
    V.geometricTerm 1 Ω γ p.1)) m := .mono'
    ((((V.orbitalIntegral_unfold hB hΩ hi (k := (N · ^ B)⁻¹) ⟨1, by simp [N, inv_mul_le_one]⟩).1
    γ).2.1.norm.mul_prod (J.mul_prod J)).const_mul C) (by fun_prop) (.of_forall fun ⟨x, y, u⟩ ↦ by
    erw [geometricTerm, geometricTerm, ← mul_inv_cancel_left (y * u) (c x).1]; set z :=
      (y * u)⁻¹ * _
    simp [L0, abs_of_pos, field, mul_assoc]; grw [ha, mul, mul, ← dec z]; linear_combination)
  obtain ⟨h₁, h₂, O, S⟩ := I fun p ↦ (lip p.1.1 p.2.1).trans (by simp [*]), I (lip ·.1.1 _
    |>.trans (mul ..)), I (a := 1) (by simp; bound), measurePreserving_prod_inv_mul_swap v v
  have P {F : _ → ℂ} {T} h (t : MeasurePreserving T m m) := (t.fubini (f := F)
    h).2.symm.trans (integral_congr_ae ((t.fubini h).1.prod_right_ae.mono fun _ ↦ integral_prod _))
  have D := (integral_prod_symm _ ((((O.const_mul ‖numberedRoots (Φ w) γ.1.1.charpoly i‖.log).add
    h₁).sub h₂).sub h₂)).trans (.trans (congrArg _ (funext fun p ↦ .trans (by
    simp [c, geometricTerm, g, division_def, mul_assoc]; grind) (identDistrib_orbitMeasure_mul_right
    (p.1, 1) fun ⟨_, _, h, rfl⟩ y ↦ have h := Commute.map (h _ rfl) V.ratEmbed; by simp [c,
      ↓Pi.sub_apply, geometricTerm, Subgroup.smul_def, mul_assoc, h.left_comm,
      hH (hQ congr(($h.symm.1 w).1.1))]).integral_eq)) (integral_skew_product (fun x ↦
    (S.comp ((measurePreserving_div_left _ (c x).1).prod (.id _))).map_eq) ((h₂.sub h₁).sub h₁)).2)
  simp (disch := fun_prop) only [m, ← integral_prod, integral_sub', integral_add',
    integral_const_mul, P h₂ (.prod (.id _) S), P h₁ (.id _), P O (.id _)] at D
  simp [c, v, geometricTerm, he.convolution_self, ← mul_assoc _ (e (_ * _))] at D hγ
  grind [norm_nonneg]

omit hΩ hi
variable {K : Subgroup (Gf E n)} [hK : IsLevel K] {h : Gf E n}
  (hh : ∀ g ∈ h • SetLike.coe K, ∃ w, Irreducible (g.atPlace w).1.charpoly)
include hE hh

/-- Let E contain μ_5040, with evenly many infinite places; K a level; each point of hK have
irreducible characteristic polynomial at some finite place; B ≥ 16[E:ℚ](n+1)³, H ≥
500n³+10n⁵. Then ∑⟨b_i, hb_i⟩, b an orthonormal basis of K-fixed forms of type e_l, is the
same for all s, V with e_l a cusp kernel of order B, l of gap H.

Known result: Comparison of simple trace formulas for unitary groups that differ only at real
places. -/
theorem exists_trace_eq [Nonempty n] [StablyUnram E]
    l H (j : gapThreshold n (10 * card n ^ 5) ≤ H) : ∃ t, ∀ {s} (V : Space E n
  s) {ι} [Fintype ι] (b : OrthonormalBasis ι ℂ (levelSpace (V.formRep (typeKernel l s)) K)),
  IsCuspKernel B (typeKernel l s) →
  (∀ w, (toHCParam s (l w)).HasGap H) → ∑ i, ⟪(b i).1, V.formRep _ h (b i)⟫_ℂ = t := by
  choose u y o r using fun a :
    {c | ∃ u, ∃ y : GL n E, HasSignType 1 1 y {1} u ∧ frameClass (u, y) = c} ↦ a.2
  let z a w : n ↪ Circle := (numberedRoots ..).codRestrict _ (have ⟨_, ⟨I, _, _, h⟩, _⟩ := o a; by
              simp [roots_eq_map_numberedRoots I.separable] at h; simpa using congr(√‖$(h w ·)‖))
  have F a s (σ : _ → Perm n) {x} : HasSignType (s ∘ σ⁻¹ ·) 1 (y a) {1} x → ∃ W, xFin W = x ∧
      ∃ h, ∀ w, (ratEmbed W ⟨y a, h⟩).1 w = diagTorus s (z a w ∘ σ w) := fun ⟨β, hy, hx, H⟩ ↦ by
    choose k hk a using fun w ↦ have ⟨_, _, _, K, S⟩ := exists_eigenbasis_diag_form hy w (σ w); S s
        (by simpa [↓K, ↓eval_interpolate_univ_node] using H w)
    use ⟨β, _, gram_mkAdelicGL hk hx⟩, rfl, by simp [mem_U, hy.2], fun w ↦ ?_
    ext : 2; erw [coe_mk]; simpa using! a w
  choose X e q _ using (F · 1 1 (o _))
  choose β _ hβ using fun a ↦
    (hasCutoff_count ((X a).Γf ⊓ (centralizer {⟨_, q a⟩}).map (embFin _))).1
  constructor; intro s V ι _ b he g
  have ω := hK.isCompact.smul h
  obtain ⟨v, p, T, hO⟩ := (measureReal_pos_of_isLevel K).ne', integral_indicator_const (μ :=
    volume) (1 : ℂ) hK.2.measurableSet, V.orbitalIntegral_unfold hB ω hh he.4
  choose _ P using hO.summable.subtype
  choose f W hU hc hf using fun σ : _ → Perm n ↦ exists_hasSignType_mul_iff (E := E) (fun _ : ℂ ↦
    (s ∘ σ⁻¹ ·)⁻¹) (by cases hE; simp [pow_add, Equiv.prod_comp, *]) _
  replace hU σ := by simpa using (hU σ · 0 1 (s ∘ σ⁻¹ ·))
  refine (eq_inv_mul_iff_mul_eq₀ (ofReal_ne_zero.2 v)).2 (.trans ?_ ((hasSum_mul_left_iff ?_).1
    (.congr_fun (((hasSum_sum fun σ _ ↦ hasSum_subtype_iff_indicator.1 (P _)).congr_fun fun c ↦
    ?_).unique (hO.mul_left _) ▸ hasSum_sum fun σ _ ↦ ((f σ).image _).hasSum_iff.2 (P _)) fun a ↦
    ((congrArg _ (funext fun σ ↦ ?_)).trans (by simpa [← pow_mul, Fintype.prod_sum, sum_mul,
    HCParam.compactForm, hE, mul_assoc, toHCParam] using congr((∏ w,
    $((Orbital.harish_chandra_degree_and_orbital ((g w).mono j)).2 _ (z a w).2)) * ∫ v, (β a
    v).toReal • ((h • K.carrier).indicator 1 (v⁻¹ * embFin _ ⟨_, q a⟩ * v))))).symm)).tsum_eq.symm)
  choose k hk using (V.exists_kernel_form he ·⁻¹ K)
  have H x v : ⟪k x, v⟫_ℂ = _ := .trans (by
    simp [inner_eq_petersson, petersson, hk, mul_assoc, v.1.2.rat_mul, ← tsum_mul_right]; rfl)
    ((integral_quotMeasure_tsum V.Γ
    (v.1.2.isBoundedMeasurable.integrable_mul_comp (.comp_mul_left (μ := volume) (he.1.2.mul_prod
    (.of_integral_ne_zero (p.trans_ne (by simpa)))) x⁻¹) id)).2.trans ((integral_mul_left_eq_self _
    x).symm.trans ((congrArg _ (funext fun y : G E s ↦ by simp +contextual [Set.indicator,
    ← mem_levelSpace_formRep_iff.1 v.2 y.2 _ (_, x.2), Prod.mul_def])).trans
    ((integral_prod_mul ..).trans (congr($(v.1.2.3 he.1.2) x * $p).trans (mul_comm ..))))))
  erw [← integral_finsetSum _ fun i _ ↦ (b i).1.2.memLp.star.integrable_mul
    (V.formRep _ h _).2.memLp, ← integral_const_mul]
  congr with x
  refine .mp ?_ congr(star $(b.sum_inner_mul_inner (k x) (k (x * (1, h)))))
  simp [*, geometricTerm, mul_assoc, mul_left_comm, ← mul_sum, Set.indicator,
    show ∀ x (v : levelSpace (V.formRep _) K), ⟪(k x).1, v.1⟫_ℂ = _ from H,
    ← Set.preimage_smul_inv, (hk ..).trans ((ofInjective _ V.ratEmbed_injective).tsum_eq _).symm]
  simpa using ⟨1, rfl⟩
  obtain ⟨Y, d, hy, ht⟩ := F a s σ ((hU ..).1 (o a))
  obtain ⟨b, l, h, -, hγ⟩ := V.exists_eq_move Y
  set j := U.conj b h
  have c z (h : y a * z = z * y a) : (u a)⁻¹ * toFinGL z * u a = Y.xFin⁻¹ * toFinGL z * Y.xFin := by
    simp [*, mul_assoc, (hc _ _ _ _ h).left_comm]
  simp [← r, -real_smul]
  erw [(hf _ _ _ ⟦_⟧).trans (frameClass_eq_iff.2 ⟨b, d ▸ (V.mem_U_one_iff_gram_eq gram_xFin).2 h,
    rfl⟩).symm, (T (j ⟨_,
    hy⟩)).2.2, IsCutoff.integral_orbitMeasure (β := (β a ·.2) ∘ (l⁻¹ * ·)) ⟨by fun_prop, fun g ↦ ?_⟩
    ((T _).1 _ ·.2), ← integral_fintype_prod_eq_prod, (by simp [Gf.val_ext_iff, coe_embFin,
    *] : (X a).embFin _ = Y.embFin ⟨_, hy⟩), ← integral_prod_mul, ← integral_mul_left_eq_self _ l]
  simp [typeKernel, geometricTerm, *, mul_assoc, -real_smul]; rfl
  erw [← hβ a (l⁻¹ * g).2, lintegral_count, lintegral_count, tsum_image (fun t ↦ β a (_ * (t *
    g)).2) V.ratEmbed_injective.injOn, (?_ : _ ⊓ _ = .map (Y.embFin.comp j.symm) (centralizer {j ⟨_,
    hy⟩})), tsum_image (β a <| · * _) (Y.fact_embFin_injective.1.comp j.symm.injective).injOn]
  simp [embFin, mul_assoc, (by simpa using hγ <| j.symm ·)]
  ext; simp [mem_centralizer_iff, ← map_mul, reindex_equiv j, coe_embFin, Gf.val_ext_iff]
  grind [mem_U_one_iff_gram_eq, gram_xFin, mem_U]
  simp [-Set.mem_image_equiv, Set.indicator, ← sum_filter]; by_contra! ⟨b, a⟩; apply b
  obtain ⟨γ, ⟨⟩⟩ := not_isEmpty_iff.1 (a <| @tsum_empty _ _ _ _ _ _ ·)
  have m := V.elliptic_of_integral_ne_zero hB ω hh he ((T _).2.2 ▸ a)
  choose _ d b J H using (exists_eigenbasis_diag_form m · 1)
  have X w := gram_inv_of_gram_eq (x :=
    V.x.map (evalInf w)) (by simpa [stdForm] using! congr($(V.3).map (evalInf w)))
  have y w i u : 0 < d w i * (u : ℤˣ) ↔ ite (0 < d w i) 1 (-1) = u := by
    have b := congrArg (fun M ↦ IsUnit M ∧ Mᴴ = M) (gram_mul_of_gram_eq (X w) (b w))
    fin_cases u <;> simp [Complex.lt_def, Complex.ext_iff, Pi.isUnit_iff, Pi.star_def,
      -coe_units_inv] at b ⊢; grind
  choose τ H using fun w ↦
    sylvester_law_of_inertia (gram_mul_of_gram_eq (X w) (H w _ (y w · _ |>.2 rfl)).choose_spec.1)
  norm_cast; simp_rw [← Fintype.card_subtype, ← card_fun]
  refine .symm (card_congr ((subtypeEquiv (.mulLeft τ) fun σ ↦ .trans ⟨fun ⟨_, a, o, e⟩ w ↦ ?_,
    fun H ↦ mul_inv_cancel_left (W σ γ 0) V.xFin ▸ ⟨_, γ, (hU σ ..).2 ⟨_, m, by simp [gram_xFin],
    H⟩, hf ..⟩⟩ (forall_congr' fun w ↦ (J w _).trans ((reindex_equiv (σ w)).1.trans
    (by simp [↓eval_interpolate_univ_node, funext_iff, *])))).trans subtypePiEquivPi))
  obtain ⟨⟨β, _, f, H⟩, z, e⟩ := (hU σ ..).1 o, frameClass_eq_iff.1 (e.symm.trans (hf ..))
  rw [← (z.map (Φ w)).isUnit.posDef_star_left_conjugate_iff, mul_assoc, mul_assoc,
    ← aeval_semiconj (x := a.1.map (Φ w))] <;> simp [← e.2, ← Matrix.map_mul]
  simpa [↓map_conjTranspose_mul_mul, mul_assoc] using! ((V.mem_U_one_iff_gram_eq f).1 e.1 ▸ H w :)
end Space
end
end
