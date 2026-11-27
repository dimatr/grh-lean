import Lib.DiscreteSeries.RegularRepL2
import Lib.DiscreteSeries.FlenstedJensenInvariance
import Lib.DiscreteSeries.HolomorphicExtension
import Lib.DiscreteSeries.SmoothMatrices
import Lib.DiscreteSeries.AnalyticVectors

-- part: Lib.DiscreteSeries.CuspKernel.BumpConvolution
section
/-! General lemmas of real and complex analysis (textbook or folklore).

Part of: Schur orthogonality; coefficients of integrable discrete series are cusp forms (known
result; see Lib.DiscreteSeries.CuspKernel.CircleMean).

This file: Convolution with compactly supported smooth functions is smooth; derivatives fall on the
bump. -/

noncomputable section

open MeasureTheory ContinuousLinearMap Set Matrix Norms.L2Operator


variable {n} [Fintype n] (ε : n → _) {E} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex subspace of smooth complex functions on U(diag ε) that have compact support. -/
abbrev Bumps : Submodule ℂ (SmoothU ε ℂ) :=
  ⟨⟨⟨{β | HasCompactSupport β.1}, .add⟩, .zero⟩, fun _ ↦ .smul_left⟩

variable {ε} (F : USign ε → E) (α : Bumps ε) (hF : Continuous F := by fun_prop)

/-- The gl_n(ℂ)-module of compactly supported smooth complex functions on U(diag ε) under right
derivatives, a submodule of `rightDeriv`. -/
def bumpDeriv := (rightDeriv ..).restrictTo (Bumps ε) fun _ f ↦ (.intro · fun _ h ↦
  (rightDeriv_comp_clm (f := f) 0 (notMem_tsupport_iff_eventuallyEq.1 h)).eq_of_nhds)

include hF

lemma integrable_bump_inv_smul : Integrable fun y ↦ α.1.1 y⁻¹ • F y :=
  (α.2.comp_homeomorph (.inv _)).smul_right.integrable

/-- For continuous F : U(diag ε) → E, the linear map sending a compactly supported smooth α to
the function g ↦ ∫ α(y⁻¹)F(gy) dy. -/
@[simps] def smear : Bumps ε →ₗ[ℂ] USign ε → E := by
  use! fun α g ↦ ∫ y, α.1.1 y⁻¹ • F (g * y) <;> simp [add_smul, integral_add, mul_smul,
    fun g ↦ (integrable_bump_inv_smul (F <| g * ·) ·), integral_smul, funext_iff]

/-- Derivatives of a convolution fall on the test function: if a curve γ in U(diag ε) has γ'(t)
= γ(t)X, then `smear` α along γ has derivative at t the value at γ(t) of
`smear` (Xα), Xα the right derivative. -/
lemma hasDerivAt_smear {γ : ℝ → USign ε} {t X} (h : HasDerivAt (γ · |>.1.1) ((γ t).1 * X) t) :
    HasDerivAt (smear F hF α <| γ ·) (smear F hF (bumpDeriv X α) (γ t)) t := by
  obtain ⟨⟨A, a⟩, ⟨C, c⟩, N, k, m⟩ := α.1.2, h.isBigO_sub.bound, exists_compact_mem_nhds (γ t)
  obtain ⟨K, n⟩ := α.2.mul k.inv, mem_of_mem_nhds m
  let ⟨L, l⟩ := (contDiff_infty.1 A.2 1).locallyLipschitz.locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact ((K.mul k).image_auto (·.1.1))
  have ⟨i, j⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip' (c.and
    (isClosedEmbedding_U.continuousAt_iff.2 h.continuousAt m)) (by fun_prop) (.congr
    ((integrable_bump_inv_smul (F <| γ t * ·) α).comp_mul_left (γ t)⁻¹) (by simp))
    (by simp [← smulRight_one_eq_toSpanSingleton]; fun_prop) (.of_forall fun y s ⟨p, q⟩ ↦ by
    rw [indicator]; split_ifs with b
    · simp [← a, ← sub_smul, norm_smul, mul_assoc, -coe_units_inv] at *
      grw [l.norm_sub_le, ← mul_sub, norm_mul_le, p, mul_comm] <;> exact ⟨_, mul_mem_mul b ‹_›, rfl⟩
    simp [fun x o ↦ image_eq_zero_of_notMem_tsupport (b ⟨y⁻¹ * x, ·, x⁻¹, o, by simp⟩), *])
    ((K.inv.integrableOn fun y ↦ ‖F y‖ * L * ‖y⁻¹.1.1‖ * C).integrable_indicator
    K.inv.measurableSet) (.of_forall fun y ↦ (hasDerivAt_curve α.1 (γ := (y⁻¹ * γ ·)) (X := X)
    (by simp [mul_assoc, h.const_mul])).smul_const (F y))
  convert ← j.hasDerivAt <;> simp [integral_apply i] <;>
    rw [← integral_mul_left_eq_self] <;> congr! 4 <;> simp

lemma rightDeriv_smear {α f} (e : smear F hF α = f.1) X : smear F hF (bumpDeriv X α) =
  (rightDeriv ε E X f).1 := have k Y g :=
    (hasDerivAt_smear F α hF (hasDerivAt_expU Y g 0)).unique (e ▸ hasDerivAt_rightDeriv_expU ..)
  eq_unitaryLiePart_add_I_smul ε X ▸ by simp_all [funext_iff]
end
end

-- part: Lib.DiscreteSeries.FlenstedJensen.PsiBasic
section
/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Basic properties of the coefficient: polar formula, inversion, conjugation, values on
K. -/


open Matrix MeasureTheory ComplexConjugate ComplexOrder U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (g : USign ε)
attribute [local simp] flenstedJensen dsCoeff ne_of_gt
attribute [local simp↓ ←] maxCompactU.coe_inv principalMinor_coe_inv integral_conj

lemma weightMinors_unitary_inv w : weightMinors w g.1.1⁻¹ = conj (weightMinors w
  g) := by simp [↓conj_weightMinors, weightMinors, ← principalMinor_of_forall (p := ⊤)]

instance {J : Matrix n n ℂ} : SigmaCompactSpace (U J) := inferInstance

/-- The function ψ_λ takes the value 1 at the identity matrix. -/
@[simp] lemma dsCoeff_one : l.dsCoeff 1 = 1 := by simp [RCLike.mul_conj, field]; norm_cast

include hg

/-- For a parameter l = 2λ, p, q in K and z in U(diag ε) positive definite, ψ_λ(pzq⁻¹) = c_Λ⁻¹ ∫_K
m_Λ(pu) conj(m_Λ(qu)) / m_{−μ}(u*zu) du, c_Λ = ∫_K |m_Λ|², Haar probability on K. -/
lemma dsCoeff_polar (p q : maxCompactU ε) {z : USign ε} (hz : z.1.1.PosDef) :
  l.dsCoeff (p * z * q⁻¹ :) = (∫ u, weightMinors l.lowestKType (p * u.1) * conj (weightMinors
  l.lowestKType (q * u)) / weightMinors (-paramAddRho l) (u.1.1.1ᴴ * z * u) ∂haarK ε) /
  l.lowestKType.kTypeNormSq := by
    rw [dsCoeff_eq_flenstedJensen hg (mem_maxCompactU.1 (p * q⁻¹).2),
      flenstedJensen, ← integral_mul_left_eq_self _ q]
    · simp [mul_assoc]
    simpa [mul_assoc] using hz.isAccretive.conjTranspose_mul_mul (k := ↑q⁻¹)

/-- For a parameter λ of gap h and g in U(diag ε), ψ_λ(g⁻¹) is the complex conjugate of ψ_λ(g). -/
lemma dsCoeff_inv : l.dsCoeff ↑g⁻¹ = conj (l.dsCoeff g) := by
  obtain ⟨k, z, ⟨hz⟩⟩ := exists_polar g
  obtain ⟨⟩ := dsCoeff_polar hg 1 k (z := z⁻¹) (by simpa), dsCoeff_polar hg k 1 hz,
    (weightMinors_unitary_inv <| ·⁻¹ * z * ·)
  simp_all [mul_assoc, mul_comm]

/-- For a parameter λ of gap h and g in U(diag ε), ψ_{−λ}(g) is the complex conjugate of ψ_λ(g). -/
@[simp] lemma dsCoeff_neg : (-l).dsCoeff g = conj (l.dsCoeff g) := by
  obtain ⟨k, z, ⟨b⟩⟩ := exists_polar g
  obtain ⟨⟩ := dsCoeff_polar hg k 1 b, dsCoeff_polar hg.neg k 1 b
  simp_all [kTypeNormSq, (by grind [two_mul_paramAddRho, hg.neg, twoRho_neg, Pi.neg_def] :
    paramAddRho (-l) = -paramAddRho l)]
  norm_cast; simp [↓weightMinors_neg, ↓weightMinors_unitary_inv]

/-- For a parameter λ of gap h and k in K = U(diag ε) ∩ U(n), ψ_λ(k) = m_Λ(k), the product of
principal minors of weight Λ = λ + ρ − 2ρ_c. -/
lemma dsCoeff_of_mem_maxCompactU {k} (hk : k ∈ maxCompactU ε) : l.dsCoeff k =
  weightMinors l.lowestKType k := by simp_all [mem_maxCompactU,
  by simpa using (isHolOfWeight_weightMinors hg.neg.1 k fun () ↦
  hg.isKDominant_lowestKType).integral_mul_conj_weightMinors hg.neg.1 hg.isKDominant_lowestKType]
end

-- part: Lib.DiscreteSeries.FlenstedJensen.KTypeProjection
section
/-! Known result: Flensted-Jensen's function, the coefficient of the lowest K-type of a discrete
series. It is treated for U(p,q) and parameters with a gap, with the integrand written by principal
minors and a decay bound whose constant does not depend on the parameter. Existence of the discrete
series is not assumed. Source: M. Flensted-Jensen, Discrete series for semisimple symmetric spaces,
Ann. of Math. 111 (1980) 253-311; B. Sun, Matrix coefficients of cohomologically induced
representations, Compositio Math. 143 (2007), Thm 1.1 (arXiv math/0403440); A. Knapp, Representation
Theory of Semisimple Groups (1986), ch. IX.

This file: Lowest K-type occurs once; K-types outside the cone above it do not occur. -/

open Matrix MeasureTheory ComplexConjugate Norms.L2Operator ComplexOrder
attribute [local simp] diagTorus Pi.star_def ne_of_gt weightMinors_unitary_inv

/-- Let l = 2λ be a parameter of some gap, x, b in U(diag ε), ν K-dominant. Then ∫_K
conj(m_ν(k)) ψ_λ(xkb) dk is c_Λ ψ_λ(x)ψ_λ(b), c_Λ = ∫_K |m_Λ|², if ν = Λ, and 0 if ν ≠ Λ and
ν − Λ lies outside `HCParam.rootCone`.

Known result: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series. -/
lemma integral_conj_weightMinors_mul_dsCoeff {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) (x b :
  USign ε) {ν} (hν : IsKDominant ε (-l) ν) (hz : ν = l.lowestKType ∨ ν - l.lowestKType ∉
  l.rootCone) : ∫ k, conj (weightMinors ν k.1) * l.dsCoeff ↑(x * k * b) ∂haarK ε = if ν =
  l.lowestKType then l.lowestKType.kTypeNormSq * (l.dsCoeff x * l.dsCoeff b) else 0 := by
  obtain ⟨o, ho, N, hN, hz⟩ : ∃ o, _ ∧ ∃ N : ℕ, N = o ⬝ᵥ (ν - l.lowestKType) ∧
    (N = 0 ↔ ν = l.lowestKType) := hz.elim (⟨-l, by simp [·]⟩) (not_forall₂.1 · |>.imp fun o h ↦
    ⟨h.1, _, Int.toNat_of_nonneg (by lia), by aesop⟩)
  have oj : o.Injective | i => by have := ho i; grind [HasGap]
  obtain ⟨⟨T, D⟩, c, _, rfl, ca, _⟩ := (by grind [IsKDominant, mt (ho _ _), HasGap, Pi.neg_apply,
    paramAddRho] : (Unit → IsKDominant ε o ν) ∧ IsKDominant 1 (-o) (-paramAddRho l)),
    exists_analytic_path (.inl rfl) b (by simp)
  let S y (k : maxCompactU ε) := k.1.1.1ᴴ * y * k
  obtain ⟨I, p, Z⟩ := neg_injective.comp oj, l.analyticAt_dsCoeff,
    isCompact_univ.eventually_forall_mem (x₀ := 1) (fun y k ↦ S ((blockDiagPart ε x)⁻¹ * x) k * y)
    {z | z.IsAccretive} (by simp [S, IsAccretive.setOf_mem_nhds])
  rw [← mul_boole]; generalize (1 : ℝ) = t; revert t
  refine congrFun (AnalyticOnNhd.eq_of_eventuallyEq (fun t _ ↦
    ((IsAnalyticFamily.of_analyticAt (.prodMk ?_ ?_) (fun (b, y, z) ↦
    y * l.dsCoeff (z * b)) fun k ↦ have := p (x * ↑k * c t); ?_).analyticAt_integral
    _).restrictScalars.comp (ca t)) (fun t _ ↦ have := (p (c t)).restrictScalars (𝕜 := ℝ); ?_)
    (.mono ((ca 0).continuousAt (isCompact_univ.eventually_forall_mem S _ fun k _ ↦ (Z.and (.and
    PosDef.one.isAccretive.setOf_mem_nhds (eventually_exists_torus_entire_factor I D
    Z))).filter_mono (by simp [*, S, ← maxCompactU.coe_inv])))
    fun t h ↦ ?_)) <;> try fun_prop (disch := simp)
  choose U W A C tC _ _ P _ e using by simpa [S, -Subtype.forall] using h
  let G (j k : maxCompactU ε) y := weightMinors l.lowestKType (blockDiagPart ε x * j) * conj
    (weightMinors l.lowestKType k) / weightMinors (-paramAddRho l) (S ((blockDiagPart ε x)⁻¹ *
    x) j * y); have : Continuous (fun j k ↦ weightMinors ν (k * j⁻¹).1 * G j k
    (S (c t) k)).uncurry := by unfold G S; fun_prop (disch := simp [U])
  simp only; rw [dsCoeff, dsCoeff_eq_flenstedJensen hg (one_mem _) (by simpa using W 1),
    flenstedJensen, flenstedJensen]; field_simp
  simp_rw [← integral_prod_mul, ← integral_mul_const]
  refine .trans ?_ (((measurePreserving_mul_prod ..).fubini (integrable_of_compactSpace
    this)).2.trans (integral_eq_of_circle_mean (fun θ ↦ map_mul_right_eq_self _ (1,
    diagTorusK (θ.toCircle ^ o ·))) (integrable_of_compactSpace this) fun (j, k) ↦ .trans ?_
    (((isHolOfWeight_weightMinors oj k T).circle_mean_weightMinors oj T (fun _ ↦ mem_maxCompactU.1
    j⁻¹.2) (fun s ↦ s ^ N * G j k (A k s) / diagChar (-paramAddRho l) (C k)) ?_).trans ?_)))
  · congr with k; rw [dsCoeff_eq_flenstedJensen hg (mul_mem (blockDiagPart_mem x) (mem_maxCompactU.1
      k.2)), flenstedJensen] <;> simp [G, S, mul_assoc, ← maxCompactU.coe_inv]
    simpa [S, mul_assoc, ← maxCompactU.coe_inv] using U 1 k
  · congr with θ; set s := θ.toCircle; have :=
      D.weightMinors_mul_borel I (P k s s.norm_coe.le j).det_ne_zero
      (by simp) (((isBorelMatrix_diagonal s).mul (tC k)).mul (isBorelMatrix_diagonal s⁻¹))
    simp at this; rw [mul_assoc, ← (A k s).mul_assoc, ← e] at this
    simp [G, S, mul_assoc, conj_weightMinors, dotProduct, diagChar, hN, ← _root_.zpow_mul,
      ← zpow_sum_of_ne_zero,
      mul_sub, zpow_sub₀, ← s.coe_inv_eq_conj, ← zpow_natCast s.1] at *; simp [*]; field_simp; simp
  simp_intro s r; fun_prop (disch := simp [*, S, -det_mul, IsAccretive.det_ne_zero])
  simp [zero_pow_eq]; grind
end

-- part: Lib.DiscreteSeries.FlenstedJensen.PsiSmooth
section
/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: The coefficient as a smooth function on the group; continuity. -/

open Set Matrix.Norms.L2Operator

attribute [-simp] finsum_eq_sum_of_fintype

variable {n : Type} [Fintype n] {ε} (l : @HCParam n ε)

/-- The restriction of ψ_λ to U(diag ε), as an element of the space of smooth complex-valued
functions on that group. -/
@[simps] noncomputable def HCParam.dsCoeffSmooth : SmoothU ε ℂ := ⟨(l.dsCoeff ·),
  (SmoothPartitionOfUnity.exists_isSubordinate _ isClosedEmbedding_U.2 _ (fun _ ↦ isOpen_analyticAt
  ℂ l.dsCoeff) (subset_iUnion_of_subset () (range_subset_iff.2 analyticAt_dsCoeff))).elim fun f h ↦
  ⟨⟨_,
  (f.contMDiff_finsum_smul fun i _ x ↦ (h i x).restrictScalars.contDiffAt.contMDiffAt).contDiff⟩,
  funext (by simp [↓← finsum_smul, f.sum_eq_one])⟩⟩

@[fun_prop] lemma continuous_dsCoeff {X} [TopologicalSpace X] {f : X → USign ε} :
    Continuous f → Continuous (l.dsCoeff <| f ·) := (SmoothU.continuous l.dsCoeffSmooth).comp
end

-- part: Lib.DiscreteSeries.FlenstedJensen.CasimirOnPsi
section
/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Flensted-Jensen's function is a Casimir eigenfunction with value |λ|²−|ρ|². -/


open Matrix Filter Norms.L2Operator ContinuousMap GlModule U HCParam
variable {n} [Fintype n] {ε h} {l : n → ℤ}

lemma exists_equiv_fin_lt_iff (hl : l.Injective) : ∃ e : Fin (Fintype.card n) ≃ n, ∀ a b,
  l (e a) < l (e b)
  ↔ a < b := ⟨_, fun _ _ ↦ lt_iff_lt_of_le_iff_le (@monoEquivOfFin n _ (.lift' l hl) _ rfl).2⟩

/-- For a parameter λ of gap h, the Casimir operator Ω = Σ E_ab E_ba, acting by right
derivatives, satisfies Ωψ_λ = (|λ|² − |ρ|²) ψ_λ.

Known result: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series. -/
lemma casimir_dsCoeffSmooth {l : @HCParam n ε} [hg : l.HasGap h] :
  (rightDeriv ε ℂ).casimirK 1 l.dsCoeffSmooth = (l.casimirValue : ℂ) • l.dsCoeffSmooth := by
  ext g; have ⟨_, hF, e⟩ := isAnalyticFamily_flenstedJensen g l analyticAt_const rfl
  obtain ⟨⟨_, d, e'⟩, _⟩ :=
    exists_contDiff_eventuallyEq hF.restrictScalars.contDiffAt, hg.neg.signs_one
  let f : SmoothU ε _ := ⟨_, ⟨_, d⟩, rfl⟩
  have ⟨L, ψ⟩ : ∃ L : StrongDual ℂ _, l.dsCoeffSmooth.1 =ᶠ[_] L ∘ f.1 :=
    ⟨l.lowestKType.kTypeNormSq⁻¹ • strongIntegral (haarK ε)
    (evalCLM ℂ), .mono (continuous_mat.tendsto _ (e.and (e'.and (tendsto_id.const_mul _
    (isAccretive_blockDiagPart_inv_mul g).2.setOf_mem_nhds)))) (by simp +contextual [f,
    strongIntegral_eval, dsCoeff_eq_flenstedJensen hg (blockDiagPart_mem g), flenstedJensen,
    field])⟩
  suffices ((rightDeriv ε C(_, ℂ)).casimirK 1 f).1 g = ((-l).compactForm.casimirKValue (paramAddRho
    l) : ℂ) • f.1 g by convert congr(L $this) <;> simp [casimir,
    (rightDeriv_comp_clm _ (rightDeriv_comp_clm _ ψ)).eq_of_nhds, ↓ψ.eq_of_nhds, casimirKValue,
    casimirValue, twoRho_neg, ← sub_eq_of_eq_add (two_mul_paramAddRho hg _)]; grind [twoRho]
  ext k; exact ((rightDeriv ε _).onRange ⟨⟨(Germ.ofFun <| evalCLM ℂ k ∘ ·.1), by simp⟩, by tauto⟩
    fun _ _ h ↦ (rightDeriv_comp_clm (f' := 0) _ (Quotient.exact h.symm)).germ_eq.symm.trans
    (by simp)).rec fun σ s ↦ congr($((by simp [↓casimirK_one_adTwist, casimir, s] :
    LinearMap.rangeRestrict _ (casimirK _ _ f) = _).trans (IsKHighest.casimirK_eq_smul (σ :=
    σ.adTwist k) (.of_E_eq_smul fun a b q o ↦
    (s _ f).trans (Subtype.ext (Quot.sound (.mono (continuous_mat.tendsto
    _ ((e.and e').eventually_nhds.and (hF.congr e'.symm).eventually_analyticAt)) fun y ⟨hy, _,
    D⟩ ↦ congr($(rightDeriv_eq_fderiv D.hasFDerivAt (by tauto) _) k).trans
    (fderiv_eq_of_borel_equivariant 1 ((evalCLM ℂ k).hasFDerivAt.comp _ D.hasFDerivAt) o q
    ((y * ·) ∘ (k * · * k⁻¹)) (hy.mono (by intros; simp_all [hy.self_of_nhds, ← mul_assoc, diagChar,
    field, hg.isKDominant_neg_paramAddRho.weightMinors_mul_borel hg.1]))))))))).1.value)
end

-- part: Lib.General.LinearAlgebra.BlockDiagonalDet
section
/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: |det| of the block diagonal part of g in U(p,q) is at least (‖g‖/2)². -/


open Matrix Norms.L2Operator MatrixOrder CStarAlgebra Finset Real Unitary Complex U CStarRing Sgn
variable {n} [Fintype.{0} n] {ε} (σ) (g : @USign n _ ε)

lemma norm_det_blockDiagPart : ‖(blockDiagPart ε g).det‖ = ‖principalMinor g (ε · =
  σ)‖ ^ 2 := by rw [twoBlockTriangular_det₀ _ (ε · =
  σ), (_ : _ * _ = principalMinor g (ε · = σ) * principalMinor g (ε · ≠ σ)),
  principalMinor_compl] <;> congr 2 <;> aesop (add simp [blockDiagPart, toSquareBlockProp, sq])

@[simp] lemma U.principalMinor_sign_ne_zero : principalMinor g (ε · = σ) ≠ 0 :=
  (by simpa [·] using norm_det_blockDiagPart σ g)

lemma sq_le_norm_det_blockDiagPart [Nonempty n] :
  (‖g.1.1‖ / 2) ^ 2 ≤ ‖(blockDiagPart ε g).det‖ := by
  have ⟨k, z, hz, _⟩ := exists_polar g
  have := (cosh_log <| hz.eigenvalues_pos ·)
  simp_all [-prod_mul_distrib, ← mem_maxCompactU, star, show blockDiagPart ε z =
    hz.1.cfc fun x ↦ 2⁻¹ * (x + x⁻¹) by
    rw [← hz.1.cfc_eq, cfc_const_mul .., cfc_add .., cfc_id' .., cfc_inv_id _]
    simp [blockDiagPart_eq, inv_mat, hz.1.eq, ← ext_iff], norm_mem_unitary_mul, mem_iff,
    ← maxCompactU.coe_inv, IsHermitian.cfc, -conjStarAlgAut_apply, -ofReal_mul]
  have ⟨⟨i, _⟩, j, _⟩ := hz.1.spectrum_real_eq_range_eigenvalues ▸ And.intro
    (norm_mem_spectrum_of_nonneg z.1.1) (spectrum.inv₀_mem (norm_inv z ▸
    norm_mem_spectrum_of_nonneg _ (CFC.inv_nonneg_of_nonneg _)))
  grw [← subset_univ {i, j}, (by simp : ∀ a, ‖a‖ ≤ ‖a‖ + ‖a‖⁻¹)] <;> grind [one_le_cosh, sq]
end

-- part: Lib.DiscreteSeries.FlenstedJensen.PsiDecay
section
/-! Part of: Flensted-Jensen's function: coefficient of the lowest K-type of a discrete series
(known result; see Lib.DiscreteSeries.FlenstedJensen.KTypeProjection).

This file: Decay of the coefficient like (2/‖g‖)^h, constant free of the parameter. -/


open Matrix MeasureTheory Finset Real ComplexOrder Norms.L2Operator PosDef U
variable {n} [Fintype n] {ε l h} (hg : @HasGap n _ ε l h) {c : ℕ} (hc : c ≤ h) (g : USign ε)

lemma weightMinors_pos {z} (hz :
  PosDef z) w : 0 < @weightMinors n _ w z := by apply finprod_induction <;>
  simp_all [principalMinor, toSquareBlockProp, toBlock, det_pos, hz.submatrix, apply_ite]

include hg hc

/-- For l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε): |ψ_λ(g)|²·|det a_g|^c ≤ 1, where
a_g is the block diagonal part of g. -/
lemma norm_dsCoeff_sq_mul_det_pow_le_one : ‖l.dsCoeff g‖ ^ 2 * ‖(blockDiagPart ε g).det‖ ^
  c ≤ 1 := by
  have d (g : USign ε) (p :
    g.1.1.PosDef) : ‖(blockDiagPart ε g).det‖ ^ c ≤ ‖weightMinors (-paramAddRho l) g‖ ^ 2 := by
    let v i := paramAddRho l i + ite True ↑c 0
    have q : (blockDiagPart ε g).PosDef :=
      p.1 ▸ by simp [blockDiagPart_eq, ← inv_mat, p, PosDef.add, PosDef.smul]
    suffices ‖weightMinors v (blockDiagPart ε g)‖ ≤ ‖_ * weightMinors (paramAddRho l) g *
      weightMinors v g⁻¹‖ by simpa [v, principalMinor_of_forall, ↓weightMinors_add_ite,
      weightMinors_neg, weightMinors_unitary_inv, q.isAccretive, field]
    obtain ⟨⟨⟩, ⟨B⟩⟩ := hg.mono hc, Finite.exists_le (|paramAddRho l| ⊔ |v|)
    norm_cast at *
    simp_all [abs_le, jacobi_complementary_minor, weightMinors_eq_det_zpow_mul_prod _ (-B) B,
      mul_assoc, ← prod_mul_distrib]
    gcongr
    grw [← fischer_inequality p.posSemidef (e := fun _ ↦ not_not), principalMinor_compl]; simp
    apply (fischer_inequality q.posSemidef ..).trans_eq
      congr(_ * ‖$(ext fun _ _ ↦ ite_eq_left _).det‖)
    repeat grind [paramAddRho]
  obtain ⟨I, k, z, ⟨p⟩⟩ := Integrable.of_integral_ne_zero (kTypeNormSq_pos l.lowestKType).ne',
    exists_polar g
  simp [*, by simpa using dsCoeff_polar hg k 1 p, ← maxCompactU.coe_inv]
  grw [norm_integral_le_of_norm_le (((I.comp_mul_left k).add I).div_const (2 * √(‖(blockDiagPart ε
    g).det‖ ^ c))) (.of_forall fun x ↦ ?_), integral_div, integral_add' integrable_of_compactSpace,
    ← integral_mul_left_eq_self _ k⁻¹, ← div_div] <;> simp [field, *, div_self_le_one]
  grw [← mul_rotate, two_mul_le_add_sq, sqrt_le_iff.2]; swap; simpa [← mem_maxCompactU] using
      d (x⁻¹ *
    z * x) (by simp [maxCompactU.coe_inv, p.conjTranspose_mul_mul_same, mulVec_injective_of_isUnit])
  repeat simp [← mem_maxCompactU]

/-- For a parameter l = 2λ of gap h, a natural number c ≤ h and g in U(diag ε): |ψ_λ(g)| ≤
(2/‖g‖)^c, with the operator norm. -/
lemma norm_dsCoeff_le_pow [Nonempty n] : ‖l.dsCoeff g‖ ≤ (2 / ‖g.1.1‖) ^ c := by grw [← sq_le_sq₀,
          pow_right_comm, ← inv_div, inv_pow, sq_le_norm_det_blockDiagPart] <;> simp [field,
  norm_dsCoeff_sq_mul_det_pow_le_one hg hc]
end

-- part: Lib.DiscreteSeries.CuspKernel.SchurOrthogonality
section
/-! Part of: Schur orthogonality; coefficients of integrable discrete series are cusp forms (known
result; see Lib.DiscreteSeries.CuspKernel.CircleMean).

This file: Module generated by the coefficient: decay, embedding in L², Schur orthogonality,
unitarity. -/

noncomputable section


open Matrix MeasureTheory ComplexConjugate Complex GlModule InnerProductSpace Real Norms.L2Operator
  Submodule Lp simpleFunc MemLp
variable {n} [Fintype n] {ε h A} {l : @HCParam n ε}

/-- The module D_λ = U(𝔤)ψ_λ: the smallest space of smooth functions on U(diag ε) that contains
ψ_λ and is stable under complexified right derivatives. -/
abbrev HCParam.DsModule := (rightDeriv ..).filtration 1 l.dsCoeffSmooth 0

/-- The action of gl_n(ℂ) by complexified right derivatives on smooth functions on U(diag ε),
restricted to the module D_λ generated by ψ_λ. -/
def HCParam.dsAction := (rightDeriv ..).generatedBy l.dsCoeffSmooth

/-- The function ψ_λ as an element of the module D_λ that it generates. -/
@[simps] def HCParam.dsGenerator : l.DsModule := ⟨_, self_mem_filtration⟩

attribute [local simp] integral_complex_ofReal inner_smul_right_eq_smul conj_mul' mul_assoc ne_of_gt
  le_of_lt div_pow

/-- For a parameter l = 2λ of gap h, ψ_λ is K-highest of weight Λ in the module D_λ = U(𝔤)ψ_λ. -/
lemma isKHighest_dsGenerator (hg : l.HasGap h) :
  l.IsKHighest l.dsAction l.lowestKType l.dsGenerator := .of_E_eq_smul fun a b q k ↦ by
  ext g; obtain ⟨d, e⟩ := (((-l).analyticAt_dsCoeff g⁻¹).comp_of_eq (analyticAt_matrix_inv
    g.1.det_ne_zero) (by simp)).differentiableAt.hasFDerivAt, by simpa using dsCoeff_inv hg.neg
  erw [rightDeriv_eq_fderiv d (by simpa), fderiv_eq_of_borel_equivariant ε d k q (g * ·) (.of_forall
    fun _ x m t _ ↦ by simp [*, t.2, by simpa using isAccretive_blockDiagPart_inv_mul g⁻¹, dsCoeff,
    flenstedJensen, ← mul_assoc, weightMinors_neg, hg.isKDominant_lowestKType.weightMinors_mul_borel
    hg.neg.1, ← integral_const_mul, mul_div]; ac_rfl)]
  aesop

/-- For a parameter l = 2λ of any gap h for the signs ε, |ψ_λ(g)| ≤ 1 for every g in U(diag ε). -/
lemma norm_dsCoeff_le_one (hg : l.HasGap h) (g : USign ε) : ‖l.dsCoeff g‖ ≤ 1 := by
  simpa using norm_dsCoeff_sq_mul_det_pow_le_one (c := 0) ⟨hg.1, hg.2, by simp⟩ le_rfl g

variable [Nonempty n] (hg : l.HasLargeGap A)
include hg

omit [Nonempty n] in
/-- Let l = 2λ have gap 500n³ + A, and w be integrable on U(diag ε) with ∫_K conj(m_Λ(k)) w(k⁻¹g)
dk = c_Λ w(g) for all g, c_Λ = ∫_K |m_Λ|². Then ∫ w(g)ψ_λ(xga) dg = ψ_λ(x) ∫ w(g)ψ_λ(ga) dg. -/
lemma integral_mul_dsCoeff_translate {w} (i : Integrable w) (hw : ∀ g, ∫ k, conj (weightMinors
  l.lowestKType k) * w (k.1⁻¹ * g) ∂haarK ε = l.lowestKType.kTypeNormSq * w g) x a : ∫ g,
  w g * l.dsCoeff (x * g * a :) = l.dsCoeff x * ∫ g, w g * l.dsCoeff (g * a :) :=
  by simpa [hw, mul_left_comm (w _), by simpa using fun g ↦
  integral_conj_weightMinors_mul_dsCoeff hg x (g * a) hg.isKDominant_lowestKType] using
  (_root_.integral_conv (k := (conj <| weightMinors l.lowestKType ·)) (ν :=
  haarK ε) (↑) integrable_of_compactSpace i
  (.of ⟨_, (norm_dsCoeff_le_one hg <| x * · * a)⟩)).symm.elim (·.symm.trans)

/-- For n ≥ 1 and l = 2λ of gap 500n³ + A, every element of D_λ = U(𝔤)ψ_λ has the form g ↦ ∫
β(y⁻¹) ψ_λ(gy) dy for some smooth compactly supported function β on U(diag ε). -/
lemma exists_smear_dsCoeffSmooth_eq (f : l.DsModule) : ∃ β, (smear l.dsCoeffSmooth.1) β = f := by
  let b : @ContDiffBump (Matrix n n ℂ) 0 := default; have ⟨P, e⟩ := l.dsCoeffSmooth.2
  let β : Bumps ε := ⟨⟨_, ⟨_, (ofRealCLM.contDiff.comp ((b.contDiff.comp (contDiff_id.mul
    (starL' ℝ).contDiff)).pow 2)).mul P.2⟩, congr(_ * $e)⟩, .intro (isCompact_U_norm_le √b.rOut) (by
    simp +contextual [b.zero_of_le_dist, CStarRing.norm_self_mul_star, sqrt_lt', sq])⟩
  refine mem_sInf.1 f.2 ((smear ..).range.submoduleOf _) ⟨(smul_mem_iff_of_isUnit _ ?_).1 ⟨β, funext
    (by simpa [mul_comm (dsCoeff ..)] using! integral_mul_dsCoeff_translate hg
          (integrable_bump_inv_smul 1 β) (by simp [β, star, mul_left_comm, ← maxCompactU.coe_inv, by
    simpa using integral_conj_weightMinors_mul_dsCoeff hg ·⁻¹ 1 hg.isKDominant_lowestKType]) · 1)⟩,
    fun _ _ _ _ ⟨_, e⟩ ↦ ⟨_, rightDeriv_smear _ _ e _⟩⟩
  simpa [β, ↓dsCoeff_inv, ← ofReal_pow, ← ofReal_mul] using
    (integral_pos_of_integrable_nonneg_nonzero
    (x := 1) (by clear_value β; fun_prop) (integrable_bump_inv_smul (l.dsCoeff ·) β).norm.abs
    (abs_nonneg _) (by simp [β, b, ContDiffBump.one_of_mem_closedBall, default])).ne'

namespace HCParam.HasLargeGap

/-- For n ≥ 1, l = 2λ of gap 500n³ + A, f in D_λ = U(𝔤)ψ_λ and a natural number c ≤ 500n³ + A,
there is K with |f(g)| ≤ K(2/‖g‖)^c for all g in U(diag ε). -/
lemma exists_decay_bound (f : l.DsModule) (c : ℕ) (hc : c ≤ gapThreshold n A) : ∃ K,
  ∀ g, ‖f.1.1 g‖ ≤ K * (2 / ‖g.1.1‖) ^ c := (exists_smear_dsCoeffSmooth_eq hg f).elim fun α e ↦
  e ▸ ⟨_, fun g ↦ .trans_eq (norm_integral_le_of_norm_le
  ((integrable_bump_inv_smul (E := ℂ) (‖·.1.1‖ ^ c) α).norm.mul_const _) (.of_forall (by
  grw [norm_smul, dsCoeffSmooth, norm_dsCoeff_le_pow hg hc]; simp [field]
  grw [mul_assoc, ← mul_pow, ← U.norm_inv ·, ← norm_mul_le]; simp))) (integral_mul_const ..)⟩

lemma integrable_norm_pow_smul (f : l.DsModule) (C := A) (h : (C : ℝ) ≤ A + 1 := by grind) :
  Integrable fun g ↦ f.1.1 g * ‖g.1.1‖ ^ C := (hg.exists_decay_bound f
  (C + (8 * Fintype.card n ^ 2).succ) (by simp; nlinarith [one_le_cast_card n])).elim fun K k ↦
  ((integral_decay_le _ .monoidHom_id .refl 1).1.const_mul
  (K * 2 ^ C)).mono' (by fun_prop) (.of_forall (by grw [norm_mul, k ·, pow_add]; simp [field]))

lemma memLp (f : l.DsModule) : MemLp f.1.1 2 := (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  (by simpa [sq] using (hg.integrable_norm_pow_smul f 0).norm.mul_bdd (by fun_prop) (.of_forall (by
  simpa using (hg.exists_decay_bound f 0 (by simp; bound)).choose_spec)))

/-- For n ≥ 1 and a parameter λ of gap 500n³ + A, the degree deg_λ, the reciprocal of ∫_G
|ψ_λ|², is positive. -/
@[simp] lemma _root_.formalDegree_pos : 0 < l.formalDegree :=
  inv_pos.2 (integral_pos_of_integrable_nonneg_nonzero
  (x := 1) (by fun_prop) (hg.memLp l.dsGenerator).norm.integrable_sq (by aesop_cat) (by simp))

/-- Let n ≥ 1 and let l = 2λ have gap 500n³ + A. For every natural number C ≤ A + 1, the
function g ↦ ‖g‖^C e_λ(g) is integrable on U(diag ε), ‖g‖ the operator norm. -/
lemma integrable_norm_pow_smul_dsKernel (C := A) (h : (C : ℝ) ≤ A + 1 := by grind) :
  Integrable fun g ↦ l.dsKernel g * ‖g.1.1‖ ^ C := by simpa [dsKernel] using
  (integrable_norm_pow_smul hg.neg dsGenerator C).const_mul _

/-- Product formula (Schur orthogonality): for n ≥ 1, a parameter λ of gap 500n³ + A and x, a in
G = U(diag ε), deg_λ ∫_G ψ_λ(xya) · conj(ψ_λ(y)) dy = ψ_λ(x) ψ_λ(a). -/
lemma _root_.dsCoeff_schur_orthogonality (x a : USign ε) : l.formalDegree * ∫ y,
  l.dsCoeff (x * y * a :) * conj (l.dsCoeff y) = l.dsCoeff x * l.dsCoeff a := by
  have k := integral_mul_dsCoeff_translate hg (hg.integrable_norm_pow_smul l.dsGenerator 0).comp_inv
    (by simpa using integral_conj_weightMinors_mul_dsCoeff hg ·⁻¹ 1 hg.isKDominant_lowestKType)
  rcases (integral_div_left_eq_self _ _ a⁻¹).trans (k a 1), formalDegree_pos hg
  simp_all [by simpa using dsCoeff_inv hg, mul_div, mul_comm _ (conj _), formalDegree, ← ofReal_pow,
    field]

/-- For n ≥ 1 and gap 500n³ + A, the linear map D_λ → L²(U(diag ε)) sending a function to √deg_λ
times its class. -/
def toL2 := √l.formalDegree • IsLinearMap.mk' (R := ℂ) (hg.memLp · |>.toLp) ⟨by tauto, by tauto⟩

/-- For n ≥ 1 and gap 500n³ + A, the action on D_λ differentiates right translation R on L²(G)
along ι: D_λ → L²(G); moreover ⟨ιψ_λ, R(g)ιy⟩ = y(g) and ⟨ιy, R(x)ιz⟩ = deg_λ ∫ z(gx)
conj(y(g)) dg.

Known result: Schur orthogonality; coefficients of integrable discrete series are cusp forms. -/
lemma toL2_spec : IsDerivedAction rightRegularL2 hg.toL2 l.dsAction ∧
  (∀ y g, ⟪hg.toL2 l.dsGenerator, rightRegularL2 g (hg.toL2 y)⟫_ℂ = y.1.1 g) ∧ ∀ y z x, ⟪hg.toL2 y,
  rightRegularL2 x (hg.toL2 z)⟫_ℂ = l.formalDegree * ∫ g, z.1.1 (g * x) * conj (y.1.1 g) := by
  have i w h z k (x : USign ε) : ⟪toLp w h, rightRegularL2 x (toLp z k)⟫_ℂ = _ :=
    integral_congr_ae (h.coeFn_toLp.comp₂ _ (AEEqFun.coeFn_mk ..))
  have c := isUnitaryRep_rightRegularL2.1 (hg.toL2 l.dsGenerator); choose β e using
    exists_smear_dsCoeffSmooth_eq hg
  have B {y β} (e : (smear l.dsCoeffSmooth.1) β = y.1) g : rightRegularL2 g (hg.toL2 y) =
    smear _ c β g := (simpleFunc.denseRange (by simp)).eq_of_inner_right ℂ fun w ↦
    toLp_toSimpleFunc w ▸ .trans (by simpa [toL2, i, -map_mul, ← e, mul_left_comm, mul_comm] using
    (_root_.integral_conv (· * g) (((SimpleFunc.memLp_iff_integrable two_ne_zero nofun).1
    (simpleFunc.memLp w)).inner_const 1) (integrable_bump_inv_smul 1 β) (.of ⟨_,
    norm_dsCoeff_le_one hg⟩)).1) (integral_inner (integrable_bump_inv_smul ..) _)
  suffices _ from ⟨fun Y v ↦ ?_, fun y g ↦ ?_, this⟩
  erw [B (e y), ← integral_inner (integrable_bump_inv_smul ..)]
  simp [*, ← e, -map_mul, by simpa using (dsCoeff_schur_orthogonality hg 1 <| g * ·)]
  simp [toL2, inner_smul_left_eq_smul, i, smul_smul, ← real_smul]
  simpa [B (e v), ↓← @B (l.dsAction Y v) _ (rightDeriv_smear _ _ (e v) _)] using
    hasDerivAt_smear _ (β v) c (hasDerivAt_expU Y 1 0)

variable [hg]

instance : NormedAddCommGroup l.DsModule :=
  .induced _ _ hg.toL2 fun _ ↦ by grind +extAll [hg.toL2_spec]

instance : InnerProductSpace ℂ l.DsModule := induced hg.toL2

variable (hg)

/-- For n ≥ 1 and gap 500n³ + A, the inner product on D_λ is invariant under 𝔲(diag ε), the
generator ψ_λ has norm 1, and |y(g)| ≤ ‖y‖ for all y in D_λ and g in U(diag ε). -/
lemma isUnitaryCasimirGe_dsAction : IsUnitaryCasimirGe l l.dsAction ∧ ‖l.dsGenerator‖ = 1 ∧
  ∀ (y : l.DsModule) g, ‖y.1.1 g‖ ≤ ‖y‖ := by
  have ⟨d, k, _⟩ := hg.toL2_spec
  have u := by simpa using congr(√‖$(k l.dsGenerator 1)‖)
  use ⟨d.form_E_eq_sign_mul isUnitaryRep_rightRegularL2, by simp [dsAction,
    casimirK_generatedBy casimir_dsCoeffSmooth, sq]⟩, u,
    (k · · ▸ by grw [norm_inner_le_norm, u]; simp [rightRegularL2]; rfl)
end HCParam.HasLargeGap
end
end
