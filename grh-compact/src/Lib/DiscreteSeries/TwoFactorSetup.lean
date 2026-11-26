import Lib.DiscreteSeries.KernelFixes
import Lib.DiscreteSeries.TailBounds

section
/-! General lemmas of linear algebra and matrices (textbook or folklore).

This file: Hilbert-Schmidt estimates, matrix logarithm and integrated Jacobi formula near the
identity. Lagrange's identity for the top coefficient, with weights at decreasing integer nodes.
Transport of the coefficient, its measure and product formula through a frame to U(J). -/

noncomputable section

open Matrix Finset Norms.Frobenius Complex intervalIntegral ComplexConjugate MatrixOrder WithLp
variable {n} [Fintype n] {ε h} {l : @HCParam n ε} {P X Y : Matrix n n ℂ} {ρ σ : ℝ}

/-- The complex diagonal matrix diag(w) of an integer vector w. -/
@[simp] abbrev intDiagonal (w : n → ℤ) := diagonal (w · : n → ℂ)

lemma frobenius_norm_sq_eq_sum : ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  simp (disch := positivity) [frobenius_norm_def, ↓← Real.sqrt_eq_rpow]

lemma norm_trace_mul_le (a : ‖X‖ ≤ ρ := by rfl) (b : ‖Y‖ ≤ σ := by rfl) : ‖(X * Y).trace‖ ≤ ρ * σ :=
  ((innerSL ℂ (toLp 2 (toLp 2 <| Xᴴ ·))).le_of_opNorm_le_of_le (x := toLp ..)
  (by simpa using norm_star X ▸ a) b).trans' (by simp [↓X.trace_mul_comm, inner, trace, mul_apply])

lemma trace_star_mul_self_eq_norm_sq : (Xᴴ * X).trace = ↑(‖X‖ ^ 2) :=
  sum_comm.trans (by simp [frobenius_norm_sq_eq_sum, conj_mul'])

lemma frobenius_norm_mul_of_unitary (h : Xᴴ * X = 1) Y : ‖X * Y‖ = ‖Y‖ := by
  rw [← sq_eq_sq₀, ← ofReal_inj] <;> simp [↓← trace_star_mul_self_eq_norm_sq]; grind

lemma norm_smul_le_of_le_one (ρ : ℝ) (a : ‖X‖ ≤ σ) (h : 0 ≤ ρ ∧ ρ ≤ 1 := by grind) : ‖ρ • X‖ ≤
  σ := by grw [norm_smul_of_nonneg, h.2, a] <;> bound

lemma inv_one_add_bounds (h : ‖X‖ ≤ σ) (hσ : σ ≤ 2⁻¹ := by nlinarith) : ((1 + X).det ≠ 0 ∧ (1 + X) *
    (1 + X)⁻¹ = 1 ∧ (1 + X)⁻¹ * (1 + X) = 1) ∧ ‖(1 + X)⁻¹ - 1‖ ≤ 2 * σ := by
  let ⟨V, e⟩ := (add_left_surjective 1).exists.1 (IsUnit.exists_left_inv
    ⟨.oneSub _ (by simp; grind), sub_neg_eq_add _ X⟩)
  simp_all [inv_eq_left_inv e, ↓mul_nonsing_inv, det_ne_zero_of_left_inverse e, mul_add, add_mul,
    add_assoc, add_eq_zero_iff_neg_eq]
  grind [norm_neg, norm_add_le, norm_mul_le_of_le (refl ‖V‖) (h.trans hσ)]

/-- The matrix ∫₀¹ (1+sX)⁻¹X ds, the logarithm of 1+X for small X. -/
def logOneAdd (X : Matrix n n ℂ) := ∫ s in 0..1, (1 + s • X)⁻¹ * X

lemma trace_mul_logOneAdd (h : ‖X‖ ≤ 2⁻¹) D : let f s := trace (D * ((1 + s • X)⁻¹ * X))
  IntervalIntegrable f MeasureTheory.volume 0 1 ∧ ∫ s in 0..1, f s = (D * logOneAdd X).trace := by
  use ?_, (traceLinearMap .. ∘ₗ .mulLeft ℂ D).toContinuousLinearMap.intervalIntegral_comp_comm
    ?_ <;> apply ContinuousOn.intervalIntegrable <;> simp [Matrix.inv_def] <;> fun_prop
    (disch := grind [inv_one_add_bounds (norm_smul_le_of_le_one _ h _)])

/-- If X has Hilbert–Schmidt norm at most ½, then det(1+X) = exp(tr lg X), where lg is
`logOneAdd`; an integrated form of Jacobi's formula. -/
lemma det_one_add_eq_exp_trace_logOneAdd (h : ‖X‖ ≤ 2⁻¹) :
  (1 + X).det = cexp (logOneAdd X).trace := by
  obtain ⟨⟨i, e⟩, u⟩ := trace_mul_logOneAdd h 1,
    (inv_one_add_bounds <| norm_smul_le_of_le_one · h ·)
  refine have := integral_eq_sub_of_hasDerivAt ?_ (i.sub i) (f := fun t ↦
      (1 + t • X).det / exp (∫ s in 0..t, ((1 + s • X)⁻¹ * X).trace)); by simp_all; grind
  simp_intro s hs
  convert! ((hasDerivAt_det (nonsing_inv_mul ..) ((((hasDerivAt_id s).smul_const X).const_add
    1).const_mul _)).const_mul (1 + s • X).det).div (integral_hasDerivAt_right (i.mono_set
    ?_) ⟨⊤, ?_⟩ ?_).cexp _
  any_goals simp [field, Set.Icc_subset_Icc, *]
  all_goals simp [Matrix.inv_def]; fun_prop (disch := simp [*])

lemma norm_logOneAdd_le (h : ‖X‖ ≤ 2⁻¹) : ‖logOneAdd X‖ ≤ 2 * ‖X‖ :=
  (norm_integral_le_of_norm_le_const fun _ _ ↦ by grw [norm_le_insert', ← sub_one_mul, norm_mul_le,
  (inv_one_add_bounds (norm_smul_le_of_le_one _ h)).2]).trans_eq (by ring)

lemma norm_proj_mul_le (h : IsStarProjection P) (a : ‖X‖ ≤ ρ) : ‖P * X‖ ≤ ρ := by
  simpa [sub_mul, two_mul P, ← two_smul ℝ, norm_smul] using
    norm_add_le_of_le (frobenius_norm_mul_of_unitary h.two_mul_sub_one_mem_unitary.1 X ▸ a :) a

variable (p) [@DecidablePred.{1} n p]

/-- The diagonal complex matrix with entry 1 at the indices satisfying the condition p and 0 at
the other indices. -/
def coordProj : Matrix n n ℂ := diagonal (if p · then 1 else 0)

lemma isStarProjection_coordProj :
  IsStarProjection (coordProj p) := by aesop (add simp [isStarProjection_iff', coordProj, star])

lemma norm_entryMask_le {r} [DecidableRel r] : ‖entryMask r
  X‖ ≤ ‖X‖ := by simp [frobenius_norm_def]; gcongr; bound

lemma isAccretive_of_norm_sub_one_lt (h : ‖X - 1‖ < 1) : X.IsAccretive :=
  ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _ (.add_star_self X)).2 fun x ↦ Not.imp_symm
    fun _ ↦ ⟨Units.mk0 (x - 2 : ℝ) (by grind) • .oneSub ((2 - x)⁻¹ • (1 - X - star (X - 1))) (by
    grw [norm_smul_of_nonneg, norm_sub_le, norm_sub_rev, norm_star, h] <;> bound), by
    simp [Algebra.algebraMap_eq_smul_one]; match_scalars <;> grind⟩).posDef

lemma flenstedJensen_shift_eq_conj (hg : l.HasGap h) {u} (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) →
  u i j = 0) (a : X.IsAccretive) (b : ((1 - u) * X).IsAccretive) :
  l.flenstedJensen 1 ((1 - u) * X)ᴴ = conj (l.flenstedJensen 1 X) := have := b.det_ne_zero
  have k : 1 - u ∈ _ := mem_blockDiagAlg.2 (by aesop)
  have := flenstedJensen_eq_of_accretive hg (one_mem _) (by simpa) k (by aesop)
  by simp_all [flenstedJensen, conj_weightMinors, mul_comm, mul_assoc,
    hg.isKDominant_lowestKType.weightMinors_oppBorel_mul hg.neg.1 _ k (by
    simp_all [IsBorelMatrix, BlockTriangular]; grind), diagChar, ← integral_conj]

open Polynomial Lagrange Real Calc MeasureTheory

/-- Lagrange weights: for integers x_0 > … > x_{M−1} there are reals c_k ≥ 1 with c_k² = (−1)^k
∏_{j≠k}(x_k−x_j) =
|∏_{j≠k}(x_k−x_j)| such that every real polynomial P of degree < M has X^{M−1}-coefficient
Σ_k (−1)^k P(x_k)/c_k². -/
lemma exists_lagrange_weights {M} {x : Fin M → ℤ} (hx : StrictAnti x) : ∃ c : _ → ℝ, (∀ k, 1 ≤ c k ∧
    c k ^ 2 = (-1) ^ k.1 * ∏ j ∈ univ.erase k, (x k - x j : ℝ)) ∧ ∀ P : ℝ[X], P.degree < M →
    P.coeff (M - 1) = ∑ k, (-1) ^ k.1 * (P.eval (x k : ℝ) / c k ^ 2) := ⟨_, (⟨·, by
  simpa [*, mul_div_mul_left, mul_div] using fun P ↦ coeff_eq_sum (s := univ)
    (Int.cast_injective.comp hx.injective).injOn⟩) fun k ↦ (⟨one_le_sqrt.2 ·, sq_sqrt (by grind)⟩)
    (mod_cast by erw [← compl_singleton, ← Ioi_disjUnion_Iio, prod_disjUnion, ← Fin.card_Iio,
    mul_left_comm, ← prod_neg]; simp [Order.one_le_iff_pos, prod_pos, hx.lt_iff_gt])⟩

variable {n : _} [Fintype n]

/-- A frame for the complex matrix J with signs ε: an invertible matrix p with pᴴJp = diag(ε). -/
class SignFrame (J ε : outParam _) where (p : GL n ℂ) (gram_eq : p.1ᴴ * J * p.1 = signMatrix ε)

variable {ε : _} {A J} {l : @HCParam n ε} [p : SignFrame J ε] [IsHermInvolution J]

/-- The isomorphism of topological groups U(J) → U(diag ε), g ↦ p⁻¹gp, for an invertible p with
p*Jp = diag(ε). -/
def frameEquiv : U J ≃ₜ* USign ε := .mk (U.conj _ p.2).symm

/-- The function g ↦ ψ_λ(p⁻¹gp) on U(J), for l = 2λ and a frame p with p*Jp = diag(ε). -/
def HCParam.psiInFrame (l : HCParam ε) (g : U J) := l.dsCoeff (frameEquiv g)

omit [IsHermInvolution J] in
@[fun_prop] lemma continuous_psiInFrame :
  Continuous l.psiInFrame := by fun_prop [HCParam.psiInFrame]

lemma measurePreserving_frameEquiv : MeasurePreserving (frameEquiv (p := p)) :=
  measurePreserving_haarU _ p.1 1 _ (by simp [p.2]) (by tauto)

lemma integral_comp_frameEquiv {E} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : USign ε → E) :
    ∫ g, f (frameEquiv g) = ∫ g, f g :=
  measurePreserving_frameEquiv.integral_comp frameEquiv.measurableEmbedding _

/-- Let l = 2λ have gap 500n³+A for ε, n ≥ 1, J a hermitian involution, p invertible with p*Jp =
diag(ε). Then g ↦ deg_λ·ψ_λ(p⁻¹gp) is a kernel (`IsIdempotentKernel`) on U(J) for the compact dual
measure. -/
lemma isIdempotentKernel_psiInFrame [Nonempty n]
    (hg : l.HasLargeGap A) : IsIdempotentKernel (l.formalDegree *
  l.psiInFrame ·) := have h := HCParam.HasLargeGap.isIdempotentKernel_dsKernel hg.neg
  by simpa [dsKernel, formalDegree] using! show IsIdempotentKernel ((-l).dsKernel <| frameEquiv
    ·) by use by fun_prop, measurePreserving_frameEquiv.integrable_comp_of_integrable h.2 <;>
    simp [h.4, ← h.3, ← h.5, ← integral_comp_frameEquiv]
end
end

section
/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Second-order expansion of log principal minors near 1 with absolute error constants. -/

open Ring Matrix Norms.Frobenius Complex intervalIntegral


variable {n} [Fintype n] {P Q X Y : Matrix n n ℂ} {ε h} {l : @HCParam n ε} {δ c : ℝ}
attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem principalMinor_eq_det coordProj

/-- For orthogonal projections P, Q and Hilbert–Schmidt norms, let ‖X‖ ≤ δ ≤ ½, tr([P,Q]Y) = 0,
‖[P,X]−Y‖ ≤ δc, ‖Y‖, ‖Q−P‖ ≤ c. Then det(1+PX) = exp(tr(Q·lg X) − ¼tr Y² + r) with |r| ≤
100δc², where lg is `logOneAdd`. -/
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hδ :
  δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h0 : (⁅P, Q⁆ * Y).trace = 0) (h1 : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤
  c) (hD : ‖Q - P‖ ≤ c) : ∃ r, (1 + P * X).det = cexp
  ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧ ‖r‖ ≤ 100 * δ * c ^ 2 := by
  obtain ⟨p, ⟨δ0, _⟩ : 0 ≤ δ ∧ 0 ≤ c⟩ := norm_proj_mul_le hP hX, by grind [norm_nonneg]
  obtain ⟨a, ⟨i, d⟩, j, k⟩ := (norm_le_insert' _ Y).trans (by grw [hY, h1, hδ]),
    trace_mul_logOneAdd (p.trans hδ) 1, trace_mul_logOneAdd (hX.trans hδ) Q
  refine ⟨_, ?_, congr(‖$(integral_add (i.sub j) (.mul_const (continuous_ofReal.intervalIntegrable
    ..) (2⁻¹ * (Y * Y).trace)))‖).ge.trans
    ((norm_integral_le_of_norm_le_const fun s h ↦ ?_).trans (by aesop))⟩
  simp_all [det_one_add_eq_exp_trace_logOneAdd (p.trans hδ), integral_ofReal]; ring
  obtain ⟨⟨⟨_, f, F⟩, w⟩, ⟨_, e, E⟩, v⟩ := inv_one_add_bounds (norm_smul_le_of_le_one s hX),
    inv_one_add_bounds (norm_smul_le_of_le_one s p)
  set W := (1 + s • X)⁻¹; set V := (1 + s • (P * X))⁻¹; set A := ⁅P, X⁆; set D := Q - P
  let Z := W - 1; let N := Z * (A * Z + A) + A * Z
  rw [show _ + _ = trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) - trace (s • (P *
    A) * ((N + A) * (V - 1) + N)) - trace ((D - P * D - P * D) * D * (X + Z * X)) - trace ((s / 2) •
    (A - Y) * (A + Y)) by
      linear_combination (norm := (
      simp +zetaDelta [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul]; ring))
        h0 + congr(($E * P * W * X * P + V * P * (A * ($F * P * (1 - W) + W * P *
      $f) - $f * X * P) + (1 - P) * $e * P * X - ⁅P, D⁆ * ($F * P * W - W * P * $f) * X).trace)]
  apply le_trans; apply_rules (transparency :=
    .reducible) (maxDepth := 99) [@norm_smul_le_of_le_one, norm_proj_mul_le hP, norm_proj_mul_le hQ,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le] <;> grind
  nlinarith [mul_nonneg δ0 (sq_nonneg c), sq_nonneg (δ * c)]

/-- Let λ have gap h, X = g−1, ‖X‖ < 10⁻³ (Frobenius). Some y has ψ_λ(g) =
`HCParam.flenstedJensen`(1,y) and, for k∈K and projectors P to sets p of lowest entries of λ,
Δ_p(k*yk) = exp(tr(P log g)+‖[P,X]‖²/4+r), |r| ≤ 2·10⁵‖X‖(‖[P,X]‖²+‖[P,k]‖²). -/
lemma exists_principalMinor_eq_exp (hg : l.HasGap h) (g : USign ε) : let X :=
    g.1.1 - 1; ‖X‖ < 1000⁻¹ → ∃ y, l.dsCoeff g = l.flenstedJensen 1 y ∧ ∀ p [DecidablePred p],
    (∀ i j, p i → ¬p j → l i < l j) → ∀ k : maxCompactU ε, let k := k.1.1.1; ∃ r, principalMinor
      (kᴴ * y * k) p = cexp ((coordProj p * logOneAdd X).trace + ‖⁅coordProj p, X⁆‖ ^ 2 / 4 + r)
    ∧ ‖r‖ ≤ 200000 * ‖X‖ * (‖⁅coordProj p, X⁆‖ ^ 2 + ‖⁅coordProj p, k⁆‖ ^ 2) := by
  intro X _; let r l := lowerMask ε l X; let u := r (-l)
  obtain ⟨⟨i, j⟩ : ‖X‖ ≤ 2⁻¹ ∧ 4 * ‖X‖ ≤ 2⁻¹, δ0, hX⟩ := by grind, norm_nonneg X, le_refl ‖X‖
  let y c := (1 - u) * g * (1 - r c); let m := X - u - u * X; have T c : ‖y c - 1‖ ≤ 4 * ‖X‖
  rw [(by grind : _ - 1 = m - r c - m * r c)]; swap
  use y l, ?_, ?_
  · have A c := isAccretive_of_norm_sub_one_lt ((T c).trans_lt (by bound))
    obtain ⟨a, b⟩ :=
      isAccretive_of_norm_sub_one_lt (by bound), by simpa [y, show r 0 = 0 from rfl] using A 0
    have := (flenstedJensen_shift_eq_conj hg (u := (r l)ᴴ) (by simp [r]; grind) (by
      simpa [IsAccretive, add_comm] using b) (by simpa [y, IsAccretive, add_comm] using A l)).trans
      (congrArg _ (flenstedJensen_shift_eq_conj hg (by simp_all [u, r]) a b))
    simp_all [dsCoeff_eq_flenstedJensen hg (one_mem _), y]
  have I p [DecidablePred p] (hp : ∀ i j, p i → ¬p j → l j < l i) : principalMinor (y l) p =
    principalMinor g p := by
    clear * - hp hg; rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.1, mul_comm, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hg.neg.1] <;> simp [u, r, BlockTriangular] <;> grind
  intro p _ hp κ k; let s := signMatrix ε
  obtain ⟨w : kᴴ * k = 1, o : k ∈ _, hP, d : Commute s (coordProj p)⟩ := (U_one_mem_unitaryGroup ⟨_,
    κ.2⟩).1, mem_maxCompactU.1 κ.2, isStarProjection_coordProj p, commute_diagonal ..
  set P := coordProj p; set A := ⁅P, X⁆; set B := ⁅P, u⁆; set C := ⁅P, r l⁆; set G := B * X + u * A
  let Q := k * P * kᴴ; let V := (1 + X)⁻¹ - 1; let H := G + m * C - (G + B - A) * r l
  have ⟨N, E⟩ : (∀ c, ⁅P, r c⁆ = lowerMask ε c A) ∧ B = blockDiagPart ε A - C := by
    simp +zetaDelta [← ext_iff, blockDiagPart]; grind
  have M x : (1 + (1 - P) * (x - 1)).det =
    principalMinor x (¬p ·) := by simp [P, det_apply, sub_mul]; grind
  obtain ⟨R, a, b, W, _ : Pᴴ = P, _, _, _ : gᴴ = s * g.1.1⁻¹ * s⟩ := hP.one_sub, norm_nonneg A,
    norm_nonneg ⁅P, k⁆, mul_eq_one_symm w, hP.2, (inv_one_add_bounds hX i).2,
    (N · ▸ norm_entryMask_le), by grind [U.inv_mat, signMatrix_mul_self]
  have := ((by simp [Q, mul_sub, ← mul_assoc, *] : k * ⁅P, k⁆ᴴ =
    P - Q) ▸ frobenius_norm_mul_of_unitary w _).trans_le (norm_star _).le
  have ⟨x, e, _⟩ := exists_det_compress_eq_exp_logOneAdd R R i hX ?_ (by simp [A, mul_sub, sub_mul,
    mul_nonneg]) (norm_neg A).le (by simp)
  have ⟨z, f, _⟩ := exists_det_compress_eq_exp_logOneAdd (Y :=
    B + C - A) (c := 4 * ‖A‖) R R j (T l) ?_ ?_ ?_ (by simp)
  have ⟨t, q, _⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := A - B - C) (c := 4 * (‖A‖ +
    ‖⁅P, k⁆‖)) (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, w, W⟩)) hP j (T l) ?_ ?_ ?_ (by linarith)
  rw [M, I _ (by tauto), ← M, e] at f
  use t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace, .trans (by
    simp [det_one_add_mul_comm k, Q, P]; noncomm_ring [w]) (q.trans (mul_right_cancel₀ (by simp)
    (congr(_ * ($f * $((det_one_add_eq_exp_trace_logOneAdd ((T l).trans j)).symm.trans
    (.trans (by simpa [principalMinor_of_forall, X] using I ⊤)
    (det_one_add_eq_exp_trace_logOneAdd i))))).trans ?_))), ?_
  on_goal 7 => rw [(by simp +zetaDelta; noncomm_ring : _ - _ = H)]
  on_goal 4 => rw [(by simp +zetaDelta; noncomm_ring :
    _ - _ = (y l - 1) * (P - Q) - (P - Q) * (y l - 1) - H)]
  any_goals (apply le_trans; apply_rules (transparency := .reducible) [norm_entryMask_le.trans,
    @norm_smul_le_of_le_one,
    @norm_trace_mul_le, norm_sub_le_of_le, norm_add_le_of_le, norm_mul_le_of_le, le_rfl]; on_goal
    -1 => first | nlinarith only [δ0, j, b, mul_nonneg δ0 a, mul_nonneg δ0 (sq_nonneg ‖A‖),
                mul_nonneg δ0 (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖))] | nlinarith)
  all_goals simp [Q, V, s, *, blockDiagPart_eq, d.eq, trace_mul_comm P,
    (mem_blockDiagAlg_iff_commute.1 o).left_comm, ← ofReal_pow,
    A, X, inv_eq_left_inv w ▸ blockDiagAlg.inv_mem o _ rfl, trace_mul_comm k, trace_mul_comm kᴴ,
    trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add, mul_sub, sub_mul,
    ← trace_star_mul_self_eq_norm_sq, inv_le_one₀] <;> ring_nf
end

section
/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Near 1 the coefficient is explicit phase times real factor, uniform error. -/

open Matrix MeasureTheory Finset Fintype Ring Complex ComplexOrder Norms.L2Operator Norms.Frobenius


variable {n} [Fintype n] {ε} {l : @HCParam n ε} {δ T : ℝ} {L A : ℕ} (w : n → ℤ)
  (X : Matrix n n ℂ)

/-- For an integer vector w and a complex matrix X, the real number ∑_{i,j} |w_i − w_j|·|X_ij|². -/
noncomputable abbrev gapWeightedNormSq := ∑ i, ∑ j, |w i - w j| * ‖X i j‖ ^ 2

lemma sum_norm_lie_coordProj_sq : letI a := ∑ j, |w j|; ∑ t ∈ Ioc (-a) a, ‖⁅coordProj (t ≤ w ·),
    X⁆‖ ^ 2 = gapWeightedNormSq w X ∧
    ∑ t ∈ Ioc (-a) a, (coordProj (t ≤ w ·) * X).trace = ∑ i, (w i + a) * X i i := by
  have := neg_sum_abs_le_and_le_sum_abs w; simp [frobenius_norm_sq_eq_sum, coordProj, lie_def,
    trace, (Ioc ..).sum_comm, ite_sub, sub_ite,
    apply_ite norm, ← Order.lt_add_one_iff]; simp [sum_ite, ← add_mul,
    ← Ico_add_one_add_one_eq_Ioc, -Order.lt_add_one_iff, -Order.add_one_le_iff]
  constructor <;> congr! <;> norm_cast <;> grind

lemma norm_weightMinors_sq_le_exp (k : maxCompactU ε) : ‖weightMinors w k‖ ^ 2 ≤
  (-(gapWeightedNormSq w k / 2)).exp := by
  simp [weightMinors_eq_det_zpow_mul_prod _ _ _ (neg_sum_abs_le_and_le_sum_abs w),
    ← sum_norm_lie_coordProj_sq, sum_div, ← sum_neg_distrib, Real.exp_sum,
    ← prod_pow]; gcongr with t; have ⟨a, b⟩ := isStarProjection_coordProj (t ≤ w ·)
  nth_rw 1 [principalMinor_eq_det, ← coordProj, ← a, mul_assoc, det_one_sub_mul_comm, sq,
    ← norm_star, ← norm_mul,
    ← det_conjTranspose, ← det_mul, (isHermitian_conjTranspose_mul_self _).det_eq_prod_eigenvalues]
  grw [norm_prod, (Real.add_one_le_exp _).trans_eq' (sub_add_cancel ‖_‖ 1)]
  simp [← Real.exp_sum, abs_of_nonneg (eigenvalues_conjTranspose_mul_self_nonneg ..),
    ← real_le_real, ↓← trace_star_mul_self_eq_norm_sq, -conjTranspose_sub]
  erw [← (isHermitian_conjTranspose_mul_self _).trace_eq_sum_eigenvalues]
  simp [lie_def, b.isHermitian.eq, mul_sub, sub_mul, mul_assoc, ← maxCompactU.coe_inv, a.eq,
    (coordProj _).trace_mul_comm, trace_mul_comm _⁻¹ (_ * _)]
  grind

/-- Gaussian shape: let l = 2λ have gap 500n³, |l_a| ≤ L, T ≥ max(1, n², n² log(n+L+1)), 10¹²δT ≤ 1,
‖g−1‖ ≤ δ (Frobenius). Then |ψ_λ(g)/exp tr(diag(Λ) log g) − κ| ≤ κ/10 + e^{−100T} for some κ∈[0,1],
log g = `logOneAdd`(g−1), Λ = `HCParam.lowestKType`.

Discrete series coefficients near 1 and explicitly large Bessel functions. -/
lemma dsCoeff_gaussian_shape [Nonempty n]
    (hg : l.HasLargeGap A) (hL : ∀ a, |l a| ≤ L) {g : USign ε} (hZ : ‖g.1.1
  - 1‖ ≤ δ) (hT : 1 ≤ T) (a : card n ^ 2 ≤ T := by nlinarith) (b : card n ^ 2 * Real.log (card n +
  L + 1) ≤ T := by bound) (hδ : δ * T ≤ 1e-12 := by bound) : ∃ κ ∈ Set.Icc (0 : ℝ) 1, ‖l.dsCoeff g /
  (intDiagonal l.lowestKType * logOneAdd (g.1.1 - 1)).trace.exp - κ‖ ≤ κ / 10 + (-100 * T).exp := by
  obtain ⟨this, ⟨y, y1, y2⟩, H0, t, h⟩ := (norm_nonneg _).trans hZ,
    exists_principalMinor_eq_exp hg g (by nlinarith), kTypeNormSq_pos l.lowestKType,
    (norm_exp_sub_sum_le_exp_norm_sub_sum · 1), measure_ball_le_integral_dsCoeff hL
    (haarK ε) (maxCompactU ε).subtype integrable_of_compactSpace 1 le_rfl
  simp [↓← ENNReal.ofReal_mul', le_of_lt, dsCoeff_of_mem_maxCompactU, unitary, star,
    @CStarRing.norm_of_mem_unitary _ instL2OpNormedRing, ← maxCompactU.coe_inv] at h t
  simp (disch := positivity) [← Real.log_nonneg_iff, Real.log_mul] at h
  repeat grw [Real.log_le_self Nat.ofNat_pos.le] at h
  let q := gapWeightedNormSq (-paramAddRho l) (g - 1) / 4
  use q.exp⁻¹, ⟨by bound, by simp [field]; positivity⟩
  set E := @trace ..
  have d k := by simpa [principalMinor_of_forall, coordProj, lie_def, -det_mul] using (y2 ⊤ · k)
  choose r e hr using fun k : maxCompactU ε ↦ show ∃ r, weightMinors _ _ =
    (q - E - r).exp ∧ ‖r‖ ≤ 1e6 * δ * (q + gapWeightedNormSq l.lowestKType k / 2 + card n ^ 2) by
    choose x f i using fun t ↦
      y2 (t ≤ (-paramAddRho l) ·) (by simp [← hg.paramAddRho_lt_iff]; lia) k
    refine ⟨_, by rw [weightMinors_eq_det_zpow_mul_prod (d k ▸ exp_ne_zero _) _ _
      (neg_sum_abs_le_and_le_sum_abs _), d, funext f,
      ← exp_int_mul, ← exp_sum, ← exp_add, sub_sub_self], ?_⟩
    simp_rw [sum_add_distrib, ← sub_sub, sum_norm_lie_coordProj_sq, ← sum_div, add_mul]
    conv_lhs => enter [1, 1]; simp [lowestKType, E, q, trace, sub_mul, mul_sum,
      ← sum_norm_lie_coordProj_sq]; ring
    grw [norm_sub_le, norm_sum_le, norm_sum_le, i, ← mul_sum, norm_mul_le_of_le (r₁ := card n)
      (mod_cast abs_twoRho_le ..)
      ((norm_logOneAdd_le (hZ.trans (by nlinarith))).trans' (by grw [← sq_le_sq₀,
      frobenius_norm_sq_eq_sum, ← single_le_sum, ← single_le_sum] <;> simp [sum_nonneg'])), hZ,
      sum_add_distrib, (sum_norm_lie_coordProj_sq ..).1, (sum_norm_lie_coordProj_sq ..).1.trans_le
      (c := gapWeightedNormSq l.lowestKType k + 2 * card n * re (k.1.1.1ᴴ *
      k).trace) (by simp [gapWeightedNormSq, trace_star_mul_self_eq_norm_sq,
                      frobenius_norm_sq_eq_sum, mul_sum, ← sum_add_distrib, ← add_mul, -ofReal_pow]
                    gcongr; norm_cast; grind [lowestKType, twoRho])]
    simp [q, ← sub_nonneg, ← maxCompactU.coe_inv]; ring; positivity
  grw [y1, flenstedJensen, div_right_comm, div_sub' (by positivity), norm_div,
    Complex.norm_of_nonneg H0.le,
    div_le_iff₀ H0, ← integral_div, ← integral_complex_ofReal, ← integral_mul_const, ← integral_sub
    (integrable_of_compactSpace (by fun_prop (disch := simp [*]))) integrable_of_compactSpace,
    add_mul, ← integral_const_mul, ← average_const (haarK ε) (_ * _), average_eq_integral,
    ← integral_add integrable_of_compactSpace integrable_of_compactSpace]
  refine norm_integral_le_of_norm_le integrable_of_compactSpace (.of_forall fun k ↦ ?_)
  simp [e, mul_conj', exp_sub]; field_simp
  simp
  by_cases ‖r k‖ < 20⁻¹
  · grw [norm_exp_sub_one_le, ← H0] <;> nlinarith
  grw [← sq_nonneg, zero_add, t, sub_one_lt, norm_weightMinors_sq_le_exp, ← Real.exp_log H0]
  field
  simp [← Real.exp_add]
  nlinarith [hr k, le_mul_of_one_le_right this hT]
end

section
/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Steep parameters, phase cancellation; integrand is large only near diagonal U(X). -/

noncomputable section

open Finset Matrix Norms.Frobenius Complex ComplexConjugate Set ComplexOrder Int HCParam Sgn


variable {n m X S : Type} [Fintype n] [Fintype m] [Fintype X] [Group S] {ε} (l : @HCParam n ε) {η}
  (k : @HCParam m η) (j : S →* USign ε × USign η) (τ : X → m) (B : ℝ) {M} (e : X ⊕ Fin M ≃ n) (φ :
  S → ℂ) {u : Matrix X X ℂ}

/-- For a pair of matrices x = (x₁, x₂), the number tr(Λx₁) − tr(Λ'x₂), with Λ, Λ' the diagonal
matrices of the weights `HCParam.lowestKType` of l and k. -/
def HCParam.phase (x : Matrix n n ℂ × Matrix m m ℂ) :=
  (intDiagonal l.lowestKType * x.1).trace - (intDiagonal k.lowestKType * x.2).trace

/-- With indices numbered by X and 0 ≤ i < M: sign + and Λ = 0 on X; on the rest, signs (−1)^i
and Λ strictly decreasing within [−3B, −B]. -/
structure IsSteep where
  sign_inl x : ε (e (.inl x)) = 1
  sign_inr i : ε (e (.inr i)) = (-1) ^ i.1
  weight_eq_zero x : l.lowestKType (e (.inl x)) = 0
  weight_strictAnti : StrictAnti fun i ↦ l.lowestKType (e (.inr i))
  weight_mem i : (l.lowestKType (e (.inr i)) : ℝ) ∈ Icc (-3 * B) (-B)

/-- For a homomorphism j : S → U(diag ε) × U(diag η) and s in S, the pair of matrices (g − 1, g'
− 1), where j(s) = (g, g'). -/
abbrev subOnePair s := ((j s).1.1.1 - 1, (j s).2.1.1 - 1)

/-- For parameters l = 2λ, k = 2λ', j(s) = (g, g') and any function φ on S, the function θ(s) =
ψ_λ(g) conj(ψ_λ'(g')) e^{−φ(s)}. -/
def HCParam.laplaceIntegrand s := l.dsCoeff (j s).1 * conj (k.dsCoeff (j s).2) * cexp (-φ s)

/-- Hypotheses for Laplace's method on S, j(s) = (g, g'): `IsSteep`; φ = tr Λ(g−1) − tr
Λ'(g'−1), additive, imaginary; tr(g−1) = tr(g'−1); j(S) contains U(X) diagonally; sign and
size conditions on Λ'. -/
structure IsTwoFactor extends IsSteep l B e where
  phase_eq s : l.phase k (subOnePair j s) = φ s
  trace_eq s : (subOnePair j s).1.trace = (subOnePair j s).2.trace
  phase_mul s t : φ (s * t) = φ s + φ t
  re_phase s : (φ s).re = 0
  sign_weight_right x : η (τ x) = 1 ∧ k.lowestKType (τ x) = 0
  weight_bounds_right i i' : 0 ≤ k.lowestKType i ∧ (η i ≠ η i' → k.lowestKType i ≤ 3 * B)
  exists_diagonal : ∀ u ∈ unitaryGroup X ℂ, ∃ s, subOnePair j s = (inclMatrix ℂ (e ∘ .inl) *
    (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ, inclMatrix ℂ τ * (u - 1) * (inclMatrix ℂ τ)ᴴ)

attribute [local simp] diagonal_apply phase Matrix.mul_apply

lemma exists_unitary_sub_one_eq_inclMatrix {Y} [Fintype Y] (e : X ⊕ Y ≃ n) (h : ∀ x,
  ε (e (.inl x)) = 1) (k : uᴴ * u = 1) : ∃ s : USign ε, s.1.1 - 1 =
  inclMatrix ℂ (e ∘ .inl) * (u - 1) * (inclMatrix ℂ (e ∘ .inl))ᴴ := ⟨U.of IsHermInvolution.isUnit _
  (by simp_all [← ext_iff, inclMatrix, signMatrix, reindex_equiv e]), add_sub_cancel_left ..⟩

lemma norm_sq_add_re_trace_le (g : USign ε) (a C : ℝ) (v w : n → ℤ) (h : ∀ i j, a * v i ^ 2 ≤ w i ∧
    (ε i ≠ ε j → w i ≤ C)) : a * ‖intDiagonal v * (g.1.1 - 1)‖ ^ 2 + 2 *
  (intDiagonal w * (g.1.1 - 1)).trace.re ≤ 2 * C * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 := by
  rw [(?_ : 2 * _ = (intDiagonal w * ((g - 1) * (1 - g.1⁻¹))).trace.re)]
  simp [frobenius_norm_sq_eq_sum, trace, mul_sum, ← sum_add_distrib, blockDiagPart, eq_comm]
  gcongr with i _ j; cases h i j
  split_ifs <;> simp_all [mul_right_comm, ← cast_mul, mul_pow,
    Complex.sq_norm, normSq, signMatrix, U.inv_mat] <;> nlinarith
  simp [↓mul_sub, ↓sub_mul, ↓Units.mul_inv, trace, signMatrix, U.inv_mat, mul_right_comm,
    ← cast_mul]; ring

variable {l k j τ B e φ}

lemma IsTwoFactor.phase_logOneAdd (H :
  IsTwoFactor l k j τ B e φ) s (a : ‖(subOnePair j s).1‖ ≤ 2⁻¹) (b : ‖(subOnePair j s).2‖ ≤ 2⁻¹) :
  l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s := by
  have p i t : l.phase k (subOnePair j s ^ i * subOnePair j s * (1 + subOnePair j t)) = 0 ^ i * φ
    s := by induction' i with i h generalizing t <;> [have := H.phase_mul s t; have := h (s *
    t)] <;> simp_all [← H.phase_eq, pow_succ, sub_mul, mul_sub] <;> grind
  have := intervalIntegral.integral_congr_Ioo_of_le (μ := by volume_tac) zero_le_one fun r o ↦
    have G {n} [Fintype n] {X D : Matrix n n ℂ} (h : ‖X‖ ≤ 2⁻¹) :=
      ((hasSum_geom_series_inverse (-r • X) (by simp; grind [norm_smul_le_of_le_one r h])).mul_right
      X).mapL (traceLinearMap .. ∘ₗ .mulLeft ℂ D).toContinuousLinearMap
    ((G a).sub (G b)).unique (hasSum_single 0 fun i _ ↦ by
      simpa [↓smul_pow, *] using Or.inl (p i 1))
  simp_all [← H.phase_eq, trace_mul_logOneAdd, ← nonsing_inv_eq_ringInverse]

open MatMul

lemma dsCoeff_mul_eq_of_zero_weight_block {σ} (z : ∀ x : X, ε (σ x) = 1 ∧ l.lowestKType (σ x) = 0)
  {k g t : USign ε} (hk : k.1.1 - 1 = inclMatrix ℂ σ * (u * (inclMatrix ℂ σ)ᴴ)) (e : t = k * g) :
  intDiagonal l.lowestKType * (k.1.1 - 1) = 0 ∧ l.dsCoeff t =
  l.dsCoeff g ∧ ‖t.1.1 - 1‖ ^ 2 + 2 * (t.1.1 - 1).trace.re ≤ 2 * ‖g.1.1 - blockDiagPart ε g‖ ^ 2 :=
  have F i j : i ∉ range σ ∨ j ∉ range σ → k.1 i j = ite (i = j) 1 0 := by
    simp_all [or_imp, sub_eq_iff_eq_add, inclMatrix, eq_comm]
  have M x : weightMinors l.lowestKType (k * x) = weightMinors l.lowestKType x :=
    finprod_congr fun t ↦ by rw [principalMinor_mul (by grind), principalMinor_eq_det,
    (?_ : 1 - _ = ite (t ≤ 0) k.1.1 1)] <;> split <;> simp [field, ← ext_iff] <;> grind
  have c : ↑k ∈ blockDiagAlg ε := by grind [mem_blockDiagAlg]
  ⟨ext (by simp; grind), by
    simpa [*, ← frobenius_norm_mul_of_unitary (U_one_mem_unitaryGroup ⟨_, mem_maxCompactU.2 c⟩).1
      (g - _), dsCoeff, flenstedJensen] using norm_sq_add_re_trace_le t 1 1 1 1⟩

lemma norm_dsCoeff_pow_four_le {h} [hg : l.HasLargeGap h] (g : USign ε) : ‖l.dsCoeff g‖ ^ 4 ≤
  (1 + ‖g.1.1 - blockDiagPart ε g‖ ^ 2)⁻¹ ^ h := by
  have b (X : Matrix n n ℂ) (H := X.posSemidef_conjTranspose_mul_self) (e := H.eigenvalues_nonneg) :
      1 + ‖X‖ ^ 2 ≤ ‖(Xᴴ * X).charpoly.eval (-1)‖ := by
    rw [← ofReal_re (_ ^ 2), ← trace_star_mul_self_eq_norm_sq]; simpa [H.1.charpoly_eq,
      Polynomial.eval_prod, ← neg_add',
      -neg_add_rev, *, H.1.trace_eq_sum_eigenvalues, add_nonneg, ← re_eq_norm.2] using
      univ.induction_on (by simp) (by simp_intro a s ..; nlinarith [e a, s.sum_nonneg' e])
  grw [b, eval_charpoly, (?_ : _ - _ = -((blockDiagPart ε g)ᴴ * blockDiagPart ε g)), pow_mul _ 2 2,
    det_neg, (le_div_iff₀ _).2 (norm_dsCoeff_sq_mul_det_pow_le_one hg (by bound) g)] <;> simp [sq,
    mul_pow, ↓map_neg]
  linear_combination (norm := (simp [blockDiagPart_eq, IsHermInvolution.mul_self,
    IsHermInvolution.isHermitian.eq]; module)) congr(blockDiagPart ε ($(g.2) * signMatrix ε))

/-- Assume `IsTwoFactor`, B ≥ 1, 0 < r ≤ 1/100. If j(s) = (g, g') has ‖g−a_g‖²+‖g'−a_{g'}‖² ≤ r²
(Frobenius, a the block diagonal part), some t has θ(t) = θ(s), θ = `HCParam.laplaceIntegrand`, with
both components of j(t)−1 of norm ≤ 10r. -/
lemma IsTwoFactor.exists_near_one (H : IsTwoFactor l k j τ B e φ) r (hB : 1 ≤ B) (e0 : 0 < r) (he :
  r ≤ 100⁻¹) s (h : ‖(j s).1.1.1 - blockDiagPart ε (j s).1‖ ^ 2 + ‖(j s).2.1.1 - blockDiagPart η
  (j s).2‖ ^ 2 ≤ r ^ 2) : ∃ t, l.laplaceIntegrand k j φ s =
  l.laplaceIntegrand k j φ t ∧ ‖(subOnePair j t).1‖ ≤ 10 * r ∧ ‖(subOnePair j t).2‖ ≤ 10 * r := by
  let χ i : ℤ := (e.symm i).elim 0 1
  obtain ⟨K, R⟩ := H.exists_diagonal, norm_sq_add_re_trace_le (j s).1 B (3 * B) χ (-l.lowestKType),
    H.phase_eq s ▸ H.re_phase s, norm_sq_add_re_trace_le (j s).1 (-1) 0 χ (-χ),
    norm_sq_add_re_trace_le (j s).2 0 _ 0 _ (mod_cast H.weight_bounds_right)
  set Q := inclMatrix ℂ _
  have : Qᴴ * Q = 1 ∧ intDiagonal χ = 1 - Q * Qᴴ ∧ signMatrix ε * Q = Q := by
    simp [← ext_iff, reindex_equiv e, Q, inclMatrix, signMatrix, χ, H.sign_inl]
  simp [reindex_equiv e, χ, H.weight_eq_zero, ← diagonal_neg, -Matrix.mul_sub, -Matrix.sub_mul] at *
  set c := _ * (subOnePair j s).1
  have : ‖c‖ ^ 2 ≤ 6 * r ^ 2 := by nlinarith [R (by bound) (by grind [IsTwoFactor, IsSteep])]
  have ⟨⟨_, f, _⟩, v⟩ := inv_one_add_bounds (norm_smul_of_nonneg one_half_pos.le c).le
  set W : Matrix n n ℂ := _⁻¹
  let N := (subOnePair j s).1 * W * Q
  have a := mem_unitaryGroup_iff (A := 1 + Nᴴ * Q).2 (by
    linear_combination (norm := (simp [star, N, c, *, IsHermInvolution.isHermitian.eq,
      ← (signMatrix ε).mul_assoc Q]; module)) congr(Qᴴ * Wᴴ *
      $((j s).1.2) * W * Q - (signMatrix ε * $f * Q)ᴴ * N - Nᴴ * signMatrix ε * $f * Q))
  let ⟨s₀, h₁, h₂⟩ := K _ a
  let T := (subOnePair j (s₀ * s)).1
  obtain ⟨k₁, k₂⟩ := dsCoeff_mul_eq_of_zero_weight_block (⟨H.sign_inl ·, H.weight_eq_zero _⟩)
    h₁ congr($(j.map_mul _ s).1), H.trace_eq _ ▸ dsCoeff_mul_eq_of_zero_weight_block
    H.sign_weight_right h₂ congr($(j.map_mul _ s).2), ((re_le_norm _).trans (norm_trace_mul_le
    (norm_sub_le T c) v)).trans_eq' (by linear_combination (norm := (simp +zetaDelta
    [eq_add_of_sub_eq h₁, Q.trace_mul_comm, star, ← Qᴴ.mul_assoc Q, *]; ring)) congr(($(a.2) +
    Nᴴ * Q * Qᴴ * $f * Q).trace.re) : _ = c.trace.re - T.trace.re), sq_nonneg (‖T‖ - 2 * ‖c‖)
  use s₀ * s, by simp [laplaceIntegrand, H.phase_mul, ← H.phase_eq, ↓k₁, ↓k₂], ?_, ?_ <;> nlinarith
end
end
