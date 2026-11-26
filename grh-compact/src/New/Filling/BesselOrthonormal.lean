import New.Filling.BesselSchurBound
import Lib.Adelic.HolomorphicIntegral
import New.Filling.FrameNorm
import Lib.DiscreteSeries.RealMeasures

section
/-! Part of: Bessel subgroup of a real unitary group: coordinates, Haar measure, Bessel functions
(known result; see Lib.DiscreteSeries.Bessel.RealMeasures).

This file: Norms of a Bessel function and of its means are invariant under Bessel subgroup. -/

namespace IsBesselFunction

open MeasureTheory
variable {𝔰 I} [Fintype I] {rep W} (hW : @IsBesselFunction 𝔰 I _ rep W) {s : 𝔰.G₁} (hs :
  s ∈ besselS)
include hW hs

lemma enorm_integral_besselS_mul (β : _ → ℂ) g {μ : Measure _} :
    ‖∫ y, β y • W (s * g * y) ∂μ‖ₑ = ‖∫ y, β y • W (g * y) ∂μ‖ₑ := by
  obtain ⟨u, a, h, rfl⟩ := exists_besselU_mul_toBesselH hs
  rw [eq_comm, ← (Unitary.linearIsometryEquiv (besselValueRep rep h)).toLinearIsometry.enorm_map,
    ← LinearIsometry.integral_comp_comm]
  simp [mul_assoc, hW.2, hW.3, smul_comm (β _), integral_smul, ← ofReal_norm, norm_smul, a]; rfl

lemma enorm_besselS_mul y : ‖W (s * y)‖ₑ = ‖W
  y‖ₑ := by simpa using hW.enorm_integral_besselS_mul hs 1 y (μ := .dirac 1)
end IsBesselFunction
end

section
/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Definition of open-cell section, its domain, differentiability, norm and derivative
bounds. -/

noncomputable section


open Matrix Function Fin Metric Real Complex Norms.L2Operator Shape
variable {𝔰 : Shape} (x) (Z : 𝔰.FrameMat)

/-- For a complex n×n matrix Z, n = ϱ + 1 the length of the frame, the last diagonal entry ξ of
Z⁻¹. -/
def invCorner := Z⁻¹ 𝔰.top 𝔰.top

/-- The set Ω of invertible complex (ϱ+1)×(ϱ+1) matrices Z such that the last diagonal entry ξ
of Z⁻¹ satisfies |ξ| < 1. -/
def Shape.openCell := {Z : 𝔰.FrameMat | det Z ≠ 0 ∧ ‖invCorner Z‖ < 1}

/-- For a (ϱ+1)×(ϱ+1) complex matrix Z, the real number 1 − |ξ|², ξ the last diagonal entry of
Z⁻¹. -/
def cornerDefect := 1 - ‖invCorner Z‖ ^ 2

/-- Z lies in Ω (`Shape.openCell`), and ‖Z‖, ‖Z⁻¹‖ (operator norms) and δ^{−1/2} are at most P,
where δ = 1 − |ξ|², ξ the last diagonal entry of Z⁻¹. -/
def IsBoundedInCell P := Z ∈ openCell ∧ ‖Z⁻¹‖ ≤ P ∧ ‖Z‖ ≤ P ∧ (√(cornerDefect Z))⁻¹ ≤ P

/-- For a complex number x, the (ϱ+1)×(ϱ+1) diagonal matrix diag(1, …, 1, x). -/
def diagLast : 𝔰.FrameMat := diagonal (snoc 1 x)

variable (W := Zᴴ) (s := (1 - invCorner Z * invCorner W).sqrt)

/-- For Z and W (by default Zᴴ), the matrix with last row (0, …, 0, −1) and other entries
−(W⁻¹)_{a,last}(Z⁻¹)_{last,b}, halved unless b is last. -/
def sectionCoeff := diagLast (𝔰 := 𝔰) 0 - 1 - diagLast (𝔰 :=
  𝔰) 0 * W⁻¹ * (1 - diagLast (𝔰 := 𝔰) 2⁻¹) * Z⁻¹ * diagLast (𝔰 := 𝔰) 2

/-- The matrix (F·Y + F'·diag(1, …, 1, s))·Z, with F the frame, F' = (e*₁, …, e*_ϱ, x_{k₀}), Y =
`sectionCoeff`; its columns are the images of the frame under γ_Z. -/
def sectionFrame := (𝔰.frameCols * sectionCoeff Z W + 𝔰.dualFrameCols * @diagLast 𝔰 s) * Z

/-- The matrix 1 − FFᴴ − F'F'ᴴ + SFᴴ + (FW⁻¹ − S·Y(W, Z))·diag(1, …, 1, s⁻¹)·F'ᴴ, with S =
`sectionFrame`, Y = `sectionCoeff`; by default W = Zᴴ, s = √δ. -/
def sectionMatrix := 1 + (sectionFrame Z W - 𝔰.frameCols) * 𝔰.frameColsᴴ + ((𝔰.frameCols * W⁻¹ -
  sectionFrame Z W * sectionCoeff W Z) * @diagLast 𝔰 s⁻¹ - 𝔰.dualFrameCols) * 𝔰.dualFrameColsᴴ

variable {Z} (h : Z ∈ 𝔰.openCell)
attribute [local simp] gramDiscReal frameDisc cornerDefect mul_conj' forall_fin_succ' diagLast
  l2_opNorm_conjTranspose openCell invCorner
  dist_eq_norm isUnit_iff_isUnit_det slitPlane_ne_zero mem_slitPlane_of_norm_lt_one Complex.sqrt
attribute [local simp ←] conjTranspose_nonsing_inv ofReal_pow

lemma gramDiscReal_eq (h : det Z ≠ 0) : gramDiscReal Z = ‖det Z‖ ^ 2 * cornerDefect Z := by
  simp [Z.inv_def, adjugate_fin_succ_eq_det_submatrix', field]; rfl

lemma mem_openCell_iff :
  Z ∈ openCell ↔ 0 < gramDiscReal Z := by by_cases Z.det = 0 <;> simp_all [↓gramDiscReal_eq]

@[fun_prop] lemma continuous_gramDiscReal :
  Continuous (@gramDiscReal 𝔰) := by fun_prop [gramDiscReal, frameDisc, leadingMinor]

/-- The open cell, the domain of the double coset section, is an open set. -/
lemma isOpen_openCell : IsOpen 𝔰.openCell :=
  Set.ext (@mem_openCell_iff 𝔰) ▸ isOpen_Ioi.preimage continuous_gramDiscReal

include h

lemma differentiableAt_sectionMatrix_uncurry (o : W ∈ openCell) :
  DifferentiableAt ℂ (sectionMatrix · ·).uncurry (Z, W) := by
  repeat erw [differentiableAt_pi] <;> intro
  have : ∀ i j, Differentiable ℂ (@diagLast 𝔰 · i j) := by simp [diagonal, eq_comm]
  have := mul_lt_mul'' h.2 o.2
  simp_all only [uncurry, sectionMatrix, sectionFrame, sectionCoeff, invCorner,
    nonsing_inv_eq_ringInverse, mul_apply,
    Matrix.add_apply, sub_eq_add_neg, Matrix.neg_apply]; fun_prop (disch := simp_all)

lemma cornerDefect_pos : 0 < cornerDefect Z := by aesop

@[simp] lemma sqrt_eq_sqrt_cornerDefect : (1 - invCorner Z * invCorner Zᴴ).sqrt = √(cornerDefect
  Z) := by simp_all [sqrt_eq_rpow, ofReal_cpow, le_of_lt]

/-- For Z in the open set Ω (Z invertible, with last diagonal entry of Z⁻¹ of absolute value
less than 1), the matrix-valued map `sectionMatrix`, as a function of its matrix argument,
is real-differentiable at Z. -/
lemma differentiableAt_sectionMatrix : DifferentiableAt ℝ sectionMatrix Z :=
  .comp Z (f := fun Z ↦ (Z, star Z))
  ((differentiableAt_sectionMatrix_uncurry Zᴴ h (by simpa)).restrictScalars ℝ) (by fun_prop)

omit h in
/-- Let r > 0, P ≥ 8, and let every y within r of Z lie in Ω with ‖y⁻¹‖, ‖y‖, δ(y)^{−1/2} ≤ P.
Then the matrix of γ_Z has norm ≤ P¹², and its real derivative in Z has norm ≤ 2P¹²/r. -/
lemma norm_sectionMatrix_le (_ : Z ∈ 𝔰.openCell) {P r} (hr : 0 < r) (hP : 8 ≤ P)
  (H : ∀ y ∈ ball Z r, IsBoundedInCell y P) :
  ‖sectionMatrix Z‖ ≤ P ^ 12 ∧ ‖fderiv ℝ sectionMatrix Z‖ ≤ 2 * P ^ 12 / r :=
  have b {x y} (hp : (x, y) ∈ ball (Z, Zᴴ) r) : _ ∧ ‖sectionMatrix x y‖ ≤ P ^ 12 := by
    simp [IsBoundedInCell, ← (y - _).l2_opNorm_conjTranspose] at hp H
    obtain ⟨⟨o, _, _, q⟩, _, o', _, -⟩ := H _ hp.1, (by simp [pi_norm_le_iff_of_nonempty] :
      ∀ s, ‖diagLast (𝔰 := 𝔰) s‖ ≤ 1 + ‖s‖), by simpa using H _ hp.2
    use differentiableAt_sectionMatrix_uncurry _ o o'; delta sectionMatrix sectionFrame
      sectionCoeff; trans; repeat' first
      | apply_assumption (transparency := .reducible) [mul_le_mul_of_nonneg, norm_add_le_of_le,
        norm_sub_le_of_le, norm_inclMatrix_le_one, (l2_opNorm_mul ..).trans] | positivity | simp
              [Injective, norm_cpow_of_imp, ← by simpa using sqrt_eq_rpow] | rfl
    grw [← (_ : 4⁻¹ * cornerDefect x ≤ ‖_‖), norm_sub_le, norm_mul, o.2, o'.2,
      sqrt_le_self_iff.2] <;> simp [o]; grw [q, ← sub_nonneg]
    obtain ⟨t, _, rfl⟩ := exists_nonneg_add_of_le hP; ring; bound
    grw [← norm_sub_norm_le, norm_mul, o'.2, norm_one]; nlinarith
  ⟨(b (by simpa)).2, norm_fderiv_le_of_lip' ℝ (by bound) (.mono (ball_mem_nhds Z hr) fun y ↦
    by simpa [two_mul, ← conjTranspose_sub] using
    norm_sub_le_of_holomorphic_bdd (Prod.rec @b) (y, yᴴ))⟩
end
end

section
/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Explicit section is unitary and represents every double coset of the open cell. -/


open Matrix Complex Fin IsHermInvolution MatMul
variable {𝔰 : Shape} {Z : 𝔰.FrameMat} (h : Z ∈ 𝔰.openCell)
attribute [local simp] sum_univ_castSucc diagonal_apply Matrix.mul_apply actOnCols diagLast
  splitGram middleGram inclMatrix cornerDefect_pos Real.sqrt_eq_zero' frameGram prod_univ_castSucc
  conjTranspose_nonsing_inv Fin.ne_of_gt isUnit_iff_isUnit_det forall_fin_succ'
attribute [local simp ←] ext_iff
attribute [-simp] fromCols_mul_fromBlocks conjTranspose_fromCols_eq_fromRows_conjTranspose

lemma sectionMatrix_mul_frameCols : sectionMatrix Z * 𝔰.frameCols =
  sectionFrame Z := by simp [sectionMatrix]

lemma frameCols_gram_sectionMatrix : 𝔰.frameColsᴴ * 𝔰.J₁ * (sectionMatrix Z * 𝔰.frameCols) =
  Z := by simp [↓sectionMatrix_mul_frameCols, sectionFrame]; simp [sectionCoeff]

/-- The section γ_Z: the element of G₁ with matrix `sectionMatrix` at Z if Z lies in
`Shape.openCell` (det Z ≠ 0, |ξ| < 1), and the identity otherwise. -/
noncomputable def gramSection (Z : 𝔰.FrameMat) : 𝔰.G₁ :=
  U.of isUnit (if Z ∈ 𝔰.openCell then sectionMatrix Z else 1) (by
  split_ifs with h; swap; simp
  let C := fromCols 𝔰.frameCols 𝔰.dualFrameCols; let J := Cᴴ * 𝔰.J₁ * C; let Δ :=
    @diagLast 𝔰 (√(cornerDefect Z))⁻¹
  obtain ⟨d, a, b⟩ := cornerDefect_pos h, (by simp [C, J]; lia : Cᴴ * C = 1 ∧ 𝔰.J₁ = actOnCols C J)
  let x := fromBlocks Z⁻¹ (sectionCoeff Zᴴ Z * Δ) 0 (1 : 𝔰.FrameMat)
  let y := fromBlocks (sectionCoeff Z) (Zᴴ⁻¹ * Δ) (diagLast √(cornerDefect Z)) 0; have e :
    yᴴ * J * y = xᴴ * J * x := by
                           simp +zetaDelta [sectionCoeff, map_ofNat, ← ofReal_pow, d.le, d.ne',
                             ← conjTranspose_nonsing_inv, field]
                           simp [cornerDefect, invCorner]; grind [conj_mul']
  rw [(by simp [x, y, C, Δ, inv_fromBlocks_zero₂₁_of_isUnit_iff', h, h.1, -ext_iff, sectionMatrix,
    sectionFrame, conjTranspose_fromCols_eq_fromRows_conjTranspose]; abel : sectionMatrix _ =
    actOnCols C (y * x⁻¹))]
  simpa [↓b, mul_mul_eq_of_mul_eq a, x, h.1, -ext_iff] using congr(actOnCols C (x⁻¹ᴴ * $e * x⁻¹)))

@[fun_prop] lemma measurable_gramSection : Measurable (@gramSection 𝔰) :=
  .subtype_mk (measurable_comap_iff.2 (by
  exact ContinuousOn.measurable_piecewise (@differentiableAt_sectionMatrix _ · ·
    |>.continuousAt.continuousWithinAt) (by fun_prop) isOpen_openCell.measurableSet))

include h

lemma diagLast_sqrt_mul_inv :
  @diagLast 𝔰 √(cornerDefect Z) * diagLast (√(cornerDefect Z))⁻¹ = 1 := by aesop

/-- For Z in the open set Ω (Z invertible, with last diagonal entry of Z⁻¹ of absolute value
less than 1), the matrix underlying the section γ_Z ∈ G₁ equals the explicit matrix
`sectionMatrix` at Z. -/
lemma coe_gramSection : (gramSection Z).1.1 = sectionMatrix Z := ite_eq_left h

lemma gramSection_eventuallyEq : (gramSection ·|>.1.1) =ᶠ[nhds Z] sectionMatrix :=
  .mono (isOpen_openCell.mem_nhds h) (@coe_gramSection _)

/-- For Z in Ω, the element γ_Z of G₁ has frame matrix Z(γ_Z) = Z. -/
lemma realFrameGram_gramSection : realFrameGram (gramSection Z) =
  Z := by simpa [coe_gramSection h] using frameCols_gram_sectionMatrix (Z := Z)

/-- If γ ∈ G₁ has Z(γ) in Ω, then γ = u h γ_{Z(γ)} h' u' with u, u' in the frame-fixing
unipotent group U⁰ and h, h' in the image of U(κ). -/
lemma exists_eq_mul_gramSection_mul {γ} (y : realFrameGram γ = Z) :
    ∃ q k r l, γ = unipotentOf q * embedH k * gramSection Z * (unipotentOf r * embedH l)⁻¹ := by
  have A {s} (z : realFrameGram s = Z) : (framePair s)ᴴ * 𝔰.J₁ * framePair s =
    fromBlocks (diagLast 0 - 1) Z Zᴴ
    (diagLast 0 - 1) := by simpa [← z] using congr(submatrix $(s.2) 𝔰.besselFrame 𝔰.besselFrame)
  have B {s} z := HasLeftInv.of_isUnit_gram (isUnit_of_mul_isUnit_right (x := fromBlocks 0 Zᴴ⁻¹
    Z⁻¹ 0) (by rw [@A s z]; simp [h.1]; rw [det_of_isUpperTriangular] <;> simp [BlockTriangular,
    conj_mul', ← conjTranspose_nonsing_inv] <;> norm_cast <;> grind [cornerDefect_pos h,
    cornerDefect, invCorner]))
  obtain ⟨g, e⟩ := witt ⟨I, by simp⟩ isHermitian isUnit (B y) (B (realFrameGram_gramSection h)) (A
    (realFrameGram_gramSection h) ▸ A y)
  simp [fromCols_ext_iff, ← mul_inclMatrix, -inclMatrix, -ext_iff] at e
  obtain ⟨⟨q, k, a⟩, p, l, b⟩ := exists_embedH_eq_of_fix_frameCols e.1,
    @exists_embedH_eq_of_fix_frameCols _ ((gramSection Z)⁻¹ * g * γ) (by simp [e, -inclMatrix])
  use q, k⁻¹, p, l⁻¹, by simp_rw [map_inv, ← a, ← b]; group
end

section
/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Jacobian and injectivity of the open-cell double coset chart of U(p,q). Explicit
perturbation bounds for determinant, inverse and discriminant near an open-cell matrix. -/

open Fin Module Complex Finset HasGaussianIntegral Haar MatMul Matrix MeasureTheory Sum
  Norms.L2Operator

/-- The chart (Z, η, q, y, q') ↦ u(q)·c(η)·γ_Z·(u(q')·c(y))⁻¹ of G₁, with u = `unipotentOf` and
c the Cayley chart of H = U(X₀), at η after the coordinate change `skewColumnEquiv`. -/
noncomputable def openCellChart {𝔰 : Shape} := fun (Z, θ, q, η, r) ↦ unipotentOf q * embedH
    (cayleyChart 1 (skewColumnEquiv 𝔰.k₀ (θ, 0))) * gramSection Z *
  (unipotentOf r * embedH (cayleyChart 1 η))⁻¹

set_option synthInstance.maxSize 999

attribute [-simp] Prod.forall map_mul _root_.mul_inv_rev

attribute [local simp] forall_fin_succ' coe_embedH inclMatrix_gram_eq_zero
  inclMatrix_gram_mul_eq_zero inclMatrix_gram_eq_one inclMatrix_gram_mul_eq_self actOnCols
  sectionFrame sectionMatrix val_unipotentOf_coe

/-- The real-linear map from square matrices S to the parameter space of the chart
`openCellChart` that reads each parameter from a block of S; its Z-component is F'ᴴSF,
with F = `Shape.frameCols` and F' = `Shape.dualFrameCols`. -/
noncomputable def chartCoords {𝔰 : Shape} := let r i := inr (inl (ite (i = 𝔰.k₀) (inr ()) (inl i)))
  let R S w d := ((skewCoords S).submatrix w w, S.submatrix d w, (skewCoords S).submatrix d d)
  (⟨⟨fun S ↦ (𝔰.dualFrameColsᴴ * S * 𝔰.frameCols, ((skewColumnEquiv 𝔰.k₀).symm (R S r inl).1).1,
    (R S r inl).2, -R S 𝔰.indexX₀ eStar), by simp [R, submatrix_add, ↓neg_add,
         -skewColumnEquiv_spec]⟩, by simp [R, submatrix_smul, -skewColumnEquiv_spec]⟩ : _ →ₗ[ℝ] _)

/-- The real-linear map (η, b, c) ↦ (Wη + Db)Wᴴ + (D·sk(c) − Wbᴴ)Dᴴ, where W, D have columns
x_i, e*_a and sk is `skewOfReal`. -/
noncomputable def besselTangent {𝔰 : Shape} :=
    (.mk ⟨⟨fun (η, b, c) ↦ (𝔰.definiteCols * η + 𝔰.dualCols * b) * 𝔰.definiteColsᴴ +
  (𝔰.dualCols * skewOfReal c - 𝔰.definiteCols * bᴴ) * 𝔰.dualColsᴴ, by
    simp; grind⟩, by simp [star_trivial, smul_sub]⟩ : Matrix 𝔰.κ _ ℂ × 𝔰.UnipotentParams →L[ℝ] _)

lemma logDerivU_unipotentOf_mul_embedH {𝔰 : Shape} {V} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {z' : V →L[ℝ] _ × 𝔰.UnipotentParams} {z p} (hz : HasFDerivAt z z'
  p) : let F p := unipotentOf (z p).2 * embedH (cayleyChart 1 (z p).1); DifferentiableAtU F p ∧ ∀ v,
    let (η, b, c) := z' v; logDerivU F p v = besselTangent (logDerivU (cayleyChart 1) (z p).1 η,
      b * (cayleyChart 1 (z p).1).1.1, c + skewCoords (skewAdjointPart ℝ ((z p).2.1 * bᴴ))) := by
  have h := (besselTangent ∘L .inr ..).hasFDerivAt.comp p hz.snd |>.const_mul 𝔰.J₁
  refine (fun h ↦ ⟨⟨_, h⟩, (congr(_ * $h.fderiv ·).trans ?_)⟩) ((((h.add ((h.mul'
    h).const_smul (2⁻¹ : ℂ))).const_add 1).mul' (((besselTangent ∘L .inl ..).hasFDerivAt.comp p
    (((abs_det_logDerivU_cayleyChart (det_cayleyDenom_one_ne_zero _)).1.hasFDerivAt.comp p
    hz.fst).sub_const 1)).const_add 1)).congr_of_eventuallyEq
    (.of_forall fun _ ↦ ?_)) <;> simp [besselTangent, -map_sub, star, J₁_eq, logDerivU] <;> module

lemma exists_symm_eq_chartCoords_skewOfReal {𝔰} : ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧ ⇑e.symm =
  @chartCoords 𝔰 ∘ₗ skewOfReal := by
  apply exists_measurePreserving_equiv; simp_intro _ [chartCoords, mul_inclMatrix,
    conjTranspose_inclMatrix_mul]; simp [skewOfReal, sum_univ_castSucc, div_pow,
    Fintype.sum_eq_add_sum_subtype_ne _ 𝔰.k₀, RCLike.norm_sq_eq_def]; ring_nf
  simp [sum_add_distrib, @sum_comm (Fin _) _ (@Subtype 𝔰.κ _)]; nth_rw 2 [sum_comm]; ring
  simp [finrank_matrix]; grind [@Fintype.card_pos _ _ ⟨𝔰.k₀⟩]

/-- For some measure-preserving real-linear identification e of the parameter space, at every p
with Z in Ω the chart `openCellChart` is differentiable and its logarithmic derivative has
|det| equal to g(Z)^{|κ|−1} times two Cayley weights `cayleyDensity`; g(Z) = |det Z|² − |D_ϱ|²
(`gramDiscReal`), D_ϱ the leading principal minor of order ϱ of Z. -/
lemma openCellChart_jacobian {𝔰 : Shape} : ∃ e : _ ≃ₗ[ℝ] _, MeasurePreserving e ∧
  ∀ p ∈ 𝔰.openCell ×ˢ Set.univ, DifferentiableAtU (@openCellChart 𝔰) p ∧
  |(e.symm.1 ∘ₗ skewCoords ∘ₗ logDerivU openCellChart p).det| = gramDiscReal p.1 ^ (𝔰.k - 1) *
  (cayleyDensity 1 (skewColumnEquiv 𝔰.k₀ (p.2.1, 0)) * cayleyDensity 1 p.2.2.2.1) := by
  cases Nat.exists_eq_add_of_lt (@Fintype.card_pos _ _ ⟨𝔰.k₀⟩)
  refine exists_symm_eq_chartCoords_skewOfReal.imp fun e ↦ .imp_right fun _ p ⟨hp@⟨_, _⟩, _⟩ ↦ ?_
  obtain ⟨⟨_, hγ⟩, s⟩ := differentiableAt_sectionMatrix hp, hasStrictFDerivAt_snd (𝕜 := ℝ) (p := p)
  obtain ⟨⟨a⟩, b, γ, d⟩ :=
    logDerivU_unipotentOf_mul_embedH (((skewColumnEquiv _).hasStrictFDerivAt.comp p (s.fst.prodMk
    (hasStrictFDerivAt_const ..))).prodMk s.snd.fst).hasFDerivAt,
    logDerivU_unipotentOf_mul_embedH s.snd.snd.hasFDerivAt, (hγ.congr_of_eventuallyEq
    (gramSection_eventuallyEq hp)).comp p hasFDerivAt_fst, cornerDefect_pos hp; extract_lets F at b
  have h : DifferentiableAtU openCellChart p := (a.mul ⟨_, γ⟩).mul
    (by simpa only [Ring.inverse_unit] using! b.1.inverse ⟨_, rfl⟩)
  let Δ := @diagLast 𝔰 (√(cornerDefect p.1))⁻¹; let R := 1 + 𝔰.dualFrameCols * (𝔰.frameCols -
    𝔰.dualFrameCols)ᴴ
  let M A B := 𝔰.frameCols * ((A * Δ - 1) * 𝔰.frameColsᴴ + B * Δ * 𝔰.dualFrameColsᴴ)
  let K := 1 + M p.1⁻¹ (sectionCoeff p.1ᴴ)
  have : (gramSection p.1).1.1 * K = R + M (sectionCoeff p.1) p.1ᴴ⁻¹ := by
    simp +zetaDelta [coe_gramSection, *, mul_mul_eq_of_mul_eq (diagLast_sqrt_mul_inv _)]; abel
  have q v A B : besselTangent v * M A B = 0 ∧
    (M A B)ᴴ * besselTangent v = 0 := by simp [M, besselTangent]
  have t := abs_det_skew_congruence e.symm (F p * K) (skewCoords ∘ₗ logDerivU openCellChart p)
  generalize hT : (e.symm.1 ∘ₗ _ : End ..) = T at t
  have hT w : T w = _ := .trans (by simp [← hT, conjTranspose_logDerivU, *])
    congr(chartCoords (Kᴴ * $(sub_eq_of_eq_add (logDerivU_mul h b.1 w)) * K)).symm
  simp [openCellChart, logDerivU_mul a ⟨_, γ⟩, *, F,
    (logDerivU.eq_1 ..).trans congr(_ ∘ₗ $γ.fderiv.1),
    mul_mul_eq_of_mul_eq (conjTranspose_mul _ K).symm, mul_mul_eq_of_mul_eq (q ..).2] at hT
  rw [det_mul, det_one_add_mul_comm, det_eq_mul_of_block_triangular, det_eq_mul_of_block_triangular,
    abs_mul, abs_mul, det_mulLeft_mulRight_real (p.1ᴴ⁻¹ *
    Δ)ᴴ (p.1⁻¹ * Δ), abs_det_logDerivU_col_eq_cayleyDensity, ← LinearMap.det_conj _ (.prodAssoc ..),
    det_eq_mul_of_block_triangular, det_mulLeft_mulRight_real 1 (cayleyChart 1 (skewColumnEquiv _
    (p.2.1, 0))).1.1, det_eq_mul_of_block_triangular 1, det_eq_mul_of_block_triangular
    (skewCoords ∘ₗ logDerivU (cayleyChart 1) p.2.2.2.1), det_eq_mul_of_block_triangular _ _
    (LinearMap.id.ext _), det_mulLeft_mulRight_real 1 (cayleyChart 1 p.2.2.2.1).1.1] at t
  simpa [abs_det_logDerivU_cayleyChart, mul_pow, pow_mul, Δ, diagLast, d.le, abs_of_pos, *,
    gramDiscReal_eq, prod_univ_castSucc, pow_add, field] using t.symm
  all_goals simp [*, K, chartCoords, Prod.mk_zero_zero, LinearEquiv.prodAssoc]
  rotate_right; exact fun _ ↦ .trans (by simp [R, M, besselTangent]) congr(_ * (_ *
    ($(((mulLeftLinearMap .. ∘ₗ mulRightLinearMap ..).toContinuousLinearMap.hasFDerivAt.comp _ hγ
    ).unique ((hasFDerivAt_id _).congr_of_eventuallyEq
    (.of_forall (@frameCols_gram_sectionMatrix _)))) _ * _)))
  all_goals simp [entrywise, @skewCoords.eq_1 𝔰.BesselIndex, inclMatrix, -re_sum, -im_sum, R,
    skewOfReal,
    sum_univ_castSucc, -Matrix.mul_sub, -Matrix.add_mul]; clear * -; simp [besselTangent,
    inclMatrix, mul_apply, -map_add] <;> first | (intros; simp [skewOfReal]; grind) |
    aesop (add simp skewCoords)

/-- The chart `openCellChart` is injective where Z lies in the open cell. -/
lemma openCellChart_injOn {𝔰 : Shape} : (𝔰.openCell ×ˢ Set.univ).InjOn openCellChart := by
  have u : (fun q ↦ (@unipotentOf 𝔰 q).1.1 * 𝔰.dualCols).Injective := fun _ _ e ↦ by
    simpa [by simpa using congr(𝔰.definiteColsᴴ * $e),
      Prod.ext_iff] using congr(skewCoords (𝔰.isotropicColsᴴ * $e))
  rintro ⟨Z, _, q, _, r⟩ ⟨hZ⟩ ⟨_, _, p, _, s⟩ ⟨⟩ e
  cases by simpa [openCellChart, realFrameGram_mul_invariant, realFrameGram_gramSection,
    Subgroup.mul_mem_sup, unipotentOf_mem_besselU0, *] using congr(realFrameGram $e)
  have c {x g} (e : openCellChart (Z, x) = g) := by
    simpa [coe_gramSection, hZ.1, hZ, diagLast_sqrt_mul_inv] using congr($(eq_mul_of_mul_inv_eq
      e).1.1 * (𝔰.frameCols * Z⁻¹ * @diagLast 𝔰 (√(cornerDefect Z))⁻¹))
  obtain ⟨this, e1⟩ := @u q p, (c e).trans (c rfl).symm
  simp [entrywise, inclMatrix, forall_and] at e1 this
  simp [openCellChart, cayleyChart_col_injective _ (funext e1.2.2), e1.1.elim this] at e ⊢
  simp_all [@u r s, by simpa [Units.val_inj, cayleyChart_injOn.eq_iff] using
    congr(𝔰.definiteColsᴴ * $e.1.1 * 𝔰.definiteCols)]

open Real Fintype Metric

/-- Let M ≥ 8(ϱ+1), 𝗀(Z) ≥ M⁻¹, all |Z_ab| ≤ M², P ≥ M^{9(ϱ+1)} and ‖Z' − Z‖ < P⁻⁶. Then 𝗀(Z') ≥
𝗀(Z)/2, Z' lies in Ω (`Shape.openCell`), and ‖Z'⁻¹‖, ‖Z'‖, δ(Z')^{−1/2} ≤ P, with δ =
`cornerDefect`. -/
lemma mem_openCell_and_bounds_of_near {𝔰 M P Z Z'} (hg : M⁻¹ ≤
  @gramDiscReal 𝔰 Z) (hM : 8 * (𝔰.ϱ + 1) ≤ M) (hZ : ∀ a b, ‖Z a b‖ ≤ M ^ 2) (hP : M ^ (9 * 𝔰.n) ≤
  P) (h : Z' ∈ ball Z (P ^ 6)⁻¹) : gramDiscReal Z / 2 ≤ gramDiscReal Z' ∧ IsBoundedInCell Z' P := by
  have ⟨r, m, _, _⟩ : 𝔰.n ≤ M ∧ 2 ≤ M ∧ M ≤ P ∧ 1 ≤ P := by grind [le_self_pow₀]
  have p n := hP.trans' ∘ pow_le_pow_right₀ (m := n) (by grind)
  have k := h.out.trans_le (c := 1) (by bound)
  have z {Y} (h : dist Y Z < 1) a b : ‖Y a b‖ ≤ M ^ 3 := by
    grw [norm_le_insert', hZ, ← Y.sub_apply, norm_apply_le_l2_opNorm, ← dist_eq_norm]; nlinarith
  have s l := (abs_norm_sub_norm_le ..).trans ((norm_sub_le_of_holomorphic_bdd (f :=
    (leadingMinor · l ^ 2)) (fun _ _ ↦ ⟨by simp [leadingMinor, det_apply]; fun_prop, by grw
    [norm_pow, leadingMinor, norm_det_le_norm_pow, l2_opNorm_le_of_apply
    (by tauto), ← sq, Fintype.card_fin, mul_pow, ← pow_mul, ← pow_mul, p, l.is_le, r, p] <;> lia⟩)
    _ k).trans (c := M⁻¹ / 4) (by grw [mem_ball_iff_norm.1 h]; field; nlinarith))
  have ⟨g, a⟩ : gramDiscReal Z ≤ 2 * gramDiscReal Z' ∧ 0 < gramDiscReal Z' := by
    simp_all [Fin.forall_fin_succ', gramDiscReal, leadingMinor, frameDisc, mul_conj',
      ← ofReal_pow]; grind [inv_pos]
  have ⟨n, _⟩ := mem_openCell_iff.2 a
  grw [g, m, ← inv_mul_le_iff₀, ← sq, ← le_sqrt', gramDiscReal_eq n, sqrt_mul, sqrt_sq,
    inv_le_comm₀] at hg
  have d := hg; grw [mul_le_of_le_one_right] at d; rw [mul_inv, inv_mul_le_iff₀] at hg
  simp [IsBoundedInCell, Z'.inv_def, norm_smul, mem_openCell_iff]; grw [d, l2_opNorm_le_of_apply (by
    simp_intro .. [adjugate_fin_succ_eq_det_submatrix']
    grw [norm_det_le_norm_pow, l2_opNorm_le_of_apply (by tauto), ← sq, Fintype.card_fin,
      𝔰.ϱ.le_succ, r]),
    hg, norm_det_le_norm_pow, l2_opNorm_le_of_apply (z k), ← sq, Fintype.card_fin, r]
  ring; repeat first | bound | simp [*, cornerDefect, ← pow_add]

lemma euclidean_enorm_sq_eq_sum {I} [Fintype I] (u : EuclideanSpace ℂ I) : ‖u‖ₑ ^ 2 =
  ∑ i, ‖u i‖ₑ ^ 2 := by simp [enorm, u.nnnorm_eq, ← ENNReal.coe_pow]
end

section
/-! This file: the coordinates of the full function of a Bessel system are orthonormal. -/

open Matrix MeasureTheory Complex Subgroup ComplexConjugate

/-- The coordinates W_i of the full function of a Bessel system are orthonormal in L²(𝖴∖G₁): the
integral of W_i times the conjugate of W_j is δ_ij. -/
lemma BesselSystem.orthonormal {𝔰 b f} (B : BesselSystem 𝔰 b f) i j :
    ∫ y, B.W .full y i * conj (B.W .full y j) ∂besselQuotMeasure = ite (i = j) 1 0 := by
  obtain ⟨⟨a, h2, _⟩, ⟨⟩⟩ := B.tail, B.tail.isBesselFunction .full
  have {i j} := (h2.eval_piLp i).mul_of_top_left ((a .full).memLp_top.eval_piLp j).star
  simp [Pi.mul_def] at this
  apply (B.irreducible (of _) fun s ↦ .symm ((commute_unitary_iff_star_right_conjugate (by simp)).2
    (ext fun i j ↦ .trans ?_ (identDistrib_orbitMeasure_comp (measurePreserving_conj_bessel
    mem_besselU besselS_le_normalizer_besselU (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem s)))
    (measurePreserving_mul_left _ (embedH s)) ?_ ?_).integral_eq))
    ).elim fun c hc ↦ congr($hc i j).symm.trans (by
      apply_fun trace at hc
      simp_all [← mul_conj', trace, integral_finsetSum, PiLp.norm_sq_eq_of_L2, ← ofReal_inj,
    lintegral_enorm_sq _ (a _).memLp_top, ← integral_complex_ofReal]) <;> generalize ⇑(B.W .full) =
    F at *
  simp (disch := fun_prop) [mul_apply, ↓← integral_const_mul, ← integral_finsetSum, ↓mul_comm]
  repeat simp [smul_def, *, mulVec_eq_sum, mul_conj',
    ← Finset.sum_mul, ← mul_assoc, mul_comm, mul_right_comm _ (F _ i)]
end
