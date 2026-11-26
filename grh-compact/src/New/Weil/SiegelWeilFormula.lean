import New.Weil.DatumLevel
import New.Weil.Edge
import Lib.ClassField.UniformiserScalar
import New.Weil.PairSumNegation
import New.Weil.ZeroTermHeight
import New.Weil.EquivariantCoefficients

section
/-! Part of: Joint harmonics and global theta lifts between discrete series types (known result; see
Lib.Weil.Lift.Edge).

This file: Theta lift on forms: equivariance, adjoint, matched real data lift types to types. -/

noncomputable section


open ComplexConjugate Space InnerProductSpace Submodule LinearMap
variable {E n n'} [Field E] [CMType E] [Fintype n] [Fintype n'] {s t X} [NormedAddCommGroup X]
  [NormedSpace ℂ X] [CompleteSpace X] {S : Space E n s} {T : Space E n' t} (K : ThetaKernel X S T)
  (e e') {φ φ'}

/-- A chosen bilinear map (φ, y) ↦ L_φ y to forms of type e' on T, equal to `Space.lift`
when y is rapid and its lift is such a form. -/
def formLift : X →ₗ[ℂ] S.Form e →ₗ[ℂ] T.Form e' := (K.liftBilin.compl₂
  (S.rapidFunctions.1.subtype.leftInverse ∘ₗ Submodule.subtype _)).compr₂ (Submodule.subtype
  _).leftInverse

/-- For the kernel K, the datum φ is an arrow e → e': forms of type e on S are rapid, and their
lifts by φ are forms of type e' on T. -/
def IsArrow φ := ∀ y : S.Form e, ↑y ∈ S.rapidFunctions ∧ T.IsForm e' (lift K φ y)

variable {K e e'}

/-- Complex conjugation F ↦ conj(F), as a conjugate-linear map from forms of type e to forms of
type e', when e' is the conjugate of e. -/
def conjForm (h : e' = star e) : S.Form e →ₗ⋆[ℂ] S.Form e' :=
  (starLinearEquiv _).1.restrict fun _ ↦ h ▸ .conj

@[simp] lemma coe_conjForm h (y : S.Form e) : (conjForm h y : S.Form e') = (conj <| y ·) := rfl

/-- Let Φ be an edge e → e' for the real Weil representation of weights γ, γ', a, b characters
of these weights, and f ∈ 𝒲_f. Then for ω_{a,b}, Φ ⊗ f is an arrow e → e' and, for the
swapped pair, ē' → ē.

Known result: Joint harmonics and global theta lifts between discrete series types. -/
lemma IsEdge.isArrow [WeilData E] {γ γ' Φ ψ ψ' f} (h : IsEdge (realPairWeil γ γ') e e' Φ) (a b :
  AutChar E) [a.HasWeight γ ψ] [b.HasWeight γ' ψ'] (hf : f ∈ (S.hom T).finitePart) :
  IsArrow (pairThetaKer S T a b) e e' (integrated _ Φ f) ∧ IsArrow (pairThetaKer S T a b).swap
  (star e') (star e) (integrated _ Φ f) := (exists_level_pairWeil a b hf).elim fun K ⟨L,
  _⟩ ↦ by use fun y ↦ ⟨y.2.mem_rapidFunctions h.isCuspKernel_source,
  ((h.lift_isForm_and_eq_realConv _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 L ?_⟩, fun y ↦
  ⟨y.2.mem_rapidFunctions h.2.1, ((h.2.3 _ ⟨0, rfl⟩).choose_spec _ ?_ y.2).1 K ?_⟩ <;>
  simp_all [lift_mul_right, ← Prod.mk_one_one, pairWeil_integrated]

namespace IsArrow

variable (h : IsArrow K e e' φ) {ε ε'} (h' : IsArrow K.swap ε' ε φ)
include h

lemma eq_formLift_of_coe_eq {y} z (a : z.1 = lift K φ' y.1) : z = formLift K e e' φ' y :=
  have l := @leftInverse_apply_of_inj; l (ker_subtype _) z ▸
  congrArg _ (a.trans congr(K.liftBilin φ' $(l (by simp) ⟨_, (h y).1⟩)).symm)

attribute [irreducible] formLift

/-- If φ is an arrow e → e' from S to T, then for every form y of type e on S, `formLift` of φ
and y equals, as a function, the theta lift `Space.lift` of y. -/
lemma coe_formLift y : formLift K e e' φ y = lift K φ y :=
  h.eq_formLift_of_coe_eq ⟨_, (h _).2⟩ rfl ▸ rfl

/-- If φ is an arrow e → e', then for k, k' in the finite groups of S, T and a form y of type e,
the right translate by k' of L_φ y equals L_{ω(k,k')φ} applied to the translate of y by k. -/
lemma formRep_formLift k k' y : T.formRep _ k' (formLift K e _ φ y) =
  formLift K e e' (K.ω ((1, k), 1, k') φ) (S.formRep e k y) :=
  h.eq_formLift_of_coe_eq _ (h.coe_formLift y ▸ funext (K.lift_equivariant y.2.1 _ _ _) :)

lemma formRep_formLift_of_eq_smul {k k'} {c : ℂ} (H : K.ω ((1, k), 1, k') φ = c • φ') y :
  T.formRep _ k' (formLift K e _ φ y) =
  c • formLift K e e' φ' (S.formRep e k y) := by simp [h.formRep_formLift k, *]

include h'

/-- Lift and descent are transposes: if φ is an arrow e → e' and, for the swapped pair, an arrow
ε' → ε, then ∫_{[T]} z·L_φ y = ∫_{[S]} y·D_φ z for forms y of type e and z of type ε'. -/
lemma integral_mul_formLift_swap y z : ∫ g, z g * formLift K e e' φ y g ∂T.quotMeasure = ∫ g,
  y g * formLift K.swap ε' ε φ z g ∂S.quotMeasure :=
  by simp [coe_formLift, K.integral_lift_eq_integral_descent, h _, h' _, *]

/-- If φ is an arrow e → e' and, for the swapped pair, an arrow between the conjugate types,
then ⟨x, L_φ y⟩ = ⟨conj(D_φ conj(x)), y⟩: the adjoint of the lift is the conjugate of the
descent. -/
lemma inner_formLift_adjoint b b' x y : ⟪formLift K e e' φ y, x⟫_ℂ = ⟪y,
  conjForm b' (formLift K.swap ε' ε φ (conjForm b x))⟫_ℂ := star_inj.1 (by simp [inner, petersson,
  ← integral_conj, mul_comm, ← h.integral_mul_formLift_swap h'])
end IsArrow
end
end

section
/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Eichler commutation relation of Hecke polynomials through theta lifts at split places. -/


open Matrix Fintype WeilData AutChar HeckeChar Valued Space G CharUnramifiedAt
open Finset hiding card

/-- Maximum principle: if v is bounded above, ∑|a_i| < l, and l·v(g) ≤ ∑|a_i|·v(r g i) for all g
(a finite sum), then v ≤ 0 everywhere. -/
lemma maximum_principle {G ι : Type*} [Fintype ι] {v} (hb : BddAbove (.range v)) {l} (a :
  ι → ℂ) (r : G → ι → G) (hl : ∑ i, ‖a i‖ < l) (h : ∀ g, l * v g ≤ ∑ i, ‖a i‖ * v (r g i)) g : v g ≤
  0 := by nlinarith [le_ciSup hb g, Real.mul_iSup_of_nonneg (hl.le.trans' (by positivity)) v ▸
  @ciSup_le _ _ _ ⟨g⟩ _ _ (by grw [h ·, le_ciSup hb, ← sum_mul])]

variable {E n m W Z : Type} [Field E] [CMType E] [Fintype n] [Fintype m] {w} [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Z] [Module ℂ Z] {π : Representation ℂ (Gf E n) W} {a b : AutChar E} {k}
  (hk : card m = card n + k) (ha : CharUnramifiedAt a.baseChange.finPart w) (hb :
  CharUnramifiedAt b.baseChange.finPart w) (hw : w.IsSplit)

lemma FinPlace.q_eq_sqrt_sq : (w.q : ℂ) = √w.q ^ 2 := mod_cast by simp

lemma CharUnramifiedAt.apply_locFullIdele {χ} (h : CharUnramifiedAt (finPart χ) w) x :
  χ.1 (locFullIdele w x) =
  χ.atUnif w ^ (-(v x.1).log) := by simpa using! congr($(h.apply_locIdele_eq_zpow x).1)

lemma heckePolyOp_eq_sum {v} (hv : v ∈ sphericalAt π w) X : heckePolyOp π hw X v = ∑ U,
  heckePolyCoeff X U • π (atSplit hw (transposeGL (basicCosetRep U))) v ∧
  heckePolyOp π hw.star X v = ∑ U, heckePolyCoeff X U • π (atSplit hw (basicCosetRep U)⁻¹)
  v := by simp [heckePolyOp, heckePolyEval, ↓← mem_sphericalAt_iff, heckeSplit_star, *,
  heckeFun_basicDoubleCoset_inv, heckeSplit.eq_1 _ hw, heckeGL_eq_sum, sum_filter, smul_sum,
  sum_comm, heckePolyCoeff, card_ResField, le_card_of_mem_basicDoubleCoset (basicCosetRep_spec _).1]

@[simp] lemma HeckeChar.norm_atUnif (χ : HeckeChar E) w : ‖χ.atUnif w‖ = 1 := Circle.norm_coe _

/-- At a split place w of norm q, a vector fixed by the finite adelic unitary group of rank n is
spherical, and the Hecke polynomial acts on it by ∏_{l<n}(1 − q^l X). -/
lemma isSphericalWith_trivialHecke {v} (hv : ∀ g, π g v = v) : IsSphericalWith π hw
  (trivialHecke w.q (card n)) v := by simp [IsSphericalWith, heckePolyOp_eq_sum, *,
  ← sum_smul, by simpa [card_ResField] using q_binomial_submodule n (ResField w) ⊤]

include ha hw

lemma CharUnramifiedAt.det_maxCompactAt_eq_one {g s} (hg : g ∈ maxCompactAt n w) :
  a.1 (detFin s g) = 1 := by ext; erw [det_of_supportedOn, detOn_eq_prod, prod_singleton,
  ha.apply_locFullIdele] <;> simp_all [mem_intGL_iff_det.1 (mem_Kf_iff.1 ..)]


variable [WeilData E] {s t} {S : Space E n s} {T : Space E m t} {f p}
  (hf : (S.hom T).projOn {w} f = f)
include hb hf

/-- Let w be split, f vacuum at w, a, b unramified there. The Hecke sum at X of U(T), or U(S),
sends f to f named at w by `trivialHecke`(d − rk(x mod w), νX) on integral x; (d, ν) = (m,
a.frobValue n w), or (n, b.frobValue m w) (`AutChar.frobValue`). -/
lemma sum_heckePolyCoeff_smul_pairWeil X : let N d c :=
    (name _ {w} (residueDatum (fun _ ↦ w) fun x ↦ trivialHecke w.q (d - (x ()).rank)
    (X * c)) f); ∑ U, heckePolyCoeff X U • pairWeil S T a b ((1, 1), 1, atSplit hw (transposeGL
    (basicCosetRep U))) f = N (card m) (a.frobValue n w) ∧ ∑ U, heckePolyCoeff X U • pairWeil S T a
    b ((1, atSplit hw (basicCosetRep U)⁻¹), 1, 1) f = N (card n) (b.frobValue m w) := by
  nth_rw 2 3 [← hf]
  simp (disch := simp [*]) only [← name_boxIndicator, pairWeil_name_on, smul_name,
    ← _root_.sum_apply, ← map_sum, ← coe_singleton, detOn_eq_prod, frobValue, AutChar.spaceChar]
  constructor <;> congr with <;> simp [*, apply_locFullIdele, atUnif, ideleAbs_locFullIdele,
    charUnramifiedAt_upsilon, norm_locField_eq_q_zpow, basicCosetRep_spec, (basicCosetRep_spec
    _).1.2, -coe_units_inv, Real.sqrt_eq_rpow, ← Real.rpow_pow_comm, mem_integralBox,
    Real.inv_rpow, idem_mul_mem_Ô, ← evalAt_apply, matToVec, RingHom.map_matrix_mul, ite_and,
    ← transpose_apply (_ * Matrix.map _ _), -transpose_apply, @forall_comm m, ← card_ResField,
    residueDatum, v_mul_inv_le_one_iff
    (basicCosetRep_spec _).1, -rank_transpose, -mulVecLin_transpose, sum_filter, ↓card_sub_rank,
    ← rank_transpose (.map _ _), ← q_binomial_submodule, atSplit, Gf.atPlace, evalAt_star_locGL,
    ← GeneralLinearGroup.val_map_apply, -Units.coe_star] <;> congr! 3 <;> ring

include hk

/-- Hecke transfer: w split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, Λ
linear, Λ(ω(g,h)f) = π(g)ρ(h)Λf for finite g, h. Then Λf is K_w-fixed for π and ρ, and
P_w^ρ(X)Λf = ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·P_{w̄}^π(q^{k/2}χ_Sχ_T⁻¹(w)X)Λf.

Known result: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation. -/
lemma hecke_transfer_of_equivariant (Λ : _ →ₗ[ℂ] W) π ρ (hΛ : ∀ g h,
  Λ (pairWeil S T a b ((1, g), 1, h) f) = π g (ρ h (Λ f))) : Λ f ∈ sphericalAt π w ∧
  Λ f ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (Λ f) = trivialHecke w.q k (a.frobValue n w * X) •
  heckePolyOp π hw.star (w.q ^ k * a.frobValue n w / b.frobValue m w * X) (Λ f) := by
  simp [heckePolyOp_eq_sum, *, -hΛ, -map_inv, -map_smul, ← by simpa using And.intro (hΛ · 1) (hΛ 1),
    ← Prod.mk_one_one, pairWeil_eq_smul_of_projOn_eq {w}, det_maxCompactAt_eq_one _
    hw, -LinearMap.map_smulₛₗ, ← map_sum, sum_heckePolyCoeff_smul_pairWeil, smul_name,
    ← LinearMap.map_smul_of_tower]
  congr!
  simp [funext_iff, residueDatum, add_comm, prod_range_add, Nat.add_sub_assoc, rank_le_card_width]
  congr! 4 <;> simp [frobValue, atUnif, field, pow_add]

/-- Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, B bilinear,
ρ(h)B(f,v) = B(ω(g,h)f, π(g)v) for finite g, h, and v K_w-fixed. Then B(f,v) is K_w-fixed
and P_w^ρ(X)B(f,v) = ∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·B(f, P_w^π(q^{k/2}χ_Sχ_T⁻¹(w)X)v). -/
lemma hecke_transfer_of_pairing {ρ} {M : Submodule ℂ _} (B : M →ₗ[ℂ] W →ₗ[ℂ] Z) o (hB : ∀ g h v,
  ∃ Ψ, Ψ.1 = pairWeil S T a b ((1, g), 1, h) f ∧ ρ h (B ⟨f, o⟩ v) = B Ψ (π g v)) {v} (hv :
  v ∈ sphericalAt π w) : B ⟨f, o⟩ v ∈ sphericalAt ρ w ∧ ∀ X, heckePolyOp ρ hw X (B ⟨f, o⟩ v) =
  trivialHecke w.q k (a.frobValue n w * X) • B ⟨f, o⟩ (heckePolyOp π hw
  (w.q ^ k * a.frobValue n w / b.frobValue m w * X) v) := by
  obtain ⟨B, ⟨⟩⟩ := B.exists_extend
  have ⟨h, K, H⟩ := hecke_transfer_of_equivariant hk ha hb hw hf B (π.linHom 1) (.linHom 1 ρ)
    (by simp [DFunLike.ext_iff, by simpa using hB ·])
  use (congr($(K ·) v)), (by erw [← map_heckePolyOp (.applyₗ v) _ ?_, H ·,
    heckePolyOp_adjoint _ .applyₗ hv h] <;> simp)

/-- Let w be split, ranks n of S, n + k of T, a, b unramified and f the vacuum at w, f an arrow
e → e' (`IsArrow`). If y is spherical at w with Hecke eigenvalue p(X), so is its lift, with
∏_{l<k}(1 − q^{l+n/2}χ_S(w)X)·p(q^{k/2}χ_Sχ_T⁻¹(w)X). -/
lemma isSphericalWith_formLift {e e' y} (A : IsArrow (pairThetaKer S T a b) e e' f) (h :
  IsSphericalWith (S.formRep e) hw p y) : IsSphericalWith (T.formRep e') hw (fun X ↦ trivialHecke
  w.q k (a.frobValue n w * X) * p (w.q ^ k * a.frobValue n w / b.frobValue m w * X)) (formLift
  (pairThetaKer S T a b) e _ f y) := (hecke_transfer_of_pairing hk ha hb hw hf (.domRestrict _ ⊤) ⟨⟩
  (by simp [← A.formRep_formLift]) h.1).imp_right (by simp [h.2, mul_smul])
end

section
/-! Part of: Siegel–Weil formula in the convergent range (known result; see
Lib.SiegelWeil.Formula.SiegelWeilFormula).

Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski theorems
(known result; see Lib.Adelic.Reduction.Defs).

This file: Invariant functional small against the positive Eisenstein series vanishes, by one Hecke
operator. Normal form, Siegel sets and uniform convergence of the Siegel Eisenstein series. -/

open Finset Matrix Real Fintype ComplexOrder WeilData Space Splitting AutChar HeckeChar Lagrangian G
  Complex

/-- Let S ≠ 0 be split, rk T > rk S, ∑_L|ev_L f| finite for each f (L Lagrangian). A continuous
U(T)(𝔸)-invariant functional ℓ vanishes if, for each f, |ℓ(ω(g)f)| − ∑_L|ev_L ω(g)vac| is
bounded above for g in U(S)(𝔸). -/
lemma eq_zero_of_le_tsum_zeroTerm {E n m p} [Field E] [CMType E] {s t} [WeilData E] [Fintype n]
  [Fintype m] {S : Space E n s} {T : Space E m t} [Fintype p] [Nonempty n] (D : CompleteSplitting S
  p) (hm : 2 * card p < card m) {ℓ : _ →L[ℂ] ℂ} (hℓ : ∀ h f, ℓ (splitWeil S T (1, h) f) = ℓ f) (hs :
  ∀ f, Summable (‖Lagrangian.zeroTerm (S := S) T · f‖)) (hB : ∀ f,
  BddAbove (.range fun g ↦ ‖ℓ (splitWeil S T (g, 1) f)‖ - ∑' L, ‖Lagrangian.zeroTerm T L (splitWeil
  S T (g, 1) (vacElem _))‖)) {f} : ℓ f = 0 := ext_integrated _ (projOn_empty ..) fun P z _ ↦ by
  obtain ⟨⟨k, k0, hk⟩, hs, w, hw, hf⟩ := lt_iff_exists_add.1 hm, (hs · |>.hasSum.mul_left),
    ((frequently_prime_q.mono fun _ ↦ isSplit_of_q_prime).and_eventually (.all fun i ↦
    (z i).2.and (star_injective.tendsto_cofinite.eventually (z i).2))).exists
  have K {f} hf {ℓ : _ →L[ℂ] ℂ} (hℓ : ∀ h f, ℓ (splitWeil S T (1, h) f) = ℓ f) := by
    choose h _ H using hecke_transfer_of_equivariant (f :=
      f) (by simpa [D.card_eq]) ((hasWeight_upsilonU1_pow (card n / 2)).charUnramifiedAt rfl rfl)
      (HasWeight.one.charUnramifiedAt rfl rfl) hw hf (.pi fun g ↦
      (ℓ ∘L splitWeil S T (g, 1)).1) (finRightRep ..) 1 fun x h ↦
      funext fun g ↦ .trans (by simp [splitWeil, rep_apply_apply]) (hℓ h _)
    simpa [(isSphericalWith_trivialHecke ..).2, ↓heckePolyOp_eq_sum hw h, frobValue,
      AutChar.spaceChar, ← pow_mul, atUnif, finPart,
      D.card_eq, mul_sum, ← mul_assoc, -Prod.forall, -map_inv] using (congr(‖$(H (-1)) ·‖))
  refine by_contra fun c ↦ (congr(‖$((hℓ ..).trans ((ℓ.map_smul ..).trans (div_mul_cancel₀ _
    c)))‖).trans_gt (NormedField.exists_lt_norm ..).choose_spec).not_ge (sub_nonpos.1
    (maximum_principle (hB _) _ _ ?_ (fun g ↦ (by simpa only [mul_sub, sum_sub_distrib] using id :
    _ → _) (sub_le_sub ((K (by rw [map_smul, projOn_integrated, projOn_finHeisOp, boxIndicator,
    ite_eq_left] <;> simp [mem_integralBox, idem_mul_mem_Ô, star_eq_iff_star_eq]; simpa
      using! hf) hℓ
    g).trans_le (norm_sum_le_of_le _ fun _ _ ↦ norm_mul_le ..)) (hasSum_le (fun L ↦ (K (by simp)
    (by simp [Lagrangian.zeroTerm, mixedValue_splitWeil]) g).trans_ge ?_) (hasSum_sum fun _ _ ↦
    hs ..) (hs ..)))) _))
  · have h : 1 < √w.q := by simp [lt_sqrt]
    have := q_binomial_submodule n (ResField w) ⊤ (-√w.q ^ k)
    simp [heckePolyCoeff, w.q_eq_sqrt_sq, -mul_self_sqrt, sq, pow_add, ← div_div, ← div_pow, *,
      D.card_eq, mul_assoc, ← mul_sum, card_ResField] at this ⊢
    norm_cast at *
    simp (disch := positivity) only [*, norm_of_nonneg, two_mul, add_right_comm,
      prod_range_add, ← prod_mul_distrib, mul_comm _ ((range k).prod _), mul_assoc]
    apply mul_lt_mul' (by congr!; ring) (prod_lt_prod_of_nonempty₀ _ (fun j _ ↦ by
      linear_combination _ ^ (2 * j) * mul_add_mul_lt_mul_add_mul (pow_lt_pow_right₀ h k0)
        (hk ▸ one_lt_pow₀ h hm.ne_bot)) ⟨0, by simpa using card_pos.trans_eq D.card_eq⟩)
      <;> intros <;> positivity
  simp [↓fun u ↦ (by rewrite [← Prod.mk_one_mul_mk_one, pairWeil_apply, G.onHom.map_mul,
    ← rep_apply_apply, ← projOn_vacElem (S := {w}), ← name_boxIndicator, show G.onHom (_, 1) =
    _ from onHom_fin .., ω_name_on, map_smul, map_smul, map_smul, ← mul_inv_cancel_left _ (G.onHom
    (g, _)), ← rep_apply_apply] <;> (try erw [RingHom.map_mul, ← Circle.coe_inv_eq_conj, (omega_name
    ..).2, (θ _).comp_apply, sourceTerm_zero, ← mixedTerm_zero, ← mulVec_zero (1 : GL _ _).1⁻¹ᴴ,
    ← finVec_zero, (exists_isAdapted_and_frame_eq ..).choose_spec.1.omega_name_of_isMixedLaw
    isMixedLaw_mixedTerm _ _ _ ((IsSchwartzBruhat.comp_mulVec _).comp_mulVec _),
    (name ..).pi_apply_eq_sum_univ, sum_unique, sliceDatum,
    eq_coe_norm_of_nonneg (MeasureTheory.integral_nonneg _)]) <;> simp [*, ite_nonneg, Pi.le_def] :
    L.zeroTerm T (splitWeil S T (g * (1, atSplit hw u), 1) (vacElem _)) = _), ← coe_singleton,
    detOn_eq_prod, (charUnramifiedAt_upsilon _).apply_locFullIdele, (basicCosetRep_spec _).1.2,
    mul_pow, mul_assoc, ← mul_sum, atUnif, finPart, div_pow, det_kronecker', _root_.zpow_mul]
  field_simp; simp [← sum_mul, mul_div_right_comm]; norm_cast
  gcongr; rw [mul_comm]; apply le_norm_self

attribute [-simp] Matrix.coe_units_inv

open ENNReal Set MonoidHom Int Classical Subsingleton
variable {E n m p} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] [Fintype p] {s t}
  {S : Space E n s} (T : Space E m t) (P : CompleteSplitting S p)

attribute [local simp] radicalElt_mul_kAdelic levi_mul_kAdelic Matrix.mul_assoc _root_.zpow_add
  dyadicDiag mul_assoc

@[local simp] lemma radicalElt_eq_conj_levi a b : P.radicalElt 0 (a.1 * (b * a.1ᴴ)) =
    MulAut.conj (P.levi (a, 1)) (P.radicalElt 0 b) := by simp [↓P.levi_conj_radicalElt]

attribute [local simp↓ ←] radicalElt_zero_mul Matrix.map_mul

lemma exists_compact_parabolic_normal_form : ∃ Ω, IsCompact Ω ∧ ∀ g γ, ∃ δ x y ν,
  (ν, P.levi (dyadicDiag x, 1) * (radicalElt P 0 ν)⁻¹ *
  S.ratEmbed δ⁻¹ * g) ∈ Ω ∧ P.ActsOnFrame (S.ratEmbed (δ⁻¹ * γ)) ((y : GL p E).map toAdele).1 := by
  obtain ⟨⟨N, hN, H⟩, M, _, hM, h⟩ := IsCovolOneLattice.exists_compact_cover (ratMatrices E p p),
    exists_isCompact_profileBases E p
  exact ⟨_, hN.prod (isCompact_maxCompact.mul (hM.image_auto (P.levi ⟨·, 1⟩) (by
    simp [↓continuous_iff, Splitting.levi]; fun_prop))).inv, fun g γ ↦
    (P.iwasawa ((S.ratEmbed γ)⁻¹ * g)).elim fun κ ⟨hκ, a, _, _, c, z, u, e⟩ ↦
    (h a).elim fun x ⟨y, hy, _⟩ ↦ let a := y⁻¹.map toAdele; (H (a * z * a.1ᴴ)).elim fun r ⟨hr, hb⟩ ↦
      (mul_mem (P.radicalElt_mem_Gamma 0 hr) (P.levi_mem_Γ y⁻¹ ⟨1,
    rfl⟩)).elim fun δ hδ ↦ ⟨γ * δ⁻¹, x, y⁻¹, _, ⟨hb, _, hκ, _, ⟨_, hy, rfl⟩, by simp [*, a, eq_zero
      c, eq_mul_inv_of_mul_eq e, ← inl_apply, eq_one u]⟩, by simp [*, ← (mat _).mul_assoc]⟩⟩

/-- Siegel-set decomposition for split S: there is a compact Ω such that every adelic g equals γ
· levi(diag(2^{x_i})) · κ with γ rational, x ∈ ℕ^p and κ ∈ Ω, where 2 is the archimedean
idele. -/
lemma exists_siegel_set : ∃ Ω, IsCompact Ω ∧ ∀ g, ∃ γ, ∃ x : p → ℕ, ∃ κ ∈ Ω,
    g = S.ratEmbed γ * P.levi (dyadicDiag (x ·), 1) * κ := by
  obtain ⟨⟨Ω, hΩ, h⟩, F, C, hF, hC, H⟩ := exists_compact_parabolic_normal_form P, exists_finite_gram
    ((toFinite {stdForm E s}).preimage Units.val_injective.injOn).isCompact
  choose! r hr using fun T (_ : T ∈ F) ↦
    @id (∃ R : Matrix n p E, HasLeftInv (diagonal T.1 * R) ∧ Rᴴ * T.2 * R = 0)
  choose c k using fun i ↦
    exists_eq_zero_of_zpow_mul_mem (hF.isCompact_biUnion fun T _ ↦ isCompact_iUnion ((hΩ.prod
    hC).image_auto fun (κ, A) ↦ (P.kCoord * κ.2.mat * A.2 * (r T).map toAdele) i ·))
  refine ⟨_, ((isCompact_closedBall_prod_integral (E := E)).matrix.prod hΩ).image_auto
    fun (a, b, κ) ↦ P.radicalElt 0 (a * b * aᴴ) * ((P.levi (dyadicDiag (-c), 1))⁻¹ * κ),
    fun g ↦ (H S.isUnit_J.unit _ (S.move g).gram_point).elim fun Y ⟨d, i, z, m⟩ ↦ ?_⟩
  set W := (star Y * _)⁻¹
  have ⟨γ, hγ⟩ := exists_isometry_orthogonal P ⟨_, congr(submatrix $Y.inv_val _ _).trans
    (submatrix_one _ (by simp))⟩ (funext₂ i)
  have u : diagonal d * (⅟W.1 * (γ.1.1 * P.k)) = _ := Matrix.ext fun i j ↦ (diagonal_mul ..).trans
    (mul_left_eq_self₀.2 (or_not.imp_right (congrFun₂ hγ ⟨i, ·⟩ j)))
  have q := hr _ m ⟨_, ⟨_, by rw [Matrix.mul_assoc _ W.1, u, Matrix.mul_invOf_cancel_left,
    U.gram_invariant, P.gram_lk]⟩, by erw [← gram_mul, W.1.mul_assoc, u,
    Matrix.mul_invOf_cancel_left, U.gram_invariant, P.gram_kk]⟩
  have ⟨a, ha⟩ := S.witt ⟨_, P.gram_lk⟩ (q.1.imp' (· * W.1⁻¹) (by simp))
    (P.gram_kk.trans ((gram_mul ..).trans q.2).symm)
  choose δ x y ν hκ hy using h g a
  choose t ht using fun i ↦ le.dest (le_neg.1 (not_lt.1 (y.det_ne_zero <| det_eq_zero_of_row_eq_zero
    i fun j ↦ k i (-x i) · (mem_biUnion m ⟨_, ⟨j, rfl⟩, (_, _), ⟨hκ, z⟩, by
    simp [move, mat.eq_1 g, radicalElt_inv] at ha hy ⊢
    erw [← ha, ← S.ratMap_mul_toAdele S, hy]; simp [← Matrix.mul_assoc]⟩))))
  exact ⟨δ, t, _, ⟨(_, _), ⟨dyadicDiag_inv_mem t, hκ⟩, rfl⟩, by
    simp [← inl_apply, ← ht, ← Pi.mul_def]⟩

/-- If rk T > 2p, there is a summable function c on the Lagrangians L of the split space S bounding,
uniformly in x, the operator norm of the zero term ev_L composed with the operator `normalisedTorus`
T P x. -/
lemma exists_summable_zeroTerm_bound (hm : 2 * card p < card m) :
    ∃ c, Summable c ∧ ∀ x L, ‖Lagrangian.zeroTerm T L ∘L normalisedTorus T P x‖ ≤ c L := by
  obtain ⟨⟨Ω, hΩ, h⟩, N, hN, H⟩ := exists_compact_parabolic_normal_form P,
    IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  choose γ hγ using fun L : Lagrangian S ↦
    exists_isometry_orthogonal P ⟨_, gram_lk _⟩ L.completeSplitting.1.2.gram_kk
  choose δ x y ν hκ e₁ using (h 1 <| γ ·)
  choose d hd using fun j ↦ exists_eq_zero_of_zpow_mul_mem (isCompact_iUnion (hΩ.image_auto fun κ ↦
    (S.x.1 * κ.2⁻¹.mat * P.kAdelic) · j))
  choose t ht using fun L j ↦ le.dest (not_lt.1 ((congrFun₂ ((U.gram_invariant (δ L) ..).trans
    P.gram_lk) j j).trans_ne (by simp) <| sum_eq_zero fun i _ ↦ mul_eq_zero_of_right _ <|
    hd j (x L j) · ⟨_, ⟨i, rfl⟩, _, hκ L, by
    simp [← (mat _).mul_assoc, ← map_inv, mat_ratEmbed]
    simp [kAdelic, ← Matrix.mul_assoc, mul_comm]⟩))
  let K := Subtype.mk _
    ((hN.image_auto (P.radicalElt 0)).mul (hΩ.image_auto ((P.levi (dyadicDiag d, 1))⁻¹ * ·.2)))
  obtain ⟨⟨R, hR⟩, ⟨F, hF⟩, C, hC, hB⟩ := exists_zeroTerm_normalisedTorus_le T P P P.kCoord
    (by simp) K.2, (tendsto_coe_cofinite_of_isDiscrete S.ratEmbed_injective
      ⟨S.discreteTopology_Gamma⟩
    (K.2.inv.mul K.2).compl_mem_cocompact).exists_encard_eq_coe,
    encard_hermitian_le (((isCompact_closedBall_prod_integral (E := E)).matrix.prod
    (hN.prod hΩ)).image_auto fun (a, u, v, _) ↦ a * (u + uᴴ) * aᴴ - (v + vᴴ))
  simp [ratMatrices, -Subtype.forall, kAdelic, -map_inv, mat_ratEmbed, coe_units_inv, ← ht,
    inv_mul_eq_iff_eq_mul_of_invertible,
    (map_injective (@toAdele E ..).injective).eq_iff] at H e₁ hκ
  choose b hc using fun L ↦ H ((dyadicDiag (t L ·)).1 * ν L * (dyadicDiag (t L ·)).1ᴴ)
  let Q L γ :=
    P.radicalElt 0 ((b L).map toAdele) * P.levi (dyadicDiag (t L ·), 1) * S.ratEmbed γ⁻¹ ∈ K.1
  have E₁ L : Q L (δ L) :=
    ⟨_, ⟨_, hc L, rfl⟩, _, ⟨_, hκ L, rfl⟩, by simp [← inl_apply, -coe_diagGL, ← Pi.mul_def]⟩
  have k L : CompleteSplitting.lagrangian ((isometrySplitting (δ L)).comp P) = L :=
    eq_of_le fun _ ⟨x, h⟩ ↦ (L.2 _).2 (L.completeSplitting.2 ▸ forall_colSpan_dot_eq_zero_iff.2
    (by simpa [← h, Splitting.comp, isometrySplitting, e₁] using congr($(hγ L) *ᵥ (y L)⁻¹.1 *ᵥ _)))
  have hB x : (t ⁻¹' {x}).encard.toENNReal ≤ _ := (mul_le_mul_left (hB (x ·)) F).trans' (mod_cast
    hF ▸ encard_prod ▸ encard_le_encard_of_injOn (f := fun L ↦ (b L + (b L)ᴴ, epsilon (Q L) * (δ
    L)⁻¹)) (fun L l ↦ ⟨⟨by simp [add_comm], (_, _, _), ⟨dyadicDiag_inv_mem x, hc L, hκ L⟩, by
    ext <;> simp [l.symm, ← map_inv, add_sub_add_comm, mul_add, twoAtInfinity, field]⟩,
    (· ⟨_, inv_mem_inv.2 (epsilon_spec ⟨_, E₁ L⟩), _, E₁ L, by simp⟩)⟩) fun L l M m ↦
    by simp +contextual [Q, radicalElt, ← Matrix.map_add, l.trans m.symm, ← (k L).congr (k M)])
  refine ⟨_, summable_toReal (f := fun L ↦ R / ((2 ^ numInfPlaces E) ^ ∑ i, t L i) ^ card m)
    (ne_of_lt ?_), fun x L ↦ (_ ∘L _).opNorm_le_bound toReal_nonneg ?_⟩
  grw [← tsum_fiberwise _ t, tsum_congr fun z ↦ by rw [tsum_congr (by rw [·.2]), tsum_set_const],
    hB, tsum_congr (g := (C * F * R * ∏ i, (.ofReal (2 ^ (2 * card p) / 2 ^ card m)
    ^ numInfPlaces E) ^ · i)) fun t ↦ by simp [toNat_add, division_def,
             prod_pow_eq_pow_sum, ← mul_sum, ENNReal.inv_pow]; ring, ENNReal.tsum_mul_left,
    tsum_prod_le_prod_tsum]
  simp [mul_lt_top_iff, hC.lt_top, div_lt_one, pow_lt_one_iff, pow_lt_pow_right₀, *]
  simpa [norm_zeroTerm_parabolic_mul (levi_mul_kAdelic ..), norm_zeroTerm_parabolic_mul (a := 1),
    -dyadicDiag, zeroTerm_isometrySplitting, field, mul_comm, k L ▸ zeroTerm_lagrangian_eq_theta ..,
    zeroTerm_homSource_comp, ← zeroTerm_lagrangian_eq_theta, -θ_apply] using hR _ (E₁ L) x x rfl
end

section
/-! Known result: Siegel–Weil formula in the convergent range. Here a split space of rank 2p is
paired with a hermitian space of rank above 2p, both unimodular at every finite place, over a CM
field with the 5040th roots of unity. The Eisenstein series is a sum over Lagrangians, and the proof
uses one Hecke operator at a split place against the positive Eisenstein series. Source: A. Weil,
Sur la formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), n° 52 Thm 5;
method of proof after Andrianov (1979), Harris (1981), P. Garrett, The Siegel-Weil formula in the
convergent range (notes, 2005). -/

open Set Matrix MeasureTheory Filter Fintype Core Space Splitting Lagrangian Metric Subsingleton
  MatMul

/-- Siegel–Weil formula: for S split of rank 2p and rk T > 2p, the norms of the zero terms ev_L
are summable over the Lagrangians L of S, and for every f, h ↦ θ(ω(1,h)f) is integrable on
[U(T)] with mean ∑_L ev_L f.

Known result: Siegel–Weil formula in the convergent range. -/
lemma siegel_weil {E n m p} [Field E] [CMType E]
    [WeilData E] [Fintype n] [Fintype m] [Fintype p] {s t} {S : Space E n s} (T : Space E m t) (P :
  CompleteSplitting S p) (hm : 2 * card p < card m) : Summable (‖Lagrangian.zeroTerm (S :=
  S) T ·‖) ∧ ∀ f, Integrable (θ _ <| splitWeil S T ⟨1, ·⟩ f) T.quotMeasure ∧ ∫ h, θ _ (splitWeil S T
  (1, h) f) ∂T.quotMeasure = T.quotMeasure.real univ * tsum (Lagrangian.zeroTerm T · f) := by
  induction' h : card n using Nat.strongRec with _ IH generalizing n p
  obtain ⟨⟨N, mN, hN, B⟩, ⟨Ω, hΩ, H⟩, b, u, hB⟩ := theta_normalisedTorus_le T P hm,
    exists_siegel_set P, exists_summable_zeroTerm_bound T P hm
  have hs := u.of_nonneg_of_le (by simp) (normalisedTorus_zero T P ▸ hB 0)
  have i f : Integrable _ T.quotMeasure := ⟨by fun_prop, (lintegral_mono
    (normalisedTorus_zero T P ▸ B · 0 f)).trans_lt (lintegral_mul_const _ mN ▸ by finiteness)⟩
  have sm f : Summable (‖Lagrangian.zeroTerm T · f‖) := (hs.of_norm.mapL (.apply ℂ _ f)).norm
  refine let ℓ : _ →L[ℂ] ℂ := T.quotMeasure.real univ • _ - strongIntegral ..
    have hℓ f : ℓ f = _ - integral .. := congrArg₂ (_ * · - ·) (ContinuousLinearMap.map_tsum
      (.apply ℂ _ f) hs.of_norm) (strongIntegral_apply _ (θ _ ∘L splitWeil S T ⟨1, ·⟩) i f)
    ⟨hs, (⟨i ·, ?_⟩)⟩
  cases isEmpty_or_nonempty n
  simp [Lagrangian.zeroTerm, mixedValue, Splitting.zeroTerm_apply, pairWeil, eq_one (G.onHom _),
    eq_zero (_ + _), sum_subsingleton _ P.lagrangian]
  have key {C} (c : IsCompact C) ι : (atTop.comap (·.1 ι)).Tendsto (fun z : _ × C ↦ ℓ
    (normalisedTorus T P z.1 z.2.1)) (nhds 0) := by
    obtain ⟨⟨_, _, _, D₁, e⟩, ⟨R, hR⟩, Ω, hΩ, H⟩ := S.exists_splitting (.of_ne_zero (ne_of_apply_ne
      (_ ⬝ᵥ ·) (congr($P.gram_lk ι ι).trans_ne (by simp)))) congr(submatrix $P.gram_kk _ _),
      c.isBounded.exists_norm_le,
      IsCovolOneLattice.exists_compact_cover (_root_.ratVectors E (m × Unit))
    choose τ hσ using exists_lagrangian_equiv_containing T D₁
    let σ := τ.trans (.subtypeEquivRight fun _ ↦ by simp [range_mulVecLin, range_unique, e]; rfl)
    have D₂ := (σ.symm ⟨P.lagrangian, _, mulVec_single_one ..⟩).completeSplitting.1.2
    choose _ I J using IH _ (h ▸ by simp [D₁.card_eq]) D₂ (by bound [P.card_eq, D₂.card_eq,
      D₁.card_eq]) rfl
    conv in ℓ _ => erw [hℓ, ← (sm _).of_norm.tsum_subtype_add_tsum_subtype_compl,
      mul_add, add_sub_right_comm, ← σ.tsum_eq, funext (hσ · _), ← J, ← integral_sub (I _) (i _)]
    let w : C(𝔸 E × G E t, _) := ⟨_, (hΩ.prod c).continuous_sSup (f := fun a y ↦ ‖ϱ _ ((a.2⁻¹.mat
      * T.dualFrame.2).kronecker D₁.lCoordᵀ *ᵥ a.1 • y.1) y.2 - y.2‖ₑ) (by fun_prop [kronecker,
      kroneckerMap])⟩
    refine .trans' (by simp) (Tendsto.add (EMetric.tendsto_nhds.2 fun _ _ ↦
      (mem_nhds_zero_finAdele_iff.1 ((tendsto_lintegral_filter_of_dominated_convergence (F :=
      fun a h ↦ N h * w (.swap a, h)) _ (.of_forall (by fun_prop)) (.of_forall fun _ ↦
      .of_forall fun _ ↦ mul_right_mono (sSup_le (forall_mem_image.2 fun _ y ↦ by grw
      [← ofReal_norm, norm_sub_le, (heisRep _).3, hR _ y.2]))) (by
      rw [lintegral_mul_const] <;> finiteness) ((ae_lt_top mN hN).mono fun _ _ ↦ Continuous.tendsto
      (by fun_prop (disch := order)) 0)).eventually_lt_const (by simpa [w, sSup_image])).curry_nhds
      ).elim fun M ⟨hM, k⟩ ↦ .mono (tendsto_comap ((summable_geometric_two.smul_const ↑M
      ).tendsto_atTop_zero (k 1 (by simp)))) fun (x, f) v ↦ (edist_zero_right _).trans_lt
      (v.trans_le' ((enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun h ↦ ?_))))
      (.const_mul _ (tendsto_tsum_of_dominated_convergence ((u.mul_right _).subtype _) (g := 0) (fun
      ⟨L, l⟩ ↦ ?_) (.of_forall fun z L ↦ hB _ L |> (_ ∘L _).le_of_opNorm_le_of_le <| hR _ z.2.2))))
    have : D₁.lCoord * (P.levi (dyadicDiag (x ·), 1)).mat = star (twoAtInfinity E ^ x ι)⁻¹.1 •
      D₁.lCoord := by ext1; simpa [dyadicDiag, ← map_inv, lCoord, kAdelic,
      e] using! congr($(P.lCoord_mul_mat (P.levi_mul_kAdelic (dyadicDiag (x ·)) 1)) ι _)
    rw [← (by simpa using D₁.sourceTerm_levi T _ 1 1 1 h 0 _ :
      _ = splitWeil _ T _ _), θ_apply, Splitting.zeroTerm_apply, ← edist_eq_enorm_sub]
    refine (convex_closedEBall ..).integral_mem isClosed_closedEBall (.of_forall fun q ↦ (((by
      simpa : (M : E) ≠ 0).isUnit.map toAdele).smul_bijective.2 q.out).elim fun b e ↦ (H b).elim
      fun c r ↦ .trans (.trans_eq' (B h x _) (.trans ?_ congr(edist $((isContPeriodic_along_k ..).2
      _ (nsmul_mem r.1 M) _) _))) (mul_right_mono (le_sSup ⟨(_, _), ⟨r.2, f.2⟩, congr(‖ϱ _ (_ *ᵥ
      $(show _ = star (twoAtInfinity E ^ x ι)⁻¹.1 • (M • c + q.out) by ext <;> simp [← e,
      twoAtInfinity, mul_add])) _ - _‖ₑ)⟩))) (isContPeriodic_along_k ..).integrable_out
    simp [-mulVec_add, normalisedTorus, varrho_pairWeil, -θ_apply, *, ← mul_sub, ← θ_ϱ, splitWeil,
      D₁.card_eq,
      ↓mulVec_smul, kronecker_mulVec_eq_matToVec, homSource_kAdelic, edist_eq_enorm_sub]; rfl
    obtain ⟨⟨_, D'⟩, rfl⟩ := L.completeSplitting
    choose Y hY hv using (reindex_equiv toLin').2.1.1
      (((D'.lᴴ * S.J).toLin'.domRestrict _).exists_extend_of_notMem l 0)
    use (exists_zeroTerm_normalisedTorus_le T P D' (Y.map toAdele * S.x.1) ?_
      isCompact_singleton).elim fun _ h ↦
      squeeze_zero_norm (fun x ↦ .trans ?_ ((h 1 rfl x.1 (indicator {ι}ᶜ x.1) ?_ _).trans (by
      grw [hR _ x.2.2]))) ?_ <;> simp [indicator, kAdelic, dyadicDiag, ← Finset.sum_sub_distrib,
      apply_ite, ite_sub, ← ext_iff, ← Matrix.mul_assoc, ← Matrix.map_mul,
      mul_apply.trans congr($hv _), by simpa [← ext_iff_mulVec] using (congr($hY ⟨_, ·, rfl⟩))]
    apply ((tendsto_pow_atTop hm.ne_bot).comp ((tendsto_pow_atTop_atTop_of_one_lt
      (mod_cast by simp)).comp tendsto_comap)).const_div_atTop
  refine (sub_eq_zero.1 (hℓ _ ▸ eq_zero_of_le_tsum_zeroTerm P hm ?_ sm fun f ↦ ?_)).symm
  intros; simpa [hℓ, Lagrangian.zeroTerm, mixedValue_splitWeil] using! thetaIntegral_pairWeil _ 1
  have c : Continuous (splitWeil S T ⟨·, 1⟩ f) := by fun_prop
  apply ((((Finite.pi' fun ι ↦ Nat.cofinite_eq_atTop.le (eventually_comap.1 (key (hΩ.image (.smul
    (.inv₀ (by fun_prop) (norm_zeroTerm_vacElem_pos T P · |>.ne')) c)) ι (closedBall_mem_nhds 0
    one_pos)))).image _).isCompact.mul hΩ).image (ℓ.2.comp c)).isBounded.exists_pos_norm_le.imp
  rintro B hB _ ⟨g, rfl⟩
  obtain ⟨γ, x, κ, k, ⟨⟩⟩ := H g
  refine (exists_lagrangian_equiv_containing T (isometrySplitting γ)).elim fun σ o ↦
    sub_le_iff_le_add'.2 (.trans' (by_contra fun h ↦ h
    ((hB.2 _ ⟨_, mul_mem_mul ⟨x, fun _ j ↦ h ?_, rfl⟩ k, rfl⟩).trans (by simp [tsum_nonneg]))) ?_)
  grw [← hB.1.le, ← (sm _).le_tsum (σ P.lagrangian) (by simp)]
  simpa [o, zeroTerm_isometrySplitting, normalisedTorus,
    norm_zeroTerm_parabolic_mul (levi_mul_kAdelic ..), rep_apply_apply, field,
    div_le_iff₀ (norm_zeroTerm_vacElem_pos ..), mul_assoc] using j ⟨x, _, κ, k, rfl⟩ rfl
  rw [hℓ, ← (σ.trans (.subtypeUnivEquiv (by simp [isometrySplitting, colSpan]))).tsum_eq]
  simp [hℓ, o, zeroTerm_isometrySplitting, rep_apply_apply, mul_assoc, splitWeil,
    (pairThetaKer ..).theta_rat_mul _ ⟨γ, rfl⟩]
end
