import Lib.Adelic.SphericalHecke
import Lib.GaloisRep.WeightParameter
import Lib.ClassField.JetChainRule
import Lib.Weil.EntireTheta
import New.Weil.DatumLevel

section
/-! Set-up used by: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular
forms.

This file: Two normalisations of the Hecke polynomial are reciprocal to each other. -/

lemma eval_heckePoly {E n} [Field E] [NumberField E] [Fintype n] (w : FinPlace E) t {x} (h :
  x ≠ 0) : (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t
  x⁻¹ := by erw [Polynomial.eval_finsetSum, Finset.mul_sum]; congr!; simp_all [pow_sub₀]; ring
end

section
/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Forms on a definite unitary group are algebraic modular forms; integrals become class
sums. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-simp] Fintype.card_pi

variable {E n} [Field E] [CMType E] [Fintype n] {κ}
  {e : NumberField.InfinitePlace E → ℤ} {l s} {V : Space E n s} [i : V.IsStd] {φ : AlgForm n κ e}
  (h : IsHCParam (n := n) κ e l) (ψ : AlgForm n κ e)

lemma isStd_signedSpace [StablyUnram E] (hs : s = 1) : (signedSpace E s).IsStd := ⟨hs, by aesop⟩

namespace Space

lemma algFormCoeff_algFormRep L a g : algFormCoeff s L (algFormRep κ e a φ) g =
  algFormCoeff s L φ (g * (1, a)) := by aesop

open Subgroup

/-- Let V be standard, F automorphic, and K an open subgroup of K₀. Then ∫_{Γ\G} F equals
[K₀:K]⁻¹ times the integral over Γ\G_f, with vol K = 1, of g ↦ ∫_{G_∞} F(x, g) dx. -/
lemma integral_eq_classIntegral_of_isLevel {F} (hF : V.IsAutomorphic F) {K} (o : IsLevel K) : ∫ g,
  F g ∂V.quotMeasure = (stdLevelIndex K : ℂ)⁻¹ * classIntegral stdRatPoints K (∫ x, F ⟨x, ·⟩) := by
  have ⟨a, b, L, k⟩ := hF; induction i
  simp [inf_of_le_left, integral_quotMeasure_eq_classSum b (by tauto) _ (o :=
    ⟨inf_le_of_right_le o.1, (isOpen_mono (H₂ := rightStab _) (show ∀ _ ∈ L.1, ∀ _, _ from
      (by simp [← k · · ⟨_, ·⟩])) L.2).inter o.2⟩) inf_le_left a,
    classIntegral, ← relIndex_inf_mul_relIndex, Rat.smul_def, o.1, field]

attribute [local simp] dsKernel algFormCoeff_apply realConv typeKernel gramForm_highestVector_self
  mul_assoc schur_orthogonality

/-- Let V be standard and φ an algebraic form of weight (κ, e) with open stabiliser under right
translation. For every linear functional L, the function g ↦ L(ḡ_∞⁻¹ φ(g_f)) on G
(`algFormCoeff`) is automorphic. -/
lemma isAutomorphic_algFormCoeff {L} : V.IsAutomorphic (algFormCoeff s L ψ) := i.std_induction
    ⟨L.continuous_on_pi.comp (.matrix_mulVec (by simp [weylRep, -Pi.inv_apply]; fun_prop)
    (isLocallyConstant_of_eventually_mul (OpenSubgroup.mem_nhds_one ⟨rightStab ψ.1,
  ψ.2.1⟩)).continuous.snd'), by
    rintro _ ⟨γ, rfl⟩ g; erw [algFormCoeff_apply, ψ.2.2]; simp [weightRep], ⟨_, ψ.2.1⟩, fun _ ↦
  (by simp [· _])⟩

lemma star_ofAlgForm (h : s = 1) x g : star (ofAlgForm l s φ (x, g)) = gramForm (φ.1 g)
    (conjWeylRep κ e x (highestVector κ l)) := by cases h; simp [← gramForm_conjWeylRep (e :=
  e) x⁻¹ (φ.1 _), conj_gramForm]

include h

/-- On a standard space, for l = 2λ the parameter of (κ, e), φ a smooth algebraic form and Φ
automorphic with Φ(x, g) = L_g(ρ(x)v⁺), L_g linear: ∫_{[G]} ΦF_φ = (dim ρ)⁻¹ ∫_{Γ\G_f}
L_g(φ(g)) dg, with F_φ = `ofAlgForm` and vol K₀ = 1. -/
lemma integral_mul_eq_classIntegral K [IsLevel K] {Φ} (hΦ : V.IsAutomorphic Φ) (L : _ →
  _ →ₗ[ℂ] ℂ) (H : ∀ x g, Φ (x, g) = L g (conjWeylRep κ e x (highestVector κ l))) : ∫ g,
  Φ g * ofAlgForm l s φ g ∂V.quotMeasure = (Fintype.card (WeylIndex n κ) * stdLevelIndex K :
  ℂ)⁻¹ * classIntegral stdRatPoints K fun g ↦ L g (φ.1 g) := by cases i.1; simp [H, h _,
  ↓integral_eq_classIntegral_of_isLevel (hΦ.map₂ (isAutomorphic_algFormCoeff φ) (· * ·)) ‹_›]

lemma isForm_ofAlgForm : V.IsForm (typeKernel l s) (ofAlgForm l s ψ) :=
  i.std_induction ⟨isAutomorphic_algFormCoeff ψ, ((stdSpace ..).isAutomorphic_algFormCoeff
  ψ).mem_rapidFunctions.2.bounded, by simp [funext_iff, h.prod_formalDegree, h _,
  ← h.gramForm_conjWeylRep_eq_dsCoeff, ← Complex.ofReal_prod]⟩

/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), the linear isomorphism F
↦ φ_F from forms of type e_l to smooth algebraic forms of weight (κ, e). -/
noncomputable def toAlgForm (V : Space E n s) [i : V.IsStd] (h : IsHCParam κ e l) :
  V.Form (typeKernel l s) ≃ₗ[ℂ] AlgForm n κ e := .symm (.ofBijective ((ofAlgForm ..).codRestrict _
  (isForm_ofAlgForm h)) (by exact i.std_induction ⟨(injective_iff_map_eq_zero _).2 fun φ z ↦ by
  ext; exact highestVector_cyclic (h · |>.1) e (.proj _) _ (.inl (inv_inv · ▸ congr($z.1 (_, _)))),
  fun ⟨y, ⟨c, r, K, k⟩, _, f⟩ ↦
  ⟨⟨fun g ↦ ∫ x, (Fintype.card (WeylIndex n κ) * y (x, g)) • conjWeylRep κ e x (highestVector κ l),
  isOpen_mono (H₁ := K.1) (H₂ := rightStab _) (fun a b g ↦ by simp [← k a b ⟨_, g⟩]) K.2,
  fun γ g ↦ ((MeasureTheory.integral_mul_left_eq_self
  ..).symm.trans (by simp [← r _ ⟨γ, rfl⟩ (_, g)]; rfl)).trans ((weightRep κ e _
  γ).toContinuousLinearMap.integral_comp_comm integrable_of_compactSpace)⟩, Subtype.ext (.trans
  (funext fun ⟨x, g⟩ ↦ ((MeasureTheory.integral_mul_left_eq_self _ x).trans ((gramForm (n :=
  n) _ ∘ₗ conjWeylRep κ e _).toContinuousLinearMap.integral_comp_comm
  integrable_of_compactSpace)).symm.trans (by
    simp [h.prod_formalDegree, h.gramForm_conjWeylRep_eq_dsCoeff, ← Complex.ofReal_prod]; ac_rfl))
  (f integrable_of_compactSpace))⟩⟩))

lemma ofAlgForm_toAlgForm y : ofAlgForm l s (V.toAlgForm h y) = y := congr($((V.toAlgForm h).3 y))

/-- The isomorphism `Space.toAlgForm` from forms of type e_l to smooth algebraic forms of weight
(κ, e) commutes with right translation by G_f. -/
@[local simp] lemma toAlgForm_formRep a y : V.toAlgForm h (V.formRep _ a y) =
  algFormRep κ e a (V.toAlgForm h y) := (V.toAlgForm h).eq_symm_apply.1 (Subtype.ext
  ((funext (algFormCoeff_algFormRep _ _)).trans congr($(ofAlgForm_toAlgForm h y) ∘ _)).symm)

variable (V)

/-- For V standard, l twice the Harish-Chandra parameter of (κ, e) and K a subgroup of G_f, the
isomorphism φ ↦ F_φ from K-fixed algebraic forms to K-fixed forms of type e_l. -/
noncomputable def algFormEquiv K : levelSpace (algFormRep κ e) K ≃ₗ[ℂ] levelSpace (V.formRep
  (typeKernel l s)) K := (V.toAlgForm h).symm.ofSubmodules _ _ (by ext; simp [↓← toAlgForm_formRep])

/-- For V standard and l twice the Harish-Chandra parameter of (κ, e), a form y of type e_l is
spherical at w with Hecke polynomial p if and only if its algebraic form, as a function on
G_f, is. -/
lemma _root_.isSphericalWith_toAlgForm_iff [WeilData E] {y w p} {u : _ ≠ w} : IsSphericalWith
  (rightRegular ..) u p (V.toAlgForm h y).1 ↔ IsSphericalWith (V.formRep _) u p y := by
  simp [IsSphericalWith, ← (V.toAlgForm h).apply_eq_iff_eq, Subtype.ext_iff]; congr!
  exact (map_heckePolyOp ((AlgForm ..).subtype ∘ₗ (V.toAlgForm h).1) _ (by simp)).symm
end Space
end

section
/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: The Fischer pairing is preserved by an injective renaming of the variables. -/

/-- The jet pairing P(∂)F(0) of a polynomial P with a power series F over a commutative ring is
unchanged when both are renamed along an injective map of variables. -/
lemma jet_rename {σ τ R} (e : σ ↪ τ) [CommRing R] {P Q} (h : .rename e P = Q) F :
    jet R Q (F.rename e) = jet R P F := h ▸ P.induction_on' (by
  simp [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain, Finsupp.prod]) (by aesop)
end

section
/-! Part of: Theta lift for a definite unitary pair as a class sum on algebraic modular forms (known
result; see Lib.Weil.CompactLift.RallisFormula).

Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms (known
result; see Lib.Adelic.CuspForms.Petersson).

This file: Matrix of jets is an equivariant kernel for definite unitary theta lifts. Restriction
period of algebraic forms as class sum through the unique branching map. -/

noncomputable section

open NumberField Matrix MvPolynomial Space Finset GeneralLinearGroup G Fintype Subgroup

/-- The ranks satisfy |n| < |n′|, κ has no column of height strictly between them, and e_τ =
eb_τ + κ_τ(|n|), with κ_τ(h) the number of columns of height h at τ. -/
def IsLiftWeight {Φ} n n' [Fintype n] [Fintype n'] κ (eb e : Φ → ℤ) :=
  FitsRanks n n' κ ∧ card n < card n' ∧ e = fun τ ↦ eb τ + κ τ (card n)

variable {E n n'} [Field E] [CMType E] [WeilData E] [Fintype n]
  [Fintype n'] {s s'} {κ : InfinitePlace E → _} {eb e} (hκ : IsLiftWeight n n' κ eb e) (c)
  (f : 𝒮 ((stdSpace E n).hom (stdSpace E n'))) (V : Space E n s) (T : Space E n' s') (a b :
  AutChar E) (z ea x y) (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ)

/-- The bilinear map (A, ξ) ↦ Aᵀ S_κ(z) ξ, with values polynomials in the entries of the n′ × n
matrices z_τ. -/
def schurCoeffPoly := C ∘ A ⬝ᵥ schur κ (fun τ ↦ of fun b c ↦ X (τ, b, c)) *ᵥ C ∘ ξ

/-- The finite Heisenberg operator `Space.finHeisOp` of x, restricted to the finite part 𝒲_f of
𝒮(V). -/
@[simps! apply_coe] def Space.heisFinPart : Module.End ℂ V.finitePart := .restrict _ fun _ ↦
  finHeisOp_mem_finitePart x

/-- The representation of pairs (g, h) of finite adelic unitary elements on the finite part 𝒲_f
of Hom(V,T), by restriction of `pairWeil` with characters a, b. -/
@[simps! apply_apply_coe] def pairWeilFinite := MonoidHom.mk (N :=
  Module.End ℂ (V.hom T).finitePart) ⟨fun p ↦
  .restrict (pairWeil V T a b ((1, Prod.fst p), 1, p.2)) fun _ ↦ (finitePart _).smul_mem _ ∘ by
  rw [onHom_fin]; apply omega_mem_finitePart, by ext; simp⟩ (by intros; ext; simp [rep_apply_apply])

variable (n n' κ e) in
/-- An abstract theta kernel: a smooth representation ω of G × G' on data S and a linear map
from S to Hom(V, V') equivariant for the rational points Γ × Γ'. -/
structure Kernel (K : Subgroup (Gf E n)) S [AddCommGroup S] [Module ℂ S] where
  ω : Representation ℂ (Gf E n × Gf E n') S
  jetMatrix : S →ₗ[ℂ] (WeylIndex n κ → ℂ) →ₗ[ℂ] WeylIndex n' κ → ℂ
  equivariant γ δ Φ v : jetMatrix (ω (stdEmbFin γ, stdEmbFin δ) Φ) ((stdSpace ..).weightRep κ e γ
    v) = (stdSpace ..).weightRep κ ea δ (jetMatrix Φ v)
  isOpen_stab Φ : (rightStab (ω · Φ)).IsOpen

variable {a b ea K S} [AddCommGroup S] [Module ℂ S] (k : Kernel n n' κ e ea K S)

omit [WeilData E] in
@[local simp] lemma Kernel.ω_ω p q Φ : k.ω p (k.ω q Φ) = k.ω (p * q) Φ := by simp

omit [WeilData E] in
/-- For a datum Φ, a smooth form φ and h in G', the integrand g ↦ jetMatrix(ω(g,h)Φ)(φ(g)) of the
theta lift is left invariant under the rational points and has open stabiliser
under right translation. -/
@[simp] lemma Kernel.integrand_mem_smoothInvariants Φ (φ : AlgForm n κ e) h : (fun g ↦
  k.jetMatrix (k.ω (g, h) Φ) (φ.1 g)) ∈ smoothInvariants stdRatPoints :=
  ⟨fun _ ⟨γ, e⟩ g ↦ by simpa [← e, φ.2.2 _] using k.3 γ 1 (k.ω (g, h) Φ) _,
  (_ ⊓ comap (.inl ..) (rightStab (k.ω · Φ))).isOpen_mono (fun _ ↦ by
  simp_all [-map_mul]) (.and φ.2.1 ((k.4 Φ).preimage (.prodMk_left 1)))⟩

variable [IsLevel K]

/-- The theta lift with datum Φ: φ goes to the smooth form h ↦ ∫ jetMatrix(ω(g,h)Φ)(φ(g)) dg over
Γ\G, Γ the rational points, with vol K = 1. -/
def Kernel.lift : S →ₗ[ℂ] AlgForm n κ e →ₗ[ℂ] AlgForm n' κ ea := by
  apply LinearMap.mk₂ ℂ fun Φ φ ↦ ⟨fun h ↦ classIntegral stdRatPoints K fun g ↦
    k.jetMatrix (k.ω (g, h) Φ) (φ.1 g), (comap (.inr ..) (rightStab (k.ω · Φ))).isOpen_mono (fun _ ↦
    (by simp [← · ⟨_, ·⟩])) ((k.4 Φ).preimage (.prodMk_right 1)), fun γ h ↦ map_classIntegral
    (weightRep _ _ _ γ).toAddMonoidHom 1 (o := by simp [← k.3 1])⟩ <;> intros <;> ext :
    2 <;> simp [classIntegral_add, ← Pi.add_def] <;>
    exact map_classIntegral (DistribSMul.toAddMonoidHom _ _) 1

omit [WeilData E] in
/-- Equivariance of the theta lift: the lift with datum ω(a,b)Φ of the right translate of φ by a
is the right translate by b of the lift of φ with datum Φ. -/
lemma Kernel.lift_equivariant a b Φ φ : k.lift (k.ω (a, b) Φ) (algFormRep κ e a φ) =
    algFormRep _ _ b (k.lift Φ φ) := by ext : 2; exact map_classIntegral (.id _) a

lemma coe_map_conj_inv_eq_transpose (u : @USign n _ 1) : (u.1⁻¹.map (starRingEnd ℂ)).1 = uᵀ :=
  by erw [val_map_apply, U.coe_inv] <;> aesop

omit [WeilData E] in
lemma dotProduct_schurJet_mulVec F : A ⬝ᵥ schurJet κ F *ᵥ ξ = jet ℂ (schurCoeffPoly A ξ) F := by
  simp [schurCoeffPoly, schurJet, entrywise, C_mul', mul_comm]

include hκ

omit [WeilData E] in
lemma map_schurJet {R S} [CommRing R] [CommRing S] (i' : WeylIndex n' κ) (i : WeylIndex n κ) (φ :
  R →+* S) F :
  φ (schurJet κ F i' i) = schurJet κ (F.map φ) i' i := by simp [schurJet, map_jet, map_schur hκ.1]

omit [WeilData E] in
lemma eval_schurCoeffPoly z (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ) :
  eval z (schurCoeffPoly A ξ) = A ⬝ᵥ schur κ (fun τ ↦
  of (z ⟨τ, ·, ·⟩)) *ᵥ ξ := by simp [schurCoeffPoly, entrywise, map_schur hκ.1]

omit [WeilData E] in
/-- For definite signs and κ satisfying `IsLiftWeight`, the real Weil representation of weights ea,
eb at (x,y) sends the Fock vector of Aᵀ S_κ(z) ξ to that with A·conjWeylMatrix(y⁻¹) (twist ea) and
conjWeylRep(x)ξ (twist eb + `schurDetExp`) in place of A, ξ. -/
lemma realPairWeil_schurCoeffPoly {ea} x y (A : WeylIndex n' κ → ℂ) (ξ : WeylIndex n κ → ℂ) :
  realPairWeil (s := 1) (s' := 1) ea eb (x, y)
  (schurCoeffPoly A ξ) = schurCoeffPoly (A ᵥ* conjWeylMatrix κ ea y⁻¹) (conjWeylRep κ e x ξ) := by
  obtain ⟨⟨_, ⟨⟩⟩, h, l, ⟨⟩⟩ := inv_surjective x, id hκ; ext
  simp [-smul_mulVec, realPairWeil_polyVector, ↓aeval_def, ← eval_assoc, eval_schurCoeffPoly hκ,
    conjWeylRep, weylRep, -map_inv, mul_smul, coe_map_conj_inv_eq_transpose,
    Units.smul_def, -val_map_apply, _root_.zpow_add, -det_transpose,
    -map_smul, h, dotProduct_mulVec, ← by simpa [schurDetExp, l] using schur_mul_right h (R := ℂ)]
  simp [vecMul_smul, field, ← submatrix_id_id (_ * _), submatrix, mul_apply, mul_sum, mul_comm]

seal Finset.univ Finset.sum Finset.prod in
/-- Let κ satisfy `IsLiftWeight`. For f in 𝒮(Hom(I_n, I_n′)), the matrix of jets of the scaled
Taylor series T_c f along the Schur matrix S_κ(z) is c^L times that of T_1 f, L the number of boxes
of κ in columns of height below |n′|. -/
lemma schurJet_jetSeries_eq_smul : schurJet κ (jetSeries _ c f) =
  c ^ boxes κ (card n') • schurJet κ (jetSeries _ 1 f) := by
  ext; simp [schurJet, map_schur hκ.1, ← C_mul']
  erw [schur_smul hκ.1, prod_pow_eq_pow_sum]
  simp [C_eq_smul_one, smul_pow]; tauto

seal Finset.univ Finset.sum Finset.prod in
/-- The theta kernel of the definite pair I_n, I_{n′}: finite data 𝒲_f with action `pairWeilFinite`,
each f giving the matrix of jets of T_c f along S_κ. -/
def thetaKernel {ψ ψ'} (ha : a.HasWeight ea ψ) (hb : b.HasWeight eb ψ') K :=
  (⟨pairWeilFinite (stdSpace ..) (stdSpace ..) a b,
  toLin'.1 ∘ₗ schurJet κ ∘ₗ jetSeries _ c ∘ₗ (finitePart _).subtype, fun γ γ' f ↦ by simp [
  weightRep, conjWeylRep, ← dotProduct_eq_iff, @pairWeil_integrated_all E, embFin,
  schurJet_jetSeries_eq_smul hκ c, dotProduct_comm, dotProduct_mulVec, ↓dotProduct_schurJet_mulVec,
  realPairWeil_schurCoeffPoly hκ, -mulVec_mulVec, ← map_mul,
  ← by simpa using fun w ↦ pairWeil_of_mem_Gamma _ _ a b ⟨γ, rfl⟩ ⟨γ', rfl⟩ (integrated _ w f) 0],
  (exists_level_pairWeil a b ·.2 |>.elim fun K ⟨K', _⟩ ↦ isOpen_mono (by simp_all [LE.le, mem_prod,
  Subtype.ext_iff]) (K.prod K').2)⟩ : Kernel n n' κ e ea K _)

omit hκ

open MeasureTheory
variable {E ι'' X : Type} [Field E] [CMType E] [Fintype ι''] [Fintype X]

/-- Let V be standard and A satisfy `SpansBranchingMaps`. For t, c there is C such that, for smooth
ψ, automorphic Φ(x,g) = L_g(x·c) and open K ≤ K₀, ∫ Φ(h) ψ_t(diag(h,u)) dh is C/[K₀:K] times
the integral, for vol K = 1, of L_h(Aψ(diag(h,u))). -/
lemma integral_algFormCoeff_blockEmb {κ e κ₀ e₀ s} (V : Space E ι'' s) [i : V.IsStd] {σ} hσ {A}
  (hA : SpansBranchingMaps (fun _ ↦ σ) e₀ e A) t c : let j := G.blockEmb (s₂ := 1) (e := σ) hσ; ∃ C,
    ∀ (ψ : AlgForm X κ e) Φ u (L : _ → _ →ₗ[ℂ] ℂ) K [IsLevel K], V.IsAutomorphic Φ → (∀ x g, Φ (x,
    g) = L g (conjWeylRep κ₀ e₀ x c)) → ∫ h, Φ h * algFormCoeff 1 t ψ (j (h, 1, u)) ∂V.quotMeasure =
    C / K.relIndex (Kf ..) * classIntegral (stdSpace ..).embFin.range K fun h ↦
    L h (A *ᵥ ψ.1 (j ((1, h), 1, u)).2) := by
  induction i; intro j
  have ⟨B, hB, hI⟩ := exists_intertwining_mean volume (conjWeylMatrix κ₀ e₀)
    ((conjWeylMatrix κ e).comp (.comp (.fst ..)
    (j.comp (.prod (.inl ..) 1)))) (t.smulRight c).toMatrix' (by simp [weylRep]; fun_prop)
  peel hA B fun g hg ↦ ⟨_, by simp [← Matrix.ext_iff, ← G.mat_fst, j, G.blockEmb,
    PolyRep.blockScalar, reindex_equiv σ]; simp, (hB fun w ↦ ⟨(g
    w).map (starRingEnd _), by simpa [U] using! congr($(hg w)ᵀᴴ)⟩).trans (by simp; congr; bound)⟩
  introv h0 hΦ H
  rw [integral_eq_classIntegral_of_isLevel
    (hΦ.map₂ (have ⟨a, r, K', l⟩ := (stdSpace ..).isAutomorphic_algFormCoeff ψ
    ⟨by fun_prop, fun γ h g ↦ .trans (by simp [← map_mul]) (r (j (γ, 1)) (by simpa [j])
      _), K'.comap ((U.block σ).comp (.inl ..)) (by fun_prop : Continuous (j ⟨⟨1, ·⟩, 1⟩ |>.2)),
      fun k hk g ↦ .trans (by erw [← (Prod.mk.inj j.map_one).1, ← j.map_mul _ (k, 1)]; simp)
      (l _ hk _)⟩) (· * ·)) h0, eq_comm, div_eq_inv_mul, mul_assoc, ← classIntegral_const_mul]
  congr!
  simpa [*, mul_comm] using! (hI (L _ ∘ₗ Matrix.toLin'.1.flip _)).symm
end
end
