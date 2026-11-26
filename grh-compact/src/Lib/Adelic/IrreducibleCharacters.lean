import Lib.Adelic.Average

section
/-! General lemmas of group theory (textbook or folklore).

This file: Basic properties of characters and virtual characters of finite groups. -/


open ComplexConjugate Submodule AddChar LinearMap IsMulCommutative Classical Finset Fint Subgroup
variable {S} [CommSemiring S] [Algebra S ℂ] {G} [Group G] {χ ψ f : G → ℂ}

lemma IsChar.mul : IsChar χ → IsChar ψ → IsChar (χ * ψ) := by grind [IsChar, =_ FDRep.char_tensor]

lemma isChar_monoidHom (l : G →* ℂ) : IsChar l :=
  ⟨.of (.comp .smulOneHom l), funext (Algebra.trace_self_apply <| l ·)⟩

variable (S G) in
/-- For a group G and a commutative semiring S acting on ℂ, the S-subalgebra of functions G → ℂ
spanned over S by the characters of G. -/
def virtualChars := (span S {f | @IsChar G _ f}).toSubalgebra (subset_span (isChar_monoidHom 1))
  (BilinMap.apply_apply_mem_of_mem_span _ _ _ (.mul ..) fun _ a _ b ↦ subset_span (a.mul b))

/-- A function on a group G in the ℕ-span of the characters of G is itself a character. -/
lemma isChar_of_mem_virtualChars (h : f ∈ virtualChars ℕ G) : IsChar f := (span_nat_eq ⟨⟨IsChar,
  fun ⟨ρ, a⟩ ⟨σ, b⟩ ↦ ⟨.of (.prod ρ.ρ σ.ρ), a ▸ b ▸ by ext; apply trace_prodMap'⟩⟩,
  ⟨default, 1⟩, by ext; apply map_zero⟩).le h

variable [Finite G] (h : IsChar χ) (v : f ∈ _root_.virtualChars S G) {H} [Group H]
include h

section

omit [Finite G]

lemma IsChar.comp (p : H →* G) : IsChar (χ ∘ p) := h.imp' (.of <| ·.ρ.comp p) (by aesop)

/-- Every character of a group G lies in the S-span `virtualChars S G` of the characters of G. -/
lemma IsChar.mem_virtualChars : χ ∈ _root_.virtualChars S G := subset_span h

lemma IsChar.isClassFunction : IsClassFunction χ := h.rec (by aesop)

end

lemma IsChar.exists_finMean_eq_natCast : ∃ m : ℕ, finMean χ = m := h.rec fun ρ e ↦
  ⟨_, .trans (by simp [finMean, e, field]) ρ.average_char_eq_finrank_invariants⟩

lemma IsChar.exists_sum_addChar_zpowers (g : G) : ∃ m : AddChar (Additive (zpowers g)) ℂ → ℕ, ∀ u h,
  ∑ l, m l • l (.ofMul ⟨u, h⟩) = χ u := .imp (fun _ e ↦ by simp [← e, finMean, div_eq_inv_mul,
  sum_comm, sum_mul, mul_assoc, ← mul_sum, field, ← map_add_eq_mul, sum_apply_eq_ite,
  neg_add_eq_zero]) (skolem.1 fun l ↦ ((h.comp (zpowers g).subtype).mul
  (isChar_monoidHom (.toAdditive.2 l⁻¹.toAddMonoidHom))).exists_finMean_eq_natCast)

lemma IsChar.apply_inv g : χ g⁻¹ = conj (χ g) := by
  simp [← (h.exists_sum_addChar_zpowers g).choose_spec, ← map_neg_eq_conj]; rfl

lemma IsChar.isIntegral g : IsIntegral ℤ (χ g) :=
  (h.exists_sum_addChar_zpowers g).choose_spec g (by simp) ▸ .sum _
  fun l _ ↦ .nsmul (.of_pow (orderOf_pos l) (by simp [← pow_apply, isIntegral_one])) _

lemma IsChar.star : IsChar (conj <| χ ·) :=
  h.imp' (.of <| .dual ·.ρ) (by aesop (add simp apply_inv))

include v

lemma IsChar.exists_classInner_eq : ∃ m, classInner χ f =
  algebraMap S ℂ m := let ⟨_, a, ψ, e⟩ := mem_span_set'.1 v
  (skolem.1 (ψ · |>.2.mul h.star |>.exists_finMean_eq_natCast)).elim fun m u ↦ ⟨a ⬝ᵥ (m ·), by
                         simp [classInner, dotProduct, ← e, ← u, mul_sum, finMean_sum,
                           ← finMean_const_mul, Algebra.smul_def, mul_rotate']⟩

omit h

omit [Finite G] in
lemma comp_mem_virtualChars [Finite H] (p : H →* G) : f ∘ p ∈ virtualChars S H :=
  mapsTo_span (f := funLeft ..) (fun _ ↦ (·.comp p)) v

omit [Finite G] in
lemma isClassFunction_of_mem_virtualChars : IsClassFunction f := by induction v using
  span_induction <;> simp_all [IsChar.isClassFunction]
end

section
/-! General lemmas of group theory (textbook or folklore).

This file: Central idempotents of group algebras and their tensor products over product groups. -/

open Fint Function MonoidAlgebra Representation

variable {H} [Group H] {e : ℂ[H]} {V} [AddCommGroup V] [Module ℂ V] {ι} [Fintype ι] {G : ι → _}
  [∀ i, Group (G i)] [∀ i, Finite (G i)] {ρ : Representation ℂ (∀ i, G i) V} {x : ∀ i, ℂ[G i]}

lemma IsClassFunction.commute (h : IsClassFunction e.coeff) x :
    Commute x e := ext (by grind [coeff_mul_apply_left, coeff_mul_apply_right, mul_inv_cancel_left])

lemma asAlgebraHom_eq_sum (σ : Representation ℂ H V) {e : ℂ[H]} [Fintype H] :
    σ.asAlgebraHom e = ∑ s, e.coeff s • σ s := Finsupp.sum_fintype _ _ (by simp)

attribute [local simp] Finset.prod_boole Finset.prod_univ_sum Finsupp.single_apply
  Finsupp.sum_fintype coeff_mul_apply_left one_def

/-- e is a central idempotent of the complex group algebra of a group. -/
def IsCentralProj (e : ℂ[H]) := IsIdempotentElem e ∧ IsClassFunction e.coeff

/-- The multiplicative map sending (x_i), x_i in ℂ[G_i], to ⊗x_i in ℂ[∏G_i], whose coefficient
at (s_i) is the product of the coefficients x_i(s_i). -/
@[simps!] noncomputable def piTensorElem : (∀ i, ℂ[G i]) →* ℂ[∀ i, G i] :=
    ⟨⟨fun x ↦ groupAlgElem fun s ↦ ∏ i, (x i).coeff (s i), by aesop⟩, by aesop⟩

/-- For a complex representation ρ of a finite product ∏ G_j of finite groups and x in ℂ[G_i],
the pure tensor with x at i and 1 elsewhere acts as x acts in the restriction of ρ to the
factor G_i. -/
lemma asAlgebraHom_piTensorElem_mulSingle i x : ρ.asAlgebraHom (piTensorElem (Pi.mulSingle i x)) =
  asAlgebraHom (ρ.comp (.mulSingle G i)) x := by rw [asAlgebraHom_eq_sum, asAlgebraHom_eq_sum,
  Fintype.sum_of_injective _ (Pi.mulSingle_injective i)] <;> simp_all [Finset.prod_congr rfl,
  Fintype.prod_eq_mul_prod_compl i, Pi.mulSingle, update_eq_iff, -not_forall]

lemma piTensorElem_apply_eq_zero {v} i (h : asAlgebraHom (ρ.comp (.mulSingle G i)) (x i) v = 0) :
    ρ.asAlgebraHom (piTensorElem x) v = 0 := (by simpa [-one_def] using! update_mul x 1 i 1 (x i) :
  x = _ * Pi.mulSingle i _) ▸ by simp_all [asAlgebraHom_piTensorElem_mulSingle]

lemma piTensorElem_mul_eq_zero {y} i (h : x i * y i = 0) : piTensorElem x * piTensorElem
  y = 0 := by ext; simp [← map_mul, ↓Finset.prod_eq_zero (Finset.mem_univ i), *]

namespace IsCentralProj

lemma one_sub : IsCentralProj e → IsCentralProj (1 - e) := .imp .one_sub (by simp [eq_comm])

lemma map (h : IsCentralProj e) σ : IsCentralProj (mapRingHom H σ e) := h.imp (·.map _) (by aesop)

lemma piTensorElem (h : ∀ i, IsCentralProj (x i)) :
    IsCentralProj (_root_.piTensorElem x) := ⟨.map (funext (h · |>.1) :) _, by simp [(h _).2]⟩
end IsCentralProj
end

section
/-! General lemmas of group theory (textbook or folklore).

This file: Recognising irreducible and virtual characters by pairings; when a character's projector
vanishes. -/


open MonoidAlgebra Finset LinearMap ComplexConjugate Fint Matrix Algebra Representation Calc
variable {G H V} [Group G] [Finite G] [Group H] {χ f : G → ℂ} [AddCommGroup V] [Module ℂ V]
  [Module.Finite ℂ V] {ρ : Representation ℂ G V} (Z) [CommSemiring Z] [Algebra Z ℂ]
attribute [local simp] basis algebraMap_eq_smul_one div_eq_inv_mul finMean FDRep.character character
  asAlgebraHom_eq_sum GroupAlgebra.average trace_tensorProduct'

/-- Let f be a class function on a finite group G. (1) f is an irreducible character if ⟨f,f⟩ =
1, Re f(1) ≥ 0 and some class function I has ⟨I,f⟩ ≠ 0 and ⟨χ,f⟩ ∈ ℤ for each character χ
with ⟨χ,I⟩ ≠ 0 and χ(1)⟨χ,I(·y)⟩ = ⟨χ,I⟩χ(y) for all y. (2) f is a Z-combination of
characters if all ⟨χ,f⟩ come from Z. (3) a ∈ ℂ[G](∑f(g)g)a if a acts as zero on every
finite-dimensional representation on which ∑f(g)g does. -/
lemma irreducible_criteria_of_isClassFunction (h : IsClassFunction f) : (∀ I, IsClassFunction I →
  classInner I f ≠ 0 → classInner f f = 1 → 0 ≤ (f 1).re → (∀ χ, IsChar χ → classInner χ I ≠ 0 →
  (∀ y, χ 1 * classInner χ (I <| · * y) = classInner χ I * χ y) → ∃ m : ℤ, classInner χ f = m) →
  IsIrrChar f) ∧ ((∀ χ, IsChar χ → ∃ m, classInner χ f = algebraMap Z ℂ m) → f ∈ virtualChars Z G) ∧
  ∀ a, (∀ V : FDRep ℂ G, asAlgebraHom V.ρ (groupAlgElem f) = 0 → asAlgebraHom V.ρ a = 0) → ∃ u, a =
  u * groupAlgElem f * a := by
  have ⟨n, d, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ ℂ[G]
  let ρ i := (lift ..).symm (toLinAlgEquiv'.toAlgHom.comp ((Pi.evalAlgHom ℂ _ i).comp e.toAlgHom))
  choose χ c v using fun i ↦ (⟨_, ⟨.of (dual (ρ i)), rfl⟩, by simp [← trace_toLin'_eq]; tauto⟩ :
    ∃ χ, IsChar χ ∧ χ 1 = d i ∧ ∀ y, (e (single y 1) i).trace = χ y⁻¹)
  choose a t using fun {f} (h : IsClassFunction (groupAlgElem f).coeff) i ↦
    (IsCentral.mem_center_iff ℂ).1
    (Set.center_pi.le (MulEquivClass.apply_mem_center e (Subring.mem_center_iff.2 h.commute)) i ⟨⟩)
  have w f h i y := (by simpa [IsChar.apply_inv, *, ·, mul_comm (f _), Finsupp.sum_fintype]
    using congr(($((groupAlgElem f * .single y⁻¹ 1).lift_unique e.toAlgHom) i).trace).symm) (@t f h)
  have u := by simpa using (w · · · 1)
  have S {f} h : f = ∑ i, classInner (χ i) f • χ i := funext fun g ↦
    (fun _ _ ↦ by simp_all [classInner, t h, traceAux, Matrix.trace, stdBasis, mul_assoc,
    toMatrix_apply, ← mul_sum, Fintype.sum_prod_type, Fintype.sum_sigma,
    ← single_eq_of_single_single]) (u f h) congr($(traceAux_eq ℂ ((Pi.basis fun _ ↦
    stdBasis ..).map e.symm.toLinearEquiv) (basis ..)) (mulLeft ℂ (groupAlgElem f * .single g⁻¹ 1)))
  use fun I _ z k _ H ↦ ?_, by grind [S h, sum_mem, algebraMap_smul, IsChar.mem_virtualChars,
    Subalgebra.smul_mem], fun _ H ↦ ⟨e.symm ((a h)⁻¹ • 1), e.injective (by
    ext1 i; by_cases z : a h i = 0; simpa [ρ, asAlgebraHom, t h, z] using H (.of (ρ i))
    simp [t h, z])⟩
  rw [congr(classInner $(S ‹_›)), classInner] at *
  simp [sum_mul, finMean_sum, mul_assoc, ← classInner.eq_1, RCLike.conj_mul, -finMean] at z k
  specialize S h; norm_cast at k; have ⟨i, _, z⟩ := exists_ne_zero_of_sum_ne_zero z
  have ⟨m, U⟩ := H _ (c i) (by grind) (by simp [*, classInner, field])
  simp +contextual [sum_eq_single i, by simpa using (fun j l p ↦ (k ▸ single_lt_sum l ‹_›
    (mem_univ j) p (by simp)).not_ge (by simp [U] at *; norm_cast; grind) :), U] at S k
  cases k <;> simp_all [classInner, IsIrrChar]; grind

/-- Let G be finite, i : G → H a homomorphism, χ a character of H, s ∈ H, ρ a finite-dimensional
complex representation of G. If the average over G of χ(i(g))·tr ρ(g) vanishes, then ∑_g
χ(i(g)s)·ρ(g) = 0. -/
lemma IsChar.groupAlgElem_eq_zero {χ} (h : IsChar χ) (i : G →* H) s (z :
  finMean (χ ∘ i * ρ.character) = 0) : ρ.asAlgebraHom (groupAlgElem (χ <| i · * s)) = 0 := by
  obtain ⟨τ, rfl⟩ := h
  simpa using congr(TensorProduct.lift (lsmul .. ∘ₗ _ ∘ₗ mulRight _ (τ.ρ s)) $(((homTensorHomEquiv
    ..).injective (by simpa using (tprod (τ.ρ.comp i) ρ).isProj_averageMap.isIdempotentElem
    |>.eq_zero_of_trace_eq_zero (by simp_all)) : ∑ u, _ ⊗ₜ ρ u = 0)))

lemma IsChar.groupAlgElem_eq_zero_iff (h : IsChar χ) : ρ.asAlgebraHom (groupAlgElem (conj ∘ χ)) =
  0 ↔ classInner χ ρ.character = 0 := ⟨(by simpa [classInner] using congrArg (trace ℂ V) ·),
  (by simpa using h.star.groupAlgElem_eq_zero (.id _) 1 ·)⟩
end
