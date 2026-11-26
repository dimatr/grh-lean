import Lib.Adelic.EulerProduct
import Lib.Adelic.SpaceGram
import Lib.Adelic.AdeleIdempotent
import Lib.Adelic.RationalPoints
import Lib.PadicHodge.GeneralisedIndex
import Lib.Adelic.Kronecker

section
/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Modulus of an idele: multiplicativity, continuity, product formula, invariance under
conjugation. -/

open MonoidHom NumberField FinitePlace

variable {E} [Field E] [NumberField E] {x : (𝔸 E)ˣ}

/-- The module of an idele: the homomorphism x ↦ |x| (the adelic absolute value if E is totally
complex) from the idele group of E to the multiplicative monoid ℝ. -/
noncomputable def ideleAbs : (𝔸 E)ˣ →* ℝ :=
  ⟨⟨fun x ↦ (∏ w, ‖x.1.1 w‖ ^ 2) * ∏ᶠ w, ‖x.1.2 w‖, by simp⟩,
  fun x y ↦ have h (z : (𝔸 E)ˣ) t := (finite_idele_val_ne_one (z.map (snd ..))).subset (t := t)
  by simp +contextual [sq, norm_def, not_imp_not, field, finprod_mul_distrib (h x _ _) (h y _ _)]⟩

@[simp] lemma ideleAbs_nonneg_and_ne_zero : 0 ≤ ideleAbs x ∧ ideleAbs x ≠ 0 :=
    ⟨mul_nonneg (by positivity) (finprod_nonneg (by simp)), (toHomUnits _ x).ne_zero⟩

@[simp] lemma ideleAbs_pos : 0 < ideleAbs x := by simp [lt_of_le_of_ne']

lemma ideleAbs_eq_prod_of_v_eq_one : (∀ w, Valued.v (x.1.2 w) = 1) → ideleAbs x =
  ∏ w, ‖x.1.1 w‖ ^ 2 := by simp_all [ideleAbs, norm_def]

@[fun_prop] lemma continuous_ideleAbs : Continuous (@ideleAbs E _ _) :=
  continuous_of_continuousAt_one _ (.congr (by fun_prop)
  (.mono (((continuous_snd.units_map (snd ..)).1 _ (isOpen_idelesUnitOff ∅)).mem_nhds
  (by simp)) fun _ _ ↦ (ideleAbs_eq_prod_of_v_eq_one (by aesop)).symm))

/-- The product formula: for a totally complex number field E and x in E^×, the principal idele of x
has module `ideleAbs` equal to 1. -/
lemma ideleAbs_toAdele [IsTotallyComplex E] [PlaceEmbedding E] (x : Eˣ) : @ideleAbs E _ _
  (x.map (toAdele (E := E))) = 1 := by simpa [← finprod_comp_equiv equivHeightOneSpectrum.symm,
  ideleAbs, ← InfinitePlace.apply] using! prod_abs_eq_one x.ne_zero

@[simp] lemma ideleAbs_star [IsCMField E] : ideleAbs (star x) = ideleAbs x :=
    congr($(by simp) * $(finprod_eq_of_bijective _ star_involutive.bijective (by simp [norm_def])))

lemma ideleAbs_eq_one_of_mem_unitary [IsCMField E] (h : x.1 ∈ unitary _) : ideleAbs x = 1 := by
  simpa using congr(√(ideleAbs $((Units.unitary_eq.ge h).1)))
end

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Sign of a Gauss sum fixed modulo 4 by orbits of order four. -/

/-- Let X be a finite abelian group without 2-torsion, f(f(x)) = −x, F an f-invariant function
with values roots of unity, F(0) = 1, ∑F real, r ≡ 1 mod 4 an integer. If |c| = 1 and c·r^a
= (∑F)·r^b, then c = 1. -/
lemma eq_one_of_orbits {X} [AddCommGroup X] [Fintype X] (f : X → X) (F : X → ℂ) r {a b c}
    (hr : r ≡ 1 [ZMOD 4]) (h₀ : F 0 = 1) (h : ∀ x, IsOfFinOrder (F x) ∧ F (f x) = F x ∧ f (f x) = -x
    ∧ (-x = x ↔ x = 0)) (hc : ‖c‖ = 1) (re : IsSelfAdjoint (Finset.univ.sum F))
    (e : c * r ^ a = Finset.univ.sum F * r ^ b) : c = 1 := by
  by_contra; let s x : Finset X := {x, f x, -x, -f x}
  have E : r ^ b • ((Finset.univ.erase 0).sum F / 4) = ((r ^ a + r ^ b) / -4 : ℚ) := by
    have := congr(star $e); simp_all [IsSelfAdjoint, ↓star_mul', ← c.inv_eq_conj]; grind [norm_zero]
  have ⟨k, _⟩ := (IsIntegral.smul _ ?_).exists_int_iff_exists_rat.1 ⟨_, E.symm⟩
  simp_all [field]; norm_cast at *
  grind [(hr.pow · |>.eq)]
  rw [Finset.sum_div, ← Finset.sum_fiberwise_of_maps_to fun _ ↦ Finset.mem_image_of_mem s]
  refine .sum _ (Finset.forall_mem_image.2 fun y _ ↦ ?_)
  convert IsPrimitiveRoot.isIntegral (.orderOf _) (h y).1.orderOf_pos
  rw [(_ : Finset.filter .. = s y), Finset.sum_insert] <;> grind (splits := 20)
end

section
/-! A general count of the fixed points of an involution on a finite field, applied to finite places
of a stably unramified CM field: a place with w̄ = w has norm r ^ 2 with r ≡ 3 mod 4, so a place of
prime norm is split. -/

open Nat NumberField StablyUnram FiniteField Ideal Quotient Fint selfAdjoint

/-- A finite field with an involution that moves a square root of `-1` has `r ^ 2` elements,
where `r`, the number of fixed points, is `3` modulo `4`. -/
lemma card_selfAdjoint {k} [Field k] [StarRing k] [Finite k] {i : k} (a : i * i = -1) (h :
    star i ≠ i) : .card (selfAdjoint k) ^ 2 = Nat.card k ∧ .card (selfAdjoint k) % 4 = 3 := by
  rw [sq, ← card_prod]
  use card_congr ⟨fun (x, y) ↦ (x - i * y) / 2, fun z ↦ ⟨⟨_, .add_star_self z⟩, _, .add_star_self
    (i * z)⟩, ?_, ?_⟩, Fintype.card_eq_nat_card ▸ isSquare_neg_one_iff.not_left.1 ?_ <;> simp_intro
    x [mem_iff, IsSquare, Subtype.ext_iff] <;> grind [star_mul, star_inj, star_neg, star_one]

variable {E} [Field E] [NumberField E] [IsCMField E] [StablyUnram E] {w : FinPlace E}

/-- For stably unramified E and a finite place w with w = w̄, the norm of w is r² for a natural
number r ≡ 3 mod 4. -/
lemma StablyUnram.exists_sq_eq_q_of_inert (h : star w = w) : ∃ r, r ^ 2 = w.q ∧ r % 4 = 3 := by
  obtain ⟨i, ω, a, b, ⟨⟩⟩ := ‹StablyUnram E›.exists_i_c₀
  let := Quotient.field w.1
  apply_fun Ideal.Quotient.mk w at *
  exact ⟨_, @card_selfAdjoint _ _ (starRingOfInvolution (quotientMap _ _ congr($h.1).ge)
    (Quot.ind (congrArg _ <| star_star ·))) _ i a
    (b.trans_ne (by grind [one_add_one_eq_two, mem_star_place, eq_zero_iff_mem]))⟩

lemma isSplit_of_q_prime (h : w.q.Prime) :
  w.IsSplit := by grind [exists_sq_eq_q_of_inert, h.pow_eq_iff]
end

section
/-! Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus
(known result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Haar modulus of ideles and adelic matrices is the adelic absolute value. -/

open LinearMap RingHom Subgroup Units Algebra Matrix MeasureTheory NumberField Valued WithZero
  MeasureTheory.Measure FinitePlace Valuation.IsRankOneDiscrete Valuation.IsUniformizer

variable {E n : Type*} [Field E] [NumberField E] [Fintype n] {w : FinPlace E} (a : GL n (𝔸 E))

lemma v_uniformizer_inv_mul_le_one_iff {y} : v ((uniformizer w).1⁻¹ * y) ≤ 1 ↔
  v y < 1 := by simp [← lt_mul_exp_iff_le]

lemma norm_locField_eq_q_zpow {x : LocField w} : x ≠ 0 → ‖x‖ = w.q ^ (v x).log := by
  simp_all [FinitePlace.norm_def, WithZeroMulInt.toNNReal, toAdd_unzero_eq_log]

lemma eq_norm_inv_of_uniformizer (χ : (LocField w)ˣ →* ℝ) (h : ∀ {x}, v x.1 = exp (-1) → χ x = w.q)
  {x} : χ x = ‖x.1‖⁻¹ := by simpa [norm_locField_eq_q_zpow, h (v_uniformizer w), field] using @h (x
  * uniformizer w ^ (v x.1).log * uniformizer w) (by simp [WithZero.exp_neg, -inv_exp])

lemma isValuationPair_Ohat : IsValuationPair (Ô E) := fun a b ↦ ⟨⟨_, idem_mem_Ô {w | v (a w) ≤
  v (b w)}⟩, by aesop (add simp [exists_eq_mul_iff_v_le, idem_apply, le_of_lt])⟩

instance [IsCMField E] : IsStarStable (Ô E) := ⟨star_mem_Ô⟩

/-- The module |x| of a finite idele x: the adelic absolute value of the idele with finite part
x and component 1 at infinity. -/
noncomputable def finIdeleAbs := (@ideleAbs E).comp finIdeleIncl

/-- The product formula, finite part: for x in E^×, the product of the normalised absolute
values |x|_w over the finite places is |N_{E/ℚ}(x)|⁻¹. -/
@[simp] lemma finIdeleAbs_principalIdele x : finIdeleAbs (principalIdele (x : Eˣ)) =
  |Algebra.norm ℚ x.1|⁻¹ := by simpa [finIdeleAbs, ideleAbs,
  ← (finprod_comp_equiv equivHeightOneSpectrum.symm)] using! prod_eq_inv_abs_norm x.ne_zero

@[simp] lemma finIdeleAbs_locIdele x : finIdeleAbs (locIdele w x) = ‖x.1‖ := by
    simp_all [finIdeleAbs, ideleAbs, finprod_eq_single _ w]

/-- For a finite idele a of a number field E, the inverse of the factor by which a scales
additive Haar measure on the finite adeles equals |a|⁻¹, where |a| = `finIdeleAbs` a is the
adelic absolute value. -/
lemma genIndex_eq_inv_finIdeleAbs (a : (𝔸f E)ˣ) : genIndex a.1 = (finIdeleAbs a)⁻¹ :=
  mem_of_locIdele_mem (H := (genIndex.1.comp (coeHom
  _)).eqLocus (invMonoidHom.comp _)) (isClosed_of_isOpen _ (isOpen_mono (fun _ _ ↦ .symm (by
  simp_all [Nat.card_unique, genIndex_eq_card isOpen_Ô isCompact_Ô, mem_Ô, finIdeleAbs,
  ideleAbs_eq_prod_of_v_eq_one])) (isOpen_idelesUnitOff ∅))) fun w ↦
  .trans (eq_norm_inv_of_uniformizer ((genIndex.1.comp _).comp _) (fun _ ↦ by
  erw [← card_ResField,
    ← Nat.card_congr (quotientKerEquivOfSurjective (funext (reduceAt_algebraMap w) ▸
    algebraMap_ResField_surjective w).of_comp).1, genIndex_eq_card isOpen_Ô isCompact_Ô (mem_Ô.2 _)]
  congr with
  all_goals simp_all +decide [Ideal.mem_span_singleton, Subtype.ext_iff, dvd_def, ← and_forall_ne w,
    exists_eq_mul_iff_v_le, mem_Ô.1, ← lt_mul_exp_iff_le, ← WithZero.exp_add])) (by simp)

lemma genIndex_eq_inv_norm (a : (LocField w)ˣ) : genIndex a.1 = ‖a.1‖⁻¹ :=
  eq_norm_inv_of_uniformizer (genIndex.1.comp (coeHom _))
  (by erw [genIndex_eq_card (isOpen_valuationSubring _) (isCompact_LocInt _), ← is_generator,
  card_ResField] <;> simp_all +decide [iff, generator_eq_exp_neg_one_of_mem_range ⟨_, ·⟩])

lemma map_mulVec_haar_finAdele μ [IsAddHaarMeasure μ] (a : GL n (𝔸f E)) :
    μ.map (a.1 *ᵥ ·) = ENNReal.ofReal (finIdeleAbs a.det)⁻¹ • μ :=
    (distribHaarChar_GL_eq_det isOpen_Ô isCompact_Ô isValuationPair_Ohat a).trans
  (genIndex_eq_inv_finIdeleAbs a.det) ▸ map_smul_eq_inv_distribHaarChar_smul a

/-- For a in GL_n of the adeles of E, the map x ↦ ax pushes the Haar measure on adelic n-vectors
forward to |det a|⁻¹ times itself, with the adelic absolute value. -/
lemma volume_map_mulVec_adele : volume.map (a.1 *ᵥ ·) = ENNReal.ofReal (ideleAbs a.det)⁻¹ •
  volume := map_haar_eq_smul_of_semiconj _ (.mk ⟨.arrowProdEquivProdArrow .., by tauto⟩)
  (congrFun (by ext : 3; exacts [Prod.fst_sum, Prod.snd_sum])) ((MeasurePreserving.prod
  ⟨(LinearMap.continuous_of_finiteDimensional _).measurable,
  map_linearMap_addHaar_eq_smul_addHaar addHaar ((a.map (.fst
  ..)).toLin.toLinearEquiv.restrictScalars _).isUnit_det'.ne_zero⟩ ⟨by fun_prop,
  map_mulVec_haar_finAdele
  volume (a.map (.snd ..))⟩).2.trans (by erw [det_restrictScalars, det_toLin', ← map_det,
  a.map_det, det_pi (mul ℝ ℂ ∘ _), funext (norm_complex_apply ∘' _)]; simp [ideleAbs, finIdeleAbs,
  ← Complex.sq_norm, prod_smul_left, prod_smul_right, mul_smul, finprod_nonneg, Finset.prod_pow]))
  ((LinearMap.continuous_of_finiteDimensional _).measurable.prodMap (by fun_prop))

@[simp] lemma det_star [IsCMField E] : (star a).det = star a.det := Units.ext (det_conjTranspose _)

/-- For a in GL_n(𝔸) and b in GL_1(𝔸), the map x ↦ axb on n×1 adelic matrices pushes the
standard measure forward to |det(b)^n det a|⁻¹ times itself, with |·| the module of an
idele. -/
lemma volume_map_mul_mul_adele (b : GL Unit (𝔸 E)) : volume.map (α := Matrix n Unit (𝔸 E))
  (a.1 * · * b.1) = ENNReal.ofReal (ideleAbs (b.det ^ Fintype.card n * a.det))⁻¹ • volume :=
  map_haar_eq_smul_of_semiconj _ (.mk ⟨.mk _ (· <| Prod.swap ⟨·, ·⟩), vec_add⟩) (.symm <|
  kronecker_mulVec_vec _ · _) ((volume_map_mulVec_adele (kroneckerGL ..)).trans
  (by simp [ideleAbs]; erw [det_kronecker']; simp))
end
