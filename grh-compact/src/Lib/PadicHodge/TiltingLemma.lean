import Lib.PadicHodge.Corepresentable

-- part: New.Selmer.LinePointPowers
section
/-! Part of: Tied conditions at new primes shrink Selmer groups (see New.Selmer.TwistTheorem).

Part of: Roots of unity keeping polynomial valuations low, in any degree (see
New.Selmer.RootsOfUnityPoints).

This file: Mirror lemma: relations isotropic on a coset are few, killed by a scalar difference. One
polynomial bounds twisted Selmer lengths everywhere, sharply at a chosen point. Points on the line
through a root of unity are almost roots of unity. -/

open Submodule commutatorElement AddMonoidHom Matrix.Module QuotientAddGroup

/-- Let ρ(G) span all matrices, c be an involution, y a cocycle mod I with a unit entry, γ and
(cγ)⁻¹ act by s with s² − 1 a unit, χ(γ) = χ(cγ) = 1, y(γ) = 0. Let U act trivially mod I, H
≤ U be normal, c-stable, containing all [g, γ], and z, cz ∈ U. If distinct χ-equivariant
homomorphisms x_w (w ∈ W) from U to the dual have ⟨x_w, ty⟩ c-invariant on zH, and ρ(g) = α,
ρ(cg)⁻¹ = α' are scalars, then |W| ≤ #(O mod I)^n[α − χ(cg)α']. -/
lemma card_le_torsion_of_isotropic {O G n} [CommRing O] [Group G] [Fintype n] {I : Ideal O}
  [Finite (O ⧸ I)] {ρ : G →* Matrix n n O} (hρ : span O (.range ρ) = ⊤) (χ : G →* O) {c : G →* G}
  (_hc : ∀ g, c (c g) = g) (H U : Subgroup G) [hN : H.Normal] γ {g₀ z} {s : O} {y : G → n → O ⧸ I}
  {W} (x : W → G → _ →+ QZ) (hi : ∀ w v, (∀ g ∈ U, x w g = x v g) → w = v) (hU : ∀ g ∈ U, ∀ m : n →
  O ⧸ I, ρ g • m = m) (hH : ∀ g ∈ H, c g ∈ H ∧ g ∈ U) (κ : ∀ g : G, ⁅g, γ⁆ ∈ H) (p : IsUnit (s - 1))
  (s₂ : IsUnit (s + 1)) (hγ : ρ (c γ)⁻¹ = s • 1 ∧ ρ γ = s • 1 ∧ χ (c γ) = 1 ∧ χ γ = 1 ∧ y γ = 0) (hz
  : z ∈ U ∧ c z ∈ U) (hy : ∀ g h, y (g * h) = y g + ρ g • y h) {i} (hu : IsUnit (y g₀ i)) (hW : ∀ᵉ
  (w) (g) (a ∈ U) (b ∈ U) (m), x w (a * (g * b * g⁻¹)) m = x w a m + x w b (χ g • ρ g⁻¹ • m)) (hq :
  ∀ᵉ (w) (h ∈ H) (t : O), x w (z * h) (t • y (z * h)) = x w (c (z * h)) (t • y (c (z * h))))
  {g α α'} (hδ : ρ g = α • 1 ∧ ρ (c g)⁻¹ = α' • 1) : Nat.card W ≤ .card (torsionBy O (n → O ⧸ I) (α
  - χ (c g) * α')) := have cj g a := eq_sub_of_add_eq (hy (a * g⁻¹) g).symm
  have J k (h : ρ k⁻¹ = s • 1) := by simpa [*, ↓map_mul] using hU (k⁻¹ * k)
  have ⟨τ, hτ, u⟩ : ∃ τ ∈ H, IsUnit (y τ i) := ⟨_, κ g₀, by simpa [map_mul_eq_one, cj, *,
    commutatorElement_def, sub_smul] using (hu.smul (-p.unit))⟩
  have C w {b} v : ∀ t k, x w b (t • ρ k • y τ) = x w (c τ) (χ (c k) • t • ρ (c k)⁻¹ • y (c b))
    := (p.mul s₂).unit.mulRight.forall_congr_right.1 fun r k ↦ by
    have F {b} v t := congr($(hq w b v (r * s * t)) -
      $(hq w _ (mul_mem v (hN.1 _ hτ k)) (r * s * t)))
    linear_combination (norm := simp (maxDischargeDepth := 6) [cj, hW, ↓hU, hy, hz, v, hH, hγ, J,
      hτ, mul_mem, hN.1, by simpa using hW w 1, mul_smul, sub_eq_add_neg, add_smul,
      ↓smul_comm (ρ _), ↓smul_add])
      F (mul_mem v (hN.1 b v γ)) 1 - F v (s + 1) + F H.one_mem s
    abel
  have V {f} h := functions_ext _ f 0 fun j m ↦ by
    simpa [Algebra.smul_def, mul_assoc] using closure_induction (p := fun A _ ↦ f (A • y τ) = 0)
      (by simp) (by grind [add_smul]) h (eq_top_iff'.1 hρ (.single j i (m * u.unit⁻¹).out))
  (Nat.card_le_card_of_injective (fun w ↦ lift _ (x w (c τ)) ((range_le_ker_iff
   (DistribSMul.toAddMonoidHom _ _) _).2
   (V (by simpa [smul_smul, ↓sub_smul, *, -_hc, mul_comm α, mul_comm α', mul_assoc] using (C w (hH _
    hτ).1 · <| · * g))))) fun w v e ↦ hi w v fun g o ↦ ext (p.smul_bijective.2.forall.2 fun m ↦
    have Z w := sub_eq_of_eq_add (hW w γ ⁅g, γ⁆ (by simp [*]) g o (ρ γ • m))
    by simpa [commutatorElement_def, *, mul_assoc, sub_smul, sub_mul, mul_sub, sub_eq_zero,
      ↓smul_smul] using ((Z
      w).congr (Z v)).2 congr($(sub_eq_zero.1 (V (by simp [*, by simpa [DFunLike.ext_iff, forall_mk]
      using e]))) _))).trans_eq ((card_hom_QZ _).trans AddSubgroup.index_range)

open IsDiscreteValuationRing Matrix Module Ideal MvPolynomial NeZero Finsupp

attribute [local simp] MulAction.compHom_smul_def mapRel linearCombination_apply twistAtPoint
  Module.smul_def sum_mapRange_index mem_obeying _root_.funext_iff mem_selmerModule_iff
  Algebra.smul_def algebraMap_eq_diagonal

/-- Let ρ modulo ℓ^M and h: Gal(Ω/E) → (ℤ/q)^σ be continuous. For each tuple y₀ over O some
polynomial F bounds the Selmer length of y^h·ρ modulo ℓ^M by v(F(y)) at every tuple y over every
discrete valuation ring over O, with equality at y₀. -/
lemma exists_sharp_fitting_poly {ℓ M q E n σ O₀ O} [NeZero ℓ] [Field E] [EmbeddedNumberField E]
  [Fintype n] [Fintype σ] [CommRing O₀] [CommRing O] [DVR O] [CharZero O] {ρ : Gal(Ω/E) →* Matrix n
  n O₀} e₀ (S : Finset (FinPlace E)) {h} (hh : ∀ j : σ, IsLocallyConstant (h j)) (hρ :
  IsLocallyConstant (reduceModPow ℓ M ρ)) L y₀ : ∃ F, addVal O (MvPolynomial.eval y₀ F) ≤ length O
  (selmerModule (twistAtPoint (q := q) h y₀ e₀ ρ) S (mapRel e₀ '' L) (QuotSpan (ℓ ^ M : O))) ∧
  ∀ O' [CommRing O'] [DVR O'] e y, length O' (selmerModule (twistAtPoint h y (e.comp e₀) ρ) S
  (mapRel (e.comp e₀) '' L) (QuotSpan (ℓ ^ M : O'))) ≤ addVal O' (eval₂Hom e y F) := by
  choose ι _ γ R r H using
    exists_corepresenting_coords (ℓ ^ M) (twistAtPoint h X (C.comp e₀) ρ) ((hρ.eventually_eq 1).and
    (.all (hh · |>.eventually_eq 1))) S.finite_toSet (mapRel (C.comp e₀) '' L)
  choose A W hu hW k using exists_matrix_addVal_det_le_length (.map ((aeval y₀).toLinearMap.compLeft
    _) (R.restrictScalars O)) (ne (ℓ.cast ^ M)) (⟨_, r <| C ∘ ·, by simp⟩)
  choose u hu hu' using hu
  have K {O'} [CommRing O'] (e : O →+* O') y :=
    @H (O' ⧸ _) _ (.compHom _ (eval₂Hom e y)) nsmul_quot_eq_zero
   fun g ⟨a, b⟩ ↦ by simpa [b] using! congr((($a).map (quotientMap _ (e.comp e₀) (by simp))).mulVec)
  use det u, ?_, fun O _ _ e y ↦ ?_ <;> erw [RingHom.map_det]
  exact (funext hu' ▸ k).trans (length_le_of_le_map ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩ _ fun w h ↦ by
    simpa using (K ..).2.2 ((hW _).1 ⟨·, ·, rfl⟩ w h))
  grw [← length_ker_le_addVal_det, ← relLength_bot,
    relLength_le_of_inj ⟨⟨(↿· ∘ γ), by tauto⟩, by tauto⟩, relLength_bot]
  simpa using! (@(K e y).1 · · _ <| hu ·)
  simpa using! (@(K e y).2.1 · · 0)

lemma dvd_one_add_mul_pow_sub_one {ℓ O k N} [p : ThePrime ℓ] [CommRing O] t {u : O} (h :
  u ^ ℓ ^ k = 1) M (a : k + M ≤
  N) : ↑ℓ ∣ (1 + t * (u - 1) - 1) ^ ℓ ^ k ∧ (ℓ : O) ^ M ∣ (1 + t * (u - 1)) ^ ℓ ^ N - 1 := by
  have H a := congr((ℓ : O) ∣ $(add_pow_prime_pow_eq' p.out 1 a k) - 1)
  simp [add_assoc, dvd_add_left] at H
  refine ⟨?t, by simpa [← pow_mul, ← pow_add, a.trans'] using
    (pow_dvd_pow _ (by lia)).trans (dvd_sub_pow_of_dvd_sub ((H _).2 ?t) (N - k))⟩
  simp [mul_pow, Dvd.dvd.mul_left, ← H, h]
end

-- part: New.Selmer.TiltingLemma
section
/-! Part of: Tied conditions at new primes shrink Selmer groups (see New.Selmer.TwistTheorem).

Part of: One anticyclotomic twist makes all Selmer groups short (see New.Selmer.TwistForRows).

This file: Selmer groups cut by relations lie in Selmer groups with local conditions. Ties cost only
determinants along twists; a group no new prime shortens is short. `tilting`: generic members of
a pencil of linear maps have short kernels. -/

section

open Matrix.Module Module Nat Ideal Matrix MonoidHom Set Subgroup commutatorElement
variable {E n O B} [Field E] [UnramCMField E] [Fintype n] [CommRing O] [CommRing B] [Algebra O B]
  [TopologicalSpace B] [DiscreteTopology B] {ρ : Gal(Ω/E) →* Matrix n n O} {S L}

/-- The linear map sending z: Gal(Ω/E) → B^n to the pair z(g), z(g^{−c}) (`idOrConjInv`). -/
noncomputable def evalConjPair (g : Gal(Ω/E)) :=
  (LinearEquiv.curry O B _ n).symm.1 ∘ₗ .funLeft O _ (idOrConjInv · g)

lemma mem_selmerZ1_of_mem_selmerModule {x A P Q K c} (h : x ∈ selmerModule ρ S L B) (l : K ⊆ L) (k :
  S ⊆ P ∪ Q := by simp [unionWithConj])
  : x ∈ selmerZ1 ⟨actionRep O _ ρ, c⟩ P A (fun _ ↦ localCocycles ρ K _ B) Q :=
  ⟨(mem_selmerModule_iff.1 (selmerModule_mono h .rfl (by grind))).imp (⟨h.2.continuous, ·⟩) (·.1),
  fun _ _ ↦ ⟨x, selmerModule_mono h l, rfl⟩, (nomatch ·, ·.false_of_isTotallyComplex)⟩

variable {ℓ} {E : _} {ι} {O : _} [ThePrime ℓ] [Field E] [UnramCMField E] [CommRing O]
  {V W S₀ M N P₀ J} {x : _ → AuxPrimeData E _ × (ι → O)} (hp :
  IsPencil ℓ S₀ V W N P₀ J x) {n : Type} [Fintype n] {ρ : Gal(Ω/E) →* Matrix n n O}
include hp

omit [ThePrime ℓ] in
lemma IsPencil.char_tame_gen {v} (hv : v ∈ J) w (hw : w ∈ J) : (x w).1.h (x v).1.γ =
  ite (w = v) (.ofAdd 1)
  1 := by grind [IsPencil, IsAnticyclotomicAt, (hp.3 w hw).eq_one_of_mem_inertiaAbove, inertiaAbove]

/-- The character χ = ∏_w y_w^{h_w} takes the value y_v at the tame generator γ_v and at
γ_v^{−c}; for v ≠ P₀ it takes the value y_{P₀} at the Frobenius φ_v and at φ_v^{−c}, P₀ the
helper prime. -/
lemma IsPencil.pointChar_idOrConjInv {R} [CommRing R] {y : J → R} hy (v :
  J) b : let χ := pointChar (x ·.1 |>.1.h) y hy
  χ (idOrConjInv b (x v).1.γ) = y v ∧ (v ≠ P₀ → χ (idOrConjInv b (x v).1.φ) = y ⟨_, hp.2⟩) := by
  simp_all [(hp.3 ..).apply_idOrConjInv, hp.char_tame_gen, hp.4, Subtype.coe_eq_iff, hp.2,
    apply_ite, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod]

attribute [local simp] Finsupp.mapRange_sub' Units.smul_def funext_iff mapRel sub_smul twistRep in
/-- Twist ρ by the point y_P = 1 + t_P(u − 1), y_{P₀} = u, with u^{ℓ^k} = 1, k + 2M ≤ N. Dropping
the ties at I ⊆ J (u = 1 if P₀ ∈ I) raises the Selmer length mod ℓ^M by at most Σ v det(uρ(w) − 1),
over w = w_P, w_P^{−c}, P ∈ I, acting mod ℓ^M like φ_P, φ_P^{−c}. -/
lemma IsPencil.length_le_of_drop_ties i (hu : ∀ g ∈ inertiaAbove S₀ᶜ, reduceModPow ℓ M ρ g = 1) k
  (hk : k + M + M ≤ N) (hU : ∀ g, V i g → reduceModPow ℓ M ρ g = 1) O' [CommRing O'] [DVR O'] (e :
  O →+* O') {u} (h : u ^ ℓ ^ k = 1) I (w : _ → _) (hI : I ⊆ J) (h₀ : P₀ ∈ I → u = 1)
  (hF : ∀ p : I × _, reduceModPow ℓ M ρ (idOrConjInv p.2 (x p.1).1.φ) =
  reduceModPow ℓ M ρ (w p)) {S L} : let y (j : J) := 1 + ite (j = P₀) 1 (e ((x j).2 i)) * (u - 1)
  let r := twistAtPoint (x ·.1 |>.1.h) y e ρ
  let B := QuotSpan (ℓ ^ M : O')
  length O' (selmerModule r S (mapRel e '' L) B) ≤
    length O' (selmerModule r S (mapRel e '' (L ∪ tieRelations I x i)) B) +
    ∑ p, IsDiscreteValuationRing.addVal _ (u • (ρ (w p)).map e - 1).det := by
  intro y r B
  rw [image_union, selmerModule.eq_1 _ _ (_ ∪ _), ← union_assoc, obeying, iInf_union,
    inf_right_comm, add_comm, iInf_image, tieRelations, iInf_range, ← relLength_add_length_inf]
  apply add_le_add_left ((relLength_iInf_le ..).trans _)
  gcongr with ⟨⟨v, o⟩, b⟩
  grw [relLength_ker, ← length_ker_le_addVal_det, length_mono]
  intro d ⟨c, H, l⟩
  have hy {N} a j : (y j : B) ^ ℓ ^ N = 1 :=
    mk_span_eq_iff_dvd_sub.2 (dvd_one_add_mul_pow_sub_one _ h M a).2
  let R := twistRep (quotientMap _ e (by simp)) (pointChar (x ·.1 |>.1.h) _ (hy (by lia)))
    (reduceModPow ℓ M ρ)
  lift v to J using hI o
  obtain ⟨⟨_, q, p⟩⟩ := hp.3 _ v.2, hp.1 _ v.2, @Algebra.smul_def O' B
  have hc g h : c (g * h) =
    c g + R g • c h := by simp +zetaDelta [mem_selmerModule_iff.1 H, twistAtPoint, reduceModPow, *]
  have C {w A} hA hw (l : w ∉ placesDividing E ℓ) := let := (hu · ⟨w, hw, A, hA, ·⟩)
    (tame_affineAction nsmul_quot_eq_zero hA hc (by simp_all [← Finset.prod_pow, smul_pow, map_pow,
      R, pow_right_comm]) ((J.eventually_all.2 (hp.3 · · |>.isLocallyConstant.eventually_eq 1)).mp
      (by simp_all [R])) ⟨·, ·⟩ (by simp [hA.valuation_natCast_eq_one_iff.2 l]) H.2 |>.2
      (q.of_dvd (pow_add ℓ .. ▸ pow_dvd_pow ℓ hk)))
  have C := congr($(show Commute (affineAction hc (idOrConjInv b (x v).1.φ))
    (affineAction hc (idOrConjInv b (x v).1.γ)) by
    cases b <;> simp [idOrConjInv, C p.conjPlace_star, IsFrob.conjPlace_conjGal, C p, *]) 0)
  obtain rfl | _ := eq_or_ne ↑v P₀ <;> simpa [R, y, hp.pointChar_idOrConjInv,
    hF ⟨⟨v, o⟩, b⟩, *] using! show R (idOrConjInv b (x v).1.φ) • d =
    d by by_cases (x v).2 i = 0 <;> simp [R, y, ← l, map_smul', hp.6,
    affineAction, hp.pointChar_idOrConjInv,
    idOrConjInv_mem_inertiaAbove p, *] at C ⊢ <;> exact (by linear_combination C ·)

/-- Mirrors. Let ρ be balanced up to β, a ∣ ℓ^M, X the Selmer module mod a (relations L, ties at J,
zero at γ), some member having a unit entry. If at each admissible new prime P the values of X at
φ_P, φ_P^{−c} are values at γ_P, γ_P^{−c} of cocycles relaxed at P, P̄, then length X ≤ β.

Tied conditions at new primes shrink Selmer groups. -/
lemma IsPencil.length_le_of_unseen_class [PadicIntegerRing O ℓ] {i S L γ β} (r : IsBalanced ℓ S ρ L
  γ β M) (hV : V i = (reduceModPow ℓ M ρ · = 1)) (hS : S ⊆ S₀) {a : O} [NeZero a] (ha : a ∣ ℓ ^ M) :
  let X T := (selmerModule ρ (unionWithConj S T) (L ∪ tieRelations J x i ∪ {.single γ 1}) (QuotSpan
    a)); (∃ y ∈ X J, ∃ g e, IsUnit (y g e)) → (∀ P ∉ J, ∀ l, (∀ t, IsPencil ℓ S₀ V W N P₀ (insert P
    J) (Function.update x P (l, Pi.single i t))) → X J ≤ ((X (insert P J)).map (evalConjPair
    l.γ)).comap (evalConjPair l.φ)) → length O (X J) ≤ β := fun ⟨y, hy, g, k, hu⟩ Z ↦ by
  obtain ⟨⟨r₁, r₂, r₄, ⟨⟨v, ⟨hv, hw⟩, B, hB, e⟩, s, hs, hs', s₁⟩, _, r₇, _, α, _, hα, h⟩, Y, m, _,
    p₁, p₂, p₃, _, _, p₆⟩ := r, (mem_selmerModule_iff.1 hy).1, (mt <| @hS ·),
    (hV.le _ <| hp.6 · · i · ·), id hp
  obtain ⟨hm, ⟨⟩, c, _, -, -, p, -, b₀, q, _⟩ := fun b : n → _ ↦ funext (nsmul_quot_eq_zero
    (ha.trans (pow_dvd_pow _ M.le_succ)) <| b ·), PSigma.mk _ (discreteTopology_bot (QuotSpan a)),
    cycChar_eq_one_of_mem_inertiaAbove ⟨v, by tauto⟩, p₁ _ p₂, p₃ _ p₂
  let := IsTorsionBy.module (smul_quot_eq_zero_of_dvd ha)
  have G (b : n → QuotSpan a) : IsLocallyConstant (ρ · • b) := r₁.comp (· • b)
  let X :=
    DiscreteModule.of (actionRep O _ ρ) (continuous_prod_of_discrete_right.2 (G · |>.continuous))
  let U := (reduceModPow ℓ M ρ).ker ⊓ (cycCharMod Ω (ℓ ^ M.succ)).ker
  let H := ⁅normalClosure (range (idOrConjInv · γ)), ⊤⁆ ⊓ U
  have k b g : ⁅idOrConjInv .., g⁆ ∈ H := ⟨commutator_mem_commutator (subset_normalClosure ⟨b, rfl⟩)
    ⟨⟩, U.inv_mem_iff.1 (by cases b <;> constructor <;> erw [commutatorElement_inv,
    div_mem_ker_iff] <;> simp [idOrConjInv, mul_inv_cancel_comm, reduceModPow, *, map_mul_eq_one])⟩
  have u : (x P₀).1.γ ∈ U ⊓ U.comap conjGal := by simp [U, reduceModPow, cycCharMod_prime_pow_eq,
    cycChar_eq_one_of_mem_inertiaAbove ⟨_, b₀,
    _, p, q⟩, (r₂ _ ⟨_, ·, _, p, q⟩), (r₂ _ ⟨_, ·, _, p.conjPlace_star, q.conjPlace_conjGal⟩), *]
  have v' g (h : reduceModPow ℓ M ρ g = 1) (m : X) : ρ g • m = m := congr($h • m).trans (by simp)
  have D (b : X) : (ρ · • b - b) ∈ selmerModule ρ S (L ∪ tieRelations J x i) _ :=
    mem_selmerModule_iff.2 ⟨by simp [mul_smul, smul_sub], by simp_all, (iInf_union.ge : _ ≤
    obeying ..) ⟨r₇ a b, mem_obeying.2 fun | _, ⟨⟨⟨w, v⟩, s⟩, rfl⟩ => by by_cases (x w).2 i = 0 <;>
    simp [*, r₂ _ (idOrConjInv_mem_inertiaAbove (p₃ _ v).3 (p₃ _ v).6.1 (by simp [*, p₁ _]) s)]⟩,
    (G b).sub (.const b)⟩
  choose A hA using fun v : FinPlace E ↦ @ENat.exists_eq_iInf {A // IsPlaceOver A v} ⟨_,
    v.isPlaceOver_placeOver⟩ (length O <| localCocycles ρ (L ∪ tieRelations J x i) · (QuotSpan a))
  let := ZMod.algebra' X _ (ringChar.dvd ((nsmul_one _).symm.trans (hm 1)))
  have o : U.IsOpen := .inter (r₁ {1}) isOpen_ker_cycCharMod.1
  choose _ _ _ _ _ σ _ π T' _ _ lc h₁ d R using selmerZ1.exists_split_primes_relations (M :=
    X) (S := unionWithConj S J) (fun g h ↦ by ext; simp [X,
    r₂ g (h.imp (by grind))]) (A · |>.2) (fun _ ↦ localCocycles ..) (fun v k _ ⟨b, e⟩ ↦ ⟨_,
    selmerModule_mono (D b) .rfl, e⟩) (·.false_of_isTotallyComplex.elim) QZ (.mk ⟨U,
    o⟩) (v' · ·.1) (fun _ ↦ (·.2)) (·.false_of_isTotallyComplex.elim)
  specialize h₁ (σ.hasFewCocycles_of_central nofun ⟨Pi.finite, hm, (v' · ·.1), fun _ _ ↦
    s₁.smul_left_cancel.1 ∘ by simp [X, *, sub_smul]⟩ c (k true · |>.2) d)
  grw [card_le_torsion_of_isotropic r₄ (.comp (Units.coeHom _) (cycCharIn O Ω ℓ)) conjGal_conjGal
    (H ⊓ H.comap conjGal) U γ (·.1 <|
    π ·) (fun w v h ↦ by ext i : 2; simpa [R _ w.2, R _ v.2] using h _ (σ.isFrob
    i).2) (v' · ·.1) (by simp +contextual [H]) (fun g ↦ by simpa [idOrConjInv, mul_assoc,
    commutatorElement_def] using (And.intro (inv_mem (k true g)) (k false (conjGal (γ * g))))) s₁
    hs' (by simpa [*] using mem_obeying.1 hy.1 _ (.inr (.inr rfl))) u Y hu (fun w g ↦ by
    simpa [by simpa using map_cycChar_smul (σ := g) (Ω := Ω) (.id _) _ hm]
      using! (R _ w.2).2.1 g) (fun w h ⟨⟨z, h₂⟩, _, h₃⟩ t ↦ ?_) hα, ← card_fin (_ + _),
    ← card_fun, ← Finset.prod_coe_sort, ← card_pi] at h₁
  simp [← card_prod] at h₁
  have := length_le_of_card_dvd_or_le ℓ (R :=
    O) (.inr ⟨h₁, ((selmerZ1.finite_unramified_cocycles X).sep _).instProd⟩)
  grw [length_prod, ← relLength_add_length_inf _ (LinearMap.proj γ).ker, relLength_ker,
    (Submodule.map ..).eq_top_iff'.2 (s₁.smul_bijective.2.forall.2 fun c ↦
    ⟨_, mem_selmerZ1_of_mem_selmerModule (D c) .rfl, by simp
    [hs, sub_smul]⟩), length_top, add_right_comm, ← length_prod] at this
  refine ((ENat.add_le_add_iff_left length_ne_top).1 (this.trans ?_)).trans' (length_mono fun x
    h ↦ ⟨mem_selmerZ1_of_mem_selmerModule h
    le_sup_left, by simpa using mem_obeying.1 h.1 _ (.inr (.inr rfl))⟩)
  simp_rw [length_prod, length_pi_of_fintype, Fin.sum_const, add_assoc]
  grw [length_mono inf_le_left, (Finset.sum_coe_sort ..).trans (congrArg _ (funext hA)),
    unionWithConj, ← S.card_sdiff_add_card_eq_card S.subset_union_left, add_rotate',
    (length_ker_le_addVal_det _ a).trans' (length_mono (smul_one_smul (Matrix n n O) _ · |>.trans)),
    ← S.sum_sdiff S.subset_union_left, Finset.sum_le_card_nsmul _ _ _ fun v hv ↦ ?_, add_assoc,
    add_assoc, add_nsmul, add_assoc, ← h a ha]
  · gcongr; exacts [length_mono (Submodule.map_mono fun _ ↦
      (selmerModule_mono · le_sup_left)), by simp]
  · let ⟨w, hw, e⟩ : ∃ w ∈ J, v = w ∨ v = star w := by clear * - hv; grind
    choose b A o H using exists_conj_side_detects (nsmul_quot_eq_zero ha) _ (p₃ w hw).6.2.2 (p₃ w
      hw).5 (r₂ · ∘ .imp (by clear * - hv; grind)) e
    grw [iInf_le _ ⟨A, o⟩, localCocycles, ← relLength_ker, ← length_top, ← relLength_bot]
    exact relLength_le_of_inj (.proj _) (by simp) fun c d (h : c _ = 0) ↦ funext ((H c d (by
      simpa [h] using mem_obeying.1 d.1 _ (.inr (.inr ⟨(⟨w, hw⟩, b), rfl⟩)))).2 _ (p₃ w hw).4 h)
  have D := lc.comp₂ hy.2 (w.1 · <| t • ·)
  obtain ⟨P, hP, n, c, ⟨f, h₁, hj⟩, _, hl⟩ := exists_isAnticyclotomicAt N (J.erase P₀) (J ∪ (S₀ ∪
    (T' ∪ S₀.image star))).finite_toSet (mul_mem (subset_normalClosure ⟨_, by simp [*], _, p, q⟩)
    (normalClosure_mono (forall_mem_range.2 (idOrConjInv_mem_inertiaAbove hB e (by simp [hS hv, hw,
    (p₁ _).mt]))) (commutator_le_left _ _ z))) (((D.comp₂ (D.comp_continuous continuous_conjGal)
    Eq).eventually_eq _).and (.and ((o.inter o.preimage_of_continuous).eventually_mem
    (mul_mem u ⟨h₂, h₃⟩)) (J.eventually_all.2 (p₃ · · |>.isLocallyConstant.eventually_eq _))))
  simp [U, idOrConjInv, (x · |>.1.h.mem_ker.1 (Abelianization.commutator_subset_ker _
    (commutator_mono le_top le_rfl z)))] at hP hj h₁ p₆
  obtain ⟨⟨⟨n₂, _⟩, _⟩, I, _, _, a, F, m, j, _⟩ := hP, mem_ker.1 (U.inv_mem h₁.2).1, hl _ .rfl
  choose δ l using exists_isTameGeneratorFor Gal(Ω/E) (ℓ ^ M.succ) a
  refine (Z P n₂ c (fun t ↦ by constructor <;> simp +contextual [*, IsAuxiliary, p₁ _, idOrConjInv,
    @eq_comm _ P, (ne_of_mem_of_not_mem · n₂), isSplit_of_q_prime, hp.char_tame_gen,
    star_eq_iff_star_eq, fun v h ↦ ((hl _ le_sup_left).eq_one_of_mem_decompGroup · (p₃ v h).3
    (p₃ v h).4.1)]) hy).elim fun x' ⟨hx, e'⟩ ↦ f.mp ?_
  choose k e using l.exists_apply_eq_nsmul a (by simpa [P.2.pow_mem_iff_mem] using!
    m ∘ .inr) j (fun g ↦ (x' (conjGal g)⁻¹, _)) ((hx.2.comp_continuous (by fun_prop)).prodMk hx.2)
    (by simp +contextual [mem_selmerModule_iff.1 hx, add_comm, by simpa [idOrConjInv] using
    (r₂ _ <| idOrConjInv_mem_inertiaAbove (τ := ·) a · (by simp [*]) ·)])
  -- a tame generator gives one at the conjugate place
  have : IsTameGeneratorFor _ (conjPlace c.place) (conjGal δ)⁻¹ := l.imp (by simp) fun ⟨π, y, u, e,
    h⟩ ↦ ⟨star π, unitsRep cmConj (unitsRep δ y), by simpa [a.conjPlace_star.isUniformiser_iff,
    a.isUniformiser_iff, DiscreteUnits.ext_iff, conjGal, ↓← map_inv, ← map_cycCharMod_mul,
    isComplexConj_cmConj.cycCharMod_eq_neg_one] using
    (⟨u, congr(unitsRep cmConj (unitsRep δ $e)), congr(-unitsRep cmConj $h)⟩ : _ ∧ _ ∧ _)⟩
  simp [*, idOrConjInv, cocycle_apply_inv Y, evalConjPair, -LinearEquiv.coe_curry_symm,
    @funext_iff Bool] at e e'
  simpa [← e, e', add_neg_eq_zero] using (R _ w.2).2.2 ![P, star P] ![c.place,
    conjPlace c.place] ![c.φ, _] ![δ, (conjGal δ)⁻¹] (by simp [(isSplit_of_q_prime n).symm])
    (by simpa [*, -h₁, a.conjPlace_star, F.conjPlace_conjGal]) _
    (mem_selmerZ1_of_mem_selmerModule (Submodule.smul_mem _ t (nsmul_mem hx k)) le_sup_left)

end

open Module Fintype IsLocalRing Polynomial LinearMap Submodule

/-- Tilting. Let O/I be Artinian, Φ₀, Φ₁: B → (O/I)^m linear, Y ⊆ B a submodule. For all s off
at most |m| residues, length(Y ∩ ker(sΦ₀ − Φ₁)) ≤ length(Y ∩ ker Φ₀ ∩ Φ₁⁻¹(Φ₀Y)). -/
lemma tilting {O m B} [CommRing O] [DVR O] [Fintype m] [AddCommGroup B] [Module O B]
    {I : Ideal O} [IsArtinian O (O ⧸ I)] (Φ₀ Φ₁ : B →ₗ[O] m → O ⧸ I) Y : ∃ T, List.length T ≤ card m
    ∧ ∀ s, residue O s ∉ T → length O ↥(Y ⊓ (s • Φ₀ - Φ₁).ker) ≤ length O ↥(Y ⊓ Φ₀.ker ⊓
    (Y.map Φ₀).comap Φ₁) := let Z := ⨆ s : O, Y ⊓ (s • Φ₀ - Φ₁).ker
  have z : Z ≤ (Z.map Φ₀).comap Φ₁ := iSup_le fun s y h ↦
    ⟨_, Z.smul_mem s (mem_iSup_of_mem s h), by aesop⟩
  have ⟨σ, e⟩ := projective_lifting_property _ ((I.mkQ.compLeft m).submoduleComap _)
    (Φ₀.submoduleMap_surjective Z)
  have q := e ▸ submoduleComap_surjective_of_surjective _ _ I.mkQ_surjective.comp_left
  (projective_lifting_property _ (Φ₁.restrict z ∘ₗ σ) q).elim fun ψ e ↦ ⟨(ψ.charpoly.aroots
    _).toList, by simp [(card_roots_map_le_natDegree _).trans, (finrank_le _).trans,
    charpoly_natDegree], fun s hs ↦ by
  simp [map_monic_ne_zero, charpoly_monic, eval_charpoly, ← isUnit_iff_isUnit_det,
    End.isUnit_iff] at hs
  grw [length_mono (le_inf (le_iSup _ s : _ ≤ Z) inf_le_right), ← ENat.add_le_add_iff_left,
    relLength_add_length_inf, ← relLength_add_length_inf _ Φ₀.ker] <;> simp [relLength_ker,
    length_ne_top]
  exact add_le_add (length_mono (Subtype.forall'.2 ((q.comp hs.2).forall.2 (⟨σ ·, by simp_all [
    DFunLike.ext_iff, -Subtype.forall]⟩)))) (length_mono (by grw [← (by simp [Z] : Z ≤ Y)]; order))⟩
end
