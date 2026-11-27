import New.Weil.TriangleArrows
import Lib.GaloisRep.LabelCompatibility
import New.Weil.LevelPlacesChosen

-- part: New.Exchange.ChainNorms
section
/-! Part of: Injectivity and norm of a chain of theta lifts (see New.Exchange.TriangleArrows).

This file: Chain of theta lifts is injective; its inner product and level index count. -/

namespace Data

open Finset Fintype Subgroup LevelPlaces
variable {P} (D : Data P) (ϑ : D.MFoldTwist)
seal dsKernel U

attribute [-simp] Bool.cond_eq_ite
attribute [local simp] Bool.cond_true Bool.cond_false

/-- There are a number C and an integer k such that, for all m-fold twists ϑ of modulus Q, [K₀ :
J_m] = C·N(Q)^k·δ^m·N_m/(N₀N₁^m). Here J_m is the level of `Data.lastResLevel`, δ =
`AuxPair.gramFactor` of the first auxiliary pair, N_n = `Data.triangleOrder` false ϑ n. -/
lemma stdLevelIndex_lastResLevel_eq : ∃ C, ∃ k : ℤ, ∀ ϑ :
  D.MFoldTwist, let w := triangleOrder false ϑ; stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) = C *
    card (D.𝔪 ϑ 0).ResRing ^ k * (D.auxPair ϑ 1).gramFactor ^ D.m * w D.m / (w 0 * w 1 ^ D.m) := by
  choose k K using card_parabolic_blockNumber D.RowIndex (Fin _)
  use D.triangleOrder false 1 0 * (D.triangleOrder false 1 1 / (D.auxPair .one 1).gramFactor) ^ D.m,
    (k 1 - D.t * card D.RowIndex) * D.m - k D.m, fun ϑ ↦ ?_
  let := Prop.linearOrder
  have f n w : _ = Nat.card (GL (D.GridIndex false 0 n) _) :=
    K n (ResField ((D.levelPlaces ϑ).twistPlace w)) ▸ index_mul_card _
  simp +instances [inf_top_eq, inf_bot_eq, ↓fun R [CommRing R] ↦ (ext fun _ ↦ forall₂_congr
    (by simp! [lt_iff_le_and_ne]) : parabolic (R := R) (· ∉ Set.range (.inl : D.RowIndex ↪ D.Y 1)) =
    parabolic (blockNumber 1)), AuxPair.gramFactor, auxPair, AuxPair.rankDiff, triangleOrder,
    triangleModulus, lastResLevel, ← f 1, ← f D.m, auxLevel, index_rangeParabolic,
    card_levelModulus_resRing, LevelPlaces.card_GL_levelModulus, field, card_ResField,
    relIndex_levelOf, Nat.card_pi, index_pi_univ, div_pow,
    prod_eq_zero_iff, zpow_sub₀, zpow_add₀, zpow_mul, prod_pow,
    -Nat.card_eq_fintype_card, Bool.cond_false, -Bool.cond_eq_ite,
    @univ_eq_empty (D.levelPlaces .one).TwistIndex _ ⟨nofun⟩]
  field_simp [prod_eq_zero_iff, NeZero.ne]; ring!

/-- For forms x, y of level g on U(Y₀), ⟨ι_ϑx, ι_ϑy⟩ = [K₀ : J_m]·d·⟨ux, uy⟩, where J_m = the level
of `Data.lastResLevel` ϑ, d the dimension of the weight on Y_m, u the chain of m weighted lifts
Y₀ → Y_m of the triangle. -/
lemma inner_iotaAtLevel x y : let u := weightedChain (D.triangleOrder false) (D.triLift _) ϑ 0 D.m;
    inner ℂ (D.iotaAtLevel ϑ x) (D.iotaAtLevel ϑ y) = stdLevelIndex (levelOf _ (D.lastResLevel ϑ)) *
    card (WeylIndex (D.Y D.m) D.columnsY) * inner ℂ (u x.1) (u y.1) := by
  rw [LevelForm.inner_eq_petersson (D.spaceY _) D.isHCParam_Y]
  congr <;> simpa [weightedChain, triangleOrder, triangleModulus,
    LevelPlaces.card_GL_levelModulus] using! (D.spaceY _).ofAlgForm_toAlgForm D.isHCParam_Y _

/-- For every twist ϑ whose first m powers are twists, the composite ι_ϑ of the m theta lifts from
U(Y₀) to the definite U(Y_m) is injective on forms of principal level g on U(Y₀).

Proved from the norm formula `inner_iotaAtLevel`. -/
@[simp] lemma iotaAtLevel_injective : Function.Injective (D.iotaAtLevel ϑ) := .of_ker _ fun y e ↦
  (D.exists_isTriangle _).choose_spec.eq_zero_of_weightedChain D.m 0 (by simp) _
  (by simpa [e, -Fintype.card_pi] using! D.inner_iotaAtLevel ϑ y y)
end Data
end

-- part: New.GaloisRep.LabelUniqueness
section
/-! Part of: Good forms on different unitary groups have equal traces (see
New.Trace.GoodFormTransfer).

This file: Given an injective lift to forms on a definite group, a Hecke eigensystem has at most one
primitive label at a chosen place over g. -/

open Matrix Polynomial Finset minpoly
variable {P n} (D : Data P) {s : D.RowIndex → ℤˣ} (V : Space D.E _ s) [Fintype n]

lemma Data.isEigenform_of_hasHeckePolyAt {M} {f : Gf _ n → M → ℂ} (h0 : f ≠ 0) {Q} (h : ∀ w
    (h : D.IsSplitOffLevel w), HasHeckePolyAt f w h.1 (Q w)) : IsEigenform f Q :=
  ⟨h0, (eventually_notMem_star_notMem 1 (image D.chosen ⊤)).mono
  fun w _ q ↦ ⟨_, h w ⟨isSplit_of_q_prime q, by simp_all⟩⟩⟩

/-- Let L inject level g forms on V into definite algebraic forms, make the p-part spherical with
fixed eigenvalues at split places off g, and intertwine the parabolic action at x up to ψ∘det and
distinct χ_l∘det, of orders dividing Mω. Then `Data.occurringLabels` V p x has at most one element.

This is one step toward showing that good forms on different unitary groups have equal traces. -/
lemma Data.occurringLabels_subsingleton {v : _ ↪ n} {S J χ' κ ν} {L : _ →ₗ[ℂ] LevelPlaces.LevelForm
  S J χ' κ ν} [Nonempty n] (hL : (⇑L).Injective) {p} {F : _ → _} (hF : ∀ y ∈ D.eigenPart V p, ∀ w
  (h : D.IsSplitOffLevel w), IsSphericalWith (rightRegular ..) h.1 (F w) (L y).toSmoothForm.1) x {m
  b} χ ψ (hk : ∀ y, HasParahoricType (s := m) (L y).toSmoothForm.1 (D.isConjApart_chosen.2 x x) v b
  ψ χ fun g ↦ (L (D.principalRep V (Pi.mulSingle x g) y)).1.1) (hχ : χ.Injective) (hψ : ψ ^ P.Mω D.s
  = 1) (hM : ∀ l, χ l ^ P.Mω D.s = 1) : (D.occurringLabels V p x).Subsingleton := fun _ J _ J' ↦ by
  choose! t e using fun w (h : _ ≠ w) ↦ exists_heckeSplit_eq_smul (hw := h) (π :=
    rightRegular ℂ (Gf _ n) (WeylIndex n κ → ℂ)) (F w)
  let T := faithfulChar (ResField (D.chosen x))
  obtain ⟨_ : ThePrime 2, _ : PadicIso 2, s, G⟩ := {},
    ⟨(exists_ringEquiv_extend mk_complex_eq_mk_padicAlgCl (Rat.castHom _) (algebraMap ..)).choose⟩,
    (exists_isTameExponent T (D.chosen x).isPlaceOver_placeOver _).1
  have k {c} (J : c ∈ D.occurringLabels V p x) := J.2.elim fun y a ↦
    have z := J.1.scaleRoots _ (charName_pow_eq_one hψ) (D.dvd_card_resField_sub_one x).2.1
    have H := (hk y).hasProductLabel ((AlgForm ..).subtype.domRestrict _ ∘ₗ L) (fun _ _ h ↦
      hL congr(⟨⟨$h, _⟩, _⟩)) a.2 hχ fun _ ↦
      z.2.1.not_isRoot_of_natDegree_ne_one (z.1.2.2.1 ▸ D.nat_lt_of_hasLogBound.ne')
    have E := D.isEigenform_of_hasHeckePolyAt (H.2.2.2.2 <| by simp [·]) (hF y a.1 · · |> fun b ↦
      ⟨b.1, _, rfl, e _ _ _ b⟩)
    (⟨z, (sphericalCompat_std x.2 (L y).toSmoothForm.2 E).1, fun {r} h ↦
      (Attached.isLabelledAt (r := r) (L y).toSmoothForm.2 E h H G.1).2.2 G⟩ : _ ∧ _ ∧ _)
  obtain ⟨⟨i, ⟨r, h⟩, B⟩, ⟨i', -, B'⟩, l⟩ := k J, k J', G.1.valuation_natCast_eq_one_iff.2
    (Nat.not_dvd_of_pos_of_lt two_pos D.nat_lt_of_hasLogBound ∘ (FinPlace.natCast_mem_iff_dvd _
    x.2.2.2).1)
  have e j := by simpa using congr(ιℓ (T (algebraMap _ _ (charName T $(hM j)).1)))
  refine (scaleRootsEquiv (charName T ψ)).injective (by_contra fun hN ↦
    i.isPrimitiveRoot_prod_roots.1.pow_ne_one_of_pos_of_lt NeZero.out (D.dvd_card_resField_sub_one
    x).2.2.le_pred (IsFaithfulMulChar.injective (ιℓ.injective ?_)))
  simpa [← det_eq_prod_roots_charpoly, Multiset.nsmul_singleton, roots_multiset_prod, roots_mul, e,
    Polynomial.map_prod, map_multiset_prod, Multiset.map_bind, prod_eq_zero_iff, roots_prod, aroots,
    X_ne_C, List.prod_ofFn, i.2.1.ne_zero, ← prod_pow, ← pow_mul, pow_mul', mul_pow, T, (B h).2 l]
    using (MonoidHom.mker (powMonoidHom (P.Mω D.s))).multiset_prod_mem _ fun _ ↦ by
    clear * - hN i i' e
    simp_all [eval_multiset_prod, prod_eq_zero_iff, ← eq_iff_aeval_eq_zero, IsPrimitiveLabel,
      IsLabel, scaleRootsEquiv]
    grind [IsFaithfulMulChar] ∘ imp_and.2 ⟨isRoot_of_isRoot_charpoly ((B h).1.1 l),
    isRoot_of_isRoot_charpoly ((B' h).1.1 l)⟩ ∘ isRoot_of_mem_roots
end

-- part: New.Trace.LabelRigidity
section
/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Good forms on different unitary groups have equal traces (see New.Trace.GoodFormTransfer).

This file: A Hecke eigensystem meets at most one primitive cuspidal type at a chosen place. -/

set_option backward.isDefEq.respectTransparency false

/-- Let w in M be split, u of level `AuxPair.levelGroup` and character `AuxPair.auxLevelChar`,
π(k)u = kf for k in GL_n(E_w), F(g) = `AuxPair.chosenGLRep`(g at w)u. Then `HasParahoricType` holds:
integral k preserving the ι-span mod w, with ι-block x, give kf = ψ_w(det x)⁻¹F(x). -/
lemma Data.hasParahoricType_chosenGLRep {P} (D : Data P) {n} [Fintype n] {r} [Fintype r] {O :
  AuxPair D.E r n} {S : Submodule ℂ (_ → WeylIndex n O.κ → ℂ)} {π : Representation ℂ _ S} {u i v f}
  (e : ∀ k, (π (atSplit v k) u.1).1 = rightRegular ℂ _ _ (atSplit v k) f) :
  HasParahoricType f v O.incl (if · ∈ Set.range O.incl then 0 else 1) (O.ψ _)⁻¹ (s := 1) 1 fun g ↦
  (O.chosenGLRep π (Pi.mulSingle i g) u).1.1 := by
  use by simp, fun k g a b ↦ e _ ▸ congr($(O.smul_chosenGLRep_eq u (Sum.rec (Pi.mulSingle i g) 1)
    (reduceFamily_atSplit (.inl i) k) (Sum.rec (fun j ↦ ?_) (by simp))).1).symm.trans (by
    simp +contextual [Finset.prod_eq_single i, -Matrix.GeneralLinearGroup.val_det_apply]; rfl)
  obtain rfl | _ := eq_or_ne j i <;> simp [*]
  erw [← b, mul_inclMatrix, eq_inclMatrix_mul_iff]
  aesop

/-- For every eigensystem p and every chosen place x over g, at most one primitive label occurs
at x in the p-part of the forms on V (`Data.occurringLabels`). -/
abbrev Data.HasRigidLabels {P} (D : Data P) {s} (V : Space D.E D.RowIndex s) := ∀ p x,
  (D.occurringLabels V p x).Subsingleton

/-- For 1 ≤ j ≤ m, the space W_j satisfies `Data.HasRigidLabels`: at each chosen place over g, at
most one primitive label of degree r occurs in each p-part of the forms on W_j. -/
lemma Data.hasRigidLabels_spaceW {P} (D : Data P) (j : D.LiftIndex) : D.HasRigidLabels (D.spaceW
  j) := fun p x ↦ D.occurringLabels_subsingleton _ (D.auxLift_injective .one) (fun _ h _ a ↦
  D.lifts_auxLift _ h _ a.1 (by simp_all [auxPair, levelPlaces, IsSplitOffLevel]; tauto)) x 1 _
  (fun _ ↦ by simpa [auxLift_principalRep] using! D.hasParahoricType_chosenGLRep fun _ ↦ rfl)
  (fun _ ↦ by lia) (by simpa using! D.omega_zpow_mul_pow_eq_one _ rfl) (by simp)

/-- Y₀ satisfies `Data.HasRigidLabels`: for each eigensystem p and chosen place above g, the
idempotent e_c kills the p-part for all but at most one primitive label c of degree r. -/
lemma Data.hasRigidLabels_spaceY_zero {P} (D : Data P) : D.HasRigidLabels (D.spaceY 0) :=
  fun p x ↦ by
  refine D.occurringLabels_subsingleton _ (D.iotaAtLevel_injective 1) (D.exists_isSphericalWith_iota
    p).choose_spec x _ 1 (fun y ↦ ⟨blockNumber_eq_zero _, fun k g h e ↦ congr($(D.algFormRep_iota _
    _ y _ _ (reduceFamily_atSplit (.inl x) k) (Sum.rec ?_ (by simp)) ?_).1).trans
    (by rw [Finset.prod_eq_single (.inl x)] <;> simp_all [-Finset.prod_mul_distrib,
    Matrix.toSquareBlock, Matrix.toSquareBlockProp, -Matrix.GeneralLinearGroup.val_det_apply];
        rfl)⟩) (fun a b h ↦ by_contra fun e ↦ ((D.omega_zpow_ne_one (a - b)) _).2 x.2.2.1 ?_)
    (by simp) fun _ ↦ D.omega_zpow_mul_pow_eq_one _ (one_pow _)
  iterate 2 exact (by cases eq_or_ne · x <;> aesop)
  simp_all [TameChar.pow, (1 : D.MFoldTwist).1.ψ_eq_one x.2.1 nofun, chosen, sub_eq_add_neg,
    zpow_add]
end
