import Lib.Adelic.LocalHomUnit
import New.Weil.AlgebraicPartDefs
import New.Weil.TriangleLevelExponent

section
/-! Part of: Injectivity and norm of a chain of theta lifts (see New.Exchange.TriangleArrows).

This file: Abstract triangle of maps: chains are injective, Gram determinant factors over first
arrows. -/

open ComplexInnerProductSpace Finset Module ComplexConjugate


variable {I V : Type} {F : ℕ → ℕ → Type} [∀ i n, NormedAddCommGroup (F i n)] [∀ i n,
  InnerProductSpace ℂ (F i n)] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (m) (w : I → ℕ → ℕ)
  (M : ℕ → (I → ℂ) → Prop) (a : I → ∀ i n, F i n →ₗ[ℂ] F i (n + 1))
  (d : I → ∀ i n, F i (n + 1) →ₗ[ℂ] F (i + 1) n) (j : ∀ i, V →ₗᵢ[ℂ] F i 0) (G : Prop)
attribute [local simp] compUpTo inner_smul_right NeZero.ne

/-- A triangle of inner product spaces with arrows a, d: weighted squares commute up to scalars
(under G graded by M, with an adjoint law); between the copies of V, a is adjoint to d and
da is injective. -/
structure IsTriangle where
  cost_one : M 0 1
  cost_mul {n n' N c c'} : M n c → M n' c' → n + n' ≤ N → M N (c * c')
  square_law i n (h : i + (n + 1) < m) : ∃ β, (∀ t y z, w t n * ⟪z, a t _ n (d t i n y)⟫ =
    conj (β t)⁻¹ * w t (n + 2) * ⟪z, d t i _ (a t i _ y)⟫) ∧ (G → M 1 β ∧ ∃ κ, M 0 κ ∧ ∀ t z, ∃ x,
    (∀ y, ⟪a t i _ y, z⟫ = ⟪y, x⟫) ∧ ∀ y, ⟪d t i n x, y⟫ = κ t * ⟪d t i _ z, a t _ n y⟫)
  length_one i (h : i < m) t y : (∀ z, ⟪z, a t i 0 (j i y)⟫ = ⟪d t i 0 z, j _ y⟫) ∧
    ∃ v, j _ v = d t i 0 (a t i 0 (j i y)) ∧ (v = 0 → y = 0)

/-- The composite F(i,0) → F(i,n) of the first n arrows a in row i, the k-th multiplied by its
weight w(t,k). -/
noncomputable abbrev weightedChain t i := compUpTo fun n ↦ (w t n : ℂ) • a t i n

variable {m w M a d j G} (h : IsTriangle m w M a d j G) [∀ t n, NeZero (w t n)]
include h

lemma IsTriangle.weightedChain_descent i n (hi : i + n < m) : ∃ β κ, (∀ t y,
  weightedChain w a t _ n (d t i 0 (a t i 0 y)) = (w t n.succ / w t 1 / w t 0 / conj (β t) : ℂ) • d
  t i n (weightedChain w a t i _ y)) ∧ (G → M n (κ * β) ∧ ∀ t y z, ⟪z, a t i n
  (weightedChain w a t i n (j i y))⟫ = κ t * ⟪d t i n z, weightedChain w a t _ n (j _ y)⟫) := by
  induction' n with n H; use 1, 1; simp [h.1, h.4 i hi]
  choose _ _ e r u using H hi.le; choose! _ f s _ c _ p q using h.3 i n hi
  refine ⟨_, _, fun t y ↦ ext_inner_left ℂ ?_, fun g ↦ ⟨(mul_mul_mul_comm ..).subst (h.2 (r g)
    (h.2 (c g) (s g) .refl) .refl), ?_⟩⟩ <;> simp [← inner_conj_symm _ (a _ i n.succ _), *, field]

/-- In a triangle of size m, for i + n ≤ m the weighted composite of the first n arrows in row i
is injective on the image of V under j i. -/
lemma IsTriangle.eq_zero_of_weightedChain {t} : ∀ n i, i + n ≤ m → ∀ y,
  weightedChain w a t i n (j i y) = 0 → y = 0 := Nat.rec (by simp [norm_map, ← norm_eq_zero]) fun _
  _ i hi y ↦ by grind [h.weightedChain_descent _ _ hi, h.4 i (by lia) t y, smul_zero]

/-- In a triangle with G, let w₀⟪a x, a s y⟫ = ⟪x, s S_i y⟫ for the first arrow a of each row i < m.
For i + n = m the weighted n-chain of row i has Gram form κ(w₀w₁ⁿ/w_n)⟪x, s T y⟫, det T = ∏_{i≤k<m}
det S_k, with M(n², κ). -/
lemma IsTriangle.inner_weightedChain_eq (hG : G) {U} [AddCommGroup U] [Module ℂ U] {s : U → V} (S :
  I → ℕ → End ℂ U) (hS :
  ∀ i < m, ∀ t x y, w t 0 * ⟪a t i 0 (j i x), a t i 0 (j i (s y))⟫ = ⟪x, s (S t i y)⟫) : ∀ n i,
  i + n = m → ∃ κ, M (n * n) κ ∧ ∀ t, ∃ T : End ℂ U, T.det = ∏ k ∈ Ico i m, (S t k).det ∧ ∀ x y,
  ⟪weightedChain w a t i n (j i x), weightedChain w a t i n (j i (s y))⟫ = κ t * (w t 0 * w t 1 ^
  n / w t n) * ⟪x, s (T y)⟫ := Nat.rec (fun _ _ ↦ ⟨_, h.1, fun _ ↦ ⟨1, by aesop⟩⟩) fun n H i hi ↦ by
  choose _ k T _ E using H i.succ (by lia); choose β _ e l _ using h.weightedChain_descent i n hi.le
  choose g z q p using h.4 i (by omega)
  refine ⟨_, h.2 (l hG) k (by lia), fun t ↦ ⟨S t i * T t,
    by grind [prod_eq_prod_Ico_succ_bot], fun x y ↦ ?_⟩⟩
  specialize E t (z t x) y; simp [*, field] at E ⊢
  grind [(j _).inner_map_map, h.eq_zero_of_weightedChain (t := t) n i.succ, zero_smul,
    inner_zero_left]
end

section
/-! Part of: Non-lifts sharing one Hecke root have zero theta periods (see
New.Rows.MemberOrthogonality).

This file: Vanishing descent for one level datum passes to all data, via reflection sums. -/

open Classical Finset Fint Gf IsLocalRing Kf MatMul Matrix Space Valued

variable {E r n} [Field E] [CMType E] [Fintype r] [Fintype n] {O : AuxPair E r n}

lemma AuxPair.exists_atPlace_eq {m} [Fintype m] g : g ∈ (supportedOn m O.places).map (.pi fun i ↦
  atPlace (O.placeAt i)) := Subgroup.pi_mem_of_mulSingle_mem g fun i ↦
  ⟨atSplit (O.apart.2 i i) (g i), by simp; grind [atPlace_atSplit_of_ne],
  Function.eq_update_iff.2 (by simp_all [atPlace_atSplit_of_ne, O.apart.1.ne, O.apart.2])⟩

attribute [local simp] prod_eq_zero_iff vecMulVec_apply MulChar.star_apply' AuxPair.resDetDatum
  AuxPair.auxLevelChar add_mul residueDatum inclMatrix mul_assoc starRingEnd_apply matToVec v_inv

lemma AuxPair.exists_annihilator_or_congr_inclMatrix {ι : r ↪ n} {w : FinPlace E} (x :
  Matrix n r (LocField w)) (h : HasLeftInv x) : ∃ l :
  Matrix n n _, l.map (LocInt w).subtype * x = 0 ∧ ((∀ c, residue _ ∘ l c ∘ ι = 0) → ∃ a : GL r
  (LocField w), ∀ i j, v ((x * a.1) i j - inclMatrix (LocInt w) ι i j) < 1) := by
  obtain ⟨b, -, h⟩ := (isValuationPair_valuationSubring (LocInt w)).exists_isPrimitiveMatrix_mul h
  obtain ⟨P, ⟨L, e⟩, rfl⟩ := by simpa [← mul_inv_eq_iff_eq_mul_of_invertible] using
    h.exists_map_subtype_eq
  use P * L - 1, (congr($Matrix.map_mul * _).trans (Matrix.mul_assoc ..)).symm.trans (by simp
    [e]), fun H ↦ (isUnit_of_mapMatrix _ (.of_mul_eq_one_right _ (ext
    (by simpa [mul_apply, funext_iff] using H <| ι ·)))).elim fun T e ↦ ⟨b * .map (algebraMap ..) T,
    by simpa [↓Matrix.mul_assoc, e, mul_apply] using!
    (residue_eq_iff_valuation_sub_lt_one.1 <| congrFun₂ (funext H) · ·)⟩

seal CStarMatrix in
/-- Let k ∈ K₀ have reductions τ_j with ι×ι block s_j and ι-columns (at M), ι-rows (at Q) zero
outside that block. On y of the pair's level and character, π(k)y is ∏_j ψ_j⁻¹(det s_j)
times `AuxPair.chosenGLRep` of (s_j)_{j∈M} applied to y. -/
lemma AuxPair.smul_chosenGLRep_eq {V} [AddCommGroup V] [Module ℂ V] {π :
  Representation ℂ _ V} y {k τ} (s : ∀ _, GL r _) (e : reduceFamily O.placeAt k = τ) (H : ∀ j,
  cond j.isLeft (τ j).1 (τ j).1ᵀ * inclMatrix _ O.incl = inclMatrix _ O.incl * cond
  j.isLeft (s j).1 (s j).1ᵀ) : (∏ j, (O.ψ _)⁻¹ (s j).1.det) • (O.chosenGLRep π (s <| .inl ·) y).1 =
  π k y := set_option backward.isDefEq.respectTransparency false in (smul_smul ..).trans (by
  let S := firstBlockHom _ O.incl (s <| .inl ·)
  have := by simpa [entrywise] using (H <| .inr ·)
  have T j : S (.inr j) = 1 := rfl
  simpa [*, MulChar.inv_apply_eq_inv', submatrix, MulChar.apply_eq_zero_iff] using! congr(π
    (liftResidue S) $(levelSpace_levelOf_apply y.2 ((liftResidue S)⁻¹ * k) ⟨S⁻¹ * τ,
    Sum.rec (by simpa [↓mem_stabilizer_col_iff, S, firstBlockHom, -inclMatrix,
    inv_mul_eq_iff_eq_mul_of_invertible] using (H <| .inl ·)) (by simp +contextual
    [mem_rangeParabolic_iff, *, eq_comm])⟩ (by simp [reduceFamily_liftResidue, e]))).symm)

lemma AuxPair.isAutomorphic_star_algFormCoeff u (y : O.FormV) :
  (stdSpace ..).IsAutomorphic (star (algFormCoeff 1 u y.1)) := (isAutomorphic_algFormCoeff y.1).conj

attribute [-simp] Sum.elim_inl Sum.elim_inr map_sub submatrix_id_mul

/-- Suppose ψ ≠ 1 at each place of Q, the reflection sums of all nonzero rows at M kill y, and
the conjugate u-coordinate of y has zero descent to W for all data P ⊗ Υ. Then its descents
vanish for all data vacuum off M, Q and conjugates. -/
lemma AuxPair.descentsVanish_of_reflectionSum [WeilData E]
    {y} u (hQ : ∀ i, O.ψ (O.twistPlace i) ≠ 1)
    (hM : ∀ i (v : ∀ _, _), v i ≠ 0 → O.formAction.asAlgebraHom (piTensorElem fun i ↦
  reflectionSum (O.ψ _) (v i)) y = 0) (h0 : ∀ P, lift (pairThetaKer _ _ O.a 1).swap (integrated _
  (polyVector _ P) O.auxDatum.1) (star (algFormCoeff 1 u y.1)) = 0) : DescentsVanish O.W (stdSpace E
  n) O.a O.places.conjClosureᶜ (star (algFormCoeff 1 u y.1)) := fun f hf ↦ funext fun g ↦ by
  obtain ⟨hy, hS⟩ := isAutomorphic_star_algFormCoeff u y,
    (by clear * -; grind [O.apart.2] : O.places.IsConjDisjoint)
  let K := (pairThetaKer O.W (stdSpace _ n) O.a 1).swap
  refine (K.exists_clm_lift hy.mem_rapidFunctions).elim fun L hL ↦
    hL .. ▸ ext_integrated _ hf fun P q h ↦ ?_
  erw [_root_.smul_apply, map_smul, map_smul, (?_ : finVec q = _), ← projOn_vacElem,
    ← name_schrodingerAct_boxIndicator hS (y := q), ← hL, mul_eq_zero]
  swap; ext : 3 <;> simp +contextual [finVec, idem_apply, h]
  let D := ((K.liftBilin ∘ₗ (integrated _ P ∘L .apply ℂ _ (vacElem _)).1 ∘ₗ name _ O.places).compr₂
    (.proj g)).compl₂ (.codRestrict _ ((starLinearEquiv ℂ).1 ∘ₛₗ (algFormCoeff 1 u).domRestrict _)
    (isAutomorphic_star_algFormCoeff u · |>.mem_rapidFunctions))
  refine .inr (IsSchwartzBruhat.mem_of_cosets (S := O.places) (D.flip y).ker fun _ _ ↦
    ⟨⊤, by simp, fun t z _ _ ↦ ?_⟩)
  let C z := D (cosetIndicator O.places t z)
  have lv (A B : ∀ j, Matrix n r (LocInt (O.placeAt j))) (s : ∀ j, GL r (ResField (O.placeAt j))) z
    q (X : ∀ j, let τ := (1 + A j * (B j)ᵀ).map (residue _); (s j).1 =
      (1 + (B j)ᵀ * A j).map (residue _) ∧ τ.submatrix O.incl O.incl = (s j).1 ∧
      ∀ b ∉ Set.range O.incl, ∀ a, cond j.isLeft τ τᵀ b (O.incl a) = 0) (H : ∀ j a b, t⁻¹.1 _ * (q
    (a, b) _ - ((1 + A j * (B j)ᵀ).map Subtype.val * (vecToMat z).map (evalAt (O.placeAt j))) a b) ∈
    LocInt _) : C q ((∏ j, (O.ψ _)⁻¹ (s j).1.det) • O.formAction (s <| .inl ·) y) = C z y := by
    obtain ⟨k, hk, e⟩ := exists_atPlace_eq fun j ↦
      .map (LocInt _).subtype (.mk'' _ ((det_one_add_mul_comm
      ..).substr ((isUnit_of_mapMatrix (residue _) ⟨_, (X j).1⟩).map detMonoidHom)))
    lift k to Kf E n using (mem_Kf_iff_of_supportedOn hk).2 fun _ ⟨j, h⟩ ↦ h ▸ ⟨_, congr($e.symm j)⟩
    refine .trans ?_ (mul_one g ▸ K.lift_equivariant hy _ k ..).symm
    erw [pairWeil_integrated_fin _ _ _ _ 1 k.1, pairWeil_name_of_mem hS (one_mem _) k.2]
    refine congr(lift _ (integrated _ _ (name _ _ $(funext fun x ↦ if_congr ?_ rfl rfl) $(by
      simp [↓pairWeil_eq_smul_of_projOn_eq ⊤]))) (star $((congrArg _
      (smul_chosenGLRep_eq y _ (funext (reduceAt_eq_of_atPlace congr($e ·))) fun j ↦
      (mul_inclMatrix ..).trans <| ((eq_inclMatrix_mul_iff _).2 (X j).2.2).trans ((X j).2.1 ▸ by
      cases j <;> rfl))).trans (funext (algFormCoeff_algFormRep u k)))) _)
    simpa [↓mulVec_smul, ↓mulVec_sub, ↓mulVec_add, ← smul_add] using ((mulVec_mem_integralBox
      (g := (G.onHom (s' := 1) ((g.1, 1), k)).2⁻¹) (by simp [mem_Kf_iff.1])).trans
      (add_mem_cancel_right (y := t⁻¹.1 • (x - q)) (x := t⁻¹.1 • (q - matToVec (k.1.1.1 * vecToMat
      z))) fun a ↦ idem_mul_mem_Ô.2 (Set.forall_mem_range.2 fun j ↦ congr(_ * (_ -
      $(Matrix.map_mul.trans congr(($e j).1 * _)) _ _) ∈ _).mpr (H ..)))).symm
  let d j a : LocInt (O.placeAt j) :=
    ite (j.isRight ∧ ∀ b, a ≠ O.incl b) ⟨_, (v_uniformizer _).trans_le (by tauto)⟩ 1
  choose! l hl a ha using fun j ↦ exists_annihilator_or_congr_inclMatrix (ι :=
    O.incl.trans .inl) ((diagonal (d j · |>.1) * (vecToMat z).map (evalAt (O.placeAt j))).fromRows
    (scalar r (t.1 _))) ⟨fromCols 0 (scalar r (t⁻¹.1 _)), by simp⟩
  set_option backward.isDefEq.respectTransparency false in
    let m c j := residue _ ∘ l j c ∘ .inl ∘ O.incl
    by_cases! N : ∀ j c, m c j = 0
    · obtain ⟨⟨A, hA', rfl⟩, _⟩ := exists_atPlace_eq a,
        isSchwartzBruhat_residueDatum O.resDetDatum O.apart.2
      let Ψ x := residueDatum _ O.resDetDatum ((G.onHom (s' := 1) ((g.1, A), 1)).2⁻¹.1.1 *ᵥ x)
      have H q (hq : Ψ q ≠ 0) : Ψ q * C q y = C (matToVec (inclMatrix _ O.incl * A⁻¹.1.1)) y := by
        obtain ⟨hx, m, p⟩ := by simpa [Ψ, -Sum.forall] using hq
        let Z i : Matrix n r (LocInt _) := (⟨_, hx i · ·⟩)
        refine .trans (by simp [*, Ψ, ← Pi.one_def]) (lv (Z · - inclMatrix _ O.incl) (fun _ ↦
          inclMatrix _ O.incl)
          (Sum.rec 1 (.mk'' _ <| MulChar.apply_ne_zero_iff.1 <| p ·)) _ q ?_ fun j a b ↦ ?_)
        · rintro (j | j) <;> simp +contextual [entrywise, ↓m, @eq_comm n, show _ = (vecToMat q *
            A.1.1).map (residueOrZero ∘ evalAt _) _ _ from (residueOrZero_coe (Z ..)).symm]
        rw [vecToMat_matToVec, Matrix.map_mul, map_inclMatrix, ← Matrix.mul_assoc, mul_inclMatrix,
          submatrix_map, show submatrix _ _ _ = Z j by simp [entrywise]]
        erw [← Matrix.map_mul (f := evalAt _)]; simp [vecToMat]
      have h i a := by simpa [atPlace, ← Matrix.map_mul] using ha i (N i) (.inl a)
      have I i a b : (vecToMat z * A.1.1) a b _ ∈ LocInt _ := if c : d i a = 1 then by
        simpa [c] using! v.map_add_le (h i a b).le (inclMatrix (LocInt _) O.incl a b).2 else by
        simpa [d, (ite_ne_right_iff.1 c).1] using! v_uniformizer_inv_mul_le_one_iff.2 (h i a b)
      have J i a b (c : d i a = 1) := (residueOrZero_coe ⟨_, I ..⟩).trans
        (residue_eq_iff_valuation_sub_lt_one.2 (by simpa [c] using h i a b))
      have hz : Ψ z ≠ 0 := by simp [Ψ, ← ext_iff, *, d, submatrix, ← diagonal.eq_1]
      obtain ⟨F, hF, h⟩ := IsSchwartzBruhat.eq_sum_cosetIndicator (S := O.places) (Ψ :=
        Ψ) t fun x _ z h ↦ residueDatum_congr _ fun i p ↦ by simpa [↓← mulVec_sub, mul_apply,
        ← evalAt_apply] using (v.map_sum_lt one_ne_zero fun c ↦ by simpa [field] using!
        (mul_lt_of_le_one_of_lt (idem_mul_mem_Ô.1 (h _) _ ⟨i, rfl⟩) (ha i (N i) (.inr c) _)))
      have e := congrFun (h0 P) (g * A)
      erw [lift_mul_right, hL, pairWeil_integrated_fin (k := A), auxDatum, Subtype.coe_mk,
        liftFn_eq_residueDatum places_levelModulus, places_levelModulus, pairWeil_name_on hS hA'
        (by simp), map_smul, map_smul, ← hL, (congr(D.flip y $(.trans (by simp [Ψ]) h)) : lift
        .. = _), map_sum, sum_eq_card_nsmul fun q ↦ (map_smul ..).trans ∘ H q ∘ hF q, ← H z hz] at e
      exact (by simpa [hz] using e :).resolve_left (hz <| h ▸ · ▸ by simp)
    have H c s (h : ∀ j, ∃ x, (s j).1 = 1 + vecMulVec x (m c j)) := (skolem.1
      (residue_surjective.comp_left.exists.1 <| h ·)).elim fun x hx ↦ lv (fun _ ↦ inclMatrix _
      O.incl) (fun j ↦ vecMulVec (l j c ∘ .inl * d j) (x j)) s z z (by simp +contextual [entrywise,
      hx, m, d, ← residueOrZero_coe ⟨(uniformizer _).1, _⟩, @eq_comm n]) fun j a b ↦ by
      simp [mul_vecMulVec, mul_apply, ← mul_sum, vecToMat, apply_ite, by
        simpa [mul_apply, add_eq_zero_iff_eq_neg, diagonal, vecToMat] using congrFun₂ (hl j) c b]
      simpa [mul_comm (t.1 _)⁻¹] using ((_ *ᵥ x j) a * l j c (.inr b)).2
    obtain ⟨i | i, c, hv⟩ := N
    · exact (smul_eq_zero_iff_right (card_ne_zero.2 ⟨1, by simp⟩)).1 ((sum_eq_card_nsmul fun s h ↦
        .trans (by simp; tauto) (H c (Sum.rec s 1) (Sum.rec (mem_filter.1 h).2
        (by simp)))).symm.trans
        (by simpa [reflectionSum, asAlgebraHom_eq_sum, ↓prod_ite_zero, sum_ite] using
        congr(C z $(hM i (m c <| .inl ·) hv)) :))
    obtain ⟨⟨t, ht⟩, b, hb⟩ := (O.ψ (O.placeAt (.inr i))).ne_one_iff.1 (hQ i), Function.ne_iff.1 hv
    have e : (1 + vecMulVec (Pi.single b ((t.1 - 1) / m c _ b)) (m c (.inr i))).det = t := by
      simp [vecMulVec_eq Unit, det_one_add_mul_comm, mul_div_cancel₀ _ hb]
    refine eq_zero_of_mul_eq_self_left ht (.trans ?_ (H c (Pi.mulSingle _ (.mk'' _ (e ▸ t.isUnit)))
      fun j ↦ (eq_or_ne j (.inr i)).elim (· ▸ ⟨_, by simp; rfl⟩) (by simp [·])))
    simp +contextual [prod_eq_single i, e, ← Pi.one_def, C]
end

section
/-! Part of: Non-lifts sharing one Hecke root have zero theta periods (see
New.Rows.MemberOrthogonality).

This file: Climbing the theta tower: bounded descents with a too small Hecke root vanish. -/

open Matrix MeasureTheory WeilData Space Splitting Finset Fintype Real G MatMul
variable {E r n m p} [Field E] [CMType E] [WeilData E] [Fintype r] [Fintype n] [Fintype m]
  [Fintype p] {s t} {W : Space E r s} {W' : Space E m t} {V : Space E n 1} {a S Y}
  (h0 : DescentsVanish W V a S Y) (D : W'.Splitting W p)

omit [WeilData E] in
/-- Let F be a bounded function on the adelic unitary group of rank m, spherical at a split
place w and killed by the Hecke polynomial at w evaluated at X. If q_w^{m+1}|X| ≤ 1, then F
= 0. -/
lemma eq_zero_of_heckePolyOp_eq_zero {F w X} (hw : w.IsSplit) (hK : F ∈ sphericalAt (finRightRep E
  t) w) (h : heckePolyOp (finRightRep ..) hw X F = 0) (hX : w.q ^ (card m + 1) * ‖X‖ ≤ 1) (b :
  BddAbove (.range (‖F ·‖))) : F = 0 := have P := q_binomial_submodule m (ResField w) ⊤ (-‖X‖); by
  let r U : G E t := (1, atSplit hw (transposeGL (basicCosetRep U)))
  refine' funext (norm_le_zero_iff.1 <|
    maximum_principle b (heckePolyCoeff X) (· / r ⊥ * r ·) (l := 2) _ (fun g
    ↦ _) ·) <;> simp [funext_iff, heckePolyCoeff, heckePolyOp_eq_sum hw hK, -Prod.forall] at *
  norm_cast at *; grw [P, card_ResField, prod_one_add_le_exp_sum _ (by bound), ← lt_log_iff_exp_lt
    two_pos, ← sum_mul, ← log_two_gt_d9, ← Nat.cast_sum, Nat.geomSum_lt w.one_lt_q fun _ ↦
    mem_range.1, pow_succ, ← Nat.mul_le_mul_left _ w.one_lt_q] at *; grind
  simpa [h, r, two_mul, le_sub_iff_add_le] using norm_sum_le (univ.erase ⊥) fun U ↦
    heckePolyCoeff X U * F (g / r ⊥ * r U)

include h0 D
attribute [local simp] sourceTerm lt_sqrt lCoord CharUnramifiedAt AutChar.frobValue
  kronecker_mulVec_eq_matToVec name_boxIndicator projOn_empty
  Splitting.zeroTerm_apply coordMatrix kAdelic

lemma DescentsVanish.integral_sourceTerm_eq_zero [IsBaseAdapted D] {f} (hf : projOn _ S f =
  f) g : ∫ h, θ _ (D.sourceTerm V 0 (pairWeil _ V (a * upsilonU1 ^ card p) 1 (g, h) f)) * Y
  h ∂V.quotMeasure = 0 := by
  choose κ hκ t _ _ c z u e using D.iwasawa g
  simp [show ∀ h : G E 1, (g, h) = (D.radicalElt c z, 1) * (D.levi (t, u),
    h) * (κ⁻¹, 1) by simp [← e], -Prod.mk_mul_mk, -sourceTerm, -sourceTerm_zero,
    sourceTerm_radicalElt, sourceTerm_levi, mul_assoc]
  exact congr($(h0 _ (projOn_pairWeil hf (κ⁻¹, 1) (by simp [mem_Kf_iff.1 hκ.2]) ▸ by
    simpa [mixedTerm_zero] using
      ((isAdapted_homSource D V).omega_projOn_of_isMixedLaw isMixedLaw_mixedTerm 0 _).symm)) _)

/-- Let W' = W ⊕ ℍ^p (adapted), V definite, r = rk W, n = rk V > 2r + 2p + 3, w split, w̄ ∈ S,
a's base change unramified at w̄, Y automorphic, spherical at w, H_w(X)Y = 0, |X| =
q_w^{(r+2−2n)/2}. Then `DescentsVanish` for W, a implies it for W', aυ^p. -/
lemma descentsVanish_add_planes [IsBaseAdapted D] (hY : V.IsAutomorphic Y) {w} (hw :
  w.IsSplit) (ha : CharUnramifiedAt a.baseChange.finPart (star w))
  (hw' : star w ∈ S) (hK : Y ∈ sphericalAt (finRightRep ..) w) {X} (hX : ‖X‖ = (√w.q ^ card r *
  w.q ^ (card n - card r - 1))⁻¹) (hP : heckePolyOp (finRightRep ..) hw X Y = 0) (h : 2 * card
  r + 2 * card p + 3 < card n) : DescentsVanish W' V (a * upsilonU1 ^ card p) S Y := by
  induction' hl : card p with l ih generalizing m p <;> intro f hf <;> ext g
  rw [card_eq_zero_iff] at hl
  simpa [univ_eq_empty, mulVec_eq_sum] using! h0.integral_sourceTerm_eq_zero D hf g
  set χ := a * _
  let Θ := (pairThetaKer W' V χ 1).swap
  obtain _ := D.card_eq, (by simpa using pow_mul √w.q 2 · |>.symm)
  refine (Θ.exists_clm_lift hY.mem_rapidFunctions).elim fun L e ↦
    e .. ▸ ext_integrated _ hf fun P y _ ↦ e .. ▸ ?_
  set f := integrated _ (polyVector _ P) _
  replace hf : projOn _ S f = f := by simp +contextual [f, finHeisOp, finVec, *]
  obtain ⟨⟨C, A, h₀⟩, ⟨c, u⟩, ⟨D', _, -⟩, K, h₅, H⟩ := Θ.moderate_growth,
    V.exists_short_basis_matrix, exists_isBaseAdapted_stage D (equivOfCardEq (α := Unit ⊕ Fin l)
    (by simp; omega)), hecke_transfer_of_equivariant (k := card n - card m) (by omega) (a :=
    χ) (by simp_all [χ, charUnramifiedAt_upsilon ..]) (b := 1) (by simp) hw.star (f := f) (hf
    ▸ by simp [← projOn_union, hw']) Θ.liftBilin (.linHom 1 (finRightRep ..))
    (rapidFunctions.toRepresentation.linHom 1) fun g h ↦ by ext y; simpa [mul_assoc] using!
    (Θ.lift_equivariant (y.2.1.comp_mul_right h⁻¹) f h ..).symm
  rw [sphericalAt, maxCompactAt,
    Gf.supportedOn_star] at *; simp at H; lift Y to V.rapidFunctions.1 using hY.mem_rapidFunctions
  have J := heckePolyOp_adjoint hw («π» := V.rapidFunctions.toRepresentation) .applyₗ
    (Subtype.ext <| hK ·) h₅ (by simp) X
  rw [Submodule.coe_eq_zero.1 ((map_heckePolyOp (Submodule.subtype _) _).trans hP), map_zero, H,
    map_smul, map_heckePolyOp _ (π' := finRightRep ..) _] at J
  refine congr($(eq_zero_of_heckePolyOp_eq_zero hw (by apply congr($(K ·) Y))
    ((IsUnit.prod_iff.2 fun i ↦ isUnit_one_sub_of_norm_lt_one ∘ ?_).smul_eq_zero.1 J.symm) ?_ ?_) g)
  any_goals simp [*, field, ← pow_add, pow_lt_pow_iff_right₀, pow_le_pow_iff_right₀]; omega
  let ℓ := θ _ - θ _ ∘L (D'.homSource V).zeroTerm
  have cov {φ B} (h : ∀ b, ‖θ _ φ - θ _ (ϱ _ ((D'.homSource V).kAdelic *ᵥ b) φ)‖ ≤ B) : ‖ℓ φ‖ ≤
    B := by simpa [ℓ, quotMean, integral_sub, by simpa using ((D'.homSource
    V).isContPeriodic_along_k φ 0).integrable_out] using! norm_quotMean_le (_root_.ratVectors ..) h
  constructor; rintro _ ⟨g, ⟨⟩⟩
  choose! ξ h1 i e using W'.exists_short_isotropic
  choose! γ hγ using fun l ↦ W'.witt (.of_ne_zero (h1 l <| ext_col fun () ↦ ·)) ⟨_,
    D'.gram_lk⟩ (D'.gram_kk ▸ i l)
  have b := ae_of_all V.quotMeasure fun h ↦ norm_mul_le_of_le (by
    simpa only [height, (V.move h).firstMinimum_le_one.antisymm one_le_firstMinimum, pow_zero,
      mul_one] using (exists_norm_name_le χ 1 disjoint_bot_left (Ψ :=
      boxIndicator _ ⊥) (finHeisOp_mem_finitePart y vacElem_mem_finitePart) 0 A (C + C)
    c).choose_spec _ (W'.ratEmbed γ * g) h ℓ _ _ (weightedNorm_polyVector_ne_top _ P)
      (one_le_height ..) (W'.height_pos g) (fun _ ↦ cov fun b ↦ by grw (transparency :=
      .default) [varrho_pairWeil, norm_sub_le, Θ.swap.theta_rat_mul, h₀, Θ.swap.theta_rat_mul,
      h₀] <;> simp [Γ, add_mul]) fun l ↦ (u h).rec fun Y u ↦ ⟨_, _, _, _, u,
      fun j ↦ by simpa [baseLattice, ↓move_vecAtPoint, ← hγ l, ← replicateCol_mulVec, col_apply', ←
      mat_mul, ← ratEmbed_mulVec_vecAtPoint, archCoords] using e l j, le_rfl, .inr D'.gram_kk,
      fun z φ ↦ congr($(by simp [← vecAtPoint_hom]) - θ _ $(by simp [← zeroTerm_rho_kAdelic
      (matToVec (V.dualFrame.1 * V.coordMatrix 1 z)) φ, ↓homSource_kAdelic,
      -transpose_mul, Space.ratMap, W'.map_J])), .inr fun φ B H ↦ cov fun b ↦ by
    simpa [ℓ, ← (Y.1.map _).mul_assoc, ← zeroTerm_rho_kAdelic b (ω _ _ φ), ↓homSource_kAdelic,
      ← mat_mul, ← h.mat.mul_assoc, ↓mat_preserves_stdForm, pairWeil, ω_ϱ,
      ← mul_sub, -transpose_mul, -θ_apply] using H (matToVec (Y⁻¹.1.map toAdele * V.x.1 *
      V.dualFrame⁻¹.1 * vecToMat b))⟩) (Y.2.2.bounded.choose_spec h)
  refine (Θ.fixesLeft_lift _ ⟨γ, rfl⟩ g).symm.trans (sub_eq_zero.1 ((integral_sub
    (Θ.integrable_theta_mul Y.2 ..) (.of_bound (hY.rec (by simp; fun_prop)) _ b)).symm.trans ?_)) ▸
    norm_integral_le_of_norm_le_const b
  simpa +zetaDelta [mul_assoc, sub_mul] using! (ih (removePlanes ..) (by simp; omega)
    (by simp)).integral_sourceTerm_eq_zero D' hf _
end

section
/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Cost in squares bookkeeping; exchange constants on the data cost one square. -/

namespace Data

open Finset Fintype Modulus MulChar
variable {P} {D : Data P} {n n' N : ℕ} {c c' : D.MFoldTwist → ℂ}

variable (D n c) in
/-- c costs n squares: for each family θ of fit twists (`Data.IsFitFamily`), the family
|c(θ_ι)/c(1)|⁻² has height (`HeightLe`) at most 2n t x^999. -/
def CostsSquares := ∀ θ, D.IsFitFamily θ → HeightLe (n * (2 * D.t * D.x ^ 999)) fun ι ↦
  (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹

/-- Costs add in products: if the functions c, c′ on twists cost n and n′ squares in the sense
of `Data.CostsSquares`, and n + n′ ≤ N, then the pointwise product c·c′ costs N squares. -/
lemma CostsSquares.mul (h : D.CostsSquares n c) (h' : D.CostsSquares n' c') (e : n + n' ≤ N) :
  D.CostsSquares N (c * c')
  | θ, o => ((h θ o).mul (h' θ o)).mono (by grw [← e]; grind) (by simp [field])

/-- The residue ring of `Data.𝔪` = M^e·Q attached to ϑ has order (∏ N w)^e · ∏_{w ∈ Q} N w, the
first product running over the chosen places w above g. -/
lemma card_𝔪 e ϑ : card (D.𝔪 ϑ e).ResRing = (∏ i, (D.chosen i).q) ^ e * ϑ.levelNorm := by
  erw [LevelPlaces.card_levelModulus_resRing, prod_coe_sort, levelPlaces]

/-- If |c(ϑ)|² = C·|O_E/𝔪_ϑ|^k for all ϑ, with C real and k an integer independent of ϑ, and 𝔪_ϑ
= M^e Q(ϑ) the modulus `Data.𝔪`, then c costs 0 squares (`Data.CostsSquares`). -/
lemma CostsSquares.of_norm_sq_eq_mul_card_zpow e C (k : ℤ) (h : ∀ ϑ, ‖c ϑ‖ ^ 2 =
  C * card (D.𝔪 ϑ e).ResRing ^ k) : D.CostsSquares 0 c
  | _, o => o.heightLe_of_eq_zpow_mul (@.prod _ ∅ id 1 nofun) (by simp) fun _ _ ↦
    ⟨-k, by simp_all [div_pow, card_𝔪, mul_zpow, field, twist_one_spec]⟩

lemma CostsSquares.one : D.CostsSquares 0 1 := .of_norm_sq_eq_mul_card_zpow 0 1 0 (by simp)

/-- If ν is tame for the squarefree modulus 𝔪 (exponent e = 1) with character χ, then χ is
primitive: for each a ≠ 0 in O_E/𝔪 some χ(1 + ca) is neither 0 nor 1. -/
lemma isPrimitiveMulChar_of_isTameFor {ϑ ν γ χ} : IsTameFor (D.𝔪 ϑ 1) ν γ χ → IsPrimitiveMulChar χ
  | ⟨_, ψ, _, hψ, H⟩, a,
    n => have := matrix_ext_modulusResidue (x := !![a]) (y := 0) (D.levelPlaces ϑ).apart.1
    have ⟨w, m, _⟩ : ∃ w m, modulusResidue _ m a ≠ 0 := by by_contra!; simp_all [← Matrix.ext_iff]
    (ne_one_iff.1 ((hψ w).2 m)).elim fun x _ ↦
      (algebraMap_ResField_surjective w ((x - 1) / modulusResidue _ m a)).elim fun b (_ :
      modulusResidue _ m b = _) ↦ ⟨Modulus.reduction _ ⟨_, idem_mem_Ô {w}⟩ * ↑b, by
      simp_all [finprod_eq_single _ (Subtype.mk w m), apply_eq_zero_iff, charOfTamePart_apply]⟩

/-- Let (ν, z) be a pair ramified exactly at the chosen places, e ≥ 1, 1 ≤ n ≤ m. Each (νϑⁿ)⁻¹
is tame for the modulus 𝔪 = M^e Q(ϑ) (`Data.𝔪`), and every c with |c(ϑ)|² = C·Π(z) (`lValueProd`)
costs one square (`Data.CostsSquares`). -/
lemma exists_isTameFor_costsSquares_one (p : D.Pair) (r : p.IsRamified) e [NeZero e] (n :
  D.LiftIndex) : (∀ ϑ : D.MFoldTwist, IsTameFor (D.𝔪 ϑ e)
  (p.ν * ϑ.toAutChar ^ n.1)⁻¹ (p.c ·) (charOfTamePart _ (p.ψ * ϑ.ψ ^ n.1))⁻¹) ∧ ∀ {c C}, (∀ ϑ :
  D.MFoldTwist, ‖c ϑ‖ ^ 2 = C * lValueProd (D.𝔪 ϑ e).places (p.ν * ϑ.toAutChar ^ n.1)⁻¹ p.z) →
  D.CostsSquares 1 c := ⟨fun ϑ ↦ by simpa [Pi.neg_def] using! (isTameFor_of_hasWeight
  _ (p.hasWeight.mul (ϑ.powTwist n).hasWeight) r).inv, fun h θ o ↦ o.heightLe_of_eq_zpow_mul
  (.prod (s := Icc 1 p.z) fun _ _ ↦ (o.height_le n (p.lowerPoint _) 1 r).pow 2) (by simp [field,
  p.7.2]) fun ι _ ↦ ⟨-p.z ^ 2, have := p.lValueProd_eq 1 ((θ ι).powTwist n)
  by simp_all [div_pow, twist_one_spec, MFoldTwist.powTwist, TameChar.pow, places_modulus_eq_union]
     simp_all [field, sq, zpow_mul, pow_mul]⟩⟩
end Data
end
