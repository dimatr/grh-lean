import Lib.Adelic.PeriodLattice
import New.Filling.BesselOrthonormal
import New.Filling.BoxPartition

-- part: Lib.General.NumberTheory.FundamentalDomains
section
/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus (known
result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Fundamental domains and covolumes of adelic lattices; box domain for filtered discrete
subgroups. -/


open NumberField MeasureTheory Matrix Finset ZSpan MeasurableEquiv mixedEmbedding
variable {E n} [Field E] [CMType E] [Fintype n]

/-- Let t ∈ (E ⊗ ℝ)ⁿ and the finite adelic matrix m be invertible. The group of vectors
(t_{j,v}Φ_v(x_j)), x ∈ Eⁿ with mx integral, has a measurable strict fundamental domain of
volume |(∏_j t_j, det m)|_𝔸 divided by the n-th power of `volÔ`. -/
lemma exists_fundamental_domain_classLattice (t : RealVectors E n) (ht :
  IsUnit t) (m : GL n (𝔸f E)) : ∃ F, MeasurableSet F ∧ volume.real F =
  (∏ w, ‖∏ j, t j w‖ ^ 2) / genIndex m.1.det / volÔ E ^ Fintype.card n ∧ ∀ x, ∃! l :
  classLattice m⁻¹ ⊥ (.smulLeft ht.unit), l.1 + x ∈ F := .imp (fun F (And.intro f u) ↦ ⟨f, by
  have T z : ∀ w, ∃! y, t * toRealVectors y + z ∈ F ∧ frameTorsionClass m⁻¹ y = w :=
    frameTorsionClass_surjective (g := m⁻¹).forall.2 (Equiv.addRight · |>.existsUnique_congr_right.1
    (by simpa [ExistsUnique, mul_add, ht.mul_right_inj, add_assoc, mem_classLattice,
    toRealVectors_injective.eq_iff, and_assoc, @imp.swap (_ ∈ F)] using u _))
  erw [genIndex_eq_inv_finIdeleAbs m.det]
  simpa [field, ideleAbs_det_mkAdelicGL] using!
    (by simpa [field, volume_pi_pi, Measure.volume_eq_prod,
    (volume_measurePreserving_arrowProdEquivProdArrow ..).measure_preimage_equiv] using
    (congr($((lintegral_encard_rat_points (mkAdelicGL (((diagGL (ht.apply · |>.unit)).map <|
    Pi.evalRingHom _ ·), m))⁻¹ ((arrowProdEquivProdArrow ..).measurable (f.prod (.univ_pi fun _ ↦
    isOpen_Ô.measurableSet)))).trans (lintegral_congr fun _ ↦ congrArg _ (Set.encard_eq_one.2 (by
    simpa [diagonal, Set.singleton_iff_unique_mem, mulVec_eq_sum, frameTorsionClass, mul_add,
      torsionClass_eq_iff, ← prod_mk_sum, -map_neg, arrowProdEquivProdArrow] using!
      T _ (torsionClass (-_)))))).toReal)) :), u⟩) ⟨_, fundamentalDomain_measurableSet _, by
    rw [← (Module.finBasis ..).ofZLatticeBasis_span ℝ (classLattice ..)]
    apply exist_unique_vadd_mem_fundamentalDomain⟩

/-- Injective graded coordinates c on G: suppose each γ ∈ Γ vanishing below deg i shifts c_i by
c(γ)_i ∈ L_i, and all of L_i arises with the other coordinates of degree ≤ deg i zero. For
fundamental domains F_i of L_i, each x has a unique γ ∈ Γ with c(xγ) ∈ ∏F_i. -/
lemma Filling.existsUnique_mul_mem_box {G ι} [Group G] [Fintype ι] {V : ι → AddGrpCat} (deg : ι → ℕ)
    (c : G → ∀ i, V i) (inj : c.Injective) (Γ : Subgroup G) (L : ∀ _, AddSubmonoid _) F (hF : ∀ i
  v, ∃! l : L i, l.1 + v ∈ F i) (hL' : ∀ i, ∀ l ∈ L i, ∃ γ : Γ, c γ i = l ∧ ∀ j ≠ i, deg j ≤ deg i →
  c γ j = c 1 j) (hL : ∀ (γ : Γ) i, (∀ j, deg j < deg i → c γ j = c 1 j) → c γ i ∈ L i ∧ ∀ x, c
  (x * γ) i = c γ i + c x i) x : ∃! γ : Γ, c (x * γ) ∈ Set.univ.pi F := have := by simpa using hL 1
  .imp (fun γ h ↦ ⟨h, (mul_left_surjective γ).forall.2 fun δ _ ↦ by simpa using @inj δ 1 (funext
    ((measure deg).2.fix fun i ih ↦ have := @(hF _ (c (x * γ) _)).unique _ _ ⟨_, (hL _ _ ih).1⟩ 0
    by simp_all [← (hL _ _ ih).2, mul_assoc]))⟩) (@coe_univ .. ▸ univ.induction_on_max_value deg
    (by simp) fun a _ _ _ ⟨γ, h⟩ ↦ (hF a (c (x * γ) a)).rec fun l _ ↦ (hL' a _ l.2).imp' (γ * ·)
    fun δ o i _ ↦ by erw [← mul_assoc, (hL ..).2] <;> grind [eq_or_ne i a])

/-- For E stably unramified and nonzero reals t_v, the group of vectors (t_v Im Φ_v(s))_v, s an
integer of E with s̄ = −s, has a measurable fundamental domain in ℝ^(infinite places) of
volume ∏|t_v|·√|disc E⁺|. -/
lemma Filling.exists_fundamental_domain_im_skew [StablyUnram E] (t : _ → ℝ) (ht : ∀ v, t v ≠ 0) :
  ∃ F, MeasurableSet F ∧
  volume.real F = (∏ v, |t v|) * √√|NumberField.discr E| ∧ ∀ x, ∃! l : (skewAdjoint (𝓞 E)).map
  (.mk' (fun s v ↦ t v * (Φ v s.val).im) (by simp [funext_iff, mul_add])), l.1 + x ∈ F := by
  obtain ⟨⟨ι, _, h⟩, f, hf, _⟩ := ‹StablyUnram E›.exists_i_c₀,
    exists_mixedEquiv_maximalReal (E := E)
  have {v} : (Φ v ι.val).re = 0 ∧ |(Φ v ι).im| = 1 := by
    cases mul_self_eq_mul_self_iff.1 (by simp [h, ← map_mul] : Φ v ι * _ = _ * .I) <;> aesop
  have k := isUnit_of_mul_isUnit_left (h.1 ▸ isUnit_neg_one)
  refine ⟨_, ?_, ?_, ((Equiv.subtypeEquivRight fun l ↦ .trans ?_ k.unit.mulLeft.exists_congr_right
    ).existsUnique_congr_right.1 <| exist_unique_vadd_mem_fundamentalDomain (((latticeBasis _).map
    f).map ((diagonal fun v ↦ t v * (Φ v ι).im).toLin'.equivOfDetNeZero
    (by simp_all [prod_eq_zero_iff, ← abs_pos]))) ·)⟩
  repeat (try erw [← map_fundamentalDomain, Measure.real, volume.addHaar_image_linearMap, ←
    hf.measure_preimage, ← map_fundamentalDomain, f.preimage_image]) <;> simp [← Int.cast_abs,
    abs_discr_eq_discr_sq, Real.sqrt_sq_eq_abs, norm, k.ne_zero, *, abs_prod, prod_nonneg,
    fundamentalDomain_measurableSet, volume_fundamentalDomain_latticeBasis, ← ZSpan.map,
    mem_span_latticeBasis, funext_iff, mul_assoc, skewAdjoint.mem_iff]
  simp [star, IsCMField.ringOfIntegersComplexConj_eq_self_iff, ← funext_iff]; rfl
end

-- part: New.Filling.UnipotentCovolume
section
/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Explicit covolume of the level-g arithmetic unipotent group in scaled real
coordinates. -/

open Classical ENNReal Finset Fintype Function Matrix MeasureTheory NumberField Sum

attribute [-instance] Pi.instMeasurableConstSMul Pi.measurableSMul

attribute [-simp] Complex.ofReal_div Nat.cast_mul

attribute [local grind] IsFreeEntry

attribute [local simp] FI.level Filling.frameScaleSq prod_eq_zero_iff prod_pow Matrix.mul_apply
  vecMul_fromBlocks div_pow funext_iff mul_assoc mul_sub pow_mul' sub_mul tsub_add_eq_tsub_tsub_swap

/-- Under the standing hypotheses, for every class c and archimedean point y, the integral of
the cutoff β_c(uy) over u in 𝖴_∞, for the product Haar measure, equals the covolume ν, which
does not depend on c. -/
lemma Filling.lintegral_classCutoff_eq_unipCovolume {E} [Field E] [CMType E] [StablyUnram E] {𝔰}
  (S : Filling E 𝔰) c [S.IsAdmissible] (y : _ → _) :
  ∫⁻ u, S.classCutoff c fun v ↦ u v * y v ∂(.pi fun _ ↦ 𝔰.besselHaar) = .ofReal S.unipCovolume := by
  let φ := MonoidHom.mk' (fun (γ : S.classUnip c) v ↦
    (⟨_, γ.2.1.ratToInf_mem_unitriangularOn v⟩ : besselU)) (by aesop)
  have n a (j : Subtype (@IsFreeEntry 𝔰 ⟨a, ·⟩)) : inl a ≠ j.1 ∧ j.1 ≠ eStar a := by grind
  let b := (classBasis c).1
  have ⟨M, e, u⟩ : ∃ m, b = fromBlocks 1 0 0 (fromBlocks m 0 0 1) ∧
    genIndex m.det = 1 / S.N ^ numInfPlaces E := by
    use ?_, by simp [b, classBasis, toBesselH, besselLatticeBasis]; rfl
    obtain _ := congr(genIndex $(c.out.2).det), congr(genIndex $S.piBar_mul_star),
      genIndex_pos c.out.1.det, genIndex_pos S.piBar
    simp_all [genIndex_natCast, ← sq, le_of_lt]
    grind
  let m a := (b.toSquareBlockProp (IsFreeEntry ⟨a, ·⟩))ᵀ
  have d a : (m a).det =
    b.det := by simp [b.twoBlockTriangular_det (IsFreeEntry ⟨a, ·⟩) (by simp [e]; omega), m,
    (by simp [toSquareBlockProp, ← ext_iff, e] : b.toSquareBlockProp (¬IsFreeEntry ⟨a, ·⟩) = 1)]
  have B a l j : (m a *ᵥ l ∘ (↑)) j = (l ᵥ* b) j :=
    sum_of_injective _ Subtype.val_injective _ _ (by revert j; simp [e]; lia) (mul_comm _ <| l ·)
  choose F hF vF uF using fun a ↦ exists_fundamental_domain_classLattice (fun j v ↦
    S.g / S.basisScale v (inl a) * S.basisScale v j.1)
    (by simp [Pi.isUnit_iff]) (.mk'' (m a) (by simp [d, b]))
  choose F' hF' vF' uF' using fun a ↦
    exists_fundamental_domain_im_skew (S.g / S.frameScaleSq · (Fin.val a)) (by simp)
  have p := ((((measurePreserving_sigma (.symm (.subtypeProdEquivSigmaSubtype
    (@IsFreeEntry 𝔰 ⟨·, ·⟩)))).comp measurePreserving_flip).prod measurePreserving_flip).comp
    (measurePreserving_arrowProdEquivProdArrow ..)).comp
    (measurePreserving_pi _ _ fun _ : InfinitePlace E ↦ measurePreserving_freeEntries_besselHaar)
  have hB := (MeasurableSet.univ_pi hF).prod (.univ_pi hF')
  have o := existsUnique_mul_mem_box (V := (fun a ↦ .of (Subtype (IsFreeEntry ⟨a, ·⟩) →
    _)) ⊕ᵥ fun _ ↦ .of _) ((2 * ·.rev) ⊕ᵥ (2 * ·.rev + 1)) (fun u : InfinitePlace E → (𝔰.middleGram
    1).besselU ↦ Sum.rec (fun a j v ↦ (u v).1.1 (inl a) j) fun a v ↦ (freeEntries IsFreeEntry
    (u v).1.1.1).2 a) (fun _ _ e ↦ funext fun v ↦ injective_freeEntries_besselU congr((($e (inl _)
    ⟨_, ·.2⟩ v), swap ($e <| inr ·) v))) φ.range (Sum.rec _ _) (Sum.rec _ _) (Sum.rec uF uF') (by
    rintro (a | a) l ⟨x, hx⟩
    rw [← extend_comp Subtype.val_injective x 0] at hx
    have ⟨γ, H⟩ := exists_eichler_classUnip c a (@extend_val_apply' _ _ _ x 0) (fun j ↦ byCases
      (B a _ ⟨j, ·⟩ ▸ torsionClass_eq_zero.1 hx.1 _) (by revert j; simp +contextual [b, e])) 0
    swap; have ⟨γ, H⟩ := exists_eichler_classUnip c a (l := 0) (by simp) (by simp) ⟨x, hx.1⟩
    all_goals
      use ⟨_, γ, rfl⟩, by simp [← hx.2, φ, basisScale, field, *]
      rintro (b | b) k l <;> simp (disch := clear * - l k; grind) [φ, ite_eq_right, H]) (by
    rintro ⟨u, γ, G⟩ i h
    have R a j : (finAdeleMat ((S.g : E)⁻¹ • (γ.1.1.1 - 1)) (inl a) ᵥ* b) j ∈ Ô E := by
      rw [← mul_apply_eq_vecMul, show _ * _ = b * S.gIdele⁻¹ • ((S.termPosition c ..).1 - 1) by
        simp [b, coe_termPosition, Matrix.map_sub]; rfl]
      simpa [e] using (S.principalLevel_eq_unitaryLevel.le (x := termPosition ..) γ.2.2).2 _ j
    have w v x ⦃a j⦄ (d : i = inr a ∧ j = eStar a ∨ i = inl a ∧ IsFreeEntry (a, j)) :
      (x * u v).1.1 (inl a) j = (u v).1.1 (inl a) j + x.1.1 (inl a) j := by
      simp at h
      clear * - h d
      have r k l : (∀ b, k = inl b → a < b ∨ j = eStar b) → (∀ d, l ≠ eStar d) →
          (u v).1.1 k l = ite (k = l) 1 0 := by simp; grind [by simpa using mem_besselU.1 (u v).2]
      simpa [(by grind : inl a ≠ j), sub_eq_iff_eq_add'] using (sum_eq_zero fun k _ ↦
          mul_eq_zero.2 (or_not.imp (sub_eq_zero_of_eq ∘ x.2 _ k) fun n ↦ by
        have A c (_ : j = eStar c) :=
          congrFun₂ (U.coe_inv IsHermInvolution.mul_self (u v).1 ▸ (u v).1.1.mul_inv) k j
        simp +contextual -dsimp [splitGram, r] at A
        rcases j, k with ⟨_ | _ | _, _ | _ | _⟩ <;> simp at n <;> simp [r, n] at A <;> simp [*]
        grind [Complex.conj_eq_iff_im]) : ((x.1.1.1 - 1) * (_ - 1)) (inl a) j = 0)
    obtain ⟨rfl, a | a⟩ := G, i
    use ⟨_, torsionClass_eq_zero.2 (B a _ · ▸ R a _), by simp [φ, n, field]⟩,
      fun _ ↦ funext₂ fun j ↦ (w · _ (.inr ⟨rfl, j.2⟩))
    use ⟨IsIntegralClosure.mk' _ (_ * _ : E) (algebraMap_mem_Ô.1 (by
      simpa [e] using! R a (eStar a))), RingOfIntegers.ext ((Φ ofNonempty).injective (by
      simpa [φ, basisScale, Complex.ext_iff, self_eq_neg, ← two_mul] using (w ofNonempty
        (φ γ ofNonempty)⁻¹ (.inl ⟨rfl, rfl⟩)).trans congr(_ + $(U.coe_inv IsHermInvolution.mul_self
        _) _ _))), by simp [φ, basisScale, field]⟩, fun x ↦ funext (congr($(w · _ (by simp)).im)))
  have := φ.rangeRestrict_surjective.countable
  apply ((toReal_eq_toReal_iff ..).1 _).resolve_right (by simp [unipCovolume_pos])
  rw [(IsFundamentalDomain.mk' (p.1 hB).inv.nullMeasurableSet (((Equiv.inv _).existsUnique_congr fun
    _ ↦ Sum.forall).1 <| o ·⁻¹)).lintegral_eq_tsum'', ← lintegral_tsum (by fun_prop),
    lintegral_congr fun u ↦ ((φ.ofInjective fun _ ↦ by simp [φ, ← SetLike.coe_eq_coe,
    GeneralLinearGroup.ext_iff, (RingHom.injective _).eq_iff]).tsum_eq _).symm.trans (congr(∑' _,
    S.classCutoff c $(mul_assoc ..)).trans (tsum_classCutoff_eq_one ..)),
    toReal_ofReal S.unipCovolume_pos.le, unipCovolume, ← sum_range_reflect,
    sum_range, frameScaleProd, prod_comm, Fin.prod_univ_castSucc]
  simp [*, volume_pi_pi, ← measureReal_def, Fintype.card_subtype, card_filter,
    basisScale, ↓prod_sum_type, ←
    prod_subtype _ mem_filter_univ, ↓sum_sum_type, prod_filter, filter_lt_eq_Ioi, mul_pow, abs_div,
    pow_right_comm _ _ 2, pow_succ _ (_ + _), prod_pow_eq_pow_sum, ↓p.measure_preimage, prod_ite,
    (by simp; omega : ∀ k (a : Fin 𝔰.ϱ), k + 2 * (𝔰.ϱ - a) = a.rev + (k + 1 + a.rev) + 1)]
  field
end

-- part: New.Filling.AmplitudeSums
section
/-! Part of: Second moment of the Poincaré series with constant one (see New.Filling.Moments).

Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Blocks of the unfolded moment: convergence, cut, weight change, moves, identity term. -/

open NumberField MeasureTheory Measure Complex ENNReal Classical Finset Fintype

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S :
  Filling E 𝔰}

lemma isStable_besselS : S.IsStable (S.ratMiddle E).besselS := by
  simp +contextual [IsStable, mul_mem_cancel_right, mul_mem_cancel_left]

attribute [local simp] mul_assoc SMul.smul
variable {A : Subgroup 𝔰.G₁} (ν : Measure A) [h : IsUnimodularHaar ν]

instance : SigmaFinite (orbitMeasure ν (@volume 𝔰.G₁ _)) :=
  .withDensity_of_ne_top ((epsilon_spec h.out).ae_lt_top.mono (by order))

lemma measurePreserving_pi_orbitMeasure {P} [Fintype P] :
  MeasurePreserving (fun p ↦ (p.2 · |>.1) * p.1) (.prod (.pi fun _
  ↦ orbitMeasure ν volume) (.pi fun _ ↦ ν)) (@volume (P → 𝔰.G₁) _) := (measurePreserving_pi _ _
  fun _ ↦ measurePreserving_orbitMeasure).comp (measurePreserving_arrowProdEquivProdArrow ..).symm

lemma tsum_integral_apply {X J I} [MeasurableSpace X] {μ : Measure X} [Countable J] [Fintype I]
    {g : J → X → EuclideanSpace ℂ I} (m : ∀ j, Measurable (g j)) (h : ∑' j, ∫⁻ x, ‖g j x‖ₑ ∂μ < ∞)
    i : (∑' j, ∫ x, g j x ∂μ) i = ∫ x, ∑' j, g j x i ∂μ := .trans ((funext fun j ↦
  eval_integral_piLp (.eval_piLp ⟨by fun_prop, (ENNReal.le_tsum j).trans_lt h⟩) i) ▸
  (EuclideanSpace.proj i).map_tsum (.of_enorm (ne_of_lt (by grw [enorm_integral_le_lintegral_enorm,
  h])))) (integral_tsum (by fun_prop) (ne_of_lt (by grw [PiLp.enorm_apply_le, h]))).symm

variable [σ : Side]

noncomputable instance : Fintype S.GRes := .ofFinite _

lemma besselFn_mul_of_mem_classUnip {c} (u : S.classUnip c) y : S.besselFn (S.ratToInf u * y) =
  S.besselFn y := have := u.2
  by simp_all [classUnip, besselFn_ratToInf_mul,
    unipotentChar_eq_of_mem_principalLevel (one_mem _) _ c.out]

lemma besselKernel_besselU_mul {u u'} (a : u ∈ besselU) (a' : u' ∈ besselU) γ y :
  S.besselKernel (u * γ * u'⁻¹) (S.ratToInf u * y) =
  ((S.unipotentChar (S.ratToFin u))⁻¹ * S.unipotentChar (S.ratToFin u')) • S.besselKernel γ y := by
  ext; simp [besselKernel, *, besselFn_ratToInf_mul, unipotentChar, ← inv_eq_conj, field]

variable [StablyUnram E] [S.IsAdmissible] (T c s c')

omit [Side] in
lemma lintegral_classCutoff_mul_prod {w : _ → _} (hm : ∀ v, Measurable (w v)) (hU : ∀ v,
  besselU.FixesLeft (w v)) c : ∫⁻ y, S.classCutoff c y * ∏ v, w v (y v) =
  .ofReal S.unipCovolume * ∏ v, ∫⁻ y, w v y ∂besselQuotMeasure := by simp (disch := measurability)
  [← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar).lintegral_comp, lintegral_prod, Pi.mul_def,
  hU, lintegral_mul_const, lintegral_classCutoff_eq_unipCovolume, lintegral_pi_prod]

/-- Under `Filling.IsAdmissible`, for the full or cut W and γ over the terms of T over (c, s, c'):
∑β_c'(γ⁻¹y)∏_v‖W_v((γ⁻¹y)_v)‖ is bounded in y, and amplitudes converge absolutely. For fixed
c, s, ∑_{c',γ}∫β_c(y)β_c'(γ⁻¹y)‖kernel − cut kernel‖dy ≤ νb^(−k³f)/2. Here β_c =
`Filling.classCutoff` c and ν = `Filling.unipCovolume`. -/
lemma amplitudeAbs_lt_top_and_cut_le : let X d := T ∩ S.termsOver c s d; (∀ c',
    (∃ M : NNReal, ∀ y, ∑' γ : X c', S.classCutoff c'
    ((S.ratToInf γ)⁻¹ * y) * ∏ v, ‖(S.besselSys v).W σ (((S.ratToInf γ)⁻¹ * y) v)‖ₑ ≤ M) ∧ ∑' γ :
    X c', S.amplitudeAbs c c' γ < ∞) ∧ ∑' (d) (γ : X d), ∫⁻ y, S.classCutoff c y * S.classCutoff d
    ((S.ratToInf γ)⁻¹ * y) * ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ ≤
    .ofReal (S.unipCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := S.of_size_bounds <| by
  intros; rename_i X; obtain ⟨⟨r, k⟩, f⟩ := S.pow_le_k.dest, S.k_le_f
  choose A m hm hU hW hA _ l using (S.besselSys · |>.tail.exists_majorant)
  let Q (z : InfinitePlace E → 𝔰.G₁) := Set.univ.pi fun v ↦ {g | InCut (z v * g) S.b}
  have R {z} : MeasurableSet (Q z) := .univ_pi (by measurability)
  choose! u a b using fun {d z g} (h : (Q z).indicator (fun _ ↦ S.classCutoff d z * 1) g ≠ 0) ↦
    exists_classUnip_mul_mem_boxedPoints d (Set.mem_of_indicator_ne_zero h · ⟨⟩)
  have n y := lintegral_mono (μ := .pi m) fun g ↦ tsum_classCutoff_box_le (V := ⊤) (y' :=
    y) Sigma.subtype_ext (fun (p : Σ d, X d) h ↦ ⟨.mul p.2.2.2 (.inv (a h).2), by simp [a h], by
    simpa using! b h, Set.indicator_le_self _ _ g⟩) (by simp)
  simp (disch := fun_prop (disch := tauto)) only [Q, pi_pi, mul_one, lintegral_const,
    lintegral_indicator_const R, lintegral_tsum, ENNReal.tsum_sigma'] at n
  have o {n} := one_le_ofReal.2 (one_le_pow₀ (n := n) ‹_›)
  grw [← hA] at n
  have e τ (y : _ → _) := prod_mono' fun v ↦ hW v τ (y v)
  simp [↓prod_mul_distrib, prod_ite] at e
  have h1 := lintegral_mono (μ := volume) fun y ↦
    mul_le_mul_right (n y) (S.classCutoff c y * ∏ v, A v (y v))
  simp (disch := fun_prop) only [← ENNReal.tsum_mul_left, lintegral_tsum, lintegral_mul_const,
    mul_mul_mul_comm _ _ (classCutoff ..), lintegral_classCutoff_mul_prod _ hU, pi_univ] at h1
  grw [mul_comm, mul_mul_mul_comm, ← prod_mul_distrib, l, prod_mul_distrib, prod_const,
    ← Nat.cast_prod, ← Fintype.card_pi] at h1
  have p γ y := have q τ := mul_le_mul' (e τ y) (e τ ((S.ratToInf γ)⁻¹ * y))
    (mul_le_iff_le_inv (one_pos.trans_le o).ne' ofReal_ne_top).1 ((add_le_add (q σ)
    (q .cut)).trans' (byCases (by
    simp_rw [mul_mul_mul_comm _ (univ.prod _), ← mul_add, ← enorm_besselKernel]
    grw [← pow_add, ← enorm_sub_le, ← le_self_pow o ·])
      (by cases σ <;> simp +contextual [besselKernel, besselFn])))
  use fun c' ↦ ?_, ?_; grw [← ENNReal.le_tsum c', ← le_mul_of_one_le_left' (one_le_pow₀ o)] at *
  simp_rw [amplitudeAbs, enorm_besselKernel]; grw [e, e, e, n, h1]
  use ⟨_, fun _ ↦ (coe_toNNReal ?_).ge⟩ <;> finiteness
  grw [p]; simp (disch := finiteness) only [mul_left_comm _ (_⁻¹ * _), ← two_mul,
    ← mul_assoc _⁻¹, lintegral_const_mul', ENNReal.tsum_mul_left]
  grw [h1]
  simp (disch := finiteness) [le_ofReal_iff_toReal_le, field, -Fintype.card_pi]
  grw [IsAdmissible.card_besselCoord_le, ‹2 ≤ S.b›]
  simp [← pow_mul, ← pow_add, ← k]
  gcongr; lia

/-- Under the standing hypotheses, for any set T of rational elements, the amplitudes of the
terms of T over (c, s, c') form a summable family. -/
lemma summable_amplitude : Summable fun γ : ↥(T ∩ S.termsOver c s c') ↦ S.amplitude c c' γ :=
  .of_enorm (ne_of_lt (by grw [enorm_amplitude_le, ((amplitudeAbs_lt_top_and_cut_le ..).1 _).2]))

variable {T} (hT : S.IsStable T)
include hT

/-- Change of weight: for stable T and measurable φ(γ,y) ≥ 0 of sum 1 on 𝖴_c(g)×𝖴_c'(g)-orbits,
the integrals ∫φ(γ,y)W(y)⊗W(γ⁻¹y)^*dy over terms of T over (c,s,c') converge and sum to
A_T(c,s,c'), and ∑_γ∫φ‖full kernel − cut kernel‖ ≤ νb^(−k³f)/2. -/
lemma hasSum_amplitudeSum_change_of_weight c s c' (φ : _ → _ → _) (h : ∀ γ ∈ T ∩ S.termsOver c s c',
  ∀ y, ∑' u : S.classUnip c × S.classUnip c',
  φ (u.1 * γ * u.2⁻¹) (S.ratToInf u.1 * y) = 1) (hm : ∀ γ, Measurable (φ γ) := by measurability) :
  let X := T ∩ S.termsOver c s c'; HasSum (fun γ : X ↦ ∫ y, (φ γ y).toReal • S.besselKernel γ y)
    (S.amplitudeSum T c s c') ∧ (∀ γ : X, Integrable fun y ↦ (φ γ y).toReal • S.besselKernel γ
    y) ∧ ∑' γ : X, ∫⁻ y, φ γ y * ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ ≤
    .ofReal (S.unipCovolume * (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ / 2) := by
  intro X; let Δ := S.classUnip c × S.classUnip c'; let : MeasurableSpace (S.G E) := ⊤
  let : MulAction Δ X := by refine' { smul u γ := ⟨_, (hT _ u.1⁻¹.2.1 _ u.2⁻¹.2.1 _).2 γ.2.1, by
    simpa using termsOver.mul (.mul u.1.2.2 γ.2.2) u.2⁻¹.2.2⟩, .. } <;> simp [HSMul.hSMul, Δ]
  let Y := InfinitePlace E → 𝔰.G₁
  let : MulAction Δ Y := .compHom _ ((S.ratToInf.domRestrict _).comp (.fst ..)); let := this.toSMul
  let K [Side] := fun ((γ : X), y) ↦ S.besselKernel γ y; let ρ := (@count X _).prod (@volume Y _)
  have p (u : Δ) : MeasurePreserving (u • ·) ρ ρ :=
    (measurePreserving_count (MulAction.toPerm u)).prod (measurePreserving_mul_left ..)
  have := MeasurableSMul₂.mk (measurable_from_prod_countable_right (p · |>.1))
  have := (((smulInvariantMeasure_tfae Δ ρ).out 7 1).1 p :)
  have k [Side] (u : Δ) p : K (u • p) =
    K p := by simp +zetaDelta [besselKernel, HSMul.hSMul, besselFn_mul_of_mem_classUnip]
  have mK [Side] : Measurable K := by fun_prop [besselKernel]
  have b : IsCutoff (@count Δ _) fun ((γ : X), y) ↦
    S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y) :=
    ⟨by fun_prop, by simp +zetaDelta [HSMul.hSMul, tsum_classCutoff_eq_one]⟩
  have q {β} (h : IsCutoff _ β) : _ ∧ _ ∧ _ :=
    have w {F} hF (hi := by simp [k]) := lintegral_withDensity_eq_lintegral_mul ρ h.1 hF ▸
      ((identDistrib_orbitMeasure h hF hi).symm.trans (identDistrib_orbitMeasure b hF
      hi)).lintegral_eq.trans_le ((lintegral_withDensity_le_lintegral_mul _ b.1 F).trans
      ((lintegral_prod_le _).trans_eq (lintegral_count _)))
    have i := integrable_toReal_smul h.1 (by fun_prop)
      ((w mK.enorm).trans_lt ((amplitudeAbs_lt_top_and_cut_le ..).1 _).2)
    ⟨by simpa using
      ((h.integral_orbitMeasure k mK).trans (integral_prod _ i) ▸ hasSum_integral_measure
      i.integral_prod_left :), ae_count_iff.1 i.prod_right_ae, have d := (mK.sub (@mK .cut)).enorm
      by simpa [ρ, ↓lintegral_prod _ (h.1.mul d).aemeasurable] using (w d).trans (.trans
        (by exact ENNReal.le_tsum (f := fun d ↦ ∑' γ : ↑(T ∩ S.termsOver c s d), ∫⁻ y,
        S.classCutoff c y * S.classCutoff d ((S.ratToInf γ)⁻¹ * y) *
        ‖S.besselKernel γ y - S.besselKernel (σ := .cut) γ y‖ₑ) c')
        (amplitudeAbs_lt_top_and_cut_le T c s).2)⟩
  exact ((q b).1.tsum_eq ▸ @q (Function.uncurry (φ ·)) ⟨measurable_from_prod_countable_right
    (hm ·), ((lintegral_count _).trans <| h _ ·.1.2 _)⟩ :)

/-- Let T be stable, σ over (c,t,c₁) and σ' over (c',t',c₁') lie in S, with γ ∈ T iff σγσ'⁻¹ ∈
T. If a continuous linear L takes the kernel at (γ,y) to that at (σγσ'⁻¹,σy), then A_T(c,
tst'⁻¹, c') = L A_T(c₁,s,c₁') for the amplitude sums. -/
lemma amplitudeSum_move {c t c₁ σ c' t' c₁' σ'} (h : σ ∈ besselS) (o : σ ∈ S.termsOver c t c₁) (h' :
  σ' ∈ besselS) (o' : σ' ∈ S.termsOver c' t' c₁') (e : ∀ γ, γ ∈ T ↔ σ * γ * σ'⁻¹ ∈ T) (L : _ →L[ℂ]
  _) (hL : ∀ γ y, S.besselKernel (σ * γ * σ'⁻¹) (S.ratToInf σ * y) = L (S.besselKernel γ y)) s :
  S.amplitudeSum T c (t * s * t'⁻¹) c' = L (S.amplitudeSum T c₁ s c₁') := by
  have m {c t d σ c' t' d' τ s γ} o o' : γ ∈ S.termsOver d s d' ↔
    σ * γ * τ⁻¹ ∈ S.termsOver c (t * s * t'⁻¹)
    c' := ⟨(.mul · (.inv o')) ∘ .mul o, (by simpa using termsOver.mul (.inv o) <| .mul · o')⟩
  have b {c t c₁ σ} h o y := (((MulAut.conj σ).subtypeEquiv (p := (· ∈ S.classUnip c₁)) fun γ ↦
    .trans (.and (besselS_le_normalizer_besselU h γ) (m (t := t) o o)) (by simp; rfl)).tsum_eq
    _).trans (tsum_classCutoff_eq_one c (S.ratToInf σ * y))
  simp [-Subtype.forall] at b
  refine (hasSum_amplitudeSum_change_of_weight hT _ s _ (fun γ y ↦
    S.classCutoff c (S.ratToInf σ * y) * S.classCutoff c' (S.ratToInf (σ' * γ⁻¹) * y))
    (by simp [b h o, b h' o'])).elim fun k f ↦ (((.mulRight σ'⁻¹ * Equiv.mulLeft σ).subtypeEquiv
    (by simp [← e, m o o', -mul_assoc])).hasSum_iff.1 ((k.mapL _).congr_fun fun γ ↦
    (integral_mul_left_eq_self _ (S.ratToInf σ)).symm.trans ?_)).tsum_eq
  simp [↓← L.integral_comp_comm (f.1 γ), ← hL]

lemma amplitudeSum_besselU_mul {u u' : S.latStabilizer} (hu : u.1 ∈ besselU) (hu' :
  u'.1 ∈ besselU) c s c' : S.amplitudeSum T c (S.reduction u * s * (S.reduction u')⁻¹) c' =
  ((S.unipotentChar u)⁻¹ * S.unipotentChar u') • S.amplitudeSum T c s c' := by
  obtain ⟨⟨x, _, ⟨k, _⟩, _⟩, _, a', ⟨k', _⟩, _⟩ := exists_rat_approx_unipotentChar_eq c hu,
    exists_rat_approx_unipotentChar_eq c' hu'
  apply amplitudeSum_move hT _ ⟨u * k, _⟩ (mem_unitriGroup_of_mem_besselU a') ⟨u' * k', _⟩
    (hT x⁻¹ _ _ _ · |>.symm) (.lsmul ℂ ℂ _) <;> simp_all [↓besselKernel_besselU_mul]

/-- If T is stable under 𝖴(E⁺) on both sides and s does not agree, that is the character of Ū
differs from its conjugate by s on Ū ∩ sŪs⁻¹, then the sum of amplitudes of T over (c, s,
c') vanishes. -/
lemma amplitudeSum_eq_zero_of_not_agrees (hs : ¬S.Agrees s) : S.amplitudeSum T c s c' = 0 :=
  by_contra (hs fun _ _ _ _ _ ↦
  eq_of_inv_mul_eq_one <| smul_left_injective _ · (by simp [← amplitudeSum_besselU_mul, *]))

omit σ hT

/-- Let T be the group of rational points of the Bessel subgroup 𝖴H. The sum of the amplitudes
of the elements of T over (c, 1, c') has (i, j) entry ν = `Filling.unipCovolume` if
c = c' and i = j, and 0 otherwise. -/
lemma amplitudeSum_besselS_one i j : S.amplitudeSum (σ := .full) (S.ratMiddle E).besselS c 1 c' (i,
  j) = ite (c = c' ∧ i = j) S.unipCovolume 0 := by
  obtain h | rfl := ne_or_eq c c'
  rw [amplitudeSum, tsum_congr fun γ ↦ (h (γ.2.elim eq_and_mem_classUnip_of_besselS).1).elim,
    tsum_zero]
  simp [h]
  obtain ⟨k, f, -⟩ := hasSum_amplitudeSum_change_of_weight isStable_besselS c 1 c
    (if 1 = · then S.classCutoff c else 0) fun γ h y ↦ by
    lift γ to S.classUnip c using (h.elim eq_and_mem_classUnip_of_besselS).2
    norm_cast
    simp [ite_apply, ↓eq_mul_inv_iff_mul_eq, tsum_classCutoff_eq_one]
  rw [k.unique (hasSum_single ⟨1, one_mem _, (classUnip ..).one_mem.2⟩ (by aesop)),
    eval_integral_piLp (f _).eval_piLp,
    ← ((measurePreserving_pi_orbitMeasure 𝔰.besselHaar).fubini ((f _).eval_piLp _)).2]
  simp [besselKernel, besselFn, ← prod_mul_distrib, Pi.mul_def,
    ((besselSys ..).tail.isBesselFunction _).2, mul_conj', integral_complex_ofReal, mul_mul_mul_comm
    _ _ (starRingEnd _ _), apply_ite ofReal, integral_toReal (Measurable.aemeasurable (by fun_prop))
    (ae_lt_top (by fun_prop) (S.lintegral_classCutoff_eq_unipCovolume c _ ▸ ofReal_ne_top)),
    lintegral_classCutoff_eq_unipCovolume, Fintype.prod_boole, (integral_fintype_prod_eq_prod
    _).trans congr(∏ v, $((S.besselSys v).orthonormal ..)), S.unipCovolume_pos.le, funext_iff]
end Filling
end
