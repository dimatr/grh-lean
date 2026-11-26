import New.Weil.UnfoldingStep
import New.Weil.EdgePair
import New.Weil.SharpData
import New.Weil.AlgebraicPartDefs

section
/-! Part of: Unfolded periods as finite sums with controlled denominators (see
New.Seesaw.SeesawTheorem).

This file: Finite coset cut with multiplicities dividing powers of q; period as weighted finite
sum. -/

open MeasureTheory Measure Subgroup QuotientGroup MulAction Set Pointwise ProbabilityTheory


variable {H} [Group H] {S A J : Subgroup H} (T : Finset (H ⧸ J)) {E ι X} [Field E] [CMType E]
  [Fintype ι] [Fintype X] {s ε N} {V : Space E ι ε} {Y : Grading V N X s}

variable (S A) in
/-- The number of cosets r(S ∩ A) in S with t in the translate rT, counted as zero if infinite. -/
noncomputable def coverMultiplicity t := (mk (s := A.subgroupOf S) '' {r | r⁻¹ • t ∈ T}).ncard

lemma coverMultiplicity_smul (p : S) t : coverMultiplicity S A T (p • t) =
  coverMultiplicity S A T t := by rw [coverMultiplicity, ← ncard_smul_set p⁻¹,
  ← image_smul_comm] <;> simp [coverMultiplicity, ← preimage_smul, mul_smul]

/-- Let J ≤ A be levels, A ≤ B, D ⊆ B compact, W ⊆ SD; each x ∈ D has n with (xux⁻¹)^{qⁿ} ∈ A
for all u ∈ J. Some finite (S ∩ A)-stable T ⊆ B/J has `coverMultiplicity` dividing a power of
q on T and on W. -/
lemma exists_cut_coverMultiplicity_dvd {S A J : Subgroup (Gf E ι)} [k : IsLevel A] [o : IsLevel J]
  (l : J ≤ A) {D q B} (cD : IsCompact D) {W : _ → _} (b : A ≤ B) (hD : ∀ x ∈ D, x ∈ B ∧ ∃ n,
  ∀ u ∈ J, (x * u * x⁻¹) ^ q ^ n ∈ A) (hW : ∀ x, W x → ∃ r ∈ S, r * x ∈ D) : ∃ T : Finset (_ ⧸ J),
  (∀ p : S, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t ∈ T) ∧ (∀ ⦃x⦄, ↑x ∈ T → x ∈ B) ∧ ∀ x, ↑x ∈ T ∨ W x → ∃ j,
  coverMultiplicity S A T x ∣ q ^ j := ((mk '' D).exists_subset_bijOn (orbit S)).elim fun C ⟨hC, _,
  i, u⟩ ↦ (Finite.exists_finset (s := {t | ∃ p : S, ↑p ∈ A ∧ p⁻¹ • t ∈ C})
  ((finite_quotient_image_of_isCompact o.2 (k.isCompact.mul cD)).subset fun t ⟨p, h,
  a⟩ ↦ (hC a).elim fun d e ↦ ⟨_, ⟨p, h, d, e.1, rfl⟩, eq_inv_smul_iff.1 e.2⟩)).imp fun T m ↦ by
  simp_rw [m]
  use fun p _ _ ↦ (toPerm p).exists_congr (by simp_all [mul_mem_cancel_left, mul_smul]), fun x
    ⟨r, hr, h⟩ ↦ (hC h).elim fun d ⟨h, e⟩ ↦ by
    simpa [mul_mem_cancel_left, b hr, *] using b (l (QuotientGroup.eq.1 e)), fun y h ↦ ?_
  let ⟨_, ht, e⟩ := h.elim (fun ⟨r, h⟩ ↦ ⟨_, h.2, by simp⟩)
    (hW y · |>.elim fun r h ↦ u ⟨_, ⟨_, h.2, rfl⟩, orbit_smul (⟨r, h.1⟩ : S) (mk y)⟩)
  obtain ⟨⟨r, e⟩, x, hx, rfl⟩ := orbit_eq_iff.1 e.symm, hC ht
  have := FiniteIndex.mk (relIndex_comap_ne_zero S.subtype ((k.isCompact.smul (ConjAct.toConjAct
    x)).relIndex_ne_zero (K := MulAut.conj x • A) k.2) ∘ relIndex_eq_zero_of_le_right
    (K := stabilizer S (mk x)) fun r h ↦ ⟨_, l (QuotientGroup.eq.1 h.symm), by simp⟩)
  erw [← e, coverMultiplicity_smul, coverMultiplicity,
    (image_subset_iff.2 fun r h ↦ ?_).antisymm (b := orbit (stabilizer S
    (mk x)) (mk 1)) fun _ ⟨r, e⟩ ↦ ⟨_, (r * 1)⁻¹.2.symm.subst ((m _).2 ⟨1, by simpa⟩), e⟩,
    ← index_stabilizer, congr(($(stabilizer_quotient (A.comap _)).subgroupOf _).index)]
  exacts [.imp (fun _ ↦ (index_dvd_of_le (normalCore_le _)).trans) (isPGroup_iff_card_dvd_pow.1
    (Quot.ind fun b ↦ (hD x hx).2.imp fun n h ↦ (eq_one_iff _).2 fun c ↦ by
    simpa using! h _ (QuotientGroup.eq.1 (c * b * c⁻¹).2.symm))), ((m _).1 h).elim fun p ⟨_, e⟩ ↦
      ⟨⟨_, i (by rwa [mul_smul]) ht (by simp)⟩⁻¹, QuotientGroup.eq.2 (by simpa)⟩]

/-- For a measurable subgroup J and a left invariant measure μ, the union of a finite non-empty
set s of left cosets of J has measure |s|·μ(J). -/
lemma measure_union_cosets [MeasurableSpace H] [MeasurableMul H] {μ} [IsMulLeftInvariant μ]
    (h : @MeasurableSet H _ J) {s} (f : ncard s ≠ 0) : μ (mk (s := J) ⁻¹' s) = s.ncard * μ J := by
  lift s to Finset (H ⧸ J) using finite_of_ncard_ne_zero f
  rw [← sum_measure_preimage_singleton, Finset.sum_eq_card_nsmul (b := μ J)] <;>
    simp [forall_mk, preimage, eq_class_eq_leftCoset, h.const_smul, -measurableSet_setOfPred]

/-- For a level A and a on G_∞, one κ gives ∫_{B(E⁺)∖G} f = κ∑_{t∈T} b(t)/mult(t),
B = `Grading.besselGroup`, for all integrable f = Py (`Grading.IsGeneric` P, y automorphic), levels
J and finite (A ∩ B_f)-stable T ⊆ G_f/J, if mult ≠ 0 where f ≠ 0 and ∫_{[B]}
f(ρt)dρ = [K₀:J]a(t_∞)b(t_f) for t_f ∈ T.

Unfolded periods as finite sums with controlled denominators. -/
lemma Grading.exists_integral_eq_sum_over_cut [WeilData E]
    A [k : IsLevel A] (a : _ → ℂ) : ∃ κ, ∀ {P y J T}
  [IsLevel J] (b : _ ⧸ J → ℂ), Y.IsGeneric P → V.IsAutomorphic y → let f :=
    P * y; Integrable f Y.ratBessel.qms → (∀ p : Y.besselFin, ↑p ∈ A → ∀ t, t ∈ T ↔ p • t ∈ T) →
    (∀ g, f g ≠ 0 → coverMultiplicity Y.besselFin A T g.2 ≠ 0) →
    (∀ t, t.2 ∈ T → ∫ r, f (r * t) ∂Y.besselMeasure = stdLevelIndex J * (a t.1 * b t.2)) →
    Y.ratBessel.qms[f] = κ * ∑ t ∈ T, (↑(coverMultiplicity Y.besselFin A T t))⁻¹ * b t := by
  let η := haarMeasure (G := Y.besselFin) ⟨⟨_, k.isCompact.preimage_val⟩, 1,
    k.2.preimage_val.interior_eq.ge A.one_mem⟩
  let ⟨β, _, hβ'⟩ := hasCutoff_of_proper (ν := @haar Y.besselGroup ..) (X := G E ε)
  let α g := ∫⁻ s, β (g, s) ∂η
  use (withDensity ℙ α)[a], @fun P y J T o b p z hI hT hs hb ↦ ?_
  obtain ⟨⟨⟩, ⟨⟩⟩ := z, p, discreteTopology o.2
  let ψ := indicator T (coverMultiplicity Y.besselFin A T · : _ → NNReal)⁻¹
  have hφ := (by fun_prop : Continuous (ψ ∘ QuotientGroup.mk)).measurable
  erw [← setIntegral_eq_integral_of_forall_compl_eq_zero (not_imp_comm.1 <| hs ·),
    restrict_withDensity',
    (integral_quotMeasure_stages _ _ id ?_ (((congrArg _ (funext fun t ↦ ?_)).trans
    (withDensity_indicator_one (isOpen_ne_fun ..).measurableSet)).subst (measurePreserving_smul_prod
    (ν := haar) (β := fun g ↦ α g.1 * ψ g.2) _)) (map_subgroupOf_eq_of_le inf_le_right) _ (by
    simp +contextual [*]) ((restrict_withDensity' ..).subst hI.restrict)).2, integral_congr_ae
    ((ae_withDensity_iff _).2 (.of_forall (hb · ∘ by simp +contextual [ψ]))), integral_const_mul,
    ← prod_withDensity _ hφ.coe_nnreal_ennreal, integral_prod_mul _ (b ∘ _),
    integral_withDensity_eq_integral_smul hφ, ← integral_map (f := fun t ↦ ψ t • b t) _
    (Continuous.aestronglyMeasurable _), ← indicator_smul_left, integral_indicator T.measurableSet,
    setIntegral_finset _ (.mono_set _ (biUnion_of_singleton _).ge)]
  any_goals fun_prop
  iterate 3 simp [real_def, map_apply measurable_coe, measure_union_cosets o.2.measurableSet, field,
    -enorm_mul, ← T.mul_sum, NNReal.smul_def, zero_lt_iff,
    inter_eq_left.2 o.1 ▸ measure_inter_eq_inv_relIndex isCompact_Kf o.2]
  simp [smul_def, α, ← lintegral_mul_const', Prod.mul_def] at hβ' ⊢
  rw [lintegral_lintegral_swap, ← lintegral_congr (lintegral_mul_left_eq_self _ ⟨_, ·⁻¹.2⟩),
    lintegral_lintegral_swap, ← lintegral_congr (lintegral_mul_left_eq_self _
    ⟨_, Y.snd_mem_besselFin ·.2⟩), lintegral_lintegral_swap] <;> try fun_prop
  simp [lintegral_mul_const', indicator, *]
  let := Classical.dec; show ∫⁻ u, ψ (u⁻¹ • t.2) ∂η = _
  split_ifs with m <;> simp [ψ, indicator, coverMultiplicity_smul, apply_ite, m]
  erw [lintegral_indicator_const (measurable_inv.smul_const t.2 T.measurableSet), (congrArg _
    ((subset_preimage_image ..).antisymm fun r ⟨s, h, e⟩ ↦ (hT (s⁻¹ * r) (QuotientGroup.eq.1 e :)
    _).2 (by simpa [mul_smul]))).trans (measure_union_cosets k.2.preimage_val.measurableSet m),
    ENNReal.inv_mul_cancel_left, haarMeasure_self] <;> simp [*]
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

Part of: Theta lift for a definite unitary pair as a class sum on algebraic modular forms (known
result; see Lib.Weil.CompactLift.RallisFormula).

This file: Two unfolding steps equal a double theta lift of the evaluated datum. -/

open Grading Matrix MeasureTheory Space Subtype Splitting

attribute [local simp] formAdjoint_formAdjoint boxProd_integrated Std.map_integrated
  Subgroup.mem_prod GradeZeroPart.splitting vecToMat entrywise mul_assoc
  realMap_flipCoords_polyVector realBoxProd_polyVector matToVec pairChar

variable {E ι ι' ι'' X X' X'' X₀ q : Type} [Field E] [CMType E] [WeilData E] [Fintype ι]
  [Fintype ι'] [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype X₀] [Fintype q]
  {ε ε' ε'' N s s' s''} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  {Y : Grading V N X s} {Y' : Grading V' N X' s'} {Y'' : Grading V'' N X₀ s''}

/-! The value of two unfolding steps is the double lift of the finite evaluation. -/

/-- Let k, k' be families of theta lifts X → X' → X₀. For fixed u and t, some t'' works for all o,
y, φ, g: integrating coefficient t of φ against the theta kernel of `integrated _ u (arrowTensor y)`
over [U(X)] × [U(X')] gives coefficient t'' of the double lift. -/
lemma integral_theta_eq_lift₂ {κ e e' e'' O k k'} {a b : O → _} (hk :
  IsThetaLift κ e e' (rankTwist <| a ·) k) (hk' : IsThetaLift κ _ e'' (rankTwist <| b ·) k') u t :
  let L o := TensorProduct.lift (.flip (.compl₁₂ (.llcomp ..) (k' o) (k o))); ∃ t'', ∀ o y φ g, ∫ x,
    algFormCoeff 1 t φ x * ∫ r, θ _ (tripleWeil (V'' := stdSpace E X₀) (a o) (b o) (x, r,
    g) (integrated _ u (arrowTensor y))) ∂(stdSpace E X').quotMeasure ∂(stdSpace E X).quotMeasure =
    algFormCoeff 1 t'' (L o y φ) g := by
  intro L; choose z _ hz using theta_arrowProduct (stdSpace E X) (stdSpace E X') (stdSpace E X₀)
  let F o (φ : AlgForm X κ e) g x := algFormCoeff 1 t φ (.fst x) • θ ((stdSpace E X').hom
    (flipSum (stdSpace ..) (stdSpace E X₀))) ∘L tripleWeil (a o) (b o) (x.1, x.2, g)
  have i {o φ g} f : Integrable (F o φ g · f) (.prod (stdSpace ..).quotMeasure
    (stdSpace ..).quotMeasure) := ((stdSpace ..).isAutomorphic_algFormCoeff φ).rec fun _ _ _ ↦
    integrable_of_cocompact (cocompact_prod (stdSpace ..).exists_isCompact_of_definite (stdSpace
    ..).exists_isCompact_of_definite) (by simp [F, tripleWeil, -circleChar_inv_apply]; fun_prop)
    (by simp_all [F, ↓theta_tripleWeil_rat_mul])
  refine (isClosed_property denseRange_polyVector ((IsLinearMap.mk' (R := ℂ) (algFormCoeff 1 ·
    <| L · · ·) ⟨by tauto, by tauto⟩).range.closed_of_finiteDimensional.preimage_of_continuous (f :=
    fun u o y φ g ↦ strongIntegral (.prod (stdSpace ..).quotMeasure (stdSpace ..).quotMeasure)
    (F o φ g) (integrated _ u (arrowTensor y)))) (fun P ↦ Submodule.mul_induction_on
    (mem_rename_range_mul (.map (·) (.map .inl (·) ∘ .swap)) (.map (·) (.map
    .inr (·))) (by simp) P) (fun _ ⟨P, p⟩ _ ⟨Q, q⟩ ↦ (hk P t).rec fun t' G ↦ (hk' (z • Q) t').imp
    fun _ H ↦ ?_) fun _ _ h ↦ by simpa using! add_mem h) u).imp fun _ h ↦ by
    simpa [funext_iff, ← integral_const_mul, strongIntegral_apply, integral_prod, i] using! h.symm
  ext o y; simp; induction y <;> try simp [*]
  simp [↓strongIntegral_apply, ↓integral_prod_symm, i, L, -θ_apply, ← H, ← G, ← integral_const_mul]
  congr!; rw [mul_rotate', mul_rotate, mul_rotate', mul_assoc, ← hz, arrowProduct_twistedPairWeil]
  simp [← p, ← q, arrowProduct, flipPoly, pairSign, MvPolynomial.rename_eq_aeval,
    MvPolynomial.bind₁_bind₁]; rfl

/-- For a pair D there is one constant z such that, for generic P on U(V), the integral over
[B] × [B'] of P(gt) times the two constant terms at T, T' equals z∫_{[U(X)]} P(gt) ∫_{[U(X')]}
θ(Ω(g, r, D.embX k) ev ϱ(T*, T')(f ⊗ f')), ev the zero term along `ArrowPair.splitting`. -/
lemma ArrowPair.integral_constTermAtT_mul (D : ArrowPair X'' q Y Y' Y'') : ∃ z, ∀ a b f f' k P t,
  Y.IsGeneric P → let F g r := P (g * t) * Y.constTermAtT Y' (rankTwist a) f g r *
    Y'.constTermAtT Y'' (rankTwist b) f' r (Y''.inclX k)
  ∫ r, ∫ g, F g r ∂Y.besselMeasure ∂Y'.besselMeasure = ∫ g, P (Y.inclX g * t) * (z * ∫ r,
    θ _ (tripleWeil a b (g, r, D.embX k) (D.splitting.zeroTerm (homHeisOp (stackedT Y Y' Y'')
    (arrowProduct f f')))) ∂(stdSpace E _).quotMeasure) ∂(stdSpace E X).quotMeasure := by
  obtain ⟨⟨z, h, M⟩, B, ⟨κ, K⟩, O, ⟨⟩, ⟨⟩, c⟩ := theta_arrowProduct V V' V'',
    Y.formAdjoint_apply Y', Y.integral_besselMeasure_eq_of_mean (.refl _), D.string_spec
  have hz f f' w w' : Y.constTerm Y'.gradeOf f w * Y'.constTerm Y''.gradeOf f' w' =
    z⁻¹ * D.homZeroPart.splitting.zeroTerm (arrowProduct (homHeisOp w f) (homHeisOp w' f')) 0 := by
    rw [eq_inv_mul_iff_mul_eq₀ h, Splitting.zeroTerm_apply,
      ← quotMean_quotMean (_root_.ratVectors ..) _ (_root_.ratVectors ..) (.mk' (fun a ↦
      matToVec ((V.formAdjoint V' (vecToMat a.1)).fromRows (vecToMat a.2)) ∘ val) (id _)) _ _
      (val_injective.surjective_comp_right.forall.2 fun b ↦ ⟨(matToVec (V'.formAdjoint V
      (vecToMat b).toRows₁), matToVec (vecToMat b).toRows₂), by simp [-vecToMat]⟩)]
    any_goals rintro _ ⟨a, ⟨⟩⟩ _ ⟨b, ⟨⟩⟩
    any_goals simp [↓isContPeriodic_along_k, continuous_pi_iff, mem_ratVectors, B, ← map_mul,
      ratAdeles, -continuous_prodMk, funext_iff, add_mul, mul_add] <;> constructor <;> fun_prop
    simp_rw [constTerm, quotMean, ← integral_mul_const, ← integral_const_mul, ← θ_ϱ, ← M,
      ← homHeisOp_arrowProduct, homHeisOp, ← x_inv_mulVec_matToVec, mulVec_zero, zero_add]; congr!
    apply (kAdelic_mulVec _ rfl _).symm.trans (congrArg ..) <;> simp +contextual [funext_iff, B]
  refine (Y'.integral_besselMeasure_eq_of_mean D.gradeOne).imp' (κ * · * z⁻¹) ?_; introv H Q F
  have C : Continuous ↿F := Q.rec (by simp [F, *]; fun_prop)
  have L r : Y.ratBessel.FixesLeft (F · r) := fun _ o ↦
    (by simp [F, Q.2 _ o, ← constTermAtT_rat_mul ⟨_, o⟩ 1 ·])
  have R g : Y'.ratBessel.FixesLeft (F g) := fun δ l r ↦ by
    simp [F, ← constTermAtT_rat_mul 1 ⟨_, l⟩ g r, ← constTermAtT_rat_mul ⟨_, l⟩ 1 r]
  simp_rw [fun r ↦
    K (L r) C.along_fst (fun n l ↦ by simp [F, mul_assoc n, -mul_assoc, Q.unipotent_mul_constTerm
    Y'.gradeOf_stringReversal l (Y.hasDegreeGe_two_of_odd O l) (Y.hasDegreeGe_neg_one_stringMap.mul
    (Y.hasDegreeGe_two_of_odd O l))]) (fun a ↦ ⟨⟨continuous_const, by simp⟩, quotMean_const
    (F (Y.inclX a) r)⟩) (by fun_prop) (by simp +contextual [L, ↓inclX_mem_ratBessel]), mul_assoc,
    ← integral_const_mul z⁻¹, mul_left_comm (P _), ← integral_const_mul (P _), integral_const_mul κ]
  rw [integral_integral_swap (integrable_of_cocompact
    (cocompact_prod Y'.isCocompact_ratBessel (stdSpace ..).exists_isCompact_of_definite)
    (by fun_prop) (by simp +contextual [*, ↓inclX_mem_ratBessel]))]; congr with x
  refine H (R _) C.along_snd (fun n o g ↦ ?_) (fun _ ↦ ⟨isContPeriodic_along_k .., by
    simp_rw [← Splitting.zeroTerm_apply, ← D.zeroTerm_splitting_tripleWeil, stackedT,
      homHeisOp_arrowProduct, ← arrowProduct_twistedPairWeil, pairWeil_homHeisOp,
      inclX_mul_stringMap_mul_inclX_inv, ← homHeisOp_arrowProduct, ← smul_eq_mul, ← map_smul,
      splitting, zeroTerm_comp]; rfl⟩) (by simp [tripleWeil, -circleChar_inv_apply]; fun_prop)
    (one_mul x ▸ by simp +contextual [↓theta_tripleWeil_rat_mul])
  rw [← θ_ϱ, ← zeroTerm_rho_iAdelic, ← zeroTerm_rho_kAdelic
    ((matToVec (stackedT Y Y' Y'' * (V'.ratCoordMatrix n - 1)) - _) ∘ val), (heisRep _).2,
    (by simp [D.homZeroPart.splitting.beta_eq_coords] : Heisenberg.β .. = 1), kAdelic_mulVec _ rfl,
    iAdelic, Space.ratMap, Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_add, sub_add_cancel,
    x_inv_mulVec_matToVec, (heisRep _).2, ← homBicharacter, homBicharacter_eq, ← Matrix.mul_assoc]
  · simp [F, one_mul (Y.inclX x) ▸ Y.constTerm_mul Y'.gradeOf_stringReversal (.inr ⟨_,
      Y'.mem_unipotent.1 o⟩) _, one_mul (Y''.inclX k) ▸ Y'.constTerm_mul Y''.gradeOf_stringReversal
      (.inr ⟨o, Y''.mem_unipotent.1 _⟩) _ _, stackedT, ↓show ∀ A B, V'.formAdjoint (flipSum V V'')
      (A.fromRows B) = (-V'.formAdjoint V A).fromCols (V'.formAdjoint V'' B) by simp [formAdjoint,
      flipSpace], formAdjoint_stringMap_mul_stringMap, c, Matrix.mul_sub]
    simp [hz, ← homHeisOp_arrowProduct, formAdjoint_ratCoordMatrix_mul]
  intro p r; obtain h | ⟨⟨⟩, ⟨⟩⟩ := not_or_of_imp (D.homZeroPart.mem_range_index p).2
  · simp [D.homZeroPart.incl_eq_zero,
      h, ↓HasDegreeGe.mul (w'' := Y.gradeOf ⊕ᵥ Y''.gradeOf) (x := stackedT Y Y' Y'') (Sum.rec (by
      simp +contextual [stackedT, B, Y.hasDegreeGe_neg_one_stringMap _, add_comm])
      Y'.hasDegreeGe_neg_one_stringMap) (Y'.mem_unipotent.1 o) le_rfl p.1 p.2 (by omega)]
  simp [homZeroPart, GradeZeroPart.hom, D.stackedT_apply, homTarget, removePlanes, inclMatrix,
    Fintype.sum_prod_type, apply_ite toAdele, Finset.sum_mul,
    Finset.sum_comm, kAdelic, Matrix.mul_assoc]
end

section
/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

This file: Levels, finite data, Weil actions and tame characters of the row lifts. Defines the
indefinite chain of theta lifts, its levels, character and equivariance law. Gradings of the spaces
Y_k and evaluated finite data for each pair. -/

noncomputable section

open Fin Kf MatMul Matrix NeZero

section

variable {P} {D : Data P} (ϑ : D.TameChar) (j) (s : D.G) (N T : Type) [Fintype N] [Fintype T] {E}
  [Field E] [CMType E] (X : LevelPlaces E)

/-- The inclusion of the basis index set of Y_j in that of Y_{j+1} as the first summand. -/
abbrev Data.inclY (j : ℕ) : D.Y j ↪ D.Y (j + 1) := .inl

lemma Data.liftTamePart_eq_of_mem_Q (w : ϑ.Q) : D.liftTamePart ϑ j w =
  ϑ.ψ w := by simp [liftTamePart, IsChosen, D.levelNorm_mem_and_notMem_of_mem_Q ϑ]

/-- The subgroup of the lattice stabiliser K₀ for Y_j of elements reducing to 1 at every chosen
place, those over g and those of the twist ϑ. -/
abbrev Data.levelY := levelOf (n := D.Y j) (D.levelPlaces ϑ).placeAt ⊥

lemma Data.levelY_le_chosenLevel : levelY ϑ j ≤ chosenLevel :=
  Subgroup.map_mono fun _ e ↦ congr(($e <| .inl ·))

/-- The finite datum on Hom(Y_j, Y_{j+1}) named, on the vacuum, by the indicator of the block
inclusion (1;0) modulo the product of the chosen places and those of Q. -/
def Data.upsilonY := delta% vacuumDatum (D.spaceY j) (D.spaceY _) (D.𝔪 ϑ 1)
  (Pi.single (inclMatrix _ (D.inclY j)) 1)

/-- The theta kernel of the pair (Y_j, Y_{j+1}), with the characters νυ^⌊n/2⌋, νυ^⌊n'/2⌋ for the
ranks n, n' of Y_j, Y_{j+1} and ν = μ⁰_{j+1}ϑ^{j+1}. -/
abbrev Data.thetaKernelY := pairThetaKer (D.spaceY j) (D.spaceY (j + 1))
  (rankTwist (D.chainChar ϑ (j + 1)) (D.Y j)) (rankTwist (D.chainChar ϑ (j + 1)) (D.Y (j + 1)))

/-- The tame part of the character μ⁰_{j+1}ϑ^{j+1} of lift j + 1, a family of characters of the
residue fields. -/
abbrev Data.liftTame := D.liftTamePart (.pow ϑ (j + 1)) (j + 1)

/-- Let k, k' in K₀ for Y_j, Y_{j+1} have reductions g, g' with g'(1;0) = (1;0)g at all chosen
places and places of Q. Then (k, k') multiplies `Data.upsilonY` by ∏ ψ(det g')/ψ(det g) over
these places, ψ = `Data.liftTame`. -/
lemma Data.thetaKernelY_omega_upsilonY {k k' g g'} (e : reduceFamily _ k = g) (e' :
  reduceFamily (D.levelPlaces ϑ).placeAt k' = g') (h : ∀ x, (g' x).1.submatrix id (D.inclY j) =
  inclMatrix _ (D.inclY j) * (g x).1) : (thetaKernelY ϑ j).ω ((1, k), 1, k') (upsilonY ϑ j) =
  (∏ x, liftTame ϑ j _ (g' x).1.det / liftTame ϑ j _ (g x).1.det) • upsilonY ϑ j := by
  subst_vars; simp [upsilonY, ← modDatum_vacVector]
  rw [pairWeil_modDatum_single _ _
    ((Modulus.matrix_ext_modulusResidue (D.levelPlaces ϑ).apart.1).2 fun x ↦ ?_)]
  simp [D.hasWeight_liftChar.hasWeight_rankTwist.apply_det_eq_prod (auxPair ..).apart.1
    (AuxPair.tame_eq_one _), -_root_.mul_inv_rev]; rfl
  simp [← map_inv, map_inclMatrix]
  erw [← h, ← mul_inclMatrix]; simp [reduceFamily]

/-- The number, from 0 to j, of the block containing an index: 0 on R and l on the l-th copy of
T. -/
def blockNumber {R T} : ∀ j, BlockIndex R T j →
  Fin (j + 1) | 0 => 0 | j + 1 => castSucc ∘ blockNumber j ⊕ᵥ fun _ ↦ last _

lemma blockNumber_eq_zero {R T} j : ∀ i, @blockNumber R T j i = 0 ↔ i ∈ Set.range
  (BlockIndex.firstBlock j) := j.rec (by tauto) fun _ _ ↦ show ∀ i, _ ↔ ∃ _, Sum.inl _ = i by simpa!

instance Data.instNonemptyY : Nonempty (D.Y j) := .map (BlockIndex.firstBlock j) inferInstance

/-- The forms on U(Y_j) of the type given by the parameter `Data.paramY` and the signs of Y_j,
with the Petersson product. -/
abbrev Data.FormY := (D.spaceY j).Form (typeKernel (D.paramY j) _)

/-- The datum φ ⊗ Υ on Hom(Y_j, Y_{j+1}) of lift j + 1: the joint harmonic at infinity and the
finite datum `Data.upsilonY`. -/
abbrev Data.datumY := ((D.spaceY j).hom (D.spaceY (j + 1))).integrated
  (polyVector _ (D.gridHarmonic 0 false true j false 0 j 0 _)) (upsilonY ϑ j)

/-- For j < m the datum of lift j + 1 satisfies `IsArrow` both ways: the kernel has moderate
growth, forms are rapid, the lift sends forms on Y_j to forms on Y_{j+1}, and the descent
sends conjugate forms on Y_{j+1} to conjugate forms on Y_j. -/
lemma Data.isArrow_datumY {j} (hj : j < D.m) : IsArrow (thetaKernelY ϑ j) (typeKernel (D.paramY j)
  _) (typeKernel (D.paramY _) _) (datumY ϑ j) ∧ IsArrow (thetaKernelY ϑ j).swap
  (star (typeKernel (D.paramY _) _)) (star (typeKernel (D.paramY j) _)) (datumY ϑ j) :=
  (D.paramsCorrespond_grid false _ _ _ _ rfl).isEdge_jointHarmonic.isArrow _ _ (upsilonY ..).2

/-- Lift j + 1, from forms on Y_j to forms on Y_{j+1}: the theta lift with datum `Data.datumY`,
multiplied by the index [K₀ : 𝒥_j], 𝒥_j = `Data.levelY`. -/
def Data.liftY : D.FormY j →ₗ[ℂ] D.FormY (j + 1) :=
  (stdLevelIndex (levelY ϑ j) : ℂ) • formLift (thetaKernelY ϑ j) _ _ (datumY ϑ j)

/-- The subgroup of ∏ GL(Y_m mod w), over the chosen places, of elements that are 1 at the
places above g and block upper triangular at Q. -/
def Data.lastResLevel : Subgroup (∀ x, GL (D.Y D.m) (ResField ((D.levelPlaces ϑ).placeAt x))) :=
  .pi .univ fun x ↦ parabolic (blockNumber _) ⊓ bif x.isLeft then ⊥ else ⊤

/-- The composite of the first j theta lifts along Y₀, …, Y_j for the twist ϑ, from forms of
principal level g on Y₀ to forms on Y_j. -/
def Data.liftChainY : D.principalForms (D.spaceY 0) →ₗ[ℂ] D.FormY j :=
  compUpTo (liftY ϑ) j ∘ₗ (D.principalForms _).subtype

/-- The chain of lifts ι_μ, on all forms of principal level g on Y₀. -/
def Data.ι := (Space.toAlgForm _ D.isHCParam_Y).1 ∘ₗ liftChainY ϑ _

/-- If k ∈ K₀ on Y_m is block upper triangular at all chosen places, with block 0 equal to s ∈ 𝖦
above g, then k·ι_μ y = ∏_w ∏_{l≥1} μ_{l,w}(det k_{ll}) · ι_μ(s·y). -/
lemma Data.algFormRep_iota y k g (e : reduceFamily (D.levelPlaces ϑ).placeAt k = g) (h : ∀ x, (g
  x).1.BlockTriangular (blockNumber _)) (h' : ∀ x, (g (.inl x)).1.submatrix (BlockIndex.firstBlock
  _) (BlockIndex.firstBlock _) = (s x).1) : algFormRep _ _ k.1 (ι ϑ y) = (∏ x, ∏ l : Fin _, liftTame
  ϑ l _ ((g x).1.toSquareBlock (blockNumber _) l.succ).det) • ι ϑ (D.principalRep _ s y) := by
  erw [← Space.toAlgForm_formRep D.isHCParam_Y, ← map_smul]; apply congrArg
  have a := @isArrow_datumY _ D ϑ; generalize D.m = j at *
  induction' j with j ih
  simpa [prod_univ_zero] using! (apply_liftResidue_eq y k (funext (Units.ext <| (e ▸ h') ·))).symm
  have b x l : ((g x).1.toBlocks₁₁.toSquareBlock (blockNumber j) l).det = _ :=
    (det_submatrix_equiv_self · ((g x).1.toSquareBlock (blockNumber _) l.castSucc)) (.trans
    (.ofInjective _ (Sum.inl_injective.comp (by simp))) (.subtypeEquivRight (by simp! [eq_comm])))
  have t x : (g x).1.toBlocks₁₁.BlockTriangular (blockNumber j) := by tauto
  have d x := by simpa [prod_univ_castSucc, ← b, ← by simpa using (t x).det_fintype] using (h
      x).det_fintype
  have u x := left_ne_zero_of_mul (d x ▸ (g _).det_ne_zero)
  have e' := reduceFamily_liftResidue (.mkOfDetNeZero _ <| u ·)
  erw [LinearMap.map_smul, (a .refl).1.formRep_formLift, pairWeil_integrated_fin,
    thetaKernelY_omega_upsilonY _ _ e' e fun x ↦ (eq_inclMatrix_mul_iff .inl).2
    (·.rec (by simp) fun _ _ _ ↦ h _ (castSucc_lt_last _)),
    ih _ _ e' t h' (a <| Nat.lt_succ_of_lt ·)]
  simp [prod_univ_castSucc, *, MulChar.apply_eq_zero_iff, smul_comm (Nat.cast _), mul_smul]; rfl

/-- The homomorphism `Data.lastResLevel` → ℂ sending κ to the product, over w chosen or in Q and
blocks l ≥ 1, of μ_{l,w}(det κ_{ll}), μ_{l,w} the tame part of μ⁰_l ϑ^l. -/
def Data.lastLevelChar : lastResLevel ϑ →* ℂ := ∏ x, ∏ l : Fin _,
  (liftTame ϑ l _).1.comp (detMonoidHom.comp ((Units.coeHom
  _).comp ((blockHom _ l.succ).comp ((Pi.evalMonoidHom _ x).restrict fun _ ↦ (· x ⟨⟩ |>.1)))))

/-- The map ι_μ with its target restricted to the space of algebraic forms on Y_m
of level `Data.lastResLevel` and its character `Data.lastLevelChar`. -/
def Data.iotaAtLevel : D.principalForms (D.spaceY 0) →ₗ[ℂ] LevelPlaces.LevelForm _ _ (lastLevelChar
  ϑ) D.columnsY (D.lastEntry D.m) :=
  (ι ϑ).codRestrict _ fun y ↦ mem_levelSpace.2 fun k ↦ have h := (mem_levelOf.1 k.2).2
  by simpa [lastLevelChar] using! algFormRep_iota ϑ 1 y _ _ rfl (h · ⟨⟩ |>.1) fun x ↦
    (h (.inl x) ⟨⟩).2 ▸ submatrix_one_embedding _

/-- For s in 𝖦, a chosen element of K₀ on Y_m reducing to diag(s, 1) at the places above g and
to 1 at Q. -/
def Data.groupLift :=
  liftResidue (firstBlockHom (D.levelPlaces ϑ) (@BlockIndex.firstBlock _ (Fin D.t) D.m) s)

/-- The chain of lifts ι_μ commutes with the group 𝖦: ι_μ(s·y) is the right translate of ι_μ(y)
by the finite element `Data.groupLift` attached to s. -/
lemma Data.iota_principalRep y : ι ϑ (D.principalRep _ s y) =
  algFormRep _ _ (groupLift ϑ s) (ι ϑ y) := by
  let g := firstBlockHom (D.levelPlaces ϑ) (@BlockIndex.firstBlock _ (Fin D.t) D.m) s
  have e {x a b} (h : blockNumber .. ≠ 0) : g x a b = ite _ 1 0 :=
    x.rec (fun _ ↦ (extendGL_spec ..).2 a (by rwa [← blockNumber_eq_zero]) b) (by tauto)
  simpa [show ∀ x l, (g x).1.toSquareBlock (blockNumber _) (.succ l) = 1 by simp_all [← ext_iff,
            toSquareBlock_def]] using! (algFormRep_iota ϑ s y _ _ (reduceFamily_liftResidue g) (by
    grind only [BlockTriangular]) fun _ ↦ (extendGL_spec ..).1).symm

lemma card_parabolic_blockNumber j : ∃ k, ∀ R [CommRing R], Nat.card (parabolic (R :=
  R) (@blockNumber N T j)) = .card (GL N R) * .card (GL T R) ^ j * .card R ^ k := j.rec ⟨0, by simp!
  [parabolic, BlockTriangular]⟩ fun j ⟨k, H⟩ ↦ ⟨k + Fintype.card (T × BlockIndex N T j), fun R ↦
  have e (u : parabolic (R := R) (@blockNumber N T j.succ)) := (ext fun _ _ ↦ u.2 (by simp!) :
    u.1.1.toBlocks₂₁ = 0) ▸ fromBlocks_toBlocks _
  have d u := isUnit_fromBlocks_zero₂₁'.1 ⟨_, (e u).symm⟩
  by simp [Nat.card_congr (β := parabolic (blockNumber j) × _ × GL T R) (.mk (fun u ↦
       (⟨(d u).1.unit, fun _ _ ↦ (u.2 ·)⟩, _, (d u).2.unit)) (fun (x, y, z) ↦
       ⟨.mk'' (fromBlocks x.1 y 0 z) (by simp!), by simpa! [parabolic, BlockTriangular,
       lt_asymm] using! x.2⟩) (by ext : 2; use e ·)), H, Matrix, Nat.card_pi]
     ring⟩

lemma LevelPlaces.ker_reductionK₀_eq {N : Type} [Fintype N] : (X.levelModulus 1).reductionK₀.ker =
  (reduceFamily (n := N) X.placeAt).ker := by ext; simp [Units.ext_iff.trans
  ((X.levelModulus 1).matrix_ext_modulusResidue X.apart.1), funext_iff]; rfl

lemma LevelPlaces.card_levelModulus_resRing e : Fintype.card (X.levelModulus e).ResRing =
  (∏ i, (X.chosenPlace i).q) ^ e * ∏ i, (X.twistPlace i).q :=
  Fintype.card_eq_nat_card.trans (by simp [levelModulus] : Ideal.absNorm _ = _)

lemma LevelPlaces.card_GL_levelModulus : Fintype.card (GL N (X.levelModulus 1).ResRing) =
  stdLevelIndex (levelOf (n := N) X.placeAt ⊥) := by
  simp [levelOf, ← ker_reductionK₀_eq]; erw [Modulus.stdLevelIndex_levelOfSubgroup (H := ⊥)]; simp

end

variable {P} {D : Data P}

/-- For k < m, a chosen grading of Y_k as X_k plus a string of length m − 1 − k, with the
indexing `Data.indexEquivY` and the constant c = −(ȷgϖ)⁻¹, ϖ a generator of the different. -/
def Data.gradingY k (hk : k ≤ 2 * D.ϱ + 1 := by omega) := (⟨D.indexEquivY k (by grind), by grind
  [spaceY], by simp [ne], -(WeilData.j * (D.gProd * P.ϖ D.s) : D.E)⁻¹, by
    simp [ne, ne_zero_of_differentIdeal_eq_span P.different_eq_span_varpi,
      ← coe_star_ringOfIntegers, P.star_ϖ]⟩ : Grading (D.spaceY k) D.N _ _)

/-- For M = m, the presentation of Y_M as a space of rank n_M − 1 in grade 0 plus a string of
length 0. -/
def Data.lastGrading {M} (e : D.m = M) : Grading (D.spaceY M) D.N (D.InitIndex M) 0 := e ▸ by
  use .trans (.sumEmpty ..) D.lastIndexEquiv.symm,
    D.isStd_spaceY.std_induction (funext₂ ?_), ?_, 1 <;> simp [gradedGram, ne]

/-- The finite evaluation `ArrowPair.finEval` of the pair of arrows Y_{2i} → Y_{2i+1} → Y_{2i+2}:
for the middle pair if i < ϱ, the last pair if i = ϱ, and 0 beyond. -/
def Data.pairEvalY i := by refine if _ : i < D.ϱ then (middlePair (D.gradingY (2 * i))
  (D.gradingY (2 * i + 1)) (D.gradingY (2 * i + 2)) ?_ ?_ ?_).finEval else if _ : D.ϱ =
  i then (lastPair (D.gradingY _) (D.gradingY _) (D.lastGrading ?_) ?_ ?_
  congr($D.π_mul_star) ?_).finEval else 0 <;> (try simp [gradingY]) <;> grind

/-- The natural number g^{f𝗇²}, with g = g₀g₁, f the number of infinite places, 𝗇 = `Data.n` m. -/
abbrev Data.cutBound := D.gProd ^ (D.f * D.n D.m ^ 2)

/-- For a tuple y of finite adelic group elements of the Y_k, the family of finite data Υ on
Hom(Y_k, Y_{k+1}) moved by y under the twisted Weil action. -/
def Data.translatedUpsilon ϑ (y : ∀ _, _) k :=
  liftWeilFin (D.chainChar ϑ (k + 1)) (y k, y _) (upsilonY ϑ k)

/-- The finite evaluation `Data.pairEvalY` of pair i on the data of lifts 2i+1 and 2i+2, moved by
(y_{2i}, y_{2i+1}) and (y_{2i+1}, y_{2i+2}) as in `Data.translatedUpsilon`. -/
def Data.evaluatedDatum ϑ y i :=
  D.pairEvalY i (arrowProduct (translatedUpsilon ϑ y _).1 (translatedUpsilon ϑ y _).1)
end
end
