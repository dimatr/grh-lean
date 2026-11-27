import New.Weil.RallisFormula
import New.Weil.GradingsOfY
import New.Weil.FitTwists
import New.Weil.SizeEstimates
import New.Weil.LineCoordinates
import New.Weil.ExchangeTheorem
import New.Weil.PairTensorData

-- part: New.Exchange.CharacterLiftNorm
section
/-! Set-up for this proof: general results applied to the objects of this proof.

How the norm of a theta lift depends on twists. For every tame twist, the theta lift from U(W_j) to
a definite unitary group of much larger rank is injective, and its Gram form is a non-zero
twist-free constant times an explicit count at the level and the twist's conductor times a sum of
Hecke operators, which also enters the chain's norm and so cancels. The Rallis inner product in the
convergent range, with small-support data giving injectivity at a level, is known. Related work:
J.-S. Li, Non-vanishing theorems for the cohomology of certain arithmetic quotients, 1992;
Cossutta–Marshall, Theta lifting and cohomology growth in p-adic towers, arXiv 1106.2765, 2011;
Rallis, Injectivity properties of liftings associated to Weil representations, 1984; Rallis,
L-functions and the oscillator representation, 1987.

Also holds known results stated on this proof's data: Critical Hecke L-values of CM fields as
squared norms of theta lifts from U(1) (known result; see Lib.SiegelWeil.RallisInner.SharpData).

This file: Norm of the adjoint lift from W_j: twist-free constant, explicit count, Hecke sum.
Squared norm of the theta lift from U(1) is a Hecke L-value. -/
seal Finset.univ Finset.sum Finset.prod

open Fin AutChar Finset Fint Fintype Function Matrix AuxPair LevelPlaces Space Sum

seal algFormCoeff

seal petersson

variable {E r n} [Field E] [CMType E] [Fintype n] [Fintype r] [WeilData E] (O : AuxPair E r n) {P}
  (D : Data P) (ϑ : D.TameChar) {s} {j : D.LiftIndex}

/-- Let l fit O, W be nonzero and y a form on W. If ⟨z, Ξ⟩ = ⟨y, θΞ⟩ for all Ξ (θ = `AuxPair.θ`),
then z is the algebraic form of the lift of y to I_n with datum `AuxPair.fockDatum` at
`highestVector`. -/
lemma AuxPair.adjoint_theta_eq_formLift [Nonempty r] {l} (h : O.FitsParams l) {y :
  O.W.Form _} {z} (a : ∀ Ξ, inner ℂ z Ξ = O.W.petersson y (O.θ Ξ)) : z.1 =
  (stdSpace ..).toAlgForm O.isHCParam_paramV (formLift O.pairThetaKernel (typeKernel l _) _
  (O.fockDatum (highestVector _ O.paramV)) y) := (h.isEdge.isArrow O.a O.b O.auxDatum.2).elim fun A
  B ↦ congrArg _ (ext_inner_right ℂ fun Ξ ↦ by erw [a, LevelForm.inner_eq_petersson (stdSpace ..)
  O.isHCParam_paramV, ofAlgForm_toAlgForm, ← inner_eq_petersson _ ⟨_, isForm_ofAlgForm
  O.isHCParam_paramV Ξ.1⟩, A.inner_formLift_adjoint B rfl (by simp), ← inner_smul_right,
  O.theta_eq_smul_star_lift_swap, mul_comm, ← B.coe_formLift ⟨_, _⟩]; rfl : z = ⟨_, fun k ↦ by
  erw [← toAlgForm_formRep, A.formRep_formLift, ← star_highestVector, O.pairWeil_fockDatum]; simp⟩)

/-- Let y be automorphic and rapidly decreasing on U(W), fixed by the principal level at the
places M. Its theta lift by v ⊗ Υ is ∏_{w∈Q} #GL_r(k_w) times its lift by the datum
`modDatum` with real part v and function `AuxPair.levelIndicator`; Υ = `AuxPair.auxDatum`. -/
lemma AuxPair.lift_auxDatum_eq_lift_modDatum v {y} (hy : y ∈ O.W.rapidFunctions) (h : HasLevel y
  (levelOf O.chosenPlace ⊥)) : lift O.pairThetaKernel (integrated _ v O.auxDatum) y = lift
  O.pairThetaKernel (modDatum _ _ _ ((Nat.card (O.TwistGL r) : ℂ) • O.levelIndicator) v) y := by
  have e A f g :=
    (O.pairThetaKernel.lift_equivariant hy.1 (integrated _ v f) (1, (O.twistLift A).1) 1 g).symm
  simp_all [upsilon_eq_sum, ← Prod.mk_one_one, fun A ↦ h _ (mem_levelOf.2 ⟨(O.twistLift A).2, funext
    (congrFun (reduceFamily_liftResidue (w := O.placeAt) _) <| inl ·)⟩),
    (O.pairThetaKernel.exists_clm_lift hy).choose_spec, funext_iff, modDatum, Pi.smul_comp]

omit [WeilData E] in
/-- Let F be γ times `AuxPair.levelIndicator`, γ = ∏_{w∈Q} #GL_r(𝔽_w), on n × r matrices modulo the
product of the places of M and Q. Where F(y) ≠ 0, the rows of y indexed by ι form the identity, and
∑|F(y)|² = γ²(∏_{w∈Q} Nw)^{tr}. -/
lemma AuxPair.levelIndicator_support_and_normSq : let F :=
    (Nat.card (O.TwistGL r) : ℂ) • O.levelIndicator
  (∀ y, F y ≠ 0 → (inclMatrix (O.levelModulus 1).ResRing O.incl)ᵀ * y = 1) ∧ star F ⬝ᵥ F =
    Nat.card (O.TwistGL r) ^ 2 * (∏ i, (O.twistPlace i).q) ^ (O.rankDiff * card r) := by
  let e := Equiv.ofBijective (fun (y : Matrix n r _) i ↦ (y.map (levelResidueAt i) ·))
    (Injective.bijective_of_nat_card_le (fun _ _ ↦
    ((O.levelModulus 1).matrix_ext_modulusResidue O.apart.1).2 ∘ congrFun)
    (by simp [Matrix, ↓Nat.card_pi, O.card_levelModulus_resRing, ↓card_ResField, prod_pow]))
  use ?_, (?_ : O.levelIndicator = (if e · ∈ piFinset fun i ↦ piFinset fun a ↦ ite (i.isRight ∧ a ∈
    (univ.map O.incl)ᶜ) univ {inclMatrix _ O.incl a} then 1 else 0)) ▸ by simp [dotProduct,
    ← e.symm.sum_comp,
    prod_pow, apply_ite, ← card_ResField, card_compl, -mem_compl, -mem_piFinset]; ring!
  repeat simp_all [levelIndicator, (O.levelModulus 1).matrix_ext_modulusResidue O.apart.1, e,
    mem_ite, ← ext_iff, funext_iff, mul_apply, inclMatrix, -elim_inl, -elim_inr]

/-- The number [K₀ : K′ ∩ K₀] γ² (∏_{w∈Q} Nw)^{tr} / #GL_r(R), with K′ = `AuxPair.levelGroup`, γ =
∏_{w∈Q} #GL_r(𝔽_w), R = O_E/MQ. -/
noncomputable def AuxPair.gramFactor : ℂ := stdLevelIndex O.levelGroup * Nat.card (O.TwistGL r) ^ 2
  * (∏ w, (O.twistPlace w).q) ^ (O.rankDiff * card r) / card (GL r (O.levelModulus 1).ResRing)

/-- The term ρ(γ)⟨y', R(γ)y⟩ (`cosetTerm`, rank n' = r + t, character μ_j⁰ϑυ^{⌊n'/2⌋}, γ modulo
elements integral off 𝔪𝔪̄) divided by #(O_E/𝔪)^{n'r}, for 𝔪 = MQ. -/
noncomputable abbrev Data.rallisTerm j (V : Space _ _ s) (y' y : D.principalForms V) γ :=
  cosetTerm (card (D.Y 1)) (D.auxPair ϑ j).b (D.𝔪 ϑ 1).places.conjClosureᶜ y'.1 y γ / card
  (D.Y 1 × D.RowIndex → (D.𝔪 ϑ 1).ResRing)

/-- For each eigensystem p there is a family F such that, for every form y on Y₀ of eigensystem
p and every split w with w, w̄ not among the chosen places over g, the lift ιy for the
trivial twist has eigensystem F_w at w. -/
lemma Data.exists_isSphericalWith_iota p : ∃ F : _ → _, ∀ y ∈ D.eigenPart _ p,
  ∀ w (h : D.IsSplitOffLevel w), IsSphericalWith (rightRegular ..) h.1 (F w) (D.ι .one y).1 := by
  simp [ι, isSphericalWith_toAlgForm_iff, -Subtype.forall]
  rw [← val_last D.m]
  induction' last _ using
    induction with i ih; exact ⟨_, fun _ h _ ↦ D.isSphericalWith_of_mem_eigenPart _ h⟩
  refine ⟨_, fun y a w h ↦
    (isSphericalWith_formLift card_sum ?_ ?_ h.1 ((projOn_integrated ..).trans (congrArg _
    (projOn_name_vacElem _ ?_))) (D.isArrow_datumY _ i.2).1 (ih.choose_spec y a w h)).smul⟩
  any_goals apply HasWeight.charUnramifiedAt <;> apply (auxPair ..).tame_eq_one
  all_goals simp_all [places_levelModulus, IsSplitOffLevel, auxPair, levelPlaces]; tauto

/-- Adjointness for 1 ≤ j ≤ m: the class sum inner product of θ_j^* y with a form Ξ on V_j
equals the Petersson product on W_j of y with the theta lift θΞ for the pair (W_j, V_j). -/
lemma Data.inner_auxLift y Ξ : inner ℂ (D.auxLift ϑ j y) Ξ = (D.spaceW j).petersson y ((D.auxPair ϑ
  j).θ Ξ) := (exists_theta_to_principalForms ..).choose_spec j.2 Ξ ▸ LinearMap.adjoint_inner_left ..

/-- For 1 ≤ j ≤ m there is A ≠ 0 such that, for every tame ϑ, θ_j^* is injective on forms of
principal level g on W_j, and ⟨θ_j^* y', θ_j^* y⟩ = A·δ·∑_γ R_j(y', y, γ) for such forms,
δ = `AuxPair.gramFactor`, R_j = `Data.rallisTerm`.

How the norm of a theta lift depends on twists. -/
lemma Data.auxLift_injective_and_hasSum_inner : ∃ A ≠ 0, ∀ ϑ, Injective (D.auxLift ϑ j) ∧ ∀ x y,
  HasSum (A * (D.auxPair ϑ j).gramFactor * D.rallisTerm ϑ j _ x y ·)
  (inner ℂ (D.auxLift ϑ j x) (D.auxLift ϑ j y)) := by
  obtain ⟨C, hC, H⟩ := rallis_inner_product_euler (S :=
    D.spaceW j) (D.fitsParams_auxPair .one j).isEdge (by grind [card_rowIndex, card_V])
  use C * card (WeylIndex (D.Y 1) (D.auxPair .one j).κ), mul_ne_zero hC NeZero.out, fun ϑ ↦ ?_
  let O := D.auxPair ϑ j
  obtain ⟨A, f, c⟩ := ((D.fitsParams_auxPair ..).isEdge.isArrow O.a O.b O.auxDatum.2).1,
    O.levelIndicator_support_and_normSq
  have U y := (congrArg _ (O.adjoint_theta_eq_formLift (D.fitsParams_auxPair ϑ j)
    (D.inner_auxLift ϑ y))).trans ((ofAlgForm_toAlgForm
    ..).trans (congrArg _ (A.eq_formLift_of_coe_eq _ (A.coe_formLift _ ▸
    O.lift_auxDatum_eq_lift_modDatum _ (A y.1).1 (mem_levelSpace_formRep_iff.1 y.2)))))
  replace H (y : D.principalForms _) := H O.a O.b (isSharp_modDatum (stdSpace ..) _
    (.inr (by apply nonempty_modulus_places)) _ f (O.tame_eq_one · <|
    places_levelModulus.ge.mt ·) (by simp [↓c, prod_eq_zero_iff])) _ (mem_levelSpace_formRep_iff.1
    y.2 · ∘ by simp [O.ker_reductionK₀_eq, levelOf, funext_iff]; tauto)
  use .of_ker _ fun y z ↦ Subtype.ext ((H y).1 (Subtype.ext (U y ▸ z ▸ map_zero _))), fun x y ↦ ?_
  rw [LevelForm.inner_eq_petersson (stdSpace ..) O.isHCParam_paramV, U, U]
  exact (((H y).2 _).mul_left _).congr_fun fun _ ↦ by push_cast [gramFactor, c]; ring!

/-- Let 1 ≤ j ≤ m, w split, w, w̄ off the chosen places above g and Q, y on W_j of eigensystem
p, with Hecke polynomial P at w. Then θ_j^*y is spherical at w, eigenvalue ∏_{l<n−r}(1 −
q^{l+r/2}χ_W(w)X)·P(q^{(n−r)/2}χ_Wχ_V⁻¹(w)X); r, n ranks of W_j, V_j. -/
lemma Data.lifts_auxLift {p y} (hy : y ∈ D.eigenPart _ p) : (D.auxPair ϑ j).Lifts (D.auxLift ϑ j y)
  (p ⟨·, ·⟩) := fun w hw hS ↦ adjoint_theta_eq_formLift _ (D.fitsParams_auxPair ϑ j)
  (D.inner_auxLift ϑ y) ▸ (isSphericalWith_toAlgForm_iff ..).2 (isSphericalWith_formLift (by
    simp [AuxPair.rankDiff]) (HasWeight.charUnramifiedAt rfl rfl) (by grind
  [HasWeight.charUnramifiedAt, tame_eq_one]) hw (by simp_all [auxDatum, projOn_name_vacElem,
  places_levelModulus]) ((D.fitsParams_auxPair ϑ j).isEdge.isArrow _ _ (auxDatum _).2).1
  (D.isSphericalWith_of_mem_eigenPart _ hy ⟨hw, by simp_all [auxPair, levelPlaces]⟩))

/-- For 1 ≤ j ≤ m, the lift θ_j^* from W_j to V_j is injective on forms of parameter ς and
principal level g. -/
lemma Data.auxLift_injective : Injective (D.auxLift ϑ j) :=
  (D.auxLift_injective_and_hasSum_inner.choose_spec.2 ϑ).1

/-- For 1 ≤ j ≤ m, θ_j^* is equivariant for the product of the GL_r(𝔽_w) over the chosen w above
g: it intertwines `Data.principalRep` on forms on W_j with `AuxPair.formAction` on forms on V_j. -/
lemma Data.auxLift_principalRep s y : D.auxLift ϑ j (D.principalRep _ s y) =
  (D.auxPair ϑ j).formAction s (D.auxLift ϑ j y) := ext_inner_right ℂ
  (((formAction _).apply_bijective s).2.forall.2 fun Ξ ↦ by
  rw [inner_auxLift, ← funext (theta_mul_eq_theta_formAction _ _ (reduceFamily_liftResidue s) Ξ),
    ← (exists_theta_to_principalForms ..).choose_spec j.2]; exact
    (inner_formRep ..).trans ((innerAt_formAction ..).trans
    ((exists_theta_to_principalForms ..).choose.adjoint_inner_left ..)).symm)

open ComplexConjugate MeasureTheory Complex MulAction Subgroup

attribute [-simp] Nat.card_eq_fintype_card mem_classAut

variable {E n : _} [Field E] [CMType E] [WeilData E] [Fintype n] (X : LValueData E n)

attribute [local simp] prod_eq_zero_iff card_ResField places_levelModulus classSum apply_eq_evalForm
  AuxPair.rankDiff

unseal univ in
/-- Ξ lifts the constant system 1 (`AuxPair.Lifts`): at w ≠ w̄, both off M and Q, it is spherical
with
Hecke polynomial ∏_{l<|n|−1}(1 − q^lαT)·(1 − q^{|n|−1}αβ⁻¹T), where α, β are `AutChar.frobValue` of
a, b against ranks 1, |n|. -/
lemma LValueData.auxPair_lifts_trivialLift : X.auxPair.Lifts X.trivialLift 1 := fun _ hw h ↦ by
  have := hecke_transfer_of_equivariant (k :=
    X.auxPair.rankDiff) (by simp [X.one_lt_card.le]) (X.a_hasWeight.charUnramifiedAt rfl rfl) (by
    apply X.b_hasWeight.charUnramifiedAt <;> grind [unramified]) hw (f :=
    X.auxPair.auxDatum.1) (projOn_name_vacElem _ (by aesop)) (stdClassSum X.chosenLevel
    fun g ↦ by use ⟨(X.kernelValue 1 · g), ?_⟩ <;> simp [kernelValue, funext_iff]) 1 (rightRegular
    ..) fun g _ ↦ by ext1; simpa [trivialLift, kernelValue,
    rep_apply_apply] using! congr($(X.trivialLift_eq_stdClassSum_translate g) _).symm
  rw [show (_ : _ →ₗ[ℂ] _) _ = ↑X.trivialLift by ext1; simp [trivialLift]; rfl] at this
  simpa [IsSphericalWith, (isSphericalWith_trivialHecke _ _).2, heckePolyEval, smul_smul,
    sum_range_succ]

/-- For even rank n ≥ 4, ⟨Ξ, Ξ⟩ = C·`hookNumber`·d·L^S(n/2, μ⁻¹)·(∏_{w ∈ Q} Nw)^{n−1}, where d is
the dimension of the weight, S the set of the places of M and Q, and C ≠ 0 depends on X only
through the places of M.

Known result: Critical Hecke L-values of CM fields as squared norms of theta lifts from U(1). -/
lemma LValueData.inner_trivialLift_self_eq_L {k} (hM : 2 * k = card n) (hk : 1 < k) :
    let C := (stdSpace E n).quotMeasure.real ⊤ * (stdSpace E Unit).quotMeasure.real ⊤ / eulerProd
      (K := E) realZetaCoeff (card n / 2 :); C ≠ 0 ∧ inner ℂ X.trivialLift X.trivialLift =
      C * (∏ i, ((X.chosenPlace i).q - 1) :) * hookNumber X.auxPair.κ (rankAt n) * card (WeylIndex n
      X.auxPair.κ) * X.μ⁻¹.L X.places k * (∏ i, (X.twistPlace i).q :) ^ (card n - 1) := by
  let O := X.auxPair
  have G (w : FinPlace E) := And.intro
    ((index_rangeParabolic (R := ResField w) O.incl).trans (index_stabilizer_line (O.incl ())
    fun _ ↦ forall_congr' (by grind [lt_iff_le_not_ge, le_Prop_eq]))) ((congrArg _ (ext fun _ ↦
    funext_iff.trans Unique.forall_iff : stabilizer (GL n (ResField w)) (inclMatrix (ResField w)
    O.incl).col = _)).trans (index_stabilizer_GL_vector (by simp [inclMatrix, funext_iff])))
  obtain ⟨⟨f, c⟩, ⟨A, B⟩, ⟨⟩⟩ := O.levelIndicator_support_and_normSq, (by simpa [realZetaCoeff,
    apply_ite] : (∀ w : FinPlace E, ‖realZetaCoeff w‖ ≤ 1) ∧ 1 < (k : ℝ)), (by lia : k = card n / 2)
  let S := univ.map ⟨_ ∘ X.placeAt ⊕ᵥ X.placeAt,
    (star_injective.comp X.apart.1).sumElim X.apart.1 X.apart.2⟩
  let D := X.places.conjClosure
  have a w : w ∈ S ↔ w ∈ D := by simp [S, D]; grind [star_star]
  obtain ⟨o, U⟩ := ((stdSpace E Unit).isAutomorphic_const 1).mem_rapidFunctions,
    places_levelModulus (S := X.1) (c := 1) ▸ isSharp_modDatum (stdSpace
    ..) O.b (by simp) _ f (by simp_all [unramified, O]) (by simp [↓c, NeZero.ne])
  have p := by simpa [heckeCoeff, Set.indicator, cpow_neg, ← HeckeChar.atUnif.eq_1] using
    (hasProd_eulerProd (X.hasWeight.inv.isHeckeOfType.norm_heckeCoeff_le (S := D)) B).div₀
                 (hasProd_eulerProd A B) (by simp [eulerProd_eq_exp, *])
  obtain ⟨⟨i, P⟩, F⟩ := inner_product_formula (hM ▸ by simpa) O.a O.b (U.clean (O.harmonicPoly
    (highestVector _ O.paramV))) o o, (fockPairing_toPoly_toPoly (conj ∘ highestVector O.κ _)
    _).trans (congrArg _ (gramForm_highestVector_self (O.isHCParam_paramV ·|>.1)))
  let T R := S ∪ R.image star ∪ R
  have Q := tendsto_nhds_unique_of_frequently_eq (.mul p (tendsto_partialIntegral D i))
    tendsto_const_nhds (Filter.frequently_atTop.2 fun R ↦ ⟨T R, le_sup_right, R.induction (by
    simp [-prod_mul_distrib, T, a, partialIntegral, localLevel]; rw [prod_map, prod_sum_type]) fun w
    R _ ↦ .trans ?_⟩)
  by_cases e : w ∈ T R; rw [(?_ : T _ = T R)]; swap
  have ⟨_, t, ht, r⟩ :=
    exists_hasSum_vacuumCoeff_at_place X.hasWeight (X.unramified w ?_) (X.unramified _ ?_) hk
  rw [(?_ : T _ = T R ∪ {w, star w}), prod_union, mul_assoc]
  refine congrArg _ (.trans congr($(Finset.prod_congr rfl ?_) * _) (((hM ▸ r).mul_right _).unique
    (hasSum_partialIntegral_coset _ t (U.vacuum_off _ _ ?_) i (fun _ ↦ ?_) (SetLike.ext ?k) ht :)))
  case' k => simp [localLevel]
  any_goals clear * - e a; grind (gen := 9) [star_star, disjoint_left, mem_localLevel,
    Gf.mem_supportedOn, one_mem]
  erw [(U.partialIntegral_eq _ (y := 1) (by simp) O.detExp 1 1).2] at Q
  have Y := (eq_inv_smul_iff₀ (by simp)).1 ((O.lift_auxDatum_eq_lift_modDatum
    (O.harmonicPoly (highestVector _ O.paramV)) o (by simp)).symm.trans (funext fun _ ↦
    (integral_quotMeasure_eq_classSum (by simpa using! (pairThetaKer ..).theta_rat_mul) (by
    simp_intro _ [X.theta_pairWeil_fockDatum, O]; rfl) _ (X.kernelForm_invariant.2.trans fun _ ↦ by
    simp_intro ..)).trans (congrArg _ ?_) : _ = (_ : ℂ)⁻¹ • ofAlgForm O.paramV 1 X.trivialLift.1))
  erw [← map_toPoly, toPoly_eq_rename_harmonicPoly, MvPolynomial.map_rename, show _ = fockPairing ℂ
    _ _ from (congrArg _ (MvPowerSeries.rename_coe ..).symm).trans (jet_rename ⟨_, ?_⟩ rfl _)] at F
  simp +instances [↓← prod_mul_distrib, ↓X.trivialLift.inner_eq_petersson (stdSpace ..)
    O.isHCParam_paramV, mul_left_comm (conj _), ← Y, O, ↓c, AutChar.L, hM, ← Set.Sum.elim_range,
    realPairWeil_schurCoeffPoly X.isLiftWeight, D, X.card_GL_levelModulus Unit,
    X.card_levelModulus_resRing, Nat.card_pi, X.apart.2, petersson, mul_assoc, ← pow_mul',
    realInner_polyVector, ↓relIndex_levelOf,
    index_pi_univ, auxLevel, HeckeChar.atUnif, mul_pow, realZetaCoeff_factor_mul,
    harmonicPoly_eq_schurCoeffPoly, modDatum, heckeCoeff, G, Nat.card_units,
    Nat.card_congr (Units.mapEquiv (@uniqueRingEquiv Unit (ResField _) ..).toMulEquiv).1] at P Q F ⊢
  simp (disch := simp) only [F, P, ← geom_sum_mul, ← one_div, one_sub_div, prod_mul_distrib,
    eulerProd_eq_exp A B, prod_div_distrib, prod_pow] at Q ⊢
  use by simp [measureReal_univ_ne_zero]
  field_simp (disch := norm_cast; simp [ne_of_gt]) at Q ⊢; rw [Q]
  simp_intro _ [Prod.ext_iff]
  simp [O, algFormCoeff_apply, trivialLift, star_highestVector]
end

-- part: New.Rows.LineArithmetic
section
/-! Twisted theta forms lie on one line. Explicit theta forms on U(W_j), whose coefficient vectors
are integral off the conductor and small when untwisted, are for every twist multiples of one
twist-free form, with squared ratio a product of Hecke L-value ratios and a power of the conductor's
norm, and this gives the number carrying the twist. The rank one case (the lift is a scalar of
square modulus an L-value), twisting on a square block and integral theta data are known. Related
work: T. Yang, Theta liftings and Hecke L-functions, 1997; Böcherer–Schmidt, p-adic measures
attached to Siegel modular forms, 2000; Harris–Li–Skinner, The Rallis inner product formula and
p-adic L-functions, 2005.

This file: Coefficient vectors are integral off the conductor and small when untwisted. -/

open RingHom ComplexConjugate Finset Fintype Ideal Matrix MvPolynomial NeZero Real Sum

variable {P} {D : Data P} (j : D.LiftIndex)

lemma Data.norm_mul_gProd_pow_mem_modulus {ϑ c} : ↑(ϑ.levelNorm * D.gProd ^ c) ∈ (D.𝔪 ϑ
  c).ideal := by with_unfolding_all simpa [← ϑ.Q.prod_coe_sort] using! mul_mem_mul_rev (pow_mem_pow
  (span_piGBar D ▸ mem_span_singleton.2 ⟨_, D.piGBar_mul_star.symm⟩) c) (prod_mem_prod fun _ _ ↦
  absNorm_mem _)

/-- One c ≠ 0, depending on j, makes every y = conj(c·`Data.lineMultiplier` ϑ j i h) integral at h
(`weylGauge` ≤ 1) for all ι: ℂ → ℂ_p, p prime to N(Q); if Q = ∅, all Aut(ℂ)-conjugates have squared
norm ≤ exp(rB₀).

Twisted theta forms lie on one line. -/
lemma Data.lineMultiplier_integral_and_small : ∃ c ≠ (0 : ℂ), ∀ i ϑ h, let y := star (c •
    lineMultiplier ϑ j i h); (∀ p [Fact p.Prime] [PadicPlace p], p.Coprime ϑ.levelNorm →
    weylGauge _ 0 h y ≤ 1) ∧ (ϑ.Q = ∅ → ∀ φ : ℂ ≃+* ℂ, weylNormSq (φ ∘ y) ≤ .exp (D.r * D.B₀)) := by
  have ⟨n, d, H, H₀, H₁, hQ⟩ := exists_denom_linePolyCoords j
  grw [(card_detIndex j _).2, sum_const, smul_eq_mul] at d; have g :=
    d.trans (D.nat_le_of_hasLogBound (B := D.gProd))
  obtain ⟨⟨c₀, _, K₀⟩, ⟨c₁, _, K₁⟩, ⟨c₂, _, K₂⟩, c, _, E⟩ := exists_modKernel_integral_bound
    (Fin D.m) D.CarrierIndex D 0, exists_modKernel_integral_bound (Fin j) (BigIndex j) D 0,
    exists_modKernel_integral_bound (LPlusIndex j) (BigIndex j) D n,
    exists_modKernel_neg_left (stdSpace D.E (Fin j)) (stdSpace _ (BigIndex j))
  use D.chosenGroupOrder * D.chosenGroupOrder * c₂ * H * c₀ * conj c₁ *
    c, by simp [ne]; grind [norm_zero]
  intro ⟨u, i⟩ ϑ h Y
  obtain ⟨⟨hL, hY⟩, e⟩ := (Space.exists_short_basis_stdSpace P.cycloConductor_mem_different
    i.1.out).choose_spec, let b := (@hasWeight_liftChar _ D ϑ j).mul_upsilonU1_pow (bigCharExp
      j); PProd.mk b (b.inv.mul_upsilonU1_pow (.card (BigIndex j)))
  specialize K₀ (unitModulus _) ϑ.levelNorm 1 (twistedChi_hasWeight ϑ j) .one ⟨⟩ (by simp) 1
  specialize K₁ _ ϑ.levelNorm (conj ∘ Pi.single (inclMatrix _ (inl ∘ inr ∘ inl)) 1 <|
    (D.𝔪 ϑ 2).normNegOne • ·) .one e.2 norm_mul_gProd_pow_mem_modulus (by simp [apply_ite]) 1 1
  specialize K₂ _ _ (lPlusDatum ϑ j u) e.1 e.1 norm_mul_gProd_pow_mem_modulus fun _ ↦
    ite_mem.2 ⟨fun _ ↦ sum_mem fun _ _ _ _ _ ι ↦ ((ι.compAddChar _).norm_apply _).le, by simp⟩
  rw [(?_ : Y = (D.chosenGroupOrder * (D.chosenGroupOrder * 1) : ℂ) • stdClassSum
    (Kf D.E D.CarrierIndex) fun w ↦ stdClassSum (Kf D.E (Fin D.m)) fun v ↦ star
    ((_ * conj _ : ℂ) • c₂ • modKernelBilin _ _ _ _ _ (1, _) (1, h) _ ∘ (H • linePolyCoords j i)))]
  use fun p _ _ hp ↦ ?_, fun _ φ ↦ let σ := starRingAut.trans φ; by
    grw (transparency := default) [weylNormSq_comp_smul, (sqrt_le_iff.1 (sqrt_weylNormSq_classSum_le
      φ fun u ↦ sqrt_weylNormSq_classSum_le _ fun v ↦ sqrt_weylNormSq_le_of_dual σ fun w k ↦ by
    simp_rw [dotProduct_smul, dotProduct, Function.comp, ← smul_eq_mul (w _), ← map_smul, ← map_sum]
    rw [smul_eq_mul, map_mul, map_mul]
    refine norm_mul_le_of_le (norm_mul_le_of_le ((K₀ v u ?_).2 ?_ ?_ ?_ ?_ _ 1 1 ?_ ?_) ((K₁ h
      ?_).2 ?_ ?_ ?_ ?_ (starRingAut.trans σ) 1 1 ?_ ?_)) ((K₂ _ _ _ ?_).2 ?_ ?_ g ?_ σ _ _ (fun σ
      _ ↦ by rw [lPlusDatum]; split; simpa using! norm_sum_le_of_le univ fun _ _ ↦
      ((σ.toRingHom.compAddChar _).norm_apply _).le; simp) fun z hz ↦ by
      specialize k ((H : ℂ) • eval z ∘ linePolyCoords j i); grw (transparency :=
        default) [weylNormSq_comp_smul, (weylNormSq_linePolyCoords_le j _ _ σ z).2 ⟨fun τ a b ↦
        (hY (.comp σ (Φ τ)) ..).trans (by simpa using D.le_of_hasLogBound), hz⟩, (card_detIndex j
        _).2] at k; simpa [dotProduct] using k; use D.le_of_hasLogBound) <;> simp +contextual
      [smul_sum, smul_comm (_ ^ n), -aeval_eq_bind₁, apply_ite, *,
      -zsmul_eq_mul, ↓card_rowIndex] <;> clear * - <;> grind)).2]
    clear * - g d H₀ H₁; repeat grw [D.card_stdClasses_le_exp principalLevel_le_Kf]
    grw [H₁, g, card_eq_nat_card, card_GL_le, Modulus.card_resRing_le
      (levelModulus_ideal_le norm_mul_gProd_pow_mem_modulus), ← le_exp_of_log_le]
    all_goals simp [log_mul, ne, log_sqrt, pos, sqrt_eq_zero', ← pow_mul, twist_one_spec]
    grw [d]; use D.le_of_hasLogBound
  swap; ext l; simp [Y, -Pi.single_apply, inv_mul_cancel_comm, ← Pi.evalAlgHom_apply ℂ _ l (_ • _),
    lineMultiplier, bigChar, E, carrierXi, mul_classSum,
    map_classSum, ↓← Int.cast_smul_eq_zsmul ℂ H, modKernelI]; ac_rfl
  iterate 2 apply weylGauge_classSum_le_one _ (card_classAut_dvd_chosenGroupOrder (by simpa using
    D.nat_le_of_hasLogBound) le_rfl); intro
  rename_i w _; let ι := ιₚ.comp conj
  choose γ hγ _ using fun {n} [Fintype n] ↦ (exists_mul_mem_integralAbove p · 1 (stdSpace D.E n))
  erw [one_smul, star_smul, weylGauge_smul]; use mul_le_one₀ (by
    simpa [modKernel_embFin_mul (twistedChi_hasWeight ..) .one, by simpa using
      (modKernel_embFin_mul (L := Fin j) .one e.2 · · 1 1 (γ h)
      1)] using! norm_mul_le_of_le (@(K₀ _ _ (by simp)).1 p _ ⟨ι⟩ hp (hγ _) (hγ _)
    (by simp)) ((K₁ _ (by simp)).1 _ hp (by simp) (hγ h) (by simp))) (norm_nonneg _) ?_
  erw [← (?_ : (stdSpace ..).weightRep _ 0 _⁻¹ _ = star _), ← weylGauge_embFin,
    Representation.self_inv_apply, weylGauge_le_one_iff _ (hγ _)]
  use fun l ↦ @(K₂ _ _ _ (hQ i (D.shortRows i * (γ _).1.1ᵀ) l).1).1 p _ ⟨ι⟩ hp
    (sum_mem_integralAbove 1 1 (by simp) (sum_mem_integralAbove _ _ (hγ i.1.out) (hγ w))) (hγ h)
    ((hQ ..).2 _ fun τ x y ↦ let σ := ι.comp (Φ τ); by simpa [← Matrix.map_mul,
      shortRows, ← transpose_mul, mul_assoc, Function.comp_def] using! ((adeleExtension_mem_intGL σ
      (hγ i.1.out)).isIntMatrix.mul (N :=
      .map _ (adeleExtension σ)) (norm_adeleExtension_le_one _ <| hL · ·) y x))
  apply star_injective ((map_weightRep conj ..).trans _); ext
  simp [weylRep, mulVec_eq_sum, RingHom.comp, @starRingEnd_apply D.E, ← modKernelBilin_apply,
    -zsmul_eq_mul, mul_left_comm _ c₂, ← mul_sum, ← smul_sum, -coe_units_inv]
  simp_rw [← smul_eq_mul (schur ..), ← map_smul, ← map_sum]
  congr 2; apply (modKernel_embFin_mul e.1 e.1 ..).trans
  erw [twoSidedSubst_firstColsCoord _ _
    (.trans (congrArg _ (congrArg _ ?_)) (twoSidedSubst_stackedDetProd _ (detRows j i) ..))]
  simp [← modKernelBilin_apply, ← map_det, mul_pow, ← card_detIndex_add_bigCharExp,
    add_assoc, -card_sum, ← mapMatrix_apply]
  field_simp [prod_ne_zero_iff]
  ext τ (k | k) x (y | y | y | y) <;> simp [U.sum, detRows, mul_apply,
    inclMatrix] <;> split <;> simp [eq_comm]
end

-- part: New.Exchange.TriangleLevelExponent
section
/-! Set-up for this proof: size bookkeeping for the data of this proof.

Also holds known results stated on this proof's data: Critical Hecke L-values of CM fields as
squared norms of theta lifts from U(1) (known result; see Lib.SiegelWeil.RallisInner.SharpData).

Also holds known results stated on this proof's data: Integral group-ring elements interpolating
twisted Hecke L-values, with norm relations (known result; see New.Selmer.ValueFamilies).

This file: Integrality of the lift; integral group-ring element interpolating tame twists of
L-values. Normalised squared norm of a character's theta lift is constant times Hecke L-value.
Exchange constant for a twist rewritten through L-value ratios and conductor norms. Spaces and
characters of the triangle of lifts. -/

open Circle Complex Finset Fintype LValueData Parameters LevelPlaces

variable {P D} (ϑ : D.TameChar) {p : @Data.Pair P D}

/-- F(ϑ′) = Σ c_a ϑ′(u_a) for all tame ϑ′ with the modulus Q of ϑ, for finitely many points u_a
of U(1)(𝔸) and c_a integral at all l prime to Q. -/
def Data.TameChar.IsIntegralMeasure (F : D.TameChar → ℂ) :=
  ∃ (α : Type) (_ : Fintype α) (u c : α → _),
  (∀ a, c a ∈ integralAway ϑ.levelNorm) ∧ ∀ ϑ', ϑ'.Q = ϑ.Q → F ϑ' = ∑ a, c a * ϑ'.toAutChar.1 (u a)

/-- If the function F of tame characters is an integral measure for ϑ
(`Data.TameChar.IsIntegralMeasure`), then so is ψ ↦ |F(ψ)|². -/
lemma Data.TameChar.IsIntegralMeasure.norm_sq {F} : ϑ.IsIntegralMeasure F →
  ϑ.IsIntegralMeasure (‖F ·‖ ^ 2) := fun ⟨α, _, u, c, a, b⟩ ↦ ⟨_,
  inferInstance, fun (x, y) ↦ u x * (u y)⁻¹, _, fun x ↦ mul_mem (a x.1) fun l ↦ (a x.2 l · <| ·.comp
  _), fun _ e ↦ by simp [*, ← mul_conj', univ.sum_mul_sum, sum_prod_type, ↓coe_inv_eq_conj]; ac_rfl⟩

/-- If F is an integral measure (`Data.TameChar.IsIntegralMeasure`) at the trivial tame character 1,
then
|ι F(1)| ≤ 1 for every prime l and every isomorphism ι from ℂ to the algebraic closure of
ℚ_l. -/
lemma Data.TameChar.IsIntegralMeasure.norm_apply_one_le {F l} [Fact l.Prime]
  (ι : ℂ ≃+* PadicAlgCl l) : (@one P D).IsIntegralMeasure F → ‖ι (F one)‖ ≤ 1 := fun ⟨_, _, _, _, a,
  b⟩ ↦ by simpa [b, twist_one_spec, ← map_sum] using!
    ((@embValRing l _ ⟨complexToCp ι⟩).sum_mem fun _ _ ↦
  a _ l (by simp [levelNorm, twist_one_spec]) (complexToCp ι))

namespace Data.Pair

instance {l} [D.HasLogUpper D.t l] : D.HasLogUpper p.z l := D.hasLogUpper_of_le p.7.2

variable {n} [Fintype n] (H : p.HasLiftRank n) (ϑ : D.TameChar) (s : ℤˣ)

/-- κ₀^|n| times the indicator modulo MQ (`AuxPair.levelIndicator`) of integral vectors congruent to
the chosen basis vector e_ι at M and with ι-th coordinate 1 at Q, on the vacuum; κ₀ =
`Parameters.vacuumScale`. -/
noncomputable def pointDatum := P.vacuumScale D.s ^ card (n × Unit) • vacuumDatum (stdSpace ..)
  (stdSpace ..) _ (lValueData H ϑ).auxPair.levelIndicator

/-- The jets `LValueData.kernelValue` of the pair p twisted by ϑ, at scale π̄·per, on the point
datum `Data.Pair.pointDatum`: a function on U(1) × U(2z) at finite points. Here π =
`Data.piG` and per = `Parameters.jetScale`. -/
noncomputable abbrev pointKernel :=
  (lValueData H ϑ).kernelValue (star ↑D.piG * P.jetScale D.s) (pointDatum H ϑ)

/-- For |n| = 2z ≥ 4, Ξ_ϑ(h) is the sum of the jets `Data.Pair.pointKernel` at (u·k_A, h), over
representatives u of the classes of U(1) at principal level at the chosen places above g and
A in ∏_{w∈Q} k_w^×, with k_A = `LevelPlaces.twistLift` A. -/
lemma trivialLift_apply h : trivialLift H ϑ h = ∑ c : StdClasses (n :=
  Unit) D.chosenLevel × TwistGL _ Unit, pointKernel H ϑ (c.1.out * (D.levelPlaces ϑ).twistLift c.2)
  h := by erw [apply_eq_evalForm, map_smul, map_classSum, classSum,
  funext (D.classAut_eq_bot_of_le_chosenLevel
  le_rfl (by simpa using D.nat_le_of_hasLogBound))]; simp [smul_sum, kernelValue, pointDatum,
  schurJet_jetSeries_eq_smul (isLiftWeight _) (_ * _), sum_prod_type, smul_smul, rep_apply_apply,
  kernelForm, Matrix.sum_mulVec, boxes, AuxPair.upsilon_eq_sum,
  ↓← apply_eq_evalForm]; simp [AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card]; rfl

/-- If the prime l is coprime to the norm of every place in Q(ϑ), then
`Data.Pair.denomBound` times the jet
`Data.Pair.pointKernel` at (g, h) is integral at h: its gauge `weylGauge` for any embedding j of ℂ
in ℂ_l is at most 1. -/
lemma weylGauge_pointKernel_le_one {l} [Fact l.Prime] {j : PadicPlace l} g h (hl :
  l.Coprime ϑ.levelNorm) : weylGauge _ 0 h ((p.denomBound : ℂ)
  • pointKernel H ϑ g h) ≤ 1 := by simpa +contextual [weylGauge, weylRep, schur_eq_one] using!
  (mem_raises_of_dvd (pointDatum H ϑ) (hκ := isLiftWeight _) (ha := a_hasWeight _) (hb :=
  b_hasWeight _) (K := ⊤) (smul_vacuumDatum_mem_standardData norm_mul_gProd_pow_mem_modulus
  (by grind [AuxPair.levelIndicator, one_mem, zero_mem]) hl) norm_star_piG_le_one
  (by simp [denomBound, boxes, AuxPair.κ, mixedWeight, (lValueData H ϑ).one_lt_card, ← H.1]) _ _ 1)

/-- One group ring element gives all twists of a modulus: the normalised values
`Data.Pair.intAlgPart` at the tame characters ϑ′ of modulus Q(ϑ) are Σ c_a ϑ′(u_a), with u_a,
c_a free of ϑ′ and c_a integral at primes prime to Q.

Known result: Integral group-ring elements interpolating twisted Hecke L-values, with norm
relations. -/
lemma isIntegralMeasure_intAlgPart : ϑ.IsIntegralMeasure (intAlgPart H) := let g (a : StdClasses
    (n := Unit) D.chosenLevel × TwistGL _ Unit) := a.1.out * (D.levelPlaces ϑ).twistLift a.2
  ⟨_ × _, _, fun x ↦ G.det (s := 1) ((1, g x.2) / (1, g x.1)), _, fun x l _ hl j ↦
    (@embValRing _ _ ⟨j⟩).1.mul_mem (smul_classSum_mem _ (D.card_classAut_dvd_chosenGroupOrder (K :=
    (lValueData H ϑ).auxPair.levelGroup) (H.1.trans_le D.nat_le_of_hasLogBound) levelOf_le_Kf)
    (gramForm_mem_embValRing _ (weylGauge_pointKernel_le_one H (ϑ.pow 0) (g x.2) _ hl) <|
    weylGauge_pointKernel_le_one H _ (g x.1) · hl))
    (by simp [hl.norm_natCast_eq_one, -Nat.cast_prod] : ‖j (ϑ.levelNorm ^ (card n - 1))⁻¹‖ ≤ 1), by
  rintro ⟨⟩ rfl
  rw [sum_prod_type]; simp [intAlgPart, ← coe_algebraMap, ← inner_self_eq_norm_sq_to_K, inner,
    LevelForm.innerAt_eq_stdClassSum, mul_sum, sum_div, classSum_sum, ← coe_inv_eq_conj,
    ← mul_classSum, trivialLift_apply, TameChar.pow, kernelValue, pairWeil_apply,
    rankTwist, ↓map_div]
  congr with; congr with; ring!⟩

attribute [local simp] intAlgPart denomBound finite_isChosen twist_one_spec Finset.prod_eq_zero_iff
  NeZero.ne mul_div_mul_left

/-- For a pair p = (ν, z) with z ≥ 2 there is A ≠ 0 such that `Data.Pair.intAlgPart` at every tame
character ϑ equals A·L(z, (νϑ)⁻¹), without Euler factors at the chosen places, the places of
Q(ϑ) and their conjugates. -/
lemma intAlgPart_eq_mul_L : ∃ A ≠ 0, ∀ ϑ, intAlgPart H ϑ =
  A * (p.ν * ϑ.toAutChar)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z := by
  have h ϑ := (lValueData H ϑ).inner_trivialLift_self_eq_L H.1.symm H.2
  refine ⟨_, ?_,
    fun ϑ ↦ by simp_all [trivialLift, norm_smul, div_eq_iff, mul_pow, range_chosen, levelPlaces,
    ← ϑ.Q.prod_coe_sort, ← mul_assoc, -Fintype.card_pi]; dsimp +instances [levelPlaces, AuxPair.κ]⟩
  simpa [ne_of_gt, -Fintype.card_pi, H] using (h .one).1

/-- For a pair p, a tame character ϑ of modulus Q and a sign s = ±1, the ratio `Data.Pair.ratio` of
twisted to untwisted L-values at ϑ^s and Q is non-zero and real. -/
lemma ratio_ne_zero_and_real : let r := p.ratio ϑ s; r ≠ 0 ∧ star r =
    r := by simp (disch := simp [funext_iff] <;> grind [p.8 1, Pair]) [ratio,
  ((ϑ.4.zpow s).inv.mul p.hasWeight.inv).L_ne_zero, p.hasWeight.inv.L_ne_zero]

/-- The ratio ρ(ϑ) of the twisted to the untwisted L-value of the pair p = (ν, z) equals
`Data.Pair.intAlgPart` at ϑ divided by its value at the trivial twist. -/
lemma ratio_eq_intAlgPart_div : p.ratio ϑ = intAlgPart H ϑ / intAlgPart H .one :=
  (intAlgPart_eq_mul_L H).elim fun _ ⟨_, h⟩ ↦ by
    simpa [*, ratio] using congr((‖$(h ϑ) / $(h .one)‖ : ℂ)).symm

/-- For a pair p, an index set n fitting p and a tame character ϑ, the normalised value
`Data.Pair.intAlgPart` at ϑ is a non-zero complex number. -/
@[simp] lemma intAlgPart_ne_zero : intAlgPart H ϑ ≠ 0 := by grind [ratio_eq_intAlgPart_div H ϑ,
  ratio_ne_zero_and_real]

/-- For a pair (ν, z) with z ≥ 2 and every tame character ϑ, the form Ξ (`Data.Pair.trivialLift`)
lifted from the definite U(1) to the definite U(2z) with the character νϑ is non-zero. -/
@[simp] lemma trivialLift_ne_zero : trivialLift H ϑ ≠ 0 := by simpa using intAlgPart_ne_zero H ϑ

end Data.Pair

namespace Data

/-- Let the twists θ(ι) satisfy `Data.IsFitFamily`. If y has height at most c ≤ c' (`HeightLe`) and
each non-zero y'(ι) is y(ι) times an integer power of the norm of the modulus of θ(ι), then y' has
height at most c'. -/
lemma IsFitFamily.heightLe_of_eq_zpow_mul {c c' y y' θ} (o : D.IsFitFamily θ) (h :
  HeightLe c y) (hc : c ≤ c') (hy : ∀ ι, y' ι ≠ 0 → ∃ k : ℤ, y' ι = (θ ι).levelNorm ^ k * y ι) :
  HeightLe c' y' := h.mono hc fun ι ↦
  (not_or_of_imp (hy ι)).elim (by aesop) (by simp_all [(o.1 ι).norm_natCast_eq_one, -Nat.cast_prod])

variable (p)

/-- The pair with the same character as p whose point is z clamped to the interval from 1 to the
point of p. -/
def Pair.lowerPoint z :=
  {p with z := 1 ⊔ z ⊓ p.z, z_mem := by grind [Pair], le_c := by grind [Pair, le_c]}

/-- Let Π be `lValueProd`, (ν, z) a pair, ϑ tame of modulus Q, s = ±1. Then Π(z) for (νϑ^s)⁻¹
away from the chosen places and Q is N(Q)^{z²} times Π(z) for ν⁻¹ away from the chosen
places times ∏_{1≤z'≤z} ρ_{z'}², ρ_{z'} the L-value ratio `Data.Pair.ratio`. -/
lemma Pair.lValueProd_eq (s : ℤˣ) (ϑ : D.TameChar) :
  lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) (p.ν * ϑ.toAutChar ^ s.1)⁻¹ p.z = ϑ.levelNorm ^ p.z ^ 2 *
  (lValueProd {w | D.IsChosen w} p.ν⁻¹ p.z * ∏ z ∈ .Icc 1 p.z, (p.lowerPoint z).ratio ϑ s ^ 2) :=
  by rw [lValueProd, lValueProd, finprod_mem_union, finprod_mem_coe_finset, Nat.mul_comm]
     push_cast [mul_pow, mul_assoc, ← prod_mul_distrib]; congr!
     cases (p.lowerPoint ‹_›).ratio_ne_zero_and_real ϑ s
     repeat simp_all [ratio, lowerPoint, field, Set.disjoint_right, IsChosen,
       levelNorm_mem_and_notMem_of_mem_Q _ ϑ, ↓finite_isChosen]

instance (D : Data P) (z) : NeZero (cond z D.b₁ 1) := z.rec .one D.instNeZeroNatB₁
end Data
end
