import Lib.Cohomology.HodgeTatePairs

section
/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: Hodge–Tate map in weight h: definition, naturality, scaling, multiplicativity. -/

open AddCommGrpCat CategoryTheory HodgeTatePair Finset TotalH TensorProduct

attribute [local simp] Functor.curryObj contractionPow H.smul_eq_push H.map H.push comp_assoc
  cup_comp_homClass_left

variable {p k} [Field k] [EmbeddedInQpBar p k] {N N' : AbFunctor (CommAlg k)} {q h} (α :
  N' ⟶ N) (x : HodgeH N q) {n}

/-- For a functor N from k-algebras to abelian groups, the total cohomology of (S,M) ↦
N(B_{S,M}) with coefficients F on the category of pairs; the target of λ_h. -/
abbrev PairH N := TotalH (pairAlg ⋙ N) scalarCoeff

/-- The Hodge–Tate map λ_h: restrict a Hodge class along B_{S,M} → T ⊕ M, apply the h-th power
of the contraction class, and project ⋀M to degree zero. -/
noncomputable def hodgeTateMap (h : ℕ) : HodgeH N q →ₗ[k] PairH N :=
  ⟨⟨((Comparison.restrict toHodgeTest _).pull (Functor.whiskerRight
  toSqZero N) q · |>.toTotalH.comp (contractionPow h)), by simp⟩, by simp [← comp_smul,
  ← act_comp_contractionPow, comp_assoc_of_eq, of_comp_homClass, Comparison.pull]⟩

/-- For α: N' → N, the k-linear pull-back from total Ext(N∘B,F) to total Ext(N'∘B,F), where B is
(S,M) ↦ B_{S,M}. -/
noncomputable def PairH.map : PairH N →ₗ[k] PairH N' :=
  ⟨(pullbackAlong (pairAlg.whiskerLeft α)).toAddHom, comp_smul⟩

/-- The k-linear map from the degree-n cohomology of N(T) on p-adic tests to total Ext(N∘B,F):
restrict along B_{S,M} → T and include as the degree-n summand. -/
noncomputable def restrictToPairs : H (genericOver ⋙ N) genericCoeff n →ₗ[k] PairH N :=
  ⟨⟨Abelian.Ext.toTotalH ∘ (Comparison.restrict toTest _).pull (Functor.whiskerRight toGeneric N)
  n, by simp⟩, by simp [smul_eq_comp, of_comp_homClass, Comparison.pull]; bound⟩

lemma restrictToPairs_map x : restrictToPairs (.map _ (genericOver.whiskerLeft α) n x) = .map α
  (restrictToPairs x) := by simpa using! (Comparison.pull_comp_restrictAlong (.mk₀ α) ..).symm

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- The Hodge–Tate map λ_h is natural: for α: N' → N and a Hodge class x on N, λ_h(α^* x) = α^*
λ_h(x). -/
lemma hodgeTateMap_map : hodgeTateMap h (.map α x) = .map α (hodgeTateMap h x) := by
  simpa using! (comp_assoc_of_eq (Comparison.pull_comp_restrictAlong (.mk₀ α) ..) _).symm

/-- For t in k and a Hodge class x of any degree, the Hodge–Tate map in weight h satisfies
λ_h(s_t x) = t^h λ_h(x), where s_t is the scaling induced by (a, m) ↦ (a, tm). -/
lemma hodgeTateMap_scale t (x : HodgeH N q) : hodgeTateMap h (.scale t x) =
  t ^ h • hodgeTateMap h x := by
  erw [← comp_smul, ← scaleModule_comp_contractionPow, ← (x.mapExactFunctor_restrictAlong_id ▸
    mapExactFunctor_naturality ((Functor.whiskeringLeft ..).map _) x :)]
  simp [hodgeTateMap, comp_assoc_of_eq, of_comp_homClass, Comparison.pull]; rfl

variable {a b} [HasFlatValues N] {M L : AbFunctor HodgeTatePair} [HasFlatValues M] (x :
  HodgeH N a) (y : HodgeH N' b) (e : b + a = n)

/-- For y in total Ext(L,F), the k-linear map x ↦ x × y from total Ext(M,F) to total Ext(M ⊗
L,F): external product followed by multiplication in F. -/
noncomputable def HodgeTatePair.cross (y : TotalH L scalarCoeff) :
  TotalH M scalarCoeff →ₗ[k] TotalH (abTensor M L) scalarCoeff := ⟨⟨(·.cup y |>.comp (.homClass
  (toTest.whiskerLeft (PadicTest.genericAlg ⋙ forget₂ ..).mulPairing))), by simp [TotalH.cup]⟩,
  by simp [smul_eq_comp]; intros; repeat erw [← homClass_comp]
     congr 2; exact abTensor_hom_ext fun _ _ _ ↦ congrArg _ (smul_mul_assoc ..)⟩

set_option backward.isDefEq.respectTransparency false

/-- Binomial rule: for x in Ext^a(M,Λ) and y in total Ext(L,Λ), the wedge product x × y followed
by u_l = `contractionPow` l equals ∑_{h ≤ l} C(l,h)(−1)^{(a+h)(l−h)} (x·u_h) × (y·u_{l−h}). -/
lemma HodgeTatePair.contractionPow_cup l (x : H M _ a) (y : TotalH L _) :
  comp (.cup x.toTotalH y) (pullbackAlong wedgePairing (contractionPow l)) = ∑ h ∈ range (l +
  1), l.choose h • (-1 : k) ^ ((a + h) * (l - h)) • cross (comp y (contractionPow (l - h)))
  (comp x.toTotalH (contractionPow h)) := by
  induction l generalizing a y
  simp [cross, cup_comp_homClass_right, ← homClass_comp]
  congr 2; exact abTensor_hom_ext fun X _ _ ↦
    congrArg _ ((@ExteriorAlgebra.algebraMapInv X.GenericRing ..).map_mul ..)
  let E : Cocycle (abTensor formCoeff formCoeff) (piAbFunctor fun _ ↦ abTensor formCoeff
    formCoeff) := ⟨fun f ↦ ofHom (.pi (cond · (abTensorMap (contractionCocycle.component f)
    (formCoeff.map f)) (abTensorMap (formCoeff.map f) (contractionCocycle.component f)) |>.hom)),
    fun _ _ ↦ addCommGrp_tensor_hom_ext (by simp [funext_iff, contractionCocycle.cocycle_comp,
    add_tmul, tmul_add, piAbFunctor, abTensor])⟩
  have h b : (comp (.cup x.toTotalH y) E.cohomClass).comp (.homClass (piAbFunctor.π _ b)) =
    cond b (.cup (x.toTotalH.comp contractionCocycle.cohomClass) y)
    ((-1) ^ a • .cup x.toTotalH (y.comp contractionCocycle.cohomClass)) := by
    simp_rw [TotalH.cup, TotalH.map_comp, comp_assoc]
    erw [← map_zsmul, map_extClass contractionCocycle.shortExact_extension,
      map_extClass contractionCocycle.shortExact_extension,
      ← extClass_sign_comm (abTensor_shortExact contractionCocycle.shortExact_extension)]
    cases b <;> refine congrArg (_ ∘ _) (.trans (E.cohomClass_comp_eq_extClass (S := ⟨_, _, _⟩) _ _
      _ (fun _ ↦ by apply abTensorMap <;> first | apply 𝟙 | exact ofHom (.inr _ (formCoeff _))) ?_
      ?_) id_comp) <;> intros <;> apply addCommGrp_tensor_hom_ext <;> simp [Cocycle.extension,
      abTensor, piAbFunctor, E, piAbFunctor.π, ← add_tmul, ← tmul_add]
  rw [sum_choose_succ_nsmul fun _ _ ↦ _, contractionPow, ← TotalH.comp_assoc_of_sq
    (E.cohomClass_naturality _ _ ((piAbFunctor.π _ false ≫ abTensor.map (toHodgeTest.whiskerLeft
    (HodgeTest.scaleModule ..)) _ + piAbFunctor.π _ true) ≫ wedgePairing) fun _ _ _ ↦
    addCommGrp_tensor_hom_ext (congrArg _ <| contraction_mul _ (neg_one_smul k) ·.1 ·.1))]
  simp [TotalH.homClass, Abelian.Ext.mk₀_add, homClass_comp, ← comp_assoc, h,
    ← cup_comp_homClass_left]
  simp [comp_of, *, smul_sum]
  congr! 2 <;> simp_all [← comp_of, scaleModule_comp_contractionPow, comp_smul,
    Nat.succ_sub] <;> module

/-- Product formula: for Hodge classes x of degree a and y, λ_l(x × y) = ∑_{h ≤ l}
C(l,h)(−1)^{(a+h)(l−h)} λ_h(x) × λ_{l−h}(y).

Known result: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. -/
lemma hodgeTateMap_cup l : hodgeTateMap l (N := abTensor N N') (_root_.cup exteriorAlg.mulPairing x
  y e) = ∑ h ∈ range (l + 1), (l.choose h • (-1 : k) ^ ((a + h) * (l - h)) • cross
  (hodgeTateMap (l - h) y)) (hodgeTateMap h x) := (comp_assoc_of_eq ((cup_of ..).trans
  (congrArg _ (Comparison.pull_cup (by simp) ..).symm)) _).symm.trans (contractionPow_cup ..)
end

section
/-! Part of: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology (known result; see
Lib.PadicComparison.HodgeTate.HodgeTateVectors).

This file: For smooth spaces, forgetting first-order lifts of points preserves cohomology. Galois
twist of p-adic tests scales μ by the cyclotomic character, preserves contraction class. -/

noncomputable section

open CategoryTheory Function TrivSqZeroExt Pi thickeningOver EtaleChart HodgeTatePair TotalH
  Comparison DirectSum Ideal
variable {p k} [Field k] [EmbeddedInQpBar p k]

/-- Restriction along B_{S,M} → T, from the cohomology of N(T) on p-adic tests S to that of
N(B_{S,M}) on pairs (S,M), is bijective in all degrees. -/
def PairRestrictBijective N := (Comparison.restrict toTest genericCoeff).IsBijective (N :=
  genericOver ⋙ N) (Functor.whiskerRight toGeneric N)

lemma PairRestrictBijective.injective_restrictToPairs {N n} (H : PairRestrictBijective N) :
  Injective (@restrictToPairs p k _ _ N n) := (of_injective _).comp (H n).1

/-- If restriction along B_{S,M} → T = S[1/p] is bijective on the cohomology of N
(`PairRestrictBijective`), then for x ∈ Hdg^q(N) the class λ_h(x) is the restriction
(`restrictToPairs`) of a class of degree q + h on p-adic tests. -/
lemma PairRestrictBijective.exists_hodgeTateMap_eq {N q} (H : PairRestrictBijective N) h (x :
  HodgeH N q) : ∃ ξ, hodgeTateMap h x = restrictToPairs (n := q + h) ξ := (h.rec ⟨_, rfl⟩ fun _ ⟨_,
  e⟩ ↦ ⟨_, by erw [contractionPow, e, comp_of]; omega⟩ : ∃ y, contractionPow h = .of _ h y).elim
  fun _ _ ↦ ((H _).2 _).imp (by aesop (add simp [hodgeTateMap, restrictToPairs, comp_of]))

lemma HodgeTatePair.existsUnique_hom (A D : HodgeTatePair) f (v : _ → _) : ∃! g : A ⟶ D,
  (∀ i, g.2 (single i 1) = v i) ∧ g.1 = f := ⟨⟨f, semilinearOfBasis _ v⟩, by simp,
  fun ⟨_, _⟩ ⟨_, rfl⟩ ↦ congrArg _ ((basisFun ..).ext (by simpa))⟩

lemma HodgeTatePair.isSquareZero_toGeneric A : IsSquareZero (toGeneric A) :=
  ⟨((exact_mulMu_proj ..).1 · |>.elim (⟨⟨⟨·, _, 0⟩, ·⟩, rfl⟩)), by
  rw [pow_two, eq_bot_iff, mul_le]; rintro ⟨⟨_, ⟨⟩⟩, h⟩ ⟨⟩ ⟨⟨_, ⟨⟩⟩, g⟩ ⟨⟩
  exact Subtype.ext
    (ext ((pow_two _).ge.trans A.test.ker_thickeningProj_sq.le (mul_mem_mul h g)) (inr_mul_inr ..))⟩

/-- For a field k mapping to Q̄_p, if every field-valued point of X lies in a chart with étale
coordinates, then ℤ[X] satisfies `PairRestrictBijective`. -/
lemma IsChartCovered.pairRestrictBijective {n X} [h : IsChartCovered n X] : PairRestrictBijective
  (freeAb X) := have a := hasPartitions_periodAlg _ exists_periodAlg_iso_genericAlg.choose
  have d := isLocallyEverything_of_open_cover (Θ := 𝟭 _)
    (h.1 · · · |>.elim (⟨_, ·.isOpenSub, ·, le_iSup locus _⟩))
  ((Comparison.of ..).isBijective_congr (p :=
    ((iSup locus).whisker genericOver).ι) (((iSup locus).whisker _).fromPreimage_ι
  (Functor.whiskerRight toGeneric X)).symm (hasZariskiDescent_genericOver (𝟭 _) a (d.whisker
    _)).isCohomEquiv ((hasZariskiDescent_genericOver _ ⟨fun A ↦ (a.1 _ · · · |>.elim fun d ⟨f, a, b,
    c⟩ ↦ ⟨_, (A.existsUnique_hom ⟨d, _⟩ f (0, single · 1)).exists.imp fun | l, ⟨_, rfl⟩ => ⟨a, fun D
    u hu ↦ (b _ _ hu).elim fun g _ _ ↦ (existsUnique_hom ⟨d, _⟩ _ g (u.2 <| single · 1)).imp fun _ ↦
    .imp (fun _ ↦ (existsUnique_hom ..).unique (by simpa [*]) ⟨fun _ ↦ rfl, rfl⟩) (by aesop), c⟩⟩),
    fun _ _ ↦ a.2 _ _⟩ (d.whisker _)).preimage _).isCohomEquiv).2 (HasUnivPoints.isBijective (by
have m := @X.map_comp_apply
rintro c ⟨_, _, ⟨_, ⟨a, ⟨⟩⟩, ⟨⟩⟩, ⟨ζ⟩, ⟨⟩⟩
obtain ⟨s, ⟨⟨⟩, hx⟩, -⟩ := etale_polyEval_iff.1 a.etale _ (isSquareZero_toGeneric ⟨c, _⟩) ζ
  (⟨⟨_, _, single · 1⟩, ((exact_mulMu_proj ..).1 _).choose_spec⟩) (by tauto)
refine ⟨_, ⟨_, le_iSup locus a _ ⟨_, m s ..⟩⟩, 𝟙 c, by simp; exact Subtype.ext (m ..).symm,
  fun D ⟨x, _⟩ f h ↦ ?_, by simpa using! bijective_id⟩
have h := (m ..).trans congr($h.symm.1)
obtain ⟨⟨ψ : _ ⟶ _⟩, ⟨⟩⟩ := a.isOpenSub.mem_of_isSquareZero _ D.isSquareZero_toGeneric x ⟨_, h⟩
have h := a.eq_comp_of_map_point_eq _ h
choose t e using fun r ↦ ((exact_mulMu_proj ..).2.2 ((ψ r).1.1 - _)).1 (by
  erw [map_sub, proj.naturality_apply, (s r).2, (ψ _).2, congr($h r), sub_self])
refine (existsUnique_congr fun g ↦ ?_).1
  (existsUnique_hom _ _ f (Function.prod t (ψ · |>.1.2.2) ∘ a.coordinate))
erw [and_congr_left_iff, Subtype.ext_iff, ← (m ..).congr_left, (a.injective _).eq_iff]
refine fun | rfl => .trans (forall_congr' fun i ↦ ?_) ⟨a.lift_unique D.isSquareZero_toGeneric
  h, by bound⟩
erw [Prod.ext_iff, ← (exact_mulMu_proj ..).2.1.eq_iff, e, eq_sub_iff_add_eq', Subtype.ext_iff,
  Prod.ext_iff, Prod.ext_iff, and_iff_right congr($h _), AlgHom.comp_apply, hx]; rfl))

open PadicTest MulSemiringAction AddCommGrpCat

seal exteriorMap contraction

lemma PadicTest.structMap_twist {p} [ThePrime p] (g : Gp p) c z : (twist g c).structMap z =
  c.structMap (g • z) := congr($(IsLocalization.ringHom_ext (k := .comp _ (toRingHom ..))
  (.powers (p : OC)) (by ext; exact structMap_coe .. ▸ (c.structMap_coe _).symm)) z)

variable (g : Gp p) (c : PadicTest)

lemma thickeningOver.mulMu_twist (t : c.GenericRing) : mulMu c t = mulMu (.twist g c)
    (c.structMap (algebraMap _ (PadicAlgCl p) (cyclotomicGp g⁻¹).1) * t) := by
  obtain ⟨⟨x, rfl⟩, a, h⟩ := c.thetaGeneric_spec.1 t, Lift.mu_sq_dvd_smul_mu_sub g⁻¹
  have e a : algebraMap Ainf c.Thickening (g • a) = algebraMap _ (c.twist g).Thickening a := congr(
    algebraMap (WittVector p c.TiltRing)
    _ $(by ext; exact (congrArg _ (pow_one _)).trans (tiltMap_comp
    ..).symm)); rw [mulMu_thickeningProj, inv_smul_eq_iff.1 (eq_add_of_sub_eq' h), e]
  erw [← c.uniqueLift.1.1.2, mulMu_proj_mul, mulMu_thickeningProj, AlgHom.commutes]
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [(ker_thickeningProj_sq _).le (Ideal.pow_mem_pow (thetaGeneric_mu _) 2)]; simp; apply mul_assoc

/-- For g in G_p, the morphism from `genericCoeff` composed with the twist of structure maps by
g to `genericCoeff` that is the identity on each R[1/p]. -/
def twistGenericCoeff {p} [ThePrime p] (g : Gp p) :
  PadicTest.twist g ⋙ genericCoeff ⟶ genericCoeff := .mk (ofHom <| .id <| ULift ·.GenericRing)

/-- For g in the Galois group of Q̄_p/ℚ_p, the endofunctor of `HodgeTatePair` twisting the
structure map of the underlying test by g and keeping all other data. -/
def HodgeTatePair.galTwist : HodgeTatePair ⥤ HodgeTatePair := .mk (⟨_, ·.rank⟩) fun f ↦
  ⟨(PadicTest.twist g).map f.1, f.2⟩

/-- The identity of ⋀_T(T^n), T = S[1/p], at each pair (S, n), as a natural map from Λ =
`HodgeTatePair.formCoeff` to Λ precomposed with the twist by g. -/
def HodgeTatePair.twistForms : formCoeff ⟶ galTwist g ⋙ formCoeff := .mk fun X ↦
  ofHom (.id (ULift (ExteriorAlgebra X.test.GenericRing (_ → X.test.GenericRing))))

lemma HodgeTatePair.contractionPow_galTwist h :
  pullbackAlong (twistForms g) (TotalH.comp (.map (restrictAlong (galTwist g)) (contractionPow h))
  (.homClass (toTest.whiskerLeft (twistGenericCoeff g)))) = contractionPow h := by
  induction' h with _ H; erw [map_homClass, homClass_comp_homClass_comp, ← homClass_comp]; rfl
  rw [contractionPow, map_comp_assoc, Cocycle.map_cohomClass_restrict,
    ← comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), H]
  tauto
end
end
