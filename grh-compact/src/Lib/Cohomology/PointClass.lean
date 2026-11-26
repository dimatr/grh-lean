import Lib.Cohomology.ChartedSchemes
import Lib.Cohomology.Contraction
import Lib.Cohomology.LocusEquations

section
/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Local cohomology vanishes below the depth; Zariski descent for Hodge tests. -/

open Localization CategoryTheory Fin Function Ideal IsLocalizedModule LinearMap MvPolynomial RingHom
  ConcreteCategory CategoryTheory.Functor IsLocalization.Away RingTheory.Sequence

variable {k ι : Type} [CommRing k] {c : HodgeTest k} {n} [Fintype ι] {f : ι → c.baseAlg} {d}

/-- For a pair c = (A,M) and a family (f_i) in A, the subfunctor of h_c of morphisms whose ring
map sends some f_i to a unit. -/
def someUnitLocus (f : ι → c.baseAlg) : Subfunctor (reprBy c) :=
    ⟨fun _ ↦ {y | ∃ i, IsUnit (y.1.1 (f i))}, fun a _ ↦ .imp fun _ ↦ .map a.1.1⟩

/-- Depth vanishing (Rees, Grothendieck): suppose each H^n(M) is I-power torsion elementwise,
and each M-regular r is regular on H^n(M) once H^m(M/rM) = 0 for m < n. Then H^n(M) = 0 if I
contains a weakly M-regular sequence longer than n. -/
lemma depth_vanishing (H : ℕ → _ → ModuleCat k) {I l} (hI : ∀ n M x, I ≤
    (torsionOf k (H n M) x).radical) (hδ : ∀ n (M : ModuleCat k) (r : k), IsSMulRegular M r → (∀ m <
    n, Subsingleton (H m (.of k (QuotSMulTop r M)))) → IsSMulRegular (H n M) r) (hl : ofList l ≤ I)
    (hn : n < l.length) (M : ModuleCat k) (h : IsWeaklyRegular M l) : Subsingleton (H n M) := by
  induction l generalizing M n <;> simp at *
  exact subsingleton_of_forall_eq 0 (hI _ _ · hl.1 |>.elim ((hδ _ _ _ h.1 (by bound)).pow ·
    |>.right_eq_zero_of_smul))

seal exteriorMap in
/-- For a pair c = (A,M) and finitely many f_i in A whose ideal contains a weakly A-regular
sequence l, the cohomology with coefficients ⋀M of h_c relative to the locus where some f_i
is a unit vanishes below the length of l. -/
lemma DepthVanishing.subsingleton_of_isWeaklyRegular l (hl : ofList l ≤ span (.range f)) (hn :
  n < l.length) (h : IsWeaklyRegular c.baseAlg l) :
  Subsingleton (H (relFreeAb (someUnitLocus f)) hodgeCoeff n) := by
  let L {C} [Category C] (φ : C ⥤ _) x s : C ⥤ Comma (𝟭 _) (coyoneda ⟨c⟩) :=
    .mk (⟨x ⟶ ·, _, ↾(s ≫ φ.map ·)⟩) fun a ↦ .mk (↾(· ≫ a)) (φ.map a)
  let ψ := L (𝟭 _) c (𝟙 _); let P := ObjectProperty.ι fun B : CommAlg c.baseAlg ↦
    Module.Flat c.baseAlg B
  let U g : Subfunctor (Comma.fst (𝟭 _) (coyoneda ⟨c⟩) ⋙ uliftFunctor) := ⟨fun X ↦ {t |
    IsUnit ((X.3 t.1).1 g)}, fun a _ ↦ congr(IsUnit (($a.w _).1 g)).mpr ∘ .map a.2.1.1⟩
  have bij B (b : P B) := (@pointMap_bijective_of_existsUnique _ _ B ⟨_, B.2.trans ..⟩) ⟨fun _ ↦
    {x | IsUnit (x.1.1 b)}, fun a _ ↦ .map a.1.1⟩ ⟨⟨⟨B.1.toAway b⟩⟩, algebraMap_isUnit _⟩ fun _ _
    h ↦ ⟨⟨ofHom (liftAlgHom _ h)⟩, by aesop (add simp Algebra.algHom)⟩; let W := ⨆ i, U (f i)
  have ind {Q} (hP : IsClosedClass Q) (h : ∀ g, Q (freeAb (U g).toFunctor)) :=
    (hP.2 _ (relFreeAb.shortExact W).2 (hP.freeAb_iSup
    (.range U) (by simpa [h] using (⟨· * ·, by ext; simp [U]⟩)) (by simp))).1
    ((hP.iff_of_isIso (freeAb.map (Subfunctor.ι ⊤))).1 (by simpa [U] using! h 1))
  let γ : Comparison hodgeCoeff (piAbFunctor fun _ ↦ moduleCoeff (asModules P ⋙ tensorWith c.baseAlg
    _)) := ⟨P ⋙ restrictAlg k _ ⋙ HodgeTest.withIndex c.Index, fun B ↦ (AddEquiv.ulift.trans
    ((Pi.basisFun B.1 c.Index).ExteriorAlgebra.equivFun.toAddEquiv.trans (.piCongrRight fun _ ↦
    .symm (.trans .ulift (TensorProduct.lid ..).toAddEquiv)))).toAddCommGrpIso.hom,
    fun B D a ↦ by ext; congrm (⟨1 ⊗ₜ $(HodgeTest.repr_withIndex_map a.1 _ ·)⟩)⟩
  let ψ' := L γ.φ ⟨.of .., .self⟩ ⟨ofHom ⟨.id _, by tauto⟩, .id⟩
  let η : ψ' ⟶ γ.φ ⋙ ψ := .mk fun B ↦ .mk (ψ' B).3 (𝟙 _)
  refine (by ext; simp [W, Subfunctor.whisker]; rfl : W.whisker ψ = someUnitLocus f) ▸ have :=
      (depth_vanishing (fun n M ↦ .of _ (H (ψ' ⋙ relFreeAb W) (moduleCoeff (asModules P ⋙ tensorWith
      _ M)) n)) (fun n M _ ↦ span_le.2 (fun | _, ⟨i, rfl⟩ => exists_exists_eq_and.1 (mem_ker_iff
      (.powers _) (g := TensorProduct.mk _ (Away (f i)) _ 1).1 ((ind (FP.isClosedClass.comap
      (restrictAlong ψ')) (bij ⟨.of .., _⟩ · |> FP.isClosedClass.of_bijective _ <|
      hasFlatBaseChange_reprFunctor _) _ c.baseAlg ..).1 (((relFreeAb.isCohomEquiv_iff_subsingleton
      (W.whisker _)).1 (IsCohomDense.isCohomEquiv (.mono (U := (U _).whisker ψ') ?_ fun _ ↦ le_iSup
      (U ∘ f) i _)) n).1 ..))))) (fun _ M r h i _ _ ↦ eq_of_tensorPush_eq (exact_lsmul_mkQ_smul_top
      M r) Quot.exists_rep (·.2.rTensor_preserves_injective_linearMap _ h) i) hl hn (.of ..) h)
    ((H.pi_bijective ..).comp (ind (γ.isClosedClass η) (fun g ↦ ((γ.isBijective_congr (pointMap_comp
      _ (whiskerRight η (U g).toFunctor)) (.of_bijective (pointMap_bijective_of_existsUnique
      ((U g).whisker ψ) _ (HodgeTest.existsUnique_lift_away _ g isLocalization.1)))
      (.of_bijective (bij ⟨.of .., .self⟩ g))).2 (γ.isBijective_of_repr (u :=
      pointMap ⟨𝟙 _⟩) ⟨𝟙 _⟩ (pointMap_id_bijective_of_fullyFaithful (𝟭 _) _) (.comp
      (AddEquiv.bijective _) (bijective_of_isIso (hodgeCoeff.map (_ ≫ _))))) :)) n)).1.subsingleton
  rintro B ⟨⟨y⟩⟩; cases show y = structureMap by ext
  exact (Comparison.isBijective_of_repr _ (bij B _) (ULift.map_bijective.2 (congr(Bijective $(show _
    = lTensor .. by ext; simp [TensorProduct.smul_tmul']; rfl)).mp (isBaseChange (.powers (f i)) _
    ((TensorProduct.assoc ..).1 ∘ₗ TensorProduct.map (TensorProduct.mk c.baseAlg _ _ 1)
    (IsScalarTower.toAlgHom _ B.1 (Away (algebraMap _ _ (f i)))).toLinearMap))))).eqv

lemma isCohomEquiv_someUnitLocus (h : span (.range f) = ⊤) : IsCohomEquiv hodgeCoeff
  (freeAb.map (someUnitLocus f).ι) := (relFreeAb.isCohomEquiv_iff_subsingleton _).2 fun n ↦
  DepthVanishing.subsingleton_of_isWeaklyRegular
  (.replicate n.succ 1) (by aesop) (by simp) ⟨by simp⟩

/-- For a pair c = (R, M) over k and étale coordinates x_1, …, x_{2d} on R, the cohomology of
h_c with coefficients ⋀M and supports in the common zeros of the x_i − x_{d+i} vanishes in
degrees below d. -/
lemma hodge_vanishing_along_diagonal {x : _ → c.baseAlg} (hx : (polyEval x).Etale) (hn : n < d) :
  Subsingleton (H (relFreeAb (someUnitLocus (x ∘ castAdd d - x ∘ natAdd d))) hodgeCoeff n) :=
  DepthVanishing.subsingleton_of_isWeaklyRegular _ (by simp [ofList, Set.range, algebraMap])
  (by simpa) (@.of_flat _ _ _ _ (_) (Flat.comp (.of_bijective (f := (bind₁ (append (X ∘ castAdd d
  - X ∘ natAdd d) (-X ∘ natAdd d))).1) (Involutive.bijective (by apply ·.induction_on <;> simp_all
  [forall_fin_add, -natAdd_eq_addNat]))) (Etale.iff_flat_and_formallyUnramified.1 hx).1)
  (.ofFn (X ∘ castAdd d)) ⟨fun i _ ↦ (isSMulRegular_quotient_iff_mem_of_smul_mem ..).2 fun p h ↦ by
  rw [smul_eq_mul, mul_top, ofList, show {r | r ∈ _} = X '' castAdd d '' {j | j < i} by
    grind [List.mem_take_iff_getElem], mem_ideal_span_X_image] at *
  exact fun m _ ↦ (h (.single ⟨i, by grind⟩ 1 + m) (by simp_all)).imp (by simp; grind)⟩)

/-- Open covers are dense for Hodge cohomology: the coefficients (A,M) ↦ ⋀_A M satisfy Zariski
descent `HasZariskiDescent` for the rings A ⊕ M. -/
lemma hasZariskiDescent_hodgeCoeff : HasZariskiDescent (@HodgeTest.sqZeroExt k _ ⋙ forget₂ _ _)
  hodgeCoeff := fun Y U h X y ↦ ((span_eq_top_iff_finite _).1
  (ne_top_iff_exists_maximal.not_right.2 fun ⟨m, l, e⟩ ↦ (h X y m l).elim fun _ a ↦ a.1
  (e (subset_span a.2)))).elim fun s ⟨l, e⟩ ↦ (IsCohomDense.mono (U := someUnitLocus fun i : s ↦
  X.baseProj _) (fun _ g ↦ isCohomEquiv_someUnitLocus (by erw
  [← Set.image_eq_range (X.baseProj ≫ _), ← Ideal.map_span, e, Ideal.map_top])) fun _ _ ⟨i, u⟩ ↦
  l i.2 _ _ (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 u)).isCohomEquiv
end

section
/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Künneth formula in Hodge cohomology, surjectivity of the cross product. -/

open Algebra.TensorProduct AddSubmonoid CategoryTheory Comparison CommAlgCat IsCohomEquiv Finset
  Finsupp TotalH TensorProduct CartesianMonoidalCategory MonoidalCategory Module.Basis Abelian.Ext

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- Künneth: over a field k of characteristic 0, if X has an atlas of dimension d, every class
in Hdg^n(X × X) is a finite sum of cross products x × y of Hodge classes on X. -/
lemma kunneth {k} [Field k] [CharZero k] {X d n} [hX : HasAtlas d X] (z : HodgeH _ n) :
    z ∈ AddSubmonoid.closure {z | ∃ a b e,
  ∃ (x : HodgeH (freeAb.obj X) a) (y : HodgeH (freeAb.obj X) b), z = .map (freeAb.prod X X)
  (_root_.cup (@exteriorAlg k _).mulPairing x y e :)} := hX.exists_isCharting.elim fun V ⟨h, t⟩ ↦ by
  have hU := hasZariskiDescent_hodgeCoeff (h.whisker _)
  have u {P} (hP : IsClosedClass P) (h : ∀ c, P (freeAb _)) : P (freeAb (V.whisker _).toFunctor) :=
    t _ (hP.comap (restrictAlong _)) fun b _ ↦
    hP.of_bijective _ b.exists_univPoint.choose_spec.2 (h _)
  refine (mem_map_iff_mem (((hU.preimage (fst ..)).inf (hU.preimage (snd ..))).isCohomEquiv n).1).1
    ((DirectSum.of_eq_same ..).subst ((((of_isIso (freeAb.map (NatIso.ofComponents fun _ ↦
    (Equiv.Set.prod ..).toIso).1 ≫ freeAb.prod (V.whisker _).toFunctor _)).bijective_totalH.comp
    (u (isClosedClass_lerayHirsch (Φ := abTensor _) (θ := fun i : Σ n,
    ofVectorSpaceIndex k (H _ _ n) ↦ H.push _ exteriorAlg.mulPairing _ (i.2.1.mapExactFunctor
    (abTensor.flip _)))) fun c ↦ ?_)).2.forall (p := (· n ∈ _))).2 (·.induction_linear (by simp)
    (by simp_all [add_mem]) fun ⟨a, x, _⟩ y ↦ ((hU.isCohomEquiv _).2 x).elim fun _ e ↦ ?_) _))
  -- U × c: the basis of H(U) is exchanged for a basis b of the forms on c
  let b := (ofVectorSpace k _).smulTower c.formBasis
  refine (bijective_iff_of_comm_sq (·.induction_linear (by simp [↓map_zero])
    (by simp_all [↓map_add]) fun _ r ↦ ?_) (curryAddEquiv.trans
    (mapRange.addEquiv (b.repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv
    hodgeCoeff _))))).bijective (u (isClosedClass_lerayHirsch (Φ := abTensor.flip _) (θ := fun j ↦
    mk₀ ((abTensor _).map ((homReprEquiv c hodgeCoeff).symm ⟨b j⟩) ≫ exteriorAlg.mulPairing)))
    fun c' ↦ ?_)).1 (Finsupp.domLCongr (.prodComm ..) ≪≫ₗ curryLinearEquiv k ≪≫ₗ
    mapRange.linearEquiv (DFinsupp.basis fun _ ↦ ofVectorSpace ..).repr.symm).bijective
  simp [DFinsupp.basis]
  conv_rhs => rw [lerayHirsch_single, TotalH.smul_eq_comp, map_comp_assoc, map_homClass,
    ← homClass_comp]
  conv_lhs => erw [lerayHirsch_single, map_homClass, (mk₀_bijective ..).1 ((push_homReprEquiv_symm
    (CoeffAction.act r).asHom ..).symm.trans (mk₀_comp_mk₀ ..)), toTotalH, ← of_comp_homClass,
    ← map_of, ← TotalH.comp_assoc_of_sq (naturality (abTensor.flip.map _) _), ← homClass_comp]
  congr 2
  exact abTensor_hom_ext fun _ _ _ ↦
    congrArg _ ((mul_smul_comm r ..).trans (smul_mul_assoc ..).symm)
  -- c' × c: the product is affine, and its forms are the tensor product
  let z : (reprBy c' ⊗ reprBy c) ⟨c'.baseAlg ⊗ c.baseAlg, _ ⊕ₗ _⟩ :=
    (⟨ofHom includeLeft, semilinearOfBasis _
    ((Pi.single · 1) ∘ .inl)⟩, ⟨ofHom includeRight, semilinearOfBasis _ ((Pi.single · 1) ∘ .inr)⟩)
  let s {c I} g (ε : I → ℤˣ) := ((HodgeTest.formBasis.reindex g).groupSMul
    ε).repr.symm.toAddEquiv.trans (.trans (.symm .ulift) (sectionEquiv (@hodgeCoeff k _) c))
  refine' ((of_isIso (freeAb.map (isoOfAppBijective (pointMap z) fun B ↦ .of_existsUnique _
    fun ⟨⟨f⟩, ⟨g⟩⟩ ↦ (existsUnique_tensor_desc f.1 g.1).elim fun _ ⟨a, b⟩ _ ↦ by
    refine' ⟨⟨_, semilinearOfBasis _ (Sum.rec _ _)⟩, congr((⟨$(HodgeTest.hom_ext a _)⟩,
      ⟨$(HodgeTest.hom_ext b _)⟩)), _⟩ <;> try exact fun _ ↦
      (congrArg _ (semilinearOfBasis_single ..)).trans (semilinearOfBasis_single ..)
    rintro _ ⟨⟩; exact congr(⟨$(HodgeTest.hom_ext (by tauto)
      (by rintro ⟨⟩ <;> exact .symm ((semilinearOfBasis_single ..).trans (congrArg _
      (semilinearOfBasis_single ..)))))⟩)).1 ≫ freeAb.prod ..)).bijective_totalH.of_comp_iff' _).1
    ((bijective_iff_of_comm_sq (curryAddEquiv.surjective.forall.2 (·.induction_linear
    (by simp [↓map_zero]) (by simp_all [↓map_add, -mapRange.addEquiv_apply]) fun ⟨⟨_, _⟩, _⟩ _ ↦ _))
    (mapRange.addEquiv (s 1 1)).bijective (s sumEquiv.1 (Function.uncurry _)).bijective).1
    ((equivFinsuppOfBasisRight b).symm ≪≫ₗ (c.formBasis.repr.restrictScalars _).lTensor _ ≪≫ₗ
    finsuppTensorFinsupp ..).bijective)
  swap; simp [s, b, lerayHirsch_single, groupSMul]
  conv_lhs => erw [map_homClass, homClass_comp_homClass_comp, ← homClass_comp]
  refine congrArg _ ((Equiv.eq_symm_apply _).2 (congr(exteriorAlg.mulPairing _ ($(add_zero _) ⊗ₜ
    $(add_zero _))).trans (congrArg _ (?_ : exteriorMap z.1.1.2 _ * exteriorMap z.2.1.2 _ = _))))
  erw [exteriorMap_smul, exteriorMap_smul, smul_mul_smul, exteriorMap_formBasis _ (.sumLexInl ..)
    (semilinearOfBasis_single _ _), exteriorMap_formBasis _ (.sumLexInr ..)
    (semilinearOfBasis_single _ _), ExteriorAlgebra.basis_mul_of_disjoint (I := Lex _)
    _ ⟨_, rfl⟩ ⟨_, rfl⟩ (disjoint_map_inl_map_inr ..)]; simp [z]; rfl
  -- U × U: every class is a sum of products of classes that extend to X
  apply y.induction_on .. <;> simp_all [add_mem, lerayHirsch_single, comp_of, DirectSum.of_apply,
    dite_mem, (hU.isCohomEquiv _).2.forall]
  exact fun | _, _, rfl => e ▸ ⟨_, subset_closure ⟨a, by tauto⟩, (H.map_comp ..).symm.trans
    ((cup_map (h := freeAb.hom_ext) ..).trans (congrArg _ (comp_assoc_of_third_deg_zero ..)))⟩
end

section
/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles (known
result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Grothendieck symbols [dT/T]: definition, transformation law, multiplicativity, degree-one
form. -/

noncomputable section


open CategoryTheory Function MonoidalCategory TensorProduct Finset Abelian Ext RingHom TrivSqZeroExt
  Matrix exteriorPower Set Ideal Fin ULift witnessed HodgeTest Comparison H TotalH freeAb
set_option backward.isDefEq.respectTransparency false
variable {k} [Field k] {d V} (f : V ⟶ sqZeroExt ⋙ affineSpace k d)

/-- For f from V to d-tuples in A ⊕ M, the subfunctor of pairs (v, l), l ∈ A^d, with l · f̄(v) =
1, where f̄ is the A-component of f. -/
def jouanolouRel : Subfunctor (V ⊗ .mk (·.baseAlg) (·.1) ⋙ affineSpace k d) :=
  ⟨fun c ↦ {(v, l) | l.1 ⬝ᵥ fst ∘ (f.app c v).1 = 1}, fun φ _ h ↦ congr(_ ⬝ᵥ
  _ ∘ $(f.naturality_apply ..).1).trans (by simpa [dotProduct] using! congr(φ.1 $h))⟩

lemma exists_jouanolouRel_of_unimodular c v (h : v ∈ ((@unimodular k _ d).whisker _).obj c) : ∃ l,
  (v, l) ∈ (jouanolouRel (𝟙 _)).obj c :=
  «exists».2 (mem_span_range_iff_exists_fun.1 ((unimodular.map c.baseProj h).ge ⟨⟩))

variable {R} (ω : freeAb.obj V ⟶ hodgeCoeff) (h : R ≤ jouanolouRel f) {c : HodgeTest k}

instance : Module c.baseAlg (hodgeCoeff.obj c) := module' (M := ExteriorAlgebra ..)

/-- The map (v, l_1, …, l_d) ↦ det(l_1, …, l_d)·ω(v) from the free abelian group on points v
with d witnesses l_i ∈ A^d to ⋀_A M. -/
@[simp] def detCochain := desc (Y := witnessed R d) (fun c t ↦ det (t.1.2 · |>.1) • ω.app c
  (.of t.1.1)) fun _ _ _ _ ↦ congrArg up (.symm ((exteriorMap_smul ..).trans
  (congrArg₂ _ (map_det ..) congr($(ω.naturality_apply ..).1).symm)))

lemma sum_minor_eq_mul_det (t : Matrix _ _ c.baseAlg) f i (h : ∀ j, t j ⬝ᵥ f = 1) :
    ∑ j : Fin d.succ, (-1) ^ (j.1 + i.1) • (t.submatrix j.succAbove i.succAbove).det =
    f i * t.det := by simpa [det_succ_column' _ i, ← dotProduct.eq_1, dotProduct_comm f, h]
    using (open Calc in t.det_updateCol_sum i f)

/-- The map (v, l_1, …, l_d) ↦ det(l_i)·ω(v), on points with d witnesses l_i·f̄(v) = 1, kills
boundaries; this is the induced map on the cokernel of the boundary. -/
def detCocycle := abCoker.desc (α := boundary (jouanolouRel f) d) (detCochain ω) (hom_ext fun c ⟨⟨v,
  l⟩, t⟩ ↦ by simpa [boundary, sum_app_apply, -NatTrans.app_sum, ← smul_assoc,
  sum_smul] using! congr($(sum_minor_eq_mul_det (vecCons
  0 <| l · |>.1) (vecCons 0 _) 0 (by simpa)) • ω.app c (.of v)))

@[simp] lemma pi_comp_detCocycle : abCoker.π _ ≫ detCocycle f ω = detCochain ω := rfl

/-- The natural map from the free abelian group on (A⊕M)^d to ⋀_A M sending a tuple (a_i,m_i) to
m_1∧…∧m_d. -/
def volumeForm : freeAb.obj (sqZeroExt ⋙ affineSpace k d) ⟶ hodgeCoeff := desc (fun _ v ↦
  ⟨(ιMulti _ d (snd ∘ v.1)).1⟩) fun _ _ _ _ ↦ congrArg _ (exteriorMap_iotaMulti ..).symm

/-- The class [dT/T] ∈ Hdg^d(𝔸^d, 𝔸^d ∖ 0) of the cocycle det(l_1, …, l_d)·dT_1 ∧ … ∧ dT_d on
tuples of linear forms with l_j(T) = 1. -/
def symbolClass : HodgeH (_root_.relFreeAb (@unimodular k _ d)) d :=
  cocycleClass exists_jouanolouRel_of_unimodular (detCocycle _ volumeForm)

attribute [-simp] map_smul zsmul_eq_mul

/-- For c = (A, M) and f ∈ (A ⊕ M)^d: α sends the class of each σ: c → C modulo D(v) to that of
σ(f) modulo 𝔸^d∖0. -/
abbrev IsInducedByCoords (v : Fin d → c.baseAlg) (f : Fin d → TrivSqZeroExt c.baseAlg _) (α :
  _root_.relFreeAb (someUnitLocus v) ⟶ _) := ∀ C σ,
  α.app C (relFreeAb.mk _ σ) = relFreeAb.mk (unimodular.whisker _) ⟨sqZeroExt.map σ.1 ∘ f⟩

seal Finset.univ Finset.sum Finset.prod in
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- Transformation law for Grothendieck symbols: let f = (f̄, ω), g = (ḡ, η) be d-tuples in the
square-zero extension, I = (f̄), f̄ = Mḡ, ω ≡ Nη and det N ≡ a·det M mod I, a ∈ k. Then
[ω/f̄] = a[η/ḡ] with supports in V(I). -/
lemma symbolClass_transformation {v : Fin d → c.baseAlg} {f g α β}
  (hα : IsInducedByCoords v f α) (hβ :
  IsInducedByCoords v g β) (hf : fst ∘ f = v) (M N : Matrix (Fin d) _ _) (a : k)
    (hM : v = M *ᵥ fst ∘ g)
  (hN : ∀ i j, (f i).snd j - ∑ l, N i l * (g l).snd j ∈ span (.range v)) (ha : N.det - algebraMap k
  _ a * M.det ∈ span (.range v)) : H.map _ α d symbolClass = a • H.map _ β d symbolClass := by
  let S : ⋀[c.baseAlg]^d _ →+ _ := (cocycleClass (U := someUnitLocus v) (hf ▸ fun _ _ ⟨i, h⟩ ↦
    ⟨⟨Pi.single i _⟩, (single_dotProduct ..).trans h.val_inv_mul⟩)).comp
    (.mk' (detCocycle (pointMap ⟨f⟩) <| ((homReprEquiv ..).trans
    .ulift).symm ·.1) fun _ _ ↦ (cancel_epi (abCoker.π _)).1 (hom_ext (by simp)))
  have T {g a} M (e : v = M *ᵥ fst ∘ g) {α} (h : IsInducedByCoords v g α) :
    a • H.map _ α d symbolClass = S ((algebraMap k _ a * M.det) • ιMulti _ d (snd ∘ g)) := by
    erw [smul_eq_push, ← pull_id_eq_push, ← map_pull_eq_pull_map rfl, H.map_id]
    refine pull_cocycleClass (R' := jouanolouRel (pointMap ⟨f⟩)) exists_jouanolouRel_of_unimodular _
      _ (pointMap _) ⟨fun C ↦ ↾fun x ↦ ⟨x.2.1 ᵥ* M.map x.1.1.1⟩, by intros; ext; congrm ⟨fun _ ↦
      $(.symm (map_vecMul ..))⟩⟩ (fun _ x ↦ (dotProduct_mulVec x.2.1 ..).symm.trans ∘ congr(_ ⬝ᵥ
      $(congr(_ ∘ $(hf.trans e)).trans (funext (map_mulVec _ _ _)))).symm.trans) ?_ h
    simp [volumeForm]; intros; erw [det_mul, ← map_det]
    exact congrArg up (.trans (by simp [exteriorMap_iotaMulti, mul_smul, ← smul_comm a]; rfl)
      congr(_ • $((add_zero _).trans (exteriorMap_smul ..))).symm)
  have K i (r : c.baseAlg) m := @T (update (inr ∘ m) i (1, r • m i)) 1 (updateCol 1 i v)
    (by ext; simp [mulVec, dotProduct, update, apply_ite]) 0 fun _ φ ↦ .symm (relFreeAb.mk_eq_zero
    (projSpace.span_eq_top_of_isUnit i (by simp [isUnit_iff_isUnit_fst, HodgeTest.sqZeroExt])))
  simp [H.map, ← cramer_apply, smul_smul, ↓comp_update, comp_def, mul_comm] at K
  rw [(one_smul ..).symm.trans (T 1 (by simp [hf]) hα), T M hM hβ, ← sub_eq_zero,
    ← map_sub, ← ((Pi.basisFun ..).exteriorPower d).sum_repr (_ - _)]
  simpa [basis_repr_apply, ιMulti_family] using sum_eq_zero fun s _ ↦
    (mem_span_range_iff_exists_fun.1 (show _ ∈ span (range v) by
    simp_rw [← Ideal.Quotient.eq] at *; simp [← ha, ← det_mul, map_det, Matrix.map,
      hN]; rfl)).elim fun t e ↦ congr(S ($e • _)).symm.trans (by simp [sum_smul, ← K])

variable (k d)

lemma symbolClass_one : ∃ ω : _ ⋙ freeAb.obj unimodular.toFunctor ⟶ hodgeCoeff, (∀ c v, ∃ w,
  (v.1.1 0).fst • w = (v.1.1 0).snd ∧ ω.app c (.of v) = ⟨.ι _ w⟩) ∧ @symbolClass k _ 1 =
  (relFreeAb.shortExact (unimodular.whisker _)).2.extClass.comp (.mk₀ ω) rfl :=
  (exists_map_extClass_comp (relFreeAb.shortExact _).2 shortExact_cokerBoundary.2 (detCocycle _
  volumeForm) (.mk₀ (𝟙 _)) _ (fromRel exists_jouanolouRel_of_unimodular) rfl).imp fun _ ↦
  .imp (fun a c ⟨⟨v⟩, u⟩ ↦ (exists_jouanolouRel_of_unimodular _ _ u).elim fun ⟨l⟩ h ↦ ⟨l 0 • _, by
  simpa [dotProduct, smul_smul, mul_comm] using! congr($h • (v 0).2), .symm (a c _ _ ⟨⟦.of ⟨(_, _),
  fun _ ↦ h⟩⟧, by with_unfolding_all congrm .of ⟨⟨_, $(funext nofun)⟩, _⟩, congrArg up (by
  simp [volumeForm]; rfl)⟩)⟩) (by simp_all [symbolClass, cocycleClass, push])

/-- The natural map 𝔸^d × 𝔸^1 → 𝔸^{d+1} appending a last coordinate. -/
@[simp] def affineSpace.snoc : affineSpace k d ⊗ affineSpace k 1 ⟶ affineSpace k d.succ :=
  ⟨fun _ ↦ ↾fun v ↦ ⟨Fin.snoc v.1.1 (v.2.1 0)⟩, by aesop_cat (add simp [affineSpace, comp_snoc])⟩

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- In characteristic 0: under 𝔸^d × 𝔸^1 → 𝔸^{d+1}, which
respects the complements of the origin, the class [dT/T] of
degree d + 1 pulls back to the external product of the classes [dT/T] of degrees d and 1. -/
lemma symbolClass_succ [CharZero k] : ∃ h, HodgeH.map (relFreeAb.prod ..)
  (_root_.cup exteriorAlg.mulPairing (@symbolClass k _ d) symbolClass (add_comm ..) :) =
  HodgeH.map (relFreeAb.map (affineSpace.snoc ..) h) symbolClass := by
  refine (symbolClass_one k).elim fun ω ⟨hω, e₁⟩ ↦ e₁ ▸ ⟨?h, by
  let G := (@unimodular k _ 1).whisker sqZeroExt
  let f := sqZeroExt.whiskerLeft (affineSpace.snoc k d)
  let Q := jouanolouRel f ⊓ ⟨({(x, l) | x.2 ∈ G.obj · ∨ l.1 (last d) = 0}), fun φ x ↦ .imp (G.map φ
    ·) (by simpa using! congrArg φ.1 ·)⟩
  have T {B : Ab} {c x} {a b : B} (e : x ∉ G.obj c → a = b) : a ⊗ₜ[ℤ] relFreeAb.mk G x =
    b ⊗ₜ relFreeAb.mk _ x := by_cases (by simp [relFreeAb.mk_eq_zero ·]) (e · ▸ rfl)
  refine (map_cocycleClass (R' := Q) (U' := .whisker (_ ⊔ _) _) exists_jouanolouRel_of_unimodular
    (fun c x a ↦ a.elim (exists_jouanolouRel_of_unimodular _ _ · |>.elim fun l a ↦ ⟨⟨snoc _ 0⟩,
    (sum_univ_castSucc _).trans (by simpa [f]), by simp⟩) fun _ ↦ (exists_jouanolouRel_of_unimodular
    _ _ (?h _ a)).imp (by tauto)) (abTensor.flip.obj (_root_.relFreeAb G)) ((-1) ^ d • 𝟙 _)
    (fun m ↦ desc (fun c ⟨⟨⟨v, x⟩, l⟩, t⟩ ↦ (if a : x ∈ G.obj c then 0 else .of ⟨(v,
    (⟨init <| l · |>.1⟩)), fun i ↦ by simpa [f, show (l i).1 _ = 0 from (t i).2.resolve_left a,
    jouanolouRel, dotProduct, sum_univ_castSucc] using! (t i).1⟩) ⊗ₜ relFreeAb.mk G x) fun _ _ φ _ ↦
    T (by have := G.map φ; split_ifs <;> tauto)) (by intros; exact T (by simp [·]; congrm ⟦.of ⟨⟨_,
    $(funext nofun)⟩, _⟩⟧)) (fun _ _ _ ↦ hom_ext fun _ _ ↦ T (by simp [·]; rfl))
    (detCocycle _ volumeForm)).elim fun y H ↦ (congrArg _ (DirectSum.of_injective
    _ ?_).symm).trans ((comp_assoc _ _ _ _ rfl (by simp)).symm.trans (congr($(H.2).comp _ rfl).trans
    ((exists_map_extClass_comp (shortExact_cokerBoundary (R := Q)).2 ((relFreeAb.shortExact
    G).2.map_of_exact (abTensor.obj _)) ((abTensor.obj _).map ω ≫ exteriorAlg.mulPairing) _
    (desc (fun c ⟨⟨⟨v, x⟩, l⟩, _⟩ ↦ ((-1) ^ d • (detCochain (R := ⊤) volumeForm).app c (.of ⟨(v,
    (⟨init <| l · |>.1⟩)), by simp⟩)) ⊗ₜ .of x) fun _ _ _ _ ↦ .symm congr($(((_ : ℤ) • detCochain
    _).naturality_apply ..) ⊗ₜ _).symm) _ (H.1.trans (hom_ext fun _ _ ↦ T (by simp [·])))).elim fun
    z h ↦ .trans (by exact h.2) ((pull_cocycleClass (R' :=
    Q) exists_jouanolouRel_of_unimodular _ (.id _) f {app _ := ↾(·.2)} (fun _ _ ↦
    (·.1)) (fun c ⟨_, t⟩ ↦ h.1 c _ _ ?_) (by tauto)).symm.trans congr($(id_pull _) _ _)))))
  erw [← comp_of, ← of_comp_homClass, ← cup_of, ← comp_of _ (.mk₀ ω), cup_comp_homClass_right,
    TotalH.cup]
  cases neg_one_pow_eq_or ℤ d <;> simpa [*, TotalH.comp_assoc, -Functor.flip_obj_obj, ← comp_of,
    TotalH.homClass, ← homClass_comp] using! congr((-1 :) ^ d • $(comp_assoc_of_eq
    (extClass_sign_comm (abTensor_shortExact (relFreeAb.shortExact G).2) (@symbolClass k _ d)) _))
  conv => enter [1, _, 1, 2, 2]; erw [sum_app_apply]
  simp
  erw [map_sum, sum_congr rfl fun _ _ ↦ map_zsmul ..]
  simp
  rw [show ∑ _, _ = _ by simpa [sum_smul, sum_tmul, pow_add, mul_zsmul]
    using! congr(($(sum_minor_eq_mul_det _ _ (last _) (t · |>.1)) • volumeForm.app c _) ⊗ₜ _)]
  refine if a : _ then (hω c ⟨_, a⟩).elim fun w e ↦ ⟨_ ⊗ₜ .of ⟨_, a⟩, rfl, congrArg up
    ?_⟩ else ⟨0, by
      simpa [det_eq_zero_of_column_eq_zero _ (t · |>.2.resolve_left a)] using map_zero _⟩
  simp [volumeForm, ExteriorAlgebra.ιMulti, ↓List.ofFn_succ', f, smul_smul, ← e.1,
    mul_comm]; erw [e.2]⟩
  rintro _ _ ⟨⟩ <;> apply eq_top_mono (span_mono _) ‹_› <;> simp <;> tauto
end
end

section
/-! Part of: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and correspondences
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Reduced coincidences of two maps are finitely many; local Jacobian terms. -/


open CategoryTheory Ideal CommAlgCat Algebra TrivSqZeroExt Matrix Set SqZeroExt NatTrans DualNumber
  Module
variable {k E d} [Field k] {W X : CommAlg k ⥤ Type 1} (u c : W ⟶ X) [Field E] [Algebra E k]

/-- For a k[ε]-point x of W: if c(x) = u(x), then x is constant, that is, comes from the k-point
below it. -/
abbrev ConstIfCoincident x := c (of k k[ε]) x = u _ x → x = W.map (fst ≫ structureMap) x

/-- The finite set s of k-points of W consists of coincidences of u and c, every field-valued
coincidence comes from s, and every k[ε]-valued coincidence is constant. -/
def IsCoincidenceSet (s : Finset _) := (∀ x, ConstIfCoincident u c x) ∧ (∀ w ∈ s, c _ w = u _ w) ∧
  ∀ K, IsField K.1 → ∀ x, c K x = u K x → ∃ w ∈ s, x = W.map structureMap w

/-- Let k be algebraically closed, X separated, u, c: W → X with every k[ε]-valued coincidence
constant and all field-valued coincidences in finitely many charts of W. Then the
coincidences form a finite set of k-points. -/
lemma exists_isCoincidenceSet [IsAlgClosed k] [hX : IsSepFunctor X] (h : ∀ x,
  ConstIfCoincident u c x) {ι} [Finite ι] (a : ι → EtaleChart d W) (ha : ∀ K, IsField K.1 → ∀ x,
  c K x = u K x → ∃ i, x ∈ (a i).locus K) : ∃ s, IsCoincidenceSet u c s := by
  choose J hJ using fun {A} y ↦ by simpa [← naturality_apply] using hX.1 A (c _ y) (u A y)
  choose o j using @nullstellensatz_exists_le_ker k
  use (finite_iUnion fun i ↦ .dependent_image (@finite_minimalPrimes_of_isNoetherianRing _ _
    (FiniteType.isNoetherianRing k _) (J (a i).point)) fun p m ↦ W.2 (ofHom (o m.isPrime.1))
    (a i).point).toFinset, h
  simp
  use fun _ _ _ m ↦ (· ▸ (hJ ..).2 (m.le.trans (j _)))
  peel ha
  obtain ⟨⟨_, ⟨⟩⟩, _⟩ := this, IsField.isDomain ‹_›
  exact (exists_minimalPrimes_le (J := comap ..) ((hJ ..).1 ‹_›)).imp fun p ⟨m, q⟩ ↦
   (exists_mem_colon_of_tangent rfl (j _) fun v _ l
    r ↦ congr(($((a _).eq_comp_of_map_point_eq _ (h _ ((hJ ..).2
   (m.le.trans l)))) r).2)).elim fun _ l ↦ ⟨m, W.map_comp_apply .. ▸ eq_comp_structureMap_of_ker_le
    (l.1 ⟨·, ·, rfl⟩ |> m.isPrime.2 |>.resolve_left (by tauto) |> q) ▸ rfl⟩

/-- In every chart of X with d coordinates containing c(w), some matrix N of determinant n has
t·du − dc = N(du − dc) on all tangent vectors of W at w. -/
def HasJacobianRatio {X} (u c : W ⟶ restrictAlg E k ⋙ X) d (t n : k) w := ∀ A : EtaleChart d X,
  c _ w ∈ A.locus _ → let ξ (γ : _ ⟶ (restrictAlg ..) (.of k k[ε])) i := (γ (A.coordinate i)).snd
      ∃ N, N.det = n ∧ ∀ v α γ, W.map fst v = w → X.map α A.point = u _ v →
        X.map γ A.point = c _ v → t • ξ α - ξ γ = N *ᵥ (ξ α - ξ γ)

/-- Let v be a (k ⊕ k^d)-point of X based in a chart with d coordinates, whose k[ε]-points φ(v),
φ linear forms on k^d, are distinct. Then their chart coordinates are those of φ in some
basis, and they exhaust the tangent vectors at the base point. -/
lemma EtaleChart.tangent_mem_range_of_jet {X} (A : EtaleChart d X) {T : FGModuleCat k} (hT : finrank
  k T = d) v : let Y := restrictAlg E k ⋙ X; let f φ := Y.map (ofHom (map (Dual.eval k T φ))) v
    Y.map fst v ∈ A.locus _ → f.Injective → (∀ w, Y.map fst w = Y.map fst v → w ∈ range f) ∧ ∃ D :
      T ≃ₗ[k] _, ∀ φ α, X.map α A.point = f φ → (A.coordinate · |> α |>.snd) = D φ := fun hv h ↦ by
  obtain ⟨⟨⟨γ⟩, ⟨⟩⟩, S : IsSquareZero ((restrictAlg E k).map fst)⟩ :=
    (A.isOpenSub.mem_of_isSquareZero _ · _ hv) (fst_surjective_and_kerIdeal_sq (k := k)),
    fst_surjective_and_kerIdeal_sq (k := k) (M := k)
  have U {α β} a b := (A.injective _).eq_iff.2 (A.lift_unique S a (ext congr($a _) <|
    congrFun b ·) : α = β)
  erw [← funext fun _ ↦ X.map_comp_apply ..] at *
  let B := (0 + LinearMap.pi fun i ↦ (γ.1 _).2).linearEquivOfInjective (by tauto) (by simpa)
  use fun w H ↦ ?_, B, fun _ _ ↦ (A.injective _ · ▸ rfl)
  obtain ⟨_, ⟨⟩⟩ := A.isOpenSub.mem_of_isSquareZero _ S w (H ▸ hv)
  refine (B.surjective _).imp fun φ ↦ U (A.injective _ ?_)
  simpa [SqZeroExt.fst, ← fstHom_comp_map (.applyₗ φ), -fstHom_comp_map] using! H.symm

/-- Let W have an atlas of dimension d and P be a tangent polynomial of c, u at w with P(1) ≠ 0.
Then `HasJacobianRatio` holds at w with determinant P(t)/P(1) for all t, and every k[ε]-valued
coincidence above w is constant. -/
lemma IsTangentPoly.hasJacobianRatio {X} {c u : W ⟶ restrictAlg E k ⋙ X} {w P} (hW :
  IsChartCovered d W) (hP : IsTangentPoly d c u w P) (h₁ : P.eval 1 ≠ 0) : (∀ t, HasJacobianRatio u
  c d t (P.eval t / P.eval 1) w) ∧ ∀ v, W.map fst v = w → ConstIfCoincident u c v := by
  obtain ⟨_, v, T, hT, ⟨⟩, h, hu, p⟩ := hP
  obtain ⟨⟨S, ⟨⟩⟩, V, _⟩ := (⟨(1 - T).equivOfDetNeZero (by grind [one_smul]), by simp⟩ : T ∈ range
    (1 - ·.1)),
    EtaleChart.tangent_mem_range_of_jet _ hT v (hW.1 _ (Field.toIsField k) _).choose_spec h.of_comp
  use fun t A hw ↦ ?_, (V · · |>.elim fun | φ, rfl, e => ((by simpa using h (e.trans (hu φ)).symm)
    ▸ .symm (W.map_comp_apply .. ▸ by congr with _ <;> simp)))
  obtain ⟨_, D, G⟩ :=
    (by simpa only [← naturality_apply] using A.tangent_mem_range_of_jet hT (c _ v) :) hw h
  use (D ∘ₗ ((1 - t • (1 - S.1)) * S.symm.1) ∘ₗ D.symm).toMatrix', by
    simp [S.det_coe_symm]; grind [one_smul, sub_sub_cancel], fun v _ _ ↦ by
    rintro ⟨φ, ⟨⟩⟩ a b; simp [G φ _ b, G _ _ (hu φ ▸ a), ↓map_neg] ∘ V v
end

section
/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Class of a rational point in Hodge cohomology; independence of choices, excision,
sums. -/

open CategoryTheory Classical Function Ideal TrivSqZeroExt relFreeAb

seal H.map

attribute [local simp] Field.toIsField mem_offPoints_iff isOpenSub_offPoints ComesFromPoints

variable {k} [Field k] {X X' d e R R'} {U : Subfunctor X} {g m} {ξ :
  HodgeH (relFreeAb U) d} (a : EtaleChart e X) {z : X (.of k k)}

/-- For a chart with ring R and e coordinates, and f ∈ R^d, the universal point gives an
equivalence for Hodge coefficients from (h_{(R,R^e)}, locus where some f_i is a unit) to
(Spec R, locus where f generates the unit ideal). -/
lemma EtaleChart.isCohomEquiv_univPoint : ∃ μ : a.R ⟶ HodgeTest.sqZeroExt ⟨_, Fin e⟩,
  LeftInverse fst μ ∧ ∀ {d f S}, S = (@unimodular k _ d).preimage (pointMap ⟨f⟩) →
  ∃ h, IsCohomEquiv hodgeCoeff (map (U' := someUnitLocus (c := ⟨_, _⟩) f) (𝟙 _) h ≫ map (U :=
  S.whisker _) (pointMap ⟨μ⟩) le_rfl) := a.exists_univPoint.imp fun _ ⟨s, j⟩ ↦
  (forall_and.1 j).elim fun j _ ↦ ⟨s, @fun _ f _ e ↦ funext (s ∘' f) ▸ e ▸ ⟨fun _ _ ⟨i, h⟩ ↦
  projSpace.span_eq_top_of_isUnit i (isUnit_iff_isUnit_fst.2 h), Iff.mpr (IsCohomEquiv.comp_iff
  (isCohomEquiv_of_le _ (isCohomEquiv_someUnitLocus <| by apply unimodular.2 ·.baseProj ·.2)))
  (relFreeAb.excision _ .of_top_le (m := mono_of_app_injective j) rfl)⟩⟩

lemma EtaleChart.symbolClass_eq_of_cutsOutLocus {f g : Fin d → a.R} {P x} (D : CutsOutLocus _ P x f)
  (F : CutsOutLocus X' P x g) : symbolClass.map (relFreeAb.map _ D.preimage_fieldLocus_not.le) =
  symbolClass.map (relFreeAb.map _ F.preimage_fieldLocus_not.le) := by
  have hg : _ = span (.range g) := eq_of_forall_ge_iff
    (·.mk_ker ▸ (D _ (CommAlgCat.ofHom (Quotient.mkₐ ..))).trans (F ..).symm)
  choose M hM using fun _ ↦ mem_span_range_iff_exists_fun.1 (hg ▸ mem_span_range_self)
  obtain ⟨⟨μ : _ →ₐ[k] TrivSqZeroExt a.R (_ → a.R)⟩, e : LeftInverse _ μ,
    V⟩ := a.isCohomEquiv_univPoint
  apply ((V D.preimage_fieldLocus_not).2 _).1; erw [← H.map_comp,
    symbolClass_transformation (f := μ ∘ f) (g := μ ∘ g) _ _ _ M M _ (funext
    _).symm, one_smul, H.map_comp] <;>
    first | tauto | (simp [comp_def, e _] <;> assumption) | rw [hg]
  simp [← hM, snd_sum, e _, Ideal.sum_mem, mul_mem_right, mem_span_range_self]

/-- Excision for Hodge cohomology: let u: X' → X be injective on points with open image, and let
every field-valued point outside the image lie in an open subfunctor contained in U. Then u
induces bijections Hdg^n(X, U) → Hdg^n(X', u⁻¹U) for all n. -/
lemma hodge_excision {u : X' ⟶ X} [Mono u] (ho : IsOpenSub (.range u)) (H : ∀ K, IsField K.1 →
  ∀ x ∉ Subfunctor.range u K, ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ U) {U'} (e : U' = U.preimage u) :
  IsCohomEquiv hodgeCoeff (HodgeTest.sqZeroExt.whiskerLeft (map _ e.le)) := excision (U := U.whisker
  _) ((restrictAlong _).map u) (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover
  (byCases (by tauto) <| .imp (by tauto) ∘ H · · ·))) congr(.whisker $e _)

@[local simp ←] lemma HodgeH.map_comp {N N' M} (α : M ⟶ N') β (x : @HodgeH k _ N d) :
    x.map (α ≫ β) = (x.map β).map α := .symm (H.map_comp ..).symm

@[simp] lemma HodgeH.map_zero {N} : ξ.map (N' := N) 0 = 0 := ((H.mapHom ..).flip ξ).map_zero

/-- g ∈ R^d cuts out P at y ∈ X(R), y maps the complement V of that locus into U, and y^*ξ =
m·[dg/g] in Hdg^d(Spec R, V). -/
def IsLocalSymbol ξ y P g (m : k) := ∃ᵉ (D : CutsOutLocus X P y g) (h), HodgeH.map (map (pointMap
  (A := R) y) (U := U) h) ξ = m • .map (map _ D.preimage_fieldLocus_not.le) (@symbolClass k _ d)

lemma IsLocalSymbol.map {y P} (h : IsLocalSymbol ξ y P g m) φ :
    IsLocalSymbol ξ (@X.map R R' φ y) P (φ ∘ g) m := ⟨(by simpa [span_le] using h.1 · <| φ ≫ ·), by
  rw! (transparency := .all) [← pointMap_comp _ (pointMap y)]
  exact ⟨_, by simpa using! congr($(h.2.2).map (relFreeAb.map _ le_rfl))⟩⟩

/-- Every z ∈ s lies in some chart on which d functions g generate the ideal of z and ξ ∈
Hdg^d(X, U) restricts to n(z)·[dg/g]. -/
def IsPointSum (s : Set _) (n : _ → k) (ξ : HodgeH (relFreeAb U) d) := ∀ z ∈ s, ∃ᵉ (a :
  EtaleChart d X) (g), z ∈ a.locus _ ∧ IsLocalSymbol ξ a.point (ComesFromPoints {z}) g (n z)

/-- The class of a k-point z: the image in Hdg^d(X) of a chosen class in Hdg^d(X, X∖z) with
local multiplicity 1 at z (`IsPointSum`), arbitrary if none exists. -/
noncomputable def pointClass d (z : X _) :=
  HodgeH.map (q := d) (π (offPoints {z})) (epsilon (IsPointSum {z} 1))

lemma exists_isOpenSub_le_offPoints [IsSepFunctor X] (h : z ∈ U _) ⦃K⦄ (hK : IsField K.1) ⦃x⦄ (n :
  x ∉ U K) :
  ∃ O, IsOpenSub O ∧ x ∈ O K ∧ O ≤ offPoints {z} := by have := U.map (V := K) structureMap h; aesop

/-- Let X be separated over a field k, a an e-dimensional chart containing z ∈ X(k), g functions
cutting out z on a. Some ξ ∈ Hdg^e(X, X∖z) restricts to [dg/g] on a and satisfies `IsPointSum` for
{z} with multiplicity 1. -/
lemma EtaleChart.exists_isLocalSymbol [IsSepFunctor X] {g} (h : CutsOutLocus X (ComesFromPoints {z})
  a.point g) (w : z ∈ a.locus _) : ∃ ξ : HodgeH (relFreeAb (offPoints {z})) e, IsLocalSymbol ξ
  a.point (ComesFromPoints {z}) g 1 ∧ IsPointSum {z} 1 ξ := ((hodge_excision a.isOpenSub
  (exists_isOpenSub_le_offPoints w) rfl e).2 _).imp fun _ l ↦ (⟨·, by rintro _ ⟨⟩; tauto⟩) ⟨h, _, l⟩

lemma IsPointSum.map_eq_smul_pointClass [IsSepFunctor X] {n ξ} (h : IsPointSum {z} n ξ) :
  .map (π (offPoints {z})) ξ = n z • pointClass d z := by
  have ⟨a, g, hz, h⟩ := h z rfl
  have ⟨b, g₀, e, h'⟩ := epsilon_spec ⟨_, (a.exists_isLocalSymbol h.1 hz).choose_spec.2⟩ _ rfl
  have ⟨c, E⟩ := a.exists_locus_eq_inf b; have ⟨⟨_, e₁⟩, _, e₂⟩ := E ▸ c.point_mem_locus
  obtain ⟨⟨D, _, h⟩, F, _, u⟩ := e₁ ▸ h.map _, e₂ ▸ h'.map _
  rw [c.symbolClass_eq_of_cutsOutLocus D F, ← u.trans (one_smul ..), ← map_smul] at h
  simp [(hodge_excision c.isOpenSub (exists_isOpenSub_le_offPoints (by aesop)) rfl _).1 h,
    pointClass]

/-- Let X be separated, s a finite set of k-points, U = X∖s. If ξ ∈ Hdg^d(X, U) has local
multiplicity n(z) ∈ k at each z ∈ s (`IsPointSum`), its image in Hdg^d(X) is Σ_{z∈s} n(z)·cl(z). -/
lemma IsPointSum.map_eq_sum_pointClass [IsSepFunctor X] {s : Finset _} {n} (h :
  IsPointSum s n ξ) (e : U = offPoints s) : .map (π _) ξ = ∑ z ∈ s, n z • pointClass d z := by
  induction' s using Finset.induction with z s hz ih generalizing U
  simp [(freeAb.hom_ext fun _ _ ↦ mk_eq_zero (e ▸ nofun) : π U = 0)]
  cases show U = offPoints {z} ⊓ offPoints s by aesop (add simp [offPoints, fieldLocus])
  obtain ⟨x, y : HodgeH .., E : y.map (relFreeAb.map _ (by simp)) = _⟩ :=
    ((hodge_excision (u := (offPoints s).ι) (by simp) (exists_isOpenSub_le_offPoints (z :=
    z) (by simpa)) (by ext _ ⟨⟩; apply_rules [and_iff_left]) d).2 (ξ.map (map _
    le_rfl))).imp fun x E ↦ ((LongExactSeq.contravariant
    ((shortExact_triple ..).2.map_of_exact (restrictAlong _)) _).exact_f_g d (ξ - .map (map
    (𝟙 _) (by simp)) x)).1 ((HodgeH.map _).sub_mem_ker_iff.2 (by simpa using! E.symm))
  have O {t A B l l' x y} t' (e : ξ = .map (map (𝟙 X) (U := A) l) x + .map (map (𝟙 X) (U := B)
      l') y) : B = offPoints t' → t = ↑(insert z s) \ t' → IsPointSum t n x := by
    rintro rfl rfl w o; peel 4 h w o.1
    exact ⟨_, by simpa [e, -ComesFromPoints, (hom_ext fun _ _ ↦ mk_eq_zero fun K _ l ↦
      (mem_offPoints_iff l).1 (X.map_comp_apply .. ▸ by_contra (exists_isOpenSub_le_offPoints (z :=
      w) (by aesop) l · |>.elim (by tauto))) : map _ this.1 ≫ map _ l' = 0)] using this.2⟩
  cases add_eq_of_eq_sub' E
  simp [hz, ih (O _ (add_comm ..) rfl _), (O s rfl _ _).map_eq_smul_pointClass, π_map]
end
