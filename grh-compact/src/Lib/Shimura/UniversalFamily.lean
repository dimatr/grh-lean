import Lib.Shimura.LiftedIsogenies
import Lib.Shimura.ModelAlongArc
import Lib.Shimura.PeakContraction
import Lib.Shimura.UniversalPoints

section
/-! Known result: Deformations of the PEL object have at most n-1 parameters. Only the upper bound
for first-order deformations is proved here, at every good place. The proof works on the finite
group scheme of w-torsion with Drinfeld's lifting lemma, without p-divisible groups or crystals.
Source: N. Katz, Serre–Tate local moduli, LNM 868 (1981), §1 (Drinfeld's lemma); J. Lubin, J. Tate,
Formal moduli for one-parameter formal Lie groups, Bull. SMF 94 (1966); M. Harris, R. Taylor, The
Geometry and Cohomology of Some Simple Shimura Varieties (2001), III.4.1. -/

noncomputable section


open CategoryTheory AlgebraicGeometry TrivSqZeroExt ThetaObject Obj IsGroupBaseChange CommRingCat
  DualNumber Module Dual Spec Over OverMorphism RingHom Algebra
variable {E k M} [Field E] [CMBase E] {D : PEL E} [Field k] {Z σ} [AddCommGroup M] [Module k M] {X :
  ThetaFamily D Z σ} {x₀ : ThetaObject X _} {x} (hp : IsPullbackAlong (sqZeroReduction k (M →ₗ[k]
  k)) x₀ x) ⦃C : Type⦄ {C'} [CommRing C] [Algebra k C] [CommRing C'] [Algebra k C'] (φ : C →ₐ[k] C')

instance : CommRing (TrivSqZeroExt C (M →ₗ[k] C)) := inferInstance

instance : IsLocalRing (TrivSqZeroExt k (M →ₗ[k] k)) :=
  .of_nonunits_add (by simp_all [isUnit_iff_isUnit_fst])

attribute [-simp] smul_eq_zero
attribute [local simp ←] Spec.map_comp map_comp_assoc ofHom_comp AlgHom.comp_toRingHom smul_smul
  map_smul
attribute [local simp↓] map_inj lift_def algebraMap_eq_inl'

/-- For a k-algebra map φ: C → C', the ring homomorphism C ⊕ Hom_k(M,C) → C' ⊕ Hom_k(M,C') of
trivial square-zero extensions given by φ and composition with φ. -/
@[simps] def sqZeroMap : TrivSqZeroExt C (M →ₗ[k] C) →+* TrivSqZeroExt C' (M →ₗ[k] C') := by
  refine' {toFun x := inl (φ x.fst) + inr (φ ∘ₗ x.snd), ..} <;> aesop

variable (C) in
def toSqZeroSpec : map (sqZeroReduction k (M →ₗ[k] k)) (specOver k C) ⟶ .mk (specMap
  (sqZeroMap (ofId k C))) := homMk (sqZeroReduction ..)

lemma exists_point_lift [IsLocalRing C] y : ∃ Z, toSqZeroSpec C ≫ Z =
  hp.isGroupBaseChange.pointEquiv y :=
  let ⟨_, _, i, L⟩ := exists_isEtaleChart _ x.smoothOfRelativeDimension
  (L _ (inl ∘ _) (landsIn_iff_mem.2 i) ((Over.w _).trans (toSqZeroSpec C).w.symm) rfl).imp fun _ ↦
    (ext ·.1.1)

/-- For a k-algebra map φ: C → C', the induced morphism Spec(C' ⊕ Hom_k(M,C')) → Spec(C ⊕
Hom_k(M,C)) over Spec(k ⊕ M*), M* the dual of M. -/
def sqZeroSpecMap : Over.mk (specMap (sqZeroMap (ofId k C'))) ⟶ .mk
  (specMap (sqZeroMap (M := M) (ofId k C))) := homMk (specMap (sqZeroMap φ))

lemma sqZeroSpecMap_point_lift {y Z} (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y) :
  toSqZeroSpec _ ≫ sqZeroSpecMap φ ≫ Z = hp.isGroupBaseChange.pointEquiv (specOver.map φ ≫ y) := by
  simp [pointEquiv_apply] at *; ext; simp [← e, toSqZeroSpec, sqZeroSpecMap,
    specOver.map]; congr 2; aesop

lemma isInfinitesimal_of_comp_eq_zero (Z : _ ⟶ x.groupScheme) : toSqZeroSpec C ≫ Z = 0 →
  IsInfinitesimal (ofHom (fstHom C ..).1) Z := by
  simp [IsInfinitesimal, ↓eq_zero_iff_factors_zero_section]; tauto

include hp in
/-- Known result: Deformations of the PEL object have at most n-1 parameters. -/
lemma tangent_bound [IsAlgClosed k] (hw : D.IsGoodAt (ker x₀.baseHom)) {V : ValuationSubring ℂ} {w}
  (e : FullStructure w) (hr : x₀.IsRigid) {χ : V →+* k} (h₀ : x₀.IsPullbackAlong (specMap χ) w)
  (hρ : x.baseHom = (algebraMap ..).comp x₀.baseHom) (h : ∀ l, specMap (map (eval k M l)).1 ≫ x =
  specMap (algebraMap ..) ≫ x₀ → l = 0) : finrank k M ≤ Fintype.card D.Index - 1 := by
  obtain ⟨_, ⟨-, c, hc, hc0, t, ht, H⟩, b, hb, ⟨_, _, co⟩, hN⟩ := isGoodAt_ker_spec hw
  choose ω L Q A F P using by simpa [hρ] using x.exists_tangent_log (b := b) (by simp [*])
  choose Y J using exists_point_lift hp
  choose N hL using fun {C} [CommRing C] [Algebra k C] [IsLocalRing C] (y : placeTorsion x₀ C) ↦
    have N := isInfinitesimal_of_comp_eq_zero (c • Y y.1) (y.rec (by simp_all))
    have hL Z (e : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv
      y := by simp [J]) := have n := isInfinitesimal_of_comp_eq_zero (Z - Y y.1) (by
        simp [*]); by simpa [← smul_add, L n, hc] using (A (n.smul c) N).symm
    And.intro N @hL
  refine finrank_le_of_placeTorsion hw h₀ e (fun _ ↦ ⟨⟨(snd <| ω <| c • Y ·.1), fun y
    z ↦ by simp [↓hL (y + z) (Y y + Y z), A (N y) (N z)]⟩, fun a y ↦ by simp [↓hL (a • y) (a • Y y),
    smul_comm c, L (N y)]⟩) (fun φ y ↦ by simp [hL (placeTorsionMap φ y) _ (sqZeroSpecMap_point_lift
    hp φ (J _)), ← ModuleObj.comp_smul, P (N y) (sqZeroSpecMap φ) rfl]) (fun y u ↦ by simp [hc, (hL
    y (Y y - sqZeroSpecMap (.comp (ofId ..) (fstHom ..)) ≫ Y y.1) (by simp [sqZeroSpecMap_point_lift
    hp, ← specOver.map_comp_assoc, *])).trans (@L _ _ (ofHom (sqZeroMap (fstHom ..))) ⟨(⟨sqZeroMap
    (ofId ..) ·, by ext <;> simp⟩), by simp +contextual [TrivSqZeroExt.ext_iff, DFunLike.ext_iff]⟩ _
    _ (by simp [IsInfinitesimal, OverMorphism.ext_iff, sqZeroSpecMap]; congr; ext <;> simp) c)])
    fun l hl ↦ ?_
  let m := specMap (map (eval k M l)).1
  obtain ⟨⟨z, hz⟩, z₀, hz'⟩ := x.exists_isPullbackAlong m,
    x₀.exists_isPullbackAlong (specMap (algebraMap _ k[ε]))
  obtain ⟨o, hq, hq₀⟩ := by simpa [hρ, ← comp_assoc] using hz.baseHom_eq_comp,
    (by simpa [m, ← hz, IsPullbackAlong] using! hp : IsPullbackAlong (sqZeroReduction ..) x₀ z),
    (by simp [← hz', IsPullbackAlong] : IsPullbackAlong (sqZeroReduction ..) x₀ z₀)
  choose G _ u K using drinfeld_lift hq₀ hq fun _ _ ↦ (·.ringChar_smul_and_smul_eq_zero.2 o hb hc)
  choose f _ g using exists_lift_of_kills_ker (hq' := hq₀) (c • 𝟙 _) (by simp) hc0 _ _ _ u fun C ↦
    fun y hy _ ↦ by
    algebraize [(algebraMap _ C).comp (inlHom k k)]
    let χ := (liftEquivOfComm (A := C) ⟨(ε : k[ε]) • .applyₗ' (R := k) C l, by simp [smul_smul]⟩).1
    let d : (map m) (specOver ..) ⟶ .mk (specMap (sqZeroMap (ofId ..))) :=
      homMk (specMap χ) (homEquiv.injective
      (by ext; simp [m, χ, TrivSqZeroExt.map, smul_def, algebraMap_toAlgebra, mul_comm]))
    let v : specOver k C ⟶ _ := homMk (V := (Over.map _).obj (specOver k[ε] C)) (𝟙 (Spec _))
      (by simp) ≫ hz'.isGroupBaseChange.pointEquiv y
    obtain ⟨⟨_, ψ, _, -, _, e, U⟩, hy⟩ := exists_isSqZeroExt_mod_eps (specOver k[ε] C).hom,
      show c • v = 0 by simpa [map_smul] using congr(_ ≫ hz'.isGroupBaseChange.pointEquiv $hy)
    obtain ⟨a, n⟩ := show ofHom χ ≫ ψ = ofHom (fstHom C ..).1 ≫ ψ by ext; simp [χ, smul_def, e,
      -map_mul], isInfinitesimal_of_comp_eq_zero (c • Y v) (by simp [*])
    refine (K _ (hz.isGroupBaseChange.pointEquiv.symm (d ≫ Y v)) y fun _ _ s ↦ (U s.w).rec fun s'
      g ↦ by ext; simpa [← g, hp.comp_toFamily, hz'.comp_toFamily, ← hz.comp_toFamily, d, v,
      toSqZeroSpec, a, pointEquiv] using (s' ≫= map ψ ≫= congr($(J v).1 ≫ x.toFamily.1))
      ).trans (hz.isGroupBaseChange.pointEquiv.injective ?_)
    simpa using Q (n.precomp d rfl _ a) (by simpa [↓P n d rfl, by simpa [smul_comm c, L n,
      ((sub_mem_ker_iff _).1 ht)] using (congr(snd $(hL ⟨t • v, by simpa using ((Ideal.torsionOf _
           _ v).span_singleton_le_iff_mem.2 hy <| H ⟨·, ·, mul_comm ..⟩)⟩ (t • Y v)) l).symm.trans
           (@hl _ _ _ _ (.trans k[ε] C) _)), χ] using F n)
  choose μ _ g using exists_lift_of_kills_ker f g (by simpa [·, hb] using congr(x₀.baseHom $co)) hq₀
    ((star D.β - b) • 𝟙 _) 1 (by simp) fun _ ↦ fun y h K ↦ by simpa [add_smul, K,
    (hr.eq_zero_of_pairing_eq_zero hz' ((D.β - b) • (star D.β - b) • y) 1 (𝟙 _) (by simp [smul_comm
    _ (D.β - _), AgreeModEps.ringChar_smul_and_smul_eq_zero hq₀, *,
    isLinear_and_pairing_eq_of_reduction f g]) fun _ t w ↦ by
    simpa [h, Pic.pairing.eq_1 _ 0, by simpa using (z₀.pairing_pow_smul_adjoint b 1 · w)] using
      ((isLinear_and_pairing_eq_of_reduction f g).2.2 hz' (t ≫ y) w).symm)] using congr($co • (star
    D.β - b) • y).symm
  choose μ _ g using exists_lift_of_kills_ker μ g (by simp) hq (𝟙 _) 1 (by simp) (by simp)
  obtain ⟨_, -, N⟩ := isLinear_and_pairing_eq_of_reduction _ g
  refine h l (hz ▸ hz' ▸ (hr.eq_of_hom hz' (o ▸ hz'.baseHom_eq_comp) μ (by simp [N hz']) fun l ↦
    eq_of_sub_eq_zero ((Ideal.torsionOf_eq_top_iff ..).1 (eq_top_mono (sup_le (by simp [smul_sub,
    ← IsLinear.smul_comp, (Subtype.ext l.2 : D.𝔑 • l = 0)]) ?_) hN))).1.symm)
  have K := AgreeModEps.ringChar_smul_and_smul_eq_zero hq (y := z₀.levelPoints l ≫ μ - z.levelPoints
    l) fun _ _ t ↦ by simp [hq.levelPoints_eq_pullSection, ← hq₀.levelPoints_eq_pullSection,
    g, OverMorphism.ext_iff, by simpa using t.w, ← hq.isGroupBaseChange.pullSection_comp,
    ← hq₀.isGroupBaseChange.pullSection_comp_assoc, ← comp_left _ _ _ hq₀.schemeMap]
  simpa [mul_comm (ker _), smul_comm (ringChar k), Ideal.span_insert, Ideal.sup_mul,
    Ideal.span_singleton_mul_le_iff, Nat.cast_smul_eq_nsmul, K] using (@K.2 _ o _ · hb)
end
end

section
/-! Part of: Moduli of abelian varieties by theta values (theta-null embedding, universal family)
(known result; see Lib.Shimura.ThetaModuli.UniversalFamily).

This file: Closure of theta points is an abelian scheme with action and theta structure. -/


open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory NumberField
  ThetaObject Obj LineBundle PointFn AddObj Scheme ThetaTorus PeriodMap Category Over Spec
  IsLocalRing Fint
attribute [local simp] pullback.lift_fst pullback.lift_snd IsHomogCoords.pull_iff paddingTuple
  doubledCoeffs thetaProduct pull_pi coordSection
  landsIn_iInf AddChar.map_add_eq_mul Finset.prod_ne_zero_iff Int.cast_smul_eq_zsmul funext_iff
attribute [-simp] map_smul
variable {V ι κ : Type} [FinComplexSpace V] {S} [IsReduced S] [IsLocallyNoetherian S] [Finite ι]
  {η : κ → _} (j : ι → κ) (hη : @IsDenseFamily ι S (η <| j ·))

omit [Finite ι] in
lemma LineBundle.IsHomogCoords.pi {K X t V} [Fintype K] {M : K → LineBundle X ι} {θ : ι →
  V → ℂ} {w : K → V} (h : ∀ l, (M l).IsHomogCoords (A := ⟨ℂ⟩) t (θ · (w l))) :
  (LineBundle.pi M).IsHomogCoords t fun μ ↦ ∏ l, θ (μ l) (w l) := by simp_all [IsHomogCoords]

include hη

/-- Let A be flat and proper over S with reduced closed fibres, with maps e_i: V → A(ℂ) dense in
reduced fibres over dense points. If addition, zero and an O-action on V extend to morphisms
of A, then A is an abelian scheme with O-action. -/
lemma exists_isAbelianScheme {O A} [CommRing O] {e : ∀ i, V → (Over.mk (η i) ⟶ A)} (he : ∀ i,
  IsSeparatingFamily fun v ↦
  (lift (e i v) (𝟙 _)).1) (s : IsSeparatingFamily fun s : κ × V ↦ (e s.1 s.2).left) [Flat A.hom]
  [IsProper A.hom] (red : AllSpecializeTo S fun t ↦ IsReduced (pullback A.hom t)) {f : O → _} {F :
  κ → O →+* V →L[ℂ] V} (q : ∀ d i z, e i z ≫ f d = e i (F i d z)) m o (hm : ∀ i y z, e i (y + z) =
  lift (e i y) (e i z) ≫ m) (ho : ∀ i, toUnit _ ≫ o = e i 0) : ∃ (_ : IsAbelianScheme A) (_ :
  ModuleObj O A) (ε : ∀ _, V →+ _), e = (ε · ·) ∧ ∀ c i z, c • e i z = e i (F i c z) := by
  obtain ⟨t, _ : Flat (A ⊗ A).hom⟩ := s.prod hη s.1 (he ·.1), Flat.comp (pullback.fst ..) _
  have := t.prod hη s.1 (he ·.1.1)
  refine let _ : AddObj A := { AddGrpObj.mk (toAddMonObj := ⟨o, m, (λ_ A).inv_comp_eq_id.1 (?_ :
      lift (toUnit A) (𝟙 A) ≫ _ = _), (ρ_ A).inv_comp_eq_id.1 (?_ : lift (𝟙 A) (toUnit A) ≫ _ = _),
      (α_ A A A).inv_comp_eq.1 ?_⟩) (f (-1)) ?_ ?_ with add_comm := ?_ }
    let _ := @ModuleObj.mk _ O _ A _ (fun T ↦ @.ofMinimalAxioms _ _ _ _ ⟨flip (· ≫ f ·)⟩
      (have := isAdditive_of_universal (f := f ·) ?_; (add_comp · · _)) (fun _ _ ↦
      (· ≫= ?_ |>.trans (comp_add ..)))
      (fun _ _ ↦ (· ≫= (?_ : _ = _ ≫ _))) (· ≫= (?_ : _ = 𝟙 A))) fun _ _ _ ↦ (assoc ..).symm
    ⟨.mk (toSmooth := open HasRingHomProperty RingHom MorphismProperty Hom Pullback in
    smoothLocus_eq_top_iff.1 (top_unique fun y _ ↦ have ⟨k, _, _, t, a, H⟩ := red (A.hom y)
      have ⟨⟨x, b, a⟩, U', u, n⟩ :=
        And.intro ((isClosedMap _).specializingMap a) (exists_isAffineOpen_landsIn t)
      let ⟨W, v, m, e⟩ := exists_isAffineOpen_mem_and_subset ((mem_preimage _).2 (a ▸ n ⟨⟩))
      let := (appLE _ U' W e).1.toAlgebra
      b.mem_open (smoothLocus _).2 ((formallySmooth_stalkMap_iff U' u W v e m).2
        (@.of_formallySmooth_fiber _ _ _ _ _ (flat_appLE _ u v _) (finitePresentation_appLE _ u v _)
        _ _ _ _ ⟨rfl⟩ (smooth_algebraMap.1 (Spec_iff.1 (of_isPullback (.paste_horiz (.of_horiz_isIso
        ⟨(fiberToSpecResidueFieldIso ..).2.w⟩) (isPullback_fiberToSpecResidueField_of_isPullback
        (.of_horiz_isIso_mono ⟨id_comp _⟩) (Spec.map _ _))) (by
      erw [← Hom.comp_apply, u.SpecMap_appLE_fromSpec _ v, Hom.comp_apply, v.fromSpec_primeIdealOf,
        a]
      exact instDescendsAlongSchemeSmoothMinMorphismPropertySurjectiveFlatQuasiCompact.1
        (isPullback_fiberToSpecResidueField_of_isPullback (.paste_vert (.of_hasPullback ..)
        (.of_hasPullback _ t)) (id (closedPoint k))).flip (by and_intros <;> infer_instance)
        (of_isPullback (.of_hasPullback ..) (comp_mem _ _ _ inferInstance ((pullbackAddObj
        t).of_chart _ (Opens.ι _) ((pullback.snd _ t).dense_smoothLocus_of_perfectField
        |>.nonempty_iff.2 (exists_preimage_pullback x _ a).nonempty).to_subtype (by
        simp [← smoothLocus_eq_top_iff, ← preimage_smoothLocus_eq])))))))).1))))
    fun m hm ↦ m.cast_smul_eq_nsmul O (𝟙 A) ▸ s.2.surjective _ _ fun z ↦ congr($(q m _ ((m⁻¹
    : ℂ) • z.2)).1).trans (by simp [← smul_assoc, hm]), ‹_›, (.mk' _ <| hm ·), rfl, q⟩ <;> exact
    IsSeparatingFamily.hom_ext ‹_› (by simp +zetaDelta [← hm, q, ← assoc, Hom.add_def,
    AddMonObj.add] <;> grind)

unseal ThetaObject.groupScheme ThetaObject.toFamily in
/-- Let S be reduced, locally Noetherian, embedded over R (Spec R → Spec O_E mono, β̄ − β and
|T| units) by systems c lifting level coordinates of theta tori x_k at points η_k over
Φ_{v₀}, finitely many dense. Under cl (`IsCutOutAt`) and cv, S carries a family
modelled on x_k at η_k.

Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). -/
theorem exists_thetaFamily_of_points {E} [Field E] [CMBase E] {D : PEL E} {R} {π : S ⟶ Spec R}
  {φ : 𝓞 E →+* R} (hd : Mono (specMap φ)) (ho : ∀ i c, (preimage (η i ≫ π ≫ specMap φ)).hom c = Φ v₀
  c.val) {g ℓ : κ → _} {c : D.levelTorsion → LineBundle S D.T} {x : ∀ k, ThetaTorus D (g k) (ℓ k) V}
  (hc : ∀ ω, (c ω).IsLinearSystem) [Fintype D.levelTorsion] (hπ : (pi c).IsProjEmbedding π) (hx :
  ∀ i ω, (c ω).IsHomogCoords (η i) ((x i).thetaCoord · ((x i).torsionLift ω))) (hβ :
  IsUnit (φ (star D.β - D.β))) (hT : IsUnit (Nat.card D.T : R)) (cl : AllSpecializeTo S fun t ↦ ∃ 𝔭,
  IsCutOutAt D.r D.i (thetaRanks D.T D.r) c t 𝔭) (cv : ∀ t s, ∃ o, ∀ (l : D.T) k, l + k ∈ [o, -o,
  s - o] → t ∈ (c ⟨l, D.T_le_levelTorsion l.2⟩).opens k) : ∃ X : ThetaFamily D S (π ≫ specMap φ),
  ∀ i, ∃ m : TorusModel (X := X) (η i) (x i).toPeriodMap, m.θ = fun μ v ↦ (x i).thetaCoord v μ := by
  have u := @Valuation.one_apply_le_one ℂ NNReal
  have ⟨A, N, e, hN@⟨hn, _, _⟩, _, hl, he, red, s₁⟩ := exists_flat_closure j hη hc
    (Nat.le_of_lt D.three_le_r) D.degree_spec.1 (x · |>.thetaCoord_vector_ne_zero)
    (fun i ↦ have k z : IsIntegralCoords _ fun _ ↦ ⟨_, u _⟩ := ⟨1, by
                                simpa using (x i).thetaCoord_vector_ne_zero z⟩
    (x i).isCutOutAt_reduction (φ :=
      algebraMap ..) (by tauto) (x i).hasGoodReduction_trivial k (fun _ ↦ k _) (hx i)) cl
  have s₀ : IsSeparatingFamily fun i ↦ (toUnit (Over.mk (η i))).1 := ⟨‹_›, hη.of_comp⟩
  obtain ⟨s₂, ⟨a, hA, h₁⟩, b, -, h₂⟩ := s₁.prod hη s₁.1 (he ·.1), D.exists_padding
  choose σ hσ hσ' using (s₀.exists_map_of_coords (hW := hc ·) hN (hx · _) (hl · _))
  -- Riemann's relation has regular coefficients where suitable theta constants are units
  have H (a : Fin (D.r - 3) → 𝓞 E) (c : 𝓞 E) (h : star c * c + 3 + ∑ l, star (a l) * a l = D.r)
    (ψ := fun c : _ × _ ↦ ite (c.1 = 1) (fst ..) (ite (c.2 = 1) (snd ..) (toUnit _ ≫ σ 0))) (b := by
    simp +zetaDelta [← comp_left, -lift_left, hσ, hl, hA]) :=
    let P b := paddingTuple (cond b a 1) (cond b c 0)
    have q b :
      IsRiemannTuple (P b) D := by cases b <;> simp [IsRiemannTuple, P, D.three_le_r, ← h] <;> ring
    (exists_isLinearSystem (fun b a ↦
      ((x a.1.1).thetaProduct (doubledCoeffs (P b) (P !b)) · a.1.2 a.2)) s₂ (.pi fun l ↦ hn.pull
    (ψ (doubledCoeffs (P false) (P true) l)).1) (forall_imp (fun _ ↦ .pi) b) fun b μ s ↦
    let y := ∑ l, star (P b l).1 • μ (.inr l) - ∑ l, star (P (!b) (.inr l)).1 • μ (.inl (.inr l))
    (cv _ y).elim fun o a ↦ let ν := Sum.elim (cond · (y - o) o) (μ ∘ .inl ∘ .inr)
      ⟨_, by exact ⟨⟨a 0 _ (by simp), a 0 _ (by simp)⟩, ⟨⟩⟩, fun q ↦ Sum.elim (μ ∘ .inr - (·.1 • q)
        ∘ P b) (ν + (·.1 • q) ∘ P !b), _, ((((hc 0).mul (hc 0)).1 (o, y - o) (μ (.inl (.inl true)),
    μ (.inl (.inl false)))).1.mul (isRegularOn_ofSection ((hT.map (toSpecΓ R ≫
        π.appTop).hom).unit⁻¹.1 * ↑(D.rTorsion.relIndex D.T).sqrt))).pull (A ⊗ A).hom, fun ⟨⟨i, u⟩,
        v⟩ U ↦ by simp [ofSection_eq, hx .., by simpa [hx ..] using U, P, ν, ↓Over.w, mul_assoc,
        ← by simpa [P, ν, mul_assoc] using (x i).riemann_relation (w := u) (q b) rfl (q !b) (μ :=
        μ ∘ .inr) (μ' := ν) (by simp [ν, y, P]) v, mul_left_comm ((x i).thetaCoord o 0)⁻¹]⟩).elim
      fun _ H ↦ (s₂.exists_map_of_coords H.1 (isProjEmbedding_pi _ (fun _ ↦ hN) (Pi.hom_ext _ _))
      H.2.1 fun z ↦ .pi (t := (Pi.lift fun k ↦ e _ _).1) fun k ↦ by
      simpa [← comp_left] using hl _ _).imp fun _ k ↦ And.intro (k.1 ⟨⟨·, ·⟩, ·⟩) (k.2 ▸ H.2.2)
  obtain ⟨g, hg, -⟩ := H a (-1) (by simp [← h₁])
  let μ k := g ≫ Pi.π _ (.inr (.inr k))
  choose f q using (Submodule.mem_span (x := ·) |>.1 (hA.ge ⟨⟩) (AddSubgroup.ofSub {d | ∃ f, ∀ i a,
    e i a ≫ f = e i ((x i).intAction d a)} ⟨1, 𝟙 _, by simp⟩ fun _ ⟨f, h⟩ _ ⟨k, l⟩ ↦ ⟨lift k f ≫ μ
    (.inl true), by simp [*, μ, ← assoc, neg_add_eq_sub, sub_eq_add_neg]⟩).toIntSubmodule
    fun | _, ⟨l, rfl⟩ => ⟨lift (𝟙 A) (𝟙 A) ≫ μ (.inr l), by simp [μ, hg, ← assoc]⟩)
  obtain ⟨_, _, e, rfl, hA⟩ := exists_isAbelianScheme j hη he s₁ red
    q (μ (.inl false)) (σ 0) (by simp [μ, hg, ← assoc]) (by simp [hσ])
  let ψ (c : 𝓞 E × 𝓞 E) := c.1 • fst A A + c.2 • snd A A
  have G i l h := by simpa using (OverMorphism.ext (hN.eq_of_isHomogCoords (by simp)
    (funext ((x i).thetaCoord_mem_thetaSpace · |>.2 l h 0) ▸ hl i _)
    ((hl i 0).smul (by simp [(x i).isAppellHumbert_periodLattice.ne_zero h]))) :)
  have w : D.HasClassLaws N.picClass := by
    simp_rw [PEL.HasClassLaws, Pic.ParallelogramLaw, ← forall_and]
    intro T y z
    have w {c a} h (y z : T ⟶ A) := (H a c h ψ).elim fun g k ↦ by
      simpa -implicitDefEqProofs [ψ, fun l ↦ (s₂.hom_ext (by simp [*, ← assoc]) : g ≫ Pi.π _ l =
        ψ (doubledCoeffs (paddingTuple a c) (paddingTuple 1 0)
        l)), -lift_left, ← pull_comp, ← comp_left] using (congr($(k.2).pull (lift y z).1))
    have := congr(($(w h₁ z 0) - $(@w (-1) a (by simp [← h₁]) z y), $(w h₂ y 0) - $(w h₂ y z),
      $(w h₂ z 0) - $(@w (-star D.β) b (by simp [← h₂, mul_comm]) z z),
      $(w h₁ y 0) - $(w h₁ y (star D.β • z))))
    simp [Pic.pairing, Pic.atPoint, sub_smul,
      D.star_beta] at this ⊢; clear * - this; grind [sub_eq_add_neg]
  have hp i := isGroupBaseChange_counit (A := A) (η i)
  let L i : (.mk (η i) ⟶ A) →ₗ[𝓞 E] _ := ((hp i).pointEquiv (T := 𝟙_ _)).symm.1
  have H i u : (L i u).1 = (lift u (𝟙 _)).1 :=
    pullback.hom_ext (by simpa using! (hp i).1.lift_fst ..) (by simpa using! (L i u).w)
  have U i d h := by refine ((x i).exists_uniformisation_of_dense d h (hN.of_isPullback (hp i).1) ?_
    (.comp (L i) (e i)) ?_ ?_ ?_) <;> simp +contextual [Pic.ParallelogramLaw,
    w.1 _, ↓(hp _).atPoint_picClass_pull, H, hl, G]; apply he
  have dim := smoothOfRelativeDimension_of_fibres s₁.2 (U ·.1 · · |>.choose_spec.2.2.2)
  choose u t using (U · (abelianDim E D.Index) (by simp; infer_instance))
  let ς :
    D.levelTorsion →ₗ[𝓞 E] _ := by use! σ <;> exact fun a b ↦ s₀.hom_ext fun i ↦ sub_eq_zero.1 (by
              simp [hσ, hA, PeriodMap.torsionLift, intAction, ← toRealVectors_smul, ← map_add,
                ← map_sub]; exact G i _ ⟨_, by simp, rfl⟩)
  refine ⟨{
    A := A, N := N, class_laws := w, relative_dim := dim, embeds := hN, η := ς
    theta_law t T _ _ q h := by
      as_aux_lemma =>
        have L i l k := by simpa [thetaShift_apply, ← eq_inv_mul_iff_mul_eq₀,
          ← PeriodMap.torsionLift.eq_1]
          using ((x i).thetaShift_thetaCoord (s := l) (frameTorsionClass_ratLift _) k)
        choose W r hr hW v using fun l m ↦ ((cv _ m).elim fun o H ↦ ⟨_, _, (((hc _).mul (hc 0)).1
          (-o - l, m - o) (m - o - l, -o)).1, landsIn_iff_mem.2 ⟨H l _ (by simp), H 0 _
          (by simp)⟩, by simp +contextual [hx .., sub_eq_add_neg, field, zero_add (_ : V) ▸ L ..]⟩ :
          ∃ W r, IsRegularOn r W ∧ LandsIn t W ∧ ∀ i, LandsIn (η i) W → r _ (η i) =
          (x i).bicharacter (torsionLift_mem ..) m)
        have F f g (h := by simp +contextual [v, bicharacter_neg_eq_swap]) (a : IsRegularOn f _ ∧
          IsRegularOn g (iInf W.uncurry) :=
          by simp +contextual [IsRegularOn, hr _ _ _]) := a.elim s₀.pointFn_ext h _ t (by simp [hW])
        refine ⟨fun s ↦ ⟨(r s · _ t), F _ 1, fun _ _ ↦ F _ (_ * _)⟩, fun s u ↦ F .., fun u s ↦
          exists_isSectionLift_coordSection _ _ fun l m B y a b ↦ ⟨⟨u.1 • l - s, by simp [N.5,
          landsIn_preimage.1 a, ↓H0_smul, smul_smul, AddChar.val_isUnit, IsUnit.map,
          -AddChar.coe_mk]⟩, fun j ↦ ?_⟩, fun s h ↦ H0_ext fun _ _ _ _ a ↦ s₁.pointFn_ext
          (hn.1 ..).1 (hn.1 ..).1 (by simp +contextual [hl .., thetaCoord_eq_of_mem_lagrangian _ s
          h]) _ _ a, by simpa using hT.map (preimage (t ≫ π)).hom,
          fun s h ↦ by simpa using! F (∑ l : D.lagrangian.addSubgroupOf D.T, r s l ^ 2) 0 (by
          simp +contextual [v]; exact fun i _ ↦ (((x i).bicharacter _ ^ 2).compAddMonoidHom
          (AddSubgroup.subtype _)).sum_eq_zero_iff_ne_zero.2
            (h ∘ (x i).mem_lagrangian_of_bicharacter_sq s ∘ DFunLike.congr_fun))⟩
        let f := translation (σ ⟨s, D.T_le_levelTorsion s.2⟩)
        have w := by simpa [f, ← h.translation_comp] using h.smul_id_comp u.1 =≫ f.1
        have R m := ((hr s m).pull A.hom).mul (hn.1 l (u.1 • (s + m))).1
        choose _ H using (x · |>.exists_thetaCoord_sign_smul u)
        simpa [↓H0_smul, ← hr _ _ _, hW, f, ← w, -comp_add] using! s₁.pointFn_ext ((R j).mono
          inf_le_left) (((R m).mul ((hn.1 ..).1.pull ((u.1 • 𝟙 A) ≫ f).1)).mono inf_le_right) (by
          simp +contextual [v, hl .., L, H, ← comp_left, field, f, hσ, ← map_zsmul, ← map_add])
          _ (y ≫ q.1) (by simp [f, ← w, LandsIn.comp, hW, -comp_add]; tauto)
    signature b _ s _ := Spec_stalkClosedPointTo_fromSpecStalk
      s ▸ by as_aux_lemma => simpa using (exists_isLieChart dim _).imp fun V ⟨z, m, J⟩ ↦ ⟨z, _,
      J rfl, .of_points (stalk_eq_zero_of_dense hη) (fun ⟨i, _, E⟩ ↦ (x (j i)).4.elim fun ε he ↦
      ((u _).hasSignature_iff (F := (x (j i)).intAction) (by simp
      [t, ← hA]) (J E) (hp _) (x (j i)).isPeriodMap.finrank_eq_abelianDim).2 (by
      use ε.symm ((1, 0), 0), ?_, ?_, Φ v₀ (star D.β.val - D.β) • .fst .. ∘ₗ .fst .. ∘ₗ ε.1 <;>
        simp +contextual [by simpa [← E] using ho (j i), ← ε.injective.eq_iff, D.emb_beta_eq_of_ne,
        fun a z ↦ by simpa using congr($(he a) (ε z)), Prod.ext_iff, sub_mul, map_smul])) _
      (.map _ (by simpa [← assoc] using hβ.map (preimage
        (S.fromSpecStalk (s (closedPoint _)) ≫ π)).hom))⟩
    eq_of_list_eq _ _ h b := hπ.ext (by simpa [← hσ'] using! congr(pi $(funext b))) (hd.1 _ _ h) },
    fun i ↦ ⟨⟨ho i, _, _, _, (t i).1, fun c w ↦ by simpa [*, intAction] using! ((L i).map_smul
    c (e i ((x i).Q w))), (by simpa [t] using! congr(L i $(hσ · i))), (t i).2.2.1⟩, rfl⟩⟩
end

section
/-! Known result: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration). Here a torus with polarisation prime to p is assumed to have arbitrarily expanding
non-unit multipliers dividing a power of p, prime to their conjugates, whose conjugates have unit
determinant on the Lie algebra. Then the sup of a valuation of theta values at torsion points is
multiplicative. Source: K.-W. Lan, Elevators for degenerations of PEL structures, Math. Res. Lett.
18 (2011); R. Kottwitz, Points on some Shimura varieties over finite fields, J. Amer. Math. Soc. 5
(1992), §5 (division algebra case); for the CM case B. Conrad, Semistable reduction for abelian
varieties (notes), Prop. 6.3, after Serre and Tate, Ann. of Math. 88 (1968).

This file: Theta tori over good places have multiplicative sup norm; degree and level are units. -/

open NumberField IsLocalRing Valuation LinearMap Ideal IsPrime valuationSubring PeriodMap

/-- Good reduction of a theta torus x: if Φ_{v₀} maps O_E into the valuation ring of v, over a
prime good for D, then the v-adic sup norm on torsion points is multiplicative
(`HasGoodReduction`), and r and |T| are v-units.

Known result: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration). -/
lemma ThetaTorus.hasGoodReduction_and_val_card_eq_one {E} [Field E] [CMBase E] {V}
  [FinComplexSpace V] {D g ℓ} (x : ThetaTorus D g ℓ V)
  {v} {ρ : 𝓞 E →+* v.valuationSubring} (B : ∀ c, ρ c = Φ v₀ c.val) (hw : D.IsGoodAt
  (comap ρ (maximalIdeal _))) : HasGoodReduction x.B x.multiplier v D.r ∧ v (Nat.card D.T) = 1 := by
  have ⟨⟨hr, hT⟩, p, b, pp, pw, bw, cb, _, w, ww, pw', q⟩ := hw
  obtain ⟨⟨t, tw, tn⟩, n⟩ := Set.not_subset.1 (ww ∘ w.isMaximal.eq_of_le ne_top'),
    notMem_of_isCoprime_of_mem cb bw
  simp [(integers v).isUnit_iff_valuation_eq_one, B] at hr hT tn n
  let H := (2⁻¹ : ℂ) • (x.B + x.B.pullForm (Complex.I • 1))
  have : riemannForm H = x.B.riemannForm := by ext; simp [riemannForm, H, re_symm]; ring
  use ⟨x.hasGoodReduction_trivial.1, by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice], hr, x.hasGoodReduction_trivial.4,
    hasMultiplicativeNorm_of_expanding (B := H) ⟨x.intAction_mem_periodLattice, fun y z ↦ by
    simpa [H, Complex.ext_iff, re_symm, add_comm] using x.re_symm (Complex.I • y) (Complex.I • _),
    (by simpa [H, riemannForm, field] using x.isPosRiemann.1 · ·), by simp [H, ← adjoint],
    this ▸ x.isAppellHumbert_periodLattice.le_dualLattice, D.star_beta⟩
    (hw.1.2 <| mem_of_dvd _ ·.natCast pw) (by grind [dualLattice_periodLattice,
    card_nsmul_mem_periodLattice, RealComplexForm.dualLattice]) pp (by simp_all
    [v.mem_maximalIdeal_iff]) ((Continuous.tendsto' (by simp [continuous_clm_apply]; fun_prop) _ _
    x.isPeriodMap.complexMul.2).frequently (Metric.nhds_basis_ball.frequently_iff.2 fun r r0 ↦
    have ⟨a, ⟨k, ha⟩, nu, A⟩ := exists_pow_eq_span_inv_lt w.one_lt_q r0
    have K {y} h := mem_span_singleton.1 (ha.le (pow_mem_pow (x := y) h k))
    have h σ {y} h (e : v (σ y.val) = 1) := (@K y h).elim fun c k ↦
      have I c := (integers (v.comap σ)).mem_of_integral c.2.tower_top
      eq_one_of_one_le_mul_left (a := v (σ a)) (I a) (I c) (by simp [← map_mul, ← k, e])
    ⟨(Φ · (star a))⁻¹, by simp [pi_norm_lt_iff, *], star a,
      k, by simp [intAction, ← x.Q.eq_symm_apply,
      funext_iff, (by aesop : a ≠ 0)], by simpa, by grw [star_star, ← starRingAut_apply, K q]; simp
      [cb.symm.pow], by simpa using map_dvd starRingAut (K pw'), x.4.rec fun ε _ ↦ by
    simpa [← det_conj _ ε, det_prodMap, piMap, det_pi, h _ q, *, h _ tw, Subtype.forall'.1
      D.emb_beta_eq_of_ne] using .inl (h (star _) q (by simpa))⟩))⟩
end

section
/-! Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). Here the base is the closure of theta values at level points of PEL tori rather than being
cut out by quartic relations, the theta group is odd, and residue characteristic 2 is allowed.
Flatness comes from constant Hilbert ranks, and the group law and action come from an r-fold Riemann
theta relation. Source: D. Mumford, On the equations defining abelian varieties II, Invent. Math. 3
(1967) 75-135, section 6; theta groups in part I, Invent. Math. 1 (1966).

Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation (known
result; see Lib.Shimura.IntegralModel.ModelExistence).

This file: Analytic families immerse, finitely many meet every point; covers have only the expected
points. Universal theta family over a smooth projective base, uniformised by balls. -/
seal Finset.univ Finset.sum Finset.prod

open ThetaObject Set AlgebraicGeometry Cardinal CategoryTheory Classical Filter IsLocalRing
  NumberField ModuliPoint Submodule LocallyOfFiniteType Over TorusModel
variable {E} [Field E] [CMBase E] {D : PEL E} {R ν} [NeZero ν] {U :
  UniversalFamily D R} {J} [Finite J] {γ : J → _} (C : U.GraphClosure γ ν) {f : AnalyticFamily D}

/-- Balls immerse. Let objects x_b of X be modelled with the period maps of the analytic family
f. If b lies in f.U and the uniformisation (b', z) ↦ ψ(b', z) is holomorphic at every (b,
z), then b' ↦ x_b' is a holomorphic immersion at b. -/
lemma AnalyticFamily.holomorphic_immersive {Z τ} {X : ThetaFamily D Z τ} {x : _ →
  ThetaObject X _} (m : ∀ b, (x b).TorusModel (f.torus b).toPeriodMap) {b}
  (h₀ : b ∈ f.U) : let ψ q := atGeneric (m _).uniformisation.expMap q.2 ≫ (x q.1).toFamily.left
  (∀ z, HolomorphicAt ψ (b, z)) → IsHolImmersionAt x b := by
  intro ψ H
  use by simpa [ψ] using ((H 0).comp (g := (·, _)) (by fun_prop)).comp_hom (hom _), fun v hv ↦
    f.eq_zero_of_linear _ h₀ _ fun _ ↦ sub_eq_zero.1
    (((m _).uniformisation.immersive_of_isPullback (x _).isGroupBaseChange.1 0).2 _ ((isJet_comp_iff
    (by fun_prop) (H _)).2 (isFirstOrderConst_iff.2 fun U r k ↦ ?_)))
  obtain ⟨d, a, L, c⟩ := f.analyticAt _ h₀,
    (H 0 (PointFn.isRegularOn_ofSection r) k).imp_right (·.fderiv.neg.differentiableAt)
  set i : _ →L[ℂ] BallBase D.Index × BallFibre E D.Index := .inr ..
  have R w : fderiv ℂ (PointFn.ofSection r _ <| ψ ·) (b, 0)
      (i (fderiv ℂ (f.torus · |>.Q ((f.torus b).Q.symm w)) b v)) = L (i w) (v, 0) := by
    induction eq_top_iff'.1 (m b).uniformisation.3.2.1 w using span_induction
    any_goals simp (disch := fun_prop) [fderiv_fun_add, fderiv_fun_const_smul, *]
    by_contra
    apply (tendsto_natCast_atTop_cobounded.eventually (tendsto_inv₀_cobounded' (((c.hasLineDerivAt
      _).clm_apply ((hasFDerivAt_id _).hasLineDerivAt _)).neg.eventually_ne
      (by simpa [add_neg_eq_zero])))).frequently
    filter_upwards [tendsto_const_nhds.prodMk_nhds (tendsto_inv_atTop_nhds_zero_nat
      (𝕜 := ℂ).zero_smul_const _) a, eventually_ne_atTop 0] with n u hn
    simpa [i] using isFirstOrderConst_iff.1 ((H _).isFirstOrderConst_of_nsmul X.relative_dim hn
      ((isJet_comp_iff (.prodMk (hasFDerivAt_id _)
      ((d ((f.torus b).Q.symm _)).differentiableAt.hasFDerivAt.const_smul (_ : ℂ)))
      ((H _).comp_hom _)).1 (cast (by simp_all [← (x _).isGroupBaseChange.nsmul_id_comp,
      ← comp_left_assoc, ← map_nsmul, (Uniformisation.eq_zero_iff ..).1, ← Nat.cast_smul_eq_nsmul ℂ,
      (f.torus _).Q.eq_symm_apply, TorusModel.lattice_eq, ψ, mem_classLattice,
      ← (x _).isGroupBaseChange.pullSection_comp]) (hv.comp_hom (X.η 0).1)))) U r u
  simp [*]

/-- For 𝔪 ≠ 0 there are finitely many analytic families f_k of theta tori such that every point
is isomorphic at level K(𝔪) to a point of some f_k lying over the domain of f_k. -/
lemma ModuliPoint.exists_finite_reps D ν {𝔪} (h : 𝔪 ≠ 0) : ∃ (κ : Type) (f : κ → AnalyticFamily D),
  Finite κ ∧ ∀ a : ModuliPoint E _ ν, ∃ k, ∃ p ∈ (f k).U.1 ×ˢ .univ, ∃ z,
  a.IsLevelIso (levelGU _ 𝔪) z ((f k).ballPoint 0 p) := let φ := _ ∘ x
  (axiomOfChoice (exists_ball_family <| rangeSplitting φ ·)).elim fun f H ↦
    ⟨_, f, (finite_isSignedFrame_classes
    (isOpen_congruenceGL_span h)).subset fun _ ⟨a, e⟩ ↦ ⟨_, ⟨_, a.isSignedFrame⟩, e⟩, fun a ↦
    have ⟨_, ⟨z, rfl⟩, _, h, e⟩ := DoubleCoset.eq.1 (apply_rangeSplitting φ ⟨_, a, rfl⟩).symm
    ⟨_, ((H _).2.2.1 ⟨_, _, realVecAction z ∘ a.P, a.isSignedFrame.mul z h.1, a.isReflection.conj _⟩
      e.symm).imp fun _ ↦ .imp_right (⟨z, · ▸ by simpa [isLevelIso_iff, mul_assoc]⟩)⟩⟩

attribute [local simp] act ratConj

/-- For an analytic family f of theta tori, the map sending p = (b, periods) to the complex
point, with its 𝔪-torsion, of the Kuga–Sato variety (fibre power of the universal abelian
scheme) is a holomorphic immersion at every p with b in the domain of f. -/
lemma UniversalFamily.isHolImmersionAt_datumPoint {P : Fin ν → _} {𝔪} p (hp : p.1 ∈ f.U) :
  IsHolImmersionAt (f.ballPoint P · |> U.datumPoint 𝔪 |>.left) p := by
  obtain ⟨I, _⟩ := f.holomorphic_immersive (U.model ⟨f, ·⟩) hp (U.holomorphic f _ hp),
    (f.analyticAt _ hp · |>.contDiffAt.fst'')
  simp_rw [← IsPt.eq_datumPoint (a := f.ballPoint ..) ⟨U.model (f, _), rfl⟩]
  refine (fun H ↦ ⟨H, fun (_, _) hv ↦ ?_⟩) (HasGermAt.of_jointly_mono ((Over.map U.base.hom).map <|
    Limits.Pi.π _ ·) (fun e ↦ OverMorphism.ext
    (fibrePower_ext_iff.2 ⟨by simpa using congr($(e ofNonempty).1 ≫ U.family.A.hom), (congr($(e
    ·).1))⟩)) (by rintro ⟨⟩ <;> simp <;> apply (U.holomorphic f _ hp _).comp (g :=
    (Prod.fst ·, _)) (ContDiffAt.analyticAt _) <;> (try simp) <;> fun_prop) (by simp; rfl))
  cases I.2 _ ((isJet_comp_iff hasFDerivAt_fst I.1).1
    (by simpa using hv.comp_hom (U.family.fibrePower _).hom))
  simpa [funext_iff] using fun i ↦ (Uniformisation.immersive_of_isPullback _
    (ThetaObject.isGroupBaseChange _).1 _).elim fun h k ↦ k _
    ((isJet_comp_iff ((hasFDerivAt_apply i p.2).add_const _) h).1 (by simpa [π] using
    ((isJet_comp_iff (hasFDerivAt_prodMk_right p.1 p.2) H).2 hv).comp_hom (U.family.proj (.inr i))))

/-- For an analytic family f and vectors P, the map sending p to the complex point of the cover
C attached to the point of f with parameter p relative to P is holomorphic at every p over
the domain of f. -/
lemma UniversalFamily.GraphClosure.holomorphicAt_point P p (hp : p.1 ∈ f.U) :
  HolomorphicAt (f.ballPoint P · |> C.point |>.left) p := .of_jointly_mono _ C.hom_ext
  fun j ↦ by simpa [↓← comp_left, ↓C.point_comp_proj] using!
  (isHolImmersionAt_datumPoint (f := f.heckeTranslate _) p hp).1

/-- Every point z of the cover W is the image of the closed point under some α: Spec V → W, V a
valuation subring of ℂ, with a point b such that: whenever a morphism u sends the complex
point of b to that of a with its 𝔪-torsion, u∘α is the V-point of a (`ThetaFamily.IsPointOf`). -/
lemma UniversalFamily.GraphClosure.exists_arc z : ∃ᵉ (V : ValuationSubring ℂ) (α) (b) (ρ :
  C.W.left.residueField z →+* _), specMap ρ ≫ C.W.left.fromSpecResidueField z =
  specMap (residue V) ≫ α ∧ ∀ {𝔪 u} {a : ModuliPoint E _ ν}, C.point b ≫ u = U.datumPoint 𝔪 a →
  U.family.IsPointOf 𝔪 a (α ≫ u.1) := C.exists_level_point_eq.elim fun m M ↦ by
  obtain ⟨_, _, f, _, H⟩ := U.isDedekindDomain, exists_finite_reps D ν (by simp : m.1 ≠ 0)
  choose b _ G using fun i ↦ exists_generic_member (hom _) ((f i).U.2.prod (by simp))
    ((f i).2.prod isConnected_univ) (C.holomorphicAt_point 0 · ·.1)
  obtain ⟨i, V, α, l, rfl⟩ := @_root_.exists_arc _ _ (isLocallyNoetherian (hom _)) _ _
    (C.isSeparatingFamily.2.induction_on · (by simp) (H · |>.elim fun c ⟨q, h, _, r⟩ ↦ M r
    ▸ (G c q h).mem_closed (by simp) (subset_closure (mem_range_self c)))) z
  exact (comap_closedPoint (residue _)).rec ⟨_, α, _, _, (Scheme.SpecToEquivOfField ..).3 (specMap
    _ ≫ α), fun h ↦ .of_generic (((reassoc_of% l) _).trans congr($h.1) ▸ isPointOf_datumPoint)⟩

/-- Let W be the closure `UniversalFamily.GraphClosure` for a finite family γ, with ν ≥ 1. If a
morphism c from W sends each point [a] to `UniversalFamily.datumPoint` of a for 𝔪 = 1, every complex
point of W over R is some [a]. -/
lemma UniversalFamily.GraphClosure.point_surjective {c} (hc : ∀ a, C.point a ≫ c =
  U.datumPoint 1 a) : C.point.Surjective := fun t ↦ by
  have ⟨z, φ, hφ, _⟩ := exists_countable_residue_point (hom _) t.1
  have ⟨V, α, b, j, hα, H⟩ := C.exists_arc z
  obtain ⟨⟨φ, rfl⟩, e, ho⟩ := exists_ringHom_complex_extend j.injective φ.injective
    (mk_quotient_le.trans (mk_set_le _)), H (hc _)
  have hφ := reassoc_of% (by simp_all [specMap] : specMap (φ.comp (residue _)) ≫ α = t.1)
  choose x p using fun {y} ↦ exists_isPullbackAlong (X := U.family) (specMap (φ.comp (residue V))) y
  choose f w using fun {y} ↦ FullStructure.exists_pullback (@p y)
  have ⟨g, ℓ, d, Y, m, v, s₂⟩ := exists_torusModel (f e.fullStructure) (by simp [baseHom, ← p, hφ,
    reassoc_of% (by simp [← c.w, reassoc_of% ho] : ‹ThetaObject ..› ≫ hom _ = α ≫ hom _)]; tauto)
  choose P G using (@id m.π.Surjective (m.uniformisation.surjective.comp Y.Q.surjective) <|
    p.isGroupBaseChange.pullSection <| e.π ·)
  use ⟨_, _, P ∘ b.P, ⟨_, Y.isSignedFrameFor⟩, s₂⟩, C.hom_ext fun i ↦ (γ i).2.2.1.elim fun _ q ↦ ?_
  obtain ⟨⟨_ | _, rfl⟩, f', h⟩ := q.2.exists_intCast_eq (γ i).2.2,
    H (C.point_comp_proj _ i) <;> simp [↓Int.cast_pos] at q
  obtain ⟨o, χ, _, _, l, _⟩ := exists_isogeny 1 (by simp) e f' (by simp) (γ i).2.2.2 (by simpa)
  obtain ⟨⟨ψ, a, _, K⟩, g₀, ℓ₀, d, Y', m', u, s⟩ :=
    p.isGroupBaseChange.exists_hom_baseChange p.isGroupBaseChange (𝟙 _) χ,
    exists_torusModel (f f'.fullStructure) (by simp [p.baseHom_eq_comp, o, ← m.baseHom_eq])
  exact (exists_matrix_of_hom m m' ψ q.1.ne' (by simpa [p.lineBundle_eq_pull] using!
    (congr((ThetaObject.lineBundle _).picClass.pull $(a (𝟙 _)).1).trans congr(($l).pull _)))).elim
    fun z ⟨F, _, _⟩ ↦ (C.point_comp_proj ..).trans (OverMorphism.ext ((isPointOf_datumPoint.eq_iff
    (b := ⟨_, _, (realVecAction z <| P <| b.P ·), ⟨_, Y'.isSignedFrameFor⟩, s⟩) ⟨m', by
    rw [comp_left, ← hφ, h]; simp [fibrePower_ext_iff, ← p.comp_toFamily, ↓← F,
      IsGroupBaseChange.pullSection_comp_assoc, *]⟩).2 ⟨z, by erw [isLevelIso_iff, ← mul_assoc,
    ← (Units.ext (funext₂ fun a b ↦ sub_eq_zero.1 (eq_zero_of_forall_mul_integral
    fun x ↦ by simpa [mul_comm, mul_sub] using torsionClass_eq_iff.1 (m'.fullStructure.injective
    (.trans (by simp [*]) (torsionPoint_comp _ _ F (Pi.single b x))) :
    torsionClass (x • (γ i).2.1.2.col b) = _) a)) : _⁻¹ = _ * g)]; simpa⟩))

open And LineBundle PeriodMap ProjSpace Ideal.IsPrime

/-- Let D be PEL data and R ⊂ E a localisation of O_E whose maximal ideals lie over primes good
for D (`PEL.IsGoodAt`). Then a universal theta family `UniversalFamily` exists: its base is
projective and smooth over R, with dense, holomorphically modelled complex objects.

Known result: Moduli of abelian varieties by theta values (theta-null embedding, universal
family). -/
lemma nonempty_universalFamily {E} [Field E] [CMBase E] {D M} {R :
  Subalgebra _ E} [IsLocalization M R] (hM : M ≤ nonZeroDivisors (𝓞 E)) (hR : ∀ m, m.IsMaximal →
  D.IsGoodAt (.comap (algebraMap _ R) m)) : Nonempty (UniversalFamily D R) := by
  obtain ⟨_, _, ι, f, _, rep⟩ :=
    @Fintype.ofFinite D.levelTorsion (finite_torsionBy ⟨_, by simp [D.level_ne_zero]⟩),
    IsLocalization.isDedekindDomain _ hM R, ModuliPoint.exists_finite_reps D 0 D.level_ne_zero
  choose t k ht using fun (ω : D.levelTorsion) (a : AnalyticFamily D × _) ↦
    exists_isHomogCoords (v := ((a.1.torus a.2).thetaCoord · ((a.1.torus a.2).torsionLift ω)))
    (specOver R ℂ).hom (Function.ne_iff.1 (thetaCoord_vector_ne_zero _ _)).choose_spec.isUnit
  have Z {B} (y : B → _) :=
    Set.univ_nonempty.imp fun (C : ReducedClosure (Over.homMk (V := Over.mk _) _ <|
    k · <| y ·)) _ ↦ let c ω := ((hyperplaneBundle _).pull Limits.prod.fst).pull (C.proj ω).1
    have := HasProjEmbedding.pi C.incl (h := fun _ ↦ ⟨isProjEmbedding_projSpace⟩)
    have A : (LineBundle.pi c).IsProjEmbedding _ ∧ ∀ a ω, (c ω).IsHomogCoords (C.point a).1 _ :=
      ⟨isProjEmbedding_pi _ (fun _ ↦ isProjEmbedding_projSpace) C.hom_ext, by
      intros; rw [IsHomogCoords.pull_iff, ← Over.comp_left, C.point_comp_proj]; apply ht⟩
    have := LocallyOfFiniteType.isLocallyNoetherian C.W.hom
    intro A fun {ι} (j : ι → B) [Finite ι] hd ↦ have H z := ((Ideal.exists_le_maximal _ (C.W.hom
      z).2.1).elim fun m h ↦ (C.W.hom.isClosedMap.specializingMap ((PrimeSpectrum.le_iff_specializes
      _ ⟨m, h.1.isPrime⟩).1 h.2)).elim fun w k ↦ Exists₃.imp (fun _ O a ↦ imp_right fun e ↦
      intro (e.symm.subst k.1) (congr(D.IsGoodAt ($(Spec.map_preimage (a ≫ C.W.hom ≫ (specOver (𝓞 E)
      R).hom)) (closedPoint _)).1).mpr (hR _ (by erw [e, k.2]; tauto)))) (exists_arc _ hd w))
      intro H ((forall_and.1 (H · |>.elim fun i ⟨v, α, h, l, d⟩ ↦ by
    -- the closed point of an arc through the point of x
    let x := (y (j i)).1.torus (y (j i)).2
    obtain ⟨hx, hc, G⟩ := h ▸ A.2 _, ?hc,
      x.hasGoodReduction_and_val_card_eq_one (by simpa [← h] using ?o (j i)) d
    choose i hi using (c · |>.exists_landsIn α)
    have n ω := ((hx ..).1.1 ((hi ω).comp _)).ne_zero
    have e ω j : Subtype.val _ = _ := ((hc ω).1 ..).1 _ _ (hi ω) ▸ (hx ..).2 j (n ω).isUnit
    have R ω := funext ((hc ω).1 _ · |>.1 _ α (hi ω)) ▸ (hc ω).2 ((hi ω).comp (specMap (residue _)))
    choose m hm using fun z ↦ Finite.exists_max (v <| x.thetaCoord · z)
    rw [← comap_closedPoint (residue _)] at l; refine ⟨⟨_, _, inferInstance, _, by exact l,
      _, x.isCutOutAt_reduction residue_surjective G.1 (q := fun z j ↦ ⟨_, by simp; bound⟩) (fun z ↦
      ⟨_, fun _ ↦ rfl, m z, by simpa using (x.thetaCoord_vector_ne_zero z <| by
      simpa [·, funext_iff] using hm z)⟩) (fun a ↦ ⟨_, by simpa using! e a, i a, by simp [*]⟩) R⟩, (
      G.elim x.exists_peak · |>.imp fun o H u _ w ↦
      l.mem_open (LineBundle.opens ..).2 (landsIn_iff_mem.1 ((R ..).1.2 ?_)))⟩
    have L i := by simpa [thetaShift, valuation_multiplier_mul_bicharacter]
      using congr(v ($(x.thetaShift_thetaCoord (frameTorsionClass_ratLift u.1) i) 0))
    simpa [v.mem_maximalIdeal_iff, e, le_mul_inv_iff₀, n, ← L, zero_lt_iff] using!
      H _ w (u + _))).elim ((IsUnit.mul_iff.1 (by_contra (exists_max_ideal_of_mem_nonunits · |>.elim
        fun m ⟨e, k⟩ ↦ (hR m e).elim fun n ⟨_, _, _, _, a, c, _⟩ ↦ notMem_of_isCoprime_of_mem c
      a (by simpa using add_mem ((mem_or_mem' k).resolve_right n.2) a)))).elim
        (exists_thetaFamily_of_points j
      hd (IsPreimmersion.of_isLocalization M).instMonoScheme ?o ?hc A.1 A.2)))
  have ⟨C, ⟨emb@⟨_, _, _⟩, hx⟩, K⟩ := Z id
  have hs {f} ⦃b⦄ n :
    HolomorphicAt (C.point ⟨f, ·⟩ |>.1) b := have ⟨_, h, k⟩ := f.exists_analytic_thetaCoord n
    .of_isHomogCoords emb (fun _ ↦ Finset.analyticAt_fun_prod _ fun ω _ ↦ (h ..).comp₂ analyticAt_id
               (f.analyticAt _ n (toRealVectors (ratLift f.frame _)))) (k.mono fun _ h ↦ .pi (w :=
      (·)) (hx _ · |>.smul h))
  choose b hb G using fun i ↦ exists_generic_member C.W.hom (f i).U.2 (f i).2 hs
  -- the generic points of the finitely many balls are dense
  choose A X m hm using K (fun i ↦ (f i,
    b i)) (C.isSeparatingFamily.2.induction_on · isClosed_closure fun x ↦ by
    choose i a ha z r using rep (x.1.ballPoint 0 (x.2, 0))
    choose _ _ m _ using
      (Z ![x, (f i, a.1)]).choose_spec.2 id (ReducedClosure.isSeparatingFamily _).2
    simpa [(C.hom_ext fun ω ↦ by simpa using (Over.OverMorphism.ext (((ThetaFamily.IsPointOf.eq_iff
      (𝔪 := 1) ⟨m 0, rfl⟩ ⟨m 1, rfl⟩).2 ⟨z, levelGU_inf_one.ge r.mem_level, r.reflection_eq,
      r.sub_mem_lattice⟩ ▸ pointOf_hom :).symm.trans pointOf_hom) =≫ ReducedClosure.proj _ ω) :
      C.point x = C.point _)] using closure_mono (by simp) (G _ _ ha.1).mem_closure)
  choose i O a ha l gd using A
  refine ⟨‹_›, _, X, ⟨emb⟩, ?_, _, m, ?l, C.isSeparatingFamily.2⟩
  -- smoothness
  choose U h h' using fun z ↦
    smooth_of_immersion _ ((f _).holomorphic_immersive (m ⟨_, ·⟩) (hb _) (?l _ _ (hb _)))
    (ha z) (fun _ ↦ Over.w _) (FaithfulSMul.algebraMap_injective ..) (((f _).U.2.eventually_mem
    (hb _)).mono (G _)) fun _ τ h₁ h₂ ↦ ((m _).exists_model_over_arc (ha _)).elim fun m _ ↦
    tangent_bound h₁ (by simp [← RingHom.comap_ker, ker_residue, baseHom]; apply gd) m.fullStructure
    (m.isRigid_pullback (residue _) rfl) rfl (by simp [baseHom, reassoc_of% h₂, RingHom.comp_assoc])
  exact HasRingHomProperty.instIsZariskiLocalAtSource.of_iSup_eq_top U (top_unique fun z _ ↦
    le_iSup U z ((l z).mem_open (U z).2 (h z ⟨⟩))) h'
  -- the uniformisations are holomorphic in families
  exact fun f b h z ↦ match f.exists_analytic_thetaCoord h, (hs h).exists_isHomogCoords emb.1 with
    | ⟨_, u, v⟩, ⟨_, k, r⟩ => .of_isHomogCoords (X.embeds.mul emb) (hb := by simp; rfl) (fun _ ↦
      (u ..).mul ((k _).comp analyticAt_fst)) (((r.and v).prod_inl_nhds _).mono fun w h ↦ .mul
    (by simpa [hm] using! ((m _).hasThetaCoords.4 _).smul h.2) (by simpa [IsHomogCoords] using h.1))
  all_goals simp [c, (isLinearSystem_hyperplaneBundle.pull _).pull] <;> tauto
end
