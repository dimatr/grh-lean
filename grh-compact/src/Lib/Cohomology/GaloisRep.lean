import Lib.Cohomology.PointClass
import Lib.Cohomology.NormalizationPullback
import Lib.Cohomology.GaloisTwist
import Lib.Cohomology.CrystallineCohomology
import Lib.PadicHodge.CrystallineLimit
import Lib.GaloisRep.Lefschetz

section
/-! Part of: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).

This file: Class of the diagonal in Hodge cohomology, glued from local Grothendieck symbols. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor


open CategoryTheory MonoidalCategory Ideal Set EtaleChart
attribute [-simp] Fin.natAdd_eq_addNat IsScalarTower.coe_toAlgHom'

/-- Class of the diagonal: if X has an atlas of dimension d, some δ in Hdg^d(X × X, complement
of the diagonal) is, near each diagonal field point, the symbol [df/f], where f_i = x_i ⊗ 1
− 1 ⊗ x_i for chart coordinates x cut out the diagonal.

Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). -/
lemma exists_diagonal_class {k} [Field k] [CharZero k] {X d} : @HasAtlas k _ d X → ∃ δ : HodgeH
  (relFreeAb (offDiagonal X)) d, ∀ K z, IsField K.1 → ∃ a O, IsOpenSub (X := X ⊗ X) O ∧ (z, z) ∈ O
  K ∧ ∀ᵉ (B) (p ∈ O B), ∃ φ ψ, X.map φ (point a) = p.1 ∧ X.map ψ a.point = p.2 ∧ IsLocalSymbol δ p
  (fun _ x ↦ x.1 = x.2) (fun i ↦ φ (a.coordinate i) - ψ (a.coordinate i)) 1 := fun ⟨_, a, ha⟩ ↦ by
  choose e h using exists_eq_iff_coordinate_eq ∘' a
  let V i := away (.prod ..) (e i)
  let l {i} : _ ⟶ (V i).R := CommAlg.toAway _
  have Q {n W V} (e : locus (d := n) V = W) := hodge_excision (U := (offDiagonal X).preimage W.ι)
    (V.comap W.ι ⟨_, e ▸ V.point_mem_locus⟩ rfl).isOpenSub (e ▸ by rintro _ _ ⟨_, _, ⟨⟩⟩; tauto) rfl
  choose x E using fun i ↦
    ((Q rfl d).2 _).imp (q := (IsLocalSymbol (X := (V i).locus.toFunctor) · ⟨_, point_mem_locus _⟩
    (fun _ x ↦ x.1.1 = x.1.2) _ 1)) fun _ ↦ (⟨fun C α ↦ by simpa [span_le, -map_sub] using! ((h i _
    (l ≫ α)).trans (and_iff_right ((CommAlg.exists_toAway_comp_iff ..).1 ⟨α, rfl⟩))).symm, _, ·⟩)
  have G {i B p χ} h : IsLocalSymbol (R := B) (x i) ⟨p, χ, h⟩ .. := h.rec ((E i).map _)
  have N {K} k z : ∃ i, (z, z) ∈ (V i).locus _ := (ha K k z).imp fun i m ↦
    ((range_pointMap_prod ..).ge _ ⟨m,
    m⟩).elim fun _ E ↦ E.subst ((mem_locus_away ..).2 ((h ..).1 (E ▸ mem_diagonal z :)).1)
  refine (relFreeAb.exists_glued_class _ {A | ∃ i c, (locus c).whisker _ = A ∧ c.locus ≤
    (V i).locus} (fun _ ⟨i, c, e, h⟩ _ ⟨_, b, E, _⟩ ↦ (c.exists_locus_eq_inf b).elim (⟨i, ·, · ▸
    ⟨congr($e ⊓ $E), by order⟩⟩)) (fun _ ⟨i, c, E, h⟩ m n ↦ E ▸ (h _ c.point_mem_locus).elim fun _
    e ↦ ⟨fun _ _ ↦ ((c.isCohomEquiv_univPoint.choose_spec.2 ((G e).1.preimage_fieldLocus_not.trans
    (by simp [EtaleChart.restrict, Pi.sub_def, away, EtaleChart.prod, ← map_sub]
        rfl))).2.comp_iff.2 (Q rfl) _).1 ((hodge_vanishing_along_diagonal (EtaleChart.restrict _ e
    c.injective c.isOpenSub).etale n).1 ..)⟩) _ (⟨·, _, rfl, le_rfl⟩)
    (hasZariskiDescent_hodgeCoeff (isLocallyEverything_of_open_cover fun _ k ⟨z, _⟩ ↦ by_cases
    (· ▸ (N k z).elim (⟨_, isOpenSub <| V ·, ·, le_sup_of_le_left (le_sSup ⟨_, rfl⟩)⟩)) (⟨_,
    isOpenSub_offDiagonal, mem_offDiagonal_of_ne k ·, le_sup_right⟩))) x fun i j ↦
    ((V i).exists_locus_eq_inf (V j)).elim fun c e ↦ (e ▸ c.point_mem_locus
    :).elim fun ⟨_, m⟩ ⟨_, n⟩ ↦ ?_).imp fun δ H K z k ↦ (N k z).elim (⟨a ·, _, isOpenSub _, ·,
    fun | _, _, ⟨⟨χ⟩, rfl⟩ => ⟨tensorInl ≫ l ≫ χ, tensorInr ≫ l ≫ χ, ?_⟩⟩)
  simpa [← map_sub] using ⟨rfl, rfl, by peel 2 G rfl; erw [← H,
    ← δ.map_comp _ (relFreeAb.map _ le_rfl), relFreeAb.map_comp] at this; tauto⟩
  obtain ⟨⟨D, _, u⟩, F, _, v⟩ := G m, G n
  refine (Q e _).1 (.trans ?_ (u.trans (c.symbolClass_eq_of_cutsOutLocus D F ▸ v ▸ ?_))) <;>
    erw [← (x _).map_comp _ (relFreeAb.restrict _ (by simp)), relFreeAb.map_comp] <;> rfl
end

section
/-! Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). The setting here is smooth separated varieties with a finite atlas in characteristic 0,
with cohomology taken as Ext of functors. These files give only surjectivity of the Künneth map for
X×X, and the pull-back of the diagonal class along reduced coincidences as a weighted sum of point
classes. Source: Stacks Project, tags 0BEC (Künneth) and 0G82 (Gysin maps); A. Chatzistamatiou, K.
Rülling, Higher direct images of the structure sheaf in positive characteristic, Algebra & Number
Theory 5 (2011) 693-775, sections 2-3; V. Srinivas, Gysin maps and cycle classes for Hodge
cohomology, Proc. Indian Acad. Sci. Math. Sci. 103 (1993) 209-247; Hartshorne, Residues and Duality
(1966) III.9 for the symbol.

Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles (known
result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Pull-back of the diagonal class is a weighted sum of point classes. -/

open CategoryTheory CommAlgCat Field H HodgeTest Ideal RingHom CartesianMonoidalCategory
  MonoidalCategory

variable {k} [Field k] [CharZero k] {d} {W X : CommAlg k ⥤ Type 1} [HasAtlas d X]

/-- For t in k and u, c: W → X, the map W(A ⊕ M) → (X × X)(A ⊕ M), w ↦ (u(s_t w), c(w)), with
s_t induced by (a,m) ↦ (a,tm). -/
def scaledGraph t (u c : W ⟶ X) :=
  lift (scaleModule t _ ≫ sqZeroExt.whiskerLeft u) (sqZeroExt.whiskerLeft c)

/-- For a k-point z of X, the constant map W → X sending every A-point of W to the image of z in
X(A). -/
def constMap (z : X (of k k)) : W ⟶ X where app A := ↾fun _ ↦ X.map structureMap z

seal H.map

/-- Fixed point formula: X with an atlas of dimension d has δ in Hdg^d(X × X) such that for E
over k, W separated and covered by charts, u, c: W → X_E with finite reduced coincidence set
s and ratios n_w as in `HasJacobianRatio`, (u s_t, c)^*δ = ∑_{w∈s} n_w cl(w).

Known result: Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck
symbols). -/
lemma exists_diagonal_local_terms {d} (hX : HasAtlas d X) : ∃ δ : HodgeH (freeAb.obj (X ⊗ X)) d,
  ∀ {E} [Field E] [CharZero E] [Algebra k E] {W} [IsSepFunctor W] [IsChartCovered d W] (u c :
  W ⟶ _) s t (n : _ → E), IsCoincidenceSet u c s → (∀ w ∈ s, HasJacobianRatio u c d t (n w) w) →
  (∃ ξ : HodgeH (_root_.relFreeAb (offPoints s)) d, IsPointSum s n ξ) ∧ H.map _ (freeAb.map
  (scaledGraph t u c)) d δ.baseChange = ∑ w ∈ s, n w • pointClass d w := (exists_diagonal_class
  hX).imp' (.map (relFreeAb.π _)) fun δ hδ E _ _ _ W _ _ u c s t n ⟨hr, h, hs⟩ hJ ↦ by
  have N {U} (h : IsOpenSub U) : (U.preimage (lift u c)).whisker _ ≤
    (U.whisker _).preimage (scaledGraph t u c) := fun C _ m ↦ h.mem_of_isSquareZero C.baseProj
    fst_surjective_and_kerIdeal_sq _ (congr(($((X.map_comp_apply ..).trans
    (congrArg _ (u.naturality_apply ..).symm)), _) ∈ _).mp (U.map C.baseProj m))
  refine ⟨⟨H.map _ (relFreeAb.map (U' := (offPoints s).whisker _) _ fun C _ _ ↦
    N (@isOpenSub_offDiagonal _ _ X _).whisker_restrictAlg C
    ((isOpenSub_offDiagonal.whisker_restrictAlg.preimage _).fieldLocus_le _ fun _ _ ↦
    (mem_offDiagonal_of_ne (X := X) · (by tauto)))) d _, ?I⟩, IsPointSum.map_eq_sum_pointClass ?I
    rfl ▸ by erw [HodgeH.baseChange_map, ← map_comp, eq_comm, ← map_comp]; rfl⟩
  refine fun w hw ↦ (hδ _ (c _ w) (toIsField E)).elim fun A ⟨O, hO, hw', L⟩ ↦ ?_
  obtain ⟨⟨Q, hQ, hT⟩, a, ⟨⟨ζ : _ ⟶ _⟩, rfl⟩, ha, v⟩ := hJ w hw A (by have := L _ _ hw'; tauto),
    ((hO.whisker_restrictAlg.preimage (lift u c :)).inf (isOpenSub_offPoints (s :=
    s \ {w}))).exists_chart_le (toIsField E)
    ⟨congr(($(h w hw), _)) ▸ hw', by simp [mem_offPoints_iff, toIsField, ComesFromPoints]⟩
  obtain ⟨⟨φ, ψ, hφ, hψ, Z, -⟩, ν, F, V⟩ := L _ _ ha, a.isCohomEquiv_univPoint
  have M {v : W ⟶ restrictAlg k E ⋙ X} {B C φ y} h (α : B ⟶ C) :=
    (X.map_comp_apply φ _ A.point).trans ((congrArg _ h).trans (v.naturality_apply α y).symm)
  let f := (φ ∘ A.coordinate : _ → a.R) - by exact ψ ∘ A.coordinate
  have Z {C} (α : a.R ⟶ C) : span _ ≤ ker α.hom ↔ _ := (Z ..).trans (eq_comm.trans
    ((c.naturality_apply α a.point).congr (u.naturality_apply α a.point) :).symm)
  obtain ⟨b, o, hb⟩ := exists_mem_colon_of_tangent rfl ((Z ζ).2 (by tauto)) fun p _ l r ↦
    congr(($(a.eq_comp_of_map_point_eq _ (hr _ ((Z _).1 l))) r).2)
  have hk := by simpa using (map_eq_top_iff_fields _ (𝟙 _)).2 fun K κ i l ↦ v K κ i ((hs
    K i _ ((Z _).1 (le_colon.trans l))).imp fun z ⟨m, e⟩ ↦ ⟨⟨m, fun q ↦ hb (by
    simpa [a.eq_comp_of_map_point_eq _ (q ▸ e), i.nontrivial] using l o)⟩, e⟩)
  refine ⟨a, f, ⟨_, rfl⟩, ?D, fun C p l K κ hK ⟨z, hz, e⟩ ↦ (offPoints _).map _ v K κ hK
    ⟨z, ⟨hz, (l K κ hK ⟨z, ·, e⟩)⟩, e⟩, ((V (CutsOutLocus.preimage_fieldLocus_not ?D)).2 _).1 ?_⟩
  exact fun C α ↦ ⟨(by simp [ComesFromPoints, eq_comp_structureMap_of_ker_le <| hk.trans ·]; rfl),
    (Z α).2 ∘ by simp_all [ComesFromPoints]⟩
  obtain ⟨_, _, h₁, h₂, Y, _, e'⟩ := L _ _ (N hO.whisker_restrictAlg _ (Subfunctor.map _ ν ha))
  obtain ⟨rfl, rfl, e'⟩ := A.injective _ ((M (M hφ _) _).trans h₁.symm),
    A.injective _ ((M hψ _).trans h₂.symm), by simpa -dsimp using congr(($e').baseChange (k := E))
  have eF i : _ = f i := congr($(F _) - $(F _))
  erw [eq_comm, map_push, ← map_comp, eq_comm, ← map_comp, ← map_comp]
  refine (congrArg (H.map _ · d _) (relFreeAb.hom_ext fun C σ ↦ ?_)).trans ((map_comp ..).trans
    ((congrArg (H.map _ (relFreeAb.map (U' := someUnitLocus _) (U := .whisker (.preimage _
    (pointMap _)) (sqZeroExt ⋙ _)) (pointMap ⟨𝟙 _⟩) fun C σ ⟨i, e⟩ ↦ Y.preimage_fieldLocus_not.ge _
    (projSpace.span_eq_top_of_isUnit i (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (eF i ▸ e :)))) d)
    e').trans ((map_comp ..).symm.trans ((congrArg _ (witnessed.pull_cocycleClass
    exists_jouanolouRel_of_unimodular exists_jouanolouRel_of_unimodular _ (𝟙 _) {app _ := ↾(·.2)} ?_
    ?_ ?_)).trans (symbolClass_transformation (by tauto) ?_ (funext eF)
    (1 : Matrix (Fin d) _ _) (Q.map (algebraMap ..))
    _ (by ext; simp; erw [F]) (fun i j ↦ hk ?_) (hQ ▸ by simp [map_det]))))))
  exact congr(relFreeAb.mk _ $(W.map_comp_apply .. ▸ (scaledGraph ..).naturality_apply ..))
  (iterate 4 tauto); show ζ (t • (ν _).snd j - (ν _).snd j - _) = 0
  let μ := (withIndex _ ⋙ sqZeroExt).map ζ ≫ ofHom (TrivSqZeroExt.map (.proj j))
  have S y : (μ y).2 = ζ _ := zero_add _
  simpa [← S, f] using! congr($(hT _ _ _ (W.map_comp_apply .. ▸
    by congr with _; exact (add_zero _).trans congr(ζ $(F _))) (by tauto) (M hψ (ν ≫ μ))) i)

lemma exists_diagonal_pointClass : ∃ δ, ∀ z, (∃ ξ : HodgeH (_root_.relFreeAb (offPoints {z})) d,
  IsPointSum {z} 1 ξ) ∧ .map (freeAb.map (lift (constMap z) (𝟙 X))) δ = pointClass d z ∧
  ∀ {W} [IsSepFunctor W] [IsChartCovered d W] (u : W ⟶ X) s, IsCoincidenceSet (constMap z) u
  s → .map (freeAb.map u) (pointClass d z) = ∑ w ∈ s, pointClass d w :=
  (exists_diagonal_local_terms ‹_›).imp' _ fun δ h z ↦ by
  have h W [IsSepFunctor W] [IsChartCovered d W] :=
    (h (W := W) (constMap z) · · 1 1 · fun _ _ _ _ ↦ ⟨1, by simp⟩)
  have e :=
    h X (𝟙 _) {z} ⟨fun | _, rfl => (map_map_structureMap ..).symm, by simp [constMap]; tauto⟩
  simp at *
  use Finset.coe_singleton z ▸ e.1, e.2; peel h; erw [← this.2, ← e.2, ← map_comp]
  congr; exact freeAb.hom_ext (Y := _ ⋙ _)

/-- If X has an atlas of dimension d and the k-points z, z' take the same value under every map
from X to the affine line, then cl(z) = cl(z') in Hdg^d(X). -/
lemma pointClass_eq_of_functions_eq {z z'} (e : ∀ g : X ⟶ affineSpace k 1, (g _ z).1 0 =
  (g _ z').1 0) : pointClass d z = pointClass d z' := by
  repeat rw [← (exists_diagonal_pointClass.choose_spec _).2.1]
  apply AddMonoidHom.eqOn_closureM _ (kunneth _)
  rintro _ ⟨a, n, h, x, y, rfl⟩
  have ⟨_, r⟩ := @projective_and_eval_bijective _ _ (@sqZeroExt k _ ⋙ 𝟙_ _) hodgeCoeff ⟨_, Empty⟩ ⟨⟩
    fun _ ↦ ⟨fun ⟨_⟩ ⟨_⟩ _ ↦ congrArg _ (hom_ext (by ext) nofun), fun _ ↦ ⟨⟨structureMap, 0⟩, rfl⟩⟩
  repeat erw [← map_comp, cup_map _ x y h (freeAb.map (sqZeroExt.whiskerLeft (constMap _))) (𝟙 _)
    (γ' := freeAb.map (λ_ _).inv ≫ freeAb.prod (_ ⋙ 𝟙_ _) (_ ⋙ X)) freeAb.hom_ext]
  congr 2; cases a <;> [rw [← x.mk₀_homEquiv₀_apply]; subsingleton]
  repeat erw [H.map, Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀]
  exact congrArg _ (r.1 (ULift.down_injective (formBasis.ext_elem fun i ↦
    e (freeAb.homEquiv X _ ((𝟭 _).whiskerRight (H := _ ⋙ sqZeroExt) ⟨fun _ ↦
    ofHom (TrivSqZeroExt.inlAlgHom ..), by intros; ext; exact TrivSqZeroExt.ext rfl (by ext ⟨⟩)⟩
    (freeAb X) ≫ (withIndex _).whiskerLeft (Abelian.Ext.homEquiv₀ x)) ≫ ⟨fun A ↦ ↾(⟨fun _ ↦
    formBasis.repr ·.1 i⟩), by intros; ext; congrm ⟨fun _ ↦ $(repr_withIndex_map ..)⟩⟩))))
end

section
/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge–Tate image of dX/X is the units extension class mod (ker θ)². Cup product with
the Hodge–Tate image of a point class on P¹ is injective. -/

open thickeningOver CategoryTheory CommAlgCat MvPolynomial NNRat TotalH PadicTest WittVector freeAb
  CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

variable {p k} [Field k] [EmbeddedInQpBar p k]

/-- The morphism from ℤ[𝔸¹∖0] to the multiplicative group A ↦ A^× (written additively) on
k-algebras, sending [v] to the coordinate of v, a unit. -/
noncomputable def Gm.ofCoord : freeAb (@unimodular k _ 1).toFunctor ⟶ forget₂ .. ⋙ Gm :=
  desc (fun _ v ↦ ⟨(by
  simpa [unimodular, Set.range_unique] using v.2 : IsUnit (v.1.1 0)).unit⟩) (by simp [ext]; tauto)

/-- The morphism t ↦ 1 − μt from the additive group of T = R[1/p] to the units of B =
W(R^♭)[1/p]/(ker θ)², on p-adic tests with ring R; μ = [ε] − 1. -/
noncomputable def thickeningOver.oneSubMu : genericCoeff ⟶ thickeningOver ⋙ forget₂ .. ⋙ Gm :=
  ⟨fun c ↦ AddCommGrpCat.uliftFunctor.map
  (AddCommGrpCat.ofHom (MonoidHom.toAdditiveRight (.toHomUnits ⟨⟨(1 - mulMu c ·.toAdd), by simp⟩, by
    simp [mul_sub, ← mulMu_proj_mul, proj_mulMu, sub_sub]⟩))), fun _ _ _ ↦ AddCommGrpCat.ext fun _ ↦
  Gm.ext.2 ((_root_.map_sub ..).trans (congrArg₂ _ (map_one _) (map_mulMu ..))).symm⟩

lemma thickeningOver.shortExact_oneSubMu : ∃ w,
  ShortComplex.ShortExact ⟨oneSubMu, whiskerRight proj _, w⟩ := by
  choose s i e using exact_mulMu_proj
  exact shortExact_of_app (fun c _ _ h ↦ congr(⟨$(i c (sub_right_inj.1 (Gm.ext.1 h)))⟩)) (fun c
    ⟨u⟩ ↦ .trans (by simpa [Gm.ext,
    sub_eq_zero.trans eq_comm, eq_comm.trans sub_eq_iff_comm] using! e c (1 - _)) ULift.exists.symm)
    fun c ⟨u⟩ ↦ (s ..).elim fun _ h ↦
    ⟨⟨((IsNilpotent.isUnit_quotient_mk_iff ⟨2, c.ker_thickeningProj_sq⟩).1
    (.of_map (RingHom.quotientKerEquivOfSurjective (s c)) _ ⟨u, h.symm⟩)).unit⟩, Gm.ext.2 h⟩

/-- For d = 1, λ₁[dT/T] is `restrictToPairs` of the boundary, for the pair (𝔸¹, 𝔸¹ ∖ 0), of the
pull-back along T of the extension 0 → R[1/p] → B^× → R[1/p]^× → 0, with B =
`thickeningOver`, first map t ↦ 1 − μt. -/
lemma hodgeTateMap_symbolClass : hodgeTateMap 1 symbolClass =
  restrictToPairs (((relFreeAb.shortExact _).2.map_of_exact (restrictAlong _)).extClass.comp
  (H.map _ (genericOver.whiskerLeft Gm.ofCoord) 1 shortExact_oneSubMu.2.extClass) rfl) := by
  choose ω hω eω using symbolClass_one k
  simpa [eω] using!
    (comp_assoc_of_eq (Comparison.pull_comp_restrictAlong ..) _).symm.trans ((congrArg _ (by
    simp [Comparison.pull, H.map, H.push, Abelian.Ext.toTotalH]
    erw [comp_assoc_of_eq (Cocycle.cohomClass_naturality ⟨_,
      _⟩ _ _ (𝟙 _) (by intros; erw [Category.comp_id])).symm, comp_id, ← homClass_comp_of]
    refine Cocycle.cohomClass_comp_eq_extClass _ (shortExact_oneSubMu.2.map_of_exact (restrictAlong
      _)) _ _ (fun _ ↦ Gm.ofCoord _ ≫ Gm.map (CommRingCat.ofHom (.pullbackFst ..))) (fun _ ↦ ?_)
      fun X _ f ↦ AddCommGrpCat.hom_ext (FreeAbelianGroup.lift_ext _ _ fun ⟨⟨v⟩, u⟩ ↦ (hω _ ⟨_,
      unimodular.map (X.toSqZero) u⟩).elim fun m ⟨h, e⟩ ↦ ?_) <;> simp [← Functor.map_comp]
    congr with ⟨⟩; tauto
    erw [e, ← sub_eq_iff_eq_add', desc_of, Gm.ext]
    show _ * (1 - (thickeningOver.mulMu ..) (-(contraction f.2 (.ι _ m)).algebraMapInv)) = _ + _
    erw [mul_one_sub, ← mulMu_proj_mul, proj.naturality_apply, (v 0).2, ← h, map_smulₛₗ]
    simp [contraction]; rfl
    simp [Cocycle.cocycle_comp, ↓NatTrans.naturality_assoc])).trans
    (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact _).2.extClass ..))

lemma thickeningOver.teichmullerLift_epsTilt c : teichmullerLift c (algebraMap _ _ epsTilt) = 1 +
  mulMu c 1 := by simp [map_one c.thickeningProj ▸ mulMu_thickeningProj c 1, mu]; erw
  [MonoidHom.comp_apply, ← map_teichmuller]; rfl

seal genericAlg thickeningOver

/-- For k embedded in Q̄_p, λ_1 of the class of [1:0] in ℙ¹ comes from a degree-2 class η on
p-adic tests such that x ↦ x × η has zero kernel on Ext^n(N, R[1/p]) for every flat-valued
abelian functor N and every n. -/
lemma projSpace.exists_hodgeTateMap_pointClass_line : ∃ η, hodgeTateMap 1 (pointClass 1
  (@affinePoint k _ 1 _ 0 0)) = restrictToPairs η ∧ ∀ {N n} [HasFlatValues N] (x : H N genericCoeff
  n), _root_.cup (genericAlg ⋙ forget₂ ..).mulPairing x η (add_comm 2 n) = 0 → x = 0 := by
  have D {V U} [s : @IsChartCovered k _ 1 V] o : PairRestrictBijective (relFreeAb U) :=
    (((Comparison.restrict ..).isClosedClass HodgeTatePair.toGeneric).2 _ (relFreeAb.shortExact U).2
    (s.comap U.ι (by simpa)).pairRestrictBijective).1 s.pairRestrictBijective
  obtain ⟨ξ, ⟨hX, h₁, E⟩, G⟩ := (stdChart k 1 0).exists_isLocalSymbol (z := affinePoint 0 0) (g :=
    X) (fun _ _ ↦ by simp [ComesFromPoints]; erw [mk_eq_mk_iff_cross_mul]; simp +contextual
    [Set.range_unique]) ((mk_mem_stdChart_iff _).2 isUnit_one)
  obtain ⟨⟨ξT, hξ⟩, G⟩ :=
    (D isOpenSub_offPoints).exists_hodgeTateMap_eq 1 ξ, G.map_eq_smul_pointClass.symm
  apply_fun hodgeTateMap 1 at E G; simp [hodgeTateMap_map, *, hodgeTateMap_symbolClass,
    ← restrictToPairs_map] at *
  refine ⟨_, G, fun x s ↦
    DirectSum.of_injective _ ((comp_id.trans x.toTotalH.map_id).symm.trans ?_)⟩
  let A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ _ ⋙ affineSpace k 1 :=
    ⟨(↾fun t ↦ ⟨fun _ ↦ teichmullerLift · (t.1.hom (.single 1 1))⟩),
    by intros; ext; with_unfolding_all exact congr(⟨fun _ ↦ .mk _ $(.symm ((IsLocalization.map_eq
    (powers_le_comap_powers ..) _).trans (congrArg _ (map_teichmuller ..))))⟩)⟩
  let b := A ≫ whiskerRight proj _
  have g c i t : b c ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.1⟩ = b c t := by
    simp [b, A, affineSpace, charTwist, funext_iff, -AddMonoidAlgebra.coe_algebraMap]
    erw [((proj c).hom.1.1.comp
      ((teichmullerLift ..).comp ((algebraMap ..).1.comp epsPow))).mem_ker.1, one_mul]
    cases i <;> simp [teichmullerLift_epsTilt, proj_mulMu]
  let T : affineSpace k 1 ⟶ reprBy (stdChart k 1 0).R := ⟨fun _ ↦ ↾(⟨ofHom <| aeval ·.1⟩), by
    intros; ext; congrm ⟨ofHom $((comp_aeval ..).symm)⟩⟩
  let φ : twoDiscs ⟶ _ := sigma.desc fun i ↦
    b ≫ whiskerLeft _ (T ≫ pointMap (stdChart k 1 (i.1.rec 1 0)).point)
  have U c t : (A c ⟨discToTorus coeHom ≫ t⟩).1 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).1 0 = 1 := by
    simp [A, ← map_mul, ← AddMonoidAlgebra.one_def]
  let W : _ ⟶ _ ⋙ freeAb unimodular.toFunctor := projFirst (B :=
    pointOrTorus) ≫ desc (.of ⟨_, span_eq_top_of_isUnit 0 <| .of_mul_eq_one _
    <| U · ·.1⟩) (by intros; exact .symm congr(.of $(Subtype.ext (A.naturality_apply ..).symm)))
  let ε {X} : freeAb X ⟶ genericCoeff := desc (fun c _ ↦ ⟨(1 : genericAlg c)⟩)
    (by intros; exact congrArg _ (map_one (genericAlg.map _).1).symm)
  obtain ⟨_, _, _, _, _, J, I⟩ := by
    apply toda_squares (oneSub_comp_gluing epsPow) (origin ⟨true⟩) (hom_ext (by simp -dsimp))
      ((relFreeAb.shortExact unimodular).2.map_of_exact (restrictAlong _)) shortExact_oneSubMu.2
      (projFirst ≫ freeAb.map b) (-W ≫ whiskerLeft _ Gm.ofCoord) (projFirst ≫ ε) (whiskerLeft
      _ Gm.ofCoord) (-W ≫ whiskerRight proj _) <;> apply freeAb.hom_ext <;> rintro c
      ⟨⟨⟨⟩⟩⟩ <;> simp [W]
    exacts [rfl, congr(.of $((g _ true _).symm)), sub_eq_of_eq_add (Gm.ext.2 (.symm (show (1 - mulMu
      c _) * _ = _ by
      erw [desc_of, desc_of, desc_of, IsUnit.unit_spec]
      simp [A, charTwist, pointOrTorus, AddEquiv.ulift, -AddMonoidAlgebra.coe_algebraMap,
        -Bool.cond_eq_ite]
      erw [AddMonoidAlgebra.lift_single]
      simp [-AddMonoidAlgebra.coe_algebraMap]
      erw [AlgHom.commutes, teichmullerLift_epsTilt]; rfl)))]
  have m A ψ := @relFreeAb.mk_eq_zero _ _ _ (offPoints {affinePoint 0 0}) A _ ((offPoints _).map ψ
    (a := (stdChart k 1 1).point)
    fun K ψ h ⟨_, rfl, e⟩ ↦ by have := h.nontrivial; simpa using (mk_mem_stdChart_iff ..).1 ⟨_, e⟩)
  obtain ⟨j', hj⟩ := by
    refine J _ _ (freeAb.map φ - origin ⟨false⟩ _ ≫ freeAb.map φ) (whiskerLeft _ (relFreeAb.π _))
      (whiskerLeft _ (relFreeAb.map T (fun _ v l ↦ hX.preimage_fieldLocus_not.ge _
      (.trans (congrArg _ (congrArg _ (funext (aeval_X _)))) l)) ≫ relFreeAb.map _ h₁)) (hom_ext ?_)
      (hom_ext (by simp [-Bool.cond_eq_ite]; simp [freeAb, φ, sigma.desc, g, -Bool.cond_eq_ite]))
        (hom_ext ?_) <;> rintro c ⟨⟨⟨⟩⟩⟩ <;> simp
    exacts [congr(.of $(mk_eq_mk_iff_cross_mul.2 (by
      simp; erw [aeval_X, aeval_X, mul_comm, ← map_mul (proj c).1, U]; simp))),
      (m ..).trans (m ..).symm, sub_eq_self.2 (m ..)]
  have q := congr(pullbackAlong $hj ξT.toTotalH).symm
  erw [← homClass_comp_homClass_comp, homClass_comp_of, whiskerLeft_comp, H.map_comp, (@D _ _
    (.comap _ (EtaleChart.isOpenSub _)) (isOpenSub_offPoints.preimage _)).injective_restrictToPairs
    E, ← H.map_comp, ← whiskerLeft_comp, show _ ≫ _ = 𝟙 _ from relFreeAb.hom_ext fun _ _ ↦
    congrArg (relFreeAb.mk unimodular ⟨·⟩) (funext (aeval_X _)), H.map_id] at q
  erw [map_zero, ← show tensorPoint ε _ ≫ (genericAlg ⋙ forget₂ ..).mulPairing = 𝟙 _ by
    ext _ ⟨⟩; exact congrArg _ ((mul_one_add ..).trans (by simp)), homClass_comp,
    TotalH.comp_assoc_of_sq (naturality ..), (I _ _ _ (subsingleton_coker_gluing
    isCohomEquiv_gluing_generic _)).1 _ (tensorPoint (𝟙 _) _) _ 0, map_zero]
  erw [← map_homClass, ← TotalH.map_comp_assoc, q, ← homClass_comp_homClass_comp, homClass_comp_of,
    TotalH.map_comp_assoc, (comp_assoc_of_eq rfl _).trans (cup_of ..), s] <;> simp +arith
end

section
/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge class of a point of a product is the product of point classes. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Functor relFreeAb Classical
set_option backward.isDefEq.respectTransparency false

-- `relFreeAb.map` is written in full: a bare `map` is ambiguous
/-- The product of point classes is a point class: over a field k of characteristic 0, if X and
Y have atlases of dimensions d and 1, then cl(z) × cl(w) = cl(z, w) in Hdg^{d+1}(X × Y) for
k-points z, w. -/
lemma IsPointSum.cup_pointClass {k} [Field k] [CharZero k] {d X Y} [HasAtlas d X] [HasAtlas 1 Y]
  z : .map (freeAb.prod X Y) (cup (@exteriorAlg k _).mulPairing (pointClass d z.1)
  (pointClass 1 z.2) (add_comm ..)) = pointClass _ z := by
  have m {R X Y U W T S} s t h l x y := (HodgeH.map_comp (relFreeAb.map (@pointMap _ _ (X ⊗ Y) R (s,
    t)) (sup_le_sup h l)) (relFreeAb.prod U W) _).symm.trans (cup_map (γ' :=
    (@HodgeTest.sqZeroExt k _).whiskerLeft (relFreeAb.map (lift (𝟙 _) (𝟙 _)) le_rfl ≫ relFreeAb.prod
    T S)) (mulPairing _) x y (add_comm 1 d) (whiskerLeft _ (relFreeAb.map (pointMap s) h))
    (whiskerLeft _ (relFreeAb.map (pointMap t) l)) (hom_ext (U := (T ⊔ S).whisker _)))
  obtain ⟨⟨a, g, ez, e⟩, b, g', ew, e'⟩ := epsilon_spec (exists_diagonal_pointClass.choose_spec _).1
    z.1 rfl, epsilon_spec (exists_diagonal_pointClass.choose_spec _).1 z.2 rfl
  have ⟨ξ, L, G⟩ := (a.prod b).exists_isLocalSymbol (g := Fin.snoc (g · ⊗ₜ 1) (1 ⊗ₜ g' 0))
    (fun _ α ↦ .symm (exists_eq_left.trans (Prod.ext_iff.trans (by simpa -dsimp [ComesFromPoints,
    Ideal.span_le, Set.subset_def, and_comm] using! ((e.1 _ (_ ≫ α)).and (e'.1 _ (_ ≫ α))).symm))))
    ((range_pointMap_prod ..).ge _ ⟨ez, ew⟩)
  use have hU := by rintro _ _ (h | h) _ _ l ⟨_, ⟨⟩, e⟩ <;> use h _ _ l ⟨_, rfl, by injections⟩
    (cup_map _ _ _ _ (whiskerLeft _ (π _)) (whiskerLeft _ (π _)) rfl).symm.trans ((HodgeH.map_comp
      (π _) (relFreeAb.prod ..) _).trans ((hodge_excision (a.prod b).isOpenSub (fun _ l _ n ↦ by
    obtain ⟨_, h⟩ | ⟨_, h⟩ := (not_and_or.1 (range_pointMap_prod a b ▸ n)).imp
      (exists_isOpenSub_le_offPoints ez l ·) (exists_isOpenSub_le_offPoints ew
    l ·) <;> exact ⟨_, h.1.preimage _, by tauto⟩) rfl _).1 ((m ..).trans ((congrArg _
    (congrArg₂ (cup _ · · _) (e.map _).2.2 (e'.map _).2.2)).trans (by
    erw [one_smul, one_smul, ← m]
    simpa -dsimp [(symbolClass_succ ..).2, ← HodgeH.map_comp, pointMap_comp] using!
      congr($(L.2.2).map (relFreeAb.map (𝟙 (reprBy _)) fun x _ ↦ (hU x ·))).symm)) : _ = (ξ.map
      (relFreeAb.map (𝟙 _) hU)).map _) ▸ by simp [← HodgeH.map_comp, π_map,
      G.map_eq_smul_pointClass]))
end

section
/-! Part of: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Hodge–Tate map does not kill the class of a point of projective space. -/

open CategoryTheory Finset CartesianMonoidalCategory CommAlgCat Fin Polynomial
set_option backward.isDefEq.respectTransparency false

seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor in
/-- For a field k with an embedding in Q̄_p and any k-point z of projective d-space
`projSpace`, the Hodge–Tate map of weight d does not kill the class cl(z) ∈ Hdg^d.

Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles. -/
lemma projSpace.hodgeTateMap_pointClass_ne_zero {p k} [Field k] [EmbeddedInQpBar p k] {d} z :
  hodgeTateMap d (pointClass (X := projSpace k d) d z) ≠ 0
  := exists_hodgeTateMap_pointClass_line.rec fun η ⟨hη, P⟩ ↦ by
  have c {d} : ∀ z, pointClass d z = pointClass d (@affinePoint k _ d _ 0 0) :=
    Quot.ind fun ⟨⟨u⟩, h⟩ ↦ pointClass_eq_of_functions_eq fun g ↦
    have n {B C z} (ψ : B ⟶ C) x (e : z =
      _ := by erw [mk_eq_mk_iff_cross_mul]; simp [forall_fin_succ] at * <;>
     grind) := congr($((congrArg _ e).trans (g.naturality_apply ψ x)).1 0)
    if hj : _ then (eq_C_of_toLaurent_eq _ _ ((n (ofHom toLaurentAlg) (mk (cons X (C ∘ u ∘ succ))
    (Exists.rec span_eq_top_of_isUnit hj))).symm.trans
      (n (ofHom (LaurentPolynomial.invert.toAlgHom.comp toLaurentAlg)) (affinePoint 0
      (monomial 1 ∘ u ∘ succ)) rfl))).rec fun _ e ↦ (n (ofHom (aeval (u 0))) _).trans ((congr(
    aeval _ $e.1 = aeval _ $e.2).mpr (by simp)).trans (n (ofHom (aeval 0)) _).symm) else n (𝟙 _) _
  have M {d} (z := @affinePoint k _ d _ 0 0) : hodgeTateMap d.succ (.map (freeAb.map (lineProductMap
    k d)) (pointClass d.succ (affinePoint 0 0))) = 0 ↔ hodgeTateMap d (pointClass d z) = 0 := by
    obtain ⟨⟨ξ, hx⟩, δ, h⟩ := IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq d
      (pointClass d z), exists_diagonal_local_terms (hasAtlas k _)
    have C : IsCoincidenceSet (𝟙 _) (constMap z) {z} := by simp [IsCoincidenceSet,
      ConstIfCoincident, constMap, @map_map_structureMap k]
    have S t : HodgeH.scale t (.map (freeAb.map (lift (𝟙 _) (constMap z))) δ.baseChange) = _ :=
      (H.map_comp ..).symm.trans (congr(H.map _ $freeAb.hom_ext _ _).trans (h _ _ _ t _ C fun _ _ A
      _ ↦ ⟨.scalar _ t, rfl, fun _ _ γ _ _ c ↦
      A.eq_comp_of_map_point_eq _ (C.1 _ c.symm) ▸ by simp; repeat erw [sub_zero]⟩).2)
    have w l (n : hodgeTateMap l (pointClass d z) ≠ 0) :=
      Nat.pow_right_injective .refl (EmbeddedInQpBar.toCharZero.1
      (by simpa [smul_left_inj n, hodgeTateMap_scale] using
      congr((2 : k) ^ l • hodgeTateMap l $(S 1) = hodgeTateMap l $(S 2))))
    have F {B v u} : lineProductMap k d B (v, u) = (projSpace ..).map structureMap
      (affinePoint 0 0) → ∀ [IsLocalRing B], ∃ j, (v, u) = _ := v.induction_on₂ u fun _ _ e _ ↦
      (exists_eq_single_of_mul_eq_zero _ _ (by simpa using mk_eq_mk_iff_cross_mul.1 e ·.succ 0)).2
    rw [(exists_diagonal_pointClass.choose_spec _).2.2 (lineProductMap ..) _ ⟨fun (_,
      _) e ↦ by rw [(F e).choose_spec, map_map_structureMap], forall_mem_image.2 fun _ _ ↦
      mk_eq_mk_iff_cross_mul.2 (by simp [forall_fin_succ]), fun _ K _ e ↦ let := K.toField
      exists_mem_image.2 ((F e).imp (⟨mem_univ ·, ·⟩))⟩]
    simp_rw [← IsPointSum.cup_pointClass, c, ← c z, map_sum, hodgeTateMap_map, hodgeTateMap_cup]
    rw [sum_eq_single d] <;> simp +contextual [Finset.ext_iff, hx, hη, Not.imp_symm (w _),
      ← Nat.cast_smul_eq_nsmul k, -Nat.cast_add]
    refine ⟨fun _ ↦ P ξ (IsChartCovered.pairRestrictBijective.injective_restrictToPairs.comp
      (IsCohomEquiv.of_isIso ..).1 ((restrictToPairs_map (freeAb.prod ..) _).trans
      ((congrArg _ ((congrArg _ (Comparison.pull_cup abTensor_hom_ext
      ..)).trans (TotalH.cup_of ..).symm)).trans (by simpa)))) ▸ map_zero _, (by simp [·])⟩
  refine mt (M z).2 (d.rec (mt (congrArg (PairH.map (freeAb.map (lift (constMap (affinePoint 0 0))
    (𝟙 _))))) fun e ↦ ?_) fun _ ↦ mt (by simp [hodgeTateMap_map, M.1 ·]))
  erw [← hodgeTateMap_map, ← HodgeH.map_comp, ← freeAb.map_comp, show _ ≫ _ = 𝟙
    _ by ext _ ⟨⟩; erw [mk_eq_mk_iff_cross_mul]; simp, freeAb.map_id, H.map_id, hη, map_zero,
    map_eq_zero_iff _ IsChartCovered.pairRestrictBijective.injective_restrictToPairs] at e
  simpa using PadicTest.eq_zero_of_algebraMap_genericRing ⟨Unit, _, Pi.constRingHom ..⟩ 1
    congr(($(show 𝟙 genericCoeff = 0 by simpa [cup, e] using P (.mk₀ _)).1 _ ⟨_⟩).1)
end

section
/-! Known result: The Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. Only the
natural multiplicative map into the part of weight h is built here, from the torsor of lifts modulo
the square of the kernel of Fontaine's map. Bijectivity is not proved. Source: Scholze, p-adic Hodge
theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8; construction as in Bhatt,
The Hodge–Tate decomposition via perfectoid spaces, Arizona Winter School 2017, §3.4.

This file: Hodge classes map naturally to vectors of Hodge–Tate weight h in étale cohomology. -/
seal CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀ CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.mapExactFunctor

open AlgebraicGeometry CategoryTheory PairRestrictBijective H freeAb ModuleCat.Algebra

/-- Let Y (smooth, charted over Ω) and W be proper over R, A a place of Ω above p containing R,
k ≅ Q̄_p compatibly over E. For x ∈ Hdg^q(Y_E), some v ∈ ℂ_p ⊗ V^{q+h}(Y) of Hodge–Tate
weight h for the decomposition group of A over E and semilinear Θ satisfy λ_h(u^*x) =
Θ(u^*v) for all u: W → Y.

Known result: Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. -/
lemma exists_hasHodgeTateWeight {p h : ℕ} {R :
  CommRingCat} {E k : Type} [Field k] [Field E] [EmbeddedInQpBar p k] [Algebra R Ω] [Algebra R E]
  [Algebra E k] [Algebra E Ω] [IsScalarTower R E Ω] {Y} [IsCharted Y Ω] [IsProper Y.hom] {A} [I :
  PadicPlaceEmbedding E A p] (hR : ∀ r, algebraMap R Ω r ∈ A) (he : ∀ x, algebraMap k
  _ (algebraMap E k x) = I.e (algebraMap E Ω x)) d [SmoothOfRelativeDimension d Y.hom] ε (hk :
  ∀ z, algebraMap k (PadicAlgCl p) (ε z) = z) {W} [IsProper W.hom] {q} (x : HodgeH _ q) : ∃ v, ∃ Θ :
  _ →ₛₗ[ε] _, HasHodgeTateWeight (ellAdicCohom.galoisAction R Ω (decompGroup Gal(Ω/E) A) Y (q + h))
  h v ∧ ∀ u : W ⟶ Y, hodgeTateMap h (x.map (freeAb.map ((algPoints E R).map u))).baseChange =
  Θ ((((ellAdicCohom ..).map u.op).hom.restrictScalars _).baseChange _ v) := by
  obtain ⟨⟨e, ⟨⟨⟩, hj⟩, _⟩, θ, hθ⟩ := I, exists_periodAlg_iso_genericAlg
  algebraize [theta.comp (algebraMap ℤ_[p] _), (algebraMap E k).comp (algebraMap R E),
    (.codRestrict (.comp (algebraMap ..) (e.comp _)) _ (by simpa) : R →+* OC)]
  have := IsScalarTower.of_algebraMap_eq (S := OC) ((OC.toPadicIntAlgHom _).2 · |>.symm)
  choose J h₁ h₂ h₃ using exists_period_map (R := R) (by tauto) _ θ _ hj isPeriodRingPair_OC
  let B {n} W [IsProper W.hom] : H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R W))
    genericCoeff n ≃ₗ[k] _ := .ofBijective (mapₗ ..) (IsCohomEquiv.of_bijective (p :=
    toGenericPoints k (congrArg (algebraMap ..) <|
    IsScalarTower.algebraMap_apply R E Ω · ▸ he _) W) (·.bijective_generic_points) n)
  have S W z y : J W (z • y) = ε z • J W y := by
    erw [← (J W).map_smul, RingHom.comp_apply, hk, IsScalarTower.algebraMap_smul]
  refine (exists_hodgeTateMap_eq ?D h x.baseChange).elim fun ξ hξ ↦ ((h₃ Y).2 (B Y ξ)).elim fun v
    hv ↦ ⟨v, restrictToPairs ∘ₛₗ (B W).symm.comp ⟨_, S W⟩, fun g ↦ (h₃ Y).1 ((h₂ Y g _ _ (by
    intros; erw [hθ, hθ, PadicTest.structMap_twist]; rfl) _).trans (hv ▸
    (Comparison.map_pull_eq_pull_map (by exact hom_ext fun A _ ↦ congr(.of ⟨$(Over.OverMorphism.ext
    ((Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap A.ProdRing A.GenericRing)) (𝟙 _)
    _).symm.trans (Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom
    (algebraMap A.ProdRing A.GenericRing)) _)))⟩)) ..).symm.trans ((congrArg (B Y)
    (injective_restrictToPairs ?D (hodgeTateMap_galois_twist (by simp [*]) hξ (hk _)))).trans (by
    simp [algebra_compatible_smul (PadicAlgCl p), *])))), fun u ↦ by
    simp [hodgeTateMap_map, *, ← restrictToPairs_map]; rw [(B W).symm_apply_eq.2]
    erw [← map_comp, ← map_comp]; congr 2; exact hom_ext⟩
  apply (hasAtlas_algPoints d).isChartCovered.pairRestrictBijective
end

section
/-! Part of: Galois representation cut out of cohomology by a Hecke eigensystem; Eichler-Shimura
(known result; see Lib.Cohomology.PointClass.GaloisRep).

This file: Largest Hecke eigen-quotient of cohomology: existence, continuity, crystallinity, killed
Frobenius, weights. -/

open Polynomial TensorProduct Submodule Module LinearMap IsScalarTower nonZeroDivisors
  ModuleCat.Algebra DFinsupp
variable {ℓ Γ ι σ} [ThePrime ℓ] [Group Γ] [Fintype ι] {V : ι → ModuleCat ℚ_[ℓ]}
  [∀ i, Module.Finite ℚ_[ℓ] (V i)] (ρ : ∀ i, Representation ℚ_[ℓ] Γ (V i)) (T : ∀ i, σ → End ℚ_[ℓ]
  (V i)) (θ : σ → PadicAlgCl ℓ) {N} (r : Γ →* GL (Fin N) (PadicAlgCl ℓ))
  (F : ∀ i, V i →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ)

/-- The ℚ_ℓ-linear maps F_i : V_i → ℚ̄_ℓ^N span, turn T_s into the scalar θ_s, intertwine ρ_i
with r, and are universal among maps to ℚ̄_ℓ-spaces turning T_s into θ_s. -/
def IsEigenQuotient := (∀ i g x, matrixRep r g (F i x) = F i (ρ i g x)) ∧
  span (PadicAlgCl ℓ) (.range fun x : Σ
  i, V i ↦ F _ x.2) = ⊤ ∧ (∀ i s x, F i (T i s x) = θ s • F i x) ∧ ∀ M [AddCommGroup.{0} M] [Module
  (PadicAlgCl ℓ) M] [Module ℚ_[ℓ] M] [IsScalarTower ℚ_[ℓ] (PadicAlgCl ℓ) M] (f : ∀ _, _ →ₗ[ℚ_[ℓ]]
  M), (∀ i s x, f i (T i s x) = θ s • f i x) → ∃ φ : _ →ₗ[PadicAlgCl ℓ] _, ∀ i x, φ (F i x) = f i x

variable {ρ T}

/-- For finitely many continuous finite-dimensional ℚ_ℓ-representations V i of Γ with operators
T commuting with Γ, there are a continuous r: Γ → GL_N(ℚ̄_ℓ) and maps F from the V i forming
the largest θ-quotient (`IsEigenQuotient`). -/
lemma exists_isEigenQuotient [TopologicalSpace Γ] [IsTopologicalGroup Γ] (h : ∀ i s g, Commute
  (T i s) (ρ i g)) (hc : ∀ i x {N} (f : _ →ₗ[ℚ_[ℓ]] Fin N → PadicAlgCl ℓ), Continuous fun g ↦
  f (ρ i g x)) : ∃ N r F, IsEigenQuotient (N := N) ρ T θ r F ∧ Continuous r := by
  let G i := mk ℚ_[ℓ] (PadicAlgCl ℓ) (Π₀ i, V i) 1 ∘ₗ lsingle i
  let S := span (PadicAlgCl ℓ) {G i (T i s x) - θ s • G i x | (i) (s) (x)}
  let e := (finBasis (PadicAlgCl ℓ) (_ ⧸ S)).equivFun; have ⟨F, _, H⟩ : ∃ F, IsEigenQuotient (Γ :=
    Γ) 1 T θ 1 F := ⟨(↑(e.1 ∘ₗ S.mkQ) ∘ₗ G ·), by simp, (ker_mkQ _).symm.trans (ker_eq_top.2
    ((cancel_right e.surjective).1 (by ext; exact (ker_mkQ _).ge (subset_span (by tauto))))), by
    simp [← map_smul, ← Quotient.mk_smul, Submodule.Quotient.eq]; aesop, by intros; exact ⟨S.liftQ
    (liftBaseChange _ (lsum ℕ ‹_›)) (span_le.2 (by aesop_cat)) ∘ₗ e.symm, by simp [G]⟩⟩
  choose R hR using fun g ↦ H.2.2 _ (F · ∘ₗ ρ _ g) (by simp [← H.2.1, ← End.mul_apply, (h ..).eq])
  exact ⟨finrank (PadicAlgCl ℓ) (_ ⧸ S), (toMatrixAlgEquiv'.toMonoidHom.comp
    ⟨⟨R, ext_on_range H.1 (by simp_all)⟩, fun _ _ ↦
  ext_on_range H.1 (by simp_all)⟩).toHomUnits, F, ⟨by simp_all [toMatrixAlgEquiv'], H⟩,
  .of_coeHom_comp (continuous_pi fun _ ↦ span_le (p := (continuousSubmodule ..).comap (pi R)).2
  (Set.range_subset_iff.2 (hc _ ·.2 (F _) |>.congr (by simp_all))) (H.1.ge ⟨⟩)).matrix_transpose⟩

variable {θ r F} (h : IsEigenQuotient ρ T θ r F) {s : Finset ℕ} {m : ℕ → ℤ} {d : ℕ → ℕ} (t : ℕ →
  σ) [OverGp Γ ℓ] (hρ : ∀ i, IsCrystalline (ρ i))
include h hρ

omit [Fintype ι] [∀ i, Module.Finite ℚ_[ℓ] (V i)] in
lemma IsEigenQuotient.isCrystalline : IsCrystalline (matrixRep r) :=
  isAdmissible_of_one_tmul_mem_span (eq_top_iff'.1 h.2.1 · |> closure_induction
  (by simp) (by simp +contextual [tmul_add, add_mem]) fun c _ ⟨⟨i, x⟩, e⟩ ↦ e ▸ (hρ
  i).baseChange_mem_span_fixedPeriods (ρ' := matrixRep r) (f := c • F i) (by simp [← h.1]) (1 ⊗ₜ x))

omit [Fintype ι] [∀ i, Module.Finite ℚ_[ℓ] (V i)] in
lemma IsEigenQuotient.isKilledBy {f g} (hg : IsWeilPair (toGp g) f) (hφ : ∀ i y, ∑ k ∈ s,
  m k • baseChange _ ((T i (t k)).restrictScalars _) (linearFrob (ρ i) (g ^ d k) (d k * f) y) = 0) :
  IsKilledBy (matrixRep r) g f (∑ k ∈ s, C (m k * θ (t k)) * X ^ d k) := have P :=
    (h.isCrystalline hρ).isPotCrys; ⟨P, AlgebraTensorModule.ext fun
  a y ↦ eq_top_iff'.1 h.2.1 y |> closure_induction (by simp) (by intros; simp only [tmul_add,
    map_add, *]) fun c _ ⟨⟨i, x⟩, e⟩ ↦ let φ := (c • F i).restrictScalars _; e ▸ .trans (by
  erw [← φ.baseChange_tmul, eval₂_finsetSum]
  simp [C_mul_X_pow_eq_monomial, -map_mul, ← linearFrob_pow P hg, ← baseChange_linearFrob
    (hρ i).isPotCrys (hg.pow _) P φ (by simp [φ, ← h.1]), -baseChange_tmul]
  congr! 1; induction linearFrob (ρ i) _ _ _ <;> [simp [h.2.2, φ, smul_comm c];
    simp only [map_add, mul_add, *]]) congr(φ.baseChange _ $(hφ i _))⟩

/-- Let θ cut r out of crystalline ρ_i (toGp Γ open, the T_s commuting with each other and with Γ),
and η = γθ. If u is no jump of r at γ, some polynomial c with c(η) = 1 has c(T) killing the weight u
vectors (`HasHodgeTateWeight`) of each ℂ_ℓ ⊗ V_i. -/
lemma IsEigenQuotient.exists_word_kill_of_jump_eq_zero {γ : _ →ₐ[_] ℂ_[ℓ]} {u} {a : Gp ℓ} (ha : ∀ x,
  γ x = a x) (hc : ∀ i s g, Commute (T i s) (ρ i g)) (hc' : ∀ i s t, Commute (T i s) (T i t)) (e :
  jump (matrixRep r) γ u = 0) : ∃ c : List σ →₀ _, (c.sum fun L z ↦ z * (L.map (a ∘ θ)).prod) = 1 ∧
  ∀ i y, HasHodgeTateWeight (ρ i) u y
  → (c.sum fun L z ↦ z • ((L.map (T i)).prod.restrictScalars _).baseChange ℂ_[ℓ]) y = 0 := by
  let Φ v L : End _ (∀ i, hodgeTateMaps (ρ i) (toAlgHom ..) v) := piMap fun i ↦ hodgeTateMaps.pull
    (List.map (T i) L).prod (by simp_all [← End.mul_apply, (Commute.list_prod_left ..).eq])
  have := IsLocalization.isAlgebraic ℚ_[ℓ] ℤ_[ℓ]⁰
  refine (exists_words_comb_eq_zero (Φ u) (by aesop)
    (by intros; ext; exact congrArg _ congr($(hc' ..) _)) fun f
    hf ↦ let := γ.toModule; (@h.2.2.2 _ _ _ _ (of_algHom (γ.extendScalarsOfIsLocalization _ _⁰))
    (⟨f · |>.1.1, by simp [Algebra.smul_def]⟩) fun _ s _ ↦ by
    simpa [ha, RingHom.toModule_smul, Algebra.smul_def] using! congr(($(hf s) _).1 _)).elim fun φ
    hφ ↦ by ext; simp_all; exact hφ .. ▸ congr($(jump_eq_zero_iff.1 e ⟨_, φ.2⟩
              (mem_hodgeTateMaps_of_span h.2.1 (by simpa [↓h.1, ← hφ] using! (f _).2 ·.2))) _)).imp
    fun c ↦ .imp_right fun _ i y hy ↦ ?_
  have ⟨_, w, _, _, b, hb, _⟩ :=
    (hρ i).isPotCrys.exists_isHodgeTateFrame (finBasis ..) (toAlgHom ..)
  let Λ := liftBaseChange ℂ_[ℓ] (.restrictScalars ℤ_[ℓ] (S := ℚ_[ℓ])
    ⟨(b.constr ℕ b).flip.1, by simp⟩)
  refine (forall_dual_apply_eq_zero_iff ℂ_[ℓ] _).1 fun φ ↦ (show φ = Λ.flip ⟨(((liftBaseChangeEquiv
    _).symm φ).extendScalarsOfIsLocalization _⁰ ℚ_[ℓ]).1, by simp [Algebra.smul_def]⟩ by
    ext; simp [Λ]) ▸ congr($(b.ext (f₂ := 0) fun l ↦ ?_) _)
  let z := c.sum (fun L ↦ (· • Φ _ L)) (Pi.single i ⟨_, hb l⟩) i
  exact congr($(show Λ.flip _ ∘ₗ _ = Λ.flip z by ext; simp +zetaDelta [hodgeTateMaps.pull,
    Finsupp.sum]) y).trans (if e : w l = u then by aesop (erase simp finsupp_sum_apply) else
    have ⟨_, _, x, _⟩ := y.exists_sum_tmul_eq
    tate_eq_zero_of_chi_twist (e ∘ neg_inj.1) (nhds_one_le_map_nearOne Γ ((Filter.Eventually.all
      (z.2 <|
    x ·)).mono fun g _ ↦ by simpa [Λ, *, Finset.smul_sum, tensorAction] using congr(Λ $(hy g) z))))
end

section
/-! Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles.
Only non-vanishing and linear independence of the distinct point classes are proved, without duality
or a trace map. The proof treats first P¹, then projective space by products, then a smooth
projective variety by transfer along a finite linear projection. Source: Faltings, p-adic Hodge
theory, JAMS 1 (1988) (compatibility with traces and cycle classes); for the transfer,
Suslin–Voevodsky, Singular homology of abstract algebraic varieties, Invent. Math. 123 (1996),
§§4–6.

Known result: Galois representation cut out of cohomology by a Hecke eigensystem; Eichler-Shimura.
Here the representation is a quotient of total cohomology, not an isotypic part. No dimension or
semisimplicity is claimed, only good reduction, annihilation by the Hecke polynomial and occurrence
of given Hodge-Tate weights. Source: Deligne, Formes modulaires et représentations l-adiques, Sém.
Bourbaki 355 (1969), Thm 4.9; Harris and Taylor, The geometry and cohomology of some simple Shimura
varieties (2001), ch. VII; Wedhorn, Congruence relations on some Shimura varieties, J. reine angew.
Math. 524 (2000).

Known result: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and
correspondences. No trace is computed here. If a combination of pull-backs kills the Hodge–Tate
images of the Hodge classes of weight h, then the z^h coefficients of the local terms
det(1−zA)/det(1−A) at simple coincidences add up to zero. Source: M. F. Atiyah, R. Bott, A Lefschetz
fixed point formula for elliptic complexes II, Ann. of Math. 88 (1968) 451-491; G. Kondyrev, A.
Prikhodko, Holomorphic Atiyah-Bott formula for correspondences, Arnold Math. J. (2022); SGA5 III
6.12.

This file: Hodge–Tate images of distinct point classes on a projective variety are linearly
independent. Half of holomorphic Lefschetz formula: killed Hodge–Tate classes force vanishing local
term sums. Galois representation from cohomology: good reduction, Eichler–Shimura relation,
Hodge–Tate weights. -/

open CategoryTheory Function CommAlgCat CutsOutLocus IsUnimodCoords projSpace MvPolynomial Finset
  RingHom Fin CommAlg IsLocalization Away Field Submodule Algebra Ideal EtaleChart
  CartesianMonoidalCategory MonoidalCategory

attribute [local instance] FractionRing.liftAlgebra FormallyEtale.of_isSeparable

/-- Let k be an algebraically closed field mapping to Q̄_p, and Y projective over R with Y_k
having an atlas of dimension d. Then the images under λ_d of the distinct classes cl(z), z
in Y(k), form a k-linearly independent family.

Known result: Hodge–Tate images of point classes are non-zero and detect degrees of zero-cycles. -/
lemma linearIndepOn_hodgeTateMap_pointClass {p k} [Field k] [EmbeddedInQpBar p k] [IsAlgClosed k]
  {R} [Algebra R.1 k] {Y d} [hX : HasAtlas d (algPointsOf k R Y)] (hE : HasProjEmbedding Y.hom) :
  LinearIndepOn k (hodgeTateMap d) (.range (pointClass
  (X := algPointsOf k R Y) d)) := hE.rec @fun _ L _ hL ↦ by
  simp_rw [linearIndepOn_iff_notMem_span, ← Set.image_compl_preimage, Set.image_image,
    mem_span_image_iff_exists_fun]
  rintro _ ⟨z, rfl⟩ ⟨t, ht, n, H⟩
  have := Fact.mk hL
  choose a ζ w₀ ez hw₀ using exists_chart_coords L z (toIsField _)
  obtain ⟨_, _, q, m, hζ⟩ := isReduced_of_etale a.etale, FiniteType.isNoetherianRing k a.R,
    @exists_minimalPrimes_le _ _ (.colon ⊥ {(1 : a.R)}) _ (ker_isPrime ζ.1) (by aesop_cat)
  obtain ⟨_, γ, hψ⟩ := m.1.1, exists_eq_colon_of_mem_minimalPrimes m
  have ⟨ψ, V⟩ : ∃ ψ, ker ψ = q := ⟨algHom k .., q.ker_algebraMap_residueField⟩
  simp [← V, Ideal.ext_iff] at *
  choose n Λ e h using
    exists_isNoetherNormalization (k := k) (ne_iff.2 (hw₀.2.imp fun _ h ↦ (h.map ψ).ne_zero))
  let β := γ * evalForms Λ w₀ 0; let c := a.away β
  obtain ⟨⟨κ, ⟨⟩⟩, w, hw, w₁⟩ := (exists_toAway_comp_iff β (ofHom ψ)).2 (by
    simpa [β, comp_aeval_apply, *, ← sq] using hψ 1), (⟨_, hw₀.map_unit_smul (toAway β)
    (isUnit_of_dvd β (dvd_mul_left ..)).unit⁻¹, by simp [Units.smul_def]; rfl⟩ : ∃ w,
    IsUnimodCoords L _ w ∧ evalForms Λ w 0 = 1)
  obtain ⟨I, hg, u, E⟩ := injective_of_map_algebraMap_zero (M := .powers β) _ κ.1.1 fun r e ↦
    (isUnit_of_dvd β ⟨_, rfl⟩).mul_right_cancel (by simp [← map_mul, (hψ r).1 e]),
    hw.comp κ, (hw.comp κ).exists_unit_smul_eq ((hw₀.comp _).comp κ)
  obtain ⟨_, h, _, m, B⟩ := I.isDomain, eq_inv_smul_iff.2 E ▸ h _,
    hg.exists_mem_open_of_isUnit c.isOpenSub ⟨_, rfl⟩
  let y := aeval (R := k) (evalForms Λ w ∘ succ)
  algebraize [y.1, (κ.hom.comp y).1, κ.1.1, κ.1.1.comp y.1]
  let S := MvPolynomial (Fin n) k
  let M := IntermediateField.mk (.restrictScalars k (.algebraicClosure S q.ResidueField))
    fun _ ↦ .inv
  obtain ⟨⟨_, ⟨⟨φ⟩, ⟨⟩⟩, e⟩, _⟩ := @B (of k M) (⟨_, IsIntegral.isAlgebraic <| h.2 _ (cons 1 X) _
    .refl (funext (by simp [forall_fin_succ, y, *])) ·⟩) (.of_ker M.val 1 (by simp) .refl) (by
    simpa [← M.val.injective.ne_iff]), (faithfulSMul_iff_algebraMap_injective
    ..).2 (.of_ker y fun a _ ↦ by
    choose G c D using exists_homogenization (isHomogeneous_X _ 0) (a.rename succ) .refl
    simpa [D, comp_def, S, bind₁_rename] using h.1.map (aeval (cons (1 : S) X)) c (by
      erw [evalForms_map, ← comp_aeval]; simp [aeval_rename, y, *]))
  have G := IsAlgebraic.mk fun r ↦ (isAlgebraic_algebraMap_iff I).1
    (congr($(c.eq_comp_of_map_point_eq _ ((e.comp (ofHom M.val)).ext hg).symm) r ∈ M).mpr (φ.1 r).2)
  have ⟨δ, hδ, et⟩ := @exists_etale_of_isEtaleAt _ _ _ _ y.1.toAlgebra
    (.of_restrict_scalars_finitePresentation k ..) ⊥ _ (by
    delta IsEtaleAt Localization.AtPrime; rw [primeCompl_bot]; exact .comp _ (FractionRing S) _)
  let U := { c.away δ with coordinate := _, etale := congr($(comp_aeval _ (toAway δ).1).1.Etale).mp
                             (etale_algebraMap.2 et) }
  have e₃ := (c.mem_locus_away δ κ).2 (by simpa using! I.ne hδ)
  have o {A x v} (h : IsUnimodCoords L x v) h' ⦃T⦄ (b : T ⊆ (pointClass d ⁻¹' {pointClass d z})ᶜ) :
    x ∈ offPoints T A := fun K φ I ⟨y, m, e⟩ ↦ let := I.toField
    b m (pointClass_eq_of_functions_eq (hg.exists_function_const · |>.elim fun _ H ↦
      ez ▸ H (hw₀.comp ζ) (.of_ker _ _ hζ (E ▸ .smul
    (.id ..) _ .refl)) ▸ structureMap.1.injective (by simpa [e] using! H (h.comp φ) (.map _ h'))))
  choose b _ _ B T using hg.exists_mem_open_of_isUnit U.isOpenSub e₃
  obtain ⟨_, oU, F, q, r⟩ := e₃.choose.1.1.domain_nontrivial,
    o hw (.of_ker κ.1 1 (by simp [← I.eq_iff]) .refl),
    (G.1 (aeval w b)).exists_nonzero_coeff_and_aeval_eq_zero (by simpa [← I.ne_iff])
  obtain ⟨⟨⟩, ⟨q, m⟩, _, f, D⟩ := equiv_iff_eq.1 ⟨(c.away δ).nonempty_basis_kaehler.some.indexEquiv
    U.nonempty_basis_kaehler.some⟩,
    not_forall.1 (funext.mt q), exists_homogenization (Λ 0).2 (F.eval₂ (bind₁ (Λ ·.succ)).1 b) .refl
  let Q := projSpace.affinePoint (A := of k k) 0 q
  let Γ : Subfunctor (_ ⊗ projSpace k d) := ⟨fun _ x ↦ ∃ v h, IsUnimodCoords L x.1 v ∧ x.2 =
    projSpace.mk (evalForms Λ v) h,
    fun φ _ ⟨v, _, a, e⟩ ↦ ⟨φ ∘ v, evalForms_map Λ φ.1 _ ▸ ⟨_, a.comp φ, congrArg _ e⟩⟩⟩
  let π := Γ.ι ≫ fst ..
  have : Mono π := mono_of_app_injective (by
    rintro _ ⟨⟨⟩, _, _, a, ⟨⟩⟩ ⟨⟨⟩, _, _, a', ⟨⟩⟩ ⟨⟩
    congrm ⟨(_, $(mk_eq_mk_iff_exists_unit.2 ((a.exists_unit_smul_eq a').imp fun _ ↦
      (· ▸ (evalForms_smul _).symm)))), _⟩)
  let O := (offPoints t).preimage π ⊓ fieldLocus fun K x ↦ constMap Q K x = x.1.2 →
    x.1.1 ∈ U.locus K
  let j := O.ι ≫ π
  have hj {A} := injective_of_mono (j A)
  let C := U.comap j ⟨⟨(_, _), _, span_eq_top_of_isUnit 0 (by simp [*]), hw.comp _, rfl⟩,
    (offPoints _).2 _ (oU ht), fun _ _ _ _ ↦ ⟨_, rfl⟩⟩ rfl
  have P {A y} b : y ∈ C.locus A := (U.locus_comap j rfl).ge _
    (U.isOpenSub.fieldLocus_le _ (y.2.2 · · · (map_map_structureMap _ Q ▸ (congrArg _ b).symm)))
  obtain ⟨hV, s, hs⟩ := IsChartCovered.comap _ (h := ⟨fun K hK ↦ let := hK.toField
    by rintro ⟨⟨x⟩, _, H, ⟨a⟩⟩
       obtain ⟨c, κ, w, ⟨⟩, a'⟩ := exists_chart_coords L x hK
       obtain ⟨⟨u, ⟨⟩⟩, j, e⟩ := (a'.comp κ).exists_unit_smul_eq a, exists_isUnit_of_span_eq_top H
       exact ⟨(c.away _).comap π ⟨(_, _), _, span_eq_top_of_isUnit j
         (by simpa using (c.mem_locus_away ..).1 (point_mem_locus _)), a'.comp _, rfl⟩ rfl,
         (locus_comap _ π rfl).ge _ ((c.mem_locus_away ..).2 (by simpa [u.smul_def] using e))⟩⟩)
    (O.range_ι.substr (.inf (isOpenSub_offPoints.preimage _) (isOpenSub_fieldLocus fun _ _ ↦
    (IsSepFunctor.exists_ideal ..).elim fun _ h ↦
    (U.isOpenSub ..).imp' _ fun _ g _ φ f ↦ let := f.toField
    by erw [← map_map_structureMap φ Q, h, g, ← isAtom_top.ne_bot_iff_eq le_top, Ne,
      map_eq_bot_iff_le_ker, sup_le_iff, not_and]))),
    exists_isCoincidenceSet (constMap Q) (O.ι ≫ Γ.ι ≫ snd ..) (fun y b ↦ by
    obtain ⟨⟨ψ : U.R ⟶ _⟩, ⟨⟩⟩ := P b
    erw [← Functor.map_comp_apply, (U.lift_unique (π :=
      SqZeroExt.fst) fst_surjective_and_kerIdeal_sq ?_ fun j ↦ ?_ : _ ≫ _ = ψ)] <;> try rfl
    have := mk_eq_mk_iff_cross_mul (v := ψ ∘ _).1 b j.succ 0
    simp [w₁] at this ⊢; erw [this]; rfl) ![C] fun _ _ _ ↦ (⟨0, P ·⟩)
  have E {X} [HasAtlas d X] x := @(exists_diagonal_pointClass (X := X).choose_spec x).2.2 _
    ⟨fun A a b ↦ (hX.exists_ideal A (j.app A a) (j.app A b)).imp fun _ h B φ ↦
      hj.eq_iff.symm.trans (by erw [j.naturality_apply, j.naturality_apply]; exact h B φ)⟩ hV
  have J x t a := E x j t ⟨fun _ e ↦ hj (by erw [j.naturality_apply, e, map_map_structureMap]; rfl),
    a⟩
  exact (IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq ..).elim fun η l ↦
    hodgeTateMap_pointClass_ne_zero Q (l ▸ by simp [(h.pullback_injective
    hg (O := O) (fun V a ↦ ⟨⟨_, _, a, rfl⟩, o a V ht, fun K φ I e ↦ let := I.toField
    (mk_eq_mk_iff_exists_unit.1 e.symm).rec fun u e ↦ ((T ..).ext (a.map_unit_smul φ u) ▸ B (V.smul
      ..) (.mk0 _ fun H ↦ m (by simpa [aeval_bind₁ _, *, congrFun (((evalForms_smul _).trans
      (congrArg _ _)).trans e), ← comp_def, aeval_algebraMap_apply, F.eval₂_eq_sum_range,
      sum_range_succ'] using V.smul φ.hom u f (IsHomogSolution.refl.map _ f
      (by simpa [*, F.aeval_def, F.eval₂_eq_sum_range, aeval_bind₁ w]
      using! r)))) :)⟩) (hV.pairRestrictBijective.injective_restrictToPairs (by
    simp_rw [restrictToPairs_map, ← l, ← hodgeTateMap_map, E _ _ _ hs, map_zero, map_sum]
    exact sum_eq_zero fun y h ↦ (P (hs.2.1 _ h)).elim fun ζ a ↦ by
      rw [← sum_singleton (pointClass d), ← J (j.app _ y) {y} ⟨fun _ h ↦ by
        cases mem_singleton.1 h; simp [constMap]; rfl, fun K _ x e ↦
        ⟨y, mem_singleton_self y, hj (e.trans (j.naturality_apply _ y).symm)⟩⟩,
        not_ne_iff.1
        (oU .rfl _ (_ ≫ ζ.1) (toIsField _) ⟨_, ·, by simp [← a]; rfl⟩)]
      simpa [← hodgeTateMap_map, fun i : t ↦ (J _ ∅ ⟨nofun, fun K hK x e ↦ ((mem_offPoints_iff hK).1
        x.2.1 ⟨_, i.2, e⟩).elim⟩).trans sum_empty] using congr(PairH.map (freeAb.map j) $H).symm)) :
          η = 0)])

open AlgebraicGeometry Polynomial Functor

set_option backward.isDefEq.respectTransparency false

/-- Half of the Atiyah–Bott formula. Let Y/R be proper, W/R projective, k algebraically closed,
Y_E and W_k with atlases of dimension d. If h > d, or ∑ b_i λ_h(u_i^*x) = 0 for all x ∈
Hdg^q(Y_E), q ≤ d, then ∑ b_i[u_i] is h-null (`IsNullFamily`).

Known result: Half of the holomorphic Lefschetz (Woods Hole) formula for h-forms and
correspondences. -/
lemma ellAdicCohom.woods_hole {p A E k d h I} [CommRing A] [Field E] [CharZero E] [Algebra A E]
  [Field k] [IsAlgClosed k] [EmbeddedInQpBar p k] [Algebra E k] {R : Subalgebra A E} {W Y :
  Over (Spec (.of R))} [IsProper Y.hom] {u} {b : I →₀ k} (hX : HasAtlas d (algPointsOf E _ Y)) (hW :
  HasAtlas d (algPointsOf k _ W)) (hE : HasProjEmbedding W.hom) (hF : h ≤ d → ∀ q ≤ d, ∀ x :
  HodgeH _ q, (b.linearCombination k fun i ↦ hodgeTateMap h (x.map
  (freeAb.map ((algPoints E _).map (u i : W ⟶ Y)))).baseChange) = 0) : IsNullFamily u b d h := by
  intro c S P hP
  obtain ⟨⟨φ, _⟩, ⟨δ, hδ⟩, ⟨_, a, _⟩, L, e⟩ := Module.exists_dual_forall_apply_eq_one
    (linearIndepOn_hodgeTateMap_pointClass hE), exists_diagonal_local_terms hX, hW.2,
    (LinearMap.pi (@leval k
    _)).dualMap_surjective_of_injective (fun _ _ ↦ funext ∘ congrFun) (Polynomial.lcoeff k h)
  let D u : algPointsOf k _ W ⟶ restrictAlg E k ⋙ algPointsOf E _ Y := (algPoints ..).map u
  let Φ t (i : b.support) : type_of% δ →+ HodgeH (freeAb (algPointsOf ..)) _ :=
    (H.map _ (freeAb.map (scaledGraph t (D (u i)) (D c))) d).comp HodgeH.baseChange
  have T := (hP · · |>.elim (IsTangentPoly.hasJacobianRatio (c := D c) hW.isChartCovered))
  choose s _ B A using fun i : b.support ↦ exists_isCoincidenceSet (D (u i)) _ (hX :=
    isSepFunctor_algPoints) (fun _ e ↦ (T ⟨i, _⟩ (by congrm _ ≫ $e.1)).2 _ rfl e) a (by tauto)
  have hδ i t : Φ t i δ = _ := (hδ _ _ _ _ _ (by tauto) (T ⟨i, ·⟩ congr($(B _ _ ·).1) |>.1 t)).2
  have e := (congr($e <| · * Polynomial.C ·))
  simp [LinearMap.pi] at e
  refine (Set.ext fun _ ↦ ULift.down_inj.trans ⟨(by simpa using A _ _ (Field.toIsField k) _ ·),
    B _ _ ∘ by simp⟩ : S = univ.sigma s) ▸ ⟨finite_toSet _, .trans (by
    simp [*, ↓finsum_mem_coe_finset, ← sum_fn, mul_sum, sum_sigma, division_def, mul_assoc,
    AddMonoidHom.pi]) ((∑ i, b i.1 • L.toAddMonoidHom.comp
    (.pi ((φ ∘ₗ hodgeTateMap d).toAddMonoidHom.comp <| Φ · i))).ker.1.closure_le.2 ?_ (kunneth δ))⟩
  intro δ ⟨q, _, _, x, _, r⟩
  have F t i : Φ t i δ = .map (freeAb.map (CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _)) ≫
    freeAb.prod ..) _ := (congrArg _ (((congrArg _ r).trans (HodgeH.baseChange_map ..)).trans
    (congrArg _ ((@HodgeTest.baseComparison k _ E _ _).pull_cup abTensor_hom_ext x ..)))).trans
    ((H.map_comp ..).symm.trans (cup_map (Functor.mulPairing _) x.baseChange _ _
    (HodgeTest.scaleModule t _ ≫ Functor.whiskerLeft _ (freeAbMap (D _)))
    (Functor.whiskerLeft _ (freeAbMap (D c))) freeAb.hom_ext))
  simpa [F, e, H.map_comp, hodgeTateMap_map (_ ≫ _), hodgeTateMap_cup, hodgeTateMap_scale, ← sum_fn,
    AddMonoidHom.pi,
    -LinearMap.smul_apply, -LinearMap.coe_smul, ← @eval_X_pow k, -Polynomial.eval_pow] using!
    congrArg (φ ∘ₗ PairH.map _ ∘ₗ _) ∘ (sum_attach ..).trans ∘ (hF · q (by omega) x)

seal ellAdicCohom

open Matrix Module ellAdicCohom LinearMap Flat Filter IsEigenQuotient ModuleCat.Algebra Int

attribute [local simp] Model.cosetSum cosetFn smul_sum baseChange_comp
  ValuationSubring.valuation_eq_one_iff

/-- For a model of neat level over a localisation of O_E where safe primes survive, σ : ℂ ≅
ℚ̄_ℓ, and J supported at σ|E, in weights where θ occurs, some continuous ρ : Gal(Ω/E) →
GL_N(ℚ̄_ℓ) satisfies `SphericalClause` at each safe w, with jumps including J and the
Hecke polynomial of σθ_w.

Known result: Galois representation cut out of cohomology by a Hecke eigensystem;
Eichler-Shimura. -/
lemma Model.exists_galois_rep {E} [Field E] [CMBase E] {a d₀} [HasQuadSubfield _ E] {𝔑 ν R}
    (X : Model (Fin a) d₀ 𝔑 ν R) {ℓ} [NeZero a] (hN : IsNeat (Fin a) 𝔑) [ThePrime ℓ] [Algebra E Ω] M
    (hM : ∀ w, IsSafe 𝔑 w → M ≤ w.1.primeCompl) [_root_.IsLocalization M R] [PadicIso ℓ] (θ :
  SafePlace 𝔑 → _) J (hJ : ∀ u ∈ J, 0 ≤ u ∧ OccursInWeight a ν θ u.toNat) : ∃ ρ : PadicRep _ ℓ,
  Continuous ρ.rep ∧ ∀ w, SphericalClause ρ.rep
  OccursIn (if algebraMap E ℂ = · then J else 0) w.1.1 (heckePoly w.1.1.q a (ιℓ <| θ w ·)) := by
  rcases X.smooth, X.proper, X.projective, X.reduction,
    IsLocalization.isNoetherianRing M R inferInstance
  have := (X.covering · |>.smoothOfRelativeDimension_baseChange X.d)
  have ⟨_, _, _⟩ : IsCharted X.Z R ∧ IsCharted X.Z Ω ∧ ∀ i, IsCharted (X.W i) Ω := by
    and_intros <;> intros <;> exact ⟨(hasAtlas_algPoints X.d).exists_isCharting⟩
  choose hV V using fun n i ↦ transfer (X.covering i) ℓ n
  choose l p _ using fun w : SafePlace 𝔑 ↦
    (Eventually.all (X.eventually_translate ∅ <| heckeIsogeny_mem_GUPlus w.1 ·)).exists
  choose T hT' ht hW using fun n : Set.Iic (X.d + X.d) ↦ exists_commuting_tau_ops (hV n) (V n) p
  have e n w b := congr((baseChangeHom ℤ_[ℓ] Bcris .. ∘ₗ restrictScalarsₗ ..) $(ht n w b))
  simp [LinearMap.ext_iff, -Subtype.forall, heckeSum] at e ht
  have hT i s (g : Gal(Ω/E)) : Commute (T i s) ((galoisAction ..) g) :=
    LinearMap.ext fun x ↦ hV _ (l s.1) (by simp [ht, map_galoisAction])
  obtain ⟨N, r, F, ⟨h₃, H⟩, hr⟩ := exists_isEigenQuotient (ιℓ ∘ ↿θ) hT (continuous_galoisAction · E)
  use ⟨r⟩, hr, fun w A hA ↦ ?_
  have hR r : algebraMap (CommRingCat.of R) Ω r ∈ A :=
    A.mem_of_valuation_le_one _ ((IsLocalization.surj M r).rec
    fun x e ↦ le_of_mul_le_of_one_le_left (by simpa using! A.valuation_le_one ⟨_, congr(algebraMap
    R Ω $e ∈ A).mpr (algebraMap_ringOfIntegers_mem ..)⟩) (not_lt.1 (hM _ w.2 x.2.2 ∘ (hA _).1)))
  have hcr [PadicPlaceEmbedding E A ℓ] i := (isCrystalline_and_linearFrob_rel E hR i
    (X.m ∘ ![]) 0 1 0 (by simp [CongruenceRelation, Cancels]) nofun).1
  obtain ⟨⟨t, f, -, hp, _, hq⟩, C⟩ := w.1.1.1.exists_prime_and_absNorm_eq_pow,
    X.congruence _ w.2 _ (algebraMap _ Ω ⁻¹' A.nonunits) (hA · |>.2) (p w)
  rw [heckePoly, ← hA, ← @fact_iff t.Prime] at *; norm_cast at *
  refine ⟨⟨fun _ _ _ ↦ Units.ext (toLin'.injective (ext_on_range H.1 fun _ ↦ (h₃ ..).trans (by
    simp [*, galoisAction_eq_one_of_inertia hR _ hp]))), isCrystalline ⟨by tauto, H⟩ (hcr ·)⟩,
    fun he γ s hs u hu z ↦ ?_, fun s hs ↦ ⟨fun h ↦ ?_, @fun he _ k o ↦ ?_⟩⟩
  · simp [apply_ite] at hu
    obtain ⟨⟨h, rfl⟩, hO⟩ := (hJ u hu.2).imp_left le.dest
    let ε := ιℓ.trans s.toRingEquiv
    let : EmbeddedInQpBar ℓ ℂ := {ε.toRingHom.toAlgebra with}
    refine (exists_word_kill_of_jump_eq_zero ⟨by tauto, H⟩ (hcr ·) hs (by tauto) hT' z).rec fun c
      ⟨_, n⟩ ↦ hO _ (ε.symm ∘ c) (ε.injective (by simpa [map_list_prod])) fun b ↦
      X.isNullHecke_of_isNullFamily hN ((c.support.eventually_all.2 fun L _ ↦ .all (hW · ℂ L _
      b.2.1)).mono fun l a m ↦ woods_hole (hasAtlas_algPoints _) (hasAtlas_algPoints _)
      (X.projective l) fun hh q hq x ↦ (exists_hasHodgeTateWeight hR (fun r ↦ congr(ε
      ($(hu.1) r)).trans (by simp [ε])) X.d ε.symm ε.right_inv (x.map (freeAb.map
      ((algPoints ..).map (X.m m))))).rec fun v ⟨Θ, hv, K⟩ ↦ .trans ?_ ((sum_congr rfl fun L hL ↦
      congrArg (ε.symm (c L) • ·) (a L hL ⟨_, add_le_add hq hh⟩ (.mk' (Θ <| ·.restrictScalars _
      |>.baseChange _ v) (by simp)))).trans ?_))
    · simp [← K, HodgeH.map_comp]
    simpa [Finsupp.linearCombination, Finsupp.sum, c.support.sum_comm, smul_comm (ε.symm _)]
      using congr(cosetSum (fun g ↦ Θ (baseChange _ _ $(n ⟨_, _⟩ v hv))) b.1)
  · refine toLinAlgEquiv'.injective (ext_on_range H.1 fun ⟨i, x⟩ ↦ ?_)
    simp [↓Polynomial.C_mul', -cast_mul]
    conv_lhs => enter [2, b]; erw [mul_smul, cast_smul_eq_zsmul, ← map_pow (matrixRep r),
      h₃, ← H.2.1 _ (w, b), ← _root_.map_zsmul]
    rw [← _root_.map_sum, congrArg (F i) (hV _ (l w) ?_), map_zero]
    simpa [ht, sum_filter, sum_comm, (finrank_le _).trans_eq]
      using ellAdicCohom.congruence_relation hR (by simpa) hp (hq.rec hs) _ _ _ (C hq) x
  exact IsEigenQuotient.isKilledBy ⟨by tauto, H⟩ (w, ·) (hcr ·) o fun i y ↦
    lTensor_preserves_injective_linearMap (.restrictScalars ℤ_[ℓ] _) (hV i (l w)) (by
    simpa [← baseChange_eq_lTensor, e, sum_filter, sum_comm, (finrank_le _).trans_eq,
      ↓LinearMap.sum_apply] using! congr($((isCrystalline_and_linearFrob_rel E hR _ _ _ _ _ (C
      (o.eq_pow_of_isFrob (_root_.map_inv he.toGp _ ▸ he.isFrob_iff.2 hs))) fun _ ↦ o.pow _).2) y))
end
