import Lib.Shimura.ProjectiveSpace

section
/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Projective embeddings by linear systems: properness, closed immersions, Segre, affine
charts. Tensor products and powers of line bundles; Segre and Veronese embeddings. -/

open AlgebraicGeometry CategoryTheory CommRingCat Finset PointFn Function MvPolynomial ProjSpace
  TopologicalSpace Over

variable {X Y S ι κ} {L : LineBundle X ι} {s : X ⟶ S} {Λ : Type} [Fintype Λ] {ν : Λ → _}
  (N : ∀ l, LineBundle X (ν l))

instance [h : HasProjEmbedding s] : IsProper s := h.rec (·.2.1)

lemma LineBundle.IsProjEmbedding.ext (h : L.IsProjEmbedding s) {a b : Y ⟶ X} (e : L.pull a =
  L.pull b) (o : a ≫ s = b ≫ s) : a = b := hom_ext_of_cover (L.pull a) fun i A t x ↦
  h.2.2 ⟨x, (e ▸ x :), (congr(($e).transition i · A t))⟩ (t ≫= o)

/-- If the linear system L embeds X projectively over S along s: X → S
(`LineBundle.IsProjEmbedding`) and p: Y → X is a closed immersion, then p*L embeds Y projectively
over S along s∘p. -/
lemma LineBundle.IsProjEmbedding.comp : L.IsProjEmbedding s → ∀ p [@IsClosedImmersion Y X p],
  (L.pull p).IsProjEmbedding (p ≫ s)
  | ⟨l, _, H⟩, p, _ => ⟨l.pull p, {}, ((cancel_mono p).1 <| H · ·)⟩

/-- Segre embedding of a tower: if L embeds X over S along s, and N embeds S over S' along b (any
index sets), then L ⊗ s*N embeds X over S' along the composite. -/
lemma LineBundle.IsProjEmbedding.mul {N b} : L.IsProjEmbedding s → @IsProjEmbedding S Y κ N b →
  (L.mul (N.pull s)).IsProjEmbedding (s ≫ b)
  | ⟨l, _, H⟩, ⟨k, _, G⟩ => ⟨l.mul (k.pull _), {}, by simp_all; grind [→ transition_self]⟩

/-- If L, with finitely many coordinates ι, is a projective embedding for s: X → S, then L is
the pull-back of O(1), cover and transition functions included, along a closed immersion of
X into ℙ^ι × S over S. -/
lemma LineBundle.IsProjEmbedding.exists_isClosedImmersion [Finite ι] (h : L.IsProjEmbedding s) :
    ∃ j, IsClosedImmersion j ∧ j ≫ Limits.prod.snd = s ∧
  ((hyperplaneBundle ι).pull Limits.prod.fst).pull j = L := (h.1.exists_hom_projSpace s).imp fun j
  a ↦ ⟨(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨@.of_comp _ _ _ _ _ (a.1 ▸ h.2.1)
  isProjEmbedding_projSpace.2.1.1, ⟨by intros; apply h.ext <;> grind [=_ pull_comp]⟩⟩, a⟩

/-- If L embeds X in projective space over Spec R, then each U_i is affine and the chart map
R[X_j] → Γ(X, U_i), X_j ↦ g_ij (the transition function), is surjective. -/
lemma LineBundle.IsProjEmbedding.exists_affine_chart [Finite ι] {R s} (h :
  @IsProjEmbedding X (Spec R) ι L s) i : ∃ u : IsAffineOpen _, ∃ φ : MvPolynomial ι R →+* Γ(X,
  L.opens i), Surjective φ ∧ specMap (φ.comp C) = u.fromSpec ≫ s ∧ ∀ {A t}, LandsIn t (L.opens i) →
  ∀ P, ofSection (φ P) A t = eval₂Hom (Spec.preimage (t ≫ s)).hom (L.transition i · A t) P := by
  obtain ⟨⟨f, _, _, e⟩, W⟩ := h.exists_isClosedImmersion, @(isAffineOpen_chart i).preimage _ _ _ _
    (MorphismProperty.of_isPullback (.flip (.of_hasBinaryProduct' _ (Spec R))) inferInstance)
  refine have u := e ▸ W.preimage f; have I := by simpa using landsIn_fromSpec u (𝟙 _)
      ⟨u, eval₂Hom (Spec.preimage (u.fromSpec ≫ s)).hom (L.transition i · _ u.fromSpec), ?_, by
        simp [specMap], (map_evalSection_fromSpec u · ▸ by simp [(h.1.1 ..).1 _, I, hom_eval₂])⟩
  obtain ⟨⟨⟩, t, _, k⟩ := e,
    @exists_isHomogCoords (Spec R) _ ⟨_⟩ i (update .X i 1) (specMap C) (by simp)
  use have T := (k i).1.2 (by simp); (f.app_surjective _ W).forall.2 fun s ↦ ⟨_,
      (isRegularOn_ofSection s (ofHom (eval₂Hom ..)) t T).symm.trans
      ((congrArg _ (?_ : _ = _ ≫ f)).trans (ofSection_map_fromSpec u _ (𝟙 _)))⟩
  refine isProjEmbedding_projSpace.2.2 ⟨T.comp _,
    I, ?_⟩ ?_ <;> simp_all [↓((isLinearSystem_hyperplaneBundle.pull _).1 ..).1 _, ↓k i,
    ← Spec.map_comp, ← ofHom_comp, update, apply_ite, transition_self]

attribute [local simp] IsRegularOn LineBundle.transition_self landsIn_iInf

/-- The tensor product of the N_a over a in s (by default all a), on the common refinement of
all covers; for linear systems, the Segre product. -/
@[simps -fullyApplied] noncomputable def LineBundle.pi (s : _ := @univ Λ _) := mk
    (fun i : ∀ l, _ ↦ ⨅ a, (N a).opens (i a)) fun i j ↦ ∏ a ∈ s, (N a).transition (i a) (j a)

/-- The m-th tensor power of L, indexed by m-tuples of indices; for a linear system, the
Veronese system of all monomials of degree m. -/
noncomputable def LineBundle.pow (L : LineBundle X ι) m := pi fun _ : Fin m ↦ L

variable {S : _} {Λ : Type} [Fintype Λ] {ν : Λ → _} {N : ∀ l, LineBundle X (ν l)} {ι : Type} {L :
  LineBundle X ι} {Y : Scheme} (p : Y ⟶ X) (m)

@[simp] lemma LineBundle.picClass_pi s : (pi N s).picClass = ∑ l ∈ s, (N l).picClass :=
  .symm (by induction s using
  cons_induction <;> simp [*] <;> (apply picClass_eq_of_le (by tauto)) <;> simp [iInf_le, *])

lemma LineBundle.IsLinearSystem.pi (h : ∀ a, (N a).IsLinearSystem) :
  (LineBundle.pi N).IsLinearSystem := by
  simp_all [IsLinearSystem, IsHomogCoords, forall_and, Ring.eq_mul_inverse_iff_mul_eq,
    ← prod_mul_distrib]
  use fun _ _ _ _ a _ ↦ prod_eq_zero (mem_univ a) (by grind), by grind

lemma LineBundle.pull_pi : (pi N).pull p = pi (N · |>.pull p) := by ext <;> simp [Opens.coe_iInf]

/-- Segre: let W be proper over S, with finitely many S-maps π_l: W → Z_l that jointly separate
morphisms into W over S. If each N_l satisfies `LineBundle.IsProjEmbedding` on Z_l, so does the
Segre product of the π_l^*N_l on W. -/
lemma LineBundle.isProjEmbedding_pi {W : Over S} [IsProper W.hom] {Z : Λ → _} (π : ∀ l, W ⟶ Z l)
  {N : ∀ l, LineBundle _ (ν l)} (h : ∀ l, (N l).IsProjEmbedding (Z l).hom) (H : ∀ {T} {x y : T ⟶ W},
  (∀ l, x ≫ π l = y ≫ π l) → x = y) : (pi fun l ↦ (N l).pull (π l).left).IsProjEmbedding W.hom :=
  ⟨.pi (h · |>.1.pull _), {}, fun {c A a b} g
  o ↦ congr($(@H (.mk _) (homMk a o) (homMk b) fun l ↦ by ext; exact (@(h l).2.2 (c l) A (a ≫ _)
  (b ≫ _) (have := (g.2.2 <| update c l ·); by simp_all [prod_eq_single l]) (by simpa))).1)⟩

@[simp] lemma LineBundle.picClass_pow : (L.pow m).picClass = m • L.picClass := by simp [pow]

lemma LineBundle.IsProjEmbedding.pow {s} (h : @IsProjEmbedding X S _ L s) {m} (hm : m ≠ 0) :
  (L.pow m).IsProjEmbedding s := @isProjEmbedding_pi _ _
  _ _ (.mk s) h.2.1 _ (fun _ ↦ 𝟙 _) _ (by tauto) (· ⟨_, hm.pos⟩)
end

section
/-! Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion
(known result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Abelian schemes with ring action, translations, Picard pairing, parallelogram law:
definitions. Spec of algebras as schemes over a ring; full faithfulness. Kernel of a finite
homomorphism is the spectrum of a finite algebra. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Adjunction
  CommRingCat Over Equiv Obj AddMonObj AddGrpObj Functor Over.OverMorphism Spec MorphismProperty
variable {S S' : Scheme.{0}} (b : S' ⟶ S) (O : outParam Type) [CommRing O] (A : Over S)

/-- A commutative group object. -/
class abbrev AddObj := AddGrpObj A, IsCommAddMonObj A

attribute [instance] Hom.addCommGroup

export AddMonObj (comp_add add_comp comp_nsmul nsmul_comp comp_zero)

/-- An action of the commutative ring O on a commutative group object A: O-module structures on
all groups Hom(T, A), functorial in T. -/
class ModuleObj [AddObj A] where
  [homModule (T) : Module O (T ⟶ A)]
  comp_smul {T' T} (a : T' ⟶ T) (c : O) x : a ≫ (c • x : _ ⟶ A) = c • a ≫ x

attribute [reducible, instance] ModuleObj.homModule

/-- The commutative group scheme A over S is an abelian scheme: it is smooth and proper over S,
and multiplication by every m ≠ 0 is surjective. -/
class IsAbelianScheme extends AddObj A, Smooth A.hom, IsProper A.hom where
  nsmul_surjective : ∀ m ≠ 0, Surjective (m • 𝟙 A).left

variable {A B T X Y : Over S} [AddObj A] [AddObj B] {R : outParam _} [CommRing R] [ModuleObj R A]
  [ModuleObj R B] (c : R) (f : A ⟶ B)

/-- The morphism p : B → A makes B the base change of A along b : S' → S, and composing with p is
R-linear on U-points for every S'-scheme U. -/
structure IsGroupBaseChange {B} [AddObj B] [ModuleObj R B] (p :
  (CategoryTheory.Over.map b).obj B ⟶ A) where
  isPullback : IsPullback p.left B.hom A.hom b
  linear {U} : IsLinearMap R (@(CategoryTheory.Over.map b).map U _ · ≫ p)

/-- The morphism f : A → B of commutative group objects is a homomorphism: composing with f is
additive on U-points for every U. -/
abbrev IsAdditive := IsAddMonHom f

/-- Isogenies: finite, flat and surjective homomorphisms. -/
class abbrev IsIsogeny := IsAddMonHom f, IsFinite f.left, Flat f.left, Surjective f.left

/-- The morphism f from A to B is a homomorphism of group objects that commutes with
multiplication by every c in R. -/
class IsLinear extends IsAddMonHom f where smul_id_comp (c : R) : (c • 𝟙 A) ≫ f = c • f

variable {f}

@[simp] lemma IsLinear.smul_comp [h : IsLinear f] t : (c • t : T ⟶ A) ≫ f = c • t ≫ f := by
  grind [t ≫= h.2 c, ModuleObj.comp_smul]

attribute [simp] comp_add ModuleObj.comp_smul add_comp comp_neg comp_sub sub_comp comp_nsmul
  nsmul_comp comp_zsmul zsmul_comp

/-- A morphism f : A → B of commutative group schemes that is additive on the two projections A
× A → A is a homomorphism. -/
lemma isAdditive_of_universal (h : (fst A A + snd ..) ≫ f = fst .. ≫ f + snd .. ≫ f) :
  IsAdditive f := ⟨by simpa [comp_add_assoc] using! 0 ≫= h, by simpa [add_eq_add]⟩

instance (priority := low) : ModuleObj ℤ A := ⟨by simp⟩

omit [ModuleObj R A] in instance [IsAdditive f] : IsAdditive (c • f) :=
  isAdditive_of_universal (by simp)

@[irreducible] instance pullbackAddObj : AddObj ((pullback b).obj A) where
  add_comm := by simp [← LaxBraided.braided_assoc, ↓← Functor.map_comp, IsCommAddMonObj.add_comm]

instance : ModuleObj R ((pullback b).obj A) where
  homModule _ := AddEquiv.module _ (.symm ⟨(mapPullbackAdj b).homEquiv .., by
          delta pullbackAddObj; simp [Adjunction.homEquiv, Functor.map_add']⟩)
  comp_smul := by simp [smul_def, ← homEquiv_naturality_left, homEquiv_counit]

variable (c : Pic A.left) (x y : T ⟶ A) (f : X ⟶ Y) (z : 𝟙_ _ ⟶ A)

instance [IsIso f] : IsIso f.left := map_isIso (forget S) f

instance [IsProper X.hom] [IsSeparated Y.hom] : IsProper f.1 := by simp_all [IsProper.of_comp _ Y.3]

instance {X Y S d} f g [@SmoothOfRelativeDimension d X S f] :
    @SmoothOfRelativeDimension d _ Y (Limits.pullback.snd f g) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange d).1 (.of_hasPullback ..) ‹_›

/-- The spectrum of an R-algebra B, as a scheme over Spec R. -/
abbrev specOver R B [CommRing.{0} R] [CommRing B] [Algebra R B] :=
  CategoryTheory.Over.mk (Spec.map (ofHom (algebraMap R B)))

/-- Translation by a section z of A over S: the S-morphism x ↦ x + z from A to itself. -/
@[simp] abbrev translation := 𝟙 A + toUnit A ≫ z

instance : IsIso (translation z) := ⟨translation (-z), by simp⟩

namespace Pic

/-- For c in Pic A and a T-point x of A, the pull-back x^*c in Pic T. -/
def atPoint := c.pull x.left

/-- For c in Pic A and T-points x, y of A, the class ⟨x, y⟩ = (x + y)^*c − x^*c − y^*c + 0^*c in
Pic T. -/
def pairing := c.atPoint (x + y) - c.atPoint x - c.atPoint y + c.atPoint 0

/-- The parallelogram law for a class c in Pic A: (x+y)^*c + (x−y)^*c + 2·0^*c = 2(x^*c + y^*c)
in Pic T for all T-points x, y of A and all S-schemes T. -/
def ParallelogramLaw := ∀ ⦃T⦄ x y,
  @atPoint _ _ T c (x + y) + c.atPoint (x - y) + 2 • c.atPoint 0 = 2 • (c.atPoint x + c.atPoint y)

end Pic

variable {R C D : Type} [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
  {E : Type} [CommRing E] [Algebra R E] (φ : C →ₐ[R] D) (ψ : D →ₐ[R] E)

/-- For an R-algebra homomorphism φ: C→D, the induced morphism Spec D → Spec C of schemes over
Spec R. -/
def specOver.map : specOver R D ⟶ specOver R C :=
  Over.homMk (Spec.map (ofHom φ)) (by simp [← Spec.map_comp, ← ofHom_comp])

@[reassoc] lemma specOver.map_comp : map ψ ≫ map φ = map (ψ.comp φ) :=
  OverMorphism.ext (Spec.map_comp ..).symm

@[simp] lemma specOver.map_id : map (.id R C) = 𝟙 _ := OverMorphism.ext (Spec.map_id _)

lemma specOver.map_bijective : (map : (C →ₐ[R] D) → _).Bijective := ((Equiv.mk
  (CommAlgCat.ofHom · |>.op) (·.1.1)).trans (@algSpec.fullyFaithful ⟨R⟩).homEquiv).bijective

variable {R : _} [CommRing R] {A B : Over (Spec ⟨R⟩)} {f : A ⟶ B}

lemma locallyOfFinitePresentation_left [g : LocallyOfFiniteType B.hom] [h :
  LocallyOfFinitePresentation A.hom] :
  LocallyOfFinitePresentation f.left := by solve_by_elim (maxDepth := 20) [(f.1.appLE_comp_appLE ..
  ▸ (f.w ▸ h).1 .. :).of_comp_finiteType, g.1, isAffineOpen_top]

lemma exists_isPullback_SpecMap {X Y} f [@IsAffineHom.{0} X Y f] {C} i :
    ∃ P φ j, IsPullback j (@Spec.map C P φ) f i := ⟨_, _, _, .of_iso_pullback
  ⟨by simp [Limits.pullback.condition]⟩ (Scheme.isoSpec _).symm rfl (Spec.map_preimage _).symm⟩

lemma eq_zero_iff_factors_zero_section [AddObj B] : f = 0 ↔ ∃ l, l ≫ ζ[B].left = f.left :=
  ⟨by aesop, fun ⟨l, e⟩ ↦ by ext; simp [CategoryTheory.Hom.zero_def, ← f.w, ← e]⟩

variable [AddObj B] [IsSeparated B.hom]

instance : IsClosedImmersion ζ[B].left := of_postcomp _ _ _ ‹_› (by simp; infer_instance)

/-- Let B be a separated commutative group scheme over R and f : A → B finite. The fibre of f
over the zero section is represented by a closed subscheme Spec S of A, S a finite
R-algebra, flat if f is flat. -/
lemma exists_finite_kernel_ring (F : IsFinite f.left) : ∃ (S : CommAlgCat R) (ι : specOver R S ⟶ A),
  Module.Finite R S ∧ (∀ [Flat f.left], Module.Flat R S) ∧ IsClosedImmersion ι.left ∧ ι ≫ f = 0 ∧
  ∀ ⦃T⦄ (y : T ⟶ A), y ≫ f = 0 → ∃ z, z ≫ ι = y := (exists_isPullback_SpecMap _ ζ[B].1).elim fun P
  ⟨φ, i, H⟩ ↦ ⟨@.of .., homMk i (by simpa using! H.w =≫ B.3), by simpa using! of_isPullback H F,
  Flat.SpecMap_iff.1 (of_isPullback H ‹_›), of_isPullback H.flip inferInstance, by ext; exact H.w,
  fun _ _ h ↦ ⟨homMk _ (H.lift_snd _ _ congr($h.1)), by aesop⟩⟩
end
end
