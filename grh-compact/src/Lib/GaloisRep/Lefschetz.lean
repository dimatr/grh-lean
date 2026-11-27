import Lib.Shimura.SeparatingPoints
import Lib.GaloisRep.WildType
import Lib.GaloisRep.MarkedPairs
import Lib.Shimura.DrinfeldLifting

-- part: Lib.General.Geometry.SmoothnessCriterion
section
/-! General lemmas of algebraic geometry (textbook or folklore).

This file: Smoothness from a tangent bound and an immersed generic holomorphic family. -/

open CategoryTheory AlgebraicGeometry Spec Set IsLocalRing CommRingCat TrivSqZeroExt Algebra Module
  TensorProduct MvPolynomial KaehlerDifferential IsLocalization.Away Localization LinearMap RingHom
  Cardinal PointFn HasRingHomProperty IsStandardSmoothOfRelativeDimension
attribute [local simp] map_inj ConcreteCategory.hom_ext_iff

/-- Let X be locally of finite type over a normal domain R ⊂ ℂ, φ a d-parameter family of
complex points over R, immersive at b, with φ(b) specialising to nearby members, and a: Spec
V → X extend φ(b). If the relative tangent space at the closed point of a has dimension ≤ d,
X is smooth of relative dimension d on an open set containing a. -/
lemma smooth_of_immersion {d X R b u k} {φ : (Fin d → ℂ) → _} {V : ValuationSubring ℂ}
  {a} [Field k] {ϑ : V →+* k} [IsLocalHom ϑ] (s : X ⟶ Spec R) [LocallyOfFiniteType s] [IsDomain R]
  [IsIntegrallyClosed R] (h : IsHolImmersionAt φ b) (ha : specMap V.subtype ≫ a = φ b) (hs : ∀ w,
  φ w ≫ s = Spec.map u) (hi : (⇑u).Injective) (hg : ∀ᶠ w in nhds b, φ b (closedPoint ℂ) ⤳ φ w
  (closedPoint ℂ)) (H : ∀ (M : ModuleCat k) τ, let t := specMap ϑ ≫ a; sqZeroReduction k _ ≫ τ = t →
    τ ≫ s = specMap (algebraMap k _) ≫
  t ≫ s → (∀ l, specMap (map (Dual.eval k M l)).1 ≫ τ = specMap (algebraMap k _) ≫ t → l = 0) →
  finrank k M ≤ d) : ∃ U, LandsIn a U ∧ SmoothOfRelativeDimension d (U.ι ≫ s) := by
  have ⟨W, hW, hb⟩ := exists_isAffineOpen_landsIn a
  let B := Γ(X, W)
  obtain ⟨⟨ρ, hρ⟩, α, rfl⟩ := map_surjective (hW.fromSpec ≫ s), landsIn_opensRange.1
    (hW.opensRange_fromSpec ▸ hb)
  have := Spec_iff.1 (hρ ▸ locallyOfFiniteType_comp ..)
  algebraize [ρ.hom, ϑ.comp α.1]
  have ⟨ι, x, _, hx, li⟩ := exists_linearIndependent' k (mk B k _ 1 ∘ D R B)
  simp [range_comp _ (D ..), ← Submodule.baseChange_span, span_range_derivation] at hx
  have ⟨i⟩ : #ι ≤ #(Fin d) := by grw [li.cardinalMk_le_finrank, ← Subspace.dual_finrank_eq,
    H (.of k _) (specMap {toFun b := .inl (ϑ (α b)) + .inr (applyₗ (mk B k _ 1 (D R B b))), ..} ≫
    hW.fromSpec) _ _ fun l ↦ ext_on_range hx ∘ _] <;> simp [← hρ, ← Spec.map_comp, B,
    ← map_comp_assoc, cancel_mono, forall_and, TrivSqZeroExt.ext_iff, tmul_add,
    ← algebraMap_toAlgebra ρ.hom] <;> tauto
  obtain ⟨z, rfl⟩ := i.2.surjective_comp_right x
  let p := PrimeSpectrum.comap (algebraMap B k) ⊥
  let A := MvPolynomial (Fin d) R
  let e := mvPolynomialBasis R (Fin d)
  algebraize [(Ideal.ResidueField.liftₐ p.1 (ofId ..) le_rfl fun _ ↦ .mk0 _).1, (eval₂AlgHom R z).1]
  obtain ⟨hw, _, _, _ : IsIntegrallyClosed (MvPolynomial (Fin d) R)⟩ := ha ▸ hb.comp _,
    FiniteType.of_restrictScalars_finiteType R A B, IsStandardSmooth.of_basis_kaehlerDifferential e
    (by simp [e]), d.rec (.of_equiv (isEmptyRingEquiv ..).symm) fun _ _ ↦ .of_equiv
    (finSuccEquiv R _).symm.toRingEquiv
  have ⟨f, hf, C, π, hπ⟩ := (unramifiedLocus_eq_compl_support.ge (
    have := (mem_support_iff_nontrivial_residueField_tensorProduct p).1 ·
    have := (AlgebraTensorModule.cancelBaseChange B p.1.ResidueField k k Ω[B⁄A]).symm.nontrivial
    ne_zero_of_surjective (baseChange_surjective k (map_surjective R A _)) (ext_on_range hx (by
    simp [← (id (aeval_X ..) : algebraMap A B _ = _)]))) :
    IsUnramifiedAt A _).exists_hasStandardEtaleSurjectionOn
  obtain ⟨⟨β, rfl⟩ : ∃ β, ofHom (algebraMap B (Away f)) ≫ β = α, ⟨⟨G⟩⟩, r⟩ := ⟨_, hom_ext (lift_comp
    _ (.of_map ϑ _ (.mk0 _ hf)))⟩, instIsStandardEtaleRing C,
    (isRegularOn_ofSection · |> (h.1 · hw))
  algebraize [β.1, β.1.comp (algebraMap A _)]
  have hx := (G.hasMap.map π).map (algHom _ _ V)
  with_unfolding_all have := (faithfulSMul_iff_algebraMap_injective A V).2 (.of_ker _ fun Q hQ ↦
   map_injective _ hi (funext (eq_zero_of_submersion (.eval_mvPolynomial _)
   (hasStrictFDerivAt_pi.2 (z · |> r |>.2.hasStrictFDerivAt)) (ker_eq_bot_iff_range_eq_top.1
   (bot_unique fun v h0 ↦ h.2 v ((h.1.exists_isJet _).elim fun τ hτ ↦ by
   convert hτ
   obtain ⟨τ, rfl⟩ :=
     landsIn_opensRange.1 (hτ _ 0 (landsIn_opensRange.2 ⟨β ≫ _, by simpa using ha⟩)).1
   algebraize [τ.hom.comp (algebraMap A _)]
   simpa [← hτ.fst_comp, specMap] using congr(specMap $((FormallyUnramified.of_surjective π hπ).ext'
     _ ⟨2, kerIdeal_sq ℂ ℂ⟩ ⟨(inlHom ..).comp ((fstHom ..).1.comp τ.hom), fun Q ↦ by
     have := And.intro (hτ.comp_base_eq hs) (hτ W <| z ·)
     simp [← hρ, ← map_comp_assoc, ← Spec.map_comp, funext_iff] at this h0
     apply Q.induction_on <;> simp +contextual [A, algebraMap_toAlgebra, algebraMap_eq_inl,
       IsScalarTower.algebraMap_apply A B, *]⟩ ⟨τ.hom, by tauto⟩ (by tauto)).1 ≫ _))))
   ((r 0).1.mp (hg.mono fun w h k ↦ by
   simpa [← (landsIn_iff_mem), landsIn_basicOpen, ofSection_eq, k,
     ← (map_injective (by simp [*, reassoc_of% map_evalSection_fromSpec]) : ρ ≫ evalSection _ k =
     u)] using! mt (h.mem_open (X.basicOpen (aeval z Q)).2)
     (ha ▸ ((hW.fromSpec_preimage_basicOpen _).le · (·.ne_zero congr($hQ)))))))))
  have hm p := minpoly.isIntegrallyClosed_dvd (p := p) ⟨_, G.monic_f, hx.1⟩
  have ⟨g, hg⟩ := hm _ hx.1
  have := Etale.iff_isStandardSmoothOfRelativeDimension_zero.1 (.of_equiv (.ofBijective (awayMapₐ π
    _) ⟨awayMap_injective_iff.2 fun c (k : π c = 0) ↦ (G.exists_mul_aeval_x_g_pow_eq_aeval_x c).elim
    fun a ⟨n, ha⟩ ↦ ⟨1, by grw [← zero_dvd_iff, ← (G.hasMap.2.pow n).dvd_mul_right, mul_assoc, ha,
    pow_one, ← map_mul, ← hm a (by simp [a.aeval_algHom_apply, ← ha, k]), mul_comm, ← hg,
    G.hasMap.1]⟩, mapₐ_surjective_of_surjective _ hπ⟩))
  refine ⟨_, landsIn_opensRange (c := specMap (algebraMap ..) ≫ specMap (algebraMap _ (Away f)) ≫
    hW.fromSpec).2 ⟨ofHom (awayLift β.hom _ (by simpa [hg, g.aeval_algHom_apply] using!
    hx.isUnit_derivative_f : _ ∧ _).2), by rw [← map_comp_assoc, ← ofHom_comp]; simp⟩, ?_⟩
  simpa [← Scheme.Hom.isoOpensRange_inv_comp, ← hρ, ← Spec.map_comp] using comp_of_isOpenImmersion
    _ _ _ (Spec_iff.2 (locally_of isStandardSmoothOfRelativeDimension_respectsIso _ (by
    simpa [← isStandardSmoothOfRelativeDimension_algebraMap] using! ((iff_of_isStandardSmooth _).2
      (rank_eq_card_basis e)).trans _ 0 ..)))
end

-- part: Lib.Shimura.TraceFormula.MarkedEqDefinite
section
/-! Known result: the simple trace formula, with the Hecke trace on a definite group and the
vanishing of non-elliptic terms. Here the group is a definite unitary similitude group, the level is
neat, and finite sums over cosets replace Haar integrals. Non-elliptic terms cancel for a regular
test function with a cuspidal type at one split place (n odd), and such a function not killing a
given vector exists. Source: Dummigan, A simple trace formula for algebraic modular forms, Exp.
Math. 22 (2013); Arthur and Clozel, Simple algebras, base change and the advanced theory of the
trace formula (1989), ch. 1 §2, after Deligne and Kazhdan.

This file: Non-elliptic terms vanish for a cuspidal type, so marked and definite counts agree. -/

attribute [-instance] instCoeTCOfCoe
open Function NumberField Matrix Polynomial Set QuotientGroup MulAction Pointwise ConjAct Fintype
  IsCoprime IsIdempotentElem Multiplicative
attribute [local simp] mul_assoc mul_add add_mul sub_mul orbit mul_sub units_smul_def eq
  mul_self_mul SemiconjBy orbitRel_apply Quotient.eq aeval_self_charpoly

/-- Let Γ permute the blocks π p of a partition of X and act freely on the support of an
invariant function F. If F has finite support and sum zero on each block meeting its
support, its orbit sum is zero. -/
lemma finsum_orbits_eq_zero_of_blocks {Γ X} [Group Γ] [MulAction Γ X] {F : orbitRel.Quotient Γ
  X → ℂ} (π : X → _) (hm : ∀ p, p ∈ π p) (hπ : ∀ (z : Γ) {p q}, p ∈ π q → π (z • p) = z • π q) (h0 :
  ∀ s, F ⟦s⟧ ≠ 0 → stabilizer Γ s ≤ ⊥ ∧ (π s ∩ support (F ⟦·⟧)).Finite ∧ ∑ᶠ p ∈ π s, F ⟦p⟧ = 0) :
  ∑ᶠ c, F c = 0 := have m p q := Iff.intro (@hπ 1 p q) (by grind [one_smul])
  (finsum_def _).trans (dite_eq_right_iff.2 fun S : Set.Finite _ ↦
    Finset.sum_cancels_of_partition_cancels ((orbitRel ..).comap _) fun c l ↦ by
  obtain ⟨⟨_, T, h⟩, _⟩ := h0 c.out (by aesop), (hπ · <| hm ·)
  use (finsum_cond_eq_sum_of_cond_iff _ fun k ↦ by simpa [*, Quotient.mk_eq_iff_out] using!
    mem_orbit_symm).symm.trans
    (finsum_image_eq_zero_of_fibers T (⟦·⟧) (by rwa [finsum_mem_inter_support])
    fun p h ↦ by rw [← Nat.card_congr ((Equiv.Set.image (· • p) (stabilizer Γ (π c.out)) fun a b e ↦
    inv_mul_eq_one.1 ((h0 p h.2).1 (by simp [mul_smul, ← e]))).trans (Set.equivOfEq (by aesop)))]))

/-- Let E⁺ ≠ ℚ, n odd, 𝔑 neat, f a regular Hecke function of level K(𝔑), χ-eigen under left
translation by J at w₀ with χ cuspidal, both unweighted counts finite modulo GL_n(E). Then
for any weight w the marked and definite orbit sums agree.

Known result: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish. -/
lemma sum_countTerm_marked_eq_definite {E n} [Field E] [Ψ : CMBase E] [Fintype n] {𝔑 : 𝓞 E} (hN :
  IsNeat n 𝔑) (hn : Odd (card n)) {f : heckeAlgebra n ℂ 𝔑} (hr : IsRegularHecke f) {w₀ J χ} (hχ :
  IsCuspidalType J χ) (hJ : ↑f ∈ fixedToEigen (levelGU n 𝔑) (conjAtSplit w₀) J χ) w (fin : ∀ ε,
  (countTerm ε f 1).support.Finite) : ∑ᶠ c, countTerm True f w c = ∑ᶠ c, countTerm False f w c := by
  let u P := ite (Irreducible P) 0 (w P)
  have z ε : finsum (countTerm ε f u) = 0
  choose q hq using fun P : (LocField w₀.1)[X] ↦ (dite _ (fun ⟨h, h', hu⟩ ↦ by
    obtain ⟨A, B, rfl, _⟩ := by simpa [irreducible_iff, hu] using h'
    have ⟨u, v, l⟩ := h.isCoprime; use u * A, ⟨-u * v, by grind⟩
    simp_all [← l, mul_left_iff, mul_right_iff, isCoprime_self]) (⟨0, by simp, ·.elim⟩) : ∃ p, P ∣
    p * p - p ∧ (P.Separable ∧ ¬Irreducible P ∧ ¬IsUnit P → ¬IsCoprime P (1 - p) ∧ ¬IsCoprime P p))
  let e g := (q (charpoly (n := n) g)).aeval g
  have he g : IsIdempotentElem (e g) := by simpa using! aeval_dvd g (hq g.charpoly).1
  let A g := MonoidHom.toHomUnits ⟨⟨(1 + e g * toAdd · * (1 - e g)), by simp⟩,
    by simp [add_assoc, he, -mul_sub]⟩
  let K := levelGU n 𝔑; let G (p : MarkedTriple K n) := dualComponent w₀ (γ p.2.1 p.1.out)
  let r p Y : MarkedTriple K n := (p.1.out * conjAtSplit w₀ (A (G p) Y), p.2)
  use finsum_orbits_eq_zero_of_blocks (range ∘ r) (fun _ ↦ ⟨1, congr(($(by simp), _))⟩) (by
    rintro z _ q ⟨m, rfl⟩; obtain ⟨k, hk : (z • r q m).1.out = _⟩ := mk_out_eq_mul K _
    erw [smul_set_range, ← ((mul_right_surjective m).comp (toPerm (β := Matrix ..)
      (toConjAct (A (G q) m * dualComponent w₀ k))).surjective).range_comp]
    use congr(range fun a ↦ ($(QuotientGroup.eq.2 ?_), _))
    conv in A (G q) _ => erw [map_mul, fun b g Y ↦ (by ext1; unfold A e; simp [↓aeval_smul,
     charpoly_mul_comm] : A g (ofAdd (toConjAct b • Y.toAdd)) = b * A (toConjAct b⁻¹ • g) Y * b⁻¹)]
    simp [G, hk, show (z • r q m).2.1 = _ * q.2.1 * _ by rfl,
      ← by simpa using conj_conjAtSplit (w := w₀) k.2.1]) fun s l ↦ ?_
  let g := G s; rw [← s.eta, ← s.1.out_eq, countTerm_mk, ite_ne_right_iff, mul_ne_zero_iff] at l
  have ⟨j, Y, hj, c⟩ := And.elim (hχ _ (he g)) (by
    apply ((hq g.1.charpoly).2 _).imp <;> simp +contextual [← isUnit_aeval_iff_isCoprime, e,
      not_imp_not]
    simp [g, G, isUnit_iff_degree_eq_zero, hn.pos.ne', -mul_assoc]
    erw [← coe_units_inv, charpoly_transpose, charpoly_map, charpoly_map, Polynomial.map_map]
    use (hr l.2.1).map, mt ((charpoly_monic _).irreducible_of_irreducible_map _)
      (l.2.2 <| by simp [u, ·]))
  have hF {a} : countTerm ε f u ⟦r s a⟧ = _ :=
    countTerm_mk.trans ((ite_eq_left (by simp [isSignedFrame_mul_iff 1, ratConj, l])).trans
      (congrArg
    (heckeCosetFn f ⟦·⟧ * _) (show _ = conjAtSplit _ ((A g a)⁻¹ * g * A g a) * _ by
    simpa [g, G] using
      eq_mul_of_mul_inv_eq (conj_conjAtSplit (heckeAlgebra.mem_GUPlus_of_ne_zero l.2.1).1 _))))
  have R : .ker (r s) = leftRel (K.comap ((conjAtSplit _).comp (A g))) := by
    ext; simp [r, MarkedTriple, QuotientGroup.eq, ↓leftRel_apply, g]
  refine ⟨fun z e ↦ hN.2 l.1 (by simpa [← QuotientGroup.eq] using ((Quotient.mk_smul_out
    ..).trans congr($e.1)).symm) ((ratConj_eigenReflection _).trans congr(eigenReflection _ $e.2.1 _)), ((finite_quotient_image_of_isCompact
    ((isOpen_comap_conjAtSplit hN.1).preimage (.of_coeHom_comp (.const_add (by fun_prop) 1)))
    ((isCompact_LocInt _).matrix.image_auto (ofAdd <| aeval · (q g.1.charpoly)))
    ).image (Quot.lift _ R.ge)).subset fun | _, ⟨⟨m, rfl⟩, h⟩ => ⟨_, ⟨_, ⟨_, (fun a k i j ↦
    mem_Ô.1 (k.2 j i) _ : ∀ a ∈ GUPlus E n, ↑(dualComponent w₀ a) ∈ _) _ (heckeAlgebra.mem_GUPlus_of_ne_zero (left_ne_zero_of_mul
    (h ∘ hF.trans))), rfl⟩, rfl⟩, congr((⟦_ * conjAtSplit _ $(Units.ext ?_)⟧, _))⟩, ?_⟩
  simp [A, -coe_units_inv, -mul_assoc, -mul_add, -mul_sub]
  erw [aeval_smul _ (toConjAct (A g m)⁻¹)]; simp +zetaDelta [he, ← map_inv]
  let a := (q g.1.charpoly).aeval (j * g).1
  have hj' : SemiconjBy (A g (ofAdd a)) (j * g) g := Units.ext (by
    have c : Commute _ (e g) := aeval_semiconj rfl _
    have ⟨s, t, d⟩ : SemiconjBy (e g) (e g) a ∧ SemiconjBy (1 - e g) a (e g) ∧
      Commute (j.1 * g.1) a := by and_intros <;> apply aeval_semiconj <;> simp [← hj, he, c.eq]
    simp [he] at s t; simp [A, ← s, ← d.eq]
    simp [← hj, he, c.eq, c.symm.left_comm, ← t]; abel)
  erw [Function.comp, mk_surjective.range_comp (Quot.lift _ R.ge), finsum_mem_range
    (by rwa [Setoid.lift_injective_iff_ker_eq_of_le])]
  use eq_zero_of_mul_eq_self_left (inv_ne_one.2 c) ((mul_finsum ..).trans (finsum_eq_of_bijective
    _ (toPerm (ofAdd a)).bijective (Quot.ind fun m ↦ congr(_ * $hF).trans (hF.trans ?_).symm)))
  simpa [← mul_assoc g, ← hj'.eq, ← (Units.ext hj : A g (ofAdd _) = _), ((Commute.all m _).map
    (A g)).inv_left.left_comm] using! congr($(hJ single_one_mem_levelSpace j⁻¹).coeff ⟦_⟧ * _)
  suffices finsum (countTerm True f (w - u)) = finsum (countTerm False f (w - u)) by
    simpa [finsum_countTerm_eq_sum (w - u), ← finsum_countTerm_eq_sum, *]
  let s μ ε w (i : n) : ℤˣ := ite (w = Ψ.v₀ → ε → i = μ) 1 (-1)
  choose e U H c he using exists_hasSignType_mul_iff (s · True) (by
    simp_all [s, Finset.prod_ite, prod_eq_single v₀, Finset.filter_ne', hn.tsub_odd]) _
  convert finsum_comp_equiv e with ⟨⟨x⟩, y, μ⟩
  erw [he, countTerm_mk, countTerm_mk]; simp [(c ..).inv_left.left_comm]; by_contra h
  obtain ⟨⟨ν, k⟩, _⟩ := (heckeAlgebra.mem_GUPlus_of_ne_zero (h <| by rw [·]; simp)).1,
    Nonempty.intro μ
  have B ε x j : IsSignedFrame x (eigenReflection ε y μ) ↔ HasSignType (s μ ε) ν y {m | ∃ c :
    (Ô ℚ)ˣ, m = finAdeleIncl ℚ E c • 1} x := exists_congr fun _ ↦
    (iff_and_self.2 (⟨by_contra (h <| by simp [u, ·]), k.1.ne', ·.similitude_and_root_norm j (by
    simp [ratConj_eigenReflection])⟩)).trans (and_congr_right' (by
    delta eigenReflection; congr!
    split_ifs <;> simp [s, apply_ite, Lagrange.sum_basis, (numberedRoots ..).injective, *]))
  simp_all [s, Pi.mul_def, (c ..).inv_left.left_comm]
end

-- part: Lib.General.Geometry.Lefschetz
section
/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Transfer of eigensystems between inner forms of a unitary group differing at a real place
(known result; see Lib.Shimura.Transfer.PELDataExistence).

This file: Reduced closures of points; free finite group actions are étale; Galois covers
generically smooth. Lefschetz local terms of Hecke correspondences rewritten as a sum over marked
pairs. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits RingHom Over Set Scheme IsArtinianRing Pi pullback
  CommRingCat Ideal Quotient Algebra TensorProduct Function Finset Module Spec OverMorphism
  FormallyUnramified LocallyQuasiFinite IsOpenImmersion IsLocalization IsIntegralClosure Fint
variable {S} {b : Spec ⟨ℂ⟩ ⟶ S} {J A : Type} [Finite J] {Z : J → _} (F : ∀ j, A → (Over.mk b ⟶ Z j))

/-- A reduced closed subscheme W of the product over S of the Z_j, with complex points over b
lifting the tuples (F j a)_j and dense in W: their reduced closure. -/
structure ReducedClosure where
  W : _
  incl : W ⟶ ∏ᶜ Z
  point _a : _ ⟶ W
  point_incl a : point a ≫ incl = lift (F · a)
  isClosedImmersion : IsClosedImmersion incl.left
  isSeparatingFamily : IsSeparatingFamily (point · |>.left)

attribute [instance] ReducedClosure.isClosedImmersion

variable {F} (C : ReducedClosure F) {J' Z' F'} [Finite J'] {C' : @ReducedClosure S b J' A _ Z' F'}

instance : IsReduced C.W.left := C.isSeparatingFamily.1

/-- The morphism from the closed subscheme W to the factor Z_j: the inclusion into the product
followed by the j-th projection. -/
def ReducedClosure.proj j := C.incl ≫ Pi.π Z j

@[simp] lemma ReducedClosure.point_comp_proj a j : C.point a ≫ C.proj j =
  F j a := by simp [proj, reassoc_of% point_incl]

instance : Nonempty (ReducedClosure F) := (exists_reduced_closure _).elim fun _ ⟨i, _, c, h, r⟩ ↦
  ⟨.mk (i ≫ _), homMk i, fun a ↦ homMk _ (by simp [reassoc_of% h]), (ext <| h ·), c, r⟩

lemma ReducedClosure.hom_ext {T} {f g : T ⟶ _} (h : ∀ j, f ≫ C.proj j = g ≫ C.proj j) : f = g :=
  (mono_of_mono_left _).1 _ _ (Pi.hom_ext _ _ h)

lemma ReducedClosure.exists_lift (σ : A → _) (f : ∀ _, _ ⟶ _) (h : ∀ a j, C'.point a ≫ f j =
  F j (σ a)) : ∃ g, (∀ j, g ≫ C.proj j = f j) ∧ ∀ a, C'.point a ≫ g = C.point (σ a) :=
  have ⟨g, e⟩ := exists_lift_of_dense_preimage _ (lift f).1 (C'.isSeparatingFamily.2.mono
    (forall_mem_range.2 fun a ↦ ⟨_, congr($((C.4 (σ a)).trans (by aesop : _ = _ ≫ _)).1 _)⟩))
  have G j : homMk g (by simpa using e =≫ hom _) ≫ _ = _ := lift_comp_π f _ ▸ ext (e =≫ _)
  ⟨_, G, fun _ ↦ C.hom_ext (by simp [*])⟩

variable {R : CommRingCat} {W Z : Over (Spec R)} [IsProper W.hom] [IsSeparated Z.hom]
  {c : W ⟶ Z} {Δ : FiniteGrp} {s : Δ →* End W}

attribute [local instance 10] Quotient.field rightAlgebra finitePresentation_of_projective
  IsFinite.of_isProper_of_locallyQuasiFinite finite_of_free

/-- Chase–Harrison–Rosenberg. Let B be a finite A-algebra containing A, and G a finite group
acting on B with ring of invariants A and simply transitively on the A-algebra maps B → k,
for every field k over A. Then B is étale over A. -/
lemma etale_of_simply_transitive {A B G} [CommRing A] [CommRing.{0} B] [Algebra A B] [Module.Finite
  A B] [Group G] [Finite G] (I : Injective (algebraMap A B)) (σ : G →* (B →ₐ[A] B)ᵐᵒᵖ) (H :
  ∀ k [Field.{0} k] [Algebra A k] (x y : B →ₐ[A] k), ∃! g, ∀ b, x ((σ g).unop b) = y b)
  (V : ∀ s, (∀ g, (σ g).unop s = s) → ∃ a, algebraMap A B a = s) : Etale A B := by
  let t := (∑ g, (σ g).unop.toLinearMap).codRestrictOfInjective (Algebra.linearMap ..) (id I)
    fun s ↦ id (V _ fun g ↦ by simpa using Equiv.sum_comp (.mulRight g) (σ · |>.unop s))
  choose u E using exists_forall_sub_mem_ideal (I := fun g ↦ ker (productMap (σ g).unop (.id ..)))
    (fun _ _ ↦ isCoprime_iff_sup_eq.2 ∘ Not.imp_symm (exists_le_maximal _ · |>.elim fun m ⟨_, _⟩ ↦
    by apply (H _ (.comp (mkₐ _ m) includeRight) (.comp (mkₐ ..) includeLeft)).unique <;>
      simp_all [Ideal.Quotient.eq, ↓sup_le_iff, IsConcreteLE.le_iff])) (Pi.single 1 1)
  obtain ⟨_, y, x, ⟨⟩⟩ := exists_sum_tmul_eq u
  have K z : ∑ i, t (z * y i) • x i = z := by simp_all [Algebra.smul_def, t, sum_mul, sum_comm,
    ← linearMap_apply, mul_assoc, ← mul_sum]
  have J s := congr(∑ i, x i ⊗ₜ[A] $(K (s * y i)))
  simp [↓tmul_sum, ↓← smul_tmul, sum_comm, ← sum_tmul, mul_right_comm, K] at J
  rcases iff_exists_tensorProduct.2 ⟨_, fun s ↦ (sub_mul ..).trans (congr(_ * $(J 1) -
    _).trans (by simp [mul_sum, J])), by simpa using E 1⟩, Projective.of_split
    (.pi (t.comp ∘ .mulRight A ∘ y)) (Fintype.linearCombination _ x) (by bound)
  exact .of_formallyUnramified_of_flat

/-- Let R be a countable domain, with a map to ℂ, whose maps to fields of characteristic 0 are
injective; W proper, Z separated over R; c: W → Z onto and Δ-invariant, Δ finite. If Δ is
simply transitive on the non-empty fibres of c on complex points, then also on k-points for
every field k of characteristic 0 (`IsGaloisCovering`). -/
lemma isGaloisCovering_of_complex_points [Countable R] [Algebra R ℂ] (hR :
  ∀ k [Field.{0} k] [CharZero k] (f : R →+* k),
  Injective f) (b : ∀ g, (s g).asHom ≫ c = c) (hc : AlgebraicGeometry.Surjective c.left)
    (o : ∀ y z :
  specOver R ℂ ⟶ W, y ≫ c = z ≫ c → ∃! g, y ≫ (s g).asHom = z) : IsGaloisCovering c s := ⟨b, hc, by
    intros
    obtain ⟨x, ⟨⟩, ⟨⟩⟩ := lift' _ _ ‹_›
    obtain ⟨z, φ, ⟨⟩, _⟩ := exists_countable_residue_point (fst .. ≫ hom W) x
    set j := fromSpecResidueField _ z
    choose ψ f using exists_ringHom_complex_extend (@hR _ _ φ.charZero (Spec.preimage (j ≫ fst .. ≫
      hom W)).hom) (hR _ (algebraMap ..)) (by simp [Cardinal.aleph0_le_continuum.trans'])
    specialize o (homMk (specMap ψ ≫ j ≫ fst ..) ?_) (homMk (specMap ψ ≫ j ≫ snd ..) ?_) <;>
    simp_all [OverMorphism.ext_iff, cancel_epi, ← f, ← c.w, condition_assoc, -w]⟩

/-- Let W → Z be a Galois cover (`IsGaloisCovering`) over a domain R, W proper and reduced, Z
separated and smooth of relative dimension d. Then W ×_R k is smooth of relative dimension d
for every field k ⊇ R of characteristic 0. -/
lemma IsGaloisCovering.smoothOfRelativeDimension_baseChange [IsDomain R]
    (G : IsGaloisCovering c s) d
  [IsReduced W.left] [SmoothOfRelativeDimension d Z.hom] k [Field k] [CharZero k] [Algebra R k]
  [FaithfulSMul R k] : SmoothOfRelativeDimension d (snd W.hom (specMap (algebraMap R k))) := by
  let ι : Spec ⟨functionField _⟩ ⟶ Spec R := fromSpecStalk ..
  obtain ⟨⟨ψ, e⟩, b, hc, o⟩ := (⟨IsFractionRing.lift (FaithfulSMul.algebraMap_injective R k), (_ ≫=
    fromSpecStalk_eq ..).trans (map_comp .. ▸ congr(specMap $(lift_comp _)))⟩ : ∃ ψ, specMap ψ ≫ ι =
    specMap (algebraMap R k)), G
  let π := fst Z.hom ι
  let q := snd c.1 π
  have C {k} [Field k] y := (charZero_iff (@preimage _ ⟨k⟩ (y ≫ snd Z.hom ι)).1.injective).1
    ψ.charZero
  have O {X p} (q : X ⟶ _) (h : p ≫ c.1 = q ≫ π) w v (e : q v = q w) : ∃ g,
    (s g).asHom.1 (p w) = p v :=
    by obtain ⟨t, ⟨⟩, ⟨⟩⟩ := Pullback.exists_preimage_pullback _ _ e
       exact fromSpecResidueField_apply t _ ▸ (@o _ _ (C (fromSpecResidueField _ t ≫ fst .. ≫ q))
    (_ ≫ _ ≫ p) (_ ≫ _ ≫ p) (by grind [condition])).exists.imp fun _ ↦ (congrArg (· default) ·)
  have et {P} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] {A B : CommRingCat} {_ : Algebra P A}
    (_ : Etale P A) {_ : Algebra A B} (_ : Module.Finite A B) [IsReduced B] {p u} [Mono p]
    (hp : IsPullback p (specOver A B).hom c.1 (u ≫ π)) : Etale A B := ?_
  rcases @isReduced_of_isReduced_stalk _ (⟨(fst c.1 π).stalkMap_surjective · |>.forall.2 (by simp
    [IsNilpotent.map_iff, stalkMap_injective_of_flat])⟩),
    of_finite_preimage_singleton q (q.surjective.forall.2
    (((finite_range _).preimage (fst _ π).injective.injOn).subset <| O _ condition ·))
  refine e ▸ c.w ▸ (smoothOfRelativeDimension_isStableUnderBaseChange d).1
    (.of_right' (.of_hasPullback ..) (.paste_vert (.of_hasPullback ..) (.of_hasPullback ..)))
    (d.zero_add ▸ smoothOfRelativeDimension_comp (hf := ⟨fun x ↦ ?_⟩) ..)
  choose U _ V h hx e hs using (inferInstance : SmoothOfRelativeDimension d (snd _ ι)).1 (q x)
  obtain ⟨⟨⟩, r⟩ := U.eq_bot_or_top.resolve_left (·.le (e hx)), h.preimage q
  exact ⟨_, h, _, r, hx, _, etale_iff_isStandardSmoothOfRelativeDimension_zero.1 (et
    hs.exists_etale_mvPolynomial.choose_spec.2 (q.app_eq_appLE ▸ q.finite_app _ h) ((isPullback _ _
    _ _ (h.SpecMap_appLE_fromSpec q r _).symm (by simp)).flip.paste_horiz (.of_hasPullback ..)))⟩
  have L k [CommRing k] [Algebra A k] y hy : ∃ χ : B →ₐ[A] k, specMap χ ≫ p = y :=
    (specOver.map_bijective.2
    (homMk _ (hp.lift_snd y _ hy))).imp fun _ e ↦ by simpa using! congr($e.1 ≫ p)
  choose a h0 using fun g ↦ L B (p ≫ (s g).asHom.1) (by simp [← comp_left, b, hp.w])
  let F := FractionRing P
  let N := A ⊗[P] F
  obtain ⟨h1, hm⟩ := h0 1, (h0 <| · * ·), fun {k} [Field k] [Algebra A k] ↦
    C ((specOver A k).hom ≫ u), Etale.of_equiv (commRight P F A)
  obtain H := fun {k} [Field k] [Algebra A k] (x y : B →ₐ[A] k) ↦ o k (specMap x ≫ p) (specMap y ≫
    p) (by simp [hp.w, ← Spec.map_comp_assoc, ← ofHom_comp]), isReduced_of_field F N, of_finite F N
  simp [← h0, ← reassoc_of% h0, ← Spec.map_comp_assoc, cancel_mono, cancel_mono_id, Spec.map_inj,
    -Spec.map_comp, ConcreteCategory.hom_ext_iff] at h1 hm H
  let Ω (m : MaximalSpectrum N) := AlgebraicClosure (_ ⧸ m.1)
  have inj := ((equivPi _).injective_comp _).2 (.piMap (Ω · |> algebraMap _ |>.injective))
  let χ := AlgHom.pi fun m ↦ (L (Ω m) _ (exists_point_over _ (hc.1 _)).choose_spec).choose
  have hA := χ.comp_algebraMap ▸ @id (Injective (algebraMap ..)) (inj.comp
    (includeLeft_injective (S := P) (IsFractionRing.injective ..)))
  refine etale_of_simply_transitive (.of_comp (f := χ) hA) ⟨⟨(⟨a ·⟩), congr(⟨$(AlgHom.ext h1)⟩)⟩,
    (congr(⟨$(AlgHom.ext <| hm · ·)⟩))⟩ @H fun s hb ↦ ?_
  obtain ⟨v, hv : algebraMap _ _ v = _⟩ := (reindex_equiv (equivPi _)).2.1.1 ((range_piMap _).ge
    fun m _ ↦ (InfiniteGalois.mem_bot_iff_fixed _).2 fun σ ↦ (H
    ((σ.restrictScalars A).toAlgHom.comp (.comp (evalAlgHom _ _ m) χ)) _).exists.elim (hb · ▸ · _))
  obtain ⟨x, ⟨⟩⟩ := toIntegralClosure_bijective_of_smooth (B := F).2.comp (includeLeft_surjective A
    A (isIntegral_iff.1 ·.2 |>.imp (by bound))) ⟨v, .tower_bot inj (hv ▸ .map χ (.of_finite ..))⟩
  use x, sub_eq_zero.1 (nilpotent_iff_mem_prime.2 fun q i ↦ (exists_ideal_over_prime_of_isIntegral
    (q.under A) (ker χ) (comap_bot_le_of_injective _ hA)).elim fun Q ⟨hQ, j, e⟩ ↦ (O (_ ≫ u) hp.w
    ⟨Q, j⟩ ⟨q, i⟩ congr(u ⟨$e.symm, _⟩)).elim fun g e ↦ congr($(p.injective (congr($(h0 g) _
    ).trans e)).1).le (hQ (by erw [map_sub, hb]; simpa))).eq_zero

open NumberField Matrix Polynomial LinearMap Nat ModuliPoint QuotientAddGroup
variable {E} [Field E] [CMBase E] {d₀ n} [Fintype n] [HasQuadSubfield d₀ E] {𝔑 : 𝓞 E} {ν} {R :
  _} (X : Model n d₀ 𝔑 ν R) [Nonempty n]

/-- If b is supported on regular elements, finitely many marked pairs contribute and, for all
α ∈ O_E^ν, the b-weighted z^h-coefficients of the local terms `localTerm` at 2α sum to 0. -/
def IsNullHecke ν h (b : heckeAlgebra n ℂ 𝔑) := IsRegularHecke b → ∀ α : Fin ν → _, (countTerm True
  b 1).support.Finite ∧ ∑ᶠ x, countTerm True b (localTerm (2 * α) · · |>.coeff h) x = 0

/-- θ occurs in weight h: for every linear combination p of words with p(θ) = 1,
`IsNullHecke` fails in weight h for some b·p(τ), b in the Hecke algebra. -/
def OccursInWeight a ν (θ : SafePlace 𝔑 → ℕ → ℂ) h := ∀ s (c : List _ → ℂ), ∑ L ∈ s,
  c L * (L.map ↿θ).prod = 1 →
  ¬∀ b : heckeAlgebra (Fin a) .., IsNullHecke ν h (b * ∑ L ∈ s, c L • (L.map tauHecke).prod)

attribute [local simp] mul_assoc ratConj_eigenReflection isLevelIso_iff map_smul'
  Matrix.map_sub prod_ne_zero_iff
  eval_prod eval_multiset_prod charpoly_map det_one_sub_smul_eq_prod_roots Nat.card_pi

/-- Let 𝔑 be neat and b in the Hecke algebra, with function f on cosets. If on all deep levels i
of the model the combinations ∑ f(q)[m_α ∘ u_{i,q}] satisfy `IsNullFamily` in weight h
for all α, then `IsNullHecke` holds for b in weight h. -/
lemma Model.isNullHecke_of_isNullFamily (hN : IsNeat n 𝔑) {b : heckeAlgebra _ ℂ 𝔑} {h}
  (hF : ∀ᶠ i in .atTop, ∀ α, IsNullFamily (X.leg i ⟦·.out⟧ ≫ X.m α) (heckeCosetFn b) X.d h) :
  IsNullHecke ν h b := fun hr α ↦ let f := heckeCosetFn b
  have o (c : f.support) := heckeAlgebra.mem_GUPlus_of_ne_zero (by aesop : f c.1.out ≠ 0)
  (hF.and (.all (X.eventually_translate ∅ <| o ·))).exists.elim fun i ⟨hF, ok⟩ ↦ by
  let B (z : GL n E) j := 1 - (2 * α j).val • z.1
  let L x z j := (frameLattice x).comap (realVecAction (B z j)).toAddMonoidHom
  let Q x z j := _ ⧸ (frameLattice x).addSubgroupOf (L x z j)
  have hd {x z} (h : f (γ z x) ≠ 0) j : frameLattice x ≤ L x z j ∧ (B z j).det ≠ 0 ∧
    Nat.card (Q x z j) = ∏ σ : E →+* ℂ, σ (B z j).det := ?_
  let Fx p (t : _ × _) := f (γ t.1 (x p)) ≠ 0 ∧ p.reflection = eigenReflection True t.1 t.2 ∧ ∀ j,
    p.P j ∈ L p.x t.1 j
  choose q hq using X.point_surjective i
  obtain ⟨hF, g⟩ := hF _ _, X.covering i
  extract_lets S at hF
  have ra c {p} z : (act p ⟨_, o c⟩ (2 * α)).IsLevelIso (levelGU _ 𝔑) z p ↔ γ z p.x = c.1 ∧ ratConj
    z p.reflection = p.reflection ∧ ∀ j, p.P j ∈ L p.x z j := by simp +zetaDelta [act,
                      sub_mem_comm_iff, Quotient.mk_eq_iff_out.trans QuotientGroup.leftRel_apply]
  have e c y := by simpa only [*, ← point_leg] using
    (X.point_eq_iff i _ (q y)).trans (exists_congr (ra c))
  choose! r hs un using fun s (h : s ∈ S) ↦ (((e ..).1 h.symm).elim fun z ⟨e, H⟩ ↦
    ((isReflection_eigenReflection (hr (e ▸ (f.3 _).1 s.1.2))).2 _ (ModuliPoint.isReflection _)
    H.1).elim fun μ U ↦ ⟨(z, μ), by grind, fun t a ↦ by grind
    [mul_inv_eq_one.1 (hN.2 (isSignedFrame _) (by simpa [← a.2, QuotientGroup.eq] using e)
    (by simpa [a.1.2] using H.1))]⟩ : ∃! t, Fx (q s.2.1) t ∧ γ t.1 (q s.2.1).x = s.1.1)
  let cl := Quotient.mk (MulAction.orbitRel (GL n E) (MarkedTriple (levelGU n 𝔑) n))
  have fix {p q z t} (hz : p.IsLevelIso _ z q) (h : Fx p t) : Fx q (z * t.1 * z⁻¹, t.2) :=
    have k := heckeAlgebra.heckeCosetFn_conj hz.mem_level ▸ by simpa using h.1
    ⟨k, by simp [← hz.reflection_eq, h.2], fun j ↦ (add_mem_cancel_left
      ((hd k _).1 (hz.sub_mem_lattice j))).1 (by simpa +zetaDelta [-sub_mulVec, mul_sub,
      sub_mul] using realVecAction_mem_frameLattice hz.mem_level.2.1.isIntMatrix (h.2.2 j))⟩
  have H {p q s t} (h : Fx p t) (hs : Fx q s) : cl (p.x, t) = cl (q.x, s) ↔ ∃ w,
    q.IsLevelIso (levelGU _ 𝔑) w {p with P j := realVecAction w (q.P j)} ∧ (w * s.1 * w⁻¹, s.2) =
    t := Quotient.eq.trans (exists_congr fun w ↦ Prod.ext_iff.trans (.symm (and_congr_left fun e ↦
    .trans (by simp [hs.2, h.2, ← e]) (QuotientGroup.eq.symm.trans comm))))
  have hc {p z δ} (e : X.point i p ≫ _ = z) := g.1 δ ▸ (reassoc_of% e) _
  have bij p {t} (h : Fx p t) : {s ∈ S | cl ((q s.2.1).x, r s) = cl (p.x, t)}.BijOn (·.2.1) (.range
    fun u : (∀ j, Q p.x t.1 j) × _ ↦
      X.point i {p with P j := (u.1 j).out} ≫ (X.deck i u.2).asHom) :=
    ⟨fun s ⟨m, a⟩ ↦ ((H h (hs s m).1).1 a.symm).elim fun w ⟨R, e⟩ ↦ let u j : Q .. := ⟦⟨_, (e ▸ fix
    R (hs s m).1).2.2 j⟩⟧; (g.3 ℂ _ _ congr($((hq _ ▸ (X.point_eq_iff i _ {p with P j :=
      (u j).out}).2 ⟨w, R.mem_level, R.reflection_eq, (eq_iff_sub_mem.1 <| u
      · |>.out_eq.symm :)⟩ :).symm).1)).exists.imp' (u, ·) fun _ _ ↦ by ext; tauto,
          fun ⟨c, ⟨y⟩⟩ a ⟨c', ⟨_⟩⟩ b E ↦ by
    cases E
    obtain ⟨w, R, e⟩ := (H (hs _ b.1).1 (hs _ a.1).1).1 (b.2.trans a.2.symm)
    cases hN.2 (isSignedFrame _) R.mem_level R.reflection_eq
    congr 1
    exact Subtype.ext ((hs _ a.1).2.symm.trans (.trans (by simp [← e]) (hs _ b.1).2)),
      fun y ⟨P, E⟩ ↦
    ((point_eq_iff ..).1 (hc (hq y ▸ E :))).elim fun w R ↦ have a := fix R ⟨h.1, by simp [h.2]⟩
    have m := ((e ⟨_, (f.3 _).2 a.1⟩ y).2 ⟨_, rfl, by simp [a.2], a.2.2⟩).symm
    ⟨⟨_, ⟨y⟩⟩, ⟨m,
      un ⟨_, ⟨y⟩⟩ m _ ⟨a, rfl⟩ ▸ (H a h).2 ⟨w, ⟨R.mem_level, R.reflection_eq, by simp⟩, rfl⟩⟩, rfl⟩⟩
  have hP {p t} (h : Fx p t) : (localTerm (2 * α) t.1.1.charpoly t.2).eval 1 = Nat.card (∀ j, Q p.x
    t.1 j) := by simp [hd h.1, B, lieRoots, apply_ite, RingHom.map_det, localTerm,
    (numberedRoots ..).injective]
  obtain ⟨fS, sum⟩ := hF _ (hs · · |>.elim fun h k ↦ ⟨hq _ ▸ X.tangent i _ _ _ _ _ (ok _).1 (hr h.1)
    h.2.1 ((ra ..).2 ⟨k, by simp [h.2]⟩), by simp [hP h, hd h.1]⟩)
  have sup {w} : (countTerm _ b w).support ⊆ _ := fun c hc ↦ ((ite_ne_right_iff.1 hc).imp_right
    left_ne_zero_of_mul).elim fun h₂ h₃ ↦
    ((bij ⟨_, _, 0, h₂, (isReflection_eigenReflection (hr h₃)).1 _⟩ ⟨h₃, by
    simp⟩).surjOn ⟨(0, 1), rfl⟩).imp fun _ ↦ (·.1.imp_right (·.trans (by simp; exact c.out_eq)))
  use (fS.image _).subset sup, Set.indicator_eq_self.2 sup ▸ (finsum_mem_def ..).symm.trans
    (finsum_image_eq_zero_of_fibers fS _ sum (hs · · |>.elim fun a k ↦ by
    rw [countTerm_mk, ite_eq_left (a.2.1 ▸ isSignedFrame _), k, card_congr (bij _ a).equiv,
      Nat.card_range_of_injective, card_prod, cast_mul, hP a, div_div]
    rintro ⟨u⟩ ⟨v⟩ e
    cases (((point_eq_iff ..).1 ((hc e).trans (hc rfl).symm)).elim fun w R ↦
      funext (Quotient.out_equiv_out
      |>.1 <| by simpa [leftRel_apply, neg_add_eq_sub, hN.2 (isSignedFrame _) R.mem_level
                   R.reflection_eq] using! R.sub_mem_lattice ·) : v = u)
    simpa using (g.3 ℂ _ _ congr($(hc e).1)).unique congr($e.1) rfl))
  let F := (realVecAction (B z j)).restrictScalars ℂ
  let G := 1 + -2 • ((realVecAction ((α j).1 • z.1)).restrictScalars ℤ).restrict fun _ ↦
    realVecAction_mem_frameLattice (by
    simpa using! mul_mem (coe_mem_Ô _) <| (heckeAlgebra.mem_GUPlus_of_ne_zero h).2 · ·)
  have hG y : F y.1 = G y := by simp +zetaDelta [mul_smul, map_ofNat]; rfl
  have hf := let c := Module.finBasis ..; show (F.restrictScalars ℝ).det = (G.toMatrix c c).det by
    simp [det_apply', hG, ← det_toMatrix (c.ofZLatticeBasis ℝ), toMatrix_apply].trans_ne (by
    rw [Int.cast_ne_zero, map_add, toMatrix_one, map_smul, det_one_add_smul]; omega)
  obtain ⟨le, dL⟩ := (hG ⟨·, ·⟩ ▸ (G _).2), show F.det = _ by erw [det_restrictScalars,
    det_toLin', ← cmEmbedding.map_det, det_pi (LinearMap.mul ℂ ℂ <| Φ · _)]
  exact ⟨le, (hf <| by simp [det_restrictScalars, dL, ·]), (relIndex_comap_lattice le
    (equivOfDetNeZero _ hf).injective).trans (by simp [dL, prod_embeddings_eq_prod_pairs])⟩
end
end
