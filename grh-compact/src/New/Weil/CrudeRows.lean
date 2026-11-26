import New.Weil.RowLadder
import New.Weil.SteepParameters
import New.Weil.TriangleArrows

section
/-! Part of: Crude rows: integral twisted lifts and bounded conjugates (see New.Exchange.CrudeRows).

This file: Twist-free restriction projected to level g; periods under translation; index ratios. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Equiv Fintype Function Ideal MatMul Matrix MulAction LevelPlaces Pointwise Space
  Ideal.Quotient

variable {P} (D : Data P) (ϑ : D.MFoldTwist)

namespace Data

instance : IsLocalHom (reduceToTriangle ϑ false) :=
  ⟨Quot.ind fun _ h ↦ ((isUnit_mk_pow_iff_isUnit_mk _ (NeZero.ne D.b₁)).2 h).map
  (factor (by simp [levelModulus, mul_pow, mul_mono, pow_le_self NeZero.out, Bool.cond_false,
    -Bool.cond_eq_ite]))⟩

/-- At node (0, j) of the grid V, the order `Data.triangleOrder` of GL modulo `Data.triangleModulus`
is C times the index `Data.levelIndex` of the level, with C independent of ϑ. -/
lemma triangleOrder_eq_mul_levelIndex j : ∃ C, ∀ ϑ, D.triangleOrder false ϑ j =
  C * levelIndex ϑ false 0 j := ⟨(card (D.triangleModulus false 1).ResRing / card
  (D.gridModulus 1).ResRing) ^ card (D.Y j) ^ 2, fun ϑ ↦ by
  simpa [finMean, nodeLevel, levelIndex, card_congr of.symm, card_𝔪, mul_pow, div_pow, field, sq,
    pow_mul, prod_eq_zero_iff, (card_congr (.ofInjective _ Units.val_injective)).trans (card_subtype
    IsUnit), isUnit_iff_isUnit_det, ← RingHom.map_det, -RingHom.mapMatrix_apply] using!
    (finMean_comp_surjective
    ((reduceToTriangle ϑ false).mapMatrix (m := D.Y j)).toAddMonoidHom (factor_surjective _ :
    Surjective (reduceToTriangle ..)).comp_left.comp_left (if IsUnit · then 1 else 0)).symm⟩

/-- For j ≤ m, the period `Data.diagonalPeriodForm` of forms y on V_{j,j} and φ on Z_{j,j} = V_{j,j}
⊕ ⟨(−1)^j⟩, at a real point g, is unchanged when y is translated by a finite point u and φ by
u ⊕ 1. -/
lemma diagonalPeriodForm_formRep {j h g} u y φ : diagonalPeriodForm ϑ h g (formRep _ _ u y)
  (formRep _ _ (U.block (D.gridDiagEquiv j) (u, 1)) φ) = diagonalPeriodForm ϑ h g y φ := by
  refine (congrArg _ (funext fun x ↦ ?_)).trans ((gridSpace ..).integral_comp_mul_right u
    (fun a b x ↦ ?_) (y.2.1.rec (φ.2.1.rec (by fun_prop)))).1
  simp [Prod.mul_def]; erw [← (U.block _).map_mul]; aesop
  simp; rw [y.2.rat_mul _ b, ← one_mul (1, _), ← Prod.mk_mul_mk, map_mul, map_mul,
    mul_assoc, φ.2.rat_mul] <;> simp_all [gridSpace_diag h, mem_Γ_iff_range, Space.reindex,
    sum, ← map_inv, reindex_equiv (D.gridDiagEquiv j), -coe_units_inv, -RingHom.mem_range]

/-- For g real, some linear r from `Data.gridLevelForms` 0 (forms on Y₀ ⊕ ⟨1⟩) to forms of level
K(g₀g₁) = `Data.chosenLevel` on Y₀ has ⟨y, rφ⟩ = ∫ ȳ(x) φ((x ⊕ 1)g) dx for all φ, ϑ and y of
principal level `Data.levelPlaces` ϑ. -/
lemma exists_restrict_bordered g : ∃ r : D.gridLevelForms 0 →ₗ[ℂ] levelSpace ((gridSpace ..).formRep
  (D.gridKernel false 0 0 false)) chosenLevel, ∀ φ (ϑ : D.MFoldTwist), ∀ y ∈ levelSpace (formRep ..)
  (levelOf (D.levelPlaces ϑ).placeAt ⊥), (gridSpace ..).petersson y (r φ) = diagonalPeriodForm ϑ
  zero_le g (conjForm (isConjKernelPair_gridKernel (by simp) false).2 y) φ := by
  have he := @isConjKernelPair_gridKernel _ D false 0 0 (by simp) false
  rcases (⟨(·.2.exists_level.elim fun K h ↦ .mono K.mem_nhds_one (Subtype.ext ∘ funext ∘ h ·))⟩ :
    IsSmoothRep ((gridSpace ..).formRep (D.gridKernel false 0 0 false))),
    (gridSpace ..).finite_levelSpace he.1 ⟨D.chosenLevel, isOpen_levelOf⟩
  refine let A :=
      (diagonalPeriodForm 1 zero_le g ∘ₛₗ conjForm he.2).flip.compr₂ₛₗ (starLinearEquiv ℂ).1
    let r := .applyₗ 1 ∘ₗ .adjoint.1 ∘ₛₗ A.domRestrict₁₂ ..
    ⟨r, fun φ ϑ y m ↦ star_injective ((map_compactMean_of_const (innerₛₗ _ (r φ).1) fun u c ↦
    ?_).symm.trans
      ((((A φ).domRestrict _).adjoint_inner_left ⟨_, compactMean_mem_levelSpace y⟩ _).trans ?_))⟩
  simpa [(r φ).2 ⟨u, c⟩] using! inner_formRep u (r φ) y
  simp [-diagonalPeriodForm]; apply map_compactMean_of_const; rintro _ ⟨u, c, rfl⟩
  have ⟨v, b, e⟩ := exists_reductionK₀_eq ((gridModulus 1).reductionK₀ u)⁻¹
  have w := (Modulus.mem_principalLevel_iff gridModulus_one_ideal (u * v)).2 (by simp [e])
  rw [← D.diagonalPeriodForm_formRep ϑ (u * v), φ.2 ⟨_, _⟩]
  simp [A, periodPairing, ← mem_levelSpace_formRep_iff.1 m v (D.chosenLevel_inf_trivialOn_le ϑ
    ⟨(D.chosenLevel.mul_mem_cancel_left ⟨u, c, rfl⟩).1 (principalLevel_le_chosenLevel
    piGBar_dvd_gridLevelGen w), by simp_all [places_modulus_eq_union, IsChosen,
    Gf.mem_supportedOn.1 b, twist_one_spec, levelNorm_mem_and_notMem_of_mem_Q _ ϑ.1.1]⟩) (_ * u.1)]
  simp_all [principalLevel, mem_Kf, reindex_equiv (D.gridDiagEquiv 0)]; exact ⟨0, by simp⟩

variable {D ϑ} {g : ∀ p, GL (D.NodeIndex p) (gridModulus ϑ).ResRing} (h : ∀ z,
  g (z, 0, D.m) = 1) (D' : Data P)

include h in
/-- Let g be 1 at both nodes (0, m), and k in K_0 reduce to g(0, b), with k = 1 if b = m. Then k
translates the descent `Data.legDescents` for the moved tuple g·S to that for S, times
`Data.edgeCharProd` over its edges. -/
lemma formRep_legDescents_tupleAction {z b} S F k (e : g (z, 0, b) = (gridModulus ϑ).reductionK₀ k)
  (n : b = D.m → k = 1 := by simp [m_eq_two_mul_varrho_add_two]) : formRep _ _ k.1 (legDescents
  (tupleAction g S) z b F) = edgeCharProd g (D.legEdges z b) • legDescents S z b F := by
  fun_induction legDescents S z b <;> rw [legDescents]
  rename_i b l i
  let u := ite (b + 1 = D.m) 1 (liftMod (g (z, 0, b + 1)))
  have U : g _ = Modulus.reductionK₀ _ u := by grind [reductionK₀_liftMod]
  simp [tupleAction, *]
  refine ((isEdgeFamily_grid id false rfl zero_le l).isArrow_modDatum.2.formRep_formLift_of_eq_smul
    (pairWeil_modDatum_single k u) _).trans (congr(_ • descentMove _
      $(i u U (ite_eq_left ·))).trans ?_)
  simp [gridChar_det, smul_smul, edgeCharProd, legEdges, prod_eq_prod_Ico_succ_bot,
    edgeChar, *]; ring
  by_cases ‹ℕ› = D.m <;> simp_all [legEdges, edgeCharProd, not_lt.2]

/-- Let g be 1 at both nodes (0, m), and its value at (0, 0) in Z be that in V extended by 1.
Moving S by g multiplies the period over U(Y₀) of the descents of Ξ, φ by `Data.edgeCharProd`
over their edges. -/
lemma diagonalPeriodForm_tupleAction (h : ∀ z, g (z, 0, D.m) = 1) (k : g (true, 0, 0) =
  blockInlGL (D.gridDiagEquiv 0) (g (_, 0, 0))) r Ξ φ S : diagonalPeriodForm ϑ zero_le r
  (legDescents (tupleAction g S) _ 0 Ξ) (legDescents (tupleAction g S) _ 0 φ) = edgeCharProd g
  (D.path 0) * diagonalPeriodForm ϑ zero_le r (legDescents S _ 0 Ξ) (legDescents S _ 0 φ) := by
  have ⟨w, W⟩ :=
    map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv 0) (liftMod (g (_, 0, 0))) 1
  erw [← diagonalPeriodForm_formRep,
    formRep_legDescents_tupleAction h S Ξ _ (reductionK₀_liftMod _).symm,
    formRep_legDescents_tupleAction h S φ ⟨_, w⟩ (by erw [k, W, reductionK₀_liftMod]; simp)]
  simp [edgeCharProd, legEdges, gridPath, prod_union, disjoint_left, field]

/-- At the last stage j = m, for each real point g there is β with period `Data.gridPeriod` equal
to β·`Data.endPeriod`(Λ(ϑ), Ξ, φ) for all (ϑ, Ξ, φ). -/
lemma gridPeriod_eq_endPeriod Λ g : ∃ β, ∀ x, D'.gridPeriod Λ x le_rfl g =
  β * endPeriod (Λ x.1) (·.rec x.2.1 x.2.2) := by
  -- the lifts along a last column are chains of theta kernels
  have C z {j} (hj : j ≤ D'.m) : ∃ c, ∀ ϑ (S : EdgeTuple ϑ) F, (gridPathMap S z j _ F).1 =
      ofAlgForm (-D'.gridParam z 0 j _) _
    ((c * levelIndex ϑ z j D'.m / levelIndex ϑ z 0 D'.m) • endChain S z j F) := by
    induction' j with j ih <;> obtain ⟨U, W⟩ := (D'.endWeightData z).2.2
    · exact ⟨1, by simp [gridPathMap,
        legDescents]; intros; erw [ofAlgForm_toAlgForm (W 0 hj)]⟩
    obtain ⟨⟨c, ih⟩, H, e⟩ := ih (by omega), U j
    refine (exists_lift_ofAlgForm_eq_smul (W j (by omega)) (W _ hj) H (c := 1 * P.jetScale D'.s)
      (by simp)).imp' (· * c / P.vacuumScale D'.s ^ Fintype.card
      (D'.EndIndex z j.succ × D'.EndIndex z j) / D'.levelIndex 1 z j.succ D'.m)
      fun _ u _ _ _ ↦ ((isEdgeFamily_grid id true rfl).isArrow_modDatum.1.coe_formLift _).trans ?_
    rw [ih, gridHarmonic, e]; repeat refine isStd_gridSpace.std_induction ?_
    erw [u _ _ (endKernel.eq_1 ..).symm (vacuumDatum ..)]; simp [compUpTo, chain, endChain,
      levelIndex_eq_untwisted, endLevel, Modulus.stdLevelIndex_levelOfSubgroup, endDatum,
      funext_iff, field]
  choose c hc using (C · le_rfl)
  choose β H using D'.endBranching.2.2 g
  use β * (∏ z, c z) * D'.levelIndex 1 true D'.m D'.m / D'.levelIndex 1 true 0 D'.m,
    fun _ ↦ congr(Λ _ fun S ↦ $(by
    simp [periodPairing]; erw [hc, hc, H _ _ _ _ (endLevel ..)]
    simp [endLevel, Modulus.stdLevelIndex_levelOfSubgroup, levelIndex_eq_untwisted, field,
      endBlockPoint])).trans ((Λ _).map_smul ..)

/-- If `S` holds at the start, the kernels preserve it and pairings of `S`-vectors satisfy
‖σ(M·a)‖ ≤ R, then `endPeriod` is a sum of N·∏ card `StdClasses` such a, N ≤ `tupleBound ϑ ^ n`. -/
lemma endPeriod_mem {n} {Λ : GridDatum ϑ} (hΛ : IsTidy n (D.path D.m) Λ) {y} (hy :
  FixedByEndLevels ϑ y) (S : ∀ _ _, _ → _ → Prop) {F M R} [NormedField F] (σ : ℂ →+* F) (hs : ∀ x z,
  ∀ j < D.m, ∀ g h v, S z j g v → S z _ h ((endKernel ϑ z j).jetMatrix ((endKernel ϑ z j).ω (g,
  h) (@endDatum _ D ϑ x z j)) v)) (hB : ∀ z g, S z 0 g ((D.endToAlgForm z (y z)).1 g)) (hA :
  ∀ {g v' v}, S _ _ g v' → S _ _ (endBlockPoint ϑ g) v → ‖σ
  (M * D.endPairing v' v)‖ ≤ R) : ∃ N ≤ tupleBound ϑ ^ n, endPeriod Λ y ∈ (N * ∏ z,
  ∏ j ∈ range (D.m + (!z).toNat), .card (StdClasses (endLevel ϑ z j))) • {a | ‖σ (M * a)‖ ≤ R} := by
  -- invariance of the integrand, by the definition of tidy data
  have J (a : ∀ z j, endLevel ϑ z j) (e : (a ..).1 = U.block (D.gridDiagEquiv _) ((a ..).1, 1))
    (β β' : _ →ₗ[ℂ] _) : let F Φ := Λ fun x ↦ D.endPairing (β
      (TensorChain.pure (Φ x false) D.m)) (β' (TensorChain.pure (Φ x true) D.m))
    F (fun x z j ↦ (endKernel ϑ z j).ω (a z j, (a z _).1) (endDatum x z j)) = F endDatum := by
    choose u k f using (a · · |>.2)
    simp_rw [← f] at *
    let g (p : Node) := Pi.mulSingle (M := fun b ↦ GL (D.GridIndex p.1 p.2.1 b) _) _
      ((gridModulus ϑ).reductionK₀ (u ..)) p.2.2
    exact mul_left_cancel₀ (by simp [edgeCharProd, prod_eq_zero_iff, MulChar.apply_eq_zero_iff])
      (((hΛ.equivariant g ⟨by simpa [g] using (k · 0), fun j ↦ by
      obtain rfl | h := em (D.m = j) <;> simp [g, *]
      convert! (e ▸ map_block_eq_blockGL _ _ _ 1).2; simp⟩) _).symm.trans (by
      simpa [-prod_mul_distrib, fun z S ↦ TensorChain.pure_smul (g := fun j ↦ (endKernel ϑ z j).ω (u
        z j, (u z _).1) (endDatum (tupleAction g S) z j)) (endDatum S z) _ D.m fun _ _ ↦ Subtype.ext
        ((map_smul ..).trans (.trans (congrArg _ (by
        simp [vacuumDatum, ← modDatum_vacVector]; apply pairWeil_modDatum_single
        simp [tupleAction, g])) (smul_comm ..))),
        ← Pi.smul_def, -smul_eq_mul, edgeCharProd, legEdges, gridPath, g, prod_union, disjoint_left,
        mul_assoc, gridChar_det, edgeChar, division_def] using! mul_left_comm ..))
  choose X W c s hW hc e using hΛ.isShortSum
  have T z j h := D.classAut_eq_bot_of_le_chosenLevel ((endLevel_le_principalLevel ϑ z j).trans
    (D.principalLevel_le_chosenLevel piGBar_dvd_gridLevelGen)) (boxes_endWeightData_le z h).1
  choose B b using fun z ↦ exists_linear_chain_eq_pure (endKernel ϑ z) _ (D.endToAlgForm z (y z))
  erw [endPeriod, e, ← classIntegral_sum _ (.mulLeft <| c ·) 1 ?_ (by tauto)]
  simp [prod_range_succ, mul_nsmul, -Nat.card_eq_fintype_card]
  exact ⟨_, hW, classIntegral_mem_nsmul (T _ _ .refl) (by
    rintro _ ⟨u, k, rfl⟩ g
    cases map_block_eq_blockGL (gridModulus ϑ).reduction (gridDiagEquiv ..) u 1
    convert J (Bool.rec (Pi.mulSingle _ ⟨u, by tauto⟩) (Pi.mulSingle _ ⟨_, ⟨_, ‹_›⟩, by simp_all
      [Modulus.reductionK₀, nodeLevel, m_eq_two_mul_varrho_add_two, Units.ext_iff, ← submatrix_map],
      rfl⟩)) _ (B _ g) (B _ (endBlockPoint ϑ g)) <;> simp [e, ← b, chain_equivariant, hy _,
      endBlockPoint, ← map_mul]) fun g ↦ IsJointlyInvariant.sum_chain_mem_nsmul (endKernel ϑ _)
    (L := (c · • D.endPairing.flip _)) (fun a _ ↦ by simpa [*] using
    (J (Bool.rec a 1) (by simp [*]) · _)) (T _ · ·.le) (hy _) _ (by tauto) (hB _) fun β h ↦
    IsJointlyInvariant.sum_chain_mem_nsmul (endKernel ϑ _) (L := (c · • D.endPairing _))
    (fun a _ ↦ by simpa [e] using J (Bool.rec 1 a) (by simp [*]) β) (T _ · ·.le) (hy _) _ (by tauto)
    (hB _) fun β' h' ↦ (sum_const {a | _}).le (Set.finsetSum_mem_finsetSum _ _ _ fun x a ↦ by
      simpa [mul_left_comm ‖σ M‖] using (mul_le_of_le_one_left (by bound) (by_cases (by
        simp [·]) (hc x · |>.1 |> σ.isOfFinOrder |>.norm_eq_one.le))).trans (hA (h x a) (h' x a)))⟩
  intro x; have η z := (endChain (s x) z D.m (y z)).2
  refine ⟨?_, (_ ⊓ Subgroup.comap ((U.block (gridDiagEquiv ..)).comp (.inl ..)) _).isOpen_mono
    (fun a x g ↦ ?_) (.and (η _).1 (.preimage_of_continuous (f :=
    (G.blockEmb (s := 1) Sum.elim_one_one.symm ⟨⟨1, ·⟩, 1⟩ |>.2)) (η _).1))⟩
  rintro _ ⟨γ, rfl⟩ _
  simpa [endBlockPoint, ← map_mul, ← block_embFin] using! congr($(((η _).2 ..).trans
    (stdSpace_weightRep_apply ..)) ⬝ᵥ _ *ᵥ $(((η _).2 (U.block _ (γ, 1)) (endBlockPoint ..)).trans
    (stdSpace_weightRep_apply ..))).trans (D.endBranching.2.1.choose_spec.1 ..)
  simpa [endBlockPoint, ← map_mul] using congr(D.endPairing $(x.1 g) $(x.2 (endBlockPoint ..)))

/-- For b ≤ m some Φ satisfies `Data.IsLevelTidy` of order 2(m − b) on the edges (0, i) → (0, i+1),
b ≤ i < m, of both grids, and B(ιΞ, ιφ) = N·Φ(S ↦ B(d_SΞ, d_Sφ)) for bilinear B; ι =
`Data.iotaPlus` (untwisted on φ), d = `Data.legDescents`, N the product of `Data.triangleOrder` over
these i and both grids. -/
lemma exists_isLevelTidy_iotaPlus_eq {b} (hb : b ≤ D.m) : ∃ Φ :
    GridDatum ϑ, IsLevelTidy (2 * (D.m - b)) (D.legEdges false b ∪ D.legEdges true b) Φ ∧
  ∀ (B : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) Ξ φ, B (iotaPlus ϑ false b Ξ) (D.iotaPlus 1 true b φ) =
  (∏ i ∈ Ico b D.m, triangleOrder false ϑ i * triangleOrder true ϑ i) * Φ fun S ↦ B
  (legDescents S _ b Ξ) (legDescents S _ b φ) := Nat.decreasingInduction (fun b h ⟨Φ, q, e⟩ ↦ by
  let u z := verticalEdge z 0 b
  let Ψ z (y : Matrix (NodeIndex (u z).2) (D.NodeIndex (u z).1) _) :=
    inclusionDatum _ (y.map (reduceToTriangle ϑ z))
  have s z {n w Λ} (v : u z ∉ w) : IsLevelTidy n w Λ →
    IsLevelTidy (n + 1) (insert (u z) w) (Λ.bind (fun _ ↦ Ψ z)
    (update · _)) := .imp (.bind (by simp [card_matrix_le_tupleBound, u, h, h.le]) fun S y e ↦ by
      cases z; have : HasLeftInv y := ⟨_ * (inclMatrix _ .inl)ᵀ, (Matrix.mul_assoc ..).trans
        (isUnit_of_mapMatrix (reduceToTriangle ..) (by simp; erw [Pi.support_single_subset e,
        transpose_map, map_inclMatrix, inclMatrix_transpose_mul_self .inl]; simp)).val_inv_mul⟩
      all_goals grind [IsOfFinOrder.one]) fun C g G f ↦ by
    have a i k (h : k ∈ nodeLevel ϑ (z, 0, i)) : k.map (reduceToTriangle ϑ z) = 1 ∧
      edgeChar ϑ (u z) k.1.det = 1 := by
      cases z <;> simp [nodeLevel] at h; simp [h]
      obtain ⟨k, rfl⟩ := reductionK₀_surjective k
      erw [← gridChar_det _ _ Unit 1, gridChar_det (ϑ := 1) false b Unit 1,
        (Units.ext Modulus.factor_reductionK₀).symm.trans h]; simp [h]
    erw [edgeCharProd, prod_insert v, mul_assoc, ← C g G]
    simp [h.le, u, *]
    congr with S; simp
    convert (injective_gl_inv_mul_mul (g (u z).2) (g (u z).1)).bijective_of_finite.sum_comp _
    simp [Ψ, u, h.le, *, -coe_units_inv, ← GeneralLinearGroup.val_map_apply]
    left; congr; set_option synthInstance.maxHeartbeats 200000 in
      grind [tupleAction, Matrix.mul_assoc]
  refine ⟨_, by convert s false ?_ (s true ?_ q) <;> first | lia | simp [legEdges,
    ← insert_Ico_add_one_left_eq_Ico h, u, insert_comm], fun B Ξ φ ↦ ?_⟩
  unfold legDescents iotaPlus
  simp_rw [h, ite_true, prod_eq_prod_Ico_succ_bot h]
  erw [e (B.compl₁₂ (pointDescent ..) (pointDescent ϑ ..))]
  simp [fun z ↦ (by erw [pointDescent, modDescent, ← modDatum_factor, modDatum_eq_sum]; simp; rfl :
    pointDescent ϑ z b = (triangleOrder z ϑ b : ℂ) • ∑ y, Ψ z y • descentMove y), fun z c S y ↦
    @legDescents_congr _ D ϑ (update S (u c) y) S z (b + 1) (by grind [legEdges]),
    u, LinearMap.pi, ← sum_fn, ← Pi.smul_def, -smul_eq_mul]
  simp [mul_sum]; ac_rfl) ⟨.proj 0, ⟨⟨_, {0}, 1, 0, by simp [legEdges]⟩, by
    delta tupleAction edgeCharProd legEdges; aesop⟩, by simp [iotaPlus, legDescents]⟩ hb

/-- For some C, every ϑ has a datum Λ, tidy of order 4m on `Data.path` 0, such that
`Data.triangleOrder` at node (0, m) of V times the period `Data.diagonalPeriodForm` over U(Y₀) of
the descents `Data.iotaPlus` of Ξ, φ equals C times `Data.gridPeriod` for Λ. -/
lemma exists_isTidy_diagonalPeriodForm_eq : ∃ C Λ, ∀ ϑ, IsTidy (4 * D.m) (D.path 0) (Λ ϑ) ∧ ∀ r Ξ φ,
  triangleOrder false ϑ D.m * diagonalPeriodForm ϑ zero_le r
  (iotaPlus ϑ _ 0 Ξ) (D.iotaPlus 1 _ 0 φ) = C * gridPeriod Λ (ϑ, Ξ, φ) zero_le r := by
  choose κ K using D.triangleOrder_eq_mul_levelIndex
  choose Φ q e using (@exists_isLevelTidy_iotaPlus_eq _ D · 0 zero_le)
  let t' {ϑ} (x : ∀ p : _ × Fin D.m, _ ⧸ D.nodeLevel ϑ (p.1, 0, p.2)) : ∀ p, GL _ _
    | (z, 0, i) => if h : _ then (x (z, ⟨i, h⟩)).out else 1 | _ => 1
  let t {ϑ} x := update (@t' ϑ x) (_, 0, 0) (blockInlGL (gridDiagEquiv ..) (t' x (_, 0, 0)))
  refine ⟨κ D.m * (range D.m).prod κ, (Φ · |>.bind (fun _ x ↦ edgeCharProd (t x) (D.path 0)) fun S
    x ↦ tupleAction (t x)⁻¹ S), fun ϑ ↦ ⟨⟨fun g ⟨G, G'⟩ f ↦ ?_, add_mul 2 2 _ ▸ (q ϑ).1.bind (by
    simp; grw [prod_le_pow_card _ _ (tupleBound ϑ)]; simp; exact fun p _ ↦ (card_le_of_embedding ⟨_,
    Units.val_injective.comp Quotient.out_injective⟩).trans (by simp [card_matrix_le_tupleBound]))
    fun S x _ n ↦ ⟨(CommMonoid.torsion ℂ).prod_mem fun _ _ ↦ (edgeChar ..).isOfFinOrder
    (Units.isUnit _).isOfFinOrder, fun e a b ↦ (n e a b).imp' ((t x e.1).1 * · * (t x e.2)⁻¹.1)
    fun L h ↦ by simp [tupleAction, ← L.mul_assoc, h]⟩⟩, fun r Ξ φ ↦ ?_⟩⟩
  · simp [LinearMap.pi, ← sum_fn, ← Pi.smul_def, -smul_eq_mul]
    rw [mul_sum, ← (piCongrRight fun p ↦ toPerm (g (p.1, 0, p.2))).sum_comp, eq_comm]
    congr with x
    set y := piCongrRight _ x
    have E z i (h : i ≤ D.m) : (t' y _)⁻¹ * (g _ * t' x _) ∈ nodeLevel ϑ (z, 0, i) := by
      obtain rfl | h := h.eq_or_lt <;> simp [t', ← QuotientGroup.eq, y, ← Quotient.mk_smul_out, *]
    erw [← mul_assoc, ← edgeCharProd_mul, ← mul_inv_cancel_left (t y) (g * _), edgeCharProd_mul,
      mul_assoc, ← (q ϑ).2]
    delta tupleAction; simp
    rintro ⟨⟩ ⟨⟩ _ <;> simp [t, *, ← map_inv, ← map_mul, Subgroup.mem_bot.1 (E false ..)]
  simp +unfoldPartialApp [-diagonalPeriodForm, LinearMap.pi, gridPathMap, ← fun x ↦
    @diagonalPeriodForm_tupleAction _ D ϑ (t x) (by simp [t, t', m_eq_two_mul_varrho_add_two])
    (by simp [t]), tupleAction, mul_left_comm _ (levelIndex ..)]
  erw [e, (Φ ϑ).map_smul, (Φ ϑ).map_smul]
  simp [prod_prod_type, prod_range, K]
  simp [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, levelIndex_eq_untwisted]; ac_rfl
end Data
end

section
/-! Every row pairs with a restriction of explicit level. Every nonzero form of level g on the
indefinite U(Y_0) pairs nontrivially with the restriction of a real translate of a form on a unitary
group of rank one more, descended from a definite group at a principal level of explicit depth, so
the construction of crude rows reaches all rows. Nonvanishing periods via Poincaré series of deep
level and restriction results of Burger–Sarnak type are known. Related work: Prasad–Schulze-Pillot,
Generalised form of a conjecture of Jacquet, 2008; Harris, Testing rationality of coherent
cohomology of Shimura varieties, 2014; Muić, Fourier coefficients of automorphic forms and
integrable discrete series, 2015.

This file: Descent chain is the transpose of the lift chain, hence onto. Form orthogonal to
restrictions of explicit deep level from rank one more vanishes. -/

open ComplexConjugate Finset Matrix MeasureTheory Space Submodule U

/-- For i ≤ m, let U be the lift of y from node (0, 0) to (0, i), each step weighted by
`Data.triangleOrder`, and ι_b = `Data.iotaPlus`. Then ∫ι_iφ·U = ∫ι₀φ·y for all φ; if i ≠ 0, U and
all ι_{i−1}φ have principal level `Data.triangleModulus`. -/
lemma Data.iotaPlus_adjoint_weightedChain {P} (D : Data P) z ϑ {i} (h : i ≤ D.m) y
    : let U := weightedChain (triangleOrder z) (D.triLift z) ϑ 0 i y; let ι := iotaPlus ϑ z
    (i ≠ 0 → (∀ φ u, (triangleModulus z ϑ).reductionK₀ u = 1 → formRep _ _ u.1 (ι (i - 1) φ) = ι _
      φ) ∧ ∀ u, (triangleModulus z ϑ).reductionK₀ u = 1 → formRep _ _ u.1 U = U) ∧ ∀ φ, ∫ g, ι i φ
      g * U g ∂(D.gridSpace ..).quotMeasure = ∫ g, ι 0 φ g * y g ∂(D.gridSpace ..).quotMeasure := by
   induction' i with i ih; tauto; have e := isEdgeFamily_grid id false (z := z) rfl bot_le
   simp only [(iotaPlus.eq_1 ..).trans (ite_eq_left h), i.succ_sub_one, ← ih (by omega)]
   refine ⟨fun _ ↦ ⟨fun _ u k ↦ ?_, fun u k ↦ ?_⟩, fun _ ↦ by erw [LinearMap.smul_apply, ← map_smul,
     e.isArrow_modDatum.1.integral_mul_formLift_swap e.isArrow_modDatum.2]; congr! 2; apply
     mul_right_comm⟩ <;> erw [LinearMap.map_smul]
     <;> [erw [e.isArrow_modDatum.2.formRep_formLift_of_eq_smul (pairWeil_modDatum_Kf _ _ _ _ _
     u 1 ..)]; erw [e.isArrow_modDatum.1.formRep_formLift_of_eq_smul (pairWeil_modDatum_Kf (k := 1)
     ..)]] <;> simp <;> erw [(gridChar_hasWeight ..).apply_det_eq_charOfTamePart _, k] <;> cases
     z <;> simp <;> first | rfl | use ((auxPair ..).tame_eq_one · <| places_levelModulus.ge.mt ·)

/-- The untwisted descent `Data.iotaPlus` from Z_{m,0} to Z_{0,0} (nodes (0, m) and (0, 0) of the
grid Z, `Data.gridSpace`) is onto on forms of principal level
`Data.gridLevelGen`. -/
lemma Data.gridLevelForms_eq_map_iotaPlus {P} (D : Data P) : D.gridLevelForms 0 = (D.gridLevelForms
  _).map (D.iotaPlus 1 _ 0) := have : Module.Finite ℂ (D.gridLevelForms D.m) := (finite_levelSpace
    (isConjKernelPair_gridKernel (by simp) _).1 ⟨_, isOpen_principalLevel Fact.out⟩)
  (sup_orthogonal_inf_of_hasOrthogonalProjection
    (K₁ := (D.gridLevelForms _).map (D.iotaPlus 1 _ 0)) (K₂ := D.gridLevelForms 0)
    (map_le_iff_le_comap.2 fun _ _ ⟨k, h⟩ ↦
    (((D.iotaPlus_adjoint_weightedChain _ 1 D.nat_le_of_hasLogBound 0).1 one_ne_zero).1 _ ⟨k,
    h.1⟩ ((Modulus.mem_principalLevel_iff gridModulus_one_ideal _).1 h)).trans
    (by simp))).symm.trans (sup_of_le_left (bot_le.trans' fun z ⟨hz, hy⟩ ↦ by
    let y : triBase .. := ⟨conjForm (isConjKernelPair_gridKernel (by simp) true).2 z,
      mem_levelSpace_formRep_iff.2 (by simp [mem_levelSpace_formRep_iff.1 hy · ·])⟩; have ⟨L, H⟩ :=
      D.iotaPlus_adjoint_weightedChain true 1 le_rfl y; rw [iotaPlus] at H; simp at H
    exact Subtype.ext (star_eq_zero.1
      congr($((exists_isTriangle ..).choose_spec.eq_zero_of_weightedChain _ 0 (by omega) y
      (inner_self_eq_zero.1 ((H (conjForm (isConjKernelPair_gridKernel (by simp) false).2 _)).trans
      (congr(integral _ $(mul_comm ..)).trans (inner_eq_zero_symm.1 (hz _ ⟨_,
      mem_levelSpace_formRep_iff.2 fun k h g ↦ congrArg (star <| · g) ((L NeZero.out).2 ⟨k,
      h.1⟩ ((Modulus.mem_principalLevel_iff gridModulus_one_ideal _).1 h)), rfl⟩)))))).1))))

open Norms.L2Operator

attribute [-simp] MulMemClass.coe_mul Subgroup.coe_mul

attribute [local simp] prod_eq_zero_iff prod_pos dsKernel abs_of_pos typeKernel mul_assoc ne_of_gt

/-- Under gap, size and matrix coefficient bounds there is a real g such that a form y of type l,
principal level `Data.chosenLevel`, on V vanishes if orthogonal to x ↦ φ((x⊕1)g) for all φ of type
l′, level K(`Data.gridLevelGen`), on V ⊕ ⟨1⟩. -/
lemma eq_zero_of_petersson_restrict_eq_zero {P : Parameters} {D : Data P} (n : Type) [Fintype n]
  [Nonempty n] {s : n → ℤˣ} {V : Space D.E n s} (A : ℕ) {L N : ℕ} (β : ℝ) {m : ℝ} {t :
  n ⊕ Unit → ℤˣ} {l : _ → HCParam s} {l' : _ → HCParam t} {e : s ⊕ᵥ 1 = t} (hg : ∀ w,
  (l w).HasLargeGap (4 * A)) (hg' : ∀ w, (l' w).HasLargeGap (2 * A)) (hl : ∀ w i, |l w i| ≤ L)
  (hA : 8 * (Fintype.card n + 1) ^ 2 < A) (hN : N < A) (hA' : 2 * D.f * (Fintype.card n + 1) + 2 ≤
  A) (hc : D.gProd * cuspConst D.E n D.cycloConductor ^ 2 ≤ β) (hβ : 2000 *
  (Fintype.card n + L + 1) ^ 6 ≤ β) (fβ : D.f ≤ β) (hm : β ^ (20 * A * (D.f + 1)) ≤ m) (hR : ∀ w,
  m ^ (3 * Fintype.card n + 2) ≤ ‖Φ w D.gridLevelGen.val‖) (H : ∀ w, ∃ ω : USign _, ‖ω.1.1‖ ^ 2 ≤ β
  ∧ volume.real {r : USign s | ‖r.1.1 - 1‖ ≤ 1} ≤ β ^ N * ‖∫ r : USign s, (l w).dsCoeff r * conj
  ((toHCParam (s ⊕ᵥ 1) (l' w)).dsCoeff (ω⁻¹ * inl s 1 r * ω).1.1)‖) : ∃ g, ∀ y ∈ levelSpace
  (V.formRep (typeKernel l s)) D.chosenLevel, (∀ φ ∈ levelSpace (((V.sum (signedSpace ..)).reindex
  (.refl _) e).formRep (typeKernel l' t)) (principalLevel _ D.gridLevelGen), V.petersson y
  (fun x ↦ φ (G.reindex (.refl _) e (.sum (x, 1)) * (g, 1))) = 0) → y.1 = 0 := by
  choose ω c H using H
  obtain ⟨rfl, b : 16 ≤ β, ke⟩ := e, hβ.trans' (mod_cast by lia), isCuspKernel_typeKernel hg
  obtain ⟨bm : β ≤ m, r : 2 ≤ β⟩ := by grw [← hm]; bound, by bound
  set v := Measure.real ..
  choose p I J using fun w ↦ And.intro (norm_dsCoeff_le_pow (hg w) (by bound))
    (integral_tail_le (hl w) (2 * A) (by lia))
  obtain ⟨_, _ : 0 < v, I : Integrable _ volume, J⟩ := b.trans bm, ENNReal.toReal_pos
    (measure_sublevel_ne_zero _) (measure_ball_ne_top_of_isProperMap _ .monoidHom_id _),
    .fintype_prod I, ((integral_fintype_prod_volume_eq_prod _).trans_le
    (prod_le_prod₀ (by delta formalDegree; positivity [·, ·]) fun w _ ↦ J w)).trans (c :=
    m / (16 * β) / (β ^ N * (2 * β) ^ (3 * A)) ^ D.f) (by
    grw [← hm, hβ, b, (by bound : 8 ≤ β), r]
    simp [field, ← pow_mul, ← pow_add, ← pow_succ', ← sq]; gcongr <;> nlinarith)
  refine ⟨ω, fun ⟨y, hy⟩ hK h0 ↦ have k a (h : _ ∣ a) :=
      (mem_levelSpace_formRep_iff.1 hK · <| D.principalLevel_le_chosenLevel h ·)
    funext (norm_le_zero_iff.1 <| le_of_halving hy.2.choose_spec le_rfl (fun S _ hS x ↦ .inl
    ((le_or_gt ..).elim (fun z ↦ ?_)
      (IsForm.norm_le_of_firstMinimum_lt hy ke P.cycloConductor_mem_different NeZero.out (k _ ⟨_,
    D.piGBar_mul_star.symm⟩) (δ := m⁻¹ ^ 2) (by bound) (by bound) · fun u h ↦ ?_))) ·)⟩
  · have F α := (norm_poincare_period_sub_le hy.1 hS Fact.out (k _ D.piGBar_dvd_gridLevelGen) hR hA'
      hA hg' (by bound) x (by
      grw [← z, hc, bm] <;> simp [field, div_pow, NeZero.pos, (one_le_cuspConst ..).trans_lt']
      ring_nf; rfl) (fβ.trans bm) (by bound) ω α).imp_right (·.trans_eq' (congrArg (‖· - _‖)
      ((exists_kernel_form _ (isCuspKernel_typeKernel hg') (G.sum (x, 1) * (α, 1))⁻¹ _).elim fun Q
      hQ ↦ by simpa [↓conj_petersson, hQ, petersson, tsum_mul_left, ↓tsum_mul_right] using!
      congrArg conj (h0 _ Q.2))))
    have T := (congrArg _ (integral_mul_realConv hy.isBoundedMeasurable (F ω).1 ke.1.2
      (x * ⟨·, 1⟩))).ge.trans (norm_integral_le_of_norm_le
      (I.mul_const (((2 * β) ^ (3 * A) * v) ^ D.f * S * 10 / m)) (.of_forall fun u ↦ ?_))
    · simp_rw [hy.realConv_translate ke, ← mul_assoc, integral_mul_const, norm_mul] at T
      nth_grw 1 [J, (congrArg _ (funext ?_)).trans (integral_fintype_prod_volume_eq_prod _)] at T
      grw [norm_prod, ← (div_le_iff₀' (by bound)).2 (H _)] at T
      simp [field, mul_pow] at T; nlinarith
      simp [field]
    obtain ⟨F, _⟩ := (F (inl .. ∘ u * ω)).2, (le_prod_opNorm u).1
    rw [realConv, ← integral_mul_left_eq_self _ u] at F
    simp [measureReal_pos_of_isLevel, realConv, Subgroup.coe_mul] at F ⊢
    grw [F, p, b, norm_mul_le]; simp [← sq]; grw [c]
    simp [field, div_pow, prod_pow, one_le_norm]; linear_combination
  have j g := hy.isBoundedMeasurable.integrable_mul_comp ke.1.2 (g * ⟨·, 1⟩)
  grw [← hy.3 ke.1.2, realConv, realConv, ← integral_mul_left_eq_self _ u⁻¹, ← integral_sub
    ((j _).comp_mul_left _) (j _), norm_integral_le_of_norm_le (((I.comp_mul_left u⁻¹).add
    I).mul_const (β / m * S)) (.of_forall fun r ↦ ?_), integral_mul_const, integral_add'
    (I.comp_mul_left _) I, (integral_mul_left_eq_self ..).trans_le J, J, div_le_self]
  field_simp; linarith; any_goals bound
  simp [← mul_sub, ← sub_mul, ← mul_add]
  grw [hS, ← mul_assoc]; gcongr
  nth_grw 1 [← sq_le_sq₀, sq, (?_ : ‖_‖ ≤ β * (β * m⁻¹ ^ 2)), norm_sub_le]
  simp; grw [p, p, ← sub_nonneg]; simp_rw [prod_pow]; ring_nf
  any_goals positivity
  apply ((ContinuousMultilinearMap.mkPiAlgebra ℂ _ ℂ).norm_image_sub_le ..).trans
  gcongr
  grw [fβ, pow_le_one₀] <;> simp [pi_norm_le_iff_of_nonempty, norm_dsCoeff_le_one]
  simp_rw [pi_norm_le_iff_of_nonempty, Pi.sub_apply, ← dsCoeff_inv, _root_.mul_inv_rev, inv_inv]
  intro
  grw [norm_dsCoeff_sub_le (hl _), ← dist_eq_norm, ← hβ, ← h, ← dist_le_pi_dist u 1 ‹_›]; bound

/-- There is a real point g of U(Z_{0,0}) such that a form y of level g₀g₁ on Y₀ vanishes if it is
orthogonal to x ↦ φ((x ⊕ 1)g) for all forms φ of principal level `Data.gridLevelGen` on
Z_{0,0} = Y₀ ⊕ ⟨1⟩.

Every row pairs with a restriction of explicit level. -/
lemma Data.eq_zero_of_orthogonal_gridLevelForms {P} (D : Data P) : ∃ g,
  ∀ y ∈ D.principalForms (D.spaceY 0), (∀ φ ∈ D.gridLevelForms 0, (spaceY ..).petersson y (fun x ↦
  φ (G.reindex (.refl _) D.gridSigns_zero.symm (.sum (x, 1)) * (g, 1))) = 0) → y.1 = 0 := by
  choose e S using D.exists_isSteep
  obtain ⟨o, a⟩ := pow_right_mono₀ (D.le_of_hasLogBound : 1 ≤ √D.gProd),
    (D.abs_gridParam_le (z := ·) · bot_le bot_le)
  have := D.hasLogLower_of_le (o (D.nat_le_of_hasLogBound : 3 ≤ ⌈D.x⌉₊))
  refine' eq_zero_of_petersson_restrict_eq_zero (D.Y 0) (D.r ^ 4) (√D.gProd ^ ⌈D.x⌉₊)
    (D.hasGap_signsY_paramW · |>.mono _) (D.hasGap_gridParam · .. |>.neg.mono _) (a false) _ _ _ _ _
    _ le_rfl (have := congr(√‖Φ · $D.piGBar_mul_star‖); _) fun w ↦ .imp (fun ω ⟨c, T, A⟩ ↦
    have b := le_trans (by grw [c]) _; ⟨b, (T.laplace_method (h := D.r ^ 7) _ ((hasGap_gridParam
      ..).mono _) ((D.gridSigns_zero ▸ hasGap_gridParam ..).neg.mono _) D.le_of_hasLogBound
    (a false w) ((abs_neg _).trans_le <| a true w ·) _ _ _ .monoidHom_id _ fun s o ↦ by
      grw [eq_add_of_sub_eq (A s), norm_add_le, norm_mul₃_le, ← b, U.norm_inv, norm_fromBlocks, o]
      simp [sq]).trans_eq congr(_ * ‖$(?_)‖)⟩) ((S _ w).exists_isTwoFactor_restriction (by grind)
    (D.gridSigns_zero ▸ S ..) (D.gridSigns_zero ▸ hasGap_gridParam ..) D.le_of_hasLogBound)
  any_goals simp [HCParam.laplaceIntegrand, gapThreshold, cuspConst, ↓card_rowIndex]
  any_goals first | exact D.le_of_hasLogBound | rfl | fun_prop | use D.nat_lt_of_hasLogBound | grw
    [(D.le_of_hasLogBound : _ + 1 ≤ √D.gProd),
    (D.le_of_hasLogBound : 6 * _ ≤ √D.gProd), ← pow_add, ← pow_mul] | simp_all [← pow_mul]
  repeat use o D.nat_le_of_hasLogBound
end

section
/-! Crude rows, with integral twisted lifts and bounded conjugates. Forms of level g on the
indefinite U(Y_0) are spanned by forms whose untwisted chain of
lifts has all conjugates explicitly bounded, and whose twisted chains are integral at primes prime
to the conductor after one scalar per twist that costs little height at the chosen twists.
Rationality or integrality of theta lifts via seesaw identities and periods along U(n+1)⊃U(n) is
known. Related work: Harris, Cohomological automorphic forms on unitary groups I, 1999; Prasanna,
Integrality of a ratio of Petersson norms, 2006; Grobner–Harris–Lin, Factorization of periods, 2025.

This file: The main result `Data.crude_rows`. Pairings of twisted chains of all rows are multiples
of the end period. -/

open Fintype Function Matrix MeasureTheory Real Space Submodule

variable {P : Parameters} (D : Data P)

/-- There are tidy data Φ ϑ of order 4m on `Data.path` 0, and g, α, a surjection r:
`Data.gridLevelForms` m → `Data.principalForms` Y₀ free of ϑ, with i·∫Ξ·lift(rφ) =
α·`Data.gridPeriod` Φ (ϑ, Ξ, φ) g; i = [K₀ : `Data.levelY` ϑ m], lift composes the m maps
`Data.liftY` ϑ. -/
lemma Data.exists_isTidy_integral_eq_gridPeriod : ∃ Φ, (∀ ϑ, IsTidy (4 * D.m) (D.path 0) (Φ ϑ)) ∧
  ∃ g α, ∃ r : D.gridLevelForms D.m →ₗ[ℂ] _, r.range = ⊤ ∧ ∀ (ϑ : D.MFoldTwist) Ξ φ,
  stdLevelIndex (D.levelY ϑ D.m) * ∫ x, Ξ x * D.liftChainY ϑ _ (r φ)
  x ∂(spaceY ..).quotMeasure = α * gridPeriod Φ (ϑ, Ξ, φ) zero_le g := by
  obtain ⟨⟨g, S⟩, ι⟩ := D.eq_zero_of_orthogonal_gridLevelForms, D.gridLevelForms_eq_map_iotaPlus
  choose C Λ q K using D.exists_isTidy_diagonalPeriodForm_eq
  choose r H using D.exists_restrict_bordered g
  use Λ, q, g, C, r ∘ₗ (iotaPlus ..).restrict (ι.ge ⟨·, ·, rfl⟩), orthogonal_eq_bot_iff.1
    (bot_unique fun y hy ↦ Subtype.ext (Subtype.ext (S _ y.2 (ι ▸ Set.forall_mem_image.2 fun φ
    m ↦ by simpa [periodPairing] using! (H _ 1 _ (levelSpace_anti (levelY_le_chosenLevel ..)
    y.2)).symm.trans (inner_eq_zero_symm.1 (hy _ ⟨⟨φ, m⟩, rfl⟩)))))), fun ϑ Ξ φ ↦ K .. ▸ ?_
  obtain ⟨Z, Y⟩ := (H · ϑ (conjForm (isConjKernelPair_gridKernel (by simp) true).2 (iotaPlus ϑ _ 0
    Ξ)) (mem_levelSpace_formRep_iff.2 fun k a g ↦ congr(star ($(((D.iotaPlus_adjoint_weightedChain
    false ϑ D.nat_le_of_hasLogBound 0).1 one_ne_zero).1 _ _ ((LevelPlaces.ker_reductionK₀_eq _).ge
    (mem_levelOf.1 a).2)) g)))), (D.iotaPlus_adjoint_weightedChain _ ϑ .refl · |>.2 Ξ)
  simp +unfoldPartialApp [liftY, liftChainY, petersson, periodPairing, iotaPlus.eq_1 _ _ D.m,
    ← LevelPlaces.card_GL_levelModulus, -Subtype.forall] at *
  erw [Y, Z]; rfl

/-- For some d(ϑ) costing k squares, tidy data of order n on path i yield tidy data of order n +
k on path j; if the new periods are constant multiples of T, the old are of T/d. -/
def Data.HasRoute {i j} (h : i ≤ D.m) (h' : j ≤ D.m) k := ∃ d : _ → ℂˣ, D.CostsSquares k (d ·) ∧ ∀ n
  Λ, (∀ ϑ, IsTidy n (D.path i) (Λ ϑ)) → ∃ Φ, (∀ ϑ, IsTidy (n + k) (D.path j) (Φ ϑ)) ∧ ∀ T : _ → ℂ,
  (∀ g, ∃ β, ∀ x, gridPeriod Φ x h' g = β * T x) → ∀ g, ∃ β, ∀ x, gridPeriod Λ x h g =
  β * (T x / d x.1)

/-- For j < m there is a `Data.HasRoute` of cost 4j + 2 from path j to path j + 1: tidy data of
order n give tidy data of order n + 4j + 2, and if the new periods are multiples of T, the
old are multiples of T/d. -/
lemma Data.hasRoute_succ {j} (h : j < D.m) : D.HasRoute (j := j + 1) h.le h (4 * j + 2) := by
  obtain ⟨⟨t, o⟩, ⟨ι, ν, s⟩, H, κ₀, σ, c₃, g₃, Q⟩ := D.t_odd, gridSpace_subdiag j,
    exists_modKernel_flip_line (gridSpace ..) (-(-1) ^ j), exists_squareLaw_grid false h h
  rw [neg_neg, ← mul_neg_one (_ ^ j), ← pow_succ] at H
  generalize flipPoly (E := D.E) _ _ = τ at H
  choose κ₁ c₁ g₁ H₁ using (descent_past_gridPathMap h · .refl); let N := D.GridIndex false j.succ j
  choose ψ c hc H using fun ϑ ↦
    H (gridModulus ϑ) (gridChar ϑ false j N) (gridChar ϑ true j N) (Modulus.flipScalar _ ^ j)
  use c₁ false * c₁ true * c₃ * c⁻¹,
    (((g₁ _).mul (g₁ _) .refl).mul g₃ .refl).mul (.of_norm_sq_eq_mul_card_zpow _ 1
    (card N) (by simpa [field, eq_comm] using hc)) (by omega), fun n Λ hΛ ↦ ?_
  choose Φ₁ q₁ e₁ using (H₁ _ · _ _ _ (by simp [gridPath, legEdges]) (hΛ _))
  choose Φ₂ q₂ e₂ using (H₁ _ · _ _ _ (by simp [gridPath, legEdges]) (q₁ _))
  simp [↓Finset.insert_union] at q₂
  let u := D.gridDiagEquiv
  choose Φ₀ q₀ e₀ using (q₂ · |>.exists_square_move (_, _, _) ι.symm (u _) (u _) (ψ _) (Q _) (R :=
    (_, _, _)) (by simp [IsAdmissibleFamily, update, h.ne']; clear * -; bound)
    (by simp [gridPath, legEdges]; clear * - h; grind))
  use Φ₀, by simpa +arith [path, gridPath, Finset.range_add_one] using q₀, fun T X g ↦ ?_
  choose _ _ _ _ _ _ E using @IsTidy.isShortSum _ D; let e := (G.reindex (E := D.E) _ ν).symm
  have : Continuous e := G.continuous_reindex _ (by simp [← ν, comp_def])
  have t x := by simpa [e, ← s] using (gridSpace ..).height_reindex _ ν (e x)
  refine (seesaw_periods _ (c := fun x ↦ T x / (c₃ / c) x.1) (T := gridSpace ..) (E <|
    q₂ ·.1) (isEdgeFamily_grid (·.1) true rfl) (isEdgeFamily_grid _ false rfl) fun P _ ↦ mul_le.2 ?_
    (mem_rename_range_mul (.map id (.map ι.symm (u _ ∘ .inl))) (.map id (.map ι.symm (u _ ∘ .inr)))
    (by simp [reindex_equiv (u _)]) P)).imp' (κ₁ false * κ₁ true * ·) fun β b x ↦
    ((e₁ _ _ (fun S ↦ diagonalPeriodForm _ _ g _) ?_).trans congr(_ * $((e₂ _ _ (fun S ↦
    (diagonalPeriodForm _ h.le g).flip _) ?_).trans congr(_ * $(b x))))).trans (by simp [field])
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  let K 𝔪 a z Ψ : ModerateWeight (gridSpace ..) (gridSpace ..) := ⟨⟨fun x ↦
    z * modKernel (gridSpace ..) (signedSpace _ fun _ ↦ (-1) ^ j.succ) a WeilData.upsilonU1 𝔪 Ψ
    (τ B) (e x) (1, 𝔪.flipScalar ^ j * 𝔪.flipScalar), by fun_prop [modKernel]⟩, ⟨e, ‹_›⟩, ⟨_, _, (by
    simp; grw [modKernel, pairTheta, ((pairThetaKer ..).isModerate ..).choose_spec.choose_spec, t ·,
      mul_assoc])⟩, 1, by simp [t, e]⟩
  have Z 𝔪 a z ψ x r G (F y : GridForm ..) : periodPairing G (K 𝔪 a z (matrixFourier ψ (Pi.single
    x 1))) r F y = z * ∑ k, ψ (k * x).trace * periodPairing G (K 𝔪 a 1 (Pi.single k 1)) r F y := by
    simp [periodPairing, ← integral_const_mul, ← integral_finsetSum,
      (integrable_moderate_mul_forms G ..).const_mul]
    simp [K, modKernel, pairTheta, modDatum_eq_sum _ _ (matrixFourier _ _), matrixFourier,
      Finset.sum_mul, Finset.mul_sum]; ac_rfl
  refine' subset_span ⟨A, _, _, fun r ↦ (seesaw_periods _ (E <| q₀ ·.1) (isEdgeFamily_grid _ true
    rfl) (isEdgeFamily_grid _ false rfl) fun _ _ ↦ subset_span ⟨_, _, _, X, fun _ _ _ _ ↦ _⟩).imp'
    (κ₀ * ·) fun β b o ↦ (congrArg _ (funext fun S ↦ Z ..)).trans ((map_smul _ (c o.1).1 _).trans
    (congr(_ * $((e₀ _ (fun S k ↦ (gridPathMap S _ j _ (levelIndex .. • o.2.1),
    periodPairing _ (K _ (gridChar o.1 true j N) 1 (Pi.single k 1)) r (gridPathMap S _ j
    _ o.2.2))) _).trans congr(_ * $(b o)))).trans (by simp [field]))), fun _ _ _ _ ↦ _⟩
  on_goal 4 => simp [K]; erw [← H, eq_comm, mul_comm, ← modKernel_sum_left,
    ← modKernel_reindex (u _) (D.gridDiagEquiv_spec h.le) _ ν, ← gridSpace_diag h.le, ← s]; congr 1
  on_goal 2 => simp [K]; erw [mul_comm, ← modKernel_sum_right, ← modKernel_reindex _ ν
    (u _) (D.gridDiagEquiv_spec h), ← gridSpace_diag h, ← s]; congr! -closePost 1
  any_goals exact (by simp +contextual [gridPathMap_congr · ·])
  all_goals clear * - o e u; simp [gridChar, card_gridIndex, mul_assoc, ← pow_succ, *, e,
    funext_iff, ← ext_iff, reindex_equiv ι.symm, reindex_equiv (u _), Prod.map_comp_map] <;> grind

/-- For j ≤ m there is a `Data.HasRoute` of cost 2j² from path 0 to path j: tidy data of order
n give tidy data of order n + 2j², and if the new periods are multiples of T, the old are
multiples of T/d. -/
lemma Data.gridPeriod_climb {j} (h : j ≤ D.m) : D.HasRoute zero_le h (2 * j * j) := by
  induction' j with j i
  · use 1, .one, fun _ ↦ (⟨·, ·, by simp⟩)
  obtain ⟨⟨c, g, X⟩, d, g', H⟩ := i (by lia), D.hasRoute_succ h
  use d * c, g'.mul g (by lia), (X · · · |>.elim fun Φ ⟨q, X⟩ ↦ (H _ Φ q).imp fun _ ↦
    .imp (by grind) (by simpa [div_div] using X _ <| · · ·))

seal HCParam.dsKernel

/-- Some integer 0 < N ≤ exp(x⁹⁹b²) makes N·`endPeriod Λ y` integral at every p prime to N(Q), for
tidy Λ on `Data.path` m and p-integral forms y as in `Data.FixedByEndLevels`. -/
lemma Data.exists_mul_endPeriod_mem_embValRing : ∃ N ≠ (0 : ℕ), N ≤ exp (D.x ^ 99 * D.b ^ 2) ∧
  ∀ {ϑ n} {Λ : GridDatum ϑ} {y p} [Fact p.Prime] [PadicPlace p], IsTidy n (D.path D.m) Λ →
  FixedByEndLevels ϑ y → p.Coprime ϑ.levelNorm → (∀ z g, weylGauge _
  (endDetExp z 0) g ((D.endToAlgForm z (y z)).1 g) ≤ 1) → N * endPeriod Λ y ∈ embValRing :=
  D.endBranching.2.1.elim fun L ⟨B, C, _⟩ ↦ by
  choose a b c using boxes_endWeightData_le
  use (∏ τ, (D.gProd ^ D.b₁ * D.N₁) ^ (D.m * (L τ).natAbs)) * (?ν ^ D.m) ^ 2, ?_, le_exp_of_log_le
    ?_, fun h hy q k ↦ (embValRing.toAddSubgroup.comap (.mulLeft _)).nsmul_subset .rfl
    (endPeriod_mem h hy (fun z j g v ↦ weylGauge _ (D.endDetExp z j) g (((?ν : ℂ) • ·)^[j] v) ≤ 1)
    ιₚ (fun _ _ _ j g h v ↦ .trans (by
    simpa [endKernel] using P.mem_raises_of_dvd (endDatum ..)
      (P.smul_vacuumDatum_mem_standardData norm_mul_gProd_pow_mem_modulus (by
    simp [ite_mem]) q) embValRing.one_mem (by grw [card_prod, b, a, a]; use 1; exacts
              [j.le, j, j]) g h ((_ : ℂ) • v))) k fun {g _ _} a b ↦ ?_).choose_spec.2
  iterate 2 simp [log_prod, log_mul, NeZero.ne, Finset.prod_eq_zero_iff, -Nat.cast_natAbs]
  grw [C, b, c] <;> simp; simpa using D.le_of_hasLogBound
  erw [Nat.cast_mul, mul_assoc, Nat.cast_pow, sq, ← smul_eq_mul (_ * _), mul_smul, ← map_smul,
    ← D.endPairing.map_smul₂, map_mul, ιₚ.map_dotProduct, Nat.cast_pow]
  simp only [map_natCast, comp_def, ιₚ.map_mulVec, smul_iterate, mulVecLin_apply, weylGauge,
    ← map_inv, Matrix.map_map, map_intCast, endBlockPoint,
    pi_norm_le_iff_of_nonneg one_pos.le] at a b ⊢
  rw [← (Units.inv_mul_eq_iff_eq_mul _).2 (B _ _ _ g⁻¹ ..), ← mul_assoc, Nat.cast_prod,
    ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine NormedField.valuation.integer.mul_mem (prod_mem fun τ _ ↦ ?_) (sum_mem fun _ _ ↦
    mul_mem (a _) (sum_mem fun _ _ ↦ mul_mem (by simp) (b _)))
  obtain ⟨u, n, e | e⟩ := mul_mem (((gridModulus ‹_›).generator_spec.2.2 _).1
    ((Modulus.reduction_eq_zero_iff _).2 (Ideal.mem_map_of_mem _ norm_mul_gProd_pow_mem_modulus)))
    (mul_mem (star_mem_Ô (mul_mem (Modulus.generator_spec _).1
    P.N₁_mul_α_mem)) P.inv_α_mem), (L τ).eq_nat_or_neg <;> [skip; apply star_mem_Ô at u] <;>
    use (norm_adeleExtension_le_one ((ιₚ.comp _).comp _) (pow_mem u (D.m * n))).trans_eq'
    (by simp [Modulus.flipScalar, e, scalarFin, coe_divStar, WeilData.α, ← inv_pow,
    adeleExtension_star, q.norm_natCast_eq_one, -Nat.cast_prod]; ring)

/-- For the trivial twist, let Λ be tidy of order 4m + 2m² on `Data.path` m, y a pair of
forms as in `Data.FixedByEndLevels`, σ an automorphism of ℂ. If the σ-conjugate values have squared
norms at most B, B′, then |σ(`Data.endPeriod`(Λ, y))| ≤ exp(x²⁰⁰b²)√B√B′. -/
lemma Data.endPeriod_le {Λ : GridDatum 1} {y} (h :
  IsTidy (4 * D.m + 2 * D.m * D.m) (D.path D.m) Λ) (hy : FixedByEndLevels 1 y)
  (σ : ℂ ≃+* ℂ) {B : _ → ℝ} (k : ∀ z g, weylNormSq (σ ∘ (D.endToAlgForm z (y z)).1 g) ≤ B z) :
  ‖σ (endPeriod Λ y)‖ ≤ exp (D.x ^ 200 * D.b ^ 2) * √(B false) * √(B true) := by
  choose a b _ using boxes_endWeightData_le
  let G := (D.x ^ 99 * D.b ^ 2).exp
  have hn z j h : _ ≤ G := (D.card_stdClasses_le_exp_mul_log (K := endLevel 1 z j) (1 * _) (a z h)
    (by with_unfolding_all exact
    Modulus.principalLevel_le_levelOfSubgroup norm_mul_gProd_pow_mem_modulus)).trans
    (by simpa [G] using D.le_of_hasLogBound)
  choose _ q r using endPeriod_mem h hy (fun z j _ v ↦ √(weylNormSq (σ ∘ v)) ≤ G ^ j * √(B z))
    σ.toRingHom (M := 1) (fun x z j o g h v u ↦ have k := ((D.endWeightData z).2.2.1 j).1
    ((P.norm_jet_le_of_isAdmissibleComb
      (P.isAdmissibleComb_vacuumDatum 1 (by simp [apply_ite, ite_le_one])) ..).2 1 k v).trans (by
    rcases D.hasLogUpper_of_le (a z o), D.hasLogUpper_of_le (a z o.le)
    simp_rw [Finset.sum_range, ← sum_prod_type']
    grw [pow_succ' G, mul_assoc G, le_abs_self (log (_ / _)), le_exp_log (_ * 1), ← exp_add,
      (Finset.single_le_sum (by simp) (by simp)).trans
      (k.1.sum_diagramWeight_eq_boxes.trans_le (b z o))]
    gcongr; simpa [G, card_𝔪, prod_q_chosenPlace, twist_one_spec] using D.le_of_hasLogBound))
    (by simp [sqrt_le_sqrt, k]) fun u v ↦ ((D.endBranching.2.1.choose_spec.2.2 _
    (b _ le_rfl) ..).trans (by grw [u, v])).trans_eq' (by simp [entrywise])
  let ⟨v, u, s⟩ := Set.mem_nsmul_iff_sum.1 r
  grw [← s, map_sum, norm_sum_le_of_le _ (by simpa [-univ_bool] using u), Fin.sum_const]
  simp [-Nat.card_eq_fintype_card, ← mul_assoc, mul_right_comm _ √(B false)]
  grw [hn, hn, q, ← le_exp_of_log_le]
  simpa [log_mul, G, NeZero.ne, card_𝔪, prod_q_chosenPlace, twist_one_spec] using
    D.le_of_hasLogBound
  repeat grind

/-- Some nowhere zero c(ϑ) costs 2m² squares (`Data.CostsSquares`), and the forms of level K(g) on
Y₀ are spanned by the y with c(ϑ)/c(1)·ι_ϑ y integral above every l prime to the norms in Q(ϑ) and
all conjugates of values of ι₁y of squared norm ≤ exp(x₁²b²).

Crude rows: integral twisted lifts and bounded conjugates. -/
lemma Data.crude_rows : ∃ c : _ → ℂˣ, D.CostsSquares (2 * D.m * D.m) (c ·) ∧ span ℂ {y |
    (∀ ϑ l [Fact l.Prime] ι, l.Coprime ϑ.levelNorm →
  (c ϑ / c 1 : ℂ) • D.iotaAtLevel ϑ y ∈ LevelPlaces.LevelForm.integralForms (l := l) ι) ∧
  ∀ (σ : ℂ ≃+* ℂ) g, weylNormSq (σ ∘ (D.ι .one y).1 g) ≤ exp (D.x₁ ^ 2 * D.b ^ 2)} = ⊤ := by
  choose Λ q g α r R J using D.exists_isTidy_integral_eq_gridPeriod; choose N n C B using
    D.exists_mul_endPeriod_mem_embValRing
  choose c hc H using D.gridPeriod_climb le_rfl; choose Φ hΦ H using H _ Λ q
  choose A L l m o using
    exists_dual_pairing_of_isHCParam D.isHCParam_Y ((D.endWeightData _).2.2.2 0 bot_le)
  choose β H using H _ (D.gridPeriod_eq_endPeriod Φ) g; use c, hc, eq_top_mono ?_ R
  simp_rw [H] at J; set β := α * β
  choose t f using show Associated β (β / β) by by_cases β = 0 <;> simp [*]
  choose a b _ using boxes_endWeightData_le
  let e := (D.gridSpace 0 ..).algFormEquiv ((D.endWeightData true).2.2.2 0 bot_le)
    (principalLevel _ D.gridLevelGen)
  let ξ ϑ x v : levelSpace (algFormRep (D.endWeightData false).1 (endDetExp false 0))
    (levelY ϑ D.m) := deltaForm _ _ 1 x v
  let Ξ ϑ x v := (D.endToAlgForm false).symm (ξ ϑ x v).1
  have h' ϑ x v : D.endToAlgForm _ (Ξ ϑ x v) = _ := (endToAlgForm ..).4 _
  erw [r.range_eq_map, ← e.range, e.range_eq_map, ← span_isShort_eq_top (B :=
    (D.x ^ 99 * D.b ^ 2).exp) (classAut_eq_bot_of_le_chosenLevel (principalLevel_le_chosenLevel
    piGBar_dvd_gridLevelGen) (a _ zero_le)) P.cycloConductor_mem_different (by grw [b, a] <;> simp)
    (by grw [shortBasisConst, a _ zero_le]; exact le_exp_of_log_le D.le_of_hasLogBound), map_span,
    e.image_eq_preimage_symm, map_span_le]
  have E ϑ x v (φ : D.gridLevelForms _) : FixedByEndLevels ϑ (·.rec (Ξ ϑ x v) φ.1) := Bool.rec
    (h' .. ▸ levelSpace_anti (Subgroup.map_mono fun k b ↦ funext fun i ↦ by simpa using! (congrArg
    (·.1.map (modulusResidue _ (places_levelModulus.ge ⟨i, rfl⟩))) b)) (ξ ..).2)
    (levelSpace_anti (endLevel_le_principalLevel ..) (e.symm φ).2)
  have δ (η : ℤ) ϑ x v φ : v ⬝ᵥ A.map (↑) *ᵥ (((c ϑ).1 / c 1) • D.ι ϑ ((t.1 * c 1 * η * N / card
    (WeylIndex (D.Y D.m) D.columnsY)) • r φ)).1 x =
    η * (β / β * (N * endPeriod (Φ ϑ) (·.rec (Ξ ϑ x v) φ.1))) := by
    obtain ⟨p, q⟩ := J ϑ (Ξ ϑ x v) φ, ((D.iotaAtLevel ϑ (r φ)).algFormRep_eq_self_of_mem (k := ·))
    erw [← ofAlgForm_toAlgForm D.isHCParam_Y (liftChainY _ _ _),
      integral_mul_eq_classIntegral D.isHCParam_Y (D.levelY ϑ _) (isAutomorphic_algFormCoeff _) _
      (l _ _), classIntegral_eq_classSum, classSum_deltaForm fun _ ↦ .mk' (· ⬝ᵥ _) (by simp)] at p
    simpa [← f, n, field, -card_pi, mul_comm (c ϑ).1, mul_assoc] using! congr(η * N * $p)
    intros; rw [levelSpace_smoothFormRep_apply (χ := 1) (by simpa)]; simpa using! L ..
    intro _ h g; simpa using! congr($((ξ ..).2 ⟨_, h⟩).1 g ⬝ᵥ _ *ᵥ $(q _ h).1 g)
  refine fun φ k ↦ (smul_mem_iff _ ?_).1 (subset_span ⟨fun ϑ p _ _ q ↦
    weylGauge_le_one_of_integralAbove _ fun x _ i ↦ congr($(mul_left_cancel₀ (by simp)
    (congr($(m.choose_spec _) i).symm.trans (δ ..))) ∈ embValRing).mpr (mul_mem
    (by simp [div_self_le_one]) (B (hΦ ϑ) (E ϑ x _ φ) q (Bool.rec (fun y ↦ h'
    .. ▸ (weylGauge_deltaForm_le (by simp)).trans <| by simp [IsUltrametricDist.norm_intCast_le_one,
    weylGauge_le_one_iff, *]) (by simpa using! k.1 p ·)))), fun σ x ↦ (o _).elim fun w ⟨u, v⟩ ↦
    u ▸ ?_⟩)
  simp [n, -card_pi]
  have s := D.endPeriod_le (hΦ 1) (E 1 x (σ.symm ∘ w) φ) σ (B := (ite · (D.x ^ 99 * D.b ^ 2).exp
    (weylNormSq w))) (Bool.rec (fun _ ↦ h' .. ▸ (weylNormSq_deltaForm_le (by simp) ..).trans
    (by simp [D.classAut_eq_bot_of_le_chosenLevel (levelY_le_chosenLevel ..) (a false zero_le),
    comp_def])) (k.2 σ))
  have e := congr(‖$((PolyRep.coe_weylNormSq w).trans ((v w).symm.trans (.trans
    (by simp [dotProduct, mulVec]; rfl) congr(σ $(δ _ 1 _ (σ.symm ∘ w) _)))))‖).le
  simp [abs_of_nonneg, ← mul_assoc, le_of_lt] at e s
  nth_grw 1 [hookNumber_le (by exact b false zero_le), div_self_le_one, s, C, ← mul_assoc,
    ← mul_assoc, mul_right_comm] at e
  exact (sqrt_le_iff.1 (div_sqrt ▸ div_le_of_le_mul₀ (by simp) (by positivity) e)).2.trans
    (le_exp_of_log_le (by simpa [log_mul, ← exp_half, NeZero.ne] using D.le_of_hasLogBound))
end
