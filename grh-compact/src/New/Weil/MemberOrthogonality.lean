import New.Weil.SingularForms
import New.Weil.FourierCoefficient
import New.Weil.MonomialCoefficientVector

-- part: Lib.Shimura.ComplexTheta.PeriodVanishing
section
/-! Known result: Fourier coefficients of theta lifts as periods over stabilisers. Here one
non-degenerate coefficient of a theta lift to a split unitary group is unfolded once by Witt's
theorem. Hence a form on the definite U(n) orthogonal to the theta kernels of the split space has
zero period over the complementary unitary group. Source: P. Walls, The theta correspondence,
periods of automorphic forms and special values of standard automorphic L-functions, arXiv
1501.01565 (2015), Prop. 2.1.1; S. Rallis, On the Howe duality conjecture, Compositio Math. 51
(1984) 333–399.

This file: Vanishing theta descent to the split group forces zero period over the stabiliser. -/

open ContinuousMap Subgroup AddChar G Gf MatMul Matrix MeasureTheory Space WeilData Splitting

attribute [local simp ←] Circle.coe_inv_eq_conj conjTranspose_mul ext_iff add_mul map_add map_mul

attribute [local simp] IsIntMatrix Matrix.mul_apply val_scaleIdele_snd inclMatrix ite_mem mul_add
  mul_assoc sq matToVec

/-- Let Y on U(I_n), n = n₁ + n₂, be continuous, left invariant under rational points, fixed by
the part of K₀ = `Kf` above T ∪ T̄, and satisfy `DescentsVanish` for ℍ^{n₁}, υ^{n₁}, T. Then the
period ∫Y(h₁u)du over [U(I_{n₂})] vanishes for every h₁ in the first block.

Known result: Fourier coefficients of theta lifts as periods over stabilisers. -/
lemma period_eq_zero {E n n₁ n₂} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n₁]
    [Fintype n₂] {T Y} (c : Continuous Y) (hY : (stdSpace E n).Γ.FixesLeft Y) (hK : HasLevel Y
    (Kf E n ⊓ supportedOn n T)) (o : n₁ ⊕ n₂ ≃ n) hs (h :
  DescentsVanish (hypSpace E n₁) (stdSpace ..) (1 * upsilonU1 ^ Fintype.card
  n₁) T Y) h₁ : ∫ u, Y (blockEmb (s₁ := 1) (e := o) hs (h₁, u)) ∂(stdSpace ..).quotMeasure = 0 := by
  set V := stdSpace E n
  let i := (blockEmb hs).comp (.inr _ (G E _))
  let t h := h⁻¹ * blockEmb hs (h₁, 1)
  have j := isClosedEmbedding_blockEmb (E := E) hs
  have : Continuous i := j.continuous.comp (.prodMk_right 1)
  have iΓ : (stdSpace ..).Γ = V.Γ.comap i := Subgroup.ext (by simp [i, V])
  let y := (inclMatrix E (o ∘ .inl)).map toAdele
  have hm g : mat (E := E) (blockEmb hs g) * y =
    y * g.1.mat := by simp [reindex_equiv o, blockEmb, y]
  have fy {g} : g ∈ i.range ↔ g.mat * y = y := ⟨(·.choose_spec ▸ by simp [i, hm]), fun h ↦
    ((U.mem_range_sum stdForm_sum (g := (reindex o.symm hs g).toUnitary).2 (by simp)).2 (by
    simpa [reindex_equiv o, y] using! h)).imp' toUnitary.symm fun a e ↦
    (reindex _ hs).symm_apply_eq.2 (ext_mat (by simpa using! congr(($e).1.1)))⟩
  let η (d : G E (1 : n → _)) := d.mat * y
  let Φ h := ‖vacuumFn ((scaleIdele E).1 • matToVec (η h))‖ ^ 2
  let e g u :=
    stdAddChar E (invDifferentIdele E * ((1 - idemAdele T.conjClosure) * u ⬝ᵥ matToVec (η g)))
  obtain ⟨hr, ce : Continuous e, _ : Continuous Φ⟩ :=
    isRapid_of_isCocompact c hY V.exists_isCompact_of_definite, by
    fun_prop [matToVec], (isVacuum_vacuumFn (s := 1).cont.comp (by fun_prop [matToVec])).norm.pow 2
  have h u : let F g := e (t g) u * Φ (t g) • Y g; let q := ((stdSpace ..).Γ.map i).qms
      Integrable F q ∧ integral q F = 0 := ?_
  let B g := ∫ h, Y (i h * (t 1 * g⁻¹)) ∂(stdSpace ..).quotMeasure
  have cB : Continuous B := hr.bounded.elim fun C b ↦ continuous_of_dominated (by fun_prop) (by
    simp [b]) (integrable_const C) (.of_forall (by fun_prop))
  have fx {a b} (e : η a = η b) : B b = B a := (fy.2 ((mul_smul _ a y).trans (inv_smul_eq_iff.2
    e))).elim fun v h ↦ by simpa +zetaDelta [← mul_inv_eq_of_eq_mul h, ← mul_assoc] using
    ((stdSpace ..).integral_comp_mul_right v (by simp +contextual [map_mul, *]) (F :=
    (Y <| i · * (t 1 * a⁻¹)))).1
  by_contra p0
  have ⟨φ, f, z⟩ := CompletelyRegularSpace.exists_BCNN (((isCompact_univ.prod isCompact_Kf).diff
    ((Complex.isOpen_re_gt 0).preimage (cB.div_const (B 1)))).image ce).isClosed (x := e 1) ?_
  have H φ := (h 0).1.bdd_mul (by fun_prop) (.of_forall (norm_coe_le_norm φ <| e <| t ·))
  have L := strongIntegral_apply _ (fun g ↦ .smulRight (evalCLM (M := ℂ) ℂ (e (t g))) _) H
  have z₁ := ContinuousLinearMap.ext_on (g := 0) (stone_weierstrass_span ⟨⟨{φ | ∃ u, ∀ g,
    φ (e g) = e g u}, fun ⟨u, _⟩ ⟨v, _⟩ ↦ ⟨u + v, by simp [*, e, map_add_eq_mul]⟩⟩, 0, by simp [e]⟩
    (fun φ ⟨u, h⟩ ↦ ⟨-u, by simp [e, *, map_neg_eq_inv]⟩) fun x y c ↦ by ext u; exact (c (.mk (· u))
    (by tauto))) fun φ ⟨u, hu⟩ ↦ (L φ).trans (by simp [hu, ← (h u).2, e])
  refine (exists_integral_stages_eq_mul _ _ volume Measure.count (i.comp (.snd Unit _)) (j.comp
    (.prodMap ⟨.of_subsingleton 1, by simp⟩ .id)) ((fun g ↦ φ (e g) * Φ g * (B g / B 1)) ∘ t) (by
    simp_intro h [mul_nonneg_iff_pos_imp_nonneg, Φ]; by_contra! ⟨a, b, l⟩
    have ⟨d, hd, ed⟩ := (fun x ↦ witt_Ohat_of_orthonormal (X :=
      inclMatrix _ (o ∘ .inl)) x ((U.gram_invariant (t h).2 ..).trans x))
      (by simp) (by simp) (by simpa [vacuumFn, η, y] using b)
    have k : η ((t h).1, d) = η (t h) := by simp [η, y, Prod.ext_iff] at ed ⊢; tauto
    exact a.ne' (z _ ⟨(_, d), ⟨⟨⟨⟩, hd⟩, (fx k ▸ l).not_gt⟩, by simp [e, k]⟩))
    ((Continuous.tendsto (by fun_prop) (t 1)).eventually_ne (by simp [-Complex.norm_exp, B, t, i,
    f, p0, Φ, vacuumFn, η, y]))).elim fun R ⟨r, q⟩ ↦ mul_ne_zero r p0 ((z₁ ▸ L (.mk (φ ·)) :).trans
    (q _ (by fun_prop) (Set.forall_mem_image.2 ?_) (H (.mk (φ ·))) _ fun g ↦ ⟨1, ?_⟩)).symm <;>
    simp +contextual [Φ, e, η, t, ← map_inv, i, hm, hY, V]
  simp [B, t, i, p0]
  rintro ⟨d, ⟨⟨-, hd⟩, h : ¬0 < (B d / _).re⟩, a⟩
  simp [p0, t, i, ↓← fx (b := (1, _)) (show η d = η (closurePart T d) from Matrix.ext fun p q ↦
    (invDifferentIdele E).mul_right_inj.1
    (sub_eq_zero.1 (eq_zero_of_forall_stdAddChar_eq_one fun u ↦ by
    erw [← div_eq_one.2 (congrFun a (Pi.single (p, q) u)), ← map_sub_eq_div]; simp [η, y]
    split <;> ring_nf))), B,
    ← hK _ ⟨componentOn_mem_Kf hd, componentOn_mem_supportedOn⟩ (_ * (_ * (1, _)))] at h
  let A := hyperbolicSplitting E n₁
  have ⟨c', c0, hc⟩ := isAdapted_homSource A V (h :=
    ⟨isOrthoIntegral_hypSpace.2.of_eq_submatrix_mul (id ⊕ᵥ Empty.elim) .one (by
    simp [lAdelic, kAdelic, A, hyperbolicSplitting])⟩).mixedTerm_omega_vacElem
  simpa [-mulVec_smul, ↓sourceTerm_levi, sourceTerm_eq_adapted_mixedTerm, by simpa [V] using hc, η,
    t, hm, e, Φ, V, c0, centreCoeff, invDifferentIdele, star_mulVec, dotProduct_mulVec,
    pairWeil_apply, integrable_const_mul_iff, mul_left_comm _ c',
    adelicHeis, vacElem_apply_eq_prod_lineTheta, Finset.univ_eq_empty, Splitting.thetaTerm,
    Subsingleton.eq_one (G.onHom (1, _)), funext_iff] using!
    A.centreCoeff_eq_integral_stabilizer (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    _ ⟨_, fun h ↦ by simp_rw [enorm_mul, ENNReal.tsum_mul_right]; grw [(exists_tsum_thetaTerm_le
    ..).choose_spec.choose_spec, ← ofReal_norm, ← ENNReal.ofReal_mul' (by simp), mul_right_comm,
    mul_assoc, (hr _).choose_spec]; rfl⟩) ⟨1, by simp [V]⟩ (by
    erw [iΓ, map_comap_eq, inf_comm, ← map_comap_eq]
    simp [↓fy, mat_ratEmbed, V, y, ← (@toAdele E ..).injective.eq_iff]) c hY (x₀ :=
    inclMatrix E (o ∘ .inl)).2.imp_right congr(A.centreCoeff _ $(h (ϱ _ (((A.homSource V).kAdelic *
    (adaptedHomBasis n₁ V).1) *ᵥ (scaleIdele E).1 • star ((1 - idemAdele T.conjClosure) • u))
    (vacElem _)) (by simp +contextual)) (A.levi (scaleIdele E • h₁.toUnitary, 1))).symm.trans
end

-- part: New.Rows.MemberOrthogonality
section
/-! Non-lifts sharing one Hecke root have zero theta periods. A form on a definite U(V) killed by
theta descent, by reflection sums at the level (as good forms are), and by a Hecke polynomial at one
split place at the smallest root of lifts has zero theta periods over U(V₂), where V=V₁⊕V₂ and V₁
has small rank, so the test forms are orthogonal to it. It is known that vanishing of lifts in a
theta tower kills theta periods on a subgroup. Related work: C. Wu, Poles of Eisenstein series and
theta lifts for unitary groups, arXiv 2104.11954, 2021; Ginzburg–Jiang–Soudry, Poles of L-functions
and theta liftings for orthogonal groups, 2009; Jiang–Wu, On (χ,b)-factors of cuspidal automorphic
representations of unitary groups I, 2016; Rallis, On the Howe duality conjecture, 1984.

This file: Forms killed by θ, the reflection sums and one Hecke polynomial have zero
theta periods; comparison forms are orthogonal to them. -/
seal Finset.univ Finset.sum Finset.prod

open AutChar ComplexConjugate Fintype G Gf MatMul Matrix MeasureTheory AuxPair Prod Space Sum
  ThetaKernel

variable {E r n N a l} [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N] [Fintype l]
    [WeilData E] {O : AuxPair E r n} {z} (V : DividedSplitting N l a O z) {l₀} [Nonempty r] (hO :
  O.FitsParams l₀) (hQ : ∀ i, O.ψ (O.twistPlace i) ≠ 1) {Ξ} (hM :
  ∀ (i) (v : (x : O.ChosenIndex) → _), v i ≠ 0 → (O.formAction.asAlgebraHom
  (piTensorElem fun i ↦ reflectionSum (O.ψ _) (v i))) Ξ = 0) (h0 : O.θ Ξ = 0) {w} {hw : _ ≠ w} {hS}
  (hH : O.heckePolyOnForms hw hS (O.testValue w) Ξ = 0) (hn : 2 * card r + 2 * card N + 3 < card n)

include hO hQ hM h0 hH hn

/-- Let O satisfy `FitsParams`, with ψ ≠ 1 on Q, 2r + 2N + 3 < n, and Ξ killed by θ, the
reflection sums and the
Hecke polynomial at `AuxPair.testValue` w. Then each conjugate matrix coefficient of Ξ has theta
lift zero to W ⊕ H^N (character aυ^N) for data that are the vacuum off the level.

Non-lifts sharing one Hecke root have zero theta periods. -/
lemma descentsVanish_hypSum u : DescentsVanish (hypSum N O.W) (stdSpace E n) (O.a *
  WeilData.upsilonU1 ^ card N) O.places.conjClosureᶜ (star (algFormCoeff 1 (gramForm u) Ξ.1)) := by
  have p := pairWeil_integrated O.W (stdSpace E n) O.a O.b
  simp [theta_eq_smul_star_lift_swap, -card_pi] at h0
  refine' descentsVanish_add_planes (descentsVanish_of_reflectionSum _ hQ hM fun P ↦ funext fun g ↦
    highestVector_cyclic (O.isHCParam_paramV · |>.1) O.detExp (.proj g ∘ₗ liftBilin _ _ ∘ₗ ⟨⟨fun u ↦
    ⟨_, (isAutomorphic_star_algFormCoeff (gramForm u) Ξ).mem_rapidFunctions⟩, _⟩, _⟩) u
    (.inr fun x ↦ _)) (removePlanes ..) _ hw _ (by grind [star_star]) (by simp [funext_iff,
    ← algFormCoeff_algFormRep, ↓mem_levelSpace.1 (Ξ.mem_sphericalAt hS)]) _
    ((map_heckePolyOp ((starLinearEquiv ℂ).1 ∘ₛₗ _) _ (by simp [funext_iff,
    algFormCoeff_algFormRep])).symm.trans ((congrArg _ congr(($hH).1)).trans (map_zero _))) hn
  any_goals simp [↓isAutomorphic_star_algFormCoeff, algFormCoeff,
    funext_iff, ↓HasWeight.charUnramifiedAt, testValue, frobValue]
  simpa [algFormCoeff_apply, ← gramForm_conjWeylRep (e := O.detExp) x (highestVector _ _),
    liftBilin, pairWeil_apply, realConv, lift, mul_left_comm _ _⁻¹, mul_assoc] using
    congrFun (((pairThetaKer ..).swap.lift_omega_left (isAutomorphic_star_algFormCoeff _ Ξ)
    (x⁻¹, 1)).symm.trans (congr(lift _ $(p ..) _).trans (((hO.isEdge.2.lift_isForm_and_eq_realConv _
    (by simp [realPairWeil_polyVector, negCount])).choose_spec _ (by simp [p])
    (isForm_ofAlgForm O.isHCParam_paramV Ξ.1).conj).2.trans (congrArg _ h0)))) g

set_option backward.isDefEq.respectTransparency false

/-- Under the hypotheses of `descentsVanish_hypSum`, let C be U(l)(ℝ)-equivariant, x supported at M,
the rows e′ in N, and each k in the open K ≤ K₀ fix Ψ with x⁻¹kx ∈ K₀ fixing Y. Then h ↦ ⟨point form
at (h₁,h)x of C(kernel at h), Ξ⟩ has K-class sum zero.

Non-lifts sharing one Hecke root have zero theta periods. -/
lemma stdClassSum_period_eq_zero (ε : N ⊕ l ≃ n) {κ Y e'} hY (C : _ →ₗ⋆[ℂ] _) (hC : ∀ (g y :
  GInf E 1) ζ, (∀ τ, (g τ).1 = reindexGL ε (blockGL (1, y τ))) → conjWeylRep _ O.detExp g (C ζ) =
  C (conjWeylRep κ 0 y ζ)) {b 𝔪} (h𝔪 : 𝔪.places ⊆ O.places) {Ψ g h₁ x} (hx :
  x ∈ supportedOn n (.range O.chosenPlace)) {K} [ho : IsLevel K] {f} (hf : ∀ h, f h =
  inner ℂ (pointForm (Y := Y) (U.block ε (h₁, h) * x) hY e' (C (kernelVector O b 𝔪 Ψ κ g h))) Ξ) {u}
  (he : ⇑e' = ε ∘ inl ∘ u) (hk : ∀ k, k.1 ∈ K → (∀ T, Ψ ((𝔪.reductionK₀ k⁻¹).1 * T) = Ψ T) ∧ ∃ m,
  ∀ i, (Kf.reduceAt _ ⟨x⁻¹ * U.block ε (1, k) * x, m⟩).1 * Y i = Y i) : stdClassSum K f = 0 := by
  obtain ⟨o, s, t⟩ := (exists_reduceAt_mul_incl_eq hY e').choose_spec
  simp_rw [inner_pointForm] at hf; set A := Exists.choose _
  let D : _ →* G E 1 := blockEmb (e := ε) elim_one_one.symm
  have ⟨y, z⟩ := not_forall.1 (eq_zero_of_realVec (f := pairWeil O.W (stdSpace ..) O.a b⁻¹ (g, 1,
    h₁) (vacElem _)).mt fun e ↦ by simpa using congr(dataInner _ $e $e))
  rw [← θ_ϱ, varrho_pairWeil, ← pairTheta] at z
  set v := (O.W.hom (stdSpace E N)).ϱ _ _
  let φ j := (O.W.hom (stdSpace ..)).boxProd (homSigns_sum_target (e := ε) (by simp)) v (modDatum
    O.W (stdSpace ..) 𝔪 Ψ (polyVector _ (fockLetters O.signs O.ord (-1) (nablaBasis ℂ _ κ j))))
  have hφ j : projOn _ O.places.conjClosureᶜ (φ j) = φ j := by erw [← boxProd_projOn,
    projOn_ϱ _ (by simp [matToVec, vecToMat, realVec, mul_apply, snd_sum]), projOn_vacElem,
    projOn_integrated, projOn_name_vacElem _ (by clear * - h𝔪; grind)]; rfl
  let L j := gramForm (C (Pi.single j 1))
  have Y j := (isAutomorphic_star_algFormCoeff (L j) Ξ).comp_mul_right (1, x * A)
  let F h := ∑ j, pairTheta _ _ O.a 1 (φ j) (g, h) * star (algFormCoeff 1 (L j) Ξ.1) (h * (1,
    x * A))
  obtain ⟨this, o⟩ := (Y · |>.1), mul_mem (supportedOn_mono (by simp) hx) o
  have hΓ γ m h : F (γ * h) =
    F h := congr(∑ j, $((pairThetaKer ..).swap.theta_rat_mul _ m h) * $((Y j).2 _ m h))
  have e y h : F (D (h₁, y, h)) = pairTheta _ _ O.a b⁻¹ v (g, h₁) * conj (f h) := by
    simp (disch := simp [blockEmb]) only [F, φ, pairTheta, D, ← inv_mul_cancel b,
      theta_boxProd_target, mul_assoc, modDatum, pairWeil_boxProd_target (g₁ := (1, h₁)) (g₂ := (y,
      h)) .., ← Finset.mul_sum, ← rep_apply_apply, pairWeil_integrated_right,
      (by simp : (g, y, h) = (g, ↑h) * (1, y, 1)), realPairWeil_fockLetters]
    erw [hf, ← gramForm_conjWeylRep (D (1, y, h)).1⁻¹, hC _ y⁻¹ _ (by tauto),
      pi_eq_sum_univ' (conjWeylRep κ _ _ _), toLin'_apply, ← star_inj]
    simp [algFormCoeff_apply, mul_assoc, weylRep, schur_map, -map_inv]; tauto
  have := (period_eq_zero (by fun_prop) hΓ (fun c m h ↦ sum_congr _ _ fun j ↦ by erw [← mul_one g, ←
    mk_mul_mk, pairTheta_mul, pairWeil_eq_smul_of_projOn_eq _ (hφ j)] <;> simp [↓m,
    upsilonU1_det_of_mem_Kf m.1, mul_assoc h, ← (commute_supportedOn_trivialOn
    o (supportedOn_compl.le m.2)).eq, ← algFormCoeff_algFormRep, Ξ.algFormRep_eq_self_of_mem
    (inf_trivialOn_le_levelOf ⟨m.1, supportedOn_compl.le m.2⟩)]) ε (by simp) (fun ψ hψ ↦ funext
    fun a ↦ .trans (by simp [hypSum, lift, F, theta_boxProd_source, pairTheta, Finset.mul_sum,
    mul_comm O.a, pairWeil_boxProd_source, mul_assoc, -θ_apply]) ((integral_finsetSum _ fun j _ ↦
    integrable_theta_mul _ (Y j).mem_rapidFunctions ..).trans (sum_eq_zero _ fun j ↦
    congrFun ((lift_omega_left _ (isAutomorphic_star_algFormCoeff _ Ξ) (1, x *
    A)⁻¹).symm.trans (descentsVanish_hypSum hO hQ hM h0 hH hn _ _ (projOn_pairWeil
    ((boxProd_projOn ..).symm.trans congr(boxProd homSigns_sum_source $hψ $(hφ j))) _ fun w m ↦
    onHom_atPlace_mem (by simp) ((not_or.1 m).elim (mem_supportedOn.1 (inv_mem o) w) ▸ one_mem _))))
    (.sum (a, g))))) h₁).symm.trans (integral_quotMeasure_eq_classSum (fun γ _ h ↦ .trans (by
    simp [D, ← map_mul]) (hΓ (D (1, γ)) (by simpa [D]) _)) (by simp [e, D]; tauto) K fun k q h ↦ ?_)
  simpa [z, ← mul_classSum, ← map_classSum]
  lift k to Kf E l using ho.1 q; obtain ⟨p, m, a⟩ := hk k q
  have := congr($(O.smul_chosenGLRep_eq Ξ 1 (k := A⁻¹ * ⟨_, m⟩ * A) rfl ?_).1 (U.block ε (h₁,
    h) * x * A))
  simp [← mul_assoc, ← Pi.one_def, ← (U.block ε).map_mul] at this p
  simp +unfoldPartialApp [kernelVector, modKernel_mul_Kf_right, *]
  simp [*, Kf.reduceFamily, ← t, transpose_nonsing_inv, -elim_inl, -elim_inr,
    inv_mul_eq_iff_eq_mul_of_invertible, Matrix.mul_right_inj_of_invertible]; intro
  erw [((MonoidHom.eq_iff _).2 (Kf.reduceAt_eq_one_of_atPlace (w :=
    O.twistPlace _) (by simp [atPlace_twistPlace_eq_one hx]))).trans (map_block_eq_blockGL _ ε
    1 k).2, mul_inclMatrix]; simp [← ext_iff, reindex_equiv ε, inclMatrix, @eq_comm N]

/-- Let O satisfy `FitsParams`, ψ ≠ 1 on Q, 2|r| + 2|N| + 3 < |n|, M² = (ϖ), and Ξ killed by θ,
the reflection
sums and one Hecke polynomial at `AuxPair.testValue`. Then the level-ϖ class sum over h of
⟨`DividedSplitting.productForm`(x, h)(y, conj `kernelVector`(g, h)), Ξ⟩ vanishes. -/
lemma DividedSplitting.stdClassSum_inner_productForm_eq_zero {ϖ} [Fact (ϖ ≠ 0)] (t :
  O.chosenModulusSq.ideal = .span {ϖ}) L x y b Ψ g : stdClassSum (principalLevel l ϖ) (fun h ↦
  inner ℂ (V.productForm L (x, h) y (star (kernelVector O b O.chosenModulusSq Ψ _ g h))) Ξ) = 0 :=
  stdClassSum_period_eq_zero hO hQ hM h0 hH hn V.ε (fun _ ↦ inclMatrix_mulVecLin_injective ..) (𝔪 :=
  O.chosenModulusSq) (cartanProduct V.ε 1 y ∘ₛₗ (starLinearEquiv ℂ).1) (fun g u ζ h ↦ by
    simp [conjWeylRep, weylRep_cartanProduct, V.low, HasColumnsBelow]
    simp [cartanProduct, weylRep, star_mulVec, ← mulVec_transpose, conjTranspose_transpose,
      V.low.2.schur_mul_schur, ← map_inv, by simpa using (U.form_mul_inv_eq <| g ·)]
    congr! 6 <;> simp [h, entrywise, reindex_equiv V.ε]) (by simp [places_levelModulus_false])
  L.mem_supportedOn (by tauto) rfl fun k
  q ↦ have ⟨m, s⟩ := map_block_eq_blockGL O.chosenModulusSq.reduction V.ε 1 k; by
    simp_all [Modulus.mem_principalLevel_iff t,
      Modulus.reductionK₀]; peel L.reduceAt_conj_eq_one _ s; simp [*]
end
