import Lib.Shimura.LiftedIsogenies
import Lib.GaloisRep.MarkedPairs
import Lib.Shimura.ModelAlongArc
import Lib.GaloisRep.Lefschetz

section
/-! Known result: the theta group of an ample line bundle, with the span of sections, K(L) and
symmetric theta structures. Here it is stated for a given system of coordinates with a Heisenberg
law of odd order over a local ring. Spanning of the sections is proved by reduction from the complex
numbers, not by Riemann–Roch, and only the consequences for K(L) and uniqueness are drawn. Source:
D. Mumford, On the equations defining abelian varieties I, Invent. Math. 1 (1966), §§1–2; S. W.
Shin, Abelian varieties and Weil representations, Algebra Number Theory 6 (2012), Prop. 2.12 (over a
base); M. Bolognesi, A. Massarenti, Comment. Math. Helv. 91 (2016), Lemma 4.1 (odd type).

This file: Theta coordinates span the sections on fibres of a modelled abelian scheme. -/

open CategoryTheory AlgebraicGeometry Submodule LineBundle Set Nat IsLocalRing Spec
attribute [local simp] H0_smul ValuativeArc.genericPt_eq
attribute [local simp ←] Over.comp_left map_nsmul

/-- Rigidity of geometric fibres: if an object y over a valuation ring O with fraction field ℂ
is modelled on a complex torus, every pull-back of y along a homomorphism from O to an
algebraically closed field satisfies `ThetaObject.IsRigid`.

Known result: Theta group of an ample line bundle: span of sections, K(L), symmetric theta
structures. -/
lemma ThetaObject.TorusModel.isRigid_pullback {E O W} [Field E] [CMBase E] [CommRing O]
    [ValuativeArc O] [FinComplexSpace W] {D : PEL E} {Z τ} {X : ThetaFamily D Z τ} {y :
  ThetaObject X (Spec ⟨O⟩)} {g ℓ} {Y : PeriodMap D g ℓ W} (a :
  y.TorusModel Y) {k} [Field k] [IsAlgClosed k] (χ : O →+* k) {x₀ : ThetaObject X _}
  (h : specMap χ ≫ y = x₀) : x₀.IsRigid := fun B _ _ _ x ↦ map_surjective.forall.2 fun ϕ g ↦ by
  obtain ⟨h : x.IsPullbackAlong _ y, C, m, hN⟩ := (map_comp_assoc ..).trans (h ▸ g),
    hasConstFunctions_of_isPullback g.isGroupBaseChange.1, (eventually_span_coordSection
    x.groupScheme x₀.isProjEmbedding g.isGroupBaseChange.1).exists_forall_of_atTop
  have ⟨c, P, e⟩ : ∃ c > m, (c : k) ≠ 0 := by by_contra!; simpa [*] using @cast_succ k _ m.succ
  let M {S} (x : ThetaObject X S) := x.lineBundle.pull (c • 𝟙 x.groupScheme).1
  let Λ {R} [CommRing R] x := pullSections (.id R) (by simp) (refl (M x))
  let Q := pullSections _ h.schemeMap.w (by simp [M, h.lineBundle_eq_pull, ← pull_comp _,
    h.isGroupBaseChange.nsmul_id_comp] : M x = .pull (M y) _)
  obtain ⟨hΦ, hR, N⟩ := (isSectionLift_pullSections ..).comp (Θ := Q) (exists_isSectionLift (L :=
    .pow _ _) (𝟙 _) (picClass_pow .. ▸ pull_nsmul_eq_sq_smul y.hasClassLaws.1 c)).choose_spec,
    a.uniformisation.card_torsion P.ne_zero, P.ne_zero
  obtain ⟨⟨_, h'⟩, F, ⟨⟩⟩ := exists_isSectionLift (𝟙 _) (L := M x) hΦ.picClass_eq.symm,
    (equivFinOfCardPos (hR.trans_ne
    (by simp [N]))).symm, by exact_mod_cast x.finite_flat_surjective_smul (cast_ne_zero.2 N)
  let τ {B} [CommRing B] {x} (j : _ →+ _) := ∑ z, pullSections (.id B) (by simp) (by simp [M,
    ← pull_comp _, ← comp_nsmul _, (F z).2] : M x = (M x).pull (translation (j (F z).1)).1)
  refine ⟨C, top_unique fun σ _ ↦ (smul_mem_iff_of_isUnit _ ((e.isUnit.map ϕ.1).pow _)).1
    ((apply_mem_span_image_iff_mem_span (isSectionLift_pullSections ..).injective).1 (Eq.subst (by
    ext; simp [τ, Λ, ← comp_nsmul _, (F _).2, *]; rfl) (mem_comap.1 ((h'.injective.mem_set_image
    (a := Λ x σ)).1 (span_le.2 (range_subset_iff.2 fun j ↦
    (((isSectionLift_pullSections _ h.schemeMap.w rfl).exists_eq_smul C (h'.comp hΦ)).choose_spec
    (coordSection (a.hasThetaCoords.pow _).1 j)).symm.subst (smul_mem _ _ (mem_map_of_mem ((fun θ ↦
    by_contra fun hσ : τ h.isGroupBaseChange.pullSection (Q θ) ∉ span B (Λ x '' _) ↦ ?_) _))))
    ((h.lineBundle_pow_eq_pull _ ▸ g.lineBundle_eq_pull ▸
    hN (c ^ 2) (by nlinarith)) ((a.hasThetaCoords.pow _).1.pull _) ▸ ⟨⟩))))))⟩
  let ω := τ (.id _) θ; let v z := a.uniformisation.expMap ((c : ℂ)⁻¹ • z)
  have hv z : c • v z = a.uniformisation.expMap z := by simp [v, ← cast_smul_eq_nsmul ℂ, N]
  have J z : atGeneric v z ≫ (c • 𝟙 y.groupScheme).1 =
    atGeneric a.uniformisation.expMap z := by simp [atGeneric, ← hv]
  have s := a.hasThetaCoords.pull 1 (J · |>.symm) fun _ ↦ id
  obtain ⟨r, _, _⟩ := by simpa using (s.exists_theta_of_isSection (s.pow 0) (w :=
    (ω.1 ·.1)) (by simpa [IsSection, LineBundle.pow, inf_of_le_left] using! ω.2.1) (fun _ ↦
    (a.uniformisation.immersive _).1.comp (by fun_prop)) fun l _ _ _ ↦
    by simp [ω, τ]; apply Fintype.sum_equiv (F.symm.permCongr (.subtypeEquiv (.addLeft (v l)) _))
    <;> simp_all [v, atGeneric, add_assoc])
  have K (w : span O (range (coordSection a.hasThetaCoords.1))) b (p : ∀ i,
    _ := by simp +contextual [Λ, M, a.hasThetaCoords.4 .., *] <;> simp [atGeneric,
    field, *]) := have H : Λ y w = b • ω := H0_ext fun {i} ↦ ((isSeparatingFamily_atGeneric (s :=
      v) (a.uniformisation.4.comp (MulAction.surjective₀ (by simpa)))).pointFn_ext · · (p i))
    (⟨(residue_eq_zero_iff b).2 fun z ↦ hσ (Eq.subst (a := Q ω) (by ext; simp [Q, ω, τ,
      h.isGroupBaseChange.translation_comp]) (mem_comap.1 ((smul_mem_iff_of_isUnit _ z).1
      (((Λ y).map_span_le ..).2 (by simp [Λ, Q, pullSections_coordSection, mem_span_of_mem,
      ← range_comp', ↓forall_mem_range]) ⟨_, w.2, H⟩)))), H⟩ : _ ∧ _)
  obtain ⟨γ, _, n, p, G⟩ := exists_sections_of_translation_stable _ a.hasThetaCoords
    y.obj_isThetaStructure.4 a.exists_isTranslationLift_of_dualLattice (by bound)
    (by tauto) () (by simpa [·] using K 0 1)
  obtain ⟨g, e⟩ | ⟨g, e⟩ := ValuationRing.isInteger_or_isInteger O γ
  exact (K (n 0) g).elim fun k e ↦ G _ (_ ≫ (y.levelPoints 0).1) fun z _ _ i ↦ by
    simpa [Λ, hv, k] using congr($e.1 i _ (specMap (residue O) ≫ (v z).1))
  simpa using K (g • n 0) 1
end

section
/-! Part of: Complex uniformisation of PEL abelian varieties; Appell–Humbert; finite class number
(known result; see Lib.Shimura.Uniformisation.AppellHumbert).

This file: Ball model for signature (1,n-1): periods, polarisation, linearised action at fixed
points. -/

noncomputable section

open Topology Matrix Polynomial ComplexOrder Complex LinearMap Real Fintype Finset


variable (E) {n} [Field E] [Ψ : CMBase E] [Fintype.{0} n] {D : PEL E} (e : (n → ℂ)
    ≃L[ℂ] ℂ × BallBase n) (H : Matrix n n ℂ)
attribute [local simp] map_smul' mulVec_sub ModuliPoint.act polarisationForm mul_sum
  vecMulVec_mulVec roots_eq_map_numberedRoots smul_smul
  PeriodMap.intAction PEL.xi_im_pos_and_re_eq_zero Prod.ext_iff toBilin'_apply' mulVec_transpose
attribute [local simp ←] Complex.coe_smul dotProduct_mulVec mulVec_mulVec
attribute [-simp] Prod.forall map_smul map_smul_of_tower map_sum Pi.star_apply Prod.smul_mk

/-- The map, ℂ-linear in q = (q₁,q') and ℝ-linear in w, with value ((e⁻¹q)ᵀHw₀, q₁y₂ − y₁q',
(q₁w_v)_{v≠v₀}), where w₀ = w_{v₀} and (y₁,y₂) = e(w̄₀). -/
@[simp] def ballPeriod : ℂ × BallBase n →ₗ[ℂ] RealVectors E n →ₗ[ℝ] BallFibre E
  n := by apply mk₂' ℂ ℝ fun q w ↦
  ((e.symm q ⬝ᵥ H *ᵥ (w · v₀)) • (1, 0) + q.1 • e (star (w · v₀)) - (e (star (w · v₀))).1 • q,
  fun v ↦ q.1 • (w · v)) <;> intros <;> ext <;>
  simp [-smul_eq_mul, ← Pi.add_def, ← Pi.smul_def] <;> ring

/-- The set of b in ℂ^(n−1) such that x = e⁻¹(1, b) in ℂⁿ is positive for H, that is, Re ∑ x_i
H_ij conj(x_j) > 0. -/
abbrev positiveBall := {b | 0 < (e.symm (1, b) ⬝ᵥ H *ᵥ star (e.symm (1, b))).re}

/-- The matrix of w ↦ 2(uᴴHw)/(uᴴHu)·u − w; if uᴴHu ≠ 0 it fixes u and is −1 on the w with uᴴHw
= 0. -/
abbrev formReflection u := vecMulVec u ((2 / star u ⬝ᵥ H *ᵥ u) • star u ᵥ* H) - 1

variable {E H}

lemma exists_eq_formReflection (hH : H.IsHermitian) {J} (p : (H * J).PosDef) : IsReflection J →
  ∃ u, 0 < star u ⬝ᵥ H *ᵥ u ∧ J = formReflection H u | ⟨u, _, _⟩ => ⟨u, by
              obtain _ := p.dotProduct_mulVec_pos (by aesop : u ≠ 0), star_form p.1
              simp_all [star_form hH, ext_iff_mulVec]
              grind⟩

/-- Assume `IsSignedFrameFor` g ℓ β, H = Φ_{v₀}(β) negative definite on {e(ȳ)₁ = 0}, and
`positiveBall` connected. Then an analytic family over this ball has frame g and, at b,
reflection in conj(e⁻¹(1,b)) and period map `ballPeriod` at (1,b). -/
lemma exists_analyticFamily_positiveBall e {H} (hS : IsConnected (positiveBall e H)) (hn : ∀ y ≠ 0,
  (e (star y)).1 = 0 → star y ⬝ᵥ H
  *ᵥ y < 0) {ℓ g β} (hβ : IsSignedFrameFor g ℓ β) (hH : β.map (Φ v₀) = H) : ∃ f : AnalyticFamily D,
  f.U.1 = positiveBall e H ∧ f.frame = g ∧ ∀ b ∈ f.U, f.reflection b =
  formReflection H (star (e.symm (1, b))) ∧ ⇑(f.torus b).Q = ⇑(ballPeriod E e H (1, b)) := by
  let f v := by apply mk₂' ℝ ℂ fun (w : RealVectors E D.Index) (p : BallFibre E D.Index) ↦ 2 * π *
    (Φ v D.ξ).im * if h : v = v₀ then (e (star (w · v))).1 * p.1.1 - e.symm (p.1 - p.1.1 •
    (1, 0)) ⬝ᵥ H *ᵥ (w · v) else star (w · v) ⬝ᵥ β.map (Φ v) *ᵥ p.2 ⟨v,
    h⟩ <;> as_aux_lemma => intros; split <;> simp [-smul_eq_mul, ← Pi.add_def,
      ← Pi.smul_def] <;> ring
  have U : IsOpen (positiveBall e H) := by apply isOpen_lt <;> fun_prop
  choose r hr _ using
    (hS.1.elim (by grind) : ∀ b, ∃ c ∈ positiveBall e H, b ∈ positiveBall e H → c = b)
  have z b := ne_zero_of_re_pos (hr b)
  let P b := ballPeriod E e H (1, r b)
  have l b w v (hv : (w · v) ≠ 0) : 0 < (f v w (P b w)).re := by
    by_cases v = v₀ <;> simp [*, f, P, pi_pos]
    set s := (e _).1
    linarith [by simpa [normSq, ← star_form (hH ▸ hβ.1.isHermitian_map) (star _)] using (by_cases
      (fun _ ↦ by simp_all) (hn ((w · v₀) - star (s • e.symm (1, r b))) · (by simp [s])
      |>.1.trans_le (mul_nonneg s.normSq_nonneg (hr b).le)))]
    simpa [*] using (hβ.2 v).re_dotProduct_pos hv
  have pos b w hw := sum_pos (Pi.lt_def.2 ⟨(by_cases (by simp [f, ·]) <|
    le_of_lt ∘ l b w ·), (Function.ne_iff.1 (mt transpose_eq_zero.1 hw)).imp (l b w)⟩)
  let Q b := ((P b).linearEquivOfInjective (.of_ker _ fun w ↦ (by simpa [·] using! pos b w))
    (by zify; simp [Fin.pos']; ring)).toContinuousLinearEquiv
  have hP b : IsPeriodMap (formReflection H (star (e.symm (1, r b)))) (Q b) := by
    simp_all [Q, P, IsPeriodMap, funext_iff, -smul_eq_mul, ← Pi.sub_def, ← Pi.smul_def]
    grind [smul_eq_mul]
  have d {w} b hb := (((ballPeriod E e H).flip w).toContinuousLinearMap.hasFDerivAt.comp _
    (hasFDerivAt_prodMk_right 1 b)).congr_of_eventuallyEq (f₁ := (Q · w))
    (.mono (U.mem_nhds hb) (by simp_all [P, Q]))
  refine suffices ∀ b, _ from ⟨⟨⟨_, U⟩, hS, g, _, fun b ↦ ⟨⟨β, _, (restrictScalars ℝ
    toContinuousLinearMap.1 ∘ₗ ∑ v, f v).toContinuousLinearMap ∘L (Q b).symm, hβ.1, hP _, ?_, ?_,
    isPosRiemann_of_re_pos (this b)⟩, ⟨_, _, by simp [z], rfl⟩, fun c ↦ ?_, .refl .., by
      simp [LinearMap.ext_iff, reindex_equiv (Q b)]; simp [Q, P, -smul_eq_mul, ← Pi.smul_def]
      simp [funext_iff, field]⟩, fun _ h _ ↦
      analyticAt_of_eventually_differentiable (.mono (U.mem_nhds h) (⟨_, d · ·⟩)), fun b hb v p ↦ by
    simpa [z, ← hP .., (d _ hb).fderiv, two_smul, self_eq_neg, -smul_eq_mul, ← Pi.smul_def] using
    congr($(p (Q b fun i _ ↦ star (e.symm (1, r b)) i)).1.2), by simp, this⟩, rfl, rfl, by
      simp +contextual [*, Q, P, funext_iff]⟩; (Q · |> reindex_equiv |>.1.2
      (by simpa using! pos _)) <;> simp [riemannForm_def, div_eq_iff, reindex_equiv (Q
    b)] <;> as_aux_lemma => intro y; simp [f, Q, P, ← hH, sum_mul, ← sum_sub_distrib, -smul_eq_mul,
    ← Pi.smul_def, ← star_form hβ.1.isHermitian_map (y · _)]; congr! 1; split <;> simp [*,
    mul_sub] <;> ring

/-- If H is hermitian and a = ūᵀHu > 0, there are linear coordinates e : ℂⁿ ≅ ℂ × ℂ^(n−1) with
a·e(y)₁ = yᵀHu and e(ū) = (1, 0), and the b for which x = e⁻¹(1, b) has Re xᵀHx̄ > 0 form a
set star-convex at 0. -/
lemma exists_ball_chart (hH : H.IsHermitian) {u a} (ha : star u ⬝ᵥ H *ᵥ u = a) (hu : 0 < a) : ∃ e,
  StarConvex ℝ 0 (positiveBall e H) ∧ (∀ y, a * (e y).1 = y ⬝ᵥ H *ᵥ u) ∧ e.symm (1, 0) =
  star u := by
  let j := ContinuousLinearEquiv.equivOfRightInverse (a⁻¹ • H.toBilin'.flip u
    ).toContinuousLinearMap (.toSpanSingleton ℂ (star u)) fun c ↦ by simp [*, hu.ne']
  refine .imp (fun e h ↦ ⟨fun b hb s t _ _ _ ↦ ?_, h⟩) ⟨j.trans (.prodCongr (.refl ..) (.ofFinrankEq
    (by simpa -dsimp using congr($j.finrank_eq.symm - 1)))), by simp -dsimp [j, hu.ne']⟩
  simpa [(e.injective (by simp [← h]) : e.symm (1, ofReal t • b) = star u + t • (e.symm (1, b) -
    star u)), ← h.1 (e.symm _), *, ← star_form hH (star _), field]
    using (convex_Ioi 0).add_smul_sub_mem hu.1 hb ⟨sq_nonneg t, by bound⟩

/-- An endomorphism Y of K × K^m that preserves both factors and acts by ν on the first is ν ⊕
N, and the characteristic roots of N are those of Y with one copy of ν removed. -/
lemma exists_roots_eq_erase {K} [Field K] ν (Y : Module.End K _) (h₀ : Y (1, 0) = (ν, 0)) (h : ∀ w,
    (Y (0, w)).1 = 0) : ∃ N : Matrix n n K, (∀ x, Y x = (ν * x.1, N *ᵥ x.2)) ∧ N.charpoly.roots =
    Y.charpoly.roots.erase ν := .imp (fun N (e : Y = .prodMap (0 - -ν • 1) N.toLin') ↦ e ▸ by
  simp [↓charpoly_prodMap, roots_mul, X_add_C_ne_zero, N.charpoly_monic.ne_zero, ↓charpoly_sub_smul,
    -map_neg]) ⟨(snd .. ∘ₗ Y ∘ₗ inr ..).toMatrix', by ext <;> simp [*, Prod.mk_zero_zero]⟩

/-- For an analytic family f and p = (b, z), the point with the frame of f, the reflection ℓ(b),
and vectors Q_b⁻¹(z_i) + P_i, Q_b the period map. -/
@[simp] def AnalyticFamily.ballPoint {ν} (f : AnalyticFamily D) (P : Fin ν → _) (p : _ × _) :=
  ModuliPoint.mk _ _ ((f.torus p.1).Q.symm ∘ p.2 + P) ⟨_,
  (f.torus p.1).isSignedFrameFor⟩ (f.torus _).reflection

/-- The Hecke translate of an analytic family by γ: frame gγ, same domain, complex structures
and period maps, forms B scaled by the c > 0 with c·γᴴγ in Ẑ^×. -/
def AnalyticFamily.heckeTranslate (f : AnalyticFamily D) (γ : GUPlus E D.Index) :
  AnalyticFamily D := by
  choose c h k using γ.2.1
  exact ⟨_, f.isConnected, f.frame * γ, _, fun b ↦ let x := f.torus b
    ⟨⟨_, _, c • x.B, x.isFrameFor.mul_iff.2 k,
      x.isPeriodMap, by simp [x.re_symm], by simp [map_rat_smul, x.riemannForm_eq, Rat.smul_def,
      mul_left_comm], isPosRiemann_of_re_pos (by simpa [h] using f.re_pos b)⟩,
      x.reflection, by simpa [h.ne'] using x.adjoint, x.exists_std_equiv⟩, f.analyticAt,
    f.eq_zero_of_linear, by simp [f.form_const 0], by simpa [h] using f.re_pos⟩

/-- Some analytic family, parametrising points A(q) with A(0) = o, meets every point with frame o.x.
If z : o·(g,α) ≅ o at level K(𝔑), z separable, o.reflection = `eigenReflection` True z μ, then z :
A(q)·(g,α) ≅ A(Kq) near 0, K linear, `localTerm`(t) = `localTerm`(0)·det(1 − tK). -/
lemma exists_ball_family {ν} (o : ModuliPoint E D.Index ν) : ∃ f : AnalyticFamily D, 0 ∈ f.U ∧
  f.ballPoint o.P 0 = o ∧ (∀ a : ModuliPoint E D.Index ν, a.x = o.x → ∃ p ∈ f.U.1 ×ˢ .univ,
  f.ballPoint 0 p = a) ∧ ∀ {g α z μ}, z.1.charpoly.Separable → o.reflection = eigenReflection True z
  μ → (o.act g α).IsLevelIso (levelGU D.Index D.𝔑) z o → ∃ K : Module.End ℂ _, (∀ᶠ q in 𝓝 0,
  ((f.ballPoint o.P q).act g α).IsLevelIso (levelGU D.Index D.𝔑) z (f.ballPoint o.P (K q))) ∧ ∀ t,
  (localTerm α z.1.charpoly μ).eval t = (localTerm α z.1.charpoly μ).eval 0 * (1 - t • K).det := by
  have ⟨_, _, _, ⟨β, S⟩, r₀⟩ := o
  obtain ⟨T, hH⟩ := ite_eq_left rfl ▸ S.2 _, S.1.isHermitian_map
  obtain ⟨u₀, hu₀, rfl⟩ := exists_eq_formReflection hH T r₀
  have ⟨e, hS, he, he₀⟩ := exists_ball_chart hH rfl hu₀
  have hn y hy (h : (e (star y)).1 = 0) := by
    simpa [← he (star y), h] using T.dotProduct_mulVec_pos (x := y) hy
  obtain ⟨f, hU, rfl, hf⟩ := exists_analyticFamily_positiveBall e (hS.isPathConnected
    (by simpa [*] using hu₀.1)).isConnected hn S rfl
  have h0 := (hU ▸ hS).mem f.isConnected.1
  refine ⟨f, h0, by simp [hf _ h0, *], ?_, fun {k α z j} hz hμ R ↦ ?_⟩
  rintro ⟨_, _, P, ⟨_, s⟩, h⟩ ⟨⟩
  cases by simpa using s.conj_eq_smul S (y := 1) ⟨one_pos, 1, by simp⟩
  obtain ⟨u, hu, rfl⟩ := exists_eq_formReflection hH (ite_eq_left rfl ▸ s.2 _ :) h
  have k := mt (hn u (by aesop)) hu.not_gt
  have ⟨b, hb⟩ : ∃ b, (1, b) = (e (star u)).1⁻¹ • e (star u) := by simp [k]
  have m : b ∈ f.U := hU.ge (by simpa [*, inv_mul_eq_div, div_div, mul_conj] using hu.1)
  exact ⟨(b, (f.torus b).Q ∘ P), by
    simp [(hf b m).1, m, hb, formReflection, ext_iff_mulVec, funext_iff]; simp [field, *]⟩
  obtain ⟨⟨c, h₀⟩, _, a, u⟩ := div_mem k.2.1 R.mem_level.1,
    (isReflection_eigenReflection hz).2 _ r₀ R.2
  obtain ⟨⟨⟩, hc, h₂⟩ := (u _).1 hμ,
    S.similitude_and_root_norm (by simpa [← mul_assoc] using h₀) R.reflection_eq
  set μ := numberedRoots (Ψ.Φ v₀) _ j
  have hr := h₂ v₀ μ (by aesop)
  obtain ⟨hμ, h₀⟩ := by simpa [hu₀.ne', smul_comm μ, -vecMulVec_smul] using congr($a *ᵥ u₀),
    mul_ne_zero_iff.1 (hr.trans_ne (by aesop))
  have hZ x w := by simpa [↓map_conjTranspose_mul_mul,
    dotProduct_mulVec _ _ᴴ, -dotProduct_mulVec] using congr(x ⬝ᵥ ($hc).map (Φ v₀) *ᵥ w)
  have ⟨N, hY, hN⟩ := exists_roots_eq_erase (star μ) (e.conj (z.1.map (Φ v₀))ᴴᵀ.toLin')
    (by simp [*, ← star_mulVec, ← e.symm_apply_eq.1 he₀]) fun w ↦ by
    simpa [hμ, ← he (_ ᵥ* _), ← he (e.symm _), hu₀.ne', h₀] using hZ (e.symm (0, w)) u₀
  erw [e.charpoly_conj, charpoly_toLin', z.1.charpoly_map (star _)] at hN
  let G a := ((mulLeft ℂ (Ψ.Φ v₀ a * μ)).prodMap (star (Φ v₀ a) • N).toLin').prodMap
    (piMap fun v : {a // a ≠ Ψ.v₀} ↦ (Φ v a • z.1.map (Φ v)).toLin')
  let K := (star μ⁻¹ • N).toLin'.prodMap (piMap (G <| α ·))
  refine ⟨K, .mono (((f.U.2.prod f.U.2).preimage (f := fun p ↦ ((K p).1, p.1))
    (by fun_prop)).mem_nhds (by simpa)) fun p ⟨h', h⟩ ↦
    have key a w : (f.torus (K p).1).Q (cmEmbedding a • z.1.map cmEmbedding *ᵥ w) =
      G a ((f.torus p.1).Q w) := by
      simp [hf _ h, hf _ h', -smul_eq_mul, ← Pi.smul_def]
      simpa [G, K, star_mulVec, by simpa [reindex_equiv e, ← e.eq_symm_apply] using hY, funext_iff,
        *, ← hr, field] using Or.inl (hZ (star μ⁻¹ • e.symm (1, p.1)) _)
    ⟨R.mem_level,
      (f.torus _).isPeriodMap.ratConj_eq (f.torus _).isPeriodMap (G 1) (by simp [← key]), by
      simpa [K, (f.torus _).Q.eq_symm_apply.2 (key ..)] using R.sub_mem_lattice⟩, fun t ↦ ?_⟩
  have hn r : _ → μ * t - r = -r * (1 - (star μ)⁻¹ * star r * t) := (by grind) ∘ h₂ v₀ r
  simp [lieRoots, (id rfl : 1 - t • K = .prodMap (1 - t • toLin' _) (piMap fun i ↦
    .prodMap (.prodMap (1 - t • mulLeft ..) (1 - t • toLin' _)) (piMap fun v ↦ 1 - t • toLin' _))),
    ← det_toMatrix', map_smul, prod_eq_mul_prod_subtype_ne _ v₀, IsLieRoot, sub_ite, μ,
    ← star_def, *, localTerm, ← map_val, ← map_erase, ← Multiset.map_erase _
    star_injective, ← erase_val, prod_ite, filter_eq', filter_ne', det_pi, piMap, @Subtype.prop _ (·
    ≠ _), -mul_eq_mul_left_iff, charpoly_map, det_prodMap, det_one_sub_smul_eq_prod_roots,
    ↓roots_map_conjugate, mul_comm t, eval_prod, ↓prod_embeddings_eq_prod_pairs,
    mul_assoc, -neg_mul, Lagrange.basis, Lagrange.basisDivisor]
  ring
end
end

section
/-! Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation
(known result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Eichler–Shimura congruence relation for GU(1,n−1) at a split place: the pointwise step
(known result; see Lib.Shimura.CongruenceRelation.CongruenceStep).

This file: Deep principal levels for finitely many isogenies; finite torsion index sets. Hecke
isogenies at a split place: multiplier, action on level points, kernel in w-torsion. Kuga–Sato fibre
powers, their complex points up to isomorphism, and level covers as closures. -/

noncomputable section

open NumberField Subgroup Submodule nonZeroDivisors
variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {𝔑 : 𝓞 E} (𝔪 : (𝓞 E)⁰)

@[simp] lemma levelGU_inf_one : levelGU n 𝔑 ⊓ levelGU n 1 = levelGU n 𝔑 := inf_of_le_left fun _ h ↦
  mem_levelGU_of_local h.1 h.2.1 (·.2.one_notMem.elim)

/-- For 𝔑 ≠ 0 and a finite set s of pairs (𝔪, g), there is a level m with g⁻¹K(m)g ⊂ K(𝔑) ∩ K(𝔪)
for all (𝔪, g) in s and for (1, 1) and (m, 1). -/
lemma exists_level_conj_mem (h : 𝔑 ≠ 0) (s : Finset ((𝓞 E)⁰ × GUPlus E n)) : ∃ m,
  ∀ x ∈ insert (m, 1) (insert 1 s), ∀ k ∈ levelGU n m.1, x.2.1⁻¹ * k * x.2 ∈ levelGU n 𝔑 ⊓ levelGU n
  x.1 := have ⟨M, _, H⟩ := (exists_congruenceGL_subset ((insert 1 s).eventually_all.2 fun x _ ↦
    (by fun_prop : ContinuousAt (x.2.1⁻¹ * · * x.2) 1) (((isOpen_congruenceGL_span h).inter
    (isOpen_congruenceGL_span (coe_ne_zero x.1))).mem_nhds (by simp))))
  ⟨⟨M, by simpa⟩, by
    simp_all [levelGU]; rintro _ _ _ ⟨a, b⟩ s k c d
    simp [mul_mem, inv_mem, *, (H k d).2 _ _ _ _ s]⟩

/-- For a non-zero element 𝔪 of O_E, the set of non-zero elements of (𝔸_f / Ô)ⁿ ≅ (E / O_E)ⁿ
killed by 𝔪. -/
abbrev NonzeroTorsion n := {s : torsionBy _ (AdelicTorsion E n) 𝔪.1 // s ≠ 0}

instance finite_torsionBy :
  Finite (torsionBy _ (AdelicTorsion E n) 𝔪.1) := Nat.finite_of_card_ne_zero
  (by rw [← torsionBySet_span_singleton_eq, card_torsionBySet_adelicTorsion] <;> simp)

instance : ((levelGU n 𝔪).subgroupOf (levelGU n 𝔑)).FiniteIndex := ⟨relIndex_inf_ne_zero (by
  simp [relIndex_eq_one.2, levelGU]) ((isCompact_intGL isCompact_Ô).relIndex_ne_zero
  (isOpen_congruenceGL_span (by simp)) ∘ relIndex_eq_zero_of_le_right fun _ ↦ (·.2.1))⟩

open Matrix IsDedekindDomain HeightOneSpectrum Nat Set QuadField GeneralLinearGroup

attribute [-simp] coe_units_inv MonoidHom.coe_comp

section

variable {E n : Type} [Field E] [NumberField E] [Fintype n]

/-- The `w`-torsion of `(𝔸_f / Ô)ⁿ` is a copy of `(𝓞 / w)ⁿ`, and an integral matrix kills a
torsion point exactly when its reduction modulo `w` kills the corresponding vector. -/
lemma exists_residue_torsion_emb w : ∃ ρ : _ →ₗ[𝓞 E] _, (⇑ρ).Injective ∧ ρ.range = .torsionBySet _ _
  w.1 ∧ ∀ x, ∃ v, ρ x = torsionClass v ∧ ∀ g : Matrix n n (Ô E), torsionClass (g.map (·.1) *ᵥ
  v) = 0 ↔ x ∈ residueKer (g.map (·.1 w)) := have L (x : n → Ô E) : torsionClass (singleAdele w
    (uniformizer w).1⁻¹ • (·.1) ∘ x) = 0 ↔ reduceAt w ∘ x = 0 := by simp_all [funext_iff, mem_Ô,
    ← and_forall_ne w, ← v_uniformizer_inv_mul_le_one_iff]
  let p := (Algebra.linearMap (𝓞 E) (ResField w)).compLeft n
  have hk : (torsionClass ∘ₗ ((_ : 𝔸f E) • (Algebra.linearMap ..).compLeft n)).ker = p.ker :=
    Submodule.ext (L <| algebraMap .. ∘ ·)
  have hp : (⇑p).Surjective := (algebraMap_ResField_surjective w).comp_left
  let ρ := liftQ _ _ hk.ge ∘ₗ (p.quotKerEquivOfSurjective hp).symm.1
  have I := ρ.ker_eq_bot.1 (by simp [ρ, LinearMap.ker_comp, ker_liftQ, *])
  by use ρ, I, SetLike.ext' (Finite.eq_of_subset_of_card_le (finite_of_card_ne_zero ?_)
    (by simp_all [subset_def, ← map_smul, funext_iff, Algebra.smul_def])
    (card_range_of_injective I ▸ ?_)), hp.forall.2 fun c ↦ ⟨_, by aesop, fun g ↦ by
    simpa [residueOrZero, funext_iff, mulVec_apply_eq_sum, mem_Ô.1] using! L (g *ᵥ algebraMap .. ∘
      c)⟩ <;> erw [card_torsionBySet_adelicTorsion w.3] <;> simp [card_pi, card_ResField]

end

variable {E n : Type} [Field E] [CMBase E] [Fintype n] {D : PEL E} {d₀ : ℕ} [HasQuadSubfield d₀ E]
  {v : n → 𝔸f E} {w : SplitFinPlace E} {C : Submodule (ResField w.1) (n → ResField w.1)}

omit [Fintype n] in
lemma smul_torsionClass_eq_zero_iff {a} : a • torsionClass v = 0 ↔ ∀ i u,
  u.intValuation a * Valued.v (v i u) ≤ 1 :=
  torsionClass_eq_zero.trans (by simp [mem_Ô, ← v_algebraMap_eq_intValuation, ← map_mul]; rfl)

lemma heckeIsogeny_inv_at_eq_basicCosetRep {I} (hw : IsSafe I w.1) : (heckeIsogeny w C)⁻¹.1.map
  (evalAt _) = (basicCosetRep C).1 := by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hw.1.star_ne_and_prime_norm.1.symm, invTransposeGL, transposeGL]

lemma heckeIsogeny_inv_mulVec_of_ne {u} (hu : u ≠ w.1) (hu' :
  u.below _ ≠ star (w.1.below (QuadField d₀))) i : ((heckeIsogeny w C)⁻¹.1
  *ᵥ v) i u = v i u := ((evalAt u).map_mulVec ..).trans (by simp [↓← val_map_apply, heckeIsogeny,
  evalAt_centralScalar_of_ne hu', evalAt_conjAtSplit_of_ne _ hu (by grind [below_star, star_star])])

lemma isScalarFrame_heckeIsogeny : IsScalarFrame (heckeIsogeny w C)
  (w.1.q ^ Module.finrank (ResField w.1) C : ℕ) := ((centralScalar_mem_GU _).2 _ (by simp
  [finIdeleAbs_adeleNorm, norm_locField_eq_q_zpow])).imp_right
  (congr(IsFrameFor $(one_smul ..) _).mp <| ·.mul_iff.2 ⟨1, by simp⟩)

lemma heckeIsogeny_torsionClass C v (hβ : D.β = algebraMap _ _ (c₀ d₀)) (hw :
  IsSafe D.𝔑 w) {b : ℤ} (co : IsCoprime (D.β - b) (star D.β - b)) (hb : D.β - b ∈
  w.1.1) : let s := torsionClass ((heckeIsogeny w C)⁻¹.1 *ᵥ v); (torsionClass v ∈ D.levelTorsion →
    s = torsionClass v) ∧ ∀ N, (D.β - b) ^ N • torsionClass v = 0 → s = 0 →
    torsionClass v ∈ torsionBySet (𝓞 E) _ w.1.1 := by
  simp [PEL.levelTorsion, smul_torsionClass_eq_zero_iff, mem_Ô, torsionClass_eq_iff]
  use fun hv i u ↦ if e : D.𝔑 ∈ u.1 then by simp [heckeIsogeny_inv_mulVec_of_ne (by grind [IsSafe])
    (hw.2.2 u · e)] else have H i := by simpa [intValuation_eq_one_iff.2 e] using! hv i u
    ((LocInt u).1.comap (evalAt u)).sub_mem (sum_mem fun a _ ↦
      mul_mem (mem_Ô.1 ((heckeIsogeny_mem_GUPlus ..).2 i a)
    u) (H a)) (H i), fun N hv h a ha i u ↦ if hu : u = w then hu ▸ mul_le_mul'
    ((intValuation_le_pow_iff_mem _ _ 1).2 (by simpa)) ((congrArg _ (by simp [RingHom.map_mulVec,
    heckeIsogeny_inv_at_eq_basicCosetRep hw] : _ = (_ *ᵥ fun _ ↦ evalAt _ _) i)).trans_le
    (v_matrix_mul_le (basicCosetRep_spec C).1.2.1 (fun _ ↦ h · w) i i)) else mul_le_one'
    (intValuation_le_one ..) (if e : D.β - b ∈ _ then heckeIsogeny_inv_mulVec_of_ne hu (fun h ↦
    w.1.2.notMem_of_isCoprime_of_mem co hb (cast (by simpa [hβ, ↓D.star_beta] using! congr(c₀ _ -
    b ∈ ($h).1)) e)) i ▸ h .. else by simpa [intValuation_eq_one_iff.2 e] using hv i u)

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory ThetaFamily
  ThetaObject Obj Over Fintype TorusModel ValuativeArc ModuliPoint Fint Function
variable {E : Type} [Field E] [CMBase E] (D : PEL E)
  (R : Subalgebra (𝓞 E) E) {κ} {ν : ℕ} [Finite κ] {T : AlgebraicGeometry.Scheme}
  {Z : AlgebraicGeometry.Scheme}
  {τ : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {O : Type} [CommRing O] [ValuativeArc O]

/-- A universal family for D over a Dedekind ring R ⊂ E: projective smooth base of relative
dimension |n| − 1, with complex objects modelling all analytic families holomorphically,
dense in the base. -/
structure UniversalFamily where
  isDedekindDomain : IsDedekindDomain R
  base : Over (Spec ⟨R⟩)
  family : ThetaFamily D _ (base.hom ≫ specMap (algebraMap ..))
  hasProjEmbedding : HasProjEmbedding base.hom
  smooth : SmoothOfRelativeDimension (card D.Index - 1) base.hom
  obj : AnalyticFamily D × _ → (specOver R ℂ ⟶ base)
  model a : TorusModel (X := family) (obj a).left (a.1.torus a.2).toPeriodMap
  holomorphic f : ∀ b ∈ f.U, ∀ z, HolomorphicAt (fun q ↦
    atGeneric (model (f, q.1)).uniformisation.expMap q.2 ≫ (toFamily (obj _).left).left) (b, z)
  dense : IsDenseFamily (obj · |>.left)

attribute [instance] UniversalFamily.hasProjEmbedding

variable {D R} {U : UniversalFamily D R} (𝔪 : (𝓞 E)⁰) (y : ThetaObject X T) (Q : κ →
  (𝟙_ _ ⟶ y.groupScheme))

instance {S : Scheme} {F : Discrete κ ⥤ Over S} : HasLimit F := inferInstance

/-- For a family X and a finite index type κ, the fibre power over the base of X of κ copies of
its abelian scheme. -/
abbrev ThetaFamily.fibrePower κ [Finite.{1} κ] := ∏ᶜ fun _ : κ ↦ X.A

/-- The i-th projection from the fibre power `ThetaFamily.fibrePower` of the family X to its abelian
scheme, as a morphism of the underlying schemes. -/
abbrev ThetaFamily.proj i := (Pi.π _ i : X.fibrePower κ ⟶ _).left

/-- The T-point of the fibre power `ThetaFamily.fibrePower` lying over the object y whose i-th
component is the section Q_i of the abelian scheme of y. -/
def ThetaObject.pointOf : T ⟶ (X.fibrePower κ).left :=
  (Pi.lift (y.isGroupBaseChange.pointEquiv <| Q ·)).left

variable {y Q} (a : ModuliPoint E D.Index ν) (t :
  Spec ⟨O⟩ ⟶ (X.fibrePower (NonzeroTorsion 𝔪 D.Index ⊕ Fin ν)).left)

/-- t is `ThetaObject.pointOf` of an object modelled on the frame and line of a, with sections the
images of the non-zero 𝔪-torsion classes and of the P_i under the model. -/
@[mk_iff] inductive ThetaFamily.IsPointOf : Prop | mk {x V} [FinComplexSpace V] {Y :
  PeriodMap D a.x a.reflection V} (m : TorusModel x Y)
  (h : t = x.pointOf ((m.fullStructure.torsionPoint ·.1) ⊕ᵥ (m.π <| a.P ·)))

@[reassoc (attr := simp)] lemma ThetaObject.pointOf_hom : y.pointOf Q ≫ hom _ =
  y := by simp [pointOf]

@[reassoc (attr := simp)] lemma ThetaObject.pointOf_proj i : y.pointOf Q ≫ proj i =
  (Q i).left ≫ y.toFamily.left := congrArg Hom.left (Pi.lift_comp_π ..)

/-- For a = (x, ℓ, P), a chosen complex point over R of the fibre power of the family: an object
modelled on (x, ℓ), with its non-zero 𝔪-torsion points and the points P. -/
def UniversalFamily.datumPoint := ((exists_ball_family a).elim fun f h ↦ h.2.1 ▸ ⟨homMk _, U.model
  (f, 0), rfl⟩ : ∃ t : specOver R ℂ ⟶ (Over.map U.base.hom) _, U.family.IsPointOf 𝔪 a t.1).choose

lemma fibrePower_ext_iff {t t' : T ⟶ _} : t = t' ↔ t ≫ (X.fibrePower κ).hom = t' ≫ hom _ ∧ ∀ i, t ≫
  proj i = t' ≫ proj i := ⟨by lia, (congr($(show homMk (U := .mk _) t ·.1 = homMk t' by aesop).1))⟩

variable {𝔪} {a} {b : ModuliPoint E D.Index ν} {t} {J : Type} [Finite J]
  (γ : J → (𝓞 E)⁰ × GUPlus E D.Index) {s u : Spec ⟨ℂ⟩ ⟶ _}

attribute [local simp] act isLevelIso_iff fibrePower_ext_iff

/-- If the generic point of an O-point t of the fibre power, O an arc, is attached to a with its
𝔪-torsion (`ThetaFamily.IsPointOf`), then so is t. -/
lemma ThetaFamily.IsPointOf.of_generic (k : IsPointOf 𝔪 a (genericPt ≫ t)) : IsPointOf 𝔪 a t :=
  k.rec fun m h ↦ have H : IsPullbackAlong .. := ((reassoc_of% h) _).trans pointOf_hom
  (m.exists_model_over_arc H).elim fun m' E ↦ ⟨m', ext_of_isDominant_of_isSeparated (hom _)
    (by simp) genericPt (by simp [*, reassoc_of% E, H.comp_toFamily, fullStructure, ← π.eq_1])⟩

/-- Let s, u be complex points of a fibre power of the family X, attached (`ThetaFamily.IsPointOf`)
to a and b with their 𝔪-torsion. Then s = u iff some z is an isomorphism from a to b
(`ModuliPoint.IsLevelIso`) at level K(𝔑) ∩ K(𝔪). -/
lemma ThetaFamily.IsPointOf.eq_iff (h : X.IsPointOf 𝔪 a s) (k : IsPointOf 𝔪 b u) :
    s = u ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓ levelGU _ 𝔪) z b := by
  obtain ⟨⟨m, rfl⟩, m', rfl⟩ := h, k
  have J :=
    (Over.forget _).map_injective.comp ((isGroupBaseChange ‹_›).pointEquiv (T := 𝟙_ _)).injective
  simp [show ∀ w, w ∈ frameLattice b.x ↔ ‹PeriodMap ..›.Q w ∈ m'.uniformisation.L by
    simp [m'.lattice_eq, mem_classLattice, frameLattice], ← π.eq_1]
  use fun ⟨rfl, s, P⟩ ↦ ?_, fun ⟨z, ⟨h, k⟩, hz, P⟩ ↦ (m.exists_isogeny z hz m' rfl h.2.1.isIntMatrix
    (levelGU.isScalarFrame_inv_one h)).elim fun ρ ⟨ψ, _, _, c, v, p⟩ ↦ by
    suffices T : ∀ {𝔞}, _ ∈ levelGU D.Index 𝔞 → ∀ s ∈ torsionBy _ _ 𝔞,
      m.fullStructure.torsionPoint s ≫ ψ = m'.fullStructure.torsionPoint s from ((m.isRigid_pullback
      (.id _) (by simp [specMap])).eq_of_hom (Category.id_comp _) ρ.symm ψ (by simp [← pairing_comp,
      c]) (by rw [FullStructure.eta_eq, FullStructure.eta_eq, T h _ ·.2])).imp_right
      (by simp_all [← ·, ← comp_left_assoc, T k])
    rintro 𝔞 k ⟨y⟩ a; choose M m e using (mem_span_singleton_iff_exists_mul.1 <| k.2.2 · ·)
    erw [v, eq_add_of_sub_eq (Matrix.ext e : _ = 𝔞 • M), add_mulVec, smul_mulVec, ← mulVec_smul,
      map_add, torsionClass_mulVec_eq_zero m a]; aesop
  choose z hF hQ hz using m.exists_matrix_of_hom m' (𝟙 _) (hψ := ⟨by simp⟩) one_ne_zero (by simp)
  have T := m.torsionPoint_comp _ hF
  set k := _ * a.x
  simp at T
  have I {k} (h : ∀ {y}, _ = 0 → torsionClass (k *ᵥ y) = 0) (i j : D.Index) : k i j ∈ Ô E :=
    mul_one k ▸ torsionClass_eq_zero.1 (h (torsionClass_eq_zero.2 ((Ô E).matrix.one_mem · j))) i
  have K {𝔞} h (s : ∀ {y}, 𝔞 • y = 0 → m.fullStructure.torsionPoint y = _) : k ∈ levelGU _ 𝔞 :=
    ⟨⟨1, by
    simp [k, ↓← ‹PeriodMap ..›.isFrameFor.mul_iff, mul_assoc, ← IsFrameFor.conj_iff]
    convert ← ‹PeriodMap _ a.x ..›.isFrameFor
    ext; exact sub_eq_zero.1 ((traceForm_nondegenerate ℚ E).1 _ fun a ↦ by
      simpa [show D.ξ ≠ 0 from (by simpa [·] using D.xi_im_pos_and_re_eq_zero v₀), mul_assoc,
        mul_comm a] using hQ (toRealVectors (Pi.single _ a)) (toRealVectors (Pi.single _
        (star D.ξ⁻¹))))⟩, mem_intGL.2 ⟨I (m'.fullStructure.injective <| by simp [← T, ·]),
    I (m.fullStructure.injective <| by simp [T, ·])⟩, fun i j ↦
    mem_span_singleton_iff_exists_mul.2 ⟨_, torsionClass_eq_iff.1 (m'.fullStructure.injective
    (T (Pi.single j (isUnit_algebraMap_finAdele (a := 𝔞) h).unit⁻¹.1) ▸ s (torsionClass_eq_zero.2
    (by simp [ite_mem, Algebra.smul_def])))) i, by simp [mul_sub, mul_left_comm]⟩⟩
  use z, ⟨K D.level_ne_zero (m.fullStructure.eta_eq ⟨_, ·⟩ ▸ m'.fullStructure.eta_eq _),
    K (by simp) (dite _ (by simp [·]) <| (J ·) ∘ s _ ·)⟩, hz, (J <| hF _ ▸ P ·)

namespace UniversalFamily

/-- For a finite family γ of pairs (𝔪_j, g_j), the reduced closure, in a product of fibre
powers, of the tuples of complex points of a·(g_j, 1) with their 𝔪_j-torsion. -/
abbrev GraphClosure ν := ReducedClosure fun j a ↦ U.datumPoint (ν := ν) (γ j).1 (.act a (γ j).2)

variable {γ} (C : U.GraphClosure γ ν)

lemma isPointOf_datumPoint : U.family.IsPointOf 𝔪 a (datumPoint 𝔪 a).1 := by grind [datumPoint]

lemma IsPt.eq_datumPoint (h : U.family.IsPointOf 𝔪 a u) : u = (datumPoint 𝔪 a).1 :=
  (h.eq_iff isPointOf_datumPoint).2 ⟨1, by simp [ratConj]⟩

lemma datumPoint_eq_iff : U.datumPoint 𝔪 a = datumPoint 𝔪 b ↔ ∃ z, a.IsLevelIso (levelGU _ D.𝔑 ⊓
  levelGU _ 𝔪) z b := OverMorphism.ext_iff.trans (isPointOf_datumPoint.eq_iff isPointOf_datumPoint)

instance : HasProjEmbedding X.A.hom := ⟨X.embeds⟩

instance : HasProjEmbedding (X.fibrePower κ).hom := .pi (𝟙 _)

instance : HasProjEmbedding C.W.hom := .pi C.incl

lemma GraphClosure.exists_level_point_eq : ∃ m : (𝓞 E)⁰, ∀ {a b z}, IsLevelIso (levelGU _ m) z a b →
  C.point a = C.point b := (exists_level_conj_mem D.level_ne_zero (.image γ .univ)).imp fun _ h _ _
  z r ↦ C.hom_ext fun j ↦ by simpa [datumPoint_eq_iff, -act] using
  ⟨z, by simpa [mul_assoc] using h _ (by simp) _ r.mem_level, r.reflection_eq,
  (by simpa using realVecAction_mem_frameLattice (A := 1) (by simpa using (γ j).2.2.2) <|
  r.sub_mem_lattice ·)⟩

/-- The ν-fold fibre power Z of the universal family is smooth over R of relative dimension |n|
− 1 + ν|n|[E⁺:ℚ]; its complex points [a] (`UniversalFamily.datumPoint`, 𝔪 = 1) are dense, and
R-endomorphisms m_α of Z send [a·(g,1)] to [a·(g,α)]. -/
lemma fibrePower_spec ν : let Z := (Over.map U.base.hom) (fibrePower (_ ⊕ Fin ν))
  let c : _ → (_ ⟶ Z) := datumPoint 1; SmoothOfRelativeDimension (card D.Index - 1 + ν * abelianDim
    E D.Index) Z.hom ∧ IsDenseFamily (c · |>.1) ∧ ∃ m : _ → _, ∀ g α a, c (.act a g) ≫ m α =
    c (a.act g α) := suffices _ from ⟨Nat.add_comm .. ▸ smoothOfRelativeDimension_comp (hf := this)
    (hg := U.smooth) .., U.dense.of_fibres _ (s := this.smooth) fun a y h ↦ ⟨a.1.ballPoint 0 (_,
    fun i ↦ surjInv (U.model a).uniformisation.surjective ((ThetaObject.isGroupBaseChange
    _).pointEquiv.2 (homMk (y ≫ U.family.proj (.inr i))))), (IsPt.eq_datumPoint ⟨U.model a,
    fibrePower_ext_iff.2 (by simp_all [π, IsGroupBaseChange.pointEquiv, surjInv_eq])⟩).symm⟩,
    fun α ↦ (Over.map _).map (Limits.Pi.map (·.swap.elim α 1 • 𝟙 _)), fun g α a ↦
    isPointOf_datumPoint.rec fun m h ↦ by ext; exact IsPt.eq_datumPoint ⟨by exact m,
    (h =≫ _).trans (congrArg Hom.left (Pi.hom_ext (_ ≫ _) _ (by simp [π, m.equivariant])))⟩⟩
  Exists.elim (by refine ν.rec ⟨⟨Fan.mk (𝟙_ _) nofun, .mk (toUnit ·.1)⟩, ?_⟩ fun m ⟨F, H⟩ ↦
    ⟨⟨_, extendFanIsLimit _ F.2 (tensorProductIsBinaryProduct ..)⟩, ?_⟩ <;> simp [extendFan,
    add_mul, pullback.condition, add_comm] <;> infer_instance) fun F ↦
  (smoothOfRelativeDimension_isStableUnderBaseChange _).1 (.of_horiz_isIso ⟨(Pi.reindex
  (@Equiv.emptySum _ _ ⟨by simp⟩) (fun _ ↦ U.family.A) ≪≫ limit.isoLimitCone F).hom.3⟩)
end UniversalFamily
end
end
