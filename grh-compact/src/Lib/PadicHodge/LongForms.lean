import New.Weil.MemberOrthogonality
import New.Weil.Separation
import New.Weil.ComparisonForms
import Lib.PadicHodge.HeckeAlgebra
import New.Weil.LabelRigidity
import Lib.PadicHodge.LabelledColumns
import Lib.PadicHodge.HeckeStableSubspaces
import Lib.PadicHodge.OddShaBound
import Lib.PadicHodge.TiltingLemma
import New.Weil.RowDimension
import Lib.PadicHodge.BaseLevel
import Lib.PadicHodge.OnePrimeTie
import Lib.PadicHodge.RibetElement
import Lib.PadicHodge.RowBalanced
import New.Weil.RowVolume
import New.Weil.CrudeRows
import New.Weil.ShortAndEnough

section
/-! Each ratio of Hecke values repays one direction. At the chosen twists, with valuations bounded
by test forms and class group characters, the inverse of a ratio of twisted to untwisted Hecke
L-values has height at most a small error minus the cost of one direction of a lift, so the product
of about k such ratios has height at most a small error minus k·`Data.dirCost`. Norms of lifts of
Hecke characters as
L-values, their divisibility via congruences and divisibility at inert primes are known. Related
work: Prasanna, Integrality of a ratio of Petersson norms, 2006; Coates–Liang–Sujatha,
Tate–Shafarevich group for elliptic curves with CM II, 2010 (after Katz, 1977); Y.-S. Lee, Hida
family of theta lift from U(1) to definite U(2), 2024.

This file: Inverse ratio of twisted Hecke values has height repaying one direction; product
version. -/

open AutChar DoubleCoset Finset Fintype IsUltrametricDist LValueData Matrix LevelPlaces
  QuotientGroup Real Submodule Data.Pair

variable {P} {D : Data P} {l : ℕ} [Fact l.Prime] {E κ n : Type} [Fintype n] {X :
  LValueData D.E n} {m}
  {q : D.Pair} {ϑ} {F : Gf D.E (Fin m) → X.auxPair.FormV} (H : q.IsFlat (Fin m)) {p q₂ q₃ : D.Pair}

open IsMulCommutative in
/-- Let K ⊂ U(1)(𝔸_f) contain the principal level at places w_i ∈ S, with trivial stabilisers, and n
the class number. Then for some z and some weight-zero χ tame on S, the class sum of
(χs)(gz), divided by n, is ι-adically at least as large as s(1). -/
lemma exists_twisted_classSum_ge [Field E] [CMType E] (w : κ → _) S (hS : ∀ i,
  w i ∈ S) (ι : ℂ →+* ℂ_[l]) (s : Gf E Unit → ℂ) {Γ K} (hΓ : stdRatPoints ≤ Γ) (hK : levelOf w ⊥ ≤
  K) [HasFiniteType Γ K] (a : ∀ g, classAut Γ K g = ⊥) : ∃ z, ∃ χ : tameChars S, ‖ι (s 1)‖ ≤ ‖ι
  (classSum Γ K (fun g ↦ χ.1.1.1 (detFin 1 (g * z)) * s (g * z)) / classSum Γ K 1)‖ := by
  have c u i j : (scalarFin (E := E) Unit u).1.1 i j = u := ite_eq_left rfl
  have := @ofFinite _ ‹HasFiniteType ..›.1; unfold classSum DoubleCoset.Quotient at *
  rw [show setoid Γ K = leftRel (Γ ⊔ K) by ext a; simp only [rel_iff, eq_comm, leftRel_apply,
    Γ.mem_sup, mul_left_comm a, eq_inv_mul_iff_mul_eq, mul_assoc]] at *
  choose χ k using fun ψ : AddChar (Additive _) ℂ ↦ (AutChar.exists_mem_tameChars
    (ψ.toMonoidHom.comp (map _ (Γ ⊔ K) ((scalarFin _).comp (Unitary.map ⟨.snd .., by simp⟩).1)
    (sup_le (fun _ ⟨_, h⟩ ↦ le_sup_of_le_left hΓ (mem_stdRatPoints_iff.2 fun _ _ ↦ ⟨_,
    (c ..).substr congr($h.2)⟩)) fun _ h ↦ le_sup_of_le_right hK (mem_levelOf.2 ⟨mem_Kf.2 fun _ _ ↦
    (c ..).substr h.1, by ext; simp; exact congr(reduceAt _ ⟨$(c ..), _⟩).trans (h.2 _
    (hS _))⟩))))).imp fun _ h g ↦ (h (detFin 1 g)).trans (congrArg (ψ <|
    .ofMul ⟦·⟧) (by ext; simp [G.det, U.det, Gf.atPlace, c]; rfl : _ = g))
  refine ⟨(1 : _ ⧸ Γ ⊔ K).out⁻¹, (exists_norm_finsetSum_le ⊤ _).imp' χ fun _ ↦ (·.2.trans_eq' ?_)⟩
  simp [a, ← map_sum, ← sum_div, sum_comm, ← sum_mul, AddChar.sum_apply_eq_ite, k]
  erw [mul_div_cancel_left₀]; simp

namespace Data

/-- Multiplicative pigeonhole: let G be a finite group, ι: ℂ → F a ring homomorphism to a normed
field, and V^|G| = ∏_χ a(χ)b(χ). Then every ψ in G is a product φχ with ‖ι V‖ ≤
‖ι(a(φ)b(χ))‖. -/
lemma exists_factorisation_le {G F} [Group G] [Fintype G] [NormedField F] (ι : ℂ →+* F) {a b :
  G → ℂ} {V} (e : V ^ card G = ∏ χ, a χ * b χ) ψ : ∃ φ χ, φ * χ = ψ ∧ ‖ι V‖ ≤ ‖ι (a φ * b χ)‖ :=
  (exists_max_image _ _ univ_nonempty).elim fun χ h ↦ ⟨_, χ, div_mul_cancel ..,
  le_of_pow_le_pow_left₀ card_ne_zero (by bound) (((prod_le_prod₀ (by bound) h.2).trans_eq
  (prod_const _)).trans' (by simp [← norm_pow, ← map_pow, e, ← (Equiv.divLeft ψ).prod_comp a]))⟩

/-- For a pair q with c = ⌊m/2⌋: `Data.chosenGroupOrder` times the class sum over h of den·(∏_{w∈Q}
Nw)^{1−m}·⟨1, den·Ξ(h)⟩·F(h), with Ξ = `Data.Pair.trivialLift` and den = `Data.Pair.denomBound`. -/
noncomputable def Pair.xiSum ϑ (F : _ → X.auxPair.FormV) :=
  D.chosenGroupOrder • stdClassSum (lValueData H.2 ϑ).auxPair.levelGroup fun h ↦ (q.denomBound /
  ϑ.levelNorm ^ (m - 1) * gramForm 1 ((q.denomBound : ℂ) • trivialLift H.2 ϑ h)) • F h

lemma Pair.xiSum_mem [PadicPlace l] (hl : l.Coprime ϑ.levelNorm) {N : Submodule embValRing _} (h :
  ∀ h, F h ∈ N) : xiSum H ϑ F ∈ N := smul_classSum_mem N (D.card_classAut_dvd_chosenGroupOrder
  (H.2.1 ▸ D.nat_le_of_hasLogBound) levelOf_le_Kf) (N.smul_mem ⟨_, mul_mem
  (by simp [← NNReal.coe_le_coe, norm_natCast_le_one, hl.norm_natCast_eq_one, -Nat.cast_prod])
  (by simpa [trivialLift_apply, smul_sum] using sum_mem fun _ _ ↦ gramForm_mem_embValRing _ (by
  simp [weylGauge, weylRep, schur_eq_one, H]) (weylGauge_pointKernel_le_one (hl := hl) ..))⟩ <| h ·)

lemma Pair.smul_apply_xiSum g {A B} {L : _ →L⋆[ℂ] ℂ} (e : ∀ h i, L (F h) =
  B * (A * (lValueData H.2 ϑ).kernelForm g h i)) : ((stdClassSum (lValueData H.2 ϑ).chosenLevel 1 *
  P.vacuumScale D.s ^ m) • L) (xiSum H ϑ F) = B * intAlgPart H.2 ϑ * A := by
  have t := congr(star $(inner_trivialLift _ g (lValueData H.2 ϑ).trivialLift))
  simp [theta_eq_inner_kernelForm, mul_comm' _ g, ← twistedCentralOp_kernelForm,
    ← inner_twistedCentralOp, twistedCentralOp_trivialLift] at t
  simp [inner, LevelForm.innerAt_eq_stdClassSum, xiSum, intAlgPart, trivialLift, norm_smul, mul_pow,
    t, ← Complex.mul_conj', apply_eq_evalForm,
    map_classSum, ↓classSum_mul, mul_classSum, division_def, H.1, gramForm_apply, mul_sum, sum_mul,
    dot_mulVec_eq_sum_sum, -norm_pow]; congr! 6; rw [e]; ring!

seal Finset.univ Finset.sum Finset.prod in
open _root_.Nat in
/-- Let p have rank one, blocks of ranks 12, 4, 4 and 2z − 20, ϑ a twist prime to l, degrees and
characters matching. Some integral test form at l pairs with the theta kernel to explicit constants
times three norms `Data.Pair.intAlgPart` times the rank-12 kernel of monomial α. -/
lemma exists_test_form_inner_kernelForm (H : q.IsFlat (Fin (2 * p.z - 20))) (H₂ : q₂.IsFlat (Fin 4))
  (H₃ : q₃.IsFlat (Fin 4)) {j α b} [PadicPlace l] (hE : p.IsRankOne j) (ϑ : D.Twist) (hl :
  l.Coprime ϑ.levelNorm) x₀ : let X := lValueData hE.1 ϑ; let u := @.one P D; (∀ τ, ∑ i, α (τ, i,
      ()) = X.jetDeg τ) → b * ((lValueData H₂.2 ϑ).auxPair.b * (lValueData H₃.2 u).auxPair.b) *
      (lValueData H.2 u).auxPair.b = X.auxPair.b → ∃ Ξ, (∀ g, inner ℂ Ξ (X.kernelForm g) *
      (stdClassSum X.chosenLevel 1 ^ 3 * P.vacuumScale D.s ^ (2 * p.z - 20 + 8)) = (∏ τ, (X.jetDeg
      τ)! :) / α.prod (fun _ k ↦ ↑k !) * q.intAlgPart H.2 u * q₃.intAlgPart H₃.2 u * q₂.intAlgPart
      H₂.2 ϑ * modKernel (stdSpace ..) (stdSpace _ (Fin 12)) 1 b (X.levelModulus 1 false)
      (Pi.single x₀ 1) (.monomial α 1) (1, g) (1, 1)) ∧ X.auxPair.IsTestForm l Ξ := by
  intro X u hα hb; have hG i : ¬D.IsChosen (X.twistPlace i) :=
    (D.levelNorm_mem_and_notMem_of_mem_Q ϑ (.inl i.2)).2.1
  obtain ⟨⟨c, hc, hr⟩, k, e⟩ := exists_int_vector_harmonicPoly_eq X (.trans .inl .inl) hα,
    (.prod_right nofun : l.Coprime u.levelNorm), (⟨nofun⟩ : IsEmpty (D.levelPlaces u).TwistIndex)
  let F h₁ h₂ h₃ := pointForm (O := X.auxPair) (Y := fun i ↦
    fromRows (fromRows (x₀.map (modulusResidue _ (places_levelModulus_false.ge ⟨_,
    rfl⟩))) (fromRows (inclMatrix _ chosenIndexEmb) (inclMatrix _ chosenIndexEmb)))
    (inclMatrix _ (lValueData H.2 u).auxPair.incl)) (U.blockSumOne (U.blockSumOne (1, U.blockSumOne
    (h₂, h₃)), h₁)) (fun _ _ _ h ↦ inclMatrix_mulVecLin_injective _ _ congr($h ∘ .inr))
    (chosenIndexEmb.trans (.trans .inl (.trans .inr .inl))) ((↑) ∘ c)
  refine ⟨xiSum H₂ ϑ fun h₂ ↦ xiSum H₃ u fun h₃ ↦ xiSum H u (F · h₂ h₃), fun g ↦ .trans (by
    simp [-classSum_mul]; ring!) (smul_apply_xiSum _ g fun _ _ ↦ smul_apply_xiSum _ g fun _ _ ↦
    smul_apply_xiSum (L := innerSLFlip ℂ _) _ g fun _ _ ↦ ?_), fun _ ↦ xiSum_mem _ hl fun _ ↦
    xiSum_mem _ k fun _ ↦ xiSum_mem _ k fun _ _ ↦
    (weylGauge_deltaForm_le isOfFinOrder_level_char).trans ?_, fun w hw hS ↦ (restrictScalars_mem
    embValRing ..).1 (xiSum_mem _ hl fun _ ↦ xiSum_mem _ k fun _ y hy ↦ inner_eq_zero_symm.1 ?_)⟩
  · erw [innerSLFlip_apply_apply, ← inner_conj_symm, ← X.theta_eq_inner_kernelForm, theta_pointForm,
      hc, ← modKernelBilin_apply]
    rw [mul_assoc (modKernel ..), ← hb]
    simp +singlePass (disch := simp +instances [levelModulus, levelPlaces, X, sq, ↓prod_of_isEmpty,
      *, funext_iff, Ideal.mul_le_left.trans]) only [↓kernelForm_of_jetDeg_eq_zero, modKernel,
      ← modDatum_factor (𝔪' := X.levelModulus 2), ← modKernel.eq_1]
    simp_rw [← modKernelI_block (.refl _)]
    simp [prod_eq_zero_iff, AuxPair.a]; congr! 2; obtain ⟨T, rfl⟩ :=
      _root_.Ideal.Quotient.mk_surjective.comp_left.comp_left ‹_›
    simp [(X.levelModulus 1 false).matrix_ext_modulusResidue X.isConjApart_chosenPlace.1, ← ext_iff,
      AuxPair.resDetDatum, X, ψ_eq_one, hG, univ_eq_empty, forall_and, ← ite_and]; congr! 1; tauto
  · erw [weylGauge_mul _ (Kf_le_localLevel _), weylGauge, hr] <;> simp [← map_inv, U.sum,
      funext_iff, pi_norm_le_iff_of_nonneg, norm_intCast_le_one]
  simp [xiSum, Pair.trivialLift, apply_eq_evalForm, LValueData.trivialLift, map_classSum, mul_assoc,
    ← mul_classSum, classSum_comm (K' := levelOf _ ⊥), ← innerSLFlip_apply_apply]; repeat right
  refine finsum_eq_zero_of_forall_eq_zero fun g ↦
    smul_eq_zero_of_right _ (stdClassSum_period_eq_zero X.fitsParams_auxPair (by simpa [X, ψ_eq_one,
    hG] using! (ϑ.psi_ne_one _ ·.2)) (fun i _ v ↦ hy.1.1.choose_spec ▸ ?_) hy.2
    hy.1.2 (by simp; grind [IsRankOne, le_m]) (.refl _) _ (.toSpanSingleton .. ∘ₛₗ gramForm (κ :=
    (lValueData H.2 u).auxPair.κ).flip 1) (fun _ _ _ f ↦ ?_) ?_ (one_mem _) (fun _ ↦ by
    simp [kernelForm_of_jetDeg_eq_zero, kernelVector, nablaBasis_eq_one, H.1, funext_iff,
      gramForm_apply, ← apply_eq_evalForm, dot_mulVec_eq_sum_sum,
    ← mul_sum, ← sum_mul, AuxPair.a]; ring!) rfl fun j hj ↦ ?_)
  · erw [← Module.End.mul_apply, ← map_mul,
      piTensorElem_mul_eq_zero i (reflectionSum_mul_labelIdem ((isApt_rank_one _
      hE).isLabel_twistedLabel (O := X.auxPair) i ∘ by simp +contextual [twistedLabel]) v)]; simp
  simp [conjWeylRep, hr, f]
  iterate 2 simp [weylRep, schur_eq_one, H.1, places_levelModulus, X, u, levelPlaces,
    twist_one_spec]
  have J i := mem_stabilizer_col_iff.1 ((mem_levelOf.1 hj).2 (.inl i) ⟨⟩)
  use by simp_all [AuxPair.resDetDatum, ↓Matrix.map_mul, ↓reductionK₀_map_modulusResidue,
    inv_mul_eq_iff_eq_mul_of_invertible, Kf.reduceFamily, univ_eq_empty, -Sum.elim_inl], by
    simpa using (map_block_eq_blockGL (reduceAt w) _ 1 j).1, fun i ↦ ?_
  simp; erw [(map_block_eq_blockGL _ _ 1 j).2, fromBlocks_mul_fromRows]
  simpa +instances [fromRows_ext_iff] using! J i

seal Finset.univ Finset.sum Finset.prod in
/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily`, 1 ≤ j ≤ m and a pair p of rank one for j
(`Data.Pair.IsRankOne`), the inverse L-value ratios 1/ρ_p(θ(ι)^j), ρ = `Data.Pair.ratio`, have
height (`HeightLe`) at most 6B₀ − 𝖴, 𝖴 = `Data.dirCost`.

Each ratio of Hecke values repays one direction. -/
lemma heightLe_inv_ratio {θ} (o : D.IsFitFamily θ) (j : D.LiftIndex) (p : D.Pair) (hE :
  p.IsRankOne j) : HeightLe (6 * D.B₀ - D.dirCost) fun ι ↦ (p.ratio ((θ ι).powTwist j))⁻¹ := by
  obtain ⟨f, _, A, H, _⟩ := ofFinite (tameChars D.finite_isChosen.toFinset), D.le_m,
    D.classAut_eq_bot_of_le_chosenLevel le_rfl (card_unit.trans_le D.nat_le_of_hasLogBound), id hE
  choose _ c₁ H₁ using D.exists_isFlat (Fin (2 * p.z - 20))
  have Z := D.exists_isFlat (Fin 4)
  obtain ⟨⟨q₂, c₂, H₂⟩, t, t0, ht, hd⟩ := Z ⟨(D.χ, D.ω), D.chi_hasWeight, by simp_all⟩,
    D.depth_indicator_jet (p.c · - p.z) fun τ ↦ by
      grw [nominalWeight_le_w_sub _ j, ← @w_le_nominalWeight_add _ D j (by grind)]
      norm_cast; grind
  choose _ c₃ H₃ using Z
  obtain ⟨⟨γ, g, G⟩, V, e⟩ := o.2 j, IsAlgClosed.exists_pow_nat_eq (∏ χ, Pair.intAlgPart (H₃ χ).2
    .one * (Pair.intAlgPart (H₁ χ).2 .one * (t * q₂.intAlgPart H₂.2 .one))) f.card_pos
  let N := Nat.card (StdClasses (n := Unit) D.chosenLevel)
  have K (l : PrimePadicIso) [PadicPlace l.1] : let ϑ := (θ l).powTwist j; ∃ Ξ,
      AuxPair.IsTestForm _ l.1 Ξ ∧ ‖ιₚ V‖ *
      l.1 ^ (-D.forcedPart l.1) ≤ ‖ιₚ (N ^ 2 * inner ℂ Ξ (Pair.trivialLift H ϑ) / q₂.ratio ϑ)‖ := ?_
  have hV (σ : ℂ ≃+* ℂ) : ‖σ V‖ ≤ exp D.B₀ := by
    choose _ _ _ h using exists_factorisation_le (σ : ℂ →+* ℂ) e 1
    simp at h; grw [h, ht]; repeat grw [norm_conj_intAlgPart_le]
    use D.le_of_hasLogBound D.lt_of_hasLogBound; all_goals apply_assumption
  refine (((heightLe_norm_trivialLift_sq hE).mul
    ((o.3 j q₂ 1 (by simpa [Pair.IsRamified, c₂] using D.omega_zpow_ne_one 1)).pow 2)).mul
    (y' := fun ι ↦ (q₂.ratio ((θ ι).powTwist j) / ‖Pair.trivialLift H ((θ ι).powTwist j)‖) ^ 2 /
    N ^ 3) ⟨V * star V, _, fun l ↦
    γ l + 2 • (D.forcedPart l * log l), by simpa [prod_eq_zero_iff, t0] using congr($e = 0), fun σ ↦
    exp_add .. ▸ map_mul σ .. ▸ norm_mul_le_of_le (hV σ) (hV (.trans starRingAut σ)), fun ι ↦ by
    choose Ξ b h using (@K ι ⟨(complexToCp ι.2).comp ·⟩)
    have := mul_le_mul (h 1) (h starRingAut.toRingHom) (by bound) (by bound)
    grw [exp_add, exp_nsmul, ← show ‖ι.2 (N * _)‖ ≤
      _ from ((G ι).2 p hE).rank_one_bound _ A (b 1) (b _)]
    simp [rpow_def_of_pos, ι.1.2.pos, exp_neg, ratio_ne_zero_and_real, field, -map_natCast, N,
      ← span_singleton_smul_eq (left_ne_zero_of_smul (trivialLift_ne_zero H .one)).isUnit
      (LValueData.trivialLift _), starProjection_singleton, ↓← Pair.trivialLift.eq_1] at this ⊢
    grw [this]; ring_nf; rfl, Filter.eventually_atTop.2 ⟨⌈D.x₁⌉₊, fun U hU ↦ by
    simp [dirCost, forcedPart, sum_mul, mul_sum, (filter ..).sum_comm, mul_assoc,
      D.primeSum_eq_sum_localAsk hU, (D.le_of_hasLogBound : D.nominalWeight _ ≤ D.a)]
    grw [g, (D.le_of_hasLogBound : D.x ^ 999 ≤ D.B₀)]; linarith; simp⟩⟩).mono (add_sub_cancel ..).le
    fun ι ↦ ?_
  have := @ratio_ne_zero_and_real
  have := @NeZero.ne ℕ
  simp [ratio_eq_intAlgPart_div H, Pair.intAlgPart, denomBound, twist_one_spec, field, *]
  repeat grw [norm_natCast_le_one]; simp
  intro ϑ; let b := (lValueData H ϑ).auxPair.b / (lValueData H₂.2 ϑ).auxPair.b
  obtain ⟨α, x₀, hα, hd⟩ :=
    hd (D.𝔪 ϑ 1 false) (pow_one D.piGBar ▸ D.ideal_untwistedModulus_eq_span) _
  obtain ⟨z, ψ, hr⟩ := exists_twisted_classSum_ge (D.levelPlaces ϑ).chosenPlace _
    (D.finite_isChosen.mem_toFinset.2 ·.2.2.1) ιₚ (modKernel (stdSpace ..) (stdSpace ..) 1 b _
    (Pi.single x₀ 1) (.monomial α 1) ⟨1, ·⟩ 1) le_rfl le_rfl A
  obtain ⟨ψ₃, ψ₁, hψ, h⟩ := exists_factorisation_le ιₚ e ψ
  refine (exists_test_form_inner_kernelForm (H₁ ψ₁) H₂ (H₃ ψ₃) (b := b / ψ.1.1) hE ϑ (o.1 l) x₀ hα
    (by simp [b, AuxPair.b, ← hψ, c₁, c₃, twist_one_spec, div_div, mul_assoc])).imp fun Ξ ⟨E, T⟩ ↦
    ⟨T, ?_⟩
  have n : stdClassSum (lValueData H ϑ).chosenLevel 1 =
    (N : ℂ) := show stdClassSum D.chosenLevel 1 = _ by simp [classSum, A, N]; rfl
  simp [MvPowerSeries.coeff_apply, Space.jetSeries_apply, modKernel, pairTheta, pairWeil, modDatum,
    n] at hd hr E
  grw [hd, hr, h, ratio_eq_intAlgPart_div H₂.2, Pair.trivialLift, inner_smul_right,
    ← inner_conj_symm, inner_trivialLift _ z]
  simp [map_classSum, hα, theta_eq_inner_kernelForm, division_def, ← mul_classSum, ← classSum_mul,
    α.degree_eq_sum, sum_prod_type, eq_div_of_mul_eq (by simp [N]) (E _)]
  field_simp [t0]
  ring_nf; rfl

/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily` and 1 ≤ j ≤ m, the numbers
(Γ(θ(ι)^j)/Γ(1))⁻¹, Γ = `Data.heckeValueProd`, have height (`HeightLe`) at most
10m·x^999 + k(6B₀ − 𝖴), 𝖴 = `Data.dirCost`.

Each ratio of Hecke values repays one direction. -/
lemma heightLe_inv_heckeValueProd_div {θ} (hf : D.IsFitFamily θ) j :
  HeightLe (10 * D.m * D.x ^ 999 + D.k * (6 * D.B₀ - D.dirCost)) fun ι ↦ (heckeValueProd j
  ((θ ι).powTwist j) / heckeValueProd j 1)⁻¹ := hf.heightLe_of_eq_zpow_mul (((HeightLe.prod (s :=
  Ioc (7 * (D.m / 2)) D.heckeCount) fun z _ ↦ heightLe_inv_ratio hf j ((linePair j none).lowerPoint
  z) (by simp [IsRankOne, HasLiftRank, Pair.lowerPoint, linePair]; grind [heckeCount, le_m])).mul
  (.prod (s := univ.sigma (Ioc 0 <| Option.elim · (7 * (D.m / 2)) D.eSign)) fun x _ ↦
  hf.3 j ((linePair j x.1).lowerPoint x.2) (x.1.getD 1)
  (by cases x.1 <;> exact omega_zpow_ne_one _ (by simp [Int.natAbs_mul]; grind)))).pow
  2) (by simp [eSign, heckeCount, Even.two_dvd, m_even, k_even]; grind) fun ι n ↦
  ⟨-∑ i, (linePair j i).z ^ 2, by
  simp [heckeValueProd,
    twist_one_spec, ↓lValueProd_eq _ _ ((θ ι).powTwist j).1, ↓_root_.zpow_neg, ↓zpow_natCast,
    Finset.prod_sigma, prod_pow, heckeCount, ← prod_Ioc_consecutive _ zero_le le_self_add, show ∀ s,
    Icc 1 (linePair j s).z = Ioc 0 (s.elim D.heckeCount D.eSign) by rintro ⟨⟩ <;> rfl] at n ⊢
  simp [*, field]; ring!⟩
end Data
end

section
/-! The rows repay the cost of the idle directions. The volume of the chain of lifts on the D rows
is a controlled factor times the volumes of m single lifts, and at the chosen twists each
untwisted-to-twisted ratio of these has height at most D times (a small error minus the cost of k
directions), which gives the lower bound that cancels this cost. Bounding the norm of a lift
by an integral form and a congruence denominator is known for one eigenform. Related work:
Böcherer–Dummigan–Schulze-Pillot, Yoshida lifts and Selmer groups, 2012; X. Zhang, Special L-values
and Selmer groups of Siegel modular forms of genus 2, 2018; Hida, Congruences of cusp forms and
special values of their zeta functions, 1981.

This file: Height bound for untwisted over twisted volume of one lift on good forms. -/

open Module ComplexConjugate Finset Function PolyRep IsAlgClosed LinearMap Matrix NumberField
  AuxPair Real Space LevelPlaces.LevelForm

variable {T U V} [NormedAddCommGroup T] [InnerProductSpace ℂ T] [Module.Finite ℂ T]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [Module.Finite ℂ U] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [Module.Finite ℂ V] {gl : T →ₗ[ℂ] V} {u : U →ₗ[ℂ] V} {A} {γ : ℂ} (k : ℂ)

namespace Data

/-- The endomorphism z ↦ k·pr_L(gl(gl* z)) of the subspace L of V, where gl* is the adjoint of
gl and pr_L the orthogonal projection to L. -/
noncomputable def compressedGramOp (L : Submodule ℂ V) (gl : T →ₗ[ℂ] V) :
    End ℂ L := k • (L.orthogonalProjectionOnto.toLinearMap ∘ₗ gl) ∘ₗ gl.adjoint.domRestrict L

/-- If u* ∘ gl = γA for linear maps of finite-dimensional complex inner product spaces, then gl*
∘ u = γ̄A*. -/
lemma adjoint_comp_eq_conj_smul (h : u.adjoint ∘ₗ gl = γ • A) :
  gl.adjoint ∘ₗ u = conj γ • A.adjoint := by simpa [map_smulₛₗ] using congr(adjoint $h)

/-- `normDet(u)² · det(compressedGramOp k (range u) gl) = k^(dim range u) · normDet(gl* ∘ u)²`. -/
lemma det_compressedGramOp : u.normDet ^ 2 * (compressedGramOp k u.range gl).det = k ^ finrank ℂ
  u.range * (gl.adjoint ∘ₗ u).normDet ^ 2 := by rw [compressedGramOp, (eq_adjoint_iff (_ ∘ₗ gl)
  (gl.adjoint.domRestrict _)).2, normDet_comp] <;> simp [adjoint_inner_right, ← normDet_sq, field]

variable {P} {D : Data P} {j : D.LiftIndex} {ϑ : D.Twist} {gl : Tables j →ₗ[ℂ]
  (D.auxPair ϑ j).FormV} {L : Submodule ℂ _} {β} (sep : ∀ z : L, gl.adjoint z = 0 → z = 0)
  (tst : ∀ (z : SubmoduleElem L), (D.auxPair ϑ.toTameChar j).IsTested D.e₀ Lᗮ (gl ((adjoint gl) z)))

include sep tst in
/-- Let gl* be injective on L, gl gl*L tested (`AuxPair.IsTested`), gl ζ integral at φ: ℂ → ℂ_ℓ
whenever ζ̄ is integral at φ∘conj, and `DenominatorLe` hold at ι. Then |ι det(𝗁·pr_L gl
gl* on L)| ≤ exp(dim L·rβ), 𝗁 = `smallHookNumber`. -/
lemma norm_det_compressedGramOp_padic_le (ι : PrimePadicIso) (int : ∀ ζ (φ : PadicPlace ι.1),
  (∀ a, weylGauge (ι := ⟨φ.ιₚ.comp conj⟩) _ 0
  a.2.out (star (ζ a)) ≤ 1) → gl ζ ∈ integralForms φ) (h : DenominatorLe ι.2 _ D.e₀ L β) :
  ‖ι.2 (compressedGramOp (smallHookNumber j) L gl).det‖ ≤ exp (finrank ℂ L * (D.r * β)) := by
  choose δ hγ _ using fun c : D.SmallClasses ↦ exists_mul_mem_integralAbove ι.1 c.out 1
  let f (a : _ × _) : Tables j := .toLp 2 fun b ↦ (star (weightRep _ 0 _ (δ b.2)⁻¹
    (star (((ite (b = a.1) (of fun i k ↦ fockPairing ℤ (nablaBasis ℤ _ _ i)
    (nablaBasis ℤ _ (untwistedAuxPair j).colsMinus k)) 0).map (↑)).col a.2))) :)
  have Y a ζ : inner ℂ (f a) ζ = smallHookNumber j * conj (weightRep _ 0 _ (δ a.1.2) (star (ζ a.1))
    a.2) := by erw [PiLp.inner_apply, Fintype.sum_eq_single a.1, show inner .. = gramForm _ _ from
    dotProduct_comm .., ← conj_gramForm, ← star_star (R := _ → ℂ) (ζ _), ← gramForm_map_weightRep
    (e := 0) conj (δ a.1.2)] <;> simp +contextual [f, comp_def, gramForm_apply, ← mulVec_single_one,
    -mulVec_single, ← map_mul_intCast, weylGram_mul_fockPairing, ← diagonal_intCast]
  choose c z e hz using exists_auerbach (finBasis ..) (fun a ↦ innerₛₗ ℂ (f a) ∘ₗ
    gl.adjoint.domRestrict _) (fun v h ↦ sep v (PiLp.ext fun c ↦ star_injective (R := _ → ℂ)
    ((Representation.apply_bijective ..).1 (by ext; simpa [Y] using h (c, _)))))
    (complexToCp ι.2) fun _ ↦ continuous_bot
  convert card_rowIndex D ▸ h _ rfl (gl ∘ f ∘ c) _ ?_ fun a ↦
    ⟨?_, tst ((smallHookNumber j : ℂ) • z a)⟩
  any_goals intros; apply int; intro; rw [← weylGauge_embFin, @weylGauge_le_one_iff (hk := hγ _)]
  simp [← det_toMatrix z, toMatrix_apply, ← z.coord_apply, e, compressedGramOp, adjoint_inner_right,
    det_apply]
  · simp [f, IsUltrametricDist.norm_intCast_le_one]
  simpa [Y] using fun i ↦ hz (_, i) a

include sep tst in
/-- Let gl* be injective on L and gl gl*L tested (`AuxPair.IsTested`). If L is the range of the lift
and gl has the size bound S at all σ, every conjugate of the determinant of `compressedGramOp` on L
has absolute value at most exp(dim L · β). -/
lemma norm_det_compressedGramOp_arch_le (e : L = (D.goodLift ϑ j).range) (S : ∀ ζ σ,
  smallHookNumber j * (gl ζ).normSqAt σ ≤ exp β * ∑ a, weylNormSq (σ ∘ ζ a)) (σ : ℂ ≃+* ℂ) : ‖σ
  (compressedGramOp (smallHookNumber j) L gl).det‖ ≤ exp (finrank ℂ L * β) := by
  erw [← place_apply σ.toRingHom, End.det_eq_prod_roots_charpoly_of_splits (splits _), exp_nat_mul,
    map_multiset_prod, ← charpoly_natDegree, ← card_roots_eq_natDegree]
  refine Multiset.prod_map_le_pow_card (by simp) fun α h ↦ ((End.hasEigenvalue_iff_isRoot_charpoly
    ..).2 (Polynomial.mem_roots'.1 h).2).exists_hasEigenvector.elim fun z h ↦ ?_
  obtain ⟨w, hw, t⟩ := (frequently_isSplit_notMem_places (D.auxPair ϑ j)).exists
  let ζ := gl.adjoint z
  have := congr(‖σ (inner ℂ (gl (.toLp 2 (star ∘ σ.symm ∘ star ∘ σ ∘ ζ ·)))
    ($h.apply_eq_smul).1)‖).ge
  simp [compressedGramOp, ← adjoint_inner_right gl _ z, ← le_div_iff₀'] at this S
  grw [show σ (inner ..) = ∑ i, weylNormSq (σ <| ζ i ·) by simp [ζ, inner, coe_weylNormSq,
    dotProduct, mulVec, mul_comm (conj _)], norm_map_inner_le, normSqAt_starProjection_le _ hw t
    D.isCentralProj_e₀ (e ▸ D.range_goodLift_le fun _ _ a _ k m ↦ ⟨D.range_tupleIdem_le k m,
    heckePolyOnForms_testValue_eq_zero _ _ (D.lifts_auxLift _ a.2)⟩) (tst z), S, S] at this
  simpa [ζ, comp_def, abs_of_pos, field, ↓Complex.norm_real, le_of_lt, (sum_pos' (by simp)
    ((not_forall.1 (h.2 ∘ sep z ∘ PiLp.ext)).imp (⟨mem_univ ·,
    weylGram_posDef.re_dotProduct_pos <| by simpa [funext_iff, SmallFormValues] using! ·⟩)) : 0 <
    ∑ i, weylNormSq (σ <| ζ i ·)), exp_pos] using this

/-- For m-fold twists θ(ι) satisfying `Data.IsFitFamily` and 1 ≤ j ≤ m, the volume ratios
λ_j(1)/λ_j(θ(ι)^j) (`Data.liftVolume`) have height (`HeightLe`) at most d·k·(B₀·log b − 𝖴), with d
the dimension of `Data.rows` and 𝖴 = `Data.dirCost` (size of a jet less its forced divisibility), B₀
= fa(log b)³/(mk) = `Data.B₀`.

The rows repay the cost of the idle directions. -/
lemma heightLe_liftVolume_ratio {θ} (O : D.IsFitFamily θ) (j : D.LiftIndex) :
  HeightLe (D.rowDim * (D.k * (D.logB * D.B₀ - D.dirCost))) fun ι ↦
  D.liftVolume 1 j / D.liftVolume (θ ι) j := (O.denominator_le j).elim fun β ⟨g, g'⟩ ↦ by
  rw [D.finrank_rows_eq_finrank_goodForms j, liftVolume, show TameChar.pow _ j =
    .one by rw [TameChar.pow]; congr <;> apply one_pow]
  obtain ⟨γ, A, gl, H, ad, sur, tst, int, S⟩ := exists_comparison_forms j
  have d ϑ := finrank_range_of_inj (f := D.goodLift ϑ j) (by simp [auxLift_injective])
  replace tst ϑ y :=
    (A.adjoint.map_smul ..).trans congr($(adjoint_comp_eq_conj_smul (ad ϑ)) y).symm ▸ tst ϑ _
  let u (ϑ : D.Twist) := (compressedGramOp (smallHookNumber j) (D.goodLift ϑ j).range (gl ϑ)).det
  have V ϑ : _ * u ϑ = _ := adjoint_comp_eq_conj_smul (ad ϑ) ▸ d ϑ ▸ det_compressedGramOp _
  have T ϑ := right_ne_zero_of_mul ((V ϑ).trans_ne (by simp [H,
    normDet_eq_zero_iff_ker_ne_bot, ← orthogonal_range, range_eq_top.2 sur]))
  have sep ϑ z (h : (gl ϑ).adjoint z.1 = 0) :=
    ker_eq_bot'.1 (equivOfDetNeZero _ (T ϑ)).ker z (by simp [compressedGramOp, h])
  refine O.heightLe_of_eq_zpow_mul (.mul (y := fun ι ↦ u ((θ ι).powTwist j) / u 1) ⟨_, _,
    (_ : ℕ) * (D.r * β), T 1, d _ ▸ norm_det_compressedGramOp_arch_le (sep 1)
    (fun | ⟨_, y, rfl⟩ => tst 1 y) rfl S, fun ι ↦ ?_, .of_forall
    fun _ ↦ by simp [← mul_sum]; grw [g]; simp⟩ ((heightLe_inv_heckeValueProd_div O j).pow _))
    (by rw [← mul_add, ← mul_add]; gcongr; simpa [mul_sub, add_sub] using D.le_of_hasLogBound) fun ι
    n ↦ ⟨0, by
    have := div_ne_zero_iff.1 n; simp [← (H _).2, field, div_pow, V 1, *]
    erw [V ((θ ι).powTwist j)]; simp; ring⟩
  exact mul_div_cancel₀ _ (T 1) ▸ d _ ▸ norm_det_compressedGramOp_padic_le (sep _)
    (fun | ⟨_, y, rfl⟩ => tst _ y) ι (int _ · _ · (O.1 ι)) (g' ι).1
end Data
end

section
/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: An auxiliary pair with apt labels c gives a `BaseLevel` of forms containing the image of
the idempotent of c. -/
seal Finset.univ Finset.sum Finset.prod

open Space

attribute [-simp] Set.Sum.elim_range

attribute [local simp] Finsupp.sum MonoidAlgebra.lift_apply Representation.asAlgebraHom_def
  twistedLabel

/-- For apt c and auxiliary Q, some `BaseLevel` over the integers of ℚ̄_ℓ contains im e_c, with
Mk·e_c preserving integrality (Mk = `Data.chosenGroupOrder`, e_c = `tupleProj`);
its eigensystems at finite levels u off `badPlaces` D ℓ give
normalised representations R that are `IsLabelledColumn` of one jump type, with (R − a)(R − 1) = 0
on inertia above Q ∪ Q̄, a the avatar of ϑ⁻¹. -/
lemma exists_baseLevel {ℓ} [ThePrime ℓ] [PadicIso ℓ] {P} {D : Data P} {r n} [Fintype r] [Fintype n]
  {O : AuxPair _ r n} [Nonempty n] {ϑ c} (h : IsApt O c ϑ) (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) :
  ∃ J, ∃ B : BaseLevel _ _ D.chosenGroupOrder, (∀ y ∈ (tupleProj O c).range, y.toSmoothForm ∈
  B.formsOfLevel ![]) ∧ (∀ y, y.toSmoothForm ∈ BaseLevel.ellIntegralForms → D.chosenGroupOrder •
  (tupleProj O c y).toSmoothForm ∈ BaseLevel.ellIntegralForms) ∧ ∀ K [Finite K] u,
  (∀ k, u k ∉ badPlaces D ℓ) → ∀ x ∈ B.Eigensystem (J := K) u, let R := normalisedRep O x.galRep;
    IsLabelledColumn O O.rankDiff J (twistedLabel O c · * (.X - 1) ^ O.rankDiff) (.conjClosure ϑ.Q ∪
    (Set.range u).conjClosure) R ∧ ∀ g ∈ inertiaAbove (.conjClosure ϑ.Q),
    ((R g).1 - ϑ.invAvatar g • 1) * ((R g).1 - 1) = 0 := let π :=
    ((stdSpace _ n).formTranslation (O.κ, O.detExp)).comp (Gf.componentOn n O.places.toFinset)
  have hπ {k} (h : k ∈ Gf.supportedOn n O.places) : π k = formTranslation _ _ k :=
    congrArg (formTranslation ..) (Gf.ext (by simp_all))
  let ρ := (O.chosenGLRep π).asAlgebraHom (tupleIdem r c)
  have hρ u := (show (ρ u).1 = _ by simp [ρ, AuxPair.chosenGLRep, levelRep]; rfl :)
  let j (y : O.FormV) : levelSpace π _ O.levelChar := ⟨y.toSmoothForm, fun k ↦
    congr(⟨$(levelSpace_levelOf_apply y.2 ⟨_, Gf.componentOn_mem_Kf (levelOf_le_Kf k.2)⟩ _ (funext
    fun j ↦ (Kf.reduceAt _).div_mem_ker_iff.1 (Kf.reduceAt_eq_one_of_atPlace (by simp)))), _⟩)⟩
  have hj y : (ρ (j y)).1 = (tupleProj O c y).toSmoothForm := by
    simp [hρ, tupleProj, AuxPair.groupAlgAction, hπ (liftResidue_mem_supportedOn _)]; rfl
  ⟨_, (⟨_, (ρ.eqLocus 1).map (Submodule.subtype _), fun T hT _ ⟨u, e, a⟩ ↦
    a ▸ ⟨⟨_, map_mem_levelSpace_of_commute u.2 (hT ⟨_, levelOf_le_Kf ·.2⟩)⟩, Subtype.ext (by
    simpa [hρ, π, ← Module.End.mul_apply, (hT _).eq, -Set.coe_toFinset, -Set.toFinset_range] using
      congr(T $e)), rfl⟩, ⟨_, _, isOpen_levelOf, Submodule.map_subtype_le ..⟩,
    D.card_classAut_dvd_chosenGroupOrder h.card_le le_rfl⟩ : BaseLevel ..), fun y m ↦ ⟨⟨j y,
    Subtype.ext ((hj y).trans congr($(IsApt.tupleProj_eq_self_of_mem_range m).toSmoothForm)), rfl⟩,
    fun k ↦ .trans congr(⟨$(y.algFormRep_eq_self_of_mem
    (inf_trivialOn_le_levelOf ⟨Gf.componentOn_mem_Kf (levelOf_le_Kf k.2), by simp_all⟩)), _⟩)
    (one_smul ..).symm⟩, fun y hy x m ↦ (h.1 ▸ D.card_GL_dvd_chosenGroupOrder (h.rank_le.1.trans
    D.nat_le_of_hasLogBound) : .card (O.ChosenGL r) ∣ D.chosenGroupOrder).elim fun t e
    i ↦ by simpa [← hj, hρ, e, Finset.mul_sum, mul_assoc, mul_left_comm _ (t :
    ℂ)] using! (sum_mem fun g _ ↦ mul_mem (by simp) (mul_mem (norm_le_one_of_isIntegral ιℓ.toRingHom
    ((isCentralProj_tupleIdem c).isChar.isIntegral g)) (mul_mem
    (ιℓ.toRingHom.isOfFinOrder (O.isOfFinOrder_prod_psi_det g)).norm_eq_one.le
    (hy _ (mul_mem m (Kf_le_localLevel (Gf.componentOn_mem_Kf (by simp)))) i)))), by
  rintro _ _ U hX x ⟨_, ⟨b, hf⟩, h₀⟩
  obtain ⟨⟨u, a, rfl⟩, he, hR⟩ := hf.1, x.isEigenform b h₀, x.attached_galRep b h₀
  have A j k := hπ (Gf.supportedOn_mono (by simp) (atSplit_mem_supportedOn (O.apart.2 j j) k))
  set_option backward.isDefEq.respectTransparency false in
    refine ⟨by simpa using! ((isLabelledColumn_of_hasProductLabel h u.1.2 he hR (fun v m k
      g ↦ congr($(And.elim levelSpace_le_sphericalAt (by simp; clear * - m k hX h hQ; grind [(h.1 ▸
      Subtype.range_coe : Set.range O.twistPlace = ϑ.Q)]) (BaseLevel.formsOfLevel_le_levelSpace hf)
      g))) fun i ↦ HasParahoricType.hasProductLabel ((forms ..).subtype.domRestrict _) (by simp)
      (a.trans_ne (h₀ ∘ congrArg _) <| piTensorElem_apply_eq_zero i ·)
      (D.hasParahoricType_chosenGLRep (A (.inl i) · ▸ rfl)) (.of_lt_imp_ne (by simp))
      (by simpa using h.isLabel_twistedLabel i)).twist_avatar (.inv (μ := O.a)) _ _ (by
      clear * -; grind only [O.rank_lt]) h (by simp)), normalisedRep_quadratic_on_inertia h hQ he hR
      fun i ↦ ⟨?_, fun k _ a _ ↦ congr($(A _ _ ▸ levelSpace_levelOf_apply u.2 _ ⟨_,
      (Subgroup.mulSingle_mem_pi ..).2 fun _ ↦ (mem_rangeParabolic_iff _).2 fun _ _ _ ↦
      a ?_⟩ (reduceFamily_atSplit ..)).1).trans ?_⟩⟩ <;> open Calc in simp +contextual [*,
      AuxPair.auxLevelChar, Fintype.prod_eq_single i, MulChar.one_apply, ite_eq_iff]
    rw [← Matrix.det_submatrix_equiv_self (O.incl.toEquivRange.trans (.subtypeEquivProp
      (by open Calc in simp)))]; rfl⟩
end

section
/-! Strings of roots of Hecke polynomials, from the eigenvalue 1 of a Galois representation.

Part of: Ties hold on forms and weak lifts do not move (see New.Patching.OnePrimeTie).

This file: Weak lifts: Hecke polynomial is the string times a factor integral after normalising. -/


open Matrix Polynomial Fintype ComplexOrder IsUltrametricDist NormedField
variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {r n} [Fintype n]

/-- Let B be monic, C integral, AB ≡ C ≡ A'B coefficientwise modulo the maximal ideal of the
integers of ℚ̄_ℓ, and ‖A'(1)‖ ≥ 1. Then A divides an integral polynomial e with e(1) = 1. -/
lemma exists_integral_multiple_eval_one {A A' B C : (PadicAlgCl ℓ)[X]} (m : B.Monic) (z :
  ∀ i, ‖C.coeff i‖ ≤ 1) (a : ∀ i, ‖(A * B - C).coeff i‖ < 1) (h : ∀ i, ‖C.coeff i - (A' * B).coeff
  i‖ < 1) (u : 1 ≤ ‖eval 1 A'‖) : ∃ e, A ∣ .map (intQpBar ℓ).subtype e ∧ e.eval 1 = 1 :=
  have v : 1 ≤ ‖A.eval 1‖ := by
    grw [← sub_add_cancel A' A, eval_add, norm_add_le_max, eval_eq_sum_range,
      (exists_norm_finsetSum_le ..).choose_spec.2, norm_mul, norm_coeff_le_of_mul_monic m
      (le_supNorm _), (exists_eq_supNorm _).choose_spec, sub_mul, ← sub_add_sub_cancel _ C,
      coeff_add, norm_add_le_max] at u; simp_all [norm_sub_rev (C.coeff _), not_le_of_gt]
  ((A * .C (A.eval 1)⁻¹).lifts_iff_coeff_lifts.2 (by simp [← NNReal.coe_le_coe,
    field, norm_coeff_le_of_mul_monic
    m (by grw [← sub_add_cancel (A * B), coeff_add _ _ ·, norm_add_le_max, a, z, max_self,
    v])])).imp fun e he ↦ ⟨⟨_, he⟩, by simpa [norm_pos_iff.1 (by bound)] using congr(eval 1 $he)⟩

/-- Let T be a continuous function from the Galois group to n × n matrices, T(δ_i) = y^i A, and
y^j − 1 a unit for 1 ≤ j ≤ 4n + 2. For some i, ‖det(1 − T(φ))‖ ≥ 1 for all φ near δ_i. -/
lemma exists_eventually_no_eigenvalue_one {T : AbsGal D → Matrix n n (PadicAlgCl ℓ)} (c : Continuous
  T) (δ : ℕ → _) {y : PadicAlgCl ℓ} {A} (h : ∀ i, T (δ i) = y ^ i • A) (hy : ∀ j ∈ Set.Icc 1
  (4 * card n + 2), ‖y ^ j - 1‖ = 1) : ∃ i, ∀ᶠ φ in nhds (δ i), 1 ≤ ‖(T φ).charpoly.eval 1‖ := by
  by_contra! a
  simp_rw [eval_charpoly, ← mem_ball_zero_iff] at a
  have (i : Fin (card n + 1)) H := a i ((isClosed_ball ..).preimage_of_continuous.compl_mem_nhds
    (by simpa [h] using! ((congrArg valuation (det_aeval_neg_eq_prod_roots (-A)
    (1 - y ^ i.1 • .X))).trans (map_multiset_prod ..)).trans_ge (Multiset.one_le_prod H)))
  choose z μ m H using by simpa using this
  refine z 0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (.of_lt_imp_ne fun i j a e ↦
    (valuation.map_sub_lt (H j) (H i)).ne ?_) m (by simp))
  simpa [e, mul_assoc, ← sub_one_mul, NNReal.eq_iff, hy (j - i) (by grind), ← pow_sub_mul_pow
    y a.le] using valuation.map_one_sub_of_lt (H i)

variable [PadicIso ℓ] [Fintype r] [Nonempty n] {O : AuxPair D.E r n} {x : Isotypic (stdSpace _
  n) (O.κ, O.detExp)} {f} (hf : f ∈ x.1) (h₀ : f ≠ 0) (h : ∀ g,
  (normalisedRep O x.galRep g).1.charpoly.IsRoot 1)
include hf h₀ h

/-- Let every g have eigenvalue 1 on the normalised representation of the eigenform f. At a
split w ∤ ℓ of prime norm q where f has Hecke polynomial S, the numbers ν q^i, i < n − r,
are roots of S, ν = `AutChar.frobValue` of `AuxPair.a`. -/
lemma isRoot_hecke_string {w hw S i} (hℓ : ↑ℓ ∉ w.1) (hS : HasHeckePolyAt f.1 w hw S) :
  i < O.rankDiff → S.IsRoot (O.a.frobValue r w * w.q ^ i) := by
  obtain ⟨⟨s, b⟩, y, _, e, a⟩ := w.isPlaceOver_placeOver.exists_isFrob (AbsGal D),
    hasHeckePolyAt_iff_localFormRep.1 hS
  exact isRoot_string_of_norm isUnitary_localFormRep y h₀ e a (.of_map (by
    simpa [↓chiOneInv_spec w.isPlaceOver_placeOver hℓ 1, b] using
      isRoot_of_isRoot_charpoly (P := comp _ ((chiOneInv O s⁻¹).1⁻¹ • .X)) (by
    simpa [aeval_comp, Units.smul_def] using (((sphericalCompat_std w f.2 (x.isEigenform hf h₀)).2
    (x.attached_galRep hf h₀) hS.1 _ w.isPlaceOver_placeOver).2.2 _ _ hS s⁻¹ b).1
      (w.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hℓ)) (h s⁻¹))
    ιℓ.toRingHom.injective) (by simp [AutChar.frobValue, sq, ← mul_pow, ← pow_add, O.rank_lt.le])

/-- Let the normalised representation u of an eigenform have integral characteristic polynomials,
all with root 1. At generic geometric Frobenii σ (`mostFrobenii`): if char
u(σ) ≡ S·∏_{i<n−r}(X − cyc(σ)^{−i}) with ‖S(1)‖ ≥ 1, the rescaled Hecke polynomial is
∏_{i<n−r}(X − q^i)·T, and ιT divides an integral e with e(1) = 1. -/
lemma eventually_heckePoly_eq_string_mul (z : ∀ g i, ‖(normalisedRep O x.galRep g).1.charpoly.coeff
  i‖ ≤ 1) : ∀ᶠ y in mostFrobenii _, ∀ S, 1 ≤ ‖eval 1 S‖ → (∀ i, ‖(normalisedRep O x.galRep
  y.frob).1.charpoly.coeff i - coeff (S * ∏ i ∈ .range O.rankDiff, (X
  - C (cycInv ℓ _ _ y.frob ^ i))) i‖ < 1) → ∃ e, HasRootString (x.heckePolyAt y.w) (.map (algebraMap
  EllAdicIntegers _) e) y.w.q (ιℓ.symm (chiOneInv O y.frob).1)⁻¹ O.rankDiff ∧ e.eval 1 = 1 := by
  filter_upwards [(x.attached_galRep hf h₀).2.2.2 _ one_half_pos, eventually_mostFrobenii
    ((x.isEigenform hf h₀).2.and (eventually_notMem_star_notMem ℓ ∅))] with w a ⟨k, _, _, l⟩ _ b e
  refine (Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C (pow_right_strictMono₀ (by
    simp)).injective).set_pairwise _)
    (by simpa [chiOneInv_spec w.isPlaceOver l 1, w.isFrob, ↓dvd_iff_isRoot] using (fun
    _ ↦ isRoot_hecke_string hf h₀ h l (k w.prime_q).2))).elim fun T y ↦
    (exists_integral_multiple_eval_one (A := chiOneInv O w.frob ^ card n • 1 * T.map ιℓ)
    (monic_prod_X_sub_C ..) (z _) (fun i ↦ ?_) e b).imp fun _ : (intQpBar ℓ)[X] ↦ .imp_left (⟨T,
    y, by simpa [Polynomial.map_map] using! map_dvd (mapEquiv ιℓ.symm) <| dvd_of_mul_left_dvd ·⟩)
  generalize x.heckePolyAt _ = H at *
  by_cases! i ≤ card n <;> simpa [‹_›, cycInv_eq_of_isFrob w l, pow_sub₀, Units.smul_def, ← mul_sub,
    ← by simpa [Polynomial.map_prod, mul_comm _ T] using congr(mapEquiv ιℓ $y), norm_sub_rev,
    charpoly_smul_coeff, coeff_eq_zero_of_natDegree_lt, mul_assoc, mul_comm (ιℓ _),
    norm_eq_one_of_continuous, AlgHeckeChar.continuous_avatar] using
    (a _ rfl i).trans_lt one_half_lt_one
end

section
/-! Part of: Triangular Taylor–Wiles primes controlling the even classes (see
New.Selmer.TrianglePrimes).

This file: A value of an even class vanishes if all its cyclic images vanish. Odd Kummer-type maps
with reciprocity law against even classes, primitive, with prescribed zeros. -/

/-- Let c lie in `evenClasses` for the twist −e modulo ℓ^r. If b is killed by every additive
map u to ℤ/ℓ^r for which u∘c is a continuous cocycle for cyc^{−e}, then b = 0. -/
lemma eq_zero_of_mem_evenClasses {ℓ} [ThePrime ℓ] {E} [Field E] [UnramCMField E] {O S r e b c} (k :
  c ∈ evenClasses (E := E) O S r e) (h : ∀ u : _ →+ ZMod (ℓ ^ r),
  (u <| c ·) ∈ Z1 (charRep _ (cycCharMod Ω (ℓ ^ r) ^ e)⁻¹) → u b = 0) : b = 0 :=
  QZ.eq_zero_of_forall_hom_eq_zero ((QZ.bijective_ofZMod_comp (funext <| nsmul_quot_eq_zero ∘' ·)
  ).2.forall.2 fun u ↦ by simp [h u ⟨(k.1.2.comp _).continuous, by simp [tateTwist, cycInv, charRep,
  CharP.cast_eq_zero, ↓← map_pow, ← map_inv, mem_selmerModule_iff.1 k.1, map_cycChar_smul u r]⟩])

open Classical Finset Function NumberField selmerZ1 Subgroup IsCMField
variable {ℓ} [ThePrime ℓ] {E : Type} [Field E] [UnramCMField E] (r : ℕ) (w : FinPlace E)

/-- A triple (w, A, σ): w a place of prime norm not above ℓ, A a place of Ω over w, σ a
geometric Frobenius at A fixing μ_{ℓ^r}. -/
def IsSplitPlace (x : FrobeniusDatum E) := ↑ℓ ∉ x.w.1 ∧ cycCharMod Ω (ℓ ^ r) x.frob = 1

/-- The prime of the maximal real subfield E⁺ below w. -/
noncomputable abbrev primeBelowPlus := w.below (maximalRealSubfield E)

/-- A locally constant z with values in ℤ/ℓ^r, on the kernel of cyc mod ℓ^r an odd homomorphism
of twist e + 1, with a reciprocity law off the finite set T bounding the ramification of
even cocycles of twist −e that vanish on Φ. -/
structure IsLaw e (Φ : Set _) (T : Finset _) (z : Gal(Ω/E) → ZMod (ℓ ^ r)) where
  isLocallyConstant : IsLocallyConstant z
  map_conj_mul g a b : cycCharMod Ω (ℓ ^ r) a = 1 → cycCharMod Ω (ℓ ^ r) b = 1 →
    z (g * a * g⁻¹ * b) = cycCharMod Ω (ℓ ^ r) g ^ (e + 1) * z a + z b
  odd b : cycCharMod Ω (ℓ ^ r) b = 1 → z (conjGal b) = -z b
  reciprocity {J : Type} [Fintype J] (x : J → _) : Injective (primeBelowPlus <| x · |>.w) → (∀ j,
    IsSplitPlace r (x j) ∧ primeBelowPlus (x j).w ∉ T) → ∀ j, (∀ i ≠ j, z (x i).frob = 0) → ∀ O,
    ∀ c ∈ evenClasses O (.range (x · |>.w)) r e,
    (∀ g ∈ Φ, c g = 0) → ∀ n : ℕ, 2 * z (x j).frob ∣ n → n • c (x j).isPlaceOver.tameGenerator = 0

lemma primeBelowPlus_star : primeBelowPlus (star w) = primeBelowPlus w := by
  ext x; exact congr($(Subtype.ext (mem_maximalRealSubfield_iff_star_eq.1 x.1.2)) ∈ w.1)

/-- Let E be stably unramified with ≥ 4 infinite places, r ≥ 1. Given Frobenii x_i fixing μ_{ℓ^r},
at degree-one places off ℓ over distinct primes of E⁺, and at most as many y_i, some function z with
`IsLaw` kills all y_i and takes a unit value on an element fixing μ_{ℓ^r}. -/
lemma exists_isLaw {r} e (hr : 0 < r) (hf : 4 ≤ Fintype.card (InfinitePlace E)) {I k}
  [Fintype I] (hI : k ≤ Fintype.card I) {x : I → FrobeniusDatum E} (hx : ∀ i, IsSplitPlace r (x i))
    (i : Injective (primeBelowPlus <| x · |>.w)) (y : Fin k → _) : ∃ z T, IsLaw r e (.range
  (x · |>.frob)) T z ∧ (∀ i, z (y i) = 0) ∧ ∃ g, IsUnit (z g) ∧ cycCharMod Ω (ℓ ^ r) g = 1 := by
  let K := maximalRealSubfield E
  let res : Gal(Ω/E) →* _ := AlgEquiv.restrictScalarsHom (maximalRealSubfield E)
  let c₀ : Gal(Ω/maximalRealSubfield E) := {cmConj with commutes' x :=
    (mem_maximalRealSubfield_iff_star_eq.1 x.2 ▸ cmConj_algebraMap x.1 :)}
  obtain ⟨⟨⟨⟨ce, ij⟩, _⟩, -, ix⟩, cs : IsComplexConj c₀, -, op⟩ := (@is_quadratic E _ _ _).2 ▸
    isClosedEmbedding_galois_restrict res, isComplexConj_cmConj,
    isOpenEmbedding_galois_restrict res (by tauto)
  have N c (h : IsComplexConj c) :
    c ∉ res.range | ⟨s, e⟩ => (e ▸ h).false_of_isTotallyComplex (c := s)
  choose p o using fun σ ↦ show ite (σ ∈ res.range) σ (σ * c₀) ∈ res.range by
    split <;> simp [mul_mem_iff_of_index_two, *]
  obtain ⟨cp, _, p1⟩ := ce.continuous_iff.2 ((continuous_congr o).2 (continuous_id.if
    (op.frontier_eq ▸ by simp) (by fun_prop))), normal_of_index_eq_two ix,
    (ij <| (o _).trans <| ite_eq_left ⟨·, rfl⟩)
  have μ g h : p (g * h) = p g * p h ∨ p (g * h) = p g * conjGal (p h) := by
    simp only [← ij.eq_iff, map_mul, mul_mem_iff_of_index_two, *,
      show res (conjGal (p h)) = c₀ * res _ * c₀ from rfl]; grind [cs.mul_self]
  have u W g : g ∈ inertiaAbove W → p g ∈ inertiaAbove (primeBelowPlus ⁻¹' W) := fun ⟨v, a, A, hA,
    h⟩ ↦ by
    obtain ⟨⟨w, hw, rfl⟩, e⟩ := hA.exists_above (L := E), o g; split at e; exact ⟨w, a, A, hw,
      (e ▸ h :)⟩
    cases StablyUnram.exists_isUnit_sub_star.elim fun y u ↦ w.1.notMem_of_isUnit u ((hw _).1 (by
      simpa [← (by simpa [res, c₀] using congr($e (algebraMap E Ω y)) :)] using
        h.2 _ (A.valuation_le_one ⟨_, algebraMap_ringOfIntegers_mem A (star y)⟩)))
  let κ := MonoidHom.mk' (cycChar Ω ℓ ∘ p) (by cases μ · · <;> simp [*])
  have hu g h : κ g = 1 :=
    cycChar_eq_one_of_mem_inertiaAbove (by simpa using! u (placesDividing _ ℓ)ᶜ g h)
  let ρ := (Units.map (PadicInt.toZModPow r).1).comp κ
  let V := OpenNormalSubgroup.mk ⟨res.range ⊓ (cycCharMod Ω (ℓ ^ r)).ker,
    op.inter isOpen_ker_cycCharMod.1⟩
  have U s (h : cycCharMod Ω (ℓ ^ r) s = 1) : res s⁻¹ ∈ V := ⟨⟨_, rfl⟩, by simpa⟩
  have v : V ≤ ρ.ker | _, ⟨⟨s, rfl⟩, h⟩ => by simpa [ρ, κ, *, cycCharMod_prime_pow_eq] using! h
  have D (x : FrobeniusDatum E) : IsFrob x.valRing (primeBelowPlus x.w).q (res x.frob⁻¹) :=
    ((x.prime_q.pow_eq_iff.1 ((primeBelowPlus x.w).1.absNorm_pow_inertiaDeg _)).1 ▸ x.isFrob :)
  obtain ⟨⟨S, hS⟩, hm, l, w⟩ := (placesDividing _ ℓ ∪ .range (primeBelowPlus <| x
    · |>.w)).toFinite.exists_finset, dvd_pow_self ℓ hr.ne', @NeZero.one_le ℓ _, isOpen_mono v V.1.2
  choose P hP η Φ using fun u : FinPlace _ ↦ show ∃ A, IsPlaceOver A u ∧ (u ∈ S → u ∉ placesDividing
    _ ℓ → ∃ i, IsFrob A u.q (res (x i).frob⁻¹)) from if h : ∃ i, primeBelowPlus (x i).w =
    u then h.rec fun i e ↦ e ▸ ⟨_, (x i).isPlaceOver.isPlaceOver_below, by tauto⟩ else ⟨_,
    u.isPlaceOver_placeOver, by simp +contextual [*]⟩
  let M := DiscreteModule.of (charRep (ZMod (ℓ ^ r)) (ρ ^ e)⁻¹)
    (((Continuous.of_isOpen_ker _ w).pow e).inv.fst'.smul continuous_snd)
  generalize m : M = A
  have t {g} (h : ρ g = 1) : A.ρ g = 1 := m ▸ by ext; simp [M, charRep, h]
  have t' {g} (h : κ g = 1) := @t g (by simp [ρ, h])
  have L (B := A) (r : ∀ {g}, A.ρ g = 1 → B.ρ g = 1) u (h : u ∈ S) : (d0 (B.restrictTo (decompGroup
    _ (P u))).ρ).range ≤ .pi {g | ↑ℓ ∈ u.1 → κ g = 1} ⊥ := fun _ ⟨m, J⟩ ↦ J ▸ fun g a ↦
    sub_eq_zero.2 congr($(r (if b : _ then t' (a b) else t ((hP _).decompGroup_le (Φ u h b) w
    (by simp [ρ, hu · ⟨u, b, _, hP u, ·⟩]) (v (U _ (hx _).2)) g.2))) m)
  have hu' g (h : g ∈ inertiaAbove Sᶜ) := t' (hu g (h.imp (by simp +contextual [hS])))
  have C c (h : IsComplexConj c) := t' (by simp [IsComplexConj.cycChar_eq_neg_one, *] :
    cycChar Ω ℓ (res (p c)) = 1)
  have c := exists_split_primes_relations hu' hP _ (L A id) @C A V (congr($(t <|
    @v · ·) ·)) (fun _ ↦ (·.2)) (N _ · ·.1)
  extract_lets Y at c
  choose q ι _ Q _ s γ π T hT hST hπ _ d H using c
  let Z := (smulAddHom _ (Y (.range s.v)) ℓ).ker
  -- the count of the `ℓ`-torsion cocycles; for it the module `A = M` is kept abstract
  have B : .card Z * ℓ ^ (k + 1) ≤ ℓ ^ Fintype.card ι := by
    let W := A.submodule (ℓ • LinearMap.id).ker fun g a h ↦ by simpa using congr(A.ρ g $h)
    obtain ⟨_, hM⟩ : Finite W ∧ .card W = ℓ := by subst m; use inferInstance,
      (IsAddCyclic.card_nsmulAddMonoidHom_ker ..).trans (by simp [M, Nat.gcd_eq_right hm])
    have r {g} (h : A.ρ g = 1) : W.ρ g = 1 := by ext; simp [W, h]
    let ψ := ((DistribMulAction.toAddAut _ W).comp W.ρ.asGroupHom).prod (cycCharMod Ω ℓ)
    have u : V ≤ ψ.ker
      | _, h => Prod.ext (by ext; exact congr($(r (t (v h))) _)) (cycCharMod_eq_one_of_dvd hm h.2)
    let O := OpenNormalSubgroup.mk ⟨_, isOpen_mono u V.1.2⟩
    have G {D : Subgroup _} [IsClosed (SetLike.coe D)] := exists_procyclic_generator (κ.domRestrict
      D) ((continuous_cycChar ℓ).comp cp |>.comp continuous_subtype_val)
      (four_dvd_cycChar_sub_one <| p ·)
    obtain ⟨γ, hγ⟩ := @G _ O.isClosed
    choose v n _ B R φ Q X _ using fun g : O × _ ↦ chebotarev (V.1.2.preimage (continuous_const_mul
      g.1.1)) ⟨g.1⁻¹, by simp⟩ (((finite_natCast_mem q).union (Set.finite_range s.v)).insert g.2)
    let t := (cond · (γ, ofNonempty) (dite _ (⟨c₀, ·⟩) fun _ ↦ 1, v (γ, ofNonempty)))
    simp [-Prod.forall] at n
    let s' : SplitPlaces ℓ q _ O _ := ⟨fun _ h ↦ congr($h.2), hm.trans s.dvd_level, _, s.4.sumElim
      (Bool.injective_iff.2 (n (t _)).1) (by simp [n]), by simp [s.level_notMem, n],
      Sum.rec s.valRing (B ∘ t),
      Sum.rec s.isPlaceOver (R ∘' t), Sum.rec s.φ (φ ∘ t), Sum.rec (s.isFrob · |>.imp id (u ·))
      fun _ ↦ ⟨X _, (mul_mem_cancel_left (by simp)).1 (u (Q _))⟩, by congr!, (s.inertiaGroup_le
      · · |>.trans u), fun F _ h ↦ s.principal_sup_idelesUnitOff F (@h · · <| inclusion u ·)⟩
    have c : W.FiniteKilledFixedInj ℓ O 1 0 := ⟨‹_›, by simp [← hM], fun _ h ↦ (congr($h.1 ·)),
      fun _ _ ↦ by simp⟩
    have B := (card_mul_pow_le (r <| hu' · ·) hP _ (L W r) (r <| C _ ·) s'
      (s'.card_trivialised_of_isHigmanProjective c (c.isHigmanProjective_of_coprime (.of_dvd_right
      (index_ker ψ ▸ card_subgroup_dvd_card _) (by simp [← sq, l, ← Nat.card_congr
      (MulAutMultiplicative W).1, Nat.totient_prime Fact.out, (hM ▸ (isCyclic_of_prime_card (α :=
      Multiplicative W) hM).card_mulAut :)]))) fun y m f ↦ by
      let F := MulAction.stabilizer Gal(Ω/K) y.toMul
      have H : V ≤ F := d y (hm.choose_spec ▸ mul_nsmul y .. ▸ nsmul_mem (m.imp id (· <|
        inclusion u ·)) _) (f <| .inl ·)
      have e j := (mul_mem_cancel_right (f (.inr j))).1 (H (Q _))
      simpa using! hγ (F.subgroupOf _) (fun g (a : cycChar Ω ℓ (p g) = 1) ↦ by
        have b := o g ▸ U (p g)⁻¹ (by simp [a, cycCharMod_prime_pow_eq])
        split at b; exacts [H b, (F.mul_mem_cancel_right (by
          simpa [t, (mul_mem_cancel_left g.2).1 (u b)] using e false)).1 (H b)]) (isOpen_mono H
        V.1.2).preimage_val (e true)).1 hT).trans' (mul_le_mul_left (@Nat.card_le_card_of_injective
      Z _ ((finite_unramified_cocycles W).subset fun _ ↦ (·.1)) (fun x ↦ ⟨fun g ↦ ⟨_,
      congr($(x.2).1 g)⟩, x.1.2.imp (.imp (.imp (·.subtype_mk _) (Subtype.ext <| · · ·)) fun b ↦
      (Subtype.ext <| b · <| ·.imp (by simp +contextual [s']))) (.imp (Subtype.ext <| · · · · ·)
      (Subtype.ext <| · · ·))⟩) (by simp [Injective, funext_iff])) _)
    grw [S.prod_le_prod' (g := fun v ↦ ite (↑ℓ ∉ v.1) 1 (.card W)) fun v _ ↦ ?_, hM,
      card_infinitePlace_eq_card_infinitePlace, ← hf, ← S.card_filter_add_card_filter_not (↑ℓ ∉
      ·.1), ← hI.trans (card_le_card_of_injOn _ ?_ i.injOn)] at B
    simpa [prod_ite, pow_add, pow_succ, ← mul_assoc, add_right_comm _ _ 4, NeZero.pos] using B
    simp [hS, (hx _).1]
    split; simp [Pi.bot_def, *, inf_eq_left.2]
    exact G.elim fun γ hγ ↦ Nat.card_le_card_of_injective _ (.of_ker
      ((LinearMap.proj γ).domRestrict _) fun ⟨_, x⟩ ↦ Subtype.ext ∘ funext ∘
      hγ (cocycleKer (W.restrictTo _).ρ x.2.2) (x.1 · ∘ const _) (x.2.1.1 {0} (by simp)))
  subst m
  choose n a n2 j β using exists_primitive_relation (.mk' (·.1 ∘ γ) (by bound)) (π ∘ res ∘ y⁻¹) hr B
    ((finite_unramified_cocycles M).subset inf_le_left)
  obtain ⟨α, ad, law⟩ := H (.mulRight <| n ·) (a ⟨·, ·⟩)
  exact ⟨(n <| π <| res ·⁻¹), T, ⟨(hπ.comp n).comp_continuous (by fun_prop), fun g a b h h' ↦ by
    simpa [M, charRep, ρ, ↓map_inv, κ, *, cycCharMod_prime_pow_eq, pow_succ', add_comm] using!
      ad (res g) _ (U b h') _ (U a h) 1, fun b h ↦ by
    simpa [by simpa using (ad 1 1 · 1 · 1), *, cs.cycCharMod_eq_neg_one, ← map_inv
      conjGal, -map_inv, inv_eq_iff_mul_eq_one.2 cs.mul_self] using! (ad c₀ 1 V.one_mem _ (U b
      h) 1), fun w i h j z O c Z φ _ ⟨y, b⟩ ↦ eq_zero_of_mem_evenClasses Z fun f ⟨l, fs⟩ ↦ by
    obtain ⟨⟨⟨h1, h2, -⟩, h3, h4⟩, F⟩ := Z.imp mem_selmerModule_iff.1 id,
      (w · |>.isPlaceOver.isPlaceOver_below (K := K))
    choose δ hδ using exists_isTameGeneratorFor Gal(Ω/K) (ℓ ^ r) ∘' F
    let X : Z1 M.ρ := ⟨_, l.comp cp, (by cases μ · · <;>
      simp [M, charRep, ρ, κ, *, -h1, cycCharMod_prime_pow_eq])⟩
    have x4 g a : (X + X).1 g = 0 := h2 _ ((u (placesDividing _ ℓ ∪ .range (primeBelowPlus <|
      w · |>.w))ᶜ g a).imp fun _ ↦ .imp (mt (by
      clear * -; simp [placesDividing]; grind only [primeBelowPlus_star])) id) |> (by simp [X, ·])
    choose m hm using (hδ j).exists_apply_eq_nsmul (F j) (by simp [(w j).w.2.pow_mem_iff_mem, *,
               (h j).1.1]) (τ := res _) (w j).isPlaceOver.tameGenerator.2 X.1 (X.2.1.1 · ⟨⟩)
      (by simp [X.2.2, t' <| hu · ⟨_, by simp [placesDividing, (h j).1.1], _, F j, ·⟩])
    have := (law _ _ _ δ i (⟨(h _).2, F _, hδ ·, D _, U _ (h _).1.2⟩) _ ⟨⟨(X + X).2, (x4 · <|
      ·.imp (by simp +contextual [hS]))⟩, fun u a ⟨g, d⟩ b ↦ if c : _ then by
      simpa [X, t' (b c), h4 (p (g * g)) ⟨_, (hP u).valuation_natCast_lt_one_iff.2 c,
        ((o _).trans (ite_eq_left (mul_self_mem_of_index_two ix g)) ▸ mul_mem d d :),
          κ.ker.mul_mem (b c)
        (b c)⟩] using (X.2.2 g g).symm else DiscreteModule.Z1.eq_zero_on_decompGroup _ (hP u) (Φ u a
      c) (x4 · ⟨u, (·.elim c fun ⟨j, e⟩ ↦ (h j).2 (e ▸ hST a :)), _, hP u, ·⟩) (by simp [X, *,
      cocycle_apply_inv h1, -map_inv]) g d, fun g h ↦ by
      simpa [C g h, h.mul_self ▸ X.2.2 g g] using X.2.2 1 1⟩).symm.trans
      (Fintype.sum_eq_single j (by simp [z · ·, -map_inv]))
    simp [X, p1] at this hm; simp [↓map_nsmul, b, hm]
    linear_combination -m * y * this⟩, n2, (s.isFrob j).2.elim fun ⟨g, e⟩ a ↦
    ⟨g⁻¹, by simpa [e, β] using congr(IsUnit ($(α j) 1)), by simpa [← e] using! a⟩⟩
end

section
/-! Set-up for this proof: general results applied to the objects of this proof.

Galois representations of theta lifts as an irreducible block plus a string. The Galois
representation of each eigenform in a space of theta lifts has the trace of a twisted block, with
the block in a finite set independent of the twist, plus a string of powers of the inverse
cyclotomic character, and the block-plus-string shape follows from the unramified theta
correspondence. Tame inertia at a level prime makes the block irreducible mod ℓ, as Ribet's method
needs, by the known device of metacyclic tame inertia, used here with two level primes to cover
every ℓ. Related work: Rallis, Langlands' functoriality and the Weil representation, 1982;
Khare–Larsen–Savin, Functoriality and the inverse Galois problem, 2008;
Arias-de-Reyna–Dieulefait–Shin–Wiese, Compatible systems of symplectic Galois representations III,
2015.

This file: A twist-free row gives traces of lifts; every good eigensystem has a row. -/


open Matrix Polynomial Fintype Filter Data AutChar Classical LinearMap Space Subtype Finset
variable {P} {D : Data P} {r n} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {ℓ} [ThePrime ℓ]
  (ι : PadicIso ℓ)

/-- Given an auxiliary pair O, with character μ, labels c apt for the trivial twist, and a
`IsLabelledColumn` R with system b whose shifted jumps obey `IsRowType`, there is one row T serving
every twist ϑ: forms lifting b with character μϑ satisfy `HasRow`.

Galois representations of theta lifts: irreducible block plus string. -/
lemma exists_row_for_all_twists {c} (hO : IsApt O c 1) b J R (h :
  IsLabelledColumn (m := r) O (card r) J c ∅ R) (s : ∀ g, (mostFrobeniiAt _ g).Tendsto (ιℓ <|
  b ·.w 1) (nhds (R g).1.trace)) (hJ : IsRowType D (card r) O.rankDiff fun σ ↦
  (J σ).map (· - ((card r - O.rankDiff) / 2 - cmSign σ * O.weight (.mk σ)))) : ∃ T, HasRow O b T :=
  have ⟨N', a, ha⟩ : 2 ∣ card n ∧ 2 ∣ (card r - O.rankDiff : ℤ) := by grind [IsApt]
  ⟨_, ⟨_, (h.twist_avatar O.hasWeight.inv 0 a (by grind [IsApt]) hO (hO.tame_part_eq.rec
    (by aesop))).isRow hO (by simpa [HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, cmSign,
    apply_ite, ha, sub_eq_add_neg] using hJ)⟩, @fun ϑ V _ _ S h₃ hy f U σ ↦ by
  simp [trace_eq_neg_charpoly_nextCoeff (S _).1, nextCoeff, O.rank_lt.ne_zero, TameChar.invAvatar]
  apply tendsto_nhds_unique (.congr' (mem_inf_of_left _)
    (.neg (.mul _ (U.tendsto_charpoly_coeff ..)))) (.add (.mul _ (.mul _ (s σ))) _)
  any_goals apply tendsto_mostFrobeniiAt (g := σ) _
  filter_upwards [eventually_mostFrobenii (f.2.and (eventually_notMem_star_notMem ℓ
    (.image V.placeAt ⊤))), (ϑ.hasWeight.inv.toAlgebraic 0 0).eventually_avatar_frob,
    (O.hasWeight.inv.toAlgebraic 0 a).eventually_avatar_frob] with x ⟨u, o, _, hl⟩ d d'
  choose _ z s E v using u x.prime_q
  have k T :=
    (smul_left_inj f.1).1 ((isSphericalWith_of_heckeSplit z v).2 T ▸ (hy _ ‹_› (by aesop)).2 T)
  obtain ⟨m, i, l⟩ := (u x.prime_q).2.isMonicOfDegree f.1, k 0, congr(-deriv ($(k ·)) 0)
  simp (disch := fun_prop) only [heckePolyEval, trivialHecke, smul_eq_mul, deriv_fun_mul,
    deriv_fun_finsetProd, deriv_fun_sum, deriv_fun_pow] at i l; simp [E, ← sum_mul, zero_pow_eq,
    O.rank_lt.pos, isMonicOfDegree_iff, sum_range_succ', hO.odd.1.pos] at i l m
  simp [↓d, ↓d', E, chiOneInv_spec x.isPlaceOver hl 1, x.isFrob, HasWeight.toAlgebraic,
    cycInv_eq_of_isFrob x hl, field, HeckeChar.atUnif,
    heckeCoeff, h₃, ← ha, ← i, m, AutChar.frobValue, Nat.sub_sub_self O.rank_lt.pos, l, zpow_sub₀,
    _root_.spaceChar_rankTwist N', ← map_natCast ιℓ, FinPlace.q_eq_sqrt_sq, pow_sub₀, O.rank_lt.le]
  ring⟩

/-- If the system p of Hecke eigenvalues occurs in a nonzero good form on W_m, then for 1 ≤ j ≤ m
some T is a row for the untwisted j-th auxiliary pair and p, serving all twists (`HasRow`).

Galois representations of theta lifts: irreducible block plus string. -/
lemma exists_hasRow_auxPair {p} (H : D.goodForms (D.spaceW D.m) ⊓ D.eigenPart _ p ≠ ⊥) (j :
  D.LiftIndex) : ∃ T, HasRow (D.auxPair .one j) (p ⟨·, ·⟩) T := by
  obtain ⟨⟨z, ⟨hz, hp⟩, z0⟩, d, κ, hκ⟩ := (Submodule.ne_bot_iff _).1 H,
    exists_isHCParam_of_hasGap D.hasGap_signsY_paramW
  let L := (AlgForm ..).subtype ∘ₗ ((D.spaceW D.m).toAlgForm hκ).1
  have ρ g y : L _ = rightRegular ℂ _ _ g (L y) := congr($(toAlgForm_formRep hκ ..).1)
  obtain ⟨K : L z ∈ levelSpace (rightRegular ℂ ..) D.chosenLevel, hf : _ ∈ forms _ (d, κ), c : ∀ x,
    (ResField ((auxPair ..).chosenPlace x))[X], hc, hl⟩ := by simp [← ρ, mem_levelSpace.1 z.2],
    (toAlgForm _ hκ z.1).2, D.goodTupleFamilies.exists_ne_zero_of_sum_ne_zero
    (by simpa [e₀] using ((D.isCentralProj_e₀.1.map _).mem_range_iff.1 hz).trans_ne z0)
  have E := D.isEigenform_of_hasHeckePolyAt (by simpa [L]) fun w a ↦ ⟨levelSpace_anti
    (maxCompactAt_le_levelOf a.2) K, (p ⟨w, ·⟩), rfl, fun i ↦ map_heckeSplit _ i L ▸ by
    simp [by simpa [heckeOperator, a, Subtype.ext_iff] using (Submodule.mem_iInf _).1 hp (w, i)]⟩
  obtain ⟨a, R, h⟩ := isApt_auxPair D 1 j hc, (sphericalCompat_std ofNonempty hf E).1
  apply exists_row_for_all_twists ι a
  convert isLabelledColumn_of_hasProductLabel a hf E h (fun _ _ b ↦
    levelSpace_anti (maxCompactAt_le_levelOf b) K) fun i ↦ HasParahoricType.hasProductLabel (e :=
    .refl _) (b := 0) (s := 0) (ψ := 1) (L.domRestrict _) (fun _ ↦ by simp [L])
    (hl <| piTensorElem_apply_eq_zero i ·) ⟨by simp, fun k _ _ e ↦ by
    simpa [-GeneralLinearGroup.val_det_apply] using ρ .. ▸ congr(L $(apply_liftResidue_eq _ _
      ((reduceFamily_atSplit ..).trans (congrArg _ (Units.ext e))))).symm⟩ nofun nofun
  simp
  simpa [Nat.sub_sub_self D.r_odd.pos, trace_eq_neg_charpoly_coeff, ↓card_rowIndex] using
    (h.tendsto_charpoly_coeff · D.r.pred |>.neg)
  simp [↓card_rowIndex, auxPair, AuxPair.rankDiff, jumps]
  convert isRowType_auxPair j.2 using 3 with σ q i
  have := hκ.eq_hcParameter (.mk σ) (D.basisVec q)
  simp [cmSign, apply_ite, hcParameter, diagramWeight_apply, ↓card_rowIndex] at *; clear * - this
    i; grind [Data.basisVec, paramW, decrPosition_paramW]
end

section
/-! Triangular Taylor–Wiles primes controlling the even classes. A count over the real subfield
gives reciprocity laws for even classes in Tate twists, and Taylor–Wiles primes, equally many at
every ℓ-power level, are chosen so that each new Frobenius kills the earlier laws but not the new
one, which lets the even classes be removed without any bound for them. Tame ramification governed
by Frobenius in the Kummer field of units and the inductive choice of primes at every level are
known. Related work: Gras–Munnier, Extensions cycliques T-totalement ramifiées, 1998;
Hajir–Maire–Ramakrishna, Tame Z/pZ-extensions with prescribed ramification, 2022; Taylor–Wiles,
Ring-theoretic properties of certain Hecke algebras, 1995; Darmon–Diamond–Taylor, Fermat's Last
Theorem (2.19), 1995; Dotto–Thorne, Residually reducible representations of rank 2, 2026.

This file: Taylor-Wiles primes in triangular form controlling the even classes. -/

open Function Finset Fintype Filter PadicInt WellFoundedLT Classical

/-- Let E ⊂ ℚ(ζ_N) have ≥ 4 infinite places, N + t < y, cyc(γ)^a − 1 ∣ ℓ^h for 0 < a < t, ℓ ≤ y² or
h = 0, and W contain, for all ν and g, most Frobenii near δ^(ℓ^ν)·g for some δ with cyc(δ) = 1. Then
some finite ordered J with types ty carries, for each ν ≥ 1, Taylor–Wiles places of norm ≡ 1 mod
ℓ^ν, with Frobenii in W, satisfying `IsPrimeTriangle` for γ⁻¹, yh, y²²h.

Triangular Taylor–Wiles primes controlling the even classes. -/
lemma exists_isPrimeTriangle {ℓ E} [ThePrime ℓ] [Field E] [UnramCMField E] t {N y h γ} [NeZero N]
  (hE : ∀ x, algebraMap E Ω x ∈ cycloField N) (hN : N + t < y) (hh : ∀ a ∈ Set.Ioo 0 t,
  (cycChar Ω ℓ γ ^ a).1 - 1 ∣ ℓ ^ h) (hy : ℓ ≤ y ^ 2 ∨ h = 0) (hf : 4 ≤ numInfPlaces E) {W} (hW :
  ∀ ν g, ∃ δ, cycChar Ω ℓ δ = 1 ∧ W ∈ mostFrobeniiAt E (δ ^ ℓ ^ ν * g)) : ∃ J,
  ∃ (_ : Fintype J) (_ : LinearOrder J), ∃ ty, ∀ ν > 0, ∃ Q : TaylorWilesPlaces E J (ℓ ^
  ν), IsPrimeTriangle ν Q.w (Q.frobData · |>.isPlaceOver.tameGenerator) (Q.frobData · |>.frob) γ⁻¹ t
  ty (y * h) (y ^ 22 * h) ∧ ∀ j, Q.frobData j ∈ W := by
  choose p hq R using exists_detecting_points_cocycles hE ℓ
  let g i := (γ⁻¹ * i)⁻¹ * (i * γ⁻¹)
  have hD (a : Fin t) : (ℓ ^ h) ^ 3 * ∏ k ∈ {a}ᶜ, ((cycChar Ω ℓ γ ^ a.1).1 -
      (cycChar Ω ℓ γ ^ k.1).1) ∣ ℓ ^ (y * h) := by
    grw [prod_dvd_prod_of_dvd _ (fun _ ↦ ℓ.cast ^ h) fun k n ↦ ?_, pow_mul']
    simp [card_compl, ← pow_add]; grind [pow_dvd_pow, NeZero, Fin]
    wlog H : k < a generalizing a k; grind [mem_compl, neg_dvd, _=_ neg_sub]
    erw [← pow_sub_mul_pow _ H.le, ← sub_one_mul, Units.mul_right_dvd]; grind
  have h2 a k := dvd_trans (by nth_grw 1 [← hh _ ⟨k, a.2⟩, pow_succ', ← map_pow,
    ← four_dvd_cycChar_sub_one]) (hD a)
  obtain ⟨⟨⟩⟩ := exists_wellFoundedLT p, (mostFrobeniiAt E 1).nonempty_of_neBot
  let J := {e : Fin t // 0 < e.1} ×ₗ p
  use J, inferInstance, inferInstance, ⟨_, Prod.Lex.monotone_fst⟩, fun ν hν ↦ ?_
  let κ := cycCharMod (Γ := Gal(Ω/E)) Ω (ℓ ^ ν)
  let m := (κ γ).1.valMinAbs
  -- the values of all relations at a point that fixes `μ_{ℓ^ν}`
  let H := (AddSubgroup.ofSub {v : _ → ℤ | ∃ y, κ y = 1 ∧ ∀ {d Φ T z}, IsLaw ν d Φ T z → z y = v (d,
    z)} ⟨(·.2 1 |>.cast), 1, by simp⟩ fun _ ⟨a, _, p⟩ _ ⟨b, _, q⟩ ↦ ⟨a / b, by simp [*], fun h ↦ by
    simp [← p h, ← q h, by simpa [κ, *] using h.map_conj_mul 1 (a / b) b]⟩).toIntSubmodule
  let I (j : J) := {i : Set.Iio j | i.1.1.1 = j.1.1}
  -- recursive choice of a prime `x` with a relation `z` and its exceptional set `T`
  have F j := (fix_eq (fun (j : J) f ↦ epsilon fun (x, T, z) ↦ IsSplitPlace ν x ∧ IsLaw ν j.1
    (.range fun i : I j ↦ (f _ i.1.2).1.frob) T z ∧ 2 * z x.frob ∣ ↑(ℓ ^ (y * h)) ∧
    (∀ O, ∀ c ∈ evenClasses O ∅ ν j.1, (c + c) (g j.2) = c x.frob) ∧
    (∀ i h, primeBelowPlus (f i h).1.w ≠ primeBelowPlus x.w ∧ primeBelowPlus
    x.w ∉ (f i h).2.1 ∧ (f i h).2.2 x.frob = 0) ∧ primeBelowPlus x.w ∉ T ∧ x ∈ W) j).symm
  generalize fix (α := J) _ = f at F
  replace F := fix fun j p ↦ F j ▸ epsilon_spec (by
    choose h₁ hz _ _ h₃ _ using (SetCoe.forall' (s := .Iio j)).1 p
    -- the next relation `r`, and a point `u` where the earlier ones vanish and it does not
    let B := Module.finBasis ℤ (H.map (.funLeft _ _ fun i : I j ↦ (↑j.1, (f i).2.2)))
    choose v hv hb using (B · |>.2); choose y hy k using id hv
    choose _ T₀ r hk w U hw using exists_isLaw j.1 hν hf (I := I j) (.trans
      (Submodule.finrank_le _) (by simp)) (h₁ ·) (.of_lt_imp_ne (by simp +contextual [h₃])) y
    have n : (·.2 w |>.cast) ∈ H := ⟨w, by simpa⟩
    choose c A using B.mem_submodule_iff'.1 ⟨_, n, rfl⟩
    have ⟨u, hu, L⟩ := prod_induction (s := {j.1.1}ᶜ) (fun a (d, _) ↦ (m ^ d - m ^ a.1) * m) (∀ v ∈
      H, · * v ∈ H) (by simp +contextual [mul_assoc]) (by simp) (fun a _ _ k@⟨b, B, q⟩ ↦ (zsmul_mem
      k (-m ^ (a.1 + 1))).rec fun a ⟨A, p⟩ ↦
      ⟨_, by simp [*], fun k ↦ (k.map_conj_mul γ b a B A).trans
      (by simp [p k, q k, m]; ring)⟩) _ (sub_mem (H.sum_smul_mem (t := univ) c fun j _ ↦ hv j) n)
    have h₄ (i : Set.Iio j) : (f i).2.2 u = 0 := by by_cases i.1.1.1 = j.1.1 <;> simp [L (hz i),
      prod_eq_zero (i := i.1.1.1), I, (by simpa [← hb] using congrFun A ⟨i, ·⟩), *]
    choose δ hδ V using hW _ _
    -- additive functions at the element that the next Frobenius approximates
    have Y (f : _ → ZMod (ℓ ^ ν)) n (hf : ∀ a b, κ a = 1 → κ b = 1 → f (a * b) = f a + f b) :
        f (δ ^ n * (g j.2 * conjGal (g j.2) * (u / conjGal u))) =
        n • f δ + (f (g j.2) + f (conjGal (g j.2)) + (f u - f (conjGal u))) := by
      clear * - hf hδ hu
      have := hf (u / conjGal u) (conjGal u)
      induction n <;> simp_all [pow_succ, add_smul, κ, cycCharMod_prime_pow_eq, g, mul_comm]
    have R {e Φ T z} (h : IsLaw ν e Φ T z) :=
      (Y z (ℓ ^ ν) (by simpa using h.map_conj_mul 1)).trans (by simp [CharP.cast_eq_zero, *,
      κ, ↓h.odd, g, mul_comm, mul_two] : _ = 2 * z u) ▸ h.isLocallyConstant.eventually_eq _
    refine (nonempty_of_mem (inter_mem V (inter_mem_inf (eventually_mostFrobenii
      ((eventually_notMem_star_notMem ℓ ∅).and (tendsto_place_comap_cofinite (algebraMap _ E)
      (Set.toFinite (T₀ ∪ ⋃ i, insert (primeBelowPlus (f i).1.w) (f
      i).2.1)).compl_mem_cofinite :)) fun _ ↦ id) ⟨_, (R r).and ((eventually_all.2 (R <| hz ·)).and
      (((selmerZ1.finite_unramified_cocycles (.of (charRep ..) (((Continuous.of_isOpen_ker κ
      Fact.out).pow _).inv.fst'.smul continuous_snd)) (placesDividing E
      ℓ).toFinite).eventually_all.2 fun x h ↦ (continuous_discrete_rng.1 h.1.1 _).mem_nhds rfl).and
      (isOpen_ker_cycCharMod.1.mem_nhds (by simp [cycCharMod_prime_pow_eq, g, mul_comm, *])))),
      .rfl⟩))).elim fun x ⟨a, ⟨z, n⟩, b, c, d, o⟩ ↦ ⟨(x, _, _),
      ⟨z.2.2, o⟩, r, by simpa [L r, ← k _ r, cycCharMod_prime_pow_eq, ← mul_assoc, map_ofNat, sq,
      m, *, κ, ((Units.isUnit _).map _).pow] using map_dvd (toZModPow ν) ((mul_dvd_mul_right
      ⟨_, rfl⟩ _).trans (h2 _ j.1.2)), fun O k hk ↦ sub_eq_zero.1 (eq_zero_of_mem_evenClasses hk
      fun u m ↦ (fun d ↦ ?_) (d _ ⟨m, ?_⟩)), by simp [h₄] at n c; simpa [Ne.symm, *]⟩
    erw [map_sub, d, Y (u <| k ·)]
    all_goals simp +contextual [hk.2.1, mem_selmerModule_iff.1 hk.1, ↓m.2, κ, charRep,
      CharP.cast_eq_zero])
  choose a d k l c e s using F
  have inj : Injective (primeBelowPlus ∘ _) := .of_lt_imp_ne (swap (c · · · |>.1))
  have hw : IsNewPlaces ν _ (f · |>.1.isPlaceOver.tameGenerator) _ := (and_assoc.1 ⟨a ·, _, _, rfl⟩)
  refine ⟨⟨(f · |>.1), ⟨inj.of_comp, by grind [isSplit_of_q_prime, primeBelowPlus_star,
    FrobeniusDatum.prime_q]⟩, (f · |>.1.isFrob.mem_ker_cycCharMod_iff
    (by simp [(FrobeniusDatum.isPlaceOver _).valuation_natCast_eq_one_iff, (a _).1]) |>.1
    (inv_mem (a _).2) |>.symm.dvd')⟩, ⟨hw, ⟨p, hy.elim (by
    simp [J]; grw [card_subtype_le, hq y (by omega) ·, Fintype.card_fin]
    nlinarith [(y ^ 21 * h).zero_le]) (by simp [·]), by tauto⟩, dvd_of_mul_left_dvd ∘' hD, fun O j z
    hz H ↦ (d j).reciprocity (J := Set.Ici j) _ inj.injOn.injective (⟨a ·, by clear * - c e; grind⟩)
    ⊥ (c · _ ·.bot_lt |>.2.2) O z ⟨IsNewPlaces.mem_selmerModule_of_tame_eq_zero (J := Set.Iio j)
    (hw ·) hz.1 (by simp +contextual [idOrConjInv, cocycle_apply_inv (mem_selmerModule_iff.1
    hz.1).1, hz.2.1, *, -smul_eq_zero]),
    hz.2⟩ (fun _ ⟨i, e⟩ ↦ e ▸ (H _ i.1.2).2 i.2) _ (k j), fun O e ↦
    ⟨by simpa [cycInv, map_ofNat] using map_dvd (algebraMap _ O) (
    .trans ⟨_, rfl⟩ (h2 _ e.2)), fun z k K ↦ ?_⟩⟩, s⟩
  choose m u _ c
    using by simpa [mem_selmerModule_iff, tateTwist, -Pi.add_apply] using add_mem k.1 k.1
  refine congrFun (sub_eq_zero.1 (R (e := e) _ (mem_selmerModule_iff.2 ⟨?_, ?_, ?_,
    (funext ?_).subst ((c.comp_continuous (continuous_const_mul γ⁻¹)).sub
    (c.comp_continuous (continuous_mul_const γ⁻¹)))⟩) fun _ h ↦
    sub_eq_zero.2 (sah m _ _ (l (e, ⟨_, h⟩) O z k ▸ K _ rfl)))) <;> simp +contextual [m, tateTwist,
    cycInv, u, cycChar_eq_one_of_mem_inertiaAbove, obeying, -Pi.add_apply] <;> intros <;> module
end

section
/-! Denominator of projection to lifts, without the even part. For a twist with short Selmer groups,
the ℓ-adic denominator of the projection to theta lifts, read by pairing integral forms with ones
orthogonal to non-lifts resembling lifts, is bounded by local losses, class number, level and odd
classes, while the even classes, where Vandiver's conjecture lives, cost nothing. Ribet-type bounds,
Taylor–Wiles primes in the residually reducible case and the mass formula case are known. Related
work: Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's method for GL2,
2023; Dotto–Thorne, Modularity of residually reducible representations of rank 2, 2026;
Martin–Wakatsuki, Mass formulas and Eisenstein congruences in higher rank, 2024.

This file: Denominator of projection to theta lifts bounded without the even classes. -/


open Polynomial Fintype Module Filter Isotypic Real LinearMap LevelPlaces.LevelForm Submodule IsApt
  NeZero PadicInt Units
attribute [-simp] map_eq_zero nsmul_eq_mul Pi.smul_apply

/-- There are h ≤ v_ℓ(`Data.chosenGroupOrder`), with h = 0 unless ℓ ≤ h₂², and γ in the Galois group
of E such that
cyc(γ)^a − 1 divides ℓ^h in ℤ_ℓ for all 0 < a < t. -/
lemma exists_cycChar_pow_sub_one_dvd {P} (D : Data P) ℓ [ThePrime ℓ] : ∃ h ≤ padicValNat ℓ
  D.chosenGroupOrder, (ℓ ≤ D.h₂ ^ 2 ∨ h = 0) ∧ ∃ γ : AbsGal D, ∀ a ∈ Set.Ioo 0 D.t, (cycChar Ω ℓ γ ^
  a).1 - 1 ∣ ℓ ^ h := if l : D.h₂ ^ 2 < ℓ then IsCyclic.exists_ofOrder_eq_natCard.elim fun b hb ↦
  (exists_inertia_cycChar_eq (valuation_comap_intQpBar_lt_one
  (IsAlgClosed.lift (R := ℚ)).1) (ZMod.val_coe_unit_coprime b).symm).elim fun γ i ↦ ⟨0, bot_le,
  .inr rfl, {γ with commutes' x := D.algebraMap_mem_cycloField x ⟨γ, cycCharMod_of_mem_inertiaGroup
  i.1 ((Nat.coprime_of_lt_prime out (D.nat_le_of_hasLogBound.trans_lt l) Fact.out).valuation_eq_one
  (valuation_comap_intQpBar_lt_one _))⟩}, fun a h ↦ (IsUnit.of_map toZMod _ (by
    erw [val_pow_eq_pow_val, i.2]
    simpa using pow_ne_one_of_lt_orderOf h.1.ne' (by grind [orderOf_units, Nat.card_units,
      Nat.card_zmod, Nat.le_self_pow]))).dvd⟩ else (exists_chosen_notMem_placesDividing D ℓ).elim
  fun v ⟨i, _, hw, hi⟩ ↦ ⟨_, le_rfl, by lia, (v.isPlaceOver_placeOver.exists_isFrob _).imp
  fun φ hφ a ha ↦ by simpa [hφ.cycChar_eq ℓ (v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2
  hw.2), hi, pos, valuation] using (g_pow_sub_one_dvd_chosenGroupOrder D ⟨ha.1,
  ha.2.le.trans D.nat_le_of_hasLogBound⟩).natCast.trans (unitCoeff_spec (p := ℓ) out).dvd⟩

/-- Let Q be auxiliary, the avatar ψ of ϑ⁻¹ anticyclotomic, Σ_Q v(ψ(γ) − 1) ≤ cr for tame generators
γ, β = `rowBudget`. A cut spanned by lifts whose rows T have Sel_M(Tψ) of length ≤ (10fr + 1)cr,
M = ⌊D.r·β⌋ + 1, has denominator ≤ rβ log ℓ.

Denominator of projection to lifts, without the even part. -/
theorem denominatorLe_rowBudget {P} {D : Data P} {ℓ} [ThePrime ℓ] (ι : PadicIso ℓ) (ϑ :
  D.Twist) (hq : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D)) {r n} [Fintype r]
  [Fintype n] {O : AuxPair _ r n} {E Z} (hw : Z ≤ span ℂ {y ∈ Z | (∃ c, y ∈ (tupleProj O c).range ∧
  IsApt O c ϑ ∧ (tupleProj O c).range ≤ range (O.groupAlgAction E)) ∧ ∃ z, O.Lifts y z ∧ ∃ R, ∃ V :
  AuxPair _ r n, HasRow V z R ∧ O.μ = V.μ * ϑ.toAutChar ∧ ∃ γ s, SelmerLengthLe ϑ.invAvatar R ϑ.Q
  (⌊D.r * rowBudget D ℓ⌋₊ + 1) γ s}) : DenominatorLe ιℓ O E Z (rowBudget D ℓ * log ℓ) := by
  refine let A := _; have hZ : span ℂ A = Z := span_eq_of_le _ inf_le_left hw; fun _ e ↦ e ▸ fun
    Ξ Ξ' hl hΞ ↦ norm_gram_det_le_of_operators hZ toSmoothForm (innerₛₗ ℂ ∘ Ξ) (by simp)
        (D.chosenGroupOrder ^ 3) fun _ m₀ o ↦ ?_
  have T {S} (k : S ⊆ A) w h s X : span ℂ S ∈ (O.heckePolyOnForms h s X).invtSubmodule :=
    span_le.2 fun y m ↦ (O.heckePolyOnForms_eq_smul h s ((k m).2.2.choose_spec.1 w h s)
    X).symm.subst (smul_mem _ _ (subset_span m))
  have hT := hZ ▸ T le_rfl
  let N (x : Isotypic (stdSpace _ n) (O.κ, O.detExp)) := normalisedRep O x.galRep
  let 𝓧 (x : Isotypic ..) := ∃ v ∈ A, v.toSmoothForm ∈ x.1 ∧ v.toSmoothForm ≠ 0
  choose c m₁ hc le using m₀.2.1
  -- a lift has another label, or it has the label `c` and lies in an isotypic space
  have z {v} (m : v ∈ A) : tupleProj O c v = 0 ∨ v ∈ (tupleProj O c).range ∧ ∃ x : Isotypic ..,
    v.toSmoothForm ∈ x.1 ∧ _ := or_iff_not_imp_left.2 fun h ↦ ⟨m.2.1.elim fun b k ↦
    (by_contra (h <| tupleProj_eq_self_of_mem_range k.1 ▸ by simp [← End.mul_apply, ← map_mul,
    tupleIdem_orthogonal.ortho ·]) : c = b) ▸ k.1, by_contra fun H ↦ h <| mem_ker.1 <|
    le_of_isotypic_mem (T (by simpa)) (by simpa [mem_span_singleton] using fun x _ m a b ↦
    (H ⟨x, (smul_mem_iff _ a).1 m, b⟩).elim) (mem_span_singleton_self v)⟩
  choose x₀ m₂ using ((z m₀).resolve_left ((tupleProj_eq_self_of_mem_range m₁).trans_ne o)).2
  have h𝓧 : 𝓧 x₀ := ⟨_, m₀, m₂⟩
  have := card_pos_iff.1 O.rank_lt.pos
  choose! _ R hR hL γ₀ y₀ hS₀ using fun {x} (m : 𝓧 x) ↦ (m.elim fun _ k ↦ k.1.2.2.elim fun _ L ↦
    L.2.elim fun R V ↦ V.elim fun _ e ↦ e.1.1.imp fun _ r ↦ ⟨R, r, e.1.2 e.2.1 L.1 (k.2.elim
    isEigenform) (k.2.elim attached_galRep), e.2.2⟩ : ∃ τ R, IsRow D O.rankDiff τ R ∧ _ ∧ _)
  choose γ hγ y h₀ hy using (hR h𝓧).exists_scalar_inertia
  choose _ B sp j co using exists_baseLevel hc hq.1
  have cp (x : B.Eigensystem ![]) g i : ‖(N x g).1.charpoly.coeff
    i‖ ≤ 1 := by simp [(eventually_exists_isLatticeIn (r :=
    N x) (co _ _ (by simp) _ x.2).1.continuous).exists.choose_spec.choose_spec.charpoly_eq_map]
  choose h hh hℓ g₁ hC using exists_cycChar_pow_sub_one_dvd D ℓ
  -- a generic normaliser is regular on the finitely many `N x` that have a regular `N x g - 1`
  let s := {x : B.Eigensystem ![] | ∀ g, (N x g).1.charpoly.IsRoot 1}
  have W (j : ℕ) (t : Set ↥sᶜ) : ∃ θ, ∀ x ∈ t, ((ribetNormaliser (@γ₀ x₀) g₁⁻¹ (@y₀ x₀) (ℓ ^ j)
      θ).linearCombination (intQpBar ℓ) fun g ↦ (N x g).1 - 1).det ≠ 0 := t.toFinite.induction_on _
    (by simp) @fun a _ _ f ⟨θ, h⟩ ↦ (not_forall.1 a.2).elim fun g k ↦ ((f.insert _).eventually_all.2
    fun z m ↦ ((mul_right_injective₀ (neg_ne_zero.2 (ne (ℓ ^ j : PadicAlgCl ℓ)))).comp
    Nat.cast_injective).tendsto_cofinite.eventually (eventually_cofinite_not_isRoot (mt ext_iff.1
    fun e ↦ m.elim (k <| ((Matrix.eval_charpoly ..).trans (coeff_det_X_add_C_card ..).symm).trans <|
    · ▸ e _) (h z · (coeff_det_X_add_C_zero (_ - (N z g).1) _ ▸ e 0))))).exists.imp' (θ + .single g
    ·) (by simp_rw [IsRoot.def, eval_det]; intro; convert id
           simp [ribetNormaliser, X_mul,
             ← Matrix.smul_eq_mul_diagonal, -Finsupp.smul_single]; module)
  choose θ z' hθ hz' using (W _ .univ).imp fun θ h ↦ ((IsFractionRing.isAlgebraic_iff (intQpBar ℓ)
    (PadicAlgCl ℓ) _).2 (.of_finite ..)).exists_nonzero_coeff_and_aeval_eq_zero
    (Pi.isUnit_iff.2 (h · ⟨⟩ |>.isUnit)).mem_nonZeroDivisors
  rw [aeval_pi_apply, funext_iff] at hz'
  choose J _ _ ty hP using exists_isPrimeTriangle O.rankDiff D.algebraMap_mem_cycloField
    (by grw [hc.rank_le.2]; exact D.nat_lt_of_hasLogBound) (by grw [hc.rank_le.2]; exact hC) hℓ
    D.nat_le_of_hasLogBound fun ν g ↦ (exists_eventually_no_eigenvalue_one
    (hq.2.1.isLocallyConstant.continuous.smul (continuous_val.comp (hR h𝓧).continuous)) _ (by
    intro; simp [hq.2.1.eq_one_of_mem_inertiaAbove γ (hγ.imp (by clear * - hq; grind [IsAuxTwist])),
      h₀, _root_.smul_pow, smul_comm (ϑ.invAvatar g), pow_right_comm y]; rfl) (hy ν)).elim fun i
    hσ ↦ ⟨γ ^ i, by simp [cycChar_eq_one_of_mem_inertiaAbove (hγ.imp fun _ ↦ .imp_left (·.2))],
    inter_mem_inf ((eventually_mostFrobenii ((eventually_notMem_star_notMem ℓ (badPlaces D ℓ)).and
    (B.eventually_isOffLevel (L := ![])))).and <| .all fun x : {x : B.Eigensystem _ // (∀ g k, ‖((N
    x g).1.charpoly.coeff - (N x₀ g).1.charpoly.coeff) k‖ < 1) ∧ x ∈ s} ↦ x.1.2.elim fun f m ↦
    eventually_heckePoly_eq_string_mul (x := x.1.1) m.1.1 m.2 x.2.2 (cp _)) (preimage_mem_comap hσ)⟩
  -- `ν` beats the constant that `exists_diagOp_mem_ellIntegralForms` names below
  choose! ν hν using @ENNReal.exists_nat_gt _
  have w (a : EllAdicIntegers) : a.1 = algebraMap _ _ a := rfl
  choose Q tri q s₅ using hP _ ν.succ_pos
  let a := ((coeHom _).comp (chiOneInv O)).codRestrict (intQpBar ℓ) (norm_eq_one_of_continuous (by
    fun_prop) · |>.le)
  choose e s he using fun k x ↦
    (q k).2 x _ (s₅ k) (congr(‖_ - coeff $(charpoly_eq_mul_of_trace_pow_add _ _ _ (by
    simpa [N, _root_.smul_pow, pow_right_comm] using hL h𝓧 <| _ ^ ·)) _‖).ge.trans_lt <| x.2.1 _ ·)
  let ξ {J L x v} m (a : _ ∧ _) : B.Eigensystem (J := J) L := ⟨x, _,
    ⟨a.1, B.formsOfLevel_base_le _ (sp v m)⟩, a.2⟩
  refine (B.exists_diagOp_mem_ellIntegralForms Q (q · |>.1.2) (a := a) (N := N) (fun _ _ ↦
    rfl) (fun k ↦ Subtype.ext ((chiOneInv_spec (Q.frobData k).isPlaceOver (tri.isNewPlaces k).1 0
    (inv_mem (Q.frobData k).isPlaceOver.tameGenerator.2)).trans (pow_zero _))) _ z' (𝓧 ·)
    ⟨ξ m₁ m₂, h𝓧⟩ _ hc.odd.2.pos.ne' (fun k x m h₀ h₁ ↦ (s k ⟨⟨x, m⟩, fun g k ↦ h₁ ⟨_, sub_mem
    (algebraMap_mem _ (⟨_, cp ..⟩ : EllAdicIntegers)) (B.charpoly_mem_heckeAlgebra (a := a) (fun _
    _ ↦ rfl) g k)⟩ (sub_self _), by_contra (h₀ <| hz' ⟨_, ·⟩)⟩).imp fun _ ↦ .imp_right (·.trans
    (Polynomial.map_dvd _ (Finset.univ.dvd_prod_of_mem _ (Finset.mem_univ _)))))
    (dvd_iff_ellVal_le.2 <|
    (hν (by simp [ellVal, ne, w, map_ofNat]; exact (hθ <| Subtype.ext ·))).le.trans <| by simp [w])
    fun S _ hS ↦ ribet_columns hc hq hh tri S (co _ _ (q · |>.1.1.1) _ ·.2) .refl (fun x ↦
    ⟨hR x.2, hS₀ x.2⟩) (hL ·.2) hS (fun j ↦ (eval_prod ..).trans
    (Finset.prod_eq_one fun i _ ↦ he j i) : ∀ j,
    eval (1 : EllAdicIntegers) _ = 1) _ θ).elim fun s h ↦ ?_
  let' E s := B.diagOp (L := Q.w) s ∘ₗ toSmoothForm
  have key s {y v} m a : (E s ∘ₗ tupleProj O c) v = _ := congr(E
    s $(IsApt.tupleProj_eq_self_of_mem_range m)).trans (B.diagOp_apply s (@ξ _ _ y v m a) a.1)
  refine ⟨_, fun v m ↦ (z m).elim (⟨0, by simp [·]⟩) fun k ↦ ⟨_, key _ k.1 k.2.choose_spec⟩,
    fun l e ↦ smul_left_injective ℂ m₂.2 (key s m₁ m₂ ▸ e) ▸ ?_, fun a b w m e ↦ ?_⟩
  convert ellVal_le_iff.1 h.1 using 1 <;> simp [rpow_def_of_pos, pos] <;> ring
  have : _ • _ • w.toSmoothForm ∈ BaseLevel.ellIntegralForms := e ▸ h.2 _ (sp _ ⟨_, rfl⟩) _ (j _
    fun _ h ↦ by simpa using! (weylGauge_le_one_iff (ι := _) _ h).1 ((hΞ b).1 _)) _ (sp _ ⟨_, rfl⟩)
    (fun s k ↦ (hw.trans (sInf_le fun v m ↦ (z m).elim (by simp [·]) fun r ↦ r.2.elim fun _ a ↦ by
    simpa [k (ξ r.1 a) ⟨v, m, a⟩] using key s r.1 a) : _ ≤ (E s ∘ₗ _).ker) (by simp))
    fun s k ↦ (E s ∘ₗ _).sub_mem_ker_iff.1 (show tupleProj O c (Ξ' b - _) ∈ (E s).ker by
    -- a weak lift that is orthogonal to the cut and to the impostors at `w` is an impostor
    choose w ok hv hS using ((B.eventually_isOffLevel (L := ![])).and_frequently
      (frequently_isSplit_notMem_places O)).exists
    refine le_of_isotypic_mem (Z :=
      (tupleProj O c).range ⊓ Zᗮ ⊓ (_ ⊓ (O.heckePolyOnForms hv hS (O.testValue w)).ker)ᗮ) (by
      iterate 2 intros; apply_rules only [Sublattice.inf_mem, orthogonal_mem_invtSubmodule_hecke,
        IsApt.range_tupleProj_mem_invtSubmodule, hT]
      intro; simp +contextual [O.heckePolyOnForms_comm hv]) (fun x v r a ↦ by_contra fun H ↦
      inner_self_ne_zero.2 (ne_zero_of_map a.2) (r.2 v ⟨r.1, ?_⟩)) ⟨⟨⟨_, rfl⟩,
      isSymmetric_tupleProj.orthogonalComplement_mem_invtSubmodule (hw.trans (sInf_le fun v m ↦
      (z m).elim (by simp [·]) (by simp [tupleProj_eq_self_of_mem_range ·.1, m.1]))) (by simp)⟩,
      fun _ a ↦ by rw [← isSymmetric_tupleProj, tupleProj_eq_self_of_mem_range a.1.1,
      sub_mem ((hΞ b).2 _ _ _) (orthogonal_le inf_le_right (by simp)) _ ⟨⟨le a.1.1, a.2⟩, a.1.2⟩]⟩
    let y {J L} := @ξ J L x v r.1.1 a
    choose z t e u using hasHeckePolyAt_of_mem_eigenformsAt (ok.2.2.2 _ y.2 ⟨a.1, sp _ r.1.1⟩) hv
    simpa [O.heckePolyOnForms_eq_smul _ _ (isSphericalWith_of_heckeSplit z u), ne_zero_of_map a.2,
      e, eval_heckePoly, AuxPair.testValue, AutChar.frobValue, HeckeChar.atUnif] using
      isRoot_hecke_string a.1 a.2 (by_contra fun h ↦ H <| by simp [E, B.diagOp_apply s y a.1,
      k y (hz' ⟨y, h⟩)]) ok.2.2.1 ⟨z, t, e, u⟩ (by simp [O.rank_lt]))
  simpa [nsmul_eq_mul, ← PadicComplex.norm_extends ℓ D.chosenGroupOrder, inner_smul_right_eq_smul,
    field] using (Ξ a).norm_inner_le_one (D.chosenGroupOrder • D.chosenGroupOrder • w) ⟨(algebraMap
    ..).comp ιℓ.toRingHom⟩ (D.card_classAut_dvd_chosenGroupOrder hc.card_le levelOf_le_Kf) (hl a _)
    (weylGauge_le_one_of_integralAbove (ι := _) _ (by simpa using! this · ·))
end

section
/-! One anticyclotomic twist makes all Selmer groups short. For finitely many irreducible blocks of Galois representations of lifts, one finite-order anticyclotomic twist ramified at new primes makes, for each of its first m powers, all Selmer groups modulo a given power of ℓ short and the ratios of twisted to untwisted Hecke values barely divisible by ℓ, which limits congruences. Twists of ℓ-power order at new primes that kill a Selmer group or keep L-values barely divisible are known. Related work: Mazur–Rubin, Diophantine stability, 2018; Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Hida, Non-vanishing modulo p of Hecke L-values, 2004. -/

open Matrix Filter Real Module Finsupp Finset CoeffRing Subalgebra RingHom
attribute [-simp] map_smul AlgHom.toRingHom_eq_coe

/-- For finitely many rows R_i and M, some m-fold twist has, for its first m powers ϑ, ψ the avatar
of ϑ⁻¹: Q auxiliary, ψ anticyclotomic, Σ v(ψ(γ) − 1) ≤ cr_ℓ over tame generators γ at Q,
Selmer length of ψR_i mod ℓ^M ≤ (10f·rank + 1)cr_ℓ, v(ιρ_p(ϑ^{±1})) ≤ 9cr_ℓ for ramified p.
Here cr_ℓ = `crudeUnit` and ρ_p = `Data.Pair.ratio` p.

One anticyclotomic twist makes all Selmer groups short. -/
lemma exists_mFoldTwist_selmerLengthLe {P} (D : Data P) ℓ [ThePrime ℓ] (ι : PadicIso ℓ) {I : Type}
    [Finite I] {r : I → Type} [∀ i, Fintype (r i)] {R : ∀ i, _ →* GL (r i)
    _} (h : ∀ i, ∃ t J, IsRow D t J (R i)) M : ∃ τ : D.MFoldTwist, ∀ n, let ϑ := τ.powTwist n
  IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D) ∧
    (∀ i, ∃ γ y, SelmerLengthLe ϑ.invAvatar (R i) ϑ.Q M γ y) ∧
    ∀ (p : D.Pair) s, p.IsRamified → ‖ιℓ (p.ratio ϑ s)⁻¹‖ ≤ exp (9 * crudeUnit ℓ D * log ℓ) := by
  choose w _ hw hℓ hi using exists_chosen_notMem_placesDividing D ℓ
  choose μ V f₁ f₃ f using fun k : Subtype _ × _ ↦ exists_isFamily hw hℓ.2 _ k.2 k.1.2
  choose O u γ β hu hβ hρ using
    (eventually_all.2 (h · |>.choose_spec.choose_spec.eventually_isBalanced hw hℓ M)).exists
  choose Q ψ a j c using exists_anticyclotomic_twist (by simp; grind) ⟨w, by grind, _,
    w.isPlaceOver_placeOver, w.isPlaceOver_placeOver.tameGenerator.2⟩
    hρ f₁ (by finiteness) hβ (fun _ _ ↦ by grw [f₃, hi, ← ellVal_le_crudeUnit D ℓ _ ⟨.refl,
    D.nat_le_of_hasLogBound⟩, pow_one]) (η := crudeUnit ℓ D) (by simp [crudeUnit]) D.m
  obtain ⟨τ, rfl, rfl⟩ :=
    (j 1 ⟨.refl, D.nat_le_of_hasLogBound⟩).elim (exists_tameChar_invAvatar_eq · <| pow_one ψ ▸ ·.1)
  simp_rw [show ∀ n, τ.invAvatar ^ n = (τ.pow n).invAvatar by simp [MonoidHom.ext_iff,
    Data.TameChar.pow, invAvatar_eq_of_artinMap_eq (artinMap_surjective ..).choose_spec]] at *
  have N n hn w c (e : τ.ψ w ^ n = 1) : False := have ⟨σ, hw, H⟩ := (j n hn).2.2
    (hw ⟨w, c⟩).2.2.elim fun B ⟨b,
      k⟩ ↦ have ⟨x, hx, j⟩ := b.exists_localArtin_eq (inv_mem b.tameGenerator.2) 0
      by simpa [ellVal, ← k, invAvatar_eq_of_artinMap_eq (b.artinAt_eq_of_localArtin_eq j ▸
        artinMap_locIdele ..), (τ.pow n).4.charUnramifiedAt e ((τ.pow n).5 _
        (τ.6 w c)) x hx] using (single_le_sum (by simp) (mem_univ ⟨w, c⟩)).trans H
  use ⟨⟨τ, by simpa using N 1 ⟨.refl, D.nat_le_of_hasLogBound⟩⟩, N⟩,
    fun ⟨n, hn⟩ ↦ have s@⟨s₁, s₂, _⟩ := j n hn
    ⟨s, fun i ↦ have ⟨⟨v, o, z⟩, y, e', _, hs⟩ := (hρ i).4
      ⟨γ i, ⟨_, norm_le_one y⟩, (c n hn i).mono ?_⟩, fun p s hp ↦ le_exp_of_log_le (by
      simpa using! neg_le_neg (le_log_of_rpow_le (by simp [NeZero.pos]) (ellVal_le_iff.1
        (f (⟨p, hp⟩, s) ⟨τ.pow n, N n hn⟩ s₁ (9 * _) ((a n hn _).trans_eq (by simp; ring))))))⟩
  rintro O' ⟨hO, ψ', k, s₇⟩; let e := (inclusion hO).1
  refine ⟨e.mapMatrix.1.comp (u i), _, e y, rfl, hu i, k, by simp [twistRep, map_smul', e', by
      simpa [← k] using s₂.eq_one_of_mem_inertiaAbove _ ⟨v, by clear * - s₁ o; simp at *; grind,
        z⟩], by simpa using hs.map e, cycChar_eq_one_of_mem_inertiaAbove ⟨v, o.2, z⟩,
    s₇.trans' (normLength_mono (length_mono ?_))⟩
  rintro x ⟨⟨h⟩⟩; use mem_obeying.2 ?_
  let := e.toAlgebra; have := (inclusion.faithfulSMul hO).to_isTorsionFree
  have := Finite.right ℤ_[ℓ] O.1 O'.1
  rintro _ (H | ⟨_, ⟨_, ⟨v, rfl⟩, f, hf, rfl⟩ | rfl, rfl⟩)
  exacts [mem_obeying.1 h _ (.inl (by simpa [unionWithConj] using! H)), mem_obeying.1 h _ (.inr ⟨_,
    ⟨v, rfl⟩, mapRel _ f, fun z a ↦ funext fun i ↦ (forall_dual_apply_eq_zero_iff O _).1 fun l ↦ by
    simpa [← smul_toAlgebra, mapRel, linearCombination, ↓sum_mapRange_index, sum] using congrFun
      (hf _ (crysCocycles.map a ((l.restrictScalars _).compLeft _) fun g ↦ by simp [funext_iff,
      twistRep, mulVec, dotProduct, ← smul_toAlgebra, by simpa [← k] using
      (s₂.eq_one_of_mem_decompGroup v.2 v.1.isPlaceOver_placeOver g.2)])) i,
    mapDomain_mapRange _ _ _ _ (map_add _)⟩), by simpa [mapRel]]
end

section
/-! A twist with few congruences for each prime. For each prime ℓ and each identification of the
complex numbers with the algebraic closure of the ℓ-adic numbers there is a twist whose first m
powers have few congruences, and the denominators of projections to theta lifts and the divisibility
of ratios of Hecke values sum over all ℓ to at most `Data.B₀` per rank and dimension, resp. x^999
(`Data.IsFitFamily`). It is known that
denominators of projections to lifts give Selmer classes and that twisting lowers Selmer ranks.
Related work: Prasanna, Integrality of a ratio of Petersson norms, 2006 (after Ribet, 1976; Wiles);
Klosin, Congruences among modular forms on U(2,2) and the Bloch–Kato conjecture, 2009; Mazur–Rubin,
Ranks of twists of elliptic curves, 2010.

This file: Existence of twists, one per embedding, whose first m powers have few congruences. -/

open Submodule Data Polynomial Multiset Finset Real

/-- All data D have m-fold twists ϑ_ι, one for each prime ℓ and isomorphism ι: ℂ ≅ ℚ̄_ℓ, such that
the family (ϑ_ι^n) is fit (`Data.IsFitFamily`) for 1 ≤ n ≤ m.

A twist with few congruences for each prime. -/
lemma exists_isFitFamily {P} (D : Data P) : ∃ θ, D.IsFitFamily θ := by
  choose R' F' using fun {ℓ} {_ : ThePrime ℓ} {ι : PadicIso ℓ} (p : {p : D.Pair × D.LiftIndex //
    p.1.IsRankOne p.2}) ↦ exists_row_for_all_twists ι (isApt_rank_one 1 p.2) 1 (fun _ ↦ {0}) 1 (by
    have := (@isFiniteTypeAt_char ℓ _ _ D.E _ _ · 1 Unit _ _ continuous_one (by simp))
    simp_rw [← C_1]
    use! continuous_one <;> simp_all [IsTraceNondeg, Matrix.trace, ← Matrix.ext_iff, IsLabelledAt,
      ↓aroots_X_sub_C, isGoodAt_iff]) (by simp) (by use ?_, ?_, ⟨p.1.2, ?_⟩ <;> simp [← cons_zero,
         countP_cons] <;> grind [Pair.IsRankOne,
    Int.units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.t < D.w _ _)])
  choose R F using fun {ℓ} {_ : ThePrime ℓ} {ι} (a : _ × (D.finite_eigenPart _
    (D.goodForms _)).toFinset) ↦ exists_hasRow_auxPair ι ((Set.Finite.mem_toFinset _).1 a.2.2) a.1
  choose τ H using fun κ : PrimePadicIso ↦ @exists_mFoldTwist_selmerLengthLe _ D κ.1 ⟨⟩ ⟨κ.2⟩ _ _
    (·.getRight?.map 0 |> @RowBlockIndex _ 1) _
    (Sum.rec _ _) (Sum.rec (⟨_, F · |>.1⟩) (⟨_, F' · |>.1⟩)) ⌊D.r * rowBudget D κ.1⌋₊.succ
  choose s s' using fun T (hT : ∀ l ∈ T, Nat.Prime l) ↦ show ∑ l ∈ T, rowBudget D l * log l ≤ D.B₀ ∧
      ∑ l ∈ T, 9 * crudeUnit l D * log l ≤ D.x ^ 999 by -- the budgets, summed over the primes
    clear * - hT
    have L {a} : ∑ l ∈ T, padicValNat l a * log l ≤ log⁺ a := by grw [log_of_nat_eq_posLog,
      log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset _ subset_union_right,
      ← T.subset_union_left] <;> simp_all [Nat.factorization_def]
    push_cast [rowBudget, _root_.loss, lambdaLoss, crudeUnit, add_mul, @mul_assoc ℝ,
      sum_add_distrib, ← mul_sum]
    grw [L, sum_le_sum fun _ _ ↦ by grw [mul_comm, log_le_self (by simp)], sum_le_hasSum _ (by simp)
      (hasSum_coe_mul_geometric_of_norm_lt_one (by bound)), L, (exists_length_shaOdd_le
      ..).choose_spec.2.1, classNumber_le, L, L, prod_le_prod' (by simp; tauto), prod_const,
      Nat.card_Ioc, tsub_tsub_le_tsub_add, add_tsub_cancel_left]
    push_cast [↓log_of_nat_eq_posLog, sub_half, Nat.cast_natAbs, abs_discr_eq_rootDiscr_pow,
      finrank_eq_two_mul_card_infinitePlace]
    any_goals exact neg_one_lt_zero.le.trans (Nat.cast_nonneg _)
    exacts [⟨add_halves D.B₀ ▸ add_le_add D.le_of_hasLogBound D.le_of_hasLogBound,
      D.le_of_hasLogBound⟩, D.nat_le_of_hasLogBound, D.algebraMap_mem_cycloField]
  use τ, fun κ ↦ (@coprime_q_of_isAuxiliary _ _ _ ⟨⟩ _ (H κ ⟨1, .refl,
    D.nat_le_of_hasLogBound⟩).1.1).1, fun j ↦ ⟨_, s, fun κ ↦
    have := ThePrime.mk; ⟨denominatorLe_rowBudget _ _ (H ..).1 (D.range_goodLift_le fun q y a c k
      m ↦ dite (y = 0) (by simp [·]) (subset_span ⟨⟨⟨y, a.1⟩, rfl⟩,
      ⟨c, m, isApt_auxPair D _ j k, D.range_tupleIdem_le k⟩, _, D.lifts_auxLift _ a.2, _, _,
      F ⟨j, q, by simpa using mt (D.goodForms_inf_eigenPart_eq_bot (D.hasRigidLabels_spaceW j)
      (D.hasRigidLabels_spaceW ⟨_, D.nat_le_of_hasLogBound, .refl⟩) · |>.le a) ·⟩, by simp [auxPair,
      liftChar, twist_one_spec], (H ..).2.1 (.inl _)⟩)), fun p h ↦ denominatorLe_rowBudget _ _
      (H ..).1 (span_mono (forall_eq.2 ⟨by simp, ⟨_, trivialLift_mem_range_tupleProj_rank_one _ h,
      isApt_rank_one _ h, le_rfl⟩, _, LValueData.auxPair_lifts_trivialLift _, _, _, F' ⟨(p, j),
      h⟩, by simp [twist_one_spec], (H ..).2.1 (.inr _)⟩))⟩⟩, (.of_le s' fun _ ↦ H _ · |>.2.2 · · ·)
end

section
/-! Part of: The inequality (⋆): upper bound for weighted non-split primes (see New.Main).

This file: Theorem C (`Data.integral_forms_long`: a lower bound for the covolume of the lifts of an
almost spanning family of small index), and the family given by Theorems A and B. -/

open Finset LinearMap Real Submodule LevelPlaces.LevelForm

variable {P} {D : Data P} {n} {y : Fin n → _} {δ V} (i : LinearIndependent ℂ y) (hn :
  (1 - 4 / D.b ^ 2) * D.rowDim ≤ n) (I : D.IndexLe y δ) (hV : ∀ σ, covolumeSq (D.Θ 1 ∘ y) σ ≤ exp V)

/-- If the twists θ_ι satisfy `Data.IsFitFamily`, the family 𝔷(1)²/𝔷(θ_ι)² of squared ratios of
volumes (`Data.𝔷`) has height (`HeightLe`) at most 2D(2fa log⁴ b − h_main), where D is
the dimension of the rows and h_main = `Data.mainHeight`. -/
lemma Data.heightLe_volume_ratio_sq {θ} (o : D.IsFitFamily θ) : HeightLe (2 * D.rowDim *
  (2 * (D.logB * D.budget) - D.mainHeight)) fun ι ↦ D.𝔷 (1 : D.MFoldTwist) ^ 2 / D.𝔷 (θ ι) ^ 2 := by
  -- `vol : 𝔷 ϑ = ‖c ϑ‖ ^ D ∏ⱼ λⱼ ϑ`
  choose c const _ vol using D.volume_iota_eq_prod_liftVolume
  -- each of the `m` lifts has height `D k (log b B₀ - 𝖴)`; `m k B₀ = budget` and `m k 𝖴 = h_main`
  have lifts : HeightLe (D.rowDim * (D.logB * D.budget - D.mainHeight))
      (∏ j ∈ Icc 1 D.m, fun ι ↦ D.liftVolume 1 j / D.liftVolume (θ ι) j) := (HeightLe.prod
    fun j h ↦ by exact heightLe_liftVolume_ratio o ⟨j, mem_Icc.1 h⟩).mono
    (by simp [mainHeight]; field_simp [(HasLogBound.pos D).ne']; rfl) fun _ ↦ le_rfl
  -- the constants have height `2 m² t x ^ 999`
  have consts : HeightLe (2 * (D.logB * D.budget)) fun ι ↦ (‖c (θ ι) / c 1‖ ^ 2 :)⁻¹ :=
    (const θ o).mono (by simpa using D.le_of_hasLogBound) fun _ ↦ le_rfl
  exact ((lifts.pow 2).mul (consts.pow D.rowDim)).mono (by grind) fun ι ↦
    (congrArg (‖ι.2 ·‖) (by simp [vol, mul_pow, div_pow, ← pow_mul]; ring)).le

include i hn I hV

/-- Let y be n ≥ (1 − 4/b²)·dim(rows) independent rows of index ≤ δ whose untwisted lifts have
squared covolume ≤ e^V at every σ. For twists θ satisfying `Data.IsFitFamily`, the ratios
𝔷(θ_ι)/𝔷(1) have height (`HeightLe`) at most V + 2δ + b·dim(rows). -/
lemma Data.heightLe_volume_rows {θ} (o : D.IsFitFamily θ) :
    HeightLe (V + 2 * δ + D.rowDim * D.b) fun ι ↦ D.𝔷 (θ ι) / D.𝔷 (1 : D.MFoldTwist) := by
  obtain ⟨⟨e, he, I⟩, γ, hγ, s⟩ := I, D.crude_rows
  -- the basis: `z a` is the good part of the auxiliary form `ψ a`
  choose k z ψ J c using exists_extend_basis_of_span_eq_top i ((s ▸ span_image
    (D.goodProjTranslate 1)).trans (by simp [range_smul, NeZero.ne, Module.End.one_eq_id]; rfl))
  choose ψ hψ ez using ψ
  -- size and completion; the matrices of the index, extended by the scalar of the auxiliary forms
  refine (one_determinant D.Θ (by simp) J (by simpa) (fun _ ↦ norm_map_det_gram_le fun σ ↦
    Sum.comp_elim .. ▸ covolumeSq_elim_le (ez · ▸ normSqAt_goodProjTranslate_le ((hψ _).2 σ))
    (hV σ)) (by simp) (hγ θ o) he (fun _ j ↦ (integralForms ⟨j⟩).carrier) k (fun ι j _ a _ b ↦ ?_)
    fun ι j ↦ (I _ ⟨j⟩ _ (o.1 ι)).imp' ((algebraMap ..).mapMatrix · |>.fromBlocks 0 0 ((γ (θ ι) /
    γ 1 : ℂ) • 1)) fun _ ↦ .imp (by grw [·]; simp [← RingHom.map_det, -RingHom.mapMatrix_apply])
    (by simpa [Matrix.one_apply] using! And.intro · fun a ↦ ez a ▸
    goodProjTranslate_mem_integralForms ⟨j⟩ ((hψ a).1 _ _ ⟨j⟩ (o.1 ι)) 1)).mono (by
    rw [add_right_comm V, add_assoc]; simp [c, field] at *
    grw [(D.le_of_hasLogBound : _ + _ ≤ 4⁻¹ * D.b ^ 3)]; nlinarith [D.logB.exp_pos]) fun _ ↦ le_rfl
  simpa using (norm_inner_le_one _ _ ⟨j⟩
    (fun g ↦ by erw [D.classAut_eq_bot_of_le_chosenLevel (Subgroup.map_mono fun _ h ↦
    funext fun _ ↦ (h (.inl _) ⟨⟩).2) (by bound [D.card_Y_le .refl])]) a b :)

/-- Integral forms are long: if n ≥ (1 − 4/b²)D independent rows, D = dim(rows), have index at
most δ and their untwisted lifts have squared covolume ≤ e^V at all σ ∈ Aut ℂ, then D(h_main
− 3fa log⁴ b) ≤ V + 2δ. -/
lemma Data.integral_forms_long : D.rowDim * (D.mainHeight - 3 * (D.logB * D.budget)) ≤
  V + 2 * δ := by
  -- one twist `θ ι` for each `ι`, with the congruence bounds; the volumes do not vanish
  obtain ⟨⟨θ, o⟩, _, -, Z⟩ := exists_isFitFamily D, D.volume_iota_eq_prod_liftVolume
  -- `(𝔷 θ / 𝔷 1)² (𝔷 1² / 𝔷 θ²) = 1`, heights add, and the height of `1` is `≥ 0`
  have formula : 0 ≤ 2 * (V + _ + _) + _ := ((((heightLe_volume_rows i hn I hV o).pow 2).mul
    (heightLe_volume_ratio_sq o)).mono le_rfl (by simp [field]; simp [(Z _).1])).nonneg
  linarith [(by gcongr; exact D.le_of_hasLogBound : D.rowDim * D.b ≤
    D.rowDim * (D.logB * D.budget))]

omit I hV i hn

/-- There are n ≥ (1 − 4/b²)D independent rows, D = dim(rows), of index at most 5D log(1 + b²)
fa log³ b, whose untwisted lifts have squared covolume at most exp(n(h_main − m·rem + fa
log⁴ b)) at all σ ∈ Aut ℂ. -/
lemma Data.exists_family_covolumeSq_le (D : Data P) : ∃ n, ∃ y : Fin n → _, LinearIndependent ℂ y ∧
    (1 - 4 / D.b ^ 2) * D.rowDim ≤ n ∧
  (∃ δ ≤ 5 * D.rowDim * log (1 + D.b ^ 2) * D.budget, D.IndexLe y δ) ∧ ∀ σ,
  covolumeSq (D.Θ 1 ∘ y) σ ≤ exp (n * (D.mainHeight - D.m * D.remainder + D.logB * D.budget)) := by
  obtain ⟨⟨q, q0, B, hB, ⟨S, hS, sp, size⟩, index⟩, -, -, t, ht, big⟩ :=
    D.short_forms, D.enough_forms
  -- the family: a basis among the translates
  let Y := Set.image2 (B ·) t S
  obtain ⟨y, hy, -, i⟩ := exists_fun_fin_finrank_span_eq ℂ Y
  rw [(by simp [Y, ← Set.iUnion_image_left, span_iUnion₂, sp]
          simp [hB, range_smul, q0.ne'] : iSup _ = span ℂ Y)] at big
  -- index and length
  exact ⟨_, y, i, big, ⟨_, mul_le_mul_of_nonneg_right ht (HasLogBound.pos D).le, index t _ y
    (Set.image2_subset_left hS <| hy ·)⟩, fun σ ↦ covolumeSq_le
    (have ⟨s, _, φ, h, e⟩ := hy ·; by simpa [e] using size φ h s σ)⟩
end
