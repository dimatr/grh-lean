import Lib.Adelic.Model

-- part: Lib.Weil.Construction.WeilOperators
section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Abstract Weil operators on vacuum coefficients: cocycle, unitarity, intertwining of
Heisenberg action, continuity. -/

noncomputable section

namespace Heisenberg.IsVacuum

open MeasureTheory Heisenberg.Rep ContinuousLinearMap
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W] {μ : Measure W}
  [μ.IsAddHaarMeasure] {e : W → ℂ} [he : IsVacuum H μ e] {G : Type _} [Group G] [TopologicalSpace G]
  [DistribMulAction G W] [ContinuousSMul G W] {c : G → G → ℂ} (B : H.MultiplierAction μ e G c)
  (A : H.MultiplierAction μ e G) (g : G) (h : G) (k : G) (x) (v : Heisenberg.IsVacuum.Model H)
  (w : Heisenberg.IsVacuum.Model H)

/-- For an action B with any cocycle c and multiplier Δ, and g in G, the bounded operator v ↦
Δ(g) ∫ v(y) ρ(gy)vac dμ(y) on the reproducing space. -/
def weilOp := B.Δ g • (heisRep.moveBy B g).integrated.flip vacElem

lemma integrated_moveBy_integrated : (heisRep.moveBy B g).integrated
  ((heisRep.moveBy B k).integrated w v) x = (heisRep.moveBy B (g * k)).integrated w ((heisRep.moveBy
  B g).integrated v x) := by rw [← flip_apply, map_integrated]; rfl; simp [mul_smul]

lemma map_integrated_moveBy (T : _ →L[ℂ] ℂ) : T ((heisRep.moveBy B g).integrated w v) = ∫ y,
  w (g⁻¹ • y) * T (heisOp y v) ∂μ
  := .trans (by simp [map_integrated_eq_integral]) ((B.2 g).integral_comp' (f := .smul g) _)

lemma weilOp_triple : weilOp B (g * h)⁻¹ * weilOp B g * weilOp B h =
  c g h • 1 := have := (map_integrated_moveBy B (T := modelEval ·))
  hom_ext (by simp_all [← B.7, weilOp, integrated_moveBy_integrated, mul_assoc, smul_smul,
    ← neg_add', he.3, -neg_add_rev, mul_left_comm])

omit [μ.IsAddHaarMeasure] in
lemma norm_integrated_flip_le (R : H.Rep (Model H)) : ‖R.integrated.flip v‖ ≤ ‖v‖ := by
  grw [le_opNorm, opNorm_flip, integrated, kernelIntegral, LinearMap.mkContinuous₂_norm_le] <;> simp

@[simp] lemma modelInner_vacElem : he.modelInner vacElem v =
  v 0 := by simp [← modelInner_heisOp_vacElem]

lemma weilOp_one : weilOp B 1 = 1 := hom_ext (by simp [weilOp, he.2])

/-- Cocycle relation for the Weil operators ω attached to a vacuum e and an action with cocycle
c: if c(g,1) = 1 for all g, then ω(g)ω(h) = c(g,h)·ω(gh). -/
lemma weilOp_mul (h1 : ∀ g, c g 1 = 1) h : weilOp B g * weilOp B h = c g h • weilOp B (g * h) := by
  grind [weilOp_triple B (g * h)⁻¹ 1, weilOp_triple, weilOp_one, =_ mul_smul_one, one_smul, inv_inv]

@[simp] lemma modelInner_weilOp (h1 : c g 1 = 1) : modelInner (weilOp B g v) (weilOp B g w) =
  modelInner v w := by
  convert congr(modelInner ($(weilOp_triple B g 1) v) w) using 1 <;> simp_all [weilOp_one,
    ← conj_modelInner w]
  set u := weilOp B g v; simp [weilOp, map_integrated_moveBy _ g, map_integrated_eq_integral,
    conj_modelInner, ← integral_conj, ← conj_modelInner _ u, mul_comm]

/-- For an action with cocycle c satisfying c(g,1)=1 for all g, the subgroup of those s in G
with c(g,s)=1 for every g. -/
def cocycleRadical (h1 : ∀ g, c g 1 = 1) : Subgroup G := by
  have H g h k := congr(modelInner (weilOp B (g * h * k) vacElem)
    ($(mul_assoc (weilOp B g) (weilOp B h) (weilOp B k)) vacElem))
  simp_all [weilOp_mul, he.2]; use! {s | ∀ g, c g s = 1}, ?_, h1 <;> grind [inv_mul_cancel]

/-- The Weil representation: for an action A with trivial cocycle, the homomorphism from G to
bounded operators sending g to v ↦ Δ(g) ∫ v(y) ρ(gy)vac dμ(y). -/
def weilRep := MonoidHom.mk ⟨_, weilOp_one A⟩ (by simp [weilOp_mul])

lemma modelInner_weilRep : modelInner (weilRep A g v) (weilRep A g w) =
  modelInner v w := by simp [weilRep]

attribute [simp] weilOp modelInner_weilRep

lemma weilRep_heisOp : weilRep A g (heisOp x v) =
  heisOp (g • x) (weilRep A g v) := by simp [weilRep]

lemma weilRep_eq_integral : weilRep A g v = A.Δ g • ∫ y, v (g⁻¹ • y) • heisOp y vacElem ∂μ := by
  rw [← (A.2 g).integral_comp' (f := .smul g)]; aesop

lemma conj_delta_mul_weilRep_vacElem : starRingEnd _ (A.Δ g) * weilRep A g vacElem 0 = 1 := by
  simpa [integrated_moveBy_integrated, he.2] using! congr($(weilOp_triple A 1 g⁻¹) vacElem 0)

@[fun_prop] lemma continuous_weilRep [FirstCountableTopology G] : Continuous ↿(weilRep A · ·) := by
  refine A.4.fst'.smul (continuous_prod_of_continuous_lipschitzWith' _ _ (lipschitzWith_of_opNorm_le
    <| norm_integrated_flip_le _ <| moveBy _ A ·) fun v ↦ continuous_of_dominated ?_ ?_
    (v.2.1.smul_const he.vacElem).norm (.of_forall ?_)) <;> simp [norm_smul] <;> fun_prop

attribute [irreducible] weilRep
end Heisenberg.IsVacuum
end
end

-- part: Lib.Weil.Construction.OrthogonalSum
section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Tensor products of Heisenberg vacuum models; Wiener amalgam bound for coefficients. -/

namespace Heisenberg

open MeasureTheory Heisenberg.Rep IsVacuum Measure ENNReal Set MultiplierAction
variable {W : Type _} [AddCommGroup W] [TopologicalSpace W] {H : Heisenberg W} [MeasurableSpace W]
  [IsTopologicalAddGroup W] [BorelSpace W] [SecondCountableTopology W]
  {μ : Measure W} [μ.IsAddHaarMeasure] {e : W → ℂ} {W₁ : Type _} [AddCommGroup W₁]
  [TopologicalSpace W₁] {H₁ : Heisenberg W₁} [MeasurableSpace W₁] [IsTopologicalAddGroup W₁]
  [BorelSpace W₁] [SecondCountableTopology W₁] [LocallyCompactSpace W₁] {μ₁ : Measure W₁}
  [μ₁.IsAddHaarMeasure] {e₁ : W₁ → ℂ} {W₂ : Type _} [AddCommGroup W₂] [TopologicalSpace W₂]
  {H₂ : Heisenberg W₂} [MeasurableSpace W₂] [IsTopologicalAddGroup W₂] [BorelSpace W₂]
  [SecondCountableTopology W₂] [LocallyCompactSpace W₂] {μ₂ : Measure W₂} [μ₂.IsAddHaarMeasure]
  {e₂ : W₂ → ℂ} {X : Type _} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An isomorphism φ: W₁ × W₂ → W of topological groups under which the bicharacter of H and the
function e are the products of those of the factors (β₁β₂, e₁e₂). -/
structure OrthogonalSum H H₁ H₂ (e : W → ℂ) [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] where
  equiv : W₁ × W₂ ≃ₜ+ W
  beta_equiv x y : β H (equiv x) (equiv y) = β H₁ x.1 y.1 * β H₂ x.2 y.2
  vac_equiv x : e (equiv x) = e₁ x.1 * e₂ x.2

variable (R : Rep H X) [IsVacuum H₁ μ₁ e₁] [IsVacuum H₂ μ₂ e₂] (S : H.OrthogonalSum H₁ H₂ e)
  [he : H.IsVacuum μ e] (v : Heisenberg.IsVacuum.Model H₁) (w : Heisenberg.IsVacuum.Model H₂)
  (x : W) (f : X)
attribute [local simp] IsVacuum.ext_iff OrthogonalSum.beta_equiv weilRep
  integrated_apply_eq_integral

/-- Wiener-type bound: T bounded, κ: W₁ → W a continuous homomorphism, u(0) ≠ 0, ‖Tρ(z+κx)u‖ =
‖g(t(z)+x)‖, g integrable. Some compact B ⊆ W₁ and M give ∑_i ‖Tρ(κφ(i))v‖ ≤ #φ⁻¹(B)·M·‖v‖
for all homomorphisms φ: I → W₁ and all v. -/
lemma IsVacuum.wiener_bound [LocallyCompactSpace W]
    [T2Space W₁] (T : Model H →L[ℂ] X) {u} (hu : u 0 ≠ 0) (κ : _ →ₜ+ W) {g :
  _ → X} (hg : Integrable g μ₁) (t : W → _) (h : ∀ z x, ‖T (heisOp (z + κ x) u)‖ₑ = ‖g
  (t z + x)‖ₑ) : ∃ B, IsCompact B ∧ ∃ M : NNReal, ∀ {I} [AddGroup I] (φ : I →+ _) v,
  ∑' i, ‖T (heisOp (κ (φ i)) v)‖ₑ ≤ (φ ⁻¹' B).encard * M * ‖v‖ₑ := by
  obtain ⟨m, K, k, o⟩ := (continuous u).enorm.comp κ.2.neg, exists_compact_mem_nhds (0 : W₁)
  let ⟨r, hr⟩ := exists_nat_mul_gt ((setLIntegral_pos_iff m.measurable).2
    (μ₁.measure_pos_of_mem_nhds ((m.continuousAt.eventually_ne (by simpa)).and o))).ne' one_ne_top
  refine ⟨_, k.neg.add k, r * ‖hg.toL1‖₊ + 1, fun φ v ↦ ?_⟩
  cases e : encard _ <;> by_cases v = 0 <;> simp [*]
  grw [← le_self_add, mul_assoc, mul_assoc, show _ * ‖v‖ₑ = ∫⁻ z, ∫⁻ x, ‖v z‖ₑ * ‖T (heisOp (z + κ
    x) u)‖ₑ ∂μ₁ ∂μ by simp [*, v.2.1, ↓lintegral_const_mul', mul_comm, lintegral_add_left_eq_self
    (‖g ·‖ₑ), ← Integrable.enorm_toL1]; exact mul_comm .., lintegral_lintegral_swap (by fun_prop),
    ← nsmul_eq_mul,
    ← mul_smul_comm, ← μ₁.restrict_le_self, ← lintegral_smul_measure, ← sum_restrict_le (fun i ↦
    measurable_sub_const (φ i) k.measurableSet) fun _ ↦ e ▸ encard_le_encard_of_injOn (fun γ h ↦
    ⟨_, neg_mem_neg.2 h, _, (Classical.epsilon_spec_aux ⟨0⟩ _ ⟨_, h⟩ :), by simp; rfl⟩)
    sub_left_injective.injOn, lintegral_sum_measure, ← ENNReal.tsum_mul_left]; gcongr
  grw [← (measurePreserving_add_left ..).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addLeft (φ i)), ← one_mul ‖_‖ₑ, hr, mul_assoc, lintegral_mul_const_le]
  gcongr; simp [preimage]
  simpa [norm_smul, ← ofReal_norm, add_left_comm] using (heisRep.map_integrated_eq_integral
    (T ∘L heisOp ..) v (heisOp _ u) ▸ enorm_integral_le_lintegral_enorm _ :)

attribute [local simp ←] integral_smul map_add map_sub integral_prod_mul

/-- From a Heisenberg representation R of H and a decomposition φ, the representation of H₁ on
the same space sending x to R(φ(x,0)). -/
@[local simp] def Rep.left : H₁.Rep X := ⟨(R.ρ <| S.equiv ⟨·, 0⟩), by simp, by simp, by fun_prop⟩

/-- From a Heisenberg representation R of H and a decomposition φ, the representation of H₂ on
the same space sending x to R(φ(0,x)). -/
@[local simp] def Rep.right : H₂.Rep X := ⟨(R.ρ <| S.equiv ⟨0, ·⟩), by simp, by simp, by fun_prop⟩

/-- The bounded bilinear map between reproducing spaces sending (v₁, v₂) to ∫ v₁(x) ϱ(φ(x,0)) (∫
v₂(y) ϱ(φ(0,y))vac dy) dx, ϱ the Heisenberg representation of the sum. -/
noncomputable def OrthogonalSum.tmul : Model H₁ →L[ℂ] Model H₂ →L[ℂ] Model H :=
  ((heisRep.left S).integrated.flip ∘L (heisRep.right S).integrated.flip vacElem).flip

lemma OrthogonalSum.isVacuum : H.IsVacuum ((μ₁.prod μ₂).map S.equiv) e := by
  unhygienic cases_type* IsVacuum OrthogonalSum; cases (equiv.eq_comp_symm ..).2 (funext ‹_›)
  use (by fun_prop) <;> simp (disch := fun_prop) [*, equiv.surjective.forall, integral_map,
    integrable_map_measure, Function.comp_def, Integrable.mul_prod]
  simp [← twisted_conv, ← twisted_conv_1, mul_mul_mul_comm]

lemma OrthogonalSum.measurePreserving_equiv [LocallyCompactSpace W] :
    MeasurePreserving S.equiv (μ₁.prod μ₂) μ :=
  ⟨by fun_prop,
  addHaar_eq_of_integral_eq_one he.integral_norm_sq_eq_one S.isVacuum.integral_norm_sq_eq_one⟩

omit [CompleteSpace X] in
lemma OrthogonalSum.integral_eq_integral_prod [LocallyCompactSpace W]
    (f : W → X) : ∫ x, f x ∂μ = ∫ x, f
  (S.equiv x) ∂μ₁.prod μ₂ := S.measurePreserving_equiv.2 ▸ S.equiv.isClosedEmbedding.integral_map f

omit [LocallyCompactSpace W₁] [μ₁.IsAddHaarMeasure] [LocallyCompactSpace W₂]
  [μ₂.IsAddHaarMeasure] in
@[local simp] lemma OrthogonalSum.tmul_apply : S.tmul v w x =
  v (S.equiv.symm x).1 * w (S.equiv.symm x).2 := by
  erw [← valueAt_apply, ← v.2.2, ← w.2.2,
    map_integrated_eq_integral _ (modelEval _ ∘L integrated _ v)]
  revert x; simp [map_integrated_eq_integral, S.equiv.surjective.forall, ← integral_const_mul,
    ← integral_mul_const, S.vac_equiv]; grind

lemma OrthogonalSum.weilRep_tmul [LocallyCompactSpace W]
    {G G₁ G₂} [Group G] [TopologicalSpace G] [DistribMulAction G W]
  [ContinuousSMul G W] [Group G₁] [TopologicalSpace G₁] [DistribMulAction G₁ W₁] [ContinuousSMul G₁
  W₁] [Group G₂] [TopologicalSpace G₂] [DistribMulAction G₂ W₂] [ContinuousSMul G₂ W₂] A A₁ A₂ {g :
  G} {g₁ : G₁} {g₂ : G₂} (hΔ : Δ A g = Δ A₁ g₁ * Δ A₂ g₂) (ha : ∀ x, g • S.equiv x = S.equiv (g₁ •
  x.1, g₂ • x.2)) v w : weilRep A g (S.tmul v w) = S.tmul (weilRep A₁ g₁ v) (weilRep A₂ g₂ w) :=
  by simp_all [S.equiv.surjective.forall, S.integral_eq_integral_prod, S.vac_equiv]; grind

lemma Rep.integrated_tmul [LocallyCompactSpace W] : R.integrated (S.tmul v w) f =
  (R.left S).integrated v ((R.right S).integrated w f) :=
  by simp [↓map_integrated_eq_integral, integrated_apply, S.integral_eq_integral_prod, smul_smul,
       mul_comm]
     exact integral_prod_symm _ ((v.2.1.mul_prod w.2.1).smul_bdd ‖f‖ (by fun_prop) (by simp))

omit [LocallyCompactSpace W₁] [μ₁.IsAddHaarMeasure] [LocallyCompactSpace W₂]
  [μ₂.IsAddHaarMeasure] in
lemma OrthogonalSum.tmul_vacElem : S.tmul vacElem vacElem = vacElem := by simp [← S.3]

omit [LocallyCompactSpace W₁] [LocallyCompactSpace W₂] in
lemma OrthogonalSum.heisOp_tmul : heisOp x (S.tmul v w) = S.tmul (heisOp (S.equiv.symm x).1 v)
  (heisOp (S.equiv.symm x).2 w) := by simp [map_sub, mul_mul_mul_comm, ← S.2]
end Heisenberg
end
