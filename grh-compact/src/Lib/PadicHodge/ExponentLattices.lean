import Lib.PadicHodge.Letters

section
/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Kisin module of a crystalline lattice: frame, finite height, divisibility tests,
spanning by nearly invariant vectors. -/

open Algebra Algebra.TensorProduct Module _root_.TensorProduct FaithfulSMul Finset LinearMap Matrix
  MulSemiringAction Pointwise Submodule algebraMap Lift.Chart

namespace Lift.KummerChart.JumpLattice

attribute [-instance] Bialgebra.toAlgebra NormedAlgebra.toAlgebra NormedSpace.toModule

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {L : JumpLattice O}

lemma exists_functional_extend (f : _ →ₗ[ℤ_[p]] BdR) : ∃ μ :
    L.Functional, ∀ t, μ (.mk 1 t) = f t := (exists_extend_of_notMem (p := ⊥) 0 (@NeZero.one _ _ (by
  apply_rules [nontrivial_of_algebraMap_injective_of_isDomain, algebraMap_injective])).1 f).rec
  fun Ψ h ↦ ⟨AlgebraTensorModule.lift ((liftBaseChangeEquiv BdR).2 Ψ), by bound⟩

attribute [-simp] LinearMap.map_smul_of_tower map_one map_smul

attribute [local simp ←] IsScalarTower.algebraMap_apply

attribute [local simp] Fintype.linearCombination_apply Function.comp_def S_smul basisValues
  frobGroup_smul_smul phiInvToBdR mulVec
  vecMul MonoidHom.map_one Prod.mk_one_one RingHom.map_one mul_smul dotProduct

lemma equivariant_iff_basisValues {μ g A μ'} (hA : IsUnit A) (H :
  (repMatrix L.ρ (finBasis ..) g).map (↑) * A.map (toGp g • ·) = A) : (∀ t, μ' (.mk 1 (L.ρ g t)) =
  toGp g • μ (.mk 1 t)) ↔ basisValues μ' ᵥ* A = toGp g • basisValues μ ᵥ* A := by
  erw [(funext ((toRingHom ..).map_vecMul A _) : toGp g • _ ᵥ* A = _), ← congr(_ ᵥ* $H),
    ← vecMul_vecMul, (vecMul_injective_of_isUnit (hA.map (toRingHom ..).mapMatrix)).eq_iff]
  simpa [funext_iff, repMatrix, toMatrixAlgEquiv_apply, ← smul_def', ← commutes,
    ← map_smul_of_tower, ← map_sum, -LinearMap.map_smulₛₗ] using ⟨by tauto, fun h t ↦ by
    simpa [inv_smul_eq_iff] using apply_eq_of_mem_fracSpan (conjForm μ' g) μ (funext (by simp [h]))
      (le_saturateBy (mk_one_mem_ainfLattice t))⟩

lemma kisinAinf_le_fracSpan : L.kisinAinf ≤ L.fracSpan := fun _ ⟨⟨_, ⟨_, rfl⟩, h⟩, _⟩ ↦
  ⟨_, by simp, h⟩

instance : IsTorsionFree Ainf L.Ambient := .trans_faithfulSMul _ WittCFlat (_ ⊗ _)

/-- Frame theorem, h the least bound of |jumps|: M = A_inf N, τ^h M ⊂ A_inf⊗L, τ^h(A_inf⊗L) ⊂ M,
E^h φN ⊂ N. Also: S-linear maps A_inf → S keep relations, crystalline forms test
divisibility in M, and for 3e ≤ p^l, eA ≤ p^l δ the vectors invariant modulo t^A span the
`valueFieldPoints` of φ^l(M) up to p^{4δ}.

Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. -/
lemma frame_theorem : ((∀ (f : _ →ₗ[k.S] k.S) {ι : Type} [Fintype ι] (v : ι → _) (c : ι → Ainf),
  (∀ i, v i ∈ L.valueFieldPoints fracSpan) → ∑ i, c i • v i = 0 → ∑ i, f (c i) • v i = 0) ∧ (∀ l A
  δ, 3 * k.e ≤ p ^ l → k.e * A ≤ p ^ l * δ → ∀ x ∈ L.valueFieldPoints (frobKisinAinf l), p ^ (4 * δ)
  • x ∈ span k.S {y ∈ L.valueFieldPoints (frobKisinAinf l) | ∀ μ ∈ forms, ∀ g : Γ', toGp g.1 • μ y -
  μ y ∈ hodgeFil A}) ∧ L.kisinAinf = span _ L.kisinModule ∧ (∀ μ ∈ crysForms, ∀ y ∈ L.kisinModule,
  ∃ s ∈ k.bicommutant, k.E.1 ^ L.jumpBound • μ y = algebraMap _ _ s) ∧ ∀ d, (∀ {m r}, ainfToBPlus
  d ∣ ainfToBPlus (k.E.1 ^ m * r) → d ∣ r) → ∀ x ∈ kisinAinf, (∀ μ ∈ L.crysForms, k.E.1 ^
  (2 * L.jumpBound) • μ x ∈ BPlus ∙ algebraMap _ _ d) → x ∈ d • kisinAinf) ∧ (∀ x ∈ kisinAinf, tau ^
  L.jumpBound • x ∈ L.ainfLattice) ∧ (∀ x ∈ ainfLattice, tau ^ L.jumpBound • x ∈ L.kisinAinf) ∧
  ∀ x ∈ L.kisinModule, k.frobEUnit 0 ^ L.jumpBound • FrobGroup.φ • x ∈ kisinModule := by
  set a := L.jumpBound
  let e := finBasis ℤ_[p] L.Carrier
  obtain ⟨M, U, v, hM, hv, hU, eU⟩ := isChartOf.exists_isPeriodMatrix a a (ρ := .comp (overZp _) _)
    (L.inClass.1.mono le_sup_right :) e (Nat.sInf_mem exists_jump_bound)
  obtain ⟨Q, Q', Z, Y, B, hQ, hZ, eZ, X, hB, hG⟩ := hU.exists_frame
  let s := Fintype.linearCombination Ainf (M := L.Ambient) (DiagTensor.mk 1 ∘ e)
  have hs : ainfLattice = s.range := by simp [ainfLattice_eq_span_basis, s, e]
  choose n hn using by simpa [← map_pow] using (((isUnit_WittCFlat_of_not_p_dvd not_p_dvd_tau).pow
    a).smul_bijective.2 <| s <| Qᵀ ·)
  let ν m := Fintype.linearCombination Ainf ((FrobGroup.φ • ·)^[m] ∘ n)
  have hν m t : (FrobGroup.φ ^ m • tau ^ a) • ν m t = s (Q.map (FrobGroup.φ ^ m • ·) *ᵥ t) := by
    simp [ν, smul_sum, smul_comm _ (t _), ← frobGroup_smul_smul, hn, ↓mulVec_eq_sum, -smul_pow']
    simp [s, smul_sum]
  have hν₀ := by simpa [ν] using hν 0
  let ψ m := (algebraMap _ BdR).comp (toRingHom FrobGal Bcris (.ofAdd m, 1))
  have I m {μ} : μ ∈ L.forms ↔ _ := forall_comm.trans (forall_congr' fun g ↦
    (equivariant_iff_basisValues (M.isUnit.map
    (ψ m).mapMatrix) (by simpa [ψ, smul_smul, ↓map_mul,
    @MulAction.compHom_smul_def _ _ Bcris] using! congr((ψ m).mapMatrix $(hM g)))).trans funext_iff)
  have G' μ m t : (k.frobE m).1 ^ a • μ (ν m t) = basisValues μ ᵥ* (ψ m).mapMatrix M ⬝ᵥ (↑) ∘
    (Z.map frobEnd^[m] *ᵥ ainfToBPlus ∘ t) := by
    have F := congr((k.frobE m).1 ^ (a + a) • μ $(hν m t) - basisValues μ ⬝ᵥ (ψ m).mapMatrix
      ($(eZ).map (↑)) *ᵥ t • 1)
    rw [Matrix.map_mul, eU, map_mul, ← mulVec_mulVec, dotProduct_mulVec] at F
    apply (((isUnit_smul_of_dvd_mu 1 ⟨_, hv.symm⟩).pow a).map (ψ m)).mul_left_cancel
    linear_combination (norm := (simp [s, ψ, smul_def', ↓map_apply, e, frobE_eq,
      FrobGroup.phi_pow_smul, mul_sum,
      ↓RingHom.mapMatrix_apply, FrobGal.smul_def, sum_mul, mul_comm (μ _)]; ring_nf)) F
  have G := by simpa [ν, smul_def'] using (G' · · <| Pi.single · 1)
  have K m {μ ν} hμ := mem_valueField_of_fixed ((@I m μ).1 hμ · ν)
  have hN i : n i ∈ L.kisinAinf := ⟨⟨_, ⟨a, rfl⟩, by simp [*]⟩, fun m μ hμ ↦
    (mul_mem_hodgeFil_iff_of_not_frobE_dvd (not_frobE_dvd_frobE_of_ne m.succ_pos.ne) a).1 (by
    simpa [G] using! sum_mem fun ν _ ↦ mul_mem_hodgeFil (K _ hμ).1 algebraMap_mem_hodgeFil_zero)⟩
  have hP l i : FrobGroup.φ ^ l • n i ∈ valueFieldPoints (frobKisinAinf l) := ⟨by
    simp [frobKisinAinf, *], fun μ hμ ↦ by simpa using (div_mem (G μ l i ▸ sum_mem fun ν _ ↦ mul_mem
    (K l hμ).2 (Subfield.subset_closure (.inr ⟨(⟨_, Set.MapsTo.iterate @k.frobEnd_mem_bicommutant l
    (hZ ν i)⟩, 1), by simp⟩)) :) (phiInvToBdR_mem_valueField (k.frobE l ^ a)))⟩
  have H m (W : Submodule BPlus _) t (H : ∀ μ ∈ L.crysForms, μ (ν m t) ∈ W) i :
    phiInvToBdR 0 (k.frobE m ^ (a + a) * t i) ∈ W := by
    choose μ hμ using (exists_functional_extend <| .comp (algHom ..).toLinearMap <| e.constr ℕ <|
      frobEnd^[m] ∘ M.2 ·)
    have R ν : basisValues (μ ν) ᵥ* (ψ m).mapMatrix M = (1 : Matrix ..) ν := funext fun l ↦ by
      simpa [ψ, FrobGal.smul_def, *, e, Matrix.mul_apply] using! congr(ψ m ($(M.4) ν l))
    convert sum_smul_mem W (Y.map frobEnd^[m] i) fun ν _ ↦ W.smul_of_tower_mem ((k.frobE m).1 ^ a)
      (H _ ⟨by simp [I m, ↓R], _, hμ ν⟩)
    simpa [-mulVec, ↓G', ↓R, ↓map_mul, ← mulVec_mulVec, frobE_eq, algebraMap_eq_diagonal,
      FrobGroup.phi_pow_smul, ↓mulVec.eq_1 (Y.map _), smul_def'] using
      congr(((((frobEnd ^ m).mapMatrix $X.symm *ᵥ ainfToBPlus ∘ t) i :) : BdR))
  have h₂ x : x ∈ L.ainfLattice → ∃ t, ν 0 t = tau ^ a • x := hs ▸ fun ⟨α, h⟩ ↦ ⟨_, by
    simpa [h, hQ, pow_add] using! hν₀ (Q' *ᵥ α)⟩
  refine and_assoc.2 ⟨?X, ?_⟩
  exact fun f _ _ v c hv e ↦ (fracSpan.sum_smul_mem (f <| c ·) (t := univ) fun i _ ↦ (hv i).1).elim
    fun r ⟨hr, E⟩ ↦ (h₂ _ E).rec fun t E ↦ by simpa [ν, by simpa using hr, by simpa using (H 0 ⊥
    t fun μ J ↦ by simp [E, smul_def', by simpa using (sum_map_mem_of_valueField f _ _ (hv · |>.2 _
    J.1) (W := ⊥) (by simpa [smul_def'] using congr(μ $e)))])] using E.symm
  have S := @mem_span_range_iff_exists_fun.{0}
  have K' w t h := (pi_dvd_iff.2 h : (fun _ ↦ w) ∣ t).imp fun s e ↦ (congr(ν 0 $e).trans
    (map_smul ..)).symm
  have e₀ := L.kisinAinf.span_eq_of_le (Set.range_subset_iff.2 hN) fun x f@⟨⟨_, ⟨N, rfl⟩, h⟩, _⟩ ↦
    (by
    rw [smul_smul, ← pow_add, S]
    induction' a + N with N ih <;> simp [pow_succ', ν]
    exact fun t h ↦ ih (by simpa [h, ν] using (K' _ t fun i ↦ tau_dvd_of_theta_frobEnd fun m ↦ by
      simpa [frobE_dvd_iff, FrobGroup.phi_pow_smul, mt frobE_dvd_iff.2 (not_frobE_dvd_frobE_of_ne
        m.succ_pos.ne)] using! phiInvToBdR_mem_hodgeFil_one_iff.1 (H (m + 1)
      ((hodgeFil 1).restrictScalars _) (FrobGroup.φ ^ (m + 1) • t ·) (by
      simp [h, ν, ← frobGroup_smul_smul, ← smul_sum]
      simpa [smul_def'] using (mul_mem_hodgeFil (phiInvToBdR_mem_hodgeFil_one_iff.2
        (frobE_dvd_phi_pow_tau m.succ_pos)) <| (smul_mem _ (tau ^ N)
      f).2 m · ·.1)) i))) : _ → _) (h₂ _ h)
  have D l := (valueFieldPoints _).span_eq_of_le (Set.range_subset_iff.2 (hP l)) fun x hx ↦
    have ⟨t, e⟩ := (S _).1 (e₀.ge hx.1)
    (S _).2 ⟨_, by simpa [add_eq_zero_iff_eq_neg'] using (?X k.coord₀ (Option.rec _ _)
      (FrobGroup.φ ^ l • ·.elim (-1) t) (.imp_left ((show frobKisinAinf l ≤ fracSpan from fun _
      h ↦ by simpa using smul_mem_fracSpan (FrobGroup.φ ^ l) (kisinAinf_le_fracSpan
      h)) ·) <| ·.rec hx (hP l)) (by simp [← frobGroup_smul_smul, ← smul_sum, e]))⟩
  simp only [↓← D, ↓← by simpa [frobKisinAinf_zero] using D 0, span_span_of_tower, ← e₀,
    forall_exists_index,
    mem_smul_pointwise_iff_exists, S, forall_apply_eq_imp_iff, exists_exists_eq_and]
  refine ⟨⟨fun l A δ b d c ↦ ?_, ⟨⟩, fun μ ⟨hμ, l, E⟩ c ↦ ?_, fun d D t h ↦ K' _ t fun i ↦ D
    (map_dvd _ (D ((mem_span_singleton.1 (H 0 _ ((_ : Ainf) • t) (by simpa [-map_sum] using! h)
    i)).imp fun y h ↦ algebraMap_injective _ BdR (by simpa [frobE, commutes y, smul_def'] using
    h.symm))))⟩, by simp [*], h₂, fun c ↦ ⟨B *ᵥ k.φ ∘ c, by
    simpa [mul_comm _ v.1, mul_comm _ tau, frobGroup_phi_smul, hB, ← hv, ← hν₀, ← mulVec_mulVec,
      mul_pow, ↓frobEUnit_pow_smul, Units.smul_def, smul_sum (r := FrobGroup.φ), «φ», frobE,
      ν] using (hν 1 (FrobGroup.φ • c ·)).symm⟩⟩
  obtain ⟨V, D, hD, eV, R⟩ := radius_lemma (fixes _) (by simpa using
    (exists_smul_z 1).choose_spec) hZ X (hG _ (fixes _)).choose_spec b a
  refine (map_nsmul (Fintype.linearCombination ..) ..).subst (mapsTo_span (fun y ↦ Exists.rec
    fun r h ↦ ⟨⟨y, rfl⟩, fun μ hμ g ↦ ?_⟩) (R A δ d c))
  choose w f using h
  simpa [by simpa [-mulVec, -mulVec_add, ν, eV, ← mulVec_mulVec, eq_add_of_sub_eq' (funext f : _ =
    (_ : BPlus) • w), algebraMap.smul, ← smul_sum] using G' μ l (y ·), ↓mulVec_add, mul_add, frobE,
    smul_sum, ← by simpa using (I l).1 hμ g, by simpa [← ext_iff] using hD _ (fixes g).1] using
    (fun F ↦ sub_mem (smul_mem_hodgeFil (toGp g) F) F) (sum_mem
    fun ν _ ↦ mul_mem_hodgeFil (K l hμ).1 (mul_mem_hodgeFil (frobE_zpow_mem_hodgeFil 0 A)
    (@algebraMap_mem_hodgeFil_zero _ _ ↑(D ν ⬝ᵥ w))))
  choose s f S using (isChartOf.exists_mem_bicommutant_of_fixed (b := ∑ i,
    l (e i) * M i ·) fun g ↦ by simpa [E, ψ, ← map_mul, ← map_sum] using ((I 0).1 hμ g _).symm)
  exact ⟨s ⬝ᵥ Z *ᵥ ainfToBPlus ∘ (c ·), by simp (maxDischargeDepth := 4) [sum_mem, mul_mem, *], by
    simpa [E, e, ψ, ← map_mul, ← map_sum, ← S] using! G' μ 0 (c ·)⟩
end Lift.KummerChart.JumpLattice
end

section
/-! Part of: Kisin modules: Galois action trivial modulo the variable, Hodge–Tate weights read off
(known result; see Lib.PadicHodge.WachGamma.Letters).

This file: Galois stability of the Kisin lattice; congruence step towards triviality modulo the
variable. -/

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {L :
  Lift.KummerChart.JumpLattice O} {x μ g} (hg : ∀ h ∈ k.Γ', g * h * g⁻¹ ∈ k.Γ')

namespace Lift.KummerChart.JumpLattice

lemma pow_smul_gal_sub_mem_span_of_dvd {g : Gp p} {d m x} (o : ∀ {y}, y ∈ k.bicommutant →
  d ∣ g • y - y) : (∃ s ∈ k.bicommutant, k.E.1 ^ m • x = algebraMap _ BdR s) → k.E.1 ^ (2 * m) •
  (g • x - x) ∈ BPlus ∙ algebraMap _ _ d := fun ⟨s, f, e⟩ ↦ Submodule.mem_span_singleton.2 (by
  obtain ⟨_, ⟨v, _⟩, ⟨r, _⟩, t, _⟩ := congr(g • $e), pow_dvd_pow_of_dvd (k.associated_smul_E g).dvd'
    m, o (k.ainfToBPlus_mem_bicommutant (k.E ^ m)), o f
  apply_fun algebraMap _ BdR at *
  use v • (k.E.1 ^ m • t - r * s)
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, pow_mul'] at *
  grind)

include hg

lemma conjForm_mem_forms (h : μ ∈ L.forms) : conjForm μ g ∈ L.forms := fun t s ↦ by
  simpa [mul_smul, inv_smul_eq_iff] using h (L.ρ g t) ⟨_, hg _ s.2⟩

/-- If g in Γ satisfies gΓ'g⁻¹ ⊂ Γ', then g maps the module `Lift.KummerChart.JumpLattice.kisinAinf`
of L into itself. -/
lemma smul_mem_kisinAinf : x ∈ kisinAinf → FrobGroup.inr g • x ∈ L.kisinAinf :=
  .imp (fun ⟨_, ⟨n, rfl⟩, s⟩ ↦ mem_saturateBy_of_smul (by simp [associated_smul_tau.pow_pow.dvd])
  ⟨n, rfl⟩ (le_saturateBy (frobGroup_smul_smul .. ▸ smul_mem_ainfLattice _ s))) fun h n _ e ↦ by
  simpa [smul_smul, ((FrobGroup.phi_mul_comm _).pow_left _).eq] using
    smul_mem_hodgeFil (toGp g) (h n _ (conjForm_mem_forms hg e))
end Lift.KummerChart.JumpLattice
end

section
/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Lattices with prescribed exponents at each E_a, cost of Galois steps, retraction API. -/

noncomputable section

open Finset Algebra MulAction MulSemiringAction NeZero Pointwise Polynomial Set Submodule
  Lift.FrobGroup

attribute [-instance] NormedAlgebra.toAlgebra NormedSpace.toModule SubsemiringClass.toCommSemiring

attribute [-simp] IsUnit.dvd IsUnit.dvd_mul_left IsUnit.mul_left_dvd span_coe_eq_restrictScalars
  map_smul pow_eq_one_iff smul_algebraMap

variable {p} [P : ThePrime p] [Γ : GroupOverGp p] [k : Lift.KummerChart Γ]

/-- The cost of the step n at p_a = φ^a(E): the number v_p(n) + d + 3a, with v_p(0) = 0 and d =
`Lift.KummerChart.differentExp`. -/
def Lift.KummerChart.cost a n := padicValInt p n + (differentExp + 3 * a)

seal WittVector.eval

variable {O} {L : Lift.KummerChart.JumpLattice O} (l i a) {n : ℤ} (c : ℕ → ℤ → ℤ)

/-- For n ≠ 0 there are g in Γ', a unit ω and υ, X in A_inf with g p_a = ω p_a, p_a ∣ gs − s for
all s in S, zτX = ω^n − 1, and υX ≡ p^{cost(a,n)} modulo p_a = φ^a E. -/
lemma Lift.KummerChart.exists_depth_step (hn : n ≠ 0) : ∃ g : galMonoid, ∃ ω : _ˣ, ∃ υ X,
  g • (k.frobE a).1 = ↑ω * k.frobE a ∧ (∀ s : k.S, (k.frobE a).1 ∣ g • s - s) ∧
  (k.frobE a).1 ∣ υ * X - p ^ cost a n ∧ zTau * X = (ω ^ n).1 - 1 := by
  obtain ⟨⟨g, hg⟩, ⟨F, ⟨G, hG⟩, T⟩, ⟨t, ht⟩, u, he⟩ := exists_smul_z (p ^ a),
    exists_derivative_dvd_p_pow,
    exists_add_pow_prime_eq P.out (theta tau) 1, k.associated_E_mul_tau_mu
  obtain ⟨⟨ω, h₀⟩, D⟩ := k.associated_smul_E (toGp g.1), zTau_mul_E_dvd_smul_sub ⟨_, g, rfl⟩ k.E
  erw [← h₀, ← mul_sub_one, mul_comm, mul_dvd_mul_iff_left k.E_ne_zero] at D
  have A : Associated (ω.1 ^ n.natAbs - 1) ((ω ^ n).1 - 1) :=
    n.rec (by simp) (⟨-ω⁻¹ ^ ·.succ, by simp [sub_mul, ← mul_pow]⟩)
  obtain ⟨⟨X, hX⟩, r, hr⟩ := (k.zTau_dvd_phi_pow_smul a).trans
    (_root_.map_dvd (toRingHom _ _ («φ» ^ a)) ((D.trans (sub_one_dvd_pow_sub_one ..)).trans A.dvd)),
    (F.map (algebraMap ..)).binomExpansion k.z.1 (toGp g • k.z - _)
  have ⟨υ, _⟩ := theta_surjective.exists.1 (?_ : thetaPhiInv a X ∣ p ^ cost a n)
  use ⟨_, g, rfl⟩, .map (toRingHom _ _ («φ» ^ a)).1 ω, «φ» ^ a • υ, X, by
    erw [frobE_eq, smul_phi_pow_comm, ← h₀]; simp [mul_comm], k.dvd_smul_sub_of_fixesLambda (hg ▸ by
    simp [frobE_dvd_iff, ← iterate_frobEnd_teichmuller, ← phi_pow_smul]) (fixes g).1, by
    simp [frobE_dvd_iff, *, mul_comm], by simp [← hX, smul_sub, ← map_zpow]
  grw [← mul_dvd_mul_iff_left (not_frobE_dvd_zTau a ∘ frobE_dvd_iff.2), ← map_mul, ← hX,
    toRingHom_apply, thetaPhiInv_phi_pow, A.dvd', lifting_the_exponent theta_surjective ω k.z
    k.chart.4 (dvd_of_mul_left_dvd D) (D.rec fun d e ↦ by
    simp [e, zTau, mul_pow]; grw [← sub_eq_of_eq_add (sub_eq_of_eq_add ht),
      ← pow_dvd_pow (theta k.z) P.out.two_le, ← dvd_pow_self (theta d) out]
    use -t; simp [tau, (map_pow _ epsRoot p).symm.trans untilt_epsTilt]; ring) (by omega)]
  erw [add_sub_cancel, eval_map_algebraMap, aeval_algHom_apply (AlgHom.mk (toRingHom ..) (fixes
    g).1), hg, ← sub_one_mul, ← mul_geom_sum, ← mu, ← he, toRingHom_apply] at hr
  simp [hG, ← h₀, k.E_ne_zero, mul_assoc, mul_left_comm _ k.E.1, ← mul_add, sq] at hr
  apply_fun theta at hr
  simp [k.theta_E, k.smul_theta_of_fixesThetaZ (fixes g), ← sub_eq_iff_eq_add', ← sub_one_mul] at hr
  grw [map_sub, map_one, Dvd.intro _ hr, T, u.coe_dvd (a := 1), cost, padicValInt]
  cases a; simp [zTau]; ring_nf; rfl
  grw [k.theta_z_dvd_p, tau_dvd_xi_sub_p]
  simp +arith [← pow_succ, ← pow_succ', ← pow_add, pow_dvd_pow, dvd_mul_of_dvd_right]

/-- There are p^{d+3a} elements t_l of Γ', d = `Lift.KummerChart.differentExp`, such that φ^a(E)
divides g(∑ t_l s) − ∑ t_l s in A_inf for all g in Γ' and s in S. -/
lemma Lift.KummerChart.exists_depth_step_zero : ∃ t : Fin (p ^ cost a 0) → galMonoid,
  ∀ (g : galMonoid) (s : k.S), (k.frobE a).1 ∣ g • ∑ l, t l • s.1 - ∑ l, t l • s.1 := by
  choose t _ using exists_smul_z
  use (⟨_, t ·, rfl⟩), fun ⟨_, g, rfl⟩ s ↦ (k.exists_dvd_sub_sum_z_pow a rfl s).rec fun w e ↦ ?_
  simp [frobE_dvd_iff, k.dvd_iff_coe_dvd] at *
  simp_rw [e, smul_sum (r := toGp (t _).1)]; rw [sum_comm, smul_sum]; congr! with m
  obtain ⟨n, e⟩ | h := em (p ^ a ∣ m)
  simp [e, pow_mul, ← phi_pow_smul_z, smul_def', ← thetaPhiInv_smul, fixes]
  have Z := by simpa [← theta_teichmuller, ← thetaPhiInv_phi_pow a, phi_pow_smul, ne,
    ← map_pow, ← ofAdd_nsmul] using isPrimitiveRoot_untilt_epsPow (.ofAdd (p ^ a)⁻¹)
  have := (mul_geom_sum (_ ^ m.1 : OC) (p ^ cost a 0)).trans (by
    rw [pow_right_comm, (Z.pow_eq_one_iff_dvd _).2 (by simp +arith [cost, pow_dvd_pow])])
  simp_all [← mul_sum, ← sum_mul, pow_right_comm _ _ m, sum_range,
    ← Z.pow_eq_one_iff_dvd, ← thetaPhiInv_smul, mul_pow, smul_def', fixes]

namespace Lift.KummerChart.JumpLattice

/-- The x in `kisinLocAinf` (A_inf·𝒩, 𝒩 = `kisinLoc`) at the letter i with exponents c:
μ(φ^{−a}x) ∈ t^{c(a,u)}B_dR^+ for all a
and all forms μ of type u ∈ U at σ^{−a}i, the letter a steps before i (`Letter.stepBack`). -/
def withExponents : Submodule Ainf L.Ambient := L.kisinLocAinf ⊓ L.letterPart i ⊓ ⟨⟨⟨{x | ∀ a,
  ∀ u ∈ L.U (i.stepBack a), ∀ μ ∈ L.formsOfType (i.stepBack a) u, valueAt a μ x ∈ hodgeFil
  (c a u)}, by aesop⟩, by simp⟩, by simp_all [valueAt, frobGroup_smul_smul, smul_of_tower_mem]⟩

/-- The S-module of x in `Lift.KummerChart.JumpLattice.kisinLoc` at the letter i with the standard
exponents of level l: 0 at φ^a E for a < l, −u for a ≥ l. -/
abbrev locLetterPart := L.kisinLoc ⊓ (withExponents i (stdExponent l)).restrictScalars _

variable {a : ℕ} {i : Letter} {c : ℕ → ℤ → ℤ} {l : ℕ} {n u : ℤ} {L' c' μ} {x : L.Ambient} {g :
  galMonoid} (F : L.Hom L')

@[simp] lemma valueAt_zero : L.valueAt 0 μ x = μ x := by simp [valueAt]

lemma frobE_smul_mem_kisinLocAinf_iff : (k.frobE a).1 • x ∈ kisinLocAinf ↔ x ∈ kisinLocAinf :=
  ⟨mem_saturateBy_of_smul dvd_rfl (by bound), smul_mem _ _⟩

lemma frobEUnit_zpow_smul_mem_kisinLoc : k.frobEUnit a ^ n • x ∈ L.kisinLoc ↔ x ∈ L.kisinLoc :=
  mem_stabilizer_set.1 (zpow_mem (mem_stabilizer_set.2 fun _ ↦
  .symm ⟨smul_mem _ _, .imp frobE_smul_mem_kisinLocAinf_iff.1 (by
  simpa [phiInvToBdR, smul_def'] using
    flip div_mem (phiInvToBdR_mem_valueField (k.frobE a)) <| · · ·)⟩) n) x

lemma Hom.wittMap_mem_kisinLocAinf : x ∈ L.kisinLocAinf → F.wittMap x ∈ L'.kisinLocAinf :=
  .imp fun _ ↦ .imp_right (by simpa using F.map_mem_kisinAinf ·)

lemma Hom.wittMap_mem_kisinLoc : x ∈ L.kisinLoc → F.wittMap x ∈ L'.kisinLoc :=
  .imp F.wittMap_mem_kisinLocAinf fun h _ ↦ h _ ∘ F.comp_wittMap_mem_forms

lemma gal_smul_mem_kisinLocAinf (hx : x ∈ kisinLocAinf) :
  g • x ∈ kisinLocAinf := have ⟨_, _, rfl⟩ := g
  saturateBy_induction hx (fun _ ↦ le_saturateBy ∘ smul_mem_kisinAinf (by bound)) fun a _ ↦
    mem_saturateBy_of_smul (associated_smul_of_dvd _ (by simp [frobE_dvd_iff,
    (@frobE_dvd_iff p _ k.chart).1])).dvd (by bound) ∘ (frobGroup_smul_smul ..).subst

lemma mem_withExponents_of_mem_hodgeFil (h : x ∈ withExponents i c) (H : ∀ a,
  ∀ u ∈ L.U (i.stepBack a), c a u < c' a u → ∀ μ ∈ L.formsOfType (i.stepBack a) u,
  valueAt a μ x ∈ hodgeFil (c' a u)) : x ∈ withExponents i c' := h.imp_right fun h a u v ↦
  (lt_or_ge ..).elim (H a u v) (hodgeFil_anti · <| h a u v · ·)

lemma mem_withExponents_of_le (h : x ∈ withExponents i c) (H : ∀ a, ∀ u ∈ L.U (i.stepBack a), c' a
  u ≤ c a u := by grind) : x ∈ withExponents i c' := mem_withExponents_of_mem_hodgeFil h (by grind)

lemma valueAt_mem_hodgeFil_of_mem_ainfLattice (e : μ ∈ formsOfType (i.stepBack a) u) (hx :
  x ∈ ainfLattice) (hi : x ∈ letterPart i) :
  valueAt a μ x ∈ hodgeFil (-u) := congr(μ $(mem_letterPart_iff_letterProj.1
  (phi_pow_smul_mem_letterPart_iff.1 (by simpa)))).subst (mem_span.1 (smul_mem_ainfLattice _ hx)
  (((hodgeFil ..).restrictScalars _).comap (μ ∘ₗ L.letterProj _)) (fun _ ⟨k, h⟩ ↦ h ▸ e.2 k))

/-- Let F: L → L' be an equivariant map of lattice data, the jump set of L' lying in that of L
at every letter. Then F sends elements with exponents c at the letter i to elements with
exponents c at i. -/
lemma Hom.map_mem_withExponents (e : L'.U ≤ L.U) : x ∈ L.withExponents i c →
  F.wittMap x ∈ L'.withExponents i c := .imp (by
  simp_all [wittMap_mem_kisinLocAinf, mem_letterPart_iff_letterProj, ← wittMap_letterProj])
  (by simp_all [← valueAt_comp_wittMap, e _ _, formsOfType, comp_wittMap_mem_forms])

/-- Saturation: let r in A_inf be prime to φ^a E for all a, and let x lie in
`Lift.KummerChart.JumpLattice.kisinLocAinf`. If rx has exponents c at the letter i, then so does
x. -/
lemma mem_withExponents_of_smul {r} (hr : ∀ a, ¬(k.frobE a).1 ∣ r) (hx : x ∈ kisinLocAinf) (H :
  r • x ∈ withExponents i c) :
  x ∈ withExponents i c := by simp_all [withExponents, mem_letterPart_iff_letterProj,
  (by aesop : r ≠ 0), zpow_one (phiInvToBdR _ r) ▸ mul_mem_hodgeFil_iff_of_not_frobE_dvd (hr _) 1]

/-- If x has exponents c at the letter i (`Lift.KummerChart.JumpLattice.withExponents`), then (φ^b
E)^m·x, m an integer, has any exponents c' with c'(a,u) ≤ c(a,u) + m for a = b and c'(a,u) ≤ c(a,u)
otherwise, u in the jump sets. -/
lemma frobEUnit_zpow_mem_withExponents b m (hx : x ∈ withExponents i c) (H : ∀ a,
  ∀ u ∈ L.U (i.stepBack a), c' a u ≤ c a u + if b = a then m else 0 := by clear * -; grind) :
  k.frobEUnit b ^ m • x ∈ withExponents i c' := hx.imp (.imp (mem_stabilizer_set.1 (zpow_mem
  (mem_stabilizer_set.2 fun _ ↦ frobE_smul_mem_kisinLocAinf_iff) m) x).2 (by simp_all
  [mem_letterPart_iff_letterProj])) fun _ a u v _ _ ↦ hodgeFil_anti (H a u v) (by split <;> simp_all
  [valueAt_frobEUnit_zpow_smul, add_comm, mul_mem_hodgeFil, frobE_zpow_mem_hodgeFil,
  mul_mem_hodgeFil_iff_of_not_frobE_dvd, not_frobE_dvd_frobE_of_ne, eq_comm])

lemma kisinLocAinf_le_fracSpan : L.kisinLocAinf ≤ L.fracSpan := fun _ ↦
  (saturateBy_induction · kisinAinf_le_fracSpan fun _ _ ↦ mem_saturateBy_of_smul dvd_rfl (by simp))

lemma valueAt_smul_sub (hx : x ∈ kisinLocAinf) (e : μ ∈ L.forms) : valueAt a μ (g • x - x) = g •
  valueAt a μ x - valueAt a μ x := form_gal_smul g e (smul_mem_fracSpan _ (kisinLocAinf_le_fracSpan
  hx)) ▸ (map_sub ..).trans congr(μ $(by simp [inv_smul_eq_iff, ← smul_phi_pow_comm]) - _)

lemma smul_sub_mem_withExponents (hx : x ∈ withExponents i c) (g : k.galMonoid) : g • x - x ∈
  withExponents i c := show _ ∧ _ by simp_all [withExponents, formsOfType, gal_smul_mem_letterPart,
  ↓valueAt_smul_sub, sub_mem_iff_left, galMonoid_smul_mem_hodgeFil, gal_smul_mem_kisinLocAinf]

/-- For x in 𝒩 and g in Γ', gx − x is divisible by zτ in A_inf·𝒩, i.e. (gx − x)/(zτ) lies in
A_inf·𝒩: the factor zτ can be split off. -/
lemma smul_sub_mem_zTau_kisinLocAinf (g : k.galMonoid) (hx : x ∈ L.kisinLoc) : k.zTauUnit⁻¹ •
  (g • x - x) ∈ kisinLocAinf := saturateBy_induction hx.1 (fun x m b ↦ have ⟨_, γ, rfl⟩ := g
  frame_theorem.1.2.2.2.rec fun u v ↦ le_saturateBy (mem_smul_set_iff_inv_smul_mem.1 (v _ (pow_one
    k.z.1 ▸ k.chart.tau_mul_z_pow_dvd) _ (sub_mem (smul_mem_kisinAinf (by bound) m) m) fun μ e ↦
    map_sub μ .. ▸ form_gal_smul ⟨_, γ, rfl⟩ e.1 (kisinAinf_le_fracSpan
    m) ▸ pow_smul_gal_sub_mem_span_of_dvd (k.tau_mul_z_dvd_smul_sub (fixes _)) (u μ e x ⟨m, b.2⟩))))
  (fun a y H e ↦ (zTau_mul_E_dvd_smul_sub g (k.frobE a)).rec
  fun c f ↦ by simpa [smul_distrib_smul, eq_add_of_sub_eq' f, add_smul, mul_assoc, mul_smul k.zTau,
  ← zTauUnit_smul, add_sub_right_comm, ← smul_sub, smul_comm _ (k.frobE a).1,
  frobE_smul_mem_kisinLocAinf_iff, add_mem_cancel_right,
  smul_mem, gal_smul_mem_kisinLocAinf e.1] using H (smul_mem _ _ e)) hx

seal SMul.comp.smul

lemma phi_pow_mem_kisinLoc (hx : x ∈ kisinLoc) : φ ^ l • x ∈ kisinLoc := by
  induction' l with l ih <;> simp [pow_succ', mul_smul, hx]
  exact saturateBy_induction ih.1 (fun y m b ↦ frobEUnit_zpow_smul_mem_kisinLoc (n :=
    .ofNat _).1 (.imp_left le_saturateBy (frame_theorem.2.2.2 y
    ⟨m, b.2⟩))) (fun a y H e ↦ frobEUnit_zpow_smul_mem_kisinLoc (n := 1) (a := a.succ).1
    (by simpa [frobE_eq, pow_succ', mul_smul, frobGroup_smul_smul] using H (smul_mem _ _ e))) ih

lemma span_kisinLoc : span _ ↑L.kisinLoc = L.kisinLocAinf := span_eq_of_le _ (sep_subset ..) fun _ ↦
    (saturateBy_induction · (frame_theorem.1.2.2.1.trans_le (span_mono fun _ ↦
  .imp_left le_saturateBy)) fun a _ ↦
  (by simpa [← frobEUnit_smul] using
  mapsTo_span (f := k.frobEUnit a ^ (-1) • .id) (fun _ ↦ frobEUnit_zpow_smul_mem_kisinLoc.2) ·))

lemma valueAt_mem_valueField (hμ : μ ∈ forms) (hx : x ∈ kisinLoc) : valueAt a μ x ∈ valueField a :=
  have ⟨r, hr, e⟩ := smul_mem_fracSpan («φ» ^ a)⁻¹ (kisinLocAinf_le_fracSpan hx.1)
  have ⟨_, t, v, E⟩ := mem_span_set'.1 (span_kisinLoc.ge (le_saturateBy (frame_theorem.2.2.1 _ e)))
  (not_forall.1 · |>.elim fun i m ↦ mem_of_eq_of_mem ((eq_inv_mul_iff_mul_eq₀ (by simpa)).2 (by
  simpa [S_smul,
    neg_add_eq_zero, -LinearMap.map_smul_of_tower] using congr(valueAt a μ $(frame_theorem.1.1
   (k.adicBasis.coord i) (Option.rec _ _) («φ» ^ a • ·.elim (-(tau ^ L.jumpBound * r)) t)
    (.imp_left (kisinLocAinf_le_fracSpan ·) <| ·.rec hx (phi_pow_mem_kisinLoc <| v · |>.2))
    (by simpa [smul_sum, frobGroup_smul_smul, smul_smul, neg_add_eq_zero] using
    congr(«φ» ^ a • $E.symm)))))) (mul_mem (inv_mem (phiInvToBdR_mem_valueField _))
    (sum_mem fun l _ ↦ mul_mem (phiInvToBdR_mem_valueField _) (valueField_zero_le (by simp [valueAt,
    (v l).2.2, *]))))) (mt k.adicBasis.eq_zero_of_coord (by simp_all [smul_eq_zero_iff_eq]))

lemma exists_coordRetract : ∃ r : kisinLocAinf →ₗ[k.S] L.kisinLoc, ∀ a, ∀ x ∈ kisinLoc, ∀ m,
  (r ⟨a • x, m⟩).1 = k.coord₀ a • x :=
  span_kisinLoc ▸ (LinearMap.exists_range_eq_graph (f := .prod _ (TensorProduct.lift (.lsmul .. ∘ₗ
  k.coord₀))) (surjective_tensorToSpan _ _) (· - · |>.exists_sum_tmul_eq.rec fun _ ⟨_, v, E⟩ ↦ by
  simpa [eq_add_of_sub_eq E, Subtype.ext_iff] using frame_theorem.1.1 _ _ _ (v · |>.2.imp_left
    (kisinLocAinf_le_fracSpan ·)))).imp fun r e a x m _ ↦ congrArg _ (e.le ⟨a ⊗ₜ ⟨x, m⟩, rfl⟩).symm

/-- A chosen S-linear map A_inf·𝒩 → 𝒩 sending a·x to λ₀(a)·x for a in A_inf and x in 𝒩, where
λ₀: A_inf → S is the coordinate of 1. -/
def coordRetract := L.exists_coordRetract.choose

lemma coordRetract_sum {ι} [Fintype ι] {a v : ι → _} (hv : ∀ i, v i ∈ L.kisinLoc) {y} (e : ∑ i,
  a i • v i = y.1) : (coordRetract y).1 = ∑ i, k.coord₀ (a i) • v i := by simp [(by aesop : y = ∑ i,
  a i • ⟨_, (hv i).1⟩), coordRetract, exists_coordRetract.choose_spec, hv]

lemma coordRetract_of_mem_kisinLoc (hx : x ∈ L.kisinLoc) hy : (coordRetract ⟨x, hy⟩).1 = x := by
  simpa [*] using! exists_coordRetract.choose_spec 1 x hx

lemma Hom.map_coordRetract (y : L.kisinLocAinf) (y' : L'.kisinLocAinf) (e : F.wittMap y = y') :
    F.wittMap (coordRetract y) =
  coordRetract y' := have ⟨_, a, v, e₁⟩ := mem_span_set'.1 (span_kisinLoc.ge y.2)
  by simp [coordRetract_sum _ e₁, ← e, ← e₁,
    coordRetract_sum (a := a) (F.wittMap_mem_kisinLoc <| v · |>.2)]

/-- If x has exponents c at i and μ is a form of type u at the letter a steps before i, then
μ(φ^{−a}x) lies in every B_dR^+-submodule W containing t^{c_a(v)}B_dR^+ for all allowed
jumps v ≤ u; u itself need not be allowed. -/
lemma valueAt_mem_of_hodgeFil_le W (hx : x ∈ withExponents i c) (hμ : μ ∈ formsOfType (i.stepBack a)
  u) (H : ∀ v ∈ L.U (i.stepBack a), v ≤ u → hodgeFil (c a v) ≤ W := by grind [hodgeFil_anti.imp]) :
  valueAt a μ x ∈ W := by_contra fun e ↦ have ⟨_, _, f⟩ := kisinLocAinf_le_fracSpan hx.1.1
  have F m := hodgeFil_anti (le_neg.1 (inf_le_right (b := -m)))
    (valueAt_mem_hodgeFil_of_mem_ainfLattice (Int.leInductionDown hμ (fun v l
    f ↦ formsOfType_subset_pred_of_notMem (fun w ↦ e (H v w l (hx.2 a v w μ f))) f) _ inf_le_left) f
    (smul_mem _ _ hx.1.2))
  have ⟨y, _⟩ := mem_hodgeFil.1 (F 0)
  by simp_all [show y = 0 from eq_zero_of_forall_pow_dvd fun _ ↦
    algebraMap_mem_hodgeFil_iff_xi_pow_dvd.1 (by simp_all)]

/-- If x lies in 𝒩, g in Γ', and gx − x has exponents c at the letter i, then (gx − x)/(zτ) also
has exponents c at i. -/
lemma smul_sub_mem_zTauUnit_smul_of_deep (hx : x ∈ L.kisinLoc) (H : g • x - x ∈ withExponents i c) :
    k.zTauUnit⁻¹ • (g • x - x) ∈ withExponents i c := mem_withExponents_of_smul not_frobE_dvd_zTau
  (smul_sub_mem_zTau_kisinLocAinf g hx) (by simpa [← zTauUnit_smul])
end Lift.KummerChart.JumpLattice
end
end
