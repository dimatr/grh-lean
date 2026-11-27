import New.Filling.GlobalToLocal
import New.Weil.OneVector
import New.Filling.SchurTest
import New.Filling.OpenCellBound
import New.Weil.Heights
import New.Weil.BadShare

-- part: New.Filling.FixedLines
section
/-! Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: A group Z between K(g) and K for which `Level.floorZeroForm` Z, divided by the measure of
Z, is smaller than for K by b^(6|κ|) for each given place above q₀ where a frame vector is fixed. -/

open Pi Subgroup Classical ENNReal Finset Fintype Matrix MeasureTheory IntegralPlace

namespace Filling

variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} [S.IsAdmissible] {T T₀ :
  Finset (FinPlace E)} [fT : T.StarStable] [P : IntegralPlace (LocProd T)] {F} [h :
  S.IsFillingLevel T F] (Sg : Finset (S.chosenPlaces 0))

omit [S.IsAdmissible] in
/-- If every place of T is a chosen place above g or the conjugate of one, then b⁹ ≥ 2 and the
non-units of the integers R at T have volume at most b⁻⁹. -/
lemma volume_nonunits_le (k : T ⊆ univ.biUnion fun p : Σ i, S.chosenPlaces i ↦
  {p.2.1, star p.2.1}) : 2 ≤ ENNReal.ofReal (S.b ^ 9) ∧
  volume (P.R \ P.intUnits) ≤ (.ofReal (S.b ^ 9))⁻¹ := by
  have b := S.thousand_le_b
  refine ⟨by grw [← b]; bound, .trans' ?_ (measure_mono_ae (t := ⋃ w, {x | (MulEquiv.piUnits.symm
    (mulSingle w (uniformizer _)) : (LocProd T)ˣ)⁻¹.1 * x ∈ R}) (P.ae_isUnit.mono fun x ⟨y, u⟩ ⟨a,
    n⟩ ↦ by_contra (n ⟨a, y, mem_O_locProd.2 fun j ↦ by_contra fun _ ↦ · ⟨_, ⟨j, rfl⟩,
    mem_O_locProd.2 fun i ↦ by obtain rfl | _ := (eq_or_ne i j) <;> simp_all [mem_O_locProd,
    v_uniformizer_inv_mul_le_one_iff, -map_mul, one_lt_inv_iff₀]⟩, u⟩)))⟩
  grw [measure_iUnion_fintype_le, sum_le_card_nsmul _ _ (.ofReal (S.b ^ 10)⁻¹) fun w _ ↦ ?_,
    card_univ, card_coe, k, card_biUnion_le_card_mul _ _ 2 (by grind),
    ← ofReal_nsmul, ← ofReal_inv_of_pos (by bound)]
  gcongr; simp [S.card_chosenPlaces, field]; bound [S.f_le_b]
  rw [volume_setOf_mul_mem, md_eq_inv_genIndex, genIndex_eq_inv_prod_norm,
    Fintype.prod_eq_single w] <;> simp +contextual [norm_locField_eq_q_zpow, -FinPlace.q_bounds]
  cases' mem_biUnion.1 (k w.2) with p; grw [S.le_levelPrime p.1]; grind [chosenPlaces_q, q_star]

/-- Let 1/g be integral off T₀, and T = T₀ ∩ {w, w̄} if o is a place w ∈ Sg. Some K(g) ≤ Z ≤ K
over T contains k_T for all k reducing into `Filling.fixingSet` Sg d, and kk(Z)·M(K)·c ≤
kk(K)·M(Z), where c = b^(6|κ|), or 1 if o is empty; kk = `Level.floorZeroForm`,
M = `Level.groupMeasure`. -/
lemma IsFillingLevel.exists_intermediateGroup_one_prime (o : Option Sg) d (hT :
  ↑S.gIdele⁻¹ ∈ integralOff T₀) (f : ∀ w ∈ o, ∀ j, j ∈ T ↔ j ∈ T₀ ∧ (j = w
  ∨ star j = w)) : ∃ Z : F.IntermediateGroup,
  (∀ k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ let K := unitaryLevel R 1 _
  F.floorZeroForm Z * F.groupMeasure K * o.elim 1 (fun _ ↦ .ofReal (S.b ^ (6 * 𝔰.k))) ≤
    F.floorZeroForm K * F.groupMeasure Z := by
  let p := (S.toPlaces T).comp S.latStabilizer.subtype
  have r : p.range = unitaryLevel R 1 _ :=
    ext (exists_toPlaces_eq · |>.elim (by simp [p, mem_latStabilizer_iff (T := T)]; aesop))
  obtain _ | ⟨w, m⟩ := o
  use ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩; simp [← r, p]
  obtain ⟨c, o, B⟩ := S.pow_chain, S.one_le_b, S.volume_nonunits_le (by aesop_cat : T ⊆ _)
  let H := (vectorFixer w (d w)).comap S.reduction
  have z r := by simpa [-reduceAt_eq_zero, ← mul_smul_comm, idem_mul_mem_Ô, reduceAboveG] using
    ((S.inv_gIdele_smul_mem_iff (⟨_, idem_mem_Ô {w.1}⟩ * r)).1 · (⟨0, w⟩, false))
  have q : F.congGroup.comap p ≤ H :=
    fun k e ↦ by simp [H, vectorFixer, show S.reduction k .. = 1 from intGL.map_eq_one.2 fun i j ↦
    z _ (by simpa [h.g_eq, apply_ite, ite_apply] using! e.2 i j ⟨w, by_contra
    fun _ ↦ by simpa [Units.smul_def, (mem_integralOff _).1 hT w (by aesop)] using z 1⟩ ⟨⟩)]
  let Z : F.IntermediateGroup := ⟨H.map p, by grw [← q,
    map_comap_eq_self (r ▸ unitaryLevel_le_unitaryLevel_one)], r ▸ H.map_le_range _⟩
  use Z, (⟨·, ·.1 w m, rfl⟩)
  intro K
  -- Z and the non-units are rare, so the form is small against that of K
  nth_grw 1 [Option.elim, pow_le_pow_right₀ o (?_ : _ ≤ 9 * _), pow_mul, ofReal_pow (by bound),
  h.floorZeroForm_le_main_term Z (𝔰.k - 10 ^ 10 * 𝔰.n ^ 4) (by omega), B.2,
    h.inv_two_pow_le_groupMeasure B, mul_right_comm, mul_assoc _ (_ + _),
    (?_ : (_ + _) * _ ≤ F.groupMeasure K), Level.floorZeroForm, ← setLIntegral_le_lintegral,
    h.floorZeroForm_on_congGroup ⟨K, unitaryLevel_le_unitaryLevel_one, le_rfl⟩]
  ring; rfl
  grw [← ENNReal.mul_le_mul_iff_left two_ne_zero (by simp), mul_two (F.groupMeasure K), B.1,
    mul_assoc, ← pow_succ, add_mul, mul_comm, (?_ : _ * _ ≤ F.groupMeasure K), mul_right_comm,
    ← mul_pow, ENNReal.inv_mul_le_one, one_pow, one_mul]
  grw [← relIndex_mul_measure_inf unitaryLevel_open_compact.2 Z.isOpen, inf_of_le_left Z.2.2, ← (r ▸
    index_comap _ p :), comap_map_eq_self (q.trans' (p.ker_le_comap _)), index_comap_of_surjective _
    IsAdmissible.reduction_surjective, vectorFixer, index_comap_of_surjective _ fun g ↦ ⟨mulSingle 0
    (mulSingle w ((S.idOrInvAdjoint (d w).1).symm g)), by simp⟩, index_stabilizer_GL_vector
    (by simpa using (inclMatrix_mulVecLin_injective ⟨_, besselFrame_injective⟩ _).ne (d w).2.2),
    card_resField_eq_levelPrime, Nat.le_succ 9, le_levelPrime]; gcongr
  exact_mod_cast
    (pow_lt_pow_right₀ (S.levelPrime_prime 0).1.one_lt (by simp; clear * - c; lia)).le_pred
  omega

/-- Let Sg be a set of chosen places above q₀, and 1/g integral off T. Some group K(g) ≤ Z ≤ K
contains k_T whenever k reduces into `Filling.fixingSet` Sg d, and kk(Z)·M(K)·b^(6|κ||Sg|) ≤
kk(K)·M(Z), kk = `Level.floorZeroForm`, M = `Level.groupMeasure`. -/
lemma IsFillingLevel.exists_intermediateGroup_lines [WeilData E]
    d [hT : Fact (↑S.gIdele⁻¹ ∈ integralOff T)] :
  ∃ Z : F.IntermediateGroup,
  (∀ k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ let K := unitaryLevel R 1 _
  F.floorZeroForm Z * F.groupMeasure K * .ofReal (S.b ^ (6 * 𝔰.k)) ^ #Sg ≤
    F.floorZeroForm K * F.groupMeasure Z := by
  choose f hf using show ∀ w, ∃ o, ∀ s : Sg, o = some s ↔ w = s.1.1 ∨ star w = s by
    simp [Option.exists]; grind [star_notMem_chosenPlaces]
  let T' i := {w ∈ T | f w = i}; have _ i : (T' i).StarStable :=
    ⟨by simp +contextual [T', fT.1, hf, or_comm, @Option.ext_iff _ _ i]⟩
  let e i : LocProd T →+* LocProd (T' i) := .pi fun w ↦ evalRingHom _ (⟨w, by grind⟩ : T)
  have A {p : T → Prop} : (∀ w, p w) ↔ ∀ i (w : T' i), p ⟨w, by grind⟩ := by aesop
  choose P' F' h' using (S.exists_isFillingLevel <| T' ·)
  choose Z b c using fun i ↦ (h' i).exists_intermediateGroup_one_prime Sg i d hT.1 (by aesop)
  let φ := MonoidHom.pi fun i ↦ U.map (e i) (by tauto) (S.map_splitGram_latMiddle _)
  have ψ x : S.charOnPlaces T x = ∏ i, S.charOnPlaces _ (e i x) := by
    with_unfolding_all refine
      (congrArg S.selfDualChar ?_).trans (map_sum S.selfDualChar.toAddMonoidHom ..)
    ext1 w; erw [map_sum (evalAt w)]; show dite .. = ∑ i, dite ..; split <;> simp [T', e, *]
  have su : (⇑φ).Surjective := fun y ↦ by
    let M := of fun a b (w : T) ↦ (y (f w)).1.1 a b ⟨w, by simp [T']⟩
    have k i : M.map (e i) = (y i).1.1 := by ext a b ⟨w, k⟩; cases (mem_filter.1 k).2; rfl
    refine ⟨U.of IsHermUnit.isUnit M (funext₃ fun a b ↦ A.2 fun i w ↦ ?_), by ext : 3; apply k⟩
    simpa [← k, ← S.map_splitGram_latMiddle (e i),
      ← map_conjTranspose_mul_mul (e i) (by tauto)] using! congr($((y i).2) a b w)
  have em := (continuous_pi (f := φ) fun i ↦ by
    simpa [φ] using! U.continuous_map (continuous_precomp' _)).measurableEmbedding
    fun x y k ↦ by ext : 3; exact funext (A.2 fun i w ↦ congr(($k i).1.1 _ _ w))
  let Q Z := (Subgroup.pi .univ Z).comap φ
  have K u : unitaryLevel R u _ = Q fun i ↦ unitaryLevel R (u.map (e i)) _ := by
    ext; simp [Q, unitaryLevel, Subgroup.mem_pi, mem_intGL, IsIntMatrix, mem_O_locProd, ↓A,
      Units.smul_def, forall_and, ite_apply, -coe_units_inv, -Sum.forall, ↓@forall_comm (Option _)]
    rfl
  have B x : x ∈ besselU ↔ ∀ i, φ x i ∈ besselU := by simp [mem_besselU, φ, U.map,
          funext_iff, ↓A, e, ite_apply, @forall_comm (Option _), -Sum.forall]
  have w a x : phase a x = ∏ i, phase (a.map (e i)) (φ x i) := by
    by_contra! n; obtain ⟨u, hu, k⟩ := (n.ne_or_ne 0).elim exists_besselU_of_phase_ne_zero
      fun k ↦ by simpa [*, Q, Subgroup.mem_pi, forall_and, ↓skolem, su.exists] using!
      (exists_besselU_of_phase_ne_zero <| prod_ne_zero_iff.1 k · (by simp))
    simp [phase_eq hu k, h.psi_eq, (h' _).psi_eq, ψ, simpleRootSum, φ,
      U.map, -Units.val_inv_eq_inv_val, ↓fun i ↦
      phase_eq (y := φ x i) ((B u).1 hu i) (by simpa using! (K _).le k i ⟨⟩)] at n
  have _ i := (h' i).isHaarMeasure_groupMeasure.sigmaFinite
  obtain ⟨t, ht⟩ := exists_eq_smul_haar (.pi (F' · |>.groupMeasure)) ⟨su.forall.2 fun g ↦
    ((em.2.measurePreserving
    F.groupMeasure).of_semiconj (measurePreserving_mul_right _ g) (map_mul _ · g) (by fun_prop)).2⟩
  have H Z : F.floorZeroForm (Q Z) = ‖t.toReal‖ₑ ^ 2 * t * ∏ i, (F' i).floorZeroForm (Z i) ∧
      F.groupMeasure (Q Z) = t * ∏ i, (F' i).groupMeasure (Z i) := by
    simp [Q, ← em.map_apply, ht, coe_pi, Level.floorZeroForm, enorm, -prod_option]
    rw [← lintegral_pi_prod _ (by fun_prop), mul_assoc, ← smul_eq_mul t, ← lintegral_smul_measure,
      ← ht, em.lintegral_map, ← lintegral_const_mul' _ _ (by simp)]
    norm_cast
    simp_rw [prod_pow, ← mul_pow, ← nnnorm_prod, ← nnnorm_smul, ← integral_fintype_prod_eq_prod,
      ← integral_smul_measure, ← Measure.restrict_pi_pi, ← Measure.restrict_smul, ← ht]
    simp [em.setIntegral_map, w, g_eq]; rfl
  use ⟨Q (Z ·), ?_⟩ <;> simp only [K, map_one, H, mul_mul_mul_comm _ _ t, ← prod_mul_distrib]
  use fun k j i _ ↦ b i k j, by grw [← prod_le_prod' fun i _ ↦ c i]; simp [mul_assoc]
  constructor <;> intro _ k i <;> cases (Z i).2 <;> simp only [Level.congGroup, g_eq] at * <;> tauto
end Filling
end

-- part: New.Filling.FiniteSystem
section
/-! Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: One-sided Siegel formula at T; top kernel dominates phase sums nearly sharply. Finite
places carry a local system with sharp bottom value and frequency bounds. -/
seal Finset.univ Finset.sum Finset.prod

open Complex ENNReal Filter Finset Matrix MeasureTheory NNReal OpenAddSubgroup IntegralPlace
  Topology IsStdLevel

/-- At a finite place, let H ≤ GL_n(R) and f ≥ c_z on the H-orbits of all vectors near p_z, z in
a finite set s. Then some compactly supported Φ ≤ f, invariant under H and small
translations, has Φ(p_z) ≥ c_z on s. -/
lemma Filling.exists_step_function {A n : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace
  A] [Fintype n] {G H ι} {p : ι → _} {f : _ → ℝ≥0∞} {s : Finset ι} {c : ι → ℝ≥0} (hf : ∀ z ∈ s, ∀ᶠ
  x in 𝓝 (p z), ∀ k ∈ H, ∀ y, k.1.1 *ᵥ y = x → c z ≤ f y) (i : H ≤ (intGL n P.R).subgroupOf G) :
  ∃ Φ : _ → ℝ≥0, HasCompactSupport Φ ∧ (∀ᶠ v in 𝓝 0, ∀ x, Φ (x + v) = Φ x) ∧
  (∀ k ∈ H, ∀ x, Φ (k.1.1 *ᵥ x) = Φ x) ∧ (∀ x, Φ x ≤ f x) ∧ ∀ z ∈ s, c z ≤ Φ (p z) := by
  obtain ⟨_, e, u, rfl⟩ := mem_closure_iff_nhds.1 (Measure.dense_of_ae P.ae_isUnit 0) _
    (s.eventually_all.2 fun z k ↦ P.intVectors_open_compact_vol.2.1.eventually_forall_mem (fun b r ↦
    (_ + b • r, b • (p z + b • r))) _ fun _ _ ↦
    prod_mem_nhds (by simpa using! hf z k) (P.intVectors_open_compact_vol.1.mem_nhds (by simp)))
  replace e z k x := e z k (u⁻¹ • (x - p z))
  have M (k : H) (b : Aˣ) x := k.1.1.1.mulVec_smul b x ▸ mulVec_mem_intVectors_iff (i k.2)
  simp [← Units.smul_def] at e M
  use fun x ↦ {z ∈ s | ∃ k : H, u⁻¹ • (k.1.1.1 *ᵥ x - p z) ∈ intVectors R n}.sup c, .intro
    (P.intVectors_open_compact_vol.2.1.smul u⁻¹) ?_,
    ((P.intVectors_open_compact_vol.1.preimage (continuous_const_smul u⁻¹)).eventually_mem ?_).mono
    (by simp +contextual [add_sub_right_comm, add_mem_cancel_right, M]), fun k l x ↦ sup_congr
    (s.filter_congr fun z _ ↦ (Equiv.mulRight ⟨k, l⟩).exists_congr ?_) ?_, ?_, fun z k ↦ le_sup
    (s.mem_filter.2 ⟨k, 1, ?_⟩) <;> simp_all [Set.mem_inv_smul_set_iff] <;> grind

namespace Filling.IsFillingLevel

variable {E 𝔰} [Field E] [CMType E] [WeilData E] {S : Filling E 𝔰} [ok : S.IsAdmissible] {T :
  Finset _} [T.StarStable] [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] (hT :
  S.latBasis ∈ intGL _ (integralOff T) ∧ (↑S.N)⁻¹ ∈ ratIntegralOff T) [P :
  IntegralPlace (LocProd T)] {F} (hF : S.IsFillingLevel T F) {π : Side} {Z : F.IntermediateGroup}
include hT hF

/-- Siegel's formula at T. Let |t|_v > N for all v, and let finitely many (class, y), Ny*y = tt̄ −
N², h⁻¹y integral off T, have weights c bounding f below on H∩K(g)-orbits near their points. For
small compact open L: ∑c·vol L ≤ (1+b⁻⁶)·#Cl·`Filling.siegelConst`·∏_v(|t|_v² −
N²)^(|κ|−1)·∫_{h(z,e)∈t+L} f. -/
lemma siegel_sum_le_lintegral_quadric {f s} {t : E} (ht : ∀ v, S.N ^ 2 < ‖Φ v t‖ ^ 2) {c :
  _ → ℝ≥0} : let x (z : S.Classes × _) := z.1.out⁻¹.1.1 *ᵥ (↑) ∘ z.2
  (∀ z ∈ s, (S.N * star z.2 ⬝ᵥ z.2 = t * star t - S.N ^ 2 ∧ ∀ i, x z i ∈ integralOff T) ∧ ∀ᶠ e in 𝓝
    (evalPlaces T ∘ tailVector S.piBar t (x z)), ∀ k ∈ besselH ⊓ F.congGroup, ∀ y, k *ᵥ y = e →
    ↑(c z) ≤ f y) → ∀ᶠ L in (𝓝 0).smallSets, IsClopen L → (∑ z ∈ s, ↑(c z)) * volume L ≤ .ofReal
    ((1 + S.b⁻¹ ^ 6) * Fintype.card S.Classes * S.siegelConst * (∏ v,
    (‖Φ v t‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)) * ∫⁻ e,
    {e | ((S.latMiddle _).splitGram *ᵥ e) (𝔰.besselFrame 𝔰.top) - ratToPlaces T t ∈ L}.indicator f e
    ∂F.floorQuadric 𝔰.top := fun hs ↦ if y0 : ∑ z ∈ s, (c z : ℝ≥0∞) = 0 then by simp [y0] else by
  obtain ⟨N0, ⟨_, d⟩⟩ := S.N_prime.pos, S.ϱ_le_k.dest
  set β := (t * star t - S.N ^ 2) / S.N
  set t' := evalPlaces T t
  let π : (LocProd T)ˣ := S.piBar.map (evalPlaces T)
  have sβ : star β = β := by simp [β, field]
  obtain ⟨u, hN : π * star π.1 = _⟩ := P.md_evalPlaces_rpow_half (x := .mk0 _ (by simp)) ⟨by simp,
    hT.2⟩, by simpa using! congr(evalPlaces T $S.piBar_mul_star)
  have p v : 0 < (Φ v β).re := by simpa [β, mul_conj', sq, N0] using ht v
  obtain ⟨Ψ, cf, uf, hk, h2, hy⟩ := exists_step_function (hs · · |>.2) fun _ ↦ (·.2.1)
  let n := LocallyConstant.indicator ⟨(Ψ <| tailVector π t' <| evalPlaces T ∘ ·),
    .comp_continuous (isLocallyConstant_of_eventually_add uf) (by fun_prop)⟩ (isClopen
    ⟨(intVectors ..).toAddSubgroup, isOpen_intVectors (isOpen_integralOff T)⟩)
  have cs : HasCompactSupport n := .of_support_subset_isCompact ((cf.image (f := fun e i ↦
    adeleOfLocal T (((besselLatticeBasis 𝔰 π).1 *ᵥ e) (𝔰.indexX₀ i))) (by fun_prop)).add
    stdLattice.isCompact_stdLattice)
    (Set.support_indicator.trans_le fun x ⟨a, h⟩ ↦ ⟨_, ⟨_, subset_closure h, rfl⟩, _,
    (by simpa [tailVector, sub_adeleOfLocal_mem_iff] using a ·), add_sub_cancel ..⟩)
  obtain ⟨sm, key⟩ := classSum_norm_eq (by lia) S.columnLevel n (fun k l x ↦
    if_congr (mulVec_mem_intVectors_iff (by clear * - l; grind [mem_intGL,
    mem_Ô_iff T, show k.1 ∈ intGL _ _ from S.hasFiniteType_columnLevel.1 l])) (.trans
    (congrArg Ψ (by rw [tailVector_evalPlaces,
    tailVector_evalPlaces]; ext1; erw [← RingHom.map_mulVec]; simp [tailVector, inclHFin,
    toLatBasis, ← mulVec_mulVec, mulVec_mulVec _ (besselLatticeBasis ..).1, toBesselH,
    fromBlocks_mulVec])) (hk (S.toPlaces T _) ⟨(inclHFin_mem_besselH k).map_mem_unitriangularOn _,
    (hF.mem_principalLevel_iff.1 (ok.columnLevel_eq.le l)).2⟩ _)) rfl) cs sβ p
  generalize eC : ofReal (_ * _) = C at key
  let r := ENNReal.ofReal ((1 + S.b⁻¹ ^ 6) / (1 + 2⁻¹ ^ 𝔰.n))
  replace hy := (ENNReal.mul_lt_mul_left y0 (by simp) (by
    grw [one_lt_ofReal, one_lt_div (by positivity), ← pow_six_le, pow_succ]
    bound)).trans_le (mul_le_mul_right (congr(‖$key‖ₑ).le.trans' (by
    simp_rw [classSum_eq_sum, ← NNReal.coe_sum, enorm_eq_nnnorm, nnnorm_real, nnnorm_eq,
      coe_finsetSum, ENNReal.coe_tsum (sm _)]
    grw [← ENNReal.tsum_prod.trans (tsum_fintype _), ← ENNReal.sum_le_tsum s]
    gcongr with z k
    grw [ite_eq_left (by simp [β, ← (hs z k).1.1]), hy z k, ← tailVector_evalPlaces]
    exact (ite_eq_left (hs z k).1.2).ge)) r)
  obtain ⟨nz, K0 : r * ‖C‖ₑ * (.ofReal (1 + 2⁻¹ ^ 𝔰.n) * volÔ E ^ 𝔰.k) * P.md π ≠ ∞⟩ := by
    simpa using hy.ne_zero, by simp [r, mul_eq_top]
  have iF := Integrable.of_integral_ne_zero nz.2.2
  let b τ := (π * star π)⁻¹.1 * τ * star τ - S.N - ratToPlaces T β
  obtain ⟨_, _, ha, _, hb, h⟩ := (isLocallyConstant_of_eventually_add uf).continuous,
    eventually_prod_iff.1
    (nhds_prod_eq.ge ((ENNReal.Tendsto.const_mul ((tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0, t')) _ (.of_forall fun p ↦ (iF.1.mul (Continuous.aestronglyMeasurable (.subtype_val
    (f := fun z : selfAdjoint _ ↦ ψf E ((2⁻¹ : E) * (z.1 * -adeleOfLocal T (b p.2)))) (by fun_prop))
    )).indicator (isOpen_codifferent E p.1).measurableSet) (by simp [(norm_indicator_le_norm_self ..
    ).trans_eq]) iF.norm (.of_forall fun z ↦ .congr' (((isOpen_Ô.preimage (by fun_prop)
    ).eventually_mem (by simp)).mono fun p l ↦ .symm (ite_eq_left fun _ ↦ ψf_of_mem ∘ mul_mem l))
    (Continuous.tendsto' (.const_mul (.subtype_val (by fun_prop)) _) _ _ (by simp [show b t' = 0 by
      rw [sub_eq_zero, sub_eq_iff_eq_add, mul_assoc, Units.inv_mul_eq_iff_eq_mul]
      simpa [t', hN] using congrArg (ratToPlaces T) (by field :
      t * star t = S.N * (β + S.N))])))).const_mul _).enorm (by simp [r])).eventually_const_lt hy))
  simp only [integral_indicator (isOpen_codifferent ..).measurableSet, Pi.mul_apply,
    ← integral_mul_const, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add,
    sub_add, sub_neg_eq_add, one_mul] at h
  filter_upwards [eventually_smallSets_forall.2 (.and ((map_add_left_nhds_zero t').le hb) ((by
    fun_prop : Continuous (tailVector π · 0)).tendsto' 0 0 (by simp [tailVector, ← Pi.zero_def])
    uf))] with L hL oL
  refine (le_mul_of_forall_lt (by simp [add_pos, nz]) (.inl K0) fun a k c hc ↦
    ?_).trans (mul_le_mul' (ofReal_toReal K0 ▸ ofReal_le_ofReal (le_of_eq ?_)) (lintegral_mono
    fun e ↦ (ENNReal.coe_indicator ..).trans_le (Set.indicator_le_indicator (h2 e))))
  · obtain ⟨V, hV, d⟩ := eventually_smallSets.1 (F.eventually_mass_near_quadric_le hN ((oL.preimage
      (by fun_prop)).continuous_indicator ‹_›) (cf.mono (by simp)) hc)
    choose M M0 ha hV using
      mem_nhds_zero_finAdele_iff.1 (ha.and ((continuous_evalPlaces T).tendsto 0 hV))
    obtain ⟨⟨u, i⟩, o, z⟩ := (isUnit_natCast_finAdele (E := E) M0).exists_right_inv,
      Fact.mk ((isCompact_codifferent E (isUnit_natCast_finAdele M0)).measure_lt_top (μ := volume)),
      idealZeta_intAdeles_pow_le 𝔰.ϱ.succ (S.degree_le.trans' (Nat.mul_le_mul_right _ 𝔰.ϱ.succ_pos))
    obtain ⟨v, _, hv, sp⟩ := P.mass_near_quadric_off_places_le i (sβ ▸ star_algebraMap_finAdele β :)
      (le_two_of_pow_le_ofReal z) (by omega : _ ≤ 𝔰.k)
    grw [← k.le, ← setLIntegral_const, setLIntegral_mono' oL.2.measurableSet fun τ l ↦ ?_,
      setLIntegral_le_lintegral, lintegral_const_mul', (lintegral_add_left_eq_self _ t').trans_le
      (d _ (fun a l ↦ by simpa [↓adeleOfLocal_evalPlaces_mul, ← mul_assoc, i] using hV (adeleOfLocal
      T (evalPlaces T u * a)) (by simpa [↓mem_Ô_iff T, ↓adeleOfLocal_mem_integralOff]))
      (measurable_const_mul (evalPlaces T u) SemilocalField.isCompact_O.measurableSet))]
    rotate_right
    grw [(h (ha 1 (by simp)) (hL _ l).1).le, enorm_mul, mul_one]
    erw [enorm_integral_codifferent i ?_
      (by simpa using isFiniteMeasure_withDensity_ofReal ((n.2.comp
      toReal).continuous.integrable_of_hasCompactSupport (cs.comp_left rfl)).2),
      withDensity_apply', funext (ENNReal.coe_indicator _ _), sp _ (Ψ <| tailVector π t' ·) (by
      fun_prop), add_sub_cancel, lintegral_congr fun y ↦ ?_]
    · simp_rw [← mul_assoc]; rfl
    · rw [← (hL _ l).2, Set.indicator_of_mem (by simpa [t', form_tailVector hN]), tailVector,
        tailVector, ← mulVec_add]; congr; simp [funext_iff, mul_add]
    simp [b, sβ, ← adeleOfLocal_star, -Units.val_inv_eq_inv_val, ← Units.coe_star_inv]; ring_nf
    grw [← z, pow_one, ← hv]; simp; ring_nf; rfl
    simp [r, mul_eq_top, o.1.ne, *]
  simp [← hN, ← sq, ← ENNReal.rpow_natCast_mul] at u
  clear * - p eC d N0 u
  simp (disch := positivity) [r, u, ← eC, classSum_eq_sum, abs_of_nonneg, abs_of_pos (p _)]
  simp [siegelConst, β, mul_conj', sq, div_pow, ← d, mul_add, prod_pow]
  field

/-- Take distinct (c, c', n̄, γ), γ fixing all e_a, e*_a, h(z,γz) = t, |t|_v > N at every v,
n_T ∈ Z, integral off T, with common Gram matrix R of the ρ_p·besselCorrelation(w_pγ),
ρ_p·headDensity = r√G, G = ∏_v(|t|_v² − N²)^(k−1). For small compact open L ∋ 0: ∑‖r∑_p
cosetAmplitude(w_pγ)‖² ≤ (1+b⁻⁶)·packetConst·Re ∑R_pq·topKernel(p,q)/(vol L·massRatio).

Phase sums are sharply dominated by local Bessel kernels. -/
lemma sum_blocks_le_topKernel {T₀ : Finset _} {j} [Fintype j] {c c' : j → _} {γ : j → S.G E} {n :
  j → _} {t : Eˣ} (h : (fun i ↦ (c i, c' i, S.reduction (n i), γ i)).Injective) (hu : ∀ i, γ i ∈ GT
  𝔰.ϱ) (hs : ∀ i, S.frameProducts (γ i) 𝔰.top 𝔰.top = t) (ht : ∀ v, S.N ^ 2 < ‖Φ v t.1‖ ^ 2) (hn :
  ∀ i, S.toPlaces T (n i) ∈ Z.1) (ho : ∀ i, S.IsIntegralOff T (S.termPosition (c i) (c' i) (γ i)))
  (i : j) {R : Matrix _ _ ℂ} {ρ : _ → ℝ} {r} : let a (p : Fin 𝔰.ϱ → T₀) := padTuple (p · |>.1) t
  let ω p := Units.map (ratToPlaces T) ∘ a p
  let y i := r ^ 2 * ‖∑ p,
    S.cosetAmplitude T (c i) (S.reduction (n i)) (c' i) (weylElem 𝔰.ϱ (a p) * γ i)‖ ^ 2
  let G := (∏ v, (‖Φ v t.1‖ ^ 2 - S.N ^ 2)) ^ (𝔰.k - 1)
  (∀ i, R = .gram ℂ fun p ↦ ρ p • besselCorrelation volume (.toLp 2 <| S.besselFn ·) (S.ratToInf
    (weylElem 𝔰.ϱ (a p) * γ i))) → (∀ p, ρ p * (F.headDensity 𝔰.ϱ (ω p) 1).toReal = r * √G) →
    (∀ i p, S.IsIntegralOff T (S.termPosition (c i) (c' i) (weylElem 𝔰.ϱ (a p) * γ i))) → ∀ᶠ L in
    (𝓝 0).smallSets, IsOpen L ∧ IsCompact L ∧ 0 ∈ L → ∑ i, y i ≤ (1 + S.b⁻¹ ^ 6) * S.packetConst *
    (∑ p, ∑ q, R p q * (F.topKernel L Z (ω p) (ω q) / volume.real L / Z.massRatio.toReal)).re := by
  intro a ω y G hR w hw
  choose A hA using fun i (b : Z.Cosets) ↦ Z.exists_coset (mul_mem (inv_mem (hn i)) b.out.2)
  choose hL hv hN _ using fun i ↦ hs i ▸ termPosition_floorGroup_spec (hu i) (c i) (c' i)
  obtain ⟨D, _, eD, f⟩ : ∃ D > 0, S.packetConst = D * _ * _ ∧ Z.massRatio ≤
    F.measureH F.congGroup * (F.groupMeasure F.congGroup ^ 2 * Fintype.card Z.Cosets) * .ofReal D :=
    ⟨_, S.of_size_bounds (by intros; positivity), rfl, div_le_of_le_mul (by
    grw [measure_mono (t := ⋃ c : Z.Cosets, (· * c.out.1⁻¹) ⁻¹' F.congGroup) fun _ h ↦
      (Z.exists_coset h).elim (by simp +contextual), measure_iUnion_fintype_le,
      ← mul_one (F.groupMeasure _), one_le_pow₀ hF.g_pow_mul_unipotentMass.ge,
      ← mul_one (_ * _ ^ 2), hF.box_eq.2.2.1.ge, hF.box_eq.2.1, ← hF.card_reducedImage_mul (B :=
      besselH ..) (F.measureH_spec.1.mono fun z a ↦ (exists_toPlaces_eq z).imp
      (by clear * - a; grind)) fun _ h ↦ F.measureH_spec.2.1 _ (h.map_mem_unitriangularOn _)]
    simp [-Nat.cast_mul, ↓card_reducedImage_besselS]; push_cast; ring_nf; rfl)⟩
  have : 0 < G := by simp [G, *, prod_pos]
  let g i := (c i, fun j ↦ (γ i).1.1 (𝔰.indexX₀ j) 𝔰.z)
  refine (hF.siegel_sum_le_lintegral_quadric hT ht (s := univ.image g) (c := fun z ↦
    (.ofReal G * (Z.massRatio / .ofReal D) * ∑ k with g k = z, .ofReal (y k)).toNNReal)
    (forall_mem_image.2 fun k₀ _ ↦ ⟨⟨hN _, ((mulVec_mem_intVectors_iff (inv_mem hT.1)).1
    (Set.mem_of_eq_of_mem (hv _).symm (by simpa [orbitPoint] using (ho k₀).isIntMatrix · _)) <|
    𝔰.indexX₀ ·)⟩, ?_⟩)).mono fun L k ⟨p, q, z⟩ ↦ by
    obtain ⟨⟨⟨o⟩, l⟩⟩ := lintegral_energy_le_topKernel Z ω p (hR i ▸ posSemidef_gram ..)
      (fun _ ↦ by simp [ω, a, padTuple]; rfl), (massRatio_ne_zero_and_ne_top Z).elim toReal_pos,
      toReal_pos (p.measure_ne_zero volume ⟨_, z⟩) q.measure_ne_top
    replace k := toReal_mono (by finiteness) ((k ⟨q.isClosed, p⟩).trans (mul_le_mul_right l _))
    simp (disch := finiteness) only [toReal_sum, toReal_mul, coe_toReal, coe_toNNReal_eq_toReal,
      toReal_ofReal, toReal_div, siegelConst, ← mul_sum] at k
    rw [sum_fiberwise_of_maps_to (by simp), mul_right_comm, ← siegelConst] at k
    exact le_of_mul_le_mul_left
      (k.trans_eq (by simp [← mul_div_assoc, ← Finset.sum_div, eD, Measure.real]; field))
        (by positivity)
  refine eventually_sum_packets_le_energy Z ω Units.isOpen (NormedRing.inverse_continuousAt 1) ⟨⟨k₀,
    rfl⟩, ⟦1⟧⟩ (n := fun (i, b) ↦ (b, A i b)) (fun θ : {k // g k = g k₀} × Z.Cosets ↦
    ⟨inv_mem (x := S.toPlaces T _) (.map_mem_unitriangularOn _ (hL θ.1)), ?_⟩) ?_ |> fun z ↦ by
    peel z
    grw [← this, coe_toNNReal_le_self, div_le_of_le_mul f, sum_subtype _
      mem_filter_univ, Fintype.sum_prod_type, mul_sum, mul_sum]
    congr! 1 with k
    simp only [ω, hR k, star_dotProduct_gram_mulVec, @smul_comm ℂ ℝ,
      hF.correlation_smul_eq_cosetAmplitude
      (hu k) (hw ..) ((hA ..).2 rfl), y, smul_smul (ρ _), w, ← smul_sum]
    simp (disch := positivity) [norm_smul, ← Complex.ofReal_pow, mul_pow, Measure.real,
      ofReal_toReal (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)]; ring
  · simp_rw [← θ.1.2, g, ← hv]; simp [orbitPoint]; rfl
  rintro ⟨⟨i, q⟩, b⟩ ⟨⟨k, q'⟩⟩ l e
  obtain ⟨⟨rfl, f⟩, q, e⟩ := by simpa [g, funext_iff] using And.intro e (q.trans q'.symm)
  have x := unitriGroup_inf_floorGroup_last.le (inv_mul_mem_of_orbitPoint_eq (hu i) (hu k)
    (by simpa [funext_iff, Unique.forall_iff, orbitPoint, floorGroup_apply (hu
    _), e, frameGram, splitGram, mul_apply, middleGram] using (hs k ▸ hs i :)))
  obtain ⟨z, ⟨m⟩⟩ := eq_and_mem_classUnip_of_besselS (mem_unitriGroup_of_mem_floorGroup x)
    (by simpa [termPosition, q, mul_assoc] using
    (hF.mem_principalLevel_iff (x := _⁻¹ * _).2 ⟨mul_mem (inv_mem (ho i)) (ho k), by simpa⟩))
  simpa using h congr(($q, $z, $((hF.reduction_eq_iff ..).2
    (by simpa using div_mem ((hA i b _).2 rfl) ((hA k b _).2 f))), $(inv_mul_eq_one.1
    (eq_one_of_mem_floorGroup_inf ⟨x, (unipotentBelow_eq_besselU le_rfl).ge m⟩ (by simp)))))

end Filling.IsFillingLevel

open ComplexOrder Level

/-- Let 1/g be integral off T. Some K(g) ≤ Z ≤ K contains k_T whenever k ∈ K reduces into
`Filling.fixingSet` Sg d, and for every compact open subgroup L the normalised forms
`Level.floorForm`, `Level.topKernel` of Z form a `SieveSystem` with bottom bound
(1 + b⁻⁶)/b^(6|κ||Sg|).

Phase sums are sharply dominated by local Bessel kernels. -/
lemma Filling.IsFillingLevel.exists_finite_sieveSystem {E 𝔰} [Field E] [CMType E] [WeilData E] {S :
  Filling E 𝔰} [S.IsAdmissible] {T : Finset _} [T.StarStable] {P : IntegralPlace (LocProd T)} {F}
  (hF : S.IsFillingLevel T F) Sg d [Fact (↑S.gIdele⁻¹ ∈ integralOff T)] : ∃ Z, (∀
  k, S.reduction k ∈ S.fixingSet Sg d → S.toPlaces T k ∈ Z.1) ∧ ∀ L : OpenAddSubgroup (LocProd T),
  IsCompact L.carrier → SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ (fun j p q ↦ (if j ≤
  𝔰.ϱ then F.floorForm j p q Z.besselVector 1 else F.topKernel L Z p q / volume.real L.carrier) /
  Z.massRatio.toReal) (S.charOnPlaces T) ((1 + S.b⁻¹ ^ 6) / (S.b ^ (6 * 𝔰.k)) ^ #Sg) (finHeadWeight
  (𝔰.n ^ 6)) (S.frequencyGain T) := (hF.exists_intermediateGroup_lines Sg d).imp fun Z ⟨hm, hk⟩ ↦ by
  obtain ⟨n, _, _, Γ, C⟩ := S.pow_chain, S.k_le_f, S.one_le_b, hF.gauge, isCut_besselVector Z
  have N {x : ℂ} {D} d h : ‖x / Z.massRatio.toReal‖ ≤ _ :=
    (toReal_mono d (@ENNReal.div_le_of_le_mul' ‖x‖ₑ Z.massRatio D h)).trans' (by simp)
  have Er {j p q ξ ω} hj (k : IsUnit ξ) H : ‖F.floorForm j p q _ ω / _‖ ≤ S.frequencyGain T ξ * _ :=
    .trans' (by
    simp (disch := positivity) [-Nat.cast_mul, md_g, frequencyGain, finHeadWeight, -map_prod]
    gcongr _ * ?_ * _
    grw [g_le_b_pow, (by linarith [S.thousand_le_b] : 2 ≤ S.b), pow_add _ 6 3, mul_assoc, pow_mul',
      ← pow_mul, ← pow_mul, ← pow_succ']
    gcongr; grw [Shape.n, ← S.ϱ_le]; omega) (N (by simp [denomIndex_ne_zero, mul_eq_top,
    div_eq_top]) (IsStdLevel.enorm_floorForm_le (ξ := k.unit) Z _ hj (by omega) n.1 H))
  refine hF.psi_eq ▸ ⟨hm, fun L hl ↦ ⟨by simp, fun j p q ξ a ↦ ?_, by
    simp [div_eq_inv_mul, ← mul_assoc]
    exact fun a t e ↦ .smul (α := ℂ) ⟨.ext (by simp [topKernel, ← integral_conj, e]),
      fun x ↦ by simpa [x.sum_fintype, mul_right_comm] using!
      (lintegral_energy_le_topKernel Z _ L.2 (Matrix.posSemidef_vecMulVec_star_self
      x) e).1⟩ (by positivity), by simpa [div_div] using! (continuous_topKernel ..).div_const _,
    fun p q ↦ (N ofReal_ne_top ?_).trans_eq (toReal_ofReal (by positivity)), fun j p q a ↦
    (ite_eq_left a ▸ Er a · (.inr ⟨j, rfl, rfl, hF.g_eq ▸ (mul_sub ..).symm⟩))⟩⟩
  split_ifs with b <;> [simp_rw [div_eq_inv_mul] at *; simp_rw [← mul_div_assoc, integral_div]]
  exact (Γ.integral_floorForm_succ C ⟨j, b⟩ _ ξ (hF.lintegral_formMajorant_ne_top Z 0 a
    (by omega))).rec fun i s ↦ s.symm ▸ ⟨i, (by simp [·, Pi.one_def]), (Er a · (.inl rfl))⟩
  -- the top floor is the integral of the top kernel, up to the mean of ψ over L
  obtain ⟨rfl, ⟨i, e⟩, o⟩ := a.eq_of_not_lt' b, hF.1.floorForm_top_eq_integral Z p q ξ,
    L.2.measurableSet
  have ⟨I, s⟩ := integral_skew_product (volume.map_sub_left_eq_self <|
    (S.latMiddle _).frameGram ·⁻¹.1 𝔰.top 𝔰.top) (i.mul_prod (((by fun_prop : ContinuousOn
    (P.ψ <| -ξ * ·) L).integrableOn_compact hl).integrable_indicator o)) (by fun_prop [frameGram])
  refine (fun k ↦ ⟨((I.congr k).div_const _).div_const _, .symm ⟨fun u ↦ ?_, ?_⟩⟩)
    (P.ae_isUnit.mono fun | _, ⟨t, rfl⟩ => ?_)
  any_goals simp_rw [← integral_congr_ae k, s, integral_const_mul, integral_mul_const, ← e]
  grw [div_right_comm, mul_div_right_comm, norm_div, norm_mul, norm_integral_le_integral_norm,
    Er a u (by left; rfl)]
  iterate 2 simp +contextual [norm_indicator_eq_indicator_norm, o, Pi.one_def, finHeadWeight,
    Measure.real, toReal_eq_zero_iff, hl.measure_ne_top, L.2.measure_ne_zero _ ⟨0, L.zero_mem⟩]
  erw [topKernel, ← integral_indicator (o.preimage (by fun_prop [frameGram]))]
  simp [← integral_const_mul, Set.indicator, mul_sub, mul_right_comm _ _ (P.ψ _),
    ← P.ψ.map_add_eq_mul, correlation, Level.headDensity, prod_range, ne_of_lt]
  grw [ite_eq_left zero_le, ofReal_div_of_pos (by bound), IntermediateGroup.massRatio,
    ← ENNReal.mul_div_mul_comm, ENNReal.le_div_iff_mul_le (by simp; left; bound),
    ← ENNReal.mul_le_mul_iff_left (P.unitaryLevel_open_compact.1.measure_ne_zero _ ?_)
    (hF.groupMeasure_ne_top le_rfl), ← mul_assoc, Level.enorm_floorForm_le, Level.headDensity,
    prod_range_zero, one_mul, lintegral_mul_const_le, (?_ : lintegral .. ≤ F.floorZeroForm
    Z), mul_right_comm, ENNReal.ofReal_pow (by bound), ← hk.ge, floorZeroForm_le_main_term ⟨_,
    P.unitaryLevel_le_unitaryLevel_one, le_rfl⟩ 0 (by omega), sdiff_le, SemilocalField.volume_O,
    ← hF.box_eq.2.1, add_le_add_left hF.groupMeasure_boxSet_le, ← pow_six_le]
  any_goals simp [ENNReal.ofReal_add, pow_succ, add_assoc, ← mul_add, inv_two_add_inv_two, -inv_pow,
    mul_eq_top]
  ring; rfl
  simp [Level.floorZeroForm, enorm_integral_phase_eq_upperPairing, formModulus, descConv.eq_1,
    weylRatio, ← formIntegrandOne_eq Γ C, formIntegrandOne, ← sq, mul_pow]
end

-- part: New.Filling.ThinClasses
section
/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Schur-test bound for total amplitude of a thin double-coset class of terms. -/

open AddSubgroup Fin DoubleCoset ENNReal Finset Fintype LinearMap MatMul Matrix MeasureTheory Metric
  Pointwise Real Norms.Elementwise

attribute [-simp] Nat.cast_mul

attribute [local simp] frameVolume_mul_left Filling.minorNorm Filling.basisScale prod_eq_zero_iff
  Subgroup.mem_sup_left realFrameGram_mul_invariant div_pow mul_pow unipotentOf_mem_besselU0

variable {E} [Field E] [CMType E] [StablyUnram E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] {j :
  Fin (𝔰.ϱ + 2)} {c s c' γ} (hk : γ ∈ S.termsOver c s c') (h : S.HasLevel j γ)

include hk h

omit [StablyUnram E] [S.IsAdmissible] in
/-- Let γ have level j and h_c⁻¹γh_c' ∈ K. Every δ in the class of γ has level j, the same Z and
the same reduction, and the middle parts of the frame images of h_c⁻¹δh_c' and h_c⁻¹γh_c'
differ by rows in g·(Ô-span of the first ϱ rows of Z(h_c⁻¹γh_c')); Z(γ) = (h(f_j, γf_l)), f the
frame. -/
lemma Filling.terms_of_class_spec δ (m : δ ∈ doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c')) :
    S.HasLevel j δ ∧ S.frameProducts δ = S.frameProducts γ ∧ δ ∈ S.termsOver c s c' ∧ ∀ i,
  (frameMiddle (S.termPosition c c' δ) - frameMiddle (S.termPosition c c' γ))ᴴ.col
  i ∈ S.gIdele • colLattice (Ô E) (xRows ((S.latMiddle _).frameGram (S.termPosition c c' γ)))ᴴ := by
  obtain ⟨u, ⟨U, hu⟩, x, ⟨X, hx⟩, rfl⟩ := mem_doubleCoset.1 m
  refine ⟨(isStable_hasLevel j _ (inv_mem hu.1) _ hx.1 _).2 h, (frameGram_inv_mul_mul (inv_mem hu.1)
    hx.1).trans (by simp_all [mem_besselU0_iff.1]), by simpa using termsOver.mul (.mul U.2 hk) X.2,
    fun i ↦ ⟨_, ⟨_, (star_mem_Ô <| (S.principalLevel_eq_unitaryLevel.le (x :=
    termPosition ..) U.2).2 (.inr (.inl i)) <| eStar ·), rfl⟩, ?_⟩⟩
  rw [frameMiddle, show frameImage _ = frameImage (S.termPosition c c u * S.termPosition c c' γ) by
    simp [↓frameImage_termPosition, coe_termPosition,
      classCoord, ↓frameImage_mul_of_mem_besselU0 hx, ↓frameImage_mul]]
  simp [funext_iff, mul_apply, mulVec_eq_sum, frameGram, splitGram, apply_inr_of_mem_besselU
    (hu.1.termPosition_mem_besselU c), show star S.gIdele = S.gIdele by ext; simp [gIdele],
    ← Units.smul_def, mul_comm]

set_option synthInstance.maxHeartbeats 200000 in
seal Finset.univ Finset.sum Finset.prod in
/-- Under `Filling.IsAdmissible`, if γ has level j and h_c⁻¹γh_c' ∈ K, the sum of
`Filling.schurIntegral` over 𝖴⁰_c(g)γ𝖴⁰_c'(g) is at most
ν·#`Filling.BesselCoord`·τ²·(b⁴g)^(−min(ϱ,j)kf)·(i/√D)^(k+1), τ = `Filling.tailScale`, i the index
`Filling.xRowsIndex` of h_c⁻¹γh_c', D = `Filling.minorNorm` j γ, ν = `Filling.unipCovolume`,
f the number of infinite places. -/
lemma Filling.tsum_schurIntegral_le : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'),
  S.schurIntegral c c' δ ≤ .ofReal (S.unipCovolume * (card S.BesselCoord * S.tailScale ^ 2 *
  (S.b ^ 4 * S.g)⁻¹ ^ (min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * (S.xRowsIndex j (S.termPosition c c'
  γ) / √(S.minorNorm j γ)) ^ (𝔰.k + 1))) := S.of_size_bounds fun g τ b t _ _ N ν o _ _ ↦ by
  have D v : _ = _ * Φ v (leadingMinor (S.frameProducts γ) j) :=
    det_submatrix_realFrameGram_ratToInf ..
  let e : IndexBelow j ↪ Fin j := ⟨fun i ↦ ⟨i, i.2⟩, id fun _ ↦ by grind⟩
  let R v := diagonal fun i : IndexBelow j ↦ π * S.g / (S.b * S.basisScale v (.inl i))
  let s (x : _ → Matrix _ (IndexBelow j) ℂ) v :=
    unipotentOf (inclMatrix ℂ (·.1 : IndexBelow j → _) * (x v * R v)ᴴ, 0)
  have := (by fun_prop : Continuous s).measurable
  simp (disch := fun_prop) [schurIntegral, ← lintegral_tsum]
  grw [lintegral_boxCutoff_le_of_average c volume this (by simp [s]) _ (fun u hu y ↦ by
    conv_lhs => rw [doubleCoset, ← smul_coe_set hu, smul_mul_assoc, smul_mul_assoc,
      ← Set.image_smul, tsum_image (S.schurWeight c' · _) (by simp)]
    simp [schurWeight, ratToInf_mem_besselU0 hu.2, doubleCoset]) (ball 0 1) (by
    repeat refine (Measure.pi_ball _ _ one_pos).ge.trans' (one_le_prod'' fun _ ↦ ?_)
    simpa using! one_le_two.trans two_le_pi) fun u hu y hy ↦ ?_]; rotate_right
  set X := @ball _ (_) _ 1
  choose G _ O T using terms_of_class_spec hk h
  grw [lintegral_tsum (by clear_value s; fun_prop), tsum_le_of_colouring _ ((relIndex_pointwise_smul
    S.gIdele ..).trans_gt (one_le_xRowsIndex_and_saturationIndex hk h).1).ne' T (∫⁻ x in X,
    S.schurWeight c' · (u * s x * y)) _ fun B (hB : ∀ ⦃_⦄, _) p₀ i r ↦ ?_]
  choose! l _ M using fun p h ↦ (G _ (hB i)).exists_frameImage_toRows₂_eq_add (.subtype (·.1 < ↑j))
    (by simp) (G _ (hB h)) (by simp [*])
    (Submodule.mem_sup_left <| by simpa [*, frameGram_termPosition, Pi.sub_def] using! r p h _ i ·)
  let L (l : type_of% (l p₀)) v := l.map (Φ v · * (S.b / π))
  choose K _ iK hK using fun v ↦ exists_kernel_frameVolume_le (hy v).2 e (R v) (by simp [R, o.ne'])
    ((D v).trans_ne (by simp [h.2]))
    (frameX₀Part ((u v)⁻¹ * S.ratToInf p₀ v) * inclMatrix ℂ (castLE j.is_le))
  apply (mul_le_mul_right ((lintegral_pi_prod ..).trans_le (prod_mono' iK)) _).trans'
  have := IsOpen.measurableSet (s := X) isOpen_ball
  grw [← volume_pi, ← lintegral_const_mul, ← tsum_congr fun p ↦
    (lintegral_sub_right_eq_self _ (L _)).trans (lintegral_indicator ‹_› _), ← lintegral_tsum]
  any_goals fun_prop
  gcongr
  set w := fun _ : B ↦ _
  choose q W using (w.support.pairwise_eq_iff_exists_eq (l ·)).1 fun _ hp _ h _ ↦ sub_eq_zero.1
    (ext fun a _ ↦
    col_eq_zero_of_norm_lt_one (c := c) (by simp [Matrix.map_sub, IsIntMatrix.sub, *]) a fun v ↦ by
    simp [w] at h hp
    have e := X.sub_mem_sub h.1 hp.1
    simp [X, L, pi_norm_lt_iff, norm_lt_iff, ← sub_mul,
      ← lt_div_iff₀ (by positivity : 0 < |S.b| / π)] at e ⊢
    grw [e, pi_le_four] <;> simp [field, Nonempty.intro a]; nlinarith [S.k_le_b])
  grw [tsum_classCutoff_box_le (V := (piMap fun v ↦ ((Fintype.linearCombination ℂ _).restrictScalars
    ℝ).compLeft _).range) (fun _ ↦ Subtype.ext) (fun p hp ↦ ⟨O _ (hB p.2), by simp, by
    exact (by simpa [schurWeight, boxCutoff, W p hp] using hp :).2.1.1, ?_⟩) fun p a r b ↦
    ⟨_, funext₂ fun v _ ↦ (frameVector_sub_eq_sum (by simp [M, W _ a, W _ b]) ..).symm⟩,
    pow_le_tailScale (by grw [finrank_range_le]; simp; lia)]
  swap; grw [X.indicator_le_self .., schurWeight, boxCutoff, Set.indicator_le_self .., W p hp]
  gcongr
  cases mem_besselU0_iff_unipotentOf.1 (hu v)
  grw [← hK v _ _ _ (((G p _).1.ratToInf v).besselU_mul (inv_mem (mul_mem (hu v)
    (unipotentOf_mem_besselU0 _ : s (a - L q) v ∈ _))).1)] <;> simp [mul_assoc, s, *,
    frameX₀Part_unipotentOf_inv_mul, ← ext_iff]
  simpa [↓mul_inclMatrix, ↓basisScale_besselFrame, L, W p hp, by simpa using congrFun₂ (M _ p.2),
    mul_apply, mul_sum, R, *, add_left_comm (_ * _), add_mul, add_sub, e, ← castSucc_mk, sum_mul,
    inclMatrix, frameX₀Part, diagonal_apply, add_assoc, sub_eq_iff_eq_add'] using fun _ _ ↦
    sum_congr _ _ (by have := o.ne'; simp [*, field, ← Complex.ofReal_pow])
  have := (one_le_prod_norm_Φ · h.2.1) (.det fun _ _ ↦ isIntegral_frameProducts hk ..)
  simp (disch := intros; positivity) only [abs_norm_eq_prod_norm_sq, prod_pow, pow_mul', D,
    xRowsIndex, relIndex_pointwise_smul, sqrt_sq, ← div_pow, ← ofReal_prod_of_nonneg, ← ofReal_mul,
    pow_add _ 𝔰.k, ← ofReal_natCast, ofReal_le_ofReal_iff, prod_mul_distrib]
  have C (x : ℝ) : x ^ j.1 = x ^ (j - 𝔰.ϱ) * x ^ min 𝔰.ϱ j := by simp [← pow_add, min_comm 𝔰.ϱ]
  apply le_of_le_of_eq
    (by grw [show _ ^ 𝔰.n ≤ S.tailScale / ((∏ v, ‖Φ v _‖) / (S.N ^ numInfPlaces E) ^ (j - 𝔰.ϱ)) by
    simp
    grw [t, ← one_le_abs_kappa, N_le, le_self_pow₀ this, ← N.nat_succ_le]
    simp [field, ← pow_mul, ← pow_add]; grw [j.is_le, pow_le_tailScale]
    repeat lia, C, show _ ^ (_ - _) ≤ (S.g / S.b ^ 6) ^ min 𝔰.ϱ j by
    grw [← le_g, t]; simp [field, ← pow_mul, ← pow_add]
    gcongr; grind [S.ϱ_le], two_le_pi, ← Nat.factorial_le bot_le])
  simp [R, C, Fintype.card_subtype, card_filter_val_lt, pow_right_comm _ _ 2, prod_pow_eq_pow_sum,
    e, ← sum_of_injective e e.2 _ (𝔰.ϱ - ·) (by simp [Fin.forall_iff]; lia) fun _ ↦ rfl]
  field

attribute [local instance] Side.cut

/-- Let γ have level j, lie over (c, s, c') and satisfy ∏_v|𝗀(γ)|_v ≤ N^f·`Filling.minorNorm` j γ.
Then the absolute amplitudes, for cut Bessel functions, over the double coset
𝖴⁰_c(g)γ𝖴⁰_c'(g) sum to at most ν·`Filling.classSize` j (𝗀*), 𝗀* = `Filling.classGauge` j c c' γ,
ν = `Filling.unipCovolume`. -/
lemma Filling.tsum_amplitudeAbs_class_le (k : S.termDiscNorm γ ≤ S.N ^ numInfPlaces E * S.minorNorm
  j γ) : ∑' δ : doubleCoset γ (S.classUnip₀ c) (S.classUnip₀ c'), S.amplitudeAbs c c' δ ≤
  .ofReal (S.unipCovolume * S.classSize j (S.classGauge j c c' γ)) := of_size_bounds (by
  intros; let : MeasurableSpace (S.G E) := ⊤; have := h.minorNorm_pos
  grw [classSize, classGauge, max_eq_right k, ← show S.N ^ numInfPlaces E * S.tailScale ^ 8 /
    (S.tailScale ^ 32) ^ min 𝔰.ϱ j * S.besselEnergy ≤ ite .. by
    grw [N_le, ← pow_mul, pow_le_tailScale (by lia), ← pow_succ']; split
    grw [← IsAdmissible.besselEnergy_le, div_le_self]
    any_goals gcongr
    repeat bound, ← ENNReal.pow_le_pow_left_iff, ← lintegral_count, sq_lintegral_le .of_discrete
    .of_discrete fun δ ↦ amplitudeAbs_sq_le, lintegral_count, lintegral_count,
    tsum_schurIntegral_le hk h, ← tsum_image _ (by simp),
    (tsum_schurIntegral_le (.inv hk) h.inv).trans' (tsum_mono_subtype _ (by simp [doubleCoset,
    mul_assoc, -Set.mul_singleton, -Set.singleton_mul])), show S.termPosition _ _ γ⁻¹ =
    (S.termPosition c c' γ)⁻¹ by simp [termPosition, mul_assoc], show S.minorNorm j γ⁻¹ =
    S.minorNorm j γ by simp [abs_norm_eq_prod_norm_sq, leadingMinor, ← conjTranspose_submatrix],
    ← ofReal_mul, ← ofReal_pow, mul_pow, mul_pow, sq_sqrt, ← sq_sqrt this.le, sqrt_sq, pow_mul
    _ 4 2, pow_mul _ 4 8, tailScale_pow_four, IsAdmissible.card_besselCoord_le] <;> try positivity
  congr! 1; push_cast [besselEnergy, columnDim, div_pow, inv_pow]; field)
end

-- part: New.Filling.BlockBound
section
/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Sum of inverse discriminant powers over classes and subspaces.
Colouring count of kept near frames weighted by inverse index powers. Weighted count of near
congruent pairs of terms, summed over classes, is bounded. Block amplitude bounded by a sum of sizes
over kept near terms. -/
seal Finset.univ Finset.sum Finset.prod

open AddSubgroup Module DoubleCoset ENNReal Fintype MatMul Matrix MeasureTheory Submodule

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Under `Filling.IsAdmissible`, the sum of d^(−(k+1)), d = `Filling.latticeDisc` c T, over all
classes c and all subspaces T of X₀ of codimension s is at most #{c}·N^(−kf)·τ^(s+1), where k = |κ|
and f counts infinite places, τ = `Filling.tailScale`. -/
lemma sum_latticeDisc_inv_le [StablyUnram E]
    [ok : S.IsAdmissible] s : ∑ c, ∑' T : {T : Submodule E _ // finrank E
  T + s = 𝔰.k}, ENNReal.ofReal (S.latticeDisc c T.1 ^ (𝔰.k + 1))⁻¹ ≤ .ofReal
  (card S.Classes / S.N ^ (𝔰.k * numInfPlaces E) * S.tailScale ^ (s + 1)) := S.of_size_bounds (by
  intros; rw [mul_comm_div]; set b : ℝ := _ / _
  set f := fun _ ↦ _; let A := Kf .. ⧸ (S.latStabilizer.comap S.inclHFin).subgroupOf _
  have := Subgroup.fintypeOfIndexNeZero (Nat.cast_pos.1 (ok.le_relIndex.trans_lt' (by bound))).ne'
  have hB u : ∑ φ : A, f ⟦u * φ.out⟧ ≤ .ofReal (Nat.card A * b)
  choose g hη k hk h using fun φ : A ↦ mk_out_eq_mul stdRatPoints S.columnLevel (u * φ.out)
  let y (φ : A) := φ.out * ⟨_, S.hasFiniteType_columnLevel.1 (hk φ)⟩
  have hy φ : ↑(y φ) = φ := .trans (QuotientGroup.mk_mul_of_mem _
    (S.principalLevel_eq_unitaryLevel.le (ok.1.le (hk φ))).1) φ.out_eq
  let r φ := replicateRow Unit ((y φ).1⁻¹.1.1 𝔰.k₀); rw [← Finset.univ.tsum_subtype']
  refine (ENNReal.tsum_mul_left.trans_le
    ((mul_le_mul_right (tsum_sublatticeDisc_inv_le u s) _).trans ?_)).trans'
    (.trans (ENNReal.tsum_le_tsum fun φ ↦ ?_) (ENNReal.tsum_comm.trans_le (ENNReal.tsum_le_tsum
    fun T ↦ if h : _ + s = _ then ENNReal.tsum_mul_right.trans_le (mul_left_mono
    (tsum_inv_index_pow_le_of_congr S.piBar_mem r (fun φ _ _ ↦ (y φ).2.isIntMatrix_inv _)
    (sublatticeBasis u.1.3 T).2.1 (equivOfCardEq (by simpa)) (K := .comap (.proj ()) (_ ∙ _))
    (fun | _, ⟨_, h, rfl⟩ => mem_span_singleton_iff_exists_mul.2 ⟨_, h (), rfl⟩) _ (fun
    _ _ ↦ dvd_rfl) (𝔰.k + 1) (by simp; lia) fun B _ a h H ↦ (tsum_eq_single ⟨a, h⟩ fun ⟨b, k⟩ ↦
    absurd (Subtype.mk_eq_mk.2 (hy b ▸ hy a ▸ QuotientGroup.eq.2 (S.inclHFin_mem_latStabilizer.2
    ⟨(_ * y a).2, fun _ ↦ (by simpa [← mul_apply, mulVec, dotProduct, r] using H _ k _ h ⟨_,
    (y a).2.isIntMatrix.isInt_transpose ·, rfl⟩)⟩)))).le)) else by simp [h])))
  · grw [show genIndex _ = _ by simpa [genIndex_natCast, genIndex_pos,
      le_of_lt] using congr(√(genIndex $S.piBar_mul_star)), mul_one, ← ofReal_mul (by bound),
      ← Subgroup.index_eq_card, ← Subgroup.relIndex, ← ok.le_relIndex]
    apply ofReal_le_ofReal (le_of_pow_le_pow_left₀ (NeZero.ne 1000) (by bound) _)
    simp [div_pow, pow_mul, field, pow_right_comm _ _ 1000]
    grw [N_le, S.size_le, pow_mul S.tailScale 4 250, tailScale_pow_four, ← Shape.k,
      ← Nat.add_sub_of_le S.ϱ_le_k]
    simp [← pow_mul, ← pow_add]; gcongr; lia
  cases' inv_mem (hη φ) with η hη; let P := η.1.toLin.toLinearEquiv
  refine .trans (ENNReal.tsum_le_tsum fun ⟨T, b⟩ ↦ ?_) (tsum_comp_le_tsum_of_injective
    ((map_injective_of_injective P.injective).comp Subtype.val_injective) _)
  erw [latticeDisc, sublatticeDisc]; obtain ⟨q, ⟨V, -⟩, x, a, -, hx, e⟩ := sublatticeBasis _ T
  by_cases d : genIndex (qᴴ * q).det = 0; simp [d]
  erw [classCoordX₀, h] at V; simp [e, ← hη, isIntMatrix_middleBaseChange_mul] at V
  obtain ⟨w, p, z⟩ := sublatticeDisc_mul_index_sq_le u.1.3 _ (r φ) (P.finrank_map_eq T).symm
    (fun | _, ⟨v, rfl⟩ => ⟨_, hx.le ⟨v, rfl⟩, mulVec_mulVec ..⟩) a (by simp [e, ← genIndex_det_conj,
    finAdeleMat_conjTranspose, by simpa using U.gram_invariant η x x])
    d (by simpa [y] using (y φ).2.isIntMatrix.mul V.1) (K := .comap (.proj ()) (_ ∙ _)) (by
    simpa [r, y, ← Matrix.mul_assoc] using! V.2)
  grw [← Real.le_sqrt_of_sq_le w]; simp [*, mul_pow, P.finrank_map_eq]
  lift f to S.Classes → NNReal using Quot.ind (div_mul_cancel · _ ▸
    sum_ne_top.1 ((hB _).trans_lt coe_lt_top).ne ⟦1⟧ (by simp)) with f
  let φ g := b - f (⟦g⟧)
  have e γ a k h g : φ _ = φ g := congr(b - f $((eq ..).2 ⟨γ, a, k, h, rfl⟩)).symm
  have r : S.columnLevel ≤ rightStab φ := by simpa [LE.le] using e 1
  simp (disch := finiteness) only [← ofNNReal_finsetSum, le_ofReal_iff_toReal_le, coe_toReal] at *
  simpa [↓classIntegral_eq_classSum r, classSum_eq_sum, φ, NeZero.pos,
    ← sum_congr _ f (congrArg f ·.out_eq)] using (classIntegral_sum (K :=
    S.columnLevel) Finset.univ (fun _ : A ↦ .id ℝ) _ (fun _ ↦ ⟨(by simpa using e · · 1),
    Subgroup.isOpen_mono r S.hasFiniteType_columnLevel.2⟩) (congrFun rfl) :).le.trans'
    (mul_nonneg (by simp) (finsum_nonneg (mul_nonneg (by simp) <| by simpa [φ] using hB ·.out))))

variable [S.IsAdmissible] {c} {γ : ↥(S.G E)} {j : Fin (𝔰.ϱ + 2)} {A : Set (S.Classes × S.G E)}

section

open Norms.L2Operator

attribute [-simp] MulMemClass.coe_mul Nat.cast_mul Prod.forall Subgroup.coe_mul sup_of_le_right

attribute [local simp ←] pow_add pow_mul pow_succ'

attribute [local simp] Finset.mul_sum IsIntMatrix Matrix.mul_apply splitGram funext_iff inclMatrix
  mul_assoc mul_pow sub_mul

/-- Shared vectors of a near γ of level j are short: for b ≥ j, D_j times the e_a-coordinate of
γf applied to column b of the inverse of `Filling.paddedLeading` j Z(γ) has absolute value below
q₀^((ϱ+1)⁴)/2 at every infinite place, q₀ = `Filling.levelPrime` 0. -/
lemma HasLevel.norm_shared_vector_lt (h : S.IsNear γ ∧ S.HasLevel j γ) {u b Y} (U :
  u ∈ besselU0) (hb : ↑j ≤ b.1) (H : paddedLeading j (S.frameProducts γ) = Y) v a : 2 * ‖Φ v
  ((frameImage (u * γ).1.1 *ᵥ Y.det • Y⁻¹ᵀ b) (.inl a))‖ < S.levelPrime 0 ^ 𝔰.n ^ 4 := by
  obtain ⟨⟨w, e⟩, t : 2 ≤ S.b, y, p, q⟩ :=
    H ▸ h.2.exists_shared_frame_vector hb, by grind [thousand_le_b], h.1
  have ⟨A, hu, r⟩ :=
    (mul_right_surjective (y v)⁻¹).exists.1 (exists_norm_le_of_besselSize_le (p v).2)
  let g {z} (_ : z ∈ S.boxedPoints) := of fun k c ↦ S.basisScale v (𝔰.besselFrame k) / S.basisScale
    v (𝔰.besselFrame c) * A.1.1 (𝔰.besselFrame k) ⬝ᵥ frameVector (z v) c
  let M := S.b ^ (5 * 𝔰.n ^ 2)
  have G z h k c : ‖@g z h k c‖ ≤ M := by
    simp [g, M, basisScale_besselFrame, field] at *
    grw [show ‖_ ⬝ᵥ _‖ ≤ _ from (PiLp.norm_apply_le ..).trans (A.1.1.l2_opNorm_mulVec _),
      r, (h v).1 c, boxSize, ← one_le_abs_kappa, abs_kappa_le]; simp
    gcongr <;> nlinarith [S.ϱ_le, 𝔰.ϱ.sub_le k]
  have k := by
    simpa [det_eq_one_of_unitriangular (Z :=
      g p) fun _ _ h ↦ congr(_ * $(frameMatrix_unitriangular hu _ _ h)).trans (by
      aesop)] using ((g p).fromBlocks (-g q) 0 (Y.map (Φ v))).det_updateCol_sum (.inl a.castSucc)
  have E k : ∑ c, Φ v (w c) * g p k c = ∑ c, Φ v (Y⁻¹ c b) * g q k c := by
    convert congr(S.basisScale v (𝔰.besselFrame k) * A.1 (𝔰.besselFrame k) ⬝ᵥ (y v)⁻¹ *ᵥ (Φ v ∘ $e /
      S.basisScale v)) <;> simp [g, entrywise, Finset.sum_div, Subgroup.coe_mul, frameVector,
      ite_div, apply_ite, -sum_sum_type, @Finset.sum_comm (Fin _)] <;> grind [basisScale_ne_zero]
  erw [mulVec_smul, map_mul, ← mulVec_mulVec, ← e, ← frameImage_mulVec, ← one_mul u,
    frameImage_mul_of_mem_besselU0 U, frameImage_one_mulVec,
    RingHom.map_det, mul_comm (det _), ← k (_ ∘ (w ⊕ᵥ Y⁻¹ᵀ b))]
  grw [← le_levelPrime, norm_det_le_norm_pow, l2_opNorm_le_of_apply (M := M) (by
    simp [updateCol_apply, E, by simpa [H] using congr(Φ v ∘ $(h.2.paddedLeading_mul_inv)ᵀ b)]
    simp [← H, paddedLeading]
    grind [norm_one, norm_zero, one_le_pow₀, one_le_b, IsNear.norm_frameProducts_le]), ← sq,
    card_sum, card_fin, Nat.cast_add, S.succ_le_b, ← two_mul, t, t]
  simp [M]
  gcongr <;> clear * - t <;> grind [S.ϱ_le]

/-- Under `Filling.IsAdmissible`, let A consist of pairs (c',γ) with `Filling.IsLabelledTerm` j c t,
and let T ⊂ X₀ have codimension ≤ s. If on A the index `Filling.frameValueIndex` (a = g, V = T) of k
= h_c⁻¹γh_c' divides n(k), then ∑_A n(k)^(−|κ|) ≤ b^(2000(ϱ+1)⁶(s+1)f). -/
lemma tsum_invPowWeight_le_of_codim_le [StablyUnram E]
    {t} s (h : A ⊆ {p | S.IsLabelledTerm j c t p}) T {n : _ → ℕ}
    (hQ : ∀ p ∈ A, S.frameValueIndex c (S.termElem c p) S.gIdele T ∣ n (S.termElem c p)) (hT : 𝔰.k ≤
  finrank E T + s) : ∑' p : A, S.invPowWeight c n p ≤
  .ofReal (S.b ^ (2000 * 𝔰.n ^ 6 * (s + 1) * numInfPlaces E)) := S.of_size_bounds fun _ _ _ o ↦ by
  cases' T.finrank_le.dest with l hl; simp at hl
  intros; have K {p} a := (@h p a).2.choose_spec.1
  grw [tsum_le_of_encard_range_le (R := (S.frameProducts ·.2 = S.frameProducts ·.2)) _
    (encard_integral_le Function.uncurry (by bound) (Set.forall_mem_range.2 fun p i ↦
    ⟨isIntegral_frameProducts (K p.2) .., ((h p.2).1.1.1.norm_frameProducts_le · ..)⟩)
    Function.uncurry_injective.injOn) (by tauto) fun A hA p₀ h₀ e ↦ ?_]; rotate_right
  obtain ⟨⟨⟨⟨N⟩, -, D⟩⟩, F⟩ := h (hA h₀), fun {p} a ↦ And.intro (h (hA a)) (e p a _ h₀)
  let O := (Ô E).comap (algebraMap E _)
  have : IsStarStable O := ⟨(by simpa [O] using star_mem_Ô ·)⟩
  let Y := paddedLeading j (S.frameProducts p₀.2)
  have iY :
    IsIntMatrix O Y := by simp [O, Y, paddedLeading, ite_mem, isIntegral_frameProducts (K (hA h₀))]
  let M := S.levelPrime 0 ^ 𝔰.n ^ 4
  have iy := nsmul_mem (iY.mul iY.isInt_conjTranspose).det_mem S.g
  have n0 : M • S.g • (Y * Yᴴ).det ≠ 0 := by simp [M, Y, D]
  let d := principalIdele n0.isUnit.unit
  have hd : ↑d ∈ Ô E := nsmul_mem iy M
  have nd : genIndex d.1 ≤ _ := (genIndex_algebraMap _).trans_le (by
    simp [M, Y, abs_norm_eq_prod_norm_sq, ← sq]; grw [g_le_b_pow, N.norm_map_leadingMinor_le,
      levelPrime_le])
  have := genIndex_pos d; simp [frameValueIndex, frameGram_termPosition, invPowWeight] at hQ ⊢
  grw [tsum_inv_index_pow_le_of_congr hd (fun p ↦ (frameMiddle (S.termElem c p).1.1)ᴴ)
    (fun p h _ _ ↦ (termsOver.isIntMatrix_termPosition (K (hA h))).isInt_conjTranspose
    _ _) ((isPrimitiveMatrix_iff.2 S.isUnimodular_latMiddle.2).mul_iff.2
    (sublatticeBasis (gram_classCoordX₀ c) T).2.1) (equivOfCardEq
    (by simp [← hl, add_assoc]; rfl)) (le_sup_of_le_right _) (n <| S.termElem c ·) (fun p h ↦ .trans
    (submoduleIndex_dvd_of_le .id le_sup_left (by simp)) ((F h).2 ▸ hQ p (hA h))) _ (by simp [← hl])
    fun B hB p₁ h₁ e ↦ (F (hB h₁)).elim fun G' f ↦ ?_, nd]
  rotate_left 2
  choose! u hu eu using fun p h ↦ (@F p (hB h)).elim fun a b ↦
    (a.1.2.exists_frameImage_toRows₂_eq_add (.refl _) (by simp) G'.1.2 (b ▸ f)
    (by simpa [b] using! e _ h₁ p h <| col_mem_colLattice ·)).elim fun l i ↦ show ∃ u ∈ S.classUnip₀
    c, ∀ i a, (u * p.2).1 (.inr i) (𝔰.besselFrame a) = p₁.2.1 (.inr i) (𝔰.besselFrame a) from
    (S.exists_mem_classUnip c id (-fromRows 0 ((l.fromRows 0).fromRows 0)) 0 (by simp) (by simp) (by
    simpa [classCoord_eq_fromBlocks] using i.1) (by simp) rfl).imp (by clear * - i; simp_all
    [middleGram, Fin.forall_fin_succ', Subgroup.coe_mul, ← ext_iff, frameGram])
  grw [tsum_le_of_colouring (fun p ↦ (frameImage (S.termPosition c p.1 (u p * p.2)).1.1).toRows₁)
    (submoduleIndex_smul_ne_zero hd) (fun _ a _ _ ↦ termsOver.isIntMatrix_termPosition
    (.mul (hu _ a).1.2 (K (hA (hB a)))) _ _) (fun _ ↦ 1) 1, submoduleIndex_smul_intVectors hd, nd]
  simp; norm_cast; simp [Set.encard_le_one_iff]
  intro C hC _ _ H' p q a b
  let ξ := (frameImage (u q * q.2) - frameImage (u p * p.2).1.1).toRows₁
  have ⟨X, x, iX⟩ : ∃ X, ξ = _ • X ∧ IsIntMatrix O X := ⟨_, (smul_inv_smul₀ n0 _).symm, (by
    simpa [ξ, O, d, frameImage_termPosition, classCoord_eq_fromBlocks, Units.smul_def,
      intVectors] using Set.mem_smul_set_iff_inv_smul_mem (a := d).1 <| H' _ b _ a ·)⟩
  grw [hC] at a b
  let P := xRows (S.frameProducts p₁.2)
  let α := (xRows Y.adjugateᵀ)ᵀ
  let T := X * α
  have s : Tᴴ * P = -(P * α)ᴴ * X := (smul_right_inj n0).1 (by
    simpa [x, T, mul_comm Y.det] using congr(αᴴ * $((by
    linear_combination (norm := (ext; simp [ξ, P, eu, a, b, frameGram, mul_sub]; ring))
      congr(submatrix $((u q * q.2).2.trans (u p * p.2).2.symm) 𝔰.besselFrame 𝔰.besselFrame) :
      ξᴴ * P = Pᴴ * -ξ))))
  have z i k (J : ↑j ≤ k.1) : (X * Y.adjugate) i k = 0 := (mul_eq_zero_iff_left (by simp [Y, D])).1
    (eq_zero_of_norm_Φ (algebraMap_mem_Ô.1 ((iX.mul iY.adjugate).smul iy i k)) fun v ↦ by
    have t p h := (F (hB h)).2 ▸ HasLevel.norm_shared_vector_lt ((F (hB h)).1.1.imp And.left id) (hu
      p h).2 J rfl v i
    have := congr(‖Φ v (($x * Y.adjugate) i k)‖).ge
    simp [ξ, Y, M, inv_def, entrywise, D, ← Finset.mul_sum] at *
    by_contra! h; grw [← h, norm_sub_le] at this
    linarith [t _ b, t _ a])
  let σ := (M : E) • (Yᴴ.det • T - Y.det • Tᴴ - (P * α)ᴴ * T)
  have k : S.g • (σ * P) =
    ξ := by cases ((lt_or_ge 𝔰.ϱ j).imp (by simpa [P, α, Y, ← ext_iff, paddedLeading,
    f, ·.trans'] using (congr(submatrix $Y.mul_adjugate Fin.castSucc Fin.castSucc))) fun J ↦
    Matrix.ext fun a b ↦ sum_of_injective _ Fin.castSuccEmb.2 _ _ (by simp +contextual [z, J.trans])
    fun c ↦ mul_eq_mul_left_iff.2 ((em' _).imp (by simp +contextual [Y, P, paddedLeading, f]) (z a
    _)) : P * α = Y.det • 1 ∨ T * P = X * Y.adjugate * Y) <;> simp [σ, adjugate_mul, *] <;> module
  have ⟨r, _, hr, τ, er⟩ := S.exists_mem_classUnip c id 0 _ (by simp) (by simp [σ, s]; module)
    (by simp) (show IsIntMatrix O σ by apply_rules (transparency := .reducible) [IsIntMatrix.smul,
    IsIntMatrix.sub, IsIntMatrix.mul, IsIntMatrix.isInt_conjTranspose, IsIntMatrix.det_mem] <;>
    simp [α, iY.adjugate _, O, P, isIntegral_frameProducts (K (hA h₀)), f]) rfl
  apply (F (hB a)).1.eq_of_frameImage_eq (mul_mem (hr (by simp)) (hu _ a)) (hu _ b) (F (hB b)).1
  simpa [↓frameImage_mul (s := r), ← ext_iff, er, eu, a, b, P, frameGram, ξ,
    eq_sub_iff_add_eq'] using k
  grw [one_le_two, add_le_mul le_rfl, o, o]
  simp (disch := bound); gcongr; simpa; grw [show l ≤ s by lia]; lia; bound
  rintro _ ⟨v, h, rfl⟩
  simpa [d, Y, preimageLattice, inv_def, smul_smul, D, mul_left_comm _⁻¹, -map_mul] using
    (iY.adjugate.isInt_conjTranspose.smul (nsmul_mem iY.det_mem M)).mulVec (M := finAdeleMat _) h

end

open Pointwise Set

omit [S.IsAdmissible] in
lemma submoduleIndex_gIdele_smul {n} {M N : Submodule (Ô E) (n → 𝔸f E)} (h : 1 ≤ submoduleIndex N M)
  (i : N ≤ M) : submoduleIndex (S.gIdele • M) M = submoduleIndex (S.gIdele • N) N :=
  Nat.eq_of_mul_eq_mul_right h (by erw [relIndex_mul_relIndex (hKL := i), mul_comm, submoduleIndex,
  ← relIndex_pointwise_smul S.gIdele, relIndex_mul_relIndex (hHK := smul_set_mono
  i)] <;> first | rfl | apply smul_le_self_of_tower (⟨_, S.gIdele_mem⟩ : Ô E))

variable [StablyUnram E] {S : Filling E 𝔰} [S.IsAdmissible] {T : Set ↥(S.G E)}

/-- Under the standing hypotheses, for each level j the pair weights `Filling.pairWeight`, summed
over all classes c, c' and all pairs p of terms, total at most 2τ², where τ = b^(kf/4). -/
lemma sum_pairWeight_le : ∑ c, ∑ c', ∑' (γ) (γ'), S.pairWeight j c c' γ γ' ≤
  .ofReal (2 * S.tailScale ^ 2) := by
  apply S.of_size_bounds; intros; apply ((tsum_fiberwise (fun (⟨i, t, c, T, q, p⟩ : Σ i t c, Σ (T :
    {T : Submodule E (𝔰.κ → E) // finrank E T + i = 𝔰.k}) (q : ofPred (S.IsLabelledTerm j c t)),
    {p | S.IsLabelledTerm j c t p ∧ S.CongruentTerms c p.1 q.1.2 p.2 ∧ commonLink q.1.2 p.2 = T}) ↦
    S.termWeight j i c q p T) fun ⟨_, _, c, _, q, p⟩ ↦ (c, p.1.1, q.1.2, p.1.2)).trans_le ?_).trans'
  · simp -iota [pairWeight]; gcongr; split_ifs with h; have ⟨h@⟨s, o, o'⟩, m, m'⟩ := h
    exact .trans (by rfl) (ENNReal.le_tsum ⟨⟨_, _, _, ⟨commonLink .., by simp [(finrank_le
      _).trans]⟩, ⟨(_, _), m, s, o, rfl⟩, (_, _), ⟨m', s, o', rfl⟩, h, rfl⟩, rfl⟩)
    simp
  simp [ENNReal.tsum_sigma', termWeight]
  grw [ENNReal.tsum_le_tsum (g := (.ofReal <| 2⁻¹ ^ · * S.tailScale ^ 2)) fun m ↦ ?_]
  simp [-inv_pow]
  grw [tsum_invPowWeight_le_of_codim_le (m + 𝔰.ϱ + 1) (by exact inf_le_left) ?T ?A ?C, ENNReal.tsum_mul_right.le,
    tsum_invPowWeight_le_of_codim_le m (by rfl) _ (by exact fun p h ↦ (relIndex_dvd_of_le_left _ inf_le_left).trans ((
                        relIndex_inf_mul_relIndex _ (toAddSubgroup _) _).symm.dvd.trans (mul_dvd_mul ((submoduleIndex_dvd_of_le
                        (K' := _ ⊓ _) .id le_rfl (by simp)).trans ((submoduleIndex_gIdele_smul (one_le_xRowsIndex_and_saturationIndex h.2.choose_spec.1 h.1.2).1
                        (colLattice_le (col_mem_colLattice ·.1))).dvd.trans (submoduleIndex_dvd_of_le _ (fun | _, ⟨v, h, rfl⟩ => ⟨_, ⟨_, h, rfl⟩,
                                                  by simp⟩) le_sup_left))) dvd_rfl))) (by exact a.2.ge)]
  case T T => exact T.1 ⊓ (frameMiddle a.1.2.1).toRows₁ᴴ.mulVecLin.ker
  case' C T => rw [← map_comap_subtype, ← LinearMap.ker_domRestrict]
  · set N := (mulVecLin _).domRestrict T.1
    obtain ⟨e : _ = _⟩ := T.2, N.finrank_range_add_finrank_ker, N.range.finrank_le
    simp_all [SubmoduleElem]; omega
  case' A c _ T => refine fun y ⟨_, ⟨s, ⟨k, rk, ek⟩, k', rk', ek'⟩, f⟩ ↦
    submoduleIndex_dvd_of_le (S.gIdele • ((frameImage (S.termElem c y).1.1)ᴴ *
    (S.latMiddle (𝔸f E)).splitGram).mulVecLin) (colLattice_le (Sum.rec (⟨_, col_mem_colLattice ·, by
    ext1; simp [frameGram, splitGram, mulVec_eq_sum, mul_apply, Units.smul_def]⟩) fun a ↦
    ⟨0, by simp, congrArg _ (funext fun i ↦ .trans (by cases i using Fin.lastCases <;> simp)
    (congrFun₂ (termElem ..).2 ..).symm)⟩)) (le_sup_of_le_left ?_)
  · set γ := a.1.2; set L := T.1 ⊓ _; obtain ⟨_, ⟨hb, -⟩, p, a, -, hp, rfl⟩ := sublatticeBasis _ L
    rintro _ ⟨r, hy, rfl⟩
    let P : Matrix 𝔰.BesselIndex .. := fromRows 0 ((p.fromRows 0).fromRows 0)
    have φ : (frameImage γ.1.1)ᴴ * S.ratGram * P = 0 := .trans (by simp [P, splitGram, entrywise,
      middleGram]) (mul_eq_zero_of_range_le_ker (hp.le.trans inf_le_right))
    obtain ⟨w, hw⟩ := exists_mul_eq_of_col_mem_range (x := isotropicFramePair y.2) (y :=
      y.2.1.1 * (γ⁻¹.1.1 * P) - P) fun i ↦ by
      obtain ⟨z, ⟨⟨h, h'⟩, hq⟩, e⟩ := f.ge (hp.le ⟨_, p.mulVec_single_one i⟩).1
      obtain ⟨w, a, e'⟩ := congr(($(U.form_mul_inv_eq _) *ᵥ _) ∘ 𝔰.besselFrame).trans congr($φᵀ i),
        mem_link.1 h'
      rw [← mulVec_mulVec] at w; set u := γ⁻¹.1.1 *ᵥ _
      simp [funext_iff, middleGram, splitGram, mulVec_eq_sum, Fin.forall_fin_succ'] at hq e w
      have l := (link γ).sub_mem ⟨_, isotropicFramePair_mulVec_eq_zero_iff.2 ⟨fun _ ↦ rfl, w.1⟩,
        rfl⟩ h
      have f := by simpa [funext_iff] using
        eq_zero_of_ratMiddle_form_eq_zero (u ∘ .inr ∘ .inl - z ∘ .inr) (by simp [*]) (by
        simpa [-Finset.sum_add_distrib, dot_mulVec_eq_sum_sum, u, P, *, ← neg_add,
          -neg_add_rev] using mem_link_iff_orthogonal.1 l _ l)
      use (y.2.1.1 *ᵥ (a ⊕ᵥ (z ∘ .inr ⊕ᵥ 0))) ∘ .inl ⊕ᵥ (u ∘ .inl - a); show _ = _ *ᵥ u - _
      simp [funext_iff, mulVec_eq_sum, sub_mul, P, w.1] at e' ⊢; grind-linarith only
    refine ⟨_, ⟨((S.principalLevel_eq_unitaryLevel.le ⟨k' * k⁻¹, by simp [*], rfl⟩).2.mul (N :=
      S.classCoord c * (finAdeleMat P * a.1)) (by simpa [IsIntMatrix, P,
      classCoord_eq_fromBlocks] using hb)).neg.mulVec hy, -(S.gIdele⁻¹ • finAdeleMat w * a.1) *ᵥ r,
      ?_⟩, ?_⟩ <;> simp [-sub_mulVec, ← smul_mulVec, -coe_units_inv] <;> congr
    simpa [↓← classCoord_mul_isotropicFramePair, ek, ek', coe_termPosition, Matrix.map_sub,
      classCoord, ← (classBasis _).1.mul_assoc, -coe_units_inv]
      using! congr(S.classCoord c * finAdeleMat ($hw) * a.1)
    simp [← ek', by simpa [↓← frameImage_mul] using congr($((U.gram_invariant (k' * k⁻¹).1
      (frameImage k) (S.classCoord c * finAdeleMat P)).trans (by erw [ek, frameImage_termPosition,
      classCoord_gram, φ])) * a.1)]
    simp [entrywise, P, classCoord_eq_fromBlocks, splitGram]
  conv_lhs => simp [ENat.card_eq_coe_natCard, ← Finset.sum_mul]
  grw [sum_latticeDisc_inv_le, ← ofReal_natCast]
  simp (disch := positivity) only [mul_pow, ← ofReal_mul, ofReal_le_ofReal_iff, inv_pow, field]
  rw [← pow_succ, sq S.tailScale, mul_pow]; nth_grw 3 [← pow_le_tailScale le_rfl]
  simp [← pow_mul, mul_assoc, ← pow_add]; gcongr; lia

attribute [local instance] IsFiniteMeasure.toSigmaFinite Side.cut

/-- For the cut Bessel functions and stable T with 𝗀 ≠ 0 on T, ‖A_T(c,s,c')‖ is at most the sum of
ν·`classSize` ⊤ (∏_v|𝗀(γ)|_v) over the near terms γ of T over (c,s,c') that are the chosen
representatives of 𝖴⁰_c(g)γ𝖴⁰_c'(g); ν = `Filling.unipCovolume`, 𝗀 = `Filling.termDisc`. -/
lemma enorm_amplitudeSum_le_classSize_top (hT : S.IsStable T) (h : ∀ γ ∈ T,
  S.termDisc γ ≠ 0) c s c' : ‖S.amplitudeSum T c s c'‖ₑ ≤ ∑' γ : ↥(T ∩ S.termsOver c s c'),
  ite (S.IsNearRep c c' γ) (.ofReal (S.unipCovolume * S.classSize ⊤ (S.termDiscNorm γ))) 0 := by
  choose ω _ ωs ωt ω1 ωS using Exists.intro _ (isBoxPartition_epsilon c')
  choose ρ R using (exists_maximalFor_of_wellFoundedGT _ (S.IsNearRep c c') <|
    @Quot.exists_rep _ (setoid (S.classUnip c) (S.classUnip₀ c')) ·)
  choose G F C using (hasSum_amplitudeSum_change_of_weight (σ := ·) hT c s c'
    (fun γ y ↦ ite (ρ ⟦γ⟧ = γ) 1 0 * ω ((S.ratToInf γ)⁻¹ * y)) fun γ o y ↦ by
    simp [mul_assoc, -ite_mul, ENNReal.tsum_comm]
    apply ωt; intro x
    let g := γ * x⁻¹
    choose u k v m e using (eq (a := g)).1 (R ⟦g⟧).1.symm
    refine ENNReal.tsum_prod ▸ .trans (tsum_congr fun (b, a) ↦ if_congr
      (((congrArg ρ ((eq (b := g)).2 ⟨_,
      one_mem _, _, b.2, by simp [g, mul_assoc]⟩)).trans e).congr_left.trans ⟨fun f ↦ ?_,
      by simp_all [g, mul_assoc]⟩) rfl rfl) (tsum_ite_eq ⟨⟨⟨v, m.1⟩, m⟩⁻¹, u, k⟩ 1)
    obtain ⟨⟨w, l⟩, ⟨⟩⟩ := mul_left_surjective ⟨u, k⟩ a
    have e' := by simpa [mul_assoc] using congr($f * b)
    cases eq_one_of_mem_besselU_of_fix (B := frameImage g.1.1 * (S.frameProducts g)⁻¹.submatrix id
      _) l.1 (by erw [← Matrix.mul_assoc, ← frameImage_mul, ← e', frameImage_mul_of_mem_besselU0
      (mul_mem m b.2).2]) (by simpa [frameGram, splitGram, entrywise] using congr($(mul_nonsing_inv
                                _ (hasLevel_last (h g (by
      simpa using! (hT 1 (by simp) _ x⁻¹.2.1 _).2 o.1))).2.1.isUnit).submatrix .castSucc .castSucc))
    clear * - e'; simp_all [g, Subtype.ext_iff, mul_eq_one_iff_eq_inv'])
  grw [← (G _).tsum_eq, enorm_tsum_le_tsum_enorm]; gcongr with γ
  split_ifs with e n <;> simp <;> try
    refine Not.imp_symm exists_ne_zero_of_integral_ne_zero fun ⟨a, z⟩ ↦ ?_
  obtain ⟨_, C, ⟨_, p, q⟩, N⟩ := S.unipCovolume_pos, C .full, n.1,
    n.1.le_classSize_and_cellMass_le (one_le_prod_norm_Φ (by
    apply_rules [IsIntegral.det, fun _ _ ↦ isIntegral_frameProducts γ.2.2 .., IsIntegral.pow,
      isIntegral_natCast, map_isIntegral_int, IsIntegral.mul, IsIntegral.sub]) (h _ γ.2.1))
  choose B l m τ hB _ H _ _ hl ht using fun v ↦
    (S.besselSys v).open_cell (by simp [gramDiscReal_realFrameGram_ratToInf, Finset.prod_pos,
    γ.2.1, *]) (p v).1 (q v).1 (le_self_pow₀ S.one_le_b nofun)
  choose x ht T using (exists_notMem_null_le_lintegral (Measurable.aemeasurable (by fun_prop))
    (Measure.ae_pi_le_pi (Filter.eventually_pi ht))).imp fun _ ↦ And.imp of_not_not
    (IsL2Contraction.pi (by fun_prop) (fun _ _ _ ↦ ContinuousOn.integrableOn_compact (hB _)
    (by fun_prop)) H (ω · |>.toReal) 1 (by fun_prop) (by simp [toReal_le_of_le_ofReal, *])).trans'
  have I σ := ((F σ γ).comp_mul_left (S.ratToInf γ * fun v ↦ τ v (x v))).restrict (s := univ.pi B)
  grw [← ENNReal.le_tsum γ, N.1, ← lintegral_mul_left_eq_self, ← enorm_toReal_smul_le,
    ← setLIntegral_le_lintegral, ← enorm_integral_le_lintegral_enorm] at C
  simp [e, smul_sub] at C I
  grw [← integral_mul_left_eq_self, ← setIntegral_eq_integral_of_forall_compl_eq_zero
    fun y ↦ Not.imp_symm fun z ↦ ?_, ← sub_eq_iff_comm.1 (integral_sub (I _) (I _)).symm,
    ← add_halves (S.unipCovolume * _), enorm_sub_le, C, ofReal_add, ENNReal.add_le_add_iff_right,
    ← ENNReal.pow_le_pow_left_iff two_ne_zero, ← ofReal_pow, ← N.2, ← hl,
    euclidean_enorm_sq_eq_sum, ← (Equiv.arrowProdEquivProdArrow ..).sum_comp]
  simp [↓eval_integral_piLp (I _).eval_piLp, volume_pi, Measure.restrict_pi_pi, besselKernel,
    besselFn, mul_assoc, ωS, ht _, ← ofReal_norm] at T ⊢
  grw [T, ofReal_toReal_le, ω1]; simp [Measure.pi_univ, ofReal_prod_of_nonneg]
  any_goals rw [classSize]; finiteness
  all_goals simp [toReal_eq_zero_iff] at z; let hy := inCut_of_besselKernel_ne_zero z.2
  exact fun v _ ↦
    (ht v).2 _ (by simpa [mul_assoc, frameBox, frameVector_mul, ht _] using ωs _ v z.1.1 (hy v).2)
    ((hy v).1.trans (pow_right_mono₀ S.one_le_b (by nlinarith [S.ϱ_le])))
  choose u H B using exists_classUnip_mul_mem_boxedPoints c (hy · |>.1)
  choose a A b B' o using mk_out_eq_mul (S.classUnip₀ c) _ (u * γ)
  exact n (e ▸ (R _).2 ((eq ..).2 ⟨_, mul_mem A.1 H, b, B', o.trans (by group)⟩).symm
    (fun h ↦ (n (e ▸ h)).elim) ⟨o ▸
    .mul_of_mem_besselU0 ⟨_, B, by simp [boxedPoints, *, -Pi.mul_apply]⟩ A.2 B'.2, by simp⟩)

/-- For the cut Bessel functions and stable T of level j, ‖A_T(c,s,c')‖ is at most the sum of
ν·`Filling.classSize` j (`Filling.classGauge`) over near terms of T over (c,s,c') that represent
their classes 𝖴⁰_c(g)γ𝖴⁰_c'(g), and is 0 unless s agrees. -/
lemma enorm_amplitudeSum_le_classSize (hT : S.IsStable T) {j} (h : ∀ γ ∈ T, S.HasLevel j γ) c s
  c' : ‖S.amplitudeSum T c s c'‖ₑ ≤ ∑' γ : {γ ∈ T ∩ S.termsOver c s c' | S.Agrees s ∧
  S.IsNearRep c c' γ}, .ofReal (S.unipCovolume * S.classSize j (S.classGauge j c c' γ)) := by
  by_cases! ¬S.Agrees s; simp [amplitudeSum_eq_zero_of_not_agrees, *]
  let K := {γ | S.N ^ numInfPlaces E * S.minorNorm j γ < S.termDiscNorm γ}
  have sK : S.IsStable (T \ K) := by simp_all [IsStable, K, minorNorm, termDiscNorm,
    frameDisc_frameGram_besselU_mul, leadingMinor_frameGram_besselU_mul]
  have ι k : S.xRowsIndex ⊤ k = 1 :=
    relIndex_eq_one.2 (colLattice_le (col_mem_colLattice <| Subtype.mk · (by simp)))
  have p γ : S.termDisc γ = 0 → γ ∉ K := by simp_all [K, termDiscNorm, minorNorm]; bound
  simp [amplitudeSum_split T K]
  grw [← tsum_extend_zero Subtype.val_injective, ← tsum_comp_le_tsum_of_injective
    Subtype.val_injective, Summable.tsum_union_disjoint, enorm_add_le, amplitudeSum,
    enorm_tsum_le_tsum_enorm, enorm_amplitude_le, enorm_amplitudeSum_le_classSize_top,
    tsum_setElem_eq_tsum_setElem_sdiff _ _ fun _ ↦ id, tsum_mono_subtype (t := ⋃ δ ∈ {δ ∈ T \
    K ∩ S.termsOver c s c' | S.IsNearRep c c' δ}, doubleCoset δ (S.classUnip₀ c) (S.classUnip₀ c')),
    tsum_biUnion_le_tsum]
  gcongr with x x <;> obtain ⟨γ, ⟨t, k⟩, w⟩ := x
  simp [*, t.1, tsum_amplitudeAbs_class_le k _ (not_lt.1 t.2), Function.extend_val_apply]
  cases show j = ⊤ by grind [HasLevel]
  split <;> simp [*, classGauge, k.out.le, Function.extend_val_apply]
  exact fun γ ⟨⟨t, w⟩, z⟩ ↦ (mk_out_eq_mul _ _ γ).elim fun u ⟨a, v, b, o⟩ ↦ mem_biUnion ⟨o ▸
    ⟨(sK u⁻¹ (inv_mem a.1.1) _ b.1.1 _).2 t, by simpa using termsOver.mul (.mul a.1.2 w) b.1.2⟩,
    o ▸ .mul_of_mem_besselU0 (((pow_ne_zero 2 z).pos.trans_le amplitudeAbs_sq_le).ne'.imp_symm
    (by simp +contextual [schurIntegral, schurWeight, boxCutoff, indicator, IsNear, -mul_ite])) a.2
    b.2, by simp⟩ ((mem_quotToDoubleCoset_iff ..).2 rfl)
  repeat first | grind | simp_all [IsStable]
end Filling
end

-- part: New.Filling.CrudeEnergy
section
/-! Incoherent and degenerate pairs are negligible. The second moment of the Poincaré series expands
over pairs of rational elements congruent mod g, and discriminant gains, lattice counts and a
weighted Schur test isolate the main term by showing that degenerate terms and pairs with different
Levi parts are negligible and that the rest shrink where frames meet mod g. Discarding small cells
and off-diagonal terms of Petersson-type and relative trace formulas by congruences and counts is
known. Related work: Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023;
Kowalski–Saha–Tsimerman, Local spectral equidistribution for Siegel modular forms, 2012; Blomer,
Density theorems for GL(n), 2023.

Part of: Agreeing characters force shared vectors up the flag (see New.Filling.BoxPartition).

This file: Agreeing characters with vanishing discriminant force a level; disagreeing terms
contribute zero. Energy of a stable set: incoherent and degenerate pairs of terms are negligible. -/

open Fin Classical ENNReal Matrix MeasureTheory MulAction Set

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰}

/-- Under the standing hypotheses, if T is stable under the rational points of 𝖴 on both sides
and no γ in T satisfies `Filling.CharsAgree` (agreement of the finite characters on 𝖴 ∩ γ𝖴γ⁻¹),
then the sum of amplitudes of T over every (c, s, c') vanishes. -/
lemma Filling.amplitudeSum_eq_zero_of_not_charsAgree [StablyUnram E]
    [S.IsAdmissible] [Side] {T} (hT :
  S.IsStable T) (h : ∀ γ ∈ T, ¬S.CharsAgree γ) c s c' : S.amplitudeSum T c s c' = 0 := by
  choose φ _ w _ q using (S.exists_cutoff_classUnip <| stabilizer _ (α := _ ⧸ S.classUnip c') ·)
  choose a e using @Quotient.mk_out _ (orbitRel (S.classUnip c) (_ ⧸ S.classUnip c'))
  refine (hasSum_amplitudeSum_change_of_weight hT c s _ (fun γ ↦ (S.classCutoff c' (S.ratToInf
    γ)⁻¹ * indicator {x | x = a x • x} 1 γ) • φ γ) fun γ _ y ↦ ?_).1.unique (hasSum_zero.congr_fun
    fun γ ↦ (h _ γ.2.1).imp_symm fun n _ a _ b e ↦ eq_of_inv_mul_eq_one (n.imp_symm fun z ↦ ?_))
  simp [tsum_classCutoff_eq_one, show ∀ u : S.classUnip c, ↑(u * γ) =
    u • (γ : _ ⧸ S.classUnip c') by tauto]
  erw [← (Equiv.mulRight (a γ)).tsum_eq, ← w (a γ • γ) (S.ratToInf (a γ) * y),
    tsum_subtype _ fun u : S.classUnip c ↦ φ _ (S.ratToInf u * _)]
  simp +contextual [indicator, *, mul_assoc, mul_smul]
  simp [mul_smul, integral_smul, (fun i ↦ ((q γ).integral_orbitMeasure i).symm.trans
    (integral_quotMeasure_eq_zero_of_twist volume (i ⟨·, ·⟩) continuous_besselKernel
    (by simp [unipotentChar]) z (mul_inv_eq_of_eq_mul e ▸ besselKernel_besselU_mul a b γ))) fun ⟨_,
    u, h, rfl⟩ y ↦ by simp [besselKernel, mul_assoc, besselFn_mul_of_mem_classUnip u,
    ← besselFn_mul_of_mem_classUnip ⟨_, QuotientGroup.eq.1 h.symm⟩ (_ * y)]]

/-- If γ satisfies `Filling.CharsAgree` and the frames f, γf share a vector with leading
coefficients
c, c' at index a, then cc̄ = c'c̄' and they share such a vector at every index b ≥ a. -/
lemma Filling.hasCommonFlagVector_of_le {γ} (hr : S.CharsAgree γ) a c c' (h : HasCommonFlagVector γ
  c c' a) : c * star c = c' * star c' ∧ ∀ b ≥ a, HasCommonFlagVector γ c c' b := by
  induction' a using reverseInduction with a i <;> have ⟨x, y, _⟩ := h
  grind [star_mul_last_eq_of_frameImage_eq]
  have := exists_mulVec_eq_of_annihilator (frameImage 1) (frameImage γ) (Iio a.succ) (Iio a.succ)
    (cons 0 (init x)) (cons 0 (init y)) fun l h k ↦
    (algebraMap E (𝔸f E)).injective (eq_of_ψf (denseRange_algebraMap_finAdele.eq fun t ↦ ?_))
  grind [i (this.imp (by simp [forall_fin_succ, init]; grind))]
  have ⟨v, Z⟩ := exists_star_vecMul_eq S.ratGram (l ᵥ* γ)
  let r := S.g * S.ϖ * -t
  obtain ⟨⟨u, a, _⟩, w, b, _⟩ := exists_mem_besselU_eq_eichlerMap _ x r (by simp [star_mulVec,
    ← U.form_mul_inv_eq, ← Z ▸ vecMul_vecMul ..] : star (γ *ᵥ v) ᵥ* S.ratGram =
    l ᵥ* 1) (by grind) h, exists_mem_besselU_eq_eichlerMap _ y r Z (by grind) k
  simpa [*, r, unipotentChar, gIdele, selfDualChar, ratToFin, simpleRootSum_adelicToFin, ← map_mul,
    mul_assoc, Circle.ext_iff, -vecMul_one] using! hr u a w b (by ext : 2; simp [*, ext_iff_mulVec,
    U.form_mulVec_mulVec, ← mulVec_mulVec, frameImage_mulVec γ.1.1, eichlerMap_mulVec, mulVec_sub])

/-- If γ satisfies `Filling.CharsAgree` (the finite characters agree on 𝖴 ∩ γ𝖴γ⁻¹) and 𝗀(γ) = 0,
then γ has level j, in the sense of `Filling.HasLevel`, for some j ≤ ϱ.

Agreeing characters force shared vectors up the flag. -/
lemma Filling.CharsAgree.exists_hasLevel {γ} (hr : S.CharsAgree γ) (h : S.termDisc γ = 0) : ∃ j,
  S.HasLevel j γ := (exists_minimal_of_wellFoundedLT (IsNormalForm ·.1 γ) ⟨⊤, 1, by simp; lia⟩).imp
  fun j m ↦ have M x y (e : frameImage 1 *ᵥ x = frameImage γ.1.1 *ᵥ y) (z : ∀ i, j ≤ i.castSucc →
    y i = 0) : ∀ a, x a = 0 ∧ y a = 0 :=
    WellFoundedGT.fix fun a _ ↦ by grind [IsNormalForm, Minimal, star_one, star_eq_zero,
    fun s ↦ hasCommonFlagVector_of_le hr a (s⁻¹ * x a) (s⁻¹ * y a) ⟨s⁻¹ • x, s⁻¹ • y, by aesop⟩]
  (fun d ↦ ⟨m.1, d, iff_of_false ((exists_mulVec_eq_single_det (S.frameProducts γ)).elim fun y a e ↦
    d (last_le_iff.1 e ▸ (by grind [frameDisc, star_eq_zero, (norm_sq_middle_part_eq a.1 rfl).2
    _, by simpa using congr(‖Φ ofNonempty $(sub_eq_zero.1 h)‖)] : (S.frameProducts γ).det = 0)))
    (· h)⟩) ((exists_mulVec_eq_zero_iff.2 ∘ det_paddedLeading.trans).mt fun ⟨y, Z⟩ ↦ by
  simp [funext_iff, paddedLeading, (of _).mulVec_apply_eq_sum, ← mulVec_apply_eq_sum] at Z
  grind [sq_nonneg, by simpa using (norm_sq_middle_part_eq (D := 0) (.trans (dotProduct_eq_zero
    (S.frameProducts γ *ᵥ y) fun w ↦ (exists_frameImage_eq_of_isNormalForm m.1.inv (star w)).elim
    fun _ ⟨_, _, e⟩ ↦ by grind [dotProduct, Pi.star_apply, star_star, Finset.sum_eq_zero, by
    simpa [star_mulVec_dotProduct] using congr(star $(frameProducts_mulVec_of_frameImage_eq e) ⬝ᵥ
      y)]) (by simp)) rfl).2 ofNonempty])

attribute [-instance] IdemSemiring.toCanonicallyOrderedAdd IdemSemiring.toMulLeftMono
  IdemSemiring.toMulRightMono

attribute [local instance high] Side.cut

attribute [local irreducible] Filling.classGauge Filling.mainEnergy Filling.saturationIndex
  Filling.termPosition Filling.frameValueIndex link

variable [StablyUnram E]

variable [ok : S.IsAdmissible] {C w : ℝ} (hC : 0 ≤ C) {Ω : Set _} {T X} (hT : S.IsStable T)
  (h₁ : (∃ γ ∈ T, ∃ c c', ∃ s ∈ Ω, γ ∈ S.termsOver c s c' ∧ IsNormalForm 0 γ) →
  S.tailScale ^ 20 * S.besselEnergy ≤ C)
  (hx : X ≠ 0) (hq : ∀ s ∈ Ω, S.FixesNormAtLeast s X) (hw : 0 ≤ w) (hz : S.besselEnergy ≤ C)

include hC hT h₁ hx hq hw hz

/-- Put 𝖽₁ = `Filling.besselEnergy`, 𝖽 = `Filling.mainEnergy`, τ = `Filling.tailScale`, ν =
`Filling.unipCovolume`; "s fixes X" is `Filling.FixesNormAtLeast` s X.
T stable of level j, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, ≥ τ²⁰𝖽₁ if a term has `IsNormalForm`
0, ≥ τ¹²𝖽/X^|κ| if j > ϱ and R omits a link. If cut `Filling.linkEnergy` ≤ wν², the cut energy
is ≤ w + C/(b³⁰4^(ϱ+1−j)).

Incoherent and degenerate pairs are negligible. -/
lemma Filling.energy_le_of_level_pairs j R (hc : ∀ γ ∈ T, S.HasLevel j γ) (h₂ : 𝔰.ϱ < j →
  (∃ Λ, Λ ∉ R) → S.tailScale ^ 12 / X ^
  𝔰.k * S.mainEnergy ≤ C) (h : linkEnergy T Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) : energy
  (S.amplitudeSum T) Ω ≤ w + C / S.b ^ 30 / 4 ^ j.rev.1 := S.of_size_bounds fun g t u z v y ↦ by
  intros; simp_rw [energy, ← Finset.sum_div]; grw [div_le_iff₀, ← ofReal_le_ofReal_iff, add_mul,
    ofReal_add, ← h, ← (?_ : ∑ c, ∑ c', ∑' (a) (b),
    .ofReal (C / S.tailScale ^ 3 * S.unipCovolume ^ 2) * (S.pairWeight j c
    c' b a + S.pairWeight j c c' a b) ≤ .ofReal _), linkEnergy] <;> try positivity
  simp (disch := intros; positivity) [← Finset.sum_subtype_eq_sum_filter, ofReal_sum_of_nonneg]
  have m {α β : Type} (f : α → ℝ≥0∞) g : tsum f * tsum g = ∑' p : α × β, f p.1 * g p.2 := by simp
  have B Λ := enorm_amplitudeSum_le_classSize (T :=
    T ∩ link ⁻¹' {Λ}) (by grind [IsStable, link_besselU_mul]) (hc · ·.1)
  simp_rw [amplitudeSum, ← ((summable_amplitude T ..).hasSum.tsum_fiberwise (link ∘ (·.1))).tsum_eq]
  grw [enorm_tsum_le_tsum_enorm]; simp_rw [← tsum_image _ injOn_subtype_val, tsum_subtype
    (_ '' _), preimage_comp, Subtype.image_preimage_coe, T.inter_right_comm _ (_ ⁻¹' _),
    ← tsum_subtype, ← amplitudeSum.eq_1, sq, m, ← ENNReal.summable.tsum_add_tsum_compl
    (s := Function.diag '' R) (by simp), Finset.sum_add_distrib]
  gcongr; exact ((Equiv.Set.image _ R fun _ _ ↦ by simp).tsum_eq _).ge
  grw [ENNReal.sum_le_tsum, B, B]; simp_rw [m, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_sigma]
  refine (ENNReal.tsum_le_tsum fun ⟨s, π, ⟨γ, ⟨⟨m, e⟩, a⟩, n⟩, γ', ⟨⟨m', e'⟩, a'⟩, _⟩ ↦ ?_).trans
    (tsum_comp_le_tsum_of_injective (f := fun ⟨_, _, a, b⟩ ↦ ⟨a, b⟩) ?_ _);
  (iterate 2 rintro ⟨⟨⟩, ⟨⟨⟩⟩, ⟨_, ⟨⟨⟨_, ⟨⟩⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩⟩⟩, _, ⟨⟨⟨_, ⟨⟩⟩⟩⟩⟩); rintro ⟨⟩; rfl; dsimp
  have k := hc _ m; apply hc at m'; specialize hq _ s.2; obtain ⟨⟨i, r, l, L⟩, ⟨-, ⟨d⟩⟩, ⟨-, ⟨d'⟩⟩,
    ⟨⟨_, p⟩, -⟩, ⟨⟨-, q⟩⟩⟩ := pairInvariant_mul_le n.1 a k hq a' m',
    one_le_xRowsIndex_and_saturationIndex a k, one_le_xRowsIndex_and_saturationIndex a' m',
    exists_link_split_le_classGauge n.1 a k hq γ', exists_link_split_le_classGauge n.1 a' m' hq γ
  unfold pairWeight termWeight invPowWeight pairInvariant commonLink classSize countWeight at *; set
    D := ite (𝔰.ϱ < j) S.mainEnergy _
  have H : S.tailScale ^ 4 * D * (2 * S.tailScale ^ 2) ^ (j - 𝔰.ϱ) * S.codimFactor ^ i / ite
    (𝔰.ϱ < j ∧ i = 0) X 1 ^ 𝔰.k ≤ C / S.tailScale ^ 3
  · clear * - t u v y h₂ h₁ l k m a e e' hz
    induction' j using lastCases with j <;> simp [Nat.sub_eq_zero_of_le, D, is_le, ← not_le]
    · cases i; · grw [← h₂ (by simp) ⟨π.1.1, by grind⟩, t]; simp [field]; bound
      grw [pow_le_of_le_one _ codimFactor_le_one, ← hz, ← ok.mainEnergy_le,
        t] <;> simp [field] <;> bound
    grw [codimFactor_le_one]; rcases j with ⟨⟨⟩⟩
    · grw [← h₁ ⟨_, m, _, _, _, s.2, a, k.1⟩]; simp [field]
    grw [← hz, ← le_self_pow₀] <;> simp [field] <;> bound
  repeat rw [ite_eq_left (by simp [*]; use s)]
  rw [inf_comm (link γ')] at *; have M := L; grw [z] at L
  nth_grw 1 [← show 1 ≤ ite _ X 1 by lia, ← d, ← d', ← g, ← p, ← q] at M; grw [tsub_le_iff_left.2
    (r.trans_eq (add_assoc ..)), ← H, mul_add, ← (ENNReal.pow_le_pow_left_iff (by simp)).1 (.trans
    ?_ ((mul_le_mul' le_self_add le_add_self).trans (sq _).ge))]; simp (disch := positivity) only
    [D, ← ofReal_mul, ← ofReal_pow, ← div_le_iff₀'] at *; nth_grw 2 [pow_succ _ 𝔰.k, ← M]
  grw +useKAbstract [← L]; simp (disch := positivity) only [mul_pow, div_pow, Real.sq_sqrt,
    (submoduleIndex ..).cast_mul, submoduleIndex_smul_intVectors S.gIdele_mem, Fintype.card_subtype,
    card_filter_val_lt, S.gIdele_val ▸
    genIndex_natCast _]; congr! 1; field; any_goals nlinarith only [t]
  simp [ENNReal.tsum_add, ← Finset.mul_sum]
  grw [ENNReal.tsum_comm.le, sum_pairWeight_le]
  simp (disch := positivity) only [← ofReal_mul, ← ofReal_add, ofReal_le_ofReal_iff, field]
  ring_nf; grw +useKAbstract [show 4 ≤ S.b by linarith, ← pow_le_tailScale (e := 𝔰.ϱ + 1 - j + 31)
    (le_mul_of_le_of_one_le (by lia) NeZero.one_le)]; ring_nf; rfl

omit hw in
/-- Letters as in `Filling.energy_le_of_level_pairs`.
T stable, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, and ≥ τ²⁰𝖽₁ if a term has `IsNormalForm` 0. If each γ
∈ T with `Filling.CharsAgree` has a level below n ≤ ϱ+1, the cut energy is ≤ C/(b³⁰4^(ϱ+1−n)). -/
lemma Filling.energy_le_of_level_lt n (h : ∀ γ ∈ T, S.CharsAgree γ → ∃ j < n, S.HasLevel j γ) :
    energy (S.amplitudeSum T) Ω ≤ C / S.b ^ 30 / 4 ^ n.rev.1 := by
  induction' n using induction with j ih generalizing T
  · simp [energy, amplitudeSum_eq_zero_of_not_charsAgree hT (by grind)]; positivity
  grw [amplitudeSum_split _ {γ | S.HasLevel j.castSucc γ}, energy_add_le one_pos, ih,
    energy_le_of_level_pairs hC _ _ hx _ le_rfl _ j.castSucc ∅ (h := by simp [linkEnergy])]
  simp [rev_castSucc, pow_succ, field]; all_goals grind [IsStable, S.isStable_hasLevel j.castSucc]

/-- Crude estimate (letters as in `Filling.energy_le_of_level_pairs`):
T stable, all s ∈ Ω fixing X ≥ 1; C ≥ 𝖽₁, ≥ τ²⁰𝖽₁ if a term has `IsNormalForm`
0, ≥ τ¹²𝖽/X^|κ| if R omits a link. If cut `Filling.linkEnergy` (𝗀 ≠ 0) ≤ wν², the full energy
is ≤ (1+b⁻⁴)²w + b⁻¹²C.

Incoherent and degenerate pairs are negligible. -/
lemma Filling.energy_le_of_linkEnergy_le R (h₂ : (∃ Λ, Λ ∉ R) →
  S.tailScale ^ 12 / X ^ 𝔰.k * S.mainEnergy ≤ C)
  (h : linkEnergy (T ∩ {γ | S.termDisc γ ≠ 0}) Ω R ≤ .ofReal (w * S.unipCovolume ^ 2)) :
  energy (S.amplitudeSum (σ := .full) T) Ω ≤ (1 + (S.b ^ 4)⁻¹) ^ 2 * w + (S.b ^ 12)⁻¹ * C := by
  obtain ⟨⟨y, _, e⟩, p⟩ := exists_nonneg_add_of_le S.thousand_le_b,
    (by bound [S.thousand_le_b] : 0 < S.b ^ 4)
  grw [← sub_add_cancel (S.amplitudeSum (σ := _) T) (S.amplitudeSum T), energy_add_le p,
    energy_sub_cut_le, amplitudeSum_split, energy_add_le p, energy_le_of_level_pairs hC _ _ hx _ _ _
    (last _) R _ _ h, energy_le_of_level_lt hC _ _ hx _ _ (last _), hz, ← e, ← sub_nonneg]
  simp [field, -sub_nonneg]; ring_nf; positivity
  all_goals grind [CharsAgree.exists_hasLevel, HasLevel, IsStable, frameDisc_frameGram_besselU_mul,
    hasLevel_last]
end

-- part: New.Heights.OneDeterminant
section
/-! Few translates nearly span; height of one Gram determinant. If translates of a linear map spread
modulo every subspace, a logarithm times the least possible number of them nearly span the target,
and for a family completed to a basis the ratio of twisted to untwisted volume has height at most
the Gram size plus twice the index plus a cost per added vector. Greedy covering with a logarithmic
loss and size-versus-divisibility bounds for a determinant are known. Related work: Wolsey, Greedy
algorithm for the submodular set covering problem, 1982; Bost, Algebraic leaves of algebraic
foliations over number fields, 2001; Laurent, Linear forms in two logarithms and interpolation
determinants, 1994.

Part of: Second moment of the Poincaré series with constant one (see New.Filling.Moments).

This file: Positive-type functions avoid singular minors; Hilbert-Schmidt variance inequality giving
spread. Few translates nearly span; height bound for a ratio of Gram determinants. -/

open Module InnerProductSpace Finset EuclideanSpace Complex Matrix WithLp Fintype AddChar Submodule
  OrthonormalBasis LinearMap
variable {G H k n m} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Field k]
  [Fintype n] [Fintype m] (b : OrthonormalBasis m ℂ H) {u v : G → H}

lemma inner_sum_sum_eq_card_mul f (h : ∀ a b, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) : ⟪∑ a, u a, ∑ a, v a⟫_ℂ =
  card G * univ.sum f := by simp [↓sum_inner, inner_sum, h, (Group.mulLeft_bijective _).sum_comp]

/-- Let π represent a finite group on 𝔽_q^n, π' be contragredient, A, A' n × m matrices, Θ ≥ 0
of positive type. If the fixers of Av, A'v (v ≠ 0) have Θ-mass ≤ Y, then q·Θ{det A'ᵀπ(s)A =
0} ≤ 2Θ(G) + q^(m+n/2) Y. -/
lemma card_mul_sum_det_le [Fintype k] (π : G →* GL n k) (A : _ → Matrix n m k) {Θ} (h0 : ∀ s, 0 ≤ Θ
  s) (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) Y (hY : 0 ≤ Y) (h : ∀ b, ∀ v ≠ 0, ∑ s with A b *ᵥ v =
  cond b invTransposeGL 1 (π s) • A b *ᵥ v, Θ s ≤ Y) : card k * ∑ s with ((A true)ᵀ *
  (π s).1 * A false).det = 0, Θ s ≤ 2 * univ.sum Θ + card k ^ card m * √(card k ^ card n) * Y := by
  set r := √_
  obtain ⟨ψ, p⟩ : ∃ _, _ := ⟨_, FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  have N {c : (n → k) → EuclideanSpace ℂ (n → k)} (h : Orthonormal ℂ c) {σ : MulAut _} x :
      ∑ s with x = σ (π s) • x, Θ s = ‖∑ a, c (σ (π a) • x) ⊗ₜ[ℂ] u a‖ ^ 2 / card G
  rw [@norm_sq_eq_re_inner ℂ, inner_sum_sum_eq_card_mul (ofReal ∘ _)]
  simpa using sum_filter ..
  simp [*, orthonormal_iff_ite.1, apply_ite ofReal, mul_smul, eq_inv_smul_iff]
  let W y v s := ψ (y ᵥ* (A true)ᵀ ᵥ* π s ᵥ* A false ⬝ᵥ v) * Θ s
  apply ((sum_mono fun y ↦ univ.expect_le_expect fun v _ ↦ (?_ : re (∑ s, W y v s) ≤
    ite (y = 0) (∑ s, Θ s) 0 + ite (v = 0) (∑ s, Θ s) 0 + r * Y)).trans _).trans'
  simp [W, -ite_mul, sum_comm, mul_sum, sum_filter, apply_ite, ↓← re_expect, ← sum_mul, ← mul_assoc,
    expect, NNRat.smul_def, sum_addChar_dotProduct p]
  gcongr; repeat' split
  cases exists_vecMul_eq_zero_iff.2 ‹_›
  grw [← card_univ, card_le_card_of_injOn _ _ (smul_left_injective _ (by tauto)).injOn]
  on_goal -1 => apply flip id (add_le_add (h true y _) (h false v _))
                grw [@N fun x ↦ toLp 2 fun ζ ↦ ψ (-x ⬝ᵥ ζ) / r, N orthonormal_single, ← add_div,
    ← two_mul_le_add_sq, mul_assoc, ← @re_inner_le_norm ℂ, inner_sum_sum_eq_card_mul (W y v · / r)]
  all_goals simp [*, smul_vecMul, mul_nonneg, expect_add_distrib, NNRat.smul_def, W, r, add_nonneg,
    sum_nonneg', inner, field, vecMul_mulVec, ← Matrix.mul_assoc, orthonormal_iff_ite, two_mul,
    invTransposeGL, dotProduct_mulVec, div_mul_div_comm, ← map_neg_eq_conj, ← map_add_eq_mul,
    ← ofReal_mul, transposeGL,
    add_assoc, ← sum_div, neg_add_eq_sub, ← sub_dotProduct, sum_addChar_dotProduct, Units.smul_def]

/-- For a finite family of vectors v_x in H, the tensor ∑_x v̄_x ⊗ v_x, where v̄_x is the vector
of conjugated coordinates of v_x in the orthonormal basis b. -/
noncomputable def dyadSum (v : n → H) := ∑ x, toLp 2 (⟪v x, b ·⟫_ℂ) ⊗ₜ[ℂ] v x

@[simp] lemma inner_dyadSum {l} [Fintype l] (v : n → H) (w : l → H) : ⟪dyadSum b v, dyadSum b w⟫_ℂ =
  ∑ x, ∑ y, ‖⟪w y, v x⟫_ℂ‖ ^ 2 := by simp [dyadSum, ← mul_conj', inner, b.sum_inner_mul_inner,
  @sum_comm n]

/-- Let P : ℂⁿ → H and R : H → H be linear, with Pv − RPv ∈ A for all v ∈ U. Then dim U − ∑_x
‖(P*P − 1)e_x‖ ≤ ‖p_A P‖² + ‖RP‖² in Hilbert–Schmidt norms, p_A the orthogonal projection to
A (first norm written with `dyadSum`). -/
lemma finrank_sub_le_re_inner_dyadSum [FiniteDimensional ℂ H] (P : EuclideanSpace ℂ n →ₗ[ℂ] H) (R :
  End ℂ H) (U A : Submodule ℂ _) {ε} (k : ∑ x, ‖(P.adjoint ∘ₗ P - 1) (.single x 1)‖ ≤ ε)
  (h : ∀ v ∈ U, P v - R (P v) ∈ A) : finrank ℂ U - ε - ∑ x, ‖R (P (.single x 1))‖ ^ 2 ≤
  re ⟪dyadSum b (P <| .single · 1), dyadSum b (stdOrthonormalBasis ℂ A ·)⟫_ℂ := by
  obtain u := stdOrthonormalBasis ℂ U, congrArg re (trace_comp_comm' U.subtype
    (U.orthogonalProjectionOnto ∘ₗ (1 - P.adjoint ∘ₗ P))),
    ((stdOrthonormalBasis ℂ A).sum_sq_norm_inner_right <| orthogonalProjectionOnto _ ·)
  have B (T : End ℂ H) : ∑ i, ‖T (P (basisFun n ℂ i))‖ ^ 2 ≥ ∑ j, ‖T (P (u j))‖ ^ 2
  simp_rw [← b.sum_sq_norm_inner_left, ← adjoint_inner_right, @sum_comm m, sum_sq_norm_inner_right]
  grw [Orthonormal.sum_inner_products_le]; exact u.orthonormal
  simp_all [trace_eq_sum_inner _ (basisFun ..), trace_eq_sum_inner _ u, ← ofReal_pow, norm_sub_rev,
    norm_coe, inner_sub_right, inner_single_left, adjoint_inner_right, -map_sub, sub_eq_iff_eq_add']
  grw (transparency := .all) [re_le_norm, PiLp.norm_apply_le, norm_starProjection_apply_le, ← B,
    ← B A.starProjection, ← sum_add_distrib, ← Aᗮ.norm_starProjection_apply_le (R _)]
  gcongr
  erw [← Aᗮ.starProjection.sub_mem_ker_iff.1 (by aesop), ← norm_sq_eq_add_norm_sq_projection]

open Real NormedField
variable {Θ V W S : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]

/-- For every subspace F of W some index s has dim (B s)⁻¹F ≤ ((1 + φ)/2 + η)·dim V, where φ =
dim F / dim W. -/
def IsSpread {W} [AddCommMonoid W] [Module ℂ W] (B : S → V →ₗ[ℂ] W) η :=
  ∀ F : Submodule .., let φ : ℝ := finrank ℂ F / finrank ℂ W
  ∃ s, finrank ℂ (comap (B s) F) ≤ ((1 + φ) / 2 + η) * finrank ℂ V

/-- Few translates. If η > 0, V ≠ 0 and B is spread (`IsSpread` B η), some finite set t of indices
has #t·dim V ≤ 5·dim W·log(1 + 1/η), and the images of the B s, s ∈ t, span dimension ≥ (1 − 4η)·dim
W. -/
lemma exists_few_translates {B : Θ → V →ₗ[ℂ] W} {η} (hη : 0 < η) (h : IsSpread B η) [Nontrivial V] :
    ∃ t, #t * finrank ℂ V ≤ 5 * finrank ℂ W * Real.log (1 + η⁻¹) ∧
    (1 - 4 * η) * finrank ℂ W ≤ finrank ℂ ↥(⨆ s ∈ t, (B s).range) := by
  let T (t : Finset Θ) := ⨆ s ∈ t, (B s).range
  let ψ (F : Submodule ℂ W) := 5 * finrank ℂ W * Real.log (1 + finrank ℂ (W ⧸ F) / finrank ℂ W / η)
  refine (exists_maximalFor_of_wellFoundedGT (fun t ↦ #t * finrank ℂ V + ψ (T t) ≤ _) T ⟨∅, by
    simp [ψ]; grw [finrank_quotient_le, div_self_le_one]; simp⟩).imp fun t ⟨ht, m⟩ ↦
    (h (T t)).rec fun s _ ↦ ⟨ht.trans' (by bound), ?_⟩; by_contra
  obtain ⟨_ | _, m⟩ := em (finrank ℂ W = 0), @m (insert s t), (T t).finrank_quotient_add_finrank,
    ((T t).mkQ ∘ₗ B s).index_eq_of_finiteDimensional <;> simp_all [T, index, t.iSup_insert]
  grw [range_comp, ker_comp, ker_mkQ, card_insert_le] at *
  have : ψ (T t ⊔ (B s).range) - ψ (T t) ≤ -finrank ℂ V
  grw [← mul_sub, ← log_div, log_le_sub_one_of_pos] <;> try positivity
  rify [field, (quotientQuotientEquivQuotientSup ..).finrank_eq] at *; nlinarith
  simpa [T, m (by grind), finrank_pos.ne']

/-- In a finite-dimensional complex vector space V, a linearly independent family y of n vectors
extends to a basis by adding finitely many members of a spanning set S. -/
lemma exists_extend_basis_of_span_eq_top {n S} {y : Fin n → V} (i : LinearIndependent ℂ y) (h :
  span ℂ S = ⊤) :
  ∃ k z, (∀ a : Fin k, z a ∈ S) ∧ LinearIndependent ℂ (y ⊕ᵥ z) ∧ finrank ℂ V = n + k := by
  choose w a _ j using exists_fun_fin_finrank_span_eq ℂ ((span ℂ (.range y)).mkQ '' S)
  choose z hz e using a
  exists _, z, hz, (linearIndependent_span i).sumElim_of_quotient z (funext e ▸ j :)
  rw [span_image, h, ← range_eq_map, range_mkQ, ← finrank_quotient_add_finrank,
    finrank_span_eq_card i]; simp; lia

/-- One determinant. Let x be a basis of W, u o injective, all conjugates of the Gram determinant of
u o ∘ x of modulus ≤ exp α, γ nonzero with |γ|⁻² of height ≤ g, all finite sums of e at most δ. If
for all ι at l and j : ℂ → ℂ_l the pairing of Λ ι (j∘conj) with Λ ι j is j-integral and a complex
matrix m with |j(det m)| ≥ exp(−e l)·|j(γ ι)|^k recombines u (θ ι) ∘ x into Λ ι j, then the
squared-volume ratios of u (θ ι) to u o have height ≤ α + 2δ + kg. -/
lemma one_determinant {θ : _ → Θ} {H : Θ → Type} [∀ ϑ, NormedAddCommGroup (H ϑ)] [∀ ϑ,
  InnerProductSpace ℂ (H ϑ)] (u : ∀ ϑ, W →ₗ[ℂ] H ϑ) {o} (hu : (⇑(u o)).Injective) [Fintype S] {x :
  S → W} (i : LinearIndependent ℂ x) (hk : finrank ℂ W = card S) {α δ g} (hα : ∀ σ : ℂ ≃+* ℂ, ‖σ
  (gram ℂ (u o ∘ x)).det‖ ≤ Real.exp α) {γ : _ → ℂ} (γ0 : ∀ ι, γ ι ≠ 0) (hγ : HeightLe g fun ι ↦ (‖γ
  ι‖ ^ 2 :)⁻¹) {e : ℕ → ℝ} (he : ∀ U, ∑ l ∈ U, e l ≤ δ) (Λ : ∀ ι : PrimePadicIso, (ℂ →+* ℂ_[ι.1]) →
  Set (H (θ ι))) (k : ℕ) (w : ∀ ι j, ∀ x ∈ Λ ι (j.comp (starRingEnd ℂ)), ∀ y ∈ Λ ι j, ‖j ⟪x, y⟫_ℂ‖ ≤
  1) (l : ∀ ι j, ∃ m, Real.exp (-e ι.1) * ‖j (γ ι)‖ ^ k ≤ ‖j (det m)‖ ∧ ∀ i, ∑ l, m i l • u _ (x
  l) ∈ Λ ι j) : HeightLe (α + 2 * δ + k * g) fun ι ↦ (u (θ ι)).normDet ^ 2 / (u o).normDet ^ 2 := by
  have Z := det_gram_ne_zero_iff_linearIndependent.2 (i.map_injOn _ hu.injOn)
  refine (IsUnit.div_mul_cancel (by simp [Pi.isUnit_iff, *]) _).subst
    (.mul ⟨_, α, 2 • e, Z, hα, fun ι ↦ ?_, by simp [← mul_sum, *]⟩ (hγ.pow k))
  -- at `ι`, the products of the integral combinations for `j ∘ conj` and for `j` are integral
  choose m a b using l ι
  let j := complexToCp ι.2
  have : ‖j (_ᴴᵀ * (_ * (m j)ᵀ)).det‖ ≤ 1 := IsIntMatrix.det_mem (R := valuation.integer.comap j)
    fun i k ↦ star_dotProduct_gram_mulVec (u _ ∘ x) (m _ i) _ ▸ w ι j _ (b ..) _ (b ..)
  -- the Gram determinant is the squared volume (`⟨.neg _⟩`: minus the standard orthonormal basis)
  simp [gram, ← by simpa [normDet_comp_of_finrank_eq, gram, *] using (u · ∘ₗ
    (PiLp.basisFun 2 ..).constr ℂ x |>.normDet_sq_eq_det_gram ⟨.neg _⟩), ← (γ ι).conj_mul'] at *
  grw [← j.comp_apply, ← a, ← a] at *
  simp [j, Z, field, mul_pow, Real.exp_neg, ← Real.exp_nsmul] at *; bound
end

-- part: New.Filling.Moments
section
/-! Second moment of the Poincaré series with constant one. For the normalised Poincaré series P on
columns, the mean over level translates s of the squared Hilbert–Schmidt norm of P*sP is at most
nearly (columns)²/(expected rows), bad types carry little of P, and a variance inequality turns this
into large rank of some translate modulo any subspace of the rows. In rank one, Poisson summation on
a product of two Kloosterman sides with a sharp diagonal term is known. Related work: Herman, Beyond
endoscopy for the Rankin–Selberg L-function, 2011; Iwaniec–Li, The orthogonality of Hecke
eigenvalues, 2007; Michel–Ramakrishnan–Yang, Bessel periods on U(2,1)×U(1,1), 2023.

Phase sums are sharply dominated by local Bessel kernels. In the unfolded second moment of the
Poincaré series, the summed main terms are dominated by the quadratic form of a positive kernel of
local Bessel (orbital) integrals at a finite set of primes, with a constant near 1. With the sieve
this bounds the main term sharply. Literature: Kloosterman sums as local orbital integrals, normal
forms for Bessel double cosets and Siegel's formula are known. Related work: Jacquet–Ye, Germs of
Kloosterman integrals for GL(3), 1999; Y. Liu, Relative trace formulae toward Bessel and
Fourier–Jacobi periods, 2014; Siegel, Über die analytische Theorie der quadratischen Formen, 1935.

Part of: Translates of the columns fill the rows (see New.Filling.FillingTheorem).

Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Trace of a small central projection on the Bessel-subgroup terms is small. Sharp bound
for the second moment over elements fixing vectors with unit minors. Moment bounds for the Poincaré
series and spread of translates modulo any subspace. -/

open Module Classical Complex EuclideanSpace Finset Fint Fintype InnerProductSpace Matrix
  MeasureTheory IntegralPlace Real Matrix.Module

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} [ok :
  S.IsAdmissible] {V} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Let x be a central idempotent of ℂ[𝖦_i] with Re x(1) ≤ b⁻⁸/2. Then Re ∑_s x(s)·ν⁻¹∑_c tr
A_S(c,s⁻¹,c) ≤ b⁻⁴D_c, where A_S sums the amplitudes of terms in the Bessel subgroup. -/
lemma re_trace_besselS_le [WeilData E] {𝔰} (S : Filling E 𝔰) [ok : S.IsAdmissible] {i x} (hx :
  IsCentralProj x) (b : (x.coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) :
  (∑ s, x.coeff s * ∑ y : _ × _, S.amplitudeSum (S.ratMiddle E).besselS y.1
  (Pi.mulSingle i s)⁻¹ y.1 (y.2, y.2) / S.unipCovolume).re ≤ (S.b ^ 4)⁻¹ * S.columnDim := by
  let T := univ.biUnion fun p : Σ i, S.chosenPlaces i ↦ {p.2.1, star p.2.1}
  have : T.StarStable := ⟨by aesop⟩
  have := Fact.mk ((mem_integralOff T).2
    (idem_mul_mem_Ô.1 ((mul_comm ..).subst ((S.inv_gIdele_smul_mem_iff ⟨idem Tᶜ, idem_mem_Ô _⟩).2
    (by simp [reduceAboveG, -reduceAt_eq_zero]; grind [reduceAt_idem, star_idem, coe_star_Ô])))))
  have ⟨P, F, hF⟩ := S.exists_isFillingLevel T
  obtain ⟨G, B, σ, _⟩ := hF.reduction_eq_iff,
    hF.floorZeroForm_le_main_term ⟨_, unitaryLevel_le_unitaryLevel_one, le_rfl⟩ 0
    (by grind [S.pow_chain]), axiomOfChoice (ok.reduction_surjective <| Pi.mulSingle i ·)
  have z g := ENNReal.toReal_pos (unitaryLevel_open_compact.1 (g := g).measure_ne_zero _ (by simp))
    (hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one)
  grw [Level.floorZeroForm, ← setLIntegral_le_lintegral, lintegral_iUnion (fun s ↦
    measurable_const_mul (S.toPlaces T (σ s))⁻¹ (measurableSet_unitaryLevel (g := F.g))) fun s t n ↦
    Set.disjoint_left.2 fun z u ↦ mt (div_mem u.out) (by simp [← G, *]),
    ← setLIntegral_mono' (measurable_const_mul _ measurableSet_unitaryLevel) fun z e ↦ by
    rw [setIntegral_congr_fun measurableSet_unitaryLevel fun y a ↦ (phase_mul_of_mem_unitaryLevel
      (unitaryLevel_one_le_normalizer a (inv_mem e))).symm.trans (by rfl)], sdiff_le,
    SemilocalField.volume_O, hF.inv_two_pow_le_groupMeasure (volume_nonunits_le le_rfl)] at B
  grw [re_le_norm, ← mul_le_mul_iff_right₀ (z 1), ← norm_smul_of_nonneg, ← measureReal_def,
    ← sq_le_sq₀, ← setIntegral_const, ← setIntegral_congr_fun measurableSet_unitaryLevel (f := fun y
    ↦ S.columnDim * ∑ s, x.coeff s * phase F.g (y * S.toPlaces T (σ s) * y⁻¹)) fun y a ↦ ?_,
    integral_const_mul, integral_finsetSum _ fun s _ ↦
    ContinuousOn.integrableOn_compact unitaryLevel_open_compact.2 (by fun_prop)]
  simp [mul_pow]
  grw [norm_sum_le, norm_mul_le, sum_mul_sq_le_sq_mul_sq, (by simpa [by simpa [-Fintype.card_pi]
    using hx.isChar.apply_inv, x.coeff_mul_apply_left, Finsupp.sum_fintype, mul_conj',
    ← ofReal_pow] using (hx.1.eq ▸ b :) :), (by simpa [← sum_mul, ENNReal.toReal_sum, ← le_div_iff₀,
    z, ← two_mul] using (ENNReal.toReal_mono (by simp [ENNReal.mul_ne_top,
    hF.groupMeasure_ne_top unitaryLevel_le_unitaryLevel_one]) B) :)]
  have := (z F.g).ne'; simp [field, Measure.real]
  any_goals positivity
  obtain ⟨k, rfl, o, -⟩ := exists_toPlaces_eq y
  lift k to S.latStabilizer using mem_latStabilizer_iff.2 ⟨o, a⟩
  rw [← (MulAut.conj (S.reduction k i)).sum_comp]; simp [mul_sum]; congr with s
  let l := k * σ s * k⁻¹
  erw [hx.2, show _ * _ = S.toPlaces T l by simp [l], Pi.mulSingle, Function.update_eq_iff
    (g := S.reduction l).2 (by simp_all [l]), phase]
  split_ifs with hs
  · obtain ⟨⟨k, r, o⟩, b, e⟩ := exists_toPlaces_eq hs.choose, hs.choose_spec; rw [← r] at *
    lift k to S.latStabilizer using mem_latStabilizer_iff.2 ⟨o.1, by
      simpa using div_mem (mem_latStabilizer_iff.1 l.2).2 (unitaryLevel_le_unitaryLevel_one e)⟩
    simp [↓hF.psi_simpleRootSum_eq_unipotentChar, o, by simpa [(G ..).2 e] using
      (amplitudeSum_besselU_mul isStable_besselS (u := 1) (one_mem _)
      (o.2.1 b) · 1), amplitudeSum_besselS_one, S.unipCovolume_pos.ne', columnDim]
  have {c} : IsEmpty ↥(_ ∩ S.termsOver c (S.reduction l)⁻¹ c) :=
    ⟨fun ⟨_, a, k, e, f⟩ ↦ have ⟨_, hu, δ, _⟩ := exists_besselU_mul_toBesselH a; hs ?_⟩
  simp [amplitudeSum, tsum_empty]
  let y := c.out⁻¹ * stdEmbFin δ * c.out
  have f : k * (S.inclHFin y)⁻¹ ∈ besselU := by simpa [*, y, termPosition, ratToFin_toBesselH,
    mul_assoc] using hu.termPosition_mem_besselU _
  cases eq_one_of_reduceAt_eq_one le_rfl _ _ ((forall_congr'
    (S.reduction_inclHFin_eq_one_iff (mem_unitaryLevel_of_besselU_mul f (inclHFin_mem_besselH y)
    (unitaryLevel_one.ge (by simpa [latStabilizer] using k.2))).1 (i + 1))).1
    fun _ ↦ by ext a b; cases (besselH_apply_eq_or f (inclHFin_mem_besselH y) a b) <;> simp [*, l,
    reduction_apply_congr k, reduction_apply_congr 1, -Matrix.one_apply])
  exact ⟨_, (by simpa [y] using f : k⁻¹.1 ∈ besselU).map_mem_unitriangularOn _,
    (G k⁻¹ _).1 (by simp [*])⟩

/-- Main-term estimate: under the standing hypotheses, for every set Σ of chosen places
above q₀, the `Filling.energy` of all terms over `Filling.fixingSet` Σ is
at most (1 − b⁻⁴)(1 + 9b⁻⁴)·𝖽·b^{−6k|Σ|}, where k = |κ|. -/
lemma energy_fixingSet_le [WeilData E] {𝔰} {S : Filling E 𝔰} [S.IsAdmissible] Sg D :
  energy (S.amplitudeSum .univ) (fixingSet Sg D) ≤ (1 - (S.b ^ 4)⁻¹) *
  ((1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #Sg) := S.of_size_bounds (by
  intros; set y : ℝ := _ ^ #Sg
  obtain ⟨⟨x, u, e⟩, a, c⟩ := exists_nonneg_add_of_le S.thousand_le_b, S.ϱ_le_k,
    S.card_chosenPlaces 0 ▸ Sg.card_le_univ
  have hy : S.tailScale ^ 20 * S.besselEnergy ≤ y * S.mainEnergy := by
    grw [← IsAdmissible.besselEnergy_le]; simp [y, field]; grw [c, pow_mul _ 4 6,
      tailScale_pow_four]; ring_nf; rfl; bound
  grw [energy_le_of_linkEnergy_le _ (by tauto) (by tauto) (by simp) (fun s k ↦ ⟨Sg.image
    fun w ↦ (⟨0, w⟩, (D w).1), (prod_image (by simp)).ge, forall_mem_image.2 (⟨_, k.1 · ·⟩)⟩)
    (w := (1 + (S.b ^ 4)⁻¹) * y * S.mainEnergy) _ (by grw [← hy, ← ‹2 ≤ S.tailScale›]; bound)
    {_Λ | Sg ≠ univ} (by
    simp; intro; grw [← le_levelPrime, pow_mul _ 4 3, tailScale_pow_four]; simp [y, field,
      S.card_chosenPlaces, *]
    ring_nf; gcongr; lia), ← e, ← sub_nonneg]; field_simp; ring_nf; any_goals positivity
  simp_rw [linkEnergy, Set.univ_inter, ← ENNReal.tsum_prod]
  refine (tsum_subtype_support _).ge.trans (ENNReal.summable.tsum_le_of_sum_le fun F ↦ ?_)
  choose t σ n ht L H H' using fun j : F ↦ S.exists_hasSum_cosetAmplitude (j.1.2 ∘ sq_eq_zero_iff.2
    ∘ enorm_eq_zero.2) fun _ ⟨k, r, f⟩ l e ↦ j.1.1.2.2.1.2.2.elim j.1.1.2.2.2.2 fun ⟨w, z⟩ ↦ z l (by
    erw [← r, leadingMinor, submatrix_submatrix, ← map_splitGram_latMiddle (reduceAt _),
      ← Matrix.map_mul, submatrix_map,
      ← RingHom.map_det, Subtype.ext (((Ô E).subtype.map_det _).trans _), map_zero]
    erw [RingHom.mapMatrix_apply, ← submatrix_map, Matrix.map_mul, map_splitGram_latMiddle,
      ← submatrix_submatrix, ← frameGram, congr(frameGram _ ($f).1.1), frameGram_termPosition,
      submatrix_map, ← RingHom.map_det]; simpa)
  simp (disch := bound) only [← ofReal_norm, ← ENNReal.ofReal_pow, ← F.sum_coe_sort,
    ← ENNReal.ofReal_sum_of_nonneg]; gcongr; cases' hk : 𝔰.k with k; omega
  let r := (∏ v, √𝔰.openCellConst * ∏ a : Fin 𝔰.n,
    S.frameScaleSq v a ^ (k + 2 * a.rev)) / Fintype.card S.BesselCoord
  have c0 := 𝔰.openCellConst_pos; choose τ hτ using (Real.range_exp.ge <| S.frameScaleSq_pos · ·)
  refine le_of_tendsto_of_frequently (tendsto_finsetSum _ fun j _ ↦ (H j).norm.pow 2)
    (Filter.frequently_atTop.2 fun A ↦ let T₀ := A.biUnion univ.image ∪ univ.image t
    ⟨univ.map (.arrowCongrRight (.subtype (· ∈ T₀))), fun p h ↦ mem_map.2 ⟨(⟨p ·, by grind⟩),
    by simp, rfl⟩, le_of_mul_le_mul_left (a := r ^ 2) ?_ (by simp [r, ← hτ]; positivity)⟩)
  apply le_of_tendsto_of_frequently ((tendsto_finsetSum _ fun j _ ↦ (tendsto_finsetSum _ fun p _ ↦
    H' j p).norm.pow 2).const_mul _) ((S.exists_places_integralOff T₀).mp (.mono _ _)); rotate_right
  rintro T (o : ∀ i j, _ ∧ _) ⟨_, h₀, g, hT⟩; obtain ⟨P, G, hG⟩ := S.exists_isFillingLevel T
  obtain ⟨Y, hm, K⟩ := hG.exists_finite_sieveSystem Sg D
  apply ((Filter.Eventually.all fun i ↦ hG.sum_blocks_le_topKernel hT (j := {j // t j = t i}) _ (ht
    · |>.1) (fun j ↦ (ht j).2.1.trans congr($(j.2))) (ht i).2.2.1 (fun j ↦ hm (n j) (by simp [ht]))
    (o i · |>.1) ⟨i, rfl⟩ («π» := .cut) _ _ (o i · |>.2)
    ).exists_mem_basis_of_smallSets Metric.nhds_basis_closedBall).elim
  rintro ε ⟨p, M⟩; let V := IsUltrametricDist.closedBall_openAddSubgroup (LocProd T) p
  apply ((mul_le_mul_of_nonneg_left (S.sieve T h₀ g.1 (K V (isCompact_closedBall ..))
    le_sup_right) _).trans _).trans'
  · rw [mul_sum, ← sum_fiberwise_of_maps_to fun i ↦ mem_image_of_mem t, re_sum, mul_sum]
    use sum_le_sum (forall_mem_image.2 fun i _ ↦ by
      simpa only [← sum_subtype_eq_sum_filter, ht, subtype_univ, Subtype.prop (p := (t · = _)),
        sum_map, Nat.not_succ_le_self] using! M i ⟨V.2, isCompact_closedBall .., zero_mem V⟩)
  · unfold packetConst siegelConst; positivity
  · obtain D := ‹0 ≤ S.mainEnergy›, S.besselDegree_pos, volÔ_ne_zero (E := E)
    simp [prod_range]
    grw [← besselDegree, prod_comm, IsAdmissible.packetConst_mul_mass_le, ← sq_sqrt c0.le,
      (?_ : (1 + _) ^ _ ≤ 1 + S.b⁻¹ ^ 9), ← c]
    simp only [y, frameScaleProd, hk, pow_add, prod_mul_distrib, prod_pow, fieldLe, ← e, inv_pow,
      ← hτ, card_univ, prod_const, Fin.val_rev, Nat.succ_sub_succ, pow_mul]
    clear * - u D; rw [← sub_nonneg]; ring_nf; positivity
    grw [add_comm, add_one_le_exp, ← Real.exp_nat_mul, S.f_le_b, Real.exp_bound' _ _ one_pos] <;>
      simp [field] <;> bound
  intro i j l e; ext <;> simp only [ht, by simpa [ht] using e]; swap
  · -- the correlation integrals of the product vector are the products of the local ones
    intro i j; ext
    rw [Finset.prod_congr rfl fun v _ ↦
      (S.besselSys v).band_limits.2 _ ((ht j).1.ratToInf_mem_unitriangularOn v) _ _ ?_ ?_]
    simp_rw [normCorrelation, gram_apply, inner_smul_left_eq_smul, inner_smul_right_eq_smul,
      real_smul]
    simp only [inner, besselFn, besselCorrelation, Pi.mul_apply, Pi.inv_apply, star_def,
      prod_univ_sum, ratToInf_weylElem_mul, prod_mul_distrib, ← map_prod, sum_prod_type,
      ← integral_fintype_prod_volume_eq_prod, ← ofReal_prod]; rfl'
    repeat simp [ht, frameScaleSq, padTuple, unitOrOne, j.2]
  · intro i p
    simp [frameScaleSq.eq_1 S _ 𝔰.ϱ, div_pow, div_mul_eq_mul_div, div_sub_one, -one_div, hk,
      mul_add, unitOrOne, ↓Fin.prod_univ_castSucc, mul_pow, abs_of_pos, pow_add, Fin.rev_castSucc,
      padTuple, prod_pow, prod_range, (S.frameScaleSq_pos ..).ne', Level.headDensity,
      P.md_evalPlaces_rpow_half (h₀ _ (p _).2), @prod_comm (Fin 𝔰.ϱ), prod_eq_zero_iff, field]
    simp [sqrt_eq_rpow, rpow_pow_comm, finsetProd_rpow, ((ht i).2.2.1 _).le, prod_nonneg]
  simp [↓Filter.eventually_all, eventually_isIntegralOff, -Filter.eventually_atTop])

attribute [-simp] mul_re univ_unique Fintype.card_pi

/-- Second moment bound: under `Filling.IsAdmissible`, for i = 0, 1, the energy `Filling.energy` of
the terms outside the Bessel subgroup S(E⁺), over the s whose i-th component is that of an element
of the image S̄ of S, is at most b⁻¹²d₁, d₁ = |S̄|·D_c, D_c = `Filling.columnDim`. -/
lemma energy_compl_besselS_le [StablyUnram E] i :
    energy (S.amplitudeSum (S.ratMiddle E).besselSᶜ) {s | ∃ t ∈ S.reducedImage besselS, s i = t i} ≤
  (S.b ^ 12)⁻¹ * S.besselEnergy := S.of_size_bounds (by
  intros; obtain _ := S.ϱ_le_k, @besselFrame_castSucc 𝔰 ⟨0, pos_of_gt S.ϱ_le⟩
  grw [energy_le_of_linkEnergy_le (by bound) (by grind [IsStable, S.isStable_besselS]) ?_ (by simp)
    (fun s h ↦ ⟨image (.map (.mk i) id) ⊤, (prod_image (by intro; grind)).ge,
    forall_mem_image.2 fun p _ ↦ ⟨⟨Pi.single (0 : Fin (𝔰.ϱ + 1)) 1, by simp⟩,
    .symm ?_⟩⟩) le_rfl le_rfl ∅ (by
    simp [S.card_chosenPlaces]; grw [← ok.mainEnergy_le, codimFactor, g_le_b_pow, ← le_levelPrime]
    simp [div_pow, field, pow_mul _ 4 2, tailScale_pow_four]; ring_nf; bound)
    (by simp [linkEnergy])]; simp
  · rintro ⟨γ, n, c, c', _, ⟨_, ⟨t, ht, rfl⟩, hs⟩, ⟨k, rfl, hk⟩, ζ, hζ, h⟩
    choose X Y e h using (h · bot_le)
    have h3 : (1⁻¹ * stdEmbFin (U.of isUnit_one (scalar Unit ζ) (by simp [mul_comm, hζ])) *
        1).1 () () = k.1.1 (𝔰.besselFrame 0) (𝔰.besselFrame 0) := by
      obtain _ := congrFun (e 0) (𝔰.besselFrame 0),
        congrFun₂ (hk ▸ frameImage_termPosition) (𝔰.besselFrame 0) 0
      simp_all [classCoord_eq_fromBlocks, mul_apply, U.of, mulVec_eq_sum, Fin.sum_univ_succ]
    have := S.eq_one_of_reduceAt_eq_one (by simp; omega) _ (mem_Kf.2 fun _ _ ↦
      h3 ▸ k.2.isIntMatrix _ _) fun w ↦ by
      ext; convert hs ▸ reduction_apply_congr 1 i w
        (mem_besselS_iff_frameImage.1 ht (𝔰.besselFrame 0) 0 bot_le)
      use congr(reduceAt _ ⟨$h3, _⟩); simp
    cases (by simpa [U.of] using congr($this.1 () ()) : ζ = 1)
    cases n (mem_besselS_iff_frameImage.2 fun j ↦
      wellFounded_lt.fix fun b ↦ by clear * - e h; grind [congrFun
      (e b) j, mulVec_apply_eq_sum, Fintype.sum_eq_single b, Matrix.one_apply, submatrix_apply])
  obtain ⟨_, ⟨k, hk, rfl⟩, h⟩ := h; have := (mem_besselS_iff_frameImage.1 hk · 0)
  simp [h, ← intGL_map_reduceAboveG, Units.smul_def]; simp_all [funext_iff, mulVec_eq_sum,
    inclMatrix, -Sum.forall, ite_eq_iff', ← Submonoid.one_def, ← ZeroMemClass.zero_def])

/-- Let Θ ≥ 0 on 𝖦 have positive type, sum over each Ω at most the `Filling.energy` of all
terms over Ω, and vanish unless s
fixes given nonzero frame vectors modulo w or w̄ for all w ∈ A (chosen places above q₀). Then
∑Θ ≤ (1 + 9b⁻⁴)·𝖽·b^(−6|κ||A|).

Second moment of the Poincaré series with constant one. -/
lemma sum_le_of_positive_type [WeilData E] {Θ : _ → ℝ} (h0 : ∀ s, 0 ≤ Θ s) (u : _ → V) (hu :
  ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) A (D : ∀ _, _) (hB : ∀ Ω, ∑ s with s ∈ Ω, Θ s ≤ energy
  (S.amplitudeSum .univ) Ω) (hA : ∀ s, Θ s ≠ 0 → ∀ w ∈ A, s ∈ S.vectorFixer (i := 0) w (D w)) :
  ∑ s, Θ s ≤ (1 + 9 / S.b ^ 4) * S.mainEnergy * (S.b ^ (6 * 𝔰.k))⁻¹ ^ #A := by
  induction' A using WellFoundedGT.induction with A ih generalizing V Θ D
  obtain ⟨hq, q, _⟩ := S.levelPrime_le 0, S.le_levelPrime 0, S.thousand_le_b, univ.sum_nonneg' h0,
    S.ϱ_le_k; by_contra! hK
  apply hK.not_ge
    (le_of_mul_le_mul_left (.trans _ (energy_fixingSet_le A D)) (by bound [@one_lt_pow₀ ℝ]))
  grw [← hB, one_sub_mul, sub_le_comm, ← sum_sdiff_eq_sub (by simp), ← sum_filter_ne_zero]
  obtain hw | ⟨w, hw⟩ := em' (Exists (· ∉ A))
  · rw [Finset.sum_eq_zero (by simp; grind [fixingSet])]; bound
  choose! L hL using fun s (e : s ∉ S.fixingSet A D) h ↦ by simpa using (e ⟨hA s h, .inr ⟨w, ·⟩⟩)
  grw [← Finset.sum_fiberwise _ L, sum_le_card_nsmul _ _ (3 * univ.sum Θ / S.b ^ 10)
    fun l _ ↦ let F b := frameImage (cond b (S.latMiddle (ResField w.1)).splitGram 1) *
      inclMatrix (ResField w.1) (Fin.castLE l.is_le)
    (le_div_iff₀' (by bound)).2 (.trans ?_ ((card_mul_sum_det_le (.mk' (· 0 w) (by simp)) F h0 hu
    (univ.sum Θ / S.b ^ (6 * 𝔰.k)) (by bound) fun b v hv ↦ by
    grw [sum_filter, ih _ (ssubset_insert hw) _ (fun a ↦
      basisFun _ ℂ (cond b invTransposeGL 1 (a 0 w) • F b *ᵥ v) ⊗ₜ[ℂ] u a) _
      (Function.update D w ⟨b, _, (map_ne_zero_iff _ (inclMatrix_mulVecLin_injective (Fin.castLEEmb
      l.is_le) _)).2 hv⟩) (.trans (by gcongr; bound) <| hB ·), ← hK] <;> simp
      [*, apply_ite ofReal, ite_nonneg, pow_succ, field, inner, smul_smul, ← eq_inv_smul_iff]
    · exact fun s h _ ↦ ⟨by cases b <;> simp [vectorFixer] <;> (repeat erw [mul_smul]) <;>
        simpa [F, ← mul_inclMatrix, ← mulVec_mulVec, inv_smul_eq_iff] using! h.symm, by grind⟩
    tauto).trans ?_))]
  · simp [field]; grw [← le_self_pow₀, ← k_le_b, ← S.ϱ_le_k] <;> push_cast <;> nlinarith
  · gcongr <;> simp [*, sum_nonneg', subset_iff, F, transpose_splitGram, mul_inclMatrix,
      ← inclMatrix.eq_1, card_eq_nat_card, ↓card_resField_eq_levelPrime]; bound
  grw [mul_div_left_comm, div_le_one_of_le₀]; linarith
  grw [← sq_le_sq₀, mul_pow, sq_sqrt, card_eq_nat_card, card_resField_eq_levelPrime, hq, hq]
  simp [← pow_mul, ← pow_add]; repeat bound [l.2]

/-- Under `Filling.IsAdmissible`, let x be a central idempotent of ℂ[𝖦_i]. The ℓ² norms of the rows
of the block matrix (∑_t x(t)ν⁻¹A_T(c, t⁻¹, c')), T the complement of 𝖲(E⁺), sum to at most
b⁻⁴D_c, D_c = `Filling.columnDim`. -/
lemma sum_norm_amplitudeSum_le [StablyUnram E] i {x} (hx : IsCentralProj x) : ∑ a :
  _ × _, ‖WithLp.toLp 2 fun b : _ × _ ↦ ∑ t, x.coeff t * (S.amplitudeSum (S.ratMiddle E).besselSᶜ
  a.1 (Pi.mulSingle i t)⁻¹ b.1 (a.2, b.2) / S.unipCovolume)‖ ≤ (S.b ^ 4)⁻¹ * S.columnDim := by
  let φ : _ →* S.GRes := .mulSingle _ i; have := S.thousand_le_b
  let Y s := ∑ c, ∑ c', ‖∑ t,
    x.coeff t • S.amplitudeSum (S.ratMiddle E).besselSᶜ c ((φ t)⁻¹ * s) c'‖ ^ 2 / S.unipCovolume ^ 2
  have h := ((card_nsmul_le_sum {s | s ∈ S.reducedImage besselS} Y (Y 1) fun σ
    h ↦ ?_).trans ?_).trans (S.energy_compl_besselS_le (i + 1))
  · simp [besselEnergy, ← card_subtype, field] at h
    grw [← sq_le_sq₀, sq_sum_le_card_mul_sum_sq, show ∑ _, _ = Y 1 by simp [Y, φ, norm_sq_eq,
      sum_prod_type, ← sum_div, div_pow, mul_div, @sum_comm S.Classes _ S.BesselCoord],
      (le_div_iff₀ _).2 h] <;> simp [columnDim, field, sum_nonneg'] <;> bound
  choose p σ₀ h₀ h₁ using (exists_besselS_mem_termsOver · (mem_filter.1 h).2)
  apply congr(∑ c, $(sum_bijective p (Finite.injective_iff_bijective.1 fun c d h ↦
    (eq_and_mem_classUnip_of_besselS (by aesop)
    (mul_inv_cancel σ ▸ termsOver.mul (h₁ c) (.inv (h ▸ h₁ d)))).1) _ _ fun d ↦ .symm ?_)).le
  obtain ⟨u, hu, η, hη, e⟩ := mem_besselS.1 (h₀ d)
  choose k hk using fun v ↦ exists_toBesselH_eq (hη.ratToInf_mem_unitriangularOn v)
  let A v := (S.besselSys v).rep (k v); let := @instDecidableEqProd
  rw [← Unitary.norm_map ⟨_, Unitary.map_mem (toEuclideanCLM (𝕜 := ℂ)) (kronecker_mem_unitary
    (one_mem _) (UnitaryGroup.map_star ⟨(S.unipotentChar (S.ratToFin u))⁻¹ • kroneckerPi (A ·), by
    erw [mem_unitaryGroup_iff, star_smul, smul_mul_smul, ← kroneckerPi_one, ← funext (A · |>.2.2),
      kroneckerPi_mul, mul_conj', norm_inv, norm_selfDualChar]
    ext; simp [mul_apply, kroneckerPi]⟩).2)⟩, map_sum]
  congr! 4; rw [map_smul, ← amplitudeSum_move (by grind [IsStable, S.isStable_besselS]) _
    (S.classUnip _).one_mem.2 _ (h₁ _)] <;> simp [h₀, mul_mem_cancel_right]
  intros; ext; simp [e, besselKernel, mul_assoc, besselFn_ratToInf_mul hu, mulVec_apply_eq_sum,
    sum_prod_type]
  simp [besselFn, hk, ((besselSys ..).tail.isBesselFunction _).3, kroneckerPi, ↓mulVec_eq_sum,
    Fintype.prod_sum, mul_sum]; ac_rfl
  simp_rw [Y, energy, ← @sum_comm S.GRes, ← sum_div]; gcongr
  refine .trans ?_ (by simpa [apply_ite, sum_ite] using
    hx.sum_norm_conv_le φ fun s ↦ ite (∃ t, _) (S.amplitudeSum ..) 0)
  grw [← subset_univ]
  congr!; aesop

/-- Filling: let ρ be unitary, ⟨ρ(s)Qe_y, Qe_x⟩ = c·(amplitude sums), c > 0, R = ρ(∏g_i) for
central idempotents with Re(1−g_i)(1) ≤ b⁻⁸/2, rank R ≤ |𝖦|·deg·mass. Each subspace F of im
R, of share φ, has an s with dim (Rρ(s)Q)⁻¹F ≤ ½(1 + φ + 19b⁻⁴)D_c. -/
lemma Fits.exists_translate_finrank_comap_le [WeilData E] {g c} [Module.Finite ℂ V] {ρ :
  Representation ℂ _ V} (hρ : ∀ s x y, ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) {Q :
  EuclideanSpace ℂ (_ × _) →ₗ[ℂ] V} (hQ : ∀ s x y, ⟪ρ s (Q (.single y 1)), Q (.single x 1)⟫_ℂ =
  ofReal c * S.amplitudeSum .univ x.1 s y.1 (x.2, y.2)) (hg : ∀ i, IsCentralProj (g i)) (hb : ∀ i,
  ((1 - g i).coeff 1).re ≤ (S.b ^ 8)⁻¹ / 2) (hc : 0 < c) (hD : finrank ℂ (ρ.asAlgebraHom
  (piTensorElem g)).range ≤ Nat.card S.GRes * S.besselDegree * mass E 𝔰.r) : IsSpread
  ((ρ.asAlgebraHom (piTensorElem g)).rangeRestrict ∘ₗ ρ · ∘ₗ Q) (19 / 2 * (S.b ^ 4)⁻¹) := by
  set R := ρ.asAlgebraHom (piTensorElem g); intro F φ; apply S.of_size_bounds; intros
  obtain ⟨⟨t, ht⟩, G, B, o⟩ := (isSquare_iff.2 (mul_pos hc S.unipCovolume_pos).le).inv,
    IsCentralProj.piTensorElem hg, S.amplitudeSum_split .univ (S.ratMiddle E).besselSᶜ,
    (hg · |>.one_sub); let P := t • Q
  have hu a b x y : ⟪ρ b (P (.single y 1)), ρ a (P (.single x 1))⟫_ℂ =
      S.amplitudeSum .univ x.1 (a⁻¹ * b) y.1 (x.2, y.2) / S.unipCovolume := hρ a⁻¹ .. ▸ by
    simp [← End.mul_apply, ← map_mul, P, ← mul_assoc, ← ofReal_mul, ← ht, hQ, field, hc.ne']
  have pr {z} (hz : IsCentralProj z) y : ⟪_, _⟫_ℂ = _ :=
    (hz.self_adjoint ρ 1 (innerₛₗ ℂ) hρ y _).trans congr(⟪y, $(hz.1.map ρ.asAlgebraHom) y⟫_ℂ)
  have hb' i := add_le_add (S.re_trace_besselS_le (o i) (hb i)) ((sum_norm_amplitudeSum_le i
    (o i)).trans' (sum_le_sum fun a _ ↦ (PiLp.norm_apply_le _ a).trans' (re_le_norm _)))
  refine (exists_le_of_sum_le univ_nonempty (g := fun _ ↦ S.columnDim / 2 * (1 + 9 * (S.b ^ 4)⁻¹ +
    φ)) ((sum_le_sum fun s _ ↦ finrank_sub_le_re_inner_dyadSum (stdOrthonormalBasis ..) (ρ s ∘ₗ P)
    (ρ.asAlgebraHom (1 - piTensorElem g)) (F.comap (R.rangeRestrict ∘ₗ ρ s ∘ₗ Q)) (F.map
    R.range.subtype) (Eq.trans_le ?_ (S.sum_norm_amplitudeSum_le 0 (.one_sub ⟨.zero, by simp⟩)))
    fun _ ↦ (⟨_, F.smul_mem t ·, by simp [P, R]⟩)).trans ?_)).imp fun s h ↦ ?_
  · congr! 2; ext; rw [← basisFun_inner]
    simp [inner_sub_right, LinearMap.adjoint_inner_right, inner_single_left, hu,
      amplitudeSum_besselS_one, ite_div, add_div, B, apply_ite, S.unipCovolume_pos.ne',
      Finsupp.single_apply, MonoidAlgebra.one_def]; grind
  · grw [← re_sum, ← sum_inner, re_le_norm, norm_inner_le_norm, ← sq_le_sq₀, mul_pow,
      @norm_sq_eq_re_inner ℂ, inner_sum_sum_eq_card_mul (energy (S.amplitudeSum .univ) {·}) ?H]
    simp [@norm_sq_eq_re_inner ℂ, ↓inner_dyadSum, apply_ite, ← Submodule.coe_inner, mul_pow,
      ← show φ *
      _ = _ from div_mul_cancel_of_imp (mod_cast by bound [F.finrank_le]), orthonormal_iff_ite.1]
    grw [sum_le_of_positive_type (fun _ ↦ by unfold energy; positivity) _ ?H ∅ (fun _ ↦
      ⟨⊤, 1, by simp⟩) _ nofun, hD, ← four_mul_le_sq_add]
    simp [mainEnergy]; field_simp [mass_pos, besselDegree_pos, ne_of_gt]; any_goals positivity
    repeat norm_num [energy, sum_filter, norm_sq_eq, sum_prod_type, sum_div, hu, div_pow,
      @sum_comm S.Classes _ S.BesselCoord, @sum_comm S.GRes]
  have k := univ.sum_nonneg' fun y ↦ pr (.piTensorElem o) (P (.single y 1)) ▸ inner_self_nonneg
  simp [add_div, show piTensorElem (1 - g ·) = ∑ i,
    piTensorElem (Pi.mulSingle i (1 - g i)) - (1 - piTensorElem g) by
    ext; simp [← map_one piTensorElem, -map_one]; ring, ↓@norm_sq_eq_re_inner ℂ, ↓hρ, columnDim,
    ↓pr G.one_sub, mul_add, mul_sum, @sum_comm (_ × _), asAlgebraHom_piTensorElem_mulSingle, B, (by
    simpa using congr(ρ.asAlgebraHom $(G.2.commute (.single s 1)) ·).symm),
    asAlgebraHom_eq_sum (ρ.comp _), by simpa using (hu · 1)] at *
  linarith
end Filling
end
