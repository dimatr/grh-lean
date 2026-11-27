import Lib.PadicHodge.HodgeTateProjectors

-- part: Lib.PadicHodge.Limit.LocalLimit
section
/-! Limits of crystalline representations with bounded weights are crystalline. The hypothesis here
is a uniform limit of traces with unbounded coefficients and ranks, and crystallinity is Liu's
theorem for the image of the group ring. Limit formulas for weight multiplicities and killing
polynomials are also proved. Source: T. Liu, Torsion p-adic Galois representations and a conjecture
of Fontaine, Ann. Sci. ENS 40 (2007) 633–674; L. Berger, Limites de représentations cristallines,
Compositio Math. 140 (2004) 1473–1498; for the passage from traces to the image of the group ring P.
Wake, C. Wang-Erickson, Deformation conditions for pseudorepresentations, Forum Math. Sigma 7
(2019).

This file: Uniform limits of traces keep crystallinity, Hodge-Tate weights and killing
polynomials. -/

attribute [-simp] map_eq_zero isUnit_map_iff
open Matrix Polynomial MonoidAlgebra Finset Module Metric IsUltrametricDist Submodule Set
  hodgeTateMaps TensorProduct Function LinearMap Amax Classical Filter

/-- Let tr r (r continuous, with `IsTraceNondeg`) be a uniform limit of combinations of traces of
continuous representations unramified or crystalline at A, finitely many in all or all with jumps J.
So is r; jump multiplicities and, under coefficientwise uniform convergence, killing polynomials of
bounded degree pass to r.

Known result: Limits of crystalline representations with bounded weights are crystalline. -/
lemma local_clauses_of_trace_limit {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E m I : Type} [Field E]
  [EmbeddedNumberField E] [Fintype m] {r : GalRep ℓ E m} {A} (hr : Continuous r) (hn : IsTraceNondeg
  r) R {R' J} {ι : I → Type} [∀ η, Fintype (ι η)] F [NeBot F] (a J' : ∀ _ _, _) (ρ : ∀ η, ι η →
  PadicRep _ ℓ) (hc : ∀ η i, Continuous (ρ η i).rep) (hU : ∀ η i, IsGoodAt (ρ η i).rep A) (hJ :
  ∀ η i, JumpsRelAt (ρ η i).rep A R' (J' η i)) (hS : Finite I ∨ ∀ η i, HasJumpsAt (ρ η i).rep A J)
  (T : TendstoUniformly (fun η g ↦ ∑ i, a η i * ((ρ η i).rep g).1.trace) (r · |>.1.trace) F) (h' :
  ∀ τ u (x : ∀ _ _, ℕ) (n : ℕ), (∀ η i, R' ((J' η i τ).count u) (x η i)) → F.Tendsto (fun η ↦ ∑ i,
  a η i * x η i) (nhds n) → R ((J τ).count u) n) : IsGoodAt r A ∧ JumpsRelAt r A R J ∧
  ∀ ⦃s N P⦄ ⦃Q : ∀ _ _, _⦄, natDegree P < N → (∀ η i, natDegree (Q η i) < N ∧ PolyKillsAt
  (ρ η i).rep A s (Q η i)) → (∀ l, TendstoUniformly (fun η g ↦ ∑ i, a η i * (Q η i).coeff l *
  ((ρ η i).rep g).1.trace) (fun g ↦ P.coeff l * (r g).1.trace) F) → PolyKillsAt r A s P := by
  let W b c := TendstoUniformly (fun η g ↦ ∑ x, (a * c) η x * ((ρ η x).rep g).1.trace)
    ((b * ·.1.trace) ∘ r) F
  obtain ⟨⟨t₀⟩, T : W 1 1⟩ := F.nonempty_of_neBot, by simpa [W]
  have B {b c} (H : W b c) η hη := (tendstoUniformly_iff.1 H η hη).mono fun n h y ↦ show
    b * (groupRingHom ⟨r⟩ y).trace - ∑ x, (a * c) n x * (groupRingHom _ y).trace ∈ ball 0 η by
    simpa [lift_apply, Finsupp.sum, mul_sum, univ.sum_comm, smul_sub, smul_sum, -mem_ball] using!
      sum_mem (S := ball_openAddSubgroup _ hη) fun g _ ↦ balanced_ball_zero.smul_mem
      (y.coeff g).2 (mem_ball_zero_iff.2 (mem_ball_iff_norm.1 (h g)))
  -- a linear relation that holds in all `ρ θ x` holds in `r`
  have Z S {b c : ℕ → _} (H : ∀ {l}, W (b l) (c l)) (y : ∀ _ _, _) (h : ∀ θ x, ∑ l ∈ S, c l θ x •
      groupRingHom (ρ θ x) _ = 0) {M} (e : ∀ θ, M = ∑ l ∈ S, b l • groupRingHom ⟨r⟩ (y θ l)) :
    M = 0 := hn _ (by simp (maxDischargeDepth := 9) [e t₀, lift_apply, Finsupp.sum, sum_mem,
    smul_of_tower_mem, mem_span_of_mem]) fun g ↦ (tendsto_const_nhds_iff.1 ((tendsto_finsetSum S
    fun l _ ↦ tendsto_nhds.2 (B (@H l) · · |>.mono fun θ h ↦ h (y θ l * .single g 1))).congr
    fun θ ↦ by simpa [e θ, sum_mul, mul_sum, mul_assoc, S.sum_comm] using
    congr(∑ x, _ * ($(h θ x) * ((ρ θ x).rep g).1).trace))).trans sum_const_zero
  obtain ⟨p, g, hg⟩ := @PadicInt.maximalIdeal_eq_span_p ℓ, skolem.1 exists_gp_eq_algHom
  let Δ := decompGroup Gal(Ω/E) A
  let X η := Option.elim' ⟨r⟩ (ρ η)
  refine ⟨⟨fun l s b ↦ by simpa using (Z {0} T (fun _ _ ↦ .single s 1 - 1) (by simp
    [(hU ..).1, *]) fun _ ↦ rfl), @fun l ↦ ?_⟩, fun l γ _ b w ↦ h' _ w _ _ (hJ · · b w) ?_, fun s n
    P Q hP h O ↦ ⟨fun l ↦ Z (range n) @O (fun _ ↦ (.single s 1 ^ ·)) (by simp [(h ..).2.1, *,
    ← aeval_eq_sum_range']) (by simp [aeval_eq_sum_range' hP]), @fun l m k w ↦ ?_⟩⟩ <;> (
    choose L q u _ _ hs hu _ U using fun η ↦ exists_finite_groupRing_quotient Δ (τ :=
      X η) (·.rec hr (hc η))
    have b η : ∀ᶠ k in cofinite, ∀ o γ, jump (decompRep (X η o).rep A) γ k = 0 := exists_jump_bound
      (ρ := actionRep _ (L η) (.domRestrict ((lift _ _ _).symm (q η)) _)).rec fun _ h ↦ (finite_Icc
      ..).subset (h · ∘ mt fun e o γ ↦ jump_eq_zero_iff.2 fun f a ↦ f.ext fun v ↦ (congrArg f (by
      simp [asSemilinear])).trans congr($(jump_eq_zero_iff.1 e _
      (pull (asSemilinear (applyVec (u _ o)) (v, γ)) (by simp [hu, asSemilinear]) ⟨_, a⟩).2) 1))
    have ⟨d, hd⟩ := ((hS.elim (fun _ ↦ .all b) fun H ↦ ((b t₀).and (∑ τ, J
      τ).finite_toSet.compl_mem_cofinite).mono fun k h η ↦ (·.rec (h.1 none) fun x γ ↦ by
      simp at h; erw [← H η x (hg γ)]; simp [*])).image Int.natAbs).bddAbove
    let α := singleHom.comp (((Units.coeHom _).comp (χ⁻¹ ^ d)).prod Δ.subtype)
    have ew {σ} g x : viaGroupRing α σ g x =
      (χ g ^ (-d : ℤ)).1 • decompRep σ.rep A g x := by simp [α]
    have K η o c : IsCrystalline .. ∧ IsCrystallineUpTo (2 * d) (viaGroupRing α (X η o)) := ⟨c,
      c.tate_twist _ ew, fun γ u h ↦ by have := hd ⟨u -
      d, by simp [← jump_twist_cyclotomicGp _ ew]; tauto, rfl⟩; omega⟩
    choose C H using fun θ o ↦ K θ o (o.rec (.tate_twist (isCrystalline_of_trace_limit α hr hn (X :=
      ρ) (K · · (hU ..).2 |>.2) hc (B T · · |>.exists.imp fun _ b y z ↦
      le_of_lt (by simpa [z] using! b y))) d (by simp [α, smul_smul, ← mul_pow])) (hU θ · |>.2)))
  use C t₀ none
  have N {x} : ‖γ x‖ = ‖x‖ := by simp [*, ← smul_coe_Cp]
  choose t z hz S using (exists_uniform_trace_sum_eq_jump _ _ (w - -d)).imp fun t S θ ↦
    S (finBasis ..) 1 (U θ (H θ))
  choose y hy using (hs · <| finBasis ℤ_[ℓ] _ ·)
  refine tendsto_nhds.2 fun ε e ↦ (exists_pos_mul_lt e ‖t‖).elim fun δ ⟨e, k⟩ ↦ (B T δ e).mono fun θ
    h ↦ k.trans_le' (.trans_eq' (norm_mul_le_of_le le_rfl (norm_tsum_le_of_forall_le_of_nonneg e.le
    fun s ↦ (norm_mul_le_of_le (hz θ s) N.le).trans (by simpa using (h (y θ s)).le))) ?_)
  have S o := S θ γ ⟨.toHomUnits _⟩ (u θ o) (by simp [hu]) (by simp) (H θ o).1.isPotCrys
  simpa [← hy, hu, mul_sub, mul_sum, sum_comm (γ := ι _), mul_left_comm (γ _), dist_eq_norm', ← N,
    ↓jump_twist_cyclotomicGp _ ew] using! congr(‖$(S none) - ∑ x, γ (a θ x) * $(S x)‖)
  -- the powers of a Weil element have bounded denominators; linear forms on `Amax` read them
  obtain ⟨⟨δ, D, S⟩, ⟨c⟩⟩ := Lift.uniform_period_bound Δ _, p ▸ nonempty_adicBasis _ p
  choose Y V using fun θ N ↦ span_le (p := (periodTensorMap _ _ id).range.comap (.restrictScalars _
    _ ∘ₗ periodTensorMap _ _ id)).2 (fun y a ↦ ⟨_,
    .symm ((linearFrob_apply (U θ (H θ)).1.isPotCrys (w.pow N) (fixedPeriods.map (by simp)
    ((nearOne _).univ_mem' a))).trans (tensorAction_periodTensorMap (fun _ ↦ id_apply _) ..))⟩)
    (nsmul_mem ((S (finBasis ..) (U θ (H θ))).1 1) ((ℓ ^ (k * d)) ^ (n - N)))
  choose G hG using (Y · · |>.exists_finset)
  choose M V E using fun θ o {Q} (h : natDegree Q < n) v ↦ show ∃ M, periodTensorMap _ _ id M = (δ •
    (ℓ ^ _ :
    Bcris) ^ n) • Q.eval₂ (coefEnd (PadicAlgCl ℓ) _) (linearFrob (decompRep (X θ o).rep A) ..) _ ∧
    ∀ f, lift (lsmul .. ∘ₗ f) M = (∑ N ∈ range n, Q.coeff N • groupRingHom _ (surjInv (hs θ) (lift
    (lsmul .. ∘ₗ f) (Y θ N)))) *ᵥ v from ⟨∑ N ∈ range n, lTensor _ (Q.coeff N • applyVec (u θ o) v)
    (Y θ N), by simpa +contextual [eval₂_eq_sum_range' _ h, smul_sum, periodTensorMap,
    hG, smul_comm _ δ, tmul_eq_smul_one_tmul δ, ← Nat.cast_smul_eq_nsmul Bcris, smul_smul,
    ← pow_add, mem_range_le, _root_.smul_pow, ↓linearFrob_pow (H
    ..).1.isPotCrys w, ↓linearFrob_twist_cyclotomicGp (C ..).isPotCrys w d ew, ↓map_nsmul]
    using congr(∑ N ∈ range n, (coefEnd ..) _ ($((congrArg _ (V θ N)).trans (baseChange_linearFrob
    (U θ (H θ)).1.isPotCrys (w.pow N) (H θ o).1.isPotCrys (applyVec (u θ o) v) (by simp [hu]) _)))),
    by simp [← hu, hG, surjInv_eq, sum_mulVec, smul_sum, smul_comm (Q.coeff _)]⟩
  have Z f := Z _ @O _ (fun θ x ↦ ext_iff_mulVec.2 fun v ↦ by
    erw [← E θ x (h ..).1,
      periodTensorMap_injective (a₂ := 0) ((V ..).trans (((h ..).2.2 w).2 ▸ smul_zero _))]
    simp; rfl) fun θ ↦ ext_iff_mulVec.2 fun v ↦ (E t₀ none hP v f).symm.trans
    (periodTensorMap_injective (V t₀ none hP v ▸ V θ none hP v) ▸ E ..)
  use (C t₀ none).isPotCrys, (isBaseChange ..).algHom_ext _ _ fun v ↦ ?_
  simpa [D.ne_zero, Algebra.smul_def δ, (NeZero.of_faithfulSMul ℚ_[ℓ] _ ℓ).1,
    tensor_eq_zero_of_separating c.eq_zero_of_coord _
    fun f ↦ (E ..).trans (Z _ ▸ zero_mulVec v)] using! (V t₀ none hP v).symm
end

-- part: Lib.PadicHodge.Crystalline.GoodCriterion
section
/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Potentially crystalline with inertia acting trivially on D_pcris implies crystalline.
Crystalline iff potentially crystalline with trivial inertia action; a multiple of a killing
polynomial kills. -/

open Submodule Subgroup IsIntegral Module.End NonarchimedeanGroup

/-- Let j have open image in G_p and T be potentially crystalline. If every s in Γ with j(s) in
inertia fixes each element of D_pcris(T), the elements of B⊗T fixed near 1, then T is
crystalline. -/
lemma IsPotCrys.isCrystalline_of_inertia_fixes {p} [ThePrime p] {Γ R T} [Group Γ] [CommRing R]
  [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 :
  OverGp Γ p] {ρ : Representation R Γ T} (h : IsPotCrys ρ) (hI : ∀ s, IsWeilPair (toGp s) 0 →
  linearFrob ρ s 0 = 1) : IsCrystalline ρ := eq_top_mono (span_le.2 fun y a ↦ by
  let ⟨V, W⟩ := is_nonarchimedean _ (nhds_one_le_map_nearOne Γ (Filter.image_mem_map a))
  let U := id (OpenSubgroup.mk (inertiaGroup _ (intQpBar p) ⊔ V.1) (isOpen_mono le_sup_right V.2))
  choose c hf _ hE _ using Lift.exists_kummer_chart _ (𝒥 := ⟨_, ⟨U.1.range_subtype ▸ U.2⟩⟩)
  refine (span_subset_span ..) (mem_span_fixed (L := (isField_of_isIntegral_of_isField' (S :=
    integralClosure ℚ_[p] Bcris) (Field.toIsField ℚ_[p])).toField) 𝒥.toGp (.tprod (actionRep _ Bcris
    toGp) (overZp _)) (fun _ _ _ ↦ tensorAction_smul ..) (fun g m ↦ ?_) fun s n ↦
    U.1.range_subtype.le (c.chart_isChartOf s ⟨fun a ↦ by
    simpa using injective_BPlus_Bcris ((smul_algebraMap_eq_algebraMap_smul ..).symm.trans congr($(
                  n ⟨⟨_, (of_finite ℤ_[p] a).algebraMap.algebraMap.tower_top⟩, fun u ↦
      Subtype.ext ((smul_algebraMap_eq_algebraMap_smul ..).trans
      (congrArg _ ((hf u).1 a)))⟩).1)), by simp [← sub_eq_of_eq_add (hE _).1, c.theta_E, U]⟩))
  let ⟨i, k, _, v, e⟩ := mem_sup_of_normal_left (hs := ⟨fun _ h g ↦
    isLocalGalois_padic.4 g ▸ h.conj g⟩).1 m
  obtain ⟨t, w, rfl⟩ := W v
  erw [← div_mul_cancel g t, map_mul, mul_apply, w, ← linearFrob_apply h, hI] <;>
    simp [isWeilPair_zero_iff, ← e, k, a]) h

variable {ℓ E m A} [ThePrime ℓ] [Field E] [EmbeddedNumberField E] [Fintype m] {r : GalRep ℓ E m}

/-- Let A be a place not above ℓ, r finite on inertia at A, and s an inertia element killed by
P. Then p(r(s)) = 0 for every polynomial p vanishing at all roots of P. -/
lemma IsFiniteTypeAt.aeval_eq_zero_of_roots (h : IsFiniteTypeAt r A) (hA : A ℓ = 1) {s} (hs :
  s ∈ inertiaGroup _ A) {P} (hP : PolyKillsAt r A s P) p : (∀ x, P.IsRoot x → p.IsRoot x) →
  Polynomial.aeval (r s).1 p = 0 := map_eq_zero_of_roots _ (by simpa [pow_mem hs, Units.ext_iff]
  using! ((mapClusterPt_one_atTop_pow s).frequently (h.1 hA)).forall_exists_of_atTop 1) (hP.1 hA)

lemma PolyKillsAt.of_dvd {s P Q} : PolyKillsAt r A s P → P ∣ Q → PolyKillsAt r A s Q := by
  grind -linarith [PolyKillsAt, IsKilledBy, Polynomial.eval₂_mul_noncomm,
    commute_coefEnd_linearFrob, dvd_def]

/-- At a place A above a finite place w, r is unramified (crystalline above ℓ) exactly when it
is of finite type and X − 1 kills every element of inertia. -/
lemma isGoodAt_iff : IsGoodAt r A ↔ IsFiniteTypeAt r A ∧ ∀ s ∈ inertiaGroup _ A,
  PolyKillsAt r A s (Polynomial.X - 1) := ⟨fun ⟨h, g⟩ ↦
  ⟨⟨by aesop, g.isPotCrys⟩, fun s i ↦ ⟨by aesop, fun t ↦ by simp_all [← (ℓ.pow_right_inj Fact.out).1
  (t.eq_pow_of_isFrob (PadicPlaceEmbedding.isWeilPair_zero_iff.2 i)), IsKilledBy,
  IsCrystalline.isPotCrys, IsCrystalline.linearFrob_eq_one]⟩⟩, fun ⟨h, g⟩ ↦
  ⟨by simp_all [PolyKillsAt], h.2.isCrystalline_of_inertia_fixes fun s t ↦ by simpa using
  ((g _ (PadicPlaceEmbedding.isWeilPair_zero_iff.1 t)).2 t).2⟩⟩
end
