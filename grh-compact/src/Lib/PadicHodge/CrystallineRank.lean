import Lib.PadicHodge.BlochKato
import Lib.ClassField.FormalHeight
import Lib.Shimura.FockThetaFunctions
import Lib.PadicHodge.DeterminantBound

section
/-! Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. Only the inequality is proved, not perfectness or the Euler characteristic formula. It is
proved outright when Galois acts through a p-group (Kummer theory, dévissage), and otherwise it
descends by a Sylow argument from a largest orthogonal pair, supplied by crystalline cocycles of a
twist. Source: J.-P. Serre, Galois Cohomology (1997), II §5.2 Thm 2 and §5.7; J. S. Milne,
Arithmetic Duality Theorems (2nd ed. 2006), I 2.3, 2.8.

This file: Dual crystalline lattices have complementary cocycle counts; index form of the local
duality inequality. -/

open Lift Module LE Submodule Function crysCocycles NeZero AddSubgroup Multiset Topology Nat Algebra
  LinearMap IsDiscreteValuationRing PadicInt MulAction Equiv DFunLike IsLocalGalois
variable {ℓ} [ThePrime ℓ] {R Γ : Type} [CommRing R] [PadicIntegerRing R ℓ] [Group Γ]
  [TopologicalSpace Γ] {L L' : GalLattice R Γ} [𝒥 : OverGp Γ ℓ] (hj :
  IsOpenEmbedding 𝒥.toGp) (h : IsPotCrys L.ρ) (h' : IsPotCrys L'.ρ) (b :
  L' ≃ₗ[ℤ_[ℓ]] Dual ℤ_[ℓ] L) (hb : ∀ g x y, b (L'.ρ g x) (L.ρ g y) = χ g • b x y)

omit [TopologicalSpace Γ] [OverGp Γ ℓ] in
/-- Let R be a discrete valuation ring, finite and free over ℤ_ℓ, and L a lattice over R. For
some ℤ_ℓ-linear form f on R, the map φ ↦ f ∘ φ is a bijection from Hom_R(L, R) onto
Hom_{ℤ_ℓ}(L, ℤ_ℓ). -/
lemma exists_perfect_pairing : ∃ f : Dual _ R, Bijective ((restrictScalarsₗ ℤ_[ℓ] R L R
    ℤ_[ℓ]).compr₂ f) := let D := Dual ℤ_[ℓ] R
  let := compHom (R := Rᵈᵐᵃ) D (algebraMap R Rᵐᵒᵖ)
  have e o y x : (o • y : D) x = y (o * x) := rfl
  have : IsScalarTower ℤ_[ℓ] R D := ⟨by aesop⟩
  have := Finite.right ℤ_[ℓ] R D
  have : IsTorsionFree R D := ⟨fun o ho ↦ (Algebra.IsAlgebraic.exists_smul_eq_mul ℤ_[ℓ] 1
    ho.ne_zero).elim fun c ⟨k, n, e⟩ ↦ .of_mul (a := c) fun _ ↦ by simp [mul_comm, ← e, n]⟩
  have t : D ≃ₗ[R] R := .ofFinrankEq _ _ (by
    simpa [finrank_linearMap, finrank_pos.ne', D] using finrank_mul_finrank ℤ_[ℓ] R D)
  by refine ⟨applyₗ (1 : R) ∘ₗ ↑t.symm.1, Equiv.bijective ⟨_, (t.1 ∘ₗ ⟨⟨fun x ↦ · ∘ₗ smulRight id
    x, ?_⟩, ?_⟩), ?_, ?_⟩⟩ <;> intro <;> simp [e, smul_smul, mul_comm, D, -smul_eq_mul, ←
    t.eq_symm_apply, ext_iff]

include h h' hb

omit [TopologicalSpace Γ] in
/-- Let L, L' be potentially crystalline lattices in perfect equivariant duality with values in
ℤ_ℓ(1), Γ open of index n in G_ℓ. The orders of the images mod ℓ^m of Z_f(L') and Z_f(L) have
product ℓ^{m d (n+2)}, d the ℤ_ℓ-rank of L.

Known result: Bloch–Kato finite local condition: rank formula and size of its annihilator. -/
lemma IsPotCrys.index_mul_index_dual m : (pPowMultiples (crysCocycles L.ρ) m).index * (pPowMultiples
  (crysCocycles L'.ρ) m).index = ((ℓ ^ m) ^ finrank ℤ_[ℓ] L) ^ (2 + 𝒥.toGp.range.index) := by
  have ⟨J, _, hJ⟩ := h.exists_hasJumps (ρ := overZp _) (ofId ..)
  obtain ⟨⟨⟩, ⟨⟩⟩ := finrank_eq h hJ, finrank_eq h' fun u ↦ by simpa [← (J.count_map_eq_count' (-· -
    1) fun _ ↦ by lia)] using (jump_eq_of_pairing (ρ := overZp _) h b 1 (by simpa)).trans (hJ _)
  simp_all [← pow_add, ← pow_mul, b.finrank_eq, finrank_linearMap]
  grind [countP_map, countP_eq_card_filter, card_eq_countP_add_countP]

include hj

/-- Local duality: L, L' potentially crystalline, perfectly paired by b into ℤ_ℓ(1), Γ → G_ℓ an open
embedding, A the image of Z_f(L) in V = L/ℓ^m. If A and S consist of continuous cocycles whose cup
products with H bound in ℚ̄_ℓ^×, then [S : S∩A] divides [Z_f(L') : H∩Z_f(L')]. -/
lemma IsPotCrys.relIndex_dvd_of_orthogonal [IsTopologicalGroup Γ]
    {m} {V : DiscreteModule ℤ_[ℓ] Γ} [Finite V] {q :
  L →+ V} (l : IsLinearMap ℤ_[ℓ] q) (e₀ : ∀ g x, q (L.ρ g x) = V.ρ g (q x)) (o : Surjective q) (k :
  q.ker = pPowMultiples L m) {H S : AddSubgroup (Γ → _)} (hZ : ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).carrier ∪ S ⊆ Z1 V.ρ) (hH : ∀ s ∈ ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).carrier ∪ S, ∃ a, q ∘ a = s ∧ ∀ c ∈ H, (fun x ↦ zmodPowToUnits m (.mk'' (b
  (L'.ρ x.1 (c x.2)) (a x.1)))) ∈ B2 (unitsRep.comp toGp)) : ((crysCocycles L.ρ).toAddSubgroup.map
  (q.compLeft Γ)).relIndex S ∣ H.relIndex (crysCocycles L'.ρ).toAddSubgroup := by
  let := MulSemiringAction.compHom (PadicAlgCl ℓ) 𝒥.toGp; have C := h.index_mul_index_dual h' b hb
  let u := (zmodPowToUnits m).comp (mkQ _).toAddMonoidHom
  obtain ⟨c, _⟩ := by simpa [k] using (index_comap_of_surjective ⊥ o).symm,
    isLocalGalois_localFieldOf hj
  obtain ⟨⟨Q, w⟩, ⟨r, I⟩ : ∃ r : L' →+ V.cartierDual, ∀ x y, r x (q y) = u (b x y)⟩ :=
    exists_openNormalSubgroup_apply_eq V.continuous, ⟨(q.liftOfSurjective o ⟨(toAddMonoidHom'.comp
    b.flip.toAddMonoidHom).compr₂ u, by simp [k, le, u, ext_iff]⟩).flip, by simp⟩
  have k' : r.ker = pPowMultiples _ m := by ext; simpa [u, ext_iff, o.forall, I, zmodPowToUnits,
    (rootPowHom ..).2,
    map_eq_zero_iff, ← RingHom.mem_ker, ker_toZModPow, mem_span_singleton, mul_comm (_ ^ m),
    (reindex_equiv b.symm).2.1, ← b.injective.eq_iff] using ⟨(⟨_,
    codRestrictOfInjective_comp_apply _ (mulRight ..) (mul_left_injective₀ out) ·⟩), by tauto⟩
  have ⟨U, _, P, p⟩ := DiscreteModule.exists_open_sylow ℓ Q
  have hU := hj.comp U.2.isOpenEmbedding_subtypeVal
  let J := OverGp.mk (toGp.comp U.subtype) ⟨hU.2⟩
  have ⟨a, ha⟩ := exists_jump_bound (ρ := overZp (L'.ρ.comp U.subtype)) (γ := ofId ..)
  let N := (a + 1 : ℤ) * Nat.card (Perm V)
  let M := {L with ρ := smulMonoidHom.comp ((χ ^ N).prod L.ρ)}
  let M' := {L' with ρ := smulMonoidHom.comp ((χ ^ (-N)).prod L'.ρ)}
  have ⟨t, t'⟩ : IsPotCrys M.ρ ∧
    IsPotCrys M'.ρ := by constructor <;> apply IsAdmissible.tate_twist <;> tauto
  have B g x y : b (M'.ρ g x) (M.ρ g y) = χ g • b x y := by simp [M, M', hb, Units.smul_def]
  have e g x : q (M.ρ g x) = V.ρ g (q x) := e₀ .. ▸ (l.2 ..).trans congr($(show
    toPermHom ℤ_[ℓ]ˣ V _ = 1 by simp [N, zpow_mul, -toPermHom_apply]) _)
  have D {σ τ : Representation R Γ _} (e : ∀ g x, q (σ g x) = V.ρ g (q x)) (B : ∀ g x
      y, b (τ g x) (σ g y) = χ g • b x y) g x : r (τ g x) = DiscreteModule.ρ _ g (r x) := by
    simp [ext_iff, (o.comp (σ.apply_bijective g).2).forall, I, ← e, B, Units.smul_def, u,
      map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, -smul_eq_mul]; tauto
  have := (mul_dvd_mul_right ((card_dvd_of_le (sup_le_iff.2 (forall₂_or_left.1 fun s z ↦ (hH s
    z).rec fun a ⟨F, G⟩ ↦ ⟨⟨_, hZ z⟩, by
    exact fun _ ⟨c, v, e⟩ ↦
    e ▸ neg_eq_zero.1 ((cupProduct_flip ..).symm.trans ((ker_mkQ _).ge (by
    simpa [← F, ← by simpa [ext_iff] using D e₀ hb, I] using! G c v))), rfl⟩))).trans (card_map_dvd
    _ (Z1 _).toAddSubgroup.subtype)) _).trans (V.local_duality_card_dvd (holdsCorestrictions hj t'
    (D e B) k' (r.range_eq_top.1 (eq_top_of_card_eq _ (by erw [← index_ker, k', index_pPowMultiples,
    b.finrank_eq, finrank_linearMap_self, card_congr (β := _ →* _ˣ)
    AddMonoidHom.toMultiplicativeLeft, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, c]))) hU)
    (t.holdsCorestrictions hj e k o hU) (c ▸ (P.pow_left _).pow_left _) ?_ ?_ ((H.addSubgroupOf
    (crysCocycles _).toAddSubgroup).map (h'.reducedCocycle hj (D e₀ hb) k')))
  · rw [← relIndex_ker, ker_reducedCocycle, ← index_ker, ker_reducedCocycle, ← index_ker,
      ker_reducedCocycle, t.index_mul_index_dual t' b B, ←
      relIndex_bot_left, ← relIndex_mul_relIndex _ _ _ bot_le le_sup_left, relIndex_sup_left,
      relIndex_bot_left, mul_right_comm, ← relIndex_ker] at this
    grw [← mul_dvd_mul_iff_left (left_ne_zero_of_mul (ne_zero_of_dvd_ne_zero out ‹_›)), this, ← C,
      mul_assoc, ← ker_reducedCocycle hj h e₀ k, AddMonoidHom.ker_codRestrict,
      index_dvd_of_le inf_le_left, ← relIndex_mul_index inf_le_right, inf_relIndex_right] <;> rfl
  · rintro _ ⟨⟨w, hw⟩, rfl⟩ _ ⟨c, rfl⟩
    choose l n y o using
      (t'.comp _).exists_coboundary_eq_smul (fun u o ↦ by nlinarith [ha _ ((jump_twist_cyclotomicGp
      N (by simp [M', J, toGp, ← Units.smul_def])).trans_ne o), @card_pos (Perm V) _ _]) c.2
    choose i v z using associated_pow_irreducible n irreducible_p
    choose E X using show ∃ E : _ →+ _, ∀ a, E (l * a) = u a by
      simpa using! QZ.exists_extend (l • .id _) u (by simp [le, n])
    have Z y : ℓ ^ (i + m) • E y = 0 := by simp [← E.map_nsmul, pow_add, ← z, mul_assoc, X, u]
    refine (ker_mkQ _).ge ⟨_, continuous_comp hU (t.comp _) (E.comp (b y)) (by tauto) hw,
      fun g v ↦ ?_⟩
    refine .trans ?_ congr($(map_cyclotomicGp_smul _ Z (b y (w v)) (toGp g.1)) - _ + _)
    simpa [apply_mul hw, sub_add, ← I, *] using! congr(E (b ($o.symm g) (M.ρ g _)))
  refine (card_mul_card_le_of_orthogonal (J := isLocalGalois_localFieldOf (j :=
    J.toGp) hU) (Q.subgroupOf U) (by simp [of_finite ⟨_, J.2.1⟩,
    isUniformiser_ell.card_quot isLocalGalois_padic 1, residueCard_padic]; rfl) ⟨‹_›, by
    rw [pow_mul, ← c]; simp, (by simpa using! w ·), fun _ ↦ by simp⟩ (p _ ·.2) · · · |>.trans_eq ?_)
  erw [← index_ker, ker_reducedCocycle, ← index_ker, ker_reducedCocycle, mul_comm,
    index_mul_index_dual (L := ⟨_, _⟩) (L' := ⟨_, _⟩) (t.comp U.subtype) (t'.comp _) _ (B ·), c]
end

section
/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Spacing lemma: no three thick places (`Data.thick`) in a short Frobenius arc;
thick embeddings have the same sign if ℓ divides `Data.cycloConductor`. -/


open Fact Int ZMod IsCyclotomicExtension Parameters IsAlgClosed
variable {P} {D : Data P} {ℓ} [hp : Fact ℓ.Prime] {e : D.E →+* PadicAlgCl ℓ} {g g' g₁ : Gp ℓ}

lemma fixes_emb_of_fixes_rootsOfUnity (H : ∀ ζ, ζ ^ D.cycloConductor = 1 → g ζ = ζ) x : g (e x) =
  e x := have := (@toCycloField P D.s).toAlgebra
  (surjective_domRestrict_of_isAlgebraic e.toRatAlgHom).elim fun ψ E ↦ congr($E x) ▸ congr($(((
  zeta_spec D.cycloConductor ℚ (cycloField D.cycloConductor)).powerBasis _).algHom_ext
  (f := .comp (g.restrictScalars ℚ) ψ) (by simp [H, ← map_pow, zeta_pow])) _)

lemma cmSign_spec (σ : D.E →+* _) : σ (P.sqrtNegDInE D.s) = cmSign σ * QuadField.sqrtNegD P.d ∧
  Φ (.mk σ) (P.ζ _) = σ (P.ζ _) ^ (cmSign σ).1 := by cases Φ_eq_or σ with exact ‹_› ▸ (by
       simp [cmSign, ← RCLike.star_def, ← map_star_complex])

variable [PadicIso ℓ] {a i n} (t : .mk (complexEmbOf e g) ∈ D.thick) (t' : .mk (complexEmbOf e g') ∈
  D.thick) (h : (g' * g⁻¹) (e (P.ζ _) ^ ℓ ^ a) = (e (P.ζ D.s) ^ ℓ ^ a) ^ ℓ ^ n)
include h

variable (e g g' a n) in
/-- Let g'g⁻¹ raise e(ζ)^{ℓ^a} to the power ℓ^n, and y be the ratio of the infinite places of
the embeddings read by g and g'. Modulo any m ∣ N₁ prime to ℓ^a, y ≡ ±ℓ^n, the sign being
the product of their signs. -/
lemma placeClass_ratio {y} m d (c : (ℓ ^ a).Coprime m) (hy : .mk (complexEmbOf e g') * y =
  .mk (complexEmbOf e g) := by apply mul_div_cancel) : (@placeClass P _ m d y).1 =
  (cmSign (complexEmbOf e g) * cmSign (complexEmbOf e g') : ℤ) * ℓ ^ n := by
  have E := congr((g' (ιℓ $(hy ▸ phi_mul _ _ (ζ ..))) ^ (cmSign (complexEmbOf e g')).1) ^ ℓ ^ a)
  simp [galOfPlace_zeta, cmSign_spec, complexEmbOf, ← zpow_natCast, ← zpow_mul] at *
  rw [zpow_mul', h, ← zpow_mul, mul_rotate, ← div_eq_one_iff_eq, ← zpow_sub₀, ← sub_mul,
    (isPrimitiveRoot_zeta.map_of_injective e.injective).zpow_eq_one_iff_dvd] at E
  simpa [placeClass, unitsMap, mul_comm, ↓← mul_assoc, ← intCast_eq_intCast_iff_dvd_sub] using
    c.symm.cast.dvd_of_dvd_mul_right (d.natCast.trans E)
  repeat simp [isPrimitiveRoot_zeta.ne_zero, NeZero.ne, zpow_ne_zero]

include t t'

/-- Spacing: let ℓ ≤ kt, 0 < i < n ≤ 27s, and g'g⁻¹, g'g₁⁻¹ raise e(ζ)^{ℓ^a} to the powers ℓ^n,
ℓ^i. If the embeddings read by g and g' are thick, that read by g₁ is not. -/
lemma not_thick_of_short_arc (h₁ : (g' * g₁⁻¹) (e (P.ζ _) ^ ℓ ^ a) =
  (e (P.ζ _) ^ ℓ ^ a) ^ ℓ ^ i) (hk : ℓ ≤ D.k * D.t) (hi : 0 < i) (hn : i < n) (hL : n ≤ 27 * D.s) :
  .mk (complexEmbOf e g₁) ∉ D.thick := fun u ↦ by
  have A {g n m} h d c := congr($(placeClass_ratio e g g' a n h m d c) ^ 2)
  simp [mul_pow, ← Int.cast_pow, isUnit_sq, -map_pow] at A
  obtain rfl | o := hp.1.eq_two_or_odd'
  · grind [@orderOf_one_add_prime 3 out nofun _ ▸ orderOf_le_of_pow_eq_one hi (.trans (by norm_num
      [← mul_pow, sq]) ((A h₁ ⟨_, mul_left_comm ..⟩ (.pow _ _ rfl)).symm.trans
      (by simp [D.thick_eq_neg_one_mod, *]))), @Nat.lt_pow_succ_log_self 3 out D.s]
  exact (@two_pow_le_of_pow_eq_one ℓ hp.1.one_lt (i * 2) _ (by lia) (by rw [Int.cast_natCast,
    pow_mul, ← A h₁ two_pow_dvd_N₁, ← map_div, D.three_term (2 * i) (2 * n) _ _ _ _ t'
    _ u _ t] <;> first | lia | simp [Units.ext_iff, pow_mul, A h, A h₁, o.pow] <;> ring)).not_gt
    (by grw [natAbs_natCast, hk, hn, hL]; use D.nat_le_of_hasLogBound)

omit h

/-- Let the prime ℓ divide N₁d and e embed E in Q̄_ℓ. If the complex embeddings `complexEmbOf e g`
and `complexEmbOf e g'` (g, g' in G_ℓ) both define thick places, then both or neither belong to the
CM type. -/
lemma cmSign_eq_of_thick (c : ℓ ∣ D.cycloConductor) : cmSign (complexEmbOf e g) =
  cmSign (complexEmbOf e g') := units_ne_iff_eq_neg.not_right.2 fun _ ↦ if b : ℓ ∣ D.N₁ then by
    let x := e (P.c₀InE D.s)
    rcases congr(g (ιℓ ($((cmSign_spec (complexEmbOf e g)).1) + $((cmSign_spec
      (complexEmbOf e g')).1)))), P.dvd_norm_c₀ out b, congr(‖e $(P.c₀InE_mul_one_sub D.s)‖),
      IsUltrametricDist.norm_add_le_max x (1 - x), dist_smul (g * g'⁻¹) x 0
    simp_all [sqrtNegDInE, map_ofNat, complexEmbOf, ← Padic.norm_natCast_lt_one_iff,
      ← PadicAlgCl.norm_extends]
    grind [sq_nonneg (‖x‖ - 1), sq] else (exists_apply_eq_pow b (by simp [← map_pow,
  isPrimitiveRoot_zeta.1]) _).elim fun n ↦ mt (placeClass_ratio e g g' 0 n · _ ⟨_, rfl⟩ (by simp))
  (by simp_all [D.placeClass_of_thick, hp.1.dvd_mul, Nat.prime_dvd_prime_iff_eq, out]; grind
  [pow_d_ne_neg_one])
end

section
/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

Part of: Bloch–Kato finite local condition: rank formula and size of its annihilator (known result;
see Lib.PadicHodge.BlochKato.BlochKato).

This file: the rank of the crystalline cocycles Z_f(L) is rk L plus the number of negative
Hodge–Tate weights; so a power of ℓ that maps Z_f(L) into a submodule bounds the quotient in
length. -/


export Lift (InClass)

open Lift crysCocycles Module Set Multiset Finset DFunLike Submodule Finite TensorProduct
variable {ℓ} [ThePrime ℓ] {O : CoeffRing ℓ} {Γ n} [Group Γ] [Fintype n] [𝒥 : OverGp Γ
  ℓ] {R} [CommRing R] [Algebra ℤ_[ℓ] R] {L : GalLattice O Γ}

/-- The Γ-lattice over R given by the module R^n with Γ acting through the matrix representation
ρ. -/
noncomputable abbrev matrixLattice (ρ : Γ →* Matrix n n R) : GalLattice R Γ :=
  ⟨n → R, actionRep R _ ρ⟩

/-- Let j identify Γ with the local Galois group of E at e, and L be potentially crystalline
with jumps J(ι⁻¹g⁻¹e) at each coefficient embedding g. Then rk Z_f(L) is rk L plus the
number of negative jumps, summed over the embeddings ι⁻¹g⁻¹e. -/
lemma finrank_crysCocycles_eq_add_neg_jumps [TopologicalSpace Γ] {E} [Field E] [UnramCMField E] {e :
  E →+* _} [PadicIso ℓ] (hj : IsCompletionGroup e 𝒥.toGp) (h : IsPotCrys L.ρ) {J : _ → _} (hJ : ∀ g,
  HasJumps L.ρ (coeffEmb O g) (J (complexEmbOf e g))) : finrank O (crysCocycles L.ρ) =
  finrank O L + ∑ σ with ∃ g, complexEmbOf e g = σ, (J σ).countP (· < 0) := have := fg h
  Nat.mul_left_cancel (card_pos_iff.2 ⟨coeffEmb O 1⟩) (by
    choose s _ using @coeffEmb_surjective _ _ O
    choose K _ hK using h.exists_hasJumps
    simpa [(finrank_eq h (J := univ.sum K) (by simp [h.sum_jump_eq_jump_overZp, count_sum',
      ← hK _ ·])).2, hj.index_eq_card_range, mul_add, finrank_mul_finrank, ← coe_countPAddMonoidHom,
      sum_set_coe, ← filter_mem_univ_eq_toFinset, (Multiset.ext' fun u ↦ hK .. ▸ hJ · u), fun g ↦
      (by simp [Function.Injective, Subtype.ext_iff, ← apply_rangeSplitting,
      hj.complexEmbOf_eq_iff] : ((⟨_, ·, rfl⟩) <| rangeSplitting (complexEmbOf e) · *
      g).Injective).bijective_of_finite.sum_comp (J ·)] using congrArg (countP _)
      (congr(∑ y, $((by intro; simp_all [coeffEmb, ext_iff]; grind : (coeffEmb O <| rangeSplitting
      (complexEmbOf e) y * s ·).Injective).bijective_of_finite.sum_comp K)).symm.trans sum_comm))

/-- Let L be potentially crystalline, ℓ^k Z_f(L) ⊆ S for a submodule S, and 2k·rank L ≤ y. Then
Z_f(L) modulo Z_f(L) ∩ S has normalised length at most y times the index of j(Γ) in the
absolute Galois group of ℚ_ℓ. -/
lemma normLength_defect_le {k : ℕ} (hT : IsPotCrys L.ρ) {S} {y : NNReal} (hk :
  finrank O L * (2 * k) ≤ y) (h : ∀ c ∈ crysCocycles L.ρ, (ℓ : ↑O) ^ k • c ∈ S) :
  O.normLength (relLength (crysCocycles L.ρ) S) ≤ 𝒥.toGp.range.index * y := by
  obtain ⟨_, K, r, H⟩ := fg hT, hT.exists_hasJumps (ρ := overZp _) _
  grw [relLength, length_le_of_surjective _ (factor_surjective ((span_smul_eq {(ℓ : ↑O) ^ k}
    ⊤).trans_le ?_)), ← (quotTensorEquivQuotSMul ..).length_eq, (equivFinsuppOfBasisRight (finBasis
    ..)).length_eq, ← hk] <;> simp_all [set_smul_le_iff, submoduleOf]
  exact_mod_cast le_of_mul_le_mul_left (by grw [← mul_assoc, finrank_mul_finrank, (finrank_eq hT
    H).2, countP_le_card, r, ← one_add_mul, Nat.one_le_of_lt (toGp.range.quotient_finite_of_isOpen
    𝒥.2.1).card_pos, ← finrank_mul_finrank _ O]; linarith!) (finrank_pos : _ < finrank ℤ_[ℓ] O)
end
