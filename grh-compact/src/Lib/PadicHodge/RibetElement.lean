import Lib.PadicHodge.CrystallineRank
import Lib.PadicHodge.ExponentTheorems
import Lib.PadicHodge.RibetFirstOrder
import Lib.PadicHodge.TiltingLemma
import Lib.PadicHodge.LabelledColumns
import Lib.PadicHodge.RowBalanced
import Lib.PadicHodge.OddShaBound

section
/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Case analysis on ℓ bounding crystalline classes modulo those orthogonal to congruent
lattices. -/

open Lift Nat Module Finset Real

/-- Local loss, crystalline case. Let L be crystalline with jumps in U'; let U, U' lie in
opposite windows `Lift.IsInJumpWindow` at b + δ (thick) or G + δ (thin), with the listed conditions
on sizes and on a Kummer chart. Assume U' lies in [−η, 0], or negative members of U' and
negative members of U are ≤ −h/2 with ≤ μ jumps per embedding in [−η, η]. Then Z_f(L) modulo
`Lift.cupOrthogonal` for crystalline lattices with jumps in U has normalised length ≤ [G_ℓ :
j(Γ)]·y if y ≥ 10⁵(rk L·⌊2λ/Q⌋·m + μλ), λ = `lambdaLoss`. -/
lemma crystalline_defect_le {ℓ} [hp : ThePrime ℓ] [Γ : GroupOverGp ℓ] [TopologicalSpace Γ]
    {O : CoeffRing ℓ} {L : GalLattice O Γ} (Q m h μ : ℕ) {G b δ η W} {th ε : _ →
  _} {U U'} (Q₀ : 0 < Q) (hQ : 99 * (Q * Q + (W + 1) * Q + Q + W + m) ≤ h) (hG : 99 * h ^ 3 ≤
  G) (hb : 99 * (G * h ^ 3 + G) ≤ b) (hm : 2 * (4 * b : ℝ).log < m) (hδ : δ < η) (hη : 99 *
  ((η + W) * Q + η + h) ≤ h ^ 3) (hU : ∀ g, IsInJumpWindow η (-ε g) (ite (th g) b G + δ) W (U g))
  (hU' : ∀ g, IsInJumpWindow η (ε g) (ite (th g) b G + δ) W (U' g)) (hL : InClass ⊤ ⊥ U' L) (c :
  (∀ g, (∀ u < 0, u ∈ U g ∨ u ∈ U' g → 2 * u ≤ -h) ∧ ∑ u ∈ Icc (-↑η) ↑η, jump L.ρ g u ≤ μ) ∨ ∀ g,
  U' g ⊆ Icc (-η) 0) {y : NNReal} (hy : (10 ^ 5 * (finrank O L * (2 * lambdaLoss h b ℓ / Q * m) +
  μ * lambdaLoss h b ℓ) : ℕ) ≤ y) (k : KummerChart Γ) (ζ : k.LetterRoot O) (T s : _ → _) (hj :
  Topology.IsOpenEmbedding Γ.overGp.toGp) (hf : k.e * k.f = Γ.overGp.toGp.range.index) (he : k.e ≤
  h) (hs : ∀ g, th g ∨ Q < ℓ → th g = T (g ζ) ∧ ε g = s (g ζ)) (hu : k.IsUnramified ∧ 7 ≤ ℓ ∨ ℓ ≤
  Q ∧ ∀ z z', s z = s z') (hT : ℓ ≤ Q → ∀ᵉ (z) (a ∈ Icc 1 (ℓ.log (h ^ 3)))
  (b ∈ Icc 1 (ℓ.log (h ^ 3))), T z → T (z ^ ℓ ^ a) → ¬T (z ^ ℓ ^ (a + b))) : O.normLength (relLength
  (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L)) ≤ Γ.overGp.toGp.range.index * y := by
  have M {H} (h : H ≤ 4 * b := by omega) : ℓ.log H < m := by grw [← @cast_lt ℝ, ← hm, h,
    natLog_le_logb, logb, ← hp.out.two_le, ← one_sub_inv_le_log_of_pos] <;> norm_num; linarith
  have N {n} :=
    (lambdaLoss.eq_1 h b ℓ ▸ padicValNat_dvd_iff_le (n := n) (by simp [prod_eq_zero_iff])).1
  have A := (2 * lambdaLoss h b ℓ).lt_div_mul_add Q₀
  generalize lambdaLoss .. = v, _ / Q = K at *
  have Λ : 2 * b < ℓ * (v + 1) := (lt_mul_div_succ _ hp.out.pos).trans_le (by grw [← N (.mul_right
    pow_padicValNat_dvd _), ← padicValNat_mul_div_factorial, padicValNat_factorial_mul]; lia)
  have hv i : let z := ↑(theta (k.letterTeich i)); let w :=
        (IsInJumpWindow (ite (ℓ ≤ Q) (2 * G) η) · (ite (T z)
        (b + δ) (G + δ)) W); w (-s z) (k.letterJumps ζ U i) ∧ w (s z) (k.letterJumps ζ U' i) := by
    clear * - hs hU hU' hδ hη hG hQ
    simp [← ite_add, KummerChart.letterJumps, IsInJumpWindow, -cast_ite] at *
    generalize theta _ = z; grind
  have ex {x} (e : x ≤ m) := normLength_defect_le hL.isPotCrys (k := 10 ^ 4 * (K * x))
    (hy.trans' (mod_cast by grw [e]; ring; omega)) ∘ forall₂_imp
    (k.mem_cupOrthogonal_of_scaledCupBounds ζ hj le_top le_rfl hL (U := U) _ ⟨·, ·⟩)
  split_ifs at hv with hl <;> simp [hl] at hu
  · have D : 2 * (b + δ) < h ^ 2 * K := by
      nlinarith only [A, Λ, hl, hQ, h.le_mul_self, (by omega : h + δ ≤ b)]
    have := (lt_pow_succ_log_self hp.out.one_lt (h ^ 3)).le
    refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_sparse_thick (by omega : _ ≤ 9 * G) hv (by
      grw [← this, D, he]; linarith) (this.trans' (by omega)) (by omega) rfl
      (by clear * - hu; tauto) (by omega) (by grw [pow_log_le_self]; linarith; omega) (by
      simpa [(k.letterFrob.coe_pow · |>.trans (pow_iterate ..))] using hT hl <| theta <|
        k.letterTeich ·) ?_ ..
    grw [KummerChart.differentExp, ite_le_sup, padicValNat_le_nat_log, M, M, M,
      (by omega : _ + m ≤ h)]
    nlinarith only [D, hb]
  -- If `h³ ≤ v`, then `v` pays for the general bound. If not, `ℓ` is at least `9 G` and divides no
  -- integer near `b`, so it divides no nonzero integer near `0`, `± G` or `± b`.
  by_cases Z : h ^ 3 ≤ v
  · refine ex M fun _ _ _ _ P _ ↦ P.scaledCupBounds_two_sizes le_rfl hv ?_ rfl hu.1 hu.2 ?_ ?_ (by
      and_intros <;> nlinarith only [Λ, hl, hb, hη, hδ, Z, A, (by omega : Q ≤ h ^ 3)]) .. <;> omega
  obtain ⟨F, B⟩ := k.few_low_jumps ζ hj hu.1 (by omega) (a := 2 * (v + 1)) (by
    intro; grw [ite_le_sup, mul_left_comm, tsub_mul]; omega) (by omega) (by
    intro; split <;> omega) (fun _ y A d ↦ by_contra fun o ↦ Z (N (by
    obtain _ := Int.natAbs_le_of_dvd_ne_zero d o, (by nlinarith only [Λ, Z, hb] : 9 * G ≤ ℓ)
    grw [← dvd_prod_of_mem (a := y.natAbs), ← Int.natCast_dvd.1 d] <;> simp at A ⊢; omega))) hL hv
  exact if n : h / 5 ≤ v ∧ _ then by
    grw [B μ n.2, O.normLength_natCast_mul, ← hy, ← hf, (by omega : _ + 1 ≤ 6 * v),
      ← (M bot_le).succ_le, @Nat.le_of_mul_le_mul_right (W + 1) K _ (by omega) Q₀]
    simp [hu.1.2]; norm_cast; ring; omega
  else by simp [relLength_eq_zero.2 (F (by clear * - n c; grind))]
end

section
/-! Part of: Crystalline losses above ℓ are affordable (see New.Selmer.RibetElement).

This file: Crystalline defect of the dual of a block at one place, by cases. -/

open Lift CoeffRing Module Nat Classical NeZero NumberField Data Finset

/-- Local loss at one place above ℓ. For O large take lattices: one of rank r with row jumps J,
others with single jump c ∈ [0, t); and a class `Lift.InClass` with jumps among theirs, crystalline,
or tame for ℓ ∣ g. For L among them and in the class, Z_f(L^∨(1)) modulo `Lift.cupOrthogonal` has
normalised length ≤ [G_ℓ : j(Γ)]·rk L·loss/x, x = 1 for the row, else D.t.

Crystalline losses above ℓ are affordable. -/
lemma block_defect_le_at_place {P ℓ Γ} {D : Data P} [hp : ThePrime ℓ] [PadicIso ℓ] [Group Γ] [𝒥 :
  OverGp Γ ℓ] [TopologicalSpace Γ] {e r t J} (hJ : IsRowType D r t J) (hj :
  IsCompletionGroup e 𝒥.toGp) : ∀ᶠ O : CoeffRing ℓ in .atTop, ∀ {L : _ → GalLattice O Γ} {F K U},
  (∃ n, ℓ = D.g n ∧ ∀ s, IsWeilPair (toGp s) 0 → Lift.IsTameType ℓ D.r ((D.r + D.t) * D.r) (K s)) ∨
  F = ⊤ ∧ K = ⊥ → (∀ g, ∀ a ∈ U g, ∃ i, jump (L i).ρ g a ≠ 0) →
  (∀ i g, HasJumps (L i).ρ (coeffEmb O g) (i.elim (J (complexEmbOf e g)) fun c : Fin t ↦ {↑c})) →
  finrank O (L none) = r → ∀ c, let x := ite (c = none) 1 D.t; InClass F K U (L c) →
    O.normLength (relLength (crysCocycles (L c).tateDual.ρ) (cupOrthogonal (InClass F K U) _)) ≤
    𝒥.toGp.range.index * ↑(finrank O (L c) * (loss D ℓ / x)) := by
  obtain ⟨⟨k, -, he, un, y, A, hy⟩, N, ⟨i, a, m⟩⟩ := exists_kummer_chart Γ,
    D.nat_le_of_hasLogBound (B := D.k * D.t).trans' ∘
    le_of_dvd one_le ∘ hp.out.dvd_of_dvd_pow ∘ (dvd_trans · P.N₁_mul_d_dvd_M_omega), hJ.low_or_high,
    D.t_odd.pos, D.k_pos, hJ.t_le, (D.nat_le_of_hasLogBound : 3 * D.t ≤ D.h₂), D.h₂.le_mul_self
  filter_upwards [eventually_primitiveRoot (ℓ ^ k.f.val - 1)] with O ⟨ζ, z⟩ L F K U Y B T rfl c x H
  choose r R using @coeffEmb_surjective _ _ O; replace T i g a := R g ▸ T i _ a
  simp [T, Option.exists, Fin.exists_iff] at B
  have W g : let σ := complexEmbOf e (r g)
    let v := (IsInJumpWindow (D.h₂ ^ 2 + 1) · (ite (id (.mk σ ∈ D.thick)) D.b₁ D.b₂ + (i * D.h +
      D.h₂ - 2 * D.t)) (4 * D.t)); v (-cmSign σ) (U g) ∧ v (cmSign σ) ((U g).image (-· - 1)) := by
    intro σ; simpa [IsInJumpWindow, ← forall_and] using
      fun u h ↦ by obtain ⟨h, ⟨⟩⟩ := (B g u h).imp_left (m σ u),
      Int.units_eq_one_or (cmSign σ) <;> simp [*, w, abs_le] at h ⊢ <;> lia
  obtain ⟨hD, ⟨X⟩, ⟨n, ⟨⟩, Y⟩ | ⟨⟨⟩, ⟨⟩⟩⟩ := H.dual, (by lia : x ≤ D.t ∧ 0 < x), Y
  · have G g := (hj.2 g).2 (fixes_emb_of_fixes_rootsOfUnity fun z hz ↦
      (exists_apply_eq_pow (P.not_dvd_N₁_mul_d_of_modEq_one (D.g_modEq_one _)) hz
      g).elim (by simp [pow_eq_pow_of_modEq ((D.g_modEq_one _).pow _) hz]))
    refine normLength_defect_le hD.isPotCrys ?_ (tame_types_exponent (Γ :=
      ⟨Γ⟩) hj.1 G hD Y (hj.complexEmbOf_eq_iff.2
      (G (_ / 1)) ▸ W ·) (by grw [sub_le, a]; split <;> use D.nat_lt_of_hasLogBound))
    grw [finrank_linearMap_self, loss, ← one_le_padicValNat_of_dvd out, ← le_self_add, X]
    gcongr; rify; use D.le_of_hasLogBound
    clear * -; revert n; simp [gProd]
  let F := (coeffEmb O · ζ)
  have C {g g' k} (this : F g' = F g ^ k) :=
    cycCharMod_eq_iff.1 (cycCharMod_eq_of_isPrimitiveRoot (g := g' * g⁻¹) (.map_of_injective
    (.coe_submonoidClass_iff.2 z) g.injective) (by simpa [coeffEmb, F, ← map_pow]))
  let w z g := ite (ℓ ∣ D.cycloConductor) (.mk (complexEmbOf e g) ∈ D.thick) (F g = z)
  have u h := un fun _ ↦
    (hj.2 _).2 ∘ fixes_emb_of_fixes_rootsOfUnity ∘ apply_eq_self_of_mem_inertiaGroup h
  have σ h g g' (H : F g = F g' ^ 1) :=
    hj.complexEmbOf_eq_iff.2 (k.chart_isChartOf _ ⟨(fixes_roots_iff_fixesLambda (g * g'⁻¹)).1
    (by simpa using C H), sub_eq_iff_eq_add.2 (u h).1 ▸ by simp [k.theta_E]⟩)
  refine crystalline_defect_le (Γ := ⟨Γ⟩) _ D.m D.h₂ (finrank O (L c) * D.m / (D.k * x))
    D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound D.nat_le_of_hasLogBound
    D.nat_le_of_hasLogBound D.lt_of_hasLogBound (by grw [sub_le, a]; use D.nat_lt_of_hasLogBound)
    D.nat_le_of_hasLogBound (W · |>.1) (fun g _ h ↦ (W g).2 _
    (filter_subset (jump (L c).tateDual.ρ g · ≠ 0) _ h)) (hD.imp_right (by simp +contextual)) ?_ (by
    simp [loss, finrank_linearMap]; grw [cast_div_le, cast_div_le, ← X]; field
    norm_cast; clear * -
    lia) k ⟨ζ, by erw [card_units, card_flatFq, z.1]⟩ (∃ g, .mk (complexEmbOf e g) ∈ D.thick ∧
    F g = ·) (cmSign ∘ complexEmbOf e ∘ epsilon ∘ w) hj.1 he (by
    grw [Nat.le_mul_of_pos_right k.e k.f.pos, he, hj.index_eq_card_range, Finite.card_subtype_le]
    simpa [Embeddings.card, finrank_eq_two_mul_card_infinitePlace] using D.nat_le_of_hasLogBound)
    (fun g H ↦ by clear * - R σ H N C; grind [cmSign_eq_of_thick, @epsilon_spec _ (w (g ζ)) (by
    grind)]) (if h : _ then .inr ⟨N h, by simp [w, h]⟩ else .inl ⟨u h, le_of_not_ge (h ∘ (dvd_trans
    · (.trans (by cbv) ((P.3.mul_right _).mul_right _))) ∘ hp.out.dvd_primorial_iff.2)⟩) (by
    rintro h _ a p b q ⟨_, c, ⟨⟩⟩ ⟨_, _, E⟩ ⟨_, v, B⟩
    rcases (pow_sub_one_mul out _).trans (apply_eq_pow_of_isFrob hy (not_dvd_ordCompl hp.out out)
      ((P.isPrimitiveRoot_zeta.pow_of_dvd out (ordProj_dvd ..)).map_of_injective
      e.injective).1).symm,
      log_mono .refl hp.out.one_lt (D.nat_le_of_hasLogBound : D.h₂ ^ 3 ≤ (2 ^ D.s) ^ 12) with X
    simp [(hj.2 _).1 A, P.isPrimitiveRoot_zeta.ne_zero out, ← pow_mul 2] at *
    apply not_thick_of_short_arc c v (C B _ X) (C (by rwa [E, ← pow_mul, ← pow_add]) _ X)
      h <;> omega)
  cases c <;> [left; right] <;> simp [jump_tateDual H.isPotCrys, x,
    le_div_iff_mul_le, *] <;> clear W T H hD C
  exact fun g ↦ ⟨by grind [Int.units_natAbs], (hJ.card_low_le _).trans' (by
    gcongr; induction J _ using Multiset.induction <;> simp [Multiset.count_cons,
    Multiset.countP_cons, sub_eq_iff_eq_add, neg_eq_iff_eq_neg]; lia)⟩
  grind
end

section
/-! Part of: Ribet's method with congruent blocks and tied auxiliary primes (see
New.Selmer.RibetElement).

This file: Cocycles in a Tate twist cost only local loss and odd classes. -/


open LinearMap Module Finset
variable {ℓ} [ThePrime ℓ] {E J : Type} [Field E] [UnramCMField E] {O : CoeffRing ℓ}
attribute [local simp] tateTwist cycInv sub_smul funext_iff idOrConjInv eq_neg_iff_add_eq_zero

/-- Let e ≠ 0 and c be a continuous cocycle in O(−e)/ℓ^ν, unramified off ℓ, S, S̄ and zero on
`shaLocalSet`. Then g ↦ c(g) + c(g^c) lies in `evenClasses`. -/
lemma add_conjGal_mem_evenClasses {e S ν c} (he : e ≠ 0) (h :
  c ∈ selmerModule (tateTwist ℓ E O e) (placesDividing E ℓ ∪ .conjClosure S) ∅ _ ⊓ .pi
  (shaLocalSet ℓ E e) ⊥) : c + c ∘ conjGal ∈ evenClasses O S ν e := by
  simp_all [evenClasses, mem_selmerModule_iff, add_add_add_comm _ (_ • _), shaLocalSet, obeying]
  exact h.elim fun ⟨_, u, l⟩ h ↦ ⟨⟨fun _ ⟨_, _, _, b, c⟩ ↦ u _ ⟨_, by aesop, _, b.conjPlace_star,
    c.conjPlace_conjGal⟩, l.add (l.comp_continuous (by fun_prop))⟩, by simp [add_comm], by
    intros; simp [*, h _ ‹_›, h _ _ _ (decompGroup.map cmConj_conjGal_smul ‹_›), ↓val_comap_lt_one]⟩

/-- Assume `IsPrimeTriangle`. Let Z be a module of cocycles of O(−e)/ℓ^ν unramified off ℓ, the
w_j, w̄_j, whose coboundaries are killed by cyc(γ)^{−e} − 1. If b bounds its local loss at ℓ
plus length `shaOdd`, `HasTriangleCost` holds with ℓ^h, b. -/
lemma hasTriangleCost_tateTwist [Fintype J] [LinearOrder J] {ν w τ φ t γ h c} {e : Fin t} {ty : J →o
  _} (tri : IsPrimeTriangle ν w τ φ γ t ty h c) {Z : Submodule O _} (N : Z ≤ selmerModule (tateTwist
  ℓ E O e) (placesDividing E ℓ ∪ .conjClosure (.range w)) ∅ (QuotSpan (ℓ ^ ν : ↑O))) (H : ∀ c ∈ Z,
  ∀ m, (∀ g, c g = (cycInv ℓ E O g ^ e.1 - 1) • m) → ∀ g, (cycInv ℓ E O γ ^ e.1 - 1) • c g = 0) {b}
  (hb : relLength Z (obeying (crysRels (tateTwist ℓ E O e)) _) + length O (shaOdd ℓ E O e ν) ≤ b) :
  HasTriangleCost Z (withConjInv τ) (withConjInv φ) {j | (ty j).1 = e}
  (ℓ ^ h) b := have C {z} k := (mem_selmerModule_iff.1 (@N z k)).1
  have F j := by simpa using
    (tri.isNewPlaces.cycInv_withConjInv O (j, false)).imp_right (smul_quot_eq_zero_of_dvd <| · e)
  ⟨shaLocalSet ℓ E e, fun j hj z k ↦ by
    cases (mem_filter.1 hj).2
    simpa [F, cocycle_apply_inv (C k.1), ← Nat.cast_smul_eq_nsmul O] using
      tri.step O j _ (add_conjGal_mem_evenClasses (ty j).2.ne' ⟨N k.1, k.2⟩), fun S hS a ↦
  have K {z} k := tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero (N (hS k).1) (a z k).1 .rfl
  hb.trans' (add_le_add (relLength_le_of_inj 1 (by simp) fun _ k l g ⟨_, h, a⟩ ↦ by
    let ⟨v, p⟩ := exists_isPlaceOver_of_val_ne_one E NeZero.out h.ne
    let ⟨x, n⟩ := p.exists_smul Gal(Ω/E) v.isPlaceOver_placeOver
    split_ifs at a with i <;> have d := n ▸ conj_mem_decompGroup_smul a.1 <;> simpa [← mul_assoc,
      C k g, a, i, by simpa using mem_obeying.1 l _ ⟨_, ⟨⟨v, p.valuation_natCast_lt_one_iff.1 h⟩,
      rfl⟩, .single ⟨_, d⟩ 1, fun z y ↦ by simp [crysCocycles.apply_eq_zero_of_cyclotomicGp (𝒥 :=
      _) (tateTwist_smul e) y (s := ⟨_, d⟩) (ext (by simp [*])) fun c ↦
      (localChart ..).isWeilPair_zero_iff.2 (n ▸ IsFrob.conj (by tauto) x :)], rfl⟩] using
      C k x⁻¹ (x * g * x⁻¹)) ((relLength_bot _).le.trans' (if n :
    e.1 = 0 then relLength_mono (fun z k ↦ ⟨⟨(hS k).2, by simp [n]⟩,
    K k⟩) bot_le else have A {z} k :=
      add_conjGal_mem_evenClasses (S := ∅) n ⟨selmerModule_mono (@K z k) .rfl, (hS k).2⟩
    (tri.coboundary O ⟨e, by omega⟩).elim fun D L ↦ D.elim fun q t ↦
      relLength_le_of_inj (funLeft _ _ conjGal - 1) (fun z k ↦ ⟨⟨sub_mem ((add_mem_cancel_left
      (hS k).2).1 (by simpa [shaLocalSet, n] using (A k).2.2)) (hS k).2, by simp⟩,
      sub_mem ((add_mem_cancel_left (K k)).1 (selmerModule_mono (A k).1 .rfl)) (K k)⟩) fun
    z k v ↦ funext fun g ↦ by linear_combination (norm := (simp [-funext_iff]; module)) q • H _ (hS
      (S.smul_mem _ (by simp [add_mem, k]))).1 _ ((sub_eq_zero.1 v : _ ∘ _ = z) ▸ L _ (A k) (by
      simpa [cocycle_apply_inv (C (hS k).1), F, Subtype.ext_iff] using (a z k).2)) g + t • z g)))⟩
end

section
/-! Ribet's method with congruent blocks and tied auxiliary primes. In any rank the method gives a
Hecke element, polynomial in the tie parameters, that kills a determinant vanishing on lifts modulo
the ties, and on lifts it has no term below the product of all parameters, whose coefficient has
valuation bounded without the even classes. Fitting-ideal forms of Ribet's method are known for
distinct blocks in any rank and for congruent characters in rank 2. Related work:
Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's method for GL2, 2023;
Bellaïche–Chenevier, Families of Galois representations and Selmer groups, 2009; Urban, Selmer
groups and the Eisenstein–Klingen ideal, 2001.

Crystalline losses above ℓ are affordable. The torsion cocycles that Ribet's method produces in the
blocks of a lift's Galois representation need not reduce from crystalline ones, but local duality
and a case analysis on ℓ bound their total distance from the crystalline condition, over all blocks
and places above ℓ, by an explicit, affordable loss. It is known that torsion crystalline classes
can miss reductions of crystalline ones by a bounded defect that vanishes for small weights. Related
work: Sweeting, Bloch–Kato conjecture for four-dimensional symplectic representations, 2025;
Chang–Diamond, Extensions of rank one (φ,Γ)-modules, 2011; T. Liu, Torsion p-adic Galois
representations and a conjecture of Fontaine, 2007.

This file: Ribet's Hecke element for columns with ties; valuation at the lift within budget. -/

open Module CoeffRing ENNReal Filter Finset Fintype Function Lift Matrix NeZero NumberField
  Polynomial Matrix.Module

attribute [-instance] NormedAlgebra.toAlgebra Subalgebra.isScalarTower_left

attribute [-simp] IsUnit.dvd length_eq_zero

/-- The budget at ℓ per unit of rank: h₂²⁷(cr_ℓ + v_ℓ(X)) + 4f·loss_ℓ, with X the integer of
`exists_length_shaOdd_le` for E and t. -/
noncomputable def rowBudget {P} (D : Data P) ℓ := D.h₂ ^ 27 * (crudeUnit ℓ D + padicValNat ℓ
  (exists_length_shaOdd_le _ D.t _ D.algebraMap_mem_cycloField).choose) + 4 * D.f * loss D ℓ

variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {K Y n r : Type} [Fintype n] [Fintype r]
  {t ν : ℕ} {w} {τ φ : K → AbsGal D} {u : Y → GalRep ℓ D.E n} {O : CoeffRing ℓ}

lemma obeyingCocycles.mem_selmerModule [Fintype Y] {u : Y → AbsGal D →* Matrix n n O} (hc : ∀ x,
  Continuous (u x)) {S} (hS : ∀ g ∈ inertiaAbove Sᶜ, ∀ x, u x g = 1) {ρ : _ →* Matrix r r O} {b c L}
  (h : c ∈ obeyingCocycles u ρ b) [NeZero b] (l : c ∈ obeying L _) : c ∈ selmerModule ρ S L _ := by
  choose k _ p H using exists_graph_subrepresentation u _ h
  refine mem_selmerModule_iff.2 ⟨mem_obeying_cocycleRels.1 h.1, fun g k ↦ congr($(@p ⟨_, H g 0⟩ 0
    (by ext; simp [*])).1.2), l, (IsLocallyConstant.iff_exists_open _).2 fun g ↦ ⟨_, (continuous_pi
    (hc · |>.matrix_map (Ideal.span {b ^ k}).continuous_mkQ)).1 {_} (by simp), rfl, fun h K ↦ ?_⟩⟩
  choose w hw using (Ideal.mk_span_eq_iff_dvd_sub.1 congr($K · · ·))
  exact congr($(@p ⟨_, H h 0⟩ ⟨_, H g (of ∘ w)⟩ (by ext; simp [← hw])).1.2)

/-- Let τ_j, φ_j satisfy `IsNewPlaces` at level ℓ^ν and the u_x be conjugate self-dual
(`IsConjSelfDual`). If `IsTraceIdeal` holds for u, ℓ^ν, τ, φ, it still holds after
adding τ_j^{−c}, φ_j^{−c}, with the same variable for both copies of j. -/
lemma isTraceIdeal_withConjInv (hw : IsNewPlaces ν w τ φ) {S 𝒥 e} (hu : ∀ x, IsConjSelfDual t (u x))
  (h : IsTraceIdeal (S := S) (L := PadicAlgCl ℓ) 𝒥 (u · · |>.1) (ℓ ^ ν : ↑O) τ φ id e) :
  IsTraceIdeal 𝒥 (u · · |>.1) (ℓ ^ ν) (withConjInv τ) (withConjInv φ) (·.1) e :=
  h.imp_right (.imp_right fun k g ↦ (k g).imp_right fun a (j, b) ↦ b.rec (by
  have H h i x : (u x (withConjInv h (j, false) ^ i * g)).1.trace = cycInv ℓ _ O (withConjInv h (j,
    false) ^ i * g) ^ (t - 1) • (u x (h j ^ i * (conjGal g)⁻¹)).1.trace := by
    simpa [idOrConjInv, cycInv, trace_mul_comm _⁻¹, O.1.smul_def] using
      (hu x).trace_conj ((h j)⁻¹ ^ i * conjGal g)
  choose d hd using (hw.cycInv_withConjInv O (j, false)).2
  convert 𝒥.smul_of_tower_mem (cycInv ℓ _ O g ^ (t - 1))
    (sub_mem ((k (conjGal g)⁻¹).2 j) (𝒥.smul_mem ⟨_, h.1 j⟩ (sum_mem fun i _ ↦ 𝒥.smul_of_tower_mem
    (d ((t - 1) * i) * ((X - 1) * e j).coeff i) (k (φ j ^ i * (conjGal g)⁻¹)).1)))
  simp [*, Subalgebra.smul_def, ↓aeval_eq_sum_range, sum_mul, sub_mul, mul_sum, mul_sub,
    eq_add_of_sub_eq' (hd _), sub_sub, add_mul, mul_add, MvPolynomial.smul_eq_C_mul,
    by simpa [hw.cycInv_withConjInv, mul_pow, ← pow_mul'] using And.intro H (H τ <| Bool.toNat ·)]
  ac_rfl) (a j))

variable [Fintype Y] [PadicIso ℓ] {V : AuxPair D.E r n} {c ϑ} (hc : IsApt V c ϑ)

/-- Fix a row of rank r and finitely many `IsLabelledColumn` representations with common jumps,
level and apt labels times (X − 1)^t. For O large, lattices u_x in them, one being
T ⊕ O ⊕ … ⊕ O(1 − t), T a lattice in the row above ℓ: the losses of the blocks, at any moduli,
total ≤ 4rf·loss.

Crystalline losses above ℓ are affordable. -/
lemma sum_blockLoss_le (hc : IsApt V c ϑ) {τ τ' S R} {R' : Y → _} (hT : IsRow D t τ R)
    (hC : ∀ x, IsLabelledColumn V t τ' (twistedLabel V c · * (X - 1) ^ t) S (R' x)) (ϵ :
  Sigma (@RowBlockIndex r t) ≃ n) π : ∀ᶠ O : CoeffRing ℓ in atTop, ∀ T {T₀} (u : Y → _ →* Matrix n n
  O) (M : Option (Fin t) → ℕ), (∀ g, u π g = reindex ϵ ϵ (blockDiagonal' (blockRep T · g))) →
  (∀ x, IsLatticeIn (R' x) (u x)) → IsLatticeIn R T₀ → (∀ v : placesDividing D.E ℓ,
  T.comp (decompGroup _ (placeOver v.1)).subtype = T₀.comp (Subgroup.subtype _)) →
  ∑ i, O.normLength (blockLoss (blockRep T i) u (M i)) ≤ 4 * card r * D.f * loss D ℓ := by
  have he v := (localChart ℓ D.E v).inducesPlace.2
  filter_upwards [Eventually.all (block_defect_le_at_place hT.2 <| he ·)] with O h T _ u M hπ Z Y H
  simp_rw [blockLoss, obeying_crysRels]
  let L H i := matrixLattice ((blockRep (t := t) T i).comp (Subgroup.subtype H))
  let f := .funCongrLeft O O ϵ ≪≫ₗ .piCurry _ fun _ _ ↦ _
  have hf H i g x : f (u π g.1 *ᵥ x) i = (L H i).ρ g (f x i) := by simp +zetaDelta [funext_iff,
    hπ, mulVec_apply_eq_sum, reindex_equiv ϵ, Fintype.sum_sigma, blockDiagonal'_apply', Sigma.curry]
  have hu v x := inClass_of_isLatticeIn v (hC x).1 (hC x) (Z x)
  have S v i :=
    InClass.of_jointly_injective (fun _ ↦ (hu v π).2) (fun () ↦ f.symm ∘ₗ .single _ (L _ ·) i)
    (by simp [f.symm_apply_eq, funext_iff, hf, (Pi.apply_single fun i ↦ (L _ i).ρ ·)]) (by simp)
  grw (transparency := default) [relLength_iInf_le, (map_sum ..).le,
    relLength_obeyingCocycles_le (he _).1
    (hu _ · |>.2) _ (S ..), fun v i ↦ h v ((em (v.1 ∈ placesAboveG D)).imp (·.imp fun k b ↦ by
    cases (v.1.charP_quotient b).eq _ (v.1.charP_quotient v.2)
    use rfl, fun s w ↦ ((exists_inertia_eigenvalues n hc b v.1.isPlaceOver_placeOver
      _).choose_spec.2 _ ((localChart ..).isWeilPair_zero_iff.1 w)).elim fun μ H ↦
      isTameType_of_roots (by grw [H.1, hc.rank_le.1, hT.t_le]) (H.2.1 · · |>.2.2) fun _ _ ↦
      ⟨⟨k, b⟩, fun _ N ↦ ⟨_, (H.2.2 N).1, by simpa [eval_multiset_prod]⟩⟩) (by simp [·,
    funext_iff])) (fun g a this ↦ exists_jump_of_jointly_injective (S v · |>.isPotCrys) (.proj · ∘ₗ
    f.1) (hf _) (by simp [← funext_iff, ← Pi.zero_def]) (surjInv_eq coeffEmb_surjective g ▸
    ((hu v π).1 ..).trans_ne (by simpa))) (Option.rec (H v ▸ inClass_of_isLatticeIn v hT.1 hT Y).1
    fun c _ _ ↦ by rw [hasJumps_of_cyclotomicGp_zpow _ (tateTwist_smul _), finrank_pi]; simp!)
    (finrank_pi _) i (S ..)]
  simp! [L, (he _).index_eq_card_range, ← sum_mul]; simp_rw [Finset.card_eq_sum_ones]; norm_cast
  grw [sum_complexEmbOf_le, hT.t_le.trans (le_mul_of_one_le_left' hT.rank_mem.1)]
  have := D.t_odd.pos.ne'
  simp [Embeddings.card, finrank_eq_two_mul_card_infinitePlace, field]; linarith

/-- Ribet's method. Let u_x be `IsLabelledColumn`, of trace ψ·row + Σ_{e<t} cyc^{−e} with
`SelmerLengthLe` on 𝓧, with places `IsPrimeTriangle`, and S, 𝒥 as in `IsTraceIdeal`, e_j(1) = 1.
Then x ↦ det Σ_g ω_g(u_x(g) − 1), ω from `ribetNormaliser`, satisfies `IsRibetElement` at π with
coefficient d, v(`chosenGroupOrder`³·d) ≤ |r|·`rowBudget`.

Ribet's method with congruent blocks and tied auxiliary primes. -/
lemma ribet_columns (hc : IsApt V c ϑ) {J' ψ Q} (hq : IsAuxTwist (badPlaces D ℓ) Q ψ (crudeUnit ℓ
  D)) [Fintype K] [LinearOrder K] {ty a h} (hh : h ≤ padicValNat ℓ D.chosenGroupOrder) (tri :
  IsPrimeTriangle ν w τ φ a V.rankDiff ty (D.h₂ * h) (D.h₂ ^ 22 * h)) (S : Subalgebra (intQpBar ℓ)
  (Y → MvPolynomial K (PadicAlgCl ℓ))) (hu : ∀ x, IsLabelledColumn V V.rankDiff J'
  (twistedLabel V c · * (X - 1) ^ V.rankDiff) (.conjClosure Q ∪ (Set.range w).conjClosure) (u x) ∧
  ∀ g ∈ inertiaAbove (.conjClosure Q), ((u x g).1 - ψ g • 1) * ((u x g).1 - 1) = 0) {𝓧 : Set Y}
  {J R γ y : 𝓧 → _} {m₀} (hm : ⌊D.r * rowBudget D ℓ⌋₊ < m₀) (hR : ∀ x, IsRow (n := r) D V.rankDiff
  (J x) (R x) ∧ SelmerLengthLe ψ (R x) Q m₀ (γ x) (y x)) (hl' : ∀ (x : 𝓧) g, (u x g).1.trace = ψ g *
  (R x g).1.trace + ∑ e ∈ range V.rankDiff, cycInv ℓ _ _ g ^ e) {𝒥 e} (h𝒥 : IsTraceIdeal (S := S) 𝒥
  (u · · |>.1) (ℓ ^ ν) τ φ id e) (he' : ∀ j, (e j).eval 1 = 1) π θ : ∃ d, IsRibetElement 𝒥 (fun x ↦
  ((ribetNormaliser (γ π) a (y π) (ℓ ^ (m₀ + D.h₂ * h)) θ).linearCombination (intQpBar ℓ) fun g ↦
  (u x g).1 - 1).det) π d ∧ @ellVal ℓ _ (D.chosenGroupOrder ^ 3 * d) ≤ card r * rowBudget D ℓ := by
  obtain ⟨⟨-, hψ, σ, hq⟩, ⟨hJ⟩, ⟨s, hs, hr⟩, ⟨od, -, odd⟩, o, hG, ϵ⟩ := hq, hR π, tri.detect,
    (exists_length_shaOdd_le _ D.t _ D.algebraMap_mem_cycloField).choose_spec, of_pos hc.odd.2.pos,
    ((finite_toSet _).subset (placesDividing_union_subset_badPlaces D ℓ)).sdiff (t := placesDividing
    _ ℓ), (equivOfCardEq (by simp! [V.rank_lt.le]) : Sigma (@RowBlockIndex r V.rankDiff) ≃ n)
  let z := σ ⊕ᵥ fun v : hG.toFinset ↦ v.1.isPlaceOver_placeOver.tameGenerator
  have N : IsNewPlaces 0 (_ ⊕ᵥ _) z 1 :=
    Sum.rec hq.1 (⟨hG.mem_toFinset.1 ·.2 |>.2, map_one _, _, _, rfl⟩)
  have M k {S} h : withConjInv z k ∈ inertiaAbove S := (N k.1).2.2.elim fun _ ⟨a, e⟩ ↦
    idOrConjInv_mem_inertiaAbove a (e ▸ a.tameGenerator.2) h _
  choose O' l hL ζ η hR' R₀ ψ' y' ey hl hψ' e₀ hy c₀ hS using
    ((sum_blockLoss_le hc hJ (hu · |>.1) ϵ π).and (.and (.all (eventually_exists_isLatticeIn <|
    hu · |>.1.continuous)) ((eventually_primitiveRoot (Monoid.exponent
    (ZMod D.cycloConductor)ˣ)).and (.and (.all (e · |>.finite_range_coeff.eventually_all.2 fun a _ ↦
    eventually_mem a.2)) (.all (hR · |>.elim (·.span_and_scalar.and ·))))))).exists
  choose η hε using fun j ↦ (mem_lifts ((e j).map (intQpBar ℓ).subtype)).1 ((mem_map_rangeS
    (algebraMap O' _)).2 (⟨⟨_, η j _ ⟨·, rfl⟩⟩, by simp⟩))
  let T x := twistRep (.id _) (ψ' x) (R₀ x)
  have p1 {g} (h : ψ g = 1) : T π g = R₀ π g := by ext; simp [*, T, twistRep]
  have sp x := Basis.units_smul_span_eq_top (w := (ψ' x).toHomUnits) (hR' x _ (hl x)).1
  let Φ R [CommRing R] := (reindexAlgEquiv R R ϵ).toAlgHom.comp blockDiagonalAlgHom
  have B x (e : Fin V.rankDiff) g : Eq (blockRep (T x) (some e) g) fun _ _ ↦
    cycInv ℓ _ O' g ^ e.1 := funext₂ fun _ _ ↦ ite_eq_left rfl
  choose u' hL hB using fun x ↦ show ∃ v, IsLatticeIn (u x) v ∧ ∀ h g, v g = Φ _
    (blockRep (T ⟨x, h⟩) · g) from if h : x ∈ 𝓧 then ⟨(Φ _).1.1.comp (.pi _), .imp (fun Z c g ↦ by
    simp [c, mul_assoc, Φ, ← submatrix_map, blockDiagonal'_map]; rfl)
    ((hu x).1.nondeg.exists_conj_of_trace_eq
    (.pi (O'.1.val.mapMatrix.1.1.comp <| blockRep (T ⟨x, h⟩) ·)) (Φ _) (fun y _ H ↦ by
    ext (_ | e) a b
    simpa [mul_apply, single_apply, ite_and] using congrFun₂ (LinearMap.congr_fun
     (LinearMap.ext_on_range (g := 0) (f := .mulLeftRight _ (y _, y _) ∘ₗ (Algebra.linearMap O'
     _).mapMatrix) (sp _) (congr($(H ·) _))) (.single b a 1)) a b
    with_unfolding_all simpa using! (sum_singleton _ a).symm.trans congr($(H 1) _ a a)) fun g ↦ by
    simp [↓hl' ⟨x, h⟩, ↓← (hl _).trace_eq, ← hψ' ⟨x, h⟩, Φ, trace, sum_range, mul_sum, reindex_equiv
      ϵ, Fintype.sum_sigma, B, cycInv]; simp!; rfl), fun _ _ ↦ rfl⟩ else (hL x).imp (by tauto)
  choose F I f d tr using (hL · |>.exists_algHom)
  have hC x := (hL x).continuous (hu x).1.continuous
  have U g h x := (hL x).eq_one ((hu x).1.eq_one_of_mem_inertiaAbove g h)
  refine (ribet_first_order (S := ⟨_, (S.2 ⟨·, norm_le_one _⟩)⟩) u' 𝒥 (.trans ⟨(⟨none, ·⟩) ⊕ᵥ (⟨some
    ·, ()⟩), (·.rec (·.rec .inl fun e _ ↦ .inr e)), by rintro ⟨⟩ <;> rfl, by rintro ⟨⟨⟩⟩ <;> rfl⟩ ϵ)
    π T (by simp) (fun x g ↦ (reindex ..).symm_apply_eq.1 (by ext1 ⟨⟩ ⟨⟩ <;>
    simp [hB, Φ, blockDiagonal', B] <;> rfl)) (sp π) e₀ hy (by simp [cycInv, c₀]) out (by
    simpa [IsTraceIdeal, ↓(hL _).charpoly_eq_map, ← f, aeval_algHom_apply (F _), ← map_mul, sub_mul,
      tr, O'.1.smul_def] using isTraceIdeal_withConjInv tri.isNewPlaces (e := η) (hu · |>.1.1.1) (by
      simpa [IsTraceIdeal, hε, ← aeval_map_algebraMap (PadicAlgCl ℓ)] using! h𝒥)) (fun e k ↦ by
    simpa [by simpa [eval_map, he'] using (congr(Polynomial.eval 1 $(hε ·)))]
      using ((tri.isNewPlaces.cycInv_withConjInv ..).2 e).trans (sub_dvd_eval_sub _ 1 (η _))) _
    (by simpa [cycInv] using
    (map_dvd (algebraMap _ O') <| tri.prod_dvd ·)) ⟨(ty ·), ty.2⟩ out (.trans (by
    simp [ribetNormaliser, Finsupp.linearCombination_apply ℕ, Finsupp.sum, f, pow_add, ey,
      O'.1.smul_def]
    rfl) <| d · _) (le_self_add.trans_lt (O'.normLength_mono.reflect_lt ((le_add_self.trans
    ?H).trans_lt (by grw [hJ.rank_mem.2]; simpa using mod_cast Nat.lt_of_floor_lt hm))))
    ((relLength_add_length_inf _ (obeying
    (crysRels (T π)) _)).ge.trans (add_le_add (relLength_mono (fun _ ↦ (·.1.1)) le_rfl)
    (length_mono (T := _ ⊓ _) fun c k ↦ ⟨tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero
    (obeyingCocycles.mem_selmerModule hC U k.1.1.1 k.2) (k.1.1.2 _ ⟨·, rfl⟩) (Set.union_assoc ..).ge
    fun g ⟨v, hv, H⟩ _ ↦ (p1 (hψ.eq_one_of_mem_inertiaAbove g ⟨v, mt .inr hv, H⟩)).trans ((hl
    π).eq_one (hJ.eq_one_of_mem_inertiaAbove g ⟨v, mt (.imp_right nofun) hv, H⟩)), k.1.2⟩))) (o :=
    fun k ↦ ite k.1.isLeft (C (ψ' π (withConjInv z k)) - X) (∑ i ∈ range D.chosenGroupOrder,
    X ^ i)) (by simp [N.cycInv_withConjInv]) (by
    rintro ⟨j | j, b⟩ x <;> apply I x
    simpa [f, ← hψ' π, Algebra.smul_def, ← neg_mul] using! congr(-$((hu x).2 _ (M _ (by simp))))
    have ⟨v, ⟨⟨i, b⟩, l⟩, A, a, s⟩ := @M (.inr j,
      b) (placesAboveG D \ placesDividing _ ℓ) (by simpa using j.2)
    have ⟨μ, _, Z, P⟩ := (exists_inertia_eigenvalues n hc b a V.rankDiff).choose_spec.2 _ s
    convert ((hu x).1.local_conditions v (·.2 (.inr ⟨i, b⟩)) a).1.aeval_eq_zero_of_roots
      (a.valuation_natCast_eq_one_iff.2 l) s (P (hu x).1).1
      (X ^ D.chosenGroupOrder - 1) _ <;> simp [f, geom_sum_mul, eval_multiset_prod]
    exact (Z · · |>.2.2.elim fun d ⟨a, h⟩ ↦ (g_pow_sub_one_dvd_chosenGroupOrder D
      (a.imp_right D.nat_le_of_hasLogBound.trans')).choose_spec
      ▸ by rw [pow_mul, h, one_pow])) (s := s ∪ image (withConjInv τ) univ) fun e Z H ↦ (fun N ↦
    ⟨hasTriangleCost_tateTwist tri N (H · · |>.2.2) (add_le_add (relLength_mono (H · · |>.1) le_rfl)
    (odd ℓ _ ⟨ζ, inferInstance⟩ e (e.2.trans_le hJ.t_le) ν)), fun c k b ↦ hr _ e c
    (tri.isNewPlaces.mem_selmerModule_of_tame_eq_zero (N c k) (by simp [b])) (by simp +contextual
    [b])⟩) fun c k ↦ N.mem_selmerModule_of_tame_eq_zero (obeyingCocycles.mem_selmerModule hC U (H c
    k).1 (by simp [obeying])) (H c k).2.1).elim fun d k ↦ ⟨d, k.1, .trans (by
    grw [ellVal_mul_le, (normLength_addVal d).ge, k.2, card_union_le, card_image_le]) ?H⟩
  rw [← @Nat.cast_le ℝ≥0∞] at hs
  simp [rowBudget, mul_add (_ ^ 27), ellVal_natCast, ne, od, two_mul, mul_two, add_mul, hψ',
    sum_prod_type,
    hψ.apply_idOrConjInv, z, -AddValuation.map_pow, -ENat.natCast_sub, -natCast_sub] at hs hq ⊢
  grw [hS, hJ.rank_mem.2, mul_add (card r : ℝ≥0∞),
    ← le_mul_of_one_le_left' (mod_cast hJ.rank_mem.1),
    hq.2, card_le_of_subset_placesAboveG D (by simp), le_self_add.trans hs, le_add_self.trans hs,
    hh, hJ.t_le, (by simp [crudeUnit] : (padicValNat ℓ _ : ℝ≥0∞) ≤ crudeUnit ℓ D)]
  exact (add_le_add (by gcongr <;> exact_mod_cast D.nat_le_of_hasLogBound) ((l _ u' (·.elim m₀
    fun _ ↦ ν) (hB _ _) hL (hl π) fun v ↦ MonoidHom.ext (p1 <| hψ.eq_one_of_mem_decompGroup v.2
    v.1.isPlaceOver_placeOver ·.2)).trans_eq (by ring)) : ((4 + D.t *
    (2 + 10 * D.f + 6 * D.h₂ ^ 22) + D.h₂ ^ 22 + D.h₂) * _ + D.t * _ + _ : ℝ≥0∞) ≤
    _).trans_eq' (by simp only [sum_option, Data.t]; push_cast; ring1!)
end
