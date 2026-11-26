import Lib.PadicHodge.LongGap
import Lib.PadicHodge.GoodCriterion

section
/-! Part of: Length bound for crystalline classes with few low weights (see
New.Lift.ExponentTheorems).

This file: Colength bound for constants lifting to deep points; cup products vanish on that
submodule. -/

open Int Finset Submodule Lift.KummerChart JumpLattice

namespace Lift.KummerChart.PairingSide

attribute [-instance] NormedAlgebra.toAlgebra

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} (S : PairingSide O) (i :
  Letter)

/-- The images in W(C^♭) ⊗ C of the x in `Lift.KummerChart.PairingSide.deepElements` i c that lie at
the letter i with exponents t − u at E and −u at φ^a E, a ≥ 1. -/
noncomputable def deepConstants t c :=
  (locKisinPart (withExponents i (raisedAtE t)) ⊓ S.deepElements i c).map S.projTrivLoc

attribute [local grind =] stepBack_zero

variable {S : PairingSide O} {i : Letter} {c : ℕ → ℤ → ℤ} (c' : ℕ → ℤ → ℤ) (hk : IsUnramified)
  (hp : 5 ≤ p) {a η W : ℕ} {b n r : _ → ℕ} {ε : _ → _} (ha : ∀ i, b i + W + η ≤ (p - 3) * a) (hb :
  ∀ i, 6 * (a + η + W) < b i) (hs : ∀ i, NoMultipleNear p (6 * (a + η + W)) (b i)) (hU : ∀ i,
  IsInJumpWindow η (ε i) (b i) W (S.U i)) (hn : ∀ i, ∑ u ∈ Icc (-↑η) ↑η,
  k.f * S.jumpMultiplicity i u ≤ n i) (hr : ∀ i, ∑ u ∈ S.U i, k.f * S.jumpMultiplicity i u ≤ r i)

include hk hn hr in
/-- Unramified chart: raising the depth from c ≥ −u to c' at φ^a E only (c'_a antitone, no
multiple of p in any (c_0(v), c_0(v)+p^a), cost ≤ A per line, plus B if |u| ≤ η) shrinks
`Lift.KummerChart.PairingSide.deepConstants` by length ≤ A·r + B·n. -/
lemma relLength_deepConstants_le {i'} a A B (f : i.stepBack a = i') (ha : ∀ v, ∀ n ∈ Ioo (c 0 v) (c
  0 v + p ^ a), ¬↑p ∣ n) (hc : ∀ b, ∀ u ∈ S.U (i.stepBack b), -u ≤ c b u ∧ (b ≠ a → c' b u ≤ c b u))
  (ho : AntitoneOn (c' a) (S.U i')) (hA : ∀ u ∈ S.U i', ∑ n ∈ Ico (c a u) (c' a u), cost a n ≤ A +
  ite (u ∈ Icc (-↑η) ↑η) B 0) : relLength (S.deepConstants i 0 c) (S.deepConstants i 0 c') ≤
  ↑(A * r i' + B * n i') := by
  replace hA := sum_le_sum fun u m ↦ mul_le_mul_left (hA u m) (k.f * S.jumpMultiplicity i' u)
  simp [add_mul, -mem_Icc, sum_mul, sum_sigma'] at hA
  grw [← mul_sum, hr, ← mul_sum, inter_subset_right, hn] at hA
  grw [← hA]
  clear hA
  induction' E : (S.U i').sigma fun u ↦ Ico (c a u) (c' a u) using eraseInduction with I ih
    generalizing c
  subst E
  obtain w | ⟨u, hu⟩ := by
    simpa using not_or_of_imp (exists_min_image {v ∈ S.U i' | c a v < c' a v} id)
  exact (relLength_eq_zero.2 (map_mono fun _ ↦
    And.imp id (.imp id (mem_withExponents_of_le <| · ·)))).trans_le bot_le
  have M : locKisinPart (S.kerWithExponents i c) ≤ locKisinPart
    (S.extLattice.withExponents i (raisedAtE 0)) := fun _ ↦ (mem_withExponents_of_le ·.1)
  grw [← add_sum_erase (a := ⟨u, c a u⟩), relLength_trans _ (ih (c := raiseExponent c a u) ..)]
  grw [deepConstants, deepConstants, ← relLength_comap, comap_map_eq, relLength_mono le_rfl
    (sup_le_sup_left (fun _ ↦ (·.2) : locKisinPart (S.kerWithExponents i c) ≤ _) _),
    relLength_le_of_relations] <;> intro x hx
  refine (S.exists_reaches_deep {⟨a, c a u⟩}).rec fun A ⟨R, d⟩ ↦
    mem_sup.2 ⟨_, ⟨R.mem_of_stable M hx.1 hx.2, d hx.2 _ ?_⟩, _, neg_mem (R hx.2), by simp⟩
  swap
  choose x' n m b e using (mem_sup.1 <| hx · |>.2)
  choose y d q B using (exists_inclKer_eq_of_projTriv_eq_zero <| b ·)
  peel 3 exists_comb_of_jumpMultiplicity_le c hk .refl a i f
    (by clear * - hu ho; grind [AntitoneOn]) (⟨_, B · (m _).2⟩) d with b t
  obtain ⟨w, m, z, o, s⟩ := mem_sup.1 t
  have t := sum_smul_mem (t := univ) _ b fun l _ ↦ (hx l).1
  have m : ⟨_, S.inclKer.wittMap_mem_kisinLoc w.2⟩ ∈ locKisinPart (S.kerWithExponents i _) :=
    ⟨S.inclKer.map_mem_withExponents le_rfl m, by simp⟩
  have e : _ ∈ S.deepElements i (raiseExponent c a u) :=
    ⟨sub_mem (smul_mem _ ↑p t.2.1) (kerWithExponents_le_deepElements m).1, by
    simpa -implicitDefEqProofs [eq_sub_of_add_eq' s, smul_sum, smul_comm _ (b _), ← e, q, add_sub]
      using (invariantsMod _).add_mem (sum_smul_mem _ b fun l _ ↦
      (n l).2.2) (smul_sub_mem_withExponents (S.inclKer.map_mem_withExponents le_rfl o))⟩
  -- an operator of cost `0` moves `E M` into `E ^ p ^ a M ⊆ p M + M'`: apply it to `x`
  obtain ⟨A, R, d⟩ :=
    S.exists_reaches_deep (.image (.mk 0) ((S.U i).biUnion fun v ↦ Ioo (c 0 v) (c 0 v + p ^ a)))
  rw [sum_eq_zero] at R
  obtain ⟨y, z⟩ := R.mem_of_stable le_rfl m (kerWithExponents_le_deepElements m)
  have m₂ := frobEUnit_zpow_mem_withExponents (c' := c) 0 (-p ^ a)
    (mem_withExponents_of_deep y (d (kerWithExponents_le_deepElements m) (fun b v ↦ c b v +
    raisedAtE (p ^ a) b 0) ?_).2) fun _ v _ ↦ by clear * - ha; grind [ha v 0, dvd_zero]
  obtain ⟨r, f⟩ : ↑p ∣ k.frobE 0 ^ p ^ a - k.frobE a := by simpa [k.dvd_iff_coe_dvd, frobE_eq, hk.1,
    phi_pow_smul_z, ← sub_sub, dvd_sub_left] using sub_dvd_pow_sub_pow (k.z + p) k.z _
  have n := (locKisinPart (S.kerWithExponents i c)).sub_mem (x :=
    r • ⟨_, frobEUnit_zpow_smul_mem_kisinLoc.2 (A _).2⟩) ⟨smul_mem _ r.1 m₂, by
    simp [by simpa using z]⟩ (R t.2)
  refine mem_sup.2 ⟨_, ⟨sub_mem t.1 (M n), (sub_mem t.2 (kerWithExponents_le_deepElements
    n)).imp_right fun m g ↦ mem_withExponents_of_smul not_frobE_dvd_p (m g).1.1 ?_⟩, _, n, by simp⟩
  convert (invariantsMod _).add_mem (R.mem_of_stable kerWithExponents_le_deepElements e e).2
    (smul_sub_mem_withExponents (frobEUnit_zpow_mem_withExponents a 1 m₂)) g
  simp [S_smul, ← sub_eq_iff_comm.1 f, ← frobEUnit_pow_smul, ← zpow_natCast (k.frobEUnit 0),
    sub_smul, mul_smul, smul_sub, smul_comm g, Nat.cast_smul_eq_nsmul, -map_smul]
  abel
  all_goals clear * - hu ha hc hk; cases a <;> grind [cost_le_of_isUnramified]

include hk hp ha hb hs hU hn hr

/-- Unramified chart, p ≥ 5, jumps in the windows, p away from 0 and ±b_i: the constants at i
lifting to points of `kisinLoc` of the stated sign-dependent depth have colength ≤ (2a+1)n_i +
3(W+1)r_{i−1} + 6a·n_{i−1}; n, r bound f times the low and total jump counts. -/
lemma exists_relLength_deepConstants_le i : relLength (S.constantAt i).range
  (S.deepConstants i 0 (if ε i = 1 then raisedAtE (2 * a + η) else fun l u ↦
  if l = 1 then W + 1 - u + if |u| ≤ η then 2 * a else 0 else if l = 0 then b i + W + 2 * a else
  -u)) ≤ ↑((2 * a + 1) * n i + (3 * (W + 1) * r (i.stepBack 1) + 6 * a * n (i.stepBack 1))) := by
  have U (n : ℕ) : ∑ m ∈ Ico (0 : ℤ) (n + 1), cost 0 m = padicValNat p n.factorial := by
    induction n <;> simp_all [↓← insert_Ico_right_eq_Ico_add_one, add_nonneg, cost, IsUnramified,
      Nat.factorial, padicValNat.mul]; rfl
  have h₁ : ∀ t, -↑η ≤ t → t ≤ 0 → relLength (S.constantAt i).range (S.deepConstants i t
    (raisedAtE (2 * a + η))) ≤ ↑(a * ∑ u ∈ Ico (-↑η) t, k.f * S.jumpMultiplicity i u) := by
    have X s d m H : p ^ s • S.constantAt i d ∈ S.deepConstants i m (raisedAtE (2 * a + η)) :=
      (pointsOver_nonempty_of_noMultipleNear
      (pointsOver_nonempty_of_killsCokernel (killsCokernel_of_isUnramified
      s (a - s) (by grw [← le_add_tsub]; grind) hk hp) d) (hs i) _ (by grind)).rec fun x ⟨a, b, c,
      d⟩ ↦ ⟨⟨x, a⟩, ⟨mem_withExponents_of_le c H, by simp [b, nsmul_mem], d⟩, by simp [b, hk.2]⟩
    refine Int.leInduction (fun _ ↦ by simpa [IsConcreteLE.le_iff]
      using (X 0 · _ (by grind))) fun t ht ih h₀ ↦ ?_
    rw [← sum_Ico_add_eq_sum_Ico_add_one ht, mul_add]
    refine relLength_trans (ih (by lia))
      ((relLength_comap ..).ge.trans (relLength_le_of_relations _ (fun x ⟨_, ⟨d, e⟩, _⟩ ↦
      by simpa [e] using X a d _ (by clear * - h₀; simp; grind)) fun x l ↦ ?_))
    peel 3 exists_comb_of_jumpMultiplicity_le _ hk (sum_le_sum fun _ _ ↦
      jump_extension_le _ (by omega)) 0 i rfl (by simp [raisedAtE]) x (l · |>.1.1) with b m
    rw [sup_of_le_right fun _ e ↦ mem_withExponents_of_le e (by clear * -; grind)] at m
    exact ⟨_, (sum_smul_mem _ b fun j _ ↦ (l j).1.2).rec fun x s ↦
      ⟨mem_withExponents_of_le (mem_withExponents_of_deep m s) (by clear * - h₀; grind), x, s⟩, rfl⟩
  specialize h₁ 0 (by lia) le_rfl
  grw [Ico_subset_Icc_self, η.cast_nonneg, hn] at h₁
  split
  exact h₁.trans (mod_cast by lia)
  obtain ⟨q, h₀, -⟩ := existsUnique_add_zsmul_mem_Ico (natCast_pos.2 p.pos_of_neZero) 0
    (b i + W + 2 * a)
  simp [IsInJumpWindow] at hU h₀
  refine relLength_trans ((relLength_trans h₁ (relLength_deepConstants_le (fun l u ↦
    raisedAtE (q * p + u) l u) hk hn hr 0 0 (a + 1)
    rfl ?_ ?_ ?_ fun u hu ↦ ?_)).trans (mod_cast ?_)) (relLength_deepConstants_le _ hk hn hr _ _ _
    rfl (fun _ n x ↦ (not_dvd_iff_lt_mul_succ _ ?_).2 ⟨q, ?_⟩) ?_ ?_ fun u hu ↦ (sum_le_card_nsmul _
    _ _ fun y e ↦ cost_le_of_isUnramified hk (hs (i.stepBack 1) y ?_)).trans ?_) <;> clear h₁
  any_goals grind [card_Ico, AntitoneOn]
  split
  exact (sum_le_sum_of_subset (by grind)).trans ((U (q * p).toNat).trans_le
    (le_of_mul_le_mul_left (by rw [sub_one_mul_padicValNat_factorial]; grind [tsub_mul]) (by lia)))
  exact sum_nonpos fun y e ↦ cost_le_of_isUnramified hk fun d ↦ hs i y (by
    grind [le_of_dvd (by grind) ((dvd_mul_left _ q).sub d)]) d

/-- Few low jumps (unramified chart, p ≥ 5, window and gap hypotheses; n_i, r_i bound f times
the low, all jumps at i): on a ℤ_p-submodule of C of colength ≤ 11Σ_i(n_i(a+1) + r_i(W+1)),
α(d) ∪-pairs to a coboundary with every α'(c) of paired sides with opposite windows. -/
lemma exists_scaledCupBounds_few_low_jumps (hη : 1 ≤ η) : ∃ V : Submodule ℤ_[p] _, relLength ⊤ V ≤
  ↑(11 * ∑ i, (n i * (a + 1) + r i * (W + 1))) ∧ ∀ T (P : SidePairing T S) c, (∀ i,
  IsInJumpWindow η (-ε i) (b i) W (T.U i)) → ∀ d ∈ V, P.ScaledCupBounds 0 c d := by
  refine ⟨_, (relLength_iInf_le ..).trans ((sum_le_sum fun i _ ↦ (relLength_comap ..).trans_le
    (map_top (S.constantAt i) ▸ exists_relLength_deepConstants_le hk hp ha hb hs hU hn hr
    i :)).trans (mod_cast by simp [← mul_sum, ← sum_mul, Equiv.sum_comp]; lia)), fun _ P c V d
    h ↦ P.scaledCupBounds_of_points_at_cuts (e' := 0) ⊤ (ε · = 1) 1 (by simp; tauto) (fun i _ ↦
    ((mem_iInf _).1 h i).rec fun x ⟨⟨s, _, t⟩, e⟩ ↦ ⟨⟨_, 0, pointsOver_nonempty_of_noMultipleNear
    (pointsOver_nonempty_of_killsCokernel (killsCokernel_of_isUnramified 0 a ?_ hk hp) c) (hs i)
    (raisedAtE (2 * a + η)) ?_, ⟨⟩, ?x⟩, ⟨_, 1, ⟨_, x.2, by simpa, mem_withExponents_of_deep
    s t, t⟩, ⟨⟩, ?y⟩, pointsOver_nonempty_of_noMultipleNear (pointsOver_nonempty_of_killsCokernel
    (killsCokernel_of_isUnramified 0 a ?_ hk hp) 1) (hs i) (raisedAtE a) ?_, ?_⟩) (by simp [hk.2])⟩
  case x | y => rintro (_ | _ | _) u _ v _ <;> obtain ⟨w, x, _, _, e | e⟩ := V _ _ ‹_›, hU _ _
                  ‹_›, hb (k.letterFrob.symm i), hb i, units_eq_one_or (ε i) <;> simp [e, raisedAtE,
    stdExponent, abs_le, ite_apply] at w x ⊢ <;> omega
  all_goals clear * - ha hb hU V hη; grind (splits := 15) [mem_image₂, Antitone]
end Lift.KummerChart.PairingSide
end

section
/-! Rank-free exponents for crystalline classes at large weights. For crystalline lattices with
weights in short windows near 0 and near large weights (no small negative weight, two sizes, or
sparse large weights), an explicit power of p (ℓ in the Selmer bound),
independent of the rank, makes crystalline classes
cup to zero with those of congruent dual lattices, which bounds the loss above ℓ in the Selmer
bound. The question, the case of small weights and a rank-free factorial torsion bound by Sen
operators are known. Related work: Gao–Liu, Integral filtered Sen theory and applications, 2024;
Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015; Y. Min, Congruences of first
syntomic cohomology groups, 2026.

Part of: Tame types: exponent independent of the ramification index (see New.Lift.ExponentTheorems).

This file: Polynomial in tame generator kills cokernel of Kisin modules independently of
ramification index. Kummer chart of a tame extension of Q_p with a generator of tame inertia.
Rank-free exponents killing cup products for two sizes and sparse thick letters. -/

namespace Lift

open KummerChart JumpLattice WittVector Submodule FrobGroup Module Finset Polynomial LinearMap
  PairingSide algebraMap
variable {p : outParam ℕ} [ThePrime p] (Γ : outParam (GroupOverGp p))

/-- A tame Kummer chart: Γ' is normal, p ∤ e, j(Γ') fixes some ϖ with ϖ^e = p, and some s in
inertia has s^k z = ξ^k z, ξ ∈ Λ of order e modulo p. -/
class TameChart extends KummerChart Γ where
  (zetaE : WittFq f) (tameGen : Γ) primitive : IsPrimitiveRoot (zetaE.coeff 0) e
  tameGen_pow_smul_z k : toGp (tameGen ^ k) • chart.z.1 = ↑(zetaE ^ k) * chart.z
  (isWeilPair_tameGen : IsWeilPair (toGp tameGen) 0) fixesLambda_tameGen_pow k :
    FixesLambda f (toGp (tameGen ^ k))
  (ϖ) apply_varpi (g : Γ') : toGp g.1 ϖ = ϖ
  (varpi_pow_eq : ϖ ^ e = p) (tame : ¬p ∣ e) [normal : Γ'.Normal]

namespace TameChart

variable [Γ] {d : TameChart Γ} {O} {L : d.JumpLattice O} {n m : ℕ} {q : ℤ_[p][X]} {S :
  PairingSide O} (hK : IsKilledBy S.ρ d.tameGen 0 (q.map (algebraMap _ O)))

/-- For a tame chart and q = ∑ a_k X^k in Z_p[X]: if q(β_{s,0}) = 0 on B ⊗ L (β = `linearFrob`,
s = `tameGen`), then ∑ a_k s^k
maps the Kisin module N into z·M, with M = `Lift.KummerChart.JumpLattice.kisinAinf`. -/
lemma exists_z_smul_eq_sum_tameGen (r : aeval (linearFrob L.ρ d.tameGen 0) q = 0) {x} (hx : x ∈ L.kisinModule) :
    ∃ y ∈ L.kisinAinf, d.z.1 • y = ∑ k ∈ range (q.natDegree + 1), q.coeff k • inr (d.tameGen ^ k) • x :=
    have n g := (d.normal.1 · · g)
    frame_theorem.1.2.2.2.elim fun u v ↦ v _ d.z_dvd_of_dvd_E_pow_mul _ (by
    simp [↓sum_mem, ↓smul_of_tower_mem, ↓smul_mem_kisinAinf (n _) hx.1]) fun μ ⟨hl, l, E⟩ ↦ by
  let Λ g := (DistribSMul.toLinearMap _ _ (toGp g)⁻¹ ∘ₗ l ∘ₗ overZp L.ρ g).liftBaseChange Bcris
  have A g g' y : Λ g' (tensorAction _ (toGp g) (L.ρ g) y) = toGp g • Λ (g' * g) y := by
    clear * -; induction y <;> simp_all [Λ, tensorAction, mul_smul]
  have S : ∑ k ∈ _, q.coeff k • Λ _ = 0 := ext_on L.inClass.isPotCrys fun y b ↦ by
    simpa [← linearFrob_pow L.inClass.isPotCrys d.isWeilPair_tameGen, fun k ↦ linearFrob_apply (m := 0) L.inClass.isPotCrys (d.isWeilPair_tameGen.pow k) b ▸
      (A _ 1 _).trans ((d.isWeilPair_tameGen.pow k).smul_eq_of_fixed_nearOne (.mp b (d.nearOne_le fun g b ↦ .trans (by
      rw [A]; congr 2 with _
      simpa [Λ, E, mul_smul, eq_inv_smul_iff, -map_pow] using (conjForm_mem_forms (n _) hl _ g).symm)
      (congrArg _ b)))), aeval_eq_sum_range] using congr(Λ 1 ($r y))
  simpa [smul_sub, smul_comm (q.coeff _), ← smul_sum, by
    simpa using apply_eq_of_mem_fracSpan (∑ k ∈ _, q.coeff k • conjForm μ (d.tameGen ^ k)) 0 (by ext; simpa [basisValues, Λ, E, smul]
                                   using congr(($S (1 ⊗ₜ _) : BdR))) (kisinAinf_le_fracSpan hx.1)] using! sum_mem (t := range
    q.natDegree.succ) fun k _ ↦ smul_of_tower_mem _ (q.coeff k) (pow_smul_gal_sub_mem_span_of_dvd (d.z_dvd_sub (d.fixesLambda_tameGen_pow k))
    (u _ ⟨conjForm_mem_forms (n (d.tameGen ^ k)) hl, (liftBaseChangeEquiv _).2 (Λ (d.tameGen ^ k)), by simp [Λ, E]⟩ _ hx))

include hK

/-- Tame chart. If the polynomial q over Z_p kills (s, 0) on Y, then q·(X − 1) evaluated at
β_{s,0} vanishes on B ⊗ Ỹ, for the extension Ỹ of the trivial lattice C by Y. -/
lemma aeval_linearFrob_extLattice_eq_zero :
  aeval (linearFrob S.extLattice.ρ d.tameGen 0) (q * (X - 1)) = 0 := LinearMap.ext fun y ↦ by
  obtain ⟨x, e⟩ := (lTensor_exact _ .inl_snd snd_surjective (_ - y)).1 (by
    simpa [IsCrystalline.linearFrob_eq_one, isAdmissible_of_cyclotomicGp_zpow 0,
      isWeilPair_tameGen] using! baseChange_linearFrob S.extLattice.inClass.isPotCrys
      d.isWeilPair_tameGen S.trivLattice.inClass.isPotCrys _ (by simp [extensionRep]) y)
  simpa [← e, eval₂_map, coefEnd, aeval_def, q.eval₂_eq_sum_range, End.pow_apply,
  Function.Semiconj.iterate_right
    (baseChange_linearFrob hK.1 d.isWeilPair_tameGen S.extLattice.inClass.isPotCrys (inl ..)
  (by simp [extensionRep])) _ _] using! congr((inl _ _ S.C).baseChange _ ($(hK.2) x))

/-- Tame chart; S a side with jumps ≤ n, and a monic q over Z_p kills (s, 0) on Y. If e ≤ p^m, m(deg
q + 1) ≤ κ and n + κ + 2 < p, then p^κ kills the cokernel
(`Lift.KummerChart.PairingSide.KillsCokernel`) at every letter. -/
lemma killsCokernel_of_isKilledBy (hn : ∀ i, ∀ u ∈ S.U i, u ≤ n) (hq : q.Monic) (hm : d.e ≤
  p ^ m) {κ i} (hp : n + κ + 2 < p) (hc : m * (q.natDegree + 1) ≤ κ) : S.KillsCokernel i κ 0 := by
  obtain ⟨⟨ν, h₀, hν⟩, M⟩ := exists_z_pow_mem_liftIdeal hn κ.succ, hq.mul (monic_X_sub_C 1)
  replace hν : ν < d.e := by nlinarith [NeZero.pos d.e]
  set Q := q * _
  replace h₀ := smul_mem _
    (p.cast ^ (m * #{k ∈ Ico ν.succ d.e | (aeval (d.zetaE ^ k) Q).coeff 0 = 0})) (h₀ i)
  induction' ν with n ih
  · apply liftIdeal_le_of_p_pow_mem <;> simpa using mem_liftIdeal_zero_of_mem_one _ _ le_rfl
      (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀) (by grw [← card_image_iff.2
      (d.primitive.injOn_pow.mono (by grind)), card_le_degree_of_subset_roots (p := Q.map _)
      (forall_mem_image.2 (by
      simp [aeval_def, hom_eval₂, eval_map, ← WittVector.constantCoeff_apply, map_monic_ne_zero M]
      tauto)), natDegree_map_le, natDegree_mul_le, natDegree_X_sub_C, hc])
  apply ih hν.le
  rw [card_filter, sum_eq_sum_Ico_succ_bot hν] at *
  split
  · exact mem_liftIdeal_zero_of_mem_one _ _ (by lia) (p_pow_mul_z_pow_mem_liftIdeal_iff.2 h₀)
      (by grind [padicValNat_factorial_mul, padicValNat.mul,
      Nat.log_lt_of_lt_pow (by omega) (hν.trans_le hm), Nat.factorial, padicValNat_le_nat_log])
  obtain ⟨u, K⟩ := S.exists_lift_of_mem_liftIdeal (f := p ^ _ * d.z ^ _) h₀
  obtain ⟨w, t, rfl⟩ := d.exists_z_dvd_sub_const u
  refine (smul_mem_iff_of_isUnit _ ((isUnit_of_coeff_zero_ne_zero _ ‹_›).map (algebraMap ..))).1
    (mem_liftIdeal_iff.2 ⟨Q.sum fun k a ↦ a • toGp (d.tameGen ^ k) • t.1 * d.zetaE ^ k, fun c ↦
    (K _ (constantAt_mem_locLetterPart c)).rec fun x ⟨m, f⟩ ↦
    have ⟨X, v, b⟩ := exists_z_smul_eq_sum_tameGen (q := Q) (aeval_linearFrob_extLattice_eq_zero hK)
      ⟨frobKisinAinf_zero.le (mem_withExponents_stdExponent_iff.1 m.2).1, m.1.2⟩
    ⟨_, letterProj_mem_withExponents (frobKisinAinf_zero.ge v),
      (isUnit_WittCFlat_of_not_p_dvd d.not_p_dvd_z).smul_left_cancel.1 ?_⟩⟩)
  linear_combination (norm := simp [f, -map_pow, tameGen_pow_smul_z, fixesLambda_tameGen_pow, smul,
    smul_letterProj (m := inr _) (fixesLambda_tameGen_pow ..),
    aeval_eq_sum_range, mem_letterPart_iff_letterProj.1 letterProj_mem_letterPart, sum_over_range,
    smul_sub, smul_sum, sum_mul, sub_smul, constantAt, ← sum_sub_distrib, sub_add_eq_sub_sub_swap,
    ← sum_add_distrib, frobGroup_smul_smul, sum_smul]) congr(letterProj i (S.projTriv.wittMap $b) -
    $(Q.eval_eq_sum_range 1 ▸ eval_mul_X_sub_C _) • p ^ κ.succ • (w : Ainf) • S.constantAt i c)
  exact sum_eq_zero fun _ _ ↦ by module

end TameChart

end Lift

/-- If j: Γ → G_p is surjective, e divides p^f − 1 and p does not divide f, then there is a tame
Kummer chart `Lift.TameChart` for j with ramification index e. -/
lemma Lift.exists_tameChart {p e} [hp : ThePrime p] [Γ : GroupOverGp p] (hj : Function.Surjective
  Γ.overGp.toGp) (f : ℕ+) (hf : ¬p ∣ f) (he : e ∣ p ^ f.val - 1) : ∃ d : TameChart Γ, d.e = e := by
  obtain n := @not_dvd_pow_sub_one p _ f, NeZero.mk (ne_zero_of_dvd_ne_zero NeZero.out he)
  obtain ⟨⟨ϖ, hϖ⟩, a, Z⟩ := IsSepClosed.exists_pow_nat_eq (p : PadicAlgCl p) e,
    (HasEnoughRootsOfUnity.of_dvd (flatFq f) he).1
  obtain ⟨c, rfl, _, _, ⟨⟨⟩⟩⟩ := (@exists_chart_of_pow_mul_eq_neg p _ f ⟨ϖ, by
    simp [le_of_pow_le_pow_left₀ (NeZero.ne e), ← norm_pow, *, norm_p_lt_one.le]⟩ e (-1)
    (Subtype.ext (by simp [PadicComplex.coe_eq, ← map_pow, *]))).choose_spec.2 (-1) (by simp)
  set N := _ - 1
  obtain ⟨T, q, K⟩ := (hj.exists.1 <| exists_smul_teichmuller_eq _
    (isLocalGalois_padic.exists_inertia_smul_eq_of_pow_eq isUniformiser_ell) c.varpiFlat · c.e (by
    simp [PadicComplex.coe_eq, ← map_pow, *]) ·), (he.rec (by simp_all [pow_mul, div_pow,
    ← map_pow]) : ∀ g : Gp p, (g ϖ / ϖ) ^ N = 1), fun {g} ↦ by simpa using (@cycCharMod_eq_iff
    (Gp p) (PadicAlgCl p) _ _ _ N g _ _ _ 1), (fixes_roots_iff_fixesLambda · |>.1 <|
    apply_eq_self_of_mem_inertiaGroup n ·), ne_zero_pow NeZero.out (hϖ.trans_ne NeZero.out)
  let U : OpenSubgroup _ :=
    ⟨(cycCharMod _ N).ker, isOpen_ker_cycCharMod.1⟩ ⊓ ⟨_, isLocalGalois_padic.1.6 ϖ⟩
  have M {g} : g ∈ U ↔ c.FixesThetaZ g :=
    (K.trans (fixes_roots_iff_fixesLambda g)).and (by simp [*, c.z_eq_teichmuller, Subtype.ext_iff])
  have Pe {g} h : g ^ N ∈ U := ⟨pow_mem h _, by
    simp [*, @Function.Commute.iterate_eq_of_map_eq _ g (g ϖ / ϖ * ·) fun _ ↦ by aesop]⟩
  have : U.Normal := ⟨fun n c g ↦ by have := K.1 c.1 _ (q g⁻¹); simp_all [U, -K]⟩
  exact (T (a * c.varpiFlat) (by simp [mul_pow, ← map_pow, ← Subring.coe_pow, Z.1])).rec fun s i ↦
    ⟨@.mk _ _
    _ ⟨c, .comap toGp U, U.index_comap_of_surjective hj ▸ .of_dvd_left (IsPGroup.exists_card_dvd_pow
    (⟨1, ·.ind' fun g ↦ by simpa [← QuotientGroup.mk_pow, pow_mul] using Pe (K.2 fun
    _ e ↦ by simp [Function.Commute.iterate_eq_of_map_eq (map_pow g · _) _ (exists_apply_eq_pow n e
    g).choose_spec, pow_right_comm, pow_eq_pow_of_modEq ((Nat.modEq_sub NeZero.one_le).pow _)
    e])⟩)).choose_spec (.pow_left _ (hp.out.coprime_iff_not_dvd.2 (hp.out.not_dvd_mul hf n)).symm),
    by simp [M], hj.forall.2 (⟨⟨·, M.2 ·⟩, rfl⟩), by simpa using ⟨_, U.mem_nhds_one, .rfl⟩, fun l ↦
    by simpa using (T (epsTilt ^ l * c.varpiFlat) (by simp)).imp (by simp_all [↓← theta_smul,
    FixesLambda, c.z_eq_teichmuller, Chart.FixesThetaZ])⟩ _ s Z (by
    induction · <;> simp_all [pow_succ', mul_smul, c.z_eq_teichmuller]
    erw [WittVector.map_teichmuller]; ring!)
    (isWeilPair_zero_iff.2 i.1) (by simp [FixesLambda, *, pow_mem]) ϖ (·.2.2)
    hϖ (n ∘ (.trans · he)) (this.comap _), rfl⟩

namespace Lift.KummerChart.PairingSide

open Finset
variable {p} [j : ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ} {O} {S S' :
  PairingSide O} (h : S.SidePairing S') {cut T : Letter → Prop} [DecidablePred T] {ε :
  Letter → ℤˣ} {s β : Letter → ℕ} {η V W X κ b n J s₀ G e K : ℕ} (hW : V + 4 * η ≤ W) (hU : ∀ i,
  IsInJumpWindow η (-ε i) (β i) V (S.U i) ∧ IsInJumpWindow η (ε i) (β i) V (S'.U i)) (hX :
  (J + 1 + k.differentExp + p.log (2 * b)) * n + k.differentExp * G ≤ X) (hκ : 12 * (J + 1)
  * X < κ) (hδ : k.e * (2 * b) ≤ p ^ (J + 1) * X) (h₈ : 8 * k.e ≤ p ^ (J + 1)) (hη : 1 ≤ η) (hs : W
  ≤ n ∧ W ≤ G ∧ ∀ i, β i + s i + W ≤ 2 * b) (hy : G ≤ (p - 1) * n) (hK : ∀ i, cut i → s i = 0 ∧ (∀ t
  ∈ Icc 1 J, β ((k.letterFrob ^ t) i) + W ≤ G) ∨ s i < β i ∧ IsUnramified ∧ 5 ≤ p ∧ s₀ ≤
  κ + s i) (hz : 5 ≤ p → ∀ i, β i + W ≤ (p - 3) * s₀) (hβ : β = fun i ↦ ite (T i) b G)
include hs hz hy hδ h₈ hX hκ hK

/-- Let the jump sets of S be bounded by β_i + W ≤ 2b − s_i. Under size inequalities, p^κE^{s_i}
kills (`Lift.KummerChart.PairingSide.KillsCokernel`) at each cut letter i, where either s_i = 0 and
β + W ≤ G at i^{p^t}, 1 ≤ t ≤ J, or the chart is unramified, p ≥ 5, s_i < β_i, s₀ ≤ κ + s_i. -/
lemma killsCokernel_at_cut (w : ∀ i n, β i + W ≤ n → ∀ u ∈ S.U i, u ≤ n) i (c : cut i) :
  S.KillsCokernel i κ (s i) := by
  obtain ⟨⟨e, t⟩ | ⟨_, hk, q, e⟩, ⟨a, H, f⟩, hp⟩ :=
    hK i c, exists_z_pow_mem_liftIdeal (w · (2 * b) (by grind)) κ.succ, j.out.one_lt
  have K x (l : p * a ≤ p ^ (J + 1) * x) :
      p ^ (J * X) * k.z.1 ^ (x + n) ∈ S.liftIdeal (p ^ κ.succ) 0 i := by
    clear hδ h₈ hκ hK c e; induction' J with s ih generalizing i x
    exact Ideal.mem_of_dvd _ (by simp_all [pow_dvd_pow, hp.pos, le_add_right]) (H i)
    apply p_pow_mul_z_pow_mem_liftIdeal_iff.1 (mem_liftIdeal_of_mul_E_pow
      (mul_E_pow_mem_liftIdeal_one (ih (by lia) _ (t ·.succ ∘ by simp) _ (by rwa [← mul_assoc]))
      (by tauto)) ⟨?_, ?_⟩) <;> nlinarith [(@sub_one_mul_padicValNat_factorial
      p _ G).trans_le tsub_le_self, p.sub_add_cancel hp.le]
  apply liftIdeal_le_of_p_pow_mem <;> simpa [e] using mem_liftIdeal_zero_of_mem_one _ κ (a := 0)
    bot_le (p_pow_mul_z_pow_mem_liftIdeal_iff.2 (K (2 * X + κ /
    4).succ (by nlinarith [κ.lt_div_mul_add four_pos]))) (by grw [padicValNat_factorial_mul,
    Nat.le_sub_one_of_lt (padicValNat_factorial_lt_of_ne_zero ..)] <;> lia)
  exact killsCokernel_of_isUnramified _ _ (w · _ (by grw [hz q, e])) hk q

include hW hη hU

variable (cut s b n J s₀ G) in
lemma SidePairing.scaledCupBounds_of_cut_windows (hd : ∀ i, s i + W ≤ p * n) (he : 51 * κ ≤ e) (hL :
  ∀ i : k.Letter, ∃ l ∈ Set.Ioc 0 (2 * J + 1), cut (i.stepBack l)) (H : ∀ i l, cut (i.stepBack l) →
  (∀ a ∈ Set.Ioo 0 l, ¬cut (i.stepBack a)) → ∃ t, (∀ a < l, ε (i.stepBack a) = ε (i.stepBack t) ∨
  β (i.stepBack a) + V ≤ η) ∨ k.IsUnramified ∧ 5 ≤ p ∧ s (i.stepBack l) = 0 ∧
  t + (J + 1) = l ∧ (s i = 0 ∨ t = 0) ∧ s₀ + G * ∑ a ∈ range (J + 1), p ^ a < β (i.stepBack t) ∧
  ∀ a < l, a ≠ t → (ε (i.stepBack a) ≠ ε (i.stepBack t) ∨ β (i.stepBack a) + V ≤ η) ∧
  (t < a → β (i.stepBack a) + W ≤ G)) c c' : h.ScaledCupBounds e c c' := by
  let A a := ite (a ≤ 2 * J) η 0
  choose l hl hn using (hL · |> Nat.findX |>.exists_of_subtype)
  choose t hc using (H · _ (hl _).2 (by grind))
  let R ρ i a u := ite (ε (.stepBack i (t i)) = ρ) (stdExponent (l i) a u) (-u - A a) ⊔ (-u - A a)
  have pt {T T' : PairingSide O} ρ {σ} (hU : ∀ i, IsInJumpWindow η (ε i / -ρ) (β i) V (T.U i) ∧
      IsInJumpWindow η (ε i / ρ) (β i) V (T'.U i)) {c i} (hi : cut i) : T.HasDeepPoint T' c i
    (25 * κ) cut (l i) (R ρ) (R σ) (raisedAtE <| -s ·) (ε (i.stepBack (t i)) = ρ) := by
    obtain ⟨⟨hL, hl⟩, hc, ht, h₀, q, z⟩ := hl i, hc i, hK i hi, (hK i hi).imp (·.1) (·.2.1.2.2),
      (show _ ≤ R σ · · · from le_sup_right), stepBack_zero i
    generalize R σ = w at *; unfold HasDeepPoint R; generalize l i = l, t i = t at *
    simp [IsInJumpWindow, div_eq_one, ← Int.units_ne_iff_eq_neg] at hU
    have kl := T.killsCokernel_at_cut hX hκ hδ h₈ hs hy hK hz ?_
    let o a u := raisedAtE (s i) a u + A (a / 2)
    obtain ⟨⟨_, hx⟩, ⟨hi, hk, hp, hy, rfl, ht, he, hc⟩ | ⟨hl, hc⟩⟩ :=
      pointsOver_nonempty_of_killsCokernel (kl i hi) c,
      (em (ε (i.stepBack t) = ρ ∧ ¬_)).imp (·.imp_right hc.resolve_left) (And.intro (z ▸ hi))
    have y a : (i.stepBack t).stepBack a = i.stepBack (t + a) := by simp [pow_add]
    have hx := phi_pow_smul_mem_pointsOver (pointsOver_nonempty_of_long_gap J.succ_pos hk (y _ ▸
      hy ▸ kl _ hl) (killsCokernel_of_isUnramified _ _ (by clear * - hU hz hp hW; grind) hk hp) rfl
      (y · ▸ by clear * - hU hc hs hW hi; grind) (he.trans_le ?_) (by lia) hδ c).some_mem
    let o a u := ite (a ≠ t) (stdExponent (t + J.succ) a u + 3 * A (a / 2)) (2 * b)
    all_goals try refine ⟨o, _,
      (pointsOver_nonempty_of_costs hx ((range (4 * J + 2)).sigma fun a ↦ twoWindows (ite (a = 0)
      (s i) 0 + W) (ite (ε (i.stepBack a) = ρ) 1 (-1) * β (i.stepBack a))) ?_ (by
      clear * - hd h₀ hs z hη hW hX hκ
      grw [← sum_sigma', sum_le_card_nsmul _ _ (72 * X), card_range]; lia
      refine fun a ha ↦ (sum_twoWindows_le n (2 * b) ?_ ?_).trans ?_ <;> grind [mul_le_mul' hs.1
        (add_le_add_left (mem_range_le ha) k.differentExp),
        le_of_mul_le_of_one_le_left (le_of_add_le_left hX) (by lia)])).imp fun _ ↦
      .imp_right (.imp_right (.imp_left (JumpLattice.mem_withExponents_of_le · ?_))), hl, ?_⟩
    all_goals
      try intro a; specialize hc a
      clear * - hU hc hi hL hs hW ht hη z hy he q; generalize i.stepBack = f at *
      (try simp [raisedAtE, -Nat.cast_sum]); grind (splits := 15)
  refine h.scaledCupBounds_of_points_at_cuts _ _ l (by grind [IsLeast, lowerBounds]) fun i e ↦
    ⟨pt 1 ?_ e, Int.units_ne_iff_eq_neg.eq ▸ pt (-1) ?_ e, pointsOver_nonempty_of_killsCokernel
    (killsCokernel_at_cut hX hκ hδ h₈ hs hy hK hz ?_ i e) 1, ?_⟩ <;>
    clear * - hU hW <;> simp [div_neg, Antitone] <;> grind

omit hs hz hy hX hκ hK
include hβ

/-- Sparse thick letters. Paired sides have jump sets in opposite windows [−η, η] ∪ ±[β_i, β_i + V],
β_i = b or G, G + V ≤ η, no three β = b at gaps in [1, J]; signs constant, or unramified with p ≥ 7.
Under size inequalities `Lift.Pairing.ScaledCupBounds` holds with exponent 10⁴X(J + 1).

Rank-free exponents for crystalline classes at large weights. -/
lemma SidePairing.scaledCupBounds_sparse_thick (hε : IsUnramified ∧ 7 ≤ p ∨ ∀ i i', ε i = ε i')
  (hG : G + V ≤ η) (hb : 11 * (p ^ J + 1) * W ≤ b) (hth : ∀ i, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J, T i →
  T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i)) (he : 4 * (J + 1 + k.differentExp +
  p.log (2 * b)) * W ≤ X) c c' : h.ScaledCupBounds (10 ^ 4 * (X * (J + 1))) c c' := by
  let C i := ∀ t ≥ 1, t ≤ J → ¬T ((k.letterFrob ^ t) i)
  replace hth i a (c : ¬C (.stepBack i a)) (t : T (i.stepBack a)) : C (i.stepBack (a + J.succ)) :=
    fun n _ hn tn ↦ c (by simp at t; simpa [t, pow_add, add_comm (_ - _), pow_sub _ hn.step] using
    (hth _ (J.succ - n) (by simp; lia) · · tn))
  apply h.scaledCupBounds_of_cut_windows _ (fun _ ↦ 0) b (2 * W) _ (3 * b / 5) (2 * W) hW hU _ .refl
    hδ h₈ hη _ _ _
    (by grw [← ·]; grind) _ _ (by_contra fun h ↦ h ⟨J + 1, by grind, fun n _ hn t ↦ h ⟨_, by grind,
    hth · (J + 1 - n) (h ⟨_, by simp; lia, ·⟩) (by simpa [pow_sub _ hn.step])⟩⟩) fun i n hl h ↦ ?_
  iterate 6 grind [mul_le_mul_left j.out.one_lt W, tsub_mul]
  replace hth a ha t := (eq_zero_or_pos a).imp_right fun a₀ ↦ (not_lt.1 fun e ↦ hl (n - a) (by lia)
    (by lia) (by simpa [← pow_mul_pow_sub _ ha.le])).eq_of_not_lt (h _ ⟨by lia, ·⟩
    (hth i a (h a ⟨a₀, ha⟩) t))
  exact (forall_or_exists_not _).elim (⟨0, .inl ·⟩) (.imp (by
    grw [sum_range_succ, @Nat.geomSum_lt _ J _ j.out.one_lt] <;> grind))

omit hδ h₈ in
lemma SidePairing.scaledCupBounds_two_sizes (hk : IsUnramified) (hp : 7 ≤ p) (h₀ : 5 * W ≤ G) (hG :
  G ≤ b) (hb : b < K * p ^ 2 ∧
  2 * G < K * p ∧ W ≤ K) c c' : h.ScaledCupBounds (10 ^ 4 * (K * (p.log (2 * b) + 1))) c c' := by
  obtain _ := pow_le_pow_left' hp 2, mul_le_mul_right hp (K - 1), mul_le_mul_right hp (b / p),
    b.div_mul_le_self p, @b.lt_div_mul_add p, @b.div_lt_of_lt_mul p (K * p)
  have z i : k.letterFrob (i.stepBack 2) = i.stepBack 1 ∧ k.letterFrob (i.stepBack 1) =
    i := by simp [sq]
  let s i := ite (T (k.letterFrob i)) (b / p - 7 * K) 0
  apply h.scaledCupBounds_of_cut_windows (fun i ↦
    s i < β i) s b K 1 (b / p + 12 * K) (G + W) hW hU .refl .refl <;> clear hU
  iterate 10 grind [tsub_mul, pow_one, hk.2]
  rintro i (_ | _ | _ | l) _ u <;> use 0 <;> try grind
  refine (em _).imp_right fun _ ↦ ⟨hk, ?_⟩; and_intros <;> try grind
  simp; nlinarith [(by grind : G + 7 * K ≤ b / p ∧ β i = b)]
end Lift.KummerChart.PairingSide
end

section
/-! (In the statements a jump is a Hodge–Tate weight, and Z_f the crystalline cocycles.) An exponent
independent of the ramification index for tame types. Over Q_ℓ, for potentially
crystalline lattices of tame inertial type with weights in two windows small against ℓ, a power of ℓ
makes Bloch–Kato classes cup to zero with those of congruent dual lattices, and the exponent, used
in the Selmer bound, depends on the sizes of the types and windows, not on the ramification index.
Small ramification, the tame potentially Barsotti–Tate case, and Kisin modules with descent data for
generic tame types are known. Related work: Iovita–Marmora, Continuity of the finite Bloch–Kato
cohomology, 2015; Nekovář, Compatibility of arithmetic and algebraic local constants II, 2018; Le–Le
Hung–Levin–Morra, Local models for Galois deformation rings, 2023.

Length bound for crystalline classes with few low weights. Over unramified ℓ-adic fields, if ℓ
divides no non-zero integer near 0 or the large weights, crystalline classes modulo those cupping to
zero with congruent dual lattices have length O(large weight/ℓ) per low weight plus O(rank × window
width), and length zero when there are no small negative weights; this bounds the loss above ℓ in
the Selmer bound. The absence of loss for weights below ℓ−1, exact Breuil–Kisin sequences for
weights of one sign, and torsion located by weights modulo ℓ are known. Related work:
Iovita–Marmora, Continuity of the finite Bloch–Kato cohomology, 2015; Čoupek–Gazaki–Marmora,
Exactness of Breuil–Kisin functors, 2026; Gao–Liu, Integral filtered Sen theory and applications,
2024.

This file: Final exponent and length bounds for crystalline classes against congruent dual
lattices. The prime ℓ of this comment is p in the code. -/

namespace Lift

open Polynomial Module Finset KummerChart JumpLattice Function IsLocalRing Topology Filter
variable {p} [l : ThePrime p] [Γ :
  GroupOverGp p] {O : Type} [CommRing O] {r N : ℕ} [PadicIntegerRing O p] [TopologicalSpace Γ] {L :
  GalLattice O Γ} {U U' : _ → Finset ℤ} (k : KummerChart Γ) (ζ : LetterRoot O) (ho :
  IsOpenEmbedding Γ.overGp.toGp) {F} (hF : map k.Γ'.subtype ⊤ ≤ F)

variable (p r N) in
/-- K holds for X^M − 1, M = lcm of the p^j − 1 for 1 ≤ j ≤ r, and for some monic polynomial over
ℤ_p of degree ≤ N. -/
def IsTameType (K : O[X] → _) := K (X ^ (Icc 1 r).lcm (p ^ · - 1) - 1) ∧
  ∃ q : ℤ_[p][X], q.Monic ∧ q.natDegree ≤ N ∧ K (q.map (algebraMap ..))

/-- For a letter i, the union of {0} and the finite sets U(g) over the Z_p-algebra maps g: O →
C_p with g(ζ) = θ(ω(i)). -/
noncomputable def KummerChart.letterJumps (U : (O →ₐ[ℤ_[p]] ℂ_[p]) → Finset ℤ) i :=
  insert 0 (Finset.biUnion {g | g ζ = ↑(theta (k.letterTeich i))} U)

/-- For L satisfying `Lift.InClass` F ⊥ U, with F containing only supersets of Γ': the side with
lattice L, jump sets `Lift.KummerChart.letterJumps` ζ U, C = Z_f(L) with trivial action, α the
identity. -/
noncomputable abbrev KummerChart.universalSide (h : InClass F ⊥ U L) : PairingSide ⟨O,
  ζ⟩ := have := crysCocycles.fg h.isPotCrys; ⟨⟨L, k.letterJumps ζ U, U, h.imp_left (.mono · (by
    gcongr)), by grind [letterJumps]⟩, ⟨crysCocycles L.ρ, 1⟩, .id, by simp [letterJumps]⟩

include ho

lemma KummerChart.mem_cupOrthogonal_of_scaledCupBounds {Q} (hc : Q ≤ InClass F ⊥ U) (hL :
  InClass F ⊥ U' L) e x (H : ∀ Y a (P : (k.universalSide ζ hF (hc Y
  a)).SidePairing (k.universalSide ζ hF hL)) c, P.ScaledCupBounds e c x) :
  (p : O) ^ e • x.1 ∈ cupOrthogonal Q L := fun Y P b y c ↦ mod_cast H Y b P ⟨y, c⟩ ho

/-- Unramified chart, p ≥ 5, L crystalline, U and U' in opposite windows, size and gap conditions.
Z_f(L) is orthogonal to crystalline lattices with jumps in U if neither U nor U' meets
[−a, 0), or U' lies in [−η, 0]; with ≤ m jumps in [−η, η], the defect has length ≤
11f(m(a+1) + (W+1) rk
L)·len(O/p). Orthogonal: in `Lift.cupOrthogonal`; defect: Z_f(L) modulo that part; U' holds the
jumps of L; p^f − 1 is the number of letters.

Length bound for crystalline classes with few low weights. -/
lemma KummerChart.few_low_jumps (hk : IsUnramified) (hp : 5 ≤ p) {a η W} {b : _ → ℕ} {ε : _ →
  _} (ha : ∀ n, b n + W + η ≤ (p - 3) * a) (hη : 1 ≤ η) (hb : ∀ n, 6 * (a + η + W) < b n) (hs : ∀ n,
  NoMultipleNear p (6 * (a + η + W)) (b n)) (hL : InClass ⊤ ⊥ U' L) (hV : ∀ i, IsInJumpWindow η
  (-ε i) (b i) W (k.letterJumps ζ U i) ∧ IsInJumpWindow η (ε i) (b i) W (k.letterJumps ζ U' i)) :
  ((∀ g u, u ∈ U g ∨ u ∈ U' g → u ∉ Ico (-↑a) 0) ∨ (∀ g, U' g ⊆ Icc (-η) 0) → crysCocycles L.ρ ≤
  cupOrthogonal (InClass ⊤ ⊥ U) L) ∧ ∀ m, (∀ g, ∑ u ∈ Icc (-↑η) ↑η, jump L.ρ g u ≤ m) →
  relLength (crysCocycles L.ρ) (cupOrthogonal (InClass ⊤ ⊥ U) L) ≤
  ↑(11 * (k.f * (m * (a + 1) + finrank O L * (W + 1)))) * length O (O ⧸ Ideal.span {(p : O)}) := by
  obtain M := k.mem_cupOrthogonal_of_scaledCupBounds ζ ho le_top le_rfl hL 0
  refine ⟨fun h₀ x m ↦ ?_, fun m hm ↦ (ENat.mul_le_mul_right_iff length_pos.ne' length_ne_top).1
    ((length_restrictScalars ℤ_[p] ..).ge.trans ?_)⟩
  · simpa using M ⟨x, m⟩ fun _ _ Q
      _ ↦ by apply Q.scaledCupBounds_of_killsCokernel (κ := 0) _ hs hV <;> (try intro <;>
      and_intros <;> apply PairingSide.killsCokernel_of_isUnramified) <;> simp [*,
      hk.2] <;> clear * - h₀ ha hb hV <;> grind [letterJumps]
  rw [mul_assoc, ← length_restrictScalars, ← map_natCast (algebraMap ℤ_[p] O),
    ← Set.image_singleton, ← Ideal.map_span, ← PadicInt.maximalIdeal_eq_span_p,
    length_eq_of_surjective residue_surjective (R := _ ⧸ _) (M := O ⧸ _),
    @length_eq_finrank _ _ (Ideal.Quotient.divisionRing _), finrank_quotient_map]
  refine ((k.universalSide ζ le_top hL).exists_scaledCupBounds_few_low_jumps hk hp ha hb hs
    (hV · |>.2) (by intro; grw [← mul_sum, sum_comm, hm]) (by intro; grw [← mul_sum, sum_comm,
    sum_le_sum fun g _ ↦ (hL.isPotCrys.exists_hasJumps g).rec fun J ⟨a, e⟩ ↦ funext e ▸ a ▸
    (sum_le_sum_of_ne_zero (by simp)).trans_eq J.toFinset_sum_count_eq]) hη).rec fun V H ↦
    ((relLength_mono le_rfl (T := ((cupOrthogonal ..).submoduleOf _).restrictScalars _) fun x y ↦ by
    simpa using! M x fun _ _ a _ ↦ H.2 _ a _ (hV · |>.1) _ y).trans (H.1.trans (mod_cast
    ?_))).trans_eq'
    (by rw [relLength_eq_length_map_mkQ, Submodule.map_top, Submodule.range_mkQ, length_top]; rfl)
  simp [← mul_sum, ← sum_mul]
  grw [← card_biUnion fun _ _ _ _ h ↦ disjoint_filter.2 fun _ _ a ↦ by simpa [a]
    using! (((isUnit_teichmuller_sub (Units.ext.mt h)).map (algebraMap ..)).map theta).ne_zero,
    card_le_univ, card_algHom_eq_finrank]; lia

/-- Tame types. Let j be a homeomorphism onto G_p, K tame on inertia (`Lift.IsTameType`),
κ = r²(N+1)², b + 6(W+η) + κ + 2 < p. For L of class (F, K(s⁻¹)) with jump sets in [−η, η] ∪ ε[b,
b+W], p^{3κ+150(η+W+1)} Z_f(L) is orthogonal to the class (F, K) with jump sets in the opposite
window.

Tame types: exponent independent of the ramification index. -/
lemma tame_types_exponent (hj : Surjective Γ.overGp.toGp) {F K} (hL : InClass F (K ·⁻¹) U' L) (hK :
  ∀ s, IsWeilPair (toGp s) 0 → IsTameType p r N (K s)) {η W b ε} (hU : ∀ g,
  IsInJumpWindow η (-ε) b W (U g) ∧ IsInJumpWindow η ε b W (U' g)) (hp : b + 6 * (W + η) +
  r ^ 2 * (N + 1) ^ 2 + 2 < p) : ∀ a ∈ crysCocycles L.ρ,
  (p : O) ^ (3 * (r ^ 2 * (N + 1) ^ 2) + 150 * (η + W + 1)) • a ∈ cupOrthogonal (InClass F K U) L :=
  (exists_tameChart hj ⟨_, r.factorial_pos⟩ (l.out.dvd_factorial.1.mt
  (by grind [le_self_pow])) (lcm_dvd fun _ ↦ Nat.pow_sub_one_dvd_pow_sub_one p ∘ And.elim
  Nat.dvd_factorial ∘ mem_Icc (b := r).1)).rec fun d he ↦ by
  obtain ⟨t, hm⟩ := d.isWeilPair_tameGen, show d.e ≤ p ^ r ^ 2 by
    grw [he, Nat.le_of_dvd _ (lcm_dvd_prod ..), prod_le_pow_card _ _ (p ^ r)] <;> simp_all
      [← pow_mul, sq, l.out.one_lt, le_add_right, pow_le_pow_iff_right₀, Nat.one_le_iff_ne_zero]
  let J := MulEquiv.ofBijective toGp ⟨ho.1.2, hj⟩
  have w (g : inertiaGroup ..) := isWeilPair_zero_iff.2 ((J.apply_symm_apply g.1).symm ▸ g.2)
  have A {K U} (hK : ∀ s, IsWeilPair (toGp s) 0 → IsTameType p r N (K s)) L (H : InClass F K ..) :
    InClass (O := O) _ ⊥ U L := ⟨.mono
    ((isAdmissible_comp_iff ..).1 ((H.isPotCrys.comp _).isCrystalline_of_inertia_fixes fun s u ↦ by
    simpa [linearFrob, Dpcris, ← map_nearOne _ ho.1.2 (@OverGp.isOpen_range d.Γ' ..)] using!
      (isLocalGalois_padic.tame_inertia isUniformiser_ell
      (valuation_natCast_eq_one d.tame) d.varpi_pow_eq ⟨⟨(linearFrob _ · 0) ∘ _, by simpa using
      (linearFrob_pow H.isPotCrys t 0)⟩, by simp [linearFrob_mul H.isPotCrys (w _) (w _)]⟩
      (Subgroup.isOpen_of_mem_nhds _ ((nhds _).3 (continuous_subtype_val.tendsto 1
      (mem_comap'.1 H.isPotCrys.eventually_linearFrob_eq_one)) fun g ↦ (· (J.right_inv _) (w g))))
      fun g ↦ by simpa [he] using (H.2.2 _ _ (hK _ (w g)).1 (w g)).2).1 (x :=
      ⟨J s, isWeilPair_zero_iff.1 u⟩) (d.apply_varpi s))) (sup_le nearOne_le le_rfl), H.2.1, nofun⟩
  obtain ⟨⟨-, q, m, n, k⟩, -, q', m', n', k'⟩ := hK _ t, hK _ t.inv
  refine (d.1.mem_cupOrthogonal_of_scaledCupBounds ⟨1, by simp⟩ ho le_rfl (A hK) (A (hK ·⁻¹ ·.inv) _
    hL) _ ⟨·, ·⟩ fun S hY h c ↦ (exists_isKilledBy_tateDual_tensor hY hL t.inv m' m k' ?_).rec fun _
    ⟨M, u, v⟩ ↦ h.scaledCupBounds_of_killsCokernel (fun _ ↦ ⟨d.killsCokernel_of_isKilledBy ?_ ?_ M
    hm hp (by grw [u, n, n']; lia), d.killsCokernel_of_isKilledBy ?_ ?_ m hm hp ?_,
    d.killsCokernel_of_isKilledBy ?_ ?_ m' hm hp ?_⟩) ?_ (fun _ ↦
    (?_ : IsInJumpWindow η (-ε) b W _ ∧ _)) ?_ ?_ c _) <;> (first | gcongr | simp_all [hY.2.2,
    hL.2.2, KummerChart.differentExp, ↓padicValNat.eq_zero_of_not_dvd d.tame]) <;> clear * - hp n n'
    hU <;> grind [NoMultipleNear, → Int.le_abs_of_dvd, KummerChart.letterJumps]
end Lift
end
