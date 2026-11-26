import Lib.PadicHodge.BlochKato
import Lib.PadicHodge.HodgeExpansion

section
/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

This file: a cup product of crystalline cocycles is a coboundary if they have lifts to
W(C^♭)-coefficients whose Galois and Frobenius differences pair into W(𝔪^♭). -/

noncomputable section

namespace Lift

open KummerChart Topology crysCocycles FrobGroup Submodule IsLocallyConstant Finset
variable {p} [ThePrime p] [Γ : GroupOverGp p] [k : KummerChart Γ] {O}

/-- One side of a pairing: a lattice datum Y (`Lift.KummerChart.JumpLattice`) with 0 in every jump
set U_i, a lattice C, and an O-linear map α: C → Z_f(Y), the crystalline cocycles. -/
structure KummerChart.PairingSide (O : Coeffs) extends kerLattice :
  JumpLattice O where (C : GalLattice O Γ) (α : C →ₗ[O] crysCocycles ρ) zero_mem i : 0 ∈ U i

variable {k} (S S' : PairingSide O)

/-- For a side S, the lattice datum formed by the extension of the trivial lattice C by Y given
by the cocycles of S, with ζ and the jump sets of S. -/
abbrev KummerChart.PairingSide.extLattice := JumpLattice.mk ⟨_,
  extensionRep S.α⟩ S.U _ ⟨isAdmissible_extensionRep _ S.inClass.1, fun _ _ n ↦ by
  simpa [or_iff_not_imp_left] using S.inClass.2.1 _ _ ∘ ne_bot_of_le_ne_bot n ∘ jump_extension_le
    _, nofun⟩ (insert_subset (S.zero_mem _) <| S.embJumps_subset ·)

/-- For a side S, the lattice datum formed by C with trivial action of Γ, with ζ and jump set
{0} at every letter. -/
abbrev KummerChart.PairingSide.trivLattice : JumpLattice O :=
  ⟨⟨S.C, 1⟩, fun _ ↦ {0}, _, .of_cyclotomic_pow 0, by simp⟩

/-- The projection from the extension of C by Y onto the trivial lattice C, as an equivariant
map of lattice data. -/
abbrev KummerChart.PairingSide.projTriv : S.extLattice.Hom S.trivLattice := ⟨.snd .., by tauto⟩

/-- For a side S with extension Ỹ = Y ⊕ C, the W(C^♭)-linear map W(C^♭) ⊗ Ỹ → W(C^♭) ⊗ Y induced
by the projection to the first summand. -/
abbrev KummerChart.PairingSide.wittFst := S.extLattice.wittMap S.kerLattice (.fst ..)

/-- For two sides S, S', the lattice datum Y ⊗_O Y' with the element ζ and, at each letter i,
the sumset U(i) + U'(i) of their integer sets. -/
abbrev KummerChart.PairingSide.tensorLattice := JumpLattice.mk _ (fun i ↦ (S.U i).image₂ (· + ·)
  (S'.U i)) _ (S.inClass.tensor S'.inClass) (by grw [S.embJumps_subset ·, S'.embJumps_subset ‹_›])

variable {S S' e} (P : Pairing S.toGalLattice S'.toGalLattice) (n : FrobGroup Γ)

/-- The side defined by a pairing P of Y and L: the lattice (Y ⊗ L)^∨(1), C = O with trivial
action, α(o) = o·c for the cocycle c of P, and jump sets holding 0 and the −u − u' − 1. -/
abbrev Pairing.thirdSide : PairingSide O := let T := S.tensorLattice S'; ⟨⟨_, fun i ↦
    insert 0 ((T.U i).image (-· - 1)), _, T.inClass.dual, (by grind [T.embJumps_subset ·])⟩, ⟨O, 1⟩,
    .toSpanSingleton _ _ P.thirdClass, by simp⟩

/-- The W(C^♭)-bilinear extension of the pairing Y×L→Z/p^m(1) to a pairing of W(C^♭)⊗Y and
W(C^♭)⊗L with values in W(C^♭)⊗Z/p^m(1). -/
abbrev Pairing.wittPairing :=
  (DiagTensor.pair P.modPairing : S.Ambient →ₗ[_] S'.Ambient →ₗ[_] DiagTensor (.of (charRep _ χ)))

/-- The pair (w, y) is safe: p^e times the pairing of the components of w, y in W(C^♭) ⊗ Y,
W(C^♭) ⊗ L lies in the image of W(𝔪^♭). -/
def Pairing.IsSafe e w y := p ^ e • P.wittPairing (S.wittFst w) (S'.wittFst y) ∈ smallPart _

/-- The cup product under P of α(c) and p^e α'(c') is a continuous coboundary
(`Lift.Pairing.CupBounds`) for every topology on Γ making j = `Γ.overGp.toGp` an open embedding. -/
def Pairing.ScaledCupBounds e c c' := ∀ ⦃_ : TopologicalSpace Γ⦄, IsOpenEmbedding Γ.overGp.toGp →
  P.CupBounds (S.α c) (p ^ e • S'.α c')

lemma wittFst_smul : ∀ x, S.wittFst (n • x) =
  n • S.wittFst x + S.trivLattice.wittMap S.kerLattice (.fst .. ∘ₗ extensionRep S.α (snd n) ∘ₗ
  .inr ..) (n • S.projTriv.wittMap x) := diagTensor_induction (by simp; simp [extensionRep])

lemma Pairing.smul_wittPairing x y : n • P.wittPairing x y = P.wittPairing (n • x) (n • y) :=
  .symm (baseChangePairing_map _ (P.modPairing_rho _) ..)

attribute [local simp] smul_sub smul_smul MonoidHom.map_one Pairing.smul_wittPairing wittFst_smul
  extensionRep
attribute [-simp] _root_.map_smul LinearMap.map_smul_of_tower map_one nsmul_eq_mul

/-- Let e₁ + e₂ + e₃ ≤ e, let x, w lie over p^{e₁}c and x' over p^{e₂}c'. If ((g−1)x, g(h−1)x'),
(w−x, (g−1)x'), ((g−1)w, g(φ−1)x'), (φx−w, (g−1)φx') satisfy `Lift.Pairing.IsSafe` e₃ for all g,
h in Γ', then `Lift.Pairing.ScaledCupBounds` holds for e, c, c'. -/
lemma Pairing.ScaledCupBounds.of_isSafe {e₁ e₂ e₃ c c'} x w x' (he : e₁ + e₂ + e₃ ≤ e) (hx :
  S.projTriv.wittMap x = p ^ e₁ • .mk 1 c) (hw : S.projTriv.wittMap w = p ^ e₁ • .mk 1 c) (hx' :
  S'.projTriv.wittMap x' = p ^ e₂ • .mk 1 c') (H : ∀ g : k.galMonoid, (∀ h :
  k.galMonoid, P.IsSafe e₃ (g • x - x) (g • (h • x' - x'))) ∧ P.IsSafe e₃ (w - x) (g • x' - x') ∧
  P.IsSafe e₃ (g • w - w) (g • (φ • x' - x')) ∧ P.IsSafe e₃ (φ • x - w) (g • φ • x' - φ • x')) :
  P.ScaledCupBounds e c c' := by
  intro _ hj; let B y := p ^ e₃ • P.wittPairing (S.wittFst y)
  have V {T : PairingSide O} {c} h := eventually_eq_pow_smul T.inClass.isPotCrys (c := c) h P.m
  obtain ⟨⟨z, h₀, C⟩, ⟨r, o⟩, u, _, Z, X, _⟩ := TateTwist.smallPart_spec (V <|
    coboundary_mem ·) (B x), pow_dvd_pow p he, nearOne_le, isLocalGalois_localFieldOf hj,
    apply_mul (S.α c).2, apply_mul (S'.α c').2, @smul_comm.{0,0,0} (FrobGroup Γ)
  choose y hd using (z (B w (S'.wittFst (φ • x' - x')))).2.1
  have N := (V (S'.α c').2).and ((V (S.α c).2).and
    ((C (S'.wittFst x')).and ((TateTwist.smallPart_spec (Quot.ind fun c ↦
    (eventually_eq_pow_smul (isAdmissible_of_cyclotomicGp_zpow 1 (ρ := charRep ..) (by simp; tauto))
    (coboundary_mem c) _).mono fun _ ⟨w, h⟩ ↦ ⟨w, congr($h)⟩) .id).2.2 y)))
  rw [nearOne_eq_nhds_one hj] at *
  choose κ hκ using fun g : k.Γ' ↦ let n := inr g.1
    (z (B (n • x) (n • S'.wittFst x') - n • (B x (S'.wittFst x') - y) - B x
      (S'.wittFst (n • x' - x')) - y)).2.2 (by
    convert (H ⟨_, g, rfl⟩).2.symm.elim (sub_mem <| ·.elim sub_mem) using 1
    linear_combination (norm := (simp +zetaDelta [*, (phi_mul_comm _).eq]; abel)) hd - n • hd)
  have key (g h : k.Γ') := congrArg (zmodPowToUnits _) (sub_eq_zero.1 (h₀ (p ^ e • P.modPairing
    ((S.α c).1 g) (S'.ρ g ((S'.α c').1 h)) - r • (charRep _ χ g.1 (κ h) - κ (g * h) + κ g)) (by
    convert nsmul_mem (add_mem ((H ⟨_, g, rfl⟩).1 ⟨_, h, rfl⟩) (add_mem (sub_mem
      (smul_mem_smallPart g.1 (hκ h)) (hκ (g * h))) (hκ g))) r
    simp +zetaDelta [*, -h₀, pow_add, mul_comm]; abel)))
  refine mem_comap.1 <| (ker_mkQ _).le <| (nsmul_eq_zero_iff_of_coprime (index_coprime.pow_right
    _)).1 ⟨((unitsModule _).restrictAlong ⟨toGp, hj.continuous⟩).index_smul_eq_zero_of_resH2 ⟨_,
    k.Γ'.isOpen_of_mem_nhds (u (·.2))⟩ (x := ⟦⟨_, ((iff_eventually_eq _).2 fun q ↦
    map_mul_left_nhds_one q ▸ ((N.and (V (coboundary_mem ((S'.α c').1 q.2)))
    ).prod_nhds N).mono (by rintro ⟨⟩ ⟨⟨⟨-, ⟨⟨⟩⟩⟩, _, e⟩, ⟨⟨⟩⟩⟩; simp [*, -h₀, eq_add_of_sub_eq e,
    ↓nsmul_quot_eq_zero])).continuous, by simp [map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, Z, X,
    modPairing_rho, Units.smul_def]⟩⟧) ((ker_mkQ _).ge ⟨zmodPowToUnits _ ∘ (r • κ),
    (isLocallyConstant_of_eventually_mul (.mono (continuousAt_subtype_val N) ?_)).continuous,
    by simpa [map_cyclotomicGp_smul _ nsmul_zmodPowToUnits, charRep] using!
    key⟩), congr(⟦⟨fun _ ↦ $(nsmul_zmodPowToUnits _), _⟩⟧)⟩
  rintro h ⟨⟨⟩, ⟨⟩, e₁, e₀⟩ _
  simpa [*, -h₀, ↓nsmul_quot_eq_zero, eq_neg_add_iff_add_eq, h₀ _ (by
    convert sub_mem (sub_mem e₀ e₁) (hκ h); simp +zetaDelta [*, -smul_smul]; abel)] using key _ h
end Lift
end
end

section
/-! Part of: Cokernel bounds and vanishing cup products for Kisin modules (see New.Lift.LongGap).

This file: Low and far weight windows, gap condition, sum of valuations over two intervals.
Annihilators p^κ E^s of cokernels of Kisin modules on crystalline extensions. S ⊂ A_inf is the
power series ring of the Kummer chart, z its variable, E = z^e·(unit) + p; a letter is a unit of
the field with p^f elements (`Lift.KummerChart.Letter`). -/

open Finset Int Ideal Submodule Lift.KummerChart.JumpLattice

namespace Lift

/-- The condition that the finite set U of integers lies in [−η, η] ∪ ε·[b, b + W], the union of
a low and a far window, for a sign ε. -/
abbrev IsInJumpWindow (η : ℕ) (ε : ℤˣ) (b W : ℕ) (U : Finset ℤ) := ∀ u ∈ U, -η ≤ u ∧ u ≤ η ∨
  ε.1 = 1 ∧ b ≤ u ∧ u ≤ b + W ∨ ε.1 = -1 ∧ b ≤ -u ∧ -u ≤ b + W

attribute [scoped grind =] Units.val_neg

/-- For an integer t, the system of exponents (a, u) ↦ t − u for a = 0 and −u for a > 0. -/
@[grind] def raisedAtE (t : ℤ) a u := ite (a = 0) t 0 - u

/-- The finite set of integers [−n, n] ∪ [i − n, i + n], two windows of radius n centred at 0
and at i. -/
noncomputable abbrev twoWindows (n : ℕ) (i : ℤ) := Icc (-↑n) ↑n ∪ Icc (i - n) (i + n)

/-- The prime-to-p gap condition: p divides no nonzero integer within distance n of 0, b or −b. -/
def NoMultipleNear (p n : ℕ) b := ∀ y ∈ twoWindows n b ∪ twoWindows n (-b), ↑p ∣ y → y = 0

lemma sum_twoWindows_le {n p d} {c : ℤ} (m H : ℕ) (e : n ≤ p * m) (hH : |c| + n ≤ H) :
    (twoWindows n c).sum (padicValInt p · + d) ≤ (4 * m + 2) * p.log H + (4 * n + 2) * d := by
  grw [← sum_add_card_nsmul, ← sum_filter_ne_zero, sum_le_card_nsmul _ (padicValInt p)
    (p.log H) fun k _ ↦ (padicValNat_le_nat_log _).trans (by gcongr; grind), (twoWindows m (c / p)
    ).card_le_card_of_surjOn (p • ·) fun _ ↦ ?_, card_union_le, card_union_le]; grind [card_Icc]
  simp; rintro m _ _ ⟨k, rfl⟩
  use k, m.imp ?_ ?_ <;> intro <;> use ?_ <;> nlinarith [(@ediv_eq_iff_of_pos p c _ (by lia)).1 rfl]

end Lift

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {S :
  Lift.KummerChart.PairingSide O} {r l : ℕ} {i : Lift.KummerChart.Letter} {a c n κ : ℕ} {f :
  k.S} {s : Ainf} {L : Lift.KummerChart.JumpLattice O}

lemma Lift.KummerChart.JumpLattice.tau_pow_smul_mem_ainfLattice_of_chi (c : ℕ) {x i} (hx :
  x ∈ L.withExponents i (stdExponent 0)) (hc : ∀ g x, L.ρ g x =
  χ g ^ (c : ℤ) • x := by simp) : tau ^ c • x ∈ L.ainfLattice := pow_mem_of_pow_mem
  (L.ainfLattice.comap (.toSpanSingleton ..)) (frame_theorem.2.1 _
  (frobKisinAinf_zero.le (mem_withExponents_stdExponent_iff.1 hx).1)) (Nat.sInf_le (by
  simp [hasJumps_of_cyclotomicGp_zpow c _ _, *, Units.smul_def, Multiset.mem_replicate]))

namespace Lift.KummerChart.PairingSide

variable (S i) in
/-- For c in C and a letter i, the image of 1⊗c in W(C^♭)⊗C under the projector to the letter i. -/
noncomputable def constantAt : S.C →ₗ[ℤ_[p]] S.trivLattice.Ambient :=
  (S.trivLattice.letterProj i).restrictScalars _ ∘ₗ DiagTensor.mk (ρ := .of _) 1

/-- The ideal of A_inf generated by r and the a that multiply the letter-i part of A_inf ⊗ C
into the image of the extension's module of standard exponents of level l. -/
noncomputable def liftIdeal (S : PairingSide O) (r l : ℕ) i :=
  span {↑r} ⊔ ((withExponents i (stdExponent l)).map (S.projTriv.wittMap.restrictScalars _)).colon
  (S.trivLattice.ainfLattice.map ((letterProj i).restrictScalars _))

/-- p^κE^s kills the cokernel at the letter i: it multiplies the letter-i part of A_inf ⊗ C into
the image of the extension's module of standard exponents of level 0. -/
def KillsCokernel (S : PairingSide O) i (κ s : ℕ) := ↑(p ^ κ * k.E ^ s) ∈ S.liftIdeal 0 0 i

/-- s lies in `Lift.KummerChart.PairingSide.liftIdeal` iff for some t in A_inf and every c in C, (s
− rt) times the letter-i part of 1⊗c lifts to an element of the extension with the standard
exponents of level l at i. -/
lemma mem_liftIdeal_iff : s ∈ S.liftIdeal r l i ↔ ∃ t, ∀ c, ∃ x ∈ S.extLattice.withExponents i
  (stdExponent l), S.projTriv.wittMap x = (s - r • t) • S.constantAt i c := by simp [liftIdeal,
  ainfLattice, Submodule.map_span, mem_span_singleton_sup, mem_colon, ← eq_sub_iff_add_eq',
  mul_comm, constantAt]

lemma p_pow_mem_liftIdeal_self : p.cast ^ κ ∈ S.liftIdeal (p ^ κ) l i :=
  Ideal.mem_sup_left (by simp)

attribute [local simp] Chart.frobE p_pow_mem_liftIdeal_self stdExponent zTau mul_dvd_mul mul_pow
  pow_dvd_pow pow_mul

lemma phi_pow_smul_constantAt c : FrobGroup.φ ^ l • S.constantAt i c = S.constantAt
  ((letterFrob ^ l) i) c := by simp [constantAt, smul_letterProj phi_pow_smul_letterTeich]

lemma mul_E_pow_mem_liftIdeal_one (H : s ∈ S.liftIdeal r 0 i) (hn : ∀ u ∈ S.U i, u ≤ n) :
    s * k.E ^ n ∈ S.liftIdeal r 1 i := mem_liftIdeal_iff.2 ((mem_liftIdeal_iff.1 H).imp' (· * _ ^ n)
  fun _ ↦ forall_imp fun _ ⟨_, s, q⟩ ↦ ⟨_, frobEUnit_zpow_mem_withExponents 0 n s
  (by rintro ⟨⟩ <;> simp_all), by simp [*, frobEUnit_pow_smul]; module⟩)

/-- Nakayama step: if p^c lies in the ideal J_l(i) taken modulo p^{c+1}
(`Lift.KummerChart.PairingSide.liftIdeal`), then this ideal is contained in the ideal taken modulo
0, of the multipliers that lift constants exactly. -/
lemma liftIdeal_le_of_p_pow_mem (H : p.cast ^ c ∈ S.liftIdeal (p ^ (c + 1)) l i) :
  S.liftIdeal (p ^ (c + 1)) l i ≤ S.liftIdeal 0 l i := by
  have := smul_le_of_le_smul_of_le_jacobson_bot (N :=
    S.liftIdeal 0 l i) (fg_span_singleton (p.cast ^ c)) (IsAdicComplete.le_jacobson_bot (span {↑p}))
  simp_all [liftIdeal, span_mul_span', pow_succ', sup_comm]

lemma constantAt_mem_locLetterPart c : S.constantAt i c ∈ S.trivLattice.locLetterPart l i :=
  letterProj_mem_of_valueFieldPoints (by
  simpa [valueFieldPoints, frobKisinAinf, kisinAinf, le_saturateBy (mk_one_mem_ainfLattice _),
    forall_and] using fun _ m ↦ mem_valueField_of_fixed (m c))

lemma phi_pow_mem_liftIdeal_iff l : FrobGroup.φ ^ l • s ∈ S.liftIdeal r l ((letterFrob ^ l) i) ↔
  s ∈ S.liftIdeal r 0 i := mem_liftIdeal_iff.trans (by
  simp_rw +singlePass [(MulAction.surjective (FrobGroup.φ ^ l)).exists]
  simp [smul_left_cancel_iff, mem_liftIdeal_iff, mem_withExponents_stdExponent_iff, frobKisinAinf,
    ← phi_pow_smul_constantAt, smul_comm r, ← smul_sub, ← frobGroup_smul_smul,
    phi_pow_smul_mem_letterPart_iff, -nsmul_eq_mul])

lemma p_pow_mul_z_pow_mem_liftIdeal_iff : p ^ c * k.z.1 ^ (p * a) ∈ S.liftIdeal r 1
  (k.letterFrob i) ↔ p ^ c * k.z.1 ^ a ∈ S.liftIdeal r 0 i := by
    simp [← phi_pow_mem_liftIdeal_iff 1, ↓phi_pow_smul_z, ↓smul_mul', ↓smul_pow']

/-- If f in S lies in the ideal `Lift.KummerChart.PairingSide.liftIdeal` (modulus r, level l, letter
i), there is t in S such that (f − rt)y lifts to φ^{l*}N of the extension at i for every y in
φ^{l*}N(C) at i. -/
lemma exists_lift_of_mem_liftIdeal (H : ↑f ∈ S.liftIdeal r l i) : ∃ t, ∀ y ∈
  S.trivLattice.locLetterPart l i, ∃ x ∈ S.extLattice.locLetterPart l i, S.projTriv.wittMap x =
  (f - r • t).1 • y := (mem_span_singleton_sup.1 H).imp' k.coord₀ fun t ⟨s, H, e⟩ y ⟨m, hy⟩ ↦
  (H ⟨y, ⟨_, tau_pow_smul_mem_ainfLattice_of_chi 0 (mem_withExponents_of_le
  hy), by simp [mem_letterPart_iff_letterProj.1 hy.1.2]⟩, rfl⟩).rec fun x ⟨hx, q⟩ ↦ ⟨_,
  ⟨Submodule.coe_mem _, coordRetract_mem_withExponents ⟨_, hx.1.1⟩ hx⟩, by
  simp [↓S.projTriv.map_coordRetract ⟨x, _⟩ ⟨_, smul_mem _ s m.1⟩ q, coordRetract, eq_sub_of_add_eq'
    e, k.coord₀_coe, exists_coordRetract.choose_spec _ _ m, ↓← map_nsmul, mul_comm]; rfl⟩

/-- If f in S lies in the level-one ideal `Lift.KummerChart.PairingSide.liftIdeal` at the letter i
and zτE(s + βf) = α(gf − f) with g in Γ' and s, α, β in A_inf, then s lies in the same ideal
(τ = [ε^{1/p}] − 1; Γ' is the subgroup of the chart). -/
lemma mem_liftIdeal_of_derivation α β (g : k.galMonoid) (H : ↑f ∈ S.liftIdeal r 1 i) (e : k.zTau *
  k.E * (s + β * f) = α * (g • f - f)) : s ∈ S.liftIdeal r 1 i := (exists_lift_of_mem_liftIdeal
  H).rec fun t K ↦ (zTau_mul_E_dvd_smul_sub g t).rec fun v hv ↦ mem_liftIdeal_iff.2 ⟨α * v - β * t,
  fun c ↦ (K _ (constantAt_mem_locLetterPart c)).rec fun x ⟨⟨m, o⟩, q⟩ ↦ ⟨_,
  sub_mem (smul_mem _ α (frobEUnit_zpow_mem_withExponents 0 (-1) (smul_sub_mem_zTauUnit_smul_of_deep
  (c := frobExponent 1 1 (stdExponent 0)) m (mem_withExponents_of_mem_hodgeFil
  (smul_sub_mem_withExponents o g) (·.rec (fun u v _ _ e ↦ by simpa [valueAt_smul_sub m.1 e.1] using
  (smul_sub_mem_hodgeFil_of_valueField g ![1] (valueAt_mem_valueField e.1 m) (o.2 0 u v _ e)
  (by simp [dvd_of_mul_left_dvd (zTau_mul_E_dvd_smul_sub ..)])))
  (by simp)))))) (smul_mem _ β o), smul_left_cancel (k.zTauUnit * k.frobEUnit 0) (by
  linear_combination (norm := (simp [k.galMonoid.smul_def, q, frobGroup_smul_smul, mul_smul,
    zTauUnit_smul, smul_comm _ α, smul_sub, constantAt, gal_smul_letterProj]; module)) congr(-($e +
    r * α * $hv) • S.constantAt i c))⟩⟩

/-- For the ideals J_l = `Lift.KummerChart.PairingSide.liftIdeal` with one modulus r: if p^c z^n
lies in J_1 at the letter i^p, pa ≤ n and c + v_p(n!) ≤ κ + v_p((pa)!), then p^κ z^a lies in J_0 at
i. -/
lemma mem_liftIdeal_zero_of_mem_one c κ (hm : p * a ≤ n) (H :
  ↑(p ^ c * k.z ^ n) ∈ S.liftIdeal r 1 (k.letterFrob i)) (e : c + padicValNat p
  n.factorial ≤ κ + padicValNat p (p * a).factorial) : p ^ κ * k.z.1 ^ a ∈ S.liftIdeal r 0 i := by
  induction' hm with n _ ih generalizing c
  exact mem_of_dvd _ (by simp_all) (p_pow_mul_z_pow_mem_liftIdeal_iff.1 H)
  obtain ⟨⟨t, _⟩, α, β, E⟩ := exists_smul_z 1,
    k.exists_tau_mul_E_eq_mul_epsTilt_pow_sub n.succ_ne_zero
  erw [padicValNat.mul (by simp) (by positivity), ← add_assoc] at e
  exact ih _ (mem_liftIdeal_of_derivation α β ⟨_, t, rfl⟩ H (by simp_all; grobner)) e

/-- If p^c z^a E^n lies in the level-one ideal `Lift.KummerChart.PairingSide.liftIdeal` at the
letter i, then so does p^b z^κ whenever b ≥ c + dn + v_p(n!) and κ ≥ a + n, where
d = `Lift.KummerChart.differentExp`. -/
lemma mem_liftIdeal_of_mul_E_pow {b} (H : ↑(p ^ c * k.z ^ a * k.E ^ n) ∈ S.liftIdeal r 1 i) (e :
  c + k.differentExp * n + padicValNat p
  n.factorial ≤ b ∧ a + n ≤ κ) : p ^ b * k.z.1 ^ κ ∈ S.liftIdeal r 1 i := by
  induction' n with n ih generalizing a c
  exact mem_of_dvd _ (by simp_all) H
  refine @ih a.succ (c + cost 0 n.succ) ?_
    (by clear H; grind [cost, padicValInt, Nat.factorial, padicValNat.mul])
  obtain ⟨g, ω, υ, _, _, -, ⟨b, R⟩, Q⟩ := exists_depth_step 0 n.cast_add_one_ne_zero
  have ⟨v, _⟩ := zTau_mul_E_dvd_smul_sub g k.z
  have ⟨t, _⟩ := sub_one_dvd_pow_sub_one (1 + tau * k.E * v) a
  refine mem_liftIdeal_of_derivation (k.z * υ) (k.z * b + υ * v * t * ω ^ n.succ) g H ?_
  simp_all [zpow_add, sub_eq_iff_eq_add', mul_assoc, ← mul_one_add, mul_comm tau]
  grobner

/-- If all allowed jumps are ≤ n, then for each κ some power z^a with (p − 1)a ≤ e(n + κ) lies,
at every letter, in the level-zero ideal `Lift.KummerChart.PairingSide.liftIdeal` of modulus p^κ. -/
lemma exists_z_pow_mem_liftIdeal (hn : ∀ i, ∀ u ∈ S.U i, u ≤ n) κ : ∃ a, (∀ i, k.z.1 ^ a ∈
  S.liftIdeal (p ^ κ) 0 i) ∧ a * p ≤ k.e * (n + κ) + a := (exists_minimal_of_wellFoundedLT _
  (radical_le_radical_iff.2 (Ideal.span_le.2 (Set.pair_subset ⟨κ, by simp⟩ ⟨_, mem_iInf.2 fun _ ↦
  mem_liftIdeal_iff.2 ⟨0, fun c ↦ ⟨_, letterProj_mem_withExponents
  (frobKisinAinf_zero.ge (frame_theorem.2.2.1 _ (mk_one_mem_ainfLattice (0, c)))), by simp; rfl⟩⟩⟩))
  (Ainf.mem_radical_of_not_isUnit (by exact k.chart.4) not_p_dvd_tau))).imp fun a m ↦
  ⟨mem_iInf.1 m.1, p.mul_le_of_le_div _ _
  (m.le (by simpa using fun i ↦ (mem_liftIdeal_zero_of_mem_one 0 0 (Nat.mul_div_le ..) (by
  simpa [pow_add] using! (sup_pow_add_le_pow_sup_pow.trans (c := under _ (colon _ {_ ^ a})) (by simp
    [span_singleton_pow, mul_comm (_ ^ n), mul_mem_right, mul_E_pow_mem_liftIdeal_one (mem_iInf.1
    m.1 _) (hn _)]) (Ideal.pow_mem_pow ((Ideal.span_insert ..).le k.z_pow_mem_span) _))))))⟩

/-- Unramified chart, p ≥ 5: if all allowed jumps are ≤ (p − 3)(s + t), then p^s E^t times the part
of A_inf ⊗ C at the letter i lifts to the extension's module of standard exponents of level 0. -/
lemma killsCokernel_of_isUnramified (s t : ℕ) (hn : ∀ i, ∀ u ∈ S.U i, u ≤
  ↑((p - 3) * (s + t))) (hk : IsUnramified) (hp : 5 ≤ p) :
  S.KillsCokernel i s t := (exists_z_pow_mem_liftIdeal hn (s + t).succ).rec fun b ⟨H, e⟩ ↦ by
  simp_all [IsUnramified, KillsCokernel, add_pow, Finset.mul_sum]
  have K m := mem_liftIdeal_zero_of_mem_one 0 (s + t - m) (mul_le_mul_right (b.le_max_right m) p)
    (p_pow_mul_z_pow_mem_liftIdeal_iff.2 (mem_of_dvd _ (by simp) (H i)))
    (by grind [padicValNat_factorial_mul,
    @Nat.lt_of_mul_lt_mul_left (p - 2) (b + padicValNat p b.factorial) (s + t).succ (by
    obtain ⟨⟨P, rfl⟩, _⟩ := hp.dest, @sub_one_mul_padicValNat_factorial p _ b; lia)])
  exact liftIdeal_le_of_p_pow_mem (by simpa using K 0)
    (sum_mem fun m _ ↦ mem_of_dvd _ (by grw [add_tsub_le_assoc]; ring_nf; simp) (K m))
end Lift.KummerChart.PairingSide
end
