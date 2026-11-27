import Lib.ClassField.DiscreteUnits
import Lib.ClassField.ExtendCharacter
import Lib.ClassField.SylowReduction
import Lib.ClassField.TameInertia
import Lib.ClassField.DecompositionLocal

-- part: Lib.Adelic.Cartan.ProjectiveModules
section
/-! Known result: Finiteness of the cokernel of the Cartan map, and Higman's criterion. It is stated
here for rational multiplicative functions on finite modules killed by a prime on which one element,
central modulo the level, fixes no nonzero vector, and projective is read as Higman's property. The
proof uses functions on two parallel affine hyperplanes, with no Brauer characters or Artin
induction. Source: J.-P. Serre, Linear Representations of Finite Groups (1977), Thm 35; for the
route by induction from cyclic subgroups in the local Euler characteristic formula, Milne,
Arithmetic Duality Theorems, I 2.10-2.12.

This file: Multiplicative function trivial on projective modules is trivial; Higman criterion,
dévissage. -/

namespace DiscreteModule

open MulAction Equiv QuotientGroup Finset Finite Submonoid Function commutatorElement Subgroup
  Module.End Fintype Fint
variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G] (l n : ℕ) [F : Fact l.Prime]
  (U : OpenNormalSubgroup G) (Q : Subgroup G) [i : Finite (G ⧸ Q)] (z : G) (m j : ℕ) (A :
  DiscreteModule R G)

/-- Higman's criterion relative to Q of finite index: some additive τ : A → A has ∑ gτg⁻¹ = 1,
summed over chosen representatives g of G/Q. -/
def IsHigmanProjective := ∃ τ : A →+ A, ∀ a, ∑ g : G ⧸ Q, A.ρ g.out (τ (A.ρ g.out⁻¹ a)) = a

/-- The condition that the subgroup Q of G acts trivially on A. -/
abbrev TrivialOn := ∀ g ∈ Q, ∀ m, A.ρ g m = m

/-- The G-module A is finite, killed by n, fixed by the subgroup Q, and the endomorphism z − m
of A (z in G, m a natural number) is injective. -/
def FiniteKilledFixedInj := Finite A ∧ (∀ a : A, n • a = 0) ∧ A.TrivialOn Q ∧ Injective ⇑(A.ρ z - m)

attribute [local simp] mul_smul QuotientGroup.eq compHom_smul_def TrivialOn

/-- For a finite set Y with an action of a discrete group Δ, the (G × Δ)-module of functions f :
Y → A, with ((g, δ)f)(x) = g f(δ⁻¹x). -/
abbrev permModule {Δ} [Group Δ] [TopologicalSpace Δ] [DiscreteTopology Δ] Y [Finite Y] [MulAction Δ
  Y] := of ⟨⟨fun g : G × Δ ↦ .pi fun x : Y ↦ A.ρ g.1 ∘ₗ .proj (g.2⁻¹ • x), by aesop⟩, by aesop⟩

variable {l n U Q i z m j A} (φ : ∀ A : DiscreteModule R G,
  FiniteKilledFixedInj l U.1.1 z 1 A → ℚ≥0)

lemma FiniteKilledFixedInj.of_isShortExact {B M ι π} (s : A.IsShortExact ι (π : Hom B M)) :
  B.FiniteKilledFixedInj n Q z m → A.FiniteKilledFixedInj n Q z m ∧ M.FiniteKilledFixedInj n Q z
  m := by refine s.rec fun r ⟨_, s⟩ ⟨_, _, _, t⟩ ↦ have := of_surjective _ s; ⟨⟨of_injective _
    r, ?_, ?_, fun a b e ↦ r (t ?_)⟩, this, ?_, ?_, injective_iff_surjective.2 ((s.comp
  t.bijective_of_finite.2).forall.2 (⟨π ·, ?_⟩))⟩ <;>
  simp_all [← r.eq_iff, ι.isIntertwining, s.forall, ← map_nsmul π n, ← π.isIntertwining]

/-- If A is finite, killed by n and fixed by Q, and the index of Q is prime to n, then A has
Higman's property `DiscreteModule.IsHigmanProjective` for Q. -/
lemma FiniteKilledFixedInj.isHigmanProjective_of_coprime (c : A.FiniteKilledFixedInj n Q z m) (h :
  n.Coprime Q.index) : A.IsHigmanProjective Q := have ⟨_, b, e⟩ := h.isCoprime
  ⟨b • .id _, (by simpa [add_smul, c.2, mul_comm b, index] using congr($e • ·))⟩

/-- Dévissage: for P normal, a property that holds for modules fixed by P and killed by l and is
stable under extensions holds for every finite l^j-torsion module on which each g in P has
some g^(l^i) acting trivially. -/
@[elab_as_elim] lemma devissage_induction (e : l ^ j = n) (P Q : Subgroup G) [P.Normal] {p : ∀ A :
  DiscreteModule R G, FiniteKilledFixedInj n Q z m A → Prop} (H : ∀ g ∈ P, ∃ i, g ^ l ^ i ∈ Q) (h :
  ∀ A c, FiniteKilledFixedInj l P z m A → p A c) (k : ∀ {A B C ι π} (s : IsShortExact ι π) c,
  p A (c.of_isShortExact s).1 → p C (c.of_isShortExact s).2 → p B c) : ∀ B c, p B c :=
  (invImage (Module.length R ·.V) inferInstance).2.fix fun B ih ⟨f, a, t, i⟩ ↦
  (IsPGroup.card_eq_or_dvd (G := Multiplicative B) (⟨j, e ▸ a ·⟩)).elim (h _ _ ⟨f,
  card_le_one_iff_subsingleton.1 ·.le |>.rec (by tauto)⟩) fun d ↦ (exists_prime_addOrderOf_dvd_card'
  (G := FixedPoints.addSubgroup (P.map B.ρ.toHomUnits) B) l (((IsPGroup.card_modEq_card_fixedPoints
  (fun ⟨_, g, h, rfl⟩ ↦ by peel H g h; ext; simp [*, ← map_pow]) B).dvd_iff dvd_rfl).1 d)).rec
  fun ⟨b, o⟩ e ↦ let W := (B.restrictTo P).H0 ⊓ (l • LinearMap.id).ker; k (B.isShortExact_submodule
    W fun g b ↦ .imp (B.ρ.le_comap_invariants _ g ·) (by simp_all [← map_nsmul])) _ ((fun c ↦
    h _ c (c.imp_right (by simp [W, ← SetLike.coe_eq_coe]; tauto))) _) (ih _ (W.length_quotient_lt
  (F.1.ne_one <| e ▸ by simpa using ·.le ⟨(o ⟨_, _, ·.2, rfl⟩), e ▸ by simp⟩)) _)

variable (R l U) [IsTopologicalGroup G] [CompactSpace G] (w : ∀ g, ⁅z, g⁆ ∈ U) (h : ∀ {A B D ι π}
  (s : IsShortExact ι π) c, φ B c = φ A (c.of_isShortExact s).1 * φ D (c.of_isShortExact s).2) (c :
  A.FiniteKilledFixedInj l U z 1) (k : ∀ {B} c, B.IsHigmanProjective U → φ B c = 1)

/-- Sylow's theorem for G/U: for a compact group G, an open normal subgroup U and a prime l,
some open subgroup P ⊇ U has index prime to l, and each g in P has g^(l^k) ∈ U for some k. -/
lemma exists_open_sylow : ∃ P : OpenSubgroup G, U.1.1 ≤ P ∧ l.Coprime P.1.index ∧
  ∀ g ∈ P, ∃ k, g ^ l ^ k ∈ U := have P : Sylow l _ := default
  ⟨⟨_, isOpen_mono (le_comap_mk' _ P.1) U.1.2⟩, le_comap_mk' .., by simp [P.not_dvd_index,
  index_comap, F.1.coprime_iff_not_dvd], (by simpa [Subtype.ext_iff, ← mk_pow] using! P.2 ⟨·, ·⟩)⟩

include w in
/-- Let z be central modulo U. Some normal S in Δ = G/U satisfies: for finite A killed by l,
fixed by U, with z − 1 injective, and finite Δ/S-sets Y, Fun(Y, A) keeps these properties,
and meets Higman's criterion for U if some Y → ℤ/l has trace 1 over Δ/S. -/
lemma exists_permModule_isHigmanProjective : ∃ S : Subgroup (G ⧸ U.1.1), ∃ _ : S.Normal,
  ∀ {A : DiscreteModule R G}, A.FiniteKilledFixedInj l U z 1 →
  ∀ Y [Finite Y] [MulAction (_ ⧸ S) Y], let := compHom Y (mk' S)
  let B :=
    (A.permModule Y).restrictAlong ⟨.prod (.id G) (mk' U.1), .prodMk continuous_id continuous_mk⟩
  B.FiniteKilledFixedInj l U z 1 ∧ ∀ a : Y → ZMod l, (∀ y, ∑ g : _ ⧸ S, a (g⁻¹ • y) = 1) →
    B.IsHigmanProjective U :=
  have ⟨j, n, _⟩ := WfDvdMonoid.max_power_factor (orderOf_pos (@mk _ _ U z)).ne' F.1
  let S := zpowers (↑z ^ l ^ j)
  have : S.Normal := ⟨by
    rintro _ ⟨i, rfl⟩ ⟨g⟩; use i, eq_mul_inv_of_mul_eq (((commutatorElement_eq_one_iff_commute.1
    ((eq_one_iff _).2 (w g))).pow_left _).zpow_left i)⟩; ⟨S, this, by
  intro A ⟨_, c, t, i⟩ Y _ _ _ B
  obtain ⟨⟩ := AddCommGroup.zmodModule c, (Commute.one_right (A.ρ z - 1)).add_pow_prime_pow_eq F.1 j
  refine ⟨⟨Pi.finite, ?_, ?_, .of_ker _ fun a e ↦ (fun _ ↦ funext fun y ↦ iterate_injective i
    (l ^ j) (a₂ := 0) ?_) (((stabilizerSubmonoid _ a).comap B.ρ).pow_mem (x := z) (by simp_all) (l
    ^ j))⟩, fun a e ↦ ⟨.pi ((a · / n) • Pi.evalAddMonoidHom _), fun _ ↦ funext fun y ↦ ?_⟩⟩
  iterate 3 simp_all [B, funext_iff, (eq_one_iff _).2, S] <;> tauto
  simp [B, ZMod.map_smul, ← sum_smul, ← sum_div]
  erw [S.groupEquivQuotientProdSubgroup.sum_comp (a <| ·.1⁻¹ • y)]
  simp [S, sum_prod_type_right, card_zpowers, orderOf_pow, ZMod.natCast_eq_zero_iff, F.1.pos, *]⟩

/-- Let f, from finite Δ-sets (Δ finite) to ℚ≥0, be 1 on empty sets, with f(Y) = f(Y − Δy)
f(Δ/Stab y). If X has a fixed point and f(X × Δ/K) = 1 for all subgroups K, then f(Δ/K) = 1
for all K. -/
lemma eq_one_of_prod_quotient.{u, v} (Δ : Type (max u v)) {X : Type v} [Group Δ] [Finite Δ]
  [Finite X] [MulAction Δ X] (f : ∀ (Y : Type (max u v)) [Finite Y] [MulAction Δ Y], ℚ≥0)
  (x : fixedPoints Δ X) (h : ∀ Y
  [Finite Y] [MulAction Δ Y], (IsEmpty Y → f Y = 1) ∧ ∀ y : Y, f Y = f ↥(SubMulAction.mk (orbit Δ y)
  (mem_orbit_of_mem_orbit ·))ᶜ * f (Δ ⧸ stabilizer Δ y)) (H : ∀ K : Subgroup Δ, f (X × Δ ⧸ K) = 1) :
  ∀ K : Subgroup Δ, f (Δ ⧸ K) = 1 := WellFoundedLT.fix fun K ih ↦ by
  rw [← pow_eq_one_iff_left, ← H, (h (X × Δ ⧸ K)).2 (x, ⟦1⟧), pow_succ, (by aesop :
  stabilizer Δ _ = K), ← (((measure _).2.fix fun Y r _ _ p ↦ (isEmpty_or_nonempty Y).elim
  (fun _ ↦ by simp [h]) fun ⟨y⟩ ↦ (p
  y).exists_rep.rec fun g e ↦ (h _).2 (g⁻¹ • y) ▸ mul_mem (r _ (card_subtype_lt (by tauto)) ⟨(p ·),
  by simp⟩) ((eq_or_lt_of_le (b := K) fun _ a ↦ by simpa [← e] using congr(p $a)).elim (· ▸
  mem_powers _) (by simp [ih, ·])) : ∀ Y [Finite Y] [MulAction Δ Y], (Y →[Δ] Δ ⧸ K) → f Y ∈ powers
  (f (Δ ⧸ K))) (Subtype _) ⟨(·.1.2), by simp⟩).choose_spec]; simp

include h k w

/-- Let l be prime, U open normal in the compact group G, z central modulo U, and φ, with values in
ℚ≥0, multiplicative in short exact sequences of finite l-torsion modules fixed by U on which z − 1
is injective. If φ = 1 on those with Higman's property, then φ = 1 on all.

Known result: The Cartan map has finite cokernel; Higman's criterion. -/
lemma IsMultiplicative.eq_one_of_isHigmanProjective :
  φ A c = 1 := have ⟨S, _, P⟩ := exists_permModule_isHigmanProjective R l U w; by
    have I {A B a b} (u : (ρ A).Equiv (ρ B)) : φ A a = φ B b := by simp [@h (of (V := Unit)
      1) _ _ 0 _ ⟨by tauto, by aesop_cat, u.surjective⟩, k _ ⟨0, _⟩]
    let Δ := _ ⧸ S
    let Λ := AddMonoidHom.mk' _ (@sum_add_distrib Δ (ZMod l) univ _)
    let := @arrowAction Δ
    let act e := (Λ.fiberEquivKer e).symm.mulAction Δ (β := SubMulAction.mk _ fun g a ↦
      (sum_comp (.mulLeft g⁻¹) (a ·)).trans)
    let := act 0
    obtain ⟨⟨⟩, _⟩ := PSigma.mk _ (discreteTopology_bot (Perm Λ.ker)), @Unique.mk' (Δ ⧸ ⊤) _
      subsingleton_quotient_top
    let H : Subgroup (G × Perm Λ.ker) := ⟨⟨⟨{p | ∀ y z, (p.2 y).1 - p.2 z = (p.1 : Δ) • (y -
      z)}, by simp_all [-Subtype.forall]⟩, by simp⟩, (by simp [eq_inv_smul_iff, ← · _])⟩
    let s e : G →ₜ* H := .mk (.mk' (fun g ↦ ⟨(g, (act e).toPerm ↑↑g), fun _ _ ↦
      by (repeat erw [add_sub_add_left_eq_sub]); rfl⟩) (by simp [← toPermHom_apply]))
    have tw e B a : ∀ b, φ (restrictAlong B (s 0)) a = φ (restrictAlong B (s e)) b :=
      devissage_induction (z := 1) (m := 0) l.pow_one
      ((MonoidHom.fst ..).domRestrict H).ker ⊥ (fun g (a : g.1.1 = 1) ↦ ⟨1, by
      ext <;> simp [a, congr($(ext (g := .addLeft (g.1.2 0)) (by simpa [a, Subtype.ext_iff,
        sub_eq_iff_eq_add'] using (g.2 · 0))) ^ l)]⟩) (fun B _ t _ _ ↦ I (.mk 1 fun g ↦ B.ρ.eq_iff.2
      (LinearMap.ext (t.2.2.1 _ (inv_mul_cancel g))))) (fun S ↦ by simp_all [h (S.restrictAlong _),
      FiniteKilledFixedInj.of_isShortExact (S.restrictAlong _)]) B (a.imp_right (by simp; tauto)) a
    exact .trans (I (.mk (.symm (.funUnique ..)) (by tauto))) (eq_one_of_prod_quotient Δ (fun Y ↦
      φ _ (P c Y).1) ⟨0, fun _ ↦ one_smul Δ 0⟩ (fun Y ↦ ⟨fun _ ↦ k _ ⟨0, by simp [funext_iff]⟩,
      fun y ↦ let E := .funCongrLeft R A (((orbitEquivQuotientStabilizer ..).symm.sumCongr
      (.refl _)).trans (sumCompl _)) ≪≫ₗ .sumArrowLequivProdArrow ..; @h _ _ _ ⟨_, by
      intro; ext _ _ x; by_cases orbit Δ x = orbit Δ y <;> simp [← orbit_eq_iff, *]; rfl⟩ ⟨_, by
      simp [DFunLike.ext_iff, funext_iff, forall_mk]⟩
        ⟨E.symm.injective.comp LinearMap.inr_injective,
      (E.conj_symm_exact_iff_exact ..).2 .inr_fst, Prod.fst_surjective.comp E.surjective⟩ _⟩)
      (fun K ↦ have C e := @P _ (P c _).1 _ _ (act e); .trans (I (b := (C 0).1) (.mk (.curry ..)
      (by tauto))) ((tw _ ((permModule ..).restrictTo H) _ _).trans (k (C _).1 ((C (Pi.single 1
        1)).2 (·.1 1 + 1) fun ⟨_, _⟩ ↦ by (repeat erw [sum_add_distrib]); simpa [Δ])))) ⊤)
end DiscreteModule
end

-- part: Lib.ClassField.GaloisCohomology.CyclicNorm
section
/-! Known result: Galois cohomology in degrees ≤ 2, covering Shapiro, Hilbert 90, Kummer, symbols
and the Herbrand quotient. Only explicit continuous cocycles are used, and Shapiro's lemma appears
only as injectivity. Corestriction is summation on functions on a coset space, and Tate's lemma on
the Herbrand quotient is an index formula for a group of prime order. Source: J.-P. Serre, Galois
Cohomology (1997); Neukirch–Schmidt–Wingberg, Cohomology of Number Fields (2nd ed. 2008), Ch. I, VI;
Atiyah–Wall, Cohomology of groups, in Cassels–Fröhlich (1967), IV §8.

Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles (known
result; see Lib.ClassField.LocalDuality.CrystallineDuality).

This file: Index of n-th powers in the multiplicative group of a local field. Tate's index formula
for norms on stable subgroups in prime-degree Galois extensions. Classes split by a cyclic extension
are symbols; symbols vanish exactly on norms. -/

open Algebra IsLocalRing Quotient DiscreteModule Fint Group Ideal IsGalois LinearMap Module
  MulSemiringAction Polynomial QuotientGroup Submodule DiscreteUnits Valuation groupCohomology
  Ideal.Quotient Mathlib.Tactic.LinearCombination

attribute [-simp] map_smul

attribute [local simp] NeZero.ne pos_iff div_sub_one cokerKerIndex valuationVia

/-- For a local field L with integers O, l ≠ 0 and a group Y ≅ L^×, the quotient #(Y/lY) / #Y[l]
is non-zero and equals l·#(O/l). -/
lemma cokerKerIndex_local_units {Γ L Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field L] [Field Ω]
  [Algebra L Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} (h : IsLocalGalois Γ L A) (l : ℕ)
  [NeZero l] {Y} [AddCommGroup Y] (y : Y ≃+ Additive Lˣ) : cokerKerIndex (l : End ℤ Y) ≠ 0 ∧
  cokerKerIndex (l : End ℤ Y) = l * Nat.card (_ ⧸ Ideal.span {(l : valRingBelow L A)}) := by
  obtain ⟨⟨π, hπ⟩, ⟨⟩⟩ := h.5.exists_irreducible, _root_.id h, (algebraMap L Ω).charZero
  have F x e := finite_quotient_iff.2 ((exists_maximalIdeal_pow_eq_of_principal (valRingBelow L A)
    inferInstance (Ideal.span {x}) (by simpa)).imp fun _ ↦ Eq.ge)
  obtain ⟨c⟩ := mul_ne_zero (NeZero.ne ↑l) hπ.ne_zero,
    (isUniformiser_iff_irreducible.2 ⟨_, hπ⟩).val_lt_one, hπ.ne_zero
  let w := Units.mk0 (valuationVia L A (l * π)) (by simpa)
  obtain ⟨k⟩ := (by simpa [w] : w < A l), F l (by simp), F _ c
  let r := (Units.map (Ideal.Quotient.mk (Ideal.span {l * π})).1).toAdditive.toIntLinearMap
  choose d hd using fun a : r.ker ↦
    (mk_span_eq_iff_dvd_sub.1 congr($(a.2).1)).imp fun _ ↦ eq_add_of_sub_eq'
  let j x : r.ker := ⟨.ofMul (isUnit_of_mem_nonunits_one_sub_self (1 + l * π * x) (by
    simp [hπ.1])).unit, by ext; simp [r]⟩
  rw [cokerKerIndex_natCast_eq_of_ne_zero (y.trans (.symm (.ofBijective ((Units.map (algebraMap _
    L).1).toAdditive.coprod (zmultiplesHom _ (.ofMul (.mk0 π (by simpa))))) ⟨.of_ker _ fun ⟨u,
    n⟩ e ↦ by simp_all [Units.ext_iff, (by simpa [← (valRingBelow L A).valuation_eq_one_iff, hπ.1,
    zpow_eq_one_iff_right₀] using congr(valRingBelow L A ($e).toMul.1) : n = 0)], fun a ↦
    have ⟨n, u, _⟩ := h.5.exists_units_eq_smul_zpow_of_irreducible hπ a.toMul.ne_zero
    ⟨(u, n), by aesop⟩⟩))).toIntLinearEquiv.1 (by simp), cokerKerIndex_mul_of_exact _ _
    inr_injective .inr_fst fst_surjective cokerKerIndex_eq_pow_finrank.1,
    cokerKerIndex_eq_pow_finrank.2, ← cokerKerIndex_natCast_eq_of_ne_zero r.ker.subtype
    (by simpa using! r.toAddMonoidHom.ker.index_ne_zero_of_finite), cokerKerIndex, ker_eq_bot'.2
    fun (a : r.ker) e ↦ by ext; exact (algebraMap ..).injective (eq_of_pow_eq_one_of_val_sub_lt (by
    simpa [← map_pow] using congr($e.1.toMul.1.1)) (by simp) (k.trans_le' (by simpa [hd, w] using
    (mul_le_of_le_one_right' (d a).2)))), Nat.card_congr (Function.Exact.linearEquivOfSurjective
    (g := (AddMonoidHom.mk' (Ideal.Quotient.mk (Ideal.span {↑l}) ∘ d)
    fun a b ↦ mk_span_eq_iff_dvd_sub.2 ⟨d a * d b * π, mul_left_cancel₀ c (by
    grind -linarith [show _ * _ = _ from hd (a + b)])⟩).toIntLinearMap) (.of_comp_of_mem_range (by
    ext; simpa using mul_eq_zero_of_left (mk_singleton_self _) _) fun a e ↦ ?_) (Quot.ind fun x ↦
    ⟨_, congrArg _ (by simpa [j, c] using (hd (j x)).symm)⟩)).toEquiv]
  simp
  obtain ⟨z, E, s⟩ : ∃ z, algebraMap L Ω a.1.toMul.1 = z ^ l ∧ A (z - 1) ≤ w
  · by_contra! N
    have := by simpa [hd] using N 1
    apply (dvd_iff_valuationVia_le.1 ((eq_zero_iff_dvd ..).1 e)).not_gt
    simpa [w, derivative_pow, field, *] using ((h.2.1 (C (algebraMap L Ω a.1.toMul.1) -
      X ^ l)).eval_derivative_div_eval_of_ne_zero (x := 1) (by simp [*]) ▸
      (A.valuation.ltAddSubgroup w⁻¹).multiset_sum_mem _ (by simp_all [inv_strictAnti₀,
      ↓Multiset.forall_mem_map_iff, map_sub_swap]) :)
  obtain ⟨x, rfl⟩ := h.1.1.3.1 z fun g ↦ eq_of_div_eq_one (eq_of_pow_eq_one_of_val_sub_lt (by
    simp [div_pow, ← smul_pow', ← E]) (by simp) (((map_sub_le _ (decompGroup.val_smul (h.4 g) _ ▸ s)
    s).trans_lt k).trans_eq' (by simp [map_eq_of_sub_lt _ (s.trans_lt (k.trans_le (by simp))),
    ← A.valuation.zero_iff, smul_sub])))
  use j ⟨(x - 1) / (l * π), by simp_all [w, field]⟩
  ext; simp_all [j, mul_div_cancel₀, ← map_pow, -hd]

/-- Let L/K be Galois of prime degree l, U ⊂ L^× Galois-stable, V = U ∩ K^×, and gz/z ∈ U for
all g only if z ∈ K^×U. With q_A = #(A/lA)/#A[l] and q_V ≠ 0, [V : N U]^{l−1} q_U = q_V^l. -/
lemma tate_index_formula_norm {K L} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L] l (hL : finrank K L = l) [Fact l.Prime] (U : Subgroup Lˣ) (V : Subgroup Kˣ)
  (hV : V = U.comap (Units.map (algebraMap K L))) (hU : ∀ g : Gal(L/K), ∀ y ∈ U, g • y ∈ U)
  (h : ∀ z, (∀ g : Gal(L/K), g • z / z ∈ U) → ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U) (iV :
  cokerKerIndex (l : End ℤ (Additive V)) ≠ 0) : (U.map (Units.map (Algebra.norm K))).relIndex V ^ (l
  - 1) * cokerKerIndex (l : End ℤ (Additive U)) = cokerKerIndex (l : End ℤ (Additive V)) ^ l := by
  subst_vars; have i@⟨g, hg⟩ := isCyclic_of_prime_card (card_aut_eq_finrank K L)
  let σ : _ →* End ℤ (Additive U) := unitsRep.subrepresentation U.toAddSubgroup.toIntSubmodule hU
  rw [Subgroup.relIndex, ← MonoidHom.domRestrict_range, MonoidHom.subgroupOf_range_eq_of_le _ ?n]
  use Tate.index_formula (MonoidHom.codRestrict _ (U.comap _) (?n ⟨·,
    rfl⟩)).toAdditive.toIntLinearMap (MonoidHom.subgroupComap ..).toAdditive.toIntLinearMap (σ g) iV
    (by simp [← card_aut_eq_finrank, ← map_pow]) (.restrictPreimage _ (Units.map_injective
    (by aesop_cat))) (fun y ↦ sub_eq_zero.trans ⟨fun a ↦
    (Set.range_restrictPreimage ..).ge (((ofBase_bijective _).2 ⟨y.1, fun k ↦
    Units.ext (smul_eq_self_of_mem_zpowers (hg k) congr($a.1.1))⟩).imp fun _ ↦ Subtype.ext_iff.1),
    (·.choose_spec ▸ by ext; apply g.commutes)⟩) (.of_comp_of_mem_range (by ext; simp [field]; apply
    norm_eq_of_algEquiv) fun y hy ↦ (exists_div_of_norm_eq_one hg (x := y.1) congr($hy.1)).rec fun z
    e ↦ ⟨.ofMul ⟨_, (h z (hg · |> mem_powers_iff_mem_zpowers.2 |>.rec fun n E ↦
    E ▸ n.rec (by simp) fun _ I ↦ Eq.subst (by ext; simp [← e, pow_succ', field]) (div_mem (hU g _
    I) y.2))).choose_spec⟩, by ext; erw [← e, Units.val_mul, Units.coe_smul, Units.val_mul]; simp
    [field]⟩) (by ext; apply Algebra.norm_algebraMap)
  simp [LE.le]; intros
  convert (∏ g, ⟨_, hU g _ ‹_›⟩ : U).2; ext; simp [norm_eq_prod_automorphisms]

attribute [-simp] LinearMap.map_smul_of_tower Pi.smul_apply one_apply zsmul_eq_mul

variable {Γ K Ω L : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω] [Field L] [Algebra K L] [Algebra L Ω]

lemma IsProGalois.of_fixingSubgroup_eq [IsScalarTower K L Ω] {U} (h :
  fixingSubgroup Γ (.range (algebraMap L Ω)) = U) [@IsClosed Γ _ U] :
  IsProGalois U L Ω := { tower_top_of_isGalois K .., (inferInstance : IsProGalois ..) with
    commutes.1 := by simp +contextual [Algebra.smul_def, ← h, mem_fixingSubgroup_iff]
    isInvariant.1 := h ▸ (fixedFieldOf_fixingSubgroup (algHom ..).fieldRange).le }

attribute [local simp] DiscreteModule.sum Finset.smul_sum mul_eq_one_iff_inv_eq smul_sub sub_smul

/-- Let χ : Γ → ℚ/ℤ have open kernel U. A class in H²(Γ, Ω^×) restricts to zero on U exactly
when it is a symbol (χ, w), w ∈ K^×; and (χ, w) = 0 exactly when w is a norm from the fixed
field of U.

Known result: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient. -/
lemma QZChar.cyclicClass_spec χ : let U := OpenSubgroup.mk _ (isOpen_ker χ); (∀ x,
    (unitsModule Γ).resH2 U x = 0 ↔ ∃ w : Kˣ, x = cyclicClass _ χ (ofBase Γ Ω (.ofMul w))) ∧ ∀ w :
    (unitsModule Γ).H0, cyclicClass _ χ w = 0 ↔ ∃ y, corestrictH0 U y =
    w.1 := by intro U; refine have := U.1.quotient_finite_of_isOpen U.2
  let f q := (kerLift (toHom χ) q).toAdd
  (Finite.exists_max (QZ.fracRep ∘ f)).elim fun γ hγ ↦ let c p q := QZ.carry (f p) (f q)
    have E q : c q γ = 1 - ite (q = 1) 1 0 :=
      sub_eq_zero.1 (Int.abs_lt_one_iff.1 (by qify [c]; grind
      [mul_eq_right, QZ.fracRep, Equiv.injective, kerLift_injective, toAdd_mul, hγ (q * γ)]))
    let M := unitsModule Γ; let D := funLeft ℤ M (· * γ) - 1
      have H f := (hilbert90_unitsRep (M.shapiroZ1 U f)).elim (shapiro_H1 U f)
      have j g : χ.1 g = f g ∧ ∀ q, g • q = mk' U g * q := by tauto
      have k p q r (m : M) : c p (q * r) • m = (c p q - (c q r - c (p * q) r)) • m := ?_
      have S := (mulRight_bijective γ).sum_comp
      ⟨Quot.ind fun x ↦
        ⟨(have ⟨a, _, e⟩ := (ker_mkQ _).le <| shapiroH2_injective U · (a₁ := (M.const _).mapH2 ⟦x⟧)
        (H ⟨D ∘ a, ?_, (eq_of_eq congr(D $(e · ·)) ?_)⟩).rec fun ε t ↦ have P (v : Γ ⧸ U.1 → ℤ) l :=
            (congr($(S (v • a l)) - M.sum _
            (v • $(t l)) + $((mulLeft_bijective ↑l).sum_comp (v • ρ _ l ε))))
          ((ofBase_bijective _).2 ⟨M.sum _ ε, (eq_of_eq congr($(P 1 ·)) ?_)⟩).imp fun _ ↦
            (·.substr <| (Submodule.Quotient.eq _).2 ⟨fun g ↦ a g γ - M.ρ g (M.sum _ (c g • ε)), ?_,
            fun g l ↦ eq_of_eq congr($(e g l) γ + c g l • $(P 1 (g * l)) - M.ρ
            g $(by simpa [*] using P (c g) l)) ?_⟩)), (·.choose_spec ▸ resH2_cyclicClass_eq_zero
        (one_smul ..) ?_)⟩, fun w ↦ ⟨(have ⟨a, _, e⟩ := (ker_mkQ _).le ·
        (H ⟨fun g q ↦ c g (g⁻¹ • q) • w - a g, ?_, (eq_of_eq congr(fun _ ↦ -$(e · ·)) ?_)⟩).rec
          fun η t ↦ (shapiro_H0 U ⟨(w - c · γ • w.1) - D η, (eq_of_eq congr(D $(t ·)) ?_)⟩).imp (by
          simp_all [corestrictH0, D, U])), (cyclicClass_corestrictH0 U χ _ ·.choose_spec 0 (bot_le
        (a := ((cyclicClass _).flip _).ker) (Subtype.ext (_root_.funext (·.2)))).symm ▸ ?_)⟩⟩ <;>
  (try fun_prop) <;> simp +zetaDelta [funext_iff, DiscreteModule.const, j,
  mul_assoc, M.H0.coe_mem _ _] <;> intros <;> match_scalars <;> qify [mul_one] <;> abel_nf

variable [IsScalarTower K L Ω] [IsAlgClosed Ω] [Module.Finite K L] [Algebra.IsSeparable K L]

lemma corestrictH0_ofBase_eq_norm U [J : IsProGalois U.1 L Ω] (y : Lˣ) :
    (unitsModule Γ).corestrictH0 U (ofBase _ Ω (.ofMul y)) =
  ofBase Γ Ω (.ofMul (y.map (Algebra.norm K))) := DiscreteUnits.ext (by
  simp [corestrictH0, norm_eq_prod_embeddings]; apply Finset.prod_bijective (toAlgHom K Ω ·.out
    |>.domRestrict L) (Function.Injective.bijective_of_nat_card_le (fun _ _ H ↦ out_equiv_out.1
    (leftRel_apply.2 (eq_fixingSubgroup_of_isProGalois.1.ge (by simpa [mem_fixingSubgroup_iff,
    mul_smul, inv_smul_eq_iff] using! (congr($H ·).symm)))))
    ((card_algHom_le_finrank ..).trans eq_fixingSubgroup_of_isProGalois.2.ge)) <;> aesop)

lemma cyclicClass_eq_zero_iff_norm {χ : QZChar Γ} [J : IsProGalois (QZChar.ker χ) L Ω] x :
    cyclicClass _ χ (ofBase Γ Ω (.ofMul x)) = 0 ↔ ∃ z : Lˣ, z.map (Algebra.norm K) = x := by
  erw [(QZChar.cyclicClass_spec χ).2, (ofBase_bijective _).2.exists]
  simp [corestrictH0_ofBase_eq_norm, DiscreteUnits.ext_iff, Units.ext_iff]
end

-- part: Lib.ClassField.LocalDuality.RealPlaceSymbols
section
/-! Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles
(known result; see Lib.ClassField.LocalDuality.CrystallineDuality).

Part of: Local class field theory: invariant of the Brauer group, Artin map, norms, tame symbol
(known result; see Lib.ClassField.Local.ArtinMapAtPlace).

This file: Invariant map Br(k) ≅ Q/Z of a henselian local field and its functoriality. Number of
Kummer cocycles; finiteness of local 1-cocycles of finite modules. The local Artin map sends
uniformisers to geometric Frobenius elements. Order bound for orthogonal cocycle groups, the
inequality for local Tate duality. Complex conjugations; symbol of a totally positive element dies
keeping real places real. -/

namespace IsLocalGalois

open Function DiscreteModule Subgroup QZChar QuotientGroup QZ Classical DiscreteUnits AddMonoidHom
variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] (V : OpenSubgroup Γ) {A : ValuationSubring Ω} [L : IsLocalGalois Γ k A]

attribute [-simp] map_smul

/-- Over a local field k, let V be open normal in Γ and β in H²(Γ, Ω^×) die on V, with nβ = 0 only
for n divisible by [Γ : V]. Then every class that dies on V is a multiple of β. -/
lemma mem_zmultiples_of_resH2_eq_zero [V.Normal] {β x} (b : (unitsModule Γ).resH2 V β = 0) (H : ∀ n,
    n • β = 0 → V.index ∣ n) (a : resH2 _ V x = 0) : x ∈ AddSubgroup.zmultiples β := by
  wlog h : Fact V.index.Prime
  · exact mem_of_prime_step _ a fun U W _ hU v hl s m e ↦
     let V' := (V.comap _ (subgroupIncl U).2).comap _ (subgroupIncl W).2
     (this W (L := (of_finite _).1) ((map_nsmul ..).trans (index_smul_eq_zero_of_resH2 V'
       (resH2_swap congr(resH2 _ _ $(resH2_swap (congrArg _ b)))))) (fun n h ↦ by
     erw [← mul_dvd_mul_iff_left (a := V'.index * U.index) (by simp), mul_right_comm,
       relIndex_mul_index v, relIndex_mul_index hU, mul_right_comm]
     apply H; simpa [mul_nsmul] using index_smul_eq_zero_of_resH2 U (by simpa)) e ⟨hl⟩).elim fun j
       e ↦ ⟨s + j • V'.index • β, by bound, by simpa [← sub_sub] using! e.symm⟩
  obtain ⟨⟨F⟩, ⟨⟩, ψ, rfl⟩ := of_finite V, V,
    exists_ker_eq_of_isCyclic V (isCyclic_of_prime_card (hp := h) rfl)
  rw [(cyclicClass_spec ψ).1] at *
  obtain ⟨⟨y, rfl⟩, ⟨x, rfl⟩, e⟩ := b, a,
    cokerKerIndex_local_units F (ker ψ).index topEquiv.toAdditive
  let f := lift (map _ ⊤) ((cyclicClass _ ψ).comp (ofBase Γ Ω)).toMultiplicativeRight fun _ ⟨_, _,
    e⟩ ↦ (cyclicClass_eq_zero_iff_norm _).2 ⟨_, e⟩
  exact (f.map_zpowers y).le ⟨x, mem_zpowers_of_prime_card (hp := h) (pow_left_injective
    h.1.pred_pos.ne' (by qify; erw [← mul_left_inj' e.1, ← index, ← relIndex_top_right,
    tate_index_formula_norm (index _)] <;> simp [*, finrank_fixedFieldOf,
    Ne, ↓cokerKerIndex_local_units L _ topEquiv.toAdditive, mul_pow, ← mul_assoc,
    pow_sub_one_mul NeZero.out])) (h.1.not_dvd_one <| H 1 <| by simpa using! congrArg f ·), rfl⟩

/-- For a local field k, the map c = `classOfInv` from ℚ/ℤ to H²(Γ, Ω^×) is injective, and
the symbol (χ, w) equals n·c(χ(φ)) for unramified χ, any Frobenius φ and any Γ-invariant w
of order n. -/
lemma isClassOfInv_classOfInv : IsClassOfInv Γ k A (classOfInv Γ k A) := epsilon_spec (by
  have hp := L.exists_isUniformiser.choose_spec.ordRat_eq_one L; set p := ofBase (K := k) Γ Ω _
  choose c hc hu using existsUnique_unramified_char L.frobenius_spec.1.choose_spec
  have d {χ} (u : inertiaGroup Γ A ≤ QZChar.ker χ) w (n : ℤ) (e : ordRat k A w.1 = n) h :
    ↑(ker χ).index ∣ n := (((cyclicClass_spec χ).2 w).1 h).elim fun y h ↦
    (exists_ordRat_eq_intCast (y.2 ⟨·, u ·⟩)).imp fun j hj ↦ by qify; erw [← e, ← h, corestrictH0,
    LinearMap.sum_apply, map_sum, Finset.sum_eq_card_nsmul (b := ↑j)] <;> simp [index,
    Fintype.card_eq_nat_card, ← hj, eq_iff, ↓L.ordRat_eq_zero, decompGroup.val_smul, L.4]
  use ((cyclicClass _).flip p).comp (.mk' c fun a b ↦ (hu _ _ (by simp_all)).symm),
    .of_ker _ fun r h ↦ (hc r).2 ▸ (index_eq_one.1 (Nat.dvd_one.1
    (mod_cast d (hc r).1 p 1 hp h))).ge ⟨⟩, fun χ u φ f w n hn ↦ ?_
  have s w := ((ofBase_bijective Γ).2 w).choose_spec ▸ ((cyclicClass_spec χ).1 _).2 ⟨_, rfl⟩
  obtain ⟨j, e⟩ :=
    mem_zmultiples_of_resH2_eq_zero _ (s p) (fun n _ ↦ by zify; simp [d u (n • p), *]) (s w)
  simp [← hu (χ.1 φ) χ ⟨u, (toHom χ).eq_iff.2 (u _ (f.inv_mul (choose_spec _)))⟩, ← e,
    ← addOrderOf_dvd_sub_iff_zsmul_eq_zsmul]
  grw [addOrderOf_dvd_of_nsmul_eq_zero (index_smul_eq_zero_of_resH2 _ (s p)),
    d u (j • p - w)] <;> simp [*])

/-- Let k, k' be local, j : Ω → Ω' equivariant along φ : Γ' → Γ, j⁻¹A' = A, q' = q^f, and ord w
= 1, ord' j(w) = e for a Γ-fixed w. Then (φ, j) sends the class in H²(Γ, Ω^×) of invariant r
to that of invariant ef·r. -/
lemma pairMapH2_classOfInv {Γ' k' Ω' : Type} [Group Γ'] [TopologicalSpace Γ'] [Field k'] [Field Ω']
  [Algebra k' Ω'] [MulSemiringAction Γ' Ω'] {A'} [L' : IsLocalGalois Γ' k' A'] (φ : Γ' →ₜ* Γ) (j :
  Ω →+* Ω') (hA : A'.comap j = A) (H : ∀ g x, j (φ g • x) = g • j x) {e f : ℕ} {w :
  (unitsModule Γ).H0} (he : ordRat k A w = 1 ∧ ordRat k' A' ((Units.map j).toAdditive w.1) =
  e) (hf : residueCard k' A' = residueCard k A ^ f) r : (pairMapH2 φ (Units.map
  j).toAdditive.toIntLinearMap) (classOfInv Γ k A r) = classOfInv _ k' A' ((e * f) • r) := by
  obtain ⟨rfl, ⟨_, s⟩, _, t⟩ := hA, L.frobenius_spec.1, L'.frobenius_spec.1
  obtain ⟨χ, ⟨⟨c, rfl⟩⟩⟩ := existsUnique_unramified_char s r
  rw [mul_smul, map_nsmul, ← (isClassOfInv_classOfInv.2 _ c _ s _ 1 he.1).trans (one_zsmul _)]
  convert! isClassOfInv_classOfInv.2 (comap φ χ) (fun _ ↦ c _ ∘ .map H) _ t ⟨_, _⟩ e he.2
  exacts [congr(⟦⟨fun _ ↦ $(map_zsmul ..), _⟩⟧), (map_pow ..).symm.trans ((toHom χ).eq_iff.2 (c _
    ((hf ▸ t.map H).inv_mul (s.pow f)))), fun g ↦ ext (H .. ▸ congr(j $(w.2 _).1):)]

/-- Restriction multiplies the invariant by the degree: for k local and V open in Γ with fixed
field k'', the Brauer class `classOfInv` of r ∈ ℚ/ℤ for k restricts to the class of
[Γ:V]·r for k''. -/
lemma _root_.resH2_classOfInv {r} : (unitsModule Γ).resH2 V (classOfInv Γ k A r) = classOfInv _
  (fixedFieldOf V.1) A (V.index • r) := have p :=
    L.exists_isUniformiser.choose_spec.ordRat_eq_one L; (of_finite V).rec fun _ ⟨⟨_, _,
  ⟨h, q, _⟩, _⟩, _⟩ ↦ h ▸ pairMapH2_classOfInv _ (.id _) rfl (by tauto) ⟨p, by simp [*]⟩ q _

lemma resH2_classOfInv_eq_zero {r} (h : V.index • r = 0) : (unitsModule Γ).resH2 V
    (classOfInv Γ k A r) = 0 := resH2_classOfInv V ▸ h ▸ map_zero _

/-- Brauer group of a local field, ℚ/ℤ ≅ Br(k): for a henselian local field k of characteristic
0 with absolute Galois group Γ, the map `classOfInv` from ℚ/ℤ to H²(Γ, Ω^×) is bijective.

Known result: Local class field theory: invariant of the Brauer group, Artin map, norms, tame
symbol. -/
lemma classOfInv_bijective : Bijective (classOfInv Γ k A) := ⟨isClassOfInv_classOfInv.1, Quot.ind
  fun ⟨_, c, q⟩ ↦ (exists_openNormalSubgroup_apply_eq (c.comp continuous_swap)).elim fun W w ↦
  (range _).zmultiples_le_of_mem ⟨@ofZMod W.index ⟨by simp⟩ 1, rfl⟩ (mem_zmultiples_of_resH2_eq_zero
  _ (resH2_classOfInv_eq_zero _ (by simp [← map_nsmul])) (by simp [← map_nsmul, map_eq_zero_iff,
  isClassOfInv_classOfInv.1, ZMod.natCast_eq_zero_iff]) ((Submodule.ker_mkQ
  _).ge ⟨_, continuous_const, fun g k ↦ (w k k.2 g).trans (by simpa using! q g 1 1)⟩))⟩

/-- For a local field k and an open subgroup V of its Galois group Γ, every class in H²(V, Ω^×)
is the restriction of the class in H²(Γ, Ω^×) with invariant r, for some r in ℚ/ℤ. -/
lemma exists_resH2_classOfInv_eq y : ∃ r, (unitsModule Γ).resH2 V (classOfInv Γ k A r) = y :=
  ((of_finite V).1.classOfInv_bijective.2.comp
  (DivisibleBy.surjective_smul _ ℤ (by simp)) y).imp fun _ ↦ (resH2_classOfInv V).trans

open Nat HasEnoughRootsOfUnity NeZero LinearMap CommGroup Ideal
variable {A : ValuationSubring Ω} [h : IsLocalGalois Γ k A]
include h

/-- Kummer theory: for a local field k with integers O and n ≥ 1, the continuous 1-cocycles Γ →
Ω^× killed by n, that is Z¹(Γ, μ_n), form a finite group of order n²·#(O/n). -/
lemma card_kummer_cocycles (n : ℕ) [NeZero n] : let c := .card (n :
    Module.End ℤ (Z1 (unitsModule Γ).ρ)).ker
  0 < c ∧ c = n ^ 2 * .card (_ ⧸ span {(n : valRingBelow k A)}) := by
  have s : Surjective (unitsModule Γ).coboundary := (hilbert90_unitsRep · |>.imp (by aesop))
  have ⟨a, b⟩ :=
    cokerKerIndex_local_units h n (.symm (.ofBijective _ (DiscreteUnits.ofBase_bijective Γ)))
  have H := cokerKerIndex_mul_of_exact _ _ (Submodule.subtype_injective _) (by
    simp [Exact, Subtype.ext_iff, funext_iff]) s a
  erw [b, cokerKerIndex, cokerKerIndex, LinearMap.range_eq_top.2 (·.exists_nsmul out),
    LinearMap.range_eq_top.2 (.of_comp
    ((funext (map_nsmul _ n)).subst (s.comp (·.exists_nsmul out)))), natCard_rootsOfUnity] at H
  qify [card_unique] at *; grind

/-- If k is a local field with absolute Galois group Γ (`IsLocalGalois`), then for every finite
discrete Γ-module M over a commutative ring R, the module Z¹(Γ, M) of continuous 1-cocycles
is finite. -/
lemma finite_Z1_local ⦃R⦄ [CommRing R] (M : DiscreteModule R Γ) [Finite M] : Finite (Z1 M.ρ) := by
  have ⟨⟨U, _⟩, w⟩ := exists_openNormalSubgroup_apply_eq M.cartierDual.continuous
  have e := equivFinOfCardPos ((of_finite U).1.card_kummer_cocycles (.card M)).1.ne'
  refine .of_injective (fun ⟨z, _, d⟩ ↦ ((z ·.out : _ ⧸ U.1 → _), fun f : _ →+ _ ↦ e ⟨⟨(f <| z ·),
    by fun_prop, fun g h ↦ by simpa [d] using! congr($(w _ g.2 f) (M.ρ g _)).symm⟩,
    by ext; simp [← map_nsmul]⟩)) ?_
  rintro ⟨_, _, a⟩ ⟨_, _, b⟩ h; ext g; have ⟨u, v⟩ := QuotientGroup.mk_out_eq_mul U g
  simpa [a, b, v, Equiv.injective _ ((forall_apply_eq_apply_iff (Multiplicative M)).1
    (congr($(e.injective congr($h.2 ·.toAdditiveRight)).1.1 u)))] using congr($h.1 g)

end IsLocalGalois

open QuotientGroup Units QZChar Complex NeZero NumberField DiscreteUnits

lemma IsLocalArtin.exists_frob_of_isUniformiser {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ]
  [Field k] [Field Ω] [Algebra k Ω] [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [L :
  IsLocalGalois Γ k A] {π : kˣ} {F} (hF : IsLocalArtin Γ k A F) (h : IsUniformiser A π.1) : ∃ φ : Γ,
  IsFrob A (residueCard k A) φ ∧ F π = φ⁻¹ := L.frobenius_spec.1.elim fun φ f ↦
  (QZChar.mem_of_forall_abelianLift (continuous_mk.isClosedMap _ isClosed_inertiaGroup) (H := .map
  (mk' _) (inertiaGroup Γ A)) (φ⁻¹ / F π) fun _ _ ↦ Multiplicative.ext (L.isClassOfInv_classOfInv.1
  (by simp_all [IsLocalArtin, h.ordRat_eq_one, L.isClassOfInv_classOfInv.2
  _ _ _ f _ 1]))).rec fun _ e ↦ ⟨_, by simpa using f.mul_iff.2 e.1, by aesop⟩

section


open DiscreteUnits DFunLike DiscreteModule QZChar NeZero QZ Ideal AddSubgroup IsLocalGalois Nat
  Function
variable {Γ k Ω : Type} [Group Γ] [TopologicalSpace Γ] [Field k] [Field Ω] [Algebra k Ω]
  [MulSemiringAction Γ Ω] {A : ValuationSubring Ω} [J : IsLocalGalois Γ k A] {l r : ℕ}
  [Fact l.Prime] {R S} [CommRing R] [CommRing S] {M : DiscreteModule R Γ} {N : DiscreteModule S Γ}

lemma char_eq_zero_of_cyclicClass_eq_zero {χ} (h : ∀ w : Additive kˣ,
  cyclicClass _ χ (ofBase Γ Ω w) = 0) g : χ.1 g = 0 :=
  isClassOfInv_classOfInv.1 ((((cyclicClass_spec χ).1 _).1 (resH2_classOfInv_eq_zero _ (by
    simpa using! (ker χ).pow_index_mem g))).choose_spec.trans (by simp [h]))

/-- Let k be local, b : M × N → Ω^× equivariant, i·[Γ:U] act as the identity on M, and X, Y
contain the coboundaries and a corestriction of each cocycle of X', Y'. If X' contains the
cup product annihilator of Y' over U, then X contains that of Y. -/
lemma DiscreteModule.HoldsCorestrictions.pairingAnnihilator_le {U X X' Y Y'} {i : ℤ} (g :
  HoldsCorestrictions U X' X) (h : HoldsCorestrictions U Y' Y) (c : ∀ m : M, i • U.index • m =
  m) {b} e (a : pairingAnnihilator (cupProduct (unitsModule _) _ _ b (e ·)).flip Y' ≤ X') :
  pairingAnnihilator (cupProduct (unitsModule Γ) M N b e).flip Y ≤ X := fun z hz ↦ (g.2 ((pairMapZ1
  _ .id) z) (a fun y hy ↦ (h.2 _ hy).rec fun F ⟨f, o⟩ ↦ (exists_resH2_classOfInv_eq U (shapiroH2 U
  (cupProduct _ _ (N.funModule _) (.mk' (b · |>.compLeft _) (by bound)) (by simp [funext_iff, e]) z
  F))).elim fun _ s ↦ (s.trans congr(⟦⟨fun _ ↦ b _ $(f ▸ funModule_apply_one ..), _⟩⟧)).symm.trans
  (resH2_classOfInv_eq_zero U (isClassOfInv_classOfInv.1 (by
    rw [map_zero, ← hz _ o, map_nsmul, ← mapH2_sum_eq_index_smul U _ _ s]
    exact congr(⟦$(by simp [← (sum ..).isIntertwining]; simp [sum])⟧)))))).rec fun F ⟨f, o⟩ ↦ by
  have ⟨n, e⟩ := shapiro_H1 U (F - (const ..).mapZ1 z) 0 (by simpa using! congr($f.1 ·))
  convert zsmul_mem (sub_mem o (g.1 (M.sum _ n))) i
  ext g; rw [← c (z.1 g), index_smul_eq_sum_const]
  simpa [← (sum ..).isIntertwining] using! congr(i • M.sum _ (F.1 g - $(e g)))

/-- Let k be local, #(O/l) = l^d, and M finite, killed by l^r and fixed by Q, every g having
some g^(l^i) in Q. Then groups X ⊂ Z¹(Hom(M, Ω^×)) and W ⊂ Z¹(M), orthogonal under the cup
product, have #X·#W ≤ (#M)^(2+d).

Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. -/
lemma card_mul_card_le_of_orthogonal {d} Q (hd : .card (_ ⧸ span {(l : valRingBelow k A)}) = l ^ d)
  (c : FiniteKilledFixedInj (l ^ r) Q 1 0 M) (p : ∀ g, ∃ i, g ^ l ^ i ∈ Q) : have := c.1; ∀ X W, X ≤
    pairingAnnihilator M.evalCup.flip W → Nat.card X * .card W ≤ .card M ^ (2 + d) := by
  obtain ⟨⟨⟨⟩, b⟩⟩ := (J.card_kummer_cocycles l).imp_left card_pos_iff.1, J.finite_Z1_local,
    (unitsModule Γ).continuous
  refine M.devissage_induction rfl ⊤ Q (by simpa) (fun M _ ⟨_, c, t,
    _⟩ X W h ↦ have := AddCommGroup.zmodModule c
    have e := Module.finBasis (ZMod l) M; ?_) (fun {_ _ _ ι π} s c H G X W h ↦ ?_) c
  grw [card_le_of_le h, card_pairingAnnihilator_mul_card _ (.ofBijective _ classOfInv_bijective),
    card_eq_one.2 (bot_unique fun y hy ↦ Subtype.ext (funext ?_)), mul_one, card_congr
    e.equivFun.toEquiv, card_fun, card_zmod, pow_right_comm, pow_add, ← hd, ← b, ← card_fun]
  exact card_le_card_of_injective (fun z j ↦ ⟨pairMapZ1 (.id _) ⟨⟨(· (e j)), by simp⟩, by simp⟩ (by
    simp [t]) z, by ext; simp [← map_nsmul, c]⟩) fun x y h ↦ by ext g : 3; exact (((((x.1 g).eqLocus
    _).toZModSubmodule l).eq_top_iff_forall_basis_mem e).2 fun j ↦ congr(($h j).1.1 g)).ge ⟨⟩
  exact (eq_zero_of_forall_hom_eq_zero <| (bijective_ofZMod_comp c).2.forall.2 fun j ↦
    char_eq_zero_of_cyclicClass_eq_zero (χ := ofZModCocycle l ⟨j ∘ y.1,
    y.2.imp (by fun_prop) (by simp_all)⟩) (fun x ↦ (exists_nsmul _ out).rec fun a u ↦ neg_eq_zero.1
    ((kummer_cup_eq_neg_cyclicClass u _ _ (by simp [t])).symm.trans (ext_iff.1 hy.1 ⟨fun g ↦ .mk'
    (fun m ↦ (j m).val • (unitsRep g a - a)) (by simp [ZMod.val_add, add_smul, ← nsmul_eq_mod_nsmul,
    smul_sub l, ← map_nsmul, u, DiscreteUnits.ext_iff]), .congr (by simp; fun_prop)
    (leftInverse_invFun coe_injective ∘' _), by simp [ext_iff, t, smul_sub]⟩))) ·)
  obtain ⟨⟨⟩, ⟨⟩, ⟨⟩⟩ := c, c.of_isShortExact s
  grw [(π.cartierDualMap.card_eq_card_comap_mul_card_map (π := ι.cartierDualMap) ?_
    (.of_comp_of_mem_range ?_ (.imp (fun _ ↦ DFunLike.ext _ _) ∘ exists_extend _ · ∘ ?_)) X).trans
    (mul_comm ..), ι.card_eq_card_comap_mul_card_map s.1 s.2.1 W, mul_mul_mul_comm, G, H,
    s.card_eq_mul, mul_pow] <;> simp [s.2.2.forall, s.2.1 _, Injective, ext_iff, LE.le, (s.2.1 _).2,
    funext_iff, pairingAnnihilator, -Subtype.forall, -Subtype.exists] <;> exact fun _ o _ m ↦
    .trans congr(⟦$(by simp [ι.isIntertwining, π.isIntertwining])⟧) (h o _ m)

/-- Local field, M finite, [Γ:U] prime to #M. Let X' ⊂ Z¹(U, M^*), W' ⊂ Z¹(U, M) be orthogonal
with #X'·#W' maximal among orthogonal pairs; let X, W contain the coboundaries and a
corestriction of each member. Then #L^⊥·#L divides #W·#X for all L ⊂ Z¹(Γ, M^*).

Known result: Local Tate duality in degree 1, as an upper bound for orthogonal groups of
cocycles. -/
lemma DiscreteModule.local_duality_card_dvd [Finite M] {U X W X' W'} (hX :
  M.cartierDual.HoldsCorestrictions U X' X) (hW : M.HoldsCorestrictions U W' W) (c :
  (Nat.card M).Coprime U.index) (o : W' ≤ pairingAnnihilator (M.restrictTo U).evalCup X') (H :
  ∀ Y Z, Y ≤ pairingAnnihilator (M.restrictTo U).evalCup.flip Z → Nat.card Y * .card Z ≤ .card X' *
  .card W') L : Nat.card (pairingAnnihilator M.evalCup L) * .card L ∣ .card W * .card X := by
  obtain ⟨e, k⟩ := AddEquiv.ofBijective _ J.classOfInv_bijective, (nsmulCoprime c).left_inv,
    (of_finite U).1.finite_Z1_local
  grw [card_pairingAnnihilator_mul_card _ e, card_dvd_of_le (inf_le_of_left_le (le_inf le_rfl fun x
    e ↦ hX.pairingAnnihilator_le hW (fun m ↦ DFunLike.ext _ _ (by simpa using congr(m $(k ·))))
    (by simp) (eq_of_le_of_card_ge (by tauto) (le_of_mul_le_mul_right (H _ _ le_rfl) card_pos)).ge
    fun _ _ ↦ ext_iff.1 e _)), ← card_pairingAnnihilator_mul_card _ e, card_dvd_of_le fun w e ↦
    hW.pairingAnnihilator_le hX k (by simp) (fun w e ↦ (eq_of_le_of_card_ge o
    (le_of_mul_le_mul_left (H _ _ (by tauto)) (@card_pos X' _ _))).ge (neg_eq_zero.1 <|
    (cupProduct_flip ..).symm.trans <| e · ·)) ((cupProduct_flip ..).trans <| by simpa using e · ·)]

end

variable {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] {K' : Type} [Field K'] [t :
  IsTotallyComplex K'] (x : K') {c : Γ} [Algebra K Ω] [MulSemiringAction Γ Ω] [G :
  IsProGalois Γ K Ω]

lemma isTotallyPositive_of_isTotallyComplex : IsTotallyPositive x :=
  (absurd (by ext; simp) <| t.complexEmbedding_not_isReal <| ofRealHom.comp ·)

lemma isReal_comp_algebraMap {j} (h : ∀ x, j (c • x) = star (j x)) :
    ComplexEmbedding.IsReal (.comp j (algebraMap K Ω)) := by ext; simp [← h, ← star_def]

variable (Γ) in
lemma exists_isComplexConj [NumberField K] {w : InfinitePlace K} (h : w.IsReal) : ∃ c : Γ,
  IsComplexConj c :=
  (exists_smul_emb_eq Γ (ComplexEmbedding.lift Ω w.embedding) (star _) (by aesop)).rec (⟨·, _, ·⟩)

include K in
lemma IsComplexConj.mul_self (h : IsComplexConj c) :
    c * c = 1 := h.rec (G.faithful.1 <| by simp [mul_smul, ← ·.injective.eq_iff, ·])

/-- For x ∈ K^× totally positive and a character χ, the symbol (χ, x) ∈ H²(Γ, Ω^×) restricts to
zero on some open subgroup containing all complex conjugations. -/
lemma IsTotallyPositive.exists_resH2_cyclicClass_eq_zero {χ} {x : Kˣ} (p : IsTotallyPositive x.1) :
  ∃ U : OpenSubgroup Γ, (∀ c, IsComplexConj c → c ∈ U) ∧ (unitsModule Γ).resH2 U
  (cyclicClass _ χ (ofBase Γ Ω (.ofMul x))) = 0 := (exists_nsmul _ out).elim (⟨⟨_, G.6 ·.toMul.1⟩ ⊓
  ⟨_, isOpen_ker (χ + χ)⟩, fun c h@⟨j, hj⟩ ↦ ⟨j.injective (by simpa [*, conj_eq_iff_im, ←
  sq_nonneg_iff, ← zero_le_real, ← map_pow, ← val_pow_eq_pow_val, ← toMul_nsmul] using
  (p (isReal_comp_algebraMap hj).embedding).le), map_mul_eq_one (toHom χ) h.mul_self⟩,
  DiscreteModule.resH2_cyclicClass_eq_zero · (·.2.imp DiscreteUnits.ext (two_nsmul _).trans)⟩)

lemma IsComplexConj.false_of_isTotallyComplex (h : IsComplexConj c) [t : IsTotallyComplex K] :
    False := t.complexEmbedding_not_isReal _ (isReal_comp_algebraMap h.choose_spec)

omit [TopologicalSpace Γ] in
lemma IsComplexConj.cycCharMod_eq_neg_one (h : IsComplexConj c) {N} [NeZero N] :
  _root_.cycCharMod Ω N c = -1 := h.rec fun j _ ↦ Units.ext
  (.trans (cycCharMod_eq_iff.2 fun ζ e ↦ left_inv_eq_right_inv (j.injective (by simp_all [conj_mul',
  ← map_pow, norm_eq_one_of_pow_eq_one _ (ne N)])) (e ▸ mul_pow_sub_one out _)) (by simp [pos]))

omit [TopologicalSpace Γ] in
/-- If σ ∈ Γ acts as a complex conjugation on the algebraically closed field Ω of characteristic
zero, then the ℓ-adic cyclotomic character takes the value −1 at σ. -/
lemma IsComplexConj.cycChar_eq_neg_one (h : IsComplexConj c) l [Fact (Nat.Prime l)] :
  _root_.cycChar Ω l c = -1 := Units.ext (PadicInt.ext_of_toZModPow.1
  (by simpa [cycCharMod_prime_pow_eq, ← val_inj] using h.cycCharMod_eq_neg_one (N := l ^ ·)))
end
