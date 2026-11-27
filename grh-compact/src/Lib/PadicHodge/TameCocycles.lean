import Lib.GaloisRep.Avatars
import Lib.GaloisRep.GaussSums

-- part: Lib.ClassField.GreenbergWiles.SelmerBasic
section
/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Selmer cocycle groups, their finiteness, S-units, split primes, tame generators,
places. -/

noncomputable section


variable {G K R X : Type} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K]
  [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] (m N : ℕ) [NeZero m] [MulAction G X] (I :
  Set G) {M : DiscreteModule R G} (x : Z1 M.ρ) (V : DiscreteModule R Gal(Ω/K)) {v : FinPlace K} {B :
  ClosurePlace} (U : OpenNormalSubgroup G)
open NeZero NumberField Pointwise MulSemiringAction Set QuotientGroup

/-- γ lies in inertia at A, and γy/y = `rootPowHom` 1 for some m-th root y of some uniformiser π of
K for A. -/
def IsTameGeneratorFor (A : ClosurePlace) γ := γ ∈ inertiaGroup G A ∧ ∃ π y, IsUniformiser A (π :
  Kˣ).1 ∧ m • y = ↑(DiscreteUnits.ofBase G Ω (.ofMul π)) ∧ unitsRep γ y - y = (rootPowHom Ω m).1 1

variable (G) in
/-- For B above a prime v of K, some γ in the inertia group of B multiplies an m-th root of some
uniformiser of K by the fixed primitive m-th root of unity given by `rootPowHom`. -/
lemma exists_isTameGeneratorFor (h : IsPlaceOver B v) : ∃ γ : G, IsTameGeneratorFor m B γ :=
  (h.exists_uniformiser G).rec fun π ⟨a, u⟩ ↦ ((DiscreteUnits.ofBase G Ω π).1.exists_nsmul out).rec
  fun y hy ↦ ((h.decompGroup_spec G).1.exists_inertia_smul_eq_of_pow_eq u (pos m) congr($hy.1) (y :=
  ((rootPowHom Ω m).1 1 + y).toMul) (mod_cast by simp [mul_pow,
  (isPrimitiveRoot_rootPowHom_one ..).1])).rec (⟨·, ·.1, π, y, h.isUniformiser_iff.2 a, by aesop⟩)

/-- The places of Ω above N and infinity: valuation subrings in which N has valuation below 1,
together with the infinite places. -/
def PlaceAboveS := {B : ClosurePlace // B N < 1} ⊕ InfinitePlace Ω deriving Nonempty

instance : MulAction G (PlaceAboveS N) := @Sum.instMulAction _ _ _ _ (SubMulAction.mk _ fun g ↦
  (by simpa using! (val_smul_lt_one g).2 ·)).mulAction (.compHom _ (toAlgAut G ℚ Ω))

instance (Q : Subgroup G) [Q.Normal] : MulAction (G ⧸ Q) (MulAction.orbitRel.Quotient Q X) := {
  smul := .map₂ (· • ·) fun a b e x y ⟨q, h⟩ ↦ ⟨⟨a * q * b⁻¹, by simp [← eq_one_iff, Quotient.sound
    e]⟩, by simp [← h, mul_smul, Q.smul_def]⟩, one_smul := Quot.ind (congr(⟦$(one_smul G ·)⟧)),
  mul_smul := by rintro ⟨⟩ ⟨⟩ ⟨⟩; exact congrArg _ (mul_smul ..) }

/-- A continuous 1-cocycle that vanishes on the inertia group and at a Frobenius element of a
place B above the prime v vanishes on the decomposition group of B. -/
lemma DiscreteModule.Z1.eq_zero_on_decompGroup {φ} (h : IsPlaceOver B v) (f : IsFrob B v.q φ) :
  (∀ g ∈ inertiaGroup G B, x.1 g = 0) → x.1 φ = 0 → ∀ g ∈ decompGroup G B, x.1 g = 0 :=
  h.decompGroup_le f (U := cocycleKer M.ρ x.2.2) (x.2.1.1 {0} (by simp))

/-- The continuous 1-cocycles of ρ restricting into L_v on Dec(A_v) for v in S, and vanishing on
complex conjugations and on inertia groups above primes outside S ∪ P. -/
def selmerZ1 S (A : _ → ClosurePlace) L P := Z1 V.ρ ⊓ .pi (inertiaAbove (S ∪ P)ᶜ) ⊥ ⊓ (.comap
  (.pi fun v ↦ .funLeft R V (decompGroup _ (A v)).subtype) (.pi S L) ⊓ .pi {c | IsComplexConj c} ⊥)

/-- For a finite discrete module V of the absolute Galois group of K and a finite set S of primes,
there are finitely many continuous 1-cocycles vanishing on all inertia groups above primes outside
S. -/
lemma selmerZ1.finite_unramified_cocycles [Finite V] {S} (hS : S.Finite := by toFinite_tac) :
    (Z1 V.ρ ⊓ .pi (inertiaAbove Sᶜ) ⊥).1.1.1.Finite := by
  cases' exists_openNormalSubgroup_apply_eq V.continuous with N
  let U := (N.1 ⊓ ⟨(cycCharMod Ω 3).ker, isOpen_ker_cycCharMod.1⟩).1
  obtain ⟨T, f : Finite T, _, -, e⟩ := exists_sup_idelesUnitOff_eq_top
    (tendsto_place_comap_cofinite (algebraMap K (fixedFieldOf U)) hS.compl_mem_cofinite)
  apply (finite_univ.prod (.pi' fun w : T ↦
    (w.1.isPlaceOver_placeOver.decompGroup_spec U).1.finite_Z1_local ((V.restrictTo _).restrictTo
    _))).of_injOn (f := AddMonoidHom.mk' (fun z ↦ ((z ·.out⁻¹ : _ ⧸ U → _), fun _ ↦ (z ·))) (by
    tauto)) fun _ ↦ (by use ⟨⟩, fun _ ↦ ·.1.imp (by fun_prop) (by tauto))
  exact (injOn_iff_map_eq_zero (F := _ →+ _) _ (Z1 V.ρ ⊓ .pi (inertiaAbove Sᶜ) ⊥)).2
    fun z ⟨c, n⟩ h ↦ funext ((cocycleKer V.ρ c.2
    ).mul_mem_cancel_left congr($h.1 ·) |>.1 (QZChar.eq_zero_of_unramified_off _ e ⟨(z ·),
    c.imp (by fun_prop) (by aesop)⟩ (Γ :=
    U) (nomatch ·.2.2 ▸ ·.cycCharMod_eq_neg_one) (congr($h.2 ⟨·, ·⟩ ⟨·, ·⟩)) (fun w _ ↦ (n · ⟨_, by
    tauto, _, w.isPlaceOver_placeOver.isPlaceOver_below, ·⟩)) ⟨_, by simp [← QuotientGroup.eq]⟩))


/-- The N-units of Ω: elements of Ω^× that are units in every valuation subring in which N does
not have valuation below 1. -/
def sUnits : Submodule ℤ (DiscreteUnits Ω) := .comap (.const ..) (.pi {B : ClosurePlace | B N = 1}
  (·.unitGroup.toAddSubgroup.toIntSubmodule))

/-- The N-units of the fixed field of U: the N-units of Ω that are fixed by U. -/
abbrev fixedSUnits := sUnits N ⊓ (unitsModule U.1.1).H0

/-- The N-units of the fixed field of the open normal subgroup U, as a module over the group
ring ℤ[G/U]. -/
abbrev fixedSUnitsRep : Representation ℤ (G ⧸ U.1.1) (fixedSUnits N U) :=
  lift _ (unitsRep.subrepresentation _ fun g _ ↦
  .imp (by simpa [isEquiv_comap.eq_one_iff_eq_one] using! · <| ·.comap (toRingHom G Ω g))
  (unitsRep.le_comap_invariants _ _ ·)) (LinearMap.ext fun x ↦ Subtype.ext <| x.2.2 ⟨·, ·⟩)

/-- Auxiliary primes: distinct v_i ∤ N with places and Frobenii in U; m ∣ N; U fixes μ_m and
contains all inertia off N; I is the inertia off N and the v_i; primes above N generate the
class groups of number fields in Ω^U over K. -/
structure SplitPlaces (ι : Type) where
  cyc_eq_one : ∀ g ∈ U, cycCharMod Ω m g = 1
  dvd_level : m ∣ N
  v : ι → FinPlace K
  v_injective : v.Injective
  level_notMem i : ↑N ∉ (v i).1
  valRing : ι → ClosurePlace
  isPlaceOver i : IsPlaceOver (valRing i) (v i)
  φ : ι → G
  isFrob i : IsFrob (valRing i) (v i).q (φ i) ∧ φ i ∈ U
  mem_inertia_iff g : g ∈ I ↔ ∃ w, ↑N ∉ w.1 ∧ w ∉ range v ∧ ∃ B : ClosurePlace, IsPlaceOver B w ∧
    g ∈ inertiaGroup G B
  inertiaGroup_le {v : FinPlace K} {B : ClosurePlace} : ↑N ∉ v.1 → IsPlaceOver B v →
    inertiaGroup G B ≤ U
  principal_sup_idelesUnitOff (F : IntermediateField K Ω) [NumberField F] : F ≤ fixedFieldOf U.1.1 →
    principalIdele (K := F).range ⊔ idelesUnitOff {w | ↑N ∈ w.1} = ⊤

variable {m N I U ι} (s : SplitPlaces m N I U ι)

lemma ofBase_mem_sUnits {x} : (DiscreteUnits.ofBase G Ω (.ofMul x)).1 ∈ sUnits N ↔
  x ∈ unit {w : FinPlace K | ↑N ∈ w.1} K :=
  ⟨fun h (w : FinPlace K) ↦ w.isPlaceOver_placeOver.valuationVia_eq_one_iff.1 ∘ h _ ∘
  w.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2, fun h B b ↦ by_cases id
  (exists_isPlaceOver_of_val_ne_one K (by simp) · |>.elim fun _ o ↦
  o.valuationVia_eq_one_iff.2 (h _ (o.valuation_natCast_eq_one_iff.1 b)))⟩

/-- Every y in Ω^× whose m-th power is an N-unit of the fixed field of U, and which all Frobenii
φ_i fix, is fixed by U. -/
abbrev SplitPlaces.FrobeniiDetectRoots := ∀ y, m • y ∈ fixedSUnits N U →
  (∀ i, unitsRep (s.φ i) y = y) → ∀ g ∈ U, unitsRep g y = y

lemma mem_sUnits_of_nsmul_mem {r} {y : fixedSUnits N U} (e : m • r = ↑y) : r ∈ sUnits N :=
  (by simpa [← e, ne] using y.2.1 · ·)

lemma SplitPlaces.decompGroup_le {i} (h : IsPlaceOver B (s.v i)) : decompGroup G B ≤ U :=
  h.decompGroup_le (((s.isPlaceOver i).exists_smul G h).choose_spec ▸ (s.isFrob i).1.conj _) U.1.2
  (s.inertiaGroup_le (s.level_notMem i) h) (U.2.1 _ (s.isFrob i).2 _)

/-- For open U ⊆ Q ⊴ B, Q fixing μ_m: the primes of the fixed field of B above s, with Frobenii
conjugated by coset representatives σ, as a family split for Q. -/
def SplitPlaces.liftToSubgroup (B : OpenSubgroup G) (Q : OpenNormalSubgroup B.1) (r : U.1.1 ≤
  B) (u : U.1.1.subgroupOf B ≤ Q) (c : ∀ g ∈ Q, cycCharMod Ω m g = 1) (σ : G ⧸ B.1 → G) (e : ∀ x,
  σ x = x) : SplitPlaces m N ((↑) ⁻¹' I) Q (ι × G ⧸ B.1) := by
  have o (θ : ι × _) := (s.isPlaceOver θ.1).smul (σ θ.2)⁻¹
  choose w W k using (o · |>.exists_above (L := fixedFieldOf B.1))
  refine ⟨c, s.dvd_level, w, fun ⟨_, a⟩ θ q ↦ ?_, (s.level_notMem ·.1 ∘ by simp [← k]), _, W,
    fun _ ↦ ⟨_, r (U.2.1 _ (s.isFrob _).2 _)⟩, fun θ ↦ ⟨(((o _).ramification_in_tower _ (W θ)).1
    ((s.decompGroup_le (o θ)).trans r)).1 ▸ (s.isFrob _).1.conj _, u (U.2.1 _ (s.isFrob _).2 _)⟩,
    (s.mem_inertia_iff · |>.trans ⟨fun ⟨v, a, b, C, c, d⟩ ↦ c.exists_above.imp fun
    _ ⟨e, rfl⟩ ↦ ⟨a ∘ by simp, fun ⟨θ, q⟩ ↦ b (by simp [← q, k]), C, e, d⟩, fun ⟨v, a, b, C, c⟩ ↦
    ⟨_, by simpa, fun ⟨i, q⟩ ↦ (c.1.isPlaceOver_below.exists_smul G (q ▸ s.isPlaceOver _)).rec fun g
    a ↦ b ⟨(i, g), (W _).unique (by simpa [smul_smul, ← a] using! c.1.smul (⟨_,
    QuotientGroup.eq.1 (e _)⟩ : B.1))⟩, C, c.imp_left .isPlaceOver_below⟩⟩), fun a b _ c ↦ u
    (s.inertiaGroup_le (by simpa) b.isPlaceOver_below c), fun F i e ↦ @s.principal_sup_idelesUnitOff
    (F.restrictScalars K) i fun _ a ⟨g, k⟩ ↦ e a ⟨⟨g, r k⟩, u k⟩⟩
  obtain ⟨rfl, t, k⟩ := s.v_injective (k _ ▸ q ▸ k _), (q ▸ W _).exists_smul B.1 (W _)
  exact congrArg _ (e a ▸ e θ.2 ▸ QuotientGroup.eq.2
    ((mul_mem_cancel_left t.2).1 (r (s.decompGroup_le (o θ) (by simpa [mul_smul])))))

include s

lemma SplitPlaces.mem_and_conj_mem g : g ∈ I → g ∈ U ∧ ∀ t, t⁻¹ * g * t ∈ I :=
  ext s.mem_inertia_iff ▸ fun ⟨w, a, b, _, c, d⟩ ↦
  ⟨s.inertiaGroup_le a c d, (⟨w, a, b, _, c.smul _, inv_inv · ▸ d.conj _⟩)⟩
end
end

-- part: Lib.ClassField.GreenbergWiles.EquivariantUnits
section
/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Herbrand's equivariant S-unit theorem: units plus Z span permutation module of places. -/

open Quot NumberField Pointwise MulAction InfinitePlace Units Matrix NeZero Function Module
  LinearMap Set Ideal


variable (G) {K : Type} [Group G] [TopologicalSpace G] [Field K] [NumberField K] (N : ℕ) [NeZero N]

/-- Non-vanishing of the S-regulator: on pairs (u, n), u an S-unit and n an integer, functions
M_v (v in S) vanishing exactly when u is a unit at v, and log|u|_w + n (w infinite), are
ℝ-linearly independent. -/
lemma linearIndependent_sUnit_log {S : Set (FinPlace K)} [Fintype S] {M : S ⊕ InfinitePlace K →
  S.unit K × ℤ → ℝ} (ho : ∀ v u, M (.inl v) u = 0 ↔ v.1.valuation K u.1.1 = 1) (hi : ∀ w u,
  M (.inr w) u = (w u.1.1).log + u.2) : LinearIndependent ℝ M := by
  choose _ _ y s using exists_valuation_eq_exp_mul S.toFinite
  exact .of_comp (funLeft ℝ ℝ (Sum.rec (y <| Pi.single · 1, 0) fun i ↦ if e : i = _ then 1 else
    (⟨.mk0 (fundSystem K ((equivFinRank K).symm ⟨i, e⟩)) (by simp), by simp [unit,
    notMem_of_isUnit]⟩, 0))) (linearIndependent_cols_of_det_ne_zero (Eq.trans_ne (congr(det $(by
    ext ⟨⟩ ⟨⟩ <;> try rfl
    aesop (add simp [fromBlocks, notMem_of_isUnit]))).trans (det_fromBlocks_zero₂₁' ..))
      (mul_ne_zero
    (det_ne_zero_of_sum_col_lt_diag (by simp_all [Finset.sum_eq_zero])) (right_ne_zero_of_mul (mt
    (congr(det $(by aesop)).trans (det_mul_row ..)).trans (abs_pos.1 ((finrank_mul_regulator_eq_det
    K _ (equivFinRank K).symm).subst (by simp [regulator_pos, finrank_pos]))))))))

variable [Algebra K Ω] [MulSemiringAction G Ω] [IsProGalois G K Ω]

/-- Given places A_v of Ω above each prime v of K, there are infinite places of Ω above those of
K which, with the A_v for v dividing N, meet every G-orbit of places above N and infinity in
exactly one index. -/
lemma PlaceAboveS.bijective_orbits {A : _ → _} (hA : ∀ v, IsPlaceOver (A v) v) :
  Bijective (Quotient.mk (orbitRel G (PlaceAboveS N)) ∘ .map (fun v : {v : FinPlace K | ↑N ∈ v.1} ↦
  ⟨_, (hA _).valuation_natCast_lt_one_iff.2 v.2⟩) (surjInv (comap_surjective (k := K)))) := ⟨by
  rintro ⟨⟩ ⟨j⟩ e <;> cases' Quotient.exact e with g <;> injections
  grind [((hA j).smul g).unique]
  grind [surjInv_eq, mem_orbit_iff.1 ⟨MulSemiringAction.toAlgEquiv K _ g, ‹_›⟩], ind (Sum.rec (fun B
    ↦ (exists_isPlaceOver_of_val_ne_one K out B.2.ne).rec fun v h ↦
  ⟨.inl ⟨v, h.valuation_natCast_lt_one_iff.1 B.2⟩, sound ((h.exists_smul
  G (hA _)).imp fun _ ↦ congrArg _ ∘ Subtype.ext)⟩) fun u ↦ ⟨.inr _, sound (((toAlgAut_surjective
  G).exists.1 (mem_orbit_iff.2 (surjInv_eq comap_surjective _).symm)).imp fun _ ↦ congrArg _)⟩)⟩

include K

/-- Equivariant Dirichlet theorem: with X the places above N∞ of the field of Q, its N-units E
are finitely generated, rank(E × ℤ) ≤ #X, and there are ℝ-linearly independent additive maps
Λ_z : E × ℤ → ℝ (z ∈ X) with Λ_z(g⁻¹y) = Λ_{gz}(y). -/
lemma dirichlet_fixedSUnits (Q :
  OpenNormalSubgroup G) : let X := orbitRel.Quotient Q.1.1 (PlaceAboveS N)
  Module.Finite ℤ (fixedSUnits N Q) ∧ ∃ Λ : X → _ →ₗ[ℤ] ℝ, (∀ g z y,
    Λ z ((fixedSUnitsRep N Q).prod (.trivial _ _ ℤ)
    g⁻¹ y) = Λ (g • z) y) ∧ LinearIndependent ℝ Λ ∧ finrank ℤ (fixedSUnits N Q × ℤ) ≤ .card X := by
  have := (@finite_natCast_mem (fixedFieldOf Q.1.1) _ _ N _).fintype
  let ⟨_, rk⟩ := SUnit.dirichlet_unit_theorem this.finite
  let e := Equiv.ofBijective _ (PlaceAboveS.bijective_orbits Q.1.1 N FinPlace.isPlaceOver_placeOver)
  let ε : Additive (unit ..) →+ fixedSUnits N Q :=
    .mk' (⟨_, ofBase_mem_sUnits.2 ·.2, Subtype.prop _⟩) (by tauto)
  have hε : Surjective ε.toIntLinearMap := fun ⟨y, h, k⟩ ↦ by
    obtain ⟨x, ⟨⟩⟩ := (DiscreteUnits.ofBase_bijective _).2 ⟨y, k⟩; exists ⟨x,
      ofBase_mem_sUnits (G := Q.1.1).1 h⟩
  let lg y n : PlaceAboveS N → ℝ := Sum.rec (ordRat K ·.1 y) fun w ↦ (w y.toMul.1).log + n
  have hl (g : G) y n : ∀ z, lg (unitsRep g⁻¹ y) n z = lg y n (g • z) := by rintro ⟨B⟩; simp [lg,
    ← (exists_isPlaceOver_of_val_ne_one K out B.2.ne).choose_spec.ordRat_smul g]; repeat rfl
  use .of_surjective _ hε, fun x ↦ AddMonoidHom.toIntLinearMap (.mk' (fun (y, n) ↦ x.lift (lg y n)
    (by rintro _ _ ⟨g, rfl⟩; erw [← hl, y.2.2 g⁻¹])) (by obtain ⟨⟨⟩⟩ := x <;> simp [Real.log_mul,
    lg, add_add_add_comm])), Quotient.ind₂ (by tauto), (linearIndependent_equiv e).1 (.of_comp (pi
    (applyₗ' ℝ <| ·.map ε id)) (linearIndependent_sUnit_log (fun v _ ↦ Rat.cast_eq_zero.trans
    (v.1.isPlaceOver_placeOver.isPlaceOver_below.ordRat_eq_zero_iff.trans
    v.1.isPlaceOver_placeOver.valuationVia_eq_one_iff)) fun w _ ↦ congr(($(
    surjInv_eq comap_surjective w) _).log + _))), Nat.card_congr e ▸ finrank_le_of_rank_le ?_
  grw [rank_eq_of_surjective fst_surjective, ker_fst, rank_range_le, rank_le_of_surjective _ hε]
  simp [← rk]
end

-- part: Lib.ClassField.GreenbergWiles.SplitPrimeReciprocity
section
/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Power residue symbols of S-units give exactly the relations on tame ramification of
cocycles. -/


variable {G K R} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction
  G Ω] [IsProGalois G K Ω] [CommRing R] {m N} [NeZero m] [NeZero N] {ι U} {A : ClosurePlace} {v :
  FinPlace K} {V : DiscreteModule R G} [Module (ZMod m) V] {I : Set G} (s : SplitPlaces m N I U ι)
open NumberField DiscreteModule trivialisedCocycles DiscreteUnits NeZero Subgroup QuotientGroup
  InfinitePlace QZChar QZ ZModModule Fint

omit [IsProGalois G K Ω] in
lemma eq_one_or_isComplexConj [J : IsProGalois G K Ω] {g} {u : InfinitePlace Ω} (h :
  MulSemiringAction.toAlgAut G ℚ Ω g • u = u) : g = 1 ∨ IsComplexConj g := ((mem_stabilizer_mk_iff
  ..).1 (u.mk_embedding ▸ h)).imp (J.faithful.1 ∘ by simp [AlgEquiv.ext_iff]) (⟨_, ·.eq⟩)

/-- Let A lie over v ∤ m, γ satisfy `IsTameGeneratorFor`, V be killed by m, and f : G → V be locally
constant and additive on inertia. For τ in inertia, f(τ) is a multiple of f(γ). -/
lemma IsTameGeneratorFor.exists_apply_eq_nsmul (h : IsPlaceOver A v) (hm : ↑m ∉ v.1) {γ τ} (hγ :
  IsTameGeneratorFor m A γ) (hτ : τ ∈ inertiaGroup G A) {V} [AddCommGroup V] [Module (ZMod m) V]
  (f : G → V) (l : IsLocallyConstant f) (a : ∀ g ∈ inertiaGroup G A, ∀ k ∈ inertiaGroup G A, f (g *
  k) = f g + f k) : ∃ c : ℕ, f τ = c • f γ := hγ.rec fun i ⟨π, y, u, hy, e⟩ ↦ (((h.decompGroup_spec
  G).1.tame_inertia ((h.decompGroup_spec G).2.2 u) (h.valuation_natCast_eq_one_iff.2 hm)
  congr($hy.1) (.mk' _ (a _ ·.2 _ ·.2)) (l _).preimage_val.preimage_val (char_nsmul_eq_zero m <|
  f ·) (P := Multiplicative V)).2 ⟨⟨_, i.1⟩, i⟩).1 (by simpa [← e,
  ← IsPrimitiveRoot.coe_units_iff] using! isPrimitiveRoot_rootPowHom_one Ω m) ⟨⟨τ, hτ.1⟩, hτ⟩

omit [NeZero N] in
lemma SplitPlaces.apply_inertia_eq_zero (h : IsPlaceOver A v) {i γ τ} (k : s.v i = v) (hγ :
  IsTameGeneratorFor m (s.valRing i) γ) (z : Z1
  V.ρ) (t : V.TrivialOn U.1.1) (e : z.1 γ = 0) (hτ : τ ∈ inertiaGroup G A) : z.1 τ = 0 := by
  obtain ⟨⟨g, k⟩, d⟩ := h.exists_smul G (k ▸ s.isPlaceOver i),
    (t · <| s.inertiaGroup_le (s.level_notMem i) (s.isPlaceOver i) ·)
  have j := k ▸ hτ.conj g
  cases hγ.exists_apply_eq_nsmul (s.isPlaceOver i) (s.level_notMem i ∘ Ideal.mem_of_dvd _
    s.dvd_level.natCast) j _ (z.2.1.1 · (by simp)) (by grind [z.2.2])
  simpa [← mul_assoc, *] using cocycle_conj_eq_smul (a := V.ρ) z.2.2 (d _ j (z.1 g⁻¹⁻¹))

/-- Let U fix V, mV = 0, γ_i satisfy `IsTameGeneratorFor`, and ζ^(b(y)_i) = φ_i r/r for N-units y =
r^m. Trivialised cocycles z obey ∑ b(gy)_i g⁻¹z(γ_i) = 0 and vanish on U if all z(γ_i) = 0. For
totally complex fixed field, ∑ b(gy)_i f(i,g) = 0 for all y makes (∑_g f(i,g) ga)_i some
(z(γ_i))_i. -/
lemma SplitPlaces.power_residue_reciprocity (γ : ι → G) (hγ : ∀ i, IsTameGeneratorFor m (s.valRing
  i) (γ i)) [Fintype ι] (t : V.TrivialOn U.1.1) : ∃ b : _ →+ ι → _, (∀ y r, m • r = ↑y → ∀ i,
  (rootPowHom Ω m).1 (b y i) = unitsRep (s.φ i) r - r) ∧ (∀ P ∈ V.trivialisedCocycles (PlaceAboveS
  N) I, ((∀ i, P.2 (γ i) = 0) → ∀ g ∈ U, P.2 g = 0) ∧ ∀ y, ∑ θ : _ × _, b (fixedSUnitsRep N U θ.2 y)
  θ.1 • V.ρ θ.2.out⁻¹ (P.2 (γ θ.1)) = 0) ∧ (IsTotallyComplex (fixedFieldOf U.1.1) → ∀ f : _ → _,
  (∀ y, ∑ θ, b (fixedSUnitsRep N U θ.2 y) θ.1 * f θ = 0) → ∀ a, ∃ P ∈ V.trivialisedCocycles
  (PlaceAboveS N) I, ∀ i, P.2 (γ i) = ∑ δ, V.ρ δ.out (f (i, δ) • a)) := by
  let Q := U.1.1
  let S := s.liftToSubgroup _ ⟨⊤, normal_top⟩ le_rfl le_top (fun g _ ↦ s.cyc_eq_one _ g.2) _ out_eq'
  obtain ⟨⟨κ, C, Ξ⟩, c, j, A', d, hd, R⟩ := exists_kummer_chars (S.cyc_eq_one · ⟨⟩),
    (S.cyc_eq_one · ⟨⟩), (rootPowHom Ω m).2.1, @FinPlace.isPlaceOver_placeOver (fixedFieldOf Q),
    (s.decompGroup_le (s.isPlaceOver _) <| hγ · |>.1.1), s.principal_sup_idelesUnitOff _ le_rfl,
    (exists_nsmul (Ω := Ω) · (ne m) |>.choose_spec)
  have Z x q h := (map_eq_zero_iff _ j).1 (C x _ (R _) q ▸ sub_eq_zero.2 h)
  have J {B v} (h : IsPlaceOver (K := fixedFieldOf Q) B v) b x a {q} i :=
    Z x q (ext (inertia_fixes_root_of_unit i (h.valuation_natCast_eq_one_iff.2
    (b ∘ v.1.mem_of_dvd s.dvd_level.natCast)) congr($(R _).1) a congr($(x.2 _).1)))
  have n θ x : (κ (ofBase Q Ω (.ofMul x))).1 ⟨_, U.2.1 _ (d θ.1) θ.2.out⁻¹⟩ =
    cycCharMod Ω m θ.2.out⁻¹ * ↑(-((S.v θ).valuation (fixedFieldOf Q) x.1).log) := by
    have O : IsPlaceOver (S.valRing θ) _ := (s.isPlaceOver _).smul _
    obtain ⟨n, a, π, y, hπ, hy, l⟩ :=
      (O.ramification_in_tower Q (S.isPlaceOver θ)).1 (s.decompGroup_le O), hγ θ.1
    exact .trans (sub_eq_zero.1 (κ.map_sub .. ▸ J (S.isPlaceOver θ) (S.level_notMem _) _
      (O.ordRat_eq_zero_iff.1 (by simp [*, Q, O.ordRat_ofBase, (s.isPlaceOver
      _).isUniformiser_iff.1, n.2 ▸ (S.isPlaceOver θ).ordRat_ofBase x])) (a.conj _))) ((fun c : ℤ ↦
      j ((C ⟨_, ((c • ofBase G Ω (.ofMul π)).2 ·)⟩ (c • unitsRep θ.2.out⁻¹ y) (by simp [(ofBase G Ω
      _).2 _, smul_comm m, ← map_nsmul, *]) _).trans (.trans (by simp [← zsmul_one, ← l,
      smul_sub, -zsmul_eq_mul] : unitsRep (_ : G) _ - _ = _) (map_cycCharMod_mul ..).symm))) _)
  let b := AddMonoidHom.mk' (fun x i ↦ (κ ((fixedSUnits N U).inclusion inf_le_right x)).1 ⟨_,
    (s.isFrob i).2⟩) (by clear * -; aesop)
  have L x h θ := j ((C x _ (R _) (S.φ θ)).trans
    (by erw [map_cycCharMod_mul _ θ.2.out⁻¹ (b (fixedSUnitsRep N U θ.2.out ⟨_, h, x.2⟩) θ.1),
    C _ _ (R _ ▸ (map_nsmul (unitsRep _) ..).symm)]; ext; simp [S, liftToSubgroup, mul_smul]))
  refine ⟨b, by tauto, fun P p ↦ (snd_mem_Z1 p).elim fun y z ↦ ?_, fun _ f hf a ↦ by
    choose ξ v e using
      (S.isPlaceOver · |>.exists_localArtin_eq ((inv_inv _).substr (S.isFrob _).1) 1)
    obtain ⟨_, ⟨x, rfl⟩, _, ⟨hx, H⟩, E⟩ := mem_sup.1 (Ξ (finite_natCast_mem _) hd (·.1.mem_of_dvd
      s.dvd_level.natCast) (∏ θ, locIdele _ (ξ θ) ^ (cycCharMod Ω m θ.2.out * f θ).val)
      (by simp [(S.isPlaceOver _).artinAt_eq_of_localArtin_eq (e _), ofBase_mem_sUnits,
      ← toAdd_eq_zero, ← map_nsmul, ← map_sum, mul_comm (f _), mul_assoc, *]))
    cases eq_div_of_mul_eq'' E
    let X := ofBase Q Ω (.ofMul x)
    simp [idelesUnitOff, Units.ext_iff, ideleAt, field] at H
    exact ⟨_, corestrict_mem _ s.mem_and_conj_mem (trivialisedCocycles.exists_mem_of_orbit_reps
      (PlaceAboveS.bijective_orbits Q N A') ((κ X).2.imp (continuous_bot (f := (· • a))).comp fun h
      p q ↦ t _ p.2 _ ▸ by simp [h, add_smul]) (Set.ext S.mem_inertia_iff ▸ fun g ⟨u, b, k, B, h,
      i⟩ ↦ by simp [J h b X (h.valuationVia_eq_one_iff.2 (H u b ▸ by simp [Ne.symm (k ⟨_, ·⟩)])),
      i]) 0 (Sum.rec (fun u g e ↦ by simp [Z X g (ext ((A' u).smul_root_eq_of_local_pow (by
      simpa [u.2.ne_of_notMem, S.level_notMem] using mem_iInf.1 hx u) congr($(R X).1) g
      (by repeat injections) (c g)))]) fun u g e ↦ by simp [(eq_one_or_isComplexConj
      (by injections)).resolve_right (·.false_of_isTotallyComplex),
      Z])).choose_spec.1, fun i ↦ congr(∑ δ, V.ρ _ ($(.trans (by exact δ.ind' (by simp [(eq_one_iff
      _).2, d, X])) ((n (i, δ) x).trans (by rw [← H _ (S.level_notMem _),
      Finset.prod_eq_single (i, δ)] <;> simp +contextual [v, S.v_injective.ne, eq_comm]))) • a))⟩⟩
  have T y (g : Q) (e : g.1 • y = y) := by simpa [*] using p.2.1 g y
  have hc c (h : IsComplexConj c) := T (.inr _) c (congrArg _ ((mem_stabilizer_mk_iff ..).2 (.inr
    (RingHom.ext h.choose_spec).symm)))
  have hD u k := (T (.inl ⟨_, (A' u).valuation_natCast_lt_one_iff.2 k⟩) · congr(.inl ⟨$(·), _⟩))
  refine ⟨fun h ↦ (eq_zero_of_unramified_off _ hd ⟨_, by fun_prop, by simp [*]⟩ hc hD (fun u _ q e ↦
    by_cases (s.apply_inertia_eq_zero (A' u).isPlaceOver_below ·.choose_spec (hγ _) ⟨_, y,
    z⟩ t (h _) e) (p.2.2 _ <| (s.mem_inertia_iff _).2 ⟨_, by simpa, ·, _, (A' u).isPlaceOver_below,
    e⟩)) ⟨·, ·⟩), fun ⟨x, i, f⟩ ↦ eq_zero_of_forall_hom_eq_zero ((bijective_ofZMod_comp
    (char_nsmul_eq_zero m)).2.forall.2 fun u ↦ (hilbert90_unitsRep ⟨fun g : Q ↦ (rootPowHom ..).1 (u
    (P.2 g)), by fun_prop, by simp [← map_cycCharMod_mul, *]⟩).elim fun r e ↦ ?_)⟩
  obtain ⟨a, hr⟩ := ((ofBase_bijective Q).2 ⟨m • r, by simp [← add_eq_of_eq_sub (e _),
        ← map_nsmul]⟩).imp fun _ ↦ (congr($(·).1).symm)
  have E {g : Q} (k : P.2 g = 0) := by simpa [k] using (e g).symm
  have J {B v} k h := (@J B v k h ⟨_,
    f⟩ (i _ (k.valuation_natCast_eq_one_iff.2 h)) · · ▸ map_zero (ofZMod m))
  refine .trans (by simp [← map_zsmul, *, ZMod.map_smul, show u (V.ρ _ _) =
    _ from cocycle_conj_eq_smul (a :=
    V.ρ) z _ ▸ n _ a ▸ j (C _ r hr _ ▸ e _)]; ac_rfl) (sum_ord_smul_frob_eq_zero (?_ :
    m • ofZModCocycle m _ = 0) (artin_reciprocity ⟨_, IsProGalois.isOpen_stabilizer _⟩ (congr($(E <|
    hc · ·).1)) (resH2_cyclicClass_eq_zero hr (⟨ext ·.2, ?_⟩))) S.v_injective (⟨S.isPlaceOver ·,
    (S.isFrob _).1, J (S.isPlaceOver _) (S.level_notMem _)⟩) fun u k ↦ (em _).imp (fun l ↦ (A'
    _).abelianLift_artinAt_eq_one_iff.2 (resH2_cyclicClass_eq_zero hr (⟨E <|
    hD u l _ ·.2, ?_⟩))) fun l ↦ ⟨⟨r, hr ▸ by simp, (E <| p.2.2 · <| (S.mem_inertia_iff _).2 ⟨_, l,
    k, _, A' u, ·⟩)⟩, J (A' u) l⟩) <;> simp [funext_iff, ← map_nsmul]
end

-- part: Lib.ClassField.GreenbergWiles.ProjectiveCount
section
/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Count of trivialised cocycles for a projective module (Euler characteristic type
formula). -/

open NumberField Classical Nat NeZero Fintype AddSubgroup Finset Submodule AddMonoidHom Fint
attribute [local simp] funext_iff

/-- Let V be finite, l-torsion, U-fixed, with Higman's property, z − n injective on V, and let U
fix zr/rⁿ whenever r^l is an N-unit and all φ_i fix r. Trivialised cocycles number at most
(#V)^{#ι+1}, exactly so if K is totally complex and z = n on μ_l. -/
lemma SplitPlaces.card_trivialised_of_isHigmanProjective {G K R ι} [Group G] [TopologicalSpace G]
  [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] {l N :
  ℕ} [Fact l.Prime] [NeZero N] {V : DiscreteModule R G} {I U} (s : SplitPlaces l N I U ι) [Fintype
  ι] {z n} (x : V.FiniteKilledFixedInj l U z n) (h : V.IsHigmanProjective U.1.1) (m : ∀ r, l • r ∈
  fixedSUnits N U → (∀ i, unitsRep (s.φ i) r = r) → unitsRep z r - n • r ∈ (unitsModule U.1.1).H0) :
  V.HasFewCocycles (PlaceAboveS N) I (card ι + 1) ∧ ((cycCharMod Ω l z).1 = n → IsTotallyComplex K →
  Nat.card (V.trivialisedCocycles (PlaceAboveS N) I) = .card V ^ (card ι + 1)) := by
  obtain ⟨⟨_, Λ, u, v, w⟩, ⟨_, hV, t, i⟩, ⟨τ, hτ⟩, ⟨γ, hγ⟩⟩ := dirichlet_fixedSUnits G N U, x, h,
    skolem.1 (exists_isTameGeneratorFor G l <| s.isPlaceOver ·), AddCommGroup.zmodModule x.2.1
  let W := QuotientGroup.lift _ (actionRep ℤ _ V.ρ) (LinearMap.ext ∘ t ·)
  obtain ⟨⟨β₀, B, R, T⟩, o⟩ := s.power_residue_reciprocity γ hγ t, show ∀ g, ⇑(V.ρ g) = W g by tauto
  simp [o, -Subtype.forall, injective_iff_map_eq_zero] at hτ R T i
  let d := (d0 V.ρ).toAddMonoidHom
  let β := mk' (fun y (i, g) ↦ β₀ (fixedSUnitsRep N U g y) i) (by simp)
  let j : (ι → V) × d.ker →+ ((fixedSUnitsRep N U).prod (.trivial _ _ ℤ)).IntertwiningMap W :=
    mk' (fun (a, v)
    ↦ ⟨.coprod (∑ θ, .smulRight (.proj θ ∘ₗ β.toIntLinearMap) (W θ.2⁻¹ (a θ.1))) (.smulRight .id v),
    fun g ↦ by ext <;> simp [β, ZMod.map_smul]; exacts [(sum_equiv (.prodCongr 1 (.mulRight g)) _ _
    (by simp)), g.ind' (sub_eq_zero.1 congr($(v.2) ·) |>.symm)]⟩) fun _ _ ↦ by ext <;> simp
  let r : V.trivialisedCocycles (PlaceAboveS N) I →+ j.ker := mk' (fun P ↦
    ⟨(P.1.2 ∘ γ, 0), by ext <;> simp [j, β, (R _ _ P.2).2]⟩) (by simp [Subtype.ext_iff])
  let f (P : r.ker) := @Quotient.lift _ _ (MulAction.orbitRel U.1.1 _) P.1.1.1 fun _ x ⟨g, e⟩ ↦ by
    simpa [← e, t, (R _ _ P.1.2).1 (congr($(P.2).1.1 ·))] using! (P.1.2.2.1 g x).symm
  have H P (g : G) y : W g (f P y) = f P ((g : _ ⧸ U.1.1) • y) + P.1.1.2 g := y.ind' (P.1.2.2.1 g)
  let p : r.ker →+ d.range := mk' (fun P ↦ ⟨P.1.1.2, ∑ x, W x (τ (W x⁻¹ (f P (x • ⟦ofNonempty⟧)))),
    funext fun g ↦ sub_eq_of_eq_add' ((map_sum ..).trans (hτ (P.1.1.2 g) ▸ (sum_equiv (.mulLeft ↑g)
    _ _ (by simp [o, ← map_add, ← H, mul_smul])).trans sum_add_distrib))⟩) (by tauto)
  have hj x : x ∈ j.range := by
    obtain ⟨v, hv⟩ := LinearMap.exists_extend (p := β.range.toZModSubmodule l) ((liftOfSurjective _
      β.rangeRestrict_surjective ⟨.comp x (inl _ ℤ), fun ⟨y, a⟩ k ↦ i _ (by
      obtain ⟨w, rfl⟩ := y.exists_nsmul (ne l)
      erw [← x.isIntertwining, ← map_nsmul, ← sub_eq_zero, ← map_sub,
        ← show l • inl (fixedSUnits N U) _ ⟨_, mem_sUnits_of_nsmul_mem ?e,
        m _ a fun i ↦ by simpa [β, B _ w] using congr((rootPowHom Ω l).1 ($k.1
        (i, 1)))⟩ = _ - _ from Prod.ext (Subtype.ext ?e) rfl, map_nsmul, hV]
      rw [smul_sub, ← map_nsmul, smul_comm]; rfl)⟩).toZModLinearMap l)
    use ⟨fun i ↦ ∑ g, W g (τ (v (Pi.single (i, g) 1))), x (0, 1), by
      simp [d, o, ← x.isIntertwining]⟩
    ext <;> simp [j]
    rw [← hτ (x _)]
    simp [↓← x.isIntertwining, congrArg v (pi_eq_sum_univ' (β _)), ZMod.map_smul, ← sum_product',
      smul_sum, ← (show (v ∘ β) · = _ by simpa using! congr($hv (β.rangeRestrict _)))]
    apply sum_nbij' (fun ((i, d), g) ↦ (d⁻¹ * g, i, g)) fun (h, i, g) ↦ ((i, g / h), g) <;> simp [β]
  have := ofSurjective j hj
  rw [DiscreteModule.HasFewCocycles, pow_succ, ← card_eq_fintype_card, ← Nat.card_fun,
    ← d.ker.card_mul_index, ← mul_assoc, ← Nat.card_prod, ← j.ker.card_mul_index, mul_rotate,
    ← r.ker.card_mul_index, ← p.ker.card_mul_index,
    ← (card_hom_lattice_eq_card_equivariant l hτ u v w).trans (@card_congr _ p.ker ⟨fun F ↦ ⟨⟨⟨⟨(F.1
    ⟦·⟧), 0⟩, by fun_prop, by simp [o, ← F.2]; tauto⟩, rfl⟩, rfl⟩, fun P ↦ ⟨f P, (·.ind'
    (by simp [H, Subtype.mk.inj P.2]))⟩, fun _ ↦ by ext ⟨⟩; rfl, by rintro ⟨⟨⟨⟨⟩⟩⟩, ⟨⟩⟩; rfl⟩)]
  simp_rw [index_ker, j.range_eq_top.2 hj, p.range_eq_top.2 fun ⟨_, m, rfl⟩ ↦ ⟨⟨⟨⟨fun _ ↦ m, _⟩,
    (V.coboundary m).2.1, by simp +contextual [t _ (s.mem_and_conj_mem ..).1]⟩, by ext <;> simp [r,
    t, s.decompGroup_le (s.isPlaceOver _) (hγ _).1.1]⟩, rfl⟩, card_top]
  use ⟨mul_pos (mul_pos (@card_pos _ ⟨0, by simp⟩ _) card_pos) card_pos,
    by grw [r.range.card_le_card_addGroup, Finite.card_subtype_le]⟩, fun c _ ↦ ?_
  erw [r.range_eq_top.2, card_top, card_congr (.subtypeUnivEquiv fun x y h ↦ i _ ?_)]
  obtain ⟨k, _, e⟩ := (torsion_int.le h).exists_nsmul_eq_zero
  have := of_pos ‹_›
  erw [← x.isIntertwining, ← cast_smul_eq_nsmul (ZMod l), ← c, cycCharMod_eq_of_dvd ⟨k, rfl⟩
    zmod_eq_natCast_val, cast_smul_eq_nsmul, ← map_nsmul]
  apply congrArg; ext; exact cycCharMod_spec z (by simpa [pow_mul'] using congr($e.1.1.toMul.1 ^ l))
  simp [by simpa [ne] using congr($e.2)]
  intro ⟨⟨a, v⟩, e⟩
  obtain ⟨⟨⟩, c⟩ := by simpa [j] using congr($e (0, 1)), Module.finBasis (ZMod l) V
  choose P Q hP m using fun k ↦ T (isTotallyComplex_of_algebra K _) _ (fun y ↦ by
    simpa [j, ZMod.map_smul] using! congr(c.repr (τ ($e (y, 0))) k)) (c k)
  exact ⟨∑ j, ⟨_, hP j⟩, by simp [r, Prod.snd_sum, m, sum_comm, ← map_sum, hτ]⟩
end

-- part: Lib.ClassField.GreenbergWiles.GreenbergWilesBound
section
/-! Known result: Greenberg–Wiles formula, as a lower bound for the dual side. Only this lower bound
is proved, under a hypothesis of a central element acting without fixed vectors. The dual Selmer
group is replaced by relations among values on tame inertia at auxiliary split primes, and no local
duality is used. Source: H. Darmon, F. Diamond, R. Taylor, Fermat's Last Theorem (1995; 2007 text),
Thm 2.18–2.19; A. Wiles, Ann. of Math. 141 (1995), Prop. 1.6; J. S. Milne, Arithmetic Duality
Theorems, I 4.10, 5.1; L. Washington, Galois cohomology (1997), Thm 2.

This file: Bound on trivialised cocycles when a central element acts without fixed vectors. -/

open NumberField Function Set Classical Nat DiscreteModule trivialisedCocycles Quotient Subgroup
  commutatorElement Fint
attribute [local simp] commutatorElement_def funext_iff add_smul

/-- Let K be totally complex, s auxiliary primes for l^r (r ≠ 0), N and U (`SplitPlaces`),
indexed by ι, with
Frobenii φ_i; V finite, l^r-torsion, U-fixed; z central modulo U, fixing l-power roots of unity,
z − 1 onto V. If U fixes each l^r-th root, fixed by all φ_i, of a U-fixed N-unit, the trivialised
cocycles unramified outside N and s are finite in number, at most (#V)^{#ι+1}.

Known result: Greenberg–Wiles formula, as a lower bound for the dual side. -/
lemma SplitPlaces.hasFewCocycles_of_central {K R ι} [Field K] [EmbeddedNumberField K] [CommRing R]
  {l r N : ℕ} [Fact l.Prime] [NeZero N] {I} {V : DiscreteModule R Gal(Ω/K)} [Fintype ι]
  [IsTotallyComplex K] {U} (s : SplitPlaces (l ^ r) N I U ι) (h : r
  ≠ 0) {z} (c : V.FiniteKilledFixedInj (l ^ r) U z 1) (o : cycChar Ω l z = 1) (w : ∀ g, ⁅z, g⁆ ∈ U)
  (d : s.FrobeniiDetectRoots) : V.HasFewCocycles (PlaceAboveS N) I (Fintype.card ι + 1) := by
  obtain ⟨j, P, f, b, q⟩ := dvd_pow_self l h, exists_open_sylow l U
  obtain ⟨e, B, r, n, i⟩ : (cycCharMod Ω l z).1 = (1 : ℕ) ∧ ∃ B ≥ P, (P.1.subgroupOf B).Normal ∧
    z ∈ B := ⟨cycCharMod_eq_of_dvd j (by simp [cycCharMod_prime_pow_eq, o]),
    ⟨_, isOpen_mono le_normalizer P.2⟩, le_normalizer,
    inferInstance, (w · |> f |> mul_mem_cancel_left |>.symm.trans (by simp))⟩
  replace d {y} i k g a := (by simp [IsFixedPt]; grind : _ → IsFixedPt (unitsRep g) (unitsRep z y -
    1 • y)) congr(unitsRep (z * g) $(d y (j.choose_spec ▸ mul_nsmul y .. ▸ nsmul_mem i _) k _ (w (g
    * z)⁻¹)) + $(cycCharMod_eq_iff_unitsRep.1 e
    ((map_nsmul (unitsRep g - 1) l y).symm.trans (sub_eq_zero.2 a))))
  let S := { s with dvd_level := j.trans s.dvd_level, cyc_eq_one :=
    (cycCharMod_eq_one_of_dvd j ∘ s.cyc_eq_one ·) }
  obtain ⟨⟨Z, _, p⟩, F, b, u⟩ :=
    exists_permModule_isHigmanProjective R l ⟨U.1.comap _ (by fun_prop), U.2.subgroupOf B⟩
    (z := ⟨z, i⟩) (w ·), f.trans r, coprime_mul_iff_right.1 (relIndex_mul_index r ▸ b)
  have hn Q u m {W} := (card_trivialised_of_isHigmanProjective (R := R) (V := W) (z :=
    ⟨z, i⟩) (S.liftToSubgroup B Q F u m (update out ⟦1⟧ 1)
    (by clear * -; grind [out_eq'])) · · fun y x o ↦ (d ⟨x.1, fun g ↦ x.2 ⟨⟨g, F g.2⟩, u g.2⟩⟩
    (by simpa [liftToSubgroup] using! o ⟨·, ⟦1⟧⟩) · (x.2 _)))
  have le := id @devissage_induction l.pow_one (P.1.subgroupOf B) (U.1.1.subgroupOf B) (q ·) (fun V
    _ t ↦ (hn ⟨⟨_, P.2.preimage_val⟩,
    n⟩ (@f ·) (by simpa [← Units.val_eq_one] using! S.cyc_eq_one _ <| q · · |>.choose_spec) t
    (t.isHigmanProjective_of_coprime b)).1) fun s _ ↦ (card_le_of_isShortExact s · · |>.1)
  have X {A V C ι π} (s : IsShortExact ι π) c := (((FiniteKilledFixedInj.of_isShortExact (B :=
    V) s c).imp (le A) (le C)).elim (card_le_of_isShortExact s)).2
  refine devissage_induction rfl U _ (by tauto) (fun _ _ t ↦ mem_of_eq_of_mem (cast_injective
    (eq_of_div_eq_one (IsMultiplicative.eq_one_of_isHigmanProjective R l U (fun A _ ↦ Nat.card
    (A.trivialisedCocycles ..) / (Nat.card A ^ _ :)) w (@fun _ V _ _ π o k ↦ ?_) t fun t@⟨_,
    _⟩ H ↦ by simp [S.card_trivialised_of_isHigmanProjective t H fun y x ↦ (d x · · (x.2 _)), *])))
    ⟨by simp [t.1], le_rfl⟩) (fun s _ ↦ (card_le_of_isShortExact s · · |>.1)) V c
  have T (c : (V.restrictTo B).FiniteKilledFixedInj .. := k.imp_right (by tauto)) (k := p c (_ ⧸
    Z)) := let ι : Hom _ _ := ⟨.const .., by tauto⟩; X (o.restrictAlong _) c (X ⟨const_injective,
    ι.1.exact_map_mkQ_range,
      (isShortExact_submodule _ _ ι.range.2).2.2⟩ k.1 ((hn _ le_rfl (S.cyc_eq_one ·) k.1 (k.2
    (Pi.single 1 1) (by simp [inv_mul_eq_one]))).2 e (isTotallyComplex_of_algebra K _)).ge).2
  simp [mul_pow, o.card_eq_mul, mul_div_mul_comm, card_eq_of_isShortExact _ I o,
    (map _ I π).range_eq_top.2 fun ⟨⟨a, x⟩, _, p⟩
    ↦ match T.1.ge (mem_univ ⟨(a, (x ·)), by fun_prop, by tauto⟩), o.2.2 (∑ g : _ ⧸ B.1, x g.out),
    u.isCoprime with | ⟨⟨q, v⟩, e⟩, ⟨m, _⟩, ⟨_, n, E⟩ => ⟨⟨_, zsmul_mem (sub_mem (corestrict_mem B
    (s.mem_and_conj_mem · · |>.imp_left (F ·)) v) (y := (fun _ ↦ m, _)) ⟨(coboundary _ m).2.1, by
    simp +contextual [k.2.2.1 _ (s.mem_and_conj_mem ..).1]⟩) n⟩, (fun (P : trivialisedCocycles ..)
    (e : P.1.1 = a) ↦ show P = _ by
      ext g; simp [*]; simpa [*] using (P.2.2.1 g ofNonempty).symm) _
    (by simpa [trivialisedCocycles.map, π.isIntertwining, (k.of_isShortExact o).2.2,
    (congr($e.1.1 _) : π _ = _), *, index, mul_smul] using congr($E • a))⟩]
end

-- part: Lib.ClassField.GreenbergWiles.SelmerRelations
section
/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

This file: Selmer conditions against trivialisations; many relations at split primes:
Greenberg–Wiles lower bound. -/

namespace selmerZ1

open NumberField Function Finset Classical QuotientGroup InfinitePlace DiscreteModule Fintype
  Submodule Filter Set Pi NeZero
variable {K R} [Field K] [EmbeddedNumberField K] [CommRing R] {M : DiscreteModule R Gal(Ω/K)} {S :
  Finset (FinPlace K)} {A : FinPlace K → ClosurePlace} (hu : ∀ g ∈ inertiaAbove Sᶜ, M.ρ g = 1) (hA :
  ∀ v, IsPlaceOver (A v) v) (L : ∀ _, Submodule R (_ → M)) (hL : ∀ v ∈ S,
  (d0 (M.restrictTo _).ρ).range ≤ L v) (hcM : ∀ {c}, IsComplexConj c → M.ρ c = 1) {m : ℕ} [NeZero m]
include hu hA hL hcM

/-- Let M be finite, unramified outside S (primes dividing N), fixed by complex conjugations, with
at most (#M)^k trivialised cocycles, and B¹ ⊂ L_v on S. Then `selmerZ1`, ramification allowed at the
primes of s, has #selmerZ1·(#M)^(#S+#∞) ≤ (#M)^k·∏_{v∈S} #(L_v ∩ Z¹), ∞ the infinite places of K. -/
theorem card_mul_pow_le [Finite M] {k U N I ι} [NeZero N] (s : SplitPlaces m N I U ι) (hk :
  M.HasFewCocycles (PlaceAboveS N) I k)
  (hT : ∀ v ∈ S, ↑N ∈ v.1) : .card (selmerZ1 M S A L (range s.v)) * .card M ^ (#S + card
  (InfinitePlace K)) ≤ Nat.card M ^ k * ∏ v ∈ S, .card ↥(L v ⊓ Z1 (M.restrictTo _).ρ) := by
  let J := (L · ⊓ Z1 (M.restrictTo _).ρ)
  let T := {v : FinPlace K | ↑N ∈ v.1}
  obtain ⟨_ : Finite T, ⟨⟩⟩ := finite_natCast_mem N, Nat.card_pos_iff.1 hk.1
  let F : selmerZ1 M S A L (range s.v) × (T ⊕ InfinitePlace K → M) →+ (∀ v : S, J v) × (↥(T \ S) →
    M) := .mk' (fun (y, m) ↦ (fun ⟨v, h⟩ ↦ ⟨_, sub_mem ⟨y.2.2.1 v h, .imp (·.comp (by fun_prop)) (by
    tauto) y.2.1.1⟩ ⟨hL v h ⟨m (.inl ⟨v, hT v h⟩), rfl⟩, (coboundary _ _).2⟩⟩, fun v ↦ (y - d0 M.ρ
    (m (.inl ⟨v, v.2.1⟩))) ((hA v).exists_isFrob _).choose)) (by intros; ext <;> simp <;> abel)
  choose f hf e using fun a : F.ker ↦ a.1.1.2.elim fun ⟨b, u⟩ C ↦
    trivialisedCocycles.exists_mem_of_orbit_reps (PlaceAboveS.bijective_orbits _ N hA) b (u · ∘
    .imp (by grind) ∘ (s.mem_inertia_iff _).1) a.1.2 (by
    rintro ⟨v, n⟩ g e <;> injections
    · exact sub_eq_zero.1 (byCases (congr($(a.2).1 ⟨v, ·⟩ |>.1 ⟨g, ‹_›⟩)) fun h ↦
        Z1.eq_zero_on_decompGroup (⟨_, b⟩ - M.coboundary _) (hA v) (choose_spec _)
        (fun g i ↦ by simpa [hu g ⟨v, by tauto⟩] using u g ⟨v,
        (·.elim h fun ⟨j, e⟩ ↦ s.level_notMem j (e ▸ n)), _, hA v, i⟩)
          (congr($(a.2).2 ⟨v, n, h⟩) :) g ‹_›)
    cases eq_one_or_isComplexConj ‹_›; simpa [*] using b.2 1 1; simp [*, by simpa using C.2])
  have {v} : Finite (J v) :=
    .inter_of_right (((hA v).decompGroup_spec _).1.finite_Z1_local (M.restrictTo _)) _
  simpa [Nat.card_fun, Nat.card_pi, ← ncard_sdiff_add_ncard_of_subset (t := T) hT, pow_add,
    ← S.prod_attach, add_rotate (ncard _), ← mul_assoc] using! F.ker.card_mul_index.ge.trans
    (mul_le_mul' (hk.2.trans' (Nat.card_le_card_of_injective (⟨_, hf ·⟩) fun _ _ _ ↦ by
    ext <;> grind)) ((AddSubgroup.index_ker F).trans_le F.range.card_le_card_addGroup))

/-- Relations at split primes. For U fixing M and μ_m, without complex conjugations, there are
split primes, Frobenii φ_i and elements γ_i such that each family (n_i) with ∑ n_i(x(γ_i)) =
0 on Selmer cocycles x extends to an equivariant homomorphism on U giving such relations at
other split primes. A bound on trivialised cocycles bounds their number below.

Known result: Greenberg–Wiles formula, as a lower bound for the dual side. -/
lemma exists_split_primes_relations N [AddCommGroup N] [Module (ZMod m) M] U (hU :
  M.TrivialOn U.1.1) (hUm : ∀ g ∈ U, cycCharMod Ω m g = 1) (hc : ∀ {c}, IsComplexConj c →
  c ∉ U) : let Y := selmerZ1 M S A L; ∃ q ι I, ∃ (_ : NeZero q) (_ : Fintype ι) (s :
    SplitPlaces m q I U ι) (γ : ι → _), ∃ π T, (∀ v ∈ S, ↑q ∈ v.1) ∧ S ⊆ T ∧ IsLocallyConstant π ∧
    (∀ [Finite M], M.HasFewCocycles (PlaceAboveS q) I (card ι + 1) → .card (Y ∅) * .card M ^ (#S
    + card (InfinitePlace K)) ≤ .card {n : ι → M →+ QZ | ∀ x ∈ Y (.range s.v), ∑ i, n i (x (γ i)) =
    0} * .card M * ∏ v ∈ S, Nat.card ↥(L v ⊓ Z1 (M.restrictTo _).ρ)) ∧ s.FrobeniiDetectRoots ∧ ∀ n :
    ι → M →+ N, (∀ x ∈ Y (.range s.v), ∑ i, n i (x (γ i)) = 0) → (∀ i, n (π (s.φ i)) = n i) ∧
    (∀ g, ∀ a ∈ U, ∀ b ∈ U, ∀ x, n (π (a * (g * b * g⁻¹))) x = n (π a) x + n (π b)
    ((cycCharMod Ω m g).1 • M.ρ g⁻¹ x)) ∧ ∀ {J : Type} [Fintype J] (v C φ δ : J → _), Injective v →
    (∀ j, v j ∉ T ∧ IsPlaceOver (C j) (v j) ∧ IsTameGeneratorFor m (C j) (δ j) ∧
    IsFrob (C j) (v j).q (φ j) ∧ φ j ∈ U) → ∀ x ∈ Y (.range v), ∑ j, n (π (φ j)) (x (δ j)) = 0 := by
  intro Z
  have o : Monotone Z := fun _ _ _ _ ↦ by simp [Z, selmerZ1, inertiaAbove]; grind
  have h {F} [Field F] [NumberField F] {T} (t : Set.Finite T) := t.eventually_all.2 fun
    (v : FinPlace F) _ ↦ .mono (mem_atTop _) fun _ h ↦ v.1.mem_of_dvd
    (Nat.dvd_factorial v.one_lt_q.le h).natCast v.1.absNorm_mem
  obtain ⟨r, hT, hr, i, d⟩ := ((h S.finite_toSet).and (.and (mem_atTop m) (.and (h (finite_ramified
    U.1.2)) ((@finite_range _ _ (fixedFieldOf U.1.1).lift (.of_equiv _
    IsGalois.intermediateFieldEquivSubgroup.1.symm)).eventually_all.2 fun F _ ↦ .all fun
    _ : NumberField F ↦ (exists_sup_idelesUnitOff_eq_top finite_empty).elim fun _ ⟨e, _, _, f⟩ ↦ (h
    e).mono fun _ k ↦ eq_top_mono (sup_le_sup_left (idelesUnitOff_mono (K := F) k) _) f)))).exists
  have n := mk r.factorial_ne_zero
  -- the m-th roots of the U-fixed r!-units form a finitely generated group
  obtain ⟨T, j⟩ := fg_of_fg_map_of_fg_inf_ker (m • .id) (.of_le (Module.Finite.iff_fg.1
    (dirichlet_fixedSUnits _ r.factorial U).1) (map_comap_le ..)) (.of_le
    (fg_range (rootPowHom Ω m).1.toIntLinearMap) fun _ h ↦ by exact ((rootPowHom ..).2.2 _).2 h.2)
  obtain ⟨⟨O, h⟩, F⟩ := exists_openNormalSubgroup_apply_eq (Y := T) ((unitsModule
    Gal(Ω/K)).continuous.comp (f := Prod.map id (↑)) (by fun_prop)), @finite_natCast_mem K _ _ _ n
  let ι := _ ⧸ O.1.1
  have hN {g k} (e : (⟦g⟧ : ι) = ⟦k⟧) y (m : m • y ∈ fixedSUnits _ U) : unitsRep k y =
    unitsRep g y := LinearMap.eqOn_span (by simpa using!
    (congr(unitsRep g $(h _ (QuotientGroup.eq.1 e) ·)))) (j.ge m)
  obtain ⟨_, ⟨e, _⟩, u, H⟩ := ofFinite ι, exists_injective_nat ι, seq_of_forall_finite_exists
    fun t f ↦ skolem.1 fun c ↦ chebotarev (U.1.2.inter (isOpen_discrete {(@invFun U ι _ (↑)
    c : ι)})) ⟨_, by simp, rfl⟩ (F.union (f.seq finite_univ))
  choose a _ P hP φ b hφ _ using fun c ↦ by simpa using H (e c) c
  let s : SplitPlaces .. := ⟨hUm, Nat.dvd_factorial one_le hr, _, by grind [Injective], by grind, P,
    hP, φ, (⟨hφ ·, (b _).1⟩), by congr!, by grind, fun F i ↦ (d F ⟨_, F.lift_restrict ·⟩ i)⟩
  have hκ g h : (s.φ ⟦g⟧ : ι) = g := (b _).2.trans (@apply_invFun_apply U ι (↑) ⟨g, h⟩)
  obtain ⟨_, γ, hγ⟩ := by simpa using hκ 1, skolem.1 (exists_isTameGeneratorFor Gal(Ω/K) m <| hP ·)
  have z {P x} (h : x ∈ Z P) i n : _ = _ := h.1.2 _ ⟨_, (·.elim (s.level_notMem i ∘ hT _) n), _,
    hP i, (hγ i).1⟩
  refine ⟨_, ι, _, n, ‹_›, s, γ, (↑), S ∪ F.toFinset ∪ univ.image s.v, hT, by simp,
    isOpen_discrete, fun k ↦ ?_, by grind, fun ν hν ↦ ?_⟩
  have := by simpa [pairingAnnihilator, Nat.card_pi] using (card_pairingAnnihilator_mul_card (∑ i,
    (evalAddMonoidHom _ i).flip.comp (evalAddMonoidHom _ (γ i))) (.refl _) (Z (range
    s.v)).toAddSubgroup).ge.trans' (mul_le_mul_right (Nat.card_mono ((finite_unramified_cocycles
    M).subset fun _ ↦ (·.2.1)) fun x h ↦ .intro (by simp [z h]) (o bot_le h)) _)
  grw [← mul_le_mul_iff_right₀, ← mul_assoc, this, mul_assoc,
    card_mul_pow_le hu hA L hL @hcM s k hT, pow_succ]
  ac_nf
  simp
  have fam {J I} [Fintype J] (s : SplitPlaces m r.factorial I U J) (γ : J → _) hγ i j k g (E :
    (s.φ i : ι) = ↑(s.φ j * (g * s.φ k * g⁻¹))) a : ∃ z ∈ Z (range s.v), ∀ n, z (γ n) = ite (n =
    i) a 0 - ite (n = j) a 0 - ite (n = k) ((cycCharMod Ω m g).1 • M.ρ g⁻¹ a) 0 :=
    (s.power_residue_reciprocity γ hγ hU).rec fun b ⟨h, t⟩ ↦ by
    obtain ⟨⟨P, hP, _⟩, _, _⟩ := t.2 ⟨fun _ ↦ not_isReal_iff_isComplex.1 (exists_isComplexConj
      U.1.1 · |>.rec (flip hc ·.2))⟩ (Pi.single (i, 1) 1 - Pi.single (j, 1) 1 - Pi.single (k,
      mk g⁻¹) ↑(cycCharMod Ω m (s.φ j * g))) (fun y ↦ (y.1.exists_nsmul (ne m)).rec fun x q ↦
      (rootPowHom Ω m).2.1 (by simp [q, sub_mul, mul_comm (b _ _), map_cycCharMod_mul, h _ x,
      ← hN E, -map_mul, unitsRep.map_mul, h (fixedSUnitsRep _ U g⁻¹ y) _
      (q ▸ map_nsmul (unitsRep _) ..).symm])) a, skolem.1 (mk_out_eq_mul U.1.1)
    have c x g (e : g • x = x) := sub_eq_of_eq_add' (e ▸ hP.2.1 ..)
    have f B h g e := c (.inl ⟨B, h⟩) g congr(.inl ⟨$e, _⟩)
    use P.2, ⟨⟨trivialisedCocycles.snd_mem_Z1 hP, fun g ⟨v, n, B, k⟩ ↦ byCases (hP.2.2 g) fun _ ↦ f
      B (by grind [s.mem_inertia_iff, k.1.valuation_natCast_lt_one_iff]) g k.2.1 ▸ by simp [hu g ⟨v,
      n ∘ .inl, _, k⟩]⟩, fun v h ↦ hL v h ⟨_, funext (f _ ((hA v).valuation_natCast_lt_one_iff.2
      (hT v h)) _ ·.2)⟩, fun g h ↦ c (.inr _) g (congrArg _
      ((mem_stabilizer_mk_iff ..).2 (.inr (RingHom.ext h.choose_spec).symm))) ▸ by simp [hcM h]⟩
    simp [*, apply_ite (M.ρ _), ite_and, -mk_inv, ← mk_one, ZMod.map_smul, s.isFrob, sub_smul]
  have T i j k g E a := (fam s _ hγ i j k g E a).elim fun _ h ↦ by simpa [h, apply_ite (ν _), ι,
    sub_eq_iff_eq_add'] using (hν _ h.1)
  have := by simpa [*] using T 1 1 1 1
  refine ⟨fun i ↦ by ext; simp [*, T i (s.φ i) 1 1, s.isFrob], fun g a ha b hb ↦ T _ _ _ g (by simp
        [↓hκ, mul_mem ha (U.2.1 _ hb _), *]), fun v C φ δ hv H x hx ↦ ?_⟩
  choose _ n m c d f using by simpa [and_assoc] using H
  let s' : SplitPlaces .. := ⟨hUm, s.2, _, s.4.sumElim hv (swap m), Sum.rec s.level_notMem n,
    Sum.rec P C, Sum.rec hP
    c, Sum.rec _ φ, Sum.rec s.isFrob f, by congr!, s.inertiaGroup_le, s.principal_sup_idelesUnitOff⟩
  choose u hw _ _ using fun j ↦ by simpa using (fam s' (Sum.rec γ δ)
    (Sum.rec hγ d) (.inr j) (.inl (φ j)) (.inl 1) 1 (by simp [s', *]) (x (δ j)))
  simpa [*, apply_ite (ν _), @sum_comm _ _ ι, ι, z hx, Ne.symm (m _ _)] using hν _ ((sub_mem (o (by
    simp [s']) hx) (sum_mem fun _ _ ↦ hw _)).imp_left fun ⟨y, z⟩ ↦ ⟨y, fun τ ⟨w, h, B, b, c⟩ ↦ if o
    : w ∈ range v then o.rec (s'.apply_inertia_eq_zero b (i := .inr ·) · (d _) ⟨_,
    y⟩ hU (by simp [*]) c) else z τ ⟨w, h ∘ by simp [s', o], B, b, c⟩⟩)
end selmerZ1
end

-- part: Lib.ClassField.GreenbergWiles.SelmerMembership
section
/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Set-up used by: Greenberg–Wiles formula, as a lower bound for the dual side.

This file: Membership in Selmer groups of cocycles; dropping conditions and places where
unramified. -/


open Matrix.Module
variable {E : Type} {Λ n B} [Field E] [EmbeddedNumberField E] [CommRing Λ] [Fintype n]
  [AddCommGroup B] [Module Λ B] {ρ : Gal(Ω/E) → Matrix n n Λ} {S T L K c}

lemma mem_selmerModule_iff : c ∈ selmerModule ρ S L B ↔ (∀ g h, c (g * h) = c g + ρ g • c h) ∧
  (∀ g ∈ inertiaAbove Sᶜ, c g = 0) ∧ c ∈ obeying L B ∧ IsLocallyConstant
  c := by simp [selmerModule, obeying, ↓iInf_union, ← mem_obeying_cocycleRels]; tauto

/-- A member c of the Selmer module for (S, L) lies in that for (T, K) if K ⊆ L and c vanishes
on inertia at all places of S outside T. -/
lemma selmerModule_mono (k : c ∈ selmerModule ρ S L B) (l : K ⊆ L) (h : ∀ v ∈ S \ T,
  ∀ g ∈ inertiaAbove {v}, c g = 0 := by simp) :
  c ∈ selmerModule ρ T K B := by simp_all [mem_selmerModule_iff, obeying, inertiaAbove]; grind
end

-- part: Lib.ClassField.GaloisCohomology.TameCocycles
section
/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

Part of: Local Tate duality in degree 1, as an upper bound for orthogonal groups of cocycles (known
result; see Lib.ClassField.LocalDuality.CrystallineDuality).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Tame cocycles are determined by a tame generator and Frobenius; local length bound. -/


open Equiv.Perm Matrix Module MulAction LinearMap
variable {ℓ E O n} [Field E] [EmbeddedNumberField E] [CommRing O] [Fintype n] {ρ : Gal(Ω/E) →*
  Matrix n n O} {L} {A : ClosurePlace} {B} [AddCommGroup B] [Module O B] {M} (hB : ∀ b : B,
  ℓ ^ M • b = 0) {P : FinPlace E} (hA : IsPlaceOver A P) {c : _ → n → B} (hc : ∀ g h, c (g * h) =
  c g + ρ g • c h) {m} (hm : ∀ i ∈ inertiaGroup _ A, ρ (i ^ m) = 1) (ho : ∀ᶠ g in nhds 1, g ∈
  inertiaGroup _ A → ρ g = 1) (γ : inertiaGroup Gal(Ω/E) A) (hq : A.valuation (m * ℓ ^ M : ℕ) = 1)

variable (ρ L A B) in
/-- The restrictions to the decomposition group of A of the continuous cocycles of Gal(Ω over E)
for ρ with values in B^n that obey the relations L. -/
noncomputable def localCocycles :=
  (selmerModule ρ .univ L B).map (funLeft O _ (decompGroup _ A).subtype)

attribute [local simp] Equiv.ext_iff Units.smul_def coe_pow

/-- The affine action attached to a cocycle c: the homomorphism sending g to the permutation v ↦
c(g) + ρ(g)v of B^n. -/
noncomputable def affineAction := MonoidHom.mk' (fun g ↦
  .addLeft (c g) * toPerm (ρ.toHomUnits g)) (by simp [*, mul_smul, add_assoc])

include hc in
lemma cocycle_apply_inv g :
  c g⁻¹ = -(ρ g⁻¹ • c g) := by simpa [eq_neg_iff_add_eq_zero, ← hc] using hc 1 1

include hA hB hm ho hq

/-- Let ℓ^M kill B, ρ kill m-th powers of inertia and inertia near 1, q = mℓ^M be a unit at A, c
a locally constant cocycle, γ inertial. If c kills the tame generator, c(γ) = 0; in the
affine action γ commutes with Frobenii of exponent ≡ 1 mod q. -/
lemma tame_affineAction (hl : IsLocallyConstant c) : (c hA.tameGenerator = 0 → c γ = 0) ∧ ∀ ⦃k⦄,
  k ≡ 1 [MOD m * ℓ ^ M] → ∀ φ, IsFrob A k φ → Commute (affineAction hc φ) (affineAction hc γ) :=
  (fun K ↦ (hA.tame_inertia (affineAction hc) ((hl.eventually_eq 1).mp
  (ho.mono (by simp_all [← (affineAction hc).map_one, affineAction]))) hq K γ).imp
  (fun ⟨a, H⟩ z ↦ by simpa [affineAction, z, Function.iterate_fixed] using congr($H 0)) fun F k
  e ↦ by simpa [pow_eq_pow_of_modEq e, K, mul_inv_eq_iff_eq_mul, commute_iff_eq] using F k)
  (by simp_all [↓pow_mul, ↓← map_pow, affineAction, Function.comp_def, funext_iff])

/-- Let ℓ^M kill B, m-th powers of inertia and inertia near 1 act trivially, and mℓ^M be a unit
at A. Then `localCocycles` has length at most that of B^n plus that of ker(ρ(γ) − 1) on
B^n, for any inertial γ. -/
lemma length_localCocycles_le : length O (localCocycles ρ L A B) ≤ length O (n →
  B) + length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := (hA.exists_isFrob _).rec fun φ hφ ↦ by
  grw [← relLength_add_length_inf _ (proj ⟨_, hA.tameGenerator.2.1⟩).ker, relLength_ker,
    length_mono le_top, length_top, ← relLength_bot, relLength_le_of_inj (proj ⟨φ, hφ.1⟩),
    relLength_bot] <;> rintro _ ⟨⟨y, Y, rfl⟩, h⟩ <;> have C := (mem_selmerModule_iff.1
    Y).1 <;> have Z := (tame_affineAction hB hA C hm ho ⟨·, ·⟩ hq Y.2 |>.1 h)
  exacts [by simpa [*, sub_smul] using (Z _ (.inv_mul (by simpa) (γ.2.mul_iff.2 hφ)) ▸ C φ _ :),
    funext ∘ (hA.decompGroup_le hφ (U := cocycleKer _ C) (Y.2 {0}) Z · ·.2)]

omit hm ho hq

/-- Let γ be the tame generator at A over P ∤ ℓ, ρ unramified at v = P or P̄, ℓ^M B = 0. For σ'
= σ or σ^{−c}, Selmer cocycles killing γ' are unramified at v, and vanish on a decomposition
group if they also kill φ', φ a Frobenius at A. -/
lemma exists_conj_side_detects [NumberField.IsCMField E] {γ} (t : ↑hA.tameGenerator = γ) {v} (l :
  P ∉ placesDividing E ℓ) (u : ∀ g ∈ inertiaAbove {v}, ρ g = 1) (hv : v = P ∨ v = star P) : ∃ b A',
  IsPlaceOver (Ω := Ω) A' v ∧ ∀ {S L}, ∀ c ∈
  selmerModule ρ S L B, c (idOrConjInv b γ) = 0 → (∀ g ∈ inertiaAbove {v}, c g = 0) ∧ ∀ φ,
  IsFrob A P.q φ → c (idOrConjInv b φ) = 0 → ∀ g : decompGroup _ A', c g.1 = 0 := by
  have T θ {c} C u j g := (tame_affineAction hB hA (ρ := ρ.comp θ) (c := c) C (m := 1) (by simpa)
    (.of_forall u) g (by simp [hA.valuation_natCast_eq_one_iff.2 l]) j).1
  simp_rw [mem_selmerModule_iff, ← t]
  obtain rfl | ⟨hA, rfl⟩ := hv.imp_right (And.intro hA.conjPlace_star) <;> refine ⟨?_, _, hA,
    fun c ⟨C, _, _, j⟩ z ↦ (fun H ↦ ⟨fun g ⟨_, rfl, _, b, i⟩ ↦ (b.exists_smul _ hA).rec fun s k ↦ by
    simpa [*, mul_assoc] using (H (k ▸ i.conj s) ▸ C s⁻¹ _ :), fun φ f k ↦
    (hA.decompGroup_le ?_ (j {0}) H (?_ : ?_ ∈ cocycleKer _ C) ·.2)⟩) ?_⟩
  exacts [true, (T (.id _) C (u · ⟨_, rfl, _, hA, ·⟩) j ⟨·, ·⟩ z), f, k, false, (conjGal_conjGal · ▸
    T conjGal (by simp [C]) (fun _ ↦ (u _ ⟨_, rfl, _, hA, ·.conjPlace_conjGal⟩))
    (j.comp_continuous (by fun_prop)) ⟨_, @conjPlace_conjPlace A ▸ ·.conjPlace_conjGal⟩
    ((cocycleKer _ C).inv_mem z)), by simpa using f.conjPlace_conjGal, inv_mem_iff.1 k]
end
