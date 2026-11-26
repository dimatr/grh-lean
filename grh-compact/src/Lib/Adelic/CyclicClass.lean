import Lib.Adelic.Base

section
/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Continuous cocycles, coboundaries, H² and functoriality for discrete modules. -/

noncomputable section


open Submodule DistribMulAction
variable {R G M H N} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M) [Group H] [TopologicalSpace
  H] [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N] {ρ' : Representation R
  H N} (φ : H →ₜ* G) (u : M →ₗ[R] N) (h : ∀ g m, u (ρ (φ g) m) = ρ' g (u m) := by bound)

instance (priority := 100) : ContinuousConstSMul R M := ⟨by fun_prop⟩

/-- The continuous 1-cocycles of ρ: the R-module of continuous f: G → M with f(gh) = f(g) +
ρ(g)f(h). -/
def Z1 := mk (R := R) ⟨⟨{f | Continuous f ∧ ∀ g h, f (g * h) = f g + ρ g (f h)},
  by simp_all [Continuous.add, add_add_add_comm]⟩, by continuity⟩ (by continuity)

/-- The R-linear map from M to functions G → M sending m to g ↦ ρ(g)m − m. -/
abbrev d0 := LinearMap.pi (ρ · - .id)

/-- The continuous 2-cocycles of ρ: continuous f: G × G → M with ρ(g)f(h,k) − f(gh,k) + f(g,hk)
− f(g,h) = 0. -/
def Z2 := ofLinearComb (R := R) {f | Continuous f ∧ ∀ g h k, f (g * h, k) = f (g, h * k) - f (g, h)
  + ρ g (f (h, k))} ⟨0, by continuity⟩ fun _ ⟨_, _⟩ _ ⟨_, _⟩ _ _ ↦
  ⟨by fun_prop, by intros; simp [*]; module⟩

/-- The 2-coboundaries of ρ: functions (g,h) ↦ ρ(g)c(h) − c(gh) + c(g) on G × G with c: G → M
continuous. -/
def B2 := ofLinearComb (R := R) {f : G × G → M | ∃ c, Continuous c ∧ ∀ g h, f (g, h) = ρ g (c h) -
  c (g * h) + c g} ⟨0, 0, by continuity⟩ fun _ ⟨c, _, _⟩ _ ⟨d, _, _⟩ a b ↦
  ⟨a • c + b • d, by fun_prop, by intros; simp [*]; module⟩

/-- Continuous cohomology H²(G,M): continuous 2-cocycles of ρ modulo coboundaries of continuous
1-cochains. -/
@[instance_reducible] def H2 := _ ⧸ (B2 ρ).comap (Z2 ρ).subtype deriving AddCommGroup, Module R

variable {ρ}

/-- For a continuous homomorphism φ: H → G and linear u: M → N with uρ(φg) = ρ'(g)u, the
additive map f ↦ u∘f∘φ from continuous 1-cocycles of ρ to those of ρ'. -/
abbrev pairMapZ1 : Z1 ρ →+ Z1 ρ' := ⟨⟨fun f ↦ ⟨(u <| f.1 <| φ.1 ·), f.2.imp (by continuity)
  (by aesop)⟩, by bound⟩, by bound⟩

/-- The linear map H²(G,M) → H²(H,N) induced by a compatible pair: continuous φ: H → G and
continuous φ-equivariant linear u: M → N. -/
def pairMapH2 : H2 ρ →ₗ[R] H2 ρ' := mapQ _ _ ⟨⟨fun f ↦ ⟨(u <| f.1 <| ·.map φ φ), f.2.imp (by
  fun_prop) (by aesop)⟩, by bound⟩, by bound⟩ fun f ⟨c, _, _⟩ ↦ ⟨u ∘ c ∘ φ, by fun_prop, by aesop⟩

variable (R) in
/-- The R-linear representation of a monoid G on M obtained from a homomorphism χ : G → S into a
monoid S acting R-linearly on M: g acts as χ(g). -/
abbrev actionRep M [AddCommMonoid M] [Module R M] {G S} [Monoid G] [Monoid S] [DistribMulAction S M]
  [SMulCommClass S R M] (χ : G →* S) : Representation R G M := (toModuleEnd ..).comp χ

/-- For an R-module M and a character χ: G → R^×, the representation of G on M in which g acts
as the scalar χ(g). -/
def charRep M [AddCommGroup M] [Module R M] (χ : G →* Rˣ) := actionRep R M ((Units.coeHom R).comp χ)
end
end

section
/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Profinite Galois groups, local fields, places, decomposition, inertia, Frobenius,
cyclotomic character. -/

noncomputable section

open NumberField Pointwise MulAction Units MulSemiringAction ValuationSubring SetLike


/-- A fixed algebraic closure of ℚ. -/
def Ω := AlgebraicClosure ℚ deriving Field, IsAlgClosed, CharZero

instance : Algebra.IsAlgebraic ℚ Ω := AlgebraicClosure.isAlgebraic ℚ

/-- The valuation subrings of Ω: its finite places, together with Ω itself (the trivial
valuation). -/
abbrev ClosurePlace := ValuationSubring Ω

/-- The element c of Γ is a complex conjugation: for some embedding j : Ω → ℂ, j(cx) is the
complex conjugate of j(x) for all x. -/
def IsComplexConj {Γ} [SMul Γ Ω] (c : Γ) := ∃ j : Ω →+* ℂ, ∀ x, j (c • x) = star (j x)

variable (O Γ : Type*) (K Ω : outParam Type*) [Group Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] (l : ℕ) [Fact l.Prime] [CommRing O] [Algebra ℤ_[l] O]

/-- The multiplicative group Ω^×, written additively; it is given the discrete topology. -/
abbrev DiscreteUnits := Additive Ωˣ

instance : TopologicalSpace (DiscreteUnits Ω) := ⊥

instance : DiscreteTopology (DiscreteUnits Ω) := ⟨rfl⟩

/-- The profinite group Γ acts on the Galois extension Ω/K as its Galois group, with open
stabilisers. -/
class IsProGalois [TopologicalSpace Γ] extends IsGaloisGroup Γ K Ω, IsGalois K Ω,
    IsTopologicalGroup Γ, CompactSpace Γ, TotallyDisconnectedSpace Γ where
  isOpen_stabilizer (x : Ω) : @IsOpen Γ _ (stabilizer Γ x)

/-- A place `A` of `Ω` is read as its valuation: `A x`. -/
instance : CoeFun (ValuationSubring Ω) (Ω → ·.ValueGroup) := ⟨(·.valuation)⟩

variable {Ω} (A : ValuationSubring Ω)

/-- The decomposition group of a valuation subring A of Ω: the elements of Γ mapping A onto
itself. -/
abbrev decompGroup := stabilizer Γ A

/-- For a valuation subring A of Ω and x in K, the value of the image of x in Ω under the
multiplicative valuation attached to A. -/
abbrev valuationVia x := A (algebraMap K Ω x)

/-- The valuation subring A ∩ K of K. -/
abbrev valRingBelow := (A.valuation.comap (algebraMap K Ω)).valuationSubring

/-- Γ = Gal(Ω/K) with Ω algebraically closed of characteristic 0 stabilises A, and A ∩ K is a
discrete valuation ring with finite residue field: K is a henselian local field. -/
class IsLocalGalois (A : outParam (ValuationSubring Ω)) [TopologicalSpace Γ] extends IsProGalois Γ K
  Ω, IsAlgClosed Ω, CharZero Ω where
  mem_decompGroup g : g ∈ decompGroup Γ A
  dvr : IsDiscreteValuationRing (valRingBelow K A)
  finite_residue : Finite (IsLocalRing.ResidueField (valRingBelow K A))

variable {Γ K} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The ℤ-linear representation of Γ on Ω^× (written additively) coming from the action of Γ on
the field Ω by ring automorphisms. -/
def unitsRep : Representation ℤ Γ (DiscreteUnits Ω) :=
  @.ofMulDistribMulAction Γ _ _ _ mulDistribMulActionRight

/-- σ stabilises A and σx ≡ x^q modulo the maximal ideal for all x in A; for q the residue order
of the base, an arithmetic Frobenius. -/
def IsFrob q σ := σ ∈ decompGroup Γ A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ • x - x ^ q) < 1

/-- The valuation subring A of Ω lies over the prime v of K: an integer of K is in the maximal
ideal of A exactly when it lies in v. -/
def IsPlaceOver := ∀ x : 𝓞 K, A.valuation (algebraMap K Ω x) < 1 ↔ x ∈ v.asIdeal

variable {A q} {σ τ g : Γ} {Γ' Ω'} [Group Γ'] [Field Ω'] [MulSemiringAction Γ' Ω'] {φ : Γ' → Γ}
  {j : Ω →+* Ω'} (e : ∀ g x, j (φ g • x) = g • j x) {A' s q'} (h : IsFrob A q σ)

lemma mem_decompGroup_iff : σ ∈ decompGroup Γ A ↔ ∀ x, σ • x ∈ A ↔ x ∈ A :=
  ext'_iff.trans mem_stabilizer_set

lemma smul_eq_comap : g • A = A.comap (toRingHom _ _ g⁻¹) := ext' (Set.preimage_smul_inv ..).symm

lemma conj_mem_decompGroup_smul : σ ∈ decompGroup Γ A →
  g * σ * g⁻¹ ∈ decompGroup Γ (g • A) := by simp_all [mul_smul]

lemma isEquiv_comap : (comap A' j).valuation.IsEquiv (A'.valuation.comap j) :=
    Valuation.isEquiv_of_val_le_one (by simp)

lemma val_comap_lt_one {x} : (comap A' j) x < 1 ↔ A' (j x) < 1 := isEquiv_comap.lt_one_iff_lt_one

attribute [local simp↓] IsFrob mem_decompGroup_iff mul_smul smul_sub val_comap_lt_one

lemma val_smul_lt_one (g : Γ) {x} : (g • A) (g • x) < 1 ↔ A x < 1 := by rw [smul_eq_comap]; simp

include e

lemma decompGroup.map : s ∈ decompGroup _ A' → φ s ∈ decompGroup Γ (A'.comap j) := by aesop

lemma IsFrob.map : IsFrob A' q s → IsFrob (A'.comap j) q (φ s) := by simp_all

omit e
include h

lemma IsFrob.conj g : IsFrob (g • A) q (g * σ * g⁻¹) := by rw [smul_eq_comap]; aesop

/-- If σ is a Frobenius at A for the exponent q, then στ is a Frobenius for qq' exactly when τ
is a Frobenius for q'. -/
lemma IsFrob.mul_iff : IsFrob A (q * q') (σ * τ) ↔ IsFrob A q' τ := (mul_mem_cancel_left h.1).and
  (forall₂_congr fun x _ ↦ .trans (by simp [pow_mul']; rfl) ((add_mem_cancel_right
  (H := A.nonunits) (h.2 (x ^ q') (by grind [pow_le_one']))).trans (h.1 ▸ val_smul_lt_one σ)))

lemma IsFrob.pow n : IsFrob A (q ^ n) (σ ^ n) := n.rec (by simp) (by grind [mul_iff, pow_succ])

variable (Γ A) in
/-- The inertia group of A: the σ in Γ stabilising the valuation subring A with σx − x in the
maximal ideal for every x in A. -/
def inertiaGroup : Subgroup Γ :=
  ⟨⟨⟨{σ | IsFrob A 1 σ}, (·.mul_iff.2)⟩, by simp⟩, (·.mul_iff.1 (by simp))⟩

lemma IsFrob.inv_mul : IsFrob A q τ → σ⁻¹ * τ ∈ inertiaGroup Γ A := h.mul_iff.1 ∘ by simp

variable (Ω)

/-- The ℓ-adic cyclotomic character Γ → ℤ_ℓ^× of a group Γ acting on the field Ω by ring
automorphisms. -/
def cycChar : Γ →* ℤ_[l]ˣ := (cyclotomicCharacter Ω l).comp (toRingAut ..)

/-- The ℓ-adic cyclotomic character of Γ composed with ℤ_ℓ^× → O^×, for a commutative
ℤ_ℓ-algebra O. -/
abbrev cycCharIn := (map (algebraMap _ O).1).comp (cycChar (Γ := Γ) Ω l)
end
end

section
/-! Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand
quotient (known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Discrete Q/Z, continuous characters and the cyclic symbol δχ ∪ w. -/

noncomputable section

/-- The group ℚ/ℤ; it is given the discrete topology. -/
def QZ := AddCircle (1 : ℚ) deriving AddCommGroup, DivisibleBy _ ℤ

instance : TopologicalSpace QZ := ⊥

instance : DiscreteTopology QZ := ⟨rfl⟩

/-- The quotient homomorphism ℚ → ℚ/ℤ. -/
def QZ.mk : ℚ →+ QZ := QuotientAddGroup.mk' _

variable (a : QZ) {R} (G) {M} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R G M)

/-- For a class a in ℚ/ℤ, its unique rational representative in the interval [0,1). -/
def QZ.fracRep := (a.equivIco 1 0).1

/-- For a, b in ℚ/ℤ, the integer part of the sum of their representatives in [0,1), an integer
equal to 0 or 1. -/
def QZ.carry b := ⌊fracRep a + fracRep b⌋

@[simp] lemma QZ.mk_fracRep : mk a.fracRep = a := a.coe_equivIco

lemma QZ.fracRep_mk r : fracRep (mk r) = Int.fract r := toIcoMod_zero_one r

@[push_cast] lemma QZ.cast_carry b : carry a b = fracRep a + fracRep b - fracRep (a + b) := by
  simp [carry, ← Int.self_sub_fract, ← fracRep_mk]

/-- Continuous characters `G → ℚ/ℤ`. -/ abbrev QZChar := Z1 (.trivial ℤ G QZ)

variable {G}

/-- The class δχ ∪ w in H²(G,M) of the cocycle (g,h) ↦ carry(χ(g), χ(h))·w, biadditive in the
character χ: G → ℚ/ℤ and the invariant w. -/
def cyclicClass : QZChar G →+ ρ.invariants →+ H2 ρ := by refine (.mk' (fun χ ↦ .mk' (fun w ↦
  ⟦⟨fun p ↦ (χ.1 p.1).carry (χ.1 p.2) • w, χ.2.imp (by fun_prop) ?_⟩⟧) ?_) fun ⟨χ, _, _⟩ ⟨ψ, _, _⟩ ↦
  AddMonoidHom.ext fun w ↦ QuotientAddGroup.eq_iff_sub_mem.2 ⟨fun g ↦
  (χ g).carry (ψ g) • -w, by fun_prop, ?_⟩) <;> intros <;>
  simp_all [(ρ.mem_invariants _).1 (Subtype.prop _)] <;>
  first | rfl | (match_scalars; qify; grind)
end
end
