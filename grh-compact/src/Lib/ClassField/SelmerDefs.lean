import Lib.ClassField.CpIntegers
import Lib.DiscreteSeries.FittingDuality
import Lib.Adelic.LocalComponents
import Lib.ClassField.CharacterLevels
import Lib.GaloisRep.ArtinMapAtPlace

section
/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Pseudocharacters, Brauer–Nesbitt, Clifford; compact subgroups of GL_n stabilise a lattice
(known result; see Lib.GaloisRep.Pseudocharacter.FibreSum).

This file: Integer rings of finite Galois extensions of Q_ℓ: DVR, compact, directed; length versus
cardinality. Compact groups in GL_n of l-adic closure stabilise a lattice; integral characteristic
polynomials. -/

open IsLocalRing Module Nat Filter InfiniteGalois IntermediateField IsDiscreteValuationRing Matrix
  PadicInt Prod Set Subalgebra Units minpoly

attribute [instance 10] Subalgebra.instSMulSubtypeMem Subalgebra.instMulActionSubtypeMem moduleLeft
  Subalgebra.instDistribMulActionSubtypeMem Subalgebra.instSMulWithZeroSubtypeMem
  Subalgebra.instMulActionWithZeroSubtypeMem

variable {R : Type*} (ℓ : ℕ) [ThePrime ℓ] {X Y : Type}

lemma card_eq_pow_length (ℓ : ℕ) [ThePrime ℓ] {X : Type} [CommRing R] [f : PadicIntegerRing R ℓ]
  [AddCommGroup X] [Module R X] h : Nat.card X = .card (ResidueField R) ^ (length R X).lift h := by
  induction length_ne_top_iff.1 h.ne; simp [card_unique]; expose_names
  let ⟨_, _, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 inst_6
  simp_all [length_eq_add_of_exact _ _ (by simp) N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
    card_congr e.toEquiv, N.card_eq_card_quotient_mul_card, isMaximal_iff]
  tauto

lemma length_le_of_card_dvd_or_le [CommRing R] [f : PadicIntegerRing R ℓ] [AddCommGroup X] [Module R
  X] [AddCommGroup Y] [Module R Y] (d : Nat.card X ∣ .card Y ∨ Nat.card X ≤ .card Y ∧ Finite X) :
  length R X ≤ length R Y := have : Finite (ResidueField R) := f.6.1 (not_a_field R)
  by by_contra! H; by_cases Finite X <;> simp_all [card_eq_zero_of_infinite,
    @card_eq_pow_length R, H.ne_top, ← not_le, length_ne_top,
    NeZero.ne, pow_dvd_pow_iff_le_right, pow_le_pow_iff_right₀, ↓Finite.one_lt_card]

/-- Rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`. -/
abbrev CoeffRing : Type := range fun K : FiniteGaloisIntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) ↦
    ⟨NormedField.valuation.integer.1, ((norm_algebraMap' ..).trans_le ·.2)⟩ ⊓
    K.toSubalgebra.restrictScalars ℤ_[ℓ]

variable {ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ} (x : ↑O)

instance : FaithfulSMul ℤ_[ℓ] (PadicAlgCl ℓ) := .trans _ ℚ_[ℓ] _

@[simp] lemma CoeffRing.norm_le_one : ‖x.1‖ ≤ 1 := by aesop

instance : Module.Finite ℤ_[ℓ] O := O.2.rec fun K e ↦ .of_fg (((IsIntegralClosure.finite _ ℚ_[ℓ] K
    _).1.map ((K.val.restrictScalars _).comp (integralClosure ..).val).toLinearMap).of_le
    (S := O.1.toSubmodule) (e ▸ fun x m ↦ have := monic (IsGalois.integral _ x); ⟨⟨⟨x, m.2⟩,
  coe_isIntegral_iff.1 ⟨_, Subtype.ext ‹_›, Polynomial.int_eval₂_eq (subring ℓ) _
  ((spectralValue_le_one_iff ‹_›).1 m.1) x ▸ aeval ..⟩⟩, ⟨⟩, rfl⟩))

lemma CoeffRing.dvd_iff_norm_le (y : ↑O) : x ∣ y ↔ ‖y.1‖ ≤ ‖x.1‖ := let ⟨_, K, rfl⟩ := O; ⟨fun ⟨c,
    h⟩ ↦ by simp [h, mul_le_of_le_one_right], fun _ ↦ ⟨⟨_, show ‖_‖ ≤ 1 by simp; bound, by
               aesop⟩, Subtype.ext (mul_div_cancel_of_imp' (by aesop)).symm⟩⟩

instance : DVR O := have := IsNoetherianRing.of_finite ℤ_[ℓ] O
  have : ValuationRing O := .iff_dvd_total.2 ⟨by simp [O.dvd_iff_norm_le, le_total]⟩
  {not_a_field' := Ideal.ne_bot_of_liesOver_of_ne_bot (not_a_field ℤ_[ℓ]) _}

lemma CoeffRing.exists_mem_of_mem_adjoin (s : Finset (PadicAlgCl ℓ)) : ∃ O : CoeffRing ℓ, ∀ x ∈
  adjoin ℚ_[ℓ] s, ‖x‖ ≤ 1 → x ∈ O.1 := ⟨⟨_, .adjoin .., rfl⟩, fun _ a ↦ (⟨·, le_normalClosure _ a⟩)⟩

instance : ContinuousSMul ℤ_[ℓ] (PadicAlgCl ℓ) := (subring ℓ).continuousSMul _

instance : CompactSpace O := Module.Finite.compactSpace ℤ_[ℓ] _

instance : IsDirectedOrder (CoeffRing ℓ) :=
    (monotone_const.inf (by tauto)).directed_le.directedOn_range.isDirectedOrder

lemma CoeffRing.eventually_mem {x} (a : ‖x‖ ≤ 1) : ∀ᶠ O : CoeffRing ℓ in .atTop, x ∈ O.1 :=
  eventually_atTop.2 ((exists_mem_of_mem_adjoin {x}).imp (by bound))

variable {n : Type} [Fintype n] {G : Type} [Group G] {O : CoeffRing ℓ} (r :
  G →* GL n (PadicAlgCl ℓ))

/-- The O-valued u is an integral form of r: there is P in GL_n(ℚ̄_ℓ) with u(g) = P⁻¹r(g)P for
all g in G. -/
def IsLatticeIn (u : G →* Matrix n n O) := ∃ P, ∀ g, ↑(P⁻¹ * r g * P) = (u g).map O.1.val

lemma IsLatticeIn.charpoly_eq_map {r : G →* GL n (PadicAlgCl ℓ)} {u : G →* Matrix n n O} (h :
  IsLatticeIn r u) g :
  (r g).1.charpoly = (u g).charpoly.map O.1.val := by erw [← charpoly_map, ← h.choose_spec]; simp

/-- A continuous representation of a compact group G on ℚ̄_ℓ^n is conjugate to one with entries
in O, for every large enough ring of integers O of a finite extension of ℚ_ℓ. -/
lemma eventually_exists_isLatticeIn {r :
  G →* GL n (PadicAlgCl ℓ)} [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (hr : Continuous r) : ∀ᶠ O in atTop, ∃ u, IsLatticeIn (O := O) r u := by
  choose c z e hm using exists_auerbach (Pi.basisFun ..) (fun x : Σ _, G ↦ .proj x.1 ∘ₗ
    (r x.2).1.toLin') (fun _ h ↦ funext (by simpa using h ⟨·, 1⟩)) (.id _) (by simp; fun_prop)
  let s := (MulAut.conj (mkOfMulEqOne _ (of z)ᵀ (.trans (Matrix.ext (congr($(e ·) <| z ·).symm))
    z.toMatrix_self))).toMonoidHom.comp r
  have hn g p : ‖s g (fst p) p.2‖ ≤ 1 := by simpa using! hm ⟨_, _ * g⟩ _
  have hs p : Continuous (s · (fst p) p.2) := by simp [s]; fun_prop
  choose D hD hc using (hs · |> isCompact_range |>.isSeparable)
  choose O _ using CoeffRing.exists_mem_of_mem_adjoin
  choose _ _ _ using fun g p ↦ exists_finset_of_mem_adjoin ((fixedField_fixingSubgroup _).le fun σ
    ↦ EqOn.closure (σ.2 ⟨·, subset_adjoin ℚ_[ℓ] _ ·⟩) (by fun_prop) continuous_id (hc p ⟨g, rfl⟩))
  choose m u using @nonempty_interior_of_iUnion_of_closed _ _ _ _ _ (countable_pi (hD · |>
    countable_ofPred_finite_subset |>.preimage Finset.coe_injective)) _
      (fun m ↦ isClosed_iInter fun p
    ↦ (isCompact_range (f := (O (m.1 p)).1.val) (by fun_prop)).isClosed.preimage (hs p)) (by aesop)
  choose t g a b using by
    simpa [subset_def] using compact_covered_by_mul_left_translates isCompact_univ u
  filter_upwards [Eventually.all (mem_atTop ∘' O ∘ m.1), t.eventually_all.2 fun g _ ↦
    .all (CoeffRing.eventually_mem ∘' hn g⁻¹)] with O' h h' using by refine ⟨⟨⟨fun x ↦
    of (⟨_, by simpa using O'.1.matrix.mul_mem (h' _ (a x) ⟨·, ·⟩) (h _ <| b x · ·) · ·⟩), ?_⟩, ?_⟩,
         _, by tauto⟩ <;> simp [entrywise, Subtype.ext_iff, apply_ite]
end

section
/-! Part of: Bound for the odd part of a twisted Tate–Shafarevich group of an abelian CM field
(known result; see Lib.Cyclotomic.OddSha.OddShaBound).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

This file: Complex conjugation, anticyclotomic characters, Selmer cocycles, Tate twists, odd Sha:
definitions. -/

noncomputable section


variable {ℓ : ℕ} [Fact ℓ.Prime] (E : Type) [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] {C} [CommMonoid C]

/-- E is a CM number field, stably unramified (`StablyUnram`), with an embedding in the algebraic
closure Ω of ℚ. -/
class UnramCMField E [Field E] extends EmbeddedNumberField E, NumberField.IsCMField E, StablyUnram E

/-- The valuation −log_ℓ|x| in [0, ∞], normalised by v(ℓ) = 1; it is ∞ at 0, and 0 for |x| ≥ 1. -/
def ellVal (x : PadicAlgCl ℓ) := ite (‖x‖ = 0) ⊤ (ENNReal.ofReal (-.logb ℓ ‖x‖))

/-- A complex conjugation in Gal(Ω/ℚ), chosen once and for all. -/
def cmConj := (exists_isComplexConj Gal(Ω/ℚ) Rat.isReal_infinitePlace).choose

/-- The chosen element c = `cmConj` of Gal(Ω/ℚ) is a complex conjugation: for some embedding j :
Ω → ℂ, j(cx) is the complex conjugate of j(x) for all x. -/
lemma isComplexConj_cmConj : IsComplexConj cmConj := .choose_spec _

/-- For a natural number N, the set of finite places of E whose prime ideal contains N. -/
def placesDividing (N : ℕ) := {v : FinPlace E | ↑N ∈ v.1}

instance : Fintype (placesDividing E ℓ) := (finite_natCast_mem ℓ).fintype

variable {E G O O' n} [CommRing O] [CommRing O'] [Fintype n] [Monoid G]

@[simp] lemma cmConj_cmConj x : cmConj (cmConj x) = x := congr($isComplexConj_cmConj.mul_self x)

/-- For a CM field E embedded in Ω, the chosen complex conjugation of Ω restricts to the complex
conjugation of E. -/
@[simp] lemma cmConj_algebraMap x : cmConj (algebraMap E Ω x) = algebraMap E Ω (star x) :=
  isComplexConj_cmConj.elim (·.injective <| map_star_complex (.comp ..) x ▸ · _)

/-- The endomorphism g ↦ g^c = cgc of the Galois group of Ω over E, c the chosen complex
conjugation. -/
def conjGal : Gal(Ω/E) →* Gal(Ω/E) :=
  .mk' ({cmConj * ·.restrictScalars ℚ * cmConj with commutes' := by simp}) (by aesop)

/-- χ is locally constant and χ(Art x) = η(x/x̄), η a character of finite ideles trivial on E^× and
on ideles that off S ∪ S̄ are units and ≡ 1 at the places of I outside S ∪ S̄. -/
structure IsFromU1 S I (χ : Gal(Ω/E) →* C) where
  isLocallyConstant : IsLocallyConstant χ
  exists_ideleChar : ∃ η : _ →* C, (∀ x, η (principalIdele x) = 1) ∧ (∀ a ∈ idelesUnitOff
    (.conjClosure S), (∀ w ∈ I \ S.conjClosure, Valued.v ((ideleAt w a).1 - 1) < 1) → η a = 1) ∧
    ∀ x (g : Gal(Ω/E)), artinMap Gal(Ω/E) x = g → χ g = η (x / star x)

/-- Given a ring map e:O→O', a character ψ:G→O' and a matrix representation ρ over O, the
representation g ↦ ψ(g)·e(ρ(g)) over O'. -/
def twistRep (e : O →+* O') (ψ : G →* O') (ρ : G →* Matrix n n O) :=
  smulMonoidHom.comp (ψ.prod (e.mapMatrix.1.comp ρ))

variable (ρ : Gal(Ω/E) → Matrix n n O) (S L B) [AddCommGroup B] [Module O B]

/-- The O-submodule of functions from a topological space G to an O-module B consisting of the
locally constant functions. -/
def locConst [TopologicalSpace G] : Submodule O (G → B) :=
  ⟨⟨⟨Set.ofPred IsLocallyConstant, (·.add)⟩, .const _⟩, fun _ ↦ (·.comp _)⟩

/-- The Selmer module: locally constant cocycles for ρ with values in B^n, unramified outside S
and obeying the relations L. -/
def selmerModule := obeying (cocycleRels ρ ∪ (.single · 1) '' inertiaAbove Sᶜ ∪ L) B ⊓ locConst _


variable (ℓ E) (Λ : Type) [CommRing Λ] [Algebra ℤ_[ℓ] Λ] (e ν : ℕ)

/-- The inverse of the ℓ-adic cyclotomic character of Gal(Ω/E), with values in the ℤ_ℓ-algebra
Λ. -/
def cycInv := (Units.coeHom _).comp (cycCharIn (Γ := Gal(Ω/E)) Λ Ω ℓ)⁻¹

/-- The rank-one representation Λ(−e): the character cyc^{−e} with values in Λ, as 1 × 1
matrices. -/
def tateTwist := (Matrix.scalar Unit).1.comp (cycInv ℓ E Λ ^ e)

/-- The union over places above ℓ of the inertia groups if e = 0, and of the kernels of cyc in
the decomposition groups if e ≠ 0. -/
def shaLocalSet := {g : Gal(Ω/E) | ∃ A : ClosurePlace, A.valuation ℓ < 1 ∧
  if e = 0 then g ∈ inertiaGroup _ A else g ∈ decompGroup _ A ∧ cycChar Ω ℓ g = 1}

/-- The locally constant cocycles z in (Λ/ℓ^νΛ)(−e), unramified outside ℓ, vanishing on
`shaLocalSet` for e, and, if e ≠ 0, odd: z(g^c) = −z(g). -/
def shaOdd := .pi (shaLocalSet ℓ E e) ⊥ ⊓ (⨅ _ : e ≠ 0, LinearMap.ker (1 + .funLeft _ _ conjGal)) ⊓
  selmerModule (tateTwist ℓ E Λ e) (placesDividing E ℓ) ∅ (QuotSpan (ℓ ^ ν : Λ))
end
end
