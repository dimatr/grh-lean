import Lib.PadicHodge.DeterminantBound
import New.Weil.LevelPlacesChosen

section
/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Part of: Galois representations of theta lifts: irreducible block plus string (see
New.Selmer.RowsExist).

This file: here (unlike New.Rows, New.Columns, where they are forms) a column is a conjugate
self-dual ℓ-adic representation with prescribed jumps, unramified off S and ℓg, and a row is one
with S empty whose lattices span all matrices. Also the Selmer length bound and the unit cr_ℓ.
Apt labels, idempotents, normalising character, labelled columns, row-plus-string predicate. -/

noncomputable section

variable {ℓ} [ThePrime ℓ] {P} (D : Data P) [PadicIso ℓ] {n} [Fintype n] (t)
  (J : (D.E →+* ℂ) → Multiset ℤ) (ψ : AbsGal D →* PadicAlgCl ℓ) (S) (R : GalRep ℓ D.E n)

/-- R is continuous, has non-degenerate trace form, and is conjugate self-dual on traces: tr
R(g^c) = cyc(g)^{1−t} tr R(g⁻¹) for all g, with t = 0 read as t = 1. -/
structure IsConjSelfDual {D : Data P} {n} [Fintype n] t (R : GalRep ℓ D.E n) where
  continuous : Continuous R
  nondeg : IsTraceNondeg R
  trace_conj g : (R (conjGal g)).1.trace = cycInv ℓ _ _ g ^ (t - 1) * (R g⁻¹).1.trace

/-- The real number cr_ℓ = v_ℓ(Mk) + 2^{−ℓ}, where Mk is the integer `Data.chosenGroupOrder`. -/
def crudeUnit (ℓ : ℕ) {P} (D : Data P) : NNReal := padicValNat ℓ D.chosenGroupOrder + (1 / 2) ^ ℓ

variable {D} in
/-- For all large O: z ∈ O, z − 1 is a unit, and on some lattice in ψR the element γ ∈ ker cyc
acts by z, and the continuous cocycles mod ℓ^m unramified off ℓg₀g₁, Q, Q̄, obeying
`crysRels`, zero at γ, have normalised length ≤ (10fn + 1)·`crudeUnit`, n the
rank. -/
def SelmerLengthLe Q m γ (z : intQpBar ℓ) := ∀ᶠ O : CoeffRing ℓ in .atTop, ∃ u ψ' y, y.1 = ↑z ∧
  IsLatticeIn R u ∧ (∀ g, ψ' g = ψ g) ∧ let ρ := twistRep (.id O) ψ' u; ρ γ = (y : ↑O) • 1 ∧
    IsUnit (y - 1) ∧ cycChar Ω ℓ γ = 1 ∧ O.normLength (Module.length O ↥(selmerModule ρ
    (placesDividing _ ℓ ∪ placesAboveG D ∪ .conjClosure Q) (crysRels ρ) (QuotSpan (ℓ ^ m : ↑O)) ⊓
    (LinearMap.proj γ).ker)) ≤ 10 * D.f * Fintype.card n * crudeUnit ℓ D + crudeUnit ℓ D

/-- A column of level S: R satisfies `IsConjSelfDual`; at places off S or above ℓg it is
potentially crystalline (finite on inertia off ℓ) with jumps J, and crystalline (unramified
off ℓ) if the place is prime to g. -/
structure IsColumn extends IsConjSelfDual t R where
  local_conditions : ∀ v ∉ S \ (placesDividing _ ℓ ∪ placesAboveG D), ∀ ⦃A : ClosurePlace⦄,
    IsPlaceOver A v → IsFiniteTypeAt R A ∧ HasJumpsAt R A J ∧ (v ∉ placesAboveG D → IsGoodAt R A)

/-- A row: `IsColumn` with S empty, jumps as in `IsRowType`, bounded v(det(R(γ) −
1)) at places above g, lattices spanning all matrices, and two elements acting by scalars,
one inertial and residually of large order. -/
structure IsRow extends IsColumn D t J ∅ R, IsRowType D (Fintype.card n) t J where
  inertia_above_g : ∀ v ∈ placesAboveG D \ placesDividing _ ℓ,
    ∀ ⦃A : ClosurePlace⦄ (h : IsPlaceOver A v), ∃ γ N, (D.IsChosen v → γ = h.tameGenerator) ∧
    A.valuation N.cast = 1 ∧ (∀ i ∈ inertiaGroup _ A, R (i ^ N) = 1) ∧
    ∀ b, ellVal ((R (idOrConjInv b γ)).1 - 1).det ≤ Fintype.card n * crudeUnit ℓ D
  span_and_scalar : ∀ᶠ O in .atTop, ∀ u, IsLatticeIn (O := O) R u → Submodule.span O
    (.range u) = ⊤ ∧ ∃ g i α, (cycChar Ω ℓ g).1 = D.g i ^ Fintype.card n ∧ u g = (α : ↑O) • 1
  exists_scalar_inertia : ∃ᵉ (γ ∈ inertiaAbove (placesAboveG D \ placesDividing _ ℓ)) (y :
    PadicAlgCl ℓ), (R γ).1 = y • 1 ∧
    ∀ᵉ (a) (j ∈ Set.Icc 1 (4 * Fintype.card n + 2)), ‖(y ^ ℓ ^ a) ^ j - 1‖ = 1

open Polynomial Fintype Set AlgHeckeChar AutChar
variable {ℓ : _} [ThePrime ℓ] {P : _} {D : Data P} [PadicIso ℓ] {r} {n : _} {m} [Fintype r] [Fintype
  n] [Fintype m] (O : AuxPair D.E r n) (k) (J : _) (c : ∀ i, (ResField (O.chosenPlace i))[X]) (S :
  _) (z) (R : _)

/-- The ℓ-adic avatar of the algebraic character bc(υ^{−r₋})·υ^r·|·|^{r/2}, r the rank of W and
r₋ its number of signs −1; it normalises representations of forms on V. -/
abbrev chiOneInv := (HasWeight.inv (μ := O.a).toAlgebraic (-card r) 0).avatar

/-- Let A lie over w ∤ ℓ and let s⁻¹ act on the residue field of A as the (Nw)^k-th power. Then
`chiOneInv` sends s to ι(ν_w)^{−k}, ν_w the scalar `AutChar.frobValue` for υ^{r₋} and the
rank of W. -/
lemma chiOneInv_spec {O : AuxPair D.E r n} {w : FinPlace _} {A : ClosurePlace} (a :
  IsPlaceOver A w) (l : ↑ℓ ∉ w.1) k {s} (h :
  IsFrob A (w.q ^ k) s⁻¹) : chiOneInv O s = ιℓ (O.a.frobValue r w)⁻¹ ^ k := by
  choose z _ e using a.exists_localArtin_eq h k
  simp [avatar_localArtin _ a _ e, ↓CharUnramifiedAt.apply_locIdele_eq_zpow _ z, *, frobValue,
    AutChar.spaceChar, HasWeight.toAlgebraic,
    HeckeChar.atUnif, ↓HasWeight.charUnramifiedAt_toAlgebraic]; ring

/-- The normalised representation: R twisted by the character `chiOneInv`. -/
abbrev normalisedRep := twistByChar (m := n) (chiOneInv O) R

/-- The label c_i with its roots multiplied by the element of the residue field that labels the
character ψ_w⁻¹, w the i-th chosen place of O and ψ the tame part of its character. -/
def twistedLabel i :=
  (c i).scaleRoots (charName (faithfulChar (ResField (O.chosenPlace i))) (O.ψ _)⁻¹).1

/-- O has the places of ϑ, tame part ω^jϑ (1 ≤ j ≤ m), odd ranks r' ≤ r, n − r' ≤ t; the c_i are
labels of degree r', twisted labels lack the root 1, and over each g_k one label is
primitive with r' = r, or X − 1 with r' = 1. -/
structure IsApt (ϑ : D.Twist) where
  toLevelPlaces_eq : O.toLevelPlaces = D.levelPlaces ϑ
  tame_part_eq : ∃ j ∈ Icc 1 D.m, O.ψ = D.ω ^ (j : ℤ) * ϑ.ψ
  odd : Odd (card r) ∧ Odd O.rankDiff
  rank_le : card r ≤ D.r ∧ O.rankDiff ≤ D.t
  isLabel i : IsLabel (card r) (c i)
  exists_primitive k : ∃ i, ↑(D.g k) ∈ (O.chosenPlace i).1 ∧
    (card r = D.r ∧ IsPrimitiveLabel (card r) (c i) ∨ card r = 1 ∧ c i = X - 1)
  isLabel_twistedLabel i : ¬(twistedLabel O c i).IsRoot 1

/-- The endomorphism of the space of forms given by the action of the group-algebra idempotent
attached to the tuple of labels c. -/
abbrev tupleProj := O.groupAlgAction (tupleIdem r c)

/-- R is a row, and for every tame character ϑ, each eigenform lifting z on a pair V with
character μϑ has normalised trace ψ·tr R + Σ_{e<t} cyc^{−e}, ψ the avatar of ϑ⁻¹. -/
def HasRow := (∃ τ, IsRow (n := r) D O.rankDiff τ R) ∧ ∀ {ϑ : D.TameChar} {V : AuxPair _ r n} {y H
  S}, V.μ = O.μ * ϑ.toAutChar → V.Lifts y z → IsEigenform y H → Attached H S → ∀ g, (normalisedRep V
  S g).1.trace = ϑ.invAvatar g * (R g).1.trace + ∑ e ∈ .range V.rankDiff, cycInv ℓ _ _ g ^ e

/-- R is a column (`IsColumn`) for k of type J and level S, and inertia at each chosen place
of O is killed through the tame characters given by the roots of its label c. -/
structure IsLabelledColumn extends IsColumn (n := m) D k J S R where
  labelled ⦃i A⦄ : IsLabelledAt A (faithfulChar (ResField (O.chosenPlace i))) (card r).factorial
    (PolyKillsAt R A) (c i)
end
end

section
/-! Set-up for this proof: size bookkeeping for the data of this proof.

Set-up for this proof: records of the data and parameters of this proof, names for its objects.

This file: Divisibility and counting bookkeeping at the level; lattice versus representation
dictionary. Basic properties of apt label tuples and their idempotents; a place off the level. -/

open Data Finset Fint Gf LinearMap Matrix NeZero

variable {P} (D : Data P) (ℓ : ℕ) [ThePrime ℓ]

/-- For 1 ≤ d ≤ rt, g_i^d − 1 divides `Data.chosenGroupOrder`. -/
lemma g_pow_sub_one_dvd_chosenGroupOrder {i d} (hd : d ∈ Set.Icc 1 (D.r * D.t)) :
  D.g i ^ d - 1 ∣ D.chosenGroupOrder := by
  grw [← D.card_GL_dvd_chosenGroupOrder (card_fin d ▸ hd.2), Nat.card_pi,
    ← dvd_prod_of_mem _ (mem_univ ⟨i, D.chosenEquiv i 1⟩),
    Subsingleton.elim (Classical.decEq _), card_GL_field, ← dvd_prod_of_mem _ (mem_univ ⟨0, hd.1⟩)]
  grind [chosen, Fintype.card_eq_nat_card, card_ResField, q_eq_g, dvd_rfl]

/-- For each of the two primes g_i and each 1 ≤ d ≤ rt, the ℓ-adic valuation of g_i^d − 1 is at
most `crudeUnit`. -/
lemma ellVal_le_crudeUnit i {d} (h : d ∈ Set.Icc 1 (D.r * D.t)) : @ellVal ℓ _ (D.g i ^ d - 1) ≤
  crudeUnit ℓ D := by simpa [pos, crudeUnit, ellVal_natCast,
  ne] using le_add_right (dvd_iff_ellVal_le.1 (g_pow_sub_one_dvd_chosenGroupOrder D h).natCast)

lemma card_le_of_subset_placesAboveG {T : Finset (FinPlace D.E)} (s : ↑T ⊆ placesAboveG D) :
    #T ≤ 4 * D.f := (univ.card_le_card_of_surjOn (D.chosen ⊕ᵥ star ∘ D.chosen) (s.trans fun _ ⟨_,
  a⟩ ↦ by simp [Set.range_comp, range_chosen, D.isChosen_star_iff a, em])).trans
  (by simp +arith [card_chosenPlace])

lemma exists_chosen_notMem_placesDividing :
    ∃ w i, D.IsChosen w ∧ w ∈ placesAboveG D \ placesDividing _ ℓ ∧ w.q = D.g i :=
  (D.g_injective.exists_ne ℓ).elim fun i h ↦ ⟨_, i, (D.chosenEquiv i 1).2.imp_right fun b ↦
  ⟨⟨⟨i, b⟩, h ∘ (FinPlace.charP_quotient _ b).eq _ ∘ FinPlace.charP_quotient _⟩, D.q_eq_g b⟩⟩

variable {D ℓ} {n} [Fintype n] {O : CoeffRing ℓ} {R} {u : AbsGal D →* Matrix n n O} (h :
  IsLatticeIn R u)

include h in
/-- If u is a lattice in R over O, some injective O-algebra map F from matrices over O to
matrices over ℚ̄_ℓ sends u(g) to R(g) and preserves determinants and traces. -/
lemma IsLatticeIn.exists_algHom : ∃ F : _ →ₐ[O] Matrix n n _, (⇑F).Injective ∧ (∀ g, F (u g) =
  R g) ∧ ∀ A, (F A).det = A.det.1 ∧ (F A).trace = A.trace := h.elim fun (P : ConjAct _) h ↦
  ⟨(MulSemiringAction.toAlgHom O _ P).comp (Algebra.ofId ..).mapMatrix, fun _ ↦ by
  simp [smul_left_cancel_iff, ← ext_iff], (eq_inv_smul_iff.1 <| h · |>.symm),
  fun A ↦ by erw [det_units_conj, trace_units_conj]; simp [Matrix.trace, det_apply]⟩

lemma IsLatticeIn.continuous (h : IsLatticeIn R u) (_ : Continuous R) : Continuous u :=
    Topology.IsInducing.subtypeVal.matrix_map.continuous_iff.2 (.congr (by fun_prop) h.choose_spec)

lemma IsLatticeIn.eq_one (h : IsLatticeIn R u) {g} (e : R g = 1) : u g = 1 :=
  h.exists_algHom.elim (by aesop)

lemma IsLatticeIn.trace_eq (h : IsLatticeIn R u) g : (u g).trace.1 = (R g).1.trace :=
  h.exists_algHom.elim (by grind)

variable {r} {n : Type} [Fintype r] [Fintype n] {O : AuxPair D.E r n} {c : (i : O.ChosenIndex) →
  Polynomial (ResField (O.chosenPlace i))} {ϑ y w} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure)

namespace IsApt

lemma card_le : IsApt O c ϑ → Fintype.card n ≤ 2 * D.n D.m := by
  grind [IsApt, Data.n, mul_le_mul_left D.le_m D.t]

lemma isSymmetric_tupleProj : (tupleProj O c).IsSymmetric :=
  O.innerAt_groupAlgAction (isCentralProj_tupleIdem _) _

lemma tupleProj_eq_self_of_mem_range : y ∈ (tupleProj O c).range → tupleProj O c y = y :=
  ((isCentralProj_tupleIdem _).1.map _).mem_range_iff.1

lemma range_tupleProj_mem_invtSubmodule X : (tupleProj O c).range ∈ (O.heckePolyOnForms hw hS
  X).invtSubmodule := O.range_groupAlgAction_mem_invtSubmodule fun _ _ ↦ (map_smul ..).trans
  (congrArg _ (map_heckePolyOp (algFormRep _ _ _) X fun _ h ↦ by rw [← Module.End.mul_apply,
  ← (commute_supportedOn_trivialOn h (by grind [liftResidue, mem_trivialOn, mem_supportedOn])).map,
  Module.End.mul_apply]).symm)

lemma _root_.frequently_isSplit_notMem_places (O : AuxPair D.E r n) : ∃ᶠ w in .cofinite, w.IsSplit ∧
  w ∉ O.places.conjClosure := frequently_prime_q.mp
  ((eventually_notMem_star_notMem 1 O.places.toFinset).mono (by grind [isSplit_of_q_prime]))
end IsApt
end
