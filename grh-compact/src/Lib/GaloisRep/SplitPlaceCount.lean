import Lib.ClassField.LocalEmbedding
import Lib.GaloisRep.FrobeniusFilter
import Lib.GaloisRep.LocalTranslates
import Lib.GaloisRep.WildType

-- part: Lib.GaloisRep.Main.AttachedDefs
section
/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Definition of attached representation and statement of the main theorem. -/


variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} {n} [Field E] [NumberField E] [Algebra E Ω]
  [Fintype n] [NumberField.IsCMField E] (P : FinPlace E → _)

/-- ρ is continuous and semisimple, j is open, and for each η > 0, most Frobenii s at w have
det(X − ρ(x)) coefficientwise within η of ιP_w whenever j(x) = s. -/
def Attached {H} [Group H] [TopologicalSpace H] (ρ : H →* GL n (PadicAlgCl ℓ)) (j : H → Gal(Ω/E) :=
    by exact id) := Continuous ρ ∧ IsTraceNondeg ρ ∧ IsOpenMap j ∧ ∀ η > 0, ∀ᶠ y in mostFrobenii E,
  ∀ x, j x = y.frob → ∀ i, ‖((ρ x).1.charpoly - .map ιℓ.toRingHom (P y.w)).coeff i‖ ≤ η

variable (E n) in
variable (E : Type) (n : _) [Field E] [CMType E] [Algebra E Ω] [Fintype n] in
/-- Every eigenform f on the standard space has an attached r; if K_w fixes f, every attached r is
unramified or crystalline at w, with the jumps of κ in rank N, and ιQ kills geometric Frobenius when
f has Hecke polynomial Q at w. -/
def SphericalCompat N w := ∀ ⦃P κ f⦄, f ∈ (stdSpace ..).forms κ → IsEigenform f P →
  (∃ r : GalRep ℓ E n, Attached P r) ∧ ∀ ⦃r : GalRep ℓ E n⦄, Attached P r → f ∈ levelSpace
  (rightRegular ℂ ..) (maxCompactAt n w) 1 → ∀ A, IsPlaceOver A w → IsGoodAt r A ∧
  HasJumpsAt r A (jumps κ N) ∧ ∀ hw Q,
  HasHeckePolyAt f w hw Q → ∀ s, IsFrob A w.q s⁻¹ → PolyKillsAt r A s (Q.map ιℓ.toRingHom)

lemma isRoot_of_isRoot_charpoly {K} [Field K] {M : Matrix n n K} {P x} (h : Polynomial.aeval M P =
  0) : M.charpoly.IsRoot x → P.IsRoot x := (by aesop) ∘ (·.dvd (charpoly_dvd_charpoly_aeval_comp P))
end

-- part: Lib.GaloisRep.Main.SplitPlaceCount
section
/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Enough places above a split quadratic place, using roots of unity. -/


open NumberField Filter Ideal IsCyclotomicExtension.Rat Set Finset
variable {E} [Field E] [NumberField E] [IsCMField E] {d} [HasQuadSubfield d E] {w : FinPlace E}

lemma IsSplitPrimeToDisc.star_ne (h : IsSplitPrimeToDisc (w.below (QuadField d))) :
  w.IsSplit := by grind [below_star, star_ne_and_prime_norm]

lemma eventually_notMem_star_notMem (ℓ : ℕ) [NeZero ℓ] (S : Finset (FinPlace E)) : ∀ᶠ w in cofinite,
  w ∉ S ∧ star w ∉ S ∧
  ↑ℓ ∉ w.1 := by simpa [↓eventually_and, finite_natCast_mem] using! S.finite_toSet.star

/-- For E stably unramified containing K = ℚ(√−d), u a split place of K prime to d
(`IsSplitPrimeToDisc`) and any places a, b of E, some place of E above u differs from a and b. -/
lemma IsSplitPrimeToDisc.exists_place_above_ne [U : StablyUnram E] {u} (h :
  IsSplitPrimeToDisc u) (a b : FinPlace E) : ∃ v, .below (QuadField d) v = u ∧
  v ≠ a ∧ star v ≠ a ∧ v ≠ b ∧ star v ≠ b := by_contra fun c ↦ by
  obtain ⟨⟨ζ, z⟩, p, o⟩ := U.1, h.star_ne_and_prime_norm.2.imp_left Fact.mk
  have H m e (k : ℕ+) [NeZero m] (t : _ = e * m ∧ ¬m.totient ≤ 4 * k.1 ∧ ∀ x : ZMod m, IsUnit x →
    x ^ k.1 = 1 := by open Calc in decide +kernel) : u.q ∣ m := by_contra fun n ↦ t.2.1 ((fun
    (K : IntermediateField ..) (_ : IsCyclotomicExtension _ ℚ K) ↦ by
    simp [← finrank m K, ← RingOfIntegers.rank, ← sum_ramification_inertia_eq_finrank
      (span {(u.q : ℤ)}), ramificationIdx_eq_of_not_dvd _ K _ n, inertiaDeg_eq_of_not_dvd _ K _ n]
    grw [orderOf_le_of_pow_eq_one k.2 (t.2.2 _ (ZMod.isUnit_prime_of_not_dvd p.1 n)),
      ncard_le_ncard (t := Finset.image (·.below K |>.1) {a, b, star a, star b}) fun P l ↦ by
      obtain ⟨v, ⟨⟩⟩ := FinPlace.comap_surjective (algebraMap K E) ⟨P, l.1, by cases l.2; aesop⟩
      exact mem_image_of_mem _ (by grind [=_ below_star, star_star, (o (v.below _)).2
        (by simpa using l.2.1.le)]), ncard_coe_finset, card_image_le, card_le_four]) _
    ((z.pow (by lia) t.1).intermediateField_adjoin_isCyclotomicExtension _))
  exact p.1.not_dvd_one (dvd_gcd (H 80 63 4) (H 63 80 6))
end
