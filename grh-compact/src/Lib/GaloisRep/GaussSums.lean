import Lib.GaloisRep.Conjugation
import Lib.GaloisRep.ZeroSymmetry

section
/-! Part of: Stickelberger annihilation and Kolyvagin–Rubin bound for odd twisted components (known
result; see Lib.Cyclotomic.Kolyvagin.ComponentBound).

Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand quotient
(known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Locally constant cocycles for a character with vanishing conditions; the odd
component. -/

variable {O} [CommRing O] {N} (l e : ℕ) [NeZero N] [Fact l.Prime] [Algebra ℤ_[l] O]
  (ψ : DirichletCharacter O N)

/-- The character Υ = cyc^e·ψ of Gal(ℚ̄/ℚ) with values in O^×: cyc is the l-adic cyclotomic
character, and ψ is read through the action on N-th roots of unity. -/
noncomputable def cycPowDirichlet :=
  cycCharIn (Γ := Gal(Ω/ℚ)) O Ω l ^ e * ψ.toUnitHom.comp (cycCharMod Ω N)

/-- The O-module of locally constant maps x : Gal(Ω/ℚ) → B with x(gh) = x(g) + χ(g)x(h) (cocycles
for the character χ) that vanish on the set s. -/
noncomputable def vanishingCocycles (χ : Gal(Ω/ℚ) →* Oˣ) B [AddCommGroup B] [Module O B] (s :
  Set _) := locConst (O := O) B ⊓ ⟨⟨⟨{x | (∀ g h, x (g * h) = x g + (χ g).1 • x h) ∧ ∀ g ∈ s,
  x g = 0}, by simp_all; grind⟩, by simp⟩, by simp_all [smul_comm (χ _).1]⟩

/-- The elements of Gal(Ω/ℚ(μ_N)) lying in the inertia group of some place above neither l nor
any prime of T. -/
def inertiaOff (N l : ℕ) [NeZero N] (T : Finset Nat.Primes) := {i | ∃ A, (i ∈ cycloGalGroup N ∧
  A.valuation l = 1 ∧ i ∈ inertiaGroup _ A) ∧ ∀ r ∈ T, ¬A.valuation (r : Ω) < 1}

/-- The locally constant O/l^ν-valued cocycles for (cyc^eψ)⁻¹ vanishing at `cmConj`, on inertia over
ℚ(μ_N) away from l, and on decomposition groups over ℚ(μ_{Nl^∞}) above l. -/
noncomputable abbrev component ν := vanishingCocycles (cycPowDirichlet l e ψ)⁻¹ (QuotSpan (l ^ ν :
  O)) (insert cmConj (cycloGalGroup N ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ shaLocalSet l ℚ 1)))
end

section
/-! Known result: Voronoi's congruence for twisted power sums and trivial zeros of Dirichlet
L-functions. The form here is twisted by a possibly imprimitive character and stated for power sums.
One non-zero integer with an explicit size bound is divisible by the Stickelberger elements for all
primes, characters ψ with ψ(−1) = −(−1)^e, and coefficient rings. Source: K. Ireland, M. Rosen, A
Classical Introduction to Modern Number Theory, 2nd ed. 1990; for the untwisted statement also M.
Eberl, Kummer's congruence, Archive of Formal Proofs 2024.

This file: Twisted Voronoi congruence, trivial zeros, one bounded integer divisible by all
Stickelberger elements. -/

open Finset DirichletCharacter Matrix Nat Polynomial Complex NeZero ZMod Real

lemma Nat.ModEq.coprime_of_modEq_one {a b} (h : a ≡ 1 [MOD b]) : a.Coprime b := by simpa using
  h.gcd_eq


variable (N e : ℕ) [NeZero N]

lemma smul_bernoulli_mem_lifts n : ((n + 1)! * N ^ n) • Polynomial.bernoulli n ∈
  (liftsRing (algebraMap ℤ ℚ)).comap (C N.cast⁻¹ * X).compRingHom := by
  rw [factorial, mul_assoc, mul_nsmul, bernoulli_eq_sub_sum, smul_sub, sum_range, smul_sum]
  refine sub_mem ⟨monomial _ (n + 1)!, funext (by simp [factorial, field, mul_pow])⟩ (sum_mem ?_)
  intros; rw [smul_comm, ← @Nat.div_mul_cancel _ (_ * _), mul_smul]
  solve_by_elim [nsmul_mem, smul_bernoulli_mem_lifts]; gcongr <;> lia

/-- Each prime l has some c ≡ 1 mod N, l ∤ c, with (c^e − 1)(c^{e+1} − 1) ∣ X; and for every c ≡
1 mod N and character ψ mod N into a characteristic zero domain O with (−1)^eψ(−1) = −1, one
w in O has (c^{e+1} − 1)X ≡ 2w∑_{0≤a<Nm} ⌊ca/(Nm)⌋a^eψ(a) mod m for all m ≥ 1 prime to c. -/
def IsStickelbergerBound X := (∀ l, Nat.Prime l → ∃ c, c ≡ 1 [MOD N] ∧ l.Coprime c ∧ (c ^ e - 1) *
  (c ^ (e + 1) - 1) ∣ X) ∧ ∀ c, c ≡ 1 [MOD N] → ∀ O [CommRing.{0} O] [IsDomain O] [CharZero O] (ψ :
  DirichletCharacter O N), ψ (-1) = -(-1) ^ e → ∃ w, ∀ m [NeZero m], m.Coprime c → ↑m ∣
  (c ^ (e + 1) - 1) * X - 2 * w * ∑ a ∈ range (N * m), ↑(c * a / (N * m)) * (a ^ e * ψ a)

attribute [local grind =] neg_one_pow_eq_ite Even.eval_neg Odd.eval_neg

/-- Trivial zeros: for a complex Dirichlet character χ mod N, not necessarily primitive, and e ≥
1, L(χ, −e) = 0 exactly when χ(−1) = (−1)^e.

Known result: Voronoi's congruence for twisted power sums; trivial zeros of Dirichlet
L-functions. -/
lemma LFunction_neg_nat_eq_zero_iff (χ : DirichletCharacter ℂ N) (he : e ≠ 0) :
    χ.LFunction (-e) = 0 ↔ χ (-1) = (-1) ^ e := by
  have := LFunction_one_sub_eq_zero χ (-e)
  simp_all [LFunction_ne_zero_of_one_le_re, LFunction_eq_completed_div_gammaFactor,
    gammaFactor, ite_eq_iff, Gammaℝ_eq_zero_iff]
  norm_cast at *
  grind [e.even_or_odd', χ.even_or_odd]

omit [NeZero N] in
/-- Voronoi's congruence, twisted by a Dirichlet character χ mod N: for f = Nm and c ≡ 1 mod N
prime to m, (c^{e+1} − 1)∑ χ(t)t^{e+1} ≡ (e+1)c^e f ∑ ⌊ct/f⌋t^e χ(t) mod f², both sums over
0 ≤ t < f.

Known result: Voronoi's congruence for twisted power sums; trivial zeros of Dirichlet
L-functions. -/
lemma voronoi_congruence {O} [CommRing O] (χ : DirichletCharacter O N) {f m c} [NeZero f] (h : f = N
  * m) (hc : m.Coprime c) (h₁ : c ≡ 1 [MOD N]) : (f : O) ^ 2 ∣ (c ^ (e + 1) - 1) * ∑ t, χ (@val f t)
  * t.val ^ (e + 1) - (e + 1) * c ^ e * f * ∑ t, ↑(c * @val f t / f) * (χ t.val * t.val ^ e) := by
  rw [sub_one_mul, mul_sum, sub_sub, dvd_sub_comm, ← Equiv.sum_comp (unitOfCoprime c (h ▸
    h₁.coprime_of_modEq_one.mul_right hc.symm)).mulLeft, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  exact dvd_sum fun t _ ↦ .trans ⟨_, mul_pow _ (-↑(c * t.val / f)) 2⟩
    ((sq_dvd_add_pow_sub_sub _ ↑(c * t.val) (e + 1)).trans ⟨_, by
    simp [val_mul, (c * _).mod_def, mul_div_le, h, (natCast_eq_natCast_iff ..).2 h₁]; ring⟩)

/-- For N, e ≥ 1 there is an integer 1 ≤ X ≤ 2^{(N+e+3)^6} with the property `IsStickelbergerBound`
N e X. -/
lemma exists_isStickelbergerBound (he : e ≠ 0) : ∃ X ≠ 0, X ≤ 2 ^ (N + e + 3) ^ 6 ∧
  IsStickelbergerBound N e X := by
  obtain ⟨⟨p, hp⟩, _⟩ := smul_bernoulli_mem_lifts N (e + 2), ne N
  let D := (e + 3)! * (e + 2) * N; let b := p.derivative.eval
  let M := D * N ^ e * (e + 1)!
  have (K) [RCLike.{0} K] t : b t = D * N ^ e * aeval (t / N : K) (bernoulli (e + 1)) := by
    have := congr((derivative $hp).aeval (t : K))
    simp [aeval_def, eval₂_comp, derivative_comp, derivative_bernoulli, derivative_pow] at *; grind
  replace hp t : p.eval (N.cast + t) = p.eval t + t ^ (e + 1) * D := by
    qify; replace hp (t : ℤ) := congr(eval ↑t $hp)
    simp_all [D, mul_add, bernoulli_eval_one_add, mul_pow]; field
  let g t := 2 * b (@val N t) + ite (t = 1) ((-1) ^ e) 0 + ite (t = -1) 1 0
  let T := of fun s t : _ˣ ↦ g (t / s).1
  have key O [CommRing O] (ψ : MulChar _ O) : T.map (↑) *ᵥ (ψ ·.1) = (∑ t, ψ t * g t) • (ψ ·.1) :=
    by
    ext s; apply (Equiv.sum_comp (.mulLeft s) _).symm.trans; simp [sum_mul]
    apply sum_of_injOn (↑) <;> simp_all [T, ψ.map_nonunit, IsUnit, Units.val_injective]; grind
  have := (Int.cast_det T).trans_ne (separatingLeft_iff_det_ne_zero.1 (separatingLeft_def.2 fun w h
    ↦ have k χ := (by simpa using (key ℂ χ ▸ h _ :) :).resolve_left (by
    have := (LFunction_neg_nat_eq_zero_iff N e χ he).symm.trans mul_eq_zero
    simp_all [g, mul_add, -natCast_val, toAddCircle_apply, ← mul_sum, val_le,
      mul_left_comm, HurwitzZeta.hurwitzZeta_neg_nat, cast_add_one_ne_zero, ↓unitInterval.div_mem]
    grind [even_or_odd χ, @ne ℂ _ M ⟨by norm_cast; positivity⟩])
    by ext a; simpa [dotProduct, sum_mul, sum_comm, ← mul_sum, mul_assoc, ← map_mul, ne,
      sum_characters_eq, -map_units_inv, Units.val_inj] using congr(∑ χ, $(k χ) * χ a⁻¹)))
  refine ⟨_, by simp_all [tsub_eq_zero_iff_le, add_assoc], ?_, fun l h ↦ (coprime_or_dvd_of_prime
    h _).elim (⟨_, add_modEq_right, ·, _, rfl⟩) (⟨1 + N + N, by simp, .of_dvd_left · (by simp),
    .mul_left ⟨T.det.natAbs, rfl⟩ _⟩), fun c h₃ O _ _ _ χ _ ↦ Dvd.elim (.trans ⟨_, by simpa
    [adjugate_mul, ← Int.cast_det] using (congr(toLin' (T.map (↑)).adjugate $(key O
    χ) 1))⟩ (by simp [← mul_assoc, ← sign_mul_self])) fun u U ↦ ⟨u * D * c ^ e * (e + 1), fun m _ hv
    ↦ (voronoi_congruence N e χ rfl hv h₃).elim fun v _ ↦
    ⟨2 * N * u * (D * v - (c ^ (e + 1) - 1) * ∑ t, χ t *
    p.binomExpansion t.val (N * m)), congr(_ * $U - _).trans (mul_left_cancel₀ (ne ↑(N * m)) ?_)⟩⟩⟩
  have (t) (_ : t ≤ N) : |b t| < M * 17 := by
    have := (@hasSum_one_div_nat_pow_mul_fourier (e + 1) (by lia) (t / N) ·
      |>.norm_le_of_bounded (hasSum_zeta_two.mul_right 6) fun n ↦ by
      grw [norm_mul, norm_add_le]; cases n <;> simp [-Nat.cast_add]; bound [he.pos])
    rify; simp [M, *, field, bernoulliFun] at *
    grw [← one_le_pow₀, pi_lt_four] at this <;> grind [two_le_pi]
  grw [show Int.natAbs _ ≤ _ * (M * 64) ^ _ by
    zify; simpa using T.det_le (abv := .abs) (by simp [T]; grind)]
  trans; apply_rules [tsub_le_self.trans, (factorial_le_pow _).trans,
    pow_le_pow_left', mul_le_mul', Nat.lt_two_pow_self.le]
  simp only [← pow_mul, ← pow_add]; gcongr; grw [totient_le]; lia
  have : ∀ f [NeZero f] F, (range f).sum F = ∑ a, (F (@val f a) : O) | _ + 1, _ => sum_range
  replace U := congr(∑ t ∈ range $(add_comm N (N * m)), χ t * p.eval ↑t)
  simp_all [add_comm (N * _), (p.binomExpansion _ (_ * _)).2, mul_add, g,
    ← mul_assoc, ← sum_mul, ↓sum_range_add, two_mul]; grind
end

section
/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Principal units, places above q, primes 1 mod m split in cyclotomic fields. -/


variable {q m : ℕ} [NeZero m] {B : ClosurePlace} [Fact q.Prime]

/-- The action of Gal(Ω/ℚ) on the multiplicative group Ω^×, written additively, as a ℤ-linear
representation. -/
noncomputable abbrev galUnitsRep := @unitsRep Gal(Ω/ℚ) Ω _ _ _

/-- The principal units of the valuation subring B of ℚ̄ (elements congruent to 1 modulo its
maximal ideal), as a subgroup of ℚ̄^× written additively. -/
noncomputable def principalUnits (B : ClosurePlace) : AddSubgroup (DiscreteUnits Ω) :=
  B.principalUnitGroup.toAddSubgroup

lemma exists_isPlaceOver_prime (h : B.valuation q < 1) : ∃ v : FinPlace ℚ, IsPlaceOver B v ∧ v.q =
  q ∧ ordRat ℚ B (.ofNeZero q NeZero.out) = 1 := (exists_rat_place_of_prime Fact.out).imp fun _ ⟨e,
  _, H⟩ ↦ ⟨H B h, e.1, by convert (H B h).ordRat_ofBase (Γ := Gal(Ω/ℚ)) (.mk0 ..) <;> aesop⟩

lemma decompGroup_le_cycloGalGroup (h : B q < 1) (k : q ≡ 1 [MOD m]) : decompGroup _ B ≤
  cycloGalGroup m := by
  obtain ⟨⟨_, v, ⟨⟩, _⟩, c⟩ := exists_isPlaceOver_prime h, k.coprime_of_modEq_one.valuation_eq_one h
  exact (v.exists_isFrob _).rec fun _ f ↦ v.decompGroup_le f Fact.out (fun _ ↦
    (cycCharMod_of_mem_inertiaGroup · c)) ((f.mem_ker_cycCharMod_iff c).2 k)
end

section
/-! Known result: Stickelberger's factorisation of Gauss sums and the Davenport–Hasse product
relation. Only prime fields are treated, and characters are named by the valuation of their Gauss
sum. The product relation is proved for Jacobi-type quotients of Gauss sums and only up to a root of
unity. Source: L. Washington, Introduction to Cyclotomic Fields, 2nd ed. 1997, 6.2 and Thm 15.1; for
the product relation, H. Davenport, H. Hasse, J. reine angew. Math. 172 (1935).

This file: Valuations of Gauss sums, Jacobi-type quotients, distribution relation up to roots of
unity. -/

open AddChar Int MulChar NeZero NumberField QZ QuotientAddGroup ValuationSubring ZMod
  ComplexEmbedding Embeddings

attribute [local simp ←] map_nsmul_eq_pow Finset.mul_sum cast_sum self_sub_fract pow_apply_coe
  QZ.fracRep_mk RingHom.map_pow Submodule.Quotient.mk_eq_zero valuation_le_one_iff map_nsmul
  mul_assoc

attribute [local simp] map_add_eq_mul ne add_div div_sub_one map_eq_zero_iff

variable {r m p : ℕ} [NeZero r] [hp : Fact p.Prime] {B : ClosurePlace} (hB :
  B.valuation p < 1) {v} (c : ℕ) {ψ : AddChar (ZMod p) (𝓞 Ω)} {χ :
  AddChar (ZMod r) (MulChar (ZMod p) (𝓞 Ω))} (g : ZMod r → DiscreteUnits Ω)

/-- For c in ℕ and x in ℚ/ℤ, the integer ⌊c⟨x⟩⌋ − ⌊c⟨−x⟩⌋, where ⟨·⟩ is the representative in
[0,1). -/
noncomputable def floorDiff x := ⌊c * QZ.fracRep x⌋ - ⌊c * (-x).fracRep⌋

lemma sum_floorDiff : m.Coprime r → ∀ x, IsUnit v → ∑ b, floorDiff m (x + ofZMod r (v * b)) =
  floorDiff m (r • x) := by
  have (x) v (h : IsUnit v) := Fintype.sum_equiv (h.unit.mulLeft.trans (.addLeft ↑⌊r * QZ.fracRep
    x⌋)) (fun b ↦ (x + ofZMod r (v * b)).fracRep) (fun b ↦ (b.val + fract (r * x.fracRep)) / r)
    fun _ ↦ .trans (by simp [← ofZMod_apply, -natCast_val, ofZMod, ← map_zsmul, add_assoc,
    ← division_def, sub_div, ↓floor_div_natCast, ↓floor_natCast_add, ↓floor_fract,
    ediv_eq_zero_of_lt, val_lt]) (floor_add_fract _)
  qify; simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← isUnit_iff_coprime] at *
  simp_all [smul_comm r, ← map_neg, ← neg_mul, add_comm, mul_div_cancel₀]; grind

/-- Kronecker's theorem in an algebraic extension of `ℚ`: an element that lies in every
valuation ring and has absolute value one in every complex embedding is a root of unity. -/
lemma isOfFinOrder_of_norm_eq_one {x} (h : ∀ A : ClosurePlace, x ∈ A) (N : ∀ τ : Ω →+* ℂ, ‖τ
  x‖ = 1) : IsOfFinOrder x := by simpa [isOfFinOrder_iff_pow_eq_one, Subtype.ext_iff] using (
  pow_eq_one_of_norm_eq_one (fixedFieldOf (id (OpenSubgroup.mk _ (stabilizer_isOpen_of_isIntegral
  (K := ℚ) x))).1) ℂ (x := ⟨x, (·.2)⟩) (IntermediateField.coe_isIntegral_iff.1 ((integralClosure ..
  ).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge (by aesop))) (lift_algebraMap_apply Ω · _ ▸ N _))

/-- Galois action on non-zero Gauss sums g(t) of χ_t and ψ over 𝔽_p, with t ↦ χ_t a homomorphism
on ℤ/r: there are homomorphisms K_σ from ℤ/r to Ω^× with σg(t) = K_σ(at)·g(at), where a is
the cyclotomic character of σ modulo r. -/
lemma smul_gaussSum (hg : ∀ t, (g t).toMul.1 = gaussSum (χ t) ψ) : ∃ K :
    _ → ZMod r →+ DiscreteUnits Ω, ∀ σ t, galUnitsRep σ (g t) = (K σ + g) (cycCharMod Ω r σ * t) :=
    ⟨fun σ ↦ AddMonoidHom.mk' (fun t ↦ .ofNeZero ((χ t)⁻¹ (cycCharMod Ω p σ))
  (by simp [apply_eq_zero_iff])) (by simp [DiscreteUnits.ext_iff, field]), fun σ t ↦
  DiscreteUnits.ext (by simpa [cycCharMod_spec (N := p), cycCharMod_spec (N := r), *, gaussSum,
  sum_eq_add_sum_units, Finset.smul_sum] using congr($(gaussSum_mulShift_eq _ ψ _).val))⟩

include hB

/-- Let B be a place of Ω above the prime p. An algebraic integer x with x^p = 1 is congruent to
1 modulo the prime ideal that B defines. -/
lemma residue_eq_one_of_pow_prime_eq_one {x : 𝓞 Ω} (e : x ^ p = 1) : ↑x =
  (1 : _ ⧸ centrePrime Ω B) := by_contra (orderOf_eq_prime (congrArg _ e) · ▸
  IsPrimitiveRoot.orderOf _ |>.neZero'.1 (Ideal.mk_ker.ge (mem_centrePrime.2 hB)))

/-- Weak form of Stickelberger's theorem: for the Gauss sums g(t) of χ^t over 𝔽_p (χ of order r
prime to p, ψ non-trivial) and B above p with ord p = 1, 0 ≤ ord g(t) < 1, and t ↦ ord g(t)
is an injective homomorphism ℤ/r → ℚ/ℤ.

Known result: Stickelberger's factorisation of Gauss sums; Davenport–Hasse product relation. -/
lemma stickelberger (hg : ∀ t, (g t).toMul.1 = gaussSum (χ t) ψ) (hψ : ψ.IsPrimitive)
    (w : χ.IsPrimitive) (cp : p.Coprime r) : ∃ S :
    _ →+ QZ, (⇑S).Injective ∧ ∀ t, (S t).fracRep = ordRat ℚ B (g t) := by
  obtain ⟨⟨v, hv, _⟩, K, H⟩ := exists_isPlaceOver_prime hB, smul_gaussSum g hg
  let S := AddMonoidHom.mk' (QZ.mk <| ordRat ℚ B <| g ·) fun a b ↦ eq_iff_sub_mem.2 (by
    simpa [← map_add, ← map_sub, ← range_castAddHom, eq_comm] using
      hv.ordRat_int_of_inertia_fixed fun σ :
      Gal(Ω/ℚ) ↦ (by simp [H, cycCharMod_of_mem_inertiaGroup ·, cp.valuation_eq_one hB]; abel))
  have lt u {χ : MulChar (ZMod p) (𝓞 Ω)} {ψ} e h := ((hv.ordRat_nonneg_iff u).2 (Eq.subst (.symm e)
    (algebraMap_ringOfIntegers_mem B (gaussSum χ ψ)))).lt_of_ne' (hv.ordRat_eq_zero_iff.1.mt
    (e ▸ (mem_centrePrime.1 (by
    simpa [gaussSum, residue_eq_one_of_pow_prime_eq_one hB, -ne]
      using congr($(gaussSum_one_right h) ∈ centrePrime ..))).ne))
  have L t : (S t).fracRep = _ := (toIcoMod_eq_self _).2 (by_cases (by simp_all
    [hv.ordRat_eq_zero_iff.2, gaussSum_one_left (by simpa using @hψ 1)]) fun h ↦
    ⟨(lt _ (hg t) h).le, by simpa [*] using lt (.ofNeZero p out - g t) (by
    simpa [field, ← hg] using congr($((gaussSum_mul_gaussSum_eq_card h hψ).symm).val)) (by simpa)⟩)
  use S, .of_ker S fun t e ↦ by
    simpa [w.zmod_char_eq_one_iff, ← L, e, QZ.mk.map_zero ▸ QZ.fracRep_mk 0] using lt _ (hg t)

/-- Stickelberger: for B above p, some J : ℚ/ℤ → ℚ̄^× satisfies, if M ∣ p−1 and Mx = 0: σJ(x) =
J(cyc_M(σ)x); J(x) is a unit off p, of order `floorDiff` c x at B, of absolute value 1 in
all complex embeddings; J(x+b)/J(x) ≡ 1 above primes q ∣ p−1 if qb = 0; ∏_{b mod r}
J(x+b/r)/J(rx) is a root of unity for r ∣ M prime to c.

Known result: Stickelberger's factorisation of Gauss sums; Davenport–Hasse product relation. -/
lemma exists_jacobi_family : ∃ J : _ → _, ∀ {M} [NeZero M], p ≡ 1 [MOD M] → ∀ ⦃x⦄, M • x = 0 →
  (∀ r [NeZero r], r ∣ M → c.Coprime r → IsOfFinAddOrder (∑ b, J (x + ofZMod r b) - J (r • x))) ∧
  (∀ σ (a : ℕ), (cycCharMod Ω M σ).1 = a → galUnitsRep σ (J x) = J (a • x)) ∧ (∀ A : ClosurePlace,
  A.valuation p = 1 → A.valuation (J x).toMul.1 = 1) ∧ ordRat ℚ B (J x) = floorDiff c x ∧ (∀ τ :
  Ω →+* ℂ, ‖τ (J x).toMul.1‖ = 1) ∧ ∀ q [Fact q.Prime] A b, q • b = 0 → q ∣ p - 1 →
  A.valuation q < 1 → J (x + b) - J x ∈ principalUnits A := by
  let n := p.pred; have := of_pos hp.1.pred_pos
  have {m} [NeZero m] := (@HasEnoughRootsOfUnity.prim Ω _ m).choose_spec.toInteger_isPrimitiveRoot
  obtain ⟨hψ, ⟨χ, w⟩, cp, _, _, _, R⟩ := zmodChar_primitive_of_primitive_root p this, PSigma.mk _
    (zmodChar_primitive_of_primitive_root n (.iff_orderOf.2 (exists_mulChar_orderOf (ZMod p)
    (by aesop) this).choose_spec)), n.coprime_of_lt_prime out (p.pred_lt out) Fact.out,
    exists_rat_place_of_prime hp.1
  have := gaussSum_one_left (@hψ 1 out)
  have gn t := by_cases (by aesop) (Dvd.intro _ <| gaussSum_mul_gaussSum_eq_card (χ := χ t) · hψ)
  let G t := DiscreteUnits.ofNeZero _ (RingOfIntegers.ext.mt (ne_zero_of_dvd_ne_zero out (gn t)))
  have {A} h t : valuation A (G t).toMul.1 = 1 := (valuation_eq_one_iff ..).1
    (by_contra (h ∘ mem_centrePrime.1 ∘ (centrePrime ..).mem_of_dvd (gn t)))
  obtain ⟨⟨K, H⟩, S, hS, L⟩ := smul_gaussSum G (by tauto), stickelberger hB G (by tauto) hψ w cp
  have {x m} h d : x ∈ S.range := ((bijective_ofZMod_comp (by simp)).2 S).rec (fun _ e ↦ e ▸
    (·.of_comp (f := ofZMod _).bijective_of_finite.2.exists.1
    (exists_ofZMod (Submodule.torsionBy_le_torsionBy_of_dvd m _ d h)))) hS
  let j := c • G - G ∘ (c • ·)
  use (⇑S).extend (j - j ∘ (-·)) 0, fun hM ↦ forall₂_and.2 ((fun E ↦ ⟨?_, E⟩) fun _ h ↦ ?_)
  obtain ⟨t, ⟨⟩⟩ := this h hM.symm.dvd'
  simp_rw [← map_nsmul, hS.extend_apply]
  and_intros <;> intros; simp [j, H, (rootPowHom ..).2.1 ((map_cycCharMod_mul _ _ t).trans
    (by rw [cycCharMod_eq_iff_unitsRep.1 ‹_› (by simp_all), map_nsmul])), -nsmul_eq_mul]
  simp [*, j, valuationVia]; simp [floorDiff, map_nsmul, ← nsmul_eq_mul, ← L, j]
  obtain ⟨g, e⟩ := exists_smul_emb_eq Gal(Ω/ℚ) ‹_› (star ‹_›) (by bound)
  simp [e, -AlgEquiv.smul_def, (by simp [j, H, IsComplexConj.cycCharMod_eq_neg_one ⟨_, e⟩] :
    j (-t) = galUnitsRep g (j t))]
  obtain ⟨_, ⟨⟩⟩ := this ‹_› ‹_›
  have (t) s (_ : ‹ℕ› • s = 0) : G (t + s) - G t ∈ principalUnits ‹_› := show valuation _ _ < 1 by
    simp [*, valuationVia, (cp.symm.of_dvd_left ‹_›).valuation_eq_one]; exact mem_centrePrime (x :=
    (_ - _ : 𝓞 Ω)).1 (by simp [gaussSum, residue_eq_one_of_pow_prime_eq_one ‹_›, *,
      sum_eq_add_sum_units])
  simp_all [← map_add, ← eq_iff_sub_mem, add_comm, mul_add, mul_right_comm, j]
  rintro x _ r _ ⟨_, ⟨⟩⟩ k
  apply Units.isOfFinOrder_val.1 (isOfFinOrder_of_norm_eq_one (fun A ↦ (A.valuation_le_one
    p).eq_or_lt.rec ?_ ((fun h ↦ (h.ordRat_nonneg_iff _).1 ((h.exists_smul Gal(Ω/ℚ) (R B hB)).rec
    (by simp +contextual [← h.ordRat_smul ·, (E ..).1 _ _ zmod_eq_natCast_val, isUnit_cast_of_dvd,
    smul_comm (r * _), *, smul_comm r, sum_floorDiff k]))) ∘ R A)) ?_) <;> erw
    [toMul_sub] <;> simp +contextual [*, smul_comm]
end
