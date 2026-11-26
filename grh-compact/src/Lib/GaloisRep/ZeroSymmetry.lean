import Lib.Adelic.OstrowskiTaussky

section
/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Compact subgroups of l-adic units (1 mod 4) are procyclic. -/

open PadicInt Filter Subgroup ZMod Nat Units

/-- A continuous κ from a compact group to ℤ_ℓ^×, with values ≡ 1 mod 4 if ℓ = 2, has procyclic
image: for some γ, every open subgroup containing γ and ker κ is the whole group. -/
lemma exists_procyclic_generator {ℓ Γ} [Fact (Prime ℓ)] [Group Γ] [TopologicalSpace Γ] [CompactSpace
  Γ] [ContinuousMul Γ] (κ : Γ →* ℤ_[ℓ]ˣ) (hκ : Continuous κ) (h₂ : ∀ g, 4 ∣ (κ g).1 - 1) :
  ∃ γ, ∀ S ≥ κ.ker, S.IsOpen → γ ∈ S → ∀ g, g ∈ S := by
  obtain ⟨μ, C, c, E⟩ : ∃ μ, (∀ k, IsCyclic ((Units.map (toZModPow (k + 2)).1).comp μ).range) ∧
      Continuous μ ∧ μ.ker ≤ κ.ker := by
    obtain h | rfl := (em' _).imp (isCyclic_units_of_prime_pow ℓ Fact.out) id
    use κ, inferInstance
    use κ ^ 2, fun k ↦ isCyclic_of_le (H' := zpowers (unitOfCoprime 5 (by bound))) (by
      simpa [LE.le] using fun _ ↦ sq_mem_of_index_two (Nat.mul_left_cancel card_pos ((card_mul_index
        _).trans (by norm_num [↓card_zpowers, ← orderOf_units, orderOf_five, ↓totient_prime_pow,
        pow_succ]))) _), hκ.pow 2, fun g h ↦ val_eq_one.1 (by
      grind [@pow_p_dvd_int_iff 2 _ 2 (-2), sq_eq_one_iff.1 congr($h.1)])
  choose γ _ h using (Set.exists_subtype_range_iff.1 <| C · |>.exists_monoid_generator)
  exact (isCompact_univ (by simp : atTop.map γ ≤ _)).imp fun δ d S s o a g ↦ comap_map_eq_self
    (E.trans s) ▸ (c.isClosedMap _ (S.isClosed_of_isOpen o)).mem_of_frequently_of_tendsto (.mono
    (d.2.frequently (o.mem_nhds a)) fun k ↦ (⟨_, pow_mem · _, rfl⟩))
    (isOpenEmbedding_val.tendsto_nhds_iff.2 (tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm (fun k ↦
    (norm_le_pow_iff_mem_span_pow _ (k + 2)).2 (by simpa [← ker_toZModPow] using! congr($(h k ⟨_, g,
    rfl⟩).1.1))) (by simp [↓← norm_p_pow, -norm_p, tendsto_add_atTop_iff_nat]))))
end

section
/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Crude bound for the class number by degree and discriminant. -/

open NumberField Ideal Module Set Real Nat

/-- The class number of a number field F of degree n over ℚ is at most (2ⁿ |disc F|)^{n+1}. -/
lemma classNumber_le F [Field F] [NumberField F] :
    classNumber F ≤ (2 ^ finrank ℚ F * (discr F).natAbs) ^ (finrank ℚ F + 1) := by
  have {B} (n : Ioc 0 B) := (span {(n : 𝓞 F)}).absNorm_ne_zero_iff.1 (by aesop)
  grw [classNumber, ← card_eq_fintype_card, (card_le_card_of_surjective (fun x ↦ .mk0
    ⟨span {↑x.1, x.2.out}, by simp; grind⟩) fun C ↦ ?_).trans_eq (@card_sigma _ _ _ this),
    Finset.sum_le_sum fun n _ ↦ (absNorm_span_natCast n.1).trans_le (by grw [n.2.2])]
  simpa [RingOfIntegers.rank] using pow_succ'.ge
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  have := absNorm_pos_of_nonZeroDivisors I
  cases IsDedekindDomain.exists_sup_span_eq I.1.span_singleton_absNorm_le (by aesop)
  use ⟨⟨_, this, ?_⟩, ‹𝓞 F›⟩
  simp_all [← comap_map_quotientMk, span_insert]
  rify
  grw [hI, factorial_le_pow, ← two_le_pi, sqrt_le_self_iff.2 (mod_cast by grind)]; ring
  bound [InfinitePlace.card_add_two_mul_card_eq_rank F]
end

section
/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Sum over Z/N, N prime, splits as zero term plus sum over units. -/

lemma sum_eq_add_sum_units {N} [Fact N.Prime] {V} [AddCommMonoid V] (f : ZMod N → V) : ∑ c, f c =
  f 0 +
  ∑ c : _ˣ, f c.1 := by simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
end

section
/-! General lemmas of algebraic number theory (textbook or folklore).

This file: Symmetry of zeros of Dirichlet L-functions from the functional equation, imprimitive
characters included. -/

open Complex DirichletCharacter CharZero Nat.Prime
variable {N} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- For a Dirichlet character χ, a natural number M and Re s ≠ 0, the product of the Euler
factors 1 − χ(p)p^{−s} over the primes p dividing M is not zero. -/
lemma prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h0 : s.re ≠ 0) :
    ∏ p ∈ M.primeFactors, (1 - χ p * p ^ (-s)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p h e ↦ by
  obtain := congr(Real.logb p ‖$(χ.star_apply' p)‖), show χ p = p ^ s by grind [cpow_neg]
  simp_all [norm_natCast_cpow_of_pos, χ.inv_apply_eq_inv', pos, ne_one]

/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
lemma exists_isPrimitive_changeLevel_eq : ∃ M f ψ, NeZero M ∧ IsPrimitive ψ ∧
  changeLevel (f : M ∣ N) ψ = χ := ⟨_,
  _, _, ⟨χ.conductor_ne_zero⟩, χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩

/-- Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the
gamma factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0. -/
lemma LFunction_one_sub_eq_zero s (h0 : s.re ≠ 0) (h1 : s ≠ 1)
    (hs : LFunction χ s = 0) : χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by
  obtain ⟨M, f, ψ, _, h, rfl⟩ := exists_isPrimitive_changeLevel_eq χ
  have := ψ.changeLevel_eq_cast_of_dvd f (-1)
  simp_all [LFunction_changeLevel, ← map_inv, gammaFactor, prod_euler_factor_ne_zero, s.ext_iff,
    @LFunction_eq_completed_div_gammaFactor M, @eq_comm ℂ 1, DirichletCharacter.Even,
    IsPrimitive.completedLFunction_one_sub (ψ.conductor_inv.trans h)]; lia
end
