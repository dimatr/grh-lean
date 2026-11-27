import Lib.DiscreteSeries.Nabla
import Lib.DiscreteSeries.OscillatorDefs
import Lib.DiscreteSeries.HighestVectors

-- part: Lib.DiscreteSeries.Theta.FischerDecomposition
section
/-! Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics
(known result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Swap symmetry, vacuum weight, Laplacians and Fischer inner product for Howe's
argument. -/

noncomputable section


open MvPolynomial Finset InnerProductSpace Submodule Int Complex ComplexOrder Pi

section

variable {R C ι} [Fintype R] [Fintype C] {ε ε'} {T : @FockDualPair R C ε ε' ι}
  {l' a η i N G j ν b} {l : HCParam ε} {P Q : MvPolynomial ι ℂ}

/-- If l, l' match for the data (σ, ε, ε', γ, γ'), then l', l match for the swapped data (−σ, ε', ε,
γ', γ). -/
lemma IsMatch.swap : IsMatch T l l' → IsMatch T.swap l' l := by
  grind [IsMatch, pairSign, Units.val_neg, units_natAbs, Units.val_mul]

/-- A joint harmonic P for (σ, ε, ε', γ, γ', l, l') is, with rows and columns exchanged, a joint
harmonic for (−σ, ε', ε, γ', γ, l', l). -/
lemma IsJointHarmonic.swap (h : IsJointHarmonic T l l' P) : IsJointHarmonic T.swap l' l P :=
  ⟨h.1.swap, by grind [FockDualPair.IsJointHighest, T.swap_swap, h.2]⟩

namespace Fischer

attribute [scoped simp] raiseOp lowerOp GlModule.E units_ne_iff_eq_neg DFunLike.ite_apply
  HCParam.IsKHighest IsHarmonic
  mem_restrictSupport_iff Set.subset_def coeff_pderiv pairSign coeff_X_mul' ite_and fockLaplacian

/-- For ε_a = ε_b, the row operator E_ab sends P to Σ X_ac ∂_bc P over the columns c of sign +1,
minus Σ X_bc ∂_ac P over those of sign −1, plus δ_ab times the vacuum weight times P. -/
lemma oscRows_E_eq_polarisation_sub (q : ε a = ε b) : T.oscRows.E a b P =
  T.polarisation P a b 1 - T.polarisation P b a (-1) + ite (a =
  b) (T.vacuumWeight (ε a) : ℂ) 0 • P := by simp [q, oscRows]; split <;> simp +contextual [glOp,
  *, sum_ite, vacuumWeight, polarisation, ← C_mul'] <;> ring

scoped instance : NormedAddCommGroup (MvPolynomial ι ℂ) := Core.toNormedAddCommGroup (cd :=
  ⟨⟨⟨(fockPairing ℂ <| map (starRingEnd ℂ) ·)⟩, by simp [map_fockPairing, fockPairing_comm,
  map_leftInverse conj_conj _], by simp; grind [fockPairing_star_self_pos, zero_re, pos_iff], by
  simp, by simp [← C_mul']; simp [C_mul']⟩, by grind [fockPairing_star_self_pos, inner]⟩)

scoped instance : InnerProductSpace ℂ (MvPolynomial ι ℂ) := .ofCore _

@[scoped simp] lemma inner_X_mul : ⟪X b * P, Q⟫_ℂ = ⟪P, pderiv b Q⟫_ℂ ∧ ⟪P,
  X b * Q⟫_ℂ = ⟪pderiv b P,
  Q⟫_ℂ := by simp [inner, fockPairing_mul_X, mul_comm (X b), fockPairing_comm (map _ _), pderiv_map]

/-- For an integer j, the space of complex polynomials of total degree at most j in variables
indexed by ι. -/
def polyDegreeLE (j : ℤ) := @restrictSupport ι ℂ _ {d | d.degree ≤ j}

instance [Fintype ι] : Module.Finite ℂ (@polyDegreeLE ι j) := finiteDimensional_of_le
  (S₂ := restrictTotalDegree ..) (restrictSupport_mono _ fun _ ↦ toNat_le_toNat)

lemma glOp_mem_polyDegreeLE : P ∈ polyDegreeLE j → j + η a ≤ i + η b →
  glOp η a b P ∈ polyDegreeLE i := by intros; simp [glOp]; split_ifs <;>
  simp_all [polyDegreeLE] <;> grind [Finsupp.degree_single, Finsupp.sub_add_single_one_cancel]

/-- The polynomials of degree at most j that are orthogonal, for the Fischer inner product, to
all elements of G of degree at most j. -/
abbrev perpInDegree j G := (@polyDegreeLE ι j ⊓ G)ᗮ ⊓ polyDegreeLE j

lemma eq_zero_of_mem_perpInDegree (h : P ∈ perpInDegree j N) : P ∈ N → P = 0 := by simpa using
  (h.1 P ⟨h.2, ·⟩)

/-- Fischer decomposition: let G contain the polynomials of degree ≤ j−1 and the row-action images
of those of degree ≤ j−2. If P of degree ≤ j is orthogonal to G in degree ≤ j, then the Laplacian
`FockDualPair.fockLaplacian` a b of P vanishes whenever ε_a ≠ ε_b. -/
lemma fockLaplacian_eq_zero (ih : ∀ k < j, polyDegreeLE k ≤ G) (h : P ∈ perpInDegree j G) (o :
  ε a ≠ ε b) (s : Q = T.fockLaplacian a b P) (g : Q ∈ G → T.oscRows.E b a Q ∈ G) : Q = 0 := by
  simp [-pairSign] at s
  have q : Q ∈ polyDegreeLE (j - 2) := s ▸ sum_mem fun _ _ ↦
    glOp_mem_polyDegreeLE h.2 (by simp_all; lia)
  rw [← @inner_self_eq_zero ℂ, s, inner_sum, ← s, ← neg_zero, ← h.1 _ ⟨sum_mem _, by
    simpa [oscRows, o, eq_comm, smul_mem_iff, ne_of_apply_ne ε] using g (ih _ (by lia) q)⟩,
    sum_filter, sum_inner, ← sum_neg_distrib]; congr! 1; split; simp_all [glOp, -s]; rw [h.1]
  all_goals simp <;> grind [glOp_mem_polyDegreeLE, units_natAbs, Units.coe_neg_one, Units.ext_iff,
    IsConcreteLE.le_iff]

/-- Let P be K-highest of weight ν for the oscillator action on rows, Q_ab = Σ ∂_{ac}∂_{bc}P
over c with σε_aε'_c = +. If no nonzero Q_ab, ε_a ≠ ε_b, is K-highest of weight ν − e_a +
e_b, all these Q_ab vanish. -/
lemma fockLaplacian_eq_zero_of_isKHighest (W : l.IsKHighest T.oscRows ν P) (H : ∀ a b, ε a ≠ ε b →
  l.IsKHighest T.oscRows (ν + single a 1 - single b 1) (T.fockLaplacian a b P) →
  T.fockLaplacian a b P = 0) : T.IsRowHarmonic P :=
  have C x z a b (h : ε x = ε z) : T.oscRows.E x z (T.fockLaplacian a b P) = T.fockLaplacian a b
    (T.oscRows.E x z P) + ite (z = a) (T.fockLaplacian x b P) 0 - ite (b = x) (T.fockLaplacian a z
    P) 0 := by simp +contextual [oscRows, h, glOp, canonical_commutation, -raiseOp, -lowerOp,
    -zsmul_eq_mul, apply_ite (raiseOp ..), apply_ite (lowerOp ..), sum_comm (t := univ)]; abel
  Prod.forall'.1 (Finite.int_weight_induction (fun i ↦ l i.2 - l i.1) fun i m o ↦
    H _ _ o (by simp_all [add_smul, sub_smul, -fockLaplacian, -H]; grind))

lemma mapsTo_perpInDegree (h : ε a = ε b) (S : N ≤ G.comap (T.oscRows.E b a)) :
  Set.MapsTo (T.oscRows.E a b) (perpInDegree j G) (perpInDegree j N) :=
  fun y k ↦ by use fun z p ↦ .trans (by by_cases a = b <;> simp [oscRows_E_eq_polarisation_sub,
  polarisation, *, eq_comm, mul_comm]) (k.1 _ ⟨?_, S p.2⟩) <;> simp_all [oscRows,
  ← cast_smul_eq_zsmul ℂ] <;> grind [sum_mem, smul_mem, glOp_mem_polyDegreeLE, pairSign, add_mem]
end Fischer
end
end
end

-- part: Lib.DiscreteSeries.Theta.JointHarmonicUnique
section
/-! Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics
(known result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Weights of matched parameters; uniqueness up to scalar of the joint harmonic. -/

open Fintype (card)


variable {R C ι} [Fintype R] [Fintype C] [Fintype ι] {ε ε' l l'} {T : @FockDualPair R C ε ε' ι}
  (hm : IsMatch T l l')

@[local grind .] lemma int_unit_val_eq_one_or_neg_one (x : ℤˣ) : x.1 = 1 ∨ x.1 = -1 :=
  Int.isUnit_iff.1 x.isUnit

open MvPolynomial Finset InnerProductSpace ComplexOrder Fischer Int Units FockDualPair
attribute [local simp] sum_eq_zero_iff_of_nonneg IsRowHarmonic IsJointHighest coeff_sum glOp

omit [Fintype ι] in
/-- Let l be injective, P killed by compact raising row operators and column Laplacians, D_ab =
Σ_{X_bc of sign s} X_ac∂_bc. Then D_abP = 0 if ε_a = ε_b, s·l_b < s·l_a. If E_aaP = Λ_aP, k
= s·`FockDualPair.relWeight`(a) ≥ 0, then D_aaP = kP and ∂_acP = 0 for X_ac of sign −s. -/
lemma polarisation_eq_of_isCompactPrimitive {P} (hl : l.Injective) (h :
  T.oscRows.IsCompactPrimitive l P) (hP : T.swap.IsRowHarmonic P) a (s : ℤˣ) :
  (∀ b, ε a = ε b → s * l b < s * l a → T.polarisation P a b s = 0) ∧
  (T.oscRows.E a a P = (l.lowestKType a : ℂ) • P → let k := s * T.relWeight l a
  0 ≤ k → T.polarisation P a a s = (k : ℂ) • P ∧ ∀ c, T.varSign (a, c) = -s →
    pderiv (T.varEquiv (a, c)) P = 0) := by
  let u a p := -pderiv (T.varEquiv (a, Prod.fst p)) (pderiv (T.varEquiv (a, p.2)) P)
  let N a b := ∑ p ∈ .product {c | T.varSign (a, c) = 1} {c | T.varSign (a, c) = -1}, ⟪u a p,
    u b p⟫_ℂ
  have G s a b (q : ε a = ε b) : ⟪T.polarisation P b a (-s), T.polarisation P a b s⟫_ℂ = N a b := by
    fin_cases s <;> [skip; erw [sum_inner]] <;> simp +zetaDelta [-sum_add_distrib, polarisation,
      ↓sum_product, q, _root_.pderiv_comm] <;> congr! <;> grind [inner_zero_left, neg_units_ne_self]
  simp +contextual [oscRows_E_eq_polarisation_sub] at h
  replace hP a := (sum_eq_zero_iff_of_nonneg (s := {b | ε b = ε a}) (f := N a) (by
    unfold polarisation at *; grind [G 1, G (-1), neg_neg, sum_nonneg,
      CStarModule.inner_self_nonneg])).1 (sum_comm.trans (sum_eq_zero fun p k ↦ by
    rw [← inner_sum, inner_eq_zero_of_right]; specialize hP p.1 p.2
    cases int_unit_val_eq_one_or_neg_one T.σ <;> simp_all [u, ↓sum_filter,
      ← _root_.eq_inv_mul_iff_mul_eq]))
  simp +contextual [hP] at G; use by fin_cases s <;> simp <;> grind [inner_self_eq_zero]
  intro w k o; specialize G s a a; have p : T.polarisation P a a s = T.polarisation P a a (-s) +
    (k : ℂ) • P := by fin_cases s <;> simp [k, sub_smul, ← w, oscRows_E_eq_polarisation_sub]
  simp (disch := simp [polarisation] <;> positivity) [p, add_eq_zero_iff_of_nonneg] at G
  simp [*]
  simpa [polarisation] using congr(⟪$(G.1), P⟫_ℂ)

omit [Fintype ι] in
lemma FockDualPair.IsJointHighest.isPreJointHarmonic {Φ ν} : T.IsJointHighest l l' Φ l.lowestKType
  ν → T.IsPreJointHarmonic l l' Φ := by simp_all [IsPreJointHarmonic, sum_eq_zero]

omit [Fintype ι] in
@[local grind .] lemma HCParam.HasGap.two_mul_lowestKType_sub_vacuumWeight {h} r (g :
  l.HasGap h) : 2 * T.relWeight l r = l r + ∑ j,
  ε r * ε j * (l j - l r).sign - (2 * T.γ - (card C - ∑ c, (T.varSign (r, c) : ℤ))) := by
  push_cast [two_mul_lowestKType, ← add_sub, vacuumWeight, mul_sub, twoRho,
    Fintype.card_eq_sum_ones, card_filter, ← sum_sub_distrib, mul_sum]
  congr <;> simp [Units.ext_iff] <;> grind

include hm

lemma IsMatch.hasLargeGap {A} (h : A ≤ card ι := by simp) : l.HasLargeGap A := hm.1.mono (by
  grw [gapThreshold, h, ← Fintype.card_congr T.varEquiv]; norm_cast; simp; cases card C <;> lia)

section

omit [Fintype ι]

lemma IsMatch.sum_cols_le_sum_rows (F : R → ℤ) (G : C → ℤ) (e : (∀ r c, T.IsMatchedPair l l' r c →
  G c ≤ F r) ∧ (∀ r, |T.centredParam l r| < card R - card C → 0 ≤ F r) ∧
  ∀ c, |T.swap.centredParam l' c| < card C - card R → G c ≤ 0) : ∑ c, G c ≤ ∑ r, F r := by
  trans ∑ r, ∑ c, ite (T.IsMatchedPair l l' r c) (F r) 0; rw [sum_comm]
  all_goals gcongr; obtain ⟨⟨⟩⟩ := (by first | apply hm.3 ‹_› | apply hm.4 ‹_›) <;>
    (try rw [sum_eq_single ‹_›]) <;> grind [IsMatch, HasGap, sum_eq_zero]

/-- Let λ, λ' match, for groups of ranks n, n'. If ξ_r = −ξ'_c, where ξ_r = λ_r − γ + n'/2 and
ξ'_c = λ'_c − γ' + n/2, then Λ_r − v_r = −(Λ'_c − v'_c), with v, v' the weights of the vacuum 1. -/
lemma IsMatch.lowestKType_sub_vacuumWeight_eq_neg {r c} (e : T.IsMatchedPair l l' r c) :
  T.relWeight l r = -T.swap.relWeight l'
  c := by have k s := (by simpa [← mul_sum, -pairSign] using hm.sum_cols_le_sum_rows (fun j ↦
  s * (T.swap.varSign (c, j) - ε r * ε j * (l j - l r).sign)) (fun d ↦ s * (ε' c * ε' d * (l' d - l'
  c).sign - T.varSign (r, d))) (by refine ⟨?_, ?_, ?_⟩ <;> grind [pairSign, val_mul,
  Units.val_neg])); grind [k 1, k (-1), IsMatch, hm.2.two_mul_lowestKType_sub_vacuumWeight (T :=
    T.swap)]

lemma IsMatch.sign_mul_lowestKType_sub_nonneg r (s : ℤˣ) (e :
  card C - card R < ↑s * T.centredParam l r) : 0 ≤ s * T.relWeight l r := by
  have ⟨i, p, g⟩ := hm.1.mono (h' := card R) (mod_cast by cases card R <;> lia); norm_cast at g
  let v j := (s * T.centredParam l j + card R - card C) / 2
  let S := Icc 0 (v r)
  have : #{j | v j ∈ S} ≤ #S := by apply card_le_card_of_injOn v <;> intro <;> grind
  specialize p r; grind [IsMatch,
    card_Icc, by simpa [← mul_sum, sum_ite, -pairSign] using hm.sum_cols_le_sum_rows (fun j ↦
    s * (ε r * ε j * (l j - l r).sign) + ite (v j ∈ S) 2 0 - 1) (s * T.varSign ⟨r, ·⟩ - 1) (by
      simp_all [Units.ext_iff]; grind)]

end

omit [Fintype ι] in
/-- For matching parameters l, l' (`IsMatch`), any two polynomials P, Q satisfying
`FockDualPair.IsPreJointHarmonic` are proportional: P = cQ for some complex number c.

Known result: Theta correspondence of discrete series for real unitary dual pairs; joint
harmonics. -/
lemma IsMatch.unique {P Q} (hP : T.IsPreJointHarmonic l l' P) (hQ : T.IsPreJointHarmonic l l' Q) :
    ∃ c : ℂ, P = c • Q := by
  let f (x : ι → ℂ) := bind₁ (X + (.C <| x ·))
  let M := T.IsMatchedPair l l'; let x i : ℂ := ite (M.uncurry (T.varEquiv.symm i)) 1 0
  have hf P i : f x (pderiv i P) = pderiv i (f x P) := by
    induction P using induction_on <;> simp_all [f, apply_ite]
  have N F : T.IsPreJointHarmonic l l' F → (f x F).coeff 0 ≠ 0 := fun ⟨o, L', D, ⟨W, L⟩, D'⟩ h ↦ by
    have ⟨n, p, z⟩ := (f x F).support.exists_min_image (·.degree) (support_nonempty.2 fun k ↦ by
      simpa [f, bind₁_bind₁, o] using congr(f (-x) $k))
    have ⟨(r, c), k⟩ := (reindex_equiv T.varEquiv).2.1.1 (n.ne_iff.1 (by grind : n ≠ 0))
    obtain ⟨t, rfl⟩ := le_iff_exists_add'.1 (n.single_le_iff.2 k.pos)
    have K {κ S G} {a b : κ → ι} j (E : ∑ k ∈ S, X (a k) * pderiv (b k) F = G)
        (k' : (f x G).coeff t = 0 := by simp <;> grind [Finsupp.degree_single])
        (h : j ∈ S ∧ ∀ d, x (a d) ≠ 0 ↔ d = j) : b j ≠ T.varEquiv (r, c) := by
      simp [-sum_add_distrib, f, ← E, add_mul] at *; rw [sum_eq_single j] at k' <;> grind
        [coeff_pderiv, Finsupp.degree_single, t.sub_add_single_one_cancel, Nat.cast_add_one_ne_zero]
    let s := T.varSign (r, c); have V s := (polarisation_eq_of_isCompactPrimitive hm.1.1 L D' r s).2
      (W r) ∘ hm.sign_mul_lowestKType_sub_nonneg r s
    have : _ ∧ _ ∧ _ ∧ _ := ⟨fun d ↦
      (K r <| (polarisation_eq_of_isCompactPrimitive hm.2.1 L' (by rwa [swap_swap]) d
      (-s)).1 c · ·), fun a ↦ (K c <| (polarisation_eq_of_isCompactPrimitive hm.1.1 L D' a s).1
      r · ·), (K c <| V s · |>.1), fun g ↦ congr((f x $((V (-s) g).2 c (by simp [s]))).coeff t)⟩
    simp [hf, mem_support_iff.1 p, x] at this; clear * - this hm
    cases hm.3 r <;> grind [pairSign, hm.4 c, val_mul, Units.ext, hm.1.1, hm.2.1]
  use (f x P).coeff 0 / (f x Q).coeff 0, by_contra (N _ ⟨sub_ne_zero.2 ·, by
    simp_all [IsPreJointHarmonic, smul_sub, smul_comm (_ / _), -fockLaplacian]⟩ (by simp [*]))
end
