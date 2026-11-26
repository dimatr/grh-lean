import Lib.Adelic.RootLemma
import Lib.Adelic.HaarUnique
import Lib.Adelic.CuspidalAtScalars

section
/-! Part of: An approximate projector from averages over generic matrices (see
New.TwistedHecke.ElementaryDivisors).

This file: Frobenius-power products of generic matrices: monomial weights track the excess up to
error. -/

noncomputable section

namespace TwistingData

open MvPolynomial Matrix Finsupp SetLike IsRealFiltration Ideal.Quotient Fintype Function List Nat
variable {N k W O R} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [CommRing R]
  (T : TwistingData N W O) (h : GL (Fin k) W) (s : ZMod N) (r ℓ n d : ℕ) (a a' : Fin k)
  (ψ : ZMod N → ℕ → Matrix (Fin k) (Fin k) R)

/-- The k × k matrix of polynomials over O whose (b,c) entry is the P^d-th power of the variable
labelled (s − d, b, c). -/
abbrev frobGenericMatrix := of fun b c : Fin k ↦ @X O _ _ (s - d, b, c) ^ T.P ^ d

/-- The Kronecker product over s of the n-th symmetric powers of the matrix whose row b is that
of ψ(s,m−1)⋯ψ(s,0) (s even) or its transposed adjugate (s odd), m = ℓ + `TwistingData.deepIndicator`
r (b,s). -/
def frobOperator := kroneckerPi fun s ↦ symPowMatrix n (of fun b c ↦ ite (T.isEven s) id
  (·.adjugateᵀ) ((range (ℓ + T.deepIndicator r (b, s))).map (ψ s)).reverse.prod b c)

/-- For h in GL_k(W) and a letter s, the monoid endomorphism A ↦ ι_s(h)·A·ι_s(h⁻¹) of the k × k
matrices over O, that is, conjugation by ι_s(h). -/
def letterConj := MonoidHom.mk ⟨(h.1.map (T.ι s) * · * h⁻¹.1.map (T.ι s)), by simp⟩
  (by simp [mul_assoc, ← (h.1⁻¹.map _).mul_assoc])

/-- For ℓ and indices a,a', the real function of index b equal to (indicator of b=a' minus
indicator of b=a) divided by P^ℓ. -/
def indexWeight b := (ite (b = a') 1 0 - ite (b = a) 1 0) / (T.P ^ ℓ : ℝ)

variable {r ℓ n d s a a' h ψ β γ ν}
attribute [local simp] weight_eq_sum sum_prod_type_right indexWeight letterConj mul_sub map
  Matrix.mul_apply letterMatrix deepIndicator

/-- For a ring map χ: R → O, matrices ψ(s,d) over R and block diagonal h in GL_k(W) (blocks b <
r, b ≥ r): χ applied to `TwistingData.frobOperator` of ψ equals ρ(h⁻¹)·Q·ρ(h), where Q is
`TwistingData.frobOperator` of the matrices ι_s(h)·χ(ψ(s,d))·ι_s(h⁻¹). -/
lemma frobOperator_map (χ : R →+* O) (hh : h ∈ levi W (twoBlock k r)) :
  (T.frobOperator r ℓ n ψ).map χ = T.letterRep n h⁻¹ * T.frobOperator r ℓ n (fun s d ↦
  T.letterConj h s ((ψ s d).map χ)) * T.letterRep n h := by
  simp_rw [letterRep_apply, frobOperator, ← kroneckerPi_mul, ← map_mul, ← kroneckerPi_map,
    ← symPowMatrix_map]
  congr!
  have e {M s} : .map (ite (T.isEven s) id (·.adjugateᵀ) M) χ = T.letterMatrix s h⁻¹ * ite (T.isEven
    s) id (·.adjugateᵀ) (T.letterConj h s (χ.mapMatrix M)) * T.letterMatrix s h := by
    split <;> simp [*, ← transpose_mul, adjugate_mul_distrib, mul_assoc, adjugate_mul, mul_adjugate,
      smul_smul, transpose_map, ← det_mul, ← (h.1⁻¹.map _).mul_assoc]; exact χ.map_adjugate _
  ext; erw [congrFun₂ e]
  simp [-coe_units_inv, map_list_prod, comp_def]; congr! 3
  grind [transpose_apply, twoBlock, hh _, inv_mem hh _]

/-- Let G be a decreasing multiplicative filtration, |α_{s,0}(b)| ≤ u, ∑_b α_{s,d}(b) = 0, and
ψ(s,d)_{bc} ∈ G(α_{s,d+1}(b) − α_{s,d}(c) − u) for d ≤ ℓ. Then row β of `TwistingData.frobOperator`
lies in G(x·β − Nnk(ℓ+2)u), where x(b,s) = ±α_{s,ℓ+ε}(b), + for even s, ε =
`TwistingData.deepIndicator` r (b,s). -/
lemma frobOperator_mem G [IsRealFiltration G] (α : _ → _ → Fin k → ℝ) x u (e :
  (∀ s b, |α s 0 b| ≤ u) ∧ ∀ s d, ∑ b, α s d b = 0) (hx : ∀ b s, x (b, s) =
  ite (T.isEven s) 1 (-1) * α s (ℓ + T.deepIndicator r (b, s)) b) (H : ∀ s, ∀ d ≤
  ℓ, ∀ b c, ψ s d b c ∈ G (α s (d + 1) b - α s d c - u)) (o : 0 ≤ u := by positivity) :
  T.frobOperator r ℓ n ψ β γ ∈ G (weight x (exponentOf β) - N * (n * (k * ((ℓ + 2) * u)))) :=
  antitone (by simp [← Finset.sum_mul, ← cast_sum, Monomials.degree_eq, ← degree_eq_sum,
  exponentOf]) (prod_mem_graded _ _ _ fun s _ ↦ (show _ ∈ gaussFiltration G (k * ((ℓ + 2) * u) - x
  ⟨·, s⟩) 0 by simpa [linSubst, bind₁_monomial, X, smul_monomial] using
  prod_pow_mem_graded _ 0 _ _ fun c _ ↦ sum_mem fun b _ ↦ monomial_mem_gaussFiltration (by
  simp [↓weight_single, *]
  generalize l : ℓ + _ = m
  replace l : m ≤ ℓ + 1 := by lia
  have h {b c} : ((range m).map (ψ s)).reverse.prod b c ∈ G (α s m b - (m + 1) * u) := by
    induction' m with m I generalizing b <;> simp [range_succ]
    grind [zero_mem, antitone _ (one_mem_graded G)]
    exact sum_mem fun x ↦ by grind [mul_mem_graded (H s m _ b x) (@I _ x)]
  split <;> simp [adjugate, cramer_apply, det_apply]
  exact antitone (by grw [← b.pos.nat_succ_le, l]; grind) h
  exact sum_mem fun π _ ↦ zsmul_mem
    (antitone (by simp [Finset.sum_update_of_mem]; grw [l, card_finset_fin_le]; grind)
    (prod_mem_graded G (update (α s m · - (m + 1) * u) b 0) _
    (by grind [zero_mem, updateCol_apply, transpose_apply, one_mem_graded G]))) _)) _)

lemma X_mem_gaussFiltration {σ w ω v} : @X O σ _ v ∈ gaussFiltration (adicFiltration w) ω (ω v) :=
  monomial_mem_gaussFiltration (by simp [weight_single])

omit [NeZero N] in
lemma p_dvd_cj_frobenius_sub {Y b c} : ↑T.p ∣ T.letterConj h s ((T.letterConj h⁻¹ (s - d) Y).map
  (· ^ T.P ^ d)) b c - Y b c ^ T.P ^ d := let π := Ideal.Quotient.mk (.span {(_ : O)})
  let f := RingHom.mk' (π.1.comp (powMonoidHom _)) (by
    simp [← pow_mul, add_pow_prime_pow_eq T.prime, π, -map_natCast])
  (eq_zero_iff_dvd ..).1 (sub_eq_zero.2 (congrFun₂ ((by simp [← RingHom.coe_comp, ← mul_assoc,
    mul_assoc (Y.map _), show π ∘ (· ^ _) = f by rfl, show π.comp _ = f.comp
    _ by ext; simpa [← eq_zero_iff_dvd] using! T.frobenius_pow_congr d (s - d) _]) : .map _ π =
    Y.map f) ..))

/-- Let a' = a+1, Nnk(ℓ+2) ≤ P^ℓ, ℓ ≤ N, and, for j = s − d and e = P^d, ψ(s,d) =
ι_s(h)(ι_j(h)⁻¹g_jι_j(h))^{(e)}ι_s(h)⁻¹ (entrywise powers). In row β of `TwistingData.frobOperator`,
w^c divides the coefficient of ν if ν_j has equal row and column `TwistingData.indexWeight`-weights
for j ≠ i and |excess of β at i+ℓ − row weight of ν_i| > 2c+1. -/
lemma pow_dvd_coeff_conj_frobOperator (ha : a + 1 = a'.1) i (hn : N * n * k * (ℓ + 2) ≤
  T.P ^ ℓ) (hl : ℓ ≤ N) h {ψ} (hψ : ψ = fun s (d : ℕ) ↦ (map C T).letterConj h s
  (((map C T).letterConj h⁻¹ (s - d) (of fun b c ↦ X (s - d, b, c))).map (· ^ T.P ^ d))) {c : ℕ}
  (e : ∀ j ≠ i, weight (T.indexWeight ℓ a a' ·.1) (ν.curry j) = weight (T.indexWeight ℓ a a' ·.2)
  (ν.curry j)) (g : 2 * c + 1 < |weight (T.excessWeight (i + ℓ) a a') (exponentOf β) - weight
  (T.indexWeight ℓ a a' ·.1) (ν.curry i)|) : T.w ^ c ∣ (T.frobOperator a' ℓ n ψ β γ).coeff ν := by
  obtain ⟨rfl, _, _, ε, hε, g⟩ := hψ, T.prime.ne_zero, T.one_lt_P.le,
    (RCLike.exists_norm_eq_mul_self _).imp fun _ ↦ And.imp_right g.trans_eq
  let A m b := T.indexWeight ℓ a a' b * (ε / 2 * T.P ^ m / T.q)
  let ω | (j, b, c) => ite (j = i) (A N b) (A (j - i).val b - A (j - i).val c)
  have hA {m} (e : m ≤ N) b : ‖A m b‖ ≤ 2⁻¹ / T.P ^ ℓ := by
    simp [A, *, field]; split_ifs <;> simp <;> gcongr <;> lia
  refine .trans (pow_dvd_pow _ (lt_ceil.2 ?_).le) (T.frobOperator_mem (gaussFiltration
    (adicFiltration _) ω) (fun s d ↦ A (d + (s - d - i).val)) (T.excessWeight (i + ℓ) a a' · *
    (ε / 2)) _ ⟨fun _ ↦ hA (by grind), by simp [A, sub_mul, div_eq_mul_inv]⟩ (fun _ _ ↦ by
    dsimp; split_ifs <;> simp [excessWeight, rootVar, field, -one_add_val_sub_one_sub] <;> ring_nf
      <;> grind only) (fun s d hd b c ↦ have hω {v} := abs_le.1 (show |ω v| ≤ 1 / T.P ^ d by
    grw [hd]; clear_value A; grind [Real.norm_eq_abs]); have := abs_le.1 (hA (hd.trans hl) c)
      antitone (by simp [ω, ← sub_sub, add_assoc]; split <;> simp_all [A, pow_add, ← mul_div] <;>
        linarith) fun μ ↦ if q :
        _ then .trans (.pow (dvd_zero _) q) ((show _ ∈ gaussFiltration (adicFiltration _) ω _ by
    simp [← monomial_zero']
    solve_by_elim (transparency := .instances) (maxDepth := 50) [mul_mem_graded, pow_mem_graded,
      antitone hω.1 X_mem_gaussFiltration, monomial_mem_gaussFiltration,
      mem_adicFiltration_of_nonpos, (sub_self _).le, sum_mem]) μ) else
    (dvd_sub_left (pow_mem_graded _ X_mem_gaussFiltration μ)).1 (.trans (pow_dvd_pow _ (by
    clear_value ω; simp [field] at *; grind)) (T.w_sq ▸ (C_dvd_iff_dvd_coeff ..).1
    (T.map C).p_dvd_cj_frobenius_sub μ))) ..)
  grw [show (N : ℝ) * _ ≤ 2⁻¹ by field; norm_cast]
  simp_all [↓sum_prod_type, ω, A, ← mul_assoc, ← Finset.sum_mul]; bound

lemma degree_le_of_coeff_frobOperator (e : (T.frobOperator (k := k) r ℓ n
  T.frobGenericMatrix β γ).coeff ν ≠ 0) j : degree (ν.curry j) ≤ N *
    (n * (k * ((ℓ + 2) * T.P ^ ℓ))) := by
  rify; simpa [degree_eq_sum] using (mt zero_pow (ne_zero_of_dvd_ne_zero e (T.frobOperator_mem
    (gaussFiltration _ (if ·.1 = j then -1 else 0)) 0 0 _ (by simp) (by simp) (fun s d h _ _ ↦
    antitone (by grw [← h] <;> bound [T.prime.pos]) (pow_mem_graded _ X_mem_gaussFiltration)) ..)))
end TwistingData
end
end

section
/-! Part of: Dimension bounds mod p from flags and a cone volume (see New.TwistedHecke.Counting).

This file: Cyclic interlacing cone volume as a signed sum over permutations, via determinant of
indicators. The cyclic interlacing cone fills the share of one flag in volume. -/

open Fin Finset Set ENNReal Equiv Fintype LinearMap Matrix MeasureTheory Tuple

variable {k m : ℕ} {T : Type} [Add T] [One T] (v : T → Bool) (P : ℝ) (k' : ℕ)

/-- For permutations σ_j, the linear map ν ↦ β with β(b,j) = ±(P·ν(b,j+1) − ν(σ_j b, j)), the
sign being + if v j is true and − otherwise. -/
@[simps!] def permStep (σ : T → Perm (Fin k)) : Module.End ℝ (Fin k × T → ℝ) := .pi fun x ↦
  ite (v x.2) (1 : ℝ) (-1) • (P • .proj (x.1, x.2 + 1) - .proj (σ x.2 x.1, x.2))

/-- The set Σ of real vectors β ≥ 0 with ∑_b β(b,j) in [D_j − 1, D_j] for every j. -/
def slab (D : T → ℝ) := {β : Fin k' × T → ℝ | 0 ≤ β ∧ ∀ j, ∑ b, β (b, j) ∈ Icc (D j - 1) (D j)}

/-- The cone of ν such that, for all j and b: P·ν(b+1,j+1) ≤ ν(b,j) if v j is true, and ν(b+1,j)
≤ P·ν(b,j+1) otherwise. -/
def pieriCone := {ν | ∀ j (b b' : Fin k), b.1 + 1 = b' → permStep v P 1 ν (ite (v j) b' b, j) ≤
  ν (b, j) - ν (b', j)}

/-- For weakly decreasing x, y in ℝ^k, the matrix with (b,c) entry 1 if y_c < x_b and 0
otherwise has determinant 1 if x₁ > y₁ ≥ x₂ > y₂ ≥ ⋯ ≥ x_k > y_k, and 0 otherwise. -/
lemma det_interlacing_indicator {x y : Fin k → ℝ} (hx : Antitone x) (hy : Antitone y) :
  det (of fun b c ↦ ite
  (y c < x b) (1 : ℝ) 0) = ite ((∀ b, y b < x b) ∧ ∀ b c, b.1 + 1 = c.1 → x c ≤ y b) 1 0 := by
  induction' k with k ih
  · simp
  obtain ⟨b, h⟩ | h := exists_or_forall_not fun b ↦ y 0 < x (succ b)
  · rw [det_zero_of_row_eq b.succ_ne_zero] <;> [grind [hy b.castSucc.zero_le]; ext c]
    grind [of_apply, hy c.zero_le, hx b.succ.zero_le]
  simp [det_succ_column_zero', sum_univ_succ, forall_fin_succ, h]
  erw [ih] <;> grind [Antitone]

omit [Add T] [One T] in
/-- For a finite set of letters, `slab` k D is bounded. -/
lemma isBounded_inter_slab [Fintype T] (D : T → ℝ) Y :
    Bornology.IsBounded (Y ∩ slab k D) := (Metric.isBounded_Icc ..).subset fun _ ⟨_, h, g⟩ ↦
    ⟨h, fun x ↦ (single_le_sum (fun b _ ↦ h (b, _)) (by simp)).trans (g _).2⟩

/-- Let P > 1, q = P^{m+1}, and `permStep` v P 1 ν ∈ Ω exactly when ν ∈ `pieriCone` v P. Then
vol(Ω ∩ Σ) = (q − 1)^k/k! · ∑_{τ∈S_k} sgn(τ)/|det(q − A_τ)| · vol(Σ), with Σ = `slab` k
D and A_τ the permutation matrix. -/
lemma volume_inter_slab_eq_signed_sum {v : Fin (m + 1) → _} (hP : 1 < P) D {Ω : Set _} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : let Δ τ := |(1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ τ).det|
  volume.real (Ω ∩ slab k D) =
          Δ id / k.factorial * (∑ τ : Perm (Fin k), τ.sign / Δ τ) * volume.real (slab k D) := by
  let S σ (τ : _ → Perm (Fin k)) (Y : Set _) := {ν | let β := permStep v P σ (ν ∘ prodCongrLeft τ)
    (∀ j, ∑ b, permStep v P 1 ν (b, j) ∈ Icc (D j - 1) (D j)) ∧ (∀ j b, 0 < β (b, j)) ∧ β ∈ Y}
  -- the map of `σ` is injective, as `P > 1`
  have z σ : (@permStep k _ _ _ v P σ).det ≠ 0 := (bot_lt_ker_of_det_eq_zero · |>.not_ge fun ν h ↦
    norm_le_zero_iff.1 (by nlinarith [(funext fun x ↦ by simpa [ite_eq_iff'] using (mul_eq_zero.1
    congr($h (_, _ - 1))) : P • ν = ν ∘ _) ▸ pi_norm_comp_le .., norm_smul P ν, P.le_norm_self]))
  -- change of variables; the walls `β x = 0` are null sets
  have V σ τ Y : volume (S σ τ Y) = .ofReal |(permStep v P σ * (Perm.permMatrix ℝ
    (prodCongrLeft τ)).toLin').det⁻¹| * volume (Y ∩ slab k D) := by
    erw [← measure_inter_conull (ae_all_iff.2 (Measure.ae_eval_ne _ · 0)) (s := Y ∩ _), ←
      Measure.addHaar_preimage_linearMap _ (by simp [z])]
    congr with ν
    simp [S, slab, -Perm.coe_one, ← mul_sum, ← Perm.mul_apply, Pi.le_def, -Perm.coe_mul,
      fun e j ↦ Equiv.sum_comp e (ν ⟨·, j⟩), permMatrix_mulVec, ↓permStep_apply]
    grind
  let B : (_ → ℝ) →ₗ[ℝ] Fin k × Fin m.succ → ℝ := LinearMap.pi fun x ↦ P⁻¹ ^ x.2.1.succ • proj x.1
  have ⟨c, hc⟩ : ∃ c, ∀ σ, (@permStep k _ _ _ v P σ).det = c * (1 - (P ^ (m + 1))⁻¹ • funLeft ℝ ℝ
      (List.ofFn σ).prod).det := ⟨_, fun σ ↦ by
    let G := (Perm.permMatrix ℝ (prodCongrLeft (partialProd σ ∘ castSucc))).toLin'
    let A := funLeft ℝ ℝ ((last _).partialProd σ ·, last m)
    rw [show _ • _ = A ∘ₗ B by ext; simp +zetaDelta [partialProd, List.take_of_length_le]]
    simpa [← det_toMatrix' (_ - _), toMatrix'_comp, det_one_sub_mul_comm B.toMatrix', field, G]
      using congr(($(show permStep v P σ * G = (permStep v 1 1 - permStep v 0 1) * G * (P • 1 -
      .pi fun x ↦ x.2.cases 0 (proj ⟨x.1, ·.castSucc⟩)) * (1 - B ∘ₗ A) by
      ext x ⟨b, j⟩
      cases j using lastCases <;>
      simp +zetaDelta [← succ_last, partialProd_succ, permMatrix_mulVec] <;> grind)).det)⟩
  have e ν : ∑ τ, (S 1 τ Ω).indicator (fun _ ↦ 1) ν =
      ∑ σ, (S σ 1 univ).indicator (fun _ ↦ ((List.ofFn σ).prod.sign : ℝ)) ν := ?_
  · simpa [↓integral_finsetSum, integrable_indicator_iff, fun σ ↦
      (by simp [S, hΩ, pieriCone, -permStep_apply]; use ?_ <;> fun_prop :
      MeasurableSet (S σ 1 univ) ∧ MeasurableSet (S 1 σ Ω)), ↓(V ..).trans_lt (mul_lt_top coe_lt_top
      (isBounded_inter_slab ..).measure_lt_top), -enorm_mul, Measure.real, hc, field, card_perm,
      ↓← ((prodCongrLeft fun g : Fin m → _ ↦ .mulRight (List.ofFn g).prod⁻¹).trans
        (consEquiv fun _ ↦ Perm
      (Fin k))).sum_comp, sum_prod_type_right, ← sum_mul, div_eq_inv_mul, abs_unit_intCast, V, by
      simpa [hc] using z 1, mul_right_comm _ _ (Int.cast _), Nat.cast_comm] using congr(∫ ν, $(e ν))
  -- the product of the determinants, expanded, and read after sorting
  let τ j := sort (-ν ⟨·, j⟩)
  have anti j := (monotone_sort (-ν ⟨·, j⟩)).neg
  simp_rw [indicator, S, hΩ, pieriCone, mem_ofPred, ite_and (∀ j, _ ∈ _), sum_ite_irrel,
    ← forall_and]
  rw [sum_eq_single τ fun σ ne ↦ ite_eq_right fun h ↦ ne (funext fun j ↦ eq_sort_iff'.2
    ((strictMono_iff_forall_covBy _).2 fun _ _ e ↦ .left _ _ (by
    simpa using (h ..).1.trans_le ((h ..).2 _ e.coe_fin.succ_eq)))), eq_comm]
  congr
  trans ∏ j, ((of fun b' b : Fin k ↦ ite (0 < permStep v P (fun _ ↦ .swap b b') ν (b, j)) 1
    0).reindex (τ j).symm (τ (j + 1)).symm).det
  · simp [↓det_reindex, ← Int.cast_prod, ← Units.coe_prod, det_apply', map_list_prod,
      prod_ofFn, -List.ofFn_succ, (AddGroup.addRight_bijective 1).prod_comp (Perm.sign <| τ ·),
      prod_univ_sum, Fintype.prod_ite_zero, -Units.val_mul]
  convert Fintype.prod_boole with j
  have a := (anti (j + 1)).const_mul (by bound : 0 ≤ P)
  by_cases v j <;> [convert (det_transpose _).trans (det_interlacing_indicator a (anti j)); convert
    det_interlacing_indicator (anti j) a using 2] <;> simp [← ext_iff, τ, *, forall_and, sub_add]
  infer_instance

/-- Let P > 1, q = P^N, and let Ω be a set such that `permStep` v P 1 ν lies in Ω exactly when ν
lies in `pieriCone` v P. Then ∏_{l=1}^{k} (q^l − 1)/(q − 1) · vol(Ω ∩ Σ) = vol(Σ), for Σ =
`slab` k D. -/
lemma prod_mul_volume_inter_slab {N} [NeZero N] {v P} (hP : 1 < P) (D : ZMod N → ℝ) {Ω} (hΩ : ∀ ν,
  permStep v P 1 ν ∈ Ω ↔ ν ∈ pieriCone v P) : (∏ l : Fin k, ((P ^ N) ^ (l.1 + 1) - 1) /
  (P ^ N - 1)) * volume.real (Ω ∩ slab k D) = volume.real (slab k D) := by
  have q := one_lt_pow₀ hP (NeZero.ne N)
  cases N; bound
  erw [volume_inter_slab_eq_signed_sum P hP D hΩ]
  set P := P ^ _
  -- the case of a single index (m = 0) with v = ⊤ and q = P^N (renamed P by the `set`): the cone is
  -- an orthant in the coordinates `β_l - q β_(l+1)`, and rescaling them maps its part of `Σ` onto
  -- `Σ`
  let d i := (P ^ (i + 1) - 1) / (P - 1)
  let p c : (Fin k × Fin 1 → ℝ) →ₗ[ℝ] ℝ := if h : c < k then .proj (⟨c, h⟩, 0) else 0
  let F : Module.End ℝ _ := LinearMap.pi fun x ↦ d x.1 • (p x.1 - P • p (x.1 + 1))
  have det : F.det = ∏ b : Fin k, d b := by
    rw [← det_toMatrix', ← det_reindex_self (prodUnique ..), det_of_isUpperTriangular]
      <;> simp [Fin.ext_iff, F, p, DFunLike.dite_apply, BlockTriangular]; lia
  have deg β : ∑ b, F β (b, 0) = ∑ b, β (b, 0) := sub_eq_zero.1 (by convert (sum_range_sub' (fun c ↦
    (d c - 1) * p c β) k) <;> simp [sum_range, F, p, ↓← sum_sub_distrib, -smul_dite] <;> grind)
  have D0 : 0 < F.det := by simp [prod_pos, d, one_lt_pow₀, *]
  have := @volume_inter_slab_eq_signed_sum k 0 P ⊤ q 1 (pieriCone ⊤ P) (by simp [pieriCone, field])
  erw [@Set.ext _ (_ ∩ _) (F ⁻¹' slab k 1), Measure.real, volume.addHaar_preimage_linearMap D0.ne',
    toReal_mul, mul_left_inj' (toReal_pos (mt (measure_mono_null (s := .Icc 0 (↑k)⁻¹) fun β ⟨h, g⟩ ↦
    ⟨h, by simp; grw [← h _, g _]; simp [mul_inv_le_one]⟩) (by simp [Real.volume_Icc_pi]))
    (Set.univ_inter _ ▸ isBounded_inter_slab ..).measure_lt_top.ne).ne', pow_one] at this
  simp [↓← this, ← det, abs_of_nonneg, D0.le, field, d]; rfl
  simp [slab, deg, ← and_assoc, pieriCone, Pi.le_def]
  simpa [F, p, DFunLike.dite_apply, d, one_lt_pow₀, *] using fun β _ _ ↦ ⟨by bound, fun h ↦
    ⟨by grind, WellFoundedGT.fix fun b I ↦ (h b).trans' (by grind [mul_nonneg])⟩⟩
end

section
/-! Dimension bounds mod p from flags and a cone volume. For the elementary divisor bound, counting
flags against the volume of a cyclic interlacing cone shows that, mod p, forms whose exponents
nearly obey the Frobenius inequalities in all Levi frames fill at most about one part in the Hecke
operator's degree, and that forms its scaling makes divisible in all frames are rare. Volumes of
interlacing regions, Frobenius amplification and counting by leading terms along flags are known.
Related work: Forrester–Zhang, Corank-1 projections and the randomised Horn problem, 2021 (after
Dixon, 1905; Anderson, 1991); Bombieri, Counting points on curves over finite fields, Sém. Bourbaki
430, 1973; Okounkov, Brunn–Minkowski inequality for multiplicities, 1996.

This file: Flag count; amplification bounds dimension of conditioned forms by flags times lattice
points. Parahoric index times dim `TwistingData.excessCond` is at most (1+κ)m^N; size conditions.
Forms deep in all frames are rare: their mean depth is small. -/

open Module Nat Subgroup Filter Finset Finsupp Fintype Matrix MeasureTheory MvPolynomial Real
  MeasureTheory.Measure

variable {N k W K} [NeZero N] [CommRing W] [IsLocalRing W] [Field K] (T :
  TwistingData N W K) {a a' : Fin k}

instance [Finite (IsLocalRing.ResidueField W)] (τ) :
    (@parahoric k W _ _ τ).FiniteIndex := finiteIndex_of_le (ker_le_comap ..)

/-- For a finite field K with q elements, the index of the lower triangular subgroup in GL_k(K),
the number of full flags, is at most ∏_{l=1}^{k} (q^l − 1)/(q − 1). -/
lemma index_borel_le [Finite K] : (parabolic (R := K) (OrderDual.toDual ∘ @Fin.val k)).index ≤ ∏ l :
    Fin k, ((Nat.card K : ℝ) ^ (l.1 + 1) - 1) / (Nat.card K - 1) := by
  set A := @parabolic ..
  simpa [card_GL_eq_prod, Nat.card_pi, Nat.card_units, prod_range, Finite.one_lt_card,
    prod_pow_eq_pow_sum,
    field] using mono_cast (α := ℝ) (A.index_mul_card.le.trans' (mul_le_mul_left _
    (card_le_card_of_injective (fun x : ∀ i, Kˣ × (Set.Iio i → K) ↦ ⟨.mkOfDetNeZero (of fun i j ↦
    ite _ 0 (dite _ ((x i).2 ⟨j, ·⟩) fun _ ↦ (x i).1)) (by simp +contextual [BlockTriangular,
    det_of_isLowerTriangular, univ.prod_eq_zero_iff]), fun _ _ ↦ (ite_eq_left ·)⟩) fun x y h ↦ by
    ext i j <;> [simpa using congr($h.1 i i); simpa [lt_asymm, j.2.out] using congr($h.1 i j)])))

variable (a) in
/-- The real vectors β whose excess `TwistingData.excessWeight` i b (b+1) is, for all letters i, at
most h if b + 1 = a and at most 0 otherwise. -/
def TwistingData.excessCone (h : ℝ) :=
  {β | ∀ i (b b' : Fin k), b.1 + 1 = b' → T.excessWeight i b b' ⬝ᵥ β ≤ ite (b' = a) h 0}

/-- For K of characteristic p, a' = a + 1: dim `TwistingData.excessCond` n a a' 0 h ≤ [L : ℐ ∩
L]·vol(`TwistingData.excessCone` a' (h + N(k+1)) ∩ Σ), L the block diagonal group (blocks a', k −
a'), ℐ the lower Iwahori subgroup, Σ = `slab` of degrees in [n+k, n+k+1]. -/
lemma TwistingData.finrank_excessCond_le_volume [CharP K T.p] (ha : a.1 + 1 = a') n h :
    finrank K (T.excessCond n a a' ⊥ h) ≤ (parahoric W (↑)).relIndex (levi W (twoBlock k a')) *
  volume.real (T.excessCone a' (h + N * (k + 1)) ∩ slab k fun _ ↦ n + k + 1) := by
  -- the set is convex, so its points over `m ^ (k N)` tend to its volume; take `m = q ^ t`
  refine ge_of_tendsto_of_frequently (.const_mul _ (tendsto_card_div_pow_atTop_volume _ ?B (by
    unfold excessCone slab dotProduct; measurability) (Convex.addHaar_frontier _
    (by exact fun _ ⟨X, _, A⟩
    _ ⟨Y, _, B⟩ _ _ s t e ↦ ⟨fun _ _ _ _ ↦ by simp; grw [X .., Y ..] <;> simp [↓← add_mul, *],
    by positivity, fun j ↦ by simpa [univ.mul_sum] using convex_Icc _ _ (A j) (B j) s t e⟩))))
    (frequently_atTop'.2 fun t ↦ let m := T.q ^ t; ⟨m, t.lt_pow_self (mod_cast T.one_lt_q), ?_⟩)
  apply isBounded_inter_slab
  obtain ⟨_, _, p0, R, hR, h1⟩ := T.finite_residueField, Fact.mk T.prime, CharP.cast_eq_zero K _,
    ((parahoric W (↑)).subgroupOf (levi W (twoBlock k a'))).exists_isComplement_right 1
  set Λ := @Inter.inter ..
  obtain ⟨m1, _, _⟩ := NeZero.pos m, hR.finite_right.fintype, ((ZSpan.setFinite_inter _ ?B).subset
    (inf_le_inf_left _ (ZSpan.smul _ (NeZero.ne _)).le) : Λ.Finite).fintype
  field_simp
  norm_cast
  -- `p F = ∑ F_u (x ^ m) x ^ γ u`, `γ u ≡ u` modulo `m` of degree in `[k m, (k + 1) m)`
  let γ (u : _ × ZMod N → Fin m) := equivFunOnFinite.symm fun x ↦
    u x + m * ite (x.1 = a) (k - (∑ b, (u (b, x.2)).1) / m) 0
  let p := ∑ u, .mulRight K (monomial (γ u) 1) ∘ₗ (expand m).toLinearMap ∘ₗ polyOfCoeffs ∘ₗ
    (T.excessCond n a a' ⊥ h).subtype ∘ₗ .proj u
  -- `p F` is determined by its coefficients at these exponents, one translate per flag
  convert (LinearMap.pi fun x : R × Λ ↦ lcoeff K (equivFunOnFinite.symm (⌊x.2.1 · * m⌋₊)) ∘ₗ
    (T.polyAction x.1).toLinearMap ∘ₗ p).finrank_le_finrank_of_injective (.of_ker _ fun F f0 ↦ ?_)
  iterate 2 simp [relIndex, ← hR.card_right, mul_comm]
  ext u β; by_contra
  -- a monomial of least weight among the translates
  let w (x : Fin k × _) : ℝ := ite (T.isEven x.2) x.1 (-x.1)
  have ⟨⟨x, α⟩, hα, H⟩ := (univ.sigma fun x : R ↦ (T.polyAction x (p F)).support).exists_min_image
    (weight w ·.2) ⟨⟨⟨1, h1⟩, m • exponentOf β + γ u⟩, by
    simp [p, polyOfCoeffs, coeff_sum]
    rw [Fintype.sum_eq_single u fun v n ↦ Finset.sum_eq_zero fun _ _ ↦ ite_eq_right fun e ↦ n (by
    ext x; simpa [γ, mod_eq_of_lt, -mul_ite] using congr($e x % m))]; simpa [m1.ne']⟩
  refine absurd (congrFun f0 ⟨x, (α · / m), ?_, BoxIntegral.unitPartition.mem_smul_span_iff.2
    (⟨α ·, by simp [field]⟩)⟩) (by simpa using hα); clear f0
  -- its exponent is `m δ + ε`, with `δ` in a translate of some `F_u`, `ε` of the degrees of `γ u`
  obtain ⟨u, δ, ⟨ε, ⟨⟩⟩, hu, hv⟩ := by
    simp [p, ← AlgHom.mul_apply, (algHom_ext
      (by simp [m, ↓← pow_mul, polyAction_X, sum_pow_char_pow, mul_pow, ← C_pow, letterMatrix,
      ← (by simpa [← pow_mul, p0] using T.frobenius_pow_congr (N * t))]) : Commute (T.polyAction _)
      (expand m)), (expand m).mul_apply, polyAction_polyOfCoeffs, monomial_eq, polyAction_X] at hα
    simp [coeff_sum, polyOfCoeffs, univ.sum_mul, ← sum_prod_type'] at hα
    simpa [coeff_monomial_mul', le_iff_exists_add] using exists_ne_zero_of_sum_ne_zero hα
  have he s : ∑ b, ε (b, s) ∈ Set.Icc (m * k) (m * k + m) := by
    apply IsWeightedHomogeneous.prod _ _ _ fun j _ ↦ .pow (.sum _ _ (ite (j.2 = s) 1 0) fun b _ ↦
      (isWeightedHomogeneous_X K (if ·.2 = s then 1 else 0) (b, _)).C_mul (T.letterMatrix _ x b _))
      _ at hv
    simp [γ, weight_eq_sum, sum_prod_type, Nat.mul_sub] at hv
    grind [(by grw [Fin.is_le']; simp : ∑ b, (u (b, s)).1 ≤ k * m), mul_div_self_eq_mod_sub_self,
      mod_lt (∑ b, (u (b, s)).1) m1]
  refine ⟨fun i b b' e ↦ ?_, fun _ ↦ by positivity, fun s ↦ by simp [← univ.mul_sum, exponentOf,
    field, ← cast_sum, ← degree_eq_sum, Monomials.degree_eq, ← sum_div]; norm_cast; grind [he s]⟩
  simp_rw [dotProduct, mul_div, ← sum_div, ← nsmul_eq_mul', ← weight_eq_sum, field, mul_ite_zero]
  split
  grw [map_add, map_nsmul, (by omega : b = a), ‹b' = _›, not_lt.1 (hu <| (F u).2 _ x.1.2 δ ⟨i, ·⟩),
    weight_eq_sum, T.excessWeight_mem_Icc.2, ← univ.sum_smul, sum_prod_type_right,
    (he _).2]; simp [field]
  -- the root lemma at the other roots
  apply T.root_lemma i _ _ w 0 (fun g hg ↦ (hR.2 (⟨g, hg⟩⁻¹ * x)).elim fun b hb ↦
    Set.mem_of_eq_of_mem (by simpa using congr(T.polyAction ($hb.symm).1 (p F)))
    (aeval_sub_mem_of_gaussFiltration _ _ (mem_adicFiltration_of_nonpos <| by
    simpa using H ⟨_, ·⟩) fun y ↦ by simpa [polyAction_X, C_mul_X_eq_monomial] using
    (sum_mem fun i _ ↦ monomial_mem_gaussFiltration (mem_adicFiltration_of_nonpos (by
    unfold w; split <;> simpa [weight_single, *] using (T.p_dvd_letterMatrix_of_mem_parahoric y.2
      b.1.2 i _).mt)))).1) <;> grind [w_sq, dvd_def, twoBlock, rootVar, congr(($e : ℝ))]

/-- For β = `permStep` ν (signs by the parity of the letter, trivial permutations), the excess
`TwistingData.excessWeight` i a a' of β equals (1 − 1/q)·(β(u) − (ν(a,i) − ν(a',i))), where
u = `TwistingData.rootVar` a a' i. -/
lemma TwistingData.excessWeight_dotProduct_permStep i ν :
  T.excessWeight i a a' ⬝ᵥ permStep T.isEven T.P 1 ν = (1 - 1 / T.q) *
  (permStep T.isEven T.P 1 ν (T.rootVar a a' i) - (ν (a, i) - ν (a', i))) := by
  let F s := T.P ^ (1 + (s - i).val) * (ν (a, s + 1) - ν (a', s + 1)) / T.q
  rw [dotProduct, sum_prod_type_right, ← add_sub_cancel_right (∑ _, _), ← sum_add_distrib,
    ← (Equiv.subRight 1).sum_comp F, ← sum_sub_distrib, Fintype.sum_eq_single i] <;> intros <;>
    by_cases T.isEven ‹_› <;> simp [F, excessWeight, ↓one_add_val_sub_one_sub, rootVar,
    division_def, sub_mul, *] <;> field [T.prime.ne_zero]

/-- For a' = a + 1 there is a vector σ in `TwistingData.excessCone` a' (−1) with all coordinates in
[0, P^{3a'}]. -/
lemma TwistingData.exists_mem_excessCone_mem_Icc (ha : a.1 + 1 = a') :
    ∃ σ ∈ T.excessCone a' (-1), σ ∈ Set.Icc 0 fun _ ↦ (T.P ^ (3 * a'.1) : ℝ) := by
  obtain ⟨h5, hq, e⟩ := T.five_le_P, le_self_pow (NeZero.ne N) T.P,
    @T.excessWeight_dotProduct_permStep _ k
  rify at h5 hq e ⊢
  generalize (_ ^ T.o₀ : ℝ) = P at *
  let u b := ite (b ≤ a) (P ^ (2 * (a.1 - b)) * 2) 0
  have s b : (P ^ 2 - 1) * u b ∈ Set.Icc 0 (P ^ (3 * a'.1)) := by
    simp [u]; split <;> constructor <;> try bound
    grw [sub_le_self, (by bound : 2 ≤ P), ← pow_succ, ← pow_add, pow_le_pow_right₀] <;> grind
  refine ⟨permStep T.isEven P 1 fun x ↦ ite (T.isEven x.2) 1 P * u x.1, fun i b b' _ ↦ ?_,
    forall_and.1 fun (b', i) ↦ ?_⟩ <;> by_cases T.isEven i <;> simp [T.isEven_succ, *, field]
  iterate 2 rw [show u b = P ^ 2 * u b' + ite (b' = a') 2 0 by by_cases b = a <;> simp [u, *, ←
    mul_assoc, ← pow_add] <;> grind]; split <;> nlinarith [(s b').1, (by bound : P ≤ P * P ^ N)]
  all_goals grind [s b']

/-- For d ≤ D, the set of y ≥ 0 in ℝ^{n+1} with coordinate sum in [d − 1, d] has volume at most
|D^n/n!|. -/
lemma volume_sum_mem_Icc_le {n} {d D : ℝ} (hd : d ≤ D) : volume
    {y : Fin n.succ → ℝ | (∀ b, 0 ≤ y b) ∧ univ.sum y ∈ Set.Icc (d - 1) d} ≤ ‖D ^ n / n !‖ₑ := by
  cases n
  grw [measure_mono, volume_pi_pi ![Set.Icc (d - 1) d]] <;> simp [Set.pi]
  grw [← (volume_preserving_piFinSuccAbove _ 0).symm.measure_preimage_equiv, volume_eq_prod,
    prod_apply_le (by measurability), ← setLIntegral_eq_of_support_subset (s := .uIcc D 0) fun x
    h ↦ (nonempty_of_measure_ne_zero h).elim _, ← setLIntegral_congr uIoc_ae_eq_interval,
    lintegral_mono ((measure_mono _).trans <| volume_sum_mem_Icc_le <| sub_le_sub_right hd ·),
    ← ofReal_integral_norm_eq_lintegral_enorm (Continuous.integrableOn_uIoc (by fun_prop))] <;> simp
    [← ofReal_norm, integral_div, abs_sub_comm D, integral_pow_abs_sub_uIoc,
    @Fin.forall_fin_succ (succ _), factorial] <;> grind [Finset.sum_nonneg, Set.mem_uIcc]

/-- Size conditions, with c = 2k(k+1)dN²+2: 0 < 2r ≤ k, κ ≤ 1 ≤ y, 2ℓ = N, Nnk(ℓ+2)+n+k < P^ℓ,
6c+2 ≤ y, 2(N+2)k/y ≤ κ, (y+N(k+1))kP^{3r}+k+2 ≤ n/y, Nn(P^{−2r}+r²/(kP)) ≤ z. -/
def HeckeSizes (P d N k n r ℓ : ℕ) (κ y z : ℝ) := 0 < r ∧ 2 * r ≤ k ∧ κ ≤ 1 ∧ 1 ≤ y ∧ ℓ + ℓ = N ∧
  N * (n * (k * (ℓ + 2))) + n + k < P ^ ℓ ∧ 6 * (2 * ((k + k ^ 2) * (d * N) * N) + 2 :) + 2 ≤
  y ∧ 2 * (N + 2) * k / y ≤ κ ∧ (y + N * (k + 1)) * k * P ^ (3 * r) + k + 2 ≤ y⁻¹ * n ∧ N * n *
  (1 / P ^ (2 * r) + r ^ 2 / (k * P)) ≤ z

/-- Let K have characteristic p, a' = a + 1, and assume `HeckeSizes` with r = a', y = h. Then
[GL_k(W) : 𝒫]·dim `TwistingData.excessCond` n a a' ⊥ h ≤ (1 + κ)·m^N, where 𝒫 is the parahoric of
`twoBlock` a' and m counts degree-n monomials in k variables.

Dimension bounds mod p from flags and a cone volume. -/
lemma TwistingData.index_mul_finrank_excessCond_le [CharP K T.p] (ha : a.1 + 1 = a') {n ℓ h κ z}
  (big : HeckeSizes T.P T.o₀ N k n a' ℓ κ h z) : (parahoric W (twoBlock k a')).index * finrank K
  (T.excessCond n a a' ⊥ h) ≤ (1 + κ) * Fintype.card (Monomials (Fin k) n) ^ N := by
  obtain ⟨_ | k, ⟨σ, σ1, _, σ2⟩, _, -, -, _, _, _⟩ := k, T.exists_mem_excessCone_mem_Icc ha,
    T.finite_residueField, big
  lia
  let τ := (h + N * (k + 2)) • σ
  -- shift by `τ` into `excessCone a' 0` ∩ `slab`; cosets of `𝒫` times flags of the Levi subgroup
  -- are at most all flags, and flags times the volume of `excessCone a' 0` ∩ `slab` is the volume
  -- of `slab`
  grw [T.finrank_excessCond_le_volume ha, Measure.real, (measure_mono _).trans_eq
    (measure_preimage_add _ τ _), ← Measure.real, relIndex_le_of_le_right, mul_left_comm,
    ← mul_assoc, ← cast_mul, relIndex_mul_index, parahoric, index_comap, relIndex_le_of_le_right,
    relIndex_top_right, index_borel_le, T.card_residueField, cast_pow, @prod_mul_volume_inter_slab _
    _ _ T.isEven _ T.one_lt_P (n + k + 2 + ∑ b, τ ⟨b, ·⟩) (T.excessCone a' 0) (by simp [excessCone,
    pieriCone, excessWeight_dotProduct_permStep, ← le_div_iff₀', inv_lt_one_iff₀,
    ↓one_lt_q, -cast_pow, -cast_npow]), Measure.real, (measure_mono (by exact fun β g j _ ↦
    ⟨(g.1 ⟨·, j⟩), g.2 j⟩)).trans
    (((measurePreserving_flip.comp measurePreserving_curry).measure_preimage_le _).trans
    ((volume_pi_pi _).trans_le (prod_le_pow_card _ _ _ fun j _ ↦ volume_sum_mem_Icc_le (show _ + _
    ≤ h⁻¹.exp * n by simp [τ]; grw [σ2 _, ← add_one_le_exp]; simp; grind))))] <;> try simp [
    relIndex, card_finsuppAntidiag_nat_eq_choose, mul_pow, mul_div_assoc, -enorm_mul, ← exp_nat_mul,
    (isBounded_inter_slab (T := ZMod N) ..).measure_lt_top.ne]
  grw [← choose_symm_add, ← pow_le_choose, ← le_add_right, exp_bound' (n := 1)] <;> (try gcongr) <;>
    simp [field] at * <;> nlinarith
  -- the Levi subgroup and the Iwahori subgroup lie in `𝒫`
  iterate 2 intro; simp [parahoric, parabolic, levi, BlockTriangular]; grind [twoBlock,
    not_isUnit_zero]
  -- the shift by `τ`
  exact ⟨fun β g _ _ _ _ ↦ by simp [τ]; grw [g.1 .., σ1 ..] <;> bound, fun β ⟨_, _, g⟩ ↦
    ⟨by positivity, (by simp; grind [g ·])⟩⟩

/-- Let K have characteristic p and assume `HeckeSizes`. Then for every M, ∑_{d<M} dim
V_d ≤ (1 + z)·m^N, where V_d = `TwistingData.deepForms` n r d and m is the number of monomials of
degree n in k variables.

Dimension bounds mod p from flags and a cone volume. -/
lemma TwistingData.sum_finrank_deepForms_le [CharP K T.p] {n r ℓ κ h z} (big :
  HeckeSizes T.P T.o₀ N k n r ℓ κ h z) M : (∑ d ∈ range M, finrank K (T.deepForms k n r d) : ℝ) ≤
  (1 + z) * Fintype.card (Monomials (Fin k) n) ^ N := by
  -- `3 r < ℓ`, as `P ^ (3 r) ≤ n < P ^ ℓ` and powers of `P` increase
  obtain ⟨_ | k, _, _, hk, -, hy, _, _, -, -, h2, h3⟩ :=
    k, (pow_right_mono₀ T.one_lt_P.le).map_sup ℓ (3 * r), big; lia
  grw [← hy, inv_one] at h2
  -- a form in `V_d` is determined by its coefficients at the monomials of cost at least `d`
  grw [((LinearMap.funLeft K K Subtype.val).domRestrict _).finrank_le_finrank_of_injective
    (.of_ker _ fun F e ↦ F.ext (Not.imp_symm (T.exists_le_weight_of_mem_deepForms hk
    (by norm_cast at *; lia) F.2) fun ⟨β, h, H⟩ ↦ h congr($e ⟨β, lt_succ_of_le (le_floor H)⟩)))]
  -- count each monomial for the `d` up to its cost
  simp [Fintype.card_subtype, ← sum_boole, (range M).sum_comm, ↓← mem_range, weight_eq_sum]
  -- take the mean, by the symmetry of the rows: average over the permutations `a ↦ b - a`
  grw [min_le_right, floor_le (by positivity), sum_add_distrib, ← h3, le_expect univ_nonempty
    fun b ↦ imp_intro ((Equiv.Perm.subtypePerm (equivCongrLeft (.subLeft b)).symm (by
    simp [↓mem_finsuppAntidiag'])).bijective.comp_left.sum_comp _).ge]
  simp [↓expect_sum_comm, Finset.expect_eq_sum_div_card, ← univ.sum_mul, *, ← univ.mul_sum,
    exponentOf, field, ↓sum_prod_type, ← cast_sum, sum_deepIndicator, apply_ite, sum_ite,
    Fin.card_filter_val_lt,
    ← degree_eq_sum, Monomials.degree_eq, ← translate_apply, sum_translate, div_eq_mul_inv]
  grw [card_finset_fin_le, cast_succ, cast_div_le]
  ring
  bound
end
