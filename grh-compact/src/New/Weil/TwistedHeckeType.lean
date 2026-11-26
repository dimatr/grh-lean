import Lib.DiscreteSeries.FrameAction
import New.Weil.LiveSum
import New.Weil.ChainValuation
import Lib.Adelic.Counting

section
/-! General lemmas on `IndexDvd` and `HasType`: bookkeeping for the index of a submodule.

Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Index of a submodule bounded via determinants; multiplicativity; operators onto up to
small index. -/


open Matrix Submodule Finset Pointwise Module
variable {O U V ι} [CommRing O] [AddCommGroup U] [Module O U] [AddCommGroup V] [Module O V]
  {M N P : Submodule O V} {M' N' : Submodule O U} {z z' a : O} {f : V →ₗ[O] V}
attribute [local simp] sum_smul_mem

variable (M N z) in
/-- The property that every finite family (Φ_k) in M admits a square matrix m over O with det m
dividing z and all combinations ∑_k m_{ik} Φ_k in N. -/
def IndexDvd := ∀ n (Φ : Fin n → V), (∀ k, Φ k ∈ M) → ∃ m, det m ∣ z ∧ ∀ i, ∑ k, m i k • Φ k ∈ N

/-- `IndexDvd` pulls back along a linear map f: U → V: if it holds for (M, N, z), f(M') ⊆ M and
every x in M' with f(x) in N lies in N', then it holds for (M', N', z). -/
lemma IndexDvd.comap (h : IndexDvd M N z) (f : U →ₗ[O] V) : M' ≤ M.comap f → (∀ x ∈ M', f x ∈ N →
  x ∈ N') → IndexDvd M' N' z := fun a _ _ _ c ↦ (h _ _ (a <| c ·)).imp (by aesop)

/-- If M ⊆ N, then `IndexDvd` holds for M, N and every scalar z. -/
@[simp] lemma IndexDvd.of_le : M ≤ N → IndexDvd M N z := fun _ _ _ _ ↦ ⟨1, by aesop⟩

/-- If `IndexDvd` holds for (M, N, z) and for (N, P, a), then it holds for (M, P, za). -/
lemma IndexDvd.trans (h : IndexDvd M N z) (g : IndexDvd N P a) : IndexDvd M P (z * a) :=
  (h · · · |>.rec fun m b ↦
  (g _ _ b.2).imp' (· * m) (by simp_all [mul_comm, mul_dvd_mul, mul_smul, ← Module.smul_apply]))

/-- `IndexDvd` pushes forward along a linear map f: if it holds for (M, N, z), M' ⊆ f(M) + N'
and f(N) ⊆ N', then it holds for (M', N', z). -/
lemma IndexDvd.map (h : IndexDvd M N z) (f : V →ₗ[O] U) : M' ≤ M.map f ⊔ N' → N.map f ≤ N' →
  IndexDvd M' N' z := by
  intro a b _ _ H; choose x hx y hy e using by simpa using (mem_sup.1 <| a <| H ·)
  peel h _ x hx
  simpa [← e, add_mem_cancel_right, hy] using b ⟨_, this, rfl⟩

/-- Let f_i : V → U be O-linear, M ⊂ V, N' ⊂ U submodules, with `IndexDvd` holding for (M,
f_i⁻¹(N'), z) for each i. For finite s it then holds for (Q, N', z^|s|), Q the span of N' and the
f_i(M), i ∈ s. -/
lemma IndexDvd.sup {f : ι → V →ₗ[O] U} (h : ∀ i, IndexDvd M (.comap (f i) N') z) (s : Finset ι) :
    IndexDvd (span O (.image2 (f ·) s M ∪ N')) N' (z ^ #s) := s.cons_induction (by simp) fun i _
  _ ↦ by simp [pow_succ', *]; use ((h i).map _ (by order) (by simp [map_comap_eq])).trans

lemma IndexDvd.comp (e : M.map f ≤ M) : IndexDvd M (M.map f ⊔ a • M) z → IndexDvd M (N ⊔ a • M) z' →
  IndexDvd M (N.map f ⊔ a • M) (z * z') := (·.trans <| ·.map f (by order) (by grw [← e]; simp))

/-- The endomorphism y preserves the submodule M, and the index of yM + p^nM in M divides p^l,
in the sense of `IndexDvd`, for some natural l ≤ c. -/
def HasType p M n (y : End O V) (c : ℝ) :=
  M.map y ≤ M ∧ ∃ l : ℕ, l ≤ c ∧ IndexDvd M (M.map y ⊔ p ^ n • M) (p ^ l)

/-- Exponents add under products: if each operator T(l), l in a list L, has type (`HasType`) with
exponent t(l) for fixed z, M, s, then the product of the T(l) has type with exponent ∑ t(l). -/
lemma HasType.prod {s T t} (L : List ι) : (∀ l ∈ L, HasType z M s (T l) (t l)) →
    HasType z M s (L.map T).prod (L.map t).sum := by
  induction L <;> simp [HasType, End.one_eq_id, End.mul_eq_comp, map_comp]
  next I => exact fun e i _ _ H ↦
    (I H).imp (by grw [·, e]) (.imp' (i + ·) (by grind [IndexDvd.comp]))

/-- Let O be a valuation domain and A a square matrix over O indexed by ι whose determinant
divides z. If N contains the image of A in O^ι, then `IndexDvd` holds for (O^ι, N, z). -/
lemma IndexDvd.of_det_dvd [IsDomain O] [ValuationRing O] [Fintype ι] {A : Matrix ι ι O} {N}
    (h : A.det ∣ z) (e : .map A.mulVecLin ⊤ ≤ N) : IndexDvd ⊤ N z := fun _ Φ _ ↦
  (isValuationPair_top.hermite (.refl _) (fromBlocks 1 (-of Φ) 0 Aᵀ) (1 ⊕ᵥ 0)).elim fun _ ⟨_, D, t,
  a, b⟩ ↦ ⟨_, .trans ⟨_, by simpa [mul_left_comm, (ext (by tauto) : D.toBlocks₁₂ = 0)] using
  (D.fromBlocks_toBlocks ▸ congr(($a).det) :)⟩ h, fun i ↦ e ⟨_ ∘ _, ⟨⟩, funext (by simpa [← b,
  toBlocks₁₁, mul_apply, mulVec_eq_sum, neg_add_eq_sub] using (@t (.inl i) <| .inr ·))⟩⟩
end

section
/-! Divisibility of matrix jets at non-split primes. The jet of a series Θ along a polynomial Q is
(Q(∂)Θ)(0); the partners of a place σ are the −p^eσ. For p inert or ramified in K, jets of theta
products along products of minors have valuation bounded below, since each derivative gains and
couplings with partner places take back, leaving about (a/p − w)₊ at inert p for order a against
partner order w; this is the weight of the prime sum, and scaled jets are integral at every p. One-
and two-variable divisibility at inert p over an imaginary quadratic field is known. Related work:
Katz, Divisibilities, congruences, and Cartier duality, 1981; Chellali, Congruences entre nombres de
Bernoulli–Hurwitz dans le cas supersingulier, 1990; Fujiwara, Divisibilities of special values of
real analytic Eisenstein series, 1988; Bannai–Kobayashi–Yasuda, Radius of convergence of the p-adic
sigma function, 2017.

This file: Tilting matrices that kill Frobenius pairings at controlled determinant cost. Lower bound
for valuations of Schur jets when Frobenius couplings are silenced. -/

open Finset Real Matrix Valuation MvPolynomial Fintype IsUltrametricDist NormedField PolyRep

/-- For Y over 𝔬, any θ ∈ 𝔬 (θ = 0 allowed) and q = |θ| there are M_{σ,h} ∈ M_h(𝔬), with ∏|det M|
over all columns ≥ q^{∑`couplingCount`}, such that the pairings ∑_a m_a^{p^j} m′_a (j ∈ S, m of
M_{σ,h}Y_σ, m′ of M_{pr_jσ,h′}Y_{pr_jσ}) vanish modulo p and θ, unless h = 1 and σ ∈ ev, or
h = h′ = 1 and pr_jσ ∈ ev. -/
lemma exists_null_coupling_frames {p : ℕ} [Fact p.Prime] {Φ n} [Fintype Φ] [Fintype n] (pr : ℕ → Φ →
  Φ) S N κ ev (Y : Φ → n → ℕ → valRingCp p) θ : ∃ M : ∀ _ h,
  Matrix (Fin h) (Fin h) _, ‖θ‖ ^ ∑ e ∈ S, ∑ σ, couplingCount p κ N
  ev σ (pr e σ) e ≤ ∏ j : Σ _, Fin N, ‖(M j.1 j.2).det‖ ^ κ j.1 j.2 ∧ ∀ {R} [CommRing R] [CharP R p]
  (g : _ →+* R), g θ = 0 → ∀ (j : S) σ {h} i {h'} i', ¬(h = 1 ∧ (σ ∈ ev ∨ h' = 1 ∧ pr j σ ∈ ev)) → g
  (∑ a, (M σ h i ⬝ᵥ (Y σ a ·)) ^ p ^ j.1 * M (pr j σ) h' i' ⬝ᵥ (Y (pr j σ) a ·)) = 0 := by
  delta couplingCount; extract_lets t r D
  choose ρ hρ using (@IsAIC.exists_pow_eq (valRingCp p) _ (.of_isIntegrallyClosedIn ℂ_[p]) <| p ^ ·)
  let A h e σ b s := (h = 1 → cond b σ (pr e σ) ∉ ev ∧ s = b) ∧ (ite (s ∧ h ≠ 1)
    ((D σ : ℝ) / p ^ e ≤ D (pr e σ)) (s = b → (t σ : ℝ) / p ^ e ≤ r (pr e σ) + t (pr e σ)) ↔ b)
  choose M hM v _ hA using fun τ h ↦ IndexDvd.of_det_dvd (det_diagonal (d :=
    fun ((e : S), σ, b, (o : Option (Fin h))) ↦ ite (cond b σ (pr e σ) = τ ∧
    A h e σ b o.isSome) (ρ (ite b e 0) θ) 1)).dvd le_rfl _ (fun j (e, σ, b, o) ↦ o.elim (∑ a,
    ite b (ρ e (Y (pr e σ) a 0)) (Y σ a 0 ^ p ^ ↑e) * Y τ a j) (diagonal 1 j)) (by simp)
  use M, ?_, fun g _ j σ h i h' _ _ ↦ ?_
  grw [← fun τ h ↦ show ‖(_ :
    valRingCp p)‖ ≤ ‖(M τ h).det‖ from (integer.integers _).le_of_dvd (hM ..)]
  simp (disch := intros; positivity) only [← rpow_mul_natCast, sum_mul, norm_prod,
    ← pow_boole, norm_pow, fun e ↦ show ‖ρ e θ‖ = ‖θ‖ ^ (p ^ e : ℝ)⁻¹ by
      simp [← congr(‖$(hρ e θ)‖), ← rpow_natCast_mul], ← S.sum_coe_sort, ← rpow_sum_of_nonneg,
    ← @sum_comm (Sigma _), min_def, Fintype.sum_prod_type]
  congr!
  split_ifs <;> simp [*, A, ite_and, Fintype.sum_sigma] <;> simp +zetaDelta [sum_range,
    sum_div, ← sum_add_distrib] <;> clear * - θ <;> grind [Nat.cast_eq_one]
  have D h b i o (_ : A h j σ b o.isSome) :=
    congr(g ($(hA (cond b σ (pr j σ)) h i) (j, σ, b, o) ^ p ^ ite b j.1 0)).symm
  simp [↓Option.forall, -pow_ite, @sum_comm n, hρ, mul_pow,
    @mul_sum n, mul_left_comm (M ..), ← mul_sum, ← map_pow _ (ρ ..), sum_pow_char_pow] at D
  obtain ⟨⟨⟩, ⟨⟩, H, ⟨⟩⟩ : ∃ b s, A (b.rec h' h) j σ b s ∧ 1 = s.rec (b.rec h h') 1; simp; lia
  repeat simp [sum_pow_char_pow, mul_pow, mul_assoc, mul_comm (∑ _, _), ← mul_sum, *, dotProduct]

attribute [local simp] sum_range prod_pow_eq_pow_sum prod_smul Finsupp.prod smul_pow ite_and
  linearSeries boxes

/-- Divisibility of Schur jets. Let κ fit, with B boxes, |ϖ| = p^{−ρ}, |θ| = p^ω, and let the
charges g be nonzero at one end of each coupling exempted by the even places ev. If
`IsIntegralOnNullCone` holds up to degree B, each entry of the jet matrix along S_κ has valuation ≥
(1/(p−1) − ρ)B + ω∑`couplingCount` − |Φ||n′|³(⌊log_p B⌋ + 1) − m, m the total charge of the boxes of
its row.

Divisibility of matrix jets at non-split primes. -/
lemma norm_schurJet_le {p : ℕ} [Fact p.Prime] {Φ n n'} [Fintype Φ] [Fintype n] [Fintype n']
    {κ} (hκ : FitsRanks n n' κ) {pr S ρ ω ϖ θ Θ ev} (hϖ : ‖ϖ‖ = p ^ (-ρ))
    (hπ : ‖(θ : valRingCp p).1‖ = p ^ ω) (g : Φ → ℕ → _ → ℕ) (hg : ∀ e ∈ S, ∀ σ h b,
    σ ∈ ev ∨ h = 1 ∧ pr e σ ∈ ev → g σ 1 b ≠ 0 ∨ g (pr e σ) h b ≠ 0) {i'} {i : WeylIndex n κ} :
  let N := card n'; let B := boxes κ N; let m := ∑ τ, ∑ h : Fin N, ∑ j, ∑ b, g τ h ((i' τ).1 h j b)
      IsIntegralOnNullCone pr S ϖ θ B Θ → ‖schurJet κ Θ i' i‖ ≤ p ^ (m - ((1 / (p - 1) - ρ) * B + ω
        * ∑ e ∈ S, ∑ σ, couplingCount p κ N ev σ (pr e σ) e - card Φ * N ^ 3 * (p.log B + 1))) := by
  intro N B m hV; let L := ((jet _).flip Θ).toAddMonoidHom
  refine (exists_val_coeff_le_val_eval valuation ![AddMonoidAlgebra.map L _]).elim fun (y : _ →
    valRingCp p) h ↦ .trans (coord_mem_of_coeff_mem ((valuation.leAddSubgroup _).comap L) _
    (sum_schur_smul_nablaBasis hκ ..) (h 0) _) ?_
  have : 1 < p := Fact.out
  choose M hM hA using exists_null_coupling_frames pr S N κ ev (y ⟨⟨·, ·⟩, ·⟩) θ
  let z := fun (τ, b, a) (o : (Σ h : Fin N, Fin h) × _) ↦
    ite (o.2 = (τ, b)) (p ^ g τ o.1.1 b * M τ _ o.1.2 ⬝ᵥ (y ⟨⟨τ, a⟩, ·⟩)) 0
  specialize hV (linearSeries ∘ z) (by simp) fun φ h0 j hj ↦ by
    simp [sum_pow_char_pow, Finset.sum_mul_sum, MvPowerSeries.smul_eq_C_mul, mul_pow,
      mul_mul_mul_comm _ (_ ^ _), @sum_comm _ _ (Φ × _), ← sum_mul]
    exact sum_eq_zero fun o _ ↦ sum_eq_zero fun q _ ↦
      flip id (hA (φ.comp _) h0 ⟨j, hj⟩ o.2.1 o.1.2 q.1.2) (by simp [apply_ite, CharP.cast_eq_zero,
      z, NeZero.ne, zero_pow_eq, sum_prod_type, Prod.ext_iff, ↓mul_comm (_ ^ _)]; grind +splitImp)
  have hc : _ * (‖ϖ‖ ^ B * (↑p)⁻¹ ^ m) ≤ ‖∏ τ, ∏ h : Fin N, ∏ j, (valRingCp p).subtype
    (M τ h)ᵀ.det * ∏ b, ϖ * p ^ g τ h ((i' τ).1 h j b)‖ := (mul_le_mul_of_nonneg_right hM
    (by positivity)).trans (by simp [B, m, Fintype.prod_sigma, norm_p_eq_inv, ← pow_mul])
  erw [(by simp [eval, eval₂, Finsupp.sum_mapRange_index, L, map_finsuppSum, C_eq_smul_one,
    mul_comm] : ∀ y f, eval y (AddMonoidAlgebra.map L f) = L (eval (C ∘ y) f)),
    ← mul_le_mul_iff_right₀ (hc.trans_lt' (hϖ ▸ hπ ▸ by positivity)), ← norm_smul,
      ← LinearMap.map_smul₂]
  grw [← hc, (?_ : _ • _ = linSubst (of (ϖ * z · ·)) (∏ τ, ∏ h : Fin N, ∏ j, (of fun b i ↦
    X (⟨h, i⟩, τ, (i' τ).1 h j b)).det)), ← jet_subst_linearSeries]
  simp only [det_apply, Fintype.prod_sum, X, ← monomial_sum_one, of_apply, prod_smul, map_sum,
    LinearMap.sum_apply]
  apply norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intros; set d : _ →₀ ℕ := Finset.sum ..
  have e : B = d.degree := by simp [d, B, mul_comm]
  apply flip id (d.support.sum_le_sum fun x _ ↦ (padicValNat_factorial_mem_Icc
    ((d.le_degree x).trans_lt (p.lt_pow_succ_log_self this _))).1)
  simp [norm_natCast_eq_inv_pow_padicValNat, smul_sum, smul_smul] at hV ⊢
  grw +useKAbstract [hV e.ge, card_le_univ, card_prod, Fintype.card_sigma,
    sum_le_card_nsmul _ _ N (by simp)]
  simpa [*, m, d.degree_apply, ← sum_div, ← rpow_mul, ← rpow_add, this.pos, ← rpow_neg,
    ← rpow_natCast p, ← rpow_mul_natCast] using (by linear_combination ·)
  simp only [nablaBasis, tableauPoly, minor, map_prod, AlgHom.map_det, RingHom.map_det, N,
    smul_eq_C_mul, ← prod_mul_distrib, map_mul, mul_rotate (det _), ← det_mul_column, ← det_mul]
  congr!; ext
  simp [z, linSubst, sum_prod_type, smul_eq_C_mul, mul_sum, rowSubst, sum_mul, entrywise,
    @sum_comm n, apply_ite, mul_assoc, mul_comm (X _), mul_left_comm (C (M ..).1)]
end

section
/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Part of: Trading denominators at the level prime for a column operator (see
New.Columns.TwistedHeckeType).

This file: Column level at N read as conjugated mirabolic group; restriction keeps valuation, size.
Index bound at N for preimage of the lattice under the Gauss-sum operator power. Splitting
characters of the chain: unramified above the level prime, double splitting. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Fintype Gf IsSplitLevel Matrix NeZero Valued WithZero Equiv

attribute [-simp] WithZero.inv_exp

variable {P} (D : Data P) {p : ℕ} [Fact p.Prime] [PadicPlace p]

lemma Data.GaugeLe.restrictToY_of_diag {d : Gf _ _} (hs : ∀ τ, .map (adeleExtension (weightEmbedding
  ιₚ τ)) d.1 = diagGL (ite ·.isLeft 1 (ite (star (inducedPlace τ) ∈ D.piPlaces) (.mk0 ↑D.N out) 1)))
  {c φ} (h : GaugeLe d c φ) : GaugeLe 1 c (D.restrictToY φ) := fun g ↦
  ((one_mul _).trans_le (h (D.borderU g))).trans' (Eq.trans_le (by
  erw [mulVec_mulVec, D.branching.2.1 _ _ fun τ ↦ (d.1.map (adeleExtension (weightEmbedding ιₚ
    τ))).det⁻¹, smul_mulVec, ← mulVec_mulVec, Units.smul_def, norm_smul, weylGauge_smul]
  use congr($(?_) * ‖_ *ᵥ $(funext (by simp [mulVec_eq_sum]))‖)
  simpa [hs, apply_ite, @starRingEnd_apply D.E, branchExp] using congr(∏ τ :
    D.Φ, $((isEquiv_placeOfEmb
    (weightEmbedding ιₚ τ)).eq_iff (s := ite _ D.N 1) |>.2 (by split <;> simp_all
    [inducedPlace, placeOfEmb_comp_star, ← v_algebraMap_eq_valuation, v_algebraMap_eq_intValuation,
    intValuation_pi, D.isSplitLevel_piPlaces.3, piPlaces])).1⁻¹ ^ D.branchExp τ)
  simp [← map_inv, ← ext_iff, borderU, PolyRep.blockScalar, hs _ ▸ map_inv ..])
    (norm_mulVec_le (by simp [IsUltrametricDist.norm_intCast_le_one]) _))

/-- Let p ≠ N be prime and ι : ℂ → ℂ_p. If the gauge at ι of φ(g) on the lattice of g is at most
c for all g, the same holds for the restriction of φ to Y_m. -/
lemma Data.GaugeLe.restrictToY (hp : p ≠ D.N) {c φ} :
    GaugeLe 1 c φ → GaugeLe 1 c (D.restrictToY φ) :=
  restrictToY_of_diag D (by simp [D.notMem_piPlaces_of_ne hp, p_mem_inducedPlace, Units.ext_iff])

lemma Data.weylNormSq_restrictToY_le (σ : ℂ →+* ℂ) φ h : weylNormSq (σ ∘ (D.restrictToY φ).1 h) ≤
  .exp (D.x ^ 70 - (∑ τ, D.branchExp τ : ℝ) * .log D.N) * weylNormSq (σ ∘ φ.1 (D.borderU h)) := by
  have k (τ : D.Φ) := congr(‖weightEmbedding σ τ $D.π_mul_star‖.log)
  erw [weylNormSq_comp_smul]
  simp [← sq, Function.comp_def, σ.map_mulVec, -RingHom.coe_comp] at *
  grw [D.branching.2.2.1 _ (sum_mono fun _ ↦ (sum_le_card_nsmul _ _ (D.n D.m * D.h) ?_).trans
    (mul_le_mul_left (c := D.n D.m) ?_ _)), ← mul_assoc, ← Real.le_exp_of_log_le]
  all_goals simp_all [Real.log_prod, Real.log_mul, @starRingEnd_apply D.E,
    sum_mul, mul_sum, mul_left_comm (2 : ℝ), card_congr D.lastIndexEquiv, prod_eq_zero_iff, -not_or]
  exacts [D.le_of_hasLogBound, by intros; gcongr <;> grind [columnsY, κ, keptColumns,
    reducedHalfGap], by lia]

/-- The set of complex conjugates of the primes `Data.inducedPlace` τ of E above p, as τ runs over
the embeddings in the CM type Φ. -/
noncomputable def Data.nonInducedPlaces := univ.image fun τ ↦ star (D.inducedPlace τ)

lemma Data.isSplitLevel_nonInducedPlaces [PadicPlace D.N] : IsSplitLevel D.nonInducedPlaces
  D.N := by use (by simpa [nonInducedPlaces, ← inducedPlace_mul] using fun τ ↦ (P.smul_ne_star
  D.N_modEq_one (D.p_mem_inducedPlace τ) (v := · / τ))) <;> grind [P.q_eq_of_modEq_one
  D.N_modEq_one, v_N_eq_exp_neg_one, p_mem_inducedPlace, mem_star_place, star_natCast, star_star, =_
  inducedPlace_mul, nonInducedPlaces, P.exists_smul_eq_or_star (D.p_mem_inducedPlace 1)]

variable [PadicPlace D.N] [l : IsSplitLevel D.nonInducedPlaces D.N]

/-- The finite adelic unitary point on X_j supported on S ∪ S̄, with component diag(1, …, 1, N)
at the w in S dividing π and 1 at the other w in S; S = `Data.nonInducedPlaces` above N. -/
noncomputable abbrev Data.diagPointN j := l.embedGL (diagN (D.InitIndex j) D.piPlaces)

/-- The homomorphism from GL(∏_{w∈S} E_w) to the finite adelic unitary group of X_j given by
`IsSplitLevel.embedGL` followed by conjugation g ↦ dgd⁻¹, d = `Data.diagPointN` j. -/
noncomputable def Data.conjEmbedGL j := (MulAut.conj (D.diagPointN j)).toMonoidHom.comp l.embedGL

/-- The representation of the general linear group over ∏_{w∈S} E_w on smooth forms of stage j,
by right translation through the conjugated embedding `Data.conjEmbedGL`. -/
noncomputable abbrev Data.nonInducedRep j :=
  Rep.of (X := D.Stage j) ((smoothFormRep ..).comp (D.conjEmbedGL j))

lemma Data.adeleExtension_map_diagN j S τ : .map (adeleExtension (weightEmbedding ιₚ τ))
  (l.embedGL (diagN (D.InitIndex j) S)).1 = diagGL (ite ·.isLeft 1
  (ite (star (inducedPlace τ) ∈ S) (.mk0 ↑D.N out) 1)) := congr($(atPlace_atSplits star_notMem _
  ⟨_, by simp [nonInducedPlaces, inducedPlace, placeOfEmb_comp_star]⟩).map _).trans
  (by simp [diagN, inducedPlace, placeOfEmb_comp_star, Units.ext_iff]; aesop)

lemma Data.lastColDatum_conj_ne_zero_iff {j} (k : Gf _ (D.X j)) : l.lastColDatum lastBasisVector
  (atPlaces _ ((D.diagPointN j)⁻¹ * k * D.diagPointN j)).1 ≠ 0 ↔ ∀ w ∈ D.nonInducedPlaces, (∀ b c,
  v (k.atPlace w b c) ≤ 1) ∧ (star w ∈ D.piPlaces → ∀ b, v (((k⁻¹.atPlace (star w)).1 - 1) (.inr ())
  b) ≤ exp (-1)) ∧ (w ∈ D.piPlaces → ∀ b, v (((k.atPlace w).1 - 1) (.inr ()) b) ≤ exp (-1)) := by
  simp [Subtype.forall', l.3, liftFn_apply, mem_O_locProd, ← map_inv, ZMod.val_one, diagN,
    lastColDatum, ← forall_and, @forall_comm _ D.nonInducedPlaces, div_le_one₀, -Subtype.forall,
    reduction_eq_iff, @funext_iff (_ ⊕ _), k⁻¹.atPlace_star rfl, show ∀ b c w,
    atPlaces D.nonInducedPlaces k b c w = k.atPlace w b c by tauto]
  congr! 1; split <;> simp [inv_mul_cancel_of_invertible, *, l.3, inv_mul_le_one₀, mul_right_comm,
    D.isSplitLevel_piPlaces.1, ((D.isSplitLevel_piPlaces.4 _).1 (l.natCast_mem ..)).resolve_left]
  grind [mul_le_one', show exp (-1) ≤ 1 by tauto]
  simp [← v_conjLoc rfl (k.atPlace _ _ _ - 1)]

lemma Data.atPlaces_conj_mem_mirabolic {j} (k : D.columnLevel j) :
  atPlaces _ ((D.diagPointN j)⁻¹ * k.1 * D.diagPointN j) ∈ l.mirabolic :=
  have B (k) := (D.lastColDatum_conj_ne_zero_iff _).2 fun w _ ↦ ⟨(mem_Kf_iff.1 (levelOf_le_Kf k.2.1)
    w).isIntMatrix, (D.mem_columnLevel.1 k⁻¹.2).2 _, (D.mem_columnLevel.1 k.2).2 w⟩
  (exists_inclGL_eq (B k) (by simpa [mul_assoc] using! B k⁻¹)).imp (by simp [Units.smul_def, col])

lemma Data.mem_ramified_of_mem_ramifiedColumns {φ} (r : φ ∈ D.ramifiedColumns) :
  φ.1 ∈ l.ramified (D.nonInducedRep 0) := fun w ↦ by
  obtain a | a := (D.isSplitLevel_piPlaces.4 _).1 (IsSplitLevel.natCast_mem _ w.2) <;> peel
    exists_embedGL_scalar_eq_scalarFin (n := D.X 0) w ((D.exists_centralGen ⟨_,
    a⟩).choose_spec.1.imp_right (by aesop)) <;> exact (D.exists_eq_sub_centralGen ⟨_, a⟩ r).imp' (↑)
    (by simp_all [conjEmbedGL, ← (commute_scalarFin _).eq, centralGen])

/-- The operator F = `IsSplitLevel.fourierOp` of the representation `Data.nonInducedRep` on smooth
forms of stage 0 sends columns to columns. -/
lemma Data.fourierOp_mem_column {φ} (r : φ ∈ D.Column) :
  fourierOp (D.nonInducedRep 0) φ ∈ D.Column := fun k ↦ have G := D.atPlaces_conj_mem_mirabolic k
  by refine (mirabolic_fix_fourierOp (π :=
    D.nonInducedRep 0) (smoothFormRep _ _ k) G fun a b e ↦ have := mul_mem e (inv_mem G)
    Iff.mpr ?_ ((fun B C o ↦ r (⟨D.conjEmbedGL 0 a * k * D.conjEmbedGL 0 b * k.1⁻¹,
      D.mem_columnLevel.2 ⟨D.mem_chosenLevel_of_supportedOn l.natCast_mem
      ⟨(mem_Kf_iff_of_supportedOn o).2 fun w h ↦ mem_intGL.2 ⟨(B w h).1, (C w h).1⟩, o⟩, fun w x ↦
      ((l.4 w).1 (D.isSplitLevel_piPlaces.natCast_mem _ x)).rec (B w · |>.2.2 x) fun y ↦
      star_star w ▸ (C _ y).2.1 (by simpa)⟩⟩ * k)) ((D.lastColDatum_conj_ne_zero_iff _).1
      (lastColDatum_ne_zero ?_)) ((D.lastColDatum_conj_ne_zero_iff (_ * _)⁻¹).1
      (lastColDatum_ne_zero (inv_mem_iff.1 ?_))) ?_)).trans ?_ <;> simp_all [conjEmbedGL,
    mem_supportedOn.1 (embedGL_mem_supportedOn _), mul_assoc]

/-- At an embedding ι : ℂ → ℂ_N, the ι-integral columns have index (`IndexDvd`) dividing N^e, for
some e ≤ 4mfb·dim(columns), relative to the smooth forms that F^{ϱ+1} sends to columns
integral at `Data.diagPointN`; F = `IsSplitLevel.fourierOp` of `Data.nonInducedRep`. -/
lemma Data.exists_indexDvd_fourierOp_pow {P} {D : Data P} [PadicPlace _] (l :=
  D.isSplitLevel_nonInducedPlaces) : ∃ e : ℕ, e ≤ 4 * D.m * D.f * D.b * Module.finrank ℂ D.Column ∧
  IndexDvd (integralFormsAt D.Column 1) ((integralFormsAt D.Column (D.diagPointN 0)).comap
  ((fourierOp (D.nonInducedRep 0) ^ (D.ϱ + 1)).restrictScalars _)) (D.N ^ e) := by
  let t a := ∑ i : StdClasses (D.columnLevel 0) × WeylIndex (D.X 0) D.κ, ∑ τ, tableauWeight i.2 τ a
  let d S := (l.embedGL (diagN (D.InitIndex 0) S))⁻¹
  have h b : IndexDvd (integralFormsAt D.Column (D.diagPointN 0 * d b))
    (integralFormsAt D.Column (D.diagPointN 0)) (D.N ^ t (.inr ()))
  choose γ h h' using fun c ↦ exists_mul_mem_integralAbove D.N (c * (D.diagPointN 0 * d b)) (d b)
  use ((IndexDvd.of_det_dvd (det_diagonal.trans (prod_pow_eq_pow_sum ..)).dvd le_rfl).map
    ((Algebra.linearMap
    ..).compLeft _) le_sup_left le_rfl).comap ⟨⟨fun φ x ↦ φ.1 (stdEmbFin (γ x.1.out) * x.1.out)
    x.2, by tauto⟩, by tauto⟩ (fun _ H ↦ ⟨(⟨_, (weylGauge_le_one_iff _ (by simp_all [mul_assoc])).1
    (H.2 _) ·.2⟩), ⟨⟩, rfl⟩) fun φ ⟨H, _⟩ ⟨_, ⟨y, _, rfl⟩, e⟩ ↦ ⟨H, fun g ↦ ?_⟩
  obtain ⟨c, _, k, rfl⟩ := exists_eq_map_mul_rep_mul stdEmbFin (D.columnLevel 0) Quotient.out_eq g
  erw [levelSpace_smoothFormRep_apply H, one_smul, mul_assoc, mul_assoc, weylGauge_embFin,
    ← weylGauge_embFin, ← φ.2.2 (γ c.out), ← weylGauge_mul _ (inv_mem (mul_mem (h' c.out)
    (mem_integralAbove_of_inclGL_eq (D.atPlaces_conj_mem_mirabolic k).choose_spec.2))), weylGauge,
    show ιₚ ∘ _ = schur _ (fun _ ↦ diagonal (1 ⊕ᵥ D.N)) *ᵥ (ιₚ <| y ⟨c, ·⟩) by
    ext; simpa [schur_diagonal, prod_pow_eq_pow_sum] using congr(ιₚ ($e (c, _))).symm]
  simp [weylRep, lastEntry, mul_assoc, d, adeleExtension_map_diagN, -coe_units_inv]
  grw [norm_schur_mulVec_le .refl, pi_norm_le_iff_of_nonempty]; use (y ⟨c, ·⟩ |>.2)
  intro; split <;> simp [← map_inv, diagonal_apply, apply_ite (‖·‖ ≤ 1), norm_p_lt_one.le,
    NeZero.ne]
  use t (.inr ()) * (D.ϱ + 1 + 1), ?_
  induction _ + 1; simpa [d] using! h D.piPlaces
  simp [pow_succ', mul_add, pow_add] at *
  use .trans ‹_› ((h D.nonInducedPlaces).comap _ (fun _ H ↦ ?_) (by tauto)); use
    D.fourierOp_mem_column H.1; intro
  conv in fourierOp .. => unfold fourierOp
  simp; apply weylGauge_sum_le; simp; intros
  erw [weylGauge_smul, P.norm_map_psi₀,
    ← weylGauge_mul _ (mem_integralAbove_of_inclGL_eq (l.atPlaces_embedGL _).symm)]
  simpa [conjEmbedGL, ← mul_assoc] using! H.2 (_ / D.diagPointN 0)
  have s a b : t a = t b := by simpa [t, schur_diagonal, prod_pow_eq_pow_sum, swap_apply_eq_iff,
    ← submatrix_mul, Fintype.sum_prod_type] using det_mul_comm (schur D.κ fun _ ↦ (diagonal (if · =
    a then (2 : ℤ) else 1)).submatrix id (swap a b)) (schur _ fun _ ↦ submatrix 1 (swap a b) id)
  have a : ∑ a, t a ≤ _ := sum_comm_cycle.ge.trans (by grw
    [(sum_tableauWeight · · |>.trans_le (sum_height_mul_kappa_le ..))])
  simp [finrank_levelSpace_smoothFormRep, classAut_columnLevel_eq_bot, ↓card_X, n, ← @Nat.cast_le ℝ,
    ← le_div_iff₀', -Fintype.card_pi, -MonoidHom.coe_range, s _ (.inr ())] at *
  grw [a]; field; use D.le_of_hasLogBound

lemma Data.charUnramifiedAt_rankTwist_of_N_mem {P} (D : Data P) ϑ j n [Fintype n] w (h :
  ↑D.N ∈ w.1) : CharUnramifiedAt (rankTwist (D.chainChar ϑ j) n).baseChange.finPart w := by apply
  AutChar.HasWeight.charUnramifiedAt <;> simp [liftTamePart, not_isChosen_of_N_mem, ϑ.5,
  (D.levelNorm_mem_and_notMem_of_mem_Q ϑ ∘ .inl).mt, *, TameChar.pow]

/-- For the character ν of lift i and twist ϑ, applying `rankTwist` for X_j and then
`AutChar.spaceChar` in rank |X_j| gives the Hecke character x ↦ ν(x/x̄). -/
lemma Data.spaceChar_rankTwist {P} (D : Data P) ϑ j i :
  (rankTwist (D.chainChar ϑ i) (D.X j)).spaceChar (Fintype.card (D.X j)) =
  (D.chainChar ϑ i).baseChange := _root_.spaceChar_rankTwist (Even.two_dvd (by grind [card_X, n]))
end

section
/-! An approximate projector from averages over generic matrices. Conjugation-invariant linear forms
on polynomials in a generic Levi matrix split evaluation at the identity by weight, up to a
controlled power of p, and the resulting approximate projector onto forms nearly obeying the
Frobenius inequalities shows that the two halves of the Hecke operator pair almost perfectly. The
Schur algebra as dual of polynomials in a generic matrix, spanned by finite points in low degree,
and truncation by weights are known. Related work: Benson–Doty, Schur–Weyl duality over finite
fields, 2009; Green, Polynomial representations of GL_n, 1980; Donkin, On Schur algebras and related
algebras I, 1986.

Part of: A Frobenius-twisted Hecke operator has small elementary divisors (see
New.Columns.TwistedHeckeType).

This file: Twisted Hecke operator has small elementary divisors; approximate projector; Smith form
of ends. -/

namespace TwistingData

open MvPolynomial Matrix IsLocalRing Function Module PiTensorProduct Finset Fintype Kronecker Equiv
  ClassMean Ideal Pointwise MatMul
attribute [local simp] dotProduct prod_prod_type prod_eq_zero_iff mul_sum sum_mul vecMul
  sum_prod_type mulVec polyOfCoeffs Matrix.map IsConcreteLE.le_iff Submodule.mem_sup_left
attribute [local simp ←] map_mul kroneckerPi_mul Matrix.mul_apply
attribute [-simp] Matrix.one_apply _root_.map_inv
attribute [local grind] dvd_trans deepIndicator twoBlock pow_mul pow_dvd_pow dvd_mul_of_dvd_right
  dvd_def
variable {N k n W O X E H} [NeZero N] [CommRing W] [IsLocalRing W] [CommRing O] [IsDomain O]
  [ValuationRing O] (T : TwistingData N W O) (c : ℕ) {a r : Fin k} [Fintype X]
  [Fintype E] (Q M : Matrix (X × (ZMod N → Monomials (Fin k) n)) E O) (R β : type_of% Qᵀ)

omit [Fintype E] in
lemma card_le_finrank_translatesIn {s G B} (h : ∀ j ∈ s, ∀ i, (R * Q) i j = ite (i = j) 1 0)
    (hs : ∀ j ∈ s, ∀ x, Q.col j ∘ (x, ·) ∈ T.translatesIn n G (maximalIdeal O) B) :
    #s ≤ finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) :=
  card_coe s ▸ LinearIndependent.fintype_card_le_finrank (b := fun j x ↦ ⟨residue O ∘ Q.col j ∘ (x,
  ·), by simp_all [translatesIn, letterRep_map, ← map_sum]⟩)
  (linearIndependent_iff.2 fun g hg i ↦ by simpa [mul_sum _, sum_comm, mul_left_comm, h,
  ← mul_sum, ← map_sum] using congr(∑ y, residue O (R i y) * ($hg y.1).1 y.2))

/-- Let RQ = 1, w be a non-unit and βM ≡ a mod aw. If Qu − Mv = aw·F forces each F(x, ·) into
`TwistingData.translatesIn` n G 𝔪 B, then im(βQ) + z·O^E has index (`IndexDvd`) dividing a^{|E|}z^l,
with |E| + l ≤ |X|·dim of that condition over the residue field. -/
lemma of_pairing a z {w G B} (hR : R * Q = 1) (hw : ¬IsUnit w) (h : ∀ i j, a * w ∣
    (β * M - a • 1 :) i j) (hn : ∀ u v F, Q *ᵥ u - M *ᵥ v = (a * w) • F → ∀ x, F ∘ (x, ·) ∈
    T.translatesIn n G (maximalIdeal O) B) : ∃ l, card E + l ≤
  finrank (ResidueField O) (X → (map (residue O) T).translatesIn n G ⊥ B) ∧
  IndexDvd ⊤ (.map (β * Q).mulVecLin ⊤ ⊔ z • ⊤) (a ^ card E * z ^ l) := by
  obtain ⟨⟨U, V⟩, _, G, _, t, e⟩ := isValuationPair_top.smith_normal_form ((Q * R * M - M) * R)
  rw [← G.mul_inv_eq_iff_eq_mul] at e
  choose s _ using (ValuationRing.cond (a * w) <| t ·)
  choose W _ using h
  let A := β * U * (diagonal (a • w • s) - diagonal t)
  refine ⟨_, (T.card_le_finrank_translatesIn (Q.fromCols U) (R.fromRows (V - V * Q * R))
    (by simp_all [V.mul_apply, Q.mul_apply, one_apply, by
    simpa [← ext_iff, ← Matrix.mul_assoc, hR, or_iff_not_imp_right] using
      congr(R * $e)]) ?_).trans_eq' (card_disjSum _ {i | t i ∣ a * w ∧ t i ≠ 0}), .trans
    (.of_det_dvd (A := A * G.1 * Q + β * Q * R * M) ?_ ?_) (.map (.of_det_dvd (by rw [det_diagonal,
    ← prod_const, prod_filter]) le_rfl) A.mulVecLin le_rfl (le_sup_of_le_right ?_))⟩
  simpa using ⟨fun j ↦ hn (Pi.single j _) 0 _ (by aesop), fun _ _ ⟨c, h⟩ _ ↦ hn _ _ _ (by
    simpa [-mulVec_smul, h, ↓ ← mulVec_mulVec, ↓diagonal_mulVec_single,
      ↓op_smul_eq_smul] using! congr($e *ᵥ Pi.single (_, _) c))⟩
  convert ((1 + w • (of W + β * U * diagonal s * G.1 * Q)).det_smul a).dvd.trans _
  ext; simp_all [A, ← e]
  grind
  simp_all [↓det_one_add_smul w, map_mul, ← residue_ne_zero_iff_isUnit, -residue_eq_zero_iff]
  simp [Submodule.add_mem_sup, -mulVec_mulVec]
  simpa using (⟨A *ᵥ ·, by simp [-sub_mulVec, A, funext_iff, -Matrix.mul_assoc]; grind⟩)

variable [CharZero O]

/-- Let a<r, all r-depths ≤x, e↦(s(e), g_e⁻¹𝒫) onto, 𝒫 the two-block parahoric. The matrix of
φ↦(w^{depth}ρ(g_e)φ(s(e)))_e is Qd, Q left invertible, det d ∣ w^{|X|∑_{τ<x}dim V_τ} (V_τ: residue
forms with all GL_k(W)-translates of depth ≥τ), and values of Q satisfy `TwistingData.excessCond`
modulo w^c at each e for h≥2c. -/
lemma exists_depth_factorization (ha : a < r) {x} (hm : ∀ β, T.depth k n r β ≤ x) (s : E → X) (g : E
  → _) (hs : Surjective fun e ↦ ((s e, ⟦(g e)⁻¹⟧) : X × _ ⧸ parahoric W (twoBlock k r))) : ∃ (Q d :
  Matrix _ _ O) (R : type_of% Qᵀ), (Q * d = of fun (e, α) (x, β) ↦ ite (s e = x) ((diagonal (T.w ^
  T.depth k n r ·) * T.letterRep n (g e) :) α β) 0) ∧ d.det ∣ T.w ^ ∑ τ ∈ range x,
  finrank (ResidueField O) (X → (map (residue O) T).deepForms k n r τ) ∧ R * Q = 1 ∧
  ∀ j e {h : ℝ}, 2 * c ≤ h → (Q *ᵥ j) ∘ (e, ·) ∈ T.excessCond n a r (span {T.w ^ c}) h := by
  set J := of _
  have hJ φ e : (J *ᵥ φ) ∘ (e, ·) = _ *ᵥ φ ∘ _ := funext (by simp [J, -diagonal_mul]; tauto)
  have hf {z φ} (h : ∀ y, z ∣ (J *ᵥ φ) y) x γ β :
      z ∣ T.w ^ T.depth k n r β * (T.letterRep n γ *ᵥ φ ∘ (x, ·)) β := by
    obtain ⟨e, rfl, he⟩ := by simpa [QuotientGroup.eq] using hs (x, ↑γ⁻¹)
    choose A hA using show ∀ s i j,
      T.w ^ T.deepIndicator r (j, s) ∣ T.w ^ T.deepIndicator r (i, s) * T.letterMatrix s
      (g e * γ⁻¹)⁻¹ i j by grind [p_dvd_letterMatrix_of_mem_parahoric, inv_mem, w_sq]
    rw [← mulVec_diagonal (_ ^ T.depth k n r ·), ← inv_mul_cancel_right γ, map_mul, mulVec_mulVec, ←
      mul_assoc, (?_ : diagonal _ * _ = kroneckerPi (symPowMatrix n ∘ of ∘ A) * _), mul_assoc,
      ← mulVec_mulVec, ← hJ]
    exact dvd_sum (by grind)
    simp [letterRep, diagonal_pow_depth]; congr! 3
    ext; simpa [mul_comm] using hA ..
  have ⟨U, _, D, _, e, _⟩ := isValuationPair_top.hermite
    (.ofSurjective _ ((Prod.fst_surjective.comp hs).prodMap surjective_id)) J
  obtain ⟨K, -, P, -, t, rfl⟩ := isValuationPair_top.smith_normal_form D
  have h0 i := @hf (t i) (P.2ᵀ i) (by simp [e, ← Matrix.mul_assoc])
  choose t' ht using fun i ↦ by simpa using show t i ∣ (P.1 * T.w ^ x • P.2) i i from (dvd_sum
    fun ⟨y, β⟩ _ ↦ by grw [h0 i y 1 β, hm]; simp [-mulVec])
  refine ⟨_, _, U.2.submatrix _ id, e.symm, ?_, by
    simpa [← submatrix_mul] using submatrix_one_embedding _, fun j _ _ _ l hl β ⟨i, h⟩ ↦ ?_⟩
  simp [-finrank_pi_fintype, -prod_prod_type]
  grw [prod_dvd_prod_of_dvd _ (T.w ^ #{τ ∈ range x | ¬t · ∣ T.w ^ τ}) fun i _ ↦ by
    set m := #_
    grind [@card_le_card _ (range (m + 1))]]
  erw [prod_pow_eq_pow_sum, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  gcongr; exact T.card_le_finrank_translatesIn P.2 P.1 (by simp [one_apply]) fun i hi y γ _ β hβ e ↦
    (mem_filter.1 hi).2 ((e.dvd_mul_right.1 (h0 ..)).trans (pow_dvd_pow _ hβ.le))
  -- `J` takes `P⁻¹ t' K⁻¹ j` to `w ^ x` times the value at `j` of the primitive factor
  have hφ := congr($e *ᵥ P.2 *ᵥ diagonal t' *ᵥ K.2 *ᵥ j)
  simp [← mul_assoc (diagonal t), ← ht, ← smul_one_eq_diagonal] at hφ
  rw [mem_span_singleton, ← mul_dvd_mul_iff_left (pow_ne_zero x T.w_ne_zero), ← pow_add, ←
    smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul, ← Pi.smul_comp, ← hφ, ← mulVec_mulVec, hJ,
    mulVec_mulVec, Commute.left_comm, ← map_mul, ← mulVec_mulVec, mulVec_diagonal]
  -- a term least for valuation plus weight `ω` among all translates of `F` weighs at least `x`
  set F := _ ∘ _
  let ω y := T.deepIndicator r y - T.excessWeight i a r y / 2
  choose l L g G using fun γ ↦ @Nat.exists_not_and_succ_of_not_zero_of_exists (fun l ↦ ∃ g, ¬T.w ^
    l ∣ (T.letterRep n g *ᵥ F) γ ∨ ⌈x - (exponentOf γ).weight ω⌉₊ < l) (by simp) ⟨_, 1, .inr .refl⟩
  let ⟨γ, H⟩ := (@Finite.exists_min _ _ _ ⟨β⟩ _ fun γ ↦
    l γ + (exponentOf γ).weight ω).imp fun _ M g δ ↦
    (pow_dvd_pow _ (Nat.ceil_le.2 (sub_le_iff_le_add.2 (M δ)))).trans (by_contra (L δ ⟨g, .inl ·⟩))
  have := (G γ).imp_left fun hg ↦ And.intro (fun d : _ ≤ x ↦ hg (by
    grw [← mul_dvd_mul_iff_left (pow_ne_zero _ T.w_ne_zero), ← @hf (_ ^ x), ← pow_add, ← d]
    simp [hφ, -mulVec])) (T.root_lemma i ha.ne 0 ω _ (f := polyOfCoeffs (T.letterRep n (g γ) *ᵥ F))
    (fun g _ ↦ by simpa [↓polyAction_polyOfCoeffs, -mulVec] using
    (_root_.sum_mem fun _ _ ↦ monomial_mem_gaussFiltration (H ..)))
    (by simpa [coeff_sum]) rfl (by simp [ω, deepIndicator]; grind [excessWeight_mem_Icc]))
  grw [← H, ← pow_add, pow_dvd_pow]
  simp [← add_assoc, ω, depth, Finsupp.weight_eq_sum, mul_sub, mul_div, ← sum_div] at this h ⊢
  rify at *; grind [Nat.le_ceil]
  simp [commute_iff_eq, letterRep, diagonal_pow_depth]; congr! 3
  ext; simp [letterMatrix, -coe_units_inv]; clear * - hl; grind [hl _, inv_mem hl _,
    transpose_apply]

/-- Tensor product of linear forms on polynomial rings: there is a multilinear S into linear
forms on R[X_{ι×σ}] with S(l)(∏_j f_j(X_{j,·})) = ∏_j l_j(f_j) for all l_j and f_j, ι
finite. -/
lemma _root_.exists_tensor_dual ι σ R [Fintype ι] [CommRing R] : ∃ S :
    MultilinearMap R (fun _ : ι ↦ Dual R (MvPolynomial σ R)) (Dual R (MvPolynomial _ R)), ∀ l
    (f : _ → _), S l (∏ j, rename (j, ·) (f j)) = ∏ j, l j (f j) := ⟨((aeval fun (i, v) ↦
    singleAlgHom i (X v)).toLinearMap.dualMap ∘ₗ dualDistrib).compMultilinearMap (tprod R), by
  simp [aeval_rename, comp_def, ← comp_aeval, -singleAlgHom_apply]; simp [← tprod_prod]⟩

/-- Projector modulo w^c. For p a non-unit, a+1 = r, 2ℓ = N, Nnk(ℓ+2)+n+k < P^ℓ there are b, Z with
all ZF in `TwistingData.excessCond` at θ, y·diag(b)ZF ≡ p^{(k+k²)o₀N²} y·F for y in it at θ−(4c+2),
and diag(b)ρ(γᵀ) = ρ(γ)ᵀdiag(b).

An approximate projector from averages over generic matrices. -/
lemma exists_projector (hp : ¬IsUnit (T.p : O)) (ha : a + 1 = r.1) {ℓ} θ (e : ℓ + ℓ = N)
    (h : N * (n * (k * (ℓ + 2))) + n + k < T.P ^ ℓ) : ∃ b Z, (∀ F, Z *ᵥ F ∈ T.excessCond n a r
    (span {T.w ^ c}) θ) ∧ (∀ y ∈ T.excessCond n a r (span {T.w ^ c}) (θ - (4 * c + 2)), ∀ F,
    T.w ^ c ∣ y ⬝ᵥ (b * Z *ᵥ F) - T.p ^ ((k + k ^ 2) * (T.o₀ * N) * N) * y ⬝ᵥ F) ∧
    ∀ γ α β, b β * T.letterRep n (transposeGL γ) β α = b α * T.letterRep n γ α β := by
  obtain ⟨⟨S, hS⟩, q, b₀, hb, hx⟩ := exists_tensor_dual (ZMod N) (Fin k × Fin k) O, e ▸ Nat.pow_add
    .. ▸ Nat.mul_le_mul_right _ h, exists_invariant_diagonal_form (Fin k) T.prime hp (T.o₀ * N)
  let b (β : ZMod N → Monomials _ n) := ∏ s, b₀ (β s).1
  choose b' hb' using fun β ↦ (prod_dvd_prod_of_dvd _ _ fun s _ ↦
    Dvd.intro_left _ (hb _ (by grind [Monomials.degree_eq])).symm : b β ∣ _)
  have hν l f : S l f = ∑ ν ∈ f.support, f.coeff ν * ∏ j, l j (monomial (ν.curry j) 1) :=
    (congrArg _ f.as_sum).trans (by simp [← hS, monomial_eq, C_mul'])
  let Z := ((LinearMap.mapMatrixLinear O).flip
    (T.frobOperator r ℓ n T.frobGenericMatrix)).compMultilinearMap S
  have key i {m} (l : type_of% m) {g y F} (hg : g ∈ _) (e : ∀ j f, m j f = l j (conjSubst (T.ι j) g
    f)) (H : ∀ β _ ν, univ.prod _ = (0 : O) ∨ _) : y ⬝ᵥ Z m *ᵥ F ∈ span {T.w ^ c} := (by
    rw [(congr(.map _ $(show _ = _ ∘ₗ (aeval _).toLinearMap by
      ext; simp [single_eq_monomial, hν m, e]
      simp [← hS, monomial_eq])) : Z _ = .map (.map ((T.map C).frobOperator _ _ _ _) (eval₂Hom C
      fun (j, v) ↦ rename (j, ·) (conjSubst (T.ι j) g (X v)))) (S l)), frobOperator_map _ _ hg]
    simp_rw [letterRep_map, map_C_mul_mul_C, ← mulVec_mulVec, dotProduct_mulVec y, funext (hν l)]
    exact sum_mem fun β _ ↦ dite _ (mul_mem_right _ _) fun q ↦ mem_span_singleton.2 (.mul_left
      (dvd_sum fun _ _ ↦ .mul_right (dvd_sum fun ν _ ↦ (H β q ν).elim (· ▸ by simp) (And.elim
      (T.pow_dvd_coeff_conj_frobOperator ha i (by lia) (by lia) g (by simp [letterConj, conjSubst,
      linSubst, ← C_mul', map, map_mul,
      mul_apply, mul_assoc, mul_comm (X _)])) · |>.mul_right _)) _) _))
  choose κ h0 h2 h1 h3 using fun P j ↦ exists_mean (twoBlock k r) (T.ι j) T.prime hp (T.o₀ * N)
    (by grind) (D := N * (n * (k * ((ℓ + 2) * T.P ^ ℓ)))) (by grind [card_residueField])
    (T.indexWeight ℓ a r) (P ∨ θ - (2 * c + 1) < ·)
  use b, Z (-κ False + κ True) * diagonal b', fun F g hg β ⟨i, hi⟩ ↦ mulVec_mulVec F (Z _) _ ▸
    key (i - ℓ) (-κ False + κ True) hg (by simp [h0 _ _ g hg]) (by
    simp [one_apply]
    clear * - h1 h2 hi; grind [zero_mem]), fun y hy F ↦ ?_, ?ρ
  have := ?ρ
  let Y := (dotProductBilin O O (b * y) ∘ₗ toLin'.1.flip (b' * F)).compMultilinearMap Z
  have hz : Z (κ True) = (_ :
    O) • (T.frobOperator r ℓ n T.frobGenericMatrix).map
      (eval (vec (1 : Matrix (Fin k) (Fin k) O) ·.2)) :=
    ext fun _ _ ↦ by
    simp [Z, hν, eval_eq']; congr! 1
    simp [h1, T.degree_le_of_coeff_frobOperator (mem_support_iff.1 ‹_›), eval_monomial]
    rw [mul_left_comm]
  simp [↓T.frobOperator_map _ (one_mem _), frobOperator, one_apply,
    T.prime.ne_zero, ite_apply, ← diagonal.eq_1, @eq_comm (Fin k)] at hz hb'
  convert (mem_span_singleton.1 (sum_mem (Finset.induction (by simp) fun s t _ _ _ ↦ ?_))).trans
    (sub_eq_of_eq_add' ((Y.map_add_univ (-κ False) (κ True)).trans
    (sum_eq_add_sum_compl ∅ _))).symm.dvd
  simp [Y]; ac_rfl; simp [Y, hz, add_mul]; grind
  rw [piecewise_insert]
  refine neg_mem (Submodule.mem_span.1 (h3 _ s) (.comap (Y.toLinearMap _ s) (span _)) fun
    | _, ⟨u, h, γ, e, rfl⟩ => And.elim (key s (update (t.piecewise (-κ False) (κ True)) s γ) h) ?_)
  have z β := (mul_mem_left _ (b β) <|
    hy (transposeGL u⁻¹) (swap (inv_mem h · · ·.symm)) β ⟨s + ℓ, ·⟩)
  simp [update, piecewise, DFunLike.ite_apply] at z ⊢; clear * - z e h0 h2 h this; grind
  simp [letterRep, kroneckerPi, b, ← prod_mul_distrib]
  congr! 1; erw [mul_comm, letterMatrix]; bound

/-- Elementary divisors of the twisted Hecke operator (AF)(c) = ∑_b (u_e ⊗ (ρ(g_e) p^{depth}
ρ(γ_b))ᵀ) F(src e), e = (c,b), the γ_b representing the cosets 𝒫γ of the parahoric. Assume p is a
non-unit, `HeckeSizes`, and e ↦ (src e, 𝒫g_eᵀ) injective. If Yf = fA, then Y has type
(z + κm + y)|X||I| at m on im f (`HasType`: Y preserves M = im f, and YM + p^m M has index dividing
p^l for some l at most this number).

A Frobenius-twisted Hecke operator has small elementary divisors. -/
lemma hasType_twisted_hecke (hp : ¬IsUnit (T.p : O)) {r ℓ κ y z} (big : HeckeSizes T.P T.o₀ N k n r
  ℓ κ y z) {I M : Type} [Fintype H] [Fintype (_ ⧸ parahoric W (twoBlock k r))] [Fintype I]
  [AddCommGroup M] [Module O M] (f : (X → I → O) →ₗ[O] M) {Y : End O M} (src :
  X × _ ⧸ parahoric W (twoBlock k r) → X) (g : _ → GL (Fin k) W) (u : _ → GL H O) (J : I ≃ _ × H)
  (hs : Injective fun e ↦ ((src e, ↑(transposeGL (g e))⁻¹) : X × _ ⧸ parahoric W (twoBlock k r)))
  (hY : ∀ F, Y (f F) = f fun c i ↦ ∑ b, ∑ j, u (c, b) (J i).2 (J j).2 * (T.letterRep n (g (c, b)) *
  diagonal ((T.p : O) ^ T.depth k n r ·) * T.letterRep n b.out⁻¹ :) (J j).1 (J i).1 * F (src (c, b))
  j) m : HasType ↑T.p f.range m Y ((z + κ * m + y) * (Nat.card X * Nat.card I)) := by
  have ⟨_, _, _, _, e, h1, _⟩ := big
  set c := 2 * _ + 2
  let S := T.map (residue O)
  have ha : @Fin.val k ⟨r - 1, by lia⟩ + 1 = @Fin.val k ⟨r, by lia⟩ := by lia
  obtain ⟨hu, _, x, hm⟩ := (T.w_sq ▸ hp) ∘ .pow 2, CharP.of_eq_zero S.prime
    ((residue_eq_zero_iff _).2 hp), Finite.exists_le (T.depth k n r)
  obtain ⟨U, U', ⟨b, Z, hZ, hZ', hρ⟩, ⟨Q, d, R, hj, h₀, hR, hQ⟩, Q', d', R', j', h₁, hR', hQ'⟩ :=
    S.index_mul_finrank_excessCond_le ha big, S.sum_finrank_deepForms_le big x, T.exists_projector c
    hp ha y e h1, T.exists_depth_factorization c ha.le hm _ _ ((prodAssoc H ..).symm.surjective.comp
    (surjective_id.prodMap hs.bijective_of_finite.2)), T.exists_depth_factorization c ha.le hm (.map
    id (·.1)) (·.2.2.out⁻¹) (⟨prodAssoc H X _ ·, by simp⟩)
  obtain ⟨l, L, key⟩ := T.of_pairing Q (blockDiagonal (u · |>.2) ⊗ₖ Z * R'ᵀ) R
    (Q'ᵀ * blockDiagonal (u · |>.1) ⊗ₖ diagonal b) (T.w ^ _) (T.p ^ m) hR hu (fun i j ↦ by
    grw [← pow_succ, one_le_two]
    convert univ.dvd_sum fun y _ ↦ hZ' _ (hQ' (Pi.single i 1) y (by bound)) (R' j ⟨y, ·⟩)
    simp [← transpose_eq_one.2 hR', ← (_ ⊗ₖ _).mul_assoc, ← mul_kronecker_mul, w_sq,
      ← blockDiagonal_mul, mul_apply, diagonal, blockDiagonal_apply, one_apply, mul_assoc, pow_mul])
      fun v _ _ h x γ hγ β hβ e ↦ by simpa [← pow_succ, pow_dvd_pow_iff T.w_ne_zero hu, c, e,
      mem_span_singleton, Pi.smul_comp, -mulVec] using (Set.mem_of_eq_of_mem (congr($h
      ∘ (x, ·)).symm.trans (by
      rw [← mulVec_mulVec, ← (vec_bijective.2 (R'ᵀ *ᵥ _)).choose_spec, kronecker_mulVec_vec]; ext
      simp; rfl)) (sub_mem (hQ v x (by bound)) (hZ _)) γ hγ β hβ)
  let ε := .funCongrLeft O O ((((prodComm ..).trans (J.prodCongr (.refl X))).trans
    (prodAssoc ..)).trans (prodComm ..)) ≪≫ₗ .curry ..
  have := (IndexDvd.of_det_dvd (d'.det_transpose ▸ h₁) le_sup_left).comp le_top
    (key.comp le_top (.of_det_dvd h₀ le_sup_left))
  simp_rw [mul_left_comm, ← mul_pow, ← sq, pow_mul, w_sq, ← pow_mul, ← pow_add] at this
  refine ⟨by simp [hY], _, ?_, this.map (f ∘ₗ ε) (by simp) ?_⟩
  grw [← (by bound : c / 2 ≤ y)]
  simp [Subgroup.index, card_congr J, c, ← mul_sum] at L U U' ⊢; rify at L
  linear_combination (norm := linarith!) ↑m * L + card X * card H * (↑m * U + U')
  simp [← LinearMap.range_comp, -IsConcreteLE.le_iff]
  refine le_sup_of_le_left fun | _, ⟨F, rfl⟩ => ⟨ε ((b ·.2) * F), ?_⟩
  simp [hY]; erw [hj, j']; congr!
  simp [ε, ← J.symm.sum_comp, @sum_prod_type_right _ _ H, ← mulVec_mulVec, sq,
    mul_apply, blockDiagonal, diagonal, ← w_sq, mul_pow, ite_and]
  congr!; rw [sum_comm_cycle]; clear * - hρ; grind
end TwistingData
end

section
/-! A Frobenius-twisted Hecke operator has small elementary divisors. An integrally scaled Hecke
operator above p, on forms at tops linked in a circle by Frobenius and conjugation, has elementary
divisors of small mean exponent outside a small share, so using it once per theta lift to keep
divisibility when the partner of a top is a top costs little index. Integral scalings of Hecke
operators and, for GL(2) over Q and regular p, slopes of T_p of at most about k/(p+1) are known.
Related work: Arsovski, Limiting measures of supersingularities, 2019; Liu–Truong–Xiao–Zhao, Slopes
of modular forms and geometry of eigencurves, 2023; Fakhruddin–Pilloni, Hecke operators and the
coherent cohomology of Shimura varieties, 2021.

Trading denominators at the level prime for a column operator. On columns ramified at the level
prime N, a chain of lifts whose data have denominator N equals a scalar of controlled denominator
times a chain with data given mod N, applied after a power of a Gauss-sum-weighted Hecke operator at
N, so the chain loses little divisibility at N on a submodule of small index. Hecke-type operators
passing through a theta lift, for data with ramified characters at a split prime, are known. Related
work: Z. Liu, Test Schwartz functions at p for theta lifts of Hida families, 2025; Rallis,
Langlands' functoriality and the Weil representation, 1982.

This file: Valuation at N of character factors and of data given modulo N. Chain with denominators N
equals scalar times chain mod N after Gauss-sum operator. Valuation of the restricted chain at the
level prime N on a submodule. Scaled Hecke operator on algebraic forms has elementary divisors of
small mean exponent. -/
seal Finset.univ Finset.sum Finset.prod

open Ideal IsSplitLevel QuadField Matrix NumberField Parameters Real Ideal.Quotient Data Finset
  Space
variable {P} (D : Data P) (ϑ) [PadicPlace D.N] [l : IsSplitLevel D.nonInducedPlaces D.N]

lemma Data.norm_detCharAt_diagN_le {i} (hi : i ≤ 2 * D.m) k j S : ‖ιₚ (detCharAt
  (D.chainChar ϑ i).baseChange k (l.diagN (D.InitIndex j) S))‖ ≤ D.N ^ (2 * D.f * D.b) := by
  grw [norm_detCharAt_diagN_anti (n' := InitIndex _ j) bot_le, ← atPlaces_embedGL (diagN ..)]
  simp [detCharAt, -atPlaces_embedGL]
  erw [D.hasWeight_liftChar.norm_padic_eq_prod ιₚ _ (unitary _).one_mem.2,
    ← G.det_of_supportedOn (s := 1) disjoint_star
    (embedGL_mem_supportedOn _), mul_right_comm, rpow_mul_natCast (by simp), ← Finset.prod_const]
  gcongr
  erw [G.det_snd, ← star_star (det _), adeleExtension_star, ← det_conjTranspose,
    ← U.inv_val_eq_conjTranspose, RingHom.map_det, congr($(adeleExtension_map_diagN ..)⁻¹.1.det)]
  split <;> grw [← D.w_le_two_mul_b hi τ] <;> simp [norm_p_eq_inv, NeZero.one_le, one_le_pow₀]

/-- For ι : ℂ → ℂ_N and j < m, cut the j-th datum of x by the indicator of integral matrices
with last column ≡ the last basis vector at the primes `Data.nonInducedPlaces`. Its kernel
multiplies ι-gauges by at most N^{fb}. -/
lemma Data.name_lastColDatum_mem_raises x {j} (hj : j < D.m) :
  l.name (lastColDatum lastBasisVector) (translateDatum x j) ∈ (liftKernel ϑ j).raises 1 1
  (D.N ^ (D.f * D.b)) := let q := algebraMap (𝓞 P.K) (_ ⧸ (D.inducedPlace 1).1)
  have z x : q x = 0 ↔ ‖ιₚ x‖ < 1 := phi_algebraMap .. ▸ eq_zero_iff_mem.trans (mem_placeOfEmb ..)
  have ⟨c, _⟩ := mem_multiples_of_prime_card (g' :=
    q (c₀ _)) (by apply q_eq_of_modEq_one D.N_modEq_one (p_mem_inducedPlace ..)) one_ne_zero
  let a := c₀ P.d - c
  have o : 1 ≤ ‖ιₚ (star ↑a * P.d)‖ := by simpa using (z (star a * P.d)).2.mt (by simp [a]; grind
    [two_mul, map_sqrtNegDInt_sq q, (FinPlace.charP_quotient _ (D.p_mem_inducedPlace 1)).1,
    not_dvd_N₁_mul_d_of_modEq_one D.N_modEq_one])
  have ⟨𝔪, hS, hm⟩ :=
    exists_modulus_places_eq (ι := D.nonInducedPlaces) (w := (↑)) (by simp [star_notMem])
  have := (congrArg _ (by simp [IsSplitLevel.name, lastColDatum,
    IsSplitLevel.liftFn_eq_residueDatum, ← _root_.liftFn_eq_residueDatum hS, *]; rfl)).subst
    ((isAdmissibleComb_name _ 𝔪 (q := 1) (B := 0) (hm (by simpa using IsSplitLevel.natCast_mem)) (by
    grind [one_mem, zero_mem]) id rfl ⟨algebraMap (𝓞 D.E) _ (star (algebraMap _ _ a)), by
    simpa [eq_zero_iff_mem] using hm (by
      simp; simp [nonInducedPlaces, inducedPlace]; intro; erw [phi_algebraMap]; grind [map_natCast])
    ⟩).smul_mem (by simp) fun _ e ↦
    finHeisOp_mem_standardData (fun i w _ ↦ by simpa [one_notMem] using! e i w) (by
    erw [hS, Space.projOn_finHeisOp _ (by simp [intVacuum]), boxIndicator_apply]; split <;> simp
    use Submodule.subset_span ⟨_, fun i w _ ↦ mul_mem (w.coe_algebraMap_mem _ _
      (algebraMap _ _ a)) (idem_mul_mem_Ô.1 (by tauto) w (by simp_all [l.4])), rfl⟩))
  (inv_smul_smul₀ (by simp [NeZero.ne]) _).subst
    (Kernel.smul_mem_raises _ (mem_raises_of_standardData (by norm_num [·, a] at o) this) (by
  grw [norm_star_piG_le_one, ← o, absNorm_span_natCast, RingOfIntegers.rank,
    finrank_eq_two_mul_card_infinitePlace, ← pow_mul]
  simp [norm_p_eq_inv, ← rpow_natCast, ↓card_X, D.N_prime.one_lt]
  grw [D.n_mono hj, n_mono _ hj.le]; use D.le_of_hasLogBound))

seal liftKernel Kernel.lift SmoothForm

/-- Some t with ‖ι t‖ ≤ N^{4fb(ϱ+1)} serves all data v_j and ramified columns φ: the chain of ϱ+1
pairs `Data.pairTranslates` of projected v_j at φ is t times the chain with data ω(d_j,
d_{j+1})(𝐛 ⊗ v_j) at F^{ϱ+1}φ (`IsSplitLevel.lastColDatum` of the last basis vector,
`Data.diagPointN`, `IsSplitLevel.fourierOp`). -/
lemma Data.chain₂_pairTranslates_eq_smul_chain {P} (D : Data P) [PadicPlace _] ϑ (l :=
  D.isSplitLevel_nonInducedPlaces) : ∃ t, ‖ιₚ t‖ ≤ D.N ^
  (2 * D.m * D.f * D.b) ∧ ∀ᵉ (v : ∀ _, _) (φ ∈ D.ramifiedColumns),
  chain₂ (D.liftKernel ϑ) (D.pairTranslates (projOnFinPart _ D.piPlaces <| v ·)) (D.ϱ + 1) φ = t •
  chain (D.liftKernel ϑ) (fun j ↦ (D.liftKernel ϑ j).ω (D.diagPointN j, D.diagPointN _) <| l.name
  (lastColDatum lastBasisVector) (v j)) _ ((fourierOp (D.nonInducedRep 0) ^ (D.ϱ + 1)) φ) := by
  refine ⟨_, ?_, fun v φ a ↦ have o j f g k := eq_inv_smul_iff.2 (congr($(D.liftKernel_ω ϑ j) _ _
    ).trans (l.pairWeilFinite_name g f _ _ k (v j))).symm
    have w j a b Φ φ := by simpa using
      (D.liftKernel ϑ j).lift_equivariant a b Φ (smoothFormRep _ _ a⁻¹ φ)
    .trans (congrArg (compUpTo · _ _) (by ext; simp [TensorChain.liftInPairs,
      l.translateSum_eq_sum_name D.isSplitLevel_piPlaces, conjEmbedGL, diagN_eq_sdiff_mul
      D.piPlaces, pairTranslates, lastColDatum, charDatum, smul_sum, smul_smul, w,
      by simpa [↓spaceChar_rankTwist] using And.intro (o · · · 1) (o · · 1 ·⁻¹)]; rfl))
      (compUpTo_pairs_eq_smul D.nonInducedRep (L := fun j ↦ (D.liftKernel ϑ j).lift ∘ₗ _ ∘ₗ .applyₗ
      _ ∘ₗ name) (fun j ↦ ⟨fun b c f ↦ by simp [↓← funext (liftIntegralFn_mul (M := ·) l.reduction f
      b c), w, conjEmbedGL, by simpa [detCharAt_inclGL _ (D.charUnramifiedAt_rankTwist_of_N_mem _ _
      _ · <| l.natCast_mem _ ·)] using o j f (inclGL b) (inclGL c)⁻¹], fun φ ↦ by
    simp [← funext lastRowDatum_conj_u₀, lastRowDatum, w,
      conjEmbedGL, by simpa [↓spaceChar_rankTwist, ↓card_X] using (o j · l.diagNInv l.diagNInv)]
    exact (inv_smul_smul (_ : ℂˣ) _).symm⟩) (mem_ramified_of_mem_ramifiedColumns _ a) _)⟩
  simp; grw [norm_detCharAt_diagN_le, norm_detCharAt_diagN_le,
    IsUltrametricDist.norm_natCast_le_one, mul_inv_le_one_of_le₀] <;>
    (try gcongr) <;> simp [← rpow_mul_natCast, ← sq, m_eq_two_mul_varrho_add_two, prod_nonneg,
    norm_detCharAt_diagN_anti, D.n_mono _] <;> grind

open GeneralLinearGroup Function TwistingData Gf ComplexConjugate WithZero Fintype

/-- For ι : ℂ → ℂ_N, Ψ good for ϑ, and a ramified column φ with F^{ϱ+1}φ a column integral at
`Data.diagPointN` (F = `IsSplitLevel.fourierOp` of `Data.nonInducedRep`), B_μφ has ι-gauge at most
N^{3mfb} everywhere. -/
lemma Data.gaugeLe_Bmu_at_N {P} (D : Data P) [PadicPlace D.N] (l := D.isSplitLevel_nonInducedPlaces)
  {ϑ Ψ} (H : IsGoodDatum ϑ Ψ) {φ} (r : φ ∈ D.ramifiedColumns) (hφ : (fourierOp (D.nonInducedRep 0) ^
  (D.ϱ + 1)) φ ∈ integralFormsAt D.Column (D.diagPointN 0)) : GaugeLe 1 (D.N ^ (3 * D.m
  * D.f * D.b)) (Bμ ϑ Ψ φ) := (D.chain₂_pairTranslates_eq_smul_chain ϑ).rec fun t h ↦
  GaugeLe.restrictToY_of_diag D (D.adeleExtension_map_diagN _ _) fun g ↦ by
  have b := H.gaugeLe_chain ϑ.1.7.coprime_mul_left (fun j ↦ (D.liftKernel ϑ j).ω (_,
    _) ∘ₗ l.name (lastColDatum lastBasisVector)) (fun j x _ a b hb ↦ ?_) _ (φ := ⟨_, hφ.1⟩)
    (fun x _ _ h _ _ _ ↦ by simpa [Kernel.ω_ω] using name_lastColDatum_mem_raises _ _ x h ..) hφ.2 g
  · have := by simpa [*, smul_comm _ t, ← Ψ.smul_sum] using H.chain_at_N φ
    simp [weylGauge_smul, @id (_ = 2 * (_ + 1)) D.m_eq_two_mul_varrho_add_two ▸ this] at *
    grw [b, h.1]; simp [← rpow_add, NeZero.pos]; grind
  obtain ⟨⟨A, r, e⟩, B, s, f⟩ := D.atPlaces_conj_mem_mirabolic a,
    D.atPlaces_conj_mem_mirabolic ⟨b, hb⟩⁻¹; ext1
  simp [liftKernel_ω, lastColDatum,
    pairWeilFinite_name, -coe_units_inv]; congr 1; dsimp [IsSplitLevel.name, comp_def]
  rw [← atPlaces_embedGL (diagN ..), ← atPlaces_embedGL (diagN (InitIndex _ j) _),
    pairWeil_name_of_mem disjoint_star (hΨ := by
    simpa only [onHom_snd_inv_mulVec, vecToMat_matToVec, Matrix.map_mul, comp_def] using!
      (l.isSchwartzBruhat_liftFn _).comp_mulVec
      (G.onHom (s := 1) (s' := 1) ((1, _), 1, _)).2⁻¹.1) (levelOf_le_Kf a.2.1) (levelOf_le_Kf hb.1)]
  congr! 3; convert liftIntegralFn_mul l.reduction _ A B using 2 <;> simp [*, Matrix.mul_assoc,
    mul_apply_eq_vecMul, vecMul_transpose, -val_map_apply, show _ᵀ _ = _ from (mulVec_single_one ..
    ).symm.trans r, (mulVec_injective_of_isUnit (Units.isUnit _)).eq_iff' s] <;> norm_cast

attribute [local simp] mul_assoc QuotientGroup.eq atPlace_atSplit_of_ne mul_sum mul_mem_cancel_right

attribute [-simp] MonoidHom.coe_range

/-- Let l lie in a marked set Λ, T be twisting data on the tops inducing l or l̄, and `HeckeSizes`
hold. Then Y = `Data.IsMarked.markOperator` keeps the integral columns 𝒜, and [𝒜 : Y𝒜 + p^s𝒜] ∣ p^c,
c ≤ (z + xs + y)·dim.

A Frobenius-twisted Hecke operator has small elementary divisors. -/
lemma Columns.hasType_markOperator {P p} {D : Data P} [Fact p.Prime] [PadicPlace p] {Λ l N W ℓ x y z
  Q} [NeZero N] (L : D.IsMarked Λ) (a : l ∈ Λ) (hW : W = (l.valuation D.E).valuationSubring)
  (T : TwistingData N W embValRing) (hp : ¬IsUnit (T.p : embValRing)) (e : T.p = p) (t : _ ≃ Subtype
  Q) (hS : ∀ σ, Q σ ↔ σ ∈ D.tops ∧ (inducedPlace σ = l ∨ inducedPlace σ = star l)) (hc : ∀ s x,
  T.ι s x = ite (T.isEven s) (Φ (t s).1) ((Φ (t s)).comp conj) x) (hA : markExponent l = D.a * #{s
  | T.isEven s}) (big : HeckeSizes T.P T.o₀ N D.k D.a (D.ceilLogM p) ℓ x y z) s : HasType ↑T.p
  D.integralColumns s (L.markOperator ⟨l, a⟩) ((z + x * s + y) * Module.finrank ℂ D.Column) := by
  have q : D.X 0 ≃ Fin D.k := equivFinOfCardEq (by simp [↓card_X, n])
  let P := parahoric W (twoBlock D.k (D.ceilLogM p))
  let ϖ : D.Eˣ := .mk0 p NeZero.out
  let d := diagGL (if q · < D.ceilLogM p then ϖ else 1)
  let jw := (GeneralLinearGroup.map W.subtype).comp (reindexGL q.symm).toMonoidHom
  let j v := GeneralLinearGroup.map (n := D.X 0) (algebraMap D.E (@LocField D.E _ _ v))
  have hM {v x} : j v x ∈ Kw .. ↔ x ∈ intGL _ (v.valuation D.E).valuationSubring.1 := by
    simp [mem_intGL, ← v_algebraMap_eq_valuation, -coe_units_inv]; rfl
  obtain ⟨rfl, _, ⟨ρ, hρ, hρ'⟩, hl, hv, hpl, hl', ⟨⟩⟩ := hW, T.finite_residueField,
    exists_reps_integralAbove (K := D.columnLevel 0) p, L.star_ne a,
    L.maxCompactAt_le_columnLevel a, L.p_mem a, L.valuation_p a, id big
  have hP {β} : j l (d⁻¹ * jw β * d) ∈ Kw .. ↔ β ∈ P := by
    have H β : (∀ i j, l.valuation _ ((d⁻¹ * jw β * d) i j) ≤ 1) ↔ β ∈ P := q.forall₂_congr q (by
      intros; dsimp [twoBlock]
      split_ifs <;> simp [*, d, jw, ← map_inv, field, ϖ, ↓OrderDual.toDual_lt_toDual,
        -WithZero.inv_exp, ← WithZero.exp_add, ← lt_mul_exp_iff_le, ↓Valuation.mem_maximalIdeal_iff]
          <;> first
        | use (β _ _).2.trans_lt (by trivial)
        | use (mul_le_one' (β _ _).2 (by trivial)).trans_lt (by trivial))
    erw [hM, mem_intGL, conj_inv, H, H β⁻¹]; simp
  choose ψ hψ using fun {τ b} (h : ite (τ ∈ D.tops) D.a 0 = b) ↦ schur_one_row_eq_symPowMatrix (k :=
    D.κ τ) (a := b) q.symm (by simp [↓card_X, n]; omega) (by grind only [card_X, κ, n])
  have hj v γ : ((stdSpace ..).embFin γ).atPlace v =
    j v γ := congr(.map (_root_.evalAt v) $(stdSpace_embFin γ))
  have hw' {x} : _ ↔ x ∈ jw.range := hM.trans (reindex_equiv (reindexGL _)).2.1
  have hD : j l d ∈ basicDoubleCoset _ l (D.ceilLogM p) := by convert (diagGL_mem_basicDoubleCoset
    (ϖ := ϖ.map _) ((v_algebraMap_eq_valuation _).trans hl') (q.finsetCongr.symm
    (Iio ⟨D.ceilLogM p, by omega⟩))).1 <;> simp [Units.ext_iff, j, d, Fin.lt_def, apply_ite,
      Equiv.finsetCongr]
  obtain ⟨_, r1, hKw⟩ := ofFinite (_ ⧸ P), (hρ' · ·), fun k : D.columnLevel 0 ↦
    mem_Kf_iff.1 (IsLevel.le k.2)
  let δ x β := ((ρ x).atPlace l)⁻¹ * (j l (jw β) * j l d)
  choose o γ u G using fun b : _ × _ ⧸ P ↦
    exists_eq_map_mul_rep_mul _ _ hρ (ρ b.1 * atSplit hl (δ b.1 b.2.out))
  have H b := eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq (G b).symm)
  choose g hg using fun b ↦ (@hw' ((jw b.2.out * d)⁻¹ * γ b)).1 (by simp [← hj, δ, *])
  have hγ b := eq_mul_of_inv_mul_eq (hg b).symm
  let ε : D.Column ≃ₗ[ℂ] _ := freeLevelEquiv _ _ 1 D.classAut_columnLevel_eq_bot hρ
  let f := ε.symm.1.restrictScalars _ ∘ₗ ((Algebra.linearMap embValRing ℂ).compLeft _).compLeft _
  let c := embValRing.subtype
  have hε F y : (f F).1.1 _ = c ∘ F y := congrFun (ε.4 _) y
  choose m hm using fun b (τ : Subtype (¬Q ·)) ↦ (if h : ↑τ ∈ D.tops then ((@hM (placeOfEmb
    (weightEmbedding ιₚ τ)) (γ b)).1 (by simp [← hj, r1 _ _ (natCast_mem_placeOfEmb _), by simpa [*,
    inducedPlace] using τ.2, H, hKw, placeOfEmb_comp_star, star_involutive.eq_iff])).elim (⟨.map
    (.restrict ((Φ τ).comp conj) _ _ fun _ ↦ (isEquiv_placeOfEmb _).le_one_iff_le_one.2) ·, · ▸
    rfl⟩) else ⟨1, Matrix.ext (by simp [by simpa using hψ (ite_eq_right h) 0])⟩ : ∃ m : GL _ _,
    schur (fun () ↦ D.κ τ) (fun _ ↦ (γ b).1.1.map (Φ τ ∘ conj)) = schur _ fun _ ↦ m.1.map c)
  convert T.hasType_twisted_hecke hp big f o g⁻¹ ((weylRep _ 0).toHomUnits ∘ m) (.trans
    (.piEquivPiSubtypeProd Q _) (.prodCongr (t.piCongr fun s ↦ (ψ (ite_eq_left ((hS _).1 (t
    s).2).1)).symm.trans (.piUnique _)).symm (.refl _))) ?_ (fun F ↦ eq_of_eq_on_class_reps hρ ?_) _
  refine le_antisymm (fun φ H ↦ ⟨fun c ↦ (⟨_, (weylGauge_le_one_iff _ (r1 c)).1
    (by simpa using H.2 _) ·⟩), ε.3 φ⟩) fun | _, ⟨F, rfl⟩ => ⟨by simp, fun g ↦ ?_⟩
  choose c γ k _ using exists_eq_map_mul_rep_mul _ _ hρ g
  simp [levelSpace_smoothFormRep_apply (f F).2, weylGauge_mul, -mul_assoc, ↓weylGauge_embFin,
    weylGauge_le_one_iff, mem_localLevel, *]; use (F c · |>.2)
  simp [finrank_levelSpace_smoothFormRep D.classAut_columnLevel_eq_bot]
  simp_intro b b' h
  use (eq_and_eq_one_of_doubleCoset_rep hρ ((map_eq_one_iff _ Fact.out).1 <|
    (D.classAut_columnLevel_eq_bot _).le ⟨⟨·, rfl⟩, ·⟩) (γ b * (γ b')⁻¹) ((mul_mem_cancel_right
    ((u b')⁻¹ * u b).2).1 (hv ((and_congr_left mem_Kf_iff_of_supportedOn).2 ⟨by
    simp [← mul_assoc, *, -H, -hg, -hM]
    simpa [mul_mem_cancel_left, hw', r1, hpl, (Units.ext (diagonal_transpose _) : invTransposeGL d =
      d⁻¹)] using! hM.2 ((invTransposeGL_mem_intGL _).2 (hM.1 (hP.2 h.2))), by simp +contextual [H,
    h]⟩)))).elim fun e f ↦ Prod.ext e (Quotient.out_equiv_out.1 (QuotientGroup.leftRel_apply.2 (hP.1
    (hw'.2 ⟨g b * (g b')⁻¹, by simp [hg, mul_inv_eq_one.1 f]⟩))))
  ext x; dsimp [IsMarked.markOperator]; erw [(heckeFun_eq_sum_pullback (J :=
    P) _ ((mem_sphericalAt_iff hl).1 (levelSpace_anti hv (f
    F).2)) univ (δ x) (fun z h ↦ ?_) (by simp [δ, ← hP]) _).2] <;> simp [δ, *, -hM, -map_mul]
  congr with b; erw [G (x, b)]
  simp [levelSpace_smoothFormRep_apply (f F).2, stdSpace_weightRep_apply, weylRep, lastEntry,
    mulVec, dotProduct, ← mul_assoc, hε]
  congr! 2; rw [pow_mul', ← prod_const, prod_filter, ← prod_pow, schur_apply_eq_prod .refl,
    schur_apply_eq_prod .refl, ← prod_subtype_mul_prod_subtype Q, ← t.prod_comp, ← mul_rotate',
    diagonal_pow_depth, map_prod]
  simp_rw [letterRep_apply, ← kroneckerPi_mul, ← map_mul, ← prod_mul_distrib, kroneckerPi, of_apply,
    map_prod]
  refine congr((∏ τ, $((hm ..).trans (schur_map .refl ..)) _ _) * ∏ s, $((hψ ..).trans
    (congrFun₂ ((congrArg _ ?_).trans (symPowMatrix_map c _)) ..))); clear * - hc hγ e
  have := NeZero.ne p
  cases _ : T.isEven s <;> ext <;> (try apply congr(p * Φ _ ($(@id ((γ _).1⁻¹.1 =
    _) (U.inv_val_eq_conjTranspose _)) _ _)).symm.trans) <;> simp [*, letterMatrix, deepIndicator,
    mul_apply, diagonal, ← map_inv, jw, d, reindex_equiv q,
    -sum_sum_type] <;> congr with <;> split_ifs <;> simp [*, ϖ, c, field] <;> omega
  choose k₁ _ _ _ h using by simpa [basicDoubleCoset_eq hD, DoubleCoset.mem_doubleCoset] using h
  choose γ a b using exists_mul_mem_integralAbove p (ρ x * atSplit hl k₁) (atSplit hl (j l d)⁻¹)
  choose β _ using hw'.1 (by simpa [*] using a l hpl)
  use β⁻¹; simpa [← mul_assoc, *] using b l hpl
end
