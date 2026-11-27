import New.Weil.ModuleIndex
import New.Weil.LiveSum
import New.Weil.ChainValuation
import New.Weil.ElementaryDivisors

-- part: New.Curve.JetDivisibility
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

-- part: New.Seesaw.LiftCharacters
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

-- part: New.Columns.TwistedHeckeType
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
