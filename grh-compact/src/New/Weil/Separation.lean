import New.Weil.Staircase
import New.Weil.TestRings
import Lib.GaloisRep.ThetaLift
import New.Weil.TriangleLevelExponent
import Lib.DiscreteSeries.OscillatorPair
import New.Weil.Carrier
import New.Weil.GridModuli
import New.Weil.DegreeBounds
import New.Weil.MonomialCoefficientVector
import Lib.PadicHodge.HeckeStableSubspaces

-- part: Lib.DiscreteSeries.Holomorphic.NearMaximum
section
/-! Known result: A cusp form is large only away from the cusps (Siegel's argument). The statement
here is for unitary groups over a CM field, highest components of vector weights and forms of rapid
decay, with half the supremum in place of an attained maximum. The depth is the first minimum of the
lattice, and it is bounded below explicitly in weight and level. Source: C. Poor, D. Yuen, Linear
dependence among Siegel modular forms, Math. Ann. 318 (2000) 205-234, Thm 1.3; M. Eichler, Math.
Ann. 213 (1975) 281-291; for the factorisation, Gill, Golub, Murray, Saunders, Math. Comp. 28 (1974)
505-535.

This file: Rapidly decreasing holomorphic forms are large only away from cusps, explicit depth. -/

open NumberField Matrix Real Finset UpperHalfPlane Function Prod ComplexConjugate Space G
  Norms.L2Operator
attribute [local simp ←] dotProduct_mulVec stdForm_dotProduct_fst sqrt_inv Space.map_J exp_add
  exp_mul Real.exp_neg rpow_intCast sum_div exp_sub exp_sum mul_sum sum_mul coe_star_ringOfIntegers
  map_sum mat_snd mat_fst coe_algebraMap_Ô
attribute [local simp] vecMulVec_mul mul_vecMulVec vecMulVec_mulVec star_vecMul vecMul_diagonal
  vecMulVec_apply mul_sub sub_mul filter_or filter_eq' ne_of_gt exp_log mul_div div_mul_eq_mul_div
  sum_ite sub_mem ite_mem mul_assoc baseLattice star_mem_Ô sum_pos_iff_of_nonneg

/-- Let F ≠ 0 be rapidly decreasing, automorphic of level ς = −ς̄, Im Φ_wς ∈ (0,c], c ≥ 1,
holomorphic of weight in [−B,B], B ≥ 2, gap 1. Some z has F(z) ≠ 0, |F| ≤ 2|F(z)|, and
|F(g)| ≥ |F(z)| implies `Space.firstMinimum`(g) ≥ (Bc)^{−½}.

Known result: A cusp form is large only away from the cusps (Siegel's argument). -/
lemma exists_near_max {E n} [Field E] [CMType E] [Fintype n] {s : n → _} [Nonempty n] {V : Space E n
  s} {o u F} (B c) {ς : 𝓞 E} (ho : IsPosFirstOrder s o) (hu : ∀ w, HasHolGap s (u w) 1) (hu' :
  ∀ w i, |↑(u w i)| ≤ B) (h2 : 2 ≤ B) (c1 : 1 ≤ c) (hς : star ς = -ς) (hc : ∀ w, (Φ w ς.val).im ∈
  Set.Ioc 0 c) (hF : F ∈ rapidOfLevel V ς) (hH : IsAdelicHol o u F) (h0 : F ≠ 0) : ∃ z, F z ≠ 0 ∧
  (∀ x, ‖F x‖ ≤ 2 * ‖F z‖) ∧ ∀ g, ‖F z‖ ≤ ‖F g‖ → (√(B * c))⁻¹ ≤ (V.move g).firstMinimum := by
  have K w {η v t} y M (e : M = 1 - t • vecMulVec v (star v) * signMatrix s) (hv :
    star v ⬝ᵥ signMatrix s *ᵥ v = 0) (_ : 1 - Complex.re t * ∑ i, ‖v i‖ ^ 2 =
    y - η) (y0 : 1 < y) (_ : 0 < η) (_ : η ≤ 2⁻¹) : ∃ h b, IsBorelMatrix o b ∧ M =
    (h : USign s) * b ∧ ‖diagChar (u w) b‖ ≤ (2 * B * η).exp / √y := ?_
  have hB := le_ciSup ⟨_, Set.forall_mem_range.2 hF.1.2.bounded.choose_spec⟩
  have h1 := (norm_pos_iff.2 (ne_iff.1 h0).choose_spec).trans_le (hB _)
  peel exists_lt_of_lt_ciSup (half_lt_self h1)
  use by grind [norm_zero], by grind, fun g z ↦ le_firstMinimum_iff.2 ⟨?l, fun y hy _ ↦ ?_⟩
  simp [field]; bound
  by_contra! H
  have iso := form_eq_zero_of_norm_mul_lt_one hy hy (by simp [← sq, H.trans_le, field, ?l]) ▸
    stdForm_vecAtPoint ..
  simp [lt_sqrt, Space.archCoords, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, field] at H hy hc
  set Y := vecAtPoint _ y
  let t : G E s :=
    ofMat (1 - toAdele ς.val • vecMulVec Y (star Y) * stdForm _ s) (by simp [add_mul, *])
  have hp h := by simpa [↓mul_assoc, t.mul_def] using ((hF.1.1.2 (g * t * g⁻¹) (by
    simp [← V.mem_move_Γ, mem_Γ_iff_range, t, Y, Space.vecAtPoint, star_mulVec, -coe_units_inv,
      -mul_assoc, vecMul_apply_eq_sum, ← map_mul]) _).trans (congrFun (hF.2 ⟨t.2, by
    use ?_, (⟨-Y · * star Y · |>.2, ?_⟩) <;> simp (maxDischargeDepth := 4) [t, *, mem_Kf, stdForm,
      apply_ite snd, mul_mem]; rfl⟩⁻¹) (g * (h, 1))) :)
  let x ζ w := 1 - (Φ w ↑ς * (ζ - .I)) • vecMulVec (Y · |>.1 w) (star (Y · |>.1 w)) * signMatrix s
  let a w := (∑ i, ‖(Y i).1 w‖ ^ 2) * (Φ w ς).im
  have a0 w : 0 < a w := by simpa [ne_iff, a, *, sq_pos_iff] using eq_zero_of_vecAtPoint_fst.mt ‹_›
  grw [sum_mul, ← sum_le_sum fun _ _ ↦ by grw [← (hc _).2]] at H
  choose φ hol hF' using by simpa [IsHolOfWeight] using hH g
  choose h b T eq le using fun (z : ℍ) w ↦ K w (1 + z.im * a w) (x z w) rfl (by simp [*]) (by
    simp [by simpa [coe_star_ringOfIntegers, self_eq_neg] using congr((Φ w $hς).re)]; ring)
    (by simp [im_pos, *]) (a0 w) (by nlinarith [le_hasSum (hasSum_fintype a) w (by grind)])
  have hf (z : ℍ) := show ‖φ (x z)‖ ≤ _ by simp [funext (eq z), *]; grw [mul_comm, hB, le]
  have z0 : IsZeroAtImInfty _ := squeeze_zero_norm hf (((tendsto_finsetProd _ fun w _ ↦
    (tendsto_sqrt_atTop.comp (tendsto_const_nhds.add_atTop (.atTop_mul_const (a0 w)
    Filter.map_comap_le))).const_div_atTop _).const_mul _).trans (by simp))
  apply (Complex.dist_le_div_mul_dist_of_mapsTo_ball (differentiableOn_cuspFunction_ball one_pos
    ?P (fun z ↦ ((funext (eq z) ▸ hol _ _ (T z)).differentiableAt.comp _
    (by fun_prop)).comp_mdifferentiableAt z.mdifferentiable_coe) z0.boundedAtFilter) (fun q _ ↦ by
    by_cases! q ≠ 0 <;> simp [*, z0.cuspFunction_apply_zero]
    grw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero, comp_def, hf, ← a0, mul_zero]
    repeat positivity) (by simpa using norm_qParam_lt_one 1 .I)).not_gt
  erw [eq_cuspFunction .I one_ne_zero ?P]
  simp [↓z0.cuspFunction_apply_zero, x,
    Periodic.norm_qParam, by simpa [diagChar, IsBorelMatrix] using hF' 1 1]
  grw [← z, ← this, ← mul_one_div, ← exp_neg_one_lt_half]
  bound [two_le_pi]
  intro z; by_cases 0 < z.im; simpa [*, ofComplex_apply_eq_ite, ← eq, ← hF', fun w ↦ show t.1 w *
    x z w = x (z + 1) w by simp [show t.1 w = x (1 + .I) w by ext; simp [t, x, stdForm, signMatrix,
    apply_ite, ite_apply, -mul_sub], x, *]; module] using hF' (t.1 * h ⟨z, ‹_›⟩) (b ⟨z, ‹_›⟩)
  simp [*, ofComplex_apply_eq_ite]
  clear! F; obtain ⟨⟨hi, _⟩, s1, _, m, _⟩ := ho, (Int.units_eq_one_or <| s ·), (sq_nonneg ‖v ·‖),
    Finite.exists_max fun k ↦ s k * u w k
  let x k := ite (s k = 1) (‖v k‖ ^ 2) (-‖v k‖ ^ 2)
  have hx k : x k = conj (v k) * (s k * v k) := by cases s1 k <;> simp [*, x, RCLike.conj_mul]
  have X0 := by simpa [← Complex.ofReal_sum, ← hx, signMatrix, dotProduct] using hv
  let τ := 2 * t.re
  let p a := 1 - τ * ∑ l with o l < a, x l
  have p0 a : 0 < p a := sub_pos.2 (by
    grw [sum_filter, le_max_left τ 0, sum_le_sum (g := (‖v ·‖ ^ 2)) (by grind), max_def]
    exacts [by bound, (em _).elim sum_nonneg fun _ ↦ X0 ▸ sum_le_sum (by grind)])
  have pq k : p (o k + 1) = p (o k) - τ * x k := by simp [p, le_iff_eq_or_lt, hi.eq_iff]; ring
  let L k := (p (o k + 1)).log - (p (o k)).log
  let r k := (-L k / 2).exp / p (o k)
  let β l := s l * conj (v l) * r l
  let c := of fun k l ↦ ite (o k < o l) (v k * τ * β l) (ite (k = l) (r l * p (o l)) 0)
  have d : IsBorelMatrix o c := ⟨?D,
    det_eq_prod_diag_of_blockTriangular hi ?D ▸ by simp [prod_ne_zero_iff, c, r, *]⟩
  use U.of IsHermInvolution.isUnit (M * c) (ext fun i l ↦ ?_), c⁻¹, d.inv, by simp [d.2]
  have K := univ.sum_nonneg fun k _ ↦ show 0 ≤ L k * (ite (τ ≤ 0) ↑(u w m + (s m).1.toNat) B -
    ite (s k = 1) (ite (τ ≤ 0) 1 (2 * B)) 0 - u w k) by
    simp [L, ↓mul_nonneg_iff, p0, log_le_log_iff]; split <;> simp [*, mul_nonneg_iff,
      mul_nonpos_iff] <;> norm_cast <;> grind [HasHolGap, Units.val_one, Units.val_neg]
  have tel T : (∀ l ∉ T, ∀ k ∈ T, o k < o l) → Finset.sum T L = (1 - τ * T.sum x).log :=
    T.induction_on_max_value o (by simp) fun a S ↦ by
    intros; grind [show univ.filter (o · < o a) = S by grind]
  simp [diagChar, ↓d.inv_apply_diag hi, c, r, *, sqrt_eq_rpow, rpow_def_of_pos, y0.trans',
    (tel {k | s k = 1} (by grind)).trans (congrArg _ (by
    simp [x, filter_filter] at *; grind [sum_filter_add_sum_filter_not] : _ = y - η))] at K ⊢
  split at K <;> nlinarith [log_pos y0, show y.log ≤ (y - η).log + 2 * η by
    grw [log_le_iff_le_exp, exp_add, exp_log, ← add_one_le_exp] <;> nlinarith]
  wlog! a : o i ≤ o l generalizing i l
  simpa [← conjTranspose_apply] using congr(star $(this l i a.le))
  rw [show _ * _ = cᴴ * (signMatrix s * (c - (τ : ℂ) • vecMulVec v β)) by
    simp [← show star v ᵥ* (signMatrix s * c) = β by
      ext; simp [vecMul_eq_sum, signMatrix, c, p, ← mul_assoc, *]
      ring, *, τ, t.re_eq_add_conj]; module, mul_apply, sum_eq_single l] <;> simp [c, signMatrix,
    diagonal_apply, β, apply_ite conj] <;> grind -zetaDelta [(mod_cast by simp [r, L,
    exp_sub, p0, ← pq] : (r l * p (o l) * r l * (p (o l) - τ * x l) : ℂ) = 1)]
  grind [BlockTriangular, of_apply]
end

-- part: Lib.Weil.Fock.ReproducingFormula
section
/-! Known result: the basis problem in the stable range, as a reproducing formula. In this unitary
version at a fixed level, pairing with a holomorphic discrete series coefficient is a fixed finite
combination of values of theta lifts to a large definite group. This is deduced from injectivity by
linear duality. Source: S. Böcherer, Über die Fourier-Jacobi-Entwicklung Siegelscher
Eisensteinreihen, Math. Z. 183 (1983); J.-S. Li, Crelle 428 (1992).

Part of: Bargmann–Fock model of the harmonic (oscillator) representation of U(p,q) (known result;
see Lib.Weil.Fock.OscillatorPair).

Part of: Harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors (known result; see
Lib.Weil.Lift.Staircase).

This file: Reproducing formula by theta lifts to large definite groups; holomorphic determinant
vectors. -/


open MeasureTheory Set Matrix MvPolynomial Finset Submodule NumberField Sum Sgn Heisenberg.IsVacuum
  Fintype ComplexConjugate Space Function Complex
variable {n n'} [Fintype n] [Fintype n'] {s O} (ho :
  @IsPosFirstOrder n s O) {E} [Field E] [CMType E] {p q} [Fintype.{0} p] [Fintype q] {s' : n' → _}
attribute [local simp] Matrix.map AlgHom.map_det vacuumWeight pairSign realConv pairHom pairHomInf
  letterMinor

lemma linSubst_letterMinor {i} {c : p → n} {κ} (hi : ∀ a, s' (i a) = κ) (hc : c.Injective) (h : ∀ k,
  s k = κ ↔ k ∈ range c) (u : GInf E s) τ : linSubst (complexLinearPart (pairHomInf (s' :=
  s') (u⁻¹, 1))) (letterMinor τ i c) = principalMinor (u τ) (s · = κ) • letterMinor τ i c := by
  rw [letterMinor, ← det_transpose, AlgHom.map_det, ← C_mul', principalMinor, ← det_reindex_self
    (.trans (.subtypeEquivRight h) (.symm (.ofInjective c hc))), C.map_det, ← det_mul]
  congr with; simp [complexLinearPart, linSubst, posProj, blockDiagonal_apply, (h _).2,
    @Matrix.mul_apply p, sum_prod_type, mul_eq_one_iff_eq_inv']
  rw [sum_of_injective c] <;> aesop

lemma realInner_realPairWeil_eq_holMinorsPi (s : n → _) (s' : n' → _) P (hP :
  P ∈ supported ℂ {p | realSigns E (homSigns s s') p = 1}) {ν c : _ → ℕ} γ e (h : ∀ u : GInf E s,
  linSubst (complexLinearPart (pairHomInf (s' := s') (u⁻¹, 1))) P =
  (∏ w, principalMinor (u w) (s · = 1) ^ ν w * principalMinor (u w) (s · = -1) ^ c w) • P) u :
  let v w i := ite (s i = 1) (-ν w : ℤ) ↑(card n' - negCount s') - c w - e w
  let k w i : ℤ := ite (s i = 1) (-(c w + negCount s')) 0
  let C u y := realInner P (realPairWeil (s' := s') γ e (u, y) P)
  C u 1 = C 1 1 * holMinorsPi s v u * conj (holMinorsPi s k u) := by
  simp [holMinorsPi, ite_sub, negCount, ← card_subtype_compl, realPairWeil]
  rw [← fockMatrixCoeff, fockMatrixCoeff_eq_realInner (d := const _ 0),
    ← congrArg (linSubst _) ((inv_smul_eq_iff₀ _).2 (h u⁻¹))]
  any_goals grind [_root_.pderiv_comm,
    pderiv_eq_zero_of_notMem_vars ∘ Set.notMem_subset (MvPolynomial.mem_supported.1 hP)]
  all_goals simp [← linSubst_mul, ← U.principalMinor_coe_inv, ← inv_eq_conj, holMinors_ite_sign,
    one_kronecker, jacobi_complementary_minor, ← fun w ↦ prod_fiberwise' s' fun σ ↦
    principalMinor (u w) (σ * s · = 1) / (u w).1.1.det, zpow_add₀, field,
    zpow_sub₀, div_pow, prod_ne_zero_iff, neg_eq_iff_eq_neg]

/-- For signature (p,q) and a definite second space of rank n′, the product over places of the
d-th power of a p×p minor in the positive columns is nonzero, and its Fock vector is
holomorphic of weight −d on positive, n′ on negative indices. -/
lemma prod_letterMinor_mem_holomorphicData {O} (ho : @IsPosFirstOrder (p ⊕ q) (1 ⊕ᵥ -1) O) (i :
  p ↪ n') d γ : let Q := ∏ w, ∏ _ : Fin d, letterMinor w i inl
  Q ≠ 0 ∧ polyVector _ Q ∈ holomorphicData (E := E) (1 ⊕ᵥ -1) 1 O (fun _ ↦ -d ⊕ᵥ card n') γ 0 := by
  apply prod_mem_holomorphicData ho (by tauto) fun w ↦
    IsLayering.joint_highest_prod_det (l := 0) ⟨const _ i.2, ?_, ?_, by tauto⟩
    ⟨const (Fin d) inl_injective, ?_, ?_, ?_⟩ rfl <;> simp [filter_eq']

lemma realPairWeil_mem_span_pairedDetProd i {Y : Matrix n' n' E} (hY : IsUnit Y) d γ y :
  realPairWeil (s := 1 ⊕ᵥ -1) (s' := 1) γ 0 (1, y) (polyVector _ (∏ w, ∏ _ : Fin d,
  letterMinor w i (@inl p q))) ∈ span ℂ (.range fun I : _ → Fin d → _ ↦
  polyVector _ (pairedDetProd (X ⟨·, ·, inl ·⟩) fun w k ↦ (Y.map (Φ w)).submatrix (I w k) id)) := by
  choose M e using fun w ↦ (hY.map (Φ w).mapMatrix).unit.mulRight.surjective (y w).1.1ᵀ
  rw [realPairWeil_polyVector]; simp_rw [map_prod]; rw [prod_congr _ _ fun w ↦
    prod_congr _ _ fun _ ↦ .trans ?_ ((detRowAlternating.restrictScalars ℂ).map_sum fun a c ↦
    M w (i a) c • fun b ↦ ∑ k, C (Φ w (Y c k)) * X (w, k, inl b))]
  simp_rw [MultilinearMap.map_smul_univ, Fintype.prod_sum, prod_smul]
  aesop (add safe sum_mem)
  simp [← ext_iff, mul_apply] at *; congr with
  all_goals simp [← e, sum_smul, mul_smul, C_mul', smul_sum] <;> rw [sum_comm]

include ho

/-- Let the orders o, O be those of an injective parameter l, and κ have no column longer than
the number of signs c. The highest vector of weight κ, in the letters of sign c, is a
nonzero polynomial, holomorphic of weight `staircaseWeight`.

Known result: Harmonic highest vectors for (U(p,q), U(n)) give holomorphic vectors. -/
lemma letterPoly_highestVector_holomorphic {o} {l : n → ℤ} (hl : ∀ a b, s a = s b → O a < O b →
  l a < l b) (hi : (-l).Injective) (hO : ∀ a, o a = #{b | s b = s a ∧ s a * l a < s a * l b}) c {κ γ
  w} (hκ : ∀ τ i, card {a // s a = c} < i → κ τ i = 0) : let Q := letterPoly s o c κ (highestVector
    κ fun _ ↦ (equivFin n' ·)); Q ≠ 0 ∧ polyVector _ Q ∈ holomorphicData (E := E) s 1 O (fun τ ↦
    staircaseWeight n' s o (Pi.single c (κ τ)) (-w τ)) γ w := by
  apply prod_mem_holomorphicData ho (fun _ ↦ hl) (fun τ ↦ staircase_harmonic_highest (l' :=
    (c * equivFin n' ·)) hi ?_ hO _ (by aesop) ?_ (by tauto)) <;> fin_cases c <;> simp [letterPoly,
    highestVector, weylKernel, highestPoly, tableauPoly, minor, _root_.permArray, fockLetters,
    ite_and, sum_filter, rowSubst, apply_ite, Fin.val_inj, decrPosition, Injective]

/-- Reproducing formula. Let 2n < n′, 𝔪 = (N) ≠ (1), c, b unramified, Q₀ ≠ 0 holomorphic of
dominant weight u, m = `holMinorsPi` s u integrable, Q spanning the U(n′)(ℝ)-translates of Q₀
at each class. For each x, ψ ↦ ∫ψ(xh)m(h)dh on rapid level-N ψ combines the pairings with
θ^{S,I_{n′}}_{c,b}[1_e,Q] linearly.

Known result: Basis problem in the stable range, as a reproducing formula. -/
lemma reproducing_formula_modKernel [WeilData E] {𝔪 N} [Fact (N ≠ 0)] (hN : 𝔪.ideal =
  .span {N}) (h𝔪 : Nonempty 𝔪.places) (S : Space E n s) {c b γ' γ u} (hc : c.HasWeight γ' 1) (hb :
  b.HasWeight γ 1) (hd : ∀ w, IsKDominant s O (u w)) (hi : Integrable (holMinorsPi s u)) (hn : 2 *
  card n < card n') (e : n ↪ n') {Q₀} (hQ : Q₀ ≠ 0 ∧ polyVector _ Q₀ ∈ holomorphicData s 1 O u γ' γ)
  {ι} [Fintype ι] (Q : StdClasses (principalLevel _ N) → ι → _) (hs : ∀ p y, realPairWeil (s :=
  s) (s' := 1) γ' 0 (1, y) (polyVector _ Q₀) ∈ span ℂ (.range (polyVector _ <| Q p ·))) x :
  ∃ a : _ × ι → ℂ, ∀ ψ ∈ rapidOfLevel S N, ∫ h, ψ (x * (h, 1)) * holMinorsPi s u h = ∑ i, a i * ∫ g,
  ψ g * modKernelI S c b 𝔪 (Pi.single (inclMatrix _ e) 1) (Q i.1 i.2) g i.1.out ∂S.quotMeasure := by
  let T := stdSpace E n'
  refine ((mem_span_range_iff_exists_fun _).1 (mem_span_of_iInf_ker_le_ker (L := fun i ↦ .proj
    (1, i.1.out) ∘ₗ (pairThetaKer S T ..).liftBilin _ ∘ₗ inclusion (p := rapidOfLevel S N)
    inf_le_left) (K := ⟨⟨(realConv (holMinorsPi s u) ·.1 x), ?_⟩, ?_⟩) fun ψ hψ ↦ ?_)).imp fun a e ψ
    l ↦ by simpa [mul_comm (ψ _)] using! congr($e.symm ⟨ψ, l⟩)
  on_goal 3 => have' := congrFun (realConv_eq_zero_of_lift_eq_zero
    (isSharp_modDatum T b _ (inclMatrix _ e)ᵀ ..) _
    (forall_mem_image.2 (congrFun <| ψ.2.2 ⟨·, (𝔪.mem_principalLevel_iff hN _).2 ·⟩)) ψ.2.1 _ (by
    ext y; choose p g w _ using
      exists_eq_map_mul_rep_mul T.embFin (principalLevel _ N) (·.out_eq) y.2
    rw [show y = T.ratEmbed g * ↑p.out * ↑w * ((T.ratEmbed g⁻¹ * y).1, 1) by aesop, lift_mul_right,
      lift_mul_right, ThetaKernel.fixesLeft_lift _ _ ⟨g, rfl⟩, pairWeil_integrated_right c,
      (by simpa [hc.apply_det_eq_one w.2.1, modDatum, (𝔪.mem_principalLevel_iff hN _).1] using
      (pairWeil_modDatum_Kf S T c b 𝔪 1 ⟨_, w.2.1⟩) :)]
    exact mem_span.1 (hs p _) (.proj _ ∘ₗ (pairThetaKer ..).liftBilin.flip _ ∘ₗ
      ((integrated _).flip _).1).ker (by aesop)) γ' _) x; revert this
  all_goals simp [*, (hQ.2 (realInner Q₀)).eq_holMinorsPi_mul ho hd (by
    rw [conj_modelInner, ← modelInner_weilRep (realAction _) <| pairHomInf ⟨·, 1⟩]
    simp [realPairWeil, rep_apply_apply, ← map_mul, inv_eq_conj]), hi.mul_const, mul_assoc, mul_add,
    eq_zero_of_modelInner_self.mt, mul_left_comm (holMinorsPi ..), integral_add,
    fun ψ : rapidOfLevel S N ↦
    IsBoundedMeasurable.integrable_mul_comp (.of ψ.2.1.2.bounded ψ.2.1.1.1) hi (x * ⟨·, 1⟩)]
end

-- part: New.Exchange.AlgebraicPartConjugates
section
/-! This file: Galois conjugate of the lift is the lift for the conjugate Hecke character. Galois
conjugates of the lift's squared norm: factorials over periods, error bounded below. -/

open Finset G LValueData Matrix Parameters Prod Real Space

/-- Galois action on Ξ. Given n, places S with Q empty and σ ∈ Aut(ℂ/K), there are t, l ≠ 0, u with
|t| = Ω^{−1/2} such that, if |n| = 2m, X is on S and μ = σ∘X.μ at finite points, σ(per^D
Ξ(h)_i) = t^D·l·(μυ^m)(u)·(σΔ(h)/Δ(h))·Ξ′(h)_{i′}; D = ∑ dg, Ξ′ the lift for μ, places permuted by
σ; Ξ = `LValueData.trivialLift`, per = `Parameters.jetScale`, dg = `jetDeg`, σΔ/Δ =
`multiplierRatio` σ. -/
lemma LValueData.map_trivialLift {P s} n [Fintype n] (S : LevelPlaces (E P s)) (hψ :
  IsEmpty S.TwistIndex) (σ : Gal(ℂ/K P)) : ∃ t l u, ‖t‖ = (√(P.bigOmega s))⁻¹ ∧ l ≠ 0 ∧ ∀ {X :
  LValueData _ n} {e μ ψ m} is unr, X.1 = S → let Y := (mk X.1 (X.jetDeg <|
    e.symm ·) μ ψ is X.one_lt_card unr); Fintype.card n = 2 * m → placePerm s σ = e → (∀ u, u.1.1 =
    1 → μ.1 u = σ (X.μ.1 u)) → ∀ h i, σ ((P.jetScale s ^ (∑ τ, X.jetDeg τ) • X.trivialLift) h i) =
    (t ^ ∑ τ, X.jetDeg τ) * (l * Y.auxPair.b.1 u) * multiplierRatio σ (onHom (s :=
    X.auxPair.signs) (s' := 1) (1, 1, h)).2 * Y.trivialLift h (i <| e.symm ·) := by
  choose t l z L T hl h1 _ using exists_semilinear_isJetConjugate ((stdSpace _ Unit).hom
    (stdSpace _ n)) (R := S.places) (by grind [S.7.2]) σ
  exact ⟨t, l, _, by simpa using congr(√$T), hl, by
  introv a Y hm he hb; subst a; simp [↓Y.trivialLift_eq_stdClassSum_translate (scalarFin _ z⁻¹),
    trivialLift, apply_eq_evalForm, classSum, mul_sum,
    map_rat_smul, -MonoidHom.coe_range]; congr! 2 with g
  have := congr((schurJet
    _ $((he ▸ h1) _ (pairWeilFinite _ _ 1 X.auxPair.b (g.out, h) X.auxPair.auxDatum).2) *ᵥ 1) i)
  rw [(_ : L _ = (_ : ℂ) • _), (_ : ∀ F, schurJet _ (.rename _ F) =
    (schurJet Y.auxPair.κ F).submatrix (e.piCongrLeft' _) (e.piCongrLeft' _)),
    submatrix_mulVec_equiv, schurJet_jetSeries_eq_smul Y.isLiftWeight] at this
  with_unfolding_all simpa [↓← apply_eq_evalForm, kernelForm, kernelValue, entrywise, ← map_schurJet
                       X.isLiftWeight, AuxPair.κ, mul_sum, mixedWeight, Y, X.one_lt_card, boxes,
    schurJet_jetSeries_eq_smul X.isLiftWeight (jetScale ..), mul_assoc (_ ^ _), Equiv.sum_comp]
  intro; ext; apply jet_rename (Equiv.prodCongr _ 1).toEmbedding
  rw [map_schur Y.isLiftWeight.1, schur_apply_eq_prod X.isLiftWeight.1, ← e.symm.prod_comp,
    schur_apply_eq_prod Y.isLiftWeight.1]; simp; rfl
  simp_rw [pairWeilFinite_apply_apply_coe, pairWeil_apply]
  rw [show G.onHom ((_, _ * _), _) = _ by simpa using ((map_mul _ ((1, _), 1, h) _).trans
      congr(_ * $(onHom_scalarFin z⁻¹ 1))), onHom_fin, ← fst_mul_snd (_, _)]
  simp only [map_smulₛₗ, snd_mul, ← one_mk_mul_one_mk, mul_apply_eq_comp, *, omega_mem_finitePart,
    smul_smul,
    AuxPair.auxDatum, places_levelModulus, liftFn_eq_residueDatum, isSchwartzBruhat_residueDatum _
    X.apart.2, name_mem_finitePart _ _ vacElem_mem_finitePart, pairChar_apply, map_mul]
  congr 1; erw [multiplierRatio, finMultiplier_onHom_left, map_pow, ← div_pow, hm, pow_mul,
    multiplierRatio_sq, detFin, map_inv _ (1, _)]
  simp [rankTwist, *, funext_iff, mul_pow, field]
  congr with; simp [univ_eq_empty, residueDatum, AuxPair.resDetDatum, apply_ite σ]⟩

/-- For σ in Aut(ℂ/K) and fixed n, one c serves all pairs (ν, z) with |n| = 2z ≥ 4: untwisted,
log|σ(‖Ξ‖²)| = c + r + ∑_τ (log λ_τ! − λ_τ log(Ω/g)), λ_τ = c_τ − z, with r ≥ −4f, and r ≤
4f if all λ_τ = 0. -/
lemma Data.Pair.log_norm_map_norm_sq_trivialLift {P} (D : Data P) n [Fintype n] (σ : Gal(ℂ/K P)) :
    ∃ c, ∀ (p : D.Pair) (H : p.HasLiftRank n), ∃ r : ℝ, -(4 * D.f) ≤ r ∧ (p.IsFlat n →
  r ≤ 4 * D.f) ∧ log ‖σ (‖trivialLift H .one‖ ^ 2)‖ = c + r + ∑ τ, D.jetSize (p.c τ - p.z) := by
  choose t c z _ _ J using map_trivialLift n (D.levelPlaces .one) ⟨nofun⟩
  constructor; intro p H
  let X := lValueData H .one
  choose ν hν hb using X.hasWeight.exists_conj (σ := σ) placePerm_spec
  let Y := LValueData.mk X.1 _ ν _ hν X.6 (by clear * -; simp_all [X.7])
  obtain ⟨C, h⟩ := Y.inner_trivialLift_self_eq_L H.1.symm H.2
  set ℓ := ν⁻¹.L ..
  have : ℓ ≠ 0 ∧ _ :=
    abs_log_norm_eulerProd_le hν.inv.isHeckeOfType.norm_heckeCoeff_le le_rfl (mod_cast H.2)
  simp [finrank_eq_two_mul_card_infinitePlace, abs_le, -Set.Sum.elim_range] at this C
  use log (Fintype.card (WeylIndex n Y.auxPair.κ)) +
    log ‖ℓ‖, by grw [← log_natCast_nonneg]; linarith!,
    fun d ↦ by grw [Fintype.card_le_one_iff.2 fun _ _ ↦ linearIndependent_nablaBasis
    (R := ℂ).injective (by simp [nablaBasis_eq_one, Y, X, d])]; simp; linarith!
  erw [trivialLift, mul_pow, ← mul_assoc, mul_smul, norm_smul, norm_mul, norm_pow (star _),
    Complex.ofReal_mul, mul_pow, ← inner_self_eq_norm_sq_to_K (_ • X.trivialLift),
    ← Complex.ofReal_pow, mul_pow, pow_right_comm, D.norm_map_star_piG_sq 1, map_mul,
    LevelPlaces.map_inner_self_eq σ _ (J σ hν Y.7 rfl H.1 rfl hb) (J {(starRingAut * σ.toRingEquiv *
    starRingAut :) with commutes' x := by simpa using congr(star $(σ.4 (star x)))} hν _ rfl
    H.1 congr(.mulLeft (.mk $(by ext; simp [← map_star_complex, placePerm_spec])))
    (by simp [← Circle.coe_inv_eq_conj, ← hb · ·])) (by simp [multiplierRatio, div_mul_div_comm,
    finMultiplier_ne_zero, ← map_finMultiplier_mul_conj σ]), h,
    prod_coe_sort, hookNumber_eq_prod_factorial, ← Equiv.prod_comp (placePerm _ σ)]
  simp +instances [jetSize, log_mul, log_div, log_prod, *, X, Y, bigOmega_pos, NeZero.pos, log_sqrt,
    le_of_lt, prod_ne_zero_iff, ne_of_gt, ← sum_mul, -Fintype.card_pi, -H, ← sub_eq_iff_eq_add,
    twist_one_spec]
  ring; rfl
end

-- part: New.Weil.FockCoeffDecay
section
/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

This file: Explicit degree-uniform decay of Heisenberg matrix coefficients of homogeneous Fock
vectors. -/

open MeasureTheory Real Fintype MvPolynomial Matrix.Norms.L2Operator Heisenberg IsVacuum Rep WithLp

/-- Let P be homogeneous of degree d in |ι| > 0 variables, v = v_P, σ in U(ε), A ≥ d + |ι| and n
natural numbers, y ≠ 0. Then |⟨v, ϱ(y)ω(σ)v⟩| ≤ (4(A+n))^n |y|^{−2n} ‖σ‖^{|ι|+2n} ⟨v,v⟩,
with Euclidean and ℓ² operator norms. -/
lemma norm_realInner_realHeisOp_le {ι : Type} [Fintype ι] [Nonempty ι] {ε P v y} (σ : USign (n := ι)
  ε) (hv : v = polyVector ε P) {d A n} (hP : ∀ (c : ℝ) x, eval (c • x) P = c ^ d * eval x P) (hA :
  d + card ι ≤ A) (h0 : A ≠ 0) (hy : 0 < ‖toLp 2 y‖) : ‖realInner v (realHeisOp y (realWeil σ v))‖ ≤
  ‖σ.1.1‖ ^ (card ι + 2 * n) * (realInner v v).re * (4 * (A + n)) ^ n * ‖toLp 2 y‖⁻¹ ^ (2 * n) := by
  let c := √(n / A + 1)
  obtain ⟨i, p⟩ := (integrable_norm_sq v).comp_smul (R := c⁻¹) (by positivity),
    ((realAction ε).2 σ).add_left _ y
  have j := p.integrable_comp_of_integrable i
  rw [← (realInner v).comp_apply]; simp [↓map_integrated_eq_integral, weilRep, realAction,
    modelInner_self]
  grw [norm_realMultiplier_le, norm_integral_le_of_norm_le ((i.add j).mul_const ((4 * (A + n) *
    (‖σ.1.1‖ / ‖toLp 2 y‖) ^ 2) ^ n / (c ^ 2) ^ card ι / 2)) (.of_forall ?_)]
  simp [mul_comm _ 2, ↓integral_mul_const, ↓integral_add' i j, ↓p.hasLaw.integral_comp i.1, mul_pow,
    pow_mul, ← two_mul, ↓Measure.integral_comp_inv_smul _ (‖v ·‖ ^ 2), div_pow, pow_add, field]
  simp_intro x [fun x ↦ (by simp (disch := positivity) [*, realVac, star_dot_self_eq_norm_sq, sq, c,
    ← exp_nat_mul, mul_assoc, ← exp_add, field, star_trivial] : ‖v (c⁻¹ • x)‖ = ‖v x‖ * exp
    (‖toLp 2 x‖ ^ 2 / (n + A) / 2) ^ n / |c| ^ d), ↓modelInner_heisOp_vacElem,
    ← conj_modelInner]; grw [← two_mul_le_add_sq]
  simp [field, pow_right_comm _ d, mul_assoc, ← pow_add, ← mul_pow, ← exp_add]
  grw [sq_sqrt (by bound), add_one_le_exp, ← exp_nat_mul, hA, mul_div_left_comm,
    div_self_le_one, exp_nat_mul, ← exp_one_mul_le_exp]; gcongr; field_simp
  grw [norm_le_add_norm_add, σ.1.1.l2_opNorm_mulVec (toLp 2 x), ← one_mul ‖_ + _‖,
    U.one_le_norm σ, add_sq_le]; linarith!
end

-- part: New.Rows.SparseThetaSum
section
/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

This file: Crude formal degree bound; rotation argument isolating a value at a point where |F| is at
least half its supremum. Sparse
theta sums approximate a matrix coefficient; first minimum of Hom lattices. -/

open MeasureTheory Matrix Norms.L2Operator Finset Fintype AddCircle NumberField
variable {E n} [Field E] [NumberField E] [Fintype n] [Nonempty n] {s m} {B : ℝ} (hn :
  numInfPlaces E * (2 * card n ^ 3) ≤ m) (hm : m ≤ B) (hB : 10 ^ 13 ≤ B) {o} {k w : InfinitePlace
  E → _} (ho : @IsPosFirstOrder n s o) (hu : ∀ τ, IsKDominant s o (w τ)) (hd : ∀ τ,
  IsKDominant s o (k τ)) (hw : ∀ τ,
  HasHolGap s (w τ) (300 * m)) (hk : ∀ τ, HasHolGap s (k τ) (300 * m)) (hk' : ∀ τ i, |↑(k τ i)| ≤ B)

attribute [fun_prop] IsHolOfWeight IsHolOfWeight.continuous

attribute [local simp] maxOpNorm abs_of_pos Measure.real

@[bound] lemma one_le_maxOpNorm (h : GInf E s) : 1 ≤ maxOpNorm h :=
  (norm_le_pi_norm _ Classical.ofNonempty).trans' (U.one_le_norm _)

include hn hm hB ho hu hd hw hk hk'

/-- Let w, k be dominant with gap 300m, |k| ≤ B, 2f|n|³ ≤ m ≤ B, B ≥ 10¹³ (f infinite places).
Then ∫|mh_k|² > 0
(`holMinorsPi`); if A is continuous, |A(h)| ≤ C‖h‖^N, N ≤ 6m, then A·mh_w is integrable and
|∫A·mh_w| ≤ C·B^{7m}∫|mh_k|². -/
lemma integral_mul_holMinorsPi_le : 0 < ∫ h, ‖holMinorsPi s k h‖ ^ 2 ∧ ∀ A, Continuous A → ∀ᵉ (C)
  (N ≤ 6 * m), (∀ h, ‖A h‖ ≤ C * maxOpNorm h ^ N) → Integrable (A * holMinorsPi s w) ∧
  ‖∫ h, A h * holMinorsPi s w h‖ ≤ C * B ^ (7 * m) * ∫ h, ‖holMinorsPi s k h‖ ^ 2 := by
  obtain ⟨_, _, q, _⟩ := @card_pos n _ _, le_of_mul_le_of_one_le_right hn card_pos,
    (card n).pow_le_pow_right card_pos (2).le_succ, (card n).le_mul_self
  let c := 2 * card n ^ 3 * 5; choose b e using
    (dsCoeff_eq_holMinors ho (8 * m) (300 * m) · · · (by lia))
  choose i t using fun τ ↦ integral_tail_le (hg := b _ (hd τ) (hk τ)) (L := 2 * ⌊B⌋₊ + card n)
    (fun a ↦ by grw [Pi.add_apply, abs_add_le, abs_twoRho_le, ← Nat.le_floor (n := (k τ a).natAbs)]
    <;> simp [*]) c (by lia)
  obtain ⟨_, P⟩ := (isHolOfWeight_holMinorsPi ho hu).continuous, univ.prod_pos fun τ _ ↦
    formalDegree_pos (b _ (hd τ) (hk τ))
  refine have I := by simp [holMinorsPi, formalDegree, prod_pow,
      ← integral_fintype_prod_volume_eq_prod, *]
    ⟨(inv_pos.2 P).trans_eq I, fun A a C N hN H ↦ have := by simpa using (norm_nonneg _).trans (H 1)
      have j := (Integrable.fintype_prod i).const_mul (C * 2 ^ N * ∫ h, ‖holMinorsPi s k h‖ ^ 2)
      (imp_and.2 ⟨j.mono' (by fun_prop), (norm_integral_le_of_norm_le j · |>.trans ?_)⟩) (.of_forall
      fun h ↦ (IsGreatest.pi_norm (h · |>.1.1)).1.elim fun a z ↦ (norm_mul_le ..).trans ?_)⟩
  grw [integral_const_mul, (integral_fintype_prod_eq_prod _).trans_le (prod_le_prod₀ (by
    intros; rw [formalDegree]; positivity) fun τ _ ↦ t τ), mul_right_comm, mul_assoc C, prod_const,
    q, pow_mul' 2, le_self_pow₀ (a := 8), ← mul_pow, ← mul_pow, ← pow_mul', card_univ,
    hn, hN, pow_mul, ← mul_pow, pow_mul B, (?_ : _ + 1 ≤ 5 * B)] <;> try bound
  gcongr; field; bound
  rify at *; grind [Nat.floor_le]
  grw [H, holMinorsPi, norm_prod, fun τ ↦ (e _ (hu τ) (hw τ) _ ▸ norm_dsCoeff_le_pow (by tauto)
    (c := c + ite (τ = a) N 0) (by rify at *; grind) _ :)]
  simp [pow_add, ← z, div_pow, field, -mul_ite, ← I]

/-- Isolation, for k, w as in `integral_mul_holMinorsPi_le`. Let F be continuous, holomorphic of
weight k,
|F| ≤ 2|F(z)| ≠ 0, K₀ bounded. If each x with |F(x)| ≥ |F(z)| has ∫conj F(xh)·K·mh_w = 0 for
some K holomorphic of weight k − w, |K − K₀| ≤ ε‖h‖^{6m}, then |K₀(1)| ≤ (4B^{7m} + 1)ε. -/
lemma isolation [IsCMField E]
    {F z C ε} {K₀ : _ → ℂ} (hF : Continuous F) (c : IsAdelicHol o k F) (ha : F z ≠ 0)
    (h2 : ∀ x, ‖F x‖ ≤ 2 * ‖F z‖) (g : ∀ h, ‖K₀ h‖ ≤ C) (H : Integrable (holMinorsPi s w) → ∀ x, ‖F
  z‖ ≤ ‖F x‖ → ∃ K, IsHolOfWeight s o (k - w) K ∧ (∀ h, ‖K h - K₀ h‖ ≤ maxOpNorm h ^ (6 * m) * ε) ∧
  ∫ h, star (F (x * (h, 1))) * K h * holMinorsPi s w h = 0) : ‖K₀ 1‖ ≤ 4 * ε * B ^ (7 * m) + ε := by
  have ⟨I, i⟩ := integral_mul_holMinorsPi_le hn hm hB ho hu hd hw hk hk'
  choose K hK r _ using fun θ ↦ H (by simpa using i 1 continuous_one 1 0 : _ ∧ _).1
    _ (by simpa using congr(‖$((c z).apply_mul_diagTorus 1 (@toCircle 1 θ ^ o ·))‖).ge)
  refine let W θ h := _; have v h : ∫ θ, W θ h = _ :=
        (c z).circle_mean_holMinorsPi ho hd h ▸ integral_conj; ?_
  have hf := ((i (K 0) (by fun_prop) (C + ε) _ le_rfl fun h ↦ by
    grw [norm_le_insert' _ (K₀ h), r, ← g]; ring; bound).1.comp_snd volume).mul_bdd (g :=
    W.uncurry) (by fun_prop) (.of_forall (by simp [W]; tauto))
  obtain ⟨j, this⟩ := hf.integral_prod_right, integral_prod_symm _ hf ▸ integral_prod _ hf ▸
    norm_integral_le_of_norm_le_const (hf.prod_right_ae.mono fun θ X ↦ by
      have ⟨d, q⟩ := i (W θ * (K 0 - K θ)) (by fun_prop) (4 * ε * ‖F z‖) _ le_rfl fun h ↦ by
        simp [W]; grw [h2, ← sub_sub_sub_cancel_right _ _ (K₀ h), norm_sub_le, r, r]; linarith
      rwa [← sub_eq_zero.1 ((integral_sub d X).symm.trans _)]
      simp; ring_nf; simp_all [W, mul_right_comm _ _⁻¹, mul_assoc z, integral_neg])
  simp_all [← mul_assoc, integrable_mul_const_iff, -Pi.mul_apply]
  grw [norm_le_insert (K 0 1), r]
  simpa [↓(sub_add_cancel k w ▸ (hK 0).mul ho.1
    (isHolOfWeight_holMinorsPi ho hu)).integral_mul_conj_holMinorsPi ho hd j, I, field] using this

omit hn hm hB ho hu hd hw hk hk'

open BigOperators Circle ComplexConjugate Prod Space WeilData

attribute [local simp] EuclideanSpace.norm_eq Modulus.liftFn_apply Set.indicator firstMinimum_pos
  move_vecAtPoint vecToMat le_of_lt realCoord traceChar vacuumFn

variable {E n n' : Type} [Field E] [CMType E] [Fintype n] {s : _} [Fintype n'] {s'} [Nonempty n]
  [Nonempty n'] {S : Space E n s} (T : Space E n' s')

/-- For a nonzero integer N in the different of E, the shortest vector length of the lattice of
Hom(S,T) is at least λ_S·λ_T/(6N(fn)²n′n), with n, n′ the ranks and f the number of infinite
places. -/
lemma firstMinimum_mul_le_hom {N} [NeZero N] (hd : ↑N ∈ differentIdeal ℤ (𝓞 E)) :
    S.firstMinimum * T.firstMinimum / (shortBasisConst E n N * Fintype.card n' * Fintype.card n) ≤
  (S.hom T).firstMinimum := by
  rw [le_firstMinimum_iff]
  use by grw [firstMinimum_le_one, firstMinimum_le_one] <;> simp [Nat.cast_inv_le_one,
    ← Nat.cast_mul], fun z _ o ↦ ?_
  choose Y hY hY' using S.exists_short_basis hd
  choose a b using (T.mem_and_norm_le_of_vecAtPoint _ S · (vecToMat (vecAtPoint _ z)) 1 (fun w ↦
    l2_opNorm_le_of_apply ((archCoords _ z).norm_apply_le ⟨w, ·, ·⟩)) (by erw [one_smul,
    vecAtPoint_hom _ _ (vecToMat z), ratMap_mulVec_vecAtPoint]))
  have := S.firstMinimum_pos
  grw [firstMinimum_le (a _ (by simp_all [baseLattice]) (hY _)) (Function.ne_iff.1 fun H :
    (vecToMat z * Y.1)ᵀ = 0 ↦
    o (by simpa using! congr(matToVec ($Hᵀ * Y.2)))).choose_spec, b, hY']; simp [field]

omit [Nonempty n] [Nonempty n'] in
/-- For Ψ_t(y) = ψ(tr(yt)) modulo 𝔪 and an adelic vector z, ⟨v ⊗ Ψ_t ⊗ vac, ϱ(z)(w ⊗ Ψ_t ⊗ vac)⟩
is Ψ_t read at α⁻¹z_f (`Modulus.liftFn`) times ⟨v, ρ(z_∞)w⟩ times the vacuum at the finite
part z_f. -/
lemma dataInner_traceChar [WeilData E] {𝔪} t v w z : dataInner _ (modDatum S T 𝔪 (traceChar t) v)
  (ϱ _ z (modDatum S T 𝔪 (traceChar t) w)) = 𝔪.liftFn (traceChar t ∘ vecToMat) (finCoord z) *
  (realInner v (realHeisOp (realCoord z) w) * vacuumFn (0, z · |>.2)) := by
  obtain ⟨u, rfl : of _ = _⟩ := 𝔪.reduction_surjective.comp_left.comp_left t
  erw [rho_integrated_realCoord, dataInner_integrated, (_ : _ ∘ vecToMat = _),
    𝔪.name_char_eq_translate_projOn _ (matToVec u ∘ swap), ϱ_swap,
    map_smul] <;> simp +contextual [-Heisenberg.Rep.mul, funext_iff, finVec, ↓← rho_integrated,
    matToVec, finCoord, trace, adelicHeis, Matrix.mul_apply, ← map_mul, ← map_sum, stdForm,
    stdAddChar, dotProduct, fst_sum, snd_sum, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, two_mul,
    ← add_mul, ← map_add, mul_mem] <;> simp [stdLattice.psi₀_apply, Finset.mul_sum, sum_prod_type,
    mul_assoc, mul_left_comm, mul_comm (u ..).1]

/-- Sparse theta sums. Let c ≠ 0, cα𝔪Ô ⊆ Ô, 0 < m, m|τc| ≤ √(2π Im τȷ)·λ_{Hom(S,T)}(g,h) for all
τ, q > fnn′, Q homogeneous of degree d. Then for some Ψ mod 𝔪, θ[Ψ,Q](gu,hu′) is within
(100(d+2q)/m²)^q(‖u‖‖u′‖)^{3q}‖v_Q‖² of ⟨v_Q, Ω(u,u′)v_Q⟩ for all real u, u′. -/
lemma norm_modKernel_sub_realInner_le [WeilData E] {a b γ γ' ψ ψ' 𝔪 g} (ha : a.HasWeight γ ψ) (hb :
  b.HasWeight γ' ψ') {c : E} (c0 : c ≠ 0) (hc : ∀ z, 𝔪.reduction z = 0 → ↑c * (α.1 * ↑z) ∈ Ô E) h m
  q (m0 : 0 < m) (hm : ∀ w, m * ‖Φ w c‖ ≤ √(2 * .pi * (Φ w j).im) * ((S.move g).hom (T.move
  h)).firstMinimum) (hq : Fintype.card (InfinitePlace E × n' × n) < q) Q {v} (hv : v = polyVector _
  Q) (d : ℕ) (hQ : ∀ (c : ℝ) x, Q.eval (c • x) = c ^ d * Q.eval x) : ∃ Ψ, ∀ u u', ‖modKernel S T a b
  𝔪 Ψ Q (g * (u, 1)) (h * (u', 1)) - realInner v (realPairWeil γ γ' (u, u') v)‖ ≤ maxOpNorm u' ^
  (3 * q) * (100 * (d + 2 * q) / m ^ 2) ^ q * ‖realInner v v‖ * maxOpNorm u ^ (3 * q) := by
  use 𝔼 t, conj (modKernel S T a b 𝔪 (traceChar t) Q g h) • traceChar t, fun u u' ↦ ?_
  let L := (S.hom T).move (G.onHom (g, h))
  rw [show hom .. = L by simp [L, move, hom, Units.ext_iff, mul_kronecker_mul, G.onHom]] at hm
  have A (y : {y | c • y ∈ L.baseLattice ∧ y ≠ 0}) : m ≤ ‖WithLp.toLp 2
    (realCoord (L.vecAtPoint y))‖ := by grw [← mul_le_mul_iff_right₀ L.firstMinimum_pos,
    ← norm_smul_of_nonneg, firstMinimum_le y.2.1, mul_comm, ← norm_smul_of_nonneg] <;> simp [*,
    abs_of_nonneg, archCoords, val_scaleIdele_fst, ← mul_assoc, ← mul_rotate √_, y.2.2]; grw [hm]
  have ⟨p, r⟩ := tsum_inv_pow_le_of_separated (n := 2 * q) m0 (fun y z h ↦ by simpa [sub_div]
    using (A ⟨y - z, by grind [smul_sub, sub_mem]⟩)) A (by simp_all; omega)
  have h4 :=
    (hasSum_sum (s := ⊤) fun t _ ↦ let φ := ω _ (G.onHom (g, h)) ∘ modDatum S T 𝔪 (traceChar t)
    hasSum_dataInner _ (φ (realPairWeil γ γ' (u, u') v)) (φ v)).mul_left
    (Fintype.card (Matrix n n' 𝔪.ResRing) : ℂ)⁻¹
  simp [dataInner_omega_left, ω_ϱ, rep_apply_apply, dataInner_traceChar, finCoord, ← Finset.sum_mul,
    sum_addChar_trace_mul, Modulus.isPrimitive_primAddChar, ← ext_iff] at h4
  refine ((((hasSum_subtype_iff_of_support_subset ?_).2 (hasSum_ite_sub_hasSum h4
    0)).norm_le_of_bounded (p.hasSum.mul_left _) fun y ↦ .trans ?_ (norm_realInner_realHeisOp_le
    (pairHomInf (u, u')) hv hQ le_rfl (by simp) (m0.trans_le (A y)))).trans' ?_).trans ?_
  simp_intro y h
  simpa [L, baseLattice] using
    (hc _ <| (𝔪.reduction_idem_mul ⟨_, h.2.1 _ _⟩).symm.trans <| h.2.2.1.2 · ·)
  simp; split_ifs <;> simp [L, realPairWeil]
  rw [← modKernelBilin_apply]; simp [modKernel, pairTheta, ← mk_mul_mk, mul_comm (conj _),
    modDatum, *, pairWeil_integrated,
    Finset.expect, NNRat.smul_def, ← ZeroMemClass.zero_def, realCoord.eq_unfold, ← Pi.zero_def]
  simp [pairWeil, mul_mul_mul_comm _ _ (_ * _), ← coe_inv_eq_conj, mul_mul_mul_comm _ _⁻¹]
  nth_grw 1 [Complex.re_le_norm, r, hq, hq, pow_mul, mul_assoc,
    ← mul_pow, show ‖(pairHomInf _).1.1‖ ≤ maxOpNorm u * _ from
    (NonUnitalStarAlgHom.norm_apply_le ({ blockMatrix with .. } : _ →⋆ₙₐ[ℂ] Matrix (InfinitePlace E
    × n' × n) _ _) _).trans ((pi_norm_le_iff_of_nonempty _).2 fun w ↦ (norm_pairHom_le ..).trans (by
    gcongr <;> apply norm_le_pi_norm _ w))] <;> simp [U.one_le_norm, submatrix_smul, star]
  linear_combination
end

-- part: New.Rows.NaturalFormNear
section
/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

Part of: The carrier: one fixed form under all twists (see New.Rows.Carrier).

This file: The carrier is non-zero, of level one, rapidly decreasing and holomorphic. Combinations
of twist-free theta forms approximate a fixed test function at points away from the cusps (first
minimum bounded below). -/

open Finset Fintype Matrix NumberField Sum WeilData

variable {E} [Field.{0} E] [CMType E] [WeilData E] {m : ℕ} [NeZero m]

/-- Let m > 0 be even, and let E have a tame character of weight 0. Then `carrierForm` is rapidly
decreasing, automorphic of every level N, and holomorphic of weight 0 and 3m on the two blocks, for
some order with the positive block first.

The carrier: one fixed form under all twists. -/
lemma carrierForm_spec (he : Even m) {𝔪 c χ} (hc : IsTameFor (E := E) 𝔪 c 0 χ) :
  (∀ N, carrierForm E m ∈ rapidOfLevel (signedSpace ..) N)
  ∧ ∃ o, IsPosFirstOrder (1 ⊕ᵥ -1) o ∧ IsAdelicHol o (fun _ ↦ 0 ⊕ᵥ 3 * m) (carrierForm E m) := by
  obtain ⟨⟨n, _, _, _⟩, _, _, H⟩ := id hc, by simpa [classSum, Rat.smul_def, mul_sum,
    ← mul_assoc, ← funext_iff] using (stdClassSum_carrierXi_eq_carrierForm E he).choose_spec hc
  use fun _ ↦ H ▸ (one_mul _).subst (mul_sum_mem_rapidOfLevel fun _ ↦ (one_mul _).substr
    ⟨⟨⟨by fun_prop [modKernel], (pairThetaKer ..).theta_rat_mul, ⟨_, isOpen_Kf⟩, ?l⟩,
    isRapid_modKernel _ _ _ _ n (⟨_, ·.nonsing_inv_mul <| χ.apply_ne_zero_iff.1 ·⟩) _ _⟩,
    (funext <| ?l _ ·.2.1)⟩), (-1 - ·) ⊕ᵥ (·), ?q, H ▸ (.sum _ fun _ ↦ isAdelicHol_pairTheta
    (by simpa +arith using (prod_letterMinor_mem_holomorphicData ?q (@.inl _ (Fin m)) 0 _).2) ·)
  simp [↓Subtype.forall', modKernel_mul_Kf_left, hc.apply_det, Pi.smul_def, mul_comm,
    χ.apply_eq_zero_iff]
  simp [IsPosFirstOrder, Function.Injective]; lia

/-- For m > 0 the carrier `carrierForm`, the theta lift of the constant 1 from U(0, m) to U(2m,
m), is not identically zero. -/
lemma carrierForm_ne_zero : carrierForm E m ≠ 0 := by
  have c a := (realInner_realPairWeil_eq_holMinorsPi (E := E) (-1) (1 ⊕ᵥ -1) (∏ τ,
    letterMinor τ (@inr (Fin a) (Fin m)) id ^ a) (by aesop (add safe [prod_mem,
    sum_mem], simp [letterMinor, det_apply', pairSign])) (ν := 0) · 0 fun _ ↦ by
    simpa [linSubst_letterMinor (κ := -1) (elim_inr _ _) Function.injective_id, smul_pow] using
      prod_smul ..)
  have : CompactSpace (@USign (Fin m) _ (-1)) := (by simp [U] : USign _ = U 1).substr inferInstance
  apply mt (integral_eq_zero_of_lift_eq_zero (isSharp_modDatum _ 1 ?_ 0 (by subsingleton) ..)
    _ ?_ ?o ?_ · 0 ?o) <;> simp [Space.IsAutomorphic.mem_rapidFunctions, prod_eq_zero_iff, c,
    Space.petersson, holMinorsPi, holMinors, Heisenberg.IsVacuum.eq_zero_of_modelInner_self.mt,
    inr_injective, MeasureTheory.measureReal_univ_ne_zero, Function.injective_id,
    Space.isAutomorphic_const, NeZero.pos]

attribute [local simp] prod_smul HasHolGap IsKDominant pairSign smul_pow smul_smul

lemma Data.negIndex_posRowIndex_spec {P} {D : Data P} (j : D.LiftIndex) :
  ((negIndex j).Injective ∧ ∀ h, (posRowIndex j h).Injective) ∧
  (∀ a, padSigns j (negIndex j a) = -1) ∧ ∀ h a, padSigns j (posRowIndex j h a) = 1 := by
  refine ⟨⟨?_, fun _ ↦ ?_⟩, ?_, ?_⟩ <;> intro <;> intros <;>
    simp_all [negIndex, posRowIndex, basisVec] <;> split_ifs at * <;> simp_all [signsW] <;> grind

open Norms.L2Operator

/-- For 1 ≤ j ≤ m and ν = `Data.nStar` there are a bounded K₀ and ε with 4ε(5b)^{7ν} + ε <
|K₀(1)| such that, whenever λ(g) ≥ (5b²⁴)^{−1/2} (`Space.firstMinimum`), some combination ∑_a
c_a(g)F♮_a(gy) of the `Data.fNatural` is within ‖y‖^{6ν}ε of K₀(y) for all archimedean y. -/
lemma Data.exists_fNatural_approx {P} {D : Data P} (j : D.LiftIndex) :
  ∃ (K₀ : _ → ℂ) (C ε : ℝ), 4 * ε * (5 * D.b) ^ (7 * nStar D) + ε < ‖K₀ 1‖ ∧ (∀ y, ‖K₀ y‖ ≤ C) ∧
  ∀ g, (√(5 * D.b * D.b ^ 23))⁻¹ ≤ ((D.spaceW j).move g).firstMinimum → ∃ c : _ → ℂ, ∀ y, ‖∑ a,
  c a * fNatural j a (g * (y, 1)) - K₀ y‖ ≤ maxOpNorm y ^ (6 * nStar D) * ε := by
  obtain ⟨hm, ⟨h4, n⟩, hr, b2, cl, _, ho, cH⟩ := (by simp [card_neg_signsW, j.2.2, *] :
    negCount (padSigns j) = D.m), (by simp [↓card_rowIndex]; grind : card D.CarrierIndex ≤ D.t ∧
    card (D.RowIndex ⊕ PadIndex j) ≤ D.t), negIndex_posRowIndex_spec j, D.nStar_bounds,
    carrierForm_spec D.m_even (isTameFor_twistedChi (c := 2) j 1)
  obtain ⟨⟨e⟩, ⟨eb, he, pb⟩, x, x0, xm, xl⟩ :=
    @Function.Embedding.nonempty_of_card_le D.CarrierIndex D.FlatIndex _ _
    (by simp; omega), (@exists_eq_left _ (AutChar.HasWeight _ · 1) _).2 (carrierChar_hasWeight j),
    exists_near_max (5 * D.b) D.x₁ ho (by simp; grind) (by simpa [Real.exp_nonneg] using
    D.le_of_hasLogBound) D.le_of_hasLogBound D.le_of_hasLogBound P.star_sqrtNegDInE
    (by simpa [P.d_prime.pos] using D.le_of_hasLogBound) (cl _) cH carrierForm_ne_zero
  let ς (_ : D.Φ) : D.CarrierIndex → ℤ := -D.reducedHalfGap ⊕ᵥ card D.FlatIndex
  have pe := realInner_realPairWeil_eq_holMinorsPi (1 ⊕ᵥ -1) (padSigns j) (linePoly j) (by
    simp (maxDischargeDepth := 9) [linePoly, letterMinor, det_apply', prod_mem, mul_mem, pow_mem,
      sum_mem, hr]) (fun _ ↦ D.m) eb fun _ ↦ by simp [linePoly, prod_pow_eq_pow_sum, -card_sum,
    linSubst_letterMinor (hr.2.2 _) inl_injective, linSubst_letterMinor hr.2.1 inr_injective]; rfl
  extract_lets v k C at pe
  let ι y : GInf D.E (padSigns j) := (G.sum ((y, 1), 1)).1
  have ⟨J, H⟩ := integral_mul_holMinorsPi_le (m := nStar D) (B := 5 * D.b) (by grw [h4])
    D.le_of_hasLogBound D.le_of_hasLogBound ho (w := ς) (k := k) (by simp [ς]) (by simp [k])
    (by simp [ς, reducedHalfGap]; lia) (by simp [k, -Nat.cast_sum]; grind [reducedHalfGap])
    fun w i ↦ by grw [← two_mul_card_detIndex_add_le j w]; clear * - hm; norm_cast; grind
  obtain ⟨v0, _, _, _, c, hc⟩ := RingOfIntegers.coe_ne_zero_iff.2 (pow_ne_zero 2 D.piGBar_ne_zero),
    NeZero.ne D.cycloConductor, D.t_odd.pos, ((signedSpace ..).move x).firstMinimum_pos,
    reproducing_formula_modKernel ho D.ideal_untwistedModulus_eq_span nonempty_modulus_places _
    (hasWeight_upsilonU1_pow D.m) .one (u :=
    ς) (by simp [ς]) (by simpa using H 1 (by fun_prop) 1 0 : _ ∧
    _).1 (by simp; omega) e (prod_letterMinor_mem_holomorphicData ho (.trans .inl e) ..) _ (fun p ↦
    realPairWeil_mem_span_pairedDetProd (Y := D.shortRows (p, 0)) _ (by simp [shortRows]) _ _) x
  have key {A b} N l (h : ∀ u, ‖A u‖ ≤ b * maxOpNorm u ^ N) (a :
    Continuous A := by fun_prop [modKernel]) := H
    _ ((cH x).continuous.fun_mul a) _ N l fun u ↦ by grw [norm_mul, xm, h, mul_comm, mul_right_comm]
  choose _ _ _ l a r using (isUnitaryRep_detTwist (ε :=
    realSigns D.E (homSigns (n := D.CarrierIndex) (1 ⊕ᵥ -1) (padSigns j)))
    (f := .id _) (γ := 0) (one_mul _).ge).exists_innerProductSpace; simp at r
  have k0 y :=
    key (A := (C · y)) 0 bot_le fun _ ↦ by simp [C, realPairWeil, ← a]; grw [norm_inner_le_norm, r]
  have e1 := IsHolOfWeight.integral_mul_conj_holMinorsPi (u := k) ho (by simp [k]) (by
    convert ((cH x).mul ho.1 (isHolOfWeight_holMinorsPi (u := ς) ho (by simp [ς]))).mul ho.1
      (.sum (T := {0}) ![C 1 1] fun _ ↦ isHolOfWeight_holMinorsPi ho (u := v) (by simp [v]))
    ext w (_ | _) <;> simp [ς, v, k, he, hm, ← card_detIndex_add_bigCharExp j] <;> omega)
  simp [mul_assoc _ (C .. * _), ← pe, mul_right_comm _ _ (C ..)] at e1
  refine ⟨_, _, _, ?_, (ι · |> k0 |>.2), fun g hl ↦ (norm_modKernel_sub_realInner_le ((D.spaceW
    j).sum ((stdSpace ..).neg.sum (stdSpace ..))) (hasWeight_upsilonU1_pow _) pb (div_ne_zero
    (NeZero.ne (D.N₁ : D.E)) v0) ?_ (.sum (g, 1)) (D.b ^ 7 * D.x) (2 * nStar D) (HasLogBound.pos D)
    (fun w ↦ ?_) (by grw [card_prod, card_prod, h4, n]; use D.nat_lt_of_hasLogBound) (linePoly j)
    rfl _ fun _ _ ↦ by simp [-sum_add_distrib, -prod_mul_distrib, linePoly, letterMinor, det_apply',
    ← Complex.coe_smul, -smul_eq_mul, ← smul_sum, ← pow_mul, ← pow_add,
    prod_pow_eq_pow_sum]; rfl).elim fun Ψ hΨ ↦ (exists_sum_smul_addChar_trace_eq (D.untwistedModulus
    2).isPrimitive_primAddChar fun x ↦ Ψ x.toRows₁ * (Pi.single (inclMatrix _ e) 1 : _ → ℂ)
    x.toRows₂).imp' (fun f a ↦ c a.2 * f a.1) fun f hf y ↦ (key _ (by omega) (hΨ · (ι y))).elim fun
    i q ↦ (congrArg _ (sub_eq_of_eq_add (.trans (.trans ?_ ((hc _ (mul_modKernel_mem_rapidOfLevel
    D.ideal_untwistedModulus_eq_span (hb := pb) (cl _) ..)).symm.trans
    (by congr with; simp [field]))) (MeasureTheory.integral_add i (k0 _).1)))).trans_le (q.trans
    (by simp_rw [mul_assoc]; grw [← mul_assoc 3, show maxOpNorm _ ≤ maxOpNorm y by simp [ι, G.sum,
    U.sum, pi_norm_le_iff_of_nonempty, one_le_maxOpNorm, norm_le_pi_norm (y · |>.1.1)]]; rfl))⟩
  grw [show ι 1 = 1 by simp [ι], e1 (k0 _).1, (?_ : _ / _ ≤ (D.b ^ 12)⁻¹)]
  simp [C, abs_of_pos J, field, ← a, linePoly]
  field_simp [prod_eq_zero_iff, hr, inl_injective, inr_injective]
  use D.lt_of_hasLogBound
    (by clear * -; grind [(D.le_of_hasLogBound : 1 + 7 * |↑(nStar D)| ≤ nStar D * D.logB)])
  grw [Nat.cast_sum, sum_le_card_nsmul _ _ (2 * D.m * (5 * D.b)) fun w _ ↦ by
    grw [← two_mul_card_detIndex_add_le j
      w]; clear * -; norm_cast; simp [← mul_sum]; lia]; simpa using D.le_of_hasLogBound
  simpa [Modulus.reduction_eq_zero_iff, ideal_untwistedModulus_eq_span,
    Ideal.mem_span_singleton, ↓dvd_def, -Subtype.forall, ← mul_assoc,
    mul_right_comm _ α.1, ← map_pow, ← map_mul, -Nat.cast_mul, ↓div_mul_cancel₀ _ v0,
    -Subtype.exists] using! fun z : Ô _ ↦ mul_right_comm _ _ z.1 ▸ mul_mem P.N₁_mul_α_mem z.2
  · grw [← firstMinimum_mul_le_hom _ P.cycloConductor_mem_different, Space.shortBasisConst,
      ← inf_le_firstMinimum_sum, ← G.sum.map_one, ← inf_le_firstMinimum_sum, ← ((stdSpace ..).move
      _).one_le_firstMinimum, ← ((stdSpace ..).neg.move _).one_le_firstMinimum, inf_idem,
      inf_of_le_left (by simp), ← hl, ← xl _ le_rfl, h4, n, show ‖_‖ = (D.N₁ : ℝ) / D.gProd by
      simpa [sq, -Nat.cast_mul] using congr(D.N₁ / ‖Φ w $D.piGBar_mul_star‖)]
    simpa [WeilData.j] using D.le_of_hasLogBound
  · simp_rw [sum_prod_type_right (α₂ := _ × _), mul_assoc (c _), ← mul_sum, fNatural, Pi.mul_apply]
    congr! 2; rw [← integral_mul_sum_const_mul fun t ↦
      mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (cl _) ..]; congr with
    simp_rw [mul_assoc, ← modKernel_sum_right, ← hf, ← modKernelBilin_apply]; simp [ι, G.sum,
      ← map_mul]; left; rfl
end

-- part: New.Rows.Separation
section
/-! Products of theta forms detect all good forms. For a finite family of choices with small
integral data, a good form on U(W_j) orthogonal to all products of the twist-free theta forms with
theta kernels of the complementary block is zero, and this non-degeneracy of the comparison forms is
needed to cancel the volumes of lifts. It is known that stable-range theta kernels reach all forms,
that maxima of forms avoid the cusps and that products span for GL(2). Related work: J.-S. Li,
Non-vanishing theorems for the cohomology of certain arithmetic quotients, 1992; Poor–Yuen, Linear
dependence among Siegel modular forms, 2000; Khuri-Makdisi, Moduli interpretation of Eisenstein
series, 2012.

Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: The main result `Data.eq_zero_of_integral_fNatural_tableTheta`. Hodge–Tate jumps of the
data lie in low or high windows. The three character
pairs and the product of Hecke value ratios. Untwisted Hecke value is large against parallel weight,
giving negative height. One twist-free form is a multiple, possibly zero here, of each twisted theta
form, with L-value
ratio. Level and holomorphic weight of the twist-free theta form. -/
seal Finset.univ Finset.sum Finset.prod

open NumberField Multiset Data Int Fintype Real WeilData Data.Pair Additive Function Matrix Sum
variable {P} {D : Data P}

@[simp] lemma cmSign_star σ : @cmSign D.E _ _ (star σ) = -cmSign σ := by
  grind [cmSign, neg_neg, Φ_eq_or, InfinitePlace.mk_eq_iff]

/-- For 1 ≤ j ≤ m, the multisets of the r integers ⌊t/2⌋ − sgn(σ)(ς_q + w_j), 0 ≤ q < r, at the
embeddings σ satisfy the jump conditions `IsRowType` for (r, t); sgn is 1 on the CM
type, else −1. -/
lemma isRowType_auxPair {j} (hj : j ∈ D.LiftIndex) : IsRowType D D.r D.t fun σ ↦ (Multiset.range
  D.r).map fun q ↦ D.t / 2 - cmSign σ * (D.rowParameter (.mk σ) q + D.w j (.mk σ)) := by
  use ⟨D.nat_le_of_hasLogBound, .refl⟩, .refl, ⟨j, hj.2, by simpa using fun σ p _ ↦ by grind
    [rowParameter, units_natAbs, (mul_le_mul_left (by grind : p + 2 - D.k + j < D.t) D.h).trans
    (D.nat_le_of_hasLogBound (B := D.h₂ ^ 2))]⟩, fun σ ↦ (mul_le_mul' (?_ : _ ≤ D.r + 1 - D.k)
    D.k_le_r).trans (by grind), fun σ ↦ ?_ <;> induction D.r <;> simp_all [countP_cons] <;> grind
    [rowParameter, units_natAbs, !(D.nat_lt_of_hasLogBound : 2 * D.h₂ ^ 2 + D.h₂ < D.w _ _)]

/-- For a sign s, the number e_s: e₊ = m and e₋ = ⌊m/2⌋. -/
def Data.eSign {P} (D : Data P) (s : ℤˣ) := ite (s = 1) D.m (D.m / 2)

/-- The natural number 𝖾 = ⌊(k + 7m)/2⌋, the point z of the pair `Data.linePair` j none. -/
def Data.heckeCount {P} (D : Data P) := 7 * (D.m / 2) + D.k / 2

/-- Three pairs (ν, z) for 1 ≤ j ≤ m: (μ_j⁰υ^{j+⌊(t−11m−1)/2⌋}, ⌊(k+7m)/2⌋) at none, and
(υ^{−e_s}χ^{sj}, e_s) at a sign s, with e₊ = m, e₋ = ⌊m/2⌋. -/
noncomputable def Data.linePair {P : Parameters} {D : Data P} (j : D.LiftIndex) : Option ℤˣ →
  D.Pair := by
  let n := j + (D.t - 11 * D.m - 1) / 2
  refine' Option.rec (.mk _ (D.w j · - n) _ D.heckeCount (((D.mu₀_hasWeight j).mul_upsilonU1_pow
    n).of_weight_eq _) ..) fun s ↦ ⟨_ * _ ^ (s.1 * j), fun _ ↦ D.eSign s, _, D.eSign s, by
    simpa using! (WeilData.hasWeight_upsilonU1_pow _).inv.mul (D.chi_hasWeight.zpow _), _, _, _, _⟩
  any_goals refine' fun v ↦ .trans (b := (D.w j v : ℝ)) (Nat.mono_cast _) _
  all_goals grind [heckeCount, eSign, omega_eq_one_of_not_isChosen, _root_.one_zpow, Pi.pow_apply,
    w_le_two_mul_b]

/-- The product, over the three pairs (ν, z) of `Data.linePair`, of `lValueProd`((νϑ^{±1})⁻¹, z)
off the chosen places and Q; the exponent is −1 only for the sign −1. -/
noncomputable def Data.heckeValueProd {P} {D : Data P} (j : D.LiftIndex) (ϑ : D.Twist) := ∏ i,
    (lValueProd ({w | D.IsChosen w} ∪ ϑ.Q) ((linePair j i).ν * ϑ.toAutChar ^ (i.getD 1).1)⁻¹
  (linePair j i).z : ℂ)

namespace Data

variable {P : _} {D : Data P}

/-- Let n have even size 2z, 4 ≤ 2z ≤ t. A weight-0 character χ of U(1)(𝔸), tame at the chosen
places, equals ν·υ^z for a pair (ν, z) of parallel weight −z with the same tame part. -/
lemma exists_isFlat n [Fintype n] (hn : 4 ≤ Fintype.card n ∧ Fintype.card n ≤
  D.t ∧ 2 ∣ Fintype.card n := by simp; grind) (χ : AutChar.tameChars D.finite_isChosen.toFinset) :
  ∃ p : D.Pair, (rankTwist p.ν n = χ.1.1 ∧ p.ψ = χ.1.2) ∧ p.IsFlat n := ⟨⟨_, _, _, Fintype.card
  n / 2, by simpa using! χ.2.1.mul (hasWeight_upsilonU1_pow _).inv, by simp_all [χ.2.2], by
    grind, fun _ ↦ le_rfl, fun _ ↦
  .trans (mod_cast by lia) (D.le_of_hasLogBound : ↑D.t ≤ _)⟩, by simp [rankTwist]; lia⟩

/-- For a pair p of rank one for j (`Data.Pair.IsRankOne`), the squared norm of the untwisted form
`Data.Pair.trivialLift`, as a constant family, has height (`HeightLe`) at most B₀ − ∑_τ st(w₀(τ)),
st = `Data.jetSize`. -/
lemma heightLe_norm_trivialLift_sq {j p} (H : @IsRankOne P D p j) :
    HeightLe (D.B₀ - ∑ τ, D.jetSize (D.w 0 τ)) fun _ ↦ ‖trivialLift H.1 .one‖ ^ 2 := by
  obtain ⟨q, -, h⟩ := D.exists_isFlat (RankOneIndex p.z) (by grind [IsRankOne]) 1
  refine ⟨q.intAlgPart h.2 .one / ‖trivialLift H.1 .one‖ ^ 2, _, 0, by simp,
    (P.exists_algEquiv_norm_eq · |>.elim fun σ e ↦
    (log_norm_map_norm_sq_trivialLift D (RankOneIndex p.z) σ).elim fun _ k ↦
    le_exp_of_log_le ?_), by simp [(isIntegralMeasure_intAlgPart ..).norm_apply_one_le], by aesop⟩
  obtain - := k, k _ h.2, k _ H.1, sum_mono fun τ ↦ D.jetSize_le_add
    (by cases j <;> grind [IsRankOne] : D.w 0 τ ≤ p.c τ - p.z + 0)
  simp [h, Pair.intAlgPart, twist_one_spec, denomBound, log_mul, log_div, NeZero.ne, jetSize] at *
  rename_i a b _; obtain ⟨⟨_, _, _, _⟩, _, _, -, _⟩ := And.intro a b; simp only [e]
  linarith [(D.le_of_hasLogBound :
    Real.log D.chosenGroupOrder + D.f * (8 * q.z * Real.log D.gProd + 8) ≤ D.B₀)]

end Data

attribute [local simp] Data.regroupEquiv Data.negIndex Data.detRows

/-- For 1 ≤ j ≤ m there are C (not shown non-zero here) and numbers c_ϑ with |c_ϑ|² = C /
`Data.heckeValueProd`(ϑ) such that
c_ϑ times `cosetKernelSum`, for w and the vectors `Data.lineMultiplier` of the choice i, equals F♮_i
(`Data.fNatural`) whenever the matrix of i is uw for some u.

Twisted theta forms lie on one line. -/
lemma Data.cosetKernelSum_eq_fNatural {P} {D : Data P} {a} [Fintype a] j : ∃ C, ∃ c : D.Twist → ℂ,
  ∀ ϑ, ‖c ϑ‖ ^ 2 = C / heckeValueProd j ϑ ∧ ∀ (u : Matrix _ a (D.untwistedModulus 2).ResRing) i g
  (w : Matrix a _ (D.untwistedModulus 2).ResRing), u * w = i.1 → fNatural j i g = c ϑ *
  cosetKernelSum (D.auxPair ϑ j) (bigChar ϑ j) w (.trans .inl .inl) (lineMultiplier ϑ j i) g := by
  have' hs : _ = blockSigns (.ofBijective (regroupEquiv j ∘ Sum.map (D.basisVec ∘ Fin.val (n :=
    D.posRank j)) inr ⊕ᵥ inr ∘ inl ∘ negIndex j) _) := _
  have e ϑ : bigChar ϑ j * WeilData.upsilonU1 ^ D.m = twistedChi ϑ j * carrierChar j := ?_
  have' := (explicit_matching _ (.refl _) · 1 (posEquiv j) _ hs _ _ (DetIndex j))
  choose _ _ _ hK using this
  choose _ _ _ hM using stdClassSum_carrierXi_eq_carrierForm D.E D.m_even
  repeat constructor
  refine fun ϑ ↦ let hν := (isTameFor_twistedChi j ϑ).mul (carrierChar_hasWeight ..); .symm ⟨fun u i
      g w H ↦ .symm (.trans ?_ (explicit_matching_of_sum _ _ hν (hM (isTameFor_twistedChi j _))
      (D.untwistedModulus 2) levelModulus_ideal_le _ fun _ _ h _ ↦ (hK _ hν
      (by simp [← card_detIndex_add_bigCharExp j]) (detRows j i.2) h (bigChar ϑ j) _ :).trans (by
    congr! <;> simp [← e, matchedPoly, pairedDetProd, letterMinor, ← mul_assoc, linePoly,
      prod_sigma, AlgHom.map_det, Matrix.map, ← Finset.prod_mul_distrib]
    congr! 4; omega; rw [← Fin.prod_const]; congr!
    repeat ext; simp [entrywise, inclMatrix, posRowIndex] <;> split <;> rfl))), ?_⟩
  simp_rw [@classSum_comm (Gf _ (BigIndex j)), ← mul_classSum]
  refine congrArg _ (.trans ?_ congr(stdClassSum _ fun _ ↦ _ * $(stdClassSum_rowStabilizer_eq hν (by
    rw [hs]; simpa [-regroupEquiv] using! realPairWeil_stackedDetProd _ _
      (funext (by simp [← card_detIndex_add_bigCharExp j])) (detRows j i.2) 1) (forgetTwist _) w
    (.trans .inl .inl) (F := fun y ↦ ∑ k : GL _ _, traceChar i.1 (y.map (forgetTwist _) * k.1))
    fun A a ↦ by simp [traceChar, Matrix.mul_assoc, trace_mul_comm (A.1.map _), ← H, a.2])))
  simp_rw [mul_classSum, @classSum_comm (Gf _ D.CarrierIndex), ← e,
    cosetKernelSum]; congr with h; clear * -
  change modKernelBilin (D.spaceW j) _ _ _ _ _ _ (columnDatum _ (forgetTwist _) _ _) (letterPoly _
    _ 1 (untwistedAuxPair j).colsPlus _) = _
  rw [pi_eq_sum_univ' (lineMultiplier ϑ j i h)]; symm
  simp [lineMultiplier, modKernelI, mul_classSum, ← classSum_sum, mul_left_comm (modKernel ..),
    mul_assoc, -mul_ite, ← Finset.mul_sum, mul_comm (modKernel (.sum ..) ..),
    ← modKernel_sum_left, -regroupEquiv]; congr!
  erw [← modKernel_reindex (regroupEquiv ..).symm ?_ (.refl _) rfl,
    ← map_sum ((modKernelBilin ..) _), modKernelBilin_apply]; congr! -closePost 1; rfl
  ext1; simp [GeneralLinearGroup.ext_iff, Space.reindex, Space.sum]
  rfl; grind [pow_sub_mul_pow, card_neg_signsW, auxPair]
  congr! 2; simp [lPlusDatum, ← ite_and]; congr
  simp [entrywise, inclMatrix, forall_and, -sum_sum_type]; tauto
  simpa [Prod.map_comp_map, ← comp_assoc, -regroupEquiv] using!
    stdClassSum_carrierXi_eq_lineMultiplier j _ inl (inr ∘ inr)
  apply G.ext_mat; simp [entrywise, Prod.ext_iff, funext_iff, U.sum]; iterate 3 aesop
  simp [← Complex.ofReal_pow, mul_pow, div_pow, heckeValueProd, places_modulus_eq_union, *,
    linePair, eSign, ← division_def,
    div_right_comm _ (_ * _), div_mul_div_comm]; with_reducible congr
  any_goals clear * -; apply_fun ofMul; simp [bigChar, liftChar, twistedChi, carrierChar, μ₀];
            match_scalars <;> grind [heckeCount]
  all_goals simp [↓card_rowIndex, ↓bijective_iff_injective_and_card, Injective, signsW, funext_iff,
    ↓Equiv.eq_comp_symm, apply_dite (padSigns j), basisVec]; grind [Equiv.injective, heckeCount]

unseal Finset.univ Finset.prod

namespace Data

variable {P : _} {D : Data P} {j : D.LiftIndex} (F : D.goodForms (D.spaceW j))

lemma goodForms_mem_rapidOfLevel {a} (d : D.piGBar ∣ a := by simp) :
  F.1.1.1 ∈ rapidOfLevel (D.spaceW j) a := ⟨F.1.1.2.mem_rapidFunctions D.isCuspKernel_paramW,
  (funext <| Space.mem_levelSpace_formRep_iff.1 F.1.2 _ <| D.principalLevel_le_chosenLevel d ·.2)⟩

/-- For a good form F on U(W_j), F·F♮_i is rapidly decreasing of level π̄² (π̄ = `Data.piGBar`), and
F♮_i = `Data.fNatural` is holomorphic of weight `conjHolWeight` − `kernelWeight`. -/
lemma mul_fNatural_mem_rapidOfLevel_and_hol i : F * fNatural j i ∈ rapidOfLevel (D.spaceW j)
  (D.piGBar ^ 2) ∧ IsAdelicHol (orderW j) (conjHolWeight j - kernelWeight j) (fNatural j i) := by
  choose _ _ _ e using cosetKernelSum_eq_fNatural (a := D.CarrierIndex) j
  simpa only [Pi.sub_def, conjHolWeight_eq_add_kernelWeight, add_sub_cancel_right, funext
    (e 1 1 i · _ i.1.one_mul), cosetKernelSum, classSum, finsum_eq_sum_of_fintype, Rat.smul_def,
    Finset.mul_sum, ← mul_assoc] using have G := D.fitsParams_auxPair ..; ⟨mul_sum_mem_rapidOfLevel
      fun _ ↦ mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span
    (goodForms_mem_rapidOfLevel F) _ _ _ ((auxPair ..).tame_eq_one · <|
      places_levelModulus.ge.mt ·), (.sum _ fun _ ↦ isAdelicHol_pairTheta
    (mem_holomorphicData_of_highestVector (e' := 0) (_ ∘ₗ _) (by simp [Injective, Fin.val_inj]) (by
      intros; erw [realPairWeil_fockLetters, star_mulVec]; simp [letterPoly, weylRep,
        ← mulVec_transpose, comp_def, conjTranspose_transpose])
      (letterPoly_highestVector_holomorphic isPosFirstOrder_orderW (paramW_lt_of_orderW_lt 1)
      (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsPlus_eq_zero).2) ·)⟩

end Data

open ComplexConjugate AuxPair Parameters

/-- On U(W_j), the sum over classes c of level ϖ² of the conjugate (W_j, V°) kernel at (g, c):
datum 1_inc mod ϖ², polynomial of conj ζ(c) in negative letters. -/
noncomputable def Data.tableTheta {P} {D : Data P} (j : D.LiftIndex) (ζ : D.SmallClasses → _) g :=
  ∑ c, conj (modKernelI (D.spaceW j) (untwistedAuxPair j).a (upsilonU1 ^ (D.m / 2 - j : ℤ))
  (D.untwistedModulus 2) (Pi.single (inclMatrix _ .inl) 1) (letterPoly (D.signsW j)
  (untwistedAuxPair j).ord (-1) (untwistedAuxPair j).colsMinus (star (ζ c))) g c.out)

/-- For 1 ≤ j ≤ m, a good form F on U(W_j) vanishes if ∫ conj(F·F♮_i)·θo(ζ) = 0 over [U(W_j)] for
all choices i and all ζ, where F♮ = `Data.fNatural` and θo = `Data.tableTheta`.

Products of theta forms detect all good forms. -/
lemma Data.eq_zero_of_integral_fNatural_tableTheta {P} {D : Data P} {j : D.LiftIndex} (F :
  D.goodForms (D.spaceW j)) (h : ∀ i ζ, ∫ g, conj (F.1.1 g * fNatural j i g) * tableTheta j ζ
  g ∂(D.spaceW j).quotMeasure = 0) : F = 0 := by
  obtain ⟨o, N, G, _, _, _, ε, C, M⟩ := @isPosFirstOrder_orderW _ D j, rank_bounds_card_bigIndex j,
    D.fitsParams_auxPair _ j, exists_fNatural_approx j
  have H : IsAdelicHol (orderW j) (conjHolWeight j) (star <| F.1.1 ·) := by
    obtain ⟨⟨_, e'⟩, _, J, k, _⟩ := (_ ∘ₗ _).surjective_of_injective
      ((LinearMap.self_comp_adjoint_injective_iff _).2 (D.auxLift_injective .one)) F.1,
      G.exists_isJointHarmonic
    erw [← e', (exists_theta_to_principalForms ..).choose_spec j.2]
    simpa [θ, AuxPair.conjKernel, classSum, Rat.smul_def] using! (.sum _ fun _ ↦
      isAdelicHol_pairTheta (mem_holomorphicData_of_highestVector (_ ∘ₗ _) (J · |>.gap.1)
      (realPairWeil_harmonicPoly _) (congr(polyVector _
      $k).substr (prod_mem_holomorphicData o paramW_lt_of_orderW_lt (J · |>.2) rfl).2)) ·)
  choose w6 w3 w2 w5 w4 using conjHolWeight_kernelWeight_bounds j
  choose lG hG using mul_fNatural_mem_rapidOfLevel_and_hol F
  repeat apply Subtype.ext
  refine star_eq_zero.1 (by_contra (exists_near_max _ _ o (by grind only [HasHolGap, nStar_bounds])
    w6 D.le_of_hasLogBound D.le_of_hasLogBound (by simp [star_sqrtNegDInE]) (by simpa [NeZero.pos]
    using D.le_of_hasLogBound) (star_mem_rapidOfLevel (goodForms_mem_rapidOfLevel F (.mul_right ⟨_,
    D.piGBar_mul_star.symm⟩ (sqrtNegDInE ..)))) H · |> fun ⟨g, g0, g2, hl⟩ ↦
    ε.not_ge (isolation (by bound) D.le_of_hasLogBound D.le_of_hasLogBound o w2
    w3 w4 w5 w6 F.1.1.2.continuous.star H g0 g2 C fun I z a ↦ ⟨_, .sum _ (hG · _), (M _ (hl _
    a)).choose_spec, ((reproducing_formula_modKernel o D.ideal_untwistedModulus_eq_span
    nonempty_modulus_places _ (hasWeight_upsilonU1_pow _) (hasWeight_upsilonU1_zpow _) w2 I
    (by simp [N]; omega) .inl (letterPoly_highestVector_holomorphic o (paramW_lt_of_orderW_lt 1)
    (G.paramsCorrespond 1).2.1 (G.ord_eq 1) _ G.colsMinus_eq_zero) (fun _ ↦ fockLetters (D.signsW j)
    (untwistedAuxPair j).ord (-1) ∘ nablaBasis ℂ _ (untwistedAuxPair j).colsMinus)
    (by intros; erw [realPairWeil_fockLetters]; clear * -; aesop (add safe sum_mem,
    simp [toPoly, linearCombination_apply])) z).choose_spec _ (star_star F.1.1.1 ▸
    mul_sum_mem_rapidOfLevel lG :)).trans (Fintype.sum_eq_zero _ fun c ↦ ?_)⟩)))
  simp [mul_assoc, Finset.sum_mul]
  refine .inr ((integral_mul_sum_const_mul fun i ↦ (mul_assoc ..).subst
    (mul_modKernel_mem_rapidOfLevel D.ideal_untwistedModulus_eq_span (lG i) ..)).trans
    (Fintype.sum_eq_zero _ fun i ↦ mul_eq_zero_of_right _ ?_))
  let ⟨v, e'⟩ := range_toPoly.ge (prod_tableauPoly_mem_nabla : nablaBasis ℂ _ _ c.2 ∈ _)
  simpa [tableTheta, ← integral_conj, ← modKernelBilin_apply, apply_ite, letterPoly, e', mul_assoc,
    nablaBasis] using! congr(conj $(h i (Pi.single c.1 (star v))))
end
