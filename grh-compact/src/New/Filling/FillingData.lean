import Lib.DiscreteSeries.ComplexPlace
import New.Filling.PoincareSeries
import New.Filling.BesselExistence
import New.Filling.OpenCellBound
import Lib.DiscreteSeries.LevelGauge
import New.Filling.StableCells
import New.Filling.SobolevCell
import New.Filling.LocalTheorem
import New.Weil.SteepParameters
import New.Weil.LineCoordinates

-- part: Lib.DiscreteSeries.Bruhat.ComplexFloorMeasure
section
/-! Part of: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar measure
(known result; see Lib.DiscreteSeries.Bruhat.ComplexPlace).

This file: Product of Heisenberg floor measures equals coordinate Haar measure on the unipotent
group. -/
seal Finset.univ Finset.sum Finset.prod


open Matrix MeasureTheory Measure Fintype Real Finset
variable {𝔰 : Shape}
attribute [-instance] MeasurableSingletonClass.toDiscreteMeasurableSpace

/-- The Gaussian exp(−π Σ_{b<l}(Σ_i |g_{i,e*_b}|² + (Im g_{e_b,e*_b})²)) on G₁, the inner sum
over the basis indices i of floor (`floorOf`) greater than b. -/
noncomputable abbrev freeGaussian l (g : 𝔰.G₁) := ‖rexp (-π * ∑ b with b.1 < l,
  let w :=
    g.1.1 *ᵥ Pi.single (eStar b) 1; ∑ i with b < floorOf i, ‖w i‖ ^ 2 + (w (.inl b)).im ^ 2)‖ₑ

lemma lintegral_freeGaussian_ascConv {l} (hl : l ≤ 𝔰.ϱ) : ∫⁻ ν : 𝔰.G₁,
  freeGaussian l ν ∂ascConv Place.heisenbergMeasure l = 1 := by
  induction' l with a ih; simp [ascConv, freeGaussian]
  erw [lintegral_mconv_symm, Place.heisenbergMeasure, dite_eq_left, ← volume.map_id, map_prod_map,
    lintegral_map, lintegral_map, lintegral_congr fun x ↦
    lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν h ↦ ?_, lintegral_lintegral_mul,
    lintegral_gaussian_eq_one, ih (by lia), one_mul]; any_goals fun_prop
  push_cast [freeGaussian, ← mulVec_mulVec, heisenbergElem_mulVec]
  rw [← add_sum_erase (a := ⟨a, hl⟩), mul_add, exp_add, enorm_mul, ← sum_subtype_eq_sum_filter]
  congr! <;> try rw [unipotentBelow_mulVec_apply h]
  all_goals simp_all [Complex.conj_eq_iff_im.1 (star_form IsHermUnit.conjTranspose_eq ..), ne_of_gt,
    inclMatrix_val_mulVec, -mulVec_mulVec, Fin.ext_iff, Nat.lt_of_succ_le] <;> grind [floorOf]

/-- The measure `Shape.besselHaar` on 𝖴, viewed on G₁, equals the convolution η₀∗⋯∗η_{ϱ−1} of the
measures of the floors.

Known result: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar
measure. -/
lemma ascConv_heisenbergMeasure_eq_besselHaar : ascConv Place.heisenbergMeasure 𝔰.ϱ =
  𝔰.besselHaar.map .val := ext_of_lintegral _ fun f hf ↦ by
  trans ∫⁻ y, ∫⁻ x,
    freeGaussian 𝔰.ϱ (y⁻¹.1 * x) * f y ∂ascConv complexPlace.heisenbergMeasure 𝔰.ϱ ∂𝔰.besselHaar
  rw [eq_comm, lintegral_lintegral_swap, lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow
    (lintegral_mul_left_eq_self _ ⟨·, unipotentBelow_le_besselU ·⟩ |>.symm.trans (by aesop)),
    lintegral_lintegral_swap, lintegral_congr fun y ↦ ?_, lintegral_mul_const,
    measurePreserving_freeEntries_besselHaar.lintegral_comp, lintegral_gaussian_eq_one, one_mul]
  all_goals first | fun_prop | simp (disch := first | fun_prop | simp [unipotentBelow_eq_besselU]) [
    lintegral_mul_const, ← lintegral_mconv_dirac, ← lintegral_dirac_mconv, lintegral_map,
    ascConv_heisenbergMeasure_invariant, lintegral_freeGaussian_ascConv]
  erw [freeGaussian, U.coe_inv IsHermInvolution.mul_self,
    ← sum_toFinset_eq_subtype _ (‖y.1.1.1.toRows₁ · ·‖ ^ 2).uncurry]
  simp [sum_filter, sum_prod_type, splitGram, middleGram, mul_apply]; ring

lemma exists_chart_ascConv_cellLaw j : ∃ g : (Fin j → ℂ) → 𝔰.G₁, Measurable g ∧ (∀ p : ℕ → ℂˣ, j ≤
  𝔰.n → g (p ·) = if j ≤ 𝔰.ϱ then weylElem j p else weylElem 𝔰.ϱ p * cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) ∧ ∀ X,
  Measurable X → ∫⁻ x, X x ∂ascConv cellLaw j = ∫⁻ z, (∏ a : Fin j, cellDensity 𝔰 a (z a)) * X
  (g z)⁻¹ := j.rec ⟨1, by simp! [measurable_one, univ_eq_empty, volume_pi]⟩ fun j ⟨g, m, e⟩ ↦
  ⟨fun z ↦ cellChart 𝔰 j (z (.last j)) * g (z ·.castSucc), by fun_prop,
  by simp! +contextual (disch := with_unfolding_all fun_prop) [lintegral_mconv, *, mul_assoc,
  (measurePreserving_piFinSuccAbove _ (.last j)).symm.lintegral_map_equiv, lintegral_prod_symm,
  volume_pi, lintegral_map, lintegral_withDensity_eq_lintegral_mul,
  Fin.prod_univ_castSucc]; grind [cellChart, weylElem_succ, (commute_weylElem cellChart_mem).eq]⟩
end

-- part: New.Filling.ColumnCoords
section
/-! Set-up for this proof: dictionaries between two encodings of the same objects.

This file: Dictionary between adelic groups and frame coordinates; columns in orthonormal
coordinates. -/
seal Finset.univ Finset.sum Finset.prod

open Equiv Grading Matrix

namespace Filling.Fits

attribute [local simp] adelicEquiv adelicToFin inclHFin basisScale inclX Shape.besselIndexEquiv
  U.map U.reindex U.sum Units.ext_iff toBesselH

variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} {ε l kw V Y η} [Frame 𝔰 ε]
  (h : S.Fits V l kw Y η)

lemma mem_unipotent_iff {g} : (g ∈ Y.unipotent ↔ h.adelicEquiv g ∈ besselU) ∧ (g ∈ Y.besselGroup ↔
  h.adelicEquiv g ∈ besselS) := by constructor <;> apply forall₂_congr <;> simp! [h.index_eq,
  gradeOf, FI.level, Functor.map, Space.ratCoordMatrix] <;> grind-ring -linarith

lemma adelicToFin_adelicEquiv_inclX a : S.adelicToFin (h.adelicEquiv (Y.inclX a)) =
  S.inclHFin a.2 := by
  simp [← ext_iff, h.index_eq, apply_ite Prod.snd]; and_intros <;> intros <;> first | rfl | grind

lemma finiteEquiv_inclX a : h.finiteEquiv (Y.inclX a).2 = S.inclHFin a.2 := by
  rw [finiteEquiv_eq_adelicToFin, adelicToFin_adelicEquiv_inclX, ((h.5 _).map _).inv_mul_cancel]

lemma adelicToInf_inclX a : S.adelicToInf (h.adelicEquiv (Y.inclX a)) = (toBesselH 𝔰 1 ⟨a.1 ·,
  @signMatrix_one .. ▸ (a.1 _).2⟩) := by
  ext _ (_ | (_ | _) | _) (_ | (_ | _) | _) <;>
    simp [h.index_eq, adelicToInf_apply, one_apply, apply_ite Prod.fst, ite_apply] <;>
    first | rfl | lia | (split_ifs <;> simp_all; lia)

/-- A linear isomorphism A from Weyl coordinates of type kw to Bessel coordinates with Av·W(gy)
= A(S_kw(gᵀ)v)·W(y) for g in ∏_v U(X₀), W the Bessel function, S_kw the Schur matrix. -/
noncomputable def weylBesselEquiv : {A : _ ≃ₗ[ℂ] _ // ∀ (g : _ → _) y v, A v ⬝ᵥ S.besselFn
  ((toBesselH 𝔰 1 <| g ·) * y) = A (schur kw (g · |>.1.1ᵀ) *ᵥ v) ⬝ᵥ S.besselFn y} := by
  choose A A' _ _ t using (h.1 · |>.2)
  let e := (funUnique Unit (WeylIndex 𝔰.κ kw)).symm.trans (piComm _)
  use toLinearEquivRight'OfInv (?_ : (kroneckerPi A').submatrix id e * (kroneckerPi A).submatrix e
    id = 1) ?_ <;> simp [← coe_refl, ← kroneckerPi_mul, *]
  intros; rw [← vecMul_transpose]; repeat erw [← dotProduct_mulVec]
  congr 1; ext; simpa [mulVec_eq_sum, Fintype.prod_sum, reindex_equiv e,
    schur_apply_eq_prod (κ := kw)] using! congr(∏ v, $(t v ..) _)

/-- The isomorphism from algebraic forms of weight (kw, 0) and level Kc on U(X₀) to ℓ²(classes ×
coordinates): evaluate at class representatives, then change coordinates by
`Filling.Fits.weylBesselEquiv`. -/
noncomputable def columnCoords : levelSpace (algFormRep kw 0) S.columnLevel ≃ₗ[ℂ] EuclideanSpace ℂ
  (S.Classes × S.BesselCoord) := freeLevelEquiv _ _ 1 S.aut_columnLevel ≪≫ₗ .piCongrRight (fun _ ↦
  h.weylBesselEquiv.1) ≪≫ₗ .symm (WithLp.linearEquiv .. ≪≫ₗ .curry ..)
end Filling.Fits
end

-- part: New.RealPlace.BesselCut
section
/-! Normalise a real-place Bessel function and cut it off. A Bessel function at a real place, an
average of a discrete series coefficient that is large at one point, inherits the coefficient's
decay, and normalising it and multiplying by a scalar cut-off gives a continuous approximant, close
in L² and compactly supported modulo the unipotent group, with an explicit tail bound. Averages of
integrable discrete series coefficients over a unipotent group and their decay are known, and the
normalisation and scalar cut-off with a tail bound are standard. Related work: Muić, Fourier
coefficients of automorphic forms and integrable discrete series, 2015; Miličić, Asymptotic behavior
of matrix coefficients of the discrete series, 1977; Wallach, Real Reductive Groups II, 1992.

Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData). -/
seal Finset.univ Finset.sum Finset.prod

open ENNReal Fintype Matrix MeasureTheory Set Norms.L2Operator

attribute [local simp] CStarRing.norm_mem_unitary_mul CStarRing.norm_mul_mem_unitary

variable {𝔰} {I : Type} {ε} [Fintype I] [p : Frame 𝔰 ε] {rep} {A : ℕ} {l : HCParam ε} {L : ℕ}

/-- Let F be Bessel, integrable on 𝖴\G₁, with F(y) = ∫ deg·ψ_λ(g⁻¹)F(yg) dg (unitary frame p, l
= 2λ with `HCParam.HasLargeGap`, |l_a| ≤ L, rank N). Then F has continuous iterated right
derivatives satisfying `HasSchurBound` with constant deg⁻¹‖F‖₂², for every B ≥
(N+1)⁴(L+N+1+2(ϱ+1)²). -/
lemma IsBesselFunction.hasSchurBound_of_convolve_eq (hg : l.HasLargeGap A) (hL : ∀ a, |l a| ≤ L) {F}
  (hW : IsBesselFunction (I := I) rep F) (h2 : Integrable F besselQuotMeasure) (B : ℝ) : let e :=
    (l.formalDegree * l.psiInFrame ·); convolve F e = F → (𝔰.r + 1) ^ 4 * (L +
    𝔰.r + 1 + (2 * 𝔰.n ^ 2 : ℕ)) ≤ B →
    HasSchurBound F rep B (.ofReal l.formalDegree⁻¹ * ∫⁻ y, ‖F y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  intro e fx H; obtain ⟨⟨β, hβ⟩, ⟨o, u, -⟩, k⟩ := exists_smear_dsCoeffSmooth_eq hg l.dsGenerator,
    hg.isUnitaryCasimirGe_dsAction, isIdempotentKernel_psiInFrame hg
  let π := frameEquiv (ε := ε); let γ w := (bumpDeriv.adTwist p.p⁻¹).word w β
  let S := smear l.dsCoeffSmooth.1; let X w g := l.formalDegree * S (γ w) (π g)
  have c := (fx ▸ hW.continuous_convolve k.2).comp π.3
  have hb : IsBoundedMeasurable e :=
    .of ⟨_, fun _ ↦ by grw [norm_mul, HCParam.psiInFrame, norm_dsCoeff_le_one hg]⟩ k.1
  have t w : Integrable (X w) ∧ convolve e (X w) = X w ∧ convolve F (X w) = smear _ c (γ w) ∘ π :=
    have z := measurePreserving_frameEquiv.integrable_comp_of_integrable (γ w).2.integrable; by
    rw [← show convolve e (_ ∘ π) = X w by
      ext; simp [X, S, e, π, convolve, ↓← integral_comp_frameEquiv, ← map_mul,
        mul_left_comm _ (l.formalDegree : ℂ)]; tauto, ← hb.convolve_assoc k.2 z, show convolve e e =
      e by ext; simpa [k.4] using! k.integral_inv_mul_translate _ 1, ← hW.convolve_assoc k.2 z, fx]
    use integrable_convolve k.2 z, rfl, by ext; simp [π, convolve, ← integral_comp_frameEquiv]
  use fun w ↦ ⟨_, hW.continuous_convolve (t w).1⟩, by simp [X]; erw [hβ, fx], fun w ↦ ?_
  let ⟨j, ex, a⟩ := t w; dsimp
  obtain ⟨x, -, b, s⟩ : ∃ x ∈ l.dsAction.filtration ε l.dsGenerator w.length,
      ‖x‖ ≤ ((𝔰.r + 1) ^ 4 * (L + 𝔰.r + 1 + w.length)) ^ w.length ∧ S (γ w) = x.1
  · refine w.rec ⟨_, GlModule.self_mem_filtration, u.le, hβ⟩ fun q w ⟨x, m, b, s⟩ ↦ ⟨_,
      ((isKHighest_dsGenerator hg).norm_apply_le_of_mem_filtration o (abs_lowestKType_le hg hL) m
      _).imp_right (⟨·.trans ?_, rightDeriv_smear _ _ s _⟩)⟩
    simp [inv_eq_left_inv p.2.1, p.2, l2_opNorm_single, pow_succ' _ w.length]
    grw [b]; gcongr <;> simp
  use ?_, fun g Z r h ↦ a ▸ .congr_deriv (hasDerivAt_smear _ _ c ?_) (by
    erw [(bumpDeriv.adTwist p.p⁻¹).apply_eq_sum Z]; simp [t, -smear_apply]; rfl), fun hw φ i ↦ ?_
  constructor <;> simp +contextual [hW.convolve_right j, convolve, mul_assoc, hW.2, hW.3, smul_comm
    (X w _), integral_smul, ← ContinuousLinearMap.integral_comp_comm, hW.integrable_smul j.comp_inv]
  simpa [π, frameEquiv, U.conj, mul_assoc] using (h.const_mul _).mul_const _
  grw [pow_mul', ← H, ← hw, ← b, show _ ^ 2 = (∫ g, ‖X w g‖ ^ 2) / l.formalDegree by
    simpa [X, s, π, field, Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal,
    mul_pow, ← integral_comp_frameEquiv] using! congr($(hg.toL2_spec.2.2 x x 1).re),
    ← hW.lintegral_sq_convolve_convolve_le rfl ?_ hW.2 h2 j k ?_ fx hb ex i] <;> simp [convolve,
    HCParam.psiInFrame]

/-- Given a peaked Bessel function (`HasPeakAt`) at x with `besselSize` x ≤ b^{5(ϱ+1)}, and
numerical bounds
on b, n, l, there are F, reproduced by convolution with deg·ψ_l, and V such that (F, V) satisfies
`IsCutPair`.

Normalise a real-place Bessel function and cut it off. -/
lemma HasPeakAt.exists_cut_isCutPair (hg : l.HasLargeGap A) {L : ℕ} (hL : ∀ a, |l a| ≤
  L) f [NeZero f] {n Y b x}
  (H : HasPeakAt (I := I) l rep Y x (b ^ n)) (hR : besselSize x ≤ b ^ (5 * 𝔰.n)) (b2 : 2000 ≤ b)
  (hM : n + 99 * 𝔰.r ^ 2 ≤ 𝔰.r ^ 3) (hb : 𝔰.r + L + 1 ≤ b ^ 4) (hf : 3 * 𝔰.r ^ 3 * f ≤ A) : ∃ F V :
  C(_, _), convolve F (l.formalDegree * l.psiInFrame ·) = F ∧ IsCutPair b f rep (·.rec F V) := by
  let M := 8 * 𝔰.r ^ 2 + 1; let B := {g : 𝔰.G₁ | ‖g.1.1 - 1‖ ≤ 1}
  obtain ⟨⟨_, b3, b8, b9, _⟩ : 1 ≤ b ∧ 2 ≤ b ∧ 8 ≤ b ∧ 16 ≤ b ∧ 0 < 𝔰.r ^ 2, _, ⟨hY, fx, h0, hS, z⟩,
    d, i, j⟩ := by bound, H.stronglyMeasurable, H, formalDegree_pos hg,
    integral_tail_le hL (M * 2) (by lia)
  have a (g : 𝔰.G₁) : ‖(frameEquiv g).1.1‖ = ‖g.1.1‖ := by simp [frameEquiv, U.conj,
    inv_eq_left_inv p.2.1, p.2]
  have k {n} (o : n ≤ A) g : ‖l.psiInFrame g‖ ≤ _ := a g ▸ norm_dsCoeff_le_pow (c :=
    M * 2 + n) hg (by delta gapThreshold; norm_cast; lia) _; let C : ℝ≥0∞ := .ofReal (16 ^ M)
  let ω c (g : 𝔰.G₁) : ℝ≥0∞ := .ofReal ((2 / ‖g.1.1‖) ^ c); let R := b ^ (6 * 𝔰.n + 2)
  let φ := ω (M * 2); let Φ y := ∫⁻ s, φ (x⁻¹ * (s.1.1 * y)) ∂𝔰.besselGraphMeasure
  have j : .ofReal l.formalDegree * (∫⁻ g, φ g) * (C * C) ≤ .ofReal b ^ (99 * 𝔰.r ^ 2) := (by
    simp_rw [φ, ω, C, ← a]; grw [lintegral_const_mul_le, (ofReal_mul d.le).ge,
    (measurePreserving_frameEquiv.lintegral_comp (by fun_prop)).trans
      (ofReal_integral_eq_lintegral_ofReal i (.of_forall
    fun _ ↦ by positivity)).symm, j, hb, b2, b8, b3, b9]
    simp (disch := positivity) only [← pow_mul, ← pow_add, ← pow_succ', ← ofReal_mul, ← ofReal_pow]
    gcongr; lia); have := fx ▸ hY.continuous_convolve (isIdempotentKernel_psiInFrame hg).2
  have r {y} (s : 𝔰.besselGraph) (h : ‖(x⁻¹ * (s.1.1 * y)).1.1‖ ≤ b * 2) : besselSize y + 1 ≤
    R := by
    grw [← besselSize_besselS_mul (besselGraph_fst_mem_besselS s), besselSize_le_norm_mul x, hR, h,
      add_one_le_two_mul, b3, b3]
    ring_nf!; repeat bound
  have hB {g} (h : g ∈ B) : ‖g.1.1‖ ≤ 16 := by grw [norm_le_insert' _ 1, h.out]; bound
  have w := @ENNReal.div_mul_cancel (volume B) C (measure_sublevel_ne_zero _)
    (measure_ball_ne_top_of_isProperMap _ .monoidHom_id 1)
  let μ := (C / volume B * (.ofReal (b ^ n) * ‖Y x‖ₑ)) • volume.withDensity (ω M)
  have m := show μ univ ≤ _ by simp [μ]; grw [show lintegral _ (ω M) ≤
    C * volume B from (lintegral_decay_le _ .monoidHom_id .refl
    1).trans_eq' (by simp [ω, M]), mul_right_comm, mul_left_comm _ C, w]
  have S y O (o : {g | besselSize (y * g) ≤ R} ⊆ O) : Φ y ≤ μ O := by
    grw [Measure.smul_apply, ← z, smul_eq_mul, mul_right_comm, ← lintegral_const_mul _ (by
      fun_prop)]; simp_rw [Φ, φ, ω, a]; gcongr with s; set t := x⁻¹ * _
    grw [← withDensity_apply_le, ← lintegral_mono_set (s := (t * ·) ⁻¹' B) fun g h ↦ o ((r s (by
      grw [← mul_assoc _ y, ← mul_assoc, hB h.out]; bound)).trans' (by simp)),
      ← setLIntegral_mono (by fun_prop) fun g h ↦ ?_, setLIntegral_const, measure_preimage_mul,
      mul_left_comm, w, ← ofReal_mul, ← mul_pow, div_mul_cancel₀, pow_mul, sq, ofReal_mul] <;>
      (try positivity); grw [div_div, ← hB h.out, ← U.norm_inv t, ← norm_mul_le] <;> simp
  have h5 := show ‖Y x‖ₑ ^ 2 ≤ _ by
    grw [← fx, convolve, enorm_integral_le_lintegral_enorm, sq_lintegral_le ?_ ?_ fun t ↦
      (?_ : _ ≤ φ t * .ofReal l.formalDegree ^ 2 * (‖Y (x * t)‖ₑ ^ 2 * φ t)),
      lintegral_unfold_besselGraphMeasure (_ * φ ·), congr(‖Y $(mul_inv_cancel_left ..)‖ₑ).le,
      (hY.enorm_besselS_mul (besselGraph_fst_mem_besselS _) _).le, (lintegral_const_mul _ ?_
    ).trans_le (mul_le_mul' le_rfl (S _ univ le_top)), m, lintegral_mul_const, lintegral_mul_const]
    <;> (try fun_prop); grw [enorm_smul, ← ofReal_norm, norm_mul, k zero_le, U.norm_inv]
    simp [abs_of_nonneg, φ, ω, d.le]; ring_nf; rfl
  have iY : Integrable Y besselQuotMeasure := ⟨by fun_prop, (lintegral_mono hS).trans_lt
    (lintegral_unfold_besselGraphMeasure (‖l.psiInFrame ·‖ₑ) (by fun_prop) ▸
    ((integrable_const_mul_iff (by simp [d.ne']) _).1 (isIdempotentKernel_psiInFrame hg).2).2)⟩
  obtain ⟨q, hq⟩ : ∃ q, _ = ofNNReal q := ⟨_, lintegral_enorm_sq iY hY.memLp_top⟩
  simp [↓hq, sq, ← mul_assoc, ENNReal.mul_le_mul_iff_left, h0] at h5
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ‖c‖ₑ ^ 2 * q = card I := ⟨(card I / q).sqrt, by
    rw [NNReal.enorm_eq]; norm_cast; simp [show q ≠ 0 from (by simp [·, h0] at h5)]⟩
  let χ t := 0 ⊔ 1 ⊓ (R - t); let F : C(_, _) := .mk (c • Y ·)
  let V : C(_, _) := .mk fun y ↦ χ (besselSize y) • F y
  have v {y} : ‖V y‖ₑ ≤ ‖F y‖ₑ ∧ ‖(χ (besselSize y) - 1) • F y‖ₑ ≤ ‖F y‖ₑ := by
    simp [V, χ, norm_smul, enorm_le_iff_norm_le, mul_le_of_le_one_left, abs_le]
  refine have nF := by simp [F, enorm_smul, mul_pow, lintegral_const_mul', *]
    have G y := by
      dsimp [F, Φ, φ, ω]; grw [enorm_smul, mul_left_comm, hS, lintegral_const_mul_le]; gcongr with s
      grw [← ofReal_norm]; split; grw [k zero_le]; simp; grw [← ofReal_mul (by bound), k hf,
      pow_add, mul_left_comm, ← mul_pow, ← mul_div_assoc, div_le_one_of_le₀ (le_of_not_ge
      (mt (r s) (‹¬_› <| by simp [inf_of_le_left, F, V, χ, le_sub_iff_add_le', ·])))] <;> simp
    have Z := by dsimp; grw [m, lintegral_const_mul, ← lintegral_unfold_besselGraphMeasure, h5,
      ← hc, ← hM, ofReal_pow,
      ofReal_pow, pow_mul', pow_add, ← j] <;> first | positivity | fun_prop | ring_nf; rfl
    ⟨F, V, by simpa [F, funext_iff, convolve, smul_comm _ c, integral_smul]
      using congr(c • $fx), ?_, iY.smul c, nF, by grw [v.1, nF], by simp +contextual [V, χ, R,
      le_of_lt], ?_, (‖c‖ₑ * Φ ·), ‖c‖ₑ • μ, by fun_prop, fun s h y ↦ congr(_ * $(.trans
      (by simp [mul_assoc]) (lintegral_mul_right_eq_self _ (𝔰.besselGraphChart (⟨s, h⟩, 1))))),
    (·.rec G (by grw [v.1, G ·])), (by simp; grw [← S · _ .rfl]), ⟨by simp; grw [m]; finiteness⟩, Z⟩
  rintro ⟨⟩ <;> use ⟨by fun_prop, hY.bounded.imp' _ fun _ k y ↦ .trans (b := ‖F y‖)
    (by simp [← enorm_le_iff_norm_le, v]) (by erw [norm_smul]; grw [k])⟩ <;> simp +contextual [F,
    V, besselSize_besselS_mul ∘ mem_unitriGroup_of_mem_besselU, besselSize_besselS_mul
    (mem_unitriGroup_of_mem_floorGroup (toBesselH_mem _)), hY.2, hY.3, smul_comm (wave _)]
  grw [← ENNReal.mul_le_mul_iff_right (a := .ofReal (b ^ (3 * 𝔰.r ^ 3 * f)) ^ 2), ← mul_assoc,
    ← mul_pow, ← ofReal_mul, ← @ofReal_pow (_ * _), ← Z.trans (mul_le_mul' ?_ le_rfl),
    lintegral_const_mul_le, ← lintegral_const_mul _ (by fun_prop), lintegral_mono fun y ↦ ?_] <;>
    try finiteness
  dsimp at *; grw [← S y univ le_top, ← sq, ← G]; split; simp [*]
  grw [← mul_pow, ← v.2, sub_smul, one_smul]; rfl
  gcongr; simp [field, ← pow_add, ← pow_mul, -card_sum]; gcongr; nlinarith [NeZero.pos f]
end

-- part: New.RealPlace.ComplexGauge
section
/-! Part of: Tower method: pairings of kernels bounded floor by floor (see
New.RealPlace.LocalTheorem).

This file: Tower measure at C is Haar with constant bound; level and gauge at C. -/

open Fin Sum Complex ComplexOrder ENNReal EuclideanSpace Filling Fintype Level Matrix MeasureTheory
  Metric ProbabilityTheory Real Set Shape Size WithLp Fin.NatCast MeasureTheory.Measure
  Norms.L2Operator

/-- The numerical hypotheses at a real place: ρ = b^(6n+2) ≥ 8r with b ≥ 2, |κ| = s + 3n + 2 ≥
n⁷, s > 10⁹n³ and ϱ ≥ 10⁸. Here ϱ counts the hyperbolic planes of the `Shape`, n = ϱ + 1, κ
indexes the basis of the summand X₀ and r is the rank of the whole space. -/
structure RealPlaceSizes (𝔰 : Shape) ρ s (b : ℝ) where
  rho_eq : ρ = b ^ (6 * 𝔰.n + 2)
  eight_mul_r_le_rho : 8 * 𝔰.r ≤ ρ
  k_eq : 𝔰.k = s + 3 * 𝔰.n + 2
  mul_cube_lt_s : 10 ^ 9 * 𝔰.n ^ 3 < s
  pow_seven_le_k : 𝔰.n ^ 7 ≤ 𝔰.k
  ten_pow_le_varrho : 10 ^ 8 ≤ 𝔰.ϱ
  two_le_b : 2 ≤ b

variable {𝔰 ρ s b} (hF : RealPlaceSizes 𝔰 ρ s b) {L : ℝ}

/-- The level at ℂ: Haar probability measure on U(X₀), g = 1, the open Euclidean ball of radius
1/4, the box of elements of operator norm ≤ ρ, all positions. -/
@[simps toHyperbolicBasis θ measureH g 𝔅 boxSet
  positions] noncomputable def RealPlaceSizes.complexLevel :
  Level {i // i ≠ 𝔰.k₀} (𝔰.middleGram (1 : ℂ)) 0 := by
  refine ⟨complexBasis 𝔰, cellLaw 𝔰.ϱ ∗ₘ volume.map embedH, volume.map embedH, 1, toLp 2 ⁻¹'
    Metric.ball 0 4⁻¹, {x | ‖x.1.1‖ ≤ ρ}, .univ, ⟨ae_mem_mconv ?_ ?_, map_orbitPoint_cellLaw_top
    ?_⟩, ?_, ?_, ⟨isOpen_ball.preimage (by fun_prop), ?_, ((PiLp.antilipschitzWith_toLp 2
    _).isBounded_preimage isBounded_ball).isCompact_closure⟩, isCompact_U_norm_le _, .univ⟩ <;>
    simp +contextual (disch := with_unfolding_all first | fun_prop | exact measurableSet_floorGroup)
    [↓ae_map_iff, cellChart_mem, embedH_mem_floorGroup, prob_le_one, hF.k_eq]
  intro _ _ h; erw [(exists_toBesselH_eq h).choose_spec, ← map_dirac,
    ← map_mconv_monoidHom (toBesselH 𝔰 1), mconv_dirac, map_mul_right_eq_self]; fun_prop

/-- A chosen constant λ in [0, ∞] such that the measure 𝖬 of the level at ℂ is λ times the Haar
measure of G₁. -/
noncomputable def RealPlaceSizes.haarRatio :=
  (exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose

/-- For the level at ℂ, λ = `RealPlaceSizes.haarRatio` has 0 < λ < ∞, 𝖬 = λ·dy, ∫ f d(θ_n ∗ ⋯ ∗ θ₀)
= λ∫_{𝖴\G₁} f for measurable left 𝖴-invariant f ≥ 0, and λ·vol U(k)/vol U(r) ≤ 1, k = |κ|. -/
lemma RealPlaceSizes.haarRatio_spec : (hF.haarRatio ≠ 0 ∧ hF.haarRatio ≠ ∞) ∧
  hF.complexLevel.groupMeasure = hF.haarRatio • ℙ ∧ (∀ f, Measurable f → besselU.FixesLeft f → ∫⁻ g,
  f g ∂hF.complexLevel.upperMeasure 0 = hF.haarRatio * ∫⁻ g, f g ∂besselQuotMeasure) ∧ .ofReal
  (volU 𝔰.k / volU 𝔰.r) * hF.haarRatio ≤ 1 := by
  obtain ⟨s, e : _ = hF.haarRatio • _, _, g, _, eg, ig⟩ := isCompact_U_norm_le (J := 𝔰.J₁) 2,
    (exists_eq_smul_haar volume hF.complexLevel.isMulRightInvariant_groupMeasure).choose_spec,
    hF.k_eq, @exists_chart_ascConv_cellLaw 𝔰 𝔰.n
  have w l : l ≤ 𝔰.ϱ → descConv hF.complexLevel.floorMeasure 0 𝔰.n =
    ascConv cellLaw l ∗ₘ descConv hF.complexLevel.floorMeasure l (𝔰.ϱ - l + 1) ∗ₘ
    ascConv complexPlace.heisenbergMeasure l := l.rec (by simp [ascConv]) fun l ih h ↦ by
    rw [ih, descConv_floorMeasure_succ, ascConv, ascConv_heisenbergMeasure_succ]
    delta cellLaw cellChart cellDensity; simp [Place.weylLaw, mconv_assoc,
      ← pow_mul]; all_goals grind
  have n := by simpa [stackMeasure_zero_eq, ascConv, ascConv_heisenbergMeasure_eq_besselHaar] using
    e
  suffices _ from ⟨⟨(by simp [·, stackMeasure_ne_zero] at e), (by simp [·] at this)⟩, e,
    fun F f j ↦ by simpa using (identDistrib_orbitMeasure_of_unfold (.id _) (.comp ⟨measurable_mul,
    n⟩ (.comp (.prod ⟨by fun_prop, rfl⟩
    (.id _)) measurePreserving_swap)) f measurable_id (j _ ·.2)).lintegral_eq.symm, this⟩
  -- one test function is enough: the indicator f of a ball
  rw [← ENNReal.mul_le_mul_iff_left (measure_sublevel_ne_zero volume) s.measure_ne_top, one_mul,
    ← lintegral_indicator_one s.measurableSet, ← smul_eq_mul, mul_smul,
    ← lintegral_smul_measure, ← n, ← map_inv_eq_self besselHaar, descConv_succ, w _ le_rfl]
  set f := @indicator _ ℝ≥0∞ _ _ 1
  have : Measurable f := by measurability
  have j h k g : f (embedH h * (embedH k * g)⁻¹) = f g := by
    simp [f, indicator, ↓U.norm_inv, ↓norm_embedH_mul, -_root_.mul_inv_rev]
  refine le_lintegral_of_gramSection ‹_› fun k ↦ (lintegral_indicator_le ..).trans' ?_
  erw [← lintegral_bruhat_coords, lintegral_mconv_symm]
  simp [descConv, floorMeasure, ← mconv_assoc, ascConv_heisenbergMeasure_eq_besselHaar, besselHaar,
    ← ascConv.eq_2, ← lintegral_const_mul']
  simp (disch := with_unfolding_all fun_prop) only [ig, lintegral_mconv, lintegral_map]
  refine lintegral_le_const (.of_forall fun t ↦ lintegral_mono_ae
    ((ae_all_iff.2 (ae_eval_ne _ · 0)).mono fun c z ↦ ?_))
  by_cases! h : ‖c (last _)‖ ≤ 1; simp [cellDensity, prod_univ_castSucc, *]
  have D x h b := @(((measurePreserving_conj_bessel mem_besselU0_iff_apply
    besselS_le_normalizer_besselU0 (mem_besselS.2 ⟨_, liftUnitri_mem_besselU x, _, toBesselH_mem h,
    rfl⟩)).mul_left 𝔰.besselHaar₀ ⟨_,
    (besselS_le_normalizer_besselU0 (mem_unitriGroup_of_mem_besselU (liftUnitri_mem_besselU x)) _).1
    (unipotentOf_mem_besselU0 b)⟩).comp (measurePreserving_inv _)).lintegral_comp
  have e := by simpa using eg (.mk0 _ <| z ·)
  have Z γ (v : realFrameGram γ = realFrameGram (g c)) x y :
    realFrameGram ((liftUnitri x)⁻¹ * γ * liftUnitri y) = (unitriMatrix x)ᴴ * Matrix.diagonal
    c * unitriMatrix y := by simp [↓frameGram_inv_mul_mul, ↓frameGram_weylElem_mul,
    realFrameGram_cellChart, cellChart_mem, liftUnitri_mem_besselU, ← init_def, *]
  have B x y := congr($((frameDisc_frameGram_besselU_mul (liftUnitri_mem_besselU x)
    (liftUnitri_mem_besselU y) 1).trans (e ▸ frameDisc_weylElem_mul cellChart_mem 1)).re)
  simp only [Z, realFrameGram_cellChart h, RCLike.star_def, mul_conj'] at B; norm_cast at B
  have o x y := mem_openCell_iff.2 ((B x y).trans_gt (by simpa [-Units.coe_prod]))
  simp [lintegral_const_mul', ← mul_assoc, row, gramDiscReal, B, o]
  gcongr 1; clear * - h
  simp (disch := bound) [cellDensity, prod_univ_castSucc, ENNReal.ofReal_mul', openCellConst,
    pow_add, ← norm_prod, enorm, Finset.prod_pow]; ring; rfl
  erw [@lintegral_lintegral_swap (_ × _)]; gcongr with w
  repeat erw [lintegral_prod]
  gcongr with x; rw [lintegral_lintegral_swap, lintegral_prod]; gcongr 1 with y
  obtain ⟨q, p, b, r, e⟩ := exists_eq_mul_gramSection_mul (o x y) (Z (embedH w⁻¹ * g c * embedH t⁻¹)
    (by simp [realFrameGram_mul_invariant, Subgroup.mem_sup_right]) ..)
  rw [← D y (r * w⁻¹) b]; gcongr 1
  rw [← D x (p * k⁻¹) q]
  simp [← j (r * w⁻¹) (p * k⁻¹) (_ * a.1⁻¹), eq_inv_mul_of_mul_eq e]; group; rfl
  all_goals fun_prop (disch := exact isOpen_openCell.measurableSet)

instance :
  hF.complexLevel.groupMeasure.IsHaarMeasure := by simp [hF.haarRatio_spec, IsHaarMeasure.smul]

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

attribute [local simp ←] ofReal_coe_nnreal ENNReal.ofReal_mul ENNReal.ofReal_pow dotProduct_mulVec

attribute [local simp] star_mulVec MeasureTheory.volume_pi_closedBall Size.vecsOfSize inclMatrix
  pi_norm_le_iff_of_nonneg

/-- Let n = ϱ+1, |ι| = s+1+3n ≤ L, L ≥ 4, and rank C ≤ 3n. Some matrix O with orthonormal
columns has CO = 0 and, for all j, the integral of (36/|Oᴴu|²)^s over the u in ℂ^ι with all
|u_i| ≤ L^j is at most L^{198n(j+1)}. -/
lemma exists_orthonormal_ker_lintegral_le {m ι : Type} [Fintype m] [Fintype ι] (C : Matrix m ι ℂ)
  (_ : card ι = s + 1 + 3 * 𝔰.n) (h4 : 4 ≤ L) (_ : C.rank ≤ 3 * 𝔰.n) (c : card ι ≤ L) : ∃ (D :
  Finset ι) (O : Matrix ι D ℂ), C * O = 0 ∧ Oᴴ * O = 1 ∧ ∀ j, ∫⁻ u in {u | ∀ i, ‖u i‖ ≤ L ^ j},
  (.ofReal (‖star (Oᴴ *ᵥ u) ⬝ᵥ Oᴴ *ᵥ u‖ / 36))⁻¹ ^ s ≤ (.ofReal L ^ 2) ^ (99 * 𝔰.n * (j + 1)) := by
  have H := C.isHermitian_conjTranspose_mul_self; let Q := H.eigenvectorUnitary
  let ⟨D, hD, d⟩ := @Finset.exists_subset_card_eq _ {i | H.eigenvalues i = 0} s.succ (by grind
    [card_subtype_compl, card_subtype, H.rank_eq_card_non_zero_eigs, rank_conjTranspose_mul_self])
  use D, Q.1.submatrix id (↑), (conjTranspose_mul_self_mul_eq_zero ..).1 (ext fun a i ↦
    congr($(H.mulVec_eigenvectorBasis i) a).trans (by simp; grind)), ext (congr($(Q.2.1) · ·).trans
    (by simp)), fun j ↦ .trans' ?_ ((lintegral_mono_set fun u h ↦ ?_).trans_eq
    (((((@measurePreserving_normSq_sphereDensity _ _ (D.card_pos.1 ?_).coe_sort).prod (.id _)).comp
    (volume_preserving_piEquivPiSubtypeProd ..)).comp (complexPlace.measurePreserving_mulVec Q.1ᴴ
    (det_of_mem_unitary (star Q).2).1)).setLIntegral_comp_preimage (f := fun p ↦
    (.ofReal (p.1 / 36))⁻¹ ^ s) (s := Iic (L * (L * L ^ j) ^ 2) ×ˢ closedBall 0 (L * L ^ j)) ?_ ?_))
  erw [setLIntegral_prod_symm]; simp [restrict_withDensity, Iic_inter_Ioi]
  grw [lintegral_withDensity_le_lintegral_mul, setLIntegral_le_iSup_mul,
    iSup₂_le (a := .ofReal (4 * 3 ^ 144))]
  · simp (disch := positivity) [*]
    grw [pi_gt_three, pi_le_four, pi_le_four, h4, h4, h4]; ring; gcongr <;> bound
  simp; intros
  grw [← exp_one_lt_three, exp_one_pow, ← pow_div_factorial_le_exp _ _ s, pi_le_four]
  simp (disch := finiteness) [← toReal_le_toReal, field, pow_succ, div_pow, d, ← mul_pow]; bound
  any_goals measurability
  have k i : ‖(Q.1ᴴ *ᵥ u) i‖ ≤ L * L ^ j := (norm_sum_le ..).trans (by
    simp; grw [entry_norm_bound_of_unitary Q.2, h _, ← c]; simp)
  simp (disch := positivity) [k, ↓star_dot_self_eq_norm_sq, norm_sq_eq]
  grw [k, ← c, ← D.card_le_univ]; simp

lemma RealPlaceSizes.ten_le (hF : RealPlaceSizes 𝔰 ρ s b) : 4 ≤ ρ :=
  hF.eight_mul_r_le_rho.trans' (by simp; bound)

/-- For L ≥ ρ, the gauge of the level at ℂ with sizes B_j = {x : |x| ≤ L^j} and constant Λ = L². -/
noncomputable def RealPlaceSizes.gauge (hF : RealPlaceSizes 𝔰 ρ s b) (hρ : ρ ≤ L := by rfl) :
  Gauge hF.complexLevel := by
  obtain ⟨hk, _, h4⟩ := hF.k_eq, hF.eight_mul_r_le_rho, hF.ten_le.trans hρ
  refine ⟨⟨fun j ↦ {x | ‖x‖ ≤ L ^ j}, ?_, fun c k ↦ by
    rify at c; simp_all [pow_succ']; grw [norm_sum_le, k]; simp; bound, ?_, ?_, by simp [
    inv_eq_left_inv IsHermInvolution.mul_self,
    (entry_norm_bound_of_unitary IsHermInvolution.mem_unitary ..).trans, h4.trans']⟩,
    .ofReal L ^ 2, fun _ ↦ by simpa [closedBall] using isCompact_closedBall (0 : ℂ) _, ?_, ?_, by
    simp [HasMatSize, apply_ite, complexBasis]
    grind [norm_add_le, norm_one, norm_I], by simp +contextual [HasMatSize, (norm_apply_le_l2_opNorm
    ..).trans, hρ.trans'], fun u h i ↦ by simp_all; grind [PiLp.norm_apply_le (toLp 2 u) i], ?_, by
    simp (disch := positivity) [← mem_closedBall_zero_iff, -mem_closedBall]
    grw [pi_le_four, h4]; ring; bound, fun σ _ j _ h ↦ .trans_eq ?_ (mul_one _), ?_⟩
  iterate 6 simp (disch := positivity) [pow_add, ← ofReal_norm, pow_right_comm, abs_of_pos] <;>
    bound [two_le_pi, sq_nonneg (L - 1)]
  · grw [Measure.map_apply, prod_apply_symm, complexPlace_skewMeasure, lintegral_map_le,
      ← lintegral_cauchyPDF_eq_one 0 one_ne_zero, ← lintegral_const_mul]
    gcongr with r; grw [measure_mono (t := closedBall 0 (2 * L ^ j / ‖r + Complex.I‖) ×ˢ
      closedBall 0 (L ^ j)) fun p h ↦ ?_]
    · simp (disch := positivity) [norm_eq_sqrt_sq_add_sq, volume_eq_prod, cauchyPDF,
        cauchyPDFReal, field]
      ring; grw [pi_le_four, pi_le_four, h4, h4, h4]; ring; bound
    simp (disch := positivity) [Place.flatChart, neg_add_eq_sub, mul_assoc,
      inv_def (starRingEnd ℂ _), ← mul_sub] at h ⊢; nth_grw 1 [← abs_im_le_norm (_ - _),
      le_div_iff₀ (by simp [Complex.ext_iff]), norm_add_le] at *
    simp_all [entrywise, ← Finset.sum_add_distrib, mul_comm]; linarith
    all_goals measurability
  let N := (1 - 𝔰.J₁).submatrix (.map id (inl ∘ inr)) id
  set e := hF.complexLevel.orthonormalPart
  intro x _ y _ v W
  refine (exists_orthonormal_ker_lintegral_le (fromRows v (fromRows (N * x⁻¹.1.1 * e) (N * (x *
    y)⁻¹.1.1 * e))) (by simp [volumeExponent, hk]; lia) h4 (by grw [rank_le_card_height]; simp; lia)
    (by simp_all; bound)).elim fun _ ⟨O, z, o, I⟩ ↦ ⟨_, by fun_prop, fun u ↦ ?_, I⟩
  clear * - z o
  generalize hr : star _ ⬝ᵥ Oᴴ *ᵥ u = r
  by_cases r = 0; simp [*]
  have B : closedBall 0 (|√‖r‖| / 9) ⊆ (star u ⬝ᵥ ·) '' W := fun t h ↦ by
    let w := O *ᵥ (t / r) • Oᴴ *ᵥ u
    have k {g : 𝔰.G₁} (a : N * g.1.1 * e * O = 0) : ‖toLp 2 (g.1.1 *ᵥ e *ᵥ w)‖ ≤ 9⁻¹ := by
      have n := congr(‖$(U.form_mulVec_mulVec g (e *ᵥ w) (e *ᵥ w))‖)
      rw [(by clear * -; simp [mulVec_eq_sum, funext_iff, N, splitGram, middleGram]; grind : ∀ z,
        N *ᵥ z = 0 →
        𝔰.J₁ *ᵥ z = z) _ (by simp [w, ← Matrix.mul_assoc, a]), star_dot_self_eq_norm_sq] at n
      simp [show eᴴ *
        (𝔰.J₁ * e) = 1 by ext; simp [e, complexBasis, mul_apply, splitGram, middleGram]; grind] at n
      simp_all [-mulVec_smul, w, ← Matrix.mul_assoc]; grw [← sq_le_sq₀, n, h, h] <;> simp [field]
    use w, ⟨by simp [-mulVec_smul, w, show v * O = 0 from congr(toRows₁ $z)], (by simp; grind
      [norm_sub_le] : _ → _ → _) (k congr($z ∘ inr ∘ inl)) (k congr($z ∘ inr ∘ inr))⟩; simp_all [w]
  grw [← B, measure_mono (t := closedBall 0 (3 / |√‖r‖|)) fun t h ↦ ?_]
  simp (disch := positivity) [field]; bound [pi_le_four, pi_gt_three]
  obtain ⟨c, w, ⟨z, a, y, b, o⟩, e⟩ := @norm_inner_J₁_le 𝔰,
    (@B (|√‖r‖| / 9) (by simp)).imp (And.imp_left <| h ·)
  replace o := congr(‖$o‖).le
  simp [e, ← mem_ball_iff_norm', dotProduct_comm (star _), inner_toLp_toLp,
    (toLp_surjective 2).forall] at *
  grw [norm_sub_le, c, c, (norm_lt_of_mem_ball a.2).le, a.1.le, norm_lt_of_mem_ball b.2] at o
  simp [field]; bound
end

-- part: New.RealPlace.ComplexShells
section
/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Summing the local theorem over shells at C; explicit band bound for forms. -/

noncomputable section


open MeasureTheory Size Fintype Real Level Shape ENNReal Finset Gauge RealPlaceSizes
variable {j s : ℕ} {𝔰 : Shape} {I : Type} [Fintype I] (F : C(𝔰.G₁, EuclideanSpace ℂ I))
  {p q : ℕ → ℂˣ} {ρ L t ε b : ℝ} {rep F₀ n W}

/-- A pair (F₀, F) of a Bessel function and its cut satisfying `IsCutPair` b n, with numerical
conditions: ρ a fixed power of b, |κ| = s + 3(ϱ+1) + 2, and lower bounds on ρ, s, |κ|, ϱ, b. -/
structure IsCutBessel rep ρ s b F₀ n extends IsCutPair b n rep (·.rec F₀ F), RealPlaceSizes 𝔰 ρ s b

namespace IsCutBessel

variable {F} (hF : IsCutBessel F rep ρ s b F₀ n) (hj : j ≤ 𝔰.ϱ)

/-- The number (vol U(k)/vol U(r))/(λ|I|)², with k, r the ranks of X₀ and the whole space, and λ
= `RealPlaceSizes.haarRatio` the ratio of 𝖬 to the Haar measure of G₁. -/
def formConst := volU 𝔰.k / volU 𝔰.r / (hF.haarRatio.toReal * card I) ^ 2

lemma isCut_complexLevel : hF.complexLevel.IsCut F := have h := hF.isBesselFunction .cut
  ⟨⟨h.1, by simpa using h.2⟩,
    (_root_.exists_norm_le_of_besselSize_le <| hF.rho_eq ▸ hF.inCut_of_ne_zero _ ·)⟩

lemma volumeExponent_eq : hF.complexLevel.volumeExponent =
  s := by simp [Level.volumeExponent, hF.k_eq]

/-- For F satisfying `IsCutBessel`, some L ≥ ρ makes p, q heads of length j for the gauge of size
L, and L^K ≤ R^{(K+6)(2j+1)}·𝗁(p)𝗁(q), 𝗁 = `headWeight` K j, for every R ≥ ρ bounding all
|p₁⋯p_l|, |q₁⋯q_l|, l ≤ j. -/
lemma exists_gauge_isHead j p q K : ∃ L, ∃ h : ρ ≤ L, (hF.gauge h).IsHead j p ∧ (hF.gauge h).IsHead
  j q ∧ ∀ R ≥ ρ, (∀ l ≤ j, ‖(∏ a ∈ range l, p a).1‖ ≤ R ∧ ‖(∏ a ∈ range l, q a).1‖ ≤ R) →
  L ^ K ≤ R ^ ((K + 6) * (2 * j + 1)) * (headWeight K j p * headWeight K j q) := by
  have n {L B R} {x : ℂˣ} (c : L ^ K ≤ B) (h : ‖x.1‖ ≤ R) (_ : 1 ≤ L) (_ : 1 ≤ R) :
      max L ‖x.1‖⁻¹ ^ K ≤ B * (R ^ (K + 6) * dampedPower K ‖x.1‖⁻¹) := by
    grw [dampedPower, ← c, max_def, min_def]
    split_ifs <;> simp [field, pow_add] <;> (try grw [h]) <;> bound
  simp [IsHead, RealPlaceSizes.gauge, headWeight, -Units.coe_prod]
  refine' j.rec ⟨ρ, by simp; grw [← le_self_add]; bound [hF.ten_le]⟩
    fun j ⟨L, a, b, h, c⟩ ↦ ⟨_, _, _, _, fun R r z ↦ (n (n (c R r _) (z _ .refl).1 ..) (z _
    .refl).2 ..).trans_eq (by simp [prod_range_succ]; ring)⟩ <;> clear n <;> grind [hF.ten_le]

include hj

/-- Let F be cut, j ≤ ϱ, p, q heads for L ≥ ρ, W Bessel, supported on points near at j, ‖W‖₂² ≤
ε²|I|, ε ≥ 0, t ≥ 1, f ≤ `Level.formMajorant`, and f² ≤ (π^kρ^{24k}t^{−s})²`Gauge.selfNormProduct`
if t > 1. Then `IsCutBessel.formConst`·κ_j∫ f d𝖬 ≤ ΘL^{10⁹(ϱ+1)⁴}ρ^{24k}t^{9.9·10⁶(ϱ+1)³−s}ε, with k
= rank X₀, κ_j = `Level.headDensity`, Θ = `Shape.bandConst`. -/
lemma formConst_mul_lintegral_le [Nonempty I] (hW : Place.IsBessel W 1)
  (hε : ∫⁻ y, ‖W y‖ₑ ^ 2 ∂besselQuotMeasure ≤ .ofReal ε ^ 2 * card I) (ε0 : 0 ≤ ε) {hL : ρ ≤
  L} (hp : (hF.gauge hL).IsHead j p) (hq : (hF.gauge hL).IsHead j q) (hs : ∀ {y}, W y ≠ 0 →
  hF.complexLevel.IsNear j y) {f} (ht : 1 ≤ t) (hf : f ≤ hF.complexLevel.formMajorant j p q F W)
  (h : ∀ {x}, 1 < t → f x ^ 2 ≤ .ofReal ((π * ρ ^ 24) ^ 𝔰.k / t ^ s) ^ 2 *
  (hF.gauge hL).selfNormProduct j p q F W x) : ‖(hF.formConst : ℂ)‖ₑ * (hF.complexLevel.headDensity
  j p q * ∫⁻ x, f x ∂hF.complexLevel.groupMeasure) ≤ .ofReal (𝔰.bandConst * L ^ (10 ^ 9 * 𝔰.n ^ 4) *
  ρ ^ (24 * 𝔰.k) * t ^ (9900000 * 𝔰.n ^ 3) / t ^ s * ε) := by
  obtain ⟨⟨l, _, _⟩ : 2 ≤ L ∧ 1 ≤ ρ ∧ 1 ≤ L, c, _, ⟨_, _⟩, -, N, -⟩ := by bound [hF.ten_le],
    hF.isCut_complexLevel, one_le_two.trans two_le_pi, hF.haarRatio_spec
  let T i := t * L ^ (11 * 𝔰.n * i)
  have o i a b (h : a ≤ 11 * 𝔰.n * i * b := by lia) : L ^ a ≤ T i ^ b := by
    grw [h, pow_mul, ← one_mul (L ^ _), ht]
  have g i b := hL.trans (pow_one L ▸ o (.succ i) 1 (.succ b))
  grw [← mul_one (ENNReal.ofReal _), ← setLIntegral_univ, ← Set.iUnion_eq_univ_iff (f := fun i ↦
    (hF.gauge (g i (99 * 𝔰.ϱ + 98))).positionsOfSize).2 fun x ↦
    (pow_unbounded_of_one_lt _ (by linarith)).imp
    fun i e ↦ ⟨⟨⟩, fun _ _ ↦ (norm_apply_le_l2_opNorm ..).trans (e.le.trans ((o _ i _).trans_eq
    (pow_mul ..)))⟩, ← iUnion_disjointed, lintegral_iUnion_le, ← tsum_two_zpow_neg_add_one]
  simp [← ENNReal.tsum_mul_left, disjointed]; gcongr 1 with i; grw [lintegral_positions_le _ _ c hW
    hj hq (Θ := .ofReal ε * (hF.haarRatio * card I) ^ 2) ?_ sdiff_le (e := .ofReal
    ((π * ρ ^ 24) ^ 𝔰.k * ρ ^ (9999 * 𝔰.n) / T i ^ s)) fun x m ↦ ?_]
  have := @toReal_ne_zero
  simp (disch := finiteness) [RealPlaceSizes.gauge, floorModulus, ← toReal_le_toReal,
    *, T, formConst, bandConst, volU, field,
    mul_pow, ← pow_mul, abs_of_nonneg, ENNReal.zpow_sub, ENNReal.zpow_neg]
  nth_grw 1 [tsub_le_self, l, l, hL, ← hF.mul_cube_lt_s]; ring_nf; gcongr <;> omega
  repeat grw [Level.pairingNorm, (ofReal_norm _).ge, norm_inner_le_norm]
  simp +contextual [mul_pow, lintegral_mul_const, N, hW.2, c.law, -upperMeasure, enorm_smul,
    ← ofReal_norm (wave _), hW.stronglyMeasurable.enorm.pow, c.stronglyMeasurable.enorm.pow]
  grw [hε, hF.lintegral_sq_cut_le]; ring_nf; rfl
  by_cases i = 0 ∧ 1 < t; grw [h] <;> bound
  grw [hf x, formMajorant_sq_le _ c hW hj hp ⟨⟩
    (by grw [hF.gauge.floorMassLe_one ⟨j, by lia⟩ hasFibreBound_floorQuadric ·, volume_le]) (σ :=
    volume (Metric.ball (0 : ℂ) (T i)⁻¹)) (by bound) hs fun z _ a b d ↦ ?_, hF.volumeExponent_eq]
  gcongr; simp (disch := finiteness) [RealPlaceSizes.gauge,
    ← toReal_le_toReal]; ring_nf; gcongr <;> grind [RealPlaceSizes]
  cases i; simp_all [T, ht.antisymm', ← NNReal.coe_lt_one, not_lt_of_ge]
  contrapose m
  simpa using fun _ ↦ ⟨_, le_rfl, ⟨⟩, by simpa [RealPlaceSizes.gauge, HasMatSize] using!
    ((hF.gauge (g _ 0)).hasMatSize_sub_one_of_floorValues _ hj hp hq (by
    simpa [RealPlaceSizes.gauge] using fun _ _ ↦
      (o _ _ 1).trans') ((c.2 (by aesop)).imp fun u ⟨h, j⟩ ↦ ⟨h, (c.2 (by aesop)).imp fun v ⟨k, l⟩ ↦
    ⟨k, j, l, by simpa using (hasMatSize_box _ l).sub (hasMatSize_box _ j)⟩⟩)
    b d fun a h ↦ (Set.not_subset.1 (m ⟨a, h, measure_mono ·⟩)).elim fun c ⟨d, r⟩ ↦ ⟨.mk0 c
    (r <| by simp [·]; bound), d, by simp [RealPlaceSizes.gauge] at r ⊢; grw [← r, inv_inv]⟩)⟩

/-- If F satisfies `IsCutBessel`, j ≤ ϱ and p, q are sequences in ℂ^×, the majorant 𝓘_j⁺
(`Level.formMajorant`, both functions equal to F) has finite integral over G₁ for the measure 𝖬
of the level. -/
lemma lintegral_formMajorant_ne_top [Nonempty I] : ∫⁻ x, hF.complexLevel.formMajorant j p q F F x
  ∂hF.complexLevel.groupMeasure ≠ ∞ := (hF.exists_gauge_isHead j p q 0).elim fun _ ⟨_, a, b, _⟩ z ↦
  (z ▸ hF.formConst_mul_lintegral_le hj hF.isCut_complexLevel.1 (by simp [hF.lintegral_sq_cut_le])
  zero_le_one a b hF.isCut_complexLevel.isNear_of_ne_zero le_rfl le_rfl (by simp)).not_gt
  (by simp [headDensity, formConst, prod_eq_zero_iff, toReal_ne_zero, ne_of_gt, haarRatio_spec])

/-- For a cut F, j ≤ ϱ, |ω| ≤ 1: if `Level.formModulus`² ≤ (π/|y|)^{2(k−1)}·`Gauge.selfNormProduct`
at all positions in every gauge with head p, then |`IsCutBessel.formConst`·𝓘_j(p, q; ω)| ≤ Θ
b^{2000n⁹} ℓ_{k−n⁷}(1/|y|) 𝗁(p)𝗁(q), with ℓ = `dampedPower`, 𝗁 = `headWeight` n⁶ j, n = ϱ+1. -/
lemma norm_floorForm_le [Nonempty I]
    (y : ℂˣ) {ω} (hω : ∀ x, ‖ω x‖ ≤ 1) (h : ∀ Γ : Gauge hF.complexLevel,
  Γ.IsHead j p → ∀ {x}, hF.complexLevel.formModulus j p q F x ω ^ 2 ≤
  (complexPlace.c / complexPlace.md y) ^ card {i // i ≠ 𝔰.k₀} * Γ.selfNormProduct j p q F F x) :
  ‖hF.formConst * hF.complexLevel.floorForm j p q F ω‖ ≤ 𝔰.bandConst * b ^ (2000 * 𝔰.n ^ 9) *
  dampedPower (𝔰.k - 𝔰.n ^ 7) ‖y.1‖⁻¹ * (headWeight (𝔰.n ^ 6) j p * headWeight (𝔰.n ^ 6) j q) := by
  obtain ⟨⟨_, _, hp, hq, Z⟩, c, _, _, _, ⟨_, N⟩, K, k⟩ := hF.exists_gauge_isHead j p q (𝔰.n ^ 6),
    hF.isCut_complexLevel, hF.ten_le, y.norm_pos, hF.two_le_b,
    exists_add_of_le hF.ten_pow_le_varrho, exists_add_of_le hF.pow_seven_le_k
  grw [← ofReal_le_ofReal_iff, ofReal_norm, enorm_mul, enorm_floorForm_le]
  obtain z | Z := not_or_of_imp (Z (ρ ^ (9 * 𝔰.n)) (by bound))
  have := (formMajorant_sq_le _ c c.1 hj hp (x := ·) ⟨⟩ (σ := 0) (by tauto) le_top
    c.isNear_of_ne_zero fun _ _ _ u v ↦ z.elim fun l m ↦ ⟨minors_mem_ofSize hF.gauge.hasMatSize_box
    hj u (c.isNear_of_ne_zero (by aesop)).choose_spec l m, minors_mem_ofSize hF.gauge.hasMatSize_box
    hj v (c.isNear_of_ne_zero (by aesop)).choose_spec l m⟩)
  simp_all [hF.volumeExponent_eq, hF.mul_cube_lt_s.ne_zero,
    (c.formModulus_le_formMajorant _).antisymm]
  let t := 1 ⊔ ρ ^ 24 * ‖y.1‖
  grw [hF.formConst_mul_lintegral_le hj c.1 (by simp [hF.lintegral_sq_cut_le]) zero_le_one hp hq
    c.isNear_of_ne_zero le_sup_left (fun _ ↦ c.formModulus_le_formMajorant hω) fun m ↦ ?_,
    (?_ : _ * _ ≤ 𝔰.n ^ 6), Z, ← (?_ : 9900000 * 𝔰.n ^ 3 + (K + 6) ≤ s), hj, dampedPower, k,
    ← (by simp [field, t] : ρ ^ 24 / t ≤ _⁻¹), ← (by simp [field, t]; bound : t⁻¹ ≤ 1 ⊓ _)]
  gcongr 1; simp [field, pow_add, div_pow, hF.rho_eq]; ring_nf
  simp [mul_assoc, ← pow_add]; gcongr
  any_goals first | clear Z; delta headWeight dampedPower bandConst volU; positivity
                  | rw [hF.k_eq, Shape.n, N] at *; lia | bound
  grw [h _ hp, hF.volumeExponent_eq.ge.trans tsub_le_self, max_eq_right (by grind)]
  gcongr 1
  simp (disch := finiteness) [← ofReal_norm, ← toReal_le_toReal, div_pow, field]
  ring_nf; repeat bound [two_le_pi]
end IsCutBessel
end
end

-- part: New.RealPlace.BandLimits
section
/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Band limits and energy bound for cut Bessel function at a real place. -/


open Matrix MeasureTheory Measure Fintype Real ENNReal InnerProductSpace Finset IsCutBessel Function
  Norms.L2Operator Level Gauge
variable {𝔰 : Shape} {s I} [Fintype I] {rep ρ b n} {F W : C(𝔰.G₁, EuclideanSpace ℂ I)}
  (hF : IsCutBessel F rep ρ s b W n) {p}

variable (F) in
/-- The vector Ξ(p) = ω(p)J_F(γ_p) (`normCorrelation`), with γ_p = w_{(p₁,…,p_ϱ)}·w_ϱ(p_n/min(1,
|p_n|)), n = ϱ+1, and w_ϱ the boost `cellChart`. -/
noncomputable def sieveVector p := normCorrelation (cellChart 𝔰 𝔰.ϱ (p 𝔰.ϱ)) F p

include hF
attribute [local simp] weylRatio ContinuousLinearMap.inner_map_map_of_mem_unitary upperPairing
  Unitary.map_mem cellDensity sqrt_eq_zero' abs_of_pos normCorrelation embedH_mem_floorGroup
  cellChart_mem weylElem_mul_left_comm

/-- If F satisfies `IsCutBessel`, the normalised Bessel integral Ξ(p) = `sieveVector` F p is a
continuous function of p. -/
lemma IsCutBessel.continuous_sieveVector : Continuous (sieveVector F) := .of_at fun p ↦ by
  choose L _ a _ using hF.exists_gauge_isHead _ p p 0
  refine have : Continuous fun c : (_ → ℂˣ) × 𝔰.G₁ ↦ cellChart 𝔰 𝔰.ϱ (c.1 𝔰.ϱ) :=
      continuous_U_iff_matrix.2 (.congr ?_ fun _ ↦ by simp [cellChart, field]; rfl); .smul
      (M := ℝ) ?_ (((PiLp.continuous_toLp ..).comp_continuousOn (continuousOn_pi.2 fun i ↦
      continuousOn_integral_of_compact_support (hF.gauge (by grind : _ ≤ L + 1)
    ).isCompact_hasMatSize ?_ fun c y m ↦ not_imp_comm.1 fun n ↦
      hasMatSize_of_ne_zero _ hF.isCut_complexLevel m cellChart_mem (n <| · ▸ by simp) (n <|
    · ▸ by simp))).continuousAt ((Set.finite_Iic _).eventually_all.2 fun i l ↦ (ContinuousAt.norm
    ?_).eventually_le_const ((a i l).trans_lt (by simp)))) <;> fun_prop (disch := simp [ne_of_gt])

/-- Let W, F be a cut pair of Bessel functions with the numerical conditions of `IsCutBessel`. If W
has Schur's bound with constant deg⁻¹|I|, where 0 < deg and deg·Θ ≤ b^{4r²} (Θ =
`Shape.bandConst`), then F has the band
limits `HasBandLimits` for some forms J.

Real-place Bessel integrals: band limits, energy and open-cell bound. -/
lemma hasBandLimits_of_isCutBessel [Nonempty I]
    {deg} (hd : 0 < deg) (hS : SchurLe W (.ofReal deg⁻¹ * card I))
  (hD : deg * 𝔰.bandConst ≤ b ^ (4 * 𝔰.r ^ 2)) : ∃ J, HasBandLimits b F deg J := by
  let δ := hF.complexLevel.upperPairing 0 (translatePairing F W 1) 1
  obtain ⟨c, Γ, ⟨_, _, a⟩, ⟨_, _, d⟩, hW, b2, _, B, _, v, H, l⟩ := hF.isCut_complexLevel, hF.gauge,
    hF.isCut_complexLevel.1.1, (hF.isBesselFunction .full).1, hF.isBesselFunction .full,
    hF.two_le_b, hF.k_eq, hF.isBesselFunction .cut, hF.haarRatio_spec
  choose _ _ x y _ using (hF.exists_gauge_isHead 𝔰.ϱ · · 0)
  refine ⟨fun i p q ↦ ite (i ≤ 𝔰.ϱ) (hF.formConst * hF.complexLevel.floorForm i p q
    F 1) ⟪sieveVector F p, sieveVector F q⟫_ℂ, ⟨by simp [wave], fun i p q ξ hi ↦
    .imp_right (fun e ↦ ⟨(e.trans <| by simp [·, hi, Pi.one_def]), ((congrArg _ e).trans_le <|
    hF.norm_floorForm_le hi ·.unit (by simp) (·.formModulus_sq_le_of_char c hi · ⟨⟩
    fun _ _ ↦ rfl))⟩) ?_, fun _ _ _ ↦ by simpa using! posSemidef_gram .., by
    simpa using! hF.continuous_sieveVector.fst'.inner hF.continuous_sieveVector.snd', fun p q ↦ ?_,
    fun i p q h y ↦ ite_eq_left h ▸ hF.norm_floorForm_le h y.unit (by simp)
    (·.formModulus_sq_le_of_heads c h · ⟨⟩ rfl (by simp))⟩, fun σ h p q e f ↦ by
    -- the isometry clause
    by_cases! t : ‖(p 𝔰.ϱ).1‖ ≤ 1
    simp [sieveVector, *]
    obtain ⟨k, k', rfl⟩ := cartan_decomposition h e t
    simp [sieveVector, *, inner_besselCorrelation _ c F.2 (x p q)]
    nth_rw 2 [← integral_mul_left_eq_self _ (embedH k, embedH k)]; simp [mul_assoc, ← map_inv _ k',
      -map_inv, B.3, weylElem_mul_left_comm]⟩
  obtain h | rfl := hi.lt_or_eq
  simpa [h] using Γ.integral_floorForm_succ c ⟨i, h⟩ _ ξ (hF.lintegral_formMajorant_ne_top hi)
  -- the top floor is the integral of the products of two vectors with one last entry
  refine integral_succ_floor_eq Γ c 𝔰.top ξ (hF.lintegral_formMajorant_ne_top hi)
    (hF.complexLevel.measureH_spec.1.mono unitriGroup_inf_floorGroup_last.ge) (by simp)
    ((ite_eq_right (by simp)).trans (ite_eq_left rfl)) (Place.ae_isUnit.mono fun
      | _, ⟨z, rfl⟩ => ?_)
  by_cases! hl : ‖z.1‖ ≤ 1; simp [sieveVector, *]
  erw [← stackMeasure_top, (by simp [descConv_add] : _ ∗ₘ _ = hF.complexLevel.groupMeasure), v]
  simp [sieveVector, inner_besselCorrelation _ c F.2 (x p q) (y p q), prod_smul_left,
    prod_smul_right, realFrameGram_cellChart hl,
    mul_left_comm _ (wave _), ← mul_assoc _ _ (integral ..)]
  rw [← (measurePreserving_prod_mul_swap ..).hasLaw.integral_comp (by fun_prop)]
  norm_cast; congr 3
  simp [headDensity, prod_range, ne_of_lt, ← toReal_rpow, ← one_div,
    ← sqrt_eq_rpow, mul_pow, posPart_def]; rw [toReal_ofReal (by positivity)]
  grind [formConst, toReal_ne_zero, Shape.openCellConst, 𝔰.openCellConst_pos, pow_right_comm]
  simp (disch := fun_prop) [formIntegrandOne, descConv, integral_map]
  simp [mul_assoc, weylElem_mul_left_comm, B.3]
  -- the energy
  have K {B} h := by simpa using Γ.isPairingKernel_translatePairing (W' := B) c h 0 1 1
  obtain ⟨k, k', V⟩ := K c.1, @K W ⟨hW.1, by simpa using hW.2⟩, (⟨⟨by fun_prop, _,
    (norm_sub_le_of_le (a _) <| d ·)⟩, by simp_all [hW.2, B.2, smul_sub]⟩ :
    Place.IsBessel (⇑F - ⇑W) 1)
  grw [ite_eq_left, add_div, one_div, ← ofReal_le_ofReal_iff, ofReal_add, ← (?_ : 2 * _ ≤ _ / deg),
    ofReal_mul, ← hF.formConst_mul_lintegral_le zero_le V hF.lintegral_sq_sub_le _ _ _ (fun {y} _ ↦
    ⟨y⁻¹, by simp [hF.ten_le.trans']⟩) le_rfl le_rfl, ofReal_norm, enorm_mul, enorm_floorForm_le,
    lintegral_mono fun x ↦ (?_ : _ ≤ ‖δ x‖ₑ ^ 2 + 2 * hF.complexLevel.formMajorant 0 p q F (F - W)
    x), lintegral_add_left, lintegral_const_mul', headDensity, prod_range_zero, one_mul, mul_add,
    mul_left_comm _ 2, v, lintegral_smul_measure, lintegral_le_of_forall_fin_meas_le
    (hF.haarRatio ^ 2 * card I * (.ofReal deg⁻¹ * card I)) fun s hs h ↦ ?_, show _ * _ ≤
    .ofReal deg⁻¹ by simpa [← toReal_le_toReal, field, formConst, mul_eq_top, le_of_lt, *] using l]
  any_goals first | finiteness | fun_prop | simp [Size.IsHead, Size.zero_one_mem_ofSize]
  obtain ⟨⟨D, d, f⟩, _⟩ := k'.exists_lintegral_le 0, Fact.mk h.lt_top; let β := s.indicator (star δ)
  have m q : MemLp β q := (memLp_indicator_iff_restrict hs.nullMeasurableSet).2
    (.star (.of_enorm_bound
    (by fun_prop) d.ne (.of_forall ((enorm_integral_le_lintegral_enorm _).trans <|
    f 1 ·)))); have i := memLp_one_iff_integrable.1 (m 1); have e := lintegral_enorm_sq i (m ⊤)
  grw [setLIntegral_mono' hs (g := (‖β ·‖ₑ ^ 2)) (by simp +contextual [β]), restrict_le_self,
    ← ENNReal.mul_div_cancel_right' id (e.trans_ne coe_ne_top).elim, div_le_of_le_mul]
  grw [← sq, mul_assoc, mul_assoc, ← hS _ i, ← hF.lintegral_sq_cut_le, ← sq_lintegral_le
    (by fun_prop) (Measurable.aemeasurable (by fun_prop)) fun z ↦ (mul_pow ..).le, ← mul_pow, ← H _
    (by fun_prop) (by simp +contextual [B.enorm_besselS_mul (mem_unitriGroup_of_mem_besselU _),
    hW.enorm_integral_besselS_mul (mem_unitriGroup_of_mem_besselU _)]), e,
    ofReal_le_enorm, ← Complex.ofRealLI.enorm_map, ← LinearIsometry.integral_comp_comm,
    integral_congr_ae (.of_forall fun x ↦ .trans (b := β x * δ x) (by by_cases x ∈ s <;> simp [β, *,
    RCLike.conj_mul]) (integral_const_mul ..).symm), integral_integral_swap ⟨by fun_prop,
    (lintegral_prod_le _).trans_lt ?_⟩, enorm_integral_le_lintegral_enorm]
  gcongr; simp [← inner_smul_right, integral_inner, hW.integrable_smul i, enorm, ← ENNReal.coe_mul,
    nnnorm_inner_le_nnnorm]
  simp_rw [uncurry, enorm_mul, lintegral_const_mul' _ _ enorm_ne_top]
  grw [f, lintegral_mul_const'] <;> finiteness [i.2]
  simp [formModulus, formMajorant, descConv, ← formIntegrandOne_eq Γ c]
  grw [← k.enorm_upperPairing_le, ← (K V).enorm_upperPairing_le, Eq.trans (a := δ x) (by simp [δ])
    (integral_sub (k.integrable_upperMeasure 0 1 x) ((K V).integrable_upperMeasure 0 1 x)),
    ← toReal_le_toReal, toReal_add] <;> simp [formIntegrandOne, mul_ne_top]
  grw [← abs_norm_sub_norm_le, sq_abs, sub_sq]; nlinarith
  grw [(le_div_iff₀' hd).2 hD, b2]; simp [hF.rho_eq, field, ← pow_mul, ← pow_add, *]
  gcongr; any_goals bound [hF.ten_le]
  clear * - hF; obtain ⟨_, rfl⟩ := hF.mul_cube_lt_s.dest; lia
end

-- part: New.Filling.FillingData
section
/-! Band limits, energy and open-cell bound for real-place Bessel integrals. At a real place,
integrals of a Bessel function on an indefinite unitary group against its translates have bounded
energy, Fourier transforms decaying beyond a band and a mean-square bound on the open cell, and they
replace Petersson's J-Bessel kernel in showing that few translates almost span the rows. Rank one is
classical and Bessel kernels are studied for GL(n) and GSp(4). Related work: Petersson, Über die
Entwicklungskoeffizienten der automorphen Formen, 1932; NIST DLMF §10.22; Baruch, Bessel
distributions on the open cell, 2001–2004; Comtat et al., Effective Kuznetsov trace formula for
GSp(4), 2025.

This file: A polynomial identity that splits a product of determinants (used in
New.Rows.Separation). Existence of a Bessel
system with tail, Schur and band bounds for the data. Builds the filling record from the global
data, with chosen Bessel systems. -/

open Matrix MvPolynomial Finset Filling MatrixOrder MeasureTheory Norms.L2Operator

/-- The product L of the determinants det(η; x), η from `Data.detRows`, equals ∑_l P_l·Q_l, with
P_l the polynomial `letterPoly` of the l-th basis vector in the positive letters of W_j and Q_l
from `Data.linePolyCoords`; columns of W_j are renamed by f, those of L⁺ by g. -/
lemma Data.stdClassSum_carrierXi_eq_lineMultiplier {P} {D : Data P} j i {n} (f g : _ → n) :
  renameRowsCols id (f ∘ D.basisVec ∘ (↑) ⊕ᵥ g) (stackedDetProd (posEquiv j) (detRows j i)) = ∑ l,
  renameRowsCols id f (letterPoly (D.signsW j) (untwistedAuxPair j).ord 1 _ (Pi.single l 1)) *
  renameRowsCols id g ((linePolyCoords j i) l) := by
  rw [(?_ : renameRowsCols .. = (aevalTower (renameRowsCols id g) (renameRowsCols id f <|
    fockLetters _ _ 1 <| .X ·)).comp inFirstCols)]
  simpa [← toPoly_linePolyCoords, toPoly, letterPoly, entrywise, nablaBasis, tableauPoly, minor,
    smul_eq_C_mul, AlgHom.map_det, Matrix.map,
    Fintype.linearCombination_apply, sum_mul, mul_right_comm _ (rename _ _)] using! sum_comm
  ext1 ⟨τ, a, s | s⟩ <;> simp [inFirstCols, fockLetters, auxPair]
  rw [sum_eq_single] <;> grind [basisVec, D.basisNumber.eq_symm_apply, signsW]

attribute [local simp] ConjAct.units_smul_def

variable {P} (D : Data P)

lemma Data.card_X₀ : Fintype.card (D.X 0) = D.k := by grind [card_X, n]

/-- An orthonormal frame with the signs of Y₀ (`Data.signsY` 0). -/
noncomputable instance Data.unitarySignFrameY : Frame _ (D.signsY 0 ·) := Nonempty.some <|
  have ⟨_, a, b⟩ := exists_frame_gradedGram D.shape.besselIndexEquiv (.id ℂ) one_pos
    ((D.card_neg_gridSigns false 0 0).trans (by grind)); ⟨@.mk _ _
    ⟨(.mkOfMulEqOne _ _ (b rfl))⁻¹, by convert! a; simp [← ext_iff, gradedGram,
    Shape.besselIndexEquiv, splitGram, middleGram, Fin.rev]; lia⟩ ⟨b rfl, Units.inv_mul _⟩⟩

/-- For every infinite place v there is a Bessel system on G₁ with the formal degree and the
reproducing property of the parameter ς(v) (doubled: `Data.paramW` v) and the U(X₀)-type with column
numbers `Data.κ` v, in the sense of `Filling.IsBessel`.

Real-place Bessel integrals: band limits, energy and open-cell bound. -/
lemma Data.exists_besselSystem v : ∃ B : BesselSystem _ D.b D.f,
  IsBessel B (D.paramW v) (D.κ v) := by
  let w (_ : Unit) := D.κ v
  obtain ⟨ck : Fintype.card D.shape.κ = _, _, _ : D.k ≤ D.a, b1 : 1 ≤ D.b, u, h⟩ := D.card_X₀,
    @isHermInvolution_J₁ D.shape, D.nat_le_of_hasLogBound, D.le_of_hasLogBound,
    Exists.intro _ (isHCParam_hcParameter D.shape.κ w 0)
  have hL i : |D.paramW v i| ≤ ↑(3 * D.a) :=
    (D.abs_gridParam_le (z := false) v bot_le bot_le i).trans (mod_cast D.nat_le_of_hasLogBound)
  obtain ⟨hg : HCParam.HasLargeGap _ (D.r ^ 7), i, _⟩ := (D.hasGap_signsY_paramW v).mono
    D.le_of_hasLogBound, h.exists_decrPosition_eq () Fintype.card_pos
  have L j : (toHCParam 1 (u ())).lowestKType j = ite (j = i) (D.κ v 1) 0 ∧ |u () j| ≤
    ↑(3 * D.a) := by have := h.eq_hcParameter () j; rw [h.lowestKType_eq, hcParameter,
    diagramWeight_apply, sum_eq_ite 1, Pi.zero_apply] at * <;> grind [κ, (h ()).1, decrPosition]
  obtain ⟨d1, ⟨p, q⟩, ⟨_, ⟨B, rfl⟩, hG⟩, K, ⟨dq⟩, _, _, x, hR, T⟩ := _root_.formalDegree_pos hg,
    exists_equiv_decrPosition (h ()).1,
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 (weylGram_posDef.isStrictlyPositive
    (n := WeylIndex D.shape.κ w)), isIdempotentKernel_psiInFrame (p := D.unitarySignFrameY.1) hg,
    Orbital.harish_chandra_degree_and_orbital (hg.mono D.le_of_hasLogBound),
    D.shape.besselGraphMeasure_isMulRightInvariant, D.shape.besselGraphMeasure_finiteOnCompacts,
    ((D.exists_isSteep false).choose_spec v).exists_isTwoFactor_besselPairHom (b :=
    D.b) (.swap (.inr ()) i) (by simpa using (L · |>.1)) D.le_of_hasLogBound
    (by grw [show D.κ .. ≤ D.a by grind [κ]]; use D.le_of_hasLogBound) D.le_of_hasLogBound
  let φ := MulSemiringAction.toAlgEquiv ℂ (type_of% B.1) (ConjAct.toConjAct B)
  -- `rep` is Sym^(κ v 1) in an orthonormal basis for the Gram form
  let rep : U (1 : Matrix D.shape.κ _ ℂ) →* unitaryGroup _ ℂ := .mk' (fun h ↦ ⟨φ (schur w fun _ ↦
    h), by simpa [mem_unitaryGroup_iff', φ, hG, star, ← U.inv_val_eq_conjTranspose,
    conjTranspose_nonsing_inv, mul_assoc]
    using congr(B.1ᴴ⁻¹ * $(PolyRep.schur_conjTranspose_weylGram_schur .refl (κ := w) (fun _ ↦ h.1.1)
             fun _ ↦ h) * B⁻¹)⟩) (by simp [schur_mul_left])
  obtain ⟨Y, hS⟩ := exists_isBesselFunction (rep := rep) (by simp [rep, φ]; fun_prop) (v :=
    .toLp ..) (fun k ↦ (dotProduct_comm (_ *ᵥ B.1 *ᵥ highestVector w u) (star (_ *ᵥ _))).trans (by
    simpa [weylRep, hG, q, rep, φ, ↓star_mulVec, ↓star_highestVector, highestVector,
      dotProduct_mulVec, mul_assoc, dsCoeff_of_mem_maxCompactU (h.hasGap () 0) (k := ⟨k, _⟩) k.2,
      _root_.funext (h.lowestKType_eq _)] using! weylRep_coeff_eq_prod_weightMinors (κ := w) (e :=
      0) (fun _ ↦ p) _)) hg D.le_of_hasLogBound (T.laplace_method (β := D.b ^ 3) _ hg (h.hasGap ..)
    D.le_of_hasLogBound hL (L · |>.2) D.le_of_hasLogBound (ck ▸ D.le_of_hasLogBound) (ck ▸
    D.le_of_hasLogBound) (isProperMap_fst_besselPairHom x) (.subtype_mk (by simp; fun_prop) _) fun s
    _ ↦ (CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup s.1.2)).trans_le D.le_of_hasLogBound)
  obtain ⟨F, V, fx, t⟩ := (pow_mul D.b .. ▸ hS).exists_cut_isCutPair hg hL D.f hR
    D.le_of_hasLogBound (ck ▸ D.nat_le_of_hasLogBound) D.le_of_hasLogBound D.nat_le_of_hasLogBound
  have s := t.isBesselFunction .full
  have k B := t.lintegral_sq_full_eq ▸ s.hasSchurBound_of_convolve_eq hg hL t.integrable B fx
  use ⟨_, _, _, d1, _, t, fun M H ↦ (scalar_of_commute_schur fun g a ↦ by
    simpa [rep] using! (H (U.of isUnit_one (g ()) (by simp [a]))).map φ.symm).imp (φ.commutes · ▸
    φ.eq_symm_apply.1 ·), (k · ∘ D.le_of_hasLogBound.trans), D.le_of_hasLogBound, _,
    (hasBandLimits_of_isCutBessel ⟨t, rfl, D.le_of_hasLogBound.trans (le_self_pow₀ b1 nofun),
    (Nat.sub_add_cancel (m := _ + 2) (ck.ge.trans' D.nat_le_of_hasLogBound)).symm,
    lt_tsub_iff_right.2 (ck.ge.trans_lt' D.nat_lt_of_hasLogBound),
    ck.ge.trans' D.nat_le_of_hasLogBound, D.nat_le_of_hasLogBound, D.le_of_hasLogBound⟩ d1 ((k _
    le_rfl).elim fun _ j ↦ by simpa [j] using (j.2 []).2.2) ?_).choose_spec⟩, dq, ⟨star B, (star
    B)⁻¹.1, by simp [s.3, rep, φ, w, ← mul_assoc, hG ▸ weylGram_mul_schur _, ← star_mul]⟩,
    fun y i ↦ by simpa [← integral_comp_frameEquiv (p := D.unitarySignFrameY.1), K.3] using!
    (eval_integral_piLp (s.integrable_smul K.2.comp_inv y).eval_piLp i).symm.trans congr($fx y i)
  rify at hL
  simp [-prod_mul_distrib, Shape.bandConst, dq, volU, ↓card_rowIndex, ck]; rw [weylDimensionPoly,
    card_rowIndex]; field_simp
  grw [le_abs_self (∏ _, _), abs_prod, (abs_prod ..).le, (abs_div ..).le, abs_sub, hL, hL, abs_two,
    (D.le_of_hasLogBound : _ / 2 ≤ D.b ^ 3), filter_subset, ← Nat.factorial_le bot_le,
    (D.nat_le_of_hasLogBound : _ * _ ≤ D.r ^ 2), k_le_r]
  simp [field, ↓card_rowIndex]
  grw [(D.le_of_hasLogBound : .pi ≤ D.b)]
  ring_nf
  repeat bound [Real.two_le_pi]

variable {P : _} (D : Data P)

instance Data.instLbHPowRealNatOfNatϱHMulLb : D.HasLogLower (ofNat(2) ^ D.ϱ) (10 * D.logB) := ⟨by
  simp [← Real.le_log_iff_exp_le]; grw [← Real.log_two_gt_d9]; norm_num; use D.le_of_hasLogBound⟩

/-- The filling data `Filling` attached to the admissible data D: its level N with π̄, primes
g₀, g₁ with chosen places, ϖ, and Bessel systems chosen from `Data.exists_besselSystem`. -/
noncomputable def Data.filling := by refine' (Filling.mk (fintypeChosen := _) _ _ D.piIdele _ _ _ _
  D.classAut_columnLevel_eq_bot (D.exists_besselSystem · |>.choose) (mod_cast D.piIdele_spec.1.symm)
  D.N_prime (by grind [D.piIdele_spec.2, D.isSplitLevel_piPlaces.q_eq]) (coe_mem_Ô _) (⟨D.g_prime ·,
  D.nat_lt_of_hasLogBound.ne⟩) (D.g_mem · |>.1) (D.g_mem · |>.2)
  (@q_eq_g _ D · · ·.2) D.isConjApart_chosen.1 (IsChosen.not_star ·.1 ·.1) (fun r ↦ by
       refine .trans ?_ (.trans (forall_congr' fun i ↦ (dvd_iff_reduceAt_eq_zero
         (Parameters.intValuation_p · (Parameters.not_dvd_N₁_mul_d_of_modEq_one (D.g_modEq_one i)))
         r).trans ?_) Sigma.forall.symm) <;> simp
       use (by grw [← ·]; simp),
         And.elim (Nat.Coprime.cast (by grind [Nat.coprime_primes, Data])).mul_dvd
       use fun h a ⟨_, k⟩ ↦ ⟨h a k, h _ (by simpa)⟩, fun h w k ↦ by_cases (h w ⟨·, k⟩ |>.1) fun n ↦
         star_star w ▸ (h _ ⟨(D.isChosen_star_iff k).2 n, by simpa⟩).2) D.card_chosenPlace P.star_ϖ
  P.different_eq_span_varpi ..) <;> and_intros <;> (try rify [Shape.k, card_X₀,
  finrank_eq_two_mul_card_infinitePlace, inv_pow, pow_mul']) <;> use D.le_of_hasLogBound

/-- The level group `Data.columnLevel` on X₀ is the preimage of the principal congruence subgroup
K(g) under the embedding of the finite adelic points of U(X₀) in those of U(Y₀). -/
lemma Data.columnLevel_zero_eq_comap : D.columnLevel 0 =
  D.filling.principalLevel.comap D.filling.inclHFin := by
  ext; simp [columnLevel, Filling.principalLevel, _root_.funext_iff,
    D.filling.reduction_inclHFin_eq_one_iff, levelOf, Sigma.forall,
    D.filling.inclHFin_mem_latStabilizer, -Subtype.forall]
  use by tauto, fun ⟨c, b⟩ ↦ ⟨⟨c.1, b⟩, c⟩
end
