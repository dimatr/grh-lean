import New.Filling.BoxPartition
import New.Filling.AmplitudeSums

-- part: New.Filling.LinkPairing
section
/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Bordered determinant bounds the discriminant of the lattice of lifts of a link.
Discriminant gain for congruent terms with differing links, via lattices of lifts. -/
seal Finset.univ Finset.sum Finset.prod

open Fin Module Equiv Fintype MatMul Matrix Pointwise Submodule Sum

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {c c' j} {γ :
  S.G E} {τ : Type}

section

attribute [local simp] paddedLeading forall_fin_succ' init is_le IsHermUnit.conjTranspose_eq
  Matrix.map_add mulVec Matrix.mul_apply
  Units.smul_def abs_norm_eq_prod_norm_sq dotProduct leadingMinor mul_pow

/-- Let γ have level j. The Gram matrix of (e_a for a ≤ ϱ; γe_a for a ≤ j; e*_a for a > j; z;
γz), with N added on the diagonal at the last three groups, has determinant of absolute norm
(N^(2f)·`Filling.minorNorm` j γ)². -/
lemma HasLevel.abs_norm_bordered_det (h :
  S.HasLevel j γ) : let r := sumCompl (@val _ · < j); let m := isotropicFramePair γ
    let f := .map r (r ∘ inl); let s := (diagonal 1).submatrix id (inr ∘ inr ∘ r ∘ inr)
      let p := (framePair γ).submatrix id (.map (fun () ↦ 𝔰.top) fun () ↦ 𝔰.top); let P :=
          ((m.submatrix id f).fromCols
          (s.fromCols p)); let M := Pᴴ * S.ratGram * P + fromBlocks 0 0 0 ((S.N : E) • 1)
          genIndex (finAdeleMat M).det = (S.N ^ (2 * numInfPlaces E) * S.minorNorm j γ) ^ 2 := by
  intro r _ _ _ _ P M; let A :=
    (paddedLeading j (S.frameProducts γ⁻¹)).updateRow 𝔰.top (S.frameProducts γ⁻¹ 𝔰.top)
  erw [← RingHom.map_det, ← (?_ : |↑(Algebra.norm ℚ A.det)| = _ * _)]
  · let g := finSuccEquivLast.trans (r.symm.optionCongr.trans (optionEquivSumPUnit _))
    have d := M.det_reindex_self ((sumAssoc ..).symm.trans (((sumAssoc ..).sumCongr
      (.refl _)).trans (sumSumSumComm ..))) ▸ det_permute (sumComm ..) _
    rw [(Matrix.ext (Sum.rec (Function.swap (Sum.rec ?_ fun _ _ ↦ by rfl)) ?_) : submatrix _ _ _ =
      fromBlocks (reindex g g A) (of _) 0 (reindex g g Aᴴ))] at d
    · simpa [sq] using congr(|(Algebra.norm ℚ $d.symm : ℝ)|)
    all_goals simp +zetaDelta [splitGram, middleGram, frameGram, apply_ite star]; grind
  cases' j using lastCases with j
  · simp [show A = S.frameProducts γ⁻¹ by simp [A, ← ext_iff], minorNorm, field]
  choose w e using h.inv.exists_shared_frame_vector j.le_last
  erw [← cramer_transpose_apply, ← det_smul_inv_vecMul_eq_cramer_transpose _ _
    (by simpa [↓det_paddedLeading] using h.inv.2.1),
    Pi.smul_apply, congr($det_paddedLeading • $(frameProducts_mulVec_of_frameImage_eq e) _)]
  obtain ⟨⟩ := (congr(‖Φ · $(star_mul_last_eq_of_frameImage_eq
    e)‖)), congr(diag $h.inv.paddedLeading_mul_inv 𝔰.top)
  simp_all [tsub_eq_zero_of_le, ← sq, minorNorm, ← conjTranspose_submatrix, j.le_last.not_gt]; ring

/-- Let γ have level j, k = h_c⁻¹γh_c' ∈ K, and w = i(k)·i(k⁻¹)·`Filling.saturationIndex` k with i =
`Filling.xRowsIndex` j. Then w ≠ 0, and for each basis v of link γ some v·e satisfies
`Filling.HasIntegralLifts` with `Filling.linkDiscSq`(v,e)·w² ≤ (`Filling.minorNorm` j γ)². -/
lemma exists_lifts_linkDiscSq_le [StablyUnram E] [Fintype τ]
    {t} (hk : γ ∈ S.termsOver c t c') (hj : S.HasLevel j γ) {v :
  Matrix _ τ E} (hv : HasLeftInv v) (hL : colSpan v = link γ) : let k := S.termPosition c c' γ
  let w : ℝ := S.xRowsIndex j k * S.xRowsIndex j k⁻¹ * S.saturationIndex k
  ∃ e, HasIntegralLifts c γ (finAdeleMat v * e.1) ∧ S.linkDiscSq v e * w ^ 2 ≤ S.minorNorm j γ ^ 2 ∧
    w ≠ 0 := by
  intro k; obtain ⟨hD, D, _, l, _⟩ := hj.abs_norm_bordered_det, hj.minorNorm_pos.ne',
    isIntMatrix_framePair (termsOver.isIntMatrix_termPosition hk), id hv
  extract_lets r m f s p P M at hD
  obtain ⟨u, ⟨h₇, h₈⟩, h₉⟩ := by simpa [fromRows_ext_iff, -Matrix.mul_assoc] using
    (exists_mul_eq_of_col_mem_range (x := ((mᴴ * S.ratGram).fromRows (linkMatrix γ)).fromRows
    (sᴴ * S.ratGram)) (y := (fromRows 0 (fromCols 0 v)).fromRows (fromCols (diagonal 1) 0)) fun b ↦
    (mem_map.1 (hL.le ⟨_, congr($(v.mul_fromCols 0 1)ᵀ b)⟩)).elim fun t ⟨a, e⟩ ↦ by
    choose _ x _ o using exists_frameImage_eq_of_isNormalForm hj.1.inv (snoc ((fromRows 0
      (fromCols 1 0) · b) ∘ r.symm - t ∘ inl) 0); use t + frameImage 1 *ᵥ ite (j ≤ 𝔰.ϱ) x 0
    obtain ⟨⟩ := star_mul_last_eq_of_frameImage_eq o, frameImage_mulVec _ x ▸ o.symm
    rw [mulVecLin_apply, fromRows_mulVec, fromRows_mulVec, ← mulVecLin_apply,
      isotropicFramePair_mulVec_eq_zero_iff.2] <;> split
      <;> simp_all [s, r, frameImage_one_mulVec, funext_iff, -mulVec, mulVec.eq_1 (_ * _)]; omega)
  choose a e z hn using exists_isPrimitiveMatrix_mul_fromBlocks (S.classCoord c * finAdeleMat u)
    ⟨finAdeleMat ((sᴴ * S.ratGram).fromRows
    (l * linkMatrix γ)) * (classBasis c).1, by simp [classCoord, ← Matrix.map_mul, *]⟩
  use e, ⟨_, _, _, of _, h₇, (hn.1 · <| inr ·), by ext; simp [*]⟩
  obtain ⟨g : (S.latMiddle (𝔸f E)).splitGram.submatrix 𝔰.besselFrame id * isotropicFramePair k =
    fromCols 0 (xRows ((S.latMiddle _).frameGram ↑k⁻¹))ᴴ, q, o⟩ := by simp [↓frameGram_inv,
    frameGram, ← ext_iff], congr($(classCoord_gram c m u) * a.1.fromBlocks z 0 e.1),
    xRows_conjTranspose_mul_eq (n :=
    u.toCols₁) congr(toCols₁ $h₇) (by simpa using! congr(zFormPair (S.ratMiddle E) * toCols₁ $h₈))
  rw [Matrix.mul_assoc, h₇, classCoord_mul_isotropicFramePair] at q; let F :=
    (isotropicFramePair k).submatrix id f
  choose hs b using jacobi_perp_discriminant (F := F) (N :=
    finAdeleMat M) S.isUnimodular_latMiddle.splitGram (by tauto) hn (congr(submatrix $q f _).trans
    (by simp)) (by simp [← card_congr r, hL ▸ card_eq_finrank_colSpan hv, finrank_link]; lia)
    (S.classCoord c * finAdeleMat (s.fromCols p)) (principalIdele (.mk0 S.N (by simp))) (by
    unfold F; erw [← classCoord_mul_isotropicFramePair, ← mul_fromCols, ← fromCols_map,
      classCoord_gram c P P]; simp [M]) (by simp [*])
  let Q := (sᴴ * S.ratGram).fromRows (pᴴ * S.ratGram) * u
  rw [hD, gram_mul, genIndex_det_conj, (?_ : _ * _ = RingHom.mapMatrix _ (uᴴ * S.ratGram * u +
    (S.N⁻¹ : E) • Qᴴ * Q)), (?_ : _ + _ = fromBlocks ((S.N⁻¹ : E) • 1) 0 0 (vᴴ * S.linkMetric * v)),
    ← RingHom.map_det, genIndex_algebraMap] at b; simp [genIndex_natCast] at b
  simp [s, r, linkMatrix, ← ext_iff, -Subtype.forall] at h₈ h₉
  have I := submoduleIndex_colLattice_intVectors (M :=
    a) fun b d ↦ by simpa [classCoord_eq_fromBlocks, h₉] using hn.1 (inl b) (inl d)
  obtain ⟨d₁, h₄⟩ := @ne_zero_and_le_of_dvd (S.xRowsIndex j k) _ (mod_cast I ▸ (genIndex_pos
    a.det).ne') (submoduleIndex_dvd_of_le (mulVecBilin
    ℕ _ _ ∘ₗ mulVecBilin ℕ _ (-(finAdeleMat u).submatrix (inl ·.1) inl)) (colLattice_le (⟨_,
    fun _ ↦ by simpa [classCoord_eq_fromBlocks] using hn.1 (inl _) <| inl ·, rfl⟩)) (colLattice_le
    (r.surjective.forall.2 (Sum.rec (mem_sup_right <| col_mem_colLattice ·) fun b ↦ mem_sup_left ⟨_,
    single_mem_intVectors b, by simpa [k, r, *, funext_iff, frameGram_termPosition, ← r.sum_comp,
    add_eq_zero_iff_eq_neg'] using congr((finAdeleMat $o)ᵀ b)⟩)))),
    @ne_zero_and_le_of_dvd (S.xRowsIndex j k⁻¹ * S.saturationIndex k) (submoduleIndex
    (intVectors ..) (preimageLattice (Ô E) F)) (by simp [·, D] at b) (by
    grw [show xRowsIndex .. ∣ submoduleIndex (colLattice _ F) (colLattice _ (isotropicFramePair
      k)) from submoduleIndex_dvd_of_le (mulVecBilin ℕ _ _) (colLattice_le
      (congr($gᵀ _ ∈ colLattice ..).ge <| ·.rec (fun _ ↦
      zero_mem _) col_mem_colLattice)) (colLattice_le (mem_sup_left ⟨_, col_mem_colLattice <|
      inr ·, congr($gᵀ (inr _))⟩)), saturationIndex, AddSubgroup.relIndex_mul_relIndex]
    exacts [submoduleIndex_dvd_of_le _ (by tauto) fun x ⟨h, r, e⟩ ↦ mem_sup_left ((hs x (by
      simpa [← e] using congr($qᴴ *ᵥ r))).imp (by simp_all [preimageLattice])), colLattice_le
      (col_mem_colLattice <| f ·), le_inf (colLattice_le (by tauto)) LinearMap.map_le_range])
  use ?_, by simp_all
  grw [mul_assoc, linkDiscSq, d₁.2, ← Nat.cast_mul, h₄.2, I]
  exact (mul_left_cancel₀ (by simp) (.trans (by simp; field) b)).le
  simp_rw [linkMetric, Q, p,
    framePair_last_eq_zFormPair_mul]; generalize zFormPair (S.ratMiddle E) = L
  simp [*, fromBlocks_smul, ← ext_iff,
    ← by simpa [← two_smul E, *] using gram_linkMatrix_mul h₇ h₇ 2⁻¹ (-2⁻¹)]
  simp [Q, finAdeleMat_conjTranspose, map_splitGram_ratMiddle, ← classCoord_conj_splitGram c]

end

attribute [-simp] fromBlocks_map

variable {S : Filling E 𝔰} {c : S.Classes} {γ : S.G E} {m}

lemma HasIntegralLifts.exists_isIntMatrix c' : HasIntegralLifts c γ
  m → let k := S.termPosition c c' γ; let T := S.latMiddle (𝔸f E); ∃ n : Matrix 𝔰.BesselIndex
      τ _, IsIntMatrix (Ô E) n ∧ zFormPair T * linkMatrix k * n = finAdeleMat (zFormPair
      (S.ratMiddle E)) * m ∧ (isotropicFramePair k)ᴴ * T.splitGram * n = 0 ∧ ∀ p, m.toRows₁ =
      fromRows p 0 → n.toRows₂.toRows₁ = S.classCoordX₀ c * p | ⟨_, _, _, w, a, i, e⟩ => ⟨_, i, by
  simp_rw [← framePair_last_eq_zFormPair_mul, isotropicFramePair, ← classCoord_mul_framePair,
    ← Matrix.mul_assoc _ _ w]; erw [classCoord_gram, framePair_last_eq_zFormPair_mul,
    classCoord_gram, a]
  simp +contextual [← e, ← ext_iff, classCoord_eq_fromBlocks, linkMatrix, mul_apply]⟩

variable [StablyUnram E] [Fintype τ]

variable {c' : S.Classes} {γ : S.G E} {j : Fin (𝔰.ϱ + 1 + 1)} {s x} {m : Matrix _ τ _} (hs :
  S.Agrees s)
  (h : γ ∈ S.termsOver c s c') (hc : S.HasLevel j γ) (hq : S.FixesNormAtLeast s x) {γ' : S.G E}

/-- Let m, y be rational with columns orthogonal for `Filling.linkMetric`, and let the columns of
(m | y)f be lifts of γ,
f invertible adelic. Then for some adelic z and invertible a, v, the columns of ma and mz + yv are
lifts, and the squared discriminants multiply: linkDiscSq(m,a)·linkDiscSq(y,v) = linkDiscSq((m | y),
f). -/
lemma HasIntegralLifts.exists_orthogonal_split {s} {y : Matrix _ (Fin s) E} {f} (o :
  mᴴ * S.linkMetric * y = 0) : HasIntegralLifts c γ (finAdeleMat (fromCols
  m y) * f.1) → ∃ᵉ (a) (v) (z : Matrix τ _ (𝔸f E)), HasIntegralLifts c γ (finAdeleMat m * a.1) ∧
  HasIntegralLifts c γ (finAdeleMat m * z + finAdeleMat y * v.1) ∧ S.linkDiscSq m a * S.linkDiscSq y
  v = S.linkDiscSq (fromCols m y) f := fun ⟨_, _, t, u, p, q, k⟩ ↦ by
  choose a v z h using exists_isPrimitiveMatrix_mul_fromBlocks _ ⟨_, f.3⟩
  have T {ι} g : HasIntegralLifts (τ := ι) c γ _ := ⟨_, _, t, _, p, ((Matrix.mul_assoc _ u _ ▸ q.mul
    h.1) · <| g ·), congr(submatrix $(Matrix.mul_assoc ..) _ g).symm⟩
  simp [↓k] at T
  use a, v, z, T .inl, T .inr, (isPrimitiveMatrix_iff.1 h).elim fun V ⟨i,
    e⟩ ↦ by simp [linkDiscSq, o, field, by simpa [genIndex_det_eq_one _ _ i,
    IsAdelic.exists_topology] using congr(genIndex (f * $e).det)]

omit [StablyUnram E] in
/-- If γ has level j, its link contains a pair (a − z, yz) with a in X₀ and y in E such that
𝗀(γ) = D_j D̄_j(1 − yȳ), D_j the leading minor of Z(γ). -/
lemma HasLevel.exists_mem_link_termDisc_eq (h : S.HasLevel j γ) : ∃ a y,
  (a ⊕ᵥ -1 ⊕ᵥ (0 ⊕ᵥ y) : _ → E) ∈ link γ ∧ S.termDisc γ = leadingMinor
  (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j) * (1 - star (y ()) * y ()) := by
  refine .elim ?_ fun x (h : _ ∧ _) ↦ ⟨(frameImage γ *ᵥ x) ∘ 𝔰.indexX₀, _,
    mem_link.2 ⟨init x, by erw [← frameImage_one_mulVec, ← frameImage_mulVec]; use h.1⟩, h.2⟩
  cases j using lastCases
  choose y e _ using exists_mulVec_eq_single_det (S.frameProducts γ)
  cases norm_sq_middle_part_eq e rfl
  use (S.N / (S.frameProducts γ).det) • y, by simp_all [HasLevel, funext_iff, leadingMinor]; grind
  simp_all [HasLevel, frameDisc, leadingMinor, field]
  choose y x hx e using exists_frameImage_eq_of_isNormalForm h.1.inv (-1)
  use y; rw [frameImage_mulVec, star_mul_last_eq_of_frameImage_eq e, e, frameImage_mulVec]
  simpa [funext_iff, frameImage_one_mulVec, hx, is_le, ← not_le] using h.2.2

lemma one_le_xRowsIndex_and_saturationIndex (h : γ ∈ S.termsOver c s c') (hc : S.HasLevel j γ) : 1 ≤
  S.xRowsIndex j (S.termPosition c c' γ) ∧ 1 ≤ S.saturationIndex (S.termPosition c c' γ) ∧ 0 <
  S.classGauge j c c' γ := (exists_basis_matrix _).choose_spec.elim (exists_lifts_linkDiscSq_le h
  hc) |>.elim (by simp_all [classGauge, hc.minorNorm_pos, ← not_lt, zero_lt_iff])

include hs h hc hq

/-- Let γ have level j over (c, s, c'), s agreeing, `Filling.FixesNormAtLeast` s x;
y be r vectors of link γ
independent modulo X₀²; w satisfy `Filling.HasIntegralLifts` with w ≡ yv modulo X₀². Then r ≤ 1 +
(j−ϱ)₊ and (x'D)² ≤ `Filling.linkDiscSq`(y,v)·max(∏_v|𝗀(γ)|_v, N^fD)², D = `Filling.minorNorm` j γ;
x' = x if j > ϱ and the premise of hp (forcing r maximal) holds, else 1. -/
lemma minorNorm_sq_le_linkDiscSq_mul {r i w} (y : Matrix _ (Fin r) E) v (hp : i = 0 → finrank
  E ↥(link γ ⊓ (zFormPair (S.ratMiddle E)).mulVecLin.ker) + r = finrank E (link γ)) (hy : colSpan
  y ≤ link γ) (hi : HasLeftInv (zFormPair (S.ratMiddle E) * y)) (hl : HasIntegralLifts c γ w) (o :
  finAdeleMat (zFormPair (S.ratMiddle E)) * w = finAdeleMat (zFormPair (S.ratMiddle E) * y) * v.1) :
  r ≤ 1 + (j - 𝔰.ϱ) ∧ ite (𝔰.ϱ < j ∧ i = 0) x 1 ^ 2 * S.minorNorm j γ ^ 2 ≤
  S.linkDiscSq y v * (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) ^ 2 := by
  obtain ⟨⟨⟨_, K⟩, rfl, rfl⟩, ⟨n, I, e, q, -⟩, D, ⟨ρ, hρ⟩, C, ⟨a, u, f, l⟩, a', u', ⟨t⟩, -⟩ :=
    h, hl.exists_isIntMatrix c', hc.minorNorm_pos, not_forall.1 (minors_eq_zero_iff.1 ·
    (mulVec_injective_iff.1 hi.mulVec_injective)), hc.2,
    hc.exists_mem_link_termDisc_eq, hc.inv.exists_mem_link_termDisc_eq
  let ε := (of ((fun () ↦ a ⊕ᵥ -1 ⊕ᵥ (0 ⊕ᵥ u)) ⊕ᵥ fun () ↦ 0 ⊕ᵥ u' ⊕ᵥ (a' ⊕ᵥ -1)))ᵀ
  have ε₁ : colSpan ε ≤ link γ := by simpa [↓range_mulVecLin, span_insert, ε, f] using ⟨γ *ᵥ t, by
        simp_all [funext_iff, ↓SetLike.mem_coe]⟩
  have ε₂ {τ w} [Fintype τ] h := have := gram_linkForm_eq_zero_of_le_link (σ := τ) (u := w) ε₁ h
    show εᴴ * S.linkMetric * w = zFormPair (S.ratMiddle E) *
      w by simp [← ext_iff, ε, middleGram, linkMetric, mul_apply] at this ⊢; grind
  have k : zFormPair (S.ratMiddle E) * ε = (S.N : E) • fromBlocks 1 (-diagonal u)ᴴ
    (-diagonal u) 1 := by simpa [← ext_iff, ε, mul_apply, middleGram, add_neg_eq_zero, mul_comm,
    Unique.forall_iff] using congrFun₂ (gram_linkForm_eq_zero_of_le_link ε₁ ε₁) (.inl ()) (.inr ())
  have p : ρ.Injective := fun _ _ _ ↦ by_contra (hρ <| det_zero_of_row_eq · (by aesop))
  let g h := Equiv.ofBijective ρ (p.bijective_of_nat_card_le h)
  apply S.isUnimodular_latMiddle.splitGram.isIntMatrix.mul at I; simp_rw
    [← framePair_last_eq_zFormPair_mul, Matrix.mul_assoc, o, ← ε₂ hy] at e q
  have' L := liouville_gram linkMetric_posDef (ε.submatrix id ρ) y 1 v (ε₂ hy ▸ hρ) _ _
  erw [submatrix_mul_equiv (εᴴ * S.linkMetric) ε ρ (.refl _)] at L
  nth_grw 1 [linkDiscSq, termDiscNorm, L]
  obtain _ | _ | r := r; iterate 2 grw [← le_max_right]; swap
  grw [← S.N_prime.one_le]; simp
  cases h : ρ 0 <;> simp [*, abs_norm_eq_prod_norm_sq] <;> linear_combination
  erw [det_submatrix_equiv_self (g (by simp))] at *
  grw [← le_max_left]
  simpa [*, minorNorm, j.is_le.antisymm (C.2.2 fun _ ↦ by simp_all [← not_lt]),
    abs_norm_eq_prod_norm_sq, field, Finset.prod_pow, pow_mul] using card_le_of_injective ρ p
  positivity
  erw [conjTranspose_one, one_mul, ← congr(det (submatrix $e ρ id))]
  split; choose _ _ _ a b _ using exists_basis_extend_ker (by rw [k]; simp_all) ε₁
  use (le_genIndex_det_of_fixesNormAtLeast hs I rfl q
    (g (by simp_all [← b ▸ card_eq_finrank_colSpan a]; omega)) · hq)
  exact_mod_cast one_le_genIndex (IsIntMatrix.det_mem fun _ _ ↦
    (isIntMatrix_framePair K.isIntMatrix).isInt_conjTranspose.mul I _ _)

/-- Let γ have level j over an agreeing s with `Filling.FixesNormAtLeast` s x. Then link γ ∩ link γ'
has codimension i in link γ, |κ| ≤ dim T° + i + (j−ϱ)₊ (T° = `commonLink` γ γ'),
and a lifting complement (y,v) has
(`Filling.pairInvariant`·x')²·`Filling.linkDiscSq`(y,v) ≤ `Filling.classGauge`²; x' = x if j > ϱ, i
= 0, else 1. -/
lemma exists_link_split_le_classGauge γ' : (0 < S.latticeDisc c (commonLink γ γ') ∧ 1 ≤
  S.frameValueIndex c (S.termPosition c c' γ) 1 (commonLink γ γ')) ∧ ∃ᵉ (i) (ρ) (_ : Fintype ρ) (m :
  Matrix _ ρ E) (y : Matrix _ (Fin i) E) (v) (z : Matrix ρ _ (𝔸f E)), let L := link γ ⊓ link γ'; i =
    𝔰.k + 1 - finrank E L ∧ 𝔰.k ≤ finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) ∧ (i = 0 → L =
    link γ) ∧ colSpan m = L ∧ colSpan y ≤ link γ ∧ (∀ t, y *ᵥ t ∈ L → t = 0) ∧ colSpan (fromCols
  m y) = link γ ∧ HasIntegralLifts c γ (finAdeleMat m * z + finAdeleMat y * v.1) ∧ (S.pairInvariant
    c c' γ γ' * ite (𝔰.ϱ < j ∧ i = 0) x 1) ^ 2 * S.linkDiscSq y v ≤ S.classGauge j c c' γ ^ 2 := by
  choose m b e using
    exists_basis_matrix (link γ ⊓ link γ' ⊓ (zFormPair (S.ratMiddle E)).mulVecLin.ker)
  choose i hl using (le_inf_iff.1 e.le).imp inf_le_left.trans' mul_eq_zero_of_range_le_ker
  let p := m.toRows₁.toRows₁
  have hQ : mᴴ * S.linkMetric * m = pᴴ * p := have := gram_linkForm_eq_zero_of_le_link i i
    by simp_all [← ext_iff, linkMetric, mul_apply, p, middleGram, add_neg_eq_zero, ← two_mul]
  rw [pairInvariant, latticeDisc, frameValueIndex, one_smul,
    (by ext; simp [commonLink, ← e]; rfl : commonLink γ γ' = colSpan p)]
  choose r u _ i k l O o using
    exists_basis_extend_ker (det_gram_linkMetric_ne_zero b) (e ▸ inf_le_left)
  choose s y _ i' k' l' O' o' using
    exists_basis_extend_ker (det_gram_linkMetric_ne_zero i) (k ▸ inf_le_left)
  choose _ P q w using exists_lifts_linkDiscSq_le h hc i' k'
  choose _ v z P p₂ q₁ using P.exists_orthogonal_split O'
  choose a g _ p₃ p₄ q₂ using P.exists_orthogonal_split O
  obtain ⟨⟨_, hn, _, h₁, e'⟩, n, n₁, n₂, _⟩ := p₃.exists_isIntMatrix c', card_eq_finrank_colSpan
    (v := p) ⟨(pᴴ * p)⁻¹ * pᴴ, by simp [hQ ▸ det_gram_linkMetric_ne_zero b]⟩,
    k ▸ card_eq_finrank_colSpan i, k' ▸ card_eq_finrank_colSpan i', finrank_link γ
  specialize e' (finAdeleMat p * a.1) (by clear * - hl; simp_all [← ext_iff, mul_apply, p,
    middleGram])
  simp at n n₁ n₂
  have L (z : s = 0) := eq_of_le_of_finrank_eq inf_le_left (n₁ ▸ z ▸ n₂)
  have ⟨B, G⟩ := minorNorm_sq_le_linkDiscSq_mul hs h hc hq u g (L · ▸ n₁) (by order) (.of_ker_le_bot
    fun t _ ↦ o t (by simp_all [l _])) p₄ (by simp [← Matrix.mul_assoc, ← Matrix.map_mul, hl])
  refine (sublatticeDisc_mul_index_sq_le _ _ _ n le_rfl a (D :=
    S.linkDiscSq m a) (by simp [← genIndex_algebraMap, RingHom.map_det, linkDiscSq,
    hQ]) (by simp [linkDiscSq, hQ ▸ det_gram_linkMetric_ne_zero b, hQ, genIndex.apply_ne_zero_iff])
    (e' ▸ by tauto) fun j ↦ e' ▸ ⟨_, fun _ ↦ hn.neg _ j, congr($(xRows_conjTranspose_mul_eq h₁
    (by simp [*, ← Matrix.mul_assoc, ← Matrix.map_mul]))ᵀ j)⟩
    ).elim fun X Y ↦ ⟨Y, s, _, _, _, y, v, z, by omega, by omega, L, k, l', k ▸ o', k', p₂, ?_⟩
  unfold linkDiscSq at *; grw [← mul_le_mul_iff_left₀ (pow_pos hc.minorNorm_pos 2), mul_pow,
    mul_right_comm (_ ^ 2), mul_assoc, G, ← q, ← q₁, ← q₂, mul_pow, X,
    classGauge]; apply le_of_eq; clear * - w; grind-linarith

/-- For γ, γ' of level j over one agreeing s with `Filling.FixesNormAtLeast` s x, some i has
|κ| ≤ dim T° + i + (j−ϱ)₊ (T° = `commonLink` γ γ'), is 0
only for equal links, and P(γ,γ')P(γ',γ)x'² ≤ (2/g)^(2if)·G(γ)G(γ') (P = `Filling.pairInvariant`,
G = `Filling.classGauge` j c c'); x' = x if j > ϱ and i = 0, else 1. -/
lemma pairInvariant_mul_le (h' : γ' ∈ S.termsOver c s c') (hd : S.HasLevel j γ') : ∃ i, 𝔰.k ≤
  finrank E (commonLink γ γ') + i + (j - 𝔰.ϱ) ∧ (i = 0 → link γ = link γ') ∧
  S.pairInvariant c c' γ γ' * S.pairInvariant c c' γ' γ * (if 𝔰.ϱ < j ∧ i = 0 then x else 1) ^ 2 ≤
  (2 / S.g) ^ (2 * i * numInfPlaces E) * (S.classGauge j c c' γ * S.classGauge j c c' γ') := by
  obtain ⟨⟨-, _, _, _, _, y, v, z, rfl, r, _, e, e₆, -, e₇, ⟨_, _, _, w, a, i, k⟩, h₉⟩, -, _, _, _,
    _, y', v', _, rfl, -, _, _, y₂, h₇, -, ⟨_, _, _, u, b, l, k'⟩, h₉'⟩ :=
    exists_link_split_le_classGauge hs h hc hq γ',
    inf_comm (link γ) _ ▸ exists_link_split_le_classGauge hs h' hd hq γ
  exists _, r, by grind
  let Q := diagonal (S.linkForm.diag / S.linkMetric.diag)
  have L := by simpa [Matrix.mul_assoc _ _ Q, y'ᴴ.mul_assoc _ S.linkForm, (by
    simp [← ext_iff, Q, linkMetric, mul_apply, diagonal_apply, middleGram]; grind :
    S.linkMetric * Q = S.linkForm ∧ Qᴴ * S.linkForm = (2 : E) ^ 2 • S.linkMetric),
    ← Matrix.mul_assoc, abs_norm_eq_prod_norm_sq, map_ofNat, ← pow_mul, -Nat.cast_mul] using
    (liouville_gram S.linkMetric_posDef ((S.g⁻¹ : E) • y) (Q * y') v v' · zero_le_one <|
    one_le_genIndex <| IsIntMatrix.det_mem ·)
  apply le_of_sq_le_sq <;> simp_rw [linkDiscSq, classGauge, termDiscNorm, abs_norm_eq_prod_norm_sq,
    mul_pow] at *
  grw [← h₉, ← h₉', ← mul_one (_ ^ 2), L (mt exists_mulVec_eq_zero_iff.2 fun ⟨t, ht, h⟩ ↦ ht (h₇ t
    ⟨mem_link_iff_orthogonal.2 (by simp [← e₇, star_mulVec_dotProduct, ← Matrix.mul_assoc, h,
    gram_linkForm_eq_zero_of_le_link _ y₂, e]), y₂ ⟨t, rfl⟩⟩))
    (by simpa [gram_linkForm_eq_zero_of_le_link e₆, gram_linkForm_eq_zero_of_le_link (γ := γ'),
    ← finAdeleMat_conjTranspose, ← Matrix.map_mul, *, ← (finAdeleMat _).mul_assoc, -Nat.cast_mul]
    using (congr($kᴴ * finAdeleMat ((S.g⁻¹ : E) • S.linkForm) * $k').subst (by
    convert ((i.isInt_conjTranspose.mul S.isUnimodular_latMiddle.splitGram.isIntMatrix).mul
      ((S.principalLevel_eq_unitaryLevel.le (mul_inv_cancel s ▸ termsOver.mul h
      (.inv h'))).2.mul l)).neg
    simpa [Matrix.map_sub, Units.smul_def, smul_sub, coe_termPosition, classCoord, gIdele,
      finAdeleMat_conjTranspose, -map_mul, map_splitGram_ratMiddle, ← classCoord_conj_splitGram c,
      fromBlocks_smul] using congr(wᴴ * finAdeleMat ($(gram_linkMatrix_mul a b ..)) * u))))]
  ring_nf; rfl
  positivity
end Filling
end

-- part: New.RealPlace.VolumeKernel
section
/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Frames with equal Gram block and congruent middle parts are lattice translates. Volume
weight for the Schur test, dominated by a kernel with Hua-type integral bound. -/
seal Finset.univ Finset.sum Finset.prod

noncomputable section

open Fin ENNReal Finset MatMul Matrix Pointwise Submodule

namespace Filling

variable {E} [Field E] [CMType E] {𝔰} {S : Filling E 𝔰} {γ j c}

/-- Let c ∈ Ô be an idele, K ⊇ cÔ^σ, Y(a) integral, m primitive π×τ, |π| = |τ| + s, |τ| ≤ l, and
[M_a : K ∩ M_a] | n(a), M_a = Y(a)mÔ^τ. If every nonempty subset of B on which the columns
of Y agree modulo K has at most x elements, then ∑_B n(a)^(−l) ≤ [Ô : cÔ]^(|σ|(|σ|+s))·x. -/
lemma tsum_inv_index_pow_le_of_congr [StablyUnram E]
    {α π σ τ : Type} {x : ℝ≥0∞} [Fintype σ] [Fintype τ] [Fintype π]
  {c : (𝔸f E)ˣ} (hc : ↑c ∈ Ô E) {B : Set α} (Y : α → Matrix σ π _) (hY : ∀ a ∈ B,
  IsIntMatrix (Ô E) (Y a)) {m : Matrix π τ _} (hm : IsPrimitiveMatrix (Ô E) m) {s} (e :
  τ ⊕ Fin s ≃ π) {K} (hK : c • intVectors .. ≤ K) (n : α → ℕ) (hn : ∀ a ∈ B,
  submoduleIndex K (colLattice (Ô E) (Y a * m)) ∣ n a) l (hl : Fintype.card τ ≤ l) (H : ∀ᵉ (D ⊆ B)
  (_ ∈ D), (∀ᵉ (a ∈ D) (b ∈ D), colLattice _ (Y a - Y b) ≤ K) → ∑' _ : D, 1 ≤ x) : ∑' a : B,
  .ofReal (n a ^ l)⁻¹ ≤ .ofReal ((genIndex c.1 ^ Fintype.card σ) ^ (Fintype.card σ + s)) * x := by
  choose V o u _ q r using fun a ↦ isValuationPair_Ohat.hermite .inr ((Y a * m)ᵀ.fromRows 0)
  have p a j : u a j ∈ colLattice _ (Y a * m) := ⟨_, ((o a).isIntMatrix_inv (.inr j) <| .inl ·), by
    simp [← r, funext_iff, mul_apply, mulVec_eq_sum]⟩
  have i a h j := colLattice_le (L := intVectors ..) ((hY a h).mul hm.1).isInt_transpose (p a j)
  obtain ⟨U, hU, rfl⟩ := (isValuationPair_Ohat.exists_firstCols_iff e).2 hm
  grw [tsum_le_of_colouring (fun _ ↦ _ ⊕ᵥ _) (submoduleIndex_smul_ne_zero hc) (fun a h ↦
    Sum.rec (i a h) (((hY a h).mul hU.isIntMatrix).isInt_transpose <| e <| .inr ·)) (fun a ↦
    .ofReal (n a ^ l)⁻¹) x fun D s _ _ f ↦ ?_]
  simp [submoduleIndex_smul_intVectors hc]
  have z := (ne_zero_and_le_of_dvd (submoduleIndex_smul_ne_zero hc)
    (submoduleIndex_dvd_of_le .id hK ((iSup₂_le (colLattice_le <| i · <| s ·)).trans (by simp)))).1
  choose k y using fun a h ↦
    (submoduleIndex_dvd_of_le 1 le_rfl (iSup₂_le (colLattice_le fun j ↦ mem_sup.2
    ⟨_, ⟨_, p .., rfl⟩, _, hK <| f · · _ h (.inl j), add_sub_cancel ..⟩))).trans (hn a (s h))
  simp [y, ← inv_pow]
  grw [Nat.cast_inv_le_one, tsum_set_const, ← tsum_set_one, tsum_le_of_colouring _ z (fun a k j ↦
    mem_iSup_of_mem a (mem_iSup_of_mem k ⟨_, ((o a).isIntMatrix (.inl j) <| .inr ·),
    (mulVec_transpose ..).trans congr($(q a) _).symm⟩)) (fun _ ↦ 1) _ fun _ t ↦ (H _ (by tauto)
    · · ∘ fun g a k b h ↦ map_le_iff_le_comap.2 fun _ ↦ (colLattice_le (by simpa [reindex_equiv e]
    using ⟨g a k b h, (hK <| f a (t k) b (t h) <| .inr ·)⟩) ⟨_, hU.isIntMatrix_inv.mulVec ·,
    inv_mulVec_eq_vec rfl⟩)), hl, mul_right_comm, ← ofReal_mul] <;> simp [z, ← Nat.not_lt]

attribute [-simp] MulMemClass.coe_mul Nat.cast_mul Subgroup.coe_mul

attribute [local simp] gIdele_val mulVec Matrix.mul_apply splitGram frameGram middleGram
  Units.smul_def dotProduct funext_iff mul_pow

lemma HasLevel.middle_shared_vector_le (h : S.HasLevel j γ) (b : Fin _) (hb : b.1 < j → b = 𝔰.top) :
    let y := frameImage γ.1.1 *ᵥ col (paddedLeading j (S.frameProducts γ))⁻¹ b
    (∀ a, y (eStar a) = 0) ∧ ∀ v, 5 * ∑ i, ‖Φ v (y (𝔰.indexX₀ i))‖ ^ 2 ≤ 1 :=
  (le_or_gt ..).rec (h.exists_shared_frame_vector · |>.rec fun _ e ↦
  e ▸ by simp [↓frameImage_one_mulVec]) fun h₀ ↦ (norm_sq_middle_part_eq
  (by simpa [paddedLeading, h₀.trans_le', is_le, hb h₀] using congr(col $h.paddedLeading_mul_inv b))
  rfl).imp (·.1) (by grw [S.le_N]; simp [↓·, mul_nonneg])

lemma col_eq_zero_of_norm_lt_one {n} {l : Matrix 𝔰.κ n E} (h : IsIntMatrix (Ô E)
  (S.classCoordX₀ c * finAdeleMat l)) {i} a (H : ∀ v, ∑ a, ‖Φ v (l a i)‖ ^ 2 < 1) :
  l a i = 0 := congr($(S.eq_zero_of_ratMiddle_form_eq_zero (lᵀ i ⊕ᵥ 0) rfl
  (eq_zero_of_norm_Φ (by simpa [↓gram_mul, ↓gram_classCoordX₀, ← algebraMap_mem_Ô] using
  (h.isInt_conjTranspose.mul S.isUnimodular_latMiddle.isIntMatrix).mul h i i)
  (by simp; grw [norm_sum_le]; simpa [← sq]))) (.inl a))

lemma IsLabelledTerm.eq_of_frameImage_eq [S.IsAdmissible]
    {j t p p' u u'} (hu : u ∈ S.classUnip₀ c) (hu' :
  u' ∈ S.classUnip₀ c) : S.IsLabelledTerm j c t p → S.IsLabelledTerm j c t p' →
  frameImage (u * p.2).1.1 = frameImage (u' * p'.2).1.1 → p = p' := by
  rintro ⟨o, s, h, rfl⟩ ⟨o', r, g, e⟩ f
  obtain ⟨⟨k, rfl, a⟩, k', rfl, a'⟩ := one_mul s ▸ termsOver.mul hu.1.2 h,
    one_mul r ▸ termsOver.mul hu'.1.2 g
  refine (termsOver.eq_and_mem_classUnip₀ ⟨k, rfl, a⟩ ⟨_, Equiv.injective _
    (Prod.ext (QuotientGroup.eq.2 ?_) e), a'⟩ f).rec fun e x ↦ Prod.ext e (by rw [← o.1.2,
    (DoubleCoset.eq (b := p'.2)).2 ⟨_, mul_mem (inv_mem hu') hu, _, x, by group⟩, e, o'.1.2])
  use k'⁻¹ * k, mem_besselS_iff_frameImage.2 (by erw [frameImage_inv_mul_eq_iff.2] <;> simp [*,
    frameImage_termPosition]), by simp

/-- Let γ, γ' have level j and equal Z, ξ rows of Z including all below min(j,ϱ). If the middle
rows of h_c⁻¹γ'h_c''f − h_c⁻¹γh_c'f lie in the Ô-row span of gξ and g·`Filling.paddedLeading` j Z,
then γ'f − γf below the e-rows is g·l·ξ on X₀, `Filling.classCoordX₀` c·l integral.
Here f is the frame, Z = `frameProducts`, h_c⁻¹γh_c' = `termPosition`, g the number `S.g`. -/
lemma HasLevel.exists_frameImage_toRows₂_eq_add [StablyUnram E]
    {c' c'' γ γ' j ι} [Fintype ι] (q : ι ↪ _) (h :
  S.HasLevel j γ) (H : ∀ a ∉ Set.range q, ↑j ≤ a.1) (h' : S.HasLevel j γ') (e : S.frameProducts γ' =
  S.frameProducts γ) : let ξ := (xRows (S.frameProducts γ)).submatrix q id
  let t := (S.g : E)⁻¹ • (paddedLeading j (S.frameProducts γ))⁻¹
  (∀ r, (frameMiddle (S.termPosition c c'' γ') - frameMiddle (S.termPosition c c' γ))ᴴ.col r ∈
    S.gIdele • colLattice (Ô E) (finAdeleMat ξ)ᴴ ⊔ preimageLattice _
  (finAdeleMat tᴴ)) → ∃ l : Matrix _ ι E, IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMat l) ∧
    (frameImage γ').toRows₂ = (frameImage γ).toRows₂ + fromRows
    (fromRows (S.g • (l * ξ)) 0) 0 := let x := (frameMiddle γ'.1.1 - frameMiddle γ).toRows₁; by
    intro ξ t e'
    have ⟨a, _, ia, Q, iq, w⟩ := exists_preimageLattice_eq_colLattice ⟨_, gram_classCoordX₀ c⟩
    have := by simpa using forall_fin_succ'.1 (congrFun e)
    choose Λ iΛ f using (by simpa [Submodule.mem_sup, colLattice, frameMiddle,
      frameImage_termPosition, classCoord_eq_fromBlocks, -funext_iff,
      ← eq_sub_iff_add_eq', pointwise_smul_def] using e' ·)
    have ⟨μ, k, k'⟩ := DenseRange.exists_mem_open (f := finAdeleMat) (.piMap (.piMap ∘ fun _ _ ↦
      denseRange_algebraMap_finAdele)) ((isOpen_Ô.matrix.prod isOpen_Ô.matrix).preimage (f :=
      fun M ↦ (S.classCoordX₀ c * M, S.classCoordX₀ c * ((finAdeleMat x -
      S.gIdele • M * finAdeleMat ξ) * finAdeleMat t))) (by fun_prop)) ⟨a.1 * Q * Λᴴᵀ, by
      simpa [by simpa using congr(a.1 * $w * a.1⁻¹ * finAdeleMat (x * t))] using!
        And.intro (ia.mul (iq.mul (.isInt_conjTranspose (.isInt_transpose iΛ)))) (ia.mul (iq.mul
        (N := (S.classCoordX₀ c * finAdeleMat x - S.gIdele • Λᴴᵀ * finAdeleMat ξ) * finAdeleMat t)
      (by simpa [x, *, mul_sub, ← Algebra.commutes] using! star_mem_Ô <| f · ·)))⟩
    let L := (x - S.g • μ * ξ) * t
    have v b hb r : L r b = 0 := col_eq_zero_of_norm_lt_one (by simpa [L] using k' · ·) r (by
      simp_intro v [L, x, t, ξ, sub_mul, ← mul_sum, -map_sum, by simpa using
        (h.middle_shared_vector_le b hb).1]
      grw [norm_sub_le, add_sq_le, ← mul_sum, sum_add_distrib,
        ← (by simp : S.g ≠ 0).pos.nat_succ_le]
      linarith! [(h.middle_shared_vector_le b hb).2 v, (e ▸ h'.middle_shared_vector_le b hb).2 v])
    use L.submatrix id (castSucc ∘ q) + μ, (by simpa [mul_add, L] using add_mem (k' _ _) <| k · ·)
    rw [Matrix.add_mul, (Matrix.ext fun k b ↦ Fintype.sum_of_injective _ (q.trans castSuccEmb).2 _ _
      (by simp_all [forall_fin_succ']) (by simp [paddedLeading, ξ]; grind) : _ * _ =
      L * paddedLeading j (S.frameProducts γ))]
    simp [L, x, t, h.2, ← ext_iff, *, -frameGram]

end Filling

open Fintype MeasureTheory Real ComplexOrder Norms.L2Operator IsHermInvolution
variable {𝔰 : Shape} (γ : 𝔰.G₁)

/-- The volume Δ(γ) = |det ⟨v_a, γ⁻¹f_b⟩|, Euclidean products, for the basis v = (e₁ − e*₁, …,
e_ϱ − e*_ϱ, 2z) of a maximal negative subspace. -/
def frameVolume := ‖(((1 - 𝔰.J₁) * 𝔰.frameCols)ᴴ * γ⁻¹.1.1 * 𝔰.frameCols).det‖

/-- For γ in G₁, the κ × (ϱ+1) complex matrix whose columns are the X₀-components of the images
γe₁, …, γe_ϱ, γz of the frame vectors. -/
def frameX₀Part := 𝔰.definiteColsᴴ * γ.1.1 * 𝔰.frameCols

/-- The volume weight Δ(y) is strictly positive for every y ∈ G₁. -/
lemma frameVolume_pos : 0 < frameVolume γ := by
  simp_rw [frameVolume, norm_pos_iff, ← exists_mulVec_eq_zero_iff.not, ← mulVec_mulVec]; rintro ⟨⟩
  set w := γ⁻¹.1.1 *ᵥ _ with ← e
  simpa [inclMatrix_gram_eq_one besselFrame_injective, *] using congr(𝔰.frameColsᴴ *ᵥ γ *ᵥ $(e.trans
    (dotProduct_star_self_pos_iff.not_left.1 (have := e ▸ U.form_mulVec_mulVec ..
    by simp_all [-sub_mulVec, inclMatrix, entrywise, sum_univ_castSucc, funext_iff,
      forall_fin_succ', add_neg_eq_zero, J₁_eq, RCLike.conj_mul, not_lt_of_ge]))))

attribute [local simp] Matrix.mul_apply inclMatrix_gram_mul_eq_zero frameVolume castLE_injective
  ne_of_gt abs_of_pos frameGram
  inclMatrix_gram_mul_eq_self inclMatrix_gram_eq_zero forall_fin_succ' frameX₀Part

attribute [local simp ←] conjTranspose_submatrix

/-- The volume Δ on G₁ is left invariant under 𝖴⁰: for u in the subgroup 𝖴⁰ of the Bessel
unipotent group fixing every frame vector, and any y in G₁, Δ(uy) = Δ(y). -/
lemma frameVolume_mul_left (hu : γ ∈ besselU0) y : frameVolume (γ * y) = frameVolume y := by
  cases mem_besselU0_iff_unipotentOf.1 (inv_mem hu)
  simp [val_unipotentOf_coe, *]

@[fun_prop] lemma continuous_frameVolume : Continuous (@frameVolume 𝔰) := by fun_prop [frameVolume]

/-- Fix `besselSize` y ≤ θ, e: σ ↪ j, V; R, z = Z_j (leading block) invertible. Some measurable
K has ∫K ≤
((2θ²)^j/|det z|)^(k+n)(π^|σ|/(|σ|!θ^{2|σ|}|det R|²))^k, and (Δ(y)/Δ(γ⁻¹y))^(k+n) ≤ K(A)
whenever Z(γ) = Z, `IsNormalForm` j γ, and γf₁, …, γf_j have X₀-components V + (AR,0)z. -/
lemma exists_kernel_frameVolume_le {y θ} (hθ : besselSize y ≤ θ) {σ j} [Fintype.{0} σ] (e :
  σ ↪ Fin j) (R : Matrix σ σ ℂ) (hR : R.det ≠ 0) {Z : 𝔰.FrameMat} {l : j ≤ 𝔰.n} : let i := castLE l
  let z := Z.submatrix i i
  z.det ≠ 0 → ∀ V, ∃ K, Measurable K ∧ ∫⁻ a : Matrix 𝔰.κ σ ℂ, K a ≤ .ofReal (((2 * θ ^ 2) ^ j /
  ‖z.det‖) ^ (𝔰.k + 𝔰.n) * (π ^ Fintype.card σ / (Fintype.card σ).factorial /
    (θ ^ Fintype.card σ * ‖R.det‖) ^ 2) ^ 𝔰.k) ∧ ∀ γ A, realFrameGram γ = Z → IsNormalForm j γ →
    frameX₀Part γ * inclMatrix ℂ i = V + A * R * (inclMatrix ℂ e)ᴴ * z →
    .ofReal ((frameVolume y / frameVolume (γ⁻¹ * y)) ^ (𝔰.k + 𝔰.n)) ≤ K A := by
  have ⟨ω, ι, g⟩ := _root_.exists_norm_le_of_besselSize_le hθ
  intro i z hD V
  have := (Units.norm_pos _).trans_le g
  let T := (θ • frameMatrix ω).submatrix i i
  have : T.det = θ ^ j ∧ (T.submatrix e e).det = θ ^ Fintype.card σ := by constructor
    <;> erw [det_smul_of_tower θ, det_eq_one_of_unitriangular fun _ _ ↦
    (frameMatrix_unitriangular ι _ _ ·|>.trans _)] <;> simp [i]
  have hB := (mul_mul_eq_of_mul_eq rfl).symm.trans (nonsing_inv_mul _
    (norm_pos_iff.1 (frameVolume_pos y)).isUnit)
  set B := (_ : 𝔰.FrameMat) * (_ : type_of% 𝔰.frameColsᴴ)
  let I := inclMatrix ℂ (𝔰.besselFrame ∘ i)
  let p := Z.submatrix id i * z⁻¹
  have o : p.submatrix i id = 1 := mul_nonsing_inv _ hD.isUnit
  let C := T * pᴴ * B
  let c := (V * z⁻¹ * Tᴴ - 𝔰.definiteColsᴴ * Cᴴ) * inclMatrix ℂ e
  let S := R * ((T * inclMatrix ℂ e)ᴴ * inclMatrix ℂ e)
  refine ⟨_, by fun_prop, (lintegral_eq_lmarginal_univ 0).trans_le ((hua_integral_le S ?_ c
    .one (by bound) _ (card_le_of_embedding (e.trans (castLEEmb l))) _).trans_eq
    (congrArg _ (congrArg _ ?_))), fun γ A s ⟨_, u, h⟩ v ↦ ENNReal.ofReal_mono ?_⟩
  iterate 2 simp [S, mul_inclMatrix, *, mul_comm]
  let t := γ.1.1 * I * z⁻¹
  have f : 𝔰.frameColsᴴ * 𝔰.J₁ * t = p :=
    mul_mul_eq_of_mul_eq (by simp [← s, I, inclMatrix, ← ext_iff])
  let M := B * t * z - inclMatrix ℂ i
  choose X _ w x using fun b ↦ show ∃ X Y, (B * γ.1.1 * 𝔰.frameCols) *ᵥ Y = (1 + M * pᴴ) *ᵥ X ∧
      ‖X b‖ = 1 ∧ Y b = 1 ∧ ∀ a > b, X a = 0 ∧ Y a = 0 by
    by_cases! b < j; use Pi.single b 1, Pi.single b 1
    simp_all [M, t, I, i, funext_iff, (congr($o ⟨b, ‹_›⟩) : p b = _), inclMatrix]
    obtain ⟨X, Y, e, rfl, _⟩ := h b ‹_›
    use X, Y, ?_, by simpa using congr(√‖$u‖)
    convert congr((B + M * tᴴ * 𝔰.J₁) *ᵥ $e).symm <;> simp [← mul_inclMatrix, ← f, t,
      isHermitian.eq, ← U.form_mul_inv_eq, *]
    simp [I, J₁_eq, (funext fun a ↦ besselFrame_castSucc ⟨a, by lia⟩ : 𝔰.besselFrame ∘ i = _)]
  have k : I = _ := (mul_inclMatrix 𝔰.frameCols i).symm
  let Y := 𝔰.J₁ * t * Tᴴ - Cᴴ
  let W := 𝔰.definiteColsᴴ * Y
  let G := A * S + c
  have P := PosDef.one.add_posSemidef G.posSemidef_self_mul_conjTranspose
  have n := congr(‖det $((ext_col w : _ * (of _)ᵀ = _ * (of X)ᵀ))‖)
  simp +contextual [*, M, mul_inclMatrix pᴴ, ↓det_mul, ← Matrix.mul_assoc, ↓M.det_one_add_mul_comm,
    det_of_isLowerTriangular (of _), BlockTriangular] at n
  grw [show ∑ i, _ = Gᴴ * G by ext; apply Matrix.sum_apply, det_one_add_mul_comm, show _ / _ = _ by
    simp [B, field, -conjTranspose_sub].trans congr($n⁻¹), (det_one_add_mul_comm W _ ▸
    ostrowski_taussky (Θ := -C * t * Tᴴ) (.add .one W.posSemidef_conjTranspose_mul_self)
    ?_ :).trans' (norm_det_le_norm_det_of_posSemidef P.posSemidef ?_)]
  iterate 2 simp [C, *, det_neg, pow_two, mul_pow, field, ↓det_mul, div_pow, P.det_pos.ne']
  let D := C * y.1.1
  let Q := θ⁻¹ • (ω * y)⁻¹.1.1 * I
  convert (posSemidef_bessel (E := Q) (by grw [l2_opNorm_mul, norm_smul, U.norm_inv, g,
    norm_inclMatrix_le_one] <;> simp [*, i, besselFrame_injective]) D).add
    (𝔰.zColᴴ * I * z⁻¹ * Tᴴ).posSemidef_conjTranspose_mul_self
  simp [(by simp +contextual [W, ← ext_iff, inclMatrix, J₁_eq] : 𝔰.frameColsᴴ * Y = 0 → Wᴴ * W =
    Yᴴ * (𝔰.J₁ * Y)) (by simp [Y, *, C, ← Matrix.mul_assoc, ← B.conjTranspose_mul]), Y, t,
    isHermitian.eq, mul_mul_eq_of_mul_eq mul_self, mul_mul_eq_of_mul_eq (U.form_mul_inv_eq γ).symm,
    ← D.conjTranspose_mul, show D * Dᴴ = -(C * (𝔰.J₁ * Cᴴ)) by
    simpa [D, C, B, mul_mul_eq_of_mul_eq mul_self] using congr(C * $(U.coe_inv mul_self y⁻¹) *
      Dᴴ), show D * Q = 1 by simp [D, C, mul_mul_eq_of_mul_eq hB, mul_inclMatrix pᴴ, *,
    mul_eq_one_comm (a := T), ← show y⁻¹.1.1 * I = Q * T by
    ext a b; simp_rw +zetaDelta [mul_inclMatrix]; apply congr($(frameVector_eq_sum (i b) ι) a).trans
    rw [mul_apply, sum_of_injective i] <;> simp [frameVector, field,
      i]; grind [frameMatrix_unitriangular, one_apply_ne]]]
  simp [k, J₁_eq]; abel
  convert posSemidef_bessel (norm_inclMatrix_le_one e.2) W
  simp [W, Y, G, S, c, t, k, ← sub_eq_of_eq_add v, hD, J₁_eq]; abel

lemma frameX₀Part_unipotentOf_inv_mul q : frameX₀Part ((unipotentOf q)⁻¹ * γ) =
  frameX₀Part γ + q.1ᴴ * Filling.xRows (realFrameGram γ) := by simp [← ext_iff, inclMatrix,
  splitGram, middleGram, val_unipotentOf_coe, ↓by simpa using U.coe_inv mul_self (unipotentOf q)]
end
end

-- part: New.Filling.SchurTest
section
/-! Part of: Incoherent and degenerate pairs are negligible (see New.Filling.CrudeEnergy).

This file: Energy of terms of the second moment; splitting; passage to cut Bessel functions. Size
function of a class of terms; open-cell mass fits under it. -/

open Subgroup ComplexOrder ENNReal Finset MeasureTheory Real

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {V : Type _} {S : Filling E 𝔰}
  [NormedAddCommGroup V] (A : S.Classes → S.GRes → S.Classes → V) (Ω : Set _) (T : Set ↥(S.G E))
  (Ω' : Set _)

/-- The energy over Ω of a family A of vectors in a normed group: ν⁻² (ν = `Filling.unipCovolume`)
times the sum of ‖A(c, s,
c')‖² over classes c, c' and s ∈ Ω. -/
noncomputable def energy := ∑ c, ∑ c', ∑ s with s ∈ Ω, ‖A c s c'‖ ^ 2 / S.unipCovolume ^ 2

/-- The sum, over c, c', s ∈ Ω and links Λ ∈ R, of the squared norms of the blocks over (c,s,c')
of the elements of T with link Λ. -/
noncomputable def linkEnergy [Side] (R : Set _) := ∑' (c) (c') (s : Ω') (Λ :
  R), ‖S.amplitudeSum (T ∩ link ⁻¹' {Λ.1}) c s.1 c'‖ₑ ^ 2

variable [StablyUnram E] [S.IsAdmissible] (U : Set ↥(S.G E)) {ε : ℝ}
  {A B : S.Classes → S.GRes → S.Classes → V} {Ω : Set _}

lemma amplitudeSum_split [Side] : S.amplitudeSum T = S.amplitudeSum (T ∩ Uᶜ) + S.amplitudeSum
  (T ∩ U) := funext₃ fun _ _ _ ↦ (tsum_congr_set_coe _ (by grind)).trans
  ((summable_amplitude ..).tsum_union_disjoint (by grind) (summable_amplitude ..))

omit [StablyUnram E] [S.IsAdmissible] in
lemma energy_add_le (hε : 0 < ε) : energy (A + B) Ω ≤
  (1 + ε) * energy A Ω + (1 + ε⁻¹) * energy B Ω := by
  simp [energy, mul_sum, ← sum_add_distrib]
  gcongr; grw [norm_add_le, add_sq, two_mul_le_add_mul_sq hε]; grind

/-- Under `Filling.IsAdmissible`, for any set U of rational terms and any Ω, the family A_U − A♭_U,
the difference of the amplitude sums for the Bessel functions and for their cuts, has energy
over Ω at most b⁻³⁰d₁, d₁ = `Filling.besselEnergy`. -/
lemma energy_sub_cut_le : energy (S.amplitudeSum U - S.amplitudeSum (σ := .cut) U) Ω ≤
  (S.b ^ 30)⁻¹ * S.besselEnergy := by
  simp [energy, amplitudeSum, summable_amplitude, ← Summable.tsum_sub, ← Finset.sum_div,
    @sum_comm S.GRes, ← toReal_enorm]
  obtain ⟨⟨r, k⟩⟩ := S.ϱ_le_k.dest, S.one_le_b, S.k_le_f, S.unipCovolume_pos
  grw [besselEnergy, columnDim, ← le_mul_of_one_le_right' NeZero.one_le, filter_subset,
    sum_sq_le_sq_sum_of_nonneg, ← Nat.card_pos.succ_le, (toReal_sum _).ge,
    toReal_le_of_le_ofReal _ ∘ (amplitudeAbs_lt_top_and_cut_le U ..).2.trans']
  any_goals simp [field, unipCovolume_pos, le_of_lt]
  grw [Fintype.card_eq_nat_card, Nat.card_pi, Nat.card_pi.le, card_GL_le _]
  simp [card_resField_eq_levelPrime, S.card_chosenPlaces, ← mul_pow, -Nat.cast_mul]
  grw [g_le_b_pow, ← one_le_two]; simp [← pow_mul, ← pow_add, ← k]; gcongr; lia
  simp [amplitude, ← integral_sub, ← smul_sub, -toReal_mul, fun [Side] c s d γ ↦
    integrable_toReal_smul (by fun_prop) (by fun_prop)
    ((ENNReal.le_tsum γ).trans_lt ((amplitudeAbs_lt_top_and_cut_le U c s).1 d).2)]
  grw [enorm_tsum_le_tsum_enorm, enorm_integral_le_lintegral_enorm, enorm_toReal_smul_le]

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰) (c : S.Classes)
  (γ : ↥(S.G E)) (c' : S.Classes) (γ' : ↥(S.G E))

/-- The number τ²·√(D/(M·g^(2min(ϱ,j)kf)·x^(k+1))), with M = `Filling.countWeight` 0, k = |κ|, f the
number of infinite places, and D = 𝖽 for j > ϱ, else τ^(13−32j)𝖽₁. -/
noncomputable def classSize (j : Fin (𝔰.ϱ + 2)) x := S.tailScale ^ 2 * √(ite (𝔰.ϱ < j) S.mainEnergy
  (S.tailScale ^ 13 / (S.tailScale ^ 32) ^ j.1 * S.besselEnergy) /
  (S.countWeight 0 * S.g ^ (2 * min 𝔰.ϱ j * 𝔰.k * numInfPlaces E) * x ^ (𝔰.k + 1)))

/-- Let γ be near with x = ∏_v|𝗀_v(γ)| ≥ 1, and let a be the top-level class size
`Filling.classSize` at x. Then b^(−k³f) ≤ a, and the product over infinite places of the open-cell
masses `cellMass` at γ is at most (νa/2)². -/
lemma IsNear.le_classSize_and_cellMass_le {S : Filling E 𝔰} {γ} [ok : S.IsAdmissible] (n :
  S.IsNear γ) (N : 1 ≤ S.termDiscNorm γ) : (S.b ^ (𝔰.k ^ 3 * numInfPlaces E))⁻¹ ≤ S.classSize ⊤
  (S.termDiscNorm γ) ∧ ∏ v, cellMass (S.ratToInf γ v) (S.besselSys v).deg S.boxSize (Fintype.card
  (S.besselSys v).I) ≤ (S.unipCovolume * S.classSize ⊤ (S.termDiscNorm γ) / 2) ^ 2 := by
  apply S.of_size_bounds; intros
  obtain ⟨⟨_, e⟩, b, m, Q, q, h, t, K⟩ := S.ϱ_le.dest, S.one_le_b, ok.packetConst_mul_mass_le,
    S.N_le, S.size_le, S.pow_le_k, ‹2 ≤ S.tailScale›,
    univ.one_le_prod₀ fun v _ ↦ S.one_le_abs_kappa v, Nonempty.intro 𝔰.k₀,
    S.besselDegree_pos, mass_pos E 𝔰.r, rootDiscr_pos E, 𝔰.openCellConst_pos
  rw [classSize, termDiscNorm, frameScaleProd, ite_eq_left, min_eq_left] at *; constructor
  grw [countWeight, ← ok.besselEnergy_le, besselEnergy, columnDim, g_le_b_pow, ← S.N_prime.one_le,
    ← t, ← one_le_two, one_pow, ← t, ← one_le_two, fun v ↦ ((n.norm_map_leadingMinor_le ⊤ v).trans'
    (by simp [↓← Complex.real_le_real, ↓← map_termDisc_eq_norm, frameDisc,
    RCLike.mul_conj]; bound) : ‖Φ v (S.termDisc γ)‖ ≤
    _), one_mul, ← @NeZero.one_le (Fintype.card S.BesselCoord), ← le_sqrt_of_sq_le]
  simp [field, ← pow_mul, ← pow_add]; gcongr; exact h.dest.choose_spec ▸ by lia
  simp_rw [cellMass, mainEnergy, besselDegree, gramDiscReal_realFrameGram_ratToInf, frameScaleSq,
    ← pow_abs_two_mul (kappa ..), add_comm 𝔰.k, pow_add] at *
  grw [packetConst, unipOrder, siegelConst, ← two_le_pi, tsub_le_self, Nat.factorial_le_pow, ← b,
    ← S.N_prime.one_le, abs_kappa_le, tsub_le_self, tsub_le_self] at m; set g := S.g
  simp (disch := positivity) only [volÔ_eq, abs_discr_eq_rootDiscr_pow, prod_pow_eq_pow_sum _ _ |_|,
    boxSize, columnDim, tailScale, Finset.prod_div_distrib, prod_const, prod_mul_distrib, card_univ,
    prod_pow, Fintype.card_pi, Fintype.card_fin, ← Real.log_le_log_iff, log_mul, log_div,
    Real.log_pow, Real.log_inv, Real.log_rpow, log_sqrt, Real.log_one, push_cast] at *; rify at *
  linear_combination (norm := rw [← neg_nonneg, ← e]) m + 3 * t + ↑(numInfPlaces E) *
    (((𝔰.k + 𝔰.ϱ + 0.5) * q + Real.log S.b * h) / 1000 + 𝔰.ϱ ^ 7 * Q)
  clear * - b N K; ring_nf; positivity
  repeat simp [one_le_pow₀, b]

/-- For a class c, the function equal to the cutoff β_c on the set `Filling.boxedPoints` and zero
outside it. -/
noncomputable def boxCutoff := S.boxedPoints.indicator (S.classCutoff c)

/-- The weight β⁰_c(γ⁻¹y)·∏_v (Δ(y_v)/Δ((γ⁻¹y)_v))^(k+ϱ+1) of Schur's test, with β⁰ the boxed
cutoff `Filling.boxCutoff`, Δ = `frameVolume` and k = |κ|. -/
noncomputable def schurWeight y := S.boxCutoff c ((S.ratToInf γ)⁻¹ * y) * ∏ v, .ofReal
    ((frameVolume (y v) / frameVolume (((S.ratToInf γ)⁻¹ * y) v)) ^ (𝔰.k + 𝔰.n))

attribute [local instance] Side.cut

/-- The integral over y of β⁰_c(y)·∏_v‖W_v(y_v)‖² times the weight `Filling.schurWeight` at (y,
γ⁻¹y), with β⁰ the truncated cutoff `Filling.boxCutoff`; used in Schur's test. -/
noncomputable def schurIntegral := ∫⁻ y,
  S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * S.schurWeight c' γ' y

variable [StablyUnram E] {S : Filling E 𝔰} {c c' : S.Classes} {γ : ↥(S.G E)} {X : Type _}
  [MeasurableSpace X]

omit [StablyUnram E] in
lemma inCut_of_besselKernel_ne_zero {y} (h : S.besselKernel γ y ≠ 0) v : InCut (y v) S.b ∧
  InCut (((S.ratToInf γ)⁻¹ * y) v)
  S.b := by simp_all [← enorm_pos, enorm_besselKernel, (S.besselSys v).tail.inCut_of_ne_zero]

@[fun_prop] lemma measurable_boxCutoff [S.IsAdmissible] :
  Measurable (S.boxCutoff c) := by delta boxCutoff boxedPoints frameBox; measurability

@[fun_prop] lemma measurable_schurWeight [S.IsAdmissible] :
  Measurable (S.schurWeight c γ) := by fun_prop [schurWeight]

lemma amplitudeAbs_sq_le [S.IsAdmissible] : S.amplitudeAbs c c' γ ^ 2 ≤
  S.schurIntegral c c' γ * S.schurIntegral c' c γ⁻¹ := by
  rw [mul_comm, schurIntegral, ← lintegral_mul_left_eq_self _ (S.ratToInf γ⁻¹)]
  apply sq_lintegral_le <;> try fun_prop
  by_contra! ⟨_, n⟩; cases by simpa using n.ne_zero
  simp_all [boxCutoff, classCutoff, boxedPoints, ↓inCut_of_besselKernel_ne_zero ‹_›,
    (isBoxPartition_epsilon c).2, ↓(isBoxPartition_epsilon c').2, enorm_besselKernel, schurWeight,
    sq]; ac_nf at n
  simp [← mul_assoc, ← prod_mul_distrib, ← ofReal_mul, ← mul_pow, field,
    frameVolume_pos, le_of_lt, ne_of_gt] at n

/-- Averaging: let s map (X, m) measurably to 𝖴⁰_∞, B ⊆ X with m(B) ≥ 1, F ≥ 0 be measurable and
left 𝖴⁰_c(g)-invariant, ∫_B F(u·s(x)·y)dm ≤ C for u ∈ 𝖴⁰_∞, y ∈ `Filling.boxedPoints`. Then
∫β⁰_c∏_v‖W_v‖²F ≤ C·ν·#`Filling.BesselCoord`, for W_v cut, β⁰ = `Filling.boxCutoff`. -/
lemma lintegral_boxCutoff_le_of_average [S.IsAdmissible] c (m : Measure X) [SFinite m] {s : X → _ →
  _} (ms : Measurable s) (hs : ∀ x v, s x v ∈ besselU0) {F} (mF : Measurable F) (hF :
  ∀ u ∈ S.classUnip₀ c, ∀ y, F (S.ratToInf u * y) = F y) B (hm : 1 ≤ m
  B) {C} (h : ∀ u, (∀ v, u v ∈ besselU0) → ∀ y ∈ S.boxedPoints, ∫⁻ x in B, F (u * s x * y) ∂m ≤
  C) : ∫⁻ y, S.boxCutoff c y * (∏ v, ‖(S.besselSys v).W .cut (y v)‖ₑ ^ 2) * F y ≤
  C * (.ofReal S.unipCovolume * Fintype.card S.BesselCoord) := by
  cases (S.exists_cutoff_classUnip _).choose_spec
  grw [Fintype.card_pi, Nat.cast_prod, ← (S.besselSys _).tail.lintegral_sq_cut_le,
    ← lintegral_classCutoff_mul_prod _ _ c]
  simp (disch := fun_prop) [lintegral_prod, ↓← lintegral_const_mul,
    ← (measurePreserving_pi_orbitMeasure 𝔰.besselHaar₀).lintegral_comp]
  gcongr 1; by_cases x ∈ S.boxedPoints
  any_goals simp +contextual [← ofReal_norm, norm_smul, ((S.besselSys _).tail.isBesselFunction _).2,
    boxCutoff, classCutoff, mul_mem_boxedPoints_iff, *, (isBoxPartition_epsilon c).2, mem_sup_left,
    Subgroup.mem_inf.1 (_ : besselU0).2, ← mul_assoc, mul_right_comm _ _ (F _)]
  set p := Exists.choose _
  have e t := ((Equiv.inv _).tsum_eq _).trans congr(∑' k : (S.classUnip₀ c).subgroupOf (S.classUnip
    c), $(lintegral_mul_left_eq_self (μ := .pi fun _ ↦ 𝔰.besselHaar₀) (fun u ↦ (p * F) (((u *
    t) · |>.1) * x) * p (S.ratToInf k * (u · |>.1) * x)) (⟨_, ratToInf_mem_besselU0 k⁻¹.2.2 ·⟩)))
  simp (disch := first | fun_prop | simp [← mem_subgroupOf]) [mul_assoc, ← Pi.mul_def
    (S.ratToInf _), *, ← lintegral_tsum, ↓lintegral_mul_const, -lintegral_const_mul] at e ⊢
  grw [← mul_one (lintegral ..), hm, ← setLIntegral_const, funext fun x ↦
    (lintegral_mul_right_eq_self _ (⟨_, hs x ·⟩)).symm.trans (e _).symm, lintegral_lintegral_swap]
  gcongr; rw [lintegral_mul_const]; bound
  repeat fun_prop
end Filling
end
