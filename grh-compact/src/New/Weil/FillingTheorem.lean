import New.Filling.GlobalToLocal
import New.Weil.DegreeBounds
import New.Weil.LatticeAndTorsionDefs
import New.Weil.DegreeOfT
import New.Weil.EdgePair
import New.Weil.UnfoldingStep
import New.Filling.LatticeChart
import New.Weil.TwistedHeckeType
import New.Weil.LabelRigidity
import New.Weil.Moments
import New.Weil.RowDimension

section
/-! Set-up for this proof: size bookkeeping for the data of this proof.

This file: Index and class counts of columns; the filling data are admissible. -/

namespace Data

open Finset Real Filling Subgroup MulAction Fintype Shape NeZero NumberField
variable {P} (D : Data P)

/-- The elements of the stabiliser of the standard lattice of X₀ that preserve the lattice of Y₀
have
index (N^k − 1)^f. -/
lemma relIndex_latStabilizer : (comap D.filling.inclHFin D.filling.latStabilizer).relIndex (Kf ..) =
  (D.N ^ D.k - 1 : ℝ) ^ D.f := by
  rw [(?_ : comap .. = levelOf (↑) (pi ⊤ fun w : D.piPlaces ↦
    (stabilizer _ (Pi.single D.shape.k₀ 1 : _ → ResField w.1)).comap invTransposeGL.toMonoidHom)),
    relIndex_levelOf (h := ⟨by simp, by simp [D.isSplitLevel_piPlaces.star_notMem]⟩)]
  simp [index_pi_univ, index_comap, index_stabilizer_GL_vector, card_ResField,
    D.isSplitLevel_piPlaces.q_eq, ↓card_X₀, card_piPlaces, Fin.pos']
  ext; erw [inclHFin_mem_latStabilizer, mem_levelOf]
  refine exists_prop.symm.trans (exists_congr fun h ↦
    (?_ : _ ↔ ∀ w _, (transposeGL _)⁻¹ ∈ stabilizer ..))
  simpa [funext_iff, Units.smul_def, ↓dvd_def, ← mem_piPlaces, Subtype.ext_iff, -reduceAt_eq_zero]
    using! (forall₂_congr fun (_ : Unit) j ↦ dvd_iff_reduceAt_eq_zero D.intValuation_pi (⟨_,
    h.isIntMatrix (.inr ()) j⟩ - ite (j = D.shape.k₀) 1 0)).trans forall₂_comm

lemma card_classes_filling : card D.filling.Classes =
  Nat.card (D.filling.reducedImage besselH) * (D.N ^ D.k - 1) ^ D.f * mass D.E D.k := by
  erw [card_eq_nat_card, card_classes_eq_classSum D.classAut_columnLevel_eq_bot,
    classSum_one_of_le IsLevel.le, columnLevel_zero_eq_comap, ← relIndex_mul_relIndex _ _ _
    (comap_mono (map_subtype_le _)) fun _ ↦ ((inclHFin_mem_latStabilizer _).1 · |>.1),
    relIndex_comap, map_comap_eq, ← subgroupOf_map_subtype, relIndex_map_map_of_injective _ _ (by
    simp), relIndex_ker, range_inclHFin, classSum_stdRatPoints_eq_mass,
    card_X₀]; simp [D.relIndex_latStabilizer, reducedImage]

/-- The filling data of D satisfies `Filling.IsAdmissible`. -/
instance : D.filling.IsAdmissible := by
  obtain ⟨m, f, p, _⟩ := @mass_pos D.E, @nsmul_le_nsmul_right ℝ, sub_pos.2 (one_lt_pow₀
    (D.lt_of_hasLogBound (G := D.N)) D.k_pos.ne'), pos D.gProd, D.filling.besselDegree_pos,
    rootDiscr_pos D.E, D.filling.frameScaleProd_pos, @Nat.card_pos (D.filling.reducedImage besselH)
    _ _, @card_pos D.filling.BesselCoord _ _, D.N_prime.two_le, Nat.le_self_pow D.k_pos.ne'
    D.N, D.log_N_mem_Icc, D.k_le_r, D.k_pos, log_natCast_nonneg (card D.filling.BesselCoord),
    congr(D.k * D.m * $(mul_div_cancel₀ (∑ v, log (D.nominalWeight v)) (ne ↑D.f)))
  obtain _ := D.card_besselCoord_mul_factorial_le, m D.k, m D.r,
    f (log_natCast_nonneg (D.k - 1).factorial) D.f, f (log_le_log (by positivity)
    (D.le_of_hasLogBound : D.b ^ 19 ≤ D.gProd)) (D.f * D.k), f (log_le_log p (sub_one_lt
    _).le) D.f, (nsmul_right_mono D.f).mapsTo_Icc ⟨(log_le_sub_one_of_pos (div_pos (p.trans
    (sub_one_lt _)) p)).trans (by field_simp; norm_cast; lia),
    (D.le_of_hasLogBound : 2 / D.N ≤ D.logB)⟩, D.log_filling_besselDegree_mem_Icc,
    congr(D.f * ∑ i ∈ $(D.k.Ico_pred_singleton ‹_›), log i.factorial), (nsmul_right_mono (D.f *
    D.k)).mapsTo_Icc D.log_N_mem_window, ((abs_sum_le_sum_abs _ (Ico D.k D.r)).trans (sum_le_sum
    fun i _ ↦ abs_log_mass_ratio_sub_le D.E i D.ϱ D.nat_le_of_hasLogBound (by grind))).trans (by
    grw [le_sub_iff_add_le, ← le_log_one_add_of_nonneg (by positivity)]; simp [*]; use
      D.le_of_hasLogBound : _ ≤ log (1 + D.b⁻¹ ^ 9) - D.f * (2 / D.N)),
    le_sub_iff_add_le.2 (D.le_of_hasLogBound : |D.f * (D.m - 1) * (D.ϱ *
    log (D.gProd * D.rootDisc / 2 / π) + log (√D.rootDisc / 2 / π)) - D.m * ∑ v,
    log (D.nominalWeight v)| + (log 2 + log (1 + D.b⁻¹ ^ 9) + D.m * (D.m * ∑ v, log (D.nominalWeight
    v) + D.f * D.r * D.x⁻¹) + D.f * D.k * √D.logB) ≤ D.f * D.k * D.logB / 4), (D.le_of_hasLogBound :
    D.f * ((D.m - 1) * (D.ϱ * log (2 / D.rootDisc / D.gProd) - log √D.rootDisc) - (D.ϱ + 1) ^ 7 *
    ((D.m - 1) * log (D.gProd * D.rootDisc / 2 / π) - log (D.gProd * D.N))) ≤ D.f * D.k * D.logB)
  apply (by simpa only [← and_imp] using IsAdmissible.mk D.columnLevel_zero_eq_comap (⟨_,
    D.filling_fits.reduction_finiteEquiv_iff _ · |>.2 ⟨_, reduceFamily_liftResidue
    (w := D.chosen) _⟩ |>.2⟩) : _ → _)
  rify [card_X₀, @id (D.filling.g = D.gProd) rfl, abs_kappa_eq, ← InfinitePlace.apply, mk_Φ,
    besselEnergy, codimFactor, columnDim, tailScale, packetConst, card_reducedImage_besselS,
    card_classes_filling, D.relIndex_latStabilizer, siegelConst, Filling.unipCovolume,
    openCellConst, bandConst, ↓card_rowIndex, volU, Shape.k, mainEnergy, volÔ_eq,
    abs_discr_eq_rootDiscr_pow, prod_mul_distrib, prod_div_distrib, prod_pow, prod_pow_eq_pow_sum]
  simp only [filling, P.prod_varpi_eq_rootDiscr_pow, eq_tsub_of_add_eq D.r_add] at *
  iterate 3 use fun _ ↦ D.le_of_hasLogBound
  simp (disch := intros; first | positivity | omega) only [← log_le_log_iff, log_div, log_mul,
    log_pow, log_sqrt, log_rpow, log_exp, log_inv, log_prod, log_one, sum_add_distrib, sum_const,
    card_range, nsmul_eq_mul, sum_range_id, ← Nat.choose_two_right, card_univ, logLevelTarget,
    abs_le, ↓sum_Ico_eq_sub, Set.mem_Icc, sum_sub_distrib, ← mul_sum, sum_singleton, ← sum_mul, ←
    Nat.cast_sum _ (·), ↓sum_range_sub (log <| mass D.E ·)] at *
  push_cast (disch := apply D.nat_le_of_hasLogBound) [Nat.cast_choose_two, ← add_assoc,
    m_eq_two_mul_varrho_add_two] at *
  and_intros <;> linarith [log_two_gt_d9]
end Data
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

Part of: Unfolded periods as finite sums with controlled denominators (see
New.Seesaw.SeesawTheorem).

This file: Lattice bases adapted to the flag, their diagonal lines, nearness and glue conditions.
Lattices with equal adapted lines lie in one double coset, by integral Witt. -/

open Fintype Matrix Valued Space WithZero MatMul
variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] {ε s N} {V : Space E ι ε}
  (e : X ⊕ Fin s ≃ ι) (Y : Grading V N X s) (y : Gf E ι)

/-- The numbering of the basis indices used for triangularity: 4i + 1 on the i-th string vector
(0 ≤ i < s) and 2s on the indices of X. -/
def flagOrder i := (e.symm i).elim (fun _ ↦ 2 * s) (4 * ·.1 + 1)

attribute [local simp] blockTriangular_inv_of_blockTriangular ideleLogVal mul_assoc v_inv

/-- For matrices A, B block triangular for the order `flagOrder` e and a string index i = e(a),
the (i,i) entry of AB is the product of the (i,i) entries of A and B. -/
lemma mul_apply_string_of_blockTriangular {e : X ⊕ Fin s ≃ ι} {R} [CommRing R] {A B} (h :
  BlockTriangular (R := R) A (flagOrder
  e)) (h' : BlockTriangular B (flagOrder e)) a : letI i := e (.inr a); (A * B) i i =
    A i i * B i i := sum_eq_single _ ((reindex_equiv e).1.2 (by grind [flagOrder, BlockTriangular]))

/-- The conditions that b is block triangular for `flagOrder`, spans the same Ô-lattice as x, and
has diagonal entry β_i at the i-th string vector. -/
structure Grading.IsAdaptedBasis (x b : GL ι (𝔸f E)) (β : _ → (𝔸f E)ˣ) where
  triangular : b.1.BlockTriangular (flagOrder Y.indexEquiv)
  integral : b⁻¹ * x ∈ intGL ι (Ô E)
  diag_eq i : b (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i)) = β i

/-- For y in G_f: b is an adapted basis (`Grading.IsAdaptedBasis`), with string diagonal β, of the
lattice spanned by the columns of x_f·y, x_f the finite frame of V. -/
abbrev Grading.IsAdaptedAt := Y.IsAdaptedBasis (V.xFin * y)

/-- The lattice of x has an adapted basis whose i-th string entry has the valuations of (a/ā)^n
c_i, exactly off Q ∪ Q̄ and within k on it; c_i = 1 (s odd), else a⁻¹ (2i < s) or ā. -/
def Grading.HasNearLines a (Q : Finset _) (n k : ℕ) x := ∃ b β, Y.IsAdaptedAt x b β ∧ ∀ i w,
  |ideleLogVal (β i) w - ideleLogVal ((a /
  star a) ^ n * ite (Odd s) 1 (ite (2 * i < s) a⁻¹ (star a))) w| ≤ ite (w ∈ Q ∨ star w ∈ Q) ↑k 0

lemma Grading.exists_isAdaptedAt : ∃ b β, Y.IsAdaptedAt y b β :=
  (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul ⟨_, (V.xFin * y).mul_inv⟩ _).imp fun b H ↦
  ⟨(.mkOfMulEqOne _ _ <| by rw [← mul_apply_string_of_blockTriangular H.1 _ ·, b.3] <;> aesop), H.1,
  inv_mem_iff.1 (exists_eq_right.1 (mod_cast isPrimitiveMatrix_iff.1 H.2)), by simp⟩

variable {w} {Y : Grading V N X s} {y : Gf E ι} {b β g g' b' β'} (h : Y.IsAdaptedBasis g b β) (h' :
  Y.IsAdaptedBasis g' b' β')

lemma Grading.IsAdaptedAt.gram_string_entry [Fintype X] (h : Y.IsAdaptedAt y b β) i j (hj : j ≤
  i.rev) : letI k := (b⁻¹ * (V.xFin * y))⁻¹.1
  letI f := Y.indexEquiv ∘ .inr; (kᴴ * k) (f i) (f j) = V.J (f i) (f j) • (star (β i) * β j).1 := by
  erw [← mul_one _ᴴ, gram_mul_of_gram_eq (gram_inv_of_gram_eq (gram_mul_of_gram_eq V.gram_xFin y.2))
    (mul_assoc ..), Y.2, mul_apply, sum_eq_single (Y.indexEquiv (.inr i))] <;>
    simp [↓map_gradedGram_mul_apply, gradedGram, stringReversal, reindex_equiv Y.indexEquiv]
    <;> grind [IsAdaptedBasis, flagOrder, BlockTriangular, star_zero, Algebra.smul_def]

lemma Grading.IsAdaptedBasis.inv (h : Y.IsAdaptedBasis g b β) : Y.IsAdaptedBasis b⁻¹ b⁻¹ β⁻¹ :=
  ⟨by simp [h.1], by simp, (Units.eq_inv_of_mul_eq_one_right <| by simp [← h.3 ·,
  ← mul_apply_string_of_blockTriangular, h.1])⟩

include h h'

lemma Grading.IsAdaptedBasis.ideleLogVal_le (e : IsIntMatrix v.integer
  ((g⁻¹ * g').map (evalAt w)).1) i : ideleLogVal (β' i) w ≤ ideleLogVal (β i) w := by
  simpa [mul_apply_string_of_blockTriangular h.inv.1 h'.1, h.inv.3, h'.3, field,
    zero_lt_iff, -coe_units_inv] using (v.valuationSubring.1.comap (evalAt w)).matrix.mul_mem
    (mul_mem (mem_intGL_Ô.1 h.2 w).isIntMatrix e) (mem_intGL_Ô.1 h'.2 w).isIntMatrix_inv
    (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i))

lemma Grading.IsAdaptedBasis.ideleLogVal_eq (e : g.map (evalAt w) = g'.map (evalAt w)) i :
  ideleLogVal (β' i) w = ideleLogVal (β i) w := by
  apply_rules [le_antisymm, ideleLogVal_le] <;> simp [e, IsIntMatrix.one]

omit h h'

/-- For E stably unramified (`StablyUnram`): if x, x′ have adapted bases whose string diagonal
entries β_i, β′_i have equal valuations at all finite places whenever 2i < s, then x′kx⁻¹
lies in `Grading.besselFin` for some k in K_0. -/
lemma Grading.IsAdaptedAt.exists_mem_besselFin {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X]
  {ε s N} {V : Space E ι ε} [StablyUnram E] {Y : Grading V N X s} {x x' b b' β β'} (h :
  Y.IsAdaptedAt x b β) (h' : Y.IsAdaptedAt x' b' β') (l : ∀ i w, i ≤ i.rev → ideleLogVal (β' i) w =
  ideleLogVal (β i) w) : ∃ k ∈ Kf E ι, x' * k * x⁻¹ ∈ Y.besselFin := by
  let γ a := ite (a ≤ a.rev) β β' a
  have ⟨b', h'⟩ : ∃ b', Y.IsAdaptedAt x' b' γ :=
    ⟨b' * diagGL ((1 ⊕ᵥ β'⁻¹ * γ) ∘ Y.indexEquiv.symm), by constructor <;> simp_all [h'.1 _,
    BlockTriangular, ← map_inv, diagonal_apply, h'.3, mul_assoc, mul_mem, h'.2, γ, mem_intGL,
    reindex_equiv Y.indexEquiv, mem_Ô, ← log_le_log, v_inv, ideleLogVal, apply_ite, ite_apply]⟩
  let f (a : {a // a ≤ a.rev}) := Y.indexEquiv (.inr a.1)
  let P {g} (h : g ∈ intGL ι (Ô E)) : IsPrimitiveMatrix (Ô E) (submatrix (Units.inv g) id f) :=
    (mem_intGL.1 h).symm.imp (by tauto) fun H ↦ ⟨g.1.submatrix f id, fun i ↦ H (f i),
      (g.3 ▸ submatrix_one f (by aesop_cat) : (g.1 * g.inv).submatrix f f = 1)⟩
  peel witt_Ô (P h.2) (P h'.2) (by ext; erw [h.gram_string_entry,
    h'.gram_string_entry] <;> grind) with g n e
  refine Y.mem_besselGroup_iff_sub_one.2 (Y.indexEquiv.surjective.forall₂.2 fun _ _ _ _ ↦ ?_)
  have q {i} c : (V.ratCoordMatrixFin (x' * g * x⁻¹) * b) i (f c) = b' i (f c) := by
    simpa [submatrix_mul (e₂ := id), ratCoordMatrixFin] using! congr(((V.xFin * x').1 * $e) i _)
  erw [sub_eq_zero, ratCoordMatrix_inr, ← b.mul_inv_cancel_right (V.ratCoordMatrixFin _), mul_apply,
    Finset.sum_congr rfl ((reindex_equiv Y.indexEquiv).1.2 _), ← mul_apply, b.mul_inv]
  apply apply_ite₂
  grind (splits := 20) [q ⟨_, _⟩, h.inv, gradeOf_inl, flagOrder, gradeOf_inr, BlockTriangular,
    IsAdaptedBasis]
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Support of unfolded periods: lattice lines move at most one step per lift. -/

open Matrix Gf WithZero Space Kronecker Valued Fintype WeilData MatMul Algebra
variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] [Fintype X]
  {s s' N ε ε'} {V : Space E ι ε} {V' : Space E ι' ε'} {Y : Grading V N X s}
attribute [local simp] gradedGram ite_apply division_def v_inv smul_smul atPlace

/-- Let E be stably unramified, b an adapted basis at x with string diagonal β, and N = ππ̄
split along P. For odd s assume that for no n in `Grading.besselFin` and w in P is (nx)⁻¹K_w(X)nx ⊂
K_w(V). Then ord_w β_i + ord_{w̄} β_{s−1−i} ≥ 0 for all i, w. -/
lemma Grading.IsAdaptedAt.ideleLogVal_add_rev_nonpos {x b β P π} [StablyUnram E] (h :
  Y.IsAdaptedAt x b β) (q : IsSplitSquarefree P N π) (hg : Odd s → ∀ᵉ (n ∈ Y.besselFin) (w : P),
  ¬∀ a ∈ maxCompactAt X w, (n * x)⁻¹ * (Y.inclXFin a * (n * x)) ∈ maxCompactAt ι w)
  i w : ideleLogVal (β i) w + ideleLogVal (β i.rev) (star w) ≤ 0 := by
  have G {x b β} (h : Y.IsAdaptedAt x b β) i := by simpa [apply_ite, -ite_mul, Y.2, q.1, smul_def,
             ← log_le_log, ← ideleLogVal.eq_1] using mem_Ô.1 (h.gram_string_entry i _ le_rfl ▸
    h.2.isIntMatrix_inv.isInt_conjTranspose.mul h.2.isIntMatrix_inv _ _ :)
  have K w : ideleLogVal π w = ite (w ∈ P) (-1) 0 := by simp [ideleLogVal, q.2, apply_ite]
  wlog p : star w ≠ w ∧ Odd s ∧ i.rev = i ∧ w ∈ P generalizing w; grind [star_star, q.2 w]
  have L a w : ideleLogVal (star β⁻¹ a) w = -ideleLogVal (β a) (star w) := by simp [ideleLogVal]
  let γ a := ite (a ≤ i) (β a) (star β⁻¹ a.rev)
  let d := diagGL ((1 ⊕ᵥ γ) ∘ Y.indexEquiv.symm)
  have D : Y.IsAdaptedBasis d d γ := by constructor <;> simp [d]
  have ⟨y, o, e⟩ : ∃ y ∈ supportedOn ι {w}, d.map (evalAt w) = (V.xFin * ↑(y * x)).map (evalAt w) :=
    ⟨atSplit p.1 (.map (evalAt w) (V.xFin⁻¹ * d / x)), by simp +contextual [atSplit,
    evalAt_star_locGL, p]⟩
  have ⟨_, _, h'⟩ := Y.exists_isAdaptedAt (y * x); contrapose! hg
  obtain := D.ideleLogVal_eq h' e, (h.ideleLogVal_eq
    h' <| by simpa using mem_supportedOn.1 o · · ·), h'.ideleLogVal_le D (w := star w) (by
    simp_rw [GeneralLinearGroup.val_map_apply, Units.val_mul, coe_units_inv, inv_eq_left_inv
      (gram_mul_of_gram_eq gram_xFin (y * x).2), Matrix.map_mul,
      @id (_ᴴ.map _ = _) (evalAt_star_GL rfl _), ← e]
    simp [d, reindex_equiv Y.indexEquiv, Y.2, apply_ite, -evalAt_apply, q.1, IsIntMatrix,
      v.mem_integer_iff]
    simp [← log_le_log, ← ideleLogVal.eq_1]; grind [star_star])
  refine (h.exists_mem_besselFin h' (by grind [star_star, q.2 w])).elim fun _ ⟨k, r⟩ ↦ ⟨p.2.1, _, r,
    ⟨w, p.2.2.2⟩, fun A ⟨⟨B, a⟩, l⟩ ↦ (and_congr_left mem_Kf_iff_of_supportedOn).2 ⟨?_,
    mem_supportedOn.2 fun u b c ↦ by simpa [mul_eq_one_iff_eq_inv] using
    (Units.ext (congr($(Y.ratCoordMatrixFin_inclXFin A).map _).trans (by simp_all [-evalAt_apply,
    Units.ext_iff, ← submatrix_map])) : (V.xFin * _ * _).map _ = 1)⟩⟩
  simpa [e, mul_assoc] using mem_intGL_Ô.1 (mul_mem (inv_mem k) (mul_mem (a := MulAut.conj (d⁻¹ *
    V.xFin) _) ⟨reindexGL Y.indexEquiv (blockGL (B, 1)), by simp [Units.ext_iff, ← ext_iff, d,
    reindex_equiv Y.indexEquiv, diagGL, ← ratCoordMatrixFin.eq_1, -Matrix.mul_assoc, -coe_units_inv,
    ratCoordMatrixFin_inclXFin, ← @id (_ = A.1) a, apply_ite]⟩ k)) w

attribute [-simp] coe_units_inv in
/-- One step of `Grading.HasNearLines`: from Y, x, m, k to Y', x', m', k + 1, where s' + 1 = s and m
= m' (s odd) or m' + 1 (s even). Assume (c) = (aā), b | conj(α/a)∏_Q w, ϱ_f(b·Ô-vectors) fixes
f, `Grading.constTermAtT` of t ⊗ f is non-zero at (x, x'), and adapted bases at x' have ord_w β_i +
ord_{w̄} β_{s'−1−i} ≥ 0. Here c is the constant of the grading Y and α = `WeilData.α`. -/
lemma Grading.HasNearLines.step {Y' : Grading V' N X' s'} [WeilData E] {μ f a m m' Q k x x' t} (hx :
  Y.HasNearLines a Q m k x.2) (hm : m = m' + ite (Odd s) 0 1) (hs : s' + 1 = s) (ha : ∀ w, v ((Y.c :
  𝔸f E) w) = v ((a * star a.1) w)) (n : Y.constTermAtT Y' μ (integrated _ t f) x x' ≠ 0) b (hb :
  ∀ w, ideleLogVal (star (α / a)) w ≤ ideleLogVal b w + ite (w ∈ Q) 1 0) (hf : ∀ y ∈ stdLattice E _,
  finHeisOp _ (b.1 • y) f = f) (hg : ∀ {b β}, Y'.IsAdaptedAt x'.2 b β → ∀ i w, ideleLogVal (β i) w +
  ideleLogVal (β i.rev) (star w) ≤ 0) : Y'.HasNearLines a Q m' (k + 1) x'.2 := by
  obtain ⟨⟨B, γ, p, _⟩, rfl, rfl⟩ := hx, hs, hm
  peel Y'.exists_isAdaptedAt x'.2 with B' γ' q
  have H i : ite (Odd s' ↔ i ≤ Fin.rev i) Y.c.1 1 • (star (b / γ i.rev.succ) / α /
    γ' i).1 ∈ Ô E := ?_
  simp [apply_ite ideleLogVal, ↓ite_smul, ite_mem, mem_Ô, smul_def] at *; unfold ideleLogVal at *
  simp [ha, ← log_le_log, ← ideleLogVal.eq_1, abs_le] at *
  grind [star_star]
  choose _ _ _ D _ P L using Y.exists_splitting_constTerm Y'.gradeOf_stringReversal
  let g := (G.onHom (x, x')).2
  obtain ⟨l, hl, e⟩ := zeroTermFin_support D (b.1 • g) (star b⁻¹.1 • g) (n <| by
    simp [L, pairWeil, omega_integrated]; rw [((zeroTermFin_spec D).2 ..).choose_spec, ·]
    simp) (by simp [← U.inv_val_eq_conjTranspose]) (by simpa using congrArg (ω _ g) <| hf · ·)
  rw [show _ᴴ = (D.kᴴ * (V.hom V').J).map (algebraMap _ (𝔸f E)) * (V.hom V').xFin.1 by
    simp [← gram_inv_of_gram_eq gram_xFin, Splitting.kAdelic, ← RingHom.coe_snd]
    congr with; simp, ← mulVec_mulVec, (rfl : (xFin _).1 = V'.xFin ⊗ₖ V.xFin⁻¹.1ᵀ),
    finCoord_homAtPoint, G.onHom_snd, smul_mulVec, mulVec_sub, mulVec_smul] at e
  have h i j (h : Y'.gradeOf i < Y.gradeOf j) := by
    simpa [← Matrix.map_mul, ↓P, matToVec, ↓vecToMat_matToVec, coe_units_inv, ← mul_assoc,
      ← star_mul, mul_sub, h, ↓kronecker_mulVec_eq_matToVec] using congr(star b *
      (((V.hom V').J⁻¹ * D.k).map (↑) *ᵥ $e) (i, j))
  generalize o : V'.xFin.1 * (_ : Matrix ι' ι (𝔸f E)) = W at h
  convert (by simpa [← o, coe_units_inv, ← U.inv_val_eq_conjTranspose, inv_eq_left_inv gram_xFin,
    ← Matrix.map_mul, ← (V.J.map _).mul_assoc] using (q.2.isIntMatrix.mul (N :=
    vecToMat l) (hl ⟨·, ·⟩)).mul p.2.isIntMatrix.isInt_conjTranspose : IsIntMatrix _ (B'⁻¹.1 * W *
    (V.J⁻¹.map (↑) * B⁻¹.1ᴴ))) (Y'.indexEquiv (.inr i)) (Y.indexEquiv (.inr i.rev.succ))
  clear * - h p q; simp [stringMap, reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv] at h
  simp only [Y.J_inv_eq_gradedGram, ↓map_gradedGram_mul_apply, mul_apply, Finset.sum_mul]
  rw [← sum_prod_type', sum_eq_single (Y.indexEquiv (.inr i.castSucc), Y'.indexEquiv (.inr i)) (by
    simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, stringReversal]
    grind (splits := 20) [p.inv, q.inv, IsAdaptedBasis, BlockTriangular, flagOrder, star_zero])]
  simp [stringReversal, algebraMap_eq_smul_one, ← h.2]
  grind [Y.N_spec, p.inv.3, q.inv.3, Pi.inv_apply]
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Under `Grading.SpansLattice`, the inclusion U(X) → U(V) maps a congruence
subgroup mod π into `Kf`; base case of the support bound. -/


open Filling Matrix Space
variable {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X] {ε s N} {V : Space E ι ε}
  (Y : Grading V N (X ⊕ _) s) {a π}
attribute [local simp] mul_assoc flagOrder BlockTriangular gradedLatticeBasis diagonal coe_divStar
  division_def

lemma Grading.hasNearLines_zero {x Q K n} (hL : Y.SpansLattice a π (divStar a ^ n)) (l : K ≤ Kf ..)
    (H : ∃ r ∈ Y.besselFin, r * x ∈ K) : Y.HasNearLines a Q n 0 x := by
  obtain ⟨⟨k, h, e⟩, r, hr, hk⟩ := hL, inv_surjective.exists.1 H
  refine ⟨_ * r * _ * (V.xFin * k⁻¹), _, ⟨.mul (M := V.ratCoordMatrixFin r) ?t ?g, by
    simpa using mul_mem h (l hk), (mul_apply_string_of_blockTriangular ?t ?g · |>.trans ?_)⟩,
    fun _ _ ↦ by rw [sub_self]; simp⟩ <;> simp [besselFin,
    mem_besselGroup_iff, ratCoordMatrix_inr, apply_ite, ↓reindex_equiv
    Y.indexEquiv] at hr <;> simp [reindex_equiv Y.indexEquiv, apply_ite Units.val, *] <;> grind

lemma Grading.inclXFin_mem_Kf {P u h} (hL : Y.SpansLattice a π u) (p : IsSplitSquarefree P N π)
    (H : h.1 ∈ congruenceGL (Ô E ∙ ↑π) .inr) : Y.inclXFin h ∈ Kf .. := hL.elim fun _ a ↦ by
  have r : IsIntMatrix _ (of _) := (a.1.isIntMatrix <| Y.indexEquiv <| .inl ·)
  by_cases Odd s <;> [have := isIntMatrix_scaleAt_sub_one π (Sum.inr ()) (by grind
    [IsSplitSquarefree]) H; have := H.1.isIntMatrix.sub .one] <;> simpa [show (Y.inclXFin h).1.1 =
    V.xFin⁻¹ * (V.ratCoordMatrixFin (Y.inclXFin h) - 1) * V.xFin + 1 by simp [ratCoordMatrixFin,
    sub_mul, mul_sub], mul_apply, ratCoordMatrixFin_inclXFin, Y.2, gradedGram, ↓inv_eq_left_inv
    gram_xFin, (reindex_equiv Y.indexEquiv).2, IsIntMatrix, apply_ite star, Matrix.mul_assoc,
    mem_Kf, *] using (r.isInt_conjTranspose.mul (this.mul r)).add .one
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Function left after k unfoldings: coefficient of the definite chain; its support. -/

namespace Data

open MeasureTheory Function UniqueFactorizationMonoid Multiset IsDedekindDomain.HeightOneSpectrum
  Space Grading stdLattice Prod Modulus
variable {P} {D : Data P} (ϑ : D.TameChar) (φ : D.Column) (ξ : ∀ k, GInf D.E (D.signsY k))
  (y : ∀ k, Gf D.E (D.Y k))

/-- The function P_k on U(Y_k)(𝔸): P₀ = 𝖶_φ is the Poincaré series of φ over the rational points
of the Bessel subgroup, and P_{k+1} comes from P_k by the unfolding step
`Grading.unfoldStep` at the point (ξ_k, y_k). -/
noncomputable def unfoldStage : ∀ k ≤ 2 * D.ϱ + 2, ∀ {X s} [Fintype X], Grading (D.spaceY k) D.N X s
  → _root_.G D.E (D.signsY k) → ℂ | 0, _ => (D.filling_fits.poincare
  (D.columnCoords φ) ·.ratBessel) | k + 1, l => ((D.gradingY k).unfoldStep · (rankTwist
  (D.chainChar ϑ (k + 1))) (datumY ϑ k) (unfoldStage k (by lia) (D.gradingY k)) (ξ k, y k))

lemma unfoldStage_update {l} s t k hk (h : k ≤ l) : @unfoldStage _ D ϑ φ (update ξ l s) (update y l
  t) k hk = @unfoldStage _ D ϑ φ ξ y k hk := by induction k <;> simp (disch := lia) [unfoldStage, *]

lemma isGeneric_unfoldStage : ∀ k l,
  (D.gradingY k l).IsGeneric (unfoldStage ϑ φ ξ y k l.step (D.gradingY k))
  | 0, _ => D.filling_fits.isGeneric_poincare _ (by simp [gradingY, filling, gProd, field])
  | _ + 1, _ => isGeneric_unfoldStep (isGeneric_unfoldStage ..) rfl

/-- Let i ≤ ϱ, R a pair of steps with evaluation `Data.pairEvalY` i, and ξ, x real points. Some
linear form t gives, for all ϑ, columns φ, y with y₀ in K(g) and g in U(X): `Data.unfoldStage`
2i + 2 at g·(x, y_{2i+2}) is the matrix coefficient at t, at the point R.embX g, of i + 1 paired
lifts of φ with data `Data.evaluatedDatum`. -/
lemma unfoldStage_even i (h : 2 * i < 2 * D.ϱ + 1) {X q s} [Fintype X] [Fintype q]
    {Y : Grading _ _ X s} (R : ArrowPair _ q (D.gradingY _ h.le) (D.gradingY _ h) Y) (e :
  D.pairEvalY i = R.finEval) x : ∃ t, ∀ ϑ φ y, y 0 ∈ D.chosenLevel → ∀ g,
  unfoldStage ϑ φ ξ y (2 * i + 2) (by lia) Y (Y.inclX g * (x, y
  _)) = algFormCoeff 1 t (chain₂ (D.liftKernel ϑ) (evaluatedDatum ϑ y) (i + 1) φ) (R.embX g) := by
  induction' i using Nat.strongRec with i H generalizing X q s
  obtain ⟨t, a⟩ : ∃ t, ∀ ϑ φ y b g, _ = _
  swap
  choose u _ using (zeroTermFin_spec R.splitting).2
  choose _ _ using R.integral_constTermAtT_mul
  have L {i} : IsThetaLift _ _ _ _ (D.liftKernel · i |>.lift) := isThetaLift_thetaKernel (by simp)
  refine .imp (fun _ H o φ y b g ↦
    .trans ?_ (H o ..)) (integral_theta_eq_lift₂ (@L (2 * i)) L ((?z : ℂ) • ?v) t)
  simp_rw [evaluatedDatum, e, R.arrowTensor_finEval]
  simp +instances [unfoldStage, Grading.unfoldStep, *, isGeneric_unfoldStage, constTermAtT,
    ← integral_mul_const, ← mk_mul_mk, arrowProduct,
    pairWeil_integrated_all (ξ _), Std.map_integrated, boxProd_integrated]
  refine .trans congr(∫ g, $(a o φ y b g) * _ ∂_) (by rfl)
  cases i; exacts [⟨(dotProductBilin ℂ ℂ).flip _ ∘ₗ D.filling_fits.weylBesselEquiv.1.1,
    fun ϑ φ y a g ↦ by simpa [simpleRootSum_eq_zero_of_mem_besselH] using!
    (D.filling_fits.poincare_bessel_normal_form (D.centralRep (D.latticeScale 0) φ) (one_mem _) g
    (x := (_, _)) a).trans congr(_ * D.filling_fits.weylBesselEquiv.1 (conjWeylRep _ _ _
    (φ.1.1 $(inv_mul_cancel_right ..))) ⬝ᵥ _)⟩, H _ .refl _ _ (dite_eq_left (by omega)) _]

lemma evaluatedDatum_out : evaluatedDatum ϑ (fun k ↦ (y k : _ ⧸ levelY ϑ k).out) =
  evaluatedDatum ϑ y := by
  choose u e using (QuotientGroup.mk_out_eq_mul (levelY ϑ _) <| y ·)
  simp [funext_iff, evaluatedDatum, translatedUpsilon, e, ← mk_mul_mk]
  congr! <;> simp [thetaKernelY_omega_upsilonY ϑ _ (mem_levelOf.1 (u _).2).2
    (mem_levelOf.1 (u _).2).2 fun _ ↦ (@Matrix.mul_one _ _ _ _ _ (_) _).symm]

/-- Let φ be a ramified column and y₀ of principal level above g. If the stage-k function is
non-zero at a point of U(Y_k), the lines of its lattice move at most k steps above Q and not
elsewhere (`Grading.HasNearLines`). -/
lemma hasNearLines_of_unfoldStage_ne_zero (φ : D.ramifiedColumns) (y₀ :
  y 0 ∈ chosenLevel) k hk g (e : unfoldStage ϑ φ ξ y k hk.step (gradingY k hk) g ≠ 0) :
  (D.gradingY k).HasNearLines D.ideleA ϑ.Q ((D.m - k + 1) / 2) k g.2 := by
  induction' k with k ih
  · exact hasNearLines_zero _ (D.spansLattice_gradingY ..) levelOf_le_Kf
      (D.filling_fits.exists_besselFin_mul_mem_of_ne_zero _ e)
  let 𝔪 := D.𝔪 ϑ 1
  refine (exists_ne_zero_of_integral_ne_zero e).rec fun r l ↦ (ih _ _ (left_ne_zero_of_mul l)).step
    (by clear * - hk; grind) (by omega) D.valuation_shift_const_eq_ideleA_norm
    (right_ne_zero_of_mul l) 𝔪.generator (fun w ↦ ?_)
    (fun x o ↦ ?_) (·.ideleLogVal_add_rev_nonpos D.piIdele_spec fun o n m w H ↦ e ?_)
  · erw [ideleLogVal, ideleLogVal, 𝔪.valued_generator,
      multiplicity_mul w.prime (.of_prime_left w.prime 𝔪.2), ← span_piGBar,
      ← count_normalizedFactors_eq_multiplicity (right_ne_zero_of_mul 𝔪.2), ϑ.Q.prod_coe_sort,
      Finset.prod, normalizedFactors_prod_of_prime] <;> simp [ideleA, chosenIdele, valued_generator,
      prime, count_map_eq_count', asIdeal_injective, count_eq_of_nodup ϑ.Q.2]
  · obtain ⟨z, a, d⟩ : IsAdmissibleComb _ _ 1 _ _ 0 (upsilonY ϑ k).1 :=
      isAdmissibleComb_name _ _ (g := 0) (by simp) (by simp
      [ite_mem]) id (projOn_vacElem _) ⟨⟨_, 𝔪.generator_spec.1⟩, by simp [𝔪, generator_spec]⟩
    rw [d, map_finsuppSum, Finsupp.sum_congr fun t e ↦ ?_]
    simp [finHeisOp_comm, finHeisOp_vacElem
      (smul_mem_stdLattice 𝔪.generator_spec.1 o), by simpa using (mem_stdLattice_iff_psi₀.1
      o (star 𝔪.generator.1 • t) fun i ↦ mem_Ô.2 (a.1 t e i · (mod_cast Ideal.one_notMem _)))]
  obtain ⟨⟨j, rfl⟩ : Odd k, ⟨u, hu, a, d⟩, ψ, f⟩ := ⟨k / 2, o.elim (by omega)⟩,
    exists_unipotent_mul_inclX _ (inv_mem (x := (1, n)) m), D.exists_eq_sub_centralGen w φ.2
  choose t ht using unfoldStage_even (update ξ _ g.1) j _ _ (dite_eq_left (by omega)) g.1
  replace ht := by simpa only [unfoldStage_update, update_self, le_rfl,
    ← evaluatedDatum_out _ (update _ _ _),
    (apply_update fun _ ↦ QuotientGroup.mk)] using fun ψ x ↦ ht ϑ ψ (update y (2 * j + 2) x) y₀
  have := by simpa [twoKernelAction, liftKernel_ω, pairWeilFinite_scalarFin,
    (D.charUnramifiedAt_rankTwist_of_N_mem _ _ _ _ (D.isSplitLevel_piPlaces.natCast_mem _
    w.2)).det_maxCompactAt_eq_one (D.isSplitLevel_piPlaces.star_notMem
    _ w.2 <| ·.symm ▸ w.2) (D.scalarFin_centralGen_mem ..)] using
    chain₂_equivariant (liftKernel ϑ) fun _ ↦ scalarFin _ (D.centralGen w)
  rw [← inv_mul_cancel_left _ g, d, mul_assoc,
    (isGeneric_unfoldStage ..).unipotent_mul _ u hu (hasDegreeGe_two_of_odd _ o hu)]
  simpa [middlePair, algFormCoeff_apply, inclX_inr, mul_assoc, mul_def _ g, *, ← QuotientGroup.eq.2
    (maxCompactAt_le_levelOf (by simp [levelPlaces, range_chosen]; clear * - w; grind
    [not_isChosen_of_N_mem, D.isSplitLevel_piPlaces.natCast_mem_iff, →
    levelNorm_mem_and_notMem_of_mem_Q]) (H _ (D.scalarFin_centralGen_mem ..)) : _ ∈ levelY ϑ _)]
    using! (ht ψ (n * g.2) (a * (1, scalarFin _ (D.centralGen w))) :)
end Data
end

section
/-! Translates of the columns fill the rows. For every subspace F of the rows, some level translate of the projected Poincaré series keeps, modulo F, ramified columns of dimension at least nearly ½(1 − dim F/dim rows) times that of all columns, so rows exist and few translates span almost all rows, which gives the basis for the Gram determinant. Spanning by Poincaré series and the link between least second moment and tight frames are known. Related work: Petersson, Über die Entwicklungskoeffizienten der automorphen Formen, 1932; Benedetto–Fickus, Finite normalized tight frames, 2003; Muić, Compactly supported Poincaré series and existence of cusp forms, 2010. -/

open Filling Module Submodule

variable {P} (D : Data P) (c : ℂˣ)

/-- The Poincaré series 𝒫 as a linear map from columns on X₀ to forms of parameter ς and level g
on Y₀, chosen to realise `Filling.Fits.poincare`. -/
noncomputable def Data.poincare : D.Column →ₗ[ℂ] D.principalForms (D.spaceY 0) :=
  D.filling_fits.poincareMap.1 ∘ₗ D.columnCoords

/-- Filling theorem: for c ≠ 0 and each space F of rows, with φ = dim F / dim(rows), some s in the
finite level group 𝖦 = `Data.G` (e₀ = `Data.e₀` projects to rows) has dim
(|𝖦|e₀s𝒫cE)⁻¹F ≤ ((1 + φ)/2 + b⁻²) dim Col. Here 𝒫 is the Poincaré series and E = `Data.ramifyingOp`
univ maps columns onto ramified columns.

Translates of the columns fill the rows. -/
lemma Data.ramifiedColumns_fill_rows :
  IsSpread (D.goodProjTranslate · ∘ₗ D.poincare ∘ₗ (c.1 • D.ramifyingOp .univ)) (D.b ^ 2)⁻¹ := by
  have := D.hasLogLower_of_le (le_sub_iff_add_le.2 D.le_of_hasLogBound : D.b ^ 9 ≤ D.N - 1)
  have h := Fits.exists_translate_finrank_comap_le (ρ :=
    .comp (D.principalRep _) (.mk' _ (by tauto))) (fun _ _ _ ↦ Space.inner_formRep ..) (fun _ ↦
    (D.filling_fits.petersson_poincare · · (@reduceFamily_liftResidue ..))) (fun _ ↦
    isCentralProj_sum_tupleIdem) (fun i ↦ (bad_share_le (M := P.Mω D.s) (q := D.g i) _ (9 * D.logB)
    (card_resField_eq_levelPrime _ i) rfl (card_chosenPlaces _ i) D.nat_lt_of_hasLogBound
    D.nat_lt_of_hasLogBound D.le_of_hasLogBound le_rfl D.le_of_hasLogBound).trans
    (filling.eq_1 D ▸ D.le_of_hasLogBound)) (measureReal_pos_of_isLevel (K := D.chosenLevel))
  erw [(?_ : Representation.asAlgebraHom _ _ = (principalRep ..).asAlgebraHom D.e₀), Shape.r,
    card_rowIndex, ← Nat.card_congr (.piCurry _)] at h
  simp_rw [IsSpread, ← D.columnCoords.finrank_eq, ← (D.columnCoords.ofSubmodule' _).finrank_eq] at h
  refine fun F ↦ (h D.finrank_rows_le_mass F).imp' Sigma.uncurry fun _ h ↦
    .trans (mod_cast finrank_mono fun _ ↦ by simpa using!
    id) (((D.ramifyingOp_finrank_comap_and_short .univ _).1.trans (add_le_add h le_rfl)).trans ?_)
  simp [← add_mul, add_assoc, card_piPlaces, filling]; gcongr; use D.le_of_hasLogBound
  open Fint in simp_rw [asAlgebraHom_eq_sum, reindex_equiv (Equiv.piCurry _)]
  simp [e₀, goodTupleFamilies, tupleIdem, Finset.prod_univ_sum, Fintype.prod_sigma]; rfl

/-- For admissible data D, the space of rows has nonzero finite dimension over ℂ.

Translates of the columns fill the rows. -/
lemma Data.finrank_rows_ne_zero : finrank ℂ D.rows ≠ 0 := fun e ↦ (D.ramifiedColumns_fill_rows 1
  ⊤).rec fun _ ↦ by erw [finrank_top, e]; norm_num [finrank_pos_iff.2 D.columnCoords.nontrivial,
  ← lt_tsub_iff_left]; use D.lt_of_hasLogBound
end
