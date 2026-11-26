import New.Weil.MovedVacuumComb
import New.Weil.EdgePair
import New.Weil.NamesAtSplitLevel
import New.Weil.PairTensorData
import New.Filling.FillingData

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Denominator control under adjoints and conjugation; membership in the glued lattice.
Evaluated vacua are admissible translates of the neighbour-lattice vacuum, the sum τ_N. -/

open AddSubgroup Finset Grading Kronecker stdLattice Matrix RingHom Space Valued Weil WeilData

variable {E n n₀ : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n] {q : ℕ}

section

attribute [local simp] mem_intGL weightedTranslations

/-- For an integral finite adele β, the function on ι ⊕ κ equal to β on ι and to its conjugate
β̄ on κ. -/
noncomputable def selfOrConj {ι κ} (β : Ô E) (j : ι ⊕ κ) := ite j.isLeft β.1 (star β)

lemma mulVec_mem_weightedTranslations {M : Matrix n n₀ _} (h : IsIntMatrix (Ô E) M) {d d' y} (hy :
  y ∈ weightedTranslations q d) (h' : ∀ i j u, v (d i u) ≠ v (d' j u) → M i j (star u) = 0) :
  Mᴴ *ᵥ y ∈ weightedTranslations q d' := mulVec_eq_sum y _ ▸ sum_mem fun i _ j ↦ by
  simp_all [mem_Ô, IsIntMatrix]
  grind +splitImp [mul_left_comm, mul_le_one', mul_eq_zero]

lemma star_mem_weightedTranslations {ι X c} (h : c ∈ Ô E) {d x} (hx : x ∈ weightedTranslations q d)
  (f : X → ι) : (fun i ↦ c * star (x (f i))) ∈ weightedTranslations q (star <| d <|
  f ·) := by simp_all [mul_left_comm, mul_le_one', mem_Ô]

lemma inv_xFin_mulVec_mem_of_spansLattice {E : Type} [Field E] [CMType E]
    [Fintype n₀] {s N a π u c} {V :
  Space E n s} {Y : Grading V N (n₀ ⊕ _) q} (hL : Y.SpansLattice a π u) (x : _ → _) (h₂ :
  c ∈ Ô E) (hs : Odd q) {v} (h : ∀ i, x (.inl i) ∈ Ô E) (h₁ : star ↑π * x (.inr ()) ∈ Ô E) (hv :
  ∀ i, v (Y.indexEquiv i) = i.elim x (if 2 * ·.1 + 1 = q then u *
  (π⁻¹ * x (.inr ()) + c) else 0)) i : (V.xFin⁻¹.1 *ᵥ v) i ∈ Ô E := hL.elim fun k _ ↦ by
  simp [show v = V.xFin.1 *ᵥ k⁻¹ *ᵥ Subtype.val ∘ (((⟨_, h ·⟩) ⊕ᵥ fun _ ↦
    ⟨_, h₁⟩) ⊕ᵥ (if 2 * ·.1 + 1 = q then ⟨_, h₂⟩ else 0)) ∘
    Y.indexEquiv.symm by simp [funext_iff, reindex_equiv Y.indexEquiv, gradedLatticeBasis, *,
    diagonal, -mul_ite, entrywise, apply_ite Subtype.val]; grind [star_mul, star_one, π.inv_mul]]
  exact sum_mem (by aesop)

end


variable {E ι ι' ι'' X X' X'' μ q : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι']
  [Fintype ι''] [Fintype X] [Fintype X'] [Fintype X''] [Fintype μ] [Fintype q] {ε : ι → ℤˣ}
  {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}
  [WeilData E] {N : ℕ} [Fact N.Prime] {m : ℕ} {m' : ℕ} {m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
  {Y' : Grading V' N (X' ⊕ _) m'} {Y'' : Grading V'' N μ m''} {a : (𝔸f E)ˣ} {π : (𝔸f E)ˣ}
  {u : ↥(unitary (𝔸f E))} (κ : (X ⊕ Unit) ⊕ X'' ⊕ Unit → _) (hL' : Y'.SpansLattice a π u)
  {P : Finset (FinPlace E)} {β : Ô E} (δ : 𝔸f E) (hN : ∀ w, ↑N ∈ w.1 → δ w = 1 ∧ v (β.1 w) = 1)
  (hP : IsSplitLevel P N) (hq : IsSplitSquarefree P ↑N π) (h1 : δ * star δ = 1)
  (hG : ∀ b, star β.1 * κ b ∈ Ô E ∧ selfOrConj β b * κ b ∈ Ô E) (hκ : ∀ b, κ b = 1 ∨ κ b = δ)
  (hδ : (star α * α⁻¹).1 * divStar a = δ)

/-- The condition δc = c, π̄x integral, x integral off the two last indices e, e'', and x_e/π ≡
c, x_{e''}/π ≡ ε̄c modulo Ô, with ε = `Weil.normNegOne`. -/
def IsNeighbourVector (π : (𝔸f E)ˣ) (δ : 𝔸f E) c (x : (X ⊕ _) ⊕ q ⊕ _ → _) := δ * c = c ∧
    (∀ i ≠ .inl (.inr ()), i ≠ .inr (.inr ()) → x i ∈ Ô E) ∧ (∀ i, star ↑π * x i ∈ Ô E) ∧ c - π⁻¹ *
    x (.inl (.inr ())) ∈ Ô E ∧ star normNegOne.1.1 * c - π⁻¹.1 * x (.inr (.inr ())) ∈ Ô E

/-- For some C, all n prime to N and all y with d_i y_{ij} integral away from n: L(ϱ_f(y)vac) is an
admissible combination (`IsAdmissibleComb`), of size ≤ 1 and denominator |Ô/β|^{(|X|+|μ|+2)|X'|}, of
the C·`translateSum`(ϱ_f(t)vac ⊗ ϱ_f(t')vac), β̄t and β̄t' integral away from n. -/
def IsAdmissibleEval (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E)) (β : Ô E) (L :
  𝒮 (V'.hom (flipSum V V'')) → _) (d : _ := selfOrConj β) := ∃ C : ℂ, ∀ n q, N.Coprime n →
  ∀ y ∈ weightedTranslations n (d ·.1), IsAdmissibleComb (fun t ↦ C • translateSum X X' P N μ
  (heisFinPart _ t.1 ⟨_, vacElem_mem_finitePart⟩ ⊗ₜ heisFinPart _ t.2 ⟨_, vacElem_mem_finitePart⟩))
  (translations _ n (star β) ×ˢ translations _ n (star β)) n (.card (((X ⊕ Unit) ⊕ μ ⊕ Unit) × X' →
  _ ⧸ Ideal.span {β})) q 1 (L (finHeisOp _ y (vacElem _)))

attribute [local push_cast] Pi.add_apply star_add star_mul' star_natCast star_one star_star
  star_sub in
include hN hP hq h1 hG hκ in
/-- Let N = ππ̄ along P, δδ̄ = 1, δ = 1 and β a unit above N, κ_b ∈ {1, δ} with βκ, β̄κ integral
as in hG. Some unitary k = diag(κ)γ ⊗ 1 has γ = 1, b = 0 off P ∪ P̄, each (b_j, column j of
γ) in `IsNeighbourVector`, and ω(1,k) followed by the left inverse of `arrowTensor`
satisfies `IsAdmissibleEval` for β, κ. -/
lemma exists_isAdmissibleEval_std : ∃ k : Gf E (_ × X'), ∃ γ, ∃ b : _ → _, k.1.1 =
  (diagonal κ * γ) ⊗ₖ 1 ∧ (∀ w, ¬(w ∈ P ∨ star w ∈ P) → ∀ j, evalAt w (b j) = 0 ∧ ∀ i,
  evalAt w (γ i j) = ite (i = j) 1 0) ∧ (∀ j, IsNeighbourVector π δ (b j) (γ · j)) ∧
  IsAdmissibleEval N P β (arrowTensor.leftInverse <| ω _ (1, k) ·) (selfOrConj β * κ) := by
  let k := U.of isUnit_one (diagonal κ) (by simp [funext_iff]; grind [star_one])
  let j : Ô E := ⟨_, idem_mem_Ô P⟩; let S := star ⁻¹' SetLike.coe P; have K :=
    hP.disjoint_star.preimage star
  have b : (j.1 * j, j * δ, π.1 * π⁻¹) = (j.1, j.1, 1) := by
    simp_all [j, DFunLike.ext_iff (F := 𝔸f E), idem_apply, hP.natCast_mem_iff]
  let ϖ := j + ⟨(1 - j) * π⁻¹, by simp +contextual [j, ← idem_compl, idem_mul_mem_Ô, v_inv, hq.2]⟩
  let p : Ô E := ⟨star π, by simp [mem_Ô, hq.2]; intro; split <;> tauto⟩
  let c : Ô E := normNegOne.1; let l := c * j; let d := p * (j * star p - j - star j) + star j
  have a := congr(($b, $(idem_mul_star hP.disjoint_star), $h1, $(hq.1), $(star_normNegOne_mul_self
    (E := E)), star $b))
  push_cast [Prod.star_def] at a
  let T := (X ⊕ Unit) ⊕ X'' ⊕ Unit
  let e : T := .inl (.inr ()); let e' : T := .inr (.inr ())
  let A := star π⁻¹.1 * d
  let θ (i m : T) : Ô E := ⟨ite (i = m) 1 0, by simp [ite_mem]⟩
  let ρ i := θ i e + star l * θ i e'
  let n (y : X' → P → ZMod N) (i : _ × _) := c * ρ i.1 * star (residueOverN (y i.2))
  have O {x} (y : Ô E) (e : x = y.1 := by
    push_cast +zetaDelta [q, of_apply, kv, ↓hv, ← star_idem]
    clear * - a; grind [star_zero, star_one]) : x ∈ Ô E := e ▸ y.2
  obtain ⟨γ, q⟩ : ∃ γ : Gf E T, γ.1.1 = of fun i m ↦ θ i m + A * (θ e m + l * θ e' m) * ρ i :=
    ⟨U.of isUnit_one _ (by
      simp +zetaDelta [entrywise, mul_add, add_mul, apply_ite star]; clear * - a; grind), rfl⟩
  have hv x i : (γ *ᵥ x) i = x i + A * (x e + l * x e') * ρ i := by
    simp [entrywise, q, θ, T, add_mul, mul_add]; ring
  let h : Gf E T →* Gf E (_ × X') := (U.kron (one_mul 1) (by simp)).comp (.inr ..)
  have kv γ x q : ((h γ).1.1 *ᵥ x) q = (γ.1.1 *ᵥ (x ⟨·, q.2⟩)) q.1 := by
    simp [h, entrywise, Fintype.sum_prod_type]
  let Z := (stdSpace E X').hom (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))
  have s {ι : Type} [Fintype ι] (v : ι → _) : semichar (star j.1 * v ·) = 1 := by
    simp [semichar, entrywise, j, mul_mul_mul_comm _ (star _), idem_mul_star hP.disjoint_star]
  refine ⟨h (γ * k), γ, fun m ↦ A * π⁻¹ * (l * θ e' m + star j * θ e m), by
    simp [h]; ext1; simp +zetaDelta [q]; clear * - a hκ; grind, have u w h i := (by
    simp +zetaDelta [*, not_or.1 h, star_idem, apply_ite (· w : 𝔸f E → _)]); ⟨u, fun m ↦ ⟨by
    simp +zetaDelta; grind, by simp +zetaDelta [q, ite_mem], fun i ↦ O (p * θ i m + d * star (ρ m) *
    ρ i), O (-ϖ * θ e m), O (-ϖ * θ e' m)⟩, ?_⟩⟩
  obtain ⟨C, H⟩ : ∃ C : ℂ, ∀ f, Z.ω (h γ) (Z.projOn S f) = C • ∑ y, Z.finHeisOp (star j.1 * n y ·)
      (Z.projOn S f) := ⟨_, fun f ↦ by
    nth_rw 1 [← name_boxIndicator K, ω_name_on K _ (Gf.mem_supportedOn.2 fun w a b ↦ by
      ext; simp [Gf.atPlace, h, u w (not_or.2 ⟨star_star w ▸ b, a⟩), ← ite_and, and_comm,
      Prod.ext_iff, apply_ite (evalAt w)]),
      (?_ : (boxIndicator _ _ <| _ *ᵥ ·) = ∑ y, (boxIndicator _ S <| · + n y))]
    · simp +zetaDelta only [finHeisOp, s, one_smul, map_sum, _root_.sum_apply,
        ← IsSchwartzBruhat.schrodingerAct_idem K,
        name_schrodingerAct_boxIndicator K, smul_smul, show idem S.conjClosure * idem S = idem S by
        ext; simp +contextual [idem_apply]]; rw [← star_idem]; rfl
    ext x; obtain ⟨x, rfl⟩ := mulVec_surjective_iff_isUnit.2 (h γ).1.isUnit x
    choose b B using fun i ↦ hP.exists_sub_residueOverN_mem_iff (l * π⁻¹.1 * star (x (e, i)))
    have z y : h γ *ᵥ x + n y ∈ integralBox _ S ↔ x ∈ integralBox _ S ∧ b = y := by
      simp_rw [mem_integralBox]; exact
        ⟨fun r ↦ have H i := (B i (y i)).1 (O (c * star ⟨_, r (e, i)⟩))
        ⟨fun i ↦ O (⟨_, r i⟩ - ρ i.1 * (⟨_, r (e, i.2)⟩ + c * ϖ * star ⟨_, (H i.2).1⟩)), funext
          (H · |>.2)⟩, fun r i ↦ O (⟨_, r.1 i⟩ - ρ i.1 * (⟨_, r.1 (e, i.2)⟩ + c * star ⟨_, (B i.2
        (y i.2)).2 ⟨O (p * c * star ⟨_, r.1 (e, i.2)⟩), congrFun r.2 _⟩⟩))⟩
    simp [z, ite_and]; rfl⟩
  simp only [← Prod.one_mk_mul_one_mk, map_mul]
  refine ⟨finMultiplier (h k) * C, fun Q _ o x hx ↦ ((isAdmissibleComb_weil_vacElem Z (A :=
    (weightedTranslations Q (selfOrConj β ·.1)).carrier) (one_mul _) (fun y hy i w e ↦ ?_) ?_
    (by simp)).map (arrowTensor.leftInverse ∘ₗ (Z.ω (h γ)).1)).of_eq_isOfFinOrder_smul fun p hp
    ↦ ⟨semichar (fun (a, b) ↦ p (.inl b, a)) ^ 2, (isOfFinOrder_ψf _).pow, ⟨_, _⟩,
    ⟨star_mem_weightedTranslations c.2 hp fun q ↦ (.inl q.2, q.1), fun q ↦ hp (.inr q.1, q.2)⟩, ?_⟩⟩
  · simpa [kv, k, mul_assoc] using
      add_mem hx (fun i w _ ↦ mem_Ô.1 (mul_mem (hG _).2 (hy i)) w) i w e
  · erw [mul_one_div, ← Complex.ofReal_pow, norm_finMultiplier_sq]
    refine div_mem_integralAway (k := 0) (.trans (dvd_index_map _ (f := .mk' ((Ô E ∙ β).mkQ ⟨_,
      star_mem_Ô <| ·.2 ·⟩) (by simp; tauto)) fun x hx i ↦ ?_) ((index_dvd_card _).mul_right _))
    obtain ⟨z, hz⟩ := (Ideal.Quotient.eq_zero_iff_dvd ..).1 congr($hx i)
    simpa [kv, k, mul_left_comm (κ _), mul_assoc, eq_star_of_eq_star
      congr($(hz).1).symm] using! mul_mem (hG _).1 (star_mem_Ô z.2)
  erw [← leftInverse_arrowTensor (_ • _)]
  simp [translateSum, arrowTensor, smul_sum,
    smul_smul, by simpa +contextual [projOn_finHeisOp, mem_integralBox, S, idem_mul_mem_Ô, or_comm,
    ← hP.natCast_mem_iff, (by simpa +contextual [selfOrConj, apply_ite, hN] using
    (fun i w ↦ hp i w ∘ w.2.notMem_of_isCoprime_of_mem o.cast))] using H (Z.finHeisOp p Z.vacElem)]
  simp [← arrowProduct_vacElem, finHeisOp_arrowProduct, s, Z, smul_smul, mul_comm (_ * C)]; congr! 7
  all_goals simp +zetaDelta [apply_ite star]; clear * - a; grind [star_mul', idem_mul_residueOverN]

include hL' hN hP hq h1 hG hκ hδ in
/-- In the setting of `exists_isAdmissibleEval_std`, with Y' of lattice `Grading.SpansLattice` a π u
and δ = (ᾱ/α)(a/ā): if the embedding of X⁻ ⊕ X'' respects the weights (hA) and maps scaled
`IsNeighbourVector` vectors into the lattices of V, V'' (hM), then `ArrowPair.finEval` satisfies
`IsAdmissibleEval` for β and κ = 1. -/
lemma isAdmissibleEval_finEval (D : ArrowPair _ q Y Y' Y'') (hA : ∀ i b, D.zeroPart.incl i
  (.inr b) = 0 ∨ ∀ w, v (selfOrConj β i w) = v ((selfOrConj β b * κ b) w)) (hM : ∀ s t,
  s * (divStar a).1 = star normNegOne.1.1 * δ ∧ t * s = 1 → ∀ x c, IsNeighbourVector π δ c x → ∀ v,
  v = D.zeroPart.incl.map (↑) *ᵥ ((0 ⊕ᵥ fun _ ↦ s * u * c) ⊕ᵥ ((fun _ ↦ s) ⊕ᵥ 1) * κ * x) → ∀ i,
  Sum.elim (V.xFin⁻¹.1 *ᵥ t • v ∘ .inl) (V''.xFin⁻¹.1 *ᵥ v ∘ .inr) i ∈ Ô E) :
  IsAdmissibleEval N P β D.finEval := by
  choose k γ b hk hγ hf C H using
    exists_isAdmissibleEval_std (X' := X' ⊕ Unit) κ δ hN hP hq h1 hG hκ
  let f := algebraMap E (𝔸f E)
  let S := removePlanes q (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))
  let s := (star (flipIdele normNegOne 1)).map (snd _ (𝔸f E)).1; let J :=
    inclMatrix (𝔸f E) (Y'.indexEquiv ∘ .inl)
  have xV : (flipSum V V'').xFin⁻¹.1 = fromBlocks (s⁻¹.1 • V.xFin⁻¹.1) 0 0 V''.xFin⁻¹.1 := by
    simp [s, xFin, sum, flipSpace, ← map_inv, ← smul_eq_mul_diagonal, entrywise]
  let c := of fun (_ : q) l ↦ s.1 * u * b l
  let M := (of fun j ↦ (0 : q → _) ⊕ᵥ (c · j) ⊕ᵥ ((fun _ ↦ s.1) ⊕ᵥ 1) * κ * (γ · j))ᵀ
  have hK : M = S.i.map f * ((flipSum (stdSpace ..) (stdSpace ..)).xFin.1 * (diagonal κ * γ)) +
    S.k.map f * c := by
    simp [entrywise, M, S, removePlanes, s, xFin, sum, flipSpace, ← mul_assoc, diagonal_apply]
  let B := ((flipSum V V'').xFin⁻¹.1 * (D.zeroPart.incl.map f * M)) ⊗ₖ (Jᵀ * V'.xFin.1)ᵀ
  have hB i j : B i j ∈ Ô E := hL'.elim fun k ⟨h, e⟩ ↦ by
    refine mul_mem (?_ : (_ *ᵥ _) _ ∈ _) (by cases j.2 <;> simp [e, gradedLatticeBasis, J,
      entrywise, inclMatrix, reindex_equiv Y'.indexEquiv, show ¬Odd m' by grind [D.string_spec],
      mem_intGL.1 h]); simp [xV, fromBlocks_mulVec, ↓← mulVec_smul, -coe_units_inv]; apply hM _ _
      ⟨by simp [s, val_flipIdele, ← hδ, mul_assoc], s.inv_mul⟩ _ _ (hf _) _ rfl
  choose C₃ ζ hζ R using zeroTermFin_finHeisOp_vacElem D.splitting k (fromRows 0 (c ⊗ₖ 1)) (by
    simp [Splitting.iAdelic, Splitting.kAdelic, Space.ratMap, ArrowPair.splitting, Splitting.comp,
      Splitting.homTarget, hom, GradeZeroPart.splitting, ArrowPair.homZeroPart, GradeZeroPart.hom,
      ← coe_snd, ← coe_comp, *, B, S, J, inclMatrix, xFin, f, toAdele, ← map_inv, add_kronecker,
      ← submatrix_map, Matrix.mul_assoc, Matrix.mul_add, map_kronecker, ↓transpose_mul]) hB
  have τ : Bᴴ *ᵥ stackedTFin Y Y' Y'' = 0 := by
    delta stackedTFin; erw [conjTranspose_kronecker, finCoord_homAtPoint,
      kronecker_mulVec_eq_matToVec _ _ᴴ]
    simp [↓vecToMat_matToVec, Matrix.mul_assoc, show (Jᵀ * V'.xFin.1)ᴴ =
      V'.xFin⁻¹.1 * J by simp [inv_eq_left_inv V'.gram_xFin, J, entrywise, Y'.gram_eq, gradedGram,
      inclMatrix, reindex_equiv Y'.indexEquiv], show (stackedT Y Y' Y'').map (·.2) * J = 0 by
      simp [J, mul_inclMatrix, entrywise, stackedT, Y.formAdjoint_apply Y', stringMap,
        stringReversal, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]]
  refine ⟨C₃ * C, fun n r hS y hy ↦ ?_⟩
  simp [ArrowPair.finEval, finHeisOp_finHeisOp, R, -omega_finHeisOp, τ, mul_smul]
  refine .smul_of_eq_zero_or_isOfFinOrder (.smul_of_eq_zero_or_isOfFinOrder
    ((H n r hS _ (mulVec_mem_weightedTranslations hB hy fun i j u h ↦ ?_)).map (C₃ • .id))
    (hζ _)) (.inr (isOfFinOrder_ψf (E := E) _))
  refine mul_eq_zero_of_left ((map_sum (evalAt _) ..).trans (sum_eq_zero fun l _ ↦ (hA l j.1).elim
    (fun e ↦ mul_eq_zero_of_right _ ((map_sum (evalAt _) ..).trans (sum_eq_zero ?_))) fun e ↦ ?_)) _
  · simp [M, c, e, -evalAt_apply, -mul_eq_zero, hγ (star u) fun a ↦ h (by
      simp [or_comm, ← hP.natCast_mem_iff] at a
      cases hκ j.1 <;> simp [selfOrConj, apply_ite, ite_apply, *])]
  obtain ⟨_ | _, _⟩ := i <;> cases l <;> first | cases h (e u) | simp [xV]
end

section
/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

This file: Constant terms of the chain's finite data are admissible sums with controlled
denominators. An invariant admissible combination yields a good datum computing the definite
chain. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Ideal Matrix Modulus Space TensorProduct TensorChain Weil

namespace Data

attribute [-simp] coe_algebraMap_Ô

attribute [local simp] lastPair middlePair entrywise inclMatrix

variable {P} (D : Data P) (ϑ : D.Twist)

lemma isAdmissibleEval_pairEvalY i (hi : i ≤ D.ϱ) :
  IsAdmissibleEval D.N D.piPlaces (algebraMap _ _ D.piGBar) (pairEvalY i) := by
  have L {k l} j (e : _ =
    j := by grind) := congr(Grading.SpansLattice _ _ _ (_ ^ $e)).mp (D.spansLattice_gradingY k l)
  let δ := star D.chosenIdele⁻¹.1 * D.chosenIdele
  unfold pairEvalY; split_ifs <;> (try lia) <;> apply isAdmissibleEval_finEval (1 ⊕ᵥ (1 ⊕ᵥ fun _ ↦
    ite (i < D.ϱ) 1 δ)) (L (D.ϱ - i).succ) δ (by simp +contextual [δ, chosenIdele, generator_spec,
    places, v_inv, not_isChosen_of_N_mem, ← v_chosenIdele, ← IsChosen.eq_1]) <;> (first
    | rintro s t e x c ⟨o, h, k, a, b⟩ _ rfl (j | j) | simp +contextual [D.isSplitLevel_piPlaces,
      selfOrConj, mem_Ô, piIdele_spec, mem_Ô.1 (generator_spec _).1, chosenIdele, ← v_chosenIdele,
      δ, ↓coe_divStar, ideleA, *, v_inv, division_def] <;> grind [Units.mul_inv, star_one,
      star_mul']) <;> subst_vars <;> [apply inv_xFin_mulVec_mem_of_spansLattice (L (D.ϱ -
    i).succ) (x ∘ .inl) a; apply inv_xFin_mulVec_mem_of_spansLattice (L (D.ϱ - i)) (x ∘ .inr)
    b; apply inv_xFin_mulVec_mem_of_spansLattice (L 1) (x ∘
    .inl) (add_mem a (mul_mem Weil.normNegOne.1.2 b)); revert j] <;> (try simp [univ_eq_empty, xFin,
    reindex_equiv (D.lastGrading D.m_eq_two_mul_varrho_add_two).indexEquiv,
    (D.m_eq_two_mul_varrho_add_two ▸ D.isStd_spaceY).point_eq_one]) <;> grind
    [star_normNegOne_mul_self, show D.piIdele⁻¹.1 = (_⁻¹ : D.E) by rfl]

/-- There is a constant C such that, for every tame ϑ (q = ∏_Q Nw) and y integral away from q,
⊗_{i≤ϱ} `Data.evaluatedDatum` ϑ y i is an admissible combination of the C·`Data.reducedVacuum` t, t
in `Data.admissibleTranslations` q, of denominator `Data.cutBound`^{2m} and, if Q = ∅, size 1. -/
lemma exists_isAdmissibleComb_reducedVacuum : ∃ C : ℂ, ∀ ϑ y,
  (∀ k, y k ∈ localLevel _ {w | ϑ.levelNorm ∉ w.1}) →
  IsAdmissibleComb (C • D.reducedVacuum ·) (admissibleTranslations ϑ.levelNorm) ϑ.levelNorm
  (D.cutBound ^ (2 * D.m)) (ϑ.Q = ∅) 1 (TensorChain.pure (evaluatedDatum ϑ y) _) := by
  choose! C hC using D.isAdmissibleEval_pairEvalY
  use (range D.ϱ.succ).prod ?Grading.c, fun ϑ y hy ↦ ?_; swap
  have a {k} : IsAdmissibleComb _ (translations _ ϑ.levelNorm (star (D.piGBar : 𝔸f D.E))).carrier
    ϑ.levelNorm _ (ϑ.Q = ∅) 1 (translatedUpsilon ϑ y k).1 :=
    .smul (.bind (.map (isAdmissibleComb_name (g := D.piGBar) (B := 1) _ _ (by
    erw [Nat.cast_prod, ← prod_coe_sort]
    exact mul_mem_mul (span_piGBar D ▸ by simp) (prod_mem_prod fun _ _ ↦ absNorm_mem _)) (by
    simp [ite_mem]) (by erw [Pi.single_comp_equiv (.curry ..)]; simp [apply_ite])
    (projOn_vacElem _)) _) 1 1 (fun x hx ↦ by
    erw [G.onHom_fin]; generalize e : Prod.snd _ = g
    have I : g ∈ localLevel _ {w | ↑ϑ.levelNorm ∉ w.1} := by simp_all [localLevel, ← e]
    exact isAdmissibleComb_weil_vacElem _ (mul_one _) (fun y hy ↦
      mulVec_eq_sum _ g.1.1 ▸ (weightedTranslations ..).sum_mem fun j _ i w h
      ↦ by erw [mul_left_comm, map_mul]; exact mul_le_one' ((I w h).isIntMatrix ..) (add_mem
      hx (fun j w _ ↦ mem_Ô.1 (mul_mem (star_mem_Ô (coe_mem_Ô _)) (hy j)) w) j w h))
      (fun _ _ hl ↦ by simp [← Complex.mul_conj', ← finMultiplier_inv,
      Parameters.norm_finMultiplier_eq_one, localLevel_le_integralAbove_of_coprime hl I]) (by
      simp +contextual [finMultiplier_eq_one_of_mem, mem_Kf_iff, I _, one_notMem])) (mul_one _).dvd)
    (fun l _ hl ↦ by simp [D.hasWeight_liftChar.hasWeight_rankTwist.norm_padic_det,
    localLevel_le_integralAbove_of_coprime hl (hy _)]) ?_
  refine .bind (.pure (D.cutBound ^ 4) 1 _ fun i hi ↦ (((a.map_bilinear arrowProduct.toLinearMap₁₂
    a).of_eq_isOfFinOrder_smul fun y hy ↦ ?_).map (D.pairEvalY i)).bind _ _ (hC i (by omega) _ _
    ϑ.7.coprime_mul_left) ?_) 1 1 (fun t h ↦ (congrArg _ (pure_smul _ _ _ fun i _ ↦ ?_)).mpr
    (.single t h)) (by rw [m_eq_two_mul_varrho_add_two]; ring_nf; rfl)
  exact ⟨_, invMonoidHom.isOfFinOrder (isOfFinOrder_ψf _).pow, fun r ↦
    r.1.elim (fun i ↦ -Weil.normNegOne.1.1 * star (y.1 (r.2, i))) (y.2 ⟨·, r.2⟩), Prod.rec (Sum.rec
    (fun i l ↦ star_star (_ : 𝔸f D.E) ▸ star_mem_weightedTranslations (neg_mem Weil.normNegOne.1.2)
    hy.1 id (l, i)) fun _ _ ↦ hy.2 _), by simp [eq_inv_smul_iff₀, ← arrowProduct_vacElem,
    finHeisOp_arrowProduct, mul_left_comm Weil.normNegOne.1.1, ← mul_assoc]; rfl⟩
  simp [↓absNorm_piGBar, ↓card_Ohat_quot_span D.piGBar_ne_zero, Nat.card_fun, ← pow_mul,
    ← pow_add, ↓card_X, n, m_eq_two_mul_varrho_add_two, Shape.MiddleIndex]
  gcongr; grw [Nat.le_of_lt_succ hi]; lia
  simp [pairTranslates, smul_smul, ← smul_tmul',
    (show translateDatum t · = _ from (heisFinPart ..).map_smul _ ⟨_, vacElem_mem_finitePart⟩)]
  congr! 1; rw [← div_mul_cancel₀ (C i)]; simp
  simp [D.hasWeight_liftChar.hasWeight_rankTwist.norm_map_eq_one, funext_iff]

lemma projOnFinPart_pairTranslates (ϑ : D.TameChar) {t} (ht : t ∈ D.admissibleTranslations
  ϑ.levelNorm) i : TensorProduct.map (projOnFinPart _ D.piPlaces) (projOnFinPart _ D.piPlaces)
  (D.pairTranslates (D.translateDatum t) i) = D.translateDatum t _ ⊗ₜ D.translateDatum t _ := by
  have {j y} : projOnFinPart _ D.piPlaces (heisFinPart _ y (D.translateDatum t j)) =
    boxIndicator .. • heisFinPart _ y _ := Subtype.ext (projOn_finHeisOp _
    (by exact D.projOn_translateDatum (D.mem_integralAfter ht fun w ↦ by grind
    [not_isChosen_of_N_mem, D.isSplitLevel_piPlaces.natCast_mem_iff, star_star,
    w.2.notMem_of_isCoprime_of_mem ϑ.7.coprime_mul_left.cast])) y)
  simp [pairTranslates, translateSum, *, ite_tmul]
  rw [Fintype.sum_eq_single 0 fun y hy ↦ ite_eq_right fun e ↦
    hy (funext fun i ↦ (D.isSplitLevel_piPlaces.reduction_eq_iff.2 (by
    cases i <;> simp_all [mem_integralBox, idem_mul_mem_Ô, or_imp])).symm.trans (map_zero _))]
  simp [← Pi.zero_def, residueOverN, heisFinPart, LinearMap.restrict_apply, finHeisOp,
    stdLattice.semichar]

/-- For t admissible for q, `Data.reducedVacuum` t is an admissible combination of pure tensors of
translated vacua (translations admissible for qN, denominator 1, under p size ≤ N^(f·n_m·(ϱ+1))). -/
lemma isAdmissibleComb_reducedVacuum {q p} ⦃t⦄ (ht : t ∈ D.admissibleTranslations q) :
  IsAdmissibleComb (fun x ↦ pure (fun _ ↦ D.translateDatum x _ ⊗ₜ D.translateDatum x _) _)
  (D.admissibleTranslations (q * D.N)) q (1 ^ D.ϱ.succ) p (|↑(D.N ^ (D.f * D.n D.m))| ^ D.ϱ.succ)
  (D.reducedVacuum t) := by
  apply IsAdmissibleComb.pure (α := (D.X ·.succ × _ → _)) (v := fun i x ↦
    heisFinPart _ x.1 _ ⊗ₜ heisFinPart _ x.2 _)
  simp_intro .. [pairTranslates, translateSum]
  refine .of_eq_isOfFinOrder_smul (congr(∑ _, $(one_smul ..)).subst (.of_sum (by simp) (by
    simp_intro .. [↓card_X, ← pow_mul, card_piPlaces]; gcongr; exacts [D.le_of_hasLogBound,
      D.n_mono (by grind)]))) fun y _ ↦ ⟨_, (isOfFinOrder_ψf _).mul (isOfFinOrder_ψf _), (_, _), ?_,
    .trans (by apply congrArg₂ <;> ext1 <;> apply finHeisOp_finHeisOp) (smul_tmul_smul ..)⟩
  constructor <;> intro i w <;> simp_intro e [w.2.mul_mem_iff_mem_or_mem,
    D.isSplitLevel_piPlaces.natCast_mem_iff] <;> simpa [e, apply_ite, ite_apply] using ht _ i w e.1

attribute [local simp] Finsupp.sum liftInPairs_pure

/-- For a twist ϑ, q = ∏_Q Nv, let w be an admissible combination of the `Data.reducedVacuum` t, t
in `Data.admissibleTranslations` q (denominator 1, size ≤ `Data.cutBound`^{3m} if Q = ∅), fixed by ∏
K_j with last component 1. Then for some good datum Ψ the chain of paired lifts with datum w equals
∑_t Ψ(t)·(chain with data `Data.translateDatum` t) on all smooth forms on X₀. -/
lemma exists_isGoodDatum_of_invariant {w} (hw :
  IsAdmissibleComb D.reducedVacuum (D.admissibleTranslations ϑ.levelNorm) ϑ.levelNorm 1 (ϑ.Q = ∅)
  (↑(D.cutBound ^ (2 * D.m)) * D.cutBound ^ (2 * D.ϱ + 2)) w) (hi : ∀ b : ∀ k, D.columnLevel k,
  b (2 * D.ϱ + 2) = 1 → TensorChain.map (twoKernelAction (D.liftKernel ϑ) (b ·)) _ w = w) : ∃ Ψ,
  IsGoodDatum ϑ Ψ ∧ ∀ φ, TensorChain.lift (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ _
  w = chainComb ϑ Ψ D.translateDatum _ φ := let T := TensorChain.lift (TensorChain.liftInPairs (M :=
    (TensorChain _ ·)) fun _ ↦ TensorProduct.mk ..) _ _
  hw.bind _ _ D.isAdmissibleComb_reducedVacuum
    (hB := by simpa using fun _ ↦ Real.le_exp_of_log_le D.le_of_hasLogBound).imp fun Ψ s ↦
  ⟨⟨s.1, @id (_ = 2 * (_ + 1)) D.m_eq_two_mul_varrho_add_two ▸ fun b h β ↦ by simpa [s,
    twoKernelAction, ← ((lift_pure ..).trans (liftInPairs_pure ..) : T _ = TensorChain.pure ..)]
    using (congr(β (T $(hi b (h _ .refl))))), fun φ ↦ by
  simpa [s] using! congrArg (TensorChain.lift (TensorChain.liftInPairs (D.liftKernel ϑ · |>.lift)) φ
    _) (hw.elim fun r e ↦ by simp +contextual [e, reducedVacuum, D.projOnFinPart_pairTranslates ϑ,
    e.1.1, ← pairTranslates.eq_1] : w = TensorChain.map (fun i ↦ translateSum .. ∘ₗ
    TensorProduct.map (projOnFinPart ..) (projOnFinPart ..)) _ w)⟩, by simp [s, chain]⟩
end Data
end

section
/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Names for column coordinates and projection to rows on the data. Transformation law,
support and normal form of the Bessel seed of the Poincaré series. -/
seal Finset.univ Finset.sum Finset.prod

variable {P} (D : Data P) {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} {ε l kw V Y η}
  [Frame 𝔰 ε] (h : S.Fits V l kw Y η)

/-- The filling data of D fit the space Y₀ with its lattice, in the sense of `Filling.Fits`. -/
lemma Data.filling_fits : D.filling.Fits _ D.paramW D.κ (D.gradingY 0) (scalarFin _
  (D.latticeScale 0))⁻¹ := ⟨(D.exists_besselSystem · |>.choose_spec), rfl, D.isCuspKernel_paramW.1,
  ((D.exists_spaceY 0).choose_spec.2 D.nat_le_of_hasLogBound).2.imp fun _ ⟨b, e⟩ ↦ ⟨(b ⟨·, ·⟩),
  Unitary.toUnits (D.latticeScale 0),
  Units.ext (e ▸ congrArg (· * _) (show gradedLatticeBasis D.shape.besselIndexEquiv _ _ _ = _ by
  rw [Units.val_mul, Units.val_smul, val_toBesselH_apply_coe, ← map_inv]
  simp [← Matrix.ext_iff, Shape.besselIndexEquiv, filling, gradedLatticeBasis, besselLatticeBasis,
    Matrix.diagonal_apply, Units.smul_def, scalarFin, ← Unitary.star_eq_inv]
  and_intros <;> grind [Unitary.mem_iff]))⟩, (commute_scalarFin · |>.inv_left)⟩

/-- The isomorphism that translates a column on X₀ by the central element `Data.latticeScale` 0,
then takes its values at the class representatives in the coordinates of
`Filling.Fits.columnCoords`. -/
noncomputable def Data.columnCoords :=
  .ofBijective _ (D.centralRep.apply_bijective (D.latticeScale 0)) ≪≫ₗ D.filling_fits.columnCoords

/-- For s in 𝖦, the linear map y ↦ |𝖦|·e₀(sy) from the forms `Data.principalForms` on Y₀ to the
image of the good idempotent e₀. -/
noncomputable abbrev Data.goodProjTranslate s := (Nat.card D.G : ℂ) •
    ((D.principalRep (D.spaceY 0)).asAlgebraHom D.e₀).rangeRestrict ∘ₗ D.principalRep _ s

attribute [local simp] Filling.Fits.adelicEquiv_ratEquiv Filling.Fits.finiteEquiv_inclX mul_assoc
  conjWeylRep

/-- The Poincaré series of φ over a subgroup Δ is left Δ-invariant: it takes the same value at
γg and at g for every γ in Δ. -/
lemma Filling.Fits.poincare_rat_mul φ {Δ} γ (o : γ ∈ Δ) g : h.poincare φ Δ (γ * g) =
  h.poincare φ Δ g := congr(∑ _, _ * $(.trans (by simp) ((Equiv.mulRight ⟨γ, o⟩).tsum_eq _)))

/-- If 𝖶_φ, the Poincaré series over the rational points of the Bessel subgroup of Y, is nonzero
at g, some finite adelic element of that subgroup moves g_f into the principal level
`Filling.stdPrincipalLevel`. -/
lemma Filling.Fits.exists_besselFin_mul_mem_of_ne_zero φ {g} (hg : h.poincare φ Y.ratBessel g ≠ 0) :
  ∃ r ∈ Y.besselFin, r * g.2 ∈ S.stdPrincipalLevel := by
  by_contra!; have (γ : Y.ratBessel) a :=
    this _ (Y.snd_mem_besselFin (mul_mem (Y.inclX_mem_besselGroup (a⁻¹ * η)) γ.2.2))
  simp_all [poincare, cutBessel, h.mem_stdPrincipalLevel_iff, -Subtype.forall]

variable [WeilData E]

/-- For a column ψ of level Kc, n unipotent, a in U(X₀)(𝔸) and x_f in `Filling.stdPrincipalLevel`,
the Poincaré series of ψ over `Grading.ratBessel` at nax is χ(n)·A(a_∞⁻¹ψ(a_f η))·W(x_∞) (dot
product), with χ(n) = `stdAddChar`(−σ(n)/(gϖ)), σ = `simpleRootSum`, A =
`Filling.Fits.weylBesselEquiv`. -/
lemma Filling.Fits.poincare_bessel_normal_form ψ [S.IsAdmissible] {n} (hn :
  n ∈ Y.unipotent) a {x} (hx : x.2 ∈ S.stdPrincipalLevel) :
  h.poincare (h.columnCoords ψ) Y.ratBessel (n * (Y.inclX a * x)) = stdAddChar E
  (toAdele (-(S.g * S.ϖ : E)⁻¹) * simpleRootSum (h.adelicEquiv n)) * h.weylBesselEquiv.1
  (conjWeylRep _ 0 a.1⁻¹ (ψ.1.1 (a.2 * η))) ⬝ᵥ S.besselFn (h.realHomeo x.1) := by
  have A {g} o : S.adelicToFin (h.adelicEquiv g) ∈ besselU :=
    toLatBasis_mem_besselU.2 ((h.mem_unipotent_iff.1.1 o).map_mem_unitriangularOn _)
  obtain ⟨⟨d : S.Classes, γ, k, e⟩, u, hu, l⟩ := exists_eq_map_mul_rep_mul stdEmbFin S.columnLevel
    (·.out_eq) (a.2 * η), exists_besselU_approx (A hn) (S.inclHFin (a.2 * η))
  have U u (o : u ∈ besselU) :=
    h.mem_unipotent_iff.1.2 ((h.adelicEquiv_ratEquiv u).substr (o.map_mem_unitriangularOn _))
  have Q g (k : (S.h d)⁻¹ * (S.inclHFin η * h.finiteEquiv g.2) ∈ S.principalLevel) :
      h.poincare (h.columnCoords ψ) Y.ratBessel g =
    h.weylBesselEquiv.1 (ψ.1.1 d.out) ⬝ᵥ S.besselFn (h.realHomeo g.1) := by
    have key γ w {c i} (o : h.cutBessel (c, i) (γ * g) ≠ 0) : c = d ∧ ∃ u : S.classUnip c,
      Subtype.mk _
      (Subgroup.mem_inf.2 ⟨(h.ratEquiv u).2, Y.unipotent_le_besselGroup (U u u.2.1)⟩) = ⟨γ, w⟩ := by
      obtain ⟨σ, e⟩ := h.ratEquiv.surjective ⟨γ, w.1⟩; obtain rfl := congr($e.1)
      simp [cutBessel_ratEquiv_mul] at o; exact .imp_right (⟨⟨_, ·⟩,
        rfl⟩) (eq_and_mem_classUnip_of_besselS (toAdele.injective <| by
        simpa using! h.mem_unipotent_iff.2.1 w.2 · · ·)
        (by simpa [termPosition] using mul_mem o.1 (inv_mem k)))
    rw [poincare, Fintype.sum_prod_type,
      Fintype.sum_eq_single d (by simp +contextual [Not.imp_symm (key _ _)]), dotProduct]; congr! 2
    rw [← Function.Injective.tsum_eq (by simp [Function.Injective]) (key _ ·.2 · |>.2),
      tsum_cutBessel_classUnip (d, _), ite_eq_left k]
  obtain ⟨r, _⟩ := U _ (inv_mem hu), levelSpace_smoothFormRep_apply ψ.2 γ d.out k
  rw [← poincare_rat_mul (o := Subgroup.mem_inf.2 ⟨(h.ratEquiv _).2, Y.unipotent_le_besselGroup r⟩),
    ← mul_assoc, ← poincare_rat_mul (o := Y.inclX_mem_ratBessel ⟨γ⁻¹, rfl⟩), Q]
  simp only [realHomeo_mul, adelicToInf_inclX, h.weylBesselEquiv.2, besselFn_adelicToInf_mul
    (h.mem_unipotent_iff.1.1 (mul_mem r hn)), dotProduct_smul, ← coe_map_conj_inv_eq_transpose]
  rw [unipotentChar_eq_of_mem_principalLevel (one_mem _) (A (mul_mem r hn)) (a.2 * η)
    (by simpa using! inv_mem l), map_mul h.adelicEquiv, simpleRootSum_mul] <;> simp_all [mul_add,
    AddChar.map_add_eq_mul, Space.weightRep, weylRep, ←
    map_mul, -map_neg, -map_inv, (stdSpace ..).ratEmbed.map_inv, h.mem_unipotent_iff]
  simpa [↓finiteEquiv_eq_adelicToFin, adelicToFin_adelicEquiv_inclX, eq_mul_inv_of_mul_eq e] using!
    mul_mem (IsAdmissible.columnLevel_eq.le k.2).out (mul_mem
    (inv_mem l) (h.mem_stdPrincipalLevel_iff.1 hx))

/-- Under `Filling.IsAdmissible`, if jc = −(gϖ)⁻¹ (j = `WeilData.j`, c the scale of the grading),
the
Poincaré series over the rational Bessel subgroup of an algebraic form ψ of level Kc
satisfies the hypotheses `Grading.IsGeneric` of the unfolding step on Y. -/
lemma Filling.Fits.isGeneric_poincare ψ [S.IsAdmissible] (hjc : WeilData.j * Y.c = -(S.g * S.ϖ :
  E)⁻¹) : Y.IsGeneric (h.poincare (h.columnCoords ψ) Y.ratBessel) := by
  choose F L C using fun g ↦ (by_contra fun H ↦ H ⟨0, fun u y k ↦ .trans (by_contra fun e ↦ H
    ((h.exists_besselFin_mul_mem_of_ne_zero _ e).elim fun r ⟨hr, l⟩ ↦
    (Y.exists_unipotent_mul_inclX (inv_mem (mul_mem hr (Y.unipotent_le_besselGroup u.2)))).elim
    fun m ⟨_, a, d⟩ ↦ ⟨_, fun n x i ↦ by
    nth_rw 1 [← inv_mul_cancel_left _ x, d, mul_assoc, ← mul_assoc, poincare_bessel_normal_form,
      map_mul h.adelicEquiv, simpleRootSum_mul, mul_add, AddChar.map_add_eq_mul, Circle.coe_mul,
      mul_assoc] <;> simp [*, mul_mem, ← h.mem_unipotent_iff.1]
    simpa using mul_mem l (mul_mem (inv_mem k) i), by fun_prop⟩)) (by simp), by fun_prop⟩ :
    ∃ F, (∀ (n : Y.unipotent) x,
    (g⁻¹ * x).2 ∈ S.stdPrincipalLevel → h.poincare (h.columnCoords ψ) _ (n * x) =
    stdAddChar E (_ * simpleRootSum (h.adelicEquiv n)) * F x) ∧ Continuous F)
  have K g x := by simpa [simpleRootSum_eq_zero_of_mem_besselH] using L g 1 x
  use continuous_of_cover_nhds (⟨·, S.stdPrincipalLevel.2.preimage_of_continuous.mem_nhds
    (by simp)⟩) (C · |>.continuousOn.congr (K _)), h.poincare_rat_mul _, fun g n hn _ ↦ ?_
  erw [L g ⟨n, hn⟩, K g, (?_ : Y.shift = toAdele Y.c.1 • besselCharMatrix _), smul_mul_assoc,
    Matrix.trace_smul, trace_besselCharMatrix_mul (h.adelicEquiv n), simpleRootSum_inv,
    ← stdAddChar_half (E := E), ← hjc] <;>
    simp [h.mem_unipotent_iff.1.1 hn, Y.c.2, div_eq_inv_mul, mul_add]
  rcases 𝔰 with ⟨_ | _⟩ <;> simp [Grading.shift, besselCharMatrix, ← Matrix.ext_iff, h.index_eq,
    Shape.besselIndexEquiv, splitGram, middleGram, besselFrame,
    Fin.forall_fin_succ', ← Fin.castSucc_succ]; clear * -; grind (splits := 20) [map_natCast]
end
