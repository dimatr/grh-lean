import Lib.DiscreteSeries.FlenstedJensenInvariance
import Lib.DiscreteSeries.JointHarmonicUnique
import Lib.DiscreteSeries.LocalThetaCorrespondence
import New.Weil.FourierCoefficient
import Lib.GaloisRep.ReproducingKernel

-- part: Lib.DiscreteSeries.Theta.JointHarmonicExists
section
/-! One general lemma (a derivation applied to a product of determinants), then joint harmonics for
`FockDualPair`.

Part of: Theta correspondence of discrete series for real unitary dual pairs; joint harmonics (known
result; see Lib.DiscreteSeries.Theta.LocalThetaCorrespondence).

This file: Products of minors are joint harmonics; existence for matched parameters. -/


open Matrix MvPolynomial Finset Units Function Fischer
variable {L} [Fintype L] {I : L → Type} [∀ t, Fintype (I t)] {R C} [Fintype R] [Fintype C] {ε ε' ι}
  [Fintype ι] (T : @FockDualPair R C ε ε' ι) (l ν : HCParam ε) {l' ν'} (ρ κ : ∀ t, I t → _)

omit [Fintype R] in
lemma derivation_prod_det (D : Derivation ℂ (MvPolynomial R ℂ) _) (N M : ∀ t, Matrix (I t) _ _)
    (h : ∀ t i k, D (M t k i) = ∑ j, N t i j • M t k j) :
    D (∏ t, det (M t)) = (∑ t, ∑ i, N t i i) * ∏ t, det (M t) := by
  have {t} : D (M t).det = ∑ i, N t i i • (M t).det := by
    have {s f} : D (s.prod f) = ∑ i ∈ s, s.prod (update f (i : I t) (D (f i))) := by
      induction s using cons_induction <;> simp_all [mul_sum, prod_update_of_notMem]
      grind [sum_congr]
    simp_all [det_apply', updateCol, ↓← det_updateCol_sum, update_apply, mul_sum, @sum_comm (I t)]
  induction @univ L _ using cons_induction <;> simp_all [← sum_mul]; ring

/-- Finitely many layers of paired rows ρ_t (distinct) and columns κ_t, with one column sign on
layers sharing a row, rows closed under moving outwards in l, and total weight ν. -/
structure IsLayering where
  injective t : Injective (ρ t)
  sign_eq t u i j k m : ρ t i = ρ u j → ε' (κ t k) = ε' (κ u m)
  closed t i r : ε r = ε (ρ t i) → 0 < T.varSign (ρ t i, κ t i) * (l r - l (ρ t i)) → ∃ j, ρ t j = r
  weight_eq r : ν r = T.vacuumWeight (ε r) + ∑ t, ∑ i with ρ t i = r, (T.varSign (r, κ t i)).1

attribute [local grind] pairSign IsLayering int_unit_val_eq_one_or_neg_one IsMatch HasGap
  sum_eq_zero val_mul Units.val_neg
variable {T l ν ρ κ} (H : IsLayering T l ν ρ κ) (hm : IsMatch T l l')
include H

omit [Fintype ι] in
lemma IsLayering.isKHighest_and_isHarmonic {P} (hP : P = ∏ t, det (of fun i j ↦
  X (T.varEquiv (ρ t i, κ t j)))ᵀ) : l.IsKHighest T.oscRows ν P ∧ T.swap.IsHarmonic P := by
  simp +contextual [-pairSign, ← C_mul', oscRows_E_eq_polarisation_sub, polarisation,
    (by simpa [-sum_boole, -pairSign] using (fun a b (s : ℤˣ) (_ : a = b ∨ ε a = ε b ∧ s * l b < s *
    l a) ↦ hP ▸ derivation_prod_det (.mk' (∑ c with T.varSign (b, c) = s, @X ℂ _ _ (T.varEquiv (a,
    c)) • (pderiv (T.varEquiv (b, c))).1) (by simp [mul_sum, ← sum_add_distrib]; grind))
    (fun t i j ↦ ite (ρ t i = b ∧ ρ t j = a ∧ T.varSign (b,
    κ t i) = s) 1 0) _ (by obtain ⟨_, rfl⟩ | _ := em <| ∃ j, ρ · j = a <;> simp [(H.1 _).eq_iff] <;>
    grind) :)), H.4, ← sub_mul, ← add_mul, ← sum_sub_distrib, -sum_boole, add_comm, sum_filter]
  use ⟨fun _ ↦ .inl (by congr!; split_ifs <;> simp_all), by grind⟩
  grind [_root_.pderiv_comm, units_ne_neg_self (R := ℤ), show ∀ x,
    (∀ t i j, (ρ t i, κ t j) ≠ x) → pderiv (T.varEquiv x) P = 0 by
    simp_all [derivation_prod_det _ 0]]

omit [Fintype ι] in
/-- If (ρ, κ) are layers as in `IsLayering` for the rows and (κ, ρ) for the columns, the product of
the minors on (ρ_t, κ_t) is nonzero, highest of weight ν for rows and ν' for columns, and
satisfies `IsHarmonic` both ways. -/
lemma IsLayering.joint_highest_prod_det {ν'} (H' : IsLayering T.swap l' ν' κ ρ) {P} (hP : P =
  ∏ t, det (of fun i j ↦ X (T.varEquiv (ρ t i, κ t j)))) : T.IsJointHighest l l' P ν ν' :=
  ⟨by simpa [*, prod_eq_zero_iff, det_apply] using (fun t ↦ (rename_injective _
  (T.varEquiv.injective.comp ((H.1 t).prodMap (H'.1 t)))).ne (det_mvPolynomialX_ne_zero _ ℂ)),
  and_assoc.1 ⟨H'.isKHighest_and_isHarmonic hP, H.isKHighest_and_isHarmonic (by simpa)⟩⟩

omit H
include hm

/-- For matching parameters λ, λ', rows and columns of the matched pairs (r, c) form layers
(`IsLayering`) of total weight Λ, one layer for each m < |Λ_r − v_r| (v the vacuum weight) and
each pair of signs, relabelled by the permutation s. -/
lemma IsMatch.isLayering (s : Equiv.Perm _) {w} (hw : w = (fun (r, c) ↦ ite (T.IsMatchedPair l l' r
  c) (T.relWeight l r).natAbs 0) ∘ T.varEquiv.symm) : IsLayering T l l.lowestKType (fun (t :
  Fin (univ.sup w) × _) (x : {x // t.1 < w x ∧ s ((T.varEquiv.symm x).map ε ε') = t.2}) ↦
  (T.varEquiv.symm x).1) fun _ x ↦ (T.varEquiv.symm x).2 := by
  have := hm.1.isKDominant_lowestKType; simp_all [IsKDominant]
  have {r} : T.relWeight l r ≠ 0 → ∃ c, T.IsMatchedPair l l' r c ∧ T.varSign (r, c) = (T.relWeight l
    r).sign := by grind [by simpa using And.intro (hm.sign_mul_lowestKType_sub_nonneg r 1)
                              (hm.sign_mul_lowestKType_sub_nonneg r (-1))]
  constructor; rotate_right; intro r
  rw [sum_sigma', sum_of_injOn (·.1.1.1), sum_const (T.relWeight l r).sign,
    card_range (T.relWeight l r).natAbs]
  all_goals simp [*, reindex_equiv T.varEquiv, Injective, Set.InjOn, Set.MapsTo,
    Fin.exists_iff, Sigma.forall, Sigma.subtype_ext_iff]; grind [Units.ext, s.injective]

/-- If the parameters l, l' match for T (`IsMatch`), then there is a joint harmonic polynomial Φ in
the sense of `IsJointHarmonic`: nonzero and highest for both lowest K-types Λ and Λ'.

Known result: Theta correspondence of discrete series for real unitary dual pairs; joint
harmonics. -/
lemma IsMatch.exists_isJointHarmonic : ∃ Φ, IsJointHarmonic T l l' Φ :=
  ⟨_, hm, (hm.isLayering 1 rfl).joint_highest_prod_det
  (hm.swap.isLayering (.prodComm ..) (by grind [lowestKType_sub_vacuumWeight_eq_neg])) rfl⟩
end

-- part: Lib.Weil.Lift.Edge
section
/-! Known result: Joint harmonics and global theta lifts between discrete series types. Here the
parameter has large gaps, and the types are given by integrable projector kernels. The lift is shown
to carry forms fixed by one kernel to forms fixed by the other, in both directions, without Howe
duality. Source: J.-S. Li, Theta lifting for unitary representations with nonzero cohomology, Duke
Math. J. 61 (1990); Howe, JAMS 2 (1989); A. Ichino, arXiv 2002.09148, Lemma 7.8.

This file: Theta lifts with joint harmonic data carry discrete series forms to the corresponding
type. -/

noncomputable section


open NumberField MeasureTheory Matrix ComplexConjugate MvPolynomial Fintype Norms.L2Operator
  Classical Complex CompactlySupported Set Heisenberg.IsVacuum
variable {E n n' ι : Type} [Field E] [CMType E] [WeilData E]
  [Fintype n] [Fintype n'] [Fintype ι] {s : n → _} {t : n' → _} (γ γ' : InfinitePlace E → ℤ)
  (l : _ → n → ℤ) (l' : _ → n' → ℤ) {η : ι → _}
  (Ω : GInf E s × GInf E t → fockSpace (realSigns E η) →L[ℂ] fockSpace (realSigns E η))
  (e : GInf E s → ℂ) (e' : GInf E t → ℂ) (Φ : fockSpace (realSigns E η))

/-- e is a cusp kernel of order 0; ∫ ⟨Φ, Ω(x,1)Φ⟩ ē(x)/e(1) dx ≠ 0; for theta kernels over Ω,
lifts of forms of type e by Φ⊗f with a level have type e', and lifts by v⊗f, v polynomial,
are R(α_v) of them, α_v in C_c. -/
structure IsHalfEdge where
  isCuspKernel_source : IsCuspKernel 0 e
  inner_ne_zero : ∫ x, realInner Φ (Ω (x, 1) Φ) * (conj (e x) / e 1) ≠ 0
  lift_isForm_and_eq_realConv : ∀ v ∈ range (polyVector _), ∃ α : C_c(_, ℂ), ∀ {V : Space E ι η} {S
    T y f} (Θ : ThetaKernel _ S T), (∀ x y v f, Θ.ω ((x, 1), y, 1) (V.integrated v f) =
    V.integrated (Ω (x, y) v) f) → S.IsForm e y → let F := S.lift Θ (V.integrated Φ f) y; (∀ K :
      OpenSubgroup _, HasLevel F K → T.IsForm e' F) ∧ S.lift Θ (V.integrated v f) y = realConv α F

/-- Φ is a half edge for Ω with kernels e, e', and also for Ω with its two groups exchanged with
kernels conj(e'), conj(e). -/
structure IsEdge extends IsHalfEdge Ω e e' Φ where
  swapped : IsHalfEdge (Ω ·.swap) (star e') (star e) Φ

/-- The element −l if the Boolean d is true, and l otherwise. -/
abbrev negIf {α} [Neg α] d (l : α) := cond d (-l) l

/-- The parameters l (signs s) and l' (signs t) correspond: at each infinite place w, l'_w and
−l_w match for signs t, s and weights γ_w, −γ'_w (`IsMatch`). -/
def ParamsCorrespond s t := ∀ w, IsMatch (.std t s (γ w) (-γ' w)) (l' w) (-l w)

/-- The product over the infinite places w of chosen joint harmonic polynomials (`IsJointHarmonic`;
arbitrary where none exists) for signs t, s and parameters l'_w, −l_w, each in the variables of
w. -/
def jointHarmonic {E n n' : Type} [Field E] [NumberField E] [Fintype n] [Fintype n']
    (γ γ' : InfinitePlace E → ℤ) (l : _ → n → ℤ) (l' : _ → n' → ℤ) s t := ∏ w,
  (epsilon (IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w))).rename (w, ·)

variable {γ γ' l l' Ω} {π π' Φ : _ → _} [Nonempty n] [Nonempty n']
attribute [local simp] realConv rep_apply_apply realPairWeil pairHomInf realWeil_piTensor mul_assoc
  ContinuousMultilinearMap.map_smul_univ

omit [WeilData E] in
lemma integral_piTensor_eq_integratedRep {A} (hu : ∀ w, IsUnitaryRep A (π w) realInner) (k : _ →
  _ → ℂ) (a : ∀ w, Continuous (k w)) (hk : ∀ w, Integrable fun g ↦ k w g * ‖g.1.1‖ ^ A) (v : _ →
  fockSpace η) {X} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : _ →L[ℂ] X) :
  let F (x : GInf E s) := T (piTensor fun w ↦ k w (x w) • π w (x w) (v w))
  Integrable F ∧ ∫ x, F x = T (piTensor fun w ↦
    integratedRep (π w) (k w) (v w)) := have := (hu · |>.1)
  (fun I ↦ ⟨T.integrable_comp I, T.integral_comp_comm I ▸ congrArg T (ext fun z ↦
    ((modelEval z).integral_comp_comm I).symm.trans (congr(∏ w, $(map_integratedRep (hu w) (hk w)
                  (modelEval _) _)) ▸ integral_fintype_prod_eq_prod _ :))⟩) (.mono' (.const_mul
                  (.fintype_prod fun w ↦ (integrable_smul_rep (hu w) (hk w) _).norm) _)
    (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun _ ↦ piTensor.le_opNorm _))

/-- Let n, n' ≥ 1, (π_w, π'_w) oscillator pairs, Φ_w joint harmonics of parameters l_w, l'_w,
and let Ω act on pure tensors through ⊗π_w and ⊗π'_w. Then the tensor product of the Fock
vectors of the Φ_w is a half edge e_{−l} → e_{l'}. -/
lemma isHalfEdge_of_oscillatorPair {T : _ → _} (hp : ∀ w, OscillatorPair (T w) (π w) (π' w))
    (hΦ : ∀ w, IsJointHarmonic (T w) (l w) (l' w) (Φ w)) (hΩ : ∀ v, (∀ x, Ω (x, 1) (piTensor v)
    = piTensor fun w ↦ π w (x w) (v w)) ∧ ∀ y, Ω (1, y) (piTensor v) = piTensor fun w ↦ π' w (y w)
  (v w)) : IsHalfEdge Ω (typeKernel (-l) s) (typeKernel l' t) (piTensor (polyVector η <| Φ ·)) := by
  have A := integral_piTensor_eq_integratedRep (hp · |>.unitary_rep) _ (by fun_prop)
    (hΦ · |>.hasLargeGap.integrable_norm_pow_smul_dsKernel)
  simp [← hΩ] at A
  choose α e using fun a w ↦ (hp w).exists_bump_integratedRep_eq (hΦ w) (monomial (.curry a w) 1)
  refine (fun h ↦ ⟨h, by simpa [h.apply_one_ne_zero, conj_dsKernel_neg (hΦ _).gap, ↓mul_div,
    mul_comm, integral_div] using (A _ (realInner _)).2.trans_ne (by simp [realInner_piTensor,
    Finset.prod_eq_zero_iff, ne_zero_of_re_pos
    ((hp _).re_inner_integratedRep_pos (hΦ _))]), fun _ ⟨P, o⟩ ↦ o ▸ ⟨∑ a ∈ P.support, P.coeff a •
    bumpProduct (α a), ?_⟩⟩) (isCuspKernel_typeKernel (l := -l) (hΦ · |>.hasLargeGap.neg))
  introv W hy
  obtain ⟨⟨L, hL⟩, ⟨_, _, hC⟩, B, ⟨⟩⟩ := Θ.exists_clm_lift (hy.mem_rapidFunctions h),
    Θ.exists_norm_theta_mul_le (hy.mem_rapidFunctions h), (hΦ · |>.swap.hasLargeGap le_rfl), hy.1
  have M v g : _ = S.lift Θ (V.integrated (piTensor v) f) y g := (hL (V.integrated _ f) g).trans (by
    erw [← (A v (_ ∘L V.integrated.flip f)).2, ← hy.3 h.1.2]
    simp [← W, ← hL, ↓Θ.lift_omega_left hy.1, Space.lift, ← integral_const_mul]
    rw [← integral_inv_eq_self, integral_integral_swap]
    simp [-integral_const_mul, typeKernel, ((hΦ _).hasLargeGap
      le_rfl).isIdempotentKernel_dsKernel.3, ← conj_dsKernel_neg (hΦ _).gap]; ac_rfl
    exact (((A v (V.integrated.flip f)).1.norm.comp_inv.const_mul _).comp_fst _).mono'
      (by fun_prop) (.of_forall fun ⟨x, a⟩ ↦ (hC _ (a * (x, 1)) g).trans' (by simp [← W])))
  have R {k} b (a := by fun_prop) g :=
    integral_piTensor_eq_integratedRep (hp · |>.column_rep.unitary_rep) k a b
    (fun w ↦ integratedRep (π w) (dsKernel (l w)) (Φ w)) (L g ∘L V.integrated.flip f)
  obtain ⟨R₀, Q⟩ := R (B · |>.integrable_norm_pow_smul_dsKernel), fun a ↦
    R (integrable_bump_inv_smul _ <| α a ·)
  simp [(hp _).integratedRep_fix (hΦ _) (B _).integrable_norm_pow_smul_dsKernel
    (B _).isIdempotentKernel_dsKernel.convolution_self, M, ← e, ← hΩ, ← W, ← hL, ← lift_mul_right,
    -Prod.forall] at R₀ Q
  use (funext (R₀ · |>.2) ▸ T.isForm_realConv (isCuspKernel_typeKernel B) ⟨.congr (by fun_prop)
    (one_mul · ▸ ((lift_mul_right Θ 1 _).trans (hL ..)).symm), Θ.fixesLeft_lift, ·, ·⟩ (R₀ · |>.1))
  ext; simp [bumpProduct, Finset.sum_mul, Q, integral_finsetSum, Integrable.const_mul]
  nth_rw 1 [P.as_sum]; simp [hL, piTensor_polyVector, monomial_eq, C_mul', prod_prod_type]

/-- In positive ranks, if each Φ_w is a joint harmonic (`IsJointHarmonic`) with parameters l'_w,
−l_w for `FockDualPair.std` t s γ_w (−γ'_w), the Fock vector of ∏_w Φ_w (separate variables per
place) is a `IsEdge` for `realPairWeil` γ γ' with kernels `typeKernel` of l, l'.

Known result: Joint harmonics and global theta lifts between discrete series types. -/
lemma isEdge_of_isJointHarmonic (hΦ : ∀ w, IsJointHarmonic (.std t s (γ w) (-γ' w)) (l' w) (-l w) (Φ
  w)) : IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t) ↑(∏ w, rename (w, ·) (Φ w)) :=
  piTensor_polyVector Φ ▸ ⟨neg_neg l ▸ isHalfEdge_of_oscillatorPair (fun _ ↦ .swap
  oscillatorPair_detTwist) (hΦ · |>.swap)
  (by simp), by simpa +unfoldPartialApp [typeKernel, ← conj_dsKernel_neg (hΦ _).gap',
  ← (conj_dsKernel_neg (hΦ _).gap), Pi.star_def] using
  isHalfEdge_of_oscillatorPair (fun x ↦ oscillatorPair_detTwist) hΦ (by simp)⟩

/-- Let n, n' ≥ 1. If l, l' correspond for the weights γ, γ' and signs s, t, the Fock vector of
the product `jointHarmonic` of joint harmonics is an edge e_l → e_{l'} for the real Weil
representation of weights γ, γ'. -/
lemma ParamsCorrespond.isEdge_jointHarmonic (h : ParamsCorrespond γ γ' l l' s t) :
  IsEdge (realPairWeil γ γ') (typeKernel l s) (typeKernel l' t) (jointHarmonic γ γ' l l' s t) :=
  isEdge_of_isJointHarmonic (epsilon_spec <| h · |>.exists_isJointHarmonic)
end
end
