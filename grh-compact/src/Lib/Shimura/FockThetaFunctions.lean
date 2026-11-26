import Lib.Weil.NameWeilAction
import Lib.Shimura.ThetaOrthogonality
import Lib.Adelic.PeriodLattice

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

Part of: Galois action on CM theta functions and on the finite Weil representation (known result;
see Lib.CM.Reciprocity.SemilinearWeilLaw).

This file: Definition of tight frames in the unimodular lattice, with multiplicities. Definition:
orthogonality relation between translates of the vacuum and of a finite vector. Relation: jets of
one vector are Galois conjugates of those of another. -/

variable {E I : Type} [Field E] [CMType E] [WeilData E] (w : I → E) [Fintype I]

/-- The finite image of γ in E^n: the finite adelic vector α⁻¹γ, with α the idele of the Weil
data. -/
noncomputable def finiteImage := (‹WeilData E›.α⁻¹.1 • Algebra.linearMap E (𝔸f E)).compLeft I

/-- The w_i lie in the lattice E ∩ αÔ and, taken m_i times, form a tight frame of length M: ∑
m_i σ(w_i)·conj(τ(w_i)) = Mδ_{στ} for σ, τ in the CM type. -/
def IsTightFrame (m : I → ℕ) (M : ℕ) := (∀ i, finiteImage w i ∈ Ô E) ∧ ∀ σ τ, ∑ i, m i *
    (Φ σ (w i) * starRingEnd ℂ (Φ τ (w i))) = ite (σ = τ) ↑M 0

lemma IsTightFrame.repeat_vectors {m M} (h : IsTightFrame w m M) : IsTightFrame (fun x : Σ i,
  Fin (m i) ↦ w x.1) 1 M := by simp_all [IsTightFrame, finiteImage, Fintype.sum_sigma]

/-- Orthogonality data for F: N^{2fn} > 0 finite vectors x_j with δx_j integral (f infinite
places, rank n), and m ∈ ℕ with ∑_j m·ℓ(ϱ(αx_j)vac)·ϱ(−αx_j)F = N^{2fn}·ℓ(F)·vac for all
linear forms ℓ. -/
structure Space.VacuumExpansion {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] {s} (V :
  Space E n s) (δ : E) (N F) where
  (Index) [fintypeIndex : Fintype Index] [nonempty : Nonempty Index] (shift : Index → n →
    𝔸f E) (multiplier : ℕ) mul_shift_mem j i : δ * shift j i ∈ Ô E
  card_dvd : Fintype.card Index = N ^ (2 * Fintype.card (NumberField.InfinitePlace E × n))
  sum_eq (ℓ : _ →ₗ[ℂ] ℂ) : ∑ j, (multiplier * ℓ (V.ϱ (finVec (shift j)) V.vacElem)) • V.ϱ (finVec
    (-shift j)) F = (Fintype.card Index * ℓ F) • V.vacElem

/-- The series T_t f with σ applied to its coefficients equals T_{t'} f' with the places of its
variables renamed by π⁻¹. -/
abbrev Space.IsJetConjugate [Field I] [CMType I] [WeilData I] {n : Type} [Fintype n] {s} {V :
  Space I n s} σ (π : Equiv.Perm _) t t' f f' := (V.jetSeries t f).map σ =
  (V.jetSeries t' f').rename (.map π.symm id)

@[simp] lemma Space.constantCoeff_jetSeries {s} {V : Space E I s} t f :
    (V.jetSeries t f).constantCoeff = V.θ (V.projReal f) := (jetSeries_apply ..).trans (by simp)
end

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Entire canonical theta functions come from finite Weil vectors, with Schur
orthogonality. -/
seal Finset.univ Finset.sum Finset.prod

open AddSubgroup Complex ComplexConjugate Heisenberg IsAppellHumbert stdLattice NumberField Space
  WeilData

variable {E n : Type} [Field E] [CMType E] [WeilData E] (γ : n → E)

/-- The archimedean image of γ in E^n in Fock's coordinates: the complex vector with entry √(2π
Im τ(ȷ))·τ(γ_i) at (τ, i). -/
noncomputable def realImage p := realCoord (toAdele ∘ γ) p

attribute [local simp] Finset.mul_sum Real.pi_nonneg Real.sqrt_ne_zero' IsStd.point_eq_one
  vecAtPoint entireTheta finHeisOp im_pos val_scaleIdele_fst val_scaleIdele_snd dotProduct
  finiteImage fieldEq funext_iff realCoord realImage realVac signMatrix

lemma denseRange_finiteImage : @DenseRange _ _ (n → E) finiteImage := .piMap fun _ ↦
    α⁻¹.mulLeft_bijective.2.denseRange.comp denseRange_algebraMap_finAdele (by fun_prop)

variable [Fintype n] {ε} {b : (_ → ℂ) →L[ℂ] _ × n → ℂ}
  (hb : ∀ u x, b u x = conj (Φ x.1 (traceOne : E)) * u x) (V : Space E n ε)
  {B : RealComplexForm (InfinitePlace E × n → ℂ)} (hB : ∀ l z, B l z = star l ⬝ᵥ z) [i : V.IsStd]

lemma exists_finiteImage_approx {V : Space E n ε} {F} (hF : F ∈ V.finitePart) x :
    ∃ γ, finiteImage γ - x ∈ stdLattice .. ∧ V.ϱ (finVec (finiteImage γ)) F = V.ϱ (finVec x) F :=
  denseRange_finiteImage.exists_mem_open ((isOpen_stdLattice.preimage_of_continuous (f :=
  (· - _))).and (isLocallyConstant_rho_finVec hF {_})) ⟨x, by simp⟩

lemma vecAtPoint_eq_adelicSum : V.vecAtPoint γ =
  (adelicSum E ε).equiv (realImage γ, finiteImage γ) := by simp [adelicSum, Prod.ext_iff]

/-- For standard V, γ in E^n and f in 𝒮(V), translation ϱ by the finite part of γ turns the
theta function Θ_f into y ↦ exp(⟨r,y⟩ − ⟨r,r⟩/2)·Θ_f(y − r), where r = `realImage` γ and ⟨z,w⟩
= ∑ z̄_i w_i. -/
lemma entireTheta_translate_finiteImage (hB : ∀ l z, B l z = star l ⬝ᵥ z) f :
  entireTheta (V.ϱ (finVec (finiteImage γ)) f) = thetaShift B (-realImage γ) (entireTheta f) := by
  ext; erw [thetaShift_apply, entireTheta, entireTheta, ← V.apply_vecAtPoint_add f γ,
    ← heisRep_right_rho, ϱ_apply]
  simp_rw [vecAtPoint_eq_adelicSum, ← adelicSum_real_eq_realVec ε, OrthogonalSum.beta_equiv,
    ← map_add]; simp [i.1, hB, mul_assoc, realHeis, ← exp_add, mul_add, add_mul, -realImage]; grind

include hb hB

/-- Product formula: if b multiplies the coordinates at τ by the conjugate of τ(c₀), then for γ
in E^n the finite factor `stdLattice.semichar` at α⁻¹γ is the inverse of the canonical multiplier of
b at −r, r = `realImage` γ. -/
lemma semichar_finiteImage : semichar (finiteImage γ) =
  (canonicalMultiplier B b (-realImage γ))⁻¹ := by refine eq_inv_of_mul_eq_one_right (.trans
  congr(exp ($(?_)) * psi₀ E $(?_)) (by simpa only [vecAtPoint_eq_adelicSum,
  OrthogonalSum.beta_equiv] using! (beta_vecAtPoint_eq_one (stdSpace ..) ((traceOne : E) • γ)
  γ))) <;> simp [*, stdLattice.traceOneAdele, ↓riemannForm_def, ↓im_eq_sub_conj, -sub_im] <;> grind

/-- Let V be standard, d in E integral, d d̄ = N ≠ 0. An entire S fixed by the normalised
translations by −`realImage`(d̄γ), for all γ with α⁻¹γ integral, is Θ_F for some F in 𝒲_f that
has orthogonality data `Space.VacuumExpansion` for d, N. -/
lemma Space.exists_entireTheta_eq {d : E} (hd : ↑d ∈ Ô E) {N : ℕ} (h0 : N ≠ 0) (hN : d * star d =
  N) {S} (hS : Differentiable ℂ S) (h : ∀ γ, finiteImage γ ∈ stdLattice .. →
  normalizedShift B b (-realImage (star d • γ)) S = S) :
  ∃ F ∈ V.finitePart, entireTheta F = S ∧ Nonempty (V.VacuumExpansion d N F) := by
  let T : _ →ₗ[ℂ] _ := ⟨⟨V.entireTheta, by simp⟩, by simp⟩
  have inj := Function.Injective.of_ker T (by simp_all [T, eq_zero_of_realVec])
  have : T V.vacElem ≠ 0 := by grind [V.dataInner_vacElem_vacElem, T.map_zero]
  let L := classLattice (.scalar n α) ⊥ (.symm (.curry ..) ≪≫ₗ .funCongrLeft ℝ ℂ (.prodComm ..) ≪≫ₗ
    (by simp [Pi.isUnit_iff]; grind [Nat.cast_ne_zero] : IsUnit (-realImage fun _ ↦
    star d)).unit.mulLeftLinearEquiv ℝ _).toContinuousLinearEquiv
  have hL {x} : x ∈ L ↔ ∃ γ, finiteImage γ ∈ stdLattice .. ∧ -realImage (star d • γ) = x :=
    exists_congr (by simp [frameTorsionClass, frameCoords, mem_stdLattice, ← map_inv, mul_comm])
  change LatticeForm L at B
  have U γ f : T _ = B.thetaShift _ (T f) := entireTheta_translate_finiteImage γ V hB f
  have hv : T V.vacElem ∈ B.thetaSpace (canonicalMultiplier B b) :=
    mem_thetaSpace_iff_normalizedShift.2 ⟨differentiable_entireTheta i.1 (by simp), by
    simpa [normalizedShift, ← U, ← semichar_finiteImage, *, -funext_iff] using
      fun x ↦ congrArg T ∘ finHeisOp_vacElem ∘ smul_mem_stdLattice (star_mem_Ô hd)⟩
  let ⟨H, _⟩ : IsAppellHumbert B (canonicalMultiplier B b) ∧ IsPosRiemann B :=
    ⟨⟨by simp [hB, mul_comm], by simp [canonicalMultiplier],
    fun x _ y _ ↦ by simpa [smul_left_inj, riemannForm_swap x, thetaShift_of_mem hv, *, -hL,
    add_mem, smul_smul, exp_neg, mul_comm] using (@thetaShift_thetaShift _ _ ⊥ 1 (T V.vacElem) B
    (by simp [isAppellHumbert_iff, mul_comm, hB, -funext_iff]) x y).symm⟩, isPosRiemann_of_re_pos
    (by simp [← normSq_apply, normSq_nonneg, Finset.sum_pos_iff_of_nonneg, *])⟩
  choose γ e using fun a : B.dualLattice ↦ (H.exists_nsmul_mem_of_mem_dualLattice.elim fun M e ↦
    (hL.1 (e.2 _ a.2)).imp' ((star d / M) • ·) (by clear * - e; simp_all) : ∃ γ, -realImage γ = a)
  have k a : d • finiteImage (γ a) ∈ _ :=
    mem_stdLattice_iff_psi₀.2 (denseRange_finiteImage.induction_on · (isClosed_imp
    isOpen_stdLattice (isClosed_eq (by fun_prop) (by fun_prop))) fun y s ↦ by
    simpa [*, smul_left_inj, canonicalMultiplier, ← algebraMap_smul (𝔸f E), -dotProduct]
      using (by simpa only [finHeisOp, _root_.smul_apply, @map_smul _ ℂ, U, e, hL.2 ⟨y, s, rfl⟩,
      smul_smul, thetaShift_of_mem hv, thetaShift_of_mem (thetaShift_mem_of_dual a.2 hv),
      H.thetaShift_thetaShift] using congr(B.thetaShift (-a) (T $(V.finHeisOp_comm
      (finiteImage (γ a)) (finiteImage (star d • y)) V.vacElem))).symm :))
  obtain ⟨⟨F, hF, rfl⟩, c⟩ := thetaSpace_le_of_thetaShift_mem hv ‹_› (.map ..) (⟨_,
    rho_finVec_mem_finitePart _ vacElem_mem_finitePart,
    e ⟨·, ·⟩ ▸ U ..⟩) (mem_thetaSpace_iff_normalizedShift.2 ⟨hS, by simpa [hL, -funext_iff]⟩),
    index_range_nsmul B.dualLattice N
  let R := (@nsmulAddMonoidHom B.dualLattice _ N).range
  have := fintypeOfIndexNeZero (c ▸ pow_ne_zero _ h0)
  exact ⟨F, hF, rfl, _ ⧸ R, _, _, (k ·.out), by
    simpa [ZLattice.rank ℝ, index, mul_comm] using c, fun ℓ ↦ inj (by
    simp [-finiteImage, mul_right_comm _ (ℓ _)]
    simpa only [← smul_eq_mul, ← map_smul, ← map_sum] using
      fun z ↦ congr(ℓ $(inj (by simpa [-finiteImage, ← map_neg, U, ← e, Pi.neg_def, neg_div',
      mul_assoc] using (sum_shift_mul_shift (_ ⧸ R) (·.out) (⟨.addLeft ·,
      fun _ ↦ (QuotientAddGroup.eq_iff_sub_mem.1 (by simp) : _ ∈ R).elim fun a h ↦
      h ▸ hL.2 ⟨d • γ a, by simp [k, -finiteImage, ← e a, smul_smul, mul_comm _ d, hN]⟩⟩) ⟨_,
      hv⟩ ⟨T F, by simpa [mem_thetaSpace_iff_normalizedShift, *, -funext_iff]⟩ z)))))⟩
end
