import Lib.Weil.ZeroTerm
import Lib.GaloisRep.Landherr

section
/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: The mixed Schrödinger model function of a vector is continuous and integrable. -/

open MeasureTheory Equiv

namespace Space.Splitting

variable {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s n₀ p} [Fintype n₀] [Fintype p]
  {s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p)

@[fun_prop] lemma continuous_mixedTerm f :
  Continuous (D.mixedTerm · f) := by simp [mixedTerm]; fun_prop

/-- For a splitting of V over V₀ with p hyperbolic planes and f in 𝒮(V), the 𝒮(V₀)-valued
function x ↦ f[x] of the mixed model is integrable on 𝔸^p. -/
@[fun_prop] lemma integrable_mixedTerm f : Integrable (D.mixedTerm · f) := ⟨by fun_prop,
  (lintegral_addOrbitMeasure_lintegral (H :=
  _root_.ratVectors E p) (continuous_mixedTerm ..).enorm.measurable).ge.trans_lt
  (IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal _ ⟨_, fun x ↦ by
  erw [lintegral_count, ← (ofInjective _ (@toAdele E ..).injective.comp_left).tsum_eq]
  simpa [← ofReal_norm] using! D.tsum_enorm_mixedTerm_le.choose_spec (ϱ _ (D.lAdelic.mulVec x) f)⟩)⟩
end Space.Splitting
end

section
/-! Known result: the Schrödinger and mixed models of the Weil representation and the action of
parabolic subgroups. This file treats adelic unitary groups over a CM field and uses vectors with
integrable coefficients instead of Schwartz functions. The representation is normalised by its
vacuum coefficient, so the parabolic and split-place formulas are proved rather than taken as the
definition. Source: C. Mœglin, M.-F. Vignéras, J.-L. Waldspurger, Correspondances de Howe sur un
corps p-adique, LNM 1291, 1987; S. Kudla, Splitting metaplectic covers of dual reductive pairs,
Israel J. Math. 87 (1994) 361–401; A. Weil, Acta Math. 111 (1964) n° 16–19, 41.

This file: Parabolic subgroup acts on the zero term by an explicit character of the determinant. -/

open Circle Complex ComplexOrder Finset G MatMul Matrix MeasureTheory WeilData Heisenberg.IsVacuum

variable {E : Type*} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s n₀ p} [Fintype n₀]
  [Fintype p] {s₀} {V : Space E n s} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) {g} (g₀ :
  G E s₀) (hi : D.iCoord * (g.mat * D.iAdelic) = g₀.mat) (a : GL p (𝔸 E)) (hk : D.ActsOnFrame g a)

namespace Space.Splitting

attribute [local simp ←] coe_inv_eq_conj conjTranspose_mul mixedTerm_zero

attribute [local simp] star_eq_conjTranspose levi_mul_iAdelic levi_mul_kAdelic levi_mul_lAdelic
  radicalElt_mul_iAdelic ω_ϱ

/-- For a in GL_p(𝔸) and x the point of the space `hypSpace` of p hyperbolic planes, some g₁ in
the adelic unitary group has matrix x⁻¹ diag(a*⁻¹, a) x, and Δ(g₁)υ(det a) is a nonnegative
real number. -/
lemma exists_hyp_levi_multiplier_nonneg : ∃ g₁ : G E (hypSigns p), 0 ≤ weilMultiplier g₁ * υ.1
  a.det ∧ g₁.mat = (hypSpace E p).x⁻¹.1 * fromBlocks a⁻¹.1ᴴ 0 0 a.1 * (hypSpace E p).x := by
  refine ⟨(hypSpace ..).toRatCoords.symm ⟨blockGL (star a⁻¹, a), by simp [U]⟩, ?_, ?m⟩
  erw [upsilon_eq_prod_mul_of_v_eq (a.map (.snd ..)).det (by simp [a.map_det]), mul_mul_mul_comm,
    ← prod_mul_distrib]
  refine mul_nonneg (b := glMultiplier (.map _ _) * _) (prod_nonneg fun w ↦ ?_) ?_
  erw [realMultiplier, ← principalMinor_conjTranspose, principalMinor, ← det_reindex_self
    (.trans (.subtypeEquivRight (by simp)) .sumIsRight), congr((($(?m)).map _)ᴴ.toBlocks₂₂.det)]
  simp [-coe_units_inv, ← evalInf_apply, RingHom.map_det]
  repeat rw [(rfl : .map _ _ = (_ : ℂ) • fromBlocks 1 _ _ 1)]
  simp [fromBlocks_smul, ← smul_add, ← det_mul, field, div_nonneg, conjTranspose_map
    (evalInf w) (by tauto), (PosSemidef.one.add (posSemidef_conjTranspose_mul_self _)).det_nonneg]
  simp
  rw [glMultiplier_mul_of_mem _ (inv_mem ?hx) ?hx, glMultiplier_fromBlocks _ _ (.refl _),
    glMultiplier_star_inv_mul]
  simp [chiFin, chiAdelic, field]
  exacts [fromBlocks_map .., mem_intGL.2 (isOrthoIntegral_hypSpace.imp (·.2) (·.2)), rfl]

lemma integrable_dataInner_mixedTerm f f' : Integrable fun x ↦
  V₀.dataInner (D.mixedTerm x f) (D.mixedTerm x f') := .mono'
  (by simp; fun_prop) (by fun_prop) (.of_forall fun _ ↦ (V₀.dataInner ∘SL D.zeroTerm).le_opNorm₂ ..)

lemma integral_dataInner_mixedTerm : ∃ C, ∀ f f', ∫ x, V₀.dataInner (D.mixedTerm x f)
  (D.mixedTerm x f') = C * V.dataInner f f' := ⟨_, integral_form_eq_mul_modelInner (fun _ ↦
  V₀.dataInner.bilinearComp ..) D.integrable_dataInner_mixedTerm fun _ _ _ ↦
  .trans (congr(∫ x, V₀.dataInner $(isMixedLaw_mixedTerm ..) $(isMixedLaw_mixedTerm ..)).trans
  (by simp [← mul_assoc]; rfl)) (integral_add_right_eq_self ..)⟩

include hi hk in
lemma exists_zeroTerm_omega_eq_smul : ∃ c : ℂ, ∀ f, D.zeroTerm (V.ω g f) =
  c • V₀.ω g₀ (D.zeroTerm f) := by
  obtain ⟨r, k, h, -⟩ :=
    D.isMixedLaw_comp_rho (V₀.ω g₀⁻¹ ∘L D.zeroTerm ∘L V.ω g) (by aesop) (by simp [*, ← mat_mul,
    ← D.lCoord.mul_assoc, D.lCoord_mul_mat hk]), D.exists_isAdapted_and_frame_eq 1
  obtain ⟨⟨c', ⟨⟩⟩, c, hc⟩ := h.mixedTerm_omega_vacElem, h.exists_omega_vacElem_of_isMixedLaw r
  exact ⟨_, by simpa [rep_apply_apply] using (congr(V₀.ω g₀ <| $(V.ext_of_vacElem k (T' := (c /
    c') • _) fun _ ↦ (V.ω_ϱ .. ▸ r 0 .. :).trans (by simp [↓hc, *, smul_smul]; field_simp)) ·))⟩

/-- If g is the Levi element of a splitting attached to a in GL_p(𝔸) and g₀ in the group of V₀,
then ev(ω(g)f) = χ_𝔸(det a)⁻¹ ω(g₀) ev(f) for all f in 𝒮(V), where χ_𝔸 = υ|·|^(−½), |·| the
idele norm. -/
lemma zeroTerm_omega_levi f : D.zeroTerm (V.ω (D.levi (a, g₀)) f) =
  (chiAdelic a.det)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  set g := D.levi _
  obtain ⟨⟨c, hc⟩, ⟨_, hC⟩, ⟨g₁, ⟨L⟩⟩, k, hg, e, hs, h⟩ := D.exists_zeroTerm_omega_eq_smul g₀
    (by simp) a (D.levi_mul_kAdelic a g₀), D.integral_dataInner_mixedTerm,
    exists_hyp_levi_multiplier_nonneg a, D.exists_isAdapted_and_frame_eq 1
  have : weilMultiplier (k⁻¹ * g * k) = weilMultiplier g₁ * weilMultiplier g₀ :=
    weilMultiplier_fromBlocks hs (.trans (by
    rw [← submatrix_one_equiv e, ← mat_one, ← inv_mul_cancel k]
    simp [↓mat_mul, submatrix_mul _ _ _ id, ← h]
    simp [*, g, frameAt, ← Matrix.mul_assoc]) (one_mul _))
  cases hg.mixedTerm_omega_vacElem; set u := V.ω k _
  obtain ⟨P, e₁⟩ := integral_pos_of_integrable_nonneg_nonzero (x := 0) (by fun_prop)
    (D.integrable_dataInner_mixedTerm u u).norm (by simp_intro _) (by simp [*, vacuumFn]),
    (hC u (V.ω g u)).symm, this ▸ V.dataInner_omega_of_vacElem _, (hC u u).symm,
    V.dataInner_omega g u u ▸ hC .., left_ne_zero_of_mul_eq_one
    (conj_delta_mul_weilRep_vacElem adelicAction (k⁻¹ * g * k)), volume_map_mulVec_adele (star a) ▸
    (integral_map (by fun_prop) ((cont (adelicHeis E 1)).norm.pow 4).aestronglyMeasurable).symm
  simp [by simpa [↓ω_ϱ, ↓mulVec_mulVec] using fun x ↦ hc (V.ϱ (D.lAdelic *ᵥ a.1ᴴ *ᵥ x) u), u, g,
    ↓dataInner_omega, dataInner_omega_left, *, chiAdelic] at *
  ring_nf at *; simp [mul_assoc, *] at *; norm_cast at *
  simp [*, field, mul_conj] at *
  simp [by simpa [field, c.norm_def, *] using norm_of_nonneg' (div_nonneg
    (pos_of_mul_pos_left (e₁.le.trans_lt' (mod_cast P)) (by positivity)).le (star_nonneg_iff.2 L))]

/-- If gk = ka with a in GL_p(𝔸) and gι = ιg₀ + kc with g₀ in the adelic group of V₀, then
ev(ω(g)f) = υ(det a)⁻¹ |det a|^{1/2} ω(g₀) ev(f) for all f.

Known result: Schrödinger and mixed models of the Weil representation; action of parabolic
subgroups. -/
lemma zeroTerm_omega (hi : D.iCoord * (g.mat * D.iAdelic) = g₀.mat) {a} (hk : D.ActsOnFrame g a) d
  (h : a.det = d.1) f : D.zeroTerm (V.ω g f) = (chiAdelic d)⁻¹ • V₀.ω g₀ (D.zeroTerm f) := by
  obtain ⟨c, b, t, _, rfl, rfl, e⟩ := D.exists_eq_radicalElt_mul_levi hk
  choose d _ using (D.exists_zeroTerm_omega_eq_smul 1 (by simp) 1 <| D.radicalElt_mul_kAdelic c ·)
  obtain ⟨⟨⟩, ⟨⟩, _, _, e⟩ := t.det.ext h, ext_mat (hi ▸ e), D.exists_levi_mul_radicalElt_eq c b
  rw [← zeroTerm_omega_levi, ← mul_inv_cancel_left (_ * _) (levi _ _)]; nth_rw 3 [e]
  simp [↓map_mul, *, -mixedTerm_zero, zeroTerm_omega_levi]; module
end Space.Splitting
end

section
/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Standard polarisation of the hyperbolic space as a splitting. -/

/-- The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k
the last p basis vectors. -/
noncomputable def hyperbolicSplitting E p [Field E] [CMType E] [WeilData E] [Fintype p] :
  (hypSpace E p).Splitting (stdSpace E Empty)
  p := by use .fromRows 0 1, .fromRows 1 0, 0 <;> first | (ext ⟨⟩; done) | simp +arith
end

section
/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa decomposition
(known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

This file: Zero term along an isotropic subspace taken in stages; independent of the frame. Witt
decomposition: every isotropic frame splits off hyperbolic planes plus a framed complement. Adapted
splittings; the standard splitting of a space plus hyperbolic planes. -/

open Classical ComplexOrder Fintype MatMul Matrix Sgn Space Splitting

attribute [local simp] Splitting.comp Splitting.zeroTerm_apply iAdelic kAdelic Space.ratMap
  funext_iff

variable {E n n₀ p n₁ q : Type*} [Field E] [CMType E] [Fintype n] {s : n → ℤˣ} [Fintype n₀]
  {s₀ : n₀ → ℤˣ} {V : Space E n s} {V₀ : Space E n₀ s₀} [Fintype n₁]
  {s₁ : n₁ → ℤˣ} {V₁ : Space E n₁ s₁}

variable (V V₀)

@[simp] lemma Space.ratMap_mul_toAdele i (k : Matrix n₀ p E) :
    V.ratMap V₀ i * (V₀.x⁻¹.1 * k.map toAdele) = V.x⁻¹.1 * (i * k).map toAdele := by simp

lemma Space.ratMap_mul_ratMap i k : V.ratMap V₀ i * V₀.ratMap V₁ k = V.ratMap V₁ (i * k) := by simp

lemma Space.map_mulVec_mem_ratVectors [Fintype p] [WeilData E] c : ∀ b ∈ _root_.ratVectors E p,
  .map c toAdele *ᵥ b ∈ _root_.ratVectors E q | _, ⟨a, rfl⟩ => ⟨_, funext (toAdele.map_mulVec c a)⟩

variable [Fintype p] [Fintype q]

variable {V V₀} [WeilData E] (D : V.Splitting V₀ p) (D' : V₀.Splitting V₁ q)

omit [WeilData E] in
lemma Space.Splitting.comp_kAdelic : (D.comp D').kAdelic =
  D.kAdelic.fromCols (D.iAdelic * D'.kAdelic) := by simp

/-- Zero terms can be taken in stages: for splittings of V over V₀ and of V₀ over V₁, the zero
term of the composite splitting is the zero term of the second applied after that of the
first. -/
lemma Space.Splitting.zeroTerm_comp f : (D.comp D').zeroTerm f = D'.zeroTerm (D.zeroTerm f) := by
  ext; rw [zeroTerm_apply, ← quotMean_quotMean (_root_.ratVectors ..) _ (_root_.ratVectors ..)
    (.mk' ..) (Homeomorph.sumArrowHomeomorphProdArrow.3.comp continuous_swap) _ (⟨(_, _),
    Sum.elim_comp_inl_inr ·⟩)] <;> simp_all [↓isContPeriodic_along_k, mem_ratVectors]; ac_nf

/-- Two splittings of V over V₀, with isotropic frames k and k′ (of possibly different index
sets), have the same zero-term map 𝒮(V) → 𝒮(V₀) if k*Jk′ = 0 and their embeddings of V₀
coincide. -/
lemma Space.Splitting.zeroTerm_congr (D' : V.Splitting _ q) (hk : D.kᴴ * V.J * D'.k = 0) (hi :
  D'.i = D.i) : D'.zeroTerm = D.zeroTerm :=
  by have := V.gram_at_point_eq_map D.k D'.k; rcases congr($D.sum_frame_mul_coord_eq_one *
  D'.kAdelic), congr($D'.sum_frame_mul_coord_eq_one * D.kAdelic), D'.coord_mul_frame,
  D.coord_mul_frame, congr($thisᴴ); ext; rw [zeroTerm_apply, ← quotMean_comp _ (D'.kCoord *
  D.kAdelic).toLin' _ (V.gram_at_point_eq_map .. ▸ map_mulVec_mem_ratVectors _) (⟨D.kCoord *ᵥ
  D'.kAdelic *ᵥ ·, _⟩)] <;> simp_all [iCoord, lCoord, ↓conjTranspose_mul, ↓isContPeriodic_along_k]

variable {E : Type} [Field.{0} E] [CMType E] [WeilData E] {n : Type} (p : Type) [Fintype n]
  [Fintype.{0} p] {s : n → ℤˣ} (V : Space E n s)

/-- Every q×p matrix k over E with a left inverse and k*Jk = 0, J the Gram matrix of V, is the
isotropic frame k of a splitting of V over some space V₀. -/
lemma Space.exists_splitting {s p} [Fintype.{0} p] (V : Space E q s) {k} (hk : HasLeftInv k)
    (h : kᴴ * V.J * k = 0) : ∃ m s₀ V₀ D, (D : V.Splitting (V₀ : Space E (Fin m) s₀) p).k = k := by
  let X := (V.x⁻¹.1 * k.map toAdele).map (evalInf ofNonempty)
  have hc ε : p ↪ s ⁻¹' {ε} := (Function.Embedding.truncOfCardLE (by
    trans X.rank; simpa [X, ← Matrix.map_mul, hk.choose_spec] using
      ((hk.choose.map toAdele * V.x.1).map (evalInf ofNonempty)).rank_mul_le_right X
    grw [← rank_conjTranspose_mul_self, show Xᴴ * X = ε • Xᴴ * (signMatrix s + ↑ε) * X by
      fin_cases ε <;> simpa [-conjTranspose_map_toAdele, X, h, stdForm] using!
        congr($(V.gram_at_point_eq_map k k).map (evalInf _)), rank_mul_le_left, rank_mul_le_right]
    erw [diagonal_add, rank_diagonal]
    simp_all [↓card_subtype_mono, LE.le, not_imp_comm])).out
  let e := ((((hc 1).sumMap (hc (-1))).trans (.sumSet (.preimage s (by simp)))
    ).toEquivRange.sumCongr (equivFin _).symm).trans (.sumCompl _)
  have D := splittingOfGram _ ((Equiv.symm_apply_eq _).2 (V.landherr
    ((hypSum p (signedSpace E (s ∘ e ∘ .inr))).reindex e (by
    simp [↓e.comp_symm_eq, funext_iff, e]
    exact ⟨fun a ↦ (hc 1 a).2.symm, fun b ↦ (hc (-1) b).2.symm⟩))).choose_spec)
    (by simp +arith [← card_congr e])
  exact ⟨_, _, _, splittingOfGram _ ((U.gram_invariant ..).trans D.gram_eq_hypSum) D.card_eq,
    (V.witt ⟨_, D.gram_lk⟩ hk (h ▸ D.gram_kk)).choose_spec⟩

/-- The splitting is adapted: the adelic frame (l, k, ι) has orthonormal columns at every
infinite place and integral entries at every finite place. -/
class IsBaseAdapted {m p : Type} [Fintype n] [Fintype m] [Fintype p] {s t} {V' : Space E m t} {V :
  Space E n s} (D : V'.Splitting V p) where
  isOrthoIntegral : IsOrthoIntegral ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic)

/-- The tautological splitting over V of the sum of p hyperbolic planes and V. -/
noncomputable def removePlanes : (hypSum p V).Splitting V p := by
  use (fromRows 0 1).fromRows 0, (fromRows 1 0).fromRows 0, fromRows 0 1 <;> simp +arith [hypSum]

instance : IsBaseAdapted (removePlanes p V) := ⟨(isOrthoIntegral_hypSpace.2.block_diag
  .one).of_eq_submatrix_mul id .one (by simp [entrywise, lAdelic,
  kAdelic, iAdelic, Space.ratMap, removePlanes, hypSum, sum, blockGL])⟩
end
