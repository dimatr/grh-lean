import New.Filling.FinitePlaceDensity
import New.Filling.NearTerms
import Lib.Weil.RealConvolution
import New.Filling.TopFloor
import New.Filling.AmplitudeSums

-- part: New.Filling.GlobalSieve
section
/-! Positive kernels and a sieve losing almost nothing. Systems of positive kernels, of one kind at
real and finite places and with each kernel the integral of the next over a common last entry,
multiply over places, and one-sided Poisson summation, entry by entry, bounds the sum over rational
points losing only a factor near 1, as the second moment's main term requires. Inductive Fourier
transforms of Kloosterman integrals and spectral large sieves losing a constant or X^ε are known.
Related work: Jacquet, Smooth transfer of Kloosterman integrals, 2003; Jacquet, Kloosterman
identities over a quadratic extension, 2004; Blomer–Buttcane, GL(3) Kloosterman sums and the
spectral large sieve, 2015; Deshouillers–Iwaniec, Kloosterman sums and Fourier coefficients of cusp
forms, 1982.

This file: Adelic sieve: one-sided Poisson summation per pivot, frequency sum bound, final sieve
inequality. -/

namespace Filling

open NumberField ENNReal Finset Fintype MeasureTheory Measure Real AddSubgroup Matrix ComplexOrder
  SemilocalField Complex
variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) (T : Finset (FinPlace E))

/-- The character x ↦ ψ_f(−x/ϖ) of the finite adeles, restricted to ∏_{w∈T} E_w by extending
elements by zero off T. -/
noncomputable def charOnPlaces : AddChar (LocProd T) ℂ :=
  S.selfDualChar.compAddMonoidHom (adeleOfLocal T)

lemma charOnPlaces_evalPlaces {x} (h : x ∈ integralOff T) : S.charOnPlaces T (evalPlaces T x) =
  S.selfDualChar x := .symm (eq_of_div_eq_one (S.selfDualChar.map_sub_eq_div .. ▸
  S.selfDualChar_eq_one_of_mem _ ((sub_adeleOfLocal_mem_iff T).2 h)))

/-- The bound [ξ]^((k − n⁷)/2) (den ξ)⁻⁶ b^(n⁹f) at a frequency ξ at the places of T, with n = ϱ
+ 1, [ξ] = [R : ξR] the generalised index. -/
noncomputable def frequencyGain (ξ : LocProd T) := √(genIndex ξ) ^ (𝔰.k - 𝔰.n ^ 7) / denomIndex O
  ξ ^ 6 * S.b ^ (𝔰.n ^ 9 * numInfPlaces E)

/-- The element t of E read as the point ((l_v v(t))_v, t) of ℂ^f × ∏_{w ∈ T} E_w, for scales
l_v at the infinite places. -/
noncomputable def ratPoint (l : _ → ℂ) t := (fun v ↦ l v * Φ v t, ratToPlaces T t)

attribute [local simp] frameScaleSq ratPoint unitOrOne intVectors funext_iff wave IsUnit.map
  prod_eq_zero_iff entrywise pi_pos Prod.isUnit_iff Pi.isUnit_iff toAdele Units.val_inj padTuple
  selfDualChar stdAddChar mul_mem mul_sum

/-- Assume B ≥ 1, |c_v|⁻¹ ≤ |x_v| ≤ B. Over any finite set of nonzero T-integers y, the sum of
[y]_T^(k/2) (den y)⁻⁶ ∏_v ℓ_k(1/|c_v y|_v), ℓ_k(r) = r^k min(1,r)⁶, is at most (b rd_E)^(3f) ∏_v
|x_v|^k (bB²)³. -/
lemma sum_frequencies_le [WeilData E] [T.StarStable]
    B k X (c : _ → ℂ) (x : _ → ℝ) (hB : 1 ≤ B) (hx : ∀ v, ‖c v‖⁻¹ ≤ |x v| ∧
  |x v| ≤ B) (h : ∀ y ∈ X, y ≠ 0 ∧ y ∈ ratIntegralOff T) : ∑ y ∈ X, (∏ v, dampedPower k ‖c v * Φ v
  y‖⁻¹) * (√(genIndex (ratToPlaces T y)) ^ k / denomIndex O (ratToPlaces T y) ^ 6) ≤
  (∏ v, |x v| ^ k * (S.b * B ^ 2) ^ 3) * (S.b * rootDiscr E) ^ (numInfPlaces E * 3) := by
  obtain ⟨Z, _, b⟩ := by simpa using tsum_sublatticeDisc_inv_le (1 : Gf E (Fin 2)) 1,
    rootDiscr_pos E, S.thousand_le_b
  simp_rw [dampedPower, norm_mul, mul_inv]; grw [← b, ← show 200 * (numInfPlaces E * 2) ≤ S.b by
    bound [S.f_le_b], ← ofReal_le_ofReal_iff, ENNReal.ofReal_mul, ← Z, ← ENNReal.sum_le_tsum
    (X.image (colSpan !![1; ·])), sum_image fun y _ u _ e ↦ (e.le ⟨1, rfl⟩).elim (by
    simp +contextual), mul_sum, ofReal_sum_of_nonneg, sum_le_sum fun y hy ↦ ?_]
  obtain ⟨⟨a, e, p, -⟩, u, w, f⟩ := exists_preimageLattice_eq_colLattice (m := finAdeleMat !![1; y])
    ⟨!![1, 0], by simp [vecMul]⟩, (denomIndex_ne_zero T _).pos, h y hy, show 1 = !![1; y].rank by
    simp [rank_eq_finrank_span_cols, finrank_span_eq_card]
  have : 0 < genIndex a.1.det := genIndex_pos a.det
  obtain ⟨D, _, -⟩ := sublatticeDisc_mul_index_sq_le (one_mul 1) _ !![,,] f le_rfl a (K := ⊤) (D :=
    ((∏ v, (1 + ‖Φ v y‖ ^ 2)) * genIndex a.1.det) ^ 2)
    (by erw [det_unique, genIndex_algebraMap]; simp [abs_norm_eq_prod_norm_sq,
    conj_mul', mul_pow, ← prod_pow]; norm_cast; simp) (by positivity) (.mul .one p) (by simp)
  simp [submoduleIndex, -det_unique] at D; grw [ite_eq_left (by tauto), le_of_sq_le_sq D,
    ← ENNReal.ofReal_mul, sqrt_genIndex_le_prod_norm T w,
    ← pow_le_pow_right₀ (mod_cast u) (by simp : 3 ≤ 6), ← (?_ : genIndex a.1.det ≤ denomIndex
    ..), fun v ↦ (?_ : min 1 (‖c v‖⁻¹ * _) ^ 6 ≤ (1000 * B ^ 2 / (1 + ‖Φ v y‖ ^ 2)) ^ 3), (hx _).1]
  any_goals intros; positivity
  · gcongr 1; simp [field, prod_pow, div_pow, mul_pow, *]
  · grw [pow_mul _ 2 3, (hx v).1, (hx v).2, min_def]; gcongr
    clear * - w hB; split <;> simp [*, field] at * <;> nlinarith [norm_nonneg (Φ v y)]
  grw [← submoduleIndex_colLattice_div, div_nat_le_self_of_nonnneg (by simp), ← e, Nat.cast_le]
  exact Nat.le_of_dvd u ((relIndex_dvd_of_le_left _ fun z ↦ by simp_all [preimageLattice, mem_Ô_iff
    T, -e]).trans (dvd_of_eq ((inf_relIndex_right ..).trans ((relIndex_comap _ (.mk' (evalPlaces
    T <| · 0) (by simp)) _).trans
    (congrArg _ (by ext; simp [locProd_O_eq_map_evalPlaces, Fin.exists_fin_succ_pi]))))))

variable [S.IsAdmissible] {A : Finset Eˣ} (hA : ∀ t ∈ A, ↑t ∈ ratIntegralOff T ∧
  ↑t⁻¹ ∈ ratIntegralOff T) (hg : (↑S.g)⁻¹ ∈ ratIntegralOff T)
include hA hg

/-- Iterated Poisson summation for a system on ℂ^f × ∏_T E_w, entries in finite sets V ⊂ A of
T-units, c_a = vol(Ô)∏_v l(v,a)⁻², l = `Filling.frameScaleSq`: if ε bounds sums of β over
nonzero T-integral frequencies and (∑_p Λ_i(p))² ≤ Γ∏_{a<i}c_a, then
Re ∑_{t∈V,p,q} J_{i+1} ≤ ∏_{a≤i}c_a·(En + (2i+1)Γε).

Positive kernels and a sieve losing almost nothing. -/
lemma one_sided_poisson {n J En Λ β} (K :
  SieveSystem (.map (unitOrOne ∘ ·) unitOrOne) (.map ((·⁻¹.1) ∘ ·) (ratToPlaces T
  S.g⁻¹ * ·⁻¹.1)) n J (fun x ↦ (∏ v, wave (x.1 v)) * S.charOnPlaces T x.2) En Λ β) {Γ ε} (hP : ∀ a
  (c : _ → ℂ), (∀ v, ‖c v‖⁻¹ ≤ |S.kappa v| / S.g) → ∀ X, (∀ y ∈ X, y ≠ 0 ∧ y ∈ ratIntegralOff T) →
  ∑ y ∈ X, β (ratPoint T (fun v ↦ c v / S.frameScaleSq v a) y) ≤ ε) (hε : 0 ≤ ε) (hΛ : ∀ i p, 0 ≤
  Λ i p) : let hd i (p : Fin i → A) t a := .map (unitOrOne ∘ ·) unitOrOne (ratPoint T
    (S.frameScaleSq · a) (padTuple (p · |>.1) t a).1)
  let c a := volÔ E / ∏ v, S.frameScaleSq v a ^ 2
  (∀ i ≤ n, (∑ p, Λ i (hd i p 1)) ^ 2 ≤ Γ * ∏ a ∈ range i, c a) → ∀ i ≤ n, ∀ V ⊆ A,
  (∑ t ∈ V, ∑ p, ∑ q, J (i + 1) (hd i p t) (hd i q t)).re ≤
    (∏ a ∈ range (i + 1), c a) * (En + (2 * i + 1) * Γ * ε) := by
  intro hd c hΓ
  refine Nat.strongRec fun i ih hi V hV ↦ ?_
  have := K.step_sum hi (hd i · 1)
  extract_lets F at *
  obtain ⟨⟨N, L⟩, o, ⟨hF, e, hM⟩, c0, d⟩ := show 0 ≤ F ∧ _ from K.nonneg_and_lowerSemicontinuous hi
    _ fun _ _ ↦ dite_eq_left rfl, (isOpen_univ.prod (isOpen_integralOff T) : @IsOpen (𝔸 E) _
        _), this,
    (by positivity : 0 ≤ c i), LinearMap.det_pi (S.frameScaleSq · i • (1 : ℂ →ₗ[ℝ] ℂ))
  set U := _ ×ˢ _; let m (z : 𝔸 E) := (fun v ↦ S.frameScaleSq v i * z.1 v, evalPlaces T z.2)
  have P : MeasurePreserving m (volume.restrict U) (ENNReal.ofReal (c i) •
    volume) := by simpa [d, U, volume_eq_prod, ← prod_restrict, prod_smul_left, prod_smul_right,
    abs_prod, div_eq_mul_inv, c, mul_smul, -frameScaleSq] using!
    MeasurePreserving.prod ⟨by fun_prop, map_linearMap_addHaar_eq_smul_addHaar _
    (d.trans_ne (by simp))⟩ ⟨by fun_prop, map_evalPlaces_restrict_volume T⟩
  have I := U.indicator_nonneg fun x _ ↦ (N (m x)).1
  refine (le_of_eq_of_le ?_ (IsDualFamily.sum_le_of_fourier ((integrable_indicator_iff
    o.measurableSet).2 (P.integrable_comp_of_integrable hF.re.smul_measure_nnreal)) I
    (V.map ⟨(⟨_, ·.1, rfl⟩), fun _ ↦ by simp⟩) (forall_mem_map.2 fun t h ↦ .of_frequently fun y k ↦
    (ite_eq_left ⟨trivial, (hA t (hV h)).1⟩).trans_le ((ofReal_le_ofReal_iff
    (k.exists.elim (I · |>.trans))).1 (((L _ fun _ ↦ continuousAt_const.update _
    (.prodMap (.piMap fun v ↦ continuousAt_unitOrOne (.mk0 _ (by simp [m])))
    (continuousAt_unitOrOne (t.map (ratToPlaces T).1)))).comp (g := m) (by fun_prop)).frequently _
    (k.mp (.mono (o.eventually_mem ⟨trivial, (hA t (hV h)).1⟩) (by simp +contextual [F,
    ofReal_le_ofReal])))))) ((reindex_equiv (Equiv.divRight₀ _ S.varpi_ne_zero).finsetCongr).1.2
    fun Y ↦ ?_))).trans (?_ : c i * (‖∫ x, F x‖ + ε * (∑ p, Λ i (hd i p 1)) ^ 2) ≤ _)
  simp +contextual [m, U, F, ← Subring.mem_comap, hA _ (hV _)]
  congr! <;> simp +contextual [hd, ↓Function.eq_update_iff]
  · erw [sum_map]
    grw [Y.insert_erase_subset 0, sum_insert (by simp),
      ← sum_filter_of_ne (p := (· ∈ ratIntegralOff T)), ← hP i (2 * π * .I / Φ · S.ϖ)
      (by simp [abs_kappa_eq, field, abs_of_pos]), mul_add, sum_mul, mul_sum]
    · gcongr with y h; any_goals simp at h; grw [← hM _ (by simp [h])]
      all_goals grw [← norm_smul_of_nonneg c0, ← toReal_ofReal c0, ← integral_smul_measure,
        ← P.hasLaw.integral_comp (by cases hF; simp [charOnPlaces, c]; fun_prop),
        ← integral_indicator o.measurableSet]; simp [m, U, ← eq_re_of_ofReal_le (N _),
        Set.indicator, apply_ite, ↓sub_conj, ← Complex.exp_sum, sum_mul, fourierChar_apply,
        div_eq_mul_inv, -neg_sub, -frameScaleSq]
      congr! 8; field; erw [S.charOnPlaces_evalPlaces T (mul_mem h.2 ‹_›)]; simp; ac_rfl
    simp +contextual
    refine fun y _ n ↦ (sub_adeleOfLocal_mem_iff T).1 ((S.forall_selfDualChar_mul_eq_one_iff _).1
      fun ⟨r, hr⟩ ↦ (mul_eq_right₀ (norm_ne_zero_iff.1 n)).1
      (.trans ?_ (integral_add_left_eq_self _ (0, r - adeleOfLocal T (evalPlaces T r)))))
    rw [← integral_const_mul]; congr with; simp [Set.indicator, U, m, add_mem_cancel_left, sub_mem,
      (mem_Ô_iff T).1 hr, mul_add, AddChar.map_add_eq_mul, div_eq_mul_inv, -frameScaleSq]
    simp_rw [adeleOfLocal_evalPlaces]; ring_nf!
  grw [← re_eq_norm.2 (integral_nonneg N), e, hΓ, prod_range_succ_comm, mul_assoc]
  gcongr; cases i <;> simp
  grw [re_le_norm, K.norm_bot_le, mul_comm]
  linear_combination (norm := ring_nf) ih _ .refl (by omega) A le_rfl + ε * hΓ _ hi
  simp [↓sum_mul, reindex_equiv (Fin.snocEquiv _), sum_prod_type, Fin.snocEquiv, sq, ←
    sum_add_distrib, ← A.sum_attach, show ∀ i p t, hd _ (Fin.snoc p t) 1 = hd i p t by
    grind [padTuple, Fin.snoc, Fin.castLT]]
  gcongr with t
  grw [sum_eq_add_sum_sdiff_singleton_of_mem ‹_›, ← A.attach.sdiff_subset]; gcongr with v
  let y := (S.g : E)⁻¹ * (t.1⁻¹ - v.1⁻¹)
  have : y ≠ 0 := by simp [y]; grind
  grw [re_le_norm, add_comm, K.off_diagonal, ← hP ‹_› S.g (by grw [← one_le_abs_kappa]; simp)
    {y} (by grind [mul_mem, sub_mem])]
  any_goals rw [show _ - _ = ratPoint T (S.g / S.frameScaleSq · ‹_›) y by
    simp [hd, y, field, ↓map_sub, ↓map_mul, ↓map_units_inv]]
  any_goals simp [*]
  all_goals grind [Finset.sum_nonneg, mul_nonneg]

/-- The sieve, under `Filling.IsAdmissible`: for the forms J_v of the Bessel systems, a system J' at
T (bounds e, `finHeadWeight`, `Filling.frequencyGain`), finite sets U ⊂ A of T-units, g⁻¹ a
T-integer: Re ∑_{t∈U, p,q∈A^ϱ} J'∏J_v ≤ vol(Ô)^(ϱ+1)∏l(v,i)⁻²·(e∏_v((1+b⁻¹⁰)/deg_v) +
b^(−6kf−10)/deg).

Positive kernels and a sieve losing almost nothing. -/
lemma sieve [WeilData E] [T.StarStable]
    {J' e U} (h' : SieveSystem unitOrOne (ratToPlaces T S.g⁻¹ * ·⁻¹.1) 𝔰.ϱ J'
  (S.charOnPlaces T) e (finHeadWeight (𝔰.n ^ 6)) (S.frequencyGain T)) (hU : U ⊆ A) :
  let x v (p : Fin 𝔰.ϱ → A) t i := unitOrOne (S.frameScaleSq v i * Φ v (padTuple (p · |>.1) t i).1)
  let y p t := Units.map (ratToPlaces T) ∘ padTuple (p · |>.1) t
  (∑ t ∈ U, ∑ p, ∑ q, (∏ v, (S.besselSys v).bandLimit 𝔰.n (x v p t) (x v q t)) * J' 𝔰.n (y p t) (y q
  t)).re ≤ (∏ i ∈ range 𝔰.n, volÔ E / ∏ v, S.frameScaleSq v i ^ 2) * ((∏ v, (1 + S.b⁻¹ ^ 10) /
    (S.besselSys v).deg) * e + S.besselDegree⁻¹ / S.b ^ (6 * 𝔰.k * numInfPlaces E + 10)) := by
  obtain ⟨b, r, _, N, K, Z, h, θ⟩ := S.one_le_b, rootDiscr_pos E, (by simp : S.g ≠ 0).pos,
    S.N_prime.pos, S.one_le_abs_kappa, S.sum_frequencies_le T, (S.besselSys · |>.band_limits.1),
    (by simp [Shape.bandConst] : 0 < 𝔰.bandConst)
  unfold headWeight finHeadWeight dampedPower at *
  refine ((S.one_sided_poisson T hA hg (h'.pi h) (fun a c hc X hy ↦ by
    simp_rw [frequencyGain, ratPoint, prod_mul_distrib, mul_assoc, ← mul_sum, ← mul_assoc,
      ← sum_mul] at *
    grw [Z _ _ _ _ (S.kappa · ^ (2 * 𝔰.ϱ + 1) / (S.g * S.N)) _ (fun v ↦ ⟨by
      simp [div_eq_mul_inv]; grw [hc, Nat.sub_le] <;> simp [pow_succ, field, K], by
      grw [abs_div, abs_pow, abs_kappa_le, div_le_self] <;> norm_cast <;> bound⟩) hy]; bound)
    (by positivity) (by intros; positivity) (Γ := S.b ^ _) (fun i hi ↦ by
    let m (p : Fin i → A) j := ∏ a ∈ range j, (padTuple (p · |>.1) 1 a).1
    have L v a := (by grw [frameScaleSq, ← pow_abs_two_mul, Nat.sub_le, abs_kappa_le,
      div_le_self] <;> bound : S.frameScaleSq v a ≤ _)
    beta_reduce
    grw [(.trans ?_ ((prod_univ_sum ..).ge.trans (prod_le_prod₀ (by intros; positivity) fun (j :
      Fin i) _ ↦ Z (S.N ^ i) (𝔰.n ^ 6) (image (m · j.succ) univ) (∏ a ∈ range j.succ, S.frameScaleSq
      · a) (fun _ ↦ S.N ^ i) (by bound) (by simp; grw [← K]; simp; bound) (by simp [m, hA,
      prod_mem, apply_dite, dite_eq_iff, -Subring.mem_comap]))) : ∑ p, _ ≤ _),
      volÔ_eq, abs_of_pos (by bound), N_le, N_le, L, half_le_self, S.rd_le_b]
    simp [field, ← pow_mul, ← pow_add, mul_pow]; grw [hi]
    iterate 3 simp [r, -frameScaleSq, le_of_lt, prod_pos]
    grw [← image_subset_iff.2 fun p h ↦ mem_piFinset.2 fun _ ↦
      mem_image_of_mem _ h, sum_image fun p _ q _ e ↦ funext fun j ↦ ?_]
    · simp_rw [@prod_range _ _ i, @prod_comm (Fin i), ← prod_mul_distrib]
      gcongr 3 <;> simp [m]
      split <;> simp +contextual [denomIndex, relIndex_eq_one.2, IsConcreteLE.le_iff, div_nonneg, *]
    simpa [m, prod_range_succ] using congr($e j / $(@Fin.cases i (fun k ↦ m p k = m q k) (by bound)
      (congrFun e) j.castSucc))) 𝔰.ϱ le_rfl U hU).trans_eq' (by congr! <;> ext <;> simp)).trans ?_
  gcongr
  grw [← IsAdmissible.prod_band_le_inv_deg, show _ + 1 ≤ S.b by grw [← k_le_b, ← S.ϱ_le_k]; grind,
    S.rd_le_b]
  simp [abs_div, field, mul_pow, ← pow_mul, ← pow_add, ← pow_succ', mul_comm _ (∏ _, _), mul_assoc]
  gcongr; grind [Fintype.card_pos, mul_le_mul_right S.pow_le_k (numInfPlaces E)]
end Filling
end

-- part: New.Filling.GlobalToLocal
section
/-! Set-up for this proof: dictionaries between two encodings of the same objects.

Set-up for this proof: general results applied to the objects of this proof.

Part of: Phase sums are sharply dominated by local Bessel kernels (see New.Filling.Moments).

This file: Dictionary between global data and the places in T; phase sums as local integrals. -/

open Complex Subgroup Classical ComplexOrder ENNReal Function Matrix MeasureTheory SemilocalField
  Set Valued

namespace Filling

attribute [-instance] NumberField.IsCMField.of_isAbelianGalois

attribute [-simp] Filter.eventually_atTop splitGram_eq_ite_oppositeIndex coe_units_inv
  Nat.card_eq_fintype_card Nat.cast_mul
  Sum.forall Unitary.mul_star_self_of_mem inv_mul_cancel₀ star_ofNat

variable {E} [Field E] [CMType E] {𝔰} (S : Filling E 𝔰) (T : Finset (FinPlace E))

/-- The element x of the finite adelic unitary group and its inverse have entries integral at
every place outside T. -/
abbrev IsIntegralOff (x : S.GFin) := x.1 ∈ intGL _ (integralOff T)

/-- The sum of the amplitudes of uγu'⁻¹ over rational u, u' in 𝖴 with uγu'⁻¹ a term over (c, s,
c') and h_c⁻¹uh_c integral off T. -/
noncomputable def cosetAmplitude [Side] c s c' γ := ∑' x : besselU .. × besselU ..,
  ite (S.IsIntegralOff T (S.termPosition c c x.1.1) ∧
  x.1.1 * γ * x.2.1⁻¹ ∈ S.termsOver c s c') (S.amplitude c c' (x.1.1 * γ * x.2.1⁻¹)) 0

variable {𝔰 : Shape} (S : Filling E 𝔰) (T : Finset (FinPlace E)) [T.StarStable] (x :
  S.GFin)

/-- The homomorphism from the finite adelic unitary group (lattice basis) to the unitary group
over the product of the completions at T, taking components at T. -/
noncomputable def toPlaces :=
  U.map (evalPlaces T) (star_evalPlaces T · |>.symm) (S.map_splitGram_latMiddle _)

/-- F is a standard level on ∏_{w∈T} E_w (3ϱ+6 further hyperbolic pairs, orthonormal part of
size |κ| − 6ϱ − 13) with modulus g, and P has the character `Filling.charOnPlaces`. -/
class IsFillingLevel [P : IntegralPlace (LocProd T)] (F : Level (Fin (𝔰.k - (6 * 𝔰.ϱ + 13)))
  (S.latMiddle (LocProd T)) (𝔰.ϱ + 1 + 2 * 𝔰.ϱ + 5)) : Prop extends P.IsStdLevel F where
  psi_eq : P.ψ = S.charOnPlaces T
  g_eq : F.g = S.gIdele.map (evalPlaces T)

/-- A finite adele is integral off T for all sufficiently large finite sets T of finite places. -/
lemma eventually_mem_integralOff (a : 𝔸f E) : ∀ᶠ T in .atTop, a ∈ integralOff T :=
  Filter.eventually_atTop.2 ⟨a.2.toFinset, by simp [integralOff, compl_subset_comm]; tauto⟩

/-- A point of the finite adelic unitary group is, with its inverse, integral off T for all
sufficiently large finite sets T of finite places. -/
lemma eventually_isIntegralOff : ∀ᶠ T in .atTop,
  S.IsIntegralOff T x := by simp [mem_intGL, eventually_mem_integralOff]

/-- For finite T₀ ⊂ E^×, there are arbitrarily large finite conjugation-stable sets T of finite
places off which all t^{±1} (t ∈ T₀), 1/g, 1/N, and the lattice basis matrix `Filling.latBasis`
and its inverse are integral. -/
lemma exists_places_integralOff (T₀ : Finset Eˣ) : ∃ᶠ T in .atTop, T.StarStable ∧
  (∀ t ∈ T₀, ↑t ∈ ratIntegralOff T ∧ ↑t⁻¹ ∈ ratIntegralOff T) ∧ Fact (↑S.gIdele⁻¹ ∈ integralOff T) ∧
  S.latBasis ∈ intGL _ (integralOff T) ∧ (S.N : E)⁻¹ ∈ ratIntegralOff T :=
  (Filter.frequently_atTop.2 fun T ↦ ⟨T ∪ T.image star, by simp, ⟨by aesop⟩⟩).and_eventually
  (by simp [mem_intGL, eventually_mem_integralOff, fact_iff])

variable {S : Filling E 𝔰} {T : Finset (FinPlace E)} [T.StarStable] {x : S.GFin}

lemma ratToInf_weylElem_mul {σ p} v : S.ratToInf (weylElem 𝔰.ϱ p * σ) v = weylElem 𝔰.ϱ (fun i ↦
  unitOrOne (S.frameScaleSq v i * Φ v (p i))) * S.ratToInf σ v := by simp; ext i (_ | (_ | _) | _)
  <;> simp [weylElem, weylOn, FI.level, basisScale, frameScaleSq, unitOrOne, two_mul,
  pow_add, Nat.add_sub_assoc] <;> split <;> simp [field, ← Complex.ofReal_pow, *]

/-- Every element y of the unitary group over the completions at T is the projection of a finite
adelic element x integral off T, with x in 𝖴 if y is, and in 𝖧 if y is. -/
lemma exists_toPlaces_eq y : ∃ x, S.toPlaces T x = y ∧ S.IsIntegralOff T x ∧
  (y ∈ besselU → x ∈ besselU) ∧ (y ∈ besselH →
  x ∈ besselH) := let f : GL 𝔰.BesselIndex _ →* _ :=
    unitsMapNonUnital ⟨⟨(Matrix.map · (adeleOfLocal T)), by simp⟩, by simp, by aesop⟩
  ⟨⟨f y, have ⟨z, k⟩ := add_left_surjective 1 y.1.1
    by simpa [mem_U, ← k, ← S.map_splitGram_latMiddle (evalPlaces T), mul_add, add_mul, add_assoc,
      f, ← ext_iff, mul_apply, adeleOfLocal_evalPlaces_mul, adeleOfLocal_star,
      mul_comm (star _), -Fintype.sum_sum_type] using! congr(Matrix.map $(mem_U.1 y.2) (adeleOfLocal
      T))⟩, by ext : 3; show evalPlaces T (_ + adeleOfLocal T _) = _; simp, mem_intGL.2
    (by constructor <;> exact IsIntMatrix.one.add fun _ _ ↦ adeleOfLocal_mem_integralOff T _), by
       constructor <;> simpa [mem_besselU, mem_floorGroup, f] using!
         (congrArg (adeleOfLocal T) <| · · · ·)⟩

lemma mem_unitaryLevel_iff {u} (h : ↑u⁻¹ ∈ integralOff T) : x ∈ unitaryLevel (Ô E) u _ ↔
  S.IsIntegralOff T x ∧ S.toPlaces T x ∈ unitaryLevel O (u.map (evalPlaces T)) _ := by
  have i (k : x.1 ∈ _) := (k.isIntMatrix.sub .one).smul h
  simp [unitaryLevel, mem_intGL, IsIntMatrix, mem_Ô_iff T, Units.smul_def, forall_and] at i ⊢; tauto

lemma mem_latStabilizer_iff : x ∈ S.latStabilizer ↔ S.IsIntegralOff T x ∧ S.toPlaces T x ∈
  unitaryLevel O 1 _ := by simp [latStabilizer, ← unitaryLevel_one, mem_unitaryLevel_iff (T := T)]

/-- For every conjugation-stable finite set T of finite places of E, the product ∏_{w∈T} E_w
carries the structure of a finite place with character `Filling.charOnPlaces` and a standard level
of modulus g, as in `Filling.IsFillingLevel`. -/
lemma exists_isFillingLevel [WeilData E]
    (T : Finset _) [T.StarStable] : ∃ _ : IntegralPlace (LocProd T), ∃ F,
  S.IsFillingLevel T F := by
  obtain ⟨y, a, τ, b, e, s, t⟩ := IsAdelic.exists_skew_unit (A := LocProd T)
  let B := {b : skewAdjoint (LocProd T) | b.1 ∈ O}
  let ν := Measure.addHaarMeasure ⟨⟨B, isCompact_O.preimage_val isClosed_skewAdjoint⟩, 0,
    isOpen_O.preimage_val.interior_eq.ge O.zero_mem⟩
  let := TraceOne.mk τ t
  have sp := (map_restrict_addHaar_eq (ν.prod ν) volume (.mk' (fun p ↦ τ * y * p.1.1 + p.2.1) (by
    simp; grind)) (by measurability) .univ (fun x ↦ ⟨(skewPart (-y * x), skewPart (star τ * x)), by
    simp; grind⟩) isCompact_O.measurableSet (C :=
    B ×ˢ B) (Set.ext fun ⟨a, b⟩ ↦ let x := τ * y * a + b
    by simp; grind [(by simp [x]; grind : -y * (x + star x) = a), mul_mem, IsStarStable.star_mem,
          add_mem_cancel_left])).1
  obtain ⟨n : ν B = 1, _⟩ := Measure.addHaarMeasure_self, S.ϱ_le_k; simp [volume_O, n] at sp
  have d a : (∀ r ∈ O, S.charOnPlaces T (r * a) = 1) ↔ a ∈ O := .trans
    (by simp [locProd_O_eq_map_evalPlaces, charOnPlaces, adeleOfLocal_evalPlaces_mul, -map_mul])
    ((S.forall_selfDualChar_mul_eq_one_iff (adeleOfLocal T a)).trans (by simp [mem_Ô_iff T]))
  choose _ m i using fun x : LocProd T ↦ (locallyIntegrable_sqrt_inv_norm _ <| x ·)
  let P := IntegralPlace.mk (toPlace :=
    ⟨.mkOfMulEqOne _ _ e, ν, ⟨⟨fun x ↦ (.ofReal (genIndex x))⁻¹, by simp⟩,
    by simp [↓map_mul, ENNReal.mul_inv, genIndex_eq_inv_prod_norm, Finset.prod_nonneg]⟩,
    S.charOnPlaces T, 1, continuous_ψf.subtype_val.comp ((continuous_adeleOfLocal T).const_mul
    _), by simp [genIndex_eq_inv_prod_norm]; fun_prop, by simp [s], ⟨by fun_prop, sp⟩, by
    simp; simp [genIndex_eq_inv_prod_norm], fun _ _ g u ↦ (map_smul_eq_inv_distribHaarChar_smul
    (GeneralLinearGroup.mk'' g u)).trans (by simp [distribHaarChar_GL_eq_det isOpen_O isCompact_O
    valPair]), by simpa [Pi.isUnit_iff, -Subtype.forall] using! (Measure.ae_eval_ne _ · _), ⟨_, fun
    x ↦ ⟨_, by simp [set_pi_mem_nhds, m], (Integrable.fintype_prod_dep (i x)).mono_measure
    (Measure.restrict_pi_pi ..).le⟩, fun _ ↦ by
    erw [inv_inv, genIndex_eq_inv_prod_norm, ← enorm_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib]; clear * -
    grw [← Real.ofReal_le_enorm]; gcongr; grind [Real.sqrt_nonneg]⟩, by simp [charOnPlaces],
    -- the kernel of Plancherel's inequality is the indicator of the integers
    by
    have q z := setIntegral_char (ν := volume) (M := O.toAddSubgroup) isOpen_O (χ :=
      S.charOnPlaces T ∘ (star · * z))
    clear * - d q; refine ⟨_, IsClopen.continuous_indicator ⟨isCompact_O.isClosed, isOpen_O⟩
      continuous_one, ?_, ?_, ?_, (lintegral_mono ?_).trans ((lintegral_indicator_one_le _).trans_eq
      volume_O)⟩ <;> simp_all [integrable_indicator_iff, isCompact_O.measurableSet, Pi.one_def,
      Pi.le_def, Measure.real_def, volume_O, ← integral_indicator, indicator_apply,
      AddChar.map_add_eq_mul, add_mul, apply_ite ofReal, apply_ite enorm] <;> grind
      [IsStarStable.star_mem, star_star]⟩) ⟨b, neg_mem a, a, rfl, n⟩ d (congrFun rfl)
  have ⟨k, l, h⟩ := exists_orthonormal_Ô (E := E) S.isUnimodular_latMiddle.splitGram
  let c := U.conj k h; have t : Continuous c := .subtype_mk (by fun_prop) _
  refine ⟨P, .imp (fun F h ↦ .mk (toIsStdLevel :=
    ⟨h.1, ⟨by grw [idealZeta_locProd_le, idealZeta_intAdeles_pow_le _ S.degree_le], by simp; lia⟩,
    Measure.haar.inv, { toIsMulLeftInvariant := ?_ }, inferInstance⟩) rfl h.2)
    (P.exists_isLatticeLevel (by simp) (by simp [gIdele_val]) (by simp; omega))⟩
  simpa using (map_restrict_haar_eq (Z := Gf ..) volume _ ((S.toPlaces T).comp c.toMonoidHom)
    ((U.continuous_map : Continuous (S.toPlaces T)).comp t).measurable
    ((isOpen_intGL (isOpen_integralOff T)).preimage_val.preimage t ).measurableSet
    (exists_toPlaces_eq · |>.elim fun g h ↦ ⟨c.symm g, by simp [mul_mem_cancel_left,
    mul_mem_cancel_right, h]⟩) P.measurableSet_unitaryLevel (C := Kf E 𝔰.BesselIndex)
    (Set.ext fun g ↦ (and_comm.trans mem_latStabilizer_iff.symm).trans (le_normalizer l _).symm)).2

attribute [local simp] classBasis coe_termPosition besselLatticeBasis frameGram entrywise
  toBesselH in
lemma termPosition_floorGroup_spec {σ} (u :
  σ ∈ GT 𝔰.ϱ) c c' : let L := S.termPosition c c' σ; let φ := algebraMap E (𝔸f E)
    let ω j := σ.1.1 (𝔰.indexX₀ j) 𝔰.z
    let t := S.frameProducts σ 𝔰.top 𝔰.top; L ∈ GT 𝔰.ϱ ∧ orbitPoint 𝔰.top L⁻¹ = tailVector S.piBar
      (φ t) (c.out⁻¹.1.1 *ᵥ φ ∘ ω) ∧ S.N * star ω ⬝ᵥ ω = t * star t - S.N ^ 2 ∧ ∀ p,
      S.termPosition c c' (weylElem 𝔰.ϱ p * σ) = weylElem 𝔰.ϱ (Units.map φ ∘ p) * L := by
  have := floorGroup_apply u; simp [Sum.forall] at this
  refine ⟨by simp [mem_floorGroup, Sum.forall, this], ?_, ?_, ?_⟩
  · simp [orbitPoint, tailVector, ← mulVec_mulVec, -mulVec_single, -besselLatticeBasis]
    congr; simp [funext_iff, Sum.forall, splitGram, middleGram, mulVec, ← piBar_mul_star,
      ← mul_assoc, ← star_mul, this]
  · have := congr(diag $(σ.2) 𝔰.z)
    simp_all [middleGram, splitGram]; grind
  simp [Subtype.ext_iff, ← mul_assoc, Units.ext_iff, Sum.forall, weylElem, weylOn]
  bound

/-- Suppose all terms over (c,s,c') have nonzero leading minors and the block `Filling.termsOfLink`
Λ is nonzero. Then s lifts to K, Λ = link(w₁σ) with σ fixing all e_a, e*_a, t = h(z,σz) ≠ 0,
|t|_v > N at every infinite place v, and the block is ∑_p lim_T `Filling.cosetAmplitude`(w_pσ). -/
lemma exists_hasSum_cosetAmplitude [WeilData E] [S.IsAdmissible] {π : Side} {c s c' Λ} (h :
  S.amplitudeSum (S.termsOfLink Λ) c s c' ≠ 0) (hs : ∀ γ ∈ S.termsOver c s c', ∀ l, leadingMinor
  (S.frameProducts γ) l ≠ 0) : ∃ (t : Eˣ) (σ : S.G E), ∃ k, (σ ∈ GT 𝔰.ϱ ∧ S.frameProducts σ 𝔰.top
  𝔰.top = t ∧ (∀ v, S.N ^ 2 < ‖Φ v t.1‖ ^ 2) ∧ S.reduction k = s ∧ Λ = link (weylElem 𝔰.ϱ 1 * σ)) ∧
  ∃ L, HasSum L (S.amplitudeSum (S.termsOfLink Λ) c s c') ∧ ∀ p : Fin 𝔰.ϱ → _, Filter.Tendsto
  (fun T ↦ S.cosetAmplitude T c s c' (weylElem 𝔰.ϱ (padTuple p t) * σ)) .atTop (nhds (L p)) := by
  obtain ⟨γ₀, ⟨h₀, l⟩, h⟩ := not_isEmpty_iff.1 (h ∘ by apply @tsum_empty)
  obtain ⟨v, m, v', n, r, σ, hσ, e⟩ := exists_big_cell_decomp (hs _ h)
  have L p : Λ = link (weylElem 𝔰.ϱ p * σ) :=
    l ▸ by simp [link_besselU_mul, link_big_cell_eq_iff, *]
  have T := e ▸ hs _ h ⊤
  simp [-sub_eq_zero, frameDisc_frameGram_besselU_mul, ↓leadingMinor_frameGram_besselU_mul,
    ↓frameDisc_weylElem_mul hσ, ↓frameGram_weylElem_mul hσ, leadingMinor, *] at T h₀
  let t := Units.mk0 _ T.2
  let δ (i : (Fin 𝔰.ϱ → _) × besselU × besselU) :=
    i.2.1.1 * (weylElem 𝔰.ϱ (padTuple i.1 t) * σ) * i.2.2.1⁻¹
  have A : HasSum ((S.termsOfLink Λ ∩ S.termsOver c s c').indicator (S.amplitude c c') ∘ δ) _ :=
    (Injective.hasSum_iff (fun _ _ ↦
    (by simpa [Prod.ext_iff, funext_iff, padTuple] using big_cell_unique hσ ·))
    fun γ n ↦ ite_eq_right fun o ↦ ?_).2 (hasSum_subtype_iff_indicator.1
      (summable_amplitude ..).hasSum)
  · have D i : δ i ∈ S.termsOfLink Λ := by simp [δ, termsOfLink]; rw [← inv_inv i.2.1.1, termDisc,
      frameDisc_frameGram_besselU_mul, link_besselU_mul,
      frameDisc_weylElem_mul] <;> simp [Finset.prod_eq_zero_iff, ← L, *]
    refine ⟨t, σ, _, ⟨hσ, rfl, fun v ↦ by simpa [mul_conj', sq] using! (((map_ne_zero (Φ v)).2
      h₀.2).lt_of_le' ((termPosition_floorGroup_spec hσ c
      c').2.2.1 ▸ by simp [dotProduct, conj_mul']; positivity)).1,
      h.choose_spec.1, L _⟩, _, A.prod_fiberwise (A.summable.prod_factor · |>.hasSum), fun p ↦
      tendsto_tsum_of_dominated_convergence (A.summable.prod_factor p).norm (fun q ↦
      tendsto_const_nhds.congr' ((S.eventually_isIntegralOff (S.termPosition c c q.1)).mono ?_))
      (.of_forall fun _ q ↦ ?_)⟩ <;> clear * - D <;> grind -ac [indicator, D (p, q), norm_zero]
  obtain ⟨w, hw, w', hw', p, τ, hτ, rfl⟩ := exists_big_cell_decomp (hs _ o.2)
  cases (link_big_cell_eq_iff hτ hσ).1 (L 1 ▸ link_besselU_mul hw hw' ▸ o.1.2)
  exact n ⟨((p ·), ⟨w, hw⟩⁻¹,
    ⟨w', hw'⟩⁻¹), by simp [δ]; ext; simp [weylElem, weylOn, padTuple]; grind⟩

lemma tailVector_evalPlaces t (x : 𝔰.κ → _) : tailVector (S.piBar.map (evalPlaces T)) (evalPlaces T
  t) (evalPlaces T ∘ x) = evalPlaces T ∘ tailVector S.piBar t x := funext (by simp [Sum.forall,
  tailVector, besselLatticeBasis, middleBaseChange, mulVec, dotProduct, Matrix.diagonal,
  apply_ite (evalPlaces T), ← star_evalPlaces, -Units.val_inv_eq_inv_val])

variable [P : IntegralPlace (LocProd T)] {F} [hF : S.IsFillingLevel T F] [hT :
  Fact (↑S.gIdele⁻¹ ∈ integralOff T)] (k l : S.latStabilizer)

lemma _root_.IntegralPlace.md_evalPlaces_rpow_half {x : Eˣ} (h : ↑x ∈ ratIntegralOff T ∧
  ↑x⁻¹ ∈ ratIntegralOff T) : P.md (evalPlaces T x) ^ (2⁻¹ : ℝ) = (∏ v, ‖Φ v x.1‖ₑ)⁻¹ := by
  let u := x.map (ratToPlaces T).1
  erw [inv_eq_iff_eq_inv.1 (P.inv_md_eq_sqrt_genIndex_sq u),
    (sqrt_genIndex_le_prod_norm T ⟨x.ne_zero, h.1⟩).antisymm (by
    simpa [u, genIndex_eq_inv_prod_norm] using
      inv_anti₀ (Real.sqrt_pos.2 (genIndex_pos u⁻¹)) (sqrt_genIndex_le_prod_norm T ⟨by simp, h.2⟩))]
  simp [inv_rpow, ← rpow_natCast_mul, ofReal_prod_of_nonneg]

lemma IsFillingLevel.mem_principalLevel_iff : x ∈ S.principalLevel ↔ S.IsIntegralOff T x ∧
  S.toPlaces T x ∈ F.congGroup := by rw [principalLevel_eq_unitaryLevel, mem_unitaryLevel_iff hT.1,
  ← hF.g_eq]

lemma IsFillingLevel.reduction_eq_iff : S.reduction k = S.reduction l ↔
  (S.toPlaces T k)⁻¹ * S.toPlaces T l ∈ F.congGroup := by
  obtain ⟨l, rfl⟩ := mul_left_surjective k l
  simpa [principalLevel, mem_latStabilizer_iff.1 l.2] using hF.mem_principalLevel_iff (x := l)

lemma IsFillingLevel.psi_simpleRootSum_eq_unipotentChar (h : S.IsIntegralOff T x) :
  P.ψ (F.g⁻¹ * simpleRootSum (S.toPlaces T x)) = S.unipotentChar x := .trans (by simp
  [hF.g_eq, hF.psi_eq, simpleRootSum, toPlaces, U.map])
  (S.charOnPlaces_evalPlaces T (mul_mem hT.1 (sum_mem fun _ _ ↦ h.isIntMatrix _ _)) :)

lemma IsFillingLevel.md_g : P.md F.g = (S.g ^ numInfPlaces E : ℝ≥0∞)⁻¹ ^ 2 := by
  simpa [hF.g_eq, gIdele_val, ↓rpow_inv_rpow, ← ofReal_norm] using congr($(P.md_evalPlaces_rpow_half
    ⟨((mem_Ô_iff T).1 S.gIdele_mem).2, hT.1⟩) ^ (2 : ℝ))

lemma IsFillingLevel.g_pow_mul_unipotentMass : S.unipOrder * F.unipotentMass = 1 := by
  simp [-Finset.sum_add_distrib, Level.unipotentMass, Level.floorModulus, hF.md_g,
    ← rpow_natCast_mul, ← pow_mul _ 2, ← pow_succ, Finset.prod_pow_eq_pow_sum]
  rw [pow_mul, (?_ : Finset.sum .. = _), ← mul_pow]; simp [ENNReal.mul_inv_cancel]
  exact 𝔰.ϱ.rec (by simp) (by grind [Finset.sum_range_succ'])

/-- Let 1/g be integral off T, and let μ be s-finite, right invariant under the T-components of
a subgroup B, and carried by T-components of elements of B integral off T. Then |image of B
∩ K in Gq|·μ(K(g)) = μ(K), both groups read at T. -/
lemma IsFillingLevel.card_reducedImage_mul {B μ} [SFinite μ] (a : ∀ᵐ z ∂μ, ∃ x ∈ B, S.toPlaces T x =
  z ∧ S.IsIntegralOff T x) (r : ∀ x ∈ B, μ ∗ₘ .dirac (S.toPlaces T x) = μ) : Nat.card
  (S.reducedImage B) * μ F.congGroup = μ (unitaryLevel P.R 1 (S.latMiddle _).splitGram) := by
  choose k c b using fun s : S.reducedImage B ↦ s.2
  refine .trans ?_ ((measure_iUnion (fun s t n ↦ disjoint_left.2 fun z u v ↦ n (by
    ext1; simpa [← b, hF.reduction_eq_iff] using mul_mem (inv_mem u.out) v)) fun s ↦
    measurable_mul_const (S.toPlaces T (k s)) (P.measurableSet_unitaryLevel (g := F.g))).symm.trans
    (measure_congr (a.mono fun | _, ⟨x, a, rfl, o⟩ => propext (mem_iUnion.trans ⟨fun ⟨s, n⟩ ↦
    (mul_mem_cancel_right (mem_latStabilizer_iff.1 (k s).2).2).1 (P.unitaryLevel_le_unitaryLevel_one
    n), fun n ↦ ⟨_, by simpa using (hF.reduction_eq_iff ..).1 (b ⟨_,
    ⟨x, mem_latStabilizer_iff.2 ⟨o, n⟩⟩⁻¹, inv_mem a, rfl⟩).symm⟩⟩))))
  simp_all [← (measurableEmbedding_mulRight _).map_apply, ← μ.mconv_dirac, Nat.card_eq_fintype_card]

variable [WeilData E]

/-- The image of the Bessel subgroup in the finite level group has order |image of
H|·`unipOrder`. -/
lemma card_reducedImage_besselS : .card (S.reducedImage besselS) =
  .card (S.reducedImage besselH) * S.unipOrder := by
  obtain ⟨T, _, -, _, -⟩ := (S.exists_places_integralOff ∅).exists; obtain ⟨P, F, hF⟩ :=
    S.exists_isFillingLevel T
  have := hF.card_reducedImage_mul (B := besselU ..) (ae_ascConv_mem_unipotentBelow.mono fun z h ↦
    (exists_toPlaces_eq z).imp (by
    simp_all [unipotentBelow_eq_besselU])) fun _ h ↦ (ascConv_heisenbergMeasure_invariant
    ((unipotentBelow_eq_besselU le_rfl).ge (h.map_mem_unitriangularOn _))).1
  simp [-Finset.prod_mul_distrib, hF.ascConv_unitaryLevel, hF.integral_data,
    Level.floorModulus] at this
  erw [← Nat.card_eq_of_bijective _ ⟨(mul_injective_of_disjoint (disjoint_def.2 ?_)).codRestrict fun
    ⟨p, q⟩ ↦ mul_mem (map_mono (comap_mono fun _ ↦ mem_unitriGroup_of_mem_besselU) p.2)
    (map_mono (comap_mono fun _ ↦
    mem_unitriGroup_of_mem_floorGroup) q.2), ?_⟩, Nat.card_prod, mul_comm]; congr
  exact_mod_cast (F.unipotentMass_ne_zero_and_ne_top.elim ENNReal.mul_left_inj).1
    (this.trans hF.g_pow_mul_unipotentMass.symm)
  rintro _ ⟨u, a, _⟩ ⟨k, b, rfl⟩
  simpa [← principalLevel_eq_unitaryLevel, principalLevel] using mem_unitaryLevel_of_besselU_mul
    (inv_mem a) b (S.principalLevel_eq_unitaryLevel.le ⟨u⁻¹ * k, by simp_all⟩)
  rintro ⟨_, ⟨_, m⟩, j, rfl⟩; obtain ⟨u, a, h, b, rfl⟩ := mem_besselS.1 j
  lift h to S.latStabilizer using (mem_unitaryLevel_of_besselU_mul a b (unitaryLevel_one.ge m)).1
  use ⟨⟨_, ⟨_, m⟩ / h, by simpa, rfl⟩, _, h, b, rfl⟩; ext1; simp

/-- Unfolding: let σ fix all e_a, e*_a, γ = w_pσ, h_c⁻¹γh_c' and 1/g be integral off T, k ∈ K,
k_T⁻¹ab⁻¹ ∈ K(g). Then entry (a,b) of `Level.correlation` at (h_c⁻¹σh_c')_T⁻¹, times the
archimedean `besselCorrelation` at γ, equals κ_ϱ(p,1)·M(K(g))·`Filling.cosetAmplitude` over (c, k̄,
c'), cut off at T. -/
lemma IsFillingLevel.correlation_smul_eq_cosetAmplitude [S.IsAdmissible] [Side] {σ p c c'} {Z :
  F.IntermediateGroup} {k : S.latStabilizer} (u : σ ∈ GT 𝔰.ϱ) (o : S.IsIntegralOff T
  (S.termPosition c c' (weylElem 𝔰.ϱ p * σ))) {a b : Z.Cosets} (e : (S.toPlaces T k)⁻¹ * a.out.1 *
  b.out.1⁻¹ ∈ F.congGroup) : let q := Units.map (ratToPlaces T) ∘ p; let γ := weylElem 𝔰.ϱ p * σ
    F.correlation Z q (S.toPlaces T (S.termPosition c c' σ))⁻¹ (a, b) • besselCorrelation volume
      (.toLp 2 <| S.besselFn ·) (S.ratToInf γ) = (F.headDensity 𝔰.ϱ q 1).toReal •
      F.groupMeasure.real F.congGroup • S.cosetAmplitude T c (S.reduction k) c' γ := by
  intro q γ
  let δ (x : besselU × besselU) := x.1.1 * γ * x.2.1⁻¹
  let B c x u y :=
    ite (S.termPosition c c u * x ∈ S.principalLevel) (S.classCutoff c (S.ratToInf u * y)) 0
  have val {c} {u : besselU} {x} (t : S.IsIntegralOff T x) (h :
    S.termPosition c c u * x ∈ S.principalLevel) : P.phase F.g (S.toPlaces T x) =
    (S.unipotentChar (S.ratToFin u.1))⁻¹ := eq_inv_of_mul_eq_one_right (by
    obtain ⟨⟨d, h⟩, j⟩ := hF.mem_principalLevel_iff.1 h, u.2.termPosition_mem_besselU c
    rw [unipotentChar_eq_of_mem_principalLevel j (ratToFin_mem_besselU.2 u.2) c.out
      (by simp [termPosition, mul_assoc]), ← hF.psi_simpleRootSum_eq_unipotentChar
      ((mul_mem_cancel_right t).1 d), ← P.phase_besselU_mul (j.map_mem_unitriangularOn _),
      P.phase_eq (one_mem _) (by simpa using h)]; simp [simpleRootSum_eq_zero_of_mem_besselH])
  have ex {c x} (t : S.IsIntegralOff T x) (h : P.phase F.g (S.toPlaces T x) ≠ 0) y : ∑' u : besselU,
    B c x u.1 y = 1 := by
    have ⟨u, hu, h⟩ := P.exists_besselU_of_phase_ne_zero h; obtain ⟨u, rfl, s, d⟩ :=
      exists_toPlaces_eq u
    obtain ⟨v, hv, d, -⟩ := exists_rat_approx_unipotentChar_eq c (d.1 hu)
    erw [← tsum_classCutoff_eq_one c ((S.ratToInf v)⁻¹ * y), tsum_subtype _ (B c x · y),
      tsum_subtype _ (S.classCutoff c <|
      S.ratToInf · * _), ← (Equiv.mulRight v⁻¹).tsum_eq]; congr with w
    simp [indicator, B, classUnip, mul_mem_cancel_right, hv, termPosition, mul_assoc, ite_and, by
      simpa [termPosition, mul_assoc] using
        mul_mem_cancel_right (y := S.termPosition c c w) (mul_mem (inv_mem d)
      (by simp [hF.mem_principalLevel_iff, IsIntegralOff, mul_mem, *] : u⁻¹ * x ∈ _))]
  let Q x := S.IsIntegralOff T (S.termPosition c c x.1) ∧ δ x ∈ S.termsOver c (S.reduction k) c'
  let h x y := ite (Q x) ((S.classCutoff c y * S.classCutoff c' ((S.ratToInf (δ x))⁻¹ * y)).toReal •
    S.besselKernel (δ x) y) 0
  let g x := (((S.toPlaces T (S.termPosition c c x.1) * ·) ⁻¹' F.congGroup) ×ˢ univ).indicator
    fun w ↦ h x (S.ratToInf x.1 * w.2)
  rw [Level.correlation, show weylElem 𝔰.ϱ q * _ = S.toPlaces T (S.termPosition c c'
    γ) by simp [γ, termPosition_floorGroup_spec u c]; ext : 3; simp [toPlaces, U.map, weylElem,
    weylOn, apply_ite (evalPlaces T), -star_algebraMap_finAdele, -Units.val_inv_eq_inv_val]; rfl,
    PiLp.smul_apply, smul_assoc, cosetAmplitude, ← tsum_const_smul'',
    tsum_congr (g := (∫ w, g · w ∂F.groupMeasure.prod volume)) fun x ↦ by
    rw [integral_indicator ((measurable_const_mul _ P.measurableSet_unitaryLevel).prod .univ),
      ← Measure.restrict_prod_eq_prod_univ, integral_fun_snd (h x <| _ * ·),
      integral_mul_left_eq_self]; split <;> simp [h, Q, amplitude, δ, Measure.real, *]]
  congr 1 with i; rw [tsum_integral_apply fun x ↦ .indicator (by unfold h; split <;> fun_prop)
    ((measurable_const_mul _ P.measurableSet_unitaryLevel).prod .univ)]
  · simp [besselCorrelation]; rw [← integral_mul_right_eq_self _ a.out.1, ← integral_prod_mul]
    congr with ⟨z, y⟩; obtain ⟨x, rfl, t, -⟩ := exists_toPlaces_eq z
    let ξ := (S.termPosition c c' γ)⁻¹ * x * k
    have s : ξ.1 ∈ _ := mul_mem (mul_mem (inv_mem o) t) (mem_latStabilizer_iff.1 k.2).1
    have C w : S.toPlaces T (S.termPosition c c w.1) * S.toPlaces T x ∈ F.congGroup ∧ Q w ↔
      S.termPosition c c w.1 * x ∈ S.principalLevel ∧ S.termPosition c' c' w.2 * ξ ∈
      S.principalLevel := and_assoc.symm.trans (.trans (and_congr_left' (by
      simp [hF.mem_principalLevel_iff, mul_mem_cancel_right t, IsIntegralOff, and_comm]))
      (and_congr_right fun ⟨l, L⟩ ↦ by
      clear * - L
      use .imp' (·⁻¹ * l * k) ?_,
        .imp' (l * k * ·⁻¹) ?_ <;> simp_all [δ, ξ, termPosition, mul_assoc]))
    have j := P.phase_mul_of_mem_unitaryLevel (y := S.toPlaces T ξ) e
    set r : ℂ := _ * _; conv_lhs at j => simp [ξ, mul_assoc]
    rw [tsum_congr (g := fun w ↦
      (B c x w.1 y * B c' ξ w.2 ((S.ratToInf γ)⁻¹ * y)).toReal • r) fun w ↦ by
      simp [h, B, δ, indicator, ← ite_and, C, ↓ite_zero_mul_ite_zero]; split_ifs with q
      simp [↓besselKernel_besselU_mul, val t q.1, val s q.2, r,
        Level.IntermediateGroup.besselVector, j, besselKernel, mul_assoc, unipotentChar,
        inv_eq_conj]; simp]
    by_cases r = 0; simp [*]
    simp_all [↓tsum_toReal_smul_of_tsum_eq_one, r, Level.IntermediateGroup.besselVector, mul_assoc]
  grw [← mul_lt_top ((amplitudeAbs_lt_top_and_cut_le univ c _).1 c').2
    (hF.groupMeasure_ne_top P.unitaryLevel_le_unitaryLevel_one).lt_top, tsum_subtype,
    ← tsum_comp_le_tsum_of_injective fun _ _ e ↦ (big_cell_unique u e).2, ← ENNReal.tsum_mul_right]
  gcongr with x; simp [enorm_indicator_eq_indicator_enorm]
  grw [lintegral_indicator_le, ← Measure.prod_restrict, lintegral_prod_le]
  simp [lintegral_mul_left_eq_self (‖h x ·‖ₑ)]
  unfold h; split_ifs with q; grw [enorm_toReal_smul_le, indicator_of_mem q.2, amplitudeAbs]; simp
end Filling
end
