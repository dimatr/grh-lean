import Lib.PadicHodge.Jumps
import Lib.ClassField.DeRhamFiltration
import Lib.PadicHodge.PeriodMatrixBasis
import Lib.PadicHodge.RegularityFrobenius

-- part: Lib.PadicHodge.BlochKato.CocycleContinuity
section
/-! Part of: Bloch–Kato finite local condition: rank formula and size of its annihilator (known
result; see Lib.PadicHodge.BlochKato.BlochKato).

This file: Filtered de Rham frame; extensions by crystalline cocycles are admissible; such cocycles
are continuous. -/


variable {p} [ThePrime p] {Γ R T C : Type} [Group Γ] [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T]
  [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [AddCommGroup C] [Module R C]
  [OverGp Γ p] {ρ : Representation R Γ T}
open Algebra Submodule Classical Matrix IsScalarTower Finset Function NonarchimedeanGroup algebraMap

/-- Hodge decomposition: for j of open image, T potentially crystalline with finite Z_p-basis e,
there are integers k_i, the jumps of T over Z_p, and a Z_p-linear automorphism of B_dR^ι
turning `coordAction` into the coordinatewise action and mapping (B_dR^+)^ι onto ∏
t^(−k_i)B_dR^+. -/
lemma IsPotCrys.exists_hodge_basis {ι} [Fintype ι] (h : IsPotCrys ρ) e : ∃ k, ∃ N : (ι → BdR)
  ≃ₗ[ℤ_[p]] ι → BdR, HasJumps (overZp ρ) (ofId ..) (univ.1.map k) ∧ (∀ g y, N (coordAction ρ e g
  y) = toGp g • N y) ∧ (∀ b, (∃ x : ι → BdRPlus, N ((↑) ∘ x) = b) ↔ ∀ i, b i ∈ hodgeFil (-k i)) ∧
  ∃ W : _ˣ, ∀ g, (repMatrix ρ e g).map (↑) * toGp g • hodgeMatrix W.1 k = hodgeMatrix W k := by
  choose U u using exists_GL_col_mem_of_span _ ((top_le_span_fixed (ρ :=
    overZp ..) e h (ofId ..)).trans (span_le.2 fun v ⟨_, u, w⟩ ↦
    (is_nonarchimedean _ u).rec fun U M ↦ (span_subset_span ..) (mem_span_fixed toGp (coordAction
    (B := BdR) ρ e) (by simp [coordAction, funext_iff, mulVec_eq_sum, mul_sum, mul_left_comm,
    Algebra.smul_def]) (by simp [comp_def, ← algebraMap_apply] at w; tauto)
    (InfiniteGalois.fixingSubgroup_fixedField ⟨_, U.isClosed⟩).le)))
  choose Y W k P _ E H _ using _root_.exists_hodge_frame Γ le_top U.isUnit fun g ↦ ext_col (u · g)
  have M : IsUnit _ := ⟨U * Y.toGL.map _, E⟩
  refine let L := DistribMulAction.toLinearEquiv _ _ M.unit; ⟨k, L.symm,
      And.left (hasJumps_of_rows e (.map _ P.unit)⁻¹ _ (.of_forall
      (inv_mul_apply_of_isHodgeTateFrame <| isHodgeTateFrame_of_hodgeMatrix <| H ·))), fun g ↦
    L.surjective.forall.2 fun b ↦ ?_, fun b ↦ P.smul_bijective.2.exists.trans ?_, P.unit, H⟩ <;>
    simp [L.symm_apply_eq, mem_hodgeFil, skolem, ← funext_iff, ← M.smul_left_cancel (y := b)]
  simpa [L, funext_iff, coordAction, ↓← mulVec_mulVec, mulVec_apply_eq_sum, smul_sum]
    using congr($(H g) *ᵥ toGp g • b)
  simp [L, funext_iff, hodgeMatrix, mulVec_apply_eq_sum]; field_simp

open Filter Module LinearMap PadicInt crysCocycles
variable (a : C →ₗ[R] crysCocycles ρ) [Free ℤ_[p] T]

/-- The extension of the trivial module C by T along an R-linear map a: C → Z_f(T): the
representation on T × C with g(x, e) = (gx + a(e)(g), e). -/
@[local simp] noncomputable def extensionRep : Representation R Γ (T × C) := ⟨⟨fun g ↦
  ((ρ g).coprod (proj g ∘ₗ (crysCocycles ρ).subtype ∘ₗ a)).prod (snd ..), by
  ext <;> simp; simpa using apply_mul (a _).2 1 1⟩, by
  intros; ext <;> simp [apply_mul (a _).2, add_comm]⟩

/-- If `IsAdmissible` holds for ρ and F, it holds, with the same F, for the extension of the
trivial module C by T defined by an R-linear family a of crystalline cocycles. -/
lemma isAdmissible_extensionRep [Module ℤ_[p] C] [IsScalarTower ℤ_[p] R C]
    {F} (h : IsAdmissible ρ F) : IsAdmissible (extensionRep a) F :=
  isAdmissible_of_one_tmul_mem_span fun (l, x) ↦ (a x).2.rec fun y e ↦
  (sub_mem_iff_left _ (h.baseChange_mem_span_fixedPeriods (f := inl ..) (by simp) (1 ⊗ₜ l + y))).1
  (subset_span (.of_forall fun g ↦ by rw [map_sub, tensorAction_periodTensorMap (R := R), map_add,
  ← add_eq_of_eq_sub (e g)] <;>
  simp [tensorAction, periodTensorMap, ← sub_sub, ← TensorProduct.tmul_sub]))

/-- Let T be finite over R and free over Z_p, and a: C → Z_f(T) be R-linear. For u ≠ 0, the
multiplicity of the jump u at γ in the extension `extensionRep` a is at most that in T. -/
lemma jump_extension_le [Module.Finite R T] {γ u} (hu : u ≠ 0) : jump (extensionRep a) γ u ≤ jump ρ
  γ u := finrank_le_finrank_of_injective (.of_ker (hodgeTateMaps.pull (inl ..) (by simp)) fun f
  e ↦ by ext; apply
  tate_eq_zero_of_chi_twist (neg_ne_zero.2 hu) (nhds_one_le_map_nearOne Γ ((f.2 _).mono fun _
  ↦ (·.symm.trans (by simpa [← sub_mem_ker_iff, Prod.sub_def] using! congr($e.1 _))))))

/-- Let T be finite free over Z_p and potentially crystalline. For c in Z_f(T) and every m, the
value c(g) lies in p^m T for all g with j(g) near 1. -/
lemma crysCocycles.eventually_eq_pow_smul [Module.Finite ℤ_[p] T] (h : IsPotCrys ρ)
    {c} (hc : c ∈ crysCocycles ρ) m : ∀ᶠ g in nearOne Γ, ∃ y, c g = p ^ m • y := by
  have e := finBasis ℤ_[p] T
  obtain ⟨χ : Continuous cyclotomicGp, _ : NormSMulClass ℤ_[p] ℂ_[p], P, k, H, -⟩ :=
    continuous_cycChar p, ⟨(norm_smul ·.1)⟩, IsPotCrys.exists_isHodgeTateFrame (e.prod (.singleton
    Unit _)) (isAdmissible_extensionRep (ρ := overZp ..) (id.smulRight ⟨_, hc⟩) h) (ofId ..)
  filter_upwards [H, Eventually.all fun i ↦ ((by fun_prop : ContinuousAt (fun g ↦ ‖∑ a, P (.inl i)
    a * (cyclotomicGp g ^ (-k a)).1 • g • P⁻¹ a (.inr ())‖) 1).eventually_le_const (u := (p : ℝ) ^
    (-m : ℤ)) (by simp [← Matrix.mul_apply, NeZero.pos])).comap toGp] with g H
  simp [↓← inv_mul_apply_of_isHodgeTateFrame H, ← Matrix.mul_apply, toMatrix_apply,
    algebraMap_eq_smul_one, dvd_def,
    -_root_.zpow_neg, skolem, norm_smul, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
    e.equivFun.surjective.exists, e.ext_elem_iff]
end

-- part: Lib.PadicHodge.PeriodRings.FundamentalKernel
section
/-! Part of: Fontaine's period rings and the fundamental exact sequence (known result; see
Lib.PadicHodge.PeriodRings.BdR).

This file: Kernel of the fundamental exact sequence for B_max; pole bound by powers of μ. -/


open Algebra IsScalarTower IsLocalization.Away algebraMap Function
variable {p} [ThePrime p]

/-- Let y ∈ B, a ∈ ℕ, and let ν ∈ A_inf be divisible by μ. If the image of φ^n(y) in B_dR lies
in t^(−a)B_dR^+ for every n ≥ 0, then ν^a y lies in the image of B^+. -/
lemma pow_smul_mem_range_BPlus (y : Bcris) (a : ℕ) {ν} (hν : mu ∣ ν) (h : ∀ n,
  ↑((⟨.ofAdd n, 1⟩ : FrobGal) • y) ∈ hodgeFil (-a)) : ∃ c : BPlus, c = ν ^ a • y :=
  hν.elim fun s E ↦ (surj (mu : BPlus) (ν ^ a • y)).rec (·.rec (by grind) fun N ih ⟨c, H⟩ ↦ ih
  ((c.dvd_of_thetaBPlus_frobEnd_eq_zero mu_dvd_of_theta_frobEnd fun n ↦ thetaBdR_algebraMap_BPlus ▸
  algebraMap_mem_hodgeFil_one_iff.1 (hodgeFil_anti (by lia) (Set.mem_of_eq_of_mem (by
  linear_combination (norm := (simp [E, smul_def, ← algebraMap_apply, FrobGal.smul_def]; ring))
    -congr((↑((⟨.ofAdd n, 1⟩ : FrobGal) • $H) : BdR)))
  (mul_mem_hodgeFil (h n) (algebraMap_mem_hodgeFil_iff_xi_pow_dvd.2 (.mul_left
  (pow_dvd_pow_of_dvd (map_dvd _ (theta_eq_zero_iff_xi_dvd.1 (by simp))) (a + N.succ)) ↑(frobEnd^[n]
  s ^ a))))))).imp fun _ _ ↦ (algebraMap_isUnit (mu : BPlus)).mul_left_cancel (by grind)))

/-- Kernel in the fundamental exact sequence: an element y of B with φ(y) = y whose image in
B_dR lies in B_dR^+ belongs to Q_p.

Known result: Fontaine's period rings and the fundamental exact sequence. -/
lemma Bcris.exists_padic_eq_of_frobEnd_fixed {y : Bcris} (h : frobEnd y = y) {x : BdRPlus} (hx :
  (y : BdR) = x) : ∃ a : ℚ_[p], a = y := by
  obtain ⟨c,
    rfl⟩ := by simpa [FrobGal.smul_def, iterate_fixed, *] using pow_smul_mem_range_BPlus y 0 dvd_rfl
  simp [injective_BPlus_Bcris.eq_iff] at h; let ⟨m, _, H⟩ := c.exists_p_pow_mul_eq_amax
  let ⟨a, e⟩ := exists_Ainf_eq_of_contraction {_} 0 1 (by simp [amaxImage]) (by simp_all [← H]) _ H
  obtain ⟨b, rfl⟩ := exists_algebraMap_eq_of_frobenius_eq a ((coe_inj _ BPlus).1
    (by simp [← frobEnd_eq_frobenius, ← frobEnd_algebraMap, e, h]))
  use b / p / p ^ m, (coe_inj _ BdR).1 (by simpa [field, algebraMap_apply _ ℚ_[p] BdR b, NeZero.ne,
    ← algebraMap_apply] using congr(($e : BdR)))
end

-- part: Lib.PadicHodge.WachKisin.PeriodMatrixFrame
section
/-! Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. This file proves
only the existence of a free lattice of finite height inside A_inf that spans the crystalline
periods, and no equivalence of categories. The proof is direct, by linear retractions onto the
Breuil–Kisin ring, without slope theory or étale φ-modules. Source: M. Kisin, Crystalline
representations and F-crystals, Progr. Math. 253 (2006), 459–496; Bhatt–Morrow–Scholze, Integral
p-adic Hodge theory, Publ. IHÉS 128 (2018), 4.26–4.34; Cais–Liu, On F-crystalline representations,
Doc. Math. 21 (2016).

General lemmas of linear algebra and matrices (textbook or folklore).

This file: Existence of a finite-height Kisin frame in A_inf for a crystalline period matrix. -/

namespace Lift.Chart

open BPlus Algebra Matrix MulSemiringAction Function Witt RingHom Ideal Quotient PreTilt
open WittVector renaming constantCoeff → π
variable {p} [ThePrime p] {d} {c : Chart} [Fintype d]
attribute [-simp] map_smul smul_right_inj Matrix.mul_smul

/-- Let R: S → D be a homomorphism to a nontrivial semiring and X a set of vectors over S. If
R(t·x) = 0 for all x in X forces R(t) = 0, some square matrix N with rows in X has R(det N)
≠ 0. -/
lemma exists_det_ne_zero {S D} [CommRing S] [Semiring D] [Nontrivial D] (R : S →+* D) (X : Set (d →
  S)) (h : ∀ t, (∀ x ∈ X, R (t ⬝ᵥ x) = 0) → ∀ i, R (t i) = 0) : ∃ N, R (det N) ≠ 0 ∧ ∀ k, N k ∈ X :=
  (exists_maximalFor_of_wellFoundedGT _ (· · ∈ X) ⟨1, by simp⟩).imp fun N m ↦
  ⟨m.1, fun k ↦ by_contra
  fun hk ↦ m.1 (by simp [N.det_eq_sum_mul_adjugate_row k, h (N.adjugate · k) fun x h ↦ by_contra
  fun n ↦ hk (@m.2 (N.updateRow k x) (by simpa [← cramer_transpose_apply, ← adjugate_transpose,
  cramer_eq_adjugate_mulVec]) (fun l ↦ by by_cases l = k <;> simp [*]) k (by simpa))])⟩

attribute [local simp] map_smul' smul_smul mulVec_sub Set.image_pair pow_succ mul_sub Units.smul_def
  comp_def map_mulVec
attribute [local simp ←] mul_assoc mul_pow Subalgebra.smul_def OFlat.frobEnd_apply iterate_frobenius

/-- A square matrix M of determinant 0 over a valuation ring R has a kernel vector a, with some
coordinate 1, such that g(a) = a for every ring endomorphism g of R with M·g(a) = 0 (Artin's
minimal support argument). -/
lemma _root_.exists_fixed_ker {R} [CommRing R] [IsDomain R] [ValuationRing R] {M : Matrix d d R}
  (h : M.det = 0) : ∃ a ν, a ν = 1 ∧ M *ᵥ a = 0 ∧ ∀ g : R →+* R, M *ᵥ g ∘ a = 0 → g ∘ a = a := by
  have ⟨w, h, hm⟩ := exists_minimalFor_of_wellFoundedLT _ support (exists_mulVec_eq_zero_iff.2 h)
  choose ν a ha using by
    simpa [mem_span_singleton] using @Finite.exists_max _ _ _ (ne_iff.1 h.1).nonempty _ (span {w ·})
  generalize e : w ν = t at *; cases (funext ha : w = t • a)
  use a, ν, ?_, ?_, fun g h ↦ by_contra (@hm _ ⟨sub_ne_zero.2 ·, ?_⟩ ?_ ν ?_ ?_) <;> aesop

/-- For a period matrix U for (h, v) there are Q, L over A_inf, Z over S_B, Z' over B^+, B over
S with QL = τ^h, UZ = E^hQ, Z'Z = E^h, φQ = vQB, and gZ ∈ Z·M_d(A_inf) for all g fixing Λ
and θ(z).

Known result: Kisin lattice (Breuil–Kisin module) of a crystalline lattice. -/
lemma IsPeriodMatrix.exists_frame {U h v} (hU : c.IsPeriodMatrix U h v) : ∃ (Q L Z Z' :
  Matrix d d _) (B : Matrix d d c.S), Q * L = tau ^ h • 1 ∧ (∀ i j, Z i j ∈ c.bicommutant) ∧ U * Z =
  c.E.1 ^ h • Q.map ainfToBPlus ∧ Z' * Z = c.E.1 ^ h • 1 ∧ Q.map frobEnd = v • (Q * B.map (↑)) ∧
  ∀ g, c.FixesThetaZ g → ∃ G, g • Z = Z * .map G ainfToBPlus := by
  obtain ⟨⟨Q, Z, h₀, hZ, e, hN, hA⟩, ⟨⟨U', _⟩, ⟨F, -, _, -, eF⟩⟩, ⟨u, hu, eu⟩,
    ⟨t, ht⟩, q, _, eq⟩ := hU.exists_basis, id hU, c.exists_bicommutant_mul_phi_E_eq_one,
    c.associated_E_mul_tau_mu.dvd, c.exists_bicommutant_mul_p_eq_one
  have act (m : FrobGal) (ρ : Matrix d d _) F w r (h₁ : .map ρ ainfToBPlus * m • U = U * F) (h₂ :
    w * ainfToBPlus (m • c.E.1) = ainfToBPlus (c.E.1 * r)) : U * w ^ h • (F * m • Z) =
    c.E.1 ^ h • (r ^ h • ρ * m • Q).map ainfToBPlus := by
    erw [mul_smul_comm, ← mul_assoc, ← h₁, mul_assoc, ← map_mul (toRingHom _ _ m).mapMatrix]
    ext; simp [@smul_def _ BPlus, mul_apply, Finset.mul_sum, mul_left_comm (ainfToBPlus _), *]
  choose b o using (hN _ _ (fun i ↦ mul_mem (pow_mem (mul_mem (ainfToBPlus_mem_bicommutant _) hu) h)
    (sum_mem fun _ _ ↦ by apply_rules [mul_mem, frobEnd_mem_bicommutant])) congr(col $(act _
    (v⁻¹ • 1) F _ 1 (congr(_ * $eF).trans (by simp)) (by simpa using! congr(_ * $eu))) ·))
  have o : Q * bᵀ.map (↑) = _ := ext_col o
  let R := π.domRestrict c.S
  have A g H := act (1, g) _ 1 1 _ ((hU.3 g H).choose_spec.trans (by simp)) (by
    erw [one_mul, ← (c.associated_smul_E g).choose_spec])
  by_cases h₁ : ↑p ∣ Q.det
  · have H i j t : t ⬝ᵥ c.adicBasis.coord i ∘ Q j = c.adicBasis.coord i ((Q *ᵥ (t ·)) j) := by
      simp [mulVec_eq_sum, dotProduct]
    -- bounded denominators
    choose N D σ τ S using exists_det_ne_zero R {c.adicBasis.coord i ∘ Q j | (i) (j)} fun t h i ↦
      (pi_dvd_iff.2 fun j ↦ p_dvd_iff.2 ((OFlat.isHausdorff_and_shiftDiff_surjective
      (mt Ainf.isUnit_iff_isUnit_constantCoeff.2 c.4)).1.1 _ fun n ↦ .zero.2
      (mem_comap.1 ((Submodule.restrictScalars_mem ..).1 (c.adicBasis.mem_of_coord (by
      simp [Ideal.map_pow, ← map_le_iff_le_comap]; rfl) (mul_mem_right _ _ <| ker_le_comap π <| H ..
      ▸ h _ ⟨·, _, rfl⟩)))))).rec fun w hw ↦ (hN w (Z *ᵥ q • ainfToBPlus ∘ (t ·)) (fun _ ↦
      sum_mem (by simp [mul_mem, *])) (by ext; simpa [e, eq] using congr(_ • (q * ainfToBPlus
      ($hw _))))).rec fun | _, rfl => p_dvd_iff.1 ⟨_, congr($(mulVec_injective_of_det_ne_zero h₀
      (hw.trans (Q.mulVecLin.2 ..).symm)) i)⟩
    have ker {m ρ C a} (h : C = ρ * m • Q) : Q.map π *ᵥ a = 0 → C.map π *ᵥ toRingHom FrobGal _ m ∘ a
      = 0 := (by simpa [h, ← Pi.zero_def] using! congr(_ *ᵥ toRingHom _ _ m ∘ $(·)))
    -- a fixed vector of the kernel
    have ⟨a, ν, e₁, hw, hm⟩ := exists_fixed_ker (π.map_det Q ▸ p_dvd_iff.1 h₁)
    refine let K := R bᵀ.det * R N.det; (mul_ne_zero (fun H ↦ h₀ (eq_of_forall_pow_dvd_sub p (·.rec
        (by simp) fun n h ↦ (map_dvd_iff (MulEquiv.ofBijective _ frobEnd_bijective)).1 (by
      simpa [map_det, IsUnit.pow, ← det_mul, o] using! mul_dvd_mul h (p_dvd_iff.2 H)))))
      D (Perfection.ext (f := K) fun M ↦ ?_)).rec
    choose n s e using ((add_right_injective M).nat_tendsto_atTop.eventually (.all fun i ↦
      c.eventually_exists_coeff_eq_of_fixed
      (fun g hg ↦ congr($(hm _ (ker (by simpa [↓← ext_iff, smul_def, e, ↓E_ne_zero, -Matrix.map_mul]
      using ((by ext; simpa using congr($(hZ _ _ ⟨(toRingHom _ _ g).toAddHom, by
      simp [c.S.smul_def, smul_def, hg]⟩ smul_mem_amaxImage) 1) : g • Z = Z) ▸ A g
      (by simp [← theta_smul, FixesThetaZ, FixesLambda, hg ⟨_, _⟩]) :)) hw)) i)) M)).exists
    have ⟨C, hC, ha⟩ : ∃ C, K * R (det C) ∣ K ^ p ^ n ∧ Q.map π *ᵥ C.map R *ᵥ a ^ p ^ n = 0 := n.rec
      ⟨1, by simpa⟩ fun n ⟨C, h, e⟩ ↦ ⟨bᵀ * C.map c.φ, by
      grw [det_mul, map_mul, pow_succ, pow_mul, ← h, mul_pow, ← pow_dvd_pow K (Fact.out : 1 < p),
        Dvd.intro _ (refl K)]; simp [map_det]; rfl, by simpa [pow_mul, Pi.pow_def] using! ker o e⟩
    simpa [OFlat, K, mul_assoc, by simpa using (map_det ..).trans (
         det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (funext fun k ↦
         (((coeff _).comp R).map_mulVec (N * C) ..).symm.trans (by
         erw [← mulVec_mulVec, mulVec, dotProduct_comm, ← S, H, ← mk_thetaPhiInv_eq_coeff,
           eq_add_of_sub_eq (c.exists_frobE_dvd_sub_of_dvd _ _ p _
           (by simpa [OFlat, ← eq_zero_iff_dvd, mk_thetaPhiInv_eq_coeff, mulVec_eq_sum, e] using!
           congr(coeff (M + n) ($ha _)))).choose_spec.choose_spec]
         simp [CharP.cast_eq_zero, frobE_dvd_iff.1 dvd_rfl])) ((e ν).subst (by simp [*])))]
      using! map_dvd (coeff (M + n)) hC
  have hQ {X Y} (eY : U * Y = c.E.1 ^ h • .map X ainfToBPlus) : ∃ L, Q * L = X := by
    choose a e using fun i ↦ (hA _ _ congr(col $eY ·) _ _ _ h₁ congr($Q.adjugate_mul i))
    use of a
    simp [← smul_right_inj h₀, ← mul_smul_comm, mul_adjugate, ← (ext e : _ * X = Q.det • of a)]
  choose k a w ea using (exists_Ainf_approx · 0 h)
  obtain ⟨⟨n, hn⟩, L, hL⟩ := Finite.exists_le (k ∘ U.uncurry),
    @hQ (tau ^ h • 1) U' (by simp [-map_pow, *])
  have hX : (U.map fun y ↦ p ^ (n - k y) * a y).map ainfToBPlus =
    U * ainfToBPlus p ^ n • (1 - t ^ h • U' * U.map
    w) := by ext i j; simp [*, ← pow_sub_mul_pow _ (hn (i, j))]; clear * - ea ht; grind [smul_def]
  obtain ⟨Y, rfl⟩ : Q.map ainfToBPlus ∣ U := (hQ (by rw [hX, ← mul_smul_comm])).imp' (q ^ n • ·.map
    ainfToBPlus + (t * c.E) ^ h • L.map ainfToBPlus * U.map w) (by simp +contextual [mul_add,
    ← Matrix.map_mul, *, -map_pow])
  use Q, L, Z, Y, bᵀ, hL, hZ, e, (isRegular_of_isLeftRegular_det (mul_right_injective₀
    (mt (ainfToBPlus.map_det Q).trans (by simpa)))).1 (by simpa), by simp [o]; rfl, fun g H ↦
    (hQ (A g H)).imp fun L hL ↦
    isLeftRegular_iff_mulVec_injective.2 hU.mulVec_injective (by simpa [← hL, e] using! A g H)
end Lift.Chart
end

-- part: Lib.PadicHodge.WachKisin.CrystallinePeriodMatrix
section
/-! Part of: Kisin lattice (Breuil–Kisin module) of a crystalline lattice (known result; see
Lib.PadicHodge.WachKisin.PeriodMatrixFrame).

This file: Period matrix of a crystalline lattice with Frobenius matrix and Hodge basis. -/

open RingHom Algebra BdRPlus Function Matrix algebraMap Module.Basis

seal Module.Basis.baseChange

attribute [local simp ←] IsScalarTower.algebraMap_apply

attribute [local simp] AlgHom.map_smul_of_tower comp_def dotProduct hodgeMatrix mul_assoc smul_smul

variable {p} [ThePrime p] {T Γ ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Group Γ] [Fintype ι]
  [𝒥 : OverGp Γ p] {ρ : Representation ℤ_[p] Γ T} (a b : ℕ) {c} (hc : Lift.Chart.IsChartOf c 𝒥.toGp)

include hc

lemma Lift.Chart.IsChartOf.exists_mem_bicommutant_of_fixed {b : Bcris} (hb : ∀ g, 𝒥.toGp g • b =
  b) : ∃ s ∈ c.bicommutant, s = b := by
  obtain ⟨⟨u, h, f⟩, m, w, e⟩ := c.exists_bicommutant_mul_p_eq_one,
    exists_witt_coeff_of_isChartOf hc one_ne_zero (by simpa)
  exact ⟨_, mul_mem (pow_mem h m)
    (ainfToBPlus_mem_bicommutant w), by simpa [smul_def, mul_pow, e] using congr($f ^ m • b)⟩

/-- Let j(Γ) contain the fixer of Λ and θ(z), T be crystalline with basis e and jumps in [−a,
b]. There are an invertible M over B with invariant columns and a unit v of A_inf, Eτv = μ,
with U = (Eτ)^aM a period matrix over B^+ for (a + b, v^a). -/
lemma Lift.Chart.IsChartOf.exists_isPeriodMatrix (h : IsCrystalline ρ) e (hab : ∀ k,
  jump ρ (ofId ..) k ≠ 0 → -a ≤ k ∧ k ≤ b) : ∃ M : GL ι Bcris, ∃ U v,
  (∀ g, (repMatrix ρ e g).map (algebraMap _ _) * M.1.map (toGp g • ·) = M.1) ∧ c.E * tau * v.1 =
  mu ∧ c.IsPeriodMatrix U (a + b) (v ^ a) ∧ U.map (algebraMap ..) = (c.E * tau) ^
  a • M.1 := let A m := mapMatrix (MulSemiringAction.toRingHom FrobGal Bcris m)
  let P := {N : _ˣ // ∀ g, (repMatrix ρ e g).map (↑) * A (1, toGp g) N = N.1}
  let F := (ofId ..).mapMatrix
  have I : Injective F := map_injective injective_BPlus_Bcris
  have X {B m} (h : ∀ n i l, _) : ∃ C, F C = (_ * tau) ^ m • B := ⟨_, ext fun i l ↦
    invFun_eq (pow_smul_mem_range_BPlus _ m c.associated_E_mul_tau_mu.dvd' (h · i l))⟩
  (h.exists_basis le_top).rec fun _ ⟨u, hu⟩ ↦ by
  let M : P :=
    ⟨@unitOfInvertible _ _ _ (invertibleToMatrix ..), fun g ↦ ext_col ((equivFun_tensorAction
    ..).symm.trans <| congrArg _ <| u.reindex_apply (u.indexEquiv (e.baseChange _)) · ▸ hu ..)⟩
  let N n : P := ⟨M.1.map (A (.ofAdd n, 1)).1, (.trans (by simp [A]) congr(A _ $(M.2 ·)))⟩
  choose Y hY W k h₄ h₅ _ using fun N :
    P ↦ by simpa [IsUnit, -hodgeMatrix] using (exists_hodge_frame Γ le_top
    (N.1.isUnit.map (mapMatrix _)) (.trans (by simp; rfl) congr($(N.2 ·).map (ofId ..))))
  have J n i := hab (k n i)
    (by rw [(hasJumps_of_rows e (.map _ (W n))⁻¹ _
    (by exact .of_forall (inv_mul_apply_of_isHodgeTateFrame <| isHodgeTateFrame_of_hodgeMatrix <|
    h₅ n ·))).1]; simp)
  have T {B : Matrix ..} {k c P} (Q : GL ι BdRPlus) (h : ∀ i, _) (e : B * _ = hodgeMatrix P k) i l :
    B i l ∈ hodgeFil c := (Q.map (ofId ..).1).eq_mul_inv_iff_mul_eq.2 e ▸ sum_mem fun m _ ↦
    hodgeFil_anti (h m) (by simp [mem_hodgeFil, ← map_inv, field, ← map_mul])
  choose R hX eX using fun M N : P ↦ (hc.exists_mem_bicommutant_of_fixed fun g ↦ congrFun₂ (by
    simpa [← map_mul, N.2] using! congr(M.1⁻¹ * $(M.2 g) * A (1, toGp g) (M.1⁻¹ * N.1)).symm) · ·)
  obtain ⟨eX, ⟨v, o⟩, ⟨w, _⟩, ⟨V, H⟩, Z, _⟩ := ((F (of _)).ext <| eX · ·),
    c.associated_E_mul_tau_mu, c.exists_bicommutant_mul_phi_E_eq_one, X (T (.map _ (Y _).toGL) (J _
    · |>.1) <| h₄ <| N ·), X fun n ↦ T (W (N n)) (neg_le_neg <| J (N n) · |>.2) (((N n).1.map (ofId
    ..).mapMatrix.1.1).inv_mul_eq_iff_eq_mul.2 (by erw [← mul_assoc, h₄]; simp [zpow_ne_zero]))
  have G m : F (m • V) = (_ * m • tau) ^ a • A m _ := ext (by
    simpa [F, smul_def] using! congr(m • $H · ·))
  refine ⟨_, V, v, M.2, o, ⟨⟨Z, I (by simp [*]; module)⟩,
    ⟨Chart.ainfToBPlus (c.φ c.E) ^ a • of (R M (N 1)), w ^ a • of (R (N 1) M), by simp [*, mul_mem,
    pow_mem], I (by simp [↓smul_mul_smul, *, ← mul_pow]), I ((G _).trans
    (by simp [Units.smul_def, H, eX, N, ← o, «φ», -smul_of, FrobGal.smul_def]; module))⟩, fun g h ↦
    (hc g h).choose_spec ▸ ((c.associated_smul_E _).symm.mul_mul associated_smul_tau).rec fun r h ↦
    ⟨r.1 ^ a • (repMatrix ρ e _).map (↑), I (by erw [map_mul, G, H, map_smul
    (ofId Ainf _).mapMatrix, smul_mul_smul, ← mul_pow, mul_comm, h, M.2])⟩, fun f y ↦ ?_⟩, H⟩
  choose t ht using fun l ↦ hc.dvd_extendToBPlus _ (fun k ⟨_, g, rfl⟩ ↦
    congr($(((toGp g).toAlgHom.map_adjugate _).trans (congrArg _ (hY M g))) l k)) f y
  simp [smul_def, ← dvd_def, pi_dvd_iff, ← xi_pow_dvd_iff,
    (c.associated_E_xi.map _).pow_pow.dvd_iff_dvd_left]
  exact fun h i ↦ (Finset.dvd_sum fun _ _ ↦ (h _).mul_left _).trans (by
    obtain _ := congr((ofId _ BdR).mapMatrix $H), ((Y M).toGL.map _).eq_mul_inv_iff_mul_eq.2 (h₄ M)
    simp [F, ofId, map_mulVec, ↓← map_inv, ← coe_inj _ BdR] at *
    simp [*, ← mul_assoc]
    simp [↓← mulVec_mulVec, mulVec, diagonal]
    congr 2; ext j; grind [(algebraMap.coe_inj ..).1 (ht j)] :
    ((↑(W M) * diagonal t * (W M).2) *ᵥ (↑) ∘ (V *ᵥ y)) i = _).dvd
end

-- part: Lib.PadicHodge.Comparison.CrystallineLimit
section
/-! Dwork's trick, as an integral crystalline comparison with a uniform denominator. The statement
here is integral over A_max. It uses one multiplier, invertible in B_max, that depends only on the
field and the range of weights, and not on the lattice or its rank. Source: M. Kisin, Crystalline
representations and F-crystals, Progr. Math. 253 (2006), Lemma 1.2.6; M. Kisin, Potentially
semi-stable deformation rings, JAMS 21 (2008), Lemma 2.2; B. Bhatt, P. Scholze, Prismatic F-crystals
and crystalline Galois representations (2023), proofs of Prop. 5.3 and Thm 7.9.

Part of: Limits of crystalline representations with bounded weights are crystalline (known result;
see Lib.PadicHodge.Limit.LocalLimit).

This file: Dwork's trick: after Frobenius the frame is constant basis times unit over A_max. Uniform
denominator for the integral crystalline comparison over A_max, independent of rank. Limit of
crystalline representations of bounded weights is crystalline (Liu), group-ring form. -/

namespace Lift.Chart

open BPlus Matrix Algebra PowerSeries WittVector Ideal Function NeZero RingHom Finset Nat
variable {p} [ThePrime p] {c : Chart} {d : Type} [Fintype d] {t} (hΛ : c.FixesThetaZ t)

attribute [-simp] isUnit_map_iff smul_of algebraMap_smul RingHom.coe_pow map_smul
  LinearMap.map_smul_of_tower

attribute [local simp] C_eq_algebraMap Subalgebra.algebraMap_def pow_mem extendToBPlus_mul
  extendedCoord_oneIndex_eq_self ite_mem sub_mul Associated.dvd associated_E_xi

lemma tau_mul_z_pow_dvd {n h a} (H : ainfToBPlus (tau * c.z ^ n) ∣ ainfToBPlus (c.E ^ h * a)) :
  tau * c.z ^ n ∣ a := by
  obtain ⟨a, rfl⟩ := @tau_dvd_of_theta_frobEnd _ _ a fun j ↦ by
    grw [c.associated_E_xi.dvd] at H
    obtain _ := theta_iterate_frobEnd_xi j, map_dvd thetaBPlus (map_dvd (frobEnd ^ (j + 1)) H)
    simp_all [coe_pow, ne]
  grw [pow_dvd_of_map _ _ (@z_dvd_of_dvd_E_pow_mul _ _ c h)] <;> simp_all [mul_left_comm,
    mul_dvd_mul_iff_left, ne_zero_of_map c.theta_z_ne_zero]

lemma frobEnd_pow_ainfToBPlus l s : (frobEnd ^ l) (ainfToBPlus s.1) = ainfToBPlus ((c.φ ^ l) s).1 :=
  coe_φ_pow .. ▸ iterate_frobEnd_algebraMap ..

@[simp] lemma frobEnd_pow_ainfToBPlus_z l : (frobEnd ^ l) (ainfToBPlus c.z) =
  ainfToBPlus c.z ^ p ^ l := by simp [coe_pow, z_eq_teichmuller]

include hΛ

lemma tau_mul_z_dvd_smul_sub {y} (hy : y ∈ c.bicommutant) : ainfToBPlus (tau * c.z) ∣ t • y - y :=
  (c.z_dvd_sub hΛ.1 hy).rec fun b
  h ↦ by grw [h, map_mul, mul_comm, ← dvd_of_thetaBPlus_frobEnd_eq_zero b tau_dvd_of_theta_frobEnd
  fun i ↦ (frobEnd^[i + 1] y).exists_p_pow_mul_eq_amax.rec fun k ⟨a, e⟩ ↦
  (c.exists_pow_mul_extendedCoord_eq_add c.E ⟨0, by simp⟩ a 1).rec fun s ⟨v, _, f⟩ ↦ by
    simpa [← e, Iterate.rec (· ∈ _) hy @c.frobEnd_mem_bicommutant, c.smul_theta_of_fixesThetaZ hΛ,
      mul_add, z_eq_teichmuller, ne, theta_E,
    eq_add_of_sub_eq h, c.z_eq_teichmuller ▸ c.theta_z_ne_zero, -theta_teichmuller, -iterate_succ,
    Commute.iterate_right (smul_frobEnd t) _ _] using congr(thetaBPlus (t • $f - $f))]

/-- Radius lemma. Let t fix Λ, tz = [ε]z, Z'Z = E^h, Z over S_B, tZ = ZG with G over A_inf, 3e ≤
p^l. Then φ^lZ = φ^l(E)^b·CV, V ∈ GL_d(A), C fixed by the fixer of Λ; if eA ≤ p^lδ, the y ∈
S^d with Vy ∈ ℕ^d + E^A(B^+)^d span p^{4δ}S^d at least.

Known result: Dwork's trick: integral crystalline comparison with a uniform denominator. -/
lemma radius_lemma (ht : t • c.z = teichmuller p epsTilt * c.z.1) {Z Z' : Matrix d d BPlus} {h}
  (hZ : ∀ i j, Z i j ∈ c.bicommutant) (e : Z' * Z = c.E ^ h • 1) {G} (hG : t • Z =
  Z * Matrix.map G ainfToBPlus) {l} (hl : 3 * c.e ≤ p ^ l) b : ∃ (V : (Matrix d d Amax)ˣ) (C :
  Matrix d d _), (∀ g : Gp p, FixesLambda c.f g → g • C = C) ∧ Z.map frobEnd^[l] =
  (c.frobE l).1 ^ b • (C * V.1.map (algebraMap ..)) ∧ ∀ A δ, c.e * A ≤ p ^ l * δ → ∀ x : d
  → c.S, p ^ (4 * δ) • x ∈ Submodule.span c.S {y | ∃ r : d → ℕ, ∀ i, ainfToBPlus c.E ^ A ∣ (V.1.map
  (algebraMap _ BPlus) *ᵥ fun i ↦ ainfToBPlus (y i)) i - r i} := by
  have P {n N} (h : c.e * n ≤ N) : ∃ y, ainfToBPlus c.z ^ N = p ^ n * ofId _ _ y :=
    ((pow_dvd_pow_of_dvd (by
    simpa [(c.unitSeries.isUnit.map _).map] using dvd_trans ⟨_, p_mul_X.symm⟩ (map_dvd _ c.7.dvd'))
    n).trans (by grw [← pow_mul, h])).imp fun y e ↦ by simpa using! congr(ofId _ BPlus $e)
  obtain ⟨⟨T, _⟩, hp, ⟨r, hr⟩, ⟨u, hu, U⟩, q, hq⟩ := P (mul_comm 3 _ ▸ hl), isUnit_p.pow,
    c.z_dvd_E_sub_p, c.exists_bicommutant_mul_p_eq_one,
    c.z_dvd_E_sub_p.trans (sub_dvd_pow_sub_pow _ _ h)
  have ⟨ev₀, h₀⟩ := exists_algHom_X_eq c.S (mem_span_singleton.2 (dvd_mul_right ↑p T))
  let ev := (algHom _ _ BPlus).comp ev₀
  have hX : ainfToBPlus c.z ^ p ^ l = p ^ 2 * ev X := by simp [ev, algHom, *]; ring
  choose m w y hy f using (u ^ h * Z' · · |> c.extendedCoord_mem_bicommutant c.oneIndex |>
    c.eventually_exists_pow_mul_eq_add_z_mul |>.exists)
  let B := of ((u ^ m · ·) * (ainfToBPlus <| ofId _ _ <| w · ·))
  have H (g : Gp p) := by simpa [mul_assoc, mul_eq_one_symm U] using congr(g • $U * u)
  let W := (u ^ h * ainfToBPlus q) • 1 - of ((u ^ m · ·) * y) * Z
  have hW : B * Z = 1 + ainfToBPlus c.z • W := by
    ext i j; linear_combination (norm := (simp +zetaDelta [mul_apply, ← sub_eq_of_eq_add (f ..),
      mul_sub, mul_add, ← mul_assoc, ← mul_pow, U, mul_sum, hu, hZ, mul_comm (Z' ..),
      smul_def (A := BPlus), mul_right_comm _ (Z ..)]; split <;> ring_nf))
      congr(u ^ h * (c.extendedCoord c.oneIndex ($e i j) + ainfToBPlus ($hq) * row 1 i j))
  have hY : t • (B * Z) = B * Z * G.map ainfToBPlus := (by simp [↓mul_assoc, ← hG, B, entrywise,
    smul_sum, H, hΛ])
  have hG i j : tau * c.z ∣ (G - 1) i j := pow_one c.z ▸ tau_mul_z_pow_dvd (by
    simpa [mul_sub, ← mul_assoc, *, smul_def (A := BPlus), apply_ite] using show _ ∣
    (Z' * (t • Z - Z)) i j from dvd_sum fun k _ ↦ (tau_mul_z_dvd_smul_sub hΛ (hZ k j)).mul_left _)
  have := IsHausdorff.mk fun x h ↦ c.eq_zero_of_z_pow_dvd (by grw [(hp 2).dvd_mul_left.1
    ((dvd_pow_self _ out).trans hX.dvd), smodEq_span_pow_iff_dvd.1 <| h ·, sub_zero])
  -- the entries of `φ ^ l (B Z)` are values of power series, by successive approximation
  choose F hF using fun i j ↦ mem_range_of_approx ev.toAddMonoidHom (ev.toSemilinearMap.2 X)
    (X := {x : ℕ × (d → _) // ∃ q : ℕ, ∃ A : d → _, ∀ j, x.2 j ∈ c.bicommutant ∧ ainfToBPlus (A j) =
    q • (B * Z) i j - ainfToBPlus c.z ^ x.1.succ * x.2 j}) (fun ⟨(n, W), _⟩ ↦
    p ^ (n - padicValNat p n ! + 2) * (frobEnd ^ l) (W j)) (fun ⟨(n, W), q, A, e⟩ ↦ by
    have ⟨α, β, f⟩ := c.exists_tau_mul_E_eq_mul_epsTilt_pow_sub n.succ_ne_zero
    set v := padicValNat p n.succ
    let a := n.succ - padicValNat p n.succ !
    choose s W' hW' H using fun j ↦ show ∃ s : c.S, ∃ W' ∈ c.bicommutant, ainfToBPlus s =
      p ^ v.succ * W j - ainfToBPlus c.z * W' from ((univ.dvd_sum fun l _ ↦
      (map_dvd ainfToBPlus (hG l j)).mul_left (W l)).sub ((tau_mul_z_dvd_smul_sub hΛ
      (e j).1).mul_left (ainfToBPlus (mu + 1) ^ n.succ))).rec fun D hD ↦
      have hV : ainfToBPlus (c.E ^ 0 * (α * (∑ l, A l * G l j - t • A j))) = ainfToBPlus (tau *
        c.z ^ n.succ) * (p ^ v.succ • W j - ainfToBPlus c.z * (ainfToBPlus α * D + -ainfToBPlus (p ^
        v • r + β * c.E) * W j)) := by linear_combination (norm :=
        (simp [← smul_algebraMap_eq_algebraMap_smul t (A _), smul_sub, e, ht, mu, mul_sub,
        mul_assoc, mul_apply, ← mul_sum]; ring)) -ainfToBPlus c.z ^ n.succ * (ainfToBPlus α * hD
        + W j * congr(ainfToBPlus ($f - p ^ v • tau * $hr))) - ainfToBPlus α * congr(q • $hY i j)
      (tau_mul_z_pow_dvd ⟨_, hV⟩).rec fun x hx ↦ ⟨_, _, c.extendedCoord_mem_bicommutant _ _, by
        simp [hx, ne_zero_of_map c.theta_z_ne_zero] at hV
        simpa [e, extendToBPlus_ainfToBPlus, -map_add] using congr(c.extendedCoord c.oneIndex $hV)⟩
    use C (p ^ a * (c.φ ^ l) (s j)), ⟨(n.succ, W'), p ^ v.succ * q, p ^ v.succ • A + (c.z.1 ^
      n.succ * s ·), by simp; grind⟩
    simp [show n - padicValNat p n ! + 2 = a + v + 1 by clear * -; grind [padicValNat_factorial_le,
      factorial, padicValNat.mul], ← frobEnd_pow_ainfToBPlus, hX, H]; ring) ⟨(0, W i), 1, row 1
    i, by simp (maxDischargeDepth := 5) [↓hW, W, mul_apply, sub_mem, _root_.sum_mem, mul_mem, *]⟩
  have ⟨⟨V, hV⟩, ε, hε⟩ : IsUnit (1 + @X c.S _ • of F) ∧ IsUnit (1 + X * C (p * (c.φ ^ l) r))
    := by simp [isUnit_iff_isUnit_det, det_one_add_smul X, isUnit_iff_constantCoeff]
  have hD := Matrix.map_mul.symm.trans (show (B * Z).map (frobEnd ^ l) = ev.mapMatrix V by
    ext; simp [hW, hV, hX, by simpa using hF]; ring)
  obtain ⟨⟨D, e⟩, V, rfl⟩ := (isUnit_of_mul_isUnit_left (hD ▸ V.isUnit.map _)).smul
    (hp b).unit, MulAction.surjective (ε ^ b) V
  refine ⟨V.map ev₀.mapMatrix.1.1, _, fun g hg ↦ congrArg (·⁻¹.1) (show
    D.map (MulSemiringAction.toRingHom ..).mapMatrix.1 = D by ext; simp [B, *,
    coe_pow, Commute.iterate_right (smul_frobEnd g) l _]), by
    erw [← mul_smul_comm, D.eq_inv_mul_iff_mul_eq, e, smul_mul_assoc, hD]; ext
    simp [frobE, hε, hX, eq_add_of_sub_eq' hr, ← mul_pow, ← mul_assoc, smul_def (A := BPlus),
      Units.smul_def, ← frobEnd_pow_ainfToBPlus]; ring!, fun A δ hA x ↦
    Submodule.mem_span.2 fun T hT ↦ (P hA).rec fun y hy ↦ ?_⟩
  -- a unit over `S⟦X⟧`, evaluated at `X = z ^ p ^ l / p ^ 2`, is nearly a matrix over `S`
  choose s G' e using fun D G ↦ show ∃ s : c.S, ∃ G', p ^ (2 * D) * ev G =
    ainfToBPlus s + ainfToBPlus c.z ^ (p ^ l
    * D) * ev G' from D.rec ⟨0, by simp⟩ fun D ⟨s, G', e⟩ ↦ ⟨p ^ 2 * (s + constantCoeff G' * c.z ^
    (p ^ l * D)), .mk _, by rw [G'.eq_X_mul_shift_add_const] at e
                            linear_combination (norm := (simp [pow_mul, hX]; ring)) p ^ 2 * e⟩
  choose a _ k using fun G ↦
    c.exists_pow_mul_extendedCoord_eq_add c.E ⟨0, by simp⟩ (y * ev₀ (G' δ G)) A
  let f := ((Ideal.Quotient.mk (span {ainfToBPlus c.E ^ A})).comp ev.1).mapMatrix (m := d)
  let g := f.comp C.mapMatrix
  choose N H using fun F ↦ show ∃ N, g N = p ^ (2 * δ) • f F from ⟨F.map (s δ + a), ext fun i j ↦
    Ideal.Quotient.eq.2 (have k := k (F i j)
    by erw [map_mul, ← map_p_pow_mul, ← mul_assoc, ← hy, extendToBPlus_mul, fun G ↦
      (sub_eq_zero.1 (c.eq_zero_of_z_pow_dvd fun n ↦ by
      grw [Nat.le_mul_of_pos_left n (pos (p ^ l)), ← (hp (2 * n)).dvd_mul_left]
      simp [mul_sub, ← map_p_pow_mul, e, _root_.dvd_sub]) :
      c.extendToBPlus _ (ev G) = ev G)] at k <;> simp [mem_span_singleton, e, k])⟩
  have K N (r : ℕ) (h : f V * g N = r) := (range_mulVecLin N).trans_le (T.span_le.2 fun
    | _, ⟨k, rfl⟩ => hT ⟨col r k, (by simpa +zetaDelta [entrywise,
      Matrix.natCast_apply, apply_ite, ← Quotient.eq_zero_iff_dvd] using! congr($h · k))⟩)
  convert add_mem (K (p ^ (4 * δ) • 1 - N V⁻¹ * N V) 0 ?_ ⟨x, rfl⟩)
    (K (N V⁻¹) (p ^ (2 * δ)) ?_ ⟨N V *ᵥ x, rfl⟩) <;>
    simp [H, ← f.map_mul, -nsmul_eq_mul, ← nsmul_one, smul_smul, ← pow_add, ← add_mul]

end Lift.Chart

open TensorProduct Matrix Module Submodule MulSemiringAction Function algebraMap MonoidAlgebra
  Finset LinearMap Algebra Lift nsmulRange NeZero ContinuousMap Set Metric IsLocalRing PadicInt
  WittVector

/-- For toGp : Γ → Gp p (from OverGp) with open image and h ≥ 0, some a in A, invertible in B,
serves every crystalline Z_p-lattice T with jumps in [0, h]: a⊗T lies in the A-span of (A⊗T)^Γ, and
UU' = a for matrices over A, U with Γ-invariant columns.

Known result: Dwork's trick: integral crystalline comparison with a uniform denominator. -/
lemma Lift.uniform_period_bound {p} [ThePrime p] Γ [Group Γ] [OverGp Γ p] h : ∃ a : Amax, IsUnit
  (a : Bcris) ∧ ∀ {T ι : Type} [AddCommGroup T] [Module ℤ_[p] T] [Fintype ι] (e : Basis ι ℤ_[p] T)
  {ρ}, IsCrystallineUpTo h ρ → (∀ t, a ⊗ₜ t ∈ span Amax (fixedPeriods ρ _ ⊤)) ∧ ∃ U U', U * U' =
  a • 1 ∧ ∀ g : Γ, ((ρ g).toMatrix e e).map ((↑) : _ → Amax) * U.map (toGp g • ·) =
  U := let ⟨k, hf, _⟩ := exists_kummer_chart Γ
  let m := (.ofAdd (p.clog (3 * k.e)), 1)
  let α := (algebraMap ..).comp (toRingHom FrobGal _ m)
  ⟨α (k.E * tau) ^ h, by simpa using! (isUnit_smul_of_dvd_mu m k.associated_E_mul_tau_mu.dvd).pow h,
    fun e ρ ⟨c, J⟩ ↦ (iff_and_self.2 fun H t ↦ let b := e.baseChange _
    let ⟨y, M, eV, H⟩ := (reindex_equiv (toLinAlgEquiv b).symm).2.1.1 H
    Eq.subst (by simpa [toLinAlgEquiv_apply, smul_tmul'] using
      congr(toLinAlgEquiv b $eV (1 ⊗ₜ t))) (sum_smul_mem _ _ fun _ _ ↦ subset_span
      (b.equivFun.injective <| (equivFun_tensorAction ..).trans congr(col $(H ·) _)))).1 (by
  choose M H _ U hU eU using by simpa using k.chart_isChartOf.exists_isPeriodMatrix 0 _ c e (J _)
  choose Q L Z _ _ hL hZ _ e' _ _ hG using hU.exists_frame
  choose V C hC eV _ using k.radius_lemma (hf _) (by simpa using
    (k.exists_smul_z 1).choose_spec) hZ e' (hG _ (hf _)) (p.le_pow_clog Fact.out _) 0
  exact let s m := (toRingHom _ _ m).mapMatrix
    let i := RingHom.mapMatrix _
    let q := (k.E.1 ^ h • Q).map α
    have E : i q = s m (U * Z) := Matrix.ext (by
      simp [*, i, s, q, @Algebra.smul_def _ BPlus]
      tauto)
    ⟨q * V.2, V * _, by simpa [q, mul_assoc, Matrix.map_smul', mul_pow, mul_smul] using
      congr(_ • ($hL).map α), fun g ↦ Matrix.map_injective injective_Amax_BPlus (by
      simpa [map_mul, ← (Matrix.ext fun _ _ ↦ smul_algebraMap_eq_algebraMap_smul (toGp g) (_ :
        Amax) : s _ (i _) = i (.map _ (toGp g • ·))), E, mul_assoc, ← map_mul i, show s (1, _) C =
        C from hC _ (hf g).1, s, m, comp_def, smul_smul, show s m Z =
        C * i V by simpa [← ext_iff, FrobGal.smul_def] using! eV] using! congr(s m
        ($((Matrix.map_injective injective_BPlus_Bcris (by simpa [← eU, comp_def] using! H g) :
      (repMatrix ρ e g).map (↑) * s (1, _) U = U))) * C) : i _ = i _)⟩)⟩


attribute [-simp] map_eq_zero

attribute [-instance] LieRinehartAlgebra.toIsScalarTower

variable {p} [ThePrime p] {G Δ κ I : Type} [Group G] [Group Δ] [OverGp Δ p] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {ι : I → Type} [∀ η, Finite (ι η)] (w : Δ →* ℤ_[p][G])
  (σ : PadicRep G p) {R : PadicRep G p}

/-- For a matrix representation σ: G→GL_m(Q̄_p), the Z_p-algebra homomorphism from the group
ring Z_p[G] to m×m matrices over Q̄_p extending σ. -/
noncomputable abbrev groupRingHom := lift ℤ_[p] _ _ ((Units.coeHom _).comp σ.rep)

/-- For a multiplicative map w: Δ→Z_p[G] and a matrix representation σ of G over Q̄_p, the matrix
representation of Δ sending g to σ(w(g)), σ extended linearly. -/
noncomputable abbrev viaGroupRing := matrixRep ((groupRingHom σ).toMonoidHom.comp w).toHomUnits

variable (Δ) in
/-- For finitely many continuous representations τ_s of a compact group G over Q̄_p, there is a
finite free Z_p-algebra T, a quotient of Z_p[G], through which all τ_s factor by jointly
injective algebra maps. -/
lemma exists_finite_groupRing_quotient [Finite κ] {τ : κ → PadicRep G p} (hτ : ∀ s, Continuous
  (τ s).rep) : ∃ (T : AlgCat ℤ_[p]) (q : _ →ₐ[ℤ_[p]] T) (u : ∀ _, T →ₐ[ℤ_[p]] _), Free ℤ_[p] T ∧
  Module.Finite ℤ_[p] T ∧ (⇑q).Surjective ∧ (∀ s y, u s (q y) = groupRingHom (τ s) y) ∧ (∀ y,
  q y = 0 ↔ ∀ s, groupRingHom (τ s) y = 0) ∧ ∀ {h w}, (∀ s, IsCrystallineUpTo (Γ := Δ) h
  (viaGroupRing w (τ s))) → IsCrystallineUpTo h (actionRep ℤ_[p] T (q.toMonoidHom.comp w)) := by
  let Φ := AlgHom.pi (groupRingHom <| τ ·)
  choose O ν P h using (hτ · |> eventually_exists_isLatticeIn |>.exists)
  have := Finite.of_fg ((fg_pi fun s ↦ fg_range (mulLeftRight _ ((P s).1, (P s).2) ∘ₗ
    (O s).1.val.toLinearMap.mapMatrix)).of_le (S := Φ.range.toSubmodule) fun _ ⟨y, e⟩ s _ ↦
    ⟨y.lift _ _ _ (ν s), by simp [← e, Φ, lift_apply, Finsupp.sum, ← by simpa using h, mul_assoc]⟩)
  have := IsTorsionFree.trans_faithfulSMul ℤ_[p] (PadicAlgCl p)
  let u s := (Pi.evalAlgHom _ _ s).comp Φ.range.val
  let f (s : Σ s, (τ s).Index) := applyVec (u s.1).toLinearMap (Pi.single s.2 1)
  have I t (h : ∀ s, f s t = 0) : t = 0 := by ext s i l; simpa [f] using! congrFun (h ⟨s, l⟩) i
  refine ⟨.of .., _, u, inferInstance, ‹_›, Φ.rangeRestrict_surjective, ?_, ?_, fun C ↦
    ⟨.of_jointly_injective le_top (C ·.1 |>.1) _ ?_ I, fun γ _ h ↦ (exists_jump_of_linearIndependent
    (fun _ ↦ (C _).1.isPotCrys) _ (asSemilinear f) ?_ (linearIndependent_emb_coords f (finBasis ..)
    I) (ext_id _ γ _ ▸ h)).elim (C ·.1.1 |>.2 _ _)⟩⟩ <;> simp [f, u, Φ,
    asSemilinear, -mulVec_single, Subtype.ext_iff, funext_iff]

/-- Limits of crystalline representations. G compact, toGp : Δ → Gp p (from OverGp) of open image,
w: Δ → Z_p[G] multiplicative, R continuous with `IsTraceNondeg`; X finite families of continuous
representations, crystalline along w with jumps in [0, h]. If ‖tr R‖ ≤ ε on the kernel in Z_p[G] of
some family, for each ε > 0, then R∘w is crystalline.

Known result: Limits of crystalline representations with bounded weights are crystalline. -/
lemma isCrystalline_of_trace_limit {h} (hR : Continuous R.rep) (hn : IsTraceNondeg R.rep) {X : ∀ η,
  ι η → _} (hc : ∀ η x, IsCrystallineUpTo h (viaGroupRing w (X η x))) (hX : ∀ η x, Continuous (X η
  x).rep) (H : ∀ ε > 0, ∃ η, ∀ y, (∀ x, groupRingHom (X η x) y = 0) → ‖(groupRingHom R y).trace‖ ≤
  ε) : IsCrystalline (viaGroupRing w R) := by
  obtain ⟨⟨κ, hf, -⟩, ⟨T, q, u, _, _, hs, hu, hi, -⟩, _, e, h₀, E⟩ := exists_kummer_chart Δ,
    exists_finite_groupRing_quotient Δ
    fun _ : Unit ↦ hR, HasUniqueDiv.of_isTorsionFree.{0, 0} Amax, uniform_period_bound Δ h
  let A := Amax; let Λ := WittFq κ.f; let := Algebra.compHom A (ofId Λ Ainf).1
  let D {T : AlgCat ℤ_[p]} (q : _ →ₐ[ℤ_[p]] T) : Submodule Λ _ := ⟨⟨⟨fixedPeriods (actionRep ℤ_[p] T
    (q.toMonoidHom.comp w)) A ⊤, by simp +contextual [fixedPeriods]⟩, by tauto⟩,
    fun c _ h g ↦ by erw [← algebraMap_smul A, mem_ofPred, tensorAction_smul, h,
    smul_algebraMap_eq_algebraMap_smul (A := Ainf), (hf _).1]; rfl⟩
  have := (isMaximal_iff Λ).2 (irreducible p).maximalIdeal_eq.symm
  have hΛ {T : AlgCat _} [Free ℤ_[p] T] [Module.Finite ℤ_[p] T] q :
    (⇑(liftBaseChange A (@D T q).subtype)).Injective ∧ Free Λ (D q) ∧ Module.Finite Λ (D q) := ?_
  obtain ⟨⟨c⟩, F, -, ⟨⟩⟩ := Amax.nonempty_adicBasis Λ rfl, (finBasis ℤ_[p] T).equivFun, hΛ q
  -- traces define the `p`-adic topology on `T`, by compactness
  choose ε K x H using fun k ↦ (nhds_basis_closedBall.mem_iff.1 ((ContinuousMap.curry ⟨_, ((u () ∘ₗ
    F.symm.1).continuous_on_pi.fst'.mul (Units.continuous_val.comp hR.snd')).matrix_trace⟩
    ).2.isClosedMap.eventually_nhds_fiber 0 ((F.surjective.comp hs).forall.2 fun z n ↦
    (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_maximalIdeal_pow _ k).mem_nhds (by simp [(hi z).2
    fun _ ↦ hn _ (sum_mem (by simp [smul_of_tower_mem, mem_span_of_mem]) |> (lift_apply ..).substr)
    (by simpa [hu] using congr($n ·))])))).imp (H · |> ·.symm.imp_right)
  choose _ π _ _ _ S _ J Y using (exists_finite_groupRing_quotient Δ fun s : Σ l : Set.Iic ·,
    ι (x l.1) ↦ hX _ s.2)
  let Q := q.toLinearMap.baseChange A; let Q' k := (π k).toLinearMap.baseChange A
  choose n b y he using fun k ↦ mem_span_set'.1 ((span_preimage_eq (f := Q' k) (D _).nonempty fun _
    _ ↦ lTensor_surjective _ (S k) _).ge (x := e ⊗ₜ 1) ((E (finBasis ..) (Y k (hc _ ·.2))).1 _))
  have hker {k v} (h : Q' k v = 0) : Q v ∈ nsmulRange (p ^ k) _ ∧ ∀ i ≤ k, Q' i v = 0 := by
    obtain ⟨v, rfl⟩ := (lTensor_exact _ (exact_subtype_ker_map _) (S k) _).1 h
    exact v.inductionOn (fun a ⟨z, m⟩ ↦ have := by simpa [J, Sigma.forall] using m
      ⟨nsmulRange.map_mem (TensorProduct.mk _ _ _ a) ((Basis.ofEquivFun F).sum_equivFun (q z) ▸
        mem_span_pow_smul_top_iff.1 (sum_mem
        fun i _ ↦ smul_mem_smul (@maximalIdeal_eq_span_p p _ ▸ K k (by simpa [hu,
        norm_le_of_nonempty, this] using (H k <| z * .single · 1)) _ rfl i ⟨⟩) ⟨⟩)), fun l e ↦ by
        simp [Q', (J l z).2 fun s ↦ this _ (s.1.2.trans e) _]⟩) (by simp +contextual [add_mem])
  have hP {k v} : Q' k v ∈ D (π k) ↔ _ := forall_congr' fun g ↦ (tensorAction_periodTensorMap
    (g := mulLeft ℤ_[p] (w g)) (by simp) ..).congr_left.trans sub_mem_ker_iff.symm
  have P {M i j} := @isAdicComplete_of_free A M _ i j (.span {↑p}) _
  simp_rw [isAdicComplete_iff, isHausdorff_iff, isPrecomplete_iff, SModEq.sub_mem,
    mem_span_pow_smul_top_iff] at P
  choose z hz using fun s ↦ P.2 (fun k ↦ Q (∑ i, c.coord s (b k i) • y k i)) @fun k m e ↦
    let v m e := ∑ i, b m i ⊗ₜ[Λ] (⟨_, hP.2 (hP.1 (y m i).2 · |> hker |>.2 k e)⟩ : D _)
    Q.map_sub .. ▸ (hker (by simpa [v] using congr((lift (lsmul .. ∘ₗ c.coord s)
      $(@(hΛ _).1 (v _ .refl) (v _ e) (by simpa [v, ← he m] using congr(Q' k $(he k))))).1))).1
  lift z to c.Index → D q using fun s g ↦ (eqLocus_eq_ker_sub _ id).ge (P.1 _ fun k ↦ by
    erw [sub_zero, ← sub_sub_cancel (Q _) (z s), map_sub, LinearMap.sub_apply,
      tensorAction_periodTensorMap (R := ℤ_[p]), ← map_sub]
    exact sub_mem (hker (hP.1 (by simp [sum_mem,
      smul_mem _ _ (y ..).2]) g)).1 (nsmulRange.map_mem _ (hz ..))
    simp)
  choose G N using fun k ↦ Filter.eventually_atTop.1 (.all (b k · |> c.eventually_sub_sum_mem <| k))
  let W := partialSups G
  have ⟨ω, hω⟩ := P.2 (∑ s ∈ W ·, c.b s ⊗ₜ[Λ] z s) @fun k _ e ↦ sub_mem_comm_iff.1
    ((sum_sdiff_eq_sub (W.mono e)).subst (sum_mem fun s h ↦ nsmulRange.map_mem (TensorProduct.mk Λ A
    _ _) ((sub_sub_cancel _ (z s).1 ▸ sub_mem (nsmulRange.map_mem _ (sum_mem fun i _ ↦
    mem_span_pow_smul_top_iff.1 (smul_mem_smul (by
    simpa [Finsupp.single_apply, mem_sdiff.1 h] using c.coord_sub_mem_pow (f := (W k).sum (.single
      · _)) (by simpa using N k _ (le_partialSups ..) i) s) ⟨⟩))) (hz ..)).rec fun v e ↦ ⟨⟨v, (by
    simpa [← e, ne, -nsmul_eq_mul] using (z s).2 ·)⟩, Subtype.ext e⟩)))
  refine isAdmissible_of_one_tmul_mem_span fun v ↦
    (smul_mem_iff_of_isUnit _ h₀).1 (span_subset_span A _ _ ?_)
  simpa [Q, periodTensorMap, Algebra.smul_def] using mapsTo_span (f := periodTensorMap A Bcris
    (applyVec (u ()) v)) (forall_mem_range.2 (fixedPeriods.map (by simp [hu]) ·.2))
    ((range_liftBaseChange A (D _).subtype).le (x := Q (e ⊗ₜ 1)) ⟨ω, sub_eq_zero.1 (P.1 _ fun k ↦ by
    simpa [← he k, sub_smul, sum_smul, smul_sum, smul_sub, univ.sum_comm, smul_comm (c.b _)]
      using sub_mem (sub_mem (sum_mem (t := W k) fun s _ ↦ nsmulRange.map_mem (lsmul _ _ (-c.b s))
      (hz s k)) (nsmulRange.map_mem (liftBaseChange A (D _).subtype) (hω k))) (sum_mem (t := ⊤)
      fun i _ ↦ nsmulRange.map_mem (toSpanSingleton _ _ (Q (y k i))) (mem_span_pow_smul_top_iff.1 (N
      k (W k) (le_partialSups ..) i))))⟩)
  -- the fixed periods are finite over the fixed coefficients and stay independent over `A`
  have L {n : Type} [Fintype n] {y : n → D q} (h : LinearIndependent Λ y) : LinearIndependent _ (y ·
    |>.1) := .of_comp (periodTensorMap A Bcris .id) (.restrict_scalars (by
    simpa [Algebra.smul_def] using! injective_BPlus_Bcris.comp injective_Amax_BPlus) (ker_eq_bot.1
    (bot_unique (le_of_fixed_mem_of_saturated le_top (by simp +contextual) (fun w e g ↦ by erw
    [mem_ker, ← eventually_tensorAction_eq (fixedPeriods.map (by tauto) <| y · |>.2) w g, e,
    map_zero]) fun a e f ↦ by
    choose m w (hw : ∀ t, _ = algebraMap _ _ (algebraMap Λ A _)) using by
      simpa using fun t ↦
        exists_witt_coeff_of_isChartOf κ.chart_isChartOf (ne 1) (by simpa using congr($(f ·) t))
    simpa [a.ext_iff, (of_faithfulSMul ℚ_[p] ..).1, by simpa [Λ, p_nonzero] using (
      linearIndependent_iff'.1 h ⊤ ((sup ⊤ m - m · |> p.pow) • w) (Subtype.ext
      (periodTensorMap_injective (by simpa [← @algebraMap_smul A _ Bcris, ← algebraMap_smul A, ← hw,
      le_sup, smul_sum, smul_smul, ← pow_add, ← mul_assoc, a.sum_fintype,
      Finsupp.linearCombination] using congr(p ^ sup ⊤ m • $e)))))] using hw))))
  cases free_finite_of_rank_le span_insert_zero.symm (isHausdorff_of_injective_pi (.span {↑p})
    (.restrictScalars Λ (finBasis A _).equivFun.1 ∘ₗ (D q).subtype)) (by simp [ne,
    Nat.cast_smul_eq_nsmul Λ]) _ (rank_le fun _ h ↦ by simpa using (L h).fintype_card_le_finrank)
  use injective_of_linearIndependent ((finBasis ..).baseChange A).span_eq
    (by convert! L (finBasis ..).linearIndependent; simp)
end
