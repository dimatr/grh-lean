import Lib.DiscreteSeries.TailBounds
import Lib.DiscreteSeries.ClassSum
import New.Weil.ClassReps
import Lib.DiscreteSeries.SmoothFormPairing
import Lib.ClassField.UniformiserScalar

section
/-! Part of: Holomorphic discrete series: highest coefficient and reproducing property (known
result; see Lib.DiscreteSeries.Holomorphic.HolomorphicExtension).

This file: Highest coefficient is holomorphic; circle mean and reproducing property of holomorphic
functions. -/


open Finset Int MeasureTheory ComplexConjugate Complex Circle
variable {n} [Fintype n] {ε o Φ F} [Fintype Φ] {u : Φ → _} (ho : @IsPosFirstOrder n ε o)
  (hu : ∀ τ, IsKDominant ε o (u τ)) (hF : IsHolOfWeight ε o u F)
attribute [local simp] holMinorsPi holMinors sum_nonneg zpow_add₀ weightMinors_ite_eq_zpow
  ite_eq_iff prod_ne_zero_iff fieldEq diagTorus Measure.real

lemma holMinors_ite_sign {a b} (h : a ≤ b) (g : USign ε) : holMinors ε (if ε · = 1 then a else b)
  g = g.1.1.det ^ b / principalMinor g (ε · = 1) ^ (b - a) := by rw [holMinors,
  weightMinors_ite_eq_zpow, div_eq_div_iff, ← weightMinors_add_ite, ← weightMinors_const,
  ← weightMinors_add_ite] <;> simp <;> grind
  [neg_sum_abs_le_and_le_sum_abs (if ε · = 1 then a else b)]

@[simp] lemma holMinorsPi_one : holMinorsPi ε u 1 = 1 := by simp

include ho hu

omit [Fintype Φ] in
lemma IsPosFirstOrder.isKDominant_shift a τ : IsKDominant 1 o fun i ↦ cond a 1 0 * u τ i + ite (ε
  i = 1) (2 * ∑ j, |u τ j|) 0 := by have := neg_sum_abs_le_and_le_sum_abs (u τ); grind [IsKDominant,
  IsPosFirstOrder, units_eq_one_or (ε _)]

/-- If the order o is injective with the indices of sign +1 first, and every u^τ is K-dominant
for o, then the product of minors m^hol_u (`holMinorsPi`) on U(diag ε)^Φ is holomorphic of weight
u in the sense of `IsHolOfWeight`. -/
lemma isHolOfWeight_holMinorsPi : IsHolOfWeight ε o u (holMinorsPi ε u) := by
  choose f _ using (isHolOfWeight_weightMinors (ε := ε) ho.1 1 <| ho.isKDominant_shift hu ·)
  use f true / f false
  simp_all (maxDischargeDepth := 4) [AnalyticAt.div, diagChar,
    IsBorelMatrix.diag_ne_zero ho.1, -mul_ite]

include hF

-- The mean over the rotations of the base point.
/-- Circle mean: let the order o be injective with sign +1 first, u K-dominant, F holomorphic of
weight u. The mean over |s| = 1 of F(diag(s^o)h)·∏_{τ,i} s^(−o_i u^τ_i) equals
m^hol_u(h)·F(1), for every h in U(diag ε)^Φ. -/
lemma IsHolOfWeight.circle_mean_holMinorsPi h : ∫ θ : UnitAddCircle, F ((fun _ ↦ diagTorus ε
  (θ.toCircle ^ o ·)) * h) * ∏ τ, ∏ i, ↑((θ.toCircle ^ o i) ^ u τ i)⁻¹ = holMinorsPi ε u h *
  F 1 := by simp [← integral_mul_const]; convert! (hF.mul ho.1 (isHolOfWeight_weightMinors ho.1 1
  (ho.isKDominant_shift hu false))).circle_mean_weightMinors ho.1 (by
  simpa using! ho.isKDominant_shift hu true) _ 1 analyticOnNhd_const using
  2 <;> simp (maxDischargeDepth := 4) [-mul_ite, Pi.add_def, ← weightMinors_ite_eq_zpow, funext_iff]

/-- Reproducing formula: let the order o be injective with signs +1 first, each u_τ K-dominant,
F holomorphic of weight u on U(diag ε)^Φ, and F·conj(m) integrable for the compact dual
measure, m = `holMinorsPi` ε u. Then ∫ F·conj(m) = (∫ |m|²)·F(1).

Known result: Holomorphic discrete series: highest coefficient and reproducing property. -/
lemma IsHolOfWeight.integral_mul_conj_holMinorsPi (hi : Integrable fun h ↦ F h * conj (holMinorsPi ε
  u h)) : ∫ h, F h * conj (holMinorsPi ε u h) = (∫ h, ‖holMinorsPi ε u h‖ ^ 2) * F 1 := by
  rw [← integral_complex_ofReal, ← integral_mul_const, integral_eq_of_circle_mean
    (map_mul_left_eq_self _ fun _ ↦ diagTorus ε fun i ↦ ·.toCircle ^ o i) hi]
  simp [← conj_mul', mul_assoc, ← hF.circle_mean_holMinorsPi, *, ← integral_const_mul, -holMinorsPi]
  congr! 2; simp (disch := simp) [← coe_inv_eq_conj, -pow_ite, mul_div_mul_comm]

/-- Let the order o be injective with signs +1 first, each u_τ K-dominant, and F holomorphic of
weight u on U(diag ε)^Φ with F(g⁻¹) = conj F(g). Then F = F(1)·`holMinorsPi` ε u. -/
lemma IsHolOfWeight.eq_holMinorsPi_mul (i : ∀ g, F g⁻¹ = conj (F g)) h : F h =
  holMinorsPi ε u h * F 1 := by simp [mul_comm, -Circle.coe_zpow, ← fun t y ↦ by
  simpa [← i, ← coe_inv_eq_conj, ← coe_zpow, -fieldEq] using congrArg
    conj (hF.apply_mul_diagTorus y⁻¹ t), ← hF.circle_mean_holMinorsPi, *, -holMinorsPi]
end

section
/-! Part of: Holomorphic discrete series: highest coefficient and reproducing property (known
result; see Lib.DiscreteSeries.Holomorphic.HolomorphicExtension).

This file: Discrete series coefficient equals a product of minors in the holomorphic chamber. -/


open Finset Fintype GlModule HCParam.IsKHighest Int Finite

/-- Holomorphic discrete series: order o with signs +1 first, w K-dominant, w_i+γ ≤ w_j for ε_i
= 1, ε_j = −1, γ > 500n³+A+n+1, λ_i = w_i + (n+1)/2 − i with i the rank in o. Then λ has gap
500n³+A and ψ_λ = `holMinors` ε w on U(diag ε).

Known result: Holomorphic discrete series: highest coefficient and reproducing property. -/
lemma dsCoeff_eq_holMinors {n} [Fintype n] {ε o} (ho :
  @IsPosFirstOrder n ε o) [Nonempty n] A γ w (hu : IsKDominant ε o w) (hw : HasHolGap ε w γ)
  (h : 500 * card n ^ 3 + A + card n + 1 < γ) : let l : HCParam ε := 2 * w + twoRho (-o) ⊤
  l.HasLargeGap A ∧ ∀ g : USign ε, l.dsCoeff g = holMinors ε w g := ho.rec (by
  intro t _ l
  clear_value (L : l = _)
  simp [funext_iff, twoRho] at L
  have k a b (q : o a < o b) : ite (ε a = ε b) (l b < l a) (2 * (γ - card n) ≤ l b - l a) := by
    grind [IsKDominant, HasHolGap, twoRho, twoRho_lt_twoRho q, units_eq_one_or (ε _)]
  have hg : l.HasLargeGap A := ⟨(by grind [o · |>.lt_or_le <| o ·]),
    (by grind [card_lt_add_card_gt_add_one t ·]), gapThreshold.eq_1 n A ▸ mod_cast by grind⟩
  obtain ⟨rfl, x⟩ := (by grind [(by simpa [twoRho, ← sum_boole, ← sum_sub_distrib, add_assoc,
    ← sum_add_distrib] using (L · ▸ two_mul_lowestKType hg _ :))] : l.lowestKType = w),
    isKHighest_dsGenerator hg
  simpa [holMinorsPi, hg] using
    ((isHolOfWeight_coeffMap (c := fun _ g ↦ ⟨⟨(·.1.1 g), by simp⟩, by simp⟩) t (fun _ ↦ ⟨x.1, by
    have ⟨(a, b), m⟩ := exists_max fun (a, b) ↦
      ite (l.dsAction.E a b l.dsGenerator = 0) 0 (o b - o a)
    by_contra; have := casimir_bound hg.isUnitaryCasimirGe_dsAction.1
      ⟨(x.E_word_eq_wordWeight_smul [(a, b)] · |>.1), by simp +contextual [word,
      apply_apply_eq_swap_add_bracket, x.2, map_single_mul_single, DFunLike.ite_apply] at *; grind⟩
    simp [word, sub_mul] at *
    grind [x.2 a]⟩) (fun _ _ _ _ ↦ hasDerivAt_rightDeriv_expU _ _ _)
    (.mkPiAlgebra ..)).eq_holMinorsPi_mul ho (by simpa) (by simp [← dsCoeff_inv]) ![·]))
end

section
/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Algebraic modular forms on definite unitary groups: inner product, conjugate norms,
integral lattice. -/

noncomputable section


open Matrix NumberField MvPolynomial ComplexConjugate ComplexOrder Subgroup Real PolyRep Finset
section

variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n]

variable (E) in
/-- The chosen places (`chosenPlace`) and the places over the primes of a twist (`twistPlace`). -/
structure LevelPlaces where
  (ChosenIndex TwistIndex) [fintypeChosen : Fintype ChosenIndex] [fintypeTwist : Fintype TwistIndex]
  chosenPlace : ChosenIndex → _
  twistPlace : TwistIndex → FinPlace E
  apart : IsConjApart (chosenPlace ⊕ᵥ twistPlace)

lemma maxCompactAt_le_levelOf {ι} {u : ι → FinPlace E} {w H} (h : w ∉ (Set.range u).conjClosure) :
  maxCompactAt n w ≤ levelOf u H :=
  .trans (by simp_all [LE.le]; grind [star_star]) inf_trivialOn_le_levelOf

/-- The algebra map sending the variable (τ, i, h) to the sum of the variables (τ, i, a) over
the indices a with sign s(a) = c and ord(a) = h. -/
def fockLetters {Φ} (s : r → ℤˣ) (ord : r → ℕ) (c : ℤˣ) : MatrixPoly (Σ _ : Φ, n) ℂ →ₐ[ℂ]
    MvPolynomial (Φ × n × r) ℂ := aeval fun x ↦ ∑ a with s a = c ∧ ord a = x.2, X (x.1.1, x.1.2, a)

/-- The linear map sending ξ of weight κ to its polynomial `toPoly` ξ, with each variable
(τ, i, h) replaced by ∑ X(τ, i, a) over s(a) = c, ord(a) = h. -/
def letterPoly {Φ} [Fintype Φ] s ord c κ := (@fockLetters r n _ Φ s ord c).toLinearMap ∘ₗ toPoly _ κ

end

variable {E n : Type} [Field E] [CMType E] [Fintype n] (P : LevelPlaces E)

/-- The class sum `classSum` for the rational points of the standard definite space I_n, as
a function of the level K and the summand. -/
abbrev stdClassSum {X} [AddCommMonoid X] [Module ℚ X] := classSum (W := X) (stdSpace E n).Γf

namespace LevelPlaces

attribute [instance] fintypeChosen fintypeTwist apart

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (P : LevelPlaces E)

instance isConjApart_chosenPlace : IsConjApart P.chosenPlace :=
  ⟨P.apart.1.comp Sum.inl_injective, fun _ _ ↦ P.apart.2 (.inl _) (.inl _)⟩

/-- All places of P: those of `chosenPlace` and of `twistPlace`, indexed by the disjoint union. -/
abbrev placeAt := P.chosenPlace ⊕ᵥ P.twistPlace

/-- The set of finite places that occur in the families `chosenPlace` or `twistPlace` of P. -/
abbrev places := Set.range P.placeAt

end

variable (S : LevelPlaces E) (H : Subgroup (∀ i, GL n (ResField (S.placeAt i)))) (χ : H →* ℂ)
  (κ : NumberField.InfinitePlace E → ℕ → ℕ) (e : NumberField.InfinitePlace E → ℤ)

/-- The space of algebraic forms of weight (κ, e) on I_n on which the level cut out by H at the
places of S acts through the character χ. -/
def LevelForm : Type := levelSpace (algFormRep κ e) _ (χ.comp (levelOf.reduction ..))
  deriving AddCommGroup, Module ℂ, Module ℚ

instance : CoeFun (S.LevelForm H χ κ e) fun _ ↦ Gf E n → WeylIndex n κ → ℂ := ⟨(·.1.1)⟩

attribute [local simp] map_classSum mul_classSum mul_sum Rat.smul_def mul_nonneg gramForm_apply
  toLinearMapₛₗ₂'_apply dotProduct mulVec
variable {S H χ κ e} (σ : ℂ ≃+* ℂ) (φ φ' : S.LevelForm H χ κ e)

lemma LevelForm.algFormRep_eq_self_of_mem {k} (hk : k ∈ levelOf S.placeAt ⊥) :
  algFormRep κ e k φ.1 = φ.1 := by simp [levelSpace_levelOf_apply φ.2 _ 1 (mem_levelOf.1 hk).2]

lemma LevelForm.mem_sphericalAt {w} (hS : w ∉ S.places.conjClosure) : φ.1 ∈ sphericalAt
  (algFormRep ..) w := by simp [↓algFormRep_eq_self_of_mem, maxCompactAt_le_levelOf hS _]

/-- Evaluation at g, as a complex-linear map on the level forms `S.LevelForm H χ κ e`. -/
def _root_.evalForm g := (⟨⟨(· g), by tauto⟩, by tauto⟩ : S.LevelForm H χ κ e →ₗ[ℂ] _)

lemma _root_.apply_eq_evalForm g : φ g = evalForm g φ := rfl

/-- An algebraic form φ on I_n of level H, viewed as a smooth form: it is fixed by a subgroup of
finite index in K₀. -/
def LevelForm.toSmoothForm : S.LevelForm H χ κ e →ₗ[ℂ] (stdSpace E n).forms (κ, e) :=
  Submodule.subtype _

/-- For σ ∈ Aut ℂ, the index of the level in K₀ times the pairing `smoothPairing` of smooth forms
for the Gram form with σ⁻¹ ∘ conj ∘ σ as conjugation. -/
@[irreducible] def LevelForm.innerAt := ((stdLevelIndex (levelOf _ H) : ℂ) • smoothPairing
  (toLinearMapₛₗ₂' ℂ (.comp ↑σ⁻¹ ((starRingEnd ℂ).comp σ)) _ (weylGramOver (κ := κ)))
  (σ.injective <| by simpa [Int.cast_comm] using
  gramForm_map_weightRep σ · · ·)).compl₂ (toSmoothForm (χ := χ)) ∘ₛₗ toSmoothForm (χ := χ) (e := e)

/-- The pairing `LevelPlaces.LevelForm.innerAt` σ of φ and φ′ is σ⁻¹ of the class sum, over the
level, of conj(σφ(g))ᵀ G σφ′(g), with G the integral Gram matrix of weight κ. -/
lemma LevelForm.innerAt_eq_stdClassSum : innerAt σ φ φ' =
  σ⁻¹ (stdClassSum (levelOf _ H) fun g ↦ gramForm (σ ∘ φ g) (σ ∘ φ' g)) := by
  unfold innerAt; generalize_proofs; dsimp [smoothPairing]
  rw [classIntegral_eq_of_le (pairing_mem_smoothInvariants ‹_› ..).1 (fun k hk g ↦ σ.injective (by
    simp [← mul_assoc, RCLike.mul_conj, ← map_pow, @Complex.norm_eq_one_of_pow_eq_one _
    (.card H), ne_of_gt, fun φ : LevelForm .. ↦ (congr($(φ.2 ⟨_, hk⟩).1 g) : φ.toSmoothForm.1 _ =
    χ _ • φ.toSmoothForm.1 g)])) (levelOf_le_Kf (H := H))]; simp [mul_comm]; rfl

lemma LevelForm.conj_innerAt : σ⁻¹ (conj (σ (φ'.innerAt σ φ))) = φ.innerAt σ φ' := by
  simp [innerAt_eq_stdClassSum, starRingEnd_apply, star_form weylGram_posDef.1, -dotProduct]

/-- Definiteness of the σ-conjugate pairing: if an algebraic form φ of weight (κ, e), level H
and character χ has `LevelPlaces.LevelForm.innerAt` σ of φ with itself equal to 0, for an
automorphism σ of ℂ, then φ = 0. -/
lemma LevelForm.eq_zero_of_innerAt_self (h : φ.innerAt σ φ = 0) : φ = 0 :=
  eq_of_eq_on_class_reps Quot.out_eq (funext fun _ ↦ by_contra fun H ↦ (classSum_pos (fun _ ↦
  weylGram_posDef.posSemidef.dotProduct_mulVec_nonneg _) (weylGram_posDef.dotProduct_mulVec_pos
  (by simpa [funext_iff] using! H))).ne' ((map_eq_zero _).1 (innerAt_eq_stdClassSum σ φ φ ▸ h :)))

instance : NormedAddCommGroup (S.LevelForm H χ κ e) := InnerProductSpace.Core.toNormedAddCommGroup
  (cd := ⟨⟨⟨(·.innerAt 1)⟩, LevelForm.conj_innerAt 1, by simp [LevelForm.innerAt_eq_stdClassSum,
  classSum, sum_nonneg, ← weylNormSq.eq_1,
  -dotProduct], by simp, by simp⟩, LevelForm.eq_zero_of_innerAt_self 1⟩)

instance : InnerProductSpace ℂ (S.LevelForm H χ κ e) := .ofCore _

instance : FiniteDimensional ℂ (S.LevelForm H χ κ e) := finite_levelSpace_smoothFormRep

attribute [local simp] LevelForm.innerAt_eq_stdClassSum

lemma isOfFinOrder_level_char k : IsOfFinOrder (χ.comp (levelOf.reduction ..) k) :=
  χ.isOfFinOrder (isMulTorsion_of_finite _)

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {S : LevelPlaces E}
  {H : Subgroup (∀ i, GL n (ResField (S.placeAt i)))} {χ : H →* ℂ} in
instance : Fact (χ.comp (levelOf.reduction _ H) =ᶠ[nhds 1] 1) := ⟨.mono ((isOpen_levelOf (w :=
  S.placeAt) (H := ⊥)).preimage continuous_subtype_val |>.mem_nhds (by simp)) fun k h ↦ by
  simp [show levelOf.reduction _ _ k = 1 from Subtype.ext (mem_levelOf.1 h).2]⟩

/-- Let φ, B be forms, σ ∈ Aut ℂ, p a permutation of the infinite places carrying the weight of φ to
that of B. If always σ(φ(g)_i) = c·a(g)·B(g)_{p i}, conj σ(conj φ(g)_i) = c'·a'(g)·B(g)_{p i},
a(g)·conj a'(g) = 1, then σ⟨φ,φ⟩ = conj(c')·c·⟨B,B⟩. -/
lemma map_inner_self_eq {χ' l p c c'} {B : S.LevelForm H χ' _ l} {a a' : _ → ℂ} (h : ∀ g i,
  σ (φ g i) = c * a g * B g (Equiv.piCongrLeft' _ p i)) (h' : ∀ g i, star (σ (star (φ g i))) =
  c' * a' g * B g (p.piCongrLeft' _ i)) (hc : ∀ g, a g * star (a' g) = 1) :
  σ (inner ℂ φ φ) = star c' * c * inner ℂ B B := by
  set f := p.piCongrLeft' _
  simp_all [inner, ↓star_involutive.eq_iff, reindex_equiv f, weylGram_eq_submatrix κ p]
  grind

namespace LevelForm

variable (σ : ℂ ≃+* ℂ) {l : ℕ} [Fact l.Prime] (j : PadicPlace l)

/-- For σ ∈ Aut ℂ, the number ‖φ‖²_σ: the class sum of the squared Gram norms of the vectors
σ(φ(g)). -/
def normSqAt := classSum stdRatPoints (levelOf _ H) fun g ↦ weylNormSq (σ ∘ φ g)

/-- Cauchy–Schwarz for conjugates: for algebraic forms x, y and σ ∈ Aut ℂ, |σ⟨y, x⟩| ≤
‖x‖_σ·‖y‖_{σ′}, where σ′ is σ conjugated by complex conjugation. -/
lemma norm_map_inner_le : ‖σ
  (inner ℂ φ' φ)‖ ≤ √(φ.normSqAt σ) * √(φ'.normSqAt ((starRingAut.trans σ).trans starRingAut)) := by
  simp_rw [inner, innerAt_eq_stdClassSum, normSqAt, classSum, finsum_eq_sum_of_fintype, map_sum]
  grw [norm_sum_le, ← sum_sqrt_mul_sqrt_le]; gcongr
  grw [← sqrt_mul, smul_mul_smul, weylNormSq, weylNormSq, ← posDef_cauchy_schwarz weylGram_posDef]
  repeat simp [-mul_sum]

/-- If u has gauge at most 1 for Weyl's lattice at g under j∘conj, and v has gauge at most 1
under j, then the Gram pairing u*Gv is integral with respect to j: ℂ → ℂ_l. -/
lemma _root_.gramForm_mem_embValRing {g u v} (hu :
  weylGauge (ι := ⟨j.ιₚ.comp conj⟩) κ e g u ≤ 1) (hv : weylGauge (ι := j) κ e g v ≤ 1) :
  gramForm (n := n) u v ∈ embValRing (ι := j) := let ⟨γ, h, _⟩ := exists_mul_mem_integralAbove l g 1
  by erw [← @weylGauge_embFin (γ := γ), @weylGauge_le_one_iff (hk := h),
       ← gramForm_map_weightRep 1] at *
     exact sum_mem fun _ _ ↦ mul_mem (hu _) (sum_mem fun _ _ ↦ mul_mem (by simp) (hv _))

/-- The module, over the valuation ring of j: ℂ → ℂ_l, of forms φ with every value φ(g) of gauge
at most 1 for Weyl's lattice at g under j. -/
def integralForms : Submodule embValRing (S.LevelForm H χ κ e) :=
  .copy ((integralFormsAt ⊤ 1).comap (toSmoothForm.restrictScalars _)) {φ | ∀ g,
  weylGauge κ e g (φ g) ≤ 1} (by unfold integralFormsAt GaugeLe; aesop (add simp top_inf_eq))

/-- If x is integral at j∘conj, y is integral at j, and A is divisible by the orders of all
stabilisers at the level, then |j(A·⟨x, y⟩)| ≤ 1. -/
lemma norm_inner_le_one {A} (hA : ∀ g, Nat.card (classAut stdRatPoints (levelOf _ H) g) ∣ A)
    (a : φ ∈ integralForms ⟨j.ιₚ.comp conj⟩) (b : φ' ∈ integralForms j) : ‖j.ιₚ (A • inner ℂ φ
  φ')‖ ≤ 1 := by simpa only [inner, innerAt_eq_stdClassSum] using!
  smul_classSum_mem _ hA (gramForm_mem_embValRing j (a _) <| b ·)

variable {J : Type} [Fintype J] (y : J → S.LevelForm H χ κ e) {V β : ℝ}

/-- For automorphisms σ_i of ℂ, the matrix whose (i, l) entry is the class sum over g of the
Gram pairing of σ_i(y_i(g)) with σ_l(y_l(g)), conjugate linear in the first. -/
def pairingMatrix (σ : J → ℂ ≃+* ℂ) :=
  of fun i l ↦ stdClassSum (levelOf _ H) fun g ↦ gramForm (σ i ∘ y i g) (σ l ∘ y l g)

/-- The squared covolume of the family y at σ: the absolute value of the determinant of the
matrix of products ⟨y_i, y_l⟩_σ of the σ-conjugated values. -/
def covolumeSq σ := ‖(pairingMatrix y fun _ ↦ σ).det‖

variable {y} {σ} {k : ℕ} {z : Fin k → S.LevelForm H χ κ e} (hz : ∀ a, (z a).normSqAt σ ≤ exp β)

open MatrixOrder in
lemma posSemidef_pairingMatrix {σ} : (pairingMatrix y σ).PosSemidef := Eq.subst (a := stdClassSum
  (levelOf _ H) fun g ↦ let T := of fun a i ↦ σ i (y i g a); Tᴴ * weylGramOver * T) (by
    simp [pairingMatrix, classSum, Matrix.mul_assoc, Matrix.sum_apply, entrywise]) (finsum_nonneg
  fun _ ↦
  ((weylGram_posDef.posSemidef.conjTranspose_mul_mul_same _).smul (by simp)).nonneg).posSemidef

/-- If the squared covolume of y is at most e^V at every automorphism of ℂ, then |σ(det G)| ≤
e^V for the Gram matrix G of y. -/
lemma norm_map_det_gram_le (h : ∀ σ, covolumeSq y σ ≤ exp V) : ‖σ (Matrix.gram ℂ y).det‖ ≤
  exp V := by simpa [σ.map_det, pairingMatrix, inner, toBlocks₁₂, Matrix.map] using
  le_of_sq_le_sq ((norm_det_sq_le_of_posSemidef ((fromBlocks_toBlocks
  (pairingMatrix (y ⊕ᵥ y) (cond ·.isLeft ((starRingAut.trans σ).trans starRingAut)
  σ))).substr posSemidef_pairingMatrix)).trans (by rw [sq]; gcongr <;> apply h)) V.exp_nonneg

include hz

/-- Hadamard's inequality: k forms of squared norm at most e^β at σ have squared covolume at
most e^(kβ) at σ. -/
lemma covolumeSq_le : covolumeSq z σ ≤ exp (k * β) := by
  grw [covolumeSq, hadamard_det_inequality posSemidef_pairingMatrix, exp_nat_mul,
    ← Fin.prod_const]; gcongr
  simpa [↓← Complex.re_eq_norm.2 posSemidef_pairingMatrix.diag_nonneg, pairingMatrix, normSqAt,
    weylNormSq, ← Complex.reLm_coe] using hz _

/-- Adjoining k forms of squared norm at most e^β at σ to a family of squared covolume at most
e^V gives squared covolume at most e^(V + kβ). -/
lemma covolumeSq_elim_le (h : covolumeSq y σ ≤ exp V) : covolumeSq (y ⊕ᵥ z) σ ≤
  exp (V + k * β) := by grw [exp_add, ← h, ← covolumeSq_le hz]; exacts
  [fischer_det_inequality posSemidef_pairingMatrix, norm_nonneg _]
end LevelForm
end LevelPlaces
end
end
