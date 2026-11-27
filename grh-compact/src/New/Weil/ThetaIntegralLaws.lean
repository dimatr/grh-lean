import New.Weil.PairReal
import New.Filling.LineParabolic
import New.Weil.PairSumNegation
import New.Weil.FourierCoefficient

-- part: Lib.ClassField.HeckeCharacter.CharOfDet
section
/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Tame Hecke character on determinants of integral adelic points is product of residue
characters. -/

namespace AutChar.HasWeight

open Matrix Prod IsIntMatrix
variable {E n} [Field E] [CMType E] [Fintype n] {μ : AutChar E} {e ψ} {s : n → _}

/-- Let μ have weight e and tame part ψ, trivial outside finitely many distinct places w_i. For
k in the stabiliser K₀ of the standard lattice, μ(det k) = ∏_i ψ_{w_i}(det(k mod w_i)). -/
lemma apply_det_eq_prod (h : μ.HasWeight e ψ) {ι} [Fintype ι] {w : ι → _} (hw : w.Injective) (hψ :
  ∀ u ∉ Set.range w, ψ u = 1) k : μ.1 (detFin s k.1) = ∏ i, ψ (w i) (Kf.reduceAt _ k).1.det := by
  simp +contextual [h.2,
    det_mem (mem_Kf.1 k.2), ↓finprod_tame_eq_prod_reduceU1 (S := .map ⟨w, hw⟩ ⊤), *, reduceU1]
  congr!; convert! RingHom.map_det ..
  simp [det_apply', snd_sum, snd_prod]; rfl

lemma apply_det_eq_one (h : μ.HasWeight e 1) {k} (hk : k ∈ Kf ..) : μ.1 (detFin s k) = 1 := by
  ext; simp [h.2, det_mem (mem_Kf.1 hk), ↓finprod_tame_eq_prod_reduceU1 (S := ∅)]
end AutChar.HasWeight
end

-- part: Lib.ClassField.HeckeCharacter.LocalCharacters
section
/-! Part of: Algebraic Hecke characters (type A₀); extension of the quadratic character of a CM
field (known result; see Lib.ClassField.HeckeCharacter.SplittingCharExists).

This file: Global characters of the determinant read through local components at chosen places. -/


open Matrix Fintype WeilData Gf Finset
variable {E} [Field E] [CMType E] {n} [Fintype n] {s} {P : Finset _} {μ}
  (𝔠 : SplitTameChar E μ) {k : Gf E n}

@[simp] lemma upsilonU1_det_of_mem_Kf [WeilData E] : k ∈ Kf .. → upsilonU1.1 (detFin s k) = 1 :=
  upsilonU1_hasWeight.apply_det_eq_one

lemma spaceChar_rankTwist [WeilData E]
    {ν : AutChar E} : 2 ∣ card n → (rankTwist ν n).spaceChar (card n) =
  ν.baseChange := by simp_all [dvd_def, AutChar.spaceChar, rankTwist, pow_mul]

lemma atPlaces_of_mem_trivialOn : k ∈ Gf.trivialOn n P → atPlaces P k = 1 := by
  simp [GeneralLinearGroup.ext_iff, atPlace, atPlaces]; aesop

/-- For finite adelic unitary g, `localChar` P ξ k at the determinant of the P-components
of g equals ξ(d)|d|^{k/2}, d the idele that is det g at P and 1 elsewhere. -/
@[simp] lemma localChar_det ξ k (g : Gf E n) :
    localChar P ξ k (atPlaces P g).1.det = ξ.1 (detOn P g.1) * √(ideleAbs (detOn P g.1)) ^ k := by
  erw [detOn_eq_prod, ← prod_attach, MulChar.ofUnitHom_coe _ (atPlaces P g).det,
    ← Circle.coeHom_apply]
  simp [g.1.map_det, atPlaces, atPlace, Real.sqrt_prod, ideleAbs_locFullIdele, prod_zpow]
  tauto

lemma SplitTameChar.exists_atPlaces_eq g : ∃ k ∈ supportedOn n 𝔠.S, atPlaces 𝔠.S k = g :=
  ⟨_, atSplits_mem_supportedOn 𝔠.star_notMem
  (g.map <| Pi.evalRingHom _ ·), by ext : 3; apply congr($(atPlace_atSplits ..) _ _)⟩

lemma SplitTameChar.nu_det_of_mem_Kf (h : k ∈ Kf ..) : 𝔠.ν.1 (detFin s k) =
  𝔠.χ (atPlaces _ k).1.det := by
  simp [nu_apply_of_integral, IsIntMatrix.det_mem (mem_Kf.1 h), RingHom.map_det, atPlaces]
end

-- part: Lib.Weil.DualPair.TwoLineTerms
section
/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Tower property: constant term of a theta lift along an isotropic line (known result; see
Lib.SiegelWeil.Tower.LargeSideConstantTerm).

This file: Rules for theta kernels with data mod m: twists, level action, sums, conjugation. Two
mixed models along isotropic lines: Levi action and Poisson equality of sums. -/

noncomputable section

open NumberField Matrix MvPolynomial ComplexConjugate WeilData Space Weil Std Modulus Fintype
  Function Pi Ideal.Quotient
variable {E : Type} [Field E] [CMType E] {n} {n' n₁ n₂ : Type} [Fintype n]
  [Fintype n'] [Fintype n₁] [Fintype n₂] [WeilData E] {s : n → ℤˣ} {s' : n' → ℤˣ}
  {s₁ : n₁ → ℤˣ} {s₂ : n₂ → ℤˣ} (S : Space E n s) (T : Space E n' s') (a b : AutChar E)
  (𝔪 : Modulus E) (V : Space E n₁ s₁)

/-- Reduction modulo 𝔪, as a homomorphism from the stabiliser of Ô^n in the finite adelic
unitary group to GL_n(O_E/𝔪). -/
def Modulus.reductionK₀ {E : Type} [Field E] [NumberField E] [IsCMField E] {n : _} [Fintype n]
    (𝔪 : Modulus E) := Kf.map n 𝔪.reduction

omit [WeilData E] in
@[simp] lemma Modulus.factor_reductionK₀ {𝔪 𝔫 h} {k : Kf E n} :
    (reductionK₀ 𝔫 k).1.map (factor h) = (reductionK₀ 𝔪 k).1 := by ext; simp [reductionK₀]

attribute [local simp↓] liftFn_apply disjoint_places_star pairTheta modKernel modDatum smul_comp
  pairSign Equiv.prodSumDistrib

attribute [-simp] θ_apply

seal Space.boxProd realBoxProd

/-- The theta kernel θ^{S,T}_{a,b}[Ψ, P](g, (1, h)) for T = I_{n′} the sum of n′ norms and h a
finite adelic point of its unitary group. -/
abbrev modKernelI Ψ P g h := modKernel S (stdSpace E n') a b 𝔪 Ψ P g (1, h)

/-- The datum Ψ ⊗ vac on Hom(S,T), as an element of 𝒲_f: Ψ, a function on matrices modulo 𝔪,
named at the places dividing 𝔪 and applied to the vacuum. -/
def vacuumDatum Ψ := (⟨(S.hom T).name 𝔪.places (𝔪.liftFn (Ψ ∘ vecToMat)) (vacElem _),
  name_mem_finitePart ..⟩ : finitePart _)

/-- For maps e, f of row and column indices, the ℂ-algebra map of polynomial rings sending the
variable X_(i,r,c) to X_(i,e(r),f(c)). -/
abbrev renameRowsCols {ι a b c d} (e : a → c) (f : b → d) :=
  rename (R := ℂ) (Prod.map (@id ι) (Prod.map e f))

/-- The value θ^{S,T}_{a,b}[Ψ, P](g, h) of the theta kernel as a complex bilinear form in the
function Ψ modulo 𝔪 and the polynomial P. -/
def modKernelBilin g
  h := by apply LinearMap.mk₂ ℂ (modKernel S T a b 𝔪 · · g h) <;> simp [Pi.add_comp]

@[simp] lemma modKernelBilin_apply g h Ψ P : modKernelBilin S T a b 𝔪 g h Ψ P =
  modKernel S T a b 𝔪 Ψ P g h := rfl

/-- Twisting the characters: for characters μ, μ′ of [U(1)], θ_{aμ,bμ′}[Ψ,P](g,h) = μ(det h)
μ′(det g)⁻¹ θ_{a,b}[Ψ,P](g,h), for all Ψ modulo 𝔪, polynomials P, and g, h. -/
lemma modKernel_twist μ μ' Ψ P g h : modKernel S T (a * μ) (b * μ') 𝔪 Ψ P g h =
  μ.1 h.det / μ'.1 g.det * modKernel S T a b 𝔪 Ψ P g h := by simp [pairWeil, field]

/-- For integral finite k in U(S) and k′ in U(T), ω_{a,b}(k, k′) sends the datum (Ψ mod 𝔪, v) to
a(det k′) b(det k)⁻¹ times the datum (x ↦ Ψ(k′⁻¹xk), v), with k, k′ reduced modulo 𝔪. -/
lemma pairWeil_modDatum_Kf k k' Ψ v : pairWeil S T a b ((1, k.1), 1, k'.1) (modDatum S T 𝔪 Ψ v) =
  (a.1 (detFin s' k'.1) * (b.1 (detFin s k.1))⁻¹).1 • modDatum S T 𝔪 (Ψ <|
  (𝔪.reductionK₀ k')⁻¹.1 * · * (𝔪.reductionK₀ k).1) v := by
  erw [pairWeil_integrated_fin, pairWeil_name_of_mem, pairWeil_eq_smul_of_projOn_eq ⊤] <;> simp
  congr with x; simpa using! liftIntegralFn_mul (M := idem 𝔪.places • _) _ _
    (Kf.map _ (.id _) k) (Kf.map _ (.id _) k'⁻¹)

lemma modKernel_mul_Kf_left k Ψ P g h : modKernel S T a b 𝔪 Ψ P (g * (1, k.1)) h =
  modKernel S T a b 𝔪 ((b.1 (detFin s k.1) : ℂ)⁻¹ • (Ψ <| · * (𝔪.reductionK₀ k).1)) P g h := by
  simpa using (pairWeil_modDatum_Kf S T a b _ k 1 .. ▸ pairTheta_mul (p := (g, h)) .. :)

lemma modKernel_mul_Kf_right k Ψ P g x h : modKernel S T a b 𝔪 Ψ P g (x, h * k.1) = modKernel S T a
  b 𝔪 ((a.1 (detFin s' k.1) : ℂ) • (Ψ <| (𝔪.reductionK₀ k)⁻¹.1 * ·)) P g (x, h) := by
  simpa using (pairWeil_modDatum_Kf S T a b _ 1 .. ▸ pairTheta_mul (p := (g, x, h)) .. :)

/-- Seesaw identity in the second space: the kernel of (S, T ⊕ V) for characters a, bb′, the
product ΨΨ′ on the two row blocks and PP′, at (g, h ⊕ h′), is θ^{S,T}_{a,b}[Ψ,P](g,h) ·
θ^{S,V}_{a,b′}[Ψ′,P′](g,h′). -/
lemma modKernel_sum_right b' Ψ Ψ' P P' g h h' :
  modKernel S (T.sum V) a (b * b') 𝔪 (fun x ↦ Ψ x.toRows₁ * Ψ'
  x.toRows₂) (renameRowsCols .inl id P * renameRowsCols .inr id P') g (.sum (h, h')) = modKernel S T
  a b 𝔪 Ψ P g h * modKernel S V a b' 𝔪 Ψ' P' g h' := by erw [← theta_boxProd_target signs_comp_refl,
  ← pairWeil_boxProd_target, boxProd_integrated, realBoxProd_polyVector, boxProd_name] <;> aesop

/-- Seesaw identity in the first space: the kernel of (S ⊕ V, T) for characters aa′, b, the
product ΨΨ′ on the two column blocks and PP′, at (g ⊕ g′, h), is θ^{S,T}_{a,b}[Ψ,P](g,h) ·
θ^{V,T}_{a′,b}[Ψ′,P′](g′,h). -/
lemma modKernel_sum_left a' Ψ Ψ' P P' g g' h : modKernel (S.sum V) T (a * a') b 𝔪 (fun x ↦ Ψ
  x.toCols₁ * Ψ' x.toCols₂) (renameRowsCols id .inl P * renameRowsCols id .inr P') (.sum (g, g')) h
  = modKernel S T a b 𝔪 Ψ P g h * modKernel V T a' b 𝔪 Ψ' P' g' h := by erw [← theta_boxProd_source,
  ← pairWeil_boxProd_source, boxProd_integrated, realBoxProd_polyVector, boxProd_name] <;> aesop

/-- The unit of O_E/𝔪 that is the reduction of the chosen element of norm −1 of Ô. -/
def Modulus.normNegOne := Weil.normNegOne.map 𝔪.reduction.1

/-- Negating S conjugates kernels: for some c of modulus one depending only on S and T,
θ^{S⁻,T}_{a⁻¹υⁿ,b⁻¹υ^{n′}}[Ψ′, P̄](g,h) is c times the conjugate of θ^{S,T}_{a,b}[Ψ,P](g,h),
where Ψ′(x) is the conjugate of Ψ(η⁻¹x), η = `Modulus.normNegOne`. -/
lemma exists_modKernel_neg_left : ∃ c, ‖c‖ = 1 ∧ ∀ a b 𝔪 Ψ P g h, conj (modKernel S T a b 𝔪 Ψ P g
  h) = c * modKernel S.neg T (a⁻¹ * upsilonU1 ^ card n) (b⁻¹ * upsilonU1 ^ card n') 𝔪 (conj <| Ψ <|
  𝔪.normNegOne⁻¹ • ·) (map conj P) (.neg g) h := by
  peel exists_theta_negSource S T
  simp_intro ..
  rw [← this, map_smul, ← pairWeil_negSource, map_integrated, map_name]; congr!; ext
  all_goals simp [Std.realMap, isVacuum_realVac (ε := 1).4, map_eval, comp_def, negSource,
    ContinuousAddEquiv.mk',
    smul_comm (idem _), mul_smul_comm, apply_dite conj, apply_ite, holCoord_eq, neg_eq_iff_eq_neg,
    ← Int.units_ne_iff_eq_neg, ↓← mem_integralBox, integralBox, stdLattice, Submodule.smul_mem_iff']
  rcongr; exact .symm (map_mul ..).symm

variable {S T a b 𝔪}

/-- If the ideal 𝔪′ is contained in 𝔪, the datum modulo 𝔪′ given by the pullback of Ψ under
reduction to O_E/𝔪 and by v equals the datum modulo 𝔪 given by Ψ and v. -/
lemma modDatum_factor {𝔪'} h Ψ v : modDatum S T 𝔪' (Ψ <| ·.map (factor h)) v =
  modDatum S T 𝔪 Ψ v := by
  rw [eq_comm, modDatum, ← projOn_vacElem, ← name_boxIndicator, ← name_union,
    Set.union_sdiff_cancel]
  congr with; simp [mem_integralBox, idem_mul_mem_Ô]; split_ifs
  rcongr; simp [vecToMat]; apply reduction_congr; simp [idem_apply]
  repeat grind [not_le_star, places]

/-- The theta kernel θ[Ψ, P](g, h) is unchanged when the coordinates of S and T are relabelled
by sign-compatible bijections e, e′ and Ψ, P, g, h are relabelled accordingly. -/
lemma modKernel_reindex e he e' he' Ψ P g h : modKernel (S.reindex (t := s₁) e he) (T.reindex (t :=
  s₂) e' he') a b 𝔪 (Ψ <| ·.submatrix e' e) (renameRowsCols e' e P) (.reindex e he g)
  (.reindex _ he' h) = modKernel S T a b 𝔪 Ψ P g h := by
  subst_vars; simp [pairWeil, G.det, U.det, ← G.mat.eq_1]
  convert mul_one _
  rw [← (_ : θ _ (ω _ 1 (integrated _ (polyVector _ 1) (name (stdSpace E Empty) _ (𝔪.liftFn 1)
    _))) = 1), ← theta_boxProd (e := .trans (.sumEmpty ..) (e'.prodCongr e)), ← omega_boxProd,
    boxProd_integrated, realBoxProd_polyVector, boxProd_name]; aesop
  all_goals simp [funext_iff, ← ext_iff, hom, Space.reindex, ← map_inv, liftFn_one,
    name_boxIndicator, vacElem_apply_eq_prod_lineTheta, θ_apply, reindex_equiv e, reindex_equiv e']
  aesop

/-- Seesaw identity for I_n = I_{n₁} ⊕ I_{n₂} along a bijection ε: with Ψ, P read on the n₁ rows
and Ψ′, P′ on the n₂ rows, θ^{T,I_n}_{a,bb′}[ΨΨ′, PP′](g, h₁ ⊕ h₂) =
θ^{T,I_{n₁}}_{a,b}[Ψ,P](g,h₁) · θ^{T,I_{n₂}}_{a,b′}[Ψ′,P′](g,h₂) for finite adelic h₁, h₂. -/
lemma modKernelI_block (ε : n₁ ⊕ n₂ ≃ n) b' Ψ Ψ' P P' g h h' : modKernelI T a (b * b') 𝔪 (fun x ↦ Ψ
    (x.submatrix (ε ∘ .inl) id) * Ψ' (x.submatrix (ε ∘ .inr) id)) (renameRowsCols (ε ∘ .inl) id P *
  renameRowsCols (ε ∘ .inr) id P') g (U.block ε (h, h')) = modKernelI T a b 𝔪 Ψ P g h * modKernelI T
  a b' 𝔪 Ψ' P' g h' := by erw [← theta_boxProd_target (e := ε), ← pairWeil_boxProd_target,
  boxProd_integrated, realBoxProd_polyVector, boxProd_name] <;> aesop (add simp (reindex_equiv ε))

open Kronecker Splitting MatMul

attribute [-simp] map_inv₀ inv_mul_cancel₀ Unitary.mul_star_self_of_mem Algebra.smul_mul_assoc
  map_zero

variable {E : _} [Field E] [CMType E] [WeilData E] {n n' r r' : Type} [Fintype n] [Fintype n']
  [Fintype r] [Fintype r'] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {t' : r' → ℤˣ} {W : Space E n s}
  {W' : Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit)
  (X : V'.Splitting V Unit)

/-- For lines split off W' and V', the operator from data of Hom(W',V') to data of Hom(W,V):
translate by a rank-one map scaled by a, then take both zero terms; β selects one of two
models. -/
def lineTerm (β : Bool) (a : 𝔸 E) :=
  ite β ((X.homTarget _).zeroTerm ∘L A.sourceTerm _ (a • X.kAdelic)) ((A.homSource _).zeroTerm ∘L
  (X.homTarget _).zeroTerm ∘L ϱ _ (matToVec (a • X.lAdelic * A.lCoord)))

attribute [local simp] pow_add lineTerm sourceTerm removePlanes

/-- If u = 1 or rk V = rk W, the Levi elements (u, g), (c, h) pass through `lineTerm`:
with x = cu, ξ becomes ξx for β true and ξx̄⁻¹ otherwise, up to `AutChar.spaceChar` a (rk W) at
x⁻¹ and powers of |u|, |x|. -/
lemma lineTerm_pairWeil_levi {u} (hu : u = 1 ∨ card r = card n) a β ξ g c h f : let x := c * u
  lineTerm A X β ξ (pairWeil _ _ (a * upsilonU1) (a * upsilonU1) (A.levi (.scalar _ u, g),
    lineLevi X (c, h)) f) = (√(ideleAbs u) ^ (2 * card r + 2) /
    ((a.spaceChar (card n)).1 x * √(ideleAbs x) ^ (card n + ite β 0 2)) :
    ℂ) • pairWeil W V a a (g, h) (lineTerm A X β (ξ * ite β ↑x (star ↑x⁻¹)) f) := by
  rcases @homTarget_zeroTerm_pairWeil (hk := X.levi_mul_kAdelic (.scalar _ c⁻¹) h),
    @homSource_zeroTerm_pairWeil (hk := A.levi_mul_kAdelic (.scalar _ u) g)
  revert β; simp_all [lineLevi, A.card_eq, X.card_eq, Pi.star_def, smul_smul, varrho_pairWeil,
    pow_mul', conjTranspose_coord, G.mat_inv, ← smul_eq_diagonal_mul, mul_pow,
    AutChar.spaceChar, -matToVec_smul, Splitting.levi, -Subtype.forall]
  cases hu <;> simp [*] <;> constructor <;> field_simp <;> ring

attribute [local simp] kAdelic lAdelic iAdelic kCoord lCoord iCoord Space.map_J Splitting.symm
  hom_point_inv_mul_kronecker Splitting.comp mixedTerm conjTranspose_nonsing_inv

attribute [local simp ←] map_inv

/-- Poisson summation: the sums over ξ in E of θ of the terms `lineTerm` agree in both
models. Each model is the mixed Schrödinger model of one splitting of Hom(W',V') over
Hom(W,V) with explicit frames, adapted when A and X are. -/
lemma tsum_lineTerm [hA : IsBaseAdapted A] [hX : IsBaseAdapted X] : ∀ β,
  (∀ f, ∑' ξ, θ _ (lineTerm A X true (toAdele ξ) f) = ∑' ξ, θ _ (lineTerm A X β (toAdele ξ) f)) ∧ ∃ᵉ
  (D) (u : GL ((Unit × (n ⊕ Unit) ⊕ r × Unit) ⊕ Unit × _) _), (∀ a, lineTerm A X β a = D.mixedTerm
  (u⁻¹.1ᴴ *ᵥ (0 ⊕ᵥ matToVec (scalar _ a)))) ∧ IsAdapted D 1 u ∧ D.frameAt 1 u = ((((X.lAdelic ⊗ₖ
  fromCols A.iCoordᵀ A.kCoordᵀ).fromCols (X.iAdelic ⊗ₖ A.kCoordᵀ)).fromCols (cond β (X.kAdelic ⊗ₖ
  A.kCoordᵀ) (X.lAdelic ⊗ₖ A.lCoordᵀ))).fromCols (((X.kAdelic ⊗ₖ fromCols (A.iAdelicᴴ * stdForm E
  s')ᵀ A.lCoordᵀ).fromCols ((X.iAdelic * stdForm E t) ⊗ₖ A.lCoordᵀ)).fromCols (cond β
  (X.lAdelic ⊗ₖ A.lCoordᵀ) (X.kAdelic ⊗ₖ A.kCoordᵀ)))).fromCols (X.iAdelic ⊗ₖ A.iCoordᵀ) := by
  refine' let k := A.kᴴ * W'.J; let l := A.lᴴ * W'.J; let m := W.J⁻¹ * A.iᴴ * W'.J
        let S := removePlanes ..; let T β := cond β S S.symm
          let D := Splitting.mk (fromCols (X.k ⊗ₖ (fromRows (W.J * m) k)ᵀ) ((X.i * V.J⁻¹) ⊗ₖ kᵀ))
            (fromCols (X.l ⊗ₖ (fromRows m l)ᵀ) (X.i ⊗ₖ lᵀ))
            (fromCols (fromCols (X.k ⊗ₖ lᵀ) (X.l ⊗ₖ kᵀ)) (X.i ⊗ₖ mᵀ)) ..
          have h β a : lineTerm A X β a =
            (T β).mixedTerm (matToVec (scalar _ a)) ∘L D.zeroTerm := ?a
          fun β ↦ ⟨fun f ↦ by simpa [↓h, diagonal_unique, ← (@Equiv.piUnique (_ × _) (.mk' _)
              _).symm.tsum_eq] using! (S.hasSum_theta_mixedTerm _).tsum_eq.trans ((T
            β).hasSum_theta_mixedTerm _).tsum_eq.symm,
          let f x := Prod.map (.inl ∘ x) (.inr ⊕ᵥ .inl ∘ x) ⊕ᵥ .map .inr (.inl ∘ x) ⊕ᵥ
            .map (.inl ∘ cond β (.swap ∘ x) x) (.inl ∘ cond β x (.swap ∘ x))
          ⟨D.comp (T β), blockGL (blockGL (kroneckerGL 1 (transposeGL (blockGL (star W.x, 1))),
            adaptedHomBasis _ V), 1), fun _ ↦ ?b, .of_eq_submatrix_mul (.mul (.of_stdForm (s' ·.2))
            (hX.1.kronecker hA.1)) (f .inl ⊕ᵥ f .inr ⊕ᵥ .map .inr .inr) (.of_stdForm
            (((s ⊕ᵥ 1) ·.2) ⊕ᵥ 1 ⊕ᵥ 1 ⊕ᵥ (1 ⊕ᵥ (t ·.1) ⊕ᵥ 1) ⊕ᵥ (s ·.2))) (.trans ?c ?e) ?f, ?c⟩⟩
  case e | f => revert β; simp [-kAdelic, -lAdelic, Injective, ← ext_iff,
    stdForm] <;> ac_nf <;> grind
  case' c => cases β <;> simp +zetaDelta [adaptedHomBasis, Splitting.frameAt, kroneckerGL,
    map_J_inv, -coe_units_inv, star, Space.ratMap]
  case' a | b => ext1; cases β <;> simp +zetaDelta [← zeroTerm_rho_iAdelic,
    ← zeroTerm_comp, -coe_units_inv, kronecker_mulVec_eq_matToVec,
    ← smul_eq_mul_diagonal, -fromRows_map] <;> congr 1 <;> apply zeroTerm_congr
  repeat simp [hom, hypSum, homSource, homTarget, conjTranspose_J, ← W'.J⁻¹.mul_assoc,
    ← Matrix.mul_assoc _ (i _), -Matrix.mul_assoc] <;> simp [entrywise, A.card_eq,
    X.card_eq] <;> ring
end
end

-- part: Lib.Weil.DualPair.ThetaIntegralLaws
section
/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Name for the real slice of a datum in the mixed model. Real part of the slice at an
isotropic line in the constant term. Basic laws of theta integrals: equivariance, linearity,
automorphy, boundedness for full-rank data. -/

/-- The slice of a real datum for (X,V) at the real part of the adelic matrix x: its value in the
mixed model of D, a real datum for (W₁,V). -/
noncomputable def realSlice {E} [Field E] [CMType E] [WeilData E] {n a b m} [Fintype n]
  [Fintype a] [Fintype b] [Fintype m] {s t r} {X : Space E m r} {W₁ : Space E n s}
  (D : X.Splitting W₁ b) (V : Space E a t) [IsBaseAdapted D] (x : Matrix a b (𝔸 E)) : PairFock E r t
  →L[ℂ] PairFock E s t := (isAdapted_homSource D V).mixedModel.slice fun p ↦ (matToVec x p.2).1 p.1

/-- The real counterpart of `lineTerm`: the slice, in the mixed model of the adapted
splitting chosen from `tsum_lineTerm`, at the point with last coordinates a ∈ ℂ^f and
others 0. -/
@[irreducible] noncomputable def lineTermReal {E} [Field E] [CMType E] [WeilData E] {n n' r r'}
  [Fintype n] [Fintype n'] [Fintype r] [Fintype r'] {s s' t t'} {W : Space E n s} {W' :
  Space E n' s'} {V : Space E r t} {V' : Space E r' t'} (A : W'.Splitting W Unit) (X :
  V'.Splitting V Unit) [IsBaseAdapted A] [IsBaseAdapted X] β (a : _ → ℂ) := (tsum_lineTerm A X
  β).2.choose_spec.choose_spec.2.1.mixedModel.slice fun (x, y) ↦ a x * y.isRight.toNat

open Matrix MeasureTheory Space CompactlyCoherentSpace
variable {E : Type} {n} {n'} {F : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype n']
  {s : n → ℤˣ} {s' : n' → ℤˣ} {μ : NumberField.InfinitePlace E → ℤ} (S : Space E n s)
  (T : Space E n' s') {v} [SemilocalField F] {A : Set (FinPlace E)} {φ : Matrix n' n F → ℂ}
  {π : 𝔸f E →+* F} {U : Set (Matrix n' n F)} (r : ReadsAt A π) (𝔠 : SplitTameChar E μ)

omit [WeilData E] in
lemma atPlaces_star {P} (g : Gf E n) : (g.1.1.map ((evalPlaces P).comp (starRingEnd _)))ᵀ =
  (atPlaces P g⁻¹).1 ∧ g.1.1.map (evalPlaces P) = (atPlaces P g).1 :=
  ⟨congr(map $(_root_.U.inv_val_eq_conjTranspose g) (evalPlaces P)).symm, rfl⟩

omit [WeilData E] [Fintype n] [Fintype n'] in
lemma ReadsAt.isSchwartzBruhat : ReadsAt A π → φ ∈ schwartzBruhat U →
  IsSchwartzBruhat A (φ <| vecToMat · |>.map π) | ⟨_, _, _, σ, _, k, h⟩, hφ => ⟨by
  simp [vecToMat, Matrix.map, ← h, k], hφ.1.comp_continuous (by continuity), (σ ∘ matToVec ·) '' _,
  hφ.2.1.image (by fun_prop [matToVec]), fun _ ↦ (⟨_, subset_closure ·, funext (by tauto)⟩)⟩

/-- The theta integral over [U(T)] of the datum v ⊗ Φ at the ramified places of 𝔠, both
characters being ν⁻¹υ^⌊n/2⌋, n = rk S. -/
noncomputable abbrev thetaLarge v Φ :=
  thetaIntegral S T (rankTwist 𝔠.ν⁻¹ n) (rankTwist 𝔠.ν⁻¹ n) (localDatum S T v Φ 𝔠.readsAt)

/-- There are B and C with |θ^{S,T}_{α,β}(f)(g,h)| ≤ C·ht(g)^B for all characters α, β and all
g, h: polynomial growth in g, uniformly in h. -/
def IsTargetBounded f := ∃ B C, ∀ α β g h, ‖pairTheta S T α β f (g, h)‖ ≤ C * S.height g ^ B

lemma exists_linear_thetaIntegral α β : ∃ Λ : _ →ₗ[ℂ] _, ∀ {f}, IsTargetBounded S T f → Λ f =
  thetaIntegral S T α β f := (LinearMap.exists_extend (K := ℂ) (p := ⟨⟨⟨(Integrable (ε := ℂ) · _),
  .add⟩, integrable_zero ..⟩, .smul⟩) ⟨⟨(integral _ ·.1), (integral_add ·.2 ·.2)⟩,
  (integral_smul · ·.1)⟩).imp' (.pi fun g ↦ · ∘ₗ .pi (θ _ ∘L pairWeil S T α β ⟨g, ·⟩)) fun _ h _ ⟨_,
  _, b⟩ ↦ funext (DFunLike.congr_fun h ⟨_, .of_bound (by fun_prop) _ <| .of_forall <| b _ _ ·⟩)

instance : Nontrivial (LocProd 𝔠.S) := Pi.nontrivial_at 𝔠.nonempty.coe_sort.some

variable {S} {T} {α : AutChar E} {β : AutChar E} {f : 𝒮 (S.hom T)} {g : Gf E n} {h : Gf E n'}

lemma ReadsAt.pairWeil_localDatum_of_mem_Kf (hφ : φ ∈ schwartzBruhat U) (hg : g ∈ _root_.Kf ..)
  (hh : h ∈ _root_.Kf ..) : pairWeil S T α β (g, h) (localDatum S T v φ r) = (α.1 (detFin s' h) *
  (β.1 (detFin s g))⁻¹).1 • localDatum S T v (φ <| h⁻¹.1.1.map π * · * g.1.1.map π) r := by simp_all
  [pairWeil_name_of_mem r.1 (hΨ := r.isSchwartzBruhat hφ), pairWeil_eq_smul_of_projOn_eq ⊤]

lemma thetaIntegral_pairWeil p g : thetaIntegral S T α β (pairWeil S T α β p f) g =
  thetaIntegral S T α β f (g * p.1) :=
  by simpa [lift] using! ((pairThetaKer ..).swap.lift_equivariant (isAutomorphic_const _ 1) ..).symm

lemma IsTargetBounded.isAutFunction_thetaIntegral : IsTargetBounded S T f → _root_.IsAutFunction S
  (thetaIntegral S T α β f) | ⟨_, C, h⟩ => ⟨isCoherentWith.continuous_iff.2 fun _ a ↦
  continuousOn_of_dominated (by fun_prop) (fun _ _ ↦ .of_forall fun _ ↦ by grw [h,
  (exists_mul_height_pow_le a _).choose_spec _ 1] <;> simp [*]) (by simp) (.of_forall
  (by fun_prop)), by simp_all [thetaIntegral, pairTheta, (pairThetaKer ..).theta_rat_mul]⟩

lemma ReadsAt.isTargetBounded [Nontrivial F] (hv : IsRapidDatum v) (hφ :
  φ ∈ schwartzBruhat (HasLeftInv ·ᵀ)) : IsTargetBounded S T (localDatum S T v φ r) :=
  (pairTheta_decay_of_onto S T 1 1 π r.1 (r.isSchwartzBruhat hφ) (fun _ ↦ @hφ.2.2 _) 0).imp
  fun _ ⟨_, _, h⟩ ↦ ⟨_, by simpa [pairWeil, pairTheta, hv _] using h v⟩
end
