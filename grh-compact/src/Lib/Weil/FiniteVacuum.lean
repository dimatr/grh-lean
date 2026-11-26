import Lib.Adelic.SpaceGram
import Lib.GaloisRep.UpsilonValues
import Lib.Weil.AdeleSelfDual

section
/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: The element of an adelic unitary group with a given isometric matrix. -/


variable {E} [Field E] [NumberField E] [NumberField.IsCMField E] {n} [Fintype n] {s : n → _}

/-- The element of the adelic unitary group of signs s given by an adelic matrix m with m*εm =
ε, ε the standard form. -/
noncomputable def G.ofMat m h := (toUnitary.symm (U.of isUnit_stdForm m h) : G E s)

@[simp] lemma G.mat_ofMat m h : (ofMat m h : G E s).mat = m := rfl
end

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Adelic vacuum function and Heisenberg cocycle of the standard hermitian form. -/

open Matrix Real WeilData

/-- The vacuum on adelic vectors: exp(−π ∑_{i,τ} Im(τȷ)|x_{i,τ}|²) times ψ_f(½c₀ȷ x_f*x_f) if
the finite part x_f lies in αÔ^n, and 0 otherwise. -/
noncomputable def vacuumFn {E} [Field E] [CMType E]
  [WeilData E] {n} [Fintype n] (x : n → 𝔸 E) := (-∑ i, ∑ w, π * (Φ w j).im * ‖(x i).1 w‖ ^ 2).exp *
  ite (∀ i, α⁻¹.1 * (x i).2 ∈ Ô E) (ψf E ((traceOne * j / 2 : E) * ∑ i, star (x i).2 * (x i).2)).1 0

/-- The Heisenberg datum on adelic n-space with bicharacter β(x,y)=ψ(½ȷ h(y,x)), h being the
standard hermitian form of signs s. -/
noncomputable def adelicHeis E [Field E] [CMType E]
    [WeilData E] {n} [Fintype n] (s : n → ℤˣ) : Heisenberg (n → 𝔸 E) := by refine ⟨fun x y ↦
  stdAddChar E (toAdele (j / 2) * star y ⬝ᵥ stdForm E s *ᵥ x), ?_, ?_, fun x ↦
  stdAddChar_half (_ : 𝔸 E) ▸ ?_, ?_, .subtype_val (by fun_prop)⟩ <;> simp [mul_add, neg_div,
  AddChar.map_add_eq_mul, ← star_dotProduct, star_mulVec_dotProduct, Circle.norm_coe]
end

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Finite adelic Heisenberg group, self-dual lattice, additive character, semicharacter and
vacuum. -/

noncomputable section

namespace stdLattice

open NumberField Matrix AddChar Circle WeilData
variable (E ι : Type _) [Field E] [CMType E] [WeilData E] [Fintype ι]

/-- The standard lattice Ô^ι, as an additive subgroup of the finite adelic vectors indexed by ι. -/
def _root_.stdLattice (E ι : Type _) [Field E] [NumberField E] :
    AddSubgroup (ι → 𝔸f E) := (intVectors (Ô E) ι).toAddSubgroup

/-- The complex-valued additive character u ↦ ψ_f(ȷαᾱu) of the finite adeles of E, with ȷ and α
from the Weil data. -/
def psi₀ := coeHom.compAddChar ((ψf E).mulShift (algebraMap E _ j * α.1 * star α.1))

variable {E ι}

/-- The integer c₀ of the Weil data (c₀ + c̄₀ = 1), viewed as a finite adele of E. -/
def traceOneAdele : 𝔸f E := (WeilData.traceOne : E)

/-- The number ½, viewed as a finite adele of E. -/
def half {E : Type _} [Field E] [NumberField E] : 𝔸f E := (2⁻¹ : E)

lemma psi₀_apply z : psi₀ E z = ψf E (algebraMap E _ j * α.1 * star α.1 * z) := rfl

@[simp] lemma norm_psi₀ z : ‖psi₀ E z‖ = 1 := norm_coe _

@[fun_prop] lemma continuous_psi₀ : Continuous (psi₀ E) :=
  continuous_ψf.subtype_val.comp (continuous_const_mul _)

lemma psi₀_star z : psi₀ E (star z) = psi₀ E (-z) := by simp [psi₀, ψf_star (-_), mul_right_comm]

/-- Self-duality of Ô: a finite adele z satisfies ψ₀(zu) = 1 for all u in Ô if and only if z
lies in Ô, where ψ₀ = ψ_f(ȷαᾱ·). -/
lemma forall_psi₀_mul_eq_one_iff z : (∀ u ∈ Ô E, psi₀ E (z * u) = 1) ↔
  z ∈ Ô E := by simpa [psi₀_apply, ← mul_rotate' _ _ z, coe_eq_one, forall_ψf_mul_eq_one] using
  ((exists_reduction_and_idele_generator differentIdeal_ne_bot).elim fun _ ⟨_, _, t,
  _, h, H⟩ ↦ (H _).trans (by simp [mem_Ô, h, -WithZero.inv_exp, WithZero.exp_neg,
    by simpa using ‹WeilData E›.self_dual]))

lemma traceOneAdele_mem : traceOneAdele ∈ Ô E := algebraMap_mem_Ô.2 isIntegral_traceOne

/-- The element c₀ of the Weil data, viewed as a finite adele, satisfies c₀ + c̄₀ = 1. -/
@[simp] lemma traceOneAdele_add_star : traceOneAdele + star traceOneAdele = (1 :
  𝔸f E) := by simp [traceOneAdele, WeilData.traceOne, ← map_add, ← add_div]

omit [WeilData E] in
lemma two_mul_half : 2 * half = (1 : 𝔸f E) := by norm_num [half, two_mul, ← map_add]

omit [WeilData E] in
lemma star_half : star half = @half E .. := by simp [half]

attribute [grind .] traceOneAdele_add_star two_mul_half star_half

lemma psi₀_eq_one_of_mem {o} : o ∈ Ô E →
  psi₀ E o = 1 := by grind [forall_psi₀_mul_eq_one_iff, (Ô E).one_mem]

lemma psi₀_congr {a b o} t : o ∈ Ô E → a = b + (t + star t) + o → psi₀ E a = psi₀ E b := by
  simp_all [map_add_eq_mul, psi₀_star, ← map_add_eq_mul _, psi₀_eq_one_of_mem]

/-- For a finite adelic vector x, the complex number sc(x) = ψ_f(½c₀ȷαᾱ x*x). -/
def semichar (x : ι → _) := psi₀ E (traceOneAdele * half * star x ⬝ᵥ x)

/-- The finite vacuum: the function on finite adelic vectors equal to ψ_f(½c₀ȷαᾱ x*x) for x in
Ô^ι and to 0 otherwise. -/
def finVac x := ite (x ∈ stdLattice E ι) (delta% semichar x) 0

variable (E ι)

/-- The Heisenberg datum on finite adelic vectors indexed by ι with bicharacter β(x,y) =
ψ_f(½ȷαᾱ y*x). -/
def finHeis : Heisenberg (ι → 𝔸f E) := by refine ⟨fun x y ↦ psi₀ E (half * star y ⬝ᵥ x), ?_, ?_,
  fun x ↦ (psi₀ E).2 ▸ psi₀_congr (traceOneAdele * half * star x ⬝ᵥ x) (zero_mem
  _) ?_, ?_, by fun_prop⟩ <;> simp [mul_add, map_add_eq_mul, half, ← star_dotProduct, ← add_mul]
end stdLattice
end
end

section
/-! Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: Self-dual lattice gives a vacuum for the finite Heisenberg group (lattice model). -/

namespace stdLattice

open NumberField MeasureTheory Measure Matrix AddChar Heisenberg
section

variable {E ι : Type _} [Field E] [NumberField E]

lemma isOpen_stdLattice [Fintype ι] : (stdLattice E ι).IsOpen := isOpen_intVectors isOpen_Ô

end

variable {E ι : Type _} [Field E] [CMType E] {x y z : ι → 𝔸f E}

lemma mem_stdLattice : x ∈ stdLattice .. ↔ ∀ i, x i ∈ Ô E := .rfl

lemma isCompact_stdLattice : IsCompact (stdLattice E ι).carrier := isCompact_pi_infinite fun _ ↦
  isCompact_Ô

variable [Fintype ι]

variable (E) in
/-- The Haar measure on n-tuples of finite adeles of E that gives the lattice Ô^n mass one. -/
noncomputable def _root_.latticeMeasure n [Fintype n] : Measure (n → 𝔸f E) := addHaarMeasure
  ⟨⟨stdLattice E n, isCompact_stdLattice⟩, by simp [isOpen_stdLattice.interior_eq]⟩ deriving
  IsAddHaarMeasure

@[simp] lemma _root_.latticeMeasure_stdLattice : latticeMeasure E ι (stdLattice E ι) = 1 :=
  addHaarMeasure_self

@[simp] lemma star_mulVec_dot_mulVec (g : Gf E ι) x y : star (g.1.1 *ᵥ x) ⬝ᵥ g.1.1 *ᵥ y =
  star x ⬝ᵥ y := by simpa using U.form_mulVec_mulVec g ..

attribute [local simp] mul_mem star_mem_Ô finVac add_mem_cancel_right add_left add_right

omit [Fintype ι] in
lemma smul_mem_stdLattice {r} : r ∈ Ô E → x ∈ stdLattice .. →
  r • x ∈ stdLattice .. := by simp_all [mem_stdLattice]

lemma dot_mem : y ∈ stdLattice .. → z ∈ stdLattice .. → star z ⬝ᵥ y ∈ Ô E :=
  (sum_mem <| by simp [· _, · _])

variable [WeilData E]

lemma semichar_add x y : semichar x * semichar y * (finHeis E ι).β x y = psi₀ E (star traceOneAdele
  * star y ⬝ᵥ x) * semichar (x + y) := by simp [semichar, finHeis, ← map_add_eq_mul]; grind
  [psi₀_congr (traceOneAdele * half * star x ⬝ᵥ y) (zero_mem _), star_mul', star_dotProduct]

lemma finVac_add x : y ∈ stdLattice .. → finVac x * finVac y * (finHeis ..).β x y =
  finVac (x + y) := by simp_all [↓← semichar.eq_1, semichar_add, psi₀_eq_one_of_mem ∘ mul_mem _,
  dot_mem, traceOneAdele_mem]

lemma semichar_mul_self (h : y ∈ stdLattice ..) :
  semichar y * semichar y = 1 := by simpa [h, semichar] using finVac_add (-y) h

lemma mem_stdLattice_iff_psi₀ : x ∈ stdLattice .. ↔ ∀ y ∈ stdLattice .., psi₀ E (star y ⬝ᵥ x) = 1 :=
  ⟨by grind [psi₀_eq_one_of_mem, dot_mem], fun h i ↦ (forall_psi₀_mul_eq_one_iff _).1 fun _ k ↦ by
    simpa [mul_comm] using h _ (smul_mem_stdLattice (star_mem_Ô k) (single_mem_intVectors i))⟩

lemma _root_.integral_psi₀_stdLattice x : ∫ y in stdLattice E ι, psi₀ E (star x ⬝ᵥ y)
  ∂latticeMeasure E ι = ite (x ∈ stdLattice ..) 1 0 := by simp [↓setIntegral_char isOpen_stdLattice,
  map_add_eq_mul, real_def, star_dotProduct x, psi₀_star, map_neg_eq_inv, ← mem_stdLattice_iff_psi₀]

instance isVacuum_finVac :
  (finHeis E ι).IsVacuum (latticeMeasure ..) finVac := have ⟨Z, n⟩ : _ ∧ _ := by aesop
  have c :=
    IsClopen.continuous_indicator ⟨isCompact_stdLattice.isClosed, isOpen_stdLattice⟩ (by fun_prop)
  ⟨c, by simp, n, by grind [→ semichar_mul_self, mul_self_eq_one_iff, finVac, semichar], fun y x ↦
  by rw [← setIntegral_eq_integral_of_ae_compl_eq_zero, setIntegral_congr_fun
      isOpen_stdLattice.measurableSet fun z ↦ ?_,
    integral_const_mul (finVac (x - y) / (finHeis ..).β x y), integral_psi₀_stdLattice
    x] <;> simp_all [-finVac, ↓sub_add_eq_sub_sub_swap, sub_eq_add_neg, add_comm x,
    ← finVac_add]; grind [map_nsmul_eq_pow _ 2 (half * star x ⬝ᵥ z), → semichar_mul_self, finVac,
    semichar, β_mul_β, finHeis], HasCompactSupport.integrable (.intro isCompact_stdLattice Z) c⟩
end stdLattice
end
