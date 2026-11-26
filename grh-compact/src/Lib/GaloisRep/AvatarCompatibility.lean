import Lib.GaloisRep.WeightCongruence
import Lib.GaloisRep.Conjugation
import Lib.GaloisRep.HeckeOperatorOfFunction
import Lib.GaloisRep.LocalCharacters
import Lib.PadicHodge.HodgeTateFrame
import Lib.GaloisRep.ArtinMapAtPlace
import Lib.Adelic.GreenTau
import Lib.GaloisRep.BaseChangeEigenchar
import New.Weil.PairSumNegation
import Lib.GaloisRep.SortedExponents
import Lib.GaloisRep.ShintaniLifting
import Lib.Shimura.UniversalPoints
import Lib.Shimura.UniversalFamily
import Lib.GaloisRep.MarkedPairs
import Lib.GaloisRep.WeightParameter
import Lib.GaloisRep.Lefschetz
import Lib.GaloisRep.SplitPlaceCount
import Lib.Cohomology.GaloisRep

section
/-! Part of: Grunwald–Wang theorem in prime exponent (known result; see
Lib.GaloisRep.Main.AttachedDeterminant).

This file: Grunwald's theorem in prime exponent over a totally complex field; symmetrised
characters. -/

open Subgroup

variable {E : Type} [Field E] [NumberField E] [Algebra E Ω]

/-- Grunwald in prime exponent: for E totally complex, S finite, ψ a ℚ/ℤ-valued character of the
finite ideles with open kernel, pψ = 0, some Galois character χ, pχ = 0, has χ∘Art = ψ on
E_u^× for u ∈ S and on local units where N u is not prime.

Known result: Grunwald–Wang theorem in prime exponent. -/
lemma grunwald [NumberField.IsTotallyComplex E] {p S} (hp : p.Prime) (hS : Set.Finite S)
    (ψ : _ →* _) (c : ψ.ker.IsOpen) (t : ∀ a, ψ a ^ p = 1) : ∃ χ, p • χ = 0 ∧ ∀ u x, u ∈ S ∨
    ¬u.q.Prime ∧ Valued.v x.1 = 1 → QZChar.abelianLift χ (artinMap Gal(Ω/E) (locIdele u x)) =
  ψ (locIdele u x) := by
  obtain ⟨_, T, f, _, -, g⟩ := Fact.mk hp, exists_sup_idelesUnitOff_eq_top hS
  let N := (@powMonoidHom (T.unit E) _ p).range
  choose r hr using IsAIC.exists_pow_eq (A := Ω) p
  choose v _ _ A H σ K F using fun q : {q : _ ⧸ N // ψ (principalIdele q.out) ≠ 1} ↦
    chebotarev (.sdiff Fact.out (isClosed_setOf_smul _ (· = _))) (Set.not_subset.1 fun h ↦
    ((pow_mem_range_pow_of_coprime (.of_dvd_left (by grw [finrank_fixedFieldOf, index_ker,
    card_subgroup_dvd_card, Nat.card_units]) (by simp [hp.one_le])) _).1
    ⟨Algebra.norm E (⟨_, (h ·.2)⟩ : fixedFieldOf (cycCharMod Ω p).ker), (map_pow ..).symm.trans
    ((congrArg _ (by bound)).trans (Algebra.norm_algebraMap q.1.out.1.1))⟩).elim
    fun z e ↦ q.2 ((Units.ofPow _ z hp.ne_zero e ^ p).ext e ▸ by simp [t])) f
  let R q := (powMonoidHom p).range.comap (ideleAt (v q))
  obtain ⟨_, θ, k, hB⟩ := N.finiteIndex_iff.2 (index_range_pow_eq
    (mod_cast @cokerKerIndex_eq_pow_finrank _ _ _ _ (SUnit.dirichlet_unit_theorem f).1)).1,
    exists_monoidHom_extend (d := by exact instDivisibleByQZInt) (idelesUnitOff T ⊓ iInf R).subtype
    (ψ.domRestrict _) principalIdele.range (by
    simp; rintro _ a b x ⟨⟩
    obtain ⟨⟨_, y, ⟨⟩⟩, e⟩ := QuotientGroup.mk_out_eq_mul N ⟨x, by aesop⟩
    exact by_contra fun _ ↦ (K ⟨_, e ▸ by simpa [t]⟩).2 ((H _).smul_root_eq_of_local_pow
      (congr($e.1 ∈ (R _).comap _).mpr (mul_mem (b ..) (by simp [R]))) (hr _) _ (F _).1.1 (K _).1))
  have ⟨μ, C, h⟩ := exists_comp_artinMap Gal(Ω/E) θ (.of_isOpen_ker _ ((_ ⊓ _ ⊓ iInf R).isOpen_mono
    (by simp_all [LE.le]) ((c.inter (isOpen_idelesUnitOff T)).and
    (coe_iInf.substr (isOpen_iInter_of_finite fun q ↦ (isOpen_of_forall_pow_mem hp.ne_zero
    (MonoidHom.mem_range.2 ⟨·, rfl⟩)).preimage_of_continuous))))) (k ⟨·, rfl⟩)
  use ⟨μ, C, μ.2⟩,
    Subtype.ext (funext (artinMap_surjective _ ⟦·⟧ |>.elim (congr($(h · _ ·) ^ p).trans
    (sup_le (c := (θ ^ p).ker) (by simp_all [LE.le]) (by simpa [t] using hB ⟨· ^ p, by simp [R,
    pow_mem ·]⟩) (g.ge ⟨⟩))))), fun w x _ ↦ .trans (by rcases _ : artinMap _ _; tauto) (hB ⟨locIdele
    w x, by simpa +contextual [← and_forall_ne w, R, show ∀ q, v q ≠ w by grind] using by tauto⟩)

variable [NumberField.IsCMField E] (χ : QZChar Gal(Ω/E))

/-- For a character χ of the absolute Galois group of a CM field, the character g ↦ χ(g) +
χ(g^c), g^c the conjugate of g by complex conjugation (`conjGal`). -/
noncomputable abbrev QZChar.symmetrise := χ + comap ⟨_, continuous_conjGal⟩ χ

/-- For a ℚ/ℤ-valued character χ of Gal(Ω/E), the character exp(2πi χ∘Art) of the finite ideles
of E. -/
noncomputable abbrev QZChar.ideleChar := QZ.expUnit.comp ((abelianLift χ).comp (artinMap _))

lemma QZChar.abelianLift_symmetrise a : abelianLift (symmetrise χ) (artinMap _ a) =
  abelianLift χ (artinMap _ a) * abelianLift χ (artinMap _ (star a)) := by
  rcases h : artinMap _ a; exact artinMap_star _ h ▸ rfl
end

section
/-! In one step of a known theorem
(Galois representations for definite unitary groups),
degree-n polynomials kill most Frobenius elements and a cocharacter with very different exponents
forces rank n. In the literature, Frobenius polynomial relations on a dense set determine a
representation when the n-dimensional one is known and large. Related work: Boston–Lenstra–Ribet
1991; Nekovář, Eichler–Shimura relations and semisimplicity, 2018; Fayad–Nekovář 2019; Harris–Taylor
2001, VII.1.8.

Part of: ℓ-adic avatar of an algebraic Hecke character and its local behaviour (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Degree-n killing polynomials and free cocharacter weights force rank n and characteristic
polynomials. Twisting a Galois representation by an algebraic Hecke character shifts weights and
Hecke polynomials. Sum of distinct irreducible constituents keeps goodness, occurring weights and
killing polynomial. -/

section

attribute [-simp] Matrix.map_mul LaurentPolynomial.single_eq_C_mul_T LaurentPolynomial.T_pow
  det_classical

open Matrix MvPolynomial Polynomial Finset Algebra Fintype Submodule Function ConjAct
  LaurentPolynomial Fin Filter
variable {k K N R S A : Type} [NormedField k] [Fintype N] [CommRing R] [CommRing S] {m n}
  {e : Fin n → ℤ} (y : Matrix N N R) [NormedField K] [NormedAlgebra K k] [CommRing A] [Algebra A R]
  [Algebra A S]

attribute [local simp high] mvPolynomialX_mapMatrix_aeval Matrix.sum_apply coeff_X_mul' comp_def sq
  units_smul_def mul_assoc LaurentPolynomial.algebraMap_apply map_mul ofId
  Finsupp.weight_single isHomogeneous_C_mul_X IsHomogeneous.sum IsHomogeneous.mul

/-- For a square matrix y and m positions a(i), the determinant of the m×m matrix whose (i,j)
entry is the a(i) entry of y^j, 0 ≤ j < m. -/
noncomputable abbrev powMinor m a := (of (flip (uncurry <| y ^ @Fin.val m ·) ∘ a)).det

@[simp] lemma map_powMinor a (φ : R →ₐ[A] S) : φ (powMinor y m a) = powMinor (φ.mapMatrix y) m a :=
  by simp [powMinor, ↓← map_pow, φ.map_det]; rfl

/-- Let e be free integers indexed by n, c: N → n surjective, x ∈ GL_N(k), m ≤ |n|+1. If all
`powMinor` of order m of diag(T^{e∘c})x vanish in k[T,T⁻¹], then |n| < m and x⁻¹ is
scalar on each fibre block of c. -/
lemma FreeInts.inv_scalar_on_blocks {c} (he : FreeInts e) (hc : Surjective c) {x : GL N k} (hm : m ≤
  n + 1) (h : ∀ a, powMinor (diagonal (T ∘ e ∘ c) * x.1.map .C) m a = 0) : n < m ∧
  ∀ {a b}, c a = c b → a ≠ b → x⁻¹ a b = 0 ∧ x⁻¹ a a = x⁻¹ b b := by
  let y := diagonal (X ∘ c) * x.1.map .C
  have hy j : ∀ a b, ((y ^ j) a b).IsHomogeneous j := by induction j <;>
    simp_all [← totalDegree_zero_iff_isHomogeneous, y, pow_add, mul_apply, diagonal, mul_comm (X _),
      apply_ite]
  let z := (ofId _ (FractionRing (MvPolynomial (Fin n) k))).mapMatrix y
  have (o : m ≤ _) := minors_eq_zero_iff.1 (fun a ↦ (map_powMinor ..).symm.trans (by
    simpa [-map_powMinor] using congr($((map_powMinor y a (AddMonoidAlgebra.mapDomainAlgHom k k
      _)).trans (.trans (by simp [y, MvPolynomial.X, ← single_eq_monomial, T, ↓algHom_C]) (h
      a))).coeff.support).symm.trans (Finsupp.mapDomain_support_of_injOn _ (.mono
      ((homogeneousSubmodule_eq_finsupp_supported ..).le (by simpa [det_apply'] using (.sum _ _ _
      fun _ _ ↦ .C_mul (.prod _ _ _ (by tauto)) _))) (he _ (by grw [isLt, ← hm]; simp))))))
    (((linearIndependent_pow z).comp _ (castLEEmb o).2).of_comp (LinearEquiv.curry ..).1)
  obtain ⟨M, D⟩ := minpoly.monic z.isIntegral, z.minpoly_dvd_charpoly.trans (charpoly_map ..).dvd
  choose s hq _ U using lifts_and_natDegree_eq_and_monic (by
    simpa [M] using! IsIntegrallyClosed.eq_map_mul_C_of_dvd _ y.charpoly_monic D) M
  have ⟨w, hw⟩ := (map_dvd_map _ (IsFractionRing.injective ..) U).1 (hq ▸ D)
  obtain ⟨⟨α, v⟩⟩ := by simpa [det_eq_sign_charpoly_coeff, hw, ne_zero_iff] using
    (by simpa [y, prod_eq_zero_iff] using (x.map _).det_ne_zero : y.det ≠ 0)
  have : ((optionEquivLeft ..).symm y.charpoly).totalDegree ≤ card N := by
    simp [charpoly, det_apply, y, charmatrix, diagonal_apply, apply_ite]
    grw (transparency := .default) [totalDegree_finsetSum, totalDegree_smul_le,
      totalDegree_finsetProd, totalDegree_sub, totalDegree_mul]; simp [ite_apply, apply_ite]
  grw [← y.charpoly_natDegree_eq_dim, hw, map_mul, totalDegree_mul_of_isDomain (by aesop)
    (by aesop), natDegree_mul_le, ← totalDegree_coeff_optionEquivLeft_le, ← le_totalDegree
    (by simpa), ← degreeOf_le_totalDegree, ← natDegree_optionEquivLeft] at this
  have hr := s.X_mul_divX_add ▸ (ext (by
    simpa [z, ↓aeval_algHom_apply,
      ↓Polynomial.aeval_map_algebraMap] using congrFun₂ congr(aeval z $hq)) : s.aeval y = 0)
  have h2 a b := congr((($((s.divX.divX_mul_X_add ▸ hr :)) * x.1⁻¹.map .C :) a b).coeff α)
  simp [y, add_mul, mul_add, algebraMap, α.sum_fintype, ↓map_add] at *
  simp [← mul_assoc, coeff_mul_X', mul_comm (s.coeff _), ← @eq_of_le_of_not_lt _ _ 1 ⇑α (hc.forall.2
    fun a ↦ Nat.pos_of_ne_zero fun z ↦ by simpa [*] using congr(($hr a a).coeff α))
    (by bound [by simpa using sum_strictMono ·])] at *
  grind [diagonal_apply, MvPolynomial.coeff_zero]

/-- Division: let continuous r: G_E → GL_N(K) span all diagonal matrices and monic P_y of degree n
kill r at most Frobenii y. If polynomials vanishing at Q·r(g) near 1 vanish at diag(T^κ)Q over
k[T,T⁻¹], with n free integers among the κ_a, then N = n and P_y = charpoly at most Frobenii. -/
lemma rank_eq_and_charpoly_eq [NeZero n] {E} [Field E] [NumberField E] [Algebra E Ω]
  (r : Gal(Ω/E) →* GL N K) (c : Continuous r) (d : ∀ v, diagonal v ∈ span K (.range (r · |>.1)))
  {P : _ → K[X]} (h₁ : ∀ᶠ y in mostFrobenii E, (P y).aeval (r y.frob).1 = 0 ∧
  (P y).IsMonicOfDegree n) (Q : GL N k) κ (he : FreeInts e) (l : ∀ i, e i ∈ Set.range κ) (t : ∀ h :
  MvPolynomial _ k, (∀ᶠ g in nhds 1, h.aeval (Q.1 * (r g).1.map (algebraMap ..)).uncurry = 0) →
  h.aeval (diagonal (T ∘ κ) * Q.1.map LaurentPolynomial.C).uncurry = 0) : card N =
  n ∧ ∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = P y := by
  delta uncurry at t
  let φ := (MulSemiringAction.toAlgHom K (Matrix N ..) (toConjAct Q)).comp (ofId K k).mapMatrix
  have W {m g} {p : K[X]} (o : p ≠ 0) (e : p.aeval (r g).1 = 0) (h : p.natDegree < m) :
    powMinor (φ _) m = 0 := funext (minors_eq_zero_iff.2 ((·.restrict_scalars' K).mt (by
    exact not_linearIndependent_iff.2 ⟨_, funext (by simpa [aeval_eq_sum_range' h, sum_range]
      using! (congr(φ $e · ·))), ⟨_, h⟩, by simpa⟩)))
  have : e.Injective := fun i j h ↦ Finsupp.basisSingleOne.injective (by apply he 1 <;> simp [*])
  have Z {m} x h a := t (powMinor (mvPolynomialX N N k * (Q⁻¹ * Units.map φ (r x)).1.map C) m a)
    (.mono ((map_mul_right_nhds_one x).le ((isClosed_eq (f := fun g ↦ powMinor (φ (r g)) m) (by
    simp [φ]; fun_prop [flip]) continuous_zero).closure_eq.subst h))
    (by simp_all [φ, Matrix.map_mul]))
  simp [-diagonal_mul, -Units.coe_map, ← Matrix.map_mul] at Z
  have H x := Z x (univ_mem' (dense_of_mostFrobenii (h₁.mono fun g h ↦
    W h.2.ne_zero h.1 congr($(h.2.1) + 1).le)))
  choose l L using l
  choose c hc using fun j ↦ ((det_vandermonde_eq_zero_iff.1 (by simpa [det_classical, diagonal_pow,
    flip_def, uncurry] using! (H 1 (Function.diag ∘ cons j l)))).elim (by
    simp [T, forall_fin_succ, AddMonoidAlgebra.single_inj]; grind) : ∃ i, e i = κ j)
  obtain ⟨rfl, hs⟩ := funext hc, (⟨l ·, by grind⟩ : Surjective c)
  have hN := card_of_bijective ⟨fun a b h ↦ by_contra fun o ↦ by simpa using ((congrFun₂ Q.3 a
    a).symm.trans (sum_eq_zero fun t _ ↦ by apply ((span_induction (p := fun x _ ↦ φ x a b = 0 ∧
    φ x a a = φ x b b) (by simpa using (H ·⁻¹ |> he.inv_scalar_on_blocks hs .refl |>.2 h o)) _ _ _
    (d (Pi.single t 1))).elim
    (by simp [φ, mul_apply, diagonal, apply_ite]; grind)) <;> simp +contextual)), hs⟩
  use by simp [*], h₁.mp fun V a ⟨x, b⟩ ↦ ⟨_, sdiff_le, a.sdiff (by simp), Set.not_subset.1
    (mem_nhds_iff.2 ⟨V, ·, a, b⟩ |> Z x |> he.inv_scalar_on_blocks hs (by simp) |>.1.false),
    .of_forall fun _ _ _
    _ _ _ g h ↦ (sub_eq_zero.1 (by_contra (g.2 <| subset_closure <| W · (by simp [*,
    aeval_self_charpoly]) (h.2.natDegree_sub_lt NeZero.out ⟨by simp [*], charpoly_monic _⟩)))).symm⟩

end

variable {E K₀ ℓ} [Field E] [EmbeddedNumberField E] [Field K₀] [NumberField K₀] [ThePrime ℓ]

open Polynomial Units Fintype Matrix Metric Filter Submodule

/-- Base change ω ∘ N to E of an algebraic Hecke character ω of K₀; its exponent at an embedding
σ of E is that of ω at σ|K₀. -/
noncomputable def AlgHeckeChar.baseChange [Algebra K₀ E] (ω : AlgHeckeChar K₀) : AlgHeckeChar E :=
  ⟨(ω.1.1.comp (Units.map (adeleNorm ..)), .ofAdd (ω.1.2.toAdd <| ·.comp (algebraMap ..))),
  ω.2.1.preimage_of_continuous, fun x ↦ by
  simp [map_adeleNorm_principalIdele, ω.2.2]
  convert ← prod_fiberwise (RingHom.comp · (algebraMap ..)) _ with s
  let := s.toAlgebra
  erw [Algebra.norm_eq_prod_embeddings, ← Finset.prod_zpow]
  apply prod_equiv (.mk (⟨_, RingHom.congr_fun ·.2⟩) (⟨_, ·.comp_algebraMap⟩)); aesop⟩

@[fun_prop] lemma continuous_cycCharIn : Continuous (cycCharIn (Γ := Gal(Ω/E)) (PadicAlgCl ℓ) Ω
  ℓ) := (continuous_algebraMap ..).units_map.comp (continuous_cycChar ℓ)

/-- Twisting by an algebraic Hecke character ω of E of type n: for continuous ρ, some continuous
ρ' inherits `SphericalClause` at each w where ω is unramified and n = d at the embeddings
inducing w; jumps shift by −n, eigenvalues t_j c^(−j) become t_j, c = ω(ϖ_w). -/
lemma exists_twist_algHeckeChar [PadicIso ℓ] [CMType E] (ω : AlgHeckeChar E) (d : ℕ) {ρ :
  PadicRep _ ℓ} (hρ : Continuous ρ.rep) : ∃ ρ' : PadicRep _ ℓ, Continuous ρ'.rep ∧ ∀ w,
  (∀ σ, inducedPrime σ = w → ω.1.2.toAdd σ = d) → CharUnramifiedAt ω.1.1 w → let c :=
    (ω.1.1 (locIdele w (uniformizer w))).1; ∀ {R J q a t}, SphericalClause ρ.rep R J w
    (heckePoly q a fun j ↦ ιℓ (t j * c⁻¹ ^ j)) → SphericalClause ρ'.rep R (fun τ ↦
    (J τ).map (· + -ω.1.2.toAdd τ)) w ((heckePoly q a t).map ιℓ) := by
  let θ := ω / show IsHeckeOfType 1 _ by simp [IsHeckeOfType, isOpen_iff_nhds].toAlgebraic (m :=
    d) (by tauto)
  let ν := cycCharIn _ Ω ℓ ^ d * θ.avatar
  use ⟨twistByChar ν ρ.rep⟩, .of_coeHom_comp (.smul (by fun_prop) (by fun_prop))
  intro w hd hω c R J q a t h A hA
  have ⟨x, b, p⟩ := show heckeCoeff θ.1.1 ∅ w = w.q ^ d * c by simp [heckeCoeff, θ, ← two_mul,
    _root_.zpow_mul, ← Complex.ofReal_pow, field] ▸ (avatarCompatAt_of_type_eq_zero θ
    (by aesop)).sphericalClause_of_unramified (fun _ ↦ by aesop) hA
  refine (local_clauses_twist A (μ := ν) (by tauto)).2.elim fun T ⟨U, V⟩ ↦ (h hA).imp (T · ⟨by
    simpa +contextual [ν, cycChar_of_mem_inertiaGroup (A := A)] using x.1, x.2.tate_twist d ?_⟩)
    (.imp (U · fun l γ τ t u ↦ (jump_twist_cyclotomicGp (-d) ?_).subst
    (.trans (by simp [Multiset.count_singleton, θ, IsHeckeOfType.toAlgebraic, ← eq_sub_iff_add_eq])
    (b t _))) fun h s hs ↦ V (c := ιℓ c) ((h s hs).of_dvd ⟨C _,
    by simp +contextual [Polynomial.ext_iff, c, apply_ite, pow_sub₀, field]⟩) (.of_dvd ⟨fun l ↦ by
    obtain := congr(algebraMap _ (PadicAlgCl ℓ) $(hs.cycChar_eq ℓ l)).symm, (p s hs).1
    simp_all [Matrix.algebraMap_eq_diagonal, ν, Matrix.diagonal_pow, funext_iff],
    @fun l h k hk ↦ ((p s hs).2 hk).elim fun o q ↦ (And.intro · ?_) (o.tate_twist d ?_)⟩
    ((C_mul_dvd (a := ↑w.q ^ d) (by simp)).2 dvd_rfl)))
  rotate_right 2
  rw [C_mul', eval₂_smul, ← q, eq_comm, linearFrob_twist_cyclotomicGp ‹_› hk d]
  simp [hk.eq_pow_of_isFrob (by rwa [← map_inv, l.isFrob_iff]), ↓eval₂_sub, ↓eval₂_C, pow_mul,
    Algebra.smul_def, mul_sub]
  all_goals simp [ν, PadicPlaceEmbedding.cyclotomicGp_eq_cycChar, mul_smul, ← map_pow,
    ← Units.smul_def]

attribute [local simp] tendstoUniformly_iff trace_blockDiagonal' Finset.mul_sum

/-- Suppose that for each τ some continuous ρ_τ is, along the filter F of places w, unramified
or crystalline, with J(τ) occurring among its jumps at τ and P_w killing geometric
Frobenius. Then one continuous r, whose image spans all diagonal matrices, does this for all
τ. -/
lemma exists_rep_span_diagonal {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E]
  (F : Filter (FinPlace E)) J (P : FinPlace E → (PadicAlgCl ℓ)[X]) (h : ∀ τ, ∃ ρ : PadicRep Gal(Ω/E)
  ℓ, Continuous ρ.rep ∧ ∀ᶠ w in F, SphericalClause ρ.rep OccursIn (Set.indicator {τ} J) w (P w)) :
  ∃ b, ∃ r : GalRep ℓ E (Fin b), Continuous r ∧ (∀ v, diagonal v ∈ span (PadicAlgCl ℓ)
  (.range fun g ↦ (r g).1)) ∧ ∀ᶠ w in F, SphericalClause r OccursIn J w (P w) := by
  choose ρ hρ H using h
  choose σ n t using exists_rep_of_pseudo fun _ ↦
    (· (.toHomUnits (.comp blockDiagonalAlgHom.1.1 (.pi ((Units.coeHom _).comp <| ρ · |>.rep)))))
  choose b d _ s f j u a using exists_wedderburn _ (.id _) n.hasSemiprimeSpan
  let f' :=
    (reindexAlgEquiv _ (PadicAlgCl ℓ) (@finSigmaFinEquiv _ d)).toAlgHom.comp blockDiagonalAlgHom
  have ht i : (f' (piMatrixUnit i)).trace = 1 := by
    simp_all [f', -coe_reindexAlgEquiv, Fintype.sum_eq_single i]
  choose B C e hB using exists_piMat_retract f f'
    (by simp_all [trace_of_idempotent, isIdempotentElem_map_piMatrixUnit]; grind)
  simp [trace] at ht a
  have := n.continuous_of_trace (by simp [t]; fun_prop)
  refine ⟨∑ i, d i, .toHomUnits (.comp f' s), .of_coeHom_comp (.congr (by fun_prop) (congr(C * $(a ·
    ▸ hB _)).trans (by simp [← C.mul_assoc, e]))), fun v ↦ (f'.toLinearMap.map_span_le ..).2 (by
    aesop) ⟨fun i ↦ diagonal (v <| finSigmaFinEquiv ⟨i, ·⟩), u.ge ⟨⟩, by aesop⟩,
    .mono (.all H) fun _ H A hA ↦ ?_⟩
  choose U K z using local_clauses_of_trace_limit this n OccursIn (pure ()) 1 _ _ (by simpa)
    (by grind [SphericalClause]) (fun _ ↦ (H · hA |>.2.1)) (.inl inferInstance) (by simp [t])
    fun τ _ _ _ h _ a _ ↦ h () τ (by aesop) (by simp_all [Tendsto, ← Nat.cast_sum])
  refine (local_clauses_of_retract (φ := .id _) 1 1 (by simp) (by simp) .id univ_mem (by simp [← hB,
    a]) e).elim fun _ y ↦ ⟨by aesop (add simp isGoodAt_iff), fun l _ _ t ↦ (mt ?_ ∘ K t ·),
    fun s i ↦ y.2 s ⟨⟩ (z .refl (fun _ τ ↦ ⟨.refl, (H τ hA).2.2 s i⟩) (by simp [t]))⟩
  simpa [jump_eq_zero_iff] using fun h g hg ↦ g.ext fun w ↦ by
    simpa [-mulVec_single, intertwiner_mul_piMatrixUnit, mul_vecMulVec, vecMulVec_mul,
      vecMulVec_mulVec, ← map_mul, ht, ← Finset.sum_mul, ← Pi.single_mul, ← sum_mulVec, ← map_sum,
      sum_piMatrixUnit, hodgeTateMaps.pull] using congr(∑ i, ∑ c, ∑ x, $(h _ (hodgeTateMaps.pull
      (intertwiner f f' fun _ ↦ vecMulVec (f (piMatrixUnit i 0 c) *ᵥ w) (Pi.single x 1)).toLin'
      (by simp [← a, mul_intertwiner]) ⟨g, hg⟩).2) (f' (piMatrixUnit i c) *ᵥ Pi.single x 1))
end

section
/-! Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. The result is
stated on coordinates in C_p, without algebraic groups or Tannakian categories. It says that a
polynomial that vanishes at the cyclotomically twisted Galois translates of a point, near the
identity, vanishes along the one-parameter torus. Source: Serre, Groupes algébriques associés aux
modules de Hodge-Tate, Astérisque 65 (1979), §1; Sen, Ann. of Math. 97 (1973).

This file: Hodge–Tate cocharacter lies in the Zariski closure of the image near the identity. -/

attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
open Finset Matrix LaurentPolynomial

seal Finset.univ Finset.sum Finset.prod in
/-- If a polynomial F over C_p vanishes at (χ(g)^(−κ_i)·g x_i)_i for all g in G_p near 1, then F
vanishes at (T^(κ_i)·x_i)_i in the ring of Laurent polynomials C_p[T, T⁻¹].

Known result: The Hodge-Tate cocharacter lies in the algebraic monodromy group. -/
lemma aeval_cocharacter_eq_zero {p} [ThePrime p] {n} [Fintype n] (κ : n → ℤ) (x : n → ℂ_[p])
    (F : MvPolynomial n ℂ_[p]) (h : ∀ᶠ g in nhds 1, F.aeval (fun i ↦
  (cyclotomicGp g ^ (-κ i)).1 • g • x i) = 0) : F.aeval (fun i ↦ T (κ i) * C (x i)) = 0 := by
  simp_rw [F.aeval_def, F.eval₂_eq', ← F.support.sum_coe_sort, ← Algebra.smul_def] at *
  let ⟨V, h⟩ := NonarchimedeanGroup.is_nonarchimedean _ h
  refine le_of_hodgeTate_stable le_rfl (∑ i, ·.1 i * κ i) (of _).vecMulLinear.ker
    (Fintype.linearCombination ..).ker (fun a u ↦ .mono V.mem_nhds_one fun k o ↦ funext fun g ↦ ?_)
    (fun v i a _ e _ _ ↦ .trans (sum_congr rfl fun l _ ↦ by cases e l <;> simp [*, T, C]; rfl)
    (sum_smul.symm.trans (congr($a 1 • T _).trans (by simp)))) (funext fun g : V ↦ h g.2)
  simpa [mul_pow, smul_smul, smul_prod', dotProduct, _root_.zpow_mul', vecMul, smul_sum,
    by simpa [-map_prod] using fun f ↦ map_prod (zpowersHom _ (cyclotomicGp k)) (.ofAdd ∘ f : n →
    _), mul_zpow, smul_pow, prod_smul, smul_comm k] using congr(k • $u (⟨k, o⟩⁻¹ * g))
end

section
/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: Fundamental tame characters of inertia; existence of exponents; link with local
reciprocity. -/


open NumberField Polynomial Ideal Quotient IsAlgClosed Fint IsLocalRing RingHom algebraMap
variable {E : Type} [Field E] [EmbeddedNumberField E] (w : FinPlace E) (A : ClosurePlace) {K : Type}
  [Field K] [Algebra (ResField w) K] (T) [IsFaithfulMulChar K T] (f) (s : Gal(Ω/E)) (a)

lemma exists_resField_hom {R} [Field R] (g : _ →+* R) (h : w.1 ≤ ker g) : ∃ j : ResField w →+* R,
    ∀ x, j (algebraMap _ _ x) = g x :=
  ⟨_, liftOfSurjective_comp_apply _ (algebraMap_ResField_surjective w) ⟨g, by simpa [LE.le]⟩⟩

/-- With Q = q_w^f > 1: s lies in inertia at A and T(residue in K of sz/z) = exp(2πi/(Q−1))^a,
for some z with z^{Q−1} in E a uniformiser. -/
def IsTameExponent := IsPlaceOver A w ∧ f ≠ 0 ∧ s ∈ inertiaGroup _ A ∧ ∃ (φ : 𝓞 Ω →+* K) (π : E)
  (z : Ω) (t : 𝓞 Ω), centrePrime Ω A ≤ ker φ ∧ (∀ x : 𝓞 E, φ x = (x : ResField w)) ∧ IsUniformiser A
  π ∧ z ^ (w.q ^ f - 1) = π ∧ t = s z / z ∧ T (φ t) = .exp (2 * Real.pi * .I / (w.q ^ f - 1 :)) ^ a

variable {w A f s a}
open Nat

/-- Whenever `IsTameExponent` relates s to the exponent a, P holds for s and ∏_x (X −
ι(T(x)^a)), over the roots x of c in K with multiplicity. -/
def IsLabelledAt {ℓ} [ThePrime ℓ] [PadicIso ℓ] A T f (P : _ → _ → Prop) (c : (ResField w)[X]) :=
  ∀ ⦃s a⦄, IsTameExponent w A T f s a → P s ((c.aroots K).map fun x ↦ X - C (ιℓ ((T ^ a) x))).prod

/-- Let `IsTameExponent` relate s to the exponent a at A above w, T injective, and let u be a
local unit with local Artin image s. Then (T^a)(x_χ) = χ(residue of u) for every character χ
of k_w^×, x_χ = `charName` T χ. -/
lemma IsTameExponent.pow_apply_charName {d} (h : IsTameExponent w A T f s a) {u} (hu :
  Valued.v u.1 = 1) (b : localArtin _ A w u =
  ⟦⟨s, d⟩⟧) χ : (T ^ a) ((charName T χ).1 : ResField w) = χ (residue _ ⟨u, hu.le⟩) := by
  obtain ⟨⟨c, q, _, ρ, π, z, t, o, _, p, r, _, e⟩, ⟨k, l⟩, x, g⟩ := h,
    w.q.sub_one_dvd_pow_sub_one f, algebraMap_ResField_surjective w (residue _ ⟨u, hu.le⟩)
  rw [l, pow_mul'] at r
  grind [thetaChar_charName, card_ResField, =_ (thetaChar_apply_pow T w.one_lt_q · (by simp [q,
    ne_of_gt]) l e), algebraMap_pow_card_pred_eq_one, mem_ker, @o (t ^ k - x) (by
    simpa [*, div_pow, mem_centrePrime] using!
      (c.localArtin_tame_symbol p hu b r).1 (residue_eq_iff_valuation_sub_lt_one.1 g.symm))]

/-- Let c be a label of degree r over the residue field k_w and x a root of c in K. Then
x^{q_w^{r!} − 1} = 1, and x^{q_w^d − 1} = 1 for some d with 1 ≤ d ≤ r. -/
lemma IsLabel.root_pow_eq_one {c : (ResField w)[X]} {r} (h : IsLabel r c) {x : K} (hx : aeval x c =
    0) : x ^ (w.q ^ (r)! - 1) = 1 ∧ ∃ d ∈ Set.Icc 1 r, x ^ (w.q ^ d - 1) = 1 :=
  have i := minpoly.irreducible ⟨c, h.1, hx⟩
  by grind [card_ResField, aroots_pow_eq_frobenius_orbit i (j := 1) (K := K), aeval_def,
    eval₂_at_zero, map_eq_zero,
    IsLabel, pow_pred_eq_one_iff, root_pow_card_pow_eq_self_iff, minpoly.aeval, dvd_factorial,
    i.natDegree_pos, natDegree_le_natDegree, minpoly.min, one_lt_pow₀ w.one_lt_q]

/-- For A above w, T injective and Q = q_w^{f!}: every s in the inertia group of A has a tame
exponent a (`IsTameExponent`), which can be taken coprime to Q − 1 for the chosen tame
generator, and some s has exponent 1. -/
lemma exists_isTameExponent (hA : IsPlaceOver A w) f :
  (∃ s : inertiaGroup _ A, IsTameExponent w A T (f)! s.1 1) ∧ ∀ s ∈ inertiaGroup _ A, ∃ a,
  IsTameExponent w A T (f)! s a ∧ (s = hA.tameGenerator → a.Coprime (w.q ^ (f)! - 1)) := by
  obtain ⟨_, H : NeZero ((w.q ^ (f)! - 1 :) : ResField w)⟩ := hA.centrePrime_liesOver,
    ⟨by simp [← card_ResField, Fin.pos']⟩
  let := Quotient.field w.1
  let := Algebra.compHom K (lift w.1 (algebraMap _ (ResField w)) (by simp))
  let ρ := (lift : _ →ₐ[_ ⧸ w.1] K).1.comp (mk (centrePrime Ω A))
  obtain ⟨_, n, hv⟩ := H.of_faithfulSMul _ K, H.of_neZero_natCast,
    hA.valuation_natCast_eq_one_iff.2 (mt algebraMap_ResField_eq_zero.2 (mod_cast H.1))
  choose π z u hz g using hA.exists_tameGenerator.choose_spec _ hv
  choose j _ G k using ((isRoot_cyclotomic_iff.1 (map_cyclotomic _ ρ ▸ (isRoot_cyclotomic_iff.2
    g.toInteger_isPrimitiveRoot).map)).map_of_injective
    IsFaithfulMulChar.injective).isPrimitiveRoot_iff.1 (Complex.isPrimitiveRoot_exp _ n.1)
  apply g.pow_of_coprime at G
  have r s h {a} e : IsTameExponent w A T _ s a := ⟨hA, by simp, h, ρ, π, z, (g.toInteger ^ j) ^
     a, by grw [← comap_ker, ← ker_le_comap, mk_ker], (lift.2 <| mk _ ·), u, hz, e, by aesop⟩
  use ⟨_, r _ (hA.tameGenerator ^ j).2 (inertia_pow_smul_div hA.tameGenerator.2 hv hz _ ▸ pow_one
    _)⟩, ((G.eq_pow_of_pow_eq_one (by simp_all [div_pow, ← map_pow])).imp fun a ⟨_, e⟩ ↦ ⟨r · · e,
    (by rwa [← G.pow_iff_coprime n.pos, e, ·])⟩)
end

section
/-! Known result: Grunwald–Wang theorem in prime exponent. It is proved here for prime exponent over
a totally complex field, and the character also agrees with the given one on units at all primes of
degree above one. A CM extension of prime degree with prescribed tame completion at a split place
follows. Source: Artin–Tate, Class Field Theory (1968), ch. X; S. Wang, Grunwald–Wang theorem, an
effective version, arXiv 1401.0389 (2014).

Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Field cut out by χχ^c is CM of prime degree, with norm-detecting character. CM extension
of prime degree with prescribed tame completion at a split place. Auxiliary quadratic CM extension
containing imaginary quadratic field, split at given places. Local properties descend from the
base-changed form's representation to the original one. Determinant of an attached Galois
representation is the avatar of the twisted central character. -/

section

open NumberField Ideal Algebra ComplexEmbedding Subgroup QZChar QZ FractionalIdeal RingOfIntegers
section
variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))

/-- The extension of the CM field E inside Ω cut out by the character g ↦ χ(g) + χ(g^c), that
is, the fixed field of its kernel. -/
noncomputable abbrev QZChar.stepField := fixedFieldOf (ker (symmetrise χ))

instance : IsCMField (stepField χ) := isCMField_of_forall_exists_conj E fun y ↦ ⟨⟨_, (cmConj_cmConj
  _ ▸ congr(cmConj $(y.2 ⟨_, add_eq_zero_symm <| congr(χ.1 $(conjGal_conjGal _) + _).trans ·.2⟩)))⟩,
  (lift_comp_algebraMap Ω · ▸ let J := lift Ω _; (exists_smul_emb_eq _ (J.comp cmConj) (star J) (by
    ext; simpa using map_star_complex (J.comp _) _)).rec fun g h ↦ (y.2 ⟨g, map_mul_eq_one (toHom χ)
    (mul_eq_one_symm (by ext; simp_all [← J.injective.eq_iff, conjGal]))⟩ ▸ h y :))⟩

end

open InfinitePlace in noncomputable instance {E} [Field E] [EmbeddedNumberField E] [CMType E]
    (χ : QZChar Gal(Ω/E)) : CMOver E (stepField χ) where
  Φ u := let e := u.embedding
    ite (e.comp (algebraMap ..) = Φ (u.comap (algebraMap E _))) e (star e)
  mk_Φ := by aesop
  mem_type_iff := by grind [embedding_mk_eq, Φ_eq_or, comap_mk, conjugate_comp, star_star]

variable {E} [Field E] [EmbeddedNumberField E] [IsCMField E] (χ : QZChar Gal(Ω/E))

instance [h : StablyUnram E] : StablyUnram (stepField χ) :=
  ⟨_, h.1.choose_spec.map_of_injective (algebraMap ..).injective⟩

/-- Let E' be the field cut out by g ↦ χ(g) + χ(g^c) and u a prime of E'. If this character
kills the inertia groups above the prime of E below u, then u does not divide the different
of E' over E. -/
lemma QZChar.not_dvd_differentIdeal_stepField {u : FinPlace (stepField χ)} (h :
  ∀ {A : ClosurePlace}, IsPlaceOver A (u.below E) → inertiaGroup _ A ≤ ker (symmetrise χ)) :
  ¬u.1 ∣ differentIdeal (𝓞 E) _ := not_dvd_differentIdeal_iff.2 <|
  ramificationIdx_eq_one_iff.1 ((u.isPlaceOver_placeOver.isPlaceOver_below.ramification_in_tower _
  u.isPlaceOver_placeOver).2.1 (h u.isPlaceOver_placeOver.isPlaceOver_below))

/-- Let E be stably unramified CM, p prime, pχ = 0, and ξ(g) = χ(g) + χ(g^c) non-zero and
unramified above p. Then the field of ξ has degree p over E and forms a step (`IsStep`)
with the character exp(2πi χ∘Art). -/
lemma isStep_stepField [StablyUnram E] {p} (hp : Nat.Prime p) (h : p • χ = 0) {g₀} (h₀ :
  (symmetrise χ).1 g₀ ≠ 0) (ht : ∀ {A : ClosurePlace} {u : FinPlace E}, IsPlaceOver A u → ↑p ∈ u.1 →
  inertiaGroup _ A ≤ ker (symmetrise χ)) :
  IsStep (stepField χ) (ideleChar χ) ∧ Module.finrank E (stepField χ) = p := have := Fact.mk hp
  (iff_and_self.2 fun | rfl => ⟨isOpen_mono (expUnit.ker.ker_le_comap _)
    (continuous_iff_isOpen_ker.1 continuous_artinMap χ), by simp [artinMap_principalIdele,
    isTotallyPositive_of_isTotallyComplex], by simp [isTotallyPositive_of_isTotallyComplex,
    ← abelianLift_symmetrise, char_artinMap_eq_one_iff (symmetrise χ), expUnit_eq_one_iff],
    ((eq_top_iff_one _).1 ((IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists
    (not_isField E) (intTrace ..).range).not_right.2 fun ⟨u, hI⟩ ↦ by
    obtain ⟨n, P, ⟨⟩⟩ := coeIdeal_ne_zero (K := E).2 u.3,
      FinPlace.comap_surjective (algebraMap E (stepField χ)) u
    refine not_dvd_differentIdeal_stepField χ (ht · (hI ⟨1, ext ?_⟩)) <| dvd_iff_le.2 <|
      (differentialIdeal_le_iff (L := stepField χ)
      ?_).2 fun _ ⟨x, hx⟩ ↦ coe_one.le <| (div_self n).le <| (mem_div_iff_of_ne_zero n).2 fun
      | _, ⟨a, ha, rfl⟩ => ((mem_inv_iff ?_).1 hx.1 _ ⟨_, ha, rfl⟩).rec fun z _ ↦ ⟨_, hI ⟨z, rfl⟩,
      ?_⟩ <;> simp_all [algebraMap_intTrace (L := stepField χ), algebraMap_eq_smul_one, trace_apply,
      map_one, P.3])).imp (by simp [← algebraMap_intTrace (A := 𝓞 E)])⟩).1 (by
    rw [finrank_fixedFieldOf, eq_comm, ← hp.dvd_iff_eq (h₀ <| index_eq_one.1 · |>.ge ⟨⟩), index_ker]
    exact .trans (card_dvd_of_le fun | _, ⟨_, rfl⟩ => χ.2.2 .. ▸ exists_ofZMod congr($h.1 _))
      (p.card_zmod ▸ card_range_dvd (ofZMod p).toMultiplicative))

/-- Grunwald: for E with Weil data, w split and χ ≠ 1 a tame character of E_w^× killed by the
prime p, some ν trivial at w gives a degree-p step E' with Weil data and one place above w,
split, where ννᶜ corresponds to χ at w.

Known result: Grunwald–Wang theorem in prime exponent. -/
lemma exists_step_of_local_char {E} [Field E] [EmbeddedNumberField E] [CMType E] {w :
  FinPlace E} {A : ClosurePlace} [WeilData E] {p} (hw : w.IsSplit) (hA : IsPlaceOver A w) (hp :
  p.Prime) (χ : _ →* _) {x₀} (h₁ : χ x₀ ≠ 1) (hχ : ∀ x, χ x ^ p = 1) (ht : ∀ x, Valued.v x.1 = 1 →
  χ (x ^ (w.q - 1)) = 1) : ∃ ν : QZChar Gal(Ω/E), let E' := QZChar.stepField ν; ∃ (u : FinPlace E')
    (_ : WeilData E'), IsStep E' (QZChar.ideleChar ν) ∧ Module.finrank E E' = p ∧ u.IsSplit ∧ (∀ u',
    u'.below E = w ↔ u' = u) ∧ IsPlaceOver A u ∧ (∀ x, QZChar.abelianLift ν (artinAt _ w x) = 1) ∧
    ∀ x, QZChar.abelianLift (QZChar.symmetrise ν) (artinAt _ w x) = χ x := by
  obtain ⟨_, ν, hν, h⟩ := Fact.mk hp, grunwald hp (((@finite_natCast_mem _ _ _ _ ⟨hp.ne_zero⟩
    ).insert w).insert (star w)) (.mk' (χ ∘ ideleAt w ∘ star) (by simp)) (isOpen_of_forall_pow_mem
    hp.ne_zero (T := χ.ker) (by simpa)).preimage_of_continuous (by tauto)
  replace ht h x e := (pow_eq_one_iff_of_coprime (.of_dvd_left
    ((w.natCast_mem_iff_dvd h).1 w.1.absNorm_mem) (by simp))).1 ⟨hχ _, map_pow χ .. ▸ ht x e⟩
  have h₆ := by simpa [star_locIdele, hw.symm] using h w
  have h₅ x := by simpa [*, star_locIdele (v := w) x ▸ h ..] using
    QZChar.abelianLift_symmetrise ν (locIdele w x)
  replace h {A u} (hA : IsPlaceOver A u) (a : star u = u ∨ ↑p ∈ u.1) :=
    (hA.artinAt_units_trivial_iff_unramified (QZChar.symmetrise ν)).1 fun x b ↦ by_cases (by aesop)
    fun _ : w ≠ u ↦ by by_cases w = star u <;> subst_eqs <;> cases a <;> simp_all [star_locIdele,
    mt isSplit_of_q_prime, ← artinMap_locIdele, QZChar.abelianLift_symmetrise]
  obtain ⟨⟨_, hg₀, e₀⟩, u, _, ⟨⟩⟩ := (hA.range_abelianLift_artinAt _).le ⟨_, h₅ x₀⟩,
    hA.exists_above (L := QZChar.stepField ν)
  obtain ⟨_, ⟨⟩⟩ := isStep_stepField ν hp hν (e₀ ▸ h₁) (h · ∘ .inr)
  simp [← hA.ncard_above_mul_relIndex (QZChar.ker (QZChar.symmetrise ν)), Nat.prime_mul_iff,
    Set.ext_iff, LE.le] at hp hg₀
  use ν, u, (nonempty_weilData_of_unramified fun v e ↦
    QZChar.not_dvd_differentIdeal_stepField _ (h · ?_)).some <;> grind [below_star]

open IsDedekindDomain HeightOneSpectrum Nat ZMod decompGroup QuadField algebraMap

attribute [local simp] QZChar.comap mul_mem_right mul_mem_left two_smul neg_eq_self NeZero.ne

/-- For E stably unramified, n ≠ 0, some χ gives a step E' ⊃ ℚ(√−D), split above n. With N =
G_{E'} ∩ ker χ: G_E = NH if H contains inertia at all x ∤ n of small norm; at w ∣ n, G_w
fixes E', and χ kills I_w, and G_w if w is split. -/
lemma exists_quadratic_step E [Field E] [EmbeddedNumberField E] [IsCMField E] [StablyUnram E]
  (n : ℕ) (hn : n ≠ 0) : ∃ χ : QZChar Gal(Ω/E), let E' := stepField χ; let U := ker (symmetrise χ)
    let N := U ⊓ ker χ; ∃ᵉ (D) (_ : HasQuadSubfield D E'), IsStep E' (ideleChar χ) ∧ (∃ m, ∀ H :
      Subgroup Gal(Ω/E), inertiaAbove {x : FinPlace E | ↑n ∉ x.1 ∧ x.q ≤ m} ⊆ H → ∀ g, ∃ h ∈ H,
      g * h ∈ N) ∧ (∀ u : FinPlace E', ↑n ∈ u.1 → IsSplitPrimeToDisc (u.below (QuadField D))) ∧
      ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w → ↑n ∈ w.1 →
    decompGroup _ A ≤ U ∧ inertiaGroup _ A ≤ N ∧ (w.IsSplit → decompGroup _ A ≤ N) := by
  let k := Ideal.absNorm (span {(4 : 𝓞 E)})
  let R := 4 * n * (2 * n) ^ k
  have ⟨j, b, O⟩ := @exists_eq_two_pow_mul_odd R (by aesop)
  let C := 1 + b * (2 + 8 * b)
  have ⟨q, g, p, f⟩ := @forall_exists_prime_gt_and_eq_mod R ⟨by aesop⟩ _ (-unitOfCoprime C (by
    cases j <;> simp [*, C, coprime_mul_iff_right, parity_simps]))⁻¹.isUnit
    (C * n * Ideal.absNorm (differentIdeal ℤ (𝓞 E)))
  let D := C * q
  obtain ⟨⟨M, hD⟩, Z, _⟩ := (natCast_eq_zero_iff (D + 1) R).1 (by simp [D, f,
    neg_add_eq_zero]), (eq_zero_of_dvd_of_lt · g), Fact.mk p
  obtain ⟨d, ⟨P, r⟩, ⟨i, ω, _⟩, ⟨⟩, s, t, l⟩ := Fact.mk (by lia : D % 4 = 3),
    FinPlace.exists_natCast_mem E q, ‹StablyUnram E›.exists_i_c₀, exists_wellFoundedLT (FinPlace E),
    @Prime.sq_add_sq q _ (by grind [C.mul_mod q 4])
  simp [p.dvd_mul, ← P.natCast_mem_iff_dvd r, *] at Z
  have ⟨α, _⟩ : ∃ α : 𝓞 E, α * star α = D :=
    ⟨(1 + 2 * b * ω) * (s + t * i), by simp [D, ← l]; grind⟩
  obtain ⟨B, s, hs⟩ := P.isPlaceOver_placeOver,
    @exists_forall_sub_mem_ideal _ _ _ (@finite_natCast_mem _ _ _ _ ⟨hn⟩)
    (·.1.1 ^ k) (fun _ _ ↦ by grind [isCoprime_pow_of_ne]) fun w ↦ ite (star w.1 < w) α 1
  have N {w : FinPlace E} (h : 2 * n.cast ∈ w.1) :
    ↑(D + 1) ∈ w.1 ^ k := by simp [hD, R, pow_mem_pow h]
  let t := ite (s = 0) 1 (s * star s)
  have T {w} (h : ↑n ∈ asIdeal w) : 1 - α * t * ite (w < star w) i (star α) ^ 2 ∈ w.1 ^ k ∨ star w =
    w ∧ α * t ∉ w.1 ∧ 2 ∉ w.1 := by grind [hs ⟨w, h⟩, =_ Quotient.eq_zero_iff_mem, star_star,
    one_notMem w.1, IsConcreteLE.le_iff, Ideal.mem_comap, le_comap_pow _ k (hs ⟨star w, by simpa⟩),
    pow_le_self, show k ≠ 0 by simp [k], starRingEnd_apply, mem_star_place, → w.2.2]
  obtain ⟨⟨b, hb⟩, ⟨G, -, U⟩, _⟩ := IsAIC.exists_pow_eq 2 (↑(↑(α * t) : E) : Ω), B.decompGroup_spec
    Gal(Ω/E), by simpa [addOrderOf_eq_prime_iff] using QZ.addOrderOf_mk_inv two_pos
  have S (g : Gal(Ω/E)) {c : Ω} {x : E} (h : c ^ 2 = x) :=
    eq_or_eq_neg_of_sq_eq_sq (g c) c (by simp [← map_pow, h])
  have L {A w g c} (a : IsPlaceOver A w) hg {x u : 𝓞 E} h (H : 1 - x * u ^ 2 ∈ w.1 ^ k) :=
      (@S g c x h).resolve_right fun e ↦ have o (z : Ω) := A.valuation.map_add_le le_rfl (val_smul
      (σ := g) hg (1 + z * (u : E))).le; mt (Int.natAbs_le_of_dvd_ne_zero ∘
      absNorm_dvd_norm_of_mem) (by simp [k, Nat.lt_pow_self]) (show 4 ∈ w.1 ^ k by
    rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := E)] at *
    grw [← H, ← a.isEquiv.le_iff_le]
    convert mul_le_mul' (o c) (o (-c)) <;> simp [← map_mul, map_ofNat] <;> grind)
  let y := (i / t : E) * b * cmConj b
  have hy : y ^ 2 = ((-D : 𝓞 E) : E) := by
    simp [y, mul_pow, ↓← map_pow, hb, -map_neg, t]; field_simp [ite_eq_iff]
    exact_mod_cast by grind [star_mul, star_star]
  have := by simpa [y] using congr($hy = 0)
  let χ : QZChar _ := ⟨_, ((isLocallyConstant_smul b).comp (if · = b then 0 else .mk
    2⁻¹)).continuous, fun g h ↦ by cases S g hb <;> cases S h hb <;> simp [*]⟩
  have H {g} : (symmetrise χ).1 g = 0 ↔ g y = y := by cases S g hb <;> cases S g (by
           rw [← map_pow cmConj, hb, cmConj_algebraMap]) <;> simp [*, y, χ, conjGal]
  have Y {A w} a h g m := H.2 (@L A w g _ a m _ 1 hy (by simpa [add_comm] using N h))
  have ⟨σ, I, J⟩ := G.exists_inertia_smul_eq_of_pow_eq (@U (.mk0 _ (by simp)) (B.isUniformiser_iff.2
    (by erw [valuation_of_algebraMap]; simp [D, *, p.ne_zero, -NeZero.ne,
    intValuation_eq_exp_neg_multiplicity, mt dvd_differentIdeal_of_mem_sq (Z.2 <| le_of_dvd
    · (absNorm_mem _)), multiplicity_eq_of_dvd_of_not_dvd (k := 1)]))) two_pos hy (neg_sq y)
  have J := mt H.1 (J.trans_ne (by simpa [y]))
  let := (@embOfSqrt D (stepField χ) _ _ ⟨y, (H.1 ·.2)⟩ _ (by ext; simp [*])).toAlgebra
  use χ, D, {}, (isStep_stepField χ prime_two (by ext; simp [χ, ite_add_ite, *]) J fun a h ↦ (Y a
    (by simp_all) · ·.1)).1, ⟨P.q, fun U e g ↦ .imp' _ (fun i : Fin 2 × Fin 2 ↦ (⟨mul_mem (pow_mem
    (e ⟨P, ?_, _, B, I⟩) i.1) (pow_mem (e ⟨_, ?_, _, B.conjPlace_star, I.conjPlace_conjGal⟩) i.2),
    ·⟩)) (Not.imp_symm (by simp [↓map_mul, toHom, χ, ← ofAdd_add]; split_ifs <;> simp [*]) J)⟩,
    fun u h ↦ ((u.below _).2.2 ((c₀_mul_one_sub D).substr ?_)).elim
    (fun _ ↦ ⟨0, ?_, 1, 1, by simp⟩)
    (⟨1, by simpa using neg_mem ·, -1, -1, ?_⟩), fun a l ↦
      (fun y ↦ ⟨y, fun g i ↦ ⟨y _ i.1, ite_eq_left
    ((T l).elim (L a i.1 hb) fun _ ↦ inertia_fixes_root_of_unit i (a.valuation_natCast_eq_one_iff.2
    ?_) hb (a.valuationVia_eq_one_iff.2 ?_) ?_)⟩, fun e _ g ↦ ⟨y _ g, ite_eq_left (L a g hb ((T
    l).resolve_right ?_))⟩⟩) (Y a ?_) <;> simp [↓valuation_eq_one_iff_notMem, *, -O, R, mul_assoc]

end

/-- Let f' be a weak base change of the eigenform f to E', cut out by χχᶜ, with attached r'.
Some continuous semisimple ρ on N = G_{E'} ∩ ker χ approximates the Hecke polynomials of f;
any r attached to f inherits finite type, jumps, and on N determinants and killing
polynomials. -/
lemma IsWeakBaseChange.exists_attached_descent {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n M M'} [Field E]
  [CMType E] [EmbeddedNumberField E] [Fintype n] {χ : QZChar Gal(Ω/E)} {f : _ → M → ℂ} {f' :
  Gf (QZChar.stepField χ) n → M' → ℂ} {S P P'} {r' : GalRep ℓ _ n} (hs : IsWeakBaseChange
  (QZChar.ideleChar χ) S f f') (hr' : Attached P' r') (he' : IsEigenform f' P') (he : IsEigenform f
  P) : let L := QZChar.stepField χ; let N := QZChar.ker (QZChar.symmetrise χ) ⊓ QZChar.ker χ
    let i : N →* _ := L.fixingSubgroupEquiv.toMonoidHom.comp (Subgroup.inclusion (id fun s h ↦
      (·.2 ⟨s, h.1⟩))); N.IsOpen ∧ (∀ {r : GalRep ℓ E n}, Attached P r → ∀ A, (IsFiniteTypeAt r' A →
    IsFiniteTypeAt r A) ∧ (∀ {κ} m, HasJumpsAt r' A (jumps κ.baseChange m) → HasJumpsAt r A
      (jumps κ m)) ∧ ∀ s, (r s.1).1.det = (r' (i s)).1.det ∧ ∀ Q, PolyKillsAt r' A (i s) Q →
      PolyKillsAt r A s Q) ∧ ∃ ρ : N →* _, Attached P ρ (·.1) ∧ ∀ s, ρ s = r' (i s) := by
  intro L N i
  obtain ⟨hφ, o⟩ := isOpenEmbedding_galois_restrict (Γ' := Gal(Ω/L))
    (AlgEquiv.restrictScalarsHom E) (by simp), (QZChar.isOpen_ker _).inter (QZChar.isOpen_ker χ)
  refine (fun c ↦ ⟨o, fun h A ↦ ?_, r'.comp i, c, by simp⟩) ⟨hr'.1.comp (hφ.continuous_iff.2
    continuous_subtype_val), (hr'.2.1.comp L.fixingSubgroupEquiv.toMonoidHom).comp _,
    o.isOpenMap_subtype_val, (hr'.2.2.2 · · |>.and (eventually_mostFrobenii he'.2 fun y ↦
    (· y.prime_q)) |> mostFrobenii_push hφ _ |>.mp (eventually_mostFrobenii
    (he.2.and ((finite_ramified o).and hs.1.cj.compl_mem_cofinite)) fun x ⟨y,
    I, z⟩ B s e ↦ x.isPlaceOver.exists_above.rec fun u ⟨a,
    i⟩ ↦ have D : _ ≤ N := x.isPlaceOver.decompGroup_le x.isFrob o (I _ x.isPlaceOver) (by bound)
    have G := x.isPlaceOver.split_completely fun _ h ↦ (D h).1
    (B ⟨_, _, _, (G u i).1 ▸ x.prime_q, a, (G u i).1 ▸ (e ▸ x.isFrob :)⟩ i (by tauto)).rec fun b d ↦
      (show _ → _ → P' u = P x.w by simp_all [HasHeckePolyAt, heckePoly, he'.1, smul_left_inj]) d.2
      ((hs.2 _ z u i).2 ⟨by simp [(x.isPlaceOver.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦
      (D h).2], G⟩ _ _ (y x.prime_q).2).2 ▸ b _ rfl))⟩
  choose Z h using c.2.1.exists_conj_of_trace_eq _ (.id ..) (h.2.1.comp N.subtype).hasSemiprimeSpan
    (c.trace_eq h · rfl)
  refine (local_clauses_of_retract 1 (algebraMap ..) (by simp) (by simp) hφ ((hφ.continuous.1 _
    o).mem_nhds N.one_mem) (fun _ ↦ (h ⟨_, ·⟩)) Z.4).imp_right (.imp (fun b _ _ ↦
    b Z.3 ∘ cast ?_) fun c s ↦ ⟨by simpa [field] using! congr($(h s).det).symm, @c _ s.2⟩)
  simp [jumps.eq_unfold]; congr!; apply CMOver.mem_type_iff

open Finset Matrix Fintype Filter Representation

attribute [local simp] smul_smul map_smul' _root_.zpow_mul scalarFin coe_divStar

/-- For r attached to a rank n eigenform f, det r is the avatar of an algebraic Hecke character
θ of explicit type; at split w, θ_w gives eigenvalues of unit scalars on f, and (−1)^n Q(0)
at uniformisers, Q a Hecke polynomial of f. -/
lemma Attached.exists_det_eq_avatar {E n} [Field E] [Fintype n] [CMType E] {κ ℓ}
    [ThePrime ℓ] [PadicIso ℓ] [Algebra E Ω] {f P} {r : GalRep ℓ E n} (hr : Attached P r) (hf : f ∈
  (stdSpace E n).forms κ) (he : IsEigenform f P) : ∃ θ : AlgHeckeChar E, (∀ σ, θ.1.2.toAdd σ =
  (if σ = Φ (.mk σ) then 1 else -1) * (card n * κ.2 (.mk σ) + ∑ i ∈ .range (card n),
  i * κ.1 (.mk σ) i) - (card n).choose 2) ∧ (∀ w (hw : star w ≠ w) x, (Valued.v x.1 = 1 → ∀ {c : ℂ},
  rightRegular ℂ _ _ (atSplit hw (.scalar n x)) f = c • f → θ.1.1 (locIdele w x) = c) ∧
  (Valued.v x.1 = .exp (-1) → ∀ {Q}, HasHeckePolyAt f w hw Q → θ.1.1 (locIdele w x) =
  (-1) ^ card n * Q.coeff 0)) ∧ ∀ g, (r g).1.det = AlgHeckeChar.avatar θ g := by
  let z := (scalarFin (E := E) n).comp divStar.1
  choose χ _ e using
    exists_monoidHom_extend (.domRestrict (.fst _ ℂˣ) (Subgroup.mk ⟨⟨{p | rightRegular ℂ _ _ (z p.1)
    f = p.2 • f}, by simp_all [mul_comm]⟩, by simp⟩ (by simp_all))) (.domRestrict
    (.snd ..) _) ⊥ fun a e ↦ Units.ext ((smul_left_inj he.1).1 (a.2.symm.trans (by simp_all)))
  have h x c (h : rightRegular ℂ _ _ (z x) f = c • f) : (χ x).1 =
    c := congr($(e ⟨(x, .mk0 c fun _ ↦ by
      simp_all [IsEigenform, ← inv_apply_eq_iff, eq_comm]), h⟩).1)
  refine ⟨IsHeckeOfType.toAlgebraic (k := -2 * (card n).choose 2) (by simp; lia)
    ⟨((rightStab f).comap z).isOpen_mono (e ⟨⟨·, 1⟩, by simpa using! funext ·⟩) (hf.1.preimage
    ((U.isClosedEmbedding_mat (by simp)).continuous_iff.2 (.matrix_diagonal (by simp; fun_prop)))),
    fun x ↦ ?_⟩, congrFun (toAdd_ofAdd _), (and_iff_left_of_imp fun H g ↦ ?_).2 fun w hw x ↦ ?_⟩
  · simp [← prod_mul_distrib, -neg_add_rev, ← two_mul, ← mul_zpow, div_pow, sq (Φ _ _),
      ← Complex.conj_mul', mul_div_mul_right, h (principalIdele x) _ (by simp [funext_iff, fun g ↦
              (Subtype.ext (by ext; simp [z, mul_comm, division_def]) : g * z (principalIdele x)
      = stdEmbFin (U.of (by simp) ((x.1 / star x.1) • 1) (by simp)) * g), stdSpace_weightRep_apply,
              hf.2 _, weylRep, Units.smul_def, schur_smul, @starRingEnd_apply E,
              ← prod_mul_distrib, ← zpow_add₀, ← zpow_natCast, ← _root_.zpow_mul]; tauto)]
  · exact (det_eq_sign_charpoly_coeff _).trans (tendsto_nhds_unique
      ((hr.tendsto_charpoly_coeff ..).const_mul _)
     ((tendsto_mostFrobeniiAt (AlgHeckeChar.avatar _ · |>.1)).congr' (mem_inf_of_left
      ((AlgHeckeChar.eventually_avatar_frob _).mp (eventually_mostFrobenii he.2 fun y a e ↦ e.trans
      (by simpa [heckeCoeff] using congr(ιℓ $((H ..).2 (v_uniformizer _) (a y.prime_q).2))))))))
  have h := (Subtype.ext (Units.ext (by simp [z]; simp [atSplit, ← map_inv, locGL, locIdele, ←
    diagonal_one, star_eq_conjTranspose])) : z (locIdele w x) = atSplit hw (.scalar n x)) ▸ h _
  exact ⟨(by simp [·, h · ·]), fun hx _ ⟨m, _, _, ht⟩ ↦ by simp [*, h _ (by erw [← ht,
    ← heckeSplit_dual hw 0 _ m hx (zero_add _).symm, heckeGL_zero (by rwa [← mem_sphericalAt_iff,
    sphericalAt, maxCompactAt, Gf.supportedOn_star])]), ← Complex.ofReal_pow, field, ← pow_mul']⟩
end

section
/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Depth-zero type induced from determinant characters yields a sorted tame Iwahori
eigenvector. -/

open Matrix Valued IsLocalRing MulChar Fintype Fint Submodule Pi Function Polynomial
attribute [-simp] MulCharClass.map_nonunit

/-- Let ρ be smooth unitary, cyclic subrepresentations having finite-dimensional I₁-invariants;
χ_a distinct, ∑m_a = N, Y = ∏_a (χ_a∘det in dimension m_a), x fixed by 1+𝔭M_N(𝒪), ∑ conj
Y(g) g x ≠ 0. Then translates of x span a ξ-eigenvector, |ξ_i(ϖ)| non-increasing, ξ_i = χ_a
on units m_a times.

Known result: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t
I. -/
lemma exists_sorted_of_detChar {F} [Field F] [Valued F _] [CompactSpace 𝒪[F]] {N} {ρ : Rep ℂ (GL
  (Fin N) F)} [IsSmoothRep ρ.ρ] {ϖ B x} (hϖ : v ϖ.1 = .exp (-1)) [∀ x, Module.Finite ℂ ((cyclicSpan
  ρ.ρ x).submoduleOf (levelSpace ρ.ρ proIwahori 1))] (hB : IsUnitary ρ.ρ B) {n r χ} [Fintype n] (e :
  n ≃ _) (hχ : Injective χ) {m : Fin r → _} (hm : ∑ a, m a = N) (hx : ∀ k, intGL.map (residue 𝒪[F])
  k = 1 → ρ (reindexGL e k.1) x = x) {s : _ → _} (_ : ∀ g, intGL.map (residue _) (s g) = g) (h : ∑ᶠ
  g, star ((∏ a, (detChar (χ a)).rankPart (m a)).evalGL g) • ρ (reindexGL e (s g).1) x ≠ 0) : ∃ y ∈
  cyclicSpan ρ.ρ x, ∃ θ, IsIwahoriEigen ρ (torusChar θ) y ∧ (Antitone fun i ↦ ‖(θ i ϖ : ℂ)‖) ∧ ∀ t
  (h : v t.1 = 1), ∏ i, (X - C (θ i t).1) = ∏ a, (X - C (χ a (residue 𝒪[F] ⟨t, h.le⟩))) ^ m a := by
  let := e.linearOrder
  obtain ⟨b, hb, rfl⟩ : ∃ b, Monotone b ∧ (card {i // b i = ·}) = m := ⟨_, (Tuple.monotone_sort
    (_ ∘ equivOfCardEq (by simp_all))).comp (by tauto), funext fun a ↦ (card_congr
    ((e.trans (.trans ..)).subtypeEquivOfSubtype.trans (.sigmaSubtype a))).trans (card_fin _)⟩
  have H g z w := by simpa [inv_mul_eq_one] using hx ((s w)⁻¹ * (g * z))
  choose _ h using by simpa using (sum_evalGL_prod_eq_zero_iff b (fun _ ↦
    lift_detChar (faithfulChar 𝓀[F]) rfl) _ (by grind)).2.mt h
  set y : ρ := Finset.sum ..
  have hu g : (BlockTriangular _ e → _ = (∏ i, χ (b i) (intGL.map (residue _) g i i)) • y) ∧ (_ →
    ∃ c, ρ (reindexGL e g) y = c • y) := (fun E : ∀ h, _ = (∏ a, χ a (blockHom b a ⟨intGL.map
    (residue _) g, h⟩).1.det) • y ↦ ⟨fun h ↦ (E fun _ _ c ↦ h (hb.reflect_lt c)).trans (by
    rw [← prod_fiberwise b]; congr!; rw [det_of_isUpperTriangular h.submatrix, map_prod]; congr!
    omega), (⟨_, E ·⟩)⟩) fun h ↦ by simpa [y, Finset.smul_sum, smul_smul, *] using .symm (sum_equiv
    (.mulLeft ⟨_, h⟩⁻¹) _ _ (by simp [inv_apply', mul_assoc, star_apply', starRingEnd_apply]))
  replace hu g (h : g ∈ intGL ..) := by
    simpa [↓(reindexGL e).apply_symm_apply, reindex_equiv e.symm, reindexGL, parabolic,
      BlockTriangular] using (hu ⟨(reindexGL e).symm g, h.elim (⟨reindexGL e.symm ·, · ▸ rfl⟩)⟩)
  lift ⇑(residue 𝒪[F]) to F → 𝓀[F] using ⟨⟩ with R hR
  have k a m := congr($hR ⟨a, m⟩).trans ∘ residue_eq_one_iff_lt.2
  have ⟨_, _, _, σ, hs, z, hz, Z⟩ :=
    exists_sorted_of_type hϖ (by simp_all [mem_proIwahori_iff_blockParahoric, mem_blockParahoric,
    mem_intGL]) (fun _ o ↦ (hu _ o).1 (by simp_all [ne_of_gt])) (fun σ o ↦ (hu _
    (permGL_mem_intGL σ)).2 fun i j _ ↦ by simp [show σ.symm i ≠ j by grind [hχ (ext
    ((surjective_units_map_of_local_ringHom _ residue_surjective inferInstance).forall.2 fun a ↦ by
       simpa [mulSingle_apply, apply_ite, ← hR, *] using! o j (a.map _) ((Valuation.integer.integers
         _).valuation_unit _)))]]) hB h
  exact ⟨z, span_le.2 (by simp [y, sum_smul_mem, ← Module.End.mul_apply, ← map_mul,
    mem_span_of_mem]) hz, _, Z, hs, fun t h ↦ by simpa [mulSingle_apply, apply_ite, *] using
    (((σ.trans e.symm).prod_comp _).trans (prod_fiberwise' b fun a ↦ X - C (χ a _)).symm)⟩
end

section
/-! Known result: the pointwise step of the Eichler–Shimura congruence relation for GU(1,n−1) at a
split place. Only the geometric step is treated, namely that at each geometric point of the special
fibre the Frobenius-twisted Hecke neighbour of a subspace depends only on its sum with one fixed
non-zero subspace. No ordinary locus is used, and the Möbius sum is taken with the model. Source:
Wedhorn, Congruence relations on some Shimura varieties, J. reine angew. Math. 524 (2000) 43–71; for
the method, Katz–Mazur 1985 ch. 13, Harris–Taylor 2001 III.4; for Weisner's theorem, Stanley, EC1
Cor. 3.9.3.

This file: Frobenius-twisted reduced Hecke neighbours of A depend only on A + W, some W ≠ 0. -/

open Matrix _root_.Module ThetaObject AddSubgroup AlgebraicGeometry CategoryTheory FiniteField
  IsGroupBaseChange QuadField NumberField Pic CartesianMonoidalCategory Category Over

/-- Let β = (1 + √−d₀)/2, let z and its Hecke neighbours z·g_A (A ⊆ k_wⁿ a subspace) have
V-points s, α(A), and let V → k be onto an algebraically closed field, with s reducing above
a safe, good split place w of norm q. Then for some subspace W ≠ 0, Frob_q^{n−dim A} of the
reduction of α(A) depends only on A + W.

Known result: Eichler–Shimura congruence relation for GU(1,n−1) at a split place: the pointwise
step. -/
lemma UniversalFamily.congruence_step {E k d d₀} [Field E] [CMBase E] {D R} [HasQuadSubfield d₀ E]
  (U : UniversalFamily D R) (hβ : D.β = algebraMap _ _ (c₀ d₀)) {V : ValuationSubring ℂ} {z :
  ModuliPoint E D.Index d} {s} (o : U.family.IsPointOf 1 z s) {w : SplitFinPlace E} [Field k]
  [IsAlgClosed k] {π : V →+* k} (hπ : (⇑π).Surjective) {x₀ : ThetaObject U.family _}
  (b₀ : x₀.IsPullbackAlong (specMap π) (s ≫ hom _)) (hk : w.1.1 = RingHom.ker x₀.baseHom) (hw :
  D.IsGoodAt w.1.1) (hG : IsSafe D.𝔑 w) {l} [Fact l.Prime] [CharP k l] {m α : Submodule .. →
  _} (hq : ∀ A, l ^ m A = w.1.q ^ (D.rank - finrank (ResField w.1) A)) (S : ∀ A,
  U.family.IsPointOf 1 (z.act ⟨_, heckeIsogeny_mem_GUPlus w A⟩ 1) (α A)) : ∃ W ≠ ⊥,
  (fun A ↦ specMap ((iterateFrobenius _ l (m A)).comp π) ≫ α A).FactorsThrough (· ⊔ W) := by
  obtain ⟨⟨e, rfl⟩, _, b, _, _, hb, co, _⟩ := o, hw.2
  choose y' _ _ _ S a using (ThetaFamily.isPointOf_iff .. |>.1 <| S ·)
  choose r ψ _ _ p o s using fun A ↦ e.exists_isogeny 1 (by simp [ratConj, ModuliPoint.act]) (S A)
    (by simp [ModuliPoint.act]) (heckeIsogeny_mem_GUPlus w A).2 isScalarFrame_heckeIsogeny
  choose σ hσ σ₂ _ K L using exists_residue_torsion_emb (n := D.Index) w.1
  have J {C v} := σ₂ ▸ heckeIsogeny_torsionClass C v hβ hG co hb
  have q := by simpa [← hβ,
    ← D.star_beta] using congr(algebraMap _ (𝓞 E) $(absNorm_span_eq_mul_star d₀ (c₀ d₀ - b)))
  simp_rw [hk, pointOf_hom] at hw hb σ₂ b₀
  obtain ⟨⟨_, ⟨_, ⟨t, rfl⟩, T, ht⟩, -⟩, ⟨_, c, h2⟩, i, j⟩ :=
    σ₂ ▸ exists_param_pow_card_eq_zero hw e.fullStructure b₀,
    co.pow (n := m ⊥), by simpa [CharP.intCast_eq_zero_iff] using Ideal.mem_of_dvd _ ⟨_, q⟩ hb
  let μ := l ^ m ⊥
  set υ' := (D.β - b) ^ m ⊥
  choose x hp using (y' · |>.exists_isPullbackAlong _)
  have hM B : l ^ m B * _ = μ := (by simpa [μ, hq] using pow_sub_mul_pow _ B.finrank_le)
  let F B : map (specMap ((iterateFrobenius _ l _).comp π)) ⟶ map (specMap π) := ⟨fun T ↦
    homMk _ (by simpa [specMap] using! (absFrobenius_comm ..).trans (T.3 ≫= comp_absFrobenius (m B)
    (.mk (𝟙 _)) (𝟙 _)) =≫ _), by simp [absFrobenius_comm, OverMorphism.ext_iff]⟩
  choose g Hg lg G using fun B ↦
    b₀.isGroupBaseChange.exists_hom_baseChange (hp B).isGroupBaseChange (F B) (ψ B)
  have cg B : pull (g B).1 (ThetaObject.lineBundle _).picClass = μ • _ := (by
    rw [← hM, mul_nsmul, picClass_pull_absFrobenius _ _ x₀.isProjEmbedding.1,
      (hp B).lineBundle_eq_pull, b₀.lineBundle_eq_pull]
    simpa [← pull_picClass, pull_comp,
      p] using! congr(pull $(Hg B (𝟙 _)).1 (ThetaObject.lineBundle _).picClass))
  have _ B := finite_flat_of_quasiFinite _ (locallyQuasiFinite_of_pull_picClass (isProjEmbedding _)
    NeZero.out (cg B)) ⟨fun z ↦ ((ψ B).1.surjective _).elim fun a e ↦
    (Scheme.exists_preimage_of_isPullback b₀.isGroupBaseChange.1 a _
    (by simpa [specMap, ← (ψ B).w, e, -Over.w] using! congr($((hp B).schemeMap.w) z))
    ).imp fun c k ↦ (IsClosedImmersion.isStableUnderBaseChange.1 (hp B).isGroupBaseChange.1.flip
    (.spec_of_surjective _ ((bijective_iterateFrobenius ..).2.comp hπ))).2.injective
    (by simpa [*, F, absFrobenius_apply, pointEquiv_apply] using congr($(Hg B (𝟙 _)).1 c))⟩
  have Δ C {v} := o C v ▸ map_eq_zero_iff _ (S C).fullStructure.injective
  have κ C x := K x ▸ (Δ C).trans (by erw [L _ (⟨_, (heckeIsogeny_mem_GUPlus w _).2 · ·⟩),
    heckeIsogeny_inv_at_eq_basicCosetRep hG, (basicCosetRep_spec _).2])
  have Z {C v} h : μ • torsionClass v = 0 :=
    (torsionClass_mulVec_eq_zero · ((@Δ C v).1 h)) |> fun H ↦ by
    rw [mulVec_mulVec, gram_inv_of_gram_eq isScalarFrame_heckeIsogeny.2.choose_spec] at H
    rw [← hM, mul_smul, smul_eq_zero_of_right]
    simpa [map_smul', ← map_nsmul, mul_mem, star_mem_Ô,
      (heckeIsogeny_mem_GUPlus w C).2, -coe_units_inv] using! H
  have K {B T} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {t u} (hu : u ≫ g B = 0) :=
    (e.isRigid_pullback _ b₀).eq_zero_of_pairing_eq_zero (B :=
    T) (id_comp _) (u ≫ (μ • 𝟙 _)) 0 _ (b₀.isGroupBaseChange.pointEquiv.map_eq_zero_iff.1
    (by simpa [eq_zero_iff_factors_zero_section, pointEquiv_apply,
    b₀.isGroupBaseChange.nsmul_id_comp, -comp_nsmul] using! (ker_factors_of_torsionPoint
    e.fullStructure (ψ B) _ (torsionClass_induction (⟨𝟙 _, by simp [← map_nsmul, Hom.zero_def,
    @Z B · ·]⟩)) ((F B).1 (.mk t) ≫ b₀.isGroupBaseChange.pointEquiv u) (by simp [← Hg, hu]))))
    (by simp [← x₀.hasClassLaws.1.nsmul_class_pairing, cg B ▸ pairing_comp _, hu, pairing.eq_1])
  let Φ (A : Submodule (ResField w.1) _) : A →+ _ := .mk' (toUnit ((map (specMap π)) (specOver k
    k)) ≫ e.fullStructure.torsionPoint.comp σ ·.1) (by simp)
  have M A o : l ^ m A * .card (Φ A ⁻¹' {o}) = ite (o ∈ (Φ A).range) (μ / .card (Φ A).range) 0 := by
    split_ifs with h
    rw [← h.choose_spec, Nat.card_congr ((Φ A).fiberEquivKer _), ← hM A, ← card_ResField,
      ← index_ker, ← natCard_eq_pow_finrank, ← (Φ A).ker.card_mul_index]
    simp [← mul_assoc, index_ne_zero_of_finite]
    simp [Set.preimage_singleton_eq_empty.2 h]
  have Y {N} [AddCommGroup N] [Module (𝓞 E) N] {s : N} (h :
    μ • s = 0) := by simpa [← mul_comm i, j,
    (mod_cast h : (l : 𝓞 E) ^ m ⊥ • s = 0), mul_pow, mul_smul] using congr($q ^ m ⊥ • s).symm
  choose ν _ W using fun {A A'} (h : (Φ A').range = _) ↦
    exists_factor_through_isogeny (g A) _ fun B ↦ fun u hu ↦ by
    have H C := (exists_ker_parameter e.fullStructure b₀ hb co _ _ (Y (by
      simpa using congr(b₀.isGroupBaseChange.pointEquiv $(K hu)))) (nullstellensatz_exists_le_ker
      bot_ne_top).choose).choose_spec.2 (ψ C) ⟨_, hσ.injOn.injective.codRestrict
      fun x : C ↦ σ₂.le ⟨x, rfl⟩⟩ _ ((F C).1 (specOver k B)) (comp_absFrobenius _ (.mk _) (𝟙 _))
    simpa [← Hg, ← map_smul, ← ModuleObj.comp_smul, κ] using ((H A').2 · <| by erw [← pow_mul, M, h,
      ← M, pow_mul, (H A).1 _ _ rfl (torsionClass_induction fun v g ↦ Subtype.exists.2 <| by
     apply (J.2 _ (Y (Z g)) ((Δ A).1 _)).imp <;> simp +contextual [← κ, g]) (by simp [← Hg, hu])])
  have P {A B j} (a : 𝓞 E) (h : g A ≫ j = a • g B) := pairing_eq_of_fpqc_cover (.id_horiz _) (g A)
    (a • 𝟙 _) (g A) j (g B) (by simp [h, ← IsLinear.smul_comp, ← pairing_comp]; rw [cg, cg]; simp)
  use _ ∙ t, T ∘ by simp +contextual, fun A' A h ↦ ?_
  have hN : (Φ A').range = (Φ A).range := by simpa [Φ, SetLike.ext_iff, ht,
    Submodule.mem_span_singleton,
    (algebraMap_ResField_surjective _).exists] using congr((Φ $h).range)
  obtain ⟨j, _, hj⟩ := exists_factor_through_isogeny (g A') _ fun T ↦ fun y hy ↦ by
    simpa [add_smul, mul_smul, ← W hN.symm, reassoc_of% hy, ((S A).isRigid_pullback _ (hp
      A)).eq_zero_of_pairing_eq_zero (id_comp _) (y ≫ (υ' • g A)) _ (𝟙 _) (by simpa using _ ≫= K hy
      =≫ (υ' • g A)) fun _ i ↦ by simpa [pairing_comm _ (i ≫ _), pairing.eq_1 _ _ 0, υ', hy,
      pairing_pow_smul_adjoint] using (P _ (W hN) · (i ≫ y))] using congr(y ≫ ($h2 • g A)).symm
  open Fint in have ⟨t, q⟩ := ((S _).isRigid_pullback _ (hp _)).eq_of_hom (id_comp _) (by
    ext a; simpa [(hp _).baseHom_eq_comp, iterateFrobenius, ← card_ResField, r,
      ← algebraMap_ResField_eq_zero, b₀.baseHom_eq_comp, pow_card_pow, hq] using
      (congr(a ^ l ^ m A' - a ^ l ^ m A ∈ $hk))) j (hl := ⟨((epi_of_epi_left _).1 _ _ <| by
    simpa [← assoc, ← hj] using (lg A).2 ·)⟩) (pairing_eq_of_fpqc_cover (.id_horiz _) (g _) (𝟙
    _) (𝟙 _) j j (by simp [pairing_comm, hj, by simpa using P 1 (by simpa)])) (Subtype.forall.2
    (torsionClass_induction fun v h ↦ by simp [(hp _).levelPoints_eq_pullSection,
    (S _).fullStructure.eta_eq, ← G, hj, ← J.1 h ▸ o _ v]))
  simp [fibrePower_ext_iff, a, ModuliPoint.act, ↓← by simpa using s, -comp_left, ← comp_left_assoc,
    ← (hp _).isGroupBaseChange.pullSection_comp_assoc, ← G, (hp _).comp_toFamily, ← q, hj, hp, t]
end

section
/-! Known result: integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation.
Here the smooth proper base is a closure of theta values with no moduli property, and the congruence
relation at good split places is part of the statement. The covers are reduced projective closures
of tuples of isogenous points, are Galois on points in characteristic zero, and are not claimed
smooth. Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties, 2001,
III.4; Kottwitz, Points on some Shimura varieties over finite fields, JAMS 5 (1992), §5.

This file: Integral Kuga-Sato model with Hecke covers and congruence relation exists. -/

open Algebra _root_.RingHom CategoryTheory Classical ReducedClosure UniversalFamily Filter Finset
  Function IsLocalRing NumberField QuotientGroup AlgebraicGeometry.Spec Category

attribute [-simp] sup_of_le_left sup_of_le_right

attribute [local simp] datumPoint_eq_iff ModuliPoint.act ModuliPoint.isLevelIso_iff QuotientGroup.eq
  ratConj mul_assoc

/-- Given a universal family for D over R (`UniversalFamily`), if the level 𝔑 is neat, β = (1 +
√−d₀)/2 and every safe place is good for D, then for any positive finite number of marked
points there is a model of level 𝔑 over R (`Model`).

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation. -/
lemma exists_model {E} [Field E] [CMBase E] {d₀} [HasQuadSubfield _ E]
  {R} {D : PEL E} (U : UniversalFamily D R) (hN : IsNeat D.Index D.𝔑) (hβ : D.β =
  algebraMap _ _ (QuadField.c₀ d₀))
  (hG : ∀ w, IsSafe D.𝔑 w → D.IsGoodAt w.1) ν [NeZero ν] : Nonempty (Model D.Index d₀ D.𝔑 ν R) := by
  choose M hM using exists_level_conj_mem (n := D.Index) hN.1
  let Q i := _ ⧸ ((levelGU _ (M i)).subgroupOf (levelGU D.Index D.𝔑)).normalCore
  let γ i (j : Q i × ↥(insert (M i, 1) (insert 1 i))) :=
    (j.2.1.1, ⟨_, mem_GUPlus_of_mem_levelGU j.1.out.2⟩ * j.2.1.2)
  obtain ⟨⟨hs, sj, m, hm⟩, C⟩ := U.fibrePower_spec ν, (ofNonempty : ∀ i, U.GraphClosure (γ i) ν)
  have L {i x a} k := ((C i).point_comp_proj a (⟦k⟧, x)).trans (c := datumPoint x.1.1
    (a.act (⟨_, mem_GUPlus_of_mem_levelGU k.2⟩ * x.1.2))) (datumPoint_eq_iff.2 ⟨1, by
    simpa using! hM i _ x.2 _ (QuotientGroup.eq.1 (k : Q i).out_eq.symm 1)⟩)
  choose p P pp using fun {i} (κ : levelGU _ D.𝔑) ↦
    (C i).exists_lift (·.act ⟨_, mem_GUPlus_of_mem_levelGU κ⁻¹.2⟩)
    (fun j ↦ (C i).proj (κ⁻¹ * j.1, j.2)) fun _ ↦ (·.1.out_eq ▸ (L _).trans (by simp [γ]))
  choose u hu using fun i ↦ (@factorsThrough_iff (Σ' g f, ∀ a, (C i).point a ≫ f = U.datumPoint 1
    (a.act g)) (_ ⧸ levelGU D.Index D.𝔑) _ (·.1) (·.2.1) ⟨(C i).proj ⟨1, 1, by simp⟩⟩).1 fun p q e ↦
    (isSeparatingFamily _).hom_ext fun a ↦ by simpa [p.2.2, q.2.2] using ⟨1, by simpa using e.symm⟩
  let s i := {g | ∃ h, ∀ a, point _ a ≫ u i ⟦g⟧ = datumPoint 1 (a.act ⟨g, h⟩)}
  have o i : 1 ∈ s i := ⟨one_mem _, fun _ ↦ congr(_ ≫ $(hu i)
    ⟨1, (C i).proj ⟨⟦1⟧, 1, by simp⟩, by simp [↓L]⟩).symm.trans (by simp [↓L])⟩
  have hc {i} := by simpa using (o i).2
  have T {g k i j f} (h : ∀ a, (C i).point a ≫ f = (C j).point (a.act ⟨g, k⟩)) ⦃q⦄ (H : q ∈ s j) : f
    ≫ u j ⟦q⟧ = u i ⟦g * q⟧ := congr($(hu i) ⟨⟨_, mul_mem k H.1⟩, _, by simp [reassoc_of% h, H.2]⟩)
  refine ⟨_, _, s, u, o, fun j hg ↦ (eventually_all.2 fun x ↦ eventually_finset_mem_atTop ((γ j
    x).1, (⟨_, hg⟩ * (γ j x).2 :))).mono fun i h ↦ ((C j).exists_lift (·.act ⟨_, hg⟩) ((C i).proj
    ⟨⟦1⟧, _, mem_insert_of_mem <| mem_insert_of_mem <| h ·⟩ :) (by simp [↓L])).elim fun f h ↦
    ⟨⟨hg, by simp [← by simpa using T h.2 (o j), ← assoc, *]⟩, f, T h.2⟩, (.of <| Q ·), fun _ ↦
    lift _ ⟨⟨(.of <| p ·), End.ext ((isSeparatingFamily _).hom_ext (by simp [pp]))⟩, fun _ _ ↦
    End.ext ((isSeparatingFamily _).hom_ext (by simp [pp, ← assoc]))⟩ fun κ h ↦ End.ext <|
    hom_ext _ fun j ↦ by erw [P,
    mul_eq_right.2] <;> simp [h], fun _ ↦ Quot.ind (⟨·⁻¹, T (pp _)⟩), m, _, (C · |>.point_surjective
    hc), by simp [*], fun g α a h ↦ by simp [reassoc_of% h.2, *, -ModuliPoint.act], _,
    hs, fun i ↦ isGaloisCovering_of_complex_points (fun k _ _ f ↦ let := f.toAlgebra
    ((IsAlgebraic.trans _ (𝓞 E) _).tower_bot_of_injective Subtype.val_injective).injective_tower_top
      R Int.cast_injective) (Quot.ind fun _ ↦ (T (pp _) (o _)).trans (by congr 1; simp))
    (sj.surjective _ _ (congr($(hc ·).1))) (((C i).point_surjective hc).forall₂.2 fun x y e ↦
    existsUnique_of_exists_of_unique ((datumPoint_eq_iff.1 (hc x ▸ hc y ▸ e)).elim fun z r ↦
    ⟨⟦⟨_, r.mem_level.1⟩⟧, (pp ..).trans ((C i).exists_level_point_eq.choose_spec ⟨by simp,
    r.reflection_eq, by simpa using r.sub_mem_lattice⟩)⟩) (mk_surjective.forall₂.2 fun κ κ' e e' ↦
    QuotientGroup.eq.2 fun q ↦ (datumPoint_eq_iff.1 (L _ ▸ L _ ▸ (pp
    ..).symm.trans (e ▸ e' ▸ pp ..) =≫ (C i).proj ⟨⟦κ * q⁻¹⟧, _, mem_insert_self
    ..⟩)).elim fun z r ↦ ?_)), fun i g α a _ _ h x y z ↦ ?_, fun w H i _ N h l m _ f k _ _ x X ↦ ?_⟩
  · cases hN.2 x.isSignedFrame
      (by simpa [mul_mem_cancel_left] using mul_mem r.mem_level.1 q.2) r.reflection_eq
    simpa using r.mem_level.2
  · choose f h0 e _ hb using exists_ball_family a
    obtain ⟨⟨K, k⟩, σ, hσ⟩ := hb x y z, ((C i).holomorphicAt_point a.P 0 h0).exists_isJet .id
    have T x :
      IsJet (f.ballPoint a.P · |> (C i).point |>.left) 0 (.applyₗ x) (specMap (TrivSqZeroExt.map
      (.applyₗ x)).1 ≫ σ) := (by simp [PointFn.isRegularOn_ofSection _ _, hσ · · ·, LandsIn.comp])
    have S x := ((T x).comp_hom _).congr (.of_forall fun _ ↦ congr($(hc _).1))
    exact ⟨.of ℂ _, ⟨Over.homMk _ ((hσ.comp_base_eq fun _ ↦ Over.w _).trans (map_comp ..).symm)⟩,
      K, by simp [(f.torus 0).isPeriodMap.finrank_eq_abelianDim], congr(⟨$(Over.OverMorphism.ext
      (e ▸ hσ.fst_comp :))⟩), fun x y e ↦
      sub_eq_zero.1 ((U.isHolImmersionAt_datumPoint 0 h0).2 _ (isFirstOrderConst_iff.2 fun U f i ↦
      by simpa using! congr($((S x U f i).2.symm.trans (congr(PointFn.ofSection f _ $e.1.1).trans (S
      y U f i).2)).snd))), fun x ↦ ULift.up_inj.2 (Over.OverMorphism.ext (((isJet_comp_iff
      (ContinuousLinearMap.mk K).hasFDerivAt (U.isHolImmersionAt_datumPoint _ (by simpa)).1).2
      (K.map_zero ▸ S _)).unique (((T x).comp_hom _).congr (k.1.mono fun q r ↦ congr($(((reassoc_of%
      h.2) _ _).trans ((hm ..).trans (datumPoint_eq_iff.2 ⟨_, by simpa using r⟩))).1)))).symm), k.2⟩
  obtain ⟨z, ρ, ⟨⟩, -⟩ := exists_countable_residue_point (Over.hom _) x
  choose V α b ρ' r S using (C i).exists_arc z
  rcases ρ.charP ρ.injective, charP_of_injective_ringHom ρ'.injective, @Fintype.toLocallyFiniteOrder
  refine (U.congruence_step hβ (S (hc b)) residue_surjective rfl (w.1.isMaximal.eq_of_le (ker_ne_top
    _) fun a h ↦ ?_) (hG _ H) H (fun _ ↦ f ▸ pow_mul' ..) (S <| h · |>.2 b)).elim fun W G ↦ .mono
    (.mono ((FreeAbelianGroup.equivFinsupp _).injective (Finsupp.ext
    (IncidenceAlgebra.moebius_inversion_bot _ 0 (fun A ↦ by by_cases W ≤ A <;> simp [‹_›, sum_ite,
    ← @Int.cast_inj ℂ, prod_eq_zero (i := 0), q_binomial_submodule,
    zero_lt_iff, ne_bot_of_le_ne_bot G.1, ← card_ResField, Finsupp.single_apply, -zsmul_eq_mul,
    sum_fiberwise_eq_sum_filter, filter_filter]) · |>.trans (by simp)))) G.2) fun A B t ↦ ?_
  · erw [ThetaObject.baseHom, ← assoc, preimage_comp]
    simpa [← reassoc_of% r, ← (u i ⟦1⟧).w] using X _ (N a h)
  simp [specMap] at t
  simp [← reassoc_of% r, ← map_comp_assoc, ← CommRingCat.ofHom_comp, ← iterateFrobenius_comm] at t ⊢
  simpa [cancel_epi] using t
end

section
/-! Part of: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish (known
result; see Lib.Shimura.TraceFormula.MarkedEqDefinite).

This file: Trace of a Hecke operator on definite algebraic modular forms as orbital sum. -/

variable {E : Type} [Field E] [CMBase E] {n : Type} [Fintype n] (𝔑) {W} [AddCommGroup.{0} W]
  [Module ℂ W] (ξ : Representation ℂ (GL n E) W)

/-- The W-valued functions φ on GL_n of the finite adeles with φ(yx) = ξ(y)φ(x) for y in GL_n(E),
right K(𝔑)-invariant, and zero at every x without `IsSignedFrame` x 1. -/
noncomputable abbrev definiteForms :=
  ξ.coindV toFinGL ⊓ .pi {x | ¬IsSignedFrame x 1} ⊥ ⊓ levelSpace (rightRegular ..) (levelGU n 𝔑)

open Set Submodule

attribute [local simp] eigenReflection subset_def countTerm_mk ratConj mul_assoc

/-- The action of the Hecke algebra of level K(𝔑) on `definiteForms` by right translation. -/
noncomputable def definiteForms.rep := Representation.subrepresentation
  ((rightRegular ..).asAlgebraHom.comp (heckeAlgebra n ℂ 𝔑).val).toMonoidHom (definiteForms 𝔑 ξ)
  fun a φ h ↦ ⟨(comap ((rightRegular ..).asAlgebraHom.toLinearMap.flip φ) (_ ⊓ _)).span_le.2
  (by simp_all [↓image_subset_iff, isSignedFrame_mul_iff 1, GUPlus]) a.2.1, a.2.2 h.2⟩

open _root_.Quotient

/-- Trace formula, definite side: for E⁺ ≠ ℚ, 𝔑 neat, W finite-dimensional, the forms are
finite-dimensional and finitely many orbits of definite triples count; if a is regular and
tr ξ(y⁻¹) = ∑_μ w(P, μ) for separable P, then tr a is their orbit sum.

Known result: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish. -/
lemma trace_definiteForms {𝔑} [Module.Finite ℂ W] (hN : IsNeat n 𝔑) a w :
  Module.Finite ℂ (definiteForms 𝔑 ξ) ∧ (countTerm False a w).support.Finite ∧
  (IsRegularHecke a → (∀ y, y.1.charpoly.Separable → (ξ y⁻¹).trace ℂ _ =
  ∑ i, w y.1.charpoly i) → (definiteForms.rep 𝔑 ξ a).trace ℂ _ = ∑ᶠ c, countTerm False a w c) := by
  let I := {c : DoubleCosets toFinGL.range (levelGU n 𝔑) // IsSignedFrame c.out 1}
  cases @nonempty_fintype I ((finite_isSignedFrame_classes (isOpen_congruenceGL_span hN.1)).subset
    fun c ↦ (⟨_, ⟨_, ·⟩, c.out_eq⟩))
  choose c γ e using by simpa [← inv_mul_eq_iff_eq_mul, -MonoidHom.coe_range] using
    exists_eq_map_mul_rep_mul toFinGL (levelGU n 𝔑) out_eq
  have D g := by simpa using
    isSignedFrame_mul_iff (x := (toFinGL (γ g))⁻¹ * g) (ℓ := 1) (γ g) (inv_mem (e g).1)
  have i {c} {d : I} := eq_and_eq_one_of_doubleCoset_rep (c := c) out_eq fun _ ↦
    (hN.2 d.2 · (by simp))
  refine .imp_right (⟨finite_of_finite_preimage (f := fun ((c : I), y, μ) ↦ ⟦(c.1.out, y⁻¹, μ)⟧) ?A
    ?S, fun r hw ↦ .trans · ?_⟩) (trace_eq_weighted_sum (·.1.out) 1 _ (range_subtype _) 1 (s := 1)
    (fun (j : I) g ↦ ite (j = c g) {γ g} ∅) (fun j g y ↦ ?_) (by
    simp +contextual [apply_ite, Subtype.coe_eq_iff, D]) (by tauto) rfl)
  exact (finite_iUnion fun c : I ↦ (((heckeCosetFn a).hasFiniteSupport.preimage (f :=
    (⟦c.1.out⁻¹ * toFinGL · * c.1.out⟧)) fun y _ z _ h ↦ inv_mul_eq_one.1 (i _ (by
    simpa using QuotientGroup.eq.1 h)).2).prod finite_univ).image (c, ·)).subset (by simp; tauto)
  use Quotient.ind fun ⟨q, y, μ⟩ ↦ q.inductionOn fun x H ↦ ⟨(⟨_, by simp_all⟩, (_ * _)⁻¹, μ), sound
    ⟨(γ x)⁻¹, Prod.ext (QuotientGroup.eq.2 (e x)).symm rfl⟩⟩
  rw [← indicator_eq_self.2 ?S, ← finsum_mem_def, finsum_mem_range, finsum_curry₃ _ ?A]
  simp [(_ : I).2, ← Finset.mul_sum]
  congr! 3; simpa [or_iff_not_imp_right] using hw _ ∘ @r _⁻¹ _
  use fun p q h ↦ (exact h).rec fun g h ↦ by
    grind [i g (by simpa using QuotientGroup.eq.1 congr($h.1).symm), inv_inj, one_smul]
  rw [← mul_mem_cancel_left (e g)]; simp [mem_ite]
  use by simp_all, fun H ↦ by grind [i ((γ g)⁻¹ * y) (by simpa), inv_mul_eq_one]
end

section
/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Weyl character and dimension formulas for U(n) and products of unitary groups (known
result; see Lib.DiscreteSeries.Character.KTypeMultiplicity).

This file: Weyl character formula at regular semisimple elements of products of GL_n. -/

variable {a} {ι : Type} [Fintype ι]

lemma det_zpow_add {r : Fin a → ℂ} {g : GL (Fin a) ℂ} (h : ∀ i, g.1.charpoly.IsRoot (r i)) d
    (k : _ → ℤ) : (Matrix.of fun i j ↦ r i ^ (d + k j)).det = Finset.univ.prod r ^ d * (Matrix.of
  (r · ^ k ·)).det := by simpa [← Finset.prod_zpow, zpow_add₀ (spectrum.ne_zero_of_mem_of_unit
  (Matrix.mem_spectrum_of_isRoot_charpoly (h _)))] using! Matrix.det_mul_column ..

/-- Weyl's character formula: if each g_v in GL_a(ℂ) has distinct eigenvalues x_{v,i}, the trace
of `weylRep` κ e at g times ∏_v det(x_{v,i}^j) equals ∏_v det(x_{v,i}^(e_v + λ_{v,a−1−j} +
j)), with 0 ≤ i, j < a and λ the weight `diagramWeight` of κ.

Known result: Weyl character and dimension formulas for U(n) and products of unitary groups. -/
lemma trace_weylRep κ e {g : ι → GL (Fin a) ℂ} {x : ι → Fin a ↪ ℂ}
    (hg : ∀ v i, (g v).1.charpoly.IsRoot
    (x v i)) : (weylRep κ e g).trace * ∏ v, (Matrix.vandermonde (x v)).det = ∏ v, Matrix.det
    (.of fun i j : Fin a ↦ x v i ^ (e v + ↑(diagramWeight (rankAt (Fin a)) κ (v, j.rev) + j))) := by
  choose h hh using (isConj_diagonal_of_isRoot_charpoly <| hg ·)
  rw [← mul_inv_cancel_right g h, map_mul, Matrix.trace_mul_comm, ← map_mul]
  simpa [weylRep, ← (hh _).eq, mul_assoc, Units.smul_def, det_zpow_add (hg _)] using .inl
    (weyl_character 1 _)
end

section
/-! Known result: Transfer of eigensystems between inner forms of a unitary group differing at a
real place. It is shown here only that the Hecke eigensystem of a definite form occurs, in each
Hodge weight, on the variety for signature (1, n-1), for n odd and with a cuspidal type at one split
place. The proof compares two finite counts, without stabilisation. Source: Harris and Labesse,
Conditional base change for unitary groups, Asian J. Math. 8 (2004), Thm 2.1.2; Labesse, Changement
de base CM et séries discrètes (2011), Thm 5.4; count as in Goresky and MacPherson, The topological
trace formula (2003), and Shimura, On the trace formula for Hecke operators, Acta Math. 132 (1974).

Part of: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation (known
result; see Lib.Shimura.IntegralModel.ModelExistence).

Part of: Simple trace formula: Hecke trace on a definite group; non-elliptic terms vanish (known
result; see Lib.Shimura.TraceFormula.MarkedEqDefinite).

This file: Regular test function with cuspidal type that does not kill the given vector. Eigensystem
of a definite form occurs in each Hodge weight for signature (1,n-1). Lagrangians exist; PEL data
with odd theta group, good at the safe places. -/
seal Finset.univ Finset.sum Finset.prod

section

open NumberField Matrix Polynomial Submodule Set Subgroup Valued Fin Finset Fintype LinearMap
variable {E} [Field E] [NumberField E] [IsCMField E] {a 𝔑 W} [AddCommGroup.{0} W] [Module ℂ W]

/-- w₀ ≠ w₁, w₁ ∣ 𝔑, w̄₀, w̄₁ ∤ 𝔑; through `conjAtSplit`, K(𝔑) at w₀ lies in J ≤ GL_n(O_w₀),
at w₁ in I₁; χ satisfies `IsCuspidalType`; J acts on v ≠ 0 by χ, GL_n(O_w₁) trivially. -/
structure IsTestVector 𝔑 (π : Representation ℂ (GL (Fin a) (𝔸f E)) W) (v : W) (w₀ w₁ :
  SplitFinPlace E) {J} χ where
  places : w₀ ≠ w₁.1 ∧ 𝔑 ∉ (star w₀.1).1 ∧ 𝔑 ∈ w₁.1.1 ∧ 𝔑 ∉ (star w₁.1).1
  level₀ : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₀) ≤ J ∧ J ≤ Kw _ _
  isCuspidalType : IsCuspidalType J χ
  level₁ : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₁) ≤ proIwahori
  ne_zero : v ≠ 0
  mem_levelSpace : v ∈ levelSpace (π.comp (conjAtSplit _)) J χ
  fixed : v ∈ levelSpace (π.comp (conjAtSplit w₁)) (Kw ..)

/-- Let 𝔑 ≠ 0, w̄ ∤ 𝔑, K(𝔑) ∩ GL(E_w) ≤ ker χ ≤ J ≤ GL(O_w), z central, zt in `GUPlus`.
Some Hecke element b supported on Jzt sends K(𝔑)-fixed vectors to χ-eigenvectors, and Tz⁻¹bx
= y whenever T(jt·x) = χ(j)y for all j in J. -/
lemma exists_local_hecke_element (π : Representation ℂ _ W) {w J z} (c : J ≤ Kw ..) (χ :
  J →* ℂ) (hχ : ∀ g, conjAtSplit w g ∈ levelGU (Fin a) 𝔑 → ∃ h, χ ⟨g, h⟩ = 1) (hw :
  𝔑 ∉ (star w.1).1) t (cz : ∀ g, Commute g z)
  (o : z * conjAtSplit w t ∈ GUPlus E _) : let r (j : J) := conjAtSplit w j * (z * conjAtSplit w t)
  ∃ b : heckeAlgebra _ ℂ 𝔑, b.1 ∈ spanOn ℂ (Set.range r) ∧
    b.1 ∈ fixedToEigen (levelGU _ 𝔑) (conjAtSplit w) J χ ∧ ∀ {x} T y,
    (∀ j, T (π (conjAtSplit w (↑j * t)) x) = χ j • y) → (T * π z⁻¹) (π.asAlgebraHom b x) = y := by
  intro r; simp_rw [Subtype.exists, bex_def]; have n j : χ j ≠ 0 := (χ.toHomUnits j).ne_zero
  let L : OpenSubgroup (type_of% t) := ⟨_, isOpen_comap_conjAtSplit (by bound : 𝔑 ≠ 0)⟩
  let U := (L ⊓ L.comap (MulAut.conj t⁻¹) (IsTopologicalGroup.continuous_conj _)).subgroupOf J
  have := U.fintypeOfIndexNeZero ((isCompact_Kw _).relIndex_ne_zero
    (L ⊓ _).2 ∘ relIndex_eq_zero_of_le_right c); let f j := (χ j * this.card)⁻¹
  refine ⟨∑ q : _ ⧸ U, f q.out • .single (r q.out) 1, (fun H ↦ .symm ⟨H, mem_heckeAlgebra hw H.1
    (fun | _, ⟨j, rfl⟩ => ⟨mul_mem ⟨by simp, (conjAtSplit_mem_intGL_iff.2 (c j.2)).isIntMatrix_inv⟩
    o, by simp_all [r]⟩) fun _ _ _ _ _ x l ↦ ((hχ _ l.2).2 ▸ H.2.1 x _ :)⟩) ⟨sum_smul_mem _ _ (by
    aesop (add simp spanOn)),
    fun _ _ _ π _ h ↦ ?_, by simp_all [f, r, ← smul_assoc, (cz _).left_comm]⟩⟩
  simpa [r, heckeFun] using heckeFun_mem_levelSpace (χ' := χ.domRestrict ⊤) (π := π.comp
    (.domRestrict ..)) (toFinite _) (fun _ k ↦ by simp [f, (hχ k k.2.1).2]) (by simp [*, field])
    (map_mem_levelSpace_of_commute (fun k : U ↦ by simpa using h ⟨_, k.2.2⟩) fun _ ↦ (cz _).map π)

/-- Let φ be K(𝔑)-fixed with `IsTestVector`, c a Hecke element supported on similitudes trivial at
w₁, cφ = φ. For some Hecke element b and all m ≥ 1: (bc)^m φ ≠ 0, (bc)^m is regular, and sends
K(𝔑)-fixed vectors to χ-eigenvectors of J at w₀. -/
lemma exists_test_function {w₀ w₁ J χ π} {φ : W} (h₂ : φ ∈ levelSpace π (levelGU (Fin a) 𝔑)) :
  IsTestVector 𝔑 π φ _ w₁ χ → ∀ {c : heckeAlgebra _ ℂ 𝔑}, c.1 ∈ spanOn ℂ (GU E _ ⊓ (dualComponent
  w₁).ker).carrier → π.asAlgebraHom c φ = φ → ∃ b, ∀ m, π.asAlgebraHom ((b * c) ^ m).1
  φ ≠ 0 ∧ let f := (b * c) ^ (m + 1); IsRegularHecke f ∧ ↑f ∈ fixedToEigen (levelGU _ 𝔑)
    (conjAtSplit w₀) J χ := fun ⟨⟨h, n₀, n₁, hw₁'⟩, ⟨hK, hJ⟩, _, M, h₁, h₃, h₄⟩ c hc hv ↦ by
  let ρ := Rep.of (smoothVectorRep (π.comp (conjAtSplit w₁))); have ⟨t, ht, I⟩ :=
    exists_iwahoriHeckeHom_injective ρ (v_uniformizer _)
  have ⟨N, n, hz⟩ := exists_forall_mul_mem_Ô (conjAtSplit _ (diagGL t)).2.uncurry
  have ⟨b₀, u₀, a₀⟩ := exists_local_hecke_element π hJ χ (fun g hg ↦
    ⟨hK hg, smul_left_injective _ h₁ ((h₃ _).symm.trans (h₂ ⟨_, hg⟩))⟩) n₀ 1 .one_right (by simp)
  obtain ⟨b₁, u₁, a₁⟩ := exists_local_hecke_element π (z :=
    (.scalar _ (principalIdele (.mk0 N (mod_cast n))))⁻¹) (sep_subset ..) 1 (by simpa) hw₁' _
    (by simp [commute_scalar_GL]) ⟨mul_mem ⟨N * N, by simpa, 1, gram_inv_of_gram_eq (by
    simp [smul_one_eq_diagonal, -map_natCast])⟩ (by simp), by simpa [← nsmul_eq_mul'] using! hz⟩
  have o := spanOn.mul u₀ hc (forall_mem_range.2 fun _ _ ↦ Subgroup.mul_mem _ (by
    simp [dualComponent, evalAt_conjAtSplit_of_ne _ h.symm (by grind [star_star])]))
  have C : Commute (b₀ * c) _ := Subtype.ext (Commute.span_left (Set.forall_mem_image.2 fun _ h ↦
    .span_right (by simp (maxDischargeDepth := 3) [commute_conjAtSplit h, commute_scalar_GL]) _ u₁)
    _ o)
  have d := spanOn.mul (D'' := {g | ∃ s, StrictMono (v <| s · |>.1) ∧ ∃ k l : proIwahori, dualComponent _ g = k.1 *
    diagGL s * l.1}) u₁ o (fun | _, ⟨j, rfl⟩, g, p => ⟨(.mk0 N (mod_cast n) * t ·), by
       simpa [StrictMono, zero_lt_iff, n], j, 1, by simp [↓map_mul, ↓dualComponent_conjAtSplit, ↓MonoidHom.mem_ker.1 p.2,
       dualComponent, invTransposeGL, Equiv.symm, Units.ext_iff, Matrix.map_natCast, map_zero]⟩)
  use b₁ * b₀, mul_assoc b₁ .. ▸ fun m ↦ ⟨(?_ : _ ∈ (levelSpace (π.comp (conjAtSplit w₁))
    proIwahori).carrier \ {0}).2, fun y x hy ↦ ?_, fun _ _ _ _ _ h ↦ ?_⟩
  induction' m with m ih; simpa [*] using (h₄ ⟨·, ·.1⟩)
  simpa [pow_succ', ((C.mul_right rfl).pow_right _).right_comm, hv, -SubmonoidClass.coe_pow,
    -mem_levelSpace, by simpa using a₀.2 1 φ (by simpa using h₃)] using (Submodule.subtype _ ∘ₗ
    compactMean ρ.ρ proIwahori).exists_extend.elim fun T e ↦ ⟨a₁.1 ((_ : heckeAlgebra ..).2.2 h₂),
    ne_zero_of_map ((a₁.2 T _ fun j ↦ by simpa using! congr($e (ρ (j * _) ⟨_, _⟩))).trans_ne (mt
    ((injective_iff_map_eq_zero _).1 I ⟨⟨_, .mono (residuePreimage ..).mem_nhds_one (by simpa using!
    ih.1)⟩, (Subtype.ext <| ih.1 ·)⟩ ∘ Subtype.ext ∘ Submodule.coe_eq_zero.1) (ih.2 congr($(·)))))⟩
  obtain ⟨g, ⟨t, ht, k, l, h⟩, e⟩ := spanOn.exists_mem_of_cosetFn_ne_zero (m.rec (by simpa) fun _ ↦
    (spanOn.mul · d (by exact fun _ ⟨t, ht, k, l, h⟩ _ ⟨s, hs, k', l', _⟩ ↦
    (exists_unipotent_conj_mem_proIwahori hs.monotone (l * k').2).elim fun x ⟨hx, H⟩ ↦
    ⟨t * s, by simpa using! ht.mul hs, k * ⟨_, conj_unitriangular_mem_proIwahori ht.monotone hx⟩,
    ⟨_, H⟩ * l', by simp [*, mul_assoc]⟩)) : _ ^ (m + 1) ∈ _) hy
  choose c _ d hd e using exists_twisted_conj_diag ht 1 (by simp) continuous_id (⟨·,
    rfl⟩) (Set.mul_mem_mul (Set.mul_mem_mul k.2 rfl) (mul_mem l.2
    (M (conjAtSplit_dualComponent hw₁' (QuotientGroup.eq.1 e)).1)))
  erw [← separable_map (algebraMap _ (LocField w₁.1)), ← charpoly_map, ← charpoly_transpose,
    ← charpoly_units_conj' (_ * c), show _ * (dualComponent _ (toFinGL y⁻¹)).1 * _ =
    _ by simpa [mul_assoc, h] using congr($e.1), charpoly_diagonal, separable_prod_X_sub_C_iff]
  exact .of_comp (f :=
    v) (.subst (by simpa [funext_iff] using v_diag_eq_one_of_mem_proIwahori hd) ht.injective)
  erw [pow_succ', ← C, mul_assoc, mul_assoc, map_mul]; use a₀.1 ((c * _).2.2 h)

attribute [-simp] univ_val_map

/-- For a odd and E⁺ ≠ ℚ, the weight κ extends to ξ on GL_a(E), with x̄ ∈ ℚ(√−d₀)^× acting by
s₀(x)^{−μ} s̄₀(x)^{−A}. For σ over s₀, a CM type with Φ(v₀) = σ alone over s₀ and neat
level, eigenvalues of test vectors in `definiteForms` occur in weights z + μ ≥ 0, z the
jumps of κ at σ.

Known result: Transfer of eigensystems between inner forms of a unitary group differing at a real
place. -/
lemma exists_occursInWeight {E} [Field E] [CMType E] {a d₀} [HasQuadSubfield d₀ E] (ha : Odd a) (i :
  QuadField d₀ →+* E) s₀ (κ : Weight E) : ∃ (ξ : Representation ℂ (GL (Fin a) E) _) (μ N : ℕ) (A : _
  → ℤ), A s₀ = μ ∧ (∀ y, (stdSpace E _).weightRep κ.1 κ.2 (entryConj y) = ξ y.1) ∧ (∀ x : (QuadField
  d₀)ˣ, ξ (.scalar _ (star (x.map i))) = (∏ s, s x ^ (-A s)) • 1) ∧ ∀ σ, σ.comp i = s₀ → ∀ z ∈ jumps
  κ a σ, 0 ≤ z + μ ∧ ∀ [Ψ : CMBase E] {𝔑 w₀ w₁ J χ φ} {θ : SafePlace 𝔑 → ℕ → ℂ}, Ψ.Φ v₀ = σ →
  (∀ v ≠ v₀, (Ψ.Φ v).comp i ≠ (Ψ.Φ v₀).comp i) → IsNeat (Fin a) 𝔑 → IsTestVector 𝔑 (rightRegular ..)
  φ w₀ w₁ (J := J) χ → φ ∈ definiteForms 𝔑 ξ → (∀ w j, (rightRegular ..).asAlgebraHom (heckeSum _ ℂ
  w.1 j) φ = θ w j • φ) → OccursInWeight a N.succ θ (z + μ).toNat := have := NeZero.of_pos ha.pos
  have hu :=
    eq_univ_of_card {star s₀, s₀} (by simp [NumberField.Embeddings.card, QuadField.finrank_K])
  let p := (.comp · i = s₀)
  have hs σ : (∀ x, σ (i x) = ite (p σ) (s₀ x) (star s₀ x)) ∧ (p (star σ) ↔ ¬p σ) := show _ ∧
    (star (σ.comp _) = _ ↔ _) by grind [Finset.mem_univ (σ.comp i), RingHom.comp_apply, star_star]
  let θ := MonoidHom.mk' (fun (z : GL (Fin a) E) σ ↦ ite (p σ) (z.map σ)
    (transposeGL (z⁻¹.map (star σ)))) (by simp +contextual [funext_iff, apply_ite, Units.ext_iff])
  let u σ (j : Fin a) := κ.2 (.mk σ) + (diagramWeight (rankAt (Fin a)) κ.1 (.mk σ, j.rev) + j)
  let k σ j := ite (σ = Φ (.mk σ)) (a - 1 - u σ j.rev) (u σ j)
  (Finite.exists_le (Int.natAbs ∘ k.uncurry)).elim fun m hm ↦ by
  choose l hm using fun σ j ↦ CanLift.prf (β := ℕ) (m + k σ j) (by grind [hm (σ, j)])
  let q σ := ite (p σ) (genericSchur (l σ)) ((-.X 0) ^ m)
  have hl {R} [CommRing R] (r : Fin a → R) : @rootCoeffEval a _ _ (Finset.univ.1.map r) (.X 0) =
    -Finset.univ.prod r := by simp [*, rootCoeffEval, coeff_zero_eq_eval_zero, eval_prod, prod_neg]
  let ξ : _ →* _ := ⟨⟨fun z ↦ ((∏ σ : _ →+* ℂ, σ z⁻¹.1.det) ^ m • weylRep κ.1 κ.2
    (θ z ∘ Φ)).toLinAlgEquiv', by simp⟩, by simp [smul_smul, mul_pow, Pi.mul_comp]⟩
  have V y (h : y.1.charpoly.Separable) :
      (ξ y⁻¹).trace ℂ _ = ∏ σ, rootCoeffEval (y.1.charpoly.map σ).roots (q σ)
  let r σ : Fin a ↪ _ := numberedRoots σ y.1.charpoly
  have hP := isRoot_numberedRoots h
  let x σ : _ ↪ ℂ := ⟨fun i ↦ ite (p σ) (r σ i.rev)⁻¹ (r (star σ) i), fun _ ↦ by grind⟩
  erw [← mul_left_inj' (prod_ne_zero_iff.2 fun v _ ↦ det_vandermonde_ne_zero_iff'.2 (x (Φ v)).2),
    trace_toLin'_eq, trace_smul, smul_mul_assoc, trace_weylRep _ _ (by simp_all [θ, x, r,
       apply_ite, -coe_units_inv, -IsRoot.def, ← mem_spectrum_iff_isRoot_charpoly])]
  simp [RingHom.map_det, (y.1.map _).det_eq_prod_roots_charpoly, charpoly_map,
    prod_embeddings_eq_prod_pairs, ← Finset.prod_pow, ← prod_mul_distrib]
  congr with v
  have (w : Fin a → ℤ) := by
    simpa [← add_sub_assoc, submatrix] using (det_submatrix_equiv_self (revPerm (n := a)) _).trans
      (det_zpow_add (hP (Φ v)) (1 - a) (a - 1 - w ·.rev))
  have S := (fun σ ↦ rootCoeffEval_genericSchur_mul_det (l σ) (r σ)) (ite (p (Φ v)) id star (Φ v))
  split at S <;> simp [k, u, r, roots_eq_map_numberedRoots, x, *, ← zpow_natCast, mul_zpow, q,
    vandermonde, det_zpow_add (hP _), -_root_.inv_zpow', _root_.inv_zpow] at S ⊢ <;> grind
  refine ⟨ξ, a * numInfPlaces E * m, ∑ σ, (q σ).totalDegree, (if · = s₀ then _ else -_),
    ite_eq_left rfl, fun y ↦ LinearMap.ext fun _ ↦ (stdSpace_weightRep_apply ..).trans ?_,
      fun x ↦ by
    simp +contextual [-prod_mul_distrib, -pow_ite, ξ, weylRep, fun v ↦ (by split <;> simp [θ, *,
      smul_one_eq_diagonal, ← map_inv] : (θ (.scalar _ (star (x.map i))) v).1 = star s₀ x ^ ite (p
      v) 1 (-1 : ℤ) • 1), prod_embeddings_eq_prod_pairs, mul_comm (starRingEnd ℂ _ ^ (a : ℤ)), hs,
      schur_smul, Units.smul_def, smul_smul, ← zpow_natCast, ← _root_.zpow_mul, ← hu,
      ← zpow_sum_of_ne_zero, mul_zpow, ← zpow_add₀, -_root_.zpow_neg, mul_assoc]
    ring, fun σ ↦ Multiset.forall_mem_map_iff.2 ∘ ?_⟩
  simp [-prod_mul_distrib, ξ, prod_embeddings_eq_prod_pairs,
    fun v ↦ by simpa [mul_comm] using congr(Φ v (det $(y.2)))]
  rcongr; simp [θ, entryConj, invTransposeGL, transposeGL, @starRingEnd_apply E, apply_ite,
    Matrix.ite_apply, ← map_inv, inv_eq_left_inv y.2]
  rintro rfl n o; let j := ite (σ = Φ (.mk σ)) id rev ⟨n, Finset.mem_range.1 o⟩
  let d := m * (a - 1 + a * (numInfPlaces E - 1)) + l σ j
  rw [show _ + _ =
    ↑d by simp [d, hm, k, u, diagramWeight_apply, Fintype.card_pos]; clear * - o; grind]
  clear_value ξ; clear * - ha V hl d
  use by simp, @fun Ψ 𝔑 _ w₁ _ _ φ θ h hΨ hN hs hφ _ s c e H ↦ ?_
  have A L := List.prod_hom_rel L (f := tauHecke) (g := ↿θ) (r := fun x t ↦
    ↑x ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier ∧
    (rightRegular ℂ ..).asAlgebraHom x.1 φ = t • φ) ⟨subset_span ⟨1, by bound⟩, by simp⟩
    fun p _ _ h ↦ ⟨spanOn.mul tau_mem_spanOn h.1 fun _ ⟨U, Q⟩ ↦ Q ▸ fun _ ↦ Subgroup.mul_mem _
    ⟨(heckeIsogeny_mem_GUPlus ..).1, by clear * - hs; simp [heckeIsogeny, dualComponent]; erw
    [evalAt_centralScalar_of_ne, evalAt_conjAtSplit_of_ne] <;> simp <;> grind only [IsSafe,
    below_star, star_star, hs.places]⟩, by simp [tauHecke, *, smul_smul, mul_comm]; rfl⟩
  obtain ⟨b, hb⟩ :=
    And.elim (exists_test_function hφ.2 hs (c := ∑ L ∈ s, c L • (L.map tauHecke).prod)) (by
    simp [*, sum_mem, smul_mem, smul_smul, ← sum_smul, -SubmonoidClass.coe_list_prod])
  have T := trace_definiteForms ξ hN; cases T 1 1
  refine ((definiteForms.rep 𝔑 ξ _).isNilpotent_iff_charpoly.2
    ((charpoly_eq_mul_of_trace_pow_add _ ∅ (·) ?_).trans
    (by simp; exact charpoly_zero))).elim fun _ k ↦ (hb _).1 congr($((map_pow ..).trans k) ⟨_, hφ⟩)
  rintro ⟨⟩ <;> simp [↓toMatrix_pow, ← trace_eq_matrix_trace, ← map_pow, -map_mul]
  cases (hb ‹_›).2; rw [pow_succ, ← mul_assoc] at *; choose K L using H _ ‹_›
  let w P (k : Fin a) :=
    ((Lagrange.basis Finset.univ (numberedRoots σ P) k).comp (X * C (numberedRoots σ P k)) * ∏ s,
    rootCoeffEval (lieRoots P (numberedRoots σ P k) s) (q s)).lcoeff ℂ d / #{i | l σ j = l σ i}
  rw [(T _ w).2.2 ‹_› fun y _ ↦ ?_, ← sum_countTerm_marked_eq_definite hN (by simpa) ‹_›
    hs.isCuspidalType ‹_› _ (by simp [Prop.forall_iff, T, K 1])]
  simp_rw [finsum_countTerm_eq_sum _ (K 1), ← (K 1).toFinset.sum_coe_sort, w, ← h, mul_div,
    ← sum_div, div_eq_zero_iff] at *
  exact .inl (map_prod_rootCoeffEval_eq_zero (by simp [sum_eq_add_sum_subtype_ne _ ·, add_assoc])
    algebraicIndependent_emb (by simp [lieRoots, IsAlgClosed.card_roots_eq_natDegree])
    (dotProductBilin ℂ ℂ _ ∘ₗ (lcoeff ..).compLeft _ ∘ₗ mulLeft ..) L)
  rw [← sum_div, ← map_sum, (?_ : Finset.univ.sum _ = C ((ξ y⁻¹).trace ℂ _) *
    ∑ i, X ^ (d - l σ j + l σ i))] <;> simp [d]
  have := sum_lagrange_smul_rootCoeffEval (l σ) (numberedRoots σ y.1.charpoly); subst h
  simp [*, p, roots_eq_map_numberedRoots, ↓@prod_embeddings_eq_prod_pairs _ _ _ _
    Ψ.toPlaceEmbedding, prod_eq_mul_prod_subtype_ne _ v₀, q,
    lieRoots, ↓roots_map_conjugate, @Subtype.prop _ (· ≠ _), ← rootCoeffEval_map, -ite_mul, pow_add,
    (RingHom.injective _).eq_iff, comp_eq_aeval, mul_pow, ← mul_assoc, ← mul_sum,
    ← sum_mul, prod_ite, filter_ne', IsLieRoot] at this ⊢; rw [this]; ring

end

open NumberField InfinitePlace FractionalIdeal Algebra Ideal Nat AddSubgroup QuadField Quotient

attribute [local simp] xiForm map_ofNat RingOfIntegers.ext_iff mul_sub AddChar.map_sub_eq_div

/-- Existence of Lagrangians. For an alternating bimultiplicative pairing `e` on an abelian
group, every isotropic set lies in a subgroup equal to its own annihilator. -/
lemma exists_lagrangian {V G} [AddCommGroup V] [CommGroup G] (e : V → V → G) (l : ∀ x y z, e (x -
  y) z = e x z / e y z ∧ e z (x - y) = e z x / e z y) (h : ∀ x, e x x = 1) S (i : IsChain (e · · =
  1) S) : ∃ Λ : AddSubgroup V, S ⊆ Λ ∧ ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, e x y = 1 := i.exists_maxChain.rec
  fun M ⟨hM, k⟩ ↦ have H x : x ∈ M ↔ ∀ y ∈ M, e x y = 1 := ⟨fun hx y ↦ by grind [hM.1 hx,
    h (x - y), div_eq_one], fun H ↦ hM.2 (hM.1.insert (by tauto)) (by simp) ▸ by simp⟩
  ⟨.ofSub M (hM.nonempty_iff.1 ⟨0⟩) (by grind [=_ sub_eq_add_neg, div_self']), k, H⟩

/-- For E ⊇ ℚ(√−d) stably unramified, σ: E → ℂ, finitely many places B: some CM type with Φ_{v₀}
= σ, other Φ_v ≠ σ on ℚ(√−d), and N prime to B give at each level 0 ≠ 𝔑 ∈ (N) PEL data with
signs, β = (1 + √−d)/2, good at safe places.

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and congruence relation. -/
lemma exists_pel n {d E} [Field E] [NumberField E] [IsCMField E] [HasQuadSubfield d E] [NeZero n] [StablyUnram E]
    σ (B : Finset (FinPlace E)) : ∃ Ψ : CMBase E, (Ψ.Φ v₀ = σ ∧ ∀ v ≠ v₀, (Φ v).comp (algebraMap (QuadField d)
    E) ≠ (Ψ.Φ v₀).comp (algebraMap ..)) ∧ ∃ N : ℕ+, (∀ w ∈ B, ↑N ∉ w.1) ∧ ∀ 𝔑 ≠ 0, ↑N ∣ 𝔑 → ∃ D :
    PEL E, D.rank = n ∧ D.𝔑 = 𝔑 ∧ D.β = algebraMap _ _ (c₀ d) ∧ ∀ w, IsSafe 𝔑 w → D.IsGoodAt w.1 :=
  have P c : ∀ᶠ r in .atTop, HasPadding E r c := open Filter Fin Finset in let b := Module.finBasis ℤ _
    let v := append ![c] b
    (b.equivFun.symm.surjective (univ.sum (1 - star v * v))).elim fun n h ↦ map_add_atTop_eq_nat
      (_ + 3) ▸ mem_map.2 (univ_mem' fun _ ↦ ⟨append 1 (append v (@append _
      (∑ i, ((n * n) i).natAbs).succ _ (⇑b + n • 1) 0)), top_unique (b.span_eq ▸ Submodule.span_mono
      fun _ ⟨i, e⟩ ↦ ⟨natAdd _ (castAdd _ (natAdd _ i)), by simp [v, e]⟩), by
    erw [sum_univ_add]; have := congr(star $h)
    simp [v, sum_univ_add, mul_add, add_mul, mul_comm] at *; grind⟩)
  let i := algebraMap (QuadField d) E; .imp (fun c hΨ ↦ ⟨hΨ, by
  let β := algebraMap _ (𝓞 E) (c₀ d)
  obtain ⟨hβ : β = i (c₀ d), r, hr⟩ := rfl, ((P 1).and (P β)).exists_forall_of_atTop
  let s := (r + B.sup FinPlace.q + 2)!
  obtain ⟨_ : _ ≤ s, ha : star β = 1 - β⟩ := self_le_factorial _, by simp [*, ← map_star_CM]; ring
  obtain ⟨ξ, c, h₁, h₂, h₃, m, hm, e⟩ : ∃ ξ c, star ξ = -ξ ∧ (∀ v, 0 < (Φ v ξ).im) ∧ (∀ u ∈ Ô E,
      ψf E (u * (ξ : E)) = 1) ∧ ∃ m ∈ differentIdeal ℤ _, (s * c - 1 : 𝓞 E) = m • ξ := by
    let F := maximalRealSubfield E
    obtain ⟨⟨C, p, -, _, b, -, -, h⟩, ⟨γ, -, i, k, -⟩, μ, e⟩ :=
      exists_hasFundDomain_toAdele (E := E), ‹StablyUnram E›.exists_i_c₀,
      IsDedekindDomain.exists_add_spanSingleton_mul_eq (@coeIdeal_le_one (𝓞 F) _ _ F _ _ (span
      {↑s})) (by simp [spanSingleton_eq_zero_iff, s]) (dual_ne_zero ℤ ℚ one_ne_zero)
    choose c a o e' using by simpa [mem_add, mem_singleton_mul, -Subtype.exists] using one_le.1 e.ge
    obtain ⟨⟨μ, hμ, rfl⟩, y, h, -⟩ := (coeIdeal_differentIdeal ..).ge (spanSingleton_le_iff_mem.1 ((
      le_div_iff_mul_le (by simp)).2 (e ▸ le_add_self))), h ((Φ · (a * γ / 2 / s) - ⟨0, C + C⟩), 0)
    let z : 𝓞 E := ⟨y, by simpa using! (b h).2⟩
    exact ⟨a * γ + ↑(s * (z - star z)), μ • γ * (z - star z) +
      c • 1, by simp [← coe_star_ringOfIntegers, k, mem_maximalRealSubfield_iff_star_eq.1,
      add_comm], fun v ↦ by simp; linarith! [by simpa [field] using (lt_add_of_le_of_pos
      ((Complex.im_le_norm _).trans (dist_pi_le_iff'.1 (b h).1 v)) p)], forall_ψf_mul_eq_one.2 fun e
      h ↦ (map_mul ..).subst (algebraMap_mem_Ô.2 (((mem_inv_iff (by simp)).1 ((
      coeIdeal_differentIdeal ..).le ⟨e, h, rfl⟩) _ (by apply_rules [smul_mem_dual_one (hx := o) ..,
      Submodule.add_mem, coe_mem_one, one_le_dual_one])).choose_spec.2.subst (Subtype.prop _))),
      γ * _, (differentIdeal_eq_differentIdeal_mul_differentIdeal ..).ge (mul_mem_mul (by simp [F])
      (mem_map_of_mem _ hμ)), by
      linear_combination (norm := (simp [smul_def]; ring!)) congr($e'.1 - μ • a * $i)⟩
  let R := s.succ
  have ⟨Λ, hM, hΛ⟩ := exists_lagrangian (ψf E <| xiForm (R ^ 2 * ξ) · ·) (by simp) (by
    simp [← ψf_half, *, ← Matrix.star_dotProduct]) {x : Fin n → _ | torsionClass (R • x) = 0} fun x
    a y b _ ↦ .inl (h₃ (star (R • y) ⬝ᵥ R • x) (sum_mem (by grind [mul_mem, star_mem_Ô,
    torsionClass_eq_zero, Pi.star_apply])) ▸ by simp [star_trivial, -nsmul_eq_mul]; ring_nf)
  rw [← Λ.comap_map_eq_self (f := torsionClass.toAddMonoidHom) (@hM · <| nsmul_mem · _)] at hΛ
  let T := (ofSub {x | ∀ y : Fin n → _, torsionClass y = 0 → ψf E (xiForm (R ^ 2 * ξ) x y) = 1}
    ⟨0, by simp⟩ (by simp_all [← sub_eq_add_neg])).map torsionClass.toAddMonoidHom
  have hc : s.Coprime (.card T) := coprime_of_dvd fun p h hs H ↦ by
    have ⟨P, _, e, l⟩ := exists_isMaximal_dvd_of_dvd_absNorm' h (span {(s * c - 1) * R ^ 2})
     (by_cases (by simp [·]) fun c ↦
      h.dvd_of_dvd_pow (H.trans ((card_torsionBySet_adelicTorsion c).subst
     (T.card_dvd_of_le (K := (Submodule.torsionBySet (𝓞 E) ..).toAddSubgroup) (map_le_iff_le_comap.2
     fun x H ↦ (Submodule.torsionBySet_span_singleton_eq _).ge (torsionClass_eq_zero.2 fun i ↦ by
      simp_rw [mul_smul, ← algebraMap_smul E (_ - _), e, smul_assoc]
      exact forall_ψf_mul_eq_one.1 (fun u h ↦ by simpa [smul_def, mul_left_comm, mul_assoc] using (H
        (Pi.single i (star u)) (by grind [star_mem_Ô, Subring.zero_mem, torsionClass_eq_zero]))) m
        hm))))))
    revert hs l; simp +contextual [R, ← Int.ofNat_dvd, ← @mem_span_singleton ℤ, ← e,
      ← @eq_zero_iff_mem (𝓞 E)]
  have ho := (hc.of_dvd_left (dvd_factorial two_pos le_add_self)).odd_of_left
  refine (@eventually_isCutDegree T (card_pos_iff.1 ho.pos).2 ..).exists.elim fun i hi ↦
    ⟨⟨R ^ i.succ * .card T, by bound [ho.pos]⟩, fun w h ↦ w.2.notMem_of_isCoprime_of_mem
    ((Coprime.mul_right (by simp [R]) hc).of_dvd_left (dvd_factorial w.one_lt_q.le (by grind
    [Finset.le_sup]))).cast w.1.absNorm_mem, fun 𝔑 h0 hN ↦ ⟨⟨β, 𝔑, _, n, _, i, T, Λ.map _, ha, by
    omega, h0, ⟨hi, fun _ l t h ↦ Submodule.torsionBy_le_torsionBy_of_dvd _ _ ((mul_dvd_mul_right
    (pow_dvd_pow _ l.step) _).natCast.trans hN) (by simpa [-cast_mul, cast_smul_eq_nsmul,
    mul_nsmul] using (nsmul_relIndex_mem ⊥ h))⟩, ho, SetLike.ext_iff.1 (comap_map_eq_self (by
    exact fun x a z b ↦ (hΛ x).1 (ker_le_comap _ _ a) z (by simp [b]))), hΛ, Quot.ind (⟨·, hM ·,
    rfl⟩), hr _ (by omega), ⟨0⟩, fun v ↦ by simpa [sq, h₂, self_eq_neg] using
    congr((Φ v $h₁).re), fun v h ↦ by simpa [*] using congr(star ($((mk_eq_iff.1 (by
    subsingleton)).resolve_left (hΨ.2 v h)) (sqrtNegD d))), by simp [*, ← map_star_CM, neg_eq_self,
           Subtype.ext_iff, NeZero.ne]⟩, rfl, rfl, rfl, fun w ⟨k@⟨b, hb, t⟩, hw, h'⟩ ↦ ?_⟩⟩
  obtain ⟨⟨v, e, n, _⟩, -, q, H⟩ := k.exists_place_above_ne w w, k.star_ne_and_prime_norm
  refine ⟨by simpa [← eq_zero_iff_mem] using hw ∘ w.1.mem_of_dvd hN, _, b, q, by
    simpa using H (w.below _), by simpa using! hb, by simpa [*] using t.map (algebraMap _ (𝓞 E)),
    (coprime_of_no_prime_ge fun P c l o ↦ ?_).sup_eq, v, mt v.ext n, by
    simpa [← e] using! And.intro (H (w.below _)) hb⟩
  simp [o.mul_le, span_insert] at c l
  exact l.elim (hw <| w.isMaximal.eq_of_le o.1 · ▸ c) fun ⟨_, h⟩ ↦ h' ⟨P, o, (h0 <| ·.le c)⟩
    (((H _).2 (by simpa)).resolve_left (IsPrime.notMem_of_isCoprime_of_mem t hb <|
    · ▸ by simpa [ha] using! h)) c⟩) (by use {v₀ := mk σ, mk_Φ := ?_, Φ v := (ite (v.embedding.comp
    i = σ.comp i ↔ v ≠ mk σ) star id v.embedding)} <;> dsimp +instances <;> grind [mk_embedding,
    mk_eq_iff, ComplexEmbedding.conjugate_comp])
end

section
/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Galois representation from geometry for odd-rank forms of cuspidal type and free
weights. -/

open IsLocalization Subgroup

attribute [local grind =] mem_star_place star_natCast star_star below_star

attribute [local simp] Function.uncurry mul_assoc starRingEnd_apply

/-- Let E ⊃ ℚ(√−d) be stably unramified, f of odd rank with polynomials P off S, of cuspidal type
at w₀ ∈ S above ℓ, with free jumps at v ∉ S ∪ S̄ over w₀'s split prime u; let w' lie over a split
prime, u if w' ∣ ℓ. Some continuous r has characteristic polynomial ιP_w at most Frobenii,
and `SphericalClause` at w' if w', w̄' ∉ S. -/
lemma exists_rep_of_cuspidal_type {ℓ E a d} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E]
  [EmbeddedNumberField E] [HasQuadSubfield d E] [StablyUnram E] (ha : Odd a) {κ f} (hf :
  f ∈ (stdSpace E (Fin a)).forms κ) {S P} (hP : IsSphericalOff S f P) {w₀ v}
  (hS : w₀ ∈ S) (hu : IsSplitPrimeToDisc (w₀.below _)) {χ} (hty : IsCuspidalType
  (localCongruence _ _ 0) χ) (hχ : ∀ j, rightRegular ℂ _ _ (atSplit hu.star_ne j.1) f =
  χ j • f) (hv : v ∉ S ∧ star v ∉ S ∧ v.below (QuadField d) = w₀.below _)
  {ε : Ω →+* PadicAlgCl ℓ} (hσ : placeOfEmb (ε.comp (algebraMap ..)) = v) {e : Fin a → ℤ}
  (he : FreeInts e) (he' : ∀ i, e i ∈ jumps κ a (.comp ιℓ.symm (ε.comp (algebraMap ..)))) w' (hw' :
  IsSplitPrimeToDisc (w'.below (QuadField d)) ∧ (↑ℓ ∈ w'.1 → w'.below (QuadField d) = w₀.below _)) :
  ∃ r : GalRep ℓ E (Fin a), Continuous r ∧ (∀ᶠ y in mostFrobenii E, (r y.frob).1.charpoly = (P
  y.w).map ιℓ) ∧ (w' ∉ S ∧ star w' ∉ S → SphericalClause r Eq (jumps κ a) w' ((P w').map ιℓ)) := by
  have _ := NeZero.of_pos ha.pos
  have {n : ℕ} (w : FinPlace E) : ↑n ∈ w.1 ↔ ↑n ∈ (w.below (QuadField d)).1 := by simp
  let F := pure v ⊔ Filter.principal {w | w' = w ∧ w' ∉ S ∧ star w' ∉ S}
  refine
    (exists_rep_span_diagonal ((mostFrobenii E).map (·.w) ⊔ F) (jumps κ a) (P · |>.map ιℓ) fun τ₀ ↦
    let s₀ := (ιℓ.symm.toRingHom.comp (ε.comp (algebraMap ..))).comp (algebraMap (QuadField d) E)
    ?_).elim fun b ⟨r, hr, hd, h₁, gv, gc⟩ ↦ ?_
  obtain ⟨⟨ξ, μ, n, A₀, hμ, hξ, hz, hl⟩, Ψ, ⟨hv₀, hΨ⟩, N, h, model⟩ :=
    exists_occursInWeight ha (algebraMap ..) s₀ κ, exists_pel a _ {w₀, w'}
  have ev w := (eventually_notMem_star_notMem d S).and ((tendsto_place_comap_cofinite (algebraMap
    ..)).eventually (eventually_notMem_star_notMem N ((insert w S).image (.below (QuadField d)))))
  obtain ⟨w₁, g₁, ⟨⟨k₁, k₂, -⟩, hw⟩, nt⟩ := ((frequently_prime_q.mono fun _ ↦
    isSplit_of_q_prime).and_eventually ((ev w').and (eventually_isNeat (n := Fin a)))).exists
  let B :=
    insert w₁ {w ∈ S ∪ S.image star | star (w.below (QuadField d)) ∉ [w₀.below _, w'.below _]}
  have cv : ∀ w ∈ insert w₁ S, w ∈ B ∨ star w ∈ B := by clear * - hu hw' this hv hσ; grind
    [IsSplitPrimeToDisc.star_ne_and_prime_norm, natCast_mem_placeOfEmb]
  choose 𝔑 h𝔑 hB hlev using exists_levelGU_conj_le (⟨rightStab f,
    hf.1⟩ ⊓ (.comap _ (Gf.continuous_atPlace w₀) ⟨localCongruence _ _ 0, isOpen_localCongruence⟩ ⊓
    .comap _ (Gf.continuous_atPlace w₁) ⟨_, isOpen_proIwahori⟩) : OpenSubgroup _).2 (fun k h ↦
    ⟨congrFun (hP.2.1 k (h.imp_right (by simp))), by simp [Gf.mem_trivialOn.1 h.2, *]⟩) cv N
  obtain ⟨gv, k₃⟩ : F.Eventually (IsSafe 𝔑) ∧ 𝔑 ∉ (star w₀).1 ∧ 𝔑 ∈ w₁.1 ∧ 𝔑 ∉ (star w₁).1 := by
    simp [F, IsSafe, hB, B]; clear * - hu hv hw' hS h hw g₁ this
    grind -ring -linarith
  have gS w : IsSafe 𝔑 w → 𝔑 ∈ w₀.1 ∧ w ∉ S ∧ star w ∉ S := by clear * - cv hB hS k₃; grind [IsSafe]
  choose t ht ht' using fun w : SafePlace 𝔑 ↦ ((gS _ w.2).2.elim (hP.2.2 _ w.1.2)).2
  have η := nt 𝔑 (by simp [·] at k₃) k₃.2.1
  obtain ⟨⟨D, rfl, rfl, T, V⟩, _, -⟩ := model 𝔑 η.1 h𝔑, trace_definiteForms ξ η 1 1
  have O (u : Gf E D.Index) : IsSignedFrameFor (invTransposeGL u.1) .. :=
    isSignedFrameFor_one (entryConj u)
  let Q (p : _ × Gf ..) : _ ⧸ levelGU D.Index D.𝔑 := ⟦toFinGL p.1 * invTransposeGL p.2.1⟧
  let φ := Q.extend (fun (y, u) ↦ ξ y (f u)) 0
  have hφ o : φ (Q o) = _ := Function.FactorsThrough.extend_apply (fun ⟨z, t⟩ ⟨y, u⟩ e ↦ by
    obtain ⟨⟨y, rfl⟩, e⟩ := mul_left_surjective z y, QuotientGroup.eq.1 e
    have := hf.2 (entryConj ⟨y, ((O u).conj_eq_smul (O t)
      (by simpa [-IsScalarFrame] using levelGU.isScalarFrame_inv_one e)).trans (by simp)⟩) u
    rw [← mul_inv_cancel_left t (_ * u), (hlev _ ?_).1] at this; simp [*]
    simp; erw [stdSpace_embFin]; simpa using! e) ..
  choose L H using fun w hw x ↦ @by_cases (∃ z k p, Q p = ⟦toFinGL z * (x * conjAtSplit w k)⟧)
    (∃ L : _ →ₗ[ℂ] _, ∀ y g, φ ⟦toFinGL y * (x * conjAtSplit w g)⟧ =
    ξ y (L (rightRegular ℂ _ _ (atSplit w.2 g) f))) (fun ⟨z, k, p, e⟩ ↦ by
    rw [QuotientGroup.eq] at e; have := conjAtSplit_dualComponent (w := w) hw e
    generalize dualComponent (n := D.Index) w _ = c at this
    exact ⟨ξ _ ∘ₗ .proj _, fun y g ↦ (congrArg φ (QuotientGroup.eq.2 (by simpa using!
      (inv_mul_eq_of_eq_mul (this.2 (k⁻¹ * g)) ▸ mul_mem (inv_mem this.1) e :)))).symm.trans ((hφ
      (y * (z⁻¹ * _), _ * atSplit w.2 (c * k⁻¹) * _)).trans congr($(map_mul ξ ..) _))⟩)
    (⟨0, by simp [φ, by simpa using ·]⟩)
  let s := @centralScalar E _ _ _ D.Index
  have hc x g : g * s x = s x * g := commute_scalar_GL ..
  have mem : cyclicSpan ((rightRegular ..).comp s) (φ ⟦·⟧) ≤ definiteForms D.𝔑 ξ :=
    Submodule.span_le.2 fun _ ⟨x, e⟩ ↦ e ▸ ⟨⟨fun y z ↦ H ⟨_, hu.star_ne⟩ k₃.1 |>
    fun G ↦ by simpa [← (by simpa using G · 1 1)] using G _ y 1,
      fun z ↦ (dite_eq_right fun ⟨p, e⟩ ↦ · (by
    simpa [s, ratConj] using IsSignedFrame.mul ⟨_, O p.2⟩ p.1 (mul_mem (QuotientGroup.eq.1 e).1
      (inv_mem (centralScalar_mem_GU x).1))))⟩, by simp [funext_iff, hc, ← mul_assoc]⟩
  choose ω ψ hψ' hψ cen using @exists_eigencharacter ℂ _ _ _ _ _ _ (.of_fg (.of_le .of_finite mem))
    _ _ _ apply_mem_cyclicSpan
    (hP.1 <| by ext1; simpa using (hφ (1, _)).symm.trans congr($(· self_mem_cyclicSpan) _))
  obtain ⟨hF, c, h₃⟩ := mem hψ', Finsupp.mem_span_range_iff_exists_finsupp.1 hψ'
  have hω' x h : x ∈ ω.toHomUnits.ker := Units.ext ((smul_left_inj hψ).1 (cen x ▸ hF.2 ⟨_, h⟩ :))
  let L w h := c.sum fun x r ↦ r • LinearMap.pi (L w h <| s x * ·)
  have hL w h g : rightRegular ℂ _ _ (conjAtSplit w g) ψ =
    L w h ((rightRegular ℂ ..).comp (atSplit w.2) g f) := by
    simp [funext_iff, ← h₃, L, Finsupp.sum, ← mul_assoc, hc, (by simpa using H _ h · 1 ·)]
  replace h₃ := (by simpa using hL · · 1 |>.symm)
  obtain ⟨hs, hω⟩ : IsTestVector _ (rightRegular ..) ψ ⟨_, hu.star_ne⟩ ⟨_, g₁⟩ χ ∧ (ω.toHomUnits,
    .ofAdd A₀) ∈ algHeckeChars _ := by refine ⟨⟨⟨hS.ne_of_notMem k₁, k₃⟩, ⟨fun g h ↦ by simpa using
    (hlev _ h).2.1, fun _ ↦ (·.1)⟩, hty, fun _ h ↦ by simpa using (hlev _ h).2.2, hψ, ?_, ?_⟩,
    isOpen_mono (hω' · ⟨(centralScalar_mem_GU _).1,
    mem_comap.1 ·⟩) ((isOpen_congruenceGL_span η.1).preimage (.of_coeHom_comp <| .matrix_diagonal <|
    by simp; fun_prop)), fun x ↦ (smul_left_inj hψ).1 (cen _ ▸ funext fun y ↦ congr(ψ $((hc
    ..).trans ?_)).trans ((hF.1.1 _ y).trans (congr($(hz x) _).trans ?_)))⟩ <;> simp +contextual [s,
    h₃, k₃, ↓hL, Units.ext_iff, ↓hχ, ↓by simpa [mem_sphericalAt_iff g₁] using (hP.2.2 _ g₁ k₁ k₂).1]
  let M := ⨅ w, ⨅ _ : IsSafe D.𝔑 w, w.1.primeCompl
  have hM w : Disjoint M.carrier w.1 ↔ IsSafe D.𝔑 w := by
    have ⟨y, _, e, _⟩ := exists_levelGU_conj_le (n := Unit) isOpen_univ le_top (S := {w}) (fun _ ↦
      .inl) 1
    clear * - e; simp_all [M, Set.disjoint_left, Ideal.one_notMem]; grind
  have z : M ≤ _ := iInf₂_le_of_le v gv.1 v.1.primeCompl_le_nonZeroDivisors
  choose ρ hρ H₁ using (exists_model (nonempty_universalFamily z fun m k ↦ V _ ((hM ⟨_, .comap _,
    (bot_lt_under_prime M (Localization.subalgebra E M z) z m (m.bot_lt_of_maximal
    (Ring.not_isField_of_ne_of_ne (Ideal.map_ne_bot_of_ne_bot v.3)
    ((map_algebraMap_ne_top_iff_disjoint ..).2 ((hM v).2 gv.1)))).ne').ne'⟩).1 ((disjoint_under_iff
    ..).2 k.1.1))).some η T V _).some.exists_galois_rep η M iInf₂_le (fun w ↦
    t w * ((ω (unifNorm w.1))⁻¹ ^ ·))
    (.filter (fun _ ↦ τ₀.comp (algebraMap ..) = s₀) ((jumps κ _ τ₀).map (· + ↑μ))) fun u hu ↦ by
    obtain ⟨⟨u, o, rfl⟩, e⟩ := by simpa using hu
    refine (hl _ e u o).imp_right (· hv₀ hΨ η hs hF fun w j ↦ ?_)
    erw [asAlgebraHom_tau (w, j) hF.2, ← h₃ _ (w.2.2.2 _ (below_star ..)),
      ← map_heckeFun _ (isBiInvariant_basicDoubleCoset
      j).1 fun g ↦ by erw [h₃, hL], ht', map_smul, h₃, map_smul, cen]; simp [smul_smul]
  refine (exists_twist_algHeckeChar (.baseChange ⟨_, hω⟩) μ hρ).imp fun _ ⟨c, H₂⟩ ↦ ⟨c,
    .mono ⟨eventually_mostFrobenii (ev w₁) fun y ⟨a, k⟩ ↦ ?_, gv⟩ fun w g A hA ↦ ?_⟩
  -- modulo a prime of degree one prime to `d`, `QuadField.c₀ d` is an integer multiple of `d`
  have g : IsSplitPrimeToDisc (y.w.below (QuadField d)) := (mem_zmultiples_of_prime_card (hp :=
    ⟨y.prime_q⟩) rfl (Ideal.Quotient.eq_zero_iff_mem.1.mt a.2.2)).elim fun a e ↦ ⟨a * d, by
    simpa using Ideal.Quotient.eq.1 e.symm, 1 - 2 * a * QuadField.sqrtNegDInt d, 2 * a *
    QuadField.sqrtNegDInt d + 1, by clear * -; simp; grind [QuadField.sqrtNegDInt_sq d]⟩
  simp [IsSafe, hB]; clear * - g k this; grind -ring -linarith
  have K s (e : inducedPrime s = w) : s.comp (algebraMap ..) = s₀ :=
    (NumberField.InfinitePlace.mk_eq_iff.1 (by subsingleton)).resolve_right fun h ↦
    g.2.2 _ (by ext; simpa [← hv.2.2, ← e, ← hσ, s₀,
    map_star_CM, -starRingEnd_apply] using (congr(‖ιℓ ($h _)‖ < 1)).symm) (gS w g).1
  refine ht ⟨⟨w, g.1.star_ne⟩, g⟩ ▸ Fintype.card_fin _ ▸ (H₂ w ?_ (fun x r ↦
    hω' _ (mem_levelGU_of_local (centralScalar_mem_GU _).1
    (by simpa [s, mem_intGL, ← map_inv, ite_mem, Matrix.diagonal, star_eq_adeleMap] using!
    (coe_idelesUnitOff_empty.le (locIdele_mem_idelesUnitOff
    r)).imp adeleNorm_mem_Ohat adeleNorm_mem_Ohat) fun v h ↦
    ⟨1, by simpa using! evalAt_centralScalar_of_ne (g.2.2 v · h) x⟩)) (H₁ ⟨⟨w, _⟩,
    g⟩) hA).imp_right (.imp_left (·.congr hA ?_)) <;> simp +contextual [*, AlgHeckeChar.baseChange,
    apply_ite, RingHom.algebraMap_toAlgebra]
  clear * -; grind
  obtain ⟨⟨j, hj⟩, z, q, -⟩ := exists_inducesPlace E Gal(Ω/E) (ι := ε) rfl,
    gv (hσ ▸ isPlaceOver_placeOfEmb ε)
  let := PadicPlaceEmbedding.mk (toOverGp := ⟨_, ⟨hj.2.1.2⟩⟩) _ hj
  choose T k hT hk _ using
    z.2.isPotCrys.exists_isHodgeTateFrame (Pi.basisFun ..) (IsScalarTower.toAlgHom ..)
  obtain ⟨rfl, u⟩ := by simpa using (rank_eq_and_charpoly_eq r hr hd (.mp h₁ <|
    eventually_mostFrobenii (eventually_notMem_star_notMem ℓ S)
    fun y ⟨o, p, l⟩ g ↦ ⟨((g y.isPlaceOver).2.2 _ y.isFrob).1
    (y.isPlaceOver.valuation_natCast_eq_one_iff.2 l), ((hP.2.2 _ (isSplit_of_q_prime
    y.prime_q) o p).isMonicOfDegree hP.1).rec (⟨by simp [·], ·.map _⟩)⟩) T⁻¹ k he (fun n ↦ by simpa
    [List.count_eq_zero] using (hk _ ▸ q (g := 1) (by tauto) _ (by simpa using! he' n) :)) fun F h ↦
    by convert aeval_cocharacter_eq_zero (k ·.1) T⁻¹.1.uncurry F (nhds_one_le_map_nearOne _ (hT.mp
      (nearOne_eq_nhds_one hj.2.1 ▸ .mono (continuousAt_subtype_val h) fun g h f ↦ .trans (by
      congr!; erw [← inv_mul_apply_of_isHodgeTateFrame f]; simp [Matrix.mul_apply]) h)))
       simp)
  use r, hr, u, fun p A h ↦ (gc ⟨rfl, p⟩ h).rec fun u ↦ (⟨u, ·.imp_left fun k o γ τ t x ↦ ?_⟩)
  choose K c d using u.2.isPotCrys.exists_hasJumps γ
  rw [d, Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (κ.nodup_jumps ..)).2
    (by simpa [d _, OccursIn] using! k t ·)) (by simp [c, jumps])]
end

section
/-! Known result: Galois representations attached to forms on definite unitary groups. For the
standard definite form and a CM field with enough roots of unity, Hecke polynomials are l-adically
close to characteristic polynomials at most Frobenius elements and kill Frobenius at spherical split
places. The proof uses l-adic limits, one quadratic descent and theta lifts for even rank, with no
eigenvariety or patching. Source: Chenevier, Harris, Construction of automorphic Galois
representations II, Camb. J. Math. 1 (2013), Thm 3.2.3; with Labesse, Changement de base CM et
séries discrètes (2011), Cor. 5.3, and Barnet-Lamb, Gee, Geraghty, Taylor, Potential automorphy and
change of weight (2014), Thm 2.1.1.

Known result: ℓ-adic avatar of an algebraic Hecke character and its local behaviour. Existence is
given over totally complex fields. For the CM fields used here, the behaviour at places above ℓ is
read from the rank-one case of the Galois representations built in this file
(`sphericalCompat_of_odd`) rather than from Lubin–Tate theory. Source: J.-P. Serre, Abelian ℓ-adic
representations and elliptic curves, 1968, II–III (locally algebraic = Hodge–Tate, Tate's theorem);
B. Conrad, Lifting global representations with local properties, App. B (crystalline case).

This file: Galois representations for all eigenforms of odd rank, by l-adic limits of seeds. Descent
of the Galois representation along quadratic steps, replacing the patching lemma. Local-global
compatibility of l-adic avatars of algebraic Hecke characters at all finite places. -/

open Matrix Polynomial Filter Finset Metric Nat Gf NumberField Ideal Subgroup Module.End

attribute [local simp] offPartComap

/-- The statement `SphericalCompat` on Galois representations attached to eigenforms holds at u
in odd rank a, for stably unramified CM fields E ⊃ ℚ(√−D), D ≡ 3 mod 4, if u and all places
above ℓ lie over split primes of ℚ(√−D) (`IsSplitPrimeToDisc`). -/
lemma sphericalCompat_of_split {ℓ E a D} [ThePrime ℓ] [PadicIso ℓ] [Field E] [CMType E]
  [EmbeddedNumberField E] [StablyUnram E] (ha : Odd a) [HasQuadSubfield D E] {u} (sp : ∀ v,
  ↑ℓ ∈ v.1 ∨ v = u → IsSplitPrimeToDisc (v.below (QuadField D))) :
  SphericalCompat E (Fin a) a u := fun P κ f hf he ↦ by
  have ⟨z, l, _⟩ : ∃ z, ↑ℓ ∈ z.1 ∧ (↑ℓ ∈ u.1 → u = z) := by grind [FinPlace.exists_natCast_mem E ℓ]
  have A a := ((sp z (.inl l)).exists_place_above_ne a u).imp fun x h ↦ (exists_comap_intQpBar_eq
    (p := ℓ) (x.isPlaceOver_placeOver.valuation_natCast_lt_one_iff.2
    (by simpa [l] using congr(↑ℓ ∈ $(h.1).1)))).imp fun e H ↦ (H ▸ isPlaceOver_placeOfEmb e).unique
    x.isPlaceOver_placeOver |> fun k ↦ (fun {θ} (o : InducesPlacePair x θ) ↦ (⟨h, k, o, by
    grind [star_star, InducesPlacePair]⟩ : ∃ _ _ _, IsSplitPrimeToDisc (x.below (QuadField D)) ∧
    ¬InducesPlacePair u θ)) (inducesPlacePair_mk _ (.comp ιℓ.symm
    (e.comp (algebraMap ..))) (by aesop))
  obtain ⟨_, v, _, B, -, o', l, n'⟩ := NeZero.of_pos ha.pos, A u
  obtain ⟨⟨x, θ, C, hθ, o, n₂, n⟩, ⟨ϑ, ty, c⟩, g, i, F⟩ := A v, exists_isCuspidalType v a,
    by simpa [funext_iff] using he.1
  let V := offPartComap n₂.star_ne ⟨_, hf.1⟩
  have ⟨S, h, h₂⟩ := exists_inf_trivialOn_le V.2
  let K := .comap _ (continuous_atPlace v) ⟨localCongruence _ v 0,
    isOpen_localCongruence⟩ ⊓ offPartComap l.star_ne V ⊓ ⟨_, isOpen_Kf⟩
  let χ : K.1 →* _ := ϑ.comp (.mk' (⟨_, ·.2.1.1⟩) (by simp [Subtype.ext_iff]))
  obtain ⟨⟨s, t, N, H, y, m⟩, O, L, _, _⟩ := isApproximatingMonoid_of_mem_closure (S :=
    {F | ∃ r Q μ M g w q k J, _}) (fun h ↦ F (by simpa [padicModel, ← map_mul, ← Pi.zero_def] using
    congr((weylRep _ κ.2 (padicComponents g) *ᵥ ($h ⟨g, ·⟩)) i))) (padicModel_mem_uniformClosure _
    ⟨by aesop, K.2⟩ (.mono (isOpen_localCongruence.preimage_of_continuous.mem_nhds (by simp))
    fun _ ↦ c _) {v | ¬_} ⟨_, hf⟩ (fun d h ↦ by simpa [V, χ, o.atPlace_eq_one, o'.atPlace_eq_one, *]
    using d.2.1.2) fun μ _ g j q M N ↦ Submodule.mapsTo_span (f := (padicModel ..).domRestrict _)
    (fun g i ↦ forall_eq'.1 fun F w ↦ i.2.rec fun P e ↦ (exists_rep_of_cuspidal_type ha g.2
    e (S.mem_insert_self v) l ty (fun j ↦ congr($(i.1 ⟨_, by simpa [K] using! j.2.1⟩).1).trans (by
    simp [χ])) ((h x (inf_le_of_right_le (by simp [V, LE.le, ← range_atSplit n₂.star_ne]))).rec (by
    clear * - B C; grind)) hθ (fun d h _ a _ b e ↦ q _ n d h a b (by simp [Finsupp.weight_eq_sum,
    Finsupp.degree_eq_sum, mul_sub, mul_add, ← sum_mul, ← cast_sum] at *; grind only))
    (List.mem_map_of_mem <| mem_range.2 ·.2) u (by simp +contextual [*])).rec (⟨·, P, μ, M, g, w, e,
    N, j, ·⟩)) (have := (stdSpace ..).finite_formTranslation_levelSpace μ K.2 χ
    (fun _ o ⟨k, a, b⟩ ↦ by simp at b; simp [χ, *, o ⟨k, by simpa [b] using h₂ ⟨a, mem_trivialOn.2
      b.2⟩, a⟩]) |> fun J ↦ le_span_isSphericalOff (levelSpace _ _ χ) J (fun _ _ a b _ _ h ↦
      heckeSplit_mem_levelSpace _ _ (levelSpace_le_sphericalAt a b (J h)) inf_le_right h) g)),
    eventually_mostFrobenii (.and (eventually_notMem_star_notMem ℓ
    (insert v S)) he.2) fun y ↦ And.imp_right (· y.prime_q), exists_padic_field_of_form_values hf
  choose r Q μ M g w q k J hr hU hw using (y · |>.2)
  choose b hb c T using exists_padicModel_hecke_contraction κ
  choose! d m using fun x h X j o o' (l : _ → x = u) e ↦ CanLift.prf (β := N) _ (m (_, _)
    ((T x h j).imp fun _ ↦ .imp_right fun T ↦ ⟨T 1 X e (by simp [← map_mul]), fun i ↦ w i ▸ T _ _
    ((q i).2.2 _ _ o o') fun _ ↦ k i _ fun _ h ↦ padicComponents_atSplit _ _ _ (l · ▸ h)⟩))
  exact (exists_trace_limit H (mostFrobeniiAt E · |>.map fun y ↦ d y.w (P y.w) (a - 1))
    L.toSubmodule.complete_of_finiteDimensional (fun _ ↦ mem_inf_of_left (O.mono fun _ ⟨_, _, e⟩ ↦
    by simp [*]; have ⟨c, _, _, t⟩ := e
       simp (maxDischargeDepth := 3) [*, eq_div_of_mul_eq F congr($(t _) _ _).symm, mul_mem,
         heckeSplit, heckeGL_eq_sum ((mem_sphericalAt_iff _).1 c), div_mem,
         _root_.sum_mem, -Int.cast_mul])) hr fun g i ↦ tendsto_map' ((tendsto_mostFrobeniiAt (r
    i · |>.1.trace)).congr' (mem_inf_of_left ((hU i).mp (O.mono (by simp +contextual [*,
    trace_eq_neg_charpoly_coeff])))))).rec fun R ⟨hR, hN, hT⟩ ↦ ⟨hR, hN, .id, fun η k ↦
    ((Iic a).eventually_all.2 fun i _ ↦ tendstoUniformly_iff.1 ((H.tendstoUniformly_eval (.C
    ((-1) ^ (a - i) / (a - i)!) * newtonPoly (a - i) 1) (⟨_, hT <| FrobeniusDatum.frob · ^ ·⟩)).add
    (H.2.comp fun z ↦ d z.w (P z.w) i)) η k).exists.rec fun ε h ↦ .mono (.and (.all (hU ⟨ε,
    ·⟩)) O) fun z ⟨p, o, n, e⟩ ↦ forall_eq.2 fun i ↦ (le_or_gt i a).rec (fun l ↦ by
    simpa [l, o, c, m, n, e, ← by simpa using (ext_iff.1 <| p ·), sub_eq_add_neg, eval_newtonPoly,
      trace_pow_eq_sum_roots, charpoly_monic, coeff_eq_esymm_roots_of_splits, IsAlgClosed.splits,
      ← mul_assoc] using (h i (by simpa) z).le) (fun _ ↦ by
    simp [*, k.le, coeff_eq_zero_of_natDegree_lt,
    (e.isMonicOfDegree he.1).1])⟩ |> fun e ↦ ⟨⟨R, e⟩, fun _ c k A hA ↦ And.elim (fun e M ↦ by
    choose g j p using (hw ⟨·, ·⟩ M hA)
    replace j η i := (j η i).congr (J' :=
      jumps κ a) hA fun _ _ ↦ by simp [*, jumps, inducesPlacePair_mk]
    exact (local_clauses_of_trace_limit c.1 c.2.1 _ _ _ _ (⟨r ⟨·, ·⟩⟩) (hr ⟨·, ·⟩) g j (.inr j) (by
    simpa [e] using! H.2.comp (⟨_, hT ·⟩)) fun _ _ _ _ h ↦ cast_inj.1 ∘ tendsto_nhds_unique
    (by simpa [← h, sum_mul] using (H.2.tendsto_at 1).mul_const _)).imp_right (.imp_right
    fun Y k Q hQ s hs ↦ Y .refl (⟨by simp [(hQ.isMonicOfDegree he.1).1, (((q _).2.2 _ k M.1
      M.2).isMonicOfDegree (q _).1).1], p · · s hs⟩) fun j ↦ by simpa [mul_assoc, *] using
      (H.tendstoUniformly_eval ((b u k j)⁻¹ • .X 0 * .X 1) (![d u Q j, ⟨_, hT ·⟩])))) ⟨c.trace_eq e,
    (h u fun g b ↦ by simpa [V, mem_supportedOn.1 b.2 x, C, funext_iff] using k ⟨g,
    b⟩).elim (by clear * - B; aesop)⟩⟩

/-- Odd rank, by descent along one quadratic step (no patching). The representation
of step `0` is conjugate to that of each later step where both are defined; it is extended by `1`
on the elements `K` that all later steps kill, and inertia groups lie in `K`.

Known result: Galois representations attached to forms on definite unitary groups. -/
lemma sphericalCompat_of_odd {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E]
  [CMType E]
  [StablyUnram E] {a} (ha : Odd a) w : SphericalCompat E (Fin a) a w := fun P κ f hf he ↦ by
  choose S _ hS using exists_inf_trivialOn_le hf.1
  let n T := ℓ * (T + w.q + S.sup FinPlace.q).factorial
  choose χ _ _ hμ G H L using fun {T} ↦ exists_quadratic_step E (n T) NeZero.out
  have hp {T} {v : FinPlace E} (h := by omega) : ↑(n T) ∈ v.1 :=
    mem_of_dvd _ ((Nat.dvd_factorial v.one_lt_q.le h).mul_left ℓ).natCast (absNorm_mem _)
  choose F _ Z hs _ using fun {T} ↦
    exists_isWeakBaseChange_of_matching (hμ := @hμ T) ⟨_, hf⟩ isLocalMatching_empty ![] 0 _ rfl (by
    simp) nofun fun _ a _ ↦ trace_restrict_ne_zero one_ne_zero (he.1 congr($(·.le ⟨by simp, a⟩)))
    fun _ _ ↦ eigenspace_le_maxGenEigenspace (by simp [heckeFun, @Fintype.card_unique _ (.mk' _)])
  choose _ e hu _ hr using fun {T x A} a m ↦ (IsPlaceOver.exists_above a).imp fun u e ↦
    And.intro e.2 ((sphericalCompat_of_split ha
    (H · <| ·.elim (mem_of_dvd _ (by simp [n])) (by simpa [·, ← e.2] using m)) (@F
    T).2 Z).symm.imp_left fun H {r} c ↦ (@H r c · A e.1) ∘ (hs.2 x nofun u e.2).1 fun v e ↦
    ⟨hμ.exists_gal_ne_one.imp (notMem_inertia_of_comap_ne ∘ (a.split_completely (L a m).1 v e).2 ·),
    fun y c ↦ by simp [localNorm, ideleAt, ((e ▸ a).artinAt_units_trivial_iff_unramified _).2 fun _
    h ↦ ((L a m).2.1 h).2, v_adeleNorm_eq_one, locIdele_mem_idelesUnitOff c]⟩)
  choose ho hR ρ hρ hs' using
    (@hs · |>.exists_attached_descent (hr w.isPlaceOver_placeOver hp) Z he)
  obtain ⟨⟨m, G⟩, ⟨C, d, o, -⟩, z⟩ := @G 0, hρ 0, (mt <| @hp 0 · ∘ _root_.le_add_left ∘ S.le_sup)
  let K := (⨅ T, (ρ (T + m)).ker.map (Subgroup.subtype _)).normalCore
  choose Q c using fun T ↦ (d.comp (inclusion inf_le_left)).exists_conj_of_trace_eq _ (.id ..)
    ((hρ (T + m)).2.1.comp (inclusion inf_le_right)).hasSemiprimeSpan fun _ ↦
    (hρ 0).trace_eq (hρ _) _ rfl
  have k {T} g h (a : h ∈ K) p : ρ 0 ⟨g.1 * h, p⟩ = Q T * ρ (T + m) g * (Q T)⁻¹ := by
    obtain ⟨y, e, rfl⟩ := Subgroup.mem_iInf.1 (normalCore_le _ a) T
    rw [← mul_one (ρ _ g), ← e, ← map_mul]
    exact eq_mul_inv_of_mul_eq (Units.ext (c _ ⟨_, p, (_ * y).2⟩))
  choose y Y s using G K fun s ⟨x, ⟨p, _⟩, A, a, i⟩ c ↦ Subgroup.mem_iInf.2 fun T ↦ ⟨⟨_,
    (L (a.smul c) hp).2.1 (i.conj c)⟩, hs' .. ▸ (hu (a.smul c) hp (hr ..) (levelSpace_le_sphericalAt
    (z _ p) (z _ (by simpa)) (by simpa [LE.le, funext_iff] using hS))).1.1
    ((a.smul c).valuation_natCast_eq_one_iff.2 (p ∘ mem_of_dvd _ (by simp [n]))) _ (i.conj c), rfl⟩
  have u {x z} (p : (z.1 : _ ⧸ K) = x.1 := by simp [Y]) : ρ 0 x = ρ 0 z :=
    (ρ 0).eq_iff.2 ((@k 0 1 _ (QuotientGroup.eq.1 p) _).trans (by simp))
  exact ⟨⟨.mk' (ρ 0 ⟨_, s ·⟩) fun _ _ ↦ .trans u (map_mul ..), continuous_of_continuousAt_one _
    fun _ h ↦ o.nhds_le 1 ((C.congr fun _ ↦ u).tendsto 1 h), fun x m t ↦ d x (Submodule.span_mono
    (by simp) m) (t · ▸ congr((x * $u).trace)), .id, fun η e V O n ↦
    (chebotarev O n he.2).elim fun y ⟨_, p, _, a, _, v, f, _⟩ ↦ ((hρ (y.q + m)).2.2.2 η e _ (O.inter
    (ho (y.q + m))) ⟨_, v, (L a hp).2.2 (isSplit_of_q_prime p) f.1⟩).imp fun O ⟨a, b⟩ ↦ ⟨fun _ h ↦
    (a h).1, by peel b; simpa [k ⟨_, (a ‹_›).2⟩, Y] using this _ rfl⟩⟩, fun _ R f A a ↦
    match hR 0 R A, L a hp with | ⟨i, j, y⟩, ⟨U, g, D⟩ => (hu a hp (hr ..) f).imp (isGoodAt_iff.2 <|
    isGoodAt_iff.1 · |>.imp i fun x s h ↦ (y ⟨s, g h⟩).2 _ (x _ h)) (.imp (j _) fun x hw P d s h ↦
    (y ⟨s, inv_mem (D hw h.1)⟩).2 _
    (x _ P ((hs.2 w nofun _ (e ..)).2 ⟨by simp [(a.artinAt_trivial_iff_decompGroup_le _).2 fun _ h ↦
    (D hw h).2], a.split_completely U⟩ _ _ d).2 _ ((a.split_completely U _ (e ..)).1 ▸ h)))⟩

/-- For a stably unramified CM field E, the ℓ-adic avatar μ of an algebraic character θ of type
n satisfies the local clauses `AvatarCompatAt` (finite type, jumps, killing polynomials in
degrees 0 and 1) at every place A above every finite place w.

Known result: ℓ-adic avatar of an algebraic Hecke character and its local behaviour. -/
lemma avatarCompatAt_of_stablyUnram {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E]
  [EmbeddedNumberField E] {w : FinPlace E}
  [NumberField.IsCMField E] [StablyUnram E] θ : AvatarCompatAt w θ := fun A hA ↦ by
  wlog hw : w.IsSplit generalizing E
  · choose χ _ _ _ _ S H using exists_quadratic_step E _ w.one_lt_q.ne_bot
    let j : Gal(Ω/QZChar.stepField χ) →* _ := AlgEquiv.restrictScalarsHom E
    obtain ⟨a, c, u, hu, rfl⟩ := (H hA w.1.absNorm_mem).1,
      isOpenEmbedding_galois_restrict j (by tauto), hA.exists_above (L := QZChar.stepField χ)
    have k := (hA.split_completely a u rfl).1
    refine have T :=
        local_clauses_of_retract 1 _ (by simp) (by tauto) c Filter.univ_mem ?_ (one_mul 1)
      (this θ.baseChange hu (S u (k ▸ u.1.absNorm_mem)).star_ne).imp T.1 (.imp (T.2.1 (by simp))
        fun c s m l t ↦ (c (.ofRingEquiv (·.2 ⟨_, a (inv_mem t.1)⟩)) m l (by rwa [k])).elim fun y
        ⟨o, e, p⟩ ↦ ⟨_, by simp [v_localNorm (f := 1), *], (hu.localArtin_adeleNorm j).1 e,
      by simpa [← adeleNorm_locIdele] using! T.2.2 _ ⟨⟩ p⟩)
    simp; refine (dense_of_mostFrobenii (eventually_mostFrobenii
      (eventually_notMem_star_notMem ℓ {u}) fun y l ↦ (y.isPlaceOver.exists_localArtin_eq
      y.isFrob 1).elim fun z e ↦ ?_)).induction (fun _ ↦ id) (by apply isClosed_eq <;> fun_prop)
    erw [AlgHeckeChar.avatar_localArtin _ y.isPlaceOver (.inl l.2.2) e.2, θ.1.1.comp_apply,
      adeleNorm_locIdele, θ.avatar_localArtin y.isPlaceOver.isPlaceOver_below _
      ((y.isPlaceOver.localArtin_adeleNorm j).1 e.2)]; simp [l]
  have : CMType E := {}
  let ⟨v, o⟩ := (((Northcott.finite_le (h := FinPlace.q) (2 ^ Module.finrank ℚ E)).insert w).insert
    (star w)).exists_notMem
  let k s := ite (inducedPrime s = w) (θ.1.2.toAdd s) (-θ.1.2.toAdd (star s))
  have e : levelSpace ((stdSpace E (Fin 1)).formTranslation (0, k ∘ Φ)) _ ≃ₗ[ℂ] _ :=
    freeLevelEquiv _ _ _ (classAut_eq_bot (w := ![v]) (by simp [·.ext_iff]) (by aesop) le_rfl)
  obtain ⟨f, ⟨-, P, hP⟩, -⟩ := have := e.symm.finiteDimensional; not_forall₂.1
    (Submodule.nontrivial_iff_ne_bot.1 e.nontrivial <| eq_bot_mono (levelSpace_anti
      (.trans (by simp) inf_trivialOn_le_levelOf) |> (le_span_isSphericalOff (S := {v}) _ · (by
    intros; apply_rules [heckeSplit_mem_levelSpace, levelSpace_le_sphericalAt, levelOf_le_Kf]))) <|
      Submodule.span_eq_bot.2 ·)
  have he : IsEigenform _ P := ⟨hP.1,
    (eventually_notMem_star_notMem 1 {v}).mono (by grind [IsSphericalOff, isSplit_of_q_prime])⟩
  obtain ⟨hP, ⟨r, hr⟩, hS⟩ := hP.2.2 w hw (by aesop) (by aesop),
    sphericalCompat_of_odd odd_one w f.2 he
  obtain ⟨⟨t, e⟩, ⟨a₁, b₁, c₁⟩, θ₁, h₁, H, D⟩ := by simpa [Polynomial.isMonicOfDegree_one_iff] using
    (hP.isMonicOfDegree he.1), (hS hr hP.1 A hA).imp_left isGoodAt_iff.1,
    hr.exists_det_eq_avatar f.2 he
  refine (local_clauses_twist A (by simp [← Matrix.ext_iff, by simpa using D])).elim fun T U ↦
    (avatarCompatAt_of_type_eq_zero (θ / θ₁) (fun σ h ↦ ?_) hA).imp (T a₁.1) (.imp (by
    convert U.2.1 b₁ ·; simp [jumps, Multiset.range, *]; lia) fun c ↦ ?_)
  simp [h₁]; grind [Φ_eq_or σ, congr(inducedPrime $(NumberField.IsCMField.isConj_complexConj E
    _)).trans (placeOfEmb_comp_star (ιℓ.toRingHom.comp _))]
  peel c with s m hm hs x v _ k
  refine U.2.2 (.of_dvd ?_ (Polynomial.dvd_iff_isRoot (a :=
    ιℓ (θ₁.1.1 (locIdele w x))).2 (by simp))) k
  interval_cases m
  simpa [(H w hw x).1 v (hP.1 ⟨_, by simp [mem_intGL, mem_LocInt, v]⟩)] using a₁.2 _ (inv_mem hs)
  simpa [(H ..).2 v hP, e] using c₁ _ _ hP _ (pow_one w.q ▸ hs)
end
