import Lib.Adelic.CongruenceLevel
import Lib.GaloisRep.HeckeOperatorOfFunction

section
/-! General lemmas of group theory (textbook or folklore).

This file: Cyclic subrepresentation of a vector; subrepresentation of smooth vectors. -/

variable {G V} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The subspace V_y spanned by the translates ρ(g)y of the vector y. -/
abbrev cyclicSpan y := Submodule.span ℂ (.range (ρ · y))

lemma self_mem_cyclicSpan {ρ : Representation ℂ G V} {y} : y ∈ cyclicSpan ρ y :=
  Submodule.subset_span ⟨1, by simp⟩

lemma apply_mem_cyclicSpan {ρ : Representation ℂ G V} {y} g : ∀ x ∈ cyclicSpan ρ y,
  ρ g x ∈ cyclicSpan ρ y := Submodule.mapsTo_span fun _ ⟨h, _⟩ ↦ ⟨g * h, by simp [*]⟩

lemma compactMean_mem_cyclicSpan {ρ : Representation ℂ G V} {y} {K : Subgroup G} [TopologicalSpace
  G] [IsTopologicalGroup G] [IsSmoothRep ρ] [CompactSpace K] g {x} (h : x ∈ cyclicSpan ρ y) :
  compactMean ρ K (ρ g x) ∈ cyclicSpan ρ y :=
  (Submodule.ker_mkQ _).le (map_compactMean_of_const _ (by simp_all [apply_mem_cyclicSpan]))

/-- The subrepresentation of ρ on its smooth vectors, those fixed by all g in some neighbourhood
of 1. -/
def smoothVectorRep [TopologicalSpace G] [IsTopologicalGroup G] := ρ.subrepresentation ⟨⟨⟨{x | ∀ᶠ
  g in _, ρ g x = x}, (·.mp <| ·.mono (by grind))⟩, by simp⟩, fun _ _ ↦ (·.mono (by simp_all))⟩
  fun a _ _ ↦ .mono ((continuous_const_mul a⁻¹).mul_const a |>.tendsto 1 (by simpa)) (by simp)

instance [TopologicalSpace G] [IsTopologicalGroup G] : IsSmoothRep (smoothVectorRep ρ) :=
  ⟨(·.2.mono (by aesop))⟩
end

section
/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Elements of I t I, t strictly dominant, are twisted-conjugate into the torus. -/

open Matrix WithZero Valued GeneralLinearGroup DoubleCoset Filter


attribute [local simp] zero_lt_iff mul_assoc zpow_ne_zero _root_.zpow_add mem_proIwahori
attribute [local simp ←] map_zpow
variable {F F' N} [Field F] [Valued F ℤᵐ⁰] [Field F'] [Valued F' ℤᵐ⁰]
  {g : GL (Fin N) F} {t : Fin N → Fˣ} (ht : StrictMono (v <| t · |>.1))

/-- The double coset I₁ diag(t) I₁ in GL_n(F), where I₁ = `proIwahori` is the pro-p Iwahori subgroup
and t a family of nonzero elements of F. -/
abbrev iwahoriDoubleCoset (t : Fin N → Fˣ) :=
  doubleCoset (diagGL t) (SetLike.coe proIwahori) (SetLike.coe proIwahori)

lemma diagGL_mem_proIwahori : diagGL t ∈ proIwahori ↔ ∀ i, v ((t i).1 - 1) < 1 := by
  simp [diagonal]; grind [v.map_eq_of_sub_lt, one_pos]

lemma map_mem_proIwahori_iff_of_isEquiv {ι : F →+* F'} (h : (v.comap ι).IsEquiv v) :
  g.map ι ∈ proIwahori ↔ g ∈ proIwahori := by simp [← h.le_one_iff_le_one, ← h.lt_one_iff_lt_one]

include ht

lemma eventually_v_mul_pow_le_one (a : _ → _ → F) : ∀ᶠ k in atTop, ∀ i j, i < j →
    v (t i ^ k / t j ^ k * a i j) ≤ 1 := by
  simp_rw [eventually_all, ← div_pow]
  exact fun i j h ↦ (tendsto_zero_pow_of_v_lt_one (by simp [ht h, field])).mul_const _
    ((isOpen_integer F).mem_nhds (by simp))

lemma eventually_pow_mul_mem_dominantTorus s : ∀ᶠ k in atTop, t ^ k * s ∈ dominantTorus :=
  (eventually_v_mul_pow_le_one ht
  (s · / s ·)).mono (by simp [dominantTorus, monotone_iff_forall_lt, field])

/-- Let σ be a continuous isometric endomorphism of the local field F, surjective on GL_n(F),
and t diagonal with strictly increasing absolute values. Every g in I₁tI₁ (I₁ the pro-p
Iwahori subgroup) satisfies k⁻¹gσ(k) = td with k, d in I₁, d diagonal. -/
lemma exists_twisted_conj_diag [CompactSpace 𝒪[F]]
    (σ : F →+* F) (hσ : ∀ x, v (σ x) = v x) (cont : Continuous σ) (sur :
  (⇑(map (n := Fin N) σ)).Surjective) (hg : g ∈ iwahoriDoubleCoset t) : ∃ k ∈ proIwahori, ∃ d,
  diagGL d ∈ proIwahori ∧ k⁻¹ * g * k.map σ = diagGL (t * d) := by
  let H (j : ℤ) := (MulAut.conj (diagGL t) ^ j).comapSubgroup proIwahori
  let X (k : proIwahori) := (diagGL t)⁻¹ * (k.1⁻¹ * g * .map σ k)
  have L {j g} : g.map σ ∈ H j ↔ g ∈ H j := by
    simp [H, ← map_inv, ← hσ (g _ _ - 1), mul_left_comm (_ ^ j), *]
  choose f h using (Nat.rec (Nat.rec (let ⟨k, p, _, q, e⟩ := mem_doubleCoset.1 hg
    ⟨⟨k, p⟩, by simp [X, (H 0).mul_mem q (L.2 p), *]⟩) fun y ⟨k, hc⟩ ↦
    (exists_unipotent_conj_mem_proIwahori ht.monotone (hc 0)).rec fun u ⟨hu,
    _⟩ ↦ let ⟨z, hp⟩ := sur (u⁻¹ * X k)
    have U (j : ℕ) : u ∈ H j := by simpa [H, ← map_pow] using
      conj_unitriangular_mem_proIwahori (pow_mem ht.monotone j) hu
    have B (j : ℕ) (h : j ≤ y.succ := by grind) : z ∈ H (j + -1) :=
      by cases j; rwa [← L, hp]; grind [mul_mem, inv_mem]
    ⟨k * ⟨_, B 1⟩⁻¹, fun j a ↦ by lift j to ℕ using a.1; simpa [X, H, *] using
      (proIwahori.mul_mem (B j) (U j))⟩) fun _ h y ↦ let ⟨k, hc⟩ := h y.succ
    ⟨k * ⟨_, hc 1⟩, fun j a ↦ by simpa [X] using (@L _ (⟨_, hc 1⟩ : proIwahori)).2 (by simpa [H]
      using (hc (j + 1)))⟩ : ∀ x y : ℕ, ∃ k, ∀ j (_ : j ∈ Set.Icc (-↑x) ↑y := by grind), X k ∈ H j)
  have ⟨k, K⟩ := exists_clusterPt_of_compactSpace (atTop.map (diag f))
  have K j : k ∈ X ⁻¹' H j := ((proIwahori.isClosed_of_isOpen isOpen_proIwahori).preimage
    (by simp; fun_prop)).mem_of_mapClusterPt K (.mono (mem_atTop j.natAbs) fun _ _ ↦ h ..)
  use k, k.2, (.mk0 _ <| v.pos_iff.1 <| v_diag_eq_one_of_mem_proIwahori (K 0) · ▸ one_pos),
    diagGL_mem_proIwahori.2 (K 0).2.2,
    map_mul diagGL t _ ▸ eq_mul_of_inv_mul_eq (Units.ext (IsDiag.diagonal_diag fun i j h ↦ by_contra
    fun e : X k i j ≠ 0 ↦ have A m := (by simpa [← map_inv, ← log_le_log, e] using
      (mem_proIwahori.1 (K (m - m * (v (X k i j)).log))).1 i j)
    by cases h.lt_or_gt <;> nlinarith [A 1, A (-1), by simpa [← log_lt_log] using ht ‹_›]).symm)
end

section
/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: Conjugation of parahorics by monomial matrices; quadratic relation of the Iwahori Hecke
algebra. Some strictly dominant U-operator is injective; values of exponents on monomial
translates. -/

open Finset Equiv Fint Function IsLocalRing Matrix OrderDual Units Valued WithZero

attribute [local simp] Pi.mulSingle_apply transvectionGL_mem_proIwahori

variable {F W} [Field F] [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] [AddCommGroup W] [Module ℂ W] {N} {ρ :
  Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] {x c d} {g : GL (Fin N) F} {a b : Fin N} {φ : ρ →ₗ[ℂ] W}
  (h : a ⋖ b) {h' : a ≠ b} {ϖ : Fˣ} (hϖ : v ϖ.1 = exp (-1)) {y z ξ l t K} (hl : IsExponent ρ ξ l)

omit [CompactSpace 𝒪[F]] in
@[grind] lemma mem_blockParahoric {c : ℕ → ℕ} : g ∈ blockParahoric c ↔ g ∈ intGL _ 𝒪[F] ∧
  ∀ i j, c j.1 < c i.1 → v (g i j) < 1 := .rfl

omit [CompactSpace 𝒪[F]] in
lemma mem_proIwahori_iff_blockParahoric : g ∈ proIwahori ↔ g ∈ blockParahoric id ∧ ∀ i,
  g i i ∈ {x | v (x - 1) < 1} := and_assoc.symm

omit [CompactSpace 𝒪[F]] in
/-- Let g lie in the parahoric of d, with diagonal entries in S, and h = σ·diag(t). If g_{σa,σb}
≠ 0 implies log|t_b| + [c(b)<c(a)] ≤ log|t_a| + [d(σb)<d(σa)] (integer logarithms), then
h⁻¹gh lies in the parahoric of c, with diagonal entries in S. -/
lemma conj_monomial_mem_blockParahoric {c d : ℕ → ℕ} t (σ : Equiv.Perm (Fin N)) (S : Set F) (hk :
  g ∈ blockParahoric d ∧ ∀ i, g i i ∈ S) (h : ∀ a b, g (σ a) (σ b) = 0 ∨
  log (v (t b).1) + ite (c b < c a) 1 0 ≤ log (v (t a).1) + ite (d (σ b) < d (σ a)) 1 0) : let k :=
    (permGL σ * diagGL t)⁻¹ * g * (permGL σ * diagGL t); k ∈ blockParahoric c ∧ ∀ i, k i i ∈ S := by
  simp_all only [mem_blockParahoric, mem_intGL_iff_det]; erw [det_units_conj']
  simp [← map_inv, mul_apply, symm_apply_eq, diagonal, mul_assoc]; grind [ne_zero, one_pos,
    =_ log_le_log, =_ log_lt_log, map_eq_zero, log_mul, log_inv, mul_eq_zero]

omit [CompactSpace 𝒪[F]] [IsSmoothRep ρ.ρ] in
lemma transvectionGL_apply_permGL_inv {σ} {x : ρ} (hx : x ∈ levelSpace ρ.ρ proIwahori) (e :
  σ a < σ b) c (hc : v c ≤ 1) : ρ (transvectionGL h' c) (ρ (permGL σ⁻¹) x) = ρ (permGL σ⁻¹) x :=
  cast (by simp_all) congr(ρ $(permGL_mul_transvectionGL σ⁻¹ e.ne c) x).symm

omit [CompactSpace 𝒪[F]] in
lemma proIwahori_le_blockParahoric {c : ℕ → ℕ} (h : ∀ i j, c j < c i → j < i := by grind) :
    proIwahori ≤ @blockParahoric F _ _ N c := fun _ ↦ by grind [mem_proIwahori_iff_blockParahoric]

omit [Valued F ℤᵐ⁰] [CompactSpace 𝒪[F]] in
@[local simp] lemma swap_mul_transvectionGL (h : a ≠ b) (u : Fˣ) : permGL (swap a b) *
  transvectionGL h u.1 = transvectionGL h u.1⁻¹ * diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b
  u) * transvectionGL h.symm u.1⁻¹ := by ext; simp [PEquiv.toMatrix_mul_apply, transvection,
  mul_add, add_mul, single_apply, diagonal_apply, @apply_ite Fˣ]; grind

omit [CompactSpace 𝒪[F]] in
lemma exists_swap_conj_mem_proIwahori (hg : g ∈ proIwahori) : ∃ c : 𝒪[F],
  MulAut.conj (permGL (swap a b)) (g * transvectionGL h.ne c.1) ∈ proIwahori :=
  have : v (-g a b / g a a) ≤ 1 := by simp_all [v_diag_eq_one_of_mem_proIwahori, mem_proIwahori]
  ⟨⟨_, this⟩, by cases h; simpa using!
    mem_proIwahori_iff_blockParahoric.2 (conj_monomial_mem_blockParahoric 1 (swap a b) _
    (mem_proIwahori_iff_blockParahoric.1 (by aesop))
    (by simp; grind [mul_transvection_apply_same, v_diag_eq_one_of_mem_proIwahori, one_pos]))⟩

/-- Quadratic relation: b = a+1, s the transposition (a b), φ invariant under I₁, 1 + 𝒪E_{ba}
fixing y, φ(ρ(d)y) = c for d with −u⁻¹ at a, u at b, 1 elsewhere, u any unit. Then qφ(s·mean
of y over I₁) = φ(sy) + (q−1)c. -/
lemma quadratic_relation c (hφ : ∀ k ∈ proIwahori, ∀ z, φ (ρ k z) = φ z) (hx : ∀ c, v c ≤ 1 →
  ρ (transvectionGL h.ne' c) x = x)
  (hc : ∀ u, v u.1 = 1 → letI t := Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u
  (∀ i, v (t i).1 = 1) → φ (ρ (diagGL t) x) = c) : letI s := ρ (permGL (swap a b))
  Nat.card 𝓀[F] • φ (s (compactMean ρ.ρ proIwahori x)) = φ (s x) + (.card 𝓀[F] - 1) • c := by
  have A (k : proIwahori) {w} (o : v w ≤ 1) : φ (ρ (k.1 * (permGL (swap a b) * transvectionGL h.ne
    w)) x) = ite (v w < 1) (φ (ρ (permGL (swap a b)) x)) c := by
    cases h; cases o.lt_or_eq
    simp_all [permGL_mul_transvectionGL]
    lift w to Fˣ <;> aesop
  simpa [h.1, ← v.mem_integer_iff] using (map_compactMean_of_const (φ ∘ₗ _) fun _ k ↦
    (exists_swap_conj_mem_proIwahori h k).rec
    fun z o ↦ by simpa [h.ne, ↓← residue_eq_zero_iff_lt, sum_ite, mul_assoc, ← map_sum,
    (Units.ext (transvection_mul_transvection_same ..) : transvectionGL .. * transvectionGL .. =
    transvectionGL ..), surjInv_eq,
    filter_ne', card_filter] using congr(∑ r, $(A ⟨_, o⟩ (surjInv residue_surjective r - z).2)) :)

/-- For F with a uniformiser and a smooth representation of GL_N(F), there is a strictly
dominant t such that U_t is injective on the vectors fixed by the pro-p Iwahori subgroup I₁. -/
lemma exists_iwahoriHeckeHom_injective (ρ : Rep ℂ (GL (Fin N) F)) [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 =
  exp (-1)) : ∃ t, ∃ h :
  StrictMono _, Injective (iwahoriHeckeHom ρ ⟨t, h.monotone⟩) := let s a : dominantTorus := ⟨(if a ≤
    · then ϖ⁻¹ else 1), by simp_all +decide [dominantTorus, Monotone, apply_ite, ite_apply]; lia⟩
  ⟨(∏ a, s a).1, by simp_all [StrictMono, prod_ite, filter_ge_eq_Iic, s], .of_ker _
    (((nonZeroSMulDivisors ..).comap (iwahoriHeckeHom ρ)).prod_mem fun a _ x h ↦ have := a.neZero
    let n := permGL (finCycle a)⁻¹ * diagGL (s a)
    have hy : ρ n x ∈ levelSpace _ _ := by simpa using fun k h ↦ x.2 ⟨n⁻¹ * k * n,
      mem_proIwahori_iff_blockParahoric.2 (conj_monomial_mem_blockParahoric _
      _ _ (mem_proIwahori_iff_blockParahoric.1 h)
      (by simp_all [s, @apply_ite Fˣ, apply_ite v, apply_ite log]; fin_omega))⟩
    by simpa [Perm.monotone_iff, *, (ρ.ρ.apply_bijective n).1] using (exists_antitone_of_swap toDual
      (fun σ ↦ compactMean ρ.ρ proIwahori (ρ (permGL σ⁻¹) (ρ n x)) = 0)
      ⟨(finCycle a)⁻¹, by simp [n]; injection h⟩ fun σ _ _ c e _ ↦ by simpa [*, -map_inv] using
      (quadratic_relation c 0 (fun _ ↦ compactMean_apply) (transvectionGL_apply_permGL_inv hy e)
      (by intros; rw [← map_compactMean_of_factor _ (⟨·, diagGL_conj_mem_proIwahori · fun _ ↦ _,
      _⟩)] <;> simp_all)).symm))⟩

lemma IsExponent.apply_compactMean (hl : IsExponent ρ ξ l) : l (compactMean ρ.ρ proIwahori z) =
  l z := by simpa using hl (one_mem _) z

lemma IsExponent.apply_proIwahori (hl : IsExponent ρ ξ l) k (hk : k ∈ proIwahori) z : l (ρ k z) =
  l z := by simp [← hl.apply_compactMean, hk]

include hl in
lemma IsExponent.apply_diagGL_unit (ht : ∀ a, v (t a).1 = 1) z : l (ρ (diagGL t) z) =
  ξ t * l z := by rw [← map_compactMean_of_factor hl.apply_proIwahori (⟨·,
  diagGL_conj_mem_proIwahori · fun _ ↦ _, _⟩), hl] <;> aesop_cat

/-- Let (ξ, l) be an exponent, y fixed by a group containing the elements of the parahoric of c
with diagonal ≡ 1 mod ϖ. Then l(ρ(t)ρ(σ)y) = ξ(t) l(ρ(σ)y) if σb < σa implies |t_{σb}| ≤
|t_{σa}|, or c(a) ≤ c(b) and |ϖt_{σb}| ≤ |t_{σa}|. -/
lemma IsExponent.apply_monomial_translate {ρ : Rep ℂ (GL (Fin N) F)} [IsSmoothRep ρ.ρ] (hϖ : v ϖ.1 =
  exp (-1)) {y ξ l t K c} (hl : IsExponent ρ ξ l) (hz : y ∈ levelSpace ρ.ρ K) (o : ∀ {g},
  g ∈ blockParahoric c ∧ (∀ i, v (g i i - 1) < 1) → g ∈
  K) σ (H : ∀ a b, σ b < σ a → v (t (σ b)).1 ≤ v (t (σ a)).1 ∨ c a.1 ≤ c b.1 ∧ v (t (σ b)).1 ≤ v
  (t (σ a)).1 * exp 1) : l (ρ (diagGL t * permGL σ) y) = ξ t * l (ρ (permGL σ) y) := by
  have key {d} hd s (e : s = 1 ∨ s = t) := (map_compactMean_of_factor hl.apply_proIwahori fun g k ↦
    (exists_iwasawa_bruhat g).imp fun _ _ ↦ ⟨conj_unitriangular_mem_proIwahori hd (by tauto), by
    simpa using hz ⟨_, o (diagGL_mul_permGL s σ ▸ conj_monomial_mem_blockParahoric _ σ
      _ (mem_proIwahori_iff_blockParahoric.1 (mul_mem (inv_mem (by tauto)) k)) (by
      cases e <;> simp_all [← log_le_log] <;> grind [σ.injective, le_total]))⟩⟩) ▸ @hl d hd _
  have ⟨s, hs, _⟩ := exists_iwahoriHeckeHom_injective ρ hϖ
  have ⟨k, h⟩ := (eventually_pow_mul_mem_dominantTorus hs t).exists
  simpa [key (pow_mem hs.monotone k), mul_assoc, -map_pow] using key h 1
end
