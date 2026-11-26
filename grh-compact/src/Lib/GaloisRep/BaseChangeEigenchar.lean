import Lib.GaloisRep.BaseChangePlaces
import Lib.GaloisRep.LocalTranslates
import Lib.GaloisRep.Landherr
import Lib.GaloisRep.Avatars
import Lib.GaloisRep.ParahoricColumns

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Level decomposition and commuting families of local and spherical operators for the trace
comparison. Twisted trace of Hecke operator on definite unitary group as weighted orbital sum. -/

open Finset HasFiniteType DoubleCoset Gf LinearMap Set Subgroup

variable {E E' n W A} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E n) W} {S T : Set (FinPlace E)}
  (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) [Group A] (a : A →* Gf E n) (r : Gf E n →* A)

/-- The homomorphism a maps into the elements supported on S ∪ S̄, r∘a is the identity, and the
kernel of r consists of the elements trivial at S. -/
def IsLocalRetraction S := (∀ g, a g ∈ supportedOn n S) ∧ (∀ g, r (a g) = g) ∧ r.ker = trivialOn n S

section

attribute [local simp] supportedOn localLevel SetLike.ext_iff placesAbove funext_iff heckeFun_sum
  leftTranslation

/-- At a level L ≤ K_0 given by L₀ at S and B ∩ C elsewhere, commuting Hecke operators D_j at S
and the T_{u,i} at spherical split u off S ∪ S̄ preserve π^L and commute; suitable products
with D_k come from explicit functions (`IsOperatorOf`). -/
lemma exists_commuting_hecke_family L {L₀ B C} (hK : L ≤ Kf ..) {J X} {F : J → _} (hF : ∀ j,
  IsBiInvariant L₀ (F j)) {u : X → _} (hu : ∀ x, (u x).IsSplit) (hX : ∀ x, u x ∉ S.conjClosure ∧
  maxCompactAt n (u x) ≤ L) : let ρ := π.comp a
  let V :=
    levelSpace ρ L₀; let D j := heckeFun ρ L₀ (F j); let W := levelSpace π (trivialOn n S ⊓ L)
      let T := Sum.elim D fun x ↦ heckeSplit π (hu (Prod.fst x)) x.2; IsLocalRetraction a r S → L =
        .comap r L₀ ⊓ (B ⊓ C) → (∀ g, a g ∈ B ⊓ C) → (∀ i j, EqOn (D i * D j) (D j * D i) V) →
        levelSpace π L = V ⊓ W ∧ (∀ g, (∀ v ∈ W, ρ g v ∈ W) ∧ ∀ x, Commute (T (.inr x)) (ρ g)) ∧
        ∃ s : ∀ _, _, let A i := (T i).restrict (s i); (∀ i j, Commute (A i) (A j)) ∧ ∃ R : J → _ →
          _ → _, ∀ k, R k (A (.inl k)) (indicator B 1) ∧ ∀ {t φ},
      R k t φ → IsOperatorOf π L t (F k ∘ r * (φ * indicator C 1)) ∧ (∀ {i j},
          EqOn (D i * D k) (D j) V → R j (A (.inl i) * t) φ) ∧ ∀ x, supportedOn n {u x.1} ≤ C →
          R k (A (.inr x) * t) (heckeSplit leftTranslation (hu x.1) x.2 φ) := by
  rintro ρ V D W T ⟨p, q, o⟩ rfl hN c; simp at hN
  refine (fun E w ↦ ⟨E, w, Sum.rec (E ▸ fun j v h ↦ ⟨(hF j).heckeFun_mem h.1, by simp [T, D, hF,
    sum_mem, W.smul_mem, (w _).1 _ h.2]⟩) fun _ _ h ↦ heckeSplit_mem_levelSpace _ _ (levelSpace_anti
    (hX _).2 h) hK h, ?_⟩) ?_ fun g ↦
    ⟨fun _ h ↦ map_mem_levelSpace_of_commute h (commute_supportedOn_trivialOn (p g) ·.2.1
    |>.symm.map _), fun x ↦ LinearMap.ext (by simp_all [T, ρ, heckeSplit_comm_of_trivialOn])⟩
  simp +contextual +zetaDelta [iff_def, ← o, q, hN]; intro _ _ h k _ _ _
  simpa [*, mul_mem, -map_inv] using h (k * a (r k)⁻¹)
  intro Z; refine ⟨?m, fun k t φ ↦ ∃ T, t = Z _ * T ∧ ∀ i, IsOperatorOf π _ (Z (.inl i) * T)
    (F i ∘ r * (φ * _)), fun k ↦ ⟨⟨1, rfl, fun i ↦ .heckeFun_mul (hF i).1 ?_ ⟨1, rfl, by simp⟩⟩,
    @fun | _, _, ⟨T, rfl, h⟩ => ⟨h k, fun H ↦ ⟨T, by ext; exact H (E.le (by simp)).1, h⟩,
    fun x H ↦ ⟨_, (?m _ _).left_comm _, fun i ↦
    (?m _ _).left_comm _ ▸ (h i).heckeFun_mul (isBiInvariant_basicDoubleCoset _).1 (map_heckeSplit _
    _ (mulLeft ℂ (F i ∘ r) * mulRight ..) fun g e ↦ by simp [indicator_subgroup_mul_left, H e,
    r.mem_ker.1 (o ▸ supportedOn_compl.le (supportedOn_mono (by grind) e))])⟩⟩⟩⟩
  rintro ⟨⟩ ⟨⟩ <;> ext ⟨_, v⟩ <;> solve_by_elim [heckeSplit_comm, symm, (E.le v).1, map_heckeFun _
    (hF _).1 fun g ↦ congr($((w g).2 _) _), levelSpace_anti (hX _).2]
  choose _ _ using QuotientGroup.mk_out_eq_mul L₀
  simp [cosetFn, Finsupp.single_apply, QuotientGroup.eq, *, indicator, mul_mem_cancel_left, ite_and,
    ← @QuotientGroup.eq A]; lia

lemma isLocalRetraction_atSplit n [Fintype n] {w u} (h : ∀ v, .below E v = w ↔ v = u) hu hw :
    IsLocalRetraction (n := n) (atSplit hw) (atPlace w) {w} ∧ IsLocalRetraction (n :=
  n) (atSplit hu) (atPlace u) (placesAbove E' {w}) ∧ localLevel n (placesAbove _ {w}) =
  .comap (atPlace u) (intGL n Valued.v.integer) := by simp_all [IsLocalRetraction, ← below_star,
  star_eq_iff_star_eq, atPlace_star_eq_one_iff, atPlace_atSplit_of_ne]; tauto

lemma Gf.supportedOn_le_trivialOn (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) : supportedOn n S ≤
  trivialOn n T := biInf_mono H

lemma exists_remaining_places (H : ∀ w ∈ T, w ∉ S ∧ star w ∉ S) {K} (h : ∀ x : T, ∀ u ∈ placesAbove
  _ {x.1}, K u = Kw ..) : ∃ Y, idem (placesAbove _ T) * idem (placesAbove E' Y) = 0 ∧
  supportedOn n (placesAbove _ T) ≤ localLevel n (placesAbove _ Y) K ∧
  placesAbove _ (T ∪ Y) = (placesAbove E' S)ᶜ ∧ idem (placesAbove _ T) + idem (placesAbove _ Y) =
  1 - idem (placesAbove E' S) ∧ localLevel n (placesAbove _ S)ᶜ K = localLevel n (placesAbove _ T) ⊓
  localLevel n (placesAbove E' Y) K := ⟨(S ∪ T).conjClosureᶜ, by
  simp_all [LE.le, Set.ext_iff, DFunLike.ext_iff, idem_apply, below_star]
  grind [star_star, one_mem]⟩

end

/-- Twisted trace formula on definite V: for compatible σ, τ, s and open σ-stable L ≤ K ≤ K_0,
some c ≠ 0 makes the trace on L-fixed forms of the Hecke operator of φ times ψ ↦ s∘ψ∘σ⁻¹ a
sample sum (`IsSampleTotal`) of weight c of φ(x⁻¹γσ(x)) tr(ρ(γ)s). -/
lemma Space.isSampleTotal_twisted_trace {E n} [Field E] [CMType E] [Fintype n] (V :
  Space E _ 1) κ {K L} (σ : _ ≃* _) (cσ : Continuous σ.symm) (hK : K ≤ Kf E n) (hL : L ≤ K) (oL :
  L.IsOpen) (hσ : L.comap σ = L) (τ : _ ≃* _) : let j := V.embFin; let ρ := V.weightRep _ κ.2; (∀ γ,
      j (τ γ) = σ (j γ)) → ∀ s, (∀ γ, s * ρ γ = ρ (τ γ) * s) → ∃ c ≠ 0, ∃ h h', ∀ {φ T},
      IsOperatorOf (V.formTranslation κ) L T φ → IsSampleTotal (fun p q : _ × _ ↦ {g | q.1⁻¹ * j g *
      p.1 ∈ K ∧ g⁻¹ * q.2 * τ g = p.2}) (fun y ↦ φ (y.1⁻¹ * j y.2 * σ y.1) * (ρ y.2 * s).trace ℂ _)
      c ((T * ((s.compLeft _ ∘ₗ funLeft ℂ _ σ.symm).restrict h).restrict h').trace ℂ _) := by
  intro j ρ hτ s hs
  have := V.hasFiniteType_of_isLevel.of_le hK (isOpen_mono hL oL)
  refine ⟨_, Nat.cast_ne_zero.2 (this.4.relIndex_ne_zero oL), fun _ h ↦ ⟨(comap σ.symm.toMonoidHom
    _).isOpen_mono (by aesop_cat) (cσ.1 _ h.1), (reindex_equiv τ).1.2 (by simp_all [j, ρ, forms,
    SmoothForm, DFunLike.ext_iff])⟩, fun _ h k ↦ ?_, fun ⟨a, e, C⟩ ↦ e.substr ?_⟩
  ext; simpa [LinearMap.restrict] using congr(s ($(h ⟨σ.symm k, hσ.le (by simp)⟩).1 _) _)
  have := this.of_le hL oL
  choose S hS cS using exists_transporter V.Γf Fact.out .rfl
  have N {J} [HasFiniteType V.Γf J] h x := classSum_eq_relIndex_smul (L := L) (f := fun y ↦ (#(S J x
    y) : ℂ)) h 1 (by simp; rfl) fun y ↦ (by rw [cS, cS, out_eq', mul_one] : _ = (#(S J x y) : ℂ))
  simp_rw [classSum, finsum_eq_sum_of_fintype, Rat.smul_def] at N
  conv at N in _ * ∑ _,
    _ => simp [cS, out_eq', ↓card_classAut_out x, -mem_classAut, -MonoidHom.coe_range]
  have f x : (fun γ ↦ cosetFn L a (x⁻¹ * j γ * σ x) * (ρ γ * s).trace ℂ _).HasFiniteSupport :=
    .mul_left ((cosetFn L a).hasFiniteSupport.preimage' fun q _ ↦ .ofFinset (S L (x * q.out) (σ x))
    (by simp [j, *, mul_assoc, ← QuotientGroup.eq, eq_comm])) _
  exact ⟨∑ i, ∑ γ ∈ _, .single (_, γ) _, (trace_eq_weighted_sum (·.out) _ (LinearMap.domRestrict
    (Submodule.subtype _) _) (le_antisymm (fun _ ⟨φ, e⟩ ↦ e ▸ ⟨⟨φ.1.2.2, by simp⟩, (congr($(φ.2
    ·).1))⟩) fun F h ↦ ⟨⟨⟨F, mem_smoothFunctions_of_eigen _ oL h.2, h.1.1⟩, (Subtype.ext <| h.2 ·)⟩,
    rfl⟩) σ _ (by simp [*, mul_assoc]) (D := ∅) ((ite_eq_left id).mpr <| N le_rfl · |>.trans
      (by simp))
    (fun _ ↦ by simpa [-map_mul, asAlgebraHom_eq_sum_support] using! congr($(C _).1)) hσ).2.trans
    (by simp [j, ρ, ← hτ, hs,
    (finsum_comp _ τ.bijective).trans (finsum_eq_sum _ (f _)), mul_sum, -MonoidHom.coe_range]; rfl),
    fun y h ↦ by simpa [*, mul_sum, ← ncard_coe_finset, ↓card_eq_sum_card_fiberwise fun g a ↦
    (f _).mem_toFinset.2 (h (_, g⁻¹ * y.2 * τ g) g ⟨((hS ..).1 a).2, rfl⟩)] using! N hL y.1⟩
end

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Matching of spherical Hecke functions at places splitting completely in the extension.
Twisted character of base-changed weight equals character at the norm. -/

open Set Matrix RingHom Polynomial Gf Module
variable {E E' n W} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n] {σ :
  Gal(E'/E)} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E' n) W} {u : FinPlace E'}

attribute [local simp] map_aeval_matrix map_smul' adeleMap_apply star_idem Matrix.map_add
  atPlace_baseChangeGf twistedNorm_map_eq_prod adeleMap_gal_pow indicator_subgroup_mul_left
  idem_apply Polynomial.map_prod cutGL Set.ext_iff below_star atPlace_atSplit_of_ne
  placesAbove mul_mem_cancel_left mul_mem_cancel_right leftTranslation funext_iff

attribute [-simp] evalAt_apply in
omit [CMType E'] in
/-- Let μ be trivial at T, T contain no place with its conjugate, B be the places above T and their
conjugates. If z = 1 off T and P ∣ Nm z − X above T, z is a root on B, and z(γ)/z(γ)* is z(γ) above
T. -/
lemma IsStep.isNormRoot_of_one_side {μ} (hμ : IsStep E' μ) {B T} (e : B = placesAbove E' T) (hD :
  ∀ w ∈ T, ∀ x, μ (locIdele w x) = 1) (s : ∀ w ∈ T, star w ∉ T) {p P z} [NeZero p] (hz : ∀ u,
  .below E u ∉ T → z.map (evalAt u) = 1) (N : ∀ u, .below E u ∈ T →
  P.map (evalAt u) ∣ (twistedNorm (.map (adeleMap σ)) p z).map (evalAt u) - X) :
  IsNormRoot n (adeleMap σ) p (idem B) (normKer _ μ) P z ∧ ∀ γ a : Gf E' n, IsRootQuotient γ
  (idem B • z) a → ∀ u, .below E u ∈ T → a.atPlace u = aeval (γ.atPlace u).1 (z.map (evalAt u)) :=
  have I (u : FinPlace E') S := (evalAt_apply ..).trans (idem_apply S u)
  ⟨⟨by ext : 2; simp_all [← evalAt_apply, ← coeff_map]; grind, by
  rintro g rfl
  have N : (twistedNorm (.map (adeleMap σ)) p z).aeval g.1.1 = cutGL (idem_mul_self (.below E ⁻¹'
    T)) g.1 := matrix_ext_evalAt fun u ↦ if a : _ then (N u a).elim (by simp_all [sub_eq_iff_eq_add,
    aeval_self_charpoly, ← charpoly_map]) else by simp [*, (map_map (adeleMap _) (evalAt u) z).trans
    (map_map (evalAt _) (locMap _ rfl) _).symm]
  choose _ _ h using (twistedNorm_map_eq_prod p z ▸ isUnit_aeval_iff_isCoprime.1 ⟨_,
    N.symm⟩).of_prod_right 0 (by grind [NeZero])
  use fun k M _ ↦ (isUnit_det_of_left_inverse (by simpa [*, one_def] using congr(aeval M $h))).imp
    fun d c ↦ ⟨mem_of_locIdele_mem hμ.isClopen_normKer.1 fun u ↦ if a :
    u.below E ∈ T then by simp [adeleNorm_locIdele,
    *] else by simp [show ideleAt u d = 1 by ext; simp_all [ideleAt, map_det]], c⟩,
    matrix_ext_evalAt fun u ↦ by simp_all [← U.inv_val_eq_conjTranspose, Matrix.map_sub]; aesop⟩,
    fun _ _ a u _ ↦ by simpa [*, fun M ↦ (id rfl : Mᴴ.map (evalAt u) =
    (M.map (evalAt _))ᵀ.map (conjLoc (star_star u)))] using! congr(map $a (evalAt u))⟩

lemma heckeSplit_comp_baseChangeGf hu hw (s : (⇑(locMap _ (.refl (u.below E)))).Surjective) {j x}
  (hx : x ∈ sphericalAt π u) (h : ∀ k ∈ supportedOn n (.below E ⁻¹' {u.below E} \ {u}), π k x = x) :
  heckeSplit (π.comp baseChangeGf) (w :=
  u.below E) hw j x = heckeSplit π (w := u) hu j x := heckeFun_comp _ (by simp)
  ((mem_sphericalAt_iff _).1 hx) (by simp) (GL_map_surjective _ s) (by apply locMap_mem_Kw) (fun _ ↦
  by erw [← π.inv_apply_eq_iff, ← End.mul_apply, ← map_mul, h _ (mem_supportedOn.2 fun v _ _ ↦ ?_)]
     by_cases star v = u <;> [rw [← atPlace_star_eq_one_iff]; by_cases v = u] <;> aesop)
  (by simp [basicDoubleCoset, indicator_apply, ← map_inv, -coe_units_inv, ← map_det,
  ← mapMatrix_apply, v_locMap_eq_of_isUnit_log _ rfl ((s (uniformizer u)).imp (by simp_all))])

attribute [local grind =] star_star below_star below_comap atPlace_star_mem_iff InjOn

/-- For a step E'/E, σ ≠ 1 and a set S of split matched places (`IsMatched`), some set of
matching pairs (`IsMatchingPairAbove`) contains the pair of level indicators and, for each w ∈ S, is
stable under all (T_{w,j}, T_{u,j}) for some place u above w. -/
lemma exists_hecke_stable_matching {μ} (hσ : σ ≠ 1) [hμ : IsStep E' μ] {S} (h : ∀ w ∈ S, w.IsSplit ∧
  IsMatched E' μ w) : let B := localLevel n (placesAbove _ S); ∃ St : Set _, (indicator B 1 ∘
    baseChangeGf (E' := E'), indicator B 1) ∈ St ∧ (∀ x ∈ St, IsMatchingPairAbove σ μ S B x.1 x.2) ∧
    ∀ w : S, ∃ u, .below E u = w.1 ∧ ∀ x ∈ St, ∀ hw hu j, (heckeSplit
  leftTranslation (w := w) hw j x.1, heckeSplit leftTranslation (w := u) hu j x.2) ∈ St := by
  intro B
  obtain ⟨V, hV, -, b, c⟩ := exists_subset_bijOn (.below E ⁻¹' S) fun u : FinPlace E' ↦
    s(u.below E, (star u).below E)
  let A := FinPlace.below E ⁻¹' .below E '' V \ V
  have s : placesAbove E' S =
    placesAbove _ (.below E '' V) := by simp [SurjOn] at c ⊢; grind [=_ below_star]
  have l {g} : g ∈ B ↔ g ∈ localLevel n V ∧
    g ∈ localLevel n A := by grind [mem_localLevel, placesAbove, =_ atPlace_star_mem_iff]
  use {(F ∘ baseChangeGf, indicator (localLevel n A) 1 * F) | (F) (_ : ∀ k ∈ localLevel n V,
    leftTranslation k F = F ∧ ∀ g, F (g * k)
    = F g)}, ⟨indicator (localLevel n V) 1, by simp +contextual [indicator], by
    ext <;> simp [indicator, l, ite_and, mem_localLevel,
      A]; congr! with H; erw [ite_eq_left fun _ _ a e _ ↦
    (locMap_mem_Kw (w := .below E _) _).2 (e ▸ (locMap_mem_Kw _).1 (H _ a))]⟩, ?_, fun ⟨w, m⟩ ↦ ?_
  rintro _ ⟨F, hF, rfl⟩; have ⟨β, η⟩ := bijective_pow_gal hσ
  have key {u : FinPlace E'} {g d : Gal(E'/E)} (a : u.comap g ∈ V) : u.comap d ∈ V ↔ d = g :=
    (mul_left_surjective g d).rec fun d e ↦ e ▸ ⟨(mul_eq_left.2 <| (((h _ (hV a)).2.2 _ rfl).2
    _).mtr <| b · a (by grind)), by grind⟩
  have t i {u} : ∀ ⦃k⦄, atPlace (.comap ↑(σ ^ i) u) k ∈ Kw n _ → ((galoisGf σ)^[i] k).atPlace u ∈
    Kw .. := i.rec (by tauto) fun _ a _ ↦ @a _ ∘ (locMap_mem_Kw _).2
  use fun k hk ↦ ?_, fun P _ _ ↦ ⟨1 + idem V • (X - 1),
    (hμ.isNormRoot_of_one_side s (forall_mem_image.2 fun _
    a ↦ (h _ (hV a)).2.1) (by grind) (by simp; tauto) fun u ⟨v, a, e⟩ ↦ ?_).imp_right fun H γ a _ d
    ↦ ?_⟩; simp_all [indicator, (@l (galoisGf σ k)).1 fun u a ↦ t 1 (hk _ (by simpa))]
  obtain ⟨i, rfl⟩ := η.exists.1 (FinPlace.exists_gal_comap_eq e.symm)
  simp [Finset.prod_range, add_ite, key a, β.eq_iff]
  have ⟨_, a₂⟩ : a ∈ localLevel n A ∧ γ⁻¹ * a ∈ localLevel n V :=
    .imp (trivialOn_le_localLevel ·) (trivialOn_le_localLevel ·) (by
    simp +contextual [↓mem_trivialOn, Units.ext_iff, H _ _ d, ↓mem_image_of_mem, A])
  rw [← Nat.succ_pred_prime hμ.out] at *
  simp +contextual [← (hF _ a₂).2 γ, *]
  rintro δ _ rfl h _; simpa [twistedNorm, mul_div_assoc] using div_mem (inv_mem a₂) (list_prod_mem
    (List.forall_mem_map.2 fun i m u a ↦ t _ (h _ ⟨⟨u, by simpa⟩, β.ne
    (Fin.succ_ne_zero ⟨i, List.mem_range.1 m⟩) ∘ (@key u 1 _ a).1⟩)))
  obtain ⟨u, rfl, e⟩ : ∃ u, .below E u = w ∧ u ∈ V.conjClosure := by
    simp at s; grind [w.comap_surjective (algebraMap E E')]
  use u, rfl; rintro _ ⟨F, hF, rfl⟩ hw hu j
  have o a : atSplit hu a ∈ localLevel n A :=
    trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) (atSplit_mem_supportedOn hu a))
  use heckeSplit leftTranslation hu j F, fun k hk ↦ ⟨(heckeSplit_comm_of_atPlace_mem hu j ?_ (by
    grind [mem_localLevel])).symm.trans (congrArg _ ?_), ?_⟩, Prod.ext (heckeSplit_comp_baseChangeGf
    hu hw (fun y ↦ ⟨_, congr(evalAt u $(finAdeleIncl_adeleNorm E _ (1 + singleAdele u
    (y - 1)))).trans (by erw [map_prod, Fintype.prod_eq_single 1, adeleMap_id] <;> simp +contextual
    [(h _ m).2.2])⟩) ?_ (fun k a ↦
    (hF _ (trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) a))).1) ▸ map_heckeSplit _ _
    (LinearMap.funLeft ℂ ℂ baseChangeGf) ?_) ?_ <;> simp +contextual [heckeSplit, *, by simpa using
    hF, heckeGL, heckeFun_sum, ← mul_assoc, mem_localLevel, mem_Kf_iff, Finset.mul_sum]

open NumberField ComplexEmbedding ComplexConjugate Finset Fin Equiv Function

attribute [local implicit_reducible] stdSpace

variable {E E' n : _} [Field E] [Field E'] [Algebra E E'] [IsGalois E E'] [Fintype n] {σ :
  Gal(E'/E)}

/-- Base change of a weight κ from E to E': its column numbers and determinant exponent at an
infinite place are those of κ at the place of E below. -/
noncomputable def Weight.baseChange (κ : Weight E) : Weight E' :=
  ((κ.1 <| ·.comap (algebraMap ..)), (κ.2 <| ·.comap (algebraMap ..)))

/-- For E'/E Galois of prime degree p, σ ≠ 1, compatible CM types and ρ the pulled-back weight
representation, some s has sρ(δ) = ρ(σδ)s, and tr(ρ(δ)s) is the character of weight κ at γ
whenever δσ(δ)⋯σ^{p−1}(δ) = γ. -/
lemma exists_twisted_weightRep_trace (hσ : σ ≠ 1) [hp : Fact (finrank E E').Prime] [CMType E] [c :
  CMOver E E'] (κ : Weight E) : let j := U.map (J := 1) (algebraMap E E') (map_star_CM _)
  let ω := U.mapEnd (map_star_CM σ)
  let ρ := (stdSpace _ n).weightRep κ.baseChange.1 κ.baseChange.2
  ∃ s, (∀ δ, s * ρ δ = ρ (ω δ) * s) ∧ ∀ δ γ, twistedNorm ω (finrank E E') δ = j γ →
    (s * ρ δ).trace ℂ _ =
  ((stdSpace ..).weightRep κ.1 κ.2 γ).trace ℂ _ := (Nat.exists_eq_add_one.2 hp.1.pos).elim (by
  intro k hE j ω ρ
  choose i hi using fun u ↦ (AlgEquiv.symm_bijective.comp (hE ▸ bijective_pow_gal hσ)).2.exists.1
    (exists_comp_symm_eq_of_comp_eq (lift _ ((Φ (u.comap (algebraMap E _))).comp conj)) ((Φ u).comp
    conj) (RingHom.ext (by simp [@starRingEnd_apply E, @starRingEnd_apply E', by
    simpa [RingHom.ext_iff] using c.2 (Φ u)])))
  let e := ofBijective _ ((Nat.bijective_iff_injective_and_card fun u ↦ (⟨i u, u.comap (algebraMap E
    _)⟩ : Σ _, _)).2 ⟨fun _ ↦ by grind [mk_Φ, cancel_right, surjective], by simp [mul_comm, *, (⟨by
    simp [InfinitePlace.IsUnramified]⟩ : IsUnramifiedAtInfinitePlaces E E').card_infinitePlace]⟩)
  let A : WeylIndex n κ.baseChange.1 ≃ (_ → WeylIndex ..) :=
    .trans (.symm (e.symm.piCongrLeft' _)) (piCurry _)
  let G l := (weylRep κ.1 κ.2).comp (.pi fun v ↦ GeneralLinearGroup.map (n := n)
    ((lift _ ((Φ v).comp conj)).comp (σ ^ l).toRingHom))
  use (submatrix 1 (A.trans ((finRotate _).piCongrLeft' _)) A).toLin'
  simp_rw [fun δ ↦ ((LinearMap.ext (stdSpace_weightRep_apply δ)).trans (congrArg _ (Matrix.ext
    (by simp [reindex_equiv A.symm, ← hi, G, weylRep, @schur_apply_eq_prod (InfinitePlace _),
    prod_smul, ← Fintype.prod_sigma', reindex_equiv e]; tauto))) : ρ δ = (of fun a b ↦ ∏ l, G l.1 δ
    (A a l) (A b l)).toLin'), End.mul_eq_comp, ← toLin'_mul, mul_submatrix_one, one_submatrix_mul]
  use fun δ ↦ congrArg _ (Matrix.ext fun i _ ↦ .trans (.symm (Equiv.prod_comp (finRotate _) _)) (by
    simp [G, val_add, ← hE, ← IsGalois.card_aut_eq_finrank]; rfl)), fun δ γ h ↦ .symm ?_
  simp [trace, reindex_equiv A.symm, prod_univ_succ, ← cycleRange_last]
  trans (G 0 (j γ)).trace
  simp [LinearMap.ext (g := toLin' _) (stdSpace_weightRep_apply γ), G, j, U.map, weylRep,
    Units.smul_def, comp_def]
  simp [*, twistedNorm, ← h]
  refine k.rec ?_ ?_ δ (G 0 δ) <;> intros <;> simp [reindex_equiv (consEquiv _), ← mul_assoc,
    mul_apply, sum_mul, Fintype.sum_prod_type_right, prod_univ_succ, *, univ_eq_empty] <;> rfl)
end

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Tame levels; matching of unit functions at principal congruence level, keeping unramified
places maximal. -/

open NumberField Matrix Set Valued Module Ideal Subtype


variable {E E' n : Type} [Field E] [CMType E] [Field E'] [NumberField E'] [CMType E'] [Algebra E E']
  [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ} [hμ : IsStep (E := E) E' μ] {f : E →+* E}
attribute [local simp] ite_mem adeleMap_idem_placesAbove adeleMap_gal_pow
  Algebra.algebraMap_ofSubring idem_mul_self

variable (E' μ) in
/-- At every place u of E' above w, some element of Gal(E'/E) lies outside the inertia group of
u, and μ∘Nm is trivial on the local units at u. -/
def IsStepUnramifiedAt w := ∀ u : FinPlace E', u.below E = w → (∃ σ, σ ∉ u.1.inertia Gal(E'/E)) ∧
  ∀ x, v x.1 = 1 → μ (locIdele _ (localNorm E u x)) = 1

/-- The ring homomorphism between the integral finite adeles of E and of E' induced by an
embedding f: E → E'. -/
noncomputable def intAdeleMap (f : E →+* E') := (adeleMap f).restrict _ _ fun _ ↦
  (adeleMap_mem_Ohat f).2

@[simp] lemma intAdeleMap_iterate i : ∀ x, (intAdeleMap f)^[i] x =
  (adeleMap f ^ i) x := by induction i <;> tauto

omit [CMType E] [NumberField E'] [CMType E'] in
lemma notMem_inertia_of_comap_ne {u : FinPlace E'} (h : u.comap σ ≠ u) : σ ∉ u.1.inertia _ :=
  fun a ↦ h (by ext x; simpa using! u.1.add_mem_iff_right (b := x) (a x))

include hσ hμ

lemma exists_isTameAtLevel_intAdeleMap : ∃ C ≠ 0, ∀ m : Ô E', intAdeleMap σ m = m →
  (∀ u, C.cast ∈ u.1 → (∀ g, g ∈ u.1.inertia Gal(E'/E)) → reduceAt u m = 0) →
  IsTameAtLevel (intAdeleMap σ) (finrank E E') m := by
  obtain ⟨⟨e, _⟩, b, x, _⟩ := hμ.exists_trace_eq_one, bijective_pow_gal hσ,
    not_forall.1 (hσ ∘ IsGaloisGroup.faithful (𝓞 E) (B := 𝓞 E').1)
  refine ⟨(span {σ • x - x}).absNorm, by simpa, fun m a h ↦ ⟨a, ⟨algebraMap _ _ e, 0, val_injective
    (by simp [b.sum_comp (· e), *, Finset.sum_range, ← map_sum, ← trace_eq_sum_automorphisms,
    -AlgEquiv.coe_pow])⟩, by ext; simp [↓adeleMap_pow_finrank_eq_one], finrank_pos,
    fun i l P _ hP ↦ ?_⟩⟩
  have H : ∀ g, g ∈ (P.under (𝓞 E')).inertia _ := (bijective_pow_gal ((@b.1 ⟨i, l.2⟩ 0).mt (by
    grind))).2.forall.2 (pow_mem (fun _ ↦ by simp; convert hP _; simp [← coe_inj, algebraMap.smul'])
      ·)
  exact map_le_of_le_comap (fun _ ↦ algebraMap_ResField_eq_zero.1) ((map_under_Ô (by simpa) (I :=
    RingHom.ker (reduceAt ⟨_, inferInstance, by simpa ∘ (·.le (H ..))⟩))
    (algebraMap_ResField_eq_zero.2
    (H ..))).ge (h _ ((span_singleton_le_iff_mem _).2 (H ..) (absNorm_mem _)) H))

/-- For a step, σ ≠ 1 and H open: there are levels K_u ≤ GL_n(O_u) over E', maximal above
`IsStepUnramifiedAt` places w with K_w ≤ H, pulling back into H; each level L above S is open,
σ-stable, satisfies `CocyclesSplit`, and its indicators form a `IsMatchingPairAbove`. -/
lemma exists_baseChange_level {H} (hH : H.IsOpen) : ∃ K, (∀ u, K u ≤ Kw n u) ∧
  (∀ S L, L = localLevel n (placesAbove _ S) K → L.IsOpen ∧ (∀ k, galoisGf σ k ∈ L ↔ k ∈ L) ∧
  CocyclesSplit (finrank E E') (idem (placesAbove _ S)) L (galoisGf σ) ∧ IsMatchingPairAbove σ μ S L
  (indicator L 1 ∘ baseChangeGf (E' := E')) (indicator L 1)) ∧ (localLevel n univ
  K).comap baseChangeGf ≤ H ∧ ∀ w, IsStepUnramifiedAt E' μ w → maxCompactAt n w ≤ H →
  ∀ u ∈ placesAbove _ {w}, K u = Kw n u := by
  obtain ⟨⟨C, C₀, t⟩, S₀, hS, hS'⟩ := exists_isTameAtLevel_intAdeleMap hσ,
    exists_inf_trivialOn_le hH
  let A := placesAbove E' {w | IsStepUnramifiedAt E' μ w ∧ w ∉ conjClosure S₀}
  have un {u} (h : u ∈ A) := h.elim (·.1 u rfl) (·.1 _ (below_star u) |>.imp (by
    simpa using fun σ x b ↦ ⟨σ, _, by convert b; ext; apply map_star_CM σ.toRingHom⟩) fun b y _ ↦ by
    simpa [↓star_mul, ↓← units_map_adeleNorm_star, adeleNorm_locIdele, star_locIdele, *] using
      (hμ.apply_norm_eq_one_iff _).2 ⟨1, locIdele u y, rfl⟩)
  let F x := x + idem A * (1 - x)
  obtain ⟨N, N₀, U⟩ := mem_nhds_zero_finAdele_iff.1 (((isCompact_Ô.prod
    (isCompact_idelesUnitOff_empty.diff hμ.isClopen_normKer.2)).eventually_forall_mem (fun x p ↦
    p.2.1 - F x * p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦
    b (mem_of_locIdele_mem hμ.isClopen_normKer.1 fun u ↦ congr(μ $(adeleNorm_locIdele
    ..)).trans (by_cases (un · |>.2 _ (mem_idelesUnitOff.1 a u id)) fun c ↦ by simp [(Units.ext (by
    simpa [F, c, ideleAt] using congr($e u)) : ideleAt u _ = 1)]))).and ((isCompact_Ô.matrix.prod
    (isCompact_Kf.diff hH)).eventually_forall_mem (fun x p ↦
    p.2.1.1.map (finAdeleIncl _ E') - F x • p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦
    b (hS' ⟨a, Gf.mem_trivialOn.2 ((FinPlace.comap_surjective
    _).forall.2 fun u c ↦ Units.ext (ext fun i j ↦ RingHom.injective _ (congr($(eq_add_of_sub_eq e)
    i j u).trans (by simp +contextual [F, A, apply_ite, placesAbove, mod_cast c]))))⟩)))
  specialize U C (by simp); let m : Ô _ := N * C + ⟨_, idem_mem_Ô A⟩ * (1 - N * C)
  let k := F ((N * C)⁻¹ : E')
  have hk : m * k = 1 := by dsimp [m]; grind [idem_mul_self, map_natCast,
    congr(($(@mul_inv_cancel₀ E' _ (N * C) (by positivity)) : 𝔸f E'))]
  have hK {u g} : g ∈ congruenceGL ((v.leSubmodule 1).comap (.mulLeft _ (k u))) id ↔ g ∈ Kw n u ∧
    ∀ i j, _ * _ ∈ LocInt u := .rfl
  refine ⟨_, fun _ _ ↦ (hK.1 · |>.1), fun S L hL ↦ ?_, fun g h ↦ by
    simp [localLevel, atPlace_sub_one_apply, forall_and, *, -Matrix.sub_apply, ← mem_Kf_iff,
      baseChangeGf_mem_Kf] at h
    exact by_contra (U.2 (k • _, g) ⟨fun _ _ ↦ mem_Ô.2 (h.2 · ..), h.1, ·⟩
      (by erw [smul_smul, hk, one_smul, sub_sub_self]; rfl)), fun w b c u hu ↦ by
    ext; simp +contextual [↓hK, k, F, mem_intGL, sub_mem, show u ∈ A by grind [placesAbove]]⟩
  have hL' g : g ∈ L ↔ ∀ a b, idem (placesAbove _ S) * k * (g.1.1 - 1) a b ∈ Ô _ := by
    simp only [*, mem_localLevel, mul_assoc, idem_mul_mem_Ô, finAdele_mul_apply,
      ← atPlace_sub_one_apply, forall_and, mem_intGL]; rw [and_iff_right_of_imp fun H ↦ ?_]; tauto
    have a := (mul_mem (mem_Ô.1 m.2 _) <| H · · · ·)
    simp [← mul_assoc, ← finAdele_mul_apply, hk, sub_eq_add_neg, add_mem_cancel_right] at a
    exact ⟨a, fun w h i j ↦ (v_locMap_le_one ..).1 (g.atPlace_star rfl ▸ a _ (by simpa) ..)⟩
  refine have a g := ?_; ⟨(ext hL').symm.subst isOpen_Ô.matrix.preimage_of_continuous, a,
      isMatchingPair_congruence_level ⟨_, idem_mem_Ô _⟩ isProfiniteRing_intAdeles (t 0 ?_ ?_) ?_
      (((map_sub ..).trans (congrArg _ ?_)).subst (exists_isUnit_sub_star_Ohat.choose_spec.map
      (intAdeleMap (algebraMap E _)))) ?_ (t (_ * m) ?_ fun u c b ↦ by
    simp [m, by simpa using algebraMap_ResField_eq_zero.2 c, un.mt, b]) ?_
    ⟨(star_mul' ·.1)⟩ (Subring.isIntegrallyClosedIn_iff.2 fun _ h ↦ mem_Ô.2 fun u ↦
    ((Valuation.integer.integers (v.comap (evalAt u))).mem_of_integral (h.map_of_comp_eq
    (Subring.inclusion (iInf_le ..)) 1 rfl) :)) _ rfl ?_ ?_ ((mul_mul_mul_comm ..).trans (by
    simp [*])) ?_ (hL' · |>.trans ⟨fun h ↦ ⟨(⟨_, h · ·⟩), rfl⟩, (congrFun₂ ·.choose_spec · ·
    |>.subst (prop _))⟩) fun y z _ ↦ by_contra (U.1 (_, _) ⟨y.2, by simp [coe_idelesUnitOff_empty,
      mul_mem, add_mem, Submonoid.mem_units_iff], ·⟩ (add_sub_cancel_right ..))⟩
  simp +zetaDelta [hL', ↓← adeleMap_mem_Ohat σ.toRingHom (x := _ * (g.1.1 - 1) _ _)]; rfl
  all_goals simp +zetaDelta [a, intAdeleMap, ← coe_inj, star_idem, preimage,
    adeleMap_star, mem_range_finAdeleIncl_iff.1, ← mul_assoc]
end

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

Part of: Landherr's Hasse principle for hermitian forms; weak approximation for unitary groups
(known result; see Lib.Adelic.Landherr.Landherr).

This file: Hasse principle for norms in one CM field via reciprocity and Hasse's norm theorem.
Adelically split unitary cocycles split rationally (Landherr); normal matrices are semisimple.
Polynomial roots inverting the norm map; products of local matching pairs. -/

open Subgroup NumberField Algebra IntermediateField IsGalois ComplexEmbedding Finset
variable {E E' : Type} {L} [Field L] [NumberField L] [IsCMField L] [Field E] [Field E']
  [Algebra E L]

lemma exists_star_principalIdele_mul_eq (x : L) {w : 𝔸f L} (h : w = x * star w) : ∃ y, IsSelfAdjoint
  ((principalIdele y).1 * w) :=
  ⟨(by grind [@exists_isUnit_sub_star L, star_one L, Ne.isUnit] : ∃ z, IsUnit (z + x *
  star z)).choose_spec.star.unit, by simp [IsSelfAdjoint]; grind [by simpa using congr(star $h)]⟩

/-- Hasse principle for a step E'/E and a CM field L = E'(x), xx̄ = 1, g any element of Gal(L/E)
fixing x (its norm N runs over orderOf g steps): an idele u with μ(N_{L/E}u) = 1 whose g-norm N
satisfies N = xN̄ has c̄·z·u·g(c) = s, z in L, c invertible, s̄ = s. -/
lemma IsStep.exists_selfAdjoint_of_norm [NumberField E] [IsCMField E] [Algebra E E'] [Algebra E' L]
  [IsScalarTower E E' L] {μ} (hμ : IsStep (E := E) E' μ) {g : Gal(L/E)} {x} (hx : g x = x) (hL :
  E'[x] = ⊤) u (hu : u ∈ normKer L μ) (hN : let N := (u.1 * adeleMap g ·)^[orderOf g] 1; N =
    x • star N) :
  ∃ z c, IsUnit c ∧ IsSelfAdjoint (star c * ((principalIdele z * u).1 * adeleMap g c)) := by
  let K := fixedField (zpowers g)
  algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap E L),
    (Ω.fieldEmb L).comp (algebraMap E' L)]
  lift x to K using (smul_eq_self_of_mem_zpowers ·.2 hx)
  rcases IsScalarTower.to₁₂₄ E E' L Ω, @id (IsGalois K L) (of_fixed_field ..),
    (subgroupEquivAlgEquiv _).isCyclic.1 (isCyclic_zpowers g), isCMField_of_forall_exists_conj E
    fun y : K ↦ ⟨⟨_, fun a ↦ (map_star_CM a.1.toRingHom y).trans (congrArg _ (y.2 a))⟩,
    (by simp [← lift_algebraMap_apply L ·])⟩
  have nm w := (finAdeleIncl_adeleNorm K L w).trans (((finEquivZPowers
    (isOfFinOrder_of_finite g)).trans (subgroupEquivAlgEquiv _).1).prod_comp _).symm
  obtain ⟨⟨y, a, w, -, e⟩, ⟨χ, i⟩, ψ, j⟩ := (exists_star_principalIdele_mul_eq x (adeleMap_injective
    _ ((nm u).trans (by simpa [adeleMap_star, nm, iterate_mul_apply, adeleMap_gal_pow,
    prod_range] using! hN)))).imp ((@exists_eq_principalIdele_mul_norm K _ {}).1 (t :=
    principalIdele · * u.map _) · 1 (by simp)), exists_char_of_isCyclic (isCyclic_of_prime_card
    (card_aut_eq_finrank E E')), exists_char_of_isCyclic ‹_›
  obtain ⟨c, s, -, ⟨⟩⟩ := (char_artinMap_eq_one_iff ψ w).1 ((artinMap _ w).exists_rep.elim
    fun f r ↦ r ▸ eq_fixingSubgroup_of_isProGalois (J := j).1.ge fun ⟨_, _, rfl⟩ ↦ hL.ge.trans
    (AlgHom.adjoin_le_equalizer ⟨f.toRingHom.comp _, (eq_fixingSubgroup_of_isProGalois (J := i).1.le
    (artinMap_adeleNorm (g := f.restrictScalars E) r.symm 1 (by tauto) ▸ (char_artinMap_eq_one_iff
    ..).2 (by simpa [← (((adeleNorm E K).comp (adeleNorm K L)).ext adeleNorm_adeleNorm),
    isTotallyPositive_of_isTotallyComplex, ← hμ.apply_norm_eq_one_iff, hμ.apply_principal,
    map_adeleNorm_principalIdele, units_map_adeleNorm_star, eq_inv_mul_of_mul_eq e] using
    hu)) ⟨_, ·, rfl⟩)⟩ (algHom ..) (forall_eq.2 (f.4 x))) ⟨⟩)
  have ⟨k, H⟩ : (s * star s / u).map (adeleNorm ..) ∈ principalIdele.range :=
    ⟨y / (a * c * star c), by simp [div_eq_div_iff_mul_eq_mul, e, Units.ext_iff]; ring⟩
  obtain ⟨z, rfl⟩ :=
    hasse_norm k (congr($H.1 ·) ▸ adeleNorm_mem_closure) (isTotallyPositive_of_isTotallyComplex _)
  exact ⟨z, (hilbert90_finite_idele (u := ↑(principalIdele z / _)) (by
    erw [prod_range, ← nm, ← Units.coe_map, map_div, ← H, map_adeleNorm_principalIdele]; simp)).imp
    fun _ ↦ .imp_right (by nth_rw 1 [← ·]; simp [IsSelfAdjoint, division_def]; ring)⟩

open Matrix Polynomial UniqueFactorizationMonoid Classical ComplexOrder Module Function U
variable {E E' n : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
  [Algebra E E'] [IsGalois E E'] [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1)
  [Fact (finrank E E').Prime]

/-- A normal matrix over a CM field (one commuting with its conjugate transpose) is killed by
the radical of its characteristic polynomial. -/
@[simp] lemma aeval_radical_charpoly [IsCMField E]
    {M : Matrix n n E} [IsStarNormal M] : aeval M (radical
  M.charpoly) = 0 := have := Matrix.isNilpotent_trace_of_isNilpotent ((commute_conjTranspose_aeval M
    (w := radical M.charpoly).isNilpotent_mul_left
    ⟨_, by simpa [aeval_self_charpoly] using aeval_dvd M (Classical.choose_spec
    (exists_dvd_radical_self_pow M.charpoly_monic.ne_zero))⟩).map (Φ ofNonempty).mapMatrix)
  by simpa [conjTranspose_map _ (map_star_complex _), ← ext_iff,
    trace_conjTranspose_mul_self_eq_zero_iff]

include hσ

/-- For E'/E Galois of prime degree and σ ≠ 1 in its Galois group, every element of E' fixed by
σ lies in E. -/
lemma galois_descent_prime ⦃x⦄ (h : σ x = x) : x ∈ (algebraMap E _).range :=
  (mem_bot_iff_fixed x).2 (by simp [(bijective_pow_gal hσ).2.forall, iterate_fixed h])

/-- For E'/E Galois of prime degree and σ ≠ 1 in its Galois group, every finite adele of E'
fixed by σ comes from a finite adele of E. -/
lemma adeleMap_galois_descent ⦃x⦄ (h : adeleMap σ x = x) : x ∈ (finAdeleIncl E E').range := by
  simp [↓mem_range_finAdeleIncl_iff, (bijective_pow_gal hσ).2.forall, ← adeleMap_gal_pow,
    iterate_fixed h]

omit hσ in
/-- Hasse principle for cocycles: for E stably unramified, E'/E Galois of prime degree, σ ≠ 1, a
rational point s of the standard definite U(n) over E' with twisted norm 1 that equals
uσ(u)⁻¹ over the finite adeles equals gσ(g)⁻¹ with g rational. -/
lemma U.hasse_principle_coboundary [IsCMField E']
    {E : Type} [Field E] [CMType E] [Algebra E E'] [IsGalois E E']
    {σ : Gal(E'/E)} (hσ : σ ≠ 1) [Fact (finrank E E').Prime] [StablyUnram E] {s} (u : Gf _ n) (hs :
  (map (algebraMap E' _)) s = u * (galoisGf σ u)⁻¹) (hN : twistedNorm (mapEnd (map_star_CM σ))
  (finrank E E') s = 1) : ∃ g, mapEnd (map_star_CM σ) g = s⁻¹ * g := by
  let a := algebraMap E' (𝔸f E')
  choose g _ hg _ using (isTameAtLevel_gal σ).hilbert90_gl (by tauto) s.1 (Y :=
    s - 1) (by simp) (by erw [← map_twistedNorm (U 1).subtype,
    orderOf_eq_prime (card_aut_eq_finrank E E' ▸ pow_card_eq_one')] <;> aesop)
  obtain ⟨⟨y, hy⟩, J, hJ⟩ := exists_gl_map_eq_of_fixed (adeleMap_injective _)
    (adeleMap_galois_descent hσ) (g := u.1⁻¹ * g.map a) (by ext1; simpa [a, (congr($hs.1.1) :
    s.1.1.map _ = _), comp_def, mul_assoc] using! congr(u⁻¹ * ($hg).map a)),
    exists_gl_map_eq_of_fixed (RingHom.injective _) (galois_descent_prime hσ) (g :=
    star g * 1 * g) (by ext1; simpa [star, conjTranspose_map _ (map_star_CM _),
    ← inv_val_eq_conjTranspose, mul_assoc, -RingHom.coe_coe] using congr($hgᴴ * $hg))
  choose l hl using Space.landherr ⟨J, _, gram_mkAdelicGL (fun w ↦ gram_inv_of_gram_eq (x :=
    g.map _) (by simpa [entrywise] using congr($hJ.symm.1.map (ComplexEmbedding.lift _ (Φ w)))))
    (gram_inv_of_gram_eq (Matrix.map_injective (adeleMap_injective (algebraMap _ E'))
    (by simpa [← hy, ↓map_conjTranspose_mul_mul, adeleMap_star] using (gram_mul_of_gram_eq u⁻¹.2
    (y := g.map a) (by simpa [entrywise, a] using congr($hJ.symm.1.map a))))))⟩ (stdSpace E n)
  use ⟨g * l.map (algebraMap ..),
    gram_mul_of_gram_eq congr($hJ.symm) (by simp [← map_conjTranspose_mul_mul, map_star_CM,
    hl])⟩, eq_inv_mul_of_mul_eq (by ext; simp_all [map, ← mul_assoc, comp_def])

omit hσ
variable {R S n : Type _} [CommRing R] [StarRing R] [Fintype n] {γ γ' a c : U (1 : Matrix n n R)}
  {σ : R →+* R} {z : Polynomial R} {w : Polynomial R} {p : ℕ} {u : R} {v : R} {D : Subgroup Rˣ}
  {x : Matrix n n R} {y : Matrix n n R} [CommRing S] [StarRing S] {hσ : ∀ x, σ _ = _}

instance : IsStarNormal γ.1.1 := ⟨by simp [commute_iff_eq, star, ← inv_val_eq_conjTranspose]⟩

attribute [local simp] mul_assoc mul_add conjTranspose_nonsing_inv map_aeval_matrix IsRootQuotient

lemma U.isRootQuotient_conj (h : γ * c = c * γ') : IsRootQuotient γ' z a → IsRootQuotient γ z
  ↑(c * a * c⁻¹) := by simp [← c.1.mul_inv_eq_iff_eq_mul.2 (aeval_semiconj congr($h.1.1).symm _),
  ← inv_val_eq_conjTranspose]; grind

lemma U.isRootQuotient_map {f : R →+* S} hf (h : IsRootQuotient γ z a) : IsRootQuotient ((map f hf)
  γ) (z.map f) ((map f hf) a : U 1) := by simpa [conjTranspose_map _ hf] using! congr(($h).map f)

lemma U.existsUnique_isRootQuotient (h : IsUnit (aeval γ.1.1 z)) : ∃! a : U 1,
  IsRootQuotient γ z a.1.1 :=
  have := h.invertible; ⟨of isUnit_one _ (by simp [commute_conjTranspose_aeval, Commute.left_comm]),
    invOf_mul_cancel_right .., by aesop (add simp mul_right_eq_iff_eq_mul_invOf)⟩

lemma IsRootQuotient.mul : IsRootQuotient γ z x → IsRootQuotient γ w y → IsRootQuotient γ (z * w)
  (x * y) := by grind [(commute_conjTranspose_aeval γ.1.1).eq, conjTranspose_mul]

lemma IsMatchingPair.mul {A j K L f f' φ φ'} (h : IsMatchingPair (A := A) (n := n) hσ p u D j K f φ)
  (h' : IsMatchingPair hσ p v D j L f' φ') : u * v = 0 → u * u = u → v * v = v → star u = u →
  star v = v → IsMatchingPair hσ p (u + v) D j (K ⊓ L) (f * f') (φ *
  φ') := by intros; refine ⟨by simp +contextual [h.1, h'.1, -mul_assoc], fun P H e ↦ match h.2 P ?_
  e, h'.2 P ?_ e with | ⟨z, ⟨a, A⟩, a'⟩, ⟨w, ⟨b, B⟩, b'⟩ => ⟨z * w, ⟨by grind [congr($a * $b),
  smul_mul_smul], fun γ c ↦ ⟨by grind [mul_mem, det_mul], by
  convert (A γ c).2.mul (B γ c).2 <;> simp [twistedNorm_map_eq_prod, add_mul]
  match_scalars <;> grind⟩⟩, fun γ r
  _ hr ↦ by simp +contextual [a' γ r, b' γ r, *, by simpa [↓smul_smul, mul_sub, mul_comm, *] using
  congr((u • $hr, v • $hr, z * u • $b.symm, v • $a.symm * w))]⟩⟩ <;> revert H <;> gcongr <;> simp

lemma IsRootQuotient.twistedNorm_eq_mul (h : IsRootQuotient γ (twistedNorm (.map σ) p z) γ) (hc :
  γ * c = c * mapEnd hσ γ) (ha : IsRootQuotient γ z a) (hu : IsUnit (aeval γ.1.1 z)) : twistedNorm
  (mapEnd hσ) p c = γ * twistedNorm (mapEnd hσ) p (a⁻¹ * c) := eq_mul_of_mul_inv_eq (And.elim
  (existsUnique_isRootQuotient · |>.unique · h) (p.rec (by simp [twistedNorm]) fun _ ih ↦ by
  erw [twistedNorm_succ' (mapRingHom σ).1, mul_comm]
  simpa [*, aeval_semiconj (x := γ.1.1.map σ) congr($hc.1.1).symm, twistedNorm_succ']
  using! ih.imp (c.1.isUnit.mul ∘ .map σ.mapMatrix)
    (isRootQuotient_map hσ · |> isRootQuotient_conj hc |>.mul ha)))
end

section
/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: An adelic polynomial root of the norm can be corrected to a rational one. Splitting data
for the Weil representation pass to suitably unramified CM extensions. -/
seal Finset.univ Finset.sum Finset.prod

attribute [-simp] Subtype.forall multiplicity_eq_one_of_not_finiteMultiplicity

open NumberField Matrix Polynomial UniqueFactorizationMonoid AdjoinRoot MulAction Function
  Norms.L2Operator Algebra AlgEquiv MulDistribMulAction Ideal ComplexConjugate Ring

/-- For a step E'/E, σ ≠ 1, σ^p = 1, z a root for P = σP = charpoly γ': some rational w and
adelic c make x = w·z·σc invertible at each adelic unitary γ killed by rad P, and a·x(γ)* =
x(γ) implies a·c(γ)* = c(γ). -/
lemma exists_global_root {E E' n} [Field E] [CMType E] [Field E'] [Algebra E E'] [Fintype n]
    {p μ} {σ : Gal(E'/E)} [Fact p.Prime] (ho : σ ^ p = 1) (hσ : σ ≠ 1) [hμ : IsStep (E := E) E' μ]
    {z} {γ' : U (n := n) 1} : let k := algebraMap E' _; let P := γ'.1.1.charpoly; σ • P = P →
    IsNormRoot n (adeleMap σ) p 1 (normKer _ μ) (P.map k) z → ∀ {γ : Gf _ n}, γ.1.1.charpoly =
      P.map k → let T c := z * mapRingHom (adeleMap σ.toRingHom) c; ∃ w c, ∀ x, .map k w * T c = x →
        ∀ γ : Gf _ n, aeval γ.1.1 ((radical P).map k) = 0 → IsUnit (aeval γ.1.1 x) ∧
        IsRootQuotient γ x ≤ IsRootQuotient γ c := by
  intro k P hγ hz γ e T
  obtain ⟨⟨_, v, hv⟩, hI⟩ := @id (IsCoprime P X) (isUnit_aeval_iff_isCoprime.1 (by simp)), fun {q} ↦
    mem_primeFactors.trans (P.mem_normalizedFactors_iff (p := q) (charpoly_monic _).ne_zero)
  have cj {γ : Gf E' n} (h : aeval γ.1.1 (P.map k) = 0) := by
    simpa [← aeval_comp, star, by simpa using left_inv_eq_left_inv γ.2 (by
      simpa [h] using congr(aeval γ.1.1 (map k $hv)))] using star_aeval (R := 𝔸f E') γ.1.1
  let τ := (toPerm σ).subtypePermOfFintype fun q h ↦ hI.2 ((hI.1 h).imp
    (.map (toMulEquiv _ σ)) (.imp (by simp [smul_eq_map]) (hγ ▸ map_dvd (toMulEquiv _ σ) ·)))
  have C S [CommRing S] f := pairwise_primeFactors_isRelPrime (a := P).imp fun _ _ ↦
    (·.isCoprime.map (mapRingHom (S := S) f))
  have crt {S} [CommRing S] f := exists_forall_sub_mem_ideal
    (((C S f).subtype _).mono fun _ _ ↦ (isCoprime_span_singleton_iff ..).2)
  have := e.symm.dvd.trans (charpoly_dvd_charpoly_aeval_comp (T^[p] 1 - X *
    ((T^[p] 1).map conj).comp (v.map k)))
  choose hq hm hP using fun q ↦ (hI.1 (Subtype.prop q)).imp_left Fact.mk
  let θ (q : primeFactors P) := aeval (R := 𝔸f E') (root q.1 : 𝔸f (AdjoinRoot q.1))
  choose _ h₁ sur ker F hβ using fun q ↦ adjoinRoot_cm_presentation (hm q) 1 (fun φ x h ↦ mod_cast
    (spectrum_subset_unitary_of_mem_unitary (U_one_mem_unitaryGroup ((U.map φ) γ'))
      (mem_spectrum_of_isRoot_charpoly ((isRoot_of_mem_roots h).dvd
        ((charpoly_map ..).substr (map_dvd φ (hP q)))))).2) (refl (θ q)) (.refl k)
  choose d hd e₀ using fun q ↦ (hz.2 _ e).1 _ (leftMulMatrix (Module.finBasis ..) (θ q X))
    (by simp [aeval_algHom_apply, *, mk_eq_zero.2])
  simp [← cj (e ▸ aeval_self_charpoly _), aeval_algHom_apply, ← norm_eq_matrix_det, by simpa [←
    (by rw [iterate_mul_apply, map_one, mul_one]; with_unfolding_all rfl : T^[p] 1 =
    twistedNorm (.map (adeleMap σ)) p z)] using (hz.2 γ e).2, mem_span_singleton] at this crt e₀ h₁
  have hu q := lmul_isUnit_iff.1 ((LinearMap.isUnit_iff_isUnit_det _).2 ⟨_, e₀ q⟩)
  have hw q := left_inv_eq_right_inv (by simpa [hP, mk_eq_zero.2] using congr(mk q $hv)) (h₁ q)
  let g {q q'} (h : τ q = q') := mapAlgEquiv σ q q' (.of_eq (smul_eq_map E' σ ▸ congr($h)))
  have hT {q q'} h f : θ q' (T f) = θ q' z * adeleMap (@g q q' h) (θ q f) := by
    simp [θ, g, T, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
  choose y c₁ h₂ h₄ using fun q ↦ show ∃ y c, IsUnit (θ q c) ∧ IsSelfAdjoint
      (star (θ q c) * ((principalIdele y).1 * θ q (T^[period τ q] c))) by
    have i := isReduced_of_injective (RingHom.pi (evalAt (E :=
      AdjoinRoot q.1))) DFunLike.coe_injective
    cases' by simpa [← ker, *, map_X k ▸ F q X] using (map_dvd k (hP q)).trans this with N
    obtain f | rfl := (eq_or_ne (τ q) q).imp_right
      (minimalPeriod_eq_prime (by simp [τ, ← toPermHom_apply, ← map_pow, *] : (τ ^ p) q = _))
    have ⟨hg, hx⟩ : Semiconj (of q.1) σ (g f) ∧ g f (root _) = root _ := by simp [g, Semiconj]
    have := orderOf_eq_prime (coe_toAlgHom_injective (by ext <;> simp [iterate_fixed, ← coe_pow σ,
      ← hg.iterate_right p _, *]) : g f ^ p = 1) fun h ↦ hσ (ext (coe_injective' <| h ▸ hg ·))
    simpa [hT f, period_eq_one_iff.2, *, (sur _).exists, mul_assoc] using
      hμ.exists_selfAdjoint_of_norm hx
      adjoinRoot_eq_top (hu q).unit (.trans congr(μ $(by ext; simp [*])) (hd q))
      (by simpa [*, Semiconj.iterate_right (gb := (_ * adeleMap _ ·)) (hT f) p _] using! N)
    peel exists_star_principalIdele_mul_eq _ N using ⟨1, by simpa⟩
  let r q := @invFun _ _ ⟨q⟩ (periodicOrbit τ) (periodicOrbit τ q)
  choose e j J hr using by simpa [periodicOrbit] using (by simp [r, τ.injective.mem_periodicPts,
    invFun_eq, periodicOrbit_apply_eq] : ∀ q, r (τ q) = r q ∧ q ∈ periodicOrbit τ (r q))
  obtain ⟨⟨c, Y⟩, w, W⟩ := crt k fun q ↦ T^[j q] (c₁ (r q)),
    crt (.id _) fun q ↦ surjInv mk_surjective (y q ^ 0 ^ j q).1
  use w, c, fun x X γ h ↦ (crt k fun q ↦ surjInv (sur q) (θ q x)⁻¹ʳ).elim fun d hd ↦ ?_
  simp [← ker, ← mk_eq_mk, surjInv_eq] at W Y hd
  choose H G using @id (∀ q, IsUnit (θ q x) ∧ IsSelfAdjoint (star (θ q c) * θ q x))
      ((reindex_equiv τ).1.2 fun q ↦ by
    simp_rw [← X, map_mul, hT rfl, Y, ← hT, ← iterate_succ_apply', F, W]
    rw [iterate_injOn_Iio_minimalPeriod (J _) ((j q).succ.mod_lt (J _).pos)
      (by simp [↓iterate_succ', ↓← hr, e]), e, congrArg τ (hr q), ← iterate_succ_apply' τ]
    use .mul (.map _ ⟨_ ^ _, rfl⟩) ((j q).succ.rec (h₂ _) fun _ _ ↦ by simp [*, -hr, iterate_succ',
      -iterate_succ, IsUnit.map]), (Nat.eq_or_lt_of_le (J q)).elim (by
      rw [·, iterate_minimalPeriod]; simpa using! (h₄ _))
      (by simp [Nat.mod_eq_of_lt ·, -iterate_succ]))
  have K (f g : (𝔸f E')[X]) := by
    simpa [Subtype.forall', ← ker] using (aeval_eq_zero_of_dvd_aeval_eq_zero · h) ∘ (map_prod
      (mapRingHom k) ..).dvd.trans ∘ Finset.prod_dvd_of_coprime (C _ k) (z := f - g)
  use .of_mul_eq_one _ (by simpa [*, inverse] using K (x * d) 1), fun a b ↦ by rw [IsRootQuotient,
    cj, K _ (_ * (c * d)), map_mul, ← mul_assoc, ← cj, b, ← map_mul, mul_left_comm, K] <;> simp [*,
    -hr, -Y, K _ 0, ← mul_assoc, mul_inverse_cancel_right, (star_star_mul ..).symm.trans (G _)]

open WithZero Valued IsDedekindDomain HeightOneSpectrum FiniteMultiplicity Finset WeilData RingHom

attribute [local simp] prime of_prime_left differentIdeal_ne_bot im_pos

/-- If E carries Weil data, so does every stably unramified CM extension L with compatible CM
type such that no place v = v̄ of L divides the relative different. -/
lemma nonempty_weilData_of_unramified {E L : Type} [Field E] [CMType E] [Field L] [Algebra E L]
    [h : CMOver E L] [WeilData E] [StablyUnram L]
  (hu : ∀ v : FinPlace L, star v = v → ¬v.1 ∣ differentIdeal (𝓞 E) _) : Nonempty (WeilData L) := by
  obtain ⟨⟨_, -, -, g, -, _, H⟩, ⟨⟩, _⟩ :=
    @exists_reduction_and_idele_generator L _ _ (differentIdeal ℤ _) (by simp),
    exists_wellFoundedLT (FinPlace L), (by simpa [RingHom.ext_iff] using h.2 <| Φ ·)
  let i := algebraMap E L
  let s := principalIdele (.map i.1 (.mk0 j j_ne_zero)) * g
  have ⟨β, _⟩ := exists_idele_eq_uniformizer_zpow (fun u ↦
    (ite (u < star u) 1 0 - (v (s.1 u)).log) / 2) ((finite_idele_val_ne_one s).subset (by aesop))
  refine have : SplittingChar L := ⟨⟨υ.1.comp ⟨_, .units_map (.prodMap (.pi (∏ u with u.comap i = ·,
    Pi.evalMonoidHom _ u)) (adeleNorm ..)) (by simp [MonoidHom.pi]; and_intros <;> fun_prop)⟩,
    fun _ ⟨x, e⟩ ↦ υ.2 _ ⟨norm E x, ?_⟩⟩, fun _ _ ↦ by
    erw [υ_unit] <;> simp_all [prod_fiberwise, adeleNorm_mem_Ohat, Submonoid.mem_units_iff], fun _ ↦
    congr(υ.1 $(by bound)).trans (υ_star _)⟩; ⟨⟨i j, by simp [← map_star_CM], by aesop, β,
    fun u ↦ ?_, by simpa [map_ofNat] using map_isIntegral_int i isIntegral_traceOne,
      exists_eq_principalIdele_mul_norm.2.2⟩⟩
  ext w <;> simp [← e]
  algebraize [Φ w]
  erw [norm_eq_prod_embeddings]
  refine' prod_bij' (fun σ _ ↦ .mk σ) (fun u _ ↦ ⟨Φ u, _⟩) .. <;>
    simp [algebraMap_toAlgebra, i, ← (h.2 _).2] <;> aesop
  let w := FinPlace.below E u
  rcases valuation_star u (i j), self_dual w ▸ log_exp _, (H (star ↑g⁻¹)).1 (forall_ψf_mul_eq_one.1
    (by simp_all [↓ψf_star (_ * _), mem_Ô, forall_ψf_mul_eq_one.2 ∘ (H _).2])),
    self_dual w ▸ exp_ne_zero,
    differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 E) (𝓞 L) ▸ emultiplicity_mul u.prime
  rw [← exp_log (x := v _), exp_inj] <;> simp_all [s, i, ← w.valuation_liesOver L, mem_Ô,
    ← map_star_CM, v_inv, ← log_le_log, emultiplicity_eq_multiplicity, irreducible,
    emultiplicity_map_eq_ramificationIdx'_mul (v := w.1), ← eq_sub_iff_add_eq, ne_bot,
    w.1.ramificationIdx'_eq_ramificationIdx _ w.ne_bot]
  norm_cast at *
  grind [multiplicity_eq_zero_of_not_dvd, star_star, below_star,
    @congrArg _ _ (star w) w (v <| α.1 ·)]
end

section
/-! Known result: cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). Only existence is proved, for a lift from U(n) over E to U(n) over E' (not GL_n), with
E'/E tame and E containing enough roots of unity. Hecke polynomials match where the place splits
completely and an auxiliary character is trivial, tame types are kept, and class sums are compared
directly, without stabilisation. Source: J.-P. Labesse, Changement de base CM et séries discrètes,
in On the stabilization of the trace formula, 2011, Cor. 5.3, and Cohomologie, stabilisation et
changement de base, Astérisque 257, 1999; J. Arthur and L. Clozel, Simple algebras, base change, and
the advanced theory of the trace formula, Ann. Math. Studies 120, 1989; local matching after P.
Scholze, The Langlands-Kottwitz approach for some simple Shimura varieties, 2013, Prop. 2.1 (norms
inverted inside O[γ]) and J.-P. Labesse, Fonctions élémentaires et lemme fondamental pour le
changement de base stable, Duke Math. J. 61, 1990.

This file: Twisted trace over E' is proportional to trace over E for matching functions. Existence
of weak prime-degree base change for definite unitary groups with matched local data. Base change
keeps a pro-p Iwahori eigencharacter, composed with the norm. -/

open Module Filter Matrix Polynomial Space U Matrix.Module

variable {E E' n : Type} [Field E] [CMType E] [Field E'] [Algebra E E'] {μ : (𝔸f E)ˣ →* ℂˣ}
  [CMOver E E'] {E₁ E'' : Type} {n'} [Field E₁] [CMType E₁] [Field E''] [Algebra E₁ E'']
  [CMOver E₁ E''] [Fintype n']

open Function in
attribute [local implicit_reducible] stdSpace in
attribute [local simp] Function.Injective _root_.Gf.atPlace RingHom.comp mul_assoc in
/-- Twisted trace identity for a step E'/E: if norm-one elements of integral K are σ-coboundaries
and L ≤ K is open, σ-stable, there are c ≠ 0 and a σ-intertwiner t on base-changed forms with
tr(T't) = c tr T for operators of matching pairs (f, φ). -/
lemma twisted_trace_identity [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) [IsStep (E := E) E' μ] κ {K L}
    (hK : K ≤ Kf _ n) (hL : L ≤ K) (oL : L.IsOpen) (σL : L.comap (galoisGf σ) = L) (coh : ∀ s ∈ K,
  twistedNorm (galoisGf σ) (finrank E E') s = 1 → ∃ t ∈ K, galoisGf σ t = s⁻¹ * t) : ∃ c ≠ 0, ∃ t :
  End ℂ _, (∀ g ψ, t (formTranslation _ _ g ψ) = formTranslation _ _ (galoisGf σ g) (t ψ)) ∧ ∃ h,
  ∀ f φ, IsMatchingPair (adeleMap_star σ) (finrank E E') 1 (normKer _ μ) baseChangeGf K f φ →
  ∀ T T', IsOperatorOf ((stdSpace E n).formTranslation κ) (L.comap baseChangeGf) T f → IsOperatorOf
  ((stdSpace ..).formTranslation κ.baseChange) L T' φ → (T' * t.restrict h).trace ℂ _ =
  c * T.trace ℂ _ := by
  have w := exists_twisted_weightRep_trace (n := n) hσ κ
  extract_lets j ω ρ at w
  let e : U 1 →* Gf E' n := U.map (algebraMap E' _)
  have fσ g (h : galoisGf σ g = g) : ∃ k : Gf E n, _ ∧ baseChangeGf k = g :=
    mem_range_map _ (adeleMap_injective
    _) (by simp) _ (ext (adeleMap_galois_descent hσ congr($h.1.1 · ·) |>.choose_spec))
  have fτ g (h : ω g = g) : ∃ k, j k = g := (mem_range_map _ (by simp) (by simp) _
    (ext (galois_descent_prime hσ congr($h.1.1 · ·) |>.choose_spec))).imp (by tauto)
  let τ := by apply ω.toMulEquiv (mapEnd (map_star_CM ↑σ⁻¹)) <;> ext <;> simp [ω, U.map]
  let θ := by apply (galoisGf (n := n) σ).toMulEquiv (galoisGf σ⁻¹) <;> ext <;> simp [U.map] <;>
    erw [adeleMap_id]
  obtain ⟨⟨s, hs, w⟩, ij, X, ie, hτ, hj, fj, ι⟩ := w, (by simp +zetaDelta [baseChangeGf, U.map,
    DFunLike.ext_iff, Gf.val_ext_iff, Units.ext_iff, ← ext_iff] : Injective j ∧
    (stdSpace ..).embFin = e ∧ Injective e ∧ (∀ γ, e (ω γ) = galoisGf σ (e γ)) ∧ (∀ γ, e (j γ) =
    baseChangeGf ((stdSpace ..).embFin γ)) ∧
    (∀ γ, ω (j γ) = j γ) ∧ ∀ g : Gf E n, galoisGf σ (baseChangeGf g) = baseChangeGf g)
  obtain ⟨M, ⟨c, _, _, _, H⟩, d, _, t, R, H'⟩ := map_twistedNorm e hτ, isSampleTotal_twisted_trace _
    κ 1 continuous_id (fun _ ↦ baseChangeGf_mem_Kf.1 ∘ @hK _) (L.comap_mono hL)
    (continuous_baseChangeGf.1 _ oL) rfl 1 (by simp) 1 (by simp), (X ▸ isSampleTotal_twisted_trace
    (stdSpace ..) _ θ (continuous_map : Continuous (galoisGf σ⁻¹)) hK hL oL σL τ) hτ s hs
  refine ⟨d / c, by simp [*], _, by intros; ext; simp; erw [θ.left_inv'], R, fun f φ h _ _ a i ↦ ?_⟩
  field_simp
  have nc x δ := M _ δ ▸ @twistedNorm_conj _ _ _ (finrank E E') x (by exact Subtype.ext (
             adeleMap_pow_finrank_eq_one (σ := σ) ▸ (finrank ..).rec (by tauto) (by tauto) x : _ =
    x.1.map 1)) _
  let q (δ : U 1) := (δ.1 : GL n E').1.charpoly
  have cq δ : (e δ).1.1.charpoly = (q δ).map _ := charpoly_map ..
  let' C (P : E'[X]) := P.map (algebraMap _ (𝔸f E')) ∈ (_ : Set _) ∧ σ • P = P
  choose! z hz m using fun {P} (c : C P) ↦ h.2 _ (by exact c.1) (ext (by simpa using ext_iff.1 c.2))
  have fx {ν} δ (h : SemiconjBy δ (ω ν) ν) x a : C (q ν) := ⟨⟨x⁻¹ * e ν * x, a,
    by simpa [← cq] using! charpoly_units_conj x.1⁻¹ _⟩, by
    simpa [q, smul_eq_map, ← charpoly_map, ← mul_assoc] using! congr(q (δ⁻¹ * $h))⟩
  choose! _ _ W using fun P (⟨_, c, e⟩ : ∃ δ, C (q δ) ∧ δ.1.1.charpoly = P) ↦ e ▸
    exists_global_root (by simp [← IsGalois.card_aut_eq_finrank]) hσ c.2 (hz c) (cq _)
  choose W u _ V using fun {ν} h ↦ W (q ν) ⟨_, h, rfl⟩ _ ((mul_left_comm ..).trans (mul_comm ..))
    (e ν) (by erw [← map_aeval_matrix]; simp [q]) |> fun w ↦ And.intro w (by simpa using w.1)
  choose! A B hA hB uB using fun {ν} h ↦ exists_and_exists_comm.1 ⟨existsUnique_isRootQuotient
    (isUnit_of_mapMatrix _ ((aeval_algHom_apply (Algebra.ofId ..).mapMatrix ..).subst (@u ν h))),
    existsUnique_isRootQuotient (W h).1⟩
  have cj {ν ν'} g h (H : g * ν = ν' * g) := (by simp [q, ← mul_inv_eq_of_eq_mul H, -mul_assoc] :
    q ν = q ν') |> fun c ↦
    And.intro (c ▸ h) (And.intro ((hA (c ▸ h)).2 _ (c ▸ isRootQuotient_conj H.symm
    (hA h).1)).symm (uB (c ▸ h) _ (c ▸ isRootQuotient_conj (SemiconjBy.map H e).symm (hB h))).symm)
  have cm {ν} h := (cj ν h rfl).2.imp (Commute.inv_left ∘ mul_eq_of_eq_mul_inv) mul_eq_of_eq_mul_inv
  have Z {ν δ} h (hν : SemiconjBy δ (ω ν) ν) := have v := hτ ν ▸ (hν.map e).symm
    (existsUnique_isRootQuotient (V h)).elim (fun _ r _ ↦ eq_inv_mul_of_mul_eq (uB h (e _ * _ * _)
    (((isRootQuotient_map _ (hA h).1).mul (isRootQuotient_conj v
      (isRootQuotient_map _ ((W h).2 _ (hB h))))).mul r)) ▸ r) |> fun r ↦ And.intro (fun y ↦
      m h _ _ (by simp [cq, -mul_assoc]) (isRootQuotient_conj (mul_inv_cancel_right _
    y) ((one_smul ..).substr r))) ((M _ δ).trans ((IsRootQuotient.twistedNorm_eq_mul (by simpa using
      ((hz h).2 _ (cq ν)).2) v r (V h)).trans (congrArg _ (by simpa using nc _ (_ * δ)))))
  choose hz' nA using fun {γ} h ↦ (Z h ((fj γ).substr (cm h).1)).imp_right
    (@ie _ (j γ) <| ·.trans (by simp [twistedNorm]))
  refine (H a).mul_eq_of_double_count (B := U 1) (fun _ : _ × U 1 ↦
    φ (_ * galoisGf σ _) * (ρ _ * s).trace ℂ _) (H' i) (fun y ↦ ((@B (j y.2))⁻¹ * baseChangeGf y.1,
    (@A (j y.2))⁻¹)) (C <| q <| j ·.2) (fun x h ↦ fx 1 (by simp [fj]) (baseChangeGf x.1) (.inl ⟨_,
    left_ne_zero_of_mul h, by simp [hj]⟩)) (fun x c y g ⟨hk, b⟩ ↦
    congrArg₂ _ (.trans (by simp [← b, ι, hτ, τ]) ((h.1 _ hk _).trans ((hz' c ((@B (j
    x.2))⁻¹ * baseChangeGf x.1)).1 _ (by simp [← hj, (cm c).2]) (.trans (by simp
    [ι]) (nA c ▸ nc ..))).symm)) (by simp [τ, ← b, ← w _ _ (nA c), ← hs, (ρ g⁻¹).trace_mul_comm,
    s.trace_mul_comm, ← ρ.map_mul g])) fun (x, δ) ↦ (fun o ↦ ?_) ∘ left_ne_zero_of_mul
  let ν := twistedNorm ω (finrank E E') δ
  have v : δ * ω ν = ν * δ := ie (by
    simpa [ν, hτ, M, map_twistedNorm _ (congrFun rfl)] using congr(e δ * $(nc (e δ) δ)))
  have h := fx _ v x (.inr ⟨_, o, nc ..⟩)
  have l := @ie _ 1 (by simpa [inv_mul_eq_one] using left_eq_mul.1 (Z h v).2)
  choose k hk H using coh _ (((Z h v).1 _).2 _ (nc ..) o) (by simpa [l] using nc (_ * x) (@A ν * δ))
  obtain ⟨g, hg : ω _ = _⟩ := hasse_principle_coboundary hσ (@B ν * x * k) (by simp [H, e]) l
  obtain ⟨⟨y, -, ey⟩, γ, eγ⟩ := fσ (e g⁻¹ * @B ν * x * k) (by simp [← hτ, hg, H]),
    fτ (g⁻¹ * ν * g) (by simp [eq_inv_mul_of_mul_eq v, hg, ← (cm h).1.left_comm])
  use (y, γ), (g * j ·)⁻¹, (⟨fun a ⟨b, c⟩ ↦ (cj (g * j a)⁻¹ h (by simp [← c,
    eγ])).symm.imp_left (⟨by simpa [·, ey, hj] using inv_mem (mul_mem hk b), by simp [*, τ]⟩), by
    simp [ij.eq_iff], fun a ⟨⟨b, (c : _ * ω _ = δ)⟩, d⟩ ↦ have N : a⁻¹ * j ·.2 = ν * a⁻¹ := ie (by
    simp [ν, ← c, hτ, nc, M, nA d, -mul_assoc, -map_inv, e.map_inv a])
    (fτ (a * g)⁻¹ (by simp [hg, ← c, cj _ d N])).imp fun _ ha ↦ ⟨⟨by simpa [cj _ d N, ey, ← hj, ha]
      using (inv_mem (mul_mem b hk)), ij (by simp [ha, eγ, ← N])⟩, by simp [ha]⟩⟩)

/-- Weak base change: Z is finite and, for u above w ∉ Z ∪ Z̄, sphericity passes from f to f' at
`IsStepUnramifiedAt` places, and Hecke polynomials at split `IsMatched` places. -/
def IsWeakBaseChange [Fintype n] μ {M M'} Z (f : Gf E n → M → ℂ) (f' : Gf E' n → M' → ℂ) :=
  Set.Finite Z ∧ ∀ w ∉ Z.conjClosure, ∀ u, .below E u = w → (IsStepUnramifiedAt E' μ w →
  f ∈ sphericalAt (rightRegular ℂ ..) w → f' ∈ sphericalAt (rightRegular ℂ ..)
  u) ∧ (IsMatched E' μ w → ∀ hw P, HasHeckePolyAt f w hw P → ∃ hu, HasHeckePolyAt f' u hu P)

/-- Matching local data above a finite set Z: retracts G, G' of the adelic groups, compatible
levels L, L', and bi-invariant functions F_j, F'_j that form pairs for j ∈ P at a level
where σ-cocycles split. -/
def IsLocalMatching μ Z {G G' J} [Group G] [Group G'] a a' L L' P (F : J → G → ℂ) (F' : J → G' →
  ℂ) := ∃ σ ≠ (1 : Gal(E''/E₁)), ∃ r r', ((∀ j, IsBiInvariant L (F j) ∧ IsBiInvariant L' (F' j)) ∧
  IsLocalRetraction a r Z ∧ IsLocalRetraction a' r' (placesAbove _ Z) ∧ Z.Finite ∧ ∀ k, r' (galoisGf
  σ k) ∈ L' ↔ r' k ∈ L') ∧ let M := L'.comap r'; M.comap baseChangeGf = L.comap r ∧ M.IsOpen ∧
    ∃ K ∈ Set.Icc M (localLevel n' (placesAbove _ Z)), CocyclesSplit (finrank E₁ E'') (idem
    (placesAbove _ Z)) K (galoisGf σ) ∧ P ⊆ {j | IsMatchingPairAbove σ μ Z K (F j ∘ r) (F' j ∘ r')}

variable [hμ : IsStep (E := E) E' μ] {u : FinPlace E'} {hw : (u.below E).IsSplit} (hu : u.IsSplit)

/-- For a step (E'/E, μ), the constant functions 1 on trivial local groups are matching local
data (`IsLocalMatching`) above the empty set of places. -/
lemma isLocalMatching_empty : IsLocalMatching (G := Unit) μ ∅ 1 (1 :
  Unit →* Gf E' n') ⊤ ⊤ {()} 1 1 := hμ.exists_gal_ne_one.imp fun _ ↦
  (⟨·, 1, 1, by simp [IsLocalRetraction, Gf.trivialOn, placesAbove, IsBiInvariant, Set.toFinite,
  localLevel, CocyclesSplit, IsMatchingPair, IsNormRoot, IsRootQuotient, twistedNorm_map_eq_prod,
  isOpen_iff_eventually, show idem ∅ = (0 : 𝔸f E') by aesop]; rfl⟩)

/-- Base change along a step: given matching local data with commuting operators A_j, A'_j, P stable
under the A_{o(i)}, and A_{j₀} of nonzero trace on stable spaces through f of generalised
eigenvalues θ, some weak base change eigenform in the image of A'_{j₀} has eigenvalues θ.

Known result: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). -/
lemma exists_isWeakBaseChange_of_matching [Fintype n] {μ} [hμ : IsStep (E := E) E' μ] [StablyUnram
  E'] {κ} f {Z G G'} [Group G] [Group G'] {a : G →* _} {a' : G' →* _} {L L'} {ι J : Type} {P F F'}
  (hM : IsLocalMatching μ Z a a' L L' P F F') (o : ι → J) (θ : ι → ℂ) j₀ (h₀ : j₀ ∈ P)
  : let ρ := ((stdSpace ..).formTranslation κ).comp a; let ρ' :=
      ((stdSpace E' n).formTranslation κ.baseChange).comp a'
    let A j := heckeFun ρ L (F j); let A' j := heckeFun ρ' L' (F' j); let V := levelSpace ρ L
        let V' := levelSpace ρ' L'; (∀ i j, (∀ x ∈ V, A i (A j x) = A j (A i x)) ∧ ∀ x ∈ V',
          A' i (A' j x) = A' j (A' i x)) → (∀ i, ∀ j ∈ P, ∃ k ∈ P, (∀ x ∈ V, A (o i) (A j x) =
          A k x) ∧ ∀ x ∈ V', A' (o i) (A' j x) = A' k x) → (∀ W : Subrepresentation ρ,
          f ∈ W → let U := (V ⊓ ⨅ i, (A (o i)).maxGenEigenspace (θ i)) ⊓ W.1; Module.Finite ℂ U →
            ∀ h, ((A j₀).restrict h).trace ℂ U ≠ 0) → ∃ g H, IsEigenform g.1 H ∧
          IsWeakBaseChange μ Z f.1 g.1 ∧ g ∈ V' ∧ g ∈ V'.map (A' j₀) ∧ ∀ i, A' (o i) g = θ i • g :=
  hM.elim fun σ ⟨hσ, r, r', ⟨hF, ha, ha', hZ, _⟩, hL, O, K, ⟨MK, KZ⟩, coh, Q⟩ c M pos ↦ by
  choose m mK l n₄ un using exists_baseChange_level hσ f.2.1
  let B w := w ∉ Z.conjClosure ∧ ∀ u ∈ placesAbove _ {w}, m u = Kw ..
  let X := {w | B w ∧ w.IsSplit ∧ IsMatched E' μ w}
  let N := localLevel n (placesAbove _ Z)ᶜ m
  let 𝓛 := L'.comap r' ⊓ N
  have kK : K ⊓ N ≤ _ := fun g h ↦ mem_Kf_iff.2 fun u ↦ by_cases (KZ h.1 u) (mK u <| h.2 u ·)
  obtain ⟨LK, oM⟩ := inf_le_inf_right N MK, ha'.2.2 ▸ L'.ker_le_comap r'
  let X' := {u // u.IsSplit ∧ u ∉ placesAbove _ Z ∧ maxCompactAt n u ≤ 𝓛}
  have kv {w S} (h : B w) (s : S ⊆ placesAbove E' {w} := by simp [placesAbove]) :
    Kf .. ⊓ Gf.supportedOn n S ≤ 𝓛 := fun g k ↦ .imp (oM ·) mem_localLevel.2 (by
    clear * - h k s; simp_all; grind [mem_Kf_iff, placesAbove, star_star, one_mem, below_star])
  let j u (e : _ ∈ X) : X' := ⟨u, ne_of_apply_ne _ ((below_star u).trans_ne e.2.1), e.1.1, kv e.1⟩
  choose Y y oX eZ _ eL using exists_remaining_places (S := Z) (T := X) (by grind) (·.2.1.2)
  choose n₀ _ n₂ _ using l _ N (by rw [eZ])
  have oL : 𝓛.IsOpen := O.inter n₀
  obtain ⟨oZ, _, _, T, -, hT⟩ := (Gf.supportedOn_le_trivialOn (S :=
    placesAbove _ Z) (by simp)).trans (eL ▸ trivialOn_le_localLevel), (stdSpace
    ..).finite_formTranslation_levelSpace κ (K := 𝓛.comap _) (continuous_baseChangeGf.1 _ oL),
    (stdSpace ..).finite_formTranslation_levelSpace κ.baseChange oL, exists_inf_trivialOn_le oL
  choose e₁ w st cm R r₀ r₁ r₂ r₃ using exists_commuting_hecke_family a r (𝓛.comap _) (fun _ h ↦
    baseChangeGf_mem_Kf.1 (kK (LK h))) (hF · |>.1) (·.2.2.1) (fun x : X ↦
    ⟨x.2.1.1, fun _ h ↦ kv x.2.1 .rfl (h.imp baseChangeGf_mem_Kf.2 baseChangeGf_mem_supportedOn)⟩)
    ha congr($hL ⊓ $((congrArg _ eL).trans (Subgroup.comap_inf ..))) (oZ <|
    baseChangeGf_mem_supportedOn <| ha.1 ·) (c · · |>.1)
  choose e₂ _ _ cm' R' u₀ u₁ u₂ u₃ using exists_commuting_hecke_family _ _ 𝓛 (LK.trans kK)
    (hF · |>.2) (X := X') (·.2.1) (by simp [X']) ha' (eL ▸ rfl) (oZ <| ha'.1 ·) (c · · |>.2)
  choose z z₀ t₀ htw tw tr using
    twisted_trace_identity hσ κ kK LK oL (by ext; simp [*]) fun s h e ↦ by
    obtain ⟨⟨t, a, c, H⟩, r, b, d, I⟩ := coh s h.1 e, n₂ s h.2 e
    simp [eZ, ↓← idem_compl, ↓idem_smul_eq_iff_mem_trivialOn, mul_assoc, inv_mul_eq_one] at c d H I
    use t * r, mul_mem ⟨a, trivialOn_le_localLevel (by simpa)⟩ ⟨MK (oM (by simpa)), b⟩
    ext1 w
    by_cases w ∈ placesAbove _ Z <;> simp [*, atPlace_galoisGf σ _ rfl, show w.comap σ ∈ placesAbove
      E' Z ↔ w ∈ placesAbove _ Z by simp [placesAbove]]
  choose D s₁ s₂ U hU s₃ using exists_hecke_stable_matching (n := n) (S := X) hσ fun _ ↦ .right
  choose Θ f' v t₁ t₂ t₅ t₃ t₄ using exists_eigenvector_of_trace_identity st rfl (.map o fun y : Σ'
    y : X × _, Σ' c, f ∈ End.eigenspace (heckeSplit _ y.1.2.2.1 y.2) c ↦ y.1) (.map o fun y ↦
    (j _ (hU _ ▸ y.1.1.2), y.1.2)) (.inl j₀) _ (Sum.elim θ _) cm cm'
    (by rw [e₁, iInf_sum, inf_inf_inf_comm]; exact (pos ⟨_ ⊓ _, fun k x h ↦
    ⟨(w k).1 _ h.1, (Submodule.mem_iInf _).2 (End.mapsTo_maxGenEigenspace_of_comm ((w k).2 _) _ <|
    (Submodule.mem_iInf _).1 h.2 ·)⟩⟩ ⟨fun g ↦ by simpa [Subtype.ext_iff] using! _root_.funext (n₄
    fun u _ ↦ by_cases (by simp +contextual [placesAbove, or_imp, atPlace_baseChangeGf,
    Gf.mem_trivialOn.1 g.2.1, Gf.atPlace_star_eq_one_iff.1]) (g.2.2.2 u)), (Submodule.mem_iInf
    _).2 (End.eigenspace_le_maxGenEigenspace ·.2.2)⟩ (Submodule.finiteDimensional_of_le
    (e₁.trans_ge fun _ ↦ .imp (·.1) (·.1))))) z₀ {t | ∃ᵉ (k ∈ P) (x ∈ D), R k t.1 x.1 ∧
    R' k t.2 x.2} ⟨_, h₀, _, s₁, r₀ _, u₀ _⟩ (by rintro _ ⟨k, p, x, i, e, d⟩; exact ⟨tr _ _
    (by convert (Q p).mul ((s₂ x i).mul (l Y _ rfl).2.2.2 ..) .. <;> simp [*, star_idem,
    idem_mul_self, Set.preimage, mul_sub, sub_mul]; rfl) _ _ (r₁ _ e) (u₁ _ d),
    Sum.forall.2 ⟨(M · k p |>.imp fun _ ⟨a, b, c⟩ ↦ ⟨a, x, i, r₂ _ e b, u₂ _ d c⟩), fun y ↦
    ⟨k, p, _, s₃ _ x i .., r₃ _ e _ fun _ h ↦ oX (baseChangeGf_mem_supportedOn (Gf.supportedOn_mono
    (by simp) h)), u₃ _ d _ (oX.trans' (by simp [Gf.supportedOn_mono, placesAbove, j, *]))⟩⟩⟩)
  have eig (x : X') := (hasHeckePolyAt_iff x.2.1).2 ⟨levelSpace_anti x.2.2.2 f'.2, _, rfl,
    (congr($(t₄ <| .inr ⟨x, ·⟩)))⟩
  choose! H hH using (Exists.intro _ <| eig ⟨·, ·⟩)
  use f', H, ⟨by simpa, .mp (tendsto_place_comap_cofinite _ hZ.cj.compl_mem_cofinite)
    ((T.eventually_all.2 (by simp [↓eventually_and])).mono fun u b a p ↦ ⟨_,
    hH u ⟨isSplit_of_q_prime p, a, (inf_le_inf_left _ (Gf.supportedOn_le_trivialOn b)).trans hT⟩⟩)⟩,
    ⟨hZ, ?_⟩, (e₂.le f'.2).1, ⟨_, (e₂.le
    v.2).1, t₅ ▸ rfl⟩, fun i ↦ congr($(t₄ _).1).trans congr($t₂ (.inl i) • _)
  rintro _ a u rfl; use fun b
    c ↦ by simpa [Subtype.ext_iff, -Gf.mem_supportedOn] using! levelSpace_anti (kv ⟨a,
    un _ b (by simpa [LE.le, funext_iff] using c)⟩) f'.2
  simp_rw [hasHeckePolyAt_iff (f := f)]; rintro b hw _ ⟨c, t, rfl, ht⟩
  let x : X := ⟨_, ⟨a, un _ (fun u e ↦ ⟨⟨_, notMem_inertia_of_comap_ne ((b.2 u e).2 σ hσ)⟩,
    fun _ _ ↦ (e ▸ b).1 _⟩) (by simpa [Subtype.ext_iff, funext_iff, LE.le] using! c)⟩, hw, b⟩
  let P u := ∀ e i, Θ (.inr (j u e, i)) = t i
  have h u (a : P u) : P (u.comap σ) := fun e i ↦ .trans (t₁ _ _ (let := σ.toAlgHom.toAlgebra
    by ext ψ : 2; exact (map_heckeSplit _ _ t₀ fun _ _ ↦
      htw ..).trans (heckeSplit_comp_baseChangeGf _ _ (fun y ↦ ⟨adeleMap ↑σ⁻¹ (singleAdele u y)
      _, by erw [← adeleMap_apply, adeleMap_adeleMap, σ.toRingEquiv.comp_symm]; simp⟩)
      (levelSpace_anti (kv e.1) (tw _ ψ.2)) fun k h ↦ by simp [Gf.eq_of_supportedOn h (one_mem _)
      fun v ⟨a, b⟩ ↦ b.elim (v.ext (Ideal.comap_injective_of_surjective _ (MulAction.surjective σ)
      congr($a.1)))]))) (a (below_comap σ u ▸ e) i)
  exact ⟨_, (b.2 u rfl).1 ▸ _root_.funext ((((bijective_pow_gal hσ).2.exists.1
    (FinPlace.exists_gal_comap_eq (hU x))).rec fun i ↦ (· ▸ i.1.rec (fun _ i ↦ congr($t₂
    (.inr ⟨(x, i), _, End.mem_eigenspace_iff.2 (ht _)⟩))) fun _ ↦ h _) : P u) x.2) ▸ eig _⟩

open Finset Valued

/-- For a step (E'/E, μ), u split, the only place above a split w, and μ_w trivial: the
indicators of the pro-p Iwahori double cosets of N(t) at w and t at u are matching local
data (`IsLocalMatching`), paired for t strictly dominant. -/
lemma isLocalMatching_proIwahori (h : ∀ u', .below E u' = u.below E ↔ u' = u) (hD : ∀ x,
  μ (locIdele (u.below E) x) = 1) : IsLocalMatching (n' := n') μ {u.below E} (embedAtSplit hw)
  (embedAtSplit hu) proIwahori proIwahori {t : dominantTorus | StrictMono (v <| t.1
  · |>.1)} (fun t ↦ (iwahoriDoubleCoset (localNorm E u ∘ t)).indicator 1) fun t ↦
  (iwahoriDoubleCoset t.1).indicator 1 := by
  let ε := Fintype.equivFin n'
  obtain ⟨Q, τ, hτ⟩ := isLocalRetraction_atSplit n' h hu hw, hμ.exists_gal_ne_one
  obtain ⟨hs, C, -, T⟩ := (h _).1 (below_comap τ u), exists_isTameAtLevel_intAdeleMap hτ
  obtain ⟨⟨c, _, hc⟩, hv, l⟩ := (T 0 (by simp) (by simp)).2.1,
    v_locMap_eq_of_surjective _ hs τ.surjective,
    (@Function.Semiconj.iterate_right (𝔸f E') _ (· u) _ _ (adeleMap_apply _ hs) · |>.eq)
  have hσ x := by simpa using
    (l ..).symm.trans congr($adeleMap_pow_finrank_eq_one (singleAdele u x) u)
  set ρ := (reindexGL ε).toMonoidHom.comp (Gf.atPlace u); have tw δ : ρ _ = (ρ δ).map (locMap _
    hs) := congr(reindexGL ε $(atPlace_galoisGf ..)); have tn := (map_twistedNorm _
    tw · · |>.symm); have cp g : (ρ g).1.charpoly = _ := (charpoly_reindex ..).trans
    (charpoly_map ..); refine have R := (by simp_all [IsLocalRetraction, ρ, ε, IsBiInvariant,
      isBiInvariant_doubleCoset, isOpen_proIwahori, map_mem_proIwahori_iff_of_isometry]); ⟨τ, hτ,
      (reindexGL ε).toMonoidHom.comp (Gf.atPlace _), ρ, R, SetLike.ext fun _ ↦
      .symm (map_mem_proIwahori_iff_of_isEquiv (isEquiv_comap_locMap _ _)).symm,
      isOpen_proIwahori.preimage (.comp (.units_map _ (by simp; fun_prop)) (by fun_prop)), _,
      ⟨le_rfl, fun _ h ↦ by simpa [Q, mem_intGL, reindex_equiv ε.symm, ρ] using h.1⟩, fun δ s e ↦
      (exists_coboundary_proIwahori hv (RingHom.ext hσ) (mem_Ô.1 c.2 _)
      (by simpa [l] using congr(evalAt u ($hc + 1))) s (by simp_all)).imp' (embedAtSplit hu)
      (by clear * - R tw; simp_all [← idem_compl, ↓idem_smul_eq_iff_mem_trivialOn,
      IsLocalRetraction, ← R.2.2.1.2.2, mul_assoc]),
      fun t ht ↦ ⟨by simp_all, fun | _, ⟨g, c, rfl⟩, _ => ((map_surjective (evalAt u) (⟨singleAdele
      u ·, by simp⟩)).exists.1 (proIwahori_doubleCoset_match hv (RingHom.ext hσ) hμ.out.pos
      (by fun_prop) (fun x e ↦ (adeleMap_galois_descent hτ (x := singleAdele u x)
      (by ext1 o; obtain rfl | _ := em (o = u) <;> simp [*, ← (h _).ne, adeleMap_apply])).imp' (· _)
      (by simp_all [← adeleMap_apply])) (isEquiv_comap_locMap _ rfl) (fun x b ↦ let n' : Ô E' :=
        ⟨singleAdele u _, by simpa +contextual [mem_Ô, ← and_forall_ne u] using b.le⟩
      have hm : ∀ o, reduceAt o n' = 0 := by simp +contextual [b, n', ← and_forall_ne u]
      have t := T n' (Subtype.ext (mem_range_finAdeleIncl_iff.1 ⟨singleAdele _ (x - 1), by
        simp +contextual [DFunLike.ext_iff, ← and_forall_ne u, n', h, adeleMap_apply]⟩ τ))
        (by tauto)
      (t.exists_norm (.inr isProfiniteRing_intAdeles) (x := 1 + n') (by simp [v.map_one_add_of_lt,
        ← reduceAt_eq_zero, hm]) (by simp [t.1]) (by simp)).elim fun z ⟨d, _, hb⟩ ↦ ⟨z.map
        ((evalAt u).domRestrict _).1, by simpa [hm, -map_sub] using map_dvd (reduceAt u) d, by
        simpa [l, n'] using congr(evalAt u $hb)⟩) ht
      (by simp_all [StrictMono, ← toNormedField.norm_lt_iff]) ?_ _ ⟨ρ g, c.imp (fun ⟨_, a, b⟩ ↦ ⟨_,
      Set.mem_of_indicator_ne_zero a, b ▸ rfl⟩) (.imp' ρ (by simp_all)), cp g⟩)).elim fun y ⟨Z, B⟩ ↦
      ⟨1 + idem {u} • (y - 1), (hμ.isNormRoot_of_one_side rfl (by simpa) (by simpa) (by simp_all)
      (by simp [h, twistedNorm_map_eq_prod,
      Polynomial.map_prod] at Z ⊢; convert Z; ext; simp [l])).imp_right fun H γ a b c ↦ (B _ (ρ a)
      (b ▸ cp _) (.trans (congrArg (reindexAlgEquiv (LocField u) _ ε) (by simp [H _ a c]))
      (aeval_algHom_apply (reindexAlgEquiv (LocField u) _ ε) ..).symm)).imp
      (fun B g i k ↦ by exact if_congr (B _ (i ▸ rfl) (by simp [*])) rfl rfl) (by simp_all)⟩⟩⟩
  ext1; simp; intro; erw [← adeleMap_apply, finAdeleIncl_adeleNorm, map_prod (evalAt _), prod_range,
    ← (bijective_pow_gal hτ).prod_comp]; simp [← adeleMap_gal_pow, l]

attribute [-simp] MonoidHom.coe_comp exists_const mem_levelSpace

/-- Base change along a step E'/E with compatible CM types, at a split w with μ_w = 1 and one
split place u above: if f has eigencharacter ξ at w, some eigenform f' over E' matches f off
w (`IsWeakBaseChange`) with eigencharacter ξ∘Nm at u.

Known result: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching). -/
lemma exists_baseChange_isIwahoriEigen (h : ∀ u', .below E u' = u.below E ↔ u' = u)
    (hD : ∀ x, μ (locIdele (u.below E) x) = 1) {m} [Fintype m] [StablyUnram E'] {κ f θ}
    (H : IsIwahoriEigen (localFormRep (stdSpace E m) κ hw) (torusChar θ) f) : ∃ f' :
  (stdSpace ..).forms κ.baseChange, ∃ P, IsEigenform f'.1 P ∧
  IsWeakBaseChange μ {u.below E} f.1 f'.1 ∧ IsIwahoriEigen (localFormRep _ _ hu) (torusChar fun i ↦
  (θ i).comp (localNorm E u)) f' := have ⟨_, s, _⟩ :=
    exists_iwahoriHeckeHom_injective (localFormRep (stdSpace _ m) κ.baseChange hu) (v_uniformizer u)
  by refine have dN n (t : Fin n → _) : localNorm E u ∘ t ∈ dominantTorus ↔ t ∈ dominantTorus :=
      (by simp [dominantTorus, Monotone, ←
      toNormedField.norm_le_iff]); have M a t := (by constructor <;> intros <;> simp only [*,
        SetLike.coe_mem, hecke_dominant_eq_iwahoriDegree_smul, map_smul, compactMean_mem_levelSpace,
        iwahori_operator_mul (ρ := localFormRep ..), smul_smul] <;> simp
        <;> ring_nf); (exists_isWeakBaseChange_of_matching f (isLocalMatching_proIwahori hu h hD)
        (·) (fun a ↦ iwahoriDegree a.1 * torusChar θ (localNorm E u ∘ a)) ⟨_, s.monotone⟩ s (by
        simp +contextual [M, mul_comm, -hecke_dominant_eq_iwahoriDegree_smul]) (fun a t ht ↦ ⟨a *
        t, by simpa using! a.2.mul_strictMono ht (by simp [zero_lt_iff]) (by simp), M a t⟩) fun _ y
        _ ↦ trace_restrict_ne_zero (by simp [prod_ne_zero_iff]) (H.1 <| ·.le
        ⟨⟨H.2.1, by simpa using fun a h ↦ ⟨1, by simp [*, H.2, mul_smul]⟩⟩, y⟩) fun _ h ↦
        (Submodule.mem_iInf _).1 h.1.2 _).imp fun _ ⟨_, e, o, k, _, L⟩ ↦
        ⟨_, e, o, ne_of_apply_ne _ e.1, k, by simpa [*, mul_smul, prod_eq_zero_iff, torusChar,
        Pi.monoidHomMulEquiv, MonoidHom.comp_apply, coe_normAbsChar_locField] using L⟩
end
