import Lib.GaloisRep.CMNorms

-- part: Lib.Adelic.Landherr.SumOfTwoSquares
section
/-! Part of: Landherr's Hasse principle for hermitian forms; weak approximation for unitary groups
(known result; see Lib.Adelic.Landherr.Landherr).

This file: A totally positive element is a sum of two squares in a quadratic algebra, via
Hasse's norm theorem. -/

open Algebra QuadraticAlgebra Set NumberField

/-- Let E satisfy `StablyUnram`, S be a set of finite places of E, and p, q, B ∈ E⁺, p ≠ 0 totally
positive, p a unit outside S, q a unit on S ∪ S̄. Then p = x² + y² is solvable in E⁺[X]/(X²
− (qp − B²)). -/
lemma exists_sq_add_sq_quadraticAlgebra {E} [Field.{0} E] [CMType E] [StablyUnram E] (p q B :
  maximalRealSubfield E) {S : Set (FinPlace E)} (t : IsTotallyPositive p) (a : ∀ w ∉ S,
  w.valuation E p = 1) (c : ∀ w ∈ S.conjClosure, w.valuation E q =
  1) : ∃ z : QuadraticAlgebra (QuadraticAlgebra _ (q * p - B ^ 2) 0) (-1) 0, z.norm = ⟨p, 0⟩ := by
  set μ := _ - B ^ 2
  have H {M} [Field M] [NumberField M] (i : _ →+* M) m (h : m * m = i μ) :
      ∃ z : QuadraticAlgebra M (-1) 0, z.norm = i p := ?_ <;> by_contra k
  let := @instField _ _ μ 0 ⟨fun r e ↦ have ⟨⟨x, y⟩, _⟩ := H 1 r (by simp_all [sq])
    k ⟨⟨.C x, .C y⟩, by ext <;> simp_all [norm_def]⟩⟩
  exact k (@H _ _ (.of_module_finite (type_of% p) _) (algebraMap ..) _ omega_mul_omega_eq_mk)
  let := @instField M _ (-1) 0 ⟨fun r e ↦ k ⟨⟨i p + 4⁻¹, (i p - 4⁻¹) / r⟩, by grind [norm_def]⟩⟩
  have := IsQuadraticExtension.mk (finrank_eq_two (-1 : M) 0)
  have n z : norm M z = _ := @det_toLinearMap_eq_norm M _ (-1) 0 z
  refine (@hasse_norm _ _ _ _ _ _ _ (of_module_finite M _) _ (.mk0 _ (k ⟨0, by simp [·]⟩))
    (fun w ↦ ?_) (t <| ·.comp i)).elim (k ⟨·.1, n _ ▸ congr($(·).1)⟩)
  obtain ⟨⟨I, _⟩, ⟨u, o⟩, y, e⟩ := ‹StablyUnram E›.exists_i_c₀, (w.comap i).comap_surjective
    (algebraMap _ E), exists_norm_eq_Ô (u := ((q⁻¹ - p) * idem S.conjClosure + p :))
    (by simp [mem_maximalRealSubfield_iff_star_eq.1]) (by aesop (add simp idem_apply))
  let T x := trace (type_of% p) E (x / 2)
  let z := ite (u ∈ S.conjClosure) (@mk M (-1) 0 (i B) m) 1
  exact mem_of_eq_of_mem (by simp [← map_mul]; by_cases q = 0 <;> split <;> simp_all [z, μ,
    norm_def, field]) (map_mem_closure ((continuous_locMap i rfl).const_mul (algebraMap M _ z.norm))
    (((locMap _ o).injective (by split <;> simp [*, -map_inv₀, ← adeleMap_apply,
    finAdeleIncl_adeleNorm_eq_mul_star] <;> rfl) : adeleNorm _ E (star y) _ =
    algebraMap _ _ (ite (u ∈ S.conjClosure) q⁻¹ p)) ▸ adeleNorm_mem_closure) (by
    rintro _ ⟨x, rfl⟩; use z * ⟨i (T x), i (T (x * I))⟩; simp [n, norm_def, show norm _ x = T x ^ 2
   + T (x * I) ^ 2 by ext; simp_all [T, trace_maximalReal_eq_add_star,
      norm_maximalRealSubfield_eq_mul_star, RingOfIntegers.ext_iff]; grind]; ring))
end

-- part: Lib.Adelic.Landherr.Landherr
section
/-! Known result: Landherr's Hasse principle for hermitian forms, and weak approximation for unitary
groups. The form here covers only adelically unimodular spaces of equal signature over a CM field
containing the roots of unity of order 5040. It is proved from Hasse's norm theorem instead of
Hasse-Minkowski, and approximation uses a Cayley transform with a norm-one scalar. Source: W.
Landherr, Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper, Abh. Math.
Sem. Hamburg 11 (1936) 245-248; M. Kneser, Lectures on Galois cohomology of classical groups, TIFR
47 (1969), §5.5. -/


open NumberField Matrix Complex Set Function MatMul
variable {E n s} [Field.{0} E] [CMType E] [Fintype n] [StablyUnram E] (V W : Space E n s)
attribute [local simp] map_smul' smul_smul sum_single_eq_diagonal Pi.isUnit_iff Matrix.map_sub
  Subtype.ext_iff funext_iff QuadraticAlgebra.norm_def

omit [StablyUnram E] in
/-- For every adele σ (as a 1×1 matrix) there is an adele a with the
same norm as b = 1 + σa: āa = b̄b. -/
lemma exists_norm_eq_norm_one_add_mul (σ : Matrix Unit Unit (𝔸 E)) : ∃ a b, 1 + σ * a = b ∧ aᴴ * a =
  bᴴ * b := by
  let x := (σ () ()).2
  obtain ⟨⟨t, _⟩, e, _, ⟨p, _⟩, _, q, _⟩ := (@isUnit_natCast_finAdele E _
    _ 2 nofun).exists_left_inv, by simpa using isValuationPair_Ohat (1 + x) (x * (1 - x))
  let f c d := scalar Unit (update (1 - id)⁻¹ 1 c ∘ (σ () ()).1, t * ((2 - x) * p - q) * d)
  use f (-2⁻¹) (x * e + star e - 1), f 2⁻¹ (x * star e + 1 - e)
  simp [f, update, ← ext_iff, Prod.ext_iff]; grind [star_mul]

/-- Hasse principle for representing 1: over a stably unramified CM field E (`StablyUnram`), if a
hermitian matrix J over E has an adelic vector z with zᴴJz = 1, it has a vector v over E
with vᴴJv = 1. -/
lemma exists_form_eq_one (K : Matrix n n E) (j : Kᴴ = K) (z : Matrix n Unit (𝔸 E))
    (k : zᴴ * K.map toAdele * z = 1) : ∃ w : Matrix n Unit E, wᴴ * K * w = 1 := by
  let N (u : Matrix n _ E) :=
    Subtype.mk ((uᴴ * (K * u)) () ()) (mem_maximalRealSubfield_iff_star_eq.2 (star_form j ..))
  have A {T} (f : Set.Finite T) := (denseRange_rat_matrix_add f.cj.infinite_compl.nonempty
    1).exists_mem_open (((isOpen_set_pi finite_univ fun _ _ ↦ isOpen_re_gt 0).prod
    (f.cj.isOpen_biInter fun w _ ↦ (Valued.isOpen_sphere _ one_ne_zero).preimage (continuous_evalAt
    w))).preimage_of_continuous (f := fun x ↦ (xᴴ * K.map toAdele * x) () ())) ⟨z, by aesop⟩
  simp_all [conjClosure, star_idem, union_comm, -compl_union, -mem_union, ← Matrix.map_mul]
  choose u a using A finite_empty
  have o : (N u).1 ≠ 0 := by aesop
  choose v b c using A (finite_idele_val_ne_one (principalIdele (.mk0 _ o)))
  let B := (N (u + v) - N u - N v) / (1 + 1)
  obtain ⟨⟨i, _⟩, ⟨⟨p, r⟩, q, s⟩, h⟩ := ‹StablyUnram E›.exists_i_c₀,
    exists_sq_add_sq_quadraticAlgebra _ (N v) B (ofRealHom.comp · |>
    bijective_cmType_restrict.2 |>.elim fun w e ↦ (a.1 w).trans_eq congr(($e (N u)).re)) (by simp) c
  use ((p + q * i - (r * i - s) * B : E) / N u) • u + (r * i - s : E) • v
  simp [mem_maximalRealSubfield_iff_star_eq.1, ← ext_iff]
  simp_all +zetaDelta [RingOfIntegers.ext_iff, QuadraticAlgebra.ext_iff]; grind

attribute [local simp ←] Int.cast_mul

/-- Let E be stably unramified (`StablyUnram`), J hermitian over E, s signs, t a set of indices, D
= ∑_{i∈t} s_i E_ii. If XᴴJX = D for a square adelic matrix X, then AᴴJA = D for a square
matrix A over E. -/
lemma exists_rat_frame_of_adelic t : ∀ ⦃J X : Matrix n n _⦄, Jᴴ = J ∧ Xᴴ * J.map toAdele * X =
  ∑ i ∈ t, .single i i (s i : 𝔸 E) → ∃ A, Aᴴ * J * A = ∑ i ∈ t, .single i i (s i) :=
  t.induction (fun _ _ _ ↦ ⟨0, by simp⟩) fun j t l I J X ⟨H, h⟩ ↦ by
  let c : E := s j
  let u := Matrix.single j () (toAdele c)
  have k := by simpa +contextual [Matrix.sum_mul, Finset.sum_eq_single j, u] using congr($h * u)
  have ⟨w, W⟩ := exists_form_eq_one (c • J) (by aesop) (X * u) (by aesop)
  let y := (wᴴ * J).map toAdele * X
  let r := y * (1 + -u * uᴴ)
  let ⟨a, _, rfl, e⟩ := exists_norm_eq_norm_one_add_mul (y * u)
  let ρ := a * r + -uᴴ
  have ⟨A, a⟩ := @I (J - c • J * w * wᴴ * J) (X * (1 + u * ρ)) ⟨by aesop, by
    linear_combination (norm := (simp +zetaDelta [H, l, (by aesop : ∀ (x : 𝔸 E) (M : type_of% r),
      Matrix.single () () x * M = x • M)]; abel))
      congr($h + ($k * ρ)ᴴ + (1 + u * ρ)ᴴ * $k * ρ + toAdele c • (rᴴ * $e * r))⟩
  let b := -c • wᴴ * J * A + .single () j 1
  use A + w * b
  linear_combination (norm := simp [b, c, *]) a + c • congr(bᴴ * $W * b)
  abel

/-- Landherr's theorem: over stably unramified E (`StablyUnram`), two spaces V, W with the same
signs have isometric hermitian matrices: aᴴ J_V a = J_W for some a in GL_n(E).

Known result: Landherr's Hasse principle for hermitian forms; weak approximation for unitary
groups. -/
lemma Space.landherr : ∃ a : GL n E, a.1ᴴ * V.J * a = W.J := by
  choose a H using fun V : Space E n s ↦ exists_rat_frame_of_adelic (s := s) .univ ⟨V.isHermitian_J,
    (gram_mul_of_gram_eq V.3 (gram_inv_of_gram_eq (signedSpace ..).3)).trans (by simp)⟩
  have u V := isUnit_of_mul_isUnit_right ((H V).substr (by simp))
  use (u V).unit / (u W).unit, gram_mul_of_gram_eq (H V) (gram_inv_of_gram_eq (H W))

/-- Landherr's theorem for spaces with a point: over stably unramified E (`StablyUnram`), any two
spaces V, W with the same signs differ by a rational change of coordinates a and moving the
point by some g in G. -/
lemma Space.exists_eq_move : ∃ (a : GL n E) (g : G E s) (h : a.1ᴴ * V.J * a = W.J), W.x =
  (a.map toAdele)⁻¹ * V.x * g.toUnitary ∧ ∀ γ, V.ratEmbed (U.conj a h γ) = g * W.ratEmbed γ * g⁻¹ :=
  (V.landherr W).imp fun a h ↦ ⟨G.toUnitary.symm ⟨_, gram_mul_of_gram_eq (gram_inv_of_gram_eq V.3)
  (gram_mul_of_gram_eq (x := a.map toAdele) (by simp [← h]) W.3)⟩,
  h, by simp [ratEmbed, toRatCoords, U.map, MulEquiv.symm_apply_eq, mul_assoc]⟩
end
