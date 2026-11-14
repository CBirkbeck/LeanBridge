import LeanBridge.ForMathlib.Algebra.EuclideanDomain.NatEuclidean
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Trace.Basic

/-!
# The five Euclidean imaginary quadratic fields

LMFDB `dq.mf.bianchi.source` states that the Bianchi modular forms of the LMFDB were computed for
the five fields `ℚ(√-1)`, `ℚ(√-2)`, `ℚ(√-3)`, `ℚ(√-7)` and `ℚ(√-11)`, "these five Euclidean
imaginary quadratic fields". We prove that they are imaginary quadratic and Euclidean: for a number
field `K` of degree `2` containing a square root `θ` of `-d`, with `d` one of `1, 2, 3, 7, 11`, `K`
is totally complex and its ring of integers is Euclidean in the sense of the LMFDB (LMFDB
`ring.euclidean_domain`, `IsNatEuclidean`), for the absolute value of the norm. That no other
imaginary quadratic field is Euclidean (Motzkin) is not proved here.

Every element of `K` is `u + v θ` with `u, v ∈ ℚ`, of norm `u² + d v²` (by Cayley–Hamilton in the
quadratic extension `K / ℚ`, Mathlib's `Algebra.IsQuadraticExtension`). The ring of integers of `K`
is Euclidean for the absolute value of the norm as soon as every `x ∈ K` has an algebraic integer
`q` with `|N(x - q)| < 1`: divide `a` by `b` with quotient `q` for `x = a / b`. For `d = 1, 2`, take
`q = m + n θ` with `m` and `n` the nearest integers to `u` and `v`, so that
`N(x - q) ≤ 1/4 + d/4 < 1`. For `d = 3, 7, 11`, take `q = m + n ω` with `ω = (1 + θ) / 2`, a root
of `X² - X + (d + 1)/4`, `n` the nearest integer to `2 v` and `m` the nearest integer to
`u - n / 2`, so that `N(x - q) ≤ 1/4 + d/16 < 1`. The rings of integers need not be computed.

## Main results

* `NumberField.isTotallyComplex_of_sq_eq_neg` (LMFDB `dq.mf.bianchi.source`): a number field
  containing a square root of `-d`, `d > 0`, is totally complex.
* `NumberField.isNatEuclidean_of_forall_exists_abs_norm_sub_lt_one`: the norm-Euclidean criterion.
* `NumberField.isNatEuclidean_ringOfIntegers_of_sq_eq_neg` (LMFDB `dq.mf.bianchi.source`): the ring
  of integers of `ℚ(√-d)` is Euclidean for `d = 1, 2, 3, 7, 11`.
* `NumberField.isTotallyComplex_quadraticAlgebra` and
  `NumberField.isNatEuclidean_ringOfIntegers_quadraticAlgebra` (LMFDB `dq.mf.bianchi.source`): the
  same for the model `ℚ[X] / (X² + d)` of `ℚ(√-d)`, Mathlib's `QuadraticAlgebra ℚ (-d) 0`.
-/

open Module Polynomial

open Algebra (IsQuadraticExtension)

namespace NumberField

variable {K : Type*} [Field K] {θ : K} {d : ℕ}

lemma isIntegral_of_sq_eq_neg (hθ : θ ^ 2 = -d) : IsIntegral ℤ θ := by
  refine ⟨X ^ 2 + C (d : ℤ), monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [← aeval_def]
  simp [hθ]

variable [CharZero K] in
lemma isIntegral_half_of_sq_eq_neg (hθ : θ ^ 2 = -d) {k : ℕ} (hk : 4 * k = d + 1) :
    IsIntegral ℤ ((1 + θ) / 2) := by
  refine ⟨X ^ 2 - X + C (k : ℤ), by monicity!, ?_⟩
  have hk' : (4 * k : K) = d + 1 := by exact_mod_cast hk
  rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast,
    Int.cast_natCast]
  linear_combination (1 / 4 : K) * hθ + (1 / 4 : K) * hk'

variable [NumberField K]

/-- **A number field containing a square root of `-d`, `d > 0`, is totally complex** (LMFDB
`dq.mf.bianchi.source`): every complex embedding sends the square root to a non-real complex
number, so it is not real. So the fields `ℚ(√-d)` are imaginary quadratic. -/
lemma isTotallyComplex_of_sq_eq_neg (hd : 0 < d) (hθ : θ ^ 2 = -d) : IsTotallyComplex K := by
  refine ⟨fun v ↦ InfinitePlace.not_isReal_iff_isComplex.mp fun hv ↦ ?_⟩
  have hθ' : v.embedding θ ^ 2 = -(d : ℂ) := by rw [← map_pow, hθ, map_neg, map_natCast]
  have hre : (starRingEnd ℂ) (v.embedding θ) = v.embedding θ :=
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) θ
  rw [Complex.conj_eq_iff_re] at hre
  rw [← hre] at hθ'
  have h : (v.embedding θ).re ^ 2 = -(d : ℝ) := by exact_mod_cast hθ'
  nlinarith [sq_nonneg (v.embedding θ).re, (Nat.cast_pos (α := ℝ)).mpr hd]

/-- **The norm-Euclidean criterion**: if every element `x` of a number field `K` is at distance less
than `1` from the ring of integers for the norm, `|N(x - q)| < 1` for some algebraic integer `q`,
then the ring of integers is Euclidean (LMFDB `ring.euclidean_domain`) for the absolute value of
the norm: `a = b q + r` with `|N(r)| = |N(b)| |N(a / b - q)| < |N(b)|`. -/
lemma isNatEuclidean_of_forall_exists_abs_norm_sub_lt_one
    (h : ∀ x : K, ∃ q : 𝓞 K, |Algebra.norm ℚ (x - q)| < 1) : IsNatEuclidean (𝓞 K) := by
  refine ⟨fun r ↦ (Algebra.norm ℤ r).natAbs, fun a b hb ↦ ?_⟩
  rcases h ((a : K) / b) with ⟨q, hq⟩
  refine ⟨q, a - b * q, by ring1, ?_⟩
  by_cases hr : a - b * q = 0
  · exact Or.inl hr
  refine Or.inr ?_
  have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
  have hN :
      (Algebra.norm ℤ (a - b * q) : ℚ) = Algebra.norm ℤ b * Algebra.norm ℚ ((a : K) / b - q) := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← map_mul]
    congr 1
    push_cast
    field_simp
  have hNb : (Algebra.norm ℤ b : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]
    exact Algebra.norm_ne_zero_iff.mpr hb'
  have hlt : |(Algebra.norm ℤ (a - b * q) : ℚ)| < |(Algebra.norm ℤ b : ℚ)| := by
    rw [hN, abs_mul]
    exact mul_lt_of_lt_one_right (abs_pos.mpr hNb) hq
  have hlt' : |Algebra.norm ℤ (a - b * q)| < |Algebra.norm ℤ b| := by exact_mod_cast hlt
  exact Int.ofNat_lt.mp (by rwa [Int.natCast_natAbs, Int.natCast_natAbs])

lemma algebraMap_add_algebraMap_mul_eq_zero_iff (hθ : θ ^ 2 = -d) (hd : 0 < d) {A B : ℚ} :
    algebraMap ℚ K A + algebraMap ℚ K B * θ = 0 ↔ A = 0 ∧ B = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨hA, hB⟩ ↦ by rw [hA, hB, map_zero, zero_mul, add_zero]⟩
  by_cases hB : B = 0
  · rw [hB, map_zero, zero_mul, add_zero, map_eq_zero_iff _ (algebraMap ℚ K).injective] at h
    exact ⟨h, hB⟩
  · exfalso
    have hB' : algebraMap ℚ K B ≠ 0 := (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr hB
    have hθq : θ = algebraMap ℚ K (-A / B) := by
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    rw [hθq, ← map_pow, ← map_natCast (algebraMap ℚ K), ← map_neg] at hθ
    have h2 : (-A / B) ^ 2 = -(d : ℚ) := (algebraMap ℚ K).injective hθ
    nlinarith [sq_nonneg (-A / B), (Nat.cast_pos (α := ℚ)).mpr hd]

lemma exists_eq_add_mul (hK : finrank ℚ K = 2) (hθ : θ ^ 2 = -d) (hd : 0 < d) (x : K) :
    ∃ u v : ℚ, x = algebraMap ℚ K u + algebraMap ℚ K v * θ := by
  have hli : LinearIndependent ℚ ![1, θ] := LinearIndependent.pair_iff.mpr fun s t hst ↦
    (algebraMap_add_algebraMap_mul_eq_zero_iff hθ hd).mp (by
      rwa [Algebra.smul_def, Algebra.smul_def, mul_one] at hst)
  have hx : x ∈ Submodule.span ℚ (Set.range ![1, θ]) :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hK]) ▸ Submodule.mem_top
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hx
  rcases hx with ⟨u, v, hx⟩
  exact ⟨u, v, by rw [← hx, Algebra.smul_def, Algebra.smul_def, mul_one]⟩

lemma norm_add_mul (hK : finrank ℚ K = 2) (hθ : θ ^ 2 = -d) (hd : 0 < d) (u v : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K u + algebraMap ℚ K v * θ) = u ^ 2 + d * v ^ 2 := by
  have hq : IsQuadraticExtension ℚ K := ⟨hK⟩
  set t : ℚ := Algebra.trace ℚ K (algebraMap ℚ K u + algebraMap ℚ K v * θ)
  set n : ℚ := Algebra.norm ℚ (algebraMap ℚ K u + algebraMap ℚ K v * θ) with hn
  have key : (algebraMap ℚ K u + algebraMap ℚ K v * θ) ^ 2 =
      algebraMap ℚ K t * (algebraMap ℚ K u + algebraMap ℚ K v * θ) - algebraMap ℚ K n :=
    (IsQuadraticExtension.sq_eq_trace_smul_sub_norm ℚ _).trans (by rw [Algebra.smul_def])
  have h1 : algebraMap ℚ K (u ^ 2 - d * v ^ 2 - t * u + n) +
      algebraMap ℚ K (2 * u * v - t * v) * θ = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat]
    linear_combination key - (algebraMap ℚ K v) ^ 2 * hθ
  rcases (algebraMap_add_algebraMap_mul_eq_zero_iff hθ hd).mp h1 with ⟨h2, h3⟩
  by_cases hv : v = 0
  · rw [hv, map_zero, zero_mul, add_zero] at hn
    rw [hn, Algebra.norm_algebraMap, hK, hv]
    ring1
  · have htu : t = 2 * u := by
      have h4 : (2 * u - t) * v = 0 := by linear_combination h3
      rcases mul_eq_zero.mp h4 with h | h
      · linear_combination -h
      · exact absurd h hv
    rw [htu] at h2
    linear_combination h2

lemma exists_abs_norm_sub_lt_one_of_lt_three (hK : finrank ℚ K = 2) (hθ : θ ^ 2 = -d) (hd : 0 < d)
    (hd3 : d < 3) (x : K) : ∃ q : 𝓞 K, |Algebra.norm ℚ (x - q)| < 1 := by
  rcases exists_eq_add_mul hK hθ hd x with ⟨u, v, rfl⟩
  rcases (⟨⟨_, (mem_integralClosure_iff ℤ K).mpr (isIntegral_algebraMap.add
      (isIntegral_algebraMap.mul (isIntegral_of_sq_eq_neg hθ)))⟩, rfl⟩ : ∃ q : 𝓞 K,
      (q : K) = algebraMap ℤ K (round u) + algebraMap ℤ K (round v) * θ) with ⟨q, hq⟩
  have hdiff : algebraMap ℚ K u + algebraMap ℚ K v * θ -
      (algebraMap ℤ K (round u) + algebraMap ℤ K (round v) * θ) =
      algebraMap ℚ K (u - round u) + algebraMap ℚ K (v - round v) * θ := by
    simp only [map_sub, map_intCast, eq_intCast]
    ring1
  refine ⟨q, ?_⟩
  rw [hq, hdiff, norm_add_mul hK hθ hd]
  have hu : |u - round u| ≤ 1 / 2 := abs_sub_round u
  have hv : |v - round v| ≤ 1 / 2 := abs_sub_round v
  have hd' : (d : ℚ) ≤ 2 := by exact_mod_cast (by omega : d ≤ 2)
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_abs (u - round u), sq_abs (v - round v), abs_nonneg (u - round u),
    abs_nonneg (v - round v)]

lemma exists_abs_norm_sub_lt_one_of_lt_twelve (hK : finrank ℚ K = 2) (hθ : θ ^ 2 = -d) (hd : 0 < d)
    {k : ℕ} (hk : 4 * k = d + 1) (hd12 : d < 12) (x : K) :
    ∃ q : 𝓞 K, |Algebra.norm ℚ (x - q)| < 1 := by
  rcases exists_eq_add_mul hK hθ hd x with ⟨u, v, rfl⟩
  rcases (⟨⟨_, (mem_integralClosure_iff ℤ K).mpr (isIntegral_algebraMap.add
      (isIntegral_algebraMap.mul (isIntegral_half_of_sq_eq_neg hθ hk)))⟩, rfl⟩ : ∃ q : 𝓞 K,
      (q : K) = algebraMap ℤ K (round (u - round (2 * v) / 2)) +
        algebraMap ℤ K (round (2 * v)) * ((1 + θ) / 2)) with ⟨q, hq⟩
  have hdiff : algebraMap ℚ K u + algebraMap ℚ K v * θ -
      (algebraMap ℤ K (round (u - round (2 * v) / 2)) +
        algebraMap ℤ K (round (2 * v)) * ((1 + θ) / 2)) =
      algebraMap ℚ K (u - round (2 * v) / 2 - round (u - round (2 * v) / 2)) +
        algebraMap ℚ K (v - round (2 * v) / 2) * θ := by
    simp only [map_sub, map_div₀, map_intCast, map_ofNat, eq_intCast]
    ring1
  refine ⟨q, ?_⟩
  rw [hq, hdiff, norm_add_mul hK hθ hd]
  have hu : |u - round (2 * v) / 2 - round (u - round (2 * v) / 2)| ≤ 1 / 2 := abs_sub_round _
  have hv : |2 * v - round (2 * v)| ≤ 1 / 2 := abs_sub_round _
  have hv' : |v - round (2 * v) / 2| ≤ 1 / 4 := by
    have h2v : v - round (2 * v) / 2 = (2 * v - round (2 * v)) / 2 := by ring1
    rw [h2v, abs_div, abs_two]
    linarith
  have hd' : (d : ℚ) ≤ 11 := by exact_mod_cast (by omega : d ≤ 11)
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_abs (u - round (2 * v) / 2 - round (u - round (2 * v) / 2)),
    sq_abs (v - round (2 * v) / 2),
    abs_nonneg (u - round (2 * v) / 2 - round (u - round (2 * v) / 2)),
    abs_nonneg (v - round (2 * v) / 2)]

/-- **The rings of integers of `ℚ(√-1)`, `ℚ(√-2)`, `ℚ(√-3)`, `ℚ(√-7)` and `ℚ(√-11)` are
Euclidean** (LMFDB `dq.mf.bianchi.source`, `ring.euclidean_domain`): for a number field `K` of
degree `2` containing a square root `θ` of `-d`, with `d` one of `1, 2, 3, 7, 11`, the ring of
integers of `K` is Euclidean for the absolute value of the norm. For `d = 1, 2` the nearest point of
`ℤ[θ]` is at norm distance at most `1/4 + d/4 < 1`, and for `d = 3, 7, 11` the nearest point of
`ℤ[(1 + θ) / 2]` at norm distance at most `1/4 + d/16 < 1`. -/
lemma isNatEuclidean_ringOfIntegers_of_sq_eq_neg (hK : finrank ℚ K = 2) (hθ : θ ^ 2 = -d)
    (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 11) : IsNatEuclidean (𝓞 K) := by
  refine isNatEuclidean_of_forall_exists_abs_norm_sub_lt_one fun x ↦ ?_
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact exists_abs_norm_sub_lt_one_of_lt_three hK hθ one_pos (by norm_num) x
  · exact exists_abs_norm_sub_lt_one_of_lt_three hK hθ two_pos (by norm_num) x
  · exact exists_abs_norm_sub_lt_one_of_lt_twelve hK hθ (by norm_num) (k := 1) rfl (by norm_num) x
  · exact exists_abs_norm_sub_lt_one_of_lt_twelve hK hθ (by norm_num) (k := 2) rfl (by norm_num) x
  · exact exists_abs_norm_sub_lt_one_of_lt_twelve hK hθ (by norm_num) (k := 3) rfl (by norm_num) x

lemma not_isSquare_neg_natCast (hd : 0 < d) : ¬IsSquare (-(d : ℚ)) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r, (Nat.cast_pos (α := ℚ)).mpr hd]

lemma omega_sq_quadraticAlgebra :
    (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-(d : ℚ)) 0) ^ 2 = -d := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero, map_neg,
    map_natCast]

/-- **The model `ℚ[X] / (X² + d)` of `ℚ(√-d)` is totally complex** for `d > 0` (LMFDB
`dq.mf.bianchi.source`): Mathlib's `QuadraticAlgebra ℚ (-d) 0`, a number field of degree `2`
(`QuadraticAlgebra.finrank_eq_two`), is an imaginary quadratic field. -/
lemma isTotallyComplex_quadraticAlgebra (hd : 0 < d) :
    haveI : Fact (¬IsSquare (-(d : ℚ))) := ⟨not_isSquare_neg_natCast hd⟩
    haveI : NumberField (QuadraticAlgebra ℚ (-(d : ℚ)) 0) := ⟨⟩
    IsTotallyComplex (QuadraticAlgebra ℚ (-(d : ℚ)) 0) := by
  have hf : Fact (¬IsSquare (-(d : ℚ))) := ⟨not_isSquare_neg_natCast hd⟩
  have hn : NumberField (QuadraticAlgebra ℚ (-(d : ℚ)) 0) := ⟨⟩
  exact isTotallyComplex_of_sq_eq_neg hd omega_sq_quadraticAlgebra

/-- **The ring of integers of the model `ℚ[X] / (X² + d)` of `ℚ(√-d)` is Euclidean** for
`d = 1, 2, 3, 7, 11` (LMFDB `dq.mf.bianchi.source`): Mathlib's `QuadraticAlgebra ℚ (-d) 0`, a
quadratic number field in which `ω = ⟨0, 1⟩` is a square root of `-d`, satisfies the hypotheses of
`NumberField.isNatEuclidean_ringOfIntegers_of_sq_eq_neg`. -/
lemma isNatEuclidean_ringOfIntegers_quadraticAlgebra (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 7 ∨ d = 11) :
    haveI : Fact (¬IsSquare (-(d : ℚ))) := ⟨not_isSquare_neg_natCast (by omega)⟩
    haveI : NumberField (QuadraticAlgebra ℚ (-(d : ℚ)) 0) := ⟨⟩
    IsNatEuclidean (𝓞 (QuadraticAlgebra ℚ (-(d : ℚ)) 0)) := by
  have hf : Fact (¬IsSquare (-(d : ℚ))) := ⟨not_isSquare_neg_natCast (by omega)⟩
  have hn : NumberField (QuadraticAlgebra ℚ (-(d : ℚ)) 0) := ⟨⟩
  exact isNatEuclidean_ringOfIntegers_of_sq_eq_neg (QuadraticAlgebra.finrank_eq_two _ _)
    omega_sq_quadraticAlgebra hd

end NumberField
