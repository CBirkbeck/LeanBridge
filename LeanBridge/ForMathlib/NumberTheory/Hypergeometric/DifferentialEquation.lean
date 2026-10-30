import LeanBridge.ForMathlib.NumberTheory.Hypergeometric.Weight
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp

/-!
# The hypergeometric differential equation of a hypergeometric family

A hypergeometric family `H(A, B)` over `ℚ` of degree `d` (LMFDB `hgm.families`, `hgm.familes`) is a
motive over `ℚ(t)` with coefficients in `ℚ`, indexed by its defining parameters `(A, B)`, whose
periods satisfy the hypergeometric differential equation
`(z ∏_{i=1}^d (θ + α_i) - ∏_{j=1}^d (θ + β_j - 1)) y = 0`, `θ = z d/dz`, where `α` and `β` are the
lists of fractions of `A` and `B` (`Hypergeometric.CuspIndex.fractions`). For every entry `β_k` of
`β`, a solution is the hypergeometric series
`z^{1-β_k} ∑_{n ≥ 0} ∏_i (α_i - β_k + 1)_n / ∏_j (β_j - β_k + 1)_n z^n`, with `(x)_n` the
Pochhammer symbol (`Hypergeometric.Parameters.hypergeometricOperator_hypergeometricSeries`); its
leading coefficient `c_0` is `1`, so it is not zero. The solutions are formal: they are Hahn series
`∑_q c_q z^q` with rational exponents `q`, the exponents of `z^{1-β_k} ∑ c_n z^n` being
`1 - β_k + n`, on which `θ` acts by `z^q ↦ q z^q`.

The knowls write the factors of the first product as `θ - α_i`; with these the series are not
solutions: for `(A, B) = ([2], [1])`, so that `α = (1/2)` and `β = (1)`, the series is
`∑ (1/2)_n / n! z^n = (1 - z)^{-1/2}`, and `(z (θ - 1/2) - θ) (1 - z)^{-1/2} = -z (1 - z)^{-1/2}`.
The equation is that of Beukers and Heckman (*Monodromy for the hypergeometric function
`nFn-1`*, §2), whose solutions near `0` are these series, the local exponents at `0` being the
`1 - β_j`. The knowls also write the equation in `t` and the series in `z`.

The family itself, a motive over `ℚ(t)` (or a hypergeometric local system on `ℙ¹ ∖ {0, 1, ∞}`),
and the identification of its periods with solutions of the equation are not formalised.

## Main definitions

* `Hypergeometric.eulerOperator`: the Euler operator `θ = z d/dz` on Hahn series.
* `Hypergeometric.Parameters.hypergeometricOperator` (LMFDB `hgm.families`, `hgm.familes`): the
  hypergeometric differential operator `z ∏_i (θ + α_i) - ∏_j (θ + β_j - 1)`.
* `Hypergeometric.Parameters.hypergeometricCoeff`: the coefficients
  `∏_i (α_i - β_k + 1)_n / ∏_j (β_j - β_k + 1)_n` of the hypergeometric series.
* `Hypergeometric.Parameters.hypergeometricSeries` (LMFDB `hgm.families`, `hgm.familes`): the
  hypergeometric series `z^{1-β_k} ∑_n c_n z^n`.

## Main results

* `Hypergeometric.Parameters.hypergeometricOperator_hypergeometricSeries`: the hypergeometric
  series are solutions of the hypergeometric differential equation.
-/

open HahnSeries Module

namespace Hypergeometric

/-- The **Euler operator** `θ = z d/dz` on the formal series `∑_q c_q z^q` with rational exponents
(Hahn series), acting by `θ (z^q) = q z^q`. -/
noncomputable def eulerOperator : HahnSeries ℚ ℚ →ₗ[ℚ] HahnSeries ℚ ℚ where
  toFun x := ⟨fun q ↦ q * x.coeff q, x.isPWO_support.mono fun _ hq ↦ right_ne_zero_of_mul hq⟩
  map_add' x y := by
    ext q
    exact mul_add q (x.coeff q) (y.coeff q)
  map_smul' c x := by
    ext q
    exact mul_left_comm q c (x.coeff q)

variable {d : ℕ} (c : CuspIndex d) (P : Parameters d) (b : ℚ) (n : ℕ) (y : HahnSeries ℚ ℚ) (q : ℚ)
    {x : ℚ}

lemma coeff_eulerOperator : (eulerOperator y).coeff q = q * y.coeff q :=
  rfl

lemma coeff_prod_eulerOperator_add (l : List ℚ) (g : ℚ → ℚ) :
    ((l.map fun a ↦ eulerOperator + g a • 1).prod y).coeff q =
      (l.map fun a ↦ q + g a).prod * y.coeff q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, End.one_apply, coeff_add, coeff_smul, coeff_eulerOperator, ih]
    ring1

lemma CuspIndex.pos_of_mem_fractions (hx : x ∈ c.fractions) : 0 < x := by
  rw [CuspIndex.fractions, Multiset.mem_sort, Multiset.mem_bind] at hx
  rcases hx with ⟨a, -, ha⟩
  exact (mem_fractionsWithDen.mp (Finset.mem_val.mp ha)).1

lemma CuspIndex.le_one_of_mem_fractions (hx : x ∈ c.fractions) : x ≤ 1 := by
  rw [CuspIndex.fractions, Multiset.mem_sort, Multiset.mem_bind] at hx
  rcases hx with ⟨a, -, ha⟩
  exact (mem_fractionsWithDen.mp (Finset.mem_val.mp ha)).2.1

/-- The **hypergeometric differential operator** `z ∏_{i=1}^d (θ + α_i) - ∏_{j=1}^d (θ + β_j - 1)`
(LMFDB `hgm.families`, `hgm.familes`) of a hypergeometric family `H(A, B)` of degree `d`, where `θ`
is the Euler operator `z d/dz` (`Hypergeometric.eulerOperator`) and `α`, `β` are the lists of
fractions of `A` and `B`, acting on formal series with rational exponents. The knowls write
`θ - α_i` for `θ + α_i`, which is inconsistent with the solutions they give (see the module
docstring); this is the equation of Beukers and Heckman, of which the knowls' series are
solutions (`hypergeometricOperator_hypergeometricSeries`). -/
noncomputable def Parameters.hypergeometricOperator : End ℚ (HahnSeries ℚ ℚ) :=
  LinearMap.mulLeft ℚ (single 1 1) * (P.A.fractions.map fun α ↦ eulerOperator + α • 1).prod -
    (P.B.fractions.map fun β ↦ eulerOperator + (β - 1) • 1).prod

lemma Parameters.coeff_hypergeometricOperator : (P.hypergeometricOperator y).coeff q =
    (P.A.fractions.map (q - 1 + ·)).prod * y.coeff (q - 1) -
      (P.B.fractions.map fun β ↦ q + (β - 1)).prod * y.coeff q := by
  rw [Parameters.hypergeometricOperator, LinearMap.sub_apply, coeff_sub, End.mul_apply,
    LinearMap.mulLeft_apply, coeff_single_mul, one_mul, coeff_prod_eulerOperator_add,
    coeff_prod_eulerOperator_add]

/-- The **coefficients** `∏_{i=1}^d (α_i - b + 1)_n / ∏_{j=1}^d (β_j - b + 1)_n` of the
hypergeometric series of a hypergeometric family `H(A, B)` at an entry `b = β_k` of `β`
(`Hypergeometric.Parameters.hypergeometricSeries`), where `(x)_n = x (x + 1) ⋯ (x + n - 1)` is the
Pochhammer symbol and `α`, `β` are the lists of fractions of `A` and `B`. For `b ∈ β` the
denominators are positive, as `β_j - b + 1 > 0`. -/
noncomputable def Parameters.hypergeometricCoeff : ℚ :=
  (P.A.fractions.map fun α ↦ (ascPochhammer ℚ n).eval (α - b + 1)).prod /
    (P.B.fractions.map fun β ↦ (ascPochhammer ℚ n).eval (β - b + 1)).prod

/-- The **hypergeometric series** `z^{1-b} ∑_{n ≥ 0} c_n z^n` (LMFDB `hgm.families`,
`hgm.familes`) of a hypergeometric family `H(A, B)` at an entry `b = β_k` of `β`, with
`c_n = ∏_i (α_i - b + 1)_n / ∏_j (β_j - b + 1)_n` (`Hypergeometric.Parameters.hypergeometricCoeff`):
the product of the monomial `z^{1-b}` and the power series `∑ c_n z^n`, a formal series with
rational exponents whose coefficient of `z^{n+1-b}` is `c_n` for `n ∈ ℕ`, all its other
coefficients vanishing. For `b ∈ β` it is a solution of the hypergeometric differential equation
(`hypergeometricOperator_hypergeometricSeries`), and it is not zero, as `c_0 = 1`. -/
noncomputable def Parameters.hypergeometricSeries : HahnSeries ℚ ℚ :=
  single (1 - b) 1 * embDomain Nat.castOrderEmbedding ⟨P.hypergeometricCoeff b, .of_linearOrder _⟩

lemma Parameters.coeff_hypergeometricSeries_natCast_add :
    (P.hypergeometricSeries b).coeff (n + (1 - b)) = P.hypergeometricCoeff b n := by
  rw [Parameters.hypergeometricSeries, coeff_single_mul, one_mul, add_sub_cancel_right,
    ← Nat.castOrderEmbedding_apply, embDomain_coeff]

variable {q} in
lemma Parameters.coeff_hypergeometricSeries_of_ne (hq : ∀ n : ℕ, q ≠ n + (1 - b)) :
    (P.hypergeometricSeries b).coeff q = 0 :=
  coeff_single_mul.trans <| (one_mul _).trans <| embDomain_of_notMem_range fun ⟨n, hn⟩ ↦
    hq n (eq_add_of_sub_eq hn.symm)

lemma Parameters.hypergeometricCoeff_zero : P.hypergeometricCoeff b 0 = 1 := by
  simp [Parameters.hypergeometricCoeff]

lemma Parameters.hypergeometricSeries_ne_zero : P.hypergeometricSeries b ≠ 0 :=
  fun h ↦ one_ne_zero <| (P.hypergeometricCoeff_zero b).symm.trans <|
    (P.coeff_hypergeometricSeries_natCast_add b 0).symm.trans <| by rw [h, coeff_zero]

/-- **The hypergeometric series are solutions of the hypergeometric differential equation**: for
every entry `b = β_k` of `β`, the series `z^{1-b} ∑_n c_n z^n` is annihilated by
`z ∏_i (θ + α_i) - ∏_j (θ + β_j - 1)`. -/
lemma Parameters.hypergeometricOperator_hypergeometricSeries (hb : b ∈ P.B.fractions) :
    P.hypergeometricOperator (P.hypergeometricSeries b) = 0 := by
  ext q
  rw [coeff_hypergeometricOperator, coeff_zero]
  by_cases hq : ∃ n : ℕ, q = n + (1 - b)
  · rcases hq with ⟨n, rfl⟩
    rcases n with _ | n
    · rw [P.coeff_hypergeometricSeries_of_ne b fun m hm ↦ by
          push_cast at hm
          linarith [m.cast_nonneg (α := ℚ)],
        List.prod_eq_zero (List.mem_map.mpr ⟨b, hb, by push_cast; ring1⟩)]
      ring1
    · have hpos (β : ℚ) (hβ : β ∈ P.B.fractions) : 0 < β - b + 1 := by
        linarith [P.B.pos_of_mem_fractions hβ, P.B.le_one_of_mem_fractions hb]
      have h : ((n + 1 : ℕ) : ℚ) + (1 - b) - 1 = n + (1 - b) := by
        push_cast
        ring1
      have hA : (P.A.fractions.map fun α ↦ (ascPochhammer ℚ (n + 1)).eval (α - b + 1)).prod =
          (P.A.fractions.map fun α ↦ (ascPochhammer ℚ n).eval (α - b + 1)).prod *
              (P.A.fractions.map fun α ↦ n + (1 - b) + α).prod := by
        rw [← List.prod_map_mul]
        refine congrArg _ <| List.map_congr_left fun α _ ↦ ?_
        rw [ascPochhammer_succ_eval]
        ring1
      have hB : (P.B.fractions.map fun β ↦ (ascPochhammer ℚ (n + 1)).eval (β - b + 1)).prod =
          (P.B.fractions.map fun β ↦ (ascPochhammer ℚ n).eval (β - b + 1)).prod *
              (P.B.fractions.map fun β ↦ ((n + 1 : ℕ) : ℚ) + (1 - b) + (β - 1)).prod := by
        rw [← List.prod_map_mul]
        refine congrArg _ <| List.map_congr_left fun β _ ↦ ?_
        rw [ascPochhammer_succ_eval]
        push_cast
        ring1
      have h₁ : (P.B.fractions.map fun β ↦ (ascPochhammer ℚ n).eval (β - b + 1)).prod ≠ 0 :=
        List.prod_ne_zero fun h ↦ by
          rcases List.mem_map.mp h with ⟨β, hβ, h⟩
          exact (ascPochhammer_pos n _ (hpos β hβ)).ne' h
      have h₂ : (P.B.fractions.map fun β ↦ ((n + 1 : ℕ) : ℚ) + (1 - b) + (β - 1)).prod ≠ 0 :=
        List.prod_ne_zero fun h ↦ by
          rcases List.mem_map.mp h with ⟨β, hβ, h⟩
          push_cast at h
          linarith [hpos β hβ, n.cast_nonneg (α := ℚ)]
      rw [h, P.coeff_hypergeometricSeries_natCast_add, P.coeff_hypergeometricSeries_natCast_add,
        hypergeometricCoeff, hypergeometricCoeff, hA, hB]
      field_simp
      ring1
  · rw [P.coeff_hypergeometricSeries_of_ne b fun n hn ↦ hq ⟨n, hn⟩,
      P.coeff_hypergeometricSeries_of_ne b fun n hn ↦ hq ⟨n + 1, by push_cast; linarith⟩]
    ring1

end Hypergeometric
