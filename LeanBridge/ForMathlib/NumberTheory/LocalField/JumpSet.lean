import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# Jump sets of `p`-adic fields

Let `K` be a `p`-adic field containing a primitive `p`-th root of unity `ζ_p`, `e = v_K(p)` its
absolute ramification index and `r = v_p(e)`. Miki showed that
`ζ_p = α₀^{p^r} α₁^{p^{r-1}} ⋯ α_{r-1}^p α_r` with each `αᵢ` either `1` or a principal unit with
`uᵢ = v_K(αᵢ - 1)` satisfying `uᵢ < pe/(p - 1)` and `p ∤ uᵢ`, or `uᵢ = pe/(p - 1)` and `αᵢ` not a
`p`-th power. The jump set of `K` (LMFDB `lf.jump_set`) is the sequence `[u₀, …, u_r]`, the
undefined `uᵢ` (those with `αᵢ = 1`) being filled in by `u_{i+1} = ρ(uᵢ)`, `ρ(x) = min(px, x + e)`;
Pagano showed that it does not depend on the factorisation, and that it determines the principal
units of `K` as a filtered `ℤ_p`-module.

Neither Miki's existence theorem nor Pagano's independence theorem is formalised, so the jump set is
defined as a relation: `u` is a jump set of `K` if it is the sequence of some such factorisation of
some primitive `p`-th root of unity. By the two theorems, exactly one `u` is, when `ζ_p ∈ K`; when
`ζ_p ∉ K` none is, as the jump set is then not defined.

The knowl writes the conditions on `αᵢ` with `v_K(αᵢ)`, which is `0` for the principal units `αᵢ`;
they are conditions on `v_K(αᵢ - 1)`, the `uᵢ` of the jump set. It also writes the sequence as
`[u₀, u₂, …, u_r]` for `[u₀, u₁, …, u_r]`.

## Main definitions

* `IsNonarchimedeanLocalField.jumpRho`: the function `ρ(x) = min(px, x + e)`.
* `IsNonarchimedeanLocalField.unitDepth`: `v_K(x - 1)` for `x ≠ 1`.
* `IsNonarchimedeanLocalField.IsMikiFactor` and `IsNonarchimedeanLocalField.IsMikiFactorisation`
  (LMFDB `lf.jump_set`): Miki's factorisations of `ζ_p`.
* `IsNonarchimedeanLocalField.jumpSequence` (LMFDB `lf.jump_set`): the extended jump set of a
  factorisation.
* `IsNonarchimedeanLocalField.IsJumpSet` (LMFDB `lf.jump_set`): `u` is the jump set of `K`.

## Main results

* `IsNonarchimedeanLocalField.jumpSequence_succ_of_eq_one`: the recursion `u_{i+1} = ρ(uᵢ)` for
  `α_{i+1} = 1`.
* `IsNonarchimedeanLocalField.not_isJumpSet_of_forall_not_isPrimitiveRoot`: without a primitive
  `p`-th root of unity, `K` has no jump set.
-/

open TauCeti Finset

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- The function `ρ(n) = min(pn, n + e)` (LMFDB `lf.jump_set`) of a `p`-adic field `K` of absolute
ramification index `e`: for a principal unit `x` with `v_K(x - 1) = n ≠ e/(p - 1)`,
`v_K(x^p - 1) = ρ(n)`. -/
noncomputable def jumpRho (n : ℤ) : ℤ :=
  min (p * n) (n + absoluteRamificationIndex K p)

variable {K} (x : K) (α : ℕ → K) (u : List ℤ)

open Classical in
/-- The **depth** `v_K(x - 1)` of an element `x ≠ 1` of a nonarchimedean local field `K`, for the
normalized valuation `v_K` of `K`, and `0` for `x = 1`: a principal unit `x` lies in the `n`-th
unit group `1 + 𝔪^n` exactly when `n ≤ v_K(x - 1)`. -/
noncomputable def unitDepth : ℤ :=
  if h : x - 1 = 0 then 0 else (normalizedValuation K (Units.mk0 (x - 1) h)).toAdd

/-- An element `x` of a `p`-adic field `K`, of absolute ramification index `e`, is a **Miki factor**
(LMFDB `lf.jump_set`) if `x = 1`, or `x` is a principal unit with `u = v_K(x - 1)` satisfying
`u < pe/(p - 1)` and `p ∤ u`, or `u = pe/(p - 1)` and `x` is not a `p`-th power in `K`. -/
def IsMikiFactor : Prop :=
  x = 1 ∨ x ≠ 1 ∧ 0 < unitDepth x ∧
    (unitDepth x * (p - 1) < p * absoluteRamificationIndex K p ∧ ¬(p : ℤ) ∣ unitDepth x ∨
      unitDepth x * (p - 1) = p * absoluteRamificationIndex K p ∧ ¬∃ y : K, y ^ p = x)

/-- A **Miki factorisation** (LMFDB `lf.jump_set`) of `ζ ∈ K`, for a `p`-adic field `K` with
`r = v_p(e)`, `e` the absolute ramification index of `K`: Miki factors `α₀, …, α_r` with
`ζ = α₀^{p^r} α₁^{p^{r-1}} ⋯ α_r`. Miki showed that every primitive `p`-th root of unity of `K` has
one (not formalised). -/
def IsMikiFactorisation (ζ : K) : Prop :=
  ζ = ∏ i ∈ range (padicValNat p (absoluteRamificationIndex K p) + 1),
      α i ^ p ^ (padicValNat p (absoluteRamificationIndex K p) - i) ∧
    ∀ i ≤ padicValNat p (absoluteRamificationIndex K p), IsMikiFactor p (α i)

open Classical in
/-- The **extended jump sequence** (LMFDB `lf.jump_set`) of a sequence `α₀, α₁, …` of elements of a
`p`-adic field `K`: `uᵢ = v_K(αᵢ - 1)` if `αᵢ ≠ 1`, and otherwise `u_{i+1} = ρ(uᵢ)`; the knowl
leaves `u₀` undefined when `α₀ = 1`, and it is `0` here. -/
noncomputable def jumpSequence : ℕ → ℤ
  | 0 => unitDepth (α 0)
  | i + 1 => if α (i + 1) = 1 then jumpRho K p (jumpSequence i) else unitDepth (α (i + 1))

variable (K) in
/-- `u` is the **jump set** (LMFDB `lf.jump_set`) of a `p`-adic field `K` containing a primitive
`p`-th root of unity: the extended jump sequence `[u₀, …, u_r]`, `r = v_p(e)`, of a Miki
factorisation of a primitive `p`-th root of unity of `K`. By Miki's theorem a jump set exists, and
by Pagano's theorem it is unique (neither is formalised); without a primitive `p`-th root of unity
there is none (`not_isJumpSet_of_forall_not_isPrimitiveRoot`). -/
def IsJumpSet : Prop :=
  ∃ ζ : K, IsPrimitiveRoot ζ p ∧ ∃ β : ℕ → K, IsMikiFactorisation p β ζ ∧
    (List.range (padicValNat p (absoluteRamificationIndex K p) + 1)).map (jumpSequence p β) = u

variable {α} in
/-- **The recursion of the extended jump sequence**: `u_{i+1} = ρ(uᵢ)` when `α_{i+1} = 1`. -/
lemma jumpSequence_succ_of_eq_one {i : ℕ} (h : α (i + 1) = 1) :
    jumpSequence p α (i + 1) = jumpRho K p (jumpSequence p α i) :=
  ite_eq_left h

/-- **A `p`-adic field without a primitive `p`-th root of unity has no jump set.** -/
lemma not_isJumpSet_of_forall_not_isPrimitiveRoot (h : ∀ ζ : K, ¬IsPrimitiveRoot ζ p) :
    ¬IsJumpSet K p u := by
  rintro ⟨ζ, hζ, -⟩
  exact h ζ hζ

end IsNonarchimedeanLocalField
