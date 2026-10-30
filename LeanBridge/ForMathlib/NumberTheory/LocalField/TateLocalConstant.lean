import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Tate's local root numbers of characters of `ℚ_p` and `ℝ`

The local root number `ε(ρ)` of a representation `ρ` of `Gal(ℚ̄_p/ℚ_p)` (LMFDB `lf.root_number`) is
the Langlands–Deligne local constant of `ρ`, and the root number of a `p`-adic field `K` is
`ε(K) = ε(ρ_K)` for the permutation representation `ρ_K` on the embeddings of `K`. The local
constants of representations of dimension at least `2`, which `ρ_K` is unless `K = ℚ_p`, are out of
reach: they rest on Deligne's existence and uniqueness theorem. This file formalises the abelian
case, Tate's local constants of characters, through which local class field theory (not used here)
gives the local constants of the representations of dimension `1`: a character `χ` of `ℚ_p^×` with
conductor `p ^ a`, `a ≥ 1`, has local root number

`W(χ) = χ(p) ^ a p ^ (-a/2) ∑_{u ∈ (ℤ/p^a)^×} χ(u)⁻¹ e ^ (2πi u / p ^ a)`,

and `W(χ) = 1` if `χ` is unramified. This is Tate's local constant `ε(χ |·| ^ (1/2), ψ_p, dx)` for
the additive character `ψ_p(x) = e ^ (2πi {x}_p)` and the self-dual Haar measure. A character `χ` of
`ℝ^×` has local root number `1` if `χ(-1) = 1` and `-i` otherwise, for `ψ_∞(x) = e ^ (-2πi x)`; as
in the knowl, the trivial and sign characters have root numbers `1` and `-i`. These normalisations
make the global root number the product of the local ones: for a Dirichlet character `ψ` of
conductor `p ^ a`, the local root numbers at `∞` and `p` of the idele class character of `ψ`
multiply to the root number of `L(s, ψ)` (`Padic.real_tateRootNumber_mul_tateRootNumber`),
Mathlib's `DirichletCharacter.rootNumber`.

The conductor exponent `a` of a character of `ℚ_p^×` is the least `a` such that the character is
trivial on the units `u ≡ 1 mod p ^ a`, and on all units of `ℤ_p` for `a = 0`. A character with no
such `a` is not continuous and has no local root number; it takes the junk value `1`.

## Main definitions

* `Real.tateRootNumber` (LMFDB `lf.root_number`): the local root number of a character of `ℝ^×`.
* `Padic.charConductorExponent`: the exponent `a` of the conductor `p ^ a` of a character of
  `ℚ_p^×`.
* `Padic.tateRootNumber` (LMFDB `lf.root_number`): the local root number of a character of `ℚ_p^×`.

## Main results

* `Real.tateRootNumber_one`, `Real.tateRootNumber_of_apply_neg_one_ne_one`: the trivial character
  of `ℝ^×` has local root number `1` and the sign character `-i`.
* `Padic.tateRootNumber_eq_one`: an unramified character has local root number `1`.
* `Padic.tateRootNumber_eq_gaussSum_div`: the local component at `p` of the idele class character
  of a Dirichlet character `ψ` of conductor `N = p ^ a` has local root number `τ(ψ) / √N`.
* `Padic.real_tateRootNumber_mul_tateRootNumber`: for a Dirichlet character of conductor `p ^ a`,
  the product of the local root numbers at `∞` and `p` is the root number of its L-function.
-/

open Complex

namespace Real

/-- The **local root number** (LMFDB `lf.root_number`) of a character `χ` of `ℝ^×`: `1` if
`χ(-1) = 1` and `-i` if `χ(-1) ≠ 1`, Tate's local constant `ε(χ |·| ^ (1/2), ψ_∞, dx)` for the
additive character `ψ_∞(x) = e ^ (-2πi x)` and the self-dual Haar measure, which only depends on
`χ(-1)`. As in the knowl, the trivial and sign characters, those of `Gal(ℂ/ℝ)`, have local root
numbers `1` and `-i`. -/
noncomputable def tateRootNumber (χ : ℝˣ →* ℂˣ) : ℂ :=
  if χ (-1) = 1 then 1 else -I

/-- **The trivial character of `ℝ^×` has local root number `1`.** -/
lemma tateRootNumber_one : tateRootNumber 1 = 1 := by
  simp [tateRootNumber]

/-- **A character of `ℝ^×` with `χ(-1) ≠ 1`, such as the sign character, has local root number
`-i`.** -/
lemma tateRootNumber_of_apply_neg_one_ne_one {χ : ℝˣ →* ℂˣ} (h : χ (-1) ≠ 1) :
    tateRootNumber χ = -I := by
  rw [tateRootNumber, ite_eq_right h]

end Real

namespace Padic

variable {p : ℕ} [Fact p.Prime] (χ : ℚ_[p]ˣ →* ℂˣ)

/-- A character `χ` of `ℚ_p^×` is **trivial on the units congruent to `1` modulo `p ^ n`**: on the
`u ∈ ℤ_p^×` with `‖u - 1‖ ≤ p ^ (-n)`, which for `n = 0` are all the units of `ℤ_p`. -/
def IsTrivialOnUnitsMod (n : ℕ) : Prop :=
  ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1

/-- The exponent `a` of the **conductor** `p ^ a` of a character `χ` of `ℚ_p^×`: the least `a` such
that `χ` is trivial on the units congruent to `1` modulo `p ^ a`, so that `a = 0` exactly when `χ`
is unramified. A continuous character has one; otherwise the value is the junk value `0`. -/
noncomputable def charConductorExponent : ℕ :=
  sInf {n | IsTrivialOnUnitsMod χ n}

/-- The value `χ(m)` of a character `χ` of `ℚ_p^×` at a natural number `m ≠ 0`, as a complex
number, with the junk value `0` at `m = 0`. -/
noncomputable def charValueNat (m : ℕ) : ℂ :=
  if h : m = 0 then 0 else χ (Units.mk0 (m : ℚ_[p]) (Nat.cast_ne_zero.mpr h))

/-- The **local root number** `W(χ)` (LMFDB `lf.root_number`) of a character `χ` of `ℚ_p^×`, Tate's
local constant `ε(χ |·| ^ (1/2), ψ_p, dx)` for the additive character `ψ_p(x) = e ^ (2πi {x}_p)` and
the self-dual Haar measure: `1` if `χ` is unramified, and otherwise

`χ(p) ^ a p ^ (-a/2) ∑_{u ∈ (ℤ/p^a)^×} χ(u)⁻¹ e ^ (2πi u / p ^ a)`,

where `p ^ a` is the conductor of `χ`, the sum running over the representatives `0 ≤ u < p ^ a`
prime to `p`. Through local class field theory it is the local root number of a character of
`Gal(ℚ̄_p/ℚ_p)`. -/
noncomputable def tateRootNumber : ℂ :=
  letI a : ℕ := charConductorExponent χ
  if a = 0 then 1 else charValueNat χ p ^ a *
    (∑ m ∈ (Finset.range (p ^ a)).filter p.Coprime,
      (charValueNat χ m)⁻¹ * ZMod.stdAddChar (m : ZMod (p ^ a))) / ((p ^ a : ℕ) : ℂ) ^ (1 / 2 : ℂ)

variable {χ}

lemma charConductorExponent_eq_zero (h : IsTrivialOnUnitsMod χ 0) : charConductorExponent χ = 0 :=
  Nat.sInf_eq_zero.mpr <| .inl h

/-- **An unramified character has local root number `1`.** -/
lemma tateRootNumber_eq_one (h : IsTrivialOnUnitsMod χ 0) : tateRootNumber χ = 1 := by
  rw [tateRootNumber, ite_eq_left (charConductorExponent_eq_zero h)]

lemma sum_range_coprime_eq_gaussSum {a : ℕ} (ψ : DirichletCharacter ℂ (p ^ a)) (ha : a ≠ 0) :
    ∑ m ∈ (Finset.range (p ^ a)).filter p.Coprime, ψ m * ZMod.stdAddChar (m : ZMod (p ^ a)) =
      gaussSum ψ ZMod.stdAddChar := by
  rw [gaussSum, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun m _ ↦ ?_).trans (Finset.sum_nbij' (fun m ↦ (m : ZMod (p ^ a)))
    ZMod.val (fun _ _ ↦ Finset.mem_univ _) (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x))
    (fun m hm ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hm)) (fun x _ ↦ ZMod.natCast_zmod_val x)
    fun _ _ ↦ rfl)
  split_ifs with h
  · rfl
  · rw [MulChar.map_nonunit, zero_mul]
    rwa [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero ha),
      Nat.coprime_comm]

variable (ψ : DirichletCharacter ℂ (p ^ charConductorExponent χ))

/-- **The local root number of the local component at `p` of a Dirichlet character** `ψ` modulo
`N = p ^ a` is `τ(ψ) / √N`, where `τ(ψ)` is the Gauss sum: the local component `χ` of the idele
class character of `ψ` at `p` has conductor `p ^ a`, `χ(p) = 1` and `χ(m) = ψ(m)⁻¹` for the integers
`m` prime to `p`; here `a ≥ 1`. -/
lemma tateRootNumber_eq_gaussSum_div (ha : charConductorExponent χ ≠ 0) (hp : charValueNat χ p = 1)
    (hψ : ∀ m, p.Coprime m → charValueNat χ m = (ψ m)⁻¹) : tateRootNumber χ =
      gaussSum ψ ZMod.stdAddChar / ((p ^ charConductorExponent χ : ℕ) : ℂ) ^ (1 / 2 : ℂ) := by
  rw [← sum_range_coprime_eq_gaussSum ψ ha, tateRootNumber, ite_eq_right ha, hp, one_pow, one_mul]
  refine congrArg (· / _) <| Finset.sum_congr rfl fun m hm ↦ ?_
  rw [hψ m (Finset.mem_filter.mp hm).2, inv_inv]

/-- **The local root numbers of a Dirichlet character multiply to its root number**: for a
Dirichlet character `ψ` modulo `p ^ a`, the local components `χ'` at `∞` and `χ` at `p` of its idele
class character, characterised by `χ'(-1) = ψ(-1)`, the conductor `p ^ a` of `χ`, `χ(p) = 1` and
`χ(m) = ψ(m)⁻¹` for the integers `m` prime to `p`, have local root numbers whose product is the
root number of `L(s, ψ)`, Mathlib's `DirichletCharacter.rootNumber`. -/
lemma real_tateRootNumber_mul_tateRootNumber {χ' : ℝˣ →* ℂˣ} (hp : charValueNat χ p = 1)
    (hψ : ∀ m, p.Coprime m → charValueNat χ m = (ψ m)⁻¹) (hψ' : (χ' (-1) : ℂ) = ψ (-1)) :
    Real.tateRootNumber χ' * tateRootNumber χ = ψ.rootNumber := by
  rcases eq_or_ne (charConductorExponent χ) 0 with ha | ha
  · have h₀ : (-1 : ZMod (p ^ charConductorExponent χ)) = 1 := by
      rw [ha]
      exact Subsingleton.elim (α := ZMod 1) _ _
    have h₁ : χ' (-1) = 1 :=
      Units.val_eq_one.mp <| by rw [hψ', h₀, map_one]
    rw [tateRootNumber, ite_eq_left ha, Real.tateRootNumber, ite_eq_left h₁, one_mul]
    revert ψ
    rw [ha]
    exact fun ψ _ _ ↦ ψ.rootNumber_modOne.symm
  rw [tateRootNumber_eq_gaussSum_div ψ ha hp hψ, DirichletCharacter.rootNumber]
  rcases ψ.even_or_odd with h | h
  · rw [Real.tateRootNumber, ite_eq_left (Units.val_eq_one.mp (hψ'.trans h)), ite_eq_left h]
    simp
  · rw [Real.tateRootNumber, ite_eq_right fun h' ↦
      absurd (hψ'.symm.trans (Units.val_eq_one.mpr h')) h.not_even, ite_eq_right h.not_even,
      pow_one, div_I]
    ring1

end Padic
