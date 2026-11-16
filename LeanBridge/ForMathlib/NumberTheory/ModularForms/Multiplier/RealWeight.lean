import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Weight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.Basic

/-!
# Multiplier systems of real weight

Let `k` be a real number and `Γ` a subgroup of `GL(2, ℝ)`. A **multiplier system** of weight `k`
on `Γ` is a function `v : Γ → S¹` with the consistency condition

`v(γδ) j(γδ, z)^k = v(γ) v(δ) j(γ, δz)^k j(δ, z)^k` for all `γ, δ ∈ Γ` and `z ∈ ℍ`,

where `j(γ, z) = cz + d` for `γ = (a, b; c, d)` and the powers are principal, and with
`v(-I) = e^{-πik}` when `-I ∈ Γ`. In Strömberg's form (Definition 2.2 of his paper, the source of
the LMFDB's Maass forms with multiplier systems) the consistency condition reads
`v(γδ) = σ_k(γ, δ) v(γ) v(δ)`, with `σ_k(γ, δ) = j_γ(δz; k) j_δ(z; k) j_{γδ}(z; k)⁻¹` and
`j_γ(z; k) = e^{ik Arg(cz + d)}`; it is the same condition, as `w^k = |w|^k e^{ik Arg w}` and
`|j(γδ, z)| = |j(γ, δz)| |j(δ, z)|`.

The conditions are those that the transformation law `exp(-ik Arg(cz + d)) f(γz) = v(γ) f(z)` of
the LMFDB's Maass forms of weight `k` (`mf.maass.mwf`) imposes on the multiplier `v` of a function
`f` that is not identically zero: for `Γ` in `SL(2, ℝ)`, the law at `γ`, `δ` and `γδ` gives the
consistency condition at every point where `f ≠ 0`, and the law at `-I`, which fixes every point,
gives `v(-I) = e^{-πik}`. Once `Γ` has a multiplier system `u` of weight `k` (on subgroups of
`SL(2, ℤ)`, the eta multiplier), the condition at one point is enough: `v / u` is then a
character, and `v = (v / u) u` satisfies it everywhere.

Products of multiplier systems are multiplier systems, of the sum of the weights, and the inverse
of a multiplier system of weight `k` has weight `-k`. For `Γ` in `SL(2, ℝ)`, the cocycle relation
`j(γδ, z) = j(γ, δz) j(δ, z)` gives:
* in integral weight `n`, the multiplier systems are the homomorphisms `v : Γ → S¹` with
  `v(-I) = (-1)^n`, the LMFDB's multiplier systems of integral weight (`mf.multipliersystem`,
  `MonoidHom.IsMultiplierSystem`);
* the quotient of two multiplier systems of the same weight is a character of `Γ`, trivial at
  `-I`;
* the multiplier systems of weight `k` and of weight `k + 2m`, `m ∈ ℤ`, are the same.

## Main definitions

* `ModularForm.IsMultiplierSystemOfWeight` (LMFDB `mf.maass.mwf`): multiplier systems of real
  weight.
* `ModularForm.IsMultiplierSystemOfWeight.divMonoidHom`: the quotient of two multiplier systems of
  the same weight, as a character.

## Main results

* `ModularForm.IsMultiplierSystemOfWeight.mul`, `ModularForm.IsMultiplierSystemOfWeight.inv`:
  products and inverses of multiplier systems.
* `ModularForm.IsMultiplierSystemOfWeight.map_mul`: a multiplier system of integral weight on a
  subgroup of `SL(2, ℝ)` is a homomorphism.
* `ModularForm.isMultiplierSystemOfWeight_intCast_iff` (LMFDB `mf.multipliersystem`): in integral
  weight, a homomorphism is a multiplier system exactly in the sense of
  `MonoidHom.IsMultiplierSystem`.
* `ModularForm.IsMultiplierSystemOfWeight.divMonoidHom_neg_one`: the quotient of two multiplier
  systems of the same weight is a character trivial at `-I`.
* `ModularForm.isMultiplierSystemOfWeight_add_two_mul_iff`: the multiplier systems of weight
  `k + 2m` are those of weight `k`.
* `ModularForm.IsMultiplierSystemOfWeight.of_maassSlash`: if `Γ` has a multiplier system of
  weight `k`, the multiplier of a function that is not identically zero and satisfies the
  transformation law of weight `k` is a multiplier system.
* `UpperHalfPlane.IsMaassFormOfWeight.isMultiplierSystemOfWeight` (LMFDB `mf.maass.mwf`): the same
  for the multiplier of a nonzero Maass form of weight `k`.

## References

* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp. 77
  (2008), 2375–2416, Definition 2.2.
* M. I. Knopp, *Modular Functions in Analytic Number Theory*, Markham, 1970.
-/

open Complex UpperHalfPlane Subgroup ModularForm

open scoped MatrixGroups Real

lemma Circle.exp_neg_pi_mul_intCast (n : ℤ) : Circle.exp (-(π * n)) = (-1) ^ n := by
  refine Circle.ext ?_
  rw [Circle.coe_exp, Circle.coe_zpow, Circle.coe_neg, Circle.coe_one, ← inv_neg_one, inv_zpow',
    ← exp_pi_mul_I, ← exp_int_mul]
  congr 1
  push_cast
  ring1

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k l : ℝ} {v u : Γ → Circle} {f : ℂ → ℂ} {z : ℍ}
    {eigenvalue : ℂ}

namespace UpperHalfPlane

variable (k f z) in
lemma maassSlash_mul_cpow (g : GL (Fin 2) ℝ) :
    maassSlash k f g z * denom g z ^ (k : ℂ) = (‖denom g z‖ ^ k : ℝ) * f ↑(g • z) := by
  rw [maassSlash, mul_right_comm, exp_neg_arg_mul_cpow k (denom_ne_zero g z)]

end UpperHalfPlane

namespace ModularForm

variable (Γ k v) in
/-- A function `v : Γ → S¹` on a subgroup `Γ` of `GL(2, ℝ)` is a **multiplier system of real weight
`k`** (LMFDB `mf.maass.mwf`) if `v(γδ) j(γδ, z)^k = v(γ) v(δ) j(γ, δz)^k j(δ, z)^k` for all
`γ, δ ∈ Γ` and `z ∈ ℍ`, where `j(γ, z) = cz + d` and the powers are principal, and
`v(-I) = e^{-πik}` if `-I ∈ Γ` (Strömberg, Definition 2.2, with the knowl's branch `Arg ∈ (-π, π]`
of the argument). These are the conditions that the unitary transformation law
`exp(-ik Arg(cz + d)) f(γz) = v(γ) f(z)` of Maass forms of weight `k` imposes on the multiplier of a
function that is not identically zero (`IsMultiplierSystemOfWeight.of_maassSlash`, on a group that
has some multiplier system of weight `k`, such as `SL(2, ℤ)`). The knowl `mf.multipliersystem`
defines multiplier systems of integral weight only, as homomorphisms; on a subgroup of `SL(2, ℝ)`
and for an integral `k` this notion is that one (`isMultiplierSystemOfWeight_intCast_iff`), while
for other `k` a multiplier system need not be a homomorphism (it never is on a group containing
`-I`), as the eta multiplier `v_η^{2k}` (`ModularForm.etaMultiplier`) shows. -/
structure IsMultiplierSystemOfWeight : Prop where
  /-- The consistency condition `v(γδ) j(γδ, z)^k = v(γ) v(δ) j(γ, δz)^k j(δ, z)^k`. -/
  mul_cpow_denom (γ δ : Γ) (z : ℍ) : (v (γ * δ) : ℂ) * denom ↑(γ * δ) z ^ (k : ℂ) =
    v γ * v δ * denom γ ↑((δ : GL (Fin 2) ℝ) • z) ^ (k : ℂ) * denom δ z ^ (k : ℂ)
  /-- The value `v(-I) = e^{-πik}` at `-I`, when `-I ∈ Γ`. -/
  neg_one (h : -1 ∈ Γ) : v ⟨-1, h⟩ = Circle.exp (-(π * k))

namespace IsMultiplierSystemOfWeight

/-- **The product of multiplier systems of weights `k` and `l` is a multiplier system of weight
`k + l`**. -/
lemma mul (hv : IsMultiplierSystemOfWeight Γ k v) (hu : IsMultiplierSystemOfWeight Γ l u) :
    IsMultiplierSystemOfWeight Γ (k + l) (v * u) := by
  have h (g : GL (Fin 2) ℝ) (w : ℍ) :
      denom g w ^ ((k + l : ℝ) : ℂ) = denom g w ^ (k : ℂ) * denom g w ^ (l : ℂ) := by
    rw [ofReal_add, cpow_add _ _ (denom_ne_zero g w)]
  refine ⟨fun γ δ z ↦ ?_, fun h1 ↦ ?_⟩
  · simp only [Pi.mul_apply, Circle.coe_mul, h]
    linear_combination (u (γ * δ) * denom ↑(γ * δ) z ^ (l : ℂ)) * hv.mul_cpow_denom γ δ z +
      (v γ * v δ * denom γ ↑((δ : GL (Fin 2) ℝ) • z) ^ (k : ℂ) * denom δ z ^ (k : ℂ)) *
        hu.mul_cpow_denom γ δ z
  · rw [Pi.mul_apply, hv.neg_one h1, hu.neg_one h1, ← Circle.exp_add]
    congr 1
    ring1

/-- **The inverse of a multiplier system of weight `k` is a multiplier system of weight `-k`**. -/
lemma inv (hv : IsMultiplierSystemOfWeight Γ k v) : IsMultiplierSystemOfWeight Γ (-k) v⁻¹ := by
  refine ⟨fun γ δ z ↦ ?_, fun h1 ↦ ?_⟩
  · simp only [Pi.inv_apply, Circle.coe_inv, ofReal_neg, cpow_neg, ← mul_inv, hv.mul_cpow_denom]
  · rw [Pi.inv_apply, hv.neg_one h1, ← Circle.exp_neg]
    congr 1
    ring1

end IsMultiplierSystemOfWeight

lemma neg_one_of_maassSlash (h : ∀ (γ : Γ) (z : ℍ), maassSlash k f γ z = v γ * f z) (hz : f z ≠ 0)
    (h1 : -1 ∈ Γ) : v ⟨-1, h1⟩ = Circle.exp (-(π * k)) := by
  have e : maassSlash k f (-1) z = v ⟨-1, h1⟩ * f z := h ⟨-1, h1⟩ z
  rw [maassSlash, UpperHalfPlane.neg_smul, one_smul, denom_neg, denom_one, arg_neg_one] at e
  refine Circle.ext ?_
  rw [Circle.coe_exp, ← mul_right_cancel₀ hz e]
  congr 1
  push_cast
  ring1

variable [Γ.HasDetOne]

variable (z) in
lemma denom_coe_mul (γ δ : Γ) :
    denom ↑(γ * δ) z = denom γ ↑((δ : GL (Fin 2) ℝ) • z) * denom δ z := by
  rw [Subgroup.coe_mul, denom_cocycle_σ]
  simp [σ, HasDetOne.det_eq δ.2]

/-- **A multiplier system of integral weight is a homomorphism**, on a subgroup `Γ` of
`SL(2, ℝ)`: the cocycle relation `j(γδ, z) = j(γ, δz) j(δ, z)` turns the consistency condition in
weight `n ∈ ℤ` into `v(γδ) = v(γ) v(δ)`. -/
lemma IsMultiplierSystemOfWeight.map_mul {n : ℤ} (hv : IsMultiplierSystemOfWeight Γ n v) (γ δ : Γ) :
    v (γ * δ) = v γ * v δ := by
  refine Circle.ext <| mul_right_cancel₀ (mul_ne_zero (zpow_ne_zero n <|
    denom_ne_zero γ ((δ : GL (Fin 2) ℝ) • UpperHalfPlane.I))
      (zpow_ne_zero n <| denom_ne_zero δ UpperHalfPlane.I)) ?_
  simpa only [ofReal_intCast, cpow_intCast, denom_coe_mul, mul_zpow, Circle.coe_mul, mul_assoc]
    using hv.mul_cpow_denom γ δ UpperHalfPlane.I

/-- **In integral weight, multiplier systems are the LMFDB's** (`mf.multipliersystem`): on a
subgroup `Γ` of `SL(2, ℝ)`, a homomorphism `χ : Γ → S¹` is a multiplier system of weight `n ∈ ℤ`
in the sense of `IsMultiplierSystemOfWeight` exactly when `χ(-I) = (-1)^n` if `-I ∈ Γ`, that is,
when it is a multiplier system in the sense of `MonoidHom.IsMultiplierSystem`. With
`IsMultiplierSystemOfWeight.map_mul`, the multiplier systems of integral weight are these
homomorphisms. -/
lemma isMultiplierSystemOfWeight_intCast_iff (χ : Γ →* Circle) (n : ℤ) :
    IsMultiplierSystemOfWeight Γ (n : ℝ) χ ↔ χ.IsMultiplierSystem n := by
  refine ⟨fun hχ h1 ↦ (hχ.neg_one h1).trans (Circle.exp_neg_pi_mul_intCast n), fun hχ ↦
    ⟨fun γ δ z ↦ ?_, fun h1 ↦ (hχ h1).trans (Circle.exp_neg_pi_mul_intCast n).symm⟩⟩
  simp only [ofReal_intCast, cpow_intCast, denom_coe_mul, mul_zpow, map_mul, Circle.coe_mul]
  ring1

lemma isMultiplierSystemOfWeight_one_two_mul (m : ℤ) :
    IsMultiplierSystemOfWeight Γ ((2 * m : ℤ) : ℝ) 1 :=
  (isMultiplierSystemOfWeight_intCast_iff 1 (2 * m)).mpr <|
    MonoidHom.isMultiplierSystem_one_iff.mpr fun _ ↦ even_two_mul m

/-- **The multiplier systems of weight `k + 2m` are those of weight `k`**, for every integer `m`,
on a subgroup `Γ` of `SL(2, ℝ)`: the factor `j(γ, z)^{2m}` satisfies the cocycle relation
exactly, and `e^{-πi(k + 2m)} = e^{-πik}`. -/
lemma isMultiplierSystemOfWeight_add_two_mul_iff (m : ℤ) :
    IsMultiplierSystemOfWeight Γ (k + 2 * m) v ↔ IsMultiplierSystemOfWeight Γ k v := by
  refine ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩
  · have h : IsMultiplierSystemOfWeight Γ (k + 2 * m + ((2 * -m : ℤ) : ℝ)) (v * 1) :=
      hv.mul (isMultiplierSystemOfWeight_one_two_mul (-m))
    have hk : k + 2 * m + ((2 * -m : ℤ) : ℝ) = k := by
      push_cast
      ring1
    rwa [hk, mul_one] at h
  · have h : IsMultiplierSystemOfWeight Γ (k + ((2 * m : ℤ) : ℝ)) (v * 1) :=
      hv.mul (isMultiplierSystemOfWeight_one_two_mul m)
    rwa [Int.cast_mul, Int.cast_ofNat, mul_one] at h

namespace IsMultiplierSystemOfWeight

variable (hv : IsMultiplierSystemOfWeight Γ k v) (hu : IsMultiplierSystemOfWeight Γ k u)

/-- **The quotient of two multiplier systems of the same weight is a character**: for multiplier
systems `v` and `u` of weight `k` on a subgroup `Γ` of `SL(2, ℝ)`, the function `γ ↦ v(γ) / u(γ)`,
a multiplier system of weight `0`, as a homomorphism `Γ → S¹`. It is trivial at `-I`
(`divMonoidHom_neg_one`). -/
noncomputable def divMonoidHom : Γ →* Circle :=
  MonoidHom.mk' (v / u) <| map_mul (n := 0) <| by simpa [div_eq_mul_inv] using hv.mul hu.inv

lemma divMonoidHom_apply (γ : Γ) : hv.divMonoidHom hu γ = v γ / u γ :=
  rfl

/-- **The quotient of two multiplier systems of the same weight is trivial at `-I`**. -/
lemma divMonoidHom_neg_one (h1 : -1 ∈ Γ) : hv.divMonoidHom hu ⟨-1, h1⟩ = 1 := by
  rw [divMonoidHom_apply, hv.neg_one h1, hu.neg_one h1, div_self']

end IsMultiplierSystemOfWeight

lemma mul_cpow_denom_of_maassSlash (h : ∀ (γ : Γ) (z : ℍ), maassSlash k f γ z = v γ * f z)
    (hz : f z ≠ 0) (γ δ : Γ) : (v (γ * δ) : ℂ) * denom ↑(γ * δ) z ^ (k : ℂ) =
      v γ * v δ * denom γ ↑((δ : GL (Fin 2) ℝ) • z) ^ (k : ℂ) * denom δ z ^ (k : ℂ) := by
  have e (g : Γ) (w : ℍ) : ((‖denom g w‖ ^ k : ℝ) : ℂ) * f ↑((g : GL (Fin 2) ℝ) • w) =
      v g * denom g w ^ (k : ℂ) * f w := by
    rw [← maassSlash_mul_cpow, h]
    ring1
  have hN : ((‖denom ↑(γ * δ) z‖ ^ k : ℝ) : ℂ) =
      ((‖denom γ ↑((δ : GL (Fin 2) ℝ) • z)‖ ^ k : ℝ) : ℂ) * ((‖denom δ z‖ ^ k : ℝ) : ℂ) := by
    rw [denom_coe_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ofReal_mul]
  have hs : ((γ * δ : Γ) : GL (Fin 2) ℝ) • z = (γ : GL (Fin 2) ℝ) • (δ : GL (Fin 2) ℝ) • z := by
    rw [Subgroup.coe_mul, mul_smul]
  have e1 : ((‖denom ↑(γ * δ) z‖ ^ k : ℝ) : ℂ) * f ↑((γ : GL (Fin 2) ℝ) • (δ : GL (Fin 2) ℝ) • z) =
      v (γ * δ) * denom ↑(γ * δ) z ^ (k : ℂ) * f z := by
    rw [← hs]
    exact e (γ * δ) z
  refine mul_right_cancel₀ hz ?_
  linear_combination -e1 + f ↑((γ : GL (Fin 2) ℝ) • (δ : GL (Fin 2) ℝ) • z) * hN +
    ((‖denom δ z‖ ^ k : ℝ) : ℂ) * e γ ((δ : GL (Fin 2) ℝ) • z) +
      (v γ * denom γ ↑((δ : GL (Fin 2) ℝ) • z) ^ (k : ℂ)) * e δ z

/-- **The multiplier of a function with the transformation law of weight `k` is a multiplier
system**, on a subgroup `Γ` of `SL(2, ℝ)` with a multiplier system `u` of weight `k` (on a
subgroup of `SL(2, ℤ)`, the eta multiplier): if `exp(-ik Arg(cz + d)) f(γz) = v(γ) f(z)` for every
`γ ∈ Γ` and `z ∈ ℍ`, and `f` is not zero at some point of `ℍ`, then `v` is a multiplier system of
weight `k`. The law gives the consistency condition at the points where `f ≠ 0`, so `v / u` is a
character, and `v = (v / u) u`. -/
lemma IsMultiplierSystemOfWeight.of_maassSlash (hu : IsMultiplierSystemOfWeight Γ k u)
    (h : ∀ (γ : Γ) (z : ℍ), maassSlash k f γ z = v γ * f z) (hz : f z ≠ 0) :
    IsMultiplierSystemOfWeight Γ k v := by
  refine ⟨fun γ δ w ↦ ?_, neg_one_of_maassSlash h hz⟩
  have hY : denom γ ↑((δ : GL (Fin 2) ℝ) • z) ^ (k : ℂ) * denom δ z ^ (k : ℂ) ≠ 0 :=
    mul_ne_zero (cpow_ne_zero_iff.mpr <| .inl <| denom_ne_zero _ _)
      (cpow_ne_zero_iff.mpr <| .inl <| denom_ne_zero _ _)
  have key : (v (γ * δ) : ℂ) * u γ * u δ = v γ * v δ * u (γ * δ) :=
    mul_right_cancel₀ hY <| by
      linear_combination (u (γ * δ) : ℂ) * mul_cpow_denom_of_maassSlash h hz γ δ -
        (v (γ * δ) : ℂ) * hu.mul_cpow_denom γ δ z
  refine mul_left_cancel₀ (Circle.coe_ne_zero (u (γ * δ))) ?_
  linear_combination (v (γ * δ) : ℂ) * hu.mul_cpow_denom γ δ w +
    denom γ ↑((δ : GL (Fin 2) ℝ) • w) ^ (k : ℂ) * denom δ w ^ (k : ℂ) * key

end ModularForm

namespace UpperHalfPlane

variable [Γ.HasDetOne] in
/-- **The multiplier of a nonzero Maass form of weight `k` is a multiplier system** (LMFDB
`mf.maass.mwf`), on a subgroup `Γ` of `SL(2, ℝ)` with a multiplier system `u` of weight `k`: if
`f` is a Maass form of weight `k` and multiplier `v` on `Γ` and `f` is not zero at some point of
`ℍ`, then `v` is a multiplier system of weight `k`. On a subgroup of `SL(2, ℤ)` the eta multiplier
is such a `u`. -/
lemma IsMaassFormOfWeight.isMultiplierSystemOfWeight (hf : IsMaassFormOfWeight Γ k f v eigenvalue)
    (hu : IsMultiplierSystemOfWeight Γ k u) (hz : f z ≠ 0) : IsMultiplierSystemOfWeight Γ k v :=
  hu.of_maassSlash hf.2.2.1 hz

end UpperHalfPlane
