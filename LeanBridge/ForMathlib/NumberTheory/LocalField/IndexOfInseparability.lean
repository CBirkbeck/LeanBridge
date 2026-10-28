import Mathlib.FieldTheory.Minpoly.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.LocalField.Unramified.Existence

/-!
# Indices of inseparability

Let `L / K` be a finite extension of nonarchimedean local fields of residue characteristic `p`, with
maximal unramified subextension `K' = unramifiedExtension K L f`, `n = [L : K'] = u p ^ ν`, and `π`
a uniformizer of `L` with minimal polynomial `X ^ n + c_{n - 1} X ^ {n - 1} + ⋯ + c_0` over `K'`.
Heiermann defines `i_j^π = min {n v_{K'}(c_h) + h - n : 0 ≤ h < n, min(v_p(h), ν) ≤ j}` and the
indices of inseparability `i_j = min {i_{j'}^π + (j' - j) e_L : j ≤ j' ≤ ν}`, with `e_L = v_L(p)`.
That `i_j` does not depend on `π` is a theorem of Heiermann which is not formalised; we define `i_j`
with a chosen uniformizer.

## Main definitions

* `IsNonarchimedeanLocalField.addValuation`: the normalized additive valuation `K → WithTop ℤ`.
* `IsNonarchimedeanLocalField.inseparabilityIndexOf` (LMFDB `lf.indices_of_inseparability`):
  `i_j^π`.
* `IsNonarchimedeanLocalField.inseparabilityIndex` (LMFDB `lf.indices_of_inseparability`): the
  `j`-th index of inseparability `i_j`.
-/

open ValuativeRel TauCeti Finset

namespace IsNonarchimedeanLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open Classical in
variable (K) in
/-- The normalized additive valuation `v_K : K → ℤ ∪ {∞}` of a nonarchimedean local field, with
`v_K(π) = 1` for a uniformizer `π` and `v_K(0) = ∞`. -/
noncomputable def addValuation (x : K) : WithTop ℤ :=
  if h : x = 0 then ⊤ else (normalizedValuation K (Units.mk0 x h)).toAdd

variable (K) (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/-- The index `i_j^π` (LMFDB `lf.indices_of_inseparability`) of a finite extension `L / K` of
nonarchimedean local fields at an element `π` of `L` (a uniformizer in the LMFDB's definition): with
`K'` the maximal unramified subextension (equipped with Tau Ceti's spectral-norm local-field
structure), `n = [L : K'] = u p ^ ν` and `c_h` the coefficients of the minimal polynomial of `π`
over `K'`, the minimum of `n v_{K'}(c_h) + h - n` over the `0 ≤ h < n` with `v̄_p(h) ≤ j`, where
`v̄_p(h) = min(v_p(h), ν)` (so `v̄_p(0) = ν`); it is `∞` when there is no such `h`. -/
noncomputable def inseparabilityIndexOf (π : L) (j : ℕ) : WithTop ℤ :=
  letI K' : IntermediateField K L := unramifiedExtension K L (inertiaDegree K L)
  letI : ValuativeRel K' := finiteIntermediateFieldValuativeRel K L K'
  letI : TopologicalSpace K' := finiteIntermediateFieldTopology K L K'
  haveI : IsNonarchimedeanLocalField K' := finiteIntermediateField_isNonarchimedeanLocalField K L K'
  letI n : ℕ := Module.finrank K' L
  letI ν : ℕ := padicValNat (ringChar 𝓀[K]) n
  ((range n).filter fun h ↦ (if h = 0 then ν else min (padicValNat (ringChar 𝓀[K]) h) ν) ≤ j).inf
    fun h ↦ n • addValuation K' ((minpoly K' π).coeff h) + ((h - n : ℤ) : WithTop ℤ)

/-- The `j`-th **index of inseparability** `i_j` (LMFDB `lf.indices_of_inseparability`) of a finite
extension `L / K` of nonarchimedean local fields, after Heiermann: with `ν = v_p([L : K'])` for the
maximal unramified subextension `K'` and `e_L = v_L(p)`, the minimum of `i_{j'}^π + (j' - j) e_L`
over `j ≤ j' ≤ ν`, for a uniformizer `π` of `L` (a chosen one: Heiermann shows that `i_j` does not
depend on it, which is not formalised). It is meant for `0 ≤ j ≤ ν`. -/
noncomputable def inseparabilityIndex (j : ℕ) : WithTop ℤ :=
  (Icc j (padicValNat (ringChar 𝓀[K])
      (Module.finrank (unramifiedExtension K L (inertiaDegree K L)) L))).inf fun j' ↦
    inseparabilityIndexOf K L (exists_isUniformizer (K := L)).choose j' +
      (j' - j) • addValuation L (ringChar 𝓀[K] : L)

end IsNonarchimedeanLocalField
