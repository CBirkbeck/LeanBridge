import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import Mathlib.GroupTheory.Commensurable

/-!
# Arithmetic and congruence subgroups of `Sp(2g, ℚ)`

A subgroup of `Sp(2g, ℚ)` is arithmetic if it is commensurable with `Sp(2g, ℤ)`, and it is a
congruence subgroup of level `N` if it contains the principal congruence subgroup `Γ(N)`. A Siegel
modular form on `Γ` is of level `N` when `Γ` is a congruence subgroup of level `N`.

## Main definitions

* `SymplecticGroup.integral`: the image of `Sp(2g, ℤ)` in `Sp(2g, ℚ)`.
* `SymplecticGroup.IsArithmetic`: arithmetic subgroups of `Sp(2g, ℚ)`.
* `SymplecticGroup.IsCongruenceOfLevel` (LMFDB `mf.siegel.level`): congruence subgroups of level
  `N`.

## Main results

* `SymplecticGroup.isCongruenceOfLevel_Gamma0`: `Γ₀(N)` is a congruence subgroup of level `N`.
-/

open Matrix

namespace SymplecticGroup

variable (l : Type*) [DecidableEq l] [Fintype l] (N : ℕ) (Γ : Subgroup (symplecticGroup l ℚ))

/-- The **integral symplectic group** `Sp(2g, ℤ)`, as a subgroup of `Sp(2g, ℚ)`. -/
def integral : Subgroup (symplecticGroup l ℚ) :=
  (⊤ : Subgroup (symplecticGroup l ℤ)).map (map (Int.castRingHom ℚ))

variable {l} in
/-- A subgroup `Γ` of `Sp(2g, ℚ)` is **arithmetic** if it is commensurable with `Sp(2g, ℤ)`: both
`Γ ∩ Sp(2g, ℤ)` has finite index in `Γ` and in `Sp(2g, ℤ)`. The LMFDB's Siegel modular forms live
on arithmetic subgroups (LMFDB `mf.siegel`). -/
def IsArithmetic : Prop :=
  Γ.Commensurable (integral l)

lemma isArithmetic_integral : IsArithmetic (integral l) :=
  .refl _

variable {l} in
/-- A subgroup `Γ` of `Sp(2g, ℚ)` is a **congruence subgroup of level `N`** (LMFDB
`group.sp2gr.subgroup.congn`, `mf.siegel.level`) if it contains the principal congruence subgroup
`Γ(N)`; a Siegel modular form on such a `Γ` is said to be of level `N`. The level is not unique:
a congruence subgroup of level `N` is also one of every multiple of `N`. The LMFDB's level is
positive: for `N = 0`, `Γ(0)` is trivial and every subgroup has level `0`. -/
def IsCongruenceOfLevel : Prop :=
  (Gamma l N).map (map (Int.castRingHom ℚ)) ≤ Γ

lemma isCongruenceOfLevel_Gamma :
    IsCongruenceOfLevel N ((Gamma l N).map (map (Int.castRingHom ℚ))) :=
  le_rfl

/-- **`Γ₀(N)` is a congruence subgroup of level `N`.** -/
lemma isCongruenceOfLevel_Gamma0 :
    IsCongruenceOfLevel N ((Gamma0 l N).map (map (Int.castRingHom ℚ))) :=
  Subgroup.map_mono <| Gamma_le_Gamma0 N

variable {l N Γ} in
lemma IsCongruenceOfLevel.mul {M : ℕ} (h : IsCongruenceOfLevel N Γ) :
    IsCongruenceOfLevel (N * M) Γ := by
  refine le_trans (Subgroup.map_mono fun A hA ↦ ?_) h
  rw [mem_Gamma_iff] at hA ⊢
  simpa [Function.comp_def] using
    congrArg (Matrix.map · (ZMod.castHom (dvd_mul_right N M) (ZMod N))) hA

end SymplecticGroup
