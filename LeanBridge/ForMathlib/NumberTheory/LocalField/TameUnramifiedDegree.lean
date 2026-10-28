import LeanBridge.ForMathlib.FieldTheory.AlgebraGaloisClosure
import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# Tame and unramified degrees of an extension of local fields

Let `L / K` be a finite extension of nonarchimedean local fields, with maximal unramified
subextension `L^un = unramifiedExtension K L f`, where `f = inertiaDegree K L`. Tau Ceti shows
`[L^un : K] = f` and `[L : L^un] = e = ramificationIndex K L`.

## Main definitions

* `IsNonarchimedeanLocalField.tameDegree` (LMFDB `lf.tame_degree`): the prime-to-`p` part of
  `e = [L : L^un]`.
* `IsNonarchimedeanLocalField.galoisTameDegree` (LMFDB `lf.tame_degree`): the tame degree of the
  Galois closure.
* `IsNonarchimedeanLocalField.galoisUnramifiedDegree` (LMFDB `lf.unramified_degree`): the
  unramified degree of the Galois closure.

The unramified degree `[L^un : K]` itself (LMFDB `lf.unramified_degree`) is Tau Ceti's
`TauCeti.inertiaDegree K L`, by `TauCeti.finrank_unramifiedExtension_inertiaDegree`.

## Main theorems

* `IsNonarchimedeanLocalField.ordProj_mul_tameDegree`: `[L : L^un] = p ^ m * t` with `t` the tame
  degree.
* `IsNonarchimedeanLocalField.not_dvd_tameDegree`: `p` does not divide the tame degree.
-/

open ValuativeRel TauCeti

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]

/-- The **tame degree** (LMFDB `lf.tame_degree`) of an extension `L / K` of nonarchimedean local
fields: the integer `t` with `[L : L^un] = p ^ m * t` and `p ∤ t`, where `p` is the residue
characteristic and `L^un` the maximal unramified subextension. Since `[L : L^un]` is the
ramification index `e(L / K)`, this is the prime-to-`p` part of `e(L / K)`. -/
noncomputable def tameDegree : ℕ :=
  ordCompl[ringChar 𝓀[K]] (ramificationIndex K L)

variable [ValuativeExtension K L]

/-- The degree of `L` over its maximal unramified subextension is `p ^ m` times the tame degree. -/
lemma ordProj_mul_tameDegree : ordProj[ringChar 𝓀[K]] (ramificationIndex K L) * tameDegree K L =
    Module.finrank (unramifiedExtension K L (inertiaDegree K L)) L := by
  rw [finrank_unramifiedExtension_inertiaDegree_eq_ramificationIndex]
  exact Nat.ordProj_mul_ordCompl_eq_self _ _

/-- The residue characteristic does not divide the tame degree. -/
lemma not_dvd_tameDegree : ¬ringChar 𝓀[K] ∣ tameDegree K L :=
  Nat.not_dvd_ordCompl (CharP.char_is_prime 𝓀[K] _) ramificationIndex_pos.ne'

/-- The **Galois tame degree** (LMFDB `lf.tame_degree`) of a finite extension `E / K` of a
nonarchimedean local field: the tame degree of its Galois closure `Algebra.galoisClosure K E` (the
normal closure of `E` in `AlgebraicClosure K`, Galois when `E / K` is separable, as it is for
`p`-adic fields), equipped with Tau Ceti's spectral-norm local-field structure. -/
noncomputable def galoisTameDegree : ℕ :=
  letI : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  tameDegree K (Algebra.galoisClosure K E)

/-- The **Galois unramified degree** (LMFDB `lf.unramified_degree`) of a finite extension `E / K`
of a nonarchimedean local field: the unramified degree, i.e. residue degree, of its Galois closure
`Algebra.galoisClosure K E`, equipped with Tau Ceti's spectral-norm local-field structure. -/
noncomputable def galoisUnramifiedDegree : ℕ :=
  letI : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  haveI : ValuativeExtension K (Algebra.galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  inertiaDegree K (Algebra.galoisClosure K E)

end IsNonarchimedeanLocalField
