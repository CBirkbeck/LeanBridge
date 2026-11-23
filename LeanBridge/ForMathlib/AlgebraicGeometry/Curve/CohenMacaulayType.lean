import LeanBridge.ForMathlib.RingTheory.FractionalIdeal.LocallyPrincipalInvertible
import TauCeti.NumberTheory.NumberField.Global.Orders.Gorenstein

/-!
# The Cohen–Macaulay type of an order

An order `R` in an étale algebra `K` over `ℚ`, a finite product of number fields, is a subring of
`K` whose additive group is a lattice of full rank, such as an order in a number field or an
overorder of the Frobenius order of an isogeny class of abelian varieties over a finite field. It
is a one-dimensional Noetherian ring, the coordinate ring of an affine arithmetic curve, and its
trace dual `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` is a canonical module. The Cohen–Macaulay type of `R` is the
minimal number of generators of a canonical module, read locally: at a maximal ideal `𝔩`, the
minimal number of generators of `Rᵗ_𝔩` over `R_𝔩` is, by Nakayama's lemma, the dimension of
`Rᵗ / 𝔩Rᵗ` over `R / 𝔩`, and the type of `R` is the largest of these. The definitions make sense
for any subring of a commutative `ℚ`-algebra; their basic properties are proved in
`LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.GorensteinOrder`, for all orders in
étale `ℚ`-algebras and, among them, for orders in number fields, Tau Ceti's
`TauCeti.GlobalNumberFields.NumberFieldOrder`, whose trace dual is the trace dual here.

An invertible fractional ideal `I` has `I / 𝔩I` of dimension at most one at every maximal ideal
`𝔩`. For a fractional ideal `I` of a Noetherian domain, the dimension is at least one if `I ≠ 0`,
and conversely a nonzero `I` with `I / 𝔩I` of dimension at most one at every maximal ideal is
locally principal by Nakayama's lemma, hence invertible. These are cases of the lemmas of
`LeanBridge.ForMathlib.RingTheory.FractionalIdeal.LocallyPrincipalInvertible`.

## Main definitions

* `Subalgebra.traceDualSubmodule`: the trace dual `Iᵗ` of an `R`-submodule `I` of `K`.
* `Subalgebra.traceDual`: the trace dual `Rᵗ` of a subring `R` of a commutative `ℚ`-algebra.
* `Subalgebra.cohenMacaulayTypeAt`: the dimension of `Rᵗ / 𝔩Rᵗ` over `R / 𝔩`.
* `Subalgebra.cohenMacaulayType` (LMFDB `ag.cohen_macaulay_type`): the Cohen–Macaulay type.
-/

open FractionalIdeal Module Submodule

open scoped nonZeroDivisors

namespace FractionalIdeal

lemma finrank_quotient_smul_top_le_one_of_isUnit {R K : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (𝔩 : Ideal R)
    [h𝔩 : 𝔩.IsMaximal] (hI : IsUnit I) : finrank (R ⧸ 𝔩) (I ⧸ 𝔩 • (⊤ : Submodule R I)) ≤ 1 :=
  residueFinrank_le_one_of_isLocallyPrincipalAt <| isLocallyPrincipalAt_of_isUnit hI h𝔩.ne_top

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {I : FractionalIdeal R⁰ K} (𝔩 : Ideal R) [𝔩.IsMaximal]

lemma one_le_finrank_quotient_smul_top (hI : I ≠ 0) :
    1 ≤ finrank (R ⧸ 𝔩) (I ⧸ 𝔩 • (⊤ : Submodule R I)) := by
  rcases exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.mpr hI) with ⟨y, hy, hy0⟩
  exact one_le_residueFinrank (fg_of_isNoetherianRing le_rfl I) hy hy0.isUnit

lemma isUnit_of_forall_finrank_quotient_smul_top_le_one (hI : I ≠ 0)
    (h : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → finrank (R ⧸ 𝔪) (I ⧸ 𝔪 • (⊤ : Submodule R I)) ≤ 1) :
    IsUnit I := by
  have hfg : (I : Submodule R K).FG := fg_of_isNoetherianRing le_rfl I
  rcases exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.mpr hI) with ⟨y, hy, hy0⟩
  exact (isUnit_iff_forall_isLocallyPrincipalAt hfg hy hy0.isUnit).mpr fun 𝔪 h𝔪 ↦
    isLocallyPrincipalAt_of_residueFinrank_le_one hfg (h 𝔪 h𝔪)

end FractionalIdeal

namespace Subalgebra

variable {K : Type*} [CommRing K] [Algebra ℚ K] (R : Subalgebra ℤ K)

/-- The **trace dual** `Iᵗ = {x ∈ K | Tr(xI) ⊆ ℤ}` of an `R`-submodule `I` of `K`, for a subring `R`
of a commutative `ℚ`-algebra `K` and the trace `Tr` of `K` over `ℚ`, as an `R`-submodule of `K`.
For `I = R` it is the trace dual `Rᵗ` of `R` (`Subalgebra.traceDual`). -/
noncomputable def traceDualSubmodule (I : Submodule R K) : Submodule R K where
  __ := (Algebra.traceForm ℚ K).dualSubmodule (I.restrictScalars ℤ)
  smul_mem' c x hx a ha := by
    rw [Algebra.traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (I.smul_mem c ha)

variable {R} in
lemma mem_traceDualSubmodule {I : Submodule R K} {x : K} :
    x ∈ R.traceDualSubmodule I ↔ ∀ y ∈ I, Algebra.trace ℚ K (x * y) ∈ (algebraMap ℤ ℚ).range :=
  ⟨fun h y hy ↦ mem_one.mp (h y hy), fun h y hy ↦ mem_one.mpr (h y hy)⟩

/-- The **trace dual** `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` of a subring `R` of a commutative `ℚ`-algebra
`K`, for the trace `Tr` of `K` over `ℚ`: the dual of `R` for the trace form, as an `R`-submodule of
`K`, the trace dual `Subalgebra.traceDualSubmodule` of `R` itself. For an order in a number field it
is, by definition, Tau Ceti's `TauCeti.GlobalNumberFields.NumberFieldOrder.traceDual`. -/
noncomputable def traceDual : Submodule R K :=
  R.traceDualSubmodule 1

lemma mem_traceDual {x : K} :
    x ∈ R.traceDual ↔ ∀ y ∈ R, Algebra.trace ℚ K (x * y) ∈ (algebraMap ℤ ℚ).range := by
  refine ⟨fun h y hy ↦ mem_one.mp (h y (mem_one.mpr ⟨⟨y, hy⟩, rfl⟩)), fun h y hy ↦ ?_⟩
  rcases mem_one.mp hy with ⟨y, rfl⟩
  exact mem_one.mpr (h _ y.2)

variable (𝔩 : Ideal R)

/-- The **Cohen–Macaulay type of `R` at a maximal ideal `𝔩`**, for a subring `R` of a commutative
`ℚ`-algebra: the dimension of `Rᵗ / 𝔩Rᵗ` over the residue field `R / 𝔩`, for the trace dual `Rᵗ`.
For an order in an étale algebra over `ℚ` it is, by Nakayama's lemma, the minimal number of
generators of the localisation `Rᵗ_𝔩`, a canonical module of the local ring `R_𝔩`, so it is the
Cohen–Macaulay type of `R_𝔩`. -/
noncomputable def cohenMacaulayTypeAt : ℕ :=
  finrank (R ⧸ 𝔩) (R.traceDual ⧸ 𝔩 • (⊤ : Submodule R R.traceDual))

/-- The **Cohen–Macaulay type** (LMFDB `ag.cohen_macaulay_type`) of an order `R` in an étale algebra
`K` over `ℚ`, a finite product of number fields: the largest dimension of `Rᵗ / 𝔩Rᵗ` over `R / 𝔩`,
for `𝔩` running over the maximal ideals of `R` and `Rᵗ = {a ∈ K | Tr(aR) ⊆ ℤ}` the trace dual. The
LMFDB defines it as the minimal number of generators of a canonical module of `R`, which `Rᵗ` is,
and computes it by this formula; that minimal number must be read locally, as the largest of the
minimal numbers of generators of the localisations `Rᵗ_𝔩` (`Subalgebra.cohenMacaulayTypeAt`), since
a canonical module is only determined up to an invertible module, which need not be principal.
Canonical modules are not available, so the formula is the definition, here for any subring of a
commutative `ℚ`-algebra. For an order in an étale algebra the trace form is nondegenerate, so `Rᵗ`
is a finitely generated `R`-module and the supremum is attained
(`Subalgebra.exists_cohenMacaulayTypeAt_eq_cohenMacaulayType_of_isLattice`). -/
noncomputable def cohenMacaulayType : ℕ :=
  ⨆ 𝔩 : MaximalSpectrum R, R.cohenMacaulayTypeAt 𝔩.asIdeal

end Subalgebra

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) (𝔩 : Ideal O.toSubalgebra)

lemma traceDual_toSubalgebra : O.toSubalgebra.traceDual = O.traceDual :=
  rfl

lemma cohenMacaulayTypeAt_toSubalgebra : O.toSubalgebra.cohenMacaulayTypeAt 𝔩 = finrank
    (O.toSubalgebra ⧸ 𝔩) (O.traceDual ⧸ 𝔩 • (⊤ : Submodule O.toSubalgebra O.traceDual)) :=
  rfl

end TauCeti.GlobalNumberFields.NumberFieldOrder
