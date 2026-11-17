import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.Localization.NormTrace
import TauCeti.Algebra.Module.Lattice
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.BassOrder
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.SingularDimension
import LeanBridge.ForMathlib.RingTheory.Trace.NondegenerateReduced

/-!
# Trace duality and Gorenstein orders in étale algebras

Let `R` be an order in an étale `ℚ`-algebra `K`, a finite product of number fields. The trace form
of `K` over `ℚ` is nondegenerate, so the trace dual `Iᵗ = {x ∈ K | Tr(xI) ⊆ ℤ}` of a fractional
`R`-ideal `I` is again a fractional ideal, and `Iᵗᵗ = I`. The multiplier ring `(I : I)` of `I` is
the trace dual of `I Iᵗ`, so `(I : I) = R` gives `I Iᵗ = Rᵗ`; if moreover `Rᵗ` is invertible, then
so is `I`. Also `(Rᵗ : I) = Iᵗ`, so `(Rᵗ : (Rᵗ : I)) = I`, and in particular `(Rᵗ : Rᵗ) = R`.

The Cohen–Macaulay type of `R` is the largest dimension of `Rᵗ / 𝔩Rᵗ` over `R / 𝔩` for `𝔩` a
maximal ideal (`Subalgebra.cohenMacaulayType`, LMFDB `ag.cohen_macaulay_type`), and `R` is
Gorenstein if it is `1` (`Subalgebra.IsGorenstein`). As `Rᵗ` is finitely generated and contains `1`,
the type is attained and at least `1` (for `K ≠ 0`), and it is `1` exactly when `Rᵗ` is locally
principal, that is invertible. Hence every fractional ideal `I` of a Gorenstein order with
`(I : I) = R` is invertible (LMFDB `av.fq.singular_dimensions`), and conversely an order whose
fractional ideals with `(I : I) = R` are invertible is Gorenstein, as `(Rᵗ : Rᵗ) = R`. This extends
to all orders in étale `ℚ`-algebras what is proved for orders in number fields by Tau Ceti
(`TauCeti.GlobalNumberFields.NumberFieldOrder.IsGorenstein`) and by
`LeanBridge.ForMathlib.AlgebraicGeometry.Curve.CohenMacaulayType`.

## Main definitions

* `Subalgebra.traceDualSubmodule`: the trace dual `Iᵗ` of an `R`-submodule `I` of `K`.
* `Subalgebra.traceDualFractionalIdeal`: the trace dual `Rᵗ` of an order, as a fractional ideal.

## Main results

* `traceForm_nondegenerate_of_etale`: the trace form of an étale `ℚ`-algebra is nondegenerate.
* `Subalgebra.traceDualSubmodule_traceDualSubmodule`: `Iᵗᵗ = I` for a fractional ideal `I`.
* `Subalgebra.div_self_eq_traceDualSubmodule_mul`: `(I : I) = (I Iᵗ)ᵗ`.
* `Subalgebra.traceDual_div_traceDual_div`: `(Rᵗ : (Rᵗ : I)) = I` for a fractional ideal `I`.
* `Subalgebra.cohenMacaulayTypeAt_le_cohenMacaulayType_of_isLattice`,
  `Subalgebra.exists_cohenMacaulayTypeAt_eq_cohenMacaulayType_of_isLattice` and
  `Subalgebra.one_le_cohenMacaulayType_of_isLattice`: the Cohen–Macaulay type of an order is the
  largest of its local types, attained at some maximal ideal, and at least `1`.
* `Subalgebra.IsGorenstein.isUnit_traceDualFractionalIdeal`: the trace dual of a Gorenstein order
  is invertible.
* `Subalgebra.cohenMacaulayType_eq_one_iff_isUnit_traceDualFractionalIdeal`: an order has
  Cohen–Macaulay type `1` if and only if its trace dual is invertible.
* `Subalgebra.IsGorenstein.isUnit_of_div_self_eq_one` (LMFDB `av.fq.singular_dimensions`): a
  fractional ideal `I` of a Gorenstein order with `(I : I) = R` is invertible.
* `Subalgebra.isGorenstein_iff_forall_isUnit_of_isLattice` (LMFDB `ag.cohen_macaulay_type`): an
  order is Gorenstein if and only if its fractional ideals `I` with `(I : I) = R` are invertible.
-/

open Module Submodule

open Algebra (FormallyUnramified traceForm)

open scoped nonZeroDivisors

variable {K : Type*} [CommRing K] [Algebra ℚ K]

variable (K) in
/-- **The trace form of an étale `ℚ`-algebra is nondegenerate**: an étale `ℚ`-algebra is reduced and
finite-dimensional. -/
lemma traceForm_nondegenerate_of_etale [Algebra.Etale ℚ K] : (traceForm ℚ K).Nondegenerate :=
  have : Module.Finite ℚ K := FormallyUnramified.finite_of_free ℚ K
  have : IsReduced K := FormallyUnramified.isReduced_of_field ℚ K
  traceForm_nondegenerate_of_isReduced ℚ K

namespace Submodule

variable [Algebra.Etale ℚ K] (M : Submodule ℤ K) [M.IsLattice ℚ]

lemma dualSubmodule_dualSubmodule_traceForm :
    (traceForm ℚ K).dualSubmodule ((traceForm ℚ K).dualSubmodule M) = M := by
  rw [← Basis.span_range_extendOfIsLattice (Free.chooseBasis ℤ M)]
  exact (traceForm ℚ K).dualSubmodule_dualSubmodule_of_basis (traceForm_nondegenerate_of_etale K)
    (Algebra.traceForm_isSymm ℚ) _

instance : ((traceForm ℚ K).dualSubmodule M).IsLattice ℚ := by
  classical
  rw [← Basis.span_range_extendOfIsLattice (Free.chooseBasis ℤ M),
    (traceForm ℚ K).dualSubmodule_span_of_basis (traceForm_nondegenerate_of_etale K)]
  exact ⟨fg_span (Set.finite_range _), by rw [span_span_of_tower, Basis.span_eq]⟩

end Submodule

namespace Subalgebra

variable (R : Subalgebra ℤ K)

section TraceDualSubmodule

variable (I : Submodule R K)

/-- The **trace dual** `Iᵗ = {x ∈ K | Tr(xI) ⊆ ℤ}` of an `R`-submodule `I` of `K`, for a subring `R`
of a commutative `ℚ`-algebra `K` and the trace `Tr` of `K` over `ℚ`, as an `R`-submodule of `K`.
For `I = R` it is the trace dual `Rᵗ` of `R` (`Subalgebra.traceDual`). -/
noncomputable def traceDualSubmodule : Submodule R K where
  __ := (traceForm ℚ K).dualSubmodule (I.restrictScalars ℤ)
  smul_mem' c x hx a ha := by
    rw [Algebra.traceForm_apply, smul_mul_assoc, mul_comm, ← smul_mul_assoc, mul_comm]
    exact hx _ (I.smul_mem c ha)

variable {R I} in
lemma mem_traceDualSubmodule {x : K} :
    x ∈ R.traceDualSubmodule I ↔ ∀ y ∈ I, Algebra.trace ℚ K (x * y) ∈ (algebraMap ℤ ℚ).range :=
  ⟨fun h y hy ↦ mem_one.mp (h y hy), fun h y hy ↦ mem_one.mpr (h y hy)⟩

lemma restrictScalars_traceDualSubmodule : (R.traceDualSubmodule I).restrictScalars ℤ =
    (traceForm ℚ K).dualSubmodule (I.restrictScalars ℤ) :=
  rfl

lemma traceDualSubmodule_one : R.traceDualSubmodule 1 = R.traceDual :=
  rfl

lemma traceDual_div_eq_traceDualSubmodule : R.traceDual / I = R.traceDualSubmodule I := by
  ext x
  rw [mem_div_iff_forall_mul_mem, mem_traceDualSubmodule]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ R.mem_traceDual.mpr fun r hr ↦ ?_⟩
  · simpa using R.mem_traceDual.mp (h y hy) 1 (one_mem R)
  · rw [mul_assoc]
    exact h _ (by rw [mul_comm]; exact I.smul_mem (⟨r, hr⟩ : R) hy)

variable [Algebra.Etale ℚ K] [(I.restrictScalars ℤ).IsLattice ℚ]

instance : ((R.traceDualSubmodule I).restrictScalars ℤ).IsLattice ℚ := by
  rw [restrictScalars_traceDualSubmodule]
  infer_instance

/-- **Trace duality is perfect on the fractional ideals of an order in an étale `ℚ`-algebra**: the
trace dual of the trace dual of `I` is `I`. -/
lemma traceDualSubmodule_traceDualSubmodule : R.traceDualSubmodule (R.traceDualSubmodule I) = I :=
  Submodule.restrictScalars_injective ℤ R K <|
    dualSubmodule_dualSubmodule_traceForm (I.restrictScalars ℤ)

/-- **The multiplier ring `(I : I)` of a fractional ideal `I` of an order in an étale `ℚ`-algebra is
the trace dual of `I Iᵗ`.** -/
lemma div_self_eq_traceDualSubmodule_mul :
    I / I = R.traceDualSubmodule (I * R.traceDualSubmodule I) := by
  ext x
  rw [mem_div_iff_forall_mul_mem, mem_traceDualSubmodule]
  refine ⟨fun h z hz ↦ ?_, fun h y hy ↦ ?_⟩
  · refine Submodule.mul_induction_on hz (fun a ha b hb ↦ ?_) fun z₁ z₂ h₁ h₂ ↦ ?_
    · have hxab : x * (a * b) = b * (x * a) := by ring1
      rw [hxab]
      exact mem_traceDualSubmodule.mp hb (x * a) (h a ha)
    · rw [mul_add, map_add]
      exact add_mem h₁ h₂
  · rw [← R.traceDualSubmodule_traceDualSubmodule I]
    refine mem_traceDualSubmodule.mpr fun b hb ↦ ?_
    rw [mul_assoc]
    exact h (y * b) (mul_mem_mul hy hb)

/-- **The trace dual `Rᵗ` of an order in an étale `ℚ`-algebra satisfies `(Rᵗ : (Rᵗ : I)) = I`** for
every fractional ideal `I` (in particular `(Rᵗ : Rᵗ) = R`): it is a canonical ideal in the sense of
Herzog and Kunz. -/
lemma traceDual_div_traceDual_div : R.traceDual / (R.traceDual / I) = I := by
  rw [traceDual_div_eq_traceDualSubmodule, traceDual_div_eq_traceDualSubmodule,
    traceDualSubmodule_traceDualSubmodule]

end TraceDualSubmodule

variable [(toSubmodule R).IsLattice ℚ]

lemma isLocalization_algebraMapSubmonoid_of_isLattice :
    IsLocalization (Algebra.algebraMapSubmonoid R ℤ⁰) K := by
  have hR : span ℚ (R : Set K) = ⊤ := IsLattice.span_eq_top (M := toSubmodule R)
  refine (isLocalization_iff _ _).mpr
    ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ⟨1, by rw [Subtype.ext h]⟩⟩
  · rcases y with ⟨-, n, hn, rfl⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ K]
    exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hn))).map _
  · rcases R.exists_natCast_mul_mem_of_span_eq_top hR z with ⟨n, hn, hnz⟩
    have hn' : (n : ℤ) ∈ ℤ⁰ := mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)
    exact ⟨⟨⟨n * z, hnz⟩, ⟨algebraMap ℤ R n, n, hn', rfl⟩⟩, by simp [mul_comm]⟩

lemma trace_mem_range_of_isLattice (x : R) : Algebra.trace ℚ K x ∈ (algebraMap ℤ ℚ).range := by
  have : Module.Free ℤ R := .of_equiv R.toSubmoduleEquiv
  have : IsLocalization (Algebra.algebraMapSubmonoid R ℤ⁰) K :=
    R.isLocalization_algebraMapSubmonoid_of_isLattice
  exact RingHom.mem_range.mpr ⟨_, (Algebra.trace_localization ℤ ℤ⁰ x).symm⟩

lemma one_le_traceDual_of_isLattice : 1 ≤ R.traceDual := fun x hx ↦ by
  rcases mem_one.mp hx with ⟨a, rfl⟩
  exact R.mem_traceDual.mpr fun y hy ↦ by
    simpa using R.trace_mem_range_of_isLattice (a * (⟨y, hy⟩ : R))

lemma one_mem_traceDual_of_isLattice : (1 : K) ∈ R.traceDual :=
  R.one_le_traceDual_of_isLattice (mem_one.mpr ⟨1, map_one _⟩)

lemma isLattice_restrictScalars_of_isUnit {N : Submodule R K} (hN : N.FG) {u : K} (hu : u ∈ N)
    (hu' : IsUnit u) : (N.restrictScalars ℤ).IsLattice ℚ := by
  refine ⟨hN.restrictScalars, eq_top_iff.mpr fun k _ ↦ ?_⟩
  have hle : span ℚ (R : Set K) ≤ (span ℚ (N : Set K)).comap (LinearMap.mulRight ℚ u) :=
    span_le.mpr fun r hr ↦ subset_span (N.smul_mem (⟨r, hr⟩ : R) hu)
  have hk : k * ↑hu'.unit⁻¹ ∈ span ℚ (R : Set K) :=
    (IsLattice.span_eq_top (M := toSubmodule R)).symm ▸ mem_top
  simpa [mul_assoc] using hle hk

instance : ((1 : Submodule R K).restrictScalars ℤ).IsLattice ℚ :=
  R.isLattice_restrictScalars_of_isUnit (by rw [one_eq_span]; exact fg_span_singleton 1)
    (mem_one.mpr ⟨1, map_one _⟩) isUnit_one

variable [Algebra.Etale ℚ K] (𝔩 : Ideal R) [𝔩.IsMaximal]

lemma fg_traceDual_of_isLattice : R.traceDual.FG :=
  FG.of_restrictScalars ℤ (IsLattice.fg (M := (R.traceDualSubmodule 1).restrictScalars ℤ))

/-- The trace dual `Rᵗ = {x ∈ K | Tr(xR) ⊆ ℤ}` of an order `R` in an étale `ℚ`-algebra `K`, as a
fractional ideal of `R` (`Subalgebra.traceDual`). -/
noncomputable def traceDualFractionalIdeal : FractionalIdeal R⁰ K :=
  ⟨R.traceDual, FractionalIdeal.isFractional_of_fg R.fg_traceDual_of_isLattice⟩

lemma coe_traceDualFractionalIdeal : (R.traceDualFractionalIdeal : Submodule R K) = R.traceDual :=
  rfl

lemma bddAbove_range_cohenMacaulayTypeAt_of_isLattice :
    BddAbove (Set.range (R.cohenMacaulayTypeAt ∘ MaximalSpectrum.asIdeal)) := by
  have : Module.Finite R R.traceDual := Finite.iff_fg.mpr R.fg_traceDual_of_isLattice
  rcases Finite.exists_fin (R := R) (M := R.traceDual) with ⟨n, f, hf⟩
  refine ⟨n, ?_⟩
  rintro - ⟨𝔩, rfl⟩
  refine (finrank_le_of_span_eq_top (v := (𝔩.asIdeal • ⊤ : Submodule R R.traceDual).mkQ ∘ f)
    ?_).trans_eq (Fintype.card_fin n)
  rw [← restrictScalars_eq_top_iff R, eq_top_iff]
  refine (span_le_restrictScalars R (R ⧸ 𝔩.asIdeal) _).trans' ?_
  rw [Set.range_comp, ← map_span, hf, Submodule.map_top, range_mkQ]

/-- **The Cohen–Macaulay type of an order in an étale `ℚ`-algebra bounds its local Cohen–Macaulay
types** (LMFDB `ag.cohen_macaulay_type`). -/
lemma cohenMacaulayTypeAt_le_cohenMacaulayType_of_isLattice :
    R.cohenMacaulayTypeAt 𝔩 ≤ R.cohenMacaulayType :=
  le_ciSup R.bddAbove_range_cohenMacaulayTypeAt_of_isLattice ⟨𝔩, ‹_›⟩

lemma one_le_cohenMacaulayTypeAt_of_isLattice : 1 ≤ R.cohenMacaulayTypeAt 𝔩 :=
  one_le_residueFinrank R.fg_traceDual_of_isLattice R.one_mem_traceDual_of_isLattice isUnit_one

variable {R} in
/-- **The trace dual of a Gorenstein order in an étale `ℚ`-algebra is invertible**: Cohen–Macaulay
type `1` says that `Rᵗ` is locally principal at every maximal ideal. -/
lemma IsGorenstein.isUnit_traceDualFractionalIdeal (hR : R.IsGorenstein) :
    IsUnit R.traceDualFractionalIdeal :=
  (FractionalIdeal.isUnit_iff_forall_isLocallyPrincipalAt (I := R.traceDualFractionalIdeal)
    R.fg_traceDual_of_isLattice R.one_mem_traceDual_of_isLattice isUnit_one).mpr fun 𝔩 _ ↦
      isLocallyPrincipalAt_of_residueFinrank_le_one R.fg_traceDual_of_isLattice
        ((R.cohenMacaulayTypeAt_le_cohenMacaulayType_of_isLattice 𝔩).trans_eq hR)

variable {R} in
/-- **A fractional ideal `I` of a Gorenstein order with multiplier ring `(I : I) = R` is
invertible** (LMFDB `av.fq.singular_dimensions`), for orders in étale `ℚ`-algebras: `(I : I) = R`
gives `I Iᵗ = Rᵗ`, which is invertible when `R` is Gorenstein. -/
lemma IsGorenstein.isUnit_of_div_self_eq_one (hR : R.IsGorenstein) {I : FractionalIdeal R⁰ K}
    (hI : ∃ x ∈ I, x ∈ K⁰) (hII : (I : Submodule R K) / I = 1) : IsUnit I := by
  rcases FractionalIdeal.exists_isUnit_mem_of_isLattice hI with ⟨u, hu, hu'⟩
  have hIL : ((I : Submodule R K).restrictScalars ℤ).IsLattice ℚ :=
    R.isLattice_restrictScalars_of_isUnit (FractionalIdeal.fg_coe_of_isNoetherianRing I) hu hu'
  rcases I.isFractional with ⟨a, ha, hIa⟩
  have haJ : algebraMap R K a ∈ R.traceDualSubmodule I := mem_traceDualSubmodule.mpr fun y hy ↦ by
    rcases hIa y hy with ⟨c, hc⟩
    rw [← Algebra.smul_def, ← hc]
    exact R.trace_mem_range_of_isLattice c
  have haK : IsUnit (algebraMap R K a) := IsLocalization.map_units K ⟨a, ha⟩
  have hJ : (R.traceDualSubmodule I).FG := FG.of_restrictScalars ℤ IsLattice.fg
  have : (((I : Submodule R K) * R.traceDualSubmodule I).restrictScalars ℤ).IsLattice ℚ :=
    R.isLattice_restrictScalars_of_isUnit ((FractionalIdeal.fg_coe_of_isNoetherianRing I).mul hJ)
      (mul_mem_mul hu haJ) (hu'.mul haK)
  have hmul : (I : Submodule R K) * R.traceDualSubmodule I = R.traceDual := by
    rw [← R.traceDualSubmodule_traceDualSubmodule ((I : Submodule R K) * _),
      ← div_self_eq_traceDualSubmodule_mul, hII, traceDualSubmodule_one]
  let J : FractionalIdeal R⁰ K := ⟨R.traceDualSubmodule I, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : I * J = R.traceDualFractionalIdeal :=
    FractionalIdeal.coeToSubmodule_inj.mp (by rw [FractionalIdeal.coe_mul]; exact hmul)
  exact isUnit_of_mul_isUnit_left (hIJ ▸ hR.isUnit_traceDualFractionalIdeal)

variable [Nontrivial K]

/-- **The Cohen–Macaulay type of an order in an étale `ℚ`-algebra is attained at some maximal
ideal** (LMFDB `ag.cohen_macaulay_type`): it is the maximum of the dimensions of `Rᵗ / 𝔩Rᵗ` over
`R / 𝔩`. -/
lemma exists_cohenMacaulayTypeAt_eq_cohenMacaulayType_of_isLattice :
    ∃ 𝔩 : MaximalSpectrum R, R.cohenMacaulayTypeAt 𝔩.asIdeal = R.cohenMacaulayType :=
  Nat.sSup_mem (Set.range_nonempty _) R.bddAbove_range_cohenMacaulayTypeAt_of_isLattice

/-- **The Cohen–Macaulay type of an order in an étale `ℚ`-algebra is at least `1`.** -/
lemma one_le_cohenMacaulayType_of_isLattice : 1 ≤ R.cohenMacaulayType :=
  R.exists_cohenMacaulayTypeAt_eq_cohenMacaulayType_of_isLattice.elim fun 𝔩 h𝔩 ↦
    h𝔩 ▸ R.one_le_cohenMacaulayTypeAt_of_isLattice 𝔩.asIdeal

/-- **An order in an étale `ℚ`-algebra has Cohen–Macaulay type `1` if and only if its trace dual
`Rᵗ` is invertible** (LMFDB `ag.cohen_macaulay_type`): type `1` says that `Rᵗ` is locally principal
at every maximal ideal. -/
lemma cohenMacaulayType_eq_one_iff_isUnit_traceDualFractionalIdeal :
    R.cohenMacaulayType = 1 ↔ IsUnit R.traceDualFractionalIdeal := by
  refine ⟨IsGorenstein.isUnit_traceDualFractionalIdeal, fun h ↦ ?_⟩
  refine le_antisymm (ciSup_le' fun 𝔩 ↦ ?_) R.one_le_cohenMacaulayType_of_isLattice
  exact residueFinrank_le_one_of_isLocallyPrincipalAt
    (FractionalIdeal.isLocallyPrincipalAt_of_isUnit h 𝔩.isMaximal.ne_top)

/-- **An order in an étale `ℚ`-algebra is Gorenstein if and only if its fractional ideals with
multiplier ring `R` are invertible** (LMFDB `ag.cohen_macaulay_type`): the trace dual `Rᵗ` has
`(Rᵗ : Rᵗ) = R`. -/
lemma isGorenstein_iff_forall_isUnit_of_isLattice : R.IsGorenstein ↔
    ∀ I : FractionalIdeal R⁰ K, (∃ x ∈ I, x ∈ K⁰) → (I : Submodule R K) / I = 1 → IsUnit I := by
  refine ⟨fun hR I hI hII ↦ hR.isUnit_of_div_self_eq_one hI hII, fun h ↦ ?_⟩
  refine R.cohenMacaulayType_eq_one_iff_isUnit_traceDualFractionalIdeal.mpr <|
    h _ ⟨1, R.one_mem_traceDual_of_isLattice, one_mem _⟩ ?_
  have h1 : R.traceDual / 1 = R.traceDual :=
    (R.traceDual_div_eq_traceDualSubmodule 1).trans R.traceDualSubmodule_one
  rw [coe_traceDualFractionalIdeal]
  nth_rewrite 2 [← h1]
  exact R.traceDual_div_traceDual_div 1

end Subalgebra
