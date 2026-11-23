import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialInvariance
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# The associated inertias of the segments of the ramification polygon

Let `L / K` be a finite separable extension of nonarchimedean local fields, `K'` its maximal
unramified subextension and `α` a uniformiser of `L`, whose minimal polynomial `φ` over `K'` is
Eisenstein. The associated inertia of a segment `S` of the ramification polygon of `φ` (LMFDB
`lf.associated_inertia`) is the least common multiple of the degrees of the irreducible factors of
the residual polynomial `A_S` of `S`. A change of uniformiser replaces `A_S(x)` by `γ A_S(u x)` for
nonzero `γ` and `u` in the residue field, and the automorphism `q(x) ↦ q(u x)` of the polynomial
ring maps the irreducible factors of `A_S` to those of `γ A_S(u x)`, with the same degrees. So the
associated inertias do not depend on the uniformiser: they are invariants of `L / K`.

## Main definitions

* `Polynomial.factorDegreeLcm`: the least common multiple of the degrees of the irreducible factors
  of a polynomial over a field.
* `IsNonarchimedeanLocalField.associatedInertia` (LMFDB `lf.associated_inertia`): the associated
  inertia of a segment of the ramification polygon.
* `IsNonarchimedeanLocalField.associatedInertias` (LMFDB `lf.associated_inertia`): the associated
  inertias of the segments, in the order of the residual polynomials.

## Main results

* `Polynomial.factorDegreeLcm_C_mul_comp_C_mul_X`: `γ A(u x)` and `A` have the same least common
  multiple of the degrees of their irreducible factors, for `γ, u ≠ 0`.
* `IsNonarchimedeanLocalField.associatedInertias_eq_of_irreducible` (LMFDB `lf.associated_inertia`):
  for a totally ramified separable extension, the associated inertias do not depend on the
  uniformiser.
* `IsNonarchimedeanLocalField.associatedInertias_minpoly_unramifiedExtension_eq_of_irreducible`
  (LMFDB `lf.associated_inertia`): for a finite separable extension `L / K` with maximal unramified
  subextension `K'`, the associated inertias of the Eisenstein polynomials over `K'` of the
  uniformisers of `L` agree: they are invariants of `L / K`.

## References

* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017), Section 4.
-/

open Finset IsDiscreteValuationRing Polynomial TauCeti UniqueFactorizationMonoid ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace Polynomial

variable {k : Type*} [Field k] {A : k[X]} {γ c : k}

open scoped Classical in
variable (A) in
/-- The **least common multiple of the degrees of the irreducible factors** of a polynomial `A`
over a field: that of the degrees of its monic irreducible factors, `1` for a constant. -/
noncomputable def factorDegreeLcm : ℕ :=
  (normalizedFactors A).toFinset.lcm natDegree

open scoped Classical in
variable (A) in
lemma factorDegreeLcm_eq :
    factorDegreeLcm A = ((normalizedFactors A).toFinset.image natDegree).lcm id := by
  rw [factorDegreeLcm, lcm_eq_lcm_image]

open scoped Classical in
lemma mem_image_natDegree_normalizedFactors_iff (hA : A ≠ 0) {d : ℕ} :
    d ∈ (normalizedFactors A).toFinset.image natDegree ↔
      ∃ q : k[X], Irreducible q ∧ q ∣ A ∧ q.natDegree = d := by
  simp only [mem_image, Multiset.mem_toFinset]
  refine ⟨fun ⟨q, hq, hd⟩ ↦ ⟨q, irreducible_of_normalized_factor q hq,
    dvd_of_mem_normalizedFactors hq, hd⟩, fun ⟨q, hq, hdvd, hd⟩ ↦ ?_⟩
  rcases exists_mem_normalizedFactors_of_dvd hA hq hdvd with ⟨q', hq', hqq'⟩
  exact ⟨q', hq', (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hqq')).symm.trans hd⟩

/-- **The least common multiple of the degrees of the irreducible factors of `γ A(u x)`** is that
of `A`, for `γ, u ≠ 0`: the automorphism `q(x) ↦ q(u x)` of `k[x]` maps the irreducible factors of
`A` to those of `A(u x)`, with the same degrees, and `γ` is a unit. -/
lemma factorDegreeLcm_C_mul_comp_C_mul_X (hγ : γ ≠ 0) (hc : c ≠ 0) :
    factorDegreeLcm (C γ * A.comp (C c * X)) = factorDegreeLcm A := by
  classical
  rcases eq_or_ne A 0 with rfl | hA
  · rw [zero_comp, mul_zero]
  have h₁ : (C c * X).comp (C c⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
  have h₂ : (C c⁻¹ * X).comp (C c * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
  let e : k[X] ≃ₐ[k] k[X] := algEquivOfCompEqX _ _ h₁ h₂
  have he (q : k[X]) : e q = q.comp (C c * X) := by
    rw [comp_eq_aeval]
    rfl
  have hdeg (q : k[X]) : (e q).natDegree = q.natDegree := by
    rw [he, natDegree_comp, natDegree_C_mul_X c hc, mul_one]
  have hdeg' (q : k[X]) : (e.symm q).natDegree = q.natDegree := by
    rw [← hdeg, e.apply_symm_apply]
  have hB : C γ * e A ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hγ) ((map_ne_zero_iff e e.injective).mpr hA)
  have hunit : IsUnit (C γ) :=
    isUnit_C.mpr hγ.isUnit
  rw [← he, factorDegreeLcm_eq, factorDegreeLcm_eq]
  refine congrArg (fun s : Finset ℕ ↦ s.lcm id) (Finset.ext fun d ↦ ?_)
  rw [mem_image_natDegree_normalizedFactors_iff hB, mem_image_natDegree_normalizedFactors_iff hA]
  refine ⟨fun ⟨q, hq, hdvd, hd⟩ ↦ ⟨e.symm q, ?_, ?_, (hdeg' q).trans hd⟩,
    fun ⟨q, hq, hdvd, hd⟩ ↦ ⟨e q, ?_, ?_, (hdeg q).trans hd⟩⟩
  · rwa [MulEquiv.irreducible_iff]
  · rw [hunit.dvd_mul_left] at hdvd
    rwa [← map_dvd_iff e, e.apply_symm_apply]
  · rwa [MulEquiv.irreducible_iff]
  · exact ((map_dvd_iff e).mpr hdvd).mul_left (C γ)

end Polynomial

namespace IsNonarchimedeanLocalField

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The **associated inertia** (LMFDB `lf.associated_inertia`) of the segment `S` of the lower
convex hull of the points `(-i, v_L(ρ_i))` of a polynomial `ρ` with right end `(-k, v_L(ρ_k))` and
length `l`, for `kl = (k, l)`: the least common multiple of the degrees of the irreducible factors
of the residual polynomial `A_S` of `S` at `α`. -/
noncomputable def associatedInertia (ρ : L[X]) (α : L) (kl : ℕ × ℕ) : ℕ :=
  factorDegreeLcm (residualPolynomial ρ α kl.1 kl.2)

/-- The **associated inertias** (LMFDB `lf.associated_inertia`) of the segments `S_1, …, S_ℓ` of
the lower convex hull of the points `(-i, v_L(ρ_i))` of a polynomial `ρ`, numbered as the residual
polynomials `A_1, …, A_ℓ`, from the right. -/
noncomputable def associatedInertias (ρ : L[X]) (α : L) : List ℕ :=
  (residualSegments ρ).map (associatedInertia ρ α)

variable {α α' : 𝒪[L]} [Algebra.IsSeparable K L]

/-- **The associated inertias do not depend on the uniformiser** (LMFDB `lf.associated_inertia`):
for a totally ramified separable extension `L / K` of nonarchimedean local fields and two
uniformisers `α`, `α'` of `L`, with minimal polynomials `φ`, `φ'` over `K`, the associated inertias
of the segments of the ramification polygons of `φ` and `φ'` agree: the residual polynomial of a
segment changes from `A(x)` to `γ A(u x)` with `γ, u ≠ 0`. -/
lemma associatedInertias_eq_of_irreducible (hKL : IsTotallyRamified K L) (hα : Irreducible α)
    (hα' : Irreducible α') :
    associatedInertias (ramificationPolynomial (minpoly K (α' : L)) (α' : L)) (α' : L) =
      associatedInertias (ramificationPolynomial (minpoly K (α : L)) (α : L)) (α : L) := by
  rw [associatedInertias, associatedInertias, residualSegments_eq_of_irreducible hKL hα hα']
  refine List.map_congr_left fun kl hkl ↦ ?_
  rcases associated_of_irreducible _ hα hα' with ⟨u, hu⟩
  have hu' : α' = u * α := by
    rw [← hu, mul_comm]
  have hu₀ : IsLocalRing.residue 𝒪[L] (u : 𝒪[L]) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr u.isUnit
  rw [associatedInertia, associatedInertia,
    residualPolynomial_eq_of_irreducible hKL hα hα' u hu' hkl]
  exact factorDegreeLcm_C_mul_comp_C_mul_X (zpow_ne_zero _ hu₀) (zpow_ne_zero _ hu₀)

/-- **The associated inertias are invariants of `L / K`** (LMFDB `lf.associated_inertia`): for a
finite separable extension `L / K` of nonarchimedean local fields with maximal unramified
subextension `K'`, over which `L` is totally ramified, and two uniformisers `α`, `α'` of `L`, whose
minimal polynomials `φ`, `φ'` over `K'` are Eisenstein, the associated inertias of the segments of
the ramification polygons of `φ` and `φ'` agree. -/
lemma associatedInertias_minpoly_unramifiedExtension_eq_of_irreducible (hα : Irreducible α)
    (hα' : Irreducible α') :
    associatedInertias (ramificationPolynomial
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α' : L)) (α' : L)) (α' : L) =
        associatedInertias (ramificationPolynomial
          (minpoly (unramifiedExtension K L (inertiaDegree K L)) (α : L)) (α : L)) (α : L) := by
  have hsep : Algebra.IsSeparable (unramifiedExtension K L (inertiaDegree K L)) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K _ L
  exact associatedInertias_eq_of_irreducible
    (isTotallyRamified_unramifiedExtension_inertiaDegree K L) hα hα'

end IsNonarchimedeanLocalField
