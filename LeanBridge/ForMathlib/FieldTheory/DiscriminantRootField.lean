import LeanBridge.ForMathlib.NumberTheory.LocalField.DiscriminantBasis

/-!
# The discriminant root field does not depend on the defining polynomial

Let `K / F` be a finite extension and `f, f'` irreducible polynomials over `F` with roots `x, x'`
generating `K` (LMFDB `nf.discriminant_root_field`). Then `disc f · disc f'` is a square in `F`:
`disc f` is `lc(f) ^ (2n - 2)` times the discriminant of the power basis of `x` (Tau Ceti), and two
bases of `K` over `F` have discriminants differing by the square of the determinant of the change
of basis. So the polynomial discriminant is well defined up to a nonzero square factor, and the
discriminant root field `F(√disc f)` (Tau Ceti's `TauCeti.discrField`) does not depend on `f`.

## Main theorems

* `Polynomial.isSquare_discr_mul_discr` (LMFDB `nf.discriminant_root_field`): `disc f · disc f'`
  is a square in `F`.
* `Polynomial.discrField_eq_discrField` (LMFDB `nf.discriminant_root_field`): the discriminant root
  fields of `f` and `f'` in an algebraically closed field agree.
-/

open Polynomial TauCeti

open scoped IntermediateField

namespace Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {x x' : K} {f f' : F[X]}

lemma discr_eq_pow_mul_discr_minpoly (hf : Irreducible f) (hfx : aeval x f = 0) :
    f.discr = f.leadingCoeff ^ (2 * (minpoly F x).natDegree - 2) * (minpoly F x).discr := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf.ne_zero
  rw [← discr_C_mul _ hlc, ← minpoly.eq_of_irreducible hf hfx, mul_comm, mul_assoc, ← C_mul,
    inv_mul_cancel₀ hlc, C_1, mul_one]

variable [FiniteDimensional F K]

lemma isSquare_discr_minpoly_mul_discr_minpoly (hx : F⟮x⟯ = ⊤) (hx' : F⟮x'⟯ = ⊤) :
    IsSquare ((minpoly F x).discr * (minpoly F x').discr) := by
  have hadj (z : K) (hz : F⟮z⟯ = ⊤) : Algebra.adjoin F {z} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hz, IntermediateField.top_toSubalgebra]
  let pbx : PowerBasis F K := PowerBasis.ofAdjoinEqTop (.of_finite F x) (hadj x hx)
  let pby : PowerBasis F K := PowerBasis.ofAdjoinEqTop (.of_finite F x') (hadj x' hx')
  have h : Algebra.discr F (pby.basis.reindex (pby.basis.indexEquiv pbx.basis)) =
      pbx.basis.det (pby.basis.reindex (pby.basis.indexEquiv pbx.basis)) ^ 2 *
        Algebra.discr F pbx.basis :=
    Algebra.discr_eq_det_sq_mul_discr pbx.basis _
  rw [pby.basis.coe_reindex, Algebra.discr_reindex, Algebra.discr_powerBasis_eq_minpoly_discr,
    Algebra.discr_powerBasis_eq_minpoly_discr, PowerBasis.ofAdjoinEqTop_gen,
    PowerBasis.ofAdjoinEqTop_gen] at h
  rw [h]
  exact ⟨pbx.basis.det (pby.basis ∘ (pby.basis.indexEquiv pbx.basis).symm) * (minpoly F x).discr,
    by ring1⟩

/-- **The polynomial discriminant is well defined up to a square** (LMFDB
`nf.discriminant_root_field`): if `f, f'` are irreducible polynomials over `F` with roots `x, x'`
generating `K`, then `disc f · disc f'` is a square in `F`. -/
lemma isSquare_discr_mul_discr (hf : Irreducible f) (hfx : aeval x f = 0) (hx : F⟮x⟯ = ⊤)
    (hf' : Irreducible f') (hfx' : aeval x' f' = 0) (hx' : F⟮x'⟯ = ⊤) :
    IsSquare (f.discr * f'.discr) := by
  rcases isSquare_discr_minpoly_mul_discr_minpoly hx hx' with ⟨s, hs⟩
  rw [discr_eq_pow_mul_discr_minpoly hf hfx, discr_eq_pow_mul_discr_minpoly hf' hfx']
  have he (n : ℕ) : 2 * n - 2 = (n - 1) + (n - 1) := by
    omega
  refine ⟨f.leadingCoeff ^ ((minpoly F x).natDegree - 1) *
    f'.leadingCoeff ^ ((minpoly F x').natDegree - 1) * s, ?_⟩
  rw [he, he, pow_add, pow_add]
  linear_combination f.leadingCoeff ^ ((minpoly F x).natDegree - 1) *
    f.leadingCoeff ^ ((minpoly F x).natDegree - 1) *
      f'.leadingCoeff ^ ((minpoly F x').natDegree - 1) *
        f'.leadingCoeff ^ ((minpoly F x').natDegree - 1) * hs

open Algebra in
/-- **The discriminant root field is well defined** (LMFDB `nf.discriminant_root_field`): for a
finite separable extension `K / F` and irreducible polynomials `f, f'` over `F` with roots `x, x'`
generating `K`, the discriminant root fields `F(√disc f)` and `F(√disc f')` in an algebraically
closed field `E` agree. -/
lemma discrField_eq_discrField [Algebra.IsSeparable F K] (E : Type*) [Field E] [Algebra F E]
    [IsAlgClosed E] (hf : Irreducible f) (hfx : aeval x f = 0) (hx : F⟮x⟯ = ⊤)
    (hf' : Irreducible f') (hfx' : aeval x' f' = 0) (hx' : F⟮x'⟯ = ⊤) :
    discrField f E = discrField f' E := by
  have hD (g : F[X]) (z : K) (hg : Irreducible g) (hgz : aeval z g = 0) : g.discr ≠ 0 := by
    rw [discr_ne_zero_iff hg.ne_zero]
    exact (IsSeparable.isSeparable F z).of_dvd
      ((minpoly.irreducible (.of_finite F z)).dvd_symm hg (minpoly.dvd F z hgz))
  rcases isSquare_discr_mul_discr hf hfx hx hf' hfx' hx' with ⟨s, hs⟩
  rcases IsAlgClosed.exists_pow_nat_eq (algebraMap F E f.discr) two_pos with ⟨δ, hδ⟩
  have hδ' : (algebraMap F E (s / f.discr) * δ) ^ 2 = algebraMap F E f'.discr := by
    rw [mul_pow, hδ, ← map_pow, ← map_mul, div_pow, sq s, ← hs]
    congr 1
    field_simp [hD f x hf hfx]
  have hc : s / f.discr ≠ 0 := by
    refine div_ne_zero (fun h₀ ↦ hD f' x' hf' hfx' ?_) (hD f x hf hfx)
    rw [h₀, mul_zero] at hs
    exact (mul_eq_zero.1 hs).resolve_left (hD f x hf hfx)
  rw [discrField_eq_adjoin_simple hδ, discrField_eq_adjoin_simple hδ']
  refine le_antisymm (IntermediateField.adjoin_simple_le_iff.2 ?_)
    (IntermediateField.adjoin_simple_le_iff.2 (mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self F δ)))
  have hmem : algebraMap F E (s / f.discr)⁻¹ * (algebraMap F E (s / f.discr) * δ) ∈
      F⟮algebraMap F E (s / f.discr) * δ⟯ :=
    mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F _)
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at hmem

end Polynomial
