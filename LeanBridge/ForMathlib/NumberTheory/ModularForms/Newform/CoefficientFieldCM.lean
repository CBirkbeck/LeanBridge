import Mathlib.NumberTheory.NumberField.CMField
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.CoefficientFieldAlmostAllPrimes
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.LFunctionSign
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint
import TauCeti.NumberTheory.ModularForms.Newforms.SelfDual

/-!
# Self-dual forms, and the coefficient field of a newform: totally real or CM

The dual of a cusp form `f = ∑ aₙ qⁿ` of level `Γ₁(N)` is the form `f̄ = ∑ conj(aₙ) qⁿ`, Tau Ceti's
`CuspForm.conj` (LMFDB `cmf.dualform`), and `f` is self dual if its coefficients are real (LMFDB
`cmf.selfdual`), that is, if `f̄ = f`, or again if the Dirichlet coefficients `aₙ / n^((k-1)/2)` of
its L-function are real, that is, if its L-function is self dual (LMFDB `lfunction.self-dual`).
For a newform, the Dirichlet coefficients of the L-function of `f̄` are the conjugates of those of
`f`, so the L-function of the dual form is the dual of the L-function (LMFDB `lfunction.dual`).

The coefficient field `K = ℚ(f)` of a newform `f` of nebentypus `χ` is totally real if `f` is self
dual, and a CM field otherwise (Ribet, *Galois representations attached to eigenforms with
Nebentypus*, Proposition 3.2). At a prime `p ∤ N`, `conj(a_p) = χ(p)⁻¹ a_p` (Tau Ceti's
`HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_eq_mul_conj`). The Galois conjugate `σ(f)` of `f`
by an automorphism `σ` of `ℂ` is a newform of nebentypus `σ ∘ χ`
(`HeckeRing.GL2.Newform.exists_isGaloisConjugateBy`), so the same relation for `σ(f)` shows that `σ`
and complex conjugation commute on `a_p` for all `p ∤ N`, hence on every `aₙ`, as two automorphisms
of `ℂ` agreeing on almost all `a_p` agree on every coefficient
(`HeckeRing.GL2.Newform.apply_coeff_eq_of_eventually_apply_coeff_eq`). So complex conjugation
preserves `K`, and every embedding `φ : K → ℂ`, which extends to an automorphism of `ℂ`, satisfies
`conj ∘ φ = φ ∘ c` for the restriction `c` of complex conjugation to `K`. If `f` is self dual, then
`c = 1` and every embedding is real; otherwise `c ≠ 1`, every embedding is complex, and `K` is a
quadratic extension of the fixed field of `c`, which is totally real: `K` is a CM field.

## Main definitions

* `CuspForm.IsSelfDual` (LMFDB `cmf.selfdual`): self-dual cusp forms of level `Γ₁(N)`.
* `HeckeRing.GL2.Newform.coefficientFieldConj`: complex conjugation on the coefficient field.

## Main results

* `CuspForm.isSelfDual_iff_conj_eq` (LMFDB `cmf.selfdual`, `cmf.dualform`): a cusp form is self
  dual exactly when it equals its dual.
* `CuspForm.coeff_conj_div_cpow` (LMFDB `cmf.dualform`): the L-function of the dual of a cusp form
  is the dual of its L-function.
* `CuspForm.isSelfDual_iff_forall_conj_div_cpow` (LMFDB `cmf.selfdual`): a cusp form is self dual
  exactly when the Dirichlet coefficients `aₙ / n^((k-1)/2)` of its L-function are real.
* `HeckeRing.GL2.Newform.analyticCoeff_conj` (LMFDB `cmf.dualform`): the L-function of the dual of a
  newform is the dual of its L-function.
* `HeckeRing.GL2.Newform.isSelfDual_iff_forall_conj_analyticCoeff` (LMFDB `cmf.selfdual`): a newform
  is self dual exactly when its L-function is self dual.
* `HeckeRing.GL2.Newform.apply_conj_of_mem_coefficientField`: complex conjugation commutes on the
  coefficient field with every automorphism of `ℂ`.
* `NumberField.IsCMField.of_forall_isConj_of_ne_one`: a number field with a nontrivial automorphism
  that is complex conjugation under every embedding is a CM field.
* `HeckeRing.GL2.Newform.isTotallyReal_coefficientField_iff` (LMFDB `cmf.selfdual`): the
  coefficient field of a newform is totally real exactly when the newform is self dual.
* `HeckeRing.GL2.Newform.isCMField_coefficientField_iff` (LMFDB `cmf.selfdual`, `cmf.dualform`):
  the coefficient field of a newform is a CM field exactly when the newform is not self dual.
-/

open UpperHalfPlane TauCeti NumberField ComplexEmbedding CongruenceSubgroup Matrix
  SpecialLinearGroup

open scoped ComplexConjugate

lemma Complex.conj_natCast_cpow_sub_one_div_two (n : ℕ) (k : ℤ) :
    conj ((n : ℂ) ^ (((k : ℂ) - 1) / 2)) = (n : ℂ) ^ (((k : ℂ) - 1) / 2) := by
  have hs : conj (((k : ℂ) - 1) / 2) = ((k : ℂ) - 1) / 2 := by
    simp [Complex.conj_ofNat]
  rw [← hs, ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
    map_natCast, hs]

namespace CuspForm

variable {N : ℕ} {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- A cusp form `f = ∑ aₙ qⁿ` of level `Γ₁(N)` is **self dual** (LMFDB `cmf.selfdual`) if the
coefficients `aₙ` of its `q`-expansion are real. Equivalently, `f` equals its dual
`f̄ = ∑ conj(aₙ) qⁿ` (`CuspForm.isSelfDual_iff_conj_eq`), and its L-function
`∑ aₙ n^(-(k-1)/2) n^(-s)` is self dual (`CuspForm.isSelfDual_iff_forall_conj_div_cpow`). -/
def IsSelfDual : Prop :=
  ∀ n : ℕ, conj ((qExpansion 1 f).coeff n) = (qExpansion 1 f).coeff n

/-- **A cusp form is self dual exactly when it equals its dual** (LMFDB `cmf.selfdual`,
`cmf.dualform`), the form `f̄ = ∑ conj(aₙ) qⁿ`. -/
lemma isSelfDual_iff_conj_eq : f.IsSelfDual ↔ f.conj (Gamma1_map_le_conjAct_inv_J N) = f := by
  rw [← (CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N)).eq_iff,
    CuspForm.qExpansion_conj one_pos (one_mem_strictPeriods_Gamma1_map N), PowerSeries.ext_iff]
  simp [IsSelfDual]

/-- **The L-function of the dual form is the dual of the L-function** (LMFDB `cmf.dualform`,
`lfunction.dual`): the Dirichlet coefficients `aₙ / n^((k-1)/2)` of the L-function of the dual
`f̄` of a cusp form `f` are the complex conjugates of those of `f`. -/
lemma coeff_conj_div_cpow (n : ℕ) :
    letI s : ℂ := ((k : ℂ) - 1) / 2
    (qExpansion 1 (f.conj (Gamma1_map_le_conjAct_inv_J N))).coeff n / (n : ℂ) ^ s =
      conj ((qExpansion 1 f).coeff n / (n : ℂ) ^ s) := by
  rw [CuspForm.qExpansion_conj one_pos (one_mem_strictPeriods_Gamma1_map N), PowerSeries.coeff_map,
    map_div₀, Complex.conj_natCast_cpow_sub_one_div_two]

lemma conj_div_cpow_eq_iff (n : ℕ) :
    letI a : ℂ := (qExpansion 1 f).coeff n
    conj (a / (n : ℂ) ^ (((k : ℂ) - 1) / 2)) = a / (n : ℂ) ^ (((k : ℂ) - 1) / 2) ↔ conj a = a := by
  rw [map_div₀, Complex.conj_natCast_cpow_sub_one_div_two]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [CuspFormClass.qExpansion_coeff_zero f one_pos (one_mem_strictPeriods_Gamma1_map N)]
  · exact div_left_inj' fun h ↦ hn <| Nat.cast_eq_zero.mp ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- **A cusp form is self dual exactly when its L-function is self dual** (LMFDB `cmf.selfdual`,
`lfunction.self-dual`): the Dirichlet coefficients `aₙ / n^((k-1)/2)` of its L-function, in the
analytic normalisation, are real. -/
lemma isSelfDual_iff_forall_conj_div_cpow : f.IsSelfDual ↔ ∀ n : ℕ,
    letI a : ℂ := (qExpansion 1 f).coeff n
    conj (a / (n : ℂ) ^ (((k : ℂ) - 1) / 2)) = a / (n : ℂ) ^ (((k : ℂ) - 1) / 2) :=
  forall_congr' fun n ↦ (f.conj_div_cpow_eq_iff n).symm

end CuspForm

namespace NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] {σ : K ≃ₐ[ℚ] K}

/-- **A number field with a nontrivial automorphism that is complex conjugation under every complex
embedding is a CM field**: it is totally complex, and a quadratic extension of the fixed field of
the automorphism, which is totally real. Mathlib's `NumberField.IsCMField.of_forall_isConj` assumes
in addition that the field is Galois over `ℚ`. -/
lemma of_forall_isConj_of_ne_one (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) (hσ₁ : σ ≠ 1) :
    IsCMField K := by
  have : IsTotallyComplex K := ⟨fun w ↦ by
    rw [← w.mk_embedding, InfinitePlace.isComplex_mk_iff]
    exact (isConj_ne_one_iff (hσ _)).mp hσ₁⟩
  have hcard : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_isConj_two_of_ne_one (hσ (Classical.arbitrary _)) hσ₁
  have : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  let F : Subfield K := FixedPoints.subfield (Subgroup.zpowers σ) K
  have : IsTotallyReal F := ⟨fun w ↦ by
    rcases w.comap_surjective (K := K) with ⟨W, rfl⟩
    dsimp only
    rw [← W.mk_embedding, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff]
    refine RingHom.ext fun x ↦ ?_
    rw [conjugate_coe_eq, RingHom.comp_apply, starRingEnd_apply, ← (hσ W.embedding).eq]
    exact congrArg W.embedding (x.2 ⟨σ, Subgroup.mem_zpowers σ⟩)⟩
  have : Algebra.IsQuadraticExtension F K := ⟨by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, hcard]⟩
  exact IsCMField.ofCMExtension F K

end NumberField.IsCMField

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)

lemma isSelfDual_iff_isSelfDual_toCuspForm : f.IsSelfDual ↔ f.toCuspForm.IsSelfDual :=
  f.isSelfDual_iff_forall_conj_coeff_eq

/-- **The L-function of the dual of a newform is the dual of its L-function** (LMFDB
`cmf.dualform`, `lfunction.dual`): the Dirichlet coefficients of `L(f̄, s)` are the complex
conjugates of those of `L(f, s)`. -/
lemma analyticCoeff_conj (n : ℕ) : f.conj.analyticCoeff n = conj (f.analyticCoeff n) :=
  f.toCuspForm.coeff_conj_div_cpow n

/-- **A newform is self dual exactly when its L-function is self dual** (LMFDB `cmf.selfdual`,
`lfunction.self-dual`): the Dirichlet coefficients `aₙ` of `L(f, s)` are real. -/
lemma isSelfDual_iff_forall_conj_analyticCoeff :
    f.IsSelfDual ↔ ∀ n : ℕ, conj (f.analyticCoeff n) = f.analyticCoeff n :=
  f.isSelfDual_iff_isSelfDual_toCuspForm.trans f.toCuspForm.isSelfDual_iff_forall_conj_div_cpow

lemma conj_coeff_eq_inv_mul {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    conj ((qExpansion 1 f.toCuspForm).coeff p) =
      (f.χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹ * (qExpansion 1 f.toCuspForm).coeff p := by
  have h : (qExpansion 1 f.toCuspForm).coeff p = f.eigenvalue ⟨p, hp.pos⟩ hpN :=
    f.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN
  rw [eq_inv_mul_iff_mul_eq₀ (Units.ne_zero _), h]
  exact (f.toEigenformAwayFromLevel.eigenvalue_eq_mul_conj hp hpN).symm

lemma apply_conj_coeff (σ : Gal(ℂ/ℚ)) (n : ℕ) : σ (conj ((qExpansion 1 f.toCuspForm).coeff n)) =
    conj (σ ((qExpansion 1 f.toCuspForm).coeff n)) := by
  let c : Gal(ℂ/ℚ) := Complex.conjAe.restrictScalars ℚ
  have hev : ∀ᶠ p in Filter.cofinite, p.Prime →
      (σ * c) ((qExpansion 1 f.toCuspForm).coeff p) =
        (c * σ) ((qExpansion 1 f.toCuspForm).coeff p) := by
    refine Filter.eventually_cofinite.mpr <| (Nat.divisors N).finite_toSet.subset fun p hp ↦ ?_
    refine Nat.mem_divisors.mpr ⟨by_contra fun hpN ↦ hp fun hpp ↦ ?_, NeZero.ne N⟩
    have hcop : p.Coprime N := hpp.coprime_iff_not_dvd.mpr hpN
    have hχ : ((σ • f).χ (ZMod.unitOfCoprime p hcop) : ℂ) = σ (f.χ (ZMod.unitOfCoprime p hcop)) :=
      (f.isGaloisConjugateBy_smul σ).χ_apply _
    simp only [AlgEquiv.mul_apply, c, AlgEquiv.restrictScalars_apply, Complex.conjAe_coe]
    rw [f.conj_coeff_eq_inv_mul hpp hcop, map_mul, map_inv₀, ← f.coeff_smul σ,
      conj_coeff_eq_inv_mul _ hpp hcop, hχ]
  simpa [c] using f.apply_coeff_eq_of_eventually_apply_coeff_eq hev n

/-- **Complex conjugation commutes on the coefficient field with every automorphism of `ℂ`**: for
`x ∈ ℚ(f)` and `σ ∈ Gal(ℂ/ℚ)`, `σ(conj x) = conj(σ x)`. -/
lemma apply_conj_of_mem_coefficientField (σ : Gal(ℂ/ℚ)) {x : ℂ} (hx : x ∈ CoefficientField f) :
    σ (conj x) = conj (σ x) := by
  let c : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.restrictScalars ℚ : Gal(ℂ/ℚ))
  have h : ((σ : ℂ →ₐ[ℚ] ℂ).comp c).comp (CoefficientField f).val =
      (c.comp (σ : ℂ →ₐ[ℚ] ℂ)).comp (CoefficientField f).val :=
    IntermediateField.algHom_ext_of_eq_adjoin ℚ (CoefficientField_def f) <| by
      rintro _ ⟨n, rfl⟩
      exact f.apply_conj_coeff σ n
  exact DFunLike.congr_fun h ⟨x, hx⟩

lemma conj_mem_coefficientField {x : ℂ} (hx : x ∈ CoefficientField f) :
    conj x ∈ CoefficientField f := by
  by_contra h
  rcases IntermediateField.exists_algEquiv_apply_ne_of_notMem h with ⟨σ, hσ, hne⟩
  exact hne <| by rw [f.apply_conj_of_mem_coefficientField σ hx, hσ ⟨x, hx⟩]

/-- **Complex conjugation on the coefficient field** `ℚ(f)` of a newform, which it preserves. -/
noncomputable def coefficientFieldConj : CoefficientField f ≃ₐ[ℚ] CoefficientField f where
  toFun x := ⟨conj (x : ℂ), f.conj_mem_coefficientField x.2⟩
  invFun x := ⟨conj (x : ℂ), f.conj_mem_coefficientField x.2⟩
  left_inv x := Subtype.ext <| Complex.conj_conj _
  right_inv x := Subtype.ext <| Complex.conj_conj _
  map_mul' x y := Subtype.ext <| map_mul _ _ _
  map_add' x y := Subtype.ext <| map_add _ _ _
  commutes' r := Subtype.ext <| by simp

lemma coe_coefficientFieldConj_apply (x : CoefficientField f) :
    (f.coefficientFieldConj x : ℂ) = conj (x : ℂ) :=
  rfl

lemma isConj_coefficientFieldConj (φ : CoefficientField f →+* ℂ) :
    IsConj φ f.coefficientFieldConj := by
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable φ.toRatAlgHom with ⟨σ, hσ⟩
  refine RingHom.ext fun x ↦ ?_
  rw [conjugate_coe_eq, RingHom.comp_apply, RingHom.coe_coe,
    ← φ.toRatAlgHom_apply (f.coefficientFieldConj x), ← hσ, coe_coefficientFieldConj_apply,
    f.apply_conj_of_mem_coefficientField σ x.2, hσ, RingHom.toRatAlgHom_apply]

lemma coefficientFieldConj_eq_one_iff : f.coefficientFieldConj = 1 ↔ f.IsSelfDual := by
  rw [isSelfDual_iff_forall_conj_coeff_eq]
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · have hn : (f.coefficientFieldConj ⟨_, f.qExpansion_coeff_mem_coefficientField n⟩ : ℂ) =
        (qExpansion 1 f.toCuspForm).coeff n := by
      rw [h, AlgEquiv.one_apply]
    rwa [coe_coefficientFieldConj_apply] at hn
  let c : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.restrictScalars ℚ : Gal(ℂ/ℚ))
  have hc : c.comp (CoefficientField f).val = (CoefficientField f).val :=
    IntermediateField.algHom_ext_of_eq_adjoin ℚ (CoefficientField_def f) <| by
      rintro _ ⟨n, rfl⟩
      exact h n
  exact AlgEquiv.ext fun x ↦ Subtype.ext <| DFunLike.congr_fun hc x

/-- **The coefficient field of a newform is totally real exactly when the newform is self dual**
(LMFDB `cmf.selfdual`). -/
lemma isTotallyReal_coefficientField_iff : IsTotallyReal (CoefficientField f) ↔ f.IsSelfDual := by
  rw [← coefficientFieldConj_eq_one_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun w ↦ ?_⟩⟩
  · exact (f.isConj_coefficientFieldConj (CoefficientField f).val.toRingHom).ext <|
      isConj_one_iff.mpr <| InfinitePlace.isReal_mk_iff.mp (h.isReal _)
  · rw [← w.mk_embedding, InfinitePlace.isReal_mk_iff]
    exact isConj_one_iff.mp (h ▸ f.isConj_coefficientFieldConj _)

/-- **The coefficient field of a newform is a CM field exactly when the newform is not self dual**
(LMFDB `cmf.selfdual`, `cmf.dualform`; Ribet). -/
lemma isCMField_coefficientField_iff : IsCMField (CoefficientField f) ↔ ¬f.IsSelfDual := by
  rw [← coefficientFieldConj_eq_one_iff]
  refine ⟨fun _ h ↦ ?_, IsCMField.of_forall_isConj_of_ne_one f.isConj_coefficientFieldConj⟩
  exact IsTotallyComplex.complexEmbedding_not_isReal (CoefficientField f).val.toRingHom <|
    isConj_one_iff.mp (h ▸ f.isConj_coefficientFieldConj _)

end HeckeRing.GL2.Newform
