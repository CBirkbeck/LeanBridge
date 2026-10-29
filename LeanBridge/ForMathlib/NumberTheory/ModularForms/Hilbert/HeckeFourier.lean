import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.FourierCoefficient
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeIdeal

/-!
# Hecke eigenvalues and Fourier coefficients of Hilbert modular forms

Let `F` be a totally real field, `𝔑` a nonzero ideal of `𝒪_F`, `𝔟` an invertible fractional ideal
and `𝔭 = (π)` an ideal with `π` totally positive. The Hecke operator `T_𝔭` of
`HilbertModularForm.heckeIdealOperator` is `ψ ↦ ∑ ψ ∣ₖ α` over representatives `α` of the right
cosets `Γ₀(𝔑)_𝔟 α` of `Δ = HilbertModularGroup.heckeSet 𝔑 𝔭 𝔟 𝔟`. For a prime `𝔭 ∤ 𝔑`, these
cosets are represented by `(π, 0; 0, 1)` and the `(1, b; 0, π)` with `b ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each
exactly once. This coset decomposition (`HilbertModularForm.IsHeckeCosetDecomposition`) is a
hypothesis of the results below; it is proved for such primes in
`Hilbert/HeckeCosetDecomposition.lean` (`HilbertModularForm.isHeckeCosetDecomposition`).

On Fourier expansions `ψ(z) = ∑ a(ν) e^{2πi Tr(νz)}` over `ν ∈ (𝔟⁻¹)^∨`, in parallel weight `m`,
`ψ ∣ (1, b; 0, π)` has coefficients `N(𝔭)^{-m/2} a(ν) e^{2πi Tr(π⁻¹νb)}` at `π⁻¹ν`, and the sum over
`b` is a character sum over `𝔟⁻¹ / π 𝔟⁻¹`, a group of order `N(𝔭)`, which is `N(𝔭)` or `0`
according as `π⁻¹ν ∈ (𝔟⁻¹)^∨` or not; `ψ ∣ (π, 0; 0, 1)` has coefficients `N(𝔭)^{m/2} a(ν)` at
`πν`. Hence `T_𝔭 ψ` has coefficients `N(𝔭)^{1 - m/2} (a(πμ) + N(𝔭)^{m - 1} a(π⁻¹μ))`. The LMFDB's
(and Shimura's) `T_𝔭` is therefore `N(𝔭)^{m/2 - 1} T_𝔭`, for which
`C(𝔪, T_𝔭 f) = C(𝔪𝔭, f) + N(𝔭)^{m - 1} C(𝔪𝔭⁻¹, f)`, and the eigenvalue of a normalised eigenform
(`a_(1) = 1`) for it is `a_𝔭`.

Only narrow-principal `𝔭` are treated: then `T_𝔭` maps each component to itself. For other `𝔭` the
operator permutes the components, and the term `C(𝔪𝔭⁻¹, f)` lives on the component of `c [𝔭]`, which
is related to the source component `c [𝔭]⁻¹` only through the central character, which the tuples
of `HilbertModularForm` do not constrain.

## Main definitions

* `HilbertModularGroup.heckeUpper`, `HilbertModularGroup.heckeLower`: the matrices `(1, b; 0, π)`
  and `(π, 0; 0, 1)`.
* `HilbertModularForm.HeckeTranslations`: the quotient `𝔟⁻¹ / π 𝔟⁻¹`.
* `HilbertModularForm.heckeChar`: the character `b ↦ e^{2πi Tr(π⁻¹νb)}` of `𝔟⁻¹ / π 𝔟⁻¹`.
* `HilbertModularForm.realNorm`: `∏_w w(x)` over the real places.
* `HilbertModularForm.heckeCosetRep`: the coset representatives of `T_𝔭`.
* `HilbertModularForm.IsHeckeCosetDecomposition`: the coset decomposition of `T_𝔭`.
* `HilbertModularForm.heckeIdealSpaceNormalised`: the LMFDB's `T_𝔞 = N(𝔞)^{m/2 - 1} T_𝔞`.
* `HilbertModularForm.heckeIdealEigenvalueNormalised` (LMFDB `mf.hilbert.eigenvalue`): the Hecke
  eigenvalue `a_𝔞` in the LMFDB's normalisation.

## Main results

* `HilbertModularForm.natCard_heckeTranslations`: `𝔟⁻¹ / π 𝔟⁻¹` has `N(𝔭)` elements.
* `HilbertModularForm.hasHilbertFourierExpansion_heckeIdealOperator`: the Fourier coefficients of
  `T_𝔭 ψ` are `N(𝔭)^{1 - m/2} (a(πμ) + N(𝔭)^{m - 1} a(π⁻¹μ))`.
* `HilbertModularForm.heckeIdealEigenvalueNormalised_eq_idealCoeff`: the normalised eigenvalue of
  `T_𝔭` on a normalised eigenform is its Fourier coefficient `a_𝔭`.
-/

open Complex Matrix NumberField InfinitePlace HilbertModularGroup Set

open scoped nonZeroDivisors UpperHalfPlane

namespace HilbertModularGroup

variable {F : Type*} [Field F] (π : Fˣ) (b : F)

/-- The matrix `(1, b; 0, π)` of `GL₂(F)`. -/
noncomputable def heckeUpper : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, (π : F)] (by simp)

/-- The matrix `(π, 0; 0, 1)` of `GL₂(F)`. -/
noncomputable def heckeLower : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![(π : F), 0; 0, 1] (by simp)

lemma det_heckeUpper : (heckeUpper π b).det.val = π := by
  simp [heckeUpper]

lemma det_heckeLower : (heckeLower π).det.val = π := by
  simp [heckeLower]

end HilbertModularGroup

namespace HilbertModularForm

variable {F : Type*} [Field F] {π : Fˣ} (b : F) (z : {w : InfinitePlace F // w.IsReal} → ℍ)

lemma coe_smul_heckeUpper (hπ : IsTotallyPositive (π : F))
    (w : {w : InfinitePlace F // w.IsReal}) :
    (smul (heckeUpper π b) z w : ℂ) =
      (z w + embedding_of_isReal w.2 b) / embedding_of_isReal w.2 (π : F) := by
  rw [coe_smul_apply _ _ (by rwa [det_heckeUpper])]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, mapGL, heckeUpper]

lemma coe_smul_heckeLower (hπ : IsTotallyPositive (π : F))
    (w : {w : InfinitePlace F // w.IsReal}) :
    (smul (heckeLower π) z w : ℂ) = embedding_of_isReal w.2 (π : F) * z w := by
  rw [coe_smul_apply _ _ (by rwa [det_heckeLower])]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, mapGL, heckeLower]

lemma coeIdeal_toAddSubgroup (𝔭 : Ideal (𝓞 F)) :
    ((𝔭 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).toAddSubgroup =
      𝔭.toAddSubgroup.map (algebraMap (𝓞 F) F).toAddMonoidHom := by
  ext y
  simp

variable [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ} {m : ℤ}

lemma map_mulLeft_toAddSubgroup (J : FractionalIdeal (𝓞 F)⁰ F) (x : F) :
    (J : Submodule (𝓞 F) F).toAddSubgroup.map (AddMonoidHom.mulLeft x) =
      ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x * J : FractionalIdeal (𝓞 F)⁰ F) :
        Submodule (𝓞 F) F).toAddSubgroup := by
  ext y
  rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_singleton_mul]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm

open scoped Classical in
/-- The real number `∏_w w(x)`, the product over the real places of `F`; for `F` totally real and
`x` totally positive, it is the norm of `x`. -/
noncomputable def realNorm (x : F) : ℝ :=
  ∏ w : {w : InfinitePlace F // w.IsReal}, embedding_of_isReal w.2 x

lemma realNorm_nonneg (hπ : IsTotallyPositive (π : F)) : 0 ≤ realNorm (π : F) :=
  Finset.prod_nonneg fun w _ ↦ (hπ w.1 w.2).le

lemma automorphyFactor_heckeUpper (hπ : IsTotallyPositive (π : F)) (hk : ∀ w, k w = m) :
    automorphyFactor k (heckeUpper π b) z = (realNorm (π : F) ^ ((m : ℝ) / 2) : ℝ) := by
  have hd (w : {w : InfinitePlace F // w.IsReal}) :
      UpperHalfPlane.denom (mapGL w (heckeUpper π b)) (z w) = embedding_of_isReal w.2 (π : F) := by
    simp [UpperHalfPlane.denom, mapGL, heckeUpper]
  simp only [automorphyFactor, hk, det_heckeUpper, hd, realNorm]
  rw [← Real.finsetProd_rpow _ _ fun w _ ↦ (hπ w.1 w.2).le, ofReal_prod]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [← ofReal_zpow, ← ofReal_mul, ← Real.rpow_intCast, ← Real.rpow_add (hπ w.1 w.2)]
  congr 2
  ring1

lemma automorphyFactor_heckeLower (hπ : IsTotallyPositive (π : F)) (hk : ∀ w, k w = m) :
    automorphyFactor k (heckeLower π) z = (realNorm (π : F) ^ (-(m : ℝ) / 2) : ℝ) := by
  have hd (w : {w : InfinitePlace F // w.IsReal}) :
      UpperHalfPlane.denom (mapGL w (heckeLower π)) (z w) = 1 := by
    simp [UpperHalfPlane.denom, mapGL, heckeLower]
  simp only [automorphyFactor, hk, det_heckeLower, hd, realNorm]
  rw [← Real.finsetProd_rpow _ _ fun w _ ↦ (hπ w.1 w.2).le, ofReal_prod]
  simp

open scoped Classical in
lemma fourierExp_smul_heckeUpper (hπ : IsTotallyPositive (π : F)) (ν : F) :
    fourierExp ν (smul (heckeUpper π b) z) = fourierExp ((π : F)⁻¹ * ν) z *
      cexp (2 * Real.pi * I * ∑ w : {w : InfinitePlace F // w.IsReal},
        (embedding_of_isReal w.2 ((π : F)⁻¹ * ν * b) : ℂ)) := by
  simp only [fourierExp, coe_smul_heckeUpper b z hπ, ← Complex.exp_add]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  simp only [map_mul, map_inv₀, ofReal_mul, ofReal_inv]
  have h : (embedding_of_isReal w.2 (π : F) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (hπ w.1 w.2).ne'
  field_simp

lemma fourierExp_smul_heckeLower (hπ : IsTotallyPositive (π : F)) (ν : F) :
    fourierExp ν (smul (heckeLower π) z) = fourierExp ((π : F) * ν) z := by
  simp only [fourierExp, coe_smul_heckeLower z hπ, map_mul, ofReal_mul]
  congr 3
  exact funext fun _ ↦ by ring1

variable (𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (π)

/-- The translation lattice `𝔟⁻¹` of `Γ₀(𝔑)_𝔟`, as a submodule of `F`. -/
abbrev translationLattice : Submodule (𝓞 F) F :=
  ((↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)

/-- The subgroup `π 𝔟⁻¹ ∩ 𝔟⁻¹` of the translation lattice `𝔟⁻¹`: the `b ∈ 𝔟⁻¹` with
`π⁻¹ b ∈ 𝔟⁻¹`. -/
def heckeTranslationSubgroup : AddSubgroup (translationLattice 𝔟) where
  carrier := {b | (π : F)⁻¹ * b ∈ translationLattice 𝔟}
  add_mem' ha hb := by
    simpa [mul_add] using add_mem ha hb
  zero_mem' := by
    rw [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, mul_zero]
    exact (translationLattice 𝔟).zero_mem
  neg_mem' ha := by
    rw [Set.mem_ofPred_eq, NegMemClass.coe_neg, mul_neg]
    exact (translationLattice 𝔟).neg_mem ha

/-- The quotient `𝔟⁻¹ / π 𝔟⁻¹` indexing the upper triangular representatives `(1, b; 0, π)` of the
Hecke operator `T_(π)`. -/
abbrev HeckeTranslations : Type _ :=
  translationLattice 𝔟 ⧸ heckeTranslationSubgroup π 𝔟

variable {𝔟} {ν y : F}

lemma mem_heckeTranslationSubgroup {x : translationLattice 𝔟} :
    x ∈ heckeTranslationSubgroup π 𝔟 ↔ (π : F)⁻¹ * x ∈ translationLattice 𝔟 :=
  Iff.rfl

lemma exists_trace_mul_eq (hν : ν ∈ fourierDual 𝔟) (hy : y ∈ translationLattice 𝔟) :
    ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ F (ν * y) := by
  rcases (FractionalIdeal.mem_dual (Units.ne_zero _)).mp hν y hy with ⟨n, hn⟩
  exact ⟨n, hn⟩

lemma cexp_trace_mul_eq_one (hν : ν ∈ fourierDual 𝔟) (hy : y ∈ translationLattice 𝔟) :
    cexp (2 * Real.pi * I * (Algebra.trace ℚ F (ν * y) : ℂ)) = 1 := by
  rcases exists_trace_mul_eq hν hy with ⟨n, hn⟩
  rw [← hn, Rat.cast_intCast, mul_comm]
  exact exp_int_mul_two_pi_mul_I n

lemma mem_fourierDual_of_forall (h : ∀ y ∈ translationLattice 𝔟,
    cexp (2 * Real.pi * I * (Algebra.trace ℚ F (ν * y) : ℂ)) = 1) : ν ∈ fourierDual 𝔟 := by
  refine (FractionalIdeal.mem_dual (Units.ne_zero _)).mpr fun y hy ↦ ?_
  rcases Complex.exp_eq_one_iff.mp (h y hy) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp
  have h' : ((Algebra.trace ℚ F (ν * y) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    rw [Rat.cast_intCast]
    exact mul_left_cancel₀ h2 (hn.trans (mul_comm _ _))
  exact (Rat.cast_injective h').symm

variable (ν) in
/-- The additive character `b ↦ e^{2πi Tr(π⁻¹ ν b)}` of `𝔟⁻¹ / π 𝔟⁻¹`, for `ν ∈ (𝔟⁻¹)^∨`. -/
noncomputable def heckeChar (hν : ν ∈ fourierDual 𝔟) : AddChar (HeckeTranslations π 𝔟) ℂ where
  toFun := Quotient.lift (fun b : translationLattice 𝔟 ↦
    cexp (2 * Real.pi * I * (Algebra.trace ℚ F ((π : F)⁻¹ * ν * b) : ℂ))) fun a b h ↦ by
    have h' : (π : F)⁻¹ * (-(a : F) + b) ∈ translationLattice 𝔟 :=
      (mem_heckeTranslationSubgroup π).mp (QuotientAddGroup.leftRel_apply.mp h)
    have he :
        cexp (2 * Real.pi * I * (Algebra.trace ℚ F (ν * ((π : F)⁻¹ * (-(a : F) + b))) : ℂ)) = 1 :=
      cexp_trace_mul_eq_one hν h'
    have ht : Algebra.trace ℚ F ((π : F)⁻¹ * ν * b) = Algebra.trace ℚ F ((π : F)⁻¹ * ν * a) +
        Algebra.trace ℚ F (ν * ((π : F)⁻¹ * (-(a : F) + b))) := by
      rw [← map_add]
      congr 1
      ring1
    rw [ht, Rat.cast_add, mul_add, Complex.exp_add, he, mul_one]
  map_zero_eq_one' := by
    have h : cexp (2 * Real.pi * I *
        (Algebra.trace ℚ F ((π : F)⁻¹ * ν * ((0 : translationLattice 𝔟) : F)) : ℂ)) = 1 := by
      simp
    exact h
  map_add_eq_mul' a b := by
    refine QuotientAddGroup.induction_on a fun a ↦ QuotientAddGroup.induction_on b fun b ↦ ?_
    have h : cexp (2 * Real.pi * I *
        (Algebra.trace ℚ F ((π : F)⁻¹ * ν * ((a + b : translationLattice 𝔟) : F)) : ℂ)) =
        cexp (2 * Real.pi * I * (Algebra.trace ℚ F ((π : F)⁻¹ * ν * a) : ℂ)) *
          cexp (2 * Real.pi * I * (Algebra.trace ℚ F ((π : F)⁻¹ * ν * b) : ℂ)) := by
      rw [← Complex.exp_add, ← mul_add, ← Rat.cast_add, ← map_add, ← mul_add]
      rfl
    exact h

lemma heckeChar_mk (hν : ν ∈ fourierDual 𝔟) (b : translationLattice 𝔟) :
    heckeChar π ν hν b = cexp (2 * Real.pi * I * (Algebra.trace ℚ F ((π : F)⁻¹ * ν * b) : ℂ)) :=
  rfl

lemma heckeChar_eq_zero_iff (hν : ν ∈ fourierDual 𝔟) :
    heckeChar π ν hν = 0 ↔ (π : F)⁻¹ * ν ∈ fourierDual 𝔟 := by
  refine ⟨fun h ↦ mem_fourierDual_of_forall fun y hy ↦ ?_, fun h ↦ AddChar.eq_zero_iff.mpr ?_⟩
  · rw [← heckeChar_mk π hν ⟨y, hy⟩, h, AddChar.zero_apply]
  · refine fun q ↦ QuotientAddGroup.induction_on q fun b ↦ ?_
    exact (heckeChar_mk π hν b).trans (cexp_trace_mul_eq_one h b.2)

open scoped Classical in
lemma sum_heckeChar [Fintype (HeckeTranslations π 𝔟)] (hν : ν ∈ fourierDual 𝔟) :
    ∑ q, heckeChar π ν hν q =
      if (π : F)⁻¹ * ν ∈ fourierDual 𝔟 then (Fintype.card (HeckeTranslations π 𝔟) : ℂ) else 0 := by
  rw [AddChar.sum_eq_ite]
  exact if_congr (heckeChar_eq_zero_iff π hν) rfl rfl

lemma injective_mul_fourierDual (hπ' : ∀ μ ∈ fourierDual 𝔟, (π : F) * μ ∈ fourierDual 𝔟) :
    Function.Injective fun μ : fourierDual 𝔟 ↦ (⟨π * μ, hπ' μ μ.2⟩ : fourierDual 𝔟) :=
  fun _ _ h ↦ Subtype.ext (mul_left_cancel₀ π.ne_zero (congrArg Subtype.val h))

variable {φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ} {a : fourierDual 𝔟 → ℂ}

open scoped Classical in
lemma hasHilbertFourierExpansion_sum_slash_heckeUpper [IsTotallyReal F]
    [Fintype (HeckeTranslations π 𝔟)] (hπ : IsTotallyPositive (π : F)) (hk : ∀ w, k w = m)
    (hπ' : ∀ μ ∈ fourierDual 𝔟, (π : F) * μ ∈ fourierDual 𝔟)
    (hφ : HasHilbertFourierExpansion 𝔟 φ a) :
    HasHilbertFourierExpansion 𝔟 (∑ q : HeckeTranslations π 𝔟, slash k (heckeUpper π q.out) φ)
      fun μ ↦ (realNorm (π : F) ^ (-(m : ℝ) / 2) : ℝ) *
        (Fintype.card (HeckeTranslations π 𝔟) : ℂ) * a ⟨π * μ, hπ' μ μ.2⟩ := by
  intro z
  have h1 (q : HeckeTranslations π 𝔟) : HasSum (fun ν : fourierDual 𝔟 ↦
      (realNorm (π : F) ^ (-(m : ℝ) / 2) : ℝ) * (a ν * fourierExp ((π : F)⁻¹ * ν) z *
        heckeChar π ν ν.2 q)) (slash k (heckeUpper π q.out) φ z) := by
    rw [slash, automorphyFactor_heckeUpper _ z hπ hk, ← ofReal_inv,
      ← Real.rpow_neg (realNorm_nonneg hπ), ← neg_div]
    refine ((hφ _).mul_left _).congr_fun fun ν ↦ ?_
    rw [fourierExp_smul_heckeUpper _ z hπ, ← coe_trace_eq_sum, ← Quotient.out_eq q,
      heckeChar_mk, Quotient.out_eq]
    ring1
  have h2 : HasSum (fun ν : fourierDual 𝔟 ↦ (realNorm (π : F) ^ (-(m : ℝ) / 2) : ℝ) *
      (a ν * fourierExp ((π : F)⁻¹ * ν) z * if (π : F)⁻¹ * ν ∈ fourierDual 𝔟 then
        (Fintype.card (HeckeTranslations π 𝔟) : ℂ) else 0))
      ((∑ q : HeckeTranslations π 𝔟, slash k (heckeUpper π q.out) φ) z) := by
    rw [Finset.sum_apply]
    refine (hasSum_sum fun q _ ↦ h1 q).congr_fun fun ν ↦ ?_
    rw [← sum_heckeChar π ν.2, Finset.mul_sum, Finset.mul_sum]
  refine (((injective_mul_fourierDual π hπ').hasSum_iff fun ν hν ↦ ?_).mpr h2).congr_fun
    fun μ ↦ ?_
  · rw [ite_eq_right fun h ↦ hν ⟨⟨_, h⟩, Subtype.ext (mul_inv_cancel_left₀ π.ne_zero _)⟩,
      mul_zero, mul_zero]
  · simp only [Function.comp_apply, inv_mul_cancel_left₀ π.ne_zero, ite_eq_left μ.2]
    ring1

open scoped Classical in
lemma hasHilbertFourierExpansion_slash_heckeLower (hπ : IsTotallyPositive (π : F))
    (hk : ∀ w, k w = m) (hπ' : ∀ μ ∈ fourierDual 𝔟, (π : F) * μ ∈ fourierDual 𝔟)
    (hφ : HasHilbertFourierExpansion 𝔟 φ a) :
    HasHilbertFourierExpansion 𝔟 (slash k (heckeLower π) φ) fun μ ↦
      (realNorm (π : F) ^ ((m : ℝ) / 2) : ℝ) *
        if h : (π : F)⁻¹ * μ ∈ fourierDual 𝔟 then a ⟨_, h⟩ else 0 := by
  intro z
  refine ((injective_mul_fourierDual π hπ').hasSum_iff fun ν hν ↦ ?_).mp ?_
  · beta_reduce
    rw [dite_eq_right fun h ↦ hν ⟨⟨_, h⟩, Subtype.ext (mul_inv_cancel_left₀ π.ne_zero _)⟩,
      mul_zero, zero_mul]
  · rw [slash, automorphyFactor_heckeLower z hπ hk, ← ofReal_inv,
      ← Real.rpow_neg (realNorm_nonneg hπ), neg_div, neg_neg]
    refine ((hφ _).mul_left _).congr_fun fun ν ↦ ?_
    simp [fourierExp_smul_heckeLower z hπ]
    ring1

variable (𝔭 : Ideal (𝓞 F))

/-- **The quotient `𝔟⁻¹ / π 𝔟⁻¹` has `N(𝔭)` elements**, for `(π) = 𝔭`: writing `𝔟⁻¹ = d⁻¹ I` with
`I` integral, it is `I / 𝔭 I`, of order `N(𝔭 I) / N(I)`. -/
lemma natCard_heckeTranslations
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F)) :
    Nat.card (HeckeTranslations π 𝔟) = Ideal.absNorm 𝔭 := by
  rcases FractionalIdeal.exists_eq_spanSingleton_mul (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) with
    ⟨d, I, hd, hI⟩
  have hα : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd
  have hN : heckeTranslationSubgroup π 𝔟 =
      ((translationLattice 𝔟).toAddSubgroup.map (AddMonoidHom.mulLeft (π : F))).addSubgroupOf
        (translationLattice 𝔟).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, mem_heckeTranslationSubgroup]
    refine ⟨fun h ↦ ⟨_, h, mul_inv_cancel_left₀ π.ne_zero _⟩, ?_⟩
    rintro ⟨y, hy, hxy⟩
    rw [← hxy, AddMonoidHom.coe_mulLeft, inv_mul_cancel_left₀ π.ne_zero]
    exact hy
  have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F d) *
      (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) = I := by
    rw [hI, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  have h2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F d) *
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) * (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)) =
        ↑(𝔭 * I) := by
    rw [mul_left_comm, h1, hπ𝔭, FractionalIdeal.coeIdeal_mul]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot, mul_zero] at hI
    exact Units.ne_zero _ hI
  have hle : (𝔭 * I).toAddSubgroup ≤ I.toAddSubgroup :=
    Submodule.toAddSubgroup_mono Ideal.mul_le_right
  refine (?_ : (heckeTranslationSubgroup π 𝔟).index = _)
  rw [hN, ← AddSubgroup.relIndex, ← AddSubgroup.relIndex_map_map_of_injective
    (f := AddMonoidHom.mulLeft (algebraMap (𝓞 F) F d)) _ _ (mul_right_injective₀ hα),
    map_mulLeft_toAddSubgroup, map_mulLeft_toAddSubgroup, map_mulLeft_toAddSubgroup, h2, h1,
    coeIdeal_toAddSubgroup, coeIdeal_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (IsFractionRing.injective (𝓞 F) F)]
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors
    ⟨I, mem_nonZeroDivisors_of_ne_zero hI0⟩)) ?_
  rw [Ideal.absNorm_eq_index I, AddSubgroup.relIndex_mul_index hle, ← Ideal.absNorm_eq_index,
    ← Ideal.absNorm_eq_index, map_mul]

open scoped Classical in
lemma realNorm_eq_absNorm [IsTotallyReal F] (hπ : IsTotallyPositive (π : F))
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F)) :
    realNorm (π : F) = Ideal.absNorm 𝔭 := by
  have h : ∏ w : InfinitePlace F, w (π : F) ^ mult w = ((|Algebra.norm ℚ (π : F)| : ℚ) : ℝ) :=
    prod_eq_abs_norm (π : F)
  have h' : |Algebra.norm ℚ (π : F)| = Ideal.absNorm 𝔭 := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 F), hπ𝔭, FractionalIdeal.coeIdeal_absNorm]
  rw [← (Equiv.subtypeUnivEquiv IsTotallyReal.isReal).prod_comp, h', Rat.cast_natCast] at h
  refine Eq.trans (Finset.prod_congr rfl fun w _ ↦ ?_) h
  simp only [Equiv.subtypeUnivEquiv_apply, IsTotallyReal.mult_eq, pow_one]
  rw [← norm_embedding_of_isReal w.2, Real.norm_of_nonneg (hπ w.1 w.2).le]

variable (𝔟)

/-- The representatives `(π, 0; 0, 1)` (for `none`) and `(1, b; 0, π)` (for `some b`,
`b ∈ 𝔟⁻¹ / π 𝔟⁻¹`) of the right cosets of the Hecke operator `T_(π)`. -/
noncomputable def heckeCosetRep : Option (HeckeTranslations π 𝔟) → GL (Fin 2) F
  | none => heckeLower π
  | some q => heckeUpper π q.out

lemma det_heckeCosetRep (r : Option (HeckeTranslations π 𝔟)) :
    (heckeCosetRep π 𝔟 r).det.val = π := by
  rcases r with _ | q
  · exact det_heckeLower π
  · exact det_heckeUpper π _

variable (𝔑 : Ideal (𝓞 F))

/-- The **coset decomposition** of the Hecke operator `T_𝔭` on the component of `𝔟`, for
`𝔭 = (π)` with `π` totally positive: the right cosets `Γ₀(𝔑)_𝔟 α` of the matrices `α` of
`HilbertModularGroup.heckeSet 𝔑 𝔭 𝔟 𝔟` are the cosets of `(π, 0; 0, 1)` and of the `(1, b; 0, π)`,
`b ∈ 𝔟⁻¹ / π 𝔟⁻¹`, each exactly once. It holds for a prime `𝔭 ∤ 𝔑`: see
`HilbertModularForm.isHeckeCosetDecomposition` in `Hilbert/HeckeCosetDecomposition.lean`. -/
def IsHeckeCosetDecomposition : Prop :=
  Set.BijOn
    (fun r ↦ (⟦heckeCosetRep π 𝔟 r⟧ : gammaZeroRightCosets 𝔑 (𝔟 : FractionalIdeal (𝓞 F)⁰ F)))
    Set.univ (heckeCosets 𝔑 𝔭 𝔟 𝔟)

variable {π 𝔟 𝔭 𝔑}

lemma mul_mem_fourierDual
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    {μ : F} (hμ : μ ∈ fourierDual 𝔟) : (π : F) * μ ∈ fourierDual 𝔟 := by
  have h : (π : F) ∈ (𝔭 : FractionalIdeal (𝓞 F)⁰ F) :=
    hπ𝔭 ▸ FractionalIdeal.mem_spanSingleton_self _ _
  rcases (FractionalIdeal.mem_coeIdeal _).mp h with ⟨p, -, hp⟩
  rw [← hp, ← Algebra.smul_def]
  exact Submodule.smul_mem (fourierDual 𝔟 : Submodule (𝓞 F) F) p hμ

variable [NeZero 𝔑] [NeZero 𝔭]

lemma coe_heckeIdealOperator_eq_sum [Fintype (HeckeTranslations π 𝔟)]
    (h : IsHeckeCosetDecomposition π 𝔟 𝔭 𝔑) (hπ : IsTotallyPositive (π : F))
    (ψ : slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus 𝔟) 𝔑)) :
    (heckeIdealOperator k 𝔑 𝔭 𝔟 𝔟 ψ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ r, slash k (heckeCosetRep π 𝔟 r) ψ := by
  rw [coe_heckeIdealOperator]
  refine (Finset.sum_nbij (fun r ↦ ⟦heckeCosetRep π 𝔟 r⟧)
    (fun r _ ↦ (Finite.mem_toFinset _).mpr (h.mapsTo (mem_univ r))) ?_ ?_
    fun r _ ↦ (slash_out_mk ψ.2 ?_).symm).symm
  · rw [Finset.coe_univ]
    exact h.injOn
  · rw [Finset.coe_univ, Finite.coe_toFinset]
    exact h.surjOn
  · rw [det_heckeCosetRep]
    exact hπ

open scoped Classical in
/-- **The Hecke operator `T_𝔭` on Fourier expansions** (Shimura), for `𝔭 = (π)`, `π` totally
positive, given the coset decomposition of `T_𝔭`, in parallel weight `m`: if `ψ` has Fourier
coefficients `a(ν)`, then `T_𝔭 ψ` has Fourier coefficients
`N(𝔭)^{1 - m/2} (a(πμ) + N(𝔭)^{m - 1} a(π⁻¹μ))`, where `a(π⁻¹μ) = 0` if `π⁻¹μ ∉ (𝔟⁻¹)^∨`. -/
lemma hasHilbertFourierExpansion_heckeIdealOperator [IsTotallyReal F]
    (h : IsHeckeCosetDecomposition π 𝔟 𝔭 𝔑) (hπ : IsTotallyPositive (π : F))
    (hπ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = (𝔭 : FractionalIdeal (𝓞 F)⁰ F))
    (hk : ∀ w, k w = m)
    (ψ : slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus 𝔟) 𝔑))
    (hψ : HasHilbertFourierExpansion 𝔟 ψ a) :
    HasHilbertFourierExpansion 𝔟 (heckeIdealOperator k 𝔑 𝔭 𝔟 𝔟 ψ) fun μ ↦
      ((Ideal.absNorm 𝔭 : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) * (a ⟨π * μ, mul_mem_fourierDual hπ𝔭 μ.2⟩ +
        (Ideal.absNorm 𝔭 : ℂ) ^ (m - 1) *
          if h : (π : F)⁻¹ * μ ∈ fourierDual 𝔟 then a ⟨_, h⟩ else 0) := by
  have hcard : Nat.card (HeckeTranslations π 𝔟) = Ideal.absNorm 𝔭 :=
    natCard_heckeTranslations π 𝔭 hπ𝔭
  have hN : Nat.card (HeckeTranslations π 𝔟) ≠ 0 := by
    rw [hcard, Ne, Ideal.absNorm_eq_zero_iff]
    exact NeZero.ne 𝔭
  have hN' : (0 : ℝ) < Ideal.absNorm 𝔭 := by
    rw [← hcard]
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have : Finite (HeckeTranslations π 𝔟) :=
    Nat.finite_of_card_ne_zero hN
  let _ : Fintype (HeckeTranslations π 𝔟) :=
    Fintype.ofFinite _
  have hcard' : (Fintype.card (HeckeTranslations π 𝔟) : ℂ) = Ideal.absNorm 𝔭 := by
    rw [Fintype.card_eq_nat_card, hcard]
  have hπ' : ∀ μ ∈ fourierDual 𝔟, (π : F) * μ ∈ fourierDual 𝔟 :=
    fun _ ↦ mul_mem_fourierDual hπ𝔭
  rw [coe_heckeIdealOperator_eq_sum h hπ, Fintype.sum_option]
  convert (hasHilbertFourierExpansion_slash_heckeLower π hπ hk hπ' hψ).add _
    (hasHilbertFourierExpansion_sum_slash_heckeUpper π hπ hk hπ' hψ) using 1
  · rfl
  funext μ
  rw [Pi.add_apply, hcard', realNorm_eq_absNorm π 𝔭 hπ hπ𝔭]
  have h1 : (((Ideal.absNorm 𝔭 : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) : ℂ) =
      (((Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℝ) / 2) : ℝ) : ℂ) * (Ideal.absNorm 𝔭 : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_mul, ← Real.rpow_add_one hN'.ne']
    congr 2
    ring1
  have h2 : (((Ideal.absNorm 𝔭 : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) : ℂ) *
      (Ideal.absNorm 𝔭 : ℂ) ^ (m - 1) = (((Ideal.absNorm 𝔭 : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← ofReal_natCast, ← ofReal_zpow, ← ofReal_mul, ← Real.rpow_intCast,
      ← Real.rpow_add hN']
    congr 2
    push_cast
    ring1
  rw [mul_add, ← mul_assoc, h2, h1]
  ring1

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {m : ℤ} {𝔑 : Ideal (𝓞 F)} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (f : HilbertModularForm 𝔑 k 𝔟 h𝔟)
  (𝔞 : (Ideal (𝓞 F))⁰) {π : Fˣ}

lemma mk0_eq_one (hπ : IsTotallyPositive (π : F)) (hπ𝔞 : FractionalIdeal.spanSingleton (𝓞 F)⁰
    (π : F) = ((𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) : NarrowClassGroup.mk0 𝔞 = 1 := by
  rw [← NarrowClassGroup.mk_mk0, NarrowClassGroup.mk_eq_one_iff, mem_narrowPrincipalSubgroup]
  exact ⟨π, hπ, Units.ext <| by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, hπ𝔞]⟩

lemma idealCoeff_eq_of_eq [IsTotallyReal F] (hk : ∀ w, k w = m) {𝔪 : (Ideal (𝓞 F))⁰}
    {c : NarrowClassGroup F} (hc : idealComponent 𝔪 = c) {ν : F} (hν : ν ∈ fourierDual (𝔟 c))
    (hpos : IsTotallyPositive ν) (hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ↑(𝔟 c)⁻¹ *
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = (𝔪 : Ideal (𝓞 F))) :
    f.idealCoeff 𝔪 = fourierCoeff (𝔟 c) (f.toFun c) ⟨ν, hν⟩ := by
  subst hc
  exact f.idealCoeff_eq hk ⟨hpos, hspan⟩

lemma inv_mul_notMem_fourierDual (h𝔞 : (𝔞 : Ideal (𝓞 F)) ≠ ⊤) (hπ𝔞 :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) = ((𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))
    {𝔠 : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {ν : F} (hspan : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν *
      ↑𝔠⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = 1) :
    (π : F)⁻¹ * ν ∉ fourierDual 𝔠 := by
  intro hmem
  have hd : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have h𝔞0 : ((𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero 𝔞)
  rw [fourierDual_eq, ← FractionalIdeal.spanSingleton_le_iff_mem] at hmem
  have h : FractionalIdeal.spanSingleton (𝓞 F)⁰ ((π : F)⁻¹ * ν) *
      (↑𝔠⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) ≤
        ↑𝔠 * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ *
          (↑𝔠⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)) :=
    mul_le_mul' hmem le_rfl
  rw [mul_mul_mul_comm, Units.mul_inv, inv_mul_cancel₀ hd, one_mul, map_mul, mul_assoc,
    ← mul_assoc (FractionalIdeal.spanSingleton (𝓞 F)⁰ ν), hspan, mul_one, map_inv₀, hπ𝔞] at h
  have h' : (1 : FractionalIdeal (𝓞 F)⁰ F) ≤ (𝔞 : Ideal (𝓞 F)) := by
    have h'' : ((𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (𝔞 : Ideal (𝓞 F)) ≤
        1 * (𝔞 : Ideal (𝓞 F)) :=
      mul_le_mul' h le_rfl
    rwa [inv_mul_cancel₀ h𝔞0, one_mul] at h''
  rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal, top_le_iff] at h'
  exact h𝔞 h'

variable [NeZero 𝔑]

lemma coe_heckeIdealForm_toFun (h : NarrowClassGroup.mk0 𝔞 = 1) (c : NarrowClassGroup F) :
    (f.heckeIdealForm 𝔞).toFun c = heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c)
      ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩ := by
  have key (c' : NarrowClassGroup F) (hc : c' = c) :
      (heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c') ⟨f.toFun c', f.toFun_mem_slashInvariants c'⟩ :
        ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      heckeIdealOperator k 𝔑 𝔞 (𝔟 c) (𝔟 c) ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩ := by
    subst hc
    rfl
  exact key _ (by rw [h, inv_one, mul_one])

variable (m) in
/-- The **normalised Hecke operator** `N(𝔞)^{m/2 - 1} T_𝔞` on the space of Hilbert modular forms of
parallel weight `m`, where `T_𝔞` is `heckeIdealSpace 𝔞`, defined with the unitarily normalised slash
operator. This is the normalisation of the LMFDB and of Shimura, for which
`C(𝔪, T_𝔭 f) = C(𝔪𝔭, f) + N(𝔭)^{m - 1} C(𝔪𝔭⁻¹, f)`
(`HilbertModularForm.hasHilbertFourierExpansion_heckeIdealOperator`). -/
noncomputable def heckeIdealSpaceNormalised : Module.End ℂ (space k 𝔑 𝔟) :=
  (((Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℝ) ^ ((m : ℝ) / 2 - 1) : ℝ) : ℂ) • heckeIdealSpace 𝔞

variable (m) {f} in
/-- The **Hecke eigenvalue** `a_𝔞` (LMFDB `mf.hilbert.eigenvalue`) of a Hecke eigenform `f` of
parallel weight `m` at a nonzero ideal `𝔞` coprime to the level, in the LMFDB's normalisation: the
eigenvalue `N(𝔞)^{m/2 - 1} λ_𝔞` of the normalised Hecke operator `heckeIdealSpaceNormalised m 𝔞`,
where `λ_𝔞` is the eigenvalue of `heckeIdealSpace 𝔞`. For a normalised eigenform (`a_(1) = 1`) and
`𝔞 = 𝔭 = (π)` with `π` totally positive, it is the Fourier coefficient `a_𝔭`
(`HilbertModularForm.heckeIdealEigenvalueNormalised_eq_idealCoeff`). -/
noncomputable def heckeIdealEigenvalueNormalised (hf : f.IsHeckeIdealEigenform)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) : ℂ :=
  (((Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℝ) ^ ((m : ℝ) / 2 - 1) : ℝ) : ℂ) *
    heckeIdealEigenvalue 𝔞 hf h𝔞

variable {f}

lemma heckeIdealSpaceNormalised_apply (hf : f.IsHeckeIdealEigenform)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) :
    heckeIdealSpaceNormalised m 𝔞 ⟨f.toFun, f.toFun_mem_space⟩ =
      heckeIdealEigenvalueNormalised m 𝔞 hf h𝔞 • (⟨f.toFun, f.toFun_mem_space⟩ : space k 𝔑 𝔟) := by
  rw [heckeIdealSpaceNormalised, LinearMap.smul_apply, heckeIdealEigenvalueNormalised, mul_smul]
  exact congrArg _ <| Subtype.ext <| hasHeckeIdealEigenvalue_heckeIdealEigenvalue 𝔞 hf h𝔞

open scoped Classical in
/-- **The Hecke eigenvalues of a normalised eigenform are its Fourier coefficients**: for `F`
totally real, a normalised Hecke eigenform `f` (`a_(1) = 1`) of parallel weight `m` whose components
have Fourier expansions, and `𝔭 = (π) ≠ 𝒪_F` with `π` totally positive and `𝔭 + 𝔑 = 𝒪_F`, the
normalised eigenvalue of `T_𝔭` is `a_𝔭`, given the coset decomposition of `T_𝔭`. -/
lemma heckeIdealEigenvalueNormalised_eq_idealCoeff [IsTotallyReal F] (hk : ∀ w, k w = m)
    (hf : f.IsHeckeIdealEigenform) (hn : f.IsNormalised)
    (hexp : ∀ c, ∃ a, HasHilbertFourierExpansion (𝔟 c) (f.toFun c) a)
    (h𝔞 : (𝔞 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) (h𝔞' : (𝔞 : Ideal (𝓞 F)) ≠ ⊤)
    (hπ : IsTotallyPositive (π : F)) (hπ𝔞 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F) =
      ((𝔞 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F))
    (hcos : ∀ 𝔠 : (FractionalIdeal (𝓞 F)⁰ F)ˣ, IsHeckeCosetDecomposition π 𝔠 𝔞 𝔑) :
    heckeIdealEigenvalueNormalised m 𝔞 hf h𝔞 = f.idealCoeff 𝔞 := by
  rcases hexp (idealComponent 1) with ⟨a, ha⟩
  have h0 : IsIdealIndex 𝔟 1 (exists_isIdealIndex 𝔟 1 h𝔟).choose :=
    (exists_isIdealIndex 𝔟 1 h𝔟).choose_spec
  have hmem : (exists_isIdealIndex 𝔟 1 h𝔟).choose ∈ fourierDual (𝔟 (idealComponent 1)) :=
    mem_fourierDual_of_isIdealIndex h0
  have hT : HasHilbertFourierExpansion (𝔟 (idealComponent 1))
      (heckeIdealEigenvalue 𝔞 hf h𝔞 • f.toFun (idealComponent 1)) fun μ ↦
        ((Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) *
          (a ⟨π * μ, mul_mem_fourierDual hπ𝔞 μ.2⟩ +
            (Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℂ) ^ (m - 1) *
              if h : (π : F)⁻¹ * μ ∈ fourierDual (𝔟 (idealComponent 1)) then a ⟨_, h⟩ else 0) := by
    rw [← Pi.smul_apply, ← (hasHeckeIdealEigenvalue_heckeIdealEigenvalue 𝔞 hf h𝔞 :
      (f.heckeIdealForm 𝔞).toFun = _), coe_heckeIdealForm_toFun f 𝔞 (mk0_eq_one 𝔞 hπ hπ𝔞)]
    exact hasHilbertFourierExpansion_heckeIdealOperator (hcos _) hπ hπ𝔞 hk _ ha
  have h1 : ((Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℝ) ^ (1 - (m : ℝ) / 2) : ℝ) *
      (a ⟨π * (exists_isIdealIndex 𝔟 1 h𝔟).choose, mul_mem_fourierDual hπ𝔞 hmem⟩ +
        (Ideal.absNorm (𝔞 : Ideal (𝓞 F)) : ℂ) ^ (m - 1) *
          if h : (π : F)⁻¹ * (exists_isIdealIndex 𝔟 1 h𝔟).choose ∈
            fourierDual (𝔟 (idealComponent 1)) then a ⟨_, h⟩ else 0) =
      heckeIdealEigenvalue 𝔞 hf h𝔞 * a ⟨_, hmem⟩ :=
    congrFun (hT.unique _ (ha.const_smul _ _)) ⟨_, hmem⟩
  have ha1 : a ⟨_, hmem⟩ = 1 := by
    rw [← (hn : f.idealCoeff 1 = 1), idealCoeff, ha.fourierCoeff_eq]
  have hspan1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (exists_isIdealIndex 𝔟 1 h𝔟).choose *
      ↑(𝔟 (idealComponent 1))⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = 1 :=
    h0.2.trans (by simp)
  have hc : idealComponent 𝔞 = idealComponent 1 := by
    rw [idealComponent, idealComponent, mk0_eq_one 𝔞 hπ hπ𝔞, map_one]
  have hspan :
      FractionalIdeal.spanSingleton (𝓞 F)⁰ ((π : F) * (exists_isIdealIndex 𝔟 1 h𝔟).choose) *
        ↑(𝔟 (idealComponent 1))⁻¹ * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) =
          (𝔞 : Ideal (𝓞 F)) := by
    rw [map_mul, mul_assoc (FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F)),
      mul_assoc (FractionalIdeal.spanSingleton (𝓞 F)⁰ (π : F)), hspan1, mul_one, hπ𝔞]
  have hpos : IsTotallyPositive ((π : F) * (exists_isIdealIndex 𝔟 1 h𝔟).choose) := fun w hw ↦ by
    rw [map_mul]
    exact mul_pos (hπ w hw) (h0.1 w hw)
  have hN : (0 : ℝ) < Ideal.absNorm (𝔞 : Ideal (𝓞 F)) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors 𝔞))
  rw [dite_eq_right (inv_mul_notMem_fourierDual 𝔞 h𝔞' hπ𝔞 hspan1), mul_zero, add_zero, ha1,
    mul_one] at h1
  rw [idealCoeff_eq_of_eq f hk hc (mul_mem_fourierDual hπ𝔞 hmem) hpos hspan,
    heckeIdealEigenvalueNormalised, ← h1, ← mul_assoc, ← ofReal_mul, ← Real.rpow_add hN,
    sub_add_sub_cancel', sub_self, Real.rpow_zero, ofReal_one, one_mul, ha.fourierCoeff_eq]

end HilbertModularForm
