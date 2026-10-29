import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.FourierExpansion
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeSpace
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# The Fourier coefficients `C(𝔪, f)` of Hilbert modular forms

Let `f = (f_c)` be a Hilbert modular form (LMFDB `mf.hilbert`) over a totally real field `F`, with
components indexed by representatives `𝔟_c` of the narrow class group, and let `𝔡` be the different
of `𝒪_F`. The component `f_c` has a Fourier expansion `∑ a_c(ν) e^{2πi Tr(νz)}` over
`ν ∈ 𝔟_c𝔡⁻¹` (`Hilbert/FourierExpansion.lean`). For a nonzero ideal `𝔪` of `𝒪_F`, the LMFDB's
coefficient `a_𝔪` (Shimura's `C(𝔪, f)`) is `a_c(ν)` for a totally positive `ν` with
`(ν) 𝔟_c⁻¹ 𝔡 = 𝔪`: such `ν` exist exactly for the class `c = [𝔡𝔪⁻¹]`, where they exist, and they are
unique up to totally positive units `ε` of `𝒪_F`. In parallel weight `a_c(εν) = a_c(ν)`, by the
transformation law under `diag(1, ε) ∈ Γ₀(𝔑)_{𝔟_c}`, whose automorphy factor is
`N(ε)^{-k/2} = 1`, and the uniqueness of Fourier expansions, so `a_𝔪` is well defined.

A Hecke eigenform is normalised if `a_(1) = 1`. The relation `a_𝔪(f) = λ_𝔪 a_(1)(f)` between the
coefficients and the Hecke eigenvalues `λ_𝔪` of `HilbertModularForm.heckeIdealSpace`, which in the
normalisation of the slash operator used here should hold up to the factor `N(𝔪)^{k/2 - 1}` (in
parallel weight `k`), is not proved: it needs the action of the Hecke operators on Fourier
expansions.

## Main definitions

* `HilbertModularForm.unitF`: a unit of `𝒪_F` as a unit of `F`.
* `HilbertModularForm.mulUnit`: multiplication by a unit of `𝒪_F` on a fractional ideal.
* `HilbertModularForm.differentNZ`: the different `𝔡`, as a nonzero ideal.
* `HilbertModularForm.idealComponent`: the narrow class `[𝔡𝔪⁻¹]`.
* `HilbertModularForm.IsIdealIndex`: `ν` is totally positive and `(ν) 𝔟_c⁻¹ 𝔡 = 𝔪`.
* `HilbertModularForm.idealCoeff` (LMFDB `mf.hilbert.q_expansion`): the coefficient `a_𝔪`.
* `HilbertModularForm.IsNormalised` (LMFDB `mf.hilbert.eigenvalue`): `a_(1) = 1`.

## Main results

* `HilbertModularForm.fourierCoeff_mulUnit`: in parallel weight, `a_c(εν) = a_c(ν)` for every
  totally positive unit `ε`.
* `HilbertModularForm.exists_isIdealIndex`: a totally positive `ν` with `(ν) 𝔟_c⁻¹ 𝔡 = 𝔪` exists.
* `HilbertModularForm.idealCoeff_eq`: in parallel weight, `a_𝔪 = a_c(ν)` for every such `ν`.
-/

open Complex Matrix NumberField InfinitePlace Real HilbertModularGroup

open scoped nonZeroDivisors UpperHalfPlane

namespace HilbertModularForm

variable {F : Type*} [Field F] {u : (𝓞 F)ˣ}

variable (u) in
/-- A unit of `𝒪_F` as a unit of `F`. -/
noncomputable def unitF : Fˣ :=
  Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) u

lemma unitF_mul_mem_iff {M : Submodule (𝓞 F) F} {y : F} : (unitF u : F) * y ∈ M ↔ y ∈ M :=
  M.smul_mem_iff' u

lemma coe_unitF_inv : (unitF u⁻¹ : F) = (unitF u : F)⁻¹ := by
  rw [unitF, map_inv, Units.val_inv_eq_inv_val]
  rfl

lemma unitF_inv_mul_unitF_mul (y : F) : (unitF u⁻¹ : F) * ((unitF u : F) * y) = y := by
  rw [← mul_assoc, ← Units.val_mul, unitF, unitF, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    one_mul]

lemma unitF_mul_unitF_inv_mul (y : F) : (unitF u : F) * ((unitF u⁻¹ : F) * y) = y := by
  rw [← mul_assoc, ← Units.val_mul, unitF, unitF, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    one_mul]

variable (u) in
/-- **Multiplication by a unit** `u` of `𝒪_F`, as a permutation of a fractional ideal `I`. -/
noncomputable def mulUnit (I : FractionalIdeal (𝓞 F)⁰ F) : I ≃ I where
  toFun ν := ⟨unitF u * ν, unitF_mul_mem_iff.mpr ν.2⟩
  invFun ν := ⟨unitF u⁻¹ * ν, unitF_mul_mem_iff.mpr ν.2⟩
  left_inv ν := Subtype.ext <| unitF_inv_mul_unitF_mul (ν : F)
  right_inv ν := Subtype.ext <| unitF_mul_unitF_inv_mul (ν : F)

variable [NumberField F] in
open scoped Classical in
lemma prod_embedding_unitF [IsTotallyReal F] (hu : IsTotallyPositive (unitF u : F)) :
    ∏ w : {w : InfinitePlace F // w.IsReal}, embedding_of_isReal w.2 (unitF u : F) = 1 := by
  have h : ∏ w : InfinitePlace F, w (unitF u : F) ^ mult w =
      ((|Algebra.norm ℚ (unitF u : F)| : ℚ) : ℝ) :=
    prod_eq_abs_norm (unitF u : F)
  have hn : |(RingOfIntegers.norm ℚ (u : 𝓞 F) : ℚ)| = 1 := isUnit_iff_norm.mp u.isUnit
  rw [RingOfIntegers.coe_norm] at hn
  rw [← (Equiv.subtypeUnivEquiv IsTotallyReal.isReal).prod_comp] at h
  refine Eq.trans ?_ (h.trans ((congrArg ((↑) : ℚ → ℝ) hn).trans Rat.cast_one))
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  simp only [Equiv.subtypeUnivEquiv_apply, IsTotallyReal.mult_eq, pow_one]
  rw [← norm_embedding_of_isReal w.2, Real.norm_of_nonneg (hu w.1 w.2).le]

variable {𝔑 : Ideal (𝓞 F)} {𝔠 : FractionalIdeal (𝓞 F)⁰ F}

lemma heckeDiagonal_mem_gammaZero (hu : IsTotallyPositive (unitF u : F)) :
    (heckeDiagonal (unitF u) hu : GL (Fin 2) F) ∈ gammaZero 𝔠 (glPlus 𝔠) 𝔑 := by
  have hval (v : Fin 2 → F) :
      (heckeDiagonal (unitF u) hu : GL (Fin 2) F).val *ᵥ v = ![v 0, unitF u * v 1] := by
    ext i
    fin_cases i <;> simp [heckeDiagonal, mulVec_diagonal]
  refine ⟨⟨fun v ↦ ?_, Subgroup.mem_comap.mpr (mem_totallyPositiveUnits.mpr ?_)⟩, fun v ↦ ?_⟩
  · rw [hval, mem_lattice, mem_lattice]
    exact and_congr_right fun _ ↦ unitF_mul_mem_iff.symm
  · rwa [det_heckeDiagonal]
  · rw [hval, mem_gammaZeroLattice, mem_gammaZeroLattice]
    exact and_congr_right fun _ ↦ unitF_mul_mem_iff.symm

lemma coe_smul_heckeDiagonal (hu : IsTotallyPositive (unitF u : F))
    (z : {w : InfinitePlace F // w.IsReal} → ℍ) (w : {w : InfinitePlace F // w.IsReal}) :
    (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z w : ℂ) =
      z w / embedding_of_isReal w.2 (unitF u : F) := by
  rw [coe_smul_apply _ _ (isTotallyPositive_det _), denom_mapGL_heckeDiagonal]
  simp only [UpperHalfPlane.num, mapGL]
  simp [heckeDiagonal]

variable [NumberField F]

open scoped Classical in
lemma automorphyFactor_heckeDiagonal [IsTotallyReal F] (hu : IsTotallyPositive (unitF u : F))
    {k : {w : InfinitePlace F // w.IsReal} → ℤ} {m : ℤ} (hk : ∀ w, k w = m)
    (z : {w : InfinitePlace F // w.IsReal} → ℍ) :
    automorphyFactor k (heckeDiagonal (unitF u) hu) z = 1 := by
  simp only [automorphyFactor, denom_mapGL_heckeDiagonal, det_heckeDiagonal, hk]
  simp_rw [← ofReal_zpow, ← ofReal_mul]
  rw [← ofReal_prod, Finset.prod_mul_distrib, Finset.prod_zpow,
    Real.finsetProd_rpow _ _ fun w _ ↦ (hu w.1 w.2).le, prod_embedding_unitF hu]
  simp

lemma fourierExp_smul_heckeDiagonal (hu : IsTotallyPositive (unitF u : F)) (ν : F)
    (z : {w : InfinitePlace F // w.IsReal} → ℍ) :
    fourierExp ν (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z) =
      fourierExp ((unitF u⁻¹ : F) * ν) z := by
  simp only [fourierExp, coe_smul_heckeDiagonal, coe_unitF_inv, map_mul, map_inv₀, ofReal_mul,
    ofReal_inv]
  exact congrArg (fun s ↦ cexp (2 * π * I * s)) (Finset.sum_congr rfl fun _ _ ↦ by ring1)

variable {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ} {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c}
  (f : HilbertModularForm 𝔑 k 𝔟 h𝔟)

/-- **The Fourier coefficients of a Hilbert modular form of parallel weight are invariant under the
totally positive units**: `a_c(εν) = a_c(ν)`. -/
lemma fourierCoeff_mulUnit [IsTotallyReal F] (hu : IsTotallyPositive (unitF u : F)) {m : ℤ}
    (hk : ∀ w, k w = m) (c : NarrowClassGroup F) (ν : fourierDual (𝔟 c)) :
    fourierCoeff (𝔟 c) (f.toFun c) (mulUnit u _ ν) = fourierCoeff (𝔟 c) (f.toFun c) ν := by
  by_cases h : ∃ a, HasHilbertFourierExpansion (𝔟 c) (f.toFun c) a
  · rcases h with ⟨a, ha⟩
    have hb : HasHilbertFourierExpansion (𝔟 c) (f.toFun c) (a ∘ mulUnit u _) := fun z ↦ by
      have hz : HasSum (fun ν ↦ a ν * fourierExp (ν : F)
          (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z))
          (f.toFun c (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z)) :=
        ha (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z)
      rw [f.smul_eq c _ (heckeDiagonal_mem_gammaZero hu) z, automorphyFactor_heckeDiagonal hu hk,
        one_mul] at hz
      refine (mulUnit u _).symm.hasSum_iff.mp ?_
      convert hz using 1
      funext ν
      simp [fourierExp_smul_heckeDiagonal, mulUnit, unitF_mul_unitF_inv_mul]
    rw [ha.fourierCoeff_eq]
    exact congrFun (hb.unique _ ha) ν
  · simp [fourierCoeff, h]

variable (F) in
/-- The different `𝔡` of `𝒪_F`, as a nonzero ideal. -/
noncomputable def differentNZ : (Ideal (𝓞 F))⁰ :=
  ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero differentIdeal_ne_bot⟩

/-- The narrow class `[𝔡𝔪⁻¹]` of the component carrying the coefficient `a_𝔪`. -/
noncomputable def idealComponent (𝔪 : (Ideal (𝓞 F))⁰) : NarrowClassGroup F :=
  NarrowClassGroup.mk0 (differentNZ F) * (NarrowClassGroup.mk0 𝔪)⁻¹

variable (𝔟) in
/-- `ν ∈ F` **indexes the ideal** `𝔪` in the component `c = [𝔡𝔪⁻¹]`: `ν` is totally positive and
`(ν) 𝔟_c⁻¹ 𝔡 = 𝔪`, that is, `(ν) = 𝔪 (𝔟_c⁻¹ 𝔡)⁻¹` as in the knowl (with `𝔞 = 𝔟_c⁻¹`). -/
def IsIdealIndex (𝔪 : (Ideal (𝓞 F))⁰) (ν : F) : Prop :=
  IsTotallyPositive ν ∧ FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ↑(𝔟 (idealComponent 𝔪))⁻¹ *
    (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = (𝔪 : Ideal (𝓞 F))

variable {𝔪 : (Ideal (𝓞 F))⁰} {ν : F}

lemma mem_fourierDual_of_isIdealIndex (hν : IsIdealIndex 𝔟 𝔪 ν) :
    ν ∈ fourierDual (𝔟 (idealComponent 𝔪)) := by
  have hd : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  have h : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν = (𝔪 : Ideal (𝓞 F)) *
      (↑(𝔟 (idealComponent 𝔪)) * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)⁻¹) := by
    rw [← hν.2, mul_mul_mul_comm, mul_assoc _ _ (𝔟 _ : FractionalIdeal (𝓞 F)⁰ F), Units.inv_mul,
      mul_one, mul_inv_cancel₀ hd, mul_one]
  rw [fourierDual_eq, ← FractionalIdeal.spanSingleton_le_iff_mem, h]
  exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one

variable (𝔟 𝔪) in
/-- **A totally positive `ν` with `(ν) 𝔟_c⁻¹ 𝔡 = 𝔪` exists** in the component `c = [𝔡𝔪⁻¹]`. -/
lemma exists_isIdealIndex (h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c) : ∃ ν, IsIdealIndex 𝔟 𝔪 ν := by
  have h : NarrowClassGroup.mk (FractionalIdeal.mk0 F 𝔪 * 𝔟 (idealComponent 𝔪) *
      (FractionalIdeal.mk0 F (differentNZ F))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, h𝔟, NarrowClassGroup.mk_mk0, NarrowClassGroup.mk_mk0,
      idealComponent]
    simp
  rcases mem_narrowPrincipalSubgroup.mp (NarrowClassGroup.mk_eq_one_iff.mp h) with ⟨x, hx, hxJ⟩
  have h' : toPrincipalIdeal (𝓞 F) F x * (𝔟 (idealComponent 𝔪))⁻¹ *
      FractionalIdeal.mk0 F (differentNZ F) = FractionalIdeal.mk0 F 𝔪 := by
    rw [hxJ, mul_right_comm _ (𝔟 (idealComponent 𝔪))⁻¹, inv_mul_cancel_right,
      mul_inv_cancel_right]
  have h'' : FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) * ↑(𝔟 (idealComponent 𝔪))⁻¹ *
      (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) = (𝔪 : Ideal (𝓞 F)) := by
    rw [← coe_toPrincipalIdeal, ← Units.val_mul]
    exact congrArg Units.val h'
  exact ⟨x, hx, h''⟩

/-- The **Fourier coefficient `a_𝔪`** (LMFDB `mf.hilbert.q_expansion`; Shimura's `C(𝔪, f)`) of a
Hilbert modular form `f` at a nonzero ideal `𝔪` of `𝒪_F`: the coefficient `a_c(ν)` of the
component `c = [𝔡𝔪⁻¹]` at a totally positive `ν` with `(ν) 𝔟_c⁻¹ 𝔡 = 𝔪`. In the knowl's notation,
`𝔞 = 𝔟_c⁻¹` and `u = ν`. In parallel weight and for `F` totally real, it does not depend on the
choice of `ν` (`HilbertModularForm.idealCoeff_eq`); in non-parallel weight `a_c(εν)` differs from
`a_c(ν)` by `∏_w w(ε)^{k_w/2}`, so the LMFDB's `a_𝔪` needs a choice there. It is the junk value `0`
if `f_c` has no Fourier expansion. -/
noncomputable def idealCoeff (𝔪 : (Ideal (𝓞 F))⁰) : ℂ :=
  fourierCoeff (𝔟 (idealComponent 𝔪)) (f.toFun (idealComponent 𝔪))
    ⟨(exists_isIdealIndex 𝔟 𝔪 h𝔟).choose,
      mem_fourierDual_of_isIdealIndex (exists_isIdealIndex 𝔟 𝔪 h𝔟).choose_spec⟩

/-- **`a_𝔪` is well defined**: for `F` totally real and `f` of parallel weight, `a_𝔪 = a_c(ν)` for
every totally positive `ν` with `(ν) 𝔟_c⁻¹ 𝔡 = 𝔪`, `c = [𝔡𝔪⁻¹]`. -/
lemma idealCoeff_eq [IsTotallyReal F] {m : ℤ} (hk : ∀ w, k w = m) (hν : IsIdealIndex 𝔟 𝔪 ν) :
    f.idealCoeff 𝔪 = fourierCoeff (𝔟 (idealComponent 𝔪)) (f.toFun (idealComponent 𝔪))
      ⟨ν, mem_fourierDual_of_isIdealIndex hν⟩ := by
  have h0 : IsIdealIndex 𝔟 𝔪 (exists_isIdealIndex 𝔟 𝔪 h𝔟).choose :=
    (exists_isIdealIndex 𝔟 𝔪 h𝔟).choose_spec
  have hd : (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  rcases FractionalIdeal.spanSingleton_eq_spanSingleton.mp <|
    mul_right_cancel₀ (Units.ne_zero _) (mul_right_cancel₀ hd (h0.2.trans hν.2.symm)) with ⟨z, hz⟩
  have hz' : (unitF z : F) * (exists_isIdealIndex 𝔟 𝔪 h𝔟).choose = ν := hz
  have hpos : IsTotallyPositive (unitF z : F) := fun w hw ↦ by
    have h1 : embedding_of_isReal hw (unitF z : F) *
        embedding_of_isReal hw (exists_isIdealIndex 𝔟 𝔪 h𝔟).choose = embedding_of_isReal hw ν := by
      rw [← map_mul, hz']
    exact pos_of_mul_pos_left (by rw [h1]; exact hν.1 w hw) (h0.1 w hw).le
  have he : (⟨ν, mem_fourierDual_of_isIdealIndex hν⟩ : fourierDual (𝔟 (idealComponent 𝔪))) =
      mulUnit z _ ⟨_, mem_fourierDual_of_isIdealIndex h0⟩ :=
    Subtype.ext hz'.symm
  rw [he, fourierCoeff_mulUnit f hpos hk]
  rfl

/-- A Hilbert modular form `f` is **normalised** (LMFDB `mf.hilbert.eigenvalue`) if its Fourier
coefficient at the unit ideal is `a_(1) = 1`. -/
def IsNormalised : Prop :=
  f.idealCoeff 1 = 1

end HilbertModularForm
