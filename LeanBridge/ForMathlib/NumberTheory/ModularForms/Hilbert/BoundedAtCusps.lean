import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.KoecherPrinciple

/-!
# Hilbert modular forms are bounded at the cusps

Let `F` be a totally real number field of degree `n > 1`, `𝔑` a nonzero ideal of `𝒪_F` and `𝔟` an
invertible fractional ideal. The LMFDB defines Hilbert modular forms (LMFDB `mf.hilbert`) as tuples
of holomorphic functions on `ℍⁿ` with the transformation law of weight `k` for the groups
`Γ₀(𝔑)_𝔟 = {(a, b; c, d) : a, d ∈ 𝒪_F, b ∈ 𝔟⁻¹, c ∈ 𝔑𝔟, ad - bc ∈ 𝒪_F^× totally positive}`
(`HilbertModularGroup.mem_gammaZero_glPlus_iff`), while `HilbertModularForm` also asks for
boundedness at every cusp (`HilbertModularForm.IsBoundedAtCusps`), so as to be right in degree `1`.
This condition is automatic in degree `n > 1` (Koecher), so the two definitions agree
(`HilbertModularForm.mem_space_iff`, `HilbertModularForm.ofSmulEq`).

Let `α ∈ SL₂(F)` and `Γ = Γ₀(𝔑)_𝔟`. Every element of `GL₂(F)` commensurates `Γ`
(`HilbertModularGroup.mem_commensurator_gammaZero`), so `Γ ∩ α⁻¹Γα` has finite index in `Γ`, and
`γ^M ∈ α⁻¹Γα` for every `γ ∈ Γ`, `M` the factorial of that index. The slash `f ∣ₖ α` is invariant
under `α⁻¹Γα`: under the translations by `M𝔟⁻¹`, the inverse of `𝔞 = 𝔟M⁻¹`, and under the matrices
`diag(1, ε^M)`, `ε` a totally positive unit. It is therefore the sum of a Fourier series over
`(𝔞⁻¹)^∨` (`HilbertModularForm.hasHilbertFourierExpansion_fourierCoeff`), supported on `0` and the
totally positive `ν`
(`HilbertModularForm.HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive`), and it is bounded
when all the imaginary parts tend to infinity
(`HilbertModularForm.HasHilbertFourierExpansion.boundedAtFilter`).

## Main definitions

* `HilbertModularForm.cuspExponent`: the exponent `M` of the cusp `α ∞`.
* `HilbertModularForm.cuspIdeal`: the invertible fractional ideal `𝔞 = 𝔟M⁻¹`, the translations by
  `𝔞⁻¹ = M𝔟⁻¹` lying in `α⁻¹Γ₀(𝔑)_𝔟α`.
* `HilbertModularForm.ofSmulEq` (LMFDB `mf.hilbert`): the Hilbert modular form defined by a tuple of
  holomorphic functions with the transformation law, as the LMFDB defines it.

## Main results

* `HilbertModularForm.hasHilbertFourierExpansion_slash` (LMFDB `mf.hilbert.q_expansion`): Fourier
  expansions at every cusp.
* `HilbertModularForm.HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive_slash` (LMFDB
  `mf.hilbert.q_expansion`): Koecher's principle at every cusp.
* `HilbertModularForm.isBoundedAtCusps_of_mem_slashInvariants`: in degree `> 1`, boundedness at the
  cusps follows from holomorphy and the transformation law.
* `HilbertModularForm.vanishesAtCusps_iff`: vanishing at the cusps is the vanishing of the constant
  terms of the Fourier expansions at all the cusps.
* `HilbertModularForm.mem_space_iff` (LMFDB `mf.hilbert`): the space of Hilbert modular forms is the
  space of the knowl, with no condition at the cusps.
* `HilbertModularForm.isCuspForm_iff` (LMFDB `mf.hilbert`): Hilbert cusp forms are the forms whose
  constant terms vanish at every cusp.
* `HilbertModularForm.fourierCoeff_toFun_zero` (LMFDB `mf.hilbert.q_expansion`): the expansions of
  the components of a cusp form have no constant term.
-/

open Filter Matrix Module NumberField InfinitePlace HilbertModularGroup Subgroup

open scoped nonZeroDivisors Pointwise Topology UpperHalfPlane

namespace HilbertModularForm

variable {F : Type*} [Field F] {𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {𝔑 : Ideal (𝓞 F)}
  {α : GL (Fin 2) F} {v : (𝓞 F)ˣ} (hv : IsTotallyPositive (unitF v : F))

variable (𝔟 𝔑 α) in
/-- The **exponent of the cusp `α ∞`** of `Γ = Γ₀(𝔑)_𝔟`: the factorial `M` of the index of
`Γ ∩ α⁻¹Γα` in `Γ`, which is finite for `𝔑 ≠ 0`, so that `α γ^M α⁻¹ ∈ Γ` for every `γ ∈ Γ`
(`HilbertModularForm.mul_pow_cuspExponent_mul_inv_mem`). -/
noncomputable def cuspExponent : ℕ :=
  ((MulAut.conj α⁻¹ • gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑).relIndex
    (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑)).factorial

lemma cuspExponent_ne_zero : cuspExponent 𝔟 𝔑 α ≠ 0 :=
  Nat.factorial_ne_zero _

variable [NumberField F] {k : {w : InfinitePlace F // w.IsReal} → ℤ}
  {f : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ}

lemma mul_pow_cuspExponent_mul_inv_mem (h𝔑 : 𝔑 ≠ ⊥) {γ : GL (Fin 2) F}
    (hγ : γ ∈ gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑) :
    α * γ ^ cuspExponent 𝔟 𝔑 α * α⁻¹ ∈
      gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑 := by
  have h : γ ^ cuspExponent 𝔟 𝔑 α ∈
      MulAut.conj α⁻¹ • gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑 :=
    (mem_inf.mp (pow_mem_of_relIndex_ne_zero_of_dvd (isFiniteRelIndex_iff_relIndex_ne_zero.mp
      (isFiniteRelIndex_conj_smul_gammaZero (Units.ne_zero 𝔟) h𝔑 α⁻¹)) hγ
        fun _ hm hle ↦ Nat.dvd_factorial hm hle)).1
  rwa [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv] at h

variable (𝔟 𝔑 α) in
/-- The invertible fractional ideal `𝔞 = 𝔟M⁻¹` of the cusp `α ∞`, `M` its exponent: the translations
by `𝔞⁻¹ = M𝔟⁻¹` lie in `α⁻¹Γ₀(𝔑)_𝔟α`, so that the Fourier expansion of `f ∣ₖ α` runs over the trace
dual `(𝔞⁻¹)^∨` (`HilbertModularForm.hasHilbertFourierExpansion_slash`). -/
noncomputable def cuspIdeal : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  (toPrincipalIdeal (𝓞 F) F (Units.mk0 (cuspExponent 𝔟 𝔑 α : F)
    (Nat.cast_ne_zero.mpr cuspExponent_ne_zero)) * 𝔟⁻¹)⁻¹

lemma mem_inv_cuspIdeal {x : F} : x ∈ (↑(cuspIdeal 𝔟 𝔑 α)⁻¹ : FractionalIdeal (𝓞 F)⁰ F) ↔
    ∃ b ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F), x = cuspExponent 𝔟 𝔑 α * b := by
  rw [cuspIdeal, inv_inv, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0,
    FractionalIdeal.mem_singleton_mul]

lemma slash_slash_eq_of_mem (hα : α.det = 1)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑))
    {x : GL (Fin 2) F}
    (hx : α * x * α⁻¹ ∈ gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑) :
    slash k x (slash k α f) = slash k α f := by
  have hα' : IsTotallyPositive α.det.val := by
    rw [hα, Units.val_one]
    exact isTotallyPositive_one
  have hx' : IsTotallyPositive x.det.val := by
    have h : IsTotallyPositive (α * x * α⁻¹).det.val := isTotallyPositive_det_of_mem_gammaZero hx
    rwa [map_mul, map_mul, map_inv, hα, one_mul, inv_one, mul_one] at h
  rw [← slash_mul k α x f hα' hx', ← inv_mul_cancel_right (α * x) α,
    slash_mul k _ α f (isTotallyPositive_det_of_mem_gammaZero hx) hα', hΓ _ hx]

lemma isTranslationInvariant_slash (h𝔑 : 𝔑 ≠ ⊥) (hα : α.det = 1)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑)) :
    IsTranslationInvariant (cuspIdeal 𝔟 𝔑 α) (slash k α f) :=
  isTranslationInvariant_of_slash_eq fun _ hx ↦ by
    rcases mem_inv_cuspIdeal.mp hx with ⟨b, hb, rfl⟩
    rw [← heckeUpper_one_pow]
    exact slash_slash_eq_of_mem hα hΓ (mul_pow_cuspExponent_mul_inv_mem h𝔑
      (heckeUpper_one_mem_gammaZero hb))

lemma slash_heckeDiagonal_slash (h𝔑 : 𝔑 ≠ ⊥) (hα : α.det = 1)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑)) :
    slash k (heckeDiagonal (unitF (v ^ cuspExponent 𝔟 𝔑 α)) (isTotallyPositive_unitF_pow hv))
      (slash k α f) = slash k α f := by
  rw [← coe_heckeDiagonal_unitF_pow hv]
  exact slash_slash_eq_of_mem hα hΓ (mul_pow_cuspExponent_mul_inv_mem h𝔑
    (heckeDiagonal_mem_gammaZero hv))

variable [IsTotallyReal F]

/-- **Fourier expansions at every cusp** (LMFDB `mf.hilbert.q_expansion`): for `F` totally real,
`𝔑 ≠ 0` and `f` holomorphic on `ℍⁿ` with the transformation law for `Γ₀(𝔑)_𝔟`, such as a component
of a Hilbert modular form, the slash `f ∣ₖ α` by every `α ∈ SL₂(F)` is the sum of its Fourier
series over the trace dual of `M𝔟⁻¹`, `M` the exponent of the cusp `α ∞`. -/
lemma hasHilbertFourierExpansion_slash (h𝔑 : 𝔑 ≠ ⊥) (hf : IsHolomorphic f)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑))
    (hα : α.det = 1) : HasHilbertFourierExpansion (cuspIdeal 𝔟 𝔑 α) (slash k α f)
      (fourierCoeff (cuspIdeal 𝔟 𝔑 α) (slash k α f)) :=
  hasHilbertFourierExpansion_fourierCoeff _
    (hf.slash (by rw [hα, Units.val_one]; exact isTotallyPositive_one))
    (isTranslationInvariant_slash h𝔑 hα hΓ)

/-- **Koecher's principle at every cusp** (LMFDB `mf.hilbert.q_expansion`): for `F` totally real of
degree `> 1`, `𝔑 ≠ 0`, `f` with the transformation law for `Γ₀(𝔑)_𝔟` and `α ∈ SL₂(F)`, every
Fourier coefficient `a(ν) ≠ 0` of `f ∣ₖ α`, over any lattice, has `ν = 0` or `ν` totally
positive. -/
lemma HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive_slash (hF : 1 < finrank ℚ F)
    (h𝔑 : 𝔑 ≠ ⊥)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑))
    (hα : α.det = 1) {𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {a : fourierDual 𝔞 → ℂ}
    (ha : HasHilbertFourierExpansion 𝔞 (slash k α f) a) {ν : fourierDual 𝔞} (hν : a ν ≠ 0) :
    (ν : F) = 0 ∨ IsTotallyPositive (ν : F) :=
  ha.eq_zero_or_isTotallyPositive hF cuspExponent_ne_zero
    (fun _ hv ↦ slash_heckeDiagonal_slash hv h𝔑 hα hΓ) hν

/-- **Hilbert modular forms are bounded at the cusps** (Koecher): for `F` totally real of degree
`> 1` and `𝔑 ≠ 0`, a holomorphic function on `ℍⁿ` with the transformation law of weight `k` for
`Γ₀(𝔑)_𝔟` is bounded at every cusp. -/
lemma isBoundedAtCusps_of_mem_slashInvariants (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥)
    (hf : IsHolomorphic f)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑)) :
    IsBoundedAtCusps k f :=
  fun _ hα ↦ (hasHilbertFourierExpansion_slash h𝔑 hf hΓ hα).boundedAtFilter fun _ hν ↦
    (hasHilbertFourierExpansion_slash h𝔑 hf hΓ hα).eq_zero_or_isTotallyPositive_slash hF h𝔑 hΓ hα hν

lemma tendsto_slash_atImInfty (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥) (hf : IsHolomorphic f)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑))
    (hα : α.det = 1) : Tendsto (slash k α f) atImInfty
      (𝓝 (fourierCoeff (cuspIdeal 𝔟 𝔑 α) (slash k α f) ⟨0, (fourierDual _).zero_mem⟩)) :=
  (hasHilbertFourierExpansion_slash h𝔑 hf hΓ hα).tendsto_atImInfty fun _ hν ↦
    (hasHilbertFourierExpansion_slash h𝔑 hf hΓ hα).eq_zero_or_isTotallyPositive_slash hF h𝔑 hΓ hα hν

/-- **Vanishing at the cusps is the vanishing of the constant terms**: for `F` totally real of
degree `> 1`, `𝔑 ≠ 0` and `f` holomorphic with the transformation law for `Γ₀(𝔑)_𝔟`, `f ∣ₖ α`
tends to the constant term of its Fourier expansion at the cusp `α ∞`, so `f` vanishes at the
cusps exactly when all these constant terms vanish. -/
lemma vanishesAtCusps_iff (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥) (hf : IsHolomorphic f)
    (hΓ : f ∈ slashInvariants k (gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑)) :
    VanishesAtCusps k f ↔ ∀ α : GL (Fin 2) F, α.det = 1 →
      fourierCoeff (cuspIdeal 𝔟 𝔑 α) (slash k α f) ⟨0, (fourierDual _).zero_mem⟩ = 0 :=
  forall₂_congr fun _ hα ↦ ⟨tendsto_nhds_unique (tendsto_slash_atImInfty hF h𝔑 hf hΓ hα),
    fun h ↦ h ▸ tendsto_slash_atImInfty hF h𝔑 hf hΓ hα⟩

variable {𝔠 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔠 : ∀ c, NarrowClassGroup.mk (𝔠 c) = c} {ψ : HilbertModularForm 𝔑 k 𝔠 h𝔠}
  {φ : NarrowClassGroup F → ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ}

variable (ψ) in
/-- **Hilbert cusp forms are the forms whose constant terms vanish at every cusp** (LMFDB
`mf.hilbert`): for `F` totally real of degree `> 1` and `𝔑 ≠ 0`, a Hilbert modular form is a cusp
form exactly when, for every component `ψ_c` and every `α ∈ SL₂(F)`, the constant term of the
Fourier expansion of `ψ_c ∣ₖ α` vanishes. -/
lemma isCuspForm_iff (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥) : ψ.IsCuspForm ↔
    ∀ c, ∀ α : GL (Fin 2) F, α.det = 1 →
      fourierCoeff (cuspIdeal (𝔠 c) 𝔑 α) (slash k α (ψ.toFun c)) ⟨0, (fourierDual _).zero_mem⟩ =
        0 :=
  forall_congr' fun c ↦
    vanishesAtCusps_iff hF h𝔑 (ψ.isHolomorphic c) (ψ.toFun_mem_slashInvariants c)

/-- **The components of a Hilbert cusp form have no constant term** (LMFDB
`mf.hilbert.q_expansion`): for `F` totally real of degree `> 1`, the Fourier expansion of every
component `ψ_c` of a Hilbert cusp form runs over the totally positive `ν` only. -/
lemma fourierCoeff_toFun_zero (hF : 1 < finrank ℚ F) (hψ : ψ.IsCuspForm) (c : NarrowClassGroup F) :
    fourierCoeff (𝔠 c) (ψ.toFun c) ⟨0, (fourierDual _).zero_mem⟩ = 0 :=
  tendsto_nhds_unique ((ψ.hasHilbertFourierExpansion_toFun c).tendsto_atImInfty fun _ hν ↦
    koecherPrinciple ‹_› hF 𝔑 k 𝔠 h𝔠 ψ c _ (ψ.hasHilbertFourierExpansion_toFun c) _ hν)
    (by simpa [slash_one] using hψ c 1 (map_one _))

/-- **The space of Hilbert modular forms is the space of the knowl** (LMFDB `mf.hilbert`): for `F`
totally real of degree `> 1` and `𝔑 ≠ 0`, a tuple `(φ_c)` of functions on `ℍⁿ` lies in
`HilbertModularForm.space` exactly when each `φ_c` is holomorphic and satisfies the transformation
law for `Γ₀(𝔑)_{𝔟_c}`: no condition at the cusps is needed. -/
lemma mem_space_iff (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥) : φ ∈ space k 𝔑 𝔠 ↔
    ∀ c, IsHolomorphic (φ c) ∧
      ∀ γ ∈ gammaZero (𝔠 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔠 c : _)) 𝔑,
        ∀ z, φ c (smul γ z) = automorphyFactor k γ z * φ c z := by
  refine forall_congr' fun c ↦ ⟨fun h ↦ ⟨h.1, (mem_slashInvariants_iff fun _ ↦
    isTotallyPositive_det_of_mem_gammaZero).mp h.2.2⟩, fun h ↦ ?_⟩
  have hΓ : φ c ∈ slashInvariants k
      (gammaZero (𝔠 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔠 c : _)) 𝔑) :=
    (mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mpr h.2
  exact ⟨h.1, isBoundedAtCusps_of_mem_slashInvariants hF h𝔑 h.1 hΓ, hΓ⟩

variable (φ) in
/-- The **Hilbert modular form** (LMFDB `mf.hilbert`) of weight `k` and level `𝔑 ≠ 0` defined, as by
the LMFDB, by a tuple `(φ_c)` of holomorphic functions on `ℍⁿ`, `F` totally real of degree `> 1`,
with the transformation law for `Γ₀(𝔑)_{𝔟_c}`: boundedness at the cusps is automatic
(`HilbertModularForm.isBoundedAtCusps_of_mem_slashInvariants`). -/
def ofSmulEq (hF : 1 < finrank ℚ F) (h𝔑 : 𝔑 ≠ ⊥) (hφ : ∀ c, IsHolomorphic (φ c))
    (hγ : ∀ c, ∀ γ ∈ gammaZero (𝔠 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔠 c : _)) 𝔑,
      ∀ z, φ c (smul γ z) = automorphyFactor k γ z * φ c z) : HilbertModularForm 𝔑 k 𝔠 h𝔠 where
  toFun := φ
  isHolomorphic := hφ
  isBoundedAtCusps c := isBoundedAtCusps_of_mem_slashInvariants hF h𝔑 (hφ c)
    ((mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mpr (hγ c))
  smul_eq := hγ

end HilbertModularForm
