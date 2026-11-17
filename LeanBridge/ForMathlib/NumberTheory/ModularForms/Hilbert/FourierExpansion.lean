import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierUniqueness
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Fourier expansions of Hilbert modular forms

Let `F` be a number field and `𝔟` an invertible fractional ideal. The translations
`z ↦ z + b = (1, b; 0, 1) z` in `Γ₀(𝔑)_𝔟` are those with `b ∈ 𝔟⁻¹`, so a component `f_c` of a
Hilbert modular form (LMFDB `mf.hilbert`) is invariant under `z ↦ z + b`, `b ∈ 𝔟⁻¹`, and has a
Fourier expansion `f_c(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` over the trace dual
`(𝔟⁻¹)^∨ = 𝔟𝔡⁻¹` of `𝔟⁻¹`, with `Tr(νz) = ∑_w w(ν) z_w`, the sum over the real places `w`.

When `F` is totally real, the expansion is unique: on the points
`z = ∑_j x_j e_j + i` for a `ℤ`-basis `(e_j)` of `𝔟⁻¹`, it is an absolutely convergent Fourier
series in `x ∈ (ℝ / ℤ)ⁿ`, with coefficients `a(ν) e^{-2π Tr ν}`, and the torus argument of
`Siegel/FourierUniqueness.lean` applies.

A Fourier series supported on `0` and the totally positive `ν` is bounded when all the imaginary
parts are at least `1`, since `|e^{2πi Tr(νz)}| = e^{-2π ∑_w w(ν) Im z_w}` decreases in each
`Im z_w`, and it tends to its constant term as all the imaginary parts tend to infinity.

## Main definitions

* `HilbertModularForm.fourierDual`: the trace dual `(𝔟⁻¹)^∨` of the translation lattice `𝔟⁻¹`.
* `HilbertModularForm.fourierExp`: the exponential `e^{2πi Tr(νz)}`.
* `HilbertModularForm.HasHilbertFourierExpansion` (LMFDB `mf.hilbert.q_expansion`): `a` is the
  family of Fourier coefficients of a function on `ℍⁿ`.
* `HilbertModularForm.fourierCoeff` (LMFDB `mf.hilbert.q_expansion`): the Fourier coefficients of
  a function on `ℍⁿ`.
* `HilbertModularForm.KoecherPrinciple`: the statement that the expansions of Hilbert modular forms
  are supported on `0` and the totally positive `ν`, in degree `> 1`.

## Main results

* `HilbertModularForm.fourierDual_eq`: `(𝔟⁻¹)^∨ = 𝔟𝔡⁻¹`.
* `HilbertModularForm.HasHilbertFourierExpansion.add` and
  `HilbertModularForm.HasHilbertFourierExpansion.const_smul`: Fourier expansions are linear.
* `HilbertModularForm.coe_trace_eq_sum`: for `F` totally real, `Tr(x) = ∑_w w(x)`.
* `HilbertModularForm.eq_zero_of_hasSum_fourierExp`: if `∑ c(ν) e^{2πi Tr(νz)} = 0` on `ℍⁿ`, then
  `c = 0`.
* `HilbertModularForm.HasHilbertFourierExpansion.unique`: Fourier expansions are unique.
* `HilbertModularForm.HasHilbertFourierExpansion.fourierCoeff_eq`: the Fourier coefficients of a
  function with a Fourier expansion `a` are `a`.
* `HilbertModularForm.HasHilbertFourierExpansion.boundedAtFilter`: a Fourier series supported on `0`
  and the totally positive `ν` is bounded as all the imaginary parts tend to infinity.
* `HilbertModularForm.HasHilbertFourierExpansion.tendsto_atImInfty`: it tends to its constant term.
-/

open Asymptotics Complex Filter NumberField InfinitePlace Real UnitAddTorus

open scoped nonZeroDivisors Topology UpperHalfPlane

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] (𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- The **trace dual** `(𝔟⁻¹)^∨ = {ν ∈ F : Tr(ν 𝔟⁻¹) ⊆ ℤ}` of the lattice `𝔟⁻¹` of the translations
of `Γ₀(𝔑)_𝔟`: the index set of the Fourier expansion of the component of `𝔟`. It is `𝔟𝔡⁻¹`, `𝔡`
the different (`HilbertModularForm.fourierDual_eq`). -/
noncomputable def fourierDual : FractionalIdeal (𝓞 F)⁰ F :=
  FractionalIdeal.dual ℤ ℚ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)

/-- **The trace dual of `𝔟⁻¹` is `𝔟𝔡⁻¹`**, `𝔡` the different of `𝒪_F`. -/
lemma fourierDual_eq :
    fourierDual 𝔟 = 𝔟 * (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
  rw [fourierDual, FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ F, inv_inv,
    Units.val_inv_eq_inv_val, inv_inv, mul_comm]

open scoped Classical in
/-- The exponential `e^{2πi Tr(νz)}` of the Fourier expansion of a Hilbert modular form, with
`Tr(νz) = ∑_w w(ν) z_w` over the real places `w`, for `ν ∈ F` and `z ∈ ℍⁿ`. -/
noncomputable def fourierExp (ν : F) (z : {w : InfinitePlace F // w.IsReal} → ℍ) : ℂ :=
  cexp (2 * π * I * ∑ w, (embedding_of_isReal w.2 ν : ℂ) * (z w : ℂ))

open scoped Classical in
lemma norm_fourierExp (z : {w : InfinitePlace F // w.IsReal} → ℍ) (x : F) :
    ‖fourierExp x z‖ = Real.exp (-(2 * π * ∑ w, embedding_of_isReal w.2 x * (z w).im)) := by
  have e : 2 * π * I * ∑ w, (embedding_of_isReal w.2 x : ℂ) * (z w : ℂ) =
      ((2 * π : ℝ) : ℂ) * (I * ∑ w, (embedding_of_isReal w.2 x : ℂ) * (z w : ℂ)) := by
    push_cast
    ring1
  rw [fourierExp, Complex.norm_exp, e, re_ofReal_mul, I_mul_re, im_sum]
  simp only [im_ofReal_mul, UpperHalfPlane.coe_im, mul_neg]

variable {φ ψ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ} {a b : fourierDual 𝔟 → ℂ}

variable (φ a) in
/-- The family `a : (𝔟⁻¹)^∨ → ℂ` is **the family of Fourier coefficients** of `φ : ℍⁿ → ℂ`
(LMFDB `mf.hilbert.q_expansion`): `φ(z) = ∑_{ν ∈ (𝔟⁻¹)^∨} a(ν) e^{2πi Tr(νz)}` for every `z ∈ ℍⁿ`,
the sum converging unconditionally. For the component `f_c` of a Hilbert modular form, `𝔟 = 𝔟_c`:
the translations of `Γ₀(𝔑)_𝔟` are by `𝔟⁻¹`, and `(𝔟⁻¹)^∨ = 𝔟𝔡⁻¹`. The knowl writes the cusp as
`𝔞 = 𝔟⁻¹` and the index as `u ∈ (𝔞𝔡)⁻¹`; it also sums over the totally positive `u` only, which
for a Hilbert modular form in degree `> 1` is a theorem (`HilbertModularForm.koecherPrinciple`), not
part of the definition. The coefficients are unique when `F` is totally real
(`HilbertModularForm.HasHilbertFourierExpansion.unique`), and every component of a Hilbert modular
form over a totally real field has an expansion
(`HilbertModularForm.hasHilbertFourierExpansion_toFun`, in `Hilbert/KoecherPrinciple.lean`). -/
def HasHilbertFourierExpansion : Prop :=
  ∀ z, HasSum (fun ν ↦ a ν * fourierExp (ν : F) z) (φ z)

/-- **Fourier expansions are additive**. -/
lemma HasHilbertFourierExpansion.add (hφ : HasHilbertFourierExpansion 𝔟 φ a)
    (hψ : HasHilbertFourierExpansion 𝔟 ψ b) : HasHilbertFourierExpansion 𝔟 (φ + ψ) (a + b) :=
  fun z ↦ by simpa [add_mul] using (hφ z).add (hψ z)

/-- **Fourier expansions are `ℂ`-linear**. -/
lemma HasHilbertFourierExpansion.const_smul (hφ : HasHilbertFourierExpansion 𝔟 φ a) (c : ℂ) :
    HasHilbertFourierExpansion 𝔟 (c • φ) (c • a) :=
  fun z ↦ by simpa [mul_assoc] using (hφ z).mul_left c

open scoped Classical in
/-- **For `F` totally real, the trace is the sum over the real places**: `Tr(x) = ∑_w w(x)`. -/
lemma coe_trace_eq_sum [IsTotallyReal F] (x : F) :
    (Algebra.trace ℚ F x : ℂ) =
      ∑ w : {w : InfinitePlace F // w.IsReal}, (embedding_of_isReal w.2 x : ℂ) := by
  have h : algebraMap ℚ ℂ (Algebra.trace ℚ F x) = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    trace_eq_sum_embeddings ℂ
  rw [eq_ratCast] at h
  rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp, ← mkReal.sum_comp,
    ← (Equiv.subtypeUnivEquiv IsTotallyReal.complexEmbedding_isReal).sum_comp]
  refine Finset.sum_congr rfl fun φ _ ↦ ?_
  rw [embedding_of_isReal_apply, mkReal_coe, embedding_mk_eq_of_isReal φ.2]
  rfl

private lemma eq_of_trace_mul_eq {ι : Type*} (e : Module.Basis ι ℚ F) {ν μ : F}
    (h : ∀ j, Algebra.trace ℚ F (ν * e j) = Algebra.trace ℚ F (μ * e j)) : ν = μ := by
  by_contra hne
  have h' : Algebra.traceForm ℚ F (ν - μ) = 0 :=
    e.ext fun j ↦ by simp [h j]
  have h1 : Algebra.trace ℚ F ((ν - μ) * (ν - μ)⁻¹) = 0 :=
    LinearMap.congr_fun h' _
  rw [mul_inv_cancel₀ (sub_ne_zero.mpr hne), ← map_one (algebraMap ℚ F), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact Module.finrank_pos.ne' h1

variable {ι : Type*} [Fintype ι]

/-- The point `∑_j x_j e_j + i` of `ℍⁿ`, for real `x_j` and `e_j ∈ F`. -/
private noncomputable def torusPoint (e : ι → F) (x : ι → ℝ) :
    {w : InfinitePlace F // w.IsReal} → ℍ :=
  fun w ↦ ⟨((∑ j, x j * embedding_of_isReal w.2 (e j) : ℝ) : ℂ) + I, by
    rw [add_im, ofReal_im, I_im, zero_add]
    exact one_pos⟩

open scoped Classical in
private lemma fourierExp_torusPoint [IsTotallyReal F] (e : ι → F) (x : ι → ℝ) (ν : F) {k : ι → ℤ}
    (hk : ∀ j, (k j : ℚ) = Algebra.trace ℚ F (ν * e j)) :
    fourierExp ν (torusPoint e x) =
      mFourier k (fun j ↦ (x j : UnitAddCircle)) * cexp (-2 * π * Algebra.trace ℚ F ν) := by
  have hk' (j : ι) : (k j : ℂ) = ∑ w : {w : InfinitePlace F // w.IsReal},
      (embedding_of_isReal w.2 ν : ℂ) * embedding_of_isReal w.2 (e j) := by
    rw [← Rat.cast_intCast, hk, coe_trace_eq_sum]
    simp only [map_mul, ofReal_mul]
  simp only [fourierExp, torusPoint, mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    ← Complex.exp_sum, ← Complex.exp_add, hk', coe_trace_eq_sum]
  congr 1
  push_cast
  simp only [mul_add, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, div_one]
  rw [Finset.sum_comm]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring1)
    (Finset.sum_congr rfl fun w _ ↦ by
      linear_combination 2 * π * (embedding_of_isReal w.2 ν : ℂ) * I_sq)

lemma exists_intCast_eq_trace (ν : fourierDual 𝔟)
    (j : Module.Free.ChooseBasisIndex ℤ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ F (ν * basisOfFractionalIdeal F 𝔟⁻¹ j) := by
  rw [basisOfFractionalIdeal_apply]
  rcases (FractionalIdeal.mem_dual (Units.ne_zero _)).mp ν.2 _
    (fractionalIdealBasis F (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) j).2 with ⟨z, hz⟩
  exact ⟨z, hz⟩

open scoped Classical in
/-- **Uniqueness of Hilbert Fourier expansions**: for `F` totally real, if
`∑_{ν ∈ (𝔟⁻¹)^∨} c(ν) e^{2πi Tr(νz)} = 0` for every `z ∈ ℍⁿ`, the sum converging unconditionally,
then `c = 0`. -/
lemma eq_zero_of_hasSum_fourierExp [IsTotallyReal F] {c : fourierDual 𝔟 → ℂ}
    (hc : ∀ z, HasSum (fun ν ↦ c ν * fourierExp (ν : F) z) 0) : c = 0 := by
  choose k hk using exists_intCast_eq_trace 𝔟
  have hinj : Function.Injective k := fun ν μ h ↦ Subtype.ext <|
    eq_of_trace_mul_eq (basisOfFractionalIdeal F 𝔟⁻¹) fun j ↦ by rw [← hk, ← hk, h]
  let d : (Module.Free.ChooseBasisIndex ℤ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) → ℤ) → ℂ :=
    Function.extend k (fun ν ↦ c ν * cexp (-2 * π * Algebra.trace ℚ F ν)) 0
  have hd (x : Module.Free.ChooseBasisIndex ℤ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) → ℝ) :
      HasSum (fun m ↦ d m * mFourier m (fun j ↦ (x j : UnitAddCircle))) 0 := by
    refine (hinj.hasSum_iff fun m hm ↦ ?_).mp
      ((hc (torusPoint (basisOfFractionalIdeal F 𝔟⁻¹) x)).congr_fun fun ν ↦ ?_)
    · rw [show d m = 0 from Function.extend_apply' _ _ _ hm, zero_mul]
    · rw [Function.comp_apply, show d (k ν) = _ from hinj.extend_apply _ _ ν,
        fourierExp_torusPoint _ x (ν : F) (hk ν)]
      ring1
  have hd0 : d = 0 := by
    refine eq_zero_of_hasSum_mFourier (by simpa [mFourier] using (hd 0).summable) fun x ↦ ?_
    choose t ht using fun j ↦ QuotientAddGroup.mk_surjective (x j)
    exact (funext ht : (fun j ↦ (t j : UnitAddCircle)) = x) ▸ hd t
  funext ν
  simpa [d, hinj.extend_apply] using congrFun hd0 (k ν)

/-- **Fourier expansions are unique**: for `F` totally real, two families of Fourier coefficients
of the same `φ : ℍⁿ → ℂ` are equal. -/
lemma HasHilbertFourierExpansion.unique [IsTotallyReal F] (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hb : HasHilbertFourierExpansion 𝔟 φ b) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_hasSum_fourierExp 𝔟 fun z ↦ by
    simpa [sub_mul] using (ha z).sub (hb z)

variable (φ) in
open scoped Classical in
/-- The **Fourier coefficients** `a(ν)`, `ν ∈ (𝔟⁻¹)^∨`, of `φ : ℍⁿ → ℂ` (LMFDB
`mf.hilbert.q_expansion`): the family of coefficients of a Fourier expansion of `φ`, unique when `F`
is totally real (`HilbertModularForm.HasHilbertFourierExpansion.fourierCoeff_eq`), and the junk
value `0` if `φ` has no Fourier expansion. -/
noncomputable def fourierCoeff : fourierDual 𝔟 → ℂ :=
  if h : ∃ a, HasHilbertFourierExpansion 𝔟 φ a then h.choose else 0

/-- **The Fourier coefficients of a function with a Fourier expansion `a` are `a`**, for `F`
totally real. -/
lemma HasHilbertFourierExpansion.fourierCoeff_eq [IsTotallyReal F]
    (ha : HasHilbertFourierExpansion 𝔟 φ a) : fourierCoeff 𝔟 φ = a := by
  rw [fourierCoeff, dite_eq_left_of_eq_true (eq_true ⟨a, ha⟩)]
  exact (Exists.choose_spec ⟨a, ha⟩).unique 𝔟 ha

variable (F) in
/-- The **Koecher principle** for Hilbert modular forms, as a statement: if `F` is totally real of
degree `> 1`, then every Fourier coefficient `a(ν) ≠ 0` of a component `f_c` of a Hilbert modular
form (LMFDB `mf.hilbert`) is indexed by `ν = 0` or a totally positive `ν`; this is why the knowl's
expansion (LMFDB `mf.hilbert.q_expansion`) runs over the totally positive `u` (and `0`). It is
proved in `Hilbert/KoecherPrinciple.lean` (`HilbertModularForm.koecherPrinciple`). -/
def KoecherPrinciple : Prop :=
  IsTotallyReal F → 1 < Module.finrank ℚ F → ∀ (𝔑 : Ideal (𝓞 F))
    (k : {w : InfinitePlace F // w.IsReal} → ℤ)
    (𝔠 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (h𝔠 : ∀ c, NarrowClassGroup.mk (𝔠 c) = c)
    (f : HilbertModularForm 𝔑 k 𝔠 h𝔠) (c : NarrowClassGroup F) (a : fourierDual (𝔠 c) → ℂ),
    HasHilbertFourierExpansion (𝔠 c) (f.toFun c) a → ∀ ν, a ν ≠ 0 →
      (ν : F) = 0 ∨ IsTotallyPositive (ν : F)

variable {𝔟} {ν : fourierDual 𝔟}

variable (ν) in
private lemma norm_mul_fourierExp_le {z : {w : InfinitePlace F // w.IsReal} → ℍ}
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) (hz : ∀ w, 1 ≤ (z w).im) :
    ‖a ν * fourierExp (ν : F) z‖ ≤ ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖ := by
  by_cases hν : a ν = 0
  · simp [hν]
  have hpos (w : {w : InfinitePlace F // w.IsReal}) : 0 ≤ embedding_of_isReal w.2 (ν : F) := by
    rcases hsupp ν hν with h | h
    · simp [h]
    · exact (h w.1 w.2).le
  rw [norm_mul, norm_mul, norm_fourierExp, norm_fourierExp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  simp only [UpperHalfPlane.I_im, mul_one, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ ↦
    le_mul_of_one_le_right (hpos w) (hz w)) Real.two_pi_pos.le

/-- **Fourier series supported on `0` and the totally positive `ν` are bounded at infinity**: if
`φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` with `a(ν) ≠ 0` only for `ν = 0` and `ν` totally positive, then `φ`
is bounded on `{z : Im z_w ≥ 1 for all w}`, by the sum of the `|a(ν)| e^{-2π Tr ν}`. -/
lemma HasHilbertFourierExpansion.boundedAtFilter (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) :
    BoundedAtFilter atImInfty φ := by
  have hs : Summable fun ν ↦ ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖ :=
    summable_norm_iff.mpr (ha _).summable
  refine IsBigO.of_bound (∑' ν, ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖) ?_
  filter_upwards [eventually_le_im 1] with z hz
  have hs' : Summable fun ν ↦ ‖a ν * fourierExp (ν : F) z‖ :=
    hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_mul_fourierExp_le · hsupp hz)
  rw [Pi.one_apply, norm_one, mul_one, ← (ha z).tsum_eq]
  exact (norm_tsum_le_tsum_norm hs').trans
    (hs'.tsum_le_tsum (norm_mul_fourierExp_le · hsupp hz) hs)

open scoped Classical in
private lemma tendsto_sum_mul_im {c : {w : InfinitePlace F // w.IsReal} → ℝ} (hc : ∀ w, 0 < c w)
    (w₀ : {w : InfinitePlace F // w.IsReal}) : Tendsto
      (fun z : {w : InfinitePlace F // w.IsReal} → ℍ ↦ ∑ w, c w * (z w).im) atImInfty atTop := by
  have h : Tendsto (fun (z : {w : InfinitePlace F // w.IsReal} → ℍ) w ↦ (z w).im) atImInfty
      (pi fun _ ↦ atTop) :=
    tendsto_comap
  exact tendsto_atTop_mono (fun z ↦ Finset.single_le_sum (fun w _ ↦
    (mul_pos (hc w) (z w).im_pos).le) (Finset.mem_univ w₀)) ((tendsto_pi.mp h w₀).const_mul_atTop
      (hc w₀))

variable [IsTotallyReal F] in
private lemma tendsto_mul_fourierExp (hν : IsTotallyPositive (ν : F)) :
    Tendsto (fun z ↦ a ν * fourierExp (ν : F) z) atImInfty (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simp only [norm_mul, norm_fourierExp]
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_sum_mul_im (fun w ↦ hν w.1 w.2)
    ⟨Classical.arbitrary (InfinitePlace F), IsTotallyReal.isReal _⟩).const_mul_atTop
      Real.two_pi_pos)).const_mul ‖a ν‖

variable [IsTotallyReal F] in
open scoped Classical in
/-- **The limit at infinity of a Fourier series supported on `0` and the totally positive `ν` is its
constant term**: if `φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` with `a(ν) ≠ 0` only for `ν = 0` and `ν`
totally positive, then `φ(z) → a(0)` as all the imaginary parts tend to infinity (Tannery's
theorem, the terms being dominated by the `|a(ν)| e^{-2π Tr ν}`). -/
lemma HasHilbertFourierExpansion.tendsto_atImInfty (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) :
    Tendsto φ atImInfty (𝓝 (a ⟨0, (fourierDual 𝔟).zero_mem⟩)) := by
  have h : Tendsto (fun z ↦ ∑' ν, a ν * fourierExp (ν : F) z) atImInfty
      (𝓝 (∑' ν, if ν = ⟨0, (fourierDual 𝔟).zero_mem⟩ then a ν else 0)) :=
    tendsto_tsum_of_dominated_convergence (summable_norm_iff.mpr (ha _).summable) (fun ν ↦ ?_)
      ((eventually_le_im 1).mono fun _ hz ↦ (norm_mul_fourierExp_le · hsupp hz))
  · rw [tsum_ite_eq] at h
    exact h.congr fun z ↦ (ha z).tsum_eq
  · by_cases hν : ν = ⟨0, (fourierDual 𝔟).zero_mem⟩
    · simp [hν, fourierExp]
    rw [ite_eq_right hν]
    by_cases haν : a ν = 0
    · simp [haν]
    exact tendsto_mul_fourierExp <| (hsupp ν haν).resolve_left fun h ↦ hν (Subtype.ext h)

end HilbertModularForm
