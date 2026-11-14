import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.PolarizationDegree
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrderDiscriminant

/-!
# The reduced trace and the reduced norm of a quaternion algebra over `ℚ`

Let `B` be a quaternion algebra over `ℚ`, a central simple `ℚ`-algebra of dimension `4`, with its
reduced trace `trd` and reduced norm `nrd` (`QuaternionAlgebra.reducedTrace`,
`QuaternionAlgebra.reducedNorm`: half the trace of left multiplication, and
`(trd(x)² - trd(x²)) / 2`). This file collects the algebra of `trd` and `nrd` that the arithmetic
of the orders of `B` uses: every `x` satisfies `x² = trd(x) x - nrd(x)`, the reduced norm is
multiplicative, the trace of `z ↦ x z y` on `B` is `trd(x) trd(y)`, and an element commuting with
a `μ` such that `μ²` is a negative rational number lies in `ℚ + ℚ μ`. On an order `O` of `B` the
reduced norm is an integer, and a `ℚ`-linear endomorphism of `B` that maps `O` into itself has an
integral trace.

The identities are transported from Mathlib's `ℍ[ℚ,a,b]`, to which `B` is isomorphic
(`QuaternionAlgebra.exists_nonempty_algEquiv_of_finrank_eq_four`), where they are computations in
the basis `1, i, j, k` or instances of Tau Ceti's `QuaternionAlgebra.normForm_mul`.

## Main definitions

* `QuaternionAlgebra.reducedTraceₗ`: the reduced trace as a `ℚ`-linear map.

## Main results

* `QuaternionAlgebra.mul_self_eq_reducedTrace_smul_sub`: `x² = trd(x) x - nrd(x)`.
* `QuaternionAlgebra.reducedNorm_mul`: the reduced norm is multiplicative.
* `QuaternionAlgebra.trace_mulLeft_comp_mulRight`: the trace of `z ↦ x z y` is `trd(x) trd(y)`.
* `QuaternionAlgebra.eq_algebraMap_add_smul_of_mul_comm`: the centraliser of an element `μ` whose
  square is a negative rational number is `ℚ + ℚ μ`.
* `Subalgebra.exists_reducedNorm_eq_intCast`: the reduced norm is an integer on an order.
* `Subalgebra.exists_trace_eq_intCast`: a `ℚ`-linear endomorphism of `B` mapping an order into
  itself has an integral trace.
-/

open Module Polynomial QuaternionAlgebra

open scoped Quaternion

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- The **reduced trace** of a quaternion algebra `B` over `ℚ` as a `ℚ`-linear map `B → ℚ`. -/
noncomputable def reducedTraceₗ : B →ₗ[ℚ] ℚ :=
  (2⁻¹ : ℚ) • (LinearMap.trace ℚ B ∘ₗ LinearMap.mul ℚ B)

variable {B} (x y : B) (q : ℚ)

lemma reducedTraceₗ_apply : reducedTraceₗ B x = reducedTrace B x := by
  rw [reducedTrace, div_eq_inv_mul]
  rfl

lemma reducedTrace_add : reducedTrace B (x + y) = reducedTrace B x + reducedTrace B y := by
  simp only [← reducedTraceₗ_apply, map_add]

lemma reducedTrace_sub : reducedTrace B (x - y) = reducedTrace B x - reducedTrace B y := by
  simp only [← reducedTraceₗ_apply, map_sub]

lemma reducedTrace_smul : reducedTrace B (q • x) = q * reducedTrace B x := by
  simp only [← reducedTraceₗ_apply, map_smul, smul_eq_mul]

lemma reducedTrace_mul_comm : reducedTrace B (x * y) = reducedTrace B (y * x) := by
  rw [reducedTrace, reducedTrace, LinearMap.mulLeft_mul, LinearMap.mulLeft_mul, ← End.mul_eq_comp,
    ← End.mul_eq_comp, LinearMap.trace_mul_comm]

lemma reducedTrace_algebraMap (h4 : finrank ℚ B = 4) :
    reducedTrace B (algebraMap ℚ B q) = 2 * q := by
  have : FiniteDimensional ℚ B := .of_finrank_pos (by omega)
  have h : LinearMap.mulLeft ℚ (algebraMap ℚ B q) = q • LinearMap.id := by
    ext z
    rw [LinearMap.mulLeft_apply, LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def]
  rw [reducedTrace, h, map_smul, LinearMap.trace_id, h4, smul_eq_mul]
  ring1

lemma reducedNorm_add : reducedNorm B (x + y) = reducedNorm B x + reducedNorm B y +
    reducedTrace B x * reducedTrace B y - reducedTrace B (x * y) := by
  have h : (x + y) ^ 2 = x ^ 2 + x * y + (y * x + y ^ 2) := by
    rw [sq, sq, sq, add_mul, mul_add, mul_add]
  rw [reducedNorm, reducedNorm, reducedNorm, h, reducedTrace_add, reducedTrace_add,
    reducedTrace_add, reducedTrace_add, reducedTrace_mul_comm y x]
  ring1

lemma reducedNorm_algebraMap (h4 : finrank ℚ B = 4) : reducedNorm B (algebraMap ℚ B q) = q ^ 2 := by
  rw [reducedNorm, ← map_pow, reducedTrace_algebraMap _ h4, reducedTrace_algebraMap _ h4]
  ring1

lemma reducedNorm_smul : reducedNorm B (q • x) = q ^ 2 * reducedNorm B x := by
  rw [reducedNorm, reducedNorm, smul_pow, reducedTrace_smul, reducedTrace_smul]
  ring1

lemma reducedNorm_algEquiv {C : Type*} [Ring C] [Algebra ℚ C] (e : C ≃ₐ[ℚ] B) (z : C) :
    reducedNorm B (e z) = reducedNorm C z := by
  rw [reducedNorm, reducedNorm, ← map_pow, reducedTrace_algEquiv, reducedTrace_algEquiv]

lemma trace_mulLeft_comp_mulRight_quaternionAlgebra {a b : ℚ} (p r : ℍ[ℚ,a,b]) :
    LinearMap.trace ℚ _ (LinearMap.mulLeft ℚ p ∘ₗ LinearMap.mulRight ℚ r) =
      2 * p.re * (2 * r.re) := by
  have hb (i : Fin 4) : basisOneIJK a 0 b i =
      ⟨![1, 0, 0, 0] i, ![0, 1, 0, 0] i, ![0, 0, 1, 0] i, ![0, 0, 0, 1] i⟩ := by
    refine (basisOneIJK a 0 b).repr.injective ?_
    ext j
    rw [(basisOneIJK a 0 b).repr_self_apply, coe_basisOneIJK_repr]
    fin_cases i <;> fin_cases j <;> simp
  rw [LinearMap.trace_eq_matrix_trace ℚ (basisOneIJK a 0 b), Matrix.trace, Fin.sum_univ_four]
  simp [LinearMap.toMatrix_apply, hb]
  ring1

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] {μ : B} {m : ℚ} {γ : Bˣ}

/-- **Every element of a quaternion algebra satisfies `x² = trd(x) x - nrd(x)`.** -/
lemma mul_self_eq_reducedTrace_smul_sub (h4 : finrank ℚ B = 4) :
    x * x = reducedTrace B x • x - algebraMap ℚ B (reducedNorm B x) := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  have h : aeval x (X ^ 2 - C (reducedTrace B x) * X + C (reducedNorm B x)) = 0 := by
    rw [← e.apply_symm_apply x, reducedTrace_algEquiv, reducedNorm_algEquiv, aeval_algHom_apply,
      reducedTrace_quaternionAlgebra, reducedNorm_quaternionAlgebra, zero_mul, add_zero,
      aeval_sq_sub_two_mul_re_add, map_zero]
  rw [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C, sq, ← Algebra.smul_def] at h
  rw [← sub_eq_zero, ← h]
  abel

/-- **The reduced norm of a quaternion algebra is multiplicative.** -/
lemma reducedNorm_mul (h4 : finrank ℚ B = 4) :
    reducedNorm B (x * y) = reducedNorm B x * reducedNorm B y := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  rw [← reducedNorm_algEquiv e.symm, ← reducedNorm_algEquiv e.symm x,
    ← reducedNorm_algEquiv e.symm y, map_mul, reducedNorm_quaternionAlgebra,
    reducedNorm_quaternionAlgebra, reducedNorm_quaternionAlgebra, ← normForm_apply,
    ← normForm_apply, ← normForm_apply, normForm_mul]

/-- **The trace of `z ↦ x z y` on a quaternion algebra is `trd(x) trd(y)`.** -/
lemma trace_mulLeft_comp_mulRight (h4 : finrank ℚ B = 4) :
    LinearMap.trace ℚ B (LinearMap.mulLeft ℚ x ∘ₗ LinearMap.mulRight ℚ y) =
      reducedTrace B x * reducedTrace B y := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  have h : LinearMap.mulLeft ℚ x ∘ₗ LinearMap.mulRight ℚ y = e.toLinearEquiv.conj
      (LinearMap.mulLeft ℚ (e.symm x) ∘ₗ LinearMap.mulRight ℚ (e.symm y)) := by
    ext z
    simp
  rw [h, LinearMap.trace_conj', trace_mulLeft_comp_mulRight_quaternionAlgebra,
    ← reducedTrace_algEquiv e.symm x, ← reducedTrace_algEquiv e.symm y,
    reducedTrace_quaternionAlgebra, reducedTrace_quaternionAlgebra]
  ring1

lemma mul_add_mul_eq (h4 : finrank ℚ B = 4) : x * y + y * x = reducedTrace B x • y +
    reducedTrace B y • x +
      algebraMap ℚ B (reducedTrace B (x * y) - reducedTrace B x * reducedTrace B y) := by
  have h : (x + y) * (x + y) = reducedTrace B (x + y) • (x + y) -
      algebraMap ℚ B (reducedNorm B (x + y)) :=
    mul_self_eq_reducedTrace_smul_sub (x + y) h4
  rw [add_mul, mul_add, mul_add, mul_self_eq_reducedTrace_smul_sub x h4,
    mul_self_eq_reducedTrace_smul_sub y h4, reducedTrace_add, reducedNorm_add] at h
  simp only [Algebra.algebraMap_eq_smul_one] at h ⊢
  rw [← sub_eq_zero, ← sub_eq_zero.mpr h]
  module

lemma reducedNorm_ne_zero (h4 : finrank ℚ B = 4) : reducedNorm B (γ : B) ≠ 0 := fun h ↦ by
  have h1 : reducedNorm B ((γ : B) * ↑γ⁻¹) = 1 := by
    rw [Units.mul_inv, ← map_one (algebraMap ℚ B), reducedNorm_algebraMap _ h4, one_pow]
  rw [reducedNorm_mul _ _ h4, h, zero_mul] at h1
  exact zero_ne_one h1

lemma reducedTrace_inv (h4 : finrank ℚ B = 4) :
    reducedTrace B (↑γ⁻¹ : B) = reducedTrace B (γ : B) / reducedNorm B (γ : B) := by
  have h : reducedNorm B (γ : B) • (↑γ⁻¹ : B) = algebraMap ℚ B (reducedTrace B (γ : B)) - γ := by
    have h1 : (↑γ⁻¹ : B) * ((γ : B) * γ) =
        ↑γ⁻¹ * (reducedTrace B (γ : B) • (γ : B) - algebraMap ℚ B (reducedNorm B (γ : B))) :=
      congrArg _ (mul_self_eq_reducedTrace_smul_sub (γ : B) h4)
    rw [Units.inv_mul_cancel_left, mul_sub, mul_smul_comm, Units.inv_mul, ← Algebra.commutes,
      ← Algebra.smul_def, ← Algebra.algebraMap_eq_smul_one] at h1
    exact eq_sub_of_add_eq' (sub_eq_iff_eq_add.mp h1.symm).symm
  have h2 : reducedTrace B (reducedNorm B (γ : B) • (↑γ⁻¹ : B)) = reducedTrace B (γ : B) := by
    rw [h, reducedTrace_sub, reducedTrace_algebraMap _ h4]
    ring1
  rw [eq_div_iff (reducedNorm_ne_zero h4), mul_comm, ← reducedTrace_smul, h2]

lemma reducedTrace_eq_zero_of_mul_self_eq (h4 : finrank ℚ B = 4) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) : reducedTrace B μ = 0 := by
  by_contra h0
  have h : reducedTrace B μ • μ = algebraMap ℚ B (m + reducedNorm B μ) := by
    rw [map_add, ← hμ, mul_self_eq_reducedTrace_smul_sub μ h4, sub_add_cancel]
  have hq : μ = algebraMap ℚ B ((reducedTrace B μ)⁻¹ * (m + reducedNorm B μ)) := by
    rw [map_mul, ← h, ← Algebra.smul_def, inv_smul_smul₀ h0]
  rw [hq, ← map_mul] at hμ
  nlinarith [(algebraMap ℚ B).injective hμ,
    mul_self_nonneg ((reducedTrace B μ)⁻¹ * (m + reducedNorm B μ))]

lemma reducedNorm_algebraMap_add_smul (h4 : finrank ℚ B = 4) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) (s t : ℚ) :
    reducedNorm B (algebraMap ℚ B s + t • μ) = s ^ 2 - m * t ^ 2 := by
  have hμ0 : reducedTrace B μ = 0 := reducedTrace_eq_zero_of_mul_self_eq h4 hm hμ
  have hN : reducedNorm B μ = -m := by
    rw [reducedNorm, hμ0, sq μ, hμ, reducedTrace_algebraMap _ h4]
    ring1
  rw [reducedNorm_add, reducedNorm_algebraMap _ h4, reducedNorm_smul, hN, reducedTrace_smul, hμ0,
    ← Algebra.smul_def, smul_smul, reducedTrace_smul, hμ0]
  ring1

variable {x} in
/-- **The centraliser of an element `μ` of a quaternion algebra whose square is a negative rational
number is `ℚ + ℚ μ`**: an element `x` commuting with `μ` is `trd(x) / 2 + (trd(x μ) / (2 μ²)) μ`. -/
lemma eq_algebraMap_add_smul_of_mul_comm (h4 : finrank ℚ B = 4) (hm : m < 0)
    (hμ : μ * μ = algebraMap ℚ B m) (h : x * μ = μ * x) :
    x = algebraMap ℚ B (reducedTrace B x / 2) + (reducedTrace B (x * μ) / (2 * m)) • μ := by
  have hμ0 : reducedTrace B μ = 0 := reducedTrace_eq_zero_of_mul_self_eq h4 hm hμ
  let δ : B := x - (algebraMap ℚ B (reducedTrace B x / 2) + (reducedTrace B (x * μ) / (2 * m)) • μ)
  have hδμ : δ * μ = x * μ -
      ((reducedTrace B x / 2) • μ + (reducedTrace B (x * μ) / (2 * m)) • algebraMap ℚ B m) := by
    rw [sub_mul, add_mul, smul_mul_assoc, hμ, ← Algebra.smul_def]
  have hμδ : μ * δ = δ * μ := by
    rw [hδμ, mul_sub, mul_add, mul_smul_comm, hμ, ← Algebra.commutes, ← Algebra.smul_def, h]
  have h1 : reducedTrace B δ = 0 := by
    rw [reducedTrace_sub, reducedTrace_add, reducedTrace_smul, reducedTrace_algebraMap _ h4, hμ0]
    ring1
  have h2 : reducedTrace B (δ * μ) = 0 := by
    rw [hδμ, reducedTrace_sub, reducedTrace_add, reducedTrace_smul, reducedTrace_smul,
      reducedTrace_algebraMap _ h4, hμ0, div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hm.ne)]
    ring1
  have h3 : δ * μ + μ * δ = 0 := by
    rw [mul_add_mul_eq δ μ h4, h1, h2, hμ0, zero_smul, zero_smul, mul_zero, sub_zero, map_zero,
      add_zero, add_zero]
  rw [hμδ, ← two_smul ℚ, smul_eq_zero_iff_right two_ne_zero] at h3
  have h4' : m • δ = 0 := by
    rw [Algebra.smul_def, Algebra.commutes, ← hμ, ← mul_assoc, h3, zero_mul]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_right hm.ne).mp h4')

end QuaternionAlgebra

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B}

/-- **A `ℚ`-linear endomorphism of a quaternion algebra that maps an order into itself has an
integral trace**: in a `ℤ`-basis of the order its matrix is integral. -/
lemma exists_trace_eq_intCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) (f : B →ₗ[ℚ] B)
    (hf : ∀ x ∈ O, f x ∈ O) : ∃ z : ℤ, LinearMap.trace ℚ B f = z := by
  rcases nonempty_basis_of_isQuaternionOrder h4 hO with ⟨x⟩
  rcases exists_basis_coe_eq hO x with ⟨c, hc⟩
  refine ⟨∑ i, x.repr ⟨f (x i), hf _ (x i).2⟩ i, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℚ c, Matrix.trace, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hc]
  exact repr_coe_eq_intCast hc ⟨f (x i), hf _ (x i).2⟩ i

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B]

/-- **The reduced norm is an integer on an order** of a quaternion algebra over `ℚ`. -/
lemma exists_reducedNorm_eq_intCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) {u : B}
    (hu : u ∈ O) : ∃ z : ℤ, reducedNorm B u = z := by
  rcases exists_reducedTrace_eq_intCast h4 hO hu with ⟨t, ht⟩
  have hmem : algebraMap ℚ B (reducedNorm B u) ∈ O := by
    rw [← sub_sub_cancel (reducedTrace B u • u) (algebraMap ℚ B (reducedNorm B u)),
      ← mul_self_eq_reducedTrace_smul_sub u h4, ht, Int.cast_smul_eq_zsmul]
    exact sub_mem (O.zsmul_mem hu t) (mul_mem hu hu)
  have hr : IsIntegral ℤ (reducedNorm B u) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ B).restrictScalars ℤ) (algebraMap ℚ B).injective).mp
      (IsIntegral.of_mem_of_fg O hO.fg _ hmem)
  rcases IsIntegrallyClosed.isIntegral_iff.mp hr with ⟨z, hz⟩
  exact ⟨z, hz.symm⟩

end Subalgebra
