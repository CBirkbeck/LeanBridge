import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.Basic
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierUniqueness

/-!
# Fourier coefficients of Jacobi forms

The Fourier expansion `f(τ, z) = ∑ c(n, r) e^{2πi(nτ + rz)}` of a function on `ℍ × ℂ` is unique:
on `τ = t + i`, `z = u` with `t, u` real it is an absolutely convergent Fourier series on the torus
`(ℝ / ℤ)²` with coefficients `c(n, r) e^{-2πn}`. So the Fourier coefficients `c(n, r)` of a Jacobi
form are well defined, and the elliptic transformation law translates into
`c(n + λr + Nλ², r + 2Nλ) = c(n, r)` for a form of index `N`. In index `1` this says that `c(n, r)`
only depends on the discriminant `4n - r²` (Eichler and Zagier, Theorem 2.2).

## Main definitions

* `ModularForm.jacobiCoeff`: the Fourier coefficients `c(n, r)` of a function on `ℍ × ℂ`.

## Main results

* `ModularForm.eq_zero_of_hasSum_jacobiFourierExp`: a Fourier series on `ℍ × ℂ` that vanishes
  everywhere has zero coefficients.
* `ModularForm.HasJacobiFourierExpansion.unique`: Fourier expansions on `ℍ × ℂ` are unique.
* `ModularForm.jacobiCoeff_add_of_mem_jacobiFormSpace`: `c(n + λr + Nλ², r + 2Nλ) = c(n, r)` for a
  Jacobi form of index `N`.
* `ModularForm.jacobiCoeff_eq_of_mem_jacobiFormSpace_one`: in index `1`, `c(n, r)` only depends on
  `4n - r²`.
-/

open Complex Real UnitAddTorus

open UpperHalfPlane hiding I

namespace ModularForm

variable {k : ℤ} {N : ℕ} {f : ℍ × ℂ → ℂ} {c d : ℤ × ℤ → ℂ} (v : Fin 2 → ℝ)

/-- The point `(v₀ + i, v₁)` of `ℍ × ℂ`, for real `v₀, v₁`. -/
private noncomputable def torusPoint : ℍ × ℂ :=
  (mk (v 0 + I) (by simp), (v 1 : ℂ))

private lemma jacobiFourierExp_torusPoint (p : Fin 2 → ℤ) :
    jacobiFourierExp (p 0, p 1) (torusPoint v) =
      cexp (-2 * π * p 0) * mFourier p fun i ↦ (v i : UnitAddCircle) := by
  simp only [jacobiFourierExp, torusPoint, mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, Fin.prod_univ_two, ← Complex.exp_add]
  congr 1
  linear_combination (2 * π * p 0 : ℂ) * I_sq

/-- **Uniqueness of Fourier expansions on `ℍ × ℂ`**: if `∑ c(n, r) e^{2πi(nτ + rz)} = 0` for every
`(τ, z) ∈ ℍ × ℂ`, the sum converging unconditionally, then `c = 0`. -/
lemma eq_zero_of_hasSum_jacobiFourierExp (hc : ∀ x, HasSum (fun p ↦ c p * jacobiFourierExp p x) 0) :
    c = 0 := by
  have hd (v : Fin 2 → ℝ) : HasSum (fun p : Fin 2 → ℤ ↦ c (p 0, p 1) * cexp (-2 * π * p 0) *
      mFourier p fun i ↦ (v i : UnitAddCircle)) 0 :=
    ((finTwoArrowEquiv ℤ).hasSum_iff.mpr (hc (torusPoint v))).congr_fun fun p ↦ by
      rw [mul_assoc, ← jacobiFourierExp_torusPoint]
      rfl
  have hs : Summable fun p : Fin 2 → ℤ ↦ c (p 0, p 1) * cexp (-2 * π * p 0) :=
    (hd 0).summable.congr fun p ↦ by
      simp [mFourier]
  have h0 : (fun p : Fin 2 → ℤ ↦ c (p 0, p 1) * cexp (-2 * π * p 0)) = 0 :=
    eq_zero_of_hasSum_mFourier hs fun x ↦ by
      choose t ht using fun i ↦ QuotientAddGroup.mk_surjective (x i)
      exact (funext ht : (fun i ↦ (t i : UnitAddCircle)) = x) ▸ hd t
  funext p
  simpa using congrFun h0 ![p.1, p.2]

/-- **Fourier expansions on `ℍ × ℂ` are unique**: two families of Fourier coefficients of the same
function are equal. -/
lemma HasJacobiFourierExpansion.unique (hc : HasJacobiFourierExpansion f c)
    (hd : HasJacobiFourierExpansion f d) : c = d :=
  sub_eq_zero.mp <| eq_zero_of_hasSum_jacobiFourierExp fun x ↦ by
    simpa [sub_mul] using (hc x).sub (hd x)

open scoped Classical in
variable (f) in
/-- The **Fourier coefficients** `c(n, r)` of `f : ℍ × ℂ → ℂ`: those of its Fourier expansion
`f(τ, z) = ∑ c(n, r) e^{2πi(nτ + rz)}`, which is unique (`HasJacobiFourierExpansion.unique`), and
the junk value `0` if `f` has none. For a Jacobi form these are its Fourier coefficients in the
sense of the LMFDB (`mf.jacobi`). -/
noncomputable def jacobiCoeff : ℤ × ℤ → ℂ :=
  if h : ∃ c, HasJacobiFourierExpansion f c then h.choose else 0

lemma HasJacobiFourierExpansion.jacobiCoeff_eq (hc : HasJacobiFourierExpansion f c) :
    jacobiCoeff f = c :=
  have h : ∃ c, HasJacobiFourierExpansion f c := ⟨c, hc⟩
  (dite_eq_left h).trans <| h.choose_spec.unique hc

lemma jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported {S : Set (ℤ × ℤ)}
    (hf : f ∈ jacobiFourierSupported S) {p : ℤ × ℤ} (hp : p ∉ S) : jacobiCoeff f p = 0 := by
  rcases hf with ⟨c, hc, hcS⟩
  rw [hc.jacobiCoeff_eq]
  exact not_not.mp (hp ∘ hcS p)

lemma hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    HasJacobiFourierExpansion f (jacobiCoeff f) := by
  rcases hf.2.2 with ⟨c, hc, -⟩
  rwa [hc.jacobiCoeff_eq]

variable (a n r : ℤ)

/-- The shear `(n, r) ↦ (n + λr, r)` of `ℤ²`. -/
private def shear : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + a * p.2, p.2)
  invFun p := (p.1 - a * p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

variable (N) in
/-- The translation `(n, r) ↦ (n - Nλ², r - 2Nλ)` of `ℤ²`. -/
private def shift : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 - N * a ^ 2, p.2 - 2 * N * a)
  invFun p := (p.1 + N * a ^ 2, p.2 + 2 * N * a)
  left_inv p := by simp
  right_inv p := by simp

/-- **The elliptic transformation law on Fourier coefficients**: the Fourier coefficients of a
Jacobi form of index `N` satisfy `c(n + λr + Nλ², r + 2Nλ) = c(n, r)` for every `λ ∈ ℤ`. -/
lemma jacobiCoeff_add_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    jacobiCoeff f (n + a * r + N * a ^ 2, r + 2 * N * a) = jacobiCoeff f (n, r) := by
  have hc : HasJacobiFourierExpansion f (jacobiCoeff f) :=
    hasJacobiFourierExpansion_jacobiCoeff_of_mem_jacobiFormSpace hf
  have h₁ : HasJacobiFourierExpansion (fun x ↦ f (x.1, x.2 + a * x.1))
      (jacobiCoeff f ∘ (shear a).symm) := fun x ↦
    (shear a).hasSum_iff.mp <| (hc (x.1, x.2 + a * x.1)).congr_fun fun p ↦ by
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      congr 1
      simp only [jacobiFourierExp, shear, Equiv.coe_fn_mk]
      congr 1
      push_cast
      ring1
  have h₂ : HasJacobiFourierExpansion (fun x ↦ f (x.1, x.2 + a * x.1))
      (jacobiCoeff f ∘ (shift N a).symm) := fun x ↦ by
    beta_reduce
    rw [apply_add_mul_of_mem_jacobiFormSpace x.1 x.2 a hf]
    refine (shift N a).hasSum_iff.mp <| ((hc x).mul_left _).congr_fun fun p ↦ ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [mul_left_comm]
    congr 1
    simp only [jacobiFourierExp, shift, Equiv.coe_fn_mk, ← Complex.exp_add]
    congr 1
    push_cast
    ring1
  have h : (jacobiCoeff f ∘ (shear a).symm) (n + a * r, r) =
      (jacobiCoeff f ∘ (shift N a).symm) (n + a * r, r) :=
    congrFun (h₁.unique h₂) _
  simp only [Function.comp_apply, shear, Equiv.coe_fn_symm_mk, add_sub_cancel_right] at h
  exact h.symm

variable {n r} in
/-- **In index `1` the Fourier coefficients only depend on the discriminant**: for a Jacobi form of
index `1`, `c(n, r) = c(n', r')` whenever `4n - r² = 4n' - r'²` (Eichler and Zagier, Theorem
2.2). -/
lemma jacobiCoeff_eq_of_mem_jacobiFormSpace_one (hf : f ∈ jacobiFormSpace k 1) {n' r' : ℤ}
    (h : 4 * n - r ^ 2 = 4 * n' - r' ^ 2) : jacobiCoeff f (n, r) = jacobiCoeff f (n', r') := by
  have h2 : r' ^ 2 = r ^ 2 + 2 * (2 * (n' - n)) := by
    linear_combination h
  have he : Even (r' - r) := by
    rw [Int.even_sub, ← Int.even_pow' two_ne_zero, ← Int.even_pow' (m := r) two_ne_zero, h2,
      Int.even_add]
    simp
  rcases he with ⟨l, hl⟩
  have hn : n' = n + l * r + 1 * l ^ 2 :=
    mul_left_cancel₀ four_ne_zero <| by linear_combination -h + (r' + r + 2 * l) * hl
  have hr : r' = r + 2 * 1 * l := by
    linear_combination hl
  rw [hn, hr, ← Nat.cast_one, jacobiCoeff_add_of_mem_jacobiFormSpace l n r hf]

end ModularForm
