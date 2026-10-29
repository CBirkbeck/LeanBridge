import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Jacobi forms

A Jacobi form of weight `k` and index `N` (of full level) is a holomorphic function
`f : ℍ × ℂ → ℂ` with
`f((aτ + b) / (cτ + d), z / (cτ + d)) = (cτ + d)^k e^{2πiNcz² / (cτ + d)} f(τ, z)` for every
`(a, b; c, d) ∈ SL(2, ℤ)`, which has a Fourier expansion `f(τ, z) = ∑ c(n, r) e^{2πi(nτ + rz)}`
over the integers `n, r` with `4nN - r² ≥ 0`. It is a cusp form if the expansion runs over the
`n, r` with `4nN - r² > 0`.

The usual definition (Eichler and Zagier) also asks for the elliptic transformation law
`f(τ, z + λτ + μ) = e^{-2πiN(λ²τ + 2λz)} f(τ, z)` for `λ, μ ∈ ℤ`, which the LMFDB omits. It
follows from the other conditions: the Fourier expansion makes `f` periodic of period `1` in `z`,
and conjugating this periodicity by `S = (0, -1; 1, 0)` gives the law for `λ = 1`, `μ = 0`. So
the LMFDB definition is the usual one.

## Main definitions

* `ModularForm.jacobiFourierExp`: the exponential `e^{2πi(nτ + rz)}`.
* `ModularForm.HasJacobiFourierExpansion`: `c` is a family of Fourier coefficients of `f`.
* `ModularForm.jacobiFourierSupported`: the functions with a Fourier expansion supported on a given
  set of pairs `(n, r)`.
* `ModularForm.jacobiFactor`: the factor `(cτ + d)^k e^{2πiNcz² / (cτ + d)}`.
* `ModularForm.jacobiFormSpace` (LMFDB `mf.jacobi`): the space `J_{k,N}` of Jacobi forms.
* `ModularForm.jacobiCuspFormSpace` (LMFDB `mf.jacobi`): the space `J_{k,N}^cusp` of Jacobi cusp
  forms.

## Main results

* `ModularForm.apply_add_intCast_of_mem_jacobiFormSpace`: Jacobi forms are periodic of period `1`
  in `z`.
* `ModularForm.apply_add_mul_add_of_mem_jacobiFormSpace`: the elliptic transformation law
  `f(τ, z + λτ + μ) = e^{-2πiN(λ²τ + 2λz)} f(τ, z)`.
-/

open Complex Real

open scoped MatrixGroups Manifold

open UpperHalfPlane hiding I

namespace ModularForm

variable {k : ℤ} {N : ℕ} {f g : ℍ × ℂ → ℂ} {c d : ℤ × ℤ → ℂ} (p : ℤ × ℤ) (x : ℍ × ℂ) (τ : ℍ) (z : ℂ)
    (a b : ℤ)

/-- The exponential `e^{2πi(nτ + rz)}` of the Fourier expansion of a Jacobi form, for `p = (n, r)`
and `x = (τ, z)`. -/
noncomputable def jacobiFourierExp : ℂ :=
  cexp (2 * π * I * (p.1 * x.1 + p.2 * x.2))

lemma jacobiFourierExp_add_intCast :
    jacobiFourierExp p (τ, z + b) = jacobiFourierExp p (τ, z) := by
  have h : 2 * π * I * (p.1 * τ + p.2 * (z + b)) =
      2 * π * I * (p.1 * τ + p.2 * z) + (p.2 * b : ℤ) * (2 * π * I) := by
    push_cast
    ring1
  rw [jacobiFourierExp, jacobiFourierExp, h, Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

variable (f c) in
/-- The family `c : ℤ × ℤ → ℂ` is **a family of Fourier coefficients** of `f : ℍ × ℂ → ℂ`:
`f(τ, z) = ∑_{n, r ∈ ℤ} c(n, r) e^{2πi(nτ + rz)}` for every `(τ, z) ∈ ℍ × ℂ`, the sum converging
unconditionally. -/
def HasJacobiFourierExpansion : Prop :=
  ∀ x, HasSum (fun p ↦ c p * jacobiFourierExp p x) (f x)

lemma HasJacobiFourierExpansion.add (hf : HasJacobiFourierExpansion f c)
    (hg : HasJacobiFourierExpansion g d) : HasJacobiFourierExpansion (f + g) (c + d) :=
  fun x ↦ by simpa [add_mul] using (hf x).add (hg x)

lemma HasJacobiFourierExpansion.const_smul (hf : HasJacobiFourierExpansion f c) (u : ℂ) :
    HasJacobiFourierExpansion (u • f) (u • c) :=
  fun x ↦ by simpa [mul_assoc] using (hf x).mul_left u

lemma hasJacobiFourierExpansion_zero : HasJacobiFourierExpansion 0 0 :=
  fun x ↦ by simp

lemma HasJacobiFourierExpansion.apply_add_intCast (hf : HasJacobiFourierExpansion f c) :
    f (τ, z + b) = f (τ, z) :=
  (hf (τ, z + b)).unique <| by simpa only [jacobiFourierExp_add_intCast] using hf (τ, z)

variable (S : Set (ℤ × ℤ)) in
/-- The functions `f : ℍ × ℂ → ℂ` with a Fourier expansion `f(τ, z) = ∑ c(n, r) e^{2πi(nτ + rz)}`
**supported on** a set `S` of pairs `(n, r)` of integers: `c(n, r) = 0` for `(n, r) ∉ S`. -/
def jacobiFourierSupported : Submodule ℂ (ℍ × ℂ → ℂ) where
  carrier := {f | ∃ c, HasJacobiFourierExpansion f c ∧ ∀ p, c p ≠ 0 → p ∈ S}
  add_mem' {f g} hf hg := by
    rcases hf with ⟨c, hc, hcS⟩
    rcases hg with ⟨d, hd, hdS⟩
    refine ⟨c + d, hc.add hd, fun p hp ↦ ?_⟩
    by_cases hcp : c p = 0
    · exact hdS p fun hdp ↦ hp <| by simp [hcp, hdp]
    · exact hcS p hcp
  zero_mem' := ⟨0, hasJacobiFourierExpansion_zero, fun _ hp ↦ absurd rfl hp⟩
  smul_mem' u f hf := by
    rcases hf with ⟨c, hc, hcS⟩
    exact ⟨u • c, hc.const_smul u, fun p hp ↦ hcS p <| right_ne_zero_of_mul hp⟩

variable (k N) in
/-- The factor `(cτ + d)^k e^{2πiNcz² / (cτ + d)}` of the transformation law of Jacobi forms of
weight `k` and index `N`, for `γ = (a, b; c, d) ∈ SL(2, ℤ)` and `x = (τ, z)`. -/
noncomputable def jacobiFactor (γ : SL(2, ℤ)) : ℂ :=
  denom γ x.1 ^ k * cexp (2 * π * I * N * γ 1 0 * x.2 ^ 2 / denom γ x.1)

variable (k N) in
/-- The space `J_{k,N}` of **Jacobi forms** (LMFDB `mf.jacobi`) of weight `k` and index `N`, of full
level: the holomorphic `f : ℍ × ℂ → ℂ` with
`f((aτ + b) / (cτ + d), z / (cτ + d)) = (cτ + d)^k e^{2πiNcz² / (cτ + d)} f(τ, z)` for every
`(a, b; c, d) ∈ SL(2, ℤ)` and `(τ, z) ∈ ℍ × ℂ`, with a Fourier expansion
`f(τ, z) = ∑ c(n, r) e^{2πi(nτ + rz)}` over the integers `n, r` with `4nN - r² ≥ 0` and `n ≥ 0`.
Holomorphy is on the complex manifold `ℍ × ℂ`.

The knowl writes `m` for the index `N` in the transformation law. For `N ≥ 1` the condition
`n ≥ 0` follows from `4nN ≥ r²`; for `N = 0` the knowl's condition `r = 0` alone would allow
`n < 0`, and `n ≥ 0` is imposed, as by Eichler and Zagier. The elliptic transformation law, which
the knowl omits, follows (`apply_add_mul_add_of_mem_jacobiFormSpace`). -/
def jacobiFormSpace : Submodule ℂ (ℍ × ℂ → ℂ) where
  carrier := {f | MDiff f ∧
    (∀ (γ : SL(2, ℤ)) x, f (γ • x.1, x.2 / denom γ x.1) = jacobiFactor k N x γ * f x) ∧
      f ∈ jacobiFourierSupported {p | 0 ≤ p.1 ∧ p.2 ^ 2 ≤ 4 * p.1 * N}}
  add_mem' hf hg := ⟨hf.1.add hg.1, fun γ x ↦ by
    rw [Pi.add_apply, Pi.add_apply, hf.2.1, hg.2.1, mul_add], add_mem hf.2.2 hg.2.2⟩
  zero_mem' := ⟨mdifferentiable_const, fun γ x ↦ by simp, zero_mem _⟩
  smul_mem' u f hf := ⟨hf.1.const_smul u, fun γ x ↦ by
    rw [Pi.smul_apply, Pi.smul_apply, hf.2.1, smul_eq_mul, smul_eq_mul, mul_left_comm],
    Submodule.smul_mem _ u hf.2.2⟩

variable (k N) in
/-- The space `J_{k,N}^cusp` of **Jacobi cusp forms** (LMFDB `mf.jacobi`) of weight `k` and index
`N`: the Jacobi forms whose Fourier expansion runs over the integers `n, r` with
`4nN - r² > 0`. -/
def jacobiCuspFormSpace : Submodule ℂ (ℍ × ℂ → ℂ) :=
  jacobiFormSpace k N ⊓ jacobiFourierSupported {p | p.2 ^ 2 < 4 * p.1 * N}

lemma jacobiCuspFormSpace_le_jacobiFormSpace : jacobiCuspFormSpace k N ≤ jacobiFormSpace k N :=
  inf_le_left

/-- **Jacobi forms are periodic of period `1` in `z`**, by their Fourier expansion. -/
lemma apply_add_intCast_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    f (τ, z + b) = f (τ, z) := by
  rcases hf.2.2 with ⟨c, hc, -⟩
  exact hc.apply_add_intCast τ z b

lemma apply_add_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    f (τ, z + τ) = cexp (-2 * π * I * N * (τ + 2 * z)) * f (τ, z) := by
  have h1 : ((ModularGroup.S 1 0 : ℤ) : ℂ) = 1 := by
    simp
  have hS (w : ℂ) : f (ModularGroup.S • τ, w / τ) =
      (τ : ℂ) ^ k * cexp (2 * π * I * N * w ^ 2 / τ) * f (τ, w) := by
    simpa only [jacobiFactor, ModularGroup.denom_S, h1, mul_one] using hf.2.1 ModularGroup.S (τ, w)
  have h : (z + τ) / τ = z / τ + (1 : ℤ) := by
    rw [add_div, div_self τ.ne_zero, Int.cast_one]
  have he : cexp (2 * π * I * N * z ^ 2 / τ) =
      cexp (2 * π * I * N * (z + τ) ^ 2 / τ) * cexp (-2 * π * I * N * (τ + 2 * z)) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp [τ.ne_zero]
    ring1
  refine mul_left_cancel₀ (mul_ne_zero (zpow_ne_zero k τ.ne_zero)
    (Complex.exp_ne_zero (2 * π * I * N * (z + τ) ^ 2 / τ))) ?_
  rw [← hS (z + τ), h, apply_add_intCast_of_mem_jacobiFormSpace _ _ _ hf, hS z, he]
  ring1

lemma apply_add_mul_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    f (τ, z + a * τ) = cexp (-2 * π * I * N * (a ^ 2 * τ + 2 * a * z)) * f (τ, z) := by
  induction a using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
    have h : f (τ, z + (n : ℤ) * τ + τ) =
        cexp (-2 * π * I * N * (τ + 2 * (z + (n : ℤ) * τ))) * f (τ, z + (n : ℤ) * τ) :=
      apply_add_of_mem_jacobiFormSpace τ (z + (n : ℤ) * τ) hf
    have h' : z + ((n + 1 : ℤ) : ℂ) * τ = z + (n : ℤ) * τ + τ := by
      push_cast
      ring1
    rw [ih] at h
    rw [h', h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring1
  | pred n ih =>
    have h : f (τ, z + (-n - 1 : ℤ) * τ + τ) =
        cexp (-2 * π * I * N * (τ + 2 * (z + (-n - 1 : ℤ) * τ))) * f (τ, z + (-n - 1 : ℤ) * τ) :=
      apply_add_of_mem_jacobiFormSpace τ (z + (-n - 1 : ℤ) * τ) hf
    have h' : z + (-n - 1 : ℤ) * τ + τ = z + (-n : ℤ) * τ := by
      push_cast
      ring1
    rw [h', ih] at h
    refine mul_left_cancel₀ (Complex.exp_ne_zero
      (-2 * π * I * N * (τ + 2 * (z + (-n - 1 : ℤ) * τ)))) ?_
    rw [← h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring1

/-- **The elliptic transformation law** `f(τ, z + λτ + μ) = e^{-2πiN(λ²τ + 2λz)} f(τ, z)` of a
Jacobi form of index `N`, for all `λ, μ ∈ ℤ`: it follows from the transformation law under
`SL(2, ℤ)` and the periodicity in `z`, so that the LMFDB definition, which omits it, agrees with
that of Eichler and Zagier. -/
lemma apply_add_mul_add_of_mem_jacobiFormSpace (hf : f ∈ jacobiFormSpace k N) :
    f (τ, z + a * τ + b) = cexp (-2 * π * I * N * (a ^ 2 * τ + 2 * a * z)) * f (τ, z) := by
  rw [apply_add_intCast_of_mem_jacobiFormSpace _ _ _ hf,
    apply_add_mul_of_mem_jacobiFormSpace τ z a hf]

end ModularForm
