import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.BaseChange
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.BaseChangeOfWeight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeFourier

/-!
# Base change of classical newforms to Hilbert modular forms

Let `f` be a classical newform of weight `w`, level `N` and nebentypus `χ`, with `a_p = α_p + β_p`
and `α_p β_p = χ(p) p^{w-1}` at the primes `p ∤ N`, so that its good Euler factors are
`L_p(f, T) = (1 - α_p T)(1 - β_p T)`. A modular form `g` on `GL(2)` over a number field `K` is a
base change of `f` (LMFDB `mf.base_change`) if `L_𝔮(g, T) = L_p^{(r)}(f, T)` at almost all primes
`𝔮 ∣ p` of `K`, `r` being the residue degree of `𝔮`; comparing the coefficients of `T`
(`HeckeRing.GL2.Newform.rootPowers_eulerFactor`), its Hecke eigenvalue is `a_𝔮 = α_p^r + β_p^r`,
the power sum `s_r` given by `s₀ = 2`, `s₁ = a_p` and `s_{r+2} = a_p s_{r+1} - χ(p) p^{w-1} s_r`
(`HeckeRing.GL2.Newform.frobeniusPowerSum`). For an imaginary quadratic `K` this is the formula of
LMFDB `mf.bianchi.base_change`
(`HeckeRing.GL2.Newform.quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum`).

For a totally real field `K`, the base change of `f` is a Hilbert modular form of parallel weight
`w`. The base change relation is formalised for the Hilbert Hecke eigenforms
(`HilbertModularForm.IsHeckeIdealEigenform`), by their eigenvalues in the LMFDB's normalisation
(`HilbertModularForm.heckeIdealEigenvalueNormalised`), which are defined at every prime `𝔮 ∤ 𝔑`,
principal or not: they must be the power sums. The constant terms of the Euler factors involve the
central character of `g`, `χ ∘ N_{K/ℚ}` for a base change, which the tuples of Hilbert modular
forms here do not determine. That the base change exists is a theorem for solvable extensions
(Langlands, Arthur–Clozel), not proved here. A Hilbert modular form over a real quadratic field is
a base change if it is the base change of a classical newform, `ℚ` being the only proper subfield;
over fields of higher degree, base changes from intermediate fields are not formalised.

## Main definitions

* `HeckeRing.GL2.Newform.frobeniusPowerSum` (LMFDB `mf.base_change`): the power sums
  `α_p^r + β_p^r`.
* `HilbertModularForm.IsHeckeIdealEigenform.IsBaseChange` (LMFDB `mf.base_change`): a Hilbert Hecke
  eigenform over a totally real field is the base change of a classical newform.
* `HilbertModularForm.IsHeckeIdealEigenform.IsBaseChangeFromRat` (LMFDB `mf.base_change`): it is a
  base change from `ℚ`.

## Main results

* `HeckeRing.GL2.Newform.frobeniusPowerSum_eq_add_pow`: `frobeniusPowerSum` is `α_p^r + β_p^r`.
* `HeckeRing.GL2.Newform.rootPowers_eulerFactor`: the polynomial `L_p^{(r)}(f, T)`
  (`Polynomial.rootPowers`) is `1 - s_r T + (χ(p) p^{w-1})^r T²`, so that a base change has the
  eigenvalues `s_r`.
* `HeckeRing.GL2.Newform.quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum`: the eigenvalues of
  LMFDB `mf.bianchi.base_change` are the power sums for the residue degree `2` at the inert primes
  and `1` otherwise.
* `HilbertModularForm.IsHeckeIdealEigenform.IsBaseChange.heckeIdealEigenvalueNormalised_eq`: the
  eigenvalues of a base change agree at the primes above the same `p` with the same residue degree,
  in particular at `𝔮` and `τ(𝔮)` for every automorphism `τ` of `K` (LMFDB `mf.base_change`).
-/

open HeckeRing GL2 NumberField Polynomial UpperHalfPlane

open scoped nonZeroDivisors

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {w : ℤ} (f : Newform N w) (p : ℕ)

/-- The **power sums** `α_p^r + β_p^r` (LMFDB `mf.base_change`) of the roots `α_p, β_p` of
`T² - a_p T + χ(p) p^{w-1}` for a classical newform `f` of weight `w` and nebentypus `χ`, where
`a_p` is the coefficient of `qᵖ`: `s₀ = 2`, `s₁ = a_p` and
`s_{r+2} = a_p s_{r+1} - χ(p) p^{w-1} s_r` (`frobeniusPowerSum_eq_add_pow`). At a prime `𝔮` of
residue degree `r` above `p ∤ N`, the eigenvalue of a base change of `f` is `s_r`. -/
noncomputable def frobeniusPowerSum : ℕ → ℂ
  | 0 => 2
  | 1 => (qExpansion 1 f.toCuspForm).coeff p
  | r + 2 => (qExpansion 1 f.toCuspForm).coeff p * frobeniusPowerSum (r + 1) -
      f.dirichletLift p * (p : ℂ) ^ (w - 1) * frobeniusPowerSum r

variable {f p} {α β : ℂ}

/-- **`frobeniusPowerSum` is the power sum `α_p^r + β_p^r`** of the roots of
`T² - a_p T + χ(p) p^{w-1}`. -/
lemma frobeniusPowerSum_eq_add_pow (hs : α + β = (qExpansion 1 f.toCuspForm).coeff p)
    (hp : α * β = f.dirichletLift p * (p : ℂ) ^ (w - 1)) :
    ∀ r, f.frobeniusPowerSum p r = α ^ r + β ^ r
  | 0 => by
    norm_num [frobeniusPowerSum]
  | 1 => by
    rw [frobeniusPowerSum, ← hs, pow_one, pow_one]
  | r + 2 => by
    rw [frobeniusPowerSum, frobeniusPowerSum_eq_add_pow hs hp (r + 1),
      frobeniusPowerSum_eq_add_pow hs hp r, ← hs, ← hp]
    ring1

variable (f p) {K : Type*} [Field K] (𝔭 : Ideal (𝓞 K))

/-- **The eigenvalues of LMFDB `mf.bianchi.base_change` are power sums**: `a_p² - 2χ(p)p^{w-1}` at
an inert prime `𝔭 = p𝒪_K`, of residue degree `2`, and `a_p` otherwise, of residue degree `1`. -/
lemma quadraticBaseChangeEigenvalue_eq_frobeniusPowerSum : f.quadraticBaseChangeEigenvalue p 𝔭 =
    f.frobeniusPowerSum p (if Ideal.span {(p : 𝓞 K)} = 𝔭 then 2 else 1) := by
  rw [quadraticBaseChangeEigenvalue]
  split_ifs
  · rw [frobeniusPowerSum, frobeniusPowerSum, frobeniusPowerSum]
    ring1
  · rw [frobeniusPowerSum]

/-- **`h^{(r)}` of a good Euler factor is given by the power sums** (LMFDB `mf.base_change`): for
`p ∤ N`, so that `χ(p) p^{w-1} ≠ 0`, the polynomial `L_p^{(r)}(f, T)` (`Polynomial.rootPowers`) of
`L_p(f, T) = 1 - a_p T + χ(p) p^{w-1} T²` is `1 - s_r T + (χ(p) p^{w-1})^r T²`, where
`s_r = α_p^r + β_p^r` (`frobeniusPowerSum`). So a modular form `g` with
`L_𝔮(g, T) = L_p^{(r)}(f, T)` has the eigenvalue `a_𝔮 = s_r`. -/
lemma rootPowers_eulerFactor (hp : f.dirichletLift p * (p : ℂ) ^ (w - 1) ≠ 0) (r : ℕ) :
    (1 - C ((qExpansion 1 f.toCuspForm).coeff p) * X +
      C (f.dirichletLift p * (p : ℂ) ^ (w - 1)) * X ^ 2).rootPowers r =
        1 - C (f.frobeniusPowerSum p r) * X +
          C ((f.dirichletLift p * (p : ℂ) ^ (w - 1)) ^ r) * X ^ 2 := by
  have hh : (1 - C ((qExpansion 1 f.toCuspForm).coeff p) * X +
      C (f.dirichletLift p * (p : ℂ) ^ (w - 1)) * X ^ 2 : ℂ[X]) =
        C (f.dirichletLift p * (p : ℂ) ^ (w - 1)) * X ^ 2 +
          C (-(qExpansion 1 f.toCuspForm).coeff p) * X + C 1 := by
    simp only [map_neg, map_one]
    ring1
  have hdeg : (C (f.dirichletLift p * (p : ℂ) ^ (w - 1)) * X ^ 2 +
      C (-(qExpansion 1 f.toCuspForm).coeff p) * X + C 1 : ℂ[X]).natDegree = 2 :=
    natDegree_quadratic hp
  rcases Multiset.card_eq_two.mp (IsAlgClosed.card_roots_eq_natDegree.trans hdeg) with
    ⟨ρ₁, ρ₂, hρ⟩
  have h₀ : 1 = f.dirichletLift p * (p : ℂ) ^ (w - 1) * ρ₁ * ρ₂ :=
    eq_mul_mul_of_roots_quadratic_eq_pair hρ
  have h₁ : -(qExpansion 1 f.toCuspForm).coeff p =
      -(f.dirichletLift p * (p : ℂ) ^ (w - 1)) * (ρ₁ + ρ₂) :=
    eq_neg_mul_add_of_roots_quadratic_eq_pair hρ
  have hρ₀ : f.dirichletLift p * (p : ℂ) ^ (w - 1) * ρ₁ * ρ₂ ≠ 0 := h₀ ▸ one_ne_zero
  have hρ₁ : ρ₁ ≠ 0 := right_ne_zero_of_mul <| left_ne_zero_of_mul hρ₀
  have hρ₂ : ρ₂ ≠ 0 := right_ne_zero_of_mul hρ₀
  have hs : ρ₁⁻¹ + ρ₂⁻¹ = (qExpansion 1 f.toCuspForm).coeff p := by
    field_simp
    linear_combination (ρ₁ + ρ₂) * h₀ + ρ₁ * ρ₂ * h₁
  have hpr : ρ₁⁻¹ * ρ₂⁻¹ = f.dirichletLift p * (p : ℂ) ^ (w - 1) := by
    field_simp
    linear_combination h₀
  have hc : (C (f.dirichletLift p * (p : ℂ) ^ (w - 1)) * X ^ 2 +
      C (-(qExpansion 1 f.toCuspForm).coeff p) * X + C 1 : ℂ[X]).coeff 0 = 1 := by
    simp
  rw [hh, rootPowers, hc, hρ, frobeniusPowerSum_eq_add_pow hs hpr r, ← hpr]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
    Multiset.map_singleton, Multiset.prod_singleton, map_one, map_add, mul_pow, map_mul, inv_pow]
  ring1

end HeckeRing.GL2.Newform

namespace HilbertModularForm.IsHeckeIdealEigenform

variable {F : Type*} [Field F] [NumberField F] {k : {v : InfinitePlace F // v.IsReal} → ℤ}
  {𝔑 : Ideal (𝓞 F)} [NeZero 𝔑] {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} {ψ : HilbertModularForm 𝔑 k 𝔟 h𝔟}
  (hψ : ψ.IsHeckeIdealEigenform) {N : ℕ} [NeZero N] {w : ℤ} (f : Newform N w)

/-- A Hilbert modular form `ψ` of level `𝔑` over a totally real field `F`, a Hecke eigenform for
the `T_𝔞` with `𝔞` coprime to `𝔑`, is the **base change** (LMFDB `mf.base_change`) of the classical
newform `f` of weight `w`, level `N` and nebentypus `χ`: `ψ` has parallel weight `w`, and for every
prime `p ∤ N` and every prime `𝔮 ∣ p` of `F` with `𝔮 ∤ 𝔑`, principal or not, its Hecke eigenvalue
`a_𝔮` in the LMFDB's normalisation is `α_p^r + β_p^r` (`frobeniusPowerSum`), where `r` is the
residue degree of `𝔮`: the coefficient of `T` in `L_𝔮(ψ, T) = L_p^{(r)}(f, T)`. The knowl asks for
this at all but finitely many `𝔮`; for a Hecke eigenform that is equivalent, by strong multiplicity
one (a theorem not proved here), to the condition at every such `𝔮` imposed here. -/
def IsBaseChange : Prop :=
  (∀ v, k v = w) ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N → ∀ 𝔮 : (Ideal (𝓞 F))⁰, (𝔮 : Ideal (𝓞 F)).IsPrime →
    ∀ h𝔮 : (𝔮 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤, (p : 𝓞 F) ∈ (𝔮 : Ideal (𝓞 F)) →
      heckeIdealEigenvalueNormalised w 𝔮 hψ h𝔮 =
        f.frobeniusPowerSum p ((𝔮 : Ideal (𝓞 F)).inertiaDeg ℤ)

/-- A Hilbert Hecke eigenform **is a base change from `ℚ`** (LMFDB `mf.base_change`): it is the
base change of some classical newform. Over a real quadratic field, whose only proper subfield is
`ℚ`, this is the LMFDB's notion of being a base change. -/
def IsBaseChangeFromRat : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (w : ℤ) (f : Newform N w), hψ.IsBaseChange f

variable {hψ f}

/-- **The eigenvalues of a base change agree at the primes above the same `p` with the same residue
degree** (LMFDB `mf.base_change`): in particular `a_{τ(𝔮)} = a_𝔮` for every automorphism `τ` of
`F`, which preserves residue degrees. -/
lemma IsBaseChange.heckeIdealEigenvalueNormalised_eq (h : hψ.IsBaseChange f) {p : ℕ} (hp : p.Prime)
    (hpN : ¬p ∣ N) {𝔮 𝔮' : (Ideal (𝓞 F))⁰} (h𝔮 : (𝔮 : Ideal (𝓞 F)).IsPrime)
    (h𝔮' : (𝔮' : Ideal (𝓞 F)).IsPrime) (h𝔑 : (𝔮 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤)
    (h𝔑' : (𝔮' : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) (hp𝔮 : (p : 𝓞 F) ∈ (𝔮 : Ideal (𝓞 F)))
    (hp𝔮' : (p : 𝓞 F) ∈ (𝔮' : Ideal (𝓞 F)))
    (hr : (𝔮 : Ideal (𝓞 F)).inertiaDeg ℤ = (𝔮' : Ideal (𝓞 F)).inertiaDeg ℤ) :
    heckeIdealEigenvalueNormalised w 𝔮 hψ h𝔑 = heckeIdealEigenvalueNormalised w 𝔮' hψ h𝔑' := by
  rw [h.2 p hp hpN 𝔮 h𝔮 h𝔑 hp𝔮, h.2 p hp hpN 𝔮' h𝔮' h𝔑' hp𝔮', hr]

end HilbertModularForm.IsHeckeIdealEigenform
