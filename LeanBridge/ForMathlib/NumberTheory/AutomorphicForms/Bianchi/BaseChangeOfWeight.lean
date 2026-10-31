import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.BaseChange
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ClassGroupHecke

/-!
# Base change of classical newforms of every weight to Bianchi modular forms

For a classical newform `f` of weight `w`, level `N` and nebentypus `χ`, and an imaginary quadratic
field `K`, the **base change** `F` of `f` to `K` (LMFDB `mf.bianchi.base_change`) is the Bianchi
form whose Hecke eigenvalues are determined from those of `f`: for every prime `p ∤ N` with `a_p`
the eigenvalue of `T_p` on `f`, and every prime `𝔭 ∣ p` of `K`, `a_𝔭 = a_p` if `p` splits or
ramifies in `K`, and `a_𝔭 = a_p² - 2χ(p)p^{w-1}` if `p` is inert, `p𝒪_K = 𝔭` (`α² + β²` for
`a_p = α + β`, `αβ = χ(p)p^{w-1}`; the knowl's `a_p² - 2p^{w-1}` is the case of a trivial
nebentypus, and `χ(p) = -1` for the character `χ_K` of `K/ℚ`, the other one for which the base
change has a trivial central character). The base change exists for every `K`, a theorem
(Langlands) not proved here, and is formalised as a relation between `F` and `f`. The central
character of the base change is `χ ∘ N_{K/ℚ}`; when it is ramified, the base change is not a form
for the groups `Γ₀(𝔑)_𝔟` on which the Bianchi Hecke operators are formalised, and no form here
satisfies the relation. The knowl's formula, with `αβ = p^{w-1}`, is that of a trivial nebentypus.

The base change of a newform of weight `w` has the coefficient system `Sym^{w-2} ⊗ conj(Sym^{w-2})`,
so it is a Bianchi form of weight `2w - 2` in the convention of LMFDB `mf.bianchi`
(`F : ℋ₃ → ℂ^{2w-1}`); its eigenvalues `a_𝔭` are those of the arithmetic Hecke operators
`N(𝔭)^{(w - 2) / 2} T_𝔭` (`bianchiHeckeIdealArith`, `bianchiHeckeTPrimeArith`). In weight `w = 2` it
is a form of weight `2`, and the relation is ZH1's `BianchiNewform.IsBaseChange`
(`BianchiNewform.isBaseChange_toBianchiNewformOfWeight_iff`).

The base change is usually a cuspidal newform, but not when `f` has complex multiplication by `K`:
it is then an Eisenstein series. To cover every `K` and both cases, the relation is defined for
the Hecke eigenforms (`IsBianchiHeckeEigenform`) of the space of tuples of Bianchi modular forms,
cuspidal or not, indexed by the class group of `K`, whose eigenvalues `a_𝔭` are defined at every
prime `𝔭 ∤ 𝔑`, principal or not; for class number `1` it is also defined for the newforms of every
weight (`BianchiNewformOfWeight`). The relation on eigenforms only involves the eigenvalues of the
arithmetic Hecke operators, not the Fourier–Bessel normalisation on which `BianchiNewformOfWeight`
rests in weight `k > 2` (facts not proved here). As the knowl of LMFDB `mf.base_change` states for
base changes from `ℚ`, the eigenvalues of a base change are invariant under the automorphisms of
`K`: they agree at any two primes above the same `p ∤ N`.

## Main definitions

* `HeckeRing.GL2.Newform.quadraticBaseChangeEigenvalue` (LMFDB `mf.bianchi.base_change`): the
  eigenvalue `a_p` or `a_p² - 2χ(p)p^{w-1}` of the base change at a prime `𝔭 ∣ p`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.IsBaseChange` (LMFDB `mf.bianchi.base_change`): a
  Hecke eigenform over `K` of any class number is the base change of `f`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.IsBaseChange` (LMFDB `mf.bianchi.base_change`): a
  Bianchi newform of any weight is the base change of `f`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.IsBaseChangeFromRat` and
  `HyperbolicThreeSpace.BianchiNewformOfWeight.IsBaseChangeFromRat` (LMFDB `mf.base_change`,
  `mf.bianchi.base_change`): a Hecke eigenform or a newform is a base change, from `ℚ`, the only
  proper subfield of `K`.

## Main results

* `HeckeRing.GL2.Newform.quadraticBaseChangeEigenvalue_eq`: the formula only depends on `p`, not
  on the prime `𝔭 ∣ p`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.IsBaseChange.eigenvalue_eq_eigenvalue` and
  `HyperbolicThreeSpace.BianchiNewformOfWeight.IsBaseChange.eigenvalue_eq_eigenvalue`: the
  eigenvalues of a base change agree at the primes above the same `p ∤ N`, so that
  `a_{τ(𝔭)} = a_𝔭` for every automorphism `τ` of `K` (LMFDB `mf.base_change`).
* `HyperbolicThreeSpace.BianchiNewform.isBaseChange_toBianchiNewformOfWeight_iff`: in weight `2`,
  the relation is the one of `BianchiNewform.IsBaseChange`.
-/

open HeckeRing GL2 NumberField UpperHalfPlane

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

lemma Ideal.span_natCast_eq_of_mem {p : ℕ} {𝔭 : Ideal (𝓞 K)} (h : (span {(p : 𝓞 K)}).IsPrime)
    (h₀ : span {(p : 𝓞 K)} ≠ ⊥) (h𝔭 : 𝔭.IsPrime) (hp : (p : 𝓞 K) ∈ 𝔭) : span {(p : 𝓞 K)} = 𝔭 :=
  (h.isMaximal h₀).eq_of_le h𝔭.ne_top <| (span_singleton_le_iff_mem _).mpr hp

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {w : ℤ} (f : Newform N w) (p : ℕ) {𝔭 𝔭' : Ideal (𝓞 K)}

variable (𝔭) in
/-- The **eigenvalue of the base change** of the classical newform `f` of weight `w` and nebentypus
`χ` to a quadratic field `K` (LMFDB `mf.bianchi.base_change`) at a prime `𝔭 ∣ p`, `p ∤ N`:
`a_p² - 2χ(p)p^{w-1}` if `p` is inert in `K`, `p𝒪_K = 𝔭`, and `a_p` if `p` splits or ramifies,
where `a_p` is the coefficient of `qᵖ` of `f`, its eigenvalue for `T_p`. -/
noncomputable def quadraticBaseChangeEigenvalue : ℂ :=
  if Ideal.span {(p : 𝓞 K)} = 𝔭 then
    (qExpansion 1 f.toCuspForm).coeff p ^ 2 - 2 * f.dirichletLift p * (p : ℂ) ^ (w - 1)
  else (qExpansion 1 f.toCuspForm).coeff p

/-- **The eigenvalue of the base change only depends on `p`**: at two nonzero primes `𝔭, 𝔭'` of
`K` above `p`, the formula gives the same value, as `p` is inert at one of them exactly when it is
inert at the other, and then `𝔭 = 𝔭' = p𝒪_K`. -/
lemma quadraticBaseChangeEigenvalue_eq (h𝔭 : 𝔭.IsPrime) (h𝔭' : 𝔭'.IsPrime) (h𝔭₀ : 𝔭 ≠ ⊥)
    (h𝔭₀' : 𝔭' ≠ ⊥) (hp : (p : 𝓞 K) ∈ 𝔭) (hp' : (p : 𝓞 K) ∈ 𝔭') :
    f.quadraticBaseChangeEigenvalue p 𝔭 = f.quadraticBaseChangeEigenvalue p 𝔭' := by
  by_cases h : Ideal.span {(p : 𝓞 K)} = 𝔭
  · subst h
    rw [Ideal.span_natCast_eq_of_mem h𝔭 h𝔭₀ h𝔭' hp']
  · by_cases h' : Ideal.span {(p : 𝓞 K)} = 𝔭'
    · subst h'
      rw [Ideal.span_natCast_eq_of_mem h𝔭' h𝔭₀' h𝔭 hp]
    · rw [quadraticBaseChangeEigenvalue, ite_eq_right h, quadraticBaseChangeEigenvalue,
        ite_eq_right h']

end HeckeRing.GL2.Newform

namespace HyperbolicThreeSpace

variable {σ : K →+* ℂ} {k : ℕ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] {N : ℕ} [NeZero N] {w : ℤ}
  (f : Newform N w)

namespace IsBianchiHeckeEigenform

variable {𝔟 : NarrowClassGroup K → (FractionalIdeal (𝓞 K)⁰ K)ˣ} {Φ : bianchiClassGroupForms σ k 𝔑 𝔟}
  (hΦ : IsBianchiHeckeEigenform Φ)

/-- A Hecke eigenform `Φ` of weight `k` and level `𝔑` over an imaginary quadratic field `K` of any
class number, cuspidal or not, is the **base change** (LMFDB `mf.bianchi.base_change`) of the
classical newform `f` of weight `w`, level `N` and nebentypus `χ`: `k = 2w - 2`, and for every
prime `p ∤ N` and every prime `𝔭 ∣ p` of `K` with `𝔭 ∤ 𝔑`, the eigenvalue `a_𝔭` of the arithmetic
Hecke operator `T_𝔭` on `Φ` is `a_p² - 2χ(p)p^{w-1}` if `p` is inert in `K` (`p𝒪_K = 𝔭`) and `a_p`
if `p` splits or ramifies (`quadraticBaseChangeEigenvalue`). -/
def IsBaseChange : Prop :=
  (k : ℤ) = 2 * w - 2 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N →
    ∀ 𝔭 : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭},
      (p : 𝓞 K) ∈ (𝔭.1 : Ideal (𝓞 K)) →
        hΦ.eigenvalue 𝔭 = f.quadraticBaseChangeEigenvalue p (𝔭.1 : Ideal (𝓞 K))

/-- A Hecke eigenform `Φ` over an imaginary quadratic field `K` of any class number **is a base
change** (LMFDB `mf.base_change`, `mf.bianchi.base_change`): it is the base change of a modular form
on `GL(2)` over a proper subfield of `K`, which can only be `ℚ`, that is of a classical newform (the
eigenvalues of a classical eigenform at the good primes are those of a newform). -/
def IsBaseChangeFromRat : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (w : ℤ) (f : Newform N w), hΦ.IsBaseChange f

variable {hΦ f}

/-- **The eigenvalues of a base change agree at the primes above the same `p`** (LMFDB
`mf.base_change`): if `Φ` is the base change of `f`, then `a_𝔭 = a_𝔭'` for any two primes
`𝔭, 𝔭' ∤ 𝔑` above the same prime `p ∤ N`. In particular `a_{τ(𝔭)} = a_𝔭` for every automorphism
`τ` of `K` with `τ(𝔭) ∤ 𝔑`. -/
lemma IsBaseChange.eigenvalue_eq_eigenvalue (h : hΦ.IsBaseChange f) {p : ℕ} (hp : p.Prime)
    (hpN : ¬p ∣ N) (𝔭 𝔭' : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭})
    (h𝔭 : (p : 𝓞 K) ∈ (𝔭.1 : Ideal (𝓞 K))) (h𝔭' : (p : 𝓞 K) ∈ (𝔭'.1 : Ideal (𝓞 K))) :
    hΦ.eigenvalue 𝔭 = hΦ.eigenvalue 𝔭' := by
  rw [h.2 p hp hpN 𝔭 h𝔭, h.2 p hp hpN 𝔭' h𝔭']
  exact f.quadraticBaseChangeEigenvalue_eq p 𝔭.2.1 𝔭'.2.1 (nonZeroDivisors.coe_ne_zero 𝔭.1)
    (nonZeroDivisors.coe_ne_zero 𝔭'.1) h𝔭 h𝔭'

end IsBianchiHeckeEigenform

namespace BianchiNewformOfWeight

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] (F : BianchiNewformOfWeight σ k 𝔑)

/-- A Bianchi newform `F` of weight `k` and level `𝔑` over `K` (of class number `1`) is the **base
change** (LMFDB `mf.bianchi.base_change`) of the classical newform `f` of weight `w`, level `N` and
nebentypus `χ`: `k = 2w - 2`, and for every prime `p ∤ N` and every prime `𝔭 ∣ p` of `𝒪_K`, the
eigenvalue `a_𝔭` of the arithmetic Hecke operator `T_𝔭` on `F` is `a_p² - 2χ(p)p^{w-1}` if `p` is
inert in `K` (`p𝒪_K = 𝔭`) and `a_p` if `p` splits or ramifies (`quadraticBaseChangeEigenvalue`).
In weight `2` this is `BianchiNewform.IsBaseChange`
(`BianchiNewform.isBaseChange_toBianchiNewformOfWeight_iff`). -/
def IsBaseChange : Prop :=
  (k : ℤ) = 2 * w - 2 ∧ ∀ p : ℕ, p.Prime → ¬p ∣ N → ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (p : 𝓞 K) ∈ 𝔭.1 → F.eigenvalue 𝔭 = f.quadraticBaseChangeEigenvalue p 𝔭.1

/-- A Bianchi newform `F` of weight `k` **is a base change** (LMFDB `mf.base_change`,
`mf.bianchi.base_change`): it is the base change of a modular form on `GL(2)` over a proper subfield
of `K`, which can only be `ℚ`, that is of a classical newform. -/
def IsBaseChangeFromRat : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (w : ℤ) (f : Newform N w), F.IsBaseChange f

variable {F f}

/-- **The eigenvalues of a base change agree at the primes above the same `p`** (LMFDB
`mf.base_change`): if `F` is the base change of `f`, then `a_𝔭 = a_𝔭'` for any two primes `𝔭, 𝔭'`
above the same prime `p ∤ N`, so that `a_{τ(𝔭)} = a_𝔭` for every automorphism `τ` of `K`. -/
lemma IsBaseChange.eigenvalue_eq_eigenvalue (h : F.IsBaseChange f) {p : ℕ} (hp : p.Prime)
    (hpN : ¬p ∣ N) (𝔭 𝔭' : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h𝔭 : (p : 𝓞 K) ∈ 𝔭.1)
    (h𝔭' : (p : 𝓞 K) ∈ 𝔭'.1) : F.eigenvalue 𝔭 = F.eigenvalue 𝔭' := by
  rw [h.2 p hp hpN 𝔭 h𝔭, h.2 p hp hpN 𝔭' h𝔭']
  exact f.quadraticBaseChangeEigenvalue_eq p 𝔭.2.1 𝔭'.2.1 𝔭.2.2 𝔭'.2.2 h𝔭 h𝔭'

end BianchiNewformOfWeight

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] (F : BianchiNewform σ 𝔑)
  (g : Newform N 2)

/-- **In weight `2`, the base change relation is that of `BianchiNewform.IsBaseChange`**: a
Bianchi newform `F` of weight `2` is the base change of a classical newform `g` of weight `2` in the
sense of `BianchiNewformOfWeight.IsBaseChange` exactly when it is in the sense of ZH1. -/
lemma BianchiNewform.isBaseChange_toBianchiNewformOfWeight_iff :
    F.toBianchiNewformOfWeight.IsBaseChange g ↔ F.IsBaseChange g := by
  simp [BianchiNewformOfWeight.IsBaseChange, BianchiNewform.IsBaseChange,
    BianchiNewform.toBianchiNewformOfWeight, Newform.quadraticBaseChangeEigenvalue]

end HyperbolicThreeSpace
