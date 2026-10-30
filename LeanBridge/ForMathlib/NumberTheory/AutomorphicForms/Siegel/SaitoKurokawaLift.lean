import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLift
import Mathlib.NumberTheory.Divisors
import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character

/-!
# The Saito–Kurokawa lift

The Saito–Kurokawa lift (LMFDB `mf.siegel.lift.saito_kurokawa`) associates to a normalised Hecke
eigenform `f ∈ S_{2k}(SL(2, ℤ))`, `k` odd, a Siegel modular form `F` of degree `2` and weight
`k + 1` on `Sp(4, ℤ)`, with spin `L`-function `L(s, F) = L(s, f) ζ(s + 1/2) ζ(s - 1/2)`. It is the
composite of three maps (Eichler and Zagier, *The theory of Jacobi forms*, §6):

* the Shimura–Kohnen correspondence `S_{2k}(SL(2, ℤ)) ≅ S^+_{k+1/2}(Γ₀(4))`, from the Kohnen plus
  space of cusp forms of weight `k + 1/2`, which is Hecke-equivariant;
* the isomorphism `S^+_{k+1/2}(Γ₀(4)) ≅ J_{k+1,1}^cusp` of Eichler and Zagier (Theorem 5.4), which
  sends `∑ c(N) q^N` to the Jacobi form with Fourier coefficients `c(n, r) = c(4n - r²)`;
* the Maass lift `V : J_{k+1,1} → M_{k+1}(Sp(4, ℤ))`, `SiegelUpperHalfSpace.maassLift`.

The Maass lift is defined in `SiegelUpperHalfSpace.maassLift` by its Fourier coefficients, and the
Jacobi forms of index `1` stand for the Kohnen plus space through the second map, which only
reindexes the coefficients. The Shimura–Kohnen correspondence, as a map, is not available; the
Jacobi eigenform `φ` corresponding to `f` is characterised by Kohnen's explicit `D`-th Shimura
lifts: for every fundamental discriminant `D < 0` (that is, `(-1)^k D > 0`),
`𝒮_D(φ) = ∑_{n ≥ 1} (∑_{d ∣ n} (D/d) d^{k-1} c(|D| n²/d²)) q^n` is `c(|D|) f` (Kohnen,
*Modular forms of half-integral weight on `Γ₀(4)`*, Theorem 1, and Kohnen and Zagier, §1). By
these theorems and the multiplicity one of the plus space, the nonzero `φ` with this property are
the nonzero multiples of the Hecke eigenform of `J_{k+1,1}^cusp` corresponding to `f`: if `φ` is a
sum of eigenforms `φ_i` corresponding to distinct newforms `f_i`, then
`∑_i c_{φ_i}(|D|) f_i = c_φ(|D|) f` forces `c_{φ_i}(|D|) = 0`, hence `𝒮_D(φ_i) = 0` and, by
induction on `m`, `c_{φ_i}(|D| m²) = 0`, for every `D` and every `f_i ≠ f`; so `φ_i = 0`, as every
positive `N ≡ 0, 3 (mod 4)` is `|D| m²` for a fundamental `D < 0`. Hence the Saito–Kurokawa lift is
defined up to a nonzero scalar, as the Maass lifts `Vφ` of these `φ`
(`SiegelUpperHalfSpace.IsSaitoKurokawaLift`); for `k` even there is none, as `J_{k+1,1} = 0`. The
coefficient formula was checked numerically on `k = 9`, `f = Δ E_6 ∈ S_18` and
`φ = φ_{10,1} = η^{18} ϑ_1²`, for the `21` fundamental `D` from `-3` to `-59` and `n ≤ 6`, the even
divisors `d` being needed (`(D/2) ≠ 0` for odd `D`): for instance
`c(12) - 2⁸ c(3) = -272 - 256 = -528 = c(3) a_2(f)` (`D = -3`), `c(16) = 1056 = c(4) a_2(f)`
(`D = -4`) and `c(28) + 2⁸ c(7) = 12544 - 4096 = 8448 = c(7) a_2(f)` (`D = -7`).

The theorems of Kohnen and Eichler–Zagier, the modularity of the Maass lift
(`SiegelUpperHalfSpace.MaassLiftTheorem`) and the identity of spin `L`-functions, for which the spin
`L`-function of a Siegel eigenform (through the Satake isomorphism for `Sp(4)`) is missing, are not
proved here. The knowl's last statement, that the Saito–Kurokawa lifts span the same space as the
Maass lifts, is stated as `SiegelUpperHalfSpace.SaitoKurokawaSpanTheorem` for the Maass lifts of
Jacobi cusp forms, the cuspidal part of the Maass space: the lifts of the cusp forms `f` are cusp
forms, while the Maass lift of the Jacobi Eisenstein series `E_{k+1,1}` is a Siegel Eisenstein
series, which is not.

## Main definitions

* `ModularForm.jacobiDiscrCoeff`: the Fourier coefficient `c(N)` of a Jacobi form of index `1` at
  the discriminant `N = 4n - r²`.
* `ModularForm.jacobiShimuraCoeff`: the coefficients `∑_{d ∣ n} (D/d) d^{k-1} c(|D| n²/d²)` of
  Kohnen's `D`-th Shimura lift.
* `SiegelUpperHalfSpace.IsSaitoKurokawaLift` (LMFDB `mf.siegel.lift.saito_kurokawa`): `F` is a
  Saito–Kurokawa lift of `f`.
* `SiegelUpperHalfSpace.SaitoKurokawaSpanTheorem` (LMFDB `mf.siegel.lift.saito_kurokawa`): the
  Saito–Kurokawa lifts span the cuspidal Maass space, as a statement.

## Main results

* `ModularForm.jacobiCoeff_eq_jacobiDiscrCoeff`: for a Jacobi form of index `1`,
  `c(n, r) = c(4n - r²)`.
* `SiegelUpperHalfSpace.IsSaitoKurokawaLift.mem_maassLift_image`: a Saito–Kurokawa lift is a Maass
  lift of a Jacobi cusp form.
-/

open ModularForm TauCeti Multiquadratic UpperHalfPlane HeckeRing GL2

namespace ModularForm

variable {k : ℤ} (φ : ℍ × ℂ → ℂ) (N : ℕ)

/-- The **Fourier coefficient** `c(N)` of a Jacobi form `φ` of index `1` at the discriminant `N`:
its Fourier coefficient `c(n, r)` at `(n, r) = (N/4, 0)` if `N ≡ 0 (mod 4)` and `((N + 1)/4, 1)`
if `N ≡ 3 (mod 4)`, which is `c(n, r)` for every `(n, r)` with `4n - r² = N`
(`jacobiCoeff_eq_jacobiDiscrCoeff`), and `0` if `N ≡ 1, 2 (mod 4)`, when there is no such
`(n, r)`. These are the coefficients of the form `∑ c(N) q^N` of Kohnen's plus space of weight
`k - 1/2` that corresponds to `φ ∈ J_{k,1}` (Eichler and Zagier, Theorem 5.4). -/
noncomputable def jacobiDiscrCoeff : ℂ :=
  if N % 4 = 0 then jacobiCoeff φ ((N / 4 : ℕ), 0)
  else if N % 4 = 3 then jacobiCoeff φ (((N + 1) / 4 : ℕ), 1) else 0

/-- **The Fourier coefficients of a Jacobi form of index `1` only depend on the discriminant**:
`c(n, r) = c(4n - r²)`. -/
lemma jacobiCoeff_eq_jacobiDiscrCoeff (hφ : φ ∈ jacobiFormSpace k 1) {n r : ℤ}
    (h : 4 * n - r ^ 2 = N) : jacobiCoeff φ (n, r) = jacobiDiscrCoeff φ N := by
  rcases Int.even_or_odd' r with ⟨s, rfl | rfl⟩
  · have h₁ : (N : ℤ) = 4 * (n - s ^ 2) := by
      linear_combination -h
    rw [jacobiDiscrCoeff, ite_eq_left (by omega)]
    refine jacobiCoeff_eq_of_mem_jacobiFormSpace_one hφ ?_
    push_cast
    omega
  · have h₁ : (N : ℤ) = 4 * (n - s ^ 2 - s) - 1 := by
      linear_combination -h
    rw [jacobiDiscrCoeff, ite_eq_right (by omega), ite_eq_left (by omega)]
    refine jacobiCoeff_eq_of_mem_jacobiFormSpace_one hφ ?_
    push_cast
    omega

variable (k) in
/-- The **coefficient** `∑_{d ∣ n} (D/d) d^{k-1} c(|D| n²/d²)` of `q^n` in Kohnen's `D`-th Shimura
lift `𝒮_D(φ)` of a Jacobi form `φ` of index `1` and weight `k + 1`, for a fundamental discriminant
`D`, where `(D/·)` is the Kronecker symbol of `D`, the primitive quadratic character modulo `|D|`
(Tau Ceti's `fundamentalDiscriminantChar`), and `c(N)` are the coefficients of `φ` by discriminant
(`ModularForm.jacobiDiscrCoeff`). Through the isomorphism of `J_{k+1,1}` with Kohnen's plus space
of weight `k + 1/2`, `𝒮_D(φ) = ∑_{n ≥ 1} (∑_{d ∣ n} (D/d) d^{k-1} c(|D| n²/d²)) q^n` is Kohnen's
`D`-th Shimura lift, a modular form of weight `2k` on `SL(2, ℤ)` when `(-1)^k D > 0` (Kohnen,
Theorem 1, not proved here). -/
noncomputable def jacobiShimuraCoeff (D : ℤ) (hD : D.IsFundamentalDiscr) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (fundamentalDiscriminantChar D hD d : ℂ) * (d : ℂ) ^ (k - 1) *
    jacobiDiscrCoeff φ (D.natAbs * (n / d) ^ 2)

end ModularForm

namespace SiegelUpperHalfSpace

variable (k : ℤ) (f : Newform 1 (2 * k)) {F : SiegelUpperHalfSpace (Fin 2) → ℂ}

variable (F) in
/-- `F` is a **Saito–Kurokawa lift** (LMFDB `mf.siegel.lift.saito_kurokawa`) of a normalised Hecke
eigenform `f ∈ S_{2k}(SL(2, ℤ))`, a newform of level `1` (Tau Ceti's `HeckeRing.GL2.Newform`),
if `F = Vφ` is the Maass lift (`SiegelUpperHalfSpace.maassLift`) of a nonzero Jacobi cusp form
`φ ∈ J_{k+1,1}^cusp` whose `D`-th Shimura lifts are `𝒮_D(φ) = c(|D|) f` for every fundamental
discriminant `D < 0`, that is,
`∑_{d ∣ n} (D/d) d^{k-1} c(|D| n²/d²) = c(|D|) a_n(f)` for `n ≥ 1`
(`ModularForm.jacobiShimuraCoeff`), where `c(N)` are the coefficients of `φ` by discriminant. By the
theorems of Kohnen and of Eichler and Zagier (see the module docstring) these `φ` are the nonzero
multiples of the Jacobi eigenform corresponding to `f` through the Shimura–Kohnen correspondence, so
that the Saito–Kurokawa lifts of `f` are the nonzero multiples of one Siegel cusp form of weight
`k + 1` on `Sp(4, ℤ)` (by Maass's theorem `SiegelUpperHalfSpace.MaassLiftTheorem`), the lift being
defined up to a scalar. For `k` even there is none, since `J_{k+1,1} = 0`. -/
def IsSaitoKurokawaLift : Prop :=
  ∃ φ ∈ jacobiCuspFormSpace (k + 1) 1, φ ≠ 0 ∧ (∀ (D : ℤ) (hD : D.IsFundamentalDiscr), D < 0 →
    ∀ n : ℕ, 0 < n → jacobiShimuraCoeff k φ D hD n =
      jacobiDiscrCoeff φ D.natAbs * (qExpansion 1 f.toCuspForm).coeff n) ∧ F = maassLift (k + 1) φ

/-- **The Saito–Kurokawa lifts span the cuspidal Maass space** (LMFDB
`mf.siegel.lift.saito_kurokawa`), as a statement: for every `k`, the Saito–Kurokawa lifts of the
normalised Hecke eigenforms in `S_{2k}(SL(2, ℤ))` span the same space as the Maass lifts of the
Jacobi cusp forms of weight `k + 1` and index `1`, the cuspidal part of the Maass space. The knowl
says "all Maass lifts", which also include the Siegel Eisenstein series, the Maass lift of the
Jacobi Eisenstein series, not a cusp form. It rests on the Hecke theory of Jacobi forms and on the
theorems of Kohnen and of Eichler and Zagier, and is not proved here; the inclusion of the lifts in
the Maass space is `SiegelUpperHalfSpace.IsSaitoKurokawaLift.mem_maassLift_image`. -/
def SaitoKurokawaSpanTheorem : Prop :=
  ∀ k : ℤ, Submodule.span ℂ {F | ∃ f : Newform 1 (2 * k), IsSaitoKurokawaLift k f F} =
    Submodule.span ℂ (maassLift (k + 1) '' jacobiCuspFormSpace (k + 1) 1)

variable {k f} in
/-- **A Saito–Kurokawa lift is a Maass lift** of a Jacobi cusp form of index `1`. -/
lemma IsSaitoKurokawaLift.mem_maassLift_image (h : IsSaitoKurokawaLift k f F) :
    F ∈ maassLift (k + 1) '' jacobiCuspFormSpace (k + 1) 1 := by
  rcases h with ⟨φ, hφ, -, -, rfl⟩
  exact ⟨φ, hφ, rfl⟩

end SiegelUpperHalfSpace
