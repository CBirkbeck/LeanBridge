import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Newform
import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# Base change of classical newforms to Bianchi newforms

For a classical newform `f` of level `N` and an imaginary quadratic field `K`, the **base change**
`F` of `f` to `K` (LMFDB `mf.bianchi.base_change`) is the Bianchi form whose Hecke eigenvalues are
determined from those of `f`: for every prime `p ∤ N` with `a_p` the eigenvalue of `T_p` on `f`,
and every prime `𝔭 ∣ p` of `K`, `a_𝔭 = a_p` if `p` splits or ramifies in `K`, and
`a_𝔭 = a_p² - 2p^{k-1}` if `p` is inert, `p𝒪_K = 𝔭`, where `k` is the weight of `f`: with
`a_p = α + β` and `αβ = p^{k-1}`, `a_𝔭 = α² + β²`. It is cuspidal, a Bianchi newform, unless `f`
has CM by `K`; that the base change exists is a theorem (Langlands), not proved here, and base
change is formalised as a relation between a Bianchi newform and a classical newform.

The classical newforms are Tau Ceti's `HeckeRing.GL2.Newform`, of level `Γ₁(N)` with a nebentypus
`χ`, and `a_p` is the coefficient of `qᵖ`, the eigenvalue of `T_p` for a newform. The knowl's
formula `αβ = p^{k-1}` is that of a trivial nebentypus; in general `αβ = χ(p) p^{k-1}`, and the
inert eigenvalue is `a_p² - 2χ(p)p^{k-1}`, which is used here. This matters for the nebentypus `χ_K`
of `K/ℚ`, the other one for which the base change has trivial character, where it is
`a_p² + 2p^{k-1}` at the inert primes. Bianchi newforms are formalised in weight `2`
(`BianchiNewform`), the base change of the classical newforms of weight `2`, so `k = 2`.

## Main definitions

* `HyperbolicThreeSpace.BianchiNewform.IsBaseChange` (LMFDB `mf.bianchi.base_change`): `F` is the
  base change of `f` to `K`.
-/

open HeckeRing GL2 NumberField UpperHalfPlane

namespace HyperbolicThreeSpace.BianchiNewform

variable {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]
  {σ : K →+* ℂ} {𝔑 : Ideal (𝓞 K)} [NeZero 𝔑] (F : BianchiNewform σ 𝔑) {N : ℕ} [NeZero N]

/-- A Bianchi newform `F` over `K` is the **base change** (LMFDB `mf.bianchi.base_change`) of the
classical newform `f` of weight `2` and level `N`, with coefficients `aₙ` and nebentypus `χ`: for
every prime `p ∤ N` and every prime `𝔭 ∣ p` of `𝒪_K`, the eigenvalue `a_𝔭` of `T_𝔭` on `F` is
`a_p² - 2χ(p)p` if `p` is inert in `K` (`p𝒪_K = 𝔭`) and `a_p` if `p` splits or ramifies. For a
trivial nebentypus these are the knowl's `a_p² - 2p^{k-1}` and `a_p` in weight `k = 2`. -/
def IsBaseChange (f : Newform N 2) : Prop :=
  ∀ p : ℕ, p.Prime → ¬p ∣ N → ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (p : 𝓞 K) ∈ 𝔭.1 →
    F.eigenvalue 𝔭 = if Ideal.span {(p : 𝓞 K)} = 𝔭.1 then
      (qExpansion 1 f.toCuspForm).coeff p ^ 2 - 2 * f.dirichletLift p * p
    else (qExpansion 1 f.toCuspForm).coeff p

end HyperbolicThreeSpace.BianchiNewform
