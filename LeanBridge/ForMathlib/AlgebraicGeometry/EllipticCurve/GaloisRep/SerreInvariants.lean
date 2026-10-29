import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import TauCeti.NumberTheory.ModularForms.Newforms.Fields

/-!
# Serre invariants of the mod-`ℓ` Galois representations of an elliptic curve over `ℚ`

Let `E` be an elliptic curve over `ℚ` of conductor `N` and `ℓ` a prime. A newform `f` of level `M`
and weight `k` (Tau Ceti's `HeckeRing.GL2.Newform M k`, in `S_k^new(Γ₁(M))`) has a mod-`ℓ`
representation isomorphic to `ρ̄_{E,ℓ}` when, in the words of the knowl, `a_p(E)` and `a_p(f)`
reduce to the same element of the residue field of a prime `𝔩` above `ℓ` of the coefficient field
`ℚ_f`. This congruence is how the matching is formalised here, at the primes `p ∤ ℓNM`, where both
representations are unramified with traces of Frobenius `a_p(E)` and `a_p(f)`: the Galois
representations of newforms of weight other than one are not available. For `ℓ = 2` equal traces
need not give isomorphic semisimplifications, and the knowl's criterion is used as it stands. Here
`a_p(f)` is the `p`-th Fourier coefficient of `f` and `a_p(E)` the `p`-th coefficient of Mathlib's
L-function of `E`, which is `p + 1 - #E(𝔽_p)` at the primes of good reduction, and `N` is the norm
of Tau Ceti's algorithmic conductor.

The Serre conductor `M` is the least level of such a newform of weight at least `2` and the Serre
weight `k` the least weight `k ≥ 2` of such a newform of level `M`, as in Serre's definition, where
the weight is at least `2`. Newforms of weight one matter only for `ℓ = 2`, where they would give
the odd weight `1`, against the knowl's `2 ∣ k`: the `2`-division field of `y² = x³ - x - 1` is the
Hilbert class field of `ℚ(√-23)`, so the weight-one newform `η(τ) η(23τ)` of level `23` is congruent
to it modulo `2`, while its Serre invariants are `(2, 23)`. The knowl asserts that the weight is the
only one at level `M`; this is not used, and is false in general: for `ℓ ≥ 5`, multiplying by the
Eisenstein series `E_{ℓ - 1} ≡ 1 mod ℓ` and lifting (Deligne–Serre) gives congruent newforms of
level `M` in the weights `k + j (ℓ - 1)`. Its claim that the invariants are `(2, N)` for every prime
`ℓ > 7` of good reduction is false too: if `p ∥ N` and `ℓ` divides the valuation at `p` of the
minimal discriminant, then `ρ̄_{E,ℓ}` is unramified at `p` and, when it is irreducible, `M ∣ N / p`
by Ribet's level lowering. The facts that `2 ∣ k`, `M ∣ N` and that only finitely many primes are
exceptional are not proved, and neither is the existence of a congruent newform (the newform of
`E`, by modularity), without which both invariants are `0`.

## Main definitions

* `WeierstrassCurve.IsCongruentNewform` (LMFDB `ec.q.serre_invariants`): `f` is congruent to `E`
  modulo a prime above `ℓ`.
* `WeierstrassCurve.serreConductor` (LMFDB `ec.q.serre_invariants`): the Serre conductor.
* `WeierstrassCurve.serreWeight` (LMFDB `ec.q.serre_invariants`): the Serre weight.
* `WeierstrassCurve.serreInvariants` (LMFDB `ec.q.serre_invariants`): the Serre invariants `(k, M)`.
* `WeierstrassCurve.IsSerreExceptional` (LMFDB `ec.q.serre_invariants`): exceptional primes.

## Main results

* `WeierstrassCurve.exists_isCongruentNewform_serreWeight`: if some newform is congruent to `E`
  modulo a prime above `ℓ`, so is a newform of level the Serre conductor and weight the Serre
  weight.
-/

open HeckeRing GL2 TauCeti UpperHalfPlane

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) {M : ℕ} [NeZero M]

/-- A newform `f` of level `M` and weight `k` is **congruent** to an elliptic curve `E` over `ℚ`
modulo a prime above `ℓ` (LMFDB `ec.q.serre_invariants`) if some prime ideal `𝔩` of the ring of
integers of the coefficient field `ℚ_f` contains `ℓ` and `a_p(f) ≡ a_p(E) mod 𝔩` at every prime
`p ∤ ℓNM`, `N` the conductor of `E`. By the knowl, this means that the mod-`ℓ` representation of `f`
is isomorphic to that of `E`, `ρ̄_{E,ℓ}`. Here `a_p(f)` is the `p`-th Fourier coefficient of `f`,
an algebraic integer, and `a_p(E)` is the `p`-th coefficient of the L-function of `E`. -/
def IsCongruentNewform {k : ℤ} (f : Newform M k) : Prop :=
  ∃ 𝔩 : Ideal (integralClosure ℤ (CoefficientField f)), 𝔩.IsPrime ∧
    (ℓ : integralClosure ℤ (CoefficientField f)) ∈ 𝔩 ∧ ∀ p : ℕ, p.Prime →
      ¬p ∣ ℓ * M * Ideal.absNorm (algorithmicConductor ℤ E) → ∃ x ∈ 𝔩,
        ((x : CoefficientField f) : ℂ) = (qExpansion 1 f.toCuspForm).coeff p - E.LFunction p

/-- The **Serre conductor** `M` (LMFDB `ec.q.serre_invariants`) of the mod-`ℓ` representation
`ρ̄_{E,ℓ}` of an elliptic curve `E` over `ℚ`: the least level of a newform of weight at least `2`
congruent to `E` modulo a prime above `ℓ`, and `0` if there is none. -/
noncomputable def serreConductor : ℕ :=
  sInf {M | ∃ (_ : NeZero M) (k : ℕ), 2 ≤ k ∧ ∃ f : Newform M k, E.IsCongruentNewform ℓ f}

/-- The **Serre weight** `k` (LMFDB `ec.q.serre_invariants`) of the mod-`ℓ` representation
`ρ̄_{E,ℓ}` of an elliptic curve `E` over `ℚ`: the least weight `k ≥ 2` of a newform of level the
Serre conductor congruent to `E` modulo a prime above `ℓ`, and `0` if there is none. As in Serre's
definition the weight is at least `2`; newforms of weight one, which can matter only for `ℓ = 2`,
are left out. -/
noncomputable def serreWeight : ℕ :=
  sInf {k | 2 ≤ k ∧ ∃ (_ : NeZero (E.serreConductor ℓ)) (f : Newform (E.serreConductor ℓ) k),
    E.IsCongruentNewform ℓ f}

/-- The **Serre invariants** `(k, M)` (LMFDB `ec.q.serre_invariants`) of the mod-`ℓ` representation
`ρ̄_{E,ℓ}` of an elliptic curve `E` over `ℚ`: its Serre weight `k` and its Serre conductor `M`. -/
noncomputable def serreInvariants : ℕ × ℕ :=
  (E.serreWeight ℓ, E.serreConductor ℓ)

/-- A prime `ℓ` is **exceptional** (LMFDB `ec.q.serre_invariants`) for an elliptic curve `E` over
`ℚ` of conductor `N` if the Serre invariants of `ρ̄_{E,ℓ}` are not `(2, N)`. -/
def IsSerreExceptional : Prop :=
  E.serreInvariants ℓ ≠ (2, Ideal.absNorm (algorithmicConductor ℤ E))

variable {E ℓ} {k : ℕ} {f : Newform M k}

lemma serreConductor_le (hk : 2 ≤ k) (hf : E.IsCongruentNewform ℓ f) : E.serreConductor ℓ ≤ M :=
  Nat.sInf_le ⟨inferInstance, k, hk, f, hf⟩

lemma serreWeight_le [NeZero (E.serreConductor ℓ)] {g : Newform (E.serreConductor ℓ) k} (hk : 2 ≤ k)
    (hg : E.IsCongruentNewform ℓ g) : E.serreWeight ℓ ≤ k :=
  Nat.sInf_le ⟨hk, inferInstance, g, hg⟩

/-- **The Serre invariants are attained**: if some newform of level `M` and weight at least `2` is
congruent to `E` modulo a prime above `ℓ`, then the Serre conductor is positive and some newform of
level the Serre conductor and weight the Serre weight is congruent to `E` modulo a prime above
`ℓ`. -/
lemma exists_isCongruentNewform_serreWeight (hk : 2 ≤ k) (hf : E.IsCongruentNewform ℓ f) :
    ∃ (_ : NeZero (E.serreConductor ℓ)) (g : Newform (E.serreConductor ℓ) (E.serreWeight ℓ)),
    E.IsCongruentNewform ℓ g := by
  rcases Nat.sInf_mem (s := {M | ∃ (_ : NeZero M) (k : ℕ), 2 ≤ k ∧ ∃ f : Newform M k,
    E.IsCongruentNewform ℓ f}) ⟨M, inferInstance, k, hk, f, hf⟩ with ⟨h, k', hk', g, hg⟩
  exact (Nat.sInf_mem (s := {k | 2 ≤ k ∧ ∃ (_ : NeZero (E.serreConductor ℓ))
    (f : Newform (E.serreConductor ℓ) k), E.IsCongruentNewform ℓ f}) ⟨k', hk', h, g, hg⟩).2

end WeierstrassCurve
