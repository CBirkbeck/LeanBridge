import LeanBridge.ForMathlib.NumberTheory.Artin.Conductor

/-!
# The conductor of a mod-`ℓ` Galois representation

Let `K/ℚ` be a finite Galois extension, `ρ` a representation of `Gal(K/ℚ)` on a finite-dimensional
vector space `V` over a field `k`, typically `𝔽_ℓ`, and `Q` a prime of `𝓞 K` above a prime number
`p`. As for Artin representations (`Representation.artinConductor`, where `k = ℂ`), the exponent
of the conductor at `p` is `f(ρ, p) = ∑_{i ≥ 0} (g_i / g_0) (dim V - dim V^{G_i})`, where `G_i` is
the `i`-th ramification group of `Q` (Tau Ceti's `Ideal.ramificationGroup`), the ramification group
in the lower numbering of the completion `K_Q/ℚ_p`, and `g_i = |G_i|`; it does not depend on `Q`.
The conductor of a mod-`ℓ` representation is the product `∏_{p ≠ ℓ} p^f(ρ, p)` over the primes
`p ≠ ℓ`.

That the exponents are integers, so that the conductor is a positive integer, is not proved here:
the exponents are rational numbers and the conductor is a real number.

## Main definitions

* `Representation.finrankInvariantsField`: the dimension of the vectors fixed by a subgroup.
* `Representation.conductorExponentAt`: the exponent `f(ρ, Q)` at a prime `Q` of `𝓞 K`.
* `Representation.conductorExponent` (LMFDB `modlgal.conductor`): the exponent `f(ρ, p)` at a
  prime number `p`.
* `Representation.modEllConductor` (LMFDB `modlgal.conductor`): the conductor `∏_{p ≠ ℓ} p^f(ρ, p)`.

## Main results

* `Representation.conductorExponentAt_smul` and `Representation.conductorExponent_eq`: the exponent
  does not depend on the prime above `p`.
* `Representation.conductorExponentAt_eq_zero` and `Representation.conductorExponent_eq_zero`: the
  exponent vanishes at primes unramified in `K`.
-/

open Module NumberField
open scoped Pointwise

namespace Representation

variable {k K V : Type*} [Field k] [Field K] [NumberField K] [AddCommGroup V] [Module k V]
  (ρ : Representation k Gal(K/ℚ) V) (Q : Ideal (𝓞 K)) (p : Nat.Primes) (ℓ : ℕ)

/-- The dimension of the subspace `V^H` of vectors fixed by a subgroup `H`, over any field `k`. -/
noncomputable def finrankInvariantsField (H : Subgroup Gal(K/ℚ)) : ℕ :=
  finrank k (invariants (ρ.comp H.subtype))

lemma finrankInvariantsField_bot : ρ.finrankInvariantsField ⊥ = finrank k V := by
  have h : invariants (ρ.comp (⊥ : Subgroup Gal(K/ℚ)).subtype) = ⊤ := eq_top_iff.mpr fun v _ g ↦ by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_bot.mp g.2, map_one, End.one_apply]
  rw [finrankInvariantsField, h, finrank_top]

lemma finrankInvariantsField_map_conj (H : Subgroup Gal(K/ℚ)) (g : Gal(K/ℚ)) :
    ρ.finrankInvariantsField (H.map (MulAut.conj g)) = ρ.finrankInvariantsField H := by
  let e : V ≃ₗ[k] V := LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (LinearMap.ext fun x ↦ ρ.self_inv_apply g x) (LinearMap.ext fun x ↦ ρ.inv_self_apply g x)
  have hρ (h : Gal(K/ℚ)) (v : V) : ρ (g * h * g⁻¹) v = ρ g (ρ h (ρ g⁻¹ v)) := by
    rw [map_mul, map_mul, End.mul_apply, End.mul_apply]
  have h : invariants (ρ.comp (H.map (MulAut.conj g)).subtype) = (invariants (ρ.comp H.subtype)).map
      (e : V →ₗ[k] V) := by
    ext v
    rw [Submodule.mem_map_equiv, mem_invariants, mem_invariants]
    refine ⟨fun hv h ↦ ?_, fun hv x ↦ ?_⟩
    · have hk : ρ g (ρ h (ρ g⁻¹ v)) = v := by
        rw [← hρ]
        exact hv ⟨g * h * g⁻¹, Subgroup.mem_map_of_mem _ h.2⟩
      have hk' : ρ g⁻¹ (ρ g (ρ h (ρ g⁻¹ v))) = ρ g⁻¹ v := congrArg (ρ g⁻¹) hk
      rwa [ρ.inv_self_apply] at hk'
    · rcases x with ⟨_, h, hh, rfl⟩
      have hv' : ρ h (ρ g⁻¹ v) = ρ g⁻¹ v := hv ⟨h, hh⟩
      simp [hv']
  rw [finrankInvariantsField, finrankInvariantsField, h, LinearEquiv.finrank_map_eq]

/-- The **exponent of the conductor** of a representation `ρ` of `Gal(K/ℚ)` over a field `k` at a
prime `Q` of `𝓞 K`: `f(ρ, Q) = ∑_{i ≥ 0} (g_i / g_0) (dim V - dim V^{G_i})`, where `G_i` is the
`i`-th ramification group of `Q` and `g_i` its order. -/
noncomputable def conductorExponentAt : ℚ :=
  ∑ᶠ i : ℕ, (Nat.card (Q.ramificationGroup Gal(K/ℚ) i) : ℚ) /
    Nat.card (Q.ramificationGroup Gal(K/ℚ) 0) *
      (finrank k V - ρ.finrankInvariantsField (Q.ramificationGroup Gal(K/ℚ) i))

/-- **The exponent of the conductor does not change when the prime is moved by the Galois group**:
the ramification groups are conjugated. -/
lemma conductorExponentAt_smul (σ : Gal(K/ℚ)) :
    ρ.conductorExponentAt (σ • Q) = ρ.conductorExponentAt Q := by
  simp only [conductorExponentAt, Ideal.ramificationGroup_smul,
    Subgroup.card_map_of_injective (f := (MulAut.conj σ : Gal(K/ℚ) →* Gal(K/ℚ)))
      (MulAut.conj σ).injective, finrankInvariantsField_map_conj]

/-- The **exponent `f(ρ, p)` of the conductor** (LMFDB `modlgal.conductor`) of a representation `ρ`
of `Gal(K/ℚ)` over a field `k` at a prime number `p`: the exponent `f(ρ, Q)` at a prime `Q` of
`𝓞 K` above `p`, which does not depend on `Q` (`Representation.conductorExponent_eq`). -/
noncomputable def conductorExponent : ℚ :=
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  ρ.conductorExponentAt (Classical.arbitrary (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))).1

open scoped Classical in
/-- The **conductor** (LMFDB `modlgal.conductor`) of a mod-`ℓ` Galois representation `ρ` of
`Gal(K/ℚ)` on a finite-dimensional vector space over `k = 𝔽_ℓ`: the product `∏_{p ≠ ℓ} p^f(ρ, p)`
over the prime numbers `p ≠ ℓ`. The exponents `f(ρ, p)` are integers, vanishing at the primes
unramified in `K` (`Representation.conductorExponent_eq_zero`), so that the conductor is a positive
integer coprime to `ℓ`; their integrality is not proved here, and the conductor is a real number.
-/
noncomputable def modEllConductor : ℝ :=
  ∏ᶠ p : Nat.Primes, if (p : ℕ) = ℓ then 1 else (p : ℝ) ^ (ρ.conductorExponent p : ℝ)

variable [IsGalois ℚ K] [Q.IsPrime]

/-- **The exponent of the conductor vanishes at an unramified prime.** -/
lemma conductorExponentAt_eq_zero [Algebra.IsUnramifiedAt (𝓞 ℚ) Q] :
    ρ.conductorExponentAt Q = 0 := by
  simp [conductorExponentAt, finrankInvariantsField_bot]

variable [Q.LiesOver (Ideal.span {(p : ℤ)})]

/-- **The exponent of the conductor at `p` is its exponent at any prime above `p`**, since the
Galois group acts transitively on the primes above `p`. -/
lemma conductorExponent_eq : ρ.conductorExponent p = ρ.conductorExponentAt Q := by
  have : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  rcases Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)})
    (Classical.arbitrary (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))).1 Q Gal(K/ℚ) with ⟨σ, hσ⟩
  rw [conductorExponent, ← hσ, conductorExponentAt_smul]

/-- **The exponent of the conductor vanishes at a prime unramified in `K`.** -/
lemma conductorExponent_eq_zero [Algebra.IsUnramifiedAt (𝓞 ℚ) Q] : ρ.conductorExponent p = 0 :=
  (ρ.conductorExponent_eq Q p).trans (ρ.conductorExponentAt_eq_zero Q)

end Representation
