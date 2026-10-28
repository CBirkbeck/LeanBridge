import LeanBridge.ForMathlib.NumberTheory.Artin.Basic

/-!
# Galois orbits of Artin representations

An automorphism `σ` of `ℂ` acts on complex representations by acting on their coefficients: the
conjugate of `ρ` by `σ` is `σ ∘ ρ` in a basis, or equivalently the base change of `ρ` along `σ`. Two
representations `ρ` and `ρ'` on `V` are Galois conjugate if `ρ'` is isomorphic to such a conjugate,
that is, if there is a `σ`-semilinear bijection `V → V` intertwining `ρ` and `ρ'`. The values of the
character of an Artin representation are algebraic, and every automorphism of `ℚ̄` extends to `ℂ`,
so the orbits of `Aut(ℂ)` are the orbits of `Gal(ℚ̄/ℚ)` of the LMFDB.

## Main definitions

* `Representation.IsGaloisConjugate` (LMFDB `artin.galois_orbit`).
* `Representation.galoisOrbit` (LMFDB `artin.galois_orbit`).

## Main results

* `Representation.IsGaloisConjugate.symm` and `Representation.IsGaloisConjugate.trans`: Galois
  conjugacy is an equivalence relation.
* `Representation.IsGaloisConjugate.isArtin`: a Galois conjugate of an Artin representation is an
  Artin representation.
-/

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {ρ ρ' ρ'' : Representation ℂ G V}

variable (ρ ρ') in
/-- Representations `ρ` and `ρ'` of `G` on a complex vector space `V` are **Galois conjugate**
(LMFDB `artin.galois_orbit`) if `ρ'` is isomorphic to the conjugate of `ρ` by an automorphism `σ` of
`ℂ`: some additive bijection `f : V → V` is `σ`-semilinear, `f (c v) = σ(c) f(v)`, and intertwines
`ρ` and `ρ'`. In a basis of `V`, this says that the matrices of `ρ'` are conjugate to those of `ρ`
with `σ` applied to their entries; the LMFDB's "pre-composition" is this action on coefficients. -/
def IsGaloisConjugate : Prop :=
  ∃ σ : ℂ ≃+* ℂ, ∃ f : V ≃+ V, (∀ (c : ℂ) (v : V), f (c • v) = σ c • f v) ∧
    ∀ (g : G) (v : V), f (ρ g v) = ρ' g (f v)

variable (ρ) in
/-- The **Galois orbit** (LMFDB `artin.galois_orbit`) of a representation `ρ` of `G` on a complex
vector space `V` (an Artin representation when `G = Gal(ℚ̄/ℚ)`): the representations on `V` that are
Galois conjugate to `ρ` (`Representation.IsGaloisConjugate`). Galois conjugates have the same
dimension, so every Galois conjugate of `ρ` is isomorphic to a representation on `V`. -/
def galoisOrbit : Set (Representation ℂ G V) :=
  {ρ' | ρ.IsGaloisConjugate ρ'}

lemma IsGaloisConjugate.refl : ρ.IsGaloisConjugate ρ :=
  ⟨.refl ℂ, .refl V, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

lemma mem_galoisOrbit_self : ρ ∈ ρ.galoisOrbit :=
  IsGaloisConjugate.refl

/-- **Galois conjugacy is symmetric.** -/
lemma IsGaloisConjugate.symm (h : ρ.IsGaloisConjugate ρ') : ρ'.IsGaloisConjugate ρ := by
  rcases h with ⟨σ, f, hf, hρ⟩
  refine ⟨σ.symm, f.symm, fun c v ↦ f.injective ?_, fun g v ↦ f.injective ?_⟩
  · rw [f.apply_symm_apply, hf, f.apply_symm_apply, σ.apply_symm_apply]
  · rw [f.apply_symm_apply, hρ, f.apply_symm_apply]

/-- **Galois conjugacy is transitive.** -/
lemma IsGaloisConjugate.trans (h : ρ.IsGaloisConjugate ρ') (h' : ρ'.IsGaloisConjugate ρ'') :
    ρ.IsGaloisConjugate ρ'' := by
  rcases h with ⟨σ, f, hf, hρ⟩
  rcases h' with ⟨σ', f', hf', hρ'⟩
  refine ⟨σ.trans σ', f.trans f', fun c v ↦ ?_, fun g v ↦ ?_⟩
  · rw [AddEquiv.trans_apply, hf, hf', AddEquiv.trans_apply, RingEquiv.trans_apply]
  · rw [AddEquiv.trans_apply, hρ, hρ', AddEquiv.trans_apply]

lemma IsGaloisConjugate.ker_eq (h : ρ.IsGaloisConjugate ρ') : ρ'.ker = ρ.ker := by
  rcases h with ⟨σ, f, -, hρ⟩
  ext g
  simp only [MonoidHom.mem_ker, LinearMap.ext_iff, Module.End.one_apply]
  refine ⟨fun h v ↦ f.injective ?_, fun h v ↦ ?_⟩
  · rw [hρ, h]
  · rw [← f.apply_symm_apply v, ← hρ, h]

/-- **A Galois conjugate of an Artin representation is an Artin representation.** -/
lemma IsGaloisConjugate.isArtin {K : Type*} [Field K]
    {π π' : Representation ℂ Gal(AlgebraicClosure K/K) V} (h : π.IsGaloisConjugate π')
    (hπ : π.IsArtin) : π'.IsArtin :=
  ⟨hπ.finiteDimensional_space, h.ker_eq ▸ hπ.isOpen_ker⟩

end Representation
