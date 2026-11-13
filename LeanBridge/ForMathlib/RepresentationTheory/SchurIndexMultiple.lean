import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.ComplexAutomorphism
import LeanBridge.ForMathlib.RepresentationTheory.CharacterLabel
import LeanBridge.ForMathlib.RepresentationTheory.SchurIndex
import Mathlib.RingTheory.Trace.Basic
import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# Schur index many copies of the rational orbit sum are afforded over `ℚ`

Let `χ` be the character of an irreducible complex representation `V` of a finite group, `ℚ(χ)`
its field of values and `ψ = ∑ σ ∘ χ` the sum of its distinct Galois conjugates, the irreducible
rational character `FDRep.rationalCharacter`. The Schur index `m` of `χ` over `ℚ`
(`FDRep.schurIndex`, LMFDB `group.representation.schur_index`) is the least degree `[E : ℚ(χ)]` of
a field `ℚ(χ) ⊆ E ⊆ ℂ` over which `V` is realized, `V ≅ ℂ ⊗_E W`. Restricting the scalars of `W`
to `ℚ` gives a representation over `ℚ` whose character is `Tr_{E/ℚ} ∘ χ`. For `x ∈ ℚ(χ)`,
`Tr_{E/ℚ}(x) = [E : ℚ(χ)] Tr_{ℚ(χ)/ℚ}(x)`, both traces being degrees times the sum of the conjugates
of `x`, and `Tr_{ℚ(χ)/ℚ}(χ(g)) = ∑ τ(χ(g))` over the embeddings `τ` of `ℚ(χ)` into `ℂ`, which are
the restrictions of the automorphisms of `ℂ` and correspond to the Galois conjugates of `χ`. So
`m ψ` is the character of a representation with matrix entries in `ℚ`: `m` copies of the
`ℚ`-valued character `ψ` produce an actual representation over `ℚ`, which is how the Schur index
enters LMFDB `group.min_faithful_linear`.

That no fewer copies suffice is the other half of the classical theorem (Isaacs, Corollary 10.2):
it needs the simple component of `ℚ[G]` attached to `χ` as a central simple algebra over `ℚ(χ)` of
index `m`, and is not proved here.

## Main results

* `FDRep.exists_character_eq_trace`: restriction of scalars along a finite field extension
  `E / k`, with character `Tr_{E/k} ∘ χ`.
* `IntermediateField.trace_inclusion`: for subfields `K ⊆ E` of `ℂ` of finite degree over `ℚ` and
  `x ∈ K`, `Tr_{E/ℚ}(x) = [E : K] Tr_{K/ℚ}(x)`.
* `FDRep.sum_algHom_characterField_eq_rationalCharacter`: the sum of the embeddings of `ℚ(χ)`
  applied to `χ(g)` is the irreducible rational character at `g`.
* `FDRep.exists_character_eq_schurIndex_mul_rationalCharacter` (LMFDB `group.min_faithful_linear`,
  `group.representation.schur_index`): `m ψ` is the character of a representation over `ℚ`, for
  `m` the Schur index of `χ` over `ℚ`.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Chapter 10.
-/

open IntermediateField Module

variable {G : Type} [Group G]

namespace FDRep

/-- **Restriction of scalars**: a representation `W` over a field `E` of finite degree over `k` is a
representation over `k`, whose character is the trace from `E` to `k` of the character of `W`. -/
lemma exists_character_eq_trace {k E : Type} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] (W : FDRep E G) :
    ∃ U : FDRep k G, ∀ g, U.character g = Algebra.trace k E (W.character g) := by
  let _ : Module k W := Module.compHom W (algebraMap k E)
  have : IsScalarTower k E W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : FiniteDimensional k W := Finite.trans E W
  let ρ : Representation k G W :=
    { toFun g := (W.ρ g).restrictScalars k
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
  exact ⟨FDRep.of ρ, fun g ↦ (congrFun (character_of ρ) g).trans
    (LinearMap.trace_restrictScalars (W.ρ g))⟩

end FDRep

namespace IntermediateField

variable {K E : IntermediateField ℚ ℂ} [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]

/-- **The trace of an element of a subfield, in a larger field**: for subfields `K ⊆ E` of `ℂ` of
finite degree over `ℚ` and `x ∈ K`, `Tr_{E/ℚ}(x) = [E : K] Tr_{K/ℚ}(x)`, both traces being the
sum of the roots of the minimal polynomial of `x` times `[E : ℚ(x)]` and `[K : ℚ(x)]`. -/
lemma trace_inclusion (h : K ≤ E) (x : K) :
    (Algebra.trace ℚ E (inclusion h x) : ℂ) = K.relfinrank E * (Algebra.trace ℚ K x : ℂ) := by
  have hmin : minpoly ℚ (inclusion h x) = minpoly ℚ x :=
    (minpoly.algebraMap_eq (algebraMap E ℂ).injective _).symm.trans
      (minpoly.algebraMap_eq (algebraMap K ℂ).injective x)
  have hE : (Algebra.trace ℚ E (inclusion h x) : ℂ) = finrank ℚ⟮inclusion h x⟯ E •
      ((minpoly ℚ (inclusion h x)).aroots ℂ).sum :=
    (eq_ratCast (algebraMap ℚ ℂ) _).symm.trans (trace_eq_sum_roots (IsAlgClosed.splits _))
  have hK : (Algebra.trace ℚ K x : ℂ) = finrank ℚ⟮x⟯ K • ((minpoly ℚ x).aroots ℂ).sum :=
    (eq_ratCast (algebraMap ℚ ℂ) _).symm.trans (trace_eq_sum_roots (IsAlgClosed.splits _))
  have hdE : (minpoly ℚ x).natDegree * finrank ℚ⟮inclusion h x⟯ E = finrank ℚ E := by
    rw [← hmin, ← adjoin.finrank (IsIntegral.of_finite ℚ _), finrank_mul_finrank]
  have hdK : (minpoly ℚ x).natDegree * finrank ℚ⟮x⟯ K = finrank ℚ K := by
    rw [← adjoin.finrank (IsIntegral.of_finite ℚ _), finrank_mul_finrank]
  have hKE : finrank ℚ K * K.relfinrank E = finrank ℚ E := by
    rw [← relfinrank_bot_left, ← relfinrank_bot_left, relfinrank_mul_relfinrank bot_le h]
  have hdeg : finrank ℚ⟮inclusion h x⟯ E = finrank ℚ⟮x⟯ K * K.relfinrank E :=
    Nat.eq_of_mul_eq_mul_left (minpoly.natDegree_pos (IsIntegral.of_finite ℚ x)) <| by
      rw [hdE, ← mul_assoc, hdK, hKE]
  rw [hE, hK, hmin, hdeg, mul_comm, mul_smul, nsmul_eq_mul]

end IntermediateField

namespace FDRep

variable [Finite G] (V : FDRep ℂ G)

/-- **The trace of a character value from its field of values is the irreducible rational
character**: the embeddings `τ` of `ℚ(χ)` into `ℂ` are the restrictions of the automorphisms of
`ℂ`, two of them agreeing on the values of `χ` only if they are equal, so the functions `τ ∘ χ` are
the distinct Galois conjugates of `χ`, and `∑ τ(χ(g))` is their sum at `g`. -/
lemma sum_algHom_characterField_eq_rationalCharacter (g : G) :
    ∑ τ : V.characterField ℚ →ₐ[ℚ] ℂ, τ ⟨V.character g, V.character_mem_characterField ℚ g⟩ =
      V.rationalCharacter g := by
  classical
  let Φ : (V.characterField ℚ →ₐ[ℚ] ℂ) → G → ℂ :=
    fun τ g ↦ τ ⟨V.character g, V.character_mem_characterField ℚ g⟩
  have hΦ : Function.Injective Φ := fun τ₁ τ₂ h ↦ adjoin_algHom_ext ℚ <| by
    rintro - ⟨g, rfl⟩
    exact congrFun h g
  have himage : Finset.univ.image Φ = V.finite_galoisConjugates.toFinset := by
    ext ψ
    rw [Finset.mem_image, V.finite_galoisConjugates.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rintro ⟨τ, -, rfl⟩
      rcases exists_algEquiv_apply_eq_of_countable τ with ⟨σ, hσ⟩
      exact ⟨σ, funext fun g ↦ hσ ⟨V.character g, V.character_mem_characterField ℚ g⟩⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ.toAlgHom.comp (V.characterField ℚ).val, Finset.mem_univ _, rfl⟩
  rw [rationalCharacter, finsum_mem_eq_finite_toFinset_sum _ V.finite_galoisConjugates, ← himage,
    Finset.sum_image fun τ₁ _ τ₂ _ h ↦ hΦ h, Finset.sum_apply]

variable [CategoryTheory.Simple V]

/-- **Schur index many copies of the irreducible rational character are afforded over `ℚ`**
(LMFDB `group.min_faithful_linear`, `group.representation.schur_index`): for an irreducible complex
representation `V` with character `χ` and Schur index `m` over `ℚ`, the multiple `m ψ` of the sum
`ψ` of the Galois conjugates of `χ` is the character of a representation over `ℚ`, obtained by
restricting the scalars of a realization of `V` over a field of degree `m` over `ℚ(χ)`. -/
lemma exists_character_eq_schurIndex_mul_rationalCharacter :
    ∃ U : FDRep ℚ G, ∀ g, (U.character g : ℂ) = V.schurIndex ℚ * V.rationalCharacter g := by
  rcases exists_relfinrank_eq_schurIndex V.schurIndex_pos with ⟨E, hKE, hd, W, ⟨e⟩⟩
  have hW (g : G) : algebraMap E ℂ (W.character g) = V.character g :=
    congrFun ((character_baseChange W).symm.trans (char_iso e)) g
  have hrank : finrank ℚ (V.characterField ℚ) * V.schurIndex ℚ = finrank ℚ E := by
    rw [← hd, ← relfinrank_bot_left, ← relfinrank_bot_left, relfinrank_mul_relfinrank bot_le hKE]
  have : FiniteDimensional ℚ E :=
    Module.finite_of_finrank_pos <| hrank ▸ Nat.mul_pos finrank_pos V.schurIndex_pos
  rcases W.exists_character_eq_trace (k := ℚ) with ⟨U, hU⟩
  refine ⟨U, fun g ↦ ?_⟩
  have hx : W.character g = inclusion hKE ⟨V.character g, V.character_mem_characterField ℚ g⟩ :=
    Subtype.ext (hW g)
  rw [hU g, hx, trace_inclusion, hd, ← sum_algHom_characterField_eq_rationalCharacter,
    ← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings]

end FDRep
