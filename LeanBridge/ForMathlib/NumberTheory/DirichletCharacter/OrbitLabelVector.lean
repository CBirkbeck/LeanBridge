import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel
import LeanBridge.ForMathlib.NumberTheory.MulChar.FieldOfValues

/-!
# The vector that orders the labels of Galois orbits of Dirichlet characters

The LMFDB labels a Galois orbit of Dirichlet characters of modulus `q` as `q.A`, where `A` encodes
the position of the orbit in the lexicographic order of the Galois-invariant vectors
`(ord χ, Tr χ(2), …, Tr χ(q - 1))` (LMFDB `character.dirichlet.conrey.orbit_label`), `Tr` being the
trace from the field of values `ℚ(χ)` of `χ` to `ℚ`. LeanBridge's label
`DirichletCharacter.galoisOrbitLabel` encodes the orbit index, the position in the lexicographic
order of the trace vectors `(ord χ, Tr χ(1), Tr χ(2), …, Tr χ(q - 1))` (LMFDB
`character.dirichlet.galois_orbit_index`), which have the extra entry `Tr χ(1)`. That entry is the
degree `[ℚ(χ) : ℚ] = φ(ord χ)` (`MulChar.degree_eq_totient`), a function of the first entry, so the
two vectors order the characters of modulus `q` in the same way: the formal label is the knowl's,
`A` being the letter code `a, …, z, ba, bb, …` of the number of orbits with a smaller vector.

## Main definitions

* `DirichletCharacter.orbitLabelVector` (LMFDB `character.dirichlet.conrey.orbit_label`): the
  vector `(ord χ, Tr χ(2), …, Tr χ(q - 1))`.

## Main results

* `DirichletCharacter.valueTrace_one`: the entry `Tr χ(1)` of the trace vector is `φ(ord χ)`.
* `DirichletCharacter.eraseIdx_galoisOrbitTraceVector`: the knowl's vector is the trace vector
  without its entry `Tr χ(1)`.
* `DirichletCharacter.orbitLabelVector_lt_orbitLabelVector_iff`: the knowl's vectors are ordered as
  the trace vectors.
* `DirichletCharacter.orbitLabelVector_eq_iff`: the knowl's vector depends only on the Galois orbit
  and determines it.
* `DirichletCharacter.galoisOrbitIndex_eq_ncard_orbitLabelVector`: the orbit index is the position
  of the knowl's vector in the lexicographic order of the knowl's vectors of modulus `q`.
* `DirichletCharacter.galoisOrbitLabel_eq`: the label of the Galois orbit is the knowl's.

## References

* A. J. Best et al., *Computing classical modular forms*, arXiv:2002.04717, §3.3.
-/

open IntermediateField Set

namespace DirichletCharacter

variable {q : ℕ} (χ : DirichletCharacter ℂ q) {ψ : DirichletCharacter ℂ q}

/-- The **Galois-invariant vector** `(ord χ, Tr χ(2), …, Tr χ(q - 1))` of a Dirichlet character `χ`
of modulus `q` (LMFDB `character.dirichlet.conrey.orbit_label`), whose lexicographic order labels
the Galois orbits: the order of `χ` followed by the traces of `χ i` from the field of values of `χ`
to `ℚ` for `i = 2, …, q - 1`. It is the trace vector `DirichletCharacter.galoisOrbitTraceVector`
without its entry `Tr χ(1)` (`DirichletCharacter.eraseIdx_galoisOrbitTraceVector`). -/
noncomputable def orbitLabelVector : List ℚ :=
  (orderOf χ : ℚ) :: (List.range (q - 2)).map fun i ↦ χ.valueTrace ((i + 2 : ℕ) : ZMod q)

/-- **The trace of `χ 1` is the degree `φ(ord χ)` of the field of values.** -/
lemma valueTrace_one : χ.valueTrace 1 = (orderOf χ).totient := by
  rw [valueTrace, map_one, ← map_one (algebraMap ℚ (adjoin ℚ (Set.range χ))),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  exact congrArg Nat.cast χ.degree_eq_totient

lemma galoisOrbitTraceVector_eq_cons (hq : 2 ≤ q) : χ.galoisOrbitTraceVector = (orderOf χ : ℚ) ::
    χ.valueTrace 1 :: (List.range (q - 2)).map fun i ↦ χ.valueTrace ((i + 2 : ℕ) : ZMod q) := by
  rcases Nat.exists_eq_add_of_le' hq with ⟨m, rfl⟩
  simp [galoisOrbitTraceVector, List.range_succ_eq_map, add_assoc, one_add_one_eq_two]

/-- **The knowl's vector is the trace vector without its entry `Tr χ(1)`.** -/
lemma eraseIdx_galoisOrbitTraceVector :
    χ.galoisOrbitTraceVector.eraseIdx 1 = χ.orbitLabelVector := by
  rcases lt_or_ge q 2 with hq | hq
  · simp [galoisOrbitTraceVector, Nat.sub_eq_zero_of_le (by omega : q ≤ 1), orbitLabelVector,
      Nat.sub_eq_zero_of_le (by omega : q ≤ 2)]
  · simp [galoisOrbitTraceVector_eq_cons χ hq, orbitLabelVector]

variable {χ}

/-- **The knowl's vectors are ordered as the trace vectors**: the extra entry `Tr χ(1) = φ(ord χ)`
of the trace vector is a function of its first entry `ord χ`. -/
lemma orbitLabelVector_lt_orbitLabelVector_iff : ψ.orbitLabelVector < χ.orbitLabelVector ↔
    ψ.galoisOrbitTraceVector < χ.galoisOrbitTraceVector := by
  rcases lt_or_ge q 2 with hq | hq
  · rw [← eraseIdx_galoisOrbitTraceVector, ← eraseIdx_galoisOrbitTraceVector,
      galoisOrbitTraceVector, galoisOrbitTraceVector, Nat.sub_eq_zero_of_le (by omega : q ≤ 1)]
    rfl
  · rw [orbitLabelVector, orbitLabelVector, galoisOrbitTraceVector_eq_cons ψ hq,
      galoisOrbitTraceVector_eq_cons χ hq, List.cons_lt_cons_iff, List.cons_lt_cons_iff,
      List.cons_lt_cons_iff, valueTrace_one, valueTrace_one]
    refine or_congr_right <| and_congr_right fun h ↦ ?_
    rw [Nat.cast_inj.mp h]
    simp

lemma orbitLabelVector_eq_orbitLabelVector_iff : ψ.orbitLabelVector = χ.orbitLabelVector ↔
    ψ.galoisOrbitTraceVector = χ.galoisOrbitTraceVector := by
  rw [le_antisymm_iff, le_antisymm_iff, ← not_lt, ← not_lt, ← not_lt, ← not_lt,
    orbitLabelVector_lt_orbitLabelVector_iff, orbitLabelVector_lt_orbitLabelVector_iff]

variable [NeZero q] in
/-- **The knowl's vector depends only on the Galois orbit and determines it**: two Dirichlet
characters of nonzero modulus have the same vector `(ord χ, Tr χ(2), …, Tr χ(q - 1))` exactly when
they lie in one Galois orbit. -/
lemma orbitLabelVector_eq_iff : ψ.orbitLabelVector = χ.orbitLabelVector ↔ ψ ∈ χ.galoisOrbit :=
  orbitLabelVector_eq_orbitLabelVector_iff.trans galoisOrbitTraceVector_eq_iff

variable (χ)

/-- **The orbit index is the position of the knowl's vector** (LMFDB
`character.dirichlet.conrey.orbit_label`): it is one more than the number of vectors
`(ord ψ, Tr ψ(2), …, Tr ψ(q - 1))` of the characters `ψ` of modulus `q` that are lexicographically
smaller than that of `χ`. -/
lemma galoisOrbitIndex_eq_ncard_orbitLabelVector : χ.galoisOrbitIndex =
    {t | t ∈ Set.range (orbitLabelVector (q := q)) ∧ t < χ.orbitLabelVector}.ncard + 1 := by
  have h : {t | t ∈ Set.range (orbitLabelVector (q := q)) ∧ t < χ.orbitLabelVector} =
      (List.eraseIdx · 1) ''
      {t | t ∈ Set.range (galoisOrbitTraceVector (q := q)) ∧ t < χ.galoisOrbitTraceVector} := by
    ext t
    constructor
    · rintro ⟨⟨ρ, rfl⟩, hρ⟩
      exact ⟨ρ.galoisOrbitTraceVector, ⟨⟨ρ, rfl⟩, orbitLabelVector_lt_orbitLabelVector_iff.mp hρ⟩,
        eraseIdx_galoisOrbitTraceVector ρ⟩
    · rintro ⟨_, ⟨⟨ρ, rfl⟩, hρ⟩, rfl⟩
      simp only [eraseIdx_galoisOrbitTraceVector]
      exact ⟨⟨ρ, rfl⟩, orbitLabelVector_lt_orbitLabelVector_iff.mpr hρ⟩
  rw [galoisOrbitIndex, h, InjOn.ncard_image]
  rintro _ ⟨⟨ρ, rfl⟩, -⟩ _ ⟨⟨ρ', rfl⟩, -⟩ hρ
  simp only [eraseIdx_galoisOrbitTraceVector] at hρ
  exact orbitLabelVector_eq_orbitLabelVector_iff.mp hρ

/-- **The label of a Galois orbit is the knowl's** (LMFDB `character.dirichlet.conrey.orbit_label`):
the label of the orbit of `χ` is `q.A`, where `A` is the letter code of the number of vectors
`(ord ψ, Tr ψ(2), …, Tr ψ(q - 1))` of the characters `ψ` of modulus `q` that are lexicographically
smaller than that of `χ`. -/
lemma galoisOrbitLabel_eq : χ.galoisOrbitLabel = toString q ++ "." ++
    letterCode {t | t ∈ Set.range (orbitLabelVector (q := q)) ∧ t < χ.orbitLabelVector}.ncard := by
  rw [galoisOrbitLabel, galoisOrbitIndex_eq_ncard_orbitLabelVector, Nat.add_sub_cancel]

end DirichletCharacter
