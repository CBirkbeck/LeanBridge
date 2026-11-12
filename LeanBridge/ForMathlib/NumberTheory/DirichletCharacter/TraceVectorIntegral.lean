import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel

/-!
# The trace vectors of Dirichlet characters are integral

The LMFDB orders the Galois orbits of the Dirichlet characters of modulus `q` by the lexicographic
order of their trace vectors `t([χ]) = (n, t₁, …, t_{q-1}) ∈ ℤ^q`, where `n` is the order of `χ`
and `tᵢ` is the trace of `χ i` from the field of values `ℚ(χ)` of `χ` to `ℚ` (LMFDB
`character.dirichlet.galois_orbit_index`). LeanBridge keeps the trace vector in `ℚ`
(`DirichletCharacter.galoisOrbitTraceVector`). Its entries are rational integers: the values of `χ`
are `0` or roots of unity, hence algebraic integers, the trace of an algebraic integer is integral
over `ℤ`, and `ℤ` is integrally closed. So the trace vector is the image in `ℚ` of a tuple of `q`
integers, and since the inclusion `ℤ → ℚ` is strictly increasing, the orbit index is the position of
that tuple in the lexicographic order of the tuples in `ℤ^q` arising from the characters of modulus
`q`.

## Main definitions

* `DirichletCharacter.intTraceVector` (LMFDB `character.dirichlet.galois_orbit_index`): the trace
  vector `t([χ]) ∈ ℤ^q`.

## Main results

* `DirichletCharacter.intCast_num_valueTrace`: the traces `tᵢ` are integers.
* `DirichletCharacter.map_intCast_intTraceVector`: in `ℚ`, the trace vector in `ℤ^q` is
  `DirichletCharacter.galoisOrbitTraceVector`.
* `DirichletCharacter.length_intTraceVector`: the trace vector has `q` entries.
* `DirichletCharacter.intTraceVector_eq_iff`: the trace vector in `ℤ^q` depends only on the Galois
  orbit and determines it.
* `DirichletCharacter.galoisOrbitIndex_eq_ncard_intTraceVector`: the orbit index is the position of
  the trace vector in the lexicographic order of the trace vectors in `ℤ^q` of modulus `q`.
-/

open IntermediateField

namespace DirichletCharacter

variable {q : ℕ} (χ : DirichletCharacter ℂ q) {ψ : DirichletCharacter ℂ q}

lemma isIntegral_toFieldOfValues (x : ZMod q) : IsIntegral ℤ (χ.toFieldOfValues x) := by
  by_cases hx : IsUnit x
  · have h : χ.toFieldOfValues x ^ orderOf χ = 1 := Subtype.ext <|
      (χ.pow_apply' χ.orderOf_pos.ne' x).symm.trans <| by
        rw [pow_orderOf_eq_one, MulChar.one_apply hx, OneMemClass.coe_one]
    exact IsIntegral.of_pow χ.orderOf_pos (h ▸ isIntegral_one)
  · rw [χ.toFieldOfValues.map_nonunit hx]
    exact isIntegral_zero

/-- **The traces `tᵢ` are rational integers** (LMFDB `character.dirichlet.galois_orbit_index`):
the trace of `χ x` from the field of values of `χ` to `ℚ` is the integer given by its numerator, as
`χ x` is an algebraic integer. -/
lemma intCast_num_valueTrace (x : ZMod q) : ((χ.valueTrace x).num : ℚ) = χ.valueTrace x := by
  have : FiniteDimensional ℚ (adjoin ℚ (Set.range χ)) := finiteDimensional_adjoin_range
  rcases IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℚ) (χ.isIntegral_toFieldOfValues x)) with ⟨m, hm⟩
  rw [valueTrace, ← hm, eq_intCast, Rat.num_intCast]

/-- The **trace vector** `t([χ]) = (n, t₁, …, t_{q-1}) ∈ ℤ^q` of a Dirichlet character `χ` of
modulus `q` (LMFDB `character.dirichlet.galois_orbit_index`): the order `n` of `χ` followed by the
traces `tᵢ = tr_{ℚ(χ)/ℚ}(χ i)` for `i = 1, …, q - 1`, which are rational integers
(`DirichletCharacter.intCast_num_valueTrace`), here written as their numerators. In `ℚ` it is
`DirichletCharacter.galoisOrbitTraceVector` (`DirichletCharacter.map_intCast_intTraceVector`). -/
noncomputable def intTraceVector : List ℤ :=
  (orderOf χ : ℤ) :: (List.range (q - 1)).map fun i ↦ (χ.valueTrace ((i + 1 : ℕ) : ZMod q)).num

/-- **The trace vector in `ℤ^q` is the trace vector of LeanBridge**: in `ℚ`, it is
`DirichletCharacter.galoisOrbitTraceVector`. -/
lemma map_intCast_intTraceVector :
    χ.intTraceVector.map ((↑) : ℤ → ℚ) = χ.galoisOrbitTraceVector := by
  simp [intTraceVector, galoisOrbitTraceVector, intCast_num_valueTrace]

variable [NeZero q] in
/-- **The trace vector has `q` entries**, the order and the traces `t₁, …, t_{q-1}`. -/
lemma length_intTraceVector : χ.intTraceVector.length = q := by
  simp [intTraceVector, Nat.sub_add_cancel NeZero.one_le]

variable {χ}

lemma intTraceVector_lt_intTraceVector_iff :
    ψ.intTraceVector < χ.intTraceVector ↔ ψ.galoisOrbitTraceVector < χ.galoisOrbitTraceVector := by
  rw [← map_intCast_intTraceVector, ← map_intCast_intTraceVector]
  exact (StrictMono.lt_iff_lt fun _ _ h ↦ List.map_lt (fun _ _ ↦ Int.cast_lt.mpr) h).symm

variable [NeZero q] in
/-- **The trace vector in `ℤ^q` depends only on the Galois orbit and determines it**: two Dirichlet
characters of nonzero modulus have the same trace vector exactly when they lie in one Galois
orbit. -/
lemma intTraceVector_eq_iff : ψ.intTraceVector = χ.intTraceVector ↔ ψ ∈ χ.galoisOrbit := by
  rw [← galoisOrbitTraceVector_eq_iff, ← map_intCast_intTraceVector, ← map_intCast_intTraceVector]
  exact (List.map_injective_iff.mpr Int.cast_injective).eq_iff.symm

variable (χ) in
/-- **The orbit index is the position of the trace vector in `ℤ^q`** (LMFDB
`character.dirichlet.galois_orbit_index`): it is one more than the number of trace vectors in
`ℤ^q` of the characters of modulus `q` that are lexicographically smaller than that of `χ`. -/
lemma galoisOrbitIndex_eq_ncard_intTraceVector : χ.galoisOrbitIndex =
    {t | t ∈ Set.range (intTraceVector (q := q)) ∧ t < χ.intTraceVector}.ncard + 1 := by
  have h : {t | t ∈ Set.range (galoisOrbitTraceVector (q := q)) ∧ t < χ.galoisOrbitTraceVector} =
      List.map ((↑) : ℤ → ℚ) ''
      {t | t ∈ Set.range (intTraceVector (q := q)) ∧ t < χ.intTraceVector} := by
    ext t
    constructor
    · rintro ⟨⟨ρ, rfl⟩, hρ⟩
      exact ⟨ρ.intTraceVector, ⟨⟨ρ, rfl⟩, intTraceVector_lt_intTraceVector_iff.mpr hρ⟩,
        map_intCast_intTraceVector ρ⟩
    · rintro ⟨_, ⟨⟨ρ, rfl⟩, hρ⟩, rfl⟩
      rw [map_intCast_intTraceVector]
      exact ⟨⟨ρ, rfl⟩, intTraceVector_lt_intTraceVector_iff.mp hρ⟩
  rw [galoisOrbitIndex, h,
    Set.ncard_image_of_injective _ (List.map_injective_iff.mpr Int.cast_injective)]

end DirichletCharacter
