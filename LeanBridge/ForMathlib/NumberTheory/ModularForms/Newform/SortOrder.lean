import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel

/-!
# The sort order of newforms

The LMFDB's newforms are the Galois orbits of newforms (LMFDB `cmf.galois_orbit`), of every level
`N ≥ 1` and every weight `k`. Its search results are sorted by level, weight, character and trace
sequence (LMFDB `cmf.sort_order`): the character of an orbit is ordered by the index of the Galois
orbit of its nebentypus (LMFDB `character.dirichlet.galois_orbit_index`), which does not depend on
the newform of the orbit, and the trace sequence `(Tr(a₁), Tr(a₂), …)` lexicographically (LMFDB
`cmf.hecke_galois_orbit`). The knowl states that these keys define a complete ordering of all
newforms: the key `(N, k, character index, trace sequence)`, in the lexicographic order, determines
the newform orbit, since newform orbits of the same level and weight with the same trace sequence
are equal (`HeckeRing.GL2.NewformOrbit.traceSeq_injective`), so it orders all newform orbits
linearly. Ties are equally impossible when another key is put first. The default order of the
LMFDB's newform search is now of this second kind, with the analytic conductor (LMFDB
`cmf.analytic_conductor`) first; the knowl still names the order by level, weight, character and
trace sequence as the default.

## Main definitions

* `HeckeRing.GL2.NewformOrbit.characterOrbitIndex` (LMFDB `cmf.sort_order`): the index of the Galois
  orbit of the character of a newform orbit.
* `HeckeRing.GL2.AllNewformOrbits` (LMFDB `cmf.sort_order`): the newform orbits of all levels and
  weights.
* `HeckeRing.GL2.AllNewformOrbits.sortKey` (LMFDB `cmf.sort_order`): the default sort key.
* `HeckeRing.GL2.AllNewformOrbits.sortOrder` (LMFDB `cmf.sort_order`): the default sort order, a
  linear order.
* `HeckeRing.GL2.AllNewformOrbits.sortOrderBy` (LMFDB `cmf.sort_order`): the sort order with
  another key first.

## Main results

* `HeckeRing.GL2.AllNewformOrbits.sortKey_injective` (LMFDB `cmf.sort_order`): the default sort key
  determines the newform orbit.
* `HeckeRing.GL2.AllNewformOrbits.injective_toLex_sortKey` (LMFDB `cmf.sort_order`): so does any key
  followed by the default one.
-/

open Function

namespace HeckeRing.GL2

/-- The **index of the Galois orbit of the character** of a newform orbit (LMFDB `cmf.sort_order`,
`character.dirichlet.galois_orbit_index`): the orbit index of the nebentypus of any newform of the
orbit, which does not depend on the newform, as Galois conjugate newforms have Galois conjugate
nebentypus. It is the character key of the LMFDB's sort order. -/
noncomputable def NewformOrbit.characterOrbitIndex {N : ℕ} [NeZero N] {k : ℤ}
    (O : NewformOrbit N k) : ℕ :=
  Quotient.lift (fun f : Newform N k ↦ f.dirichletLift.galoisOrbitIndex)
    (fun (f g : Newform N k) (h : f.IsGaloisConjugate g) ↦ h.elim fun _ hσ ↦
      (DirichletCharacter.galoisOrbitIndex_eq_of_mem_galoisOrbit
        hσ.dirichletLift_mem_galoisOrbit).symm) O

/-- The **newform orbits of all levels and weights** (LMFDB `cmf.sort_order`: "the set of all
newforms"): the triples of a level `N ≥ 1`, a weight `k` and a newform orbit of level `N` and
weight `k`, the newforms of the LMFDB. -/
abbrev AllNewformOrbits : Type :=
  Σ N : ℕ+, Σ k : ℤ, NewformOrbit N k

namespace AllNewformOrbits

/-- The **default sort key** of a newform orbit (LMFDB `cmf.sort_order`): its level, its weight,
the index of the Galois orbit of its character (`NewformOrbit.characterOrbitIndex`) and its trace
sequence (`NewformOrbit.traceSeq`), in the lexicographic order. -/
noncomputable def sortKey (O : AllNewformOrbits) : ℕ ×ₗ ℤ ×ₗ ℕ ×ₗ Lex (ℕ → ℚ) :=
  toLex ((O.1 : ℕ), toLex (O.2.1, toLex (O.2.2.characterOrbitIndex, O.2.2.traceSeq)))

/-- **The default sort key determines the newform orbit** (LMFDB `cmf.sort_order`: "sorted by
level, weight, character, and trace sequence, which defines a complete ordering on the set of all
newforms"): two newform orbits with the same level, weight, character and trace sequence are equal,
as the trace sequence determines the newform orbit among those of a given level and weight. -/
lemma sortKey_injective : Injective sortKey := by
  rintro ⟨N, k, O⟩ ⟨N', k', O'⟩ h
  simp only [sortKey, toLex_inj, Prod.mk_inj, PNat.coe_inj] at h
  rcases h with ⟨rfl, rfl, -, h⟩
  rw [NewformOrbit.traceSeq_injective h]

/-- The **default sort order** of the newform orbits (LMFDB `cmf.sort_order`): the linear order in
which one orbit precedes another when its sort key `sortKey` is lexicographically smaller. It is a
linear order, that is a complete ordering of all newforms, as the sort key is injective
(`sortKey_injective`). -/
noncomputable abbrev sortOrder : LinearOrder AllNewformOrbits :=
  LinearOrder.lift' sortKey sortKey_injective

variable {β : Type*} (g : AllNewformOrbits → β)

/-- **Any key followed by the default sort key determines the newform orbit** (LMFDB
`cmf.sort_order`: "If a specific sort key is chosen, results will be sorted first on that key and
then by level, weight, character, and trace sequence, so that the sort order is always uniquely
determined"). -/
lemma injective_toLex_sortKey : Injective fun O ↦ toLex (g O, sortKey O) :=
  fun _ _ h ↦ sortKey_injective <| congrArg Prod.snd <| toLex.injective h

/-- The **sort order with the key `g` first** (LMFDB `cmf.sort_order`): newform orbits are compared
by `g`, then by the default sort key. It is a linear order (`injective_toLex_sortKey`). -/
noncomputable abbrev sortOrderBy [LinearOrder β] : LinearOrder AllNewformOrbits :=
  LinearOrder.lift' _ (injective_toLex_sortKey g)

end AllNewformOrbits

end HeckeRing.GL2
