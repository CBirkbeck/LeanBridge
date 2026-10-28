import TauCeti.NumberTheory.IntegralLattice.Genus
import TauCeti.NumberTheory.IntegralLattice.JordanSplitting
import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals

/-!
# The Conway genus symbol of an integral lattice: type, signature and Jordan ranks

The Conway genus symbol (LMFDB `lattice.conway_genus_symbol`; Conway and Sloane, *Sphere Packings,
Lattices and Groups*, Chapter 15, §7) of a nondegenerate integral lattice `L` is an invariant of
its genus, written `I_{r,s}(⋯)` or `II_{r,s}(⋯)`: the Roman numeral is the type of `L`, `II` when
`L` is even and `I` when it is odd, `(r, s)` is the signature of `L`, and `(⋯)` collects, for each
prime `p`, the `p`-adic symbol of `L`. For a `p`-adic Jordan decomposition
`L ⊗ ℤ_p = ⊕_q q f_q`, over the powers `q = p^k`, with unimodular forms `f_q`, the `p`-adic symbol
records for each `q` the rank `n_q` of `f_q` and a sign `ε_q`, the Legendre symbol of `det f_q`
(the Jacobi symbol `(2 | det f_q)` when `p = 2`), and when `p = 2` the type `I` or `II` of `f_q`
and the oddity of `f_q` if it has type `I`, up to the rules of Conway and Sloane (compartments,
trains, oddity fusion and sign walking) which make it a genus invariant.

Only part of the symbol is formalised here: the type, the signature and the ranks `n_q`, which
Tau Ceti shows not to depend on the Jordan decomposition. All three are genus invariants
(`TauCeti.IntegralLattice.SameGenus.conwayGenusSymbolCore_eq`). The signs `ε_q` and the dyadic
types, oddities, compartments and trains are not: their independence of the Jordan decomposition is
not available. Nor is the theorem that the symbol and the signature determine the genus.

## Main definitions

* `TauCeti.IntegralLattice.ConwayType`: the type `I` or `II`.
* `TauCeti.IntegralLattice.jordanRank`: the rank `n_q` of the `q`-modular Jordan constituent at
  `q = p ^ k`.
* `TauCeti.IntegralLattice.ConwayGenusSymbolCore` and
  `TauCeti.IntegralLattice.conwayGenusSymbolCore` (LMFDB `lattice.conway_genus_symbol`, partial):
  the type, the signature and the Jordan ranks.

## Main results

* `TauCeti.IntegralLattice.jordanRank_eq`: the Jordan ranks can be read off any Jordan splitting.
* `TauCeti.IntegralLattice.SameGenus.isEven_iff`: lattices in the same genus are both even or both
  odd.
* `TauCeti.IntegralLattice.SameGenus.conwayGenusSymbolCore_eq`: the type, signature and Jordan
  ranks are genus invariants.
-/

open Module
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

lemma IsometryEquiv.normIdeal_le {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] {B₁ : BilinForm R M₁} {B₂ : BilinForm R M₂}
    (e : B₁.IsometryEquiv B₂) : B₁.normIdeal ≤ B₂.normIdeal :=
  (B₁.normIdeal_le_iff _).mpr fun x ↦ e.map_app x x ▸ B₂.self_mem_normIdeal (e x)

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  (L : IntegralLattice V) (M : IntegralLattice W)

/-- The type of an integral lattice in its Conway genus symbol (LMFDB
`lattice.conway_genus_symbol`): **`II`** for an even lattice and **`I`** for an odd one. -/
inductive ConwayType
  | I
  | II
  deriving DecidableEq

open scoped Classical in
/-- The type `I` or `II` of an integral lattice `L` in its Conway genus symbol: `II` if `L` is
even, `I` if it is odd. -/
noncomputable def conwayType : ConwayType :=
  if L.IsEven then .II else .I

/-- The part of the **Conway genus symbol** `I_{r,s}(⋯)` or `II_{r,s}(⋯)` (LMFDB
`lattice.conway_genus_symbol`) formalised here: the type, the signature `(r, s)`, and for every
prime `p` and `k ≥ 0` the rank `n_q` of the `q`-modular constituent of the `p`-adic Jordan
decompositions, `q = p ^ k`. The signs `ε_q` and the dyadic types and oddities are not
included. -/
@[ext]
structure ConwayGenusSymbolCore where
  /-- The type, `I` or `II`. -/
  type : ConwayType
  /-- The signature `(r, s)`. -/
  signature : ℕ × ℕ
  /-- The rank `n_q` of the constituent of scale `q = p ^ k` of the `p`-adic Jordan
  decompositions. -/
  jordanRank : Nat.Primes → ℕ → ℕ

variable {L M} in
/-- **Lattices in the same genus are both even or both odd**: evenness is read off the norm ideal
of the dyadic localization. -/
lemma SameGenus.isEven_iff (h : L.SameGenus M) : L.IsEven ↔ M.IsEven := by
  rcases h.localIntegralForm_equivalent 2 with ⟨e⟩
  have hideal : L.localNormIdeal 2 = M.localNormIdeal 2 :=
    le_antisymm e.normIdeal_le e.symm.normIdeal_le
  rw [isEven_iff_localNormIdeal_le_span_two, isEven_iff_localNormIdeal_le_span_two, hideal]

variable [L.IsNondegenerate] [M.IsNondegenerate] (p : ℕ) [Fact p.Prime] (k : ℕ)

/-- The **Jordan rank** `n_q` of a nondegenerate integral lattice `L` at `q = p ^ k`: the rank of
the `p ^ k`-modular constituent of a `p`-adic Jordan splitting of `L`, which does not depend on
the splitting (`jordanRank_eq`). -/
noncomputable def jordanRank : ℕ :=
  finrank ℤ_[p] ((L.exists_isJordanSplitting_localIntegralForm p L.form_nondegenerate).choose k)

/-- The type, signature and Jordan ranks of a nondegenerate integral lattice `L`, the part of its
**Conway genus symbol** (LMFDB `lattice.conway_genus_symbol`) formalised here. -/
noncomputable def conwayGenusSymbolCore : ConwayGenusSymbolCore where
  type := L.conwayType
  signature := (L.sigPos, L.sigNeg)
  jordanRank q j :=
    haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
    L.jordanRank q j

variable {L M}

/-- **The Jordan ranks can be read off any Jordan splitting.** -/
lemma jordanRank_eq {N : ℕ → Submodule ℤ_[p] (L.LocalCarrier p)}
    (hN : (L.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N) :
    L.jordanRank p k = finrank ℤ_[p] (N k) :=
  L.finrank_eq_of_isJordanSplitting_localIntegralForm p
    ((SameGenus.refl L).localIntegralForm_equivalent p)
    (L.exists_isJordanSplitting_localIntegralForm p L.form_nondegenerate).choose_spec hN k

lemma SameGenus.jordanRank_eq (h : L.SameGenus M) : L.jordanRank p k = M.jordanRank p k :=
  L.finrank_eq_of_isJordanSplitting_localIntegralForm p (h.localIntegralForm_equivalent p)
    (L.exists_isJordanSplitting_localIntegralForm p L.form_nondegenerate).choose_spec
    (M.exists_isJordanSplitting_localIntegralForm p M.form_nondegenerate).choose_spec k

/-- **The type, signature and Jordan ranks are genus invariants.** -/
lemma SameGenus.conwayGenusSymbolCore_eq (h : L.SameGenus M) :
    L.conwayGenusSymbolCore = M.conwayGenusSymbolCore := by
  refine ConwayGenusSymbolCore.ext ?_ ?_ (funext fun q ↦ funext fun j ↦ ?_)
  · rw [conwayGenusSymbolCore, conwayGenusSymbolCore, conwayType, conwayType, h.isEven_iff]
  · exact congrArg (fun s : ℕ × ℕ × ℕ ↦ (s.1, s.2.2)) h.signature_eq
  · have : Fact (q : ℕ).Prime := ⟨q.2⟩
    exact h.jordanRank_eq q j

end TauCeti.IntegralLattice
