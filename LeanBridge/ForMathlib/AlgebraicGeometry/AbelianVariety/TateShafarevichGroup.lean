import LeanBridge.ForMathlib.AlgebraicGeometry.AbelianVariety.SelmerGroup

/-!
# The Tate–Shafarevich group of an abelian variety, and whether its order is a square

The Tate–Shafarevich group `Ш(A / K)` of an abelian variety `A` over a number field `K` (LMFDB
`ag.tate_shafarevich`) is the kernel of the restriction maps `H¹(G_K, A) → ∏ᵥ H¹(G_{K_v}, A)`, over
all the places `v` of `K`, finite and infinite, where `K_v` is the completion of `K` at `v`. Here
`H¹(G_L, A)` is the Galois cohomology of the discrete module `A(Lˢ)` over the absolute Galois group
`G_L` (`TauCeti.AlgebraicGeometry.AbelianVariety.PointCoeff`), and the restriction maps are taken
along embeddings `Kˢ → K_vˢ` of separable closures, on which they do not depend. That `Ш(A / K)` is
a torsion group, conjecturally finite, is not formalised.

By a theorem of Poonen and Stoll, the order of the Tate–Shafarevich group of the Jacobian of a
curve, when it is finite, is either a square or twice a square. Only squares occur for elliptic
curves, but both cases occur for the Jacobians of genus `2` curves, and the LMFDB records which one
holds (LMFDB `g2c.has_square_sha`), assuming the group finite. The Jacobian `J` of a curve `X` is
the abelian variety with `J.IsJacobian X` (`TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian`);
its existence is not formalised, and the property is stated for every abelian variety. Neither the
theorem of Poonen and Stoll nor that for elliptic curves (Cassels) is formalised.

## Main definitions

* `TauCeti.AlgebraicGeometry.AbelianVariety.pointRes`: the restriction
  `H¹(G_K, A(Kˢ)) → H¹(G_L, A(Lˢ))` along an embedding `Kˢ → Lˢ`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.tateShafarevichGroup` (LMFDB `ag.tate_shafarevich`):
  the Tate–Shafarevich group `Ш(A / K)`.
* `TauCeti.AlgebraicGeometry.AbelianVariety.HasSquareSha` (LMFDB `g2c.has_square_sha`): `Ш(A / K)`
  is finite, of square order.

## Main results

* `TauCeti.AlgebraicGeometry.AbelianVariety.pointRes_eq_pointRes`: the restriction does not depend
  on the embedding of separable closures.
* `TauCeti.AlgebraicGeometry.AbelianVariety.mem_tateShafarevichGroup_iff`: a class lies in
  `Ш(A / K)` exactly when its restrictions to all the completions of `K` vanish, for any choice of
  embeddings of separable closures.
-/

open IsDedekindDomain NumberField TauCeti ContCohomology

universe u

namespace TauCeti.AlgebraicGeometry.AbelianVariety

variable {K : Type u} [Field K] (A : AbelianVariety K) {L : Type u} [Field L] [Algebra K L]
  (τ τ' : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- The **restriction** `H¹(G_K, A(Kˢ)) → H¹(G_L, A(Lˢ))` along a `K`-embedding `τ : Kˢ → Lˢ` of
separable closures, for a field extension `L` of `K`: the pullback along the map `G_L → G_K` and the
map `A(Kˢ) → A(Lˢ)` given by `τ`. It does not depend on `τ` (`pointRes_eq_pointRes`). -/
noncomputable def pointRes :
    H1 (AbsoluteGaloisGroup K) (A.PointCoeff K) →+ H1 (AbsoluteGaloisGroup L) (A.PointCoeff L) :=
  explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (A.pointCoeffMap τ) continuous_of_discreteTopology
    (A.pointCoeffMap_smul τ)

/-- **The restriction `H¹(G_K, A) → H¹(G_L, A)` does not depend on the embedding of separable
closures**: two embeddings differ by an element of `G_K`, which acts trivially on cohomology. -/
lemma pointRes_eq_pointRes : A.pointRes τ = A.pointRes τ' :=
  explicitMap1_absoluteGaloisGroupMap_eq (N := A.PointCoeff L) A.pointCoeffMap A.pointCoeffMap_smul
    A.pointCoeffMap_comp τ τ'

variable [NumberField K]

/-- The **Tate–Shafarevich group** `Ш(A / K)` (LMFDB `ag.tate_shafarevich`) of an abelian variety
`A` over a number field `K`: the classes in `H¹(G_K, A(Kˢ))` whose restriction to
`H¹(G_{K_v}, A(K_vˢ))` vanishes for every place `v` of `K`, finite or infinite, where `K_v` is the
completion of `K` at `v`. The restrictions are taken along embeddings `Kˢ → K_vˢ` of separable
closures, whose choice does not matter (`mem_tateShafarevichGroup_iff`). -/
noncomputable def tateShafarevichGroup :
    AddSubgroup (H1 (AbsoluteGaloisGroup K) (A.PointCoeff K)) :=
  (⨅ v : HeightOneSpectrum (𝓞 K), (A.pointRes (L := v.adicCompletion K) IsSepClosed.lift).ker) ⊓
    ⨅ v : InfinitePlace K, (A.pointRes (L := v.Completion) IsSepClosed.lift).ker

/-- **A class lies in the Tate–Shafarevich group exactly when its restrictions to all the
completions vanish**, for any choice of embeddings of separable closures. -/
lemma mem_tateShafarevichGroup_iff (ρ : ∀ v : HeightOneSpectrum (𝓞 K), SeparableClosure K →ₐ[K]
    SeparableClosure (v.adicCompletion K)) (ρ' : ∀ v : InfinitePlace K, SeparableClosure K →ₐ[K]
    SeparableClosure v.Completion) {c : H1 (AbsoluteGaloisGroup K) (A.PointCoeff K)} :
    c ∈ A.tateShafarevichGroup ↔ (∀ v, A.pointRes (ρ v) c = 0) ∧ ∀ v, A.pointRes (ρ' v) c = 0 := by
  simp only [tateShafarevichGroup, AddSubgroup.mem_inf, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker,
    A.pointRes_eq_pointRes _ (ρ _), A.pointRes_eq_pointRes _ (ρ' _)]

/-- An abelian variety `A` over a number field `K` **has square Ш** (LMFDB `g2c.has_square_sha`) if
its Tate–Shafarevich group `Ш(A / K)` (`tateShafarevichGroup`) is finite, of square order. The
LMFDB records this for the Jacobian `J` of a genus `2` curve `X` over `ℚ`, an abelian surface with
`J.IsJacobian X` (`TauCeti.AlgebraicGeometry.AbelianVariety.IsJacobian`), assuming, as the knowl
does, that `Ш(J / ℚ)` is finite, as it is conjectured to be. The finiteness is part of the
definition, so that an infinite `Ш(A / K)`, which has no order, does not count as square (its
`Nat.card` is the junk value `0`). By a theorem of Poonen and Stoll (not formalised), a finite
`Ш(J / K)` of the Jacobian `J` of a curve has the order of a square or twice a square. -/
def HasSquareSha : Prop :=
  Finite A.tateShafarevichGroup ∧ IsSquare (Nat.card A.tateShafarevichGroup)

end TauCeti.AlgebraicGeometry.AbelianVariety
