import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Class

/-!
# The isogeny graph of an isogeny class

The isogeny graph of the isogeny class of an elliptic curve `W` over a field `K` has the
isomorphism classes in the isogeny class as vertices, and an edge labelled by a prime `ℓ` between
two vertices for the isogenies of degree `ℓ` between them. Several edges may join two vertices,
with different labels, so the graph is a quiver: the arrows from `c` to `c'` are the primes `ℓ`
such that there is an isogeny of degree `ℓ` from a curve in `c` to a curve in `c'`. The dual of such
an isogeny is an isogeny of degree `ℓ` back, so every arrow has a reverse with the same label, and
the quiver is an undirected multigraph (`Quiver.HasInvolutiveReverse`).

The LMFDB labels the vertices by the last component of the LMFDB labels of the curves; here they
are the isomorphism classes themselves.

## Main definitions

* `WeierstrassCurve.IsomorphismClass.HasIsogenyOfDegree`: there is an isogeny of a given degree
  from a curve in one isomorphism class to a curve in another.
* `WeierstrassCurve.IsogenyGraph` (LMFDB `ec.isogeny_graph`): the isogeny graph, as a quiver on the
  isogeny class with involutive reversal of arrows.

## Main results

* `WeierstrassCurve.IsomorphismClass.mk_hasIsogenyOfDegree_iff`: the isogenies between two
  isomorphism classes are those between any curves in them, up to isomorphism.
* `WeierstrassCurve.IsomorphismClass.HasIsogenyOfDegree.symm`: between elliptic curves, an isogeny
  of degree `n` gives an isogeny of degree `n` back, the dual isogeny.
-/

open TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W : WeierstrassCurve K} {n : ℕ} {c c' : IsomorphismClass K}

namespace IsomorphismClass

variable (n c c') in
/-- There is an isogeny of degree `n` over `K` from a Weierstrass curve in the isomorphism class
`c` to a Weierstrass curve in the isomorphism class `c'`. -/
def HasIsogenyOfDegree : Prop :=
  ∃ W₁ W₂ : WeierstrassCurve K, ⟦W₁⟧ = c ∧ ⟦W₂⟧ = c' ∧ ∃ φ : Isogeny W₁.toAffine W₂.toAffine,
    φ.degree = n

/-- **The isogenies between two isomorphism classes are those between any of their curves**, up
to composing with isomorphisms, which keeps the degree. -/
lemma mk_hasIsogenyOfDegree_iff {W₁ W₂ : WeierstrassCurve K} :
    HasIsogenyOfDegree n ⟦W₁⟧ ⟦W₂⟧ ↔ ∃ φ : Isogeny W₁.toAffine W₂.toAffine, φ.degree = n := by
  refine ⟨?_, fun ⟨φ, hn⟩ ↦ ⟨W₁, W₂, rfl, rfl, φ, hn⟩⟩
  rintro ⟨V₁, V₂, h₁, h₂, φ, rfl⟩
  rcases mk_eq_mk_iff.mp h₁ with ⟨C₁, rfl⟩
  rcases mk_eq_mk_iff.mp h₂.symm with ⟨C₂, rfl⟩
  exact ⟨(Isogeny.variableChangeIsogeny C₂ rfl).comp
    (φ.comp (Isogeny.variableChangeIsogeny C₁ rfl)), by simp⟩

/-- **The dual of an isogeny of degree `n` between curves of the isogeny class of `W` is an
isogeny of degree `n` back.** -/
lemma HasIsogenyOfDegree.symm (hc : c ∈ W.isogenyClass) (hc' : c' ∈ W.isogenyClass)
    (h : HasIsogenyOfDegree n c c') : HasIsogenyOfDegree n c' c := by
  rcases h with ⟨W₁, W₂, rfl, rfl, φ, rfl⟩
  have : W₁.IsElliptic := isElliptic_of_mk_mem_isogenyClass hc
  have : W₂.IsElliptic := isElliptic_of_mk_mem_isogenyClass hc'
  exact ⟨W₂, W₁, rfl, rfl, φ.dual, φ.degree_dual⟩

end IsomorphismClass

variable (W) in
/-- The **isogeny graph** (LMFDB `ec.isogeny_graph`) of an elliptic curve `W` over `K`: its vertices
are the isomorphism classes in the isogeny class of `W`, and its edges are labelled by primes. It
is a quiver: the arrows from `c` to `c'` are the primes `ℓ` such that there is an isogeny of degree
`ℓ` over `K` from a curve in `c` to a curve in `c'`. Its reversal of arrows, which keeps the label
by taking dual isogenies, is involutive, so it is an undirected multigraph. -/
def IsogenyGraph : Type _ :=
  W.isogenyClass

instance : Quiver W.IsogenyGraph where
  Hom c c' := {ℓ : ℕ // ℓ.Prime ∧ c.1.HasIsogenyOfDegree ℓ c'.1}

instance : Quiver.HasInvolutiveReverse W.IsogenyGraph where
  reverse' {c c'} ℓ := ⟨ℓ.1, ℓ.2.1, ℓ.2.2.symm c.2 c'.2⟩
  inv' _ := rfl

end WeierstrassCurve
