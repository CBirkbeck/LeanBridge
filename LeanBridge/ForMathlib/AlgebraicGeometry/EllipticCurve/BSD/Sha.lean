import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.EmbeddingIndependence

/-!
# The Tate–Shafarevich group of an elliptic curve over a number field

The Tate–Shafarevich group `Ш(E / K)` of a Weierstrass curve `E` over a number field `K` is the
kernel of the restriction maps `H¹(G_K, E) → ∏ᵥ H¹(G_{K_v}, E)`, over all the places `v` of `K`,
finite and infinite, where `K_v` is the completion of `K` at `v`. It is Tau Ceti's
`WeierstrassCurve.shafarevichTateGroup` relative to a family of extensions, for the completions of
`K` at its finite places and at its infinite places. The restriction maps involve a choice of
embeddings of separable closures, on which the group does not depend.

## Main definitions

* `WeierstrassCurve.sha` (LMFDB `ec.analytic_sha_order`): the Tate–Shafarevich group `Ш(E / K)`.

## Main results

* `WeierstrassCurve.mem_sha_iff`: a class lies in `Ш(E / K)` exactly when its restrictions to all
  the completions of `K` vanish, for any choice of embeddings of separable closures.
-/

open IsDedekindDomain NumberField TauCeti TauCeti.ContCohomology

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The **Tate–Shafarevich group** `Ш(E / K)` (LMFDB `ec.analytic_sha_order`) of a Weierstrass curve
over a number field `K`: the classes in `H¹(G_K, E(Kˢ))` whose restriction to
`H¹(G_{K_v}, E(K_vˢ))` vanishes for every place `v` of `K`, finite or infinite, where `K_v` is the
completion of `K` at `v`. The restrictions are taken along embeddings `Kˢ → K_vˢ` of separable
closures, whose choice does not matter (`mem_sha_iff`). Its order `#Ш` is
`Nat.card W.sha`, which takes the junk value `0` if `Ш` is infinite. -/
noncomputable def sha : AddSubgroup (H1 (AbsoluteGaloisGroup K) W.PointCoeff) :=
  W.shafarevichTateGroup (L := fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun _ ↦ IsSepClosed.lift) ⊓
    W.shafarevichTateGroup (L := fun v : InfinitePlace K ↦ v.Completion) fun _ ↦ IsSepClosed.lift

/-- A class lies in the Tate–Shafarevich group exactly when its restrictions to the completions of
`K` at all its finite and infinite places vanish, for any choice of embeddings of separable
closures. -/
lemma mem_sha_iff (τ : ∀ v : HeightOneSpectrum (𝓞 K), SeparableClosure K →ₐ[K] SeparableClosure
    (v.adicCompletion K))
    (σ : ∀ v : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion)
    {c : H1 (AbsoluteGaloisGroup K) W.PointCoeff} :
    c ∈ W.sha ↔ (∀ v, W.pointRes (τ v) c = 0) ∧ ∀ v, W.pointRes (σ v) c = 0 := by
  rw [sha, AddSubgroup.mem_inf, W.shafarevichTateGroup_eq_shafarevichTateGroup _ τ,
    W.shafarevichTateGroup_eq_shafarevichTateGroup _ σ, mem_shafarevichTateGroup_iff,
    mem_shafarevichTateGroup_iff]

end WeierstrassCurve
