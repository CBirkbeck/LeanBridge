import TauCeti.AlgebraicGeometry.ModularCurve.FullLevel

/-!
# The full modular curve `Y_full(N)`

Over `ℤ[1/N]`, a full level `N` structure on an elliptic curve `E` over a scheme `S` is an
isomorphism of group schemes `E[N] ≅ (ℤ/Nℤ)²`, or equivalently (Katz–Mazur) a Drinfeld basis of
`E[N]`: these are the level structures of Tau Ceti's moduli problem `[Γ(N)]` over the category
`Ell/ℤ[1/N]` of elliptic curves over `ℤ[1/N]`-schemes. For `N ≥ 3` this moduli problem is
representable by an elliptic curve over a smooth affine `ℤ[1/N]`-scheme, the full modular curve
`Y_full(N)`, which represents the functor sending a `ℤ[1/N]`-algebra `R` to the isomorphism classes
of elliptic curves over `R` with a full level `N` structure.

The existence of `Y_full(N)` is not formalised: we define its data, a representing object of
`[Γ(N)]`, which is unique up to unique isomorphism, and makes `[Γ(N)]` rigid.

## Main definitions

* `FullModularCurve` (LMFDB `modcurve.xn`): the full modular curve of level `N`, as a representing
  object of the moduli problem `[Γ(N)]`.
* `FullModularCurve.scheme`: the scheme `Y_full(N)`.
* `FullModularCurve.iso`: two full modular curves of the same level are isomorphic.

## Main results

* `FullModularCurve.isRigid`: a moduli problem `[Γ(N)]` with a full modular curve is rigid.
-/

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry

variable {N : ℕ} [NeZero N]

variable (N) in
/-- The **full modular curve of level `N`** (LMFDB `modcurve.xn`, first variant), as the data of a
representing object of Tau Ceti's moduli problem `[Γ(N)]` over `Ell/ℤ[1/N]`: an elliptic curve `E`
over a `ℤ[1/N]`-scheme `Y_full(N)` (`FullModularCurve.scheme`) with a full level `N` structure,
from which every elliptic curve with a full level `N` structure over a `ℤ[1/N]`-scheme is pulled
back along a unique arrow of `Ell/ℤ[1/N]`. -/
structure FullModularCurve where
  /-- The universal elliptic curve over `Y_full(N)`, as an object of `Ell/ℤ[1/N]`. -/
  obj : EllObj (Spec (.of (Localization.Away (N : ℤ))))
  /-- The universal elliptic curve represents the moduli problem `[Γ(N)]`. -/
  representableBy :
    (ModuliProblem.gamma (Spec (.of (Localization.Away (N : ℤ)))) N).RepresentableBy obj

namespace FullModularCurve

variable (Y Y' : FullModularCurve N)

/-- The **full modular curve** `Y_full(N)` (LMFDB `modcurve.xn`), the base of the universal
elliptic curve. -/
noncomputable def scheme : Scheme :=
  Y.obj.base

/-- Two full modular curves of level `N` are isomorphic, through the unique isomorphism of their
universal elliptic curves compatible with the universal level structures. -/
noncomputable def iso : Y.obj ≅ Y'.obj :=
  Y.representableBy.uniqueUpToIso Y'.representableBy

include Y in
/-- **A moduli problem `[Γ(N)]` with a full modular curve is rigid**: no automorphism of an
elliptic curve other than the identity fixes a full level `N` structure. -/
lemma isRigid : (ModuliProblem.gamma (Spec (.of (Localization.Away (N : ℤ)))) N).IsRigid :=
  ModuliProblem.isRigid_of_representableBy Y.representableBy

end FullModularCurve
