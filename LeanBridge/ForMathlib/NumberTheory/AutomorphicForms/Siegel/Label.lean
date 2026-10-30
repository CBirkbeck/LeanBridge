import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel

/-!
# Labels of Siegel newforms

The LMFDB labels a newform `f ∈ S_k^new(Γ_F(N), χ)` by `g.F.N.k₁…k_d.a.x`: `g` is the degree, `F`
is the family of the group `Γ_F(N)` (principal congruence subgroups `Γ(N)`, Siegel parabolic
subgroups `Γ₀(N)` or paramodular groups), `N` is the level, `k = (k₁, …, k_d)` is the weight, `N.a`
is the label of the Galois orbit of the Dirichlet character `χ` of modulus `N`, and `x` is the label
of the Galois orbit of `f`. Each embedding of the coefficient field of `f` into `ℂ` gives a form
labelled `g.F.N.k₁…k_d.a.x.n.i`, where `N.n` is the Conrey label of its character and `i`
distinguishes the embeddings with the same character.

The label `x` follows an ordering of the Galois orbits of Siegel newforms that the knowl does not
specify (it links to a knowl `mf.siegel.hecke_galois_orbit` that does not exist), and `i` follows
an LMFDB ordering of the embeddings: they are database numberings, with nothing to formalise in
them. The Conrey index `n` is a mathematical function of the character, but Conrey labels are not
available in the pinned Tau Ceti, so it is not formalised; nor are Siegel newforms, outside the
spaces of forms. The mathematically defined part `g.F.N.k₁…k_d.a` of the label depends only on the
space `S_k^new(Γ_F(N), χ)` that contains `f`, and on `χ` only through its Galois orbit: the letters
`a` encode the orbit index of `χ` (`DirichletCharacter.galoisOrbitIndex`), which determines the
orbit (`SiegelUpperHalfSpace.newformLabel_eq_newformLabel_iff`). The knowl does not say how the
families are written in the label, so the family is recorded as such.

In degree `2`, the weight `(k, j)` is that of the representation `det^k ⊗ Sym^j`
(`SiegelUpperHalfSpace.rhoKJ`), and the groups of the three families are `Γ(N)`, `Γ₀(N)` and the
paramodular groups `K(N) = Γ^para(1, N)` (`SiegelUpperHalfSpace.Family.degreeTwoGroup`).

## Main definitions

* `SiegelUpperHalfSpace.Family` (LMFDB `mf.siegel.family`, `mf.siegel.label`): the families.
* `SiegelUpperHalfSpace.Family.degreeTwoGroup`: the group `Γ_F(N)` of a family in degree `2`.
* `SiegelUpperHalfSpace.NewformLabel` (LMFDB `mf.siegel.label`): the mathematically defined part
  of the label of a Siegel newform.
* `SiegelUpperHalfSpace.newformLabel` (LMFDB `mf.siegel.label`): that of a newform in
  `S_k^new(Γ_F(N), χ)`.

## Main results

* `SiegelUpperHalfSpace.newformLabel_eq_newformLabel_iff`: for the same degree, family, level and
  weight, two characters give the same label exactly when they lie in one Galois orbit.
-/

open Matrix

namespace SiegelUpperHalfSpace

/-- The **families** (LMFDB `mf.siegel.family`) of discrete subgroups `Γ_F(N)` of `Sp(2g, ℚ)` on
which the LMFDB's Siegel modular forms live, the entry `F` of their labels (LMFDB
`mf.siegel.label`). -/
inductive Family
  /-- The principal congruence subgroups `Γ(N)` (`SymplecticGroup.Gamma`). -/
  | principalCongruence
  /-- The Siegel parabolic subgroups `Γ₀(N)` (`SymplecticGroup.Gamma0`). -/
  | siegelParabolic
  /-- The paramodular groups (`SymplecticGroup.paramodular`), `K(N)` in degree `2`. -/
  | paramodular

/-- The group `Γ_F(N)` of a family `F` in degree `2` and level `N`, inside `Sp(4, ℚ)`: the principal
congruence subgroup `Γ(N)`, the Siegel parabolic subgroup `Γ₀(N)` or the paramodular group
`K(N) = Γ^para(1, N)`, the groups of degree `2` and level `N` of the LMFDB (LMFDB
`mf.siegel.level`). -/
def Family.degreeTwoGroup : Family → ℕ+ → Subgroup (symplecticGroup (Fin 2) ℚ)
  | principalCongruence, N =>
    (SymplecticGroup.Gamma (Fin 2) N).map (SymplecticGroup.map (Int.castRingHom ℚ))
  | siegelParabolic, N =>
    (SymplecticGroup.Gamma0 (Fin 2) N).map (SymplecticGroup.map (Int.castRingHom ℚ))
  | paramodular, N => SymplecticGroup.paramodular ![1, N]

/-- The mathematically defined part `g.F.N.k₁…k_d.a` of the **label** `g.F.N.k₁…k_d.a.x` (LMFDB
`mf.siegel.label`) of a Siegel newform `f ∈ S_k^new(Γ_F(N), χ)`. The label `x` of the Galois orbit
of `f` is a database numbering. -/
structure NewformLabel where
  /-- The degree `g`. -/
  degree : ℕ
  /-- The family `F` of the group `Γ_F(N)`. -/
  family : Family
  /-- The level `N`. -/
  level : ℕ
  /-- The weight `k = (k₁, …, k_d)`. -/
  weight : List ℕ
  /-- The orbit index of the Galois orbit of `χ`, written `a` in the label `N.a` of the orbit. -/
  characterOrbitIndex : ℕ

variable (g : ℕ) (F : Family) (N : ℕ) (k : List ℕ) (χ ψ : DirichletCharacter ℂ N)

/-- The mathematically defined part `g.F.N.k₁…k_d.a` of the **label** `g.F.N.k₁…k_d.a.x` (LMFDB
`mf.siegel.label`) of a Siegel newform of degree `g` in `S_k^new(Γ_F(N), χ)`: the degree, the
family, the level, the weight and the orbit index of `χ`, whose letter code is the entry `a` of the
label `N.a = χ.galoisOrbitLabel` of the Galois orbit of `χ`. -/
noncomputable def newformLabel : NewformLabel where
  degree := g
  family := F
  level := N
  weight := k
  characterOrbitIndex := χ.galoisOrbitIndex

variable [NeZero N] in
/-- **The label determines the Galois orbit of the character**: for the same degree, family, level
and weight, the characters `ψ` and `χ` give the same label exactly when they are Galois conjugate,
so that the Galois conjugates of a newform share the part `g.F.N.k₁…k_d.a` of their labels. -/
lemma newformLabel_eq_newformLabel_iff :
    newformLabel g F N k ψ = newformLabel g F N k χ ↔ ψ ∈ χ.galoisOrbit := by
  simp [newformLabel, DirichletCharacter.galoisOrbitIndex_eq_iff]

end SiegelUpperHalfSpace
