import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The modular form associated to an elliptic curve over `ℚ`

For every elliptic curve `E` over `ℚ` of conductor `N` there is a unique newform `f` of weight `2`
for `Γ₀(N)` with the same L-function as `E` (LMFDB `ec.q.modular_form`): its Fourier coefficients
`aₙ(f)` are the Dirichlet coefficients `aₙ(E)` of the L-function of `E`. Existence is the
modularity theorem of Wiles, Taylor–Wiles and Breuil–Conrad–Diamond–Taylor, which is not
formalised; this file defines the relation and proves the uniqueness.

A newform for `Γ₀(N)` is a newform of Tau Ceti (`HeckeRing.GL2.Newform`, of level `Γ₁(N)`) with
trivial nebentypus, the L-function of `E` is Mathlib's formal L-function
`WeierstrassCurve.LFunction`, and the conductor `N` is the norm of Tau Ceti's algorithmic conductor
`WeierstrassCurve.algorithmicConductor`, which is the conductor by Ogg's formula, an
identification not formalised there.

## Main definitions

* `WeierstrassCurve.IsAssociatedNewform` (LMFDB `ec.q.modular_form`): a newform is the modular form
  associated to `E`.
* `WeierstrassCurve.IsModular` (LMFDB `ec.q.modular_form`): `E` has an associated newform.

## Main results

* `WeierstrassCurve.IsAssociatedNewform.eq`: an elliptic curve over `ℚ` has at most one associated
  newform.
-/

open HeckeRing GL2 TauCeti UpperHalfPlane

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] {M : ℕ} [NeZero M]

/-- A newform `f` of level `M` and weight `2` is the **modular form associated to** an elliptic
curve `E` over `ℚ` (LMFDB `ec.q.modular_form`) if it is a newform for `Γ₀(N)`, where `N` is the
conductor of `E`: its level `M` is `N` and its nebentypus is trivial; and it has the same
L-function as `E`: its Fourier coefficients `aₙ(f)` are the Dirichlet coefficients `aₙ(E)` of the
L-function `WeierstrassCurve.LFunction` of `E`. Both sides vanish at `n = 0`, so this is the
equality of the L-series `∑ aₙ n ^ (-s)`. By the modularity theorem such a newform exists (it is
not proved here), and it is unique (`IsAssociatedNewform.eq`). -/
def IsAssociatedNewform (f : Newform M 2) : Prop :=
  M = Ideal.absNorm (algorithmicConductor ℤ E) ∧ f.χ = 1 ∧
    ∀ n, (qExpansion 1 f.toCuspForm).coeff n = E.LFunction n

/-- An elliptic curve `E` over `ℚ` is **modular** (LMFDB `ec.q.modular_form`) if it has an
associated newform: a newform of weight `2` for `Γ₀(N)`, `N` the conductor of `E`, with the same
L-function as `E`. By the modularity theorem of Wiles, Taylor–Wiles and
Breuil–Conrad–Diamond–Taylor every elliptic curve over `ℚ` is modular; that theorem is not proved
here. -/
def IsModular : Prop :=
  ∃ (N : ℕ) (_ : NeZero N) (f : Newform N 2), E.IsAssociatedNewform f

variable {E} {f g : Newform M 2}

lemma IsAssociatedNewform.level_eq (hf : E.IsAssociatedNewform f) :
    M = Ideal.absNorm (algorithmicConductor ℤ E) :=
  hf.1

lemma IsAssociatedNewform.χ_eq_one (hf : E.IsAssociatedNewform f) : f.χ = 1 :=
  hf.2.1

lemma IsAssociatedNewform.qExpansion_coeff (hf : E.IsAssociatedNewform f) (n : ℕ) :
    (qExpansion 1 f.toCuspForm).coeff n = E.LFunction n :=
  hf.2.2 n

lemma IsAssociatedNewform.isModular (hf : E.IsAssociatedNewform f) : E.IsModular :=
  ⟨M, inferInstance, f, hf⟩

/-- **An elliptic curve over `ℚ` has at most one associated newform**: two newforms with the
L-function of `E` have the same `q`-expansion, and a cusp form is determined by its
`q`-expansion. -/
lemma IsAssociatedNewform.eq (hf : E.IsAssociatedNewform f) (hg : E.IsAssociatedNewform g) :
    f = g :=
  Newform.ext <| CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map M) <|
    PowerSeries.ext fun n ↦ (hf.qExpansion_coeff n).trans (hg.qExpansion_coeff n).symm

end WeierstrassCurve
