import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GammaZeroOneStructure
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange

/-!
# Isomorphism classes of the moduli pairs of `X₀(N)`, `X₁(N)` and `X_{±1}(N)`

Let `F` be a field and `K` an extension of `F` (in the LMFDB a separable or algebraic closure). The
LMFDB describes the non-cuspidal `F`-points of `X₀(N)`, `X₁(N)` and `X_{±1}(N)` as the
`K`-isomorphism classes of pairs `(E, C)`, `(E, P)` and `(E, ±P)`: an elliptic curve `E` over `F`
with an `X₀(N)`-level structure `C`, a Galois-stable cyclic subgroup of `E[N]` of order `N`, an
`X₁(N)`-level structure `P`, a rational point of exact order `N`, or an `X_{±1}(N)`-level structure
`±P`, a point of exact order `N` with `{P, -P}` Galois-stable, as in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GammaZeroOneStructure`. An isomorphism
`(E, C) ≅ (E', C')` over `K` is an isomorphism `E_K ≅ E'_K`, a change of variables `C` over `K`
with `C • E_K = E'_K` (Tau Ceti's `TauCeti.Isogeny.variableChangeIsogeny`; every isomorphism of
elliptic curves is one), mapping `C` onto `C'`, `P` to `P'`, or `P` to `±P'`.

The group `(ℤ/Nℤ)ˣ` acts on the classes of pairs `(E, P)` by `(E, P) ↦ (E, dP)` (LMFDB
`ag.modcurve.x1`). The subgroup `{±1}` acts trivially, as `(E, -P)` is isomorphic to `(E, P)`
through `[-1]`, the change of variables `negVariableChange`, and the map `(E, P) ↦ (E, ⟨P⟩)` to the
classes of pairs `(E, C)` has for fibres exactly the orbits of `(ℤ/Nℤ)ˣ`; it is onto when `F = K`,
so that on these moduli sets over an algebraically closed field `X₀(N)` is the quotient of `X₁(N)`
by `(ℤ/Nℤ)ˣ / {±1}`. The map `(E, P) ↦ (E, ±P)` is injective on isomorphism classes; its
surjectivity (a pair `(E, ±P)` is isomorphic over `K` to a pair `(E', P')` on a quadratic twist `E'`
of `E`) is not proved. The modular curves themselves, and the bijection between their non-cuspidal
points and these classes, are not formalised.

## Main definitions

* `WeierstrassCurve.variableChangeTorsionMap`: the action on `N`-torsion of the isomorphism given by
  a change of variables.
* `WeierstrassCurve.GammaZeroPair` and `WeierstrassCurve.GammaZeroModuli` (LMFDB `modcurve.x0`,
  `ag.modcurve.x0`): the pairs `(E, C)` and their isomorphism classes over `K`.
* `WeierstrassCurve.GammaOnePair` and `WeierstrassCurve.GammaOneModuli` (LMFDB `modcurve.x1`,
  `ag.modcurve.x1`): the pairs `(E, P)` and their isomorphism classes over `K`.
* `WeierstrassCurve.GammaPMOnePair` and `WeierstrassCurve.GammaPMOneModuli` (LMFDB
  `modcurve.xpm1`): the pairs `(E, ±P)` and their isomorphism classes over `K`.
* `WeierstrassCurve.GammaOneModuli.toGammaZeroModuli`,
  `WeierstrassCurve.GammaOneModuli.toGammaPMOneModuli` and
  `WeierstrassCurve.GammaPMOneModuli.toGammaZeroModuli`: the maps `(E, P) ↦ (E, ⟨P⟩)`,
  `(E, P) ↦ (E, ±P)` and `(E, ±P) ↦ (E, ⟨P⟩)`.
* The action of `(ℤ/Nℤ)ˣ` on `WeierstrassCurve.GammaOneModuli`, by `(E, P) ↦ (E, dP)`.

## Main results

* `WeierstrassCurve.GammaOneModuli.neg_one_smul`: `-1` acts trivially.
* `WeierstrassCurve.GammaOneModuli.toGammaZeroModuli_eq_iff`: the fibres of `(E, P) ↦ (E, ⟨P⟩)` are
  the orbits of `(ℤ/Nℤ)ˣ`.
* `WeierstrassCurve.GammaOneModuli.toGammaZeroModuli_surjective`: `(E, P) ↦ (E, ⟨P⟩)` is onto for
  `F = K`.
* `WeierstrassCurve.GammaOneModuli.toGammaPMOneModuli_injective`: `(E, P) ↦ (E, ±P)` is injective on
  isomorphism classes.
-/

open TauCeti Isogeny

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (N : ℕ)

section VariableChange

variable {W W' W'' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic] [W''.IsElliptic]
  {C C' : VariableChange K} (h : C • (W⁄K).toAffine = (W'⁄K).toAffine)
  (h' : C' • (W'⁄K).toAffine = (W''⁄K).toAffine)
  (h'' : (C' * C) • (W⁄K).toAffine = (W''⁄K).toAffine)
  (hinv : C⁻¹ • (W'⁄K).toAffine = (W⁄K).toAffine)
  (h₁ : (1 : VariableChange K) • (W⁄K).toAffine = (W⁄K).toAffine)
  (P : AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ))

/-- The action on the `N`-torsion over `K` of the isomorphism `W_K ≅ W'_K` given by a change of
variables `C` over `K` with `C • W_K = W'_K`: the torsion action of Tau Ceti's
`TauCeti.Isogeny.variableChangeIsogeny`, the substitution `(x, y) ↦ (u⁻²(x - r), …)`. -/
noncomputable def variableChangeTorsionMap :
    AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ) →ₗ[ZMod N]
      AddSubgroup.torsionBy (W'⁄K).toAffine.Point (N : ℤ) :=
  (Hom.ofIsogeny (variableChangeIsogeny C h)).torsionLinearMap N

lemma variableChangeTorsionMap_one : variableChangeTorsionMap N h₁ = LinearMap.id := by
  rw [variableChangeTorsionMap, variableChangeIsogeny_one, ← Hom.id_def, Hom.torsionLinearMap_id]

lemma variableChangeTorsionMap_one_apply : variableChangeTorsionMap N h₁ P = P := by
  rw [variableChangeTorsionMap_one, LinearMap.id_apply]

lemma map_variableChangeTorsionMap_one
    (S : AddSubgroup (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ))) :
    S.map (variableChangeTorsionMap N h₁).toAddMonoidHom = S := by
  rw [variableChangeTorsionMap_one]
  exact S.map_id

lemma variableChangeTorsionMap_comp :
    (variableChangeTorsionMap N h').comp (variableChangeTorsionMap N h) =
      variableChangeTorsionMap N h'' := by
  rw [variableChangeTorsionMap, variableChangeTorsionMap, variableChangeTorsionMap,
    ← Hom.torsionLinearMap_comp, Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_comp]

lemma variableChangeTorsionMap_inv_comp :
    (variableChangeTorsionMap N hinv).comp (variableChangeTorsionMap N h) = LinearMap.id := by
  rw [variableChangeTorsionMap, variableChangeTorsionMap, ← Hom.torsionLinearMap_comp,
    Hom.ofIsogeny_comp_ofIsogeny, variableChangeIsogeny_inv_comp, ← Hom.id_def,
    Hom.torsionLinearMap_id]

lemma variableChangeTorsionMap_inv_apply :
    variableChangeTorsionMap N hinv (variableChangeTorsionMap N h P) = P := by
  rw [← LinearMap.comp_apply, variableChangeTorsionMap_inv_comp, LinearMap.id_apply]

lemma variableChangeTorsionMap_negVariableChange_apply
    (hneg : (W⁄K).toAffine.negVariableChange • (W⁄K).toAffine = (W⁄K).toAffine) :
    variableChangeTorsionMap N hneg P = -P := by
  rw [variableChangeTorsionMap, variableChangeIsogeny_negVariableChange, Hom.ofIsogeny_negIsogeny,
    Hom.torsionLinearMap_neg, Hom.one_def, Hom.torsionLinearMap_id, LinearMap.neg_apply,
    LinearMap.id_apply]

end VariableChange

variable (F K) in
/-- A **pair `(E, C)`** (LMFDB `modcurve.x0`, `ag.modcurve.x0`): an elliptic curve `E` over `F`
with an `X₀(N)`-level structure `C` over `K`, a Galois-stable cyclic subgroup of `E[N]` of order
`N`. -/
structure GammaZeroPair where
  /-- The elliptic curve `E` over `F`. -/
  curve : WeierstrassCurve F
  [isElliptic : curve.IsElliptic]
  /-- The cyclic subgroup `C` of the `N`-torsion of `E` over `K`. -/
  subgroup : AddSubgroup (AddSubgroup.torsionBy (curve⁄K).toAffine.Point (N : ℤ))
  isGammaZeroLevelStructure : curve.IsGammaZeroLevelStructure N subgroup

variable (F K) in
/-- A **pair `(E, P)`** (LMFDB `modcurve.x1`, `ag.modcurve.x1`): an elliptic curve `E` over `F` with
an `X₁(N)`-level structure `P` over `K`, an `F`-rational point of `E[N]` of exact order `N`. -/
structure GammaOnePair where
  /-- The elliptic curve `E` over `F`. -/
  curve : WeierstrassCurve F
  [isElliptic : curve.IsElliptic]
  /-- The point `P` of the `N`-torsion of `E` over `K`. -/
  point : AddSubgroup.torsionBy (curve⁄K).toAffine.Point (N : ℤ)
  isGammaOneLevelStructure : curve.IsGammaOneLevelStructure N point

variable (F K) in
/-- A **pair `(E, ±P)`** (LMFDB `modcurve.xpm1`): an elliptic curve `E` over `F` with an
`X_{±1}(N)`-level structure `±P` over `K`, a point of `E[N]` of exact order `N` such that `{P, -P}`
is Galois-stable; `P` and `-P` give isomorphic pairs (`GammaPMOnePair.IsIso`). -/
structure GammaPMOnePair where
  /-- The elliptic curve `E` over `F`. -/
  curve : WeierstrassCurve F
  [isElliptic : curve.IsElliptic]
  /-- A representative `P` of `±P`, in the `N`-torsion of `E` over `K`. -/
  point : AddSubgroup.torsionBy (curve⁄K).toAffine.Point (N : ℤ)
  isGammaPMOneLevelStructure : curve.IsGammaPMOneLevelStructure N point

attribute [instance] GammaZeroPair.isElliptic GammaOnePair.isElliptic GammaPMOnePair.isElliptic

namespace GammaZeroPair

variable {N} {p q r : GammaZeroPair F K N}

variable (p q) in
/-- Two pairs `(E, C)` and `(E', C')` are **isomorphic over `K`** if a change of variables over `K`
carries `E` to `E'` and `C` onto `C'`. -/
def IsIso : Prop :=
  ∃ (C : VariableChange K) (h : C • (p.curve⁄K).toAffine = (q.curve⁄K).toAffine),
    p.subgroup.map (variableChangeTorsionMap N h).toAddMonoidHom = q.subgroup

variable (p) in
lemma IsIso.refl : p.IsIso p :=
  ⟨1, one_smul _ _, map_variableChangeTorsionMap_one N _ p.subgroup⟩

lemma IsIso.symm (h : p.IsIso q) : q.IsIso p := by
  rcases h with ⟨C, hC, hpq⟩
  refine ⟨C⁻¹, inv_smul_eq_iff.mpr hC.symm, ?_⟩
  rw [← hpq, AddSubgroup.map_map]
  exact (congrArg (fun f ↦ p.subgroup.map (LinearMap.toAddMonoidHom f))
    (variableChangeTorsionMap_inv_comp N hC _)).trans p.subgroup.map_id

lemma IsIso.trans (h₁ : p.IsIso q) (h₂ : q.IsIso r) : p.IsIso r := by
  rcases h₁ with ⟨C, hC, hpq⟩
  rcases h₂ with ⟨C', hC', hqr⟩
  refine ⟨C' * C, by rw [mul_smul, hC, hC'], ?_⟩
  rw [← hqr, ← hpq, AddSubgroup.map_map, ← variableChangeTorsionMap_comp N hC hC']
  rfl

variable (F K N) in
/-- Isomorphism over `K` of pairs `(E, C)`, as an equivalence relation. -/
def setoid : Setoid (GammaZeroPair F K N) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

end GammaZeroPair

namespace GammaPMOnePair

variable {N} {p q r : GammaPMOnePair F K N}

variable (p q) in
/-- Two pairs `(E, ±P)` and `(E', ±P')` are **isomorphic over `K`** if a change of variables over
`K` carries `E` to `E'` and `P` to `P'` or to `-P'`. -/
def IsIso : Prop :=
  ∃ (C : VariableChange K) (h : C • (p.curve⁄K).toAffine = (q.curve⁄K).toAffine),
    variableChangeTorsionMap N h p.point = q.point ∨ variableChangeTorsionMap N h p.point = -q.point

variable (p) in
lemma IsIso.refl : p.IsIso p :=
  ⟨1, one_smul _ _, .inl <| variableChangeTorsionMap_one_apply N _ p.point⟩

lemma IsIso.symm (h : p.IsIso q) : q.IsIso p := by
  rcases h with ⟨C, hC, hpq⟩
  refine ⟨C⁻¹, inv_smul_eq_iff.mpr hC.symm, hpq.imp (fun hσ ↦ ?_) fun hσ ↦ ?_⟩
  · rw [← hσ, variableChangeTorsionMap_inv_apply]
  · rw [← neg_neg q.point, ← hσ, map_neg, variableChangeTorsionMap_inv_apply]

lemma IsIso.trans (h₁ : p.IsIso q) (h₂ : q.IsIso r) : p.IsIso r := by
  rcases h₁ with ⟨C, hC, hpq⟩
  rcases h₂ with ⟨C', hC', hqr⟩
  refine ⟨C' * C, by rw [mul_smul, hC, hC'], ?_⟩
  rw [← variableChangeTorsionMap_comp N hC hC', LinearMap.comp_apply]
  rcases hpq with hpq | hpq <;> rcases hqr with hqr | hqr <;> simp [hpq, hqr]

variable (F K N) in
/-- Isomorphism over `K` of pairs `(E, ±P)`, as an equivalence relation. -/
def setoid : Setoid (GammaPMOnePair F K N) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

variable (p) in
/-- The pair `(E, ⟨P⟩)` of a pair `(E, ±P)`. -/
def toGammaZeroPair : GammaZeroPair F K N where
  curve := p.curve
  subgroup := AddSubgroup.zmultiples p.point
  isGammaZeroLevelStructure := p.isGammaPMOneLevelStructure.isGammaZeroLevelStructure

lemma IsIso.toGammaZeroPair (h : p.IsIso q) : p.toGammaZeroPair.IsIso q.toGammaZeroPair := by
  rcases h with ⟨C, hC, hpq⟩
  refine ⟨C, hC, (AddMonoidHom.map_zmultiples _ _).trans ?_⟩
  rcases hpq with hpq | hpq
  · exact congrArg AddSubgroup.zmultiples hpq
  · exact (congrArg AddSubgroup.zmultiples hpq).trans AddSubgroup.zmultiples_neg

end GammaPMOnePair

namespace GammaOnePair

variable {N} {p q r : GammaOnePair F K N}

variable (p q) in
/-- Two pairs `(E, P)` and `(E', P')` are **isomorphic over `K`** if a change of variables over `K`
carries `E` to `E'` and `P` to `P'`. -/
def IsIso : Prop :=
  ∃ (C : VariableChange K) (h : C • (p.curve⁄K).toAffine = (q.curve⁄K).toAffine),
    variableChangeTorsionMap N h p.point = q.point

variable (p) in
lemma IsIso.refl : p.IsIso p :=
  ⟨1, one_smul _ _, variableChangeTorsionMap_one_apply N _ p.point⟩

lemma IsIso.symm (h : p.IsIso q) : q.IsIso p := by
  rcases h with ⟨C, hC, hpq⟩
  refine ⟨C⁻¹, inv_smul_eq_iff.mpr hC.symm, ?_⟩
  rw [← hpq, variableChangeTorsionMap_inv_apply]

lemma IsIso.trans (h₁ : p.IsIso q) (h₂ : q.IsIso r) : p.IsIso r := by
  rcases h₁ with ⟨C, hC, hpq⟩
  rcases h₂ with ⟨C', hC', hqr⟩
  refine ⟨C' * C, by rw [mul_smul, hC, hC'], ?_⟩
  rw [← hqr, ← hpq, ← LinearMap.comp_apply, variableChangeTorsionMap_comp]

variable (F K N) in
/-- Isomorphism over `K` of pairs `(E, P)`, as an equivalence relation. -/
def setoid : Setoid (GammaOnePair F K N) where
  r := IsIso
  iseqv := ⟨IsIso.refl, IsIso.symm, IsIso.trans⟩

variable (p) in
/-- The pair `(E, ±P)` of a pair `(E, P)`. -/
def toGammaPMOnePair : GammaPMOnePair F K N where
  curve := p.curve
  point := p.point
  isGammaPMOneLevelStructure := p.isGammaOneLevelStructure.isGammaPMOneLevelStructure

lemma IsIso.toGammaPMOnePair (h : p.IsIso q) : p.toGammaPMOnePair.IsIso q.toGammaPMOnePair := by
  rcases h with ⟨C, hC, hpq⟩
  exact ⟨C, hC, .inl hpq⟩

variable (p) in
/-- The pair `(E, ⟨P⟩)` of a pair `(E, P)`. -/
def toGammaZeroPair : GammaZeroPair F K N :=
  p.toGammaPMOnePair.toGammaZeroPair

lemma IsIso.toGammaZeroPair (h : p.IsIso q) : p.toGammaZeroPair.IsIso q.toGammaZeroPair :=
  h.toGammaPMOnePair.toGammaZeroPair

noncomputable instance : SMul (ZMod N)ˣ (GammaOnePair F K N) where
  smul d p :=
    { curve := p.curve
      point := d • p.point
      isGammaOneLevelStructure := p.isGammaOneLevelStructure.units_smul d }

lemma IsIso.smul (h : p.IsIso q) (d : (ZMod N)ˣ) : (d • p).IsIso (d • q) := by
  rcases h with ⟨C, hC, hpq⟩
  exact ⟨C, hC, (LinearMap.map_smul_of_tower _ d p.point).trans (congrArg (d • ·) hpq)⟩

end GammaOnePair

variable (F K) in
/-- The **isomorphism classes over `K` of pairs `(E, C)`** (LMFDB `modcurve.x0`, `ag.modcurve.x0`):
for `K` a separable closure of `F`, the set parametrized by the non-cuspidal `F`-points of
`X₀(N)`. -/
abbrev GammaZeroModuli : Type _ :=
  Quotient (GammaZeroPair.setoid F K N)

variable (F K) in
/-- The **isomorphism classes over `K` of pairs `(E, P)`** (LMFDB `modcurve.x1`, `ag.modcurve.x1`):
for `K` a separable closure of `F`, the set parametrized by the non-cuspidal `F`-points of
`X₁(N)`. -/
abbrev GammaOneModuli : Type _ :=
  Quotient (GammaOnePair.setoid F K N)

variable (F K) in
/-- The **isomorphism classes over `K` of pairs `(E, ±P)`** (LMFDB `modcurve.xpm1`): for `K` a
separable closure of `F`, the set parametrized by the non-cuspidal `F`-points of `X_{±1}(N)`. -/
abbrev GammaPMOneModuli : Type _ :=
  Quotient (GammaPMOnePair.setoid F K N)

variable {N}

/-- The map `(E, ±P) ↦ (E, ⟨P⟩)` from the classes of pairs `(E, ±P)` to those of pairs `(E, C)`,
the moduli description of the covering `X_{±1}(N) → X₀(N)`. -/
def GammaPMOneModuli.toGammaZeroModuli : GammaPMOneModuli F K N → GammaZeroModuli F K N :=
  Quotient.map GammaPMOnePair.toGammaZeroPair fun _ _ h ↦ h.toGammaZeroPair

namespace GammaOneModuli

/-- The map `(E, P) ↦ (E, ⟨P⟩)` from the classes of pairs `(E, P)` to those of pairs `(E, C)`, the
moduli description of the covering `X₁(N) → X₀(N)`. -/
def toGammaZeroModuli : GammaOneModuli F K N → GammaZeroModuli F K N :=
  Quotient.map GammaOnePair.toGammaZeroPair fun _ _ h ↦ h.toGammaZeroPair

/-- The map `(E, P) ↦ (E, ±P)` from the classes of pairs `(E, P)` to those of pairs `(E, ±P)`, the
moduli description of the isomorphism `X₁(N) → X_{±1}(N)` of curves, which refines the moduli
problem (LMFDB `modcurve.quadratic_refinements`). -/
def toGammaPMOneModuli : GammaOneModuli F K N → GammaPMOneModuli F K N :=
  Quotient.map GammaOnePair.toGammaPMOnePair fun _ _ h ↦ h.toGammaPMOnePair

lemma toGammaZeroModuli_toGammaPMOneModuli (x : GammaOneModuli F K N) :
    x.toGammaPMOneModuli.toGammaZeroModuli = x.toGammaZeroModuli :=
  Quotient.inductionOn x fun _ ↦ rfl

/-- **For `F = K`, every pair `(E, C)` comes from a pair `(E, P)`**: a generator `P` of `C` has
exact order `N` and is rational, as `K ≃ₐ[K] K` is trivial. For `K` algebraically closed, the
classes of pairs `(E, C)` are thus the quotient of the classes of pairs `(E, P)` by `(ℤ/Nℤ)ˣ`
(`toGammaZeroModuli_eq_iff`), the moduli description of `X₀(N)` as a quotient of `X₁(N)` (LMFDB
`ag.modcurve.x1`). -/
lemma toGammaZeroModuli_surjective :
    (toGammaZeroModuli : GammaOneModuli K K N → GammaZeroModuli K K N).Surjective := by
  intro y
  induction y using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨E, C, hC, hcard, -⟩
    rcases (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC with ⟨P, rfl⟩
    refine ⟨Quotient.mk _ ⟨E, P, (Nat.card_zmultiples P).symm.trans hcard, fun σ ↦ ?_⟩, rfl⟩
    rw [(AlgEquiv.ext fun x ↦ σ.commutes x : σ = 1), map_one]
    rfl

/-- **The map `(E, P) ↦ (E, ±P)` is injective on isomorphism classes**: if `(E, ±P)` and
`(E', ±P')` are isomorphic, so are `(E, P)` and `(E', P')`, composing with `[-1]` on `E'` if the
isomorphism maps `P` to `-P'`. -/
lemma toGammaPMOneModuli_injective :
    (toGammaPMOneModuli : GammaOneModuli F K N → GammaPMOneModuli F K N).Injective := by
  intro x y h
  induction x, y using Quotient.inductionOn₂ with
  | h p q =>
    have h' : p.toGammaPMOnePair.IsIso q.toGammaPMOnePair := Quotient.exact h
    rcases h' with ⟨C, hC, hpq | hpq⟩
    · exact Quotient.sound ⟨C, hC, hpq⟩
    · have hC' : C • (p.curve⁄K).toAffine = (q.curve⁄K).toAffine := hC
      have hpq' : variableChangeTorsionMap N hC' p.point = -q.point := hpq
      have hneg :
          (q.curve⁄K).toAffine.negVariableChange • (q.curve⁄K).toAffine = (q.curve⁄K).toAffine :=
        negVariableChange_smul_self _
      refine Quotient.sound ⟨_, by rw [mul_smul, hC', hneg], ?_⟩
      rw [← variableChangeTorsionMap_comp N hC' hneg, LinearMap.comp_apply, hpq',
        variableChangeTorsionMap_negVariableChange_apply, neg_neg]

noncomputable instance : MulAction (ZMod N)ˣ (GammaOneModuli F K N) where
  smul d := Quotient.map (d • ·) fun _ _ h ↦ h.smul d
  one_smul x := Quotient.inductionOn x fun _ ↦ Quotient.sound
    ⟨1, one_smul _ _, (variableChangeTorsionMap_one_apply N _ _).trans (one_smul _ _)⟩
  mul_smul _ _ x := Quotient.inductionOn x fun _ ↦ Quotient.sound
    ⟨1, one_smul _ _, (variableChangeTorsionMap_one_apply N _ _).trans (mul_smul _ _ _)⟩

lemma smul_mk (d : (ZMod N)ˣ) (p : GammaOnePair F K N) :
    d • (Quotient.mk _ p : GammaOneModuli F K N) = Quotient.mk _ (d • p) :=
  rfl

/-- **`-1` acts trivially on the classes of pairs `(E, P)`**: `(E, -P)` is isomorphic to `(E, P)`
through `[-1]`, the change of variables `negVariableChange`. -/
lemma neg_one_smul (x : GammaOneModuli F K N) : (-1 : (ZMod N)ˣ) • x = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    refine Quotient.sound ⟨_, negVariableChange_smul_self _,
      (variableChangeTorsionMap_negVariableChange_apply N ((-1 : (ZMod N)ˣ) • p.point) _).trans ?_⟩
    rw [Units.neg_smul, one_smul, neg_neg]

variable [NeZero N]

/-- **The fibres of `(E, P) ↦ (E, ⟨P⟩)` are the orbits of `(ℤ/Nℤ)ˣ`**: two classes of pairs
`(E, P)` have the same image in the classes of pairs `(E, C)` if and only if they differ by a unit
of `ℤ/Nℤ`. With `neg_one_smul`, the classes of pairs `(E, C)` arising from pairs `(E, P)` are the
quotient by `(ℤ/Nℤ)ˣ / {±1}`. -/
lemma toGammaZeroModuli_eq_iff (x y : GammaOneModuli F K N) :
    x.toGammaZeroModuli = y.toGammaZeroModuli ↔ ∃ d : (ZMod N)ˣ, x = d • y := by
  induction x, y using Quotient.inductionOn₂ with
  | h p q =>
    refine ⟨fun h ↦ ?_, ?_⟩
    · have h' : p.toGammaZeroPair.IsIso q.toGammaZeroPair := Quotient.exact h
      rcases h' with ⟨C, hC, hpq⟩
      rcases (ZMod.zmultiples_eq_zmultiples_iff q.isGammaOneLevelStructure.1).mp
        ((AddMonoidHom.map_zmultiples _ _).symm.trans hpq) with ⟨d, hd⟩
      exact ⟨d, Quotient.sound ⟨C, hC, hd⟩⟩
    · rintro ⟨d, hd⟩
      rw [hd, smul_mk]
      exact Quotient.sound ⟨1, one_smul _ _, (map_variableChangeTorsionMap_one N _ _).trans <|
        ZMod.zmultiples_smul_of_isUnit d.isUnit⟩

end GammaOneModuli

end WeierstrassCurve
