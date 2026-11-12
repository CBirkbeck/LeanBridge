import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwo
import LeanBridge.ForMathlib.RepresentationTheory.HighestWeightTheorem
import TauCeti.RepresentationTheory.ClassicalGroups.ExtremeShape

/-!
# The irreducible rational representations `ρ_{k,j}` of `GL(2, ℂ)`

Vector-valued Siegel modular forms of degree `2` take their weight among the representations
`ρ_{k,j} = det^k ⊗ Sym^j(St)` of `GL(2, ℂ)`, for `k ∈ ℤ` and `j ≥ 0`
(`SiegelUpperHalfSpace.rhoKJ`, which lets `g` act on `Sym^j(ℂ²)` by `det(g)^k Sym^j(g)`). The LMFDB
knowls `mf.siegel.vector_valued`, `mf.siegel.weight` and `mf.siegel.vector_valued_degree_two` state
that `ρ_{k,j}` is irreducible of highest weight `(j + k, k)` and that the `ρ_{k,j}` are all the
irreducible representations of `GL(2, ℂ)`. The last statement holds for the rational (holomorphic)
representations, which the theorem of the highest weight classifies: `g ↦ |det g|` is irreducible
and not rational.

The proof identifies `ρ_{k,j}` with Tau Ceti's rational Weyl module `V_λ` of the dominant weight
`λ = (j + k, k)`. That module is the twist by `det ^ λ₂ = det ^ k` of the Weyl module of the
one-row Young diagram with `λ₁ - λ₂ = j` boxes, which is the symmetric power `Sym^j(ℂ²)`
(`TauCeti.weylRepOfShapeEquivSymPowerRep`). So `ρ_{k,j}` is irreducible
(`TauCeti.isIrreducible_rationalWeylRep`) of highest weight `λ`
(`Representation.highestWeight_rationalWeylRep`), and by the theorem of the highest weight
(`Representation.nonempty_equiv_rationalWeylRep_iff_eq_highestWeight`) an irreducible rational
representation of `GL(2, ℂ)` is isomorphic to `ρ_{k,j}` exactly when its highest weight is
`(j + k, k)`. Every dominant weight `λ₁ ≥ λ₂` is `(j + k, k)` for exactly one pair, `k = λ₂` and
`j = λ₁ - λ₂`.

## Main definitions

* `SiegelUpperHalfSpace.dominantWeightKJ`: the dominant weight `(j + k, k)` of `GL(2)`.
* `SiegelUpperHalfSpace.tprodEquivRhoKJ`: the isomorphism `det^k ⊗ Sym^j(St) ≅ ρ_{k,j}` from the
  tensor product.

## Main results

* `SiegelUpperHalfSpace.nonempty_equiv_rationalWeylRep_rhoKJ`: `ρ_{k,j} ≅ V_{(j + k, k)}`.
* `SiegelUpperHalfSpace.isRationalRep_rhoKJ`: `ρ_{k,j}` is rational.
* `SiegelUpperHalfSpace.isIrreducible_rhoKJ` (LMFDB `mf.siegel.weight`): `ρ_{k,j}` is irreducible.
* `SiegelUpperHalfSpace.highestWeight_rhoKJ` (LMFDB `mf.siegel.weight`): the highest weight of
  `ρ_{k,j}` is `(j + k, k)`.
* `SiegelUpperHalfSpace.nonempty_equiv_rhoKJ_iff`: an irreducible rational representation of
  `GL(2, ℂ)` is isomorphic to `ρ_{k,j}` exactly when its highest weight is `(j + k, k)`.
* `SiegelUpperHalfSpace.existsUnique_nonempty_equiv_rhoKJ` (LMFDB `mf.siegel.vector_valued`,
  `mf.siegel.vector_valued_degree_two`): every irreducible rational representation of `GL(2, ℂ)` is
  isomorphic to `ρ_{k,j}` for exactly one pair `(k, j)` with `k ∈ ℤ` and `j ∈ ℕ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, Springer, 1991,
  Lecture 6 and §15.5.
* G. van der Geer, *Siegel modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer, 2008.
-/

open TauCeti Matrix Representation DominantWeight

namespace SiegelUpperHalfSpace

variable (k : ℤ) (j : ℕ) {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin 2) ℂ) W} [ρ.IsIrreducible]

/-- The **dominant weight** `(j + k, k)` of `GL(2)`, for `k ∈ ℤ` and `j ∈ ℕ`: the highest weight of
`ρ_{k,j}` (`SiegelUpperHalfSpace.highestWeight_rhoKJ`). -/
def dominantWeightKJ : DominantWeight 2 :=
  ⟨![j + k, k], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all⟩

lemma rhoKJ_eq_charTwist : rhoKJ k j = (symPowerRep ℂ 2 j).charTwist (GeneralLinearGroup.det ^ k) :=
  rfl

lemma card_detShiftShape_dominantWeightKJ : (dominantWeightKJ k j).detShiftShape.card = j := by
  have h : ((dominantWeightKJ k j).detShiftShape.card : ℤ) =
      ∑ i, ((dominantWeightKJ k j).shift (-(dominantWeightKJ k j).detShift)).1 i :=
    natCast_card_shape (isPolynomial_shift_neg_detShift (dominantWeightKJ k j))
  simp [dominantWeightKJ] at h
  exact_mod_cast h

/-- The isomorphism `det^k ⊗ Sym^j(St) ≅ ρ_{k,j}`: the tensor product with the line of `det ^ k`
is the twist of `Sym^j(St)` by `det ^ k`, along `TensorProduct.lid`. -/
noncomputable def tprodEquivRhoKJ :
    ((detPowerRep ℂ 2 k).tprod (symPowerRep ℂ 2 j)).Equiv (rhoKJ k j) := by
  rw [detPowerRep_def]
  exact tprodEquivCharTwist _ _

private lemma nonempty_equiv_charTwist_symPowerRep {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ 1) {d : ℕ}
    (hd : μ.card = d) (χ : GL (Fin 2) ℂ →* ℂˣ) :
    Nonempty (((symPowerRep ℂ 2 d).charTwist χ).Equiv ((weylRepOfShape ℂ 2 μ).charTwist χ)) := by
  subst hd
  let e : (symPowerRep ℂ 2 μ.card).Equiv (weylRepOfShape ℂ 2 μ) :=
    (weylRepOfShapeEquivSymPowerRep ℂ 2 μ hμ).symm
  refine ⟨.mk e.toLinearEquiv fun g ↦ LinearMap.ext fun v ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, charTwist_apply_apply, charTwist_apply_apply,
    map_smul]
  congr 1
  exact IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

/-- **`ρ_{k,j}` is the rational Weyl module `V_{(j + k, k)}`**: the Weyl module of the one-row
Young diagram with `j` boxes is `Sym^j(ℂ²)`, and both sides are twisted by `det ^ k`. -/
lemma nonempty_equiv_rationalWeylRep_rhoKJ :
    Nonempty ((rhoKJ k j).Equiv (rationalWeylRep ℂ 2 (dominantWeightKJ k j))) := by
  rw [rationalWeylRep_def, rhoKJ_eq_charTwist]
  exact nonempty_equiv_charTwist_symPowerRep (colLen_zero_detShiftShape_le_pred _)
    (card_detShiftShape_dominantWeightKJ k j) _

/-- **`ρ_{k,j}` is rational**: it is the twist by `det ^ k` of the polynomial representation
`Sym^j(St)`. -/
lemma isRationalRep_rhoKJ : IsRationalRep (rhoKJ k j) :=
  (isPolynomialRep_symPowerRep 2 j).isRationalRep.charTwist k

/-- **`ρ_{k,j}` is irreducible** (LMFDB `mf.siegel.weight`), as the rational Weyl module
`V_{(j + k, k)}` is. -/
lemma isIrreducible_rhoKJ : (rhoKJ k j).IsIrreducible := by
  rcases nonempty_equiv_rationalWeylRep_rhoKJ k j with ⟨e⟩
  exact isIrreducible_of_linearEquiv e.symm.toLinearEquiv
    (fun g v ↦ IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap g v) inferInstance

instance : (rhoKJ k j).IsIrreducible :=
  isIrreducible_rhoKJ k j

/-- **The highest weight of `ρ_{k,j}` is `(j + k, k)`** (LMFDB `mf.siegel.weight`), that of the
rational Weyl module `V_{(j + k, k)}`. -/
lemma highestWeight_rhoKJ : (rhoKJ k j).highestWeight = ![j + k, k] := by
  rcases nonempty_equiv_rationalWeylRep_rhoKJ k j with ⟨e⟩
  exact (highestWeight_eq_of_equiv e).trans (highestWeight_rationalWeylRep (dominantWeightKJ k j))

variable {k j} in
/-- **An irreducible rational representation of `GL(2, ℂ)` is isomorphic to `ρ_{k,j}` exactly when
its highest weight is `(j + k, k)`**, by the theorem of the highest weight. -/
lemma nonempty_equiv_rhoKJ_iff (h : IsRationalRep ρ) :
    Nonempty (ρ.Equiv (rhoKJ k j)) ↔ ρ.highestWeight = ![j + k, k] := by
  refine ⟨fun ⟨e⟩ ↦ (highestWeight_eq_of_equiv e).trans (highestWeight_rhoKJ k j), fun hρ ↦ ?_⟩
  rcases (nonempty_equiv_rationalWeylRep_iff_eq_highestWeight (dominantWeightKJ k j) h).mpr
    hρ.symm with ⟨e⟩
  rcases nonempty_equiv_rationalWeylRep_rhoKJ k j with ⟨e'⟩
  exact ⟨e.trans e'.symm⟩

/-- **The `ρ_{k,j}` are the irreducible rational representations of `GL(2, ℂ)`**
(LMFDB `mf.siegel.vector_valued`, `mf.siegel.vector_valued_degree_two`): each is isomorphic to
`ρ_{k,j}` for exactly one pair `(k, j)` with `k ∈ ℤ` and `j ∈ ℕ`, namely `k = λ₂` and
`j = λ₁ - λ₂` for its highest weight `(λ₁, λ₂)`. -/
lemma existsUnique_nonempty_equiv_rhoKJ (h : IsRationalRep ρ) :
    ∃! p : ℤ × ℕ, Nonempty (ρ.Equiv (rhoKJ p.1 p.2)) := by
  have : Nontrivial W := IsIrreducible.nontrivial ‹_›
  have hle : ρ.highestWeight 1 ≤ ρ.highestWeight 0 := antitone_highestWeight h (by decide)
  refine ⟨(ρ.highestWeight 1, (ρ.highestWeight 0 - ρ.highestWeight 1).toNat),
    (nonempty_equiv_rhoKJ_iff h).mpr ?_, fun p hp ↦ ?_⟩
  · ext i
    fin_cases i
    · simp
      omega
    · simp
  · have h0 : ρ.highestWeight 0 = p.2 + p.1 := congrFun ((nonempty_equiv_rhoKJ_iff h).mp hp) 0
    have h1 : ρ.highestWeight 1 = p.1 := congrFun ((nonempty_equiv_rhoKJ_iff h).mp hp) 1
    ext
    · simp [h1]
    · simp [h0, h1]

end SiegelUpperHalfSpace
