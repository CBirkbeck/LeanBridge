import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.Hyperelliptic

/-!
# Gonality of a curve

The gonality, or `k`-gonality, of an integral algebraic curve `X` over a field `k` is the minimal
degree of a dominant `k`-morphism `X → ℙ¹_k`. Equivalently, it is the minimum of `[k(X) : k(t)]` as
`t` ranges over the elements of the function field `k(X)` transcendental over `k`, and this is how
it is defined here: first for a field extension `F / k` (Tau Ceti's algebraic function fields
`TauCeti.IsFunctionField` being the case of interest), then for a scheme over `k` through its
function field. The geometric gonality, or `k̄`-gonality, is the gonality of the base change `X_k̄`
to an algebraic closure `k̄` of `k`.

The correspondence between dominant morphisms to `ℙ¹` and transcendental rational functions (a
standard fact about curves) is not formalised, nor is the inequality between the geometric gonality
and the `k`-gonality, which needs `[k̄(X_k̄) : k̄(t)] = [k(X) : k(t)]` for `t ∈ k(X)`.

## Main definitions

* `TauCeti.gonality` (LMFDB `ag.gonality`): the gonality of a field extension `F / k`.
* `AlgebraicGeometry.Scheme.gonality` (LMFDB `ag.gonality`): the `k`-gonality of a curve.
* `AlgebraicGeometry.Scheme.geometricGonality` (LMFDB `ag.gonality_geom`): the geometric gonality
  of a curve.

## Main results

* `TauCeti.IsFunctionField.exists_finrank_eq_gonality`: the gonality of an algebraic function field
  is attained.
* `TauCeti.IsFunctionField.gonality_pos`: the gonality of an algebraic function field is positive.
* `TauCeti.IsHyperellipticFunctionField.gonality_le_two`: a hyperelliptic function field has
  gonality at most two.
* `AlgebraicGeometry.Scheme.IsHyperellipticCurveOver.geometricGonality_le_two`: a hyperelliptic
  curve has geometric gonality at most two.
-/

open scoped IntermediateField

namespace TauCeti

variable (k F : Type*) [Field k] [Field F] [Algebra k F]

/-- The **gonality** (LMFDB `ag.gonality`) of a field extension `F / k`, such as the function field
`k(X)` of an integral curve `X` over `k`: the minimum of the degrees `[F : k(t)]` over the elements
`t ∈ F` transcendental over `k` with `F / k(t)` finite. For an algebraic function field of one
variable, every such `F / k(t)` is finite and the minimum exists; when there is no such `t`, the
gonality is `0` by convention. -/
noncomputable def gonality : ℕ :=
  sInf {n | ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F ∧ Module.finrank k⟮t⟯ F = n}

variable {k F}

lemma gonality_le {t : F} (ht : Transcendental k t) (hF : FiniteDimensional k⟮t⟯ F) :
    gonality k F ≤ Module.finrank k⟮t⟯ F :=
  Nat.sInf_le ⟨t, ht, hF, rfl⟩

/-- **The gonality of an algebraic function field is attained** by some transcendental `t`. -/
lemma IsFunctionField.exists_finrank_eq_gonality (hF : IsFunctionField k F) : ∃ t : F,
    Transcendental k t ∧ FiniteDimensional k⟮t⟯ F ∧ Module.finrank k⟮t⟯ F = gonality k F := by
  rcases hF with ⟨t, ht, hft⟩
  exact Nat.sInf_mem (s := {n | ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F ∧
    Module.finrank k⟮t⟯ F = n}) ⟨_, t, ht, hft, rfl⟩

/-- **The gonality of an algebraic function field is positive.** -/
lemma IsFunctionField.gonality_pos (hF : IsFunctionField k F) : 0 < gonality k F := by
  rcases hF.exists_finrank_eq_gonality with ⟨t, -, hft, ht⟩
  exact ht ▸ Module.finrank_pos

/-- **A hyperelliptic function field has gonality at most two.** -/
lemma IsHyperellipticFunctionField.gonality_le_two (hF : IsHyperellipticFunctionField k F) :
    gonality k F ≤ 2 := by
  rcases hF.exists_separable_finrank_adjoin_eq_two with ⟨t, ht, h2, -⟩
  exact h2 ▸ gonality_le ht (Module.finite_of_finrank_eq_succ h2)

end TauCeti

namespace AlgebraicGeometry.Scheme

universe u

variable (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- The **gonality**, or **`K`-gonality** (LMFDB `ag.gonality`), of an integral curve `X` over `K`:
the minimum of `[K(X) : K(t)]` over the rational functions `t ∈ K(X)` transcendental over `K`,
equivalently the minimal degree of a dominant `K`-morphism `X → ℙ¹_K`. -/
noncomputable def gonality [IsIntegral X] : ℕ :=
  TauCeti.gonality K X.functionField

/-- The **geometric gonality**, or **`K̄`-gonality** (LMFDB `ag.gonality_geom`), of a variety `X`
over `K`, such as a geometrically integral curve: the gonality of its base change `X_K̄` to the
algebraic closure `K̄` of `K`, the minimal degree of a dominant morphism `X_K̄ → ℙ¹_K̄`. -/
noncomputable def geometricGonality [X.IsVarietyOver K] : ℕ :=
  (X.geometricBaseChange K).left.gonality (AlgebraicClosure K)

variable {K X}

/-- **A hyperelliptic curve has geometric gonality at most two.** -/
lemma IsHyperellipticCurveOver.geometricGonality_le_two [X.IsHyperellipticCurveOver K] :
    X.geometricGonality K ≤ 2 :=
  IsHyperellipticCurveOver.isHyperellipticFunctionField.gonality_le_two

end AlgebraicGeometry.Scheme
