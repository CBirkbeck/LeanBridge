import TauCeti.LinearAlgebra.IntegralLattice.Examples
import TauCeti.NumberTheory.IntegralLattice.Neighbor

/-!
# Kneser neighbours are neither reflexive nor transitive

Two integral lattices `L` and `M` on the same rational quadratic space are `p`-neighbours (LMFDB
`lattice.pneighbor`, Tau Ceti's `TauCeti.IntegralLattice.IsNeighbor`) when their intersection has
index `p` in each of them, `[L : L ∩ M] = [M : L ∩ M] = p`. Tau Ceti proves that the relation is
symmetric (`TauCeti.IntegralLattice.IsNeighbor.symm`), and that neighbours lie in one genus when
`p` is prime to `2 det L` (`TauCeti.IntegralLattice.IsNeighbor.sameGenus`). This file proves the
knowl's remaining claim, that the relation is in general neither reflexive nor transitive.

A lattice is its own `p`-neighbour only for `p = 1`, as `L ∩ L = L` has index `1` in `L`. And for
every `p ≠ 0` the hyperbolic plane `L = ℤe₀ ⊕ ℤe₁` on `ℚ²`, with the form `x₀y₁ + x₁y₀`, has the
`p`-neighbour `M = ℤ(pe₀) ⊕ ℤ(e₁/p)` for the same form. The form is integral on `M`, its value on
`pe₀` and `e₁/p` being `1`, and `L ∩ M = ℤ(pe₀) ⊕ ℤe₁` has index `p` in both, the determinants of
the changes of basis being `p` and `(p · p⁻¹)⁻¹ · p = p`. So `L ∼_p M` and `M ∼_p L`, but `L ≁_p L`
for `p ≠ 1`.

## Main definitions

* `TauCeti.IntegralLattice.hyperbolicPlaneNeighbor`: the `p`-neighbour `ℤ(pe₀) ⊕ ℤ(e₁/p)` of the
  hyperbolic plane.

## Main results

* `TauCeti.IntegralLattice.isNeighbor_self_iff` (LMFDB `lattice.pneighbor`): a lattice is its own
  `p`-neighbour only for `p = 1`.
* `TauCeti.IntegralLattice.not_refl_isNeighbor` (LMFDB `lattice.pneighbor`): for `p ≠ 1` the
  `p`-neighbour relation is not reflexive.
* `TauCeti.IntegralLattice.isNeighbor_hyperbolicPlaneNeighbor` (LMFDB `lattice.pneighbor`): the
  hyperbolic plane and `ℤ(pe₀) ⊕ ℤ(e₁/p)` are `p`-neighbours.
* `TauCeti.IntegralLattice.not_isTrans_isNeighbor` (LMFDB `lattice.pneighbor`): for `p ≠ 0, 1` the
  `p`-neighbour relation is not transitive.

## References

* M. Kneser, *Klassenzahlen definiter quadratischer Formen*, Arch. Math. 8 (1957), 241--250.
-/

open Module

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V} {p : ℕ}

/-- **A lattice is its own `p`-neighbour only for `p = 1`** (LMFDB `lattice.pneighbor`): `L ∩ L = L`
has index `1` in `L`. So for `p ≠ 1` no lattice is its own `p`-neighbour. -/
@[simp]
lemma isNeighbor_self_iff : L.IsNeighbor L p ↔ p = 1 :=
  ⟨fun h ↦ by rw [← h.relIndex_inf_left, inf_idem, AddSubgroup.relIndex_self],
    fun h ↦ h ▸ isNeighbor_one_iff.mpr rfl⟩

/-- **The `p`-neighbour relation is not reflexive for `p ≠ 1`** (LMFDB `lattice.pneighbor`): the
hyperbolic plane is not its own `p`-neighbour. -/
lemma not_refl_isNeighbor (hp : p ≠ 1) :
    ¬Std.Refl fun M N : IntegralLattice (Fin 2 → ℚ) ↦ M.IsNeighbor N p :=
  fun h ↦ hp <| isNeighbor_self_iff.mp <| h.refl hyperbolicPlane

private lemma mem_span_unitsSMul_iff (w : Fin 2 → ℚˣ) (x : Fin 2 → ℚ) :
    x ∈ Submodule.span ℤ (Set.range ((Pi.basisFun ℚ (Fin 2)).unitsSMul w)) ↔
      ∀ i, ∃ z : ℤ, (z : ℚ) = ((w i)⁻¹ : ℚˣ) * x i := by
  simp [Basis.mem_span_iff_repr_mem, Units.smul_def]

variable (p) [NeZero p]

/-- The basis `(pe₀, e₁/p)` of `ℚ²`. -/
private noncomputable def neighborBasis : Basis (Fin 2) ℚ (Fin 2 → ℚ) :=
  (Pi.basisFun ℚ (Fin 2)).unitsSMul ![.mk0 p (NeZero.ne _), (.mk0 p (NeZero.ne _))⁻¹]

/-- The basis `(pe₀, e₁)` of `ℚ²`. -/
private noncomputable def interBasis : Basis (Fin 2) ℚ (Fin 2 → ℚ) :=
  (Pi.basisFun ℚ (Fin 2)).unitsSMul ![.mk0 p (NeZero.ne _), 1]

/-- The `p`-neighbour `ℤ(pe₀) ⊕ ℤ(e₁/p)` of the hyperbolic plane (LMFDB `lattice.pneighbor`), for
`p ≠ 0`: the lattice of `ℚ²` spanned by `pe₀` and `e₁/p`, with the form `x₀y₁ + x₁y₀` of Tau Ceti's
`TauCeti.IntegralLattice.hyperbolicPlane`, which is integral on it since its value on `pe₀` and
`e₁/p` is `1`. -/
noncomputable def hyperbolicPlaneNeighbor : IntegralLattice (Fin 2 → ℚ) :=
  ofBasis (neighborBasis p) hyperbolicPlane.form hyperbolicPlane.isSymm fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp [neighborBasis, Basis.unitsSMul_apply, Units.smul_def]

@[simp]
lemma hyperbolicPlaneNeighbor_form : (hyperbolicPlaneNeighbor p).form = hyperbolicPlane.form :=
  ofBasis_form ..

@[simp]
lemma mem_hyperbolicPlaneNeighbor_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ (hyperbolicPlaneNeighbor p).carrier ↔
      (∃ z : ℤ, (z : ℚ) = (p : ℚ)⁻¹ * x 0) ∧ ∃ z : ℤ, (z : ℚ) = p * x 1 := by
  rw [hyperbolicPlaneNeighbor, ofBasis_carrier, neighborBasis, mem_span_unitsSMul_iff,
    Fin.forall_fin_two]
  simp

private lemma inf_carrier_eq_span : hyperbolicPlane.carrier ⊓ (hyperbolicPlaneNeighbor p).carrier =
    Submodule.span ℤ (Set.range (interBasis p)) := by
  ext x
  rw [Submodule.mem_inf, mem_hyperbolicPlane_carrier_iff, mem_hyperbolicPlaneNeighbor_carrier_iff,
    interBasis, mem_span_unitsSMul_iff, Fin.forall_fin_two, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.cons_val_one,
    inv_one, Units.val_one, one_mul]
  refine ⟨fun ⟨⟨_, h₁⟩, h₀, _⟩ ↦ ⟨h₀, h₁⟩, fun ⟨⟨a, ha⟩, b, hb⟩ ↦ ⟨⟨⟨p * a, ?_⟩, b, hb⟩, ⟨a, ha⟩,
    p * b, ?_⟩⟩
  · rw [Int.cast_mul, Int.cast_natCast, ha, mul_inv_cancel_left₀ (NeZero.ne _)]
  · rw [Int.cast_mul, Int.cast_natCast, hb]

/-- **The hyperbolic plane and `ℤ(pe₀) ⊕ ℤ(e₁/p)` are `p`-neighbours** (LMFDB `lattice.pneighbor`),
for every `p ≠ 0`: their intersection `ℤ(pe₀) ⊕ ℤe₁` has index `p` in both. -/
lemma isNeighbor_hyperbolicPlaneNeighbor :
    hyperbolicPlane.IsNeighbor (hyperbolicPlaneNeighbor p) p where
  form_eq := (hyperbolicPlaneNeighbor_form p).symm
  relIndex_inf_left := Nat.cast_injective (R := ℚ) <| by
    rw [AddSubgroup.relIndex_eq_abs_det _ _ (Submodule.toAddSubgroup_mono inf_le_left)
      (interBasis p) (Pi.basisFun ℚ (Fin 2))
      (by rw [inf_carrier_eq_span, Submodule.span_int_eq_addSubgroupClosure])
      (by rw [hyperbolicPlane, ofGramMatrix_carrier, Submodule.span_int_eq_addSubgroupClosure]),
      interBasis, Basis.det_unitsSMul_self]
    simp
  relIndex_inf_right := Nat.cast_injective (R := ℚ) <| by
    rw [AddSubgroup.relIndex_eq_abs_det _ _ (Submodule.toAddSubgroup_mono inf_le_right)
      (interBasis p) (neighborBasis p)
      (by rw [inf_carrier_eq_span, Submodule.span_int_eq_addSubgroupClosure])
      (by rw [hyperbolicPlaneNeighbor, ofBasis_carrier, Submodule.span_int_eq_addSubgroupClosure]),
      neighborBasis, interBasis, Basis.det_unitsSMul, smul_apply, Basis.det_unitsSMul_self]
    simp

variable {p} in
/-- **The `p`-neighbour relation is not transitive for `p ≠ 0, 1`** (LMFDB `lattice.pneighbor`):
the hyperbolic plane `L` and `M = ℤ(pe₀) ⊕ ℤ(e₁/p)` satisfy `L ∼_p M` and `M ∼_p L`, but not
`L ∼_p L`. For `p = 0` the relation is empty, and for `p = 1` it is equality. -/
lemma not_isTrans_isNeighbor (hp : p ≠ 1) :
    ¬IsTrans (IntegralLattice (Fin 2 → ℚ)) fun M N ↦ M.IsNeighbor N p :=
  fun h ↦ hp <| isNeighbor_self_iff.mp <| h.trans _ _ _ (isNeighbor_hyperbolicPlaneNeighbor p)
    (isNeighbor_hyperbolicPlaneNeighbor p).symm

end TauCeti.IntegralLattice
