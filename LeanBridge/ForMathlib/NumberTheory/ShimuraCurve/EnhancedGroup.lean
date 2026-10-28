import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Coarse

/-!
# The enhanced group of a polarized quaternion order, its index and its level

Let `O` be an order in a quaternion algebra `B` over `ℚ` with a polarization `μ`, and let
`Ô = O ⊗ ℤ̂`. Its unit group is the inverse limit `Ô^× = lim_N (O/NO)^×` over the positive integers
`N` ordered by divisibility, which we take as its definition: the compatible families `(x_N)_N` of
units `x_N ∈ (O/NO)^×`, a subgroup of `∏_N (O/NO)^×`. The group `Aut_{±μ}(O)` acts on each
`(O/NO)^×` by conjugation, compatibly with the reductions, hence on `Ô^×`, and the enhanced group is
the semidirect product `Aut_{±μ}(O) ⋉ Ô^×`, Mathlib's `Ô^× ⋊ Aut_{±μ}(O)` as in
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Coarse`.

The index of a Shimura curve `X_H` (LMFDB `shimcurve.index`) is Mathlib's `Subgroup.index` of `H` in
the enhanced group. The level of `H` is the least `N > 0` such that `H` contains the kernel of
`Ô^× → (O/NO)^×`; it is `0` when there is no such `N`, which does not happen for the open subgroups
`H` of the LMFDB.

As in `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.Coarse`, `B` is any `ℚ`-algebra, `O` any
subring and `μ` any element. The profinite topology of `Ô^×` (the subspace topology of the product
of the discrete groups `(O/NO)^×`) and of the enhanced group is not introduced: the index and the
level are purely group-theoretic.

## Main definitions

* `Subalgebra.completedUnits` (LMFDB `shimcurve.enhanced_group`): the group `Ô^×`.
* `Subalgebra.completedUnitsAction`: the action of `Aut_{±μ}(O)` on `Ô^×` by conjugation.
* `Subalgebra.EnhancedGroup` (LMFDB `shimcurve.enhanced_group`): the enhanced group
  `Aut_{±μ}(O) ⋉ Ô^×`.
* `Subalgebra.enhancedGroupKernel`: the kernel of `Ô^× → (O/NO)^×` in the enhanced group.
* `Subalgebra.enhancedGroupLevel` (LMFDB `shimcurve.level`): the level of a subgroup.

## Main results

* `Subalgebra.enhancedGroupKernel_le_of_level_pos`: a subgroup of positive level contains the
  kernel of reduction modulo its level.
-/

namespace Subalgebra

variable {B : Type*} [Ring B] (O : Subalgebra ℤ B) {M N : ℕ}

lemma span_natCast_le_of_dvd (h : M ∣ N) : Ideal.span {(N : O)} ≤ Ideal.span {(M : O)} := by
  rcases h with ⟨k, rfl⟩
  rw [Ideal.span_le, Set.singleton_subset_iff, mul_comm, Nat.cast_mul]
  exact Ideal.mul_mem_left _ _ <| Ideal.mem_span_singleton_self _

/-- Reduction `(O/NO)^× → (O/MO)^×` for positive integers `M ∣ N`. -/
noncomputable def quotientUnitsReduction (h : M ∣ N) :
    (O ⧸ Ideal.span {(N : O)})ˣ →* (O ⧸ Ideal.span {(M : O)})ˣ :=
  Units.map (Ideal.Quotient.factor <| O.span_natCast_le_of_dvd h).toMonoidHom

/-- The unit group **`Ô^×`** (LMFDB `shimcurve.enhanced_group`) of `Ô = O ⊗ ℤ̂`, as the inverse
limit `lim_N (O/NO)^×`: the families `(x_N)_N ∈ ∏_N (O/NO)^×` over the positive integers `N` such
that `x_N` reduces to `x_M` modulo `M` whenever `M ∣ N`. -/
def completedUnits : Subgroup (∀ N : ℕ+, (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ) where
  carrier := {x | ∀ M N : ℕ+, ∀ h : (M : ℕ) ∣ N, O.quotientUnitsReduction h (x N) = x M}
  one_mem' _ _ _ := map_one _
  mul_mem' hx hy M N h := by
    rw [Pi.mul_apply, map_mul, hx M N h, hy M N h, Pi.mul_apply]
  inv_mem' hx M N h := by
    rw [Pi.inv_apply, map_inv, hx M N h, Pi.inv_apply]

variable [Algebra ℚ B] (μ : B)

lemma quotientUnitsReduction_autPmMuQuotientUnitsAction (h : M ∣ N) (w : O.autPmMu μ)
    (x : (O ⧸ Ideal.span {(N : O)})ˣ) :
    O.quotientUnitsReduction h (O.autPmMuQuotientUnitsAction N μ w x) =
      O.autPmMuQuotientUnitsAction M μ w (O.quotientUnitsReduction h x) := by
  rcases x with ⟨x, -, -, -⟩
  refine Units.ext ?_
  induction x using Quotient.inductionOn'
  rfl

/-- The action of `Aut_{±μ}(O)` on `Ô^× = lim_N (O/NO)^×` by conjugation, componentwise. -/
noncomputable def completedUnitsAction : O.autPmMu μ →* MulAut O.completedUnits where
  toFun w :=
    { toFun x := ⟨fun N ↦ O.autPmMuQuotientUnitsAction N μ w (x.1 N), fun M N h ↦ by
        rw [quotientUnitsReduction_autPmMuQuotientUnitsAction, x.2 M N h]⟩
      invFun x := ⟨fun N ↦ O.autPmMuQuotientUnitsAction N μ w⁻¹ (x.1 N), fun M N h ↦ by
        rw [quotientUnitsReduction_autPmMuQuotientUnitsAction, x.2 M N h]⟩
      left_inv x := Subtype.ext <| funext fun N ↦ by
        simp
      right_inv x := Subtype.ext <| funext fun N ↦ by
        simp
      map_mul' x y := Subtype.ext <| funext fun N ↦ map_mul _ _ _ }
  map_one' := MulEquiv.ext fun x ↦ Subtype.ext <| funext fun N ↦ by
    simp
  map_mul' w v := MulEquiv.ext fun x ↦ Subtype.ext <| funext fun N ↦ by
    simp

/-- The **enhanced group** `Aut_{±μ}(O) ⋉ Ô^×` (LMFDB `shimcurve.enhanced_group`) of a polarized
order `(O, μ)`, Mathlib's semidirect product `Ô^× ⋊ Aut_{±μ}(O)`, where `⟨x, w⟩` is the product
`x w` and `w` acts on `Ô^×` by conjugation. -/
abbrev EnhancedGroup : Type _ :=
  O.completedUnits ⋊[O.completedUnitsAction μ] O.autPmMu μ

/-- Reduction `Ô^× → (O/NO)^×` modulo a positive integer `N`. -/
noncomputable def completedUnitsReduction (N : ℕ+) :
    O.completedUnits →* (O ⧸ Ideal.span {((N : ℕ) : O)})ˣ :=
  (Pi.evalMonoidHom _ N).comp O.completedUnits.subtype

/-- The kernel of reduction `Ô^× → (O/NO)^×` modulo a positive integer `N`, as a subgroup of the
enhanced group `Aut_{±μ}(O) ⋉ Ô^×`. -/
noncomputable def enhancedGroupKernel (N : ℕ+) : Subgroup (O.EnhancedGroup μ) :=
  (O.completedUnitsReduction N).ker.map SemidirectProduct.inl

/-- The **level** (LMFDB `shimcurve.level`) of a subgroup `H` of the enhanced group
`Aut_{±μ}(O) ⋉ Ô^×`: the least positive integer `N` such that `H` contains the kernel of
`Ô^× → (O/NO)^×`, and `0` if there is none. For the open subgroups of the LMFDB there is one. -/
noncomputable def enhancedGroupLevel (H : Subgroup (O.EnhancedGroup μ)) : ℕ :=
  sInf {n | ∃ N : ℕ+, (N : ℕ) = n ∧ O.enhancedGroupKernel μ N ≤ H}

/-- **A subgroup of positive level contains the kernel of reduction modulo its level.** -/
lemma enhancedGroupKernel_le_of_level_pos {H : Subgroup (O.EnhancedGroup μ)}
    (hH : 0 < O.enhancedGroupLevel μ H) :
    O.enhancedGroupKernel μ ⟨O.enhancedGroupLevel μ H, hH⟩ ≤ H := by
  rcases Nat.sInf_mem (Nat.nonempty_of_pos_sInf hH) with ⟨N, hN, h⟩
  exact (PNat.eq hN : N = ⟨_, hH⟩) ▸ h

end Subalgebra
