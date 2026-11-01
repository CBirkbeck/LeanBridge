import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoQuotient

/-!
# `Sp(4, ℤ)/Γ[2] ≅ S₆` through the six odd theta characteristics

The group `Sp(4, ℤ/2ℤ) ≅ Sp(4, ℤ)/Γ[2]` (`SymplecticGroup.quotientGammaTwoEquiv`) acts faithfully
on the six odd theta characteristics, and every permutation of them arises, so
`Sp(4, ℤ)/Γ[2] ≅ S₆` (LMFDB `mf.siegel.family.gamma_2`).

A characteristic `m = (m', m'') ∈ (ℤ/2ℤ)⁴` defines the quadratic form
`q_m(x) = x'·x'' + ω(m, x)` on `(ℤ/2ℤ)⁴`, where `ω(x, y) = x'·y'' + x''·y'` is the symplectic form
modulo 2, and `q_m` polarises to `ω`. For `M ∈ Sp(4, ℤ/2ℤ)` the form `q_m ∘ M⁻¹` polarises to `ω`
too, so it differs from `q₀` by an additive, hence linear, form, which is `ω(m', ·)` for a unique
`m'`: this defines the action `m ↦ M · m` with `q_{M·m} = q_m ∘ M⁻¹`
(`SymplecticGroup.quadChar_charAct`), and `m ↦ q_m` is injective. The odd characteristics
(`m'·m'' = 1`) are those whose form takes the value 1 exactly ten times, so the action preserves
them. It is faithful: two forms `q_m` with `m` odd agree at `x` and `y` for all six odd `m` only if
`x = y` (a finite check), so an element fixing all six fixes every vector. The symplectic
transvection `x ↦ x + ω(x, m₁ + m₂)(m₁ + m₂)` swaps the odd characteristics `m₁ ≠ m₂` and fixes the
other four (a finite check, by `decide`), and transpositions generate the symmetric group.

## Main definitions

* `SymplecticGroup.quadChar`: the quadratic form `q_m` of a characteristic `m`.
* `SymplecticGroup.omegaTwo`: the symplectic form `ω` modulo 2.
* `SymplecticGroup.charAct`: the action of `Sp(4, ℤ/2ℤ)` on the characteristics.
* `SymplecticGroup.quadCharCount`: the number of `x` with `q_m(x) = 1`.
* `SymplecticGroup.OddChar`: the six odd characteristics.
* `SymplecticGroup.oddCharPerm`, `SymplecticGroup.oddCharHom`: the action of `Sp(4, ℤ/2ℤ)` on the
  odd characteristics.
* `SymplecticGroup.symplecticTransvection`: the transvection `x ↦ x + ω(x, v) v` of `(ℤ/2ℤ)⁴`.
* `SymplecticGroup.oddCharEquiv`: `Sp(4, ℤ/2ℤ) ≅ S₆`.
* `SymplecticGroup.quotientGammaTwoEquivPerm`: `Sp(4, ℤ)/Γ[2] ≅ S₆`.

## Main results

* `SymplecticGroup.quadChar_charAct`: `q_{M·m} = q_m ∘ M⁻¹`.
* `SymplecticGroup.injective_oddCharHom`: the action on the odd characteristics is faithful.
* `SymplecticGroup.surjective_oddCharHom`: every permutation of the odd characteristics arises.
-/

open Equiv Matrix

namespace SymplecticGroup

variable (M N : symplecticGroup (Fin 2) (ZMod 2)) (m v x y : Fin 2 ⊕ Fin 2 → ZMod 2)

/-- The quadratic form `q_m(x) = x'·x'' + ω(m, x)` on `(ℤ/2ℤ)⁴` of a theta characteristic
`m = (m', m'')` modulo 2 (LMFDB `mf.siegel.family.gamma_2`). It polarises to `ω`. -/
def quadChar : ZMod 2 :=
  ∑ i, x (.inl i) * x (.inr i) + ∑ i, (m (.inl i) * x (.inr i) + m (.inr i) * x (.inl i))

/-- The symplectic form `ω(x, y) = x'·y'' + x''·y'` on `(ℤ/2ℤ)⁴`. -/
def omegaTwo : ZMod 2 :=
  ∑ i, (x (.inl i) * y (.inr i) + x (.inr i) * y (.inl i))

lemma quadChar_add : quadChar m (x + y) = quadChar m x + quadChar m y + omegaTwo x y := by
  simp only [quadChar, omegaTwo, Fin.sum_univ_two, Pi.add_apply]
  ring1

lemma omegaTwo_eq : omegaTwo x y = x ⬝ᵥ J (Fin 2) (ZMod 2) *ᵥ y := by
  simp [omegaTwo, J, dotProduct, mulVec]
  ring1

lemma omegaTwo_mulVec : omegaTwo (M.1 *ᵥ x) (M.1 *ᵥ y) = omegaTwo x y := by
  rw [omegaTwo_eq, omegaTwo_eq, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul,
    ← dotProduct_mulVec, mulVec_mulVec, mem_iff'.mp M.2]

/-- The **action of `Sp(4, ℤ/2ℤ)` on the theta characteristics** modulo 2 (LMFDB
`mf.siegel.family.gamma_2`): `M · m` is the characteristic `m'` with `q_{m'} = q_m ∘ M⁻¹`, read off
from the values of the linear form `q_m ∘ M⁻¹ - q₀ = ω(m', ·)` on the standard basis. -/
def charAct : Fin 2 ⊕ Fin 2 → ZMod 2 :=
  fun k ↦ quadChar m (M⁻¹.1 *ᵥ Pi.single k.swap 1) + quadChar 0 (Pi.single k.swap 1)

/-- **The action on characteristics transports the quadratic forms**: `q_{M·m} = q_m ∘ M⁻¹`. The
difference `q_m ∘ M⁻¹ - q₀` is additive, since both forms polarise to the `M`-invariant form `ω`,
hence linear over `ℤ/2ℤ` and determined by its values on the standard basis. -/
lemma quadChar_charAct : quadChar (charAct M m) x = quadChar m (M⁻¹.1 *ᵥ x) := by
  let f : (Fin 2 ⊕ Fin 2 → ZMod 2) →+ ZMod 2 :=
    { toFun z := quadChar m (M⁻¹.1 *ᵥ z) + quadChar 0 z
      map_zero' := by simp [quadChar]
      map_add' z w := by
        rw [mulVec_add, quadChar_add, quadChar_add, omegaTwo_mulVec]
        linear_combination CharTwo.add_self_eq_zero (omegaTwo z w) }
  have hf (z : Fin 2 ⊕ Fin 2 → ZMod 2) : f z = ∑ k, z k * f (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (z k) with h | h <;> simp [h]
  have hl (i : Fin 2) : charAct M m (.inl i) = f (Pi.single (.inr i) 1) := rfl
  have hr (i : Fin 2) : charAct M m (.inr i) = f (Pi.single (.inl i) 1) := rfl
  have e : quadChar (charAct M m) x = quadChar 0 x + f x := by
    rw [hf x]
    simp only [quadChar, hl, hr]
    simp
    ring1
  have hfx : f x = quadChar m (M⁻¹.1 *ᵥ x) + quadChar 0 x := rfl
  rw [e, hfx]
  linear_combination CharTwo.add_self_eq_zero (quadChar 0 x)

variable {m} in
lemma quadChar_injective {m' : Fin 2 ⊕ Fin 2 → ZMod 2}
    (h : ∀ z, quadChar m z = quadChar m' z) : m = m' := by
  ext k
  have hk : quadChar m (Pi.single k.swap 1) = quadChar m' (Pi.single k.swap 1) := h _
  rcases k with i | i <;> fin_cases i <;>
    simpa [quadChar] using hk

lemma charAct_mul : charAct (M * N) m = charAct M (charAct N m) :=
  quadChar_injective fun z ↦ by
    rw [quadChar_charAct, quadChar_charAct, quadChar_charAct, mul_inv_rev M N, Submonoid.coe_mul,
      mulVec_mulVec]

lemma charAct_one : charAct 1 m = m :=
  quadChar_injective fun z ↦ by
    rw [quadChar_charAct, inv_one, Submonoid.coe_one, one_mulVec]

/-- The number of `x ∈ (ℤ/2ℤ)⁴` with `q_m(x) = 1`, which is 10 for the odd characteristics and 6
for the even ones. -/
def quadCharCount : ℕ :=
  (Finset.univ.filter fun z ↦ quadChar m z = 1).card

lemma odd_iff_quadCharCount : ∑ i, m (.inl i) * m (.inr i) = 1 ↔ quadCharCount m = 10 := by
  revert m
  decide

lemma quadCharCount_charAct : quadCharCount (charAct M m) = quadCharCount m := by
  have e : M.1 * M⁻¹.1 = 1 := by
    rw [← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one]
  have e' : M⁻¹.1 * M.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  refine Finset.card_nbij' (fun z ↦ M⁻¹.1 *ᵥ z) (fun z ↦ M.1 *ᵥ z) (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    (fun z _ ↦ by simp only [mulVec_mulVec, e, one_mulVec])
      fun z _ ↦ by simp only [mulVec_mulVec, e', one_mulVec]
  · simpa [quadChar_charAct] using hz
  · simpa [quadChar_charAct, mulVec_mulVec, e'] using hz

lemma eq_of_quadChar_eq (h : ∀ m, ∑ i, m (.inl i) * m (.inr i) = 1 → quadChar m y = quadChar m x) :
    y = x := by
  revert x y
  decide

/-- The six **odd theta characteristics** `m = (m', m'')` modulo 2, those with `m'·m'' = 1` (LMFDB
`mf.siegel.family.gamma_2`). -/
abbrev OddChar : Type :=
  {m : Fin 2 ⊕ Fin 2 → ZMod 2 // ∑ i, m (.inl i) * m (.inr i) = 1}

/-- The permutation of the odd characteristics induced by an element of `Sp(4, ℤ/2ℤ)`. -/
def oddCharPerm : Equiv.Perm OddChar where
  toFun o := ⟨charAct M o.1, (odd_iff_quadCharCount _).mpr ((quadCharCount_charAct M o.1).trans
    ((odd_iff_quadCharCount _).mp o.2))⟩
  invFun o := ⟨charAct M⁻¹ o.1, (odd_iff_quadCharCount _).mpr
    ((quadCharCount_charAct M⁻¹ o.1).trans ((odd_iff_quadCharCount _).mp o.2))⟩
  left_inv o := Subtype.ext <| ((charAct_mul _ _ _).symm.trans <| by
    rw [inv_mul_cancel, charAct_one] : charAct M⁻¹ (charAct M o.1) = o.1)
  right_inv o := Subtype.ext <| ((charAct_mul _ _ _).symm.trans <| by
    rw [mul_inv_cancel, charAct_one] : charAct M (charAct M⁻¹ o.1) = o.1)

/-- The **action of `Sp(4, ℤ/2ℤ)` on the six odd theta characteristics** (LMFDB
`mf.siegel.family.gamma_2`). -/
def oddCharHom : symplecticGroup (Fin 2) (ZMod 2) →* Equiv.Perm OddChar where
  toFun := oddCharPerm
  map_one' := Equiv.ext fun o ↦ Subtype.ext (charAct_one o.1)
  map_mul' M N := Equiv.ext fun o ↦ Subtype.ext (charAct_mul M N o.1)

/-- **`Sp(4, ℤ/2ℤ)` acts faithfully on the six odd theta characteristics**: if `M` fixes them all,
then `q_m(M⁻¹x) = q_m(x)` for the six odd `m`, which forces `M⁻¹x = x`. -/
lemma injective_oddCharHom : Function.Injective oddCharHom := by
  refine (injective_iff_map_eq_one _).mpr fun M hM ↦ ?_
  have hx (z : Fin 2 ⊕ Fin 2 → ZMod 2) : M⁻¹.1 *ᵥ z = z :=
    eq_of_quadChar_eq z _ fun m hm ↦ by
      have h : charAct M m = m := congrArg Subtype.val (Equiv.ext_iff.mp hM ⟨m, hm⟩)
      rw [← quadChar_charAct, h]
  have h1 : M⁻¹.1 = 1 := by
    ext i j
    simpa [Pi.single_apply, one_apply] using congrFun (hx (Pi.single j 1)) i
  exact inv_eq_one.mp (Subtype.ext h1)

lemma symplecticTransvection_mem :
    1 + vecMulVec v (J (Fin 2) (ZMod 2) *ᵥ v) ∈ symplecticGroup (Fin 2) (ZMod 2) := by
  refine mem_iff.mpr ?_
  revert v
  decide

/-- The **symplectic transvection** `x ↦ x + ω(x, v) v` of `(ℤ/2ℤ)⁴`, an element of
`Sp(4, ℤ/2ℤ)`. -/
def symplecticTransvection : symplecticGroup (Fin 2) (ZMod 2) :=
  ⟨1 + vecMulVec v (J (Fin 2) (ZMod 2) *ᵥ v), symplecticTransvection_mem v⟩

lemma oddCharHom_symplecticTransvection_apply : ∀ o : OddChar × OddChar × OddChar,
    o.1 ≠ o.2.1 → oddCharHom (symplecticTransvection (o.1.1 + o.2.1.1)) o.2.2 =
      Equiv.swap o.1 o.2.1 o.2.2 := by
  decide +kernel

/-- **Every permutation of the six odd theta characteristics comes from `Sp(4, ℤ/2ℤ)`**: the
transvection by `m₁ + m₂` swaps the odd characteristics `m₁ ≠ m₂`, and transpositions generate the
symmetric group. -/
lemma surjective_oddCharHom : Function.Surjective oddCharHom := by
  have h : oddCharHom.range = ⊤ := by
    rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
    rintro σ ⟨a, b, hab, rfl⟩
    exact ⟨symplecticTransvection (a.1 + b.1), Equiv.ext fun o ↦
      oddCharHom_symplecticTransvection_apply (a, b, o) hab⟩
  exact MonoidHom.range_eq_top.mp h

lemma card_oddChar : Fintype.card OddChar = 6 := by
  decide

/-- The isomorphism **`Sp(4, ℤ/2ℤ) ≅ S₆`** (LMFDB `mf.siegel.family.gamma_2`) given by the action
on the six odd theta characteristics, numbered by an arbitrary bijection with `Fin 6`. -/
noncomputable def oddCharEquiv : symplecticGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 6) :=
  (MulEquiv.ofBijective oddCharHom ⟨injective_oddCharHom, surjective_oddCharHom⟩).trans
    (Fintype.equivFinOfCardEq card_oddChar).permCongrHom

/-- The isomorphism **`Sp(4, ℤ)/Γ[2] ≅ S₆`** of the knowl `mf.siegel.family.gamma_2`: reduction
modulo 2 followed by the action of `Sp(4, ℤ/2ℤ)` on the six odd theta characteristics. -/
noncomputable def quotientGammaTwoEquivPerm :
    symplecticGroup (Fin 2) ℤ ⧸ Gamma (Fin 2) 2 ≃* Equiv.Perm (Fin 6) :=
  quotientGammaTwoEquiv.trans oddCharEquiv

end SymplecticGroup
