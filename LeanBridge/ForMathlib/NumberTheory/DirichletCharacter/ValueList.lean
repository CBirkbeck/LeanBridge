import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The values of a Dirichlet character

A Dirichlet character `χ` of modulus `q ≥ 1` is determined by its list of values
`(χ(1), χ(2), …, χ(q))`, in which `χ(1) = 1` and, for `q > 1`, `χ(q) = 0` (LMFDB
`character.dirichlet.values`). Each value is `0` or a root of unity, hence of the form
`e(r) = exp(2πir)` for a rational number `r`: the knowl calls every value a root of unity, which
fails for the values `χ(n) = 0` at the integers `n` not prime to `q`, such as `χ(q)`.

The character is also determined, by multiplicativity, by its values on any list of generators of
the group `(ℤ/qℤ)ˣ` (LMFDB `character.dirichlet.values_on_gens`), and these values are roots of
unity `e(r)` with `r` rational. For `q > 1`, every element of `(ℤ/qℤ)ˣ` is the class of an integer
in `[1, q - 1]`, so the generators can be given as such integers.

## Main results

* `DirichletCharacter.eq_iff_forall_mem_Icc` (LMFDB `character.dirichlet.values`): a Dirichlet
  character is determined by its values `χ(1), …, χ(q)`.
* `DirichletCharacter.apply_modulus` (LMFDB `character.dirichlet.values`): `χ(q) = 0` for `q ≠ 1`.
* `DirichletCharacter.eq_iff_forall_apply_eq_of_closure_eq_top` (LMFDB
  `character.dirichlet.values_on_gens`): a Dirichlet character is determined by its values on
  generators of `(ℤ/qℤ)ˣ`.
* `DirichletCharacter.exists_rat_apply_eq_exp` (LMFDB `character.dirichlet.values_on_gens`): the
  value of `χ` at a unit is `e(r)` for a rational number `r`.
* `DirichletCharacter.apply_eq_zero_or_exists_rat_apply_eq_exp` (LMFDB
  `character.dirichlet.values`): every value of `χ` is `0` or `e(r)` for a rational number `r`.
* `ZMod.val_mem_Icc_of_isUnit` (LMFDB `character.dirichlet.values_on_gens`): for `q > 1`, the
  least nonnegative representative of a unit modulo `q` lies in `[1, q - 1]`.
-/

open Complex

open scoped Real

variable {q : ℕ}

namespace DirichletCharacter

variable (χ ψ : DirichletCharacter ℂ q)

variable [NeZero q] in
/-- **A Dirichlet character of modulus `q` is determined by its list of values
`χ(1), …, χ(q)`**, as every residue class modulo `q` has a representative in `[1, q]`. -/
lemma eq_iff_forall_mem_Icc : χ = ψ ↔ ∀ n ∈ Finset.Icc 1 q, χ n = ψ n := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ MulChar.ext' fun a ↦ ?_⟩
  rcases eq_or_ne a.val 0 with ha | ha
  · rw [a.val_eq_zero.mp ha, ← ZMod.natCast_self]
    exact h q <| Finset.mem_Icc.mpr ⟨NeZero.one_le, le_rfl⟩
  · rw [← a.natCast_zmod_val]
    exact h a.val <| Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr ha, a.val_lt.le⟩

/-- **The value of a Dirichlet character at its modulus `q ≠ 1` is `0`.** -/
lemma apply_modulus (hq : q ≠ 1) : χ q = 0 := by
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  rw [ZMod.natCast_self, χ.map_zero]

/-- **A Dirichlet character is determined by its values on generators of `(ℤ/qℤ)ˣ`**: if the
units `g i` generate `(ℤ/qℤ)ˣ`, then two characters that agree at every `g i` are equal. -/
lemma eq_iff_forall_apply_eq_of_closure_eq_top {ι : Type*} {g : ι → (ZMod q)ˣ}
    (hg : Subgroup.closure (Set.range g) = ⊤) : χ = ψ ↔ ∀ i, χ (g i) = ψ (g i) := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ MulChar.ext fun u ↦ ?_⟩
  have hχψ : χ.toUnitHom = ψ.toUnitHom :=
    MonoidHom.eq_of_eqOn_dense hg fun _ ⟨i, hi⟩ ↦ Units.ext <| by
      rw [← hi, χ.coe_toUnitHom, ψ.coe_toUnitHom, h i]
  rw [← χ.coe_toUnitHom, hχψ, ψ.coe_toUnitHom]

variable [NeZero q]

/-- **The value of a Dirichlet character at a unit is a root of unity `e(r) = exp(2πir)` for a
rational number `r`.** -/
lemma exists_rat_apply_eq_exp (u : (ZMod q)ˣ) : ∃ r : ℚ, χ u = exp (2 * π * I * r) := by
  have : NeZero (Fintype.card (ZMod q)ˣ) := ⟨Fintype.card_ne_zero⟩
  rcases (Complex.mem_rootsOfUnity _ _).mp (MulChar.apply_mem_rootsOfUnity u (χ := χ)) with
    ⟨i, -, hi⟩
  refine ⟨i / Fintype.card (ZMod q)ˣ, ?_⟩
  rw [← χ.coe_equivToUnitHom, ← hi]
  push_cast
  rfl

/-- **Every value of a Dirichlet character is `0` or a root of unity `e(r) = exp(2πir)` for a
rational number `r`.** It is `0` exactly at the residues that are not units. -/
lemma apply_eq_zero_or_exists_rat_apply_eq_exp (a : ZMod q) :
    χ a = 0 ∨ ∃ r : ℚ, χ a = exp (2 * π * I * r) := by
  by_cases ha : IsUnit a
  · exact .inr <| ha.unit_spec ▸ χ.exists_rat_apply_eq_exp ha.unit
  · exact .inl <| χ.map_nonunit ha

end DirichletCharacter

namespace ZMod

/-- **For `q > 1`, the least nonnegative representative of a unit modulo `q` lies in
`[1, q - 1]`**, so every element of `(ℤ/qℤ)ˣ` is the class of an integer in `[1, q - 1]`. -/
lemma val_mem_Icc_of_isUnit (hq : 1 < q) {a : ZMod q} (ha : IsUnit a) :
    a.val ∈ Finset.Icc 1 (q - 1) := by
  have : NeZero q := ⟨by omega⟩
  have : Nontrivial (ZMod q) := nontrivial_iff.mpr hq.ne'
  have hval : a.val ≠ 0 := fun h ↦ ha.ne_zero <| a.val_eq_zero.mp h
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hval, Nat.le_sub_one_of_lt a.val_lt⟩

end ZMod
