import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GammaOne

/-!
# The congruence subgroups `Γ₀(N)` and `Γ(N)` of `Sp(2, ℤ)`

For `g = 1` the symplectic group `Sp(2g, ℤ)` is `SL(2, ℤ)`, through the isomorphism
`SymplecticGroup.toSL` (a `2 × 2` matrix is symplectic exactly when its determinant is `1`). It
identifies the Siegel congruence subgroup `Γ₀(N)` (LMFDB `group.sp2gr.gamma0`,
`SymplecticGroup.Gamma0`) with the subgroup `Γ₀(N)` of `SL(2, ℤ)` (LMFDB
`group.sl2z.subgroup.gamma0n`, Mathlib's `CongruenceSubgroup.Gamma0`), and the principal congruence
subgroup `Γ(N)` (LMFDB `group.sp2gr.ppal.congruence`, `SymplecticGroup.Gamma`) with the subgroup
`Γ(N)` of `SL(2, ℤ)` (LMFDB `group.sl2z.subgroup.gamman`, Mathlib's `CongruenceSubgroup.Gamma`), as
the knowls say: each is the preimage, and so the image, of the other.

## Main results

* `SymplecticGroup.Gamma0_fin_one` and `SymplecticGroup.map_toSL_Gamma0` (LMFDB
  `group.sp2gr.gamma0`): for `g = 1`, `Γ₀(N)` is the subgroup `Γ₀(N)` of `SL(2, ℤ)`.
* `SymplecticGroup.Gamma_fin_one` and `SymplecticGroup.map_toSL_Gamma` (LMFDB
  `group.sp2gr.ppal.congruence`): for `g = 1`, `Γ(N)` is the subgroup `Γ(N)` of `SL(2, ℤ)`.
-/

open Matrix

namespace SymplecticGroup

variable (N : ℕ)

private lemma finSumFinEquiv_symm_zero : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = .inl 0 :=
  rfl

private lemma finSumFinEquiv_symm_one : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 1 = .inr 0 :=
  rfl

/-- **For `g = 1`, `Γ₀(N)` is the subgroup `Γ₀(N)` of `SL(2, ℤ)`** (LMFDB `group.sp2gr.gamma0`,
Mathlib's `CongruenceSubgroup.Gamma0`): it is its preimage under the isomorphism
`Sp(2, ℤ) → SL(2, ℤ)`. -/
lemma Gamma0_fin_one : Gamma0 (Fin 1) N = (CongruenceSubgroup.Gamma0 N).comap (toSL ℤ) := by
  ext B
  rw [Subgroup.mem_comap, CongruenceSubgroup.Gamma0_mem, mem_Gamma0_iff, coe_toSL_apply]
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd, finSumFinEquiv_symm_one, finSumFinEquiv_symm_zero]

/-- **For `g = 1`, the isomorphism `Sp(2, ℤ) → SL(2, ℤ)` maps `Γ₀(N)` onto the subgroup `Γ₀(N)` of
`SL(2, ℤ)`** (LMFDB `group.sp2gr.gamma0`, Mathlib's `CongruenceSubgroup.Gamma0`). -/
lemma map_toSL_Gamma0 : (Gamma0 (Fin 1) N).map (toSL ℤ) = CongruenceSubgroup.Gamma0 N := by
  rw [Gamma0_fin_one, Subgroup.map_comap_eq_self_of_surjective toSL_surjective]

/-- **For `g = 1`, `Γ(N)` is the subgroup `Γ(N)` of `SL(2, ℤ)`** (LMFDB
`group.sp2gr.ppal.congruence`, Mathlib's `CongruenceSubgroup.Gamma`): it is its preimage under the
isomorphism `Sp(2, ℤ) → SL(2, ℤ)`. -/
lemma Gamma_fin_one : Gamma (Fin 1) N = (CongruenceSubgroup.Gamma N).comap (toSL ℤ) := by
  ext B
  rw [Subgroup.mem_comap, CongruenceSubgroup.Gamma_mem, mem_Gamma_iff, coe_toSL_apply]
  simp [← Matrix.ext_iff, finSumFinEquiv_symm_zero, finSumFinEquiv_symm_one, and_assoc]

/-- **For `g = 1`, the isomorphism `Sp(2, ℤ) → SL(2, ℤ)` maps `Γ(N)` onto the subgroup `Γ(N)` of
`SL(2, ℤ)`** (LMFDB `group.sp2gr.ppal.congruence`, Mathlib's `CongruenceSubgroup.Gamma`). -/
lemma map_toSL_Gamma : (Gamma (Fin 1) N).map (toSL ℤ) = CongruenceSubgroup.Gamma N := by
  rw [Gamma_fin_one, Subgroup.map_comap_eq_self_of_surjective toSL_surjective]

end SymplecticGroup
