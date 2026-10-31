import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The congruence subgroup `Γ₁(N)` of `Sp(2g, ℤ)`

The subgroup `Γ₁(N)` of `Sp(2g, ℤ)` consists of the matrices congruent to `(1_g, *; 0, 1_g)`
modulo `N`: it is the preimage of the subgroup of the `(1, b; 0, 1)` of `Sp(2g, ℤ/Nℤ)`, the
unipotent radical of the Siegel parabolic subgroup. It lies between the principal congruence
subgroup `Γ(N)` and the Siegel congruence subgroup `Γ₀(N)`. For `g = 1`, the isomorphism
`Sp(2, R) ≅ SL(2, R)` (a `2 × 2` matrix is symplectic exactly when its determinant is `1`) maps it
onto Mathlib's `Γ₁(N)`, as the knowl says.

## Main definitions

* `SymplecticGroup.siegelUnipotent`: the subgroup of the `(1, b; 0, 1)` in `Sp(2g, R)`.
* `SymplecticGroup.Gamma1` (LMFDB `group.sp2gr.gamma1`): the subgroup `Γ₁(N)` of `Sp(2g, ℤ)`.
* `SymplecticGroup.toSL`: the isomorphism `Sp(2, R) → SL(2, R)`.

## Main results

* `SymplecticGroup.Gamma1_fin_one` and `SymplecticGroup.map_toSL_Gamma1`: for `g = 1`, `Γ₁(N)` is
  the subgroup `Γ₁(N)` of `SL(2, ℤ)`, its preimage and its image under `Sp(2, ℤ) ≅ SL(2, ℤ)`.
-/

open Matrix

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] {R : Type*} [CommRing R]

private lemma eq_fromBlocks_of_toBlocks {M : Matrix (l ⊕ l) (l ⊕ l) R} (h₁₁ : M.toBlocks₁₁ = 1)
    (h₂₁ : M.toBlocks₂₁ = 0) (h₂₂ : M.toBlocks₂₂ = 1) : M = fromBlocks 1 M.toBlocks₁₂ 0 1 := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h₁₁, h₂₁, h₂₂]

variable [Fintype l] (N : ℕ) {A : symplecticGroup l ℤ}

variable (l R) in
/-- The subgroup of `Sp(2g, R)` of the matrices `(1, b; 0, 1)`, the unipotent radical of the Siegel
parabolic subgroup. -/
def siegelUnipotent : Subgroup (symplecticGroup l R) where
  carrier := {B | (B : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ = 1 ∧
    (B : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0 ∧ (B : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ = 1}
  mul_mem' {B C} hB hC := by
    rw [Set.mem_ofPred_eq, Submonoid.coe_mul, eq_fromBlocks_of_toBlocks hB.1 hB.2.1 hB.2.2,
      eq_fromBlocks_of_toBlocks hC.1 hC.2.1 hC.2.2, fromBlocks_multiply]
    simp
  one_mem' := by
    simp [← fromBlocks_one]
  inv_mem' {B} hB := by
    rw [Set.mem_ofPred_eq, coe_inv, eq_fromBlocks_of_toBlocks hB.1 hB.2.1 hB.2.2]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg]

variable (l) in
/-- The **congruence subgroup `Γ₁(N)`** (LMFDB `group.sp2gr.gamma1`) of `Sp(2g, ℤ)`: the matrices
`(a, b; c, d)` congruent to `(1_g, *; 0, 1_g)` modulo `N`, that is, with `a ≡ d ≡ 1_g` and
`c ≡ 0 (mod N)`; the preimage of the subgroup of the `(1, b; 0, 1)` of `Sp(2g, ℤ/Nℤ)`. -/
def Gamma1 : Subgroup (symplecticGroup l ℤ) :=
  (siegelUnipotent l (ZMod N)).comap (map (Int.castRingHom (ZMod N)))

variable {N} in
lemma mem_Gamma1_iff : A ∈ Gamma1 l N ↔
    (A : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₁₁.map (Int.cast : ℤ → ZMod N) = 1 ∧
      (A : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₁.map (Int.cast : ℤ → ZMod N) = 0 ∧
        (A : Matrix (l ⊕ l) (l ⊕ l) ℤ).toBlocks₂₂.map (Int.cast : ℤ → ZMod N) = 1 :=
  Iff.rfl

lemma Gamma_le_Gamma1 : Gamma l N ≤ Gamma1 l N :=
  (MonoidHom.comap_bot _).ge.trans <| Subgroup.comap_mono bot_le

lemma Gamma1_le_Gamma0 : Gamma1 l N ≤ Gamma0 l N :=
  fun _ hA ↦ hA.2.1

variable (R) in
/-- The isomorphism `Sp(2, R) → SL(2, R)`, reindexing `Fin 1 ⊕ Fin 1` as `Fin 2`: symplectic
matrices have determinant `1` (`SymplecticGroup.det_eq_one`), and it is bijective
(`SymplecticGroup.toSL_injective`, `SymplecticGroup.toSL_surjective`), a `2 × 2` matrix of
determinant `1` being symplectic. -/
def toSL : symplecticGroup (Fin 1) R →* SpecialLinearGroup (Fin 2) R where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R),
    by rw [det_reindex_self, det_eq_one B.2]⟩
  map_one' := Subtype.ext <| by simp
  map_mul' B C := Subtype.ext (submatrix_mul_equiv (B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R)
    (C : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) _ finSumFinEquiv.symm _).symm

lemma coe_toSL_apply (B : symplecticGroup (Fin 1) R) : (toSL R B : Matrix (Fin 2) (Fin 2) R) =
    reindex finSumFinEquiv finSumFinEquiv (B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :=
  rfl

lemma toSL_injective : Function.Injective (toSL R) := fun _ _ h ↦
  Subtype.ext <| (reindex finSumFinEquiv finSumFinEquiv).injective <| congrArg Subtype.val h

private lemma fromBlocks_of_mem_symplecticGroup (B : SpecialLinearGroup (Fin 2) R) :
    fromBlocks (of fun _ _ ↦ B 0 0) (of fun _ _ ↦ B 0 1) (of fun _ _ ↦ B 1 0)
      (of fun _ _ ↦ B 1 1) ∈ symplecticGroup (Fin 1) R := by
  have h : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    rw [← det_fin_two]
    exact B.2
  refine fromBlocks_mem_iff.mpr ⟨?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.mul_apply, one_apply, Subsingleton.elim i j, mul_comm]
  linear_combination h

lemma toSL_surjective : Function.Surjective (toSL R) := fun B ↦
  ⟨⟨_, fromBlocks_of_mem_symplecticGroup B⟩, Subtype.ext <| by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩

/-- **For `g = 1`, `Γ₁(N)` is the subgroup `Γ₁(N)` of `SL(2, ℤ)`** (Mathlib's
`CongruenceSubgroup.Gamma1`): it is its preimage under the isomorphism `Sp(2, ℤ) → SL(2, ℤ)`. -/
lemma Gamma1_fin_one : Gamma1 (Fin 1) N = (CongruenceSubgroup.Gamma1 N).comap (toSL ℤ) := by
  have h₀ : (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).symm 0 = .inl 0 := rfl
  ext B
  rw [Subgroup.mem_comap, CongruenceSubgroup.Gamma1_mem, mem_Gamma1_iff, coe_toSL_apply]
  simp [← Matrix.ext_iff, toBlocks₁₁, h₀]
  exact fun _ ↦ and_comm

/-- **For `g = 1`, the isomorphism `Sp(2, ℤ) → SL(2, ℤ)` maps `Γ₁(N)` onto the subgroup `Γ₁(N)`
of `SL(2, ℤ)`** (Mathlib's `CongruenceSubgroup.Gamma1`). -/
lemma map_toSL_Gamma1 : (Gamma1 (Fin 1) N).map (toSL ℤ) = CongruenceSubgroup.Gamma1 N := by
  rw [Gamma1_fin_one, Subgroup.map_comap_eq_self_of_surjective toSL_surjective]

end SymplecticGroup
