import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Congruence and paramodular subgroups of the symplectic group

The families of discrete subgroups of `Sp(2g, ℚ)` on which the LMFDB's Siegel modular forms live:
the principal congruence subgroups `Γ(N)` and the Siegel congruence subgroups `Γ₀(N)` of
`Sp(2g, ℤ)`, and the paramodular groups `Γ^para(d)`. Mathlib's `Matrix.symplecticGroup l R` is
defined with `J = (0, -1; 1, 0)`, the negative of the LMFDB's `J`, which gives the same group.

## Main definitions

* `SymplecticGroup.map`: the homomorphism `Sp(2g, R) → Sp(2g, S)` induced by a ring homomorphism.
* `SymplecticGroup.Gamma` (LMFDB `group.sp2gr.ppal.congruence`, `mf.siegel.family`).
* `SymplecticGroup.siegelParabolic`: the Siegel parabolic subgroup `{c = 0}` of `Sp(2g, R)`.
* `SymplecticGroup.Gamma0` (LMFDB `group.sp2gr.gamma0`, `mf.siegel.family`).
* `SymplecticGroup.paramodularGL` and `SymplecticGroup.paramodular` (LMFDB
  `paramodulargroup.sp2gr`, `mf.siegel.family`): the integral isometry group of
  `T = (0, d; -d, 0)` and its conjugate `δ Γ δ⁻¹` in `Sp(2g, ℚ)`, `δ = diag(1_g, d)`.

## Main results

* `SymplecticGroup.paramodularDelta_mul_mul_mem`: `δ γ δ⁻¹` is symplectic for every integral
  isometry `γ` of `T`.
-/

open Matrix

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] [Fintype l] {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (N : ℕ) {A : symplecticGroup l ℤ}

/-- The homomorphism `Sp(2g, R) → Sp(2g, S)` induced by a ring homomorphism `f : R → S`, applying
`f` to the entries. -/
def map : symplecticGroup l R →* symplecticGroup l S where
  toFun B := ⟨(B : Matrix (l ⊕ l) (l ⊕ l) R).map f, map_mem B.2 f⟩
  map_one' := Subtype.ext <| by simp
  map_mul' B C := Subtype.ext <| Matrix.map_mul

@[simp]
lemma coe_map_apply (B : symplecticGroup l R) :
    (map f B : Matrix (l ⊕ l) (l ⊕ l) S) = (B : Matrix (l ⊕ l) (l ⊕ l) R).map f :=
  rfl

variable (l) in
/-- The **principal congruence subgroup** `Γ(N)` (LMFDB `group.sp2gr.ppal.congruence`,
`mf.siegel.family`) of `Sp(2g, ℤ)`: the symplectic integral matrices congruent to the identity
modulo `N`. -/
def Gamma : Subgroup (symplecticGroup l ℤ) :=
  (map (Int.castRingHom (ZMod N))).ker

variable {N} in
lemma mem_Gamma_iff :
    A ∈ Gamma l N ↔ (A : Matrix (l ⊕ l) (l ⊕ l) ℤ).map (Int.cast : ℤ → ZMod N) = 1 :=
  MonoidHom.mem_ker.trans Subtype.ext_iff

variable (l R) in
/-- The **Siegel parabolic subgroup** of `Sp(2g, R)`: the symplectic matrices `(a, b; c, d)` with
`c = 0`, the stabiliser of the Lagrangian subspace spanned by the first `g` basis vectors. -/
def siegelParabolic : Subgroup (symplecticGroup l R) where
  carrier := {B | (B : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ = 0}
  mul_mem' {B C} hB hC := by
    ext i j
    have hB' : ∀ k, (B : Matrix (l ⊕ l) (l ⊕ l) R) (.inr i) (.inl k) = 0 :=
      fun k ↦ congrFun (congrFun hB i) k
    have hC' : ∀ k, (C : Matrix (l ⊕ l) (l ⊕ l) R) (.inr k) (.inl j) = 0 :=
      fun k ↦ congrFun (congrFun hC k) j
    simp [toBlocks₂₁, Matrix.mul_apply, hB', hC']
  one_mem' := by
    ext i j
    simp [toBlocks₂₁]
  inv_mem' {B} hB := by
    ext i j
    have hB' : (B : Matrix (l ⊕ l) (l ⊕ l) R) (.inr j) (.inl i) = 0 := congrFun (congrFun hB j) i
    simp [toBlocks₂₁, coe_inv, J, Matrix.mul_apply, one_apply, hB']

variable (l) in
/-- The **Siegel parabolic subgroup** `Γ₀(N)` (LMFDB `group.sp2gr.gamma0`, `mf.siegel.family`) of
`Sp(2g, ℤ)`, also called the Hecke congruence subgroup: the matrices `(a, b; c, d)` with
`c ≡ 0 (mod N)`, the preimage of the Siegel parabolic subgroup of `Sp(2g, ℤ/Nℤ)`. -/
def Gamma0 : Subgroup (symplecticGroup l ℤ) :=
  (siegelParabolic l (ZMod N)).comap (map (Int.castRingHom (ZMod N)))

variable {N} in
lemma mem_Gamma0_iff :
    A ∈ Gamma0 l N ↔ ∀ i j, (N : ℤ) ∣ (A : Matrix (l ⊕ l) (l ⊕ l) ℤ) (.inr i) (.inl j) := by
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Matrix.ext_iff.symm

lemma Gamma_le_Gamma0 : Gamma l N ≤ Gamma0 l N := fun A hA ↦ by
  refine mem_Gamma0_iff.mpr fun i j ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp ?_
  simpa using congrFun (congrFun (mem_Gamma_iff.mp hA) (.inr i)) (.inl j)

variable (d : l → ℕ+)

/-- The integral alternating matrix `T = (0, d; -d, 0)` of a type `d = diag(d₁, …, d_g)`. -/
def paramodularForm : Matrix (l ⊕ l) (l ⊕ l) ℤ :=
  fromBlocks 0 (diagonal fun i ↦ ((d i : ℕ) : ℤ)) (-diagonal fun i ↦ ((d i : ℕ) : ℤ)) 0

/-- The **paramodular group** (LMFDB `paramodulargroup.sp2gr`) `{γ ∈ GL(2g, ℤ) : γᵀ T γ = T}` of
type `d`, the integral isometry group of `T = (0, d; -d, 0)`. The LMFDB normalises the type by
`d₁ ∣ d₂ ∣ ⋯ ∣ d_g`, which the definition does not need. -/
def paramodularGL : Subgroup (GL (l ⊕ l) ℤ) where
  carrier := {γ | (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ)ᵀ * paramodularForm d * γ = paramodularForm d}
  mul_mem' {γ δ} hγ hδ := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at hγ hδ ⊢
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ),
      Matrix.mul_assoc (δ : Matrix (l ⊕ l) (l ⊕ l) ℤ)ᵀ,
      ← Matrix.mul_assoc _ _ (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ), hγ, hδ]
  one_mem' := by
    simp
  inv_mem' {γ} hγ := by
    simp only [Set.mem_ofPred_eq] at hγ ⊢
    conv_lhs => rw [← hγ]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Units.mul_inv, transpose_one,
      Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- The rational matrix `δ = diag(1_g, d)` conjugating the paramodular group of type `d` into
`Sp(2g, ℚ)`. -/
def paramodularDelta : Matrix (l ⊕ l) (l ⊕ l) ℚ :=
  fromBlocks 1 0 0 (diagonal fun i ↦ ((d i : ℕ) : ℚ))

/-- The inverse `δ⁻¹ = diag(1_g, d⁻¹)` of `paramodularDelta d`. -/
def paramodularDeltaInv : Matrix (l ⊕ l) (l ⊕ l) ℚ :=
  fromBlocks 1 0 0 (diagonal fun i ↦ ((d i : ℕ) : ℚ)⁻¹)

lemma paramodularDelta_mul_paramodularDeltaInv :
    paramodularDelta d * paramodularDeltaInv d = 1 := by
  simp [paramodularDelta, paramodularDeltaInv, fromBlocks_multiply]

lemma paramodularDeltaInv_mul_paramodularDelta :
    paramodularDeltaInv d * paramodularDelta d = 1 := by
  simp [paramodularDelta, paramodularDeltaInv, fromBlocks_multiply]

omit [Fintype l] in
lemma transpose_paramodularDelta : (paramodularDelta d)ᵀ = paramodularDelta d := by
  simp [paramodularDelta, fromBlocks_transpose]

omit [Fintype l] in
lemma transpose_paramodularDeltaInv : (paramodularDeltaInv d)ᵀ = paramodularDeltaInv d := by
  simp [paramodularDeltaInv, fromBlocks_transpose]

lemma paramodularDelta_mul_J_mul_paramodularDelta : paramodularDelta d * J l ℚ *
    paramodularDelta d = -(paramodularForm d).map (Int.castRingHom ℚ) := by
  simp [paramodularDelta, paramodularForm, J, fromBlocks_multiply, fromBlocks_map, fromBlocks_neg]

private lemma paramodularDelta_mul_mul_mem_aux {Γ : Matrix (l ⊕ l) (l ⊕ l) ℚ}
    (hΓ : Γᵀ * (paramodularForm d).map (Int.castRingHom ℚ) * Γ =
      (paramodularForm d).map (Int.castRingHom ℚ)) :
    paramodularDelta d * Γ * paramodularDeltaInv d ∈ symplecticGroup l ℚ := by
  have e : paramodularDeltaInv d * (Γᵀ * paramodularDelta d) * J l ℚ *
      (paramodularDelta d * Γ * paramodularDeltaInv d) = paramodularDeltaInv d *
      (Γᵀ * (paramodularDelta d * J l ℚ * paramodularDelta d) * Γ) * paramodularDeltaInv d := by
    simp only [Matrix.mul_assoc]
  rw [mem_iff', transpose_mul, transpose_mul, transpose_paramodularDelta,
    transpose_paramodularDeltaInv, e, paramodularDelta_mul_J_mul_paramodularDelta, Matrix.mul_neg,
    Matrix.neg_mul, hΓ, ← paramodularDelta_mul_J_mul_paramodularDelta, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, paramodularDeltaInv_mul_paramodularDelta, Matrix.one_mul,
    Matrix.mul_assoc, paramodularDelta_mul_paramodularDeltaInv, Matrix.mul_one]

/-- **The conjugate of the paramodular group lies in `Sp(2g, ℚ)`**: if `γᵀ T γ = T`, then
`δ γ δ⁻¹` is symplectic, since `δ J δ = -T` for `δ = diag(1_g, d)`. -/
lemma paramodularDelta_mul_mul_mem {γ : GL (l ⊕ l) ℤ} (hγ : γ ∈ paramodularGL d) :
    paramodularDelta d * (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).map (Int.castRingHom ℚ) *
      paramodularDeltaInv d ∈ symplecticGroup l ℚ := by
  refine paramodularDelta_mul_mul_mem_aux d ?_
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congrArg (Matrix.map · (Int.castRingHom ℚ)) hγ

/-- The conjugation `γ ↦ δ γ δ⁻¹` by `δ = diag(1_g, d)`, from the paramodular group of type `d`
into `Sp(2g, ℚ)`. -/
def paramodularConj : paramodularGL d →* symplecticGroup l ℚ where
  toFun γ := ⟨paramodularDelta d *
    ((γ : GL (l ⊕ l) ℤ) : Matrix (l ⊕ l) (l ⊕ l) ℤ).map (Int.castRingHom ℚ) *
    paramodularDeltaInv d, paramodularDelta_mul_mul_mem d γ.2⟩
  map_one' := Subtype.ext <| by
    simp [paramodularDelta_mul_paramodularDeltaInv]
  map_mul' γ γ' := Subtype.ext <| by
    have h : ∀ X : Matrix (l ⊕ l) (l ⊕ l) ℚ,
        paramodularDeltaInv d * (paramodularDelta d * X) = X := fun X ↦ by
      rw [← Matrix.mul_assoc, paramodularDeltaInv_mul_paramodularDelta, Matrix.one_mul]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]
    simp [Matrix.mul_assoc, h]

/-- The **paramodular group** `Γ^para(d) = δ Γ δ⁻¹ ⊆ Sp(2g, ℚ)` (LMFDB `paramodulargroup.sp2gr`,
`mf.siegel.family`) of type `d`, where `Γ = {γ ∈ GL(2g, ℤ) : γᵀ T γ = T}` is `paramodularGL d` and
`δ = diag(1_g, d)`. In degree `2`, `K(N) = Γ^para(1, N)` is the paramodular group of level `N`
(LMFDB `group.paramodular`). -/
def paramodular : Subgroup (symplecticGroup l ℚ) :=
  (paramodularConj d).range

lemma mem_paramodular_iff {M : symplecticGroup l ℚ} : M ∈ paramodular d ↔ ∃ γ ∈ paramodularGL d,
    (M : Matrix (l ⊕ l) (l ⊕ l) ℚ) = paramodularDelta d *
      (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ).map (Int.castRingHom ℚ) * paramodularDeltaInv d :=
  ⟨fun ⟨γ, h⟩ ↦ ⟨γ, γ.2, (congrArg Subtype.val h).symm⟩,
    fun ⟨γ, hγ, h⟩ ↦ ⟨⟨γ, hγ⟩, Subtype.ext h.symm⟩⟩

end SymplecticGroup
