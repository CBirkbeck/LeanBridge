import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Level

/-!
# Paramodular groups are arithmetic

The paramodular group `Γ^para(d) = δ Γ_d δ⁻¹ ⊆ Sp(2g, ℚ)` of type `d = (d₁, …, d_g)`, with
`δ = diag(1_g, d)` and `Γ_d` the integral isometry group of `T = (0, d; -d, 0)`, is commensurable
with `Sp(2g, ℤ)`. With `D = d₁ ⋯ d_g`: an element `γ = 1 + D E` of the principal congruence
subgroup `Γ(D)` is `δ (1 + (D δ⁻¹) E δ) δ⁻¹`, where `D δ⁻¹` is integral, so `Γ(D) ⊆ Γ^para(d)`; and
for `γ = 1 + D E ∈ Γ_d`, `δ γ δ⁻¹ = 1 + δ E (D δ⁻¹)` is integral, so the conjugate of the kernel of
reduction modulo `D` on `Γ_d`, of finite index, lies in `Sp(2g, ℤ)`.

## Main results

* `SymplecticGroup.isCongruenceOfLevel_paramodular`: `Γ^para(d)` contains `Γ(d₁ ⋯ d_g)`.
* `SymplecticGroup.isArithmetic_paramodular`: `Γ^para(d)` is arithmetic.
-/

open Matrix Subgroup

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] {N : ℕ} {E M : Matrix (l ⊕ l) (l ⊕ l) ℤ}

private lemma eq_one_add_smul (hM : M.map (Int.cast : ℤ → ZMod N) = 1) :
    M = 1 + (N : ℤ) • (M - 1).map (· / (N : ℤ)) := by
  have h (i j : l ⊕ l) : (N : ℤ) ∣ (M - 1) i j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← map_apply (f := Int.cast),
      Matrix.map_sub _ Int.cast_sub, hM, Matrix.map_one _ Int.cast_zero Int.cast_one, sub_self,
      Matrix.zero_apply]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, map_apply, smul_eq_mul, Int.mul_ediv_cancel' (h i j),
    Matrix.sub_apply, add_sub_cancel]

variable [Fintype l] (d : l → ℕ+) (N)

/-- The integral matrix `δ = diag(1_g, d)`. -/
private def deltaZ : Matrix (l ⊕ l) (l ⊕ l) ℤ :=
  fromBlocks 1 0 0 (diagonal fun i ↦ ((d i : ℕ) : ℤ))

/-- The integral matrix `N δ⁻¹ = diag(N 1_g, N / d)`, for `d₁, …, d_g` dividing `N`. -/
private def coDeltaZ : Matrix (l ⊕ l) (l ⊕ l) ℤ :=
  fromBlocks (diagonal fun _ ↦ (N : ℤ)) 0 0 (diagonal fun i ↦ ((N / (d i : ℕ) : ℕ) : ℤ))

private lemma map_deltaZ : (Int.castRingHom ℚ).mapMatrix (deltaZ d) = paramodularDelta d := by
  simp [deltaZ, paramodularDelta, fromBlocks_map]

private lemma map_coDeltaZ (hd : ∀ i, (d i : ℕ) ∣ N) :
    (Int.castRingHom ℚ).mapMatrix (coDeltaZ N d) = (N : ℚ) • paramodularDeltaInv d := by
  ext (i | i) (j | j) <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [coDeltaZ, paramodularDeltaInv, div_eq_mul_inv, *]

variable {d N}

private lemma inv_conj_one_add_smul (hd : ∀ i, (d i : ℕ) ∣ N) :
    paramodularDeltaInv d * (Int.castRingHom ℚ).mapMatrix (1 + (N : ℤ) • E) * paramodularDelta d =
      (Int.castRingHom ℚ).mapMatrix (1 + coDeltaZ N d * E * deltaZ d) := by
  rw [map_add, map_add, map_one, map_zsmul, map_mul, map_mul, map_coDeltaZ N d hd,
    map_deltaZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    paramodularDeltaInv_mul_paramodularDelta]
  simp [← Int.cast_smul_eq_zsmul ℚ]

private lemma conj_one_add_smul (hd : ∀ i, (d i : ℕ) ∣ N) :
    paramodularDelta d * (Int.castRingHom ℚ).mapMatrix (1 + (N : ℤ) • E) * paramodularDeltaInv d =
      (Int.castRingHom ℚ).mapMatrix (1 + deltaZ d * E * coDeltaZ N d) := by
  rw [map_add, map_add, map_one, map_zsmul, map_mul, map_mul, map_coDeltaZ N d hd,
    map_deltaZ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    paramodularDelta_mul_paramodularDeltaInv]
  simp [← Int.cast_smul_eq_zsmul ℚ]

private lemma inv_conj_mem_range (hd : ∀ i, (d i : ℕ) ∣ N)
    (hM : M.map (Int.cast : ℤ → ZMod N) = 1) :
    paramodularDeltaInv d * (Int.castRingHom ℚ).mapMatrix M * paramodularDelta d ∈
      (Int.castRingHom ℚ).mapMatrix.range := by
  rw [eq_one_add_smul hM, inv_conj_one_add_smul hd]
  exact ⟨_, rfl⟩

private lemma conj_mem_range (hd : ∀ i, (d i : ℕ) ∣ N) (hM : M.map (Int.cast : ℤ → ZMod N) = 1) :
    paramodularDelta d * (Int.castRingHom ℚ).mapMatrix M * paramodularDeltaInv d ∈
      (Int.castRingHom ℚ).mapMatrix.range := by
  rw [eq_one_add_smul hM, conj_one_add_smul hd]
  exact ⟨_, rfl⟩

private lemma mapMatrix_injective :
    Function.Injective ((Int.castRingHom ℚ).mapMatrix : Matrix (l ⊕ l) (l ⊕ l) ℤ → _) :=
  Matrix.map_injective Int.cast_injective

private lemma mem_symplecticGroup_of_map
    (hM : (Int.castRingHom ℚ).mapMatrix M ∈ symplecticGroup l ℚ) : M ∈ symplecticGroup l ℤ := by
  rw [mem_iff'] at hM ⊢
  refine mapMatrix_injective ?_
  simp only [map_mul, RingHom.mapMatrix_apply, map_J]
  exact hM

variable (d) in
private lemma inv_conj_mul_inv_conj (X Y : Matrix (l ⊕ l) (l ⊕ l) ℚ) :
    paramodularDeltaInv d * X * paramodularDelta d *
      (paramodularDeltaInv d * Y * paramodularDelta d) =
        paramodularDeltaInv d * (X * Y) * paramodularDelta d := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (paramodularDelta d), paramodularDelta_mul_paramodularDeltaInv,
    Matrix.one_mul]

private lemma mul_eq_one_of_inv_conj {X Y A B : Matrix (l ⊕ l) (l ⊕ l) ℤ}
    (hX : (Int.castRingHom ℚ).mapMatrix X =
      paramodularDeltaInv d * (Int.castRingHom ℚ).mapMatrix A * paramodularDelta d)
    (hY : (Int.castRingHom ℚ).mapMatrix Y =
      paramodularDeltaInv d * (Int.castRingHom ℚ).mapMatrix B * paramodularDelta d)
    (hAB : A * B = 1) : X * Y = 1 :=
  mapMatrix_injective <| by
    rw [map_mul, hX, hY, inv_conj_mul_inv_conj, ← map_mul, hAB, map_one, Matrix.mul_one,
      paramodularDeltaInv_mul_paramodularDelta]

private lemma transpose_inv_conj_mul_mul_inv_conj {X : Matrix (l ⊕ l) (l ⊕ l) ℚ}
    (hX : X ∈ symplecticGroup l ℚ) :
    letI Y : Matrix (l ⊕ l) (l ⊕ l) ℚ := paramodularDeltaInv d * X * paramodularDelta d
    Yᵀ * (paramodularForm d).map (Int.castRingHom ℚ) * Y =
      (paramodularForm d).map (Int.castRingHom ℚ) := by
  rw [← neg_neg ((paramodularForm d).map (Int.castRingHom ℚ)),
    ← paramodularDelta_mul_J_mul_paramodularDelta]
  simp only [transpose_mul, transpose_paramodularDelta, transpose_paramodularDeltaInv,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (paramodularDeltaInv d) (paramodularDelta d),
    paramodularDeltaInv_mul_paramodularDelta, Matrix.one_mul,
    ← Matrix.mul_assoc (paramodularDelta d) (paramodularDeltaInv d),
    paramodularDelta_mul_paramodularDeltaInv, Matrix.one_mul, ← Matrix.mul_assoc (J l ℚ),
    ← Matrix.mul_assoc Xᵀ, ← Matrix.mul_assoc Xᵀ, mem_iff'.mp hX]

/-- **The paramodular group of type `d` is a congruence subgroup of level `N`** for every `N`
divisible by `d₁, …, d_g`: it contains `Γ(N)`, since `γ = 1 + N E ∈ Γ(N)` is
`δ (1 + (N δ⁻¹) E δ) δ⁻¹` with `N δ⁻¹` integral. -/
lemma isCongruenceOfLevel_paramodular (hd : ∀ i, (d i : ℕ) ∣ N) :
    IsCongruenceOfLevel N (paramodular d) := by
  rintro _ ⟨γ, hγ, rfl⟩
  rcases inv_conj_mem_range hd (mem_Gamma_iff.mp hγ) with ⟨X, hX⟩
  rcases inv_conj_mem_range hd (mem_Gamma_iff.mp (inv_mem hγ)) with ⟨Y, hY⟩
  refine (mem_paramodular_iff d).mpr ⟨⟨X, Y, mul_eq_one_of_inv_conj hX hY ?_,
    mul_eq_one_of_inv_conj hY hX ?_⟩, mapMatrix_injective ?_, ?_⟩
  · exact congrArg Subtype.val (mul_inv_cancel γ)
  · exact congrArg Subtype.val (inv_mul_cancel γ)
  · rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := Xᵀ), transpose_map,
      ← RingHom.mapMatrix_apply, hX]
    exact transpose_inv_conj_mul_mul_inv_conj (map (Int.castRingHom ℚ) γ).2
  · rw [coe_map_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, hX]
    simp only [Matrix.mul_assoc]
    rw [paramodularDelta_mul_paramodularDeltaInv, Matrix.mul_one, ← Matrix.mul_assoc,
      paramodularDelta_mul_paramodularDeltaInv, Matrix.one_mul]

variable (d N) in
/-- The reduction modulo `N` on the integral isometry group `Γ_d` of `T = (0, d; -d, 0)`. -/
private def paramodularReduction : paramodularGL d →* GL (l ⊕ l) (ZMod N) :=
  (Units.map (Int.castRingHom (ZMod N)).mapMatrix.toMonoidHom).comp (paramodularGL d).subtype

private lemma ker_paramodularReduction_le (hd : ∀ i, (d i : ℕ) ∣ N) :
    (paramodularReduction N d).ker ≤ (integral l).comap (paramodularConj d) := by
  intro γ hγ
  have hγ' : ((γ : GL (l ⊕ l) ℤ) : Matrix (l ⊕ l) (l ⊕ l) ℤ).map (Int.cast : ℤ → ZMod N) = 1 :=
    congrArg Units.val hγ
  rcases conj_mem_range hd hγ' with ⟨X, hX⟩
  have hmem : (Int.castRingHom ℚ).mapMatrix X ∈ symplecticGroup l ℚ := by
    rw [hX]
    exact paramodularDelta_mul_mul_mem d γ.2
  refine ⟨⟨X, mem_symplecticGroup_of_map hmem⟩, trivial, Subtype.ext ?_⟩
  rw [coe_map_apply, ← RingHom.mapMatrix_apply, hX]
  rfl

variable (d) in
/-- **Paramodular groups are arithmetic**: `Γ^para(d)` is commensurable with `Sp(2g, ℤ)`. It
contains `Γ(D)` for `D = d₁ ⋯ d_g` (`SymplecticGroup.isCongruenceOfLevel_paramodular`), of finite
index in `Sp(2g, ℤ)`; and its intersection with `Sp(2g, ℤ)` contains the conjugate `δ Γ_d(D) δ⁻¹`
of the kernel of the reduction modulo `D` on `Γ_d`, of finite index in `Γ^para(d) = δ Γ_d δ⁻¹`. -/
lemma isArithmetic_paramodular : IsArithmetic (paramodular d) := by
  have hd (i : l) : (d i : ℕ) ∣ ∏ j, (d j : ℕ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have : NeZero (∏ j, (d j : ℕ)) := ⟨Finset.prod_ne_zero_iff.mpr fun j _ ↦ (d j).ne_zero⟩
  have hinj : Function.Injective (map (l := l) (Int.castRingHom ℚ)) := fun _ _ h ↦
    Subtype.ext <| mapMatrix_injective <| congrArg Subtype.val h
  have : ((Gamma l (∏ j, (d j : ℕ))).map (map (Int.castRingHom ℚ))).IsFiniteRelIndex
      (integral l) := by
    refine ⟨?_⟩
    rw [integral, relIndex_map_map_of_injective _ _ hinj, relIndex_top_right]
    exact (finiteIndex_ker _).index_ne_zero
  refine ⟨isFiniteRelIndex_of_le_left _ (isCongruenceOfLevel_paramodular hd), ⟨?_⟩⟩
  rw [paramodular, ← index_comap]
  exact ne_zero_of_dvd_ne_zero (finiteIndex_ker (paramodularReduction _ d)).index_ne_zero
    (index_dvd_of_le (ker_paramodularReduction_le hd))

end SymplecticGroup
