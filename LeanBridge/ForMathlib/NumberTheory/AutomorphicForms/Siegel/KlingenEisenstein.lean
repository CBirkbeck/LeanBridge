import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm

/-!
# Klingen Eisenstein series

For `0 ≤ r ≤ n` and a function `f` on the Siegel upper half-space `ℋ_r` of degree `r`, the Klingen
Eisenstein series of weight `k` is
`E_{n,r}(f)(Z) = ∑_{γ ∈ P_{n,r} \ Sp(2n, ℤ)} f((γZ)*) det(CZ + D)^{-k}` on `ℋ_n`, where `W*` is the
upper-left `r × r` block of `W` and `P_{n,r}` is the Klingen parabolic subgroup of the
`γ = (a₁, 0, b₁, b₂; a₃, u, b₃, b₄; c₁, 0, d₁, d₂; 0, 0, 0, v)` (blocks of sizes `r` and `n - r`).
For `γ ∈ P_{n,r}`, `(γZ)* = γ*Z*` with `γ* = (a₁, b₁; c₁, d₁) ∈ Sp(2r)`, and
`det(CZ + D) = det(c₁Z* + d₁) det v`; so for a modular form `f` of even weight `k` the terms only
depend on the cosets `P_{n,r} γ`. Here `ℋ_n` is indexed by `l ⊕ m` with `|l| = r`, `|m| = n - r`.

Klingen proved that for a cusp form `f` of even weight `k > n + r + 1` the series converges
absolutely to a Siegel modular form of degree `n` with `Φ^{n-r}(E_{n,r}(f)) = f`, the property by
which the LMFDB knowl characterises it; this is not proved here.

## Main definitions

* `SymplecticGroup.klingenParabolic`: the Klingen parabolic subgroup `P_{n,r}` of `Sp(2n, R)`.
* `SymplecticGroup.klingenProj`: the homomorphism `γ ↦ γ*` from `P_{n,r}` to `Sp(2r, R)`.
* `SymplecticGroup.klingenV`: the block `v` of `γ ∈ P_{n,r}`.
* `SymplecticGroup.KlingenCosets`: the right cosets `P_{n,r} \ Sp(2n, ℤ)`.
* `SiegelUpperHalfSpace.upperLeft`: the upper-left block `Z* ∈ ℋ_r` of `Z ∈ ℋ_n`.
* `SiegelUpperHalfSpace.klingenTerm`: the term `f((γZ)*) det(CZ + D)^{-k}`.
* `SiegelUpperHalfSpace.klingenEisensteinSeries` (LMFDB `mf.siegel.klingen_eisenstein_series`): the
  Klingen Eisenstein series `E_{n,r}(f)`.

## Main results

* `SiegelUpperHalfSpace.det_denom_klingen`: `det(CZ + D) = det(c₁Z* + d₁) det v` on `P_{n,r}`.
* `SiegelUpperHalfSpace.upperLeft_smul`: `(γZ)* = γ*Z*` on `P_{n,r}`.
* `SiegelUpperHalfSpace.klingenTerm_mul`: for `f` of even weight `k` under `Sp(2r, ℤ)`, the terms
  of the series only depend on the cosets of `P_{n,r}`.
-/

open Matrix

namespace SymplecticGroup

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m] {R : Type*}
    [CommRing R]

variable (l m R) in
/-- The **Klingen parabolic subgroup** `P_{n,r}` of `Sp(2n, R)`, `n = |l| + |m|`, `r = |l|`: the
`γ` whose rows of index `(2, m)` are `(0, 0 | 0, V)` and whose columns of index `(1, m)` are
`(0; U; 0; 0)`, in the block decomposition along `(l ⊕ m) ⊕ (l ⊕ m)`; it is the stabiliser of the
isotropic subspace spanned by the basis vectors of index `(1, m)`. Klingen's `Δ_{n,r}` is defined by
the condition on the rows alone, which implies that on the columns for symplectic matrices (not
proved here). -/
def klingenParabolic : Subgroup (symplecticGroup (l ⊕ m) R) where
  carrier := {γ | ∀ j : m, (∀ x, γ.1 (.inr (.inr j)) (.inl x) = 0) ∧
    (∀ i, γ.1 (.inr (.inr j)) (.inr (.inl i)) = 0) ∧
      (∀ i, γ.1 (.inl (.inl i)) (.inl (.inr j)) = 0) ∧ ∀ x, γ.1 (.inr x) (.inl (.inr j)) = 0}
  mul_mem' {γ δ} hγ hδ j := by
    refine ⟨fun x ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩ <;>
      simp [Matrix.mul_apply, (hγ _).1, (hγ _).2.1, (hγ _).2.2.1, (hγ _).2.2.2, (hδ _).1,
        (hδ _).2.1, (hδ _).2.2.1, (hδ _).2.2.2]
  one_mem' j := by
    simp
  inv_mem' {γ} hγ j := by
    refine ⟨fun x ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩ <;>
      simp [coe_inv, J, Matrix.mul_apply, (hγ _).1, (hγ _).2.1, (hγ _).2.2.1, (hγ _).2.2.2]

variable (γ : klingenParabolic l m R)

lemma klingenParabolic_submatrix_mem :
    γ.1.1.submatrix (Sum.map .inl .inl) (Sum.map .inl .inl) ∈ symplecticGroup l R := by
  rw [mem_iff']
  ext x y
  have h : (γ.1.1ᵀ * J (l ⊕ m) R * γ.1.1) (Sum.map .inl .inl x) (Sum.map .inl .inl y) =
      J (l ⊕ m) R (Sum.map .inl .inl x) (Sum.map .inl .inl y) :=
    congrFun (congrFun (mem_iff'.mp γ.1.2) _) _
  rcases x with x | x <;> rcases y with y | y <;>
    simpa [J, Matrix.mul_apply, one_apply, (γ.2 _).1, (γ.2 _).2.1] using h

variable (l m R) in
/-- The projection `γ ↦ γ*` from the Klingen parabolic subgroup of `Sp(2n, R)` to `Sp(2r, R)`: for
`γ = (a₁, 0, b₁, b₂; a₃, u, b₃, b₄; c₁, 0, d₁, d₂; 0, 0, 0, v)`, `γ* = (a₁, b₁; c₁, d₁)`. -/
def klingenProj : klingenParabolic l m R →* symplecticGroup l R where
  toFun γ := ⟨_, klingenParabolic_submatrix_mem γ⟩
  map_one' := Subtype.ext <| by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> simp [one_apply]
  map_mul' γ δ := Subtype.ext <| by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;>
      simp [Matrix.mul_apply, (γ.2 _).2.2.1, (γ.2 _).2.2.2, (δ.2 _).1, (δ.2 _).2.1]

/-- The block `v = (γ_{(2,j),(2,j')})` of an element `γ` of the Klingen parabolic subgroup. -/
def klingenV : Matrix m m R :=
  γ.1.1.submatrix (.inr ∘ .inr) (.inr ∘ .inr)

lemma transpose_mul_klingenV : (γ.1.1.submatrix (.inl ∘ .inr) (.inl ∘ .inr))ᵀ * klingenV γ = 1 := by
  ext j j'
  simpa [klingenV, J, Matrix.mul_apply, one_apply, (γ.2 _).2.2.1, (γ.2 _).2.2.2] using
    congrFun (congrFun (mem_iff'.mp γ.1.2) (.inl (.inr j))) (.inr (.inr j'))

variable (l m) in
/-- The right cosets `P_{n,r} γ` of the Klingen parabolic subgroup `P_{n,r}` in `Sp(2n, ℤ)`, over
which the Klingen Eisenstein series is summed. -/
abbrev KlingenCosets : Type _ :=
  Quotient (QuotientGroup.rightRel (klingenParabolic l m ℤ))

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    (Z : SiegelUpperHalfSpace (l ⊕ m)) (γ : SymplecticGroup.klingenParabolic l m ℤ) (i i' : l)
    (j j' : m)

/-- The upper-left block `Z*` of `Z ∈ ℋ_n`, an element of `ℋ_r`, `r = |l|`. -/
def upperLeft : SiegelUpperHalfSpace l where
  val := Z.val.toBlocks₁₁
  transpose_val := by
    ext x y
    simpa [toBlocks₁₁] using congrFun (congrFun Z.transpose_val (.inl x)) (.inl y)
  posDef_im := Z.posDef_im.submatrix Sum.inl_injective

private lemma denom_inr_inl :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val (.inr j) (.inl i) = 0 := by
  simp [denom, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, (γ.2 _).1, (γ.2 _).2.1]

private lemma denom_inl_inl :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val (.inl i) (.inl i') =
      denom (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
        (upperLeft Z).val i i' := by
  simp [denom, upperLeft, SymplecticGroup.klingenProj, toBlocks₁₁, toBlocks₂₁, toBlocks₂₂,
    Matrix.mul_apply, (γ.2 _).2.2.2]

private lemma num_inl_inl :
    num (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val (.inl i) (.inl i') =
      num (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
        (upperLeft Z).val i i' := by
  simp [num, upperLeft, SymplecticGroup.klingenProj, toBlocks₁₁, toBlocks₁₂, Matrix.mul_apply,
    (γ.2 _).2.2.1]

private lemma denom_inr_inr :
    denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val (.inr j) (.inr j') =
      SymplecticGroup.klingenV γ j j' := by
  simp [denom, SymplecticGroup.klingenV, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, (γ.2 _).1]

/-- **The automorphy factor of the Klingen parabolic splits**: for `γ` in the Klingen parabolic
subgroup, `det(CZ + D) = det(c₁Z* + d₁) det v`, where `γ* = (a₁, b₁; c₁, d₁)` and `Z*` is the
upper-left block of `Z`. -/
lemma det_denom_klingen : (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val).det =
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
      (upperLeft Z).val).det * ((SymplecticGroup.klingenV γ).det : ℂ) := by
  have h : denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val = fromBlocks
      (denom (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
        (upperLeft Z).val) (denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val).toBlocks₁₂ 0
      ((SymplecticGroup.klingenV γ).map (Int.castRingHom ℂ)) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y
    · exact denom_inl_inl Z γ x y
    · rfl
    · exact denom_inr_inl Z γ y x
    · simpa using denom_inr_inr Z γ x y
  rw [h, det_fromBlocks_zero₂₁, ← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_intCast]

/-- **The Klingen parabolic acts on the upper-left block through `γ ↦ γ*`**: for `γ` in the
Klingen parabolic subgroup, `(γZ)* = γ* Z*`. -/
lemma upperLeft_smul :
    upperLeft (SymplecticGroup.map (Int.castRingHom ℝ) (γ : symplecticGroup (l ⊕ m) ℤ) • Z) =
      SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ) •
        upperLeft Z := by
  have hW : (SymplecticGroup.map (Int.castRingHom ℝ) (γ : symplecticGroup (l ⊕ m) ℤ) • Z).val *
      denom (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val =
        num (SymplecticGroup.map (Int.castRingHom ℝ) γ) Z.val := by
    rw [val_smul, nonsing_inv_mul_cancel_right _ _ (isUnit_det_denom _ Z)]
  have h₁₁ : (upperLeft (SymplecticGroup.map (Int.castRingHom ℝ) γ.1 • Z)).val *
      denom (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
        (upperLeft Z).val =
      num (SymplecticGroup.map (Int.castRingHom ℝ) (SymplecticGroup.klingenProj l m ℤ γ))
        (upperLeft Z).val := by
    ext x x'
    simpa [Matrix.mul_apply, denom_inl_inl, denom_inr_inl, num_inl_inl, upperLeft, toBlocks₁₁] using
      congrFun (congrFun hW (.inl x)) (.inl x')
  ext : 1
  rw [val_smul, ← h₁₁, mul_nonsing_inv_cancel_right _ _ (isUnit_det_denom _ _)]

variable (k : ℤ) (f : SiegelUpperHalfSpace l → ℂ) (δ : symplecticGroup (l ⊕ m) ℤ)

/-- The term `f((γZ)*) det(CZ + D)^{-k}` of the Klingen Eisenstein series of `f : ℋ_r → ℂ`, for
`γ = (A, B; C, D) ∈ Sp(2n, ℤ)` and `Z ∈ ℋ_n`, where `W*` is the upper-left block of `W`. -/
noncomputable def klingenTerm : ℂ :=
  f (upperLeft (SymplecticGroup.map (Int.castRingHom ℝ) δ • Z)) *
    (denom (SymplecticGroup.map (Int.castRingHom ℝ) δ) Z.val).det ^ (-k)

/-- **The terms of the Klingen Eisenstein series only depend on the coset `P δ`** of the Klingen
parabolic subgroup `P`, for `f` of even weight `k` under `Sp(2r, ℤ)`: for `γ ∈ P`, `f((γδZ)*) =
f(γ* (δZ)*) = det(c₁(δZ)* + d₁)^k f((δZ)*)` and `det(C_{γδ}Z + D_{γδ}) = det(c₁(δZ)* + d₁) det v
det(C_δ Z + D_δ)`, with `det v = ±1`. -/
lemma klingenTerm_mul (hk : Even k) (hf : ∀ (β : symplecticGroup l ℤ) (τ : SiegelUpperHalfSpace l),
    f (SymplecticGroup.map (Int.castRingHom ℝ) β • τ) =
      (denom (SymplecticGroup.map (Int.castRingHom ℝ) β) τ.val).det ^ k * f τ) :
    klingenTerm Z k f ((γ : symplecticGroup (l ⊕ m) ℤ) * δ) = klingenTerm Z k f δ := by
  have hv : ((SymplecticGroup.klingenV γ).det : ℂ) ^ (-k) = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_det_of_left_inverse (SymplecticGroup.transpose_mul_klingenV γ))
      with h | h <;> simp [h, hk.neg.neg_one_zpow]
  have key (a b c : ℂ) (ha : a ≠ 0) : a ^ k * b * (a ^ (-k) * c) = b * c := by
    rw [mul_comm (a ^ k) b, mul_assoc, ← mul_assoc (a ^ k), ← zpow_add₀ ha, add_neg_cancel,
      zpow_zero, one_mul]
  rw [klingenTerm, klingenTerm, map_mul, mul_smul, upperLeft_smul, hf, denom_mul, det_mul,
    det_denom_klingen, mul_zpow, mul_zpow, hv, mul_one]
  exact key _ _ _ (isUnit_det_denom _ _).ne_zero

/-- The **Klingen Eisenstein series** `E_{n,r}(f)` (LMFDB `mf.siegel.klingen_eisenstein_series`) of
`f : ℋ_r → ℂ` of weight `k`:
`E_{n,r}(f)(Z) = ∑_{γ ∈ P_{n,r} \ Sp(2n, ℤ)} f((γZ)*) det(CZ + D)^{-k}`, the sum over the cosets
of the Klingen parabolic subgroup `P_{n,r}`, with chosen representatives; for a modular form `f`
of even weight the terms do not depend on them (`klingenTerm_mul`). For a cusp form `f` of degree
`r` and even weight `k > n + r + 1` the series converges absolutely to a Siegel modular form of
degree `n` and weight `k` with `Φ^{n-r}(E_{n,r}(f)) = f`, which is how the knowl characterises it
(Klingen); this is not proved here. The `tsum` is the sum of the series wherever it converges
absolutely, so in particular for those `f` and `k`, and is the junk value `0` elsewhere. The
knowl's characterisation does not determine `E_{n,r}(f)` (adding a cusp form preserves it) and
needs `k` even: for odd `k` and `r < n`, no Siegel modular form `F` of degree `n` has
`Φ^{n-r} F ≠ 0`. For `r = 0` and `f = 1` this is the Siegel Eisenstein series. -/
noncomputable def klingenEisensteinSeries : ℂ :=
  ∑' x : SymplecticGroup.KlingenCosets l m, klingenTerm Z k f x.out

lemma klingenTerm_out (hk : Even k) (hf : ∀ (β : symplecticGroup l ℤ) (τ : SiegelUpperHalfSpace l),
    f (SymplecticGroup.map (Int.castRingHom ℝ) β • τ) =
      (denom (SymplecticGroup.map (Int.castRingHom ℝ) β) τ.val).det ^ k * f τ) :
    klingenTerm Z k f (⟦δ⟧ : SymplecticGroup.KlingenCosets l m).out = klingenTerm Z k f δ := by
  have h : δ * (⟦δ⟧ : SymplecticGroup.KlingenCosets l m).out⁻¹ ∈
      SymplecticGroup.klingenParabolic l m ℤ :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out δ)
  conv_rhs => rw [← inv_mul_cancel_right δ (⟦δ⟧ : SymplecticGroup.KlingenCosets l m).out]
  exact (klingenTerm_mul Z ⟨_, h⟩ k f _ hk hf).symm

end SiegelUpperHalfSpace
