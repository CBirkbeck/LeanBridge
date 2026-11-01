import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoQuotient

/-!
# `Γ₀[2]/Γ[2] ≅ ℤ/2ℤ × S₄`

Reduction modulo 2 identifies `Γ₀[2]/Γ[2]` with the Siegel parabolic subgroup
`P(ℤ/2ℤ) = {(A, B; 0, D)}` of `Sp(4, ℤ/2ℤ)` (`SymplecticGroup.quotientGammaTwoGamma0Equiv`), a
group of order 48. Its element `p = (A, B; 0, D)` factors as `(A, 0; 0, D)(1, S; 0, 1)` with
`D = A⁻ᵀ` and `S = DᵀB` symmetric, and `S_{pq} = D_qᵀ S_p D_q + S_q`. Two homomorphisms come out of
this:

* the sign `p ↦ ℓ(S_p)`, where `ℓ(S) = S₁₁ + S₁₂ + S₂₂`, a linear form on the symmetric matrices
  over `ℤ/2ℤ` invariant under `S ↦ DᵀSD` for invertible `D` (a finite check);
* the affine action `x ↦ A(x + diag S)` of `P(ℤ/2ℤ)` on the plane `(ℤ/2ℤ)²`, a homomorphism into
  the permutations of its four points since `diag(DᵀSD) = Dᵀ diag S` for symmetric `S` over
  `ℤ/2ℤ` (a finite check). It is `x ↦ Ax + diag(ABᵀ)`, the formula of Igusa's action of `p` on
  the four theta characteristics `(0, x)` modulo 2.

Together they give `P(ℤ/2ℤ) ≅ ℤ/2ℤ × S₄`. The kernel is trivial: if `A(x + diag S) = x` for all
`x`, then `A = 1` and `diag S = 0`, so `D = 1`, and `ℓ(S) = 0` forces `S = 0`. Every element of
`ℤ/2ℤ × S₄` arises: the central element `(1, (0, 1; 1, 0); 0, 1)` has nontrivial sign and trivial
affine action, and every transposition of the four points is the affine action of some
`(A, AS; 0, A⁻ᵀ)` with `ℓ(S) = 0` (a finite check), the transpositions generating the symmetric
group. The four points are numbered by an arbitrary bijection with `Fin 4`. Hence
`Γ₀[2]/Γ[2] ≅ ℤ/2ℤ × S₄`, as the knowl `mf.siegel.family.gamma_2` says.

## Main definitions

* `SymplecticGroup.parabolicSym`: the symmetric matrix `S = DᵀB` of `(A, B; 0, D)`.
* `SymplecticGroup.symForm`: the linear form `ℓ(S) = S₁₁ + S₁₂ + S₂₂`.
* `SymplecticGroup.parabolicSign`: the sign `p ↦ ℓ(S_p)` of `P(ℤ/2ℤ)`.
* `SymplecticGroup.parabolicAffine`, `SymplecticGroup.parabolicPerm`,
  `SymplecticGroup.parabolicPermHom`: the affine action `x ↦ A(x + diag S)` of `P(ℤ/2ℤ)` on
  `(ℤ/2ℤ)²`.
* `SymplecticGroup.parabolicHom`: the homomorphism `P(ℤ/2ℤ) → ℤ/2ℤ × Perm((ℤ/2ℤ)²)`.
* `SymplecticGroup.parabolicTwoEquiv`: `P(ℤ/2ℤ) ≅ ℤ/2ℤ × S₄`.
* `SymplecticGroup.quotientGammaTwoGamma0EquivProd`: `Γ₀[2]/Γ[2] ≅ ℤ/2ℤ × S₄`.

## Main results

* `SymplecticGroup.parabolicSym_mul`: `S_{pq} = D_qᵀ S_p D_q + S_q`.
* `SymplecticGroup.injective_parabolicHom`, `SymplecticGroup.surjective_parabolicHom`: the
  homomorphism `P(ℤ/2ℤ) → ℤ/2ℤ × Perm((ℤ/2ℤ)²)` is bijective.
-/

open Equiv Matrix

namespace SymplecticGroup

variable {R : Type*} [CommRing R] (p q : siegelParabolic (Fin 2) R) (M N : Matrix (Fin 2) (Fin 2) R)
    (r s : siegelParabolic (Fin 2) (ZMod 2)) (x : Fin 2 → ZMod 2)
    {A S : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hA : A.det = 1) (hS : Sᵀ = S)

private lemma eq_fromBlocks_of_siegelParabolic :
    p.1.1 = fromBlocks p.1.1.toBlocks₁₁ p.1.1.toBlocks₁₂ 0 p.1.1.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks p.1.1, (p.2 : p.1.1.toBlocks₂₁ = 0)]

private lemma fromBlocks_mem_symplecticGroup :
    fromBlocks p.1.1.toBlocks₁₁ p.1.1.toBlocks₁₂ 0 p.1.1.toBlocks₂₂ ∈ symplecticGroup (Fin 2) R :=
  eq_fromBlocks_of_siegelParabolic p ▸ p.1.2

private lemma transpose_toBlocks₁₁_mul_toBlocks₂₂_eq_one :
    p.1.1.toBlocks₁₁ᵀ * p.1.1.toBlocks₂₂ = 1 := by
  simpa using (fromBlocks_mem_iff.mp (fromBlocks_mem_symplecticGroup p)).2.2

private lemma transpose_toBlocks₂₂_mul_toBlocks₁₁ : p.1.1.toBlocks₂₂ᵀ * p.1.1.toBlocks₁₁ = 1 := by
  rw [← transpose_transpose p.1.1.toBlocks₁₁, ← transpose_mul,
    transpose_toBlocks₁₁_mul_toBlocks₂₂_eq_one p, transpose_one]

private lemma toBlocks₁₁_mul_transpose_toBlocks₂₂_eq_one :
    p.1.1.toBlocks₁₁ * p.1.1.toBlocks₂₂ᵀ = 1 :=
  mul_eq_one_comm.mp (transpose_toBlocks₂₂_mul_toBlocks₁₁ p)

private lemma val_mul_siegelParabolic : (p * q).1.1 = fromBlocks
    (p.1.1.toBlocks₁₁ * q.1.1.toBlocks₁₁)
    (p.1.1.toBlocks₁₁ * q.1.1.toBlocks₁₂ + p.1.1.toBlocks₁₂ * q.1.1.toBlocks₂₂) 0
    (p.1.1.toBlocks₂₂ * q.1.1.toBlocks₂₂) := by
  rw [Subgroup.coe_mul, Submonoid.coe_mul, eq_fromBlocks_of_siegelParabolic p,
    eq_fromBlocks_of_siegelParabolic q, fromBlocks_multiply]
  simp

/-- The symmetric matrix `S = DᵀB` of an element `(A, B; 0, D) = (A, 0; 0, D)(1, S; 0, 1)` of the
Siegel parabolic subgroup of `Sp(4, R)`. -/
def parabolicSym : Matrix (Fin 2) (Fin 2) R :=
  p.1.1.toBlocks₂₂ᵀ * p.1.1.toBlocks₁₂

lemma transpose_parabolicSym : (parabolicSym p)ᵀ = parabolicSym p := by
  rw [parabolicSym, transpose_mul, transpose_transpose,
    (fromBlocks_mem_iff.mp (fromBlocks_mem_symplecticGroup p)).2.1]

/-- **The symmetric part of a product**: `S_{pq} = D_qᵀ S_p D_q + S_q` for elements `p`, `q` of the
Siegel parabolic subgroup, since `D_pᵀ A_p = 1`. -/
lemma parabolicSym_mul : parabolicSym (p * q) =
    q.1.1.toBlocks₂₂ᵀ * parabolicSym p * q.1.1.toBlocks₂₂ + parabolicSym q := by
  rw [parabolicSym, parabolicSym, parabolicSym, val_mul_siegelParabolic, toBlocks_fromBlocks₂₂,
    toBlocks_fromBlocks₁₂, transpose_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc p.1.1.toBlocks₂₂ᵀ p.1.1.toBlocks₁₁, transpose_toBlocks₂₂_mul_toBlocks₁₁,
    Matrix.one_mul, add_comm]
  simp only [Matrix.mul_assoc]

/-- The linear form `ℓ(M) = M₁₁ + M₁₂ + M₂₂` on `2 × 2` matrices. -/
def symForm : R :=
  M 0 0 + M 0 1 + M 1 1

lemma symForm_add : symForm (M + N) = symForm M + symForm N := by
  simp only [symForm, Matrix.add_apply]
  ring1

lemma symForm_transpose_mul_mul : ∀ S D : Matrix (Fin 2) (Fin 2) (ZMod 2), Sᵀ = S → D.det ≠ 0 →
    symForm (Dᵀ * S * D) = symForm S := by
  decide

lemma diag_transpose_mul_mul : ∀ S D : Matrix (Fin 2) (Fin 2) (ZMod 2), Sᵀ = S →
    (Dᵀ * S * D).diag = Dᵀ *ᵥ S.diag := by
  decide

lemma eq_zero_of_symForm_eq_zero : ∀ S : Matrix (Fin 2) (Fin 2) (ZMod 2), Sᵀ = S → S.diag = 0 →
    symForm S = 0 → S = 0 := by
  decide

/-- The **sign** `p ↦ ℓ(S_p)` of the Siegel parabolic subgroup `P(ℤ/2ℤ)` of `Sp(4, ℤ/2ℤ)`, a
homomorphism to `ℤ/2ℤ` (written multiplicatively), nontrivial on the central element
`(1, (0, 1; 1, 0); 0, 1)`. -/
def parabolicSign : siegelParabolic (Fin 2) (ZMod 2) →* Multiplicative (ZMod 2) where
  toFun r := .ofAdd (symForm (parabolicSym r))
  map_one' := by
    simp [parabolicSym, symForm, ← fromBlocks_one]
  map_mul' r s := by
    rw [← ofAdd_add, parabolicSym_mul, symForm_add, symForm_transpose_mul_mul _ _
      (transpose_parabolicSym r) (det_ne_zero_of_left_inverse
        (transpose_toBlocks₁₁_mul_toBlocks₂₂_eq_one s))]

/-- The **affine action** `x ↦ A(x + diag S)` of `(A, B; 0, D) ∈ P(ℤ/2ℤ)` on `(ℤ/2ℤ)²`, where
`S = DᵀB`. It is `x ↦ Ax + diag(ABᵀ)`. -/
def parabolicAffine : Fin 2 → ZMod 2 :=
  r.1.1.toBlocks₁₁ *ᵥ (x + (parabolicSym r).diag)

lemma parabolicAffine_mul :
    parabolicAffine (r * s) x = parabolicAffine r (parabolicAffine s x) := by
  rw [parabolicAffine, parabolicAffine, parabolicAffine, parabolicSym_mul, diag_add,
    diag_transpose_mul_mul _ _ (transpose_parabolicSym r), val_mul_siegelParabolic,
    toBlocks_fromBlocks₁₁, ← mulVec_mulVec]
  congr 1
  rw [mulVec_add, mulVec_add, mulVec_add, mulVec_mulVec,
    toBlocks₁₁_mul_transpose_toBlocks₂₂_eq_one s, one_mulVec]
  abel

lemma parabolicAffine_eq_add_diag :
    parabolicAffine r x = r.1.1.toBlocks₁₁ *ᵥ x + (r.1.1.toBlocks₁₁ * r.1.1.toBlocks₁₂ᵀ).diag := by
  have h : (r.1.1.toBlocks₁₁ * parabolicSym r * r.1.1.toBlocks₁₁ᵀ).diag =
      r.1.1.toBlocks₁₁ *ᵥ (parabolicSym r).diag := by
    simpa using diag_transpose_mul_mul _ r.1.1.toBlocks₁₁ᵀ (transpose_parabolicSym r)
  rw [parabolicAffine, mulVec_add, ← h, parabolicSym, ← Matrix.mul_assoc,
    toBlocks₁₁_mul_transpose_toBlocks₂₂_eq_one, Matrix.one_mul, ← diag_transpose, transpose_mul,
    transpose_transpose]

lemma parabolicAffine_one : parabolicAffine 1 x = x := by
  simp [parabolicAffine, parabolicSym, ← fromBlocks_one]

/-- The permutation `x ↦ A(x + diag S)` of `(ℤ/2ℤ)²` induced by `(A, B; 0, D) ∈ P(ℤ/2ℤ)`. -/
def parabolicPerm : Perm (Fin 2 → ZMod 2) where
  toFun := parabolicAffine r
  invFun := parabolicAffine r⁻¹
  left_inv y := by
    rw [← parabolicAffine_mul, inv_mul_cancel, parabolicAffine_one]
  right_inv y := by
    rw [← parabolicAffine_mul, mul_inv_cancel, parabolicAffine_one]

/-- The **affine action of `P(ℤ/2ℤ)`** on the four points of the plane `(ℤ/2ℤ)²`. -/
def parabolicPermHom : siegelParabolic (Fin 2) (ZMod 2) →* Perm (Fin 2 → ZMod 2) where
  toFun := parabolicPerm
  map_one' := Equiv.ext parabolicAffine_one
  map_mul' r s := Equiv.ext (parabolicAffine_mul r s)

/-- The homomorphism `p ↦ (ℓ(S_p), x ↦ A(x + diag S_p))` from `P(ℤ/2ℤ)` to
`ℤ/2ℤ × Perm((ℤ/2ℤ)²)`. -/
def parabolicHom :
    siegelParabolic (Fin 2) (ZMod 2) →* Multiplicative (ZMod 2) × Perm (Fin 2 → ZMod 2) :=
  parabolicSign.prod parabolicPermHom

/-- **The homomorphism `P(ℤ/2ℤ) → ℤ/2ℤ × Perm((ℤ/2ℤ)²)` is injective**: if `A(x + diag S) = x` for
all `x`, then `A = 1` and `diag S = 0`, hence `D = 1`, and `ℓ(S) = 0` forces `S = 0`. -/
lemma injective_parabolicHom : Function.Injective parabolicHom := by
  refine (injective_iff_map_eq_one _).mpr fun r hr ↦ ?_
  have hsign : symForm (parabolicSym r) = 0 := congrArg Multiplicative.toAdd (congrArg Prod.fst hr)
  have haff (y : Fin 2 → ZMod 2) : parabolicAffine r y = y :=
    congrArg (fun σ : Perm (Fin 2 → ZMod 2) ↦ σ y) (congrArg Prod.snd hr)
  have hdiag : (parabolicSym r).diag = 0 := by
    have h0 : r.1.1.toBlocks₁₁ *ᵥ (parabolicSym r).diag = 0 := by
      simpa [parabolicAffine] using haff 0
    rw [← one_mulVec (parabolicSym r).diag, ← transpose_toBlocks₂₂_mul_toBlocks₁₁ r,
      ← mulVec_mulVec, h0, mulVec_zero]
  have hA : r.1.1.toBlocks₁₁ = 1 := ext_of_mulVec_single fun i ↦ by
    rw [one_mulVec]
    simpa [parabolicAffine, hdiag] using haff (Pi.single i 1)
  have hD : r.1.1.toBlocks₂₂ = 1 := by
    simpa [hA] using transpose_toBlocks₁₁_mul_toBlocks₂₂_eq_one r
  have hB : r.1.1.toBlocks₁₂ = 0 := by
    simpa [parabolicSym, hD] using
      eq_zero_of_symForm_eq_zero _ (transpose_parabolicSym r) hdiag hsign
  refine Subtype.ext (Subtype.ext ?_)
  rw [eq_fromBlocks_of_siegelParabolic r, hA, hB, hD, fromBlocks_one]
  rfl

/-- The element `(A, AS; 0, A⁻ᵀ)` of `P(ℤ/2ℤ)`, for `det A = 1` and `S` symmetric. -/
private noncomputable def parabolicOf : siegelParabolic (Fin 2) (ZMod 2) :=
  ⟨⟨fromBlocks A (A * S) 0 A⁻¹ᵀ, fromBlocks_mem_iff.mpr ⟨by simp, by
    rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, ← transpose_mul, ← Matrix.mul_assoc,
      nonsing_inv_mul _ (hA ▸ isUnit_one), transpose_one, Matrix.mul_one, Matrix.one_mul, hS], by
    rw [← transpose_mul, nonsing_inv_mul _ (hA ▸ isUnit_one), transpose_one, transpose_zero,
      Matrix.zero_mul, sub_zero]⟩⟩, by simp [siegelParabolic]⟩

private lemma parabolicAffine_parabolicOf (y : Fin 2 → ZMod 2) :
    parabolicAffine (parabolicOf hA hS) y = A *ᵥ (y + S.diag) := by
  rw [parabolicAffine, parabolicSym, parabolicOf, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂,
    toBlocks_fromBlocks₁₂, transpose_transpose, ← Matrix.mul_assoc,
    nonsing_inv_mul _ (hA ▸ isUnit_one), Matrix.one_mul]

private lemma parabolicSign_parabolicOf :
    parabolicSign (parabolicOf hA hS) = .ofAdd (symForm S) := by
  rw [parabolicSign, MonoidHom.coe_mk, OneHom.coe_mk, parabolicSym, parabolicOf,
    toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₂, transpose_transpose, ← Matrix.mul_assoc,
    nonsing_inv_mul _ (hA ▸ isUnit_one), Matrix.one_mul]

lemma exists_affine_swap : ∀ x : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2), x.1 ≠ x.2 →
    ∃ T : Matrix (Fin 2) (Fin 2) (ZMod 2) × Matrix (Fin 2) (Fin 2) (ZMod 2), T.1.det = 1 ∧
      T.2ᵀ = T.2 ∧ symForm T.2 = 0 ∧ ∀ y, T.1 *ᵥ (y + T.2.diag) = swap x.1 x.2 y := by
  decide +kernel

/-- **Every element of `ℤ/2ℤ × Perm((ℤ/2ℤ)²)` comes from `P(ℤ/2ℤ)`**: the central element
`(1, (0, 1; 1, 0); 0, 1)` has nontrivial sign and trivial affine action, and every transposition of
the four points of `(ℤ/2ℤ)²` is the affine action of an element of trivial sign. -/
lemma surjective_parabolicHom : Function.Surjective parabolicHom := by
  have hz : (Multiplicative.ofAdd (1 : ZMod 2), (1 : Perm (Fin 2 → ZMod 2))) ∈
      parabolicHom.range :=
    ⟨parabolicOf det_one (by decide : !![(0 : ZMod 2), 1; 1, 0]ᵀ = !![0, 1; 1, 0]),
      Prod.ext (parabolicSign_parabolicOf _ _) <| Equiv.ext fun y ↦
        (parabolicAffine_parabolicOf _ _ y).trans <| by
          rw [(by decide : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)).diag = 0), add_zero,
            one_mulVec]
          rfl⟩
  have hσ : parabolicHom.range.comap (MonoidHom.inr _ _) = ⊤ := by
    rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
    rintro σ ⟨a, b, hab, rfl⟩
    rcases exists_affine_swap (a, b) hab with ⟨⟨A, S⟩, hA, hS, hℓ, h⟩
    exact ⟨parabolicOf hA hS, Prod.ext ((parabolicSign_parabolicOf hA hS).trans
      (congrArg Multiplicative.ofAdd hℓ)) <| Equiv.ext fun y ↦
        (parabolicAffine_parabolicOf hA hS y).trans (h y)⟩
  rintro ⟨ε, σ⟩
  have h1 : ((1 : Multiplicative (ZMod 2)), σ) ∈ parabolicHom.range :=
    Subgroup.mem_comap.mp ((Subgroup.eq_top_iff' _).mp hσ σ)
  have e : (Multiplicative.ofAdd (1 : ZMod 2), σ) = (Multiplicative.ofAdd 1, 1) * (1, σ) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd ε) with h | h
  · rw [← ofAdd_toAdd ε, h, ofAdd_zero]
    exact h1
  · rw [← ofAdd_toAdd ε, h, e]
    exact mul_mem hz h1

lemma card_plane : Fintype.card (Fin 2 → ZMod 2) = 4 := by
  decide

/-- The isomorphism **`P(ℤ/2ℤ) ≅ ℤ/2ℤ × S₄`** (LMFDB `mf.siegel.family.gamma_2`),
`p ↦ (ℓ(S_p), x ↦ A(x + diag S_p))`, the four points of `(ℤ/2ℤ)²` numbered by an arbitrary
bijection with `Fin 4`. -/
noncomputable def parabolicTwoEquiv :
    siegelParabolic (Fin 2) (ZMod 2) ≃* Multiplicative (ZMod 2) × Perm (Fin 4) :=
  (MulEquiv.ofBijective parabolicHom ⟨injective_parabolicHom, surjective_parabolicHom⟩).trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (Fintype.equivFinOfCardEq card_plane).permCongrHom)

/-- The isomorphism **`Γ₀[2]/Γ[2] ≅ ℤ/2ℤ × S₄`** (LMFDB `mf.siegel.family.gamma_2`): reduction
modulo 2 onto the Siegel parabolic subgroup `P(ℤ/2ℤ)` of `Sp(4, ℤ/2ℤ)`, followed by
`P(ℤ/2ℤ) ≅ ℤ/2ℤ × S₄`. -/
noncomputable def quotientGammaTwoGamma0EquivProd : Gamma0 (Fin 2) 2 ⧸
    (Gamma (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2) ≃* Multiplicative (ZMod 2) × Perm (Fin 4) :=
  quotientGammaTwoGamma0Equiv.trans parabolicTwoEquiv

end SymplecticGroup
