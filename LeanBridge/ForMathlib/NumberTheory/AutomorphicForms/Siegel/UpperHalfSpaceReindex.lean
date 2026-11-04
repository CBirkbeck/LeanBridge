import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Reindexing the Siegel upper half-space

An equivalence `e : l ≃ m` of finite index types renames the rows and columns of matrices
(`Matrix.reindex e e`). It identifies the Siegel upper half-spaces `ℋ_g` indexed by `l` and by `m`,
the symplectic groups `Sp(2g, R)` indexed by `l ⊕ l` and by `m ⊕ m` (through `e ⊕ e`, which
preserves `J`), and the general linear groups `GL(g, ℂ)` (Tau Ceti's `Equiv.reindexGL`). These
identifications are compatible with the action of `Sp(2g, ℝ)` on `ℋ_g` and with the automorphy
factor `cτ + d`, hence with the slash operator: transporting a function on `ℋ_g` and its weight
`ρ` along `e` commutes with slashing. Through them, a notion that LeanBridge states on one index
type, such as the cusp forms `SiegelUpperHalfSpace.IsSiegelCuspForm` on `ℋ_g` indexed by
`l ⊕ Unit`, applies on another, such as `Fin g`.

A permutation `π` of `l` reindexes `ℋ_g` to itself, and this is the action of the block-diagonal
permutation matrix `diag(P_π, P_π)` of `Sp(2g, ℚ)`, `P_π` the matrix of `e_j ↦ e_{π(j)}`: as
`P_πᵀ P_π = 1`, it sends `τ` to `P_π τ P_πᵀ`, whose entries are those of `τ` renamed through `π`.

## Main definitions

* `SymplecticGroup.reindex`: the isomorphism of symplectic groups induced by `e : l ≃ m`.
* `SymplecticGroup.ofPerm`: the symplectic permutation matrix `diag(P_π, P_π)`.
* `SiegelUpperHalfSpace.reindex`: the bijection of Siegel upper half-spaces induced by `e : l ≃ m`.

## Main results

* `SiegelUpperHalfSpace.reindex_smul`: `SiegelUpperHalfSpace.reindex` is equivariant for the action
  of the symplectic group.
* `SiegelUpperHalfSpace.slash_comp_reindex`: the slash operator commutes with reindexing.
* `SiegelUpperHalfSpace.ofPerm_smul`: reindexing along a permutation is the action of the
  symplectic permutation matrix.
-/

open Matrix

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [NonAssocSemiring R] (π : Equiv.Perm n)

lemma transpose_permMatrix_mul_permMatrix : (π.permMatrix R)ᵀ * π.permMatrix R = 1 := by
  rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

end Matrix

namespace SymplecticGroup

variable {l m : Type*} [DecidableEq l] [Fintype l] [DecidableEq m] [Fintype m] {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (e : l ≃ m) (γ : symplecticGroup l R) (π : Equiv.Perm l)

lemma reindex_mem {M : Matrix (l ⊕ l) (l ⊕ l) R} (hM : M ∈ symplecticGroup l R) :
    M.reindex (e.sumCongr e) (e.sumCongr e) ∈ symplecticGroup m R := by
  have hJ : (J l R).reindex (e.sumCongr e) (e.sumCongr e) = J m R := by
    ext (i | i) (j | j) <;> simp [J, one_apply]
  rw [mem_iff, ← hJ, transpose_reindex, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, submatrix_mul_equiv, mem_iff.mp hM]

/-- The isomorphism `Sp(2g, R) ≃* Sp(2g, R)` from the symplectic group indexed by `l ⊕ l` to the
one indexed by `m ⊕ m`, induced by `e : l ≃ m`: the rows and columns of `γ` are renamed through
`e ⊕ e`, which preserves `J`. -/
def reindex : symplecticGroup l R ≃* symplecticGroup m R where
  toFun γ := ⟨γ.1.reindex (e.sumCongr e) (e.sumCongr e), reindex_mem e γ.2⟩
  invFun γ := ⟨(Matrix.reindex (e.sumCongr e) (e.sumCongr e)).symm γ, reindex_mem e.symm γ.2⟩
  left_inv γ := Subtype.ext <| (Matrix.reindex (e.sumCongr e) (e.sumCongr e)).symm_apply_apply γ.1
  right_inv γ := Subtype.ext <| (Matrix.reindex (e.sumCongr e) (e.sumCongr e)).apply_symm_apply γ.1
  map_mul' γ γ' := Subtype.ext (submatrix_mul_equiv γ.1 γ'.1 _ _ _).symm

@[simp]
lemma coe_reindex : (reindex e γ : Matrix (m ⊕ m) (m ⊕ m) R) =
    (γ : Matrix (l ⊕ l) (l ⊕ l) R).reindex (e.sumCongr e) (e.sumCongr e) :=
  rfl

lemma map_reindex : map f (reindex e γ) = reindex e (map f γ) :=
  rfl

variable (R) in
/-- The **symplectic permutation matrix** `diag(P_π, P_π)` of `Sp(2g, R)` of a permutation `π` of
`l`, where `P_π` is the matrix of `e_j ↦ e_{π(j)}` (Mathlib's `Equiv.Perm.permMatrix` of `π⁻¹`): a
symplectic matrix since `P_πᵀ P_π = 1`. It acts on `ℋ_g` by `τ ↦ P_π τ P_πᵀ`, the reindexing
along `π` (`SiegelUpperHalfSpace.ofPerm_smul`). -/
def ofPerm : symplecticGroup l R :=
  ⟨fromBlocks (π⁻¹.permMatrix R) 0 0 (π⁻¹.permMatrix R),
    fromBlocks_diagonal_mem (transpose_permMatrix_mul_permMatrix π⁻¹)⟩

lemma coe_ofPerm : (ofPerm R π : Matrix (l ⊕ l) (l ⊕ l) R) =
    fromBlocks (π⁻¹.permMatrix R) 0 0 (π⁻¹.permMatrix R) :=
  rfl

lemma map_ofPerm : map f (ofPerm R π) = ofPerm S π :=
  Subtype.ext <| by
    rw [coe_map_apply, coe_ofPerm, coe_ofPerm, fromBlocks_map, PEquiv.map_toMatrix,
      Matrix.map_zero _ (map_zero f)]

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l m : Type*} (e : l ≃ m) (τ : SiegelUpperHalfSpace l)

/-- The bijection `ℋ_g ≃ ℋ_g` from the Siegel upper half-space indexed by `l` to the one indexed
by `m`, induced by `e : l ≃ m`: the rows and columns of `τ` are renamed through `e`. -/
def reindex : SiegelUpperHalfSpace l ≃ SiegelUpperHalfSpace m where
  toFun τ := ⟨τ.val.reindex e e, by rw [transpose_reindex, τ.transpose_val],
    τ.posDef_im.submatrix e.symm.injective⟩
  invFun τ := ⟨τ.val.reindex e.symm e.symm, by rw [transpose_reindex, τ.transpose_val],
    τ.posDef_im.submatrix e.injective⟩
  left_inv τ := SiegelUpperHalfSpace.ext <| (Matrix.reindex e e).symm_apply_apply τ.val
  right_inv τ := SiegelUpperHalfSpace.ext <| (Matrix.reindex e e).apply_symm_apply τ.val

@[simp]
lemma val_reindex : (reindex e τ).val = τ.val.reindex e e :=
  rfl

lemma reindex_reindex {n : Type*} (e' : m ≃ n) :
    reindex e' (reindex e τ) = reindex (e.trans e') τ :=
  SiegelUpperHalfSpace.ext <| submatrix_submatrix ..

variable [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m] (γ : symplecticGroup l ℝ)
    (M : Matrix l l ℂ) (π : Equiv.Perm l) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL m ℂ) V) (f : SiegelUpperHalfSpace m → V)

lemma num_reindex : num (SymplecticGroup.reindex e γ) (M.reindex e e) = (num γ M).reindex e e := by
  rw [num, num, reindex_apply, reindex_apply, submatrix_add, Pi.add_apply, Pi.add_apply,
    ← submatrix_mul_equiv _ _ _ e.symm]
  rfl

lemma denom_reindex :
    denom (SymplecticGroup.reindex e γ) (M.reindex e e) = (denom γ M).reindex e e := by
  rw [denom, denom, reindex_apply, reindex_apply, submatrix_add, Pi.add_apply, Pi.add_apply,
    ← submatrix_mul_equiv _ _ _ e.symm]
  rfl

/-- **Reindexing is equivariant**: `e(γτ) = e(γ) e(τ)` for the bijection `e : ℋ_g ≃ ℋ_g` and the
isomorphism `e : Sp(2g, ℝ) ≃* Sp(2g, ℝ)` induced by `e : l ≃ m`. -/
lemma reindex_smul : reindex e (γ • τ) = SymplecticGroup.reindex e γ • reindex e τ :=
  SiegelUpperHalfSpace.ext <| by
    rw [val_smul, val_reindex, val_reindex, num_reindex, denom_reindex, val_smul, inv_reindex,
      reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

lemma denomGL_reindex :
    denomGL (SymplecticGroup.reindex e γ) (reindex e τ) = e.reindexGL ℂ (denomGL γ τ) :=
  Units.ext <| by
    rw [coe_denomGL, Equiv.coe_reindexGL, coe_denomGL, val_reindex, denom_reindex, reindex_apply]

/-- **The slash operator commutes with reindexing**: for `f : ℋ_g → V` on the Siegel upper
half-space indexed by `m`, a weight `ρ` of `GL(g, ℂ)` indexed by `m` and `γ ∈ Sp(2g, ℝ)` indexed
by `l ⊕ l`, the slash of the transport `f ∘ e` of `f` along `e : l ≃ m`, in the transported weight
`ρ ∘ e`, is the transport of the slash `f ∣_ρ e(γ)`. -/
lemma slash_comp_reindex : slash (ρ.comp (e.reindexGL ℂ).toMonoidHom) γ (f ∘ reindex e) =
    slash ρ (SymplecticGroup.reindex e γ) f ∘ reindex e := by
  funext τ
  rw [Function.comp_apply, slash_apply, slash_apply, Function.comp_apply, reindex_smul,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, denomGL_reindex]

lemma num_ofPerm : num (SymplecticGroup.ofPerm ℝ π) M = π⁻¹.permMatrix ℂ * M := by
  rw [num, SymplecticGroup.coe_ofPerm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    Matrix.map_zero _ Complex.ofReal_zero, add_zero]
  exact congrArg (· * M) (PEquiv.map_toMatrix Complex.ofRealHom _)

lemma denom_ofPerm : denom (SymplecticGroup.ofPerm ℝ π) M = π⁻¹.permMatrix ℂ := by
  rw [denom, SymplecticGroup.coe_ofPerm, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.map_zero _ Complex.ofReal_zero, Matrix.zero_mul, zero_add]
  exact PEquiv.map_toMatrix Complex.ofRealHom _

/-- **Reindexing along a permutation is a symplectic action**: the symplectic permutation matrix
`diag(P_π, P_π)` of a permutation `π` of `l` sends `τ` to `P_π τ P_πᵀ`, that is, to the reindexing
of `τ` along `π`. -/
lemma ofPerm_smul : SymplecticGroup.ofPerm ℝ π • τ = reindex π τ :=
  SiegelUpperHalfSpace.ext <| by
    rw [val_smul, num_ofPerm, denom_ofPerm, val_reindex,
      inv_eq_left_inv (transpose_permMatrix_mul_permMatrix π⁻¹), transpose_permMatrix, inv_inv]
    simp [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]

lemma denomGL_ofPerm : denomGL (SymplecticGroup.ofPerm ℝ π) τ = permMatrixHom.toHomUnits π :=
  Units.ext <| by rw [coe_denomGL, denom_ofPerm, MonoidHom.coe_toHomUnits, permMatrixHom_apply]

end SiegelUpperHalfSpace
