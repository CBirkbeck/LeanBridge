import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CuspForm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.UpperHalfSpaceReindex
import TauCeti.RepresentationTheory.ClassicalGroups.Determinant

/-!
# Siegel cusp forms on Siegel upper half-spaces of any index type

The cusp forms `SiegelUpperHalfSpace.IsSiegelCuspForm` (LMFDB `mf.siegel.cusp_form`) are stated on
the Siegel upper half-space `ℋ_g` indexed by `l ⊕ Unit`, where the Siegel `Φ` operator takes the
limit of `f(diag(τ, it))` for `τ ∈ ℋ_{g-1}` indexed by `l`. On `ℋ_g` indexed by another type `m`,
such as `Fin g` for the scalar-valued Siegel modular forms
`SiegelUpperHalfSpace.scalarModularForms`, a function `f` and its weight `ρ` are transported along
an equivalence `e : l ⊕ Unit ≃ m` (`SiegelUpperHalfSpace.reindex`, Tau Ceti's `Equiv.reindexGL`).
Reindexing commutes with the slash operator (`SiegelUpperHalfSpace.slash_comp_reindex`) and
identifies the symplectic groups over `ℚ`, so the transport is a cusp form exactly when
`(f ∣_ρ γ)(e(diag(τ, it)))` tends to `0` for every `γ ∈ Sp(2g, ℚ)` indexed by `m ⊕ m`: the knowl's
condition, with the limit taken in the diagonal entry that `e` assigns to `Unit`. For `l = Fin n`
and `m = Fin (n + 1)`, `SiegelUpperHalfSpace.finSumUnitEquiv` assigns it the last entry, as in the
knowl `mf.siegel.phi`; in degree `3`, `e(diag(τ, it))` is the matrix with `τ ∈ ℋ_2` in its upper
left `2 × 2` block and `it` in its last diagonal entry. The transport of the weight `det^k` is the
weight `det^k`.

The choice of `e` does not matter: two identifications differ by a permutation of `m`, which acts
on `ℋ_g` through a symplectic permutation matrix in `Sp(2g, ℚ)`
(`SiegelUpperHalfSpace.ofPerm_smul`), so the cusp condition along one is the cusp condition along
the other.

## Main definitions

* `SiegelUpperHalfSpace.finSumUnitEquiv`: the equivalence `Fin n ⊕ Unit ≃ Fin (n + 1)`.

## Main results

* `SiegelUpperHalfSpace.isSiegelCuspForm_comp_reindex_iff`: the transported cusp condition in the
  coordinates of `m`.
* `SiegelUpperHalfSpace.isSiegelCuspForm_comp_reindex_congr`: it does not depend on the
  identification of `m` with `l ⊕ Unit`.
* `SiegelUpperHalfSpace.val_reindex_finSumUnitEquiv_phiPoint`: the point `diag(τ, it)` of `ℋ_3`.
-/

open Matrix Module

namespace SiegelUpperHalfSpace

variable {l m : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m] {n : ℕ}

variable (n) in
/-- The equivalence `Fin n ⊕ Unit ≃ Fin (n + 1)`, sending `i` to `i` and `()` to the last index
`n`. Along it, the point `diag(τ, it)` of the Siegel `Φ` operator on `ℋ_{n+1}` indexed by
`Fin n ⊕ Unit` is the matrix indexed by `Fin (n + 1)` with `τ` in its upper left `n × n` block and
`it` in its last diagonal entry, as in the knowl `mf.siegel.phi`. -/
def finSumUnitEquiv : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv.symm).trans finSumFinEquiv

lemma detPowerRep_comp_reindexGL_apply (e : l ≃ Fin n) (k : ℤ) (g : GL l ℂ) (x : ℂ) :
    (TauCeti.detPowerRep ℂ n k).comp (e.reindexGL ℂ).toMonoidHom g x =
      ((GeneralLinearGroup.det g ^ k : ℂˣ) : ℂ) * x := by
  have h : GeneralLinearGroup.det (e.reindexGL ℂ g) = GeneralLinearGroup.det g :=
    Units.ext <| by
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, Equiv.coe_reindexGL,
        det_submatrix_equiv_self]
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, TauCeti.detPowerRep_apply, h]

variable (e e' : l ⊕ Unit ≃ m) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL m ℂ) V) (f : SiegelUpperHalfSpace m → V)

/-- **Cusp forms on `ℋ_g` indexed by `m`** (LMFDB `mf.siegel.cusp_form`): the transport of
`f : ℋ_g → V` and of its weight `ρ` along `e : l ⊕ Unit ≃ m` is a cusp form exactly when, for every
`γ ∈ Sp(2g, ℚ)` indexed by `m ⊕ m` and every `τ ∈ ℋ_{g-1}` indexed by `l`,
`(f ∣_ρ γ)(e(diag(τ, it)))` tends to `0` as `t → ∞`. -/
lemma isSiegelCuspForm_comp_reindex_iff :
    IsSiegelCuspForm (ρ.comp (e.reindexGL ℂ).toMonoidHom) (f ∘ reindex e) ↔
      ∀ γ : symplecticGroup m ℚ,
        HasSiegelPhi (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) f ∘ reindex e) 0 :=
  (SymplecticGroup.reindex e).toEquiv.forall_congr fun _ ↦ iff_of_eq <|
    congrArg (HasSiegelPhi · 0) <| slash_comp_reindex ..

lemma comp_reindex_eq_comp_slash (π : Equiv.Perm m) :
    f ∘ reindex π = ρ (permMatrixHom.toHomUnits π) ∘ slash ρ (SymplecticGroup.ofPerm ℝ π) f := by
  funext τ
  rw [Function.comp_apply, Function.comp_apply, slash_apply, denomGL_ofPerm, ofPerm_smul,
    ← End.mul_apply, ← map_mul, mul_inv_cancel, map_one, End.one_apply]

lemma isSiegelCuspForm_comp_reindex_of_comp_reindex
    (hf : IsSiegelCuspForm (ρ.comp (e.reindexGL ℂ).toMonoidHom) (f ∘ reindex e)) :
    IsSiegelCuspForm (ρ.comp (e'.reindexGL ℂ).toMonoidHom) (f ∘ reindex e') := by
  rw [isSiegelCuspForm_comp_reindex_iff] at hf ⊢
  intro γ
  have hπ : ⇑(reindex e') = reindex (e.symm.trans e') ∘ reindex e := by
    funext τ
    rw [Function.comp_apply, reindex_reindex, ← Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.refl_trans]
  rw [hπ, ← Function.comp_assoc, comp_reindex_eq_comp_slash,
    ← SymplecticGroup.map_ofPerm (algebraMap ℚ ℝ), ← slash_mul, ← map_mul, Function.comp_assoc]
  intro τ φ
  simpa using hf (γ * SymplecticGroup.ofPerm ℚ (e.symm.trans e')) τ
    (φ ∘ₗ ρ (permMatrixHom.toHomUnits (e.symm.trans e')))

/-- **The transported cusp condition does not depend on the identification** (LMFDB
`mf.siegel.cusp_form`): for two equivalences `e, e' : l ⊕ Unit ≃ m`, the transport of `f` and `ρ`
along `e` is a cusp form exactly when the transport along `e'` is. The two differ by the
permutation `e' e⁻¹` of `m`, which acts on `ℋ_g` through a symplectic permutation matrix of
`Sp(2g, ℚ)`. -/
lemma isSiegelCuspForm_comp_reindex_congr :
    IsSiegelCuspForm (ρ.comp (e.reindexGL ℂ).toMonoidHom) (f ∘ reindex e) ↔
      IsSiegelCuspForm (ρ.comp (e'.reindexGL ℂ).toMonoidHom) (f ∘ reindex e') :=
  ⟨isSiegelCuspForm_comp_reindex_of_comp_reindex e e' ρ f,
    isSiegelCuspForm_comp_reindex_of_comp_reindex e' e ρ f⟩

/-- **The point `diag(τ, it)` of `ℋ_3`** (LMFDB `mf.siegel.phi`): along
`SiegelUpperHalfSpace.finSumUnitEquiv`, the point `diag(τ, it)` of the Siegel `Φ` operator on
`ℋ_3`, for `τ ∈ ℋ_2` and `t > 0`, is the matrix with `τ` in its upper left `2 × 2` block, `it` in
its last diagonal entry and `0` elsewhere. -/
lemma val_reindex_finSumUnitEquiv_phiPoint (τ : SiegelUpperHalfSpace (Fin 2))
    (t : Set.Ioi (0 : ℝ)) : (reindex (finSumUnitEquiv 2) (phiPoint τ t)).val =
      !![τ.val 0 0, τ.val 0 1, 0; τ.val 1 0, τ.val 1 1, 0; 0, 0, (t : ℝ) * Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end SiegelUpperHalfSpace
