import LeanBridge.ForMathlib.LinearAlgebra.Lattice.OrthogonalDecomposition
import Mathlib.Data.Matrix.Block
import TauCeti.LinearAlgebra.IntegralLattice.Restriction
import TauCeti.Order.SupIndep

/-!
# Existence of orthogonal decompositions into indecomposable lattices

Every integral lattice (LMFDB `lattice.orthogonal_decomposition`), of any signature, degenerate or
not, has an orthogonal decomposition `L = L₁ ⊕ ⋯ ⊕ L_r` into (orthogonally) indecomposable
summands, by induction on the rank: a nonzero lattice that is not indecomposable is an orthogonal
sum of two nonzero lattices of smaller rank. The summand `Lᵢ`, a submodule of `L`, is the lattice
`L.restrict Lᵢ` of Tau Ceti, with the restricted form.

An orthogonal decomposition is the same as a basis of `L` in which the Gram matrix is block
diagonal: the union of bases of the summands is such a basis, the blocks being the Gram matrices
of the summands, and conversely the blocks of such a basis span the summands of an orthogonal
decomposition.

The uniqueness of the decomposition into indecomposable summands, up to the order of the summands,
holds for positive definite lattices (Eichler's theorem, with Kneser's proof; it fails for
indefinite lattices, see `LeanBridge.ForMathlib.LinearAlgebra.Lattice.OrthogonalDecomposition`). It
is not proved here: it is `LinearMap.BilinForm.eq_orthComponents_iff` on Tau Ceti's main, which
the pinned Tau Ceti lacks.

## Main definitions

* `LinearMap.BilinForm.IsOrthogonallyIndecomposable`: a `ℤ`-valued bilinear form on a nonzero
  module that is not the orthogonal sum of two forms on nonzero modules.

## Main results

* `LinearMap.BilinForm.exists_iSupIndep_isOrthogonallyIndecomposable`: a symmetric `ℤ`-valued
  bilinear form on a finite free `ℤ`-module is an orthogonal sum of indecomposable forms.
* `TauCeti.IntegralLattice.isOrthogonallyIndecomposable_restrict_iff`: a submodule of a lattice is
  an indecomposable lattice exactly when the restricted integral form is indecomposable.
* `TauCeti.IntegralLattice.exists_isOrthogonalDecomposition_isOrthogonallyIndecomposable` (LMFDB
  `lattice.orthogonal_decomposition`): every integral lattice has an orthogonal decomposition into
  indecomposable summands.
* `TauCeti.IntegralLattice.IsOrthogonalDecomposition.gramMatrix_collectedBasis` (LMFDB
  `lattice.orthogonal_decomposition`): in the union of bases of the summands of an orthogonal
  decomposition, the Gram matrix is block diagonal, with the Gram matrices of the summands as
  blocks.
* `TauCeti.IntegralLattice.isOrthogonalDecomposition_of_gramMatrix_eq_blockDiagonal'` and
  `TauCeti.IntegralLattice.gramMatrix_restrict_span_eq` (LMFDB `lattice.orthogonal_decomposition`):
  a basis in which the Gram matrix is block diagonal gives an orthogonal decomposition, whose
  summands have the blocks as Gram matrices.
-/

open Module

open LinearMap (BilinForm)

universe u

namespace LinearMap.BilinForm

variable {M : Type u} [AddCommGroup M] {B : BilinForm ℤ M} {M' : Type*} [AddCommGroup M']
  {B' : BilinForm ℤ M'}

variable (B) in
/-- A `ℤ`-valued bilinear form `B` on `M` is (orthogonally) **indecomposable** if `M` is nonzero
and is not the direct sum of two nonzero submodules orthogonal to each other. For the integral form
of an integral lattice `L` this is `TauCeti.IntegralLattice.IsOrthogonallyIndecomposable L` (LMFDB
`lattice.orthogonal_decomposition`). -/
def IsOrthogonallyIndecomposable : Prop :=
  Nontrivial M ∧ ∀ P Q : Submodule ℤ M, IsCompl P Q → (∀ x ∈ P, ∀ y ∈ Q, B x y = 0) →
    P = ⊥ ∨ Q = ⊥

lemma IsOrthogonallyIndecomposable.congr (h : B.IsOrthogonallyIndecomposable) (e : M ≃ₗ[ℤ] M')
    (he : ∀ x y, B' (e x) (e y) = B x y) : B'.IsOrthogonallyIndecomposable := by
  have hM : Nontrivial M := h.1
  let f : Submodule ℤ M' ≃o Submodule ℤ M := (Submodule.orderIsoMapComap e).symm
  have hf (N : Submodule ℤ M') (hN : f N = ⊥) : N = ⊥ := f.injective (hN.trans f.map_bot.symm)
  exact ⟨e.symm.toEquiv.nontrivial, fun P Q hPQ ho ↦ (h.2 (f P) (f Q) (f.isCompl hPQ)
    fun x hx y hy ↦ (he x y).symm.trans (ho (e x) hx (e y) hy)).imp (hf P) (hf Q)⟩

/-- **A symmetric integral bilinear form on a finite free `ℤ`-module is an orthogonal sum of
indecomposable forms**: `M` is the direct sum of finitely many pairwise orthogonal submodules on
which the form is indecomposable, by induction on the rank. -/
lemma exists_iSupIndep_isOrthogonallyIndecomposable [Module.Free ℤ M] [Module.Finite ℤ M]
    (hB : B.IsSymm) : ∃ (ι : Type) (_ : Fintype ι) (S : ι → Submodule ℤ M), iSupIndep S ∧
      ⨆ i, S i = ⊤ ∧ (Pairwise fun i j ↦ ∀ x ∈ S i, ∀ y ∈ S j, B x y = 0) ∧
      ∀ i, (B.restrict (S i)).IsOrthogonallyIndecomposable := by
  induction hn : finrank ℤ M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases hsub : Subsingleton M
  · exact ⟨PEmpty, inferInstance, fun i ↦ i.elim, fun i ↦ i.elim, Subsingleton.elim _ _,
      fun i ↦ i.elim, fun i ↦ i.elim⟩
  rw [not_subsingleton_iff_nontrivial] at hsub
  by_cases hind : B.IsOrthogonallyIndecomposable
  · refine ⟨Unit, inferInstance, fun _ ↦ ⊤, fun _ ↦ by simp, iSup_const, Subsingleton.pairwise,
      fun _ ↦ hind.congr Submodule.topEquiv.symm fun x y ↦ rfl⟩
  have hPQ :
      ∃ P Q : Submodule ℤ M, IsCompl P Q ∧ (∀ x ∈ P, ∀ y ∈ Q, B x y = 0) ∧ P ≠ ⊥ ∧ Q ≠ ⊥ := by
    by_contra! h
    exact hind ⟨hsub, fun P Q hPQ ho ↦ or_iff_not_imp_left.mpr (h P Q hPQ ho)⟩
  rcases hPQ with ⟨P, Q, hPQ, ho, hP, hQ⟩
  have hrank : finrank ℤ P + finrank ℤ Q = finrank ℤ M := by
    rw [← finrank_prod, (Submodule.prodEquivOfIsCompl P Q hPQ).finrank_eq]
  have hP0 : 0 < finrank ℤ P := finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hP)
  have hQ0 : 0 < finrank ℤ Q := finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hQ)
  rcases ih (finrank ℤ P) (by omega) (hB.restrict P) rfl with ⟨ι₁, _, S₁, hi₁, hs₁, ho₁, hd₁⟩
  rcases ih (finrank ℤ Q) (by omega) (hB.restrict Q) rfl with ⟨ι₂, _, S₂, hi₂, hs₂, ho₂, hd₂⟩
  refine ⟨ι₁ ⊕ ι₂, inferInstance,
    Sum.elim (fun i ↦ (S₁ i).map P.subtype) fun j ↦ (S₂ j).map Q.subtype,
    (P.subtype.iSupIndep_map P.injective_subtype hi₁).sum_elim
      (Q.subtype.iSupIndep_map Q.injective_subtype hi₂) <| hPQ.disjoint.mono
        (iSup_le fun i ↦ P.map_subtype_le (S₁ i)) (iSup_le fun j ↦ Q.map_subtype_le (S₂ j)),
    ?_, ?_, ?_⟩
  · simp only [iSup_sum, Sum.elim_inl, Sum.elim_inr]
    rw [← Submodule.map_iSup, ← Submodule.map_iSup, hs₁, hs₂, Submodule.map_top,
      Submodule.map_top, Submodule.range_subtype, Submodule.range_subtype, hPQ.sup_eq_top]
  · rintro (a | c) (a' | c') hne _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    · exact ho₁ (fun h ↦ hne (congrArg Sum.inl h)) x hx y hy
    · exact ho x x.2 y y.2
    · exact (hB.eq _ _).trans (ho y y.2 x x.2)
    · exact ho₂ (fun h ↦ hne (congrArg Sum.inr h)) x hx y hy
  · rintro (a | c)
    · exact (hd₁ a).congr (Submodule.equivSubtypeMap P (S₁ a)) fun x y ↦ rfl
    · exact (hd₂ c).congr (Submodule.equivSubtypeMap Q (S₂ c)) fun x y ↦ rfl

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- **A submodule of a lattice is an indecomposable lattice exactly when the restricted integral
form is indecomposable**: the lattice `L.restrict N` of Tau Ceti, the submodule `N` of `L` with the
restricted form, is indecomposable (LMFDB `lattice.orthogonal_decomposition`) exactly when `N` is
nonzero and is not the direct sum of two nonzero submodules orthogonal to each other. -/
lemma isOrthogonallyIndecomposable_restrict_iff (N : Submodule ℤ L) :
    (L.restrict N).IsOrthogonallyIndecomposable ↔
      (L.integralForm.restrict N).IsOrthogonallyIndecomposable := by
  rw [isOrthogonallyIndecomposable_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ h.congr (L.restrictCarrierEquiv N)
    (L.integralForm_restrictCarrierEquiv N)⟩
  have h' : (L.restrict N).integralForm.IsOrthogonallyIndecomposable := h
  refine h'.congr (L.restrictCarrierEquiv N).symm fun x y ↦ ?_
  simpa using (L.integralForm_restrictCarrierEquiv N ((L.restrictCarrierEquiv N).symm x)
    ((L.restrictCarrierEquiv N).symm y)).symm

/-- **Every integral lattice has an orthogonal decomposition into indecomposable summands** (LMFDB
`lattice.orthogonal_decomposition`): for every integral lattice `L`, of any signature, degenerate
or not, there are submodules `L₁, …, L_r` forming an orthogonal decomposition of `L` such that each
lattice `Lᵢ` (`L.restrict Lᵢ`, with the restricted form) is indecomposable. The zero lattice has
the empty decomposition, `r = 0`. -/
lemma exists_isOrthogonalDecomposition_isOrthogonallyIndecomposable :
    ∃ (r : ℕ) (S : Fin r → Submodule ℤ L), L.IsOrthogonalDecomposition S ∧
      ∀ i, (L.restrict (S i)).IsOrthogonallyIndecomposable := by
  classical
  rcases BilinForm.exists_iSupIndep_isOrthogonallyIndecomposable L.isSymm_integralForm with
    ⟨ι, _, S, hi, hs, ho, hd⟩
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, S ∘ e,
    ⟨(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
      ⟨hi.comp e.injective, e.iSup_comp.trans hs⟩, fun i j hij ↦ ho (e.injective.ne hij)⟩,
    fun i ↦ (L.isOrthogonallyIndecomposable_restrict_iff _).mpr (hd _)⟩

variable {L} {r : ℕ} {κ : Fin r → Type*}

/-- **The Gram matrix of an orthogonal decomposition is block diagonal** (LMFDB
`lattice.orthogonal_decomposition`): if `L = L₁ ⊕ ⋯ ⊕ L_r` is an orthogonal decomposition and `vᵢ`
is a basis of `Lᵢ`, then the Gram matrix of `L` in the basis of `L` formed by the `vᵢ` is the block
diagonal matrix of the Gram matrices `Gᵢ` of the lattices `Lᵢ` in the bases `vᵢ`. -/
lemma IsOrthogonalDecomposition.gramMatrix_collectedBasis {S : Fin r → Submodule ℤ L}
    (hS : L.IsOrthogonalDecomposition S) (v : ∀ i, Basis (κ i) ℤ (S i)) :
    L.gramMatrix (hS.1.collectedBasis v) = Matrix.blockDiagonal' fun i ↦
      (L.restrict (S i)).gramMatrix ((v i).map (L.restrictCarrierEquiv (S i))) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [gramMatrix_apply, hS.1.collectedBasis_coe]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.blockDiagonal'_apply_eq, gramMatrix_apply, Basis.map_apply, Basis.map_apply,
      integralForm_restrictCarrierEquiv]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij]
    exact hS.2 hij _ (v i a).2 _ (v j c).2

variable (b : Basis (Σ i, κ i) ℤ L) (G : ∀ i, Matrix (κ i) (κ i) ℤ)

/-- **A basis in which the Gram matrix is block diagonal gives an orthogonal decomposition** (LMFDB
`lattice.orthogonal_decomposition`): if the Gram matrix of `L` in a basis `b`, indexed by the
disjoint union of sets `κ₁, …, κ_r`, is block diagonal, then the submodules `Lᵢ` spanned by the
basis vectors of the blocks `κᵢ` form an orthogonal decomposition of `L`. -/
lemma isOrthogonalDecomposition_of_gramMatrix_eq_blockDiagonal'
    (hG : L.gramMatrix b = Matrix.blockDiagonal' G) :
    L.IsOrthogonalDecomposition fun i ↦ Submodule.span ℤ (Set.range (b ∘ Sigma.mk i)) := by
  classical
  refine ⟨(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨fun i ↦ ?_, ?_⟩,
    fun i j hij x hx y hy ↦ ?_⟩
  · refine (b.linearIndependent.disjoint_span_image (s := {p | p.1 = i}) (t := {p | p.1 ≠ i})
      (Set.disjoint_left.mpr fun p hp hp' ↦ hp' hp)).mono (Submodule.span_mono ?_)
      (iSup₂_le fun j hj ↦ Submodule.span_mono ?_)
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨i, a⟩, rfl, rfl⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨j, a⟩, hj, rfl⟩
  · rw [← Submodule.span_iUnion, ← b.span_eq]
    congr 1
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, a, h⟩ ↦ ⟨⟨i, a⟩, h⟩, fun ⟨⟨i, a⟩, h⟩ ↦ ⟨i, a, h⟩⟩
  · refine Submodule.span_induction₂ (p := fun x y _ _ ↦ L.integralForm x y = 0) ?_
      (fun y _ ↦ LinearMap.map_zero₂ _ y) (fun x _ ↦ map_zero _)
      (fun x y z _ _ _ hx hy ↦ by rw [LinearMap.map_add₂, hx, hy, add_zero])
      (fun x y z _ _ _ hy hz ↦ by rw [map_add, hy, hz, add_zero])
      (fun n x y _ _ h ↦ by rw [LinearMap.map_smul₂, h, smul_zero])
      (fun n x y _ _ h ↦ by rw [map_smul, h, smul_zero]) hx hy
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    rw [Function.comp_apply, Function.comp_apply, ← gramMatrix_apply, hG,
      Matrix.blockDiagonal'_apply_ne _ _ _ hij]

/-- **The blocks of a block diagonal Gram matrix are Gram matrices of the summands** (LMFDB
`lattice.orthogonal_decomposition`): if the Gram matrix of `L` in a basis `b` is block diagonal
with blocks `Gᵢ`, then `Gᵢ` is the Gram matrix of the lattice `Lᵢ` spanned by the basis vectors of
the `i`-th block, in the basis formed by these vectors. -/
lemma gramMatrix_restrict_span_eq (hG : L.gramMatrix b = Matrix.blockDiagonal' G) (i : Fin r) :
    (L.restrict (Submodule.span ℤ (Set.range (b ∘ Sigma.mk i)))).gramMatrix
      ((Basis.span (b.linearIndependent.comp _ sigma_mk_injective)).map
        (L.restrictCarrierEquiv _)) = G i := by
  ext a c
  rw [gramMatrix_apply, Basis.map_apply, Basis.map_apply, integralForm_restrictCarrierEquiv,
    Basis.span_apply, Basis.span_apply, ← Matrix.blockDiagonal'_apply_eq G i a c, ← hG,
    gramMatrix_apply]
  rfl

end TauCeti.IntegralLattice
