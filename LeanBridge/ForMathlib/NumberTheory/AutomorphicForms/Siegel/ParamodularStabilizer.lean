import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularPattern
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.LinearAlgebra.Matrix.Action

/-!
# The paramodular group as a stabiliser

The paramodular group `Γ^para(d) = δ Γ δ⁻¹` of type `d` (LMFDB `paramodulargroup.sp2gr`,
`SymplecticGroup.paramodular`), for `δ = diag(1_g, d)` and `Γ` the integral isometry group of
`T = (0, d; -d, 0)`, is the stabiliser in `Sp(2g, ℚ)` of the lattice `δ ℤ^{2g}` of column
vectors `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ`: a rational matrix `X` maps that lattice into itself exactly when
`δ⁻¹ X δ` is integral, and for a symplectic `X` the integral matrix `δ⁻¹ X δ` has determinant `1`
and is an isometry of `T = -δJδ`. In particular a symplectic matrix mapping the lattice into itself
maps it onto itself.

For the paramodular group `K(N)` of level `N` (LMFDB `group.paramodular`,
`SiegelUpperHalfSpace.paramodularLevel N`, the type `d = (1, N)`), the lattice is
`ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ`, so `K(N)` is its stabiliser in `Sp(4, ℚ)`, as the knowl says. A rational matrix
maps `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself exactly when it has the shape
`[ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; Nℤ, Nℤ, Nℤ, ℤ]`, so `K(N)` comprises the
symplectic matrices of that shape; the symplectic conditions then force the stronger shape
`[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]` of the elements of `K(N)`
(`SiegelUpperHalfSpace.isParamodularShape_of_mem`).

## Main definitions

* `SymplecticGroup.paramodularLattice` (LMFDB `group.paramodular`): the lattice
  `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ` of column vectors.
* `SiegelUpperHalfSpace.IsParamodularWeakShape` (LMFDB `group.paramodular`): the shape of the
  rational matrices mapping `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself.

## Main results

* `SymplecticGroup.mem_paramodularLattice_iff` (LMFDB `group.paramodular`): the lattice
  `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ`, coordinatewise.
* `SymplecticGroup.paramodular_eq_stabilizer` (LMFDB `group.paramodular`): the paramodular group
  of type `d` is the stabiliser in `Sp(2g, ℚ)` of `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ`.
* `SymplecticGroup.mem_stabilizer_iff_forall_mulVec_mem`: a symplectic matrix stabilises it
  exactly when it maps it into itself.
* `SiegelUpperHalfSpace.forall_mulVec_mem_iff_isParamodularWeakShape` (LMFDB `group.paramodular`):
  a rational matrix maps `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself exactly when it has the weaker shape.
* `SiegelUpperHalfSpace.paramodularLevel_eq_stabilizer` (LMFDB `group.paramodular`): `K(N)` is the
  stabiliser in `Sp(4, ℚ)` of `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ`.
* `SiegelUpperHalfSpace.mem_paramodularLevel_iff_isParamodularWeakShape` (LMFDB
  `group.paramodular`): `K(N)` comprises the symplectic matrices of the weaker shape.
* `SiegelUpperHalfSpace.isParamodularShape_of_isParamodularWeakShape` (LMFDB
  `group.paramodular`): the symplectic conditions force the stronger shape.
-/

open Matrix

open scoped Pointwise

namespace SymplecticGroup

variable {l : Type*} [DecidableEq l] (d : l → ℕ+) {v : l ⊕ l → ℚ}

/-- The lattice `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ` of column vectors in `ℚ^{2g}` (LMFDB `group.paramodular`):
the vectors `v` with `v(e_i) ∈ ℤ` and `v(f_i) ∈ d_i ℤ`, each coordinate lying in the multiples of
the corresponding diagonal entry of `δ = diag(1_g, d)`. It is `δ ℤ^{2g}`
(`SymplecticGroup.mem_paramodularLattice_iff_exists`), and for the paramodular group `K(N)` of
level `N`, of type `d = (1, N)`, it is `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ`. -/
def paramodularLattice : Submodule ℤ (l ⊕ l → ℚ) :=
  Submodule.pi Set.univ fun j ↦ Submodule.span ℤ {paramodularDelta d j j}

lemma paramodularDelta_eq_diagonal :
    paramodularDelta d = diagonal (Sum.elim 1 fun i ↦ ((d i : ℕ) : ℚ)) := by
  rw [paramodularDelta, ← diagonal_one, fromBlocks_diagonal]
  rfl

lemma paramodularDeltaInv_eq_diagonal :
    paramodularDeltaInv d = diagonal (Sum.elim 1 fun i ↦ ((d i : ℕ) : ℚ)⁻¹) := by
  rw [paramodularDeltaInv, ← diagonal_one, fromBlocks_diagonal]
  rfl

/-- **The lattice `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ`, coordinatewise** (LMFDB `group.paramodular`). -/
lemma mem_paramodularLattice_iff : v ∈ paramodularLattice d ↔ (∀ i, ∃ a : ℤ, v (.inl i) = a) ∧
    ∀ i, ∃ a : ℤ, v (.inr i) = (d i : ℕ) * a := by
  simp [paramodularLattice, Submodule.mem_span_singleton, paramodularDelta_eq_diagonal, eq_comm,
    mul_comm]

variable [Fintype l]

lemma mem_paramodularLattice_iff_exists :
    v ∈ paramodularLattice d ↔ ∃ z : l ⊕ l → ℤ, paramodularDelta d *ᵥ (fun j ↦ (z j : ℚ)) = v := by
  simp [paramodularLattice, Submodule.mem_span_singleton, paramodularDelta_eq_diagonal, funext_iff,
    mulVec_diagonal, Classical.skolem, mul_comm]

lemma paramodularDeltaInv_mul_paramodularDelta_mul (Y : Matrix (l ⊕ l) (l ⊕ l) ℚ) :
    paramodularDeltaInv d * (paramodularDelta d * Y) = Y := by
  rw [← Matrix.mul_assoc, paramodularDeltaInv_mul_paramodularDelta, Matrix.one_mul]

lemma paramodularDelta_mul_paramodularDeltaInv_mul (Y : Matrix (l ⊕ l) (l ⊕ l) ℚ) :
    paramodularDelta d * (paramodularDeltaInv d * Y) = Y := by
  rw [← Matrix.mul_assoc, paramodularDelta_mul_paramodularDeltaInv, Matrix.one_mul]

variable {d} {X : Matrix (l ⊕ l) (l ⊕ l) ℚ} {x : Matrix (l ⊕ l) (l ⊕ l) ℤ} {M : symplecticGroup l ℚ}

lemma eq_paramodularDelta_mul_mul_of_map_eq
    (hx : x.map (Int.castRingHom ℚ) = paramodularDeltaInv d * X * paramodularDelta d) :
    X = paramodularDelta d * x.map (Int.castRingHom ℚ) * paramodularDeltaInv d := by
  rw [hx]
  simp only [Matrix.mul_assoc, paramodularDelta_mul_paramodularDeltaInv_mul,
    paramodularDelta_mul_paramodularDeltaInv, Matrix.mul_one]

lemma mulVec_mem_paramodularLattice_of_map_eq
    (hx : x.map (Int.castRingHom ℚ) = paramodularDeltaInv d * X * paramodularDelta d)
    (hv : v ∈ paramodularLattice d) : X *ᵥ v ∈ paramodularLattice d := by
  rcases (mem_paramodularLattice_iff_exists d).mp hv with ⟨z, rfl⟩
  refine (mem_paramodularLattice_iff_exists d).mpr ⟨x *ᵥ z, ?_⟩
  have hz : (fun j ↦ ((x *ᵥ z) j : ℚ)) = x.map (Int.castRingHom ℚ) *ᵥ fun j ↦ (z j : ℚ) :=
    funext fun j ↦ RingHom.map_mulVec (Int.castRingHom ℚ) x z j
  simp [hz, eq_paramodularDelta_mul_mul_of_map_eq hx, Matrix.mul_assoc,
    paramodularDeltaInv_mul_paramodularDelta]

lemma exists_map_eq_of_forall_mulVec_mem
    (hX : ∀ v ∈ paramodularLattice d, X *ᵥ v ∈ paramodularLattice d) :
    ∃ x : Matrix (l ⊕ l) (l ⊕ l) ℤ, x.map (Int.castRingHom ℚ) =
    paramodularDeltaInv d * X * paramodularDelta d := by
  have hj (j : l ⊕ l) : paramodularDelta d *ᵥ Pi.single j 1 ∈ paramodularLattice d :=
    (mem_paramodularLattice_iff_exists d).mpr
      ⟨Pi.single j 1, congrArg _ <| funext fun k ↦ by simp [Pi.single_apply]⟩
  choose z hz using fun j ↦ (mem_paramodularLattice_iff_exists d).mp (hX _ (hj j))
  refine ⟨of fun i j ↦ z j i, ext_of_mulVec_single fun j ↦ ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hz j, mulVec_mulVec,
    paramodularDeltaInv_mul_paramodularDelta, one_mulVec]
  ext i
  simp

lemma forall_mulVec_mem_iff_exists_map_eq :
    (∀ v ∈ paramodularLattice d, X *ᵥ v ∈ paramodularLattice d) ↔
    ∃ x : Matrix (l ⊕ l) (l ⊕ l) ℤ, x.map (Int.castRingHom ℚ) =
    paramodularDeltaInv d * X * paramodularDelta d :=
  ⟨exists_map_eq_of_forall_mulVec_mem, fun ⟨_, hx⟩ _ ↦ mulVec_mem_paramodularLattice_of_map_eq hx⟩

lemma mem_paramodular_of_map_eq
    (hx : x.map (Int.castRingHom ℚ) = paramodularDeltaInv d * M * paramodularDelta d) :
    M ∈ paramodular d := by
  have hdet : IsUnit x.det := by
    have h : ((x.det : ℤ) : ℚ) = 1 := by
      rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det, RingHom.mapMatrix_apply, hx, det_mul,
        det_mul, mul_right_comm, ← det_mul, paramodularDeltaInv_mul_paramodularDelta, det_one,
        one_mul]
      exact det_eq_one M.2
    rw [Int.cast_eq_one.mp h]
    exact isUnit_one
  have hT : xᵀ * paramodularForm d * x = paramodularForm d := by
    refine map_injective (Int.cast_injective (α := ℚ)) ?_
    have e (Y : Matrix (l ⊕ l) (l ⊕ l) ℤ) : Y.map Int.cast = Y.map (Int.castRingHom ℚ) :=
      rfl
    have hJ : (M : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * (J l ℚ * (M * paramodularDelta d)) =
        J l ℚ * paramodularDelta d := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_iff'.mp M.2]
    have hF : (paramodularForm d).map (Int.castRingHom ℚ) =
        -(paramodularDelta d * J l ℚ * paramodularDelta d) := by
      rw [paramodularDelta_mul_J_mul_paramodularDelta, neg_neg]
    simp only [e, Matrix.map_mul, transpose_map, hx, hF, transpose_mul, transpose_paramodularDelta,
      transpose_paramodularDeltaInv, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
      paramodularDeltaInv_mul_paramodularDelta_mul, paramodularDelta_mul_paramodularDeltaInv_mul,
      hJ]
  let γ : GL (l ⊕ l) ℤ := ((isUnit_iff_isUnit_det x).mpr hdet).unit
  have hγ : (γ : Matrix (l ⊕ l) (l ⊕ l) ℤ) = x := IsUnit.unit_spec _
  refine (mem_paramodular_iff d).mpr
    ⟨γ, (congrArg (fun A ↦ Aᵀ * paramodularForm d * A) hγ).trans hT, ?_⟩
  rw [hγ]
  exact eq_paramodularDelta_mul_mul_of_map_eq hx

lemma mem_paramodular_iff_exists_map_eq : M ∈ paramodular d ↔ ∃ x : Matrix (l ⊕ l) (l ⊕ l) ℤ,
    x.map (Int.castRingHom ℚ) = paramodularDeltaInv d * M * paramodularDelta d := by
  refine ⟨fun hM ↦ ?_, fun ⟨_, hx⟩ ↦ mem_paramodular_of_map_eq hx⟩
  rcases (mem_paramodular_iff d).mp hM with ⟨γ, -, hγ⟩
  refine ⟨γ, ?_⟩
  rw [hγ]
  simp only [Matrix.mul_assoc, paramodularDeltaInv_mul_paramodularDelta_mul,
    paramodularDeltaInv_mul_paramodularDelta, Matrix.mul_one]

variable (d) in
/-- **The paramodular group of type `d` is the stabiliser in `Sp(2g, ℚ)` of the lattice
`ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ`** (LMFDB `group.paramodular`, `paramodulargroup.sp2gr`): a symplectic
matrix `M` maps the lattice onto itself exactly when `δ⁻¹ M δ` is an integral isometry of `T`. For
`d = (1, N)` the lattice is `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ`. -/
lemma paramodular_eq_stabilizer : paramodular d =
    MulAction.stabilizer (symplecticGroup l ℚ) (paramodularLattice d : Set (l ⊕ l → ℚ)) := by
  ext M
  rw [MulAction.mem_stabilizer_set]
  refine ⟨fun hM v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [← inv_smul_smul M v]
    rcases mem_paramodular_iff_exists_map_eq.mp (inv_mem hM) with ⟨x, hx⟩
    exact mulVec_mem_paramodularLattice_of_map_eq hx hv
  · rcases mem_paramodular_iff_exists_map_eq.mp hM with ⟨x, hx⟩
    exact mulVec_mem_paramodularLattice_of_map_eq hx hv
  · exact mem_paramodular_iff_exists_map_eq.mpr <|
      exists_map_eq_of_forall_mulVec_mem fun v hv ↦ (h v).mpr hv

/-- **A symplectic matrix stabilises `ℤ^g ⊕ d₁ℤ ⊕ ⋯ ⊕ d_gℤ` exactly when it maps it into itself**:
`δ⁻¹ M δ` is then integral, of determinant `1`. -/
lemma mem_stabilizer_iff_forall_mulVec_mem :
    M ∈ MulAction.stabilizer (symplecticGroup l ℚ) (paramodularLattice d : Set (l ⊕ l → ℚ)) ↔
    ∀ v ∈ paramodularLattice d, (M : Matrix (l ⊕ l) (l ⊕ l) ℚ) *ᵥ v ∈ paramodularLattice d := by
  rw [← paramodular_eq_stabilizer, mem_paramodular_iff_exists_map_eq,
    forall_mulVec_mem_iff_exists_map_eq]

end SymplecticGroup

namespace SiegelUpperHalfSpace

open SymplecticGroup (paramodularDelta paramodularDeltaInv paramodularLattice)

variable (N : ℕ+)

/-- The matrix `[1, 1, 1, N⁻¹; 1, 1, 1, N⁻¹; 1, 1, 1, N⁻¹; N, N, N, 1]` of the scales of the
entries of the rational matrices mapping `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself, in the coordinates
`(e₁, e₂, f₁, f₂)`. -/
def paramodularWeakScale : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ :=
  fromBlocks !![1, 1; 1, 1] !![1, (N : ℚ)⁻¹; 1, (N : ℚ)⁻¹] !![1, 1; (N : ℚ), (N : ℚ)]
    !![1, (N : ℚ)⁻¹; (N : ℚ), 1]

/-- A rational matrix `X` has the **weaker shape** of LMFDB `group.paramodular`: it lies in
`[ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; Nℤ, Nℤ, Nℤ, ℤ]`, the shape of the rational matrices
mapping the lattice `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` of column vectors into itself
(`SiegelUpperHalfSpace.forall_mulVec_mem_iff_isParamodularWeakShape`). -/
def IsParamodularWeakShape (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) : Prop :=
  ∃ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, ∀ i j, X i j = paramodularWeakScale N i j * x i j

variable {N} {X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ} {M : symplecticGroup (Fin 2) ℚ}

lemma isParamodularWeakShape_iff_exists_map_eq : IsParamodularWeakShape N X ↔
    ∃ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, x.map (Int.castRingHom ℚ) =
    paramodularDeltaInv ![1, N] * X * paramodularDelta ![1, N] := by
  refine exists_congr fun x ↦ ?_
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i ↦ forall_congr' fun j ↦ ?_
  rw [SymplecticGroup.paramodularDeltaInv_eq_diagonal, SymplecticGroup.paramodularDelta_eq_diagonal,
    mul_diagonal, diagonal_mul, map_apply]
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by
    positivity
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [paramodularWeakScale] <;> constructor <;> intro h <;> rw [h] <;> field_simp

/-- **A rational matrix maps `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself exactly when it has the shape
`[ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; Nℤ, Nℤ, Nℤ, ℤ]`** (LMFDB `group.paramodular`). -/
lemma forall_mulVec_mem_iff_isParamodularWeakShape :
    (∀ v ∈ paramodularLattice ![1, N], X *ᵥ v ∈ paramodularLattice ![1, N]) ↔
    IsParamodularWeakShape N X := by
  rw [SymplecticGroup.forall_mulVec_mem_iff_exists_map_eq, isParamodularWeakShape_iff_exists_map_eq]

variable (N) in
/-- **The paramodular group `K(N)` is the stabiliser in `Sp(4, ℚ)` of the lattice
`ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` of column vectors** (LMFDB `group.paramodular`). -/
lemma paramodularLevel_eq_stabilizer : paramodularLevel N = MulAction.stabilizer
    (symplecticGroup (Fin 2) ℚ) (paramodularLattice ![1, N] : Set (Fin 2 ⊕ Fin 2 → ℚ)) :=
  SymplecticGroup.paramodular_eq_stabilizer _

/-- **The paramodular group `K(N)` comprises the symplectic matrices of the shape
`[ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; Nℤ, Nℤ, Nℤ, ℤ]`** (LMFDB `group.paramodular`):
these are the symplectic matrices mapping `ℤ ⊕ ℤ ⊕ ℤ ⊕ Nℤ` into itself, which then map it onto
itself. -/
lemma mem_paramodularLevel_iff_isParamodularWeakShape :
    M ∈ paramodularLevel N ↔ IsParamodularWeakShape N M := by
  rw [isParamodularWeakShape_iff_exists_map_eq, ← SymplecticGroup.mem_paramodular_iff_exists_map_eq]

/-- **The symplectic conditions force the stronger shape** (LMFDB `group.paramodular`): a
symplectic matrix of the shape `[ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; Nℤ, Nℤ, Nℤ, ℤ]` has
the shape `[ℤ, Nℤ, ℤ, ℤ; ℤ, ℤ, ℤ, N⁻¹ℤ; ℤ, Nℤ, ℤ, ℤ; Nℤ, Nℤ, Nℤ, ℤ]`, lying in `K(N)`. -/
lemma isParamodularShape_of_isParamodularWeakShape (h : IsParamodularWeakShape N M) :
    IsParamodularShape N M :=
  isParamodularShape_of_mem <| mem_paramodularLevel_iff_isParamodularWeakShape.mpr h

end SiegelUpperHalfSpace
