import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EllipticPointStabilizer
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.MaximalOrderConjugate

/-!
# The maximal orders of `M₂(ℚ)` form one conjugacy class

LMFDB `shimcurve.order` says that the maximal orders of a quaternion algebra `B` over `ℚ` fall into
finitely many `B^×`-conjugacy classes, and that in many cases there is exactly one. This file proves
that there is exactly one for the quaternion algebra `M₂(ℚ)`: its maximal orders are exactly the
conjugates `γ M₂(ℤ) γ⁻¹`, `γ ∈ GL₂(ℚ)`, of the integral matrices.

The integral matrices form a maximal order: the reduced trace of `M₂(ℚ)` is the trace of matrices
and is an integer on every order, so for `x` in an order containing `M₂(ℤ)` each entry
`x_{ij} = tr(E_{ji} x)` is an integer. Every order `O` of `M₂(ℚ)` lies in a conjugate of `M₂(ℤ)`:
the `ℤ`-span `L` of the columns of the elements of `O` is finitely generated and contains `ℤ²`, as
`1 ∈ O`, so it is a lattice of `ℚ²`, and `O` maps it into itself; a `ℤ`-basis of `L` is a `ℚ`-basis
of `ℚ²`, the columns of a matrix `γ`, in which every element of `O` acts by an integral matrix, so
that `γ⁻¹ O γ ⊆ M₂(ℤ)`. Hence a maximal order is a conjugate `γ M₂(ℤ) γ⁻¹`, and these are maximal
orders: they are the orders `{x : x L ⊆ L}` of the lattices `L = γ ℤ²` of `ℚ²`.

Here `M₂(ℤ)` is the range of the entrywise map `M₂(ℤ) → M₂(ℚ)`, an order by
`Subalgebra.isQuaternionOrder_range_mapMatrix`.

## Main results

* `Module.Basis.extendOfIsLattice_repr`: the coordinates of a vector of a lattice in the basis
  extending a basis of the lattice are those in the basis of the lattice.
* `QuaternionAlgebra.reducedTrace_matrix`: the reduced trace of `M₂(ℚ)` is the trace.
* `Subalgebra.isMaximalQuaternionOrder_range_mapMatrix` (LMFDB `shimcurve.order`): the integral
  matrices form a maximal order of `M₂(ℚ)`.
* `Subalgebra.exists_le_map_conj_range_mapMatrix` (LMFDB `shimcurve.order`): every order of
  `M₂(ℚ)` lies in a conjugate of `M₂(ℤ)`.
* `Subalgebra.isMaximalQuaternionOrder_iff_exists_eq_map_conj` (LMFDB `shimcurve.order`): the
  maximal orders of `M₂(ℚ)` are the conjugates of `M₂(ℤ)`.
* `Subalgebra.exists_eq_map_conj_of_isMaximalQuaternionOrder` (LMFDB `shimcurve.order`): any two
  maximal orders of `M₂(ℚ)` are conjugate, so they form exactly one `GL₂(ℚ)`-conjugacy class.
-/

open Matrix Module QuaternionAlgebra Submodule

namespace Module.Basis

variable {R K V κ : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V] {M : Submodule R V}
  [IsLattice K M] [Fintype κ]

variable (K) in
/-- **The coordinates of a vector of a lattice in the extended basis are those in the basis of the
lattice**: for a basis `b` of an `R`-lattice `M` of a `K`-vector space `V`, the `K`-basis
`b.extendOfIsLattice K` of `V` gives `v ∈ M` the coordinates of `v` in `b`, mapped to `K`. -/
lemma extendOfIsLattice_repr (b : Basis κ R M) (v : M) (k : κ) :
    (b.extendOfIsLattice K).repr v k = algebraMap R K (b.repr v k) := by
  have h : (v : V) = ∑ j, algebraMap R K (b.repr v j) • b.extendOfIsLattice K j := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [coe_sum, Submodule.coe_smul, extendOfIsLattice_apply, algebraMap_smul]
  rw [h, repr_sum_self]

end Module.Basis

namespace QuaternionAlgebra

/-- **The reduced trace of `M₂(ℚ)` is the trace of matrices**: left multiplication by `x` on the
`4`-dimensional `M₂(ℚ)` has trace `2 tr(x)`. -/
lemma reducedTrace_matrix (x : Matrix (Fin 2) (Fin 2) ℚ) : reducedTrace _ x = x.trace := by
  have h : LinearMap.mulLeft ℚ x = LinearMap.mulLeftRight ℚ (x, 1) := by
    ext
    simp
  rw [reducedTrace, h, trace_mulLeftRight_fin_two, trace_one, Fintype.card_fin]
  push_cast
  ring1

end QuaternionAlgebra

namespace Subalgebra

variable {O O₁ O₂ : Subalgebra ℤ (Matrix (Fin 2) (Fin 2) ℚ)}

/-- **The integral matrices form a maximal order of `M₂(ℚ)`** (LMFDB `shimcurve.order`): for `x` in
an order `O` containing `M₂(ℤ)`, each entry `x_{ij} = tr(E_{ji} x)` of `x` is the reduced trace of
an element of `O`, an integer. -/
lemma isMaximalQuaternionOrder_range_mapMatrix :
    ((Algebra.ofId ℤ ℚ).mapMatrix (m := Fin 2)).range.IsMaximalQuaternionOrder := by
  refine ⟨isQuaternionOrder_range_mapMatrix, fun O hO hle x hx ↦ ?_⟩
  have hE (i j : Fin 2) : single j i (1 : ℚ) ∈ O :=
    hle ⟨single j i 1, by simp⟩
  choose z hz using fun i j ↦
    exists_reducedTrace_eq_intCast (by simp [finrank_matrix]) hO (mul_mem (hE i j) hx)
  refine ⟨of z, Matrix.ext fun i j ↦ ?_⟩
  simp [← hz, reducedTrace_matrix, trace_single_mul]

/-- **Every order of `M₂(ℚ)` lies in a conjugate of `M₂(ℤ)`** (LMFDB `shimcurve.order`): the
`ℤ`-span `L` of the columns of the elements of an order `O` is a lattice of `ℚ²` which `O` maps
into itself, and for a matrix `γ` whose columns form a `ℤ`-basis of `L`, `γ⁻¹ O γ ⊆ M₂(ℤ)`. -/
lemma exists_le_map_conj_range_mapMatrix (hO : O.IsQuaternionOrder) :
    ∃ γ : (Matrix (Fin 2) (Fin 2) ℚ)ˣ, O ≤ ((Algebra.ofId ℤ ℚ).mapMatrix (m := Fin 2)).range.map
      (MulSemiringAction.toAlgHom ℤ _ (ConjAct.toConjAct γ)) := by
  let f (k : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ →ₗ[ℤ] Fin 2 → ℚ :=
    (mulVec.addMonoidHomLeft (Pi.single k 1)).toIntLinearMap
  have hf (k : Fin 2) (x : Matrix (Fin 2) (Fin 2) ℚ) : f k x = x *ᵥ Pi.single k 1 := rfl
  let L : Submodule ℤ (Fin 2 → ℚ) := ⨆ k, (toSubmodule O).map (f k)
  have hL {x : Matrix (Fin 2) (Fin 2) ℚ} (hx : x ∈ O) {v : Fin 2 → ℚ} (hv : v ∈ L) :
      x *ᵥ v ∈ L := by
    refine iSup_induction _ (motive := fun v ↦ x *ᵥ v ∈ L) hv (fun k v hv ↦ ?_) ?_
      fun v w hv hw ↦ ?_
    · rcases hv with ⟨y, hy, rfl⟩
      exact mem_iSup_of_mem k ⟨x * y, (mul_mem hx hy : x * y ∈ O), by rw [hf, hf, mulVec_mulVec]⟩
    · rw [mulVec_zero]
      exact zero_mem L
    · rw [mulVec_add]
      exact add_mem hv hw
  have _ : IsLattice ℚ L := by
    refine ⟨fg_iSup _ fun k ↦ hO.fg.map _, eq_top_iff.mpr <|
      (Pi.basisFun ℚ (Fin 2)).span_eq.symm.trans_le <| span_mono ?_⟩
    rintro _ ⟨k, rfl⟩
    exact mem_iSup_of_mem k ⟨1, one_mem O, by rw [hf, one_mulVec, Pi.basisFun_apply]⟩
  let b : Basis (Fin 2) ℤ L :=
    finBasisOfFinrankEq ℤ L (by rw [IsLattice.finrank_of_pi ℚ L, Fintype.card_fin])
  let c : Basis (Fin 2) ℚ (Fin 2 → ℚ) := b.extendOfIsLattice ℚ
  let P : Matrix (Fin 2) (Fin 2) ℚ := (Pi.basisFun ℚ (Fin 2)).toMatrix c
  let Q : Matrix (Fin 2) (Fin 2) ℚ := c.toMatrix (Pi.basisFun ℚ (Fin 2))
  have hPQ : P * Q = 1 := (Pi.basisFun ℚ (Fin 2)).toMatrix_mul_toMatrix_flip c
  have hQP : Q * P = 1 := c.toMatrix_mul_toMatrix_flip (Pi.basisFun ℚ (Fin 2))
  refine ⟨⟨P, Q, hPQ, hQP⟩, fun x hx ↦ ⟨Q * x * P, ?_, ?_⟩⟩
  · have hc (j : Fin 2) : x *ᵥ c j ∈ L := hL hx (by simp [c])
    have hx' : Q * x * P = LinearMap.toMatrix c c (toLin' x) := by
      rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c (Pi.basisFun ℚ (Fin 2)) c
        (Pi.basisFun ℚ (Fin 2)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    refine ⟨of fun i j ↦ b.repr ⟨x *ᵥ c j, hc j⟩ i, ?_⟩
    rw [hx']
    ext i j
    simp only [LinearMap.toMatrix_apply]
    exact (b.extendOfIsLattice_repr ℚ ⟨x *ᵥ c j, hc j⟩ i).symm
  · have h : P * (Q * x * P) * Q = x := by
      rw [← mul_assoc, ← mul_assoc, hPQ, one_mul, mul_assoc, hPQ, mul_one]
    simpa only [AlgHom.coe_toRingHom, MulSemiringAction.toAlgHom_apply, ConjAct.units_smul_def,
      ConjAct.ofConjAct_toConjAct, Units.inv_mk] using h

/-- **The maximal orders of `M₂(ℚ)` are the conjugates of `M₂(ℤ)`** (LMFDB `shimcurve.order`): an
order of `M₂(ℚ)` is maximal exactly when it is `γ M₂(ℤ) γ⁻¹` for some `γ ∈ GL₂(ℚ)`. -/
lemma isMaximalQuaternionOrder_iff_exists_eq_map_conj : O.IsMaximalQuaternionOrder ↔
    ∃ γ : (Matrix (Fin 2) (Fin 2) ℚ)ˣ, O = ((Algebra.ofId ℤ ℚ).mapMatrix (m := Fin 2)).range.map
      (MulSemiringAction.toAlgHom ℤ _ (ConjAct.toConjAct γ)) := by
  refine ⟨fun hO ↦ ?_, ?_⟩
  · rcases exists_le_map_conj_range_mapMatrix hO.prop with ⟨γ, hγ⟩
    exact ⟨γ, le_antisymm hγ (hO.le_of_ge (isMaximalQuaternionOrder_range_mapMatrix.map
      (MulSemiringAction.toAlgEquiv ℚ _ (ConjAct.toConjAct γ))).prop hγ)⟩
  · rintro ⟨γ, rfl⟩
    exact isMaximalQuaternionOrder_range_mapMatrix.map
      (MulSemiringAction.toAlgEquiv ℚ _ (ConjAct.toConjAct γ))

/-- **Any two maximal orders of `M₂(ℚ)` are conjugate** (LMFDB `shimcurve.order`): `M₂(ℚ)` has
exactly one `B^×`-conjugacy class of maximal orders, the class of `M₂(ℤ)`. -/
lemma exists_eq_map_conj_of_isMaximalQuaternionOrder (h₁ : O₁.IsMaximalQuaternionOrder)
    (h₂ : O₂.IsMaximalQuaternionOrder) : ∃ γ : (Matrix (Fin 2) (Fin 2) ℚ)ˣ,
      O₂ = O₁.map (MulSemiringAction.toAlgHom ℤ _ (ConjAct.toConjAct γ)) := by
  rcases isMaximalQuaternionOrder_iff_exists_eq_map_conj.mp h₁ with ⟨γ₁, rfl⟩
  rcases isMaximalQuaternionOrder_iff_exists_eq_map_conj.mp h₂ with ⟨γ₂, rfl⟩
  refine ⟨γ₂ * γ₁⁻¹, ?_⟩
  rw [map_map]
  congr 1
  ext x
  simp [ConjAct.units_smul_def, mul_assoc]

end Subalgebra
