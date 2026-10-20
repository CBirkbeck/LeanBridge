import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.ClassDegree
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.CyclicDual

/-!
# The isogeny matrix of an isogeny class

The isogeny matrix of the isogeny class of an elliptic curve `W` over a field `K` is indexed by the
isomorphism classes in the isogeny class. Its `(c, c')` entry is the least degree of a cyclic
isogeny over `K` from a curve in `c` to a curve in `c'`. Over a field of characteristic zero it is
symmetric, the dual of a cyclic isogeny being a cyclic isogeny of the same degree back.

The LMFDB orders the rows and columns by the last component of the LMFDB labels of the curves; here
they are indexed by the isomorphism classes themselves.

## Main definitions

* `WeierstrassCurve.isogenyMatrix` (LMFDB `ec.isogeny_matrix`): the isogeny matrix.

## Main results

* `WeierstrassCurve.isogenyMatrix_apply_mk`: the entry at the classes of two curves is the least
  degree of a cyclic isogeny between those curves.
* `WeierstrassCurve.isogenyMatrix_apply_self`: the diagonal entries are `1`.
* `WeierstrassCurve.isSymm_isogenyMatrix`: over a field of characteristic zero, the isogeny matrix
  is symmetric.
-/

open Matrix TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W : WeierstrassCurve K}

variable (W) in
/-- The **isogeny matrix** (LMFDB `ec.isogeny_matrix`) of an elliptic curve `W` over `K`: the
matrix indexed by the isomorphism classes in the isogeny class of `W` whose `(c, c')` entry is the
least degree of a cyclic isogeny over `K` (`TauCeti.Isogeny.IsCyclic`) from a curve in `c` to a
curve in `c'`. Over a field of characteristic zero it is symmetric (`isSymm_isogenyMatrix`). The
LMFDB orders its rows and columns by the LMFDB labels of the curves. -/
noncomputable def isogenyMatrix : Matrix W.isogenyClass W.isogenyClass ℕ :=
  Matrix.of fun c c' ↦ sInf (c.1.cyclicIsogenyDegrees c'.1)

/-- **The entry of the isogeny matrix at the classes of two curves is the least degree of a cyclic
isogeny between them.** -/
lemma isogenyMatrix_apply_mk {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
    (h₁ : (⟦W₁⟧ : IsomorphismClass K) ∈ W.isogenyClass)
    (h₂ : (⟦W₂⟧ : IsomorphismClass K) ∈ W.isogenyClass) : W.isogenyMatrix ⟨_, h₁⟩ ⟨_, h₂⟩ =
    sInf {n | ∃ φ : Isogeny W₁.toAffine W₂.toAffine, φ.IsCyclic ∧ φ.degree = n} :=
  congrArg sInf <| Set.ext fun _ ↦ IsomorphismClass.mk_mem_cyclicIsogenyDegrees_iff

/-- **The diagonal entries of the isogeny matrix are `1`**, the identity being a cyclic isogeny of
degree `1`. -/
lemma isogenyMatrix_apply_self (c : W.isogenyClass) : W.isogenyMatrix c c = 1 := by
  rcases exists_isElliptic_of_mem_isogenyClass c.2 with ⟨W', _, hW'⟩
  exact IsLeast.csInf_eq ⟨hW' ▸ IsomorphismClass.one_mem_cyclicIsogenyDegrees W', fun _ ↦
    IsomorphismClass.pos_of_mem_cyclicIsogenyDegrees⟩

variable [CharZero K]

lemma IsomorphismClass.cyclicIsogenyDegrees_subset {c c' : IsomorphismClass K} :
    c.cyclicIsogenyDegrees c' ⊆ c'.cyclicIsogenyDegrees c := by
  rintro _ ⟨W₁, W₂, _, _, rfl, rfl, φ, hφ, rfl⟩
  exact ⟨W₂, W₁, ‹_›, ‹_›, rfl, rfl, φ.dual, hφ.dual, φ.degree_dual⟩

/-- **The isogeny matrix is symmetric** over a field of characteristic zero: the dual of a cyclic
isogeny is a cyclic isogeny of the same degree in the other direction. -/
lemma isSymm_isogenyMatrix : W.isogenyMatrix.IsSymm :=
  IsSymm.ext fun _ _ ↦ congrArg sInf <| IsomorphismClass.cyclicIsogenyDegrees_subset.antisymm
    IsomorphismClass.cyclicIsogenyDegrees_subset

end WeierstrassCurve
