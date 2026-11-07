import Mathlib.LinearAlgebra.Matrix.Unique
import TauCeti.Algebra.CentralSimple.BaseChange
import TauCeti.Algebra.CentralSimple.Wedderburn
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder

/-!
# Indefinite quaternion algebras over `ℚ`

A quaternion algebra `B` over `ℚ`, a central simple `ℚ`-algebra of dimension `4`, is indefinite
(LMFDB `shimcurve.quaternion_algebra`) if `ℝ ⊗ B` is split, that is, isomorphic to `M₂(ℝ)`. The
polarized orders of `shimcurve.polarized_order` are formalised with
`QuaternionAlgebra.IsIndefinite B`: `ℝ ⊗ B` is not a division algebra. The two agree
(`QuaternionAlgebra.isIndefinite_iff_nonempty_algEquiv_matrix`), by the split-or-division
dichotomy for central simple real algebras of dimension `4`
(`QuaternionAlgebra.not_forall_isUnit_iff_nonempty_algEquiv_matrix`): by Wedderburn–Artin such an
algebra is `Mₙ(D)` for a central division algebra `D` with `n² dim D = 4`, so it is either a
division algebra (`n = 1`) or `M₂(ℝ)` (`n = 2`, `D = ℝ`). So a polarized order of a quaternion
algebra over `ℚ` (`PolarizedQuaternionOrder`) has `ℝ ⊗ B ≅ M₂(ℝ)`
(`PolarizedQuaternionOrder.nonempty_algEquiv_matrix`).

## Main results

* `QuaternionAlgebra.not_forall_isUnit_iff_nonempty_algEquiv_matrix`: a central simple real
  algebra of dimension `4` is not a division algebra exactly when it is isomorphic to `M₂(ℝ)`.
* `QuaternionAlgebra.isIndefinite_iff_nonempty_algEquiv_matrix` (LMFDB `shimcurve.polarized_order`,
  `shimcurve.quaternion_algebra`): a quaternion algebra `B` over `ℚ` is indefinite exactly when
  `ℝ ⊗ B ≅ M₂(ℝ)`.
* `PolarizedQuaternionOrder.nonempty_algEquiv_matrix` (LMFDB `shimcurve.polarized_order`): the
  quaternion algebra of a polarized order is indefinite in the sense of
  `shimcurve.quaternion_algebra`.
-/

open Module TauCeti

open scoped TensorProduct

namespace QuaternionAlgebra

/-- **The split-or-division dichotomy over `ℝ`**: a central simple `ℝ`-algebra of dimension `4` is
not a division algebra exactly when it is isomorphic to `M₂(ℝ)`. -/
lemma not_forall_isUnit_iff_nonempty_algEquiv_matrix (A : Type*) [Ring A] [Algebra ℝ A]
    [Algebra.IsCentral ℝ A] [IsSimpleRing A] [FiniteDimensional ℝ A] (h4 : finrank ℝ A = 4) :
    (¬∀ y : A, y ≠ 0 → IsUnit y) ↔ Nonempty (A ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ hu ↦ ?_⟩
  · rcases IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing ℝ A with
      ⟨n, _, D, _, _, _, _, hrank, ⟨e⟩⟩
    have hd : 0 < finrank ℝ D := finrank_pos
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have hn2 : n ≤ 2 := by nlinarith
    interval_cases n
    · let φ : A ≃+* D := e.toRingEquiv.trans Matrix.uniqueRingEquiv
      exact absurd (fun y hy ↦ (isUnit_map_iff φ y).mp <|
        isUnit_iff_ne_zero.mpr <| (map_ne_zero_iff φ φ.injective).mpr hy) h
    · have hbot : (⊥ : Subalgebra ℝ D) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr <| by
        norm_num at hrank
        omega
      exact ⟨e.trans <| AlgEquiv.mapMatrix <| Subalgebra.topEquiv.symm.trans <|
        (Subalgebra.equivOfEq _ _ hbot.symm).trans (Algebra.botEquiv ℝ D)⟩
  · have hs : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℝ) ≠ 0 := fun h ↦ by
      simpa using congrFun₂ h 0 0
    exact absurd ((hu (e.symm (Matrix.single 0 0 1)) (by simpa using hs)).map e)
      (by simp [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two])

variable (B : Type*) [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  [FiniteDimensional ℚ B]

/-- **A quaternion algebra over `ℚ` is indefinite exactly when `ℝ ⊗ B ≅ M₂(ℝ)`** (LMFDB
`shimcurve.polarized_order`, `shimcurve.quaternion_algebra`): for a central simple `ℚ`-algebra `B`
of dimension `4`, `QuaternionAlgebra.IsIndefinite B`, that `ℝ ⊗ B` is not a division algebra, is
the splitting of `ℝ ⊗ B`. -/
lemma isIndefinite_iff_nonempty_algEquiv_matrix (h4 : finrank ℚ B = 4) :
    IsIndefinite B ↔ Nonempty (ℝ ⊗[ℚ] B ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  not_forall_isUnit_iff_nonempty_algEquiv_matrix _ <| by rw [finrank_baseChange, h4]

end QuaternionAlgebra

namespace PolarizedQuaternionOrder

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  [FiniteDimensional ℚ B]

/-- **The quaternion algebra of a polarized order is indefinite** in the sense of LMFDB
`shimcurve.quaternion_algebra` (LMFDB `shimcurve.polarized_order`): if `B` is a quaternion algebra
over `ℚ`, then `ℝ ⊗ B ≅ M₂(ℝ)`. -/
lemma nonempty_algEquiv_matrix (P : PolarizedQuaternionOrder B) (h4 : finrank ℚ B = 4) :
    Nonempty (ℝ ⊗[ℚ] B ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  (QuaternionAlgebra.isIndefinite_iff_nonempty_algEquiv_matrix B h4).mp P.isIndefinite

end PolarizedQuaternionOrder
