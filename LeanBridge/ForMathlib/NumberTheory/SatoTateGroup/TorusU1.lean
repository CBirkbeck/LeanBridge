import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.ComponentProbability
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.EllipticCurve

/-!
# The two constructions of the Sato–Tate group `U(1)`

The Sato–Tate group `U(1)` of weight `1` and degree `2` (LMFDB `1.2.B.1.1a`) has two constructions:
`SatoTateGroup.torusU1`, the image of the whole circle in the diagonal torus of `USp(2)`, for the
event probabilities (LMFDB `st_group.probabilities`), and `WeierstrassCurve.satoTateU1`, the group
of the unitary matrices `diag(u, ū)`, the Sato–Tate group of an elliptic curve with complex
multiplication (LMFDB `ag.sato_tate_group`). They are the same Sato–Tate group: the matrix
`diag(u, u⁻¹)` of the torus is `diag(u, ū)` for `|u| = 1`, and the entry `u` of a unitary matrix
`diag(u, ū)` has `|u| = 1`.

## Main results

* `SatoTateGroup.torusU1_eq_satoTateU1`: the two constructions of `U(1)` agree.
-/

open Matrix WeierstrassCurve

namespace SatoTateGroup

/-- **The two constructions of the Sato–Tate group `U(1)` agree**: the image of the circle in the
diagonal torus of `USp(2)` is the group of the unitary matrices `diag(u, ū)`. -/
lemma torusU1_eq_satoTateU1 : torusU1 = satoTateU1 := by
  have h : (⊤ : Subgroup (Fin 1 → Circle)).map (uspTorusHom 1) = satoTateTorus := by
    ext U
    refine ⟨?_, fun hU ↦ ?_⟩
    · rintro ⟨x, -, rfl⟩
      exact ⟨rfl, rfl, Circle.coe_inv_eq_conj (x 0)⟩
    · rcases hU with ⟨h01, h10, h11⟩
      have hstar : (star (U : Matrix (Fin 2) (Fin 2) ℂ) * U) 0 0 = 1 := by
        rw [Unitary.star_mul_self_of_mem U.2, one_apply_eq]
      have hu : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
        simp [mul_apply, h10, Complex.conj_mul'] at hstar
        rcases hstar with h | h
        · exact_mod_cast h
        · have h' : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = -1 := mod_cast h
          linarith [norm_nonneg ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0)]
      refine ⟨fun _ ↦ ⟨_, mem_sphere_zero_iff_norm.mpr hu⟩, Subgroup.mem_top _, Subtype.ext ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      exacts [rfl, h01.symm, h10.symm, (Circle.coe_inv_eq_conj _).trans h11.symm]
  unfold torusU1 ofTorus satoTateU1
  congr 1

end SatoTateGroup
