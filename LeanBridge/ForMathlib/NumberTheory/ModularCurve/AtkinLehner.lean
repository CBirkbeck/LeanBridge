import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CompactRiemannSurface
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Conj
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Matrix

/-!
# The Atkin–Lehner involutions of the modular curve `X₀(N)`

Let `Q ∥ N` and let `W = (Qx y; Nz Qt)` be an Atkin–Lehner matrix, of determinant `Q` (Tau Ceti's
`TauCeti.IsAtkinLehnerMatrix`). Divided by `√Q` it lies in `SL(2, ℝ)`, and its class in `PSL(2, ℝ)`
normalizes the image of `Γ₀(N)`, since `W γ = δ W` with `δ ∈ Γ₀(N)` for every `γ ∈ Γ₀(N)`, in both
directions (Tau Ceti's `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul_left` and
`TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_eq_mul_right`). So the Möbius map
`z ↦ (Qxz + y) / (Nzz + Qt)` induces, by Tau Ceti's
`Subgroup.CompactifiedQuotient.conjBiholomorph`, a biholomorphism `w_Q` of the compactified quotient
`X₀(N)(ℂ) = Γ₀(N) \ ℍ*`, the compact Riemann surface of the modular curve `X₀(N)`
(`LeanBridge.ForMathlib.NumberTheory.ModularCurve.CompactRiemannSurface`): the automorphism of
`X₀(N)` induced by `W` (LMFDB `cmf.atkin-lehner`). It is an involution, since `W² = Q γ` with
`γ ∈ Γ₀(N)` (Tau Ceti's `TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_mul_self`) and `γ` acts
trivially on the quotient, and it does not depend on the choice of `W`, since two Atkin–Lehner
matrices for `Q` differ by an element of `Γ₀(N)` (Tau Ceti's
`TauCeti.IsAtkinLehnerMatrix.exists_mem_Gamma0_eq_mul_left`). For `Q = N` it is the Fricke
involution.

## Main definitions

* `TauCeti.IsAtkinLehnerMatrix.toSL2R`: the matrix `W / √Q` in `SL(2, ℝ)`.
* `TauCeti.IsAtkinLehnerMatrix.toPSL2R`: the class of `W / √Q` in `PSL(2, ℝ)`.
* `TauCeti.IsAtkinLehnerMatrix.atkinLehnerX0` (LMFDB `cmf.atkin-lehner`): the Atkin–Lehner
  automorphism `w_Q` of `X₀(N)(ℂ) = Γ₀(N) \ ℍ*`, a biholomorphism.

## Main results

* `TauCeti.IsAtkinLehnerMatrix.coe_toPSL2R_smul`: `W / √Q` acts on `ℍ` by the Möbius map of `W`.
* `TauCeti.IsAtkinLehnerMatrix.conjAct_toPSL2R_smul`: it normalizes the image of `Γ₀(N)`.
* `TauCeti.IsAtkinLehnerMatrix.atkinLehnerX0_ofQuotient` (LMFDB `cmf.atkin-lehner`): `w_Q` sends
  the orbit of `z` to the orbit of `W z`.
* `TauCeti.IsAtkinLehnerMatrix.atkinLehnerX0_apply_atkinLehnerX0` (LMFDB `cmf.atkin-lehner`):
  `w_Q` is an involution.
* `TauCeti.IsAtkinLehnerMatrix.atkinLehnerX0_eq` (LMFDB `cmf.atkin-lehner`): `w_Q` does not depend
  on the Atkin–Lehner matrix.

## References

* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. 185 (1970), 134–160.
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.5.
-/

open Matrix CongruenceSubgroup MulAction UpperHalfPlane Subgroup

open scoped MatrixGroups Manifold Pointwise ContDiff

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)} {g g' : PSL(2, ℝ)}

lemma compactifiedQuotientConj_of_mem (hg : g ∈ Γ) (h : ConjAct.toConjAct g • Γ = Γ) :
    compactifiedQuotientConj h = id := by
  funext x
  cases x with
  | ofQuotient p =>
    induction p using Quotient.inductionOn with
    | h z =>
      rw [compactifiedQuotientConj_ofQuotient, quotientConjHomeomorph_mk]
      exact congrArg CompactifiedQuotient.ofQuotient (Quotient.sound ⟨⟨g, hg⟩, rfl⟩)
  | ofCusp C =>
    rcases cuspOrbitMk_surjective C with ⟨c, rfl⟩
    rw [compactifiedQuotientConj_ofCusp, cuspOrbitConjEquiv_cuspOrbitMk]
    exact congrArg CompactifiedQuotient.ofCusp ((cuspOrbitMk_eq_iff _ _).mpr ⟨⟨g, hg⟩, rfl⟩)

lemma compactifiedQuotientConj_congr (hgg : g = g') (h : ConjAct.toConjAct g • Γ = Γ)
    (h' : ConjAct.toConjAct g' • Γ = Γ) :
    compactifiedQuotientConj h = compactifiedQuotientConj h' := by
  subst hgg
  rfl

end Subgroup

namespace TauCeti.IsAtkinLehnerMatrix

variable {N Q : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ} (hM : IsAtkinLehnerMatrix N Q M) (hQ : Q ≠ 0)
    (hM' : IsAtkinLehnerMatrix N Q M') {γ δ : SL(2, ℤ)} (z : ℍ)

/-- An Atkin–Lehner matrix `W` of determinant `Q ≠ 0`, divided by `√Q`: an element of
`SL(2, ℝ)`. -/
noncomputable def toSL2R : SL(2, ℝ) :=
  ⟨(Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M, by
    rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt (Nat.cast_nonneg Q), ← RingHom.map_det,
      hM.det_eq, eq_intCast, Int.cast_natCast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hQ)]⟩

lemma toSL2R_mul_map (h : M * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * M) :
    hM.toSL2R hQ * SpecialLinearGroup.map (Int.castRingHom ℝ) γ =
      SpecialLinearGroup.map (Int.castRingHom ℝ) δ * hM.toSL2R hQ := by
  have hmat : (Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M *
      (Int.castRingHom ℝ).mapMatrix γ =
        (Int.castRingHom ℝ).mapMatrix δ * ((Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M) := by
    rw [smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul, h]
  ext i j
  exact congrFun (congrFun hmat i) j

lemma toSL2R_mul_self (h : M * M = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    hM.toSL2R hQ * hM.toSL2R hQ = SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by
  have hmat : (Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M *
      ((Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M) = (Int.castRingHom ℝ).mapMatrix γ := by
    rw [smul_mul_smul_comm, ← map_mul, h, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul,
      ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg Q), Int.cast_natCast,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hQ), one_smul]
  ext i j
  exact congrFun (congrFun hmat i) j

lemma toSL2R_eq_map_mul (h : M' = (γ : Matrix (Fin 2) (Fin 2) ℤ) * M) :
    hM'.toSL2R hQ = SpecialLinearGroup.map (Int.castRingHom ℝ) γ * hM.toSL2R hQ := by
  have hmat : (Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M' =
      (Int.castRingHom ℝ).mapMatrix γ * ((Real.sqrt Q)⁻¹ • (Int.castRingHom ℝ).mapMatrix M) := by
    rw [Matrix.mul_smul, ← map_mul, h]
  ext i j
  exact congrFun (congrFun hmat i) j

/-- The class in `PSL(2, ℝ)` of an Atkin–Lehner matrix `W` of determinant `Q ≠ 0`, divided by
`√Q`. It acts on `ℍ` by the Möbius map of `W` (`coe_toPSL2R_smul`). -/
noncomputable def toPSL2R : PSL(2, ℝ) :=
  hM.toSL2R hQ

lemma toPSL2R_mul_sl2zToPSL2R
    (h : M * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * M) :
    hM.toPSL2R hQ * sl2zToPSL2R γ = sl2zToPSL2R δ * hM.toPSL2R hQ := by
  rw [toPSL2R, sl2zToPSL2R_apply, sl2zToPSL2R_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hM.toSL2R_mul_map hQ h]

lemma toPSL2R_mul_self (h : M * M = (Q : ℤ) • (γ : Matrix (Fin 2) (Fin 2) ℤ)) :
    hM.toPSL2R hQ * hM.toPSL2R hQ = sl2zToPSL2R γ := by
  rw [toPSL2R, sl2zToPSL2R_apply, ← QuotientGroup.mk_mul, hM.toSL2R_mul_self hQ h]

lemma toPSL2R_eq_sl2zToPSL2R_mul (h : M' = (γ : Matrix (Fin 2) (Fin 2) ℤ) * M) :
    hM'.toPSL2R hQ = sl2zToPSL2R γ * hM.toPSL2R hQ := by
  rw [toPSL2R, toPSL2R, sl2zToPSL2R_apply, ← QuotientGroup.mk_mul, hM.toSL2R_eq_map_mul hQ hM' h]

/-- **`W / √Q` acts on `ℍ` by the Möbius map of the Atkin–Lehner matrix `W`**:
`z ↦ (Qxz + y) / (Nzz + Qt)` for `W = (Qx y; Nz Qt)`. -/
lemma coe_toPSL2R_smul : (↑(hM.toPSL2R hQ • z) : ℂ) =
    ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) / ((M 1 0 : ℂ) * z + (M 1 1 : ℂ)) := by
  have hs : ((Real.sqrt Q)⁻¹ : ℂ) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero hQ))))
  rw [toPSL2R, pslMk_smul, coe_specialLinearGroup_apply,
    ← mul_div_mul_left ((M 0 0 : ℂ) * z + (M 0 1 : ℂ)) ((M 1 0 : ℂ) * z + (M 1 1 : ℂ)) hs]
  simp [toSL2R]
  ring1

lemma mem_normalizer (hQN : Q ∣ N) :
    hM.toPSL2R hQ ∈ Subgroup.normalizer ((Gamma0 N).map sl2zToPSL2R : Set PSL(2, ℝ)) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x ↦ ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨γ, hγ, rfl⟩
    rcases hM.exists_mem_Gamma0_mul_eq_mul_left hQ hQN hγ with ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, by rw [hM.toPSL2R_mul_sl2zToPSL2R hQ h, mul_inv_cancel_right]⟩
  · rcases hx with ⟨δ, hδ, hδx⟩
    rcases hM.exists_mem_Gamma0_mul_eq_mul_right hQ hQN hδ with ⟨γ, hγ, h⟩
    refine ⟨γ, hγ, mul_left_cancel (a := hM.toPSL2R hQ) ?_⟩
    rw [hM.toPSL2R_mul_sl2zToPSL2R hQ h.symm, hδx, inv_mul_cancel_right]

/-- **An Atkin–Lehner matrix normalizes `Γ₀(N)` in `PSL(2, ℝ)`**: for `Q ∣ N`, conjugation by the
class of `W / √Q` preserves the image of `Γ₀(N)`. -/
lemma conjAct_toPSL2R_smul (hQN : Q ∣ N) :
    ConjAct.toConjAct (hM.toPSL2R hQ) • (Gamma0 N).map sl2zToPSL2R = (Gamma0 N).map sl2zToPSL2R :=
  Subgroup.conjAct_pointwise_smul_eq_self (hM.mem_normalizer hQ hQN)

variable [NeZero N]

/-- The **Atkin–Lehner involution `w_Q` of the modular curve `X₀(N)`** (LMFDB `cmf.atkin-lehner`):
the biholomorphism of the compact Riemann surface `X₀(N)(ℂ) = Γ₀(N) \ ℍ*` induced by an
Atkin–Lehner matrix `W` for `Q ∣ N`, sending the orbit of `z` to the orbit of `W z` and the cusp
orbit of `c` to that of `W c`. It is an involution (`atkinLehnerX0_apply_atkinLehnerX0`) and does
not depend on `W` (`atkinLehnerX0_eq`). -/
noncomputable def atkinLehnerX0 (hQN : Q ∣ N) :
    ((Gamma0 N).map sl2zToPSL2R).CompactifiedQuotient ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯
      ((Gamma0 N).map sl2zToPSL2R).CompactifiedQuotient :=
  CompactifiedQuotient.conjBiholomorph (hM.conjAct_toPSL2R_smul hQ hQN)

/-- **`w_Q` is induced by the Atkin–Lehner matrix** (LMFDB `cmf.atkin-lehner`): it sends the
`Γ₀(N)`-orbit of `z ∈ ℍ` to the orbit of `W z` (`coe_toPSL2R_smul`). -/
lemma atkinLehnerX0_ofQuotient (hQN : Q ∣ N) :
    hM.atkinLehnerX0 hQ hQN (.ofQuotient (Quotient.mk _ z)) =
      .ofQuotient (Quotient.mk _ (hM.toPSL2R hQ • z)) :=
  rfl

/-- **`w_Q` is an involution of `X₀(N)`** (LMFDB `cmf.atkin-lehner`): `W² = Q γ` with
`γ ∈ Γ₀(N)`, and `γ` acts trivially on `Γ₀(N) \ ℍ*`. -/
lemma atkinLehnerX0_apply_atkinLehnerX0 (hQN : Q ∣ N)
    (x : ((Gamma0 N).map sl2zToPSL2R).CompactifiedQuotient) :
    hM.atkinLehnerX0 hQ hQN (hM.atkinLehnerX0 hQ hQN x) = x := by
  rcases hM.exists_mem_Gamma0_mul_self hQ hQN with ⟨γ, hγ, h⟩
  have hmem : hM.toPSL2R hQ * hM.toPSL2R hQ ∈ (Gamma0 N).map sl2zToPSL2R :=
    hM.toPSL2R_mul_self hQ h ▸ Subgroup.mem_map_of_mem _ hγ
  exact (congrFun (Subgroup.compactifiedQuotientConj_comp (hM.conjAct_toPSL2R_smul hQ hQN)
    (hM.conjAct_toPSL2R_smul hQ hQN)) x).trans
      (congrFun (Subgroup.compactifiedQuotientConj_of_mem hmem _) x)

/-- **`w_Q` does not depend on the Atkin–Lehner matrix** (LMFDB `cmf.atkin-lehner`): two
Atkin–Lehner matrices for `Q ∣ N` differ by an element of `Γ₀(N)`, which acts trivially on
`Γ₀(N) \ ℍ*`. -/
lemma atkinLehnerX0_eq (hQN : Q ∣ N) : hM'.atkinLehnerX0 hQ hQN = hM.atkinLehnerX0 hQ hQN := by
  rcases hM.exists_mem_Gamma0_eq_mul_left hQ hQN hM' with ⟨γ, hγ, h⟩
  have hγ' : sl2zToPSL2R γ ∈ (Gamma0 N).map sl2zToPSL2R := Subgroup.mem_map_of_mem _ hγ
  have hγΓ : ConjAct.toConjAct (sl2zToPSL2R γ) • (Gamma0 N).map sl2zToPSL2R =
      (Gamma0 N).map sl2zToPSL2R :=
    Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hγ')
  refine Diffeomorph.ext fun x ↦ ?_
  exact (congrFun (Subgroup.compactifiedQuotientConj_congr
    (hM.toPSL2R_eq_sl2zToPSL2R_mul hQ hM' h) _ _) x).trans
      ((congrFun (Subgroup.compactifiedQuotientConj_comp (hM.conjAct_toPSL2R_smul hQ hQN) hγΓ)
        x).symm.trans (congrFun (Subgroup.compactifiedQuotientConj_of_mem hγ' hγΓ) _))

end TauCeti.IsAtkinLehnerMatrix
