import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Conjugate
import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.EisensteinFamily

/-!
# Galois conjugates of modular forms of level `Γ₁(N)`

Let `σ` be a field endomorphism of `ℂ`, for instance an automorphism. For a modular form
`f = ∑ aₙ qⁿ` of level `Γ₁(N)` and weight `k`, the series `∑ σ(aₙ) qⁿ` is the `q`-expansion of a
modular form of level `Γ₁(N)` and weight `k`, in every weight, weight one included (compare Shimura,
*Introduction to the arithmetic theory of automorphic functions*, Theorem 3.52, on bases of forms
with rational Fourier coefficients). It is a cusp form if `f` is one, and the conjugation commutes
with the diamond operators, so that it sends a form of nebentypus `χ` to one of nebentypus `σ ∘ χ`.

The proof applies `TauCeti.GaloisAction.exists_modularForm_qExpansion_eq_map` to the Eisenstein
series `θ_1`, the form `TauCeti.GaloisAction.rowForm` at `1`: it is a primitive element for `Γ₁(N)`
over level one, of odd weight if `N ≥ 3`, and `σ` permutes the `q`-expansions of the series `θ_e`.

## Main definitions

* `TauCeti.GaloisAction.primitiveWeight`: the weight of the primitive element.

## Main results

* `TauCeti.GaloisAction.exists_modularForm_Gamma1_qExpansion_eq_map`: the conjugate of a modular
  form of level `Γ₁(N)`.
* `TauCeti.GaloisAction.exists_cuspForm_Gamma1_qExpansion_eq_map`: the conjugate of a cusp form of
  level `Γ₁(N)`.
* `TauCeti.GaloisAction.mem_cuspFormCharSpace_of_qExpansion_diamond_eq_map`: the conjugate of a
  cusp form of nebentypus `χ` is a cusp form of nebentypus `σ ∘ χ`.
-/

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix SpecialLinearGroup Subgroup

open scoped MatrixGroups

namespace TauCeti.GaloisAction

variable (σ : ℂ →+* ℂ) {N : ℕ} {k : ℤ}

variable (N) in
/-- The weight of the Eisenstein series used as a primitive element for `Γ₁(N)`: `3` if `N ≥ 3`, and
`4` otherwise. -/
def primitiveWeight : ℕ :=
  if 3 ≤ N then 3 else 4

lemma three_le_primitiveWeight : 3 ≤ primitiveWeight N := by
  unfold primitiveWeight
  split_ifs <;> simp

lemma isPrimitiveWeight_primitiveWeight : IsPrimitiveWeight N (primitiveWeight N) := by
  unfold primitiveWeight
  split_ifs with h
  · exact Or.inl ⟨by decide, h⟩
  · exact Or.inr ⟨by decide, by omega⟩

/-- **The conjugate of a cusp form of nebentypus `χ` has nebentypus `σ ∘ χ`.** -/
lemma mem_cuspFormCharSpace_of_qExpansion_diamond_eq_map {χ : (ZMod N)ˣ →* ℂˣ}
    {f F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ)
    (hQ : qExpansion 1 F = PowerSeries.map σ (qExpansion 1 f))
    (hd : ∀ d : (ZMod N)ˣ, qExpansion 1 (diamondOpCusp k d F) =
      PowerSeries.map σ (qExpansion 1 (diamondOpCusp k d f))) :
    F ∈ cuspFormCharSpace k ((Units.map (σ : ℂ →* ℂ)).comp χ) := by
  rw [mem_cuspFormCharSpace_iff]
  intro d
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  refine CuspForm.qExpansion_injective one_pos h1 ?_
  have h : qExpansion 1 (diamondOpCusp k d F) =
      PowerSeries.map σ (qExpansion 1 (diamondOpCusp k d f)) := hd d
  rw [diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ d hf, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos h1, map_smul_powerSeries, ← hQ] at h
  beta_reduce
  rw [diamondOpCuspHom_apply, h, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos h1]
  rfl

variable [NeZero N]

/-- **The conjugate of a modular form of level `Γ₁(N)`.** For a field endomorphism `σ` of `ℂ` and a
modular form `f` of level `Γ₁(N)` and weight `k`, the series `∑ σ(aₙ) qⁿ` is the `q`-expansion of a
modular form `F` of level `Γ₁(N)` and weight `k`. It is a cusp form if `f` is one, and `σ` sends the
`q`-expansion of the diamond translate `⟨d⟩ f` to that of `⟨d⟩ F`. -/
lemma exists_modularForm_Gamma1_qExpansion_eq_map (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      qExpansion 1 F = PowerSeries.map σ (qExpansion 1 f) ∧
      (IsCuspForm ((Gamma1 N).map (mapGL ℝ)) k f → IsCuspForm ((Gamma1 N).map (mapGL ℝ)) k F) ∧
      ∀ d : (ZMod N)ˣ, qExpansion 1 (diamondOp k d F) =
        PowerSeries.map σ (qExpansion 1 (diamondOp k d f)) := by
  have hK : 3 ≤ primitiveWeight N := three_le_primitiveWeight
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  rcases exists_map_stdAddChar (N := N) σ with ⟨u, hu⟩
  have hθ' : PowerSeries.map σ (qExpansion 1 (rowForm hK (1 : ZMod N))) =
      qExpansion 1 (rowForm hK ((u : ZMod N) * 1)) :=
    map_qExpansion_rowForm 1 hK σ hu
  rcases exists_modularForm_qExpansion_eq_map f (map_le_range _ _) h1
    (quotientFunc_rowForm_one_ne hK isPrimitiveWeight_primitiveWeight) hθ'.symm with
    ⟨F, hQ, hc, hδ⟩
  refine ⟨F, hQ, hc, fun d ↦ ?_⟩
  rcases Gamma0Map_toHomUnits_surjective (N := N) d with ⟨g, hg⟩
  have hF : ⇑(diamondOp k d F) = ⇑F ∣[k] (g : SL(2, ℤ)) := coe_diamondOp k d g hg F
  have hf : ⇑(diamondOp k d f) = ⇑f ∣[k] (g : SL(2, ℤ)) := coe_diamondOp k d g hg f
  have hθ₁ : ⇑(rowForm hK (1 : ZMod N)) ∣[(primitiveWeight N : ℤ)] (g : SL(2, ℤ)) =
      rowForm hK ((1 : ZMod N) * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) :=
    rowForm_slash (1 : ZMod N) hK g.2
  have hθ₂ : ⇑(rowForm hK ((u : ZMod N) * 1)) ∣[(primitiveWeight N : ℤ)] (g : SL(2, ℤ)) =
      rowForm hK ((u : ZMod N) * 1 * (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)) :=
    rowForm_slash ((u : ZMod N) * 1) hK g.2
  rw [hF, hf]
  refine hδ g (hf ▸ (isForm_coe _).hasQExpansion h1) (hθ₁ ▸ (isForm_coe _).hasQExpansion h1)
    (hθ₂ ▸ (isForm_coe _).hasQExpansion h1) (hF ▸ (isForm_coe _).hasQExpansion h1) ?_
  rw [hθ₁, hθ₂, map_qExpansion_rowForm _ hK σ hu, mul_assoc]

/-- **The conjugate of a cusp form of level `Γ₁(N)`.** For a field endomorphism `σ` of `ℂ` and a
cusp form `f` of level `Γ₁(N)` and weight `k`, the series `∑ σ(aₙ) qⁿ` is the `q`-expansion of a
cusp form `F` of level `Γ₁(N)` and weight `k`, and `σ` sends the `q`-expansion of the diamond
translate `⟨d⟩ f` to that of `⟨d⟩ F`. -/
lemma exists_cuspForm_Gamma1_qExpansion_eq_map (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∃ F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      qExpansion 1 F = PowerSeries.map σ (qExpansion 1 f) ∧ ∀ d : (ZMod N)ˣ,
        qExpansion 1 (diamondOpCusp k d F) =
          PowerSeries.map σ (qExpansion 1 (diamondOpCusp k d f)) := by
  rcases exists_modularForm_Gamma1_qExpansion_eq_map σ
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) with ⟨F, hQ, hc, hd⟩
  rcases hc ⟨f, rfl⟩ with ⟨F', hF'⟩
  have hFF' : (F' : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = F := DFunLike.coe_injective hF'
  refine ⟨F', hF' ▸ hQ, fun d ↦ ?_⟩
  have hd' : qExpansion 1 (diamondOp k d (F' : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      PowerSeries.map σ
        (qExpansion 1 (diamondOp k d (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))) :=
    hFF' ▸ hd d
  rw [diamondOp_coe_cuspForm, diamondOp_coe_cuspForm] at hd'
  exact hd'

end TauCeti.GaloisAction
