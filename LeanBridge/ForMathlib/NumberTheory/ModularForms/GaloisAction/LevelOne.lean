import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion

/-!
# Conjugates of level one modular forms by field automorphisms

A field endomorphism `σ` of `ℂ` acts on power series through their coefficients. This file shows
that the space `M_k(SL₂(ℤ))` of level one modular forms is stable under this action on
`q`-expansions, in every weight: the normalised Eisenstein series and the discriminant have rational
`q`-expansions, and every form of even weight at least four is a multiple of the Eisenstein series
plus the discriminant times a form of weight lower by twelve.

The rationality of these `q`-expansions is short here, and it is on Tau Ceti's main as
`TauCeti.ModularForm.qExpansion_E_mem_range_map` and
`TauCeti.ModularForm.exists_discriminant_qExpansion_coeff_eq_intCast`, not at the pin: they can
replace the two lemmas on it after the bump.

## Main results

* `TauCeti.GaloisAction.exists_qExpansion_eq_map_levelOne`: for a level one modular form `f` of
  weight `k`, the series `σ(f) = ∑ σ(aₙ) qⁿ` is the `q`-expansion of a level one modular form of
  weight `k`.
-/

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries

open scoped MatrixGroups

namespace TauCeti.GaloisAction

variable (σ : ℂ →+* ℂ)

lemma map_qExpansion_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    map σ (qExpansion 1 (E hk)) = qExpansion 1 (E hk) := by
  ext m
  rw [coeff_map, E_qExpansion_coeff hk hk2]
  split_ifs <;> simp [map_ofNat]

lemma map_qExpansion_discriminant :
    map σ (qExpansion 1 discriminant) = qExpansion 1 discriminant := by
  have h₄ : map σ (qExpansion 1 E₄) = qExpansion 1 E₄ := map_qExpansion_E σ _ ⟨2, rfl⟩
  have h₆ : map σ (qExpansion 1 E₆) = qExpansion 1 E₆ := map_qExpansion_E σ _ ⟨3, rfl⟩
  ext m
  rw [ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq, coeff_map, coeff_smul,
    smul_eq_mul, map_mul, map_inv₀, map_ofNat, ← coeff_map, map_sub, map_pow, map_pow, h₄, h₆]

lemma map_smul_powerSeries (c : ℂ) (p : PowerSeries ℂ) : map σ (c • p) = σ c • map σ p := by
  ext m
  simp

lemma exists_qExpansion_eq_map_levelOne_weight_zero (f : ModularForm 𝒮ℒ 0) :
    ∃ g : ModularForm 𝒮ℒ 0, qExpansion 1 g = map σ (qExpansion 1 f) := by
  rcases ModularFormClass.levelOne_weight_zero_const f with ⟨c, hc⟩
  have hf : (f : ℍ → ℂ) = c • ⇑(1 : ModularForm 𝒮ℒ 0) := hc.trans <| funext fun τ ↦ by simp
  refine ⟨σ c • 1, ?_⟩
  rw [hf, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_smul_powerSeries,
    ModularForm.qExpansion_one, map_one]

lemma exists_qExpansion_eq_map_levelOne_aux (n : ℕ) : ∀ (k : ℤ), k < n →
    ∀ f : ModularForm 𝒮ℒ k, ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = map σ (qExpansion 1 f) := by
  have hzero {k : ℤ} (f : ModularForm 𝒮ℒ k) (hf : f = 0) :
      ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = map σ (qExpansion 1 f) :=
    ⟨0, by simp [hf, qExpansion_zero]⟩
  induction n with
  | zero =>
    intro k hk f
    exact hzero f <| DFunLike.coe_injective <|
      ModularFormClass.levelOne_neg_weight_eq_zero (by exact_mod_cast hk) f
  | succ n ih =>
    intro k hk f
    rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp (by exact_mod_cast hk) : k ≤ n) with hlt | rfl
    · exact ih k hlt f
    rcases Nat.even_or_odd n with hn | hn
    · by_cases h3 : 3 ≤ n
      · let c : ℂ := (qExpansion 1 f).coeff 0
        let f₁ : ModularForm 𝒮ℒ n := f - c • E h3
        have hsub : qExpansion 1 f₁ = qExpansion 1 f - c • qExpansion 1 (E h3) := by
          rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
            FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL]
        have hf₁ : (qExpansion 1 f₁).coeff 0 = 0 := by
          rw [hsub, map_sub, coeff_smul, E_qExpansion_coeff_zero h3 hn, smul_eq_mul, mul_one,
            sub_self]
        rcases ih ((n : ℤ) - 12) (by omega)
          (CuspForm.discriminantEquiv (toCuspForm f₁ hf₁)) with ⟨g₂, hg₂⟩
        refine ⟨σ c • E h3 + (CuspForm.ofMulDiscriminant g₂ : ModularForm 𝒮ℒ n), ?_⟩
        have hΔ : qExpansion 1 (CuspForm.ofMulDiscriminant g₂ : ModularForm 𝒮ℒ n) =
            qExpansion 1 discriminant * qExpansion 1 g₂ :=
          ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL CuspForm.discriminant g₂
        rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL,
          FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hΔ, hg₂,
          ← map_qExpansion_discriminant σ, ← map_mul,
          ← qExpansion_eq_qExpansion_discriminant_mul f₁ hf₁, hsub, map_sub, map_smul_powerSeries,
          map_qExpansion_E σ h3 hn, add_sub_cancel]
      · have hn' : n = 0 ∨ n = 2 := by
          rcases hn with ⟨m, rfl⟩
          omega
        rcases hn' with rfl | rfl
        · exact exists_qExpansion_eq_map_levelOne_weight_zero σ f
        · exact hzero f <| rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f
    · exact hzero f <| ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast hn) f

/-- **Level one modular forms are stable under field endomorphisms of `ℂ`**: for a modular form `f`
of level one and weight `k`, and a field endomorphism `σ` of `ℂ`, the series `∑ σ(aₙ) qⁿ` obtained
from the `q`-expansion `∑ aₙ qⁿ` of `f` is the `q`-expansion of a modular form of level one and
weight `k`. -/
lemma exists_qExpansion_eq_map_levelOne {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = map σ (qExpansion 1 f) :=
  exists_qExpansion_eq_map_levelOne_aux σ (k + 1).toNat k (by omega) f

end TauCeti.GaloisAction
