import LeanBridge.Mathlib.Units.QuadraticField
import LeanBridge.Compute.LogPhi

open NumberField InfinitePlace Units Polynomial QuadraticField

universe u

macro "polynomial_simp" : tactic =>
  `(tactic| simp only [map_C, map_X, Polynomial.map_zero, Polynomial.map_one, Polynomial.map_neg,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    eval_C, eval_X, eval_zero, eval_one, eval_neg, eval_add, eval_sub, eval_mul, eval_pow,
    eval₂_C, eval₂_X, eval₂_zero, eval₂_one, eval₂_neg, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

noncomputable section

namespace K_2_2_5_1

abbrev minPolyℤ : Polynomial ℤ :=
  X ^ 2 - X - 1

abbrev minPoly : Polynomial ℚ :=
  minPolyℤ.map <| algebraMap ℤ ℚ

abbrev K : Type :=
  AdjoinRoot minPoly

abbrev root :=
  AdjoinRoot.root minPoly

instance irreducible_minPoly : Fact <| Irreducible minPoly :=
  ⟨sorry⟩ -- tactic_dev

instance irreducible_minPolyℤ : Fact <| Irreducible minPolyℤ :=
  ⟨(monic_minPolyℤ 1).irreducible_of_irreducible_map _ _ irreducible_minPoly.out⟩

abbrev unit₁ : 𝓞 K :=
  ⟨root, minPolyℤ, monic_minPolyℤ _,
    by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly⟩

lemma unit₁_poly : unit₁ ^ 2 - unit₁ - 1 = 0 :=
  RingOfIntegers.coe_injective <| by simpa [minPoly, minPolyℤ] using AdjoinRoot.eval₂_root minPoly

def fundUnit₁ : (𝓞 K)ˣ :=
  ⟨unit₁, unit₁ - 1, by linear_combination unit₁_poly, by linear_combination unit₁_poly⟩

lemma fundSystem_eq : Units.fundSystem K = (fun _ ↦ fundUnit₁) := by
  sorry

theorem rank : rank K = 1 :=
  have : Fact <| Irreducible <| QuadraticField.minPoly 1 := irreducible_minPoly
  QuadraticField.rank _

lemma regulator_mem : regulator K ∈ Set.Icc
    0.48121182505960344749775891342436
    0.48121182505960344749775891342437 := by
  have : Fact <| Irreducible <| QuadraticField.minPoly 1 := irreducible_minPoly
  simp_rw [regulator_eq_det K _ <| (place₀_equiv _).trans <| finCongr rank.symm, place₀_mult _,
    Nat.cast_one, one_mul, place₀_default, place₁, realPlace₁, mkReal_coe, apply, fundSystem_eq]
  erw [realEmbedding₁_root]
  rw [@Matrix.det_unique _ _ _ <| place₀_unique _, Matrix.of_apply, Complex.norm_real,
    Real.norm_eq_abs, Real.log_abs, show root₁ 1 = (1 + √5) / 2 by norm_num [root₁],
    abs_of_nonneg <| Real.log_nonneg <| by linarith only [Set.mem_Icc.mp bound_sqrt_5]]
  exact bound_log_φ

axiom discr : discr K = 5

axiom isGalois : IsGalois ℚ K

axiom classNumber : classNumber K = 1

end K_2_2_5_1

end
