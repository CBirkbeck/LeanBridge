import Mathlib
import LeanBridge.ForMathlib.tactics.LMFDB_search
import LeanBridge.ForMathlib.Irreduciblepolys.LMFDB_Proof_2_2_5_1

noncomputable section

open NumberField


abbrev min_poly_2_2_5_1_int : Polynomial ℤ := (1) * Polynomial.X ^ 2 + (-1) * Polynomial.X + (-1)

abbrev min_poly_2_2_5_1 : Polynomial ℚ := ((min_poly_2_2_5_1_int).mapRingHom (Int.castRingHom ℚ))


abbrev K_2_2_5_1 := AdjoinRoot min_poly_2_2_5_1

abbrev K := K_2_2_5_1

lemma irreducible_poly :  Irreducible min_poly_2_2_5_1 := by
  have := irreducible_T
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast] at this
  · convert this
    simp
    ring
  · refine Polynomial.Monic.isPrimitive ?_
    refine Polynomial.Monic.def.mpr ?_
    rw [T_ofList', ofList_leadingCoeff]
    · simp
    · apply List.cons_ne_nil _ _
    · rfl

instance: Fact (Irreducible min_poly_2_2_5_1) := ⟨irreducible_poly⟩

axiom LMFDB_NF_2_2_5_1_discr : NumberField.discr K_2_2_5_1 = 5

axiom LMFDB_NF_2_2_5_1_isGalois : IsGalois ℚ K_2_2_5_1

axiom LMFDB_NF_2_2_5_1_classNumber : NumberField.classNumber K_2_2_5_1 = 1


abbrev K_gen : K_2_2_5_1 := AdjoinRoot.root min_poly_2_2_5_1

lemma K_int : IsIntegral ℤ K_gen := by
  use min_poly_2_2_5_1_int
  constructor
  · simp [min_poly_2_2_5_1_int]
    ring
    monicity!
    rw [@Polynomial.coeff_one]
    grind
  · simpa [K_gen, min_poly_2_2_5_1] using AdjoinRoot.eval₂_root min_poly_2_2_5_1


def K_gen_int : 𝓞 K_2_2_5_1 := ⟨K_gen, K_int⟩

lemma K_gen_int_pol : K_gen_int ^ 2 - K_gen_int - 1 = 0 := by
  simp [K_gen_int, min_poly_2_2_5_1]
  suffices  K_gen ^ 2  - K_gen - 1 = 0 by
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  simpa [K_gen, min_poly_2_2_5_1] using AdjoinRoot.eval₂_root min_poly_2_2_5_1

def fundamental_unit_one : (𝓞 K_2_2_5_1)ˣ  where
  val := K_gen_int
  inv := K_gen_int - 1
  val_inv := by
    have := K_gen_int_pol
    grind
  inv_val := by
    have := K_gen_int_pol
    grind

@[simp]
lemma fundamental_unit_one_val : (fundamental_unit_one : 𝓞 K) = K_gen_int := rfl

def sqrt5 : ℝ := (1 + Real.sqrt 5) / 2

def emb1 : K →ₐ[ℚ] ℝ := by
  apply AdjoinRoot.liftHom min_poly_2_2_5_1 sqrt5
  simp [min_poly_2_2_5_1, sqrt5]

def embcompl : K →ₐ[ℚ] ℂ := (Algebra.algHom ℚ ℝ ℂ).comp emb1

def sqrt5' : ℝ := (1 - Real.sqrt 5) / 2

def emb2 : K →ₐ[ℚ] ℝ := by
  apply AdjoinRoot.liftHom min_poly_2_2_5_1 sqrt5
  simp [min_poly_2_2_5_1, sqrt5]

def embcompl2 : K →ₐ[ℚ] ℂ := (Algebra.algHom ℚ ℝ ℂ).comp emb2

lemma embcompl_isReal : ComplexEmbedding.IsReal embcompl.toRingHom := by
  rw [embcompl]
  rw [@ComplexEmbedding.isReal_iff]
  ext x
  simp [Algebra.algHom]

lemma embcompl_isReal2 : ComplexEmbedding.IsReal embcompl2.toRingHom := by
  rw [embcompl2]
  rw [@ComplexEmbedding.isReal_iff]
  ext x
  simp [Algebra.algHom]

def Inf1 : {w : InfinitePlace K // w.IsReal} := InfinitePlace.mkReal ⟨embcompl.toRingHom, embcompl_isReal⟩

def Inf2 : {w : InfinitePlace K // w.IsReal} := InfinitePlace.mkReal ⟨embcompl2.toRingHom, embcompl_isReal2⟩

open NumberField.Units

def fundsys : Fin (rank K) → (𝓞 K)ˣ :=
  λ i => fundamental_unit_one

lemma fundsyseq : fundSystem K = fundsys := by

  sorry

def e : { w // w ≠ ↑Inf2 } ≃ Fin (1) where
  toFun w := 1
  invFun := fun 1 => ⟨Inf1, sorry⟩
  left_inv := by sorry
  right_inv := by sorry

def ee : { w // w ≠ ↑Inf2 } ≃ Fin (rank K) := by
  have : rank K = 1 := by sorry
  rw [this]
  exact e

def unique_place : Unique { w // w ≠ ↑Inf2 } where
  default := ⟨Inf1, sorry⟩
  uniq := sorry

lemma rEGGulator_approx_eq : NumberField.Units.regulator K ∈ Set.Ico 0.48 0.49 := by
  rw [regulator_eq_det K Inf2]
  rw [fundsyseq]
  have : rank K = 1 := by sorry
  simp [fundsys, unique_place]

  have : NumberField.Units.dirichletUnitTheorem.logEmbedding_component  fundamental_unit_one



  sorry

end
