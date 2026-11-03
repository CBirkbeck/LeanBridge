import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Functions that are modular forms, and their `q`-expansions

This file sets up the bookkeeping used to manipulate polynomial expressions in modular forms of
different weights, on the level of functions on the upper half-plane, without casts between the
types of modular forms of equal weights: the predicates `TauCeti.GaloisAction.IsForm` and
`TauCeti.GaloisAction.IsCuspForm`, their closure properties, and the multiplicativity of
`q`-expansions on functions whose cusp function is analytic at `0`.

## Main definitions

* `TauCeti.GaloisAction.IsForm`: a function on the upper half-plane is a modular form of a given
  level and weight.
* `TauCeti.GaloisAction.IsCuspForm`: a function on the upper half-plane is a cusp form of a given
  level and weight.
* `TauCeti.GaloisAction.HasQExpansion`: the cusp function at period one of a function on the upper
  half-plane is analytic at `0`.
* `TauCeti.GaloisAction.cosetOf`: the coset indexing the translate of a modular form by an element
  of `SL₂(ℤ)` in the norm and the trace down to level one.
-/

open UpperHalfPlane ModularForm SlashInvariantForm Matrix

open scoped MatrixGroups

namespace TauCeti.GaloisAction

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {w w' : ℤ} {a b : ℍ → ℂ} {ι : Type*} {s : Finset ι}
  {c : ι → ℍ → ℂ}

/-- The cusp function at period one of a function on the upper half-plane is analytic at `0`: the
functions for which the `q`-expansion is multiplicative. -/
abbrev HasQExpansion (a : ℍ → ℂ) : Prop :=
  AnalyticAt ℂ (cuspFunction 1 a) 0

lemma HasQExpansion.mul (ha : HasQExpansion a) (hb : HasQExpansion b) : HasQExpansion (a * b) := by
  rw [HasQExpansion, cuspFunction_mul ha.continuousAt hb.continuousAt]
  exact AnalyticAt.mul ha hb

lemma HasQExpansion.add (ha : HasQExpansion a) (hb : HasQExpansion b) : HasQExpansion (a + b) := by
  rw [HasQExpansion, cuspFunction_add ha.continuousAt hb.continuousAt]
  exact AnalyticAt.add ha hb

lemma HasQExpansion.smul (ha : HasQExpansion a) (c : ℂ) : HasQExpansion (c • a) := by
  rw [HasQExpansion, cuspFunction_smul ha.continuousAt]
  exact AnalyticAt.const_smul ha

/-- A function on the upper half-plane **is a modular form** of level `𝒢` and weight `w`. -/
def IsForm (𝒢 : Subgroup (GL (Fin 2) ℝ)) (w : ℤ) (a : ℍ → ℂ) : Prop :=
  ∃ g : ModularForm 𝒢 w, ⇑g = a

/-- A function on the upper half-plane **is a cusp form** of level `𝒢` and weight `w`. -/
def IsCuspForm (𝒢 : Subgroup (GL (Fin 2) ℝ)) (w : ℤ) (a : ℍ → ℂ) : Prop :=
  ∃ g : CuspForm 𝒢 w, ⇑g = a

lemma isForm_coe (g : ModularForm 𝒢 w) : IsForm 𝒢 w g :=
  ⟨g, rfl⟩

lemma isCuspForm_coe (g : CuspForm 𝒢 w) : IsCuspForm 𝒢 w g :=
  ⟨g, rfl⟩

lemma IsForm.cast (h : w = w') (ha : IsForm 𝒢 w a) : IsForm 𝒢 w' a :=
  h ▸ ha

lemma IsCuspForm.cast (h : w = w') (ha : IsCuspForm 𝒢 w a) : IsCuspForm 𝒢 w' a :=
  h ▸ ha

lemma IsCuspForm.isForm (ha : IsCuspForm 𝒢 w a) : IsForm 𝒢 w a :=
  ha.elim fun g hg ↦ ⟨g, hg⟩

lemma IsForm.restrict (h : 𝒢 ≤ ℋ) (ha : IsForm ℋ w a) : IsForm 𝒢 w a :=
  ha.elim fun g hg ↦ ⟨g.restrict h, hg⟩

lemma IsForm.add (ha : IsForm 𝒢 w a) (hb : IsForm 𝒢 w b) : IsForm 𝒢 w (a + b) := by
  rcases ha with ⟨g, rfl⟩
  rcases hb with ⟨g', rfl⟩
  exact ⟨g + g', rfl⟩

lemma IsCuspForm.add (ha : IsCuspForm 𝒢 w a) (hb : IsCuspForm 𝒢 w b) : IsCuspForm 𝒢 w (a + b) := by
  rcases ha with ⟨g, rfl⟩
  rcases hb with ⟨g', rfl⟩
  exact ⟨g + g', rfl⟩

lemma isForm_zero : IsForm 𝒢 w 0 :=
  ⟨0, rfl⟩

lemma isCuspForm_zero : IsCuspForm 𝒢 w 0 :=
  ⟨0, rfl⟩

lemma IsForm.sum (hc : ∀ i ∈ s, IsForm 𝒢 w (c i)) : IsForm 𝒢 w (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isForm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hc i <| s.mem_insert_self i).add <| ih fun j hj ↦ hc j <| Finset.mem_insert_of_mem hj

lemma IsCuspForm.sum (hc : ∀ i ∈ s, IsCuspForm 𝒢 w (c i)) : IsCuspForm 𝒢 w (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCuspForm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hc i <| s.mem_insert_self i).add <| ih fun j hj ↦ hc j <| Finset.mem_insert_of_mem hj

/-- The coset of `δ⁻¹` in `SL₂(ℤ) ⧸ 𝒢`, the index of the translate `f ∣ δ` in the norm and the trace
down to level one. -/
noncomputable def cosetOf (𝒢 : Subgroup (GL (Fin 2) ℝ)) (δ : SL(2, ℤ)) : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ :=
  ⟦⟨SpecialLinearGroup.mapGL ℝ δ⁻¹, δ⁻¹, rfl⟩⟧

lemma quotientFunc_cosetOf {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒢 w] (g : F)
    (δ : SL(2, ℤ)) : quotientFunc g (cosetOf 𝒢 δ) = ⇑g ∣[w] δ := by
  rw [cosetOf, quotientFunc_mk, ← map_inv, inv_inv]
  rfl

lemma exists_cosetOf_eq (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) : ∃ δ : SL(2, ℤ), cosetOf 𝒢 δ = q := by
  induction q using Quotient.inductionOn with
  | h r =>
    rcases r with ⟨_, γ, rfl⟩
    exact ⟨γ⁻¹, by simp [cosetOf]⟩

lemma pow_slash (δ : SL(2, ℤ)) (n : ℕ) : (a ^ n) ∣[(n : ℤ) * w] δ = (a ∣[w] δ) ^ n := by
  induction n with
  | zero => simpa using is_invariant_one δ
  | succ n ih =>
    rw [pow_succ, pow_succ, Nat.cast_succ, add_mul, one_mul, mul_slash_SL2, ih]

lemma IsForm.hasQExpansion (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (ha : IsForm 𝒢 w a) :
    HasQExpansion a := by
  rcases ha with ⟨g, rfl⟩
  exact ModularFormClass.analyticAt_cuspFunction_zero g one_pos h1

variable [𝒢.HasDetOne]

lemma IsForm.smul (ha : IsForm 𝒢 w a) (c : ℂ) : IsForm 𝒢 w (c • a) := by
  rcases ha with ⟨g, rfl⟩
  exact ⟨c • g, rfl⟩

lemma IsCuspForm.smul (ha : IsCuspForm 𝒢 w a) (c : ℂ) : IsCuspForm 𝒢 w (c • a) := by
  rcases ha with ⟨g, rfl⟩
  exact ⟨c • g, rfl⟩

lemma IsForm.mul (ha : IsForm 𝒢 w a) (hb : IsForm 𝒢 w' b) : IsForm 𝒢 (w + w') (a * b) := by
  rcases ha with ⟨g, rfl⟩
  rcases hb with ⟨g', rfl⟩
  exact ⟨g.mul g', rfl⟩

lemma IsCuspForm.mul_isForm (ha : IsCuspForm 𝒢 w a) (hb : IsForm 𝒢 w' b) :
    IsCuspForm 𝒢 (w + w') (a * b) := by
  rcases ha with ⟨g, rfl⟩
  rcases hb with ⟨g', rfl⟩
  exact ⟨g.mulModularForm g', rfl⟩

lemma isForm_one : IsForm 𝒢 0 1 :=
  ⟨1, rfl⟩

lemma IsForm.pow (ha : IsForm 𝒢 w a) (n : ℕ) : IsForm 𝒢 (n * w) (a ^ n) := by
  rcases ha with ⟨g, rfl⟩
  exact ⟨g.pow n, g.coe_pow n⟩

lemma IsCuspForm.pow (ha : IsCuspForm 𝒢 w a) {n : ℕ} (hn : n ≠ 0) :
    IsCuspForm 𝒢 (n * w) (a ^ n) := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  rw [pow_succ', Nat.succ_eq_add_one, Nat.cast_add_one, add_comm, add_mul, one_mul]
  exact ha.mul_isForm (ha.isForm.pow m)

lemma IsForm.det {n : ℕ} {M : ℍ → Matrix (Fin n) (Fin n) ℂ} {r t : Fin n → ℤ}
    (hM : ∀ i j, IsForm 𝒢 (r i + t j) (fun τ ↦ M τ i j)) :
    IsForm 𝒢 (∑ i, r i + ∑ j, t j) (fun τ ↦ (M τ).det) := by
  have h : (fun τ ↦ (M τ).det) = ∑ π : Equiv.Perm (Fin n), ((π.sign : ℤ) : ℂ) •
      ∏ i, fun τ ↦ M τ (π i) i := by
    ext τ
    simp [Matrix.det_apply']
  rw [h]
  refine IsForm.sum fun π _ ↦ IsForm.smul ?_ _
  choose F hF using fun i ↦ hM (π i) i
  refine ⟨ModularForm.prod (s := Finset.univ) _ ?_ F, ?_⟩
  · rw [Finset.sum_add_distrib, Equiv.sum_comp π r]
  · ext τ
    simp [hF]

lemma quotientFunc_mul (g : ModularForm 𝒢 w) (g' : ModularForm 𝒢 w') (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    quotientFunc (g.mul g') q = quotientFunc g q * quotientFunc g' q := by
  rcases exists_cosetOf_eq q with ⟨δ, rfl⟩
  rw [quotientFunc_cosetOf, quotientFunc_cosetOf, quotientFunc_cosetOf, ModularForm.coe_mul,
    mul_slash_SL2]

lemma quotientFunc_pow (g : ModularForm 𝒢 w) (n : ℕ) (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    quotientFunc (g.pow n) q = quotientFunc g q ^ n := by
  rcases exists_cosetOf_eq q with ⟨δ, rfl⟩
  rw [quotientFunc_cosetOf, quotientFunc_cosetOf, coe_pow, pow_slash]

lemma hasQExpansion_one : HasQExpansion (1 : ℍ → ℂ) :=
  (isForm_one (𝒢 := 𝒮ℒ)).hasQExpansion one_mem_strictPeriods_SL

lemma hasQExpansion_zero : HasQExpansion (0 : ℍ → ℂ) :=
  (isForm_zero (𝒢 := 𝒮ℒ) (w := 0)).hasQExpansion one_mem_strictPeriods_SL

lemma HasQExpansion.pow (ha : HasQExpansion a) (n : ℕ) : HasQExpansion (a ^ n) := by
  induction n with
  | zero => simpa using hasQExpansion_one
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul ha

lemma HasQExpansion.qExpansion_pow (ha : HasQExpansion a) (n : ℕ) :
    qExpansion 1 (a ^ n) = qExpansion 1 a ^ n := by
  induction n with
  | zero => simp [qExpansion_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, qExpansion_mul (ha.pow n) ha, ih]

lemma hasQExpansion_sum (hc : ∀ i ∈ s, HasQExpansion (c i)) : HasQExpansion (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasQExpansion_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hc i <| s.mem_insert_self i).add <| ih fun j hj ↦ hc j <| Finset.mem_insert_of_mem hj

lemma qExpansion_sum_of_hasQExpansion (hc : ∀ i ∈ s, HasQExpansion (c i)) :
    qExpansion 1 (∑ i ∈ s, c i) = ∑ i ∈ s, qExpansion 1 (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, HasQExpansion (c j) := fun j hj ↦ hc j <| Finset.mem_insert_of_mem hj
    rw [Finset.sum_insert hi, Finset.sum_insert hi, qExpansion_add (hc i <| s.mem_insert_self i)
      (hasQExpansion_sum hs), ih hs]

end TauCeti.GaloisAction
