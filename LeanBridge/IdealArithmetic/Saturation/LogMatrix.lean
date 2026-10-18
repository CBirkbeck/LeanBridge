/-
Copyright (c) 2026 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.LinearAlgebra.Matrix.Rank

/- # Matrix of discrete logarithms and proofs of saturation

We define a matrix of discrete logarithms modulo a prime `p`, and prove how it
can be used to certify a system of independent units and the `p`-saturation of the class group of
an integrally closed domain with finite quotients.

## Main definition
- `LogFiniteRing`: the discrete logarithm function modulo `p` in a finite ring with cylic
  unit group.
- `MatrixLogProd`: the discrete logarithm mattrix modulo `p` for a collection of elements.

## Main results
- `units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion` : if `p` does not divide
  torsion order, this proves independence of units from a full-rank discrete log matrix.
- `units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion` : if `p` does not divide
  torsion order, certifies generators for the unit group modulo `p`-th powers.
- `units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion` : if `p` divides the
  torsion order, this proves independence of units from a full-rank discrete log matrix.
- `units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion` : if `p` divides the
  torsion order, certifies generators for the unit group modulo `p`-th powers.
- `not_principal_of_full_rank_matrix''`: proves `p`-saturation of a tuple in the class group
  from a full-rank discrete log matrix.   -/

open Polynomial Classical Module

section DiscreteLog

lemma unit_eq_primitive_root_pow {R : Type*} [CommRing R] [Fintype R]
    {ζ : R} (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (x : Rˣ) :
    ∃ (n : ℕ), ζ ^ n = x := by
  have hu : IsUnit ζ := IsPrimitiveRoot.isUnit hr (pos_iff_ne_zero.1 Fintype.card_pos)
  obtain ⟨ζ',hz ⟩ := hu
  haveI : Fintype (Subgroup.zpowers ζ') := by exact
    (Subgroup.zpowers ζ').instFintypeSubtypeMemOfDecidablePred
  have heq : Subgroup.zpowers ζ' = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [← Fintype.card_eq_nat_card (α := (Subgroup.zpowers ζ')), Fintype.card_zpowers,
    ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr, Fintype.card_eq_nat_card]
  have hmem : x ∈ Subgroup.zpowers ζ' := by
    rw [heq]
    exact trivial
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k ,hk⟩ := hmem
  use (k % (orderOf ζ')).natAbs
  have hpow : ζ' ^ (k % (orderOf ζ')) = x := by
    rw [Int.emod_def, zpow_sub, hk, zpow_mul, zpow_natCast, pow_orderOf_eq_one]
    simp only [one_zpow, inv_one, mul_one]
  have hnpow : (↑(Int.natAbs (k % (orderOf ζ'))) : ℤ) = k % (orderOf ζ')  := by
    simp only [Int.natCast_natAbs, abs_eq_self]
    refine Int.emod_nonneg k (Int.ofNat_ne_zero.mpr ?_)
    have hu : orderOf ζ' = orderOf ζ := by
      rw [← hz]
      exact Eq.symm orderOf_units
    rw [hu]
    rw [← IsPrimitiveRoot.eq_orderOf hr]
    exact Fintype.card_ne_zero
  rw [← hnpow] at hpow
  rw [← hpow, zpow_natCast]
  simp only [Units.val_pow_eq_pow_val, hz]

/-- The discrete logarithm map. Given a finite ring `R` and a
  generator `ζ` of its group of units, this maps an element `x : R` to `0` if it is not a unit,
  and to the coercion of `n` in `ZMod p` (where `n` is such that `ζ ^ n = x`) if it is.

  Note: We are using choice to pick `n`. This definition is independent of the choice if
  `p` divides the order of the unit group.  -/
noncomputable def LogFiniteRing {R : Type*} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (p : ℕ) : R → ZMod p := by
  intro x
  by_cases hc : IsUnit x
  · choose n _ using unit_eq_primitive_root_pow hr (hc.unit)
    exact (n : ZMod p)
  · exact 0

lemma LogFiniteRing_of_pow  {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (n : ℕ) :
    LogFiniteRing hr p (ζ ^ n) = (n : ZMod p) := by
  have hc : IsUnit (ζ ^ n) := by
    refine IsUnit.pow n ?_
    exact IsPrimitiveRoot.isUnit hr (pos_iff_ne_zero.1 Fintype.card_pos)
  obtain ⟨ζ', hz ⟩ := IsPrimitiveRoot.isUnit hr (pos_iff_ne_zero.1 Fintype.card_pos)
  unfold LogFiniteRing
  simp only [hc, ↓reduceDIte]
  have aux := choose_spec (unit_eq_primitive_root_pow hr hc.unit)
  simp_rw [IsUnit.unit_spec, ← hz, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Units.val_inj,
    ← orderOf_dvd_sub_iff_zpow_eq_zpow, ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr] at aux
  symm
  refine (ZMod.natCast_eq_natCast_iff _ _ p).2 ?_
  refine Nat.modEq_of_dvd ?_
  refine dvd_trans (Int.natCast_dvd_natCast.2 hdvd) ?_
  convert aux
  simp only [IsUnit.unit_spec]
  simp_rw [ ← hz, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Units.val_inj,
    ← orderOf_dvd_sub_iff_zpow_eq_zpow, ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr]

lemma LogFiniteRing_of_ne_unit_eq_zero {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ))
    {x : R} (hx : ¬ IsUnit x) : LogFiniteRing hr p x = 0 := by
  unfold LogFiniteRing
  simp only [hx, ↓reduceDIte]

/-- The discrete logarithm map turns multiplication into addition. -/
lemma LogFiniteRing_mul {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x y : R)
    (hx : IsUnit x) (hy : IsUnit y) :
    LogFiniteRing hr p (x * y) = LogFiniteRing hr p x + LogFiniteRing hr p y := by
  obtain ⟨n, hn⟩ :=  unit_eq_primitive_root_pow hr hx.unit
  obtain ⟨m, hm⟩ :=  unit_eq_primitive_root_pow hr hy.unit
  rw [IsUnit.unit_spec] at hn hm
  have hmn : ζ ^ (n + m) = x * y := by
    rw [← hn, ← hm, pow_add]
  rw [← hmn, ← hm, ← hn, LogFiniteRing_of_pow hr hdvd, LogFiniteRing_of_pow hr hdvd,
    LogFiniteRing_of_pow hr hdvd]
  simp only [Nat.cast_add]

lemma LogFiniteRing_one {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) :
    LogFiniteRing hr p 1  = 0 := by
  rw [← pow_zero ζ, LogFiniteRing_of_pow hr hdvd]
  simp only [Nat.cast_zero]

/-- The discrete logarithm map turns products into sums. -/
lemma LogFiniteRing_prod {R ι : Type*} {p : ℕ} [CommRing R] [Fintype R] (s : Finset ι) {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ))
    (x : ι → R) (hx : ∀ i ∈ s, IsUnit (x i)) :
    LogFiniteRing hr p (∏ i ∈ s, x i) = ∑ i ∈ s, LogFiniteRing hr p (x i) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.prod_empty, Finset.sum_empty]
    exact LogFiniteRing_one hr hdvd
  · rw [Finset.forall_mem_cons] at hx
    simp only [Finset.cons_eq_insert, ha, not_false_eq_true, Finset.prod_insert,
      Finset.sum_insert, ← ih hx.2]
    refine LogFiniteRing_mul hr hdvd _ _ ?_ ?_
    · exact hx.1
    · rw [IsUnit.prod_iff]
      exact hx.2

lemma LogFiniteRing_pow {R : Type*} {p n : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x : R) :
    LogFiniteRing hr p (x ^ n)  = n * LogFiniteRing hr p x := by
  by_cases hc : IsUnit x
  · obtain ⟨m, hm⟩ := unit_eq_primitive_root_pow hr hc.unit
    simp only [IsUnit.unit_spec] at hm
    rw [← hm, ← pow_mul, LogFiniteRing_of_pow hr hdvd _, LogFiniteRing_of_pow hr hdvd _]
    simp only [Nat.cast_mul, mul_comm]
  · by_cases hn : n = 0
    · rw [hn]
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      rw [LogFiniteRing_one hr hdvd ]
    · have hcc := hc
      rw [← isUnit_pow_iff hn] at hc
      rw [LogFiniteRing_of_ne_unit_eq_zero hr hc, LogFiniteRing_of_ne_unit_eq_zero hr hcc]
      simp only [mul_zero]

/-- The discrete logarithm map applied to a `p`-th power equals `0`. -/
lemma LogFiniteRing_p_power_eq_zero {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x : R) :
    LogFiniteRing hr p (x ^ p) = 0 := by
  rw [LogFiniteRing_pow hr hdvd]
  simp only [CharP.cast_eq_zero, zero_mul]

end DiscreteLog

section LogMatrix

lemma LogFiniteRing_hom_prod_eq_dot_product {S R ι : Type*} {p : ℕ} [CommRing R] [CommRing S]
    [Fintype R] [Fintype ι] {ζ : R} (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ))
    (hdvd : p ∣ (Fintype.card Rˣ)) (φ : S →+* R) (x : ι → S) (hu : ∀ i, IsUnit (φ (x i)))
    (e : ι → ℕ) : LogFiniteRing hr p (φ (∏ i, (x i) ^ (e i))) =
    (fun i => LogFiniteRing hr p (φ (x i))) ⬝ᵥ (fun i => (e i : ZMod p)) := by
  simp_rw [map_prod, map_pow]
  rw [LogFiniteRing_prod _ hr hdvd]
  simp_rw [LogFiniteRing_pow hr hdvd]
  congr ; ext i ; dsimp
  rw [mul_comm]
  · intro i _
    exact IsUnit.pow (e i) (hu i)

/-- Take `S` to be a ring, and suppose we have reduction maps `φᵢ : S → Fᵢ` with `Fᵢ` finite rings.
For a collection of elements `x₁, …, xₘ` in `S`, we define the discrete logarithm matrix by letting
the `ij`-th entry be the discrete logarithm of `φᵢ(xⱼ)` modulo `p`.  -/
noncomputable def MatrixLogProd {S ι τ : Type*} (p : ℕ) [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ)) : Matrix τ ι (ZMod p) :=
  fun i j => LogFiniteRing (hr i) p ((φ i) (x j))

lemma MatrixLogProd_def {S ι τ : Type*} (p : ℕ) [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ)) (i : τ) (j : ι) :
    (MatrixLogProd p F φ x ζ hr) i j = LogFiniteRing (hr i) p ((φ i) (x j)) := rfl

end LogMatrix

open Matrix

/-- For a collection of elements `x₁, …, xₘ` in `S`, if the  `MatrixLogProd` is of full rank,
  then if `∏ i, xᵢ ^ eᵢ` is a `p`-th power, this implies that `p` divides `eᵢ`. -/
lemma exponent_vec_eq_zero_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i))
    (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι)
    (hp : ∃ y, ∏ i, (x i) ^ (e i) = y ^ p) : ∀ i, p ∣ e i := by
  intro i
  rw [← ZMod.natCast_eq_zero_iff]
  let E : Matrix ι (Fin 1) (ZMod p) := fun i _ => (e i : ZMod p)
  obtain ⟨y, hy ⟩ := hp
  have hzM : (MatrixLogProd p F φ x ζ hr) * E = 0 := by
    ext i j
    fin_cases j
    rw [Matrix.mul_apply', Matrix.zero_apply]
    erw [← LogFiniteRing_hom_prod_eq_dot_product (hr i) (hdvd i) (φ i) _ (hu i), hy,
    map_pow, LogFiniteRing_p_power_eq_zero (hr i) (hdvd i) ]
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzM
  rw [hrank] at hle
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hle
  rw [← Matrix.rank_transpose] at hle
  have hEz : Eᵀ = 0 := by
    by_contra hc
    rw [LinearIndependent.rank_matrix ?_] at hle
    contradiction
    rw [linearIndependent_fin_succ]
    simp only [Nat.reduceAdd, Fin.tail_def, linearIndependent_empty_type, range_empty,
      Submodule.span_empty, Fin.isValue, Submodule.mem_bot, true_and]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    fin_cases j
    simp only [Fin.zero_eta, Fin.isValue, ne_eq] at hj
    exact hj
  exact congr_fun (congr_fun hEz 0) i

/-- For a collection of elements `x₁, …, xₘ` in an integrally closed `S`.
  If the  `MatrixLogProd` is of full rank, then if `(∏ i, xᵢ ^ eᵢ) * z ^ p` is a `p`-th power,
  this implies that `p` divides `eᵢ`. -/
lemma exponent_vec_eq_zero_of_full_rank_matrix' {S ι τ : Type*} {p : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [∀ i, CommRing (F i)]
    [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι)
    (z : S) (hznz : z ≠ 0)
    (hp : ∃ y , (∏ i, (x i) ^ (e i)) * z ^ p = y ^ p) : ∀ i, p ∣ e i := by
  obtain ⟨y, hyz⟩ := hp
  obtain ⟨k, hk⟩:=
    (IsIntegrallyClosed.pow_dvd_pow_iff (Nat.Prime.ne_zero hp.out)).1 (Dvd.intro_left _ hyz)
  rw [hk, mul_pow, mul_comm (z ^ p) _] at hyz
  simp [hznz] at hyz
  exact exponent_vec_eq_zero_of_full_rank_matrix F φ x e ζ hr hdvd hu hrank ⟨k, hyz⟩

/-- If `uᵢ` are units and `w = ∏ uᵢ ^ e'ᵢ` modulo `p`-th powers, with `e'ᵢ : ℤ`, then
  there are `eᵢ : ℕ` such that `w = ∏ uᵢ ^ eᵢ` modulo `p`-th powers. -/
lemma nat_up_to_power_of_int_up_to_power {S ι : Type*} [CommRing S]
    [Fintype ι] {u : ι → S} (hu : ∀ i, IsUnit (u i)) {w : Sˣ} {p : ℕ} (hp : p ≠ 0)
    (e' : ι → ℤ) (t : Sˣ) (het : w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) :
    ∃ (e : ι → ℕ), (∀ i, (e i : ZMod p) = e' i) ∧ (∃ (t : Sˣ) ,
      w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p) := by
  use (fun i => ((e' i) % p).toNat)
  have : ∀ i, (u i) ^ ((e' i) % p).toNat = ↑((hu i).unit ^ ((e' i) % p)) := by
    intro i
    nth_rw 2 [← Int.toNat_of_nonneg (Int.emod_nonneg (e' i) (Int.ofNat_ne_zero.mpr hp))]
    rw [zpow_natCast]
    rfl
  constructor
  · intro i
    dsimp
    have := Int.toNat_of_nonneg (Int.emod_nonneg (e' i) (Int.ofNat_ne_zero.mpr hp))
    apply_fun (algebraMap ℤ (ZMod p)) at this
    simp only [algebraMap_int_eq, eq_intCast, ZMod.intCast_mod] at this
    rw [← this]
    exact Eq.symm (AddCommGroupWithOne.intCast_ofNat (e' i % ↑p).toNat)
  use (∏ (i : ι), ((hu i).unit) ^ ((e' i) / p)) * t
  simp_rw [this]
  simp only [Units.val_mul, Units.coe_prod, mul_pow, ← Finset.prod_pow]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  have aux : ∀ i, (↑((hu i).unit ^ ((e' i) % p)) : S) * (↑((hu i).unit ^ ((e' i) / p)): S) ^ p =
    (↑((hu i).unit ^ (e' i)) : S) := by
    intro i
    nth_rw 3 [← Int.emod_add_mul_ediv (e' i) p]
    rw [zpow_add]
    rw [Units.val_mul, Units.mul_right_inj, mul_comm, zpow_mul, zpow_natCast]
    rfl
  simp_rw [aux, het]
  simp only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]

/-- Version of `exponent_vec_eq_zero_of_full_rank_matrix` for exponents over `ℤ`. -/
lemma z_exponent_vec_eq_zero_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [hpp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i))  (u : ι → S)
    (hu : ∀ i, IsUnit (u i)) (e : ι → ℤ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)
    (hp : ∃ y, ∏ i : ι, ↑(hu i).unit ^ (e i)= y ^ p) : ∀ i, ↑p ∣ e i := by
  obtain ⟨y, hy⟩ := hp
  have aux := nat_up_to_power_of_int_up_to_power hu (Nat.Prime.ne_zero hpp.out ) e (w := 1) (y⁻¹) ?_
  swap
  · rw [hy]
    simp only [inv_pow, mul_inv_cancel]
  obtain ⟨e', hmod, t, h2⟩ :=  aux
  symm at h2
  apply_fun (fun x => x * (↑t⁻¹) ^ p ) at h2
  rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_pow, mul_one] at h2
  have hdvde : ∀ (i : ι), p ∣ e' i := exponent_vec_eq_zero_of_full_rank_matrix F
    φ u e' ζ hr hdvd ?_ hrank ⟨↑t⁻¹, h2 ⟩
  intro k
  specialize hmod k
  specialize hdvde k
  rw [← ZMod.natCast_eq_zero_iff] at hdvde
  rw [hdvde, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
  exact hmod
  intro i j
  apply RingHom.isUnit_map
  exact hu j

lemma nat_up_to_p_power_iff_int_up_to_p_power {S ι : Type*} [CommRing S]
  [Fintype ι] (u : ι → S) (hu : ∀ i, IsUnit (u i)) (w : Sˣ) {p : ℕ} (hp : p ≠ 0) :
  (∃ (e : ι → ℕ), (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)) ↔
  (∃ (e' : ι → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p)) := by
  constructor
  · rintro ⟨e, t, het ⟩
    use (fun i => e i) , t
    rw [← Units.val_inj]
    simp only [het, zpow_natCast, Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec]
  · rintro ⟨e', t, het ⟩
    obtain ⟨e, hmod, tt, h2⟩ := nat_up_to_power_of_int_up_to_power hu hp e' t het
    use e, tt

/-- For a prime `p : R`, proving `R`-linear dependence of a collection `v`, is equivalent to
  proving that there exists a linear combination of the elements in `v` where at least one
  coefficient is not divisible by a prime `p`. -/
lemma linearIndependent_int_iff_no_common_divisor {M ι R: Type*} [AddCommGroup M]
  [CommRing R] [IsDomain R] [WfDvdMonoid R] [Module R M] [NoZeroSMulDivisors R M]
  {p : R} (hp : Prime p) (v : ι → M) : ¬ LinearIndependent R v ↔
    ∃ (s : Finset ι) (g : ι → R), (∃ i ∈ s, ¬ p ∣ (g i)) ∧ ∑ i ∈ s, g i • v i = 0  := by
  by_cases hnnempty : Nonempty ι
  rw [linearIndependent_iff']
  push Not
  constructor
  swap
  · rintro ⟨s , g , ⟨j , hpj1, hpj2⟩ ,hg⟩
    use s, g
    refine ⟨hg, ⟨j , ⟨hpj1, ?_ ⟩ ⟩ ⟩
    by_contra hz
    rw [hz] at hpj2
    simp only [dvd_zero, not_true_eq_false] at hpj2
  · rintro ⟨s , g ,hg ,bhneq⟩
    by_cases hc : ∃ i ∈ s, ¬ p ∣ (g i)
    · use s , g
    · push Not at hc
      let S := Finset.filter (fun x => g x ≠ 0) s
      haveI hS : S.Nonempty := by
        rw [Finset.filter_nonempty_iff]
        use bhneq.choose
        simp only [ne_eq]
        exact bhneq.choose_spec
      have hSaux : ∀ x, x ∈ S → x ∈ s := by
        intro x hx
        exact Finset.mem_of_mem_filter x hx
      · set m := S.inf' hS (fun i => multiplicity p (g i)) with hmm
        have hmp : m ≠ 0 := by
          suffices 1 ≤ m by exact Nat.ne_zero_of_lt this
          unfold m
          simp only [Finset.le_inf'_iff]
          intro j
          by_cases  hm : FiniteMultiplicity p (g j)
          · intro hj
            refine FiniteMultiplicity.le_multiplicity_of_pow_dvd hm ?_
            rw [pow_one]
            exact hc j (hSaux _ hj)
          · intro hj
            exact absurd (FiniteMultiplicity.of_prime_left hp (Finset.mem_filter.1 hj).2) hm
        have aux : ∀ i ∈ s , ∃ k, g i = p ^ m * k := by
          intro i hi
          by_cases hgi : g i ≠ 0
          have aux2 : m ≤ multiplicity p (g i) := by
            simp only [Finset.inf'_le_iff, m]
            use i
            exact ⟨Finset.mem_filter.mpr ⟨hi, hgi⟩  , by rfl⟩
          exact pow_dvd_of_le_multiplicity aux2
          push Not at hgi
          use 0
          rw [hgi, mul_zero]
        let g' : ι → R := fun i => if hi : i ∈ s then (aux i hi).choose else 0
        have hgaux :  ∀ i ∈ s, g i = p ^ m  * g' i := by
          intro i hi
          simp only [hi, ↓reduceDIte, g', m]
          exact (aux i hi).choose_spec
        obtain ⟨a, ha1, ha2⟩ := Finset.exists_mem_eq_inf' hS (fun i => multiplicity p (g i))
        rw [← hmm] at ha2
        have hndvd : ¬ p ∣ g' a := by
          by_contra hdvd
          obtain ⟨t, ht ⟩ := hdvd
          specialize hgaux a  (hSaux _ ha1)
          rw [ht, ← mul_assoc] at hgaux
          nth_rw 2 [← pow_one (a := p)] at hgaux
          rw [← pow_add] at hgaux
          have haux2 := (FiniteMultiplicity.pow_dvd_iff_le_multiplicity ?_).1 (Dvd.intro t (id (Eq.symm hgaux)))
          rw [← ha2] at haux2
          simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, m] at haux2
          refine FiniteMultiplicity.of_prime_left (α := R) hp ?_
          rw [Finset.mem_filter] at ha1
          exact ha1.2
        have hg' := Finset.sum_congr (s₂ := s) (f := fun x => g x • v x) (g := fun x =>
          (p ^ m  * g' x) • v x) rfl (fun x hx => by simp only [hgaux x hx] )
        simp_rw [hg', ← smul_smul, ← Finset.smul_sum] at hg
        simp only [smul_eq_zero, pow_eq_zero_iff', Prime.ne_zero hp, ne_eq, false_and, false_or,
          m] at hg
        use s , g'
        constructor
        · use a
          exact ⟨hSaux _ ha1, hndvd⟩
        · exact hg
  simp only [not_nonempty_iff] at hnnempty
  simp only [IsEmpty.exists_iff, false_and, exists_const, iff_false, Decidable.not_not]
  exact linearIndependent_empty_type

-- NOTE: We assume integrally closed

/-- Proves `p` saturation of a tuple of ideals from a full rank discrete logarithm matrix.
  Given a collection of ideals `Iᵢ` with `Iᵢ^ nᵢ = ⟨aᵢ⟩` and generators `uᵢ` of the unit group
  modulo `p`-th powers, together with reduction maps `φᵢ : S → Fᵢ`, form the discrete logarithm
  matrix using the elements `aᵢ` if `p ∣ nᵢ` and the elements `uᵢ`. If this matrix is of full
  rank, then the tuple `([I₁], …, [Iₘ])` is `p`-maximal.  -/
lemma not_principal_of_full_rank_matrix'' {S ι τ κ γ : Type*} {p : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] [Fintype κ] [Fintype γ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (I : κ → Ideal S) (a : κ → S) (n : κ → ℕ) (r : κ → ℕ)
    (ψ : γ → κ) (hψ : ∀ i, (p ∣ n i) → ∃ j , ψ j = i )
    (hua : ∀ i j, IsUnit ((φ i) (a (ψ j))))
    (hnzero : ∀ j , j ∈ (Finset.image ψ Finset.univ)ᶜ → a j ≠ 0 )
    (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i}) (b : S)
    (hrprod : ∏ i, (I i) ^ (r i) = Ideal.span {b}) (hdvdp : ∀ i , (n i) ∣ p * (r i))
    (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i)
      (fun i => a (ψ i))) ζ hr).rank = Fintype.card ι + Fintype.card γ) :
    ∀ i , n i ∣ r i := by
  intro i
  by_cases hdvdc : p ∣ n i
  · have hdvdcc := hψ i hdvdc
    apply_fun (fun x => x ^ p) at hrprod
    let q := fun i => (hdvdp i).choose
    have hq : ∀ (i : κ), p * r i = n i * q i := fun i => (hdvdp i).choose_spec
    simp_rw [← Finset.prod_pow, ← pow_mul, Ideal.span_singleton_pow, mul_comm, hq, pow_mul, h,
      Ideal.span_singleton_pow, Ideal.prod_span_singleton,
        Ideal.span_singleton_eq_span_singleton] at hrprod
    obtain ⟨v, hv⟩ := hrprod
    rw [← Finset.prod_mul_prod_compl {j ∈ Finset.univ | ∃ k , ψ k = j}] at hv
    have haux : ∀ i , i ∈ ({j ∈ Finset.univ | ∃ k , ψ k = j} : Finset κ)ᶜ → p ∣ q i := by
      intro i hi
      simp at hi
      refine (Nat.Coprime.dvd_mul_left ?_ ).1 (Dvd.intro _ (hq i))
      refine (Nat.Prime.coprime_iff_not_dvd (hp.out)).2 ?_
      revert hi
      contrapose!
      exact hψ i
    let χ := fun i => if hi : i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ
      then (haux i hi).choose else 0
    have : ∀ i, i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ → q i = p * (χ i) :=
      fun i hi => by
      unfold χ
      simp only [hi, ↓reduceDIte]
      exact (haux i hi).choose_spec
    have hauxprod : ∏ i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ, a i ^ q i =
      (∏ i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ, a i ^ (χ i)) ^ p := by
      simp_rw [← Finset.prod_pow, ← pow_mul, mul_comm]
      refine Finset.prod_congr rfl ?_
      intro x hx
      rw [this x hx]
    obtain ⟨e, t , het ⟩ := hugen v
    have hinj' : Function.Injective ψ := by
      unfold Function.Injective
      by_contra! hc
      obtain ⟨a,b, habeq, hneq⟩ := hc
      rw [Matrix.rank_eq_finrank_span_cols, Eq.comm] at hrank
      have := hrank ▸ (finrank_span_le_card _)
      simp at this
      have hunivcard : (Finset.univ (α := ι ⊕ γ)).card = Fintype.card ι + Fintype.card γ := by
        simp only [Finset.card_univ, Fintype.card_sum]
      rw [← hunivcard] at this
      have heqcard := le_antisymm this (Finset.card_image_le)
      rw [Eq.comm, Finset.card_image_iff] at heqcard
      have := heqcard (x₁ := Sum.inr a) (by simp only [Finset.coe_univ, Set.mem_univ])
        (x₂ := Sum.inr b) (by simp only [Finset.coe_univ,
        Set.mem_univ])
      rw [Sum.inr.injEq] at this
      refine hneq (this ?_ )
      ext i
      simp only [col_apply, MatrixLogProd, Sum.elim_inr, habeq]
    have hauxprod2 : (∏ i ∈ Finset.filter (fun j ↦ ∃ k, ψ k = j) Finset.univ, a i ^ q i) =
      ∏ i, a (ψ i) ^ q (ψ i) := by
      symm
      refine Finset.prod_nbij ψ ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · exact fun x1 a x2 a ↦ fun a ↦ hinj' a
      · intro x hx
        simp at hx
        obtain ⟨j, hj⟩ := hx
        exact ⟨j, by simp only [Finset.coe_univ, Set.mem_univ, true_and] ; exact hj⟩
      · simp
    let e' := Sum.elim e (fun i => q (ψ i))
    let x := (Sum.elim (fun i => u i) (fun i => a (ψ i)))
    have auxp : ∏ i, x i ^ (e' i) = (∏ i : ι, u i ^ e i) * (∏ i : γ, a (ψ i) ^ q (ψ i)) := by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, x, e']
    rw [hauxprod, hauxprod2, mul_assoc, mul_comm _ v.val, het, mul_assoc, ← mul_pow, ← mul_assoc,
      mul_comm _ (∏ i : ι, u i ^ e i), ← auxp] at hv
    have he : ∀ i , p ∣ e' i := by
      refine exponent_vec_eq_zero_of_full_rank_matrix' F φ x e' ζ hr hdvd ?_ ?_ _ ?_ ⟨b, hv⟩
      · intro i
        simp [x]
        constructor
        · intro j
          apply RingHom.isUnit_map
          exact hu j
        · intro j
          exact hua i j
      · simp only [Fintype.card_sum, x]
        exact hrank
      · simp only [Finset.univ_filter_exists, ne_eq, mul_eq_zero, Units.ne_zero, false_or]
        rw [← ne_eq, Finset.prod_ne_zero_iff]
        intro i hi
        exact pow_ne_zero _ (hnzero i hi)
    simp [e'] at he
    obtain ⟨m, hm⟩ := hdvdcc
    rcases he with ⟨h1, h2⟩
    obtain ⟨k, hk ⟩ := h2 m
    specialize hq (ψ m)
    rw [hk, ← mul_assoc, mul_comm _ p, mul_assoc] at hq
    simp only [mul_eq_mul_left_iff, Nat.Prime.ne_zero hp.out, or_false] at hq
    rw [← hm]
    exact ⟨k, hq⟩
  · rw [← Nat.Prime.coprime_iff_not_dvd (hp.out), Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] at hdvdc
    specialize hdvdp i
    rw [← Nat.dvd_gcd_mul_iff_dvd_mul, hdvdc, one_mul] at hdvdp
    exact hdvdp

/-- In the case that `p` does not divide the torsion order, if the discrete logarithm
  matrix formed from a collection of units `uᵢ` is of full rank, then these units are independent
  (linearly independent in the additive version of `Sˣ ⧸ (CommGroup.torsion Sˣ)` ). -/
lemma units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion {S ι τ : Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
  [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Sˣ))
  (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)  :
   LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk
    (s := (CommGroup.torsion Sˣ)) (hu i).unit)) := by
  by_contra hi
  · rw [linearIndependent_int_iff_no_common_divisor (Nat.prime_iff_prime_int.1 hp.out)] at hi
    obtain ⟨ s , g , ⟨k, hk,  hdvdp⟩ , hg⟩ := hi
    simp_rw [← ofMul_zpow, ← ofMul_prod, ofMul_eq_zero] at hg
    have : ∏ i ∈ s, ((QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit) ^ (g i)) =
      QuotientGroup.mk (∏ i ∈ s, (hu i).unit ^ (g i)) := by
      exact Eq.symm (QuotientGroup.mk_prod (CommGroup.torsion Sˣ) s)
    rw [this, QuotientGroup.eq_one_iff] at hg
    have auxcard : (Nat.card (CommGroup.torsion Sˣ)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpndvdt
      exact hp.out
    let y := (powCoprime auxcard)⁻¹ ⟨_ , hg⟩
    have aux2 : (powCoprime auxcard) y = ∏ i ∈ s, (hu i).unit ^ (g i) := by
      erw [Equiv.apply_symm_apply]
    rw [powCoprime_apply] at aux2
    simp only [SubmonoidClass.coe_pow] at aux2
    have haux2 := nat_up_to_power_of_int_up_to_power hu (w := 1) (p := p)
      (Ne.symm (NeZero.ne' p)) (fun i => if i ∈ s then g i else 0) (y⁻¹) ?_
    obtain ⟨e, hmod, t, h2⟩ :=  haux2
    symm at h2
    apply_fun (fun x => x * (↑t⁻¹) ^ p ) at h2
    rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_pow, mul_one] at h2
    have hdvde : ∀ (i : ι), p ∣ e i := exponent_vec_eq_zero_of_full_rank_matrix F
      φ u e ζ hr hdvd ?_ hrank ⟨↑t⁻¹, h2 ⟩
    specialize hmod k
    specialize hdvde k
    rw [← ZMod.natCast_eq_zero_iff] at hdvde
    rw [hdvde, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    simp only [hk, ↓reduceIte] at hmod
    exact hdvdp hmod
    · intro i j
      apply RingHom.isUnit_map
      exact hu j
    · simp only [pow_ite, zpow_zero, Finset.prod_ite_mem, Finset.univ_inter]
      rw [← aux2]
      simp only [inv_pow, mul_inv_cancel, y]

-- Note: some challenges are the switch between this as an additive subgroup vs multiplicative

/-- In the case that `p` does not divide the torsion order, if the discrete logarithm
  matrix formed from a collection of units `uᵢ` is of full rank, then these units generate `Sˣ`
  modulo `p`-th powers. -/
lemma units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion {S ι τ : Type*} {p : ℕ}
    [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] (F : τ → Type*) [CommRing S] [IsDomain S]
    [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
    [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Sˣ))
    (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)
    (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
    ∃ (e' : ι → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) := by
  have hlin := units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion
    F u hu φ ζ hr hdvd hpndvdt hrank
  let M : Submodule ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) :=
    Submodule.span ℤ (Set.range (fun i => Additive.ofMul (QuotientGroup.mk
      (s := (CommGroup.torsion Sˣ)) (hu i).unit)))
  let BM : Basis ι ℤ M := ⟨(LinearIndependent.linearCombinationEquiv hlin).symm⟩
  let N := ((Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))))
  have hdim : Module.finrank ℤ N = Fintype.card ι := by
    refine le_antisymm huc ?_
    refine le_of_eq_of_le ?_ (Submodule.finrank_le M)
    symm
    exact Module.finrank_eq_card_basis BM
  have B := Module.finBasisOfFinrankEq ℤ _ hdim
  have B' : Basis (Fin (Fintype.card ι)) ℤ M := Basis.reindex BM (Fintype.equivFin ι)
  have hinz : Nat.card (N ⧸ M) ≠ 0 := by
    rw [← indexPID_eq_index_int _ B B' , Int.natAbs_ne_zero,
    ← Associated.ne_zero_iff (Associated.comm.1 (prod_moduleSmithCoeffs_associated_index _ B B')),
      Finset.prod_ne_zero_iff]
    intro i hi
    exact moduleSmithCoeffs_ne_zero _ B B' i
  haveI : Finite (N ⧸ M) := (Nat.card_ne_zero.1 hinz).2
  have auxcard : (Nat.card (CommGroup.torsion Sˣ)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpndvdt
      exact hp.out
  have hpmaximal : ¬ p ∣ Nat.card (N ⧸ M) := by
    by_contra hpdvd
    obtain ⟨x  , hx ⟩ := exists_prime_addOrderOf_dvd_card' p hpdvd
    have xpow : p • x = 0  := by
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have xnezero : x ≠ 0 := by
      rw [addOrderOf_eq_iff] at hx
      rw [← one_nsmul x]
      exact (hx.2 1 (Nat.Prime.one_lt hp.out) (by decide))
      exact (Nat.Prime.pos hp.out)
    obtain ⟨y, hy ⟩ := Quotient.exists_rep x
    rw [← hy] at xpow xnezero
    simp only [ne_eq] at xnezero
    erw [Submodule.Quotient.mk_eq_zero] at xpow xnezero
    rw [Submodule.mem_span_range_iff_exists_fun] at xpow
    obtain ⟨g, hg⟩ := xpow
    dsimp at hg
    have hgc := hg
    conv at hg =>
      left  ; right ; intro i ; rw [← ofMul_zpow]
    rw [← ofMul_prod, ← ofMul_toMul y, ← ofMul_pow p _] at hg
    apply_fun Additive.ofMul.symm at hg
    erw [toMul_ofMul, toMul_ofMul] at hg
    obtain ⟨z, hz ⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Sˣ) (Additive.toMul y)
    rw [← hz] at hg
    erw [← QuotientGroup.mk_prod, ← QuotientGroup.mk'_apply, Eq.comm, QuotientGroup.mk'_eq_mk'
      (CommGroup.torsion Sˣ)] at hg
    obtain ⟨t, htmem, ht ⟩ := hg
    have : t = ((((powCoprime auxcard)⁻¹ ⟨_ , htmem⟩)) ^ p : CommGroup.torsion Sˣ) := by
      rw [← powCoprime_apply auxcard]
      erw [Equiv.apply_symm_apply]
    rw [this] at ht
    dsimp at ht
    rw [← mul_pow, Eq.comm] at ht
    have hdvdgi : ∀ i, ↑p ∣ (g i):=
      z_exponent_vec_eq_zero_of_full_rank_matrix F φ u hu g ζ hr hdvd hrank ⟨_, ht⟩
    set J : ι → ℤ := fun i => (hdvdgi i).choose
    have htaux : ∀ i , g i = p * (J i) := fun i => (hdvdgi i).choose_spec
    simp_rw [htaux, ← smul_smul, ← Finset.smul_sum, ← natCast_zsmul] at hgc
    rw [smul_right_inj (Ne.symm (NeZero.ne' (p : ℤ)))] at hgc
    apply xnezero
    rw [← hgc, Submodule.mem_span_range_iff_exists_fun]
    use J
  have auxcard' : (Nat.card (N ⧸ M)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpmaximal
      exact hp.out
  set α : N ⧸ M :=  (QuotientAddGroup.mk ((Additive.ofMul (QuotientGroup.mk
    (s := (CommGroup.torsion Sˣ)) w)) )) with hwdef
  have hauxg := nsmulCoprime_apply auxcard' ((nsmulCoprime auxcard')⁻¹ α)
  erw [Equiv.apply_symm_apply] at hauxg
  --obtain ⟨α', hα ⟩ := QuotientAddGroup.mk'_surjective _ α
  obtain ⟨β', hβ ⟩ := QuotientAddGroup.mk'_surjective _ ((nsmulCoprime auxcard')⁻¹ α)
  nth_rw 1 [hwdef] at hauxg
  erw [ ← hβ, QuotientAddGroup.mk'_apply,  ← QuotientAddGroup.mk_nsmul] at hauxg
  erw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, Eq.comm,
    QuotientAddGroup.mk'_eq_mk'] at hauxg
  obtain ⟨m, hmmem, hmeq ⟩ := hauxg
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hmmem
  obtain ⟨e' ,he ⟩ := hmmem
  use e'
  apply_fun Additive.toMul at hmeq
  rw [← he] at hmeq
  simp only [toMul_add, toMul_nsmul, toMul_sum, toMul_zsmul, toMul_ofMul] at hmeq
  obtain ⟨β'', hβ'' ⟩ := QuotientGroup.mk'_surjective _ (Additive.toMul β')
  erw [← hβ'', ← QuotientGroup.mk_prod, ← QuotientGroup.mk_pow ,
    QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hmeq
  obtain ⟨l, hlmem, hl⟩ := hmeq
  rw [mul_comm, ← mul_assoc] at hl
  have auxl : ((powCoprime auxcard)⁻¹ ⟨l ,hlmem⟩) ^ p  = l := by
    erw [← SubmonoidClass.coe_pow, ← powCoprime_apply auxcard, Equiv.apply_symm_apply]
  rw [← auxl, ← mul_pow, mul_comm, Eq.comm] at hl
  exact ⟨_ , hl⟩

/-- In the case that `p` divides the torsion order, if the discrete logarithm
  matrix formed from a collection of units `uᵢ` and a set of generators for the torsion subgroup
  of `Sˣ` is of full rank, then the units `uᵢ` are independent
  (linearly independent in the additive version of `Sˣ ⧸ (CommGroup.torsion Sˣ)` ). -/
lemma units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion {S ι τ κ: Type*} {p : ℕ}
    [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
    [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (v : κ → S) (hv : ∀ i, IsUnit (v i))
    (hvt : ∀ w ∈ CommGroup.torsion Sˣ,
      (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Sˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ) :
    LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk
      (s := (CommGroup.torsion Sˣ)) (hu i).unit)) := by
  by_contra hi
  · rw [linearIndependent_int_iff_no_common_divisor (Nat.prime_iff_prime_int.1 hp.out)] at hi
    obtain ⟨ s , g , ⟨k, hk,  hdvdp⟩ , hg⟩ := hi
    simp_rw [← ofMul_zpow, ← ofMul_prod, ofMul_eq_zero] at hg
    have : ∏ i ∈ s, ((QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit) ^ (g i)) =
      QuotientGroup.mk (∏ i ∈ s, (hu i).unit ^ (g i)) := by
      exact Eq.symm (QuotientGroup.mk_prod (CommGroup.torsion Sˣ) s)
    rw [this, QuotientGroup.eq_one_iff] at hg
    obtain ⟨a, t, ht, ha⟩ := hvt _ hg
    have haux2 := nat_up_to_power_of_int_up_to_power (u := Sum.elim u v) (by simp only
      [Sum.forall, Sum.elim_inl, hu, implies_true, Sum.elim_inr, hv, and_self])
      (w := 1) (p := p) (Ne.symm (NeZero.ne' p)) (Sum.elim (fun i => if i ∈ s then g i else 0)
        (fun j => - a j) ) (t⁻¹ : Sˣ) ?_
    swap
    · simp only [Fintype.prod_sum_type, Sum.elim_inl, pow_ite, zpow_zero, Finset.prod_ite_mem,
      Finset.univ_inter, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      simp only [ha, mul_inv_cancel_comm, inv_pow, mul_inv_cancel]
    obtain ⟨e', hep, t, hpeq⟩ := haux2
    apply_fun (fun x => x * (↑t⁻¹) ^ p ) at hpeq
    rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_pow, mul_one] at hpeq
    have hdvde : ∀ (i : _), p ∣ e' i := exponent_vec_eq_zero_of_full_rank_matrix F φ (Sum.elim u v)
      e' ζ hr hdvd ?_ (by simp only [hrank,
      Fintype.card_sum]) ⟨↑t⁻¹, hpeq.symm ⟩
    simp only [Sum.forall, Sum.elim_inl, Int.cast_ite, Int.cast_zero, Sum.elim_inr,
      Int.cast_neg] at hdvde hep
    rcases hdvde with ⟨hdvde1, hdvde2⟩
    rcases hep with ⟨hep1, hep2⟩
    specialize hdvde1 k
    specialize hep1 k
    rw [← ZMod.natCast_eq_zero_iff] at hdvde1
    simp only [hk, ↓reduceIte] at hep1
    rw [hdvde1, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hep1
    exact hdvdp hep1
    · intro i j
      apply RingHom.isUnit_map
      cases j
      · simp only [Sum.elim_inl, hu]
      · simp only [Sum.elim_inr, hv]

/-- In the case that `p` divides the torsion order, if the discrete logarithm
  matrix formed from a collection of units `uᵢ` and a set of generators for the torsion subgroup
  (modulo `p`-th powers) of `Sˣ`  is of full rank, then these units
  generate `Sˣ` modulo `p`-th powers. -/
lemma units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion {S ι τ κ: Type*} {p : ℕ}
    [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*)
    [CommRing S] [IsDomain S]
    [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
    [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (v : κ → S) (hv : ∀ i, IsUnit (v i))
    (hvt : ∀ w ∈ CommGroup.torsion Sˣ,
      (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Sˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
    (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ)
    (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
    ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit)
      (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
  have hlin := units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion
    F u hu v hv hvt φ ζ hr hdvd hrank
  let M : Submodule ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) :=
    Submodule.span ℤ (Set.range (fun i => Additive.ofMul (QuotientGroup.mk
      (s := (CommGroup.torsion Sˣ)) (hu i).unit)))
  let BM : Basis ι ℤ M := ⟨(LinearIndependent.linearCombinationEquiv hlin).symm⟩
  let N := ((Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))))
  have hdim : Module.finrank ℤ N = Fintype.card ι := by
    refine le_antisymm huc ?_
    refine le_of_eq_of_le ?_ (Submodule.finrank_le M)
    symm
    exact Module.finrank_eq_card_basis BM
  have B := Module.finBasisOfFinrankEq ℤ _ hdim
  have B' : Basis (Fin (Fintype.card ι)) ℤ M := Basis.reindex BM (Fintype.equivFin ι)
  have hinz : Nat.card (N ⧸ M) ≠ 0 := by
    rw [← indexPID_eq_index_int _ B B' , Int.natAbs_ne_zero,
    ← Associated.ne_zero_iff (Associated.comm.1 (prod_moduleSmithCoeffs_associated_index _ B B')),
      Finset.prod_ne_zero_iff]
    intro i hi
    exact moduleSmithCoeffs_ne_zero _ B B' i
  haveI : Finite (N ⧸ M) := (Nat.card_ne_zero.1 hinz).2
  have hpmaximal : ¬ p ∣ Nat.card (N ⧸ M) := by
    by_contra hpdvd
    obtain ⟨x  , hx ⟩ := exists_prime_addOrderOf_dvd_card' p hpdvd
    have xpow : p • x = 0  := by
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have xnezero : x ≠ 0 := by
      rw [addOrderOf_eq_iff] at hx
      rw [← one_nsmul x]
      exact (hx.2 1 (Nat.Prime.one_lt hp.out) (by decide))
      exact (Nat.Prime.pos hp.out)
    obtain ⟨y, hy ⟩ := Quotient.exists_rep x
    rw [← hy] at xpow xnezero
    simp only [ne_eq] at xnezero
    erw [Submodule.Quotient.mk_eq_zero] at xpow xnezero
    rw [Submodule.mem_span_range_iff_exists_fun] at xpow
    obtain ⟨g, hg⟩ := xpow
    dsimp at hg
    have hgc := hg
    conv at hg =>
      left  ; right ; intro i ; rw [← ofMul_zpow]
    rw [← ofMul_prod, ← ofMul_toMul y, ← ofMul_pow p _] at hg
    apply_fun Additive.ofMul.symm at hg
    erw [toMul_ofMul, toMul_ofMul] at hg
    obtain ⟨z, hz ⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Sˣ) (Additive.toMul y)
    rw [← hz] at hg
    erw [← QuotientGroup.mk_prod, ← QuotientGroup.mk'_apply, Eq.comm,
      QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hg
    obtain ⟨t, htmem, ht ⟩ := hg
    obtain ⟨a, k, hk, ha⟩ := hvt _ htmem
    dsimp at ht
    have hdvdgi := z_exponent_vec_eq_zero_of_full_rank_matrix F φ (Sum.elim u v)
      (by simp only [Sum.forall, Sum.elim_inl, hu, implies_true, Sum.elim_inr, hv, and_self] )
        (Sum.elim g (fun j => - a j) ) ζ hr hdvd (by simp only [hrank, Fintype.card_sum]) ?_
    swap
    use z * k
    · simp only [Fintype.prod_sum_type, Sum.elim_inl, ← ht, ha, Sum.elim_inr, zpow_neg,
      Finset.prod_inv_distrib]
      simp [mul_pow, mul_comm, mul_assoc]
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, dvd_neg] at hdvdgi
    set J : ι → ℤ := fun i => (hdvdgi.1 i).choose
    have htaux : ∀ i , g i = p * (J i) := fun i => (hdvdgi.1 i).choose_spec
    simp_rw [htaux, ← smul_smul, ← Finset.smul_sum, ← natCast_zsmul] at hgc
    rw [smul_right_inj (Ne.symm (NeZero.ne' (p : ℤ)))] at hgc
    apply xnezero
    rw [← hgc, Submodule.mem_span_range_iff_exists_fun]
    use J
  have auxcard' : (Nat.card (N ⧸ M)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpmaximal
      exact hp.out
  set α : N ⧸ M :=  (QuotientAddGroup.mk ((Additive.ofMul (QuotientGroup.mk
    (s := (CommGroup.torsion Sˣ)) w)) )) with hwdef
  have hauxg := nsmulCoprime_apply auxcard' ((nsmulCoprime auxcard')⁻¹ α)
  erw [Equiv.apply_symm_apply] at hauxg
  obtain ⟨β', hβ ⟩ := QuotientAddGroup.mk'_surjective _ ((nsmulCoprime auxcard')⁻¹ α)
  nth_rw 1 [hwdef] at hauxg
  erw [ ← hβ, QuotientAddGroup.mk'_apply,  ← QuotientAddGroup.mk_nsmul] at hauxg
  erw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, Eq.comm,
    QuotientAddGroup.mk'_eq_mk'] at hauxg
  obtain ⟨m, hmmem, hmeq ⟩ := hauxg
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hmmem
  obtain ⟨e' ,he ⟩ := hmmem
  apply_fun Additive.toMul at hmeq
  rw [← he] at hmeq
  simp only [toMul_add, toMul_nsmul, toMul_sum, toMul_zsmul, toMul_ofMul] at hmeq
  obtain ⟨β'', hβ'' ⟩ := QuotientGroup.mk'_surjective _ (Additive.toMul β')
  erw [← hβ'', ← QuotientGroup.mk_prod, ← QuotientGroup.mk_pow ,
    QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hmeq
  obtain ⟨l, hlmem, hl⟩ := hmeq
  rw [mul_comm, ← mul_assoc] at hl
  obtain ⟨a', k, hk, ha'⟩ := hvt _ hlmem
  use Sum.elim e' a'
  use k * β''
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_pow, mul_assoc _ _ (k ^ p * β'' ^ p), ← mul_assoc _ (k ^ p) ,
    ← ha', ← mul_assoc _ l, ← hl, mul_comm, mul_assoc]

/-- Version of `units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion` assuming full knowledge
of generators for the torsion subgroup. -/
lemma units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion' {S ι τ κ: Type*} {p : ℕ}
    [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*)
    [CommRing S] [IsDomain S]
    [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
    [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (v : κ → S) (hv : ∀ i, IsUnit (v i))
    (hvt : CommGroup.torsion Sˣ = Subgroup.closure (Set.range (fun j => (hv j).unit )) )
    (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ)
    (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
    ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit)
      (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
 refine units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion
  F u hu φ ζ hr hdvd v hv ?_ hrank huc w
 intro k hkmem
 rw [hvt, Subgroup.mem_closure_range_iff_of_fintype] at hkmem
 obtain ⟨a, ha⟩ := hkmem
 use a , 1
 simp [ha]

section NonPrincipality

/- The results in this section, with more relaxed assumptions on `S`
  (not necessarily integrally closed) can be used for certifying the nonprincipaly of
  a single ideal. This suffices to certify a cylic class group.
  However, in practice, we use the previous results that prove `p`-saturation directly
  for a tuple of ideals. -/

lemma not_p_power_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i))
    (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι) (he : ∃ i, ¬ p ∣ e i) :
    ¬ ∃ y , ∏ i, (x i) ^ (e i) = y ^ p := by
  obtain ⟨j ,hj⟩ := he
  by_contra hc
  exact hj (exponent_vec_eq_zero_of_full_rank_matrix F φ x e ζ hr hdvd hu hrank hc j)

lemma not_principal_of_full_rank_matrix {S ι τ : Type*} {p n : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (I : Ideal S) (a : S) (hua : ∀ i, IsUnit ((φ i) a)) (hdvdp : p ∣ n) (h : I ^ n = Ideal.span {a})
    (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a)) ζ hr).rank
      = Fintype.card ι + 1) :
      ¬ ∃ b, I = Ideal.span {b} := by
  by_contra hb
  obtain ⟨c, hc⟩ := hb
  obtain ⟨m, hm⟩ := hdvdp
  set b := c ^ m with hb
  rw [hm, mul_comm, pow_mul, hc, Ideal.span_singleton_pow, ← hb,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  symm at h
  obtain ⟨w, hw⟩ := h
  obtain ⟨e, t, het⟩ := hugen w
  rw [mul_comm, het, mul_assoc, mul_comm _ a, ← mul_assoc,
    ← Units.mul_left_inj ((t⁻¹) ^ p), mul_assoc] at hw
  nth_rw 1 [inv_pow] at hw
  rw [(show ((t : S) ^ p  = ((t ^ p : Sˣ) : S)) by rfl), Units.mul_inv, mul_one] at hw
  erw [← mul_pow] at hw
  let e' := Sum.elim e (fun (_ : Fin 1) => 1)
  let x := (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a))
  have auxp : ∏ i, x i ^ (e' i) = (∏ i : ι, u i ^ e i) * a := by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Sum.elim_inr, pow_one, Finset.prod_const, Finset.card_singleton, x, e']
  rw [← auxp] at hw
  refine not_p_power_of_full_rank_matrix F φ x e' ζ hr hdvd ?_ ?_ ?_ ?_
  · intro i j
    cases j
    · apply RingHom.isUnit_map
      simp only [Sum.elim_inl, x]
      exact hu _
    · exact hua i
  · simp only [Fintype.card_sum, Fintype.card_unique]
    exact hrank
  · use Sum.inr 0
    simp only [Fin.isValue, Sum.elim_inr, Nat.dvd_one, e']
    refine Nat.Prime.ne_one hp.out
  · exact ⟨b * t⁻¹, hw⟩

lemma not_principal_of_full_rank_matrix' {S ι τ : Type*} {p n : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i)
    (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (I : Ideal S) (a : S) (hua : ∀ i, IsUnit ((φ i) a)) (hdvdp : p ∣ n) (h : I ^ n = Ideal.span {a})
    (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a)) ζ hr).rank =
      Fintype.card ι + 1) :
    ¬ ∃ b, I ^ (n / p) = Ideal.span {b} := by
  refine not_principal_of_full_rank_matrix (n := p)
    F u hu hugen φ ζ hr hdvd (I ^ (n / p)) a hua ?_ ?_ hrank
  · rfl
  · rw [← pow_mul, Nat.div_mul_cancel hdvdp]
    exact h

end NonPrincipality
