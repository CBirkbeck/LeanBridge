import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeElementaryDivisors
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeWeylInvariance
import Mathlib.Data.Int.NatAbs

/-!
# The triangularity of the Satake map of `Sp(2g, ℤ)`

Let `T(δ; a) = Γ diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ-a_0}, …, p^{δ-a_{g-1}}) Γ` be a double coset of
`Γ = Sp(2g, ℤ)` with dominant exponents, `a_0 ≤ ⋯ ≤ a_{g-1}` and `2 a_j ≤ δ`
(`SiegelUpperHalfSpace.elementaryCoset`). Every `k × k` minor of the diagonal is a product of `k`
of its entries, so it is divisible by `p^{a_0 + ⋯ + a_{k-1}}` for `k ≤ g`, the exponents
`a_0 ≤ ⋯ ≤ a_{g-1} ≤ δ - a_{g-1} ≤ ⋯ ≤ δ - a_0` being increasing in this order. The `k × k` minors
of a product are combinations of the `k × k` minors of each factor (the expansion behind the
Cauchy–Binet formula), so the same divisibility holds for every integral matrix of `T(δ; a)`.

The representative `b = (A, B; 0, D)` of a right coset `Γx ⊆ T(δ; a)` in the Borel subgroup is
integral, with `A` upper triangular: its leading `k × k` minor is `A_00 ⋯ A_{k-1,k-1}`, so
`v_p(A_00) + ⋯ + v_p(A_{k-1,k-1}) ≥ a_0 + ⋯ + a_{k-1}`. In terms of the weights `(δ; d)`,
`d_j = δ - v_p(A_jj)`, of the universal Satake map: every weight in the support of `Ω(T(δ; a))`
has first coordinate `δ` and `∑_{j<k} (δ - d_j) ≥ a_0 + ⋯ + a_{k-1}`
(`SiegelUpperHalfSpace.sum_le_sum_of_coeff_satakeMapUniv_ne_zero`). The right coset of the
diagonal itself has the weight `(δ; δ - a)` (`SiegelUpperHalfSpace.dominantWeight`), and the
coefficient of `Ω(T(δ; a))` there is a sum of positive reals, hence nonzero
(`SiegelUpperHalfSpace.coeff_satakeMapUniv_dominantWeight_ne_zero`). This is the triangularity of
the Satake map (Andrianov, *Quadratic forms and Hecke operators*, Lemma 3.3.29). Finally the weights
of every `Ω(T)` lie in the cone `0 ≤ d_j ≤ δ`
(`SiegelUpperHalfSpace.nonneg_of_coeff_satakeMapUniv_ne_zero`,
`SiegelUpperHalfSpace.le_of_coeff_satakeMapUniv_ne_zero`).

The expansion `Matrix.det_mul_eq_sum_det_submatrix` of the determinant of a product is a short
helper: Tau Ceti's main has the Cauchy–Binet formula as
`TauCeti.det_mul_transpose_eq_sum_plucker_mul` (`TauCeti.LinearAlgebra.ExteriorPower.Plucker`),
which is not at the pin and can replace it after the bump.

## Main definitions

* `Matrix.DvdMinors`: an element divides every `k × k` minor of a square matrix.
* `SiegelUpperHalfSpace.dominantWeight`: the weight `(δ; δ - a)` of `diag(p^a, p^{δ-a})`.

## Main results

* `Matrix.det_mul_eq_sum_det_submatrix`: the determinant of a product, expanded over the columns.
* `SiegelUpperHalfSpace.sum_le_sum_of_coeff_satakeMapUniv_ne_zero`: the weights of `Ω(T(δ; a))`
  are below the dominant weight.
* `SiegelUpperHalfSpace.coeff_satakeMapUniv_dominantWeight_ne_zero`: the coefficient of
  `Ω(T(δ; a))` at the dominant weight is nonzero.
* `SiegelUpperHalfSpace.nonneg_of_coeff_satakeMapUniv_ne_zero`,
  `SiegelUpperHalfSpace.le_of_coeff_satakeMapUniv_ne_zero`: the weights of `Ω(T)` lie in the cone.
-/

open DoubleCoset MonoidAlgebra

open HeckeCosetModule (single)

namespace Matrix

variable {ι R : Type*} [CommRing R] {k : ℕ}

variable [Fintype ι] in
/-- **The determinant of a product, expanded over the columns** (LMFDB `mf.siegel.lift`, through
Satake's theorem): `det (A B) = ∑_g (∏_i B_{g(i), i}) det (A_{·, g})` over all `g : Fin k → ι`, the
expansion behind the Cauchy–Binet formula. -/
lemma det_mul_eq_sum_det_submatrix (A : Matrix (Fin k) ι R) (B : Matrix ι (Fin k) R) :
    (A * B).det = ∑ g : Fin k → ι, (∏ i, B (g i) i) * (A.submatrix id g).det := by
  simp only [det_apply', mul_apply, submatrix_apply, id_eq, Finset.prod_univ_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.prod_mul_distrib]
  ring1

variable (k) in
/-- `d` **divides the `k × k` minors** of `M` (LMFDB `mf.siegel.lift`, through Satake's theorem):
`d ∣ det (M_{r(i), c(j)})` for all `r, c : Fin k → ι`. -/
def DvdMinors (d : R) (M : Matrix ι ι R) : Prop :=
  ∀ r c : Fin k → ι, d ∣ (M.submatrix r c).det

variable {d : R} {M : Matrix ι ι R}

variable [Fintype ι] in
lemma DvdMinors.mul_right (h : M.DvdMinors k d) (X : Matrix ι ι R) : (M * X).DvdMinors k d :=
  fun r c ↦ by
    rw [submatrix_mul _ _ r id c Function.bijective_id, det_mul_eq_sum_det_submatrix]
    exact Finset.dvd_sum fun g _ ↦ (h r g).mul_left _

lemma dvdMinors_transpose : Mᵀ.DvdMinors k d ↔ M.DvdMinors k d :=
  ⟨fun h r c ↦ by
    rw [← det_transpose, transpose_submatrix]
    exact h c r, fun h r c ↦ by
    rw [← transpose_submatrix, det_transpose]
    exact h c r⟩

variable [Fintype ι] in
lemma DvdMinors.mul_left (h : M.DvdMinors k d) (X : Matrix ι ι R) : (X * M).DvdMinors k d := by
  rw [← dvdMinors_transpose, transpose_mul]
  exact (dvdMinors_transpose.mpr h).mul_right _

variable [DecidableEq ι] in
lemma dvdMinors_diagonal {e : ι → R}
    (he : ∀ c : Fin k → ι, Function.Injective c → d ∣ ∏ i, e (c i)) :
    (diagonal e).DvdMinors k d := fun r c ↦ by
  by_cases hc : Function.Injective c
  · rw [det_apply']
    refine Finset.dvd_sum fun σ _ ↦ ?_
    have h (i : Fin k) : (diagonal e).submatrix r c (σ i) i =
        (if r (σ i) = c i then 1 else 0) * e (c i) := by
      rw [submatrix_apply, diagonal_apply]
      split_ifs with h
      · rw [h, one_mul]
      · rw [zero_mul]
    rw [Finset.prod_congr rfl fun i _ ↦ h i, Finset.prod_mul_distrib]
    exact ((he c hc).mul_left _).mul_left _
  · rcases Function.not_injective_iff.mp hc with ⟨i, j, hij, hne⟩
    rw [det_zero_of_column_eq hne fun l ↦ by rw [submatrix_apply, submatrix_apply, hij]]
    exact dvd_zero d

end Matrix

namespace SiegelUpperHalfSpace

open Matrix

variable {n k : ℕ}

/-! ### The minors of the elementary divisors -/

lemma sum_castLE_le_sum_of_injective {N : ℕ} {f : Fin N → ℕ} (hf : Monotone f) (hk : k ≤ N)
    {g : Fin k → Fin N} (hg : Function.Injective g) : ∑ i, f (Fin.castLE hk i) ≤ ∑ i, f (g i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Finset.exists_max_image Finset.univ g Finset.univ_nonempty with ⟨i₀, -, hi₀⟩
    have hle : k ≤ (g i₀ : ℕ) := by
      by_contra hlt
      have hcard : Fintype.card (Fin (k + 1)) ≤ Fintype.card (Fin k) :=
        Fintype.card_le_of_injective (fun i ↦ ⟨g i, lt_of_le_of_lt
          (Fin.le_def.mp (hi₀ i (Finset.mem_univ i))) (not_le.mp hlt)⟩) fun i i' h ↦
            hg (Fin.ext (Fin.mk.inj_iff.mp h))
      simp at hcard
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ i₀, add_comm (f (g i₀))]
    exact add_le_add (ih (Nat.le_of_succ_le hk) (hg.comp Fin.succAbove_right_injective))
      (hf (Fin.le_def.mpr hle))

variable {δ : ℕ} {a : Fin n → ℕ}

lemma monotone_addCases (ha : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ) :
    Monotone (Fin.addCases a fun j ↦ δ - a j.rev : Fin (n + n) → ℕ) := by
  intro s s' hss'
  induction s using Fin.addCases with
  | left i =>
    induction s' using Fin.addCases with
    | left i' =>
      simp only [Fin.addCases_left]
      exact ha (Fin.le_def.mpr (Fin.le_def.mp hss'))
    | right j' =>
      simp only [Fin.addCases_left, Fin.addCases_right]
      have h₁ : 2 * a i ≤ δ := h2 i
      have h₂ : 2 * a j'.rev ≤ δ := h2 j'.rev
      omega
  | right j =>
    induction s' using Fin.addCases with
    | left i' =>
      have h : (Fin.natAdd n j : ℕ) ≤ Fin.castAdd n i' := hss'
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    | right j' =>
      simp only [Fin.addCases_right]
      have h : n + (j : ℕ) ≤ n + j' := Fin.le_def.mp hss'
      exact Nat.sub_le_sub_left (ha (Fin.rev_le_rev.mpr (Fin.le_def.mpr (by omega)))) δ

lemma sum_castLE_le_sum_elim (ha : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ) (hk : k ≤ n)
    {c : Fin k → Fin n ⊕ Fin n} (hc : Function.Injective c) :
    ∑ j, a (Fin.castLE hk j) ≤ ∑ i, Sum.elim a (fun j ↦ δ - a j) (c i) := by
  let τ : Fin n ⊕ Fin n → Fin (n + n) := Sum.elim (Fin.castAdd n) fun j ↦ Fin.natAdd n j.rev
  have hτ : Function.Injective τ := by
    rintro (i | i) (j | j) h <;> simp [τ, Fin.ext_iff] at h ⊢ <;> omega
  have he (m : Fin n ⊕ Fin n) : (Fin.addCases a fun j ↦ δ - a j.rev : Fin (n + n) → ℕ) (τ m) =
      Sum.elim a (fun j ↦ δ - a j) m := by
    rcases m with j | j
    · exact Fin.addCases_left j
    · simp only [τ, Sum.elim_inr]
      rw [Fin.addCases_right, Fin.rev_rev]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun j _ ↦ ?_)
    ((sum_castLE_le_sum_of_injective (monotone_addCases ha h2) (hk.trans (Nat.le_add_right n n))
      (hτ.comp hc)).trans_eq (Finset.sum_congr rfl fun i _ ↦ he (c i)))
  rw [show Fin.castLE (hk.trans (Nat.le_add_right n n)) j = Fin.castAdd n (Fin.castLE hk j) from
    Fin.ext rfl, Fin.addCases_left]

variable (p : ℕ)

lemma elementaryEntries_eq_pow (m : Fin n ⊕ Fin n) :
    elementaryEntries p δ a m = p ^ Sum.elim a (fun j ↦ δ - a j) m := by
  rcases m with j | j <;> rfl

lemma dvdMinors_elementaryEntries (ha : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ) (hk : k ≤ n) :
    (diagonal fun i ↦ (elementaryEntries p δ a i : ℤ)).DvdMinors k
      ((p : ℤ) ^ ∑ j, a (Fin.castLE hk j)) :=
  dvdMinors_diagonal fun c hc ↦ by
    simp only [elementaryEntries_eq_pow, Nat.cast_pow, Finset.prod_pow_eq_pow_sum]
    exact pow_dvd_pow _ (sum_castLE_le_sum_elim ha h2 hk hc)

/-! ### The representatives in the Borel subgroup -/

variable (δ a) in
/-- The weight `(δ; δ - a_0, …, δ - a_{g-1})` of the right coset of
`diag(p^{a_0}, …, p^{a_{g-1}}, p^{δ-a_0}, …, p^{δ-a_{g-1}})` (LMFDB `mf.siegel.lift`, through
Satake's theorem: the **dominant weight** of `T(δ; a)`). -/
def dominantWeight : SatakeWeight n :=
  .ofAdd ((δ : ℤ), fun j ↦ (δ : ℤ) - a j)

variable [Fact p.Prime] (ha : ∀ j, a j ≤ δ)

attribute [local instance] Fintype.ofFinite

lemma elementaryDiag_mem_siegelBorel :
    (elementaryDiag p δ a ha : GL (Fin n ⊕ Fin n) ℚ) ∈ siegelBorel n := by
  refine ⟨heckeMonoid_le_gspPlusGL (heckeMonoidAt_le_heckeMonoid p (elementaryDiag p δ a ha).2),
    ?_, fun i j hij ↦ ?_⟩
  · ext i j
    simp [coe_elementaryDiag]
  · simp only [toBlocks₁₁, Matrix.of_apply]
    exact diagonal_apply_ne _ fun h ↦ hij.ne' (Sum.inl_injective h)

variable {p ha}

lemma mem_doubleCoset_elementaryDiag (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
    ((elementaryCoset p δ a ha).out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) :
    (borelRep (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v) :
      GL (Fin n ⊕ Fin n) ℚ) ∈ doubleCoset (elementaryDiag p δ a ha : GL (Fin n ⊕ Fin n) ℚ)
        (heckeGamma (Fin n)) (heckeGamma (Fin n)) := by
  rcases exists_borelRep_eq (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v) with
    ⟨γ, hγ, h⟩
  have hD : doubleCoset ((elementaryCoset p δ a ha).out : GL (Fin n ⊕ Fin n) ℚ)
      (heckeGamma (Fin n)) (heckeGamma (Fin n)) = doubleCoset (elementaryDiag p δ a ha :
        GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n)) (heckeGamma (Fin n)) :=
    doubleCoset_eq_of_mem (HeckeCoset.rep_mk_mem_doubleCoset _)
  rcases mem_doubleCoset.mp (hD ▸ rightCosetRep_mem_doubleCoset (elementaryCoset p δ a ha) v) with
    ⟨γ₁, hγ₁, γ₂, hγ₂, h'⟩
  rw [h, h']
  exact mem_doubleCoset.mpr ⟨γ * γ₁, mul_mem hγ hγ₁, γ₂, hγ₂, by group⟩

lemma dvdMinors_of_mem_doubleCoset {x : GL (Fin n ⊕ Fin n) ℚ}
    (hx : x ∈ doubleCoset (elementaryDiag p δ a ha : GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n))
      (heckeGamma (Fin n))) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ}
    (hM : (Int.castRingHom ℚ).mapMatrix M = x) (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ)
    (hk : k ≤ n) : M.DvdMinors k ((p : ℤ) ^ ∑ j, a (Fin.castLE hk j)) := by
  rcases mem_doubleCoset.mp hx with ⟨_, ⟨g, -, rfl⟩, _, ⟨g', -, rfl⟩, rfl⟩
  have e : (Int.castRingHom ℚ).mapMatrix M = (Int.castRingHom ℚ).mapMatrix
      ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) *
        diagonal (fun i ↦ (elementaryEntries p δ a i : ℤ)) *
          (g' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)) := by
    rw [hM, map_mul, map_mul, mapMatrix_elementaryEntries ha, Units.val_mul, Units.val_mul]
    rfl
  rw [map_injective Int.cast_injective e]
  exact ((dvdMinors_elementaryEntries p hmono h2 hk).mul_left _).mul_right _

lemma dvd_prod_borelDiag_num (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ) {b : siegelBorel n}
    (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ doubleCoset (elementaryDiag p δ a ha :
      GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
    (hb' : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) (hk : k ≤ n) :
    (p : ℤ) ^ ∑ j, a (Fin.castLE hk j) ∣ ∏ j : Fin k, (borelDiag b (Fin.castLE hk j)).num := by
  rcases hb' with ⟨⟨-, M, hM⟩, -⟩
  have hMb (i i' : Fin n ⊕ Fin n) :
      ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ) i i' = M i i' :=
    (congrFun (congrFun hM i) i').symm
  have hdet : (M.submatrix (fun j : Fin k ↦ .inl (Fin.castLE hk j))
      fun j ↦ .inl (Fin.castLE hk j)).det = ∏ j : Fin k, (borelDiag b (Fin.castLE hk j)).num := by
    rw [det_of_isUpperTriangular fun i j hij ↦ ?_]
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [submatrix_apply, borelDiag, hMb, Rat.num_intCast]
    · have h0 : ((b : GL (Fin n ⊕ Fin n) ℚ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℚ)
          (.inl (Fin.castLE hk i)) (.inl (Fin.castLE hk j)) = 0 :=
        b.2.2.2 ((Fin.castLE_lt_castLE_iff hk).mpr hij)
      rw [hMb] at h0
      exact_mod_cast h0
  rw [← hdet]
  exact dvdMinors_of_mem_doubleCoset hb hM hmono h2 hk _ _

variable [NeZero n]

variable (p ha) in
lemma satakeValuation_elementaryDiag :
    satakeValuation p ⟨_, elementaryDiag_mem_siegelBorel p ha⟩ = dominantWeight δ a := by
  have hd (j : Fin n) : borelDiag ⟨_, elementaryDiag_mem_siegelBorel p ha⟩ j = (p : ℚ) ^ a j := by
    simp [borelDiag, coe_elementaryDiag, elementaryEntries]
  have hr : borelMultiplier ⟨_, elementaryDiag_mem_siegelBorel p ha⟩ = (p : ℚ) ^ δ := by
    rw [← borelDiag_mul_apply_inr _ 0, hd]
    simp [coe_elementaryDiag, elementaryEntries, ← pow_add, Nat.add_sub_cancel' (ha 0)]
  have hv (e : ℕ) : padicValRat p ((p : ℚ) ^ e) = e := by
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
  simp only [satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, hr, hd, hv, dominantWeight]

lemma sum_le_sum_padicValRat_borelDiag (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ)
    {b : siegelBorel n} (hb : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ doubleCoset
      (elementaryDiag p δ a ha : GL (Fin n ⊕ Fin n) ℚ) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
    (hb' : (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeMonoidAt (Fin n) p) (hk : k ≤ n) :
    ∑ j, (a (Fin.castLE hk j) : ℤ) ≤ ∑ j, padicValRat p (borelDiag b (Fin.castLE hk j)) := by
  choose e he hq using exists_natAbs_num_borelDiag hb'
  have hv (j : Fin n) : padicValRat p (borelDiag b j) = e j := by
    rw [← hq j, padicValRat.of_int, padicValInt, he j, padicValNat.prime_pow]
  have hd : p ^ ∑ j : Fin k, a (Fin.castLE hk j) ∣ p ^ ∑ j : Fin k, e (Fin.castLE hk j) := by
    have h : ((p : ℤ) ^ ∑ j, a (Fin.castLE hk j)).natAbs ∣
        Int.natAbsHom (∏ j : Fin k, (borelDiag b (Fin.castLE hk j)).num) :=
      Int.natAbs_dvd_natAbs.mpr (dvd_prod_borelDiag_num hmono h2 hb hb' hk)
    rwa [map_prod, Int.natAbs_pow, Int.natAbs_natCast, Finset.prod_congr rfl fun j _ ↦
      (Int.natAbsHom_apply _).trans (he (Fin.castLE hk j)), Finset.prod_pow_eq_pow_sum] at h
  simp only [hv]
  exact_mod_cast (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd

lemma borelMultiplier_elementaryDiag :
    borelMultiplier ⟨_, elementaryDiag_mem_siegelBorel p ha⟩ = (p : ℚ) ^ δ := by
  rw [← borelDiag_mul_apply_inr _ 0]
  simp [borelDiag, coe_elementaryDiag, elementaryEntries, ← pow_add, Nat.add_sub_cancel' (ha 0)]

/-! ### The coefficients of the universal Satake map -/

variable (p) in
lemma coeff_satakeMapUniv_single (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n))
    (heckeGamma (Fin n))) (μ : SatakeWeight n) :
    (satakeMapUniv p (single ℂ D 1)).coeff μ = ((Finset.univ.filter fun v ↦ satakeValuation p
      (borelRep (rightCosetRep_mem_gspPlusGL p D v)) = μ).card : ℂ) *
        (weightCharacter 1 (fun i ↦ (primeUnit p)⁻¹ ^ (n - (i : ℕ))) μ : ℂ) := by
  rw [satakeMapUniv_single_one, coeff_sum, Finsupp.finsetSum_apply, ← nsmul_eq_mul,
    ← Finset.sum_const, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [coe_satakeCharacterUniv, coeff_single, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · rfl

lemma exists_satakeValuation_eq_of_coeff_ne_zero {D : HeckeCoset (heckeMonoidAt (Fin n) p)
    (heckeGamma (Fin n)) (heckeGamma (Fin n))} {μ : SatakeWeight n}
    (h : (satakeMapUniv p (single ℂ D 1)).coeff μ ≠ 0) :
    ∃ v, satakeValuation p (borelRep (rightCosetRep_mem_gspPlusGL p D v)) = μ := by
  rw [coeff_satakeMapUniv_single] at h
  rcases Finset.card_ne_zero.mp fun h' ↦ h (by rw [h', Nat.cast_zero, zero_mul]) with ⟨v, hv⟩
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

lemma exists_coeff_satakeMapUniv_single_ne_zero {T : localSiegelHeckeRing (Fin n) p}
    {μ : SatakeWeight n} (h : (satakeMapUniv p T).coeff μ ≠ 0) :
    ∃ D, (satakeMapUniv p (single ℂ D 1)).coeff μ ≠ 0 := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 =>
    rw [map_zero, coeff_zero, Finsupp.zero_apply] at h
    exact absurd rfl h
  | hadd x y hx hy =>
    rw [map_add, coeff_add, Finsupp.add_apply] at h
    by_cases hx' : (satakeMapUniv p x).coeff μ = 0
    · rw [hx', zero_add] at h
      exact hy h
    · exact hx hx'
  | hsingle D c =>
    refine ⟨D, fun h' ↦ h ?_⟩
    rw [satakeMapUniv_single, coeff_smul_apply, h', smul_zero]

/-- **The weights of the universal Satake map have nonnegative coordinates** (LMFDB
`mf.siegel.lift`, through Satake's theorem): `d_j = v_p(D_jj) ≥ 0` for the integral representative
`(A, B; 0, D)` in the Borel subgroup of a right coset. -/
lemma nonneg_of_coeff_satakeMapUniv_ne_zero {T : localSiegelHeckeRing (Fin n) p}
    {μ : SatakeWeight n} (h : (satakeMapUniv p T).coeff μ ≠ 0) (j : Fin n) : 0 ≤ μ.toAdd.2 j := by
  rcases exists_coeff_satakeMapUniv_single_ne_zero h with ⟨D, hD⟩
  rcases exists_satakeValuation_eq_of_coeff_ne_zero hD with ⟨v, rfl⟩
  have hb : (borelRep (rightCosetRep_mem_gspPlusGL p D v) : GL (Fin n ⊕ Fin n) ℚ) ∈
      heckeMonoidAt (Fin n) p :=
    borelRep_mem_heckeMonoidAt (rightCosetRep_mem_heckeMonoidAt p D v) _
  simp only [satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    padicValRat_borelMultiplier_eq p (j₀ := j) hb, borelDiag,
    padicValRat_borelDiag_eq_padicValNat p hb j]
  omega

/-- **The weights of the universal Satake map lie below their multiplier** (LMFDB `mf.siegel.lift`,
through Satake's theorem): `d_j = δ - v_p(A_jj) ≤ δ` for the integral representative
`(A, B; 0, D)` in the Borel subgroup of a right coset. -/
lemma le_of_coeff_satakeMapUniv_ne_zero {T : localSiegelHeckeRing (Fin n) p} {μ : SatakeWeight n}
    (h : (satakeMapUniv p T).coeff μ ≠ 0) (j : Fin n) : μ.toAdd.2 j ≤ μ.toAdd.1 := by
  rcases exists_coeff_satakeMapUniv_single_ne_zero h with ⟨D, hD⟩
  rcases exists_satakeValuation_eq_of_coeff_ne_zero hD with ⟨v, rfl⟩
  have hb : (borelRep (rightCosetRep_mem_gspPlusGL p D v) : GL (Fin n ⊕ Fin n) ℚ) ∈
      heckeMonoidAt (Fin n) p :=
    borelRep_mem_heckeMonoidAt (rightCosetRep_mem_heckeMonoidAt p D v) _
  simp only [satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, borelDiag,
    padicValRat_borelDiag_eq_padicValNat p hb j]
  omega

/-! ### The triangularity -/

lemma fst_eq_of_coeff_satakeMapUniv_ne_zero {μ : SatakeWeight n}
    (h : (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff μ ≠ 0) :
    μ.toAdd.1 = δ := by
  rcases exists_satakeValuation_eq_of_coeff_ne_zero h with ⟨v, rfl⟩
  rcases mem_doubleCoset.mp (mem_doubleCoset_elementaryDiag v) with ⟨γ, hγ, γ', hγ', e⟩
  have hr : borelMultiplier (borelRep (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v))
      = (p : ℚ) ^ δ := by
    rw [borelMultiplier_eq_of_mul (b := ⟨_, elementaryDiag_mem_siegelBorel p ha⟩) hγ hγ' e,
      borelMultiplier_elementaryDiag]
  simp only [satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, hr]
  rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]

/-- **The weights of `Ω(T(δ; a))` lie below the dominant weight** (LMFDB `mf.siegel.lift`, through
Satake's theorem): for `a` dominant, every weight `(δ'; d)` with a nonzero coefficient in the
universal Satake map of `T(δ; a)` has `∑_{j<k} (δ' - d_j) ≥ a_0 + ⋯ + a_{k-1}` for every `k ≤ g`
(and `δ' = δ`). -/
lemma sum_le_sum_of_coeff_satakeMapUniv_ne_zero (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ)
    {μ : SatakeWeight n} (h : (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff μ ≠ 0)
    (hk : k ≤ n) :
    ∑ j, (a (Fin.castLE hk j) : ℤ) ≤ ∑ j, (μ.toAdd.1 - μ.toAdd.2 (Fin.castLE hk j)) := by
  rcases exists_satakeValuation_eq_of_coeff_ne_zero h with ⟨v, rfl⟩
  simp only [satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, sub_sub_cancel]
  exact sum_le_sum_padicValRat_borelDiag hmono h2 (mem_doubleCoset_elementaryDiag v)
    (borelRep_mem_heckeMonoidAt (rightCosetRep_mem_heckeMonoidAt p _ v) _) hk

lemma exists_satakeValuation_eq_dominantWeight : ∃ v, satakeValuation p (borelRep
    (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v)) = dominantWeight δ a := by
  rcases exists_rightCosetRep_smul_eq (elementaryCoset p δ a ha)
    (HeckeCoset.mem_doubleCoset_rep_mk (elementaryDiag p δ a ha)) with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  have hc : rightCosetRep (elementaryCoset p δ a ha) v * (elementaryDiag p δ a ha :
      GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈ heckeGamma (Fin n) :=
    (rightCoset_eq_iff _).mp hv
  rcases exists_borelRep_eq (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v) with
    ⟨γ, hγ, h⟩
  have hb : ((borelRep (rightCosetRep_mem_gspPlusGL p (elementaryCoset p δ a ha) v) *
      (⟨_, elementaryDiag_mem_siegelBorel p ha⟩ : siegelBorel n)⁻¹ : siegelBorel n) :
        GL (Fin n ⊕ Fin n) ℚ) ∈ heckeGamma (Fin n) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h, mul_assoc]
    exact mul_mem hγ hc
  have h₁ : satakeValuation p (borelRep (rightCosetRep_mem_gspPlusGL p
      (elementaryCoset p δ a ha) v) * (⟨_, elementaryDiag_mem_siegelBorel p ha⟩ :
        siegelBorel n)⁻¹) = 1 :=
    satakeValuation_eq_one p hb
  rw [map_mul, map_inv, mul_inv_eq_one] at h₁
  rw [h₁, satakeValuation_elementaryDiag]

/-- **The coefficient of `Ω(T(δ; a))` at the dominant weight is nonzero** (LMFDB
`mf.siegel.lift`, through Satake's theorem): the right coset of the diagonal has the weight
`(δ; δ - a)`, and the coefficient there is the number of such right cosets times a unit. -/
lemma coeff_satakeMapUniv_dominantWeight_ne_zero :
    (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff (dominantWeight δ a) ≠ 0 := by
  rcases exists_satakeValuation_eq_dominantWeight (p := p) (ha := ha) with ⟨v, hv⟩
  rw [coeff_satakeMapUniv_single]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩)) (Units.ne_zero _)

end SiegelUpperHalfSpace
