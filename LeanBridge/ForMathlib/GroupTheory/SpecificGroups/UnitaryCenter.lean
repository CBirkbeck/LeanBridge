import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.Unitary
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The centres of the finite unitary groups

The centre of `GU(n, q)`, and that of `SU(n, q)`, is the subgroup of scalar matrices it contains
(LMFDB `group.unitary`), so that `PGU(n, q)` and `PSU(n, q)` are the quotients of `GU(n, q)` and
`SU(n, q)` by their centres. A matrix `A` commuting with every element of `SU(n, q)` is scalar: it
commutes with the diagonal matrices with entries `c` and `c⁻¹` in places `i ≠ j` and `1`
elsewhere, for an element `c` of `𝔽_{q²}` with `c ^ (q + 1) = 1` and `c² ≠ 1`, so it is diagonal;
and it commutes with the signed transpositions `eᵢ ↦ eⱼ ↦ -eᵢ`, so its diagonal entries agree.
Both kinds of matrices are unitary of determinant `1`, the first because `c x ^ q = c ^ (q + 1)`
for `x = c`. Such a `c` exists because `𝔽_{q²}ˣ` is cyclic of order `q² - 1`: `c = ζ ^ (q - 1)`
for a generator `ζ` has order `q + 1 > 2`.

## Main results

* `Matrix.center_specialUnitaryGroupFq` (LMFDB `group.unitary`): the centre of `SU(n, q)` is its
  subgroup of scalar matrices.
* `Matrix.center_generalUnitaryGroup` (LMFDB `group.unitary`): the centre of `GU(n, q)` is its
  subgroup of scalar matrices.
* `Matrix.projectiveGeneralUnitaryGroupEquiv`, `Matrix.projectiveSpecialUnitaryGroupEquiv` (LMFDB
  `group.unitary`): `PGU(n, q)` and `PSU(n, q)` are the quotients by the centres.
-/

open Equiv Subgroup

variable {p r : ℕ} [Fact p.Prime]

namespace Matrix

variable {K : Type*} [Field K] (σ : K →+* K) {n : Type*} [DecidableEq n] {c : K} {i j : n}

lemma mulSingle_mul_map_mulSingle (hc : c * σ c = 1) (k : n) :
    (Pi.mulSingle i c : n → K) k * σ ((Pi.mulSingle i c : n → K) k) = 1 := by
  rcases eq_or_ne k i with rfl | hk
  · simpa using hc
  · simp [Pi.mulSingle_eq_of_ne hk]

lemma permMatrix_map (τ : Equiv.Perm n) : (τ.permMatrix K).map σ = τ.permMatrix K := by
  ext k l
  simp only [map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

variable [Fintype n] {A : Matrix n n K} {d : n → K}

lemma apply_eq_zero_of_mul_diagonal_eq (h : A * diagonal d = diagonal d * A) (hd : d i ≠ d j) :
    A i j = 0 := by
  have hij : A i j * d j = d i * A i j := by
    simpa using congrFun (congrFun h i) j
  have h₀ : A i j * (d j - d i) = 0 := by
    linear_combination hij
  exact (mul_eq_zero.mp h₀).resolve_right (sub_ne_zero.mpr hd.symm)

lemma apply_eq_apply_of_mul_eq {a : n → K} {S : Matrix n n K} (h : diagonal a * S = S * diagonal a)
    (hS : S j i ≠ 0) : a i = a j := by
  have hji : a j * S j i = S j i * a i := by
    simpa using congrFun (congrFun h j) i
  exact mul_left_cancel₀ hS <| hji.symm.trans (mul_comm _ _)

lemma diagonal_mul_transpose_map_diagonal (hd : ∀ k, d k * σ (d k) = 1) :
    diagonal d * ((diagonal d).map σ)ᵀ = 1 := by
  rw [diagonal_map (map_zero σ), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg diagonal <| funext hd

lemma mem_range_scalar_of_forall_commute (hc : c * σ c = 1) (hc2 : c ^ 2 ≠ 1)
    (hA : ∀ g ∈ sesquiUnitaryGroup σ n ⊓ GeneralLinearGroup.det.ker, A * g = g * A) :
    A ∈ Set.range (scalar n) := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hσc : σ c = c⁻¹ := eq_inv_of_mul_eq_one_right hc
  have hoff (i j : n) (hij : i ≠ j) : A i j = 0 := by
    let d : n → K := Pi.mulSingle i c * Pi.mulSingle j c⁻¹
    have hd : diagonal d * ((diagonal d).map σ)ᵀ = 1 := by
      refine diagonal_mul_transpose_map_diagonal σ fun k ↦ ?_
      have h₁ : (Pi.mulSingle i c : n → K) k * σ ((Pi.mulSingle i c : n → K) k) = 1 :=
        mulSingle_mul_map_mulSingle σ hc k
      have h₂ : (Pi.mulSingle j c⁻¹ : n → K) k * σ ((Pi.mulSingle j c⁻¹ : n → K) k) = 1 :=
        mulSingle_mul_map_mulSingle σ (by rw [map_inv₀, hσc, inv_inv, inv_mul_cancel₀ hc0]) k
      simp only [d, Pi.mul_apply, map_mul]
      linear_combination
        ((Pi.mulSingle j c⁻¹ : n → K) k * σ ((Pi.mulSingle j c⁻¹ : n → K) k)) * h₁ + h₂
    have hdet : (diagonal d).det = 1 := by
      rw [det_diagonal]
      simp [d, Finset.prod_mul_distrib, hc0]
    refine apply_eq_zero_of_mul_diagonal_eq (hA ⟨diagonal d, _, hd, mul_eq_one_comm.mp hd⟩
      ⟨hd, Units.ext hdet⟩) ?_
    simp only [d, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij,
      Pi.mulSingle_eq_of_ne hij.symm, mul_one, one_mul]
    exact fun h ↦ hc2 <| (pow_two c).trans <| (congrArg (c * ·) h).trans (mul_inv_cancel₀ hc0)
  have hA' : A = diagonal fun k ↦ A k k := by
    ext k l
    rcases eq_or_ne k l with rfl | hkl
    · simp
    · rw [diagonal_apply_ne _ hkl, hoff k l hkl]
  have hdiag (i j : n) (hij : i ≠ j) : A i i = A j j := by
    let S : Matrix n n K := (Equiv.swap i j).permMatrix K * diagonal (Pi.mulSingle i (-1))
    have hS : S * (S.map σ)ᵀ = 1 := by
      simp only [S, Matrix.map_mul, permMatrix_map, diagonal_map (map_zero σ), transpose_mul,
        diagonal_transpose, transpose_permMatrix]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal,
        funext (mulSingle_mul_map_mulSingle σ (by simp)), diagonal_one, Matrix.one_mul,
        ← permMatrix_mul, inv_mul_cancel, permMatrix_one]
    have hSdet : S.det = 1 := by
      simp [S, Perm.sign_swap hij]
    have hSji : S j i ≠ 0 := by
      simp [S]
    have h : A * S = S * A := hA ⟨S, _, hS, mul_eq_one_comm.mp hS⟩ ⟨hS, Units.ext hSdet⟩
    rw [hA'] at h
    exact apply_eq_apply_of_mul_eq h hSji
  rcases isEmpty_or_nonempty n with hn | ⟨⟨k₀⟩⟩
  · exact ⟨0, ext fun k ↦ (IsEmpty.false k).elim⟩
  refine ⟨A k₀ k₀, hA'.trans (congrArg diagonal <| funext fun k ↦ ?_) |>.symm⟩
  rcases eq_or_ne k₀ k with rfl | hk
  · rfl
  · exact (hdiag k₀ k hk).symm

lemma exists_mul_iterateFrobenius_eq_one (hr : r ≠ 0) : ∃ c : GaloisField p (2 * r),
    c * iterateFrobenius (GaloisField p (2 * r)) p r c = 1 ∧ c ^ 2 ≠ 1 := by
  have hq : 2 ≤ p ^ r := Nat.one_lt_pow hr (Fact.out : p.Prime).one_lt
  have hcard : Nat.card (GaloisField p (2 * r))ˣ = (p ^ r + 1) * (p ^ r - 1) := by
    rw [Nat.card_units, GaloisField.card p (2 * r) (by omega), pow_mul', ← Nat.sq_sub_sq, one_pow]
  rcases IsCyclic.exists_generator (α := (GaloisField p (2 * r))ˣ) with ⟨ζ, hζ⟩
  have hord : orderOf ζ = (p ^ r + 1) * (p ^ r - 1) :=
    (orderOf_eq_card_of_forall_mem_zpowers hζ).trans hcard
  refine ⟨((ζ ^ (p ^ r - 1) : (GaloisField p (2 * r))ˣ) : GaloisField p (2 * r)), ?_, fun h ↦ ?_⟩
  · rw [iterateFrobenius_def, ← pow_succ', ← Units.val_pow_eq_pow_val, ← pow_mul,
      mul_comm (p ^ r - 1), ← hord, pow_orderOf_eq_one, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, Units.val_eq_one, ← pow_mul, mul_comm (p ^ r - 1)] at h
    have h₂ : (p ^ r + 1) * (p ^ r - 1) ∣ 2 * (p ^ r - 1) := hord ▸ orderOf_dvd_of_pow_eq_one h
    have h₁ : p ^ r + 1 ∣ 2 := Nat.dvd_of_mul_dvd_mul_right (by omega) h₂
    have h₃ : p ^ r + 1 ≤ 2 := Nat.le_of_dvd two_pos h₁
    omega

end Matrix

namespace Matrix

variable (n : ℕ)

lemma mem_range_scalar_of_forall_commute_specialUnitaryGroupFq (hr : r ≠ 0)
    {A : Matrix (Fin n) (Fin n) (GaloisField p (2 * r))}
    (hA : ∀ g ∈ specialUnitaryGroupFq n p r, A * g = g * A) : A ∈ Set.range (scalar (Fin n)) := by
  rcases exists_mul_iterateFrobenius_eq_one (p := p) hr with ⟨c, hc, hc2⟩
  exact mem_range_scalar_of_forall_commute _ hc hc2 hA

lemma center_eq_subgroupOf_of_specialUnitaryGroupFq_le (hr : r ≠ 0)
    {G : Subgroup (GL (Fin n) (GaloisField p (2 * r)))} (hG : specialUnitaryGroupFq n p r ≤ G) :
    center G = (center (GL (Fin n) (GaloisField p (2 * r)))).subgroupOf G := by
  ext g
  rw [mem_subgroupOf, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, mem_center_iff]
  refine ⟨fun hg ↦ mem_range_scalar_of_forall_commute_specialUnitaryGroupFq n hr fun h hh ↦ ?_,
    fun hg h ↦ Subtype.ext <|
      mem_center_iff.mp (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr hg) h⟩
  simpa using (Units.ext_iff.mp (Subtype.ext_iff.mp (hg ⟨h, hG hh⟩))).symm

/-- **The centre of `SU(n, q)` is its subgroup of scalar matrices** (LMFDB `group.unitary`), for
`q = p ^ r` with `r ≠ 0`: the elements of `SU(n, q)` that are scalar matrices. -/
lemma center_specialUnitaryGroupFq (hr : r ≠ 0) : center (specialUnitaryGroupFq n p r) =
    (center (GL (Fin n) (GaloisField p (2 * r)))).subgroupOf (specialUnitaryGroupFq n p r) :=
  center_eq_subgroupOf_of_specialUnitaryGroupFq_le n hr le_rfl

/-- **The centre of `GU(n, q)` is its subgroup of scalar matrices** (LMFDB `group.unitary`), for
`q = p ^ r` with `r ≠ 0`: a central element of `GU(n, q)` commutes with `SU(n, q)`, so it is
scalar. -/
lemma center_generalUnitaryGroup (hr : r ≠ 0) : center (generalUnitaryGroup n p r) =
    (center (GL (Fin n) (GaloisField p (2 * r)))).subgroupOf (generalUnitaryGroup n p r) :=
  center_eq_subgroupOf_of_specialUnitaryGroupFq_le n hr inf_le_left

/-- **`PGU(n, q)` is the quotient of `GU(n, q)` by its centre** (LMFDB `group.unitary`), for
`q = p ^ r` with `r ≠ 0`. -/
noncomputable def projectiveGeneralUnitaryGroupEquiv (hr : r ≠ 0) :
    projectiveGeneralUnitaryGroup n p r ≃*
      generalUnitaryGroup n p r ⧸ center (generalUnitaryGroup n p r) :=
  QuotientGroup.quotientMulEquivOfEq (center_generalUnitaryGroup n hr).symm

/-- **`PSU(n, q)` is the quotient of `SU(n, q)` by its centre** (LMFDB `group.unitary`), for
`q = p ^ r` with `r ≠ 0`. -/
noncomputable def projectiveSpecialUnitaryGroupEquiv (hr : r ≠ 0) :
    projectiveSpecialUnitaryGroup n p r ≃*
      specialUnitaryGroupFq n p r ⧸ center (specialUnitaryGroupFq n p r) :=
  QuotientGroup.quotientMulEquivOfEq (center_specialUnitaryGroupFq n hr).symm

end Matrix
