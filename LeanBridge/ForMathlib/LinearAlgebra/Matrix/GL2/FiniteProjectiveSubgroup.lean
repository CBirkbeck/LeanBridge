import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.IntegralDomain
import LeanBridge.ForMathlib.GroupTheory.GroupAction.TwoFixedPoints

/-!
# Finite subgroups of `PGL₂(ℂ)`

Every finite subgroup of `PGL₂(ℂ)` is cyclic, dihedral of order `2n` with `n ≥ 2`, or isomorphic to
`A₄`, `S₄` or `A₅` (`Matrix.ProjGenLinGroup.classification`). This is the classification of the
finite groups acting with two fixed points (`MulAction.HasTwoFixedPoints.classification`), applied
to the action of a finite subgroup `H` of `PGL₂(ℂ)` on the projective line `ℙ¹(ℂ)`:

* a nontrivial element of `H` has exactly two fixed points: a matrix `A` representing it has `Aⁿ`
  scalar for some `n ≥ 1`; if its characteristic polynomial had a double root `μ`, then
  `A = μ (1 + N)` with `N² = 0`, and `Aⁿ = μⁿ (1 + n N)` scalar forces `N = 0`, so `A` would be
  scalar; so `A` has two distinct eigenvalues, and its fixed points are its two eigenlines;
* the stabiliser of a point is cyclic: conjugating the point to `(1 : 0)`, the stabiliser consists
  of upper triangular matrices modulo scalars, and the ratio of the diagonal entries is an injective
  homomorphism from it to `ℂ×`, whose finite subgroups are cyclic.

## Main definitions

* `Matrix.ProjGenLinGroup.diagRatio`: the ratio of the diagonal entries of a matrix representing an
  element of `PGL₂(ℂ)`.

## Main results

* `Matrix.ProjGenLinGroup.ncard_fixedBy_eq_two`: a nontrivial element of finite order of `PGL₂(ℂ)`
  has exactly two fixed points on the projective line.
* `Matrix.ProjGenLinGroup.isCyclic_stabilizer`: point stabilisers in a finite subgroup of `PGL₂(ℂ)`
  are cyclic.
* `Matrix.ProjGenLinGroup.hasTwoFixedPoints`: a finite subgroup of `PGL₂(ℂ)` acts on the projective
  line with two fixed points.
* `Matrix.ProjGenLinGroup.classification`: the classification of the finite subgroups of `PGL₂(ℂ)`.
-/

open Matrix MulAction Projectivization Set

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Matrix.ProjGenLinGroup

variable {A N : Matrix (Fin 2) (Fin 2) ℂ} {μ c : ℂ} {v w : Fin 2 → ℂ} {n : ℕ} {g : GL (Fin 2) ℂ}
  {h h₁ h₂ : PGL(Fin 2, ℂ)}

variable (A) in
lemma mul_self_eq_trace_smul_sub : A * A = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, trace_fin_two, det_fin_two] <;> ring1

lemma eq_zero_of_pow_eq_smul_one (hn : n ≠ 0) (hμ : μ ≠ 0) (hN : N * N = 0)
    (hpow : (μ • 1 + N) ^ n = c • 1) : N = 0 := by
  have key : ∀ k : ℕ, (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + N) ^ (k + 1) = μ ^ (k + 1) • 1 +
      (((k : ℂ) + 1) * μ ^ k) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hN, smul_zero, add_zero]
      push_cast
      module
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [key] at hpow
  have ht : ((k : ℂ) + 1) * μ ^ k ≠ 0 :=
    mul_ne_zero (by exact_mod_cast k.succ_ne_zero) (pow_ne_zero _ hμ)
  have hN' :
      N = ((((k : ℂ) + 1) * μ ^ k)⁻¹ * (c - μ ^ (k + 1))) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [mul_smul, sub_smul, ← hpow, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [hN', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hN
  rw [hN', mul_self_eq_zero.mp ((smul_eq_zero.mp hN).resolve_right one_ne_zero), zero_smul]

variable (A μ) in
lemma det_sub_smul_one : (A - μ • 1).det = μ * μ - A.trace * μ + A.det := by
  simp [det_fin_two, trace_fin_two]
  ring1

lemma exists_mulVec_eq_smul (hμ : μ * μ - A.trace * μ + A.det = 0) :
    ∃ v, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  rcases exists_mulVec_eq_zero_iff.mpr ((det_sub_smul_one A μ).trans hμ) with ⟨v, hv, hAv⟩
  exact ⟨v, hv, by rwa [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hAv⟩

lemma mul_self_sub_trace_mul_add_det_eq_zero (hv : v ≠ 0) (hAv : A *ᵥ v = μ • v) :
    μ * μ - A.trace * μ + A.det = 0 :=
  (det_sub_smul_one A μ).symm.trans <| exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by rw [sub_mulVec, smul_mulVec, one_mulVec, hAv, sub_self]⟩

lemma mk_eq_mk_of_mulVec_eq_smul (hA : A ≠ μ • 1) (hv : v ≠ 0) (hw : w ≠ 0) (hAv : A *ᵥ v = μ • v)
    (hAw : A *ᵥ w = μ • w) : Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  have hD : v 0 * w 1 = v 1 * w 0 := by
    by_contra hD
    have hD' : v 0 * w 1 - v 1 * w 0 ≠ 0 := sub_ne_zero.mpr hD
    have hv₀ : A 0 0 * v 0 + A 0 1 * v 1 = μ * v 0 := by
      simpa [mulVec] using congrFun hAv 0
    have hv₁ : A 1 0 * v 0 + A 1 1 * v 1 = μ * v 1 := by
      simpa [mulVec] using congrFun hAv 1
    have hw₀ : A 0 0 * w 0 + A 0 1 * w 1 = μ * w 0 := by
      simpa [mulVec] using congrFun hAw 0
    have hw₁ : A 1 0 * w 0 + A 1 1 * w 1 = μ * w 1 := by
      simpa [mulVec] using congrFun hAw 1
    refine hA <| ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp
    · exact sub_eq_zero.mp <| (mul_eq_zero.mp (by linear_combination w 1 * hv₀ - v 1 * hw₀ :
        (A 0 0 - μ) * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hD'
    · exact (mul_eq_zero.mp (by linear_combination v 0 * hw₀ - w 0 * hv₀ :
        A 0 1 * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hD'
    · exact (mul_eq_zero.mp (by linear_combination w 1 * hv₁ - v 1 * hw₁ :
        A 1 0 * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hD'
    · exact sub_eq_zero.mp <| (mul_eq_zero.mp (by linear_combination v 0 * hw₁ - w 0 * hv₁ :
        (A 1 1 - μ) * (v 0 * w 1 - v 1 * w 0) = 0)).resolve_right hD'
  refine (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mpr ?_
  by_cases hw0 : w 0 = 0
  · have hw1 : w 1 ≠ 0 := fun hw1 ↦ hw <| funext fun i ↦ by fin_cases i <;> assumption
    have hv0 : v 0 = 0 := by
      rw [hw0, mul_zero] at hD
      exact (mul_eq_zero.mp hD).resolve_right hw1
    refine ⟨v 1 / w 1, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [hw0, hv0]
    · simp [div_mul_cancel₀ _ hw1]
  · refine ⟨v 0 / w 0, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [div_mul_cancel₀ _ hw0]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hD

variable (μ) in
lemma val_ne_smul_one (hg : g ∉ Subgroup.center (GL (Fin 2) ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) ≠ μ • 1 := fun hμ ↦ hg <|
  GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    ⟨μ, by rw [hμ, scalar_apply, smul_one_eq_diagonal]⟩

lemma val_pow_eq_smul_one (hgn : g ^ n ∈ Subgroup.center (GL (Fin 2) ℂ)) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) ^ n = ((g : Matrix (Fin 2) (Fin 2) ℂ) ^ n) 0 0 • 1 := by
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hgn with ⟨c, hc⟩
  rw [← Units.val_pow_eq_pow_val, ← hc, scalar_apply, smul_one_eq_diagonal, diagonal_apply_eq]

lemma ncard_fixedBy_mk_of_ne (hg : g ∉ Subgroup.center (GL (Fin 2) ℂ)) {μ₁ μ₂ : ℂ} (hμ : μ₁ ≠ μ₂)
    (hsum : μ₁ + μ₂ = (g : Matrix (Fin 2) (Fin 2) ℂ).trace)
    (hprod : μ₁ * μ₂ = (g : Matrix (Fin 2) (Fin 2) ℂ).det) :
    (fixedBy (ℙ ℂ (Fin 2 → ℂ)) (mk g)).ncard = 2 := by
  rcases exists_mulVec_eq_smul (A := g) (μ := μ₁) (by rw [← hsum, ← hprod]; ring1) with
    ⟨v₁, hv₁, hAv₁⟩
  rcases exists_mulVec_eq_smul (A := g) (μ := μ₂) (by rw [← hsum, ← hprod]; ring1) with
    ⟨v₂, hv₂, hAv₂⟩
  have hfix : fixedBy (ℙ ℂ (Fin 2 → ℂ)) (mk g) =
      {Projectivization.mk ℂ v₁ hv₁, Projectivization.mk ℂ v₂ hv₂} := by
    ext x
    induction x using Projectivization.ind with
    | h w hw =>
      rw [mem_fixedBy, PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff', mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro ⟨a, ha⟩
        have hroot : a * a - (g : Matrix (Fin 2) (Fin 2) ℂ).trace * a +
            (g : Matrix (Fin 2) (Fin 2) ℂ).det = 0 :=
          mul_self_sub_trace_mul_add_det_eq_zero hw ha.symm
        rw [← hsum, ← hprod] at hroot
        rcases mul_eq_zero.mp (by linear_combination hroot : (a - μ₁) * (a - μ₂) = 0) with h | h
        · rw [sub_eq_zero] at h
          subst h
          exact Or.inl <| mk_eq_mk_of_mulVec_eq_smul (val_ne_smul_one _ hg) hw hv₁ ha.symm hAv₁
        · rw [sub_eq_zero] at h
          subst h
          exact Or.inr <| mk_eq_mk_of_mulVec_eq_smul (val_ne_smul_one _ hg) hw hv₂ ha.symm hAv₂
      · rintro (h | h) <;> rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ hw _).mp h with ⟨b, rfl⟩
        · refine ⟨μ₁, ?_⟩
          rw [smul_comm μ₁ b v₁, ← hAv₁]
          exact (mulVec_smul _ b v₁).symm
        · refine ⟨μ₂, ?_⟩
          rw [smul_comm μ₂ b v₂, ← hAv₂]
          exact (mulVec_smul _ b v₂).symm
  rw [hfix, ncard_pair]
  intro h
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ hv₁ hv₂).mp h with ⟨b, rfl⟩
  rw [mulVec_smul, hAv₂, smul_comm] at hAv₁
  exact hμ (smul_left_injective ℂ hv₁ hAv₁).symm

lemma ncard_fixedBy_mk (hg : g ∉ Subgroup.center (GL (Fin 2) ℂ)) (hn : n ≠ 0)
    (hgn : g ^ n ∈ Subgroup.center (GL (Fin 2) ℂ)) :
    (fixedBy (ℙ ℂ (Fin 2 → ℂ)) (mk g)).ncard = 2 := by
  have hc : (g : Matrix (Fin 2) (Fin 2) ℂ) ^ n = ((g : Matrix (Fin 2) (Fin 2) ℂ) ^ n) 0 0 • 1 :=
    val_pow_eq_smul_one hgn
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := (isUnits_det_units g).ne_zero
  rcases IsAlgClosed.isSquare
    ((g : Matrix (Fin 2) (Fin 2) ℂ).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) ℂ).det) with ⟨s, hs⟩
  by_cases hs0 : s = 0
  · subst hs0
    have hμ : (g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2 ≠ 0 := fun hμ ↦ hdet <| by
      linear_combination (-1 / 4 : ℂ) * hs + (g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2 * hμ
    have hdet' : (g : Matrix (Fin 2) (Fin 2) ℂ).det =
        (g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2 * ((g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2) := by
      linear_combination (-1 / 4 : ℂ) * hs
    have hN : ((g : Matrix (Fin 2) (Fin 2) ℂ) - ((g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2) • 1) *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) - ((g : Matrix (Fin 2) (Fin 2) ℂ).trace / 2) • 1) = 0 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
      rw [mul_self_eq_trace_smul_sub, hdet']
      module
    exact (val_ne_smul_one _ hg <| sub_eq_zero.mp <| eq_zero_of_pow_eq_smul_one hn hμ hN
      (by rwa [add_sub_cancel])).elim
  · exact ncard_fixedBy_mk_of_ne hg (μ₁ := ((g : Matrix (Fin 2) (Fin 2) ℂ).trace + s) / 2)
      (μ₂ := ((g : Matrix (Fin 2) (Fin 2) ℂ).trace - s) / 2) (fun h ↦ hs0 (by linear_combination h))
      (by ring1) (by linear_combination (1 / 4 : ℂ) * hs)

/-- **A nontrivial element of finite order of `PGL₂(ℂ)` has exactly two fixed points on the
projective line**: a matrix `A` representing it has `Aⁿ` scalar for some `n ≥ 1`, so it has two
distinct eigenvalues, as otherwise `A` would be a scalar times a unipotent matrix of finite order,
hence scalar; its fixed points are its two eigenlines. -/
lemma ncard_fixedBy_eq_two (hh : IsOfFinOrder h) (h1 : h ≠ 1) :
    (fixedBy (ℙ ℂ (Fin 2 → ℂ)) h).ncard = 2 := by
  induction h using ProjGenLinGroup.induction_on with
  | mk g =>
    rcases hh.exists_pow_eq_one with ⟨n, hn, hgn⟩
    exact ncard_fixedBy_mk (fun hg ↦ h1 (mk_eq_one.mpr hg)) hn.ne' <| mk_eq_one.mp <|
      by rwa [map_pow]

/-- The ratio `a / d` of the diagonal entries of a matrix `(a b; c d)` representing an element of
`PGL₂(ℂ)`, which does not depend on the representative. On the stabiliser of the point `(1 : 0)` of
the projective line, the matrices are upper triangular and this is a homomorphism. -/
noncomputable def diagRatio : PGL(Fin 2, ℂ) → ℂ :=
  Quotient.lift (fun g : GL (Fin 2) ℂ ↦ g 0 0 / g 1 1) fun a b hab ↦ by
    rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      (QuotientGroup.leftRel_apply.mp hab) with ⟨u, hu⟩
    have hb : (b : Matrix (Fin 2) (Fin 2) ℂ) = a * scalar (Fin 2) u := by
      rw [hu, ← Units.val_mul, mul_inv_cancel_left]
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact (isUnits_det_units b).ne_zero <| by simpa using congrArg det hb
    simp only [hb, scalar_apply, mul_diagonal]
    exact (mul_div_mul_right _ _ hu0).symm

variable (g) in
lemma diagRatio_mk : diagRatio (mk g) = g 0 0 / g 1 1 :=
  rfl

lemma ne_zero_vecCons_one_zero : (![1, 0] : Fin 2 → ℂ) ≠ 0 := by
  simp

variable (g v) in
lemma smul_eq_mulVec : g • v = (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v :=
  rfl

lemma val_one_zero_eq_zero (hg : mk g • Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero =
    Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero) : g 1 0 = 0 := by
  rw [PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff'] at hg
  rcases hg with ⟨a, ha⟩
  simpa [smul_eq_mulVec, mulVec, dotProduct] using (congrFun ha 1).symm

lemma diagRatio_mul (hh₁ : h₁ • Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero =
    Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero)
    (hh₂ : h₂ • Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero =
      Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero) :
    diagRatio (h₁ * h₂) = diagRatio h₁ * diagRatio h₂ := by
  induction h₁ using ProjGenLinGroup.induction_on with
  | mk g₁ =>
    induction h₂ using ProjGenLinGroup.induction_on with
    | mk g₂ =>
      rw [← map_mul, diagRatio_mk, diagRatio_mk, diagRatio_mk, ← mul_div_mul_comm]
      simp [Matrix.mul_apply, val_one_zero_eq_zero hh₁, val_one_zero_eq_zero hh₂]

lemma eq_one_of_diagRatio_eq_one (hh : h • Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero =
    Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero) (hfin : IsOfFinOrder h)
    (h1 : diagRatio h = 1) : h = 1 := by
  induction h using ProjGenLinGroup.induction_on with
  | mk g =>
    have h10 : g 1 0 = 0 := val_one_zero_eq_zero hh
    rw [diagRatio_mk] at h1
    have h11 : g 1 1 ≠ 0 := fun h11 ↦ by simp [h11] at h1
    have h00 : g 0 0 = g 1 1 := (div_eq_one_iff_eq h11).mp h1
    have hμ : g 0 0 ≠ 0 := h00 ▸ h11
    rcases hfin.exists_pow_eq_one with ⟨n, hn, hgn⟩
    have hc : (g : Matrix (Fin 2) (Fin 2) ℂ) ^ n = ((g : Matrix (Fin 2) (Fin 2) ℂ) ^ n) 0 0 • 1 :=
      val_pow_eq_smul_one (mk_eq_one.mp <| (map_pow mk g n).trans hgn)
    have hN : ((g : Matrix (Fin 2) (Fin 2) ℂ) - g 0 0 • 1) *
        ((g : Matrix (Fin 2) (Fin 2) ℂ) - g 0 0 • 1) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h10, h00]
    have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = g 0 0 • 1 :=
      sub_eq_zero.mp <| eq_zero_of_pow_eq_smul_one hn.ne' hμ hN (by rwa [add_sub_cancel])
    exact mk_eq_one.mpr <| GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      ⟨g 0 0, by rw [scalar_apply, ← smul_one_eq_diagonal, ← hg]⟩

lemma isCyclic_of_smul_eq {K : Type*} [Group K] [Finite K] (φ : K →* PGL(Fin 2, ℂ))
    (hφ : Function.Injective φ) (hφx : ∀ k, φ k • Projectivization.mk ℂ ![1, 0]
      ne_zero_vecCons_one_zero = Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero) :
    IsCyclic K := by
  let ψ : K →* ℂ :=
    { toFun k := diagRatio (φ k)
      map_one' := by
        rw [map_one, ← mk_one, diagRatio_mk]
        simp
      map_mul' k₁ k₂ := by rw [map_mul, diagRatio_mul (hφx k₁) (hφx k₂)] }
  refine isCyclic_of_injective_ringHom ψ fun k₁ k₂ hk ↦ ?_
  have h1 : ψ (k₁⁻¹ * k₂) = 1 := by rw [map_mul, ← hk, ← map_mul, inv_mul_cancel, map_one]
  have h2 : φ (k₁⁻¹ * k₂) = 1 :=
    eq_one_of_diagRatio_eq_one (hφx _) (φ.isOfFinOrder (isOfFinOrder_of_finite _)) h1
  exact inv_mul_eq_one.mp <| (injective_iff_map_eq_one φ).mp hφ _ h2

variable (H : Subgroup PGL(Fin 2, ℂ)) [Finite H]

/-- **The stabiliser of a point of the projective line in a finite subgroup of `PGL₂(ℂ)` is
cyclic**: conjugating the point to `(1 : 0)`, the stabiliser becomes a finite group of upper
triangular matrices modulo scalars, on which the ratio of the diagonal entries is an injective
homomorphism to `ℂ×`. -/
lemma isCyclic_stabilizer (x : ℙ ℂ (Fin 2 → ℂ)) : IsCyclic (stabilizer H x) := by
  have : IsPretransitive (SpecialLinearGroup (Fin 2) ℂ) (ℙ ℂ (Fin 2 → ℂ)) :=
    isPretransitive_of_is_two_pretransitive
  rcases exists_smul_eq (SpecialLinearGroup (Fin 2) ℂ) x
    (Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero) with ⟨s, hs⟩
  have hc : mk s.toGL • x = Projectivization.mk ℂ ![1, 0] ne_zero_vecCons_one_zero := by
    rw [← hs]
    induction x using Projectivization.ind with
    | h v hv =>
      rw [PGL.mk_smul_mk, matrixSpecialLinearGroup_smul_def, smul_mk]
      rfl
  refine isCyclic_of_smul_eq ((MulAut.conj (mk s.toGL)).toMonoidHom.comp
    (H.subtype.comp (stabilizer H x).subtype)) ((MulAut.conj _).injective.comp
      (H.subtype_injective.comp (stabilizer H x).subtype_injective)) fun k ↦ ?_
  have hk : ((k : H) : PGL(Fin 2, ℂ)) • x = x := k.2
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype, mul_smul]
  rw [← hc, inv_smul_smul, hk]

/-- **A finite subgroup of `PGL₂(ℂ)` acts on the projective line with two fixed points**: every
nontrivial element has exactly two fixed points, and every point stabiliser is cyclic. -/
lemma hasTwoFixedPoints : HasTwoFixedPoints H (ℙ ℂ (Fin 2 → ℂ)) where
  ncard_fixedBy k hk := ncard_fixedBy_eq_two (H.subtype.isOfFinOrder (isOfFinOrder_of_finite k)) <|
    by simpa using hk
  isCyclic_stabilizer := isCyclic_stabilizer H

/-- **Classification of the finite subgroups of `PGL₂(ℂ)`**: every finite subgroup of `PGL₂(ℂ)` is
cyclic, dihedral of order `2n` with `n ≥ 2`, or isomorphic to the alternating group `A₄`, the
symmetric group `S₄` or the alternating group `A₅`. -/
lemma classification : IsCyclic H ∨ (∃ n, 2 ≤ n ∧ Nonempty (H ≃* DihedralGroup n)) ∨
    Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 5)) :=
  (hasTwoFixedPoints H).classification

end Matrix.ProjGenLinGroup
