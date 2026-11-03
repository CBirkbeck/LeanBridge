import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.IntegralDomain
import LeanBridge.ForMathlib.GroupTheory.GroupAction.TwoFixedPoints
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Finite subgroups of `PGL₂(F)` of order prime to the characteristic

Let `F` be an algebraically closed field. A finite subgroup `H` of `PGL₂(F)` whose order is
invertible in `F` is cyclic, dihedral of order `2n` with `n ≥ 2`, or isomorphic to `A₄`, `S₄` or
`A₅` (`Matrix.ProjGenLinGroup.classification_of_natCard_ne_zero`). This is the classification of
the finite groups acting with two fixed points (`MulAction.HasTwoFixedPoints.classification`),
applied to the action of `H` on the projective line `ℙ¹(F)`, as for `F = ℂ`:

* a nontrivial element of `H` has exactly two fixed points: a matrix `A` representing it has `Aⁿ`
  scalar for an `n` invertible in `F`; if its characteristic polynomial had a double root `μ`, then
  `A = μ + N` with `N² = 0`, and `Aⁿ = μⁿ + n μⁿ⁻¹ N` scalar forces `N = 0`, so `A` would be scalar;
  so `A` has two distinct eigenvalues, and its fixed points are its two eigenlines;
* the stabiliser of a point is cyclic: conjugating the point to `(1 : 0)`, the stabiliser consists
  of upper triangular matrices modulo scalars, and the ratio of the diagonal entries is an injective
  homomorphism from it to `Fˣ`, whose finite subgroups are cyclic.

Dickson's classification of the subgroups of `GL₂(𝔽_p)` (`Matrix.GeneralLinearGroup`, in
`LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2Dickson`) rests on this for `F` an algebraic
closure of `𝔽_p`.

## Main definitions

* `Matrix.ProjGenLinGroup.diagonalRatio`: the ratio of the diagonal entries of a matrix representing
  an element of `PGL₂(F)`.

## Main results

* `Matrix.ProjGenLinGroup.ncard_fixedBy_eq_two_of_pow_eq_one`: a nontrivial element of `PGL₂(F)` of
  order invertible in `F` has exactly two fixed points on the projective line.
* `Matrix.ProjGenLinGroup.isCyclic_stabilizer_of_natCard_ne_zero`: point stabilisers in a finite
  subgroup of `PGL₂(F)` of order invertible in `F` are cyclic.
* `Matrix.ProjGenLinGroup.hasTwoFixedPoints_of_natCard_ne_zero`: such a subgroup acts on the
  projective line with two fixed points.
* `Matrix.ProjGenLinGroup.classification_of_natCard_ne_zero`: the classification of such subgroups.
-/

open Matrix MulAction Polynomial Projectivization Set

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Matrix.ProjGenLinGroup

variable {F : Type*} [Field F] {A N : Matrix (Fin 2) (Fin 2) F} {μ c : F} {v w : Fin 2 → F} {n : ℕ}
  {g : GL (Fin 2) F} {h h₁ h₂ : PGL(Fin 2, F)}

lemma eq_zero_of_pow_eq_smul_one_of_natCast_ne_zero (hn : (n : F) ≠ 0) (hμ : μ ≠ 0) (hN : N * N = 0)
    (hpow : (μ • 1 + N) ^ n = c • 1) : N = 0 := by
  have key : ∀ k : ℕ, (μ • (1 : Matrix (Fin 2) (Fin 2) F) + N) ^ (k + 1) = μ ^ (k + 1) • 1 +
      (((k : F) + 1) * μ ^ k) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hN]
      push_cast
      module
  rcases n with _ | k
  · exact absurd Nat.cast_zero hn
  rw [key] at hpow
  have ht : ((k : F) + 1) * μ ^ k ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn) (pow_ne_zero _ hμ)
  have hN' :
      N = ((((k : F) + 1) * μ ^ k)⁻¹ * (c - μ ^ (k + 1))) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_smul, sub_smul, ← hpow, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [hN', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at hN
  rw [hN', mul_self_eq_zero.mp ((smul_eq_zero.mp hN).resolve_right one_ne_zero), zero_smul]

variable (A μ) in
private lemma det_sub_smul_one : (A - μ • 1).det = μ * μ - A.trace * μ + A.det := by
  simp [det_fin_two, trace_fin_two]
  ring1

lemma exists_mulVec_eq_smul_of_field (hμ : μ * μ - A.trace * μ + A.det = 0) :
    ∃ v, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  rcases exists_mulVec_eq_zero_iff.mpr ((det_sub_smul_one A μ).trans hμ) with ⟨v, hv, hAv⟩
  exact ⟨v, hv, by rwa [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hAv⟩

private lemma mul_self_sub_trace_mul_add_det_eq_zero (hv : v ≠ 0) (hAv : A *ᵥ v = μ • v) :
    μ * μ - A.trace * μ + A.det = 0 :=
  (det_sub_smul_one A μ).symm.trans <| exists_mulVec_eq_zero_iff.mp
    ⟨v, hv, by rw [sub_mulVec, smul_mulVec, one_mulVec, hAv, sub_self]⟩

private lemma mk_eq_mk_of_mulVec_eq_smul (hA : A ≠ μ • 1) (hv : v ≠ 0) (hw : w ≠ 0)
    (hAv : A *ᵥ v = μ • v) (hAw : A *ᵥ w = μ • w) :
    Projectivization.mk F v hv = Projectivization.mk F w hw := by
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
  refine (Projectivization.mk_eq_mk_iff' F v w hv hw).mpr ?_
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
private lemma val_ne_smul_one (hg : g ∉ Subgroup.center (GL (Fin 2) F)) :
    (g : Matrix (Fin 2) (Fin 2) F) ≠ μ • 1 := fun hμ ↦ hg <|
  GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    ⟨μ, by rw [hμ, scalar_apply, smul_one_eq_diagonal]⟩

lemma val_pow_eq_smul_one_of_field (hgn : g ^ n ∈ Subgroup.center (GL (Fin 2) F)) :
    (g : Matrix (Fin 2) (Fin 2) F) ^ n = ((g : Matrix (Fin 2) (Fin 2) F) ^ n) 0 0 • 1 := by
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hgn with ⟨c, hc⟩
  rw [← Units.val_pow_eq_pow_val, ← hc, scalar_apply, smul_one_eq_diagonal, diagonal_apply_eq]

private lemma ncard_fixedBy_mk_of_ne (hg : g ∉ Subgroup.center (GL (Fin 2) F)) {μ₁ μ₂ : F}
    (hμ : μ₁ ≠ μ₂) (hsum : μ₁ + μ₂ = (g : Matrix (Fin 2) (Fin 2) F).trace)
    (hprod : μ₁ * μ₂ = (g : Matrix (Fin 2) (Fin 2) F).det) :
    (fixedBy (ℙ F (Fin 2 → F)) (mk g)).ncard = 2 := by
  rcases exists_mulVec_eq_smul_of_field (A := g) (μ := μ₁) (by rw [← hsum, ← hprod]; ring1) with
    ⟨v₁, hv₁, hAv₁⟩
  rcases exists_mulVec_eq_smul_of_field (A := g) (μ := μ₂) (by rw [← hsum, ← hprod]; ring1) with
    ⟨v₂, hv₂, hAv₂⟩
  have hfix : fixedBy (ℙ F (Fin 2 → F)) (mk g) =
      {Projectivization.mk F v₁ hv₁, Projectivization.mk F v₂ hv₂} := by
    ext x
    induction x using Projectivization.ind with
    | h w hw =>
      rw [mem_fixedBy, PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff', mem_insert_iff,
        mem_singleton_iff]
      constructor
      · rintro ⟨a, ha⟩
        have hroot : a * a - (g : Matrix (Fin 2) (Fin 2) F).trace * a +
            (g : Matrix (Fin 2) (Fin 2) F).det = 0 :=
          mul_self_sub_trace_mul_add_det_eq_zero hw ha.symm
        rw [← hsum, ← hprod] at hroot
        rcases mul_eq_zero.mp (by linear_combination hroot : (a - μ₁) * (a - μ₂) = 0) with h | h
        · rw [sub_eq_zero] at h
          subst h
          exact Or.inl <| mk_eq_mk_of_mulVec_eq_smul (val_ne_smul_one _ hg) hw hv₁ ha.symm hAv₁
        · rw [sub_eq_zero] at h
          subst h
          exact Or.inr <| mk_eq_mk_of_mulVec_eq_smul (val_ne_smul_one _ hg) hw hv₂ ha.symm hAv₂
      · rintro (h | h) <;> rcases (Projectivization.mk_eq_mk_iff' F _ _ hw _).mp h with ⟨b, rfl⟩
        · refine ⟨μ₁, ?_⟩
          rw [smul_comm μ₁ b v₁, ← hAv₁]
          exact (mulVec_smul _ b v₁).symm
        · refine ⟨μ₂, ?_⟩
          rw [smul_comm μ₂ b v₂, ← hAv₂]
          exact (mulVec_smul _ b v₂).symm
  rw [hfix, ncard_pair]
  intro h
  rcases (Projectivization.mk_eq_mk_iff' F _ _ hv₁ hv₂).mp h with ⟨b, rfl⟩
  rw [mulVec_smul, hAv₂, smul_comm] at hAv₁
  exact hμ (smul_left_injective F hv₁ hAv₁).symm

private lemma ncard_fixedBy_mk [IsAlgClosed F] (hg : g ∉ Subgroup.center (GL (Fin 2) F))
    (hn : (n : F) ≠ 0) (hgn : g ^ n ∈ Subgroup.center (GL (Fin 2) F)) :
    (fixedBy (ℙ F (Fin 2 → F)) (mk g)).ncard = 2 := by
  have hc : (g : Matrix (Fin 2) (Fin 2) F) ^ n = ((g : Matrix (Fin 2) (Fin 2) F) ^ n) 0 0 • 1 :=
    val_pow_eq_smul_one_of_field hgn
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (isUnits_det_units g).ne_zero
  rcases IsAlgClosed.exists_root (g : Matrix (Fin 2) (Fin 2) F).charpoly
      (by simp) with ⟨μ₁, hμ₁⟩
  have hμ₁' : μ₁ * μ₁ - (g : Matrix (Fin 2) (Fin 2) F).trace * μ₁ +
      (g : Matrix (Fin 2) (Fin 2) F).det = 0 := by
    rw [charpoly_fin_two] at hμ₁
    simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hμ₁
    linear_combination hμ₁
  by_cases hμ : μ₁ = (g : Matrix (Fin 2) (Fin 2) F).trace - μ₁
  · have hμ₀ : μ₁ ≠ 0 := fun hμ₀ ↦ hdet <| by
      rw [hμ₀] at hμ₁'
      simpa using hμ₁'
    have htr : (g : Matrix (Fin 2) (Fin 2) F).trace = 2 * μ₁ := by
      linear_combination -hμ
    have hdet' : (g : Matrix (Fin 2) (Fin 2) F).det = μ₁ * μ₁ := by
      rw [htr] at hμ₁'
      linear_combination hμ₁'
    have hN : ((g : Matrix (Fin 2) (Fin 2) F) - μ₁ • 1) *
        ((g : Matrix (Fin 2) (Fin 2) F) - μ₁ • 1) = 0 := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
      rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hdet', htr]
      module
    exact (val_ne_smul_one _ hg <| sub_eq_zero.mp <|
      eq_zero_of_pow_eq_smul_one_of_natCast_ne_zero hn hμ₀ hN (by rwa [add_sub_cancel])).elim
  · exact ncard_fixedBy_mk_of_ne hg (μ₁ := μ₁) (μ₂ := (g : Matrix (Fin 2) (Fin 2) F).trace - μ₁) hμ
      (by ring1) (by linear_combination -hμ₁')

/-- **A nontrivial element of `PGL₂(F)` of order invertible in the algebraically closed field `F`
has exactly two fixed points on the projective line**: a matrix `A` representing it has `Aⁿ` scalar
with `n` invertible, so it has two distinct eigenvalues, as otherwise `A` would be a scalar times a
unipotent matrix, hence scalar; its fixed points are its two eigenlines. -/
lemma ncard_fixedBy_eq_two_of_pow_eq_one [IsAlgClosed F] (hn : (n : F) ≠ 0) (hh : h ^ n = 1)
    (h1 : h ≠ 1) : (fixedBy (ℙ F (Fin 2 → F)) h).ncard = 2 := by
  induction h using ProjGenLinGroup.induction_on with
  | mk g =>
    exact ncard_fixedBy_mk (fun hg ↦ h1 (mk_eq_one.mpr hg)) hn <| mk_eq_one.mp <|
      by rwa [map_pow]

/-- The ratio `a / d` of the diagonal entries of a matrix `(a b; c d)` representing an element of
`PGL₂(F)`, which does not depend on the representative. On the stabiliser of the point `(1 : 0)` of
the projective line, the matrices are upper triangular and this is a homomorphism. -/
noncomputable def diagonalRatio : PGL(Fin 2, F) → F :=
  Quotient.lift (fun g : GL (Fin 2) F ↦ g 0 0 / g 1 1) fun a b hab ↦ by
    rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      (QuotientGroup.leftRel_apply.mp hab) with ⟨u, hu⟩
    have hb : (b : Matrix (Fin 2) (Fin 2) F) = a * scalar (Fin 2) u := by
      rw [hu, ← Units.val_mul, mul_inv_cancel_left]
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact (isUnits_det_units b).ne_zero <| by simpa using congrArg det hb
    simp only [hb, scalar_apply, mul_diagonal]
    exact (mul_div_mul_right _ _ hu0).symm

variable (g) in
private lemma diagonalRatio_mk : diagonalRatio (mk g) = g 0 0 / g 1 1 :=
  rfl

variable (F) in
/-- The point `(1 : 0)` of the projective line. -/
private noncomputable def basePoint : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![1, 0] (by simp)

variable (g v) in
private lemma smul_eq_mulVec : g • v = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v :=
  rfl

private lemma val_one_zero_eq_zero (hg : mk g • basePoint F = basePoint F) : g 1 0 = 0 := by
  rw [basePoint, PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff'] at hg
  rcases hg with ⟨a, ha⟩
  simpa [smul_eq_mulVec, mulVec, dotProduct] using (congrFun ha 1).symm

private lemma diagonalRatio_mul (hh₁ : h₁ • basePoint F = basePoint F)
    (hh₂ : h₂ • basePoint F = basePoint F) :
    diagonalRatio (h₁ * h₂) = diagonalRatio h₁ * diagonalRatio h₂ := by
  induction h₁ using ProjGenLinGroup.induction_on with
  | mk g₁ =>
    induction h₂ using ProjGenLinGroup.induction_on with
    | mk g₂ =>
      rw [← map_mul, diagonalRatio_mk, diagonalRatio_mk, diagonalRatio_mk, ← mul_div_mul_comm]
      simp [Matrix.mul_apply, val_one_zero_eq_zero hh₁, val_one_zero_eq_zero hh₂]

private lemma eq_one_of_diagonalRatio_eq_one (hh : h • basePoint F = basePoint F) (hn : (n : F) ≠ 0)
    (hfin : h ^ n = 1) (h1 : diagonalRatio h = 1) : h = 1 := by
  induction h using ProjGenLinGroup.induction_on with
  | mk g =>
    have h10 : g 1 0 = 0 := val_one_zero_eq_zero hh
    rw [diagonalRatio_mk] at h1
    have h11 : g 1 1 ≠ 0 := fun h11 ↦ by simp [h11] at h1
    have h00 : g 0 0 = g 1 1 := (div_eq_one_iff_eq h11).mp h1
    have hμ : g 0 0 ≠ 0 := h00 ▸ h11
    have hc : (g : Matrix (Fin 2) (Fin 2) F) ^ n = ((g : Matrix (Fin 2) (Fin 2) F) ^ n) 0 0 • 1 :=
      val_pow_eq_smul_one_of_field (mk_eq_one.mp <| (map_pow mk g n).trans hfin)
    have hN : ((g : Matrix (Fin 2) (Fin 2) F) - g 0 0 • 1) *
        ((g : Matrix (Fin 2) (Fin 2) F) - g 0 0 • 1) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h10, h00]
    have hg : (g : Matrix (Fin 2) (Fin 2) F) = g 0 0 • 1 :=
      sub_eq_zero.mp <|
        eq_zero_of_pow_eq_smul_one_of_natCast_ne_zero hn hμ hN (by rwa [add_sub_cancel])
    exact mk_eq_one.mpr <| GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      ⟨g 0 0, by rw [scalar_apply, ← smul_one_eq_diagonal, ← hg]⟩

private lemma isCyclic_of_smul_eq {K : Type*} [Group K] [Finite K] (φ : K →* PGL(Fin 2, F))
    (hφ : Function.Injective φ) (hn : (n : F) ≠ 0) (hpow : ∀ k : K, k ^ n = 1)
    (hφx : ∀ k, φ k • basePoint F = basePoint F) : IsCyclic K := by
  let ψ : K →* F :=
    { toFun k := diagonalRatio (φ k)
      map_one' := by
        rw [map_one, ← mk_one, diagonalRatio_mk]
        simp
      map_mul' k₁ k₂ := by rw [map_mul, diagonalRatio_mul (hφx k₁) (hφx k₂)] }
  refine isCyclic_of_injective_ringHom ψ fun k₁ k₂ hk ↦ ?_
  have h1 : ψ (k₁⁻¹ * k₂) = 1 := by
    rw [map_mul, ← hk, ← map_mul, inv_mul_cancel, map_one]
  have h2 : φ (k₁⁻¹ * k₂) = 1 :=
    eq_one_of_diagonalRatio_eq_one (hφx _) hn (by rw [← map_pow, hpow, map_one]) h1
  exact inv_mul_eq_one.mp <| (injective_iff_map_eq_one φ).mp hφ _ h2

variable (H : Subgroup PGL(Fin 2, F)) [Finite H]

/-- **The stabiliser of a point of the projective line in a finite subgroup of `PGL₂(F)` of order
invertible in `F` is cyclic**: conjugating the point to `(1 : 0)`, the stabiliser becomes a finite
group of upper triangular matrices modulo scalars, on which the ratio of the diagonal entries is an
injective homomorphism to `Fˣ`. -/
lemma isCyclic_stabilizer_of_natCard_ne_zero (hH : (Nat.card H : F) ≠ 0) (x : ℙ F (Fin 2 → F)) :
    IsCyclic (stabilizer H x) := by
  rcases exists_smul_eq (SpecialLinearGroup (Fin 2) F) x (basePoint F) with ⟨s, hs⟩
  have hc : mk s.toGL • x = basePoint F := by
    rw [← hs]
    induction x using Projectivization.ind with
    | h v hv =>
      rw [PGL.mk_smul_mk, matrixSpecialLinearGroup_smul_def, smul_mk]
      rfl
  refine isCyclic_of_smul_eq ((MulAut.conj (mk s.toGL)).toMonoidHom.comp
    (H.subtype.comp (stabilizer H x).subtype)) ((MulAut.conj _).injective.comp
      (H.subtype_injective.comp (stabilizer H x).subtype_injective)) hH (fun k ↦ ?_) fun k ↦ ?_
  · have h₁ : (k : H) ^ Nat.card H = 1 := pow_card_eq_one'
    exact Subtype.ext <| (Subgroup.coe_pow _ k _).trans h₁
  · have hk : ((k : H) : PGL(Fin 2, F)) • x = x := k.2
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, mul_smul]
    rw [← hc, inv_smul_smul, hk]

/-- **A finite subgroup of `PGL₂(F)` of order invertible in the algebraically closed field `F` acts
on the projective line with two fixed points**: every nontrivial element has exactly two fixed
points, and every point stabiliser is cyclic. -/
lemma hasTwoFixedPoints_of_natCard_ne_zero [IsAlgClosed F] (hH : (Nat.card H : F) ≠ 0) :
    HasTwoFixedPoints H (ℙ F (Fin 2 → F)) where
  ncard_fixedBy k hk := by
    have h₁ : k ^ Nat.card H = 1 := pow_card_eq_one'
    exact ncard_fixedBy_eq_two_of_pow_eq_one hH (congrArg Subtype.val h₁) <| by simpa using hk
  isCyclic_stabilizer := isCyclic_stabilizer_of_natCard_ne_zero H hH

/-- **Classification of the finite subgroups of `PGL₂(F)` of order invertible in the algebraically
closed field `F`**: such a subgroup is cyclic, dihedral of order `2n` with `n ≥ 2`, or isomorphic to
the alternating group `A₄`, the symmetric group `S₄` or the alternating group `A₅`. -/
lemma classification_of_natCard_ne_zero [IsAlgClosed F] (hH : (Nat.card H : F) ≠ 0) :
    IsCyclic H ∨ (∃ n, 2 ≤ n ∧ Nonempty (H ≃* DihedralGroup n)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 4)) ∨ Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (H ≃* alternatingGroup (Fin 5)) :=
  (hasTwoFixedPoints_of_natCard_ne_zero H hH).classification

end Matrix.ProjGenLinGroup
