import LeanBridge.ForMathlib.NumberTheory.ModularForms.LowerUnipotent
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.EllipticInvariance
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.Fricke.Matrix

/-!
# The group-theoretic core of Weil's converse theorem

Let `f` be holomorphic on `ℍ`, with `f` and `g = f ∣[k] W_N` both `1`-periodic, `k > 0`, and let
`χ` be a Dirichlet character modulo `N`. For a prime `r ∤ N` and `γ = (a, b; N c, r) ∈ Γ₀(N)`, the
matrix identity `T(b / r) W_{N r²} = r γ W_N T(c / r)` shows that the difference
`f ∣ T(b / r) W_{N r²} - r ^ (k - 2) χ(r) g ∣ T(c / r)` is `r ^ (k - 2)` times
`(f ∣ γ - χ(r) f) ∣ W_N T(c / r)`, where `c ≡ -(b N)⁻¹` modulo `r`. The twisted functional
equation, in the form `HasTwistedTransformation`, says that this difference is orthogonal to every
nontrivial character of `b` modulo `r`, so it does not depend on `b`.

Take a second prime `r'` with `r r' = 1 + N v`, and `γ = (r', 1; N v, r)`, `γ₋ = (r', -1; -N v, r)`.
Comparing the differences of `γ` and `γ₋` at `r` with those of `γ⁻¹` and `γ₋⁻¹` at `r'`, through
the cocycle relation of the defect `f ∣ γ - χ(d) f`, shows that the slashed defect is invariant
under the matrix `M = ((1 - N v) / (r r'), -2 v / (r² r'); 2 N / r', (1 - N v) / (r r'))`. This
matrix has determinant `1` and trace `4 / (r r') - 2`, so for `r r' ≥ 5` it is elliptic of infinite
order, and the slashed defect vanishes. Thus `f ∣ γ = χ(d) f` when `d` is a large prime. By
Dirichlet's theorem on primes in arithmetic progressions every `γ ∈ Γ₀(N)` with `c ≠ 0` is such a
matrix times a power of `T = (1, 1; 0, 1)`, and `c = 0` follows from a product.

## Main definitions

* `ModularForm.nebentypusDefect`: the defect `f ∣ γ - χ(d) f`.
* `ModularForm.HasTwistedTransformation`: the twisted transformation law at a character modulo a
  prime.

## Main results

* `ModularForm.slash_eq_smul_of_hasTwistedTransformation`: the twisted transformation laws imply the
  nebentypus law on `Γ₀(N)`.
* `ModularForm.hasTwistedTransformation_of_nebentypus`: conversely, the nebentypus law implies the
  twisted transformation laws.

## References

* A. Weil, *Über die Bestimmung Dirichletscher Reihen durch Funktionalgleichungen*, Math. Ann. 168
  (1967), 149–156.
* D. Bump, *Automorphic Forms and Representations*, Theorem 1.5.1.
-/

open UpperHalfPlane CongruenceSubgroup Matrix SpecialLinearGroup GeneralLinearGroup TauCeti

open scoped ModularForm MatrixGroups Manifold

namespace ModularForm

variable {N r r' v : ℕ} (hv : (r' : ℤ) * r = 1 + N * v)

variable (N r r' v) in
/-- The matrix `(r', 1; N v, r)`, for `r r' = 1 + N v`. -/
private def gammaPlus : SL(2, ℤ) :=
  ⟨!![(r' : ℤ), 1; N * v, r], by rw [Matrix.det_fin_two_of]; linarith⟩

variable (N r r' v) in
/-- The matrix `(r', -1; -N v, r)`, for `r r' = 1 + N v`. -/
private def gammaMinus : SL(2, ℤ) :=
  ⟨!![(r' : ℤ), -1; -(N * v), r], by rw [Matrix.det_fin_two_of]; linarith⟩

variable (N r r' v) in
/-- The inverse `(r, -1; -N v, r')` of `(r', 1; N v, r)`. -/
private def deltaPlus : SL(2, ℤ) :=
  ⟨!![(r : ℤ), -1; -(N * v), r'], by rw [Matrix.det_fin_two_of]; linarith⟩

variable (N r r' v) in
/-- The inverse `(r, 1; N v, r')` of `(r', -1; -N v, r)`. -/
private def deltaMinus : SL(2, ℤ) :=
  ⟨!![(r : ℤ), 1; N * v, r'], by rw [Matrix.det_fin_two_of]; linarith⟩

private lemma gammaPlus_inv : (gammaPlus N r r' v hv)⁻¹ = deltaPlus N r r' v hv := by
  have h : !![(r' : ℤ), 1; N * v, r] * !![(r : ℤ), -1; -(N * v), r'] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  exact inv_eq_of_mul_eq_one_right (Subtype.ext h)

private lemma gammaMinus_inv : (gammaMinus N r r' v hv)⁻¹ = deltaMinus N r r' v hv := by
  have h : !![(r' : ℤ), -1; -(N * v), r] * !![(r : ℤ), 1; N * v, r'] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  exact inv_eq_of_mul_eq_one_right (Subtype.ext h)

private lemma cast_mul_eq (h : (r' : ℤ) * r = 1 + N * v) : (r' : ℝ) * r = 1 + N * v := by
  exact_mod_cast h

variable (N r) in
/-- The residue `v = -(x N)⁻¹` paired with `x` modulo `r`. -/
private noncomputable def pairedResidue (x : ZMod r) : ZMod r :=
  -(x * (N : ZMod r))⁻¹

variable (χ : DirichletCharacter ℂ N) (k : ℤ) (f : ℍ → ℂ)

/-- The **defect** `f ∣[k] γ - χ(d) f` of `f` from the nebentypus law of `χ` at `γ = (a, b; c, d)`:
`f` transforms under `γ` with `χ(d)` exactly when the defect vanishes. It is a cocycle on
`Γ₀(N)`. -/
noncomputable def nebentypusDefect (γ : SL(2, ℤ)) : ℍ → ℂ :=
  f ∣[k] γ - χ (γ 1 1 : ℤ) • f

variable {χ k f} {γ δ : SL(2, ℤ)} [Fact r.Prime] {c : ℤ} {R : ℕ}

lemma nebentypusDefect_mul (hγ : γ ∈ Gamma0 N) : nebentypusDefect χ k f (γ * δ) =
    nebentypusDefect χ k f γ ∣[k] δ + χ (γ 1 1 : ℤ) • nebentypusDefect χ k f δ := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  have hd : (((γ * δ) 1 1 : ℤ) : ZMod N) = (γ 1 1 : ℤ) * (δ 1 1 : ℤ) := by
    simp [Matrix.mul_apply, hc]
  simp only [nebentypusDefect, hd, map_mul, SlashAction.slash_mul]
  rw [sub_eq_add_neg (f ∣[k] γ), SlashAction.add_slash, SlashAction.neg_slash, SL_smul_slash]
  simp only [smul_sub, smul_smul]
  abel

variable (χ k f) in
lemma nebentypusDefect_one : nebentypusDefect χ k f 1 = 0 := by
  simp [nebentypusDefect]

lemma smul_nebentypusDefect_inv (hγ : γ ∈ Gamma0 N) :
    χ (γ 1 1 : ℤ) • nebentypusDefect χ k f γ⁻¹ = -(nebentypusDefect χ k f γ ∣[k] γ⁻¹) := by
  have h : nebentypusDefect χ k f (γ * γ⁻¹) =
      nebentypusDefect χ k f γ ∣[k] γ⁻¹ + χ (γ 1 1 : ℤ) • nebentypusDefect χ k f γ⁻¹ :=
    nebentypusDefect_mul hγ
  rw [mul_inv_cancel, nebentypusDefect_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma slash_upperRightHom_intCast (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f) (n : ℤ) :
    f ∣[k] upperRightHom (n : ℝ) = f := by
  have h : upperRightHom (n : ℝ) = (upperRightHom (1 : ℝ) : GL (Fin 2) ℝ) ^ n := by
    rw [← AddChar.map_zsmul_eq_zpow]
    simp
  rw [h]
  exact slash_zpow_eq_self_of_slash_eq k f hf₁ n

lemma slash_upperRightHom_add_intCast (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f) (n : ℤ) (x : ℝ) :
    f ∣[k] upperRightHom ((n : ℝ) + x) = f ∣[k] upperRightHom x := by
  rw [AddChar.map_add_eq_mul, SlashAction.slash_mul, slash_upperRightHom_intCast hf₁]

lemma slash_upperRightHom_val_div (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f) (x : ZMod r) {b : ℤ}
    (hb : (b : ZMod r) = x) :
    f ∣[k] upperRightHom ((x.val : ℝ) / r) = f ∣[k] upperRightHom ((b : ℝ) / r) := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hmod : (x.val : ℤ) ≡ b [ZMOD r] := by
    rw [← ZMod.intCast_eq_intCast_iff, ← hb]
    simp
  rcases hmod.dvd with ⟨n, hn⟩
  have hx : (b : ℝ) / r = (n : ℝ) + (x.val : ℝ) / r := by
    have hn' : (b : ℝ) - x.val = r * n := by exact_mod_cast hn
    field_simp
    linear_combination hn'
  rw [hx, slash_upperRightHom_add_intCast hf₁]

private lemma pairedResidue_pairedResidue (hN : (N : ZMod r) ≠ 0) (x : ZMod r) :
    pairedResidue N r (pairedResidue N r x) = x := by
  simp only [pairedResidue, neg_mul]
  field_simp

private lemma coe_mul_mul_eq_neg_one (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) :
    ((γ 0 1 : ℤ) : ZMod r) * N * c = -1 := by
  have hdet : (γ 0 0 : ℤ) * r - γ 0 1 * (N * c) = 1 := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
    rwa [Matrix.det_fin_two, hc, hd] at h1
  have h3 : (((γ 0 0 : ℤ) * r - γ 0 1 * (N * c) : ℤ) : ZMod r) = ((1 : ℤ) : ZMod r) :=
    congrArg (Int.cast : ℤ → ZMod r) hdet
  push_cast at h3
  rw [ZMod.natCast_self, mul_zero, zero_sub] at h3
  linear_combination -h3

private lemma coe_ne_zero_of_eq (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) :
    ((γ 0 1 : ℤ) : ZMod r) ≠ 0 := by
  intro h
  have h2 : ((γ 0 1 : ℤ) : ZMod r) * N * c = -1 := coe_mul_mul_eq_neg_one hc hd
  rw [h, zero_mul, zero_mul] at h2
  exact one_ne_zero (neg_eq_zero.mp h2.symm)

private lemma pairedResidue_eq (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) :
    pairedResidue N r (γ 0 1 : ℤ) = (c : ZMod r) := by
  have h2 : ((γ 0 1 : ℤ) : ZMod r) * N * c = -1 := coe_mul_mul_eq_neg_one hc hd
  rw [pairedResidue, inv_eq_of_mul_eq_one_right (b := -(c : ZMod r)) (by linear_combination -h2),
    neg_neg]

private lemma eq_of_sum_inv_smul_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E] {Ψ : ZMod r → E}
    (h : ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → ∑ x, ψ⁻¹ x • Ψ x = 0) {a b : ZMod r} (ha : a ≠ 0)
    (hb : b ≠ 0) : Ψ a = Ψ b := by
  have key :
      ∀ a : ZMod r, a ≠ 0 → (r.totient : ℂ) • Ψ a = ∑ x, (1 : DirichletCharacter ℂ r)⁻¹ x • Ψ x :=
    fun a ha ↦ by
      have h1 : ∑ ψ : DirichletCharacter ℂ r, ψ a • ∑ x, ψ⁻¹ x • Ψ x =
          ∑ x, (∑ ψ : DirichletCharacter ℂ r, ψ⁻¹ x * ψ a) • Ψ x := by
        simp only [Finset.smul_sum, Finset.sum_smul, smul_smul, mul_comm]
        exact Finset.sum_comm
      have h2 : ∀ x : ZMod r, (∑ ψ : DirichletCharacter ℂ r, ψ⁻¹ x * ψ a) =
          if x = a then (r.totient : ℂ) else 0 := fun x ↦ by
        rcases eq_or_ne x 0 with rfl | hx
        · simp [ha.symm, MulChar.map_zero]
        · simp only [MulChar.inv_apply']
          exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx.isUnit a
      have h3 : ∑ ψ : DirichletCharacter ℂ r, ψ a • ∑ x, ψ⁻¹ x • Ψ x =
          ∑ x, (1 : DirichletCharacter ℂ r)⁻¹ x • Ψ x := by
        rw [Finset.sum_eq_single 1 (fun ψ _ hψ ↦ by rw [h ψ hψ, smul_zero]) (by simp)]
        rw [MulChar.one_apply ha.isUnit, one_smul]
      rw [← h3, h1]
      simp [h2]
  have htot : (r.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Fact.out : r.Prime).pos).ne'
  exact smul_right_injective E htot ((key a ha).trans (key b hb).symm)

private lemma nebentypusDefect_T_zpow (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f) (n : ℤ) :
    nebentypusDefect χ k f (ModularGroup.T ^ n) = 0 := by
  have h1 : f ∣[k] (ModularGroup.T ^ n : SL(2, ℤ)) = f := by
    rw [SL_slash]
    exact (congrArg (f ∣[k] ·) (ModularGroup.mapGL_T_zpow_eq_upperRightHom n)).trans
      (slash_upperRightHom_intCast hf₁ n)
  have h2 : ((ModularGroup.T ^ n : SL(2, ℤ)) 1 1 : ℤ) = 1 := by
    simp [ModularGroup.coe_T_zpow]
  rw [nebentypusDefect, h1, h2]
  simp

variable [Fact r'.Prime]

private lemma weilM_det (h : (r' : ℤ) * r = 1 + N * v) :
    ((1 - N * v) / (r * r') * ((1 - N * v) / (r * r')) -
      -2 * v / (r ^ 2 * r') * (2 * N / r') : ℝ) = 1 := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have h1 : (r' : ℝ) * r = 1 + N * v := cast_mul_eq h
  field_simp
  have h2 : ((r : ℝ) * r') ^ 2 = (1 + N * v) ^ 2 := by rw [mul_comm, h1]
  linear_combination -h2

variable (N r r' v) in
/-- The matrix `(1/r, -v/(r r'); N, 1/r')`, of determinant `1`. -/
private noncomputable def weilA₁ : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![1 / r, -v / (r * r'); N, 1 / r'] <| by
    have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
    have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
    have h1 : (1 / r * (1 / r') - -v / (r * r') * N : ℝ) = 1 := by
      field_simp
      linear_combination -cast_mul_eq hv
    rw [Matrix.det_fin_two_of, h1]
    exact one_ne_zero

variable (N r r' v) in
/-- The matrix `(1/r, v/(r r'); -N, 1/r')`, of determinant `1`. -/
private noncomputable def weilA₂ : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![1 / r, v / (r * r'); -N, 1 / r'] <| by
    have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
    have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
    have h1 : (1 / r * (1 / r') - v / (r * r') * -N : ℝ) = 1 := by
      field_simp
      linear_combination -cast_mul_eq hv
    rw [Matrix.det_fin_two_of, h1]
    exact one_ne_zero

variable (N r r' v) in
/-- The elliptic matrix `((1 - N v)/(r r'), -2 v/(r² r'); 2 N / r', (1 - N v)/(r r'))`, of
determinant `1` and trace `2 (1 - N v)/(r r')`. -/
private noncomputable def weilM : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(1 - N * v) / (r * r'), -2 * v / (r ^ 2 * r'); 2 * N / r',
    (1 - N * v) / (r * r')] <| by
    rw [Matrix.det_fin_two_of, weilM_det hv]
    exact one_ne_zero

private lemma weilM_identity : weilM N r r' v hv * weilA₂ N r r' v hv = weilA₁ N r r' v hv := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have h1 : (r' : ℝ) * r = 1 + N * v := cast_mul_eq hv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weilA₁, weilA₂, weilM]
  all_goals field_simp
  · linear_combination -h1
  · linear_combination (v : ℝ) * h1
  · linear_combination -(N : ℝ) * h1
  · linear_combination -h1

private lemma det_weilM : (weilM N r r' v hv).det.val = 1 := by
  rw [val_det_apply]
  exact (Matrix.det_fin_two_of _ _ _ _).trans (weilM_det hv)

private lemma trace_ne_intCast (h₀ : (r' : ℤ) * r = 1 + N * v) (h5 : 5 ≤ r * r') (n : ℤ) :
    (2 * (1 - N * v) / (r * r') : ℚ) ≠ n := by
  intro h
  have hr : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have h1 : (r' : ℚ) * r = 1 + N * v := by exact_mod_cast h₀
  rw [div_eq_iff (mul_ne_zero hr hr')] at h
  have h2 : (n + 2) * ((r : ℤ) * r') = 4 := by
    have h3 : ((n + 2) * ((r : ℤ) * r') : ℚ) = 4 := by
      push_cast
      linear_combination -h + 2 * h1
    exact_mod_cast h3
  have h4 : (r : ℤ) * r' ≤ 4 := Int.le_of_dvd (by norm_num) ⟨n + 2, by linarith⟩
  have h5' : (5 : ℤ) ≤ (r : ℤ) * r' := by exact_mod_cast h5
  linarith

variable (γ) in
private lemma det_mapGL_mul_pos (A : GL (Fin 2) ℝ) (hA : 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det) :
    0 < ((mapGL ℝ γ * A : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have h1 : ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← val_det_apply, det_mapGL, Units.val_one]
  rwa [Units.val_mul, Matrix.det_mul, h1, one_mul]

variable [NeZero N]

variable (r) in
/-- The positive integer `r`, as a unit of `ℝ`. -/
private noncomputable def unitOf : ℝˣ :=
  Units.mk0 (r : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne r))

private lemma upperRightHom_mul_frickeGL_eq (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) :
    upperRightHom ((γ 0 1 : ℝ) / r) * frickeGL ℝ (N * r ^ 2) =
      scalar (Fin 2) (unitOf r) * mapGL ℝ γ * frickeGL ℝ N * upperRightHom ((c : ℝ) / r) := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hdet : (γ 0 0 : ℝ) * r - γ 0 1 * (N * c) = 1 := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
    rw [Matrix.det_fin_two, hc, hd] at h1
    exact_mod_cast h1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, unitOf, hc, hd, Matrix.natCast_apply]
  · field_simp
  · field_simp
    linear_combination hdet
  · ring1
  · field_simp
    ring1

variable (χ k f r) in
/-- The difference `f ∣ T(x/r) W_{N r²} - r ^ (k - 2) χ(r) (f ∣ W_N) ∣ T(v/r)`, for `x` modulo `r`
and `v = -(x N)⁻¹`, whose average against the characters modulo `r` is the twisted functional
equation of Weil's converse theorem. -/
private noncomputable def weilDifference (x : ZMod r) : ℍ → ℂ :=
  f ∣[k] (upperRightHom ((x.val : ℝ) / r) * frickeGL ℝ (N * r ^ 2)) -
    (((r : ℝ) : ℂ) ^ (k - 2) * χ r) •
      (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (((pairedResidue N r x).val : ℝ) / r)

private lemma det_frickeGL_mul_upperRightHom_pos (x : ℝ) :
    0 < ((frickeGL ℝ N * upperRightHom x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  simpa using hN

private lemma weilDifference_eq (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) : weilDifference r χ k f (γ 0 1 : ℤ) =
      ((r : ℝ) : ℂ) ^ (k - 2) • (nebentypusDefect χ k f γ ∣[k] (frickeGL ℝ N *
        upperRightHom ((c : ℝ) / r))) := by
  have h1 : f ∣[k] (upperRightHom ((((γ 0 1 : ℤ) : ZMod r).val : ℝ) / r) *
      frickeGL ℝ (N * r ^ 2)) = ((r : ℝ) : ℂ) ^ (k - 2) •
        (f ∣[k] γ) ∣[k] (frickeGL ℝ N * upperRightHom ((c : ℝ) / r)) := by
    rw [SlashAction.slash_mul, slash_upperRightHom_val_div hf₁ _ rfl, ← SlashAction.slash_mul,
      upperRightHom_mul_frickeGL_eq hc hd, mul_assoc, mul_assoc, SlashAction.slash_mul,
      slash_scalar,
      smul_slash_of_det_pos k (det_mapGL_mul_pos γ _ (det_frickeGL_mul_upperRightHom_pos _)),
      SlashAction.slash_mul k (mapGL ℝ γ) _ f]
    rfl
  have h2 : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom
      (((pairedResidue N r ((γ 0 1 : ℤ) : ZMod r)).val : ℝ) / r) =
        (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom ((c : ℝ) / r) :=
    slash_upperRightHom_val_div hg₁ _ (pairedResidue_eq hc hd).symm
  rw [weilDifference, h1, h2, nebentypusDefect, sub_eq_add_neg (f ∣[k] γ), SlashAction.add_slash,
    SlashAction.neg_slash, smul_slash_of_det_pos k (det_frickeGL_mul_upperRightHom_pos _),
    SlashAction.slash_mul k (frickeGL ℝ N) _ f, hd]
  simp only [smul_add, smul_neg, smul_smul, Int.cast_natCast, sub_eq_add_neg]

variable (χ k f) in
/-- The **twisted transformation law** of Weil's converse theorem for a character `ψ` modulo a prime
`r ∤ N`: the sum of `ψ⁻¹(u) f ∣ T(u/r) W_{N r²}` is `r ^ (k - 2) χ(r) ψ(-1) ψ(N)` times the sum of
`ψ(v) (f ∣ W_N) ∣ T(v/r)`. In terms of the twists `f_ψ` of `f` and `g_ψ̄` of `g = f ∣ W_N` by Gauss
sums it is the law `f_ψ ∣ W_{N r²} = C g_ψ̄`, which holds if `f` satisfies the nebentypus law of `χ`
and which Mellin inversion extracts from the functional equation of the twisted L-function. -/
def HasTwistedTransformation (ψ : DirichletCharacter ℂ r) : Prop :=
  ∑ u : ZMod r, ψ⁻¹ u • f ∣[k] (upperRightHom ((u.val : ℝ) / r) * frickeGL ℝ (N * r ^ 2)) =
    (((r : ℝ) : ℂ) ^ (k - 2) * χ r * ψ (-1) * ψ N) •
      ∑ v : ZMod r, ψ v • (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom ((v.val : ℝ) / r)

private lemma hasTwistedTransformation_iff (hN : (N : ZMod r) ≠ 0) {ψ : DirichletCharacter ℂ r} :
    HasTwistedTransformation χ k f ψ ↔ ∑ x, ψ⁻¹ x • weilDifference r χ k f x = 0 := by
  have hinv : Function.Involutive (pairedResidue N r) := pairedResidue_pairedResidue hN
  have hψ : ∀ x, ψ (-1) * ψ N * ψ (pairedResidue N r x) = ψ⁻¹ x := fun x ↦ by
    rw [MulChar.inv_apply', ← map_mul, ← map_mul]
    congr 1
    simp only [pairedResidue]
    field_simp
  have hre : ∑ v : ZMod r, ψ v • (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom ((v.val : ℝ) / r) =
      ∑ x, ψ (pairedResidue N r x) • (f ∣[k] frickeGL ℝ N) ∣[k]
        upperRightHom (((pairedResidue N r x).val : ℝ) / r) :=
    (Equiv.sum_comp hinv.toPerm fun v ↦ ψ v • (f ∣[k] frickeGL ℝ N) ∣[k]
      upperRightHom ((v.val : ℝ) / r)).symm
  have he : ∑ x, (((r : ℝ) : ℂ) ^ (k - 2) * χ r * ψ (-1) * ψ N) • ψ (pairedResidue N r x) •
      (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (((pairedResidue N r x).val : ℝ) / r) =
        ∑ x, ψ⁻¹ x • (((r : ℝ) : ℂ) ^ (k - 2) * χ r) • (f ∣[k] frickeGL ℝ N) ∣[k]
          upperRightHom (((pairedResidue N r x).val : ℝ) / r) := Finset.sum_congr rfl fun x _ ↦ by
    rw [smul_smul, smul_smul, ← hψ]
    congr 1
    ring1
  rw [HasTwistedTransformation, hre, Finset.smul_sum, he]
  simp only [weilDifference, smul_sub, Finset.sum_sub_distrib, sub_eq_zero]

private lemma weilDifference_eq_of_ne_zero (hN : (N : ZMod r) ≠ 0)
    (h : ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → HasTwistedTransformation χ k f ψ) {a b : ZMod r}
    (ha : a ≠ 0) (hb : b ≠ 0) : weilDifference r χ k f a = weilDifference r χ k f b :=
  eq_of_sum_inv_smul_eq_zero (fun ψ hψ ↦ (hasTwistedTransformation_iff hN).mp (h ψ hψ)) ha hb

/-- **The nebentypus law implies the twisted transformation law**: if `f` and `f ∣[k] W_N` are
`1`-periodic and `f` satisfies the nebentypus law of `χ` on `Γ₀(N)`, then
`HasTwistedTransformation χ k f ψ` holds for every character `ψ` modulo a prime `r ∤ N`. This is the
easy converse of `slash_eq_smul_of_hasTwistedTransformation`, and it confirms the constants there.
-/
lemma hasTwistedTransformation_of_nebentypus (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (hN : (N : ZMod r) ≠ 0) (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f)
    (ψ : DirichletCharacter ℂ r) : HasTwistedTransformation χ k f ψ := by
  refine (hasTwistedTransformation_iff hN).mpr (Finset.sum_eq_zero fun x _ ↦ ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp [MulChar.map_zero]
  have hb : ((x.val : ℤ) : ZMod r) = x := by simp
  have hprod : (((x.val : ℤ) * N : ℤ) : ZMod r) ≠ 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact mul_ne_zero hx hN
  have hcop : IsCoprime (r : ℤ) ((x.val : ℤ) * N) := by
    refine ((Nat.prime_iff_prime_int.mp (Fact.out : r.Prime)).coprime_iff_not_dvd).mpr fun hd ↦ ?_
    exact hprod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ r).mpr hd)
  rcases hcop with ⟨u, v, huv⟩
  let γ : SL(2, ℤ) := ⟨!![u, (x.val : ℤ); N * (-v), r], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hc : γ 1 0 = N * (-v) := rfl
  have hd : γ 1 1 = r := rfl
  have h01 : γ 0 1 = x.val := rfl
  have hγ : γ ∈ Gamma0 N := by
    rw [Gamma0_mem, hc]
    simp
  have h1 : weilDifference r χ k f (γ 0 1 : ℤ) = ((r : ℝ) : ℂ) ^ (k - 2) •
      (nebentypusDefect χ k f γ ∣[k] (frickeGL ℝ N * upperRightHom (((-v : ℤ) : ℝ) / r))) :=
    weilDifference_eq hf₁ hg₁ hc hd
  have h2 : nebentypusDefect χ k f γ = 0 := sub_eq_zero.mpr (hlaw γ hγ)
  rw [h2, SlashAction.zero_slash, smul_zero, h01, hb] at h1
  rw [h1, smul_zero]

private lemma defect_slash_eq (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (hN : (N : ZMod r) ≠ 0)
    (h : ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → HasTwistedTransformation χ k f ψ) {c' : ℤ}
    (hc : γ 1 0 = N * c) (hd : γ 1 1 = r) (hc' : δ 1 0 = N * c') (hd' : δ 1 1 = r) :
    nebentypusDefect χ k f γ ∣[k] (frickeGL ℝ N * upperRightHom ((c : ℝ) / r)) =
      nebentypusDefect χ k f δ ∣[k] (frickeGL ℝ N * upperRightHom ((c' : ℝ) / r)) := by
  have hr : (((r : ℝ) : ℂ) ^ (k - 2)) ≠ 0 :=
    zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne r)))
  refine smul_right_injective _ hr ?_
  simp only [← weilDifference_eq hf₁ hg₁ hc hd, ← weilDifference_eq hf₁ hg₁ hc' hd']
  exact weilDifference_eq_of_ne_zero hN h (coe_ne_zero_of_eq hc hd) (coe_ne_zero_of_eq hc' hd')

private lemma mapGL_mk_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (h : A.det = 1) (i j : Fin 2) :
    ((mapGL ℝ (⟨A, h⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) :=
  rfl

private lemma weilA₁_identity : (frickeGL ℝ N * upperRightHom ((v : ℝ) / r)) * weilA₁ N r r' v hv =
    mapGL ℝ (deltaPlus N r r' v hv) *
      (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r' : ℝ))) := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have h1 : (r' : ℝ) * r = 1 + N * v := cast_mul_eq hv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, weilA₁, deltaPlus, mapGL_mk_apply]
  all_goals field_simp
  · linear_combination h1
  · linear_combination -(N : ℝ) * h1
  · ring1

private lemma weilA₂_identity : (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r : ℝ))) *
    weilA₂ N r r' v hv = mapGL ℝ (deltaMinus N r r' v hv) *
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r')) := by
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have h1 : (r' : ℝ) * r = 1 + N * v := cast_mul_eq hv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, weilA₂, deltaMinus, mapGL_mk_apply]
  all_goals field_simp
  · linear_combination h1
  · linear_combination -(N : ℝ) * h1
  · ring1

variable (N r v) in
/-- The fixed point `i √(N v) / (N r)` of the elliptic matrix `weilM`. -/
private noncomputable def weilFixedPoint (hNv : 0 < N * v) : ℍ :=
  ⟨((Real.sqrt (N * v) / (N * r) : ℝ) : ℂ) * Complex.I, by
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hr : (0 : ℝ) < r := Nat.cast_pos.mpr (NeZero.pos r)
    have hs : 0 < Real.sqrt (N * v) := Real.sqrt_pos.mpr (by exact_mod_cast hNv)
    have hy : 0 < Real.sqrt (N * v) / (N * r) := div_pos hs (mul_pos hN hr)
    rw [Complex.mul_I_im, Complex.ofReal_re]
    exact hy⟩

private lemma weilM_entries_eq (hNv : 0 < N * v) : ((2 * N / r' : ℝ) : ℂ) *
    (weilFixedPoint N r v hNv : ℂ) ^ 2 = ((-2 * v / (r ^ 2 * r') : ℝ) : ℂ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hr' : (r' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r')
  have hs : ((Real.sqrt (N * v) : ℝ) : ℂ) ^ 2 = N * v := by
    have h1 : Real.sqrt (N * v) ^ 2 = N * v := Real.sq_sqrt (by positivity)
    exact_mod_cast congrArg (fun x : ℝ ↦ (x : ℂ)) h1
  have hz : (weilFixedPoint N r v hNv : ℂ) = (Real.sqrt (N * v) : ℝ) / (N * r) * Complex.I := by
    simp [weilFixedPoint]
  rw [hz, mul_pow, div_pow, hs, Complex.I_sq]
  push_cast
  field_simp

private lemma weilM_smul (hNv : 0 < N * v) :
    weilM N r r' v hv • weilFixedPoint N r v hNv = weilFixedPoint N r v hNv := by
  have hpos : 0 < (weilM N r r' v hv).det.val := det_weilM hv ▸ one_pos
  have hd : denom (weilM N r r' v hv) (weilFixedPoint N r v hNv) ≠ 0 := denom_ne_zero _ _
  refine UpperHalfPlane.ext ?_
  rw [coe_smul_of_det_pos hpos, div_eq_iff hd]
  have h1 : ((2 * N / r' : ℝ) : ℂ) * (weilFixedPoint N r v hNv : ℂ) ^ 2 =
      ((-2 * v / (r ^ 2 * r') : ℝ) : ℂ) := weilM_entries_eq hNv
  have e00 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 0 0 : ℝ) = (1 - N * v) / (r * r') := rfl
  have e01 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 0 1 : ℝ) = -2 * v / (r ^ 2 * r') := rfl
  have e10 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 1 0 : ℝ) = 2 * N / r' := rfl
  have e11 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 1 1 : ℝ) = (1 - N * v) / (r * r') := rfl
  simp only [num, denom, e00, e01, e10, e11]
  linear_combination -h1

private lemma denom_weilM_mul (hNv : 0 < N * v) :
    denom (weilM N r r' v hv) (weilFixedPoint N r v hNv) * (((2 * (1 - N * v) / (r * r') : ℚ) : ℂ) -
      denom (weilM N r r' v hv) (weilFixedPoint N r v hNv)) = 1 := by
  have h1 : ((2 * N / r' : ℝ) : ℂ) * (weilFixedPoint N r v hNv : ℂ) ^ 2 =
      ((-2 * v / (r ^ 2 * r') : ℝ) : ℂ) := weilM_entries_eq hNv
  have e10 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 1 0 : ℝ) = 2 * N / r' := rfl
  have e11 : ((weilM N r r' v hv : GL (Fin 2) ℝ) 1 1 : ℝ) = (1 - N * v) / (r * r') := rfl
  have e : ((2 * (1 - N * v) / (r * r') : ℚ) : ℂ) = 2 * (((1 - N * v) / (r * r') : ℝ) : ℂ) := by
    push_cast
    ring1
  have h2 : (((1 - N * v) / (r * r') : ℝ) : ℂ) * (((1 - N * v) / (r * r') : ℝ) : ℂ) -
      ((-2 * v / (r ^ 2 * r') : ℝ) : ℂ) * ((2 * N / r' : ℝ) : ℂ) = 1 := by
    exact_mod_cast weilM_det hv
  rw [e]
  simp only [denom, e10, e11]
  linear_combination h2 - ((2 * N / r' : ℝ) : ℂ) * h1

private lemma nebentypusDefect_gammaPlus_eq_zero (hf : MDiff f) (hk : 0 < k)
    (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (hN : (N : ZMod r) ≠ 0) (hN' : (N : ZMod r') ≠ 0)
    (h : ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 → HasTwistedTransformation χ k f ψ)
    (h' : ∀ ψ : DirichletCharacter ℂ r', ψ ≠ 1 → HasTwistedTransformation χ k f ψ)
    (h5 : 5 ≤ r * r') : nebentypusDefect χ k f (gammaPlus N r r' v hv) = 0 := by
  have hNv : 0 < N * v := by
    have h6 : (r' : ℤ) * r = ((r * r' : ℕ) : ℤ) := by push_cast; ring1
    have h7 : (5 : ℤ) ≤ ((r * r' : ℕ) : ℤ) := by exact_mod_cast h5
    have h8 : (0 : ℤ) < N * v := by linarith
    exact_mod_cast h8
  have hγ : gammaPlus N r r' v hv ∈ Gamma0 N := by
    rw [Gamma0_mem]
    have h1 : gammaPlus N r r' v hv 1 0 = N * (v : ℤ) := rfl
    simp [h1]
  have hγm : gammaMinus N r r' v hv ∈ Gamma0 N := by
    rw [Gamma0_mem]
    have h1 : gammaMinus N r r' v hv 1 0 = -(N * (v : ℤ)) := rfl
    simp [h1]
  have e₁ : nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r)) = nebentypusDefect χ k f
        (gammaMinus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r : ℝ))) := by
    simpa only [Int.cast_natCast] using defect_slash_eq (c := (v : ℤ)) (c' := -(v : ℤ)) hf₁ hg₁ hN h
      rfl rfl (by rw [mul_neg]; rfl) rfl
  have e₂ : nebentypusDefect χ k f (deltaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r' : ℝ))) = nebentypusDefect χ k f
        (deltaMinus N r r' v hv) ∣[k] (frickeGL ℝ N * upperRightHom ((v : ℝ) / r')) := by
    simpa only [Int.cast_natCast] using defect_slash_eq (c := -(v : ℤ)) (c' := (v : ℤ)) hf₁ hg₁ hN'
      h' (by rw [mul_neg]; rfl) rfl rfl rfl
  have i₁ : χ (r : ℤ) • nebentypusDefect χ k f (deltaPlus N r r' v hv) =
      -(nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k] deltaPlus N r r' v hv) := by
    rw [← gammaPlus_inv hv]
    exact smul_nebentypusDefect_inv hγ
  have i₂ : χ (r : ℤ) • nebentypusDefect χ k f (deltaMinus N r r' v hv) =
      -(nebentypusDefect χ k f (gammaMinus N r r' v hv) ∣[k] deltaMinus N r r' v hv) := by
    rw [← gammaMinus_inv hv]
    exact smul_nebentypusDefect_inv hγm
  have e₃ : (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k] deltaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r' : ℝ))) =
        (nebentypusDefect χ k f (gammaMinus N r r' v hv) ∣[k] deltaMinus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((v : ℝ) / r')) := by
    have h3 : (χ (r : ℤ) • nebentypusDefect χ k f (deltaPlus N r r' v hv)) ∣[k]
        (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r' : ℝ))) =
          (χ (r : ℤ) • nebentypusDefect χ k f (deltaMinus N r r' v hv)) ∣[k]
            (frickeGL ℝ N * upperRightHom ((v : ℝ) / r')) := by
      rw [smul_slash_of_det_pos k (det_frickeGL_mul_upperRightHom_pos _),
        smul_slash_of_det_pos k (det_frickeGL_mul_upperRightHom_pos _), e₂]
    rwa [i₁, i₂, SlashAction.neg_slash, SlashAction.neg_slash, neg_inj] at h3
  have hA₁ : (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))) ∣[k] weilA₁ N r r' v hv =
        (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k] deltaPlus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((-(v : ℤ) : ℤ) / (r' : ℝ))) := by
    rw [← SlashAction.slash_mul, weilA₁_identity, SlashAction.slash_mul]
    rfl
  have hA₂ : (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))) ∣[k] weilA₂ N r r' v hv =
        (nebentypusDefect χ k f (gammaMinus N r r' v hv) ∣[k] deltaMinus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((v : ℝ) / r')) := by
    rw [e₁, ← SlashAction.slash_mul, weilA₂_identity, SlashAction.slash_mul]
    rfl
  have hM : ((nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))) ∣[k] weilM N r r' v hv) ∣[k]
        weilA₂ N r r' v hv = (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))) ∣[k] weilA₂ N r r' v hv := by
    rw [← SlashAction.slash_mul (a := nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))), weilM_identity, hA₁, hA₂, e₃]
  have hinv : (nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
      (frickeGL ℝ N * upperRightHom ((v : ℝ) / r))) ∣[k] weilM N r r' v hv =
        nebentypusDefect χ k f (gammaPlus N r r' v hv) ∣[k]
          (frickeGL ℝ N * upperRightHom ((v : ℝ) / r)) := by
    simpa [← SlashAction.slash_mul] using congrArg (· ∣[k] (weilA₂ N r r' v hv)⁻¹) hM
  have hD : MDiff (nebentypusDefect χ k f (gammaPlus N r r' v hv)) :=
    (MDifferentiable.slash hf k _).sub (hf.const_smul _)
  exact (SlashAction.slash_eq_zero_iff _ _ _).mp <| eq_zero_of_slash_eq_of_smul_eq
    (MDifferentiable.slash hD k _) (det_weilM hv) (weilM_smul hv hNv)
    (fun n ↦ zpow_ne_one_of_mul_sub_eq_one (denom_weilM_mul hv hNv) (trace_ne_intCast hv h5)
      (by omega)) hinv

private lemma nebentypusDefect_eq_zero_of_prime (hf : MDiff f) (hk : 0 < k)
    (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (h : ∀ (r : ℕ) [Fact r.Prime], R < r → ¬r ∣ N → ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 →
      HasTwistedTransformation χ k f ψ) (hR : R < r) (hrN : ¬r ∣ N) (hc : γ 1 0 = N * c)
    (hd : γ 1 1 = r) : nebentypusDefect χ k f γ = 0 := by
  have hp : r.Prime := Fact.out
  have hNr : (N : ZMod r) ≠ 0 := fun h0 ↦ hrN ((ZMod.natCast_eq_zero_iff N r).mp h0)
  have hu : IsUnit (r : ZMod N) :=
    (ZMod.isUnit_iff_coprime r N).mpr (hp.coprime_iff_not_dvd.mpr hrN)
  rcases Nat.forall_exists_prime_gt_and_eq_mod (hu.unit⁻¹ : (ZMod N)ˣ).isUnit (max (max R 5) N) with
    ⟨r₁, hgt, hp₁, heq⟩
  have hfact : Fact r₁.Prime := ⟨hp₁⟩
  have hR₁ : R < r₁ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hgt
  have h5₁ : 5 < r₁ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hgt
  have hN₁ : N < r₁ := lt_of_le_of_lt (le_max_right _ _) hgt
  have hdvd : ¬r₁ ∣ N := Nat.not_dvd_of_pos_of_lt (NeZero.pos N) hN₁
  have hNr₁ : (N : ZMod r₁) ≠ 0 := fun h0 ↦ hdvd ((ZMod.natCast_eq_zero_iff N r₁).mp h0)
  have h1 : (r₁ : ZMod N) * r = 1 := by
    rw [heq]
    exact hu.unit.inv_mul
  have hle : 1 ≤ r₁ * r := Nat.mul_pos hp₁.pos hp.pos
  have hmod : ((r₁ * r : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, h1, Nat.cast_one]
  rcases (Nat.modEq_iff_dvd' hle).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hmod).symm with ⟨v, hv⟩
  have hv' : (r₁ : ℤ) * r = 1 + N * v := by
    have h2 : r₁ * r = 1 + N * v := by omega
    exact_mod_cast h2
  have h5 : 5 ≤ r * r₁ := h5₁.le.trans (Nat.le_mul_of_pos_left r₁ hp.pos)
  have hkey : nebentypusDefect χ k f (gammaPlus N r r₁ v hv') = 0 :=
    nebentypusDefect_gammaPlus_eq_zero hv' hf hk hf₁ hg₁ hNr hNr₁ (h r hR hrN) (h r₁ hR₁ hdvd) h5
  have he : nebentypusDefect χ k f γ ∣[k] (frickeGL ℝ N * upperRightHom ((c : ℝ) / r)) =
      nebentypusDefect χ k f (gammaPlus N r r₁ v hv') ∣[k]
        (frickeGL ℝ N * upperRightHom (((v : ℤ) : ℝ) / r)) :=
    defect_slash_eq hf₁ hg₁ hNr (h r hR hrN) hc hd rfl rfl
  rw [hkey, SlashAction.zero_slash] at he
  exact (SlashAction.slash_eq_zero_iff _ _ _).mp he

private lemma nebentypusDefect_eq_zero_of_ne_zero (hf : MDiff f) (hk : 0 < k)
    (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (h : ∀ (r : ℕ) [Fact r.Prime], R < r → ¬r ∣ N → ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 →
      HasTwistedTransformation χ k f ψ) (hγ : γ ∈ Gamma0 N) (hc : γ 1 0 ≠ 0) :
    nebentypusDefect χ k f γ = 0 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
    rwa [Matrix.det_fin_two] at h1
  have hcop : IsCoprime (γ 1 1 : ℤ) ((γ 1 0).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, IsCoprime.abs_right_iff]
    exact ⟨γ 0 0, -γ 0 1, by linear_combination hdet⟩
  rcases Nat.forall_exists_prime_gt_and_zmodEq (max R N) (Int.natAbs_ne_zero.mpr hc) hcop with
    ⟨p, hgt, hp, hmod⟩
  have hfact : Fact p.Prime := ⟨hp⟩
  have hR : R < p := lt_of_le_of_lt (le_max_left _ _) hgt
  have hN : N < p := lt_of_le_of_lt (le_max_right _ _) hgt
  have hdvd : ¬p ∣ N := Nat.not_dvd_of_pos_of_lt (NeZero.pos N) hN
  rcases Int.natAbs_dvd.mp hmod.dvd with ⟨m, hm⟩
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp hγ) with ⟨c₁, hc₁⟩
  have hc₂ : (γ * ModularGroup.T ^ (-m)) 1 0 = N * c₁ := by
    simp [Matrix.mul_apply, ModularGroup.coe_T_zpow, hc₁]
  have hd₂ : (γ * ModularGroup.T ^ (-m)) 1 1 = p := by
    simp [Matrix.mul_apply, ModularGroup.coe_T_zpow]
    linear_combination hm
  have h1 : nebentypusDefect χ k f (γ * ModularGroup.T ^ (-m)) = 0 :=
    nebentypusDefect_eq_zero_of_prime hf hk hf₁ hg₁ h hR hdvd hc₂ hd₂
  rw [nebentypusDefect_mul hγ, nebentypusDefect_T_zpow hf₁, smul_zero, add_zero] at h1
  exact (SlashAction.slash_eq_zero_iff _ _ _).mp h1

/-- **The transformation law in Weil's converse theorem.** Let `f` be holomorphic on the upper half
plane, with `f` and `g = f ∣[k] W_N` both `1`-periodic, `k > 0`, and let `χ` be a Dirichlet
character modulo `N`. If the twisted transformation law `HasTwistedTransformation χ k f ψ` holds
for every nontrivial character `ψ` modulo every prime `r > R` not dividing `N`, then
`f ∣[k] γ = χ(d) f` for every `γ = (a, b; c, d) ∈ Γ₀(N)`. -/
lemma slash_eq_smul_of_hasTwistedTransformation (hf : MDiff f) (hk : 0 < k)
    (hf₁ : f ∣[k] upperRightHom (1 : ℝ) = f)
    (hg₁ : (f ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = f ∣[k] frickeGL ℝ N)
    (h : ∀ (r : ℕ) [Fact r.Prime], R < r → ¬r ∣ N → ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 →
      HasTwistedTransformation χ k f ψ) (hγ : γ ∈ Gamma0 N) : f ∣[k] γ = χ (γ 1 1 : ℤ) • f := by
  refine sub_eq_zero.mp ?_
  rcases ne_or_eq (γ 1 0) 0 with hc | hc
  · exact nebentypusDefect_eq_zero_of_ne_zero hf hk hf₁ hg₁ h hγ hc
  have hL : lowerUnipotent N ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp [lowerUnipotent]
  have hL0 : lowerUnipotent N 1 0 ≠ 0 := by
    simpa [lowerUnipotent] using NeZero.ne N
  have hd : γ 1 1 ≠ 0 := fun hd ↦ by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ.det_coe
    rw [Matrix.det_fin_two, hd, hc] at h1
    simp at h1
  have hmul : (γ * lowerUnipotent N) 1 0 ≠ 0 := by
    have e : (γ * lowerUnipotent N) 1 0 =
        γ 1 0 * lowerUnipotent N 0 0 + γ 1 1 * lowerUnipotent N 1 0 := by
      simp [Matrix.mul_apply]
    rw [e, hc, zero_mul, zero_add]
    exact mul_ne_zero hd hL0
  have h2 : nebentypusDefect χ k f (γ * lowerUnipotent N) = 0 :=
    nebentypusDefect_eq_zero_of_ne_zero hf hk hf₁ hg₁ h (mul_mem hγ hL) hmul
  rw [nebentypusDefect_mul hγ, nebentypusDefect_eq_zero_of_ne_zero hf hk hf₁ hg₁ h hL hL0,
    smul_zero, add_zero] at h2
  exact (SlashAction.slash_eq_zero_iff _ _ _).mp h2

end ModularForm
