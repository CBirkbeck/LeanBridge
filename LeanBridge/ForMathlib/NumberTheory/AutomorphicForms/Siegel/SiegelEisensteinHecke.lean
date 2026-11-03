import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonHecke
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonSiegelEisenstein

/-!
# The Siegel Eisenstein series are Hecke eigenforms

The Siegel Eisenstein series `ψ_k`, for even `k > 5`, is the series over `P(ℤ) \ Sp(4, ℤ)` of the
constant function, with `P` the Siegel parabolic subgroup. The Hecke monoid lies in the group
`GSp(4, ℚ)⁺`, which is the product `U Sp(4, ℤ)` of its upper triangular subgroup `U` and `Sp(4, ℤ)`,
and `q = (A, B; 0, D)` in `U` acts on the constant function by the factor `r(q)^e det(D)^{-k}`. So a
right translation permutes `P(ℤ) \ Sp(4, ℤ)` and multiplies the terms of the series by factors, and
the sum of these factors over the right cosets of a double coset does not depend on the term. This
gives `T_D ψ_k = C ψ_k` (LMFDB `mf.siegel.subspace.degree.two`), so that the line spanned by `ψ_k`
is stable under the Hecke operators.

## Main results

* `SiegelUpperHalfSpace.exists_sum_hasSum_eq_mul`: a series over `H \ A`, for a homomorphism
  `j : A → G` and a subgroup `U ≤ G` with `G = U j(A)` and `j⁻¹(U) = H`, under a family of right
  translations permuted by `j(A)`.
* `SiegelUpperHalfSpace.exists_heckeOperator_siegelEisensteinKJ`: `T_D ψ_k = C ψ_k`.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex Module MulAction SymplecticGroup DoubleCoset

open scoped TensorProduct

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

/-! ### Eisenstein type series and right translations -/

variable {A G : Type*} [Group A] [Group G] {j : A →* G} {H : Subgroup A} {U : Subgroup G}
    {c : G → ℂ}

variable (j H U) in
open scoped Classical in
/-- The class in `H \ A` of an element `y = q j(a)` of `G`, with `q ∈ U`. -/
private noncomputable def tau (y : G) : Quotient (QuotientGroup.rightRel H) :=
  if h : ∃ a : A, y * (j a)⁻¹ ∈ U then ⟦h.choose⟧ else ⟦1⟧

private lemma tau_eq (hU : ∀ a, j a ∈ U ↔ a ∈ H) {y : G} {a : A} (h : y * (j a)⁻¹ ∈ U) :
    tau j H U y = ⟦a⟧ := by
  have hex : ∃ a : A, y * (j a)⁻¹ ∈ U := ⟨a, h⟩
  rw [tau, dite_eq_left hex]
  refine Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)
  have h₁ : (y * (j hex.choose)⁻¹)⁻¹ * (y * (j a)⁻¹) ∈ U := mul_mem (inv_mem hex.choose_spec) h
  have e : (y * (j hex.choose)⁻¹)⁻¹ * (y * (j a)⁻¹) = j (hex.choose * a⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [e, hU] at h₁
  have h₂ : (hex.choose * a⁻¹)⁻¹ ∈ H := inv_mem h₁
  rwa [mul_inv_rev, inv_inv] at h₂

private lemma mul_inv_out_mem (hU : ∀ a, j a ∈ U ↔ a ∈ H) (hG : ∀ y : G, ∃ q ∈ U, ∃ a, y = q * j a)
    (y : G) : y * (j (tau j H U y).out)⁻¹ ∈ U := by
  rcases hG y with ⟨q, hq, a, rfl⟩
  have h₁ : q * j a * (j a)⁻¹ ∈ U := by
    simpa using hq
  rw [tau_eq hU h₁]
  have h₂ : a * (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out a)
  have h₃ : q * j a * (j (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out)⁻¹ =
      q * j (a * (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out⁻¹) := by
    rw [map_mul, map_inv, mul_assoc]
  rw [h₃]
  exact mul_mem hq ((hU _).mpr h₂)

variable (j H U) in
/-- The right translation by `W` on the classes in `H \ A`. -/
private noncomputable def transfer (W : G) (x : Quotient (QuotientGroup.rightRel H)) :
    Quotient (QuotientGroup.rightRel H) :=
  tau j H U (j x.out * W)

private lemma transfer_transfer (hU : ∀ a, j a ∈ U ↔ a ∈ H)
    (hG : ∀ y : G, ∃ q ∈ U, ∃ a, y = q * j a) (W : G) (x : Quotient (QuotientGroup.rightRel H)) :
    transfer j H U W⁻¹ (transfer j H U W x) = x := by
  have h₁ : (j x.out * W * (j (tau j H U (j x.out * W)).out)⁻¹)⁻¹ ∈ U :=
    inv_mem (mul_inv_out_mem hU hG (j x.out * W))
  have h₂ : (j x.out * W * (j (tau j H U (j x.out * W)).out)⁻¹)⁻¹ =
      j (transfer j H U W x).out * W⁻¹ * (j x.out)⁻¹ := by
    simp [transfer, mul_assoc]
  rw [h₂] at h₁
  rw [transfer, tau_eq hU h₁, Quotient.out_eq]

/-- The right translation by `W` as a permutation of the classes in `H \ A`. -/
private noncomputable def transferEquiv (hU : ∀ a, j a ∈ U ↔ a ∈ H)
    (hG : ∀ y : G, ∃ q ∈ U, ∃ a, y = q * j a) (W : G) :
    Equiv.Perm (Quotient (QuotientGroup.rightRel H)) where
  toFun := transfer j H U W⁻¹
  invFun := transfer j H U W
  left_inv x := by
    have h : transfer j H U W⁻¹⁻¹ (transfer j H U W⁻¹ x) = x := transfer_transfer hU hG W⁻¹ x
    rwa [inv_inv] at h
  right_inv := transfer_transfer hU hG W

variable (j H U c) in
/-- The value of `c` on the `U`-part of `w = j(a)⁻¹ q`. -/
private noncomputable def lam (w : G) : ℂ :=
  c (j (tau j H U w⁻¹).out * w)

private lemma lam_eq (hU : ∀ a, j a ∈ U ↔ a ∈ H) (hc₁ : ∀ a ∈ H, c (j a) = 1)
    (hc₂ : ∀ q₁ ∈ U, ∀ q₂ ∈ U, c (q₁ * q₂) = c q₁ * c q₂) {w : G} {a : A} (h : j a * w ∈ U) :
    lam j H U c w = c (j a * w) := by
  have h₁ : w⁻¹ * (j a)⁻¹ ∈ U := by
    have h₂ : (j a * w)⁻¹ ∈ U := inv_mem h
    rwa [mul_inv_rev] at h₂
  have h₂ : a * (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out a)
  have h₃ : (a * (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out⁻¹)⁻¹ ∈ H := inv_mem h₂
  have e : j (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out * w =
      j (a * (⟦a⟧ : Quotient (QuotientGroup.rightRel H)).out⁻¹)⁻¹ * (j a * w) := by
    simp
  rw [lam, tau_eq hU h₁, e, hc₂ _ ((hU _).mpr h₃) _ h, hc₁ _ h₃, one_mul]

private lemma lam_mul (hU : ∀ a, j a ∈ U ↔ a ∈ H) (hG : ∀ y : G, ∃ q ∈ U, ∃ a, y = q * j a)
    (hc₁ : ∀ a ∈ H, c (j a) = 1) (hc₂ : ∀ q₁ ∈ U, ∀ q₂ ∈ U, c (q₁ * q₂) = c q₁ * c q₂) (b : A)
    (w : G) : lam j H U c (j b * w) = lam j H U c w := by
  have h₁ : j (tau j H U w⁻¹).out * w ∈ U := by
    have h₂ : (w⁻¹ * (j (tau j H U w⁻¹).out)⁻¹)⁻¹ ∈ U := inv_mem (mul_inv_out_mem hU hG w⁻¹)
    rwa [mul_inv_rev, inv_inv, inv_inv] at h₂
  have h₂ : j ((tau j H U w⁻¹).out * b⁻¹) * (j b * w) = j (tau j H U w⁻¹).out * w := by
    simp
  rw [lam_eq hU hc₁ hc₂ (a := (tau j H U w⁻¹).out * b⁻¹) (by rwa [h₂]), h₂, lam]

/-- **A series over `H \ A`, under right translations**: let `j : A → G` be a homomorphism of groups
and `U ≤ G` a subgroup with `G = U j(A)` and `j⁻¹(U) = H`. Let `t : G → ℂ` satisfy
`t(q y) = c(q) t(y)` for `q ∈ U`, with a character `c` of `U` trivial on `j(H)`, and let `(W_i)` be
a finite family of elements of `G` whose right cosets `j(A) W_i` are permuted by `j(A)`. Then
`∑_i ∑_{x ∈ H \ A} t(j(x) W_i) = C ∑_{x ∈ H \ A} t(j(x))`, with a constant `C` independent of `t`:
for each `i`, right translation by `W_i` permutes `H \ A`, and multiplies `t` by a factor, which
only depends on the right coset of `W_i j(x)⁻¹`. -/
lemma exists_sum_hasSum_eq_mul (hU : ∀ a, j a ∈ U ↔ a ∈ H) (hG : ∀ y : G, ∃ q ∈ U, ∃ a, y = q * j a)
    (hc₁ : ∀ a ∈ H, c (j a) = 1) (hc₂ : ∀ q₁ ∈ U, ∀ q₂ ∈ U, c (q₁ * q₂) = c q₁ * c q₂) {ι : Type*}
    [Fintype ι] (W : ι → G) (hW : ∀ a : A, ∃ (σ : Equiv.Perm ι) (b : ι → A),
      ∀ i, W i * j a = j (b i) * W (σ i)) : ∃ C : ℂ, ∀ (t : G → ℂ) (S : ι → ℂ) (S₀ : ℂ),
      (∀ q ∈ U, ∀ y, t (q * y) = c q * t y) →
      (∀ i, HasSum (fun x : Quotient (QuotientGroup.rightRel H) ↦ t (j x.out * W i)) (S i)) →
      HasSum (fun x : Quotient (QuotientGroup.rightRel H) ↦ t (j x.out)) S₀ → ∑ i, S i =
        C * S₀ := by
  refine ⟨∑ i, lam j H U c (W i), fun t S S₀ ht hS hS₀ ↦ ?_⟩
  have hkey (i : ι) (x' : Quotient (QuotientGroup.rightRel H)) :
      j (transfer j H U (W i)⁻¹ x').out * W i * (j x'.out)⁻¹ ∈ U := by
    have h₁ : j (transfer j H U (W i)⁻¹ x').out * W i *
        (j (tau j H U (j (transfer j H U (W i)⁻¹ x').out * W i)).out)⁻¹ ∈ U :=
      mul_inv_out_mem hU hG (j (transfer j H U (W i)⁻¹ x').out * W i)
    have h₂ : tau j H U (j (transfer j H U (W i)⁻¹ x').out * W i) = x' := by
      have h₃ : transfer j H U (W i)⁻¹⁻¹ (transfer j H U (W i)⁻¹ x') = x' :=
        transfer_transfer hU hG (W i)⁻¹ x'
      rwa [inv_inv] at h₃
    rwa [h₂] at h₁
  have h₁ (i : ι) : HasSum (fun x' : Quotient (QuotientGroup.rightRel H) ↦
      c (j (transfer j H U (W i)⁻¹ x').out * W i * (j x'.out)⁻¹) * t (j x'.out)) (S i) := by
    refine ((transferEquiv hU hG (W i)).hasSum_iff.mpr (hS i)).congr_fun fun x' ↦ ?_
    have e : j (transfer j H U (W i)⁻¹ x').out * W i =
        j (transfer j H U (W i)⁻¹ x').out * W i * (j x'.out)⁻¹ * j x'.out := by
      group
    rw [← ht _ (hkey i x'), ← e]
    rfl
  have h₂ : ∀ x' : Quotient (QuotientGroup.rightRel H),
      ∑ i, c (j (transfer j H U (W i)⁻¹ x').out * W i * (j x'.out)⁻¹) = ∑ i, lam j H U c (W i) := by
    intro x'
    rcases hW x'.out⁻¹ with ⟨σ, b, hσ⟩
    rw [← Equiv.sum_comp σ fun i ↦ lam j H U c (W i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h₃ : j (transfer j H U (W i)⁻¹ x').out * (W i * (j x'.out)⁻¹) ∈ U := by
      rw [← mul_assoc]
      exact hkey i x'
    have h₄ : lam j H U c (W i * (j x'.out)⁻¹) =
        c (j (transfer j H U (W i)⁻¹ x').out * (W i * (j x'.out)⁻¹)) :=
      lam_eq hU hc₁ hc₂ h₃
    rw [← mul_assoc] at h₄
    rw [← h₄, ← map_inv, hσ, lam_mul hU hG hc₁ hc₂]
  have h₃ : HasSum (fun x' : Quotient (QuotientGroup.rightRel H) ↦
      ∑ i, c (j (transfer j H U (W i)⁻¹ x').out * W i * (j x'.out)⁻¹) * t (j x'.out)) (∑ i, S i) :=
    hasSum_sum fun i _ ↦ h₁ i
  simp only [← Finset.sum_mul, h₂] at h₃
  exact h₃.unique (hS₀.mul_left _)

/-! ### `GSp(4, ℚ)⁺` as a group, and its upper triangular subgroup -/

/-- `GSp(4, ℚ)⁺` as a subgroup of `GL(4, ℚ)`. -/
private def gspGroup : Subgroup GL₄ where
  toSubmonoid := gspPlusGL (Fin 2)
  inv_mem' {x} hx := by
    rcases hx with ⟨r, hr, h⟩
    refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
    have e₁ : ((x⁻¹ : GL₄) : M₄)ᵀ * (x : M₄)ᵀ = 1 := by
      rw [← transpose_mul, Units.mul_inv, transpose_one]
    have e₂ : (x : M₄) * ((x⁻¹ : GL₄) : M₄) = 1 :=
      Units.mul_inv x
    have h₁ :
        ((x⁻¹ : GL₄) : M₄)ᵀ * ((x : M₄)ᵀ * J (Fin 2) ℚ * x) * ((x⁻¹ : GL₄) : M₄) = J (Fin 2) ℚ := by
      have e₃ : ((x⁻¹ : GL₄) : M₄)ᵀ * ((x : M₄)ᵀ * J (Fin 2) ℚ * x) * ((x⁻¹ : GL₄) : M₄) =
          (((x⁻¹ : GL₄) : M₄)ᵀ * (x : M₄)ᵀ) * J (Fin 2) ℚ * ((x : M₄) * ((x⁻¹ : GL₄) : M₄)) := by
        simp only [Matrix.mul_assoc]
      rw [e₃, e₁, e₂, Matrix.one_mul, Matrix.mul_one]
    have h' : (x : M₄)ᵀ * J (Fin 2) ℚ * x = r • J (Fin 2) ℚ := h
    rw [h', Matrix.mul_smul, Matrix.smul_mul] at h₁
    exact (eq_inv_smul_iff₀ hr.ne').mpr h₁

variable {k : ℤ} (y y' : gspGroup) (a : symplecticGroup (Fin 2) ℤ)

/-- The element of the monoid `GSp(4, ℚ)⁺` of matrices given by an element of the group. -/
private def toMon : gspPlus (Fin 2) :=
  ⟨((y : GL₄) : M₄), y.2⟩

private lemma toMon_mul : toMon (y * y') = toMon y * toMon y' :=
  rfl

private lemma toBlocks₂₁_mul (X Y : M₄) :
    (X * Y).toBlocks₂₁ = X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁ := by
  ext i j
  simp [toBlocks₂₁, toBlocks₁₁, toBlocks₂₂, Matrix.mul_apply]

private lemma toBlocks₂₂_mul (X Y : M₄) :
    (X * Y).toBlocks₂₂ = X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  ext i j
  simp [toBlocks₂₁, toBlocks₁₂, toBlocks₂₂, Matrix.mul_apply]

/-- The subgroup of the upper triangular elements `(A, B; 0, D)` of `GSp(4, ℚ)⁺`. -/
private def gspUpper : Subgroup gspGroup where
  carrier := {y | ((y : GL₄) : M₄).toBlocks₂₁ = 0}
  mul_mem' {y y'} hy hy' := by
    have h₁ : ((y : GL₄) : M₄).toBlocks₂₁ = 0 := hy
    have h₂ : ((y' : GL₄) : M₄).toBlocks₂₁ = 0 := hy'
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul, toBlocks₂₁_mul, h₁, h₂,
      Matrix.zero_mul, Matrix.mul_zero, add_zero]
  one_mem' := by
    ext i j
    simp [toBlocks₂₁]
  inv_mem' {y} hy := by
    have h₁ : ((y : GL₄) : M₄).toBlocks₂₁ = 0 := hy
    have h₂ : (((y : GL₄)⁻¹ : GL₄) * ((y : GL₄) : M₄) : M₄).toBlocks₂₁ =
        (((y : GL₄)⁻¹ : GL₄) : M₄).toBlocks₂₁ * ((y : GL₄) : M₄).toBlocks₁₁ +
          (((y : GL₄)⁻¹ : GL₄) : M₄).toBlocks₂₂ * ((y : GL₄) : M₄).toBlocks₂₁ :=
      toBlocks₂₁_mul _ _
    have h₃ : ((1 : M₄)).toBlocks₂₁ = 0 := by
      ext i j
      simp [toBlocks₂₁]
    rw [Units.inv_mul, h₃, h₁, Matrix.mul_zero, add_zero] at h₂
    have hdet : ((y : GL₄) : M₄).det =
        ((y : GL₄) : M₄).toBlocks₁₁.det * ((y : GL₄) : M₄).toBlocks₂₂.det := by
      conv_lhs => rw [← fromBlocks_toBlocks ((y : GL₄) : M₄), h₁, det_fromBlocks_zero₂₁]
    have hunit : IsUnit ((y : GL₄) : M₄).toBlocks₁₁ := by
      rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      have h₄ : ((y : GL₄) : M₄).det = 0 := by
        rw [hdet, h, zero_mul]
      exact (((y : GL₄).isUnit.map (detMonoidHom)).ne_zero) h₄
    exact hunit.mul_left_eq_zero.mp h₂.symm

/-- The homomorphism from `Sp(4, ℤ)` to `GSp(4, ℚ)⁺`. -/
private def jSp : symplecticGroup (Fin 2) ℤ →* gspGroup :=
  (spToGL (Fin 2)).codRestrict gspGroup fun a ↦
    heckeMonoid_le_gspPlusGL (heckeGamma_le_heckeMonoid ⟨a, trivial, rfl⟩)

private lemma toMon_jSp : toMon (jSp a) = ofSp (SymplecticGroup.map (Int.castRingHom ℚ) a) :=
  rfl

private lemma coe_jSp_apply (x y : Fin 2 ⊕ Fin 2) : ((jSp a : GL₄) : M₄) x y = (a.1 x y : ℚ) :=
  rfl

private lemma jSp_mem_gspUpper_iff : jSp a ∈ gspUpper ↔ a ∈ siegelParabolic (Fin 2) ℤ := by
  constructor
  · intro h
    ext i x
    have h₁ : ((jSp a : GL₄) : M₄) (.inr i) (.inl x) = 0 :=
      congrFun (congrFun h i) x
    rw [coe_jSp_apply] at h₁
    exact_mod_cast h₁
  · intro h
    ext i x
    have h₁ : a.1 (.inr i) (.inl x) = 0 := congrFun (congrFun h i) x
    simp [toBlocks₂₁, coe_jSp_apply, h₁]

private lemma exists_gspUpper_mul : ∃ q ∈ gspUpper, ∃ a, y = q * jSp a := by
  generalize hr : multiplier (toMon y) = r
  have hr₀ : 0 < r := hr ▸ multiplier_pos _
  have hy : ((y : GL₄) : M₄)ᵀ * J (Fin 2) ℚ * ((y : GL₄) : M₄) = r • J (Fin 2) ℚ :=
    hr ▸ transpose_mul_J_mul (toMon y)
  generalize hΘ : (fromBlocks (r⁻¹ • 1) 0 0 1 : M₄) = Θ
  have hΘJ : Θᵀ * (J (Fin 2) ℚ * Θ) = r⁻¹ • J (Fin 2) ℚ := by
    rw [← hΘ]
    simp [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]
  have hM : Θ * ((y : GL₄) : M₄) ∈ symplecticGroup (Fin 2) ℚ := by
    rw [SymplecticGroup.mem_iff', transpose_mul]
    have e : ((y : GL₄) : M₄)ᵀ * Θᵀ * J (Fin 2) ℚ * (Θ * ((y : GL₄) : M₄)) =
        ((y : GL₄) : M₄)ᵀ * (Θᵀ * (J (Fin 2) ℚ * Θ)) * ((y : GL₄) : M₄) := by
      simp only [Matrix.mul_assoc]
    rw [e, hΘJ, Matrix.mul_smul, Matrix.smul_mul, hy, smul_smul, inv_mul_cancel₀ hr₀.ne', one_smul]
  rcases exists_mem_integral_inv_mul_mem_siegelParabolic
    (⟨_, hM⟩ : symplecticGroup (Fin 2) ℚ)⁻¹ with ⟨g, hg, hp⟩
  rcases hg with ⟨a₀, -, rfl⟩
  have hp' : ((SymplecticGroup.map (Int.castRingHom ℚ) a₀)⁻¹ *
      (⟨_, hM⟩ : symplecticGroup (Fin 2) ℚ)⁻¹)⁻¹ ∈ siegelParabolic (Fin 2) ℚ :=
    inv_mem hp
  rw [mul_inv_rev, inv_inv, inv_inv] at hp'
  refine ⟨y * jSp a₀, ?_, a₀⁻¹, by simp⟩
  have h₁ : (Θ * ((y : GL₄) : M₄) * ((jSp a₀ : GL₄) : M₄)).toBlocks₂₁ = 0 :=
    hp'
  rw [Matrix.mul_assoc, toBlocks₂₁_mul] at h₁
  have h₂ : Θ.toBlocks₂₁ = 0 := by
    rw [← hΘ, toBlocks_fromBlocks₂₁]
  have h₃ : Θ.toBlocks₂₂ = 1 := by
    rw [← hΘ, toBlocks_fromBlocks₂₂]
  rw [h₂, h₃, Matrix.zero_mul, zero_add, Matrix.one_mul] at h₁
  exact h₁

variable (k) in
/-- The factor `r(q)^e det(D)^{-k}` by which `q = (A, B; 0, D)` acts on the constant function of
weight `det^k`. -/
private noncomputable def cUpper : ℂ :=
  ((multiplier (toMon y) : ℚ) : ℂ) ^ slashExponent (rhoKJ k 0) *
    ((((y : GL₄) : M₄).toBlocks₂₂.det : ℚ) : ℂ) ^ (-k)

variable {a} in
private lemma cUpper_jSp (hk' : Even k) (ha : a ∈ siegelParabolic (Fin 2) ℤ) :
    cUpper k (jSp a) = 1 := by
  have h₁ : ((jSp a : GL₄) : M₄).toBlocks₂₂ = a.1.toBlocks₂₂.map (Int.castRingHom ℚ) := by
    ext x y
    rfl
  have h₂ : ((a.1.toBlocks₂₂.det : ℤ) : ℂ) ^ (-k) = 1 := by
    rcases Int.isUnit_iff.mp (isUnit_det_toBlocks₂₂ (⟨a, ha⟩ : siegelParabolic (Fin 2) ℤ)) with
      h | h <;> rw [h]
    · simp
    · simp [hk'.neg.neg_one_zpow]
  rw [cUpper, toMon_jSp, multiplier_ofSp, h₁, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simpa using h₂

variable {y} in
private lemma cUpper_mul (h₁ : y ∈ gspUpper) : cUpper k (y * y') = cUpper k y * cUpper k y' := by
  have h₁' : ((y : GL₄) : M₄).toBlocks₂₁ = 0 := h₁
  simp only [cUpper, toMon_mul, multiplier_mul, Subgroup.coe_mul, Units.val_mul, toBlocks₂₂_mul,
    h₁', Matrix.zero_mul, zero_add, det_mul, Rat.cast_mul, mul_zpow]
  ring1

/-! ### The Hecke operators on `ψ_k` -/

attribute [local instance] Fintype.ofFinite

variable {y} in
private lemma gspSlash_siegelSeed (hq : y ∈ gspUpper) :
    gspSlash (rhoKJ k 0) (toMon y) siegelSeed = cUpper k y • siegelSeed := by
  funext Z
  have hq' : ((y : GL₄) : M₄).toBlocks₂₁ = 0 := hq
  have hJ : ((gspDenomGL (toMon y) Z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((y : GL₄) : M₄).toBlocks₂₂.map (Rat.castHom ℂ) := by
    have e : (toMon y : M₄).toBlocks₂₁ = 0 := hq'
    rw [coe_gspDenomGL, gspDenom, e]
    ext x y
    simp
    rfl
  have hdet : (((gspDenomGL (toMon y) Z)⁻¹.det ^ k : ℂˣ) : ℂ) =
      ((((y : GL₄) : M₄).toBlocks₂₂.det : ℚ) : ℂ) ^ (-k) := by
    rw [Units.val_zpow_eq_zpow_val, map_inv, Units.val_inv_eq_inv_val,
      GeneralLinearGroup.val_det_apply, hJ, ← RingHom.mapMatrix_apply, ← RingHom.map_det, inv_zpow']
    rfl
  have e : rhoKJ k 0 (gspDenomGL (toMon y) Z)⁻¹ (siegelSeed (gspSmul (toMon y) Z)) =
      (((gspDenomGL (toMon y) Z)⁻¹.det ^ k : ℂˣ) : ℂ) •
        TauCeti.symPowerRep ℂ 2 0 (gspDenomGL (toMon y) Z)⁻¹ (siegelSeed (gspSmul (toMon y) Z)) :=
    rfl
  rw [gspSlash, e, symPowerRep_zero, hdet, smul_smul, cUpper]
  rfl

private lemma gspSlash_smul (β : gspPlus (Fin 2)) (z : ℂ)
    (f : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) :
    gspSlash (rhoKJ k 0) β (z • f) = z • gspSlash (rhoKJ k 0) β f := by
  ext τ
  simp [gspSlash, smul_comm z]

private lemma gspSlash_toMon_jSp_siegelSeed (Z : SiegelUpperHalfSpace (Fin 2)) :
    gspSlash (rhoKJ k 0) (toMon (jSp a)) siegelSeed Z =
      vectorSiegelEisensteinTerm (rhoKJ k 0) (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1) Z a := by
  rw [toMon_jSp, gspSlash_ofSp, map_algebraMap_map_intCast]
  rfl

private lemma hasSum_gspSlash_jSp_mul (hk : 5 < k) (β : gspPlus (Fin 2))
    (φ : Dual ℂ (Sym[ℂ]^0 (Fin 2 → ℂ))) (Z : SiegelUpperHalfSpace (Fin 2)) :
    HasSum (fun x : SiegelParabolicCosets (Fin 2) ↦
      φ (gspSlash (rhoKJ k 0) (toMon (jSp x.out) * β) siegelSeed Z))
        (φ (gspSlash (rhoKJ k 0) β (siegelEisensteinKJ k) Z)) := by
  have e (a : symplecticGroup (Fin 2) ℤ) :
      φ (gspSlash (rhoKJ k 0) (toMon (jSp a) * β) siegelSeed Z) =
        (φ ∘ₗ (((multiplier β : ℂ) ^ slashExponent (rhoKJ k 0)) • rhoKJ k 0 (gspDenomGL β Z)⁻¹))
          (vectorSiegelEisensteinTerm (rhoKJ k 0) (⨂ₛ[ℂ] _ : Fin 0, Pi.single 0 1)
            (gspSmul β Z) a) := by
    rw [gspSlash_mul, ← gspSlash_toMon_jSp_siegelSeed]
    rfl
  simp only [e]
  exact isVectorSiegelEisensteinSeries_siegelEisensteinKJ hk (gspSmul β Z)
    (φ ∘ₗ (((multiplier β : ℂ) ^ slashExponent (rhoKJ k 0)) • rhoKJ k 0 (gspDenomGL β Z)⁻¹))

/-- **The Siegel Eisenstein series `ψ_k` is an eigenform of the Hecke operators**, for even `k > 5`:
`T_D ψ_k = C ψ_k` for a constant `C`, as `ψ_k` is the series over `P(ℤ) \ Sp(4, ℤ)` of the constant
function, on which the upper triangular `q = (A, B; 0, D)` acts by the factor
`r(q)^e det(D)^{-k}`. -/
lemma exists_heckeOperator_siegelEisensteinKJ (hk : 5 < k) (hk' : Even k)
    (D : HeckeCoset (heckeMonoid (Fin 2)) (heckeGamma (Fin 2)) (heckeGamma (Fin 2))) : ∃ C : ℂ,
      ∀ F : slashInvariants (rhoKJ k 0), (F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) =
        siegelEisensteinKJ k →
        (heckeOperator (rhoKJ k 0) D F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^0 (Fin 2 → ℂ)) =
          C • siegelEisensteinKJ k := by
  let W (v : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) (D.out : GL₄)⁻¹) : gspGroup :=
    ⟨heckeRep D v, heckeMonoid_le_gspPlusGL (heckeRep D v).2⟩
  have hW (a : symplecticGroup (Fin 2) ℤ) :
      ∃ (σ : Equiv.Perm (DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) (D.out : GL₄)⁻¹))
        (b : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) (D.out : GL₄)⁻¹ →
          symplecticGroup (Fin 2) ℤ), ∀ v, W v * jSp a = jSp (b v) * W (σ v) := by
    have hγ : spToGL (Fin 2) a ∈ heckeGamma (Fin 2) := ⟨a, trivial, rfl⟩
    have h (v : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2)) (D.out : GL₄)⁻¹) :
        ∃ b, W v * jSp a = jSp b * W ((⟨_, hγ⟩ : heckeGamma (Fin 2))⁻¹ • v) := by
      rcases exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2) with
        ⟨γ₁, hγ₁, hsplit⟩
      have hmk : (QuotientGroup.mk ⟨(spToGL (Fin 2) a)⁻¹ * (v.out : GL₄),
          mul_mem (inv_mem hγ) v.out.2⟩ : DecompQuotient (heckeGamma (Fin 2)) (heckeGamma (Fin 2))
            (D.out : GL₄)⁻¹) = (⟨_, hγ⟩ : heckeGamma (Fin 2))⁻¹ • v :=
        Quotient.mk_smul_out _ (⟨_, hγ⟩ : heckeGamma (Fin 2))⁻¹ v
      have hprod : rightCosetRep D v * spToGL (Fin 2) a =
          γ₁ * rightCosetRep D ((⟨_, hγ⟩ : heckeGamma (Fin 2))⁻¹ • v) := by
        simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
      rcases hγ₁ with ⟨b, -, rfl⟩
      exact ⟨b, Subtype.ext hprod⟩
    choose b hb using h
    exact ⟨toPerm (⟨_, hγ⟩ : heckeGamma (Fin 2))⁻¹, b, hb⟩
  rcases exists_sum_hasSum_eq_mul (j := jSp) (H := siegelParabolic (Fin 2) ℤ) (U := gspUpper)
    (c := cUpper k) jSp_mem_gspUpper_iff exists_gspUpper_mul (fun a ha ↦ cUpper_jSp hk' ha)
    (fun q₁ h₁ q₂ _ ↦ cUpper_mul q₂ h₁) W hW with ⟨C, hC⟩
  refine ⟨C, fun F hF ↦ ?_⟩
  funext Z
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, sub_eq_zero, coe_heckeOperator, Finset.sum_apply, map_sum, Pi.smul_apply, map_smul,
    smul_eq_mul]
  refine hC (fun y ↦ φ (gspSlash (rhoKJ k 0) (toMon y) siegelSeed Z)) _ _ (fun q hq y ↦ ?_)
    (fun v ↦ ?_) ?_
  · rw [toMon_mul, gspSlash_mul, gspSlash_siegelSeed hq, gspSlash_smul, Pi.smul_apply, map_smul,
      smul_eq_mul]
  · rw [hF]
    exact hasSum_gspSlash_jSp_mul hk (toMon (W v)) φ Z
  · simp only [gspSlash_toMon_jSp_siegelSeed]
    exact isVectorSiegelEisensteinSeries_siegelEisensteinKJ hk Z φ

end SiegelUpperHalfSpace
