import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ScaledLattice
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.WhittakerHecke

/-!
# Cuspidal functions on hyperbolic 3-space

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`. The definition
of a cusp form (`IsBianchiCuspidal`) refers to the level through the lattices of translations of the
cusps. For the operators which change the level, such as the traces and the level raising, it is
better to separate the local conditions from the invariance. A **cuspidal function** of weight `k`
(`IsBianchiCuspFunction`) is a function `F : ℋ₃ → ℂ^{k+1}` which is real analytic, harmonic and of
moderate growth at the cusps, such that for each `g ∈ SL₂(K)`, the function `F ∣_k g` is periodic
for some lattice `σ(t𝒪_K)` with vanishing mean. For even `k`, the cuspidal functions form a complex
vector space (`IsBianchiCuspFunction.add`, `IsBianchiCuspFunction.const_smul`) stable under the
slash operators of `GL₂(K)` (`IsBianchiCuspFunction.slash`), since `αg = g't` with `g' ∈ SL₂(K)` and
`t = (1, b; 0, u)` upper triangular, and `F ∣_k t` is an affine change of variables, by a constant
matrix.

## Main definitions

* `HyperbolicThreeSpace.bianchiGLSlash`: the slash operator of `α ∈ GL₂(K)`.
* `HyperbolicThreeSpace.bianchiCuspSection`: the function `x ↦ (F ∣_k g)(x, y)`.
* `HyperbolicThreeSpace.IsBianchiCuspFunction`: cuspidal functions.
* `HyperbolicThreeSpace.HasVanishingMean`: periodic functions with vanishing means.

## Main results

* `HyperbolicThreeSpace.IsSLRepresentative.eq_or_eq_neg`: two representatives differ by a sign.
* `HyperbolicThreeSpace.bianchiSlash_eq_of_isSLRepresentative`: in even weight, the slash operator
  of a matrix does not depend on its representative.
* `HyperbolicThreeSpace.bianchiGLSlash_mul`: in even weight, the slash operators of `GL₂(K)` form a
  right action.
* `HyperbolicThreeSpace.bianchiGLSlash_of_eq_smul_one`: scalar matrices act trivially.
* `HyperbolicThreeSpace.mem_bianchiSlashInvariants_iff`: invariance in even weight.
* `HyperbolicThreeSpace.extend_bianchiGLSlash_heckeUpper`: the slash operator of `(1, b; 0, u)`.
* `HyperbolicThreeSpace.isBianchiCuspFunction_zero`,
  `HyperbolicThreeSpace.IsBianchiCuspFunction.add`,
  `HyperbolicThreeSpace.IsBianchiCuspFunction.sum`,
  `HyperbolicThreeSpace.IsBianchiCuspFunction.const_smul`,
  `HyperbolicThreeSpace.IsBianchiCuspFunction.slash`: the closure properties of cuspidal functions.
* `HyperbolicThreeSpace.exists_eq_toGL_mul_heckeUpper`: a matrix of `GL₂(K)` is the product of a
  matrix of `SL₂(K)` and of an upper triangular matrix.
* `HyperbolicThreeSpace.HasVanishingMean.bianchiGLSlash_heckeUpper`: the slash operator of an upper
  triangular matrix preserves the vanishing of the means.
-/

open Complex Matrix MeasureTheory Module NumberField HilbertModularGroup

open scoped ComplexConjugate MatrixGroups nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ} {α β : GL (Fin 2) K} {M M' : SL(2, ℂ)}
  {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {p : ℂ × ℝ} (g : SL(2, K)) (x : ℂ) {y : ℝ} (c : ℂ)
  (u : Kˣ) (b : K)

/-- **Two representatives of a matrix differ by a sign**: if `M, M' ∈ SL(2, ℂ)` both represent
`α ∈ GL₂(K)`, then `M' = ±M`. -/
lemma IsSLRepresentative.eq_or_eq_neg (hM : IsSLRepresentative σ α M)
    (hM' : IsSLRepresentative σ α M') : M' = M ∨ M' = -M := by
  rcases hM with ⟨s, hs⟩
  rcases hM' with ⟨t, ht⟩
  have hs₀ : s ≠ 0 := ne_zero_of_coe_eq_inv_smul hs
  have ht₀ : t ≠ 0 := ne_zero_of_coe_eq_inv_smul ht
  have h₁ : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := M.det_coe
  have h₂ : (M' : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := M'.det_coe
  rw [hs, det_smul, Fintype.card_fin, inv_pow, inv_mul_eq_div,
    div_eq_one_iff_eq (pow_ne_zero 2 hs₀)] at h₁
  rw [ht, det_smul, Fintype.card_fin, inv_pow, inv_mul_eq_div,
    div_eq_one_iff_eq (pow_ne_zero 2 ht₀)] at h₂
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h₂.symm.trans h₁) with rfl | rfl
  · exact Or.inl (Subtype.ext (ht.trans hs.symm))
  · refine Or.inr (Subtype.ext ?_)
    rw [SpecialLinearGroup.coe_neg, ht, hs, inv_neg, neg_smul]

/-- **In even weight, the slash operator of a matrix does not depend on its representative.** -/
lemma bianchiSlash_eq_of_isSLRepresentative (hk : Even k) (hM : IsSLRepresentative σ α M)
    (hM' : IsSLRepresentative σ α M') : bianchiSlash k M' F = bianchiSlash k M F := by
  rcases hM.eq_or_eq_neg hM' with rfl | rfl
  · rfl
  · rw [bianchiSlash_neg, hk.neg_one_pow, one_smul]

variable (σ k α F) in
/-- The **slash operator** `F ↦ F ∣_k α` of `α ∈ GL₂(K)`, through the chosen representative of `α`
in `SL(2, ℂ)` (`slRepresentative`). In even weight it does not depend on the representative
(`bianchiGLSlash_eq`), and it is a right action of `GL₂(K)` (`bianchiGLSlash_mul`). -/
noncomputable def bianchiGLSlash : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  bianchiSlash k (slRepresentative σ α) F

lemma bianchiGLSlash_eq (hk : Even k) (hM : IsSLRepresentative σ α M) :
    bianchiGLSlash σ k α F = bianchiSlash k M F :=
  bianchiSlash_eq_of_isSLRepresentative hk hM (isSLRepresentative_slRepresentative α)

/-- **The slash operators of `GL₂(K)` form a right action, in even weight**:
`F ∣_k αβ = (F ∣_k α) ∣_k β`. -/
lemma bianchiGLSlash_mul (hk : Even k) :
    bianchiGLSlash σ k (α * β) F = bianchiGLSlash σ k β (bianchiGLSlash σ k α F) := by
  rw [bianchiGLSlash_eq hk ((isSLRepresentative_slRepresentative α).mul
    (isSLRepresentative_slRepresentative β)), bianchiSlash_mul]
  rfl

variable (α) in
lemma bianchiGLSlash_add :
    bianchiGLSlash σ k α (F + G) = bianchiGLSlash σ k α F + bianchiGLSlash σ k α G :=
  bianchiSlash_add ..

variable (α) in
lemma bianchiGLSlash_smul : bianchiGLSlash σ k α (c • F) = c • bianchiGLSlash σ k α F :=
  bianchiSlash_smul ..

variable (α) in
lemma bianchiGLSlash_sum {ι : Type*} (s : Finset ι)
    (H : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    bianchiGLSlash σ k α (∑ i ∈ s, H i) = ∑ i ∈ s, bianchiGLSlash σ k α (H i) :=
  bianchiSlash_sum k _ s H

/-- **A scalar matrix acts trivially, in even weight.** -/
lemma bianchiGLSlash_of_eq_smul_one (hk : Even k) {a : K}
    (hα : (α : Matrix (Fin 2) (Fin 2) K) = a • 1) (ha : a ≠ 0) : bianchiGLSlash σ k α F = F := by
  have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  have h₁ : IsSLRepresentative σ α 1 := ⟨σ a, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hα, hσa]⟩
  rw [bianchiGLSlash_eq hk h₁, bianchiSlash_one]

/-- **Invariance under a subgroup of `GL₂(K)`, in even weight**: a function is invariant under
`Γ` when `F ∣_k γ = F` for `γ ∈ Γ`, for the chosen representatives. -/
lemma mem_bianchiSlashInvariants_iff (hk : Even k) {Γ : Subgroup (GL (Fin 2) K)} :
    F ∈ bianchiSlashInvariants σ k Γ ↔ ∀ γ ∈ Γ, bianchiGLSlash σ k γ F = F :=
  ⟨fun hF γ hγ ↦ hF γ hγ _ (isSLRepresentative_slRepresentative γ), fun hF γ hγ _ hM ↦
    (bianchiGLSlash_eq hk hM).symm.trans (hF γ hγ)⟩

lemma mul_apply_one_one_eq_one_of_apply_one_zero (hM : M 1 0 = 0) : M 0 0 * M 1 1 = 1 := by
  have h : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := M.det_coe
  rw [det_fin_two, hM] at h
  simpa using h

lemma inv_automorphyFactor_eq_of_apply_one_zero (hM : M 1 0 = 0) :
    (automorphyFactor M p)⁻¹ = !![M 0 0, 0; 0, conj (M 0 0)] := by
  rw [automorphyFactor_of_apply_one_zero M p hM]
  refine inv_eq_left_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply_one_one_eq_one_of_apply_one_zero hM, ← map_mul]

lemma moebius_eq_of_apply_one_zero (hM : M 1 0 = 0) :
    moebius M p = (M 0 0 ^ 2 * p.1 + M 0 0 * M 0 1, ‖M 0 0‖ ^ 2 * p.2) := by
  have h₁ : M 0 0 * M 1 1 = 1 := mul_apply_one_one_eq_one_of_apply_one_zero hM
  have ha : M 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one h₁
  simp only [moebius, moebiusDenom, hM, zero_mul, zero_add, map_zero, mul_zero, add_zero,
    eq_inv_of_mul_eq_one_right h₁]
  ext
  · simp only
    rw [normSq_inv, map_inv₀]
    field_simp
    rw [one_div, ← inv_def, div_inv_eq_mul, mul_comm]
  · simp only
    rw [normSq_inv, normSq_eq_norm_sq]
    field_simp

lemma extend_bianchiSlash_of_apply_one_zero (hM : M 1 0 = 0) (hp : 0 < p.2) :
    extend (bianchiSlash k M F) p = symPowMatrix k !![M 0 0, 0; 0, conj (M 0 0)] *ᵥ
      extend F (M 0 0 ^ 2 * p.1 + M 0 0 * M 0 1, ‖M 0 0‖ ^ 2 * p.2) := by
  rw [extend_bianchiSlash_of_pos M hp, inv_automorphyFactor_eq_of_apply_one_zero hM,
    moebius_eq_of_apply_one_zero hM]

variable (σ) in
lemma coe_slRepresentative_heckeUpper : (slRepresentative σ (heckeUpper u b) : SL(2, ℂ)) =
    !![(σ u ^ (2⁻¹ : ℂ))⁻¹, (σ u ^ (2⁻¹ : ℂ))⁻¹ * σ b; 0, (σ u ^ (2⁻¹ : ℂ))⁻¹ * σ u] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slRepresentative, heckeUpper, det_fin_two]

variable (σ) in
/-- **The slash operator of `(1, b; 0, u)`**: an affine change of variables `x ↦ τ(x + b)`,
`y ↦ |τ|y`, `τ = u⁻¹`, followed by a constant matrix. -/
lemma extend_bianchiGLSlash_heckeUpper (hp : 0 < p.2) :
    extend (bianchiGLSlash σ k (heckeUpper u b) F) p =
      symPowMatrix k !![(σ u ^ (2⁻¹ : ℂ))⁻¹, 0; 0, conj (σ u ^ (2⁻¹ : ℂ))⁻¹] *ᵥ
        extend F ((σ u)⁻¹ * p.1 + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * p.2) := by
  have hs : (σ u ^ (2⁻¹ : ℂ)) ^ 2 = σ u := cpow_ofNat_inv_pow _ 2
  have h₁₀ : (slRepresentative σ (heckeUpper u b) : SL(2, ℂ)) 1 0 = 0 := by
    rw [coe_slRepresentative_heckeUpper]
    rfl
  have h₀₀ : (slRepresentative σ (heckeUpper u b) : SL(2, ℂ)) 0 0 = (σ u ^ (2⁻¹ : ℂ))⁻¹ := by
    rw [coe_slRepresentative_heckeUpper]
    rfl
  have h₀₁ : (slRepresentative σ (heckeUpper u b) : SL(2, ℂ)) 0 1 = (σ u ^ (2⁻¹ : ℂ))⁻¹ * σ b := by
    rw [coe_slRepresentative_heckeUpper]
    rfl
  rw [bianchiGLSlash, extend_bianchiSlash_of_apply_one_zero h₁₀ hp, h₀₀, h₀₁, ← mul_assoc, ← sq,
    inv_pow, hs, ← norm_pow, inv_pow, hs]

variable (σ k F y) in
/-- The function `x ↦ (F ∣_k g)(x, y)` on `ℂ`, of `F : ℋ₃ → ℂ^{k+1}`, for `g ∈ SL₂(K)` and
`y ∈ ℝ`, whose mean over a lattice of periods is the constant term of `F` at the cusp `g ∞`. -/
noncomputable def bianchiCuspSection : Fin (k + 1) → ℂ :=
  extend (bianchiSlash k (SpecialLinearGroup.map σ g) F) (x, y)

variable (σ k F) in
/-- A **cuspidal function** of weight `k` on `ℋ₃`, for an imaginary quadratic field `K` embedded in
`ℂ` by `σ`: a real analytic harmonic function `F : ℋ₃ → ℂ^{k+1}`, of moderate growth at the cusps,
such that for each `g ∈ SL₂(K)` the function `F ∣_k g` is periodic, in `x`, for a lattice
`σ(t𝒪_K)`, on which its mean vanishes. No invariance is required: this class is stable under the
slash operators of `GL₂(K)` in even weight (`IsBianchiCuspFunction.bianchiSlash`), and the invariant
functions in it are the cusp forms (`mem_bianchiCuspForms_iff`). -/
structure IsBianchiCuspFunction : Prop where
  /-- `F` is real analytic. -/
  analyticAt (z : HyperbolicThreeSpace) : AnalyticAt ℝ (extend F) z.coords
  /-- `F` is harmonic. -/
  harmonic : IsBianchiHarmonic k F
  /-- `F` has at worst polynomial growth at the cusps. -/
  growth : HasPolynomialGrowthAtCusps σ k F
  /-- `F ∣_k g` is periodic for a lattice, with vanishing mean. -/
  constantTerm (g : SL(2, K)) : ∃ t : K, t ≠ 0 ∧
    (∀ y : ℝ, 0 < y → ∀ l ∈ bianchiScaledLattice σ t, ∀ x : ℂ,
      bianchiCuspSection σ k F g (l + x) y = bianchiCuspSection σ k F g x y) ∧
    ∀ (y : ℝ) (P : Set ℂ), 0 < y → IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume →
      ∫ x in P, bianchiCuspSection σ k F g x y = 0

lemma continuous_extend_mk (hF : ∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend F) z.coords)
    (hy : 0 < y) : Continuous fun x : ℂ ↦ extend F (x, y) :=
  continuous_iff_continuousAt.mpr fun t ↦
    (hF (.mk (WithLp.toLp 2 (t, y)) hy)).continuousAt.comp (f := fun x : ℂ ↦ (x, y)) (by fun_prop)

lemma IsBianchiCuspFunction.continuous_bianchiCuspSection (hF : IsBianchiCuspFunction σ k F)
    (hy : 0 < y) : Continuous fun x ↦ bianchiCuspSection σ k F g x y :=
  continuous_extend_mk (analyticAt_extend_bianchiSlash _ hF.analyticAt) hy

lemma bianchiCuspSection_add : bianchiCuspSection σ k (F + G) g x y =
    bianchiCuspSection σ k F g x y + bianchiCuspSection σ k G g x y := by
  simp only [bianchiCuspSection, bianchiSlash_add, extend_add, Pi.add_apply]

lemma bianchiCuspSection_smul :
    bianchiCuspSection σ k (c • F) g x y = c • bianchiCuspSection σ k F g x y := by
  simp only [bianchiCuspSection, bianchiSlash_smul, extend_smul, Pi.smul_apply]

lemma bianchiCuspSection_zero : bianchiCuspSection σ k 0 g x y = 0 := by
  simp [bianchiCuspSection, bianchiSlash_zero, extend_zero]

/-- **A scalar multiple of a cuspidal function is cuspidal.** -/
lemma IsBianchiCuspFunction.const_smul (hF : IsBianchiCuspFunction σ k F) :
    IsBianchiCuspFunction σ k (c • F) where
  analyticAt z := by
    rw [extend_smul]
    exact (hF.analyticAt z).const_smul
  harmonic := hF.harmonic.const_smul c hF.analyticAt
  growth g := by
    rcases hF.growth g with ⟨C, n, h⟩
    refine ⟨‖c‖ * C, n, fun z hz ↦ ?_⟩
    rw [bianchiSlash_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg c)
  constantTerm g := by
    rcases hF.constantTerm g with ⟨t, ht, hp, hz⟩
    refine ⟨t, ht, fun y hy l hl x ↦ ?_, fun y P hy hP ↦ ?_⟩
    · rw [bianchiCuspSection_smul, bianchiCuspSection_smul, hp y hy l hl x]
    · simp only [bianchiCuspSection_smul]
      rw [integral_smul, hz y P hy hP, smul_zero]

/-- **The zero function is cuspidal.** -/
lemma isBianchiCuspFunction_zero : IsBianchiCuspFunction σ k 0 where
  analyticAt z := by
    rw [extend_zero]
    exact analyticAt_const
  harmonic := isBianchiHarmonic_zero k
  growth _ := ⟨0, 0, fun _ _ ↦ by simp [bianchiSlash_zero]⟩
  constantTerm _ := ⟨1, one_ne_zero, fun _ _ _ _ _ ↦ by simp only [bianchiCuspSection_zero],
    fun _ _ _ _ ↦ by simp only [bianchiCuspSection_zero, integral_zero]⟩

variable (β) in
/-- **A matrix of `GL₂(K)` is the product of a matrix of `SL₂(K)` and of `(1, b; 0, u)`.** -/
lemma exists_eq_toGL_mul_heckeUpper :
    ∃ (g' : SL(2, K)) (u : Kˣ) (b : K), β = SpecialLinearGroup.toGL g' * heckeUpper u b := by
  have hdet : β.val 0 0 * β.val 1 1 - β.val 0 1 * β.val 1 0 ≠ 0 := by
    rw [← det_fin_two]
    exact (GeneralLinearGroup.det β).ne_zero
  have hcop : IsCoprime (β.val 0 0) (β.val 1 0) :=
    ⟨β.val 1 1 / (β.val 0 0 * β.val 1 1 - β.val 0 1 * β.val 1 0),
      -β.val 0 1 / (β.val 0 0 * β.val 1 1 - β.val 0 1 * β.val 1 0), by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hdet]
        ring1⟩
  rcases hcop.exists_SL2_col 0 with ⟨g', h₀₀, h₁₀⟩
  have hg' : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = 1 := g'.fin_two_mul_sub_mul_eq_one
  rw [h₀₀, h₁₀] at hg'
  refine ⟨g', GeneralLinearGroup.det β, g' 1 1 * β.val 0 1 - g' 0 1 * β.val 1 1, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeUpper, mul_apply, det_fin_two, h₀₀, h₁₀]
  · linear_combination (-β.val 0 1) * hg'
  · linear_combination (-β.val 1 1) * hg'

lemma isSLRepresentative_toGL_map :
    IsSLRepresentative σ (SpecialLinearGroup.toGL g) (SpecialLinearGroup.map σ g) :=
  ⟨1, by ext i j; simp⟩

lemma mul_unipotent_mul_inv (a : K) : (g : Matrix (Fin 2) (Fin 2) K) * !![1, a; 0, 1] *
    ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 + a • ((g : Matrix (Fin 2) (Fin 2) K) *
      !![0, 1; 0, 0] * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) := by
  have h₁ : !![1, a; 0, 1] = 1 + a • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h₂ : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  rw [h₁, mul_add, add_mul, mul_one, h₂, mul_smul_comm, smul_mul_assoc]

variable [NumberField K]

variable {t₁ t₂ : K} in
lemma exists_mul_eq_mul (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) :
    ∃ w₁ w₂ : 𝓞 K, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ t₁ * w₁ = t₂ * w₂ := by
  rcases IsFractionRing.div_surjective (A := 𝓞 K) t₁ with ⟨a₁, b₁, hb₁, rfl⟩
  rcases IsFractionRing.div_surjective (A := 𝓞 K) t₂ with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁' : b₁ ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hb₂' : b₂ ≠ 0 := nonZeroDivisors.ne_zero hb₂
  have ha₁ : a₁ ≠ 0 := fun h ↦ ht₁ (by simp [h])
  have ha₂ : a₂ ≠ 0 := fun h ↦ ht₂ (by simp [h])
  have hb₁'' : (algebraMap (𝓞 K) K) b₁ ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb₁'
  have hb₂'' : (algebraMap (𝓞 K) K) b₂ ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb₂'
  refine ⟨b₁ * a₂, b₂ * a₁, mul_ne_zero hb₁' ha₂, mul_ne_zero hb₂' ha₁, ?_⟩
  push_cast
  field_simp

variable [IsTotallyComplex K] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : ℂ → V}
  {t : K} {P P' : Set ℂ}

lemma setIntegral_eq_zero_of_mul (hK : finrank ℚ K = 2) (ht : t ≠ 0) {w : 𝓞 K} (hw : w ≠ 0)
    (hc : Continuous f) (hper : ∀ l ∈ bianchiScaledLattice σ t, ∀ x, f (l + x) = f x)
    (hP' : IsAddFundamentalDomain (bianchiScaledLattice σ (t * w)) P' volume)
    (h₀ : ∀ P, IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume → ∫ x in P, f x = 0) :
    ∫ x in P', f x = 0 := by
  rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) hK ht with
    ⟨P₀, -, hP₀⟩
  rw [setIntegral_bianchiScaledLattice_mul hK ht hw hc hper hP₀ hP', h₀ P₀ hP₀, smul_zero]

lemma setIntegral_eq_zero_of_mul_eq_zero (hK : finrank ℚ K = 2) (ht : t ≠ 0) {w : 𝓞 K} (hw : w ≠ 0)
    (hc : Continuous f) (hper : ∀ l ∈ bianchiScaledLattice σ t, ∀ x, f (l + x) = f x)
    (hP : IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume)
    (hP' : IsAddFundamentalDomain (bianchiScaledLattice σ (t * w)) P' volume)
    (h₀ : ∫ x in P', f x = 0) : ∫ x in P, f x = 0 := by
  have hfin : Finite (𝓞 K ⧸ Ideal.span {w}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hw)
  have hn : (Nat.card (𝓞 K ⧸ Ideal.span {w}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [setIntegral_bianchiScaledLattice_mul hK ht hw hc hper hP hP',
    ← Nat.cast_smul_eq_nsmul ℝ] at h₀
  exact (smul_eq_zero.mp h₀).resolve_left hn

/-- **The sum of two cuspidal functions is cuspidal**, over an imaginary quadratic field: `F ∣_k g`
and `G ∣_k g` are periodic for a common lattice, on which their means vanish. -/
lemma IsBianchiCuspFunction.add (hK : finrank ℚ K = 2) (hF : IsBianchiCuspFunction σ k F)
    (hG : IsBianchiCuspFunction σ k G) : IsBianchiCuspFunction σ k (F + G) where
  analyticAt z := by
    rw [extend_add]
    exact (hF.analyticAt z).add (hG.analyticAt z)
  harmonic := hF.harmonic.add hF.analyticAt hG.analyticAt hG.harmonic
  growth := hF.growth.add hG.growth
  constantTerm g := by
    rcases hF.constantTerm g with ⟨t₁, ht₁, hp₁, hz₁⟩
    rcases hG.constantTerm g with ⟨t₂, ht₂, hp₂, hz₂⟩
    rcases exists_mul_eq_mul ht₁ ht₂ with ⟨w₁, w₂, hw₁, hw₂, he⟩
    have ht : t₁ * (w₁ : K) ≠ 0 := mul_ne_zero ht₁ (RingOfIntegers.coe_ne_zero_iff.mpr hw₁)
    have ht' : t₂ * (w₂ : K) ≠ 0 := mul_ne_zero ht₂ (RingOfIntegers.coe_ne_zero_iff.mpr hw₂)
    have hle₁ : bianchiScaledLattice σ (t₁ * w₁) ≤ bianchiScaledLattice σ t₁ :=
      bianchiScaledLattice_mul_le w₁
    have hle₂ : bianchiScaledLattice σ (t₂ * w₂) ≤ bianchiScaledLattice σ t₂ :=
      bianchiScaledLattice_mul_le w₂
    refine ⟨t₁ * w₁, ht, fun y hy l hl x ↦ ?_, fun y P hy hP ↦ ?_⟩
    · rw [bianchiCuspSection_add, bianchiCuspSection_add, hp₁ y hy l (hle₁ hl) x,
        hp₂ y hy l (hle₂ (he ▸ hl)) x]
    · have hP₂ : IsAddFundamentalDomain (bianchiScaledLattice σ (t₂ * w₂)) P volume := he ▸ hP
      have hc₁ : Continuous fun x ↦ bianchiCuspSection σ k F g x y :=
        hF.continuous_bianchiCuspSection g hy
      have hc₂ : Continuous fun x ↦ bianchiCuspSection σ k G g x y :=
        hG.continuous_bianchiCuspSection g hy
      have hi₁ : Integrable (fun x ↦ bianchiCuspSection σ k F g x y) (volume.restrict P) :=
        integrableOn_of_continuous_of_periodic hK ht hc₁ (fun l hl x ↦ hp₁ y hy l (hle₁ hl) x) hP
      have hi₂ : Integrable (fun x ↦ bianchiCuspSection σ k G g x y) (volume.restrict P) :=
        integrableOn_of_continuous_of_periodic hK ht' hc₂ (fun l hl x ↦ hp₂ y hy l (hle₂ hl) x) hP₂
      simp only [bianchiCuspSection_add]
      rw [integral_add hi₁ hi₂,
        setIntegral_eq_zero_of_mul hK ht₁ hw₁ hc₁ (hp₁ y hy) hP fun P hP ↦ hz₁ y P hy hP,
        setIntegral_eq_zero_of_mul hK ht₂ hw₂ hc₂ (hp₂ y hy) hP₂ fun P hP ↦ hz₂ y P hy hP,
        add_zero]

/-- **A finite sum of cuspidal functions is cuspidal.** -/
lemma IsBianchiCuspFunction.sum (hK : finrank ℚ K = 2) {ι : Type*} (s : Finset ι)
    {H : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ}
    (hH : ∀ i ∈ s, IsBianchiCuspFunction σ k (H i)) : IsBianchiCuspFunction σ k (∑ i ∈ s, H i) :=
  Finset.sum_induction _ (IsBianchiCuspFunction σ k) (fun _ _ h₁ h₂ ↦ h₁.add hK h₂)
    isBianchiCuspFunction_zero hH

variable (σ F t) in
/-- `F : ℋ₃ → ℂ^{k+1}` **has vanishing means** on the lattice `σ(t𝒪_K)`: for each `y > 0`, the
function `x ↦ F(x, y)` is periodic for this lattice, and its mean over a fundamental domain
vanishes. -/
def HasVanishingMean : Prop :=
  (∀ y : ℝ, 0 < y → ∀ l ∈ bianchiScaledLattice σ t, ∀ x : ℂ,
    extend F (l + x, y) = extend F (x, y)) ∧
    ∀ (y : ℝ) (P : Set ℂ), 0 < y → IsAddFundamentalDomain (bianchiScaledLattice σ t) P volume →
      ∫ x in P, extend F (x, y) = 0

/-- **The slash operator of `(1, b; 0, u)` preserves the vanishing of the means**:
`F ∣_k (1, b; 0, u)` is `F` after the affine change of variables `x ↦ u⁻¹(x + b)` and a constant
matrix, which maps a lattice of periods `σ(tu𝒪_K)` and a fundamental domain to a lattice of periods
`σ(t𝒪_K)` of `F` and a fundamental domain. -/
lemma HasVanishingMean.bianchiGLSlash_heckeUpper (hK : finrank ℚ K = 2) (ht : t ≠ 0)
    (hF : HasVanishingMean σ F t) (hc : ∀ y, 0 < y → Continuous fun x ↦ extend F (x, y)) :
    HasVanishingMean σ (bianchiGLSlash σ k (heckeUpper u b) F) (t * u) := by
  have hu₀ : σ (u : K) ≠ 0 := (map_ne_zero σ).mpr u.ne_zero
  have hτ : (σ u)⁻¹ ≠ 0 := inv_ne_zero hu₀
  have hsec (y : ℝ) (hy : 0 < y) (x : ℂ) : extend (bianchiGLSlash σ k (heckeUpper u b) F) (x, y) =
      symPowMatrix k !![(σ u ^ (2⁻¹ : ℂ))⁻¹, 0; 0, conj (σ u ^ (2⁻¹ : ℂ))⁻¹] *ᵥ
        extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) :=
    extend_bianchiGLSlash_heckeUpper σ u b (p := (x, y)) hy
  have hy' {y : ℝ} (hy : 0 < y) : 0 < ‖(σ (u : K))⁻¹‖ * y := mul_pos (norm_pos_iff.mpr hτ) hy
  have hper (y : ℝ) (hy : 0 < y) (l : ℂ) (hl : l ∈ bianchiScaledLattice σ (t * u)) (x : ℂ) :
      extend F ((σ u)⁻¹ * (l + x) + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) =
        extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) := by
    rcases mem_bianchiScaledLattice.mp hl with ⟨a, rfl⟩
    have h₁ : (σ u)⁻¹ * (σ (t * u * a) + x) + (σ u)⁻¹ * σ b = σ (t * a) +
        ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b) := by
      simp only [map_mul]
      field_simp
      ring1
    rw [h₁]
    exact hF.1 _ (hy' hy) _ (apply_mul_mem_bianchiScaledLattice σ t a) _
  have hut : t * (u : K) ≠ 0 := mul_ne_zero ht u.ne_zero
  refine ⟨fun y hy l hl x ↦ ?_, fun y P hy hP ↦ ?_⟩
  · rw [hsec y hy, hsec y hy, hper y hy l hl x]
  · have hP' : IsAddFundamentalDomain (bianchiScaledLattice σ t)
        ((fun x ↦ (σ u)⁻¹ * x + (σ u)⁻¹ * σ b) '' P) volume := by
      refine isAddFundamentalDomain_image_mul_add hP hτ _ fun l ↦ ?_
      rw [inv_inv, mem_bianchiScaledLattice, mem_bianchiScaledLattice]
      refine exists_congr fun a ↦ ?_
      rw [map_mul, map_mul, map_mul]
      constructor
      · intro h
        rw [← h]
        ring1
      · intro h
        apply mul_left_cancel₀ hu₀
        rw [← h]
        ring1
    have h₀ : ∫ x in P, extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) = 0 := by
      have h₁ : ∫ x in (fun x ↦ (σ u)⁻¹ * x + (σ u)⁻¹ * σ b) '' P, extend F (x, ‖(σ u)⁻¹‖ * y) =
          normSq (σ u)⁻¹ • ∫ x in P, extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) :=
        setIntegral_image_mul_add P (fun x ↦ extend F (x, ‖(σ u)⁻¹‖ * y)) hτ ((σ u)⁻¹ * σ b)
      rw [hF.2 _ _ (hy' hy) hP'] at h₁
      exact (smul_eq_zero.mp h₁.symm).resolve_left (normSq_eq_zero.not.mpr hτ)
    have hcont : Continuous fun x ↦ extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y) :=
      (hc _ (hy' hy)).comp (by fun_prop)
    have hi : Integrable (fun x ↦ extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y))
        (volume.restrict P) :=
      integrableOn_of_continuous_of_periodic hK hut hcont (hper y hy) hP
    let L : (Fin (k + 1) → ℂ) →L[ℂ] Fin (k + 1) → ℂ := LinearMap.toContinuousLinearMap <|
      mulVecLin <| symPowMatrix k !![(σ u ^ (2⁻¹ : ℂ))⁻¹, 0; 0, conj (σ u ^ (2⁻¹ : ℂ))⁻¹]
    have hL (x : ℂ) : extend (bianchiGLSlash σ k (heckeUpper u b) F) (x, y) =
        L (extend F ((σ u)⁻¹ * x + (σ u)⁻¹ * σ b, ‖(σ u)⁻¹‖ * y)) :=
      hsec y hy x
    simp only [hL]
    rw [L.integral_comp_comm hi, h₀, map_zero]

/-- **The slash operators of `GL₂(K)` preserve cuspidal functions, in even weight**: for
`M ∈ SL(2, ℂ)` representing `β ∈ GL₂(K)`, and `g ∈ SL₂(K)`, write `βg = g' t` with `g' ∈ SL₂(K)` and
`t = (1, b; 0, u)`. Then `F ∣_k M ∣_k g` is `F ∣_k g' ∣_k t`, whose means vanish. -/
lemma IsBianchiCuspFunction.slash (hK : finrank ℚ K = 2) (hk : Even k)
    (hF : IsBianchiCuspFunction σ k F) (hM : IsSLRepresentative σ β M) :
    IsBianchiCuspFunction σ k (bianchiSlash k M F) where
  analyticAt := analyticAt_extend_bianchiSlash _ hF.analyticAt
  harmonic := hF.harmonic.bianchiSlash _
  growth := hF.growth.bianchiSlash hM
  constantTerm g := by
    rcases exists_eq_toGL_mul_heckeUpper (β * SpecialLinearGroup.toGL g) with ⟨g', u, b, he⟩
    rcases hF.constantTerm g' with ⟨t, ht, hp, hz⟩
    have hrep₁ : IsSLRepresentative σ (β * SpecialLinearGroup.toGL g)
        (M * SpecialLinearGroup.map σ g) := hM.mul (isSLRepresentative_toGL_map g)
    have hrep₂ : IsSLRepresentative σ (β * SpecialLinearGroup.toGL g)
        (SpecialLinearGroup.map σ g' * slRepresentative σ (heckeUpper u b)) := by
      rw [he]
      exact (isSLRepresentative_toGL_map g').mul (isSLRepresentative_slRepresentative _)
    have hslash : bianchiSlash k (SpecialLinearGroup.map σ g) (bianchiSlash k M F) =
        bianchiGLSlash σ k (heckeUpper u b) (bianchiSlash k (SpecialLinearGroup.map σ g') F) := by
      rw [← bianchiSlash_mul, bianchiGLSlash, ← bianchiSlash_mul,
        bianchiSlash_eq_of_isSLRepresentative hk hrep₂ hrep₁]
    have h₁ : HasVanishingMean σ
        (bianchiGLSlash σ k (heckeUpper u b) (bianchiSlash k (SpecialLinearGroup.map σ g') F))
        (t * u) :=
      HasVanishingMean.bianchiGLSlash_heckeUpper u b hK ht ⟨hp, hz⟩
        fun y hy ↦ hF.continuous_bianchiCuspSection g' hy
    rw [← hslash] at h₁
    exact ⟨t * u, mul_ne_zero ht u.ne_zero, h₁⟩

end HyperbolicThreeSpace
