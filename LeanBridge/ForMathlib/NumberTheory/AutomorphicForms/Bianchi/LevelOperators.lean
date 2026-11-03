import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.CuspTranslations

/-!
# Level-changing operators on Bianchi modular forms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `k` an even
weight. For a function `F` on `ℋ₃` and a prime `q` of `𝒪_K`, with `n = |𝒪_K / (q)|`, this file
studies the operators (`∣` being the slash operator `bianchiGLSlash` of `GL₂(K)`)

* `G ∣ (q, 0; 0, 1)`, raising the level by `q` (`bianchiLevelRaise`), with inverse
  `F ∣ (1, 0; 0, q)` (`bianchiLevelLower`);
* `U_q F = ∑_{j mod q} F ∣ (1, 0; 0, q) ∣ (1, j; 0, 1)` (`bianchiUpOperator`);
* `E_q F = n⁻¹ ∑_{j mod q} F ∣ (1, j/q; 0, 1)`, the average of `F(x + j/q, y)`
  (`bianchiPeriodAverage`), which is `n⁻¹ (U_q F) ∣ (q, 0; 0, 1)`;
* `Tr H = n⁻¹ ∑_{i mod q} H ∣ (1, 0; N i, 1)`, the trace from `Γ₀(Nq)` to `Γ₀(N)` for `q ∣ N`
  (`bianchiLevelTrace`).

This is the setting of the Main Lemma of Atkin and Lehner, as in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.LevelOperators`, with `n = N(q)` in
place of the prime of `ℤ`. For `F` in `S_k(N)` with `q ∣ N`: `U_q F` lies in `S_k(N)`, and in
`S_k(N / q)` if `q² ∣ N`; `E_q F` lies in `S_k(Nq)`; the trace maps `S_k(Nq)` to `S_k(N)` and
commutes with the level raising. The key identity (`sub_bianchiLevelTrace_bianchiPeriodAverage`) is:
for `N = qM`, `F - Tr (E_q F) = c (F - Z ∣ (q, 0; 0, 1))`, with `c ≠ 0` and `Z` in `S_k(M)`. If
`q ∣ M`, then `c = 1` and `Z = n⁻¹ U_q F`. If `q ∤ M`, the function `G = F ∣ (1, 0; 0, q)` is
invariant under `Γ₀(M) ∩ Γ⁰(q)`, which has `n + 1` right cosets in `Γ₀(M)`, represented by `1` and
`(1, j; 0, 1) (1, 0; M i, 1)`, `i mod q`, for each `j ≠ 0 mod q`, while the matrices
`(1, 0; M i, 1)` lie in the trivial coset. So `c = 1 - n⁻²` and `Z` is a multiple of the trace of
`G` to `Γ₀(M)`.

All the elements `q`, `N`, … of `𝒪_K` are nonzero, as elements of the submonoid `(𝒪_K)⁰`.

## Main definitions

* `HyperbolicThreeSpace.IsRightTransversal`: systems of representatives of right cosets.
* `HyperbolicThreeSpace.bianchiUnit`: a nonzero integer as a unit of `K`.
* `HyperbolicThreeSpace.glUpper`, `HyperbolicThreeSpace.glLower`: the unipotent matrices.
* `HyperbolicThreeSpace.gamma0Upper`: the subgroup `Γ₀(M) ∩ Γ⁰(q)`.
* `HyperbolicThreeSpace.glSlash`: the slash operator of a matrix of `GL₂(𝒪_K)`.
* `HyperbolicThreeSpace.bianchiLevelRaise`, `HyperbolicThreeSpace.bianchiLevelLower`: the functions
  `G ∣ (q, 0; 0, 1)` and `F ∣ (1, 0; 0, q)`.
* `HyperbolicThreeSpace.bianchiUpOperator`: the operator `U_q`.
* `HyperbolicThreeSpace.bianchiPeriodAverage`: the operator `E_q`.
* `HyperbolicThreeSpace.bianchiLevelTrace`: the trace from `Γ₀(Nq)` to `Γ₀(N)`.
* `HyperbolicThreeSpace.bianchiLowerTrace`: the trace of `F ∣ (1, 0; 0, q)` to `Γ₀(M)` for a prime
  `q ∤ M`.
* `HyperbolicThreeSpace.bianchiTraceConstant`, `HyperbolicThreeSpace.bianchiTraceRemainder`: the
  constant `c` and the function `Z` of the key identity.

## Main results

* `HyperbolicThreeSpace.isRightTransversal_glLower`,
  `HyperbolicThreeSpace.isRightTransversal_glUpper`,
  `HyperbolicThreeSpace.isRightTransversal_option`: the coset representatives.
* `HyperbolicThreeSpace.coe_inv_gl`: the inverse of a matrix of `GL₂(𝒪_K)`.
* `HyperbolicThreeSpace.bianchiGLSlash_of_coe_eq_smul`: proportional matrices act in the same way.
* `HyperbolicThreeSpace.glSlash_bianchiLevelLower`: the invariance of `F ∣ (1, 0; 0, q)`.
* `HyperbolicThreeSpace.sum_glSlash_mem_bianchiCuspForms`: the trace of a cuspidal function along a
  coset transversal is a cusp form.
* `HyperbolicThreeSpace.bianchiLevelRaise_mem_bianchiCuspForms`: the level raising maps `S_k(M)` to
  `S_k(dM)`.
* `HyperbolicThreeSpace.bianchiUpOperator_mem_bianchiCuspForms`: `U_q` lowers the level.
* `HyperbolicThreeSpace.bianchiPeriodAverage_mem_bianchiCuspForms`: `E_q` raises the level by `q`.
* `HyperbolicThreeSpace.bianchiLevelTrace_mem_bianchiCuspForms`: the trace lowers the level by `q`.
* `HyperbolicThreeSpace.bianchiLevelTrace_bianchiLevelRaise`: the trace commutes with the level
  raising.
* `HyperbolicThreeSpace.bianchiTraceRemainder_mem_bianchiCuspForms`: the function `Z` has level `M`.
* `HyperbolicThreeSpace.sub_bianchiLevelTrace_bianchiPeriodAverage`: the key identity.
-/

open Complex Ideal Matrix Module NumberField HilbertModularGroup

open Ideal renaming Quotient.mk → quotientMk, Quotient.mk_out → quotientMk_out

open scoped MatrixGroups nonZeroDivisors

namespace HyperbolicThreeSpace

section Group

variable {G W ι ι' : Type*} [Group G] [AddCommMonoid W] {Γ' Γ : Subgroup G} {r : ι → G} {γ : G}

variable (Γ' Γ r) in
/-- `r` is a **system of representatives of the right cosets** `Γ' r_i` of `Γ'` in `Γ`: every `r_i`
lies in `Γ`, and every `γ ∈ Γ` lies in exactly one coset `Γ' r_i`. No inclusion `Γ' ≤ Γ` is
asked for. -/
def IsRightTransversal : Prop :=
  (∀ i, r i ∈ Γ) ∧ ∀ γ ∈ Γ, ∃! i, r i * γ⁻¹ ∈ Γ'

lemma IsRightTransversal.sum_eq [Fintype ι] [Fintype ι'] {r' : ι' → G}
    (hr : IsRightTransversal Γ' Γ r) (hr' : IsRightTransversal Γ' Γ r') {φ : G → W}
    (hφ : ∀ δ ∈ Γ', ∀ x, φ (δ * x) = φ x) : ∑ i, φ (r i) = ∑ i, φ (r' i) := by
  choose f hf using fun i ↦ (hr'.2 (r i) (hr.1 i)).exists
  have hbij : Function.Bijective f := by
    refine ⟨fun i j hij ↦ ?_, fun i' ↦ ?_⟩
    · refine (hr.2 (r j) (hr.1 j)).unique ?_ (by simp)
      have h1 : r' (f j) * (r i)⁻¹ ∈ Γ' := hij ▸ hf i
      have h : r i * (r j)⁻¹ = (r' (f j) * (r i)⁻¹)⁻¹ * (r' (f j) * (r j)⁻¹) := by
        group
      rw [h]
      exact mul_mem (inv_mem h1) (hf j)
    · rcases (hr.2 (r' i') (hr'.1 i')).exists with ⟨i, hi⟩
      refine ⟨i, (hr'.2 (r i) (hr.1 i)).unique (hf i) ?_⟩
      simpa using inv_mem hi
  rw [← hbij.sum_comp fun i' ↦ φ (r' i')]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : r' (f i) = (r' (f i) * (r i)⁻¹) * r i := by
    group
  rw [h, hφ _ (hf i)]

lemma IsRightTransversal.mul_right (hr : IsRightTransversal Γ' Γ r) (hγ : γ ∈ Γ) :
    IsRightTransversal Γ' Γ fun i ↦ r i * γ := by
  refine ⟨fun i ↦ mul_mem (hr.1 i) hγ, fun g hg ↦ ?_⟩
  simpa [mul_assoc] using hr.2 (g * γ⁻¹) (mul_mem hg (inv_mem hγ))

end Group

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ}

/-- A nonzero integer of `K`, as a unit of `K`. -/
noncomputable def bianchiUnit (q : (𝓞 K)⁰) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K q) <|
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (nonZeroDivisors.ne_zero q.2)

lemma coe_bianchiUnit (q : (𝓞 K)⁰) : (bianchiUnit q : K) = algebraMap (𝓞 K) K q :=
  rfl

/-- The matrix `(1, b; 0, 1)` of `GL₂(𝒪_K)`. -/
def glUpper (b : 𝓞 K) : GL (Fin 2) (𝓞 K) :=
  SpecialLinearGroup.toGL ⟨!![1, b; 0, 1], by simp⟩

/-- The matrix `(1, 0; x, 1)` of `GL₂(𝒪_K)`. -/
def glLower (x : 𝓞 K) : GL (Fin 2) (𝓞 K) :=
  SpecialLinearGroup.toGL ⟨!![1, 0; x, 1], by simp⟩

variable {b x : 𝓞 K} {γ δ : GL (Fin 2) (𝓞 K)} {M N d q : (𝓞 K)⁰}
  {F G H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

variable (b) in
lemma coe_glUpper : (glUpper b : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, b; 0, 1] :=
  rfl

variable (x) in
lemma coe_glLower : (glLower x : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, 0; x, 1] :=
  rfl

lemma mem_gamma0GL_span_iff :
    γ ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL ↔ (N : 𝓞 K) ∣ (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) 1 0 :=
  Ideal.mem_span_singleton

lemma glLower_mem_gamma0GL_iff : glLower x ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL ↔ (N : 𝓞 K) ∣ x :=
  mem_gamma0GL_span_iff

variable (b N) in
lemma glUpper_mem_gamma0GL : glUpper b ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL := by
  rw [mem_gamma0GL_span_iff, coe_glUpper]
  simp

variable (γ) in
/-- The formula for the inverse of a matrix of `GL₂(𝒪_K)`. -/
lemma coe_inv_gl : ((γ⁻¹ : GL (Fin 2) (𝓞 K)) : Matrix (Fin 2) (Fin 2) (𝓞 K)) =
    ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val •
      !![γ.val 1 1, -γ.val 0 1; -γ.val 1 0, γ.val 0 0] := by
  rw [coe_units_inv, Matrix.inv_def, adjugate_fin_two, ← GeneralLinearGroup.val_det_apply]
  congr 1
  exact Ring.inverse_unit _

variable (γ) in
lemma det_eq_of_gl :
    γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = (GeneralLinearGroup.det γ : (𝓞 K)ˣ) := by
  rw [GeneralLinearGroup.val_det_apply, det_fin_two]

variable (M q) in
/-- The subgroup `Γ₀(M) ∩ Γ⁰(q)` of `GL₂(𝒪_K)`: the matrices `(a, b; c, d)` with `M ∣ c` and
`q ∣ b`. For `F` invariant under `Γ₀(qM)`, the function `F ∣ (1, 0; 0, q)` is invariant under it
(`glSlash_bianchiLevelLower`). -/
def gamma0Upper : Subgroup (GL (Fin 2) (𝓞 K)) where
  carrier := {γ | (M : 𝓞 K) ∣ γ.val 1 0 ∧ (q : 𝓞 K) ∣ γ.val 0 1}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, mul_apply, Fin.sum_univ_two]
      exact dvd_add (hx.1.mul_right _) (hy.1.mul_left _)
    · simp only [Units.val_mul, mul_apply, Fin.sum_univ_two]
      exact dvd_add (hy.2.mul_left _) (hx.2.mul_right _)
  one_mem' := by simp
  inv_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · rw [coe_inv_gl]
      simpa using hx.1
    · rw [coe_inv_gl]
      simpa using hx.2

lemma mem_gamma0Upper_iff : γ ∈ gamma0Upper M q ↔ (M : 𝓞 K) ∣ γ.val 1 0 ∧ (q : 𝓞 K) ∣ γ.val 0 1 :=
  Iff.rfl

noncomputable instance [NumberField K] (q : (𝓞 K)⁰) : Fintype (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :=
  have : Finite (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simp)
  Fintype.ofFinite _

variable (σ k γ F) in
/-- The slash operator of a matrix of `GL₂(𝒪_K)`, through `GL₂(K)`. -/
noncomputable def glSlash : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  bianchiGLSlash σ k (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) F

lemma glSlash_mul (hk : Even k) : glSlash σ k (γ * δ) F = glSlash σ k δ (glSlash σ k γ F) := by
  rw [glSlash, map_mul, bianchiGLSlash_mul hk]
  rfl

lemma glSlash_one : glSlash σ k 1 F = F := by
  rw [glSlash, map_one]
  have h : slRepresentative σ (1 : GL (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slRepresentative]
  rw [bianchiGLSlash, h, bianchiSlash_one]

lemma IsBianchiSlashInvariant.glSlash_eq {Γ : Subgroup (GL (Fin 2) (𝓞 K))}
    (hF : IsBianchiSlashInvariant σ Γ k F) (hγ : γ ∈ Γ) : glSlash σ k γ F = F :=
  hF γ hγ _ _ rfl

lemma isBianchiSlashInvariant_of_glSlash_eq (hk : Even k) {Γ : Subgroup (GL (Fin 2) (𝓞 K))}
    (h : ∀ γ ∈ Γ, glSlash σ k γ F = F) : IsBianchiSlashInvariant σ Γ k F := by
  intro γ hγ g s hg
  have h₁ : ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).map σ = (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map
        (σ.comp (algebraMap (𝓞 K) K)) := by
    ext i j
    rfl
  have h₂ : IsSLRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ) g :=
    ⟨s, by rw [h₁, hg]⟩
  exact (bianchiGLSlash_eq hk h₂).symm.trans (h γ hγ)

/-- **Slash operators differing by a scalar agree, in even weight.** -/
lemma bianchiGLSlash_of_coe_eq_smul (hk : Even k) {α β : GL (Fin 2) K} {c : K}
    (hαβ : (α : Matrix (Fin 2) (Fin 2) K) = c • (β : Matrix (Fin 2) (Fin 2) K)) (hc : c ≠ 0) :
    bianchiGLSlash σ k α F = bianchiGLSlash σ k β F := by
  rcases isSLRepresentative_slRepresentative (σ := σ) β with ⟨s, hs⟩
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hs₀ : s ≠ 0 := ne_zero_of_coe_eq_inv_smul hs
  have h₂ : (α : Matrix (Fin 2) (Fin 2) K).map σ = σ c • (β : Matrix (Fin 2) (Fin 2) K).map σ := by
    rw [hαβ]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
  have h₁ : IsSLRepresentative σ α (slRepresentative σ β) := by
    refine ⟨s * σ c, ?_⟩
    rw [hs, h₂, smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hσc, mul_one]
  rw [bianchiGLSlash_eq hk h₁]
  rfl

variable (σ k q G) in
/-- The function `G ∣ (q, 0; 0, 1)`, of level `dM` for `G` of level `M` and `q = d`
(`bianchiLevelRaise_mem_bianchiCuspForms`). -/
noncomputable def bianchiLevelRaise : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  bianchiGLSlash σ k (heckeLower (bianchiUnit q)) G

variable (σ k q F) in
/-- The function `F ∣ (1, 0; 0, q)`, the inverse of `bianchiLevelRaise σ k q`
(`bianchiLevelRaise_bianchiLevelLower`). -/
noncomputable def bianchiLevelLower : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  bianchiGLSlash σ k (heckeUpper (bianchiUnit q) 0) F

lemma bianchiLevelRaise_bianchiLevelLower (hk : Even k) :
    bianchiLevelRaise σ k q (bianchiLevelLower σ k q F) = F := by
  rw [bianchiLevelRaise, bianchiLevelLower, ← bianchiGLSlash_mul hk]
  refine bianchiGLSlash_of_eq_smul_one hk (a := bianchiUnit q) ?_ (bianchiUnit q).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeUpper, heckeLower]

lemma bianchiLevelRaise_add :
    bianchiLevelRaise σ k q (F + G) = bianchiLevelRaise σ k q F + bianchiLevelRaise σ k q G :=
  bianchiGLSlash_add _

lemma bianchiLevelRaise_smul (c : ℂ) :
    bianchiLevelRaise σ k q (c • F) = c • bianchiLevelRaise σ k q F :=
  bianchiGLSlash_smul _ _

lemma bianchiLevelRaise_sum {ι : Type*} (s : Finset ι)
    (Φ : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    bianchiLevelRaise σ k q (∑ i ∈ s, Φ i) = ∑ i ∈ s, bianchiLevelRaise σ k q (Φ i) :=
  bianchiGLSlash_sum _ s Φ

lemma glSlash_add : glSlash σ k γ (F + G) = glSlash σ k γ F + glSlash σ k γ G :=
  bianchiGLSlash_add _

lemma glSlash_smul (c : ℂ) : glSlash σ k γ (c • F) = c • glSlash σ k γ F :=
  bianchiGLSlash_smul _ _

lemma glSlash_sum {ι : Type*} (s : Finset ι) (Φ : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    glSlash σ k γ (∑ i ∈ s, Φ i) = ∑ i ∈ s, glSlash σ k γ (Φ i) :=
  bianchiGLSlash_sum _ s Φ

lemma heckeUpper_mul_map_eq_of_mem (hδ : δ ∈ gamma0Upper M q) :
    ∃ δ' ∈ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL, heckeUpper (bianchiUnit q) 0 *
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ =
        GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeUpper (bianchiUnit q) 0 := by
  rcases hδ.2 with ⟨b', hb'⟩
  have hdet : IsUnit (!![δ.val 0 0, b'; (q : 𝓞 K) * δ.val 1 0, δ.val 1 1]).det := by
    have h : (!![δ.val 0 0, b'; (q : 𝓞 K) * δ.val 1 0, δ.val 1 1]).det =
        (GeneralLinearGroup.det δ : (𝓞 K)ˣ) := by
      rw [← det_eq_of_gl, det_fin_two_of, hb']
      ring1
    rw [h]
    exact Units.isUnit _
  refine ⟨GeneralLinearGroup.mk'' _ hdet, mem_gamma0GL_span_iff.mpr ?_, ?_⟩
  · rw [Submonoid.coe_mul]
    exact mul_dvd_mul_left _ hδ.1
  · refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeUpper, mul_apply, hb', coe_bianchiUnit, mul_comm]

/-- **`F ∣ (1, 0; 0, q)` is invariant under `Γ₀(M) ∩ Γ⁰(q)`** for `F` invariant under `Γ₀(qM)`:
`(1, 0; 0, q)` conjugates `Γ₀(M) ∩ Γ⁰(q)` to `Γ₀(qM)`, as
`(1, 0; 0, q) (a, qb; c, d) = (a, b; qc, d) (1, 0; 0, q)`. -/
lemma glSlash_bianchiLevelLower (hk : Even k)
    (hF : IsBianchiSlashInvariant σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k F)
    (hδ : δ ∈ gamma0Upper M q) :
    glSlash σ k δ (bianchiLevelLower σ k q F) = bianchiLevelLower σ k q F := by
  rcases heckeUpper_mul_map_eq_of_mem hδ with ⟨δ', hδ', hmat⟩
  rw [bianchiLevelLower, glSlash, ← bianchiGLSlash_mul hk, hmat, bianchiGLSlash_mul hk]
  exact congrArg _ (hF.glSlash_eq hδ')

variable (x) in
lemma glSlash_glLower_bianchiLevelRaise (hk : Even k) :
    glSlash σ k (glLower ((d : 𝓞 K) * x)) (bianchiLevelRaise σ k d G) =
      bianchiLevelRaise σ k d (glSlash σ k (glLower x) G) := by
  rw [bianchiLevelRaise, glSlash, ← bianchiGLSlash_mul hk, bianchiLevelRaise, glSlash,
    ← bianchiGLSlash_mul hk]
  congr 1
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeLower, coe_glLower, mul_apply, coe_bianchiUnit, mul_comm]

variable (N) in
lemma ne_bot_span : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := by
  simp

lemma glLower_mul_inv_mem_gamma0GL_iff {c : 𝓞 K} (hc : γ.val 1 0 = (M : 𝓞 K) * c)
    (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹ ∈
      (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL ↔
        i * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) =
          quotientMk (Ideal.span {(q : 𝓞 K)}) c := by
  have h : (glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹).val 1 0 =
      ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val *
        ((M : 𝓞 K) * (Quotient.out i * γ.val 1 1 - c)) := by
    rw [Units.val_mul, coe_glLower, coe_inv_gl, hc]
    simp
    ring1
  rw [mem_gamma0GL_span_iff, h, IsUnit.dvd_mul_left (Units.isUnit _), Submonoid.coe_mul,
    mul_dvd_mul_iff_left (nonZeroDivisors.ne_zero M.2), ← Ideal.mem_span_singleton,
    ← Quotient.eq_zero_iff_mem, map_sub, map_mul, quotientMk_out, sub_eq_zero]

lemma not_dvd_one_of_prime (hq : Prime (q : 𝓞 K)) : ¬(q : 𝓞 K) ∣ 1 :=
  fun h ↦ hq.not_isUnit (isUnit_of_dvd_one h)

variable [NumberField K]

lemma isMaximal_span_of_prime (hq : Prime (q : 𝓞 K)) : (Ideal.span {(q : 𝓞 K)}).IsMaximal :=
  ((Ideal.span_singleton_prime hq.ne_zero).mpr hq).isMaximal (by simp)

variable (q) in
lemma card_residue_ne_zero : (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

lemma one_lt_card_residue (hq : Prime (q : 𝓞 K)) :
    1 < Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  have h₁ : Nontrivial (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.nontrivial_iff.mpr
    (IsMaximal.ne_top inferInstance)
  exact Fintype.one_lt_card

variable (σ k q F) in
/-- The operator `U_q F = ∑_{j mod q} F ∣ (1, 0; 0, q) ∣ (1, j; 0, 1)`, without normalisation. It
preserves `S_k(N)` for a prime `q ∣ N` and lowers the level of `F` to `N / q` when `q² ∣ N`
(`bianchiUpOperator_mem_bianchiCuspForms`). -/
noncomputable def bianchiUpOperator : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, glSlash σ k (glUpper (Quotient.out j))
    (bianchiLevelLower σ k q F)

variable (σ k q F) in
/-- The average `E_q F = n⁻¹ ∑_{j mod q} F ∣ (1, j / q; 0, 1)` of `F`, `n = |𝒪_K / (q)|`, whose
value at `(x, y)` is the average of the `F(x + j / q, y)`. For `F` with a Fourier expansion in `x`,
it keeps exactly the terms whose index is divisible by `q`. -/
noncomputable def bianchiPeriodAverage : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ • ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
    bianchiGLSlash σ k (heckeUpper 1 (algebraMap (𝓞 K) K (Quotient.out j) / bianchiUnit q)) F

variable (σ k N q H) in
/-- The normalised trace `Tr H = n⁻¹ ∑_{i mod q} H ∣ (1, 0; N i, 1)`, `n = |𝒪_K / (q)|`, from
`Γ₀(Nq)` to `Γ₀(N)` for a prime `q ∣ N`: the matrices represent the right cosets of `Γ₀(Nq)` in
`Γ₀(N)` (`isRightTransversal_glLower`). -/
noncomputable def bianchiLevelTrace : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ • ∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
    glSlash σ k (glLower ((N : 𝓞 K) * Quotient.out i)) H

variable (σ k M q F) in
/-- The trace of `F ∣ (1, 0; 0, q)` from `Γ₀(M) ∩ Γ⁰(q)` to `Γ₀(M)` for a prime `q ∤ M`, along the
representatives `1` and `(1, 1; 0, 1) (1, 0; M i, 1)`, `i mod q`, of
`isRightTransversal_option`. -/
noncomputable def bianchiLowerTrace : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  ∑ p : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}), glSlash σ k
    (p.elim 1 fun i ↦ glUpper 1 * glLower ((M : 𝓞 K) * Quotient.out i)) (bianchiLevelLower σ k q F)

open scoped Classical in
variable (M q) in
/-- The constant `c` of the key identity `F - Tr (E_q F) = c (F - Z ∣ (q, 0; 0, 1))`
(`sub_bianchiLevelTrace_bianchiPeriodAverage`): `1` if `q ∣ M`, and `1 - n⁻²` otherwise, for
`n = |𝒪_K / (q)|`. -/
noncomputable def bianchiTraceConstant : ℂ :=
  if (q : 𝓞 K) ∣ M then 1 else
    1 - (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ *
      (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹

open scoped Classical in
variable (σ k M q F) in
/-- The function `Z` of the key identity `F - Tr (E_q F) = c (F - Z ∣ (q, 0; 0, 1))`
(`sub_bianchiLevelTrace_bianchiPeriodAverage`), of level `M`: `n⁻¹ U_q F` if `q ∣ M`, and
`n⁻² (n - 1) c⁻¹ Y` otherwise, for `Y` the trace `bianchiLowerTrace σ k M q F`. -/
noncomputable def bianchiTraceRemainder : HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
  if (q : 𝓞 K) ∣ M then
    (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ • bianchiUpOperator σ k q F
  else ((Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ *
    (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ *
      ((Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) - 1) / bianchiTraceConstant M q) •
        bianchiLowerTrace σ k M q F

lemma unit_ne_zero_residue (hq : Prime (q : 𝓞 K)) (u : (𝓞 K)ˣ) :
    quotientMk (Ideal.span {(q : 𝓞 K)}) (u : 𝓞 K) ≠ 0 := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  have h₁ : Nontrivial (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.nontrivial_iff.mpr
    (IsMaximal.ne_top inferInstance)
  exact (u.isUnit.map _).ne_zero

/-- **The matrices `(1, 0; M i, 1)`, `i mod q`, represent the right cosets of `Γ₀(Mq)` in `Γ₀(M)`**
for a prime `q ∣ M`. -/
lemma isRightTransversal_glLower (hq : Prime (q : 𝓞 K)) (hqM : (q : 𝓞 K) ∣ M) :
    IsRightTransversal (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL
      (Ideal.span {(M : 𝓞 K)}).gamma0GL
      fun i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)} ↦ glLower ((M : 𝓞 K) * Quotient.out i) := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  let _ : Field (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.field _
  refine ⟨fun i ↦ glLower_mem_gamma0GL_iff.mpr (dvd_mul_right _ _), fun γ hγ ↦ ?_⟩
  rcases mem_gamma0GL_span_iff.mp hγ with ⟨c, hc⟩
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = (GeneralLinearGroup.det γ : (𝓞 K)ˣ) :=
    det_eq_of_gl γ
  have hd : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) ≠ 0 := by
    intro hd
    have h₁ : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 0) = 0 :=
      Quotient.eq_zero_iff_mem.mpr <| Ideal.mem_span_singleton.mpr <|
        hqM.trans ⟨c, hc⟩
    refine unit_ne_zero_residue hq (GeneralLinearGroup.det γ) ?_
    rw [← hdet, map_sub, map_mul, map_mul, hd, h₁, mul_zero, mul_zero, sub_zero]
  have key (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹ ∈
      (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL ↔
        i * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) =
          quotientMk (Ideal.span {(q : 𝓞 K)}) c :=
    glLower_mul_inv_mem_gamma0GL_iff hc i
  exact ⟨quotientMk _ c / quotientMk _ (γ.val 1 1),
    (key _).mpr (div_mul_cancel₀ _ hd),
    fun i hi ↦ eq_div_of_mul_eq hd ((key i).mp hi)⟩

/-- **The translations `(1, j; 0, 1)`, `j mod q`, represent the right cosets of `Γ₀(M) ∩ Γ⁰(q)` in
`Γ₀(M)`** for a prime `q ∣ M`. -/
lemma isRightTransversal_glUpper (hq : Prime (q : 𝓞 K)) (hqM : (q : 𝓞 K) ∣ M) :
    IsRightTransversal (gamma0Upper M q) (Ideal.span {(M : 𝓞 K)}).gamma0GL
      fun j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)} ↦ glUpper (Quotient.out j) := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  let _ : Field (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.field _
  refine ⟨fun j ↦ glUpper_mem_gamma0GL _ _, fun γ hγ ↦ ?_⟩
  have hM : (M : 𝓞 K) ∣ γ.val 1 0 := mem_gamma0GL_span_iff.mp hγ
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = (GeneralLinearGroup.det γ : (𝓞 K)ˣ) :=
    det_eq_of_gl γ
  have ha : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) ≠ 0 := by
    intro ha
    have h₁ : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 0) = 0 :=
      Quotient.eq_zero_iff_mem.mpr <| Ideal.mem_span_singleton.mpr <| hqM.trans hM
    refine unit_ne_zero_residue hq (GeneralLinearGroup.det γ) ?_
    rw [← hdet, map_sub, map_mul, map_mul, ha, h₁, mul_zero, zero_mul, sub_zero]
  have key (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glUpper (Quotient.out j) * γ⁻¹ ∈ gamma0Upper M q ↔
      j * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) =
        quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) := by
    have h₁ : (glUpper (Quotient.out j) * γ⁻¹).val 1 0 =
        ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val * -γ.val 1 0 := by
      rw [Units.val_mul, coe_glUpper, coe_inv_gl]
      simp
    have h₂ : (glUpper (Quotient.out j) * γ⁻¹).val 0 1 =
        ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val * (Quotient.out j * γ.val 0 0 - γ.val 0 1) := by
      rw [Units.val_mul, coe_glUpper, coe_inv_gl]
      simp
      ring1
    rw [mem_gamma0Upper_iff, h₁, h₂, IsUnit.dvd_mul_left (Units.isUnit _),
      IsUnit.dvd_mul_left (Units.isUnit _), dvd_neg, and_iff_right hM,
      ← Ideal.mem_span_singleton, ← Quotient.eq_zero_iff_mem, map_sub, map_mul,
      quotientMk_out, sub_eq_zero]
  exact ⟨quotientMk _ (γ.val 0 1) / quotientMk _ (γ.val 0 0),
    (key _).mpr (div_mul_cancel₀ _ ha), fun i hi ↦ eq_div_of_mul_eq ha ((key i).mp hi)⟩

/-- **For a prime `q ∤ M`, `1` and `(1, j; 0, 1) (1, 0; M i, 1)`, `i mod q`, represent the right
cosets of `Γ₀(M) ∩ Γ⁰(q)` in `Γ₀(M)`**, for every `j` prime to `q`. -/
lemma isRightTransversal_option (hq : Prime (q : 𝓞 K)) (hqM : ¬(q : 𝓞 K) ∣ M) {j : 𝓞 K}
    (hj : ¬(q : 𝓞 K) ∣ j) : IsRightTransversal (gamma0Upper M q) (Ideal.span {(M : 𝓞 K)}).gamma0GL
      fun p : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ↦
        p.elim 1 fun i ↦ glUpper j * glLower ((M : 𝓞 K) * Quotient.out i) := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  let _ : Field (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.field _
  have hM₀ : quotientMk (Ideal.span {(q : 𝓞 K)}) (M : 𝓞 K) ≠ 0 := fun h ↦ hqM <|
    Ideal.mem_span_singleton.mp (Quotient.eq_zero_iff_mem.mp h)
  have hj₀ : quotientMk (Ideal.span {(q : 𝓞 K)}) j ≠ 0 := fun h ↦ hj <|
    Ideal.mem_span_singleton.mp (Quotient.eq_zero_iff_mem.mp h)
  refine ⟨fun p ↦ ?_, fun γ hγ ↦ ?_⟩
  · rcases p with _ | i
    · exact one_mem _
    · exact mul_mem (glUpper_mem_gamma0GL _ _)
        (glLower_mem_gamma0GL_iff.mpr (dvd_mul_right _ _))
  · have hM : (M : 𝓞 K) ∣ γ.val 1 0 := mem_gamma0GL_span_iff.mp hγ
    have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 =
        (GeneralLinearGroup.det γ : (𝓞 K)ˣ) := det_eq_of_gl γ
    have key0 : (1 : GL (Fin 2) (𝓞 K)) * γ⁻¹ ∈ gamma0Upper M q ↔
        quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) = 0 := by
      rw [one_mul, mem_gamma0Upper_iff, coe_inv_gl]
      simp only [Matrix.smul_apply, of_apply, cons_val_zero, cons_val_one, smul_eq_mul]
      rw [IsUnit.dvd_mul_left (Units.isUnit _), IsUnit.dvd_mul_left (Units.isUnit _), dvd_neg,
        dvd_neg, and_iff_right hM, Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    have key (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glUpper j *
        glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹ ∈ gamma0Upper M q ↔
          quotientMk (Ideal.span {(q : 𝓞 K)}) j * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) =
              quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) *
                (1 + quotientMk (Ideal.span {(q : 𝓞 K)}) j *
                  quotientMk (Ideal.span {(q : 𝓞 K)}) (M : 𝓞 K) * i) := by
      have h₁ : (glUpper j * glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹).val 1 0 =
          ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val *
            ((M : 𝓞 K) * Quotient.out i * γ.val 1 1 - γ.val 1 0) := by
        rw [Units.val_mul, Units.val_mul, coe_glUpper, coe_glLower, coe_inv_gl]
        simp
        ring1
      have h₂ : (glUpper j * glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹).val 0 1 =
          ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val *
            (j * γ.val 0 0 - γ.val 0 1 * (1 + j * (M : 𝓞 K) * Quotient.out i)) := by
        rw [Units.val_mul, Units.val_mul, coe_glUpper, coe_glLower, coe_inv_gl]
        simp
        ring1
      rw [mem_gamma0Upper_iff, h₁, h₂, IsUnit.dvd_mul_left (Units.isUnit _),
        IsUnit.dvd_mul_left (Units.isUnit _),
        and_iff_right (dvd_sub ((dvd_mul_right _ _).mul_right _) hM),
        ← Ideal.mem_span_singleton, ← Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      simp only [map_mul, map_add, map_one, quotientMk_out]
    by_cases hb : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) = 0
    · have ha : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) ≠ 0 := by
        intro ha
        refine unit_ne_zero_residue hq (GeneralLinearGroup.det γ) ?_
        rw [← hdet, map_sub, map_mul, map_mul, ha, hb, zero_mul, zero_mul, sub_zero]
      refine ⟨none, key0.mpr hb, ?_⟩
      rintro (_ | i) hi
      · rfl
      · have h : quotientMk (Ideal.span {(q : 𝓞 K)}) j *
            quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) =
              quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) *
                (1 + quotientMk (Ideal.span {(q : 𝓞 K)}) j *
                  quotientMk (Ideal.span {(q : 𝓞 K)}) (M : 𝓞 K) * i) :=
          (key i).mp hi
        rw [hb, zero_mul] at h
        exact absurd h (mul_ne_zero hj₀ ha)
    · refine ⟨some ((quotientMk _ j * quotientMk _ (γ.val 0 0) /
        quotientMk _ (γ.val 0 1) - 1) / (quotientMk _ j *
          quotientMk _ (M : 𝓞 K))), ?_, ?_⟩
      · refine (key _).mpr ?_
        field_simp
        ring1
      · rintro (_ | i) hi
        · exact absurd (key0.mp hi) hb
        · have h : quotientMk (Ideal.span {(q : 𝓞 K)}) j *
              quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 0) =
                quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 0 1) *
                  (1 + quotientMk (Ideal.span {(q : 𝓞 K)}) j *
                    quotientMk (Ideal.span {(q : 𝓞 K)}) (M : 𝓞 K) * i) :=
            (key i).mp hi
          refine congrArg some ?_
          field_simp
          linear_combination -h

lemma bianchiPeriodAverage_eq (hk : Even k) : bianchiPeriodAverage σ k q F =
    (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ •
      bianchiLevelRaise σ k q (bianchiUpOperator σ k q F) := by
  rw [bianchiPeriodAverage, bianchiUpOperator, bianchiLevelRaise_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [bianchiLevelRaise, glSlash, bianchiLevelLower, ← bianchiGLSlash_mul hk,
    ← bianchiGLSlash_mul hk]
  refine (bianchiGLSlash_of_coe_eq_smul hk (c := (bianchiUnit q : K)) ?_
    (bianchiUnit q).ne_zero).symm
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [heckeUpper, heckeLower, coe_glUpper, mul_apply, mul_div_cancel₀]

lemma bianchiLevelTrace_eq_self
    (hF : IsBianchiSlashInvariant σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k F) :
    bianchiLevelTrace σ k M q F = F := by
  have h (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :
      glSlash σ k (glLower ((M : 𝓞 K) * Quotient.out i)) F = F :=
    hF.glSlash_eq (glLower_mem_gamma0GL_iff.mpr (dvd_mul_right _ _))
  simp only [bianchiLevelTrace, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_residue_ne_zero q), one_smul]

/-- **The trace commutes with the level raising**: in even weight,
`Tr_{dM, q} (G ∣ (d, 0; 0, 1)) = (Tr_{M, q} G) ∣ (d, 0; 0, 1)`, as `(d, 0; 0, 1)` conjugates the
representatives `(1, 0; dM i, 1)` to `(1, 0; M i, 1)`. -/
lemma bianchiLevelTrace_bianchiLevelRaise (hk : Even k) :
    bianchiLevelTrace σ k (d * M) q (bianchiLevelRaise σ k d G) =
      bianchiLevelRaise σ k d (bianchiLevelTrace σ k M q G) := by
  simp only [bianchiLevelTrace, bianchiLevelRaise_smul, bianchiLevelRaise_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Submonoid.coe_mul, mul_assoc, glSlash_glLower_bianchiLevelRaise _ hk]

lemma bianchiLevelTrace_bianchiPeriodAverage (hk : Even k) :
    bianchiLevelTrace σ k (q * M) q (bianchiPeriodAverage σ k q F) =
      (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ •
        (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ •
          bianchiLevelRaise σ k q (∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
            glSlash σ k (glLower ((M : 𝓞 K) * Quotient.out i)) (bianchiUpOperator σ k q F)) := by
  have h (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :
      glSlash σ k (glLower (((q * M : (𝓞 K)⁰) : 𝓞 K) * Quotient.out i))
        ((Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ •
          bianchiLevelRaise σ k q (bianchiUpOperator σ k q F)) =
            (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ • bianchiLevelRaise σ k q
              (glSlash σ k (glLower ((M : 𝓞 K) * Quotient.out i)) (bianchiUpOperator σ k q F)) := by
    rw [glSlash_smul, Submonoid.coe_mul, mul_assoc, glSlash_glLower_bianchiLevelRaise _ hk]
  rw [bianchiPeriodAverage_eq hk, bianchiLevelTrace, bianchiLevelRaise_sum]
  simp only [h, Finset.smul_sum]

lemma bianchiTraceConstant_ne_zero (hq : Prime (q : 𝓞 K)) : bianchiTraceConstant M q ≠ 0 := by
  rw [bianchiTraceConstant]
  split_ifs
  · exact one_ne_zero
  · intro h
    have hn : (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) ≠ 0 := card_residue_ne_zero q
    have h₁ : (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) *
        (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) = 1 := by
      field_simp at h
      linear_combination h
    have h₂ : Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) *
        Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) = 1 := by
      exact_mod_cast h₁
    exact (one_lt_card_residue hq).ne' (Nat.eq_one_of_mul_eq_one_right h₂)

lemma sum_glSlash_glLower_bianchiUpOperator_of_not_dvd (hk : Even k) (hq : Prime (q : 𝓞 K))
    (hqM : ¬(q : 𝓞 K) ∣ M)
    (hF : IsBianchiSlashInvariant σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k F) :
    ∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, glSlash σ k (glLower ((M : 𝓞 K) * Quotient.out i))
        (bianchiUpOperator σ k q F) = bianchiLevelLower σ k q F +
      ((Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) - 1) • bianchiLowerTrace σ k M q F := by
  have hinv (δ : GL (Fin 2) (𝓞 K)) (hδ : δ ∈ gamma0Upper M q) :
      glSlash σ k δ (bianchiLevelLower σ k q F) = bianchiLevelLower σ k q F :=
    glSlash_bianchiLevelLower hk hF hδ
  let φ : GL (Fin 2) (𝓞 K) → HyperbolicThreeSpace → Fin (k + 1) → ℂ :=
    fun x ↦ glSlash σ k x (bianchiLevelLower σ k q F)
  have hφ : ∀ δ ∈ gamma0Upper M q, ∀ x, φ (δ * x) = φ x := fun δ hδ x ↦ by
    simp only [φ]
    rw [glSlash_mul hk, hinv δ hδ]
  have hzero (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) (hj : j = 0) : ∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
        φ (glUpper (Quotient.out j) * glLower ((M : 𝓞 K) * Quotient.out i)) =
          (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) • bianchiLevelLower σ k q F := by
    have h₁ : (q : 𝓞 K) ∣ Quotient.out j := by
      rw [← Ideal.mem_span_singleton, ← Quotient.eq_zero_iff_mem, quotientMk_out, hj]
    have h₂ (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) :
        φ (glUpper (Quotient.out j) * glLower ((M : 𝓞 K) * Quotient.out i)) =
          bianchiLevelLower σ k q F := by
      refine hinv _ ⟨?_, ?_⟩
      · simp [coe_glUpper, coe_glLower]
      · simpa [coe_glUpper, coe_glLower] using h₁
    simp only [h₂, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul ℂ]
  have hnz (j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) (hj : j ≠ 0) : ∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
        φ (glUpper (Quotient.out j) * glLower ((M : 𝓞 K) * Quotient.out i)) =
          bianchiLowerTrace σ k M q F - bianchiLevelLower σ k q F := by
    have h₁ : ¬(q : 𝓞 K) ∣ Quotient.out j := fun h ↦ hj <| by
      rw [← quotientMk_out j]
      exact Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
    have h₂ : ∑ i : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}), φ (i.elim 1 fun i ↦
        glUpper (Quotient.out j) * glLower ((M : 𝓞 K) * Quotient.out i)) =
          ∑ i : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}), φ (i.elim 1 fun i ↦
            glUpper 1 * glLower ((M : 𝓞 K) * Quotient.out i)) :=
      (isRightTransversal_option hq hqM h₁).sum_eq
        (isRightTransversal_option hq hqM (not_dvd_one_of_prime hq)) hφ
    rw [Fintype.sum_option] at h₂
    have h₃ : φ 1 = bianchiLevelLower σ k q F := glSlash_one
    simp only [Option.elim_none] at h₂
    rw [h₃] at h₂
    have h₄ : bianchiLevelLower σ k q F + ∑ i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)},
        φ (glUpper (Quotient.out j) * glLower ((M : 𝓞 K) * Quotient.out i)) =
          bianchiLowerTrace σ k M q F := h₂
    rw [← h₄, add_sub_cancel_left]
  have hU (x : 𝓞 K) : glSlash σ k (glLower x) (bianchiUpOperator σ k q F) =
      ∑ j : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}, φ (glUpper (Quotient.out j) * glLower x) := by
    rw [bianchiUpOperator, glSlash_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (glSlash_mul hk).symm
  simp only [hU]
  classical
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ
    (0 : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})), hzero 0 rfl, Finset.sum_congr rfl fun j hj ↦
      hnz j (Finset.ne_of_mem_erase hj), Finset.sum_const, Finset.card_erase_of_mem
        (Finset.mem_univ _), Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have hn : 1 ≤ Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Fintype.card_pos
  rw [Nat.cast_sub hn, Nat.cast_one]
  module

variable [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)]

/-- **The trace of a cuspidal function along a coset transversal is a cusp form**: for `H` cuspidal
(`IsBianchiCuspFunction`), invariant under `Γ'`, and `r` a system of representatives of the right
cosets of `Γ'` in `Γ₀(N)`, the function `∑_i H ∣ r_i` lies in `S_k(N)`, in even weight. -/
lemma sum_glSlash_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k) {ι : Type*} [Fintype ι]
    {Γ' : Subgroup (GL (Fin 2) (𝓞 K))} {r : ι → GL (Fin 2) (𝓞 K)}
    (hr : IsRightTransversal Γ' (Ideal.span {(N : 𝓞 K)}).gamma0GL r)
    (hH : IsBianchiCuspFunction σ k H) (hinv : ∀ δ ∈ Γ', glSlash σ k δ H = H) :
    (∑ i, glSlash σ k (r i) H) ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k := by
  refine (mem_bianchiCuspForms_iff hK (ne_bot_span N)).mpr
    ⟨IsBianchiCuspFunction.sum hK _ fun i _ ↦
      hH.slash hK hk (isSLRepresentative_slRepresentative _),
      isBianchiSlashInvariant_of_glSlash_eq hk fun γ hγ ↦ ?_⟩
  rw [glSlash_sum]
  have h (i : ι) : glSlash σ k γ (glSlash σ k (r i) H) = glSlash σ k (r i * γ) H :=
    (glSlash_mul hk).symm
  simp only [h]
  exact (hr.mul_right hγ).sum_eq hr (φ := fun x ↦ glSlash σ k x H) fun δ hδ x ↦ by
    rw [glSlash_mul hk, hinv δ hδ]

lemma bianchiCuspForms_mono (hK : finrank ℚ K = 2) (hMN : (M : 𝓞 K) ∣ N)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k) :
    F ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k := by
  rcases (mem_bianchiCuspForms_iff hK (ne_bot_span M)).mp hF with ⟨h₁, h₂⟩
  refine (mem_bianchiCuspForms_iff hK (ne_bot_span N)).mpr ⟨h₁, fun γ hγ ↦ h₂ γ ?_⟩
  exact mem_gamma0GL_span_iff.mpr (hMN.trans (mem_gamma0GL_span_iff.mp hγ))

/-- **The level raising**: for `G` in `S_k(M)`, in even weight, the function `G ∣ (d, 0; 0, 1)` lies
in `S_k(dM)`, as `(d, 0; 0, 1) (a, b; dc, e) = (a, db; c, e) (d, 0; 0, 1)`. -/
lemma bianchiLevelRaise_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hG : G ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k) : bianchiLevelRaise σ k d G ∈
    bianchiCuspForms σ (Ideal.span {((d * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k := by
  rcases (mem_bianchiCuspForms_iff hK (ne_bot_span M)).mp hG with ⟨h₁, h₂⟩
  refine (mem_bianchiCuspForms_iff hK (ne_bot_span _)).mpr
    ⟨h₁.slash hK hk (isSLRepresentative_slRepresentative _),
      isBianchiSlashInvariant_of_glSlash_eq hk fun γ hγ ↦ ?_⟩
  rcases mem_gamma0GL_span_iff.mp hγ with ⟨c, hc⟩
  rw [Submonoid.coe_mul] at hc
  have hdet : IsUnit (!![γ.val 0 0, (d : 𝓞 K) * γ.val 0 1; (M : 𝓞 K) * c, γ.val 1 1]).det := by
    have h : (!![γ.val 0 0, (d : 𝓞 K) * γ.val 0 1; (M : 𝓞 K) * c, γ.val 1 1]).det =
        (GeneralLinearGroup.det γ : (𝓞 K)ˣ) := by
      rw [← det_eq_of_gl, det_fin_two_of, hc]
      ring1
    rw [h]
    exact Units.isUnit _
  let γ' : GL (Fin 2) (𝓞 K) := GeneralLinearGroup.mk'' _ hdet
  have hγ' : γ' ∈ (Ideal.span {(M : 𝓞 K)}).gamma0GL :=
    mem_gamma0GL_span_iff.mpr ⟨c, rfl⟩
  have hmat : heckeLower (bianchiUnit d) * GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ =
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ' * heckeLower (bianchiUnit d) := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heckeLower, γ', mul_apply, hc, coe_bianchiUnit, mul_comm]
    ring1
  rw [bianchiLevelRaise, glSlash, ← bianchiGLSlash_mul hk, hmat, bianchiGLSlash_mul hk]
  exact congrArg _ (h₂.glSlash_eq hγ')

/-- **`U_q` lowers the level**: for a prime `q ∣ M`, in even weight, and `F` in `S_k(qM)`, `U_q F`
lies in `S_k(M)`, the translations `(1, j; 0, 1)` representing the cosets of `Γ₀(M) ∩ Γ⁰(q)` in
`Γ₀(M)`. -/
lemma bianchiUpOperator_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K)) (hqM : (q : 𝓞 K) ∣ M)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k) :
    bianchiUpOperator σ k q F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k := by
  rcases (mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hF with ⟨h₁, h₂⟩
  exact sum_glSlash_mem_bianchiCuspForms hK hk (isRightTransversal_glUpper hq hqM)
    (h₁.slash hK hk (isSLRepresentative_slRepresentative _))
    fun δ hδ ↦ glSlash_bianchiLevelLower hk h₂ hδ

/-- **`E_q` raises the level by `q`**: for a prime `q ∣ M`, in even weight, and `F` in `S_k(M)`,
`E_q F` lies in `S_k(Mq)`, being `n⁻¹ (U_q F) ∣ (q, 0; 0, 1)` with `U_q F` in `S_k(M)`. -/
lemma bianchiPeriodAverage_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K)) (hqM : (q : 𝓞 K) ∣ M)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k) :
    bianchiPeriodAverage σ k q F ∈
      bianchiCuspForms σ (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k := by
  have hU : bianchiUpOperator σ k q F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k :=
    bianchiUpOperator_mem_bianchiCuspForms hK hk hq hqM
      (bianchiCuspForms_mono hK (Dvd.intro_left _ rfl) hF)
  have h : bianchiLevelRaise σ k q (bianchiUpOperator σ k q F) ∈
      bianchiCuspForms σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k :=
    bianchiLevelRaise_mem_bianchiCuspForms hK hk hU
  rw [mul_comm q M] at h
  rw [bianchiPeriodAverage_eq hk]
  exact Submodule.smul_mem _ _ h

/-- **The trace lowers the level by `q`**: for a prime `q ∣ M`, in even weight, and `H` in
`S_k(Mq)`, `Tr H` lies in `S_k(M)`. -/
lemma bianchiLevelTrace_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K)) (hqM : (q : 𝓞 K) ∣ M)
    (hH : H ∈ bianchiCuspForms σ (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k) :
    bianchiLevelTrace σ k M q H ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k := by
  rcases (mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hH with ⟨h₁, h₂⟩
  exact Submodule.smul_mem _ _ <| sum_glSlash_mem_bianchiCuspForms hK hk
    (isRightTransversal_glLower hq hqM) h₁ fun δ hδ ↦ h₂.glSlash_eq hδ

lemma bianchiLowerTrace_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K)) (hqM : ¬(q : 𝓞 K) ∣ M)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k) :
    bianchiLowerTrace σ k M q F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k := by
  rcases (mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hF with ⟨h₁, h₂⟩
  exact sum_glSlash_mem_bianchiCuspForms hK hk
    (isRightTransversal_option hq hqM (not_dvd_one_of_prime hq))
    (h₁.slash hK hk (isSLRepresentative_slRepresentative _))
    fun δ hδ ↦ glSlash_bianchiLevelLower hk h₂ hδ

/-- **The function `Z` of the key identity has level `M`**. -/
lemma bianchiTraceRemainder_mem_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K))
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k) :
    bianchiTraceRemainder σ k M q F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k := by
  rw [bianchiTraceRemainder]
  split_ifs with hqM
  · exact Submodule.smul_mem _ _ (bianchiUpOperator_mem_bianchiCuspForms hK hk hq hqM hF)
  · exact Submodule.smul_mem _ _ (bianchiLowerTrace_mem_bianchiCuspForms hK hk hq hqM hF)

/-- **The key identity of the Main Lemma**: for a prime `q`, in even weight, and `F` in `S_k(qM)`,
`F - Tr (E_q F) = c (F - Z ∣ (q, 0; 0, 1))` with `c = bianchiTraceConstant M q ≠ 0` and
`Z = bianchiTraceRemainder σ k M q F` in `S_k(M)`. If `q ∣ M`, then
`Tr (E_q F) = n⁻¹ (U_q F) ∣ (q, 0; 0, 1)` with `U_q F` of level `M`, so `c = 1`. If `q ∤ M`, then
`n² Tr (E_q F) = F + (n - 1) Y ∣ (q, 0; 0, 1)` with `Y` the trace of `F ∣ (1, 0; 0, q)` from
`Γ₀(M) ∩ Γ⁰(q)` to `Γ₀(M)`, so `c = 1 - n⁻²`. -/
lemma sub_bianchiLevelTrace_bianchiPeriodAverage (hK : finrank ℚ K = 2) (hk : Even k)
    (hq : Prime (q : 𝓞 K))
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k) : F -
      bianchiLevelTrace σ k (q * M) q (bianchiPeriodAverage σ k q F) = bianchiTraceConstant M q •
        (F - bianchiLevelRaise σ k q (bianchiTraceRemainder σ k M q F)) := by
  have hn : (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ) ≠ 0 := card_residue_ne_zero q
  by_cases hqM : (q : 𝓞 K) ∣ M
  · have hU : bianchiUpOperator σ k q F ∈ bianchiCuspForms σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k :=
      bianchiUpOperator_mem_bianchiCuspForms hK hk hq hqM hF
    have h₁ : IsBianchiSlashInvariant σ (Ideal.span {(M : 𝓞 K)}).gamma0GL k
        (bianchiUpOperator σ k q F) := ((mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hU).2
    have h₂ (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glSlash σ k (glLower ((M : 𝓞 K) * Quotient.out i))
        (bianchiUpOperator σ k q F) = bianchiUpOperator σ k q F :=
      h₁.glSlash_eq (glLower_mem_gamma0GL_iff.mpr (dvd_mul_right _ _))
    rw [bianchiLevelTrace_bianchiPeriodAverage hk, bianchiTraceConstant, bianchiTraceRemainder,
      ite_eq_left hqM, ite_eq_left hqM, one_smul, bianchiLevelRaise_smul]
    simp only [h₂, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, bianchiLevelRaise_smul, smul_smul
      (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ (Fintype.card (𝓞 K ⧸ _) : ℂ),
      inv_mul_cancel₀ hn, one_smul]
  · have hc : bianchiTraceConstant M q ≠ 0 := bianchiTraceConstant_ne_zero hq
    have h₀ : bianchiTraceConstant M q = 1 - (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ *
        (Fintype.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : ℂ)⁻¹ := ite_eq_right hqM
    have hinv : IsBianchiSlashInvariant σ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k F :=
      ((mem_bianchiCuspForms_iff hK (ne_bot_span _)).mp hF).2
    rw [bianchiLevelTrace_bianchiPeriodAverage hk, sum_glSlash_glLower_bianchiUpOperator_of_not_dvd
      hk hq hqM hinv, bianchiLevelRaise_add, bianchiLevelRaise_smul,
      bianchiLevelRaise_bianchiLevelLower hk, bianchiTraceRemainder, ite_eq_right hqM,
      bianchiLevelRaise_smul, smul_sub, smul_smul (bianchiTraceConstant M q), mul_div_cancel₀ _ hc,
      h₀]
    module

end HyperbolicThreeSpace
