import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.CuspFunction

/-!
# The cusp forms of level `Γ₀(𝔑)` as invariant cuspidal functions

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑` a
nonzero ideal of `𝒪_K`. For `g ∈ SL₂(K)`, the `a ∈ K` such that `g (1, a; 0, 1) g⁻¹` lies in the
level `Γ₀(𝔑)` form an `𝒪_K`-submodule of `K` (`cuspTranslationSubmodule`), as this condition says
that the matrix `a g E g⁻¹`, `E = (0, 1; 0, 0)`, is integral with lower left entry in `𝔑`, and it is
principal, `𝒪_K` being a principal ideal domain. So the group of translations of `Γ₀(𝔑)` at the cusp
`g ∞` (`cuspTranslations`) is a lattice `σ(u𝒪_K)` (`exists_cuspTranslations_gamma0GL_eq`). Hence the
forms of `S_k(Γ₀(𝔑))` are exactly the cuspidal functions (`IsBianchiCuspFunction`) invariant under
`Γ₀(𝔑)` (`mem_bianchiCuspForms_iff`), and the Hecke operators preserve the cusp forms
(`bianchiHeckeOperatorModularForms_mem_bianchiCuspForms`).

## Main definitions

* `HyperbolicThreeSpace.cuspTranslationSubmodule`: the `𝒪_K`-module of the translations of `Γ₀(𝔑)`
  at a cusp.

## Main results

* `HyperbolicThreeSpace.mem_cuspTranslationSubmodule_iff`: its elements are the translations of
  `Γ₀(𝔑)` at the cusp.
* `HyperbolicThreeSpace.exists_cuspTranslationSubmodule_eq_span`: it is principal.
* `HyperbolicThreeSpace.exists_cuspTranslations_gamma0GL_eq`: the lattices of translations of
  `Γ₀(𝔑)`.
* `HyperbolicThreeSpace.IsBianchiSlashInvariant.bianchiCuspSection_add_eq`: invariant functions are
  periodic at the cusps.
* `HyperbolicThreeSpace.mem_bianchiCuspForms_iff`: a cusp form is an invariant cuspidal function.
* `HyperbolicThreeSpace.bianchiHeckeOperatorModularForms_mem_bianchiCuspForms`: the Hecke operators
  preserve the cusp forms.
-/

open Complex Matrix MeasureTheory Module NumberField HilbertModularGroup

open scoped ComplexConjugate MatrixGroups nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ} {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
  (g : SL(2, K)) {y : ℝ} (x : ℂ) {𝔑 : Ideal (𝓞 K)} {a : K}

variable (𝔑) in
/-- The `𝒪_K`-module of the translations of `Γ₀(𝔑)` at the cusp `g ∞`, for `g ∈ SL₂(K)`: the
`a ∈ K` such that `g (1, a; 0, 1) g⁻¹ ∈ Γ₀(𝔑)`, that is, such that the matrix `a g E g⁻¹`,
`E = (0, 1; 0, 0)`, has integral entries, with lower left entry in `𝔑`
(`mem_cuspTranslationSubmodule_iff`). -/
noncomputable def cuspTranslationSubmodule : Submodule (𝓞 K) K where
  carrier := {a | ∃ W : Matrix (Fin 2) (Fin 2) (𝓞 K), W.map (algebraMap (𝓞 K) K) =
    a • ((g : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 0, 0] *
      ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧ W 1 0 ∈ 𝔑}
  add_mem' := by
    rintro a b ⟨W, hW, hW'⟩ ⟨V, hV, hV'⟩
    refine ⟨W + V, ?_, 𝔑.add_mem hW' hV'⟩
    rw [Matrix.map_add _ (map_add _), hW, hV, add_smul]
  zero_mem' := ⟨0, by simp, 𝔑.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨W, hW, hW'⟩
    refine ⟨c • W, ?_, 𝔑.mul_mem_left c hW'⟩
    ext i j
    have h₁ : W.map (algebraMap (𝓞 K) K) i j = (a • ((g : Matrix (Fin 2) (Fin 2) K) *
        !![0, 1; 0, 0] * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) :
          Matrix (Fin 2) (Fin 2) K) i j :=
      congrFun (congrFun hW i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h₁ ⊢
    rw [map_mul, h₁, Algebra.smul_def]
    ring1

/-- **The translations of `Γ₀(𝔑)` at a cusp**: `a ∈ K` lies in `cuspTranslationSubmodule g 𝔑`
exactly when `g (1, a; 0, 1) g⁻¹` lies in the level `Γ₀(𝔑)`. -/
lemma mem_cuspTranslationSubmodule_iff : a ∈ cuspTranslationSubmodule g 𝔑 ↔ ∃ γ ∈ 𝔑.gamma0GL,
    (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map (algebraMap (𝓞 K) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * !![1, a; 0, 1] * (g⁻¹ : SL(2, K)) := by
  rw [mul_unipotent_mul_inv]
  refine ⟨?_, ?_⟩
  · rintro ⟨W, hW, hW'⟩
    have hmap : (1 + W).map (algebraMap (𝓞 K) K) = 1 + a • ((g : Matrix (Fin 2) (Fin 2) K) *
        !![0, 1; 0, 0] * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), hW]
    have hdet : (1 + W).det = 1 := by
      refine RingOfIntegers.coe_injective ?_
      have h₁ : algebraMap (𝓞 K) K (1 + W).det = ((1 + W).map (algebraMap (𝓞 K) K)).det :=
        RingHom.map_det _ _
      have h₂ : (g : Matrix (Fin 2) (Fin 2) K) * !![1, a; 0, 1] *
          ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = (1 + W).map (algebraMap (𝓞 K) K) := by
        rw [hmap, mul_unipotent_mul_inv]
      have h₃ : ((1 + W).map (algebraMap (𝓞 K) K)).det = 1 := by
        rw [← h₂, det_mul, det_mul, SpecialLinearGroup.det_coe, SpecialLinearGroup.det_coe]
        simp
      simp only [map_one]
      exact h₁.trans h₃
    refine ⟨SpecialLinearGroup.toGL ⟨1 + W, hdet⟩, ?_, hmap⟩
    have h₁ : (1 + W) 1 0 = W 1 0 := by
      simp
    have h₂ : (1 + W) 1 0 ∈ 𝔑 := by
      rwa [h₁]
    exact h₂
  · rintro ⟨γ, hγ, he⟩
    refine ⟨γ.val - 1, ?_, ?_⟩
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), he,
        add_sub_cancel_left]
    · have h₁ : (γ.val - 1) 1 0 = γ.val 1 0 := by
        simp
      rw [h₁]
      exact hγ

/-- **Invariant functions are periodic at the cusps**: if `F` is invariant under `Γ` and
`g (1, a; 0, 1) g⁻¹ ∈ Γ`, for `g ∈ SL₂(K)` and `a ∈ K`, then
`(F ∣_k g)(x + σ(a), y) = (F ∣_k g)(x, y)` for `y > 0`. -/
lemma IsBianchiSlashInvariant.bianchiCuspSection_add_eq {Γ : Subgroup (GL (Fin 2) (𝓞 K))}
    (hF : IsBianchiSlashInvariant σ Γ k F)
    (ha : ∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map (algebraMap (𝓞 K) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * !![1, a; 0, 1] * (g⁻¹ : SL(2, K))) (hy : 0 < y) :
    bianchiCuspSection σ k F g (σ a + x) y = bianchiCuspSection σ k F g x y := by
  rcases ha with ⟨γ, hγ, he⟩
  let n : SL(2, K) := ⟨!![1, a; 0, 1], by simp⟩
  have hinv : bianchiSlash k (SpecialLinearGroup.map σ (g * n * g⁻¹)) F = F := by
    refine hF γ hγ _ 1 ?_
    have h₂ : ((g * n * g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map (algebraMap (𝓞 K) K) := by
      rw [he, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
    ext i j
    have h₃ : σ (((g * n * g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j) =
        σ (algebraMap (𝓞 K) K ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j)) :=
      congrArg σ (congrFun (congrFun h₂ i) j)
    have h₄ :
        ((1 : ℂ)⁻¹ • (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)).map (σ.comp (algebraMap (𝓞 K) K))) i j =
        σ (algebraMap (𝓞 K) K ((γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) i j)) := by
      simp
    rw [h₄]
    exact h₃
  have hmul : SpecialLinearGroup.map σ g * SpecialLinearGroup.map σ n =
      SpecialLinearGroup.map σ (g * n * g⁻¹) * SpecialLinearGroup.map σ g := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h₁ : bianchiSlash k (SpecialLinearGroup.map σ n)
      (bianchiSlash k (SpecialLinearGroup.map σ g) F) =
        bianchiSlash k (SpecialLinearGroup.map σ g) F := by
    rw [← bianchiSlash_mul, hmul, bianchiSlash_mul, hinv]
  have h₁₀ : (SpecialLinearGroup.map σ n : SL(2, ℂ)) 1 0 = 0 :=
    map_zero σ
  have h₀₀ : (SpecialLinearGroup.map σ n : SL(2, ℂ)) 0 0 = 1 :=
    map_one σ
  have h₀₁ : (SpecialLinearGroup.map σ n : SL(2, ℂ)) 0 1 = σ a :=
    rfl
  have hone : !![(1 : ℂ), 0; 0, conj 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h₂ : extend (bianchiSlash k (SpecialLinearGroup.map σ n)
      (bianchiSlash k (SpecialLinearGroup.map σ g) F)) (x, y) =
        symPowMatrix k !![(↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0, 0;
          0, conj ((↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] *ᵥ
        extend (bianchiSlash k (SpecialLinearGroup.map σ g) F)
          ((↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ 2 * x +
            (↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
              (↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 1,
            ‖(↑(SpecialLinearGroup.map σ n) : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 * y) :=
    extend_bianchiSlash_of_apply_one_zero (p := (x, y)) h₁₀ hy
  rw [h₁, h₀₀, h₀₁, hone, symPowMatrix_one, one_mulVec] at h₂
  simp only [one_pow, one_mul, norm_one] at h₂
  rw [bianchiCuspSection, bianchiCuspSection, h₂, add_comm (σ a) x]

lemma cuspTranslations_gamma0GL_eq {u : K}
    (hS : cuspTranslationSubmodule g 𝔑 = Submodule.span (𝓞 K) {u}) :
    cuspTranslations σ 𝔑.gamma0GL g = bianchiScaledLattice σ u := by
  refine le_antisymm ?_ ?_
  · rw [cuspTranslations, AddSubgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ cuspTranslationSubmodule g 𝔑 := mem_cuspTranslationSubmodule_iff g |>.mpr ha
    rw [hS, Submodule.mem_span_singleton] at ha'
    rcases ha' with ⟨c, rfl⟩
    exact mem_bianchiScaledLattice.mpr ⟨c, by rw [Algebra.smul_def, mul_comm]⟩
  · intro l hl
    rcases mem_bianchiScaledLattice.mp hl with ⟨c, rfl⟩
    refine AddSubgroup.subset_closure ⟨u * c, (mem_cuspTranslationSubmodule_iff g).mp ?_, rfl⟩
    rw [hS]
    exact Submodule.mem_span_singleton.mpr ⟨c, by rw [Algebra.smul_def, mul_comm]⟩

lemma IsBianchiSlashInvariant.bianchiCuspSection_add_eq_of_mem {u : K}
    (hF : IsBianchiSlashInvariant σ 𝔑.gamma0GL k F)
    (hS : cuspTranslationSubmodule g 𝔑 = Submodule.span (𝓞 K) {u}) (hy : 0 < y) {l : ℂ}
    (hl : l ∈ bianchiScaledLattice σ u) :
    bianchiCuspSection σ k F g (l + x) y = bianchiCuspSection σ k F g x y := by
  rcases mem_bianchiScaledLattice.mp hl with ⟨c, rfl⟩
  refine hF.bianchiCuspSection_add_eq g x ((mem_cuspTranslationSubmodule_iff g).mp ?_) hy
  rw [hS]
  exact Submodule.mem_span_singleton.mpr ⟨c, by rw [Algebra.smul_def, mul_comm]⟩

variable [NumberField K]

variable [IsPrincipalIdealRing (𝓞 K)] (𝔑) in
/-- **The module of translations of `Γ₀(𝔑)` at a cusp is principal**, as `𝒪_K` is a principal ideal
domain: it is `u𝒪_K` for some `u ≠ 0`. -/
lemma exists_cuspTranslationSubmodule_eq_span (h𝔑 : 𝔑 ≠ ⊥) :
    ∃ u : K, u ≠ 0 ∧ cuspTranslationSubmodule g 𝔑 = Submodule.span (𝓞 K) {u} := by
  let X : Matrix (Fin 2) (Fin 2) K := (g : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 0, 0] *
    ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  have hg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
  have hinv : ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    rfl
  have hX₀₁ : X 0 1 = g 0 0 ^ 2 := by
    simp [X, hinv, mul_apply, sq]
  have hX₁₀ : X 1 0 = -(g 1 0 ^ 2) := by
    simp [X, hinv, mul_apply, sq]
  have he : ∃ e : K, e ≠ 0 ∧ ∀ a ∈ cuspTranslationSubmodule g 𝔑, ∃ z : 𝓞 K, (z : K) = a * e := by
    by_cases hr : g 1 0 = 0
    · have hp : g 0 0 ≠ 0 := fun hp ↦ by simp [hp, hr] at hg
      refine ⟨g 0 0 ^ 2, pow_ne_zero 2 hp, ?_⟩
      rintro a ⟨W, hW, -⟩
      refine ⟨W 0 1, ?_⟩
      have h₁ : W.map (algebraMap (𝓞 K) K) 0 1 = (a • ((g : Matrix (Fin 2) (Fin 2) K) *
          !![0, 1; 0, 0] * ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) :
            Matrix (Fin 2) (Fin 2) K) 0 1 :=
        congrFun (congrFun hW 0) 1
      rw [← hX₀₁]
      exact h₁
    · refine ⟨g 1 0 ^ 2, pow_ne_zero 2 hr, ?_⟩
      rintro a ⟨W, hW, -⟩
      refine ⟨-W 1 0, ?_⟩
      have h₁ : (W 1 0 : K) = a * X 1 0 := congrFun (congrFun hW 1) 0
      rw [hX₁₀] at h₁
      push_cast
      linear_combination -h₁
  rcases he with ⟨e, he₀, he⟩
  rcases IsFractionRing.div_surjective (A := 𝓞 K) e with ⟨e₁, e₂, he₂, rfl⟩
  have he₂' : (algebraMap (𝓞 K) K) e₂ ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero he₂)
  have he₁ : e₁ ≠ 0 := fun h ↦ he₀ (by simp [h])
  have hfrac : IsFractional (𝓞 K)⁰ (cuspTranslationSubmodule g 𝔑) := by
    refine ⟨e₁, mem_nonZeroDivisors_of_ne_zero he₁, fun a ha ↦ ?_⟩
    rcases he a ha with ⟨z, hz⟩
    refine ⟨z * e₂, ?_⟩
    rw [map_mul, Algebra.smul_def]
    have hz' : algebraMap (𝓞 K) K z = a * (algebraMap (𝓞 K) K e₁ / algebraMap (𝓞 K) K e₂) := hz
    rw [hz']
    field_simp
  rcases (FractionalIdeal.isPrincipal (⟨_, hfrac⟩ : FractionalIdeal (𝓞 K)⁰ K)).principal with
    ⟨u, hu⟩
  have hu' : cuspTranslationSubmodule g 𝔑 = Submodule.span (𝓞 K) {u} := hu
  refine ⟨u, ?_, hu'⟩
  rintro rfl
  rw [Submodule.span_singleton_eq_bot.mpr rfl] at hu'
  rcases IsLocalization.exist_integer_multiples_of_finite (𝓞 K)⁰
    (fun ij : Fin 2 × Fin 2 ↦ X ij.1 ij.2) with ⟨d, hd⟩
  choose W₀ hW₀ using hd
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h𝔑 with ⟨n, hn, hn₀⟩
  have hmem : algebraMap (𝓞 K) K (n * d) ∈ cuspTranslationSubmodule g 𝔑 := by
    refine ⟨of fun i j ↦ n * W₀ (i, j), ?_, 𝔑.mul_mem_right _ hn⟩
    ext i j
    have h₁ : algebraMap (𝓞 K) K (W₀ (i, j)) = (d : 𝓞 K) • X (i, j).1 (i, j).2 := hW₀ (i, j)
    simp only [Algebra.smul_def] at h₁
    simp only [Matrix.map_apply, of_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [h₁, mul_assoc]
  rw [hu', Submodule.mem_bot] at hmem
  have h₂ : n * d = 0 := RingOfIntegers.coe_injective (by simpa using hmem)
  exact mul_ne_zero hn₀ (nonZeroDivisors.ne_zero d.2) h₂

variable [IsPrincipalIdealRing (𝓞 K)]

/-- **The lattices of translations of `Γ₀(𝔑)`**: for an imaginary quadratic field `K` of class
number `1` and `g ∈ SL₂(K)`, the group of translations of `Γ₀(𝔑)` at the cusp `g ∞`
(`cuspTranslations`) is `σ(u𝒪_K)` for some `u ≠ 0`. -/
lemma exists_cuspTranslations_gamma0GL_eq (h𝔑 : 𝔑 ≠ ⊥) :
    ∃ u : K, u ≠ 0 ∧ cuspTranslations σ 𝔑.gamma0GL g = bianchiScaledLattice σ u := by
  rcases exists_cuspTranslationSubmodule_eq_span g 𝔑 h𝔑 with ⟨u, hu, hS⟩
  exact ⟨u, hu, cuspTranslations_gamma0GL_eq g hS⟩

variable [IsTotallyComplex K]

/-- **The cusp forms of level `Γ₀(𝔑)` are the invariant cuspidal functions**: for an imaginary
quadratic field `K` of class number `1` and `𝔑 ≠ 0`, a function `F : ℋ₃ → ℂ^{k+1}` lies in
`S_k(Γ₀(𝔑))` exactly when it is cuspidal (`IsBianchiCuspFunction`) and invariant under `Γ₀(𝔑)`. -/
lemma mem_bianchiCuspForms_iff (hK : finrank ℚ K = 2) (h𝔑 : 𝔑 ≠ ⊥) : F ∈
    bianchiCuspForms σ 𝔑.gamma0GL k ↔ IsBianchiCuspFunction σ k F ∧
      IsBianchiSlashInvariant σ 𝔑.gamma0GL k F := by
  refine ⟨fun hF ↦ ⟨⟨hF.1.analyticAt, hF.1.harmonic, hF.1.growth, fun g ↦ ?_⟩, hF.1.invariant⟩,
    fun ⟨hF, hinv⟩ ↦ ⟨⟨hF.analyticAt, hinv, hF.harmonic, hF.growth⟩, fun g y P hy hP ↦ ?_⟩⟩
  · rcases exists_cuspTranslationSubmodule_eq_span g 𝔑 h𝔑 with ⟨u, hu, hS⟩
    refine ⟨u, hu, fun y hy l hl x ↦ hF.1.invariant.bianchiCuspSection_add_eq_of_mem g x hS hy hl,
      fun y P hy hP ↦ (hF.2 g y P hy ?_).2⟩
    rwa [cuspTranslations_gamma0GL_eq g hS]
  · rcases exists_cuspTranslationSubmodule_eq_span g 𝔑 h𝔑 with ⟨u, hu, hS⟩
    rw [cuspTranslations_gamma0GL_eq g hS] at hP
    rcases hF.constantTerm g with ⟨t, ht, hp, hz⟩
    rcases exists_mul_eq_mul ht hu with ⟨w₁, w₂, hw₁, hw₂, he⟩
    have hc : Continuous fun x ↦ bianchiCuspSection σ k F g x y :=
      hF.continuous_bianchiCuspSection g hy
    have hper : ∀ l ∈ bianchiScaledLattice σ u, ∀ x, bianchiCuspSection σ k F g (l + x) y =
        bianchiCuspSection σ k F g x y :=
      fun l hl x ↦ hinv.bianchiCuspSection_add_eq_of_mem g x hS hy hl
    rcases exists_isBounded_isAddFundamentalDomain_bianchiScaledLattice (σ := σ) (t := t * w₁) hK
      (mul_ne_zero ht (RingOfIntegers.coe_ne_zero_iff.mpr hw₁)) with ⟨P₀, -, hP₀⟩
    have h₀ : ∫ x in P₀, bianchiCuspSection σ k F g x y = 0 :=
      setIntegral_eq_zero_of_mul hK ht hw₁ hc (hp y hy) hP₀ fun P hP ↦ hz y P hy hP
    exact ⟨integrableOn_of_continuous_of_periodic hK hu hc hper hP,
      setIntegral_eq_zero_of_mul_eq_zero hK hu hw₂ hc hper hP (he ▸ hP₀) h₀⟩

/-- **The Hecke operators preserve the cusp forms** (LMFDB `mf.bianchi.spaces`): for an imaginary
quadratic field `K` of class number `1` and `𝔑 ≠ 0`, the Hecke operator of a double coset
`Γ₀(𝔑) α Γ₀(𝔑)` on `M_k(Γ₀(𝔑))` maps `S_k(Γ₀(𝔑))` to itself, as a sum of slash operators maps a
cuspidal function to a cuspidal function, and the value of the operator is invariant. -/
lemma bianchiHeckeOperatorModularForms_mem_bianchiCuspForms (hK : finrank ℚ K = 2) [NeZero 𝔑]
    (D : HeckeCoset (glTotallyPositive K) (bianchiGammaZero 𝔑) (bianchiGammaZero 𝔑))
    (Φ : bianchiModularForms σ 𝔑.gamma0GL k)
    (hΦ : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiCuspForms σ 𝔑.gamma0GL k) :
    (bianchiHeckeOperatorModularForms σ k 𝔑 D Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiCuspForms σ 𝔑.gamma0GL k := by
  by_cases hk : Even k
  · have hF : IsBianchiCuspFunction σ k (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
      ((mem_bianchiCuspForms_iff hK (NeZero.ne 𝔑)).mp hΦ).1
    refine (mem_bianchiCuspForms_iff hK (NeZero.ne 𝔑)).mpr
      ⟨?_, (bianchiHeckeOperatorModularForms σ k 𝔑 D Φ).2.invariant⟩
    rw [coe_bianchiHeckeOperatorModularForms]
    exact IsBianchiCuspFunction.sum hK _ fun v _ ↦
      hF.slash hK hk (isSLRepresentative_slRepresentative _)
  · have h₀ : Φ = 0 := Subtype.ext <| Φ.2.invariant.eq_zero_of_odd (Nat.not_even_iff_odd.mp hk)
    rw [h₀, map_zero]
    exact zero_mem _

end HyperbolicThreeSpace
