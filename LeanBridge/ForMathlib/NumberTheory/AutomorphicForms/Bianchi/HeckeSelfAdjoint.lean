import LeanBridge.ForMathlib.MeasureTheory.Group.FundamentalDomainUnfolding
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.FrickeNewform
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.PeterssonProduct

/-!
# The Hecke operators of primes not dividing the level are self-adjoint

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, `N ≠ 0` in
`𝒪_K`, and `q` a prime of `𝒪_K` with `q ∤ N`. Write `h = (1, 0; 0, q)` and `h' = (q, 0; 0, 1)`,
which is a multiple of `h⁻¹`. The double coset `D = Γ₀(N) h Γ₀(N)` of the Hecke operator `T_q` also
contains `h'`. For `r_i` representing the right cosets of `Γ₀(N) ∩ h⁻¹ Γ₀(N) h` in `Γ₀(N)`, the
matrices `h r_i` represent the right cosets in `D`
(`HyperbolicThreeSpace.doubleCoset_eq_iUnion_op_mul_smul`). Here
`Γ₀(N) ∩ h⁻¹ Γ₀(N) h = Γ₀(N) ∩ Γ⁰(q)` and `Γ₀(N) ∩ h'⁻¹ Γ₀(N) h' = Γ₀(Nq)`. So

* `T_q F = ∑_i (F ∣ h) ∣ r_i`, a trace from `Γ₀(N) ∩ Γ⁰(q)` to `Γ₀(N)`
  (`HyperbolicThreeSpace.coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelLower`);
* `T_q G = ∑_i (G ∣ h') ∣ t_i`, a trace from `Γ₀(Nq)` to `Γ₀(N)`
  (`HyperbolicThreeSpace.coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelRaise`).

Unfolding the traces, and using the invariance of the pairing and of the hyperbolic volume,
`⟨T_q F, G⟩` and `⟨F, T_q G⟩` are two integrals of the `Γ₀(Nq)`-invariant function
`y^k ⟨F, G ∣ h'⟩_k` over fundamental domains of `Γ̄₀(Nq)`, so they are equal
(`HyperbolicThreeSpace.bianchiPetersson_bianchiHeckeTPrime`).

The hypothesis `q ∤ N` is necessary: the knowl's "the Hecke operators are all self-adjoint" fails
for the operators `U_𝔭`, `𝔭 ∣ 𝒩`. The same unfolding gives their adjoint in general
(`HyperbolicThreeSpace.bianchiPetersson_sum_glSlash_bianchiLevelLower`).

## Main results

* `HyperbolicThreeSpace.doubleCoset_eq_iUnion_op_mul_smul`: the right cosets in a double coset.
* `HyperbolicThreeSpace.isRightTransversal_gamma0_mul`: the right cosets of `Γ₀(Nq)` in `Γ₀(N)`, for
  `q ∤ N`.
* `HyperbolicThreeSpace.coe_bianchiHeckeTPrime_eq_sum_glSlash`: the Hecke operator along a system of
  right cosets of its double coset.
* `HyperbolicThreeSpace.setIntegral_bianchiPairing_sum_glSlash`: the unfolding of a trace.
* `HyperbolicThreeSpace.isFundamentalDomain_heckeUpper_smul`: `(1, 0; 0, q)` maps a fundamental
  domain of `Γ₀(M) ∩ Γ⁰(q)` to one of `Γ₀(qM)`.
* `HyperbolicThreeSpace.bianchiPetersson_sum_glSlash_bianchiLevelLower`: the adjoint of a trace of
  `F ∣ (1, 0; 0, q)`.
* `HyperbolicThreeSpace.bianchiPetersson_bianchiHeckeTPrime`: `T_𝔭` is self-adjoint on `S_k(𝔑)` for
  a prime `𝔭 ∤ 𝔑`.
-/

open Complex Ideal Matrix MeasureTheory Module NumberField HilbertModularGroup HilbertModularForm
  DoubleCoset MulOpposite

open Ideal renaming Quotient.mk → quotientMk, Quotient.mk_out → quotientMk_out

open Submodule (IsPrincipal)

open scoped ComplexConjugate ENNReal MatrixGroups nonZeroDivisors Pointwise Real

namespace HyperbolicThreeSpace

section Group

variable {G ι : Type*} [Group G] {Γ : Subgroup G} {h : G} {r : ι → G}

/-- **The right cosets in a double coset**: if `r_i ∈ Γ` and every `γ ∈ Γ` has a unique `i` with
`h r_i γ⁻¹ h⁻¹ ∈ Γ`, then `Γ h Γ` is the union of the right cosets `Γ h r_i`. -/
lemma doubleCoset_eq_iUnion_op_mul_smul (hr : ∀ i, r i ∈ Γ)
    (huniq : ∀ γ ∈ Γ, ∃! i, h * (r i * γ⁻¹) * h⁻¹ ∈ Γ) :
    doubleCoset h (Γ : Set G) Γ = ⋃ i, op (h * r i) • (Γ : Set G) :=
  doubleCoset_eq_iUnion_rightCosets_of_forall_exists Γ Γ h _ (fun b hb ↦ by
    rcases (huniq b hb).exists with ⟨i, hi⟩
    exact ⟨i, _, inv_mem hi, by group⟩) fun i ↦ ⟨r i, hr i, rfl⟩

lemma injective_op_mul_smul (hr : ∀ i, r i ∈ Γ) (huniq : ∀ γ ∈ Γ, ∃! i, h * (r i * γ⁻¹) * h⁻¹ ∈ Γ) :
    Function.Injective fun i ↦ op (h * r i) • (Γ : Set G) := by
  intro i j hij
  have h₁ : h * r j * (h * r i)⁻¹ ∈ Γ := (rightCoset_eq_iff _).mp hij
  have e : h * r j * (h * r i)⁻¹ = h * (r j * (r i)⁻¹) * h⁻¹ := by
    group
  rw [e] at h₁
  have h₂ : h * (r i * (r i)⁻¹) * h⁻¹ ∈ Γ := by
    simp
  exact (huniq (r i) (hr i)).unique h₂ h₁

end Group

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ}
  {F G A B : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {M N q : (𝓞 K)⁰} {δ δ' : GL (Fin 2) (𝓞 K)}

lemma exists_mem_gamma0Upper_heckeUpper_mul_eq
    (hδ' : δ' ∈ (Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL) : ∃ δ ∈ gamma0Upper M q,
      heckeUpper (bianchiUnit q) 0 * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ =
        GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeUpper (bianchiUnit q) 0 := by
  rcases mem_gamma0GL_span_iff.mp hδ' with ⟨c, hc⟩
  rw [Submonoid.coe_mul] at hc
  have hdet : IsUnit (!![δ'.val 0 0, (q : 𝓞 K) * δ'.val 0 1; (M : 𝓞 K) * c, δ'.val 1 1]).det := by
    have h : (!![δ'.val 0 0, (q : 𝓞 K) * δ'.val 0 1; (M : 𝓞 K) * c, δ'.val 1 1]).det =
        (GeneralLinearGroup.det δ' : (𝓞 K)ˣ) := by
      rw [← det_eq_of_gl, det_fin_two_of, hc]
      ring1
    rw [h]
    exact Units.isUnit _
  refine ⟨GeneralLinearGroup.mk'' _ hdet, ⟨?_, ?_⟩, ?_⟩
  · exact Dvd.intro _ rfl
  · exact Dvd.intro _ rfl
  · refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heckeUpper, mul_apply, hc, coe_bianchiUnit, mul_comm, mul_left_comm]

lemma dvd_of_heckeUpper_mul_map_eq
    (h : heckeUpper (bianchiUnit q) 0 * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ =
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeUpper (bianchiUnit q) 0) :
    (q : 𝓞 K) ∣ δ.val 0 1 := by
  have h₁ : ((heckeUpper (bianchiUnit q) 0 * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
        ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeUpper (bianchiUnit q) 0 :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 := by
    rw [h]
  simp [heckeUpper, mul_apply, coe_bianchiUnit] at h₁
  refine ⟨δ'.val 0 1, RingOfIntegers.coe_injective ?_⟩
  simpa [mul_comm] using h₁

lemma heckeLower_mul_map_eq_of_mem (hδ : δ ∈ (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL) :
    ∃ δ' ∈ (Ideal.span {(M : 𝓞 K)}).gamma0GL,
      heckeLower (bianchiUnit q) * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ =
        GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeLower (bianchiUnit q) := by
  rcases mem_gamma0GL_span_iff.mp hδ with ⟨c, hc⟩
  rw [Submonoid.coe_mul] at hc
  have hdet : IsUnit (!![δ.val 0 0, (q : 𝓞 K) * δ.val 0 1; (M : 𝓞 K) * c, δ.val 1 1]).det := by
    have h : (!![δ.val 0 0, (q : 𝓞 K) * δ.val 0 1; (M : 𝓞 K) * c, δ.val 1 1]).det =
        (GeneralLinearGroup.det δ : (𝓞 K)ˣ) := by
      rw [← det_eq_of_gl, det_fin_two_of, hc]
      ring1
    rw [h]
    exact Units.isUnit _
  refine ⟨GeneralLinearGroup.mk'' _ hdet, mem_gamma0GL_span_iff.mpr (Dvd.intro _ rfl), ?_⟩
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeLower, mul_apply, hc, coe_bianchiUnit, mul_comm]
  ring1

lemma dvd_of_heckeLower_mul_map_eq (hδ' : δ' ∈ (Ideal.span {(M : 𝓞 K)}).gamma0GL)
    (h : heckeLower (bianchiUnit q) * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ =
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeLower (bianchiUnit q)) :
    δ ∈ (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL := by
  have h₁ : ((heckeLower (bianchiUnit q) * GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
        ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ' * heckeLower (bianchiUnit q) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    rw [h]
  simp [heckeLower, mul_apply, coe_bianchiUnit] at h₁
  rcases mem_gamma0GL_span_iff.mp hδ' with ⟨c, hc⟩
  refine mem_gamma0GL_span_iff.mpr ⟨c, RingOfIntegers.coe_injective ?_⟩
  rw [Submonoid.coe_mul]
  simp only [h₁, hc, map_mul]
  ring1

variable (σ) in
/-- The class in `PSL(2, ℂ)` of a matrix of `GL₂(𝒪_K)`, as a group homomorphism. -/
noncomputable def glToPSLHom : GL (Fin 2) (𝓞 K) →* ProjectiveSpecialLinearGroup (Fin 2) ℂ where
  toFun := glToPSL σ
  map_one' := glToPSL_one σ
  map_mul' := glToPSL_mul σ

variable (σ) in
lemma coe_glToPSLHom (γ : GL (Fin 2) (𝓞 K)) : glToPSLHom σ γ = glToPSL σ γ :=
  rfl

lemma mem_of_glToPSL_eq_one {Γ' : Subgroup (GL (Fin 2) (𝓞 K))}
    (hsc : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ Γ') {z : GL (Fin 2) (𝓞 K)}
    (h : glToPSL σ z = 1) : z ∈ Γ' := by
  have hc : slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z) ∈
      Subgroup.center SL(2, ℂ) := (QuotientGroup.eq_one_iff _).mp h
  rcases isSLRepresentative_slRepresentative (σ := σ)
    (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z) with ⟨s, hs⟩
  have hs₀ : s ≠ 0 := ne_zero_of_coe_eq_inv_smul hs
  rcases SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hc with hc | hc
  · rw [hc] at hs
    have h₀₁ : (1 : SL(2, ℂ)) 0 1 = (s⁻¹ • (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z :
        Matrix (Fin 2) (Fin 2) K).map σ) 0 1 := congrFun (congrFun hs 0) 1
    have h₁₀ : (1 : SL(2, ℂ)) 1 0 = (s⁻¹ • (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z :
        Matrix (Fin 2) (Fin 2) K).map σ) 1 0 := congrFun (congrFun hs 1) 0
    simp [hs₀] at h₀₁ h₁₀
    exact hsc z h₀₁ h₁₀
  · rw [hc] at hs
    have h₀₁ : (-1 : SL(2, ℂ)) 0 1 = (s⁻¹ • (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z :
        Matrix (Fin 2) (Fin 2) K).map σ) 0 1 := congrFun (congrFun hs 0) 1
    have h₁₀ : (-1 : SL(2, ℂ)) 1 0 = (s⁻¹ • (GeneralLinearGroup.map (algebraMap (𝓞 K) K) z :
        Matrix (Fin 2) (Fin 2) K).map σ) 1 0 := congrFun (congrFun hs 1) 0
    simp [hs₀] at h₀₁ h₁₀
    exact hsc z h₀₁ h₁₀

instance (N : (𝓞 K)⁰) : NeZero (N : 𝓞 K) :=
  ⟨nonZeroDivisors.ne_zero N.2⟩

lemma heckeDiagonal_eq_heckeUpper (ϖ : Kˣ) (hϖ : IsTotallyPositive (ϖ : K)) :
    (heckeDiagonal ϖ hϖ : GL (Fin 2) K) = heckeUpper ϖ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeDiagonal, heckeUpper]

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma generator_ne_zero {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥) : IsPrincipal.generator 𝔭 ≠ 0 :=
  fun h ↦ h𝔭 ((IsPrincipal.eq_bot_iff_generator_eq_zero 𝔭).mpr h)

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma prime_generator {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) :
    Prime (IsPrincipal.generator 𝔭) :=
  (Ideal.span_singleton_prime (generator_ne_zero h𝔭)).mp <| by
    rw [Ideal.span_singleton_generator]
    exact h𝔭p

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma exists_coe_eq_generator {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥) :
    ∃ q : (𝓞 K)⁰, (q : 𝓞 K) = IsPrincipal.generator 𝔭 :=
  ⟨⟨_, mem_nonZeroDivisors_of_ne_zero (generator_ne_zero h𝔭)⟩, rfl⟩

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma span_coe_eq_of_coe_eq_generator {𝔭 : Ideal (𝓞 K)} (hq : (q : 𝓞 K) = IsPrincipal.generator 𝔭) :
    Ideal.span {(q : 𝓞 K)} = 𝔭 := by
  rw [hq, Ideal.span_singleton_generator]

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma bianchiUnit_eq_bianchiIdealGenerator {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥)
    (hq : (q : 𝓞 K) = IsPrincipal.generator 𝔭) : bianchiUnit q = bianchiIdealGenerator 𝔭 h𝔭 :=
  Units.ext <| by
    rw [coe_bianchiUnit, hq]
    rfl

variable [IsTotallyComplex K] in
lemma heckeLower_conj_mem_iff {x : GL (Fin 2) (𝓞 K)} : heckeLower (bianchiUnit q) *
    GeneralLinearGroup.map (algebraMap (𝓞 K) K) x * (heckeLower (bianchiUnit q))⁻¹ ∈
      bianchiGammaZero (Ideal.span {(M : 𝓞 K)}) ↔ x ∈
        (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases (mem_bianchiGammaZero_iff _).mp h with ⟨δ', hδ', he⟩
    refine dvd_of_heckeLower_mul_map_eq hδ' ?_
    rw [he, inv_mul_cancel_right]
  · rcases heckeLower_mul_map_eq_of_mem h with ⟨δ', hδ', he⟩
    exact (mem_bianchiGammaZero_iff _).mpr ⟨δ', hδ', by rw [he, mul_inv_cancel_right]⟩

variable [NumberField K] in
/-- **The matrices `(1, 0; M i, 1)`, `i mod q`, and a matrix with second row `(M, q)` represent the
right cosets of `Γ₀(Mq)` in `Γ₀(M)`**, for a prime `q ∤ M`. -/
lemma isRightTransversal_gamma0_mul (hq : Prime (q : 𝓞 K)) {w : GL (Fin 2) (𝓞 K)}
    (hw₁ : w.val 1 0 = M) (hw₂ : w.val 1 1 = q) :
    IsRightTransversal (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL
      (Ideal.span {(M : 𝓞 K)}).gamma0GL fun p : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ↦
        p.elim w fun i ↦ glLower ((M : 𝓞 K) * Quotient.out i) := by
  have : (Ideal.span {(q : 𝓞 K)}).IsMaximal := isMaximal_span_of_prime hq
  let _ : Field (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) := Quotient.field _
  have hM₀ : (M : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero M.2
  refine ⟨fun p ↦ ?_, fun γ hγ ↦ ?_⟩
  · rcases p with _ | i
    · exact mem_gamma0GL_span_iff.mpr (hw₁ ▸ dvd_rfl)
    · exact glLower_mem_gamma0GL_iff.mpr (dvd_mul_right _ _)
  rcases mem_gamma0GL_span_iff.mp hγ with ⟨c, hc⟩
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 =
      (GeneralLinearGroup.det γ : (𝓞 K)ˣ) := det_eq_of_gl γ
  have key₀ : w * γ⁻¹ ∈ (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL ↔
      quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) = 0 := by
    have h : (w * γ⁻¹).val 1 0 = ((GeneralLinearGroup.det γ)⁻¹ : (𝓞 K)ˣ).val *
        ((M : 𝓞 K) * (γ.val 1 1 - (q : 𝓞 K) * c)) := by
      rw [Units.val_mul, coe_inv_gl, hc]
      simp [mul_apply, hw₁, hw₂]
      ring1
    rw [mem_gamma0GL_span_iff, h, IsUnit.dvd_mul_left (Units.isUnit _), Submonoid.coe_mul,
      mul_dvd_mul_iff_left hM₀, ← Ideal.mem_span_singleton, ← Quotient.eq_zero_iff_mem,
      map_sub, map_mul, Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      zero_mul, sub_zero]
  have key (i : 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) : glLower ((M : 𝓞 K) * Quotient.out i) * γ⁻¹ ∈
      (Ideal.span {((M * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL ↔
        i * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) =
          quotientMk (Ideal.span {(q : 𝓞 K)}) c :=
    glLower_mul_inv_mem_gamma0GL_iff hc i
  by_cases hd : quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) = 0
  · refine ⟨none, key₀.mpr hd, ?_⟩
    rintro (_ | i) hi
    · rfl
    · have hc₀ : i * quotientMk (Ideal.span {(q : 𝓞 K)}) (γ.val 1 1) =
          quotientMk (Ideal.span {(q : 𝓞 K)}) c := (key i).mp hi
      rw [hd, mul_zero] at hc₀
      refine absurd ?_ (unit_ne_zero_residue hq (GeneralLinearGroup.det γ))
      rw [← hdet, map_sub, map_mul, map_mul, hd, hc, map_mul, ← hc₀, mul_zero, mul_zero, mul_zero,
        sub_zero]
  · refine ⟨some (quotientMk _ c / quotientMk _ (γ.val 1 1)),
      (key _).mpr (div_mul_cancel₀ _ hd), ?_⟩
    rintro (_ | i) hi
    · exact absurd (key₀.mp hi) hd
    · exact congrArg some (eq_div_of_mul_eq hd ((key i).mp hi))

variable [IsTotallyComplex K] in
lemma heckeUpper_conj_mem_iff {x : GL (Fin 2) (𝓞 K)} (hx : x ∈ (Ideal.span {(M : 𝓞 K)}).gamma0GL) :
    heckeUpper (bianchiUnit q) 0 * GeneralLinearGroup.map (algebraMap (𝓞 K) K) x *
      (heckeUpper (bianchiUnit q) 0)⁻¹ ∈ bianchiGammaZero (Ideal.span {(M : 𝓞 K)}) ↔ x ∈
        gamma0Upper M q := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases (mem_bianchiGammaZero_iff _).mp h with ⟨δ', -, he⟩
    refine ⟨mem_gamma0GL_span_iff.mp hx, dvd_of_heckeUpper_mul_map_eq (δ' := δ') ?_⟩
    rw [he, inv_mul_cancel_right]
  · rcases heckeUpper_mul_map_eq_of_mem h with ⟨δ', hδ', he⟩
    have h₁ : (M : 𝓞 K) ∣ ((q * M : (𝓞 K)⁰) : 𝓞 K) := Dvd.intro_left (q : 𝓞 K) rfl
    refine (mem_bianchiGammaZero_iff _).mpr ⟨δ', mem_gamma0GL_span_iff.mpr
      (h₁.trans (mem_gamma0GL_span_iff.mp hδ')), ?_⟩
    rw [he, mul_inv_cancel_right]

variable [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **The Hecke operator `T_𝔭` along any system of right cosets of its double coset**: if
`h₀ ∈ Γ₀(N) diag(1, π) Γ₀(N)` and `r_i` represents the right cosets of `Γ'` in `Γ₀(N)`, where `Γ'`
consists of the `x ∈ Γ₀(N)` with `h₀ x h₀⁻¹ ∈ Γ₀(N)`, then `T_𝔭 Φ = ∑_i (Φ ∣ h₀) ∣ r_i`. -/
lemma coe_bianchiHeckeTPrime_eq_sum_glSlash {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥) {h₀ : GL (Fin 2) K}
    (hh₀ : h₀ ∈ doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})))
    {ι : Type*} [Fintype ι] {Γ' : Subgroup (GL (Fin 2) (𝓞 K))} {r : ι → GL (Fin 2) (𝓞 K)}
    (hr : IsRightTransversal Γ' (Ideal.span {(N : 𝓞 K)}).gamma0GL r)
    (hkey : ∀ x ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL,
      h₀ * GeneralLinearGroup.map (algebraMap (𝓞 K) K) x * h₀⁻¹ ∈
        bianchiGammaZero (Ideal.span {(N : 𝓞 K)}) ↔ x ∈ Γ')
    (Φ : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    (bianchiHeckeTPrime σ k (Ideal.span {(N : 𝓞 K)}) 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
        ∑ i, glSlash σ k (r i) (bianchiSlash k (slRepresentative σ h₀) Φ) := by
  have hout : doubleCoset ((heckeT 1 (Ideal.span {(N : 𝓞 K)}) (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _)).out : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) =
      doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
        (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
          (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) :=
    Quotient.mk_out (s := HeckeCoset.setoid _ _ _) _
  have hR (i : ι) : GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i) ∈
      bianchiGammaZero (Ideal.span {(N : 𝓞 K)}) :=
    (mem_bianchiGammaZero_iff _).mpr ⟨r i, hr.1 i, rfl⟩
  have huniq : ∀ γ ∈ bianchiGammaZero (Ideal.span {(N : 𝓞 K)}), ∃! i,
      h₀ * (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i) * γ⁻¹) * h₀⁻¹ ∈
        bianchiGammaZero (Ideal.span {(N : 𝓞 K)}) := by
    intro γ hγ
    rcases (mem_bianchiGammaZero_iff _).mp hγ with ⟨γ₀, hγ₀, rfl⟩
    have e (i : ι) : h₀ * (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i) *
        (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ₀)⁻¹) * h₀⁻¹ =
          h₀ * GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i * γ₀⁻¹) * h₀⁻¹ := by
      rw [map_mul, map_inv]
    simp only [e, hkey _ (mul_mem (hr.1 _) (inv_mem hγ₀))]
    exact hr.2 γ₀ hγ₀
  refine (bianchiHeckeOperator_eq_sum σ k (bianchiGammaZero (Ideal.span {(N : 𝓞 K)}))
    (glTotallyPositive K) (heckeT 1 (Ideal.span {(N : 𝓞 K)}) (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _)) ⟨Φ, Φ.2.mem_bianchiSlashInvariants⟩ _
    (hout.trans ((doubleCoset_eq_of_mem hh₀).symm.trans
      (doubleCoset_eq_iUnion_op_mul_smul hR huniq))) (injective_op_mul_smul hR huniq)
    (fun i ↦ slRepresentative σ h₀ *
      slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i)))
    fun i ↦ (isSLRepresentative_slRepresentative _).mul
      (isSLRepresentative_slRepresentative _)).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [bianchiSlash_mul]
  rfl

variable [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **`T_q` as a trace from `Γ₀(N) ∩ Γ⁰(q)` to `Γ₀(N)`**: for a prime `𝔭 = (q)` with `q ∤ N`,
`T_𝔭 Φ = ∑_i (Φ ∣ (1, 0; 0, q)) ∣ r_i`, for `r_i` representing the right cosets of `Γ₀(N) ∩ Γ⁰(q)`
in `Γ₀(N)`. -/
lemma coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelLower {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥)
    (hq : (q : 𝓞 K) = IsPrincipal.generator 𝔭) {ι : Type*} [Fintype ι] {r : ι → GL (Fin 2) (𝓞 K)}
    (hr : IsRightTransversal (gamma0Upper N q) (Ideal.span {(N : 𝓞 K)}).gamma0GL r)
    (Φ : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    (bianchiHeckeTPrime σ k (Ideal.span {(N : 𝓞 K)}) 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
        ∑ i, glSlash σ k (r i) (bianchiLevelLower σ k q Φ) := by
  have hϖ : bianchiUnit q = bianchiIdealGenerator 𝔭 h𝔭 :=
    bianchiUnit_eq_bianchiIdealGenerator h𝔭 hq
  refine coe_bianchiHeckeTPrime_eq_sum_glSlash h𝔭 (h₀ := heckeUpper (bianchiUnit q) 0) ?_ hr
    (fun x hx ↦ heckeUpper_conj_mem_iff hx) Φ
  rw [hϖ, ← heckeDiagonal_eq_heckeUpper _ (isTotallyPositive_of_isTotallyComplex _)]
  exact mem_doubleCoset_self _ _ _

variable [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **`T_q` as a trace from `Γ₀(Nq)` to `Γ₀(N)`**: for a prime `𝔭 = (q)` with `𝔭 ⊔ (N) = 𝒪_K`,
`T_𝔭 Φ = ∑_i (Φ ∣ (q, 0; 0, 1)) ∣ t_i`, for `t_i` representing the right cosets of `Γ₀(Nq)` in
`Γ₀(N)`. -/
lemma coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelRaise {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ Ideal.span {(N : 𝓞 K)} = ⊤)
    (hq : (q : 𝓞 K) = IsPrincipal.generator 𝔭) {ι : Type*} [Fintype ι] {t : ι → GL (Fin 2) (𝓞 K)}
    (ht : IsRightTransversal (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL
      (Ideal.span {(N : 𝓞 K)}).gamma0GL t)
    (Φ : bianchiModularForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    (bianchiHeckeTPrime σ k (Ideal.span {(N : 𝓞 K)}) 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
        ∑ i, glSlash σ k (t i) (bianchiLevelRaise σ k q Φ) := by
  have hϖ : bianchiUnit q = bianchiIdealGenerator 𝔭 h𝔭 :=
    bianchiUnit_eq_bianchiIdealGenerator h𝔭 hq
  have hspan : Ideal.span {(q : 𝓞 K)} = 𝔭 := span_coe_eq_of_coe_eq_generator hq
  refine coe_bianchiHeckeTPrime_eq_sum_glSlash h𝔭 (h₀ := heckeLower (bianchiUnit q)) ?_ ht
    (fun x _ ↦ heckeLower_conj_mem_iff) Φ
  have hunion : doubleCoset (heckeDiagonal (bianchiUnit q)
      (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) =
      ⋃ r, op (heckeCosetRep (bianchiUnit q) 1 r) •
        (bianchiGammaZero (Ideal.span {(N : 𝓞 K)}) : Set (GL (Fin 2) K)) :=
    doubleCoset_heckeDiagonal_eq_iUnion (p := q) (hspan ▸ h𝔭p) (hspan ▸ h𝔭𝔑) rfl
  rw [hϖ] at hunion ⊢
  rw [hunion]
  refine Set.mem_iUnion.mpr ⟨none, (mem_rightCoset_iff _).mpr ?_⟩
  rw [SetLike.mem_coe]
  have h₁ : heckeLower (bianchiIdealGenerator 𝔭 h𝔭) *
      (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 none)⁻¹ = 1 := mul_inv_cancel _
  rw [h₁]
  exact one_mem _

variable [IsTotallyComplex K] in
lemma bianchiPSLGroup_bianchiGammaZero (𝔑 : Ideal (𝓞 K)) :
    bianchiPSLGroup σ (bianchiGammaZero 𝔑) = (𝔑.gamma0GL).map (glToPSLHom σ) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rcases exists_mem_gamma0GL_of_mem_bianchiPSLGroup hx with ⟨γ, hγ, g, hg, rfl⟩
    exact ⟨γ, hγ, (mk_eq_glToPSL g hg).symm⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨_, ⟨_, (mem_bianchiGammaZero_iff _).mpr ⟨γ, hγ, rfl⟩,
      isSLRepresentative_slRepresentative _⟩, rfl⟩

variable {ι : Type*} {Γ Γ' : Subgroup (GL (Fin 2) (𝓞 K))} {r : ι → GL (Fin 2) (𝓞 K)}
  {s : Set HyperbolicThreeSpace}

lemma bijective_mk_inv_glToPSL
    (hsc : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ Γ')
    (hr : IsRightTransversal Γ' Γ r) : Function.Bijective fun i ↦
      (QuotientGroup.mk (⟨glToPSLHom σ (r i), Subgroup.mem_map_of_mem _ (hr.1 i)⟩ :
        Γ.map (glToPSLHom σ))⁻¹ : Γ.map (glToPSLHom σ) ⧸
          (Γ'.map (glToPSLHom σ)).subgroupOf (Γ.map (glToPSLHom σ))) := by
  refine ⟨fun i j hij ↦ ?_, fun q ↦ ?_⟩
  · have h₁ : (⟨glToPSLHom σ (r i), Subgroup.mem_map_of_mem _ (hr.1 i)⟩ :
        Γ.map (glToPSLHom σ))⁻¹⁻¹ * (⟨glToPSLHom σ (r j), Subgroup.mem_map_of_mem _ (hr.1 j)⟩ :
          Γ.map (glToPSLHom σ))⁻¹ ∈ (Γ'.map (glToPSLHom σ)).subgroupOf (Γ.map (glToPSLHom σ)) :=
      QuotientGroup.eq.mp hij
    rw [inv_inv, Subgroup.mem_subgroupOf] at h₁
    rcases h₁ with ⟨δ, hδ, he⟩
    have he' : glToPSL σ δ = glToPSL σ (r i) * (glToPSL σ (r j))⁻¹ := he
    have h₂ : glToPSL σ (δ⁻¹ * (r i * (r j)⁻¹)) = 1 := by
      rw [glToPSL_mul, glToPSL_mul, glToPSL_inv, glToPSL_inv, he', inv_mul_cancel]
    have h₄ : r i * (r j)⁻¹ ∈ Γ' := by
      have e : r i * (r j)⁻¹ = δ * (δ⁻¹ * (r i * (r j)⁻¹)) := by
        group
      rw [e]
      exact mul_mem hδ (mem_of_glToPSL_eq_one hsc h₂)
    exact (hr.2 (r j) (hr.1 j)).unique h₄ (by simp)
  · rcases QuotientGroup.mk_surjective q with ⟨⟨x, hx⟩, rfl⟩
    rcases hx with ⟨γ, hγ, rfl⟩
    rcases (hr.2 γ⁻¹ (inv_mem hγ)).exists with ⟨i, hi⟩
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    rw [inv_inv, Subgroup.mem_subgroupOf]
    refine ⟨r i * γ, by simpa using hi, ?_⟩
    simp

lemma isFundamentalDomain_subgroupOf_iUnion_smul [Countable ι]
    (hsc : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ Γ')
    (hr : IsRightTransversal Γ' Γ r)
    (hs : IsFundamentalDomain (Γ.map (glToPSLHom σ)) s hyperbolicVolume) :
    IsFundamentalDomain ((Γ'.map (glToPSLHom σ)).subgroupOf (Γ.map (glToPSLHom σ)))
      (⋃ i, (⟨glToPSLHom σ (r i), Subgroup.mem_map_of_mem _ (hr.1 i)⟩ : Γ.map (glToPSLHom σ)) • s)
        hyperbolicVolume :=
  hs.iUnion_smul_of_transversal (fun _ ↦ hs.nullMeasurableSet_smul _)
    (bijective_mk_inv_glToPSL hsc hr)

lemma isFundamentalDomain_iUnion_glToPSL_smul [Countable ι] (hle : Γ' ≤ Γ)
    (hsc : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ Γ')
    (hr : IsRightTransversal Γ' Γ r)
    (hs : IsFundamentalDomain (Γ.map (glToPSLHom σ)) s hyperbolicVolume) :
    IsFundamentalDomain (Γ'.map (glToPSLHom σ)) (⋃ i, glToPSL σ (r i) • s) hyperbolicVolume := by
  have h₂ : IsFundamentalDomain (Γ'.map (glToPSLHom σ) ⊓ Γ.map (glToPSLHom σ) : Subgroup _)
      (⋃ i, (⟨glToPSLHom σ (r i), Subgroup.mem_map_of_mem _ (hr.1 i)⟩ : Γ.map (glToPSLHom σ)) • s)
        hyperbolicVolume :=
    (isFundamentalDomain_subgroupOf_iUnion_smul hsc hr hs).of_subgroupOf
  rwa [inf_of_le_left (Subgroup.map_mono hle)] at h₂

lemma bianchiPairing_sum_glSlash [Fintype ι] (hB : ∀ i, glSlash σ k (r i) B = B)
    (z : HyperbolicThreeSpace) : bianchiPairing (∑ i, glSlash σ k (r i) A) B z =
    ∑' i, bianchiPairing A B (glToPSL σ (r i) • z) := by
  rw [tsum_fintype]
  have h (i : ι) :
      bianchiPairing A B (glToPSL σ (r i) • z) = bianchiPairing (glSlash σ k (r i) A) B z := by
    have h₁ : bianchiPairing
        (bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i))) A)
        (bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i))) B)
          z = bianchiPairing A B
            (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) (r i)) • z) :=
      bianchiPairing_bianchiSlash _ A B z
    have h₂ : bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K)
        (r i))) B = B := hB i
    rw [h₂] at h₁
    exact h₁.symm
  simp only [h]
  simp only [bianchiPairing, Finset.sum_apply, symPowInner, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The unfolding of a trace**: for `r_i` representing the right cosets of `Γ'` in `Γ`, `A`
invariant under `Γ'`, `B` invariant under `Γ` and `s` a fundamental domain of `Γ̄` of finite volume,
`∫_s y^k ⟨∑_i A ∣ r_i, B⟩_k dμ = ∫_{⋃_i r_i s} y^k ⟨A, B⟩_k dμ`, for bounded `A` and `B`. -/
lemma setIntegral_bianchiPairing_sum_glSlash [Fintype ι] [Countable (Γ.map (glToPSLHom σ))]
    (hle : Γ' ≤ Γ) (hsc : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ Γ')
    (hr : IsRightTransversal Γ' Γ r)
    (hs : IsFundamentalDomain (Γ.map (glToPSLHom σ)) s hyperbolicVolume)
    (hfin : hyperbolicVolume s < ⊤) (hA : ∀ δ ∈ Γ', glSlash σ k δ A = A)
    (hB : ∀ γ ∈ Γ, glSlash σ k γ B = B) (hcA : Continuous A) (hcB : Continuous B) {C C' : ℝ}
    (hC : ∀ z, bianchiNormSq A z ≤ C) (hC' : ∀ z, bianchiNormSq B z ≤ C') :
    ∫ z in s, bianchiPairing (∑ i, glSlash σ k (r i) A) B z ∂hyperbolicVolume =
      ∫ z in ⋃ i, glToPSL σ (r i) • s, bianchiPairing A B z ∂hyperbolicVolume := by
  have hfinU : hyperbolicVolume (⋃ i, glToPSL σ (r i) • s) < ⊤ := by
    refine (measure_iUnion_fintype_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun i _ ↦ ?_)
    rw [measure_smul]
    exact hfin
  have hφ : ∀ (h : (Γ'.map (glToPSLHom σ)).subgroupOf (Γ.map (glToPSLHom σ)))
      (x : HyperbolicThreeSpace), bianchiPairing A B (h • x) = bianchiPairing A B x := by
    intro h x
    rcases Subgroup.mem_subgroupOf.mp h.2 with ⟨δ, hδ, he⟩
    have e : h • x = glToPSL σ δ • x := by
      have he' :
          glToPSL σ δ = ((h : Γ.map (glToPSLHom σ)) : ProjectiveSpecialLinearGroup (Fin 2) ℂ) :=
        he
      rw [he']
      rfl
    have h₁ : bianchiPairing
        (bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ)) A)
        (bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ)) B) x =
          bianchiPairing A B
            (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ) • x) :=
      bianchiPairing_bianchiSlash _ A B x
    have h₂ : bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ))
        A = A := hA δ hδ
    have h₃ : bianchiSlash k (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) δ))
        B = B := hB δ (hle hδ)
    rw [h₂, h₃] at h₁
    rw [e]
    exact h₁.symm
  simp only [bianchiPairing_sum_glSlash fun i ↦ hB _ (hr.1 i)]
  exact hs.setIntegral_tsum_smul_eq (isFundamentalDomain_subgroupOf_iUnion_smul hsc hr hs)
    (bijective_mk_inv_glToPSL hsc hr) hφ
    (integrableOn_bianchiPairing_of_le hcA hcB hC hC' hfinU)

lemma bianchiLevelLower_bianchiLevelRaise (hk : Even k) :
    bianchiLevelLower σ k q (bianchiLevelRaise σ k q F) = F := by
  rw [bianchiLevelLower, bianchiLevelRaise, ← bianchiGLSlash_mul hk]
  refine bianchiGLSlash_of_eq_smul_one hk (a := bianchiUnit q) ?_ (bianchiUnit q).ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeUpper, heckeLower]

lemma mk_mul_mk_eq_of_mul_eq {α β α' β' : GL (Fin 2) K} (h : α * β = α' * β') :
    (QuotientGroup.mk (slRepresentative σ α) * QuotientGroup.mk (slRepresentative σ β) :
      ProjectiveSpecialLinearGroup (Fin 2) ℂ) =
        QuotientGroup.mk (slRepresentative σ α') * QuotientGroup.mk (slRepresentative σ β') := by
  have h₁ : IsSLRepresentative σ (α * β) (slRepresentative σ α * slRepresentative σ β) :=
    (isSLRepresentative_slRepresentative _).mul (isSLRepresentative_slRepresentative _)
  have h₂ : IsSLRepresentative σ (α * β) (slRepresentative σ α' * slRepresentative σ β') := by
    rw [h]
    exact (isSLRepresentative_slRepresentative _).mul (isSLRepresentative_slRepresentative _)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  refine QuotientGroup.eq.mpr ?_
  rcases h₁.eq_or_eq_neg h₂ with h₃ | h₃
  · rw [h₃, inv_mul_cancel]
    exact one_mem _
  · rw [h₃, mul_neg, inv_mul_cancel]
    exact SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mpr (Or.inr rfl)

/-- The matrix `(1, 0; 0, q)` maps a fundamental domain of `Γ₀(M) ∩ Γ⁰(q)` to a fundamental domain
of `Γ₀(qM)`. -/
lemma isFundamentalDomain_heckeUpper_smul
    (hs : IsFundamentalDomain ((gamma0Upper M q).map (glToPSLHom σ)) s hyperbolicVolume) :
    IsFundamentalDomain ((Ideal.span {((q * M : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL.map (glToPSLHom σ))
      ((QuotientGroup.mk (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) :
        ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s) hyperbolicVolume := by
  refine hs.smul_of_eq_conjAct_pointwise_smul (measurePreserving_smul _ _).quasiMeasurePreserving ?_
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨?_, ?_⟩
  · rintro ⟨δ', hδ', rfl⟩
    rcases exists_mem_gamma0Upper_heckeUpper_mul_eq hδ' with ⟨δ, hδ, he⟩
    refine ⟨glToPSLHom σ δ, Subgroup.mem_map_of_mem _ hδ, ?_⟩
    rw [ConjAct.toConjAct_smul, mul_inv_eq_iff_eq_mul]
    exact mk_mul_mk_eq_of_mul_eq he
  · rintro ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩
    rcases heckeUpper_mul_map_eq_of_mem hδ with ⟨δ', hδ', he⟩
    refine ⟨δ', hδ', ?_⟩
    rw [ConjAct.toConjAct_smul, eq_mul_inv_iff_mul_eq]
    exact (mk_mul_mk_eq_of_mul_eq he).symm

lemma IsBianchiSlashInvariant.mono {Γ₁ Γ₂ : Subgroup (GL (Fin 2) (𝓞 K))} (h : Γ₁ ≤ Γ₂)
    (hF : IsBianchiSlashInvariant σ Γ₂ k F) : IsBianchiSlashInvariant σ Γ₁ k F :=
  fun γ hγ ↦ hF γ (h hγ)

variable [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **The adjoint of a trace of `F ∣ (1, 0; 0, q)`**: for `K` imaginary quadratic of class number
`1`, `k ≥ 1` even, `F, G ∈ S_k(N)`, `r_i` representing the right cosets of `Γ₀(N) ∩ Γ⁰(q)` in
`Γ₀(N)` and `t_j` those of `Γ₀(Nq)` in `Γ₀(N)`,
`⟨∑_i (F ∣ (1, 0; 0, q)) ∣ r_i, G⟩ = ⟨F, ∑_j (G ∣ (q, 0; 0, 1)) ∣ t_j⟩`. Both sides are the integral
of the `Γ₀(Nq)`-invariant function `y^k ⟨F, G ∣ (q, 0; 0, 1)⟩_k` over a fundamental domain of
`Γ̄₀(Nq)`. -/
lemma bianchiPetersson_sum_glSlash_bianchiLevelLower (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hk' : Even k) {κ : Type*} [Fintype ι] [Fintype κ] {t : κ → GL (Fin 2) (𝓞 K)}
    (hr : IsRightTransversal (gamma0Upper N q) (Ideal.span {(N : 𝓞 K)}).gamma0GL r)
    (ht : IsRightTransversal (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL
      (Ideal.span {(N : 𝓞 K)}).gamma0GL t)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
    (hG : G ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
    bianchiPetersson σ k (Ideal.span {(N : 𝓞 K)})
      (∑ i, glSlash σ k (r i) (bianchiLevelLower σ k q F)) G =
        bianchiPetersson σ k (Ideal.span {(N : 𝓞 K)}) F
          (∑ j, glSlash σ k (t j) (bianchiLevelRaise σ k q G)) := by
  have h𝔑 : Ideal.span {(N : 𝓞 K)} ≠ ⊥ := NeZero.ne _
  rcases exists_isFundamentalDomain_bianchiPSLGroup (σ := σ) (Ideal.span {(N : 𝓞 K)}) hK with
    ⟨s, -, hs⟩
  have hfin : hyperbolicVolume s < ⊤ := hyperbolicVolume_lt_top hK h𝔑 hs
  have hs' : IsFundamentalDomain ((Ideal.span {(N : 𝓞 K)}).gamma0GL.map (glToPSLHom σ)) s
      hyperbolicVolume := by
    rw [← bianchiPSLGroup_bianchiGammaZero]
    exact hs
  have hcount : Countable ((Ideal.span {(N : 𝓞 K)}).gamma0GL.map (glToPSLHom σ)) := by
    rw [← bianchiPSLGroup_bianchiGammaZero]
    exact countable_bianchiPSLGroup
  have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
      (hH : H ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
      H ∈ bianchiSlashInvariants σ k (bianchiGammaZero (Ideal.span {(N : 𝓞 K)})) :=
    (isBianchiSlashInvariant_iff_mem _).mp hH.1.invariant
  have hcont {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
      (hH : H ∈ bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) : Continuous H :=
    continuous_of_analyticAt hH.1.analyticAt
  rcases exists_bianchiNormSq_le hK hk h𝔑 hF with ⟨MF, hMF⟩
  rcases exists_bianchiNormSq_le hK hk h𝔑 hG with ⟨MG, hMG⟩
  have hAinv : ∀ δ ∈ gamma0Upper N q, glSlash σ k δ (bianchiLevelLower σ k q F) =
      bianchiLevelLower σ k q F := fun δ hδ ↦ glSlash_bianchiLevelLower hk'
    (hF.1.invariant.mono fun γ hγ ↦ mem_gamma0GL_span_iff.mpr
      ((Dvd.intro_left (q : 𝓞 K) rfl).trans (mem_gamma0GL_span_iff.mp hγ))) hδ
  have hC : bianchiLevelRaise σ k q G ∈
      bianchiCuspForms σ (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL k := by
    rw [mul_comm N q]
    exact bianchiLevelRaise_mem_bianchiCuspForms hK hk' hG
  have hCinv : ∀ δ ∈ (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL,
      glSlash σ k δ (bianchiLevelRaise σ k q G) = bianchiLevelRaise σ k q G :=
    fun δ hδ ↦ hC.1.invariant.glSlash_eq hδ
  have hle₁ : gamma0Upper N q ≤ (Ideal.span {(N : 𝓞 K)}).gamma0GL :=
    fun δ hδ ↦ mem_gamma0GL_span_iff.mpr hδ.1
  have hle₂ : (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL ≤
      (Ideal.span {(N : 𝓞 K)}).gamma0GL := fun δ hδ ↦ mem_gamma0GL_span_iff.mpr
    ((Dvd.intro (q : 𝓞 K) rfl).trans (mem_gamma0GL_span_iff.mp hδ))
  have hsc₁ : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈ gamma0Upper N q :=
    fun z h₀₁ h₁₀ ↦ ⟨h₁₀ ▸ dvd_zero _, h₀₁ ▸ dvd_zero _⟩
  have hsc₂ : ∀ z : GL (Fin 2) (𝓞 K), z.val 0 1 = 0 → z.val 1 0 = 0 → z ∈
      (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL :=
    fun z _ h₁₀ ↦ mem_gamma0GL_span_iff.mpr (h₁₀ ▸ dvd_zero _)
  have hAc : Continuous (bianchiLevelLower σ k q F) :=
    continuous_of_analyticAt (analyticAt_extend_bianchiSlash _ hF.1.analyticAt)
  have hCc : Continuous (bianchiLevelRaise σ k q G) :=
    continuous_of_analyticAt (analyticAt_extend_bianchiSlash _ hG.1.analyticAt)
  have hMA (z : HyperbolicThreeSpace) : bianchiNormSq (bianchiLevelLower σ k q F) z ≤ MF :=
    (bianchiNormSq_bianchiSlash _ _ z).trans_le (hMF _)
  have hMC (z : HyperbolicThreeSpace) : bianchiNormSq (bianchiLevelRaise σ k q G) z ≤ MG :=
    (bianchiNormSq_bianchiSlash _ _ z).trans_le (hMG _)
  have hU₁ : IsFundamentalDomain ((gamma0Upper N q).map (glToPSLHom σ))
      (⋃ i, glToPSL σ (r i) • s) hyperbolicVolume :=
    isFundamentalDomain_iUnion_glToPSL_smul hle₁ hsc₁ hr hs'
  have hU₂ : IsFundamentalDomain
      ((Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL.map (glToPSLHom σ))
      (⋃ i, glToPSL σ (t i) • s) hyperbolicVolume :=
    isFundamentalDomain_iUnion_glToPSL_smul hle₂ hsc₂ ht hs'
  have hV₁ : IsFundamentalDomain
      ((Ideal.span {((q * N : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL.map (glToPSLHom σ))
      ((QuotientGroup.mk (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) :
        ProjectiveSpecialLinearGroup (Fin 2) ℂ) • ⋃ i, glToPSL σ (r i) • s) hyperbolicVolume :=
    isFundamentalDomain_heckeUpper_smul hU₁
  rw [mul_comm q N] at hV₁
  have hI₁ : ∫ z in s, bianchiPairing (∑ i, glSlash σ k (r i) (bianchiLevelLower σ k q F)) G z
      ∂hyperbolicVolume = ∫ z in ⋃ i, glToPSL σ (r i) • s,
        bianchiPairing (bianchiLevelLower σ k q F) G z ∂hyperbolicVolume :=
    setIntegral_bianchiPairing_sum_glSlash hle₁ hsc₁ hr hs' hfin hAinv
      (fun γ hγ ↦ hG.1.invariant.glSlash_eq hγ) hAc (hcont hG) hMA hMG
  have hI₂ : ∫ z in s, bianchiPairing (∑ i, glSlash σ k (t i) (bianchiLevelRaise σ k q G)) F z
      ∂hyperbolicVolume = ∫ z in ⋃ i, glToPSL σ (t i) • s,
        bianchiPairing (bianchiLevelRaise σ k q G) F z ∂hyperbolicVolume :=
    setIntegral_bianchiPairing_sum_glSlash hle₂ hsc₂ ht hs' hfin hCinv
      (fun γ hγ ↦ hF.1.invariant.glSlash_eq hγ) hCc (hcont hF) hMC hMF
  have hS₁ : ∑ i, glSlash σ k (r i) (bianchiLevelLower σ k q F) ∈
      bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k :=
    sum_glSlash_mem_bianchiCuspForms hK hk' hr (((mem_bianchiCuspForms_iff hK h𝔑).mp hF).1.slash hK
      hk' (isSLRepresentative_slRepresentative _)) hAinv
  have hS₂ : ∑ j, glSlash σ k (t j) (bianchiLevelRaise σ k q G) ∈
      bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k :=
    sum_glSlash_mem_bianchiCuspForms hK hk' ht (((mem_bianchiCuspForms_iff hK h𝔑).mp hG).1.slash hK
      hk' (isSLRepresentative_slRepresentative _)) hCinv
  have hpair (z : HyperbolicThreeSpace) : bianchiPairing (bianchiLevelLower σ k q F) G z =
      bianchiPairing F (bianchiLevelRaise σ k q G)
        ((QuotientGroup.mk (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) :
          ProjectiveSpecialLinearGroup (Fin 2) ℂ) • z) := by
    have h₁ : bianchiPairing (bianchiSlash k (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) F)
        (bianchiSlash k (slRepresentative σ (heckeUpper (bianchiUnit q) 0))
          (bianchiLevelRaise σ k q G)) z = bianchiPairing F (bianchiLevelRaise σ k q G)
            (slRepresentative σ (heckeUpper (bianchiUnit q) 0) • z) :=
      bianchiPairing_bianchiSlash _ F (bianchiLevelRaise σ k q G) z
    have h₂ : bianchiSlash k (slRepresentative σ (heckeUpper (bianchiUnit q) 0))
        (bianchiLevelRaise σ k q G) = G := bianchiLevelLower_bianchiLevelRaise hk'
    rw [h₂] at h₁
    exact h₁
  have hL (U : Set HyperbolicThreeSpace) :
      ∫ z in U, bianchiPairing (bianchiLevelLower σ k q F) G z ∂hyperbolicVolume =
        ∫ z in (QuotientGroup.mk (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) :
          ProjectiveSpecialLinearGroup (Fin 2) ℂ) • U,
            bianchiPairing F (bianchiLevelRaise σ k q G) z ∂hyperbolicVolume := by
    simp only [hpair]
    exact ((measurePreserving_smul _ _).setIntegral_image_emb
      (measurableEmbedding_const_smul _) _ _).symm
  have hinvC : bianchiLevelRaise σ k q G ∈ bianchiSlashInvariants σ k
      (bianchiGammaZero (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)})) :=
    (isBianchiSlashInvariant_iff_mem _).mp hC.1.invariant
  have hinvF :
      F ∈ bianchiSlashInvariants σ k (bianchiGammaZero (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)})) :=
    (isBianchiSlashInvariant_iff_mem _).mp (hF.1.invariant.mono hle₂)
  rw [← bianchiPSLGroup_bianchiGammaZero] at hV₁ hU₂
  have : Countable (bianchiPSLGroup σ (bianchiGammaZero
      (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}))) := countable_bianchiPSLGroup
  have hmain : ∫ x in (QuotientGroup.mk (slRepresentative σ (heckeUpper (bianchiUnit q) 0)) :
      ProjectiveSpecialLinearGroup (Fin 2) ℂ) • ⋃ i, glToPSL σ (r i) • s,
        bianchiPairing F (bianchiLevelRaise σ k q G) x ∂hyperbolicVolume =
      ∫ x in ⋃ i, glToPSL σ (t i) • s,
        bianchiPairing F (bianchiLevelRaise σ k q G) x ∂hyperbolicVolume :=
    hV₁.setIntegral_eq hU₂ (bianchiPairing_smul_bianchiPSLGroup hinvF hinvC)
  rw [bianchiPetersson_eq (hinv hS₁) (hinv hG) hs, hI₁, hL, hmain,
    ← conj_bianchiPetersson hK (hinv hS₂) (hinv hF), bianchiPetersson_eq (hinv hS₂) (hinv hF) hs,
    hI₂, ← integral_conj]
  simp only [conj_bianchiPairing]

variable [NumberField K] [IsTotallyComplex K] [IsPrincipalIdealRing (𝓞 K)] in
/-- **`T_𝔭` is self-adjoint on `S_k(𝔑)` for a prime `𝔭 ∤ 𝔑`** (LMFDB `mf.bianchi.spaces`), for `K`
imaginary quadratic of class number `1` and `k ≥ 1`: `⟨T_𝔭 F, G⟩ = ⟨F, T_𝔭 G⟩`. -/
lemma bianchiPetersson_bianchiHeckeTPrime (hK : finrank ℚ K = 2) (hk : k ≠ 0) {𝔑 : Ideal (𝓞 K)}
    [NeZero 𝔑] {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤)
    {Φ Ψ : bianchiModularForms σ 𝔑.gamma0GL k}
    (hΦ : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiCuspForms σ 𝔑.gamma0GL k)
    (hΨ : (Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiCuspForms σ 𝔑.gamma0GL k) :
    bianchiPetersson σ k 𝔑 (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ) Ψ =
      bianchiPetersson σ k 𝔑 Φ (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Ψ) := by
  have hTΦ : (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiCuspForms σ 𝔑.gamma0GL k :=
    bianchiHeckeOperatorModularForms_mem_bianchiCuspForms hK _ _ hΦ
  have hTΨ : (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiCuspForms σ 𝔑.gamma0GL k :=
    bianchiHeckeOperatorModularForms_mem_bianchiCuspForms hK _ _ hΨ
  rcases Nat.even_or_odd k with hk' | hodd
  · rcases exists_span_eq (NeZero.ne 𝔑) with ⟨N, rfl⟩
    rcases exists_coe_eq_generator h𝔭 with ⟨q, hq𝔭⟩
    have hqp : Prime (q : 𝓞 K) := hq𝔭 ▸ prime_generator h𝔭 h𝔭p
    have hqN : ¬(q : 𝓞 K) ∣ N := fun h ↦ h𝔭p.ne_top <| by
      have hle : Ideal.span {(N : 𝓞 K)} ≤ 𝔭 := by
        rw [← span_coe_eq_of_coe_eq_generator hq𝔭]
        exact Ideal.span_singleton_le_span_singleton.mpr h
      rwa [sup_eq_left.mpr hle] at h𝔭𝔑
    rcases hqp.coprime_iff_not_dvd.mpr hqN with ⟨a, b, hab⟩
    let w : GL (Fin 2) (𝓞 K) := SpecialLinearGroup.toGL ⟨!![a, -b; (N : 𝓞 K), (q : 𝓞 K)], by
      rw [det_fin_two_of]
      linear_combination hab⟩
    have htr₁ : IsRightTransversal (gamma0Upper N q) (Ideal.span {(N : 𝓞 K)}).gamma0GL
        fun p : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ↦
          p.elim 1 fun i ↦ glUpper 1 * glLower ((N : 𝓞 K) * Quotient.out i) :=
      isRightTransversal_option hqp hqN (not_dvd_one_of_prime hqp)
    have htr₂ : IsRightTransversal (Ideal.span {((N * q : (𝓞 K)⁰) : 𝓞 K)}).gamma0GL
        (Ideal.span {(N : 𝓞 K)}).gamma0GL fun p : Option (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) ↦
          p.elim w fun i ↦ glLower ((N : 𝓞 K) * Quotient.out i) :=
      isRightTransversal_gamma0_mul hqp rfl rfl
    rw [coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelLower h𝔭 hq𝔭 htr₁ Φ,
      coe_bianchiHeckeTPrime_eq_sum_glSlash_bianchiLevelRaise h𝔭 h𝔭p h𝔭𝔑 hq𝔭 htr₂ Ψ]
    exact bianchiPetersson_sum_glSlash_bianchiLevelLower hK hk hk' htr₁ htr₂ hΦ hΨ
  · rw [hTΦ.1.invariant.eq_zero_of_odd hodd, hΨ.1.invariant.eq_zero_of_odd hodd,
      hΦ.1.invariant.eq_zero_of_odd hodd, hTΨ.1.invariant.eq_zero_of_odd hodd]

end HyperbolicThreeSpace
