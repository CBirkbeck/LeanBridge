import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeNewspace

/-!
# A basis of the newspace of Bianchi forms consisting of newforms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, `𝔑 ≠ 0` an
ideal of `𝒪_K` and `k ≥ 1`. The Hecke operators `T_𝔭`, `𝔭 ∤ 𝔑`, are commuting and self-adjoint for
the Petersson product on the finite dimensional space `S_k(𝔑)`, and all `T_𝔭` preserve the newspace.
So the newspace is the sum of the simultaneous eigenspaces of the `T_𝔭`, `𝔭 ∤ 𝔑`, which are lines by
multiplicity one, and are therefore stable under the `T_𝔮`, `𝔮 ∣ 𝔑`, as well.

## Main definitions

* `HyperbolicThreeSpace.bianchiHeckeTPrimeNew`: the Hecke operator `T_𝔭` on the newspace.

## Main results

* `HyperbolicThreeSpace.conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul`: the eigenvalues of `T_𝔭` on
  `S_k(𝔑)`, `𝔭 ∤ 𝔑`, are real.
* `HyperbolicThreeSpace.bianchiPetersson_eq_zero_of_eigenvalue_ne`: eigenforms of `T_𝔭` with
  distinct eigenvalues are orthogonal.
* `HyperbolicThreeSpace.conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul_of_le`: the eigenvalues of `T_𝔭`,
  `𝔭 ∣ 𝔑`, on the eigenforms of the Fricke involution are real, though `T_𝔭` is not self-adjoint.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.conj_eigenvalue`: the Hecke eigenvalues of a newform
  are real at every prime.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.conj_eq_of_mem_heckeField`: the Hecke field of a
  newform is contained in `ℝ`.
* `HyperbolicThreeSpace.iSup_iInf_eigenspace_bianchiHeckeTPrimeNew`: the `T_𝔭`, `𝔭 ∤ 𝔑`, act
  semisimply on the newspace.
* `HyperbolicThreeSpace.exists_bianchiHeckeTPrimeCusp_eq_smul`: a form of the newspace which is an
  eigenform of `T_𝔭` for every `𝔭 ∤ 𝔑` is an eigenform of all the `T_𝔮`.
* `HyperbolicThreeSpace.span_range_toFun`: the newforms span the newspace.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.bianchiPetersson_toFun_eq_zero`: distinct newforms
  are orthogonal.
* `HyperbolicThreeSpace.linearIndependent_range_toFun`: the distinct newforms are linearly
  independent, so that they form a basis of the newspace of simultaneous eigenforms of the `T_𝔭`.
* `HyperbolicThreeSpace.sup_bianchiOldforms_bianchiNewSubspace`: `S_k(𝔑)` is the sum of the oldforms
  and the newspace.
* `HyperbolicThreeSpace.disjoint_bianchiOldforms_bianchiNewSubspace`: this sum is direct.
-/

open Complex Module NumberField

open Submodule (IsPrincipal)

open scoped ComplexConjugate nonZeroDivisors

namespace HyperbolicThreeSpace

lemma sup_eq_top_of_mem_iff_inner_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (core : InnerProductSpace.Core ℂ E) (W W' : Submodule ℂ E)
    (h : ∀ x, x ∈ W' ↔ ∀ y ∈ W, core.inner y x = 0) : W ⊔ W' = ⊤ := by
  let _ : NormedAddCommGroup E := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ E := InnerProductSpace.ofCore core.toCore
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have e : W' = Wᗮ := by
    ext x
    rw [h, Submodule.mem_orthogonal]
  rw [e]
  exact W.sup_orthogonal_of_hasOrthogonalProjection

variable {K : Type*} [Field K] {σ : K →+* ℂ} {k : ℕ} {𝔑 : Ideal (𝓞 K)}
  {F : HyperbolicThreeSpace → Fin (k + 1) → ℂ} [NumberField K]

lemma bianchiUpOperator_smul {q : (𝓞 K)⁰} (c : ℂ) :
    bianchiUpOperator σ k q (c • F) = c • bianchiUpOperator σ k q F := by
  simp only [bianchiUpOperator, bianchiLevelLower, bianchiGLSlash_smul, glSlash_smul,
    Finset.smul_sum]

lemma absNorm_rpow_ne_zero (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 :=
  ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.2.2))) _).ne'

lemma sup_eq_top_of_not_le (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (h : ¬𝔑 ≤ 𝔭.1) :
    𝔭.1 ⊔ 𝔑 = ⊤ :=
  (𝔭.2.1.isMaximal 𝔭.2.2).out.2 _ <| lt_of_le_of_ne le_sup_left
    fun e ↦ h (sup_eq_left.mp e.symm)

variable [IsTotallyComplex K]

/-- **The oldforms and the newspace meet in `0`** (LMFDB `mf.bianchi.spaces`). -/
lemma disjoint_bianchiOldforms_bianchiNewSubspace (hK : finrank ℚ K = 2) :
    Disjoint (bianchiOldforms σ k 𝔑) (bianchiNewSubspace σ k 𝔑) :=
  Submodule.disjoint_def.mpr fun _ hold hnew ↦
    eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace hK hold hnew

variable [IsPrincipalIdealRing (𝓞 K)] [NeZero 𝔑]

lemma conj_eq_of_bianchiPetersson_smul_eq (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    {Φ : bianchiCuspForms σ 𝔑.gamma0GL k} (hΦ : Φ ≠ 0) {a : ℂ}
    (h : bianchiPetersson σ k 𝔑 (a • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ)) Φ =
      bianchiPetersson σ k 𝔑 Φ (a • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ))) :
    conj a = a := by
  have hinv : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp Φ.2.1.invariant
  have hinv' : a • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
      bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp (a • Φ).2.1.invariant
  rw [← conj_bianchiPetersson hK hinv' hinv, bianchiPetersson_smul_left hK a hinv hinv, map_mul,
    conj_bianchiPetersson hK hinv hinv] at h
  have h₀ : bianchiPetersson σ k 𝔑 (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) Φ ≠ 0 := fun h₀ ↦
    hΦ (Subtype.ext ((bianchiPetersson_self_eq_zero_iff hK hk (NeZero.ne 𝔑) Φ.2).mp h₀))
  exact (mul_right_cancel₀ h₀ h).symm

section Eigenvalue

variable {𝔭 : Ideal (𝓞 K)}

/-- **The eigenvalues of `T_𝔭` on `S_k(𝔑)`, `𝔭 ∤ 𝔑`, are real** (LMFDB `mf.bianchi.spaces`), for `K`
imaginary quadratic of class number `1` and `k ≥ 1`: this is reality in the given embedding `σ`, as
`T_𝔭` is self-adjoint. -/
lemma conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) {Φ : bianchiCuspForms σ 𝔑.gamma0GL k} (hΦ : Φ ≠ 0) {a : ℂ}
    (h : bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ = a • Φ) : conj a = a := by
  have h₁ : bianchiPetersson σ k 𝔑 (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) Φ = bianchiPetersson σ k 𝔑 Φ
        (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    bianchiPetersson_bianchiHeckeTPrimeCusp hK hk h𝔭 h𝔭p h𝔭𝔑 Φ Φ
  rw [h, Submodule.coe_smul] at h₁
  exact conj_eq_of_bianchiPetersson_smul_eq hK hk hΦ h₁

/-- **The eigenvalues of `T_𝔭` on the eigenforms of the Fricke involution are real, for `𝔭 ∣ 𝔑`**
(LMFDB `mf.bianchi.spaces`), for `K` imaginary quadratic of class number `1` and `k ≥ 1`: `T_𝔭` is
not self-adjoint for these primes, but its adjoint is `W T_𝔭 W`. -/
lemma conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul_of_le {n : (𝓞 K)⁰} (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) (hk' : Even k) (h𝔭 : 𝔭 ≠ ⊥) (h𝔭p : 𝔭.IsPrime) (hle : Ideal.span {(n : 𝓞 K)} ≤ 𝔭)
    {Φ : bianchiCuspForms σ (Ideal.span {(n : 𝓞 K)}).gamma0GL k} (hΦ : Φ ≠ 0) {a w : ℂ}
    (hw : w ^ 2 = 1) (hT : bianchiHeckeTPrimeCusp σ k _ hK 𝔭 h𝔭 Φ = a • Φ)
    (hW : bianchiGLSlash σ k (frickeMatrix (n : 𝓞 K)) Φ =
      w • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ)) : conj a = a := by
  rcases exists_coe_eq_generator h𝔭 with ⟨q, hq⟩
  have hqn : (q : 𝓞 K) ∣ n := Ideal.span_singleton_le_span_singleton.mp
    (span_coe_eq_of_coe_eq_generator hq ▸ hle)
  have hqp : Prime (q : 𝓞 K) := hq ▸ prime_generator h𝔭 h𝔭p
  have hU₀ : (bianchiHeckeTPrimeCusp σ k (Ideal.span {(n : 𝓞 K)}) hK 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) = bianchiUpOperator σ k q Φ :=
    coe_bianchiHeckeTPrime_eq_bianchiUpOperator h𝔭 hq hqp hqn _
  have hU : bianchiUpOperator σ k q Φ = a • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) := by
    rw [← hU₀, hT, Submodule.coe_smul]
  have h₁ : bianchiPetersson σ k (Ideal.span {(n : 𝓞 K)}) (bianchiUpOperator σ k q Φ) Φ =
      bianchiPetersson σ k (Ideal.span {(n : 𝓞 K)}) Φ (bianchiGLSlash σ k (frickeMatrix (n : 𝓞 K))
        (bianchiUpOperator σ k q (bianchiGLSlash σ k (frickeMatrix (n : 𝓞 K)) Φ))) :=
    bianchiPetersson_bianchiUpOperator hK hk hk' hqp hqn Φ.2 Φ.2
  have e : w • a • w • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      a • (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) := by
    rw [smul_comm a w, smul_smul, ← sq, hw, one_smul]
  rw [hW, bianchiUpOperator_smul, hU, bianchiGLSlash_smul, bianchiGLSlash_smul, hW, e] at h₁
  exact conj_eq_of_bianchiPetersson_smul_eq hK hk hΦ h₁

/-- **Eigenforms of `T_𝔭` with distinct eigenvalues are orthogonal**, for `𝔭 ∤ 𝔑`. -/
lemma bianchiPetersson_eq_zero_of_eigenvalue_ne (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤) {Φ Ψ : bianchiCuspForms σ 𝔑.gamma0GL k} (hΨ₀ : Ψ ≠ 0)
    {a b : ℂ} (hΦ : bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ = a • Φ)
    (hΨ : bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ = b • Ψ) (hab : a ≠ b) :
    bianchiPetersson σ k 𝔑 (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) Ψ = 0 := by
  have hinv {H : HyperbolicThreeSpace → Fin (k + 1) → ℂ}
      (hH : H ∈ bianchiCuspForms σ 𝔑.gamma0GL k) :
      H ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) :=
    (isBianchiSlashInvariant_iff_mem 𝔑).mp hH.1.invariant
  have hb : conj b = b := conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul hK hk h𝔭 h𝔭p h𝔭𝔑 hΨ₀ hΨ
  have h₁ : bianchiPetersson σ k 𝔑 (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Φ :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) Ψ = bianchiPetersson σ k 𝔑 Φ
        (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    bianchiPetersson_bianchiHeckeTPrimeCusp hK hk h𝔭 h𝔭p h𝔭𝔑 Φ Ψ
  rw [hΦ, hΨ, Submodule.coe_smul, bianchiPetersson_smul_left hK a (hinv Φ.2) (hinv Ψ.2),
    ← conj_bianchiPetersson hK (hinv (b • Ψ).2) (hinv Φ.2), Submodule.coe_smul,
    bianchiPetersson_smul_left hK b (hinv Ψ.2) (hinv Φ.2), map_mul, hb,
    conj_bianchiPetersson hK (hinv Ψ.2) (hinv Φ.2)] at h₁
  exact (mul_eq_mul_right_iff.mp h₁).resolve_left hab

end Eigenvalue

namespace BianchiNewformOfWeight

variable (N N' : BianchiNewformOfWeight σ k 𝔑)

lemma coe_bianchiHeckeTPrimeCusp_toFun (hK : finrank ℚ K = 2)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2
      ⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩ =
        ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) •
          ⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩ := by
  have h₁ : (bianchiHeckeTPrime σ k 𝔑 𝔭.1 𝔭.2.2 N.toBianchiModularForm :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
        ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) • N.toFun :=
    congrArg Subtype.val (N.bianchiHeckeTPrime_toBianchiModularForm 𝔭)
  exact Subtype.ext h₁

lemma coe_ne_zero (hK : finrank ℚ K = 2) :
    (⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩ :
      bianchiCuspForms σ 𝔑.gamma0GL k) ≠ 0 :=
  fun h ↦ N.toFun_ne_zero hK (congrArg Subtype.val h)

/-- **The Hecke eigenvalues of a newform are real at every prime** (LMFDB `mf.bianchi.newform`), for
`K` imaginary quadratic of class number `1` and `k ≥ 1`: at `𝔭 ∤ 𝔑` as `T_𝔭` is self-adjoint, and at
`𝔭 ∣ 𝔑` as the adjoint of `T_𝔭` is `W T_𝔭 W`, of which a newform is an eigenform with the same
eigenvalue, being an eigenform of the Fricke involution `W` with eigenvalue `±1`. -/
lemma conj_eigenvalue (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : conj (N.eigenvalue 𝔭) = N.eigenvalue 𝔭 := by
  have h₁ : conj ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) =
      ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) := by
    by_cases h𝔭𝔑 : 𝔑 ≤ 𝔭.1
    · rcases exists_span_eq (NeZero.ne 𝔑) with ⟨n, rfl⟩
      rcases (⟨_, N.hasSign_sign_exists (n : 𝓞 K) hK hk,
        N.sign_eq_one_or_eq_neg_one (n : 𝓞 K) hK hk⟩ : ∃ ε : ℂ, N.HasSign ε ∧ (ε = 1 ∨ ε = -1))
        with ⟨ε, hs, hε⟩
      refine conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul_of_le hK hk (N.even hK) 𝔭.2.2 𝔭.2.1 h𝔭𝔑
        (N.coe_ne_zero hK) (w := -ε) ?_ (N.coe_bianchiHeckeTPrimeCusp_toFun hK 𝔭)
        (congrArg Subtype.val hs)
      rcases hε with rfl | rfl <;> norm_num
    · exact conj_eq_of_bianchiHeckeTPrimeCusp_eq_smul hK hk 𝔭.2.2 𝔭.2.1
        (sup_eq_top_of_not_le 𝔭 h𝔭𝔑) (N.coe_ne_zero hK) (N.coe_bianchiHeckeTPrimeCusp_toFun hK 𝔭)
  have hr : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 := absNorm_rpow_ne_zero 𝔭
  rw [map_mul, map_inv₀, conj_ofReal, mul_right_inj' (inv_ne_zero hr)] at h₁
  exact h₁

/-- **The Hecke field of a newform is contained in `ℝ`** (LMFDB `mf.bianchi.newform`): this is the
part of total reality which holds in the given embedding, all the other embeddings of the Hecke
field being out of reach without the rational structure of `S_k(𝔑)`. -/
lemma conj_eq_of_mem_heckeField (hK : finrank ℚ K = 2) (hk : k ≠ 0) {z : ℂ}
    (hz : z ∈ N.heckeField) : conj z = z := by
  refine IntermediateField.adjoin_induction ℚ (fun x hx ↦ ?_) (fun q ↦ ?_) (fun x y _ _ hx hy ↦ ?_)
    (fun x _ hx ↦ ?_) (fun x y _ _ hx hy ↦ ?_) hz
  · rcases hx with ⟨𝔭, -, rfl⟩
    exact N.conj_eigenvalue hK hk 𝔭
  · simp
  · rw [map_add, hx, hy]
  · rw [map_inv₀, hx]
  · rw [map_mul, hx, hy]

/-- **Distinct newforms are orthogonal** (LMFDB `mf.bianchi.spaces`). -/
lemma bianchiPetersson_toFun_eq_zero (hK : finrank ℚ K = 2) (hk : k ≠ 0) (h : N.toFun ≠ N'.toFun) :
    bianchiPetersson σ k 𝔑 N.toFun N'.toFun = 0 := by
  have hex : ∃ 𝔭, ¬𝔑 ≤ 𝔭.1 ∧ N.eigenvalue 𝔭 ≠ N'.eigenvalue 𝔭 := by
    by_contra hcon
    push Not at hcon
    exact h (N.toFun_eq_of_eigenvalue_eq N' hK hcon)
  rcases hex with ⟨𝔭, h𝔭𝔑, hne⟩
  have hr : (((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 := absNorm_rpow_ne_zero 𝔭
  exact bianchiPetersson_eq_zero_of_eigenvalue_ne hK hk 𝔭.2.2 𝔭.2.1 (sup_eq_top_of_not_le 𝔭 h𝔭𝔑)
    (Φ := ⟨N.toFun, bianchiNewSubspace_le σ k 𝔑 N.mem_bianchiNewSubspace⟩)
    (Ψ := ⟨N'.toFun, bianchiNewSubspace_le σ k 𝔑 N'.mem_bianchiNewSubspace⟩)
    (N'.coe_ne_zero hK) (N.coe_bianchiHeckeTPrimeCusp_toFun hK 𝔭)
      (N'.coe_bianchiHeckeTPrimeCusp_toFun hK 𝔭) fun h ↦ hne (mul_left_cancel₀ (inv_ne_zero hr) h)

end BianchiNewformOfWeight

/-- A nonzero form of the newspace which is an eigenform of `T_𝔭` for every `𝔭 ∤ 𝔑` is an eigenform
of `T_𝔮` for every `𝔮`: by commutativity `T_𝔮 F` has the same eigenvalues at the `𝔭 ∤ 𝔑` as `F`, and
it lies in the newspace, so that multiplicity one applies. -/
lemma exists_bianchiHeckeTPrimeCusp_eq_smul (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) (hF₀ : F ≠ 0)
    {χ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ}
    (hχ : ∀ 𝔭, ¬𝔑 ≤ 𝔭.1 → (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le σ k 𝔑 hF⟩ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) = χ 𝔭 • F)
    (𝔮 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : ∃ b : ℂ,
      (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, bianchiNewSubspace_le σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = b • F := by
  by_cases h𝔮 : 𝔑 ≤ 𝔮.1
  · have hF' : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k := bianchiNewSubspace_le σ k 𝔑 hF
    have hnew : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, hF'⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑 :=
      bianchiHeckeTPrimeCusp_mem_bianchiNewSubspace hK hk 𝔮.2.2 𝔮.2.1 ⟨F, hF'⟩ hF
    have hG : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, hF'⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiCuspForms σ 𝔑.gamma0GL k :=
      (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, hF'⟩).2
    have hΦ₀ : (⟨F, bianchiCuspForms_le σ _ k hF'⟩ : bianchiModularForms σ 𝔑.gamma0GL k) ≠ 0 :=
      fun h ↦ hF₀ (congrArg Subtype.val h)
    refine ⟨_, congrArg Subtype.val (eq_smul_of_mem_bianchiNewSubspace
      (Φ := ⟨F, bianchiCuspForms_le σ _ k hF'⟩) (Ψ := ⟨_, bianchiCuspForms_le σ _ k hG⟩) hK hF hnew
      hΦ₀ (hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK hF' hk)
      (hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK hG hk) fun 𝔭 h𝔭 hp hsup ↦ ?_)⟩
    have h𝔭𝔑 : ¬𝔑 ≤ 𝔭 := fun hle ↦ hp.ne_top (by rwa [sup_eq_left.mpr hle] at hsup)
    have hne : 𝔭 ≠ 𝔮.1 := fun h ↦ h𝔭𝔑 (h ▸ h𝔮)
    have hc : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 *
        bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2) ⟨F, hF'⟩ =
          (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 *
            bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭) ⟨F, hF'⟩ :=
      LinearMap.congr_fun (commute_bianchiHeckeTPrimeCusp hK hk h𝔭 hp 𝔮.2.2 𝔮.2.1 hne).eq _
    have hT : bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭 ⟨F, hF'⟩ = χ ⟨𝔭, hp, h𝔭⟩ • ⟨F, hF'⟩ :=
      Subtype.ext (hχ ⟨𝔭, hp, h𝔭⟩ h𝔭𝔑)
    refine ⟨χ ⟨𝔭, hp, h𝔭⟩, Subtype.ext (hχ ⟨𝔭, hp, h𝔭⟩ h𝔭𝔑), Subtype.ext ?_⟩
    rw [End.mul_apply, End.mul_apply, hT, map_smul] at hc
    have hc' : (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭 h𝔭
        (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, hF'⟩) :
          HyperbolicThreeSpace → Fin (k + 1) → ℂ) = χ ⟨𝔭, hp, h𝔭⟩ •
            (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔮.1 𝔮.2.2 ⟨F, hF'⟩ :
              HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
      congrArg Subtype.val hc
    exact hc'
  · exact ⟨χ 𝔮, hχ 𝔮 h𝔮⟩

lemma mem_span_toFun_of_forall_eigen (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) {χ : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ}
    (hχ : ∀ 𝔭, ¬𝔑 ≤ 𝔭.1 → (bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le σ k 𝔑 hF⟩ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) = χ 𝔭 • F) :
    F ∈ Submodule.span ℂ (Set.range (BianchiNewformOfWeight.toFun (σ := σ) (k := k) (𝔑 := 𝔑))) := by
  by_cases hF₀ : F = 0
  · rw [hF₀]
    exact zero_mem _
  choose b hb using exists_bianchiHeckeTPrimeCusp_eq_smul hK hk hF hF₀ hχ
  let a : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ := fun 𝔭 ↦
    ((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) * b 𝔭
  have ha : ∀ 𝔭, (bianchiHeckeTPrimeArith σ k 𝔑 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = a 𝔭 • F := fun 𝔭 ↦ by
    have h₁ : (bianchiHeckeTPrime σ k 𝔑 𝔭.1 𝔭.2.2
        ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
          HyperbolicThreeSpace → Fin (k + 1) → ℂ) = b 𝔭 • F := hb 𝔭
    rw [bianchiHeckeTPrimeArith, LinearMap.smul_apply, Submodule.coe_smul, h₁, smul_smul]
  have hc₁ : bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1 ≠ 0 :=
    BianchiNewformOfWeight.bianchiWhittakerCoeff_one_ne_zero hK hk hF hF₀ ha
  have he : F = bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1 •
      (BianchiNewformOfWeight.ofEigenform hK hk hF hF₀ ha).toFun := by
    rw [BianchiNewformOfWeight.toFun_ofEigenform, smul_inv_smul₀ hc₁]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

variable (σ k 𝔑) in
/-- The Hecke operator `T_𝔭` on the newspace of level `𝔑`, which it preserves. -/
noncomputable def bianchiHeckeTPrimeNew (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) : Module.End ℂ (bianchiNewSubspace σ k 𝔑) :=
  LinearMap.codRestrict _ ((bianchiCuspForms σ 𝔑.gamma0GL k).subtype ∘ₗ
    bianchiHeckeTPrimeCusp σ k 𝔑 hK 𝔭.1 𝔭.2.2 ∘ₗ Submodule.inclusion (bianchiNewSubspace_le σ k 𝔑))
      fun F ↦ bianchiHeckeTPrimeCusp_mem_bianchiNewSubspace hK hk 𝔭.2.2 𝔭.2.1 _ F.2

/-- **The Hecke operators at `𝔭 ∤ 𝔑` act semisimply on the newspace** (LMFDB `mf.bianchi.spaces`):
for `K` imaginary quadratic of class number `1` and `k ≥ 1`, the newspace is the sum of the
simultaneous eigenspaces of the `T_𝔭`, `𝔭 ∤ 𝔑`. -/
lemma iSup_iInf_eigenspace_bianchiHeckeTPrimeNew (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    ⨆ χ : {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} // ¬𝔑 ≤ 𝔭.1} → ℂ, ⨅ i,
      End.eigenspace (bianchiHeckeTPrimeNew σ k 𝔑 hK hk i.1) (χ i) = ⊤ := by
  have hT : ∀ (i : {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} // ¬𝔑 ≤ 𝔭.1})
      (x y : bianchiNewSubspace σ k 𝔑), bianchiPetersson σ k 𝔑
        (bianchiHeckeTPrimeNew σ k 𝔑 hK hk i.1 x : HyperbolicThreeSpace → Fin (k + 1) → ℂ) y =
          bianchiPetersson σ k 𝔑 x
            (bianchiHeckeTPrimeNew σ k 𝔑 hK hk i.1 y : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    fun i x y ↦ bianchiPetersson_bianchiHeckeTPrimeCusp hK hk i.1.2.2 i.1.2.1
      (sup_eq_top_of_not_le i.1 i.2)
        ⟨x, bianchiNewSubspace_le σ k 𝔑 x.2⟩ ⟨y, bianchiNewSubspace_le σ k 𝔑 y.2⟩
  refine iSup_iInf_eigenspace_of_le hK hk (NeZero.ne 𝔑) (bianchiNewSubspace_le σ k 𝔑) hT
    fun i j hij ↦ LinearMap.ext fun x ↦ Subtype.ext ?_
  have hne : i.1.1 ≠ j.1.1 := fun h ↦ hij (Subtype.ext (Subtype.ext h))
  have hc : (bianchiHeckeTPrimeCusp σ k 𝔑 hK i.1.1 i.1.2.2 *
      bianchiHeckeTPrimeCusp σ k 𝔑 hK j.1.1 j.1.2.2) ⟨x, bianchiNewSubspace_le σ k 𝔑 x.2⟩ =
        (bianchiHeckeTPrimeCusp σ k 𝔑 hK j.1.1 j.1.2.2 *
          bianchiHeckeTPrimeCusp σ k 𝔑 hK i.1.1 i.1.2.2) ⟨x, bianchiNewSubspace_le σ k 𝔑 x.2⟩ :=
    LinearMap.congr_fun
      (commute_bianchiHeckeTPrimeCusp hK hk i.1.2.2 i.1.2.1 j.1.2.2 j.1.2.1 hne).eq _
  have hc' : ((bianchiHeckeTPrimeCusp σ k 𝔑 hK i.1.1 i.1.2.2 *
      bianchiHeckeTPrimeCusp σ k 𝔑 hK j.1.1 j.1.2.2) ⟨x, bianchiNewSubspace_le σ k 𝔑 x.2⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = ((bianchiHeckeTPrimeCusp σ k 𝔑 hK j.1.1 j.1.2.2 *
        bianchiHeckeTPrimeCusp σ k 𝔑 hK i.1.1 i.1.2.2) ⟨x, bianchiNewSubspace_le σ k 𝔑 x.2⟩ :
          HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    congrArg Subtype.val hc
  exact hc'

/-- **The newforms span the newspace** (LMFDB `mf.bianchi.spaces`): for `K` imaginary quadratic of
class number `1` and `k ≥ 1`, the newspace of level `𝔑` is spanned by the Bianchi newforms, which
are simultaneous eigenforms of all the Hecke operators, normalised by `c(1) = 1`. -/
lemma span_range_toFun (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    Submodule.span ℂ (Set.range (BianchiNewformOfWeight.toFun (σ := σ) (k := k) (𝔑 := 𝔑))) =
      bianchiNewSubspace σ k 𝔑 := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun F hF ↦ ?_
  · rintro _ ⟨N, rfl⟩
    exact N.mem_bianchiNewSubspace
  have hmem : (⟨F, hF⟩ : bianchiNewSubspace σ k 𝔑) ∈ (⊤ : Submodule ℂ (bianchiNewSubspace σ k 𝔑)) :=
    Submodule.mem_top
  rw [← iSup_iInf_eigenspace_bianchiHeckeTPrimeNew hK hk] at hmem
  have key : ∀ x ∈ ⨆ χ : {𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} // ¬𝔑 ≤ 𝔭.1} → ℂ, ⨅ i,
      End.eigenspace (bianchiHeckeTPrimeNew σ k 𝔑 hK hk i.1) (χ i),
      (x : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈
        Submodule.span ℂ (Set.range (BianchiNewformOfWeight.toFun (σ := σ) (k := k) (𝔑 := 𝔑))) := by
    intro x hx
    induction hx using Submodule.iSup_induction' with
    | mem χ x hx =>
      classical
      refine mem_span_toFun_of_forall_eigen hK hk x.2 (χ := fun 𝔭 ↦
        if h : ¬𝔑 ≤ 𝔭.1 then χ ⟨𝔭, h⟩ else 0) fun 𝔭 h𝔭 ↦ ?_
      rw [dite_eq_left_of_eq_true (eq_true h𝔭)]
      exact congrArg Subtype.val (End.mem_eigenspace_iff.mp
        ((Submodule.mem_iInf _).mp hx ⟨𝔭, h𝔭⟩))
    | zero => exact zero_mem _
    | add x y _ _ h₁ h₂ => exact add_mem h₁ h₂
  exact key _ hmem

/-- **The newforms are linearly independent** (LMFDB `mf.bianchi.spaces`), being pairwise
orthogonal, and they form a basis of the newspace of simultaneous eigenforms for all the Hecke
operators (`span_range_toFun`). -/
lemma linearIndependent_range_toFun (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    LinearIndependent ℂ ((↑) : Set.range (BianchiNewformOfWeight.toFun (σ := σ) (k := k) (𝔑 := 𝔑)) →
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) := by
  let core : InnerProductSpace.Core ℂ (bianchiNewSubspace σ k 𝔑) :=
    bianchiPeterssonCore σ hK hk (NeZero.ne 𝔑) (bianchiNewSubspace_le σ k 𝔑)
  let _ : NormedAddCommGroup (bianchiNewSubspace σ k 𝔑) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ (bianchiNewSubspace σ k 𝔑) := InnerProductSpace.ofCore core.toCore
  let v : Set.range (BianchiNewformOfWeight.toFun (σ := σ) (k := k) (𝔑 := 𝔑)) →
      bianchiNewSubspace σ k 𝔑 := fun x ↦ ⟨x.1, by
    rcases x with ⟨_, N, rfl⟩
    exact N.mem_bianchiNewSubspace⟩
  have hv : LinearIndependent ℂ v := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℂ) (fun x h ↦ ?_) fun x y hxy ↦ ?_
    · rcases x with ⟨_, N, rfl⟩
      exact N.toFun_ne_zero hK (congrArg Subtype.val h)
    · rcases x with ⟨_, N, rfl⟩
      rcases y with ⟨_, N', rfl⟩
      exact N'.bianchiPetersson_toFun_eq_zero N hK hk fun h ↦ hxy (Subtype.ext h.symm)
  exact hv.map' (bianchiNewSubspace σ k 𝔑).subtype (Submodule.ker_subtype _)

/-- **`S_k(𝔑)` is the sum of the oldforms and the newspace** (LMFDB `mf.bianchi.spaces`), for `K`
imaginary quadratic of class number `1` and `k ≥ 1`: the newspace is the orthogonal complement of
the oldforms in the finite dimensional inner product space `S_k(𝔑)`. -/
lemma sup_bianchiOldforms_bianchiNewSubspace (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    bianchiOldforms σ k 𝔑 ⊔ bianchiNewSubspace σ k 𝔑 = bianchiCuspForms σ 𝔑.gamma0GL k := by
  have h𝔑 : 𝔑 ≠ ⊥ := NeZero.ne 𝔑
  have hold : bianchiOldforms σ k 𝔑 ≤ bianchiCuspForms σ 𝔑.gamma0GL k :=
    bianchiOldforms_le_bianchiCuspForms hK h𝔑
  refine le_antisymm (sup_le hold (bianchiNewSubspace_le σ k 𝔑)) fun F hF ↦ ?_
  have : FiniteDimensional ℂ (bianchiCuspForms σ 𝔑.gamma0GL k) :=
    finiteDimensional_bianchiCuspForms hK hk h𝔑
  have hsup : (bianchiOldforms σ k 𝔑).comap (bianchiCuspForms σ 𝔑.gamma0GL k).subtype ⊔
      (bianchiNewSubspace σ k 𝔑).comap (bianchiCuspForms σ 𝔑.gamma0GL k).subtype = ⊤ :=
    sup_eq_top_of_mem_iff_inner_eq_zero (bianchiPeterssonCore σ hK hk h𝔑 le_rfl) _ _ fun x ↦ ?_
  · have hmem : (⟨F, hF⟩ : bianchiCuspForms σ 𝔑.gamma0GL k) ∈
        (bianchiOldforms σ k 𝔑).comap (bianchiCuspForms σ 𝔑.gamma0GL k).subtype ⊔
          (bianchiNewSubspace σ k 𝔑).comap (bianchiCuspForms σ 𝔑.gamma0GL k).subtype :=
      hsup ▸ Submodule.mem_top
    rcases Submodule.mem_sup.mp hmem with ⟨u, hu, v, hv, huv⟩
    have hFe : F = u.1 + v.1 := (congrArg Subtype.val huv).symm
    rw [hFe]
    exact add_mem (Submodule.mem_sup_left hu) (Submodule.mem_sup_right hv)
  · refine ⟨fun hx y hy ↦ ((mem_bianchiNewSubspace_iff hK hk h𝔑).mp hx).2 _ hy, fun h ↦ ?_⟩
    exact (mem_bianchiNewSubspace_iff hK hk h𝔑).mpr ⟨x.2, fun G hG ↦ h ⟨G, hold hG⟩ hG⟩

end HyperbolicThreeSpace
