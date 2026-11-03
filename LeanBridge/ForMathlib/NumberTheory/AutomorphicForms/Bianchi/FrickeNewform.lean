import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.Fricke
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeCosetDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformAtkinLehner
import TauCeti.MeasureTheory.Group.FundamentalDomain

/-!
# Bianchi newforms are eigenforms of the Fricke involution

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `n ≠ 0` in
`𝒪_K`. The Fricke involution `W_n` (`HyperbolicThreeSpace.bianchiFricke`) of the space of Bianchi
modular forms of level `Γ₀(n)` preserves

* the cusp forms (`HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiCuspForms`), since the
  slash operators of `GL₂(K)` preserve the cuspidal functions;
* the oldforms (`HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiOldforms`), as
  `(δ, 0; 0, 1) W_n = δ W_M (e, 0; 0, 1)` for `n = δMe`, so that `G ∣ (δ, 0; 0, 1) ∣ W_n` is
  `(G ∣ W_M) ∣ (e, 0; 0, 1)`, for `G` of level `Γ₀(M)`;
* the newspace (`HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiNewSubspace`), as `W_n`
  is an isometry for the invariant pairing `y^k ⟨F, G⟩_k`, the hyperbolic volume is invariant, and
  `W_n` maps a fundamental domain of the level to a fundamental domain of the level.

It commutes with `T_𝔭` for a prime `𝔭 ∤ n`
(`HyperbolicThreeSpace.bianchiHeckeTPrime_bianchiFricke`): `W_n diag(1, π) W_n⁻¹ = diag(π, 1)` lies
in the double coset `Γ₀(n) diag(1, π) Γ₀(n)`, which `W_n` therefore normalises, so that it permutes
the right cosets of this double coset.

So `W_n F` is, for a newform `F` of level `(n)`, a form of the newspace with the same eigenvalues
as `F` at the primes `𝔭 ∤ n`. By multiplicity one
(`HyperbolicThreeSpace.eq_smul_of_mem_bianchiNewSubspace`), **every Bianchi newform of level `(n)`
is an eigenform of `W_n`** (LMFDB `mf.bianchi.sign`)
(`HyperbolicThreeSpace.BianchiNewformOfWeight.exists_bianchiFricke_eq_smul`), in every weight
`k ≥ 1`, and so has a sign, which is `±1`
(`HyperbolicThreeSpace.BianchiNewformOfWeight.sign_eq_one_or_eq_neg_one`).

## Main results

* `HyperbolicThreeSpace.bianchiSlash_frickeMatrix_unit_mul`: `W_n` does not depend on the generator
  `n` of the level.
* `HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiCuspForms`: `W_n` preserves the cusp
  forms.
* `HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiOldforms`: `W_n` preserves the
  oldforms.
* `HyperbolicThreeSpace.isFundamentalDomain_frickeMatrix_smul`: `W_n` maps a fundamental domain of
  the level to a fundamental domain of the level.
* `HyperbolicThreeSpace.bianchiSlash_frickeMatrix_mem_bianchiNewSubspace`: `W_n` preserves the
  newspace.
* `HyperbolicThreeSpace.bianchiHeckeTPrime_bianchiFricke`: `W_n` commutes with `T_𝔭`, `𝔭 ∤ n`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.exists_bianchiFricke_eq_smul`: a newform of level
  `(n)` is an eigenform of `W_n`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.hasSign_sign_exists`: a newform of level `(n)` has a
  sign.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.sign_eq_one_or_eq_neg_one`: its sign is `±1`.
-/

open Complex Matrix MeasureTheory Module NumberField HilbertModularGroup HilbertModularForm
  DoubleCoset MulOpposite

open Submodule (IsPrincipal)

open scoped MatrixGroups Pointwise

namespace HyperbolicThreeSpace

section Group

variable {G ι : Type*} [Group G] {Γ : Subgroup G} {a : ι → G} {w x h : G}

lemma iUnion_op_smul_eq_iUnion_op_conj_smul (hΓ : ∀ y, w * y * w⁻¹ ∈ Γ ↔ y ∈ Γ)
    (hD : ∀ y, w * y * w⁻¹ ∈ ⋃ i, op (a i) • (Γ : Set G) ↔ y ∈ ⋃ i, op (a i) • (Γ : Set G)) :
    ⋃ i, op (a i) • (Γ : Set G) = ⋃ i, op (w * a i * w⁻¹) • (Γ : Set G) := by
  ext y
  have h₁ (i : ι) : y * (w * a i * w⁻¹)⁻¹ = w * (w⁻¹ * y * w * (a i)⁻¹) * w⁻¹ := by
    group
  have h₂ : y ∈ ⋃ i, op (a i) • (Γ : Set G) ↔ w⁻¹ * y * w ∈ ⋃ i, op (a i) • (Γ : Set G) := by
    rw [← hD (w⁻¹ * y * w)]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  rw [h₂]
  simp only [Set.mem_iUnion, mem_rightCoset_iff, SetLike.mem_coe, h₁, hΓ]

lemma injective_op_conj_smul (ha : Function.Injective fun i ↦ op (a i) • (Γ : Set G))
    (hΓ : ∀ y, w * y * w⁻¹ ∈ Γ ↔ y ∈ Γ) :
    Function.Injective fun i ↦ op (w * a i * w⁻¹) • (Γ : Set G) := by
  intro i j hij
  refine ha ((rightCoset_eq_iff _).mpr ?_)
  have h₁ : w * a j * w⁻¹ * (w * a i * w⁻¹)⁻¹ ∈ Γ := (rightCoset_eq_iff _).mp hij
  have h₂ : w * a j * w⁻¹ * (w * a i * w⁻¹)⁻¹ = w * (a j * (a i)⁻¹) * w⁻¹ := by
    group
  rwa [h₂, hΓ] at h₁

lemma mul_mul_inv_mem_doubleCoset (hw : ∀ y ∈ Γ, w * y * w⁻¹ ∈ Γ)
    (hh : w * h * w⁻¹ ∈ doubleCoset h (Γ : Set G) Γ) (hx : x ∈ doubleCoset h (Γ : Set G) Γ) :
    w * x * w⁻¹ ∈ doubleCoset h (Γ : Set G) Γ := by
  rcases mem_doubleCoset.mp hx with ⟨b, hb, b', hb', rfl⟩
  rcases mem_doubleCoset.mp hh with ⟨c, hc, c', hc', he⟩
  refine mem_doubleCoset.mpr ⟨w * b * w⁻¹ * c, mul_mem (hw b hb) hc, c' * (w * b' * w⁻¹),
    mul_mem hc' (hw b' hb'), ?_⟩
  have h₁ : w * (b * h * b') * w⁻¹ = w * b * w⁻¹ * (w * h * w⁻¹) * (w * b' * w⁻¹) := by
    group
  rw [h₁, he]
  group

end Group

variable {K : Type*} [Field K] {k : ℕ} {F H : HyperbolicThreeSpace → Fin (k + 1) → ℂ} (n : 𝓞 K)
  [NeZero n]

lemma frickeMatrix_inv_mul_mul (x : GL (Fin 2) K) :
    (frickeMatrix n)⁻¹ * x * frickeMatrix n = frickeMatrix n * x * (frickeMatrix n)⁻¹ := by
  have h : x * (frickeMatrix n * frickeMatrix n) = frickeMatrix n * frickeMatrix n * x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frickeMatrix, mul_apply, mul_comm, Algebra.smul_def]
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, inv_mul_eq_iff_eq_mul, h, mul_assoc]

lemma frickeMatrix_mul_heckeDiagonal_mul_inv (ϖ : Kˣ) (hϖ : IsTotallyPositive (ϖ : K)) :
    frickeMatrix n * (heckeDiagonal ϖ hϖ : GL (Fin 2) K) * (frickeMatrix n)⁻¹ = heckeLower ϖ := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeMatrix, heckeDiagonal, heckeLower]

variable (σ : K →+* ℂ)

variable {σ} in
lemma bianchiSlash_frickeMatrix_bianchiSlash_frickeMatrix (hk : Even k) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n))
      (bianchiSlash k (slRepresentative σ (frickeMatrix n)) F) = F := by
  rw [← bianchiSlash_mul, slRepresentative_frickeMatrix_mul_self, bianchiSlash_neg_one,
    hk.neg_one_pow, one_smul]

lemma isSLRepresentative_conj {x : GL (Fin 2) K} {y : SL(2, ℂ)} (hy : IsSLRepresentative σ x y) :
    IsSLRepresentative σ (frickeMatrix n * x * (frickeMatrix n)⁻¹)
      (slRepresentative σ (frickeMatrix n) * y * (slRepresentative σ (frickeMatrix n))⁻¹) :=
  ((isSLRepresentative_slRepresentative _).mul hy).mul (isSLRepresentative_slRepresentative _).inv

lemma isSLRepresentative_inv_conj {x : GL (Fin 2) K} {y : SL(2, ℂ)}
    (hy : IsSLRepresentative σ x y) : IsSLRepresentative σ (frickeMatrix n * x * (frickeMatrix n)⁻¹)
      ((slRepresentative σ (frickeMatrix n))⁻¹ * y * slRepresentative σ (frickeMatrix n)) := by
  rw [← frickeMatrix_inv_mul_mul]
  exact ((isSLRepresentative_slRepresentative _).inv.mul hy).mul
    (isSLRepresentative_slRepresentative _)

variable [IsTotallyComplex K]

lemma frickeMatrix_mul_mul_inv_mem_iff {x : GL (Fin 2) K} : frickeMatrix n * x *
    (frickeMatrix n)⁻¹ ∈ bianchiGammaZero (Ideal.span {n}) ↔ x ∈
      bianchiGammaZero (Ideal.span {n}) := by
  refine ⟨fun h ↦ ?_, frickeMatrix_mul_mul_inv_mem n⟩
  have h₁ : frickeMatrix n * (frickeMatrix n * x * (frickeMatrix n)⁻¹) * (frickeMatrix n)⁻¹ ∈
      bianchiGammaZero (Ideal.span {n}) := frickeMatrix_mul_mul_inv_mem n h
  rw [← frickeMatrix_inv_mul_mul] at h₁
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h₁

/-- **The Fricke involution does not depend on the generator of the level**: for a unit `u` and `F`
invariant under `Γ₀(n)`, `F ∣ W_{un} = F ∣ W_n`, as `W_{un} = (1, 0; 0, u) W_n` with
`(1, 0; 0, u) ∈ Γ₀(n)`. -/
lemma bianchiSlash_frickeMatrix_unit_mul (u : (𝓞 K)ˣ) [NeZero ((u : 𝓞 K) * n)]
    (hF : F ∈ bianchiSlashInvariants σ k (bianchiGammaZero (Ideal.span {n}))) :
    bianchiSlash k (slRepresentative σ (frickeMatrix ((u : 𝓞 K) * n))) F =
      bianchiSlash k (slRepresentative σ (frickeMatrix n)) F := by
  refine bianchiSlash_eq_of_mul_inv_mem hF ((mem_bianchiGammaZero_iff _).mpr
    ⟨GeneralLinearGroup.rowScale 1 u, by simp [Ideal.gamma0GL], ?_⟩)
    (isSLRepresentative_slRepresentative _) (isSLRepresentative_slRepresentative _)
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeMatrix, mul_apply]

/-- `W_n` maps a fundamental domain of `Γ₀(n)` to a fundamental domain of `Γ₀(n)`. -/
lemma isFundamentalDomain_frickeMatrix_smul {s : Set HyperbolicThreeSpace}
    (hs : IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero (Ideal.span {n}))) s
      hyperbolicVolume) :
    IsFundamentalDomain (bianchiPSLGroup σ (bianchiGammaZero (Ideal.span {n})))
      ((QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
        ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s) hyperbolicVolume := by
  refine hs.smul_of_eq_conjAct_pointwise_smul (measurePreserving_smul _ _).quasiMeasurePreserving ?_
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rcases hx with ⟨y, ⟨γ, hγ, hy⟩, rfl⟩
    refine ⟨(QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
      ProjectiveSpecialLinearGroup (Fin 2) ℂ)⁻¹ * QuotientGroup.mk y *
        QuotientGroup.mk (slRepresentative σ (frickeMatrix n)), ?_, ?_⟩
    · exact ⟨_, ⟨_, frickeMatrix_mul_mul_inv_mem n hγ, isSLRepresentative_inv_conj n σ hy⟩, rfl⟩
    · simp [ConjAct.toConjAct_smul, mul_assoc]
  · rintro ⟨y, ⟨y', ⟨γ, hγ, hy'⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, frickeMatrix_mul_mul_inv_mem n hγ, isSLRepresentative_conj n σ hy'⟩, rfl⟩

variable [NumberField K]

/-- **The Fricke involution commutes with the Hecke operator `T_𝔭` of a prime `𝔭 ∤ n`**: for
`K` imaginary quadratic of class number `1`, `W_n diag(1, π) W_n⁻¹ = diag(π, 1)` lies in
`Γ₀(n) diag(1, π) Γ₀(n)`, so that `W_n` normalises this double coset, and permutes its right
cosets. -/
lemma bianchiHeckeTPrime_bianchiFricke [IsPrincipalIdealRing (𝓞 K)] {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥)
    (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ Ideal.span {n} = ⊤)
    (Φ : bianchiModularForms σ (Ideal.span {n}).gamma0GL k) :
    bianchiHeckeTPrime σ k (Ideal.span {n}) 𝔭 h𝔭 (bianchiFricke σ k n Φ) =
      bianchiFricke σ k n (bianchiHeckeTPrime σ k (Ideal.span {n}) 𝔭 h𝔭 Φ) := by
  have hϖ : algebraMap (𝓞 K) K (IsPrincipal.generator 𝔭) = bianchiIdealGenerator 𝔭 h𝔭 :=
    rfl
  have hcard : Nat.card (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) = Ideal.absNorm 𝔭 :=
    natCard_heckeTranslations _ _ (spanSingleton_bianchiIdealGenerator _ h𝔭)
  have hN₀ : Ideal.absNorm 𝔭 ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr h𝔭
  have hfin : Finite (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) :=
    Nat.finite_of_card_ne_zero (hcard ▸ hN₀)
  let _ : Fintype (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1) := Fintype.ofFinite _
  have hD : IsHeckeCosetDecomposition (bianchiIdealGenerator 𝔭 h𝔭) 1 𝔭 (Ideal.span {n}) :=
    isHeckeCosetDecomposition (spanSingleton_bianchiIdealGenerator 𝔭 h𝔭) h𝔭p h𝔭𝔑
      (isTotallyPositive_of_isTotallyComplex _)
  have hout : doubleCoset ((heckeT 1 (Ideal.span {n}) (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _)).out : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) =
      doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
        (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
          (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) :=
    Quotient.mk_out (s := HeckeCoset.setoid _ _ _) _
  have hinj : Function.Injective fun r ↦ op (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 r) •
      (bianchiGammaZero (Ideal.span {n}) : Set (GL (Fin 2) K)) := fun r r' h ↦
    hD.injOn (Set.mem_univ r) (Set.mem_univ r')
      (Quotient.sound (QuotientGroup.rightRel_apply.mpr ((rightCoset_eq_iff _).mp h)))
  have hunion : doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) =
      ⋃ r, op (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 r) •
        (bianchiGammaZero (Ideal.span {n}) : Set (GL (Fin 2) K)) :=
    doubleCoset_heckeDiagonal_eq_iUnion (p := IsPrincipal.generator 𝔭)
      (by rwa [Ideal.span_singleton_generator]) (by rwa [Ideal.span_singleton_generator]) hϖ
  have hlower : heckeLower (bianchiIdealGenerator 𝔭 h𝔭) ∈ doubleCoset (heckeDiagonal
      (bianchiIdealGenerator 𝔭 h𝔭) (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) := by
    rw [hunion]
    refine Set.mem_iUnion.mpr ⟨none, (mem_rightCoset_iff _).mpr ?_⟩
    rw [SetLike.mem_coe]
    have h₁ : heckeLower (bianchiIdealGenerator 𝔭 h𝔭) *
        (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 none)⁻¹ = 1 := mul_inv_cancel _
    rw [h₁]
    exact one_mem _
  have hDw (y : GL (Fin 2) K) : frickeMatrix n * y * (frickeMatrix n)⁻¹ ∈ doubleCoset (heckeDiagonal
      (bianchiIdealGenerator 𝔭 h𝔭) (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) ↔ y ∈
      doubleCoset (heckeDiagonal
        (bianchiIdealGenerator 𝔭 h𝔭) (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
          (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) := by
    have hmem {z : GL (Fin 2) K} (hz : z ∈ doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
        (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
          (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n}))) :
        frickeMatrix n * z * (frickeMatrix n)⁻¹ ∈ doubleCoset (heckeDiagonal
          (bianchiIdealGenerator 𝔭 h𝔭) (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
            (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) :=
      mul_mul_inv_mem_doubleCoset (fun _ h ↦ frickeMatrix_mul_mul_inv_mem n h)
        (frickeMatrix_mul_heckeDiagonal_mul_inv n _ _ ▸ hlower) hz
    refine ⟨fun h ↦ ?_, hmem⟩
    have h₁ : frickeMatrix n * (frickeMatrix n * y * (frickeMatrix n)⁻¹) * (frickeMatrix n)⁻¹ ∈
        doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
          (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
            (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) :=
      hmem h
    rw [← frickeMatrix_inv_mul_mul] at h₁
    simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h₁
  have hcover : doubleCoset ((heckeT 1 (Ideal.span {n}) (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _)).out : GL (Fin 2) K)
        (bianchiGammaZero (Ideal.span {n})) (bianchiGammaZero (Ideal.span {n})) =
      ⋃ i, op (frickeMatrix n * heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 i *
        (frickeMatrix n)⁻¹) • (bianchiGammaZero (Ideal.span {n}) : Set (GL (Fin 2) K)) :=
    hout.trans <| hunion.trans <| iUnion_op_smul_eq_iUnion_op_conj_smul
      (fun y ↦ frickeMatrix_mul_mul_inv_mem_iff n) fun y ↦ by rw [← hunion]; exact hDw y
  have hT : ((bianchiHeckeTPrime σ k (Ideal.span {n}) 𝔭 h𝔭 Φ : bianchiModularForms σ _ k) :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) = ∑ i, bianchiSlash k
        (slRepresentative σ (frickeMatrix n) *
          slRepresentative σ (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 i) *
            (slRepresentative σ (frickeMatrix n))⁻¹) (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) :=
    bianchiHeckeOperator_eq_sum σ k (bianchiGammaZero (Ideal.span {n}))
      (glTotallyPositive K) (heckeT 1 (Ideal.span {n}) (bianchiIdealGenerator 𝔭 h𝔭)
        (isTotallyPositive_of_isTotallyComplex _)) ⟨Φ, Φ.2.mem_bianchiSlashInvariants⟩ _ hcover
      (injective_op_conj_smul hinj fun y ↦ frickeMatrix_mul_mul_inv_mem_iff n) _
      fun r ↦ isSLRepresentative_conj n σ (isSLRepresentative_slRepresentative _)
  refine Subtype.ext ?_
  rw [coe_bianchiFricke, coe_bianchiHeckeTPrime_eq_sum σ k h𝔭 h𝔭p h𝔭𝔑, coe_bianchiFricke]
  rw [hT, bianchiSlash_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [← bianchiSlash_mul, ← bianchiSlash_mul, inv_mul_cancel_right]

variable [IsPrincipalIdealRing (𝓞 K)]

variable {σ}

/-- **`W_n` preserves the cusp forms** of level `Γ₀(n)`, for `K` imaginary quadratic of class number
`1`. -/
lemma bianchiSlash_frickeMatrix_mem_bianchiCuspForms (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiCuspForms σ (Ideal.span {n}).gamma0GL k) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) F ∈
      bianchiCuspForms σ (Ideal.span {n}).gamma0GL k := by
  have hn : Ideal.span {n} ≠ ⊥ := NeZero.ne _
  rcases Nat.even_or_odd k with hk | hk
  · rcases (mem_bianchiCuspForms_iff hK hn).mp hF with ⟨h₁, -⟩
    exact (mem_bianchiCuspForms_iff hK hn).mpr ⟨h₁.slash hK hk
      (isSLRepresentative_slRepresentative _), (hF.1.bianchiSlash_frickeMatrix).invariant⟩
  · rw [hF.1.invariant.eq_zero_of_odd hk, bianchiSlash_zero]
    exact zero_mem _

/-- **`W_n` preserves the oldforms** of level `Γ₀(n)`, for `K` imaginary quadratic of class number
`1`: for `n = δMe`, `G` of level `Γ₀(M)`, `(δ, 0; 0, 1) W_n = δ W_M (e, 0; 0, 1)`, so that
`G ∣ (δ, 0; 0, 1) ∣ W_n = (G ∣ W_M) ∣ (e, 0; 0, 1)`, with `G ∣ W_M` of level `Γ₀(M)`. -/
lemma bianchiSlash_frickeMatrix_mem_bianchiOldforms (hK : finrank ℚ K = 2)
    (hH : H ∈ bianchiOldforms σ k (Ideal.span {n})) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) H ∈
      bianchiOldforms σ k (Ideal.span {n}) := by
  induction hH using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨𝔐, h𝔐, δ, hδ, hle, G, hG, rfl⟩
    rcases Nat.even_or_odd k with hk | hk
    · rcases (IsPrincipalIdealRing.principal 𝔐).principal with ⟨M, rfl⟩
      rw [Ideal.submodule_span_eq, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_le_span_singleton] at hle
      rcases hle with ⟨e, he⟩
      have hn₀ : n ≠ 0 := NeZero.ne n
      have hM : M ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (he ▸ hn₀))
      have he₀ : e ≠ 0 := right_ne_zero_of_mul (he ▸ hn₀)
      have : NeZero M := ⟨hM⟩
      have hG' : bianchiSlash k (slRepresentative σ (frickeMatrix M)) G ∈
          bianchiCuspForms σ (Ideal.span {M}).gamma0GL k :=
        bianchiSlash_frickeMatrix_mem_bianchiCuspForms M hK hG
      refine Submodule.subset_span ⟨Ideal.span {M}, h𝔐, e, he₀, ?_, _, hG', ?_⟩
      · rw [Ideal.span_singleton_mul_span_singleton]
        exact Ideal.span_singleton_le_span_singleton.mpr ⟨δ, by rw [he]; ring1⟩
      · rw [rowScale_eq_heckeLower, rowScale_eq_heckeLower]
        have key : bianchiGLSlash σ k (heckeLower (Units.mk0 (algebraMap (𝓞 K) K δ)
            ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hδ)) * frickeMatrix n) G =
              bianchiGLSlash σ k (frickeMatrix M * heckeLower (Units.mk0 (algebraMap (𝓞 K) K e)
                ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr he₀))) G :=
          bianchiGLSlash_of_coe_eq_smul hk (c := algebraMap (𝓞 K) K δ) (by
            ext i j
            fin_cases i <;> fin_cases j <;>
              simp [frickeMatrix, heckeLower, he, mul_assoc, Algebra.smul_def])
            ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hδ)
        rw [bianchiGLSlash_mul hk, bianchiGLSlash_mul hk] at key
        exact key
    · rw [hG.1.invariant.eq_zero_of_odd hk, bianchiSlash_zero, bianchiSlash_zero]
      exact zero_mem _
  | zero =>
    rw [bianchiSlash_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [bianchiSlash_add]
    exact add_mem hy hz
  | smul a y _ hy =>
    rw [bianchiSlash_smul]
    exact Submodule.smul_mem _ a hy

/-- **`W_n` preserves the newspace** of level `Γ₀(n)`, for `K` imaginary quadratic of class number
`1`: for `H` old and a fundamental domain `s` of `Γ̄₀(n)`, the integrand
`y^k ⟨(F ∣ W_n)(z), H(z)⟩_k` is `y^k ⟨F(W_n z), (H ∣ W_n)(W_n z)⟩_k`, with `H ∣ W_n` old and
`W_n s` a fundamental domain, the hyperbolic volume being invariant. -/
lemma bianchiSlash_frickeMatrix_mem_bianchiNewSubspace (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiNewSubspace σ k (Ideal.span {n})) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) F ∈
      bianchiNewSubspace σ k (Ideal.span {n}) := by
  rcases Nat.even_or_odd k with hk | hk
  · refine ⟨bianchiSlash_frickeMatrix_mem_bianchiCuspForms n hK hF.1, fun H hH s hs ↦ ?_⟩
    rcases hF.2 _ (bianchiSlash_frickeMatrix_mem_bianchiOldforms n hK hH) _
      (isFundamentalDomain_frickeMatrix_smul n σ hs) with ⟨h₁, h₂⟩
    have he (z : HyperbolicThreeSpace) : (z.height ^ k : ℂ) * symPowInner k
        (bianchiSlash k (slRepresentative σ (frickeMatrix n)) F z) (H z) =
          bianchiPairing F (bianchiSlash k (slRepresentative σ (frickeMatrix n)) H)
            (slRepresentative σ (frickeMatrix n) • z) := by
      rw [← bianchiPairing_bianchiSlash, bianchiSlash_frickeMatrix_bianchiSlash_frickeMatrix n hk]
      rfl
    have hpre : (fun z : HyperbolicThreeSpace ↦ slRepresentative σ (frickeMatrix n) • z) ⁻¹'
        ((QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
          ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s) = s := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, ← mk_smul_eq, inv_smul_smul]
    have hmp : MeasurePreserving (fun z : HyperbolicThreeSpace ↦
        slRepresentative σ (frickeMatrix n) • z) hyperbolicVolume hyperbolicVolume :=
      measurePreserving_smul _ _
    have hemb : MeasurableEmbedding (fun z : HyperbolicThreeSpace ↦
        slRepresentative σ (frickeMatrix n) • z) := measurableEmbedding_const_smul _
    simp only [he]
    refine ⟨?_, ?_⟩
    · have h₃ : IntegrableOn ((fun z ↦ bianchiPairing F
          (bianchiSlash k (slRepresentative σ (frickeMatrix n)) H) z) ∘
            fun z ↦ slRepresentative σ (frickeMatrix n) • z)
          ((fun z : HyperbolicThreeSpace ↦ slRepresentative σ (frickeMatrix n) • z) ⁻¹'
            ((QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
              ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s)) hyperbolicVolume :=
        (hmp.integrableOn_comp_preimage hemb).mpr h₁
      rwa [hpre] at h₃
    · have h₃ : ∫ x in (fun z : HyperbolicThreeSpace ↦ slRepresentative σ (frickeMatrix n) • z) ⁻¹'
          ((QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
            ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s),
            bianchiPairing F (bianchiSlash k (slRepresentative σ (frickeMatrix n)) H)
              (slRepresentative σ (frickeMatrix n) • x) ∂hyperbolicVolume =
          ∫ y in (QuotientGroup.mk (slRepresentative σ (frickeMatrix n)) :
            ProjectiveSpecialLinearGroup (Fin 2) ℂ) • s,
              bianchiPairing F (bianchiSlash k (slRepresentative σ (frickeMatrix n)) H)
                y ∂hyperbolicVolume :=
        hmp.setIntegral_preimage_emb hemb _ _
      rw [hpre] at h₃
      rw [h₃]
      exact h₂
  · rw [hF.1.1.invariant.eq_zero_of_odd hk, bianchiSlash_zero]
    exact zero_mem _

namespace BianchiNewformOfWeight

/-- **A Bianchi newform of level `(n)` is an eigenform of the Fricke involution `W_n`** (LMFDB
`mf.bianchi.sign`), for `K` imaginary quadratic of class number `1` and in weight `k ≥ 1`: `W_n F`
lies in the newspace (`bianchiSlash_frickeMatrix_mem_bianchiNewSubspace`), with the eigenvalues of
`F` at the primes `𝔭 ∤ n` (`bianchiHeckeTPrime_bianchiFricke`), so is a multiple of `F` by
multiplicity one (`eq_smul_of_mem_bianchiNewSubspace`). -/
lemma exists_bianchiFricke_eq_smul (N : BianchiNewformOfWeight σ k (Ideal.span {n}))
    (hK : finrank ℚ K = 2) (hk : k ≠ 0) :
    ∃ c : ℂ, bianchiFricke σ k n N.toBianchiModularForm = c • N.toBianchiModularForm := by
  have hnew : ((bianchiFricke σ k n N.toBianchiModularForm : bianchiModularForms σ _ k) :
      HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k (Ideal.span {n}) :=
    bianchiSlash_frickeMatrix_mem_bianchiNewSubspace n hK N.mem_bianchiNewSubspace
  refine ⟨_, eq_smul_of_mem_bianchiNewSubspace hK N.mem_bianchiNewSubspace hnew
    (toBianchiModularForm_ne_zero (N.toFun_ne_zero hK))
    N.hasWhittakerExpansion (hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK
      (bianchiNewSubspace_le σ k _ hnew) hk) fun 𝔭 h𝔭 hp hsup ↦ ?_⟩
  refine ⟨_, N.bianchiHeckeTPrime_toBianchiModularForm ⟨𝔭, hp, h𝔭⟩, ?_⟩
  rw [bianchiHeckeTPrime_bianchiFricke n σ h𝔭 hp hsup, ← map_smul,
    N.bianchiHeckeTPrime_toBianchiModularForm ⟨𝔭, hp, h𝔭⟩]

/-- **A Bianchi newform of level `(n)` has a sign** (LMFDB `mf.bianchi.sign`), for `K` imaginary
quadratic of class number `1` and in weight `k ≥ 1`. -/
lemma hasSign_sign_exists (N : BianchiNewformOfWeight σ k (Ideal.span {n})) (hK : finrank ℚ K = 2)
    (hk : k ≠ 0) : N.HasSign (sign (N.exists_bianchiFricke_eq_smul n hK hk)) :=
  hasSign_sign _

/-- **The sign of a Bianchi newform of level `(n)` is `±1`** (LMFDB `mf.bianchi.sign`). -/
lemma sign_eq_one_or_eq_neg_one (N : BianchiNewformOfWeight σ k (Ideal.span {n}))
    (hK : finrank ℚ K = 2) (hk : k ≠ 0) : sign (N.exists_bianchiFricke_eq_smul n hK hk) = 1 ∨
    sign (N.exists_bianchiFricke_eq_smul n hK hk) = -1 :=
  (N.hasSign_sign_exists n hK hk).eq_one_or_eq_neg_one (N.toFun_ne_zero hK)

end BianchiNewformOfWeight

end HyperbolicThreeSpace
