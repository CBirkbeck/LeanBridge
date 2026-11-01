import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.HeckeAlgebra
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeCosetDecomposition

/-!
# The coset decomposition of the Bianchi Hecke operators `T_𝔭`

Let `K` be a totally complex field (imaginary quadratic for the LMFDB) whose ring of integers is a
principal ideal domain, `𝔑` a nonzero ideal of `𝒪_K` and `𝔭 = (ϖ)` a prime with `𝔭 ⊔ 𝔑 = 𝒪_K`. The
double coset `Γ₀(𝔑) diag(1, ϖ) Γ₀(𝔑)` of the Hecke operator `T_𝔭` (`bianchiHeckeTPrime`) is the
union of the right cosets of `(ϖ, 0; 0, 1)` and of the `(1, β; 0, ϖ)`, `β ∈ 𝒪_K / 𝔭`
(`HilbertModularForm.heckeCosetRep`, for the representative `𝔟 = 𝒪_K` of the trivial class), each
exactly once (`doubleCoset_heckeDiagonal_eq_iUnion`): these cosets are those of the matrices of the
Hecke set `HilbertModularGroup.heckeSet 𝔑 𝔭 1 1` (`HilbertModularForm.isHeckeCosetDecomposition`),
which contains the double coset, and each of them lies in the double coset, as
`(1, β; 0, ϖ) = diag(1, ϖ) (1, β; 0, 1)` and, writing `1 = ϖu + n` with `n ∈ 𝔑`,
`(ϖ, 0; 0, 1) = (ϖu, -1; n, 1) diag(1, ϖ) (ϖ, 1; -n, u)`. Hence
`T_𝔭 F = ∑_r F ∣_k r` over these representatives, acting through their `SL(2, ℂ)`-representatives
(`coe_bianchiHeckeTPrime_eq_sum`).

## Main results

* `HyperbolicThreeSpace.doubleCoset_heckeDiagonal_eq_iUnion`: the coset decomposition of
  `Γ₀(𝔑) diag(1, ϖ) Γ₀(𝔑)`.
* `HyperbolicThreeSpace.coe_bianchiHeckeTPrime_eq_sum`: `T_𝔭` as a sum over these representatives.
-/

open Matrix NumberField HilbertModularGroup HilbertModularForm MulOpposite DoubleCoset

open Submodule (IsPrincipal)

open scoped MatrixGroups Pointwise nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] [IsTotallyComplex K] {𝔑 𝔭 : Ideal (𝓞 K)} {ϖ : Kˣ} {p : 𝓞 K}

private lemma heckeUpper_mem_doubleCoset (hϖ : algebraMap (𝓞 K) K p = ϖ) (b : 𝓞 K) :
    heckeUpper ϖ (b : K) ∈ doubleCoset (heckeDiagonal ϖ (isTotallyPositive_of_isTotallyComplex _) :
      GL (Fin 2) K) (bianchiGammaZero 𝔑) (bianchiGammaZero 𝔑) := by
  let γ : GL (Fin 2) (𝓞 K) := SpecialLinearGroup.toGL ⟨!![1, b; 0, 1], by simp⟩
  have he : (γ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![1, b; 0, 1] :=
    rfl
  refine DoubleCoset.mem_doubleCoset.mpr ⟨1, one_mem _,
    GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ, (mem_bianchiGammaZero_iff _).mpr
      ⟨γ, 𝔑.zero_mem, rfl⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeUpper, heckeDiagonal, ← hϖ, he]

private lemma heckeLower_mem_doubleCoset (hϖ : algebraMap (𝓞 K) K p = ϖ) {u n : 𝓞 K} (hn : n ∈ 𝔑)
    (h : p * u + n = 1) :
    heckeLower ϖ ∈ doubleCoset (heckeDiagonal ϖ (isTotallyPositive_of_isTotallyComplex _) :
      GL (Fin 2) K) (bianchiGammaZero 𝔑) (bianchiGammaZero 𝔑) := by
  have h' : algebraMap (𝓞 K) K p * algebraMap (𝓞 K) K u + algebraMap (𝓞 K) K n = 1 := by
    rw [← map_mul, ← map_add, h, map_one]
  let γ₁ : GL (Fin 2) (𝓞 K) := SpecialLinearGroup.toGL ⟨!![p * u, -1; n, 1], by
    rw [det_fin_two_of]
    linear_combination h⟩
  let γ₂ : GL (Fin 2) (𝓞 K) := SpecialLinearGroup.toGL ⟨!![p, 1; -n, u], by
    rw [det_fin_two_of]
    linear_combination h⟩
  have he₁ : (γ₁ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![p * u, -1; n, 1] :=
    rfl
  have he₂ : (γ₂ : Matrix (Fin 2) (Fin 2) (𝓞 K)) = !![p, 1; -n, u] :=
    rfl
  refine DoubleCoset.mem_doubleCoset.mpr ⟨GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ₁,
    (mem_bianchiGammaZero_iff _).mpr ⟨γ₁, hn, rfl⟩, GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ₂,
      (mem_bianchiGammaZero_iff _).mpr ⟨γ₂, 𝔑.neg_mem hn, rfl⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heckeLower, heckeDiagonal, ← hϖ, he₁, he₂, mul_apply]
  · linear_combination -algebraMap (𝓞 K) K p * h'
  · ring1
  · linear_combination -h'

variable [NumberField K]

/-- **The coset decomposition of `Γ₀(𝔑) diag(1, ϖ) Γ₀(𝔑)`** (LMFDB `mf.bianchi.hecke_algebra`): for
a totally complex `K` and `ϖ = p ∈ 𝒪_K` generating a prime `𝔭 = (p)` with `𝔭 ⊔ 𝔑 = 𝒪_K`, the
double coset `Γ₀(𝔑) diag(1, ϖ) Γ₀(𝔑)` in `GL₂(K)` is the union of the right cosets `Γ₀(𝔑) r` of
the representatives `r = (ϖ, 0; 0, 1)` and `r = (1, β; 0, ϖ)`, `β ∈ 𝒪_K / 𝔭`
(`HilbertModularForm.heckeCosetRep`). -/
lemma doubleCoset_heckeDiagonal_eq_iUnion (h𝔭 : (Ideal.span {p}).IsPrime)
    (h𝔭𝔑 : Ideal.span {p} ⊔ 𝔑 = ⊤) (hϖ : algebraMap (𝓞 K) K p = ϖ) :
    doubleCoset (heckeDiagonal ϖ (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K)
      (bianchiGammaZero 𝔑) (bianchiGammaZero 𝔑) =
        ⋃ r, op (heckeCosetRep ϖ 1 r) • (bianchiGammaZero 𝔑 : Set (GL (Fin 2) K)) := by
  have hϖ𝔭 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ϖ : K) =
      (Ideal.span {p} : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, hϖ]
  have hD : IsHeckeCosetDecomposition ϖ 1 (Ideal.span {p}) 𝔑 :=
    isHeckeCosetDecomposition hϖ𝔭 h𝔭 h𝔭𝔑 (isTotallyPositive_of_isTotallyComplex _)
  ext g
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · have hg' : g ∈ heckeSet 𝔑 (Ideal.span {p}) 1 1 :=
      doubleCoset_heckeDiagonal_subset_heckeSet one_ne_zero _ hϖ hg
    rcases hD.surjOn ⟨g, hg', rfl⟩ with ⟨r, -, hr⟩
    exact Set.mem_iUnion.mpr ⟨r, (mem_rightCoset_iff _).mpr
      (QuotientGroup.rightRel_apply.mp (Quotient.exact hr))⟩
  · rcases Set.mem_iUnion.mp hg with ⟨r, hr⟩
    have hrep : heckeCosetRep ϖ 1 r ∈ doubleCoset (heckeDiagonal ϖ
        (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K) (bianchiGammaZero 𝔑)
          (bianchiGammaZero 𝔑) := by
      rcases r with _ | q
      · have h1 : (1 : 𝓞 K) ∈ Ideal.span {p} ⊔ 𝔑 := h𝔭𝔑 ▸ Submodule.mem_top
        rcases Submodule.mem_sup.mp h1 with ⟨a, ha, n, hn, han⟩
        rcases Ideal.mem_span_singleton'.mp ha with ⟨u, rfl⟩
        exact heckeLower_mem_doubleCoset hϖ hn (by rw [mul_comm, han])
      · have hq : (q.out : K) ∈ (1 : Submodule (𝓞 K) K) := by
          simpa only [translationLattice, inv_one, Units.val_one, FractionalIdeal.coe_one] using
            q.out.2
        rcases Submodule.mem_one.mp hq with ⟨b, hb⟩
        rw [heckeCosetRep, ← hb]
        exact heckeUpper_mem_doubleCoset hϖ b
    rcases DoubleCoset.mem_doubleCoset.mp hrep with ⟨h₁, hh₁, h₂, hh₂, he⟩
    exact DoubleCoset.mem_doubleCoset.mpr ⟨g * (heckeCosetRep ϖ 1 r)⁻¹ * h₁,
      mul_mem ((mem_rightCoset_iff _).mp hr) hh₁, h₂, hh₂, by rw [he]; group⟩

variable (σ : K →+* ℂ) (k : ℕ) [IsPrincipalIdealRing (𝓞 K)] [NeZero 𝔑] (h𝔭 : 𝔭 ≠ ⊥)

/-- **The Hecke operator `T_𝔭` as a sum over coset representatives** (LMFDB
`mf.bianchi.hecke_algebra`): for a totally complex `K` whose ring of integers is a principal ideal
domain and a prime `𝔭 = (ϖ)` of `𝒪_K` with `𝔭 ⊔ 𝔑 = 𝒪_K`, the Hecke operator `T_𝔭`
(`bianchiHeckeTPrime`) maps a Bianchi modular form `F` of weight `k` and level `Γ₀(𝔑)` to
`F ∣_k (ϖ, 0; 0, 1) + ∑_{β ∈ 𝒪_K / 𝔭} F ∣_k (1, β; 0, ϖ)`, the matrices acting through their
`SL(2, ℂ)`-representatives (`slRepresentative`). -/
lemma coe_bianchiHeckeTPrime_eq_sum (h𝔭p : 𝔭.IsPrime) (h𝔭𝔑 : 𝔭 ⊔ 𝔑 = ⊤)
    [Fintype (HeckeTranslations (bianchiIdealGenerator 𝔭 h𝔭) 1)]
    (F : bianchiModularForms σ 𝔑.gamma0GL k) :
    (bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 F : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      ∑ r, bianchiSlash k (slRepresentative σ (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 r))
        F := by
  have hϖ : algebraMap (𝓞 K) K (IsPrincipal.generator 𝔭) = bianchiIdealGenerator 𝔭 h𝔭 :=
    rfl
  have hϖ𝔭 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (bianchiIdealGenerator 𝔭 h𝔭 : K) =
      (𝔭 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← hϖ, ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_generator]
  have hD : IsHeckeCosetDecomposition (bianchiIdealGenerator 𝔭 h𝔭) 1 𝔭 𝔑 :=
    isHeckeCosetDecomposition hϖ𝔭 h𝔭p h𝔭𝔑 (isTotallyPositive_of_isTotallyComplex _)
  have hout : doubleCoset ((heckeT 1 𝔑 (bianchiIdealGenerator 𝔭 h𝔭)
      (isTotallyPositive_of_isTotallyComplex _)).out : GL (Fin 2) K) (bianchiGammaZero 𝔑)
        (bianchiGammaZero 𝔑) = doubleCoset (heckeDiagonal (bianchiIdealGenerator 𝔭 h𝔭)
          (isTotallyPositive_of_isTotallyComplex _) : GL (Fin 2) K) (bianchiGammaZero 𝔑)
            (bianchiGammaZero 𝔑) :=
    Quotient.mk_out (s := HeckeCoset.setoid _ _ _) _
  have hinj : Function.Injective fun r ↦ op (heckeCosetRep (bianchiIdealGenerator 𝔭 h𝔭) 1 r) •
      (bianchiGammaZero 𝔑 : Set (GL (Fin 2) K)) := fun r r' h ↦
    hD.injOn (Set.mem_univ r) (Set.mem_univ r')
      (Quotient.sound (QuotientGroup.rightRel_apply.mpr ((rightCoset_eq_iff _).mp h)))
  exact bianchiHeckeOperator_eq_sum σ k (bianchiGammaZero 𝔑) (glTotallyPositive K) _
    ⟨F, F.2.mem_bianchiSlashInvariants⟩ _ (hout.trans (doubleCoset_heckeDiagonal_eq_iUnion
      (by rwa [Ideal.span_singleton_generator]) (by rwa [Ideal.span_singleton_generator]) hϖ)) hinj
        _ fun r ↦ isSLRepresentative_slRepresentative _

end HyperbolicThreeSpace
