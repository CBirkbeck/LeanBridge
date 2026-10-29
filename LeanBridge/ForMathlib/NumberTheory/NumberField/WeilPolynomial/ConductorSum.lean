import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.SingularPrime

/-!
# Conductor sums

An order `R` in an étale `ℚ`-algebra `K` is a `ℤ`-conductor sum if `R = ℤ + 𝔣_R`, and an overorder
`R` of the Frobenius order `ℤ[F, V]` of an isogeny class of abelian varieties over a finite field is
a `ℤ[F, V]`-conductor sum if `R = ℤ[F, V] + 𝔣_R`, where `𝔣_R = (R : 𝒪_K) = {x ∈ K | x 𝒪_K ⊆ R}` is
the conductor of `R` in the maximal order `𝒪_K` of `K`. Equivalently, the image of `ℤ`,
respectively of `ℤ[F, V]`, in the quotient ring `R / 𝔣_R` is everything.

## Main definitions

* `Subalgebra.IsConductorSum`: `R = R₀ + 𝔣_R`, for two subrings `R₀` and `R` of `K`.
* `Subalgebra.IsIntConductorSum` (LMFDB `av.fq.is_zconductor_sum`): `R = ℤ + 𝔣_R`.
* `Polynomial.IsFrobeniusConductorSum` (LMFDB `av.fq.is_zfvconductor_sum`): `R = ℤ[F, V] + 𝔣_R`.

## Main results

* `Subalgebra.isConductorSum_iff_surjective`: for `R₀ ⊆ R`, `R = R₀ + 𝔣_R` if and only if `R₀`
  maps onto `R / 𝔣_R`.
* `Subalgebra.isIntConductorSum_iff_surjective`: `R = ℤ + 𝔣_R` if and only if `ℤ` maps onto
  `R / 𝔣_R`.
* `Subalgebra.isConductorSum_of_integralClosure_le`: the maximal order is a conductor sum.
* `Polynomial.isFrobeniusConductorSum_of_isIntConductorSum`: an overorder of `ℤ[F, V]` that is a
  `ℤ`-conductor sum is a `ℤ[F, V]`-conductor sum.
-/

namespace Subalgebra

variable {K : Type*} [CommRing K] (R R₀ : Subalgebra ℤ K)

/-- An order `R` in an étale `ℚ`-algebra `K` is an **`R₀`-conductor sum**, for a subring `R₀` of
`K`, if `R = R₀ + 𝔣_R` as additive subgroups of `K`, where `𝔣_R = (R : 𝒪_K) = {x ∈ K | x 𝒪_K ⊆ R}`
is the conductor of `R` in the maximal order `𝒪_K` of `K`, the integral closure of `ℤ` in `K`
(LMFDB `av.fq.conductor`). The conductor lies in `R`, so this needs `R₀ ⊆ R`, and then it says that
`R₀` maps onto `R / 𝔣_R` (`Subalgebra.isConductorSum_iff_surjective`). The definition makes sense
for any two subrings of a commutative ring. -/
def IsConductorSum : Prop :=
  toSubmodule R = toSubmodule R₀ ⊔ toSubmodule R / toSubmodule (integralClosure ℤ K)

/-- An order `R` in an étale `ℚ`-algebra `K` is a **`ℤ`-conductor sum** (LMFDB
`av.fq.is_zconductor_sum`) if `R = ℤ + 𝔣_R` as additive subgroups of `K`, where
`𝔣_R = (R : 𝒪_K) = {x ∈ K | x 𝒪_K ⊆ R}` is the conductor of `R` in the maximal order `𝒪_K` of `K`,
the integral closure of `ℤ` in `K`, and `ℤ` is the image of `ℤ` in `K`. Equivalently, `R / 𝔣_R` is
a quotient of `ℤ` (`Subalgebra.isIntConductorSum_iff_surjective`). The definition makes sense for
any subring of a commutative ring. -/
def IsIntConductorSum : Prop :=
  R.IsConductorSum ⊥

variable {R R₀} {S : Subalgebra ℤ K}

lemma mem_toSubmodule_div_iff {x : K} :
    x ∈ toSubmodule R / toSubmodule S ↔ ∃ y ∈ R.relativeConductor S, (y : K) = x :=
  Submodule.mem_div_iff_forall_mul_mem.trans ⟨fun h ↦ ⟨⟨x, mul_one x ▸ h 1 S.one_mem⟩, h, rfl⟩,
    fun ⟨_, hy, hyx⟩ ↦ hyx ▸ hy⟩

lemma toSubmodule_div_le : toSubmodule R / toSubmodule S ≤ toSubmodule R :=
  fun x hx ↦ mul_one x ▸ Submodule.mem_div_iff_forall_mul_mem.mp hx 1 S.one_mem

lemma isConductorSum_iff_le (hR : R₀ ≤ R) : R.IsConductorSum R₀ ↔ toSubmodule R ≤ toSubmodule R₀ ⊔
    toSubmodule R / toSubmodule (integralClosure ℤ K) :=
  ⟨le_of_eq, fun h ↦ h.antisymm <| sup_le (toSubmodule.monotone hR) toSubmodule_div_le⟩

/-- For subrings `R₀ ⊆ R` of `K`, `R = R₀ + 𝔣_R` if and only if `R₀` maps onto `R / 𝔣_R`. -/
lemma isConductorSum_iff_surjective (hR : R₀ ≤ R) : R.IsConductorSum R₀ ↔ Function.Surjective
    ((R.relativeConductor (integralClosure ℤ K)).mkQ ∘ inclusion hR) := by
  rw [isConductorSum_iff_le hR]
  refine ⟨fun h x ↦ ?_, fun h x hx ↦ ?_⟩
  · rcases Submodule.mkQ_surjective _ x with ⟨x, rfl⟩
    rcases Submodule.mem_sup.mp (h x.2) with ⟨y, hy, z, hz, hyz⟩
    rcases mem_toSubmodule_div_iff.mp hz with ⟨w, hw, rfl⟩
    refine ⟨⟨y, hy⟩, LinearMap.sub_mem_ker_iff.mp ?_⟩
    rw [Submodule.ker_mkQ]
    convert neg_mem hw
    ext
    simp [← hyz]
  · rcases h (Submodule.mkQ _ ⟨x, hx⟩) with ⟨y, hy⟩
    rw [Function.comp_apply, ← LinearMap.sub_mem_ker_iff, Submodule.ker_mkQ] at hy
    refine Submodule.mem_sup.mpr ⟨y, y.2, x - y, mem_toSubmodule_div_iff.mpr ⟨_, neg_mem hy, ?_⟩,
      add_sub_cancel _ _⟩
    simp

/-- `R = ℤ + 𝔣_R` if and only if `ℤ` maps onto `R / 𝔣_R`. -/
lemma isIntConductorSum_iff_surjective : R.IsIntConductorSum ↔ Function.Surjective
    (algebraMap ℤ (R ⧸ R.relativeConductor (integralClosure ℤ K))) := by
  have hbot : Function.Surjective (algebraMap ℤ (⊥ : Subalgebra ℤ K)) := fun x ↦
    (Set.mem_range.mp (Algebra.mem_bot.mp x.2)).imp fun _ hn ↦ Subtype.ext hn
  rw [IsIntConductorSum, isConductorSum_iff_surjective bot_le, ← hbot.of_comp_iff]
  refine iff_of_eq <| congrArg _ <| funext fun n ↦ ?_
  simp

lemma IsConductorSum.mono {R₁ : Subalgebra ℤ K} (hR : R.IsConductorSum R₀) (h₀₁ : R₀ ≤ R₁)
    (h₁ : R₁ ≤ R) : R.IsConductorSum R₁ :=
  hR.le.trans (sup_le_sup_right (toSubmodule.monotone h₀₁) _) |>.antisymm <|
    sup_le (toSubmodule.monotone h₁) toSubmodule_div_le

/-- The maximal order is a conductor sum: if `R` contains `𝒪_K`, then `𝔣_R = R`, so `R = R₀ + 𝔣_R`
for every subring `R₀` of `R`. -/
lemma isConductorSum_of_integralClosure_le (hR : R₀ ≤ R) (hO : integralClosure ℤ K ≤ R) :
    R.IsConductorSum R₀ :=
  (isConductorSum_iff_le hR).mpr <| le_sup_of_le_right fun _ hx ↦
    Submodule.mem_div_iff_forall_mul_mem.mpr fun _ hy ↦ R.mul_mem hx (hO hy)

end Subalgebra

namespace Polynomial

variable (q : ℕ) (h : ℤ[X]) (R : Subalgebra ℤ h.EtaleAlgebra)

/-- An overorder `R` of the Frobenius order `ℤ[F, V]` of a polynomial `h ∈ ℤ[x]`
(`Polynomial.frobeniusOrder`) is a **`ℤ[F, V]`-conductor sum** (LMFDB `av.fq.is_zfvconductor_sum`)
if `R = ℤ[F, V] + 𝔣_R` as additive subgroups of the étale algebra `K = ℚ[F]` of `h`, where
`𝔣_R = (R : 𝒪_K) = {x ∈ K | x 𝒪_K ⊆ R}` is the conductor of `R` in the maximal order `𝒪_K` of `K`,
the integral closure of `ℤ` in `K`. The LMFDB's `h` is the Weil polynomial of an isogeny class of
abelian varieties over `𝔽_q`; here `h` is any polynomial and `R` any subring of its étale algebra.
-/
def IsFrobeniusConductorSum : Prop :=
  R.IsConductorSum (h.frobeniusOrder q)

variable {q h R}

/-- An overorder of the Frobenius order `ℤ[F, V]` that is a `ℤ`-conductor sum is a
`ℤ[F, V]`-conductor sum. -/
lemma isFrobeniusConductorSum_of_isIntConductorSum (hR : h.frobeniusOrder q ≤ R)
    (hR' : R.IsIntConductorSum) : h.IsFrobeniusConductorSum q R :=
  hR'.mono bot_le hR

end Polynomial
