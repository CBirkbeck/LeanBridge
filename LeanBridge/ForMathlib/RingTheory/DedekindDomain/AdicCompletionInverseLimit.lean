import Mathlib.RingTheory.AdicCompletion.RingHom
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The inverse limit `lim R / 𝔓 ^ n` is the ring of integers of the completion

Let `R` be a Dedekind domain with fraction field `K`, and `v` a height-one prime `𝔓` of `R` (LMFDB
`nf.padic_completion`, for `R = 𝒪_K` the ring of integers of a number field). The inverse limit
`lim R / 𝔓 ^ n` (Mathlib's `AdicCompletion 𝔓 R`) is isomorphic to the ring of integers `𝒪_v` of
the completion `K_v`: the maps `R / 𝔓 ^ n → 𝒪_v / 𝔪 ^ n` induced by `R → 𝒪_v` are isomorphisms,
since `𝔪 ^ n` is cut out by the valuation and `R` is dense in `𝒪_v` (Tau Ceti), and `𝒪_v` is
`𝔪`-adically complete (Tau Ceti). So the inverse limit is an integral domain, with field of
fractions `K_v`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionRingEquiv` (LMFDB `nf.padic_completion`): the
  isomorphism `lim R / 𝔓 ^ n ≃+* 𝒪_v`, which extends the identity of `R`.

## Main theorems

* `IsDedekindDomain.HeightOneSpectrum.isDomain_adicCompletion` (LMFDB `nf.padic_completion`): the
  inverse limit `lim R / 𝔓 ^ n` is an integral domain.
* `IsDedekindDomain.HeightOneSpectrum.isFractionRing_adicCompletion` (LMFDB `nf.padic_completion`):
  its field of fractions is `K_v`.
-/

open IsLocalRing Ideal Quotient

/-- The quotient map `R → R ⧸ I` of an ideal: inside the namespace `HeightOneSpectrum`, `mk` is the
constructor of `HeightOneSpectrum`, and `Quotient.mk` is the quotient map of a setoid. -/
local notation "π" => Ideal.Quotient.mk

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    factorPow I hle (evalₐ I n x) = evalₐ I m x := by
  rcases mk_surjective I R x with ⟨c, rfl⟩
  rw [evalₐ_mk, evalₐ_mk, factor_mk]
  exact Ideal.mk_eq_mk I hle c

end AdicCompletion

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

lemma comap_maximalIdeal_pow (n : ℕ) :
    (maximalIdeal (v.adicCompletionIntegers K) ^ n).comap (algebraMap R _) = v.asIdeal ^ n := by
  ext r
  rw [mem_comap, mem_maximalIdeal_pow_iff, mem_asIdeal_pow_iff_valued_algebraMap_le (K := K)]
  rfl

lemma surjective_quotientMap (n : ℕ) :
    Function.Surjective (quotientMap _ _ (comap_maximalIdeal_pow K v n).ge) := by
  intro y
  rcases mk_surjective (I := _) y with ⟨x, rfl⟩
  rcases v.exists_valued_sub_le x n with ⟨a, ha⟩
  refine ⟨π _ a, ?_⟩
  rw [quotientMap_mk, mk_eq_mk_iff_sub_mem, mem_maximalIdeal_pow_iff, AddSubgroupClass.coe_sub,
    Valuation.map_sub_swap]
  exact ha

/-- The isomorphism `R / 𝔓 ^ n ≃+* 𝒪_v / 𝔪 ^ n` induced by `R → 𝒪_v`. -/
noncomputable def quotientPowEquiv (n : ℕ) : R ⧸ v.asIdeal ^ n ≃+*
    v.adicCompletionIntegers K ⧸ maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  RingEquiv.ofBijective _
    ⟨quotientMap_injective' (comap_maximalIdeal_pow K v n).le, surjective_quotientMap K v n⟩

lemma quotientPowEquiv_mk (n : ℕ) (r : R) :
    quotientPowEquiv K v n (π _ r) = π _ (algebraMap R _ r) :=
  rfl

lemma factorPow_quotientPowEquiv {m n : ℕ} (hle : m ≤ n) (x : R ⧸ v.asIdeal ^ n) :
    factorPow _ hle (quotientPowEquiv K v n x) = quotientPowEquiv K v m (factorPow _ hle x) := by
  rcases mk_surjective (I := _) x with ⟨r, rfl⟩
  rw [quotientPowEquiv_mk, factor_mk, factor_mk, quotientPowEquiv_mk]

lemma factorPow_comp_quotientPowEquiv_comp_evalₐ {m n : ℕ} (hle : m ≤ n) : (factorPow _ hle).comp
    ((quotientPowEquiv K v n).toRingHom.comp (AdicCompletion.evalₐ v.asIdeal n).toRingHom) =
    (quotientPowEquiv K v m).toRingHom.comp (AdicCompletion.evalₐ v.asIdeal m).toRingHom :=
  RingHom.ext fun x ↦ by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [factorPow_quotientPowEquiv, AdicCompletion.factorPow_evalₐ]

lemma factorPow_comp_quotientPowEquiv_symm_comp_mk {m n : ℕ} (hle : m ≤ n) :
    (factorPow v.asIdeal hle).comp ((quotientPowEquiv K v n).symm.toRingHom.comp (π _)) =
    (quotientPowEquiv K v m).symm.toRingHom.comp (π _) :=
  RingHom.ext fun x ↦ (quotientPowEquiv K v m).injective <| by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← factorPow_quotientPowEquiv, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      factor_mk]

/-- The ring homomorphism `lim R / 𝔓 ^ n → 𝒪_v`, the limit of the isomorphisms
`R / 𝔓 ^ n ≃+* 𝒪_v / 𝔪 ^ n`. -/
noncomputable def adicCompletionToIntegers :
    AdicCompletion v.asIdeal R →+* v.adicCompletionIntegers K :=
  IsAdicComplete.liftRingHom (maximalIdeal (v.adicCompletionIntegers K))
    (fun n ↦ (quotientPowEquiv K v n).toRingHom.comp (AdicCompletion.evalₐ v.asIdeal n).toRingHom)
    (factorPow_comp_quotientPowEquiv_comp_evalₐ K v)

/-- The ring homomorphism `𝒪_v → lim R / 𝔓 ^ n`, the limit of the isomorphisms
`𝒪_v / 𝔪 ^ n ≃+* R / 𝔓 ^ n`. -/
noncomputable def integersToAdicCompletion :
    v.adicCompletionIntegers K →+* AdicCompletion v.asIdeal R :=
  AdicCompletion.liftRingHom v.asIdeal
    (fun n ↦ (quotientPowEquiv K v n).symm.toRingHom.comp (π _))
    (factorPow_comp_quotientPowEquiv_symm_comp_mk K v)

/-- The isomorphism `lim R / 𝔓 ^ n ≃+* 𝒪_v` (LMFDB `nf.padic_completion`) between the inverse limit
of the `R / 𝔓 ^ n` and the ring of integers of the completion `K_v`. -/
noncomputable def adicCompletionRingEquiv :
    AdicCompletion v.asIdeal R ≃+* v.adicCompletionIntegers K :=
  RingEquiv.ofRingHom (adicCompletionToIntegers K v) (integersToAdicCompletion K v)
    (DFunLike.coe_injective <| IsHausdorff.funext' (maximalIdeal (v.adicCompletionIntegers K))
      fun n x ↦ by
        rw [RingHom.comp_apply, RingHom.id_apply, adicCompletionToIntegers,
          IsAdicComplete.mk_liftRingHom _ _ (factorPow_comp_quotientPowEquiv_comp_evalₐ K v),
          integersToAdicCompletion, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom,
          AdicCompletion.evalₐ_liftRingHom _ _ (factorPow_comp_quotientPowEquiv_symm_comp_mk K v)]
        simp)
    (RingHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ by
      rw [RingHom.comp_apply, RingHom.id_apply, integersToAdicCompletion,
        AdicCompletion.evalₐ_liftRingHom _ _ (factorPow_comp_quotientPowEquiv_symm_comp_mk K v),
        RingHom.comp_apply, adicCompletionToIntegers,
        IsAdicComplete.mk_liftRingHom _ _ (factorPow_comp_quotientPowEquiv_comp_evalₐ K v)]
      simp)

lemma adicCompletionRingEquiv_of (r : R) :
    adicCompletionRingEquiv K v (AdicCompletion.of v.asIdeal R r) = algebraMap R _ r := by
  refine congrFun (IsHausdorff.funext' (maximalIdeal (v.adicCompletionIntegers K))
    (f := fun r ↦ adicCompletionRingEquiv K v (AdicCompletion.of v.asIdeal R r)) fun n r ↦ ?_) r
  rw [adicCompletionRingEquiv, RingEquiv.ofRingHom_apply, adicCompletionToIntegers,
    IsAdicComplete.mk_liftRingHom _ _ (factorPow_comp_quotientPowEquiv_comp_evalₐ K v)]
  simp [quotientPowEquiv_mk]

/-- **The inverse limit `lim R / 𝔓 ^ n` is an integral domain** (LMFDB `nf.padic_completion`), being
isomorphic to the ring of integers of the completion of `R` at `𝔓`. -/
lemma isDomain_adicCompletion : IsDomain (AdicCompletion v.asIdeal R) :=
  (adicCompletionRingEquiv (FractionRing R) v).toMulEquiv.isDomain _

/-- **The field of fractions of `lim R / 𝔓 ^ n` is `K_v`** (LMFDB `nf.padic_completion`), the
completion of `K` at `𝔓`, through the isomorphism `lim R / 𝔓 ^ n ≃+* 𝒪_v`. -/
lemma isFractionRing_adicCompletion :
    letI : Algebra (AdicCompletion v.asIdeal R) (v.adicCompletion K) :=
      ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).comp
        (adicCompletionRingEquiv K v).toRingHom).toAlgebra
    IsFractionRing (AdicCompletion v.asIdeal R) (v.adicCompletion K) :=
  (IsFractionRing.isFractionRing_iff_of_base_ringEquiv _ (adicCompletionRingEquiv K v).symm).1
    inferInstance

end IsDedekindDomain.HeightOneSpectrum
