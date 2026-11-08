import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Nakayama
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.MultiplierRing
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.OrderIndex
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.SingularPrime

/-!
# The invertible maximal ideals of an order and its conductor

Let `R` be an order in an étale `ℚ`-algebra `K`, a subring whose additive group is finitely
generated and spans `K` over `ℚ`, `𝒪_K` the maximal order, the integral closure of `ℤ` in `K`, and
`𝔣_R = (R : 𝒪_K)` the conductor of `R` (LMFDB `av.endomorphism_ring_conductor`). A maximal ideal
`𝔪` of `R` is non-invertible, as a fractional ideal, exactly when `𝔣_R ⊆ 𝔪`.

* If `𝔣_R ⊆ 𝔪` and `𝔪 J = R`, then `J 𝔣_R ⊆ 𝔣_R`, as `𝔣_R` is an `𝒪_K`-ideal contained in `R`;
  `𝔣_R` is a finitely generated abelian group containing the unit `[𝒪_K : R]` of `K`, so `J` is
  integral, `J ⊆ 𝒪_K`, and `1 ∈ 𝔪 J ⊆ 𝔪 𝒪_K`, which Nakayama's lemma forbids: `𝒪_K` is a finitely
  generated `R`-module.
* If `c ∈ 𝔣_R \ 𝔪`, write `1 = r c + a` with `a ∈ 𝔪`. As `𝒪_K` is a product of Dedekind domains,
  the rings of integers of the factors `K ⧸ 𝔐` of `K`, there is `z ∉ 𝒪_K` with `z 𝔪 ⊆ 𝒪_K`: in a
  factor where `𝔪` generates a proper ideal of the ring of integers, `z` comes from the inverse of
  that ideal. Then `w = c z` satisfies `w 𝔪 ⊆ R` but not `w 𝔪 ⊆ 𝔪`, since otherwise `w ∈ 𝒪_K` and
  `z = r w + z a ∈ 𝒪_K`. So `𝔪 (R + R w)` is an ideal of `R` strictly containing `𝔪`, hence `R`.

The components are those of the decomposition `IsArtinianRing.equivPi` of a reduced Artinian ring
into the product of its residue fields: `IsArtinianRing.single 𝔐 x` is the element with component
`x` at `𝔐` and `0` elsewhere, and an element is integral exactly when all its components are.

## Main definitions

* `IsArtinianRing.single`: the element of a reduced Artinian ring with a single nonzero component.

## Main results

* `IsArtinianRing.isIntegral_iff_forall_isIntegral_mk`: an element of a reduced Artinian ring is
  integral exactly when its components are.
* `Subalgebra.not_isUnit_of_relativeConductor_le` (LMFDB `av.endomorphism_ring_conductor`): a
  maximal ideal containing the conductor is not invertible.
* `Subalgebra.isUnit_of_not_relativeConductor_le` (LMFDB `av.endomorphism_ring_conductor`): a
  maximal ideal not containing the conductor is invertible.
* `Subalgebra.not_isUnit_iff_relativeConductor_le` (LMFDB `av.endomorphism_ring_conductor`): a
  maximal ideal of an order in an étale `ℚ`-algebra is non-invertible exactly when it contains the
  conductor.
* `Subalgebra.mem_singularPrimes_iff_not_isUnit`: the singular primes of an order are its
  non-invertible maximal ideals.
-/

open Module Polynomial Submodule

open scoped nonZeroDivisors

open Algebra (FormallyUnramified)

namespace IsArtinianRing

variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

open Classical in
/-- The element of a reduced Artinian ring `A` with component `x` at the maximal ideal `𝔐` and `0`
at the others, in the decomposition of `A` into the product of its residue fields
(`IsArtinianRing.equivPi`). -/
noncomputable def single (𝔐 : MaximalSpectrum A) (x : A ⧸ 𝔐.asIdeal) : A :=
  (equivPi A).symm (Pi.single 𝔐 x)

variable {𝔐 : MaximalSpectrum A}

lemma mk_single_self (x : A ⧸ 𝔐.asIdeal) : ((single 𝔐 x : A) : A ⧸ 𝔐.asIdeal) = x := by
  classical
  exact (congrFun ((equivPi A).apply_symm_apply (Pi.single 𝔐 x)) 𝔐).trans (Pi.single_eq_same _ _)

lemma mk_single_of_ne {𝔐' : MaximalSpectrum A} (h : 𝔐' ≠ 𝔐) (x : A ⧸ 𝔐.asIdeal) :
    ((single 𝔐 x : A) : A ⧸ 𝔐'.asIdeal) = 0 := by
  classical
  exact (congrFun ((equivPi A).apply_symm_apply (Pi.single 𝔐 x)) 𝔐').trans
    (Pi.single_eq_of_ne h _)

lemma ext_mk {x y : A} (h : ∀ 𝔐 : MaximalSpectrum A, (x : A ⧸ 𝔐.asIdeal) = y) : x = y :=
  (equivPi A).injective <| funext h

lemma single_mul (x y : A ⧸ 𝔐.asIdeal) : single 𝔐 (x * y) = single 𝔐 x * single 𝔐 y := by
  classical
  simp only [single, Pi.single_mul, map_mul]

lemma single_add (x y : A ⧸ 𝔐.asIdeal) : single 𝔐 (x + y) = single 𝔐 x + single 𝔐 y := by
  classical
  simp only [single, Pi.single_add, map_add]

lemma single_zero : single 𝔐 (0 : A ⧸ 𝔐.asIdeal) = 0 := by
  classical
  simp only [single, Pi.single_zero, map_zero]

lemma single_mk (x : A) : single 𝔐 (x : A ⧸ 𝔐.asIdeal) = x * single 𝔐 1 := by
  refine ext_mk fun 𝔐' ↦ ?_
  rw [map_mul]
  by_cases h : 𝔐' = 𝔐
  · subst h
    rw [mk_single_self, mk_single_self, mul_one]
  · rw [mk_single_of_ne h, mk_single_of_ne h, mul_zero]

lemma sum_single_one [Fintype (MaximalSpectrum A)] : ∑ 𝔐 : MaximalSpectrum A, single 𝔐 1 = 1 := by
  classical
  simp only [single, ← map_sum, Finset.univ_sum_single]
  exact map_one _

open Ideal in
/-- **An element of a reduced Artinian ring is integral exactly when its components are**, the
components of `x` being its images in the residue fields of `A`: `x` is a root of the product of
monic polynomials annihilating them. -/
lemma isIntegral_iff_forall_isIntegral_mk {R : Type*} [CommRing R] [Algebra R A] (x : A) :
    IsIntegral R x ↔ ∀ 𝔐 : MaximalSpectrum A, IsIntegral R (x : A ⧸ 𝔐.asIdeal) := by
  refine ⟨fun hx 𝔐 ↦ hx.map (Quotient.mkₐ R 𝔐.asIdeal), fun h ↦ ?_⟩
  have hfin : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  choose p hp hpx using h
  refine ⟨∏ 𝔐, p 𝔐, monic_prod_of_monic _ _ fun 𝔐 _ ↦ hp 𝔐, ?_⟩
  refine (equivPi A).injective <| funext fun 𝔐 ↦ ?_
  rw [map_zero, Pi.zero_apply, equivPi_apply, hom_eval₂, eval₂_finsetProd,
    ← Quotient.algebraMap_eq]
  exact Finset.prod_eq_zero (Finset.mem_univ 𝔐) (hpx 𝔐)

lemma isIntegral_single {R : Type*} [CommRing R] [Algebra R A] {x : A ⧸ 𝔐.asIdeal}
    (hx : IsIntegral R x) : IsIntegral R (single 𝔐 x) := by
  refine (isIntegral_iff_forall_isIntegral_mk _).mpr fun 𝔐' ↦ ?_
  by_cases h : 𝔐' = 𝔐
  · subst h
    rwa [mk_single_self]
  · rw [mk_single_of_ne h]
    exact isIntegral_zero

end IsArtinianRing

namespace Subalgebra

variable {K : Type*} [CommRing K]

lemma isIntegral_of_forall_mul_mem {F : Submodule ℤ K} (hF : F.FG) {c : K} (hc : IsUnit c)
    (hcF : c ∈ F) {x : K} (hx : ∀ y ∈ F, x * y ∈ F) : IsIntegral ℤ x := by
  let S : Subalgebra ℤ K :=
    { carrier := {z | ∀ y ∈ F, z * y ∈ F}
      mul_mem' := fun {a b} ha hb y hy ↦ by rw [mul_assoc]; exact ha _ (hb y hy)
      one_mem' := fun y hy ↦ by rwa [one_mul]
      add_mem' := fun {a b} ha hb y hy ↦ by rw [add_mul]; exact F.add_mem (ha y hy) (hb y hy)
      zero_mem' := fun y _ ↦ by rw [zero_mul]; exact F.zero_mem
      algebraMap_mem' := fun n y hy ↦ by
        rw [algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul]
        exact F.smul_mem n hy }
  have hS : toSubmodule S ≤ F.map (LinearMap.mulLeft ℤ ((hc.unit⁻¹ : Kˣ) : K)) := fun z hz ↦
    ⟨z * c, hz c hcF, by rw [LinearMap.mulLeft_apply, mul_comm, mul_assoc, hc.mul_val_inv,
      mul_one]⟩
  exact IsIntegral.of_mem_of_fg S ((hF.map _).of_le hS) x hx

variable (R : Subalgebra ℤ K)

lemma natCast_maximalOrderIndex_mul_mem {o : K} (ho : o ∈ integralClosure ℤ K) :
    (R.maximalOrderIndex : K) * o ∈ R := by
  have h : R.maximalOrderIndex • o ∈ R :=
    AddSubgroup.nsmul_relIndex_mem (toSubmodule R).toAddSubgroup
      (K := (toSubmodule (integralClosure ℤ K)).toAddSubgroup) ho
  rwa [nsmul_eq_mul] at h

variable [Algebra ℚ K]

variable [Algebra.Etale ℚ K] in
lemma fg_span_integralClosure : (span R (integralClosure ℤ K : Set K)).FG := by
  rcases (Finite.iff_fg (N := toSubmodule (integralClosure ℤ K))).mp
    (.equiv (integralClosure ℤ K).toSubmoduleEquiv.symm) with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  rw [← span_span_of_tower ℤ, hs]
  rfl

variable [(toSubmodule R).IsLattice ℚ]

lemma mem_integralClosure_of_mem_span {n : K} (hn : n ∈ span R (integralClosure ℤ K : Set K)) :
    n ∈ integralClosure ℤ K := by
  induction hn using span_induction with
  | mem x hx => exact hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def]
    exact mul_mem (le_integralClosure_of_fg IsLattice.fg r.2) hx

lemma mul_mem_smul_span_integralClosure (𝔞 : Ideal R) {n x : K} (hn : n ∈ integralClosure ℤ K)
    (hx : x ∈ 𝔞 • span R (integralClosure ℤ K : Set K)) :
    n * x ∈ 𝔞 • span R (integralClosure ℤ K : Set K) := by
  refine smul_induction_on hx (fun a ha y hy ↦ ?_) fun y z hy hz ↦ ?_
  · rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
    exact smul_mem_smul ha <| subset_span <| mul_mem hn <| R.mem_integralClosure_of_mem_span hy
  · rw [mul_add]
    exact add_mem hy hz

open Ideal in
lemma isIntegral_mk {𝔐 : MaximalSpectrum K} (m : R) : IsIntegral ℤ ((m : K) : K ⧸ 𝔐.asIdeal) :=
  (le_integralClosure_of_fg IsLattice.fg m.2).map (Quotient.mkₐ ℤ 𝔐.asIdeal)

lemma exists_intCast_mem (𝔪 : Ideal R) [𝔪.IsMaximal] : ∃ n : ℤ, n ≠ 0 ∧ (n : R) ∈ 𝔪 := by
  have hfin : Module.Finite ℤ R := .equiv R.toSubmoduleEquiv
  have hmax : (𝔪.under ℤ).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔪
  rcases Submodule.exists_mem_ne_zero_of_ne_bot
    (Ring.ne_bot_of_isMaximal_of_not_isField hmax Int.not_isField) with ⟨n, hn, hn0⟩
  exact ⟨n, hn0, by simpa using hn⟩

lemma mem_integralClosure_of_forall_mul_mem (𝔪 : Ideal R) [𝔪.IsMaximal] {w : K}
    (hw : ∀ m ∈ 𝔪, ∃ m' ∈ 𝔪, (m' : K) = w * m) : w ∈ integralClosure ℤ K := by
  rcases R.exists_intCast_mem 𝔪 with ⟨n, hn0, hn⟩
  let F : Submodule ℤ K := (𝔪.restrictScalars ℤ).map R.val.toLinearMap
  have hmemF {x : K} : x ∈ F ↔ ∃ m ∈ 𝔪, (m : K) = x := by
    simp [F]
  have hF : F.FG := (IsLattice.fg (M := toSubmodule R)).of_le fun x hx ↦ by
    rcases hmemF.mp hx with ⟨m, -, rfl⟩
    exact m.2
  have hnK : IsUnit (n : K) := by
    rw [← map_intCast (algebraMap ℚ K)]
    exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn0)).map _
  refine isIntegral_of_forall_mul_mem hF hnK (hmemF.mpr ⟨n, hn, by simp⟩) fun y hy ↦ ?_
  rcases hmemF.mp hy with ⟨m, hm, rfl⟩
  rcases hw m hm with ⟨m', hm', hm'w⟩
  exact hmemF.mpr ⟨m', hm', hm'w⟩

variable [IsArtinianRing K] [IsReduced K] in
lemma single_mem_smul_span (𝔪 : Ideal R) (𝔐 : MaximalSpectrum K)
    {a : integralClosure ℤ (K ⧸ 𝔐.asIdeal)} (ha : a ∈ Ideal.span
      {a : integralClosure ℤ (K ⧸ 𝔐.asIdeal) | ∃ m ∈ 𝔪, (a : K ⧸ 𝔐.asIdeal) = (m : K)}) :
    IsArtinianRing.single 𝔐 (a : K ⧸ 𝔐.asIdeal) ∈ 𝔪 • span R (integralClosure ℤ K : Set K) := by
  induction ha using span_induction with
  | mem a ha =>
    rcases ha with ⟨m, hm, ha⟩
    rw [ha, IsArtinianRing.single_mk]
    exact smul_mem_smul hm (subset_span (IsArtinianRing.isIntegral_single isIntegral_one))
  | zero =>
    rw [ZeroMemClass.coe_zero, IsArtinianRing.single_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [AddMemClass.coe_add, IsArtinianRing.single_add]
    exact add_mem ha hb
  | smul a b _ hb =>
    rw [smul_eq_mul, MulMemClass.coe_mul, IsArtinianRing.single_mul]
    exact R.mul_mem_smul_span_integralClosure 𝔪 (IsArtinianRing.isIntegral_single a.2) hb

variable [Algebra.Etale ℚ K]

lemma isUnit_natCast_maximalOrderIndex : IsUnit (R.maximalOrderIndex : K) := by
  rw [← map_natCast (algebraMap ℚ K)]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr R.maximalOrderIndex_pos.ne')).map _

lemma one_notMem_smul_span_integralClosure (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] :
    (1 : K) ∉ 𝔪 • span R (integralClosure ℤ K : Set K) := fun h1 ↦ by
  have hle : span R (integralClosure ℤ K : Set K) ≤ 𝔪 • span R (integralClosure ℤ K : Set K) :=
    fun n hn ↦ by
      simpa using R.mul_mem_smul_span_integralClosure 𝔪 (R.mem_integralClosure_of_mem_span hn) h1
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 _ R.fg_span_integralClosure hle
    with ⟨r, hr1, hr⟩
  have hr0 : r = 0 :=
    Subtype.ext <| by simpa [Algebra.smul_def] using hr 1 (subset_span (one_mem _))
  rw [hr0, zero_sub, neg_mem_iff] at hr1
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr hr1)

variable [IsArtinianRing K] [IsReduced K] in
open Ideal in
lemma span_mk_eq_top (𝔪 : Ideal R) {n : ℤ} (hn0 : n ≠ 0) (hn : (n : R) ∈ 𝔪)
    (𝔐 : MaximalSpectrum K)
    (hcon : ∀ z : K, (∀ m ∈ 𝔪, z * m ∈ integralClosure ℤ K) → z ∈ integralClosure ℤ K) :
    Ideal.span {a : integralClosure ℤ (K ⧸ 𝔐.asIdeal) |
      ∃ m ∈ 𝔪, (a : K ⧸ 𝔐.asIdeal) = (m : K)} = ⊤ := by
  have h𝔐 : 𝔐.asIdeal.IsMaximal := 𝔐.isMaximal
  let : Field (K ⧸ 𝔐.asIdeal) := Quotient.field 𝔐.asIdeal
  have hfin : Module.Finite ℚ K := FormallyUnramified.finite_of_free ℚ K
  have hded : IsDedekindDomain (integralClosure ℤ (K ⧸ 𝔐.asIdeal)) :=
    integralClosure.isDedekindDomain ℤ ℚ (K ⧸ 𝔐.asIdeal)
  have hfrac : IsFractionRing (integralClosure ℤ (K ⧸ 𝔐.asIdeal)) (K ⧸ 𝔐.asIdeal) :=
    integralClosure.isFractionRing_of_finite_extension ℚ (K ⧸ 𝔐.asIdeal)
  have hmemI {m : R} (hm : m ∈ 𝔪) :
      (⟨((m : K) : K ⧸ 𝔐.asIdeal), R.isIntegral_mk m⟩ : integralClosure ℤ (K ⧸ 𝔐.asIdeal)) ∈
        Ideal.span {a : integralClosure ℤ (K ⧸ 𝔐.asIdeal) |
          ∃ m ∈ 𝔪, (a : K ⧸ 𝔐.asIdeal) = (m : K)} :=
    Ideal.subset_span ⟨m, hm, rfl⟩
  by_contra hI
  have hI0 : Ideal.span {a : integralClosure ℤ (K ⧸ 𝔐.asIdeal) |
      ∃ m ∈ 𝔪, (a : K ⧸ 𝔐.asIdeal) = (m : K)} ≠ ⊥ := fun h0 ↦ by
    have h : (⟨(((n : R) : K) : K ⧸ 𝔐.asIdeal), R.isIntegral_mk (n : R)⟩ :
        integralClosure ℤ (K ⧸ 𝔐.asIdeal)) = 0 := by
      rw [← Ideal.mem_bot, ← h0]
      exact hmemI hn
    have hcast : ((n : R) : K) = (n : K) := by
      simp
    have h' : (((n : R) : K) : K ⧸ 𝔐.asIdeal) = 0 := congrArg Subtype.val h
    rw [hcast, map_intCast, ← map_intCast (algebraMap ℚ (K ⧸ 𝔐.asIdeal)),
      map_eq_zero_iff _ (algebraMap ℚ _).injective, Int.cast_eq_zero] at h'
    exact hn0 h'
  rcases FractionalIdeal.exists_notMem_one_of_ne_bot (K := K ⧸ 𝔐.asIdeal) hI0 hI with
    ⟨x, hxI, hx1⟩
  have hxm {m : R} (hm : m ∈ 𝔪) : IsIntegral ℤ (x * ((m : K) : K ⧸ 𝔐.asIdeal)) := by
    rcases (FractionalIdeal.mem_one_iff _).mp
      ((FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)).mp hxI _
        (FractionalIdeal.mem_coeIdeal_of_mem _ (hmemI hm))) with ⟨a, ha⟩
    have hxa : x * ((m : K) : K ⧸ 𝔐.asIdeal) = a := ha.symm
    rw [hxa]
    exact a.2
  have hz : IsArtinianRing.single 𝔐 x ∈ integralClosure ℤ K := hcon _ fun m hm ↦ by
    have h : IsArtinianRing.single 𝔐 x * (m : K) =
        IsArtinianRing.single 𝔐 (x * ((m : K) : K ⧸ 𝔐.asIdeal)) := by
      rw [IsArtinianRing.single_mul, IsArtinianRing.single_mk, mul_left_comm,
        ← IsArtinianRing.single_mul, mul_one, mul_comm]
    rw [h]
    exact IsArtinianRing.isIntegral_single (hxm hm)
  have hx : IsIntegral ℤ x := by
    have h : IsIntegral ℤ (Quotient.mkₐ ℤ 𝔐.asIdeal (IsArtinianRing.single 𝔐 x)) :=
      ((mem_integralClosure_iff ℤ K).mp hz).map (Quotient.mkₐ ℤ 𝔐.asIdeal)
    rwa [Quotient.mkₐ_eq_mk, IsArtinianRing.mk_single_self] at h
  exact hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hx⟩, rfl⟩)

lemma exists_notMem_integralClosure_forall_mul_mem (𝔪 : Ideal R) [𝔪.IsMaximal] :
    ∃ z : K, z ∉ integralClosure ℤ K ∧ ∀ m ∈ 𝔪, z * m ∈ integralClosure ℤ K := by
  have hred : IsReduced K := FormallyUnramified.isReduced_of_field ℚ K
  have hfin : Module.Finite ℚ K := FormallyUnramified.finite_of_free ℚ K
  have hart : IsArtinianRing K := isArtinian_of_tower ℚ inferInstance
  have hfin' : Fintype (MaximalSpectrum K) := Fintype.ofFinite _
  rcases R.exists_intCast_mem 𝔪 with ⟨n, hn0, hn⟩
  by_contra hcon
  have hcon' (z : K) (hz : ∀ m ∈ 𝔪, z * m ∈ integralClosure ℤ K) : z ∈ integralClosure ℤ K :=
    by_contra fun hzO ↦ hcon ⟨z, hzO, hz⟩
  refine R.one_notMem_smul_span_integralClosure 𝔪 ?_
  rw [← IsArtinianRing.sum_single_one]
  refine sum_mem fun 𝔐 _ ↦ ?_
  have h : IsArtinianRing.single 𝔐 ((1 : integralClosure ℤ (K ⧸ 𝔐.asIdeal)) : K ⧸ 𝔐.asIdeal) ∈
      𝔪 • span R (integralClosure ℤ K : Set K) := R.single_mem_smul_span 𝔪 𝔐 <| by
    rw [R.span_mk_eq_top 𝔪 hn0 hn 𝔐 hcon']
    exact mem_top
  rwa [OneMemClass.coe_one] at h

/-- **A maximal ideal of an order containing its conductor is not invertible** (LMFDB
`av.endomorphism_ring_conductor`): if `𝔣_R ⊆ 𝔪` then `𝔪` has no inverse fractional ideal. -/
lemma not_isUnit_of_relativeConductor_le {𝔪 : Ideal R} [𝔪.IsMaximal]
    (h : R.relativeConductor (integralClosure ℤ K) ≤ 𝔪) : ¬IsUnit (𝔪 : FractionalIdeal R⁰ K) := by
  rintro ⟨u, hu⟩
  have hmJ : (𝔪 : FractionalIdeal R⁰ K) * ↑u⁻¹ = 1 := by
    rw [← hu, Units.mul_inv]
  have hRmJ {c : K} (hcR : c ∈ R) (hc : ∀ o ∈ integralClosure ℤ K, c * o ∈ R) {j : K}
      (hj : j ∈ (↑u⁻¹ : FractionalIdeal R⁰ K)) : c * j ∈ R := by
    have hcm : c ∈ (𝔪 : FractionalIdeal R⁰ K) :=
      (FractionalIdeal.mem_coeIdeal R⁰).mpr ⟨⟨c, hcR⟩, h hc, rfl⟩
    have h1 : c * j ∈ (1 : FractionalIdeal R⁰ K) := hmJ ▸ FractionalIdeal.mul_mem_mul hcm hj
    rcases (FractionalIdeal.mem_one_iff R⁰).mp h1 with ⟨r, hr⟩
    exact hr ▸ r.2
  let F : Submodule ℤ K := toSubmodule R ⊓
    ⨅ o ∈ integralClosure ℤ K, (toSubmodule R).comap (LinearMap.mulRight ℤ o)
  have hF : F.FG := (IsLattice.fg (M := toSubmodule R)).of_le inf_le_left
  have hmemF {c : K} : c ∈ F ↔ c ∈ R ∧ ∀ o ∈ integralClosure ℤ K, c * o ∈ R := by
    simp [F]
  have hNF : (R.maximalOrderIndex : K) ∈ F :=
    hmemF.mpr ⟨R.natCast_mem _, fun o ho ↦ R.natCast_maximalOrderIndex_mul_mem ho⟩
  have hJO {j : K} (hj : j ∈ (↑u⁻¹ : FractionalIdeal R⁰ K)) : j ∈ integralClosure ℤ K := by
    refine isIntegral_of_forall_mul_mem hF R.isUnit_natCast_maximalOrderIndex hNF fun c hc ↦ ?_
    rcases hmemF.mp hc with ⟨hcR, hcO⟩
    refine hmemF.mpr ⟨mul_comm c j ▸ hRmJ hcR hcO hj, fun o ho ↦ ?_⟩
    rw [mul_assoc, mul_comm j]
    exact hRmJ (hcO o ho) (fun o' ho' ↦ (mul_assoc c o o').symm ▸ hcO _ (mul_mem ho ho')) hj
  have h1 : (1 : K) ∈ (𝔪 : FractionalIdeal R⁰ K) * ↑u⁻¹ :=
    hmJ ▸ (FractionalIdeal.mem_one_iff R⁰).mpr ⟨1, map_one _⟩
  refine R.one_notMem_smul_span_integralClosure 𝔪 <|
    FractionalIdeal.mul_induction_on h1 (fun i hi j hj ↦ ?_) fun x y hx hy ↦ add_mem hx hy
  rcases (FractionalIdeal.mem_coeIdeal R⁰).mp hi with ⟨m, hm, rfl⟩
  rw [← Algebra.smul_def]
  exact smul_mem_smul hm (subset_span (hJO hj))

/-- **A maximal ideal of an order not containing its conductor is invertible** (LMFDB
`av.endomorphism_ring_conductor`): if `𝔣_R ⊄ 𝔪` then `𝔪 (R + R w) = R` for `w = c z`, with
`c ∈ 𝔣_R \ 𝔪` and `z ∉ 𝒪_K` such that `z 𝔪 ⊆ 𝒪_K`. -/
lemma isUnit_of_not_relativeConductor_le {𝔪 : Ideal R} [h𝔪 : 𝔪.IsMaximal]
    (h : ¬R.relativeConductor (integralClosure ℤ K) ≤ 𝔪) : IsUnit (𝔪 : FractionalIdeal R⁰ K) := by
  rcases R.exists_notMem_integralClosure_forall_mul_mem 𝔪 with ⟨z, hzO, hz⟩
  rcases IsConcreteLE.not_le_iff_exists.mp h with ⟨c, hcf, hc𝔪⟩
  rcases h𝔪.exists_inv hc𝔪 with ⟨r, a, ha, hra⟩
  have hwR {m : R} (hm : m ∈ 𝔪) : (c : K) * z * m ∈ R := by
    rw [mul_assoc]
    exact hcf _ (hz m hm)
  have hm0 : ∃ m : R, ∃ hm : m ∈ 𝔪, (⟨(c : K) * z * m, hwR hm⟩ : R) ∉ 𝔪 := by
    by_contra hcon
    have hw : (c : K) * z ∈ integralClosure ℤ K := R.mem_integralClosure_of_forall_mul_mem 𝔪
      fun m hm ↦ ⟨_, by_contra fun h' ↦ hcon ⟨m, hm, h'⟩, rfl⟩
    refine hzO ?_
    have hz1 : z = (r : K) * ((c : K) * z) + z * a := by
      have h1 : (r : K) * c + a = 1 := congrArg Subtype.val hra
      linear_combination (-z) * h1
    rw [hz1]
    exact add_mem (mul_mem (le_integralClosure_of_fg IsLattice.fg r.2) hw) (hz a ha)
  rcases hm0 with ⟨m₀, hm₀, hm₀𝔪⟩
  rcases R.exists_natCast_mul_mem_of_span_eq_top (IsLattice.span_eq_top (M := toSubmodule R))
    ((c : K) * z) with ⟨N, hN0, hN⟩
  have hNK : IsUnit (N : K) := by
    rw [← map_natCast (algebraMap ℚ K)]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN0)).map _
  have hJ : IsFractional R⁰ (span R {1, (c : K) * z}) := by
    refine ⟨(N : R), mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ Subtype.ext ?_, fun b hb ↦ ?_⟩
    · have hx' : (x : K) * N = 0 * N := by
        simpa using congrArg Subtype.val hx
      exact hNK.mul_right_cancel hx'
    · rcases mem_span_pair.mp hb with ⟨s, t, rfl⟩
      refine ⟨N * s + t * ⟨_, hN⟩, ?_⟩
      simp [Algebra.smul_def]
      ring1
  let J : FractionalIdeal R⁰ K := ⟨span R {1, (c : K) * z}, hJ⟩
  have hJ1 : (1 : K) ∈ J := subset_span (Set.mem_insert _ _)
  have hJw : (c : K) * z ∈ J := subset_span (Set.mem_insert_of_mem _ rfl)
  have hle : (𝔪 : FractionalIdeal R⁰ K) * J ≤ 1 := FractionalIdeal.mul_le.mpr fun i hi j hj ↦ by
    rcases (FractionalIdeal.mem_coeIdeal R⁰).mp hi with ⟨m, hm, rfl⟩
    rcases mem_span_pair.mp hj with ⟨s, t, rfl⟩
    refine (FractionalIdeal.mem_one_iff R⁰).mpr ⟨m * s + t * ⟨_, hwR hm⟩, ?_⟩
    simp [Algebra.smul_def]
    ring1
  let I' : Ideal R := ((𝔪 : FractionalIdeal R⁰ K) * J : Submodule R K).comap (Algebra.linearMap R K)
  have hmemI' {x : R} : x ∈ I' ↔ (x : K) ∈ (𝔪 : FractionalIdeal R⁰ K) * J := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]
    rfl
  have h𝔪I' : 𝔪 ≤ I' := fun m hm ↦ hmemI'.mpr <| by
    simpa using FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem R⁰ hm) hJ1
  have hI' : I' = ⊤ := by
    by_contra hI'
    refine hm₀𝔪 ((h𝔪.eq_of_le hI' h𝔪I').symm ▸ hmemI'.mpr ?_)
    have h : algebraMap R K m₀ * ((c : K) * z) ∈ (𝔪 : FractionalIdeal R⁰ K) * J :=
      FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem R⁰ hm₀) hJw
    rwa [mul_comm (algebraMap R K m₀)] at h
  have h1 : (1 : K) ∈ (𝔪 : FractionalIdeal R⁰ K) * J :=
    hmemI'.mp (hI' ▸ mem_top : (1 : R) ∈ I')
  exact IsUnit.of_mul_eq_one J (le_antisymm hle (FractionalIdeal.one_le.mpr h1))

/-- **A maximal ideal `𝔪` of an order `R` in an étale `ℚ`-algebra is non-invertible exactly when it
contains the conductor `𝔣_R = (R : 𝒪_K)`** (LMFDB `av.endomorphism_ring_conductor`), invertibility
being that of `𝔪` as a fractional ideal of `R`. -/
lemma not_isUnit_iff_relativeConductor_le (𝔪 : Ideal R) [𝔪.IsMaximal] :
    ¬IsUnit (𝔪 : FractionalIdeal R⁰ K) ↔ R.relativeConductor (integralClosure ℤ K) ≤ 𝔪 :=
  ⟨fun h ↦ by_contra fun h' ↦ h (R.isUnit_of_not_relativeConductor_le h'),
    R.not_isUnit_of_relativeConductor_le⟩

/-- **The singular primes of an order are its non-invertible maximal ideals**: the maximal ideals
containing the conductor (`Subalgebra.singularPrimes`, LMFDB `av.fq.singular_primes`) are those
without an inverse fractional ideal. -/
lemma mem_singularPrimes_iff_not_isUnit (𝔓 : Ideal R) :
    𝔓 ∈ R.singularPrimes ↔ 𝔓.IsMaximal ∧ ¬IsUnit (𝔓 : FractionalIdeal R⁰ K) :=
  and_congr_right fun _ ↦ (R.not_isUnit_iff_relativeConductor_le 𝔓).symm

end Subalgebra
