import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.LinearCombination
import LeanBridge.ForMathlib.RingTheory.FractionalIdeal.LocallyPrincipal

/-!
# Locally principal fractional ideals and invertibility

Let `I` be a fractional ideal of a commutative ring `R` with total ring of fractions `K`, and `𝔓` a
prime ideal of `R`. This file compares three ways of saying that `I` is locally principal at `𝔓`
(LMFDB `av.fq.singular_dimensions`): the localisation `I_𝔓` is a principal `R_𝔓`-submodule of the
localisation `K_𝔓`; there is `x ∈ I` such that every `y ∈ I` has a multiple `s y ∈ R x` with
`s ∉ 𝔓` (`Submodule.IsLocallyPrincipalAt`); and, when `𝔓` is maximal and `I` is finitely
generated, the quotient `I / 𝔓I` has dimension at most one over the residue field `R / 𝔓`, which
by Nakayama's lemma is exactly one when `I` contains a unit of `K`.

It then proves that a finitely generated fractional ideal containing a unit of `K` is invertible
exactly when it is locally principal at every maximal ideal: if `I` is locally principal at `𝔓`,
some `x ∈ I` and `y ∈ (R : I)` have `x y ∉ 𝔓`, so the ideal `I (R : I)` of `R` lies in no maximal
ideal. Finally, over a Noetherian ring, every such fractional ideal is locally principal at a
maximal ideal `𝔓` that is invertible: otherwise `I (R : I) ⊆ 𝔓`, so `(R : I) ⊆ 𝔓 (R : I)`, which
Nakayama's lemma forbids.

## Main results

* `Submodule.isLocallyPrincipalAt_iff_isPrincipal_localized'`: `I` is locally principal at a prime
  `𝔓` if and only if its localisation at `𝔓` is principal.
* `Submodule.residueFinrank_eq_one_iff`: a finitely generated `I` containing a unit of `K` is
  locally principal at a maximal ideal `𝔓` if and only if `I / 𝔓I` has dimension one over `R / 𝔓`.
* `FractionalIdeal.isUnit_iff_forall_isLocallyPrincipalAt`: a finitely generated fractional ideal
  containing a unit is invertible if and only if it is locally principal at every maximal ideal.
* `FractionalIdeal.isLocallyPrincipalAt_of_isUnit_coeIdeal`: over a Noetherian ring, a fractional
  ideal containing a unit is locally principal at every invertible maximal ideal.
-/

open Module Submodule

open Ideal (Quotient.field)

open scoped nonZeroDivisors

attribute [local instance] Quotient.field

namespace Submodule

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {I N : Submodule R K} {𝔓 : Ideal R}
  {u : K}

/-- **A submodule `I` of `K` is locally principal at a prime `𝔓` exactly when its localisation
`I_𝔓` is a principal `R_𝔓`-submodule of the localisation `K_𝔓`**, for any localisations `R_𝔓` of
`R` and `f : K → K_𝔓` of `K` at `𝔓` (LMFDB `av.fq.singular_dimensions`). -/
lemma isLocallyPrincipalAt_iff_isPrincipal_localized' [𝔓.IsPrime] (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.AtPrime S 𝔓] {M : Type*} [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] (f : K →ₗ[R] M) [IsLocalizedModule 𝔓.primeCompl f] :
    I.IsLocallyPrincipalAt 𝔓 ↔ (I.localized' S 𝔓.primeCompl f).IsPrincipal := by
  refine ⟨fun ⟨x, hx, h⟩ ↦ ⟨f x, le_antisymm ?_ ?_⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  · rw [localized'_eq_span, span_le]
    rintro - ⟨y, hy, rfl⟩
    rcases h y hy with ⟨s, hs, hsy⟩
    rcases mem_span_singleton.mp hsy with ⟨r, hr⟩
    refine mem_span_singleton.mpr ⟨IsLocalization.mk' S r (⟨s, hs⟩ : 𝔓.primeCompl), ?_⟩
    rw [← IsLocalizedModule.mk'_one 𝔓.primeCompl f x, IsLocalizedModule.mk'_smul_mk' S, mul_one,
      hr]
    exact IsLocalizedModule.mk'_cancel f y (⟨s, hs⟩ : 𝔓.primeCompl)
  · exact span_le.mpr <| Set.singleton_subset_iff.mpr <|
      (mem_localized' S _ f I _).mpr ⟨x, hx, 1, IsLocalizedModule.mk'_one _ f x⟩
  · rcases (mem_localized' S _ f I a).mp (ha.ge (mem_span_singleton_self a)) with ⟨x, hx, t, rfl⟩
    refine ⟨x, hx, fun y hy ↦ ?_⟩
    rcases mem_span_singleton.mp <| ha.le <|
      (mem_localized' S _ f I _).mpr ⟨y, hy, 1, IsLocalizedModule.mk'_one _ f y⟩ with ⟨c, hc⟩
    rcases IsLocalization.mk'_surjective 𝔓.primeCompl c with ⟨⟨r, s⟩, rfl⟩
    rw [IsLocalizedModule.mk'_smul_mk' S, ← IsLocalizedModule.mk'_one 𝔓.primeCompl f y,
      IsLocalizedModule.mk'_eq_mk'_iff] at hc
    rcases hc with ⟨u, hu⟩
    refine ⟨(u * (s * t) : 𝔓.primeCompl), (u * (s * t)).2, mem_span_singleton.mpr ⟨u * r, ?_⟩⟩
    simpa [Submonoid.smul_def, smul_smul] using hu.symm

lemma isLocallyPrincipalAt_iff_isPrincipal_localized [𝔓.IsPrime] :
    I.IsLocallyPrincipalAt 𝔓 ↔ (I.localized 𝔓.primeCompl).IsPrincipal :=
  isLocallyPrincipalAt_iff_isPrincipal_localized' (Localization 𝔓.primeCompl)
    (LocalizedModule.mkLinearMap 𝔓.primeCompl K)

lemma exists_notMem_forall_smul_mem [𝔓.IsPrime] (T : Finset K) (h : ∀ y ∈ T, ∃ s ∉ 𝔓, s • y ∈ N) :
    ∃ s ∉ 𝔓, ∀ y ∈ span R (T : Set K), s • y ∈ N := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, 𝔓.ne_top_iff_one.mp ‹𝔓.IsPrime›.ne_top, fun y hy ↦ by simp_all⟩
  | insert a T _ ih =>
    rcases h a (Finset.mem_insert_self a T) with ⟨s, hs, hsa⟩
    rcases ih fun y hy ↦ h y (Finset.mem_insert_of_mem hy) with ⟨t, ht, htT⟩
    refine ⟨s * t, ‹𝔓.IsPrime›.mul_notMem hs ht, fun y hy ↦ ?_⟩
    rw [Finset.coe_insert, mem_span_insert] at hy
    rcases hy with ⟨r, z, hz, rfl⟩
    rw [smul_add, mul_smul s t z]
    refine N.add_mem ?_ (N.smul_mem s (htT z hz))
    convert N.smul_mem (t * r) hsa using 1
    rw [smul_smul, smul_smul, mul_comm (t * r) s, mul_assoc]

lemma exists_notMem_forall_smul_mem_of_fg [𝔓.IsPrime] (hI : I.FG)
    (h : ∀ y ∈ I, ∃ s ∉ 𝔓, s • y ∈ N) : ∃ s ∉ 𝔓, ∀ y ∈ I, s • y ∈ N := by
  rcases hI with ⟨T, rfl⟩
  exact exists_notMem_forall_smul_mem T fun y hy ↦ h y (subset_span hy)

lemma isLocallyPrincipalAt_of_mul_eq {x y : K} (hx : x ∈ I) (hy : y ∈ 1 / I) {t : R} (ht : t ∉ 𝔓)
    (hxy : algebraMap R K t = x * y) : I.IsLocallyPrincipalAt 𝔓 :=
  ⟨x, hx, fun z hz ↦ ⟨t, ht, by
    rcases mem_one.mp (mem_div_iff_forall_mul_mem.mp hy z hz) with ⟨c, hc⟩
    exact mem_span_singleton.mpr ⟨c, by rw [Algebra.smul_def, Algebra.smul_def, hc, hxy]; ring1⟩⟩⟩

lemma exists_mul_eq_of_isLocallyPrincipalAt [𝔓.IsPrime] (hI : I.FG) (hu : u ∈ I) (hu' : IsUnit u)
    (h : I.IsLocallyPrincipalAt 𝔓) : ∃ x ∈ I, ∃ y ∈ 1 / I, ∃ t ∉ 𝔓, algebraMap R K t = x * y := by
  rcases h with ⟨x, hx, h⟩
  rcases exists_notMem_forall_smul_mem_of_fg hI h with ⟨s, hs, hsI⟩
  rcases mem_span_singleton.mp (hsI u hu) with ⟨r, hr⟩
  have hU : u * ↑hu'.unit⁻¹ = 1 := hu'.mul_val_inv
  rw [Algebra.smul_def, Algebra.smul_def] at hr
  refine ⟨x, hx, algebraMap R K (s * r) * ↑hu'.unit⁻¹, mem_div_iff_forall_mul_mem.mpr fun z hz ↦ ?_,
    s * s, ‹𝔓.IsPrime›.mul_notMem hs hs, ?_⟩
  · rcases mem_span_singleton.mp (hsI z hz) with ⟨c, hc⟩
    rw [Algebra.smul_def, Algebra.smul_def] at hc
    refine mem_one.mpr ⟨c * s, ?_⟩
    rw [map_mul, map_mul]
    linear_combination (algebraMap R K r * ↑hu'.unit⁻¹) * hc -
      (algebraMap R K c * ↑hu'.unit⁻¹) * hr - (algebraMap R K c * algebraMap R K s) * hU
  · rw [map_mul, map_mul]
    linear_combination (-(algebraMap R K s * ↑hu'.unit⁻¹)) * hr -
      (algebraMap R K s * algebraMap R K s) * hU

lemma finite_quotient_smul_top (hI : I.FG) : Module.Finite (R ⧸ 𝔓) (I ⧸ 𝔓 • (⊤ : Submodule R I)) :=
  have : Module.Finite R I := Finite.iff_fg.mpr hI
  .of_restrictScalars_finite R _ _

section Residue

variable [𝔓.IsMaximal]

open Ideal in
lemma residueFinrank_le_one_of_isLocallyPrincipalAt (h : I.IsLocallyPrincipalAt 𝔓) :
    I.residueFinrank 𝔓 ≤ 1 := by
  rcases h with ⟨x, hx, h⟩
  refine (finrank_le_of_span_eq_top (v := fun _ : Unit ↦ (𝔓 • ⊤ : Submodule R I).mkQ ⟨x, hx⟩)
    (eq_top_iff.mpr fun w _ ↦ ?_)).trans_eq Fintype.card_unit
  rcases (𝔓 • ⊤ : Submodule R I).mkQ_surjective w with ⟨⟨y, hy⟩, rfl⟩
  rcases h y hy with ⟨s, hs, hsy⟩
  rcases mem_span_singleton.mp hsy with ⟨r, hr⟩
  have hs0 : algebraMap R (R ⧸ 𝔓) s ≠ 0 := fun h0 ↦
    hs (Quotient.eq_zero_iff_mem.mp ((Quotient.algebraMap_eq 𝔓).symm ▸ h0))
  have hrs : algebraMap R (R ⧸ 𝔓) r • (𝔓 • ⊤ : Submodule R I).mkQ ⟨x, hx⟩ =
      algebraMap R (R ⧸ 𝔓) s • (𝔓 • ⊤ : Submodule R I).mkQ ⟨y, hy⟩ := by
    rw [algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul]
    exact congrArg _ (Subtype.ext hr)
  rw [Set.range_const, mem_span_singleton]
  refine ⟨(algebraMap R (R ⧸ 𝔓) s)⁻¹ * algebraMap R (R ⧸ 𝔓) r, ?_⟩
  rw [mul_smul, hrs, smul_smul, inv_mul_cancel₀ hs0, one_smul]

lemma isLocallyPrincipalAt_of_residueFinrank_le_one (hI : I.FG) (h : I.residueFinrank 𝔓 ≤ 1) :
    I.IsLocallyPrincipalAt 𝔓 := by
  have : Module.Finite R I := Finite.iff_fg.mpr hI
  have : Module.Finite (R ⧸ 𝔓) (I ⧸ 𝔓 • (⊤ : Submodule R I)) := finite_quotient_smul_top hI
  rcases finrank_le_one_iff.mp h with ⟨v, hv⟩
  rcases (𝔓 • ⊤ : Submodule R I).mkQ_surjective v with ⟨x, rfl⟩
  have hle : (⊤ : Submodule R (I ⧸ R ∙ x)) ≤ 𝔓 • ⊤ := by
    rintro m -
    rcases (R ∙ x).mkQ_surjective m with ⟨y, rfl⟩
    rcases hv ((𝔓 • ⊤ : Submodule R I).mkQ y) with ⟨c, hc⟩
    rcases 𝔓.mkQ_surjective c with ⟨s, rfl⟩
    have hs : s • (𝔓 • ⊤ : Submodule R I).mkQ x = (𝔓 • ⊤ : Submodule R I).mkQ y :=
      (algebraMap_smul (R ⧸ 𝔓) s _).symm.trans hc
    rw [← map_smul, ← LinearMap.sub_mem_ker_iff, ker_mkQ, ← neg_mem_iff, neg_sub] at hs
    have hmem : (R ∙ x).mkQ (y - s • x) ∈ 𝔓 • (⊤ : Submodule R (I ⧸ R ∙ x)) := by
      rw [← (R ∙ x).range_mkQ, ← Submodule.map_top, ← map_smul'']
      exact mem_map_of_mem hs
    have hsx : (R ∙ x).mkQ (s • x) = 0 :=
      LinearMap.mem_ker.mp <| (ker_mkQ (R ∙ x)).symm ▸ smul_mem _ s (mem_span_singleton_self x)
    rwa [map_sub, hsx, sub_zero] at hmem
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔓 ⊤ Finite.fg_top hle with
    ⟨r, hr1, hr⟩
  refine ⟨x, x.2, fun y hy ↦ ⟨r, fun hr𝔓 ↦ ?_, ?_⟩⟩
  · exact ‹𝔓.IsMaximal›.ne_top (𝔓.eq_top_iff_one.mpr (sub_sub_cancel r 1 ▸ sub_mem hr𝔓 hr1))
  · have hy' : (R ∙ x).mkQ (r • ⟨y, hy⟩) = 0 := (map_smul _ r _).trans (hr _ mem_top)
    rw [← LinearMap.mem_ker, ker_mkQ, mem_span_singleton] at hy'
    rcases hy' with ⟨t, ht⟩
    exact mem_span_singleton.mpr ⟨t, congrArg Subtype.val ht⟩

variable [IsFractionRing R K]

lemma one_le_residueFinrank (hI : I.FG) (hu : u ∈ I) (hu' : IsUnit u) : 1 ≤ I.residueFinrank 𝔓 := by
  have : Module.Finite (R ⧸ 𝔓) (I ⧸ 𝔓 • (⊤ : Submodule R I)) := finite_quotient_smul_top hI
  have : Nontrivial (I ⧸ 𝔓 • (⊤ : Submodule R I)) := by
    refine Quotient.nontrivial_iff.mpr fun h ↦ ?_
    rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔓 ⊤ (I.fg_top.mpr hI) h.ge with
      ⟨r, hr1, hr⟩
    have hr0 : r = 0 := by
      have h0 : r • u = 0 := congrArg Subtype.val (hr ⟨u, hu⟩ mem_top)
      rw [Algebra.smul_def, hu'.mul_left_eq_zero] at h0
      exact IsFractionRing.injective R K (h0.trans (map_zero _).symm)
    rw [hr0, zero_sub, neg_mem_iff] at hr1
    exact ‹𝔓.IsMaximal›.ne_top (𝔓.eq_top_iff_one.mpr hr1)
  exact finrank_pos

/-- **A finitely generated submodule `I` of `K` containing a unit of `K` is locally principal at a
maximal ideal `𝔓` if and only if `I / 𝔓I` has dimension one over the residue field `R / 𝔓`** (LMFDB
`av.fq.singular_dimensions`). -/
lemma residueFinrank_eq_one_iff (hI : I.FG) (hu : u ∈ I) (hu' : IsUnit u) :
    I.residueFinrank 𝔓 = 1 ↔ I.IsLocallyPrincipalAt 𝔓 :=
  ⟨fun h ↦ isLocallyPrincipalAt_of_residueFinrank_le_one hI h.le, fun h ↦
    (residueFinrank_le_one_of_isLocallyPrincipalAt h).antisymm (one_le_residueFinrank hI hu hu')⟩

end Residue

end Submodule

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
  {I : FractionalIdeal R⁰ K} {u : K}

lemma isFractional_one_div {N : Submodule R K} (hu : u ∈ N) (hu' : IsUnit u) :
    IsFractional R⁰ (1 / N) := by
  rcases IsLocalization.surj R⁰ (↑hu'.unit⁻¹ : K) with ⟨⟨a, b⟩, hab⟩
  have hU : u * ↑hu'.unit⁻¹ = 1 := hu'.mul_val_inv
  refine ⟨b, b.2, fun y hy ↦ ?_⟩
  rcases mem_one.mp (mem_div_iff_forall_mul_mem.mp hy u hu) with ⟨c, hc⟩
  refine ⟨a * c, ?_⟩
  dsimp only at hab
  rw [map_mul, Algebra.smul_def, hc]
  linear_combination (y * u) * hab.symm + (y * algebraMap R K b) * hU

/-- **A finitely generated fractional ideal containing a unit of `K` is invertible if and only if
it is locally principal at every maximal ideal** (LMFDB `av.fq.singular_dimensions`). -/
lemma isUnit_iff_forall_isLocallyPrincipalAt (hI : (I : Submodule R K).FG) (hu : u ∈ I)
    (hu' : IsUnit u) :
    IsUnit I ↔ ∀ 𝔓 : Ideal R, 𝔓.IsMaximal → (I : Submodule R K).IsLocallyPrincipalAt 𝔓 := by
  refine ⟨fun h 𝔓 h𝔓 ↦ isLocallyPrincipalAt_of_isUnit h h𝔓.ne_top, fun h ↦ ?_⟩
  let J : FractionalIdeal R⁰ K := ⟨1 / (I : Submodule R K), isFractional_one_div hu hu'⟩
  refine IsUnit.of_mul_eq_one J (le_antisymm ?_ ?_)
  · rw [← coe_le_coe, coe_mul, coe_one]
    exact mul_one_div_le_one
  · let 𝔞 : Ideal R :=
      ((I * J : FractionalIdeal R⁰ K) : Submodule R K).comap (Algebra.linearMap R K)
    have h𝔞 : 𝔞 = ⊤ := by
      by_contra h𝔞
      rcases 𝔞.exists_le_maximal h𝔞 with ⟨𝔪, h𝔪, hle⟩
      rcases exists_mul_eq_of_isLocallyPrincipalAt hI hu hu' (h 𝔪 h𝔪) with
        ⟨x, hx, y, hy, t, ht, hxy⟩
      refine ht (hle ?_)
      rw [mem_comap, Algebra.linearMap_apply, hxy, coe_mul]
      exact Submodule.mul_mem_mul hx hy
    have h1 : (1 : R) ∈ 𝔞 := h𝔞 ▸ mem_top
    rw [mem_comap, Algebra.linearMap_apply, map_one] at h1
    exact one_le.mpr h1

variable [IsNoetherianRing R]

variable (I) in
lemma fg_coe_of_isNoetherianRing : (I : Submodule R K).FG := by
  rcases I.isFractional with ⟨a, ha, hI⟩
  have haK : IsUnit (algebraMap R K a) := IsLocalization.map_units K ⟨a, ha⟩
  refine fg_of_fg_map_injective (LinearMap.mulLeft R (algebraMap R K a))
    (fun x y hxy ↦ haK.mul_left_cancel hxy) ?_
  have hle : (I : Submodule R K).map (LinearMap.mulLeft R (algebraMap R K a)) ≤
      LinearMap.range (Algebra.linearMap R K) := by
    rintro - ⟨x, hx, rfl⟩
    rcases hI x hx with ⟨r, hr⟩
    exact ⟨r, hr.trans (Algebra.smul_def a x)⟩
  rw [← map_comap_eq_of_le hle]
  exact (IsNoetherian.noetherian _).map _

/-- **Over a Noetherian ring, a fractional ideal containing a unit of `K` is locally principal at
every invertible maximal ideal `𝔓`** (LMFDB `av.fq.singular_dimensions`): otherwise
`I (R : I) ⊆ 𝔓`, so `(R : I) ⊆ 𝔓 (R : I)`, and Nakayama's lemma gives `r ∉ 𝔓` killing the
non-zero-divisors of `(R : I)`. -/
lemma isLocallyPrincipalAt_of_isUnit_coeIdeal {𝔓 : Ideal R} [𝔓.IsMaximal]
    (h𝔓 : IsUnit (𝔓 : FractionalIdeal R⁰ K)) (hu : u ∈ I) (hu' : IsUnit u) :
    (I : Submodule R K).IsLocallyPrincipalAt 𝔓 := by
  by_contra hn
  let J : FractionalIdeal R⁰ K := ⟨1 / (I : Submodule R K), isFractional_one_div hu hu'⟩
  have hIJ {x y : K} (hx : x ∈ I) (hy : y ∈ 1 / (I : Submodule R K)) :
      ∃ p ∈ 𝔓, algebraMap R K p = x * y := by
    rcases mem_one.mp (mem_div_iff_forall_mul_mem.mp hy x hx) with ⟨c, hc⟩
    exact ⟨c, by_contra fun hc𝔓 ↦ hn <| isLocallyPrincipalAt_of_mul_eq hx hy hc𝔓 <|
      hc.trans (mul_comm y x), hc.trans (mul_comm y x)⟩
  rcases h𝔓.exists_right_inv with ⟨P, hP⟩
  have hJP {y q : K} (hy : y ∈ 1 / (I : Submodule R K)) (hq : q ∈ P) :
      y * q ∈ 1 / (I : Submodule R K) := by
    refine mem_div_iff_forall_mul_mem.mpr fun x hx ↦ ?_
    rcases hIJ hx hy with ⟨p, hp, hpxy⟩
    have h1 : algebraMap R K p * q ∈ (𝔓 : FractionalIdeal R⁰ K) * P :=
      mul_mem_mul (mem_coeIdeal_of_mem R⁰ hp) hq
    rw [hP, hpxy] at h1
    rcases (mem_one_iff R⁰).mp h1 with ⟨c, hc⟩
    exact Submodule.mem_one.mpr ⟨c, hc.trans (by ring1)⟩
  have hle : 1 / (I : Submodule R K) ≤ 𝔓 • (1 / (I : Submodule R K)) := by
    intro y hy
    have h1 : (1 : K) ∈ (𝔓 : FractionalIdeal R⁰ K) * P := hP ▸ one_mem_one R⁰
    have hmul (z : K) (hz : z ∈ (𝔓 : FractionalIdeal R⁰ K) * P) :
        y * z ∈ 𝔓 • (1 / (I : Submodule R K)) := by
      refine FractionalIdeal.mul_induction_on hz (fun i hi j hj ↦ ?_) fun a b ha hb ↦ ?_
      · rcases (mem_coeIdeal R⁰).mp hi with ⟨p, hp, rfl⟩
        rw [mul_left_comm, ← Algebra.smul_def]
        exact smul_mem_smul hp (hJP hy hj)
      · rw [mul_add]
        exact add_mem ha hb
    simpa using hmul 1 h1
  rcases exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔓 _ (fg_coe_of_isNoetherianRing J)
    hle with ⟨r, hr1, hr⟩
  rcases I.isFractional with ⟨a, ha, hIa⟩
  have haJ : algebraMap R K a ∈ 1 / (I : Submodule R K) :=
    mem_div_iff_forall_mul_mem.mpr fun x hx ↦ by
      rcases hIa x hx with ⟨c, hc⟩
      exact mem_one.mpr ⟨c, hc.trans (Algebra.smul_def a x)⟩
  have hra : r * a = 0 := IsFractionRing.injective R K <| by
    rw [map_mul, map_zero, ← Algebra.smul_def]
    exact hr _ haJ
  rw [mem_nonZeroDivisors_iff_right.mp ha r hra, zero_sub, neg_mem_iff] at hr1
  exact ‹𝔓.IsMaximal›.ne_top (𝔓.eq_top_iff_one.mpr hr1)

end FractionalIdeal
