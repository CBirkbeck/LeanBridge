import Mathlib.GroupTheory.FiniteAbelian.Basic
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.ConductorInvertible
import LeanBridge.ForMathlib.RingTheory.FractionalIdeal.LocallyPrincipalInvertible

/-!
# The dimension of a fractional ideal at a residue field

Let `R` be an order in an étale `ℚ`-algebra `K`, a finite product of number fields, and `I` a
fractional `R`-ideal, a finitely generated `R`-submodule of `K` containing a non-zero-divisor of `K`
(LMFDB `av.fq.singular_dimensions`). For every maximal ideal `𝔓` of `R`, the residue field `R / 𝔓`
is finite and `I / 𝔓I` is a finite-dimensional vector space over it. Its dimension is `1` exactly
when the localisation `I_𝔓` is a principal `R_𝔓`-submodule of `K_𝔓`; `I` is invertible exactly
when it is locally principal at every maximal ideal; and if `I` is not locally principal at `𝔓`,
then `𝔓` is a singular prime of `R`, since the maximal ideals not containing the conductor are
invertible.

The primes `𝔓` of the knowl are the maximal ideals of `R` ("a maximal ideal, or prime", LMFDB
`av.fq.singular_primes`), those with finite residue field: an order has dimension one, its other
prime ideals being the kernels of its maps to the factors of `K`. The invertibility criterion holds
with all prime ideals as well.

The orders here are the subrings `R` of `K` whose additive group is a lattice, finitely generated
and spanning `K` over `ℚ` (`Submodule.IsLattice`). Then `K` is the total ring of fractions of `R`
and `R` is Noetherian, so the fractional ideals of `R` in Mathlib's sense (`FractionalIdeal`) are
its finitely generated `R`-submodules of `K`; the LMFDB's fractional ideals are those containing a
non-zero-divisor of `K`, which is then a unit of `K`. The instances `Module.Finite ℤ R`,
`IsFractionRing R K` and `IsNoetherianRing R` record these facts. Instance search finds them when
the `ℤ`-algebra structure of `K` is `Ring.toIntAlgebra`, as for a variable `K`; for a concrete `K`
with another one, such as `Fin n → ℚ` or an `AdjoinRoot`, they apply by name.

## Main results

* `Subalgebra.finite_quotient_of_isLattice`: the residue fields of an order are finite.
* `FractionalIdeal.finite_quotient_smul_top_of_isLattice`: `I / 𝔓I` is a finite-dimensional vector
  space over `R / 𝔓`.
* `FractionalIdeal.residueFinrank_eq_one_iff_isPrincipal_localized`: `I / 𝔓I` has dimension `1`
  over `R / 𝔓` if and only if `I_𝔓` is principal.
* `FractionalIdeal.isUnit_iff_forall_isPrincipal_localized`: `I` is invertible if and only if it is
  locally principal at every maximal ideal.
* `FractionalIdeal.isUnit_iff_forall_isPrime_isPrincipal_localized`: the same at every prime ideal.
* `FractionalIdeal.mem_singularPrimes_of_not_isPrincipal_localized`: a maximal ideal at which `I` is
  not locally principal is a singular prime.
-/

open Module Submodule

open scoped nonZeroDivisors

namespace Submodule

variable {K : Type*} [CommRing K] [Algebra ℚ K]

lemma isArtinianRing_of_isLattice (M : Submodule ℤ K) [M.IsLattice ℚ] : IsArtinianRing K := by
  rcases IsLattice.fg (M := M) with ⟨T, hT⟩
  have : Module.Finite ℚ K :=
    ⟨⟨T, by rw [← span_span_of_tower ℤ, hT]; exact IsLattice.span_eq_top⟩⟩
  exact isArtinian_of_tower ℚ inferInstance

lemma isUnit_of_mem_nonZeroDivisors_of_isLattice (M : Submodule ℤ K) [M.IsLattice ℚ] {x : K}
    (hx : x ∈ K⁰) : IsUnit x :=
  have : IsArtinianRing K := isArtinianRing_of_isLattice M
  IsArtinianRing.isUnit_of_mem_nonZeroDivisors hx

end Submodule

namespace Subalgebra

variable {K : Type*} [CommRing K] [Algebra ℚ K] (R : Subalgebra ℤ K)

private lemma isUnit_natCast_of_ne_zero {n : ℕ} (hn : n ≠ 0) : IsUnit (n : K) := by
  rw [← map_natCast (algebraMap ℚ K)]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)).map _

lemma natCast_mem_nonZeroDivisors {n : ℕ} (hn : n ≠ 0) : (n : R) ∈ R⁰ :=
  mem_nonZeroDivisors_iff_right.mpr fun r hr ↦ Subtype.ext <|
    (isUnit_natCast_of_ne_zero hn).mul_left_eq_zero.mp (by simpa using congrArg Subtype.val hr)

variable [(toSubmodule R).IsLattice ℚ]

instance : Module.Finite ℤ R :=
  .equiv R.toSubmoduleEquiv

instance : IsFractionRing R K := by
  have hR : span ℚ (R : Set K) = ⊤ := IsLattice.span_eq_top (M := toSubmodule R)
  have : IsArtinianRing K := isArtinianRing_of_isLattice (toSubmodule R)
  refine (isLocalization_iff _ _).mpr
    ⟨fun y ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ⟨1, by rw [Subtype.ext h]⟩⟩
  · refine IsArtinianRing.isUnit_of_mem_nonZeroDivisors <|
      mem_nonZeroDivisors_iff_right.mpr fun k hk ↦ ?_
    rcases R.exists_natCast_mul_mem_of_span_eq_top hR k with ⟨n, hn, hnk⟩
    have h0 : (⟨n * k, hnk⟩ : R) * y = 0 :=
      Subtype.ext <| by simpa [mul_assoc] using congrArg ((n : K) * ·) hk
    exact (isUnit_natCast_of_ne_zero hn).mul_right_eq_zero.mp <|
      congrArg Subtype.val (mem_nonZeroDivisors_iff_right.mp y.2 _ h0)
  · rcases R.exists_natCast_mul_mem_of_span_eq_top hR z with ⟨n, hn, hnz⟩
    exact ⟨⟨⟨n * z, hnz⟩, ⟨n, R.natCast_mem_nonZeroDivisors hn⟩⟩, by simp [mul_comm]⟩

instance : IsNoetherianRing R :=
  isNoetherian_of_tower ℤ inferInstance

/-- **The residue fields of an order are finite** (LMFDB `av.fq.singular_dimensions`): a maximal
ideal `𝔓` of an order `R` contains a nonzero integer `n`, and `R / 𝔓` is a finitely generated
abelian group killed by `n`. -/
lemma finite_quotient_of_isLattice (𝔓 : Ideal R) [𝔓.IsMaximal] : Finite (R ⧸ 𝔓) := by
  rcases R.exists_intCast_mem 𝔓 with ⟨n, hn0, hn⟩
  have : Module.Finite ℤ (R ⧸ 𝔓) := .of_surjective (𝔓.mkQ.restrictScalars ℤ) 𝔓.mkQ_surjective
  refine Module.finite_of_fg_torsion _ fun x ↦ ?_
  rcases 𝔓.mkQ_surjective x with ⟨r, rfl⟩
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn0⟩, ?_⟩
  rw [Submonoid.smul_def, ← map_zsmul, zsmul_eq_mul, ← LinearMap.mem_ker, ker_mkQ]
  exact 𝔓.mul_mem_right r hn

end Subalgebra

namespace FractionalIdeal

variable {K : Type*} [CommRing K] [Algebra ℚ K] {R : Subalgebra ℤ K}
  [(Subalgebra.toSubmodule R).IsLattice ℚ] {I : FractionalIdeal R⁰ K} (𝔓 : Ideal R)

lemma exists_isUnit_mem_of_isLattice (hI : ∃ x ∈ I, x ∈ K⁰) : ∃ u ∈ I, IsUnit u := by
  rcases hI with ⟨u, hu, hu'⟩
  exact ⟨u, hu, isUnit_of_mem_nonZeroDivisors_of_isLattice (Subalgebra.toSubmodule R) hu'⟩

variable (I) in
/-- **The quotient `I / 𝔓I` of a fractional ideal of an order is a finite-dimensional vector space
over the residue field `R / 𝔓`** (LMFDB `av.fq.singular_dimensions`), as `I` is finitely
generated. -/
lemma finite_quotient_smul_top_of_isLattice : Module.Finite (R ⧸ 𝔓) (I ⧸ 𝔓 • (⊤ : Submodule R I)) :=
  have : Module.Finite R I := Finite.iff_fg.mpr (fg_coe_of_isNoetherianRing I)
  .of_restrictScalars_finite R _ _

/-- **A fractional ideal `I` of an order `R` has `I / 𝔓I` of dimension `1` over `R / 𝔓` if and only
if its localisation `I_𝔓` is a principal `R_𝔓`-submodule of `K_𝔓`**, at every maximal ideal `𝔓` of
`R` (LMFDB `av.fq.singular_dimensions`). -/
lemma residueFinrank_eq_one_iff_isPrincipal_localized (hI : ∃ x ∈ I, x ∈ K⁰) [𝔓.IsMaximal] :
    (I : Submodule R K).residueFinrank 𝔓 = 1 ↔
      ((I : Submodule R K).localized 𝔓.primeCompl).IsPrincipal := by
  rcases exists_isUnit_mem_of_isLattice hI with ⟨u, hu, hu'⟩
  rw [residueFinrank_eq_one_iff (fg_coe_of_isNoetherianRing I) hu hu',
    isLocallyPrincipalAt_iff_isPrincipal_localized]

/-- **A fractional ideal of an order is invertible if and only if it is locally principal at every
maximal ideal** (LMFDB `av.fq.singular_dimensions`), its localisation `I_𝔓` being a principal
`R_𝔓`-submodule of `K_𝔓` for every maximal ideal `𝔓` of `R`. -/
lemma isUnit_iff_forall_isPrincipal_localized (hI : ∃ x ∈ I, x ∈ K⁰) : IsUnit I ↔
    ∀ (𝔓 : Ideal R) [𝔓.IsMaximal], ((I : Submodule R K).localized 𝔓.primeCompl).IsPrincipal := by
  rcases exists_isUnit_mem_of_isLattice hI with ⟨u, hu, hu'⟩
  rw [isUnit_iff_forall_isLocallyPrincipalAt (fg_coe_of_isNoetherianRing I) hu hu']
  exact forall_congr' fun 𝔓 ↦ ⟨fun h h𝔓 ↦ isLocallyPrincipalAt_iff_isPrincipal_localized.mp (h h𝔓),
    fun h h𝔓 ↦ isLocallyPrincipalAt_iff_isPrincipal_localized.mpr h⟩

/-- **A fractional ideal of an order is invertible if and only if it is locally principal at every
prime ideal** (LMFDB `av.fq.singular_dimensions`). -/
lemma isUnit_iff_forall_isPrime_isPrincipal_localized (hI : ∃ x ∈ I, x ∈ K⁰) : IsUnit I ↔
    ∀ (𝔓 : Ideal R) [𝔓.IsPrime], ((I : Submodule R K).localized 𝔓.primeCompl).IsPrincipal :=
  ⟨fun h _ h𝔓 ↦ isLocallyPrincipalAt_iff_isPrincipal_localized.mp
    (isLocallyPrincipalAt_of_isUnit h h𝔓.ne_top),
    fun h ↦ (isUnit_iff_forall_isPrincipal_localized hI).mpr fun 𝔓 _ ↦ h 𝔓⟩

variable {𝔓} in
/-- **A maximal ideal of an order at which a fractional ideal is not locally principal is a singular
prime** (LMFDB `av.fq.singular_dimensions`): a maximal ideal `𝔓` not containing the conductor is
invertible, and then every fractional ideal is locally principal at `𝔓`. -/
lemma mem_singularPrimes_of_not_isPrincipal_localized [Algebra.Etale ℚ K] (hI : ∃ x ∈ I, x ∈ K⁰)
    [𝔓.IsMaximal] (h : ¬((I : Submodule R K).localized 𝔓.primeCompl).IsPrincipal) :
    𝔓 ∈ R.singularPrimes := by
  refine ⟨‹_›, by_contra fun h𝔓 ↦ h ?_⟩
  rcases exists_isUnit_mem_of_isLattice hI with ⟨u, hu, hu'⟩
  exact isLocallyPrincipalAt_iff_isPrincipal_localized.mp <|
    isLocallyPrincipalAt_of_isUnit_coeIdeal (R.isUnit_of_not_relativeConductor_le h𝔓) hu hu'

end FractionalIdeal
