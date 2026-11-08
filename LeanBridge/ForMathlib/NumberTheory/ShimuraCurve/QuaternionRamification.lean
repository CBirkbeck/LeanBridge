import LeanBridge.ForMathlib.Algebra.Quaternion.OfFinrankEqFour
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder
import TauCeti.Algebra.Quaternion.BaseChange
import TauCeti.NumberTheory.QuadraticForm.Global.HilbertSymbol

/-!
# A quaternion algebra over `ℚ` is ramified at finitely many primes

A quaternion algebra `B` over `ℚ`, a central simple `ℚ`-algebra of dimension `4`, is ramified at a
prime `p` if `B ⊗ ℚ_p` is a division algebra, and its discriminant is the product of the ramified
primes (LMFDB `shimcurve.discb`, `QuaternionAlgebra.discriminant`). That product is finite: `B` is
isomorphic to some `(a, b / ℚ) = ℍ[ℚ,a,b]`
(`QuaternionAlgebra.exists_nonempty_algEquiv_of_finrank_eq_four`), so `B ⊗ ℚ_p ≅ ℍ[ℚ_p,a,b]`
(Tau Ceti's `TauCeti.QuaternionAlgebra.baseChangeTwoParams`), which is split, isomorphic to
`M₂(ℚ_p)`, when the norm equation `b = x² - a y²` has a solution in `ℚ_p` (Tau Ceti's splitting
criterion `TauCeti.QuaternionAlgebra.nonempty_algEquiv_matrix_tfae`), that is, when the Hilbert
symbol `(a, b)_p` is `1`. By Hensel's lemma it is `1` at every odd prime at which `a` and `b` are
`p`-adic units, so at all but finitely many primes (Tau Ceti's
`TauCeti.hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace`, read over `ℚ_p` through
`TauCeti.hilbertSymbol_unitAtFinitePlace_rat`).

## Main results

* `QuaternionAlgebra.not_isRamifiedAt_of_exists_eq_sq_sub_mul_sq`: `(a, b / ℚ)` is split at `p` if
  `b = x² - a y²` is solvable in `ℚ_p`.
* `QuaternionAlgebra.finite_setOf_isRamifiedAt` (LMFDB `shimcurve.discb`): a quaternion algebra over
  `ℚ` is ramified at finitely many primes.
* `QuaternionAlgebra.discriminant_eq_prod` (LMFDB `shimcurve.discb`): the discriminant of a
  quaternion algebra over `ℚ` is the product of its ramified primes.
-/

open Module TauCeti

open scoped TensorProduct Quaternion

namespace QuaternionAlgebra

variable {B : Type*} [Ring B] [Algebra ℚ B]

/-- **`(a, b / ℚ)` is split at `p` if the norm equation `b = x² - a y²` is solvable in `ℚ_p`**, for
a `ℚ`-algebra `B ≅ ℍ[ℚ,a,b]`: then `B ⊗ ℚ_p ≅ ℍ[ℚ_p,a,b] ≅ M₂(ℚ_p)` is not a division algebra. -/
lemma not_isRamifiedAt_of_exists_eq_sq_sub_mul_sq {p : ℕ} [Fact p.Prime] {a b : ℚˣ}
    (e : ℍ[ℚ,(a : ℚ),(b : ℚ)] ≃ₐ[ℚ] B) (h : ∃ x y : ℚ_[p], (b : ℚ_[p]) = x ^ 2 - a * y ^ 2) :
    ¬IsRamifiedAt B ⟨p, Fact.out⟩ := by
  let a' : ℚ_[p]ˣ := Units.map (algebraMap ℚ ℚ_[p] : ℚ →* ℚ_[p]) a
  let b' : ℚ_[p]ˣ := Units.map (algebraMap ℚ ℚ_[p] : ℚ →* ℚ_[p]) b
  let _ : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  have hsplit : ¬∀ x : ℍ[ℚ_[p],(a' : ℚ_[p]),(b' : ℚ_[p])], x ≠ 0 → IsUnit x :=
    (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_not_forall_isUnit a' b').mp <|
      (QuaternionAlgebra.nonempty_algEquiv_matrix_iff_exists_eq_sq_sub_mul_sq a' b').mpr <| by
        simpa [a', b'] using h
  let ψ : ℍ[ℚ_[p],(a' : ℚ_[p]),(b' : ℚ_[p])] ≃+* ℚ_[p] ⊗[ℚ] B :=
    (QuaternionAlgebra.baseChangeTwoParams ℚ ℚ_[p] (a : ℚ) (b : ℚ)).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : ℚ_[p] ≃ₐ[ℚ] ℚ_[p]) e).toRingEquiv
  exact fun hram ↦ hsplit fun x hx ↦ (isUnit_map_iff ψ x).mp <|
    hram (ψ x) ((map_ne_zero_iff ψ ψ.injective).mpr hx)

variable (B) [Algebra.IsCentral ℚ B] [IsSimpleRing B]

open Rat HeightOneSpectrum in
/-- **A quaternion algebra over `ℚ` is ramified at finitely many primes** (LMFDB
`shimcurve.discb`): for `B ≅ (a, b / ℚ)`, it is split at every prime `p` at which the Hilbert symbol
`(a, b)_p` is `1`, that is, at all but finitely many primes. -/
lemma finite_setOf_isRamifiedAt (h4 : finrank ℚ B = 4) :
    {p : Nat.Primes | IsRamifiedAt B p}.Finite := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  refine ((hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace a b).image primesEquiv).subset
    fun p hp ↦ ⟨_, fun h ↦ ?_, Equiv.apply_symm_apply _ p⟩
  simp only [hilbertSymbol_unitAtFinitePlace_rat, hilbertSymbol_eq_one_iff] at h
  exact not_isRamifiedAt_of_exists_eq_sq_sub_mul_sq e (by simpa using h) hp

/-- **The discriminant of a quaternion algebra over `ℚ` is the product of its ramified primes**
(LMFDB `shimcurve.discb`), a finite product. -/
lemma discriminant_eq_prod (h4 : finrank ℚ B = 4) :
    discriminant B = ∏ p ∈ (finite_setOf_isRamifiedAt B h4).toFinset, (p : ℕ) := by
  classical
  rw [discriminant, finprod_eq_prod_of_mulSupport_subset _ fun p hp ↦ ?_]
  · exact Finset.prod_congr rfl fun p hp ↦
      ite_eq_left ((finite_setOf_isRamifiedAt B h4).mem_toFinset.mp hp)
  rw [(finite_setOf_isRamifiedAt B h4).coe_toFinset]
  by_contra h
  exact hp (ite_eq_right h)

end QuaternionAlgebra
