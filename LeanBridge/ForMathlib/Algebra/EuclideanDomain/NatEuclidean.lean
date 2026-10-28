import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Order.Lattice.Nat
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Euclidean domains with a natural-number-valued Euclidean function

The LMFDB calls an integral domain `R` Euclidean if there is a function `ν : R ∖ {0} → ℕ` such that
every `a` can be divided by every `b ≠ 0` with a remainder `r` that is `0` or satisfies
`ν r < ν b`. Mathlib's `EuclideanDomain` carries a quotient and a remainder as data and allows any
well-founded relation in place of `ν`, together with the condition `¬ r (a * b) a`. This file shows
that the LMFDB notion gives a Mathlib Euclidean domain, after replacing `ν` by
`a ↦ 1 + min_{b ≠ 0} ν (a b)` on `R ∖ {0}`, and hence a principal ideal domain.

## Main definitions

* `IsNatEuclidean` (LMFDB `ring.euclidean_domain`).
* `IsNatEuclidean.toEuclideanDomain`: the Euclidean domain structure of an `IsNatEuclidean` domain.

## Main results

* `IsNatEuclidean.isPrincipalIdealRing`: an `IsNatEuclidean` domain is a principal ideal domain.
-/

variable {R : Type*} [CommRing R]

variable (R) in
/-- A commutative ring `R` is **Euclidean** (LMFDB `ring.euclidean_domain`, for an integral domain
`R`) if there is a function `ν : R → ℕ` such that for all `a` and all `b ≠ 0` there are `q` and `r`
with `a = b q + r` and `r = 0` or `ν r < ν b`. The value `ν 0` plays no role, so `ν` is a function
on `R ∖ {0}` as in the LMFDB. -/
def IsNatEuclidean : Prop :=
  ∃ ν : R → ℕ, ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ ν r < ν b)

namespace IsNatEuclidean

variable [IsDomain R] (ν : R → ℕ)

instance : Nonempty {b : R // b ≠ 0} :=
  ⟨⟨1, one_ne_zero⟩⟩

/-- The Euclidean function `a ↦ 1 + min_{b ≠ 0} ν (a b)` on `R ∖ {0}`, extended by `0` at `0`, which
satisfies `ν' a ≤ ν' (a b)` for `b ≠ 0`. -/
noncomputable def minFun (a : R) : ℕ :=
  open scoped Classical in if a = 0 then 0 else (⨅ b : {b : R // b ≠ 0}, ν (a * b)) + 1

lemma minFun_le_minFun_mul {a b : R} (hb : b ≠ 0) : minFun ν a ≤ minFun ν (a * b) := by
  by_cases ha : a = 0
  · simp [minFun, ha]
  rw [minFun, minFun, ite_eq_right ha, ite_eq_right (mul_ne_zero ha hb), add_le_add_iff_right]
  exact le_ciInf fun c ↦ (mul_assoc a b c).symm ▸ ciInf_le (OrderBot.bddBelow _)
    (⟨b * c, mul_ne_zero hb c.2⟩ : {b : R // b ≠ 0})

lemma exists_minFun_lt (hν : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ ν r < ν b))
    (a : R) {b : R} (hb : b ≠ 0) : ∃ q : R, minFun ν (a - b * q) < minFun ν b := by
  rcases Nat.sInf_mem (Set.range_nonempty fun c : {b : R // b ≠ 0} ↦ ν (b * c)) with ⟨c, hc⟩
  rcases hν a (b * c) (mul_ne_zero hb c.2) with ⟨q, r, rfl, hr⟩
  refine ⟨c * q, ?_⟩
  rw [mul_assoc, add_sub_cancel_left]
  by_cases hr₀ : r = 0
  · simp [minFun, hr₀, hb]
  rw [minFun, minFun, ite_eq_right hr₀, ite_eq_right hb, add_lt_add_iff_right]
  refine (ciInf_le (OrderBot.bddBelow _) (⟨1, one_ne_zero⟩ : {b : R // b ≠ 0})).trans_lt ?_
  rw [mul_one]
  exact (hr.resolve_left hr₀).trans_eq hc

/-- The **Euclidean domain** structure (Mathlib's `EuclideanDomain`) of an integral domain that is
Euclidean in the sense of the LMFDB (`IsNatEuclidean`), with the well-founded relation
`ν' x < ν' y` for the modified Euclidean function `ν'` (`IsNatEuclidean.minFun`). -/
@[instance_reducible]
noncomputable def toEuclideanDomain (h : IsNatEuclidean R) : EuclideanDomain R :=
  open scoped Classical in
  { ‹CommRing R›, ‹IsDomain R›.toNontrivial with
    quotient a b := if hb : b = 0 then 0 else (exists_minFun_lt h.choose h.choose_spec a hb).choose
    quotient_zero a := dite_eq_left rfl
    remainder a b := a - b * if hb : b = 0 then 0 else
      (exists_minFun_lt h.choose h.choose_spec a hb).choose
    quotient_mul_add_remainder_eq a b := add_sub_cancel _ a
    r := InvImage (· < ·) (minFun h.choose)
    r_wellFounded := InvImage.wf _ wellFounded_lt
    remainder_lt a b hb := by
      simp only [InvImage, dite_eq_right hb]
      exact (exists_minFun_lt h.choose h.choose_spec a hb).choose_spec
    mul_left_not_lt a _ hb := by
      simp only [InvImage]
      exact (minFun_le_minFun_mul h.choose hb).not_gt }

/-- **An LMFDB Euclidean domain is a principal ideal domain.** -/
lemma isPrincipalIdealRing (h : IsNatEuclidean R) : IsPrincipalIdealRing R :=
  let _ : EuclideanDomain R := h.toEuclideanDomain
  inferInstance

end IsNatEuclidean
