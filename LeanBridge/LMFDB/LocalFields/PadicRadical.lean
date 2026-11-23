import LeanBridge.ForMathlib.NumberTheory.LocalField.PadicRadical
import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# The totally ramified extensions `ℚ_p(p^{1/e})`

This file certifies the tame test case of LeanBridge issue #63, on the ramification index `e`, the
residue degree `f` and the discriminant exponent `d` of a finite extension of `p`-adic fields:
`ℚ_p(p^{1/e})` is totally ramified over `ℚ_p`, and when `p ∤ e` it is tamely ramified with
`d = e − 1`. It is certified for every prime `p` and every `e ≥ 1`, the invariants being Tau Ceti's
`TauCeti.ramificationIndex`, `TauCeti.inertiaDegree` and `TauCeti.discriminantExponent`.

The field `ℚ_p(p^{1/e})`, `LeanBridge.PadicRadical p e`, is obtained by adjoining a root of
`X^e − p` to `ℚ_p`; `LeanBridge.ForMathlib.NumberTheory.LocalField.PadicRadical` shows that it has
degree `e` and is totally ramified (`LeanBridge.PadicRadical.isTotallyRamified`). The polynomial is
Eisenstein at `p`, so by Tau Ceti's results on Eisenstein extensions the extension has ramification
index `e` and residue degree `1`. When `p ∤ e` it is tamely ramified, and the tame case of
Dedekind's different theorem,
`TauCeti.discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_iff`, gives
`d = f (e − 1) = e − 1`. For instance `ℚ₃(√3)` has `d = 1` and `ℚ₅(∛5)` has `d = 2`.

## Main results

* `LeanBridge.PadicRadical.ramificationIndex_eq`: the ramification index is `e`.
* `LeanBridge.PadicRadical.inertiaDegree_eq_one`: the residue degree is `1`.
* `LeanBridge.PadicRadical.isTamelyRamified`: it is tamely ramified when `p ∤ e`.
* `LeanBridge.PadicRadical.discriminantExponent_eq`: its discriminant exponent is `e − 1` when
  `p ∤ e`.
* `LeanBridge.PadicRadical.discriminantExponent_three_two` and
  `LeanBridge.PadicRadical.discriminantExponent_five_three`: `ℚ₃(√3)` has discriminant exponent
  `1`, and `ℚ₅(∛5)` has discriminant exponent `2`.
-/

open Polynomial ValuativeRel TauCeti

namespace LeanBridge.PadicRadical

variable (p e : ℕ) [Fact p.Prime] [NeZero e]

/-- **`ℚ_p(p^{1/e})` has ramification index `e`** over `ℚ_p`. -/
lemma ramificationIndex_eq : ramificationIndex ℚ_[p] (PadicRadical p e) = e :=
  (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top _ (isEisensteinAt p e) _
    (isRoot_integerRoot p e) (adjoin_root_eq_top p e)).trans natDegree_X_pow_sub_C

/-- **`ℚ_p(p^{1/e})` has residue degree `1`** over `ℚ_p`. -/
lemma inertiaDegree_eq_one : inertiaDegree ℚ_[p] (PadicRadical p e) = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _ (isEisensteinAt p e) _
    (isRoot_integerRoot p e) (adjoin_root_eq_top p e)

variable {p e}

/-- **`ℚ_p(p^{1/e})` is tamely ramified** over `ℚ_p` when `p ∤ e`: its ramification index `e` is
a unit in the residue field `𝔽_p`. -/
lemma isTamelyRamified (h : ¬p ∣ e) : IsTamelyRamified ℚ_[p] (PadicRadical p e) := by
  rw [isTamelyRamified_iff_natCast_ne_zero, ramificationIndex_eq,
    ← map_natCast (IsLocalRing.residue 𝒪[ℚ_[p]]), IsLocalRing.residue_ne_zero_iff_isUnit,
    ← Int.cast_natCast]
  exact Padic.isUnit_intCast_integerRing (by exact_mod_cast h)

/-- **`ℚ_p(p^{1/e})` has discriminant exponent `e − 1`** over `ℚ_p` when `p ∤ e`, by the tame case
of Dedekind's different theorem. -/
lemma discriminantExponent_eq (h : ¬p ∣ e) :
    discriminantExponent ℚ_[p] (PadicRadical p e) = e - 1 := by
  rw [(discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_iff _ _).2
    (isTamelyRamified h), inertiaDegree_eq_one, ramificationIndex_eq, one_mul]

/-- **`ℚ₃(√3)` has discriminant exponent `1`** over `ℚ₃`. -/
lemma discriminantExponent_three_two : discriminantExponent ℚ_[3] (PadicRadical 3 2) = 1 :=
  discriminantExponent_eq (by norm_num)

local instance : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- **`ℚ₅(∛5)` has discriminant exponent `2`** over `ℚ₅`. -/
lemma discriminantExponent_five_three : discriminantExponent ℚ_[5] (PadicRadical 5 3) = 2 :=
  discriminantExponent_eq (by norm_num)

end LeanBridge.PadicRadical
