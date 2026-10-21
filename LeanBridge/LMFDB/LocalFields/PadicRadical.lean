import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.NumberTheory.LocalField.Discriminant.Basic
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing

/-!
# The totally ramified extensions `ℚ_p(p^{1/e})`

This file certifies the tame test case of LeanBridge issue #63, on the ramification index `e`, the
residue degree `f` and the discriminant exponent `d` of a finite extension of `p`-adic fields:
`ℚ_p(p^{1/e})` is totally ramified over `ℚ_p`, and when `p ∤ e` it is tamely ramified with
`d = e − 1`. It is certified for every prime `p` and every `e ≥ 1`, the invariants being Tau Ceti's
`TauCeti.ramificationIndex`, `TauCeti.inertiaDegree` and `TauCeti.discriminantExponent`.

The field `ℚ_p(p^{1/e})` is obtained by adjoining a root of `X^e − p` to `ℚ_p`, as Tau Ceti's
worked example `TauCeti.DyadicSqrtTwo` adjoins one of `X² − 2` to `ℚ₂`. The polynomial is
Eisenstein at `p`, so by Tau Ceti's results on Eisenstein extensions the extension has degree `e`,
ramification index `e` and residue degree `1`. When `p ∤ e` it is tamely ramified, and the tame
case of Dedekind's different theorem,
`TauCeti.discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_iff`, gives
`d = f (e − 1) = e − 1`. For instance `ℚ₃(√3)` has `d = 1` and `ℚ₅(∛5)` has `d = 2`.

## Main definitions

* `LeanBridge.PadicRadical p e`: the local field `ℚ_p(p^{1/e})`.
* `LeanBridge.PadicRadical.root`: its generator `p^{1/e}`.
* `LeanBridge.PadicRadical.integerRoot`: the same generator, in its ring of integers.

## Main results

* `LeanBridge.PadicRadical.finrank_eq`: `[ℚ_p(p^{1/e}) : ℚ_p] = e`.
* `LeanBridge.PadicRadical.ramificationIndex_eq`: the ramification index is `e`.
* `LeanBridge.PadicRadical.inertiaDegree_eq_one`: the residue degree is `1`.
* `LeanBridge.PadicRadical.isTotallyRamified`: `ℚ_p(p^{1/e}) / ℚ_p` is totally ramified.
* `LeanBridge.PadicRadical.isTamelyRamified`: it is tamely ramified when `p ∤ e`.
* `LeanBridge.PadicRadical.discriminantExponent_eq`: its discriminant exponent is `e − 1` when
  `p ∤ e`.
* `LeanBridge.PadicRadical.discriminantExponent_three_two` and
  `LeanBridge.PadicRadical.discriminantExponent_five_three`: `ℚ₃(√3)` has discriminant exponent
  `1`, and `ℚ₅(∛5)` has discriminant exponent `2`.
-/

open Polynomial Valuation ValuativeRel TauCeti
open scoped IntermediateField

namespace LeanBridge

variable (p e : ℕ) [Fact p.Prime]

/-- The local field `ℚ_p(p^{1/e})`, obtained by adjoining a root of `X^e − p` to `ℚ_p`. For
`e ≥ 1` it carries the structure of a nonarchimedean local field extending `ℚ_p` given by Tau
Ceti's `TauCeti.algebraicExtensionValuativeRel`. -/
def PadicRadical : Type :=
  AdjoinRoot (X ^ e - C (p : ℚ_[p]))

namespace PadicRadical

/-- The generator `p^{1/e}` of `ℚ_p(p^{1/e})`, the class of `X`. -/
noncomputable def root : PadicRadical p e :=
  AdjoinRoot.root (X ^ e - C (p : ℚ_[p]))

variable [NeZero e]

local instance : Fact (Irreducible (X ^ e - C (p : ℚ_[p]))) :=
  ⟨map_natCast (algebraMap ℤ_[p] ℚ_[p]) p ▸
    X_pow_sub_C_irreducible_of_irreducible PadicInt.irreducible_p (NeZero.ne e)⟩

noncomputable instance : Field (PadicRadical p e) :=
  inferInstanceAs (Field (AdjoinRoot (X ^ e - C (p : ℚ_[p]))))

noncomputable instance : Algebra ℚ_[p] (PadicRadical p e) :=
  inferInstanceAs (Algebra ℚ_[p] (AdjoinRoot (X ^ e - C (p : ℚ_[p]))))

private noncomputable def powerBasis : PowerBasis ℚ_[p] (PadicRadical p e) :=
  AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ e - C (p : ℚ_[p]))).ne_zero

instance : FiniteDimensional ℚ_[p] (PadicRadical p e) :=
  (powerBasis p e).finite

instance : CharZero (PadicRadical p e) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicRadical p e)).injective

noncomputable instance : ValuativeRel (PadicRadical p e) :=
  algebraicExtensionValuativeRel ℚ_[p] (PadicRadical p e)

noncomputable instance : TopologicalSpace (PadicRadical p e) :=
  algebraicExtensionNormedFieldTopology ℚ_[p] (PadicRadical p e)

instance : ValuativeExtension ℚ_[p] (PadicRadical p e) :=
  algebraicExtension_valuativeExtension ℚ_[p] (PadicRadical p e)

instance : IsNonarchimedeanLocalField (PadicRadical p e) :=
  finiteExtension_isNonarchimedeanLocalField ℚ_[p] (PadicRadical p e)

lemma root_pow : root p e ^ e = p :=
  (root_X_pow_sub_C_pow e (p : ℚ_[p])).trans (map_natCast _ p)

lemma adjoin_root_eq_top : ℚ_[p]⟮root p e⟯ = ⊤ :=
  IntermediateField.adjoin_root_eq_top _

/-- **`ℚ_p(p^{1/e})` has degree `e`** over `ℚ_p`. -/
lemma finrank_eq : Module.finrank ℚ_[p] (PadicRadical p e) = e := by
  rw [(powerBasis p e).finrank, powerBasis, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

private lemma isIntegral_root : IsIntegral 𝒪[ℚ_[p]] (root p e) :=
  ⟨X ^ e - C (p : 𝒪[ℚ_[p]]), monic_X_pow_sub_C _ (NeZero.ne e), by simp [root_pow]⟩

/-- The generator `p^{1/e}` of `ℚ_p(p^{1/e})`, as an element of its ring of integers. -/
noncomputable def integerRoot : 𝒪[PadicRadical p e] :=
  ⟨root p e, (integer.integers (valuation ℚ_[p])).isIntegral_iff_valuation_le_one _ |>.1
    (isIntegral_root p e)⟩

lemma isRoot_integerRoot : ((X ^ e - C (p : 𝒪[ℚ_[p]])).map (algebraMap 𝒪[ℚ_[p]] 𝒪[PadicRadical p
    e])).IsRoot (integerRoot p e) := by
  apply Subtype.ext
  simp [integerRoot, root_pow]

lemma isEisensteinAt : (X ^ e - C (p : 𝒪[ℚ_[p]])).IsEisensteinAt 𝓂[ℚ_[p]] :=
  isEisensteinAt_X_pow_sub_C_of_irreducible (Padic.irreducible_natCast_self p) (NeZero.pos e)

/-- **`ℚ_p(p^{1/e})` has ramification index `e`** over `ℚ_p`. -/
lemma ramificationIndex_eq : ramificationIndex ℚ_[p] (PadicRadical p e) = e :=
  (ramificationIndex_eq_natDegree_of_eisenstein_adjoin_eq_top _ (isEisensteinAt p e) _
    (isRoot_integerRoot p e) (adjoin_root_eq_top p e)).trans natDegree_X_pow_sub_C

/-- **`ℚ_p(p^{1/e})` has residue degree `1`** over `ℚ_p`. -/
lemma inertiaDegree_eq_one : inertiaDegree ℚ_[p] (PadicRadical p e) = 1 :=
  inertiaDegree_eq_one_of_eisenstein_adjoin_eq_top _ (isEisensteinAt p e) _
    (isRoot_integerRoot p e) (adjoin_root_eq_top p e)

/-- **`ℚ_p(p^{1/e})` is totally ramified** over `ℚ_p`. -/
lemma isTotallyRamified : IsTotallyRamified ℚ_[p] (PadicRadical p e) :=
  isTotallyRamified_of_eisenstein_adjoin_eq_top (isEisensteinAt p e) (isRoot_integerRoot p e)
    (adjoin_root_eq_top p e)

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

end PadicRadical

end LeanBridge
