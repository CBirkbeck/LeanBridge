import TauCeti.FieldTheory.Kummer.Extension
import TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing

/-!
# The totally ramified extensions `ℚ_p(p^{1/e})`

The field `ℚ_p(p^{1/e})` is obtained by adjoining a root of `X^e − p` to `ℚ_p`, as Tau Ceti's
worked example `TauCeti.DyadicSqrtTwo` adjoins one of `X² − 2` to `ℚ₂`. For `e ≥ 1` it carries the
structure of a nonarchimedean local field extending `ℚ_p` given by Tau Ceti's
`TauCeti.algebraicExtensionValuativeRel`. The polynomial `X^e − p` is Eisenstein at `p`, so by Tau
Ceti's results on Eisenstein extensions the extension has degree `e`, its generator `p^{1/e}` is a
uniformiser, and it is totally ramified.

## Main definitions

* `LeanBridge.PadicRadical p e`: the local field `ℚ_p(p^{1/e})`.
* `LeanBridge.PadicRadical.root`: its generator `p^{1/e}`.
* `LeanBridge.PadicRadical.integerRoot`: the same generator, in its ring of integers.

## Main results

* `LeanBridge.PadicRadical.finrank_eq`: `[ℚ_p(p^{1/e}) : ℚ_p] = e`.
* `LeanBridge.PadicRadical.irreducible_integerRoot`: `p^{1/e}` is a uniformiser of `ℚ_p(p^{1/e})`.
* `LeanBridge.PadicRadical.isTotallyRamified`: `ℚ_p(p^{1/e}) / ℚ_p` is totally ramified.
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

lemma root_ne_zero : root p e ≠ 0 :=
  ne_zero_pow (NeZero.ne e) (root_pow p e ▸ Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

lemma minpoly_root : minpoly ℚ_[p] (root p e) = X ^ e - C (p : ℚ_[p]) :=
  (AdjoinRoot.minpoly_root (Fact.out : Irreducible (X ^ e - C (p : ℚ_[p]))).ne_zero).trans
    (by rw [leadingCoeff_X_pow_sub_C (NeZero.pos e), inv_one, C_1, mul_one])

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

lemma coe_integerRoot : (integerRoot p e : PadicRadical p e) = root p e :=
  rfl

lemma isRoot_integerRoot :
    ((X ^ e - C (p : 𝒪[ℚ_[p]])).map (algebraMap 𝒪[ℚ_[p]] 𝒪[PadicRadical p e])).IsRoot
      (integerRoot p e) := by
  apply Subtype.ext
  simp [integerRoot, root_pow]

lemma isEisensteinAt : (X ^ e - C (p : 𝒪[ℚ_[p]])).IsEisensteinAt 𝓂[ℚ_[p]] :=
  isEisensteinAt_X_pow_sub_C_of_irreducible (Padic.irreducible_natCast_self p) (NeZero.pos e)

/-- **`p^{1/e}` is a uniformiser** of `ℚ_p(p^{1/e})`, as a root of the Eisenstein polynomial
`X^e − p` generating the extension. -/
lemma irreducible_integerRoot : Irreducible (integerRoot p e) :=
  irreducible_of_eisenstein_adjoin_eq_top _ (isEisensteinAt p e) _ (isRoot_integerRoot p e)
    (adjoin_root_eq_top p e)

/-- **`ℚ_p(p^{1/e})` is totally ramified** over `ℚ_p`. -/
lemma isTotallyRamified : IsTotallyRamified ℚ_[p] (PadicRadical p e) :=
  isTotallyRamified_of_eisenstein_adjoin_eq_top (isEisensteinAt p e) (isRoot_integerRoot p e)
    (adjoin_root_eq_top p e)

end PadicRadical

end LeanBridge
