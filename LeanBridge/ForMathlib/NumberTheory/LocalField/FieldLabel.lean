import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantRams
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.Discriminant.Basic

/-!
# Labels of `p`-adic fields and of families of `p`-adic extensions

The LMFDB labels of `p`-adic fields and of families of extensions of `p`-adic fields begin with
their basic data.

* A `p`-adic field `K` has the label `p.f.e.cℓm.n` (LMFDB `lf.field_label`), also written
  `p.f.e.cAi.j` (LMFDB `lf.field.label`): `p` is the residue characteristic of `K`, and `f`, `e`
  and `c` are the residue degree, the ramification index and the discriminant exponent of
  `K / ℚ_p`. The rest identifies the absolute family of `K` (`ℓ`, or `A`), the subfamily of `K` in
  it, that is the class of its residual polynomials (`m`, or `i`), and `K` within the subfamily
  (`n`, or `j`). Before 2025 the LMFDB labelled `K` by `p.n.c.num` (LMFDB `lf.field.label`), where
  `n = e f` is the degree of `K / ℚ_p`.
* A relative family `I / K` has the label `s-f.e.cℓ` and an absolute family `I / ℚ_p` the label
  `p.f.e.cℓ` (LMFDB `lf.family_label`, and `p.f.e.cA` in LMFDB `lf.field.label`), where `s` is the
  label of the base field `K`, `f`, `e` and `c` are the residue degree, ramification index and
  discriminant exponent of every extension in the family, and the letters `ℓ` tell apart the
  families with the same basic data.

The basic data `p.f.e.c` are formalised here, from Tau Ceti's `TauCeti.inertiaDegree`,
`TauCeti.ramificationIndex` and `TauCeti.discriminantExponent` for a field, and from the Herbrand
invariant `I = (r_1, …, r_w)_ε^f` for a family: `f`, `e = ε p ^ w`, and `c = f (e - 1 + e m_w)` for
the last mean `m_w` of `I`, which is the discriminant exponent of every extension in `I / K` by
LMFDB `lf.means` (`c = f (e - 1 + e m)` for the mean `m` of `L / K`, which is `m_w`); this last
agreement is not proved here.

The rest of the labels is not formalised. The indices `n`, `j` and `num` are numberings of the
database (`j` sorts the defining polynomials that the database chose, and `num` follows an
unspecified ordering), and so is the code `i`, which also depends on chosen representatives of the
classes of residual polynomials. The letters `ℓ` (or `A`) sort the families with the same basic
data by their number of wild segments, the lengths of these segments in the ramification polygon,
and their rams, in an encoding by letters that the knowls do not specify; ramification polygons are
not formalised. The label `s` of the base field of a relative family ends in the index `n`.

## Main definitions

* `IsNonarchimedeanLocalField.padicLabelPrefix` (LMFDB `lf.field_label`, `lf.field.label`): the
  prefix `p.f.e.c` of the label of a `p`-adic field.
* `IsNonarchimedeanLocalField.padicOldLabelPrefix` (LMFDB `lf.field.label`): the prefix `p.n.c` of
  the old label of a `p`-adic field.
* `IsNonarchimedeanLocalField.HerbrandInvariant.discriminantExponent` (LMFDB `lf.family_label`,
  `lf.means`): the discriminant exponent `c = f (e - 1 + e m_w)` of a family.
* `IsNonarchimedeanLocalField.HerbrandInvariant.labelBasicData` (LMFDB `lf.family_label`): the
  basic data `f.e.c` of a family.
* `IsNonarchimedeanLocalField.HerbrandInvariant.absoluteLabelPrefix` (LMFDB `lf.family_label`,
  `lf.field.label`): the prefix `p.f.e.c` of the label of an absolute family.
* `IsNonarchimedeanLocalField.HerbrandInvariant.dyadicSqrtTwo`: the Herbrand invariant `(2)_1^1`
  of `ℚ_2(√2)`.

## Main results

* `IsNonarchimedeanLocalField.ringChar_residueField_eq`: the first entry `p` of the label of a
  finite extension of `ℚ_p` is its residue characteristic.
* `IsNonarchimedeanLocalField.HerbrandInvariant.absoluteLabelPrefix_dyadicSqrtTwo`: the family of
  `ℚ_2(√2)` has the label prefix `2.1.2.3`, as in its LMFDB label `2.1.2.3a`.
-/

open ValuativeRel

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (p : ℕ) [Fact p.Prime] [TauCeti.FinitePadicExtension K p]

/-- **The prime `p` of a finite extension `K` of `ℚ_p` is its residue characteristic**, the first
entry of its LMFDB label: the valuation of `p` in `K` is the absolute ramification index of `K`,
which is not `0`, so `p` is not a unit of `𝒪[K]`. -/
lemma ringChar_residueField_eq : ringChar 𝓀[K] = p := by
  have hp : p.Prime := Fact.out
  refine (TauCeti.natCastValuation_ne_zero_iff_ringChar_eq K hp (NeZero.ne _)).mp ?_
  rw [TauCeti.natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p p hp.ne_zero,
    padicValNat_self, Nat.mul_one]
  exact (TauCeti.absoluteRamificationIndex_pos K p).ne'

private lemma isSeparable_padic : Algebra.IsSeparable ℚ_[p] K :=
  have : Algebra.IsIntegral ℚ_[p] K := Algebra.IsIntegral.of_finite ℚ_[p] K
  Algebra.IsSeparable.of_integral ℚ_[p] K

/-- The **label prefix** `p.f.e.c` of a `p`-adic field `K` (LMFDB `lf.field_label`,
`lf.field.label`): its residue characteristic `p` (`ringChar_residueField_eq`), and the residue
degree `f`, the ramification index `e` and the discriminant exponent `c` of `K / ℚ_p` (Tau Ceti's
`TauCeti.inertiaDegree`, `TauCeti.ramificationIndex` and `TauCeti.discriminantExponent`), in
decimal and separated by dots; the degree of `K / ℚ_p` is `e f`
(`TauCeti.ramificationIndex_mul_inertiaDegree`). The LMFDB label of `K` continues with the letters
of its absolute family, the code of its subfamily and an index, which are not formalised: the
index is a numbering of the database, and the letters and the code depend on encodings and choices
of representatives that the knowls do not specify. -/
noncomputable def padicLabelPrefix : String :=
  haveI : Algebra.IsSeparable ℚ_[p] K := isSeparable_padic K p
  toString p ++ "." ++ toString (TauCeti.inertiaDegree ℚ_[p] K) ++ "." ++
    toString (TauCeti.ramificationIndex ℚ_[p] K) ++ "." ++
    toString (TauCeti.discriminantExponent ℚ_[p] K)

/-- The **prefix `p.n.c` of the old label** of a `p`-adic field `K` (LMFDB `lf.field.label`), the
label `p.n.c.num` that the LMFDB used before 2025: its residue characteristic `p`, the degree `n` of
`K / ℚ_p`, and the discriminant exponent `c` of `K / ℚ_p`, in decimal and separated by dots. The
final `num` is an integer code from an ordering that the knowl does not specify, and is not
formalised. -/
noncomputable def padicOldLabelPrefix : String :=
  haveI : Algebra.IsSeparable ℚ_[p] K := isSeparable_padic K p
  toString p ++ "." ++ toString (Module.finrank ℚ_[p] K) ++ "." ++
    toString (TauCeti.discriminantExponent ℚ_[p] K)

namespace HerbrandInvariant

variable {p} (I : HerbrandInvariant p)

/-- The **discriminant exponent** `c = f (e - 1 + e m_w)` (LMFDB `lf.family_label`, `lf.means`) of
a Herbrand invariant `I = (r_1, …, r_w)_ε^f`, where `e = ε p ^ w` and `m_w` is the last mean of `I`
(`HerbrandInvariant.mean`). By LMFDB `lf.means`, whose mean `m` of an extension `L / K` is defined
by `c = f (e - 1 + e m)` and is the last mean `m_w` of `L / K`, it is the discriminant exponent of
every extension in a family `I / K`; this agreement is not proved here. It is an integer for the
invariants of extensions, and is kept in `ℚ`. -/
def discriminantExponent : ℚ :=
  I.f * (I.ε * p ^ I.w - 1 + I.ε * p ^ I.w * I.mean I.w)

/-- The **basic data** `f.e.c` (LMFDB `lf.family_label`) of a family `I / K` with Herbrand
invariant `I = (r_1, …, r_w)_ε^f`: the residue degree `f`, the ramification index `e = ε p ^ w`
and the discriminant exponent `c` (`discriminantExponent`) of its extensions, in decimal and
separated by dots. The label of a relative family is `s-f.e.cℓ`, where `s` is the label of the
base field, and that of an absolute family is `p.f.e.cℓ` (`absoluteLabelPrefix`); the letters `ℓ`,
which sort the families with the same basic data, are not formalised. -/
def labelBasicData : String :=
  toString I.f ++ "." ++ toString (I.ε * p ^ I.w) ++ "." ++ toString I.discriminantExponent

/-- The **label prefix** `p.f.e.c` of an absolute family `I / ℚ_p` (LMFDB `lf.family_label`,
`lf.field.label`): the prime `p` followed by the basic data `f.e.c` of the family
(`labelBasicData`). The label is `p.f.e.cℓ`, where the letters `ℓ`, which sort the families with
the same basic data, are not formalised. -/
def absoluteLabelPrefix : String :=
  toString p ++ "." ++ I.labelBasicData

/-- The Herbrand invariant `(2)_1^1` at `p = 2`, with the single ram `r_1 = 2`: that of the
ramified quadratic extension `ℚ_2(√2) / ℚ_2`, whose nontrivial automorphism `σ` moves the
uniformiser `√2` by `σ(√2) - √2 = -2√2`, of valuation `3`, so that its lower ramification jump is
`2`. -/
def dyadicSqrtTwo : HerbrandInvariant 2 where
  w := 1
  ram k := if k = 0 then 0 else 2
  ε := 1
  f := 1
  ram_zero := rfl
  zero_lt_ram_one _ := by
    norm_num
  monotone_ram a b hab := by
    grind
  ram_of_le k hk := by
    grind
  ε_pos := one_pos
  f_pos := one_pos
  not_dvd_ε := by
    decide

/-- **The family of `ℚ_2(√2)` has the label prefix `2.1.2.3`**, as in its LMFDB label `2.1.2.3a`:
its extensions have residue degree `1`, ramification index `2` and discriminant exponent
`1 · (2 - 1 + 2 m_1) = 3`, the mean being `m_1 = (2 - 1) · 2 / 2 = 1`; indeed `x ^ 2 - 2` is
Eisenstein of discriminant `8`. -/
lemma absoluteLabelPrefix_dyadicSqrtTwo : dyadicSqrtTwo.absoluteLabelPrefix = "2.1.2.3" := by
  have h : dyadicSqrtTwo.discriminantExponent = 3 := by
    norm_num [discriminantExponent, mean, dyadicSqrtTwo]
  rw [absoluteLabelPrefix, labelBasicData, h]
  decide

end HerbrandInvariant

end IsNonarchimedeanLocalField
