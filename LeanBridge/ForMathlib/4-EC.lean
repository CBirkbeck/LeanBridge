import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Elliptic curve definitions for LeanBridge (chapter 4)

Definitions from the LMFDB elliptic-curve knowls that are not (yet) in mathlib, written here in
mathlib style for the LeanBridge blueprint audit.
-/

namespace WeierstrassCurve

open IsLocalRing

section FiniteField

variable {F : Type*} [Field F] [Finite F]

/-- The trace of Frobenius `aₚ = #F + 1 − #E(F)` of an elliptic curve over a finite field `F`.
(`Nat.card` gives the true cardinality since `F` is finite.) -/
noncomputable def traceOfFrobenius (E : WeierstrassCurve F) [E.IsElliptic] : ℤ :=
  (Nat.card F : ℤ) + 1 - Nat.card E.toAffine.Point

/-- An elliptic curve over a finite field is **ordinary** if its characteristic `p` does not divide
its trace of Frobenius `aₚ`. This is the divisibility `p ∤ aₚ`, *not* `aₚ ≠ 0`: for `p ≥ 5` the two
agree, but in characteristic 2 and 3 they differ, and divisibility is the correct criterion
(see `IsSupersingular`). -/
def IsOrdinary (E : WeierstrassCurve F) [E.IsElliptic] : Prop :=
  ¬ (ringChar F : ℤ) ∣ traceOfFrobenius E

/-- An elliptic curve over a finite field is **supersingular** if its characteristic `p` divides its
trace of Frobenius `aₚ`. The criterion is `p ∣ aₚ`, **not** `aₚ = 0`: for `p ≥ 5` these coincide
(Hasse gives `|aₚ| ≤ 2√q < p`), but in characteristic 2 and 3 `|aₚ|` can reach or exceed `p`
(e.g. `aₚ = ±2` at `p = 2`), where `aₚ = 0` would misclassify. `p ∣ aₚ` is correct in all
characteristics (Silverman, *Arithmetic of Elliptic Curves*, V.3.1). -/
def IsSupersingular (E : WeierstrassCurve F) [E.IsElliptic] : Prop :=
  (ringChar F : ℤ) ∣ traceOfFrobenius E

end FiniteField

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A minimal Weierstrass curve over `K` has **additive reduction** (LMFDB `ec.additive_reduction`)
if its reduction over the residue field of `R` has a cuspidal singularity. Equivalently, both the
discriminant `Δ` and the invariant `c₄` of the reduced curve vanish: a singular Weierstrass curve
has a cusp iff `c₄ = 0` and a node iff `c₄ ≠ 0` (Silverman, *Arithmetic of Elliptic Curves*, III),
a criterion that is independent of the residue characteristic. -/
@[mk_iff]
class IsAdditiveReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop where
  additive : (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ = 0

/-- A minimal Weierstrass curve over `K` has **bad reduction** (LMFDB `ec.bad_reduction`) if its
reduction over the residue field of `R` is singular — equivalently, it does not have good
reduction. -/
def IsBadReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop :=
  ¬ IsGoodReduction R W

/-- A minimal Weierstrass curve over `K` has **multiplicative reduction** (LMFDB
`ec.multiplicative_reduction`) if its reduction over the residue field of `R` has a nodal
singularity: the discriminant `Δ` of the reduced curve vanishes but `c₄` does not. -/
@[mk_iff]
class IsMultiplicativeReduction (W : WeierstrassCurve K) [IsMinimal R W] : Prop where
  multiplicative : (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ ≠ 0

/-- A Weierstrass curve over `K` (with `R` a DVR, `K = Frac R`) has **potential good reduction**
(LMFDB `ec.potential_good_reduction`) if its `j`-invariant is integral, i.e. lies in `R`. By the
knowl / Silverman AEC VII.5.5 this is equivalent to `E` acquiring good reduction over a finite
extension. -/
def IsPotentialGoodReduction (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  ∃ r : R, algebraMap R K r = W.j

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **good ordinary reduction**
(LMFDB `ec.good_ordinary_reduction`) if it has good reduction and the reduced elliptic curve is
ordinary. (Ordinary uses `p ∤ aₚ`, the characteristic-independent criterion; see `IsOrdinary`.) -/
def IsGoodOrdinaryReduction [Finite (ResidueField R)] (W : WeierstrassCurve K) [IsMinimal R W] :
    Prop :=
  ∃ h : (W.reduction R).IsElliptic, @IsOrdinary _ _ (W.reduction R) h

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **good supersingular
reduction** (LMFDB `ec.good_supersingular_reduction`) if it has good reduction and the reduced
elliptic curve is supersingular. (Uses `p ∣ aₚ`, not `aₚ = 0` — correct in char 2 and 3; see
`IsSupersingular`.) -/
def IsGoodSupersingularReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  ∃ h : (W.reduction R).IsElliptic, @IsSupersingular _ _ (W.reduction R) h

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **split multiplicative
reduction** (LMFDB `ec.split_multiplicative_reduction`) if it has multiplicative reduction whose
reduced curve's nonsingular points form `𝔾ₘ`, i.e. number `#𝔽 − 1`. This point-count criterion is
characteristic-independent: the smooth locus of a nodal cubic is `𝔾ₘ` (split) or the non-split
torus (non-split), of order `#𝔽 ∓ 1` in every characteristic — no tangent-cone analysis is
involved, so the char 2/3 subtleties do not arise. -/
def IsSplitMultiplicativeReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  IsMultiplicativeReduction R W ∧
    Nat.card (W.reduction R).toAffine.Point = Nat.card (ResidueField R) - 1

/-- A minimal Weierstrass curve over `K` (with finite residue field) has **non-split multiplicative
reduction** (LMFDB `ec.nonsplit_multiplicative_reduction`) if it has multiplicative reduction with
`#Ẽ_ns(𝔽) = #𝔽 + 1` (the non-split torus). Like `IsSplitMultiplicativeReduction`, this point count
is characteristic-independent. -/
def IsNonsplitMultiplicativeReduction [Finite (ResidueField R)] (W : WeierstrassCurve K)
    [IsMinimal R W] : Prop :=
  IsMultiplicativeReduction R W ∧
    Nat.card (W.reduction R).toAffine.Point = Nat.card (ResidueField R) + 1

end Reduction

end WeierstrassCurve
