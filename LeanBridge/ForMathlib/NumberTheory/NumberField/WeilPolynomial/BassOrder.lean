import LeanBridge.ForMathlib.AlgebraicGeometry.Curve.CohenMacaulayType
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder

/-!
# Bass orders and the maximum Cohen–Macaulay type of the Frobenius order

An order `R` in an étale `ℚ`-algebra `K`, a finite product of number fields, is Gorenstein if its
Cohen–Macaulay type is `1`, and Bass if all its overorders, the orders of `K` containing `R`, are
Gorenstein. The overorders of `R` are the subrings of `K` between `R` and the maximal order `𝒪_K`:
every order lies in `𝒪_K`, and a subring between two orders is an order. The LMFDB records whether
the Frobenius order `ℤ[F, V]` of an isogeny class of abelian varieties over a finite field is Bass,
and the maximum Cohen–Macaulay type of its overorders; it is Bass exactly when that maximum is `1`.

## Main definitions

* `Subalgebra.overorders` (LMFDB `av.fq.order`): the subrings of `K` between `R` and `𝒪_K`.
* `Subalgebra.IsGorenstein` (LMFDB `ag.cohen_macaulay_type`): Cohen–Macaulay type `1`.
* `Subalgebra.IsBass`: every overorder is Gorenstein.
* `Subalgebra.maxCohenMacaulayType`: the maximum Cohen–Macaulay type of the overorders.
* `Polynomial.HasBassFrobeniusOrder` (LMFDB `av.fq.bass_zfv`): the Frobenius order `ℤ[F, V]` is
  Bass.
* `Polynomial.maxCohenMacaulayType` (LMFDB `av.fq.max_cohen_macaulay_type`): the maximum
  Cohen–Macaulay type of the overorders of `ℤ[F, V]`.

## Main results

* `Subalgebra.le_integralClosure_of_fg`: an order lies in the maximal order, so every order of `K`
  containing `R` is an overorder of `R`.
* `Subalgebra.IsBass.mono`: an overorder of a Bass order is Bass.
* `Subalgebra.isBass_iff_maxCohenMacaulayType_eq_one`: an order is Bass if and only if the maximum
  Cohen–Macaulay type of its overorders is `1`, given that it has finitely many overorders, each of
  Cohen–Macaulay type at least `1`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_toSubalgebra_iff`: for an order in a
  number field, this is Tau Ceti's notion of a Gorenstein order.
* `Polynomial.hasBassFrobeniusOrder_iff_isGorenstein`: a maximal Frobenius order is Bass if and
  only if it is Gorenstein.
-/

namespace Subalgebra

variable {K : Type*} [CommRing K] (R : Subalgebra ℤ K) {S : Subalgebra ℤ K}

/-- The **overorders** (LMFDB `av.fq.order`) of an order `R` in an étale `ℚ`-algebra `K`: the
orders of `K` containing `R`. They are the subrings of `K` between `R` and the maximal order `𝒪_K`
of `K`, the integral closure of `ℤ` in `K`, which is how they are defined here: every order lies in
`𝒪_K` (`Subalgebra.le_integralClosure_of_fg`), and a subring between two orders, which are free of
full rank as abelian groups, is an order. They are finitely many, as `𝒪_K / R` is finite (not
formalised here). The definition makes sense for any subring of a commutative ring. -/
def overorders : Set (Subalgebra ℤ K) :=
  Set.Icc R (integralClosure ℤ K)

variable {R}

lemma mem_overorders_iff : S ∈ R.overorders ↔ R ≤ S ∧ S ≤ integralClosure ℤ K :=
  Iff.rfl

/-- An order lies in the maximal order: a subring of `K` that is finitely generated as an abelian
group consists of integral elements. -/
lemma le_integralClosure_of_fg (hS : (toSubmodule S).FG) : S ≤ integralClosure ℤ K :=
  fun x hx ↦ IsIntegral.of_mem_of_fg S hS x hx

lemma mem_overorders_of_fg (hRS : R ≤ S) (hS : (toSubmodule S).FG) : S ∈ R.overorders :=
  ⟨hRS, le_integralClosure_of_fg hS⟩

lemma self_mem_overorders (hO : R ≤ integralClosure ℤ K) : R ∈ R.overorders :=
  ⟨le_rfl, hO⟩

lemma overorders_subset (hRS : R ≤ S) : S.overorders ⊆ R.overorders :=
  fun _ hT ↦ ⟨hRS.trans hT.1, hT.2⟩

variable [Algebra ℚ K]

variable (R) in
/-- An order `R` in an étale `ℚ`-algebra `K` is **Gorenstein** (LMFDB `ag.cohen_macaulay_type`) if
its Cohen–Macaulay type (`Subalgebra.cohenMacaulayType`) is `1`. For an order in a number field
this is Tau Ceti's `TauCeti.GlobalNumberFields.NumberFieldOrder.IsGorenstein`, the invertibility of
the trace dual (`TauCeti.GlobalNumberFields.NumberFieldOrder.isGorenstein_toSubalgebra_iff`). The
definition makes sense for any subring of a commutative `ℚ`-algebra. -/
def IsGorenstein : Prop :=
  R.cohenMacaulayType = 1

variable (R) in
/-- An order `R` in an étale `ℚ`-algebra `K` is **Bass** if all its overorders
(`Subalgebra.overorders`) are Gorenstein (`Subalgebra.IsGorenstein`). -/
def IsBass : Prop :=
  ∀ S ∈ R.overorders, S.IsGorenstein

variable (R) in
/-- The **maximum Cohen–Macaulay type** of an order `R` in an étale `ℚ`-algebra `K`: the largest
Cohen–Macaulay type (`Subalgebra.cohenMacaulayType`) of an overorder of `R`
(`Subalgebra.overorders`). The overorders are finitely many (not formalised here), so the supremum
is a maximum; it is `0` if they are infinitely many with unbounded types, or if `R` has none. -/
noncomputable def maxCohenMacaulayType : ℕ :=
  ⨆ S : R.overorders, (S : Subalgebra ℤ K).cohenMacaulayType

lemma IsBass.isGorenstein (hR : R.IsBass) (hO : R ≤ integralClosure ℤ K) : R.IsGorenstein :=
  hR R <| self_mem_overorders hO

/-- An overorder of a Bass order is Bass. -/
lemma IsBass.mono (hR : R.IsBass) (hRS : R ≤ S) : S.IsBass :=
  fun T hT ↦ hR T <| overorders_subset hRS hT

lemma IsBass.maxCohenMacaulayType_le_one (hR : R.IsBass) : R.maxCohenMacaulayType ≤ 1 :=
  ciSup_le' fun S ↦ (hR S S.2).le

lemma cohenMacaulayType_le_maxCohenMacaulayType (hfin : R.overorders.Finite)
    (hS : S ∈ R.overorders) : S.cohenMacaulayType ≤ R.maxCohenMacaulayType :=
  have : Finite R.overorders := hfin.to_subtype
  le_ciSup (Set.finite_range fun T : R.overorders ↦ (T : Subalgebra ℤ K).cohenMacaulayType).bddAbove
    ⟨S, hS⟩

/-- An order `R` with finitely many overorders, each of Cohen–Macaulay type at least `1`, is Bass if
and only if the maximum Cohen–Macaulay type of its overorders is `1`. Both hypotheses hold for every
order in an étale `ℚ`-algebra (not formalised here; the second one is
`TauCeti.GlobalNumberFields.NumberFieldOrder.one_le_cohenMacaulayType` for orders in number
fields). -/
lemma isBass_iff_maxCohenMacaulayType_eq_one (hfin : R.overorders.Finite)
    (hO : R ≤ integralClosure ℤ K) (hpos : ∀ S ∈ R.overorders, 1 ≤ S.cohenMacaulayType) :
    R.IsBass ↔ R.maxCohenMacaulayType = 1 := by
  refine ⟨fun hR ↦ hR.maxCohenMacaulayType_le_one.antisymm ?_, fun hR S hS ↦ ?_⟩
  · exact (hpos R <| self_mem_overorders hO).trans <|
      cohenMacaulayType_le_maxCohenMacaulayType hfin <| self_mem_overorders hO
  · exact (hR ▸ cohenMacaulayType_le_maxCohenMacaulayType hfin hS).antisymm (hpos S hS)

end Subalgebra

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-- An order in a number field is Gorenstein in the sense of `Subalgebra.IsGorenstein`, of
Cohen–Macaulay type `1`, if and only if it is Gorenstein in Tau Ceti's sense, its trace dual being
invertible. -/
lemma isGorenstein_toSubalgebra_iff : O.toSubalgebra.IsGorenstein ↔ O.IsGorenstein :=
  O.cohenMacaulayType_eq_one_iff_isGorenstein

end TauCeti.GlobalNumberFields.NumberFieldOrder

namespace Polynomial

variable (q : ℕ) (h : ℤ[X])

/-- The Frobenius order `ℤ[F, V]` of a polynomial `h ∈ ℤ[x]` (`Polynomial.frobeniusOrder`) is
**Bass** (LMFDB `av.fq.bass_zfv`) if all its overorders, the subrings of the étale algebra
`K = ℚ[F]` of `h` between `ℤ[F, V]` and the maximal order `𝒪_K` (`Subalgebra.overorders`), are
Gorenstein, of Cohen–Macaulay type `1` (`Subalgebra.IsGorenstein`). The LMFDB's `h` is the Weil
polynomial of an isogeny class of abelian varieties over `𝔽_q`, whose Frobenius order is the subring
of the endomorphism ring generated by the Frobenius `F` and the Verschiebung `V`; here `h` is any
polynomial, and the notion has its meaning when `h` is a Weil `q`-polynomial. -/
def HasBassFrobeniusOrder : Prop :=
  (h.frobeniusOrder q).IsBass

/-- The **maximum Cohen–Macaulay type** (LMFDB `av.fq.max_cohen_macaulay_type`) of a polynomial
`h ∈ ℤ[x]`: the largest Cohen–Macaulay type (`Subalgebra.cohenMacaulayType`) of an overorder of its
Frobenius order `ℤ[F, V]` (`Polynomial.frobeniusOrder`), that is of a subring of the étale algebra
`K = ℚ[F]` of `h` between `ℤ[F, V]` and the maximal order `𝒪_K` (`Subalgebra.overorders`). The
LMFDB's `h` is the Weil polynomial of an isogeny class of abelian varieties over `𝔽_q`; here `h` is
any polynomial, and the notion has its meaning when `h` is a Weil `q`-polynomial. The overorders are
then finitely many (not formalised here), so the supremum is a maximum. -/
noncomputable def maxCohenMacaulayType : ℕ :=
  (h.frobeniusOrder q).maxCohenMacaulayType

variable {q h}

lemma IsWeilPolynomial.frobeniusOrder_mem_overorders (hh : h.IsWeilPolynomial q) :
    h.frobeniusOrder q ∈ (h.frobeniusOrder q).overorders :=
  Subalgebra.self_mem_overorders hh.frobeniusOrder_le_integralClosure

lemma HasBassFrobeniusOrder.isGorenstein (hb : h.HasBassFrobeniusOrder q)
    (hh : h.IsWeilPolynomial q) : (h.frobeniusOrder q).IsGorenstein :=
  hb _ hh.frobeniusOrder_mem_overorders

/-- A maximal Frobenius order `ℤ[F, V] = 𝒪_K` is Bass if and only if it is Gorenstein, as it is its
only overorder. -/
lemma hasBassFrobeniusOrder_iff_isGorenstein (hmax : h.HasMaximalFrobeniusOrder q) :
    h.HasBassFrobeniusOrder q ↔ (h.frobeniusOrder q).IsGorenstein :=
  ⟨fun hb ↦ hb _ <| Subalgebra.self_mem_overorders hmax.le, fun hg _ hS ↦
    (hS.2.trans hmax.ge |>.antisymm hS.1) ▸ hg⟩

end Polynomial
