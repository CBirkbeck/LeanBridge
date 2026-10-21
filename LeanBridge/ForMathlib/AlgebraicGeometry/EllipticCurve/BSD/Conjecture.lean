import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.GlobalPeriod
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Regulator
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.Tamagawa
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.LFunction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.BSD.Sha
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence

/-!
# The Birch and Swinnerton-Dyer conjecture

The Birch and Swinnerton-Dyer conjecture for an elliptic curve `E` over a number field `K` relates
the order of vanishing `r` of its L-function at the central point `s = 1` and its leading
coefficient `L⁽ʳ⁾(E, 1) / r!` to the arithmetic invariants of `E`. The weak form states that `r` is
the rank of `E(K)`, and the strong form also that

`L⁽ʳ⁾(E, 1) / r! = #Ш(E / K) Ω(E / K) Reg_NT(E / K) ∏_𝔭 c_𝔭 / (|d_K| ^ (1 / 2) #E(K)_tors ^ 2)`.

The invariants are in the LMFDB's normalisation: `Ω(E / K)` is the global period
`WeierstrassCurve.globalPeriod`, which on a global minimal model is the product over the infinite
places of the real periods and of the complex periods `|∫ ω ∧ ω̄|`; `Reg_NT(E / K)` is the
Néron-Tate regulator `WeierstrassCurve.Affine.regulator`, for the canonical height relative to
`K`, which is `[K : ℚ] ^ r` times the base-change invariant regulator
`WeierstrassCurve.Affine.normalizedRegulator`; the `c_𝔭` are the Tamagawa numbers
`WeierstrassCurve.tamagawaNumber`, with product `WeierstrassCurve.tamagawaProduct`; and Ш is the
Tate–Shafarevich group `WeierstrassCurve.sha`.

As for `WeierstrassCurve.analyticRank`, the L-function of `E` is an analytic L-function whose
Dirichlet coefficients are those of `WeierstrassCurve.LFunction`; the conjecture includes the
existence of such an analytic continuation, which holds over `ℚ` by the modularity theorem. Over
`ℚ`, where `d_ℚ = 1` and the global period of a globally minimal equation is its real period, this
is the LMFDB's statement for curves over `ℚ`.

## Main definitions

* `WeierstrassCurve.analyticShaOrder` (LMFDB `ec.analytic_sha_order`, `ec.q.analytic_sha_order`):
  the analytic order of Ш.
* `WeierstrassCurve.WeakBirchSwinnertonDyer` (LMFDB `ec.bsdconjecture`): the weak form of the
  conjecture.
* `WeierstrassCurve.BirchSwinnertonDyer` (LMFDB `ec.bsdconjecture`, `ec.q.bsdconjecture`): the
  conjecture.

## Main results

* `WeierstrassCurve.birchSwinnertonDyer_iff`: the conjecture, for an analytic L-function of the
  curve.
* `WeierstrassCurve.BirchSwinnertonDyer.weakBirchSwinnertonDyer`: the strong form implies the weak
  form.
* `WeierstrassCurve.BirchSwinnertonDyer.analyticShaOrder_eq`: the conjecture predicts that the
  analytic order of Ш is the order of Ш.
* `WeierstrassCurve.exists_isGlobalMinimal_smul_rat`: every elliptic curve over `ℚ` has a globally
  minimal equation.
* `WeierstrassCurve.globalPeriod_eq_realPeriod_of_isGlobalMinimal`: over `ℚ`, the global period of
  a globally minimal equation is its real period.
* `WeierstrassCurve.birchSwinnertonDyer_iff_of_isGlobalMinimal` and
  `WeierstrassCurve.analyticShaOrder_eq_of_isGlobalMinimal`: the conjecture and the analytic order
  of Ш over `ℚ`, in the LMFDB's form for curves over `ℚ`.
-/

open NumberField

namespace WeierstrassCurve

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The **weak Birch and Swinnerton-Dyer conjecture** (LMFDB `ec.bsdconjecture`) for a Weierstrass
curve `E` over a number field `K`: its L-function `L(E / K, s)` is an analytic L-function, whose
analytic rank, its order of vanishing at `s = 1`, is the rank of the Mordell-Weil group
`E(K)`. -/
def WeakBirchSwinnertonDyer : Prop :=
  (∃ L, W.IsAnalyticLFunction L) ∧ W.analyticRank = Module.finrank ℤ W.toAffine.Point

variable [W.IsElliptic]

/-- The **analytic order of Ш** (LMFDB `ec.analytic_sha_order`, `ec.q.analytic_sha_order`) of an
elliptic curve `E` over a number field `K`: the order of the Tate–Shafarevich group predicted by the
Birch and Swinnerton-Dyer conjecture,

`Ш_an = |d_K| ^ (1 / 2) (L⁽ʳ⁾(E, 1) / r!) #E(K)_tors ^ 2 / (Reg_NT(E / K) Ω(E / K) ∏_𝔭 c_𝔭)`,

where `d_K` is the discriminant of `K`, `L⁽ʳ⁾(E, 1) / r!` is the special value
`WeierstrassCurve.specialValue` at the analytic rank `r`, `Reg_NT(E / K)` is the Néron-Tate
regulator, `Ω(E / K)` is the global period and the `c_𝔭` are the Tamagawa numbers. The special value
is real, `L(E / K, s)` having real Dirichlet coefficients, and its real part is used. -/
noncomputable def analyticShaOrder : ℝ :=
  √|(discr K : ℝ)| * W.specialValue.re * Nat.card (AddCommGroup.torsion W.toAffine.Point) ^ 2 /
    (W.toAffine.regulator * W.globalPeriod * W.tamagawaProduct)

/-- The **Birch and Swinnerton-Dyer conjecture** (LMFDB `ec.bsdconjecture`, `ec.q.bsdconjecture`)
for an elliptic curve `E` over a number field `K`: its L-function `L(E / K, s)` is an analytic
L-function, whose analytic rank `r`, its order of vanishing at `s = 1`, is the rank of the
Mordell-Weil group `E(K)`; the Tate–Shafarevich group `Ш(E / K)` is finite; and

`L⁽ʳ⁾(E, 1) / r! = #Ш(E / K) Ω(E / K) Reg_NT(E / K) ∏_𝔭 c_𝔭 / (|d_K| ^ (1 / 2) #E(K)_tors ^ 2)`,

where `Ω(E / K)` is the global period, `Reg_NT(E / K)` is the Néron-Tate regulator, the `c_𝔭` are
the Tamagawa numbers and `d_K` is the discriminant of `K`. The existence of the analytic
L-function, a theorem over `ℚ` by modularity, and the finiteness of Ш are implicit in the LMFDB's
statement. -/
def BirchSwinnertonDyer : Prop :=
  (∃ L, W.IsAnalyticLFunction L) ∧ W.analyticRank = Module.finrank ℤ W.toAffine.Point ∧
    Finite W.sha ∧ W.specialValue = ↑(Nat.card W.sha * W.globalPeriod * W.toAffine.regulator *
    W.tamagawaProduct / (√|(discr K : ℝ)| * Nat.card (AddCommGroup.torsion W.toAffine.Point) ^ 2))

variable {W} {L : AnalyticLFunction} (h : W.BirchSwinnertonDyer)

/-- The Birch and Swinnerton-Dyer conjecture, for an analytic L-function of the curve. -/
lemma birchSwinnertonDyer_iff (hL : W.IsAnalyticLFunction L) : W.BirchSwinnertonDyer ↔
    L.analyticRank = Module.finrank ℤ W.toAffine.Point ∧ Finite W.sha ∧ L.leadingCoeff = ↑(Nat.card
    W.sha * W.globalPeriod * W.toAffine.regulator * W.tamagawaProduct / (√|(discr K : ℝ)| * Nat.card
    (AddCommGroup.torsion W.toAffine.Point) ^ 2)) := by
  rw [BirchSwinnertonDyer, analyticRank_eq hL, specialValue_eq hL]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨L, hL⟩, h⟩⟩

include h in
/-- The strong form of the Birch and Swinnerton-Dyer conjecture implies the weak form. -/
lemma BirchSwinnertonDyer.weakBirchSwinnertonDyer : W.WeakBirchSwinnertonDyer :=
  ⟨h.1, h.2.1⟩

include h in
/-- The Birch and Swinnerton-Dyer conjecture predicts that the analytic order of Ш is the order of
Ш, given that the Tamagawa product does not vanish; the regulator does not, by
`WeierstrassCurve.Affine.regulator_pos`. -/
lemma BirchSwinnertonDyer.analyticShaOrder_eq (hc : W.tamagawaProduct ≠ 0) :
    W.analyticShaOrder = Nat.card W.sha := by
  have hD : √|(discr K : ℝ)| ≠ 0 :=
    Real.sqrt_ne_zero'.mpr <| abs_pos.mpr <| Int.cast_ne_zero.mpr <| discr_ne_zero K
  have hΩ : W.globalPeriod ≠ 0 :=
    W.globalPeriod_pos.ne'
  have : Finite (AddCommGroup.torsion W.toAffine.Point) :=
    Affine.finite_torsion
  have ht : (Nat.card (AddCommGroup.torsion W.toAffine.Point) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hR : W.toAffine.regulator ≠ 0 :=
    W.toAffine.regulator_pos.ne'
  rw [analyticShaOrder, h.2.2.2, Complex.ofReal_re]
  field_simp

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsGlobalMinimal (𝓞 ℚ) E)

variable (E) in
/-- Every elliptic curve over `ℚ` has a globally minimal equation over `𝓞 ℚ`, a principal ideal
domain, so that the forms of the conjecture and of the analytic order of Ш for a globally minimal
equation apply to it. -/
lemma exists_isGlobalMinimal_smul_rat : ∃ C : VariableChange ℚ, IsGlobalMinimal (𝓞 ℚ) (C • E) :=
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    .of_surjective _ Rat.ringOfIntegersEquiv.symm.surjective
  exists_isGlobalMinimal_smul (𝓞 ℚ) E

include hE in
/-- Over `ℚ`, the global period of a globally minimal equation is its real period `Ω_E` (LMFDB
`ec.q.real_period`). -/
lemma globalPeriod_eq_realPeriod_of_isGlobalMinimal : E.globalPeriod = (E⁄ℝ).realPeriod := by
  rw [E.globalPeriod_eq_prod_of_isGlobalMinimal hE, Fintype.prod_unique,
    localPeriod_of_isReal E default Rat.isReal_infinitePlace,
    RingHom.ext_rat (InfinitePlace.embedding_of_isReal _) (algebraMap ℚ ℝ)]
  rfl

include hE in
/-- The Birch and Swinnerton-Dyer conjecture over `ℚ` (LMFDB `ec.q.bsdconjecture`), for a globally
minimal equation: `L⁽ʳ⁾(E, 1) / r! = #Ш(E / ℚ) Ω_E Reg(E / ℚ) ∏_p c_p / #E(ℚ)_tors ^ 2`, where `Ω_E`
is the real period of the equation. -/
lemma birchSwinnertonDyer_iff_of_isGlobalMinimal : E.BirchSwinnertonDyer ↔ (∃ L,
    E.IsAnalyticLFunction L) ∧ E.analyticRank = Module.finrank ℤ E.toAffine.Point ∧ Finite E.sha ∧
    E.specialValue = ↑(Nat.card E.sha * (E⁄ℝ).realPeriod * E.toAffine.regulator *
    E.tamagawaProduct / Nat.card (AddCommGroup.torsion E.toAffine.Point) ^ 2) := by
  rw [BirchSwinnertonDyer, globalPeriod_eq_realPeriod_of_isGlobalMinimal hE, discr_rat]
  simp

include hE in
/-- The analytic order of Ш over `ℚ` (LMFDB `ec.q.analytic_sha_order`), for a globally minimal
equation: `Ш_an = (L⁽ʳ⁾(E, 1) / r!) #E(ℚ)_tors ^ 2 / (Reg(E / ℚ) Ω_E ∏_p c_p)`, where `Ω_E` is the
real period of the equation. -/
lemma analyticShaOrder_eq_of_isGlobalMinimal : E.analyticShaOrder = E.specialValue.re * Nat.card
    (AddCommGroup.torsion E.toAffine.Point) ^ 2 / (E.toAffine.regulator * (E⁄ℝ).realPeriod *
    E.tamagawaProduct) := by
  rw [analyticShaOrder, globalPeriod_eq_realPeriod_of_isGlobalMinimal hE, discr_rat]
  simp

end WeierstrassCurve
