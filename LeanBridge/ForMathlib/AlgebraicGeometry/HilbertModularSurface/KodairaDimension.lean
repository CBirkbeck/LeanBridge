import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.KrullDimension
import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
import TauCeti.AlgebraicGeometry.Modules.Differentials.Basic
import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# The Kodaira dimension of a variety

Let `X` be a scheme over a field `k` of dimension `n`, typically a smooth projective variety, such
as a Hilbert modular surface. Its canonical sheaf is `K = ⋀ⁿ Ω_{X/k}`, the canonical line bundle
when `X` is smooth of dimension `n`, and its plurigenera are the dimensions `h⁰(X, K^{⊗m})` of the
global sections of the tensor powers of `K`. The **Kodaira dimension** of `X` (LMFDB
`hmsurface.kodaira_dimension`) is the least integer `d` such that `h⁰(X, K^{⊗m}) = O(m^d)` as
`m → ∞`, that is, such that `h⁰(X, K^{⊗m}) / m^d` is bounded, and `-1` if there is no least such
integer. When the plurigenera vanish for all large `m`, every integer qualifies, and `-1` is the
LMFDB's convention for the Kodaira dimension `-∞`. Otherwise, for a smooth projective variety of
Kodaira dimension `κ`, Iitaka's theorem gives constants `0 < c ≤ C` with `h⁰(X, K^{⊗m}) ≤ C m^κ`
for all large `m`, and `c m^κ ≤ h⁰(X, K^{⊗m})` for infinitely many `m`, so `κ` is the least such
integer. This is the usual definition of the Kodaira dimension by the growth order of the
plurigenera.

The knowl instead takes the least integer `d` such that `h⁰(X, K^{⊗m}) / m^d` has a nonzero limit,
and `-1` if there is none. When that limit exists the two definitions agree
(`AlgebraicGeometry.Scheme.kodairaDimension_eq_of_tendsto`), but it need not exist: the plurigenera
of an Enriques surface alternate between `0` and `1`, and those of a bielliptic surface are `1` or
`0` according as `m` is divisible by the order `2`, `3`, `4` or `6` of `K` or not, so the knowl's
definition gives them `-1` instead of their Kodaira dimension `0`
(`AlgebraicGeometry.Scheme.kodairaDimension_eq_of_frequently_le` gives `0`).

The dimension `n` is the Krull dimension of the topological space of `X`, read as a natural number;
the cohomology is Tau Ceti's sheaf cohomology, whose degree `0` part is the space of global
sections, and the tensor product is Tau Ceti's monoidal structure on `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorPow`: the tensor powers `M^{⊗m}` of an `𝒪_X`-module.
* `AlgebraicGeometry.Scheme.canonicalSheaf`: the canonical sheaf `⋀ⁿ Ω_{X/k}`.
* `AlgebraicGeometry.Scheme.plurigenus`: the plurigenus `h⁰(X, K^{⊗m})`.
* `AlgebraicGeometry.Scheme.PlurigenusIsBigO`: `h⁰(X, K^{⊗m}) = O(m^d)`.
* `AlgebraicGeometry.Scheme.kodairaDimension` (LMFDB `hmsurface.kodaira_dimension`).

## Main results

* `AlgebraicGeometry.Scheme.kodairaDimension_eq`: the Kodaira dimension is `d` when
  `h⁰(X, K^{⊗m}) = O(m^d)` but not `O(m^{d - 1})`.
* `AlgebraicGeometry.Scheme.kodairaDimension_eq_of_frequently_le`: it is `d` when
  `h⁰(X, K^{⊗m}) = O(m^d)` and `c m^d ≤ h⁰(X, K^{⊗m})` for infinitely many `m`, for some `c > 0`.
* `AlgebraicGeometry.Scheme.kodairaDimension_eq_of_tendsto`: it is `d` when
  `h⁰(X, K^{⊗m}) / m^d` has a nonzero limit, as in the knowl.
* `AlgebraicGeometry.Scheme.kodairaDimension_eq_neg_one`: it is `-1` when the plurigenera vanish
  for all large `m`.
-/

open CategoryTheory MonoidalCategory Filter Asymptotics Topology
open TauCeti.AlgebraicGeometry.Scheme.Modules (Cohomology)

namespace AlgebraicGeometry.Scheme

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] {d d' : ℤ} {c : ℝ}

variable {X} in
/-- The **tensor powers** `M^{⊗m}` of an `𝒪_X`-module `M`, for the tensor product of
`𝒪_X`-modules, with `M^{⊗0} = 𝒪_X`. -/
noncomputable def Modules.tensorPow (M : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | m + 1 => tensorPow M m ⊗ M

/-- The **canonical sheaf** `K = ⋀ⁿ Ω_{X/k}` of a scheme `X` over `k` of dimension `n`, the top
exterior power of its sheaf of relative differentials: the canonical line bundle of `X` when `X` is
smooth of dimension `n` over `k`. The dimension is the Krull dimension of `X` as a natural number,
`0` for the empty scheme or an infinite dimension. -/
noncomputable def canonicalSheaf : X.Modules :=
  (SheafOfModules.exteriorPower X.sheaf ((topologicalKrullDim X).unbotD 0).toNat).obj
    (X.relativeDifferentials k)

/-- The `m`-th **plurigenus** `h⁰(X, K^{⊗m})` of a scheme `X` over `k`: the dimension over `k` of
the global sections of the `m`-th tensor power of its canonical sheaf `K`, `0` if it is infinite. -/
noncomputable def plurigenus (m : ℕ) : ℕ :=
  Module.finrank k (Cohomology ((X.canonicalSheaf k).tensorPow m) 0)

variable (d) in
/-- The plurigenera of `X` are **`O(m^d)`**: `h⁰(X, K^{⊗m}) / m^d` is bounded as `m → ∞`. -/
def PlurigenusIsBigO : Prop :=
  (fun m : ℕ ↦ (X.plurigenus k m : ℝ)) =O[atTop] fun m : ℕ ↦ (m : ℝ) ^ d

open scoped Classical in
/-- The **Kodaira dimension** (LMFDB `hmsurface.kodaira_dimension`) of a scheme `X` over `k`,
typically a smooth projective variety with canonical bundle `K`: the least integer `d` such that
`h⁰(X, K^{⊗m}) = O(m^d)` as `m → ∞`, and `-1` if there is no least such integer, the LMFDB's
convention for the Kodaira dimension `-∞` of the varieties whose plurigenera all vanish. This is the
usual growth-order definition. The knowl asks instead for the least `d` such that
`h⁰(X, K^{⊗m}) / m^d` has a nonzero limit; the two agree when that limit exists
(`kodairaDimension_eq_of_tendsto`), but for an Enriques or a bielliptic surface it does not, and
the knowl's definition gives `-1` instead of `0`. -/
noncomputable def kodairaDimension : ℤ :=
  if ∃ d, IsLeast {d | X.PlurigenusIsBigO k d} d then sInf {d | X.PlurigenusIsBigO k d} else -1

variable {k X}

lemma PlurigenusIsBigO.mono (h : X.PlurigenusIsBigO k d) (hd : d ≤ d') : X.PlurigenusIsBigO k d' :=
  h.trans <| .of_bound' <| (eventually_ge_atTop 1).mono fun m hm ↦ by
    simpa using zpow_le_zpow_right₀ (Nat.one_le_cast.mpr hm) hd

/-- **The Kodaira dimension is `d` when the plurigenera are `O(m^d)` but not `O(m^{d - 1})`.** -/
lemma kodairaDimension_eq (h : X.PlurigenusIsBigO k d) (h' : ¬X.PlurigenusIsBigO k (d - 1)) :
    X.kodairaDimension k = d := by
  have hd : IsLeast {d | X.PlurigenusIsBigO k d} d :=
    ⟨h, fun _ hd' ↦ not_lt.mp fun hlt ↦ h' (hd'.mono (Int.le_sub_one_of_lt hlt))⟩
  exact (ite_eq_left ⟨d, hd⟩).trans hd.csInf_eq

/-- **The Kodaira dimension is `d` when `h⁰(X, K^{⊗m}) = O(m^d)` and `c m^d ≤ h⁰(X, K^{⊗m})` for
infinitely many `m`**, for some `c > 0`. For a smooth projective variety this holds for its Kodaira
dimension `d ≥ 0` by Iitaka's theorem; for an Enriques surface, with `d = 0` and `c = 1`. -/
lemma kodairaDimension_eq_of_frequently_le (h : X.PlurigenusIsBigO k d) (hc : 0 < c)
    (h' : ∃ᶠ m : ℕ in atTop, c * (m : ℝ) ^ d ≤ X.plurigenus k m) : X.kodairaDimension k = d := by
  refine kodairaDimension_eq h fun h'' ↦ ?_
  rcases h''.bound with ⟨C, hC⟩
  rcases (h'.and_eventually (hC.and (eventually_gt_atTop ⌈C / c⌉₊))).exists with
    ⟨m, hm, hm', hm''⟩
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hm'')
  have h₁ : C < m * c := (div_lt_iff₀ hc).mp ((Nat.le_ceil _).trans_lt (Nat.cast_lt.mpr hm''))
  rw [← sub_add_cancel d 1, zpow_add_one₀ hm₀.ne'] at hm
  rw [Real.norm_natCast, norm_zpow, Real.norm_natCast] at hm'
  nlinarith [zpow_pos hm₀ (d - 1)]

/-- **The Kodaira dimension is `d` when `h⁰(X, K^{⊗m}) / m^d` has a nonzero limit**: it agrees with
the knowl's definition whenever that limit exists. -/
lemma kodairaDimension_eq_of_tendsto (hc : c ≠ 0)
    (h : Tendsto (fun m : ℕ ↦ (X.plurigenus k m : ℝ) / (m : ℝ) ^ d) atTop (𝓝 c)) :
    X.kodairaDimension k = d := by
  have hc₀ : 0 < c := (ge_of_tendsto' h fun _ ↦
    div_nonneg (Nat.cast_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _)).lt_of_ne' hc
  have hpos : ∀ᶠ m : ℕ in atTop, (0 : ℝ) < (m : ℝ) ^ d :=
    (eventually_ne_atTop 0).mono fun m hm ↦ zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) d
  exact kodairaDimension_eq_of_frequently_le (isBigO_of_div_tendsto_nhds
    (hpos.mono fun _ hm h ↦ (hm.ne' h).elim) c h) (half_pos hc₀)
    ((h.eventually (lt_mem_nhds (half_lt_self hc₀))).and hpos |>.mono fun _ hm ↦
      ((lt_div_iff₀ hm.2).mp hm.1).le).frequently

/-- **The Kodaira dimension is `-1` when the plurigenera vanish for all large `m`**, the LMFDB's
convention for the Kodaira dimension `-∞`. -/
lemma kodairaDimension_eq_neg_one (h : ∀ᶠ m in atTop, X.plurigenus k m = 0) :
    X.kodairaDimension k = -1 :=
  ite_eq_right fun ⟨d, hd⟩ ↦ (sub_one_lt d).not_ge <| hd.2 <| .of_bound 0 <| h.mono fun m hm ↦ by
    simp [hm]

end AlgebraicGeometry.Scheme
