import LeanBridge.ForMathlib.NumberTheory.LFunction.RiemannZeta
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Multiset.Sort

/-!
# The spectral label of an L-function

The LMFDB encodes the spectral parameters `μⱼ` and `νₖ` of the functional equation
`Λ(s) = N ^ (s / 2) ∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ) L(s)` of an L-function, in its analytic
normalisation, by its **spectral label** `x-y` (LMFDB `lfunction.spectral_label`), the part `x-y`
of the label `d-N-q.k-x-y-i` of the L-function (LMFDB `lfunction.label`).

* First, factors `Γ_ℝ(s + μ) Γ_ℝ(s + μ + 1)` are combined into `Γ_ℂ(s + μ)` as often as possible.
  As `re μⱼ` is `0` or `1`, this pairs `min (a, b)` parameters `μ = it` with as many parameters
  `μ + 1 = 1 + it`, where `a` and `b` are their multiplicities, into parameters `ν = it` of factors
  `Γ_ℂ`, of real part `0`. The combined factors have the same product
  (`AnalyticLFunction.SelbergData.prod_labelμ_mul_prod_labelν`).
* `x` lists the factors `Γ_ℝ(s + μ)` as `r u` with `u = re μ`, then the factors `Γ_ℂ(s + ν)` as
  `c v` with `v = 2 re ν`, each kind sorted by `u` or `v`. When the multiplicities of all the `r u`
  and `c v` are divisible by an integer `n > 1`, each term is listed with its multiplicity divided
  by `n`, followed by `e n`: `r0r0c0c0` becomes `r0c0e2`.
* `y` is `0` when all the parameters are real. Otherwise it lists their imaginary parts, in the
  order of `x` and by increasing absolute value among the parameters with the same real part: `p t`
  and `m t` stand for imaginary parts `t` and `-t` with `t > 0`, and `c t` for a pair of parameters
  with imaginary parts `t` and `-t`. The number `t` is rounded to two decimals, so that `p0.00` and
  `m0.00` stand for nonzero imaginary parts of absolute value less than `0.005`, and `p0` stands
  for an imaginary part `0`.

The knowl leaves some choices open, which are made as follows. The integer `n` of the `e n` is the
greatest common divisor of the multiplicities, as any `n > 1` dividing them all would shorten `x`.
An imaginary part is written `p0` when it is exactly `0`, where the knowl says "zero to the known
precision", which would make the label depend on the precision of the database. Ties are rounded
up, as by Mathlib's `round`, in line with the knowl's `p0.00` and `m0.00` for absolute values
smaller than `0.005` only. Among the terms of `y` for one absolute value `t`, the `c` terms come
first, then the `p` terms, then the `m` terms. The real parts are read as natural numbers, which
they are by the normalisation of the Selberg data.

## Main definitions

* `AnalyticLFunction.spectralLabelRe`: the part `x` of a spectral label, from the values `u` and
  `v`.
* `AnalyticLFunction.spectralLabelIm`: the part `y` of a spectral label, from the values `u` and
  `v` and the imaginary parts.
* `AnalyticLFunction.SelbergData.labelμ`, `AnalyticLFunction.SelbergData.labelν`: the parameters
  of the factors `Γ_ℝ` and `Γ_ℂ` after combining pairs of factors `Γ_ℝ`.
* `AnalyticLFunction.SelbergData.spectralLabel`, `AnalyticLFunction.spectralLabel` (LMFDB
  `lfunction.spectral_label`): the spectral label.

## Main results

* `AnalyticLFunction.SelbergData.prod_labelμ_mul_prod_labelν`: combining factors does not change
  the gamma factor.
* `AnalyticLFunction.spectralLabelRe_zero_zero_zero_zero`: the knowl's example, `r0r0c0c0` is
  encoded `r0c0e2`.
* `AnalyticLFunction.spectralLabel_zeta`: the spectral label of the Riemann zeta function is
  `r0-0`.
* `AnalyticLFunction.spectralLabelRe_append_spectralLabelIm_maass`: the parameters `1 ± 9.53 i` of
  two factors `Γ_ℝ`, as for an odd Maass form such as the first Maass form of level `1`, are
  encoded `r1e2-c9.53`.
-/

namespace AnalyticLFunction

variable (m us vs : Multiset ℕ)

/-- The multiset `m` with each multiplicity divided by `n`, rounding down. -/
def spectralDivCount (n : ℕ) : Multiset ℕ :=
  m.dedup.bind fun a ↦ Multiset.replicate (m.count a / n) a

/-- The greatest common divisor of the multiplicities of the elements of `us` and of `vs`, the
largest `n` that shortens the part `x` of a spectral label by `e n`. -/
def spectralExponent : ℕ :=
  Nat.gcd (us.toFinset.gcd us.count) (vs.toFinset.gcd vs.count)

/-- The terms `c a` for the elements `a` of `m` in increasing order, where `c` is `r` or `c`. -/
def spectralTerms (c : String) : String :=
  String.join (m.sort.map fun a ↦ c ++ toString a)

/-- The **part `x` of a spectral label** (LMFDB `lfunction.spectral_label`) of a functional
equation with factors `Γ_ℝ(s + μ)` with `re μ = u` for `u` in `us` and factors `Γ_ℂ(s + ν)` with
`2 re ν = v` for `v` in `vs`: the terms `r u` in increasing order followed by the terms `c v` in
increasing order, and, when the greatest common divisor `n` of all the multiplicities exceeds `1`,
the terms with their multiplicities divided by `n` followed by `e n`. -/
def spectralLabelRe : String :=
  if 1 < spectralExponent us vs then
    spectralTerms (spectralDivCount us (spectralExponent us vs)) "r" ++
      spectralTerms (spectralDivCount vs (spectralExponent us vs)) "c" ++ "e" ++
      toString (spectralExponent us vs)
  else spectralTerms us "r" ++ spectralTerms vs "c"

/-- **The knowl's example**: `r0r0c0c0` is encoded `r0c0e2`. -/
lemma spectralLabelRe_zero_zero_zero_zero : spectralLabelRe {0, 0} {0, 0} = "r0c0e2" := by
  decide +kernel

/-- A real number `t ≥ 0` rounded to two decimals and written with two decimals, as `9.53` or
`0.00`; ties are rounded up. -/
noncomputable def spectralDecimal (t : ℝ) : String :=
  toString ((round (100 * t)).toNat / 100) ++ "." ++
    (if (round (100 * t)).toNat % 100 < 10 then "0" else "") ++
    toString ((round (100 * t)).toNat % 100)

open scoped Classical in
/-- The terms of the part `y` of a spectral label for the imaginary parts `ts` of the parameters
with one real part: `p0` for each imaginary part `0`, then, for each absolute value `t > 0` in
increasing order, `c t` for each pair of imaginary parts `t` and `-t`, then `p t` for each
remaining imaginary part `t` and `m t` for each remaining imaginary part `-t`. -/
noncomputable def spectralLabelImGroup (ts : Multiset ℝ) : String :=
  String.join (List.replicate (ts.count 0) "p0") ++
    String.join ((((ts.filter (· ≠ 0)).map abs).dedup.sort).map fun t ↦
      String.join (List.replicate (min (ts.count t) (ts.count (-t))) ("c" ++ spectralDecimal t)) ++
        String.join (List.replicate (ts.count t - ts.count (-t)) ("p" ++ spectralDecimal t)) ++
        String.join (List.replicate (ts.count (-t) - ts.count t) ("m" ++ spectralDecimal t)))

open scoped Classical in
/-- The **part `y` of a spectral label** (LMFDB `lfunction.spectral_label`) of a functional
equation with factors `Γ_ℝ(s + μ)` with `(re μ, im μ)` in `rs` and factors `Γ_ℂ(s + ν)` with
`(2 re ν, im ν)` in `cs`: `0` if all the imaginary parts vanish, and otherwise the terms
`spectralLabelImGroup` of the imaginary parts of the factors `Γ_ℝ` with each real part, in
increasing order, followed by those of the factors `Γ_ℂ`. -/
noncomputable def spectralLabelIm (rs cs : Multiset (ℕ × ℝ)) : String :=
  if ∀ x ∈ rs + cs, x.2 = 0 then "0" else
    String.join ((rs.map Prod.fst).dedup.sort.map fun u ↦
      spectralLabelImGroup ((rs.filter (·.1 = u)).map Prod.snd)) ++
    String.join ((cs.map Prod.fst).dedup.sort.map fun v ↦
      spectralLabelImGroup ((cs.filter (·.1 = v)).map Prod.snd))

namespace SelbergData

variable (D : SelbergData) {s : ℂ}

open scoped Classical in
/-- The parameters `μ = it` of the factors `Γ_ℝ(s + μ)` that are combined with a factor
`Γ_ℝ(s + μ + 1)` into `Γ_ℂ(s + μ)`, each with multiplicity `min (a, b)`, where `a` and `b` are the
multiplicities of `μ` and `μ + 1` among the parameters `μⱼ`. -/
noncomputable def pairedμ : Multiset ℂ :=
  ∑ z ∈ D.μ.toFinset with z.re = 0, Multiset.replicate (min (D.μ.count z) (D.μ.count (z + 1))) z

open scoped Classical in
/-- The parameters `μ` of the factors `Γ_ℝ(s + μ)` that remain after combining the pairs of
factors `Γ_ℝ(s + μ) Γ_ℝ(s + μ + 1)` into `Γ_ℂ(s + μ)`. -/
noncomputable def labelμ : Multiset ℂ :=
  D.μ - D.pairedμ - D.pairedμ.map (· + 1)

/-- The parameters `ν` of the factors `Γ_ℂ(s + ν)` after combining the pairs of factors
`Γ_ℝ(s + μ) Γ_ℝ(s + μ + 1)` into `Γ_ℂ(s + μ)`: those of the functional equation and the combined
ones. -/
noncomputable def labelν : Multiset ℂ :=
  D.ν + D.pairedμ

open scoped Classical in
lemma count_pairedμ (w : ℂ) :
    D.pairedμ.count w = if w.re = 0 then min (D.μ.count w) (D.μ.count (w + 1)) else 0 := by
  rw [pairedμ, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq']
  by_cases hw : w ∈ D.μ <;> simp [hw]

lemma pairedμ_add_map_le : D.pairedμ + D.pairedμ.map (· + 1) ≤ D.μ := by
  classical
  rw [Multiset.le_iff_count]
  intro w
  have hmap : (D.pairedμ.map (· + 1)).count w = D.pairedμ.count (w - 1) := by
    simpa using Multiset.count_map_eq_count' (· + 1) D.pairedμ (add_left_injective 1) (w - 1)
  rw [Multiset.count_add, hmap, D.count_pairedμ, D.count_pairedμ, sub_add_cancel]
  split_ifs with h₁ h₂ h₂
  · simp [h₁] at h₂
  all_goals omega

/-- **Combining factors does not change the gamma factor**: the product of the factors
`Γ_ℝ(s + μ)` for `μ` in `labelμ` and `Γ_ℂ(s + ν)` for `ν` in `labelν` is the gamma factor
`∏ⱼ Γ_ℝ(s + μⱼ) ∏ₖ Γ_ℂ(s + νₖ)`, by `Γ_ℝ(s + μ) Γ_ℝ(s + μ + 1) = Γ_ℂ(s + μ)`. -/
lemma prod_labelμ_mul_prod_labelν :
    (D.labelμ.map fun x ↦ Complex.Gammaℝ (s + x)).prod *
      (D.labelν.map fun x ↦ Complex.Gammaℂ (s + x)).prod = D.gammaFactor s := by
  have hμ : D.μ = D.labelμ + D.pairedμ + D.pairedμ.map (· + 1) := by
    rw [labelμ, tsub_tsub, add_assoc, tsub_add_cancel_of_le D.pairedμ_add_map_le]
  have hP : (D.pairedμ.map fun x ↦ Complex.Gammaℝ (s + x)).prod *
      (D.pairedμ.map fun x ↦ Complex.Gammaℝ (s + (x + 1))).prod =
      (D.pairedμ.map fun x ↦ Complex.Gammaℂ (s + x)).prod := by
    rw [← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ ↦ ?_)
    rw [← add_assoc, Complex.Gammaℝ_mul_Gammaℝ_add_one]
  rw [gammaFactor, hμ, labelν, Multiset.map_add, Multiset.map_add, Multiset.map_map,
    Multiset.prod_add, Multiset.prod_add, Multiset.map_add, Multiset.prod_add, ← hP]
  simp only [Function.comp_def]
  ring1

/-- The **spectral label** `x-y` (LMFDB `lfunction.spectral_label`) of Selberg data: after
combining factors `Γ_ℝ(s + μ) Γ_ℝ(s + μ + 1)` into `Γ_ℂ(s + μ)` (`labelμ`, `labelν`), the part
`x` (`spectralLabelRe`) of the values `re μ` and `2 re ν` and the part `y` (`spectralLabelIm`) of
the imaginary parts. -/
noncomputable def spectralLabel : String :=
  spectralLabelRe (D.labelμ.map fun z ↦ ⌊z.re⌋₊) (D.labelν.map fun z ↦ ⌊2 * z.re⌋₊) ++ "-" ++
    spectralLabelIm (D.labelμ.map fun z ↦ (⌊z.re⌋₊, z.im))
      (D.labelν.map fun z ↦ (⌊2 * z.re⌋₊, z.im))

end SelbergData

/-- The **spectral label** `x-y` (LMFDB `lfunction.spectral_label`) of an analytic L-function, the
spectral label of its Selberg data. -/
noncomputable def spectralLabel (L : AnalyticLFunction) : String :=
  L.selbergData.spectralLabel

/-- **An example with complex parameters**: the gamma factor
`Γ_ℝ(s + 1 + 9.53 i) Γ_ℝ(s + 1 - 9.53 i)` of an odd Maass form of spectral parameter `9.53`, with
the parameters `μ = 1 ± 9.53 i`, is encoded `r1e2-c9.53`. The first Maass form of level `1` is odd,
of spectral parameter `9.5336…`, so that the knowl's rules give its L-function the same spectral
label. -/
lemma spectralLabelRe_append_spectralLabelIm_maass : spectralLabelRe {1, 1} 0 ++ "-" ++
    spectralLabelIm {(1, 953 / 100), (1, -(953 / 100))} 0 = "r1e2-c9.53" := by
  have hdec : spectralDecimal (953 / 100) = "9.53" := by
    have h : round ((100 : ℝ) * (953 / 100)) = 953 := by
      norm_num
    simp only [spectralDecimal, h]
    decide +kernel
  have hsort : ((({953 / 100, -(953 / 100)} : Multiset ℝ).filter (· ≠ 0)).map abs).dedup.sort
      (· ≤ ·) = [953 / 100] := by
    rw [Multiset.filter_eq_self.mpr (by norm_num)]
    norm_num
  have hgroup : spectralLabelImGroup {953 / 100, -(953 / 100)} = "c9.53" := by
    have hc₀ : ({953 / 100, -(953 / 100)} : Multiset ℝ).count 0 = 0 := by
      norm_num
    have hc₁ : ({953 / 100, -(953 / 100)} : Multiset ℝ).count (953 / 100) = 1 := by
      norm_num
    have hc₂ : ({953 / 100, -(953 / 100)} : Multiset ℝ).count (-(953 / 100)) = 1 := by
      norm_num
    rw [spectralLabelImGroup, hsort, hc₀]
    simp only [List.map_cons, hc₁, hc₂, hdec]
    decide +kernel
  have hIm : spectralLabelIm {(1, 953 / 100), (1, -(953 / 100))} 0 = "c9.53" := by
    rw [spectralLabelIm, ite_eq_right (by norm_num)]
    simpa [Multiset.filter_singleton] using hgroup
  rw [hIm]
  decide +kernel

/-- **The spectral label of the Riemann zeta function is `r0-0`**, as in its LMFDB label
`1-1-1.1-r0-0-0`: its only factor is `Γ_ℝ(s)`. -/
lemma spectralLabel_zeta : zeta.spectralLabel = "r0-0" := by
  have h : zeta.selbergData.pairedμ = 0 := by
    simp [SelbergData.pairedμ, zeta]
  have hx : spectralLabelRe {0} 0 = "r0" := by
    decide +kernel
  simp only [spectralLabel, SelbergData.spectralLabel, SelbergData.labelμ, SelbergData.labelν, h]
  simp [zeta, spectralLabelIm, hx]

end AnalyticLFunction
