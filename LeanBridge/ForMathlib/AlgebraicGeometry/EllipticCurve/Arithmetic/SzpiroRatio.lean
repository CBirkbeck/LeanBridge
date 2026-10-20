import TauCeti.AlgebraicGeometry.EllipticCurve.Szpiro

/-!
# The modified Szpiro ratio of an elliptic curve over `ℚ`

The (modified) Szpiro ratio of LMFDB `ec.q.szpiro_ratio` is

`σₘ(E) = log max (|c₄|³, c₆²) / log N`,

where `c₄` and `c₆` are the invariants of a minimal equation of `E` and `N` is the conductor. Tau
Ceti's `WeierstrassCurve.algorithmicSzpiroRatio` is the other ratio of the knowl,
`log |Δ_min| / log N`, which the LMFDB does not record; this file adds the modified one, against
the same conductor: Tau Ceti's algorithmic conductor `WeierstrassCurve.algorithmicConductor`,
whose exponents are read off Tate's algorithm and which is the conductor by Ogg's formula, an
identification not formalised there. The invariants are those of Tau Ceti's reduced minimal model
`WeierstrassCurve.reducedMinimalModel`, the minimal model the LMFDB records; every globally minimal
equation has the same `|c₄|` and `|c₆|`. Since `1728 Δ = c₄³ - c₆²`, the modified ratio is at least
the ratio `log |Δ_min| / log N`, which is why the modified Szpiro conjecture
(`TauCeti.AlgorithmicModifiedSzpiroConjecture`) implies the original one.

## Main definitions

* `WeierstrassCurve.algorithmicModifiedSzpiroRatio`: the modified Szpiro ratio
  (LMFDB `ec.q.szpiro_ratio`).

## Main results

* `WeierstrassCurve.rpow_algorithmicModifiedSzpiroRatio`: `N ^ σₘ = max (|c₄|³, c₆²)`.
* `WeierstrassCurve.algorithmicModifiedSzpiroRatio_smul`: the ratio is invariant under a change of
  variables.
* `WeierstrassCurve.algorithmicSzpiroRatio_le_algorithmicModifiedSzpiroRatio`: the ratio
  `log |Δ_min| / log N` is at most the modified ratio.
-/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (h : 1 < Ideal.absNorm (algorithmicConductor ℤ E))

/-- The (modified) **Szpiro ratio** `σₘ(E) = log max (|c₄|³, c₆²) / log N` (LMFDB
`ec.q.szpiro_ratio`) of an elliptic curve over `ℚ`, where `c₄` and `c₆` are the invariants of the
reduced minimal model and `N` is the norm of the algorithmic conductor. The conductor of an
elliptic curve over `ℚ` exceeds `1`, as there is no elliptic curve over `ℚ` with good reduction
everywhere; that theorem is not formalised, and when `N = 1` the quotient is `0` by division by
zero. -/
noncomputable def algorithmicModifiedSzpiroRatio : ℝ :=
  Real.log (max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3) (((reducedMinimalModel E).c₆ : ℝ) ^ 2)) /
    Real.log (Ideal.absNorm (algorithmicConductor ℤ E))

private lemma c_relation_reducedMinimalModel : (1728 : ℝ) * (reducedMinimalModel E).Δ =
    ((reducedMinimalModel E).c₄ : ℝ) ^ 3 - ((reducedMinimalModel E).c₆ : ℝ) ^ 2 :=
  mod_cast (reducedMinimalModel E).c_relation

lemma max_c₄_c₆_pos :
    0 < max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3) (((reducedMinimalModel E).c₆ : ℝ) ^ 2) := by
  have hΔ : ((reducedMinimalModel E).Δ : ℝ) ≠ 0 := mod_cast (reducedMinimalModel E).isUnit_Δ.ne_zero
  by_contra! hmax
  rcases max_le_iff.mp hmax with ⟨h₄, h₆⟩
  have h₄' : ((reducedMinimalModel E).c₄ : ℝ) ^ 3 = 0 := by
    rw [← abs_eq_zero, abs_pow]
    exact le_antisymm h₄ (by positivity)
  have h₆' : ((reducedMinimalModel E).c₆ : ℝ) ^ 2 = 0 := le_antisymm h₆ (sq_nonneg _)
  exact hΔ (by linarith [E.c_relation_reducedMinimalModel])

include h in
/-- **The modified Szpiro ratio is the exponent of `N` giving `max (|c₄|³, c₆²)`**:
`N ^ σₘ = max (|c₄|³, c₆²)`, when `N > 1`. -/
lemma rpow_algorithmicModifiedSzpiroRatio : (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^
    E.algorithmicModifiedSzpiroRatio = max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3)
    (((reducedMinimalModel E).c₆ : ℝ) ^ 2) := by
  have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) := mod_cast h
  rw [algorithmicModifiedSzpiroRatio, Real.rpow_def_of_pos (by linarith),
    mul_div_cancel₀ _ (Real.log_pos hN).ne', Real.exp_log E.max_c₄_c₆_pos]

/-- **The modified Szpiro ratio is invariant under a change of variables**, so it is an invariant
of the curve and not of the equation presenting it. -/
@[simp]
lemma algorithmicModifiedSzpiroRatio_smul (C : VariableChange ℚ) :
    (C • E).algorithmicModifiedSzpiroRatio = E.algorithmicModifiedSzpiroRatio := by
  simp only [algorithmicModifiedSzpiroRatio, VariableChange.reducedMinimalModel_smul,
    algorithmicConductor_smul]

/-- **The Szpiro ratio is at most the modified Szpiro ratio**: `log |Δ_min| / log N ≤ σₘ`, since
`1728 Δ = c₄³ - c₆²` on the reduced minimal model gives `|Δ_min| ≤ max (|c₄|³, c₆²)`. -/
lemma algorithmicSzpiroRatio_le_algorithmicModifiedSzpiroRatio :
    E.algorithmicSzpiroRatio h ≤ E.algorithmicModifiedSzpiroRatio := by
  have hΔ :
      (Ideal.absNorm (minimalDiscriminantIdeal ℤ E) : ℝ) = |((reducedMinimalModel E).Δ : ℝ)| :=
    mod_cast E.absNorm_minimalDiscriminantIdeal
  have habs : |((reducedMinimalModel E).c₄ : ℝ) ^ 3 - ((reducedMinimalModel E).c₆ : ℝ) ^ 2| ≤
      |((reducedMinimalModel E).c₄ : ℝ) ^ 3| + |((reducedMinimalModel E).c₆ : ℝ) ^ 2| :=
    abs_sub _ _
  rw [← c_relation_reducedMinimalModel, abs_mul, abs_pow, abs_sq] at habs
  rw [algorithmicSzpiroRatio_le_iff, E.rpow_algorithmicModifiedSzpiroRatio h, hΔ]
  norm_num at habs
  linarith [le_max_left (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3)
    (((reducedMinimalModel E).c₆ : ℝ) ^ 2), le_max_right (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3)
    (((reducedMinimalModel E).c₆ : ℝ) ^ 2)]

end WeierstrassCurve
