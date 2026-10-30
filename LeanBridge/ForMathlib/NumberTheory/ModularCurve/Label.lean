import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GenusOfOpenSubgroup

/-!
# Labels of modular curves

The LMFDB labels the modular curve `X_H` of an open subgroup `H ≤ GL₂(ℤ̂)` with `det(H) = ℤ̂ˣ` by
the label of `H`. When `-I ∈ H` it is `N.i.g.c.n`, where `N`, `i` and `g` are the level, the index
and the genus of `H`; when `-I ∉ H` it is `N.i.g-M.c.m.n`, where `M` is the level of
`H' = ⟨H, -I⟩` and `i = 2j` for the index `j` of `H'`, whose label is `M.j.g.c.m`.

The base-`26` ordinal `c` of the Gassmann class among the groups of the same level, index and genus,
the integer `n` distinguishing nonconjugate groups and the integer `m` of the label of `H'` follow
the LMFDB's (RSZB) orderings of subgroups, which the knowl does not specify: they are database
numberings rather than mathematical functions of `H`, and there is nothing to formalise in them.
What `c` and `n` number, the Gassmann class of `H` (`Matrix.GeneralLinearGroup.gassmannClass`) and
its conjugacy class, are mathematical, but their numbering is not. The mathematically defined part
of the label is the level, the index and the genus of `H` and, when `-I ∉ H`, the level of `H'`.
Conjugate subgroups, which define isomorphic modular curves, have the same level and index, and the
same level of `⟨H, -I⟩`.

As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product
`∏_ℓ GL₂(ℤ_ℓ)`, and a conjugate `g H g⁻¹` is the pointwise action `g • H` of `g ∈ ConjAct GL₂(ℤ̂)`.
The genus is the rational number `Matrix.GeneralLinearGroup.adelicGenus` given by the genus formula;
that it is a nonnegative integer, that it is invariant under conjugation, and that `H` and `H'` have
the same genus, as the label `M.j.g.c.m` of `H'` says, are not formalised.

## Main definitions

* `Matrix.GeneralLinearGroup.ModularCurveLabel` (LMFDB `modcurve.label`): the mathematically
  defined part of the label of a modular curve.
* `Matrix.GeneralLinearGroup.modularCurveLabel` (LMFDB `modcurve.label`): that of `X_H`.

## Main results

* `Matrix.GeneralLinearGroup.index_eq_two_mul_index_adjoinNegOne`: when `-I ∉ H`, the index of `H`
  is twice the index of `⟨H, -I⟩`.
* `Matrix.GeneralLinearGroup.adelicLevel_conj`, `Matrix.GeneralLinearGroup.index_conj` and
  `Matrix.GeneralLinearGroup.adjoinNegOneLevel_modularCurveLabel_conj`: conjugate subgroups have
  the same level, index, and level of `⟨H, -I⟩`.
-/

open scoped Pointwise

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))
  (g : ConjAct (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The mathematically defined part of the **label** (LMFDB `modcurve.label`) of the modular curve
`X_H` of an open subgroup `H ≤ GL₂(ℤ̂)` with `det(H) = ℤ̂ˣ`: the part `N.i.g` of the label
`N.i.g.c.n` when `-I ∈ H`, and the part `N.i.g-M` of the label `N.i.g-M.c.m.n` when `-I ∉ H`. The
remaining entries `c`, `m` and `n` are database numberings. -/
structure ModularCurveLabel where
  /-- The level `N` of `H`. -/
  level : ℕ
  /-- The index `i` of `H` in `GL₂(ℤ̂)`. -/
  index : ℕ
  /-- The genus `g` of `H`. -/
  genus : ℚ
  /-- The level `M` of `⟨H, -I⟩` when `-I ∉ H`, and `none` when `-I ∈ H`. -/
  adjoinNegOneLevel : Option ℕ

open scoped Classical in
/-- The mathematically defined part of the **label** (LMFDB `modcurve.label`) of the modular curve
`X_H` of a subgroup `H` of `GL₂(ℤ̂)`: its level `N` (`adelicLevel`), its index `i` in `GL₂(ℤ̂)`, its
genus `g` (`adelicGenus`) and, when `-I ∉ H`, the level `M` of `⟨H, -I⟩`. The LMFDB defines the
label for open subgroups with `det(H) = ℤ̂ˣ`, completing these entries by database numberings. -/
noncomputable def modularCurveLabel : ModularCurveLabel where
  level := adelicLevel ⊤ H
  index := H.index
  genus := adelicGenus H
  adjoinNegOneLevel := if -1 ∈ H then none else some (adelicLevel ⊤ H.adjoinNegOne)

/-- **When `-I ∉ H`, the index of `H` is twice that of `⟨H, -I⟩`**: the index `i` of the label
`N.i.g-M.c.m.n` of `H` is `2j` for the index `j` of the label `M.j.g.c.m` of `⟨H, -I⟩`. -/
lemma index_eq_two_mul_index_adjoinNegOne (hH : -1 ∉ H) : H.index = 2 * H.adjoinNegOne.index := by
  rw [← H.relIndex_mul_index H.le_adjoinNegOne, H.relIndex_adjoinNegOne_eq_two hH]

lemma comap_map_adelicReduction_conj (N : ℕ) :
    ((g • H).map (adelicReduction N)).comap (adelicReduction N) =
      g • (H.map (adelicReduction N)).comap (adelicReduction N) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def]
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ⟨_, hy, by simp only [map_mul, hxy]⟩,
    fun ⟨h, hh, hxh⟩ ↦ ⟨(ConjAct.ofConjAct g⁻¹)⁻¹ * h * ConjAct.ofConjAct g⁻¹, ?_, ?_⟩⟩
  · simpa [mul_assoc] using hh
  · simp only [map_mul, map_inv, hxh]
    group

/-- **Conjugate subgroups of `GL₂(ℤ̂)` have the same level.** -/
lemma adelicLevel_conj : adelicLevel ⊤ (g • H) = adelicLevel ⊤ H := by
  simp only [adelicLevel, top_inf_eq, comap_map_adelicReduction_conj, smul_left_cancel_iff]

/-- **Conjugate subgroups of `GL₂(ℤ̂)` have the same index.** -/
lemma index_conj : (g • H).index = H.index :=
  H.index_map_of_bijective (MulAction.bijective g)

lemma neg_one_mem_conj_iff : -1 ∈ g • H ↔ -1 ∈ H := by
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]

/-- **Conjugate subgroups of `GL₂(ℤ̂)` have the same entry `M` in their labels**: they both contain
`-I` or not, and in the latter case `⟨g H g⁻¹, -I⟩ = g ⟨H, -I⟩ g⁻¹` has the level of `⟨H, -I⟩`. -/
lemma adjoinNegOneLevel_modularCurveLabel_conj :
    (modularCurveLabel (g • H)).adjoinNegOneLevel = (modularCurveLabel H).adjoinNegOneLevel := by
  grind [modularCurveLabel, neg_one_mem_conj_iff, Subgroup.adjoinNegOne_conj, adelicLevel_conj]

end Matrix.GeneralLinearGroup
