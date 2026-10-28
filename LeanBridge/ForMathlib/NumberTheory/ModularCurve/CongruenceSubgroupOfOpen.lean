import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The congruence subgroup `Γ_H` of an open subgroup `H` of `GL₂(ℤ̂)`

As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, we model `GL₂(ℤ̂)` as the product
`∏_ℓ GL₂(ℤ_ℓ)` over the primes. The determinant of `GL₂(ℤ̂)` takes values in `ℤ̂ˣ = ∏_ℓ ℤ_ℓˣ`, its
kernel is `SL₂(ℤ̂)`, and `SL₂(ℤ)` embeds diagonally into `GL₂(ℤ̂)`. The group `Γ_H = H ∩ SL₂(ℤ)` of
an open subgroup `H` of `GL₂(ℤ̂)` is the inverse image of `H` under this embedding; it contains the
principal congruence subgroup `Γ(N)` for the level `N` of `H`, so it is a congruence subgroup.

## Main definitions

* `Matrix.GeneralLinearGroup.adelicDet`: the determinant `GL₂(ℤ̂) → ℤ̂ˣ`.
* `Matrix.GeneralLinearGroup.adelicSL`: the subgroup `SL₂(ℤ̂)` of `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.sl2zToAdelic`: the embedding `SL₂(ℤ) → GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.modularGamma` (LMFDB `modcurve.sl2level`): the congruence subgroup
  `Γ_H = H ∩ SL₂(ℤ)` of `H`.
* `Matrix.GeneralLinearGroup.psl2Index` (LMFDB `modcurve.psl2index`): the `PSL₂`-index of `H`.
* `Matrix.GeneralLinearGroup.sl2Level` (LMFDB `modcurve.sl2level`): the `SL₂`-level of `H`.

## Main results

* `Matrix.GeneralLinearGroup.modularGamma_adjoinNegOne`: `±H ∩ SL₂(ℤ) = ±(H ∩ SL₂(ℤ))`.
* `Matrix.GeneralLinearGroup.Gamma_adelicLevel_le_modularGamma`: `Γ_H` contains `Γ(N)` for the level
  `N` of an open subgroup `H`, so it is a congruence subgroup.
* `Matrix.GeneralLinearGroup.sl2Level_pos`, `Matrix.GeneralLinearGroup.Gamma_sl2Level_le` and
  `Matrix.GeneralLinearGroup.sl2Level_le_adelicLevel`: the `SL₂`-level of an open subgroup is
  positive, `Γ_H` contains `Γ(N)` for it, and it is at most the level of `H`.
-/

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- The **determinant** `GL₂(ℤ̂) → ℤ̂ˣ`, as the product `∏_ℓ GL₂(ℤ_ℓ) → ∏_ℓ ℤ_ℓˣ` of the
determinants of `GL₂(ℤ_ℓ)`. -/
noncomputable def adelicDet : (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) →* ∀ ℓ : Nat.Primes, ℤ_[ℓ]ˣ :=
  MonoidHom.pi fun ℓ ↦ det.comp (Pi.evalMonoidHom _ ℓ)

/-- The **special linear group** `SL₂(ℤ̂)`, the kernel of the determinant of `GL₂(ℤ̂)`. -/
noncomputable def adelicSL : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  adelicDet.ker

/-- The diagonal **embedding** `SL₂(ℤ) → GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)`. -/
noncomputable def sl2zToAdelic : SL(2, ℤ) →* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] :=
  MonoidHom.pi fun _ ↦ SpecialLinearGroup.mapGL _

/-- The **congruence subgroup** `Γ_H = H ∩ SL₂(ℤ)` (LMFDB `modcurve.sl2level`) of a subgroup `H` of
`GL₂(ℤ̂)`: the inverse image of `H` under the embedding `SL₂(ℤ) → GL₂(ℤ̂)`. For an open subgroup
`H` it contains `Γ(N)` for the level `N` of `H` (`Gamma_adelicLevel_le_modularGamma`). -/
noncomputable def modularGamma : Subgroup SL(2, ℤ) :=
  H.comap sl2zToAdelic

lemma sl2zToAdelic_mem_adelicSL (g : SL(2, ℤ)) : sl2zToAdelic g ∈ adelicSL :=
  funext fun _ ↦ SpecialLinearGroup.det_mapGL g

lemma sl2zToAdelic_neg (g : SL(2, ℤ)) : sl2zToAdelic (-g) = -sl2zToAdelic g :=
  funext fun _ ↦ ext fun i j ↦ by simp [sl2zToAdelic]

/-- **`±H ∩ SL₂(ℤ) = ±(H ∩ SL₂(ℤ))`.** -/
lemma modularGamma_adjoinNegOne : modularGamma H.adjoinNegOne = (modularGamma H).adjoinNegOne :=
  Subgroup.ext fun g ↦ by simp [modularGamma, sl2zToAdelic_neg]

/-- The **`PSL₂`-index** (LMFDB `modcurve.psl2index`) of a subgroup `H` of `GL₂(ℤ̂)`: the index of
`±Γ_H = ±H ∩ SL₂(ℤ)` in `SL₂(ℤ)` (`modularGamma_adjoinNegOne`), that is, the index in `PSL₂(ℤ)` of
the image of `Γ_H`. -/
noncomputable def psl2Index : ℕ :=
  (modularGamma H).adjoinNegOne.index

/-- The **`SL₂`-level** (LMFDB `modcurve.sl2level`) of a subgroup `H` of `GL₂(ℤ̂)`: the level of the
congruence subgroup `Γ_H = H ∩ SL₂(ℤ)`, the least positive integer `N` such that `Γ(N) ≤ Γ_H`. For
an open subgroup `H` it is positive (`sl2Level_pos`) and at most the level of `H`
(`sl2Level_le_adelicLevel`); it is `0` when there is no such `N`. -/
noncomputable def sl2Level : ℕ :=
  sInf {N : ℕ | 0 < N ∧ CongruenceSubgroup.Gamma N ≤ modularGamma H}

lemma adelicReduction_sl2zToAdelic_eq_one {N : ℕ} {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma N) : adelicReduction N (sl2zToAdelic g) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem', SpecialLinearGroup.ext_iff] at hg
  refine funext fun ℓ ↦ ext fun i j ↦ ?_
  have h : ((ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))).comp
      (Int.castRingHom (ZMod N))) (g i j) = (PadicInt.toZModPow (N.factorization ℓ)) (g i j) := by
    simp
  simpa [adelicReduction, padicReduction, sl2zToAdelic, ← h, Matrix.one_apply] using
    congr_arg (ZMod.castHom (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) (hg i j)

variable {H}

/-- **`Γ_H` contains `Γ(N)` for the level `N` of an open subgroup `H` of `GL₂(ℤ̂)`**, so it is a
congruence subgroup. -/
lemma Gamma_adelicLevel_le_modularGamma (hH : IsOpen (SetLike.coe H)) :
    CongruenceSubgroup.Gamma (adelicLevel ⊤ H) ≤ modularGamma H := fun g hg ↦ by
  rw [modularGamma, Subgroup.mem_comap, ← inf_comap_map_adelicReduction_adelicLevel ⊤ le_top
    (hH.preimage continuous_subtype_val)]
  exact ⟨trivial, 1, one_mem H, by rw [map_one, adelicReduction_sl2zToAdelic_eq_one hg]⟩

lemma sl2Level_mem (hH : IsOpen (SetLike.coe H)) :
    sl2Level H ∈ {N : ℕ | 0 < N ∧ CongruenceSubgroup.Gamma N ≤ modularGamma H} :=
  Nat.sInf_mem ⟨_, adelicLevel_pos ⊤ le_top (hH.preimage continuous_subtype_val),
    Gamma_adelicLevel_le_modularGamma hH⟩

/-- **The `SL₂`-level of an open subgroup of `GL₂(ℤ̂)` is positive.** -/
lemma sl2Level_pos (hH : IsOpen (SetLike.coe H)) : 0 < sl2Level H :=
  (sl2Level_mem hH).1

/-- **`Γ_H` contains `Γ(N)` for the `SL₂`-level `N` of an open subgroup `H` of `GL₂(ℤ̂)`.** -/
lemma Gamma_sl2Level_le (hH : IsOpen (SetLike.coe H)) :
    CongruenceSubgroup.Gamma (sl2Level H) ≤ modularGamma H :=
  (sl2Level_mem hH).2

/-- **The `SL₂`-level of an open subgroup of `GL₂(ℤ̂)` is at most its level.** -/
lemma sl2Level_le_adelicLevel (hH : IsOpen (SetLike.coe H)) : sl2Level H ≤ adelicLevel ⊤ H :=
  Nat.sInf_le ⟨adelicLevel_pos ⊤ le_top (hH.preimage continuous_subtype_val),
    Gamma_adelicLevel_le_modularGamma hH⟩

end Matrix.GeneralLinearGroup
