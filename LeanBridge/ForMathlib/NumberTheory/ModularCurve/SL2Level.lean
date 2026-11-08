import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen
import Mathlib.Topology.Instances.ZMod
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The `SL₂`-level divides the level, and need not equal it

The `SL₂`-level of an open subgroup `H` of `GL₂(ℤ̂)` (LMFDB `modcurve.sl2level`) is the least
`N > 0` with `Γ(N) ≤ Γ_H = H ∩ SL₂(ℤ)`. It divides every `N > 0` with `Γ(N) ≤ Γ_H`, since
`Γ(gcd(M, N)) = Γ(M) ⊔ Γ(N)` (Tau Ceti's `CongruenceSubgroup.Gamma_gcd_eq_sup`, from strong
approximation for `SL₂`), so it divides the level of `H`, for which `Γ(N) ≤ Γ_H`. It need not equal
the level: the matrices whose determinant is `1` modulo `3` form an open subgroup of level `3`
containing `SL₂(ℤ̂)`, so of `SL₂`-level `1`.

## Main definitions

* `Matrix.GeneralLinearGroup.detModThreeKer`: the open subgroup of `GL₂(ℤ̂)` of the matrices whose
  determinant is `1` modulo `3`.

## Main results

* `Matrix.GeneralLinearGroup.sl2Level_dvd` (LMFDB `modcurve.sl2level`): the `SL₂`-level of an open
  subgroup divides every `N > 0` with `Γ(N) ≤ Γ_H`.
* `Matrix.GeneralLinearGroup.sl2Level_dvd_adelicLevel` (LMFDB `modcurve.sl2level`): the `SL₂`-level
  of an open subgroup divides its level.
* `Matrix.GeneralLinearGroup.isOpen_detModThreeKer`,
  `Matrix.GeneralLinearGroup.adelicLevel_detModThreeKer`,
  `Matrix.GeneralLinearGroup.sl2Level_detModThreeKer`,
  `Matrix.GeneralLinearGroup.index_detModThreeKer`: the subgroup `detModThreeKer` is open, of level
  `3`, `SL₂`-level `1` and index `2`.
* `Matrix.GeneralLinearGroup.exists_sl2Level_ne_adelicLevel` (LMFDB `modcurve.sl2level`): the
  `SL₂`-level of an open subgroup need not equal its level.
-/

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])}

local notation "ℓ₃" => (Subtype.mk 3 Nat.prime_three : Nat.Primes)

/-- **The `SL₂`-level of an open subgroup `H` of `GL₂(ℤ̂)` divides every `N > 0` with
`Γ(N) ≤ Γ_H`** (LMFDB `modcurve.sl2level`): `Γ(gcd(s, N)) = Γ(s) ⊔ Γ(N) ≤ Γ_H` for the `SL₂`-level
`s`, which is minimal, so `gcd(s, N) = s`. -/
lemma sl2Level_dvd (hH : IsOpen (SetLike.coe H)) {N : ℕ} (hN : 0 < N)
    (hΓ : CongruenceSubgroup.Gamma N ≤ modularGamma H) : sl2Level H ∣ N := by
  have hle : CongruenceSubgroup.Gamma ((sl2Level H).gcd N) ≤ modularGamma H := by
    rw [CongruenceSubgroup.Gamma_gcd_eq_sup]
    exact sup_le (Gamma_sl2Level_le hH) hΓ
  have hs : sl2Level H ≤ (sl2Level H).gcd N := Nat.sInf_le ⟨Nat.gcd_pos_of_pos_right _ hN, hle⟩
  exact Nat.gcd_eq_left_iff_dvd.mp <| le_antisymm (Nat.gcd_le_left N (sl2Level_pos hH)) hs

/-- **The `SL₂`-level of an open subgroup of `GL₂(ℤ̂)` divides its level** (LMFDB
`modcurve.sl2level`). -/
lemma sl2Level_dvd_adelicLevel (hH : IsOpen (SetLike.coe H)) : sl2Level H ∣ adelicLevel ⊤ H :=
  sl2Level_dvd hH (adelicLevel_pos ⊤ le_top (hH.preimage continuous_subtype_val))
    (Gamma_adelicLevel_le_modularGamma hH)

/-- The subgroup of `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)` of the matrices whose determinant is `1` modulo `3`:
the kernel of `g ↦ det(g₃) mod 3`, `g₃ ∈ GL₂(ℤ₃)` being the component of `g` at `3`. It is open,
of level `3`, `SL₂`-level `1` and index `2`. -/
noncomputable def detModThreeKer : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  (det.comp ((map (PadicInt.toZModPow 1 : ℤ_[3] →+* ZMod (3 ^ 1))).comp
    (Pi.evalMonoidHom (fun ℓ : Nat.Primes ↦ GL (Fin 2) ℤ_[ℓ]) ℓ₃))).ker

lemma mem_detModThreeKer {g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]} : g ∈ detModThreeKer ↔
    PadicInt.toZModPow 1 ((g ℓ₃ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det) = 1 := by
  rw [detModThreeKer, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
    GeneralLinearGroup.map_det, Units.ext_iff, Units.coe_map, val_det_apply]
  rfl

/-- **The subgroup `detModThreeKer` of `GL₂(ℤ̂)` is open**: membership depends continuously on the
component at `3`, through the determinant and the reduction modulo `3`. -/
lemma isOpen_detModThreeKer : IsOpen (SetLike.coe detModThreeKer) := by
  have h₃ : Continuous fun g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] ↦ g ℓ₃ :=
    continuous_pi_iff.mp continuous_id _
  have h : Continuous fun g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] ↦ PadicInt.toZModPow 1
      ((g ℓ₃ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det) :=
    (PadicInt.continuous_toZModPow 1).comp (Units.continuous_val.comp h₃).matrix_det
  have hset : SetLike.coe detModThreeKer = (fun g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] ↦
      PadicInt.toZModPow 1 ((g ℓ₃ : Matrix (Fin 2) (Fin 2) ℤ_[3]).det)) ⁻¹' {1} :=
    Set.ext fun g ↦ mem_detModThreeKer
  rw [hset]
  exact (isOpen_discrete _).preimage h

lemma ker_adelicReduction_three_le_detModThreeKer :
    (adelicReduction (n := Fin 2) 3).ker ≤ detModThreeKer := fun g hg ↦ by
  have h₃ : g ℓ₃ ∈ (map (PadicInt.toZModPow (p := 3) 1)).ker :=
    ker_map_toZModPow_mono 3 Nat.prime_three.factorization_self.ge
      (congrFun hg ℓ₃)
  have h : det (map (PadicInt.toZModPow (p := 3) 1) (g ℓ₃)) = 1 := by
    rw [MonoidHom.mem_ker.mp h₃, map_one]
  rw [GeneralLinearGroup.map_det, Units.ext_iff, Units.coe_map, val_det_apply] at h
  exact mem_detModThreeKer.mpr h

lemma three_dvd_of_inf_comap_map_eq {N : ℕ} (hN : ⊤ ⊓
    (detModThreeKer.map (adelicReduction N)).comap (adelicReduction N) = detModThreeKer) :
    3 ∣ N := by
  by_contra h3
  have h0 : N.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3
  let g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] :=
    Pi.mulSingle ℓ₃ (TauCeti.diagGL ![-1, 1])
  have hg : adelicReduction N g = 1 := by
    funext ℓ
    by_cases hℓ : ℓ = ℓ₃
    · subst hℓ
      have : Subsingleton (ZMod (3 ^ N.factorization 3)) :=
        ZMod.subsingleton_iff.mpr (by rw [h0, pow_zero])
      exact Units.ext (Matrix.ext fun i j ↦ Subsingleton.elim _ _)
    · have hgℓ : g ℓ = 1 := Pi.mulSingle_eq_of_ne hℓ _
      rw [adelicReduction, MonoidHom.pi_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, hgℓ,
        map_one, Pi.one_apply]
  have hgH : g ∈ detModThreeKer := by
    rw [← hN]
    exact ⟨trivial, 1, one_mem _, by rw [map_one, hg]⟩
  have hg₃ : g ℓ₃ = TauCeti.diagGL ![-1, 1] := Pi.mulSingle_eq_same _ _
  rw [mem_detModThreeKer, hg₃, TauCeti.diagGL_coe, Matrix.det_fin_two] at hgH
  simp +decide at hgH

/-- **The subgroup `detModThreeKer` of `GL₂(ℤ̂)` has level `3`**: it is the inverse image of its
reduction modulo `3`, and not of its reduction modulo any `N` prime to `3`, which forgets the
component at `3`. -/
lemma adelicLevel_detModThreeKer : adelicLevel ⊤ detModThreeKer = 3 := by
  have h3 : 3 ∈ {N : ℕ | 0 < N ∧ ⊤ ⊓
      (detModThreeKer.map (adelicReduction N)).comap (adelicReduction N) = detModThreeKer} := by
    refine ⟨by norm_num, ?_⟩
    rw [top_inf_eq, Subgroup.comap_map_eq, sup_eq_left]
    exact ker_adelicReduction_three_le_detModThreeKer
  have hmem : adelicLevel ⊤ detModThreeKer ∈ {N : ℕ | 0 < N ∧ ⊤ ⊓
      (detModThreeKer.map (adelicReduction N)).comap (adelicReduction N) = detModThreeKer} :=
    Nat.sInf_mem ⟨3, h3⟩
  exact le_antisymm (Nat.sInf_le h3) (Nat.le_of_dvd hmem.1 (three_dvd_of_inf_comap_map_eq hmem.2))

lemma modularGamma_detModThreeKer : modularGamma detModThreeKer = ⊤ :=
  eq_top_iff.mpr fun γ _ ↦ mem_detModThreeKer.mpr <| by
    have h : det (sl2zToAdelic γ ℓ₃) = 1 :=
      congrFun (sl2zToAdelic_mem_adelicSL γ) ℓ₃
    rw [Units.ext_iff, val_det_apply] at h
    rw [h, Units.val_one, map_one]

/-- **The subgroup `detModThreeKer` of `GL₂(ℤ̂)` has `SL₂`-level `1`**: it contains `SL₂(ℤ̂)`, so
`Γ_H = SL₂(ℤ)`. -/
lemma sl2Level_detModThreeKer : sl2Level detModThreeKer = 1 :=
  le_antisymm (Nat.sInf_le ⟨one_pos, modularGamma_detModThreeKer ▸ le_top⟩)
    (sl2Level_pos isOpen_detModThreeKer)

/-- **The subgroup `detModThreeKer` of `GL₂(ℤ̂)` has index `2`**: it is the kernel of a surjection
onto `(ℤ/3ℤ)ˣ`, the determinant of `diag(-1, 1)` at `3` being `-1`. -/
lemma index_detModThreeKer : detModThreeKer.index = 2 := by
  rw [detModThreeKer, Subgroup.index_ker, MonoidHom.range_eq_top.mpr fun u ↦ ?_, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  · rfl
  rcases (by decide : ∀ u : (ZMod (3 ^ 1))ˣ, u = 1 ∨ u = -1) u with rfl | rfl
  · exact ⟨1, map_one _⟩
  refine ⟨Pi.mulSingle ℓ₃ (TauCeti.diagGL ![-1, 1]), Units.ext ?_⟩
  have hg₃ : Pi.evalMonoidHom (fun ℓ : Nat.Primes ↦ GL (Fin 2) ℤ_[ℓ]) ℓ₃
      (Pi.mulSingle ℓ₃ (TauCeti.diagGL ![-1, 1])) = TauCeti.diagGL ![-1, 1] :=
    Pi.mulSingle_eq_same (M := fun ℓ : Nat.Primes ↦ GL (Fin 2) ℤ_[ℓ]) ℓ₃ (TauCeti.diagGL ![-1, 1])
  simp [hg₃]

/-- **The `SL₂`-level of an open subgroup of `GL₂(ℤ̂)` need not equal its level** (LMFDB
`modcurve.sl2level`): `detModThreeKer` has level `3` and `SL₂`-level `1`. -/
lemma exists_sl2Level_ne_adelicLevel : ∃ H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]),
    IsOpen (SetLike.coe H) ∧ sl2Level H ≠ adelicLevel ⊤ H := by
  refine ⟨detModThreeKer, isOpen_detModThreeKer, ?_⟩
  rw [sl2Level_detModThreeKer, adelicLevel_detModThreeKer]
  decide

end Matrix.GeneralLinearGroup
