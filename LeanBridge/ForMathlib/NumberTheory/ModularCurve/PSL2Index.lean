import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GammaZeroOneGroups
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.SL2Level

/-!
# The `PSL₂`-index and the index of an open subgroup of `GL₂(ℤ̂)`

For an open subgroup `H` of `GL₂(ℤ̂)` with surjective determinant, `det(H) = ℤ̂ˣ`, the congruence
subgroup `Γ_H = H ∩ SL₂(ℤ)` has the same index in `SL₂(ℤ)` as `H` in `GL₂(ℤ̂)`. Indeed `SL₂(ℤ)` acts
on `GL₂(ℤ̂) / H` with stabilizer `Γ_H` at the trivial coset, and transitively: an element `g` is
`s h` with `h ∈ H` of the same determinant and `s ∈ SL₂(ℤ̂)`, and `s` agrees with an element of
`SL₂(ℤ)` modulo the level of `H` (strong approximation for `SL₂`, Tau Ceti's
`Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`, glued along the primes dividing the level
by the Chinese remainder theorem), whose kernel lies in `H`. So the `PSL₂`-index of `H` (LMFDB
`modcurve.psl2index`), the index of `±Γ_H`, is the index of `H` when `-1 ∈ H` and half of it when
`-1 ∉ H`.

The hypothesis `det(H) = ℤ̂ˣ` is needed, and the LMFDB's text omits it: the matrices with
determinant `1` modulo `3` form an open subgroup of index `2` containing `-1` and `SL₂(ℤ)`, of
`PSL₂`-index `1`.

## Main results

* `Matrix.GeneralLinearGroup.exists_adelicReduction_sl2zToAdelic_eq`: `SL₂(ℤ)` is dense in
  `SL₂(ℤ̂)`: modulo each positive integer `N`, every element of `SL₂(ℤ̂)` agrees with one of
  `SL₂(ℤ)`.
* `Matrix.GeneralLinearGroup.map_adelicDet_adelicPreimage_eq_top_iff`: the inverse image in
  `GL₂(ℤ̂)` of a subgroup of `GL₂(ℤ/Nℤ)` has surjective determinant exactly when the subgroup has.
* `Matrix.GeneralLinearGroup.index_modularGamma` (LMFDB `modcurve.psl2index`): for an open subgroup
  `H` with surjective determinant, `[SL₂(ℤ) : Γ_H] = [GL₂(ℤ̂) : H]`.
* `Matrix.GeneralLinearGroup.psl2Index_eq_index` and
  `Matrix.GeneralLinearGroup.two_mul_psl2Index_eq_index` (LMFDB `modcurve.psl2index`): the
  `PSL₂`-index is the index when `-1 ∈ H`, and half the index when `-1 ∉ H`.
* `Matrix.GeneralLinearGroup.exists_psl2Index_ne_index` (LMFDB `modcurve.psl2index`): without
  `det(H) = ℤ̂ˣ`, the `PSL₂`-index of an open subgroup containing `-1` need not be its index.
-/

open MulAction

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])}

variable {s : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]} (N : ℕ)

lemma val_padicReduction_sl2zToAdelic (ℓ : Nat.Primes) (γ : SL(2, ℤ)) :
    (padicReduction ℓ N (sl2zToAdelic γ ℓ) :
      Matrix (Fin 2) (Fin 2) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) =
        SpecialLinearGroup.map (Int.castRingHom (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) γ := by
  ext i j
  simp [padicReduction, sl2zToAdelic]

lemma det_val_padicReduction (hs : s ∈ adelicSL) (ℓ : Nat.Primes) :
    (padicReduction ℓ N (s ℓ) : Matrix (Fin 2) (Fin 2) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))).det =
      1 := by
  have h : det (s ℓ) = 1 := congrFun hs ℓ
  rw [← val_det_apply, padicReduction, GeneralLinearGroup.map_det, h, map_one, Units.val_one]

lemma exists_forall_mem_map_eq (hs : s ∈ adelicSL) (S : Finset Nat.Primes) : ∃ γ : SL(2, ℤ),
    ∀ ℓ ∈ S, (SpecialLinearGroup.map (Int.castRingHom (ZMod ((ℓ : ℕ) ^ N.factorization ℓ))) γ).val =
    (padicReduction ℓ N (s ℓ)).val := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun ℓ hℓ ↦ absurd hℓ (Finset.notMem_empty ℓ)⟩
  | insert q S hq ih =>
    rcases ih with ⟨γ₀, hγ₀⟩
    have hcop : Nat.Coprime ((q : ℕ) ^ N.factorization q) (∏ ℓ ∈ S, (ℓ : ℕ) ^ N.factorization ℓ) :=
      Nat.coprime_prod_right_iff.mpr fun ℓ hℓ ↦ ((Nat.coprime_primes q.prop ℓ.prop).mpr fun h ↦
        hq (Subtype.ext h ▸ hℓ)).pow _ _
    let A : SL(2, ZMod ((q : ℕ) ^ N.factorization q)) :=
      ⟨padicReduction q N (s q), det_val_padicReduction N hs q⟩
    rcases CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq hcop
      ((SpecialLinearGroup.map (Int.castRingHom _) γ₀)⁻¹ * A) with ⟨δ, hδ, hδA⟩
    have hA : SpecialLinearGroup.map (Int.castRingHom (ZMod ((q : ℕ) ^ N.factorization q)))
        (γ₀ * δ) = A := by
      rw [map_mul, hδA, mul_inv_cancel_left]
    refine ⟨γ₀ * δ, fun ℓ hℓ ↦ ?_⟩
    rcases Finset.mem_insert.mp hℓ with rfl | hℓ
    · exact congrArg Subtype.val hA
    · have hdvd : (ℓ : ℕ) ^ N.factorization ℓ ∣ ∏ ℓ ∈ S, (ℓ : ℕ) ^ N.factorization ℓ :=
        Finset.dvd_prod_of_mem (fun ℓ : Nat.Primes ↦ (ℓ : ℕ) ^ N.factorization ℓ) hℓ
      have hδℓ : δ ∈ CongruenceSubgroup.Gamma ((ℓ : ℕ) ^ N.factorization ℓ) :=
        CongruenceSubgroup.Gamma_le_Gamma_of_dvd hdvd hδ
      rw [map_mul, CongruenceSubgroup.Gamma_mem'.mp hδℓ, mul_one, hγ₀ ℓ hℓ]

/-- **`SL₂(ℤ)` is dense in `SL₂(ℤ̂)`**: modulo each positive integer `N`, every element of
`SL₂(ℤ̂) = ∏_ℓ SL₂(ℤ_ℓ)` agrees with an element of `SL₂(ℤ)`. -/
lemma exists_adelicReduction_sl2zToAdelic_eq (hs : s ∈ adelicSL) :
    ∃ γ : SL(2, ℤ), adelicReduction N (sl2zToAdelic γ) = adelicReduction N s := by
  rcases exists_forall_mem_map_eq N hs (N.factorization.support.subtype Nat.Prime) with ⟨γ, hγ⟩
  refine ⟨γ, funext fun ℓ ↦ Units.ext ?_⟩
  by_cases hℓ : (ℓ : ℕ) ∈ N.factorization.support
  · exact (val_padicReduction_sl2zToAdelic N ℓ γ).trans (hγ ℓ (Finset.mem_subtype.mpr hℓ))
  · have : Subsingleton (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) :=
      ZMod.subsingleton_iff.mpr (by rw [Finsupp.notMem_support_iff.mp hℓ, pow_zero])
    exact Matrix.ext fun i j ↦ Subsingleton.elim _ _

variable {N} [NeZero N] in
/-- **The inverse image in `GL₂(ℤ̂)` of a subgroup of `GL₂(ℤ/Nℤ)` has surjective determinant exactly
when the subgroup has**: `det(H) = ℤ̂ˣ` for `H` the inverse image of `K` under reduction modulo `N`
if and only if `det(K) = (ℤ/Nℤ)ˣ`. Two elements of `GL₂(ℤ̂)` with the same determinant differ by an
element of `SL₂(ℤ̂)`, whose reduction modulo `N` is that of an element of `SL₂(ℤ)`; and `SL₂(ℤ)`
maps onto `SL₂(ℤ/Nℤ)`. -/
lemma map_adelicDet_adelicPreimage_eq_top_iff (K : Subgroup (GL (Fin 2) (ZMod N))) :
    (adelicPreimage N K).map adelicDet = ⊤ ↔ K.map det = ⊤ := by
  refine ⟨fun h ↦ eq_top_iff.mpr fun x _ ↦ ?_, fun h ↦ eq_top_iff.mpr fun u _ ↦ ?_⟩
  · rcases det_surjective (n := Fin 2) x with ⟨k₁, rfl⟩
    rcases adelicReductionZMod_surjective N k₁ with ⟨g₁, rfl⟩
    rcases (h ▸ Subgroup.mem_top (adelicDet g₁) : adelicDet g₁ ∈ (adelicPreimage N K).map
      adelicDet) with ⟨g, hg, hdet⟩
    have hs : g * g₁⁻¹ ∈ adelicSL := by
      rw [adelicSL, MonoidHom.mem_ker, map_mul, map_inv, hdet, mul_inv_cancel]
    rcases exists_adelicReduction_sl2zToAdelic_eq N hs with ⟨γ, hγ⟩
    have hred : adelicReductionZMod N (g * g₁⁻¹) = SpecialLinearGroup.mapGL (ZMod N) γ := by
      rw [← adelicReductionZMod_sl2zToAdelic]
      exact chineseRemainder_injective N (by
        rw [chineseRemainder_adelicReductionZMod, chineseRemainder_adelicReductionZMod, hγ])
    have hdet1 : det (adelicReductionZMod N (g * g₁⁻¹)) = 1 := by
      rw [hred, SpecialLinearGroup.det_mapGL]
    rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at hdet1
    exact ⟨adelicReductionZMod N g, hg, hdet1⟩
  · let g₁ : ∀ p : Nat.Primes, GL (Fin 2) ℤ_[p] := fun p ↦ (det_surjective (u p)).choose
    have hg₁ : adelicDet g₁ = u := funext fun p ↦ (det_surjective (u p)).choose_spec
    rcases (h ▸ Subgroup.mem_top (det (adelicReductionZMod N g₁)) :
      det (adelicReductionZMod N g₁) ∈ K.map det) with ⟨k, hk, hdk⟩
    have hs : (k * (adelicReductionZMod N g₁)⁻¹ : GL (Fin 2) (ZMod N)).val.det = 1 := by
      rw [← val_det_apply, map_mul, map_inv, hdk, mul_inv_cancel, Units.val_one]
    rcases CongruenceSubgroup.exists_mem_Gamma_map_intCast_zmod_eq (Nat.coprime_one_right N)
      ⟨_, hs⟩ with ⟨γ, -, hγ⟩
    have hγ' : SpecialLinearGroup.mapGL (ZMod N) γ = k * (adelicReductionZMod N g₁)⁻¹ :=
      Units.ext (congrArg Subtype.val hγ)
    have hmem : sl2zToAdelic γ * g₁ ∈ adelicPreimage N K := Subgroup.mem_comap.mpr <| by
      rw [map_mul, adelicReductionZMod_sl2zToAdelic, hγ', inv_mul_cancel_right]
      exact hk
    exact ⟨sl2zToAdelic γ * g₁, hmem, by
      rw [map_mul, hg₁, MonoidHom.mem_ker.mp (sl2zToAdelic_mem_adelicSL γ), one_mul]⟩

lemma ker_adelicReduction_adelicLevel_le (hH : IsOpen (SetLike.coe H)) :
    (adelicReduction (n := Fin 2) (adelicLevel ⊤ H)).ker ≤ H := fun g hg ↦ by
  rw [← inf_comap_map_adelicReduction_adelicLevel ⊤ le_top (hH.preimage continuous_subtype_val)]
  exact ⟨trivial, 1, one_mem H, by rw [map_one, MonoidHom.mem_ker.mp hg]⟩

lemma exists_inv_mul_mem (hH : IsOpen (SetLike.coe H)) (hdet : H.map adelicDet = ⊤)
    (g : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) : ∃ γ : SL(2, ℤ), (sl2zToAdelic γ)⁻¹ * g ∈ H := by
  rcases (hdet ▸ Subgroup.mem_top (adelicDet g) : adelicDet g ∈ H.map adelicDet) with
    ⟨h, hh, hdeth⟩
  have hs : g * h⁻¹ ∈ adelicSL := by
    rw [adelicSL, MonoidHom.mem_ker, map_mul, map_inv, hdeth, mul_inv_cancel]
  rcases exists_adelicReduction_sl2zToAdelic_eq (adelicLevel ⊤ H) hs with ⟨γ, hγ⟩
  have hk : (sl2zToAdelic γ)⁻¹ * (g * h⁻¹) ∈ H := ker_adelicReduction_adelicLevel_le hH <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hγ, inv_mul_cancel]
  refine ⟨γ, ?_⟩
  simpa [mul_assoc] using mul_mem hk hh

/-- **The congruence subgroup `Γ_H` has the index of `H`**, for an open subgroup `H` of `GL₂(ℤ̂)`
with surjective determinant (LMFDB `modcurve.psl2index`): `SL₂(ℤ)` acts transitively on
`GL₂(ℤ̂) / H`, with stabilizer `Γ_H` at the trivial coset. -/
lemma index_modularGamma (hH : IsOpen (SetLike.coe H)) (hdet : H.map adelicDet = ⊤) :
    (modularGamma H).index = H.index := by
  let : MulAction SL(2, ℤ) ((∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) :=
    MulAction.compHom _ sl2zToAdelic
  have hstab : MulAction.stabilizer SL(2, ℤ)
      ((1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) : (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) =
        modularGamma H := by
    ext γ
    rw [MulAction.mem_stabilizer_iff, modularGamma, Subgroup.mem_comap, MulAction.compHom_smul_def,
      Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have horbit : MulAction.orbit SL(2, ℤ)
      ((1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) : (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) =
        Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ QuotientGroup.induction_on x fun g ↦ ?_
    rcases exists_inv_mul_mem hH hdet g with ⟨γ, hγ⟩
    exact ⟨γ, (QuotientGroup.eq.mpr (by rwa [mul_one]) :
      ((sl2zToAdelic γ * 1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :
        (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) = g)⟩
  rw [← hstab, MulAction.index_stabilizer, horbit, Set.ncard_univ, Subgroup.index]

lemma neg_one_mem_modularGamma_iff :
    -1 ∈ modularGamma H ↔ (-1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ∈ H := by
  rw [modularGamma, Subgroup.mem_comap, sl2zToAdelic_neg, map_one]

/-- **The `PSL₂`-index of `H` is its index when `-1 ∈ H`** (LMFDB `modcurve.psl2index`), for an
open subgroup `H` of `GL₂(ℤ̂)` with surjective determinant. -/
lemma psl2Index_eq_index (hH : IsOpen (SetLike.coe H)) (hdet : H.map adelicDet = ⊤)
    (h : (-1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ∈ H) : psl2Index H = H.index := by
  rw [psl2Index, Subgroup.adjoinNegOne_eq_self_iff.mpr (neg_one_mem_modularGamma_iff.mpr h),
    index_modularGamma hH hdet]

/-- **The `PSL₂`-index of `H` is half its index when `-1 ∉ H`** (LMFDB `modcurve.psl2index`), for
an open subgroup `H` of `GL₂(ℤ̂)` with surjective determinant. -/
lemma two_mul_psl2Index_eq_index (hH : IsOpen (SetLike.coe H)) (hdet : H.map adelicDet = ⊤)
    (h : (-1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ∉ H) : 2 * psl2Index H = H.index := by
  rw [← index_modularGamma hH hdet, psl2Index,
    ← Subgroup.relIndex_mul_index (Subgroup.le_adjoinNegOne (modularGamma H)),
    Subgroup.relIndex_adjoinNegOne_eq_two (mt neg_one_mem_modularGamma_iff.mp h)]

lemma neg_one_mem_detModThreeKer : (-1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ∈ detModThreeKer :=
  neg_one_mem_modularGamma_iff.mp (modularGamma_detModThreeKer ▸ Subgroup.mem_top _)

lemma psl2Index_detModThreeKer : psl2Index detModThreeKer = 1 := by
  rw [psl2Index, modularGamma_detModThreeKer,
    Subgroup.adjoinNegOne_eq_self_iff.mpr (Subgroup.mem_top _), Subgroup.index_top]

/-- **The `PSL₂`-index of an open subgroup `H` of `GL₂(ℤ̂)` containing `-1` need not be its index**
when `det(H) ≠ ℤ̂ˣ`, against the text of LMFDB `modcurve.psl2index`: `detModThreeKer` is open,
contains `-1`, and has `PSL₂`-index `1` and index `2`. -/
lemma exists_psl2Index_ne_index : ∃ H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]),
    IsOpen (SetLike.coe H) ∧ (-1 : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ∈ H ∧ psl2Index H ≠
    H.index := by
  refine ⟨detModThreeKer, isOpen_detModThreeKer, neg_one_mem_detModThreeKer, ?_⟩
  rw [psl2Index_detModThreeKer, index_detModThreeKer]
  decide

end Matrix.GeneralLinearGroup
