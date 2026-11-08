import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularPattern

/-!
# The minimal level of a congruence subgroup of `Sp(2g, ℚ)`

A subgroup `Γ` of `Sp(2g, ℚ)` is a congruence subgroup of level `N` if it contains the principal
congruence subgroup `Γ(N)` (`SymplecticGroup.IsCongruenceOfLevel`, LMFDB `mf.siegel.level`). The
level is not unique, as a congruence subgroup of level `N` has every multiple of `N` as a level,
and the LMFDB indexes families of congruence subgroups by their **minimal level**, the least
positive level (LMFDB `mf.siegel.level`).

The principal congruence subgroups `Γ(N)` and the Siegel congruence subgroups `Γ₀(N)` of every
degree `g ≥ 1`, and the paramodular groups `K(N)` of degree `2`, have minimal level `N`, as the
LMFDB's indexing presumes. Each contains `Γ(N)`. Conversely, the unipotent element
`(1, M e; 0, 1)` or `(1, 0; M e, 1)` of `Γ(M)`, for a diagonal matrix unit `e`, has an entry `M`
at a place where the entries of the elements of the group lie in `Nℤ`, so `Γ(M)` is contained in
the group only if `N ∣ M`.

## Main definitions

* `SymplecticGroup.minimalLevel` (LMFDB `mf.siegel.level`): the minimal level of a subgroup of
  `Sp(2g, ℚ)`.
* `SymplecticGroup.lowerUnipotentSingle`, `SymplecticGroup.upperUnipotentSingle`: the unipotent
  elements `(1, 0; M e, 1)` and `(1, M e; 0, 1)` of `Γ(M)`.

## Main results

* `SymplecticGroup.isCongruenceOfLevel_minimalLevel`: a congruence subgroup is a congruence
  subgroup of its minimal level.
* `SymplecticGroup.minimalLevel_le`: the minimal level is at most every positive level.
* `SymplecticGroup.minimalLevel_Gamma`: `Γ(N)` has minimal level `N`.
* `SymplecticGroup.minimalLevel_Gamma0`: `Γ₀(N)` has minimal level `N`.
* `SiegelUpperHalfSpace.minimalLevel_paramodularLevel`: `K(N)` has minimal level `N`.
-/

open Matrix SymplecticGroup

namespace SymplecticGroup

lemma map_single_natCast_self {l : Type*} [DecidableEq l] (M : ℕ) (i : l) :
    (single i i (M : ℤ)).map (Int.cast : ℤ → ZMod M) = 0 := by
  ext a b
  rw [map_apply, single_apply, Matrix.zero_apply]
  split_ifs <;> simp

variable {l : Type*} [DecidableEq l] [Fintype l] {N M : ℕ} {Γ : Subgroup (symplecticGroup l ℚ)}

variable (Γ) in
/-- The **minimal level** of a subgroup `Γ` of `Sp(2g, ℚ)` (LMFDB `mf.siegel.level`): the least
positive integer `N` such that `Γ` is a congruence subgroup of level `N`, that is, contains the
principal congruence subgroup `Γ(N)`. It is `0` when there is no such `N`, that is, when `Γ` is not
a congruence subgroup. -/
noncomputable def minimalLevel : ℕ :=
  sInf {N | 0 < N ∧ IsCongruenceOfLevel N Γ}

/-- **A congruence subgroup is a congruence subgroup of its minimal level.** -/
lemma isCongruenceOfLevel_minimalLevel (h : {N | 0 < N ∧ IsCongruenceOfLevel N Γ}.Nonempty) :
    IsCongruenceOfLevel (minimalLevel Γ) Γ :=
  (Nat.sInf_mem h).2

lemma minimalLevel_pos (h : {N | 0 < N ∧ IsCongruenceOfLevel N Γ}.Nonempty) :
    0 < minimalLevel Γ :=
  (Nat.sInf_mem h).1

/-- **The minimal level is at most every positive level.** -/
lemma minimalLevel_le (hN : 0 < N) (h : IsCongruenceOfLevel N Γ) : minimalLevel Γ ≤ N :=
  Nat.sInf_le ⟨hN, h⟩

lemma minimalLevel_eq (hN : 0 < N) (h : IsCongruenceOfLevel N Γ)
    (hmin : ∀ M, IsCongruenceOfLevel M Γ → N ∣ M) : minimalLevel Γ = N :=
  le_antisymm (minimalLevel_le hN h) <| Nat.le_of_dvd (minimalLevel_pos ⟨N, hN, h⟩) <|
    hmin _ (isCongruenceOfLevel_minimalLevel ⟨N, hN, h⟩)

lemma map_intCastRingHom_injective :
    Function.Injective (map (l := l) (Int.castRingHom ℚ)) := fun _ _ h ↦
  Subtype.ext <| Matrix.map_injective Int.cast_injective <| congrArg Subtype.val h

variable (M) in
/-- The unipotent element `(1, 0; M e, 1)` of `Sp(2g, ℤ)`, `e` the diagonal matrix unit at `i`. -/
def lowerUnipotentSingle (i : l) : symplecticGroup l ℤ :=
  ⟨fromBlocks 1 0 (single i i (M : ℤ)) 1, fromBlocks_lower_mem (transpose_single i i _)⟩

variable (M) in
/-- The unipotent element `(1, M e; 0, 1)` of `Sp(2g, ℤ)`, `e` the diagonal matrix unit at `i`. -/
def upperUnipotentSingle (i : l) : symplecticGroup l ℤ :=
  symTranslation (single i i (M : ℤ)) (transpose_single i i _)

lemma lowerUnipotentSingle_mem_Gamma (i : l) : lowerUnipotentSingle M i ∈ Gamma l M := by
  rw [mem_Gamma_iff]
  simp [lowerUnipotentSingle, fromBlocks_map, map_single_natCast_self]

lemma upperUnipotentSingle_mem_Gamma (i : l) : upperUnipotentSingle M i ∈ Gamma l M := by
  rw [mem_Gamma_iff]
  simp [upperUnipotentSingle, coe_symTranslation, fromBlocks_map, map_single_natCast_self]

lemma mem_of_isCongruenceOfLevel {Δ : Subgroup (symplecticGroup l ℤ)} {A : symplecticGroup l ℤ}
    (h : IsCongruenceOfLevel M (Δ.map (map (Int.castRingHom ℚ)))) (hA : A ∈ Gamma l M) : A ∈ Δ :=
  (Subgroup.mem_map_iff_mem map_intCastRingHom_injective).mp <| h <| Subgroup.mem_map_of_mem _ hA

/-- **The principal congruence subgroup `Γ(N)` has minimal level `N`** (LMFDB `mf.siegel.level`),
in every degree `g ≥ 1`. -/
lemma minimalLevel_Gamma [Nonempty l] (hN : 0 < N) :
    minimalLevel ((Gamma l N).map (map (Int.castRingHom ℚ))) = N := by
  refine minimalLevel_eq hN (isCongruenceOfLevel_Gamma l N) fun M h ↦ ?_
  let i : l := Classical.arbitrary l
  simpa [upperUnipotentSingle, coe_symTranslation, ZMod.natCast_eq_zero_iff] using
    congrFun₂ (mem_Gamma_iff.mp (mem_of_isCongruenceOfLevel h (upperUnipotentSingle_mem_Gamma i)))
      (.inl i) (.inr i)

/-- **The Siegel congruence subgroup `Γ₀(N)` has minimal level `N`** (LMFDB `mf.siegel.level`),
in every degree `g ≥ 1`. -/
lemma minimalLevel_Gamma0 [Nonempty l] (hN : 0 < N) :
    minimalLevel ((Gamma0 l N).map (map (Int.castRingHom ℚ))) = N := by
  refine minimalLevel_eq hN (isCongruenceOfLevel_Gamma0 l N) fun M h ↦ ?_
  let i : l := Classical.arbitrary l
  simpa [lowerUnipotentSingle, Int.natCast_dvd_natCast] using
    mem_Gamma0_iff.mp (mem_of_isCongruenceOfLevel h (lowerUnipotentSingle_mem_Gamma i)) i i

end SymplecticGroup

namespace SiegelUpperHalfSpace

/-- **The paramodular group `K(N)` of degree `2` has minimal level `N`** (LMFDB `mf.siegel.level`,
`group.paramodular`): it contains `Γ(N)`, and the entries of its elements in the place `(f₂, e₂)`
lie in `Nℤ`. -/
lemma minimalLevel_paramodularLevel (N : ℕ+) : minimalLevel (paramodularLevel N) = N := by
  refine minimalLevel_eq N.pos (isCongruenceOfLevel_paramodular fun i ↦ ?_) fun M h ↦ ?_
  · fin_cases i <;> simp
  rcases isParamodularShape_of_mem (h (Subgroup.mem_map_of_mem _
    (lowerUnipotentSingle_mem_Gamma (1 : Fin 2)))) with ⟨x, hx⟩
  have hM : (M : ℚ) = (N : ℕ) * x (.inr 1) (.inl 1) := by
    simpa [lowerUnipotentSingle, paramodularScale] using hx (.inr 1) (.inl 1)
  exact Int.natCast_dvd_natCast.mp ⟨x (.inr 1) (.inl 1), by exact_mod_cast hM⟩

end SiegelUpperHalfSpace
