import LeanBridge.ForMathlib.NumberTheory.LocalField.TameUnramifiedDegree
import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# Wild Artin slopes, Swan slopes, rams and the slope content of extensions of local fields

Let `L / K` be a finite Galois extension of nonarchimedean local fields with Galois group `G` and
residue characteristic `p`. The LMFDB writes `G^{(s)} = G^{s - 1}` for Serre's upper numbering and
`G^{(s+)} = ⋃_{ε > 0} G^{(s + ε)}`. The wild Artin slopes are the `s > 1` with
`G^{(s)} ≠ G^{(s+)}`, each repeated `m` times where `p ^ m = [G^{(s)} : G^{(s+)}]`.

Lower jumps are integers, and the Herbrand function `φ` carries them exactly to the upper jumps
(Tau Ceti's `upperJump_herbrand_iff`). For an integer `i ≥ 0` we have `G^{φ(i)} = G_i`, and
`G^v = G_{i + 1}` for `φ(i) < v ≤ φ(i + 1)`, so `G^{φ(i)+} = G_{i + 1}`. Hence the wild Artin slopes
are the `1 + φ(i)` for the positive lower jumps `i`, with multiplicity `log_p [G_i : G_{i + 1}]`,
which is how we define them.

## Main definitions

* `IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois` (LMFDB `lf.wild_slopes`,
  `lf.galois_invariants`): the wild Artin slopes of a Galois extension.
* `IsNonarchimedeanLocalField.swanSlopesOfIsGalois` (LMFDB `lf.swan_slopes`): its Swan slopes.
* `IsNonarchimedeanLocalField.ramsOfIsGalois` (LMFDB `lf.rams`): its rams, the positive lower jumps.
* `IsNonarchimedeanLocalField.wildArtinSlopes` (LMFDB `lf.slope_content`): the wild Artin slopes of
  the Galois closure of a finite separable extension.
* `IsNonarchimedeanLocalField.swanSlopes` (LMFDB `lf.slope_content`): its Swan slopes.
* `IsNonarchimedeanLocalField.artinSlopeContent` (LMFDB `lf.slope_content`): the Artin slope content
  `[s_1, …, s_k]_t^u`.

## Main theorems

* `IsNonarchimedeanLocalField.upperRamificationGroup_eq_of_mem_Ioc`: `G^v = G_{i + 1}` for
  `φ(i) < v ≤ φ(i + 1)`, which identifies `G^{φ(i)+}` with `G_{i + 1}`.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L] [IsGalois K L]

/-- **The upper ramification group just above `φ(i)`**: for a natural number `i` and
`φ(i) < v ≤ φ(i + 1)`, the upper ramification group `G^v` is the lower ramification group
`G_{i + 1}`. Together with `G^{φ(i)} = G_i`, this says `G^{φ(i)+} = G_{i + 1}`. -/
lemma upperRamificationGroup_eq_of_mem_Ioc (i : ℕ) {v : RamificationIndexDomain}
    (hv : v ∈ Set.Ioc (herbrand K L ⟨i, Nat.cast_mem_ramificationIndexDomain i⟩)
      (herbrand K L ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩)) :
    upperRamificationGroup K L v = lowerRamificationGroup K L (i + 1) := by
  have h₁ : (i : ℝ) < inverseHerbrand K L v := by
    simpa [← Subtype.coe_lt_coe] using inverseHerbrand_strictMono K L hv.1
  have h₂ : (inverseHerbrand K L v : ℝ) ≤ (i + 1 : ℕ) := by
    simpa [← Subtype.coe_le_coe] using (inverseHerbrand_strictMono K L).monotone hv.2
  rw [upperRamificationGroup_def]
  apply lowerRamificationGroupReal_eq_of_sub_one_lt_of_le
  · push_cast
    linarith
  · exact_mod_cast h₂

/-- The **wild Artin slopes** (LMFDB `lf.wild_slopes`, `lf.galois_invariants`) of a finite Galois
extension `L / K` of nonarchimedean local fields of residue characteristic `p`: the `s > 1` with
`G^{(s)} ≠ G^{(s+)}`, where `G^{(s)} = G^{s - 1}`, each repeated `m` times with
`p ^ m = [G^{(s)} : G^{(s+)}]`. As a multiset, it is the sum over the integers `1 ≤ i ≤ t`, for `t`
the largest lower jump, of `1 + φ(i)` repeated `log_p [G_i : G_{i + 1}]` times: the upper jumps are
the `φ(i)` (`upperJump_herbrand_iff`), `G^{φ(i)} = G_i` and `G^{φ(i)+} = G_{i + 1}`
(`upperRamificationGroup_eq_of_mem_Ioc`). The LMFDB lists them in nondecreasing order. -/
noncomputable def wildArtinSlopesOfIsGalois : Multiset ℝ :=
  ∑ i ∈ range (largestLowerJump K L).toNat, Multiset.replicate
    (padicValNat (ringChar 𝓀[K])
      ((lowerRamificationGroup K L (i + 2)).relIndex (lowerRamificationGroup K L (i + 1))))
    (1 + herbrand K L ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩)

/-- The **Swan slopes** (LMFDB `lf.swan_slopes`) of a finite Galois extension `L / K` of
nonarchimedean local fields: the wild Artin slopes minus `1`, that is the positive upper jumps `u`
of the ramification filtration, each repeated `log_p [G^u : G^{u+}]` times. There are
`v_p(e(L / K))` of them. LMFDB `lf.swan_slopes` says "nonnegative upper breaks", but the tame break
`0` is not a Swan slope in the LMFDB's data (LMFDB `lf.slopes` says "positive"). -/
noncomputable def swanSlopesOfIsGalois : Multiset ℝ :=
  (wildArtinSlopesOfIsGalois K L).map (· - 1)

/-- The **rams** (LMFDB `lf.rams`) of a finite Galois extension `L / K` of nonarchimedean local
fields: the positive lower ramification jumps `i`, each repeated `log_p [G_i : G_{i + 1}]` times,
so that there are `v_p(e(L / K))` of them. The rams of a non-Galois extension (Deligne's lower
numbering) are not formalised. -/
noncomputable def ramsOfIsGalois : Multiset ℕ :=
  ∑ i ∈ range (largestLowerJump K L).toNat, Multiset.replicate
    (padicValNat (ringChar 𝓀[K])
      ((lowerRamificationGroup K L (i + 2)).relIndex (lowerRamificationGroup K L (i + 1)))) (i + 1)

variable (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- The **wild Artin slopes** (LMFDB `lf.slope_content`, `lf.galois_invariants`) of a finite
separable extension `E / K` of a nonarchimedean local field: those of its Galois closure
`Algebra.galoisClosure K E` over `K`, equipped with Tau Ceti's spectral-norm local-field
structure. -/
noncomputable def wildArtinSlopes : Multiset ℝ :=
  letI : ValuativeRel (Algebra.galoisClosure K E) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K E) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K E) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  haveI : ValuativeExtension K (Algebra.galoisClosure K E) :=
    finiteIntermediateField_valuativeExtension K _ _
  wildArtinSlopesOfIsGalois K (Algebra.galoisClosure K E)

/-- The **Swan slopes** (LMFDB `lf.slope_content`) of the Galois closure of a finite separable
extension `E / K` of a nonarchimedean local field: its wild Artin slopes minus `1`. -/
noncomputable def swanSlopes : Multiset ℝ :=
  (wildArtinSlopes K E).map (· - 1)

/-- The **Artin slope content** `[s_1, …, s_k]_t^u` (LMFDB `lf.slope_content`) of a finite
separable extension `E / K` of a nonarchimedean local field: the wild Artin slopes `s_i` of its
Galois closure, its tame degree `t` and its unramified degree `u`. -/
noncomputable def artinSlopeContent : Multiset ℝ × ℕ × ℕ :=
  (wildArtinSlopes K E, galoisTameDegree K E, galoisUnramifiedDegree K E)

end IsNonarchimedeanLocalField
