import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeTriangular
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The Satake isomorphism of `Sp(2g, ℤ)` at `p`

The universal Satake map `Ω : 𝓗_p → L_g` of the local Hecke algebra of `Γ = Sp(2g, ℤ)` at a prime
`p` is injective (`SiegelUpperHalfSpace.satakeMapUniv_injective`) with image the Weyl-invariant
Laurent polynomials supported on the cone `0 ≤ d_j ≤ δ` of the weights `(δ; d)`
(`SiegelUpperHalfSpace.exists_satakeMapUniv_eq_iff`): Satake's theorem (Andrianov, *Quadratic forms
and Hecke operators*, Theorem 3.3.30, with the Laurent polynomials of the cone in place of the
polynomials in `x_0, x_0 x_1, …`).

Injectivity. By the elementary divisor theorem every double coset is `T(δ; a)` with dominant `a`,
and `Ω(T(δ; a))` has a nonzero coefficient at the dominant weight `(δ; δ - a)`, while its other
weights `(δ; δ - a')` with `a'` dominant have `a_0 + ⋯ + a_{k-1} ≤ a'_0 + ⋯ + a'_{k-1}` for every
`k`, so a larger height `∑_k (a'_0 + ⋯ + a'_{k-1})` (`SiegelUpperHalfSpace.expHeight`). In a
nonzero combination of double cosets, the coefficient at the dominant weight of one of least height
does not cancel.

Image. A Weyl-invariant `f` has the same coefficient at a weight of the cone as at the dominant
weight of its orbit (sign changes make `d_j ≥ δ - d_j`, a permutation sorts). Subtracting the
multiples of `Ω(T(δ; a))` that clear the coefficients of `f` at the dominant weights of largest
`(g + 1) g δ - height` only creates coefficients at dominant weights of smaller such level, so an
induction on it reaches `0`.

## Main definitions

* `SiegelUpperHalfSpace.satakeCone`: the cone of the weights `(δ; d)` with `0 ≤ d_j ≤ δ`.
* `SiegelUpperHalfSpace.coneAlgebra`: the Laurent polynomials supported on the cone.
* `SiegelUpperHalfSpace.expHeight`: the height of exponents.

## Main results

* `SiegelUpperHalfSpace.satakeMapUniv_injective`: the universal Satake map is injective.
* `SiegelUpperHalfSpace.exists_satakeMapUniv_eq_iff`: its image is the Weyl-invariant Laurent
  polynomials supported on the cone.
-/

open DoubleCoset MonoidAlgebra

open HeckeCosetModule (single)

namespace SiegelUpperHalfSpace

variable {n : ℕ}

/-! ### The cone -/

variable (n) in
/-- The **cone** of the weights `(δ; d)` with `0 ≤ d_j ≤ δ` (LMFDB `mf.siegel.lift`, through
Satake's theorem), in which the weights of the universal Satake map lie. -/
def satakeCone : Submonoid (SatakeWeight n) where
  carrier := {μ | 0 ≤ μ.toAdd.1 ∧ ∀ j, 0 ≤ μ.toAdd.2 j ∧ μ.toAdd.2 j ≤ μ.toAdd.1}
  mul_mem' hμ hν := ⟨add_nonneg hμ.1 hν.1, fun j ↦
    ⟨add_nonneg (hμ.2 j).1 (hν.2 j).1, add_le_add (hμ.2 j).2 (hν.2 j).2⟩⟩
  one_mem' := ⟨le_rfl, fun _ ↦ ⟨le_rfl, le_rfl⟩⟩

variable (n) in
/-- The subalgebra of the Laurent polynomials **supported on the cone** `0 ≤ d_j ≤ δ` (LMFDB
`mf.siegel.lift`, through Satake's theorem), in which the universal Satake map takes its values. -/
def coneAlgebra : Subalgebra ℂ (SatakeLaurent n) where
  carrier := {f | ∀ μ, f.coeff μ ≠ 0 → μ ∈ satakeCone n}
  mul_mem' {f g} hf hg μ hμ := by
    rcases Finset.mem_mul.mp (support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr hμ)) with
      ⟨μ₁, h₁, μ₂, h₂, rfl⟩
    exact mul_mem (hf μ₁ (Finsupp.mem_support_iff.mp h₁)) (hg μ₂ (Finsupp.mem_support_iff.mp h₂))
  add_mem' {f g} hf hg μ hμ := by
    rw [coeff_add, Finsupp.add_apply] at hμ
    by_cases h : f.coeff μ = 0
    · rw [h, zero_add] at hμ
      exact hg μ hμ
    · exact hf μ h
  algebraMap_mem' c μ hμ := by
    rw [coe_algebraMap, Function.comp_apply, coeff_single, Finsupp.single_apply] at hμ
    rw [← (ite_ne_right_iff.mp hμ).1]
    exact one_mem _

variable {μ : SatakeWeight n} {f : SatakeLaurent n}

lemma single_mem_coneAlgebra (hμ : μ ∈ satakeCone n) (c : ℂ) : single μ c ∈ coneAlgebra n :=
  fun ν hν ↦ by
    rw [coeff_single, Finsupp.single_apply] at hν
    rwa [← (ite_ne_right_iff.mp hν).1]

/-! ### The dominant weight of an orbit -/

lemma coeff_weylSign_of_mem (hf : f ∈ weylInvariants n) (j : Fin n) (μ : SatakeWeight n) :
    f.coeff (weylSign j μ) = f.coeff μ := by
  have h : (domCongr ℂ ℂ (weylSign j) f).coeff (weylSign j μ) = f.coeff μ := by
    rw [coeff_domCongr, MulEquiv.symm_apply_apply]
  rwa [domCongr_weylSign_of_mem j hf] at h

lemma coeff_weylPerm_of_mem (hf : f ∈ weylInvariants n) (σ : Equiv.Perm (Fin n))
    (μ : SatakeWeight n) : f.coeff (weylPerm σ μ) = f.coeff μ := by
  have h : (domCongr ℂ ℂ (weylPerm σ) f).coeff (weylPerm σ μ) = f.coeff μ := by
    rw [coeff_domCongr, MulEquiv.symm_apply_apply]
  rwa [domCongr_weylPerm_of_mem σ hf] at h

lemma coeff_ofAdd_ite_of_mem (hf : f ∈ weylInvariants n) (μ : SatakeWeight n) (s : Finset (Fin n)) :
    f.coeff (.ofAdd (μ.toAdd.1, fun j ↦ if j ∈ s then μ.toAdd.1 - μ.toAdd.2 j else μ.toAdd.2 j)) =
      f.coeff μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have e : weylSign j (.ofAdd (μ.toAdd.1, fun i ↦
        if i ∈ s then μ.toAdd.1 - μ.toAdd.2 i else μ.toAdd.2 i)) = .ofAdd (μ.toAdd.1, fun i ↦
          if i ∈ insert j s then μ.toAdd.1 - μ.toAdd.2 i else μ.toAdd.2 i) := by
      simp only [weylSign, MulEquiv.coe_mk, Equiv.coe_fn_mk]
      congr 2
      funext i
      rcases eq_or_ne i j with rfl | hi
      · simp [hj]
      · simp [hi]
    rw [← e, coeff_weylSign_of_mem hf, ih]

lemma exists_coeff_eq_dominantWeight (hμ : μ ∈ satakeCone n) :
    ∃ (δ : ℕ) (a : Fin n → ℕ), Monotone a ∧ (∀ j, 2 * a j ≤ δ) ∧
      ∀ f ∈ weylInvariants n, f.coeff μ = f.coeff (dominantWeight δ a) := by
  let u : Fin n → ℤ := fun j ↦ max (μ.toAdd.2 j) (μ.toAdd.1 - μ.toAdd.2 j)
  let σ : Equiv.Perm (Fin n) := Tuple.sort fun j ↦ OrderDual.toDual (u j)
  have hu (j : Fin n) : 2 * (μ.toAdd.1 - u j) ≤ μ.toAdd.1 ∧ 0 ≤ μ.toAdd.1 - u j := by
    have h₁ : 0 ≤ μ.toAdd.2 j := (hμ.2 j).1
    have h₂ : μ.toAdd.2 j ≤ μ.toAdd.1 := (hμ.2 j).2
    simp only [u]
    omega
  refine ⟨μ.toAdd.1.toNat, fun j ↦ (μ.toAdd.1 - u (σ j)).toNat, fun i j hij ↦ ?_,
    fun j ↦ ?_, fun f hf ↦ ?_⟩
  · have h : u (σ j) ≤ u (σ i) := Tuple.monotone_sort (fun j ↦ OrderDual.toDual (u j)) hij
    exact Int.toNat_le_toNat (by omega)
  · have h : 2 * (μ.toAdd.1 - u (σ j)) ≤ μ.toAdd.1 ∧ 0 ≤ μ.toAdd.1 - u (σ j) := hu (σ j)
    beta_reduce
    omega
  · have e : weylPerm σ.symm (.ofAdd (μ.toAdd.1, fun j ↦ if j ∈ Finset.univ.filter fun j ↦
        μ.toAdd.2 j < μ.toAdd.1 - μ.toAdd.2 j then μ.toAdd.1 - μ.toAdd.2 j else μ.toAdd.2 j)) =
          dominantWeight μ.toAdd.1.toNat fun j ↦ (μ.toAdd.1 - u (σ j)).toNat := by
      simp only [weylPerm, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd]
      refine congrArg Multiplicative.ofAdd (Prod.ext (Int.toNat_of_nonneg hμ.1).symm
        (funext fun j ↦ ?_))
      have h : 2 * (μ.toAdd.1 - u (σ j)) ≤ μ.toAdd.1 ∧ 0 ≤ μ.toAdd.1 - u (σ j) := hu (σ j)
      simp only [Function.comp_apply, Equiv.symm_symm, Finset.mem_filter, Finset.mem_univ,
        true_and, Int.toNat_of_nonneg h.2, u]
      split_ifs <;> omega
    rw [← e, coeff_weylPerm_of_mem hf, coeff_ofAdd_ite_of_mem hf]

/-! ### Heights of exponents -/

variable (n) in
/-- The **height** `∑_{k ≤ g} (a_0 + ⋯ + a_{k-1})` of exponents `a : Fin g → ℕ` (LMFDB
`mf.siegel.lift`, through Satake's theorem), which increases along the triangularity of the Satake
map. -/
def expHeight (a : Fin n → ℕ) : ℕ :=
  ∑ k : Fin (n + 1), ∑ j : Fin k, a (Fin.castLE (Nat.lt_succ_iff.mp k.2) j)

variable {δ : ℕ} {a a' : Fin n → ℕ}

lemma expHeight_le (ha : ∀ j, a j ≤ δ) : expHeight n a ≤ (n + 1) * (n * δ) := by
  have h (k : Fin (n + 1)) : ∑ j : Fin k, a (Fin.castLE (Nat.lt_succ_iff.mp k.2) j) ≤ n * δ :=
    (Finset.sum_le_card_nsmul _ _ δ fun j _ ↦ ha _).trans (by
      rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      exact Nat.mul_le_mul_right δ (Nat.lt_succ_iff.mp k.2))
  refine (Finset.sum_le_card_nsmul _ _ (n * δ) fun k _ ↦ h k).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul]

lemma eq_of_forall_sum_le (h : ∀ k (hk : k ≤ n), ∑ j : Fin k, a (Fin.castLE hk j) ≤
    ∑ j : Fin k, a' (Fin.castLE hk j)) (h' : expHeight n a' ≤ expHeight n a) : a = a' := by
  rw [expHeight, expHeight] at h'
  have hs : ∀ k : Fin (n + 1), ∑ j : Fin k, a (Fin.castLE (Nat.lt_succ_iff.mp k.2) j) =
      ∑ j : Fin k, a' (Fin.castLE (Nat.lt_succ_iff.mp k.2) j) := fun k ↦
    (Finset.sum_eq_sum_iff_of_le fun (k : Fin (n + 1)) _ ↦ h k (Nat.lt_succ_iff.mp k.2)).mp
      (le_antisymm (Finset.sum_le_sum fun (k : Fin (n + 1)) _ ↦ h k (Nat.lt_succ_iff.mp k.2))
        h') k (Finset.mem_univ k)
  funext j
  have h₁ : ∑ i : Fin (j + 1), a (Fin.castLE (Nat.lt_succ_iff.mp (Nat.succ_lt_succ j.2)) i) =
      ∑ i : Fin (j + 1), a' (Fin.castLE (Nat.lt_succ_iff.mp (Nat.succ_lt_succ j.2)) i) :=
    hs ⟨j + 1, Nat.succ_lt_succ j.2⟩
  have h₀ : ∑ i : Fin j, a (Fin.castLE (Nat.lt_succ_iff.mp (Nat.lt_succ_of_lt j.2)) i) =
      ∑ i : Fin j, a' (Fin.castLE (Nat.lt_succ_iff.mp (Nat.lt_succ_of_lt j.2)) i) :=
    hs ⟨j, Nat.lt_succ_of_lt j.2⟩
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at h₁
  have e : Fin.castLE (Nat.lt_succ_iff.mp (Nat.succ_lt_succ j.2)) (Fin.last j) = j := Fin.ext rfl
  rw [e] at h₁
  exact Nat.add_left_cancel (h₀.symm ▸ h₁)

/-! ### Injectivity -/

variable (p : ℕ) [Fact p.Prime]

lemma elementaryCoset_congr {δ' : ℕ} (ha : ∀ j, a j ≤ δ) (ha' : ∀ j, a' j ≤ δ') (hδ : δ = δ')
    (h : a = a') : elementaryCoset p δ a ha = elementaryCoset p δ' a' ha' := by
  subst hδ h
  rfl

variable [NeZero n]

lemma satakeMapUniv_smul (c : ℂ) (T : localSiegelHeckeRing (Fin n) p) :
    satakeMapUniv p (c • T) = c • satakeMapUniv p T := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => rw [smul_zero, map_zero, smul_zero]
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | hsingle D b =>
    rw [← HeckeCosetModule.smul_single_one ℂ D b, smul_smul, HeckeCosetModule.smul_single_one,
      HeckeCosetModule.smul_single_one, satakeMapUniv_single, satakeMapUniv_single p D b,
      smul_smul]

lemma sum_le_sum_dominantWeight (ha : ∀ j, a j ≤ δ) (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ)
    {δ' : ℕ} (h : (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff
      (dominantWeight δ' a') ≠ 0) (k : ℕ) (hk : k ≤ n) :
    ∑ j : Fin k, a (Fin.castLE hk j) ≤ ∑ j : Fin k, a' (Fin.castLE hk j) := by
  have h' : ∑ j, (a (Fin.castLE hk j) : ℤ) ≤ ∑ j, ((dominantWeight δ' a').toAdd.1 -
      (dominantWeight δ' a').toAdd.2 (Fin.castLE hk j)) :=
    sum_le_sum_of_coeff_satakeMapUniv_ne_zero hmono h2 h hk
  simp only [dominantWeight, toAdd_ofAdd, sub_sub_cancel] at h'
  exact_mod_cast h'

lemma eq_of_coeff_satakeMapUniv_dominantWeight_ne_zero (ha : ∀ j, a j ≤ δ) {δ' : ℕ}
    (h : (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff
      (dominantWeight δ' a') ≠ 0) : δ' = δ := by
  have h' : (dominantWeight δ' a').toAdd.1 = δ := fst_eq_of_coeff_satakeMapUniv_ne_zero h
  simp only [dominantWeight, toAdd_ofAdd] at h'
  exact_mod_cast h'

/-- **The universal Satake map is injective** (LMFDB `mf.siegel.lift`, through Satake's theorem):
a nonzero combination of double cosets has, at the dominant weight of one of its double cosets of
least height, a nonzero coefficient. -/
lemma satakeMapUniv_injective : Function.Injective (satakeMapUniv p (n := n)) := by
  refine (injective_iff_map_eq_zero _).mpr fun T hT ↦ ?_
  by_contra hT0
  choose δ a ha hmono h2 hD using fun D ↦ exists_eq_elementaryCoset (p := p) D
  rcases Finset.exists_min_image T.support (fun D ↦ expHeight n (a D))
    (Finsupp.support_nonempty_iff.mpr hT0) with ⟨D₀, hD₀, hmin⟩
  have hc₀ : (satakeMapUniv p (single ℂ D₀ 1)).coeff (dominantWeight (δ D₀) (a D₀)) ≠ 0 := by
    have h : (satakeMapUniv p (single ℂ (elementaryCoset p (δ D₀) (a D₀) (ha D₀)) 1)).coeff
        (dominantWeight (δ D₀) (a D₀)) ≠ 0 := coeff_satakeMapUniv_dominantWeight_ne_zero
    rwa [← hD D₀] at h
  have hcoeff : (satakeMapUniv p T).coeff (dominantWeight (δ D₀) (a D₀)) =
      T D₀ * (satakeMapUniv p (single ℂ D₀ 1)).coeff (dominantWeight (δ D₀) (a D₀)) := by
    conv_lhs => rw [← HeckeCosetModule.sum_single ℂ T]
    rw [HeckeCosetModule.sum_def, map_sum, coeff_sum, Finsupp.finsetSum_apply,
      Finset.sum_eq_single D₀]
    · rw [satakeMapUniv_single, coeff_smul_apply, smul_eq_mul]
    · intro D hDT hne
      rw [satakeMapUniv_single, coeff_smul_apply, smul_eq_mul]
      refine mul_eq_zero_of_right _ ?_
      by_contra hc
      rw [hD D] at hc
      have hδ : δ D₀ = δ D := eq_of_coeff_satakeMapUniv_dominantWeight_ne_zero p (ha D) hc
      have ha' : a D = a D₀ := eq_of_forall_sum_le
        (sum_le_sum_dominantWeight p (ha D) (hmono D) (h2 D) hc) (hmin D hDT)
      refine hne ?_
      rw [hD D, hD D₀]
      exact elementaryCoset_congr p _ _ hδ.symm ha'
    · exact fun h ↦ absurd hD₀ h
  rw [hT, coeff_zero, Finsupp.zero_apply] at hcoeff
  exact mul_ne_zero (Finsupp.mem_support_iff.mp hD₀) hc₀ hcoeff.symm

/-! ### The image -/

lemma satakeMapUniv_mem_coneAlgebra (T : localSiegelHeckeRing (Fin n) p) :
    satakeMapUniv p T ∈ coneAlgebra n := fun _ hμ ↦
  ⟨(nonneg_of_coeff_satakeMapUniv_ne_zero hμ 0).trans (le_of_coeff_satakeMapUniv_ne_zero hμ 0),
    fun j ↦ ⟨nonneg_of_coeff_satakeMapUniv_ne_zero hμ j, le_of_coeff_satakeMapUniv_ne_zero hμ j⟩⟩

lemma expHeight_lt_of_coeff_ne_zero (ha : ∀ j, a j ≤ δ) (hmono : Monotone a) (h2 : ∀ j, 2 * a j ≤ δ)
    {δ' : ℕ} (h : (satakeMapUniv p (single ℂ (elementaryCoset p δ a ha) 1)).coeff
      (dominantWeight δ' a') ≠ 0) (hne : a' ≠ a) : expHeight n a < expHeight n a' :=
  lt_of_le_of_ne (Finset.sum_le_sum fun k _ ↦ sum_le_sum_dominantWeight p ha hmono h2 h k _)
    fun he ↦ hne (eq_of_forall_sum_le (sum_le_sum_dominantWeight p ha hmono h2 h) he.ge).symm

lemma exists_satakeMapUniv_eq_of_lt (N : ℕ) {f : SatakeLaurent n} (hf : f ∈ weylInvariants n)
    (hc : f ∈ coneAlgebra n) (hN : ∀ δ a, Monotone a → (∀ j, 2 * a j ≤ δ) →
      f.coeff (dominantWeight δ a) ≠ 0 → (n + 1) * (n * δ) < expHeight n a + N) :
    ∃ T, satakeMapUniv p T = f := by
  induction N generalizing f with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero]
    ext μ
    rw [coeff_zero, Finsupp.zero_apply, eq_comm]
    by_contra hμ
    rcases exists_coeff_eq_dominantWeight (hc μ hμ) with ⟨δ, a, hmono, h2, hfa⟩
    have h₁ : (n + 1) * (n * δ) < expHeight n a + 0 := hN δ a hmono h2 (by rwa [← hfa f hf])
    have h₂ : expHeight n a ≤ (n + 1) * (n * δ) := expHeight_le fun j ↦ by
      have h : 2 * a j ≤ δ := h2 j
      omega
    omega
  | succ N ih =>
    have H : ∀ F : Finset (ℕ × (Fin n → ℕ)), (∀ x ∈ F, (n + 1) * (n * x.1) <
        expHeight n x.2 + (N + 1)) → ∀ g ∈ weylInvariants n, g ∈ coneAlgebra n →
          (∀ δ a, Monotone a → (∀ j, 2 * a j ≤ δ) → g.coeff (dominantWeight δ a) ≠ 0 →
            (n + 1) * (n * δ) < expHeight n a + N ∨ (δ, a) ∈ F) →
              ∃ T, satakeMapUniv p T = g := by
      intro F
      induction F using Finset.induction_on with
      | empty =>
        rintro - g hg hgc hgN
        exact ih hg hgc fun δ a hm h2 hne ↦
          (hgN δ a hm h2 hne).resolve_right (Finset.notMem_empty _)
      | insert x F hx ihF =>
        intro hF g hg hgc hgN
        by_cases hxd : Monotone x.2 ∧ ∀ j, 2 * x.2 j ≤ x.1
        · have hxa : ∀ j, x.2 j ≤ x.1 := fun j ↦ by
            have h : 2 * x.2 j ≤ x.1 := hxd.2 j
            omega
          let T₁ : localSiegelHeckeRing (Fin n) p := single ℂ (elementaryCoset p x.1 x.2 hxa) 1
          have hT₁ : (satakeMapUniv p T₁).coeff (dominantWeight x.1 x.2) ≠ 0 :=
            coeff_satakeMapUniv_dominantWeight_ne_zero
          let c : ℂ := g.coeff (dominantWeight x.1 x.2) /
            (satakeMapUniv p T₁).coeff (dominantWeight x.1 x.2)
          have hgN' : ∀ δ a, Monotone a → (∀ j, 2 * a j ≤ δ) →
              (g - c • satakeMapUniv p T₁).coeff (dominantWeight δ a) ≠ 0 →
                (n + 1) * (n * δ) < expHeight n a + N ∨ (δ, a) ∈ F := by
            intro δ a hm h2 hne
            rw [coeff_sub, Finsupp.sub_apply, coeff_smul_apply, smul_eq_mul] at hne
            by_cases hxe : (δ, a) = x
            · subst hxe
              exact absurd (sub_eq_zero.mpr (div_mul_cancel₀ _ hT₁).symm) hne
            by_cases hΩ : (satakeMapUniv p T₁).coeff (dominantWeight δ a) = 0
            · rw [hΩ, mul_zero, sub_zero] at hne
              exact (hgN δ a hm h2 hne).imp_right fun h ↦
                (Finset.mem_insert.mp h).resolve_left hxe
            · have hδ : δ = x.1 := eq_of_coeff_satakeMapUniv_dominantWeight_ne_zero p hxa hΩ
              have ha : a ≠ x.2 := fun ha ↦ hxe (Prod.ext hδ ha)
              have hlt : expHeight n x.2 < expHeight n a :=
                expHeight_lt_of_coeff_ne_zero p hxa hxd.1 hxd.2 hΩ ha
              have hx' : (n + 1) * (n * x.1) < expHeight n x.2 + (N + 1) :=
                hF x (Finset.mem_insert_self x F)
              left
              rw [hδ]
              omega
          rcases ihF (fun y hy ↦ hF y (Finset.mem_insert_of_mem hy)) (g - c • satakeMapUniv p T₁)
            (sub_mem hg (Subalgebra.smul_mem _ (satakeMapUniv_mem_weylInvariants p T₁) c))
            (sub_mem hgc (Subalgebra.smul_mem _ (satakeMapUniv_mem_coneAlgebra p T₁) c)) hgN' with
            ⟨T, hT⟩
          exact ⟨T + c • T₁, by rw [map_add, satakeMapUniv_smul, hT, sub_add_cancel]⟩
        · exact ihF (fun y hy ↦ hF y (Finset.mem_insert_of_mem hy)) g hg hgc fun δ a hm h2 hne ↦
            (hgN δ a hm h2 hne).imp_right fun h ↦ (Finset.mem_insert.mp h).resolve_left
              fun hxe ↦ hxd (by
                subst hxe
                exact ⟨hm, h2⟩)
    refine H ((f.coeff.support.image fun μ ↦ (μ.toAdd.1.toNat,
      fun j ↦ (μ.toAdd.1 - μ.toAdd.2 j).toNat)).filter fun x ↦
        (n + 1) * (n * x.1) < expHeight n x.2 + (N + 1)) (fun x hx ↦ (Finset.mem_filter.mp hx).2)
      f hf hc fun δ a hm h2 hne ↦ Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨_, Finsupp.mem_support_iff.mpr hne, ?_⟩, hN δ a hm h2 hne⟩)
    refine Prod.ext (by simp [dominantWeight]) (funext fun j ↦ ?_)
    simp [dominantWeight]

/-- **The image of the universal Satake map** (LMFDB `mf.siegel.lift`, through Satake's theorem):
a Laurent polynomial is `Ω(T)` for some `T ∈ 𝓗_p` exactly when it is Weyl-invariant and supported
on the cone `0 ≤ d_j ≤ δ`. -/
lemma exists_satakeMapUniv_eq_iff :
    (∃ T, satakeMapUniv p T = f) ↔ f ∈ weylInvariants n ∧ f ∈ coneAlgebra n := by
  refine ⟨?_, fun ⟨hf, hc⟩ ↦ exists_satakeMapUniv_eq_of_lt p ((n + 1) * (n *
    f.coeff.support.sup fun μ ↦ μ.toAdd.1.toNat) + 1) hf hc fun δ a hm h2 hne ↦ ?_⟩
  · rintro ⟨T, rfl⟩
    exact ⟨satakeMapUniv_mem_weylInvariants p T, satakeMapUniv_mem_coneAlgebra p T⟩
  · have h : δ ≤ f.coeff.support.sup fun μ ↦ μ.toAdd.1.toNat := by
      have h' : (dominantWeight δ a).toAdd.1.toNat ≤
          f.coeff.support.sup fun μ ↦ μ.toAdd.1.toNat :=
        Finset.le_sup (f := fun μ : SatakeWeight n ↦ μ.toAdd.1.toNat)
          (Finsupp.mem_support_iff.mpr hne)
      simpa [dominantWeight] using h'
    have h' : (n + 1) * (n * δ) ≤ (n + 1) * (n * f.coeff.support.sup fun μ ↦ μ.toAdd.1.toNat) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
    omega

end SiegelUpperHalfSpace
