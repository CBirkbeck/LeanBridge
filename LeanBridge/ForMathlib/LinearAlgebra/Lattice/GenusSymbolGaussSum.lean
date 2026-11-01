import LeanBridge.ForMathlib.LinearAlgebra.Lattice.DyadicGaussSum
import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolOddity

/-!
# The genus invariance of the canonical `2`-adic symbol and of the label

The oddities of the compartments of Conway and Sloane's canonical `2`-adic symbol (LMFDB
`lattice.conway_genus_symbol`), and hence the label of the genus (LMFDB `lattice.genus_label`),
are determined by the genus invariants proved so far and the Gauss oddities `Θ_m` at the scales
`2 ^ m` of type `II` (`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolOddity`). This file
proves that these Gauss oddities are genus invariants, so that the canonical `2`-adic symbol and
the label are genus invariants unconditionally.

At a scale `2 ^ m` of type `II`, the dyadic Gauss sum of level `m + 1` of the localization
`L ⊗ ℤ_2`, `Σ_(x ∈ L ⊗ ℤ_2 / 2 ^ (m + 1)) exp(2 π i B(x, x) / 2 ^ (m + 1))`, factors over the
dyadic Jordan splitting `⊕_j 2 ^ j f_j`. The constituents with `j < m` contribute a positive real
times `ε_j ^ (m - j) ζ₈ ^ t_j`, and the other ones a positive real, every term of their sums being
`1`. The Gauss sum is thus a positive real times `ζ₈ ^ Θ_m`, and it is a genus invariant, which
determines `Θ_m`.

## Main results

* `TauCeti.IntegralLattice.exists_dyadicGaussSum_eq`: the Gauss sum of level `m + 1` of the
  dyadic localization is a positive real times `ζ₈ ^ Θ_m` at a scale of type `II`.
* `TauCeti.IntegralLattice.SameGenus.dyadicGaussOddity_eq`: the Gauss oddities at the scales of
  type `II` are genus invariants.
* `TauCeti.IntegralLattice.SameGenus.compartmentOddities_eq`: so are the oddities of the
  compartments of the canonical `2`-adic symbol.
* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_congr`: so is the label of the genus.
-/

open Module TauCeti IntegralLattice

open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {K : Type*} [AddCommGroup K] [Module ℤ_[2] K] [Free ℤ_[2] K] [Module.Finite ℤ_[2] K]
  {B : BilinForm ℤ_[2] K} {N : ℕ → Submodule ℤ_[2] K}

lemma pow_mul_stdAddChar {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (s : ℕ) (t : ZMod 8) :
    (ε : ℂ) ^ s * ZMod.stdAddChar t =
      ZMod.stdAddChar (t + if Odd s then DyadicBlock.signOddity ε else 0) := by
  rw [AddChar.map_add_eq_mul, mul_comm]
  rcases hε with rfl | rfl
  · simp [DyadicBlock.signOddity]
  · rcases Nat.even_or_odd s with hs | hs
    · simp [hs.neg_one_pow, Nat.not_odd_iff_even.mpr hs]
    · have h4 : ZMod.stdAddChar (4 : ZMod 8) = -1 := ZMod.stdAddChar_four_eq_neg_one
      simp [hs, DyadicBlock.signOddity, h4]

lemma IsJordanSplitting.dyadicGaussSum_restrict_succ_of_lt
    (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) (hB : B.IsSymm) {j m : ℕ} (hjm : j < m) :
    (B.restrict (N j)).dyadicGaussSum (m + 1) = (2 ^ (j * finrank ℤ_[2] (N j)) *
      (√2 : ℂ) ^ ((m - j + 2) * finrank ℤ_[2] (N j))) * ZMod.stdAddChar (h.dyadicOddity j +
        if Odd (m - j) then DyadicBlock.signOddity (h.dyadicSign j) else 0) := by
  rw [(by omega : m + 1 = m - j + 1 + j), h.dyadicGaussSum_restrict,
    h.dyadicGaussSum_unitForm (m - j + 1) hB j (by omega), Nat.add_sub_cancel, mul_assoc,
    mul_assoc, pow_mul_stdAddChar h.dyadicSign_eq_one_or_eq_neg_one]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
  (m : ℕ)

/-- **The dyadic Gauss sum at a scale of type `II` has argument `ζ₈ ^ Θ_m`**: if the dyadic
Jordan constituent of scale `2 ^ m` of `L` has type `II`, the Gauss sum of level `m + 1` of the
dyadic localization of `L` is a positive real times `ζ₈ ^ Θ_m`, `Θ_m` being the Gauss oddity. -/
lemma exists_dyadicGaussSum_eq (hm : L.dyadicJordanType m = .II) : ∃ r : ℝ, 0 < r ∧
    (L.localIntegralForm 2).dyadicGaussSum (m + 1) =
      r * ZMod.stdAddChar (L.dyadicGaussOddity m) := by
  let N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2) :=
    (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose
  have h : (L.localIntegralForm 2).IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N :=
    (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose_spec
  rcases h.hasFiniteSupport.bddAbove with ⟨b, hb⟩
  have hJ (j : ℕ) (hj : max (b + 1) (m + 1) ≤ j) : N j = ⊥ := by
    by_contra hne
    have hjb : j ≤ b := hb hne
    omega
  have hfac (j : Fin (max (b + 1) (m + 1))) : ∃ r : ℝ, 0 < r ∧
      ((L.localIntegralForm 2).restrict (N j)).dyadicGaussSum (m + 1) =
        r * ZMod.stdAddChar (if (j : ℕ) < m then L.dyadicJordanOddity j +
          if Odd (m - j) then DyadicBlock.signOddity (L.dyadicJordanSign j) else 0 else 0) := by
    by_cases hjm : (j : ℕ) < m
    · simp only [hjm, ↓reduceIte]
      refine ⟨2 ^ ((j : ℕ) * finrank ℤ_[2] (N j)) * √2 ^ ((m - j + 2) * finrank ℤ_[2] (N j)),
        by positivity, ?_⟩
      rw [h.dyadicGaussSum_restrict_succ_of_lt (L.isSymm_localIntegralForm 2) hjm]
      push_cast
      rfl
    · simp only [hjm, ↓reduceIte, AddChar.map_zero_eq_one, mul_one]
      refine ⟨2 ^ ((m + 1) * finrank ℤ_[2] (N j)), by positivity, ?_⟩
      push_cast
      refine BilinForm.dyadicGaussSum_eq_of_forall_dvd _ _ fun x ↦ ?_
      rw [BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      by_cases hjm' : (j : ℕ) = m
      · rcases j with ⟨j, hjJ⟩
        simp only at hjm'
        subst hjm'
        simpa using forall_mem_pow_dvd_of_dyadicJordanType_eq hm x x.2
      · have hx : ((2 : ℕ) : ℤ_[2]) ^ (j : ℕ) ∣ L.localIntegralForm 2 x x := h.pow_dvd_apply x.2 x
        rw [Nat.cast_ofNat] at hx
        exact (pow_dvd_pow 2 (by omega)).trans hx
  choose r hr hG using hfac
  rw [h.dyadicGaussSum_eq_prod (m + 1) hJ, Finset.prod_congr rfl fun j _ ↦ hG j,
    Finset.prod_mul_distrib, ← ZMod.stdAddChar_sum]
  refine ⟨∏ j, r j, Finset.prod_pos fun j _ ↦ hr j, ?_⟩
  push_cast
  congr 2
  rw [dyadicGaussOddity_eq_sum, Fin.sum_univ_eq_sum_range (fun j ↦ if j < m then
    L.dyadicJordanOddity j + (if Odd (m - j) then DyadicBlock.signOddity (L.dyadicJordanSign j)
      else 0) else 0), ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **The Gauss oddities are genus invariants**: lattices in the same genus have the same Gauss
oddity `Θ_m` at every scale `2 ^ m` at which the dyadic Jordan constituent has type `II`, the
hypothesis of `SameGenus.compartmentOddities_eq_of_dyadicGaussOddity_eq`. -/
lemma SameGenus.dyadicGaussOddity_eq (h : L.SameGenus M) (hm : L.dyadicJordanType m = .II) :
    L.dyadicGaussOddity m = M.dyadicGaussOddity m := by
  rcases exists_dyadicGaussSum_eq m hm with ⟨r, hr, hL⟩
  rcases exists_dyadicGaussSum_eq m ((h.dyadicJordanType_eq m).symm.trans hm) with ⟨r', hr', hM⟩
  have heq : (r : ℂ) * ZMod.stdAddChar (L.dyadicGaussOddity m) =
      r' * ZMod.stdAddChar (M.dyadicGaussOddity m) := by
    rw [← hL, ← hM]
    exact h.dyadicGaussSum_eq (m + 1)
  have hrr : r = r' := by
    have hn : ‖(r : ℂ) * ZMod.stdAddChar (L.dyadicGaussOddity m)‖ =
        ‖(r' : ℂ) * ZMod.stdAddChar (M.dyadicGaussOddity m)‖ := by
      rw [heq]
    rw [norm_mul, norm_mul, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, Circle.norm_coe,
      Circle.norm_coe, mul_one, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hr.le, Real.norm_of_nonneg hr'.le] at hn
    exact hn
  subst hrr
  exact ZMod.injective_stdAddChar (mul_left_cancel₀ (by exact_mod_cast hr.ne') heq)

/-- **The oddities of the compartments of the canonical `2`-adic symbol are genus invariants**, so
that the whole canonical `2`-adic symbol is (LMFDB `lattice.conway_genus_symbol`). -/
lemma SameGenus.compartmentOddities_eq (h : L.SameGenus M) :
    L.compartmentOddities = M.compartmentOddities :=
  h.compartmentOddities_eq_of_dyadicGaussOddity_eq h.dyadicGaussOddity_eq

/-- **The label of the genus is a genus invariant** (LMFDB `lattice.genus_label`): lattices in the
same genus have the same label `canonicalGenusLabel` (for the LMFDB's exact encoding, see
`SameGenus.lmfdbGenusLabel_eq`). -/
lemma SameGenus.canonicalGenusLabel_congr (h : L.SameGenus M) :
    L.canonicalGenusLabel = M.canonicalGenusLabel :=
  h.canonicalGenusLabel_eq h.compartmentOddities_eq

end TauCeti.IntegralLattice
