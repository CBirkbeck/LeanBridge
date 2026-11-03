import LeanBridge.ForMathlib.Analysis.Fourier.TubeFourierSeries
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HolomorphicOperations

/-!
# Existence of Fourier expansions of Siegel modular forms

If the translation lattice `L_Γ` of `Γ ⊆ Sp(2g, ℚ)` contains `N · Sym_g(ℤ)` for some `N ≠ 0`, every
holomorphic `f : ℋ_g → V` periodic under `L_Γ`, with `V` finite-dimensional, has a Fourier expansion
`f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}` (LMFDB `mf.siegel.q-expansion`), the sum converging
absolutely through every linear form. This applies to every Siegel modular form on an arithmetic
subgroup.

The function `z ↦ u(N(z + zᵀ))` on the tube over `{y : N(y + yᵀ) > 0}` in `ℂ^{g × g}`, for a
coordinate `u` of `f`, is holomorphic and periodic under `ℤ^{g × g}`, so it is the sum of its
Fourier series (`hasSum_tubeFourierCoeff_mul_cexp`). The real periods of this function restrict the
frequencies `k ∈ ℤ^{g × g}` with `c(k) ≠ 0`: it does not change under `z ↦ z + t(E_ij - E_ji)`,
which makes `k` symmetric, and it does not change under `z ↦ z + s / (2N)`, `s ∈ L_Γ`, which makes
`n = k / (2N)` an element of the dual lattice `L_Γ^∨`.

## Main definitions

* `SiegelUpperHalfSpace.IsPeriodicOn`: periodicity under the translation lattice.

## Main results

* `SiegelUpperHalfSpace.exists_hasSiegelFourierExpansion_of_periodic`: a holomorphic function
  `ℋ_g → V` periodic under `L_Γ`, for `V` finite-dimensional, has a Fourier expansion.
* `SiegelUpperHalfSpace.exists_hasSiegelFourierExpansion` (LMFDB `mf.siegel.q-expansion`): a Siegel
  modular form on an arithmetic subgroup has a Fourier expansion.
-/

open Complex Matrix Module

open scoped Real

namespace SiegelUpperHalfSpace

variable {l : Type*} {N : ℕ} {u : SiegelUpperHalfSpace l → ℂ} (z : l × l → ℂ)

variable (l N) in
/-- The set of `y ∈ ℝ^{g × g}` with `N(y + yᵀ)` positive definite. -/
private def paramTube : Set (l × l → ℝ) :=
  {y | (of fun i j ↦ (N : ℝ) * (y (i, j) + y (j, i))).PosDef}

variable (N) in
/-- The matrix `2N z`, whose symmetrisation is `N(z + zᵀ)`. -/
private def scaleTwo : l → l → ℂ :=
  fun i j ↦ 2 * N * z (i, j)

private lemma map_im_symmetrize_scaleTwo : (symmetrize (scaleTwo N z)).map im = of fun i j ↦
    (N : ℝ) * ((z (i, j)).im + (z (j, i)).im) := by
  ext i j
  simp [symmetrize, scaleTwo]
  ring1

variable (N u) in
/-- The function `z ↦ u(N(z + zᵀ))` on the tube. -/
private noncomputable def tubeFunction : ℂ :=
  extend u (scaleTwo N z)

variable {z} in
private lemma scaleTwo_mem_iff :
    scaleTwo N z ∈ symmetrizePreimage l ↔ z ∈ tubeOver (paramTube l N) := by
  rw [symmetrizePreimage, Set.mem_ofPred_eq, map_im_symmetrize_scaleTwo]
  rfl

variable (N) [DecidableEq l] in
/-- The point `y₀ = 1 / (2N)` of `paramTube`, on the diagonal. -/
private noncomputable def baseHeight : l × l → ℝ :=
  fun p ↦ if p.1 = p.2 then 1 / (2 * N) else 0

variable [DecidableEq l] in
private lemma baseHeight_mem (hN : N ≠ 0) : baseHeight N ∈ paramTube l N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have e : (of fun i j ↦ (N : ℝ) * (baseHeight N (i, j) + baseHeight N (j, i))) =
      (1 : Matrix l l ℝ) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp [baseHeight]
      field_simp
      norm_num
    · simp [baseHeight, h, h.symm]
  rw [paramTube, Set.mem_ofPred_eq, e]
  exact PosDef.one

variable [Fintype l]

private lemma isOpen_paramTube : IsOpen (paramTube l N) := by
  have h : paramTube l N = (fun y : l × l → ℝ ↦ scaleTwo N fun p ↦ I * y p) ⁻¹'
      symmetrizePreimage l := by
    ext y
    rw [Set.mem_preimage, scaleTwo_mem_iff, mem_tubeOver]
    simp
  rw [h]
  refine isOpen_symmetrizePreimage.preimage <| continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  simp only [scaleTwo]
  fun_prop

private lemma convex_paramTube : Convex ℝ (paramTube l N) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have hH : (of fun i j ↦ (N : ℝ) * ((a • y₁ + b • y₂) (i, j) +
      (a • y₁ + b • y₂) (j, i))).IsHermitian := by
    ext i j
    simp [add_comm]
  refine posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun x hx ↦ ?_⟩
  have h₁ : 0 < star x ⬝ᵥ (of fun i j ↦ (N : ℝ) * (y₁ (i, j) + y₁ (j, i))) *ᵥ x :=
    (posDef_iff_dotProduct_mulVec.mp hy₁).2 hx
  have h₂ : 0 < star x ⬝ᵥ (of fun i j ↦ (N : ℝ) * (y₂ (i, j) + y₂ (j, i))) *ᵥ x :=
    (posDef_iff_dotProduct_mulVec.mp hy₂).2 hx
  have e : (of fun i j ↦ (N : ℝ) * ((a • y₁ + b • y₂) (i, j) + (a • y₁ + b • y₂) (j, i))) =
      a • (of fun i j ↦ (N : ℝ) * (y₁ (i, j) + y₁ (j, i))) +
        b • (of fun i j ↦ (N : ℝ) * (y₂ (i, j) + y₂ (j, i))) := by
    ext i j
    simp
    ring1
  rw [e, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : b = 1 := by linarith
    simpa [hb'] using h₂
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' h₁) (mul_nonneg hb h₂.le)

private lemma differentiableOn_tubeFunction (hu : IsHolomorphic u) :
    DifferentiableOn ℂ (tubeFunction N u) (tubeOver (paramTube l N)) :=
  (isHolomorphic_iff_differentiableOn.mp hu).comp (Differentiable.differentiableOn <|
    differentiable_pi.mpr fun i ↦ differentiable_pi.mpr fun j ↦ by
      simp only [scaleTwo]
      fun_prop) fun _ hz ↦ scaleTwo_mem_iff.mpr hz

variable [DecidableEq l] {Γ : Subgroup (symplecticGroup l ℚ)}

variable (Γ) in
/-- The function `f : ℋ_g → V` is **periodic under the translation lattice** `L_Γ`:
`f(τ + s) = f(τ)` for all `s ∈ L_Γ`. -/
def IsPeriodicOn {V : Type*} (f : SiegelUpperHalfSpace l → V) : Prop :=
  ∀ s ∈ translationLattice Γ, ∀ τ τ' : SiegelUpperHalfSpace l,
    τ'.val = τ.val + s.map ((↑) : ℚ → ℂ) → f τ' = f τ

private lemma tubeFunction_add (hu : IsPeriodicOn Γ u) {s : Matrix l l ℚ}
    (hs : s ∈ translationLattice Γ) {v : l × l → ℝ}
    (hv : ∀ i j, (N : ℝ) * (v (i, j) + v (j, i)) = (s i j : ℝ)) :
    tubeFunction N u (fun p ↦ z p + v p) = tubeFunction N u z := by
  have him : (fun p ↦ (z p + v p).im) = fun p ↦ (z p).im := by
    funext p
    simp
  have hmem : scaleTwo N (fun p ↦ z p + v p) ∈ symmetrizePreimage l ↔
      scaleTwo N z ∈ symmetrizePreimage l := by
    rw [scaleTwo_mem_iff, scaleTwo_mem_iff, mem_tubeOver, mem_tubeOver, him]
  by_cases hz : scaleTwo N z ∈ symmetrizePreimage l
  · rw [tubeFunction, tubeFunction, extend_of_mem _ hz, extend_of_mem _ (hmem.mpr hz)]
    refine hu s hs _ _ ?_
    ext i j
    have h₂ : ((s i j : ℚ) : ℂ) = (N : ℂ) * ((v (i, j) : ℂ) + v (j, i)) := by
      rw [← ofReal_ratCast, ← hv i j]
      push_cast
      rfl
    simp [symmetrize, scaleTwo, h₂]
    ring1
  · have h₁ : extend u (scaleTwo N z) = 0 := dite_eq_right hz
    have h₂ : extend u (scaleTwo N fun p ↦ z p + v p) = 0 := dite_eq_right (hz ∘ hmem.mp)
    rw [tubeFunction, tubeFunction, h₁, h₂]

private lemma of_mul_add_mem_translationLattice
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (m : l × l → ℤ) :
    (of fun i j ↦ (N : ℚ) * ((m (i, j) : ℚ) + m (j, i))) ∈ translationLattice Γ := by
  have e : (of fun i j ↦ (N : ℚ) * ((m (i, j) : ℚ) + m (j, i))) =
      ∑ p : l × l, m p • ((N : ℚ) • (single p.1 p.2 1 + single p.2 p.1 1)) := by
    ext i j
    simp [Matrix.sum_apply, Fintype.sum_prod_type, single_apply, ite_and, Finset.sum_add_distrib]
    ring1
  rw [e]
  exact sum_mem fun p _ ↦ zsmul_mem (hΓ p.1 p.2) _

private lemma tubeFunction_intCast
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (hu : IsPeriodicOn Γ u) (m : l × l → ℤ) :
    tubeFunction N u (fun p ↦ z p + m p) = tubeFunction N u z := by
  have h : tubeFunction N u (fun p ↦ z p + ((m p : ℝ) : ℂ)) = tubeFunction N u z :=
    tubeFunction_add z hu (of_mul_add_mem_translationLattice hΓ m) fun i j ↦ by simp
  simpa using h

private lemma symm_of_tubeFourierCoeff_ne_zero
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (hu : IsPeriodicOn Γ u) {y : l × l → ℝ} {k : l × l → ℤ}
    (hc : tubeFourierCoeff (tubeFunction N u) y k ≠ 0) (i j : l) : k (i, j) = k (j, i) := by
  by_contra hne
  have hne' : (k (i, j) : ℝ) - k (j, i) ≠ 0 := sub_ne_zero.mpr (mod_cast hne)
  let t : ℝ := 1 / (2 * ((k (i, j) : ℝ) - k (j, i)))
  let v : l × l → ℝ := fun p ↦ (if p = (i, j) then t else 0) - if p = (j, i) then t else 0
  have hv (a b : l) : (N : ℝ) * (v (a, b) + v (b, a)) = (((0 : Matrix l l ℚ) a b : ℚ) : ℝ) := by
    have e₁ : ((b, a) = (j, i)) = ((a, b) = (i, j)) := by
      simp [and_comm]
    have e₂ : ((b, a) = (i, j)) = ((a, b) = (j, i)) := by
      simp [and_comm]
    simp only [v, e₁, e₂]
    simp
  rcases exists_sum_eq_intCast_of_tubeFourierCoeff_ne_zero k
    (fun m z ↦ tubeFunction_intCast z hΓ hu m) v (tubeFunction_add · hu (zero_mem _) hv) hc with
    ⟨m, hm⟩
  have hsum : ∑ p, (k p : ℝ) * v p = 1 / 2 := by
    simp only [v, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    simp only [t]
    field_simp
  rw [hsum] at hm
  have h₂ : (2 : ℤ) * m = 1 := by
    have h₃ : (2 : ℝ) * m = 1 := by
      linarith
    exact_mod_cast h₃
  omega

private lemma mem_dualLattice_of_tubeFourierCoeff_ne_zero (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (hu : IsPeriodicOn Γ u) {y : l × l → ℝ} {k : l × l → ℤ}
    (hc : tubeFourierCoeff (tubeFunction N u) y k ≠ 0) :
    (of fun i j ↦ (k (i, j) : ℚ) / (2 * N)) ∈ dualLattice Γ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  refine ⟨?_, fun s hs ↦ ?_⟩
  · ext i j
    simp [symm_of_tubeFourierCoeff_ne_zero hΓ hu hc j i]
  · let v : l × l → ℝ := fun p ↦ (s p.1 p.2 : ℝ) / (2 * N)
    have hv (a b : l) : (N : ℝ) * (v (a, b) + v (b, a)) = (s a b : ℝ) := by
      have hsym : s b a = s a b := congrFun (congrFun hs.1 a) b
      simp only [v, hsym]
      field_simp
      ring1
    rcases exists_sum_eq_intCast_of_tubeFourierCoeff_ne_zero k
      (fun m z ↦ tubeFunction_intCast z hΓ hu m) v (tubeFunction_add · hu hs hv) hc with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h : (((s * of fun i j ↦ (k (i, j) : ℚ) / (2 * N)).trace : ℚ) : ℝ) = m := by
      rw [← hm, Fintype.sum_prod_type]
      simp only [trace, diag_apply, mul_apply, of_apply]
      push_cast
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      rw [symm_of_tubeFourierCoeff_ne_zero hΓ hu hc b a]
      ring1
    exact_mod_cast h

private lemma exists_hasSum_fourierExp (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (hu : IsHolomorphic u) (hp : IsPeriodicOn Γ u) :
    ∃ a : dualLattice Γ → ℂ, ∀ τ, HasSum (fun n ↦ fourierExp n τ * a n) (u τ) := by
  have hN₁ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hN₂ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  choose κ hκ using exists_intCast_eq hΓ
  have hinj : Function.Injective κ := fun n m h ↦ Subtype.ext <| ext fun i j ↦ by
    have h₁ : (κ n (i, j) : ℚ) = 2 * N * (n : Matrix l l ℚ) i j := hκ n (i, j)
    rw [h, hκ m (i, j)] at h₁
    exact (mul_right_injective₀ (by positivity : (2 * N : ℚ) ≠ 0) h₁).symm
  refine ⟨fun n ↦ tubeFourierCoeff (tubeFunction N u) (baseHeight N) (κ n), fun τ ↦ ?_⟩
  let z : l × l → ℂ := fun p ↦ τ.val p.1 p.2 / (2 * N)
  have hz : scaleTwo N z = τ.val := by
    funext i j
    simp only [scaleTwo, z]
    field_simp
  have hsym : symmetrize τ.val = τ.val := by
    ext i j
    have hτ : τ.val j i = τ.val i j := congrFun (congrFun τ.transpose_val i) j
    have e (a b : l) : of (τ.val : l → l → ℂ) a b = τ.val a b := rfl
    simp only [symmetrize, Matrix.smul_apply, Matrix.add_apply, transpose_apply, e, hτ]
    ring1
  have hτ₀ : (τ.val : l → l → ℂ) ∈ symmetrizePreimage l := by
    have h₁ : ((symmetrize τ.val).map im).PosDef := by
      rw [hsym]
      exact τ.posDef_im
    exact h₁
  have hz₀ : z ∈ tubeOver (paramTube l N) := scaleTwo_mem_iff.mp (hz ▸ hτ₀)
  have hval : tubeFunction N u z = u τ := by
    rw [tubeFunction, hz, extend_of_mem _ hτ₀]
    exact congrArg u (SiegelUpperHalfSpace.ext hsym)
  have h : HasSum (fun k ↦ tubeFourierCoeff (tubeFunction N u) (baseHeight N) k *
      cexp (2 * π * I * ∑ p, (k p : ℂ) * z p)) (u τ) :=
    hval ▸ hasSum_tubeFourierCoeff_mul_cexp isOpen_paramTube convex_paramTube
      (differentiableOn_tubeFunction hu) (fun m z ↦ tubeFunction_intCast z hΓ hp m)
      (baseHeight_mem hN) hz₀
  refine ((hinj.hasSum_iff fun k hk ↦ ?_).mpr h).congr_fun fun n ↦ ?_
  · by_contra hne
    have hc : tubeFourierCoeff (tubeFunction N u) (baseHeight N) k ≠ 0 := left_ne_zero_of_mul hne
    refine hk ⟨⟨_, mem_dualLattice_of_tubeFourierCoeff_ne_zero hN hΓ hp hc⟩, funext fun p ↦ ?_⟩
    have h₂ : (κ ⟨_, mem_dualLattice_of_tubeFourierCoeff_ne_zero hN hΓ hp hc⟩ p : ℚ) = k p := by
      rw [hκ]
      simp only [of_apply]
      field_simp
    exact_mod_cast h₂
  · have e : ((n : Matrix l l ℚ).map ((↑) : ℚ → ℂ) * τ.val).trace = ∑ p, (κ n p : ℂ) * z p := by
      rw [Fintype.sum_prod_type]
      simp only [trace, diag_apply, mul_apply, map_apply]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
      have hκ' : (κ n (a, b) : ℂ) = 2 * N * ((n : Matrix l l ℚ) a b : ℂ) := by
        exact_mod_cast hκ n (a, b)
      have hτ : τ.val b a = τ.val a b := congrFun (congrFun τ.transpose_val a) b
      simp only [z]
      rw [hκ', hτ]
      field_simp
    rw [Function.comp_apply, fourierExp, e, mul_comm]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f : SiegelUpperHalfSpace l → V}

/-- **Periodic holomorphic functions have Fourier expansions**: if the translation lattice `L_Γ`
contains `N · Sym_g(ℤ)` with `N ≠ 0`, every holomorphic `f : ℋ_g → V`, with `V` finite-dimensional,
which is periodic under `L_Γ` has a Fourier expansion
`f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}`. -/
lemma exists_hasSiegelFourierExpansion_of_periodic [FiniteDimensional ℂ V] (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (hf : IsHolomorphic f) (hp : IsPeriodicOn Γ f) :
    ∃ a : dualLattice Γ → V, HasSiegelFourierExpansion Γ f a := by
  let b : Basis (Fin (finrank ℂ V)) ℂ V := finBasis ℂ V
  have hc (i : Fin (finrank ℂ V)) :
      ∃ a : dualLattice Γ → ℂ, ∀ τ, HasSum (fun n ↦ fourierExp n τ * a n) (b.coord i (f τ)) :=
    exists_hasSum_fourierExp hN hΓ (isHolomorphic_iff_differentiableOn.mpr (hf (b.coord i)))
      fun s hs τ τ' h ↦ congrArg (b.coord i) (hp s hs τ τ' h)
  choose a ha using hc
  refine ⟨fun n ↦ ∑ i, a i n • b i, fun τ φ ↦ ?_⟩
  have h₁ : φ (f τ) = ∑ i, b.coord i (f τ) * φ (b i) := by
    conv_lhs => rw [← b.sum_repr (f τ), map_sum]
    simp
  rw [h₁]
  refine (hasSum_sum fun i _ ↦ (ha i τ).mul_right (φ (b i))).congr_fun fun n ↦ ?_
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable (ρ : Representation ℂ (GL l ℂ) V)

lemma isPeriodicOn_of_mem_modularForms (hf : f ∈ modularForms ρ Γ 1) : IsPeriodicOn Γ f := by
  rintro s ⟨-, γ, hγ, hγs⟩ τ τ' h
  have hcoe : (SymplecticGroup.map (algebraMap ℚ ℝ) γ : Matrix (l ⊕ l) (l ⊕ l) ℝ) =
      fromBlocks 1 (s.map ((↑) : ℚ → ℝ)) 0 1 := by
    rw [SymplecticGroup.coe_map_apply, hγs]
    simp [fromBlocks_map]
    ext i j
    simp
  have hdenom : denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) γ) τ = 1 := Units.ext <| by
    rw [coe_denomGL, denom, hcoe]
    simp
  have hτ' : τ' = SymplecticGroup.map (algebraMap ℚ ℝ) γ • τ := SiegelUpperHalfSpace.ext <| by
    rw [h, val_smul, num, denom, hcoe]
    simp
    ext i j
    simp
  have h₁ : f (SymplecticGroup.map (algebraMap ℚ ℝ) γ • τ) = ((1 : (Γ →* ℂˣ)) ⟨γ, hγ⟩ : ℂ) •
      ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) γ) τ) (f τ) := hf.2 ⟨γ, hγ⟩ τ
  rw [hτ']
  simpa [hdenom] using h₁

/-- **Siegel modular forms have Fourier expansions** (LMFDB `mf.siegel.q-expansion`): every
`f ∈ M_ρ(Γ)`, for `Γ` arithmetic and `ρ` finite-dimensional, is the sum
`f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}` of a Fourier series. -/
lemma exists_hasSiegelFourierExpansion [FiniteDimensional ℂ V] (hΓ : SymplecticGroup.IsArithmetic Γ)
    (hf : f ∈ modularForms ρ Γ 1) : ∃ a : dualLattice Γ → V, HasSiegelFourierExpansion Γ f a :=
  exists_hasSiegelFourierExpansion_of_periodic (Nat.factorial_ne_zero _)
    (smul_mem_translationLattice_of_isArithmetic · · hΓ) hf.1
    (isPeriodicOn_of_mem_modularForms ρ hf)

end SiegelUpperHalfSpace
