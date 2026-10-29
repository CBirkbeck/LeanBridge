import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.FourierExpansion
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Uniqueness of Fourier expansions of Siegel modular forms

If the translation lattice `L_Γ` of `Γ ⊆ Sp(2g, ℚ)` contains `N · Sym_g(ℤ)` for some `N ≠ 0` (for
instance when `Γ` contains the principal congruence subgroup `Γ(N)`, so whenever `Γ` is
commensurable with `Sp(2g, ℤ)`), then a function on `ℋ_g` has at most one Fourier expansion on `Γ`.

The proof restricts the expansion to `τ = X + i` with `X = N (A + Aᵀ)` for real `A`: there it is
an absolutely convergent Fourier series on the torus `(ℝ / ℤ)^{g × g}`, whose coefficients
`a(n) e^{-2π tr n}` are recovered from the orthonormality of the monomials in `L²`.

## Main results

* `UnitAddTorus.eq_zero_of_hasSum_mFourier`: an absolutely convergent Fourier series on the torus
  which vanishes everywhere has zero coefficients.
* `SiegelUpperHalfSpace.eq_zero_of_hasSum_fourierExp`: if `∑ c(n) e^{2πi tr(nτ)} = 0` on `ℋ_g`, the
  sum converging unconditionally, then `c = 0`.
* `SiegelUpperHalfSpace.HasSiegelFourierExpansion.unique`: Fourier expansions are unique.
* `SiegelUpperHalfSpace.fourierCoeffs_eq_range`: the Fourier coefficients of a function with a
  Fourier expansion `a` are the values of `a`.
-/

open Complex Matrix MeasureTheory Real UnitAddTorus

/-- The Haar probability measure on `ℝ / ℤ`, as in `Mathlib.Analysis.Fourier.AddCircleMulti`. -/
noncomputable local instance unitAddCircleHaarMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι]

/-- **Uniqueness of Fourier series on the torus**: if `∑ c(k) e^{2πi k·x}` converges absolutely and
vanishes at every `x ∈ (ℝ / ℤ)^ι`, then `c = 0`. -/
lemma eq_zero_of_hasSum_mFourier {c : (ι → ℤ) → ℂ} (hc : Summable c)
    (h : ∀ x, HasSum (fun k ↦ c k * mFourier k x) 0) : c = 0 := by
  have hC : Summable fun k ↦ c k • mFourier k :=
    .of_norm <| by simpa [norm_smul, mFourier_norm] using hc.norm
  have h0 : HasSum (fun k ↦ c k • mFourier k) 0 := by
    convert hC.hasSum
    ext x
    exact (h x).unique (by simpa using (ContinuousMap.evalCLM ℂ x).hasSum hC.hasSum)
  funext m
  have hm := ((innerSL ℂ (mFourierLp (d := ι) 2 m)).comp
    (ContinuousMap.toLp (E := ℂ) 2 volume ℂ)).hasSum h0
  simp only [ContinuousLinearMap.comp_apply, map_smul, map_zero, innerSL_apply_apply,
    orthonormal_iff_ite.mp orthonormal_mFourier m, smul_eq_mul, mul_ite, mul_one, mul_zero,
    eq_comm (a := m)] at hm
  refine (hasSum_ite_eq m (c m)).unique (hm.congr_fun fun b ↦ ?_)
  split_ifs with hb
  · rw [hb]
  · rfl

end UnitAddTorus

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {Γ : Subgroup (symplecticGroup l ℚ)} {N : ℕ}

variable (l N) in
/-- The point `N (A + Aᵀ) + i` of `ℋ_g`, for a real matrix `A` given by its entries `x`. -/
private noncomputable def torusPoint (x : l × l → ℝ) : SiegelUpperHalfSpace l where
  val := of (fun i j ↦ ((N * (x (i, j) + x (j, i)) : ℝ) : ℂ)) + I • 1
  transpose_val := by
    ext i j
    simp [one_apply, eq_comm, add_comm]
  posDef_im := by
    convert PosDef.one (n := l) (R := ℝ)
    ext i j
    simp [one_apply, apply_ite]

private lemma exp_trace_torusPoint (x : l × l → ℝ) {n : Matrix l l ℚ} (hn : nᵀ = n)
    {k : l × l → ℤ} (hk : ∀ p, (k p : ℚ) = 2 * N * n p.1 p.2) :
    cexp (2 * π * I * (n.map ((↑) : ℚ → ℂ) * (torusPoint l N x).val).trace) =
      mFourier k (fun p ↦ (x p : UnitAddCircle)) * cexp (-2 * π * n.trace) := by
  have hs (i j : l) : n j i = n i j := congrFun (congrFun hn i) j
  have hk' (p : l × l) : (k p : ℂ) = 2 * N * n p.1 p.2 := by exact_mod_cast hk p
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, ← Complex.exp_sum,
    ← Complex.exp_add]
  congr 1
  simp [torusPoint, trace, mul_apply, hk', Fintype.sum_prod_type, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  have h1 : ∑ a, ∑ b, 2 * π * I * ((n a b : ℂ) * (N * x (b, a))) =
      ∑ a, ∑ b, 2 * π * I * ((n a b : ℂ) * (N * x (a, b))) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ by rw [hs]
  have h2 : ∑ a, 2 * π * I * (I * (n a a : ℂ)) = -∑ a, 2 * π * (n a a : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by linear_combination (2 * π * (n a a : ℂ)) * I_sq
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine congrArg (· + _) (Finset.sum_congr rfl fun a _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ ↦ by ring1

private lemma exists_intCast_eq
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (n : dualLattice Γ) (p : l × l) : ∃ z : ℤ, (z : ℚ) = 2 * N * (n : Matrix l l ℚ) p.1 p.2 := by
  rcases n.2.2 _ (hΓ p.1 p.2) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hs : (n : Matrix l l ℚ) p.2 p.1 = (n : Matrix l l ℚ) p.1 p.2 :=
    congrFun (congrFun n.2.1 p.1) p.2
  rw [← hz, smul_mul, trace_smul, add_mul, trace_add, trace_single_mul, trace_single_mul, hs,
    one_smul, smul_eq_mul]
  ring1

/-- **Uniqueness of Siegel Fourier expansions**: if the translation lattice `L_Γ` contains
`N · Sym_g(ℤ)` with `N ≠ 0`, and `∑_{n ∈ L_Γ^∨} c(n) e^{2πi tr(nτ)} = 0` for every `τ ∈ ℋ_g`, the
sum converging unconditionally, then `c = 0`. -/
lemma eq_zero_of_hasSum_fourierExp (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    {c : dualLattice Γ → ℂ} (hc : ∀ τ, HasSum (fun n ↦ fourierExp n τ * c n) 0) : c = 0 := by
  choose k hk using exists_intCast_eq hΓ
  have hinj : Function.Injective k := fun n m h ↦ Subtype.ext <| ext fun i j ↦ by
    have h' : (k n (i, j) : ℚ) = 2 * N * (n : Matrix l l ℚ) i j := hk n (i, j)
    rw [h, hk m (i, j)] at h'
    exact (mul_right_injective₀ (by positivity : (2 * N : ℚ) ≠ 0) h').symm
  let d : (l × l → ℤ) → ℂ :=
    Function.extend k (fun n ↦ c n * cexp (-2 * π * (n : Matrix l l ℚ).trace)) 0
  have hd (x : l × l → ℝ) :
      HasSum (fun m ↦ d m * mFourier m (fun p ↦ (x p : UnitAddCircle))) 0 := by
    refine (hinj.hasSum_iff fun m hm ↦ ?_).mp ((hc (torusPoint l N x)).congr_fun fun n ↦ ?_)
    · rw [show d m = 0 from Function.extend_apply' _ _ _ hm, zero_mul]
    · rw [Function.comp_apply, show d (k n) = _ from hinj.extend_apply _ _ n, fourierExp,
        exp_trace_torusPoint x n.2.1 (hk n)]
      ring1
  have hd0 : d = 0 := by
    refine eq_zero_of_hasSum_mFourier (by simpa [mFourier] using (hd 0).summable) fun x ↦ ?_
    choose t ht using fun p ↦ QuotientAddGroup.mk_surjective (x p)
    exact (funext ht : (fun p ↦ (t p : UnitAddCircle)) = x) ▸ hd t
  funext n
  simpa [d, hinj.extend_apply] using congrFun hd0 (k n)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {f : SiegelUpperHalfSpace l → V}
    {a b : dualLattice Γ → V}

/-- **Fourier expansions are unique**: if the translation lattice `L_Γ` contains `N · Sym_g(ℤ)`
with `N ≠ 0`, two families of Fourier coefficients of the same `f : ℋ_g → V` are equal. -/
lemma HasSiegelFourierExpansion.unique (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    (ha : HasSiegelFourierExpansion Γ f a) (hb : HasSiegelFourierExpansion Γ f b) : a = b := by
  funext n
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  refine congrFun (eq_zero_of_hasSum_fourierExp hN hΓ (c := fun n ↦ φ (a n - b n)) fun τ ↦ ?_) n
  simpa [mul_sub] using (ha τ φ).sub (hb τ φ)

/-- The **Fourier coefficients** of `F : ℋ_g → ℂ` with a Fourier expansion `a` on `Γ` are the
values of `a`, if the translation lattice `L_Γ` contains `N · Sym_g(ℤ)` with `N ≠ 0`. -/
lemma fourierCoeffs_eq_range (hN : N ≠ 0)
    (hΓ : ∀ i j : l, (N : ℚ) • (single i j 1 + single j i 1) ∈ translationLattice Γ)
    {F : SiegelUpperHalfSpace l → ℂ} {a : dualLattice Γ → ℂ}
    (ha : HasSiegelFourierExpansion Γ F a) : fourierCoeffs Γ F = Set.range a := by
  ext z
  refine ⟨fun ⟨b, hb, n, hn⟩ ↦ ⟨n, ?_⟩, fun ⟨n, hn⟩ ↦ ⟨a, ha, n, hn⟩⟩
  rw [ha.unique hN hΓ hb, hn]

end SiegelUpperHalfSpace
