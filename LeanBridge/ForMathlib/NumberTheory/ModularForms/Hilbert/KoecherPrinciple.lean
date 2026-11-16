import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.FourierExistence
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeU
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# The Koecher principle for Hilbert modular forms

Let `F` be a totally real field of degree `n > 1` and `φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` a Fourier
series on `ℍⁿ` over the trace dual `(𝔟⁻¹)^∨` of an invertible fractional ideal, such as the
expansion of a component of a Hilbert modular form (LMFDB `mf.hilbert`, `mf.hilbert.q_expansion`).
Koecher's principle says that if `φ` transforms under the matrices `diag(1, ε)`, `ε` running over
the `M`-th powers of the totally positive units of `𝒪_F` for some `M ≠ 0`, then `a(ν) ≠ 0` only for
`ν = 0` and `ν` totally positive; then `φ` is bounded when all the imaginary parts are at least `1`.
This is why the LMFDB imposes no condition at the cusps in degree `n > 1`.

The transformation law under `diag(1, ε)`, which acts by `z ↦ z / ε` with a constant automorphy
factor `C`, and the uniqueness of Fourier expansions give `a(εν) = C a(ν)`. If `w₀(ν) < 0` at a real
place `w₀`, Dirichlet's unit theorem gives a unit `u` with `|w₀(u)| > 1` and `|w(u)| < 1` at the
other real places (there is one, as `n > 1`); take `ε = u^{2M}`. Along the orbit `ε^s ν`, the terms
of the Fourier series at `z = (i, …, i)` have absolute value `|C|^s |a(ν)| e^{-2π Tr(ε^s ν)}`, and
`-Tr(ε^s ν) ≥ |w₀(ν)| w₀(ε)^s - ∑_w |w(ν)|` grows exponentially: these terms do not tend to `0`
unless `a(ν) = 0`.

For a Hilbert modular form, `Γ₀(𝔑)_𝔟` contains `diag(1, ε)` for every totally positive unit `ε` and
the translations `z ↦ z + b`, `b ∈ 𝔟⁻¹`, so every component has a Fourier expansion, supported on
`0` and the totally positive `ν`. This discharges the hypothesis on Fourier expansions of the
comparison between Hecke eigenvalues and Fourier coefficients at narrow-principal primes.

## Main results

* `HilbertModularForm.HasHilbertFourierExpansion.boundedAtFilter`: a Fourier series supported on `0`
  and the totally positive `ν` is bounded as all the imaginary parts tend to infinity.
* `HilbertModularForm.HasHilbertFourierExpansion.tendsto_atImInfty`: it tends to its constant term.
* `HilbertModularForm.HasHilbertFourierExpansion.apply_mulUnit`: `a(εν) = C a(ν)` under the
  transformation law for `diag(1, ε)`, `ε` a totally positive unit.
* `HilbertModularForm.HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive`: Koecher's principle
  for Fourier series transforming under the `M`-th powers of the totally positive units.
* `HilbertModularForm.hasHilbertFourierExpansion_toFun` (LMFDB `mf.hilbert.q_expansion`): every
  component of a Hilbert modular form over a totally real field has a Fourier expansion.
* `HilbertModularForm.IsHeckeIdealEigenform.heckeIdealEigenvalueNormalised_eq_idealCoeff` and
  `HilbertModularForm.IsUEigenform.uEigenvalueNormalised_eq_idealCoeff` (LMFDB
  `mf.hilbert.q_expansion`, `mf.hilbert.eigenvalue`): the eigenvalues of `T_𝔭` and `U_𝔭` of a
  normalised eigenform at a prime `𝔭 = (ϖ)`, `ϖ` totally positive, are its Fourier coefficients.
* `HilbertModularForm.koecherPrinciple` (LMFDB `mf.hilbert`, `mf.hilbert.q_expansion`): the
  statement `HilbertModularForm.KoecherPrinciple` holds for every number field.
-/

open Asymptotics Complex Filter Matrix Module NumberField InfinitePlace HilbertModularGroup

open scoped nonZeroDivisors Real Topology UpperHalfPlane

namespace HilbertModularForm

variable {F : Type*} [Field F] {𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ} {𝔑 : Ideal (𝓞 F)} {u : (𝓞 F)ˣ}
  {M : ℕ} (𝔞 : FractionalIdeal (𝓞 F)⁰ F) (y : 𝔞) (s : ℕ) (b : F)
  (z : {w : InfinitePlace F // w.IsReal} → ℍ) (w : {w : InfinitePlace F // w.IsReal})

lemma isTotallyPositive_unitF_pow (hu : IsTotallyPositive (unitF u : F)) :
    IsTotallyPositive (unitF (u ^ M) : F) := by
  intro w hw
  rw [unitF, map_pow, Units.val_pow_eq_pow_val, map_pow]
  exact pow_pos (hu w hw) M

lemma coe_mulUnit : (mulUnit u 𝔞 y : F) = (unitF u : F) * y :=
  rfl

lemma coe_mulUnit_iterate : ((mulUnit u 𝔞)^[s] y : F) = (unitF u : F) ^ s * y := by
  induction s with
  | zero => simp
  | succ s ih => rw [Function.iterate_succ_apply', coe_mulUnit, ih, pow_succ', mul_assoc]

lemma coe_smul_heckeUpper_one :
    (smul (heckeUpper 1 b) z w : ℂ) = z w + embedding_of_isReal w.2 b := by
  rw [coe_smul_heckeUpper b z (by simp) w]
  simp

private lemma embedding_unitF_sq_pow :
    embedding_of_isReal w.2 (unitF ((u ^ 2) ^ M) : F) = (w.1 (algebraMap (𝓞 F) F u) ^ 2) ^ M := by
  rw [← norm_embedding_of_isReal w.2, Real.norm_eq_abs, sq_abs, unitF, map_pow, map_pow,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow]
  rfl

variable {b} in
lemma heckeUpper_one_mem_gammaZero (hb : b ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F)) :
    heckeUpper 1 b ∈ gammaZero (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 : _)) 𝔑 := by
  refine mem_gammaZero_of_apply_mem ?_ (fun y hy ↦ ?_) ?_ ?_ ?_ ?_
  · simp [heckeUpper]
  · have h : b * y ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F) * ↑𝔟 :=
      FractionalIdeal.mul_mem_mul hb hy
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, ← FractionalIdeal.mem_coe,
      FractionalIdeal.coe_one] at h
    simpa [heckeUpper] using h
  · simp [heckeUpper]
  · simp [heckeUpper]
  · rw [det_heckeUpper, Units.val_one, inv_one]
    exact Submodule.one_le.mp le_rfl
  · rw [det_heckeUpper, Units.val_one]
    exact isTotallyPositive_one

instance : (atImInfty : Filter ({w : InfinitePlace F // w.IsReal} → ℍ)).NeBot := by
  have h : Tendsto (fun (t : ℝ) (_ : {w : InfinitePlace F // w.IsReal}) ↦
      (⟨I * (max t 1 : ℝ), by simp⟩ : ℍ)) atTop atImInfty :=
    tendsto_comap_iff.mpr <| tendsto_pi.mpr fun _ ↦ by
      simpa using tendsto_atTop_mono (fun t ↦ le_max_left t 1) tendsto_id
  exact h.neBot

private lemma tendsto_mul_pow_add {α r β γ : ℝ} (hα : 0 < α) (hr : 1 < r) :
    Tendsto (fun s : ℕ ↦ α * r ^ s + β * s + γ) atTop atTop := by
  have h₁ : Tendsto (fun s : ℕ ↦ r ^ s) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hr
  have h₂ : Tendsto (fun s : ℕ ↦ α + β * ((s : ℝ) ^ 1 / r ^ s) + γ / r ^ s) atTop
      (𝓝 (α + β * 0 + 0)) :=
    (tendsto_const_nhds.add ((tendsto_pow_const_div_const_pow_of_one_lt 1 hr).const_mul β)).add
      (tendsto_const_nhds.div_atTop h₁)
  refine (h₁.atTop_mul_pos (by simpa using hα) h₂).congr fun s ↦ ?_
  have hs : r ^ s ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp

variable [NumberField F] {φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ} {a : fourierDual 𝔟 → ℂ}
  {k : {w : InfinitePlace F // w.IsReal} → ℤ} (hu : IsTotallyPositive (unitF u : F))
  {ν : fourierDual 𝔟}

lemma eventually_le_im (R : ℝ) :
    ∀ᶠ z in atImInfty, ∀ w : {w : InfinitePlace F // w.IsReal}, R ≤ (z w).im :=
  (eventually_pi fun _ ↦ eventually_ge_atTop R).comap _

open scoped Classical in
lemma norm_fourierExp (x : F) :
    ‖fourierExp x z‖ = Real.exp (-(2 * π * ∑ w, embedding_of_isReal w.2 x * (z w).im)) := by
  have e : 2 * π * I * ∑ w, (embedding_of_isReal w.2 x : ℂ) * (z w : ℂ) =
      ((2 * π : ℝ) : ℂ) * (I * ∑ w, (embedding_of_isReal w.2 x : ℂ) * (z w : ℂ)) := by
    push_cast
    ring1
  rw [fourierExp, Complex.norm_exp, e, re_ofReal_mul, I_mul_re, im_sum]
  simp only [im_ofReal_mul, UpperHalfPlane.coe_im, mul_neg]

variable {z} (ν) in
private lemma norm_mul_fourierExp_le
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) (hz : ∀ w, 1 ≤ (z w).im) :
    ‖a ν * fourierExp (ν : F) z‖ ≤ ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖ := by
  by_cases hν : a ν = 0
  · simp [hν]
  have hpos (w : {w : InfinitePlace F // w.IsReal}) : 0 ≤ embedding_of_isReal w.2 (ν : F) := by
    rcases hsupp ν hν with h | h
    · simp [h]
    · exact (h w.1 w.2).le
  rw [norm_mul, norm_mul, norm_fourierExp, norm_fourierExp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  simp only [UpperHalfPlane.I_im, mul_one, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ ↦
    le_mul_of_one_le_right (hpos w) (hz w)) Real.two_pi_pos.le

/-- **Fourier series supported on `0` and the totally positive `ν` are bounded at infinity**: if
`φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` with `a(ν) ≠ 0` only for `ν = 0` and `ν` totally positive, then `φ`
is bounded on `{z : Im z_w ≥ 1 for all w}`, by the sum of the `|a(ν)| e^{-2π Tr ν}`. -/
lemma HasHilbertFourierExpansion.boundedAtFilter (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) :
    BoundedAtFilter atImInfty φ := by
  have hs : Summable fun ν ↦ ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖ :=
    summable_norm_iff.mpr (ha _).summable
  refine IsBigO.of_bound (∑' ν, ‖a ν * fourierExp (ν : F) fun _ ↦ UpperHalfPlane.I‖) ?_
  filter_upwards [eventually_le_im 1] with z hz
  have hs' : Summable fun ν ↦ ‖a ν * fourierExp (ν : F) z‖ :=
    hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_mul_fourierExp_le · hsupp hz)
  rw [Pi.one_apply, norm_one, mul_one, ← (ha z).tsum_eq]
  exact (norm_tsum_le_tsum_norm hs').trans
    (hs'.tsum_le_tsum (norm_mul_fourierExp_le · hsupp hz) hs)

open scoped Classical in
private lemma tendsto_sum_mul_im {c : {w : InfinitePlace F // w.IsReal} → ℝ} (hc : ∀ w, 0 < c w)
    (w₀ : {w : InfinitePlace F // w.IsReal}) : Tendsto
      (fun z : {w : InfinitePlace F // w.IsReal} → ℍ ↦ ∑ w, c w * (z w).im) atImInfty atTop := by
  have h : Tendsto (fun (z : {w : InfinitePlace F // w.IsReal} → ℍ) w ↦ (z w).im) atImInfty
      (pi fun _ ↦ atTop) :=
    tendsto_comap
  exact tendsto_atTop_mono (fun z ↦ Finset.single_le_sum (fun w _ ↦
    (mul_pos (hc w) (z w).im_pos).le) (Finset.mem_univ w₀)) ((tendsto_pi.mp h w₀).const_mul_atTop
      (hc w₀))

variable [IsTotallyReal F] in
private lemma tendsto_mul_fourierExp (hν : IsTotallyPositive (ν : F)) :
    Tendsto (fun z ↦ a ν * fourierExp (ν : F) z) atImInfty (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  simp only [norm_mul, norm_fourierExp]
  simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp ((tendsto_sum_mul_im (fun w ↦ hν w.1 w.2)
    ⟨Classical.arbitrary (InfinitePlace F), IsTotallyReal.isReal _⟩).const_mul_atTop
      Real.two_pi_pos)).const_mul ‖a ν‖

variable [IsTotallyReal F] in
open scoped Classical in
/-- **The limit at infinity of a Fourier series supported on `0` and the totally positive `ν` is its
constant term**: if `φ(z) = ∑_ν a(ν) e^{2πi Tr(νz)}` with `a(ν) ≠ 0` only for `ν = 0` and `ν`
totally positive, then `φ(z) → a(0)` as all the imaginary parts tend to infinity (Tannery's
theorem, the terms being dominated by the `|a(ν)| e^{-2π Tr ν}`). -/
lemma HasHilbertFourierExpansion.tendsto_atImInfty (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hsupp : ∀ ν, a ν ≠ 0 → (ν : F) = 0 ∨ IsTotallyPositive (ν : F)) :
    Tendsto φ atImInfty (𝓝 (a ⟨0, (fourierDual 𝔟).zero_mem⟩)) := by
  have h : Tendsto (fun z ↦ ∑' ν, a ν * fourierExp (ν : F) z) atImInfty
      (𝓝 (∑' ν, if ν = ⟨0, (fourierDual 𝔟).zero_mem⟩ then a ν else 0)) :=
    tendsto_tsum_of_dominated_convergence (summable_norm_iff.mpr (ha _).summable) (fun ν ↦ ?_)
      ((eventually_le_im 1).mono fun _ hz ↦ (norm_mul_fourierExp_le · hsupp hz))
  · rw [tsum_ite_eq] at h
    exact h.congr fun z ↦ (ha z).tsum_eq
  · by_cases hν : ν = ⟨0, (fourierDual 𝔟).zero_mem⟩
    · simp [hν, fourierExp]
    rw [ite_eq_right hν]
    by_cases haν : a ν = 0
    · simp [haν]
    exact tendsto_mul_fourierExp <| (hsupp ν haν).resolve_left fun h ↦ hν (Subtype.ext h)

lemma automorphyFactor_heckeUpper_one : automorphyFactor k (heckeUpper 1 b) z = 1 := by
  simp [automorphyFactor, UpperHalfPlane.denom, mapGL, heckeUpper]

lemma slash_one : slash k 1 φ = φ := by
  funext z
  have hz : smul 1 z = z := funext fun w ↦ by rw [smul, map_one, one_smul]
  simp [slash, automorphyFactor, hz]

lemma isTranslationInvariant_of_slash_eq
    (h : ∀ b ∈ (↑𝔟⁻¹ : FractionalIdeal (𝓞 F)⁰ F), slash k (heckeUpper 1 b) φ = φ) :
    IsTranslationInvariant 𝔟 φ := by
  intro b hb z z' hz
  have hz' : z' = smul (heckeUpper 1 b) z :=
    funext fun w ↦ UpperHalfPlane.ext <| by rw [hz w, ← coe_smul_heckeUpper_one]
  rw [hz', ← congrFun (h b hb) z, slash, automorphyFactor_heckeUpper_one, inv_one, one_mul]

variable (ν) [IsTotallyReal F] in
/-- **The Fourier coefficients under a totally positive unit**: if `φ ∣ₖ diag(1, ε) = φ` for a
totally positive unit `ε` of `𝒪_F`, then `a(εν) = C a(ν)`, `C` being the automorphy factor of
`diag(1, ε)`, which does not depend on the point. -/
lemma HasHilbertFourierExpansion.apply_mulUnit (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hφ : slash k (heckeDiagonal (unitF u) hu) φ = φ) : a (mulUnit u _ ν) =
      automorphyFactor k (heckeDiagonal (unitF u) hu) (fun _ ↦ UpperHalfPlane.I) * a ν := by
  have hC : automorphyFactor k (heckeDiagonal (unitF u) hu) (fun _ ↦ UpperHalfPlane.I) ≠ 0 :=
    automorphyFactor_ne_zero _ _ _ (by rwa [det_heckeDiagonal])
  have h₁ : HasHilbertFourierExpansion 𝔟
      (automorphyFactor k (heckeDiagonal (unitF u) hu) (fun _ ↦ UpperHalfPlane.I) • φ)
      (a ∘ mulUnit u _) := fun z ↦ by
    have hz : HasSum (fun ν ↦ a ν * fourierExp (ν : F)
        (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z))
        (φ (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z)) :=
      ha (smul (heckeDiagonal (unitF u) hu : GL (Fin 2) F) z)
    have hφz : slash k (heckeDiagonal (unitF u) hu) φ z = φ z := congrFun hφ z
    rw [slash_heckeDiagonal, inv_mul_eq_iff_eq_mul₀ hC] at hφz
    rw [hφz] at hz
    refine (mulUnit u _).symm.hasSum_iff.mp ?_
    convert hz using 1
    funext μ
    simp [mulUnit, unitF_mul_unitF_inv_mul, fourierExp_smul_heckeDiagonal]
  exact congrFun (h₁.unique 𝔟 (ha.const_smul 𝔟 _)) ν

variable (ν) [IsTotallyReal F] in
lemma HasHilbertFourierExpansion.apply_mulUnit_iterate (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hφ : slash k (heckeDiagonal (unitF u) hu) φ = φ) : a ((mulUnit u _)^[s] ν) =
      automorphyFactor k (heckeDiagonal (unitF u) hu) (fun _ ↦ UpperHalfPlane.I) ^ s * a ν := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ha.apply_mulUnit hu _ hφ, ih, pow_succ', mul_assoc]

variable (w₀ : {w : InfinitePlace F // w.IsReal})

variable {w₀} [IsTotallyReal F] in
open scoped Classical in
private lemma HasHilbertFourierExpansion.eq_zero_of_unit (ha : HasHilbertFourierExpansion 𝔟 φ a)
    (hφ : slash k (heckeDiagonal (unitF u) hu) φ = φ)
    (hu₀ : 1 < embedding_of_isReal w₀.2 (unitF u : F))
    (hu₁ : ∀ w ≠ w₀, embedding_of_isReal w.2 (unitF u : F) < 1)
    (hν : embedding_of_isReal w₀.2 (ν : F) < 0) : a ν = 0 := by
  by_contra haν
  let C : ℂ := automorphyFactor k (heckeDiagonal (unitF u) hu) fun _ ↦ UpperHalfPlane.I
  let z₀ : {w : InfinitePlace F // w.IsReal} → ℍ := fun _ ↦ UpperHalfPlane.I
  let T : fourierDual 𝔟 → ℝ := fun μ ↦
    ∑ w : {w : InfinitePlace F // w.IsReal}, embedding_of_isReal w.2 (μ : F)
  let β : ℝ := ∑ w : {w : InfinitePlace F // w.IsReal}, |embedding_of_isReal w.2 (ν : F)|
  have hC : 0 < ‖C‖ :=
    norm_pos_iff.mpr <| automorphyFactor_ne_zero _ _ _ (by rwa [det_heckeDiagonal])
  have haν' : 0 < ‖a ν‖ := norm_pos_iff.mpr haν
  have hnorm (μ : fourierDual 𝔟) :
      ‖a μ * fourierExp (μ : F) z₀‖ = ‖a μ‖ * Real.exp (-(2 * π * T μ)) := by
    rw [norm_mul, norm_fourierExp]
    simp [z₀, T]
  have hfin : {μ | 1 ≤ ‖a μ * fourierExp (μ : F) z₀‖}.Finite := by
    have h : ∀ᶠ μ in cofinite, ‖a μ * fourierExp (μ : F) z₀‖ < 1 :=
      (ha z₀).summable.tendsto_cofinite_zero.norm.eventually (gt_mem_nhds (by simp))
    simpa using eventually_cofinite.mp h
  rcases (hfin.image T).bddBelow with ⟨B, hB⟩
  have hT (s : ℕ) : T ((mulUnit u _)^[s] ν) ≤
      embedding_of_isReal w₀.2 (ν : F) * embedding_of_isReal w₀.2 (unitF u : F) ^ s + β := by
    have h₁ : T ((mulUnit u _)^[s] ν) = ∑ w : {w : InfinitePlace F // w.IsReal},
        embedding_of_isReal w.2 (unitF u : F) ^ s * embedding_of_isReal w.2 (ν : F) := by
      simp only [T, coe_mulUnit_iterate, map_mul, map_pow]
    rw [h₁, ← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)]
    refine add_le_add (mul_comm _ _).le <| (Finset.sum_le_sum fun w hw ↦ ?_).trans <|
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ ↦ abs_nonneg _
    have h₀ : 0 < embedding_of_isReal w.2 (unitF u : F) := hu w.1 w.2
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg h₀.le s)).trans <|
      mul_le_of_le_one_left (abs_nonneg _) <|
        pow_le_one₀ h₀.le (hu₁ w (Finset.ne_of_mem_erase hw)).le
  rcases ((tendsto_mul_pow_add (β := 0) (γ := -β) (neg_pos.mpr hν) hu₀).eventually_ge_atTop
    (-B + 1)).and ((tendsto_mul_pow_add (β := Real.log ‖C‖) (γ := Real.log ‖a ν‖ - 2 * π * β)
      (mul_pos Real.two_pi_pos (neg_pos.mpr hν)) hu₀).eventually_ge_atTop 0) |>.exists with
    ⟨s, hs₁, hs₂⟩
  have hTs : 2 * π * T ((mulUnit u _)^[s] ν) ≤ 2 * π *
      (embedding_of_isReal w₀.2 (ν : F) * embedding_of_isReal w₀.2 (unitF u : F) ^ s + β) :=
    mul_le_mul_of_nonneg_left (hT s) Real.two_pi_pos.le
  have hmem : 1 ≤ ‖a ((mulUnit u _)^[s] ν) * fourierExp (((mulUnit u _)^[s] ν : _) : F) z₀‖ := by
    rw [hnorm, ha.apply_mulUnit_iterate _ hu _ hφ, norm_mul, norm_pow,
      ← Real.exp_log hC, ← Real.exp_nat_mul, ← Real.exp_log haν', ← Real.exp_add, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hBs : B ≤ T ((mulUnit u _)^[s] ν) := hB ⟨_, hmem, rfl⟩
  linarith [hT s]

variable [IsTotallyReal F] in
open scoped Classical in
open Units dirichletUnitTheorem in
private lemma exists_unit_one_lt (hF : 1 < finrank ℚ F) :
    ∃ u : (𝓞 F)ˣ, 1 < w₀.1 (algebraMap (𝓞 F) F u) ∧ ∀ w ≠ w₀.1, w (algebraMap (𝓞 F) F u) < 1 := by
  rcases exists_unit F w₀.1 with ⟨u, hu⟩
  refine ⟨u, ?_, fun w hw ↦ (Real.log_neg_iff (Units.pos_at_place u w)).mp (hu w hw)⟩
  rw [IsTotallyReal.finrank] at hF
  rcases Fintype.exists_ne_of_one_lt_card hF w₀ with ⟨w₁, hw₁⟩
  have hneg :
      ∑ w ∈ Finset.univ.erase w₀.1, (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) < 0 :=
    Finset.sum_neg (fun w hw ↦ mul_neg_of_pos_of_neg (Nat.cast_pos.mpr mult_pos)
      (hu w (Finset.ne_of_mem_erase hw)))
      ⟨w₁.1, Finset.mem_erase.mpr ⟨fun h ↦ hw₁ (Subtype.ext h), Finset.mem_univ _⟩⟩
  have hsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) = 0 :=
    Units.sum_mult_mul_log u
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀.1)] at hsum
  exact (Real.log_pos_iff (Units.pos_at_place u w₀.1).le).mp <|
    pos_of_mul_pos_right (by linarith) (Nat.cast_nonneg _)

variable [IsTotallyReal F] in
private lemma exists_isTotallyPositive_unit (hF : 1 < finrank ℚ F) (hM : M ≠ 0) :
    ∃ v : (𝓞 F)ˣ, IsTotallyPositive (unitF v : F) ∧
      1 < embedding_of_isReal w₀.2 (unitF (v ^ M) : F) ∧
        ∀ w ≠ w₀, embedding_of_isReal w.2 (unitF (v ^ M) : F) < 1 := by
  rcases exists_unit_one_lt w₀ hF with ⟨u, hu₀, hu₁⟩
  refine ⟨u ^ 2, mem_totallyPositiveIntegerUnits.mp (sq_mem_totallyPositiveIntegerUnits u), ?_,
    fun w hw ↦ ?_⟩
  · rw [embedding_unitF_sq_pow]
    exact one_lt_pow₀ (one_lt_pow₀ hu₀ two_ne_zero) hM
  · rw [embedding_unitF_sq_pow]
    exact pow_lt_one₀ (sq_nonneg _) (pow_lt_one₀ (Units.pos_at_place u w.1).le
      (hu₁ w.1 fun h ↦ hw (Subtype.ext h)) two_ne_zero) hM

variable [IsTotallyReal F] in
/-- **Koecher's principle**: for `F` totally real of degree `> 1`, if
`φ(z) = ∑_{ν ∈ (𝔟⁻¹)^∨} a(ν) e^{2πi Tr(νz)}` and `φ ∣ₖ diag(1, ε^M) = φ` for every totally positive
unit `ε` of `𝒪_F`, for some `M ≠ 0`, then every `ν` with `a(ν) ≠ 0` is `0` or totally positive. -/
lemma HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive (hF : 1 < finrank ℚ F)
    (ha : HasHilbertFourierExpansion 𝔟 φ a) (hM : M ≠ 0)
    (hφ : ∀ (v : (𝓞 F)ˣ) (hv : IsTotallyPositive (unitF v : F)),
      slash k (heckeDiagonal (unitF (v ^ M)) (isTotallyPositive_unitF_pow hv)) φ = φ)
    (hν : a ν ≠ 0) : (ν : F) = 0 ∨ IsTotallyPositive (ν : F) := by
  refine or_iff_not_imp_left.mpr fun hν₀ w₀ hw₀ ↦ ?_
  by_contra hneg
  rcases exists_isTotallyPositive_unit ⟨w₀, hw₀⟩ hF hM with ⟨v, hv, h₀, h₁⟩
  exact hν <| ha.eq_zero_of_unit (isTotallyPositive_unitF_pow hv) (hφ v hv) h₀ h₁ <|
    (not_lt.mp hneg).lt_of_ne ((map_ne_zero _).mpr hν₀)

variable {𝔠 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔠 : ∀ c, NarrowClassGroup.mk (𝔠 c) = c} {ψ : HilbertModularForm 𝔑 k 𝔠 h𝔠} {m : ℤ}
  {𝔭 : (Ideal (𝓞 F))⁰} {ϖ : Fˣ}

variable (ψ) [IsTotallyReal F] in
/-- **The components of a Hilbert modular form have Fourier expansions** (LMFDB
`mf.hilbert.q_expansion`): for `F` totally real, every component `f_c` of a Hilbert modular form
(LMFDB `mf.hilbert`) is the sum `f_c(z) = ∑_ν a_c(ν) e^{2πi Tr(νz)}` of its Fourier series over
`(𝔟_c⁻¹)^∨ = 𝔟_c 𝔡⁻¹`, its translations in `Γ₀(𝔑)_{𝔟_c}` being those by `𝔟_c⁻¹`. -/
lemma hasHilbertFourierExpansion_toFun (c : NarrowClassGroup F) :
    HasHilbertFourierExpansion (𝔠 c) (ψ.toFun c) (fourierCoeff (𝔠 c) (ψ.toFun c)) :=
  hasHilbertFourierExpansion_fourierCoeff _ (ψ.isHolomorphic c) <|
    isTranslationInvariant_of_slash_eq fun _ hb ↦
      ψ.toFun_mem_slashInvariants c _ (heckeUpper_one_mem_gammaZero hb)

variable [IsTotallyReal F] [NeZero 𝔑] in
/-- **The `T_𝔭`-eigenvalues of a normalised eigenform are its Fourier coefficients** (LMFDB
`mf.hilbert.q_expansion`, `mf.hilbert.eigenvalue`), with no hypothesis on Fourier expansions: for
`F` totally real, a normalised Hecke eigenform `ψ` of parallel weight `m` and a prime `𝔭 = (ϖ)`,
`ϖ` totally positive, with `𝔭 + 𝔑 = 𝒪_F`, the normalised eigenvalue of `T_𝔭` is `a_𝔭`. -/
lemma IsHeckeIdealEigenform.heckeIdealEigenvalueNormalised_eq_idealCoeff (hk : ∀ w, k w = m)
    (hψ : ψ.IsHeckeIdealEigenform) (hn : ψ.IsNormalised) (h𝔭 : (𝔭 : Ideal (𝓞 F)).IsPrime)
    (h𝔭𝔑 : (𝔭 : Ideal (𝓞 F)) ⊔ 𝔑 = ⊤) (hϖ : IsTotallyPositive (ϖ : F))
    (hϖ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (ϖ : F) =
      ((𝔭 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) :
    heckeIdealEigenvalueNormalised m 𝔭 hψ h𝔭𝔑 = ψ.idealCoeff 𝔭 :=
  heckeIdealEigenvalueNormalised_eq_idealCoeff_of_isPrime hk hψ hn
    (fun c ↦ ⟨_, ψ.hasHilbertFourierExpansion_toFun c⟩) h𝔭 h𝔭𝔑 hϖ hϖ𝔭

variable [IsTotallyReal F] [NeZero 𝔑] in
/-- **The `U_𝔭`-eigenvalues of a normalised eigenform are its Fourier coefficients** (LMFDB
`mf.hilbert.q_expansion`, `mf.hilbert.eigenvalue`), with no hypothesis on Fourier expansions: for
`F` totally real, a normalised eigenform `ψ` of the `U_𝔭` of parallel weight `m` and a prime
`𝔭 = (ϖ) ⊇ 𝔑`, `ϖ` totally positive, the normalised eigenvalue of `U_𝔭` is `a_𝔭`. -/
lemma IsUEigenform.uEigenvalueNormalised_eq_idealCoeff (hk : ∀ w, k w = m) (hψ : ψ.IsUEigenform)
    (hn : ψ.IsNormalised) (h𝔭 : (𝔭 : Ideal (𝓞 F)).IsPrime) (h𝔑𝔭 : 𝔑 ≤ 𝔭)
    (hϖ : IsTotallyPositive (ϖ : F)) (hϖ𝔭 : FractionalIdeal.spanSingleton (𝓞 F)⁰ (ϖ : F) =
      ((𝔭 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) :
    uEigenvalueNormalised 𝔭 m hψ h𝔭 h𝔑𝔭 = ψ.idealCoeff 𝔭 :=
  HilbertModularForm.uEigenvalueNormalised_eq_idealCoeff hk hψ hn
    ⟨_, ψ.hasHilbertFourierExpansion_toFun _⟩ h𝔭 h𝔑𝔭 hϖ hϖ𝔭

/-- **The Koecher principle for Hilbert modular forms** (LMFDB `mf.hilbert`,
`mf.hilbert.q_expansion`): for `F` totally real of degree `> 1`, every Fourier coefficient
`a(ν) ≠ 0` of a component of a Hilbert modular form has `ν = 0` or `ν` totally positive, by
`HilbertModularForm.HasHilbertFourierExpansion.eq_zero_or_isTotallyPositive` with `M = 1`: the
matrices `diag(1, ε)`, `ε` a totally positive unit, lie in `Γ₀(𝔑)_𝔟`. -/
lemma koecherPrinciple : KoecherPrinciple F :=
  fun _ hF _ _ _ _ f c _ ha _ hν ↦ ha.eq_zero_or_isTotallyPositive hF one_ne_zero
    (fun _ hv ↦ f.toFun_mem_slashInvariants c _
      (heckeDiagonal_mem_gammaZero (isTotallyPositive_unitF_pow hv))) hν

end HilbertModularForm
