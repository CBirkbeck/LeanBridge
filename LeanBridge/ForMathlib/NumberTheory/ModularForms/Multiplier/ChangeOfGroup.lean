import LeanBridge.ForMathlib.NumberTheory.ModularForms.Gamma1Index
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ModularForm
import Mathlib.NumberTheory.ModularForms.NormTrace
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.QExpansion
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion
import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform
import TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# New modular forms from given ones: changing and enlarging the group

This file proves the ways of creating new modular forms from given ones that change the group on
which they are modular (LMFDB `mf.gl2.history.new`).

* **Dilation.** If `f` is a modular form of weight `k` and multiplier system `v` on `Γ`, and `α`
  has positive determinant, then `f ∣[k] α` is a modular form of weight `k` on `α⁻¹ Γ α`, with
  multiplier system `δ ↦ v(α δ α⁻¹)`. For `α = diag(m, 1)` with `m ∈ ℚ` positive this is, up to a
  constant, `z ↦ f(mz)`, and `α⁻¹ Γ α` is arithmetic if `Γ` is. The LMFDB allows every
  `m ∈ ℚ^×`, but `mz` lies in the upper half-plane only for `m > 0`.
* **Sub-series and twists.** If `f = ∑ aₙ q^(n/N)` is a modular form on `Γ`, where `q^(1/N)` is
  `e^(2πiz/N)` and `N` is a strict period of `Γ`, and `ψ` is a function on `ℤ / M`, then
  `∑ ψ(n) aₙ q^(n/N)` is the modular form `M⁻¹ ∑_{a mod M} 𝓕ψ(a) f(z + aN/M)` on the intersection
  of the conjugates of `Γ` by the translations by `aN/M`, which is arithmetic if `Γ` is. For the
  indicator function of `r` this is the sub-series `∑_{n ≡ r (M)} aₙ q^(n/N)`. On `Γ₁(N)`, with
  `q = e^(2πiz)`, Tau Ceti's `ModularForm.twist` is this twist as a form on `Γ₁(L)` for an explicit
  `L`. The same sum of translates twists a function that is only invariant under the weight `k`
  action of `Γ`, with any expansion `∑_{n ∈ ℤ} aₙ q^(n/N)`: this covers poles at the cusp, that
  is, expansions over `n ≥ n₀` with `n₀ < 0`. It is holomorphic if `f` is.
* **Traces.** If `f` is a modular form on `H` and `G = ⨆ᵢ (H ∩ G) γᵢ` is a finite disjoint union,
  then `∑ᵢ f ∣[k] γᵢ` is Mathlib's trace `ModularForm.trace`, a modular form on `G`.
* **Hecke operators.** Tau Ceti's Hecke operator `T_p` on `Γ₁(N)` is the trace of the translate by
  `diag(1, p)`, so it combines the two methods. For a modular form `f` of weight `k` on
  `SL(2, ℤ)` and a prime `p`, `T_p f = (∑_{j < p} f((z + j)/p) + p^k f(pz)) / p`. Here `z ↦ f(pz)`
  is a modular form on `Γ₀(p)` (Tau Ceti's `ModularForm.levelRaise`) and `z ↦ f((z + j)/p)` is
  `p^k` times its translate by `S T^j`, a modular form on the conjugate `(S T^j)⁻¹ Γ₀(p) S T^j`.
  None of them is modular on `SL(2, ℤ)` in general: `Δ(pz)` is not invariant under `S`, and
  `Δ((z + j)/p)` is not invariant under `T`. The LMFDB says that the functions `f((z + j)/p)` are
  modular on `Γ₀(p)` as well, which fails for the same reason, since `T ∈ Γ₀(p)`.

## Main definitions

* `ModularForm.conjMultiplier`: the multiplier system `δ ↦ v(α δ α⁻¹)` on `α⁻¹ Γ α`.
* `ModularForm.dilationGL`: the matrix `diag(m, 1)` for a nonzero rational `m`.
* `ModularForm.twistLevel`: the intersection of the conjugates of `Γ` by the translations by
  `aN/M`.
* `ModularForm.twistOfWidth`: the twist `∑ ψ(n) aₙ q^(n/N)` of a modular form on `Γ`.
* `SlashInvariantForm.twistOfWidth`: the twist of a function invariant under the weight `k` action
  of `Γ`.
* `HeckeRing.GL2.upperTriTranslate`: `z ↦ f((z + j)/p)` as a modular form on a conjugate of
  `Γ₀(p)`, for `f` of level `1`.

## Main results

* `ModularForm.slash_mem_multiplierSpace`: `f ∣[k] α` is a modular form on `α⁻¹ Γ α`.
* `ModularForm.coe_dilationGL_smul`: `diag(m, 1)` acts by `z ↦ mz` for `m > 0`.
* `ModularForm.comp_dilationGL_smul_mem_multiplierSpace`: `z ↦ f(mz)` is a modular form on
  `diag(m, 1)⁻¹ Γ diag(m, 1)`.
* `ModularForm.qExpansion_twistOfWidth_coeff`: the coefficients of the twist are `ψ(n) aₙ`.
* `ModularForm.qExpansion_twistOfWidth_single_coeff`: the coefficients of the sub-series.
* `SlashInvariantForm.hasSum_twistOfWidth`: the twist of `∑_{n ∈ ℤ} aₙ q^(n/N)` is
  `∑_{n ∈ ℤ} ψ(n) aₙ q^(n/N)`.
* `ModularForm.sum_slash_eq_trace`: `∑ᵢ f ∣[k] γᵢ` is the trace of `f`.
* `HeckeRing.GL2.Gamma0_map_le_conjAct_scaleGL_one`: `diag(p, 1)` conjugates `Γ₀(p)` into
  `SL(2, ℤ)`, so that `z ↦ f(pz)` is modular on `Γ₀(p)`.
* `HeckeRing.GL2.upperTriTranslate_apply`: the values of `upperTriTranslate`.
* `HeckeRing.GL2.heckeTNat_apply_of_level_one`:
  `T_p f = (∑_{j < p} f((z + j)/p) + p^k f(pz)) / p` at level `1`.
* `HeckeRing.GL2.heckeTNat_eq_trace_translate`: `T_p` is the trace of the translate by
  `diag(1, p)`.
* `HeckeRing.GL2.qExpansion_coeff_one_eq_zero_of_slash_upperTriTranslate`,
  `HeckeRing.GL2.not_forall_slash_upperTriTranslate_discriminant`: `z ↦ f((z + j)/p)` is invariant
  under `T` only if the first Fourier coefficient of `f` vanishes, so `Δ((z + j)/p)` is not modular
  on `Γ₀(p)`.
* `HeckeRing.GL2.qExpansion_coeff_one_eq_zero_of_slash_levelRaise`,
  `HeckeRing.GL2.not_slash_levelRaise_discriminant`: `z ↦ f(pz)` is invariant under `S` only if the
  first Fourier coefficient of `f` vanishes, so `Δ(pz)` is not modular on `SL(2, ℤ)`.

## References

* H. Cohen and F. Strömberg, *Modular forms: a classical approach*, Graduate Studies in
  Mathematics 179, AMS, 2017.
* F. Diamond and J. Shurman, *A first course in modular forms*, GTM 228, Springer, 2005, §5.2.
-/

open UpperHalfPlane hiding I

open Complex CongruenceSubgroup ConjAct Function HeckeRing GL2 GLn Matrix GeneralLinearGroup
  ModularForm ModularGroup OnePoint SpecialLinearGroup Subgroup TauCeti ZMod

open scoped Manifold MatrixGroups ModularForm Pointwise Real

local notation "𝕢" => Periodic.qParam

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {v : Γ →* Circle} {k : ℤ} {f : ℍ → ℂ} {α : GL (Fin 2) ℝ}
  (m : ℚˣ) {M N : ℕ} (Φ : ZMod M → ℂ) (F : ModularForm Γ k) {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
  [𝒢.IsFiniteRelIndex ℋ] (G : ModularForm 𝒢 k) {ι : Type*} [Fintype ι] {δ : ι → ℋ}

variable (v α) in
/-- The **conjugate multiplier system** `δ ↦ v(α δ α⁻¹)` on the conjugate `α⁻¹ Γ α` of `Γ`: the
multiplier system of `f ∣[k] α` when `f` has multiplier system `v`. -/
noncomputable def conjMultiplier : (toConjAct α⁻¹ • Γ : Subgroup (GL (Fin 2) ℝ)) →* Circle :=
  v.comp (equivSMul (toConjAct α⁻¹) Γ).symm.toMonoidHom

variable [Γ.HasDetOne] in
/-- **Translating a modular form with multiplier**: if `f` is a modular form of weight `k` and
multiplier system `v` on `Γ` and `α` has positive determinant, then `f ∣[k] α` is a modular form of
weight `k` on `α⁻¹ Γ α` with multiplier system `δ ↦ v(α δ α⁻¹)`. For `v = 1` this is Mathlib's
`ModularForm.translate`. -/
lemma slash_mem_multiplierSpace (hf : f ∈ multiplierSpace k v) (hα : 0 < α.val.det) :
    f ∣[k] α ∈ multiplierSpace k (conjMultiplier v α) := by
  refine ⟨hf.1.slash k α, fun δ ↦ ?_, fun {c} hc ↦ ?_⟩
  · have h : ((equivSMul (toConjAct α⁻¹) Γ).symm δ : GL (Fin 2) ℝ) =
        (toConjAct α⁻¹)⁻¹ • (δ : GL (Fin 2) ℝ) :=
      equivSMul_symm_apply_coe (toConjAct α⁻¹) Γ δ
    have hδ : α * δ = ((equivSMul (toConjAct α⁻¹) Γ).symm δ : GL (Fin 2) ℝ) * α := by
      rw [h, ← map_inv, inv_inv, toConjAct_smul, inv_mul_cancel_right]
    rw [← SlashAction.slash_mul, hδ, SlashAction.slash_mul, hf.2.1, smul_slash_of_det_pos k hα]
    rfl
  · refine IsBoundedAt.smul_iff.mp (hf.2.2 ?_)
    simpa using hc.smul α

/-- The matrix `diag(m, 1)` of `GL(2, ℝ)` for a nonzero rational number `m`. For `m > 0` it acts on
the upper half-plane by `z ↦ mz`. -/
noncomputable def dilationGL : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (Rat.castHom ℝ) (diagGL ![m, 1])

lemma val_det_dilationGL : (dilationGL m).val.det = m := by
  simp [dilationGL]

lemma val_det_dilationGL_pos (hm : 0 < (m : ℚ)) : 0 < (dilationGL m).val.det :=
  (val_det_dilationGL m).symm ▸ Rat.cast_pos.mpr hm

/-- **The matrix `diag(m, 1)` acts by `z ↦ mz`**, for a positive rational number `m`. -/
lemma coe_dilationGL_smul (hm : 0 < (m : ℚ)) (z : ℍ) : ((dilationGL m • z : ℍ) : ℂ) = m * z := by
  rw [coe_smul_of_det_pos ((val_det_dilationGL_pos m hm).trans_eq (val_det_apply _).symm)]
  simp [dilationGL, num, denom]

variable [Γ.HasDetOne] in
/-- **Dilating a modular form** (LMFDB `mf.gl2.history.new`): if `f` is a modular form of weight
`k` and multiplier system `v` on `Γ` and `m` is a positive rational number, then `z ↦ f(mz)` is a
modular form of weight `k` on `α⁻¹ Γ α`, where `α = diag(m, 1)`, with multiplier system
`δ ↦ v(α δ α⁻¹)`. This group is arithmetic if `Γ` is. The LMFDB allows every `m ∈ ℚ^×`, but
`mz` lies in the upper half-plane only for `m > 0`. -/
lemma comp_dilationGL_smul_mem_multiplierSpace (hf : f ∈ multiplierSpace k v) (hm : 0 < (m : ℚ)) :
    (fun z ↦ f (dilationGL m • z)) ∈ multiplierSpace k (conjMultiplier v (dilationGL m)) := by
  have hα : 0 < (dilationGL m).val.det := val_det_dilationGL_pos m hm
  have h : (fun z ↦ f (dilationGL m • z)) = ((m : ℚ) : ℂ) ^ (1 - k) • (f ∣[k] dilationGL m) := by
    ext z
    have hd : denom (dilationGL m) z ^ (-k) = 1 := by
      simp [dilationGL, denom]
    rw [Pi.smul_apply, slash_apply_of_det_pos k hα, val_det_apply, val_det_dilationGL, hd, mul_one,
      abs_of_pos (Rat.cast_pos.mpr hm), ofReal_ratCast, smul_eq_mul, mul_left_comm,
      ← zpow_add₀ (by exact_mod_cast m.ne_zero), sub_add_sub_cancel, sub_self, zpow_zero, mul_one]
  exact h ▸ Submodule.smul_mem _ _ (slash_mem_multiplierSpace hf hα)

instance [Γ.IsArithmetic] : (toConjAct (dilationGL m)⁻¹ • Γ).IsArithmetic := by
  rw [dilationGL, ← map_inv]
  exact IsArithmetic.conj Γ _

variable (Γ M N) in
/-- The **level of a twist**: the intersection of the conjugates of `Γ` by the translations
`z ↦ z + aN/M` for `a` modulo `M`, on which the twists by functions modulo `M` of the modular
forms on `Γ` with expansions in `q^(1/N)` are modular. -/
noncomputable def twistLevel : Subgroup (GL (Fin 2) ℝ) :=
  ⨅ a : ZMod M, toConjAct (upperRightHom ((a.val : ℝ) * N / M))⁻¹ • Γ

variable (Γ M N) in
lemma twistLevel_le (a : ZMod M) :
    twistLevel Γ M N ≤ toConjAct (upperRightHom ((a.val : ℝ) * N / M))⁻¹ • Γ :=
  iInf_le _ a

instance [Γ.HasDetOne] : (twistLevel Γ M N).HasDetOne :=
  ⟨fun hg ↦ HasDetOne.det_eq (twistLevel_le Γ M N 0 hg)⟩

private lemma isArithmetic_iInf {I : Type*} [Finite I] [Nonempty I]
    {H : I → Subgroup (GL (Fin 2) ℝ)} (hH : ∀ i, (H i).IsArithmetic) : (⨅ i, H i).IsArithmetic := by
  have : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex (H (Classical.arbitrary I)) :=
    (hH _).is_commensurable.2
  exact ⟨⟨relIndex_iInf_ne_zero fun i ↦ (hH i).is_commensurable.1.relIndex_ne_zero⟩,
    isFiniteRelIndex_of_le_right _ (iInf_le H (Classical.arbitrary I))⟩

instance [NeZero M] [Γ.IsArithmetic] : (twistLevel Γ M N).IsArithmetic := by
  refine isArithmetic_iInf fun a ↦ ?_
  have h : upperRightHom ((a.val : ℝ) * N / M) =
      GeneralLinearGroup.map (Rat.castHom ℝ) (upperRightHom ((a.val : ℚ) * N / M)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [-natCast_val]
  rw [h, ← map_inv]
  exact IsArithmetic.conj Γ _

lemma natCast_mem_strictPeriods_twistLevel (hΓ : (N : ℝ) ∈ Γ.strictPeriods) :
    (N : ℝ) ∈ (twistLevel Γ M N).strictPeriods := by
  rw [mem_strictPeriods_iff] at hΓ ⊢
  refine mem_iInf.mpr fun a ↦ ?_
  rwa [map_inv, Γ.mem_inv_pointwise_smul_iff, toConjAct_smul, ← upperRightHom.map_add_eq_mul,
    add_comm, upperRightHom.map_add_eq_mul, mul_inv_cancel_right]

variable [NeZero M] in
private lemma hasSum_twist {κ : Type*} (e : κ → ℤ) {c : κ → ℂ} (hN : N ≠ 0)
    (hf : ∀ τ : ℍ, HasSum (fun i ↦ c i * 𝕢 N τ ^ e i) (f τ)) (τ : ℍ) :
    HasSum (fun i ↦ Φ (e i) * c i * 𝕢 N τ ^ e i)
      ((M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * f (((a.val : ℝ) * N / M) +ᵥ τ)) := by
  have hinv (r : ZMod M) : Φ r = (M : ℂ)⁻¹ * ∑ a, 𝓕 Φ a * stdAddChar (a * r) := by
    conv_lhs => rw [← LinearEquiv.symm_apply_apply dft Φ]
    simp [ZMod.invDFT_apply, mul_comm]
  have hq (a : ZMod M) (r : ℤ) : 𝕢 N ((((a.val : ℝ) * N / M) +ᵥ τ : ℍ) : ℂ) ^ r =
      stdAddChar (a * (r : ZMod M)) * 𝕢 N (τ : ℂ) ^ r := by
    have har : a * (r : ZMod M) = ((a.val * r : ℤ) : ZMod M) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [har, ZMod.stdAddChar_coe, coe_vadd, Periodic.qParam, Periodic.qParam,
      ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  refine ((hasSum_sum fun a _ ↦ (hf (((a.val : ℝ) * N / M) +ᵥ τ)).mul_left (𝓕 Φ a)).mul_left
    (M : ℂ)⁻¹).congr_fun fun i ↦ ?_
  rw [hinv, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hq]
  ring1

variable [Γ.HasDetOne] [NeZero M] (N) in
/-- The **twist** `∑ ψ(n) aₙ q^(n/N)` of a modular form `f = ∑ aₙ q^(n/N)` on `Γ` by a function `ψ`
modulo `M` (LMFDB `mf.gl2.history.new`): the modular form `M⁻¹ ∑_{a mod M} 𝓕ψ(a) f(z + aN/M)` on
`twistLevel Γ M N`, where `𝓕ψ` is the discrete Fourier transform of `ψ`. Its expansion in
`q^(1/N) = e^(2πiz/N)` is computed in `qExpansion_twistOfWidth_coeff`. On `Γ₁(N)`, Tau Ceti's
`ModularForm.twist` is the twist of width `1` as a form on `Γ₁(L)`. -/
noncomputable def twistOfWidth : ModularForm (twistLevel Γ M N) k :=
  (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a •
    (translate F (upperRightHom ((a.val : ℝ) * N / M))).restrict (twistLevel_le Γ M N a)

variable [Γ.HasDetOne] [NeZero M] in
lemma twistOfWidth_apply (τ : ℍ) :
    twistOfWidth N Φ F τ = (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * F (((a.val : ℝ) * N / M) +ᵥ τ) := by
  simp only [twistOfWidth, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, coe_restrict, coe_translate, ModularForm.slash_upperRightHom_apply]

variable [Γ.HasDetOne] [NeZero M] [NeZero N] in
/-- **The expansion of a twist** (LMFDB `mf.gl2.history.new`): if `f = ∑ aₙ q^(n/N)` is a modular
form on `Γ`, where `N` is a strict period of `Γ`, then for every function `ψ` modulo `M` the
function `∑ ψ(n) aₙ q^(n/N)` is the modular form `twistOfWidth N ψ f`: its `n`-th coefficient in
`q^(1/N)` is `ψ(n) aₙ`. -/
lemma qExpansion_twistOfWidth_coeff (hΓ : (N : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    (qExpansion N (twistOfWidth N Φ F)).coeff n = Φ n * (qExpansion N F).coeff n := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hN hΓ⟩
  have key (τ : ℍ) : HasSum (fun r : ℕ ↦ (Φ r * (qExpansion N F).coeff r) • 𝕢 N (τ : ℂ) ^ r)
      (twistOfWidth N Φ F τ) := by
    simpa [twistOfWidth_apply] using hasSum_twist Φ (fun r : ℕ ↦ (r : ℤ)) (NeZero.ne N)
      (fun z ↦ by simpa using ModularForm.hasSum_qExpansion F hN hΓ z) τ
  exact (ModularFormClass.qExpansion_coeff_unique hN (natCast_mem_strictPeriods_twistLevel hΓ)
    key n).symm

variable [Γ.HasDetOne] [NeZero M] [NeZero N] in
/-- **Sub-series of a modular form** (LMFDB `mf.gl2.history.new`): if `f = ∑ aₙ q^(n/N)` is a
modular form on `Γ`, where `N` is a strict period of `Γ`, then `∑_{n ≡ r (M)} aₙ q^(n/N)` is the
modular form `twistOfWidth N 1_r f`, the twist by the indicator function of `r` modulo `M`. -/
lemma qExpansion_twistOfWidth_single_coeff (hΓ : (N : ℝ) ∈ Γ.strictPeriods) (r : ZMod M) (n : ℕ) :
    (qExpansion N (twistOfWidth N (Pi.single r 1) F)).coeff n =
      if (n : ZMod M) = r then (qExpansion N F).coeff n else 0 := by
  rw [qExpansion_twistOfWidth_coeff _ _ hΓ, Pi.single_apply]
  split_ifs <;> simp

/-- **The sum over coset representatives is the trace** (LMFDB `mf.gl2.history.new`): if `f` is a
modular form on `H`, with trivial multiplier system, and `G` is the disjoint union of finitely many
right cosets `(H ∩ G) γᵢ`, then `∑ᵢ f ∣[k] γᵢ` is the trace of `f`, a modular form on `G`. The
LMFDB's `H` is a subgroup of finite index of `G`, in which case `H ∩ G = H`. -/
lemma sum_slash_eq_trace (hδ : Function.Bijective fun i ↦
    (Quotient.mk'' (δ i) : Quotient (QuotientGroup.rightRel (𝒢.subgroupOf ℋ)))) :
    ∑ i, ⇑G ∣[k] (δ i : GL (Fin 2) ℝ) = ⇑(ModularForm.trace ℋ G) := by
  let _ : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  rw [ModularForm.coe_trace]
  exact Fintype.sum_bijective _
    ((QuotientGroup.quotientRightRelEquivQuotientLeftRel _).bijective.comp hδ) _ _ fun i ↦ by
      simp [QuotientGroup.quotientRightRelEquivQuotientLeftRel]

end ModularForm

namespace SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {M N : ℕ} [NeZero M] (Φ : ZMod M → ℂ)
  (E : SlashInvariantForm Γ k)

variable (N) in
/-- The **twist** of a function `f` on the upper half-plane that is invariant under the weight `k`
action of `Γ`, by a function `ψ` modulo `M`: the function `M⁻¹ ∑_{a mod M} 𝓕ψ(a) f(z + aN/M)`, which
is invariant under the weight `k` action of `twistLevel Γ M N`. This is `ModularForm.twistOfWidth`
without holomorphy or growth conditions, for functions with poles at the cusps: if
`f = ∑_{n ≥ n₀} aₙ q^(n/N)` with `n₀ < 0`, the twist is `∑_{n ≥ n₀} ψ(n) aₙ q^(n/N)`
(`hasSum_twistOfWidth`). -/
noncomputable def twistOfWidth : SlashInvariantForm (twistLevel Γ M N) k :=
  (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a •
    (translate E (upperRightHom ((a.val : ℝ) * N / M))).restrict (twistLevel_le Γ M N a)

lemma twistOfWidth_apply (τ : ℍ) :
    twistOfWidth N Φ E τ = (M : ℂ)⁻¹ * ∑ a : ZMod M, 𝓕 Φ a * E (((a.val : ℝ) * N / M) +ᵥ τ) := by
  simp only [twistOfWidth, FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul, coe_restrict, coe_translate, ModularForm.slash_upperRightHom_apply]

lemma mdifferentiable_twistOfWidth (hE : MDiff E) : MDiff (twistOfWidth N Φ E) := by
  rw [twistOfWidth, FunLike.coe_smul, FunLike.coe_sum]
  exact (MDifferentiable.sum fun a _ ↦ (hE.slash k _).const_smul (𝓕 Φ a)).const_smul _

/-- **The expansion of a twist, with poles at the cusp allowed** (LMFDB `mf.gl2.history.new`): if a
function `f` on the upper half-plane, invariant under the weight `k` action of `Γ`, has an expansion
`f = ∑_{n ∈ ℤ} aₙ q^(n/N)`, for instance `∑_{n ≥ n₀} aₙ q^(n/N)` with `n₀ < 0`, then for every
function `ψ` modulo `M` the function `∑ ψ(n) aₙ q^(n/N)` is `twistOfWidth N ψ f`, which is
invariant under the weight `k` action of `twistLevel Γ M N`, and holomorphic if `f` is. -/
lemma hasSum_twistOfWidth {c : ℤ → ℂ} (hN : N ≠ 0)
    (hE : ∀ τ : ℍ, HasSum (fun n : ℤ ↦ c n * 𝕢 N τ ^ n) (E τ)) (τ : ℍ) :
    HasSum (fun n : ℤ ↦ Φ n * c n * 𝕢 N τ ^ n) (twistOfWidth N Φ E τ) :=
  twistOfWidth_apply Φ E τ ▸ hasSum_twist Φ id hN hE τ

end SlashInvariantForm

namespace HeckeRing.GL2

variable {p : ℕ} [NeZero p] {k : ℤ} (f : ModularForm ((Gamma1 1).map (mapGL ℝ)) k)

variable (p) in
/-- **`diag(p, 1)` conjugates `Γ₀(p)` into `SL(2, ℤ)`**, so that for a modular form `f` on
`SL(2, ℤ)` the function `z ↦ f(pz)` is the modular form `ModularForm.levelRaise p _ f` on `Γ₀(p)`
(LMFDB `mf.gl2.history.new`). -/
lemma Gamma0_map_le_conjAct_scaleGL_one :
    (Gamma0 p).map (mapGL ℝ) ≤ toConjAct (scaleGL p)⁻¹ • (Gamma1 1).map (mapGL ℝ) := by
  have h1 : Gamma1 1 = ⊤ := top_unique (Gamma_one_top ▸ Gamma_le_Gamma1 1)
  simpa [Gamma0_one_eq_top, h1] using Gamma0_map_le_conjAct_scaleGL 1 p

/-- The function `z ↦ f((z + j)/p)`, for a modular form `f` on `SL(2, ℤ)`, as a modular form on the
conjugate `(S T^j)⁻¹ Γ₀(p) S T^j` of `Γ₀(p)` (LMFDB `mf.gl2.history.new`): it is `p^k` times the
translate by `S T^j` of `z ↦ f(pz)`. Its values are computed in `upperTriTranslate_apply`. -/
noncomputable def upperTriTranslate (j : Fin p) :
    ModularForm (toConjAct (mapGL ℝ (S * T ^ (j : ℤ)))⁻¹ • (Gamma0 p).map (mapGL ℝ)) k :=
  (p : ℂ) ^ k • translate (ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) f)
    (mapGL ℝ (S * T ^ (j : ℤ)))

/-- **The values of `upperTriTranslate`**: `upperTriTranslate f j` is `z ↦ f((z + j)/p)`, where
`(z + j)/p` is the image of `z` under `!![1, j; 0, p]` (`coe_upperTriRep_smul`). -/
lemma upperTriTranslate_apply (j : Fin p) (z : ℍ) : upperTriTranslate f j z =
    f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p j) • z) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hα : mapGL ℝ S * GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p j) =
      scaleGL p * mapGL ℝ (S * T ^ (j : ℤ)) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply]
  have hS : ⇑f ∣[k] mapGL ℝ S = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Gamma1_one_map_eq_SL ▸ ⟨S, rfl⟩)
  have h : (⇑f ∣[k] scaleGL p) ∣[k] mapGL ℝ (S * T ^ (j : ℤ)) =
      ⇑f ∣[k] (upperTriRep p j : GL (Fin 2) ℚ) := by
    rw [← SlashAction.slash_mul, ← hα, SlashAction.slash_mul, hS, rat_slash]
  rw [upperTriTranslate, FunLike.coe_smul, coe_translate, ModularForm.coe_levelRaise,
    ModularForm.smul_slash, σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply, h, Pi.smul_apply,
    Pi.smul_apply, slash_upperTriRep_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ← zpow_add₀ hp0, add_sub_cancel, zpow_one, mul_inv_cancel₀ hp0, one_mul]

/-- **The Hecke operator `T(p)` at level `1`** (LMFDB `mf.gl2.history.new`): for a modular form `f`
of weight `k` on `SL(2, ℤ)` and a prime `p`,
`T_p f = (∑_{0 ≤ j < p} f((z + j)/p) + p^k f(pz)) / p`, where `T_p` is Tau Ceti's Hecke operator,
`(z + j)/p` is the image of `z` under `!![1, j; 0, p]` (`coe_upperTriRep_smul`) and `pz` its image
under `diag(p, 1)` (`coe_scaleGL_smul`). So the sum is again a modular form on `SL(2, ℤ)`. -/
lemma heckeTNat_apply_of_level_one (hp : p.Prime) (z : ℍ) : heckeTNat k p f z =
    (∑ j : Fin p, f (GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p j) • z) +
      p ^ k * f (scaleGL p • z)) / p := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hd : diamondOpNat k p f = f := by
    rw [diamondOpNat_of_coprime k (Nat.coprime_one_right p),
      Subsingleton.elim (ZMod.unitOfCoprime p _) 1, diamondOp_one]
    rfl
  rw [coe_heckeTNat_prime k hp f, Pi.add_apply, heckeSlashUpperTri_apply, hd, rat_slash,
    scaleRep_def, map_natDiagGL_d_one_eq_scaleGL, slash_scaleGL_apply]
  simp only [slash_upperTriRep_apply]
  rw [← Finset.mul_sum, zpow_sub_one₀ hp0]
  field_simp

variable {N : ℕ} [NeZero N] (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) in
/-- **The Hecke operator is the trace of a translate** (LMFDB `mf.gl2.history.new`): for a modular
form `g` on `Γ₁(N)` and every `p ≥ 1`, Tau Ceti's Hecke operator `T_p g` is the trace to `Γ₁(N)` of
the translate `g ∣[k] diag(1, p)` of `g`, a modular form on `diag(1, p)⁻¹ Γ₁(N) diag(1, p)`. So the
Hecke operators are constructed by combining the two methods: changing the group, then enlarging
it by a sum over coset representatives. For cusp forms this is Tau Ceti's
`TauCeti.heckeTCuspNat_eq_trace_translate`. -/
lemma heckeTNat_eq_trace_translate : heckeTNat k p g = ModularForm.trace ((Gamma1 N).map (mapGL ℝ))
    (translate g (GeneralLinearGroup.map (algebraMap ℚ ℝ) (natDiagGL 2 ![1, p]))) := by
  apply DFunLike.coe_injective
  rw [coe_heckeTNat]
  apply heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N p) _ (map_mapGL (Gamma1 N))
    (map_mapGL (Gamma1 N)) g
  rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

/-- **`z ↦ f((z + j)/p)` is not modular on `Γ₀(p)` in general**: if a modular form `f` on
`SL(2, ℤ)` is such that `z ↦ f((z + j)/p)` is invariant under the weight `k` action of
`T ∈ Γ₀(p)`, where `p > 1`, then the first Fourier coefficient of `f` vanishes. Indeed
`f((z + j)/p) = ∑ aₙ e^(2πin(z + j)/p)` has period `1` only if `aₙ = 0` for all `n` prime to `p`. -/
lemma qExpansion_coeff_one_eq_zero_of_slash_upperTriTranslate (hp : 1 < p) (j : Fin p)
    (h : ⇑(upperTriTranslate f j) ∣[k] mapGL ℝ T = upperTriTranslate f j) :
    (qExpansion 1 f).coeff 1 = 0 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hΓ : (1 : ℝ) ∈ ((Gamma1 1).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map 1
  have : Fact (IsCusp OnePoint.infty ((Gamma1 1).map (mapGL ℝ))) :=
    ⟨isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hT (z : ℍ) : upperTriTranslate f j ((1 : ℝ) +ᵥ z) = upperTriTranslate f j z := by
    have hz :
        (⇑(upperTriTranslate f j) ∣[k] mapGL ℝ (T ^ (1 : ℤ))) z = upperTriTranslate f j z := by
      rw [zpow_one, h]
    rwa [ModularGroup.mapGL_T_zpow_eq_upperRightHom, ModularForm.slash_upperRightHom_apply,
      Int.cast_one] at hz
  have hper (τ : ℍ) : f ((p : ℝ)⁻¹ +ᵥ τ) = f τ := by
    have h2 : upperTriTranslate f j ((1 : ℝ) +ᵥ (-(j : ℝ) +ᵥ scaleGL p • τ)) =
        upperTriTranslate f j (-(j : ℝ) +ᵥ scaleGL p • τ) :=
      hT _
    rw [upperTriTranslate_apply, upperTriTranslate_apply] at h2
    convert h2 using 2 <;> ext1 <;> simp [coe_upperTriRep_smul] <;> field_simp
    ring1
  have hq (τ : ℍ) : 𝕢 1 (((p : ℝ)⁻¹ +ᵥ τ : ℍ) : ℂ) = cexp (2 * π * I / p) * 𝕢 1 (τ : ℂ) := by
    rw [coe_vadd, Periodic.qParam, Periodic.qParam, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have key (τ : ℍ) : HasSum (fun m : ℕ ↦ (cexp (2 * π * I / p) ^ m * (qExpansion 1 f).coeff m) •
      𝕢 1 (τ : ℂ) ^ m) (f τ) := by
    refine (hper τ ▸ ModularForm.hasSum_qExpansion f one_pos hΓ ((p : ℝ)⁻¹ +ᵥ τ)).congr_fun
      fun m ↦ ?_
    rw [hq, mul_pow, smul_eq_mul]
    ring1
  have h1 : cexp (2 * π * I / p) ^ 1 * (qExpansion 1 f).coeff 1 = (qExpansion 1 f).coeff 1 :=
    ModularFormClass.qExpansion_coeff_unique one_pos hΓ key 1
  have hζ : cexp (2 * π * I / p) ≠ 1 := by
    rw [Ne, Complex.exp_eq_one_iff]
    rintro ⟨n, hn⟩
    have hn' : (n : ℂ) * p = 1 := by
      field_simp at hn
      linear_combination -hn
    have hn'' : n * p = 1 := by
      exact_mod_cast hn'
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hn'' with ⟨-, hp1⟩ | ⟨-, hp1⟩ <;> omega
  rw [pow_one, mul_left_eq_self₀] at h1
  exact h1.resolve_left hζ

/-- **`z ↦ f(pz)` is not modular on `SL(2, ℤ)` in general**: if a modular form `f` on `SL(2, ℤ)`
is such that `z ↦ f(pz)` is invariant under the weight `k` action of `S`, where `p > 1`, then the
first Fourier coefficient of `f` vanishes. Indeed `z ↦ f(z/p)` is then `p^k f(pz)`, which has period
`1`. -/
lemma qExpansion_coeff_one_eq_zero_of_slash_levelRaise (hp : 1 < p)
    (h : ⇑(ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) f) ∣[k] mapGL ℝ S =
      ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) f) :
    (qExpansion 1 f).coeff 1 = 0 := by
  have hu : ⇑(upperTriTranslate f (0 : Fin p)) =
      (p : ℂ) ^ k • ⇑(ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) f) := by
    rw [upperTriTranslate, FunLike.coe_smul, coe_translate]
    simp [h]
  refine qExpansion_coeff_one_eq_zero_of_slash_upperTriTranslate f hp 0 ?_
  rw [hu, ModularForm.smul_slash, σ_mapGL_real_eq_refl, ContinuousAlgEquiv.refl_apply]
  exact congrArg _ <| SlashInvariantFormClass.slash_action_eq _ _ <| mem_map_of_mem _ <| by simp

private lemma qExpansion_coeff_one_discriminant : (qExpansion 1 ⇑(discriminantEigenform.toCuspForm :
    ModularForm ((Gamma1 1).map (mapGL ℝ)) 12)).coeff 1 = 1 := by
  have h : ⇑(discriminantEigenform.toCuspForm : ModularForm ((Gamma1 1).map (mapGL ℝ)) 12) =
      ⇑discriminantEigenform.toCuspForm :=
    rfl
  rw [h, coe_discriminantEigenform, discriminant_qExpansion_coeff_one]

/-- **`Δ((z + j)/p)` is not modular on `Γ₀(p)`**, for `p > 1` and every `j`: the LMFDB's claim that
the functions `f((z + j)/p)` are modular on `Γ₀(p)` (LMFDB `mf.gl2.history.new`) fails for the
discriminant function `Δ`, whose first Fourier coefficient is `1`. In particular none of these
functions is modular on `SL(2, ℤ)` in general. -/
lemma not_forall_slash_upperTriTranslate_discriminant (hp : 1 < p) (j : Fin p) :
    letI Δ : ModularForm ((Gamma1 1).map (mapGL ℝ)) 12 := discriminantEigenform.toCuspForm
    ¬∀ γ ∈ (Gamma0 p).map (mapGL ℝ), ⇑(upperTriTranslate Δ j) ∣[(12 : ℤ)] γ =
      upperTriTranslate Δ j :=
  fun h ↦ one_ne_zero <| qExpansion_coeff_one_discriminant.symm.trans <|
    qExpansion_coeff_one_eq_zero_of_slash_upperTriTranslate _ hp j <| h _ <| mem_map_of_mem _ <| by
      simp

/-- **`Δ(pz)` is not modular on `SL(2, ℤ)`**, for `p > 1`: it is not invariant under `S`. So the
function `z ↦ f(pz)` is modular only on a proper subgroup of `SL(2, ℤ)` in general (LMFDB
`mf.gl2.history.new`). -/
lemma not_slash_levelRaise_discriminant (hp : 1 < p) :
    letI Δ : ModularForm ((Gamma1 1).map (mapGL ℝ)) 12 := discriminantEigenform.toCuspForm
    ⇑(ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) Δ) ∣[(12 : ℤ)] mapGL ℝ S ≠
      ModularForm.levelRaise p (Gamma0_map_le_conjAct_scaleGL_one p) Δ :=
  fun h ↦ one_ne_zero <| qExpansion_coeff_one_discriminant.symm.trans <|
    qExpansion_coeff_one_eq_zero_of_slash_levelRaise _ hp h

end HeckeRing.GL2
