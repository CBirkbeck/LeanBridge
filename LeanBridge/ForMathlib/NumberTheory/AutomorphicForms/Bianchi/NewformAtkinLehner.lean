import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.GammaZeroFundamentalDomain
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.MainLemma

/-!
# Atkin–Lehner theory of Bianchi newforms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑 ≠ 0` an
ideal of `𝒪_K`. This file draws the consequences of the Main Lemma of Atkin and Lehner
(`HyperbolicThreeSpace.mem_bianchiOldforms_of_coeff_eq_zero`), as in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner`.

The Fourier–Bessel coefficients `c(α)` of a form of level `Γ₀(𝔑)` only depend on the ideal `(α)`,
since `(u, 0; 0, 1)` lies in `Γ₀(𝔑)` for a unit `u`, and acts on Fourier–Bessel functions by
multiplying the frequency by `u`, in even weight, as `|u| = 1`
(`HyperbolicThreeSpace.HasBianchiWhittakerExpansion.coeff_unit_mul`). This uses the class number
`1` nowhere.

For an eigenform of the `T_𝔭`, `𝔭 ∤ 𝔑`, the Hecke relations
`a_𝔭 c(α) = n |ϖ|^{-(k/2+1)} c(ϖα) + |ϖ|^{k/2+1} c(α / ϖ)` then express `c(α)`, for `α` prime to
`𝔑`, as a multiple of `c(1)` (by induction on `|N(α)|`). So if `c(1) = 0`, all the coefficients
prime to `𝔑` vanish, and a form of the newspace with this property is both new and old, so is `0`
(`HyperbolicThreeSpace.eq_zero_of_coeff_one_eq_zero`). Hence:

* **`c(1) ≠ 0`** for a nonzero eigenform of the newspace
  (`HyperbolicThreeSpace.coeff_one_ne_zero_of_mem_bianchiNewSubspace`);
* **multiplicity one**: two forms of the newspace with the same eigenvalues at the `𝔭 ∤ 𝔑` are
  proportional (`HyperbolicThreeSpace.eq_smul_of_mem_bianchiNewSubspace`), and two newforms with
  the same eigenvalues at the `𝔭 ∤ 𝔑` are equal
  (`HyperbolicThreeSpace.BianchiNewformOfWeight.toFun_eq_of_eigenvalue_eq`);
* **strong multiplicity one inside the newspace**: two forms of the newspace with the same
  coefficients prime to `𝔑` are equal
  (`HyperbolicThreeSpace.eq_of_mem_bianchiNewSubspace_of_coeff_eq`);
* a nonzero eigenform of the newspace of weight `k ≥ 1` is a multiple of a unique newform
  (`HyperbolicThreeSpace.BianchiNewformOfWeight.ofEigenform`).

The eigenvalue of `T_𝔭` at a prime `𝔭 ∤ 𝔑` is the coefficient of index `𝔭`, for every generator of
`𝔭` (`HyperbolicThreeSpace.BianchiNewformOfWeight.eigenvalue_eq_idealCoeff`), the coefficients of
a newform being indexed by the ideals of `𝒪_K`, as the LMFDB has them
(`HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff`).

## Main definitions

* `HyperbolicThreeSpace.BianchiNewformOfWeight.idealCoeff` (LMFDB `mf.bianchi.newform`): the
  coefficient `c(𝔞)` of index an ideal `𝔞`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.ofEigenform` (LMFDB `mf.bianchi.spaces`): the newform
  of a nonzero eigenform of the newspace.

## Main results

* `HyperbolicThreeSpace.HasBianchiWhittakerExpansion.coeff_unit_mul`: `c(uα) = c(α)` for a unit `u`.
* `HyperbolicThreeSpace.coeff_eq_zero_of_coeff_one_eq_zero`: if `c(1) = 0`, an eigenform has zero
  coefficients at every index prime to the level.
* `HyperbolicThreeSpace.eq_zero_of_coeff_one_eq_zero`: an eigenform of the newspace with `c(1) = 0`
  vanishes.
* `HyperbolicThreeSpace.coeff_one_ne_zero_of_mem_bianchiNewSubspace`: `c(1) ≠ 0` for a nonzero
  eigenform of the newspace.
* `HyperbolicThreeSpace.eq_smul_of_mem_bianchiNewSubspace`: multiplicity one in the newspace.
* `HyperbolicThreeSpace.eq_of_mem_bianchiNewSubspace_of_coeff_eq`: strong multiplicity one inside
  the newspace.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.coeff_unit_mul`: `c(uα) = c(α)` for a newform.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.toFun_eq_of_eigenvalue_eq`: a newform is determined
  by its eigenvalues at the `𝔭 ∤ 𝔑`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.eigenvalue_eq_idealCoeff`: `a_𝔭 = c(𝔭)` for `𝔭 ∤ 𝔑`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.toFun_ofEigenform`: the form of the newform of an
  eigenform `F` is `F / c(1)`.
-/

open Complex Matrix Module NumberField HilbertModularGroup HilbertModularForm

open Submodule (IsPrincipal)

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {x : K} {k : ℕ} {c c' : 𝓞 K → ℂ}
  {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {𝔑 : Ideal (𝓞 K)} {α : 𝓞 K}

lemma coe_slRepresentative_heckeLower (ϖ : Kˣ) :
    (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ, 0; 0, (σ ϖ ^ (2⁻¹ : ℂ))⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slRepresentative, heckeLower, det_fin_two]

lemma span_sup_eq_top_of_mul {p β : 𝓞 K} (h : Ideal.span {p * β} ⊔ 𝔑 = ⊤) :
    Ideal.span {β} ⊔ 𝔑 = ⊤ :=
  top_le_iff.mp <| h ▸ sup_le_sup_right
    (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left β p)) 𝔑

variable [NumberField K]

variable (α) in
lemma bianchiWhittakerTerm_smul (r : ℂ) (p : ℂ × ℝ) :
    bianchiWhittakerTerm σ δ k (r • c) p α = r • bianchiWhittakerTerm σ δ k c p α := by
  simp only [bianchiWhittakerTerm, Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

lemma HasBianchiWhittakerExpansion.smul (r : ℂ)
    (h : HasBianchiWhittakerExpansion σ δ k (extend F) c) :
    HasBianchiWhittakerExpansion σ δ k (extend (r • F)) (r • c) := by
  intro p hp
  rw [extend_smul, Pi.smul_apply]
  simpa only [bianchiWhittakerTerm_smul] using (h p hp).const_smul r

lemma HasBianchiWhittakerExpansion.sub (h : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (h' : HasBianchiWhittakerExpansion σ δ k (extend G) c') :
    HasBianchiWhittakerExpansion σ δ k (extend (F - G)) (c - c') := by
  intro p hp
  rw [extend_sub, Pi.sub_apply]
  simpa only [bianchiWhittakerTerm_sub] using (h p hp).sub (h' p hp)

lemma coeff_eq_of_hasSum (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0) (hδ : δ ^ 2 = discr K)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (hc' : ∀ z, HasSum (fun β : {β : 𝓞 K // β ≠ 0} ↦
      c' β • bianchiWhittakerFunction (σ β.1 / δ) k z) (F z)) (hα : α ≠ 0) : c α = c' α := by
  refine sub_eq_zero.mp <| eq_zero_of_hasSum_smul_bianchiWhittakerFunction (c := c - c') (k := k) hK
    hx hδ one_ne_zero (fun z ↦ ?_) hα
  have h₁ : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ bianchiWhittakerTerm σ δ k c z.coords α)
      (extend F z.coords) := hc z.coords (coords_snd_pos z)
  rw [extend_coords] at h₁
  simp only [bianchiWhittakerTerm_coords k σ δ c _ (norm_eq_sqrt_of_sq_eq_discr hδ) z] at h₁
  simpa [sub_smul] using h₁.sub (hc' z)

lemma absNorm_span_lt_of_mul {p β : 𝓞 K} (hp : ¬IsUnit p) (h : p * β ≠ 0) :
    Ideal.absNorm (Ideal.span {β}) < Ideal.absNorm (Ideal.span {p * β}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  have h₁ : Ideal.absNorm (Ideal.span {β}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr <| by
    simpa using right_ne_zero_of_mul h
  have h₂ : Ideal.absNorm (Ideal.span {p}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr <| by
    simpa using left_ne_zero_of_mul h
  have h₃ : Ideal.absNorm (Ideal.span {p}) ≠ 1 := fun h₄ ↦
    hp (Ideal.span_singleton_eq_top.mp (Ideal.absNorm_eq_one_iff.mp h₄))
  exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero h₁) (by omega)

variable [IsTotallyComplex K]

/-- **The Fourier–Bessel coefficients only depend on the ideal** (LMFDB `mf.bianchi.newform`): for
a quadratic field `K` embedded in `ℂ` by `σ` with `σ(K) ⊄ ℝ`, `δ² = Δ`, and `F` invariant under
`Γ₀(𝔑)`, with the Fourier–Bessel expansion of weight `k` with coefficients `c`, one has
`c(uα) = c(α)` for every unit `u` of `𝒪_K` and every `α ≠ 0`. The matrix `(u, 0; 0, 1)` lies in
`Γ₀(𝔑)`, so that `F ∣ (u, 0; 0, 1) = F`, and it maps the Fourier–Bessel function of frequency `μ` to
that of frequency `uμ`, as `|u| = 1`. -/
lemma HasBianchiWhittakerExpansion.coeff_unit_mul (hK : finrank ℚ K = 2) (hx : (σ x).im ≠ 0)
    (hδ : δ ^ 2 = discr K) (hF : IsBianchiSlashInvariant σ 𝔑.gamma0GL k F)
    (hc : HasBianchiWhittakerExpansion σ δ k (extend F) c) (u : (𝓞 K)ˣ) (hα : α ≠ 0) :
    c (u * α) = c α := by
  rcases Nat.even_or_odd k with hk | hk
  · let ϖ : Kˣ := Units.map (algebraMap (𝓞 K) K) u
    have hnorm : ‖σ (ϖ : K)‖ = 1 := norm_unit_eq_one hK u
    have hσϖ : σ (ϖ : K) ≠ 0 := (map_ne_zero σ).mpr ϖ.ne_zero
    have hs : (σ ϖ ^ (2⁻¹ : ℂ)) ^ 2 = σ ϖ := cpow_ofNat_inv_pow _ 2
    have hs₀ : σ ϖ ^ (2⁻¹ : ℂ) ≠ 0 := fun h ↦ hσϖ (by rw [← hs, h, zero_pow two_ne_zero])
    have hg : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      rw [coe_slRepresentative_heckeLower]
      rfl
    have h₀₀ : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
        (σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ := by
      rw [coe_slRepresentative_heckeLower]
      rfl
    have h₀₁ : (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      rw [coe_slRepresentative_heckeLower]
      rfl
    have hsq : ((σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ) ^ 2 = σ ϖ := by
      rw [mul_pow, inv_pow, hs, sq, ← mul_assoc, inv_mul_cancel₀ hσϖ, one_mul]
    have hnorm₀₀ : ‖(σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ‖ = 1 := by
      have h₁ : ‖(σ ϖ ^ (2⁻¹ : ℂ))⁻¹ * σ ϖ‖ ^ 2 = 1 := by
        rw [← norm_pow, hsq, hnorm]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h₁
    have hslash : bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F = F := by
      rcases isSLRepresentative_slRepresentative (σ := σ) (heckeLower ϖ) with ⟨s, hs'⟩
      refine hF (GeneralLinearGroup.rowScale 0 u) (by simp [Ideal.gamma0GL]) _ s (hs'.trans ?_)
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [heckeLower, ϖ]
    let e : {β : 𝓞 K // β ≠ 0} ≃ {β : 𝓞 K // β ≠ 0} :=
      (Units.mulLeft u).subtypeEquiv fun β ↦ by simp
    have hc' (z : HyperbolicThreeSpace) : HasSum (fun β : {β : 𝓞 K // β ≠ 0} ↦
        c ((u⁻¹ : (𝓞 K)ˣ) * β.1) • bianchiWhittakerFunction (σ β.1 / δ) k z) (F z) := by
      have h : HasSum (fun α : {α : 𝓞 K // α ≠ 0} ↦ (c α *
          (((‖(slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ (k + 2) : ℝ) :
            ℂ) * cexp (2 * π * I * (σ α.1 / δ *
              ((slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
                (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1) +
              conj (σ α.1 / δ *
                ((slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
                  (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1)))))) •
            bianchiWhittakerFunction (σ α.1 / δ *
              (slRepresentative σ (heckeLower ϖ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ 2) k z)
          (bianchiSlash k (slRepresentative σ (heckeLower ϖ)) F z) :=
        hc.hasSum_bianchiSlash hk (norm_eq_sqrt_of_sq_eq_discr hδ) hg z
      rw [hslash, h₀₀, h₀₁, hnorm₀₀, hsq] at h
      refine e.hasSum_iff.mp (h.congr_fun fun β ↦ ?_)
      have e₁ : σ ((e β).1 : K) / δ = σ β.1 / δ * σ ϖ := by
        have e₂ : ((e β).1 : K) = ϖ * β.1 := rfl
        rw [e₂, map_mul]
        ring1
      have e₃ : c ((u⁻¹ : (𝓞 K)ˣ) * (e β).1) = c β := by
        simp [e]
      rw [Function.comp_apply, e₁, e₃]
      simp
    have h : c ((u : 𝓞 K) * α) = c ((u⁻¹ : (𝓞 K)ˣ) * ((u : 𝓞 K) * α)) :=
      coeff_eq_of_hasSum (c' := fun β : 𝓞 K ↦ c ((u⁻¹ : (𝓞 K)ˣ) * β)) hK hx hδ hc hc'
        (mul_ne_zero u.ne_zero hα)
    rwa [Units.inv_mul_cancel_left] at h
  · have hF₀ : F = 0 := hF.eq_zero_of_odd hk
    rw [hF₀, extend_zero] at hc
    rw [hc.eq_zero hK hx hδ (mul_ne_zero u.ne_zero hα), hc.eq_zero hK hx hδ hα]

variable [IsPrincipalIdealRing (𝓞 K)]

/-- **If `c(1) = 0`, the coefficients of an eigenform prime to the level vanish**: for `K` imaginary
quadratic of class number `1`, in even weight, and a form of level `Γ₀(𝔑)` which is an eigenform of
`T_𝔭` for every `𝔭 ∤ 𝔑`, with Fourier–Bessel coefficients `c`, `c(1) = 0` implies `c(α) = 0` for
every `α ≠ 0` prime to `𝔑`, by induction on `|N(α)|`: `c(u) = c(1)` for a unit `u`, and for
`α = ϖβ`, `ϖ` a prime, the Hecke relation at `β` expresses `c(α)` through `c(β)` and `c(β / ϖ)`. -/
lemma coeff_eq_zero_of_coeff_one_eq_zero [NeZero 𝔑] (hK : finrank ℚ K = 2) (hk : Even k)
    {Φ : bianchiModularForms σ 𝔑.gamma0GL k}
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c)
    (hT : ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊥), 𝔭.IsPrime → 𝔭 ⊔ 𝔑 = ⊤ →
      ∃ a : ℂ, bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ = a • Φ) (h₁ : c 1 = 0) (hα : α ≠ 0)
    (hα𝔑 : Ideal.span {α} ⊔ 𝔑 = ⊤) : c α = 0 := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  generalize hn : Ideal.absNorm (Ideal.span {α}) = n
  induction n using Nat.strong_induction_on generalizing α with
  | _ n ih =>
    by_cases hu : IsUnit α
    · rcases hu with ⟨u, rfl⟩
      have h : c ((u : 𝓞 K) * 1) = c 1 :=
      hc.coeff_unit_mul hK hx (cpow_ofNat_inv_pow _ 2) Φ.2.invariant u one_ne_zero
      rwa [mul_one, h₁] at h
    · rcases WfDvdMonoid.exists_irreducible_factor hu hα with ⟨ϖ, hϖ, hdvd⟩
      have hϖp : Prime ϖ := hϖ.prime
      have h𝔭p : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖp.ne_zero).mpr hϖp
      have h𝔭 : Ideal.span {ϖ} ≠ ⊥ := by
        simpa using hϖp.ne_zero
      have hle : Ideal.span {α} ≤ Ideal.span {ϖ} := Ideal.span_singleton_le_span_singleton.mpr hdvd
      have h𝔭𝔑 : Ideal.span {ϖ} ⊔ 𝔑 = ⊤ := top_le_iff.mp (hα𝔑 ▸ sup_le_sup_right hle 𝔑)
      have hp : ¬IsUnit (IsPrincipal.generator (Ideal.span {ϖ})) := fun hu' ↦ h𝔭p.ne_top <| by
        rw [← Ideal.span_singleton_generator (Ideal.span {ϖ}), Ideal.span_singleton_eq_top]
        exact hu'
      rcases (IsPrincipal.mem_iff_generator_dvd _).mp (hle (Ideal.mem_span_singleton_self α)) with
        ⟨β, rfl⟩
      have hβ : β ≠ 0 := right_ne_zero_of_mul hα
      have hp₀ : IsPrincipal.generator (Ideal.span {ϖ}) ≠ 0 := left_ne_zero_of_mul hα
      have hβ𝔑 : Ideal.span {β} ⊔ 𝔑 = ⊤ := span_sup_eq_top_of_mul hα𝔑
      have hβn : Ideal.absNorm (Ideal.span {β}) < n := hn ▸ absNorm_span_lt_of_mul hp hα
      have hcβ : c β = 0 := ih _ hβn hβ hβ𝔑 rfl
      have hext : Function.extend (IsPrincipal.generator (Ideal.span {ϖ}) * ·) c 0 β = 0 := by
        by_cases hβ' : ∃ γ, IsPrincipal.generator (Ideal.span {ϖ}) * γ = β
        · rcases hβ' with ⟨γ, rfl⟩
          rw [(mul_right_injective₀ hp₀).extend_apply]
          exact ih _ ((absNorm_span_lt_of_mul hp hβ).trans hβn) (right_ne_zero_of_mul hβ)
            (span_sup_eq_top_of_mul hβ𝔑) rfl
        · exact Function.extend_apply' _ _ _ hβ'
      have hcard : Nat.card (HeckeTranslations (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭) 1) =
          Ideal.absNorm (Ideal.span {ϖ}) :=
        natCard_heckeTranslations _ _ (spanSingleton_bianchiIdealGenerator _ h𝔭)
      have hN₀ : Ideal.absNorm (Ideal.span {ϖ}) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr h𝔭
      have hfin : Finite (HeckeTranslations (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭) 1) :=
        Nat.finite_of_card_ne_zero (hcard ▸ hN₀)
      let _ : Fintype (HeckeTranslations (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭) 1) :=
        Fintype.ofFinite _
      rcases hT _ h𝔭 h𝔭p h𝔭𝔑 with ⟨a, ha⟩
      have hrel : a * c β = Fintype.card
          (HeckeTranslations (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭) 1) *
            ((‖σ (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭)‖ ^ (k / 2 + 1))⁻¹ : ℝ) *
              c (IsPrincipal.generator (Ideal.span {ϖ}) * β) +
          ((‖σ (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭)‖ ^ (k / 2 + 1) : ℝ) : ℂ) *
            Function.extend (IsPrincipal.generator (Ideal.span {ϖ}) * ·) c 0 β :=
        hc.mul_coeff_eq_of_bianchiHeckeTPrime σ hK hk h𝔭 h𝔭p h𝔭𝔑 ha hβ
      rw [hcβ, hext, mul_zero, mul_zero, add_zero, Fintype.card_eq_nat_card, hcard] at hrel
      have hne : (Ideal.absNorm (Ideal.span {ϖ}) : ℂ) *
          ((‖σ (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭)‖ ^ (k / 2 + 1))⁻¹ : ℝ) ≠ 0 := by
        refine mul_ne_zero (Nat.cast_ne_zero.mpr hN₀) (ofReal_ne_zero.mpr (inv_ne_zero ?_))
        exact pow_ne_zero _ (norm_ne_zero_iff.mpr
          ((map_ne_zero σ).mpr (bianchiIdealGenerator (Ideal.span {ϖ}) h𝔭).ne_zero))
      exact (mul_eq_zero.mp hrel.symm).resolve_left hne

/-- **An eigenform of the newspace with `c(1) = 0` vanishes**: for `K` imaginary quadratic of class
number `1`, its coefficients prime to the level vanish, so that it is old
(`mem_bianchiOldforms_of_coeff_eq_zero`), and new. -/
lemma eq_zero_of_coeff_one_eq_zero [NeZero 𝔑] (hK : finrank ℚ K = 2)
    {Φ : bianchiModularForms σ 𝔑.gamma0GL k}
    (hnew : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c)
    (hT : ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊥), 𝔭.IsPrime → 𝔭 ⊔ 𝔑 = ⊤ →
      ∃ a : ℂ, bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ = a • Φ) (h₁ : c 1 = 0) : Φ = 0 := by
  refine Subtype.ext ?_
  rcases Nat.even_or_odd k with hk | hk
  · rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
    exact eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace hK
      (mem_bianchiOldforms_of_coeff_eq_zero hK hx (cpow_ofNat_inv_pow _ 2) (NeZero.ne 𝔑)
        (bianchiNewSubspace_le σ k 𝔑 hnew) hc fun α hα h ↦
          coeff_eq_zero_of_coeff_one_eq_zero hK hk hc hT h₁ hα h) hnew
  · exact Φ.2.invariant.eq_zero_of_odd hk

/-- **`c(1) ≠ 0` for a nonzero eigenform of the newspace** (LMFDB `mf.bianchi.spaces`,
`mf.bianchi.newform`): for `K` imaginary quadratic of class number `1`, a nonzero form of the
newspace which is an eigenform of `T_𝔭` for every `𝔭 ∤ 𝔑` has a nonzero Fourier–Bessel coefficient
at `(1)`, so that it can be normalised by `c(1) = 1`. -/
lemma coeff_one_ne_zero_of_mem_bianchiNewSubspace [NeZero 𝔑] (hK : finrank ℚ K = 2)
    {Φ : bianchiModularForms σ 𝔑.gamma0GL k}
    (hnew : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑) (hΦ : Φ ≠ 0)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c)
    (hT : ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊥), 𝔭.IsPrime → 𝔭 ⊔ 𝔑 = ⊤ →
      ∃ a : ℂ, bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ = a • Φ) : c 1 ≠ 0 :=
  fun h₁ ↦ hΦ (eq_zero_of_coeff_one_eq_zero hK hnew hc hT h₁)

/-- **Multiplicity one in the newspace** (LMFDB `mf.bianchi.spaces`): for `K` imaginary quadratic of
class number `1`, two forms of the newspace, the first nonzero, which are eigenforms with the same
eigenvalue for `T_𝔭`, for every `𝔭 ∤ 𝔑`, are proportional. -/
lemma eq_smul_of_mem_bianchiNewSubspace [NeZero 𝔑] (hK : finrank ℚ K = 2)
    {Φ Ψ : bianchiModularForms σ 𝔑.gamma0GL k}
    (hnew : (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑)
    (hnew' : (Ψ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∈ bianchiNewSubspace σ k 𝔑) (hΦ : Φ ≠ 0)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Φ) c)
    (hc' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend Ψ) c')
    (hT : ∀ (𝔭 : Ideal (𝓞 K)) (h𝔭 : 𝔭 ≠ ⊥), 𝔭.IsPrime → 𝔭 ⊔ 𝔑 = ⊤ →
      ∃ a : ℂ, bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ = a • Φ ∧ bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Ψ = a • Ψ) :
    Ψ = (c' 1 / c 1) • Φ := by
  have hc₁ : c 1 ≠ 0 := coeff_one_ne_zero_of_mem_bianchiNewSubspace hK hnew hΦ hc fun 𝔭 h𝔭 hp h ↦
    (hT 𝔭 h𝔭 hp h).imp fun _ h ↦ h.1
  refine sub_eq_zero.mp <| eq_zero_of_coeff_one_eq_zero (c := c' - (c' 1 / c 1) • c) hK
    (Submodule.sub_mem _ hnew' (Submodule.smul_mem _ _ hnew)) (hc'.sub (hc.smul _))
    (fun 𝔭 h𝔭 hp h ↦ ?_) ?_
  · rcases hT 𝔭 h𝔭 hp h with ⟨a, ha, ha'⟩
    refine ⟨a, ?_⟩
    rw [map_sub, map_smul, ha, ha', smul_sub, smul_comm]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hc₁, sub_self]

/-- **Strong multiplicity one inside the newspace** (LMFDB `mf.bianchi.spaces`): for `K` imaginary
quadratic of class number `1`, two forms of the newspace whose Fourier–Bessel coefficients agree at
every `α ≠ 0` prime to `𝔑` are equal. -/
lemma eq_of_mem_bianchiNewSubspace_of_coeff_eq [NeZero 𝔑] (hK : finrank ℚ K = 2)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) (hG : G ∈ bianchiNewSubspace σ k 𝔑)
    (hc : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) c)
    (hc' : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend G) c')
    (h : ∀ α, α ≠ 0 → Ideal.span {α} ⊔ 𝔑 = ⊤ → c α = c' α) : F = G := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  refine sub_eq_zero.mp <| eq_zero_of_mem_bianchiOldforms_of_mem_bianchiNewSubspace hK
    (mem_bianchiOldforms_of_coeff_eq_zero hK hx (cpow_ofNat_inv_pow _ 2) (NeZero.ne 𝔑)
      (Submodule.sub_mem _ (bianchiNewSubspace_le σ k 𝔑 hF) (bianchiNewSubspace_le σ k 𝔑 hG))
        (hc.sub hc') fun α hα hα𝔑 ↦ ?_) (Submodule.sub_mem _ hF hG)
  rw [Pi.sub_apply, h α hα hα𝔑, sub_self]

lemma bianchiHeckeTPrime_eq_of_bianchiHeckeTPrimeArith_eq [NeZero 𝔑] {𝔭 : Ideal (𝓞 K)} (h𝔭 : 𝔭 ≠ ⊥)
    {Φ : bianchiModularForms σ 𝔑.gamma0GL k} {a : ℂ}
    (h : bianchiHeckeTPrimeArith σ k 𝔑 𝔭 h𝔭 Φ = a • Φ) : bianchiHeckeTPrime σ k 𝔑 𝔭 h𝔭 Φ =
    (((((Ideal.absNorm 𝔭 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * a) • Φ) := by
  have hN₀ : Ideal.absNorm 𝔭 ≠ 0 := (Ideal.absNorm_eq_zero_iff).not.mpr h𝔭
  have hN' : (((Ideal.absNorm 𝔭 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN₀))
      _).ne'
  rw [mul_smul, ← h, bianchiHeckeTPrimeArith, LinearMap.smul_apply, inv_smul_smul₀ hN']

namespace BianchiNewformOfWeight

variable [NeZero 𝔑] (N N' : BianchiNewformOfWeight σ k 𝔑)

/-- **`c(uα) = c(α)` for a newform** (LMFDB `mf.bianchi.newform`): the coefficients of a Bianchi
newform only depend on the ideal `(α)`. -/
lemma coeff_unit_mul (hK : finrank ℚ K = 2) (u : (𝓞 K)ˣ) (hα : α ≠ 0) :
    N.coeff (u * α) = N.coeff α := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  exact N.hasWhittakerExpansion.coeff_unit_mul hK hx (cpow_ofNat_inv_pow _ 2)
    N.toBianchiModularForm.2.invariant u hα

lemma toFun_ne_zero (hK : finrank ℚ K = 2) : N.toFun ≠ 0 := by
  intro h₀
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have h : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k 0 N.coeff := by
    simpa only [h₀, extend_zero] using N.hasWhittakerExpansion
  exact one_ne_zero <| N.coeff_one.symm.trans <|
    h.eq_zero hK hx (cpow_ofNat_inv_pow _ 2) one_ne_zero

/-- The coefficient `c(𝔞)` (LMFDB `mf.bianchi.newform`) of a Bianchi newform at an ideal `𝔞` of
`𝒪_K`, which is `c(α)` for every generator `α` of `𝔞 ≠ 0` (`idealCoeff_span`). -/
noncomputable def idealCoeff (𝔞 : Ideal (𝓞 K)) : ℂ :=
  N.coeff (IsPrincipal.generator 𝔞)

lemma idealCoeff_span (hK : finrank ℚ K = 2) (hα : α ≠ 0) :
    N.idealCoeff (Ideal.span {α}) = N.coeff α := by
  have h₁ : Associated (IsPrincipal.generator (Ideal.span {α})) α := by
    rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator]
  rcases h₁.symm with ⟨u, hu⟩
  rw [idealCoeff, ← hu, mul_comm, N.coeff_unit_mul hK u hα]

lemma idealCoeff_top (hK : finrank ℚ K = 2) : N.idealCoeff ⊤ = 1 := by
  rw [← Ideal.span_singleton_one, N.idealCoeff_span hK one_ne_zero, N.coeff_one]

/-- **`a_𝔭 = c(𝔭)`** (LMFDB `mf.bianchi.newform`): the Hecke eigenvalue of a Bianchi newform at a
prime `𝔭 ∤ 𝔑` is the coefficient of index `𝔭` of its Fourier–Bessel expansion. -/
lemma eigenvalue_eq_idealCoeff (hK : finrank ℚ K = 2) (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (h𝔭𝔑 : ¬𝔑 ≤ 𝔭.1) : N.eigenvalue 𝔭 = N.idealCoeff 𝔭.1 :=
  N.eigenvalue_eq_coeff 𝔭 hK h𝔭𝔑

lemma bianchiHeckeTPrime_toBianchiModularForm (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    bianchiHeckeTPrime σ k 𝔑 𝔭.1 𝔭.2.2 N.toBianchiModularForm =
      ((((Ideal.absNorm 𝔭.1 : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ)⁻¹ * N.eigenvalue 𝔭) •
        N.toBianchiModularForm :=
  bianchiHeckeTPrime_eq_of_bianchiHeckeTPrimeArith_eq 𝔭.2.2
    (N.bianchiHeckeTPrimeArith_toBianchiModularForm 𝔭)

/-- **Multiplicity one for Bianchi newforms** (LMFDB `mf.bianchi.spaces`, `mf.bianchi.newform`): two
newforms of the same weight and level `Γ₀(𝔑)` with the same Hecke eigenvalues at the primes `𝔭 ∤ 𝔑`
have the same form. -/
lemma toFun_eq_of_eigenvalue_eq (hK : finrank ℚ K = 2)
    (h : ∀ 𝔭, ¬𝔑 ≤ 𝔭.1 → N.eigenvalue 𝔭 = N'.eigenvalue 𝔭) : N.toFun = N'.toFun := by
  have hΦ : N.toBianchiModularForm ≠ 0 := fun h₀ ↦ N.toFun_ne_zero hK (congrArg Subtype.val h₀)
  have h₁ : N'.toBianchiModularForm = (N'.coeff 1 / N.coeff 1) • N.toBianchiModularForm :=
    eq_smul_of_mem_bianchiNewSubspace hK N.mem_bianchiNewSubspace N'.mem_bianchiNewSubspace
    hΦ N.hasWhittakerExpansion N'.hasWhittakerExpansion fun 𝔭 h𝔭 hp hsup ↦ by
      have h𝔭𝔑 : ¬𝔑 ≤ 𝔭 := fun hle ↦ hp.ne_top (by rwa [sup_eq_left.mpr hle] at hsup)
      refine ⟨_, N.bianchiHeckeTPrime_toBianchiModularForm ⟨𝔭, hp, h𝔭⟩, ?_⟩
      rw [h ⟨𝔭, hp, h𝔭⟩ h𝔭𝔑]
      exact N'.bianchiHeckeTPrime_toBianchiModularForm ⟨𝔭, hp, h𝔭⟩
  rw [N.coeff_one, N'.coeff_one, div_one, one_smul] at h₁
  exact (congrArg Subtype.val h₁).symm

lemma coeff_eq_of_eigenvalue_eq (hK : finrank ℚ K = 2)
    (h : ∀ 𝔭, ¬𝔑 ≤ 𝔭.1 → N.eigenvalue 𝔭 = N'.eigenvalue 𝔭) (hα : α ≠ 0) :
    N.coeff α = N'.coeff α := by
  rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
  have h₁ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend N'.toFun)
      N'.coeff := N'.hasWhittakerExpansion
  rw [← N.toFun_eq_of_eigenvalue_eq N' hK h] at h₁
  exact N.hasWhittakerExpansion.coeff_eq hK hx (cpow_ofNat_inv_pow _ 2) h₁ hα

variable {a : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℂ}

lemma bianchiWhittakerCoeff_one_ne_zero (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) (hF₀ : F ≠ 0)
    (ha : ∀ 𝔭, (bianchiHeckeTPrimeArith σ k 𝔑 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = a 𝔭 • F) :
    bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1 ≠ 0 :=
  coeff_one_ne_zero_of_mem_bianchiNewSubspace (Φ := ⟨F, _⟩) hK hF
    (fun h₀ ↦ hF₀ (congrArg Subtype.val h₀))
    (hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK (bianchiNewSubspace_le σ k 𝔑 hF) hk)
    fun 𝔭 h𝔭 hp _ ↦ ⟨_, bianchiHeckeTPrime_eq_of_bianchiHeckeTPrimeArith_eq h𝔭
      (Subtype.ext (ha ⟨𝔭, hp, h𝔭⟩))⟩

/-- The **newform of a nonzero eigenform of the newspace** (LMFDB `mf.bianchi.spaces`): for `K`
imaginary quadratic of class number `1` and `F ≠ 0` of the newspace of weight `k ≥ 1`, an eigenform
of every `T_𝔭`, the form `F / c(1)` is a newform (`toFun_ofEigenform`), with the same eigenvalues,
as `c(1) ≠ 0`. -/
noncomputable def ofEigenform (hK : finrank ℚ K = 2) (hk : k ≠ 0)
    (hF : F ∈ bianchiNewSubspace σ k 𝔑) (hF₀ : F ≠ 0)
    (ha : ∀ 𝔭, (bianchiHeckeTPrimeArith σ k 𝔑 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = a 𝔭 • F) : BianchiNewformOfWeight σ k 𝔑 :=
  ofBianchiWhittakerCoeff σ 𝔑 hK hk
    (F := (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1)⁻¹ • F)
    (Submodule.smul_mem _ _ hF) a (fun 𝔭 ↦ by
      have h : (⟨(bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1)⁻¹ • F,
          bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 (Submodule.smul_mem _ _ hF)⟩ :
            bianchiModularForms σ 𝔑.gamma0GL k) =
          (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1)⁻¹ •
            ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ := rfl
      rw [h, map_smul, Submodule.coe_smul, ha 𝔭, smul_comm]) <| by
    rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
    rw [((hasBianchiWhittakerExpansion_bianchiWhittakerCoeff hK (bianchiNewSubspace_le σ k 𝔑 hF)
      hk).smul _).bianchiWhittakerCoeff_eq hK hx (cpow_ofNat_inv_pow _ 2) one_ne_zero,
      Pi.smul_apply, smul_eq_mul,
      inv_mul_cancel₀ (bianchiWhittakerCoeff_one_ne_zero hK hk hF hF₀ ha)]

/-- **The form of the newform of an eigenform `F` is `F / c(1)`.** -/
lemma toFun_ofEigenform (hK : finrank ℚ K = 2) (hk : k ≠ 0) (hF : F ∈ bianchiNewSubspace σ k 𝔑)
    (hF₀ : F ≠ 0) (ha : ∀ 𝔭, (bianchiHeckeTPrimeArith σ k 𝔑 𝔭.1 𝔭.2.2
      ⟨F, bianchiNewSubspace_le_bianchiModularForms σ k 𝔑 hF⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) = a 𝔭 • F) : (ofEigenform hK hk hF hF₀ ha).toFun =
    (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend F) 1)⁻¹ • F :=
  rfl

end BianchiNewformOfWeight

end HyperbolicThreeSpace
