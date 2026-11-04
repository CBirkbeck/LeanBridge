import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLift
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# The adelic lift of a cusp form is cuspidal

Let `N ≥ 1` and `k` be integers, `f` a cusp form of level `Γ₁(N)` and weight `k`, and `φ_f` its
adelic lift `AdelicGL2.adelicLift` to `GL₂(𝔸_ℚ)`. This file proves that `φ_f` is cuspidal: its
constant term `∫_{𝔸_ℚ / ℚ} φ_f(n(x) g) dx` vanishes for every `g ∈ GL₂(𝔸_ℚ)`, where
`n(x) = (1, x; 0, 1)`.

Write `g = γ x u` with `γ ∈ GL₂(ℚ)`, `x ∈ GL₂(ℝ)` of positive determinant and `u ∈ K₁(N)`. For
`t ∈ ℝ`, `n(t) g = γ (γ⁻¹ n(t) γ x) u`, so `φ_f(n(t) g)` is a constant times `F(t + z)`, or its
complex conjugate, for a point `z` of `ℍ` and the translate `F = f ∣[k] γ⁻¹`, a cusp form of the
arithmetic group `γ Γ₁(N) γ⁻¹`. The integral of `F` along a horizontal segment whose length is the
strict width `T` of this group is `T` times the constant coefficient of its `q`-expansion, which
vanishes. As `ℚ` is dense in `𝔸_ℚ^f`, every adele is `q + s + λ` with `q ∈ ℚ`, `s ∈ ℝ` and `λ` a
finite adele such that `g⁻¹ n(λ) g ∈ K₁(N)`, so `φ_f(n(a + t) g) = φ_f(n(s + t) g)` and the
integral of `t ↦ φ_f(n(a + t) g)` over `[0, T]` vanishes for every adele `a`. The Haar measure of
the compact group `𝔸_ℚ / ℚ` being invariant, `T` times the constant term at `g` is the integral over
`𝔸_ℚ / ℚ` of these integrals, by Fubini's theorem, so it vanishes.

## Main definitions

* `AdelicGL2.realAdele`: the adele `(t, 0)` of `𝔸_ℚ`, for `t ∈ ℝ`.

## Main results

* `AdelicGL2.intervalIntegral_cuspForm_vadd_eq_zero`: the integral of a cusp form of an arithmetic
  group along a horizontal segment of length its strict width vanishes.
* `AdelicGL2.continuous_adelicLift`: the adelic lift of a cusp form is continuous.
* `AdelicGL2.isCuspidal_adelicLift`: the adelic lift of a cusp form is cuspidal.
-/

open ConjAct IsDedekindDomain MeasureTheory NumberField Subgroup UpperHalfPlane

open Matrix hiding mul_inv_rev one_zpow zpow_mul zpow_neg

open GeneralLinearGroup (continuous_upperRightHom upperRightHom)

open mixedEmbedding (mixedSpace)

open scoped AdeleRing Pointwise

namespace AdelicGL2

variable {N : ℕ} [NeZero N] {k : ℤ} (t : ℝ)

section Classical

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] (f : CuspForm 𝒢 k) (B : GL (Fin 2) ℝ)

lemma intervalIntegral_σ (G : ℝ → ℂ) (a b : ℝ) :
    ∫ t in a..b, σ B (G t) = σ B (∫ t in a..b, G t) := by
  simp only [σ]
  split_ifs
  · simp
  · simp [intervalIntegral.intervalIntegral_conj]

/-- **A cusp form integrates to zero along a horizontal period**: for a cusp form `f` of an
arithmetic group of strict width `T` at `∞`, `∫_0^T f(t + z) dt = 0` for every `z ∈ ℍ`, as it is
`T` times the constant coefficient of the `q`-expansion of `f`. -/
lemma intervalIntegral_cuspForm_vadd_eq_zero (z : ℍ) :
    ∫ t in 0..𝒢.strictWidthInfty, f (t +ᵥ z) = 0 := by
  have hT : 0 < 𝒢.strictWidthInfty := 𝒢.strictWidthInfty_pos
  have hp : 𝒢.strictWidthInfty ∈ 𝒢.strictPeriods := 𝒢.strictWidthInfty_mem_strictPeriods
  have hG : Function.Periodic (fun t : ℝ ↦ f (t +ᵥ z)) 𝒢.strictWidthInfty := fun t ↦ by
    dsimp only
    rw [add_comm, add_vadd]
    exact SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f _ hp
  have hI (s : ℝ) : (⟨s + z.im * Complex.I, by simpa using z.im_pos⟩ : ℍ) = (-z.re + s) +ᵥ z := by
    ext
    rw [coe_vadd]
    apply Complex.ext <;> simp
  have h : (qExpansion 𝒢.strictWidthInfty f).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero f hT hp
  rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral f hT hp 0 z.im_pos] at h
  simp only [hI, pow_zero, div_one, one_mul, mul_eq_zero, one_div, inv_eq_zero,
    Complex.ofReal_eq_zero] at h
  rw [intervalIntegral.integral_comp_add_left (fun t ↦ f (t +ᵥ z)), add_zero,
    hG.intervalIntegral_add_eq (-z.re) 0, zero_add] at h
  exact h.resolve_left hT.ne'

open TauCeti in
lemma normalizedSlash_upperRightHom_mul (G : ℍ → ℂ) : normalizedSlash k G (upperRightHom t * B) =
    ((Real.sqrt |(B.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) *
        (σ B (G (t +ᵥ B • I)) * |(B.det : ℝ)| ^ (k - 1) * denom B I ^ (-k)) := by
  rw [normalizedSlash_mul, det_upperRightHom, Units.val_one, abs_one, Real.sqrt_one, one_zpow,
    Complex.ofReal_one, one_mul, normalizedSlash, ModularForm.slash_apply,
    ModularForm.slash_upperRightHom_apply]

lemma intervalIntegral_normalizedSlash_upperRightHom_mul :
    ∫ t in 0..𝒢.strictWidthInfty, normalizedSlash k f (upperRightHom t * B) = 0 := by
  simp_rw [normalizedSlash_upperRightHom_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral_σ, intervalIntegral_cuspForm_vadd_eq_zero,
    map_zero, zero_mul, zero_mul, mul_zero]

end Classical

section Unipotent

variable {F : Type*} [Field F] [NumberField F] (a : 𝔸[F])

lemma toInf_unipotent : toInf F (unipotent a) = upperRightHom (adeleEquiv F a).1 :=
  map_upperRightHom a _

lemma toFin_unipotent : toFin F (unipotent a) = upperRightHom (adeleEquiv F a).2 :=
  map_upperRightHom a _

lemma ofFin_mul_eq_mul_ofFin (y : GL (Fin 2) 𝔸ᶠ[F]) (g : AdelicGL2 F) :
    ofFin F y * g = g * ofFin F ((toFin F g)⁻¹ * y * toFin F g) := by
  refine ext_toInf_toFin ?_ ?_ <;> simp [mul_assoc]

end Unipotent

/-- The adele `(t, 0)` of `𝔸_ℚ`, with infinite component `t ∈ ℝ` and finite component `0`. -/
noncomputable def realAdele : 𝔸[ℚ] :=
  (adeleEquiv ℚ).symm (ratMixedEquiv.symm t, 0)

lemma realAdele_add (s : ℝ) : realAdele (t + s) = realAdele t + realAdele s := by
  rw [realAdele, realAdele, realAdele, ← map_add, Prod.mk_add_mk, add_zero, map_add]

lemma continuous_realAdele : Continuous realAdele :=
  ((InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm ℚ).comp
    continuous_ratMixedEquiv_symm).prodMk continuous_const

lemma adeleEquiv_realAdele : adeleEquiv ℚ (realAdele t) = (ratMixedEquiv.symm t, 0) :=
  (adeleEquiv ℚ).apply_symm_apply _

lemma unipotent_realAdele :
    unipotent (realAdele t) = ofInf ℚ (upperRightHom (ratMixedEquiv.symm t)) := by
  refine ext_toInf_toFin ?_ ?_
  · rw [toInf_unipotent, adeleEquiv_realAdele, toInf_ofInf]
  · rw [toFin_unipotent, adeleEquiv_realAdele, toFin_ofInf, AddChar.map_zero_eq_one]

lemma ratInfEquiv_upperRightHom (w : mixedSpace ℚ) :
    ratInfEquiv (upperRightHom w) = upperRightHom (ratMixedEquiv w) :=
  map_upperRightHom w (ratMixedEquiv : mixedSpace ℚ →+* ℝ)

variable {b : 𝔸[ℚ]}

variable (b) in
lemma unipotent_sub_realAdele : unipotent (b - realAdele (ratMixedEquiv (adeleEquiv ℚ b).1)) =
    ofFin ℚ (upperRightHom (adeleEquiv ℚ b).2) := by
  refine ext_toInf_toFin ?_ ?_
  · simp [toInf_unipotent, adeleEquiv_realAdele]
  · simp [toFin_unipotent, adeleEquiv_realAdele]

variable (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)) k)
  (g : AdelicGL2 ℚ)

lemma adelicLift_unipotent_realAdele_add_mul (hb : (toFin ℚ g)⁻¹ *
    upperRightHom (adeleEquiv ℚ b).2 * toFin ℚ g ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    adelicLift N k f (unipotent (realAdele t + b) * g) =
      adelicLift N k f (unipotent (realAdele (t + ratMixedEquiv (adeleEquiv ℚ b).1)) * g) := by
  have he : realAdele t + b = realAdele (t + ratMixedEquiv (adeleEquiv ℚ b).1) +
      (b - realAdele (ratMixedEquiv (adeleEquiv ℚ b).1)) := by
    rw [realAdele_add]
    abel
  rw [he, unipotent_add, unipotent_sub_realAdele, mul_assoc, ofFin_mul_eq_mul_ofFin, ← mul_assoc,
    adelicLift_mul_ofFin (slash_mapGL_eq_of_mem_gamma1 f) _ hb]

lemma exists_adelicLift_unipotent_add_mul (a : 𝔸[ℚ]) : ∃ s : ℝ, ∀ t : ℝ,
    adelicLift N k f (unipotent (realAdele t + a) * g) =
      adelicLift N k f (unipotent (realAdele (t + s)) * g) := by
  let U : Set 𝔸ᶠ[ℚ] := {y | (toFin ℚ g)⁻¹ * upperRightHom ((adeleEquiv ℚ a).2 - y) * toFin ℚ g ∈
    levelOne (Ideal.span {(N : 𝓞 ℚ)})}
  have hU : IsOpen U := (isOpen_levelOne (span_natCast_ne_bot N)).preimage <|
    (continuous_const.mul (continuous_upperRightHom.comp (continuous_const.sub continuous_id))).mul
      continuous_const
  have hne : U.Nonempty := ⟨(adeleEquiv ℚ a).2, by
    simp only [U, Set.mem_ofPred_eq, sub_self, AddChar.map_zero_eq_one, mul_one, inv_mul_cancel,
      one_mem]⟩
  rcases (FiniteAdeleRing.denseRange_algebraMap (𝓞 ℚ) ℚ).exists_mem_open hU hne with ⟨q, hq⟩
  have hq' : (toFin ℚ g)⁻¹ * upperRightHom (adeleEquiv ℚ (a - algebraMap ℚ 𝔸[ℚ] q)).2 *
      toFin ℚ g ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)}) := hq
  refine ⟨ratMixedEquiv (adeleEquiv ℚ (a - algebraMap ℚ 𝔸[ℚ] q)).1, fun t ↦ ?_⟩
  have he : realAdele t + a = algebraMap ℚ 𝔸[ℚ] q + (realAdele t + (a - algebraMap ℚ 𝔸[ℚ] q)) := by
    abel
  rw [he, unipotent_add, ← ofGlobal_upperRightHom, mul_assoc,
    adelicLift_ofGlobal_mul (slash_mapGL_eq_of_mem_gamma1 f)]
  exact adelicLift_unipotent_realAdele_add_mul t f _ hq'

lemma adelicLift_unipotent_realAdele_mul (γ : GL (Fin 2) ℚ) {x : GL (Fin 2) (mixedSpace ℚ)}
    (hx : 0 < ((ratInfEquiv x).det : ℝ)) {u : GL (Fin 2) 𝔸ᶠ[ℚ]}
    (hu : u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    adelicLift N k f (unipotent (realAdele t) * (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u)) =
      ((Real.sqrt |((γ.map (algebraMap ℚ ℝ))⁻¹.det : ℝ)| ^ (2 - k) : ℝ) : ℂ) *
          normalizedSlash k (CuspForm.translate f (γ.map (algebraMap ℚ ℝ))⁻¹)
            (upperRightHom t * (γ.map (algebraMap ℚ ℝ) * ratInfEquiv x)) := by
  have he : unipotent (realAdele t) * (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) = ofGlobal ℚ γ *
      ofInf ℚ ((toInf ℚ (ofGlobal ℚ γ))⁻¹ * upperRightHom (ratMixedEquiv.symm t) *
        toInf ℚ (ofGlobal ℚ γ) * x) * ofFin ℚ u := by
    refine ext_toInf_toFin ?_ ?_ <;> simp [unipotent_realAdele, mul_assoc]
  have hd : 0 < (((γ.map (algebraMap ℚ ℝ))⁻¹ * upperRightHom t * γ.map (algebraMap ℚ ℝ) *
      ratInfEquiv x).det : ℝ) := by
    rw [map_mul, map_mul, map_mul, map_inv, det_upperRightHom, mul_one, inv_mul_cancel, one_mul]
    exact hx
  rw [he, adelicLift_apply (slash_mapGL_eq_of_mem_gamma1 f) _ _ hu, map_mul, map_mul, map_mul,
    map_inv, ratInfEquiv_upperRightHom, RingEquiv.apply_symm_apply, toInf_ofGlobal,
    ratInfEquiv_map_mixedEmbedding, classicalFun_of_pos k _ hd, mul_assoc, mul_assoc,
    normalizedSlash_mul, CuspForm.coe_translate]

lemma exists_intervalIntegral_adelicLift_eq_zero : ∃ T > 0, ∀ a : 𝔸[ℚ], ∫ t in 0..T,
    adelicLift N k f (unipotent (realAdele t + a) * g) = 0 := by
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin_of_pos N g with ⟨γ, x, hx, u, hu, rfl⟩
  have hΓ : (toConjAct (γ.map (algebraMap ℚ ℝ))⁻¹⁻¹ •
      (CongruenceSubgroup.Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)).IsArithmetic := by
    rw [inv_inv]
    exact IsArithmetic.conj _ γ
  refine ⟨_, (toConjAct (γ.map (algebraMap ℚ ℝ))⁻¹⁻¹ •
    (CongruenceSubgroup.Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)).strictWidthInfty_pos,
    fun a ↦ ?_⟩
  rcases exists_adelicLift_unipotent_add_mul f (ofGlobal ℚ γ * ofInf ℚ x * ofFin ℚ u) a with ⟨s, hs⟩
  simp_rw [hs, adelicLift_unipotent_realAdele_mul _ f γ hx hu, AddChar.map_add_eq_mul, mul_assoc]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_normalizedSlash_upperRightHom_mul,
    mul_zero]

/-- **The adelic lift of a cusp form is continuous** on `GL₂(𝔸_ℚ)`: it is smooth in the
archimedean variable, and right invariant under the open subgroup `K₁(N)` of `GL₂(𝔸_ℚ^f)`. -/
lemma continuous_adelicLift : Continuous (adelicLift N k f) := by
  rcases exists_openSubgroup_adelicLift f with ⟨U, hU⟩
  refine continuous_iff_continuousAt.mpr fun g₀ ↦ ?_
  have hV : {g | (toFin ℚ g₀)⁻¹ * toFin ℚ g ∈ U} ∈ nhds g₀ :=
    (U.isOpen.preimage (continuous_const.mul (continuous_toFin ℚ))).mem_nhds (by simp)
  have heq : adelicLift N k f =ᶠ[nhds g₀]
      fun g ↦ adelicLift N k f (ofFin ℚ (toFin ℚ g₀) * ofInf ℚ (toInf ℚ g)) := by
    filter_upwards [hV] with g hg
    rw [← hU _ hg (ofFin ℚ (toFin ℚ g₀) * ofInf ℚ (toInf ℚ g))]
    refine congrArg _ (ext_toInf_toFin ?_ ?_) <;> simp
  refine ContinuousAt.congr ?_ heq.symm
  exact ((isSmoothAtInfinity_adelicLift_cuspForm f _).continuous.comp
    (continuous_toInf ℚ)).continuousAt

/-- **The adelic lift of a cusp form is cuspidal**: the constant term
`∫_{𝔸_ℚ / ℚ} φ_f(n(x) g) dx` of the adelic lift `φ_f` of a cusp form `f` of level `Γ₁(N)` vanishes
for every `g ∈ GL₂(𝔸_ℚ)`. It is `T⁻¹` times the integral over `𝔸_ℚ / ℚ` of the integrals of
`t ↦ φ_f(n(x + t) g)` over `[0, T]`, which vanish for a suitable `T > 0`. -/
lemma isCuspidal_adelicLift : IsCuspidal (adelicLift N k f) := fun g ↦ by
  rcases exists_intervalIntegral_adelicLift_eq_zero f g with ⟨T, hT, hT₀⟩
  rcases exists_norm_adelicLift_le f with ⟨C, hC⟩
  have hl (γ : GL (Fin 2) ℚ) (h : AdelicGL2 ℚ) :
      adelicLift N k f (ofGlobal ℚ γ * h) = adelicLift N k f h :=
    adelicLift_ofGlobal_mul (slash_mapGL_eq_of_mem_gamma1 f) γ h
  let ψ : AdeleQuotient ℚ → ℂ := fun x ↦ adelicLift N k f (unipotent (Quotient.out x) * g)
  have hψ : Continuous ψ := by
    refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr ?_
    have he : ψ ∘ QuotientAddGroup.mk = fun a ↦ adelicLift N k f (unipotent a * g) :=
      funext fun a ↦ unipotent_out_mul hl a g
    rw [he]
    exact (continuous_adelicLift f).comp ((continuous_unipotent ℚ).mul continuous_const)
  have hi : Integrable
      (Function.uncurry fun s (x : AdeleQuotient ℚ) ↦ ψ ((realAdele s : AdeleQuotient ℚ) + x))
      ((volume.restrict (Set.uIoc 0 T)).prod Measure.addHaar) := by
    rw [Set.uIoc_of_le hT.le]
    refine Integrable.of_bound ?_ C (.of_forall fun p ↦ hC _)
    exact (hψ.comp ((QuotientAddGroup.continuous_mk.comp
      (continuous_realAdele.comp continuous_fst)).add continuous_snd)).aestronglyMeasurable
  have h₁ (s : ℝ) (x : AdeleQuotient ℚ) : ψ ((realAdele s : AdeleQuotient ℚ) + x) =
      adelicLift N k f (unipotent (realAdele s + Quotient.out x) * g) := by
    have he : (realAdele s : AdeleQuotient ℚ) + x =
        ((realAdele s + Quotient.out x : 𝔸[ℚ]) : AdeleQuotient ℚ) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [he]
    exact unipotent_out_mul hl _ g
  have h : ∫ s in 0..T, ∫ x, ψ ((realAdele s : AdeleQuotient ℚ) + x) ∂Measure.addHaar =
      ∫ x, (∫ s in 0..T, ψ ((realAdele s : AdeleQuotient ℚ) + x)) ∂Measure.addHaar :=
    intervalIntegral_integral_swap hi
  simp_rw [integral_add_left_eq_self, h₁, hT₀, integral_zero, intervalIntegral.integral_const,
    sub_zero] at h
  exact (smul_eq_zero.mp h).resolve_left hT.ne'

end AdelicGL2
