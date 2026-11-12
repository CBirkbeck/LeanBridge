import LeanBridge.ForMathlib.NumberTheory.ModularForms.Gamma1Index
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralCuspBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ThetaMultiplier
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Elliptic.Gamma1
import TauCeti.NumberTheory.ModularForms.Norm.Valence

/-!
# The theta function has no zero on the upper half-plane

The theta function `θ(z) = ∑_{n ∈ ℤ} e^{2πin²z}` (`ModularForm.thetaSeries`) does not vanish on
`ℍ`. So the automorphy factor `j(γ, z) = θ(γz) / θ(z)` of the LMFDB knowl `mf.half_integral_weight`
is defined for all `γ ∈ Γ₀(4)` and `z ∈ ℍ`, and by the transformation law `θ(γz) = j(γ, z) θ(z)`
(`ModularForm.thetaSeries_smul`) it is Shimura's theta multiplier
`j(γ, z) = (c/d) ε_d⁻¹ (cz + d)^(1/2)` (`ModularForm.thetaFactor`). The spaces `M_{k/2}(N, χ)` of
`ModularForm.halfIntegralWeightSpace`, defined with Shimura's factor, are therefore the spaces of
the knowl, defined with `θ(γz) / θ(z)`.

The proof uses no product formula for `θ`. For `γ ∈ Γ₁(4)` we have `d ≡ 1 (mod 4)`, hence
`ε_d = 1` and `j(γ, z)² = cz + d` (`ModularForm.thetaFactor_sq`), so `θ²` is a modular form of
weight `1` on `Γ₁(4)`. That group has index `12` in `SL(2, ℤ)` and no point has a nontrivial
stabiliser in it (Tau Ceti's `TauCeti.eq_one_of_mem_Gamma1_of_smul_eq_self`). The valence formula
at general level (Tau Ceti's `TauCeti.ModularForm.valence_formula_finiteIndex_norm`) bounds the
order of vanishing of a nonzero form of weight `k` on `Γ` at a point `P` by
`k [SL(2, ℤ) : Γ] |Stab_Γ(P)| / 24`, which is `1 · 12 · 1 / 24 < 1` for `θ²`.

## Main definitions

* `ModularForm.thetaSqModularForm`: `θ²`, as a modular form of weight `1` on `Γ₁(4)`.

## Main results

* `ModularForm.thetaSeries_apply_ne_zero`: `θ(z) ≠ 0` for every `z ∈ ℍ`.
* `ModularForm.thetaFactor_eq_div` (LMFDB `mf.half_integral_weight`): `j(γ, z) = θ(γz) / θ(z)`
  for `γ ∈ Γ₀(4)`.
* `ModularForm.mem_halfIntegralWeightSpace_iff` (LMFDB `mf.half_integral_weight`): for odd `k` and
  `4 ∣ N`, `f ∈ M_{k/2}(N, χ)` exactly when `f` is holomorphic on `ℍ` and at the cusps and
  `f(γz) = χ(d) (θ(γz) / θ(z))^k f(z)` for every `γ ∈ Γ₀(N)`, the definition of the knowl.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), 440–481.
* N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, 2nd ed., GTM 97, Chapter IV.
-/

open Complex CongruenceSubgroup Matrix SpecialLinearGroup MulAction

open scoped MatrixGroups Manifold ModularForm

open UpperHalfPlane hiding I I_re I_im

open TauCeti

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ} {f : ℍ → ℂ} {γ : SL(2, ℤ)} (z : ℍ)

/-- The square `θ²` of the theta function, as a modular form of weight `1` on `Γ₁(4)`: on `Γ₁(4)`
the square of the theta multiplier is `cz + d`. -/
noncomputable def thetaSqModularForm : ModularForm ((Gamma1 4).map (mapGL ℝ)) 1 where
  toFun := thetaSeries * thetaSeries
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    funext z
    have h0 : γ ∈ Gamma0 4 := Gamma0_mem.mpr ((Gamma1_mem 4 γ).mp hγ).2.2
    have h1 : ((4 : ℕ) : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [((Gamma1_mem 4 γ).mp hγ).2.1, sub_self]
    have h2 : thetaFactor γ z ^ 2 = denom γ z := by
      have h5 : γ 1 1 % 4 = 1 := by omega
      simp [thetaFactor_sq, thetaEpsilon, h5]
    have e : ((thetaSeries * thetaSeries) ∣[(1 : ℤ)] mapGL ℝ γ) z =
        (thetaSeries * thetaSeries) (γ • z) * denom γ z ^ (-1 : ℤ) :=
      SL_slash_apply (f := thetaSeries * thetaSeries) γ z
    rw [e, Pi.mul_apply, Pi.mul_apply, thetaSeries_smul z h0, zpow_neg_one (denom γ z)]
    field_simp
    linear_combination thetaSeries z ^ 2 * h2
  holo' := mdifferentiable_thetaSeries.mul mdifferentiable_thetaSeries
  bdd_at_cusps' {c} hc := by
    have hc' : IsCusp c 𝒮ℒ := hc.mono (by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩)
    refine (OnePoint.isBoundedAt_iff_forall_SL2Z hc').mpr fun γ _ ↦ ?_
    rcases isBoundedAtImInfty_iff.mp (isBoundedAtImInfty_slash_thetaSeries γ) with ⟨M, A, hMA⟩
    refine isBoundedAtImInfty_iff.mpr ⟨M ^ 2, A, fun z hz ↦ ?_⟩
    have hd : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
    have e : (‖denom γ z‖ ^ (-(((1 : ℤ) : ℝ) / 2))) ^ 2 = ‖denom γ z‖ ^ (-1 : ℤ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le, ← Real.rpow_intCast]
      norm_num
    have hnorm : ‖((thetaSeries * thetaSeries) ∣[(1 : ℤ)] γ) z‖ =
        ‖halfIntegralWeightSlash 1 γ thetaSeries z‖ ^ 2 := by
      rw [SL_slash_apply, norm_mul, Pi.mul_apply, norm_mul, norm_zpow, halfIntegralWeightSlash,
        norm_mul, norm_real, Real.norm_of_nonneg (by positivity), mul_pow, e]
      ring1
    rw [hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hMA z hz) 2

private lemma card_quotient_Gamma1_four :
    Nat.card (𝒮ℒ ⧸ ((Gamma1 4).map (mapGL ℝ)).subgroupOf 𝒮ℒ) = 12 := by
  rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, MonoidHom.range_eq_map (mapGL ℝ),
    ← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective mapGL_injective,
    Subgroup.relIndex_top_right, index_Gamma1]
  have h : (Gamma0 (2 ^ 2)).index = 2 ^ (2 - 1) * (2 + 1) :=
    Gamma0_prime_power_index 2 Nat.prime_two 2 two_pos
  norm_num at h
  rw [h]
  decide

private lemma stabilizer_Gamma1_four_map_eq_bot : stabilizer ((Gamma1 4).map (mapGL ℝ)) z = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦ ?_
  rcases g with ⟨_, γ, hγ, rfl⟩
  have hz : γ • z = z := hg
  rw [Subgroup.mem_bot]
  ext1
  simp [eq_one_of_mem_Gamma1_of_smul_eq_self le_rfl hγ hz]

private lemma twentyFour_mul_le_thetaSqModularForm (hf : (⇑thetaSqModularForm : ℍ → ℂ) ≠ 0)
    (o : orbitRel.Quotient ((Gamma1 4).map (mapGL ℝ)) ℍ) :
    24 * ModularForm.orderOfVanishingOnSubgroupOrbit thetaSqModularForm o ≤
      1 * Nat.card (𝒮ℒ ⧸ ((Gamma1 4).map (mapGL ℝ)).subgroupOf 𝒮ℒ) * cardStabilizerOnOrbit o :=
  ModularForm.twentyFour_mul_orderOfVanishingOnSubgroupOrbit_le_weight_mul_index_mul_cardStabilizer
    _ hf o

/-- **The theta function has no zero on the upper half-plane**: `θ(z) ≠ 0` for every `z ∈ ℍ`. The
modular form `θ²` of weight `1` on `Γ₁(4)`, of index `12` and with trivial point stabilisers, has
order of vanishing at most `1 · 12 · 1 / 24` at every point, by the valence formula. -/
lemma thetaSeries_apply_ne_zero : thetaSeries z ≠ 0 := by
  have hf : (⇑thetaSqModularForm : ℍ → ℂ) ≠ 0 := fun h ↦ thetaSeries_ne_zero <| funext fun w ↦
    mul_self_eq_zero.mp (congrFun h w)
  have hle : 24 * orderOfVanishingAt thetaSqModularForm z ≤ 1 * 12 * 1 := by
    simpa only [ModularForm.orderOfVanishingOnSubgroupOrbit_mk, card_quotient_Gamma1_four,
      Nat.cast_ofNat, cardStabilizerOnOrbit_mk, stabilizer_Gamma1_four_map_eq_bot,
      Subgroup.card_bot, Nat.cast_one] using twentyFour_mul_le_thetaSqModularForm hf (.mk'' z)
  have h0 : orderOfVanishingAt thetaSqModularForm z = 0 :=
    (orderOfVanishingAt_nonneg (ModularFormClass.holo thetaSqModularForm) z).antisymm' (by omega)
  exact left_ne_zero_of_mul
    ((orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo thetaSqModularForm) hf).mp h0)

/-- **The theta multiplier is `θ(γz) / θ(z)`** (LMFDB `mf.half_integral_weight`): for `γ ∈ Γ₀(4)`,
Shimura's factor `j(γ, z) = (c/d) ε_d⁻¹ (cz + d)^(1/2)` is the knowl's automorphy factor, the
quotient being defined as `θ` has no zero on `ℍ`. -/
lemma thetaFactor_eq_div (hγ : γ ∈ Gamma0 4) :
    thetaFactor γ z = thetaSeries (γ • z) / thetaSeries z :=
  eq_div_of_mul_eq (thetaSeries_apply_ne_zero z) (thetaSeries_smul z hγ).symm

lemma weightFactor_eq_div_pow (hk : Odd k) (hγ : γ ∈ Gamma0 4) :
    weightFactor k γ z = (thetaSeries (γ • z) / thetaSeries z) ^ k := by
  simp [weightFactor, Int.not_even_iff_odd.mpr hk, thetaFactor_eq_div z hγ]

/-- **The knowl's definition of `M_{k/2}(N, χ)`** (LMFDB `mf.half_integral_weight`): for odd `k`
and `4 ∣ N`, a function `f : ℍ → ℂ` lies in `M_{k/2}(N, χ)` exactly when it is holomorphic,
satisfies `f(γz) = χ(d) j(γ, z)^k f(z)` for every `γ = (a, b; c, d) ∈ Γ₀(N)` with
`j(γ, z) = θ(γz) / θ(z)`, and is holomorphic at the cusps. -/
lemma mem_halfIntegralWeightSpace_iff (hk : Odd k) (hN : 4 ∣ N) : f ∈ halfIntegralWeightSpace χ k ↔
    MDiff f ∧ (∀ γ ∈ Gamma0 N, ∀ z, f (γ • z) =
      χ (γ 1 1) * (thetaSeries (γ • z) / thetaSeries z) ^ k * f z) ∧
        ∀ γ, IsBoundedAtImInfty (halfIntegralWeightSlash k γ f) :=
  and_congr_right fun _ ↦ and_congr_left fun _ ↦ forall₂_congr fun γ hγ ↦ forall_congr' fun z ↦ by
    rw [weightFactor_eq_div_pow z hk (Gamma0_le_Gamma0_of_dvd hN hγ)]

end ModularForm
