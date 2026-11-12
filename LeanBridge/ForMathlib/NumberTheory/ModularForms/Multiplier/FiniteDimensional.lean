import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.CuspDecay
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm

/-!
# Cusp forms with any multiplier form a finite-dimensional space

Let `G` be a subgroup of finite index of `SL(2, ℤ)` and `v : G → S¹` any multiplier (LMFDB
`mf.multipliersystem`), of finite or infinite order. The space `S_k(G, v)` of cusp forms of weight
`k` and multiplier `v` is finite-dimensional. For `v` of finite order this reduces to the trivial
multiplier on `ker v` (`PoincareSpanFiniteOrder.lean`); in general, `ker v` has infinite index,
and we use the norm. Fix a nonzero `f₀ ∈ S_k(G, v)` and representatives `r_q = q.out⁻¹` of the
cosets `G r` of `G` in `SL(2, ℤ)`. Each translate `f₀ ∣[k] r_q γ` is a multiple of some
`f₀ ∣[k] r_{q'}` by a value of `v`, so the norm `F₀ = ∏_q f₀ ∣[k] r_q` satisfies
`F₀ ∣[km] γ = c(γ) F₀` for every `γ ∈ SL(2, ℤ)`, with `|c(γ)| = 1`. As `F₀ ≠ 0`, `c` is a
character of `SL(2, ℤ)`, and the relations `S⁴ = 1` and `S³TSTS = T⁻¹` give `c¹² = 1`. The partial
product `g₀ = ∏_{q ≠ G} f₀ ∣[k] r_q` transforms under `G` by `c / v`, so `H = g₀ F₀¹¹` transforms by
`c¹² / v = 1 / v`, and `f ↦ f H` maps `S_k(G, v)` injectively (by the identity theorem, as
`H ≠ 0`) into a space of cusp forms with trivial multiplier on `G`, which is finite-dimensional by
Tau Ceti's `TauCeti.finiteDimensional_cuspForm_finiteIndex`.

## Main results

* `ModularForm.exists_prod_slash`: a product of translates `f ∣[k] r_q` over a set of cosets that
  `γ` permutes is multiplied by a number of absolute value `1` under `∣[km] γ`.
* `ModularForm.pow_twelve_eq_one`: a character of `SL(2, ℤ)` given by the transformation of a
  nonzero function has order dividing `12`.
* `ModularForm.finiteDimensional_multiplierCuspSpace` (LMFDB `specialfunction.poincare`):
  `S_k(G, v)` is finite-dimensional for every multiplier `v` on a subgroup `G` of finite index,
  also registered as the instance `Module.Finite ℂ (multiplierCuspSpace k (multiplierMapGL v))`.

## Implementation notes

The instance is spelt with `Module.Finite`, which `FiniteDimensional` abbreviates: spelt with
`FiniteDimensional`, it would get the generated name of the instance for multipliers of finite
order in `PoincareSpanFiniteOrder.lean`, and the two files could not be imported together.
-/

open UpperHalfPlane Filter Function Matrix SpecialLinearGroup ModularGroup MulAction Subgroup

open scoped ModularForm Manifold MatrixGroups

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} {v : G →* Circle} {k : ℤ} {f F : ℍ → ℂ} (γ : SL(2, ℤ))

lemma exists_slash_out_inv_mul (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (q : SL(2, ℤ) ⧸ G) : ∃ c : Circle, f ∣[k] (q.out⁻¹ * γ) = (c : ℂ) • f ∣[k] (γ⁻¹ • q).out⁻¹ := by
  have hmem : ((γ⁻¹ • q).out)⁻¹ * (γ⁻¹ * q.out) ∈ G := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, ← Quotient.smul_mk,
      QuotientGroup.out_eq']
  refine ⟨v ⟨_, G.inv_mem hmem⟩, ?_⟩
  have hγ : q.out⁻¹ * γ = (((γ⁻¹ • q).out)⁻¹ * (γ⁻¹ * q.out))⁻¹ * ((γ⁻¹ • q).out)⁻¹ := by
    group
  rw [hγ, SlashAction.slash_mul, hf ⟨_, G.inv_mem hmem⟩, SL_smul_slash]

lemma prod_slash_SL2 {ι : Type*} (s : Finset ι) (P : ι → ℍ → ℂ) :
    (∏ i ∈ s, P i) ∣[k * s.card] γ = ∏ i ∈ s, P i ∣[k] γ := by
  simp [SL_slash, prod_slash]

/-- **Products of translates of a form with a multiplier transform by a scalar of absolute value
`1`**: if `f ∣[k] g = v(g) f` for `g ∈ G`, `s` is a set of cosets of `G` in `SL(2, ℤ)` that `γ`
permutes, and `r_q = q.out⁻¹`, then `(∏_{q ∈ s} f ∣[k] r_q) ∣[k |s|] γ` is `c` times the product,
with `|c| = 1`: `r_q γ` lies in `G r_{γ⁻¹ q}`. -/
lemma exists_prod_slash (hf : ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (s : Finset (SL(2, ℤ) ⧸ G)) (hs : ∀ q, γ⁻¹ • q ∈ s ↔ q ∈ s) : ∃ c : Circle,
    (∏ q ∈ s, f ∣[k] q.out⁻¹) ∣[k * s.card] γ = (c : ℂ) • ∏ q ∈ s, f ∣[k] q.out⁻¹ := by
  choose c hc using fun q ↦ exists_slash_out_inv_mul γ hf q
  refine ⟨∏ q ∈ s, c q, ?_⟩
  have hprod : ∏ q ∈ s, f ∣[k] (γ⁻¹ • q).out⁻¹ = ∏ q ∈ s, f ∣[k] q.out⁻¹ :=
    Finset.prod_nbij' (γ⁻¹ • ·) (γ • ·) (fun q hq ↦ (hs q).mpr hq)
      (fun q hq ↦ (hs _).mp (by rwa [inv_smul_smul])) (fun q _ ↦ smul_inv_smul γ q)
      (fun q _ ↦ inv_smul_smul γ q) (fun q _ ↦ rfl)
  rw [prod_slash_SL2]
  simp_rw [← SlashAction.slash_mul, hc]
  rw [← hprod]
  ext τ
  simp only [Finset.prod_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  congr 1
  exact (map_prod Circle.coeHom c s).symm

lemma prod_slash_out_inv_ne_zero (hf : MDiff f) (hf0 : f ≠ 0) (s : Finset (SL(2, ℤ) ⧸ G)) :
    ∏ q ∈ s, f ∣[k] q.out⁻¹ ≠ 0 := by
  rw [Ne, prod_eq_zero_iff fun q _ ↦ by simpa [SL_slash] using hf.slash k _]
  rintro ⟨q, -, hq⟩
  refine hf0 ?_
  rw [← (SlashAction.slash_one k f : f ∣[k] (1 : SL(2, ℤ)) = f), ← inv_mul_cancel q.out,
    SlashAction.slash_mul, hq, SlashAction.zero_slash]

/-- **Characters of `SL(2, ℤ)` given by a transformation law have order dividing `12`**: if
`F ≠ 0` and `F ∣[w] γ = c(γ) F` with `|c(γ)| = 1` for every `γ ∈ SL(2, ℤ)`, then `c` is a
character and `c(γ)¹² = 1`, by the relations `S⁴ = 1` and `S³TSTS = T⁻¹` between the generators
`S` and `T` of `SL(2, ℤ)`. -/
lemma pow_twelve_eq_one {w : ℤ} (hF0 : F ≠ 0) {c : SL(2, ℤ) → Circle}
    (hc : ∀ γ : SL(2, ℤ), F ∣[w] γ = (c γ : ℂ) • F) : c γ ^ 12 = 1 := by
  have hmul (γ δ : SL(2, ℤ)) : c (γ * δ) = c γ * c δ := by
    refine Circle.ext <| smul_left_injective ℂ hF0 ?_
    beta_reduce
    rw [← hc, SlashAction.slash_mul, hc γ, SL_smul_slash, hc δ, smul_smul, Circle.coe_mul]
  let χ : SL(2, ℤ) →* Circle := MonoidHom.mk' c hmul
  have hS4 : S * S * (S * S) = 1 := by
    have hS2 : S * S = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hS2, neg_one_mul, neg_neg]
  have hA4 : (χ S : ℂ) ^ 4 = 1 := by
    have h : (χ (S * S * (S * S)) : ℂ) = χ 1 := congrArg (fun g ↦ (χ g : ℂ)) hS4
    rw [map_mul, map_mul, map_one, Circle.coe_mul, Circle.coe_mul, Circle.coe_one] at h
    linear_combination h
  have hrel : (χ S : ℂ) * ((χ S : ℂ) * ((χ S : ℂ) * ((χ T : ℂ) * ((χ S : ℂ) * ((χ T : ℂ) *
      (χ S : ℂ)))))) = (χ T : ℂ)⁻¹ := by
    simpa using congrArg (fun g ↦ (χ g : ℂ)) T_S_rel
  have hT0 : (χ T : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hAB : (χ S : ℂ) ^ 5 * (χ T : ℂ) ^ 3 = 1 := by
    field_simp at hrel
    linear_combination hrel
  have h12 : χ ^ 12 = 1 := by
    refine MonoidHom.eq_of_eqOn_dense SL2Z_generators fun x hx ↦ Circle.ext ?_
    rcases hx with rfl | rfl
    · rw [MonoidHom.pow_apply, MonoidHom.one_apply, Circle.coe_pow, Circle.coe_one]
      linear_combination ((χ S : ℂ) ^ 8 + (χ S : ℂ) ^ 4 + 1) * hA4
    · rw [MonoidHom.pow_apply, MonoidHom.one_apply, Circle.coe_pow, Circle.coe_one]
      linear_combination (-((χ T : ℂ) ^ 12) * ((χ S : ℂ) ^ 16 + (χ S : ℂ) ^ 12 + (χ S : ℂ) ^ 8 +
        (χ S : ℂ) ^ 4 + 1)) * hA4 + (((χ S : ℂ) ^ 5 * (χ T : ℂ) ^ 3) ^ 3 +
          ((χ S : ℂ) ^ 5 * (χ T : ℂ) ^ 3) ^ 2 + (χ S : ℂ) ^ 5 * (χ T : ℂ) ^ 3 + 1) * hAB
  exact congrFun (congrArg DFunLike.coe h12) γ

variable (F) in
lemma pow_slash_SL2 (n : ℕ) : (F ^ n) ∣[k * n] γ = (F ∣[k] γ) ^ n := by
  simpa [Finset.prod_const] using prod_slash_SL2 (k := k) γ (Finset.range n) (fun _ ↦ F)

lemma isBoundedAtImInfty_pow (hF : IsBoundedAtImInfty F) (n : ℕ) : IsBoundedAtImInfty (F ^ n) := by
  have h : BoundedAtFilter atImInfty (∏ _i ∈ Finset.range n, F) :=
    BoundedAtFilter.prod _ fun _ _ ↦ hF
  rw [Finset.prod_const, Finset.card_range] at h
  exact h

variable [G.FiniteIndex]

lemma isBoundedAtImInfty_prod_slash (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v))
    (s : Finset (SL(2, ℤ) ⧸ G)) :
    IsBoundedAtImInfty ((∏ q ∈ s, f ∣[k] q.out⁻¹) ∣[k * s.card] γ) := by
  rw [prod_slash_SL2]
  refine BoundedAtFilter.prod s fun q _ ↦ ?_
  rw [← SlashAction.slash_mul]
  exact (isZeroAtImInfty_slash_of_mem_multiplierCuspSpace _ hf).boundedAtFilter

variable (k v) in
/-- **Cusp forms with any multiplier form a finite-dimensional space** (LMFDB
`specialfunction.poincare`, `mf.multipliersystem`): for a subgroup `G` of finite index of
`SL(2, ℤ)` and any multiplier `v : G → S¹`, of finite or infinite order, the space `S_k(G, v)` of
cusp forms of weight `k` and multiplier `v` is finite-dimensional. For a nonzero `f₀ ∈ S_k(G, v)`,
multiplication by `H = g₀ F₀¹¹`, with `F₀` the norm of `f₀` and `g₀` its product over the cosets
other than `G`, maps `S_k(G, v)` injectively into cusp forms with trivial multiplier on `G`. -/
lemma finiteDimensional_multiplierCuspSpace :
    FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL v)) := by
  classical
  let _ : Fintype (SL(2, ℤ) ⧸ G) := Fintype.ofFinite _
  rcases eq_or_ne (multiplierCuspSpace k (multiplierMapGL v)) ⊥ with h0 | h0
  · rw [h0]
    infer_instance
  rcases (Submodule.ne_bot_iff _).mp h0 with ⟨f₀, hf₀, hf₀0⟩
  have hv₀ : ∀ g : G, f₀ ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f₀ :=
    slash_eq_smul_of_mem_multiplierCuspSpace hf₀
  set q₀ : SL(2, ℤ) ⧸ G := ((1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ G) with hq₀
  have hq₀G : q₀.out ∈ G := by
    simpa using QuotientGroup.eq.mp ((QuotientGroup.out_eq' q₀).trans hq₀)
  have hstab (g : SL(2, ℤ)) (hg : g ∈ G) (q : SL(2, ℤ) ⧸ G) :
      g⁻¹ • q ∈ Finset.univ.erase q₀ ↔ q ∈ Finset.univ.erase q₀ := by
    have hq : g⁻¹ • q₀ = q₀ := by
      rw [hq₀, Quotient.smul_mk, smul_eq_mul, mul_one]
      exact QuotientGroup.eq.mpr (by simpa using hg)
    simp only [Finset.mem_erase, Finset.mem_univ, ne_eq]
    conv_lhs => rw [← hq, smul_left_cancel_iff]
  choose c hc using fun γ ↦ exists_prod_slash γ hv₀ Finset.univ (by simp)
  choose μ hμ using fun g : G ↦ exists_prod_slash g hv₀ (Finset.univ.erase q₀) (hstab g g.2)
  have hF₀0 : ∏ q : SL(2, ℤ) ⧸ G, f₀ ∣[k] q.out⁻¹ ≠ 0 :=
    prod_slash_out_inv_ne_zero hf₀.1.1 hf₀0 _
  have hc12 (γ : SL(2, ℤ)) : c γ ^ 12 = 1 := pow_twelve_eq_one γ hF₀0 hc
  have hhol (s : Finset (SL(2, ℤ) ⧸ G)) : MDiff (∏ q ∈ s, f₀ ∣[k] q.out⁻¹) :=
    MDifferentiable.prod fun q _ ↦ by simpa [SL_slash] using hf₀.1.1.slash k _
  set g₀ : ℍ → ℂ := ∏ q ∈ Finset.univ.erase q₀, f₀ ∣[k] q.out⁻¹ with hg₀
  set F₀ : ℍ → ℂ := ∏ q : SL(2, ℤ) ⧸ G, f₀ ∣[k] q.out⁻¹ with hF₀
  set wg : ℤ := k * ((Finset.univ.erase q₀).card : ℤ) with hwg
  set wF : ℤ := k * ((Finset.univ : Finset (SL(2, ℤ) ⧸ G)).card : ℤ) with hwF
  have hw : wF = k + wg := by
    rw [hwF, hwg, Finset.card_erase_of_mem (Finset.mem_univ q₀),
      Nat.cast_sub (Finset.card_pos.mpr ⟨q₀, Finset.mem_univ q₀⟩)]
    push_cast
    ring1
  have hFg : F₀ = (v ⟨_, G.inv_mem hq₀G⟩ : ℂ) • (f₀ * g₀) := by
    rw [hF₀, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q₀), hv₀ ⟨_, G.inv_mem hq₀G⟩,
      smul_mul_assoc]
  have hcμ (g : G) : (c g : ℂ) = v g * μ g := by
    refine smul_left_injective ℂ hF₀0 ?_
    beta_reduce
    rw [← hc, hw]
    nth_rw 1 [hFg]
    rw [SL_smul_slash, mul_slash_SL2, hv₀ g, hμ g, hFg]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply]
    ring1
  have hpow (γ : SL(2, ℤ)) : (F₀ ^ 11) ∣[wF * 11] γ = (F₀ ∣[wF] γ) ^ 11 := by
    simpa using pow_slash_SL2 (k := wF) F₀ γ 11
  have hH : MDiff (g₀ * F₀ ^ 11) := (hhol _).mul ((hhol _).pow 11)
  have hzero (f : ℍ → ℂ) (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v))
      {c' : OnePoint ℝ} (hc' : IsCusp c' (G.map (mapGL ℝ))) :
      c'.IsZeroAt (f * (g₀ * F₀ ^ 11)) (k + (wg + wF * 11)) := by
    rw [IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc'
    refine (OnePoint.isZeroAt_iff_forall_SL2Z hc').mpr fun γ _ ↦ ?_
    rw [mul_slash_SL2, mul_slash_SL2, hpow]
    exact (isZeroAtImInfty_slash_of_mem_multiplierCuspSpace γ hf).mul_boundedAtFilter
      ((isBoundedAtImInfty_prod_slash γ hf₀ _).mul
        (isBoundedAtImInfty_pow (isBoundedAtImInfty_prod_slash γ hf₀ _) 11))
  have hmem (f : ℍ → ℂ) (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v)) :
      f * (g₀ * F₀ ^ 11) ∈
        multiplierCuspSpace (k + (wg + wF * 11)) (multiplierMapGL (1 : G →* Circle)) := by
    refine ⟨⟨hf.1.1.mul hH, ?_, fun hc' g hg ↦ (hzero f hf hc' g hg).boundedAtFilter⟩,
      fun hc' ↦ hzero f hf hc'⟩
    rintro ⟨_, g, hg, rfl⟩
    have hgl : (f * (g₀ * F₀ ^ 11)) ∣[k + (wg + wF * 11)] g = f * (g₀ * F₀ ^ 11) := by
      rw [mul_slash_SL2, mul_slash_SL2, hpow, slash_eq_smul_of_mem_multiplierCuspSpace hf ⟨g, hg⟩,
        hμ ⟨g, hg⟩, hc g]
      ext τ
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply]
      have h1 : (v ⟨g, hg⟩ : ℂ) * μ ⟨g, hg⟩ * (c g : ℂ) ^ 11 = 1 := by
        rw [← hcμ ⟨g, hg⟩, ← pow_succ', ← Circle.coe_pow, hc12, Circle.coe_one]
      linear_combination (f τ * (g₀ τ * F₀ τ ^ 11)) * h1
    rw [multiplierMapGL, MonoidHom.one_comp, MonoidHom.one_apply, Circle.coe_one, one_smul]
    exact hgl
  have hH0 : g₀ * F₀ ^ 11 ≠ 0 := by
    rw [Ne, mul_eq_zero_iff (hhol _) ((hhol _).pow 11)]
    rintro (h | h)
    · exact prod_slash_out_inv_ne_zero hf₀.1.1 hf₀0 _ h
    · exact hF₀0 (IsNilpotent.eq_zero ⟨11, h⟩)
  let Φ : multiplierCuspSpace k (multiplierMapGL v) →ₗ[ℂ]
      multiplierCuspSpace (k + (wg + wF * 11)) (multiplierMapGL (1 : G →* Circle)) :=
    { toFun f := ⟨f * (g₀ * F₀ ^ 11), hmem f f.2⟩
      map_add' f f' := Subtype.ext (add_mul _ _ _)
      map_smul' a f := Subtype.ext (smul_mul_assoc _ _ _) }
  refine FiniteDimensional.of_injective Φ fun f f' hff' ↦ Subtype.ext ?_
  have h : ((f : ℍ → ℂ) - f') * (g₀ * F₀ ^ 11) = 0 := by
    rw [sub_mul]
    exact sub_eq_zero.mpr (congrArg Subtype.val hff')
  rcases (mul_eq_zero_iff (f.2.1.1.sub f'.2.1.1) hH).mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hH0

instance : Module.Finite ℂ (multiplierCuspSpace k (multiplierMapGL v)) :=
  finiteDimensional_multiplierCuspSpace v k

end ModularForm
