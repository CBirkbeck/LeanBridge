import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.CuspFunctionBound
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformAtkinLehner

/-!
# Finite dimensionality of Bianchi cusp forms

Let `K` be an imaginary quadratic field of class number `1`, embedded in `ℂ` by `σ`, and `𝔑 = (N)` a
nonzero ideal of `𝒪_K`. For `F` in `S_k(𝔑)` and `r ∈ GL₂(𝒪_K)`, the function
`H_r = F ∣ r ∣ (N, 0; 0, 1)` is a cuspidal function, periodic for `σ(𝒪_K)`
(`HyperbolicThreeSpace.glSlash_glUpper_bianchiLevelRaise_glSlash`). Reduction theory
(`HyperbolicThreeSpace.exists_finite_bianchiNormSq_eq`) and the decay of `H_r` show that the
invariant norm `y^k ⟨F, F⟩_k` is bounded on `ℋ₃` (`HyperbolicThreeSpace.exists_bianchiNormSq_le`),
and the Sturm bound (`HyperbolicThreeSpace.exists_bianchiNormSq_le_half`) shows that `F` vanishes
when finitely many Fourier–Bessel coefficients of the finitely many `H_r` do, whence **`S_k(𝔑)` is
finite dimensional** (`HyperbolicThreeSpace.finiteDimensional_bianchiCuspForms`), for `k ≥ 1`.

## Main results

* `HyperbolicThreeSpace.glSlash_glUpper_bianchiLevelRaise_glSlash`: the function
  `F ∣ r ∣ (N, 0; 0, 1)` is periodic for `σ(𝒪_K)`.
* `HyperbolicThreeSpace.exists_bianchiNormSq_le`: the invariant norm of a cusp form is bounded.
* `HyperbolicThreeSpace.finiteDimensional_bianchiCuspForms`: `S_k(𝔑)` is finite dimensional.
-/

open Complex Matrix Module NumberField HilbertModularGroup

open scoped ComplexConjugate MatrixGroups nonZeroDivisors Real

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] {σ : K →+* ℂ} {δ : ℂ} {k : ℕ} {c c' : 𝓞 K → ℂ}
  {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {N : (𝓞 K)⁰}

lemma mul_glUpper_mul_inv_mem_gamma0GL (r : GL (Fin 2) (𝓞 K)) (a : 𝓞 K) :
    r * glUpper ((N : 𝓞 K) * a) * r⁻¹ ∈ (Ideal.span {(N : 𝓞 K)}).gamma0GL := by
  refine mem_gamma0GL_span_iff.mpr ?_
  have h : (r * glUpper ((N : 𝓞 K) * a) * r⁻¹).val 1 0 =
      ((GeneralLinearGroup.det r)⁻¹ : (𝓞 K)ˣ).val * (N : 𝓞 K) * (-(r.val 1 0 ^ 2) * a) := by
    rw [Units.val_mul, Units.val_mul, coe_glUpper, coe_inv_gl]
    simp [mul_apply]
    ring1
  rw [h]
  exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _

lemma heckeLower_mul_glUpper (a : 𝓞 K) : heckeLower (bianchiUnit N) *
    GeneralLinearGroup.map (algebraMap (𝓞 K) K) (glUpper a) =
      GeneralLinearGroup.map (algebraMap (𝓞 K) K) (glUpper ((N : 𝓞 K) * a)) *
        heckeLower (bianchiUnit N) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeLower, coe_glUpper, mul_apply, coe_bianchiUnit]

/-- **`F ∣ r ∣ (N, 0; 0, 1)` is periodic for `σ(𝒪_K)`**, for `F` invariant under `Γ₀(N)` and
`r ∈ GL₂(𝒪_K)`, in even weight: `(N, 0; 0, 1) (1, a; 0, 1) = (1, Na; 0, 1) (N, 0; 0, 1)`, and
`r (1, Na; 0, 1) r⁻¹` lies in `Γ₀(N)`. -/
lemma glSlash_glUpper_bianchiLevelRaise_glSlash (hk : Even k)
    (hF : IsBianchiSlashInvariant σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k F) (r : GL (Fin 2) (𝓞 K))
    (a : 𝓞 K) : glSlash σ k (glUpper a) (bianchiLevelRaise σ k N (glSlash σ k r F)) =
      bianchiLevelRaise σ k N (glSlash σ k r F) := by
  have h₁ : glSlash σ k (r * glUpper ((N : 𝓞 K) * a)) F = glSlash σ k r F := by
    have e : r * glUpper ((N : 𝓞 K) * a) = r * glUpper ((N : 𝓞 K) * a) * r⁻¹ * r := by
      group
    rw [e, glSlash_mul hk, hF.glSlash_eq (mul_glUpper_mul_inv_mem_gamma0GL r a)]
  have h₂ : glSlash σ k (glUpper ((N : 𝓞 K) * a)) (glSlash σ k r F) = glSlash σ k r F := by
    rw [← glSlash_mul hk, h₁]
  rw [glSlash, bianchiLevelRaise, ← bianchiGLSlash_mul hk, heckeLower_mul_glUpper,
    bianchiGLSlash_mul hk]
  exact congrArg _ h₂

variable (N F) in
lemma bianchiNormSq_bianchiLevelRaise (z : HyperbolicThreeSpace) :
    bianchiNormSq (bianchiLevelRaise σ k N F) z =
      bianchiNormSq F (slRepresentative σ (heckeLower (bianchiUnit N)) • z) :=
  bianchiNormSq_bianchiSlash _ _ _

variable (F) in
lemma bianchiNormSq_glSlash (r : GL (Fin 2) (𝓞 K)) (z : HyperbolicThreeSpace) :
    bianchiNormSq (glSlash σ k r F) z = bianchiNormSq F
      (slRepresentative σ (GeneralLinearGroup.map (algebraMap (𝓞 K) K) r) • z) :=
  bianchiNormSq_bianchiSlash _ _ _

variable (N) in
lemma height_slRepresentative_heckeLower_smul (z : HyperbolicThreeSpace) :
    (slRepresentative σ (heckeLower (bianchiUnit N)) • z).height = z.height * ‖σ (N : 𝓞 K)‖ := by
  have hσ : σ ((bianchiUnit N : Kˣ) : K) = σ ((N : 𝓞 K) : K) := rfl
  have hs : (σ ((bianchiUnit N : Kˣ) : K) ^ (2⁻¹ : ℂ)) ^ 2 = σ ((bianchiUnit N : Kˣ) : K) :=
    cpow_ofNat_inv_pow _ 2
  have hN : σ ((bianchiUnit N : Kˣ) : K) ≠ 0 := (map_ne_zero σ).mpr (bianchiUnit N).ne_zero
  have hs₀ : σ ((bianchiUnit N : Kˣ) : K) ^ (2⁻¹ : ℂ) ≠ 0 := fun h ↦ hN <| by
    rw [← hs, h, zero_pow two_ne_zero]
  have h₁ : ‖σ ((bianchiUnit N : Kˣ) : K) ^ (2⁻¹ : ℂ)‖ ^ 2 = ‖σ ((bianchiUnit N : Kˣ) : K)‖ := by
    rw [← norm_pow, hs]
  have h₁₀ :
      (slRepresentative σ (heckeLower (bianchiUnit N)) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
    rw [coe_slRepresentative_heckeLower]
    rfl
  have h₁₁ : (slRepresentative σ (heckeLower (bianchiUnit N)) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      (σ ((bianchiUnit N : Kˣ) : K) ^ (2⁻¹ : ℂ))⁻¹ := by
    rw [coe_slRepresentative_heckeLower]
    rfl
  rw [height_smul, moebiusDenom, h₁₀, h₁₁, zero_mul, zero_add, map_zero, zero_mul, add_zero,
    normSq_eq_norm_sq, norm_inv, inv_pow, h₁, div_inv_eq_mul, hσ]

lemma norm_apply_coe_pos : 0 < ‖σ ((N : 𝓞 K) : K)‖ :=
  norm_pos_iff.mpr ((map_ne_zero σ).mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero N.2)))

lemma div_norm_le_height_inv_smul {y₀ : ℝ} {w : HyperbolicThreeSpace} (hw : y₀ ≤ w.height) :
    y₀ / ‖σ (N : 𝓞 K)‖ ≤ ((slRepresentative σ (heckeLower (bianchiUnit N)))⁻¹ • w).height := by
  rw [div_le_iff₀ norm_apply_coe_pos]
  have h₃ : (slRepresentative σ (heckeLower (bianchiUnit N)) •
      (slRepresentative σ (heckeLower (bianchiUnit N)))⁻¹ • w).height =
        ((slRepresentative σ (heckeLower (bianchiUnit N)))⁻¹ • w).height * ‖σ ((N : 𝓞 K) : K)‖ :=
    height_slRepresentative_heckeLower_smul N _
  rw [smul_inv_smul] at h₃
  rw [← h₃]
  exact hw

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma exists_span_eq {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥) : ∃ N : (𝓞 K)⁰, 𝔑 = Ideal.span {(N : 𝓞 K)} := by
  rcases (IsPrincipalIdealRing.principal 𝔑).principal with ⟨N₀, rfl⟩
  exact ⟨⟨N₀, mem_nonZeroDivisors_of_ne_zero fun h₀ ↦ h𝔑 (by simp [h₀])⟩, rfl⟩

variable [IsPrincipalIdealRing (𝓞 K)] in
lemma IsBianchiSlashInvariant.glSlash_glUpper {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥)
    (hF : IsBianchiSlashInvariant σ 𝔑.gamma0GL k F) (a : 𝓞 K) : glSlash σ k (glUpper a) F = F := by
  rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
  exact hF.glSlash_eq (glUpper_mem_gamma0GL a N)

variable [NumberField K]

lemma HasBianchiWhittakerExpansion.add (h : HasBianchiWhittakerExpansion σ δ k (extend F) c)
    (h' : HasBianchiWhittakerExpansion σ δ k (extend G) c') :
    HasBianchiWhittakerExpansion σ δ k (extend (F + G)) (c + c') := by
  intro p hp
  rw [extend_add, Pi.add_apply]
  have e (α : {α : 𝓞 K // α ≠ 0}) : bianchiWhittakerTerm σ δ k (c + c') p α =
      bianchiWhittakerTerm σ δ k c p α + bianchiWhittakerTerm σ δ k c' p α := by
    simp only [bianchiWhittakerTerm, Pi.add_apply, add_mul, add_smul]
  simpa only [e] using (h p hp).add (h' p hp)

variable [IsTotallyComplex K]

lemma isBianchiCuspFunction_bianchiLevelRaise_glSlash (hK : finrank ℚ K = 2) (hk : Even k)
    (hF : IsBianchiCuspFunction σ k F) (r : GL (Fin 2) (𝓞 K)) :
    IsBianchiCuspFunction σ k (bianchiLevelRaise σ k N (glSlash σ k r F)) :=
  (hF.slash hK hk (isSLRepresentative_slRepresentative _)).slash hK hk
    (isSLRepresentative_slRepresentative _)

variable [IsPrincipalIdealRing (𝓞 K)]

/-- **The invariant norm of a cusp form is bounded**: for `K` imaginary quadratic of class number
`1` and `F` in `S_k(𝔑)`, `𝔑 ≠ 0`, `k ≥ 1`, the function `y^k ⟨F, F⟩_k` is bounded on `ℋ₃`, by
reduction theory and the decay of the functions `F ∣ r ∣ (N, 0; 0, 1)`. -/
lemma exists_bianchiNormSq_le (hK : finrank ℚ K = 2) (hk : k ≠ 0) {𝔑 : Ideal (𝓞 K)} (h𝔑 : 𝔑 ≠ ⊥)
    (hF : F ∈ bianchiCuspForms σ 𝔑.gamma0GL k) : ∃ M : ℝ, ∀ z, bianchiNormSq F z ≤ M := by
  rcases Nat.even_or_odd k with hk' | hodd
  · rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
    rcases exists_finite_bianchiNormSq_eq σ hK h𝔑 with ⟨y₀, R, hy₀, hR, hred⟩
    rcases (mem_bianchiCuspForms_iff hK h𝔑).mp hF with ⟨hc, hinv⟩
    have hy₁ : 0 < y₀ / ‖σ ((N : 𝓞 K) : K)‖ := div_pos hy₀ norm_apply_coe_pos
    choose m hm using fun r ↦
      (isBianchiCuspFunction_bianchiLevelRaise_glSlash (N := N) hK hk' hc r
        ).exists_bianchiNormSq_le hK hk' hk
        (glSlash_glUpper_bianchiLevelRaise_glSlash hk' hinv r) hy₁
    rcases (hR.image m).bddAbove with ⟨M, hM⟩
    refine ⟨M, fun z ↦ ?_⟩
    rcases hred k F hk' hinv z with ⟨r, hr, w, hw, he⟩
    have h₁ : bianchiNormSq (glSlash σ k r F) w = bianchiNormSq
        (bianchiLevelRaise σ k N (glSlash σ k r F))
          ((slRepresentative σ (heckeLower (bianchiUnit N)))⁻¹ • w) := by
      rw [bianchiNormSq_bianchiLevelRaise, smul_inv_smul]
    rw [he, h₁]
    exact (hm r _ (div_norm_le_height_inv_smul hw)).trans (hM ⟨r, hr, rfl⟩)
  · refine ⟨0, fun z ↦ ?_⟩
    rw [hF.1.invariant.eq_zero_of_odd hodd]
    exact ((bianchiNormSq_eq_zero_iff _ z).mpr rfl).le

/-- **`S_k(𝔑)` is finite dimensional** (LMFDB `mf.bianchi.spaces`), for `K` imaginary quadratic of
class number `1`, `𝔑 ≠ 0` and `k ≥ 1`: by the Sturm bound (`exists_bianchiNormSq_le_half`), a form
vanishes when finitely many Fourier–Bessel coefficients of the finitely many functions
`F ∣ r ∣ (N, 0; 0, 1)` do. -/
lemma finiteDimensional_bianchiCuspForms (hK : finrank ℚ K = 2) (hk : k ≠ 0) {𝔑 : Ideal (𝓞 K)}
    (h𝔑 : 𝔑 ≠ ⊥) : FiniteDimensional ℂ (bianchiCuspForms σ 𝔑.gamma0GL k) := by
  rcases Nat.even_or_odd k with hk' | hodd
  · rcases exists_im_ne_zero_of_isTotallyComplex σ with ⟨x, hx⟩
    have hδ : ((discr K : ℂ) ^ (2⁻¹ : ℂ)) ^ 2 = discr K := cpow_ofNat_inv_pow _ 2
    rcases exists_span_eq h𝔑 with ⟨N, rfl⟩
    rcases exists_finite_bianchiNormSq_eq σ hK h𝔑 with ⟨y₀, R, hy₀, hR, hred⟩
    have hy₁ : 0 < y₀ / ‖σ ((N : 𝓞 K) : K)‖ := div_pos hy₀ norm_apply_coe_pos
    rcases exists_bianchiNormSq_le_half σ hK hk' hk hy₁ with ⟨B, hB⟩
    have hcf (Φ : bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
        IsBianchiCuspFunction σ k Φ := ((mem_bianchiCuspForms_iff hK h𝔑).mp Φ.2).1
    have hinv (Φ : bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k) :
        IsBianchiSlashInvariant σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k Φ :=
      ((mem_bianchiCuspForms_iff hK h𝔑).mp Φ.2).2
    have hexp (Φ : bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k)
        (r : GL (Fin 2) (𝓞 K)) :=
      ((isBianchiCuspFunction_bianchiLevelRaise_glSlash (N := N) hK hk' (hcf Φ) r
        ).hasBianchiWhittakerExpansion hK hx hk' hk hδ
          (glSlash_glUpper_bianchiLevelRaise_glSlash hk' (hinv Φ) r)
            ).hasBianchiWhittakerExpansion_bianchiWhittakerCoeff
    have hfinR : Finite R := hR.to_subtype
    have hfinA : {α : 𝓞 K | α ≠ 0 ∧ ‖σ α‖ ≤ B}.Finite :=
      (finite_setOf_norm_apply_le hK B).subset fun _ hα ↦ hα.2
    have hfinA' : Finite {α : 𝓞 K | α ≠ 0 ∧ ‖σ α‖ ≤ B} := hfinA.to_subtype
    let Ψ : bianchiCuspForms σ (Ideal.span {(N : 𝓞 K)}).gamma0GL k →ₗ[ℂ]
        (R × {α : 𝓞 K | α ≠ 0 ∧ ‖σ α‖ ≤ B} → ℂ) :=
      { toFun := fun Φ p ↦ bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
          (extend (bianchiLevelRaise σ k N (glSlash σ k p.1.1 Φ))) p.2.1
        map_add' := fun Φ Ψ ↦ by
          funext p
          have h₁ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
              (extend (bianchiLevelRaise σ k N
                (glSlash σ k p.1.1 (Φ + Ψ : bianchiCuspForms σ _ k))))
              (bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
                (extend (bianchiLevelRaise σ k N (glSlash σ k p.1.1 Φ))) +
                  bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
                    (extend (bianchiLevelRaise σ k N (glSlash σ k p.1.1 Ψ)))) := by
            rw [Submodule.coe_add, glSlash_add, bianchiLevelRaise_add]
            exact (hexp Φ p.1.1).add (hexp Ψ p.1.1)
          exact h₁.bianchiWhittakerCoeff_eq hK hx hδ p.2.2.1
        map_smul' := fun a Φ ↦ by
          funext p
          have h₁ : HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
              (extend (bianchiLevelRaise σ k N
                (glSlash σ k p.1.1 (a • Φ : bianchiCuspForms σ _ k))))
              (a • bianchiWhittakerCoeff σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k
                (extend (bianchiLevelRaise σ k N (glSlash σ k p.1.1 Φ)))) := by
            rw [Submodule.coe_smul, glSlash_smul, bianchiLevelRaise_smul]
            exact (hexp Φ p.1.1).smul a
          exact h₁.bianchiWhittakerCoeff_eq hK hx hδ p.2.2.1 }
    refine FiniteDimensional.of_injective Ψ ((injective_iff_map_eq_zero Ψ).mpr fun Φ hΦ ↦ ?_)
    rcases exists_bianchiNormSq_le hK hk h𝔑 Φ.2 with ⟨M, hM⟩
    have hbdd : BddAbove (Set.range (bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ))) :=
      ⟨M, by
        rintro _ ⟨z, rfl⟩
        exact hM z⟩
    have hne : Nonempty HyperbolicThreeSpace := ⟨.mk (WithLp.toLp 2 (0, 1)) one_pos⟩
    have hle (z : HyperbolicThreeSpace) :
        bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) z ≤
        ⨆ w, bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) w := le_ciSup hbdd z
    have hhalf (z : HyperbolicThreeSpace) :
        bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) z ≤
          (⨆ w, bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) w) / 2 := by
      rcases hred k Φ hk' (hinv Φ) z with ⟨r, hr, w, hw, he⟩
      have h₁ : bianchiNormSq (glSlash σ k r (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ)) w =
          bianchiNormSq (bianchiLevelRaise σ k N (glSlash σ k r
            (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ)))
              ((slRepresentative σ (heckeLower (bianchiUnit N)))⁻¹ • w) := by
        rw [bianchiNormSq_bianchiLevelRaise, smul_inv_smul]
      rw [he, h₁]
      refine hB _ _ _ (isBianchiCuspFunction_bianchiLevelRaise_glSlash hK hk' (hcf Φ) r)
        (glSlash_glUpper_bianchiLevelRaise_glSlash hk' (hinv Φ) r) (hexp Φ r) (fun z' ↦ ?_)
        (fun α hα hαB ↦ ?_) _ (div_norm_le_height_inv_smul hw)
      · rw [bianchiNormSq_bianchiLevelRaise, bianchiNormSq_glSlash]
        exact hle _
      · exact congrFun hΦ (⟨r, hr⟩, ⟨α, hα, hαB⟩)
    have hsup : (⨆ w, bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) w) ≤ 0 := by
      have h₁ : (⨆ w, bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) w) ≤
        (⨆ w, bianchiNormSq (Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) w) / 2 := ciSup_le hhalf
      linarith
    refine Subtype.ext (funext fun z ↦ ?_)
    exact (bianchiNormSq_eq_zero_iff _ z).mp
      (le_antisymm ((hle z).trans hsup) (bianchiNormSq_nonneg _ z))
  · have : Subsingleton (bianchiCuspForms σ (𝔑.gamma0GL) k) :=
      ⟨fun Φ Ψ ↦ Subtype.ext <| by
        rw [Φ.2.1.invariant.eq_zero_of_odd hodd, Ψ.2.1.invariant.eq_zero_of_odd hodd]⟩
    infer_instance

end HyperbolicThreeSpace
