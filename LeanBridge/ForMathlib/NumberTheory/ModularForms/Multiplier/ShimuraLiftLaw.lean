import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraCoeffBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraDilate
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraHecke
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraPetersson

/-!
# The law of the Shimura lift `Sh_t` on `Γ₀(N / 2)`

Let `g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `4 ∣ N`, and let `t ≥ 1` be
square-free. Following Niwa, `g(t z)` lies in `S_{k/2}(N t, χ (t / ·))`, and its lift `Sh₁` is
`F_t(t w)`, with `F_t = ∑ Sh_t(a)(n) e(n w)`, since `t ∣ m² ⟺ t ∣ m`. So `F_t` has the law of weight
`2 l` and character `χ²` on the `γ ∈ Γ₀(N / 2)` with upper right entry divisible by `t`. These
generate `Γ₀(N / 2)` with the translations, under which `F_t` is invariant.

## Main definitions

* `ModularForm.shimuraLiftCharacter`: the character `χ²` modulo `N / 2`.

## Main results

* `ModularForm.shimuraCoeff_comp_natMul`: the sequence of `Sh₁` of `g(t z)`.
* `ModularForm.expSum_shimuraCoeff_smul_of_dvd`: the law of `F_t` when `t` divides the upper right
  entry.
* `ModularForm.expSum_shimuraCoeff_smul_of_mem`: the law of `F_t` on `Γ₀(N / 2)`.
-/

open Complex CongruenceSubgroup Function Matrix SpecialLinearGroup ModularGroup

open scoped Real MatrixGroups Manifold NumberTheorySymbols

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {l t : ℕ} {g : ℍ → ℂ}

lemma shimuraCharacter_dilateCharacter (h4 : 4 ∣ N) (ht : t ≠ 0) (m : ℕ) : shimuraCharacter
    (dilateCharacter χ t h4) (2 * l + 1) 1 m = shimuraCharacter χ (2 * l + 1) t m := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    omega
  simp only [shimuraCharacter, Nat.cast_one, jacobiSym.one_left]
  by_cases hu : IsUnit (m : ZMod (N * t))
  · have hu' : IsUnit (((m : ℤ)) : ZMod (N * t)) := by exact_mod_cast hu
    have h : dilateCharacter χ t h4 ((m : ℤ) : ZMod (N * t)) =
        χ ((m : ℤ) : ZMod N) * ((J((t : ℤ) | (m : ℤ).natAbs) : ℤ) : ℂ) :=
      dilateCharacter_intCast h4 ht hu'
    simp only [Int.natAbs_natCast, Int.cast_natCast] at h
    rw [h]
    ring1
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    by_cases hN : IsUnit (m : ZMod N)
    · have hc : m.Coprime N := (ZMod.isUnit_iff_coprime m N).mp hN
      have hnc : ¬m.Coprime (N * t) := fun h ↦ hu ((ZMod.isUnit_iff_coprime m _).mpr h)
      have hnt : ¬t.Coprime m := fun h ↦ hnc (hc.mul_right h.symm)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hN1 (Nat.coprime_zero_left N |>.mp hc)
      have hJ : J((t : ℤ) | m) = 0 := by
        refine jacobiSym.eq_zero_iff.mpr ⟨hm0, fun h ↦ hnt ?_⟩
        rwa [Int.gcd_natCast_natCast] at h
      rw [hJ]
      simp
    · simp [MulChar.map_nonunit _ hN]

variable [NeZero N] in
/-- **The sequence of `Sh₁` of the dilation** (LMFDB `cmf.shimura_correspondence`): for `t ≥ 1`
square-free, the coefficient of `Sh₁(g(t z))` at `n` is that of `Sh_t(g)` at `n / t` if `t ∣ n`, and
`0` otherwise. This is where `t` square-free is used: `t ∣ m² ⟺ t ∣ m`. -/
lemma shimuraCoeff_comp_natMul (h4 : 4 ∣ N) (ht : 0 < t) (hsq : Squarefree t)
    (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (n : ℕ) : shimuraCoeff
    (dilateCharacter χ t h4) (2 * l + 1) 1 (fun m ↦ (qExpansion 1 (g ∘ natMul ht)).coeff m) n =
      if t ∣ n then shimuraCoeff χ (2 * l + 1) t (fun m ↦ (qExpansion 1 g).coeff m) (n / t)
        else 0 := by
  have e : (fun m : ℕ ↦ (qExpansion 1 (g ∘ natMul ht)).coeff (1 * m ^ 2)) =
      fun m ↦ if t ∣ m then (qExpansion 1 g).coeff (t * (m / t) ^ 2) else 0 := by
    funext m
    rw [coeff_qExpansion_comp_natMul h4 ht hg, one_mul]
    by_cases hm : t ∣ m
    · rcases hm with ⟨q, rfl⟩
      have hq : (t * q) ^ 2 / t = t * q ^ 2 := by
        refine Nat.div_eq_of_eq_mul_right ht ?_
        ring1
      have hd2 : t ∣ (t * q) ^ 2 := ⟨t * q ^ 2, by ring1⟩
      simp [hd2, hq, Nat.mul_div_cancel_left _ ht]
    · have hm2 : ¬t ∣ m ^ 2 := fun h ↦ hm ((hsq.dvd_pow_iff_dvd two_ne_zero).mp h)
      simp [hm, hm2]
  have e2 : (fun d : ℕ ↦ shimuraCharacter (dilateCharacter χ t h4) (2 * l + 1) 1 d *
      (d : ℂ) ^ ((((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) : ℂ) - 1)) = fun d : ℕ ↦
        shimuraCharacter χ (2 * l + 1) t d *
          (d : ℂ) ^ ((((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) : ℂ) - 1) :=
    funext fun d ↦ by rw [shimuraCharacter_dilateCharacter h4 ht.ne']
  have h : shimuraCoeff (dilateCharacter χ t h4) (2 * l + 1) 1
      (fun m ↦ (qExpansion 1 (g ∘ natMul ht)).coeff m) = LSeries.convolution
        (fun d : ℕ ↦ shimuraCharacter χ (2 * l + 1) t d *
          (d : ℂ) ^ ((((2 * (l : ℤ) + 1 - 1) / 2 : ℤ) : ℂ) - 1))
        (fun m ↦ if t ∣ m then (qExpansion 1 g).coeff (t * (m / t) ^ 2) else 0) :=
    congrArg₂ LSeries.convolution e2 e
  rw [h]
  exact LSeries.convolution_ite_dvd_of_pos (f := fun m ↦ (qExpansion 1 g).coeff (t * m ^ 2)) ht

lemma expSum_ite_dvd (ht : 0 < t) (c : ℕ → ℂ) (w : ℍ) :
    expSum (fun n ↦ if t ∣ n then c (n / t) else 0) w = expSum c (natMul ht w) := by
  have hinj : Function.Injective fun m : ℕ ↦ t * m := fun a b h ↦ Nat.eq_of_mul_eq_mul_left ht h
  rw [expSum, expSum, ← hinj.tsum_eq]
  · refine tsum_congr fun m ↦ ?_
    simp only [dvd_mul_right, Nat.mul_div_cancel_left _ ht, coe_natMul]
    push_cast
    congr 2
    ring1
  · intro n hn
    have hnd : t ∣ n := by
      by_contra hd
      exact hn (by simp [hd])
    rcases hnd with ⟨m, rfl⟩
    exact ⟨m, rfl⟩

lemma shimuraThetaCharacter_sq (h4 : 4 ∣ N) (d : ℤ) :
    shimuraThetaCharacter χ l h4 (d : ZMod N) ^ 2 = χ (d : ZMod N) ^ 2 := by
  have h : ((thetaEpsilon d)⁻¹ ^ (2 * l)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, ← mul_assoc, pow_mul]
    have e : (thetaEpsilon d)⁻¹ ^ (2 * 2) = 1 := by
      rw [thetaEpsilon]
      split_ifs
      · simp
      · rw [inv_pow, I_pow_four, inv_one]
    rw [e, one_pow]
  rw [shimuraThetaCharacter_intCast, mul_pow, h, mul_one]

lemma dilateCharacter_sq (h4 : 4 ∣ N) (ht : t ≠ 0) {d : ℤ} (hd : IsUnit (d : ZMod (N * t))) :
    dilateCharacter χ t h4 (d : ZMod (N * t)) ^ 2 = χ (d : ZMod N) ^ 2 := by
  have hcop : IsCoprime ((N * t : ℕ) : ℤ) d := (ZMod.coe_int_isUnit_iff_isCoprime d _).mp hd
  have hgcd : (t : ℤ).gcd ((d.natAbs : ℕ) : ℤ) = 1 := by
    have h1 : IsCoprime (t : ℤ) d := hcop.of_isCoprime_of_dvd_left ⟨N, by
      push_cast
      ring1⟩
    simpa [Int.gcd, Int.natAbs_abs] using Int.isCoprime_iff_gcd_eq_one.mp h1
  have hJ : ((J((t : ℤ) | d.natAbs) : ℤ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast jacobiSym.sq_one hgcd
  rw [dilateCharacter_intCast h4 ht hd, mul_pow, hJ, mul_one]

variable [NeZero N]

private lemma sq_eq_one_of_cast_eq_one (h4 : 4 ∣ N) {x : ℤ} (hx : (x : ZMod (N / 2)) = 1) :
    (x : ZMod N) ^ 2 = 1 := by
  rcases h4 with ⟨M, rfl⟩
  have e : 4 * M / 2 = 2 * M := by omega
  rw [e] at hx
  have h1 : ((2 * M : ℕ) : ℤ) ∣ x - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hx, sub_self]
  rcases h1 with ⟨r, hr⟩
  have h2 : (x : ZMod (4 * M)) ^ 2 - 1 = (((4 * M : ℕ) : ℤ) : ZMod (4 * M)) * (r + M * r ^ 2) := by
    have h3 : x ^ 2 - 1 = ((4 * M : ℕ) : ℤ) * (r + M * r ^ 2) := by
      have h4 : x = 1 + ((2 * M : ℕ) : ℤ) * r := by linarith
      rw [h4]
      push_cast
      ring1
    have h5 : ((x ^ 2 - 1 : ℤ) : ZMod (4 * M)) =
        ((((4 * M : ℕ) : ℤ) * (r + M * r ^ 2) : ℤ) : ZMod (4 * M)) :=
      congrArg (Int.cast : ℤ → ZMod (4 * M)) h3
    push_cast at h5 ⊢
    exact h5
  rw [Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_eq_zero] at h2
  exact h2

variable (χ) in
lemma factorsThrough_sq_div_two (h4 : 4 ∣ N) :
    DirichletCharacter.FactorsThrough (χ ^ 2) (N / 2) := by
  have hdvd : N / 2 ∣ N := Nat.div_dvd_of_dvd (dvd_trans (by norm_num) h4)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rcases ZMod.intCast_surjective (u : ZMod N) with ⟨x, hx⟩
  have h1 : (x : ZMod (N / 2)) = 1 := by
    have h2 : (ZMod.unitsMap hdvd u : ZMod (N / 2)) = ((1 : (ZMod (N / 2))ˣ) : ZMod (N / 2)) :=
      congrArg Units.val hu
    rw [ZMod.unitsMap_val, ← hx, ZMod.cast_intCast hdvd] at h2
    simpa using h2
  have h3 : (u : ZMod N) ^ 2 = 1 := by
    rw [← hx]
    exact sq_eq_one_of_cast_eq_one h4 h1
  refine Units.ext ?_
  rw [MulChar.coe_toUnitHom, MulChar.pow_apply_coe, ← map_pow, h3, map_one]
  rfl

variable (χ) in
/-- The **character `χ²` modulo `N / 2`** (LMFDB `cmf.shimura_correspondence`) of the Shimura lift
of a form of character `χ` modulo `N`, for `4 ∣ N`: the character `χ²` modulo `N` factors through
`N / 2`. -/
noncomputable def shimuraLiftCharacter (h4 : 4 ∣ N) : DirichletCharacter ℂ (N / 2) :=
  (factorsThrough_sq_div_two χ h4).χ₀

private lemma isUnit_of_isUnit_div_two (h4 : 4 ∣ N) {d : ℤ} (hd : IsUnit (d : ZMod (N / 2))) :
    IsUnit (d : ZMod N) := by
  have hcop : IsCoprime ((N / 2 : ℕ) : ℤ) d := (ZMod.coe_int_isUnit_iff_isCoprime d _).mp hd
  rcases h4 with ⟨M, rfl⟩
  have e : 4 * M / 2 = 2 * M := by omega
  rw [e] at hcop
  refine (ZMod.coe_int_isUnit_iff_isCoprime d _).mpr ?_
  have e1 : ((4 * M : ℕ) : ℤ) = 2 * ((2 * M : ℕ) : ℤ) := by
    push_cast
    ring1
  rw [e1]
  have h2 : IsCoprime (2 : ℤ) d := hcop.of_isCoprime_of_dvd_left ⟨M, by
    push_cast
    ring1⟩
  exact h2.mul_left hcop

variable (χ) in
lemma shimuraLiftCharacter_intCast (h4 : 4 ∣ N) {d : ℤ} (hd : IsUnit (d : ZMod (N / 2))) :
    shimuraLiftCharacter χ h4 (d : ZMod (N / 2)) = χ (d : ZMod N) ^ 2 := by
  have hdvd : N / 2 ∣ N := Nat.div_dvd_of_dvd (dvd_trans (by norm_num) h4)
  rcases isUnit_of_isUnit_div_two h4 hd with ⟨u, hu⟩
  have h2 : (χ ^ 2) (u : ZMod N) =
      DirichletCharacter.changeLevel hdvd (factorsThrough_sq_div_two χ h4).χ₀ (u : ZMod N) :=
    DFunLike.congr_fun (factorsThrough_sq_div_two χ h4).eq_changeLevel (u : ZMod N)
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, MulChar.pow_apply_coe, hu,
    ZMod.cast_intCast hdvd] at h2
  rw [shimuraLiftCharacter, ← h2]

lemma expSum_shimuraCoeff_comp_natMul (h4 : 4 ∣ N) (ht : 0 < t) (hsq : Squarefree t)
    (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (w : ℍ) : expSum
    (shimuraCoeff (dilateCharacter χ t h4) (2 * l + 1) 1
      (fun m ↦ (qExpansion 1 (g ∘ natMul ht)).coeff m)) w =
        expSum (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) (natMul ht w) := by
  rw [← expSum_ite_dvd ht]
  congr 1
  exact funext (shimuraCoeff_comp_natMul h4 ht hsq hg)

/-- **The law of `F_t` when `t` divides the upper right entry** (LMFDB
`cmf.shimura_correspondence`), by Niwa's argument: it is the law of `Sh₁` of `g(t z)`, for
`(a, b; t c, d) ∈ Γ₀(N t / 2)`. -/
lemma expSum_shimuraCoeff_smul_of_dvd (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 (N / 2)) (hβ : (t : ℤ) ∣ γ 0 1) (w : ℍ) : expSum
    (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) (γ • w) =
      shimuraLiftCharacter χ h4 ((γ 1 1 : ℤ) : ZMod (N / 2)) * ((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l) *
        expSum (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) w := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  have ht' : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  have hc : ((N / 2 : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  rcases hc with ⟨c₀, hc₀⟩
  rcases hβ with ⟨b₀, hb₀⟩
  rcases h4 with ⟨M, hM⟩
  have h4 : 4 ∣ N := ⟨M, hM⟩
  have hN2 : ((N / 2 : ℕ) : ℤ) = 2 * M := by
    omega
  have hMt : ((N * t : ℕ) : ℤ) = 4 * ((M : ℤ) * t) := by
    rw [hM]
    push_cast
    ring1
  let γ₀ : SL(2, ℤ) := ⟨!![γ 0 0, b₀; t * γ 1 0, γ 1 1], by
    rw [det_fin_two_of]
    rw [hb₀] at hdet
    linear_combination hdet⟩
  have hc₁ : γ₀ 1 0 = 2 * ((M : ℤ) * t) * c₀ := by
    have e : γ₀ 1 0 = t * γ 1 0 := rfl
    rw [e, hc₀, hN2]
    ring1
  have hne : NeZero (N * t) := ⟨mul_ne_zero (NeZero.ne N) ht.ne'⟩
  have hV : g ∘ natMul ht ∈ halfIntegralWeightCuspSpace (dilateCharacter χ t h4) (2 * l + 1) :=
    comp_natMul_mem_halfIntegralWeightCuspSpace h4 ht hg
  let w₀ : ℍ := ⟨(w : ℂ) / t, by
    have ht'' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
    have e : ((w : ℂ) / t).im = w.im / t := by
      simp
    rw [e]
    exact div_pos w.im_pos ht''⟩
  have hw₀ : natMul ht w₀ = w := by
    ext
    rw [coe_natMul]
    exact mul_div_cancel₀ _ ht'
  have hL : expSum (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) (γ • w) =
      expSum (shimuraCoeff (dilateCharacter χ t h4) (2 * l + 1) 1
        fun m ↦ (qExpansion 1 (g ∘ natMul ht)).coeff m) (γ₀ • w₀) := by
    rw [expSum_shimuraCoeff_comp_natMul h4 ht hsq hg,
      natMul_smul ht (γ := γ₀) (γ' := γ) rfl hb₀ rfl rfl, hw₀]
  have hu₀ : IsUnit ((γ 1 1 : ℤ) : ZMod (N / 2)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr ⟨-γ 0 1 * c₀, γ 0 0, by
      rw [hc₀] at hdet
      linear_combination hdet⟩
  have hu₁ : IsUnit ((γ 1 1 : ℤ) : ZMod (N * t)) := by
    refine (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr ?_
    have h1 : IsCoprime (N : ℤ) (γ 1 1) :=
      (ZMod.coe_int_isUnit_iff_isCoprime _ _).mp (isUnit_of_isUnit_div_two h4 hu₀)
    have h2 : IsCoprime (t : ℤ) (γ 1 1) := ⟨-b₀ * γ 1 0, γ 0 0, by
      rw [hb₀] at hdet
      linear_combination hdet⟩
    rw [Nat.cast_mul]
    exact h1.mul_left h2
  have e1 : (γ₀ 1 0 : ℂ) * w₀ + γ₀ 1 1 = (γ 1 0 : ℂ) * w + γ 1 1 := by
    have e2 : ((γ₀ 1 0 : ℤ) : ℂ) = t * (γ 1 0 : ℂ) := by
      have e : γ₀ 1 0 = t * γ 1 0 := rfl
      rw [e]
      push_cast
      rfl
    have e3 : γ₀ 1 1 = γ 1 1 := rfl
    have e4 : ((w₀ : ℍ) : ℂ) = (w : ℂ) / t := rfl
    rw [e2, e3, e4]
    field_simp
  have e5 : γ₀ 1 1 = γ 1 1 := rfl
  rw [hL, expSum_shimuraCoeff_smul hV (dvd_mul_of_dvd_left h4 t) hl hMt hc₁ w₀,
    shimuraThetaCharacter_sq, e1, e5, dilateCharacter_sq h4 ht.ne' hu₁,
    expSum_shimuraCoeff_comp_natMul h4 ht hsq hg, hw₀, shimuraLiftCharacter_intCast χ h4 hu₀]

lemma expSum_T_zpow_smul (c : ℕ → ℂ) (j : ℤ) (w : ℍ) : expSum c ((T ^ j) • w) = expSum c w := by
  refine tsum_congr fun m ↦ ?_
  rw [coe_T_zpow_smul_eq]
  have e : 2 * π * I * m * ((w : ℂ) + j) = 2 * π * I * m * w + ((m * j : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    ring1
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma exists_isCoprime_add_mul {a c : ℤ} (h : IsCoprime a c) (ht : 0 < t) :
    ∃ i : ℤ, IsCoprime (a + i * c) (t : ℤ) := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨0, ?_⟩
    rcases Int.isUnit_iff.mp (isCoprime_zero_right.mp h) with rfl | rfl
    · simpa using (isCoprime_one_left : IsCoprime (1 : ℤ) (t : ℤ))
    · simpa using (isCoprime_one_left : IsCoprime (1 : ℤ) (t : ℤ)).neg_left
  have hne : NeZero (c.natAbs * t) := ⟨mul_ne_zero (Int.natAbs_ne_zero.mpr hc) ht.ne'⟩
  have hcn : (c.natAbs : ℤ) = c ∨ (c.natAbs : ℤ) = -c := by
    omega
  have hna : IsCoprime ((c.natAbs : ℕ) : ℤ) a := by
    rcases hcn with h1 | h1 <;> rw [h1]
    · exact h.symm
    · exact h.symm.neg_left
  have hu : IsUnit ((a : ℤ) : ZMod c.natAbs) := (ZMod.coe_int_isUnit_iff_isCoprime a _).mpr hna
  have hdvd : c.natAbs ∣ c.natAbs * t := dvd_mul_right _ _
  rcases ZMod.unitsMap_surjective hdvd hu.unit with ⟨V, hV⟩
  rcases ZMod.intCast_surjective (V : ZMod (c.natAbs * t)) with ⟨x, hx⟩
  have hxu : IsUnit ((x : ℤ) : ZMod (c.natAbs * t)) := hx ▸ V.isUnit
  have hxc : IsCoprime (t : ℤ) x := by
    refine ((ZMod.coe_int_isUnit_iff_isCoprime x _).mp hxu).of_isCoprime_of_dvd_left ⟨c.natAbs, ?_⟩
    push_cast
    ring1
  have hxa : (a : ZMod c.natAbs) = (x : ZMod c.natAbs) := by
    have h2 : (ZMod.unitsMap hdvd V : ZMod c.natAbs) = (hu.unit : ZMod c.natAbs) :=
      congrArg Units.val hV
    rw [ZMod.unitsMap_val, ← hx, ZMod.cast_intCast hdvd, IsUnit.unit_spec] at h2
    exact h2.symm
  rcases (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hxa with ⟨r, hr⟩
  rcases hcn with h1 | h1 <;> rw [h1] at hr
  · refine ⟨r, ?_⟩
    have e : a + r * c = x := by
      rw [← sub_eq_zero]
      linear_combination -hr
    rw [e]
    exact hxc.symm
  · refine ⟨-r, ?_⟩
    have e : a + -r * c = x := by
      rw [← sub_eq_zero]
      linear_combination -hr
    rw [e]
    exact hxc.symm

/-- **The law of the Shimura lift `Sh_t` on `Γ₀(N / 2)`** (LMFDB `cmf.shimura_correspondence`): for
`g = ∑ a(n) qⁿ ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `l ≥ 1`, `4 ∣ N`, and `t ≥ 1` square-free, the sum
`F = ∑ Sh_t(a)(n) e(n w)` satisfies `F(γ w) = χ²(d) (c w + d) ^ (2 l) F(w)` for
`γ = (a, b; c, d) ∈ Γ₀(N / 2)`. -/
lemma expSum_shimuraCoeff_smul_of_mem (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1))
    (h4 : 4 ∣ N) (hl : l ≠ 0) (ht : 0 < t) (hsq : Squarefree t) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 (N / 2)) (w : ℍ) : expSum
    (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) (γ • w) =
      shimuraLiftCharacter χ h4 ((γ 1 1 : ℤ) : ZMod (N / 2)) * ((γ 1 0 : ℂ) * w + γ 1 1) ^ (2 * l) *
        expSum (shimuraCoeff χ (2 * l + 1) t fun m ↦ (qExpansion 1 g).coeff m) w := by
  rcases exists_isCoprime_add_mul (a := γ 0 0) (c := γ 1 0) ⟨γ 1 1, -γ 0 1, by
    linear_combination γ.fin_two_mul_sub_mul_eq_one⟩ ht with ⟨i, u, v, huv⟩
  let j : ℤ := -u * (γ 0 1 + i * γ 1 1)
  let γ' : SL(2, ℤ) := T ^ i * γ * T ^ j
  have h10 : γ' 1 0 = γ 1 0 := by
    simp [γ', mul_apply, coe_T_zpow, vecMul, dotProduct]
  have h11 : γ' 1 1 = γ 1 0 * j + γ 1 1 := by
    simp [γ', mul_apply, coe_T_zpow, vecMul, dotProduct]
  have h01 : γ' 0 1 = (γ 0 0 + i * γ 1 0) * j + (γ 0 1 + i * γ 1 1) := by
    simp [γ', mul_apply, coe_T_zpow, vecMul, dotProduct]
  have hγ' : γ' ∈ Gamma0 (N / 2) := by
    rw [Gamma0_mem, h10]
    exact Gamma0_mem.mp hγ
  have hβ : (t : ℤ) ∣ γ' 0 1 := ⟨(γ 0 1 + i * γ 1 1) * v, by
    rw [h01]
    simp only [j]
    linear_combination (-(γ 0 1 + i * γ 1 1)) * huv⟩
  have hsm : γ • w = T ^ (-i) • γ' • T ^ (-j) • w := by
    rw [smul_smul, smul_smul]
    congr 1
    simp only [γ']
    group
  have hw : (((T ^ (-j)) • w : ℍ) : ℂ) = (w : ℂ) + (-j : ℤ) := coe_T_zpow_smul_eq w
  have hd : ((γ' 1 1 : ℤ) : ZMod (N / 2)) = ((γ 1 1 : ℤ) : ZMod (N / 2)) := by
    have h1 : ((γ 1 0 : ℤ) : ZMod (N / 2)) = 0 := Gamma0_mem.mp hγ
    rw [h11]
    push_cast
    rw [h1, zero_mul, zero_add]
  have hJ : (γ' 1 0 : ℂ) * (((T ^ (-j)) • w : ℍ) : ℂ) + γ' 1 1 = (γ 1 0 : ℂ) * w + γ 1 1 := by
    rw [hw, h10, h11]
    push_cast
    ring1
  rw [hsm, expSum_T_zpow_smul, expSum_shimuraCoeff_smul_of_dvd hg h4 hl ht hsq hγ' hβ, hd, hJ,
    expSum_T_zpow_smul]

end ModularForm
