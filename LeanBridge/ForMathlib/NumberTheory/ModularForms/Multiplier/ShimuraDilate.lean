import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraStrip

/-!
# The dilation `g(z) ↦ g(t z)` on forms of half-integral weight

For `t ≥ 1`, the function `d ↦ (t / |d|)` is a Dirichlet character modulo `4 t`, by quadratic
reciprocity. For `g ∈ S_{k/2}(N, χ)`, `4 ∣ N`, `k > 0`, the function `g(t z)` lies in
`S_{k/2}(N t, χ (t / ·))`, the vanishing at the cusps being a consequence of Hecke's bound.

## Main definitions

* `ModularForm.jacobiCharacter`: the character `d ↦ (t / |d|)` modulo `4 t`.
* `ModularForm.dilateCharacter`: the character `χ (t / ·)` modulo `N t`.
* `ModularForm.natMul`: the map `z ↦ t z` on `ℍ`.

## Main results

* `ModularForm.jacobiCharacter_intCast`: the value of `jacobiCharacter`.
* `ModularForm.thetaFactor_natMul`: the theta multiplier under the dilation.
* `ModularForm.comp_natMul_mem_halfIntegralWeightCuspSpace`: `g(t z) ∈ S_{k/2}(N t, χ (t / ·))`.
* `ModularForm.coeff_qExpansion_comp_natMul`: the `q`-expansion of `g(t z)`.
-/

open Complex CongruenceSubgroup Filter Function Matrix SpecialLinearGroup ModularGroup

open scoped Real MatrixGroups Manifold NumberTheorySymbols

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {l t : ℕ} {g : ℍ → ℂ}

private lemma odd_val_of_unit (u : (ZMod (4 * t))ˣ) : Odd (u : ZMod (4 * t)).val :=
  Nat.coprime_two_right.mp <|
    (ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_mul_of_dvd_left (by norm_num : 2 ∣ 4) t)

private lemma gcd_val_of_unit (u : (ZMod (4 * t))ˣ) :
    (t : ℤ).gcd ((u : ZMod (4 * t)).val : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast]
  exact ((ZMod.val_coe_unit_coprime u).coprime_dvd_right (dvd_mul_left t 4)).symm

private lemma jacobiSym_val_ne_zero (u : (ZMod (4 * t))ˣ) :
    ((J((t : ℤ) | (u : ZMod (4 * t)).val) : ℤ) : ℂ) ≠ 0 := by
  have h : J((t : ℤ) | (u : ZMod (4 * t)).val) ≠ 0 := fun h0 ↦
    (jacobiSym.eq_zero_iff.mp h0).2 (gcd_val_of_unit u)
  exact_mod_cast h

private lemma jacobiSym_eq_of_modEq {x y : ℕ} (hx : Odd x) (hy : Odd y) (h : x ≡ y [MOD 4 * t]) :
    J((t : ℤ) | x) = J((t : ℤ) | y) := by
  rw [jacobiSym.mod_right (t : ℤ) hx, jacobiSym.mod_right (t : ℤ) hy, Int.natAbs_natCast, h]

variable (t) in
/-- The **Jacobi character** `d ↦ (t / |d|)` modulo `4 t` (LMFDB `cmf.shimura_correspondence`). -/
noncomputable def jacobiCharacter : DirichletCharacter ℂ (4 * t) :=
  MulChar.ofUnitHom <| MonoidHom.mk'
    (fun u ↦ Units.mk0 ((J((t : ℤ) | (u : ZMod (4 * t)).val) : ℤ) : ℂ) (jacobiSym_val_ne_zero u))
    fun u v ↦ by
      refine Units.ext ?_
      have hx : Odd (u : ZMod (4 * t)).val := odd_val_of_unit u
      have hy : Odd (v : ZMod (4 * t)).val := odd_val_of_unit v
      have h : J((t : ℤ) | ((u * v : (ZMod (4 * t))ˣ) : ZMod (4 * t)).val) =
          J((t : ℤ) | (u : ZMod (4 * t)).val) * J((t : ℤ) | (v : ZMod (4 * t)).val) := by
        rw [Units.val_mul, ZMod.val_mul, ← jacobiSym.mul_right' _ hx.pos.ne' hy.pos.ne',
          jacobiSym.mod_right (t : ℤ) (hx.mul hy), Int.natAbs_natCast]
      simp only [Units.val_mk0, Units.val_mul]
      exact_mod_cast h

private lemma jacobiSym_four_mul_sub_one (ht : t ≠ 0) : J((t : ℤ) | 4 * t - 1) = 1 := by
  have ho : Odd (4 * t - 1) := by
    rw [Nat.odd_iff]
    omega
  have h2 : ((2 : ℤ)).gcd ((4 * t - 1 : ℕ) : ℤ) = 1 := by
    have h3 : Nat.Coprime 2 (4 * t - 1) := Nat.coprime_two_left.mpr ho
    simpa [Int.gcd] using h3
  have h4 : J(((4 : ℤ) * t) | 4 * t - 1) = J((t : ℤ) | 4 * t - 1) := by
    have e : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [jacobiSym.mul_left, e, jacobiSym.sq_one' h2, one_mul]
  have h5 : J(((4 : ℤ) * t) | 4 * t - 1) = 1 := by
    have e : ((4 : ℤ) * t) % ((4 * t - 1 : ℕ) : ℤ) = 1 % ((4 * t - 1 : ℕ) : ℤ) := by
      have e1 : ((4 * t - 1 : ℕ) : ℤ) = 4 * t - 1 := by
        omega
      rw [e1]
      have e2 : (4 : ℤ) * t = 1 + (4 * t - 1) := by
        ring1
      exact (congrArg (· % (4 * (t : ℤ) - 1)) e2).trans (Int.add_emod_right 1 (4 * (t : ℤ) - 1))
    rw [jacobiSym.mod_left' e, jacobiSym.one_left]
  rw [← h4, h5]

/-- **The value of the Jacobi character**: for `t ≥ 1` and `d` prime to `4 t`, of either sign, its
value is the Jacobi symbol `(t / |d|)`; that it does not depend on the sign of `d` is the evenness
of this character, which comes from `(t / (4 t - 1)) = 1`. -/
lemma jacobiCharacter_intCast (ht : t ≠ 0) {d : ℤ} (hd : IsUnit (d : ZMod (4 * t))) :
    jacobiCharacter t (d : ZMod (4 * t)) = ((J((t : ℤ) | d.natAbs) : ℤ) : ℂ) := by
  have hne : NeZero (4 * t) := ⟨by omega⟩
  have hcop : IsCoprime ((4 * t : ℕ) : ℤ) d := (ZMod.coe_int_isUnit_iff_isCoprime d _).mp hd
  have hom : Odd d.natAbs := by
    have hod : Odd d := by
      rcases Int.even_or_odd d with he | ho
      · have h2 : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' ⟨2 * t, by push_cast; ring1⟩ he.two_dvd
        rw [Int.isUnit_iff] at h2
        omega
      · exact ho
    exact Int.natAbs_odd.mpr hod
  rcases hd with ⟨u, hu⟩
  have hx : Odd (u : ZMod (4 * t)).val := odd_val_of_unit u
  have hval : (((u : ZMod (4 * t)).val : ℕ) : ZMod (4 * t)) = (d : ZMod (4 * t)) := by
    rw [ZMod.natCast_zmod_val, hu]
  have hmod : (((u : ZMod (4 * t)).val : ℕ) : ℤ) ≡ d [ZMOD ((4 * t : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact hval
  have h1 : J((t : ℤ) | (u : ZMod (4 * t)).val) = J((t : ℤ) | d.natAbs) := by
    rcases Int.natAbs_eq d with h | h
    · refine jacobiSym_eq_of_modEq hx hom ?_
      rw [← Int.natCast_modEq_iff, ← h]
      exact hmod
    · have h3 : (4 * t - 1) * (u : ZMod (4 * t)).val ≡ d.natAbs [MOD 4 * t] := by
        rw [← Int.natCast_modEq_iff]
        have h5 : ((4 * t : ℕ) : ℤ) ∣ d - (((u : ZMod (4 * t)).val : ℕ) : ℤ) := hmod.dvd
        refine Int.modEq_iff_dvd.mpr ?_
        rcases h5 with ⟨r, hr⟩
        refine ⟨-r - ((u : ZMod (4 * t)).val : ℕ), ?_⟩
        have e1 : ((4 * t - 1 : ℕ) : ℤ) = ((4 * t : ℕ) : ℤ) - 1 := by
          omega
        rw [Nat.cast_mul, e1]
        linear_combination h - hr
      have ho : Odd (4 * t - 1) := by
        rw [Nat.odd_iff]
        omega
      rw [← jacobiSym_eq_of_modEq (ho.mul hx) hom h3, jacobiSym.mul_right' _ ho.pos.ne' hx.pos.ne',
        jacobiSym_four_mul_sub_one ht, one_mul]
  rw [← hu, jacobiCharacter, MulChar.ofUnitHom_coe, ← h1]
  rfl

variable (χ t) in
/-- The character `χ (t / ·)` modulo `N t` of the **dilation** `g(t z)` (LMFDB
`cmf.shimura_correspondence`) of a form `g` of character `χ` modulo `N`, for `4 ∣ N`. -/
noncomputable def dilateCharacter (h4 : 4 ∣ N) : DirichletCharacter ℂ (N * t) :=
  DirichletCharacter.changeLevel (Dvd.intro t rfl) χ *
    DirichletCharacter.changeLevel (mul_dvd_mul_right h4 t) (jacobiCharacter t)

lemma dilateCharacter_intCast (h4 : 4 ∣ N) (ht : t ≠ 0) {d : ℤ} (hd : IsUnit (d : ZMod (N * t))) :
    dilateCharacter χ t h4 (d : ZMod (N * t)) = χ d * ((J((t : ℤ) | d.natAbs) : ℤ) : ℂ) := by
  have hd4 : IsUnit (d : ZMod (4 * t)) := by
    simpa using hd.map (ZMod.castHom (mul_dvd_mul_right h4 t) (ZMod (4 * t)))
  rcases hd with ⟨u, hu⟩
  rw [dilateCharacter, MulChar.mul_apply, ← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hu, ZMod.cast_intCast (Dvd.intro t rfl),
    ZMod.cast_intCast (mul_dvd_mul_right h4 t), jacobiCharacter_intCast ht hd4]

/-- The map `z ↦ t z` on the upper half plane, for `t ≥ 1`, of the **dilation** of a form (LMFDB
`cmf.shimura_correspondence`). -/
noncomputable def natMul (ht : 0 < t) (z : ℍ) : ℍ :=
  ⟨(t : ℂ) * z, by simpa using mul_pos (Nat.cast_pos.mpr ht : (0 : ℝ) < t) z.im_pos⟩

lemma coe_natMul (ht : 0 < t) (z : ℍ) : ((natMul ht z : ℍ) : ℂ) = (t : ℂ) * z :=
  rfl

lemma im_natMul (ht : 0 < t) (z : ℍ) : (natMul ht z).im = t * z.im := by
  rw [← UpperHalfPlane.coe_im, coe_natMul]
  simp

lemma mdifferentiable_comp_natMul (ht : 0 < t) (hg : MDiff g) : MDiff (g ∘ natMul ht) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hg ⊢
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have h1 : DifferentiableOn ℂ ((g ∘ ofComplex) ∘ fun z : ℂ ↦ (t : ℂ) * z) {z : ℂ | 0 < z.im} := by
    refine hg.comp (by fun_prop) fun z hz ↦ ?_
    simpa using mul_pos ht' hz
  refine h1.congr fun z hz ↦ ?_
  have e : natMul ht (ofComplex z) = ofComplex ((t : ℂ) * z) := by
    have hz' : 0 < ((t : ℂ) * z).im := by simpa using mul_pos ht' hz
    ext
    rw [coe_natMul, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
  simp only [Function.comp_apply, e]

lemma natMul_smul (ht : 0 < t) {γ γ' : SL(2, ℤ)} (h00 : γ' 0 0 = γ 0 0) (h01 : γ' 0 1 = t * γ 0 1)
    (h10 : γ 1 0 = t * γ' 1 0) (h11 : γ' 1 1 = γ 1 1) (z : ℍ) :
    natMul ht (γ • z) = γ' • natMul ht z := by
  have e : (γ' 1 0 : ℂ) * ((t : ℂ) * z) + γ 1 1 = (γ 1 0 : ℂ) * z + γ 1 1 := by
    rw [h10]
    push_cast
    ring1
  ext
  rw [coe_natMul, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply, coe_natMul]
  simp only [eq_intCast, ofReal_intCast, h00, h01, h11, e]
  push_cast
  rw [mul_div_assoc']
  congr 1
  ring1

lemma denom_natMul (ht : 0 < t) {γ γ' : SL(2, ℤ)} (h10 : γ 1 0 = t * γ' 1 0) (h11 : γ' 1 1 = γ 1 1)
    (z : ℍ) : denom γ' (natMul ht z) = denom γ z := by
  rw [ModularGroup.denom_apply, ModularGroup.denom_apply, coe_natMul, h10, h11]
  push_cast
  ring1

private lemma shimuraSymbol_mul (ht : 0 < t) (c d : ℤ) :
    shimuraSymbol (t * c) d = J((t : ℤ) | d.natAbs) * shimuraSymbol c d := by
  have ht' : (0 : ℤ) < t := Int.natCast_pos.mpr ht
  have hneg : (t : ℤ) * c < 0 ↔ c < 0 := by
    constructor
    · intro h
      by_contra hc
      exact absurd h (not_lt.mpr (mul_nonneg ht'.le (not_lt.mp hc)))
    · exact fun h ↦ mul_neg_of_pos_of_neg ht' h
  simp only [shimuraSymbol, hneg, jacobiSym.mul_left]
  split_ifs <;> ring1

/-- **The theta multiplier under the dilation**: if `γ = (a, b; t c, d)` with `d` prime to `t` and
`γ' = (a, t b; c, d)`, then `j(γ', t z) = (t / |d|) j(γ, z)`. -/
lemma thetaFactor_natMul (ht : 0 < t) {γ γ' : SL(2, ℤ)} (h10 : γ 1 0 = t * γ' 1 0)
    (h11 : γ' 1 1 = γ 1 1) (hd : (t : ℤ).gcd ((γ 1 1).natAbs : ℤ) = 1) (z : ℍ) :
    thetaFactor γ' (natMul ht z) = ((J((t : ℤ) | (γ 1 1).natAbs) : ℤ) : ℂ) * thetaFactor γ z := by
  have hsq : J((t : ℤ) | (γ 1 1).natAbs) * J((t : ℤ) | (γ 1 1).natAbs) = 1 := by
    rw [← sq]
    exact jacobiSym.sq_one hd
  have hsym : shimuraSymbol (γ' 1 0) (γ 1 1) =
      J((t : ℤ) | (γ 1 1).natAbs) * shimuraSymbol (γ 1 0) (γ 1 1) := by
    rw [h10, shimuraSymbol_mul ht, ← mul_assoc, hsq, one_mul]
  rw [thetaFactor, thetaFactor, denom_natMul ht h10 h11, h11, hsym]
  push_cast
  ring1

private lemma comp_natMul_smul (h4 : 4 ∣ N) (ht : 0 < t)
    (hg : g ∈ halfIntegralWeightSpace χ (2 * l + 1)) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N * t))
    (z : ℍ) : (g ∘ natMul ht) (γ • z) = dilateCharacter χ t h4 ((γ 1 1 : ℤ) : ZMod (N * t)) *
      weightFactor (2 * l + 1) γ z * (g ∘ natMul ht) z := by
  have hdvd : ((N * t : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  rcases hdvd with ⟨c, hc⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := γ.fin_two_mul_sub_mul_eq_one
  have hc' : γ 1 0 = t * (N * c) := by
    rw [hc]
    push_cast
    ring1
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, t * γ 0 1; N * c, γ 1 1], by
    rw [det_fin_two_of]
    linear_combination hdet + γ 0 1 * hc'⟩
  have h00 : γ' 0 0 = γ 0 0 := rfl
  have h01 : γ' 0 1 = t * γ 0 1 := rfl
  have h10 : γ 1 0 = t * γ' 1 0 := hc'
  have h11 : γ' 1 1 = γ 1 1 := rfl
  have hγ' : γ' ∈ Gamma0 N := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨c, rfl⟩
  have hcop : IsCoprime ((N * t : ℕ) : ℤ) (γ 1 1) :=
    ⟨-γ 0 1 * c, γ 0 0, by
      rw [hc] at hdet
      linear_combination hdet⟩
  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod (N * t)) :=
    (ZMod.coe_int_isUnit_iff_isCoprime _ _).mpr hcop
  have hgcd : (t : ℤ).gcd ((γ 1 1).natAbs : ℤ) = 1 := by
    have h1 : IsCoprime (t : ℤ) (γ 1 1) := hcop.of_isCoprime_of_dvd_left ⟨N, by
      push_cast
      ring1⟩
    simpa [Int.gcd, Int.natAbs_abs] using Int.isCoprime_iff_gcd_eq_one.mp h1
  simp only [Function.comp_apply]
  rw [natMul_smul ht h00 h01 h10 h11, hg.2.1 γ' hγ', weightFactor_two_mul_add_one,
    weightFactor_two_mul_add_one, thetaFactor_natMul ht h10 h11 hgcd,
    denom_natMul ht h10 h11, h11, dilateCharacter_intCast h4 ht.ne' hunit]
  ring1

variable [NeZero N]

private lemma isZeroAtImInfty_slash_comp_natMul (h4 : 4 ∣ N) (ht : 0 < t)
    (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (halfIntegralWeightSlash (2 * l + 1) γ (g ∘ natMul ht)) := by
  rcases exists_norm_mul_rpow_le_of_mem_halfIntegralWeightCuspSpace hg (by simp) h4 with
    ⟨K, hK0, hK⟩
  have ht' : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hpos : (0 : ℝ) < ((2 * l + 1 : ℤ) : ℝ) / 4 := by
    have h1 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    push_cast
    linarith
  have hlim : Tendsto (fun z : ℍ ↦ K * ((t : ℝ) * z.im) ^ (-(((2 * l + 1 : ℤ) : ℝ) / 4))) atImInfty
      (nhds 0) := by
    have h1 : Tendsto (fun z : ℍ ↦ (t : ℝ) * z.im) atImInfty atTop :=
      Tendsto.const_mul_atTop ht' tendsto_comap
    rw [← mul_zero K]
    exact ((tendsto_rpow_neg_atTop hpos).comp h1).const_mul K
  refine squeeze_zero_norm (fun z ↦ ?_) hlim
  have hJ : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have hy : 0 < z.im := z.im_pos
  have h1 : ‖g (natMul ht (γ • z))‖ * (natMul ht (γ • z)).im ^ (((2 * l + 1 : ℤ) : ℝ) / 4) ≤ K :=
    hK (natMul ht (γ • z))
  have him : (natMul ht (γ • z)).im = (t : ℝ) * z.im / ‖denom γ z‖ ^ 2 := by
    rw [im_natMul, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
    ring1
  have hty : 0 < (t : ℝ) * z.im := by positivity
  have e1 : ((t : ℝ) * z.im / ‖denom γ z‖ ^ 2) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) =
      ((t : ℝ) * z.im) ^ (((2 * l + 1 : ℤ) : ℝ) / 4) /
        ‖denom γ z‖ ^ (((2 * l + 1 : ℤ) : ℝ) / 2) := by
    rw [Real.div_rpow hty.le (by positivity), ← Real.rpow_natCast ‖denom γ z‖ 2,
      ← Real.rpow_mul hJ.le]
    congr 2
    push_cast
    ring1
  rw [him, e1] at h1
  have e2 : ‖halfIntegralWeightSlash (2 * l + 1) γ (g ∘ natMul ht) z‖ =
      ‖denom γ z‖ ^ (-(((2 * l + 1 : ℤ) : ℝ) / 2)) * ‖g (natMul ht (γ • z))‖ := by
    rw [halfIntegralWeightSlash, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]
    rfl
  rw [e2, Real.rpow_neg hJ.le, Real.rpow_neg hty.le, ← div_eq_inv_mul, ← div_eq_mul_inv,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have e3 : 0 < ‖denom γ z‖ ^ (((2 * l + 1 : ℤ) : ℝ) / 2) := by positivity
  rw [mul_div_assoc', div_le_iff₀ e3] at h1
  linarith

/-- **The dilation of a cusp form of half-integral weight** (LMFDB `cmf.shimura_correspondence`):
for `g ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `4 ∣ N` and `t ≥ 1`, one has
`g(t z) ∈ S_{k/2}(N t, χ (t / ·))`. The vanishing at the cusps comes from Hecke's bound. -/
lemma comp_natMul_mem_halfIntegralWeightCuspSpace (h4 : 4 ∣ N) (ht : 0 < t)
    (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) :
    g ∘ natMul ht ∈ halfIntegralWeightCuspSpace (dilateCharacter χ t h4) (2 * l + 1) :=
  ⟨⟨mdifferentiable_comp_natMul ht hg.1.1, fun _ hγ z ↦ comp_natMul_smul h4 ht hg.1 hγ z,
    fun γ ↦ (isZeroAtImInfty_slash_comp_natMul h4 ht hg γ).isBoundedAtImInfty⟩,
      isZeroAtImInfty_slash_comp_natMul h4 ht hg⟩

/-- **The `q`-expansion of the dilation** (LMFDB `cmf.shimura_correspondence`). -/
lemma coeff_qExpansion_comp_natMul (h4 : 4 ∣ N) (ht : 0 < t)
    (hg : g ∈ halfIntegralWeightCuspSpace χ (2 * l + 1)) (n : ℕ) :
    (qExpansion 1 (g ∘ natMul ht)).coeff n =
      if t ∣ n then (qExpansion 1 g).coeff (n / t) else 0 := by
  refine coeff_qExpansion_eq_of_hasSum (comp_natMul_mem_halfIntegralWeightCuspSpace h4 ht hg)
    (b := fun n ↦ if t ∣ n then (qExpansion 1 g).coeff (n / t) else 0) (fun z ↦ ?_) n
  have hinj : Function.Injective fun m : ℕ ↦ t * m := fun a b h ↦ Nat.eq_of_mul_eq_mul_left ht h
  refine (hinj.hasSum_iff fun x hx ↦ ?_).mp ?_
  · have hnd : ¬t ∣ x := fun ⟨m, hm⟩ ↦ hx ⟨m, hm.symm⟩
    simp [hnd]
  · convert hasSum_qExpansion_of_mem_halfIntegralWeightCuspSpace g hg (natMul ht z) using 2 with m
    · simp only [Function.comp_apply, dvd_mul_right, Nat.mul_div_cancel_left _ ht, coe_natMul]
      push_cast
      congr 2
      ring1
    · rfl

end ModularForm
