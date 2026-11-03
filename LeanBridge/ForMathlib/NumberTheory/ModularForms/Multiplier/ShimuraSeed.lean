import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralCuspBound
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareConvergence
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraCorrespondence
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraDecomposition
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ShimuraKernel

/-!
# The Petersson integrand of Niwa's kernel as a periodisation

Let `g ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `4 ∣ N`. For `ψ = χ χ₄ ^ l` the law of `g` reads
`g(γ z) = ψ(d) j(γ, z) (c z + d) ^ l g(z)`. The kernel `Θ^(l)(z, w) = ∑ ψ⁻¹(μ) S^(l)(z, w; N C, μ)`
has the factor `j(γ, z) (c z + d) ^ l` as well, on the pairs, so that the terms at the pairs
`n (c, d)` of the Petersson integrand of `g` against `Θ^(l)` are those at `(0, n)` evaluated at
`γ z`, and a pair `(N C, μ)` with `μ` prime to `N` is `n (c, d)` for a unique `n ≥ 1` and a bottom
row `(c, d)` of `Γ₀(N)`, each coset of `Γ_∞ \ Γ₀(N)` carrying two rows `± (c, d)`.

## Main definitions

* `ModularForm.shimuraThetaCharacter`: the character `ψ = χ χ₄ ^ l`.
* `ModularForm.shimuraPairTerm`: the term of the kernel at a pair.
* `ModularForm.shimuraSeed`: the seed of the Petersson integrand.
* `ModularForm.gamma0InfPair`: the pair attached to a coset, a sign and an integer `n ≥ 1`.

## Main results

* `ModularForm.apply_smul_eq_of_mem`: the law of a form of weight `l + 1/2` in terms of `ψ`.
* `ModularForm.integrand_shimuraPairTerm_smul`: the integrand at a pair is a translate.
* `ModularForm.shimuraSeed_smul_of_apply_one_zero`: the seed is invariant under the stabiliser
  of `∞`.
* `ModularForm.integrand_shimuraTheta_eq_tsum`: the Petersson integrand is a periodisation.
-/

open Complex CongruenceSubgroup Matrix SpecialLinearGroup ModularGroup

open scoped Real MatrixGroups ComplexConjugate

open UpperHalfPlane hiding I I_re I_im

namespace ModularForm

variable {N : ℕ}

private lemma emod_four_of_isUnit (h4 : 4 ∣ N) {d : ℤ} (hd : IsUnit (d : ZMod N)) :
    d % 4 = 1 ∨ d % 4 = 3 := by
  have hc : IsCoprime (N : ℤ) d := (ZMod.coe_int_isUnit_iff_isCoprime d N).mp hd
  rcases Int.even_or_odd d with he | ho
  · have h2 : IsUnit (2 : ℤ) := hc.isUnit_of_dvd' ((by norm_num : (2 : ℤ) ∣ 4).trans
      (Int.natCast_dvd_natCast.mpr h4)) he.two_dvd
    rw [Int.isUnit_iff] at h2
    omega
  · rcases ho with ⟨m, rfl⟩
    omega

/-- The term `ψ⁻¹(μ) S^(l)(z, w; C, μ)` of **Niwa's kernel** (LMFDB `cmf.shimura_correspondence`) at
a pair `(C, μ)`. -/
noncomputable def shimuraPairTerm (ψ : DirichletCharacter ℂ N) (w : ℍ) (l : ℕ) (C μ : ℤ) (z : ℍ) :
    ℂ :=
  ψ⁻¹ (μ : ZMod N) * shimuraKernelCoeff z w C μ l

/-- The **seed** `φ(z) = ∑_{n ≥ 1} g(z) conj(ψ⁻¹(n) S^(l)(z, w; 0, n)) y^{k/2}` of the Petersson
integrand of `g` against **Niwa's kernel** (LMFDB `cmf.shimura_correspondence`). -/
noncomputable def shimuraSeed (ψ : DirichletCharacter ℂ N) (g : ℍ → ℂ) (w : ℍ) (l : ℕ) (z : ℍ) :
    ℂ :=
  ∑' n : ℕ+, halfIntegralPeterssonIntegrand (2 * l + 1) g
    (shimuraPairTerm ψ w l 0 ((n : ℕ) : ℤ)) z

variable [NeZero N] in
lemma summable_shimuraPairTerm (ψ : DirichletCharacter ℂ N) (w z : ℍ) (l : ℕ) :
    Summable fun p : ℤ × ℤ ↦ shimuraPairTerm ψ w l ((N : ℤ) * p.1) p.2 z := by
  refine (summable_inv_mul_shimuraKernelTerm ψ z w l).prod.congr fun p ↦ ?_
  dsimp only
  rw [tsum_mul_left, shimuraPairTerm, shimuraKernelCoeff]

variable (χ : DirichletCharacter ℂ N) (l : ℕ) (h4 : 4 ∣ N)

/-- The character `ψ = χ χ₄ ^ l` modulo `N` of **Niwa's kernel** (LMFDB
`cmf.shimura_correspondence`) of weight `l + 1/2` attached to `χ`, for `4 ∣ N`. -/
noncomputable def shimuraThetaCharacter : DirichletCharacter ℂ N :=
  χ * DirichletCharacter.changeLevel h4 (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) ^ l

lemma shimuraThetaCharacter_intCast (d : ℤ) :
    shimuraThetaCharacter χ l h4 (d : ZMod N) = χ d * (thetaEpsilon d)⁻¹ ^ (2 * l) := by
  by_cases hd : IsUnit (d : ZMod N)
  · have hmod : d % 4 = 1 ∨ d % 4 = 3 := emod_four_of_isUnit h4 hd
    rcases hd with ⟨u, hu⟩
    have e : (DirichletCharacter.changeLevel h4 (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))
        (d : ZMod N) = (thetaEpsilon d)⁻¹ ^ 2 := by
      rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd _ h4 u, hu, ZMod.cast_intCast h4,
        MulChar.ringHomComp_apply]
      rcases hmod with h | h
      · simp [thetaEpsilon, h, ZMod.χ₄_int_one_mod_four h]
      · have h1 : ¬d % 4 = 1 := by omega
        simp [thetaEpsilon, h1, ZMod.χ₄_int_three_mod_four h]
    rw [shimuraThetaCharacter, MulChar.mul_apply, ← hu, MulChar.pow_apply_coe, hu, e, pow_mul]
  · rw [MulChar.map_nonunit _ hd, MulChar.map_nonunit _ hd, zero_mul]

lemma shimuraThetaCharacter_natCast (m : ℕ) :
    shimuraThetaCharacter χ l h4 (m : ZMod N) = shimuraCharacter χ (2 * l + 1) 1 m := by
  have e0 : (((2 * (l : ℤ) + 1 - 1) / 2 : ℤ)) = l := by omega
  rw [shimuraCharacter, Nat.cast_one, jacobiSym.one_left, e0, zpow_natCast, Int.cast_one, mul_one]
  by_cases hd : IsUnit (m : ZMod N)
  · have hd' : IsUnit (((m : ℤ)) : ZMod N) := by exact_mod_cast hd
    have hmod : (m : ℤ) % 4 = 1 ∨ (m : ℤ) % 4 = 3 := emod_four_of_isUnit h4 hd'
    have ho : Odd m := by
      rw [Nat.odd_iff]
      omega
    have e : shimuraThetaCharacter χ l h4 (m : ZMod N) =
        χ m * (thetaEpsilon (m : ℤ))⁻¹ ^ (2 * l) := by
      simpa using shimuraThetaCharacter_intCast χ l h4 (m : ℤ)
    rw [e, jacobiSym.at_neg_one ho, pow_mul]
    rcases hmod with h | h
    · have h' : ZMod.χ₄ (m : ZMod 4) = 1 := by
        simpa using ZMod.χ₄_int_one_mod_four h
      simp [thetaEpsilon, h, h']
    · have h1 : ¬(m : ℤ) % 4 = 1 := by omega
      have h' : ZMod.χ₄ (m : ZMod 4) = -1 := by
        simpa using ZMod.χ₄_int_three_mod_four h
      simp [thetaEpsilon, h1, h']
  · simp [MulChar.map_nonunit _ hd]

variable {χ l} {g : ℍ → ℂ} {γ : SL(2, ℤ)}

variable (l γ) in
lemma weightFactor_two_mul_add_one (z : ℍ) : weightFactor (2 * l + 1) γ z = thetaFactor γ z *
    (thetaEpsilon (γ 1 1))⁻¹ ^ (2 * l) * denom γ z ^ l := by
  have e : weightFactor (2 * l + 1) γ z = thetaFactor γ z ^ (2 * l + 1) := by
    have e1 : weightFactor (2 * l + 1) γ z = thetaFactor γ z ^ (2 * (l : ℤ) + 1) := by
      simp [weightFactor]
    rw [e1]
    exact_mod_cast zpow_natCast (thetaFactor γ z) (2 * l + 1)
  rw [e, pow_succ', pow_mul, thetaFactor_sq, mul_pow, pow_mul]
  ring1

/-- **The law of a form of weight `l + 1/2`** in terms of `ψ = χ χ₄ ^ l`: for `γ ∈ Γ₀(N)`,
`g(γ z) = ψ(d) j(γ, z) (c z + d) ^ l g(z)`. -/
lemma apply_smul_eq_of_mem (hg : g ∈ halfIntegralWeightSpace χ (2 * l + 1)) (hγ : γ ∈ Gamma0 N)
    (z : ℍ) : g (γ • z) =
      shimuraThetaCharacter χ l h4 (γ 1 1 : ℤ) * thetaFactor γ z * denom γ z ^ l * g z := by
  rw [hg.2.1 γ hγ z, weightFactor_two_mul_add_one, shimuraThetaCharacter_intCast]
  ring1

variable (γ) in
lemma normSq_thetaFactor (z : ℍ) : normSq (thetaFactor γ z) = ‖denom γ z‖ := by
  have h : ‖thetaFactor γ z ^ 2‖ = ‖(thetaEpsilon (γ 1 1))⁻¹ ^ 2 * denom γ z‖ :=
    congrArg norm (thetaFactor_sq γ z)
  have hε : ‖(thetaEpsilon (γ 1 1))⁻¹‖ = 1 := by
    rw [thetaEpsilon]
    split_ifs <;> simp
  rw [norm_pow, norm_mul, norm_pow, hε, one_pow, one_mul] at h
  rwa [Complex.normSq_eq_norm_sq]

variable (l γ) in
lemma normSq_mul_im_rpow (z : ℍ) : normSq (thetaFactor γ z * denom γ z ^ l) *
    (γ • z).im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) = z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) := by
  have hJ : 0 < ‖denom γ z‖ := norm_pos_iff.mpr (denom_ne_zero γ z)
  have h1 : (γ • z).im = z.im / ‖denom γ z‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have h2 : (z.im / ‖denom γ z‖ ^ 2) ^ (((2 * l + 1 : ℤ) : ℝ) / 2) =
      z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) / ‖denom γ z‖ ^ (2 * l + 1) := by
    rw [Real.div_rpow z.im_pos.le (by positivity), ← Real.rpow_natCast ‖denom γ z‖ 2,
      ← Real.rpow_mul hJ.le, ← Real.rpow_natCast ‖denom γ z‖ (2 * l + 1)]
    congr 2
    push_cast
    ring1
  have h3 : normSq (denom γ z ^ l) = ‖denom γ z‖ ^ (2 * l) := by
    rw [map_pow, Complex.normSq_eq_norm_sq, pow_mul]
  rw [h1, h2, map_mul, normSq_thetaFactor, h3, pow_succ]
  field_simp

lemma conj_inv_apply (ψ : DirichletCharacter ℂ N) (a : ZMod N) : conj (ψ⁻¹ a) = ψ a := by
  have h : star (ψ⁻¹ a) = ψ⁻¹⁻¹ a := MulChar.star_apply' ψ⁻¹ a
  rwa [inv_inv] at h

/-- **The Petersson integrand at a pair is a translate**: for `γ = (a, b; c, d) ∈ Γ₀(N)` and an
integer `n`, the integrand of `g` against the kernel at the pair `(0, n)`, evaluated at `γ z`, is
the integrand at the pair `(n c, n d)`, evaluated at `z`. -/
lemma integrand_shimuraPairTerm_smul (hg : g ∈ halfIntegralWeightSpace χ (2 * l + 1))
    (hγ : γ ∈ Gamma0 N) (w : ℍ) (n : ℤ) (z : ℍ) : halfIntegralPeterssonIntegrand (2 * l + 1) g
      (shimuraPairTerm (shimuraThetaCharacter χ l h4) w l 0 n) (γ • z) =
        halfIntegralPeterssonIntegrand (2 * l + 1) g
          (shimuraPairTerm (shimuraThetaCharacter χ l h4) w l (n * γ 1 0) (n * γ 1 1)) z := by
  have hA' : (thetaFactor γ z * denom γ z ^ l) * conj (thetaFactor γ z * denom γ z ^ l) *
      (((γ • z).im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) =
        ((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, ← normSq_mul_im_rpow l γ z]
    push_cast
    rfl
  have e : ((n * γ 1 1 : ℤ) : ZMod N) = (n : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) := Int.cast_mul _ _
  simp only [halfIntegralPeterssonIntegrand, shimuraPairTerm]
  rw [apply_smul_eq_of_mem h4 hg hγ z,
    shimuraKernelCoeff_smul z w 0 n (Gamma0_le_Gamma0_of_dvd h4 hγ) l]
  simp only [zero_mul, zero_add, e, map_mul, conj_inv_apply] at hA' ⊢
  linear_combination (shimuraThetaCharacter χ l h4 ((γ 1 1 : ℤ) : ZMod N) * g z *
    shimuraThetaCharacter χ l h4 (n : ZMod N) *
      conj (shimuraKernelCoeff z w (n * γ 1 0) (n * γ 1 1) l)) * hA'

variable (N) in
/-- The cosets `Γ_∞ \ Γ₀(N)` of the stabiliser of the **cusp `∞`** in `Γ₀(N)`. -/
abbrev Gamma0InfCosets : Type :=
  Quotient (QuotientGroup.rightRel (cuspStabilizer (Gamma0 N) (1 : SL(2, ℤ))))

/-- The pair `ε n (c / N, d)` attached to a coset of `Γ_∞ \ Γ₀(N)`, of bottom row `(c, d)` for its
chosen representative, a **sign** `ε` and an integer `n ≥ 1`: the pairs `(C, μ)` of integers with
`μ` prime to `N` are exactly these. -/
noncomputable def gamma0InfPair (x : Gamma0InfCosets N × ℤˣ × ℕ+) : ℤ × ℤ :=
  (((x.2.1 : ℤ) * ((x.2.2 : ℕ) : ℤ)) * ((x.1.out : SL(2, ℤ)) 1 0 / N),
    ((x.2.1 : ℤ) * ((x.2.2 : ℕ) : ℤ)) * (x.1.out : SL(2, ℤ)) 1 1)

private lemma natCast_dvd_apply_one_zero (hγ : γ ∈ Gamma0 N) : (N : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)

private lemma mul_inv_apply_one_zero (A B : SL(2, ℤ)) :
    (A * B⁻¹) 1 0 = A 1 0 * B 1 1 - A 1 1 * B 1 0 := by
  simp [mul_apply, adjugate_fin_two]
  ring1

private lemma rel_of_mul_sub_eq_zero (q q' : Gamma0InfCosets N)
    (h : (q.out : SL(2, ℤ)) 1 0 * (q'.out : SL(2, ℤ)) 1 1 -
      (q.out : SL(2, ℤ)) 1 1 * (q'.out : SL(2, ℤ)) 1 0 = 0) : q' = q := by
  refine Quotient.out_equiv_out.mp (QuotientGroup.rightRel_apply.mpr ?_)
  rw [mem_cuspStabilizer_iff]
  simpa [mul_inv_apply_one_zero] using h

private lemma neg_mem_Gamma0 (hγ : γ ∈ Gamma0 N) : -γ ∈ Gamma0 N := by
  rw [Gamma0_mem] at hγ ⊢
  simp [hγ]

/-- **The seed is invariant under the stabiliser of the cusp `∞`** (LMFDB
`cmf.shimura_correspondence`). -/
lemma shimuraSeed_smul_of_apply_one_zero (hg : g ∈ halfIntegralWeightSpace χ (2 * l + 1)) (w : ℍ)
    (hγ : γ ∈ Gamma0 N) (h10 : γ 1 0 = 0) (z : ℍ) : shimuraSeed (shimuraThetaCharacter χ l h4) g w l
      (γ • z) = shimuraSeed (shimuraThetaCharacter χ l h4) g w l z := by
  have h11 : γ 1 1 = 1 ∨ γ 1 1 = -1 := by
    have h : γ 0 0 * γ 1 1 = 1 := by
      simpa only [h10, mul_zero, sub_zero] using γ.fin_two_mul_sub_mul_eq_one
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  refine tsum_congr fun n ↦ ?_
  rcases h11 with h1 | h1
  · rw [integrand_shimuraPairTerm_smul h4 hg hγ, h10, h1, mul_zero, mul_one]
  · rw [← SL_neg_smul, integrand_shimuraPairTerm_smul h4 hg (neg_mem_Gamma0 hγ)]
    simp [h10, h1]

variable [NeZero N]

lemma injective_gamma0InfPair : Function.Injective (gamma0InfPair (N := N)) := by
  rintro ⟨q, ε, n⟩ ⟨q', ε', n'⟩ h
  simp only [gamma0InfPair, Prod.mk_inj] at h
  rcases h with ⟨h1, h2⟩
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hc : (N : ℤ) * ((q.out : SL(2, ℤ)) 1 0 / N) = (q.out : SL(2, ℤ)) 1 0 :=
    Int.mul_ediv_cancel' (natCast_dvd_apply_one_zero q.out.2)
  have hc' : (N : ℤ) * ((q'.out : SL(2, ℤ)) 1 0 / N) = (q'.out : SL(2, ℤ)) 1 0 :=
    Int.mul_ediv_cancel' (natCast_dvd_apply_one_zero q'.out.2)
  have h1' : ((ε : ℤ) * ((n : ℕ) : ℤ)) * (q.out : SL(2, ℤ)) 1 0 =
      ((ε' : ℤ) * ((n' : ℕ) : ℤ)) * (q'.out : SL(2, ℤ)) 1 0 := by
    rw [← hc, ← hc']
    linear_combination (N : ℤ) * h1
  have hg (ε'' : ℤˣ) (m : ℕ+) (q'' : Gamma0InfCosets N) :
      (((ε'' : ℤ) * ((m : ℕ) : ℤ)) * (q''.out : SL(2, ℤ)) 1 0).gcd
        (((ε'' : ℤ) * ((m : ℕ) : ℤ)) * (q''.out : SL(2, ℤ)) 1 1) = m := by
    rw [Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp ((q''.out : SL(2, ℤ)).isCoprime_row 1),
      mul_one]
    rcases Int.units_eq_one_or ε'' with rfl | rfl <;> simp
  have hnn : n = n' := PNat.coe_injective (by rw [← hg ε n q, ← hg ε' n' q', h1', h2])
  subst hnn
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  have h3 : (ε : ℤ) * (q.out : SL(2, ℤ)) 1 0 = (ε' : ℤ) * (q'.out : SL(2, ℤ)) 1 0 :=
    mul_left_cancel₀ hn0 (by linear_combination h1')
  have h4' : (ε : ℤ) * (q.out : SL(2, ℤ)) 1 1 = (ε' : ℤ) * (q'.out : SL(2, ℤ)) 1 1 :=
    mul_left_cancel₀ hn0 (by linear_combination h2)
  have hεε : (ε : ℤ) * ε = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hqq : q' = q := by
    refine rel_of_mul_sub_eq_zero q q' ?_
    linear_combination ((ε : ℤ) * (q'.out : SL(2, ℤ)) 1 1) * h3 -
      ((ε : ℤ) * (q'.out : SL(2, ℤ)) 1 0) * h4' -
        ((q.out : SL(2, ℤ)) 1 0 * (q'.out : SL(2, ℤ)) 1 1 -
          (q.out : SL(2, ℤ)) 1 1 * (q'.out : SL(2, ℤ)) 1 0) * hεε
  subst hqq
  rcases (q'.out : SL(2, ℤ)).isCoprime_row 1 with ⟨u, v, huv⟩
  have hee : (ε : ℤ) = ε' := by
    linear_combination (ε - ε' : ℤ) * (-huv) + u * h3 + v * h4'
  rw [Units.ext hee]

lemma exists_gamma0InfPair_eq (hN1 : N ≠ 1) {p : ℤ × ℤ} (hp : IsUnit (p.2 : ZMod N)) :
    ∃ x, gamma0InfPair (N := N) x = p := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcop : IsCoprime (N : ℤ) p.2 := (ZMod.coe_int_isUnit_iff_isCoprime p.2 N).mp hp
  have hp2 : p.2 ≠ 0 := by
    intro h0
    rw [h0, isCoprime_zero_right, Int.isUnit_iff] at hcop
    omega
  have hG : 0 < ((N : ℤ) * p.1).gcd p.2 := Int.gcd_pos_of_ne_zero_right _ hp2
  rcases Int.exists_gcd_one hG with ⟨c, d, hcd, hc, hd⟩
  generalize ((N : ℤ) * p.1).gcd p.2 = G at hG hc hd
  have hNG : IsCoprime (N : ℤ) (G : ℤ) := by
    rw [hd] at hcop
    exact hcop.of_mul_right_right
  have hNc : (N : ℤ) ∣ c := hNG.dvd_of_dvd_mul_right ⟨p.1, hc.symm⟩
  rcases Int.isCoprime_iff_gcd_eq_one.mpr hcd with ⟨u, v, huv⟩
  let γ : SL(2, ℤ) := ⟨!![v, -u; c, d], by
    rw [det_fin_two_of]
    linear_combination huv⟩
  have hγ : γ ∈ Gamma0 N := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hNc
  let q : Gamma0InfCosets N := Quotient.mk _ ⟨γ, hγ⟩
  have hrel : ((⟨γ, hγ⟩ : Gamma0 N) * q.out⁻¹) ∈ cuspStabilizer (Gamma0 N) (1 : SL(2, ℤ)) :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel _) _)
  have h0 : c * (q.out : SL(2, ℤ)) 1 1 - d * (q.out : SL(2, ℤ)) 1 0 = 0 := by
    have h1 : ((1 : SL(2, ℤ))⁻¹ * ((⟨γ, hγ⟩ * q.out⁻¹ : Gamma0 N) : SL(2, ℤ)) * 1) 1 0 = 0 :=
      (mem_cuspStabilizer_iff (1 : SL(2, ℤ))).mp hrel
    simp only [inv_one, one_mul, mul_one, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    rwa [mul_inv_apply_one_zero] at h1
  rcases (q.out : SL(2, ℤ)).isCoprime_row 1 with ⟨u', v', huv'⟩
  have hce : c = (u' * c + v' * d) * (q.out : SL(2, ℤ)) 1 0 := by
    linear_combination (-c) * huv' + v' * h0
  have hde : d = (u' * c + v' * d) * (q.out : SL(2, ℤ)) 1 1 := by
    linear_combination (-d) * huv' - u' * h0
  have hue : IsUnit (u' * c + v' * d) := by
    refine IsUnit.of_mul_eq_one (u * (q.out : SL(2, ℤ)) 1 0 + v * (q.out : SL(2, ℤ)) 1 1) ?_
    linear_combination huv - u * hce - v * hde
  refine ⟨⟨q, hue.unit, ⟨G, hG⟩⟩, Prod.ext ?_ ?_⟩
  · refine mul_left_cancel₀ hN ?_
    have hq : (N : ℤ) * ((q.out : SL(2, ℤ)) 1 0 / N) = (q.out : SL(2, ℤ)) 1 0 :=
      Int.mul_ediv_cancel' (natCast_dvd_apply_one_zero q.out.2)
    simp only [gamma0InfPair, IsUnit.unit_spec, PNat.mk_coe]
    linear_combination (((u' * c + v' * d)) * (G : ℤ)) * hq - (G : ℤ) * hce - hc
  · simp only [gamma0InfPair, IsUnit.unit_spec, PNat.mk_coe]
    linear_combination (-(G : ℤ)) * hde - hd

lemma tsum_comp_gamma0InfPair (hN1 : N ≠ 1) {f : ℤ × ℤ → ℂ}
    (hf : ∀ p, ¬IsUnit (p.2 : ZMod N) → f p = 0) : ∑' x, f (gamma0InfPair (N := N) x) = ∑' p, f p :=
  injective_gamma0InfPair.tsum_eq fun p hp ↦
    exists_gamma0InfPair_eq hN1 (not_not.mp fun h ↦ hp (hf p h))

/-- **The Petersson integrand of Niwa's kernel is a periodisation** (LMFDB
`cmf.shimura_correspondence`): for `g ∈ S_{k/2}(N, χ)`, `k = 2 l + 1`, `4 ∣ N`, the integrand of `g`
against `Θ^(l)(·, w)` is `2 ∑_{Γ_∞ γ} φ(γ z)`, with `φ` the seed. -/
lemma integrand_shimuraTheta_eq_tsum (hg : g ∈ halfIntegralWeightSpace χ (2 * l + 1)) (w z : ℍ) :
    halfIntegralPeterssonIntegrand (2 * l + 1) g
      (fun z ↦ shimuraTheta (shimuraThetaCharacter χ l h4) z w l) z =
        2 * ∑' q : Gamma0InfCosets N,
          shimuraSeed (shimuraThetaCharacter χ l h4) g w l ((q.out : SL(2, ℤ)) • z) := by
  have hN1 : N ≠ 1 := by
    rintro rfl
    omega
  let f : ℤ × ℤ → ℂ := fun p ↦ halfIntegralPeterssonIntegrand (2 * l + 1) g
    (shimuraPairTerm (shimuraThetaCharacter χ l h4) w l ((N : ℤ) * p.1) p.2) z
  have hsum : Summable f := by
    refine (((Complex.summable_conj.mpr
      (summable_shimuraPairTerm (shimuraThetaCharacter χ l h4) w z l)).mul_left (g z)).mul_right
        (((z.im ^ (((2 * l + 1 : ℤ) : ℝ) / 2) : ℝ) : ℂ))).congr fun p ↦ rfl
  have hf0 : ∀ p : ℤ × ℤ, ¬IsUnit (p.2 : ZMod N) → f p = 0 := fun p hp ↦ by
    simp [f, halfIntegralPeterssonIntegrand, shimuraPairTerm, MulChar.map_nonunit _ hp]
  have e1 : halfIntegralPeterssonIntegrand (2 * l + 1) g
      (fun z ↦ shimuraTheta (shimuraThetaCharacter χ l h4) z w l) z = ∑' p, f p := by
    simp only [f, halfIntegralPeterssonIntegrand, shimuraPairTerm, shimuraTheta]
    rw [Complex.conj_tsum, ← tsum_mul_left, ← tsum_mul_right]
  have hs2 : Summable fun x ↦ f (gamma0InfPair (N := N) x) :=
    hsum.comp_injective injective_gamma0InfPair
  have hinner (q : Gamma0InfCosets N) (ε : ℤˣ) : ∑' n : ℕ+, f (gamma0InfPair (q, ε, n)) =
      shimuraSeed (shimuraThetaCharacter χ l h4) g w l ((q.out : SL(2, ℤ)) • z) := by
    refine tsum_congr fun n ↦ ?_
    have hq : (N : ℤ) * ((q.out : SL(2, ℤ)) 1 0 / N) = (q.out : SL(2, ℤ)) 1 0 :=
      Int.mul_ediv_cancel' (natCast_dvd_apply_one_zero q.out.2)
    have e2 : (N : ℤ) * (((ε : ℤ) * ((n : ℕ) : ℤ)) * ((q.out : SL(2, ℤ)) 1 0 / N)) =
        ((ε : ℤ) * ((n : ℕ) : ℤ)) * (q.out : SL(2, ℤ)) 1 0 := by
      linear_combination ((ε : ℤ) * ((n : ℕ) : ℤ)) * hq
    simp only [f, gamma0InfPair, e2]
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using (integrand_shimuraPairTerm_smul h4 hg q.out.2 w ((n : ℕ) : ℤ) z).symm
    · rw [← SL_neg_smul, integrand_shimuraPairTerm_smul h4 hg (neg_mem_Gamma0 q.out.2)]
      simp
  rw [e1, ← tsum_comp_gamma0InfPair hN1 hf0, hs2.tsum_prod, ← tsum_mul_left]
  refine tsum_congr fun q ↦ ?_
  have hs3 : Summable fun y : ℤˣ × ℕ+ ↦ f (gamma0InfPair (q, y)) := hs2.prod_factor q
  rw [hs3.tsum_prod]
  simp only [hinner q]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_units_int, nsmul_eq_mul]
  norm_num

end ModularForm
