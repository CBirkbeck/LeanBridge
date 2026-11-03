import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSquareIntegrable
import TauCeti.MeasureTheory.Group.FundamentalDomain

/-!
# The Hecke operators are self-adjoint on Maass forms of trivial character

For a prime `p ∤ N`, the Hecke operator `T_p F(z) = p^{-1/2} (F(pz) + ∑_{j < p} F((z + j)/p))` of
`UpperHalfPlane.maassHeckeOperator` is self-adjoint for the Petersson inner product
`⟨F, G⟩ = ∫_{Γ₀(N) \ ℍ} F conj(G) dμ` (`UpperHalfPlane.maassPetersson`) on the space
`M(N, 1, λ)` of square-integrable Maass forms of weight `0` on `Γ₀(N)` with trivial character
(`UpperHalfPlane.maassSpace`). Hence the Hecke eigenvalues of a Maass newform are real.

With `α = diag(p, 1)` and the twist `σ = !![m, n; N, p]` of `gamma0Twist`, the matrices `1` and
`σ T^b`, `b < p`, are right coset representatives of `Γ₀(Np) = Γ₀(N) ∩ α⁻¹ Γ₀(N) α` in `Γ₀(N)`, and
`T_p F(z) = p^{-1/2} ∑_i F(α r_i z)`, since `α σ = !![p m, n; N, 1] α⁻¹` up to a scalar. So
the translates `r_i D` of a fundamental domain `D` of `Γ₀(N)` tile a fundamental domain `D'` of
`Γ₀(Np)`, and `⟨T_p F, G⟩ = p^{-1/2} ∫_{D'} F(αw) conj(G(w)) dμ(w)`. The substitutions `w ↦ αw`
and `w ↦ σw` turn both `∫_{D'} F(αw) conj(G(w)) dμ` and `∫_{D'} F(w) conj(G(αw)) dμ` into integrals
of `F(u) conj(G(α⁻¹u))` over fundamental domains `α D'` and `σ⁻¹ D'` of the same group
`Γ₀(N) ∩ Γ⁰(p) = α Γ₀(Np) α⁻¹ = σ⁻¹ Γ₀(Np) σ`, under which this function is invariant, so they are
equal; this is `⟨T_p F, G⟩ = ⟨F, T_p G⟩`.

## Main definitions

* `UpperHalfPlane.heckeCosetRep`: the right coset representatives of `Γ₀(Np)` in `Γ₀(N)`.
* `UpperHalfPlane.heckeTwistInfty`: the matrix `!![p m, n; N, 1]` of `Γ₀(N)`.

## Main results

* `UpperHalfPlane.heckeCosetRep_injective`, `UpperHalfPlane.exists_heckeCosetRep_mul_mem`: the
  representatives name distinct right cosets of `Γ₀(Np)` and every one of them.
* `UpperHalfPlane.isFundamentalDomain_iUnion_heckeCosetRep_smul`: their translates of a
  fundamental domain of `Γ₀(N)` tile a fundamental domain of `Γ₀(Np)`.
* `UpperHalfPlane.maassHeckeOperator_eq_sum_heckeCosetRep`: `T_p F(z) = p^{-1/2} ∑_i F(α r_i z)`.
* `UpperHalfPlane.setIntegral_maassHeckeOperator_mul_conj`: the unfolding
  `⟨T_p F, G⟩ = p^{-1/2} ∫_{D'} F(αw) conj(G(w)) dμ(w)`.
* `UpperHalfPlane.setIntegral_scaleRep_eq`:
  `∫_{D'} F(αw) conj(G(w)) dμ = ∫_{D'} F(w) conj(G(αw)) dμ`.
* `UpperHalfPlane.maassPetersson_maassHeckeOperator`: `T_p` is self-adjoint.
* `UpperHalfPlane.IsMaassNewform.conj_heckeEigenvalue`: the Hecke eigenvalues of a Maass newform
  of trivial character are real.
-/

open MeasureTheory CongruenceSubgroup ModularGroup Matrix SpecialLinearGroup HeckeRing TauCeti

open scoped MatrixGroups Pointwise ComplexConjugate

namespace UpperHalfPlane

variable {N p : ℕ} {eigenvalue : ℂ} {F G : ℍ → ℂ} {γ : SL(2, ℤ)} {τ : ℍ} (x y : SL(2, ℤ))

lemma smul_eq_of_mem_maassSpace_one (hF : F ∈ maassSpace N 1 eigenvalue) (hγ : γ ∈ Gamma0 N) :
    F (γ • τ) = F τ := by
  rw [smul_eq_of_mem_maassSpace hF hγ, dirichletCharacter_one_apply_of_mem_gamma0 hγ, one_mul]

lemma sl_mul_apply_one_zero : (x * y) 1 0 = x 1 0 * y 0 0 + x 1 1 * y 1 0 := by
  simp [Matrix.mul_apply]

lemma sl_mul_apply_one_one : (x * y) 1 1 = x 1 0 * y 0 1 + x 1 1 * y 1 1 := by
  simp [Matrix.mul_apply]

section CosetRep

variable (hpN : p.Coprime N) (b : Fin p) {i j : Option (Fin p)}

/-- The matrix `!![p m, n; N, 1]` of `Γ₀(N)` built from the twist `σ = !![m, n; N, p]` of
`gamma0Twist`, with `diag(p, 1) σ diag(p, 1) = p · !![p m, n; N, 1]`. -/
noncomputable def heckeTwistInfty : SL(2, ℤ) :=
  ⟨!![p * gamma0Twist N p hpN 0 0, gamma0Twist N p hpN 0 1; N, 1], by
    rw [det_fin_two_of]
    linear_combination mul_sub_mul_eq_one_of_lowerRow (gamma0Twist_apply_one_zero hpN)
      (gamma0Twist_apply_one_one hpN)⟩

/-- The `p + 1` right coset representatives `1` and `σ T^b = !![m, m b + n; N, N b + p]`,
`b < p`, of `Γ₀(Np)` in `Γ₀(N)`, for the twist `σ = gamma0Twist N p = !![m, n; N, p]`. -/
noncomputable def heckeCosetRep : Option (Fin p) → SL(2, ℤ)
  | none => 1
  | some b => ⟨!![gamma0Twist N p hpN 0 0, gamma0Twist N p hpN 0 0 * b + gamma0Twist N p hpN 0 1;
      N, N * b + p], by
    rw [det_fin_two_of]
    linear_combination mul_sub_mul_eq_one_of_lowerRow (gamma0Twist_apply_one_zero hpN)
      (gamma0Twist_apply_one_one hpN)⟩

lemma heckeTwistInfty_mem : heckeTwistInfty hpN ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp [heckeTwistInfty]

variable (i) in
lemma heckeCosetRep_mem : heckeCosetRep hpN i ∈ Gamma0 N := by
  rcases i with _ | b
  · exact (Gamma0 N).one_mem
  · rw [Gamma0_mem]
    simp [heckeCosetRep]

lemma heckeCosetRep_some_apply_one_zero : heckeCosetRep hpN (some b) 1 0 = N :=
  rfl

lemma heckeCosetRep_some_apply_one_one : heckeCosetRep hpN (some b) 1 1 = N * b + p :=
  rfl

/-- **The coset representatives are distinct**: if `r_i r_j⁻¹ ∈ Γ₀(Np)` for the representatives
`heckeCosetRep`, then `i = j`, the lower left entries of `r_i r_j⁻¹` being `∓N` and
`N² (b - a)` otherwise. -/
lemma heckeCosetRep_injective (hp : p.Prime)
    (h : heckeCosetRep hpN i * (heckeCosetRep hpN j)⁻¹ ∈ Gamma0 (N * p)) : i = j := by
  have hN : (N : ℤ) ≠ 0 := by
    rintro hN
    rw [Int.natCast_eq_zero] at hN
    exact hp.one_lt.ne' <| (Nat.coprime_zero_right p).mp (hN ▸ hpN)
  have hp1 : ¬(N * p : ℤ) ∣ N := fun h' ↦ by
    have h1 : (p : ℤ) ∣ 1 := Int.dvd_of_mul_dvd_mul_left hN (by simpa using h')
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  rcases i with _ | a <;> rcases j with _ | b
  · rfl
  · rw [heckeCosetRep, one_mul, inv_apply_one_zero, heckeCosetRep_some_apply_one_zero, Nat.cast_mul,
      dvd_neg] at h
    exact absurd h hp1
  · rw [heckeCosetRep, inv_one, mul_one, heckeCosetRep_some_apply_one_zero, Nat.cast_mul] at h
    exact absurd h hp1
  · rw [sl_mul_apply_one_zero, inv_apply_zero_zero, inv_apply_one_zero,
      heckeCosetRep_some_apply_one_zero, heckeCosetRep_some_apply_one_one,
      heckeCosetRep_some_apply_one_zero, heckeCosetRep_some_apply_one_one, Nat.cast_mul] at h
    have h2 : (p : ℤ) ∣ N * (b - a) := Int.dvd_of_mul_dvd_mul_left hN <| by
      convert h using 1
      ring1
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd h2 with h3 | ⟨k, hk⟩
    · exact absurd (hpN.eq_one_of_dvd (Int.natCast_dvd_natCast.mp h3)) hp.one_lt.ne'
    · have ha : (a : ℕ) < p := a.2
      have hb : (b : ℕ) < p := b.2
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · nlinarith
        · exact hk0
        · nlinarith
      rw [hk0, mul_zero, sub_eq_zero] at hk
      exact congrArg some (Fin.ext (by exact_mod_cast hk.symm))

/-- **The coset representatives cover `Γ₀(N)`**: for every `γ ∈ Γ₀(N)` some `r_i γ` lies in
`Γ₀(Np)`, so that (applied to `γ⁻¹`) every element of `Γ₀(N)` lies in a right coset `Γ₀(Np) r_i`:
`r_none = 1` if `p` divides the lower left entry `c` of `γ`, and otherwise `r_b = σ T^b` with
`b ≡ -a c⁻¹ mod p`. -/
lemma exists_heckeCosetRep_mul_mem (hp : p.Prime) (hγ : γ ∈ Gamma0 N) :
    ∃ i, heckeCosetRep hpN i * γ ∈ Gamma0 (N * p) := by
  have hN : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hcop : IsCoprime (N : ℤ) p := Nat.isCoprime_iff_coprime.mpr hpN.symm
  simp only [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  by_cases hp1 : (p : ℤ) ∣ γ 1 0
  · exact ⟨none, by simpa [heckeCosetRep] using hcop.mul_dvd hN hp1⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hc : ((γ 1 0 : ℤ) : ZMod p) ≠ 0 := fun h ↦
      hp1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    refine ⟨some ⟨(-(γ 0 0 : ZMod p) * (γ 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩, ?_⟩
    rw [sl_mul_apply_one_zero, heckeCosetRep_some_apply_one_zero, heckeCosetRep_some_apply_one_one]
    refine hcop.mul_dvd (dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right hN _)) ?_
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self]
    field_simp
    ring1

/-- **The translates of a fundamental domain of `Γ₀(N)` by the coset representatives tile a
fundamental domain of `Γ₀(Np)`**, for the actions of the images in `PSL(2, ℤ)`. -/
lemma isFundamentalDomain_iUnion_heckeCosetRep_smul (hp : p.Prime) {S : Set ℍ}
    (hS : IsFundamentalDomain ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) S
      volume) :
    IsFundamentalDomain ((Gamma0 (N * p)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      (⋃ i, heckeCosetRep hpN i • S) volume := by
  let r : Option (Fin p) → (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) :=
    fun i ↦ ⟨_, Subgroup.mem_map_of_mem _ (heckeCosetRep_mem hpN i)⟩
  have h : IsFundamentalDomain ((Gamma0 (N * p)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
      ⊓ (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) : Subgroup PSL(2, ℤ))
      (⋃ i, r i • S) volume := (hS.iUnion_smul_of_transversal (r := r) (H :=
    ((Gamma0 (N * p)).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).subgroupOf
      ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))))
    (fun i ↦ hS.nullMeasurableSet.smul (r i : PSL(2, ℤ)))
    ⟨fun i j hij ↦ ?_, fun q ↦ ?_⟩).of_subgroupOf
  · rwa [inf_of_le_left (Subgroup.map_mono (Gamma0_le_Gamma0_of_dvd (dvd_mul_right N p)))] at h
  · rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hij
    simp only [inv_inv] at hij
    exact heckeCosetRep_injective hpN hp <| (CongruenceSubgroup.mem_Gamma0Projective_mk _ _).mp hij
  · induction q using QuotientGroup.induction_on with
    | H g =>
      rcases g with ⟨_, γ, hγ, rfl⟩
      rcases exists_heckeCosetRep_mul_mem hpN hp hγ with ⟨i, hi⟩
      refine ⟨i, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [inv_inv]
      exact Subgroup.mem_map_of_mem _ hi

lemma coe_scaleRep_inv_smul (hp : 0 < p) :
    ↑(((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • τ) = (τ : ℂ) / p := by
  have h : ↑((GL2.scaleRep p).map (Rat.castHom ℝ) • ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • τ) =
      (p : ℂ) * ↑(((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • τ) :=
    coe_scaleRep_map_smul hp
  rw [smul_inv_smul] at h
  have hp' : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne'
  rw [h]
  field_simp

lemma scaleRep_smul_gamma0Twist_smul (hp : 0 < p) :
    (GL2.scaleRep p).map (Rat.castHom ℝ) • (gamma0Twist N p hpN • τ) =
      heckeTwistInfty hpN • (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • τ) := by
  have hden : ((N : ℤ) : ℂ) * τ + ((p : ℤ) : ℂ) ≠ 0 := by
    have h : denom (gamma0Twist N p hpN) τ ≠ 0 := denom_ne_zero _ τ
    rwa [denom_apply, gamma0Twist_apply_one_zero, gamma0Twist_apply_one_one] at h
  have hp' : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne'
  apply UpperHalfPlane.ext
  rw [coe_scaleRep_map_smul hp, coe_specialLinearGroup_apply, coe_specialLinearGroup_apply,
    coe_scaleRep_inv_smul hp]
  simp [heckeTwistInfty]
  push_cast at hden ⊢
  field_simp

lemma heckeCosetRep_some_smul :
    heckeCosetRep hpN (some b) • τ = gamma0Twist N p hpN • (T ^ (b : ℤ) • τ) := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply, coe_T_zpow_smul_eq]
  simp [heckeCosetRep]
  congr 1 <;> ring1

/-- **`T_p` as a sum over the coset representatives**: for `F` in `M(N, 1, λ)` and a prime `p ∤ N`,
`T_p F(z) = p^{-1/2} ∑_i F(α r_i z)` with `α = diag(p, 1)`, since `α σ T^b z` and `(z + b)/p` are
in the same `Γ₀(N)`-orbit. -/
lemma maassHeckeOperator_eq_sum_heckeCosetRep (hp : p.Prime) (hF : F ∈ maassSpace N 1 eigenvalue) :
    maassHeckeOperator p (F ∘ ofComplex) τ = ((√p)⁻¹ : ℝ) *
      ∑ i, F ((GL2.scaleRep p).map (Rat.castHom ℝ) • (heckeCosetRep hpN i • τ)) := by
  rw [maassHeckeOperator, Fintype.sum_option,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ (F ∘ ofComplex) ((↑τ + j) / p)) p]
  congr 2
  · rw [heckeCosetRep, one_smul, Function.comp_apply, ← coe_scaleRep_map_smul hp.pos,
      ofComplex_apply]
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [heckeCosetRep_some_smul, scaleRep_smul_gamma0Twist_smul hpN hp.pos,
      smul_eq_of_mem_maassSpace_one hF (heckeTwistInfty_mem hpN), Function.comp_apply]
    congr 1
    rw [← ofComplex_apply (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • (T ^ (b : ℤ) • τ)),
      coe_scaleRep_inv_smul hp.pos, coe_T_zpow_smul_eq]
    push_cast
    rfl

variable {y} in
lemma mem_conjGL_gamma0Twist_iff :
    y ∈ conjGL (Gamma0 (N * p)) (gamma0Twist N p hpN) ↔ (N : ℤ) ∣ y 1 0 ∧ (p : ℤ) ∣ y 0 1 := by
  have hcop : IsCoprime (N : ℤ) p := Nat.isCoprime_iff_coprime.mpr hpN.symm
  have key : (gamma0Twist N p hpN * y * (gamma0Twist N p hpN)⁻¹) 1 0 =
      N * p * (y 0 0 - y 1 1) + p ^ 2 * y 1 0 - N ^ 2 * y 0 1 := by
    rw [sl_mul_apply_one_zero, inv_apply_zero_zero, inv_apply_one_zero, sl_mul_apply_one_zero,
      sl_mul_apply_one_one, gamma0Twist_apply_one_zero, gamma0Twist_apply_one_one]
    ring1
  rw [conjGL_coe, map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul, Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd, key, Nat.cast_mul]
  constructor
  · intro h
    have h1 : (N : ℤ) ∣ p ^ 2 * y 1 0 := by
      have e : (p : ℤ) ^ 2 * y 1 0 = N * p * (y 0 0 - y 1 1) + p ^ 2 * y 1 0 - N ^ 2 * y 0 1 -
          N * (p * (y 0 0 - y 1 1) - N * y 0 1) := by
        ring1
      rw [e]
      exact dvd_sub ((dvd_mul_right _ _).trans h) (dvd_mul_right _ _)
    have h2 : (p : ℤ) ∣ N ^ 2 * y 0 1 := by
      have e : (N : ℤ) ^ 2 * y 0 1 = p * (N * (y 0 0 - y 1 1) + p * y 1 0) -
          (N * p * (y 0 0 - y 1 1) + p ^ 2 * y 1 0 - N ^ 2 * y 0 1) := by
        ring1
      rw [e]
      exact dvd_sub (dvd_mul_right _ _) ((dvd_mul_left _ _).trans h)
    exact ⟨hcop.pow_right.dvd_of_dvd_mul_left h1, hcop.symm.pow_right.dvd_of_dvd_mul_left h2⟩
  · rintro ⟨h1, h2⟩
    refine hcop.mul_dvd (dvd_sub (dvd_add (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
      (dvd_mul_of_dvd_right h1 _)) (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) _))
      (dvd_sub (dvd_add (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
      (dvd_mul_of_dvd_left (dvd_pow_self _ two_ne_zero) _)) (dvd_mul_of_dvd_right h2 _))

variable {y} in
lemma mem_conjGL_scaleRep_inv_iff (hp : p.Prime) :
    y ∈ conjGL (Gamma0 (N * p)) ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ ↔
      (N : ℤ) ∣ y 1 0 ∧ (p : ℤ) ∣ y 0 1 := by
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  rw [mem_conjGL, inv_inv]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : mapGL ℝ z = ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ * mapGL ℝ y *
        (GL2.scaleRep p).map (Rat.castHom ℝ) := hzy
    have hNp : ((N * p : ℕ) : ℤ) ∣ z 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    rw [Nat.cast_mul] at hNp
    have hzp : (p : ℤ) ∣ z 1 0 := (dvd_mul_left _ _).trans hNp
    have h : (GL2.scaleRep p).map (Rat.castHom ℝ) * mapGL ℝ z =
        mapGL ℝ (gammaZeroScale p z hzp) * (GL2.scaleRep p).map (Rat.castHom ℝ) :=
      scaleRep_map_mul_mapGL hp.pos hzp
    rw [hzy', ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h
    rw [mapGL_injective (mul_right_cancel h)]
    exact ⟨Int.dvd_div_of_mul_dvd (mul_comm (N : ℤ) p ▸ hNp), dvd_mul_right _ _⟩
  · rintro ⟨h1, h2⟩
    let z : SL(2, ℤ) := ⟨!![y 0 0, y 0 1 / p; p * y 1 0, y 1 1], by
      have h : (y : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := y.2
      rw [det_fin_two] at h
      rw [det_fin_two_of]
      linear_combination h - y 1 0 * Int.mul_ediv_cancel' h2⟩
    have hzp : (p : ℤ) ∣ z 1 0 := dvd_mul_right _ _
    have hz : z ∈ Gamma0 (N * p) := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul, mul_comm (N : ℤ)]
      exact mul_dvd_mul_left _ h1
    have hgz : gammaZeroScale p z hzp = y := by
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact Int.mul_ediv_cancel' h2
      · exact Int.mul_ediv_cancel_left _ hp0
      · rfl
    have h : (GL2.scaleRep p).map (Rat.castHom ℝ) * mapGL ℝ z =
        mapGL ℝ (gammaZeroScale p z hzp) * (GL2.scaleRep p).map (Rat.castHom ℝ) :=
      scaleRep_map_mul_mapGL hp.pos hzp
    rw [hgz] at h
    refine ⟨z, hz, ?_⟩
    rw [mul_assoc]
    exact eq_inv_mul_iff_mul_eq.mpr h

variable [NeZero N] in
lemma integrableOn_smul_gammaZeroDomain (hF : F ∈ maassSpace N 1 eigenvalue)
    (hG : G ∈ maassSpace N 1 eigenvalue) (k : SL(2, ℤ)) :
    IntegrableOn (fun w ↦ F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w))
      (k • gammaZeroDomain N) := by
  rw [gammaZeroDomain, Set.smul_set_iUnion]
  refine integrableOn_finite_iUnion.mpr fun q ↦ ?_
  rw [smul_smul]
  have hFA : MemLp (fun w ↦ F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w)) 2
      (volume.restrict ((k * (q.out : SL(2, ℤ))⁻¹) • fdo)) := by
    have h : MemLp (fun w ↦ F ((GL2.scaleRep p).map (algebraMap ℚ ℝ) • w)) 2
        (volume.restrict ((k * (q.out : SL(2, ℤ))⁻¹) • fdo)) :=
      memLp_comp_smul (GL2.scaleRep p) (k * (q.out : SL(2, ℤ))⁻¹) hF
    rwa [RingHom.ext_rat (algebraMap ℚ ℝ) (Rat.castHom ℝ)] at h
  have hGL : MemLp G 2 (volume.restrict ((k * (q.out : SL(2, ℤ))⁻¹) • fdo)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_of_mem_maassSpace hG).aestronglyMeasurable).mpr
      (integrableOn_norm_sq_smul_fdo _ hG)
  exact hFA.integrable_mul hGL.star

variable [NeZero N] in
/-- **The unfolding of `⟨T_p F, G⟩`**: for `F`, `G` in `M(N, 1, λ)`, `N ≠ 0` and a prime `p ∤ N`,
`⟨T_p F, G⟩ = p^{-1/2} ∫_{D'} F(αw) conj(G(w)) dμ(w)`, with `α = diag(p, 1)` and the fundamental
domain `D' = ⋃_i r_i D` of `Γ₀(Np)` tiled by the coset representatives `r_i`. -/
lemma setIntegral_maassHeckeOperator_mul_conj (hp : p.Prime) (hF : F ∈ maassSpace N 1 eigenvalue)
    (hG : G ∈ maassSpace N 1 eigenvalue) :
    ∫ z in gammaZeroDomain N, maassHeckeOperator p (F ∘ ofComplex) z * conj (G z) =
      ((√p)⁻¹ : ℝ) * ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w) := by
  have hS : IsFundamentalDomain ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      (gammaZeroDomain N) volume :=
    isFundamentalDomain_gammaZeroDomain N
  have hpiece (i : Option (Fin p)) : ∫ z in gammaZeroDomain N,
      F ((GL2.scaleRep p).map (Rat.castHom ℝ) • (heckeCosetRep hpN i • z)) * conj (G z) =
      ∫ w in heckeCosetRep hpN i • gammaZeroDomain N,
        F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w) := by
    have h : ∫ w in (heckeCosetRep hpN i • ·) '' gammaZeroDomain N,
        F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w) =
        ∫ z in gammaZeroDomain N, F ((GL2.scaleRep p).map (Rat.castHom ℝ) •
          (heckeCosetRep hpN i • z)) * conj (G (heckeCosetRep hpN i • z)) :=
      (measurePreserving_smul _ volume).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _
    rw [Set.image_smul] at h
    rw [h]
    simp only [smul_eq_of_mem_maassSpace_one hG (heckeCosetRep_mem hpN i)]
  have hint (i : Option (Fin p)) : IntegrableOn (fun z ↦
      F ((GL2.scaleRep p).map (Rat.castHom ℝ) • (heckeCosetRep hpN i • z)) * conj (G z))
      (gammaZeroDomain N) := by
    have h0 : IntegrableOn (fun w ↦ F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w))
        ((heckeCosetRep hpN i • ·) '' gammaZeroDomain N) := by
      rw [Set.image_smul]
      exact integrableOn_smul_gammaZeroDomain hF hG _
    have h : IntegrableOn ((fun w ↦ F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w)) ∘
        (heckeCosetRep hpN i • ·)) (gammaZeroDomain N) :=
      ((measurePreserving_smul _ volume).integrableOn_image
        (measurableEmbedding_const_smul _)).mp h0
    simpa only [Function.comp_def, smul_eq_of_mem_maassSpace_one hG (heckeCosetRep_mem hpN i)]
      using h
  have hdisj : Pairwise fun i j ↦ AEDisjoint volume (heckeCosetRep hpN i • gammaZeroDomain N)
      (heckeCosetRep hpN j • gammaZeroDomain N) := by
    intro i j hij
    let r : Option (Fin p) → (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) :=
      fun i ↦ ⟨_, Subgroup.mem_map_of_mem _ (heckeCosetRep_mem hpN i)⟩
    have hne : r i ≠ r j := fun he ↦ hij <| by
      have hc : heckeCosetRep hpN i / heckeCosetRep hpN j ∈ Subgroup.center SL(2, ℤ) :=
        QuotientGroup.eq_iff_div_mem.mp (congrArg Subtype.val he)
      rw [div_eq_mul_inv] at hc
      exact heckeCosetRep_injective hpN hp (CongruenceSubgroup.center_le_Gamma0 _ hc)
    have h : AEDisjoint volume (r i • gammaZeroDomain N) (r j • gammaZeroDomain N) :=
      hS.aedisjoint hne
    exact h
  simp_rw [maassHeckeOperator_eq_sum_heckeCosetRep hpN hp hF, mul_assoc, Finset.sum_mul]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i,
    integral_iUnion_ae (fun i ↦ hS.nullMeasurableSet.smul _) hdisj
      (integrableOn_finite_iUnion.mpr fun i ↦ integrableOn_smul_gammaZeroDomain hF hG _),
    tsum_fintype]
  exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ hpiece i)

/-- **The symmetry behind the self-adjointness of `T_p`**: for `F`, `G` in `M(N, 1, λ)` and a
prime `p ∤ N`, `∫_{D'} F(αw) conj(G(w)) dμ = ∫_{D'} F(w) conj(G(αw)) dμ` on the fundamental domain
`D'` of `Γ₀(Np)`: both are integrals of `F(u) conj(G(α⁻¹u))` over fundamental domains `α D'` and
`σ⁻¹ D'` of `Γ₀(N) ∩ Γ⁰(p)`, under which it is invariant. -/
lemma setIntegral_scaleRep_eq (hp : p.Prime) (hF : F ∈ maassSpace N 1 eigenvalue)
    (hG : G ∈ maassSpace N 1 eigenvalue) :
    ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w) =
      ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F w * conj (G ((GL2.scaleRep p).map (Rat.castHom ℝ) • w)) := by
  have hS₁ : IsFundamentalDomain ((Gamma0 (N * p)).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (⋃ i, heckeCosetRep hpN i • gammaZeroDomain N)
      volume :=
    isFundamentalDomain_iUnion_heckeCosetRep_smul hpN hp (isFundamentalDomain_gammaZeroDomain N)
  have hK : conjGL (Gamma0 (N * p)) ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ =
      conjGL (Gamma0 (N * p)) (gamma0Twist N p hpN) :=
    Subgroup.ext fun _ ↦ (mem_conjGL_scaleRep_inv_iff hp).trans
      (mem_conjGL_gamma0Twist_iff hpN).symm
  have hA : IsFundamentalDomain ((conjGL (Gamma0 (N * p))
      ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      ((GL2.scaleRep p).map (Rat.castHom ℝ) • ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N)
      volume :=
    isFundamentalDomain_smul_of_inv_conjAct_eq
      (by rw [← toConjAct_smul_gamma0_eq hp.pos (dvd_mul_left p N), map_inv, inv_smul_smul]) hS₁
  have htop : conjGL ⊤ ((gamma0Twist N p hpN : GL (Fin 2) ℝ))⁻¹ = ⊤ := by
    rw [← map_inv, ← map_inv, conjGL_coe]
    exact eq_top_iff.mpr fun x _ ↦ Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr
      (Subgroup.mem_top _)
  have hσ : IsFundamentalDomain ((conjGL (Gamma0 (N * p))
      ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
      (((gamma0Twist N p hpN : GL (Fin 2) ℝ))⁻¹ • ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N)
      volume :=
    isFundamentalDomain_smul_of_inv_conjAct_eq
      (by rw [inv_inv, hK, toConjAct_smul_conjGL_eq, htop, inf_top_eq]) hS₁
  have hinv (g : (conjGL (Gamma0 (N * p)) ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) (u : ℍ) :
      F (g • u) * conj (G (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • (g • u))) =
        F u * conj (G (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • u)) := by
    rcases g.2 with ⟨y, hy, hg⟩
    have hyN : y ∈ Gamma0 N := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ((mem_conjGL_scaleRep_inv_iff hp).mp hy).1
    rcases mem_conjGL.mp hy with ⟨z, hz, hzy⟩
    rw [inv_inv] at hzy
    have hpt : ((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • (y • u) =
        z • (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • u) := by
      rw [sl_moeb, sl_moeb, smul_smul, smul_smul, hzy, mul_inv_cancel_right]
    rw [Subgroup.smul_def, ← hg, QuotientGroup.mk'_apply, pslMk_smul, hpt,
      smul_eq_of_mem_maassSpace_one hF hyN, smul_eq_of_mem_maassSpace_one hG
      (Gamma0_le_Gamma0_of_dvd (dvd_mul_right N p) hz)]
  have e1 : ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
      F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G w) =
      ∫ u in (GL2.scaleRep p).map (Rat.castHom ℝ) • ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F u * conj (G (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • u)) := by
    have h : ∫ u in ((GL2.scaleRep p).map (Rat.castHom ℝ) • ·) ''
        ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F u * conj (G (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • u)) =
        ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
          F ((GL2.scaleRep p).map (Rat.castHom ℝ) • w) * conj (G (((GL2.scaleRep p).map
            (Rat.castHom ℝ))⁻¹ • (GL2.scaleRep p).map (Rat.castHom ℝ) • w)) :=
      (measurePreserving_smul _ volume).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _
    rw [Set.image_smul] at h
    rw [h]
    simp only [inv_smul_smul]
  have e2 : ∫ w in ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
      F w * conj (G ((GL2.scaleRep p).map (Rat.castHom ℝ) • w)) =
      ∫ u in ((gamma0Twist N p hpN : GL (Fin 2) ℝ))⁻¹ •
        ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
        F u * conj (G (((GL2.scaleRep p).map (Rat.castHom ℝ))⁻¹ • u)) := by
    have h : ∫ w in ((gamma0Twist N p hpN : GL (Fin 2) ℝ) • ·) ''
        (((gamma0Twist N p hpN : GL (Fin 2) ℝ))⁻¹ • ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N),
        F w * conj (G ((GL2.scaleRep p).map (Rat.castHom ℝ) • w)) =
        ∫ u in ((gamma0Twist N p hpN : GL (Fin 2) ℝ))⁻¹ •
          ⋃ i, heckeCosetRep hpN i • gammaZeroDomain N,
          F ((gamma0Twist N p hpN : GL (Fin 2) ℝ) • u) * conj (G ((GL2.scaleRep p).map
            (Rat.castHom ℝ) • (gamma0Twist N p hpN : GL (Fin 2) ℝ) • u)) :=
      (measurePreserving_smul _ volume).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _
    rw [Set.image_smul, smul_inv_smul] at h
    rw [h]
    congr 1
    funext u
    rw [← sl_moeb, smul_eq_of_mem_maassSpace_one hF (gamma0Twist_mem_Gamma0 hpN),
      scaleRep_smul_gamma0Twist_smul hpN hp.pos,
      smul_eq_of_mem_maassSpace_one hG (heckeTwistInfty_mem hpN)]
  rw [e1, e2]
  exact hA.setIntegral_eq hσ hinv

end CosetRep

variable [NeZero N]

/-- **The Hecke operators are self-adjoint** for the Petersson inner product on Maass forms of
trivial character: `⟨T_p F, G⟩ = ⟨F, T_p G⟩` for `F`, `G` in `M(N, 1, λ)`, `N ≠ 0`, and every prime
`p ∤ N`. -/
lemma maassPetersson_maassHeckeOperator (hpN : p.Coprime N) (hp : p.Prime)
    (hF : F ∈ maassSpace N 1 eigenvalue) (hG : G ∈ maassSpace N 1 eigenvalue) :
    maassPetersson N (fun τ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) G =
      maassPetersson N F fun τ ↦ maassHeckeOperator p (G ∘ ofComplex) τ := by
  have hc (H₁ H₂ : ℍ → ℂ) : maassPetersson N H₁ H₂ = conj (maassPetersson N H₂ H₁) := by
    rw [maassPetersson, maassPetersson, ← integral_conj]
    simp only [map_mul, Complex.conj_conj, mul_comm]
  rw [hc F, maassPetersson, maassPetersson, setIntegral_maassHeckeOperator_mul_conj hpN hp hF hG,
    setIntegral_maassHeckeOperator_mul_conj hpN hp hG hF, setIntegral_scaleRep_eq hpN hp hF hG,
    map_mul, Complex.conj_ofReal, ← integral_conj]
  simp only [map_mul, Complex.conj_conj, mul_comm]

/-- **The Hecke eigenvalues of a Maass newform of trivial character are real**: if
`T_p F = λ_p F` on `ℍ` for a Maass newform `F` on `Γ₀(N)` and a prime `p ∤ N`, then `λ_p` is real,
since `λ_p ⟨F, F⟩ = ⟨T_p F, F⟩ = ⟨F, T_p F⟩ = conj(λ_p) ⟨F, F⟩` and `⟨F, F⟩ ≠ 0`. -/
lemma IsMaassNewform.conj_heckeEigenvalue (hF : IsMaassNewform N 1 eigenvalue F) (hp : p.Prime)
    (hpN : ¬p ∣ N) {c : ℂ} (hc : ∀ z : ℍ, maassHeckeOperator p (F ∘ ofComplex) z = c * F z) :
    conj c = c := by
  have h : maassPetersson N (fun τ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) F =
      maassPetersson N F fun τ ↦ maassHeckeOperator p (F ∘ ofComplex) τ :=
    maassPetersson_maassHeckeOperator (hp.coprime_iff_not_dvd.mpr hpN) hp hF.1.1 hF.1.1
  have h1 : maassPetersson N (fun τ ↦ c * F τ) F = c * maassPetersson N F F := by
    simp only [maassPetersson, mul_assoc, integral_const_mul]
  have h2 : maassPetersson N F (fun τ ↦ c * F τ) = conj c * maassPetersson N F F := by
    rw [maassPetersson, maassPetersson, ← integral_const_mul]
    congr 1
    funext z
    rw [map_mul]
    ring1
  have h0 : maassPetersson N F F ≠ 0 := fun h0 ↦
    hF.2.1 (eq_zero_of_maassPetersson_self_eq_zero hF.1.1 h0)
  simp only [hc] at h
  rw [h1, h2] at h
  exact (mul_right_cancel₀ h0 h).symm

end UpperHalfPlane
