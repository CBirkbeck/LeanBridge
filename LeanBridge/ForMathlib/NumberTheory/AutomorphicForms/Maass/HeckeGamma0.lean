import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Hecke
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Invariance
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Prime.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-!
# Hecke operators preserve `Γ₀(N)`-invariance

For a prime `p ∤ N`, the Hecke operator `T_p` of `maassHeckeOperator` is `√p` times Tau Ceti's
weight-`0` slash sum `heckeSlashSum 0 D` over the double coset `D = Γ₀(N) diag(1, p) Γ₀(N)`, whose
right cosets are named by `!![1, j; 0, p]` and `σ diag(p, 1)` with `σ ∈ Γ₀(N)`. The slash sum of a
`Γ₀(N)`-invariant function is `Γ₀(N)`-invariant (Shimura, Proposition 3.37), hence so is `T_p f`.

## Main results

* `UpperHalfPlane.maassHeckeOperator_smul_eq`: `T_p` preserves `Γ₀(N)`-invariance.
* `UpperHalfPlane.IsMaassForm.maassHeckeOperator_smul_eq`,
  `UpperHalfPlane.IsMaassForm.contDiffOn_maassHeckeOperator`,
  `UpperHalfPlane.IsMaassForm.hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero`: `T_p f` of a
  Maass form `f` on `Γ₀(N)` is smooth, `Γ₀(N)`-invariant and a Laplace eigenfunction with the same
  eigenvalue. Square-integrability of `T_p f` on `Γ₀(N) \ ℍ` is not proved here.
-/

open Matrix SpecialLinearGroup CongruenceSubgroup DoubleCoset HeckeRing GL2 GLn

open scoped ContDiff MatrixGroups ModularForm Pointwise

namespace UpperHalfPlane

variable {N p : ℕ} {f : ℂ → ℂ} {eigenvalue : ℂ}

lemma slash_zero_mapGL_apply (G : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    (G ∣[(0 : ℤ)] mapGL ℚ σ) τ = G (mapGL ℝ σ • τ) := by
  rw [ModularForm.rat_slash, map_mapGL, ModularForm.slash_def_of_det_pos]
  · simp
  · simp [← Int.cast_det]

lemma rat_slash_zero_apply {g : GL (Fin 2) ℚ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℚ).det)
    (G : ℍ → ℂ) (τ : ℍ) :
    (G ∣[(0 : ℤ)] g) τ =
      G (GeneralLinearGroup.map (algebraMap ℚ ℝ) g • τ) /
        ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℚ) := by
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ)).det =
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, eq_ratCast]
  have habs :
      |((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ)| = ((g : Matrix (Fin 2) (Fin 2) ℚ).det : ℝ) :=
    abs_of_pos <| Rat.cast_pos.mpr hg
  rw [ModularForm.rat_slash_apply_of_det_pos 0 hg]
  simp [hdet, habs, div_eq_mul_inv]

lemma slash_zero_eq_of_mem_Gamma0
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ∀ z : ℍ, f ↑(γ • z) = f z) {δ : GL (Fin 2) ℚ}
    (hδ : δ ∈ (Gamma0 N).map (mapGL ℚ)) :
    (fun z : ℍ ↦ f z) ∣[(0 : ℤ)] δ = fun z : ℍ ↦ f z := by
  rcases hδ with ⟨σ, hσ, rfl⟩
  funext z
  rw [slash_zero_mapGL_apply]
  exact hf _ (Subgroup.mem_map_of_mem _ hσ) z

lemma maassHeckeOperator_eq_heckeSlashSum [NeZero N] (hp : p.Prime) (hpN : p.Coprime N)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ∀ z : ℍ, f ↑(γ • z) = f z) (τ : ℍ) :
    maassHeckeOperator p f τ = √p *
      heckeSlashSum 0 (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N)
        (fun z : ℍ ↦ f z) τ := by
  have hF : ∀ δ ∈ (Gamma0 N).map (mapGL ℚ), (fun z : ℍ ↦ f z) ∣[(0 : ℤ)] δ = fun z : ℍ ↦ f z :=
    fun _ ↦ slash_zero_eq_of_mem_Gamma0 hf
  have hcover : doubleCoset ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).out :
      GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ i, MulOpposite.op (primeRep (gamma0Twist N p hpN) p i) •
        ((Gamma0 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
    rw [← HeckeCoset.rep_def, ← HeckeCoset.toSet_eq_doubleCoset_rep]
    exact (diagCosetGamma0_toSet N _ _).trans <|
      doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_prime hp
        (gamma0Twist_apply_one_zero hpN) (gamma0Twist_apply_one_one hpN)
  rw [heckeSlashSum_eq_sum_of_rightCosets 0 _ _ hcover
    (op_primeRep_smul_injective (G := Gamma0 N) hp.one_lt (gamma0Twist_apply_one_one hpN)) _ hF,
    Fintype.sum_option]
  simp only [primeRep_some, primeRep_none, SlashAction.slash_mul,
    hF _ (Subgroup.mem_map_of_mem _ (gamma0Twist_mem_Gamma0 hpN))]
  have hs : ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (scaleRep p) • τ : ℍ) : ℂ) = p * τ := by
    rw [coe_smul_of_det_pos]
    · simp [num, denom, coe_scaleRep p hp.pos]
    · rw [GeneralLinearGroup.val_det_apply]
      exact ModularForm.det_map_ratCast_pos (det_scaleRep_pos p)
  have hds : ((scaleRep p : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) = p := by
    simp [coe_scaleRep p hp.pos, det_fin_two]
  have hdu (b : Fin p) : ((upperTriRep p b : Matrix (Fin 2) (Fin 2) ℚ).det : ℂ) = p := by
    simp [det_fin_two]
  rw [Pi.add_apply, Finset.sum_apply, rat_slash_zero_apply (det_scaleRep_pos p),
    Finset.sum_congr rfl fun b _ ↦ rat_slash_zero_apply (det_upperTriRep_pos p b) _ τ, hs, hds]
  simp only [coe_upperTriRep_smul, hdu, maassHeckeOperator]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ f ((τ + j) / p)) p, ← Finset.sum_div]
  have hp2 : (√p : ℂ) * √p = p := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hp0 : (√p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos)).ne'
  have hpC : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  push_cast
  field_simp
  linear_combination -(f (p * τ) + ∑ i : Fin p, f ((τ + i) / p)) * hp2

/-- **`T_p` preserves `Γ₀(N)`-invariance** for a prime `p ∤ N`: if `f(γz) = f(z)` for all
`γ ∈ Γ₀(N)` and `z ∈ ℍ`, then the same holds for `T_p f`. -/
lemma maassHeckeOperator_smul_eq (hp : p.Prime) (hpN : p.Coprime N)
    (hf : ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ∀ z : ℍ, f ↑(γ • z) = f z) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ (Gamma0 N).map (mapGL ℝ)) (z : ℍ) :
    maassHeckeOperator p f ↑(γ • z) = maassHeckeOperator p f z := by
  have hN : NeZero N := ⟨by
    rintro rfl
    exact hp.one_lt.ne' <| (Nat.coprime_zero_right p).mp hpN⟩
  rcases hγ with ⟨σ, hσ, rfl⟩
  have h : (heckeSlashSum 0 (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N)
      (fun z : ℍ ↦ f z) ∣[(0 : ℤ)] mapGL ℚ σ) z =
      heckeSlashSum 0 (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N)
        (fun z : ℍ ↦ f z) z :=
    congrFun (heckeSlashSum_slash_invariant 0 _ _ (fun _ ↦ slash_zero_eq_of_mem_Gamma0 hf)
      (Subgroup.mem_map_of_mem _ hσ)) z
  rw [slash_zero_mapGL_apply] at h
  rw [maassHeckeOperator_eq_heckeSlashSum hp hpN hf, maassHeckeOperator_eq_heckeSlashSum hp hpN hf,
    h]

/-- **`T_p` of a Maass form on `Γ₀(N)` is `Γ₀(N)`-invariant** for a prime `p ∤ N`. -/
lemma IsMaassForm.maassHeckeOperator_smul_eq
    (hf : IsMaassForm ((Gamma0 N).map (mapGL ℝ)) f eigenvalue) (hp : p.Prime) (hpN : p.Coprime N)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma0 N).map (mapGL ℝ)) (z : ℍ) :
    maassHeckeOperator p f ↑(γ • z) = maassHeckeOperator p f z :=
  UpperHalfPlane.maassHeckeOperator_smul_eq hp hpN hf.2.2.1 hγ z

/-- **`T_p` of a Maass form is smooth on `ℍ`**. -/
lemma IsMaassForm.contDiffOn_maassHeckeOperator {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hf : IsMaassForm Γ f eigenvalue) (hp : p ≠ 0) :
    ContDiffOn ℝ ∞ (maassHeckeOperator p f) {w | 0 < w.im} :=
  UpperHalfPlane.contDiffOn_maassHeckeOperator hp hf.1

/-- **`T_p` of a Maass form with eigenvalue `λ` is a Laplace eigenfunction with eigenvalue
`λ`**. -/
lemma IsMaassForm.hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero
    {Γ : Subgroup (GL (Fin 2) ℝ)} (hf : IsMaassForm Γ f eigenvalue) (hp : p ≠ 0) {z : ℂ}
    (hz : 0 < z.im) :
    hyperbolicLaplacian (maassHeckeOperator p f) z + eigenvalue * maassHeckeOperator p f z = 0 :=
  UpperHalfPlane.hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero hp (hf.1.of_le (by simp))
    hf.2.2.2 hz

end UpperHalfPlane
