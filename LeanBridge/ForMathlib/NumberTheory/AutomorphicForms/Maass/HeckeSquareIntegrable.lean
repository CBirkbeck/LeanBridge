import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeGamma0
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.TrivialCharacter

/-!
# Hecke operators preserve square-integrable Maass forms

For a Maass form `F` in `M(N, χ, λ)` (`UpperHalfPlane.maassSpace`) and `β ∈ GL(2, ℚ)`, the function
`z ↦ F(βz)` is square-integrable on every translate `σ 𝒟ᵒ`, `σ ∈ SL(2, ℤ)`, of the open standard
fundamental domain: `β` conjugates `SL(2, ℤ) ∩ β⁻¹ Γ₀(N) β` onto the congruence subgroup
`Γ₀(N) ∩ β SL(2, ℤ) β⁻¹` of `Γ₀(N)`, whose fundamental domain made of finitely many translates of
`𝒟ᵒ` carries `|F|²` with a finite integral. The Hecke operator `T_p` of `maassHeckeOperator` is a
sum of such functions, so `T_p F` is square-integrable on `Γ₀(N) \ ℍ`. With its
`Γ₀(N)`-invariance (`UpperHalfPlane.maassHeckeOperator_smul_eq`) and its eigenvalue
(`UpperHalfPlane.hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero`), `T_p` preserves the
space `M(N, 1, λ)` of Maass forms of trivial character for every prime `p ∤ N`, `N ≠ 0`, and so
the Maass forms on `Γ₀(N)` of `UpperHalfPlane.IsMaassForm`, whose square-integrability was the
missing property of `T_p f`.

## Main results

* `UpperHalfPlane.integrableOn_norm_sq_comp_smul`: `F(βz)` is square-integrable on every
  `σ 𝒟ᵒ` when `SL(2, ℤ) ∩ β SL(2, ℤ) β⁻¹` has finite index, for instance for `β ∈ GL(2, ℚ)`.
* `UpperHalfPlane.integrableOn_maassHeckeOperator`: `T_p F` is square-integrable on
  `Γ₀(N) \ ℍ`.
* `UpperHalfPlane.maassHeckeOperator_mem_maassSpace`: `T_p` preserves `M(N, 1, λ)` for primes
  `p ∤ N`.
* `UpperHalfPlane.IsMaassForm.maassHeckeOperator_isMaassForm`: `T_p` preserves the Maass forms on
  `Γ₀(N)` of `UpperHalfPlane.IsMaassForm` for primes `p ∤ N`.
-/

open MeasureTheory CongruenceSubgroup ModularGroup Matrix SpecialLinearGroup HeckeRing TauCeti

open scoped MatrixGroups Pointwise

namespace UpperHalfPlane

variable {N p : ℕ} {χ : DirichletCharacter ℂ N} {eigenvalue : ℂ} {F : ℍ → ℂ}
  {Γ : Subgroup SL(2, ℤ)} {b : GL (Fin 2) ℝ} {x : SL(2, ℤ)} (β : GL (Fin 2) ℚ) (σ : SL(2, ℤ))
  (z : ℍ) {f g : ℂ → ℂ}

variable (Γ b) in
lemma toConjAct_smul_conjGL_eq :
    ConjAct.toConjAct b • (conjGL Γ b).map (mapGL ℝ) = (Γ ⊓ conjGL ⊤ b⁻¹).map (mapGL ℝ) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
    ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · rintro ⟨s, hs, hsx⟩
    rcases mem_conjGL.mp hs with ⟨y, hy, hys⟩
    have hys' : mapGL ℝ y = b * mapGL ℝ s * b⁻¹ := hys
    refine ⟨y, ⟨hy, mem_conjGL.mpr ⟨s, Subgroup.mem_top s, ?_⟩⟩, ?_⟩
    · rw [hys, inv_inv]
      group
    · rw [hys', hsx]
      group
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    rcases mem_conjGL.mp hy' with ⟨s, -, hs⟩
    have hs' : mapGL ℝ s = b⁻¹ * mapGL ℝ y * b⁻¹⁻¹ := hs
    refine ⟨s, mem_conjGL.mpr ⟨y, hy, ?_⟩, ?_⟩
    · rw [hs, inv_inv]
      group
    · rw [hs', inv_inv]

variable (b) in
lemma center_le_conjGL (hΓ : Subgroup.center SL(2, ℤ) ≤ Γ) :
    Subgroup.center SL(2, ℤ) ≤ conjGL Γ b := by
  intro y hy
  refine mem_conjGL.mpr ⟨y, hΓ hy, ?_⟩
  rcases mem_center_iff_eq_one_or_eq_neg_one.mp hy with rfl | rfl
  · simp
  · have h : b * toGL (-1 : SL(2, ℝ)) = toGL (-1) * b := by
      ext i j
      simp
    simp [h]

lemma smul_smul_eq_of_mem_conjGL (hx : x ∈ conjGL Γ b) : ∃ y ∈ Γ, b • (x • z) = y • (b • z) := by
  rcases mem_conjGL.mp hx with ⟨y, hy, hyx⟩
  have hyx' : mapGL ℝ y = b * mapGL ℝ x * b⁻¹ := hyx
  have h : b * mapGL ℝ x = mapGL ℝ y * b := by
    rw [hyx', inv_mul_cancel_right]
  refine ⟨y, hy, ?_⟩
  rw [sl_moeb, sl_moeb, smul_smul, smul_smul]
  exact congrArg (· • z) h

lemma norm_comp_smul_smul (hF : F ∈ maassSpace N χ eigenvalue) (hx : x ∈ conjGL (Gamma0 N) b) :
    ‖F (b • (x • z))‖ = ‖F (b • z)‖ := by
  rcases smul_smul_eq_of_mem_conjGL z hx with ⟨y, hy, h⟩
  rw [h, smul_eq_of_mem_maassSpace hF hy, norm_mul, norm_dirichletCharacter_of_mem_gamma0 χ hy,
    one_mul]

variable [NeZero N] in
/-- **Compositions with rational matrices are square-integrable on the translates of `𝒟ᵒ`**: for
`F` in `M(N, χ, λ)`, `N ≠ 0`, and `b ∈ GL(2, ℝ)` such that `SL(2, ℤ) ∩ b SL(2, ℤ) b⁻¹` has finite
index (as for `b ∈ GL(2, ℚ)`), `|F(bz)|²` is integrable on `σ 𝒟ᵒ` for every `σ ∈ SL(2, ℤ)`. -/
lemma integrableOn_norm_sq_comp_smul (hF : F ∈ maassSpace N χ eigenvalue)
    (hb : (conjGL ⊤ b⁻¹).FiniteIndex) : IntegrableOn (fun z ↦ ‖F (b • z)‖ ^ 2) (σ • fdo) := by
  have hcan : IntegrableOn (fun z ↦ ‖F (b • z)‖ ^ 2)
      (⋃ q : SL(2, ℤ) ⧸ (conjGL (Gamma0 N) b).withCenter, (q.out : SL(2, ℤ))⁻¹ • fdo) := by
    refine (isFundamentalDomain_smul_of_inv_conjAct_eq (Γ' := conjGL (Gamma0 N) b) (α := b⁻¹)
      (by rw [inv_inv]; exact toConjAct_smul_conjGL_eq _ _)
      (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter (Gamma0 N ⊓ conjGL ⊤ b⁻¹))
      |>.integrableOn_iff (isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter _)
        fun σ' z ↦ ?_).mp ?_
    · rcases σ'.2 with ⟨x, hx, hσ'⟩
      rw [Subgroup.smul_def, ← hσ', QuotientGroup.mk'_apply, pslMk_smul,
        norm_comp_smul_smul z hF hx]
    · have hcomp : (fun z ↦ ‖F (b • z)‖ ^ 2) = (fun u ↦ ‖F u‖ ^ 2) ∘ (b • ·) := rfl
      rw [hcomp, ← Set.preimage_smul, (measurePreserving_smul b volume).integrableOn_comp_preimage
          (measurableEmbedding_const_smul b)]
      exact integrableOn_finite_iUnion.mpr fun q ↦ integrableOn_norm_sq_smul_fdo hF _
  rcases QuotientGroup.mk_out_eq_mul (conjGL (Gamma0 N) b).withCenter σ⁻¹ with ⟨k, hk⟩
  have hk' : (k : SL(2, ℤ)) ∈ conjGL (Gamma0 N) b :=
    (Subgroup.withCenter_eq_self_iff.mpr <|
      center_le_conjGL b (CongruenceSubgroup.center_le_Gamma0 N)).le k.2
  have hsub : ((QuotientGroup.mk σ⁻¹ : SL(2, ℤ) ⧸ (conjGL (Gamma0 N) b).withCenter).out)⁻¹ • fdo ⊆
      ⋃ q : SL(2, ℤ) ⧸ (conjGL (Gamma0 N) b).withCenter, (q.out : SL(2, ℤ))⁻¹ • fdo :=
    Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (conjGL (Gamma0 N) b).withCenter ↦
      (q.out : SL(2, ℤ))⁻¹ • fdo) _
  have hσ : σ • (fdo : Set ℍ) = (k : SL(2, ℤ)) •
      (((QuotientGroup.mk σ⁻¹ : SL(2, ℤ) ⧸ (conjGL (Gamma0 N) b).withCenter).out)⁻¹ • fdo) := by
    rw [hk, smul_smul]
    congr 1
    group
  rw [hσ, integrableOn_sl_smul_iff]
  · exact hcan.mono_set hsub
  · intro u
    rw [norm_comp_smul_smul u hF (inv_mem hk')]

lemma finiteIndex_conjGL_map_inv : (conjGL ⊤ (β.map (algebraMap ℚ ℝ))⁻¹).FiniteIndex := by
  have h : algebraMap ℚ ℝ = Rat.castHom ℝ := RingHom.ext_rat _ _
  rw [← map_inv, h]
  exact finiteIndex_conjGL β⁻¹

variable [NeZero N] in
lemma memLp_comp_smul (hF : F ∈ maassSpace N χ eigenvalue) :
    MemLp (fun z ↦ F (β.map (algebraMap ℚ ℝ) • z)) 2 (volume.restrict (σ • fdo)) :=
  (memLp_two_iff_integrable_sq_norm ((continuous_of_mem_maassSpace hF).comp
    (continuous_const_smul _)).aestronglyMeasurable).mpr <|
      integrableOn_norm_sq_comp_smul σ hF (finiteIndex_conjGL_map_inv β)

lemma maassHeckeOperator_comp_ofComplex (hp : p.Prime) : maassHeckeOperator p (F ∘ ofComplex) z =
    ((√p)⁻¹ : ℝ) * (F ((GL2.scaleRep p).map (algebraMap ℚ ℝ) • z) +
      ∑ b : Fin p, F ((GL2.upperTriRep p b).map (algebraMap ℚ ℝ) • z)) := by
  have hs : (((GL2.scaleRep p).map (algebraMap ℚ ℝ) • z : ℍ) : ℂ) = p * z := by
    rw [coe_smul_of_det_pos]
    · simp [num, denom, GL2.coe_scaleRep p hp.pos]
    · rw [GeneralLinearGroup.val_det_apply]
      exact ModularForm.det_map_ratCast_pos (GL2.det_scaleRep_pos p)
  rw [maassHeckeOperator, ← Fin.sum_univ_eq_sum_range (fun j ↦ (F ∘ ofComplex) ((↑z + j) / p)) p]
  simp only [Function.comp_apply, ← hs, ← GL2.coe_upperTriRep_smul, ofComplex_apply]

variable [NeZero N] in
/-- **`T_p` of a Maass form is square-integrable**: for `F` in `M(N, χ, λ)`, `N ≠ 0`, and a prime
`p`, `|T_p F|²` is integrable on the fundamental domain `gammaZeroDomain N` of `Γ₀(N)`, `T_p F`
being a combination of the functions `F(βz)` with `β` the `p + 1` matrices of `T_p`. -/
lemma integrableOn_maassHeckeOperator (hF : F ∈ maassSpace N χ eigenvalue) (hp : p.Prime) :
    IntegrableOn (fun τ : ℍ ↦ ‖maassHeckeOperator p (F ∘ ofComplex) τ‖ ^ 2)
      (gammaZeroDomain N) := by
  refine integrableOn_finite_iUnion.mpr fun q ↦ ?_
  have hmem : MemLp (fun τ : ℍ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) 2
      (volume.restrict ((q.out : SL(2, ℤ))⁻¹ • fdo)) := by
    convert ((memLp_comp_smul (GL2.scaleRep p) (q.out : SL(2, ℤ))⁻¹ hF).add
      (memLp_finsetSum Finset.univ fun b _ ↦
        memLp_comp_smul (GL2.upperTriRep p b) (q.out : SL(2, ℤ))⁻¹ hF)).const_mul
      (((√p)⁻¹ : ℝ) : ℂ) using 1
    funext τ
    simp only [maassHeckeOperator_comp_ofComplex τ hp, Pi.add_apply]
  exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem

variable [NeZero N] in
/-- **The Hecke operators preserve Maass forms**: for a Maass form `F` in `M(N, 1, λ)` of trivial
character, `N ≠ 0`, and a prime `p ∤ N`, the function `T_p F` on `ℍ` lies in `M(N, 1, λ)`: it is
smooth, `Γ₀(N)`-invariant, square-integrable on `Γ₀(N) \ ℍ`, and has eigenvalue `λ`. -/
lemma maassHeckeOperator_mem_maassSpace (hF : F ∈ maassSpace N 1 eigenvalue) (hp : p.Prime)
    (hpN : p.Coprime N) :
    (fun τ : ℍ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) ∈ maassSpace N 1 eigenvalue := by
  have heq : Set.EqOn ((fun τ : ℍ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) ∘ ofComplex)
      (maassHeckeOperator p (F ∘ ofComplex)) {w | 0 < w.im} := by
    intro w hw
    simp [ofComplex_apply_of_im_pos (hw : 0 < w.im)]
  refine ⟨(contDiffOn_maassHeckeOperator hp.ne_zero hF.1).congr heq, ?_, fun γ hγ z ↦ ?_,
    fun w hw ↦ ?_⟩
  · simpa using integrableOn_maassHeckeOperator hF hp
  · simp only [Function.comp_apply, ofComplex_apply, dirichletCharacter_one_apply_of_mem_gamma0 hγ,
      one_mul]
    exact maassHeckeOperator_smul_eq hp hpN (forall_smul_eq_iff.mp hF.2.2.1)
      (Subgroup.mem_map_of_mem _ hγ) z
  · rw [hyperbolicLaplacian_congr <| Filter.eventuallyEq_of_mem
      (isOpen_upperHalfPlaneSet.mem_nhds hw) heq, heq hw]
    exact hyperbolicLaplacian_maassHeckeOperator_add_mul_eq_zero hp.ne_zero (hF.1.of_le (by simp))
      hF.2.2.2 hw

lemma IsMaassFormWithCharacter.congr (hf : IsMaassFormWithCharacter N χ f eigenvalue)
    (h : Set.EqOn f g {w | 0 < w.im}) : IsMaassFormWithCharacter N χ g eigenvalue := by
  have hn : (fun z : ℍ ↦ ‖g z‖ ^ 2) = fun z : ℍ ↦ ‖f z‖ ^ 2 :=
    funext fun z ↦ by rw [h z.im_pos]
  refine ⟨hf.1.congr fun w hw ↦ (h hw).symm, hn ▸ hf.2.1, fun γ hγ z ↦ ?_, fun w hw ↦ ?_⟩
  · rw [← h (γ • z).im_pos, ← h z.im_pos]
    exact hf.2.2.1 γ hγ z
  · rw [← hyperbolicLaplacian_congr <| Filter.eventuallyEq_of_mem
      (isOpen_upperHalfPlaneSet.mem_nhds hw) h, ← h hw]
    exact hf.2.2.2 w hw

variable [NeZero N] in
/-- **The Hecke operators preserve the Maass forms on `Γ₀(N)`** of `IsMaassForm`: for a Maass form
`f` on `Γ₀(N)`, `N ≠ 0`, with eigenvalue `λ` and a prime `p ∤ N`, `T_p f` is a Maass form on
`Γ₀(N)` with eigenvalue `λ`, including its square-integrability on `Γ₀(N) \ ℍ`. -/
lemma IsMaassForm.maassHeckeOperator_isMaassForm
    (hf : IsMaassForm ((Gamma0 N).map (mapGL ℝ)) f eigenvalue) (hp : p.Prime) (hpN : p.Coprime N) :
    IsMaassForm ((Gamma0 N).map (mapGL ℝ)) (maassHeckeOperator p f) eigenvalue := by
  have hF : (fun z : ℍ ↦ f z) ∈ maassSpace N 1 eigenvalue :=
    (isMaassFormWithCharacter_one_iff.mpr hf).congr fun w hw ↦ by
      simp [ofComplex_apply_of_im_pos (hw : 0 < w.im)]
  refine isMaassFormWithCharacter_one_iff.mp <|
    (maassHeckeOperator_mem_maassSpace hF hp hpN).congr fun w hw ↦ ?_
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast hp.pos
  have h1 : 0 < ((p : ℂ) * w).im := by
    simpa using mul_pos hp0 hw
  have h2 (j : ℕ) : 0 < ((w + j) / p : ℂ).im := by
    simpa using div_pos hw hp0
  simp [maassHeckeOperator, ofComplex_apply_of_im_pos (hw : 0 < w.im), ofComplex_apply_of_im_pos h1,
    ofComplex_apply_of_im_pos (h2 _)]

end UpperHalfPlane
