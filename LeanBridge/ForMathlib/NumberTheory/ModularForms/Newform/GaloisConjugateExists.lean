import LeanBridge.ForMathlib.NumberTheory.ModularForms.GaloisAction.Gamma1
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.RationalHeckeAlgebra

/-!
# Galois conjugates of newforms are newforms

For an automorphism `σ` of `ℂ` and a newform `f = ∑ aₙ qⁿ` of level `N`, weight `k` and nebentypus
`χ`, the series `σ(f) = ∑ σ(aₙ) qⁿ` is a newform of level `N`, weight `k` and nebentypus `σ ∘ χ`, in
every weight (LeanBridge issue #38).

By `TauCeti.GaloisAction.exists_cuspForm_Gamma1_qExpansion_eq_map`, `σ(f)` is a cusp form of level
`Γ₁(N)`, of nebentypus `σ ∘ χ`, and the Hecke recurrence shows that it is an eigenform of every
`T_p` with eigenvalue `σ(a_p)`. The conjugation by `σ⁻¹` preserves the old subspace, as it commutes
with the level-raising operators, and `f` is not old. So `σ(f)` is not old, and its new component is
a nonzero eigenform of the `T_p` with the same eigenvalues. The newforms being a basis of the new
subspace, there is a newform `g` with `a_p(g) = σ(a_p)` and nebentypus `σ ∘ χ`, and so `g = σ(f)`
by the Hecke recurrence.

## Main results

* `TauCeti.GaloisAction.exists_mem_cuspFormsOld_qExpansion_eq_map`: conjugation by a field
  endomorphism of `ℂ` preserves the old subspace.
* `HeckeRing.GL2.Newform.exists_isGaloisConjugateBy`: the Galois conjugate `σ(f)` of a newform is a
  newform of the same level and weight (LeanBridge issue #38).
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix SpecialLinearGroup

namespace TauCeti.GaloisAction

variable (σ : ℂ →+* ℂ) {N : ℕ} [NeZero N] {k : ℤ}

/-- **Conjugation preserves the old subspace.** If `x` is an old form of level `Γ₁(N)`, the series
`σ(x)` is the `q`-expansion of an old form of level `Γ₁(N)`: the old subspace is spanned by the
images of the level-raising operators `V_d`, which commute with the conjugation by `σ`. -/
lemma exists_mem_cuspFormsOld_qExpansion_eq_map {x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hx : x ∈ cuspFormsOld N k) :
    ∃ x' ∈ cuspFormsOld N k, qExpansion 1 x' = PowerSeries.map σ (qExpansion 1 x) := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  let V : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    { carrier := {x | ∃ x' ∈ cuspFormsOld N k, qExpansion 1 x' = PowerSeries.map σ (qExpansion 1 x)}
      add_mem' := by
        rintro a b ⟨a', ha', hQa⟩ ⟨b', hb', hQb⟩
        refine ⟨a' + b', add_mem ha' hb', ?_⟩
        rw [FunLike.coe_add, FunLike.coe_add, ModularForm.qExpansion_add one_pos h1,
          ModularForm.qExpansion_add one_pos h1, hQa, hQb, map_add]
      zero_mem' := ⟨0, zero_mem _, by simp [qExpansion_zero]⟩
      smul_mem' := by
        rintro c a ⟨a', ha', hQa⟩
        refine ⟨σ c • a', Submodule.smul_mem _ _ ha', ?_⟩
        rw [FunLike.coe_smul, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos h1,
          ModularForm.qExpansion_smul one_pos h1, hQa, map_smul_powerSeries] }
  refine cuspFormsOld_le (V := V) (fun M d h hM g ↦ ?_) hx
  have : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd h)
  have : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd h)
  rcases exists_cuspForm_Gamma1_qExpansion_eq_map σ g with ⟨g', hg', -⟩
  refine ⟨CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) g',
    levelRaise_mem_cuspFormsOld h hM k g', ?_⟩
  rw [CuspForm.qExpansion_levelRaise (one_mem_strictPeriods_Gamma1_map M) h1,
    CuspForm.qExpansion_levelRaise (one_mem_strictPeriods_Gamma1_map M) h1, hg',
    PowerSeries.map_expand]

end TauCeti.GaloisAction

namespace HeckeRing.GL2.Newform

open GaloisAction

variable {N : ℕ} [NeZero N] {k : ℤ} (s : ℂ →+* ℂ) (f : Newform N k)

lemma ofUnitHom_comp_units_map_apply (χ : (ZMod N)ˣ →* ℂˣ) (x : ZMod N) :
    (MulChar.ofUnitHom ((Units.map (s : ℂ →* ℂ)).comp χ) : DirichletCharacter ℂ N) x =
      s ((MulChar.ofUnitHom χ : DirichletCharacter ℂ N) x) := by
  by_cases hx : IsUnit x
  · rcases hx with ⟨u, rfl⟩
    rw [MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx, MulChar.map_nonunit _ hx, map_zero]

lemma heckeTCuspNat_eq_smul_of_qExpansion_eq_map {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k ((Units.map (s : ℂ →* ℂ)).comp f.χ))
    (hQ : qExpansion 1 F = PowerSeries.map s (qExpansion 1 f.toCuspForm)) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F = s ((qExpansion 1 f.toCuspForm).coeff p) • F := by
  rw [heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom hp hχ]
  intro m
  have h : (qExpansion 1 f.toCuspForm).coeff (p * m) =
      (qExpansion 1 f.toCuspForm).coeff p * (qExpansion 1 f.toCuspForm).coeff m -
        if p ∣ m then (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1) *
          (qExpansion 1 f.toCuspForm).coeff (m / p) else 0 :=
    (heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom hp
      f.mem_charSpace _).mp (f.heckeTCuspNat_eq_qExpansion_coeff_smul hp) m
  simp only [hQ, PowerSeries.coeff_map, h, ofUnitHom_comp_units_map_apply]
  split_ifs <;> simp

lemma apply_eq_smul_of_add_eq_smul_add {T : Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hold : ∀ x ∈ cuspFormsOld N k, T x ∈ cuspFormsOld N k)
    (hnew : ∀ x ∈ cuspFormsNew N k, T x ∈ cuspFormsNew N k) {v u : CuspForm _ k} {c : ℂ}
    (hv : v ∈ cuspFormsOld N k) (hu : u ∈ cuspFormsNew N k) (hT : T (v + u) = c • (v + u)) :
    T u = c • u := by
  have h : T v - c • v = c • u - T u := by
    rw [map_add, smul_add] at hT
    rw [sub_eq_sub_iff_add_eq_add, hT, add_comm (c • u)]
  have hmem₁ : T v - c • v ∈ cuspFormsOld N k :=
    sub_mem (hold v hv) (Submodule.smul_mem _ _ hv)
  have hmem₂ : T v - c • v ∈ cuspFormsNew N k :=
    h ▸ sub_mem (Submodule.smul_mem _ _ hu) (hnew u hu)
  have h₀ : T v - c • v = 0 :=
    Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k) _ hmem₁ hmem₂
  rw [h₀] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- **Galois conjugates of newforms are newforms** (LeanBridge issue #38): for every newform `f` of
level `N` and weight `k`, and every automorphism `σ` of `ℂ`, the Galois conjugate `σ(f)` is a
newform of level `N` and weight `k`, whose nebentypus is `σ ∘ χ` by `IsGaloisConjugateBy.χ_eq`. -/
lemma exists_isGaloisConjugateBy (σ : Gal(ℂ/ℚ)) : ∃ g : Newform N k, f.IsGaloisConjugateBy σ g := by
  let s : ℂ →+* ℂ := σ
  have h1 : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := one_mem_strictPeriods_Gamma1_map N
  rcases exists_cuspForm_Gamma1_qExpansion_eq_map s f.toCuspForm with ⟨F, hQ, hd⟩
  have hχ : F ∈ cuspFormCharSpace k ((Units.map (s : ℂ →* ℂ)).comp f.χ) :=
    mem_cuspFormCharSpace_of_qExpansion_diamond_eq_map s f.mem_charSpace hQ hd
  have hold : F ∉ cuspFormsOld N k := fun hF ↦ by
    rcases exists_mem_cuspFormsOld_qExpansion_eq_map ((σ⁻¹ : Gal(ℂ/ℚ)) : ℂ →+* ℂ) hF with
      ⟨x, hx, hQx⟩
    have hxf : x = f.toCuspForm := CuspForm.qExpansion_injective one_pos h1 <| by
      beta_reduce
      rw [hQx, hQ]
      ext n
      simp [s]
    exact f.ne_zero <| Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k) _
      (hxf ▸ hx) f.isNew
  rcases Submodule.mem_sup.mp ((sup_cuspFormsOld_cuspFormsNew_eq_top N k).ge
    (Submodule.mem_top (x := F))) with ⟨v, hv, u, hu, rfl⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hold (by simpa using hv)
  have hT {p : ℕ} (hp : p.Prime) : heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) u =
      s ((qExpansion 1 f.toCuspForm).coeff p) • u :=
    apply_eq_smul_of_add_eq_smul_add (fun _ hx ↦ heckeTCuspNat_mem_cuspFormsOld hp hx)
      (fun _ hx ↦ heckeTCuspNat_mem_cuspFormsNew hp hx) hv hu
      (heckeTCuspNat_eq_smul_of_qExpansion_eq_map s f hχ hQ hp)
  have hD (e : (ZMod N)ˣ) : diamondOpCusp k e u = (((Units.map (s : ℂ →* ℂ)).comp f.χ) e : ℂ) • u :=
    apply_eq_smul_of_add_eq_smul_add (fun _ hx ↦ diamondOpCusp_mem_cuspFormsOld e hx)
      (fun _ hx ↦ diamondOpCusp_mem_cuspFormsNew e hx) hv hu
      (diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ e hχ)
  have hne : (basis N k).repr ⟨u, hu⟩ ≠ 0 := fun h ↦
    hu0 <| congrArg Subtype.val ((basis N k).repr.map_eq_zero_iff.mp h)
  rcases Finsupp.ne_iff.mp hne with ⟨g, hg⟩
  have hg' : (basis N k).repr ⟨u, hu⟩ g ≠ 0 := by simpa using hg
  have hc {t : heckeCuspNewRationalAlgebra N k} {c : ℂ}
      (ht : (t : Module.End ℂ (cuspFormsNew N k)) ⟨u, hu⟩ = c • ⟨u, hu⟩) :
      g.heckeCuspNewRationalCharacter t = c := by
    have h₁ : (basis N k).repr ((t : Module.End ℂ (cuspFormsNew N k)) ⟨u, hu⟩) g =
        g.heckeCuspNewRationalCharacter t * (basis N k).repr ⟨u, hu⟩ g :=
      basis_repr_apply_heckeCuspNewRationalAlgebra t ⟨u, hu⟩
    simp only [ht, map_smul] at h₁
    exact (mul_right_cancel₀ hg' h₁).symm
  exact ⟨g, isGaloisConjugateBy_iff.mpr <| qExpansion_coeff_eq_of_forall_prime (fun _ hp ↦
    (heckeCuspNewRationalCharacter_heckeTCuspNewEndOfPrime hp).symm.trans <| hc <|
      Subtype.ext (hT hp)) fun e ↦
      (heckeCuspNewRationalCharacter_diamondOpCuspNewEnd e).symm.trans <| hc <| Subtype.ext (hD e)⟩

end HeckeRing.GL2.Newform
