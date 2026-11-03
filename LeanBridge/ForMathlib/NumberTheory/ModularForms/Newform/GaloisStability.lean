import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace

/-!
# Galois orbits of newforms and the rational Hecke algebra

The rational Hecke algebra `T_ℚ` of the newspace (`TauCeti.heckeCuspNewRationalAlgebra`) is a
`ℚ`-form of its complex span, the complex newspace Hecke algebra `T_ℂ`: the natural map
`ℂ ⊗_ℚ T_ℚ → End_ℂ(S_k(Γ₁(N))ⁿᵉʷ)` is injective, i.e. operators of `T_ℚ` that are linearly
independent over `ℚ` stay linearly independent over `ℂ`. Classically this comes from a
`ℚ`-structure on `S_k(Γ₁(N))` stable under the Hecke and diamond operators, such as the forms with
rational Fourier coefficients (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, Theorem 3.52), or from the Eichler–Shimura isomorphism. Here it follows from the theorem
that the Galois conjugates of newforms are newforms: the characters of the newforms embed `T_ℚ` into
the product of the coefficient fields of the Galois orbits, of total degree the number of newforms,
which is the dimension of `T_ℂ`.

The rational Hecke algebra cuts the newspace into the pieces of the LMFDB decomposition (LMFDB
`cmf.decomposition.new.gamma0chi`, `cmf.newspaces`): two newforms are Galois conjugate exactly when
their characters on `T_ℚ` have the same kernel, and the vectors killed by that kernel form the span
of their Galois orbit, of dimension `[ℚ(f) : ℚ]`.

## Main results

* `TauCeti.hasRationalHeckeForm`: the rational Hecke algebra of the newspace is a `ℚ`-form of its
  complex span.
* `HeckeRing.GL2.Newform.range_heckeCuspNewRationalCharacter`: the character of `f` on the rational
  Hecke algebra has image the coefficient field.
* `HeckeRing.GL2.Newform.isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le`,
  `HeckeRing.GL2.Newform.isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_eq`: the Galois
  orbits of newforms are the fibres of the kernels of their characters on `T_ℚ`.
* `HeckeRing.GL2.Newform.map_heckeCuspNewPiece_ker`: the piece of the newspace cut out by the kernel
  of the character of a newform `f` on `T_ℚ` is the span of the Galois orbit of `f`.
-/

open HeckeRing GL2 Algebra TensorProduct TauCeti Module

namespace TauCeti

variable (N : ℕ) [NeZero N] (k : ℤ)

open Newform in
/-- **The rational Hecke algebra of the newspace is a `ℚ`-form of its complex span**, in every
weight: the natural map `ℂ ⊗_ℚ T_ℚ → End_ℂ(S_k(Γ₁(N))ⁿᵉʷ)` is injective. The characters of the
newforms embed `T_ℚ` into the product of the coefficient fields of the Galois orbits, of total
degree the number of newforms, which is the dimension of the complex span of `T_ℚ`. -/
lemma hasRationalHeckeForm : HasRationalHeckeForm N k := by
  classical
  let : Fintype (Newform N k) := Fintype.ofFinite _
  let : Fintype (NewformOrbit N k) := Fintype.ofFinite _
  let Λ : heckeCuspNewRationalAlgebra N k →ₗ[ℚ] ∀ O : NewformOrbit N k, CoefficientField O.out :=
    LinearMap.pi fun O ↦
      { toFun t := ⟨O.out.heckeCuspNewRationalCharacter t,
          heckeCuspNewRationalCharacter_mem_coefficientField t⟩
        map_add' t t' := Subtype.ext (map_add _ t t')
        map_smul' c t := Subtype.ext (map_smul O.out.heckeCuspNewRationalCharacter c t) }
  have hΛ : Function.Injective Λ := fun t t' htt' ↦ Subtype.ext <| (basis N k).ext fun g ↦ by
    have hO : (⟦g⟧ : NewformOrbit N k).out.heckeCuspNewRationalCharacter t =
        (⟦g⟧ : NewformOrbit N k).out.heckeCuspNewRationalCharacter t' :=
      congrArg Subtype.val (congrFun htt' ⟦g⟧)
    rcases Quotient.mk_out (s := galoisOrbitRel N k) g with ⟨σ, hσ⟩
    rw [apply_basis_eq_heckeCuspNewRationalCharacter_smul,
      apply_basis_eq_heckeCuspNewRationalCharacter_smul, hσ.heckeCuspNewRationalCharacter_eq,
      AlgHom.comp_apply, AlgHom.comp_apply, hO]
  have : FiniteDimensional ℚ (heckeCuspNewRationalAlgebra N k) := .of_injective Λ hΛ
  have h₁ : finrank ℚ (heckeCuspNewRationalAlgebra N k) ≤
      ∑ O : NewformOrbit N k, finrank ℚ (CoefficientField O.out) :=
    (LinearMap.finrank_le_finrank_of_injective hΛ).trans_eq (finrank_pi_fintype ℚ)
  have hO (O : NewformOrbit N k) : finrank ℚ (CoefficientField O.out) =
      (Finset.univ.filter fun g : Newform N k ↦ (⟦g⟧ : NewformOrbit N k) = O).card := by
    rw [← ncard_galoisOrbit_eq, ← Set.ncard_coe_finset]
    congr 1
    ext g
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ (Quotient.sound h).symm.trans O.out_eq,
      fun h ↦ Quotient.exact (O.out_eq.trans h.symm)⟩
  have h₂ : ∑ O : NewformOrbit N k, finrank ℚ (CoefficientField O.out) =
      Fintype.card (Newform N k) := by
    rw [Finset.sum_congr rfl fun O _ ↦ hO O, ← Finset.card_eq_sum_card_fiberwise
      fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _), Finset.card_univ]
  have h₃ : finrank ℂ (LinearMap.range (heckeCuspNewComplexify N k).toLinearMap) =
      Fintype.card (Newform N k) := by
    have e : LinearMap.range (heckeCuspNewComplexify N k).toLinearMap =
        Subalgebra.toSubmodule (heckeTDiamondCuspNewAlgebra N k) := by
      rw [← range_heckeCuspNewComplexify]
      rfl
    rw [e, Subalgebra.finrank_toSubmodule,
      Newform.heckeTDiamondCuspNewAlgebraEquiv.toLinearEquiv.finrank_eq,
      finrank_fintype_fun_eq_card]
  have h₄ : finrank ℂ (LinearMap.range (heckeCuspNewComplexify N k).toLinearMap) +
      finrank ℂ (LinearMap.ker (heckeCuspNewComplexify N k).toLinearMap) =
        finrank ℂ (ℂ ⊗[ℚ] heckeCuspNewRationalAlgebra N k) :=
    LinearMap.finrank_range_add_finrank_ker _
  have : Module.Free ℚ (heckeCuspNewRationalAlgebra N k) :=
    @Free.of_divisionRing ℚ _ _ (addCommMonoidToAddCommGroup ℚ) _
  have h₅ : finrank ℂ (ℂ ⊗[ℚ] heckeCuspNewRationalAlgebra N k) =
      finrank ℚ (heckeCuspNewRationalAlgebra N k) :=
    finrank_baseChange
  have h₆ : finrank ℂ (LinearMap.ker (heckeCuspNewComplexify N k).toLinearMap) = 0 := by
    omega
  exact LinearMap.ker_eq_bot.mp <| Submodule.finrank_eq_zero.mp h₆

end TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k}

variable (f) in
/-- **The character of a newform on the rational Hecke algebra has image the coefficient field.** -/
lemma range_heckeCuspNewRationalCharacter :
    f.heckeCuspNewRationalCharacter.range = (CoefficientField f).toSubalgebra := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨t, rfl⟩
    exact heckeCuspNewRationalCharacter_mem_coefficientField t
  · let R : Subalgebra ℚ ℂ := f.heckeCuspNewRationalCharacter.range
    have hR : R ≤ (CoefficientField f).toSubalgebra := by
      rintro _ ⟨t, rfl⟩
      exact heckeCuspNewRationalCharacter_mem_coefficientField t
    let L : IntermediateField ℚ ℂ := R.toIntermediateField fun y hy ↦
      R.inv_mem_of_algebraic (x := ⟨y, hy⟩) <| (IntermediateField.isAlgebraic_iff
        (x := (⟨y, hR hy⟩ : CoefficientField f))).mp (IsAlgebraic.isAlgebraic _)
    refine (CoefficientField_le_iff_forall_prime_and_char f L).mpr ⟨fun p hp ↦ ?_, fun u ↦ ?_⟩ hx
    · exact ⟨⟨_, heckeTCuspNewEndOfPrime_mem hp⟩,
        heckeCuspNewRationalCharacter_heckeTCuspNewEndOfPrime hp⟩
    · exact ⟨⟨_, diamondOpCuspNewEnd_mem_heckeCuspNewRationalAlgebra u⟩,
        heckeCuspNewRationalCharacter_diamondOpCuspNewEnd u⟩

/-- **The Galois orbits of newforms are cut out by the rational Hecke algebra**, in every weight: a
newform `g` is Galois conjugate to the newform `f` exactly when its character `λ_g` on the rational
Hecke algebra `T_ℚ` of the newspace vanishes on the kernel of the character `λ_f` of `f`. If `λ_g`
vanishes on the kernel of `λ_f`, then `λ_g = σ ∘ λ_f` for an automorphism `σ` of `ℂ` extending the
induced embedding of the number field `λ_f(T_ℚ)`, and then `g = σ(f)` by the Hecke recurrence. -/
lemma isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le : f.IsGaloisConjugate g ↔
    RingHom.ker f.heckeCuspNewRationalCharacter ≤ RingHom.ker g.heckeCuspNewRationalCharacter := by
  refine ⟨fun ⟨σ, hσ⟩ t ht ↦ ?_, fun h ↦ ?_⟩
  · rw [RingHom.mem_ker, hσ.heckeCuspNewRationalCharacter_eq, AlgHom.comp_apply,
      RingHom.mem_ker.mp ht, map_zero]
  let R : Subalgebra ℚ (ℂ × ℂ) :=
    (f.heckeCuspNewRationalCharacter.prod g.heckeCuspNewRationalCharacter).range
  let pr : R →ₐ[ℚ] ℂ := (AlgHom.fst ℚ ℂ ℂ).comp R.val
  have hpr : Function.Injective pr := by
    rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ htt'
    have h₁ : f.heckeCuspNewRationalCharacter t = f.heckeCuspNewRationalCharacter t' := htt'
    have hker : t - t' ∈ RingHom.ker g.heckeCuspNewRationalCharacter :=
      h <| RingHom.mem_ker.mpr ((map_sub _ t t').trans (sub_eq_zero.mpr h₁))
    exact Subtype.ext <| Prod.ext h₁ <| sub_eq_zero.mp <|
      (map_sub g.heckeCuspNewRationalCharacter t t').symm.trans (RingHom.mem_ker.mp hker)
  have hsub : (pr.range : Set ℂ) ⊆ CoefficientField f := by
    rintro _ ⟨⟨_, t, rfl⟩, rfl⟩
    exact heckeCuspNewRationalCharacter_mem_coefficientField t
  let L : IntermediateField ℚ ℂ := pr.range.toIntermediateField fun x hx ↦
    pr.range.inv_mem_of_algebraic (x := ⟨x, hx⟩) <| (IntermediateField.isAlgebraic_iff
      (x := (⟨x, hsub hx⟩ : CoefficientField f))).mp (IsAlgebraic.isAlgebraic _)
  have : Countable (CoefficientField f : Set ℂ) := inferInstanceAs (Countable (CoefficientField f))
  have : Countable L := (Set.inclusion_injective hsub).countable
  let ι : L →ₐ[ℚ] ℂ :=
    ((AlgHom.snd ℚ ℂ ℂ).comp R.val).comp (AlgEquiv.ofInjective pr hpr).symm.toAlgHom
  rcases IntermediateField.exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
  have key (t : heckeCuspNewRationalAlgebra N k) :
      g.heckeCuspNewRationalCharacter t = σ (f.heckeCuspNewRationalCharacter t) := by
    have he : (AlgEquiv.ofInjective pr hpr).symm
        ⟨f.heckeCuspNewRationalCharacter t, ⟨_, t, rfl⟩, rfl⟩ = ⟨_, t, rfl⟩ :=
      (AlgEquiv.symm_apply_eq _).mpr <|
        Subtype.ext (AlgEquiv.ofInjective_apply pr hpr ⟨_, t, rfl⟩).symm
    exact ((hσ ⟨_, ⟨_, t, rfl⟩, rfl⟩).trans (congrArg (fun r : R ↦ (r : ℂ × ℂ).2) he)).symm
  exact ⟨σ, isGaloisConjugateBy_of_heckeCuspNewRationalCharacter_eq key⟩

/-- **The Galois orbits of newforms are the fibres of the rational Hecke characters**, in every
weight: two newforms are Galois conjugate exactly when their characters on the rational Hecke
algebra `T_ℚ` of the newspace have the same kernel. The newforms whose characters have a given
kernel thus form a Galois orbit, and span its piece of the newspace (LMFDB
`cmf.decomposition.new.gamma0chi`, `cmf.newspaces`). -/
lemma isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_eq : f.IsGaloisConjugate g ↔
    RingHom.ker f.heckeCuspNewRationalCharacter = RingHom.ker g.heckeCuspNewRationalCharacter :=
  ⟨fun h ↦ (isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le.mp h).antisymm
    (isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le.mp h.symm),
    fun h ↦ isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le.mpr h.le⟩

variable (f) in
/-- **The newspace breaks up under the rational Hecke algebra into the spans of the Galois
orbits**, in every weight: the piece of the newspace cut out by the kernel of the character of the
rational Hecke algebra `T_ℚ` on a newform `f` is the newform subspace of `f`, the span of its Galois
orbit (LMFDB `cmf.decomposition.new.gamma0chi`, `cmf.newspaces`). -/
lemma map_heckeCuspNewPiece_ker :
    (heckeCuspNewPiece N k (RingHom.ker f.heckeCuspNewRationalCharacter)).map
      (cuspFormsNew N k).subtype = f.newformSubspace := by
  classical
  let : Fintype (Newform N k) := Fintype.ofFinite _
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro _ ⟨v, hv, rfl⟩
    rw [← (basis N k).sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun g _ ↦ ?_
    rw [map_smul, Submodule.subtype_apply, coe_basis_apply]
    by_cases hg : (basis N k).repr v g = 0
    · rw [hg, zero_smul]
      exact zero_mem _
    refine Submodule.smul_mem _ _ <| toCuspForm_mem_newformSubspace <|
      isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le.mpr fun t ht ↦ ?_
    have h₀ : (t : Module.End ℂ (cuspFormsNew N k)) v = 0 :=
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv t) ht
    have h₁ : (basis N k).repr ((t : Module.End ℂ (cuspFormsNew N k)) v) g =
        g.heckeCuspNewRationalCharacter t * (basis N k).repr v g :=
      basis_repr_apply_heckeCuspNewRationalAlgebra t v
    rw [h₀, map_zero, Finsupp.zero_apply] at h₁
    exact RingHom.mem_ker.mpr <| (mul_eq_zero.mp h₁.symm).resolve_right hg
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨basis N k g, (Submodule.mem_iInf _).mpr fun t ↦ (Submodule.mem_iInf _).mpr fun ht ↦ ?_,
      coe_basis_apply g⟩
    rw [LinearMap.mem_ker, apply_basis_eq_heckeCuspNewRationalCharacter_smul,
      RingHom.mem_ker.mp (isGaloisConjugate_iff_ker_heckeCuspNewRationalCharacter_le.mp hg ht),
      zero_smul]

end HeckeRing.GL2.Newform
