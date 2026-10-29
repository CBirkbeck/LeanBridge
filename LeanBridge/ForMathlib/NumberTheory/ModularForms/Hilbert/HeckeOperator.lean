import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeRing

/-!
# Hecke operators on Hilbert modular forms

The slash operator `f ↦ f ∣ₖ g` of weight `k` is a right action of the monoid `GL₂⁺(F)` of
matrices with totally positive determinant. For a Hecke pair `(Γ, GL₂⁺(F))`, such as
`Γ = Γ₀(𝔑)_𝔟`, a double coset `ΓαΓ = ⊔ᵢ Γαᵢ` acts on the functions satisfying the transformation
law of weight `k` for `Γ` by `f ↦ ∑ᵢ f ∣ₖ αᵢ`, which does not depend on the representatives and
again satisfies the transformation law; linearly, the Hecke ring acts.

For a prime `𝔭 = (π)` with `π` totally positive, so that `𝔭` is trivial in the narrow class
group, the Hecke operator `T_𝔭` of the double coset `Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟` acts on each
component `f_𝔟` of a Hilbert modular form (LMFDB `mf.hilbert`). A Hilbert modular form is a Hecke
eigenform if it is nonzero and an eigenvector, with one eigenvalue for all components, of every
such `T_𝔭` with `𝔭 ∤ 𝔑`. The general `T_𝔭`, which permutes the components by `𝔟 ↦ 𝔟𝔭⁻¹`, is not
formalised. That the slash operator preserves holomorphy and boundedness at the cusps, making `T_𝔭`
an endomorphism of the space of Hilbert modular forms, is proved in `Hilbert/HeckeSpace.lean`.

## Main definitions

* `HilbertModularForm.slashInvariants`: the functions satisfying the transformation law for `Γ`.
* `HilbertModularForm.heckeOperator`: the Hecke operator `f ↦ ∑ᵢ f ∣ₖ αᵢ` of a double coset.
* `HilbertModularForm.heckeAlgebraAction`: the action of the Hecke ring.
* `HilbertModularForm.heckeTComponent`: the Hecke operator `T_𝔭` on a component.
* `HilbertModularForm.IsHeckeEigenform`: Hecke eigenforms.
* `HilbertModularForm.indicatorOne`: the weight-`0` form that is `1` on one component.

## Main results

* `HilbertModularForm.slash_mul`: the slash operator is a right action of `GL₂⁺(F)`.
* `HilbertModularForm.heckeOperator_eq_sum`: the Hecke operator is the sum over any family of
  representatives of the right cosets.
* `HilbertModularForm.isHolomorphic_heckeOperator`: the Hecke operators preserve holomorphy when
  the slash operators do.
* `HilbertModularForm.heckeTComponent_smul_eq`: `T_𝔭` preserves the transformation law.
* `HilbertModularForm.isHeckeEigenform_indicatorOne`: Hecke eigenforms exist.
-/

open Matrix hiding mul_inv_rev

open NumberField InfinitePlace UpperHalfPlane HilbertModularGroup DoubleCoset MulAction

open scoped Pointwise nonZeroDivisors

namespace HilbertModularForm

variable {F : Type*} [Field F] (k : {w : InfinitePlace F // w.IsReal} → ℤ) (g h : GL (Fin 2) F)
  (z : {w : InfinitePlace F // w.IsReal} → ℍ) (f : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)

lemma smul_mul : smul (g * h) z = smul g (smul h z) :=
  funext fun w ↦ by
    rw [smul, smul, smul, map_mul, mul_smul]

lemma isTotallyPositive_det (x : glTotallyPositive F) :
    IsTotallyPositive (x : GL (Fin 2) F).det.val :=
  mem_totallyPositiveUnits.mp x.2

variable [NumberField F]

lemma automorphyFactor_zero : automorphyFactor 0 g z = 1 := by
  simp [automorphyFactor]

lemma slash_zero_const (b : ℂ) : slash 0 g (fun _ ↦ b) = fun _ ↦ b := by
  ext z
  rw [slash, automorphyFactor_zero, inv_one, one_mul]

lemma automorphyFactor_mul (hg : IsTotallyPositive g.det.val) (hh : IsTotallyPositive h.det.val) :
    automorphyFactor k (g * h) z = automorphyFactor k g (smul h z) * automorphyFactor k h z := by
  rw [automorphyFactor, automorphyFactor, automorphyFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have hd : denom (mapGL w (g * h)) (z w) =
      denom (mapGL w g) (smul h z w) * denom (mapGL w h) (z w) := by
    rw [map_mul, denom_cocycle_σ, σ, ite_eq_left (det_mapGL_pos h hh w)]
    rfl
  rw [hd, map_mul, Units.val_mul, map_mul, Real.mul_rpow (hg w.1 w.2).le (hh w.1 w.2).le, mul_zpow]
  push_cast
  ring1

/-- **The slash operator is a right action of `GL₂⁺(F)`**: `f ∣ₖ gh = (f ∣ₖ g) ∣ₖ h` for `g` and
`h` with totally positive determinant, by the cocycle relation of the automorphy factor. -/
lemma slash_mul (hg : IsTotallyPositive g.det.val) (hh : IsTotallyPositive h.det.val) :
    slash k (g * h) f = slash k h (slash k g f) := by
  ext z
  rw [slash, slash, slash, automorphyFactor_mul k g h z hg hh, smul_mul, mul_inv]
  ring1

variable (Γ : Subgroup (GL (Fin 2) F))

/-- The space of functions `f : ℍⁿ → ℂ` satisfying the transformation law of weight `k` for a
subgroup `Γ` of `GL₂(F)`: `f ∣ₖ γ = f`, that is, `f(γ z) = automorphyFactor k γ z · f(z)`, for
every `γ ∈ Γ`. -/
def slashInvariants : Submodule ℂ (({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) where
  carrier := {f | ∀ γ ∈ Γ, slash k γ f = f}
  add_mem' {f₁ f₂} hf₁ hf₂ γ hγ := by
    ext z
    simp only [slash, Pi.add_apply, mul_add]
    rw [← slash, ← slash, hf₁ γ hγ, hf₂ γ hγ]
  zero_mem' γ _ := by
    ext z
    simp [slash]
  smul_mem' c f hf γ hγ := by
    ext z
    simp only [slash, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← slash, hf γ hγ]

variable {k Γ f} in
lemma mem_slashInvariants_iff (hΓ : ∀ γ ∈ Γ, IsTotallyPositive γ.det.val) :
    f ∈ slashInvariants k Γ ↔ ∀ γ ∈ Γ, ∀ z, f (smul γ z) = automorphyFactor k γ z * f z := by
  refine forall₂_congr fun γ hγ ↦ ⟨fun h z ↦ ?_, fun h ↦ funext fun z ↦ ?_⟩
  · rw [← congrFun h z, slash, mul_inv_cancel_left₀ (automorphyFactor_ne_zero k γ z (hΓ γ hγ))]
  · rw [slash, h z, inv_mul_cancel_left₀ (automorphyFactor_ne_zero k γ z (hΓ γ hγ))]

/-- The slash operator `f ↦ f ∣ₖ g` as a linear map. -/
noncomputable def slashLinearMap : (({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) →ₗ[ℂ]
    ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ where
  toFun f := slash k g f
  map_add' f₁ f₂ := by
    ext z
    simp [slash, mul_add]
  map_smul' c f := by
    ext z
    simp [slash, mul_left_comm _ c]

lemma slashLinearMap_apply : slashLinearMap k g f = slash k g f :=
  rfl

variable [IsHeckeTriple (glTotallyPositive F) Γ Γ]

variable {k Γ f} in
private lemma slash_eq_of_mul_inv_mem (hf : f ∈ slashInvariants k Γ) {x y : GL (Fin 2) F}
    (hx : IsTotallyPositive x.det.val) (h : y * x⁻¹ ∈ Γ) : slash k x f = slash k y f := by
  rw [← inv_mul_cancel_right y x,
    slash_mul k _ _ f (isTotallyPositive_det ⟨_, IsHeckeTriple.left_le (H₂ := Γ) h⟩) hx, hf _ h]

variable (D : HeckeCoset (glTotallyPositive F) Γ Γ)

attribute [local instance] Fintype.ofFinite

/-- The representative `δ τᵥ⁻¹` of the `v`-th right coset `Γ δ τᵥ⁻¹` of the double coset
`D = Γ δ Γ`, as an element of `GL₂⁺(F)`. -/
noncomputable def heckeRep (v : DecompQuotient Γ Γ (D.out : GL (Fin 2) F)⁻¹) :
    glTotallyPositive F :=
  ⟨rightCosetRep D v, rightCosetRep_mem D D.out.2 (IsHeckeTriple.left_le (H₂ := Γ)) v⟩

/-- The **Hecke operator** of a double coset `D = ΓαΓ = ⊔ᵢ Γαᵢ`, `α ∈ GL₂⁺(F)`, of a Hecke pair
`(Γ, GL₂⁺(F))`, such as `Γ = Γ₀(𝔑)_𝔟`, on the functions satisfying the transformation law of
weight `k` for `Γ`: `f ↦ ∑ᵢ f ∣ₖ αᵢ`. It is defined with chosen representatives `αᵢ` but does not
depend on them (`heckeOperator_eq_sum`), and its value again satisfies the transformation law, since
right multiplication by `γ ∈ Γ` permutes the right cosets `Γαᵢ`. -/
noncomputable def heckeOperator : Module.End ℂ (slashInvariants k Γ) where
  toFun f := ⟨∑ v, slashLinearMap k (heckeRep Γ D v) f, fun γ hγ ↦ by
    rw [← slashLinearMap_apply, map_sum]
    refine Fintype.sum_equiv (toPerm (⟨γ, hγ⟩ : Γ)⁻¹) _ _ fun v ↦ ?_
    have hγ' : IsTotallyPositive γ.det.val :=
      isTotallyPositive_det ⟨γ, IsHeckeTriple.left_le (H₂ := Γ) hγ⟩
    rw [slashLinearMap_apply, slashLinearMap_apply, slashLinearMap_apply,
      ← slash_mul k _ _ f (isTotallyPositive_det _) hγ']
    refine slash_eq_of_mul_inv_mem f.2 (isTotallyPositive_det
      ⟨_, mul_mem (heckeRep Γ D v).2 (IsHeckeTriple.left_le (H₂ := Γ) hγ)⟩) ?_
    rcases exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2) with
      ⟨γ₁, hγ₁, hsplit⟩
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : GL (Fin 2) F), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient Γ Γ (D.out : GL (Fin 2) F)⁻¹) = (⟨γ, hγ⟩ : Γ)⁻¹ • v :=
      Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ)⁻¹ v
    have hprod : rightCosetRep D v * γ = γ₁ * rightCosetRep D ((⟨γ, hγ⟩ : Γ)⁻¹ • v) := by
      simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
    simpa [heckeRep, hprod] using inv_mem hγ₁⟩
  map_add' f₁ f₂ := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c f := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_heckeOperator (φ : slashInvariants k Γ) :
    (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ v, slash k (heckeRep Γ D v) φ :=
  rfl

/-- **The Hecke operator does not depend on the representatives**: for any family `(aᵢ)` in
`GL₂⁺(F)` whose right cosets `Γaᵢ` are pairwise distinct and cover `D = ΓαΓ`,
`f ∣ₖ D = ∑ᵢ f ∣ₖ aᵢ`. -/
lemma heckeOperator_eq_sum {ι : Type*} [Fintype ι] (a : ι → glTotallyPositive F)
    (hcover : doubleCoset (D.out : GL (Fin 2) F) (Γ : Set (GL (Fin 2) F)) Γ =
      ⋃ i, MulOpposite.op (a i : GL (Fin 2) F) • (Γ : Set (GL (Fin 2) F)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i : GL (Fin 2) F) •
      (Γ : Set (GL (Fin 2) F)))
    (φ : slashInvariants k Γ) :
    (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) =
      ∑ i, slash k (a i) φ := by
  rcases exists_bijective_rightCosetRep_smul_eq D (fun i ↦ (a i : GL (Fin 2) F)) hcover hinj with
    ⟨e, he, h⟩
  exact (Fintype.sum_bijective e he _ _ fun i ↦
    slash_eq_of_mul_inv_mem φ.2 (isTotallyPositive_det (a i))
      ((rightCoset_eq_iff _).mp (h i))).symm

/-- **The Hecke operators preserve holomorphy** when the slash operators of `GL₂⁺(F)` do. -/
lemma isHolomorphic_heckeOperator
    (hk : ∀ (g : GL (Fin 2) F) f, IsHolomorphic f → IsHolomorphic (slash k g f))
    {φ : slashInvariants k Γ}
    (hφ : IsHolomorphic (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    IsHolomorphic (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ha hb ↦ ha.add hb) (differentiableOn_const 0)
    fun v _ ↦ hk _ _ hφ

/-- The action of the Hecke ring of a Hecke pair `(Γ, GL₂⁺(F))`, such as that of `Γ₀(𝔑)_𝔟`
(`HilbertModularGroup.hilbertHeckeRing`), on the functions satisfying the transformation law of
weight `k` for `Γ`: the linear extension of `f ↦ f ∣ₖ ΓαΓ`. -/
noncomputable def heckeAlgebraAction :
    HeckeRing (glTotallyPositive F) Γ ℂ →ₗ[ℂ] Module.End ℂ (slashInvariants k Γ) :=
  Finsupp.linearCombination ℂ (heckeOperator k Γ)

end HilbertModularForm

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {𝔑 : Ideal (𝓞 F)}
  {k : {w : InfinitePlace F // w.IsReal} → ℤ} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (f : HilbertModularForm 𝔑 k 𝔟 h𝔟)

instance (u : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : NeZero (u : FractionalIdeal (𝓞 F)⁰ F) :=
  ⟨u.ne_zero⟩

lemma toFun_mem_slashInvariants (c : NarrowClassGroup F) : f.toFun c ∈
    slashInvariants k (gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c : _)) 𝔑) :=
  (mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mpr (f.smul_eq c)

variable [NeZero 𝔑]

/-- The **Hecke operator `T_𝔭`** applied to the component `f_c` of a Hilbert modular form, for a
prime `𝔭 = (π)` with `π` totally positive: `f_c ∣ₖ Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟 = ∑ᵢ f_c ∣ₖ αᵢ`,
with `𝔟 = 𝔟_c` and `Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟 = ⊔ᵢ Γ₀(𝔑)_𝔟 αᵢ`. As `𝔭` is trivial in the
narrow class group, `𝔟𝔭⁻¹` and `𝔟` are in the same narrow class, so `T_𝔭` maps each component to
itself; the general case, where `T_𝔭` permutes the components by `𝔟 ↦ 𝔟𝔭⁻¹`, is not covered. -/
noncomputable def heckeTComponent (c : NarrowClassGroup F) (π : Fˣ)
    (hπ : IsTotallyPositive (π : F)) : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ :=
  heckeOperator k _ (heckeT (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) 𝔑 π hπ)
    ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩

/-- **The Hecke operator `T_𝔭` preserves the transformation law**: `T_𝔭 f_c` satisfies
`(T_𝔭 f_c)(γ z) = automorphyFactor k γ z · (T_𝔭 f_c)(z)` for every `γ ∈ Γ₀(𝔑)_{𝔟_c}`. -/
lemma heckeTComponent_smul_eq (c : NarrowClassGroup F) (π : Fˣ) (hπ : IsTotallyPositive (π : F))
    {γ : GL (Fin 2) F} (hγ : γ ∈ gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c : _)) 𝔑)
    (z : {w : InfinitePlace F // w.IsReal} → ℍ) :
    f.heckeTComponent c π hπ (smul γ z) = automorphyFactor k γ z * f.heckeTComponent c π hπ z :=
  (mem_slashInvariants_iff fun _ ↦ isTotallyPositive_det_of_mem_gammaZero).mp
    (heckeOperator k _ (heckeT (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) 𝔑 π hπ)
      ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩).2 γ hγ z

/-- A Hilbert modular form `f` is a **Hecke eigenform** if it is nonzero and, for every prime
`𝔭 ∤ 𝔑` generated by a totally positive `π`, it is an eigenvector of `T_𝔭`: there is `a_𝔭 ∈ ℂ`
with `T_𝔭 f_c = a_𝔭 f_c` for every component `c`, the same eigenvalue on all components. Only the
primes trivial in the narrow class group are covered, for which `T_𝔭` preserves each component. -/
def IsHeckeEigenform : Prop :=
  f.toFun ≠ 0 ∧ ∀ (π : Fˣ) (hπ : IsTotallyPositive (π : F)) (p : 𝓞 F), algebraMap (𝓞 F) F p = π →
    (Ideal.span {p}).IsPrime → ¬𝔑 ≤ Ideal.span {p} →
      ∃ a : ℂ, ∀ c, f.heckeTComponent c π hπ = a • f.toFun c

open scoped Classical in
/-- The Hilbert modular form of weight `0` whose component at the narrow class `c₀` is the
constant `1` and whose other components vanish. -/
noncomputable def indicatorOne (c₀ : NarrowClassGroup F) : HilbertModularForm 𝔑 0 𝔟 h𝔟 where
  toFun c _ := if c = c₀ then 1 else 0
  isHolomorphic _ := differentiableOn_const _
  isBoundedAtCusps _ α _ := by
    rw [slash_zero_const]
    exact Filter.const_boundedAtFilter _ _
  smul_eq _ γ _ z := by
    rw [automorphyFactor_zero, one_mul]

attribute [local instance] Fintype.ofFinite in
lemma heckeTComponent_indicatorOne (c₀ c : NarrowClassGroup F) (π : Fˣ)
    (hπ : IsTotallyPositive (π : F)) :
    (indicatorOne c₀ : HilbertModularForm 𝔑 0 𝔟 h𝔟).heckeTComponent c π hπ =
      (Nat.card (DecompQuotient (gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c : _)) 𝔑)
        (gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c : _)) 𝔑)
        ((heckeT (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) 𝔑 π hπ).out : GL (Fin 2) F)⁻¹) : ℂ) •
        (indicatorOne c₀ : HilbertModularForm 𝔑 0 𝔟 h𝔟).toFun c := by
  rw [heckeTComponent, coe_heckeOperator]
  simp only [indicatorOne, slash_zero_const]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

/-- **Hecke eigenforms exist**: the form of weight `0` that is `1` on one component and `0` on the
others is a Hecke eigenform, with eigenvalue the number of right cosets in `T_𝔭`; so
`IsHeckeEigenform` is not vacuous. -/
lemma isHeckeEigenform_indicatorOne (c₀ : NarrowClassGroup F) :
    (indicatorOne c₀ : HilbertModularForm 𝔑 0 𝔟 h𝔟).IsHeckeEigenform := by
  refine ⟨fun h ↦ ?_, fun π hπ _ _ _ _ ↦ ⟨Nat.card (DecompQuotient
    (gammaZero (𝔟 c₀ : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c₀ : _)) 𝔑)
    (gammaZero (𝔟 c₀ : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c₀ : _)) 𝔑)
    ((heckeT (𝔟 c₀ : FractionalIdeal (𝓞 F)⁰ F) 𝔑 π hπ).out : GL (Fin 2) F)⁻¹), fun c ↦ ?_⟩⟩
  · simpa [indicatorOne] using congrFun (congrFun h c₀) fun _ ↦ I
  · rw [heckeTComponent_indicatorOne c₀ c π hπ]
    rcases eq_or_ne c c₀ with rfl | hc
    · rfl
    · simp only [indicatorOne, ite_eq_right hc]
      rw [← Pi.zero_def, smul_zero, smul_zero]

end HilbertModularForm
