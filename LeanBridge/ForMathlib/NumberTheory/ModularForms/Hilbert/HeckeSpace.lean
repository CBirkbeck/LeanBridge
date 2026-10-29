import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeEigenvalue

/-!
# Hecke operators on the space of Hilbert modular forms

The slash operator `f ↦ f ∣ₖ g` by a matrix `g ∈ GL₂(F)` with totally positive determinant
preserves holomorphy on `ℍⁿ`, since `z ↦ g z` is holomorphic coordinatewise and the automorphy
factor is holomorphic and nowhere zero. It also preserves boundedness and vanishing at the cusps:
for `α ∈ SL₂(F)`, `g α = β diag(1, det g)` with `β ∈ SL₂(F)`, and the slash by `diag(1, d)`, `d`
totally positive, is a constant times `z ↦ f(z / d)`, which keeps all the imaginary parts tending
to infinity. Hence the Hecke operators `T_𝔭`, for primes `𝔭 = (π)` with `π` totally positive, map
Hilbert modular forms (LMFDB `mf.hilbert`) to Hilbert modular forms and cusp forms to cusp forms,
and they are linear endomorphisms of the space of Hilbert modular forms of level `𝔑` and weight `k`.
The Hecke orbit of a Hilbert modular form (LMFDB `mf.hilbert.hecke_orbit`) lies in this space.

## Main definitions

* `HilbertModularForm.space`: the space of Hilbert modular forms of level `𝔑` and weight `k`, as a
  subspace of the tuples of functions on `ℍⁿ`.
* `HilbertModularForm.heckeTForm`: the Hilbert modular form `T_𝔭 f`.
* `HilbertModularForm.heckeTSpace`: `T_𝔭` as a linear endomorphism of the space of Hilbert modular
  forms.

## Main results

* `HilbertModularForm.IsHolomorphic.slash`: the slash operator preserves holomorphy.
* `HilbertModularForm.IsBoundedAtCusps.slash`: the slash operator preserves boundedness at the
  cusps.
* `HilbertModularForm.VanishesAtCusps.slash`: the slash operator preserves vanishing at the cusps.
* `HilbertModularForm.IsCuspForm.heckeTForm`: `T_𝔭` maps cusp forms to cusp forms.
* `HilbertModularForm.heckeOrbit_le_space`: the Hecke orbit lies in the space of Hilbert modular
  forms.
-/

open Filter Matrix NumberField InfinitePlace UpperHalfPlane HilbertModularGroup

open scoped nonZeroDivisors

namespace HilbertModularForm

variable {F : Type*} [Field F] {k : {w : InfinitePlace F // w.IsReal} → ℤ} {g : GL (Fin 2) F}
  {f f' : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ} {π : Fˣ} {hπ : IsTotallyPositive (π : F)}

lemma coe_smul_ofComplex (hg : IsTotallyPositive g.det.val)
    {z : {w : InfinitePlace F // w.IsReal} → ℂ} (hz : ∀ w, 0 < (z w).im)
    (w : {w : InfinitePlace F // w.IsReal}) :
    (smul g (fun w ↦ ofComplex (z w)) w : ℂ) = num (mapGL w g) (z w) / denom (mapGL w g) (z w) := by
  rw [coe_smul_apply _ _ hg, ofComplex_apply_of_im_pos (hz w)]

lemma denom_mapGL_heckeDiagonal (w : {w : InfinitePlace F // w.IsReal}) (τ : ℂ) :
    denom (mapGL w (heckeDiagonal π hπ)) τ = embedding_of_isReal w.2 π := by
  simp only [denom, mapGL]
  simp [heckeDiagonal]

lemma im_smul_heckeDiagonal (z : {w : InfinitePlace F // w.IsReal} → ℍ)
    (w : {w : InfinitePlace F // w.IsReal}) :
    (smul (heckeDiagonal π hπ : GL (Fin 2) F) z w).im = (z w).im / embedding_of_isReal w.2 π := by
  rw [← coe_im, coe_smul_apply _ _ (isTotallyPositive_det _), denom_mapGL_heckeDiagonal]
  simp only [num, mapGL]
  simp [heckeDiagonal]
  rw [← embedding_of_isReal_apply w.2, Complex.div_ofReal_im, coe_im]

lemma tendsto_smul_heckeDiagonal :
    Tendsto (smul (heckeDiagonal π hπ : GL (Fin 2) F)) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr <| tendsto_pi.mpr fun w ↦ ?_
  simp only [Function.comp_apply, im_smul_heckeDiagonal]
  have h : Tendsto (fun (z : {w : InfinitePlace F // w.IsReal} → ℍ) w ↦ (z w).im) atImInfty
      (pi fun _ ↦ atTop) :=
    tendsto_comap
  exact (tendsto_pi.mp h w).atTop_div_const (hπ w.1 w.2)

lemma det_heckeDiagonal : (heckeDiagonal π hπ : GL (Fin 2) F).det = π :=
  Units.ext <| by simp [heckeDiagonal]

lemma det_mul_mul_inv_heckeDiagonal (hg : IsTotallyPositive g.det.val) {α : GL (Fin 2) F}
    (hα : α.det = 1) : (g * α * (heckeDiagonal g.det hg : GL (Fin 2) F)⁻¹).det = 1 := by
  rw [map_mul, map_mul, map_inv, hα, det_heckeDiagonal, mul_one, mul_inv_cancel]

variable [NumberField F]

open scoped Classical in
lemma differentiableOn_denom (w : {w : InfinitePlace F // w.IsReal}) :
    DifferentiableOn ℂ (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦ denom (mapGL w g) (z w))
      {z | ∀ w, 0 < (z w).im} := by
  unfold denom
  fun_prop

open scoped Classical in
/-- **The slash operator by a matrix with totally positive determinant preserves holomorphy.** -/
lemma IsHolomorphic.slash (hg : IsTotallyPositive g.det.val) (hf : IsHolomorphic f) :
    IsHolomorphic (slash k g f) := by
  rw [IsHolomorphic] at hf ⊢
  have hΦ : DifferentiableOn ℂ (fun (z : {w : InfinitePlace F // w.IsReal} → ℂ) w ↦
      num (mapGL w g) (z w) / denom (mapGL w g) (z w)) {z | ∀ w, 0 < (z w).im} := by
    refine differentiableOn_pi.mpr fun w ↦ ?_
    simp only [div_eq_mul_inv]
    have hnum : DifferentiableOn ℂ
        (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦ num (mapGL w g) (z w))
        {z | ∀ w, 0 < (z w).im} := by
      unfold num
      fun_prop
    exact hnum.mul <| (differentiableOn_denom w).fun_inv fun z hz ↦ denom_ne_zero_of_im _ (hz w).ne'
  have hfΦ : DifferentiableOn ℂ (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦
      f (smul g fun w ↦ ofComplex (z w))) {z | ∀ w, 0 < (z w).im} := by
    refine (hf.comp hΦ fun z hz w ↦ ?_).congr fun z hz ↦ ?_
    · rw [← coe_smul_ofComplex hg hz]
      exact UpperHalfPlane.im_pos _
    · simp only [Function.comp_apply, ← coe_smul_ofComplex hg hz, ofComplex_apply]
  have hA : DifferentiableOn ℂ (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦
      automorphyFactor k g fun w ↦ ofComplex (z w)) {z | ∀ w, 0 < (z w).im} := by
    unfold automorphyFactor
    refine (Finset.prod_induction (fun w (z : {w : InfinitePlace F // w.IsReal} → ℂ) ↦
      denom (mapGL w g) (ofComplex (z w) : ℂ) ^ k w *
        ((embedding_of_isReal w.2 g.det.val ^ (-(k w : ℝ) / 2) : ℝ) : ℂ))
      (fun h ↦ DifferentiableOn ℂ h {z | ∀ w, 0 < (z w).im}) (fun _ _ ↦ DifferentiableOn.mul)
      (differentiableOn_const 1) fun w _ ↦ ?_).congr fun z _ ↦ by rw [Finset.prod_apply]
    have h : DifferentiableOn ℂ (fun z : {w : InfinitePlace F // w.IsReal} → ℂ ↦
        denom (mapGL w g) (z w) ^ k w *
          ((embedding_of_isReal w.2 g.det.val ^ (-(k w : ℝ) / 2) : ℝ) : ℂ))
        {z | ∀ w, 0 < (z w).im} :=
      ((differentiableOn_denom w).zpow (.inl fun z hz ↦ denom_ne_zero_of_im _ (hz w).ne')).mul
        (differentiableOn_const _)
    refine h.congr fun z hz ↦ ?_
    rw [ofComplex_apply_of_im_pos (hz w)]
  exact (hA.fun_inv fun z _ ↦ automorphyFactor_ne_zero _ _ _ hg).mul hfΦ

open scoped Classical in
lemma IsHolomorphic.add (hf : IsHolomorphic f) (hf' : IsHolomorphic f') :
    IsHolomorphic (f + f') := by
  rw [IsHolomorphic] at *
  exact hf.add hf'

open scoped Classical in
lemma IsHolomorphic.smul (a : ℂ) (hf : IsHolomorphic f) : IsHolomorphic (a • f) := by
  rw [IsHolomorphic] at *
  exact hf.const_smul a

lemma slash_heckeDiagonal : slash k (heckeDiagonal π hπ) f = fun z ↦
    (automorphyFactor k (heckeDiagonal π hπ) fun _ ↦ I)⁻¹ *
      f (smul (heckeDiagonal π hπ : GL (Fin 2) F) z) := by
  ext z
  simp only [slash, automorphyFactor, denom_mapGL_heckeDiagonal]

lemma slash_slash_eq (hg : IsTotallyPositive g.det.val) {α : GL (Fin 2) F} (hα : α.det = 1) :
    slash k α (slash k g f) = slash k (heckeDiagonal g.det hg)
      (slash k (g * α * (heckeDiagonal g.det hg : GL (Fin 2) F)⁻¹) f) := by
  rw [← slash_mul k g α f hg (by simp [hα]), ← slash_mul k _ _ f
    (by simp [det_mul_mul_inv_heckeDiagonal hg hα]) (isTotallyPositive_det _), inv_mul_cancel_right]

/-- **The slash operator by a matrix with totally positive determinant preserves boundedness at the
cusps**: for `α ∈ SL₂(F)`, `g α = β diag(1, det g)` with `β ∈ SL₂(F)`. -/
lemma IsBoundedAtCusps.slash (hg : IsTotallyPositive g.det.val) (hf : IsBoundedAtCusps k f) :
    IsBoundedAtCusps k (slash k g f) := by
  intro α hα
  rw [slash_slash_eq hg hα, slash_heckeDiagonal]
  exact ((hf _ (det_mul_mul_inv_heckeDiagonal hg hα)).comp_tendsto
    tendsto_smul_heckeDiagonal).const_mul_left _

/-- **The slash operator by a matrix with totally positive determinant preserves vanishing at the
cusps.** -/
lemma VanishesAtCusps.slash (hg : IsTotallyPositive g.det.val) (hf : VanishesAtCusps k f) :
    VanishesAtCusps k (slash k g f) := by
  intro α hα
  rw [slash_slash_eq hg hα, slash_heckeDiagonal]
  simpa using ((hf _ (det_mul_mul_inv_heckeDiagonal hg hα)).comp
    tendsto_smul_heckeDiagonal).const_mul _

lemma isBoundedAtCusps_zero :
    IsBoundedAtCusps k (0 : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  intro α _
  rw [← slashLinearMap_apply, map_zero]
  exact const_boundedAtFilter _ (0 : ℂ)

lemma IsBoundedAtCusps.add (hf : IsBoundedAtCusps k f) (hf' : IsBoundedAtCusps k f') :
    IsBoundedAtCusps k (f + f') := by
  intro α hα
  rw [← slashLinearMap_apply, map_add]
  exact (hf α hα).add (hf' α hα)

lemma IsBoundedAtCusps.smul (a : ℂ) (hf : IsBoundedAtCusps k f) :
    IsBoundedAtCusps k (a • f) := by
  intro α hα
  rw [← slashLinearMap_apply, map_smul]
  exact (hf α hα).smul a

lemma vanishesAtCusps_zero :
    VanishesAtCusps k (0 : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  intro α _
  rw [← slashLinearMap_apply, map_zero]
  exact tendsto_const_nhds

lemma VanishesAtCusps.add (hf : VanishesAtCusps k f) (hf' : VanishesAtCusps k f') :
    VanishesAtCusps k (f + f') := by
  intro α hα
  rw [← slashLinearMap_apply, map_add, ← add_zero 0]
  exact (hf α hα).add (hf' α hα)

variable {Γ : Subgroup (GL (Fin 2) F)} [IsHeckeTriple (glTotallyPositive F) Γ Γ]
  {D : HeckeCoset (glTotallyPositive F) Γ Γ} {φ : slashInvariants k Γ}

lemma IsHolomorphic.hecke (h : IsHolomorphic (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    IsHolomorphic (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeOperator]
  exact Finset.sum_induction (fun v ↦ HilbertModularForm.slash k (heckeRep Γ D v : GL (Fin 2) F) φ)
    IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) (differentiableOn_const 0) fun _ _ ↦
      h.slash (isTotallyPositive_det _)

lemma IsBoundedAtCusps.hecke
    (h : IsBoundedAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    IsBoundedAtCusps k (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeOperator]
  exact Finset.sum_induction (fun v ↦ HilbertModularForm.slash k (heckeRep Γ D v : GL (Fin 2) F) φ)
    (fun f ↦ IsBoundedAtCusps k f) (fun _ _ ↦ IsBoundedAtCusps.add) isBoundedAtCusps_zero fun _ _ ↦
      h.slash (isTotallyPositive_det _)

lemma VanishesAtCusps.hecke
    (h : VanishesAtCusps k (φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) :
    VanishesAtCusps k (heckeOperator k Γ D φ : ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  rw [coe_heckeOperator]
  exact Finset.sum_induction (fun v ↦ HilbertModularForm.slash k (heckeRep Γ D v : GL (Fin 2) F) φ)
    (fun f ↦ VanishesAtCusps k f) (fun _ _ ↦ VanishesAtCusps.add) vanishesAtCusps_zero fun _ _ ↦
      h.slash (isTotallyPositive_det _)

variable {𝔑 : Ideal (𝓞 F)} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (ψ : HilbertModularForm 𝔑 k 𝔟 h𝔟)

variable (𝔑 k 𝔟) in
/-- The **space of Hilbert modular forms** (LMFDB `mf.hilbert`) of weight `k` and level `𝔑`,
relative to the representatives `𝔟`: the subspace of the tuples `(f_c)` of functions on `ℍⁿ`
whose components are holomorphic, bounded at the cusps and satisfy the transformation law of
weight `k` for `Γ₀(𝔑)_{𝔟_c}`; these are the tuples `HilbertModularForm.toFun`. -/
def space : Submodule ℂ (NarrowClassGroup F → ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) where
  carrier := {f | ∀ c, IsHolomorphic (f c) ∧ IsBoundedAtCusps k (f c) ∧
    f c ∈ slashInvariants k (gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) (glPlus (𝔟 c : _)) 𝔑)}
  add_mem' hf hf' c :=
    ⟨(hf c).1.add (hf' c).1, (hf c).2.1.add (hf' c).2.1, add_mem (hf c).2.2 (hf' c).2.2⟩
  zero_mem' _ := ⟨differentiableOn_const 0, isBoundedAtCusps_zero, zero_mem _⟩
  smul_mem' a _ hf c := ⟨(hf c).1.smul a, (hf c).2.1.smul a, Submodule.smul_mem _ a (hf c).2.2⟩

lemma toFun_mem_space : ψ.toFun ∈ space k 𝔑 𝔟 :=
  fun c ↦ ⟨ψ.isHolomorphic c, ψ.isBoundedAtCusps c, ψ.toFun_mem_slashInvariants c⟩

variable [NeZero 𝔑]

variable (π hπ) in
/-- The **Hecke operator `T_𝔭`** applied to a Hilbert modular form `f`, for a prime `𝔭 = (π)` with
`π` totally positive: the Hilbert modular form `(T_𝔭 f_c)_c`. -/
noncomputable def heckeTForm : HilbertModularForm 𝔑 k 𝔟 h𝔟 where
  toFun c := ψ.heckeTComponent c π hπ
  isHolomorphic c := IsHolomorphic.hecke (φ := ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩)
    (ψ.isHolomorphic c)
  isBoundedAtCusps c := IsBoundedAtCusps.hecke (φ := ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩)
    (ψ.isBoundedAtCusps c)
  smul_eq c _ hγ z := ψ.heckeTComponent_smul_eq c π hπ hγ z

variable {ψ} in
/-- **`T_𝔭` maps cusp forms to cusp forms.** -/
lemma IsCuspForm.heckeTForm (h : ψ.IsCuspForm) : (ψ.heckeTForm π hπ).IsCuspForm :=
  fun c ↦ VanishesAtCusps.hecke (φ := ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩) (h c)

variable (π hπ) in
/-- The **Hecke operator `T_𝔭`**, for a prime `𝔭 = (π)` with `π` totally positive, as a linear
endomorphism of the space of Hilbert modular forms of weight `k` and level `𝔑`. -/
noncomputable def heckeTSpace : Module.End ℂ (space k 𝔑 𝔟) where
  toFun f := ⟨fun c ↦ (heckeTEnd k 𝔟 c π hπ ⟨f.1 c, (f.2 c).2.2⟩ :
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ),
    fun c ↦ ⟨(f.2 c).1.hecke, (f.2 c).2.1.hecke, (heckeTEnd k 𝔟 c π hπ _).2⟩⟩
  map_add' f f' := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_add (heckeTEnd k 𝔟 c π hπ) ⟨f.1 c, (f.2 c).2.2⟩ ⟨f'.1 c, (f'.2 c).2.2⟩
  map_smul' a f := Subtype.ext <| funext fun c ↦ congrArg Subtype.val <|
    map_smul (heckeTEnd k 𝔟 c π hπ) a ⟨f.1 c, (f.2 c).2.2⟩

lemma coe_heckeTSpace_toFun :
    (heckeTSpace π hπ ⟨ψ.toFun, ψ.toFun_mem_space⟩ : NarrowClassGroup F →
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) = (ψ.heckeTForm π hπ).toFun :=
  rfl

lemma coe_prod_heckeTSpace (l : List {π : Fˣ // IsHeckePrimeGenerator 𝔑 π})
    (c : NarrowClassGroup F) :
    ((l.map fun π ↦ heckeTSpace π.1 π.2.1).prod ⟨ψ.toFun, ψ.toFun_mem_space⟩ :
      NarrowClassGroup F → ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) c =
      ((l.map fun π ↦ heckeTEnd k 𝔟 c π.1 π.2.1).prod ⟨ψ.toFun c, ψ.toFun_mem_slashInvariants c⟩ :
        ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) := by
  induction l with
  | nil => rfl
  | cons π l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons,
      Module.End.mul_apply]
    exact congrArg (fun φ ↦ (heckeTEnd k 𝔟 c π.1 π.2.1 φ :
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)) (Subtype.ext ih)

/-- **The Hecke orbit of a Hilbert modular form lies in the space of Hilbert modular forms.** -/
lemma heckeOrbit_le_space : ψ.heckeOrbit ≤ space k 𝔑 𝔟 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨l, rfl⟩
  beta_reduce
  rw [← funext (ψ.coe_prod_heckeTSpace l)]
  exact Subtype.prop _

end HilbertModularForm
