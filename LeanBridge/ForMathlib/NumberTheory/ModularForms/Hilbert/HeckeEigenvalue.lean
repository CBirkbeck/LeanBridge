import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeOperator

/-!
# Hecke eigenvalues and Hecke orbits of Hilbert modular forms

For a prime `𝔭 = (π)` of `𝒪_F` not dividing the level `𝔑`, with `π` totally positive, the Hecke
operator `T_𝔭` acts on each component of a Hilbert modular form (LMFDB `mf.hilbert`). A Hecke
eigenform `f` satisfies `T_𝔭 f = a_𝔭 f` for a unique `a_𝔭 ∈ ℂ`, its Hecke eigenvalue
(LMFDB `mf.hilbert.eigenvalue`). The Hecke orbit of `f` (LMFDB `mf.hilbert.hecke_orbit`) is the
subspace spanned by the images of `f` under the products of these `T_𝔭`; for an eigenform it is the
line `ℂ f`.

Only the primes that are trivial in the narrow class group are covered, for which `T_𝔭` maps each
component to itself: the general `T_𝔭`, which permutes the components by `𝔟 ↦ 𝔟𝔭⁻¹`, and the
operators `T_𝔫` for composite `𝔫` are not formalised, nor is the normalisation `a_(1) = 1`, which
needs Fourier expansions. The Hecke orbit is defined as a subspace of the tuples of functions on
`ℍⁿ`; it lies in the space of Hilbert modular forms by `heckeOrbit_le_space` in
`Hilbert/HeckeSpace.lean`.

## Main definitions

* `HilbertModularForm.IsHeckePrimeGenerator`: totally positive generators of primes `𝔭 ∤ 𝔑`.
* `HilbertModularForm.HasHeckeEigenvalue`: `T_𝔭 f = a f` on every component.
* `HilbertModularForm.heckeEigenvalue` (LMFDB `mf.hilbert.eigenvalue`): the Hecke eigenvalue `a_𝔭`.
* `HilbertModularForm.heckeTEnd`: `T_𝔭` as an endomorphism of the functions of a component.
* `HilbertModularForm.heckeOrbit` (LMFDB `mf.hilbert.hecke_orbit`): the Hecke orbit.

## Main results

* `HilbertModularForm.HasHeckeEigenvalue.eq`: the Hecke eigenvalue of a nonzero form is unique.
* `HilbertModularForm.heckeOrbit_eq_span`: the Hecke orbit of an eigenform is `ℂ f`.
-/

open NumberField UpperHalfPlane HilbertModularGroup

open scoped nonZeroDivisors

namespace HilbertModularForm

variable {F : Type*} [Field F] [NumberField F] {𝔑 : Ideal (𝓞 F)} [NeZero 𝔑]
  {k : {w : InfinitePlace F // w.IsReal} → ℤ} {𝔟 : NarrowClassGroup F → (FractionalIdeal (𝓞 F)⁰ F)ˣ}
  {h𝔟 : ∀ c, NarrowClassGroup.mk (𝔟 c) = c} (f : HilbertModularForm 𝔑 k 𝔟 h𝔟) {π : Fˣ}

variable (𝔑) in
/-- `π ∈ Fˣ` is a **totally positive generator of a prime `𝔭 ∤ 𝔑`**: `π` is totally positive and
`π = p` for some `p ∈ 𝒪_F` generating a prime ideal that does not divide `𝔑`. -/
def IsHeckePrimeGenerator (π : Fˣ) : Prop :=
  IsTotallyPositive (π : F) ∧ ∃ p : 𝓞 F, algebraMap (𝓞 F) F p = π ∧ (Ideal.span {p}).IsPrime ∧
    ¬𝔑 ≤ Ideal.span {p}

/-- `f` **has Hecke eigenvalue** `a` for `T_𝔭`, `𝔭 = (π)` with `π` totally positive:
`T_𝔭 f_c = a f_c` for every component `c`. -/
def HasHeckeEigenvalue (hπ : IsTotallyPositive (π : F)) (a : ℂ) : Prop :=
  ∀ c, f.heckeTComponent c π hπ = a • f.toFun c

variable {f} in
/-- **The Hecke eigenvalue of a nonzero form is unique.** -/
lemma HasHeckeEigenvalue.eq (hf : f.toFun ≠ 0) {hπ : IsTotallyPositive (π : F)} {a b : ℂ}
    (ha : f.HasHeckeEigenvalue hπ a) (hb : f.HasHeckeEigenvalue hπ b) : a = b := by
  rcases Function.ne_iff.mp hf with ⟨c, hc⟩
  exact smul_left_injective ℂ hc <| (ha c).symm.trans (hb c)

/-- The **Hecke eigenvalue** `a_𝔭` (LMFDB `mf.hilbert.eigenvalue`) of a Hecke eigenform `f` at a
prime `𝔭 = (π) ∤ 𝔑` with `π` totally positive: the unique `a_𝔭 ∈ ℂ` with `T_𝔭 f = a_𝔭 f`
(`HasHeckeEigenvalue.eq`). The LMFDB defines `a_𝔫` for every ideal `𝔫`, with `f` normalised by
`a_(1) = 1`; only primes trivial in the narrow class group are covered here, and since `a_𝔭` is an
eigenvalue, it does not depend on the normalisation of `f`. -/
noncomputable def heckeEigenvalue (hf : f.IsHeckeEigenform) (hπ : IsHeckePrimeGenerator 𝔑 π) : ℂ :=
  (hf.2 π hπ.1 hπ.2.choose hπ.2.choose_spec.1 hπ.2.choose_spec.2.1 hπ.2.choose_spec.2.2).choose

lemma hasHeckeEigenvalue_heckeEigenvalue (hf : f.IsHeckeEigenform)
    (hπ : IsHeckePrimeGenerator 𝔑 π) : f.HasHeckeEigenvalue hπ.1 (f.heckeEigenvalue hf hπ) :=
  (hf.2 π hπ.1 hπ.2.choose hπ.2.choose_spec.1 hπ.2.choose_spec.2.1 hπ.2.choose_spec.2.2).choose_spec

variable (k 𝔟) in
/-- The Hecke operator `T_𝔭`, `𝔭 = (π)` with `π` totally positive, as an endomorphism of the
functions satisfying the transformation law of weight `k` for `Γ₀(𝔑)_{𝔟_c}`. -/
noncomputable def heckeTEnd (c : NarrowClassGroup F) (π : Fˣ) (hπ : IsTotallyPositive (π : F)) :
    Module.End ℂ (slashInvariants k (gammaZero (𝔟 c : FractionalIdeal (𝓞 F)⁰ F)
      (glPlus (𝔟 c : FractionalIdeal (𝓞 F)⁰ F)) 𝔑)) :=
  heckeOperator k _ (heckeT (𝔟 c : FractionalIdeal (𝓞 F)⁰ F) 𝔑 π hπ)

/-- The **Hecke orbit** (LMFDB `mf.hilbert.hecke_orbit`) of a Hilbert modular form `f`: the subspace
spanned by the images `(T_{𝔭₁} ⋯ T_{𝔭ᵣ} f_c)_c` of `f` under the products of the Hecke operators
`T_𝔭` for primes `𝔭 = (π) ∤ 𝔑` with `π` totally positive, which generate the algebra of these
Hecke operators coprime to the level. Only the primes trivial in the narrow class group are covered,
and the orbit is a subspace of the tuples of functions on `ℍⁿ`. -/
noncomputable def heckeOrbit :
    Submodule ℂ (NarrowClassGroup F → ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ) :=
  Submodule.span ℂ <| Set.range fun l : List {π : Fˣ // IsHeckePrimeGenerator 𝔑 π} ↦ fun c ↦
    ((l.map fun π ↦ heckeTEnd k 𝔟 c π.1 π.2.1).prod ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩ :
      ({w : InfinitePlace F // w.IsReal} → ℍ) → ℂ)

lemma toFun_mem_heckeOrbit : f.toFun ∈ f.heckeOrbit :=
  Submodule.subset_span ⟨[], rfl⟩

lemma prod_heckeTEnd_apply (hf : f.IsHeckeEigenform)
    (l : List {π : Fˣ // IsHeckePrimeGenerator 𝔑 π}) (c : NarrowClassGroup F) :
    (l.map fun π ↦ heckeTEnd k 𝔟 c π.1 π.2.1).prod ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩ =
      (l.map fun π ↦ f.heckeEigenvalue hf π.2).prod •
        ⟨f.toFun c, f.toFun_mem_slashInvariants c⟩ := by
  induction l with
  | nil => simp
  | cons π l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, List.map_cons,
      List.prod_cons, mul_comm, mul_smul]
    exact congrArg _ <| Subtype.ext <| f.hasHeckeEigenvalue_heckeEigenvalue hf π.2 c

/-- **The Hecke orbit of a Hecke eigenform `f` is the line `ℂ f`.** -/
lemma heckeOrbit_eq_span (hf : f.IsHeckeEigenform) : f.heckeOrbit = ℂ ∙ f.toFun := by
  refine le_antisymm (Submodule.span_le.mpr ?_) <|
    (Submodule.span_singleton_le_iff_mem _ _).mpr f.toFun_mem_heckeOrbit
  rintro _ ⟨l, rfl⟩
  exact Submodule.mem_span_singleton.mpr ⟨(l.map fun π ↦ f.heckeEigenvalue hf π.2).prod,
    funext fun c ↦ (congrArg Subtype.val <| f.prod_heckeTEnd_apply hf l c).symm⟩

end HilbertModularForm
