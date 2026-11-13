import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.ModularForm

/-!
# Cusp forms with a multiplier system

A cusp form of weight `k ∈ ℤ` and multiplier system `v : Γ → S¹` on a subgroup `Γ` of `SL(2, ℝ)`
(inside `GL(2, ℝ)`) is a modular form of weight `k` and multiplier `v` that vanishes at every cusp
of `Γ`. These form a complex vector space. For `v = 1` they are Mathlib's cusp forms. A multiplier
on a subgroup `G` of `SL(2, ℤ)` is carried to the image of `G` in `GL(2, ℝ)`, where these spaces
live.

## Main definitions

* `ModularForm.multiplierCuspSpace`: the space of cusp forms of weight `k` and multiplier `v` on
  `Γ`.
* `ModularForm.multiplierMapGL`: a multiplier on `G ≤ SL(2, ℤ)`, as a multiplier on the image of
  `G` in `GL(2, ℝ)`.

## Main results

* `ModularForm.mem_multiplierCuspSpace_one_iff`: for the trivial multiplier, these are Mathlib's
  cusp forms.
-/

open UpperHalfPlane OnePoint Subgroup Matrix SpecialLinearGroup

open scoped ModularForm Manifold MatrixGroups

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {f : ℍ → ℂ}

variable (k) in
/-- The space of **cusp forms** (LMFDB `cmf.cusp_form`, here with a multiplier system) of weight
`k ∈ ℤ` and multiplier system `v` on a subgroup `Γ` of `SL(2, ℝ)`: the modular forms of weight `k`
and multiplier `v` on `Γ` (`ModularForm.multiplierSpace`) that vanish at every cusp of `Γ`, that
is, `f ∣[k] g → 0` as `Im z → ∞` for every `g ∈ GL(2, ℝ)` mapping `∞` to a cusp, as a complex
vector space. For `v = 1` this is Mathlib's `CuspForm Γ k` (`mem_multiplierCuspSpace_one_iff`). -/
def multiplierCuspSpace (v : Γ →* Circle) : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | f ∈ multiplierSpace k v ∧ ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt f k}
  add_mem' hf hg := ⟨add_mem hf.1 hg.1, fun hc ↦ (hf.2 hc).add (hg.2 hc)⟩
  zero_mem' := ⟨zero_mem _, fun _ g _ ↦ by
    rw [SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _⟩
  smul_mem' a f hf := ⟨Submodule.smul_mem _ a hf.1, fun hc g hg ↦ by
    simpa only [IsZeroAtImInfty, smul_slash] using (hf.2 hc g hg).smul (σ g a)⟩

/-- **For the trivial multiplier these are Mathlib's cusp forms**: a function lies in the space of
cusp forms of weight `k` and multiplier `1` on `Γ` exactly when it is a cusp form of weight `k` on
`Γ`. -/
lemma mem_multiplierCuspSpace_one_iff : f ∈ multiplierCuspSpace k (1 : Γ →* Circle) ↔
    ∃ g : CuspForm Γ k, ⇑g = f := by
  refine ⟨fun hf ↦ ⟨⟨⟨f, fun γ hγ ↦ by simpa using hf.1.2.1 ⟨γ, hγ⟩⟩, hf.1.1, hf.2⟩, rfl⟩, ?_⟩
  rintro ⟨g, rfl⟩
  exact ⟨⟨g.holo', fun γ ↦ by simpa using g.slash_action_eq' γ γ.2,
    fun hc h hh ↦ (g.zero_at_cusps' hc h hh).boundedAtFilter⟩, g.zero_at_cusps'⟩

variable {G : Subgroup SL(2, ℤ)} (v : G →* Circle)

/-- A homomorphism `v : G → S¹` on a subgroup `G` of `SL(2, ℤ)`, as a homomorphism on the image of
`G` in `GL(2, ℝ)`, the group on which modular forms with multiplier are defined
(`ModularForm.multiplierSpace`). -/
noncomputable def multiplierMapGL : G.map (mapGL ℝ) →* Circle :=
  v.comp (G.equivMapOfInjective (mapGL ℝ) mapGL_injective).symm.toMonoidHom

lemma multiplierMapGL_apply_mapGL (g : G) :
    multiplierMapGL v ⟨mapGL ℝ (g : SL(2, ℤ)), Subgroup.mem_map_of_mem _ g.2⟩ = v g :=
  congrArg v <| (G.equivMapOfInjective (mapGL ℝ) mapGL_injective).symm_apply_apply g

variable {v} in
lemma slash_eq_smul_of_mem_multiplierCuspSpace (hf : f ∈ multiplierCuspSpace k (multiplierMapGL v))
    (g : G) : f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f :=
  multiplierMapGL_apply_mapGL v g ▸ hf.1.2.1 ⟨_, Subgroup.mem_map_of_mem _ g.2⟩

end ModularForm
