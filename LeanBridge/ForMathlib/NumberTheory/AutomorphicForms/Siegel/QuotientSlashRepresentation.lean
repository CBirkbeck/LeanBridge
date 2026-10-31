import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CongruenceSubgroups
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwo

/-!
# The representation of `Sp(2g, ℤ)/Γ` on `Γ`-invariant functions

For a normal subgroup `Γ` of `Sp(2g, ℤ)`, such as the principal congruence subgroup `Γ(N)`, the
slash operator of `g ∈ Sp(2g, ℤ)` preserves the functions `f : ℋ_g → V` with `f ∣_ρ γ = f` for
all `γ ∈ Γ`, since `f ∣ gγ = f ∣ (gγg⁻¹)g`; so `g ↦ (f ↦ f ∣_ρ g⁻¹)` is a representation of
`Sp(2g, ℤ)` on them in which `Γ` acts trivially, a representation of `Sp(2g, ℤ)/Γ`. The Siegel
modular forms on `Γ` are such functions. For `Γ = Γ[2]` in degree 2 this is the action of
`Sp(4, ℤ)/Γ[2]`, a group isomorphic to `S₆`, on `M_{k,j}(Γ[2])` of the knowl
`mf.siegel.family.gamma_2`; the isomorphism with `S₆`, the preservation of holomorphy by the slash
operator and the isotypic decomposition are not formalised.

## Main definitions

* The instance `(SymplecticGroup.Gamma l N).Normal`: `Γ(N)` is normal in `Sp(2g, ℤ)`, as a kernel.
* `SiegelUpperHalfSpace.intSlashInvariants`: the functions invariant under a subgroup of
  `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.intSlashRep`: the representation `g ↦ (f ↦ f ∣_ρ g⁻¹)` of `Sp(2g, ℤ)` on
  the functions invariant under a normal subgroup.
* `SiegelUpperHalfSpace.quotientSlashRep`: the induced representation of `Sp(2g, ℤ)/Γ`.
* `SiegelUpperHalfSpace.levelTwoSlashRep` (LMFDB `mf.siegel.family.gamma_2`): the representation
  of `Sp(4, ℤ)/Γ[2]` on the `Γ[2]`-invariant functions of weight `ρ_{k,j}`.

## Main results

* `SiegelUpperHalfSpace.mem_intSlashInvariants_of_mem_modularForms`: the Siegel modular forms on
  a subgroup `Γ` of `Sp(2g, ℤ)` are invariant under the slash operator of `Γ`.
-/

open Matrix hiding mul_inv_rev

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL l ℂ) V) (Γ : Subgroup (symplecticGroup l ℤ))

instance (N : ℕ) : (SymplecticGroup.Gamma l N).Normal :=
  MonoidHom.normal_ker _

/-- The space of functions `f : ℋ_g → V` invariant under the slash operator of weight `ρ` of a
subgroup `Γ` of `Sp(2g, ℤ)`: `f ∣_ρ γ = f` for every `γ ∈ Γ`. -/
def intSlashInvariants : Submodule ℂ (SiegelUpperHalfSpace l → V) where
  carrier := {f | ∀ γ ∈ Γ, slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) γ) f = f}
  add_mem' {f g} hf hg γ hγ := by
    rw [slash_add, hf γ hγ, hg γ hγ]
  zero_mem' γ _ :=
    slash_zero ρ _
  smul_mem' c f hf γ hγ := by
    rw [slash_smul, hf γ hγ]

variable {ρ Γ} in
lemma slash_mem_intSlashInvariants [Γ.Normal] {f : SiegelUpperHalfSpace l → V}
    (hf : f ∈ intSlashInvariants ρ Γ) (g : symplecticGroup l ℤ) :
    slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g) f ∈ intSlashInvariants ρ Γ := fun γ hγ ↦ by
  have h : g * γ = g * γ * g⁻¹ * g := by group
  rw [← slash_mul, ← map_mul, h, map_mul, slash_mul, hf _ (‹Γ.Normal›.conj_mem γ hγ g)]

/-- The action `f ↦ f ∣_ρ g⁻¹` of `Sp(2g, ℤ)` on the functions invariant under a normal subgroup
`Γ`, a representation since the slash operator is a right action. -/
noncomputable def intSlashRep [Γ.Normal] :
    Representation ℂ (symplecticGroup l ℤ) (intSlashInvariants ρ Γ) where
  toFun g :=
    { toFun f := ⟨slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g⁻¹) f,
        slash_mem_intSlashInvariants f.2 g⁻¹⟩
      map_add' f f' := Subtype.ext <| slash_add ρ _ f f'
      map_smul' c f := Subtype.ext <| slash_smul ρ _ f c }
  map_one' := LinearMap.ext fun f ↦ Subtype.ext <| by
    simp only [inv_one, map_one]
    exact slash_one ρ f
  map_mul' g h := LinearMap.ext fun f ↦ Subtype.ext <| by
    simp only [mul_inv_rev, map_mul]
    exact slash_mul ρ _ _ f

lemma intSlashRep_apply [Γ.Normal] (g : symplecticGroup l ℤ) (f : intSlashInvariants ρ Γ) :
    (intSlashRep ρ Γ g f : SiegelUpperHalfSpace l → V) =
      slash ρ (SymplecticGroup.map (Int.castRingHom ℝ) g⁻¹) f :=
  rfl

/-- The **representation of `Sp(2g, ℤ)/Γ`** on the functions `f : ℋ_g → V` invariant under the
slash operator of a normal subgroup `Γ` of `Sp(2g, ℤ)`, by `f ↦ f ∣_ρ g⁻¹`, in which `Γ` acts
trivially. -/
noncomputable def quotientSlashRep [Γ.Normal] :
    Representation ℂ (symplecticGroup l ℤ ⧸ Γ) (intSlashInvariants ρ Γ) :=
  QuotientGroup.lift Γ (intSlashRep ρ Γ) fun γ hγ ↦ LinearMap.ext fun f ↦ Subtype.ext <|
    f.2 γ⁻¹ (Γ.inv_mem hγ)

lemma quotientSlashRep_mk [Γ.Normal] (g : symplecticGroup l ℤ) :
    quotientSlashRep ρ Γ g = intSlashRep ρ Γ g :=
  rfl

/-- **The Siegel modular forms on a subgroup `Γ` of `Sp(2g, ℤ)` are invariant under the slash
operator of `Γ`.** -/
lemma mem_intSlashInvariants_of_mem_modularForms {f : SiegelUpperHalfSpace l → V}
    (hf : f ∈ modularForms ρ (Γ.map (SymplecticGroup.map (Int.castRingHom ℚ))) 1) :
    f ∈ intSlashInvariants ρ Γ := fun γ hγ ↦ by
  have h : slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ)
      (SymplecticGroup.map (Int.castRingHom ℚ) γ)) f = (1 : ℂˣ) • f :=
    ((mem_modularForms_iff_slash ρ f _ 1).mp hf).2 ⟨SymplecticGroup.map (Int.castRingHom ℚ) γ,
      γ, hγ, rfl⟩
  have e : SymplecticGroup.map (algebraMap ℚ ℝ) (SymplecticGroup.map (Int.castRingHom ℚ) γ) =
      SymplecticGroup.map (Int.castRingHom ℝ) γ :=
    Subtype.ext <| by
      ext i j
      simp
  simpa [e] using h

/-- The **representation of `Sp(4, ℤ)/Γ[2]`** on the functions `f : ℋ₂ → Sym^j(ℂ²)` invariant
under the slash operator of weight `ρ_{k,j}` of the principal congruence subgroup `Γ[2]` (LMFDB
`mf.siegel.family.gamma_2`), which contain `M_{k,j}(Γ[2])`
(`mem_intSlashInvariants_of_mem_modularForms`). The knowl identifies `Sp(4, ℤ)/Γ[2]` with `S₆`,
which is not formalised. -/
noncomputable abbrev levelTwoSlashRep (k : ℤ) (j : ℕ) :
    Representation ℂ (symplecticGroup (Fin 2) ℤ ⧸ SymplecticGroup.Gamma (Fin 2) 2)
      (intSlashInvariants (rhoKJ k j) (SymplecticGroup.Gamma (Fin 2) 2)) :=
  quotientSlashRep (rhoKJ k j) (SymplecticGroup.Gamma (Fin 2) 2)

end SiegelUpperHalfSpace
