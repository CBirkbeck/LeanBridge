import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoVectorRepresentation
import TauCeti.RepresentationTheory.Symmetric.Specht.Complex

/-!
# The isotypic multiplicities of the vector-valued Siegel modular forms of level 2

The knowl `mf.siegel.family.gamma_2` decomposes the representation of `S₆ ≅ Sp(4, ℤ)/Γ[2]` on
`M_{k,j}(Γ[2])` into isotypic components `m_{s[λ]} s[λ]`, one for each irreducible representation
`s[λ]` of `S₆`, indexed by the partitions `λ` of 6, and likewise for `S_{k,j}(Γ[2])` (multiplicities
`l_{s[λ]}`) and for the Eisenstein part `E_{k,j}(Γ[2])` (multiplicities `n_{s[λ]}`), and the
representation of `S₃ ≅ Γ₀[2]/Γ₁[2]` on `M_{k,j}(Γ₁[2])`. Here `s[λ]` is the complex Specht module
`TauCeti.spechtModuleℂ λ` of Tau Ceti, which runs through the irreducible complex representations of
the symmetric group exactly once, and the multiplicity of `s[λ]` in a representation `V` is
`dim Hom_{S₆}(s[λ], V)`, the number of copies of `s[λ]` in `V` when `V` is finite-dimensional
(Schur's lemma, `ℂ[S₆]` being semisimple).

Deviations from the knowl. That `M_{k,j}(Γ[2])` is finite-dimensional is not proved here; the
multiplicities are `Module.finrank`s, so they are the knowl's numbers as soon as the intertwiner
spaces are finite-dimensional, which holds when `M_{k,j}(Γ[2])` is. The Eisenstein space
`E_{k,j}(Γ[2])` is not defined in LeanBridge; its multiplicities are taken in the quotient
`M_{k,j}(Γ[2]) / S_{k,j}(Γ[2])`, which is `E_{k,j}(Γ[2])` by the knowl's splitting
`M_{k,j}(Γ[2]) = S_{k,j}(Γ[2]) ⊕ E_{k,j}(Γ[2])` (not proved here). The labels `s[λ]` do not
depend on the numbering of the six odd theta characteristics (an inner automorphism of `S₆`), but
they depend on the action on the odd characteristics among the two classes of isomorphisms
`Sp(4, ℤ/2ℤ) ≅ S₆`, which differ by the outer automorphism of `S₆`; the one used has not been
checked formally against the knowl's `M₂(Γ[2]) = s[2³]`, which needs `dim M₂(Γ[2]) = 5` (Igusa).
By hand it agrees: the translation `Ω ↦ Ω + diag(1, 0)` is a transvection, hence a transposition,
and has trace `-1` on the span of `x₁, …, x₅`, the value on a transposition of the character of
`s[2³]` and of no other irreducible representation of dimension 5.

## Main definitions

* `SiegelUpperHalfSpace.levelTwoCuspSubrep`: `S_{k,j}(Γ[2])` as a subrepresentation of
  `M_{k,j}(Γ[2])` under `S₆`.
* `SiegelUpperHalfSpace.levelTwoMultiplicity`: the multiplicity `m_{s[λ]}` of `s[λ]` in
  `M_{k,j}(Γ[2])`.
* `SiegelUpperHalfSpace.levelTwoCuspMultiplicity`: the multiplicity `l_{s[λ]}` of `s[λ]` in
  `S_{k,j}(Γ[2])`.
* `SiegelUpperHalfSpace.levelTwoEisensteinMultiplicity`: the multiplicity `n_{s[λ]}` of `s[λ]` in
  `M_{k,j}(Γ[2]) / S_{k,j}(Γ[2])`.
* `SiegelUpperHalfSpace.gammaOneMultiplicity`: the multiplicity of the irreducible representation
  `s[λ]` of `S₃` in `M_{k,j}(Γ₁[2])`.

## Main results

* `SiegelUpperHalfSpace.map_invariants_levelTwoVectorSymmetricRep`: the `S₆`-invariants of
  `M_{k,j}(Γ[2])`, its trivial isotypic part `s[6]`, are `M_{k,j}(Sp(4, ℤ))`.
* `SiegelUpperHalfSpace.map_invariants_gammaOneVectorSymmetricRep`: the `S₃`-invariants of
  `M_{k,j}(Γ₁[2])` are `M_{k,j}(Γ₀[2])`, so that `dim M_{k,j}(Γ₀[2])` is the dimension of the
  trivial isotypic part `s[3]` of `M_{k,j}(Γ₁[2])`, as the knowl says.
-/

open Module SymplecticGroup

namespace SiegelUpperHalfSpace

variable (k : ℤ) (j : ℕ) (μ : Nat.Partition 6)

/-- **`S_{k,j}(Γ[2])` as a subrepresentation of `M_{k,j}(Γ[2])`** (LMFDB
`mf.siegel.family.gamma_2`) under `S₆ ≅ Sp(4, ℤ)/Γ[2]`: the modular forms on `Γ[2]` that are cusp
forms, a subspace stable under the action of `S₆`. -/
noncomputable def levelTwoCuspSubrep : Subrepresentation (levelTwoVectorSymmetricRep k j) where
  toSubmodule := (cuspFormsKJ k j IgusaLevelTwo.principal).comap
    (modularFormsKJ k j IgusaLevelTwo.principal).subtype
  apply_mem_toSubmodule σ _ hF := levelTwoVectorSymmetricRep_mem_cuspFormsKJ k σ hF

/-- The **multiplicity `m_{s[λ]}` of the irreducible representation `s[λ]` of `S₆` in
`M_{k,j}(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`): the dimension of the space of
`S₆`-equivariant maps from the complex Specht module `s[λ]` to `M_{k,j}(Γ[2])`, for the action of
`S₆ ≅ Sp(4, ℤ)/Γ[2]` through the six odd theta characteristics. -/
noncomputable def levelTwoMultiplicity : ℕ :=
  finrank ℂ (Representation.IntertwiningMap (TauCeti.spechtModuleℂ μ).ρ
    (levelTwoVectorSymmetricRep k j))

/-- The **multiplicity `l_{s[λ]}` of the irreducible representation `s[λ]` of `S₆` in
`S_{k,j}(Γ[2])`** (LMFDB `mf.siegel.family.gamma_2`): the dimension of the space of
`S₆`-equivariant maps from the complex Specht module `s[λ]` to `S_{k,j}(Γ[2])`. -/
noncomputable def levelTwoCuspMultiplicity : ℕ :=
  finrank ℂ (Representation.IntertwiningMap (TauCeti.spechtModuleℂ μ).ρ
    (levelTwoCuspSubrep k j).toRepresentation)

/-- The **multiplicity `n_{s[λ]}` of the irreducible representation `s[λ]` of `S₆` in the
Eisenstein part** (LMFDB `mf.siegel.family.gamma_2`), taken in the quotient
`M_{k,j}(Γ[2]) / S_{k,j}(Γ[2])`, which is the knowl's `E_{k,j}(Γ[2])` by its splitting
`M_{k,j}(Γ[2]) = S_{k,j}(Γ[2]) ⊕ E_{k,j}(Γ[2])` (not proved here). -/
noncomputable def levelTwoEisensteinMultiplicity : ℕ :=
  finrank ℂ (Representation.IntertwiningMap (TauCeti.spechtModuleℂ μ).ρ
    (Subrepresentation.quotient (W := modularFormsKJ k j IgusaLevelTwo.principal)
      (levelTwoCuspSubrep k j)))

/-- The **multiplicity of the irreducible representation `s[λ]` of `S₃` in `M_{k,j}(Γ₁[2])`**
(LMFDB `mf.siegel.family.gamma_2`): the dimension of the space of `S₃`-equivariant maps from the
complex Specht module `s[λ]`, `λ` a partition of 3, to `M_{k,j}(Γ₁[2])`, for the action of
`S₃ ≅ Γ₀[2]/Γ₁[2]` through the three nonzero vectors of `(ℤ/2ℤ)²`. -/
noncomputable def gammaOneMultiplicity (ν : Nat.Partition 3) : ℕ :=
  finrank ℂ (Representation.IntertwiningMap (TauCeti.spechtModuleℂ ν).ρ
    (gammaOneVectorSymmetricRep k j))

private lemma map_invariants_eq_modularFormsKJ {P : Type*} [Group P]
    {H K : Subgroup (Matrix.symplecticGroup (Fin 2) ℤ)}
    (σ : Representation ℂ P (modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))))
    (hHK : H ≤ K) (h₁ : ∀ p, ∃ γ ∈ K, ∀ F,
      (σ p F).1 = slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ⁻¹) F)
    (h₂ : ∀ γ ∈ K, ∃ p, ∀ F,
      (σ p F).1 = slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ⁻¹) F) :
    Submodule.map (modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))).subtype
      (Representation.invariants
        (V := modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ)))) σ) =
      modularFormsKJ k j (K.map (SymplecticGroup.map (Int.castRingHom ℚ))) := by
  ext f
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rcases Submodule.mem_map.mp hf with ⟨F, hF, rfl⟩
    refine mem_modularFormsKJ_of_slash_eq k F.2.1 fun γ hγ ↦ ?_
    rcases h₂ γ⁻¹ (inv_mem hγ) with ⟨p, hp⟩
    have e : slash (rhoKJ k j) (SymplecticGroup.map (Int.castRingHom ℝ) γ⁻¹⁻¹) F = F :=
      (hp F).symm.trans (congrArg Subtype.val ((Representation.mem_invariants _ _).mp hF p))
    rwa [inv_inv] at e
  · have hf' : f ∈ modularFormsKJ k j (H.map (SymplecticGroup.map (Int.castRingHom ℚ))) :=
      mem_modularFormsKJ_of_slash_eq k hf.1 fun δ hδ ↦
        mem_intSlashInvariants_of_mem_modularForms _ _ hf δ (hHK hδ)
    refine Submodule.mem_map.mpr ⟨⟨f, hf'⟩, (Representation.mem_invariants _ _).mpr fun p ↦ ?_, rfl⟩
    rcases h₁ p with ⟨γ, hγ, hp⟩
    exact Subtype.ext <|
      (hp _).trans (mem_intSlashInvariants_of_mem_modularForms _ _ hf _ (inv_mem hγ))

/-- **`M_{k,j}(Sp(4, ℤ))` is the space of `S₆`-invariants of `M_{k,j}(Γ[2])`** (LMFDB
`mf.siegel.family.gamma_2`): a modular form on `Γ[2]` is one on `Sp(4, ℤ)` exactly when it is fixed
by `S₆ ≅ Sp(4, ℤ)/Γ[2]`, so the trivial isotypic part `s[6]` of `M_{k,j}(Γ[2])` is
`M_{k,j}(Sp(4, ℤ))`. -/
lemma map_invariants_levelTwoVectorSymmetricRep : Submodule.map
    (modularFormsKJ k j IgusaLevelTwo.principal).subtype (Representation.invariants
      (V := modularFormsKJ k j IgusaLevelTwo.principal) (levelTwoVectorSymmetricRep k j)) =
    modularFormsKJ k j (integral (Fin 2)) := by
  refine map_invariants_eq_modularFormsKJ k j (levelTwoVectorSymmetricRep k j) le_top (fun p ↦ ?_)
    fun γ _ ↦ ⟨quotientGammaTwoEquivPerm γ, fun F ↦ ?_⟩
  · rcases QuotientGroup.mk_surjective (quotientGammaTwoEquivPerm.symm p) with ⟨x, hx⟩
    refine ⟨x, Subgroup.mem_top x, fun F ↦ ?_⟩
    rw [levelTwoVectorSymmetricRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hx]
    rfl
  · rw [levelTwoVectorSymmetricRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rfl

/-- **`M_{k,j}(Γ₀[2])` is the space of `S₃`-invariants of `M_{k,j}(Γ₁[2])`** (LMFDB
`mf.siegel.family.gamma_2`): a modular form on `Γ₁[2]` is one on `Γ₀[2]` exactly when it is fixed
by `S₃ ≅ Γ₀[2]/Γ₁[2]`, so the trivial isotypic part of `M_{k,j}(Γ₁[2])` is `M_{k,j}(Γ₀[2])`. -/
lemma map_invariants_gammaOneVectorSymmetricRep : Submodule.map
    (modularFormsKJ k j ((Gamma1 (Fin 2) 2).map (SymplecticGroup.map (Int.castRingHom ℚ)))).subtype
    (Representation.invariants (V := modularFormsKJ k j ((Gamma1 (Fin 2) 2).map
      (SymplecticGroup.map (Int.castRingHom ℚ)))) (gammaOneVectorSymmetricRep k j)) =
    modularFormsKJ k j ((Gamma0 (Fin 2) 2).map (SymplecticGroup.map (Int.castRingHom ℚ))) := by
  refine map_invariants_eq_modularFormsKJ k j (gammaOneVectorSymmetricRep k j) (Gamma1_le_Gamma0 2)
    (fun p ↦ ?_) fun γ hγ ↦ ⟨quotientGammaOneGamma0EquivPerm (⟨γ, hγ⟩ : Gamma0 (Fin 2) 2),
      fun F ↦ ?_⟩
  · rcases QuotientGroup.mk_surjective (quotientGammaOneGamma0EquivPerm.symm p) with ⟨x, hx⟩
    refine ⟨x, x.2, fun F ↦ ?_⟩
    rw [gammaOneVectorSymmetricRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hx]
    rfl
  · rw [gammaOneVectorSymmetricRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rfl

end SiegelUpperHalfSpace
