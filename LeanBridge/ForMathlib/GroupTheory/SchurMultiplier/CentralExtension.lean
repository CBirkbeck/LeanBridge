import Mathlib.Algebra.Module.CharacterModule
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# The Schur multiplier of the quotient of a central extension

Let `π : C →* G` be a homomorphism whose kernel `N` lies in the centre of `C`, and let `σ : G → C`
be a section of `π`. The factor set `α(g, h) = σ(g) σ(h) σ(gh)⁻¹` takes its values in `N ≤ Z(C)`
and satisfies the cocycle identity, so pairing the inhomogeneous `2`-chains `Σ n_{g,h} [g, h]` of
the trivial representation `ℤ` of `G` with `α` kills the boundaries. This gives a homomorphism
`θ : H₂(G, ℤ) → Z(C)` from Mathlib's `groupHomology (Rep.trivial ℤ G ℤ) 2`, the Schur multiplier
of `G` (LMFDB `group.schur_multiplier`).

The image of `θ` is `N ∩ C'`. It lies in `N`, and in `C'` because the image of a cycle in the
abelianization of `C` is the image of its boundary under `[g] ↦ σ(g) C'`. Conversely, if an element
`z` of `N ∩ C'` were not in the image, a character `χ` of `Z(C)` with values in `ℚ/ℤ` would kill the
image and not `z`. Then `χ ∘ α` vanishes on the `2`-cycles, so it factors through the boundary map
into the `1`-chains, and it extends to the `1`-chains since `ℚ/ℤ` is an injective `ℤ`-module: there
is `b : G → ℚ/ℤ` with `χ(α(g, h)) = b(g) + b(h) - b(gh)`. Then `c ↦ χ(c σ(π c)⁻¹) + b(π c)` is a
homomorphism `C → ℚ/ℤ` that extends `χ` on `N`; it kills `C'`, hence `z`, a contradiction. This is
the part of the five-term exact sequence `H₂(G, ℤ) → N → C^{ab}` that Schur's theory of stem
extensions needs (LMFDB `group.stem_extension`), proved here from the chains alone.

## Main definitions

* `MonoidHom.centralFactorSet`: the factor set `σ(g) σ(h) σ(gh)⁻¹` of a section, in the centre.
* `MonoidHom.H2ToCenter`: the homomorphism `θ : H₂(G, ℤ) → Z(C)`.
* `MonoidHom.H2ToKerInfCommutator`: `θ` as a homomorphism onto `N ∩ C'`.

## Main results

* `MonoidHom.mem_range_H2ToCenter_iff` (LMFDB `group.stem_extension`): the image of `θ` is
  `N ∩ C'`.
* `MonoidHom.surjective_H2ToKerInfCommutator` (LMFDB `group.stem_extension`,
  `group.schur_multiplier`): `N ∩ C'` is a quotient of `H₂(G, ℤ)`.

## References

* I. Schur, *Über die Darstellung der endlichen Gruppen durch gebrochene lineare Substitutionen*,
  J. Reine Angew. Math. 127 (1904), 20–50.
* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982), §II.5.
-/

open Finsupp Subgroup Submodule groupHomology

open scoped IsMulCommutative

namespace MonoidHom

variable {G : Type} [Group G] {C : Type*} [Group C] (π : C →* G) (hπ : π.ker ≤ center C)
  (σ : G → C) (hσ : ∀ g, π (σ g) = g)

/-- The factor set `(g, h) ↦ σ(g) σ(h) σ(gh)⁻¹` of a section `σ` of a homomorphism `π : C →* G`
with central kernel, as a function to the centre of `C`. -/
def centralFactorSet (p : G × G) : center C :=
  ⟨σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹, hπ <| by simp [hσ]⟩

local notation "α" => centralFactorSet π hπ σ hσ

lemma coe_centralFactorSet (p : G × G) : (α p : C) = σ p.1 * σ p.2 * (σ (p.1 * p.2))⁻¹ :=
  rfl

lemma centralFactorSet_mem_ker (p : G × G) : (α p : C) ∈ π.ker := by
  simp [coe_centralFactorSet, hσ]

lemma centralFactorSet_mul_mul (g h j : G) : α (g * h, j) * α (g, h) = α (h, j) * α (g, h * j) := by
  rw [mul_comm (α (g * h, j))]
  refine Subtype.ext ?_
  have hc : Commute (α (h, j) : C) (σ g) := (mem_center_iff.mp (α (h, j)).2 (σ g)).symm
  rw [coe_mul, coe_mul, coe_centralFactorSet π hπ σ hσ (g, h * j), mul_assoc (σ _), hc.left_comm]
  simp only [coe_centralFactorSet]
  group

/-- The pairing of the inhomogeneous `2`-chains of the trivial representation `ℤ` of `G` with the
factor set `centralFactorSet`, `Σ n_{g,h} [g, h] ↦ Σ n_{g,h} α(g, h)`. -/
noncomputable def centralFactorSetChain : (G × G →₀ ℤ) →ₗ[ℤ] Additive (center C) :=
  linearCombination ℤ fun p ↦ .ofMul (α p)

local notation "θ₀" => centralFactorSetChain π hπ σ hσ

lemma centralFactorSetChain_single (p : G × G) (n : ℤ) : θ₀ (single p n) = n • .ofMul (α p) :=
  linearCombination_single ℤ n p

lemma centralFactorSetChain_d₃₂ (x : G × G × G →₀ ℤ) :
    θ₀ ((d₃₂ (Rep.trivial ℤ G ℤ)).hom x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single p n =>
    rcases p with ⟨g, h, j⟩
    have hα : (Additive.ofMul (α (g * h, j)) + .ofMul (α (g, h)) : Additive (center C)) =
        .ofMul (α (h, j)) + .ofMul (α (g, h * j)) := by
      rw [← ofMul_mul, ← ofMul_mul, centralFactorSet_mul_mul]
    simp [d₃₂, centralFactorSetChain_single]
    rw [← smul_sub, ← smul_add, ← smul_sub, sub_add_eq_add_sub, sub_sub, ← hα, sub_self, smul_zero]

lemma ker_H2π_le_ker_centralFactorSetChain_comp : LinearMap.ker (H2π (Rep.trivial ℤ G ℤ)).hom ≤
    LinearMap.ker (θ₀ ∘ₗ (cycles₂ (Rep.trivial ℤ G ℤ)).subtype) := by
  intro z hz
  rcases (H2π_eq_zero_iff z).mp hz with ⟨x, hx⟩
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hx]
  exact centralFactorSetChain_d₃₂ π hπ σ hσ x

/-- The homomorphism `θ : H₂(G, ℤ) → Z(C)` induced by the factor set of a section of a homomorphism
`π : C →* G` with central kernel: the class of a `2`-cycle `Σ n_{g,h} [g, h]` goes to
`Π α(g, h) ^ n_{g,h}`. -/
noncomputable def H2ToCenter : H2 (Rep.trivial ℤ G ℤ) →ₗ[ℤ] Additive (center C) :=
  (LinearMap.ker (H2π (Rep.trivial ℤ G ℤ)).hom).liftQ (θ₀ ∘ₗ (cycles₂ _).subtype)
      (ker_H2π_le_ker_centralFactorSetChain_comp π hπ σ hσ) ∘ₗ
    ((H2π _).hom.quotKerEquivOfSurjective <|
      (ModuleCat.epi_iff_surjective _).mp inferInstance).symm.toLinearMap

local notation "θ" => H2ToCenter π hπ σ hσ

lemma H2ToCenter_H2π (z : cycles₂ (Rep.trivial ℤ G ℤ)) : θ (H2π _ z) = θ₀ z := by
  simp [H2ToCenter]

lemma coe_centralFactorSetChain_mem_ker (x : G × G →₀ ℤ) : ((θ₀ x).toMul : C) ∈ π.ker := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [map_add, toMul_add, coe_mul] using mul_mem hx hy
  | single p n =>
    simpa [centralFactorSetChain_single] using zpow_mem (centralFactorSet_mem_ker π hπ σ hσ p) n

lemma ofMul_of_centralFactorSetChain (x : G × G →₀ ℤ) :
    Additive.ofMul (Abelianization.of ((θ₀ x).toMul : C)) = linearCombination ℤ
      (fun g ↦ Additive.ofMul (Abelianization.of (σ g))) ((d₂₁ (Rep.trivial ℤ G ℤ)).hom x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, toMul_add, coe_mul, map_mul, ofMul_mul, hx, hy]
  | single p n =>
    simp [d₂₁, centralFactorSetChain_single, coe_centralFactorSet]
    abel

lemma coe_centralFactorSetChain_mem_commutator {x : G × G →₀ ℤ}
    (hx : x ∈ cycles₂ (Rep.trivial ℤ G ℤ)) : ((θ₀ x).toMul : C) ∈ commutator C := by
  rw [← Abelianization.ker_of, mem_ker, ← ofMul_eq_zero, ofMul_of_centralFactorSetChain,
    LinearMap.mem_ker.mp hx, map_zero]

lemma exists_H2ToCenter_eq {z : center C} (hz : (z : C) ∈ π.ker ⊓ commutator C) :
    ∃ x, θ x = .ofMul z := by
  by_contra hne
  push Not at hne
  let R : Submodule ℤ (Additive (center C)) := LinearMap.range θ
  have hzR : R.mkQ (.ofMul z) ≠ 0 := by
    rw [Ne, mkQ_apply, Quotient.mk_eq_zero]
    rintro ⟨x, hx⟩
    exact hne x hx
  rcases CharacterModule.exists_character_apply_ne_zero_of_ne_zero hzR with ⟨c, hc⟩
  let χ : Additive (center C) →+ AddCircle (1 : ℚ) := c.comp R.mkQ.toAddMonoidHom
  let d : (G × G →₀ ℤ) →ₗ[ℤ] (G →₀ ℤ) := (d₂₁ (Rep.trivial ℤ G ℤ)).hom
  let f : (G × G →₀ ℤ) →ₗ[ℤ] AddCircle (1 : ℚ) := (χ.comp (θ₀).toAddMonoidHom).toIntLinearMap
  have hf : LinearMap.ker d ≤ LinearMap.ker f := by
    intro y hy
    have hyR : θ₀ y ∈ R := ⟨H2π _ ⟨y, hy⟩, H2ToCenter_H2π π hπ σ hσ ⟨y, hy⟩⟩
    rw [LinearMap.mem_ker]
    exact (congrArg c ((Quotient.mk_eq_zero R).mpr hyR)).trans (map_zero c)
  rcases CharacterModule.dual_surjective_of_injective ((LinearMap.ker d).liftQ d le_rfl)
    (LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker d).liftQ f hf).toAddMonoidHom with ⟨b, hb⟩
  have hbd (x : G × G →₀ ℤ) : b (d x) = χ (θ₀ x) :=
    DFunLike.congr_fun hb ((LinearMap.ker d).mkQ x)
  have hα (g h : G) :
      χ (.ofMul (α (g, h))) = b (single g 1) + b (single h 1) - b (single (g * h) 1) := by
    have hgh : b (d (single (g, h) 1)) = χ (θ₀ (single (g, h) 1)) := hbd (single (g, h) 1)
    simp [d, d₂₁, centralFactorSetChain_single] at hgh
    rw [← hgh]
    abel
  let ν (c : C) : center C := ⟨c * (σ (π c))⁻¹, hπ <| by simp [hσ]⟩
  have hν (c₁ c₂ : C) : ν (c₁ * c₂) = ν c₁ * ν c₂ * α (π c₁, π c₂) := by
    refine Subtype.ext ?_
    have hc : Commute (ν c₂ : C) (σ (π c₁)) := (mem_center_iff.mp (ν c₂).2 _).symm
    rw [coe_mul, coe_mul, coe_centralFactorSet, mul_assoc _ (ν c₂ : C), mul_assoc (σ (π c₁)),
      hc.left_comm]
    simp only [ν, map_mul]
    group
  let ψf (c : C) : Multiplicative (AddCircle (1 : ℚ)) :=
    .ofAdd (χ (.ofMul (ν c)) + b (single (π c) 1))
  have hψf (c₁ c₂ : C) : ψf (c₁ * c₂) = ψf c₁ * ψf c₂ := by
    simp only [ψf, ← ofAdd_add, hν, ofMul_mul, map_add, hα, map_mul]
    congr 1
    abel
  rcases mem_inf.mp hz with ⟨(hz₁ : π z = 1), hz₂⟩
  have hψ : MonoidHom.mk' ψf hψf z = 1 :=
    Abelianization.commutator_subset_ker (MonoidHom.mk' ψf hψf) hz₂
  have h₁ : χ (.ofMul (ν z)) + b (single (π z) 1) = 0 := ofAdd_eq_one.mp hψ
  rw [hz₁] at h₁
  have h₂ : χ (.ofMul (α (1, 1))) = b (single 1 1) := by
    rw [hα, mul_one, add_sub_cancel_right]
  have hνz : ν z * α (1, 1) = z := by
    refine Subtype.ext ?_
    simp only [coe_mul, coe_centralFactorSet, ν, hz₁]
    group
  have h₃ : χ (.ofMul z) = 0 := by
    rw [← hνz, ofMul_mul, map_add, h₂, h₁]
  exact hc h₃

/-- **The image of `θ : H₂(G, ℤ) → Z(C)` is `N ∩ C'`** (LMFDB `group.stem_extension`), for a
homomorphism `π : C →* G` with central kernel `N` and a section `σ` of `π`. -/
lemma mem_range_H2ToCenter_iff (z : Additive (center C)) :
    z ∈ LinearMap.range θ ↔ (z.toMul : C) ∈ π.ker ⊓ commutator C := by
  refine ⟨?_, fun hz ↦ exists_H2ToCenter_eq π hπ σ hσ hz⟩
  rintro ⟨x, rfl⟩
  induction x using H2_induction_on with
  | h y =>
    rw [H2ToCenter_H2π]
    exact mem_inf.mpr ⟨coe_centralFactorSetChain_mem_ker π hπ σ hσ y,
      coe_centralFactorSetChain_mem_commutator π hπ σ hσ y.2⟩

/-- The homomorphism `θ : H₂(G, ℤ) → Z(C)` of `H2ToCenter`, as a homomorphism onto `N ∩ C'`, for a
homomorphism `π : C →* G` with central kernel `N` and a section `σ` of `π`. -/
noncomputable def H2ToKerInfCommutator :
    H2 (Rep.trivial ℤ G ℤ) →+ Additive ↥(π.ker ⊓ commutator C) where
  toFun x := .ofMul ⟨(θ x).toMul, (mem_range_H2ToCenter_iff π hπ σ hσ _).mp ⟨x, rfl⟩⟩
  map_zero' := Additive.toMul.injective <| Subtype.ext <| by simp
  map_add' x y := Additive.toMul.injective <| Subtype.ext <| by simp

lemma coe_H2ToKerInfCommutator (x : H2 (Rep.trivial ℤ G ℤ)) :
    ((π.H2ToKerInfCommutator hπ σ hσ x).toMul : C) = (θ x).toMul :=
  rfl

/-- **`N ∩ C'` is a quotient of the Schur multiplier `H₂(G, ℤ)`** (LMFDB `group.stem_extension`,
`group.schur_multiplier`), for a homomorphism `π : C →* G` with central kernel `N` and a section `σ`
of `π`. -/
lemma surjective_H2ToKerInfCommutator : Function.Surjective (π.H2ToKerInfCommutator hπ σ hσ) := by
  intro y
  rcases exists_H2ToCenter_eq π hπ σ hσ (z := ⟨y.toMul, hπ (mem_inf.mp y.toMul.2).1⟩) y.toMul.2 with
    ⟨x, hx⟩
  exact ⟨x, Additive.toMul.injective <| Subtype.ext <| by
    rw [coe_H2ToKerInfCommutator, hx, toMul_ofMul]⟩

end MonoidHom
