import LeanBridge.ForMathlib.GroupTheory.Isoclinism
import LeanBridge.ForMathlib.GroupTheory.SchurMultiplier.CentralExtension
import LeanBridge.ForMathlib.GroupTheory.StemExtension
import Mathlib.GroupTheory.Schreier
import TauCeti.Algebra.GroupAction.Trivial
import TauCeti.GroupTheory.GroupExtension.Of.FactorSet
import TauCeti.LinearAlgebra.FreeModule.PID

/-!
# A Schur cover

For a group `G`, let `M = H₂(G, ℤ)` be its Schur multiplier (Mathlib's
`groupHomology (Rep.trivial ℤ G ℤ) 2`, LMFDB `group.schur_multiplier`). The `1`-boundaries form a
submodule of the free `ℤ`-module of `1`-chains, so they are free (Tau Ceti's
`Submodule.free_of_isPrincipalIdealRing`, in every rank), and the `2`-cycles have a complement in
the `2`-chains. Extending the quotient map `Z₂ → M` to the `2`-chains gives a function
`f : G × G → M` whose values pair with every `2`-cycle `z` to its class `[z]`, and which satisfies
the cocycle identity since `M` kills the boundaries. Normalised, it is a factor set (Tau Ceti's
`TauCeti.FactorSet`, for the trivial action), and the extension it builds is a central extension
`1 → M → SchurCover G → G → 1`.

Its homomorphism `θ : H₂(G, ℤ) → Z(SchurCover G)` (`MonoidHom.H2ToCenter`, for the canonical
section) is the inclusion of `M`, so `M` lies in the commutator subgroup: the extension is a stem
extension (LMFDB `group.stem_extension`) whose kernel is the Schur multiplier itself. For a finite
group `G` the centre of `SchurCover G` has finite index, so its commutator subgroup is finite by
Schur's theorem (Mathlib's instance `Finite (commutator G)` for finitely many commutators), and so
is the Schur multiplier.

## Main definitions

* `SchurCover.factorSet`: the normalised `2`-cocycle `G × G → H₂(G, ℤ)`.
* `SchurCover G`: the group it builds, a Schur cover of `G`.
* `SchurCover.extension`: the stem extension `1 → H₂(G, ℤ) → SchurCover G → G → 1`.

## Main results

* `SchurCover.isStem_extension` (LMFDB `group.stem_extension`, `group.schur_multiplier`): the
  Schur multiplier is the kernel of a stem extension of `G`.
* `SchurCover.finite_H2` (LMFDB `group.schur_multiplier`): the Schur multiplier of a finite group is
  finite.

## References

* I. Schur, *Über die Darstellung der endlichen Gruppen durch gebrochene lineare Substitutionen*,
  J. Reine Angew. Math. 127 (1904), 20–50.
* G. Karpilovsky, *The Schur Multiplier*, London Mathematical Society Monographs 2, Oxford
  University Press (1987), Ch. 2.
-/

open Finsupp Subgroup groupHomology TauCeti

open scoped IsMulCommutative

attribute [local instance] trivialMulDistribMulAction

variable (G : Type) [Group G]

namespace groupHomology

lemma linearCombination_one_d₂₁ (x : G × G →₀ ℤ) : linearCombination ℤ (fun _ ↦ (1 : ℤ))
    ((d₂₁ (Rep.trivial ℤ G ℤ)).hom x) = linearCombination ℤ (fun _ ↦ (1 : ℤ)) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | single p n => simp [d₂₁]

lemma linearCombination_one_eq_zero_of_mem_cycles₂ {z : G × G →₀ ℤ}
    (hz : z ∈ cycles₂ (Rep.trivial ℤ G ℤ)) : linearCombination ℤ (fun _ ↦ (1 : ℤ)) z = 0 := by
  rw [← linearCombination_one_d₂₁, LinearMap.mem_ker.mp hz, map_zero]

end groupHomology

namespace SchurCover

lemma exists_retraction : ∃ r : (G × G →₀ ℤ) →ₗ[ℤ] cycles₂ (Rep.trivial ℤ G ℤ),
    ∀ z : cycles₂ (Rep.trivial ℤ G ℤ), r z = z := by
  let d : (G × G →₀ ℤ) →ₗ[ℤ] (G →₀ ℤ) := (d₂₁ (Rep.trivial ℤ G ℤ)).hom
  have : Module.Free ℤ (LinearMap.range d) := Submodule.free_of_isPrincipalIdealRing _
  rcases Module.projective_lifting_property d.rangeRestrict LinearMap.id d.surjective_rangeRestrict
    with ⟨s, hs⟩
  refine ⟨LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ d.rangeRestrict) fun x ↦ ?_, fun z ↦ ?_⟩
  · exact LinearMap.mem_ker.mpr <| (map_sub d x _).trans <| sub_eq_zero.mpr
      (congrArg Subtype.val (LinearMap.congr_fun hs (d.rangeRestrict x))).symm
  · have hz : d.rangeRestrict z = 0 := Subtype.ext z.2
    exact Subtype.ext <| sub_eq_self.mpr <| (congrArg s hz).trans (map_zero s)

/-- A retraction of the `2`-chains onto the `2`-cycles of the trivial representation `ℤ` of `G`. -/
noncomputable def retraction : (G × G →₀ ℤ) →ₗ[ℤ] cycles₂ (Rep.trivial ℤ G ℤ) :=
  (exists_retraction G).choose

lemma retraction_apply (z : cycles₂ (Rep.trivial ℤ G ℤ)) : retraction G z = z :=
  (exists_retraction G).choose_spec z

/-- The extension `C₂ → H₂(G, ℤ)` of the quotient map from the `2`-cycles to the Schur multiplier,
through `retraction`. -/
noncomputable def classOfChain : (G × G →₀ ℤ) →ₗ[ℤ] H2 (Rep.trivial ℤ G ℤ) :=
  (H2π (Rep.trivial ℤ G ℤ)).hom ∘ₗ retraction G

lemma classOfChain_apply (z : cycles₂ (Rep.trivial ℤ G ℤ)) :
    classOfChain G z = H2π (Rep.trivial ℤ G ℤ) z := by
  rw [classOfChain, LinearMap.comp_apply, retraction_apply]

lemma classOfChain_d₃₂ (x : G × G × G →₀ ℤ) :
    classOfChain G ((d₃₂ (Rep.trivial ℤ G ℤ)).hom x) = 0 := by
  have hx : (d₃₂ (Rep.trivial ℤ G ℤ)).hom x ∈ cycles₂ (Rep.trivial ℤ G ℤ) :=
    boundaries₂_le_cycles₂ _ (LinearMap.mem_range_self _ x)
  exact (classOfChain_apply G ⟨_, hx⟩).trans ((H2π_eq_zero_iff ⟨_, hx⟩).mpr ⟨x, rfl⟩)

lemma classOfChain_cocycle (g h j : G) : classOfChain G (single (g * h, j) 1) +
    classOfChain G (single (g, h) 1) = classOfChain G (single (h, j) 1) +
      classOfChain G (single (g, h * j) 1) := by
  have h₀ :
      classOfChain G ((d₃₂ (Rep.trivial ℤ G ℤ)).hom (single (g, h, j) 1 : G × G × G →₀ ℤ)) = 0 :=
    classOfChain_d₃₂ G (single (g, h, j) 1)
  simp [d₃₂] at h₀
  rw [← sub_eq_zero, ← neg_eq_zero, ← h₀]
  abel

/-- The normalised `2`-cocycle `(g, h) ↦ c[g, h] - c[1, 1]` of `G` with values in its Schur
multiplier `H₂(G, ℤ)`, written multiplicatively, where `c` is `classOfChain`: a factor set for the
trivial action of `G`. -/
noncomputable def factorSet : FactorSet G (Multiplicative (H2 (Rep.trivial ℤ G ℤ))) where
  toFun p := .ofAdd (classOfChain G (single p 1) - classOfChain G (single (1, 1) 1))
  isMulCocycle₂' g h j := by
    rw [trivialMulDistribMulAction_smul, ← ofAdd_add, ← ofAdd_add, sub_add_sub_comm,
      sub_add_sub_comm, classOfChain_cocycle]
  map_one_one' := by simp

end SchurCover

/-- **A Schur cover of `G`**: the central extension of `G` by its Schur multiplier `H₂(G, ℤ)` built
from `SchurCover.factorSet`. It depends on a choice of a retraction of the `2`-chains onto the
`2`-cycles. -/
abbrev SchurCover : Type :=
  (SchurCover.factorSet G).Extension

namespace SchurCover

/-- The stem extension `1 → H₂(G, ℤ) → SchurCover G → G → 1` (LMFDB `group.stem_extension`). -/
noncomputable def extension :
    GroupExtension (Multiplicative (H2 (Rep.trivial ℤ G ℤ))) (SchurCover G) G :=
  (factorSet G).groupExtension

lemma factorSet_apply (p : G × G) :
    factorSet G p = .ofAdd (classOfChain G (single p 1) - classOfChain G (single (1, 1) 1)) :=
  rfl

lemma range_inl_le_center : (factorSet G).inl.range ≤ center (SchurCover G) :=
  (factorSet G).inl_range_le_center fun _ _ ↦ rfl

lemma ker_rightHom_le_center : (factorSet G).rightHom.ker ≤ center (SchurCover G) :=
  (factorSet G).range_inl_eq_ker_rightHom ▸ range_inl_le_center G

/-- The inclusion of the Schur multiplier `H₂(G, ℤ)` in the centre of the Schur cover. -/
noncomputable def inlCenter : Multiplicative (H2 (Rep.trivial ℤ G ℤ)) →* center (SchurCover G) :=
  (factorSet G).inl.codRestrict _ fun m ↦ range_inl_le_center G ⟨m, rfl⟩

lemma rightHom_canonicalSection (g : G) :
    (factorSet G).rightHom ((factorSet G).canonicalSection g) = g :=
  rfl

local notation "α" => MonoidHom.centralFactorSet (FactorSet.rightHom (factorSet G))
  (ker_rightHom_le_center G) (FactorSet.canonicalSection (factorSet G))
  (rightHom_canonicalSection G)

local notation "θ₀" => MonoidHom.centralFactorSetChain (FactorSet.rightHom (factorSet G))
  (ker_rightHom_le_center G) (FactorSet.canonicalSection (factorSet G))
  (rightHom_canonicalSection G)

local notation "θ" => MonoidHom.H2ToCenter (FactorSet.rightHom (factorSet G))
  (ker_rightHom_le_center G) (FactorSet.canonicalSection (factorSet G))
  (rightHom_canonicalSection G)

lemma centralFactorSet_eq (p : G × G) : α p = inlCenter G (factorSet G p) :=
  Subtype.ext <| mul_inv_eq_of_eq_mul <| (factorSet G).canonicalSection_mul p.1 p.2

lemma centralFactorSetChain_eq (x : G × G →₀ ℤ) : θ₀ x = (inlCenter G).toAdditiveRight
    (classOfChain G (x - linearCombination ℤ (fun _ ↦ (1 : ℤ)) x • single (1, 1) 1)) := by
  let ε : (G × G →₀ ℤ) →ₗ[ℤ] (G × G →₀ ℤ) := LinearMap.id -
    (LinearMap.toSpanSingleton ℤ _ (single (1, 1) 1)).comp (linearCombination ℤ fun _ ↦ (1 : ℤ))
  have h : (θ₀).toAddMonoidHom = (inlCenter G).toAdditiveRight.comp
      ((classOfChain G).toAddMonoidHom.comp ε.toAddMonoidHom) := by
    refine Finsupp.addHom_ext' fun p ↦ AddMonoidHom.ext_int ?_
    simp [ε, MonoidHom.centralFactorSetChain_single]
    rw [centralFactorSet_eq, factorSet_apply]
    exact map_sub (inlCenter G).toAdditiveRight _ _
  exact DFunLike.congr_fun h x

lemma H2ToCenter_eq (x : H2 (Rep.trivial ℤ G ℤ)) : θ x = (inlCenter G).toAdditiveRight x := by
  induction x using H2_induction_on with
  | h z =>
    rw [MonoidHom.H2ToCenter_H2π, centralFactorSetChain_eq,
      linearCombination_one_eq_zero_of_mem_cycles₂ G z.2, zero_smul, sub_zero, classOfChain_apply]

/-- **The Schur multiplier is the kernel of a stem extension** (LMFDB `group.stem_extension`,
`group.schur_multiplier`): `1 → H₂(G, ℤ) → SchurCover G → G → 1` is a stem extension, for every
group `G`. -/
lemma isStem_extension : (extension G).IsStem := by
  rintro _ ⟨m, rfl⟩
  refine mem_inf.mpr ⟨range_inl_le_center G ⟨m, rfl⟩, ?_⟩
  have hm : (((inlCenter G).toAdditiveRight m.toAdd).toMul : SchurCover G) ∈
      (factorSet G).rightHom.ker ⊓ commutator (SchurCover G) :=
    ((factorSet G).rightHom.mem_range_H2ToCenter_iff (ker_rightHom_le_center G)
      (factorSet G).canonicalSection (rightHom_canonicalSection G) _).mp
      ⟨m.toAdd, H2ToCenter_eq G _⟩
  exact (mem_inf.mp hm).2

end SchurCover

lemma Subgroup.finite_commutatorSet {E : Type*} [Group E] [(center E).FiniteIndex] :
    (commutatorSet E).Finite := by
  refine (Set.finite_range fun p : (E ⧸ center E) × (E ⧸ center E) ↦
    (Group.centralCommutatorMap E p.1 p.2 : E)).subset ?_
  rintro _ ⟨g, h, rfl⟩
  exact ⟨(↑g⁻¹, ↑h⁻¹), (Group.commutatorElement_eq_centralCommutatorMap g h).symm⟩

namespace SchurCover

variable [Finite G] in
/-- **The Schur multiplier of a finite group is finite** (LMFDB `group.schur_multiplier`): the
centre of `SchurCover G` has finite index, so its commutator subgroup is finite by Schur's theorem,
and it contains the Schur multiplier. -/
lemma finite_H2 : Finite (H2 (Rep.trivial ℤ G ℤ)) := by
  have : (center (SchurCover G)).FiniteIndex := finiteIndex_of_le (ker_rightHom_le_center G)
  have : Finite (commutatorSet (SchurCover G)) := finite_commutatorSet.to_subtype
  have hle : (extension G).inl.range ≤ commutator (SchurCover G) := fun _ hx ↦
    (mem_inf.mp (isStem_extension G hx)).2
  have : Finite (extension G).inl.range := Finite.of_injective _ (inclusion_injective hle)
  have : Finite (Multiplicative (H2 (Rep.trivial ℤ G ℤ))) :=
    Finite.of_injective _ ((extension G).inl.rangeRestrict_injective_iff.mpr
      (extension G).inl_injective)
  exact Finite.of_equiv _ Multiplicative.toAdd

variable [Finite G] in
instance : Finite (H2 (Rep.trivial ℤ G ℤ)) :=
  finite_H2 G

end SchurCover
