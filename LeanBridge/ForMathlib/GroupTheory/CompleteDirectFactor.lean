import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.SpecificGroups.Heisenberg
import LeanBridge.ForMathlib.GroupTheory.Complete

/-!
# Complete groups are the direct factors of every group containing them as normal subgroups

A complete group is a direct factor of every group in which it is a normal subgroup, its
centralizer being a normal complement (`Subgroup.isComplement'_centralizer`). Conversely (Baer), a
group `G` that is a direct factor of every group containing it as a normal subgroup is complete.
Its automorphisms are inner, as `G` is a direct factor of its holomorph `G ⋊ Aut(G)`
(`Group.surjective_conj_of_isComplement'`). Its centre is trivial: a central element `z` becomes
the commutator `c = ⁅(1, 0, 0), (0, 1, 0)⁆ = (0, 0, 1)` of the Heisenberg group `H(ℤ)`, which is
central and of infinite order, in the central product `(G × H(ℤ)) / ⟨(z, c⁻¹)⟩`. There `G` is a
normal subgroup, and a retraction onto `G` along a normal complement sends `H(ℤ)`, which
centralizes `G`, into the centre of `G`, hence the commutator `c`, that is `z`, to `1`.

Groups are embedded in groups of their own universe.

## Main results

* `Group.IsComplete.isComplement'_centralizer_range` (LMFDB `group.complete`): a complete group is
  a direct factor of every group containing it as a normal subgroup, with the centralizer as a
  normal complement.
* `Group.center_eq_bot_of_forall_exists_isComplement'`: a group that is a direct factor of every
  group containing it as a normal subgroup has trivial centre.
* `Group.surjective_conj_of_forall_exists_isComplement'`: all automorphisms of such a group are
  inner.
* `Group.isComplete_iff_forall_exists_isComplement'` (LMFDB `group.complete`): **Baer's theorem**,
  a group is complete if and only if it is a direct factor of every group containing it as a
  normal subgroup.

## References

* R. Baer, *Absolute retracts in group theory*, Bull. Amer. Math. Soc. **52** (1946), 501–506.
* J. J. Rotman, *An Introduction to the Theory of Groups*, 4th ed., Graduate Texts in Mathematics
  148, Springer, 1995, chapter 7.
-/

universe u v

open Subgroup TauCeti

open scoped commutatorElement

namespace Group

variable {G : Type u} [Group G]

/-- **A complete group is a direct factor of every group containing it as a normal subgroup**
(LMFDB `group.complete`), in any universe: the image of an injective homomorphism `f : G →* H` is
complete, so if it is normal, its centralizer, a normal subgroup, is a complement
(`Subgroup.isComplement'_centralizer`). -/
lemma IsComplete.isComplement'_centralizer_range [IsComplete G] {H : Type v} [Group H] {f : G →* H}
    (hf : Function.Injective f) [f.range.Normal] : f.range.IsComplement' (centralizer f.range) :=
  have : IsComplete f.range := IsComplete.of_mulEquiv (MonoidHom.ofInjective hf)
  f.range.isComplement'_centralizer

private lemma zpow_heisenberg (k : ℤ) : (⟨0, 0, 1⟩ : HeisenbergGroup ℤ) ^ k = ⟨0, 0, k⟩ := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ k ih =>
    rw [zpow_add_one, ih]
    ext <;> simp
  | pred k ih =>
    rw [zpow_sub_one, ih]
    ext <;> simp [sub_eq_add_neg]

/-- **A group that is a direct factor of every group containing it as a normal subgroup has trivial
centre.** A central element `z` is identified with the central commutator `c = (0, 0, 1)` of the
Heisenberg group `H(ℤ)` in the central product `(G × H(ℤ)) / ⟨(z, c⁻¹)⟩`, in which `G` is normal;
a retraction onto `G` sends `H(ℤ)` into the centre of `G`, hence `c = z` to `1`. -/
lemma center_eq_bot_of_forall_exists_isComplement' (h : ∀ (H : Type u) [Group H] (f : G →* H),
    Function.Injective f → f.range.Normal → ∃ K : Subgroup H, K.Normal ∧ f.range.IsComplement' K) :
    center G = ⊥ := by
  refine eq_bot_iff.mpr fun z hz ↦ mem_bot.mpr ?_
  let c : HeisenbergGroup ℤ := ⟨0, 0, 1⟩
  have hc : c ∈ center (HeisenbergGroup ℤ) := HeisenbergGroup.zAxis_le_center ⟨rfl, rfl⟩
  have hcomm : ⁅(⟨1, 0, 0⟩ : HeisenbergGroup ℤ), ⟨0, 1, 0⟩⁆ = c := by
    rw [HeisenbergGroup.commutatorElement_eq]
    ext <;> simp [c]
  have hd : zpowers ((z, c⁻¹) : G × HeisenbergGroup ℤ) ≤ center (G × HeisenbergGroup ℤ) := by
    rw [zpowers_le, mem_center_iff]
    exact fun x ↦ Prod.ext (mem_center_iff.mp hz x.1) (mem_center_iff.mp (inv_mem hc) x.2)
  have : (zpowers ((z, c⁻¹) : G × HeisenbergGroup ℤ)).Normal := normal_of_le_center hd
  let ι : G →* (G × HeisenbergGroup ℤ) ⧸ zpowers ((z, c⁻¹) : G × HeisenbergGroup ℤ) :=
    (QuotientGroup.mk' _).comp (MonoidHom.inl _ _)
  let j :
      HeisenbergGroup ℤ →* (G × HeisenbergGroup ℤ) ⧸ zpowers ((z, c⁻¹) : G × HeisenbergGroup ℤ) :=
    (QuotientGroup.mk' _).comp (MonoidHom.inr _ _)
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).mpr fun g hg ↦ ?_
    rcases mem_zpowers_iff.mp ((QuotientGroup.eq_one_iff _).mp hg) with ⟨k, hk⟩
    have h1 : z ^ k = g := congrArg Prod.fst hk
    have h2 : c⁻¹ ^ k = 1 := congrArg Prod.snd hk
    rw [inv_zpow', zpow_heisenberg] at h2
    have hk0 : k = 0 := by simpa using congrArg HeisenbergGroup.z h2
    rw [← h1, hk0, zpow_zero]
  have hinl : (MonoidHom.inl G (HeisenbergGroup ℤ)).range.Normal :=
    ⟨fun _ ⟨g, hg⟩ x ↦ ⟨x.1 * g * x.1⁻¹, hg ▸ Prod.ext (by simp) (by simp)⟩⟩
  have hN : ι.range.Normal := by
    rw [MonoidHom.range_comp]
    exact hinl.map _ (QuotientGroup.mk'_surjective _)
  rcases h _ ι hι hN with ⟨K, hK, hcompl⟩
  let r : (G × HeisenbergGroup ℤ) ⧸ zpowers ((z, c⁻¹) : G × HeisenbergGroup ℤ) →* G :=
    (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
      (hcompl.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' K))
  have hr (g : G) : r (ι g) = g :=
    (MonoidHom.ofInjective hι).symm_apply_eq.mpr (hcompl.QuotientMulEquiv.eq_symm_apply.mp rfl)
  have hcen (b : HeisenbergGroup ℤ) : r (j b) ∈ center G := mem_center_iff.mpr fun g ↦ by
    rw [← hr g, ← map_mul, ← map_mul]
    exact congrArg r ((MonoidHom.commute_inl_inr g b).map (QuotientGroup.mk' _)).eq
  have hrc : r (j c) = 1 := by
    rw [← congrArg j hcomm, map_commutatorElement, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact (mem_center_iff.mp (hcen _) _).symm
  have hdc : ((1, c) : G × HeisenbergGroup ℤ)⁻¹ * (z, 1) = (z, c⁻¹) := by
    simp
  have hjc : j c = ι z := QuotientGroup.eq.mpr (hdc ▸ mem_zpowers _)
  rw [← hr z, ← hjc, hrc]

/-- **All automorphisms of a group that is a direct factor of every group containing it as a normal
subgroup are inner**, as it is a direct factor of its holomorph `G ⋊ Aut(G)`
(`Group.surjective_conj_of_isComplement'`). -/
lemma surjective_conj_of_forall_exists_isComplement' (h : ∀ (H : Type u) [Group H] (f : G →* H),
    Function.Injective f → f.range.Normal → ∃ K : Subgroup H, K.Normal ∧ f.range.IsComplement' K) :
    Function.Surjective (MulAut.conj : G →* MulAut G) := by
  have hN : (SemidirectProduct.inl : G →* G ⋊[MonoidHom.id (MulAut G)] MulAut G).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  rcases h _ _ SemidirectProduct.inl_injective hN with ⟨K, hK, hc⟩
  exact surjective_conj_of_isComplement' hc

/-- **Baer's theorem** (LMFDB `group.complete`): a group `G` is complete if and only if it is a
direct factor of every group `H` (of the universe of `G`) containing it as a normal subgroup, that
is, the image of every injective homomorphism `f : G →* H` with normal image has a normal
complement. -/
lemma isComplete_iff_forall_exists_isComplement' : IsComplete G ↔ ∀ (H : Type u) [Group H]
    (f : G →* H), Function.Injective f → f.range.Normal →
      ∃ K : Subgroup H, K.Normal ∧ f.range.IsComplement' K :=
  ⟨fun _ _ _ _ hf _ ↦ ⟨_, inferInstance, IsComplete.isComplement'_centralizer_range hf⟩,
    fun h ↦ (isComplete_iff G).mpr ⟨center_eq_bot_of_forall_exists_isComplement' h,
      surjective_conj_of_forall_exists_isComplement' h⟩⟩

end Group
