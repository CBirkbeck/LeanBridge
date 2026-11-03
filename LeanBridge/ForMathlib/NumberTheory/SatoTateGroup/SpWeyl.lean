import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.MomentMatrix
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.SpCartan

/-!
# The Weyl group of the symplectic Lie algebra

The Weyl group of the root system of `𝔰𝔭(2g, ℂ)` acts on the weights by signed permutations of the
coordinates (`SatoTateGroup.spAct`), and all signed permutations arise. The sign of a Weyl group
element is the sign of the permutation times the product of the signs.

## Main definitions

* `SatoTateGroup.spAct`: the signed permutation of the coordinates of a weight.
* `SatoTateGroup.spSign`: its sign.
* `SatoTateGroup.IsSpSigned`: an element of the Weyl group acts by a signed permutation.
* `SatoTateGroup.spHeight`: the height of an index of the standard module.

## Main results

* `SatoTateGroup.exists_isSpSigned`: an element of the Weyl group acts by a signed permutation.
* `SatoTateGroup.exists_isSpSigned_of`: all signed permutations arise.
* `SatoTateGroup.sum_weylGroup_eq`: a signed sum over the Weyl group is a signed sum over the signed
  permutations.
* `SatoTateGroup.weylVector_spDelta`: the Weyl vector is `(g, g - 1, …, 1)`.
* `SatoTateGroup.exists_apply_spDelta_eq_highestWeight`: a dominant integral weight is a partition
  with at most `g` parts.
* `SatoTateGroup.isHighestWeightVector_of_spRootVector`: to be a highest weight vector, it is enough
  to be killed by the root vectors of the positive roots.
-/

open Equiv LieAlgebra LieModule Module RootPairing TauCeti

namespace SatoTateGroup

variable {g : ℕ}

lemma spRootIdx_congr {a b b' : Fin g ⊕ Fin g} (h : b = b') (hab : a ≠ b) :
    spRootIdx a b hab = spRootIdx a b' (h ▸ hab) := by
  subst h
  rfl

lemma coroot_spRootIdx_short {i j : Fin g} (hij : i ≠ j)
    (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inl j) :
    (IsKilling.rootSystem (spCartan (g := g))).coroot (spRootIdx (.inl i) (.inl j) hne) =
      spDelta i - spDelta j := by
  refine Subtype.ext ?_
  refine (coroot_short hij hne).trans ?_
  rw [map_sub]
  rfl

lemma coroot_spRootIdx_long (i : Fin g) (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inr i) :
    (IsKilling.rootSystem (spCartan (g := g))).coroot (spRootIdx (.inl i) (.inr i) hne) =
      spDelta i :=
  Subtype.ext (coroot_long i hne)

lemma spSimpleIdx_eq_of_lt (k : Fin g) (h : (k : ℕ) + 1 < g) : spSimpleIdx k =
    spRootIdx (.inl k) (.inl ⟨k + 1, h⟩)
      (by simp [Fin.ext_iff] : (Sum.inl k : Fin g ⊕ Fin g) ≠ Sum.inl ⟨k + 1, h⟩) :=
  spRootIdx_congr (dite_eq_left_of_eq_true (eq_true h)) _

lemma spSimpleIdx_eq_of_not_lt (k : Fin g) (h : ¬(k : ℕ) + 1 < g) :
    spSimpleIdx k = spRootIdx (.inl k) (.inr k) (by simp) :=
  spRootIdx_congr (dite_eq_right_of_eq_false (eq_false h)) _

lemma spEpsilon_spDelta_eq_ite (i j : Fin g) :
    spEpsilon i (spDelta j) = if i = j then 1 else 0 := by
  rw [spEpsilon_spDelta, Pi.single_apply]

/-- The signed permutation of the coordinates of a weight: the coordinate `φ(δᵢ)` of `φ` becomes
the coordinate `sᵢ φ(δᵢ)` at the index `π i`. -/
noncomputable def spAct (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) (φ : Dual ℂ (spCartan (g := g))) :
    Dual ℂ (spCartan (g := g)) :=
  ∑ i, (((s i : ℤ) : ℂ) * φ (spDelta i)) • spEpsilon (π i)

lemma spAct_apply (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) (φ : Dual ℂ (spCartan (g := g)))
    (m : Fin g) : spAct π s φ (spDelta m) = ((s (π⁻¹ m) : ℤ) : ℂ) * φ (spDelta (π⁻¹ m)) := by
  rw [spAct, LinearMap.sum_apply, Finset.sum_eq_single (π⁻¹ m)]
  · rw [LinearMap.smul_apply, spEpsilon_spDelta_eq_ite, ite_eq_left (by simp), smul_eq_mul, mul_one]
  · intro i _ hi
    have h₁ : π i ≠ m := fun h ↦ hi (by simp [← h])
    rw [LinearMap.smul_apply, spEpsilon_spDelta_eq_ite, ite_eq_right h₁, smul_zero]
  · simp

lemma spAct_spAct (π π' : Equiv.Perm (Fin g)) (s s' : Fin g → ℤˣ) (φ : Dual ℂ (spCartan (g := g))) :
    spAct π s (spAct π' s' φ) = spAct (π * π') (fun i ↦ s (π' i) * s' i) φ := by
  refine dual_ext fun m ↦ ?_
  have h₁ : π' (π'⁻¹ (π⁻¹ m)) = π⁻¹ m := π'.apply_symm_apply _
  rw [spAct_apply, spAct_apply, spAct_apply, mul_inv_rev, Perm.mul_apply, h₁]
  push_cast
  ring1

lemma spAct_one_apply (s : Fin g → ℤˣ) (φ : Dual ℂ (spCartan (g := g))) (m : Fin g) :
    spAct 1 s φ (spDelta m) = ((s m : ℤ) : ℂ) * φ (spDelta m) :=
  spAct_apply 1 s φ m

lemma spAct_one_one (φ : Dual ℂ (spCartan (g := g))) : spAct 1 1 φ = φ := by
  refine dual_ext fun m ↦ ?_
  rw [spAct_one_apply]
  simp

/-- The sign of a signed permutation: the sign of the permutation times the product of the signs. -/
def spSign (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) : ℤˣ :=
  Perm.sign π * ∏ i, s i

lemma spSign_mul (π π' : Equiv.Perm (Fin g)) (s s' : Fin g → ℤˣ) :
    spSign (π * π') (fun i ↦ s (π' i) * s' i) = spSign π s * spSign π' s' := by
  rw [spSign, spSign, spSign, Perm.sign_mul, Finset.prod_mul_distrib, Equiv.prod_comp π' s]
  simp only [mul_assoc, mul_left_comm]

lemma reflection_apply_eq (i : (spCartan (g := g)).root) (φ : Dual ℂ (spCartan (g := g))) :
    (IsKilling.rootSystem (spCartan (g := g))).reflection i φ =
      φ - φ ((IsKilling.rootSystem (spCartan (g := g))).coroot i) •
        (IsKilling.rootSystem (spCartan (g := g))).root i := by
  rw [RootPairing.reflection_apply]
  rfl

lemma reflection_short {i j : Fin g} (hij : i ≠ j) (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inl j)
    (φ : Dual ℂ (spCartan (g := g))) :
    (IsKilling.rootSystem (spCartan (g := g))).reflection (spRootIdx (.inl i) (.inl j) hne) φ =
      spAct (Equiv.swap i j) 1 φ := by
  refine dual_ext fun m ↦ ?_
  rw [reflection_apply_eq, coroot_spRootIdx_short hij, root_spRootIdx, spAct_apply, spRootForm,
    spEps_inl, spEps_inl, Perm.inv_def, Equiv.symm_swap]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_sub, spEpsilon_spDelta_eq_ite,
    Pi.one_apply, Units.val_one]
  by_cases hmi : m = i
  · rw [hmi, Equiv.swap_apply_left, ite_eq_left rfl, ite_eq_right (Ne.symm hij)]
    ring1
  by_cases hmj : m = j
  · rw [hmj, Equiv.swap_apply_right, ite_eq_right hij, ite_eq_left rfl]
    ring1
  · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj, ite_eq_right (Ne.symm hmi),
      ite_eq_right (Ne.symm hmj)]
    ring1

/-- The sign change of the coordinate `i`. -/
def spFlip (i : Fin g) : Fin g → ℤˣ :=
  Function.update 1 i (-1)

lemma reflection_long (i : Fin g) (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inr i)
    (φ : Dual ℂ (spCartan (g := g))) :
    (IsKilling.rootSystem (spCartan (g := g))).reflection (spRootIdx (.inl i) (.inr i) hne) φ =
      spAct 1 (spFlip i) φ := by
  refine dual_ext fun m ↦ ?_
  rw [reflection_apply_eq, coroot_spRootIdx_long i, root_spRootIdx, spAct_one_apply, spRootForm,
    spEps_inl, spEps_inr]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    spEpsilon_spDelta_eq_ite, spFlip]
  by_cases hmi : m = i
  · rw [hmi, Function.update_self, ite_eq_left rfl]
    simp
    ring1
  · rw [Function.update_of_ne hmi, ite_eq_right (Ne.symm hmi)]
    simp

lemma spSign_swap {i j : Fin g} (hij : i ≠ j) : spSign (Equiv.swap i j) 1 = -1 := by
  simp [spSign, Perm.sign_swap hij]

lemma spSign_flip (i : Fin g) : spSign 1 (spFlip i) = -1 := by
  classical
  rw [spSign, map_one, one_mul, spFlip, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

variable (g) in
/-- The root system of the diagonal Cartan subalgebra of `𝔰𝔭(2g, ℂ)`. -/
noncomputable abbrev spRootSystem :=
  IsKilling.rootSystem (spCartan (g := g))

lemma exists_spSimpleIdx_eq (i : (spBase (g := g)).support) :
    ∃ k, spSimpleIdx k = (i : (spCartan (g := g)).root) :=
  mem_spBase_support.mp i.2

section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma ofIdx_mul_smul (P : RootPairing ι R M N) (i : ι) (w : P.weylGroup) (m : M) :
    (weylGroup.ofIdx P i * w) • m = P.reflection i (w • m) :=
  mul_smul _ _ _

lemma weylSign_ofIdx_mul [Finite ι] [CharZero R] [IsDomain R] (P : RootPairing ι R M N)
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base) (i : ι) (w : P.weylGroup) :
    weylSign P b (weylGroup.ofIdx P i * w) = -weylSign P b w := by
  rw [map_mul, weylSign_ofIdx, neg_one_mul]

end

/-- The Weyl group element `w` acts by the signed permutation `(π, s)` with the same sign. -/
def IsSpSigned (w : (spRootSystem g).weylGroup) (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) : Prop :=
  (∀ φ, w • φ = spAct π s φ) ∧ weylSign (spRootSystem g) spBase w = spSign π s

lemma isSpSigned_one : IsSpSigned (1 : (spRootSystem g).weylGroup) 1 1 := by
  refine ⟨fun φ ↦ ?_, ?_⟩
  · rw [one_smul, spAct_one_one]
  · simp [spSign]

lemma IsSpSigned.ofIdx_short {w : (spRootSystem g).weylGroup} {π : Equiv.Perm (Fin g)}
    {s : Fin g → ℤˣ} (h : IsSpSigned w π s) {i j : Fin g} (hij : i ≠ j)
    (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inl j) :
    IsSpSigned (weylGroup.ofIdx _ (spRootIdx (.inl i) (.inl j) hne) * w)
      (Equiv.swap i j * π) s := by
  have h₁ : (fun m ↦ (1 : Fin g → ℤˣ) (π m) * s m) = s := by
    funext m
    rw [Pi.one_apply, one_mul]
  refine ⟨fun φ ↦ ?_, ?_⟩
  · rw [ofIdx_mul_smul, h.1, reflection_short hij, spAct_spAct, h₁]
  · have h₂ : spSign (Equiv.swap i j * π) s = spSign (Equiv.swap i j) 1 * spSign π s := by
      rw [← spSign_mul, h₁]
    rw [weylSign_ofIdx_mul, h.2, h₂, spSign_swap hij, neg_one_mul]

lemma IsSpSigned.ofIdx_long {w : (spRootSystem g).weylGroup} {π : Equiv.Perm (Fin g)}
    {s : Fin g → ℤˣ} (h : IsSpSigned w π s) (i : Fin g)
    (hne : (Sum.inl i : Fin g ⊕ Fin g) ≠ Sum.inr i) :
    IsSpSigned (weylGroup.ofIdx _ (spRootIdx (.inl i) (.inr i) hne) * w)
      π (fun m ↦ spFlip i (π m) * s m) := by
  have h₁ : spSign (1 * π) (fun m ↦ spFlip i (π m) * s m) = spSign 1 (spFlip i) * spSign π s :=
    spSign_mul 1 π (spFlip i) s
  refine ⟨fun φ ↦ ?_, ?_⟩
  · rw [ofIdx_mul_smul, h.1, reflection_long, spAct_spAct, one_mul]
  · rw [one_mul] at h₁
    rw [weylSign_ofIdx_mul, h.2, h₁, spSign_flip, neg_one_mul]

lemma exists_isSpSigned_wordProd (l : List (spBase (g := g)).support) :
    ∃ (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ),
      IsSpSigned (wordProd (spRootSystem g) spBase l) π s := by
  induction l with
  | nil => exact ⟨1, 1, isSpSigned_one⟩
  | cons i l ih =>
    rcases ih with ⟨π, s, h⟩
    rcases exists_spSimpleIdx_eq i with ⟨k, hk⟩
    rw [wordProd_cons, ← hk]
    by_cases hlt : (k : ℕ) + 1 < g
    · rw [spSimpleIdx_eq_of_lt k hlt]
      exact ⟨_, _, h.ofIdx_short (by simp [Fin.ext_iff]) _⟩
    · rw [spSimpleIdx_eq_of_not_lt k hlt]
      exact ⟨_, _, h.ofIdx_long k _⟩

/-- **An element of the Weyl group acts by a signed permutation**, and its sign is the sign of the
signed permutation. -/
lemma exists_isSpSigned (w : (spRootSystem g).weylGroup) :
    ∃ (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ), IsSpSigned w π s := by
  rcases exists_wordProd_eq (spRootSystem g) spBase w with ⟨l, hl⟩
  rw [← hl]
  exact exists_isSpSigned_wordProd l

lemma exists_isSpSigned_perm (π : Equiv.Perm (Fin g)) :
    ∃ w : (spRootSystem g).weylGroup, IsSpSigned w π 1 := by
  induction π using Perm.swap_induction_on with
  | one => exact ⟨1, isSpSigned_one⟩
  | swap_mul f x y hxy ih =>
    rcases ih with ⟨w, hw⟩
    exact ⟨_, hw.ofIdx_short hxy (by simpa using hxy)⟩

lemma exists_isSpSigned_finset (π : Equiv.Perm (Fin g)) (A : Finset (Fin g)) :
    ∃ w : (spRootSystem g).weylGroup, IsSpSigned w π fun m ↦ if π m ∈ A then -1 else 1 := by
  induction A using Finset.induction_on with
  | empty =>
    have h₁ : (fun m ↦ if π m ∈ (∅ : Finset (Fin g)) then (-1 : ℤˣ) else 1) = 1 := by
      funext m
      simp
    rw [h₁]
    exact exists_isSpSigned_perm π
  | insert k A hk ih =>
    rcases ih with ⟨w, hw⟩
    have h₁ : (fun m ↦ spFlip k (π m) * if π m ∈ A then (-1 : ℤˣ) else 1) =
        fun m ↦ if π m ∈ insert k A then -1 else 1 := by
      funext m
      by_cases hm : π m = k
      · simp [spFlip, hm, hk]
      · simp [spFlip, hm]
    rw [← h₁]
    exact ⟨_, hw.ofIdx_long k (by simp)⟩

/-- **All signed permutations arise from the Weyl group.** -/
lemma exists_isSpSigned_of (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) :
    ∃ w : (spRootSystem g).weylGroup, IsSpSigned w π s := by
  have h₁ : s = fun m ↦ if π m ∈ Finset.univ.filter (fun k ↦ s (π⁻¹ k) = -1) then -1 else 1 := by
    funext m
    rcases Int.units_eq_one_or (s m) with h | h <;> simp [h]
  rw [h₁]
  exact exists_isSpSigned_finset π _

lemma spAct_spEpsilon (π : Equiv.Perm (Fin g)) (s : Fin g → ℤˣ) (i : Fin g) :
    spAct π s (spEpsilon i) = ((s i : ℤ) : ℂ) • spEpsilon (π i) := by
  rw [spAct, Finset.sum_eq_single i]
  · rw [spEpsilon_spDelta_eq_ite, ite_eq_left rfl, mul_one]
  · intro j _ hj
    rw [spEpsilon_spDelta_eq_ite, ite_eq_right (Ne.symm hj), mul_zero, zero_smul]
  · simp

lemma eq_of_spAct_eq {π π' : Equiv.Perm (Fin g)} {s s' : Fin g → ℤˣ}
    (h : ∀ φ : Dual ℂ (spCartan (g := g)), spAct π s φ = spAct π' s' φ) : (π, s) = (π', s') := by
  have h₁ (i : Fin g) : π i = π' i ∧ s i = s' i := by
    have h₂ : ((s i : ℤ) : ℂ) * spEpsilon (π i) (spDelta (π i)) =
        ((s' i : ℤ) : ℂ) * spEpsilon (π' i) (spDelta (π i)) := by
      have h₃ :
          spAct π s (spEpsilon i) (spDelta (π i)) = spAct π' s' (spEpsilon i) (spDelta (π i)) :=
        DFunLike.congr_fun (h (spEpsilon i)) (spDelta (π i))
      rwa [spAct_spEpsilon, spAct_spEpsilon, LinearMap.smul_apply, LinearMap.smul_apply] at h₃
    rw [spEpsilon_spDelta_eq_ite, spEpsilon_spDelta_eq_ite, ite_eq_left rfl, mul_one] at h₂
    have h₄ : ((s i : ℤ) : ℂ) ≠ 0 := by
      simp
    have h₅ : π' i = π i := by
      by_contra h₆
      rw [ite_eq_right h₆, mul_zero] at h₂
      exact h₄ h₂
    rw [ite_eq_left h₅, mul_one] at h₂
    exact ⟨h₅.symm, Units.ext (by exact_mod_cast h₂)⟩
  exact Prod.ext (Equiv.ext fun i ↦ (h₁ i).1) (funext fun i ↦ (h₁ i).2)

/-- The signed permutation by which an element of the Weyl group acts. -/
noncomputable def spSigned (w : (spRootSystem g).weylGroup) : Equiv.Perm (Fin g) × (Fin g → ℤˣ) :=
  ((exists_isSpSigned w).choose, (exists_isSpSigned w).choose_spec.choose)

lemma isSpSigned_spSigned (w : (spRootSystem g).weylGroup) :
    IsSpSigned w (spSigned w).1 (spSigned w).2 :=
  (exists_isSpSigned w).choose_spec.choose_spec

lemma IsSpSigned.spSigned_eq {w : (spRootSystem g).weylGroup} {π : Equiv.Perm (Fin g)}
    {s : Fin g → ℤˣ} (h : IsSpSigned w π s) : spSigned w = (π, s) :=
  eq_of_spAct_eq fun φ ↦ ((isSpSigned_spSigned w).1 φ).symm.trans (h.1 φ)

lemma injective_spSigned : Function.Injective (spSigned (g := g)) := fun w w' hw ↦ by
  refine weylGroup.ext fun φ ↦ ?_
  rw [(isSpSigned_spSigned w).1, (isSpSigned_spSigned w').1, hw]

lemma surjective_spSigned : Function.Surjective (spSigned (g := g)) := by
  rintro ⟨π, s⟩
  rcases exists_isSpSigned_of π s with ⟨w, hw⟩
  exact ⟨w, hw.spSigned_eq⟩

/-- **A signed sum over the Weyl group is a signed sum over the signed permutations.** -/
lemma sum_weylGroup_eq [Fintype (spRootSystem g).weylGroup] (F : Dual ℂ (spCartan (g := g)) → ℂ)
    (x : Dual ℂ (spCartan (g := g))) : ∑ w : (spRootSystem g).weylGroup,
      (((weylSign (spRootSystem g) spBase w : ℤˣ) : ℤ) : ℂ) * F (w • x) =
        ∑ p : Equiv.Perm (Fin g) × (Fin g → ℤˣ),
          ((spSign p.1 p.2 : ℤ) : ℂ) * F (spAct p.1 p.2 x) := by
  refine Fintype.sum_bijective _ ⟨injective_spSigned, surjective_spSigned⟩ _ _ fun w ↦ ?_
  rw [(isSpSigned_spSigned w).2, (isSpSigned_spSigned w).1]

lemma coroot_spSimpleIdx_of_lt (k : Fin g) (h : (k : ℕ) + 1 < g) :
    (spRootSystem g).coroot (spSimpleIdx k) = spDelta k - spDelta ⟨k + 1, h⟩ := by
  rw [spSimpleIdx_eq_of_lt k h]
  exact coroot_spRootIdx_short (by simp [Fin.ext_iff]) _

lemma coroot_spSimpleIdx_of_not_lt (k : Fin g) (h : ¬(k : ℕ) + 1 < g) :
    (spRootSystem g).coroot (spSimpleIdx k) = spDelta k := by
  rw [spSimpleIdx_eq_of_not_lt k h]
  exact coroot_spRootIdx_long k _

lemma apply_spDelta_eq_sum (φ : Dual ℂ (spCartan (g := g))) (i : Fin g) :
    φ (spDelta i) = ∑ k ∈ Finset.Ici i, φ ((spRootSystem g).coroot (spSimpleIdx k)) := by
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    rw [← Finset.Ioi_insert, Finset.sum_insert (by simp)]
    by_cases h : (i : ℕ) + 1 < g
    · have h₁ : Finset.Ioi i = Finset.Ici (⟨i + 1, h⟩ : Fin g) := by
        ext k
        simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.le_def]
        omega
      rw [coroot_spSimpleIdx_of_lt i h, map_sub, h₁, ← ih ⟨i + 1, h⟩ (Fin.lt_def.mpr (by simp))]
      ring1
    · have h₁ : Finset.Ioi i = ∅ := by
        ext k
        simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false]
        omega
      rw [coroot_spSimpleIdx_of_not_lt i h, h₁, Finset.sum_empty, add_zero]

lemma apply_coroot_eq (φ : Dual ℂ (spCartan (g := g))) (i : (spCartan (g := g)).root) :
    (spRootSystem g).coroot' i φ = φ ((spRootSystem g).coroot i) :=
  rootSystem_coroot'_apply i φ

/-- **The Weyl vector is `(g, g - 1, …, 1)`.** -/
lemma weylVector_spDelta (i : Fin g) :
    weylVector (spRootSystem g) spBase (spDelta i) = ((g - i : ℕ) : ℂ) := by
  rw [apply_spDelta_eq_sum]
  have h₁ (k : Fin g) :
      weylVector (spRootSystem g) spBase ((spRootSystem g).coroot (spSimpleIdx k)) = 1 := by
    rw [← apply_coroot_eq]
    exact coroot'_weylVector _ _ (mem_spBase_support.mpr ⟨k, rfl⟩)
  rw [Finset.sum_congr rfl fun k _ ↦ h₁ k]
  simp

/-- **A dominant integral weight is a partition with at most `g` parts.** -/
lemma exists_apply_spDelta_eq_highestWeight {φ : Dual ℂ (spCartan (g := g))}
    (hφ : IsDominantIntegral spBase φ) :
    ∃ c : Fin g → ℕ, ∀ i, φ (spDelta i) = (highestWeight c i : ℂ) := by
  have h₁ (k : Fin g) : ∃ n : ℕ, φ ((spRootSystem g).coroot (spSimpleIdx k)) = (n : ℂ) :=
    isDominantIntegral_iff.mp hφ _ (mem_spBase_support.mpr ⟨k, rfl⟩)
  choose c hc using h₁
  refine ⟨c, fun i ↦ ?_⟩
  rw [apply_spDelta_eq_sum, highestWeight, Nat.cast_sum]
  exact Finset.sum_congr rfl fun k _ ↦ hc k

/-- The height of an index in the flag `e₁, …, e_g, ē_g, …, ē₁`, where `e₁` is the highest. -/
def spHeight : Fin g ⊕ Fin g → ℤ :=
  Sum.elim (fun i ↦ ((g - i : ℕ) : ℤ)) fun i ↦ -((g - i : ℕ) : ℤ)

lemma spHeight_swap (a : Fin g ⊕ Fin g) : spHeight a.swap = -spHeight a := by
  rcases a with i | i <;> simp [spHeight]

lemma spHeight_injective : Function.Injective (spHeight (g := g)) := by
  rintro (i | i) (j | j) h
  all_goals simp only [spHeight, Sum.elim_inl, Sum.elim_inr] at h
  · have h₁ : (i : ℕ) = j := by
      omega
    rw [Fin.ext h₁]
  · omega
  · omega
  · have h₁ : (i : ℕ) = j := by
      omega
    rw [Fin.ext h₁]

/-- The element `diag(g, …, 1, -g, …, -1)` of the Cartan subalgebra. -/
noncomputable def spRegular : spCartan (g := g) :=
  ⟨spDiag fun i ↦ ((g - i : ℕ) : ℂ), spDiag_mem_spCartan _⟩

lemma spRootForm_spRegular (a b : Fin g ⊕ Fin g) :
    spRootForm a b spRegular = ((spHeight a - spHeight b : ℤ) : ℂ) := by
  rw [spRegular, spRootForm_spDiag]
  rcases a with i | i <;> rcases b with j | j <;> simp [spHeight, spValue_inl, spValue_inr]

lemma exists_natCast_of_mem_posRootCone {φ : Dual ℂ (spCartan (g := g))}
    (hφ : φ ∈ posRootCone (spRootSystem g) spBase) : ∃ n : ℕ, φ spRegular = n := by
  induction hφ using AddSubmonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, hi, rfl⟩
    rcases mem_spBase_support.mp hi with ⟨k, rfl⟩
    by_cases h : (k : ℕ) + 1 < g
    · refine ⟨1, ?_⟩
      rw [root_spSimpleIdx_of_lt k h, ← spEps_inl, ← spEps_inl]
      refine (spRootForm_spRegular (.inl k) (.inl ⟨k + 1, h⟩)).trans ?_
      have h₁ : spHeight (.inl k) - spHeight (.inl ⟨k + 1, h⟩ : Fin g ⊕ Fin g) = 1 := by
        simp only [spHeight, Sum.elim_inl]
        omega
      rw [h₁]
      simp
    · refine ⟨2, ?_⟩
      have h₁ : spHeight (.inl k) - spHeight (.inr k : Fin g ⊕ Fin g) = 2 := by
        simp only [spHeight, Sum.elim_inl, Sum.elim_inr]
        omega
      rw [root_spSimpleIdx_of_not_lt k h]
      have h₂ : spEpsilon k + spEpsilon k = spRootForm (.inl k) (.inr k) := by
        rw [spRootForm, spEps_inl, spEps_inr, sub_neg_eq_add]
      rw [h₂, spRootForm_spRegular, h₁]
      simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨m, hm⟩
    rcases hy with ⟨n, hn⟩
    exact ⟨m + n, by rw [LinearMap.add_apply, hm, hn, Nat.cast_add]⟩

lemma spHeight_lt_of_mem_posRoots {i : (spCartan (g := g)).root}
    (hi : i ∈ posRoots (spRootSystem g) spBase) {a b : Fin g ⊕ Fin g} (hab : a ≠ b)
    (h : (spRootSystem g).root i = spRootForm a b) : spHeight b < spHeight a := by
  have h₁ : (spRootSystem g).root i ∈ posRootCone (spRootSystem g) spBase :=
    root_mem_posRootCone_of_mem_posRoots (spRootSystem g) spBase hi
  rw [h] at h₁
  rcases exists_natCast_of_mem_posRootCone h₁ with ⟨n, hn⟩
  rw [spRootForm_spRegular] at hn
  have h₂ : spHeight a - spHeight b = n := by
    exact_mod_cast hn
  have h₃ : spHeight b ≠ spHeight a := fun h₄ ↦ hab (spHeight_injective h₄).symm
  omega

/-- **To be a highest weight vector, it is enough to be killed by the root vectors of the positive
roots.** -/
lemma isHighestWeightVector_of_spRootVector {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule (Symplectic.sp (Fin g) ℂ) M] [LieModule ℂ (Symplectic.sp (Fin g) ℂ) M]
    {lam : Dual ℂ (spCartan (g := g))} {v : M} (hv : v ≠ 0)
    (hH : ∀ x : spCartan (g := g), ⁅(x : Symplectic.sp (Fin g) ℂ), v⁆ = lam x • v)
    (hpos : ∀ a b : Fin g ⊕ Fin g, a ≠ b → spHeight b < spHeight a → ⁅spRootVector a b, v⁆ = 0) :
    IsHighestWeightVector spBase lam v := by
  refine isHighestWeightVector_iff_forall_rootSpace.mpr ⟨hv, hH, fun i hi x hx ↦ ?_⟩
  have h₀ : i.1.IsNonZero := spCartan.isNonZero_coe_root i
  rcases exists_eq_spRootForm i.1 h₀ with ⟨a, b, hab, h₁⟩
  have h₂ : (spRootSystem g).root i = spRootForm a b :=
    LinearMap.ext fun y ↦ congrFun h₁ y
  have h₃ : spHeight b < spHeight a := spHeight_lt_of_mem_posRoots hi hab h₂
  have h₄ : spRootVector a b ∈ rootSpace (spCartan (g := g)) (i.1 : spCartan (g := g) → ℂ) := by
    rw [h₁]
    exact spRootVector_mem_rootSpace a b
  have h₅ : Module.finrank ℂ (rootSpace (spCartan (g := g)) (i.1 : spCartan (g := g) → ℂ)) = 1 :=
    IsKilling.finrank_rootSpace_eq_one i.1 h₀
  have h₆ :
      (⟨spRootVector a b, h₄⟩ : rootSpace (spCartan (g := g)) (i.1 : spCartan (g := g) → ℂ)) ≠ 0 :=
    fun h₇ ↦ spRootVector_ne_zero hab (congrArg Subtype.val h₇)
  rcases (finrank_eq_one_iff_of_nonzero' _ h₆).mp h₅ ⟨x, hx⟩ with ⟨c, hc⟩
  have h₇ : x = c • spRootVector a b := (congrArg Subtype.val hc).symm
  rw [h₇, smul_lie, hpos a b hab h₃, smul_zero]

end SatoTateGroup
