import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CoefficientField
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.NumberTheory.HeckeRing.LinearExtension
import TauCeti.NumberTheory.HeckeRing.Multiplicity.Handedness

/-!
# The product of the Hecke ring as a sum over pairs of right cosets

Shimura's multiplicity `m(Γ₁g₁Γ₂, Γ₂g₂Γ₃; Γ₁dΓ₃)`, the structure constant of the Hecke ring, is
defined by Tau Ceti through the *left* coset decompositions `Γ₁g₁Γ₂ = ⊔ᵢ σᵢg₁Γ₂`: it counts the
pairs `(i, j)` with `σᵢg₁τⱼg₂Γ₃ = dΓ₃`. Counted with the *right* coset decompositions it is the
multiplicity `m(Γ₃g₂⁻¹Γ₂, Γ₂g₁⁻¹Γ₁; Γ₃d⁻¹Γ₁)` (Tau Ceti's
`DoubleCoset.card_pairs_mem_rightCoset_eq_multiplicity`). The two are equal: the first counts the
left cosets `aΓ₂ ⊆ Γ₁g₁Γ₂` with `a⁻¹d ∈ Γ₂g₂Γ₃`, the second the left cosets `cΓ₂ ⊆ Γ₃g₂⁻¹Γ₂` with
`dc ∈ Γ₁g₁Γ₂`, and `aΓ₂ ↦ d⁻¹aΓ₂` matches them. (Tau Ceti's `HeckeSlash/Composition.lean` records
the two counts as different; they run over the two degrees of a double coset, which can differ,
but the counts themselves agree.)

So for a Hecke pair `(Γ, Δ)` and a function `f` on the group with `f(γx) = f(x)` for `γ ∈ Γ`, the
sum of `f` over the products `aᵥb_w` of the right coset representatives of two double cosets
`D₁ = ⊔ᵥ Γaᵥ` and `D₂ = ⊔_w Γb_w` is `∑_D m(D₁, D₂; D) ∑_{Γx ⊆ D} f(x)`: Shimura's product formula,
read through any function of the right cosets. For the slash operator this says that the Hecke
operators of a Hecke pair `(Γ, Δ)` of `GSp(2g, ℚ)⁺` compose as the Hecke ring multiplies, so the
eigenvalues of a Hecke eigenform form a ring homomorphism on the Hecke ring.

The fibre count over the double cosets follows Tau Ceti's `HeckeRing/GL2/PairCoset.lean` and the
multiplicity-weighted composite of `HeckeSlash/Composition.lean`, which are stated for `GL(2, ℚ)`
only; here they hold in any group.

## Main definitions

* `HeckeCoset.rightCosetSum`: the sum `∑_{Γx ⊆ D} f(x)` over the right cosets of a double coset.
* `HeckeCoset.rightCosetSumLinear`: its linear extension to the Hecke ring.
* `SiegelUpperHalfSpace.IsHeckeEigenform.eigencharacter`: the eigenvalues of a Hecke eigenform,
  as a ring homomorphism on the Hecke ring.

## Main results

* `DoubleCoset.multiplicity_eq_multiplicity_inv`: Shimura's multiplicity counted with left cosets
  equals the one counted with right cosets.
* `HeckeCoset.rightCosetSumLinear_single_mul_single`: the product formula
  `∑_{v, w} f(aᵥb_w) = ∑_D m(D₁, D₂; D) ∑_{Γx ⊆ D} f(x)`.
* `SiegelUpperHalfSpace.heckeAlgebraActionOf_mul`: the Hecke algebra of a Hecke pair of
  `GSp(2g, ℚ)⁺` acts on invariant functions as an anti-homomorphism (the slash operator being a
  right action), `T(xy) = T(y) T(x)`.
* `SiegelUpperHalfSpace.IsHeckeEigenform.heckeAlgebraActionOf_apply`: a Hecke eigenform is an
  eigenvector of every element of the Hecke algebra, with eigenvalue its eigencharacter.
-/

open DoubleCoset Finset Module

open scoped Pointwise

namespace DoubleCoset

variable {G : Type*} [Group G] {Γ₁ Γ₂ Γ₃ : Subgroup G} (g : G)

private lemma image_mk_out_mul (P : G → Prop) (hP : ∀ a, ∀ γ ∈ Γ₂, P (a * γ) ↔ P a) :
    (fun i : DecompQuotient Γ₁ Γ₂ g ↦ (((i.out : G) * g : G) : G ⧸ Γ₂)) ''
        {i | P ((i.out : G) * g)} =
      (QuotientGroup.mk : G → G ⧸ Γ₂) '' {a | a ∈ doubleCoset g (Γ₁ : Set G) Γ₂ ∧ P a} := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨mem_doubleCoset.mpr ⟨_, i.out.2, 1, one_mem _, (mul_one _).symm⟩, hi⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hPa⟩, rfl⟩
    rw [doubleCoset_eq_iUnion_leftCosets, Set.mem_iUnion] at ha
    rcases ha with ⟨i, hi⟩
    rw [mem_leftCoset_iff] at hi
    refine ⟨i, (hP _ _ hi).mp ?_, QuotientGroup.eq.mpr hi⟩
    rwa [mul_inv_cancel_left]

/-- **Shimura's multiplicity counted with left cosets equals the one counted with right
cosets**: `m(Γ₁g₁Γ₂, Γ₂g₂Γ₃; Γ₁dΓ₃) = m(Γ₃g₂⁻¹Γ₂, Γ₂g₁⁻¹Γ₁; Γ₃d⁻¹Γ₁)`. The left side counts the
left cosets `aΓ₂ ⊆ Γ₁g₁Γ₂` with `a⁻¹d ∈ Γ₂g₂Γ₃`, the right side the left cosets
`cΓ₂ ⊆ Γ₃g₂⁻¹Γ₂` with `dc ∈ Γ₁g₁Γ₂`, and `aΓ₂ ↦ d⁻¹aΓ₂` matches them. -/
lemma multiplicity_eq_multiplicity_inv (h d : G) [Finite (DecompQuotient Γ₁ Γ₂ g)]
    [Finite (DecompQuotient Γ₂ Γ₃ h)] [Finite (DecompQuotient Γ₃ Γ₂ h⁻¹)]
    [Finite (DecompQuotient Γ₂ Γ₁ g⁻¹)] :
    multiplicity Γ₁ Γ₂ Γ₃ g h d = multiplicity Γ₃ Γ₂ Γ₁ h⁻¹ g⁻¹ d⁻¹ := by
  rw [multiplicity_eq_card_filter, multiplicity_eq_card_filter,
    ← Nat.card_image_of_injective (mk_out_mul_injective Γ₁ Γ₂ g),
    ← Nat.card_image_of_injective (mk_out_mul_injective Γ₃ Γ₂ h⁻¹),
    image_mk_out_mul g (fun a ↦ a⁻¹ * d ∈ doubleCoset h (Γ₂ : Set G) Γ₃) fun a γ hγ ↦ by
      rw [mul_inv_rev, mul_assoc, mul_mem_doubleCoset_iff (inv_mem hγ)],
    image_mk_out_mul h⁻¹ (fun c ↦ c⁻¹ * d⁻¹ ∈ doubleCoset g⁻¹ (Γ₂ : Set G) Γ₁) fun c γ hγ ↦ by
      rw [mul_inv_rev, mul_assoc, mul_mem_doubleCoset_iff (inv_mem hγ)],
    ← Nat.card_image_of_injective (MulAction.injective d⁻¹), Set.image_image]
  have e : (fun x : G ↦ d⁻¹ • (x : G ⧸ Γ₂)) = QuotientGroup.mk ∘ (d⁻¹ * ·) :=
    rfl
  rw [e, Set.image_comp, Set.image_mul_left, inv_inv]
  congr 3
  ext c
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mul_inv_rev, inv_mul_cancel_right]
  rw [← inv_mem_doubleCoset_inv_iff (x := d * c), ← inv_mem_doubleCoset_inv_iff (x := c⁻¹), inv_inv,
    mul_inv_rev, and_comm]

end DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} {Γ : Subgroup G}

instance : Subsingleton (DecompQuotient Γ Γ ((1 : HeckeCoset Δ Γ Γ).out : G)⁻¹) :=
  subsingleton_decompQuotient_of_mem (inv_mem rep_one_mem)

lemma rightCosetRep_one_mem (v : DecompQuotient Γ Γ ((1 : HeckeCoset Δ Γ Γ).out : G)⁻¹) :
    rightCosetRep (1 : HeckeCoset Δ Γ Γ) v ∈ Γ := by
  rw [rightCosetRep_def]
  exact mul_mem rep_one_mem (inv_mem (Quotient.out v).2)

variable [IsHeckeTriple Δ Γ Γ] (D D₁ D₂ : HeckeCoset Δ Γ Γ) {M : Type*} [AddCommMonoid M]
  (f : G → M)

attribute [local instance] Fintype.ofFinite

/-- The **sum over the right cosets** `∑_{Γx ⊆ D} f(x)` of a double coset `D = ⊔ᵥ Γaᵥ`, at the
chosen representatives `aᵥ` (`DoubleCoset.rightCosetRep`); it does not depend on them when
`f(γx) = f(x)` for `γ ∈ Γ`. -/
noncomputable def rightCosetSum : M :=
  ∑ v : DecompQuotient Γ Γ (D.out : G)⁻¹, f (rightCosetRep D v)

/-- The double coset `Γ(aᵥb_w)Γ` of the product of the right coset representatives `aᵥ` of `D₁`
and `b_w` of `D₂`, over which the sum of a product of two right coset sums is regrouped. -/
noncomputable def pairRightCoset
    (q : DecompQuotient Γ Γ (D₁.out : G)⁻¹ × DecompQuotient Γ Γ (D₂.out : G)⁻¹) :
    HeckeCoset Δ Γ Γ :=
  mk Γ Γ ⟨rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2,
    mul_mem (rightCosetRep_mem D₁ D₁.out.2 (IsHeckeTriple.right_le (H₁ := Γ)) q.1)
      (rightCosetRep_mem D₂ D₂.out.2 (IsHeckeTriple.right_le (H₁ := Γ)) q.2)⟩

variable {D D₁ D₂} in
lemma pairRightCoset_eq_iff
    {q : DecompQuotient Γ Γ (D₁.out : G)⁻¹ × DecompQuotient Γ Γ (D₂.out : G)⁻¹} :
    pairRightCoset D₁ D₂ q = D ↔
      rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2 ∈ doubleCoset (D.out : G) (Γ : Set G) Γ := by
  constructor
  · intro h
    have hD : doubleCoset (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) (Γ : Set G) Γ =
        doubleCoset (D.out : G) (Γ : Set G) Γ :=
      eq_iff.mp (h.trans (mk_rep D).symm)
    exact hD ▸ mem_doubleCoset_self _ _ _
  · intro h
    rw [← mk_rep D]
    exact eq_iff.mpr (doubleCoset_eq_of_mem h)

lemma card_pairRightCoset_fiber {x : G} (hx : x ∈ doubleCoset (D.out : G) (Γ : Set G) Γ) :
    Nat.card {i : {q // pairRightCoset D₁ D₂ q = D} //
      MulOpposite.op (rightCosetRep D₁ i.1.1 * rightCosetRep D₂ i.1.2) • (Γ : Set G) =
        MulOpposite.op x • (Γ : Set G)} =
      multiplicity Γ Γ Γ (D₁.out : G) (D₂.out : G) (D.out : G) := by
  have hiff (y : G) : MulOpposite.op y • (Γ : Set G) = MulOpposite.op x • (Γ : Set G) ↔
      y ∈ MulOpposite.op x • (Γ : Set G) := by
    rw [rightCoset_eq_iff, mem_rightCoset_iff, ← inv_mem_iff, mul_inv_rev, inv_inv, SetLike.mem_coe]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtype (p := fun q ↦ pairRightCoset D₁ D₂ q = D)
      (q := fun q ↦ MulOpposite.op (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) •
        (Γ : Set G) = MulOpposite.op x • (Γ : Set G))
      fun {q} hq ↦ pairRightCoset_eq_iff.mpr <| by
        rw [← doubleCoset_eq_of_mem hx]
        exact mem_doubleCoset.mpr ⟨_, (mem_rightCoset_iff x).mp ((hiff _).mp hq), 1, one_mem _,
          by group⟩),
    multiplicity_eq_multiplicity_inv,
    ← card_pairs_mem_rightCoset_eq_multiplicity Γ Γ Γ (D₁.out : G) (D₂.out : G) (D.out : G)]
  simp only [hiff]
  exact card_pairs_mem_rightCoset_congr Γ Γ Γ (D₁.out : G) (D₂.out : G) hx

variable {f} in
lemma sum_eq_nsmul_rightCosetSum (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) {ι : Type*} [Fintype ι]
    (a : ι → G) (m : ℕ) (hmem : ∀ i, a i ∈ doubleCoset (D.out : G) (Γ : Set G) Γ)
    (hcard : ∀ x ∈ doubleCoset (D.out : G) (Γ : Set G) Γ,
      Nat.card {i // MulOpposite.op (a i) • (Γ : Set G) = MulOpposite.op x • (Γ : Set G)} = m) :
    ∑ i, f (a i) = m • rightCosetSum D f := by
  classical
  have heq {x y : G} (h : MulOpposite.op x • (Γ : Set G) = MulOpposite.op y • (Γ : Set G)) :
      f x = f y := by
    rw [← hf _ ((rightCoset_eq_iff Γ).mp h) x, inv_mul_cancel_right]
  choose g hg using fun i ↦ exists_rightCosetRep_smul_eq D (hmem i)
  rw [rightCosetSum, Finset.smul_sum, ← Finset.sum_fiberwise Finset.univ g fun i ↦ f (a i)]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finset.sum_congr rfl fun i hi ↦ heq ((Finset.mem_filter.mp hi).2 ▸ hg i), Finset.sum_const,
    card_filter_eq_of_rightCosetRep_smul_eq D hcard hg v]

open scoped Classical in
variable {f} in
lemma sum_mul_rightCosetRep (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) :
    ∑ q : DecompQuotient Γ Γ (D₁.out : G)⁻¹ × DecompQuotient Γ Γ (D₂.out : G)⁻¹,
        f (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) =
      ∑ D ∈ univ.image (pairRightCoset D₁ D₂),
        multiplicity Γ Γ Γ (D₁.out : G) (D₂.out : G) (D.out : G) • rightCosetSum D f := by
  rw [TauCeti.sum_eq_sum_image_fiber (pairRightCoset D₁ D₂)]
  exact sum_congr rfl fun D _ ↦ sum_eq_nsmul_rightCosetSum D hf _ _
    (fun i ↦ pairRightCoset_eq_iff.mp i.2) fun _ hx ↦ card_pairRightCoset_fiber D D₁ D₂ hx

variable (k : Type*) [CommSemiring k] [Module k M]

/-- The **linear extension** `∑_D c_D D ↦ ∑_D c_D ∑_{Γx ⊆ D} f(x)` of
`HeckeCoset.rightCosetSum` to the Hecke ring `𝓗(Γ, Δ)` with coefficients in `k`. -/
noncomputable def rightCosetSumLinear : HeckeRing Δ Γ k →ₗ[k] M :=
  Finsupp.linearCombination k fun D ↦ rightCosetSum D f

lemma rightCosetSumLinear_single (c : k) :
    rightCosetSumLinear f k (HeckeCosetModule.single k D c) = c • rightCosetSum D f :=
  Finsupp.linearCombination_single k c D

/-- **Shimura's product formula, read through a function of the right cosets**: for `f` with
`f(γx) = f(x)` for `γ ∈ Γ`, the linear extension of `∑_{Γx ⊆ D} f(x)` takes the product
`D₁ D₂ = ∑_D m(D₁, D₂; D) D` of two double cosets `D₁ = ⊔ᵥ Γaᵥ` and `D₂ = ⊔_w Γb_w` to the sum
`∑_{v, w} f(aᵥ b_w)` over the pairs of right coset representatives. -/
lemma rightCosetSumLinear_single_mul_single (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) :
    rightCosetSumLinear f k (HeckeCosetModule.single k D₁ 1 * HeckeCosetModule.single k D₂ 1) =
      ∑ q : DecompQuotient Γ Γ (D₁.out : G)⁻¹ × DecompQuotient Γ Γ (D₂.out : G)⁻¹,
        f (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) := by
  classical
  have hm₁ (D : HeckeCoset Δ Γ Γ) : HeckeCosetModule.structureConstants k Γ Γ Γ D₁.rep D₂.rep D •
      rightCosetSum D f = multiplicity Γ Γ Γ (D₁.out : G) (D₂.out : G) (D.out : G) •
        rightCosetSum D f := by
    rw [HeckeCosetModule.structureConstants_apply, Nat.cast_smul_eq_nsmul]
    rfl
  have hm₂ (D : HeckeCoset Δ Γ Γ) (hD : D ∉ univ.image (pairRightCoset D₁ D₂)) :
      multiplicity Γ Γ Γ (D₁.out : G) (D₂.out : G) (D.out : G) = 0 := by
    by_contra h
    rw [← card_pairRightCoset_fiber D D₁ D₂ (mem_doubleCoset_self _ _ _)] at h
    rcases Nat.card_ne_zero.mp h with ⟨⟨⟨⟨q, hq⟩, -⟩⟩, -⟩
    exact hD (hq ▸ mem_image_of_mem _ (mem_univ q))
  have hlc : rightCosetSumLinear f k (HeckeCosetModule.structureConstants k Γ Γ Γ D₁.rep D₂.rep) =
      ∑ D ∈ (HeckeCosetModule.structureConstants k Γ Γ Γ D₁.rep D₂.rep).support,
        HeckeCosetModule.structureConstants k Γ Γ Γ D₁.rep D₂.rep D • rightCosetSum D f :=
    (Finsupp.linearCombination_apply k _).trans (HeckeCosetModule.sum_def _ _)
  rw [sum_mul_rightCosetRep D₁ D₂ hf, HeckeCosetModule.single_mul_single, one_smul, one_smul, hlc]
  refine (sum_subset (subset_union_left (s₂ := univ.image (pairRightCoset D₁ D₂)))
    fun D _ hD ↦ ?_).trans ((sum_congr rfl fun D _ ↦ hm₁ D).trans
      (sum_subset subset_union_right fun D _ hD ↦ ?_).symm)
  · rw [HeckeCosetModule.notMem_support_iff.mp hD, zero_smul]
  · rw [hm₂ D hD, zero_smul]

end HeckeCoset

namespace SiegelUpperHalfSpace

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) ℂ) V) {Δ : Submonoid (GL (Fin n ⊕ Fin n) ℚ)}
  [Fact (Δ ≤ gspPlusGL (Fin n))] {Γ : Subgroup (GL (Fin n ⊕ Fin n) ℚ)} [IsHeckeTriple Δ Γ Γ]
  (F : slashInvariantsOf ρ Δ Γ)

attribute [local instance] Fintype.ofFinite

open scoped Classical in
/-- The slash `F ∣_ρ x` of a `Γ`-invariant function `F` by the elements `x` of `Δ`, and `0` off
`Δ`; it only depends on the right coset `Γx`. -/
noncomputable def slashOn (x : GL (Fin n ⊕ Fin n) ℚ) : SiegelUpperHalfSpace (Fin n) → V :=
  if hx : x ∈ Δ then heckeMonoidSlash ρ ⟨x, hx⟩ F else 0

lemma slashOn_of_mem (x : Δ) : slashOn ρ F x = heckeMonoidSlash ρ x F :=
  dite_eq_left x.2

variable [NeZero n]

lemma slashOn_mul_left {γ : GL (Fin n ⊕ Fin n) ℚ} (hγ : γ ∈ Γ) (x : GL (Fin n ⊕ Fin n) ℚ) :
    slashOn ρ F (γ * x) = slashOn ρ F x := by
  have hγΔ : γ ∈ Δ := IsHeckeTriple.mem_of_mem_left Γ hγ
  by_cases hx : x ∈ Δ
  · have h : heckeMonoidSlash ρ (⟨γ, hγΔ⟩ * ⟨x, hx⟩ : Δ) F = heckeMonoidSlash ρ ⟨x, hx⟩ F := by
      rw [heckeMonoidSlash_mul, F.2 γ hγ]
    rw [slashOn, dite_eq_left (mul_mem hγΔ hx), slashOn, dite_eq_left hx, ← h]
    rfl
  · have hγx : γ * x ∉ Δ := fun h ↦ hx <| by
      simpa using mul_mem (IsHeckeTriple.mem_of_mem_left Γ (inv_mem hγ)) h
    rw [slashOn, dite_eq_right hγx, slashOn, dite_eq_right hx]

lemma coe_heckeAlgebraActionOf_apply (T : HeckeRing Δ Γ ℂ) :
    (heckeAlgebraActionOf ρ Δ Γ T F : SiegelUpperHalfSpace (Fin n) → V) =
      HeckeCoset.rightCosetSumLinear (slashOn ρ F) ℂ T := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => simp
  | hadd T₁ T₂ h₁ h₂ => rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add, h₁, h₂]
  | hsingle D c =>
    rw [heckeAlgebraActionOf_single, HeckeCoset.rightCosetSumLinear_single, LinearMap.smul_apply,
      Submodule.coe_smul, coe_heckeOperator, HeckeCoset.rightCosetSum]
    congr 1
    exact Finset.sum_congr rfl fun v _ ↦ (slashOn_of_mem ρ F (heckeRep D v)).symm

lemma heckeOperator_heckeOperator (D₁ D₂ : HeckeCoset Δ Γ Γ) :
    (heckeOperator ρ D₂ (heckeOperator ρ D₁ F) : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ q : DecompQuotient Γ Γ (D₁.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ×
          DecompQuotient Γ Γ (D₂.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹,
        slashOn ρ F (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) := by
  rw [coe_heckeOperator, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [coe_heckeOperator, map_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← heckeMonoidSlash_mul]
  exact (slashOn_of_mem ρ F (heckeRep D₁ v * heckeRep D₂ w)).symm

/-- **The Hecke algebra acts on invariant functions as an anti-homomorphism**: for a Hecke pair
`(Γ, Δ)` of `GSp(2g, ℚ)⁺`, such as `Sp(2g, ℤ)` with `S` or `S_p`, `T(xy) = T(y) T(x)`, the slash
operator being a right action: `(F ∣ D₁) ∣ D₂ = F ∣ D₁D₂`. -/
lemma heckeAlgebraActionOf_mul (T₁ T₂ : HeckeRing Δ Γ ℂ) : heckeAlgebraActionOf ρ Δ Γ (T₁ * T₂) =
    heckeAlgebraActionOf ρ Δ Γ T₂ * heckeAlgebraActionOf ρ Δ Γ T₁ :=
  (heckeAlgebraActionOf ρ Δ Γ).map_mul_reverse_of_basis (fun D₁ D₂ ↦ LinearMap.ext fun F ↦
    Subtype.ext <| by
      rw [coe_heckeAlgebraActionOf_apply, HeckeCoset.rightCosetSumLinear_single_mul_single D₁ D₂ _ ℂ
          fun γ hγ x ↦ slashOn_mul_left ρ F hγ x, End.mul_apply,
        heckeAlgebraActionOf_single, heckeAlgebraActionOf_single, one_smul, one_smul,
        heckeOperator_heckeOperator]) T₁ T₂

lemma heckeOperator_one : heckeOperator ρ (1 : HeckeCoset Δ Γ Γ) F = F := by
  rcases (inferInstance : Nonempty (DecompQuotient Γ Γ
    ((1 : HeckeCoset Δ Γ Γ).out : GL (Fin n ⊕ Fin n) ℚ)⁻¹)) with ⟨v⟩
  exact Subtype.ext <| (coe_heckeOperator ρ 1 F).trans <|
    (Fintype.sum_subsingleton _ v).trans (F.2 _ (HeckeCoset.rightCosetRep_one_mem v))

variable {ρ F} (hF : IsHeckeEigenform ρ F)

/-- The linear extension `∑ c_D D ↦ ∑ c_D λ_F(D)` of the Hecke eigenvalues of `F`. -/
private noncomputable def eigenvalueLinear : HeckeRing Δ Γ ℂ →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ hF.eigenvalue

private lemma eigenvalueLinear_single (D : HeckeCoset Δ Γ Γ) (c : ℂ) :
    eigenvalueLinear hF (HeckeCosetModule.single ℂ D c) = c * hF.eigenvalue D :=
  Finsupp.linearCombination_single ℂ c D

private lemma heckeAlgebraActionOf_eq_eigenvalueLinear (T : HeckeRing Δ Γ ℂ) :
    heckeAlgebraActionOf ρ Δ Γ T F = eigenvalueLinear hF T • F := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => rw [map_zero, map_zero, LinearMap.zero_apply, zero_smul]
  | hadd x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, add_smul]
  | hsingle D c =>
    rw [heckeAlgebraActionOf_single, LinearMap.smul_apply, hF.heckeOperator_eq,
      eigenvalueLinear_single, smul_smul]

/-- The **eigencharacter** `λ_F : 𝓗(Γ, Δ) → ℂ` of a Hecke eigenform `F`: the linear extension
`∑ c_D D ↦ ∑ c_D λ_F(D)` of its Hecke eigenvalues `F ∣_ρ D = λ_F(D) F`
(`SiegelUpperHalfSpace.IsHeckeEigenform.eigenvalue`), a ring homomorphism since the Hecke algebra
acts as an anti-homomorphism (`SiegelUpperHalfSpace.heckeAlgebraActionOf_mul`). -/
noncomputable def IsHeckeEigenform.eigencharacter : HeckeRing Δ Γ ℂ →+* ℂ where
  toFun := eigenvalueLinear hF
  map_one' := by
    rw [HeckeCosetModule.one_def, eigenvalueLinear_single, one_mul]
    exact (hF.eq_eigenvalue 1 (by rw [heckeOperator_one, one_smul])).symm
  map_mul' T₁ T₂ := smul_left_injective ℂ hF.2.1 <| by
    dsimp only
    rw [← heckeAlgebraActionOf_eq_eigenvalueLinear, heckeAlgebraActionOf_mul, End.mul_apply,
      heckeAlgebraActionOf_eq_eigenvalueLinear hF T₁, map_smul,
      heckeAlgebraActionOf_eq_eigenvalueLinear hF T₂, smul_smul]
  map_zero' := map_zero _
  map_add' := map_add _

/-- **A Hecke eigenform is an eigenvector of the whole Hecke algebra**: `F ∣_ρ T = λ_F(T) F` for
every `T ∈ 𝓗(Γ, Δ)`, with `λ_F` its eigencharacter. -/
lemma IsHeckeEigenform.heckeAlgebraActionOf_apply (T : HeckeRing Δ Γ ℂ) :
    heckeAlgebraActionOf ρ Δ Γ T F = hF.eigencharacter T • F :=
  heckeAlgebraActionOf_eq_eigenvalueLinear hF T

lemma IsHeckeEigenform.eigencharacter_single (D : HeckeCoset Δ Γ Γ) (c : ℂ) :
    hF.eigencharacter (HeckeCosetModule.single ℂ D c) = c * hF.eigenvalue D :=
  Finsupp.linearCombination_single ℂ c D

end SiegelUpperHalfSpace
