import LeanBridge.ForMathlib.GroupTheory.ChiefSeries
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.JordanHolder

/-!
# The Jordan–Hölder theorems for chief series and composition series

The chief factors and the composition factors of a group (LMFDB `group.chief_series`) do not
depend on the chosen series: two chief series of a group, and two composition series, have the same
length and the same factors up to isomorphism and permutation. Both are instances of Mathlib's
Jordan–Hölder theorem `CompositionSeries.jordan_holder` for a `JordanHolderLattice`:

* the normal subgroups of `G` form a modular lattice (`Subgroup.NormalLattice`, the Dedekind law
  `(H ⊔ N) ⊓ K = H ⊔ (N ⊓ K)` for `H ≤ K` and `N` normal), hence a Jordan–Hölder lattice in which
  `N` is maximal in `M` when `M` covers `N`; a chief series (`Subgroup.NormalSeries.IsChief`, each
  `Nᵢ₊₁ / Nᵢ` minimal normal in `G / Nᵢ`) is a composition series of this lattice;
* the Jordan–Hölder lattice `Subgroup.jordanHolderLattice` on `Subgroup G` declares `H` maximal in
  `K` when `H` is normal in `K` with simple quotient, so that its composition series are the
  composition series of `G` (`Subgroup.SubnormalSeries.IsComposition`). It is not an instance, since
  for a commutative group it would override Mathlib's instance on the modular lattice `Subgroup G`.

In both cases the equivalence of intervals of Mathlib's theorem is turned into isomorphism of the
factor groups by the second isomorphism theorem.

## Main definitions

* `Subgroup.NormalLattice` (LMFDB `group.chief_series`): the lattice of normal subgroups.
* `Subgroup.jordanHolderLattice` (LMFDB `group.chief_series`): the Jordan–Hölder lattice of the
  subgroups, whose composition series are the composition series of the group.

## Main results

* `Subgroup.NormalSeries.IsChief.exists_equiv_nonempty_mulEquiv_factor` (LMFDB
  `group.chief_series`): the Jordan–Hölder theorem for chief series.
* `Subgroup.SubnormalSeries.IsComposition.exists_equiv_nonempty_mulEquiv_factor` (LMFDB
  `group.chief_series`): the Jordan–Hölder theorem for composition series, so that the composition
  factors of a group are well defined.
-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

variable (G) in
/-- The **lattice of normal subgroups** of `G` (LMFDB `group.chief_series`), ordered by inclusion.
It is modular, and `M` covers `N` in it exactly when `M / N` is a minimal normal subgroup of
`G / N`: its maximal chains from `⊥` to `⊤` are the chief series of `G`. -/
def NormalLattice : Type _ :=
  {N : Subgroup G // N.Normal}

namespace NormalLattice

instance : Lattice (NormalLattice G) :=
  Subtype.lattice (fun _ _ _ _ ↦ inferInstance) fun _ _ _ _ ↦ inferInstance

instance (N : NormalLattice G) : N.1.Normal :=
  N.2

instance : IsModularLattice (NormalLattice G) := by
  refine ⟨fun {x} y {z} hxz g hg ↦ ?_⟩
  have h : g ∈ (x.1 : Set G) * ((y.1 ⊓ z.1 : Subgroup G) : Set G) := by
    rw [mul_inf_assoc _ _ _ hxz, ← mul_normal]
    exact hg
  rcases h with ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_sup ha hb

lemma nonempty_mulEquiv_sup_inf (x y : NormalLattice G) :
    Nonempty ((x ⊔ y).1 ⧸ x.1.subgroupOf (x ⊔ y).1 ≃* y.1 ⧸ (x ⊓ y).1.subgroupOf y.1) := by
  have h (K : Subgroup G) (hK : y.1 ⊔ x.1 = K) :
      Nonempty (K ⧸ x.1.subgroupOf K ≃* y.1 ⧸ (x ⊓ y).1.subgroupOf y.1) := by
    subst hK
    exact ⟨(QuotientGroup.quotientInfEquivProdNormalQuotient y.1 x.1).symm.trans <|
      QuotientGroup.quotientMulEquivOfEq (inf_subgroupOf_right x.1 y.1).symm⟩
  exact h _ (sup_comm y.1 x.1)

end NormalLattice

namespace NormalSeries

variable {s s₁ s₂ : NormalSeries G}

lemma IsChief.covBy (hs : s.IsChief) (i : Fin s.length) :
    (⟨s i.castSucc, s.normal _⟩ : NormalLattice G) ⋖ ⟨s i.succ, s.normal _⟩ := by
  have hle : s i.castSucc ≤ s i.succ := s.le_succ i
  refine ⟨lt_of_le_of_ne hle fun h ↦ (hs i).prop.2 ?_, fun K hNK hKM ↦ ?_⟩
  · exact (congrArg (fun N : NormalLattice G ↦ N.1.map (QuotientGroup.mk' (s i.castSucc))) h).symm
      |>.trans (QuotientGroup.map_mk'_self _)
  · have hNK' : s i.castSucc ≤ K.1 := hNK.le
    have hK : (K.1.map (QuotientGroup.mk' (s i.castSucc))).Normal ∧
        K.1.map (QuotientGroup.mk' (s i.castSucc)) ≠ ⊥ := by
      refine ⟨K.2.map _ (QuotientGroup.mk'_surjective _), fun h ↦ hNK.not_ge ?_⟩
      rw [map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact h
    refine hKM.not_ge <| (map_le_map_iff.mp ((hs i).eq_of_le hK (map_mono hKM.le)).ge).trans ?_
    rw [QuotientGroup.ker_mk']
    exact sup_le le_rfl hNK'

/-- **The Jordan–Hölder theorem for chief series** (LMFDB `group.chief_series`): two chief series of
a group have the same length and, up to a permutation, isomorphic factors `Nᵢ₊₁ / Nᵢ`. -/
lemma IsChief.exists_equiv_nonempty_mulEquiv_factor (h₁ : s₁.IsChief) (h₂ : s₂.IsChief) :
    ∃ e : Fin s₁.length ≃ Fin s₂.length, ∀ i, Nonempty (s₁.factor i ≃* s₂.factor (e i)) := by
  let c₁ : CompositionSeries (NormalLattice G) :=
    ⟨s₁.length, fun i ↦ ⟨s₁ i, s₁.normal i⟩, h₁.covBy⟩
  let c₂ : CompositionSeries (NormalLattice G) :=
    ⟨s₂.length, fun i ↦ ⟨s₂ i, s₂.normal i⟩, h₂.covBy⟩
  rcases CompositionSeries.jordan_holder c₁ c₂
    (Subtype.ext <| s₁.apply_zero.trans s₂.apply_zero.symm)
    (Subtype.ext <| s₁.apply_last.trans s₂.apply_last.symm) with ⟨e, he⟩
  exact ⟨e, fun i ↦ (he i).rel
    (fun p q : NormalLattice G × NormalLattice G ↦
      Nonempty (p.2.1 ⧸ p.1.1.subgroupOf p.2.1 ≃* q.2.1 ⧸ q.1.1.subgroupOf q.2.1))
    ⟨MulEquiv.refl _⟩ (fun ⟨f⟩ ↦ ⟨f.symm⟩) (fun ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩)
    fun _ ↦ NormalLattice.nonempty_mulEquiv_sup_inf _ _⟩

end NormalSeries

variable {H K L x y : Subgroup G}

lemma eq_or_eq_of_isSimpleGroup_quotient [(H.subgroupOf K).Normal]
    [IsSimpleGroup (K ⧸ H.subgroupOf K)] (hHL : H ≤ L) (hLK : L ≤ K)
    (hL : (L.subgroupOf K).Normal) : L = H ∨ L = K := by
  rcases (hL.map _ (QuotientGroup.mk'_surjective (H.subgroupOf K))).eq_bot_or_eq_top with h | h
  · rw [map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    refine .inl <| le_antisymm ?_ hHL
    have h' : (L.subgroupOf K).map K.subtype ≤ (H.subgroupOf K).map K.subtype := map_mono h
    rwa [map_subgroupOf_eq_of_le hLK, map_subgroupOf_eq_of_le (hHL.trans hLK)] at h'
  · refine .inr <| le_antisymm hLK <| subgroupOf_eq_top.mp ?_
    have hle : H.subgroupOf K ≤ L.subgroupOf K := comap_mono hHL
    have h' : ((L.subgroupOf K).map (QuotientGroup.mk' (H.subgroupOf K))).comap
        (QuotientGroup.mk' (H.subgroupOf K)) = (⊤ : Subgroup _).comap (QuotientGroup.mk' _) :=
      congrArg _ h
    rwa [comap_map_eq, comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hle] at h'

lemma lt_of_isSimpleGroup_quotient [(H.subgroupOf K).Normal] [IsSimpleGroup (K ⧸ H.subgroupOf K)]
    (hHK : H ≤ K) : H < K := by
  refine lt_of_le_of_ne hHK fun h ↦ ?_
  subst h
  refine not_subsingleton (H ⧸ H.subgroupOf H) ⟨fun a b ↦ ?_⟩
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  exact QuotientGroup.eq.mpr (mem_subgroupOf.mpr (a⁻¹ * b).2)

lemma normal_inf_subgroupOf_left [hy : (y.subgroupOf (x ⊔ y)).Normal] :
    ((x ⊓ y).subgroupOf x).Normal :=
  (normal_subgroupOf_iff inf_le_left).mpr fun h k hh hk ↦
    mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hh).1) (inv_mem hk),
      (normal_subgroupOf_iff le_sup_right).mp hy h k (mem_inf.mp hh).2 (le_sup_left (a := x) hk)⟩

lemma normal_inf_subgroupOf_right [hx : (x.subgroupOf (x ⊔ y)).Normal] :
    ((x ⊓ y).subgroupOf y).Normal :=
  (normal_subgroupOf_iff inf_le_right).mpr fun h k hh hk ↦ mem_inf.mpr
    ⟨(normal_subgroupOf_iff le_sup_left).mp hx h k (mem_inf.mp hh).1 (le_sup_right (b := y) hk),
      mul_mem (mul_mem hk (mem_inf.mp hh).2) (inv_mem hk)⟩

variable (G) in
/-- The **Jordan–Hölder lattice of the subgroups** of `G` (LMFDB `group.chief_series`), in which `H`
is maximal in `K` when `H` is normal in `K` with simple quotient `K / H`, so that its composition
series are the composition series of `G` (`Subgroup.SubnormalSeries.IsComposition`). It is not an
instance: for a commutative group `G` it would override Mathlib's instance on the modular lattice
`Subgroup G`, in which `H` is maximal in `K` when `K` covers `H`. -/
abbrev jordanHolderLattice : JordanHolderLattice (Subgroup G) where
  IsMaximal H K := H ≤ K ∧ ∃ _ : (H.subgroupOf K).Normal, IsSimpleGroup (K ⧸ H.subgroupOf K)
  lt_of_isMaximal := fun ⟨hHK, _, _⟩ ↦ lt_of_isSimpleGroup_quotient hHK
  sup_eq_of_isMaximal := by
    rintro x y z ⟨hxz, hxn, hxs⟩ ⟨hyz, hyn, hys⟩ hne
    have hn : ((x ⊔ y).subgroupOf z).Normal := by
      rw [subgroupOf_sup hxz hyz]
      infer_instance
    rcases eq_or_eq_of_isSimpleGroup_quotient (H := x) le_sup_left (sup_le hxz hyz) hn with h | h
    · rcases eq_or_eq_of_isSimpleGroup_quotient (H := y) (h ▸ le_sup_right) hxz hxn with h' | h'
      · exact absurd h' hne
      · exact absurd h' (lt_of_isSimpleGroup_quotient (H := x) hxz).ne
    · exact h
  isMaximal_inf_left_of_isMaximal_sup := by
    rintro x y - ⟨-, hyn, hys⟩
    have hle : x ≤ normalizer y :=
      le_sup_left.trans (le_normalizer_of_normal_subgroupOf le_sup_right)
    have hyx : (y.subgroupOf x).Normal := normal_subgroupOf_of_le_normalizer hle
    have hs : IsSimpleGroup (x ⧸ y.subgroupOf x) :=
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient x y hle).isSimpleGroup
    have hn : ((x ⊓ y).subgroupOf x).Normal := normal_inf_subgroupOf_left
    exact ⟨inf_le_left, hn,
      (QuotientGroup.quotientMulEquivOfEq (inf_subgroupOf_left y x)).isSimpleGroup⟩

lemma exists_nonempty_mulEquiv_sup_inf [(x.subgroupOf (x ⊔ y)).Normal] :
    ∃ _ : ((x ⊓ y).subgroupOf y).Normal,
      Nonempty ((x ⊔ y : Subgroup G) ⧸ x.subgroupOf (x ⊔ y) ≃* y ⧸ (x ⊓ y).subgroupOf y) := by
  have hle : y ≤ normalizer x :=
    le_sup_right.trans (le_normalizer_of_normal_subgroupOf le_sup_left)
  have hn : ((x ⊓ y).subgroupOf y).Normal := normal_inf_subgroupOf_right
  have hxy : (x.subgroupOf y).Normal := normal_subgroupOf_of_le_normalizer hle
  have h (K : Subgroup G) (hK : y ⊔ x = K) [(x.subgroupOf K).Normal] :
      Nonempty (K ⧸ x.subgroupOf K ≃* y ⧸ (x ⊓ y).subgroupOf y) := by
    subst hK
    exact ⟨(QuotientGroup.quotientInfEquivProdNormalizerQuotient y x hle).symm.trans <|
      QuotientGroup.quotientMulEquivOfEq (inf_subgroupOf_right x y).symm⟩
  exact ⟨hn, h _ (sup_comm y x)⟩

namespace SubnormalSeries

variable {s₁ s₂ : SubnormalSeries G}

/-- **The Jordan–Hölder theorem for composition series** (LMFDB `group.chief_series`): two
composition series of a group have the same length and, up to a permutation, isomorphic factors, so
that the composition factors of a group, with their multiplicities, are well defined. -/
lemma IsComposition.exists_equiv_nonempty_mulEquiv_factor (h₁ : s₁.IsComposition)
    (h₂ : s₂.IsComposition) :
    ∃ e : Fin s₁.length ≃ Fin s₂.length, ∀ i, Nonempty (s₁.factor i ≃* s₂.factor (e i)) := by
  let _ : JordanHolderLattice (Subgroup G) := jordanHolderLattice G
  let c₁ : CompositionSeries (Subgroup G) :=
    ⟨s₁.length, s₁.toFun, fun i ↦ ⟨s₁.le_succ i, s₁.normal_subgroupOf i, h₁ i⟩⟩
  let c₂ : CompositionSeries (Subgroup G) :=
    ⟨s₂.length, s₂.toFun, fun i ↦ ⟨s₂.le_succ i, s₂.normal_subgroupOf i, h₂ i⟩⟩
  rcases CompositionSeries.jordan_holder c₁ c₂ (s₁.apply_zero.trans s₂.apply_zero.symm)
    (s₁.apply_last.trans s₂.apply_last.symm) with ⟨e, he⟩
  refine ⟨e, fun i ↦ ?_⟩
  rcases (he i).rel (fun p q : Subgroup G × Subgroup G ↦ p = q ∨
      ∃ (_ : (p.1.subgroupOf p.2).Normal) (_ : (q.1.subgroupOf q.2).Normal),
        Nonempty (p.2 ⧸ p.1.subgroupOf p.2 ≃* q.2 ⧸ q.1.subgroupOf q.2))
    (.inl rfl) (by
      rintro p q (rfl | ⟨h₁, h₂, ⟨f⟩⟩)
      · exact .inl rfl
      · exact .inr ⟨h₂, h₁, ⟨f.symm⟩⟩) (by
      rintro p q r (rfl | ⟨h₁, h₂, ⟨f⟩⟩) (rfl | ⟨h₂', h₃, ⟨g⟩⟩)
      · exact .inl rfl
      · exact .inr ⟨h₂', h₃, ⟨g⟩⟩
      · exact .inr ⟨h₁, h₂, ⟨f⟩⟩
      · exact .inr ⟨h₁, h₃, ⟨f.trans g⟩⟩) (by
      rintro x y ⟨-, hxn, -⟩
      exact .inr ⟨hxn, exists_nonempty_mulEquiv_sup_inf⟩) with h | ⟨_, _, h⟩
  · have h' (p : Subgroup G × Subgroup G) (hp : (s₁ i.castSucc, s₁ i.succ) = p)
        [(p.1.subgroupOf p.2).Normal] : Nonempty (s₁.factor i ≃* p.2 ⧸ p.1.subgroupOf p.2) := by
      subst hp
      exact ⟨MulEquiv.refl _⟩
    exact h' _ h
  · exact h

end SubnormalSeries

end Subgroup
