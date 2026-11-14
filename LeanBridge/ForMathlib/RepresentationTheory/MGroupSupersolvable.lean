import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.AGroupClosure
import LeanBridge.ForMathlib.GroupTheory.SupersolvableClosure
import LeanBridge.ForMathlib.RepresentationTheory.MGroup

/-!
# Supersolvable groups and solvable A-groups are M-groups

Let `G` be a finite group with a normal subgroup `N` such that `G ⧸ N` is supersolvable and `N` is
a solvable A-group. Then `G` is an M-group (LMFDB `group.monomial`): every irreducible
representation of `G` over an algebraically closed field of characteristic zero is induced from a
one-dimensional representation of a subgroup (Isaacs, Theorem 6.22). The case `N = ⊥` is
**Huppert's theorem**, that supersolvable groups are M-groups, and the case `N = ⊤` says that
solvable A-groups are M-groups (Isaacs, 6.23).

## The argument

The proof is by induction on `|G|`, and extends the argument of Tau Ceti's
`FDRep.exists_character_eq_indClassFun_of_isNilpotent` (Serre, §8.5). Let `W` be irreducible.

* If `W ≅ Ind_T^G U` for a proper subgroup `T` and an irreducible `U`, then `T`, with its normal
  subgroup `N ∩ T`, satisfies the hypotheses, so `U` is induced from a linear character by
  induction, and so is `W` by transitivity of induction.
* Otherwise `W` is primitive. Then every normal subgroup `A` acting through pairwise commuting
  operators acts centrally, that is, lies in the subgroup `Z` of the elements whose operators
  commute with all operators of `G`: by Clifford's correspondence, `W` is induced from the inertia
  group of an irreducible constituent of `Res_A W`, which is therefore all of `G`.
* `N ≤ Z`: going up the derived series of `N`, a term `M` with `⁅M, M⁆ ≤ Z` acts through a
  quotient that is nilpotent of class at most two and an A-group, hence abelian, so `M ≤ Z`.
* So `G ⧸ Z` is supersolvable. If `Z ≠ ⊤`, some normal subgroup `⟨x⟩ Z` with `x ∉ Z` acts through
  commuting operators, so it lies in `Z`, which is absurd. Hence `Z = ⊤`, the operators of `W`
  commute, and `W` is a linear character.

## Main results

* `FDRep.exists_character_eq_indClassFun_of_isSupersolvable_quotient`: the character of an
  irreducible representation of such a group is induced from a linear character of a subgroup.
* `FDRep.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isSupersolvable_quotient`: the
  representation itself is induced from a one-dimensional representation of a subgroup.
* `IsMGroup.of_isSupersolvable_quotient` (LMFDB `group.monomial`): a finite group with a normal
  solvable A-subgroup and supersolvable quotient is an M-group.
* `IsMGroup.of_isSupersolvable` (LMFDB `group.monomial`, `group.supersolvable`): **Huppert's
  theorem**, finite supersolvable groups are M-groups.
* `IsMGroup.of_isSolvable_of_isAGroup` (LMFDB `group.monomial`, `group.a_group`): finite solvable
  A-groups are M-groups.
* `IsMetacyclic.isMGroup` (LMFDB `group.metacyclic`), `IsZGroup.isMGroup` (LMFDB `group.z_group`):
  finite metacyclic groups and finite Z-groups are M-groups.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), 6.22 and 6.23.
* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §8.5,
  Theorem 16.
-/

open CategoryTheory Function Subgroup TauCeti

open scoped commutatorElement

universe u

namespace FDRep

variable {k G : Type u} [Field k] [Group G] [Finite G] (W : FDRep k G)

lemma exists_character_eq_indClassFun_of_iso_indFDRep {T : Subgroup G} {U : FDRep k T}
    (e : indFDRep U ≅ W)
    (h : ∃ (L : Subgroup T) (χ : L →* kˣ), U.character = L.indClassFun fun x ↦ (χ x : k)) :
    ∃ (H : Subgroup G) (χ : H →* kˣ), W.character = H.indClassFun fun x ↦ (χ x : k) := by
  rcases h with ⟨L₀, χ, hχ⟩
  rcases (⟨L₀.map T.subtype, map_subtype_le L₀,
    comap_map_eq_self_of_injective T.subtype_injective L₀⟩ : ∃ L ≤ T, L.subgroupOf T = L₀) with
    ⟨L, hLT, rfl⟩
  refine ⟨L, χ.comp (subgroupOfEquivOfLe hLT).symm.toMonoidHom, ?_⟩
  rw [← char_iso e, ← indClassFun_ofFDRep_character, hχ, ← indClassFun_indClassFun_subgroupOf L hLT
    (ClassFunction.mem_iff.mp <| MonoidHom.comp_mem_classFunction _ Units.val)]
  simp

variable [IsAlgClosed k] [CharZero k]

lemma commute_of_forall_isEmpty_iso_indFDRep [Simple W]
    (hW : ∀ (T : Subgroup G) (U : FDRep k T), T ≠ ⊤ → Simple U → IsEmpty (indFDRep U ≅ W))
    {A : Subgroup G} [A.Normal] (hA : ∀ a b : A, Commute (W.ρ a) (W.ρ b)) (a : A) (g : G) :
    Commute (W.ρ a) (W.ρ g) := by
  have : Nontrivial W := (isIrreducible_of_simple W).nontrivial
  rcases Representation.exists_isAtom (W.ρ.comp A.subtype) with ⟨σ, hσ⟩
  let V : FDRep k A := FDRep.of σ.toRepresentation
  have hV : Representation.IsIrreducible V.ρ :=
    Representation.isIrreducible_toRepresentation_of_isAtom hσ
  have : Simple V := simple_of_isIrreducible V
  by_cases hT : inertia V = ⊤
  · exact commute_of_inertia_eq_top W hA hσ hT a g
  · rcases exists_simple_liesOver_inertia_nonempty_iso_indFDRep V W
      (liesOver_of_ne_bot W A.subtype hσ.1) with ⟨U, hU, -, ⟨e⟩⟩
    exact ((hW _ U hT hU).false e).elim

/-- **The irreducible characters of a finite group with a normal solvable A-subgroup and
supersolvable quotient are monomial** (Isaacs, Theorem 6.22). Over an algebraically closed field
of characteristic zero, let `N` be a normal subgroup of the finite group `G` that is a solvable
A-group and such that `G ⧸ N` is supersolvable. Then for every irreducible representation `W` of
`G` there are a subgroup `H` and a linear character `χ` of `H` with `χ_W = Ind_H^G χ`. -/
lemma exists_character_eq_indClassFun_of_isSupersolvable_quotient [Simple W] (N : Subgroup G)
    [N.Normal] [Group.IsSolvable N] [IsAGroup N] (hN : Group.IsSupersolvable (G ⧸ N)) :
    ∃ (H : Subgroup G) (χ : H →* kˣ), W.character = H.indClassFun fun x ↦ (χ x : k) := by
  rcases (⟨_, rfl⟩ : ∃ n, Nat.card G = n) with ⟨n, hn⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hW : ∀ (T : Subgroup G) (U : FDRep k T), T ≠ ⊤ → Simple U → IsEmpty (indFDRep U ≅ W)
  · let Z : Subgroup G := upperCentralSeriesStep W.ρ.ker
    have hZn : Z.Normal := normal_upperCentralSeriesStep W.ρ.ker
    have hZ {A : Subgroup G} [A.Normal] (hA : ∀ a b : A, Commute (W.ρ a) (W.ρ b)) : A ≤ Z :=
      fun a ha ↦ (mem_upperCentralSeriesStep _ a).mpr fun g ↦
        W.ρ.commutatorElement_mem_ker_iff.mpr <|
          commute_of_forall_isEmpty_iso_indFDRep W hW hA ⟨a, ha⟩ g
    have hZc {z : G} (hz : z ∈ Z) (g : G) : Commute (W.ρ z) (W.ρ g) :=
      W.ρ.commutatorElement_mem_ker_iff.mp <| (mem_upperCentralSeriesStep _ z).mp hz g
    have hNZ : N ≤ Z := by
      rcases ‹Group.IsSolvable N›.solvable with ⟨d, hd⟩
      have key (j : ℕ) : j ≤ d → (derivedSeries N (d - j)).map N.subtype ≤ Z := by
        induction j with
        | zero => exact fun _ ↦ by simp [hd]
        | succ j ih =>
          intro hj
          have hM : ⁅(derivedSeries N (d - (j + 1))).map N.subtype,
              (derivedSeries N (d - (j + 1))).map N.subtype⁆ ≤ Z := by
            rw [← map_commutator, ← derivedSeries_succ, show d - (j + 1) + 1 = d - j by omega]
            exact ih <| by omega
          have : IsAGroup ((derivedSeries N (d - (j + 1))).map N.subtype) :=
            IsAGroup.of_injective <| inclusion_injective <| map_subtype_le _
          exact hZ fun a b ↦ W.ρ.commutatorElement_mem_ker_iff.mp <|
            IsAGroup.commutatorElement_mem_of_forall_commutatorElement_mem
              (W.ρ.comp ((derivedSeries N (d - (j + 1))).map N.subtype).subtype).ker
              (fun a b c ↦ (MonoidHom.commutatorElement_mem_ker_iff _).mpr <|
                hZc (hM <| commutator_mem_commutator a.2 b.2) c) a b
      simpa [← MonoidHom.range_eq_map] using key d le_rfl
    have hZtop : Z = ⊤ := by
      by_contra hZ'
      rcases (hN.of_surjective <| QuotientGroup.map_surjective_of_surjective N Z (MonoidHom.id G)
        QuotientGroup.mk_surjective hNZ).exists_notMem_normal_zpowers_sup hZ' with ⟨x, hx, hxn⟩
      have hxZ : x ∈ normalizer (Z : Set G) := normalizer_eq_top_iff.mpr hZn ▸ mem_top x
      refine hx <| hZ (A := zpowers x ⊔ Z) (fun a b ↦ ?_) <| mem_sup_left <| mem_zpowers x
      rcases exists_zpow_mul_eq_of_mem_sup hxZ a.2 with ⟨m, y, hy, ha⟩
      rcases exists_zpow_mul_eq_of_mem_sup hxZ b.2 with ⟨m', y', hy', hb⟩
      rw [← ha, ← hb, map_mul, map_mul]
      exact ((((Commute.refl x).zpow_zpow m m').map W.ρ).mul_right (hZc hy' _).symm).mul_left <|
        (hZc hy _).mul_right <| hZc hy _
    rcases exists_character_eq_of_commute W fun g g' ↦ hZc (hZtop ▸ mem_top g) g' with ⟨χ, hχ⟩
    refine ⟨⊤, χ.comp (⊤ : Subgroup G).subtype, hχ.trans <| funext fun g ↦ ?_⟩
    rw [indClassFun_top <| ClassFunction.mem_iff.mp <| MonoidHom.comp_mem_classFunction _ Units.val]
    rfl
  · simp only [not_forall, not_isEmpty_iff] at hW
    rcases hW with ⟨T, U, hT, hU, ⟨e⟩⟩
    have hinj : Injective (T.subtype.subgroupComap N) :=
      T.subtype.subgroupComap_injective N T.subtype_injective
    have : Group.IsSolvable (N.subgroupOf T) := Group.isSolvable_of_isSolvable_injective hinj
    have : IsAGroup (N.subgroupOf T) := IsAGroup.of_injective hinj
    have hTN : Group.IsSupersolvable (T ⧸ N.subgroupOf T) :=
      hN.of_injective (f := QuotientGroup.map (N.subgroupOf T) N T.subtype le_rfl) <|
        (injective_iff_map_eq_one _).mpr fun q hq ↦ by
          rcases QuotientGroup.mk_surjective q with ⟨t, rfl⟩
          exact (QuotientGroup.eq_one_iff t).mpr <| (QuotientGroup.eq_one_iff (t : G)).mp hq
    exact exists_character_eq_indClassFun_of_iso_indFDRep W e <|
      ih _ (hn ▸ (card_lt_of_lt <| lt_top_iff_ne_top.mpr hT).trans_eq card_top) U
        (N.subgroupOf T) hTN rfl

/-- **A finite group with a normal solvable A-subgroup and supersolvable quotient is an M-group**
(Isaacs, Theorem 6.22), over every algebraically closed field of characteristic zero: every
irreducible representation is induced from a one-dimensional representation of a subgroup. -/
lemma exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isSupersolvable_quotient [Simple W]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] [IsAGroup N]
    (hN : Group.IsSupersolvable (G ⧸ N)) :
    ∃ (H : Subgroup G) (χ : H →* kˣ), Nonempty (W ≅ indFDRep (ofLinearCharacter χ)) := by
  rcases exists_character_eq_indClassFun_of_isSupersolvable_quotient W N hN with ⟨H, χ, hχ⟩
  refine ⟨H, χ, nonempty_iso_of_character_eq _ _ ?_⟩
  rw [hχ, ← indClassFun_ofFDRep_character]
  exact congrArg (indClassFun H) <| funext fun h ↦ (char_ofLinearCharacter χ h).symm

end FDRep

variable {G : Type} [Group G] [Finite G]

namespace IsMGroup

/-- **A finite group with a normal solvable A-subgroup and supersolvable quotient is an M-group**
(LMFDB `group.monomial`; Isaacs, Theorem 6.22). -/
lemma of_isSupersolvable_quotient (N : Subgroup G) [N.Normal] [Group.IsSolvable N] [IsAGroup N]
    (hN : Group.IsSupersolvable (G ⧸ N)) : IsMGroup G :=
  ⟨fun W _ ↦ W.exists_nonempty_iso_indFDRep_ofLinearCharacter_of_isSupersolvable_quotient N hN⟩

/-- **Huppert's theorem: finite supersolvable groups are M-groups** (LMFDB `group.monomial`,
`group.supersolvable`). -/
lemma of_isSupersolvable (hG : Group.IsSupersolvable G) : IsMGroup G :=
  of_isSupersolvable_quotient ⊥ <| hG.quotient ⊥

/-- **Finite solvable A-groups are M-groups** (LMFDB `group.monomial`, `group.a_group`; Isaacs,
6.23). -/
lemma of_isSolvable_of_isAGroup [Group.IsSolvable G] [IsAGroup G] : IsMGroup G :=
  have : IsAGroup (⊤ : Subgroup G) := IsAGroup.of_injective (⊤ : Subgroup G).subtype_injective
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  of_isSupersolvable_quotient ⊤ Group.isSupersolvable_of_subsingleton

end IsMGroup

/-- **Finite metacyclic groups are M-groups** (LMFDB `group.metacyclic`), being supersolvable. -/
lemma IsMetacyclic.isMGroup [IsMetacyclic G] : IsMGroup G :=
  .of_isSupersolvable IsMetacyclic.isSupersolvable

/-- **Finite Z-groups are M-groups** (LMFDB `group.z_group`), being supersolvable. -/
lemma IsZGroup.isMGroup [IsZGroup G] : IsMGroup G :=
  .of_isSupersolvable IsZGroup.isSupersolvable
