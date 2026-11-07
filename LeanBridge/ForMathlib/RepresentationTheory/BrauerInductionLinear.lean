import LeanBridge.ForMathlib.GroupTheory.InternalDirectProduct
import TauCeti.RepresentationTheory.Induction.Brauer.Induction
import TauCeti.RepresentationTheory.Induction.Monomial

/-!
# Brauer's induction theorem with linear characters

A finite group is `p`-elementary (LMFDB `group.elementary`) if it is the direct product of a cyclic
group of order prime to `p` and a `p`-group. Tau Ceti's `IsPElementary` asks instead for an internal
decomposition, a cyclic subgroup of order prime to `p` and a `p`-subgroup that commute elementwise
and are complements of each other; we prove that the two agree.

Brauer's induction theorem (LMFDB `group.elementary`) states that every character of a finite group
`G` is an integer linear combination of characters induced from linear characters of elementary
subgroups of `G`, `p`-elementary for primes `p` dividing `|G|`. Tau Ceti proves it with characters
induced from irreducible characters of elementary subgroups. Elementary groups are nilpotent, so
their irreducible characters are induced from linear characters of subgroups (finite nilpotent
groups are M-groups), which are again elementary, and induction is transitive; this gives the
statement with linear characters. An elementary subgroup that is `q`-elementary for a prime `q` not
dividing `|G|` is cyclic, hence `p`-elementary for every prime `p`, so when `G` is nontrivial the
primes can be taken to divide `|G|`.

## Main results

* `TauCeti.isPElementary_iff_exists_mulEquiv_prod` (LMFDB `group.elementary`): a group is
  `p`-elementary in Tau Ceti's sense if and only if it is isomorphic to `C × P` for a cyclic group
  `C` of order prime to `p` and a `p`-group `P`.
* `FDRep.character_mem_closure_indClassFun_linear_isElementary` (LMFDB `group.elementary`):
  Brauer's induction theorem with linear characters of elementary subgroups.
* `FDRep.character_mem_closure_indClassFun_linear_isPElementary` (LMFDB `group.elementary`): the
  same with `p`-elementary subgroups for primes `p` dividing `|G|`, for nontrivial `G`.
-/

open CategoryTheory TauCeti ClassFunction

universe u

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G]

lemma isPElementary_prod {C P : Type*} [Group C] [Group P] [IsCyclic C]
    (hC : (Nat.card C).Coprime p) (hP : IsPGroup p P) : IsPElementary p (C × P) := by
  have h : (MonoidHom.inl C P).range.IsDirectFactors (MonoidHom.inr C P).range :=
    MonoidHom.isDirectFactors_range_inl_range_inr C P
  refine isPElementary_def.mpr ⟨(MonoidHom.inl C P).range, (MonoidHom.inr C P).range,
    isCyclic_of_surjective _ (MonoidHom.inl C P).rangeRestrict_surjective, ?_,
    hP.of_surjective _ (MonoidHom.inr C P).rangeRestrict_surjective, ?_,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ h.disjoint h.mul_eq_univ⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective (Prod.mk_left_injective 1)).toEquiv]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hC.symm
  · rintro _ ⟨c, rfl⟩ _ ⟨x, rfl⟩
    exact MonoidHom.commute_inl_inr c x

/-- **A group is `p`-elementary if and only if it is the direct product of a cyclic group of order
prime to `p` and a `p`-group** (LMFDB `group.elementary`): Tau Ceti's internal decomposition gives
direct factors `C` and `P` with `G ≃* C × P`, and conversely such a product is `p`-elementary. -/
lemma isPElementary_iff_exists_mulEquiv_prod :
    IsPElementary p G ↔ ∃ (C P : Type u) (_ : Group C) (_ : Group P), IsCyclic C ∧
      (Nat.card C).Coprime p ∧ IsPGroup p P ∧ Nonempty (G ≃* C × P) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isPElementary_def.mp h with ⟨C, P, hC, hCp, hP, hcomm, hCP⟩
    have hd : C.IsDirectFactors P := ⟨normal_of_commute_of_isComplement' hcomm hCP,
      normal_of_commute_of_isComplement' (fun x hx c hc ↦ (hcomm c hc x hx).symm) hCP.symm,
      hCP.disjoint, hCP.mul_eq⟩
    exact ⟨C, P, inferInstance, inferInstance, hC,
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hCp).symm, hP, ⟨hd.mulEquiv.symm⟩⟩
  · rintro ⟨C, P, _, _, hC, hCp, hP, ⟨e⟩⟩
    exact (isPElementary_prod hCp hP).of_injective e.toMonoidHom e.injective

lemma IsPElementary.isCyclic_of_not_dvd (h : IsPElementary p G) (hp : ¬p ∣ Nat.card G) :
    IsCyclic G := by
  rcases isPElementary_def.mp h with ⟨C, P, hC, -, hP, -, hCP⟩
  have hP1 : P = ⊥ := Subgroup.card_eq_one.mp <| (hP.card_eq_or_dvd).resolve_right fun hdvd ↦
    hp (hdvd.trans P.card_subgroup_dvd_card)
  rw [hP1, Subgroup.isComplement'_bot_right] at hCP
  subst hCP
  exact isCyclic_of_surjective (⊤ : Subgroup G).subtype fun x ↦ ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩

end TauCeti

namespace FDRep

variable {k G : Type u} [Field k] [Group G] [Finite G] [CharZero k] [IsAlgClosed k]
  (V : FDRep k G)

/-- **Brauer's induction theorem with linear characters** (LMFDB `group.elementary`): over an
algebraically closed field of characteristic zero, every character of a finite group `G` is an
integer linear combination of characters `Ind_H^G χ` induced from linear characters `χ : H →* kˣ`
of elementary subgroups `H` of `G`. -/
lemma character_mem_closure_indClassFun_linear_isElementary :
    V.character ∈ AddSubgroup.closure {f | ∃ (H : Subgroup G) (χ : H →* kˣ),
      IsElementary H ∧ Subgroup.indClassFun H (fun h ↦ (χ h : k)) = f} := by
  refine indCharacterSpanInt_le_iff.mpr (fun E hE d ρ hρ ↦ ?_)
    (character_mem_indCharacterSpanInt_isElementary V)
  have hnil : Group.IsNilpotent E := hE.isNilpotent
  have hirr : Representation.IsIrreducible (FDRep.of ρ).ρ := by
    simpa only [FDRep.of_ρ'] using hρ
  have hsimple : Simple (FDRep.of ρ) := FDRep.simple_of_isIrreducible _
  rcases (FDRep.of ρ).exists_character_eq_indClassFun_of_isNilpotent with ⟨D, χ, hχ⟩
  rcases (⟨D.map E.subtype, Subgroup.map_subtype_le D,
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective D⟩ :
      ∃ H ≤ E, H.subgroupOf E = D) with ⟨H, hHE, rfl⟩
  let ψ : H →* kˣ := χ.comp (Subgroup.subgroupOfEquivOfLe hHE).symm.toMonoidHom
  refine AddSubgroup.subset_closure ⟨H, ψ, ?_, Eq.symm ?_⟩
  · rcases isElementary_def.mp hE with ⟨q, hq, hqE⟩
    have : Fact q.Prime := ⟨hq⟩
    exact isElementary_def.mpr
      ⟨q, hq, hqE.of_injective (Subgroup.inclusion hHE) (Subgroup.inclusion_injective hHE)⟩
  · have hρχ : ((ofCharacter ρ : ClassFunction k E) : E → k) = (FDRep.of ρ).character :=
      funext fun g ↦ by simp
    have hInd : ((E.indClassFunction (ofCharacter ρ) : ClassFunction k G) : G → k) =
        Subgroup.indClassFun E (ofCharacter ρ) :=
      funext (Subgroup.indClassFunction_apply E (ofCharacter ρ))
    rw [hInd, hρχ, hχ]
    convert Subgroup.indClassFun_indClassFun_subgroupOf H hHE
      (ClassFunction.mem_iff.mp (MonoidHom.comp_mem_classFunction ψ Units.val)) using 1
    simp [ψ]

/-- **Brauer's induction theorem with linear characters and primes dividing `|G|`** (LMFDB
`group.elementary`): for a nontrivial finite group `G`, the elementary subgroups in Brauer's
theorem can be taken `p`-elementary for primes `p` dividing `|G|`, since an elementary subgroup
that is `q`-elementary for a prime `q ∤ |G|` is cyclic, hence `p`-elementary for every `p`. -/
lemma character_mem_closure_indClassFun_linear_isPElementary [Nontrivial G] :
    V.character ∈ AddSubgroup.closure {f | ∃ (p : ℕ) (H : Subgroup G) (χ : H →* kˣ), p.Prime ∧
      p ∣ Nat.card G ∧ IsPElementary p H ∧ Subgroup.indClassFun H (fun h ↦ (χ h : k)) = f} := by
  refine AddSubgroup.closure_mono ?_ V.character_mem_closure_indClassFun_linear_isElementary
  rintro _ ⟨H, χ, hH, rfl⟩
  rcases isElementary_def.mp hH with ⟨q, hq, hqH⟩
  by_cases hqG : q ∣ Nat.card G
  · exact ⟨q, H, χ, hq, hqG, hqH, rfl⟩
  · rcases Nat.exists_prime_and_dvd (Finite.one_lt_card (α := G)).ne' with ⟨p, hp, hpG⟩
    have : Fact p.Prime := ⟨hp⟩
    have : Fact q.Prime := ⟨hq⟩
    have : IsCyclic H :=
      hqH.isCyclic_of_not_dvd fun hdvd ↦ hqG (hdvd.trans H.card_subgroup_dvd_card)
    exact ⟨p, H, χ, hp, hpG, isPElementary_of_isCyclic p, rfl⟩

end FDRep
