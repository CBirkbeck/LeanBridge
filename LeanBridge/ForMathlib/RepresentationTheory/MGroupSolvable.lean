import LeanBridge.ForMathlib.RepresentationTheory.MGroup
import TauCeti.RepresentationTheory.Augmentation.Basic
import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# Taketa's theorem: M-groups are solvable

A finite group `G` all of whose irreducible complex representations are induced from
one-dimensional representations of subgroups (an M-group, LMFDB `group.monomial`) is solvable.

## The argument

Following Isaacs, Theorem 5.12, we show by induction on `n` that the `n`-th derived subgroup
`G⁽ⁿ⁾` acts trivially on every irreducible representation of degree at most `n`, hence on every
representation of degree at most `n`, a sum of such. Let `W ≅ Ind_H^G χ` be irreducible of degree
`n + 1 = [G : H]`.

* The permutation representation `ℂ[G ⧸ H]` is the sum of the trivial representation and the
  augmentation representation, of degree `n`. So `G⁽ⁿ⁾` acts trivially on `ℂ[G ⧸ H]`, that is, it
  fixes every coset, and `G⁽ⁿ⁾ ≤ H`.
* Then `G⁽ⁿ⁺¹⁾ ≤ ⁅H, H⁆` lies in the kernel of `χ`, and so do all its conjugates, `G⁽ⁿ⁺¹⁾` being
  normal. So `G⁽ⁿ⁺¹⁾` acts trivially on `Ind_H^G χ`.

As the irreducible representations have degree at most `|G|`, the derived subgroup `G⁽ⁿ⁾` with
`n = |G|` acts trivially on every representation, in particular on the regular one, which is
faithful. So it is trivial.

## Main results

* `IsMGroup.isSolvable` (LMFDB `group.monomial`): **Taketa's theorem**, M-groups are solvable.
* `IsMGroup.exists_index_eq_characterDegree`: in an M-group, the degree of every irreducible
  character is the index of a subgroup.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Theorem 5.12.
* K. Taketa, *Über die Gruppen, deren Darstellungen sich sämtlich auf monomiale Gestalt
  transformieren lassen*, Proc. Imp. Acad. Tokyo 6 (1930), 31–33.
-/

open CategoryTheory Module Subgroup TauCeti

variable {G : Type} [Group G]

lemma Subgroup.indClassFun_eq_index_of_forall_conj {k : Type*} [Semiring k] {H : Subgroup G}
    [H.FiniteIndex] (f : H → k) {g : G} (hg : ∀ x : G, ∃ y : H, y = x⁻¹ * g * x ∧ f y = 1) :
    H.indClassFun f g = H.index := by
  classical
  have h1 (t : G ⧸ H) : (if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ H then
      f ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩ else 0) = 1 := by
    rcases hg (Quotient.out t) with ⟨y, hy, hf⟩
    rw [dite_eq_left (hy ▸ y.2), ← hf]
    exact congrArg f <| Subtype.ext hy.symm
  simp [indClassFun_apply, h1, index_eq_card, Fintype.card_eq_nat_card]

variable [Finite G]

lemma FDRep.character_eq_character_one_of_forall_irreducibleCharacter_eq
    [Invertible (Nat.card G : ℂ)] (V : FDRep ℂ G) {g : G}
    (h : ∀ i, characterDegree ℂ i ≤ finrank ℂ V → irreducibleCharacter ℂ i g =
      characterDegree ℂ i) : V.character g = V.character 1 := by
  rcases (⟨_, character_eq_sum_nsmul_irreducibleCharacter V⟩ :
    ∃ m : Fin (Nat.card (ConjClasses G)) → ℕ, V.character = ∑ i, m i • irreducibleCharacter ℂ i)
    with ⟨m, hV⟩
  have h1 : finrank ℂ V = ∑ i, m i * characterDegree ℂ i := by
    have h2 : V.character 1 = (finrank ℂ V : ℂ) := V.char_one
    rw [hV] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, irreducibleCharacter_one] at h2
    simp only [nsmul_eq_mul] at h2
    exact_mod_cast h2.symm
  rw [hV]
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (m i) with hm | hm
  · rw [hm, zero_smul, zero_smul]
  · rw [irreducibleCharacter_one, h i <| (Nat.le_mul_of_pos_left _ hm).trans <| h1 ▸
      Finset.single_le_sum (f := fun i ↦ m i * characterDegree ℂ i) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ i)]

namespace IsMGroup

variable [Invertible (Nat.card G : ℂ)] {i : Fin (Nat.card (ConjClasses G))}

variable (i) in
lemma exists_irreducibleCharacter_eq_indClassFun [IsMGroup G] : ∃ (H : Subgroup G) (χ : H →* ℂˣ),
    irreducibleCharacter ℂ i = H.indClassFun fun x ↦ (χ x : ℂ) := by
  let W : FDRep ℂ G := FDRep.of (irreducibleRepresentation ℂ i)
  have : Representation.IsIrreducible W.ρ := by
    dsimp only [W, FDRep.of_ρ']
    infer_instance
  have : Simple W := FDRep.simple_of_isIrreducible W
  rcases exists_iso_indFDRep W with ⟨H, χ, ⟨e⟩⟩
  refine ⟨H, χ, ?_⟩
  rw [← character_irreducibleRepresentation ℂ i,
    show (fun x ↦ (χ x : ℂ)) = (FDRep.ofLinearCharacter χ).character from
      funext fun x ↦ (FDRep.char_ofLinearCharacter χ x).symm,
    indClassFun_ofFDRep_character]
  exact FDRep.char_iso e

lemma index_eq_characterDegree {H : Subgroup G} {χ : H →* ℂˣ}
    (h : irreducibleCharacter ℂ i = H.indClassFun fun x ↦ (χ x : ℂ)) :
    H.index = characterDegree ℂ i := by
  have h1 : (H.index : ℂ) = characterDegree ℂ i := by
    rw [← irreducibleCharacter_one, h]
    exact (indClassFun_eq_index_of_forall_conj _ fun x ↦ ⟨1, by simp, by simp⟩).symm
  exact_mod_cast h1

variable (i) in
/-- **In an M-group, the degree of every irreducible character is the index of a subgroup**, a
subgroup from a linear character of which the character is induced. -/
lemma exists_index_eq_characterDegree [IsMGroup G] :
    ∃ H : Subgroup G, H.index = characterDegree ℂ i := by
  rcases exists_irreducibleCharacter_eq_indClassFun i with ⟨H, χ, hχ⟩
  exact ⟨H, index_eq_characterDegree hχ⟩

end IsMGroup

/-- **Taketa's theorem: M-groups are solvable** (LMFDB `group.monomial`). If every irreducible
complex representation of the finite group `G` is induced from a one-dimensional representation
of a subgroup, then `G` is solvable: its `n`-th derived subgroup acts trivially on the irreducible
representations of degree at most `n`. -/
lemma IsMGroup.isSolvable [IsMGroup G] : Group.IsSolvable G := by
  let _ : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero <| Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key (n : ℕ) : ∀ i, characterDegree ℂ i ≤ n → ∀ g ∈ derivedSeries G n,
      irreducibleCharacter ℂ i g = characterDegree ℂ i := by
    induction n with
    | zero => exact fun i hi ↦ absurd hi (characterDegree_pos ℂ i).not_ge
    | succ n ih =>
      intro i hi g hg
      rcases hi.lt_or_eq with hi | hi
      · exact ih i (Nat.lt_succ_iff.mp hi) g <| derivedSeries_antitone G n.le_succ hg
      rcases exists_irreducibleCharacter_eq_indClassFun i with ⟨H, χ, hχ⟩
      have hidx : H.index = n + 1 := (index_eq_characterDegree hχ).trans hi
      have hH : derivedSeries G n ≤ H := fun x hx ↦ by
        let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
        let A : FDRep ℂ G := FDRep.of (augmentationSubrepresentation ℂ G (G ⧸ H)).toRepresentation
        have hA : finrank ℂ A = n :=
          (finrank_augmentationSubrepresentation (k := ℂ) (G := G) (X := G ⧸ H)).trans <| by
            rw [← Nat.card_eq_fintype_card, ← index_eq_card, hidx, Nat.add_sub_cancel]
        have hAc (y : G) : A.character y = (Nat.card {q : G ⧸ H // y • q = q} : ℂ) - 1 :=
          (character_augmentationSubrepresentation y).trans <|
            congrArg (· - 1) <| char_ofMulAction ℂ (G ⧸ H) y
        have hAx : A.character x = A.character 1 :=
          A.character_eq_character_one_of_forall_irreducibleCharacter_eq fun j hj ↦
            ih j (hA ▸ hj) x hx
        rw [hAc, hAc, sub_left_inj, Nat.cast_inj] at hAx
        by_contra hxH
        refine (Finite.card_subtype_lt (p := fun q : G ⧸ H ↦ x • q = q) (x := ((1 : G) : G ⧸ H))
          fun h ↦ hxH ?_).ne <| hAx.trans <| by simp
        simpa [QuotientGroup.eq] using h
      rw [hχ, hi, ← hidx]
      refine indClassFun_eq_index_of_forall_conj _ fun x ↦ ?_
      have hx : x⁻¹ * g * x ∈ ⁅H, H⁆ :=
        commutator_mono hH hH <| (derivedSeries_normal G (n + 1)).conj_mem' g hg x
      rw [← map_subtype_commutator, mem_map] at hx
      rcases hx with ⟨y, hy, hyx⟩
      exact ⟨y, hyx, by
        simp [MonoidHom.mem_ker.mp <| Abelianization.commutator_subset_ker χ hy]⟩
  refine ⟨⟨Nat.card G, (eq_bot_iff_forall _).mpr fun g hg ↦ ?_⟩⟩
  let R : FDRep ℂ G := FDRep.of (Representation.ofMulAction ℂ G G)
  have hR (y : G) : R.character y = (Nat.card {x : G // y • x = x} : ℂ) :=
    char_ofMulAction ℂ G y
  have hg1 : R.character g = R.character 1 :=
    R.character_eq_character_one_of_forall_irreducibleCharacter_eq fun j _ ↦
      key _ j (Nat.le_of_dvd Nat.card_pos <| characterDegree_dvd_card ℂ j) g hg
  rw [hR, hR, Nat.cast_inj] at hg1
  by_contra hg'
  have : IsEmpty {x : G // g • x = x} :=
    ⟨fun x ↦ hg' <| mul_right_cancel <| x.2.trans (one_mul x.1).symm⟩
  have h1 : Nat.card {x : G // (1 : G) • x = x} = Nat.card G := by
    simp
  rw [Nat.card_of_isEmpty, h1] at hg1
  exact Nat.card_pos.ne hg1
