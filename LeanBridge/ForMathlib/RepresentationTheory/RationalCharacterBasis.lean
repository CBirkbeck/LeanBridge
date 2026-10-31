import LeanBridge.ForMathlib.RepresentationTheory.CharacterLabel
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import TauCeti.RepresentationTheory.CharacterTable.Galois

/-!
# Irreducible rational characters and the rational character table

A rational character of a finite group `G` (LMFDB `group.representation.rational_character`) is a
complex character with values in `ℚ`, and the irreducible rational character attached to an
irreducible complex character `χ` is the sum `∑ σ ∘ χ` of its distinct Galois conjugates
(`FDRep.rationalCharacter`). We prove the facts that the knowl states: the irreducible rational
characters are rational characters, they form a `ℚ`-basis of the `ℚ`-vector space spanned by the
rational characters, and rational characters are constant on the rational conjugacy classes. For
the rational character table (LMFDB `group.rational_character_table`), the values of the
irreducible rational characters on the rational classes, we prove that its entries do not depend on
the representatives of the classes and that it is square.

The values of a character `χ` at `g` and at `g ^ k`, for `k` prime to the order of `g`, are
conjugate by an automorphism of `ℂ` raising the roots of unity to the `k`-th power, which exists
because the cyclotomic polynomials are irreducible over `ℚ` and embeddings of countable subfields of
`ℂ` extend to automorphisms of `ℂ`. Conversely an algebraic number fixed by every automorphism of
`ℂ` is rational. Writing a rational valued function `f` constant on the rational classes in the
basis of irreducible characters, its coefficients `⟨χ, f⟩` are then rational and constant on the
Galois orbits, so `f` is a `ℚ`-combination of the irreducible rational characters; with the
`ℚ`-linear independence of the irreducible rational characters, this identifies their `ℚ`-span
with the functions on the rational classes, whence both the basis and the squareness.

## Main definitions

* `FDRep.rationalCharacterSpace` (LMFDB `group.representation.rational_character`): the
  `ℚ`-vector space spanned by the rational characters.
* `FDRep.irreducibleRationalCharacterBasis` (LMFDB `group.representation.rational_character`): the
  irreducible rational characters, as a `ℚ`-basis of the rational characters.

## Main results

* `IsPrimitiveRoot.exists_algEquiv_complex_apply_eq_pow`: every power `ζ ↦ ζ ^ k` with `k` prime to
  the order of a root of unity `ζ ∈ ℂ` is induced by an automorphism of `ℂ`.
* `Complex.exists_eq_ratCast_of_forall_algEquiv_apply_eq`: an algebraic number fixed by every
  automorphism of `ℂ` is rational.
* `FDRep.algEquiv_comp_rationalCharacter`: the irreducible rational character is fixed by the
  automorphisms of `ℂ`.
* `FDRep.exists_isRationalCharacter_character_eq_rationalCharacter`: the irreducible rational
  character of an irreducible representation is a rational character.
* `FDRep.IsRationalCharacter.character_eq_of_isRationallyConj`: rational characters are constant on
  the rational conjugacy classes.
* `FDRep.mem_span_irreducibleRationalCharacters`: a rational valued function constant on the
  rational classes is a `ℚ`-combination of the irreducible rational characters.
* `FDRep.linearIndepOn_irreducibleRationalCharacters` and
  `FDRep.span_irreducibleRationalCharacters`: the irreducible rational characters are linearly
  independent over `ℚ` and span the rational characters.
* `FDRep.rationalCharacterTable_mk`: the entries of the rational character table do not depend on
  the representatives of the rational classes.
* `FDRep.card_irreducibleRationalCharacters`: the rational character table is square, there being
  as many irreducible rational characters as rational conjugacy classes.
-/

open CategoryTheory IntermediateField Limits Module TauCeti

variable {n j : ℕ} [NeZero n] {ζ z : ℂ}

variable (z) in
lemma Complex.countable_adjoin_simple : Countable ℚ⟮z⟯ := by
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (cardinalMk_adjoin_le ℚ _).trans <|
    sup_le (sup_le Cardinal.mk_le_aleph0 (Set.countable_singleton z).le_aleph0) le_rfl

/-- **Coprime powers of a root of unity are induced by automorphisms of `ℂ`**: the power `ζ ^ j` of
a primitive `n`-th root of unity `ζ` with `j` prime to `n` is a root of the cyclotomic polynomial,
the minimal polynomial of `ζ` over `ℚ`, so `ζ ↦ ζ ^ j` is an embedding of `ℚ(ζ)`, which extends to
`ℂ`. -/
lemma IsPrimitiveRoot.exists_algEquiv_complex_apply_eq_pow (hζ : IsPrimitiveRoot ζ n)
    (hj : n.Coprime j) : ∃ σ : ℂ ≃ₐ[ℚ] ℂ, σ ζ = ζ ^ j := by
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  have : Countable ℚ⟮ζ⟯ := Complex.countable_adjoin_simple ζ
  have hroot : ζ ^ j ∈ (minpoly ℚ ζ).aroots ℂ := by
    rw [Polynomial.mem_aroots, ← Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos n),
      Polynomial.cyclotomic_eq_minpoly_rat (hζ.pow_of_coprime j hj.symm) (NeZero.pos n)]
    exact ⟨minpoly.ne_zero (hint.pow j), minpoly.aeval ℚ (ζ ^ j)⟩
  rcases exists_algEquiv_apply_eq_of_countable
    ((algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ ^ j, hroot⟩) with ⟨σ, hσ⟩
  exact ⟨σ, (hσ (AdjoinSimple.gen ℚ ζ)).trans (algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _)⟩

/-- **An algebraic number fixed by every automorphism of `ℂ` is rational**: every embedding of
`ℚ(z)` into `ℂ` extends to an automorphism of `ℂ`, which fixes `z`, so `ℚ(z)` has a single
embedding and degree `1`. -/
lemma Complex.exists_eq_ratCast_of_forall_algEquiv_apply_eq (hz : IsIntegral ℚ z)
    (h : ∀ σ : ℂ ≃ₐ[ℚ] ℂ, σ z = z) : ∃ q : ℚ, z = q := by
  have : Countable ℚ⟮z⟯ := Complex.countable_adjoin_simple z
  have : FiniteDimensional ℚ ℚ⟮z⟯ := adjoin.finiteDimensional hz
  have hι (ι : ℚ⟮z⟯ →ₐ[ℚ] ℂ) : ι = ℚ⟮z⟯.val := by
    rcases exists_algEquiv_apply_eq_of_countable ι with ⟨σ, hσ⟩
    refine adjoin_algHom_ext ℚ ?_
    rintro x rfl
    exact (hσ _).symm.trans (h σ)
  have hrank : finrank ℚ ℚ⟮z⟯ = 1 := by
    rw [← AlgHom.card ℚ ℚ⟮z⟯ ℂ, Fintype.card_eq_one_iff]
    exact ⟨_, hι⟩
  rcases mem_bot.mp (finrank_eq_one_iff.mp hrank ▸ mem_adjoin_simple_self ℚ z) with ⟨q, hq⟩
  exact ⟨q, hq.symm.trans <| eq_ratCast (algebraMap ℚ ℂ) q⟩

namespace FDRep

variable {G : Type} [Group G] (X : FDRep ℂ G) {Y : FDRep ℂ G}

open Finset in
lemma exists_character_eq_sum {s : Finset (G → ℂ)} (hs : s.Nonempty)
    (h : ∀ ψ ∈ s, ∃ Y : FDRep ℂ G, Y.character = ψ) :
    ∃ Y : FDRep ℂ G, Y.character = ∑ ψ ∈ s, ψ := by
  induction hs using Nonempty.cons_induction with
  | singleton a => simpa using h a (Finset.mem_singleton_self a)
  | cons a s _ _ ih =>
    rcases h a (Finset.mem_cons_self a s) with ⟨A, hA⟩
    rcases ih fun ψ hψ ↦ h ψ (Finset.mem_cons_of_mem hψ) with ⟨B, hB⟩
    exact ⟨A ⊞ B, by rw [char_biprod, hA, hB, Finset.sum_cons]⟩

variable [Finite G] {x y : G}

/-- **The irreducible rational character is fixed by the automorphisms of `ℂ`**, which permute the
Galois conjugates of a character. -/
lemma algEquiv_comp_rationalCharacter (σ : ℂ ≃ₐ[ℚ] ℂ) :
    σ ∘ X.rationalCharacter = X.rationalCharacter := by
  have hmem (τ : ℂ ≃ₐ[ℚ] ℂ) {ψ : G → ℂ} (hψ : ψ ∈ X.finite_galoisConjugates.toFinset) :
      τ ∘ ψ ∈ X.finite_galoisConjugates.toFinset := by
    rcases X.finite_galoisConjugates.mem_toFinset.mp hψ with ⟨υ, rfl⟩
    exact X.finite_galoisConjugates.mem_toFinset.mpr ⟨τ * υ, rfl⟩
  rw [rationalCharacter, finsum_mem_eq_finite_toFinset_sum _ X.finite_galoisConjugates]
  funext g
  rw [Function.comp_apply, Finset.sum_apply, map_sum]
  exact Finset.sum_nbij' (σ ∘ ·) (σ.symm ∘ ·) (fun ψ hψ ↦ hmem σ hψ) (fun ψ hψ ↦ hmem σ.symm hψ)
    (fun ψ _ ↦ funext fun g ↦ σ.symm_apply_apply (ψ g))
    (fun ψ _ ↦ funext fun g ↦ σ.apply_symm_apply (ψ g)) fun ψ _ ↦ rfl

variable [Simple X] in
lemma exists_character_eq_rationalCharacter :
    ∃ Y : FDRep ℂ G, Y.character = X.rationalCharacter := by
  rw [rationalCharacter, finsum_mem_eq_finite_toFinset_sum _ X.finite_galoisConjugates]
  refine exists_character_eq_sum ⟨X.character, X.finite_galoisConjugates.mem_toFinset.mpr ⟨1, rfl⟩⟩
    fun ψ hψ ↦ ?_
  rcases mem_irreducibleCharacters_iff.mp <| rationalClass_subset_irreducibleCharacters
    X.character_mem_irreducibleCharacters <| X.finite_galoisConjugates.mem_toFinset.mp hψ with
    ⟨n, ρ, -, rfl⟩
  exact ⟨FDRep.of ρ, character_of ρ⟩

variable [Simple X] in
/-- **The irreducible rational character attached to an irreducible representation is a rational
character** (LMFDB `group.representation.rational_character`): it is the character of the direct
sum of representations affording the Galois conjugates of the character, and it is rational valued,
being fixed by the automorphisms of `ℂ`. -/
lemma exists_isRationalCharacter_character_eq_rationalCharacter :
    ∃ Y : FDRep ℂ G, Y.IsRationalCharacter ∧ Y.character = X.rationalCharacter := by
  rcases X.exists_character_eq_rationalCharacter with ⟨Y, hY⟩
  refine ⟨Y, (rationalClass_subsingleton_iff Y).mp ?_, hY⟩
  rintro - ⟨σ, rfl⟩ - ⟨τ, rfl⟩
  rw [hY]
  exact (X.algEquiv_comp_rationalCharacter σ).trans (X.algEquiv_comp_rationalCharacter τ).symm

lemma IsRationalCharacter.character_pow_eq (hY : Y.IsRationalCharacter)
    (hj : (orderOf x).Coprime j) : Y.character (x ^ j) = Y.character x := by
  have hx : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have : NeZero (orderOf x) := ⟨hx⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / orderOf x)) (orderOf x) :=
    Complex.isPrimitiveRoot_exp _ hx
  rcases hζ.exists_algEquiv_complex_apply_eq_pow hj with ⟨σ, hσ⟩
  rcases hY x with ⟨q, hq⟩
  rw [← map_character_eq_character_pow Y hx (pow_orderOf_eq_one x) σ.toRingEquiv.toRingHom
    fun μ hμ ↦ hζ.map_eq_pow _ hσ hμ, hq]
  exact map_ratCast σ q

/-- **A rational character is constant on the rational conjugacy classes** (LMFDB
`group.representation.rational_character`): a character is constant on conjugacy classes, and its
values at `g` and at `g ^ k`, `k` prime to the order of `g`, are conjugate by an automorphism of
`ℂ`, which fixes a rational value. -/
lemma IsRationalCharacter.character_eq_of_isRationallyConj (hY : Y.IsRationalCharacter)
    (h : IsRationallyConj x y) : Y.character x = Y.character y := by
  rcases h with ⟨m, hm, h⟩
  rcases isConj_iff.mp h with ⟨c, rfl⟩
  rw [char_conj]
  rcases mem_powers_iff_mem_zpowers.mpr (zpow_mem (Subgroup.mem_zpowers x) m) with ⟨k, hk⟩
  have hk' : x ^ k = x ^ m := hk
  have hord : orderOf (x ^ k) = orderOf x := hk' ▸ orderOf_zpow_of_gcd_eq_one hm
  rw [orderOf_pow] at hord
  rw [← hk']
  exact (hY.character_pow_eq <| Nat.coprime_iff_gcd_eq_one.mpr <|
    (Nat.div_eq_self.mp hord).resolve_left (orderOf_pos x).ne').symm

open scoped Classical in
lemma rationalCharacter_eq_sum_filter (i : Fin (Nat.card (ConjClasses G)))
    (hX : X.character = irreducibleCharacter ℂ i) : X.rationalCharacter = ∑ j with
    irreducibleCharacter ℂ j ∈ rationalClass (irreducibleCharacter ℂ i),
    irreducibleCharacter ℂ j := by
  have hset : rationalClass (irreducibleCharacter ℂ i) = irreducibleCharacter ℂ ''
      ↑({j | irreducibleCharacter ℂ j ∈ rationalClass (irreducibleCharacter ℂ i)} :
        Finset (Fin (Nat.card (ConjClasses G)))) := by
    ext ψ
    refine ⟨fun hψ ↦ ?_, ?_⟩
    · rcases exists_irreducibleCharacter_eq ℂ (rationalClass_subset_irreducibleCharacters
        (irreducibleCharacter_mem ℂ i) hψ) with ⟨j, rfl⟩
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hψ⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact (Finset.mem_filter.mp hj).2
  rw [rationalCharacter, galoisConjugates_eq_rationalClass, hX]
  refine (congrArg (fun s ↦ ∑ᶠ ψ ∈ s, ψ) hset).trans ?_
  rw [finsum_mem_image (irreducibleCharacter_injective ℂ).injOn, finsum_mem_coe_finset]

variable {f : G → ℂ} (ψ : irreducibleRationalCharacters G)

variable [Fintype G] in
lemma sum_algEquiv_character_mul_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hfc : ∀ x y, IsRationallyConj x y → f x = f y) (σ : ℂ ≃ₐ[ℚ] ℂ) :
    ∑ g, σ (ρ.character g) * f g⁻¹ = ∑ g, ρ.character g * f g⁻¹ := by
  have hN : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have : NeZero (Nat.card G) := ⟨hN⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Nat.card G)) (Nat.card G) :=
    Complex.isPrimitiveRoot_exp _ hN
  have hk : (Nat.card G).Coprime (hζ.autToPow ℚ σ : ZMod (Nat.card G)).val :=
    (ZMod.val_coe_unit_coprime _).symm
  refine (Finset.sum_congr rfl fun g _ ↦ ?_).trans
    ((powCoprime hk).sum_comp fun g ↦ ρ.character g * f g⁻¹)
  have hfg : f g⁻¹ = f (g ^ (hζ.autToPow ℚ σ : ZMod (Nat.card G)).val)⁻¹ := by
    refine hfc _ _ ⟨(hζ.autToPow ℚ σ : ZMod (Nat.card G)).val, ?_, ?_⟩
    · rw [Int.gcd_natCast_natCast]
      exact hk.symm.coprime_dvd_right (orderOf_dvd_natCard g⁻¹)
    · rw [zpow_natCast, inv_pow]
  rw [powCoprime_apply, hfg]
  exact congrArg (· * _) <| Representation.map_character_eq_character_pow ρ
    (Nat.cast_ne_zero.mpr hN) pow_card_eq_one' σ.toRingEquiv.toRingHom
    fun μ hμ ↦ hζ.map_eq_pow _ (hζ.autToPow_spec ℚ σ).symm hμ

/-- **A rational valued function constant on the rational classes is a `ℚ`-linear combination of
the irreducible rational characters**: its coefficients `⟨χ, f⟩` in the basis of irreducible
characters are algebraic numbers fixed by the automorphisms of `ℂ`, hence rational, and they are
constant on the Galois orbits of the irreducible characters. -/
lemma mem_span_irreducibleRationalCharacters (hf : ∀ g, ∃ q : ℚ, f g = q)
    (hfc : ∀ x y, IsRationallyConj x y → f x = f y) :
    f ∈ Submodule.span ℚ (irreducibleRationalCharacters G) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let c : Fin (Nat.card (ConjClasses G)) → ℂ :=
    fun i ↦ (Nat.card G : ℂ)⁻¹ * ∑ g, irreducibleCharacter ℂ i g * f g⁻¹
  have hc (i : Fin (Nat.card (ConjClasses G))) :
      c i = (Nat.card G : ℂ)⁻¹ * ∑ g, irreducibleCharacter ℂ i g * f g⁻¹ :=
    rfl
  have hexp : f = ∑ i, c i • irreducibleCharacter ℂ i := by
    funext y
    rw [Finset.sum_apply]
    refine (ClassFunction.apply_eq_sum_characterPairing_mul_character
      (irreducibleRepresentation ℂ) (pairwise_isEmpty_equiv_irreducibleRepresentation ℂ) (by simp)
      ⟨f, fun g h ↦ (hfc _ _ (isConj_iff.mpr ⟨h, rfl⟩).isRationallyConj).symm⟩ y).trans <|
      Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ClassFunction.characterPairing_apply, Pi.smul_apply, smul_eq_mul, hc,
      character_irreducibleRepresentation]
    simp
  have hσf (σ : ℂ ≃ₐ[ℚ] ℂ) (g : G) : σ (f g) = f g := by
    rcases hf g with ⟨q, hq⟩
    rw [hq, map_ratCast]
  have hcomp (σ : ℂ ≃ₐ[ℚ] ℂ) (i : Fin (Nat.card (ConjClasses G))) :
      (Nat.card G : ℂ)⁻¹ * ∑ g, σ (irreducibleCharacter ℂ i g) * f g⁻¹ = c i := by
    rw [hc, ← character_irreducibleRepresentation, sum_algEquiv_character_mul_eq _ hfc σ]
  have hint (i : Fin (Nat.card (ConjClasses G))) : IsIntegral ℚ (c i) := by
    have hA (x : ℂ) (hx : x ^ Nat.card G = 1) : x ∈ (integralClosure ℚ ℂ).toSubring :=
      (mem_integralClosure_iff ℚ ℂ).mpr <| IsIntegral.of_pow Nat.card_pos (hx ▸ isIntegral_one)
    rw [← mem_integralClosure_iff ℚ ℂ, hc, ← map_natCast (algebraMap ℚ ℂ), ← map_inv₀]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun g _ ↦
      Subalgebra.mul_mem _ (irreducibleCharacter_apply_mem_of_forall_pow_eq_one_mem ℂ hA i g) ?_)
    rcases hf g⁻¹ with ⟨q, hq⟩
    rw [hq, ← eq_ratCast (algebraMap ℚ ℂ)]
    exact Subalgebra.algebraMap_mem _ _
  have hq (i : Fin (Nat.card (ConjClasses G))) : ∃ q : ℚ, c i = q := by
    refine Complex.exists_eq_ratCast_of_forall_algEquiv_apply_eq (hint i) fun σ ↦ ?_
    rw [hc, map_mul, map_inv₀, map_natCast, map_sum]
    simp only [map_mul, hσf]
    exact hcomp σ i
  have hconst (i i₀ : Fin (Nat.card (ConjClasses G)))
      (h : irreducibleCharacter ℂ i ∈ rationalClass (irreducibleCharacter ℂ i₀)) : c i = c i₀ := by
    rcases h with ⟨σ, hσ⟩
    rw [← hcomp σ i₀, hc, ← hσ]
    rfl
  choose q hq using hq
  let κ : Fin (Nat.card (ConjClasses G)) → Finset (Fin (Nat.card (ConjClasses G))) :=
    fun i ↦ Finset.univ.filter fun j ↦
      irreducibleCharacter ℂ j ∈ rationalClass (irreducibleCharacter ℂ i)
  have hκ (i j : Fin (Nat.card (ConjClasses G))) : κ j = κ i ↔ j ∈ κ i := by
    refine ⟨fun h ↦ h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, mem_rationalClass_self _⟩,
      fun h ↦ ?_⟩
    have hj : rationalClass (irreducibleCharacter ℂ j) = rationalClass (irreducibleCharacter ℂ i) :=
      rationalClass_eq_of_mem (Finset.mem_filter.mp h).2
    simp only [κ, hj]
  rw [hexp, ← Finset.sum_fiberwise Finset.univ κ]
  refine Submodule.sum_mem _ fun T _ ↦ ?_
  by_cases hT : ∃ i₀, κ i₀ = T
  · rcases hT with ⟨i₀, rfl⟩
    have hfib : Finset.univ.filter (fun i ↦ κ i = κ i₀) = κ i₀ := by
      ext i
      rw [Finset.mem_filter, hκ]
      exact and_iff_right (Finset.mem_univ i)
    rw [hfib, Finset.sum_congr rfl fun i hi ↦ by
      rw [hconst i i₀ (Finset.mem_filter.mp hi).2, hq i₀], ← Finset.smul_sum,
      ← eq_ratCast (algebraMap ℚ ℂ), algebraMap_smul]
    exact Submodule.smul_mem _ _ <| Submodule.subset_span
      ⟨FDRep.of (irreducibleRepresentation ℂ i₀),
        (simple_iff_isIrreducible _).mpr (by rw [of_ρ']; infer_instance),
        rationalCharacter_eq_sum_filter _ i₀ (character_irreducibleRepresentation ℂ i₀)⟩
  · rw [Finset.sum_eq_zero fun i hi ↦ absurd ⟨i, (Finset.mem_filter.mp hi).2⟩ hT]
    exact zero_mem _

/-- **The irreducible rational characters are linearly independent over `ℚ`** (LMFDB
`group.representation.rational_character`): they are the sums of the irreducible characters over
the distinct Galois orbits, which are disjoint, and the irreducible characters are linearly
independent. -/
lemma linearIndepOn_irreducibleRationalCharacters :
    LinearIndepOn ℚ id (irreducibleRationalCharacters G) := by
  classical
  let _ : Fintype (irreducibleRationalCharacters G) :=
    (finite_irreducibleRationalCharacters G).fintype
  refine LinearIndependent.restrict_scalars' ℚ (K := ℂ) <|
    Fintype.linearIndependent_iff.mpr fun a ha ψ₀ ↦ ?_
  have hi (ψ : irreducibleRationalCharacters G) : ∃ i, (ψ : G → ℂ) = ∑ j with
      irreducibleCharacter ℂ j ∈ rationalClass (irreducibleCharacter ℂ i),
      irreducibleCharacter ℂ j := by
    rcases ψ.2 with ⟨X, hX, hψ⟩
    have : Simple X := hX
    rcases exists_irreducibleCharacter_eq ℂ X.character_mem_irreducibleCharacters with ⟨i, hi⟩
    exact ⟨i, hψ ▸ X.rationalCharacter_eq_sum_filter i hi.symm⟩
  choose i hi using hi
  have hmem (ψ : irreducibleRationalCharacters G) :
      irreducibleCharacter ℂ (i ψ₀) ∈ rationalClass (irreducibleCharacter ℂ (i ψ)) ↔ ψ = ψ₀ := by
    refine ⟨fun h ↦ Subtype.ext ?_, fun h ↦ h ▸ mem_rationalClass_self _⟩
    rw [hi ψ, hi ψ₀, rationalClass_eq_of_mem h]
  have h0 : ∑ j, (∑ ψ, if irreducibleCharacter ℂ j ∈ rationalClass (irreducibleCharacter ℂ (i ψ))
      then a ψ else 0) • irreducibleCharacter ℂ j = 0 := by
    rw [← ha]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ ↦ ?_
    rw [id_eq, hi ψ, Finset.smul_sum, Finset.sum_filter]
    simp only [ite_smul, zero_smul]
  simpa [hmem] using
    Fintype.linearIndependent_iff.mp (linearIndependent_irreducibleCharacter (k := ℂ)) _ h0 (i ψ₀)

variable (G) in
/-- The **`ℚ`-vector space of rational characters** of `G` (LMFDB
`group.representation.rational_character`): the `ℚ`-span of the rational characters. -/
noncomputable def rationalCharacterSpace : Submodule ℚ (G → ℂ) :=
  Submodule.span ℚ {f | ∃ Y : FDRep ℂ G, Y.IsRationalCharacter ∧ Y.character = f}

variable (G) in
/-- **The irreducible rational characters span the rational characters over `ℚ`** (LMFDB
`group.representation.rational_character`). -/
lemma span_irreducibleRationalCharacters :
    Submodule.span ℚ (irreducibleRationalCharacters G) = rationalCharacterSpace G := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨X, hX, rfl⟩
    have : Simple X := hX
    rcases X.exists_isRationalCharacter_character_eq_rationalCharacter with ⟨Y, hY, hYX⟩
    exact Submodule.subset_span ⟨Y, hY, hYX⟩
  · rintro - ⟨Y, hY, rfl⟩
    exact mem_span_irreducibleRationalCharacters hY fun x y h ↦
      hY.character_eq_of_isRationallyConj h

variable (G) in
/-- The **irreducible rational characters** of `G` (LMFDB
`group.representation.rational_character`), as a `ℚ`-basis of the `ℚ`-vector space of rational
characters. -/
noncomputable def irreducibleRationalCharacterBasis :
    Basis (irreducibleRationalCharacters G) ℚ (rationalCharacterSpace G) :=
  (Basis.span linearIndepOn_irreducibleRationalCharacters).map <|
    LinearEquiv.ofEq _ _ <| by simp [span_irreducibleRationalCharacters]

lemma coe_irreducibleRationalCharacterBasis :
    (irreducibleRationalCharacterBasis G ψ : G → ℂ) = ψ := by
  simp only [irreducibleRationalCharacterBasis]
  exact congrArg Subtype.val <| Basis.span_apply linearIndepOn_irreducibleRationalCharacters ψ

/-- **The entries of the rational character table do not depend on the representatives of the
rational classes** (LMFDB `group.rational_character_table`): the entry of `ψ` at the rational class
of `g` is `ψ(g)`, irreducible rational characters being rational characters. -/
lemma rationalCharacterTable_mk (g : G) :
    rationalCharacterTable G ψ (RatConjClasses.mk g) = (ψ : G → ℂ) g := by
  rcases ψ.2 with ⟨X, hX, hψ⟩
  have : Simple X := hX
  rcases X.exists_isRationalCharacter_character_eq_rationalCharacter with ⟨Y, hY, hYX⟩
  rw [rationalCharacterTable, ← hψ, ← hYX]
  exact hY.character_eq_of_isRationallyConj (Quotient.mk_out (s := IsRationallyConj.setoid G) g)

variable (G) in
/-- **The rational character table is square** (LMFDB `group.rational_character_table`): there
are as many irreducible rational characters as rational conjugacy classes. Their `ℚ`-span is the
space of rational valued functions constant on the rational classes, whose dimension is the number
of rational classes. -/
lemma card_irreducibleRationalCharacters :
    Nat.card (irreducibleRationalCharacters G) = Nat.card (RatConjClasses G) := by
  classical
  let _ : Fintype (irreducibleRationalCharacters G) :=
    (finite_irreducibleRationalCharacters G).fintype
  have : Finite (RatConjClasses G) := Quotient.finite _
  let _ : Fintype (RatConjClasses G) := Fintype.ofFinite _
  let Φ : (RatConjClasses G → ℚ) →ₗ[ℚ] G → ℂ :=
    { toFun := fun a g ↦ (a (RatConjClasses.mk g) : ℂ)
      map_add' := fun a b ↦ funext fun g ↦ Rat.cast_add _ _
      map_smul' := fun q a ↦ funext fun g ↦ Rat.cast_mul _ _ }
  have hΦ : Function.Injective Φ := fun a b h ↦ funext fun c ↦ by
    rcases Quotient.exists_rep c with ⟨g, rfl⟩
    exact Rat.cast_injective (congrFun h g)
  have hrange : LinearMap.range Φ = Submodule.span ℚ (irreducibleRationalCharacters G) := by
    refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
    · rintro - ⟨a, rfl⟩
      exact mem_span_irreducibleRationalCharacters (fun g ↦ ⟨a (RatConjClasses.mk g), rfl⟩)
        fun x y h ↦ congrArg (fun c ↦ (a c : ℂ)) (Quotient.sound h)
    · rintro - ⟨X, hX, rfl⟩
      have : Simple X := hX
      rcases X.exists_isRationalCharacter_character_eq_rationalCharacter with ⟨Y, hY, hYX⟩
      have hY' : ∀ g, ∃ q : ℚ, Y.character g = q := hY
      choose q hq using hY'
      refine ⟨fun c ↦ q c.out, funext fun g ↦ ?_⟩
      rw [← hYX]
      exact (hq _).symm.trans <| hY.character_eq_of_isRationallyConj <|
        Quotient.mk_out (s := IsRationallyConj.setoid G) g
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card,
    ← finrank_span_set_eq_card linearIndepOn_irreducibleRationalCharacters, ← hrange,
    LinearMap.finrank_range_of_inj hΦ, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end FDRep
