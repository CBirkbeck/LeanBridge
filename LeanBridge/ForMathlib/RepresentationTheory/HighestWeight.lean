import TauCeti.RepresentationTheory.ClassicalGroups.Weight.HighestWeight
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight

/-!
# The highest weight of a representation of `GL(n, ℂ)`

A weight of a representation `ρ` of `GL(n, ℂ)` is a tuple `l ∈ ℤⁿ` such that some nonzero vector `v`
satisfies `ρ(diag(a₁, …, aₙ)) v = a₁ ^ l₁ ⋯ aₙ ^ lₙ • v` (Tau Ceti's `TauCeti.weightSpace`). The
LMFDB knowl `repn.highest.weight` defines the highest weight of an irreducible finite-dimensional
representation as the unique dominant weight `λ₁ ≥ ⋯ ≥ λₙ` of a line `⟨v₀⟩`. As stated, that
uniqueness fails: in `Sym²(ℂ²)` both `(2, 0)` and `(1, 1)` are dominant weights. The intended `v₀`
is a highest weight vector, also fixed by the upper unitriangular matrices, and the representation
is implicitly rational (holomorphic).

We define the highest weight of a representation as its lexicographically largest weight. For a
nonzero rational representation it is dominant and is the weight of a highest weight vector; for
the rational Weyl module `V_λ` (Tau Ceti's `TauCeti.rationalWeylRep`), irreducible by Tau Ceti, it
is `λ`, so it is the highest weight in the usual sense on every representation isomorphic to some
`V_λ`. The determinant and the standard representation have highest weights `(1, …, 1)` and
`(1, 0, …, 0)`, as in the knowl. That every irreducible rational representation is isomorphic to
some `V_λ`, equivalently has a unique highest weight line, is not proved.

## Main definitions

* `Representation.IsGLHighestWeightVector`: a highest weight vector.
* `Representation.highestWeight` (LMFDB `repn.highest.weight`).

## Main results

* `Representation.highestWeight_eq_of_equiv`: the highest weight is an isomorphism invariant.
* `Representation.antitone_highestWeight`: the highest weight of a nonzero rational representation
  is dominant.
* `Representation.exists_isGLHighestWeightVector_highestWeight`: it is the weight of a highest
  weight vector.
* `Representation.highestWeight_rationalWeylRep`: the highest weight of `V_λ` is `λ`.
* `Representation.highestWeight_detPowerRep` and `Representation.highestWeight_stdRep`: the highest
  weights of the powers of the determinant and of the standard representation.
-/

open Finset Matrix TauCeti

namespace Representation

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (GL (Fin n) ℂ) W)

/-- A **highest weight vector** of weight `l` of a representation `ρ` of `GL(n, ℂ)`: a nonzero
vector `v` of weight `l`, that is, `ρ(diag(a₁, …, aₙ)) v = a₁ ^ l₁ ⋯ aₙ ^ lₙ • v`, fixed by every
upper unitriangular transvection. -/
def IsGLHighestWeightVector (v : W) (l : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ v ∈ weightSpace ρ l ∧
    ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) v = v

open scoped Classical in
/-- The **highest weight** of a representation `ρ` of `GL(n, ℂ)` (LMFDB `repn.highest.weight`):
the lexicographically largest weight of `ρ`, or `0` if `ρ` has none.

For a nonzero rational representation, this weight is dominant and is the weight of a highest
weight vector (`Representation.exists_isGLHighestWeightVector_highestWeight`), and for the rational
Weyl module `V_λ` it is `λ` (`Representation.highestWeight_rationalWeylRep`). -/
noncomputable def highestWeight : Fin n → ℤ :=
  if h : ∃ l, weightSpace ρ l ≠ ⊥ ∧ ∀ l', weightSpace ρ l' ≠ ⊥ → toLex l' ≤ toLex l then
    h.choose else 0

variable {ρ} {l : Fin n → ℤ} (hl : weightSpace ρ l ≠ ⊥)

include hl in
lemma highestWeight_eq (hmax : ∀ l', weightSpace ρ l' ≠ ⊥ → toLex l' ≤ toLex l) :
    ρ.highestWeight = l := by
  rw [highestWeight]
  split_ifs with hex
  · exact toLex.injective <| le_antisymm (hmax _ hex.choose_spec.1) (hex.choose_spec.2 l hl)
  · exact absurd ⟨l, hl, hmax⟩ hex

/-- **The highest weight is an isomorphism invariant**, since isomorphic representations have the
same weights. -/
lemma highestWeight_eq_of_equiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ (GL (Fin n) ℂ) V} (e : ρ.Equiv σ) :
    ρ.highestWeight = σ.highestWeight := by
  have he (l : Fin n → ℤ) : weightSpace ρ l ≠ ⊥ ↔ weightSpace σ l ≠ ⊥ :=
    (e.weightSpace_eq_bot_iff l).not
  rw [highestWeight]
  split_ifs with hρ
  · exact (highestWeight_eq ((he _).mp hρ.choose_spec.1) fun l' hl' ↦
      hρ.choose_spec.2 l' ((he l').mpr hl')).symm
  · rw [highestWeight]
    split_ifs with hσ
    · exact absurd ⟨_, (he _).mpr hσ.choose_spec.1, fun l' hl' ↦
        hσ.choose_spec.2 l' ((he l').mp hl')⟩ hρ
    · rfl

variable (h : IsRationalRep ρ) [Nontrivial W]

include h in
private lemma exists_weightSpace_ne_bot_forall_toLex_le :
    ∃ l, weightSpace ρ l ≠ ⊥ ∧ ∀ l', weightSpace ρ l' ≠ ⊥ → toLex l' ≤ toLex l := by
  have : Module.Finite ℂ W := h.finite
  exact Set.exists_max_image _ toLex (finite_setOf_weightSpace_ne_bot weightChar_injective ρ)
    h.exists_weightSpace_ne_bot

include h in
lemma weightSpace_highestWeight_ne_bot : weightSpace ρ ρ.highestWeight ≠ ⊥ := by
  rcases exists_weightSpace_ne_bot_forall_toLex_le h with ⟨l, hl, hmax⟩
  rwa [highestWeight_eq hl hmax]

include h hl in
lemma toLex_le_highestWeight : toLex l ≤ toLex ρ.highestWeight := by
  rcases exists_weightSpace_ne_bot_forall_toLex_le h with ⟨l₀, hl₀, hmax⟩
  rw [highestWeight_eq hl₀ hmax]
  exact hmax l hl

include h in
/-- **The highest weight of a nonzero rational representation is dominant**: transposing two
entries in increasing position gives another weight, which would otherwise be lexicographically
larger. -/
lemma antitone_highestWeight : Antitone ρ.highestWeight := by
  intro a b hab
  rcases hab.lt_or_eq with hab | rfl
  · have hw : weightSpace ρ (ρ.highestWeight ∘ Equiv.swap a b) ≠ ⊥ :=
      (weightSpace_eq_bot_comp_perm_iff ρ _ _).not.mpr (weightSpace_highestWeight_ne_bot h)
    simpa using Pi.apply_le_of_toLex (toLex_le_highestWeight hw h) (i := a) fun j hj ↦ by
      simp [Equiv.swap_apply_of_ne_of_ne hj.ne (hj.trans hab).ne]
  · exact le_rfl

include h in
/-- **The highest weight of a nonzero rational representation is the weight of a highest weight
vector**: a vector of the lexicographically largest weight is fixed by the upper unitriangular
transvections, which raise weights. -/
lemma exists_isGLHighestWeightVector_highestWeight :
    ∃ v, ρ.IsGLHighestWeightVector v ρ.highestWeight := by
  rcases (Submodule.ne_bot_iff _).mp (weightSpace_highestWeight_ne_bot h) with ⟨v, hv, hv0⟩
  refine ⟨v, hv0, hv, fun i j hij c ↦ h.apply_transvectionUnit_eq_self hij.ne hv
    (fun m hm ↦ ?_) c⟩
  by_contra hne
  have hi :
      (ρ.highestWeight + m • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) i ≤ ρ.highestWeight i :=
    Pi.apply_le_of_toLex (toLex_le_highestWeight hne h) fun k hk ↦ by
      simp [hk.ne, (hk.trans hij).ne]
  simp [hij.ne] at hi
  omega

private lemma toLex_le_of_forall_sum_le {a b : Fin n → ℤ} (hab : ∀ m : ℕ,
    ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < m, a j ≤
      ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < m, b j) : toLex a ≤ toLex b := by
  refine not_lt.mp fun ⟨i, hi, hlt⟩ ↦ ?_
  have hset : (univ.filter fun j : Fin n ↦ (j : ℕ) < i + 1) =
      insert i (univ.filter fun j : Fin n ↦ (j : ℕ) < i) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    omega
  have hsum : ∑ j ∈ univ.filter (fun j : Fin n ↦ (j : ℕ) < i), b j =
      ∑ j ∈ univ.filter (fun j : Fin n ↦ (j : ℕ) < i), a j :=
    sum_congr rfl fun j hj ↦ hi j (by simpa using hj)
  have hi' : i ∉ univ.filter fun j : Fin n ↦ (j : ℕ) < i := by
    simp
  refine absurd (hab (i + 1)) ?_
  rw [hset, sum_insert hi', sum_insert hi', hsum]
  exact not_le.mpr (add_lt_add_left hlt _)

/-- **The highest weight of the rational Weyl module `V_λ` is `λ`**: `λ` is a weight of `V_λ` and
dominates all of its weights, hence is lexicographically largest. -/
lemma highestWeight_rationalWeylRep (l : DominantWeight n) :
    highestWeight (W := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
      (rationalWeylRep ℂ n l) = l.1 :=
  highestWeight_eq (weightSpace_rationalWeylRep_self_ne_bot ℂ l) fun _ ha ↦
    toLex_le_of_forall_sum_le (sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ha)

/-- **The highest weight of `det ^ m` is `(m, …, m)`**; for `m = 1` this is the knowl's
`(1, …, 1)`. -/
lemma highestWeight_detPowerRep (m : ℤ) : (detPowerRep ℂ n m).highestWeight = fun _ ↦ m := by
  have hm : weightSpace (detPowerRep ℂ n m) (fun _ ↦ m) = ⊤ := weightSpace_detPowerRep m
  refine highestWeight_eq (hm ▸ top_ne_bot) fun l hl ↦ le_of_eq ?_
  by_contra hne
  have hd :
      Disjoint (weightSpace (detPowerRep ℂ n m) l) (weightSpace (detPowerRep ℂ n m) fun _ ↦ m) :=
    (iSupIndep_weightSpace weightChar_injective _).pairwiseDisjoint fun h ↦ hne (congrArg toLex h)
  rw [hm] at hd
  exact hl (disjoint_top.mp hd)

/-- **The highest weight of the standard representation is `(1, 0, …, 0)`.** -/
lemma highestWeight_stdRep : (stdRep ℂ (n + 1)).highestWeight = Pi.single 0 1 := by
  refine highestWeight_eq ?_ fun l hl ↦ ?_
  · rw [weightSpace_stdRep_single weightChar_injective, Ne, Submodule.span_singleton_eq_bot]
    exact (Pi.basisFun ℂ (Fin (n + 1))).ne_zero 0
  · have hi : ∃ i, l = Pi.single i 1 := by
      by_contra h
      exact hl (weightSpace_stdRep_eq_bot weightChar_injective fun i hi ↦ h ⟨i, hi⟩)
    rcases hi with ⟨i, rfl⟩
    rcases eq_or_ne i 0 with rfl | hi
    · exact le_rfl
    · exact le_of_lt (⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), by simp [hi]⟩ :
        Pi.Lex (· < ·) (· < ·) (Pi.single i 1 : Fin (n + 1) → ℤ) (Pi.single 0 1))

end Representation
