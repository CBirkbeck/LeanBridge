import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.HeckeCharpoly

/-!
# The distinguishing primes of a space of newforms

A set of Hecke operators `T_p` distinguishes the newforms of `S_k^{new}(N, χ)` (LMFDB
`cmf.distinguishing_primes`) if the characteristic polynomials of the `T_p` on the newform
subspaces `V_f` separate the Galois orbits of newforms
(`HeckeRing.GL2.Newform.DistinguishesNewforms`). The LMFDB lists a canonical sequence `p₁ < ⋯ < pₙ`
of primes not dividing `N`. Write `c(S)` for the number of distinct families
`X_f(S) = (charpoly of T_p on V_f)_{p ∈ S}` as `f` ranges over the newforms of the space; then each
`pₘ` is the least prime `p ∤ N` with `c({p₁, …, pₘ₋₁, p}) > c({p₁, …, pₘ₋₁})`, and the sequence
stops when no prime `p ∤ N` increases the count. This greedy rule is formalised here: the sequence
exists and is unique, so it is a function of the space, and it has the properties the LMFDB states.

The knowl states the rule as the strict increase of the counts `c₁, …, cₙ` with
`c_m = c({p_i : i < m})`. Read literally, this does not determine the sequence: `cₙ` does not
involve `pₙ`, and the condition holds for every sequence of primes that increase the count, for
instance the empty sequence. The least choice of each prime and the maximality of the sequence,
which make it unique, are those of the greedy rule. Equivalently, the distinguishing primes are the
primes `p ∤ N` at which the count along all the primes not dividing `N` increases, i.e. with
`c({q ∤ N : q < p}) < c({q ∤ N : q ≤ p})`.

Following `HeckeRing.GL2.Newform.DistinguishesNewforms`, the space `S_k^{new}(N, χ)` is that of the
newforms of level `N`, weight `k` and nebentypus `χ`, and the families `X_f(S)` are indexed by the
primes of `S`, so that `c(S)` is the number of classes of newforms under equality of their Hecke
characteristic polynomials at every prime of `S`. Whether the primes not dividing `N`, hence the
distinguishing primes, do distinguish the newforms is not proved here.

## Main definitions

* `HeckeRing.GL2.Newform.heckeCharpolyClassCount`: the number `c(S)` of distinct families of Hecke
  characteristic polynomials at the primes of `S`.
* `HeckeRing.GL2.Newform.IsDistinguishingPrimeSeq`: the greedy rule defining the sequence of
  distinguishing primes (LMFDB `cmf.distinguishing_primes`).
* `HeckeRing.GL2.Newform.distinguishingPrimes`: the sequence of distinguishing primes of
  `S_k^{new}(N, χ)` (LMFDB `cmf.distinguishing_primes`).

## Main results

* `HeckeRing.GL2.Newform.exists_isDistinguishingPrimeSeq`,
  `HeckeRing.GL2.Newform.IsDistinguishingPrimeSeq.eq`: the sequence of distinguishing primes exists
  and is unique.
* `HeckeRing.GL2.Newform.heckeCharpolyClassCount_take_lt`: the counts increase strictly along it.
* `HeckeRing.GL2.Newform.pairwise_lt_distinguishingPrimes`: it is strictly increasing.
* `HeckeRing.GL2.Newform.mem_distinguishingPrimes_iff`: its primes are the primes `p ∤ N` at
  which the count along all the primes not dividing `N` increases.
* `HeckeRing.GL2.Newform.length_distinguishingPrimes_lt`: its length is less than the number of
  Galois orbits of newforms in the space.
* `HeckeRing.GL2.Newform.distinguishingPrimes_eq_nil`: it is empty when the space has a single
  Galois orbit of newforms.
* `HeckeRing.GL2.Newform.distinguishesNewforms_distinguishingPrimes_iff`: its primes distinguish
  the newforms exactly when all the primes not dividing `N` do.
-/

open Polynomial

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {S T : Set Nat.Primes} {p : Nat.Primes}
  {l l' : List ℕ} {m : ℕ}

variable (N k χ S) in
/-- The number `c(S)` of distinct families of **Hecke characteristic polynomials** at the primes of
`S` (LMFDB `cmf.distinguishing_primes`): the number of families `(X_f(T_p))_{p ∈ S}` of
characteristic polynomials of the Hecke operators `T_p` on the newform subspaces `V_f`, as `f`
ranges over the newforms of `S_k^{new}(N, χ)`. -/
noncomputable def heckeCharpolyClassCount : ℕ :=
  ((fun f : Newform N k ↦ fun p : S ↦ f.heckeCharpoly p.1.2) '' {f | f.χ = χ}).ncard

private lemma image_eq_image_restrict (hST : S ⊆ T) :
    (fun f : Newform N k ↦ fun p : S ↦ f.heckeCharpoly p.1.2) '' {f | f.χ = χ} =
      (fun φ : T → ℂ[X] ↦ fun p : S ↦ φ ⟨p.1, hST p.2⟩) ''
        ((fun f : Newform N k ↦ fun p : T ↦ f.heckeCharpoly p.1.2) '' {f | f.χ = χ}) := by
  rw [Set.image_image]

lemma heckeCharpolyClassCount_le_of_subset (hST : S ⊆ T) :
    heckeCharpolyClassCount N k χ S ≤ heckeCharpolyClassCount N k χ T := by
  rw [heckeCharpolyClassCount, image_eq_image_restrict hST]
  exact Set.ncard_image_le (Set.toFinite _)

lemma heckeCharpolyClassCount_eq_iff (hST : S ⊆ T) : heckeCharpolyClassCount N k χ S =
    heckeCharpolyClassCount N k χ T ↔ ∀ f g : Newform N k, f.χ = χ → g.χ = χ →
    (∀ p ∈ S, f.heckeCharpoly p.2 = g.heckeCharpoly p.2) →
    ∀ p ∈ T, f.heckeCharpoly p.2 = g.heckeCharpoly p.2 := by
  rw [heckeCharpolyClassCount, image_eq_image_restrict hST, heckeCharpolyClassCount,
    Set.ncard_image_iff (Set.toFinite _)]
  simp only [Set.InjOn, Set.forall_mem_image, funext_iff, Subtype.forall]
  exact ⟨fun h f g hf hg ↦ h hf hg, fun h f hf g hg ↦ h f g hf hg⟩

lemma heckeCharpolyClassCount_le_insert :
    heckeCharpolyClassCount N k χ S ≤ heckeCharpolyClassCount N k χ (insert p S) :=
  heckeCharpolyClassCount_le_of_subset (Set.subset_insert p S)

lemma heckeCharpolyClassCount_insert_eq_iff : heckeCharpolyClassCount N k χ (insert p S) =
    heckeCharpolyClassCount N k χ S ↔ ∀ f g : Newform N k, f.χ = χ → g.χ = χ →
    (∀ q ∈ S, f.heckeCharpoly q.2 = g.heckeCharpoly q.2) →
    f.heckeCharpoly p.2 = g.heckeCharpoly p.2 := by
  rw [eq_comm, heckeCharpolyClassCount_eq_iff (Set.subset_insert p S)]
  simp only [Set.forall_mem_insert]
  exact ⟨fun h f g hf hg hS ↦ (h f g hf hg hS).1, fun h f g hf hg hS ↦ ⟨h f g hf hg hS, hS⟩⟩

lemma heckeCharpolyClassCount_insert_eq_of_subset
    (h : heckeCharpolyClassCount N k χ (insert p S) = heckeCharpolyClassCount N k χ S)
    (hST : S ⊆ T) : heckeCharpolyClassCount N k χ (insert p T) = heckeCharpolyClassCount N k χ T :=
  heckeCharpolyClassCount_insert_eq_iff.mpr fun f g hf hg hT ↦
    heckeCharpolyClassCount_insert_eq_iff.mp h f g hf hg fun q hq ↦ hT q (hST hq)

lemma heckeCharpolyClassCount_le_ncard :
    heckeCharpolyClassCount N k χ S ≤ {f : Newform N k | f.χ = χ}.ncard :=
  Set.ncard_image_le (Set.toFinite _)

lemma heckeCharpolyClassCount_pos_iff :
    0 < heckeCharpolyClassCount N k χ S ↔ ∃ f : Newform N k, f.χ = χ :=
  (Set.ncard_pos (Set.toFinite _)).trans Set.image_nonempty

lemma heckeCharpolyClassCount_le_ncard_newformOrbit :
    heckeCharpolyClassCount N k χ S ≤ (newformOrbit '' {f : Newform N k | f.χ = χ}).ncard := by
  have h : (fun f : Newform N k ↦ fun p : S ↦ f.heckeCharpoly p.1.2) '' {f | f.χ = χ} =
      Quotient.lift (s := galoisOrbitRel N k) (fun f : Newform N k ↦ fun p : S ↦
        f.heckeCharpoly p.1.2) (fun f g hfg ↦ funext fun p ↦ hfg.heckeCharpoly_eq p.1.2) ''
        (newformOrbit '' {f : Newform N k | f.χ = χ}) := by
    rw [Set.image_image]
    rfl
  rw [heckeCharpolyClassCount, h]
  exact Set.ncard_image_le (Set.toFinite _)

private lemma setOf_mem_append_singleton {n : ℕ} (hn : n.Prime) :
    {q : Nat.Primes | (q : ℕ) ∈ l ++ [n]} = insert ⟨n, hn⟩ {q : Nat.Primes | (q : ℕ) ∈ l} :=
  Set.ext fun _ ↦ ⟨fun h ↦ (List.mem_append.mp h).elim Or.inr fun h ↦
    Or.inl <| Subtype.ext <| List.mem_singleton.mp h, fun h ↦ List.mem_append.mpr <|
    h.elim (fun h ↦ Or.inr <| List.mem_singleton.mpr <| congrArg Subtype.val h) Or.inl⟩

variable (N k χ l) in
/-- The list `l = [p₁, …, pₙ]` of natural numbers is **the sequence of distinguishing primes** of
`S_k^{new}(N, χ)` (LMFDB `cmf.distinguishing_primes`): each `pₘ` is the least prime `p ∤ N` whose
Hecke operator increases the number `c` of distinct families of Hecke characteristic polynomials,
`c({p₁, …, pₘ₋₁, p}) > c({p₁, …, pₘ₋₁})`, and no prime `p ∤ N` increases `c({p₁, …, pₙ})`. This
is the greedy rule of the LMFDB; the knowl's own wording, that the counts increase strictly along
the sequence, does not single it out. -/
structure IsDistinguishingPrimeSeq : Prop where
  /-- Each prime of the sequence is the least prime not dividing `N` that increases the count of
  the primes before it. -/
  isLeast : ∀ (m : ℕ) (hm : m < l.length), IsLeast {n : ℕ | ∃ hn : n.Prime, ¬n ∣ N ∧
    heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ l.take m} <
      heckeCharpolyClassCount N k χ (insert ⟨n, hn⟩ {q | (q : ℕ) ∈ l.take m})} l[m]
  /-- No prime not dividing `N` increases the count of the whole sequence. -/
  insert_eq : ∀ p : Nat.Primes, ¬(p : ℕ) ∣ N →
    heckeCharpolyClassCount N k χ (insert p {q | (q : ℕ) ∈ l}) =
      heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ l}

variable (l) in
private lemma exists_isDistinguishingPrimeSeq_aux (j : ℕ)
    (hl : ∀ (m : ℕ) (hm : m < l.length), IsLeast {n : ℕ | ∃ hn : n.Prime, ¬n ∣ N ∧
      heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ l.take m} <
        heckeCharpolyClassCount N k χ (insert ⟨n, hn⟩ {q | (q : ℕ) ∈ l.take m})} l[m])
    (hj : {f : Newform N k | f.χ = χ}.ncard ≤
      heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ l} + j) :
    ∃ l : List ℕ, IsDistinguishingPrimeSeq N k χ l := by
  induction j generalizing l with
  | zero =>
    exact ⟨l, hl, fun p _ ↦ le_antisymm (heckeCharpolyClassCount_le_ncard.trans hj)
      heckeCharpolyClassCount_le_insert⟩
  | succ j ih =>
    by_cases h : ∀ p : Nat.Primes, ¬(p : ℕ) ∣ N → heckeCharpolyClassCount N k χ
        (insert p {q | (q : ℕ) ∈ l}) = heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ l}
    · exact ⟨l, hl, h⟩
    push Not at h
    rcases h with ⟨p, hpN, hp⟩
    let s : Set ℕ := {n : ℕ | ∃ hn : n.Prime, ¬n ∣ N ∧ heckeCharpolyClassCount N k χ
        {q | (q : ℕ) ∈ l} < heckeCharpolyClassCount N k χ (insert ⟨n, hn⟩ {q | (q : ℕ) ∈ l})}
    have hs : s.Nonempty := ⟨p, p.2, hpN, heckeCharpolyClassCount_le_insert.lt_of_ne' hp⟩
    rcases Nat.sInf_mem hs with ⟨hn, -, hlt⟩
    refine ih (l ++ [sInf s]) (fun m hm ↦ ?_) ?_
    · rcases Nat.lt_succ_iff.mp (by simpa using hm) |>.lt_or_eq with hm | rfl
      · rw [List.getElem_append_left hm, List.take_append_of_le_length hm.le]
        exact hl m hm
      · rw [List.getElem_concat_length rfl, List.take_left]
        exact ⟨Nat.sInf_mem hs, fun _ hn ↦ Nat.sInf_le hn⟩
    · rw [setOf_mem_append_singleton hn]
      omega

variable (N k χ) in
/-- **The sequence of distinguishing primes exists**: the greedy rule stops, as the count is
bounded by the number of newforms of the space. -/
lemma exists_isDistinguishingPrimeSeq : ∃ l : List ℕ, IsDistinguishingPrimeSeq N k χ l :=
  exists_isDistinguishingPrimeSeq_aux [] _ (fun m hm ↦ absurd hm m.not_lt_zero)
    (Nat.le_add_left _ _)

/-- **The sequence of distinguishing primes is unique**: each of its primes is the least prime with
a property of the primes before it, and it stops exactly when no prime increases the count. -/
lemma IsDistinguishingPrimeSeq.eq (hl : IsDistinguishingPrimeSeq N k χ l)
    (hl' : IsDistinguishingPrimeSeq N k χ l') : l = l' := by
  have h : ∀ m : ℕ, l.take m = l'.take m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.take_add_one, List.take_add_one, ih]
      by_cases hm : m < l.length <;> by_cases hm' : m < l'.length
      · rw [List.getElem?_eq_getElem hm, List.getElem?_eq_getElem hm',
          (hl.isLeast m hm).unique (ih ▸ hl'.isLeast m hm')]
      · rcases (hl.isLeast m hm).1 with ⟨hn, hnN, hlt⟩
        rw [ih, List.take_of_length_le (not_lt.mp hm')] at hlt
        exact (hlt.ne' (hl'.insert_eq ⟨_, hn⟩ hnN)).elim
      · rcases (hl'.isLeast m hm').1 with ⟨hn, hnN, hlt⟩
        rw [← ih, List.take_of_length_le (not_lt.mp hm)] at hlt
        exact (hlt.ne' (hl.insert_eq ⟨_, hn⟩ hnN)).elim
      · rw [List.getElem?_eq_none (not_lt.mp hm), List.getElem?_eq_none (not_lt.mp hm')]
  exact (List.take_of_length_le (le_max_left _ _)).symm.trans <|
    (h _).trans (List.take_of_length_le (le_max_right l.length l'.length))

variable (N k χ) in
/-- The **distinguishing primes** of the space `S_k^{new}(N, χ)` (LMFDB
`cmf.distinguishing_primes`): the sequence `p₁ < ⋯ < pₙ` of primes not dividing `N` in which each
`pₘ` is the least prime `p ∤ N` with `c({p₁, …, pₘ₋₁, p}) > c({p₁, …, pₘ₋₁})`, for the number `c`
of distinct families of Hecke characteristic polynomials, and after which no prime `p ∤ N`
increases the count. It is the unique list with these properties (`IsDistinguishingPrimeSeq.eq`),
and it is strictly increasing (`pairwise_lt_distinguishingPrimes`). -/
noncomputable def distinguishingPrimes : List ℕ :=
  (exists_isDistinguishingPrimeSeq N k χ).choose

lemma isDistinguishingPrimeSeq_distinguishingPrimes :
    IsDistinguishingPrimeSeq N k χ (distinguishingPrimes N k χ) :=
  (exists_isDistinguishingPrimeSeq N k χ).choose_spec

lemma isDistinguishingPrimeSeq_iff :
    IsDistinguishingPrimeSeq N k χ l ↔ l = distinguishingPrimes N k χ :=
  ⟨fun hl ↦ hl.eq isDistinguishingPrimeSeq_distinguishingPrimes,
    fun hl ↦ hl ▸ isDistinguishingPrimeSeq_distinguishingPrimes⟩

lemma prime_of_mem_distinguishingPrimes {n : ℕ} (hn : n ∈ distinguishingPrimes N k χ) :
    n.Prime := by
  rcases List.mem_iff_getElem.mp hn with ⟨m, hm, rfl⟩
  exact (isDistinguishingPrimeSeq_distinguishingPrimes.isLeast m hm).1.1

lemma not_dvd_of_mem_distinguishingPrimes {n : ℕ} (hn : n ∈ distinguishingPrimes N k χ) :
    ¬n ∣ N := by
  rcases List.mem_iff_getElem.mp hn with ⟨m, hm, rfl⟩
  exact (isDistinguishingPrimeSeq_distinguishingPrimes.isLeast m hm).1.2.1

/-- **The counts increase strictly along the distinguishing primes**: `c_m < c_{m + 1}` for the
number `c_m` of distinct families of Hecke characteristic polynomials at the first `m`
distinguishing primes, the condition of the knowl (with the counts indexed from `0`). -/
lemma heckeCharpolyClassCount_take_lt (hm : m < (distinguishingPrimes N k χ).length) :
    heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m} <
      heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take (m + 1)} := by
  rcases (isDistinguishingPrimeSeq_distinguishingPrimes.isLeast m hm).1 with ⟨hn, -, hlt⟩
  rwa [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some,
    setOf_mem_append_singleton hn]

/-- **The distinguishing primes are increasing**: a prime below `pₘ` that does not increase the
count at an earlier step does not increase it at a later one. -/
lemma pairwise_lt_distinguishingPrimes : (distinguishingPrimes N k χ).Pairwise (· < ·) := by
  have hl : IsDistinguishingPrimeSeq N k χ (distinguishingPrimes N k χ) :=
    isDistinguishingPrimeSeq_distinguishingPrimes
  refine List.pairwise_iff_getElem.mpr fun i j hi hj hij ↦ lt_of_not_ge fun hji ↦ ?_
  rcases (hl.isLeast j hj).1 with ⟨hn, hnN, hlt⟩
  rcases hji.lt_or_eq with hji | hji
  · refine hlt.ne' <| heckeCharpolyClassCount_insert_eq_of_subset (le_antisymm (not_lt.mp
      fun h ↦ hji.not_ge ((hl.isLeast i hi).2 ⟨hn, hnN, h⟩)) heckeCharpolyClassCount_le_insert)
      fun q hq ↦ List.take_subset_take_left _ hij.le hq
  · exact hlt.ne (congrArg _ (Set.insert_eq_of_mem (List.mem_take_iff_getElem.mpr
      ⟨i, lt_min hij hi, hji.symm⟩))).symm

/-- **There are fewer distinguishing primes than newforms**: the length of the sequence of
distinguishing primes of a nonzero space `S_k^{new}(N, χ)` is less than the number of Galois
orbits of newforms in it, which the LMFDB calls its newforms. -/
lemma length_distinguishingPrimes_lt (hχ : ∃ f : Newform N k, f.χ = χ) :
    (distinguishingPrimes N k χ).length < (newformOrbit '' {f : Newform N k | f.χ = χ}).ncard := by
  have h : ∀ m ≤ (distinguishingPrimes N k χ).length,
      m < heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m} := by
    intro m hm
    induction m with
    | zero => exact heckeCharpolyClassCount_pos_iff.mpr hχ
    | succ m ih =>
      exact Nat.lt_of_le_of_lt (ih (by omega)) (heckeCharpolyClassCount_take_lt (by omega))
  exact (List.take_length ▸ h _ le_rfl).trans_le heckeCharpolyClassCount_le_ncard_newformOrbit

/-- **A space with a single Galois orbit of newforms has no distinguishing primes.** -/
lemma distinguishingPrimes_eq_nil
    (h : ∀ f g : Newform N k, f.χ = χ → g.χ = χ → f.IsGaloisConjugate g) :
    distinguishingPrimes N k χ = [] := by
  refine List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos fun hl ↦ ?_)
  have hχ : ∃ f : Newform N k, f.χ = χ :=
    heckeCharpolyClassCount_pos_iff.mp (Nat.zero_lt_of_lt (heckeCharpolyClassCount_take_lt hl))
  have h₁ : (newformOrbit '' {f : Newform N k | f.χ = χ}).ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr <| by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      exact newformOrbit_eq_iff.mpr (h f g hf hg)
  exact (length_distinguishingPrimes_lt hχ).not_ge (h₁.trans hl)

/-- **The distinguishing primes distinguish the newforms exactly when all the primes not dividing
the level do**: no prime `p ∤ N` refines the classes of newforms under equality of their Hecke
characteristic polynomials at the distinguishing primes. -/
lemma distinguishesNewforms_distinguishingPrimes_iff :
    DistinguishesNewforms N k χ {p | (p : ℕ) ∈ distinguishingPrimes N k χ} ↔
      DistinguishesNewforms N k χ {p | ¬(p : ℕ) ∣ N} :=
  ⟨fun h ↦ h.mono fun _ hp ↦ not_dvd_of_mem_distinguishingPrimes hp, fun h f g hf hg hfg ↦
    h f g hf hg fun p hp ↦ heckeCharpolyClassCount_insert_eq_iff.mp
      (isDistinguishingPrimeSeq_distinguishingPrimes.insert_eq p hp) f g hf hg hfg⟩

private lemma heckeCharpolyClassCount_insert_take_eq (hm : m ≤ (distinguishingPrimes N k χ).length)
    (hpN : ¬(p : ℕ) ∣ N) (hp : ∀ h : m < (distinguishingPrimes N k χ).length,
      (p : ℕ) < (distinguishingPrimes N k χ)[m]) :
    heckeCharpolyClassCount N k χ (insert p {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m}) =
      heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m} := by
  rcases hm.lt_or_eq with hm | rfl
  · exact le_antisymm (not_lt.mp fun h ↦ (hp hm).not_ge
      ((isDistinguishingPrimeSeq_distinguishingPrimes.isLeast m hm).2 ⟨p.2, hpN, h⟩))
      heckeCharpolyClassCount_le_insert
  · rw [List.take_length]
    exact isDistinguishingPrimeSeq_distinguishingPrimes.insert_eq p hpN

private lemma exists_heckeCharpolyClassCount_insert_take_eq (hpN : ¬(p : ℕ) ∣ N)
    (hpl : (p : ℕ) ∉ distinguishingPrimes N k χ) : ∃ m ≤ (distinguishingPrimes N k χ).length,
      (∀ i < m, ∀ hi : i < (distinguishingPrimes N k χ).length,
        (distinguishingPrimes N k χ)[i] < p) ∧
      heckeCharpolyClassCount N k χ (insert p {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m}) =
        heckeCharpolyClassCount N k χ {q | (q : ℕ) ∈ (distinguishingPrimes N k χ).take m} := by
  classical
  have hex : ∃ m, m = (distinguishingPrimes N k χ).length ∨
      ∃ h : m < (distinguishingPrimes N k χ).length, (p : ℕ) < (distinguishingPrimes N k χ)[m] :=
    ⟨_, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), fun i hi hi' ↦ ?_,
    heckeCharpolyClassCount_insert_take_eq (Nat.find_min' hex (Or.inl rfl)) hpN fun h ↦ ?_⟩
  · refine (not_lt.mp fun h ↦ Nat.find_min hex hi (Or.inr ⟨hi', h⟩)).lt_of_ne fun h ↦ ?_
    exact hpl (h ▸ List.getElem_mem hi')
  · rcases Nat.find_spec hex with h' | ⟨_, h'⟩
    · exact absurd h' h.ne
    · exact h'

private lemma lt_of_getElem_distinguishingPrimes_lt {i : ℕ}
    (hi : i < (distinguishingPrimes N k χ).length) (hm : m < (distinguishingPrimes N k χ).length)
    (h : (distinguishingPrimes N k χ)[i] < (distinguishingPrimes N k χ)[m]) : i < m := by
  refine lt_of_not_ge fun him ↦ ?_
  rcases him.lt_or_eq with him | rfl
  · exact lt_asymm (List.pairwise_iff_getElem.mp pairwise_lt_distinguishingPrimes m i hm hi him) h
  · exact h.false

/-- **The distinguishing primes are the primes at which the count increases**: `n` is a
distinguishing prime of `S_k^{new}(N, χ)` exactly when it is a prime not dividing `N` whose Hecke
operator increases the number of distinct families of Hecke characteristic polynomials at the primes
`q ∤ N` below `n`. This is the reading of the knowl's rule in which the counts are taken along all
the primes not dividing `N`; it gives the same sequence as the greedy rule. -/
lemma mem_distinguishingPrimes_iff {n : ℕ} : n ∈ distinguishingPrimes N k χ ↔ ∃ hn : n.Prime,
    ¬n ∣ N ∧ heckeCharpolyClassCount N k χ {q | ¬(q : ℕ) ∣ N ∧ (q : ℕ) < n} <
      heckeCharpolyClassCount N k χ (insert ⟨n, hn⟩ {q | ¬(q : ℕ) ∣ N ∧ (q : ℕ) < n}) := by
  have hl : IsDistinguishingPrimeSeq N k χ (distinguishingPrimes N k χ) :=
    isDistinguishingPrimeSeq_distinguishingPrimes
  refine ⟨fun hn ↦ ?_, fun ⟨hp, hpN, hlt⟩ ↦ by_contra fun hpl ↦ ?_⟩
  · rcases List.mem_iff_getElem.mp hn with ⟨m, hm, rfl⟩
    rcases (hl.isLeast m hm).1 with ⟨hp, hpN, hlt⟩
    refine ⟨hp, hpN, heckeCharpolyClassCount_le_insert.lt_of_ne fun h ↦ hlt.ne' ?_⟩
    refine heckeCharpolyClassCount_insert_eq_iff.mpr fun f g hf hg hfg ↦
      heckeCharpolyClassCount_insert_eq_iff.mp h.symm f g hf hg fun q hq ↦ ?_
    by_cases hql : (q : ℕ) ∈ distinguishingPrimes N k χ
    · rcases List.mem_iff_getElem.mp hql with ⟨i, hi, hiq⟩
      exact hfg q (List.mem_take_iff_getElem.mpr ⟨i, lt_min (lt_of_getElem_distinguishingPrimes_lt
        hi hm (hiq ▸ hq.2)) hi, hiq⟩)
    · rcases exists_heckeCharpolyClassCount_insert_take_eq hq.1 hql with ⟨m', -, hlt', heq⟩
      refine heckeCharpolyClassCount_insert_eq_iff.mp heq f g hf hg fun q' hq' ↦ hfg q' ?_
      rcases List.mem_take_iff_getElem.mp hq' with ⟨i, hi, hiq⟩
      have hil : i < (distinguishingPrimes N k χ).length := hi.trans_le (min_le_right _ _)
      exact List.mem_take_iff_getElem.mpr ⟨i, lt_min (lt_of_getElem_distinguishingPrimes_lt hil hm
        ((hlt' i (hi.trans_le (min_le_left _ _)) hil).trans hq.2)) hil, hiq⟩
  · rcases exists_heckeCharpolyClassCount_insert_take_eq (p := ⟨n, hp⟩) hpN hpl with
      ⟨m', -, hlt', heq⟩
    refine hlt.ne' (heckeCharpolyClassCount_insert_eq_iff.mpr fun f g hf hg hfg ↦
      heckeCharpolyClassCount_insert_eq_iff.mp heq f g hf hg fun q hq ↦ hfg q ?_)
    rcases List.mem_take_iff_getElem.mp hq with ⟨i, hi, hiq⟩
    have hil : i < (distinguishingPrimes N k χ).length := hi.trans_le (min_le_right _ _)
    exact ⟨hiq ▸ (hl.isLeast i hil).1.2.1, hiq ▸ hlt' i (hi.trans_le (min_le_left _ _)) hil⟩

end HeckeRing.GL2.Newform
