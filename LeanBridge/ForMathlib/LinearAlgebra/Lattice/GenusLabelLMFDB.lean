import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum

/-!
# The label of a genus of integral lattices, as the LMFDB computes it

The LMFDB labels a genus of nondegenerate integral lattices (LMFDB `lattice.genus_label`) by a
string `r.s.d.j₁.⋯.jₖ.x`. The labels are computed by `create_genus_label` in `lattices/genus.py`
of <https://github.com/jvoight/k3s-lmfdb> (with Sage's genus symbols; `CreateGenusLabel` in
`lattices/create_label.m` is its Magma port), and the LMFDB's own test-suite
(`lmfdb/lattice/test_lattice.py` on the branch `alpha` of <https://github.com/LMFDB/lmfdb>,
2026-08-04) records labels of the data together with Gram matrices or determinants. These sources
settle the conventions that the knowl leaves open, and correct its example.

* `s` is the signature `n₊ - n₋`, as the knowl says and as in the labels of the LMFDB data: the
  lattice `3.1.1.3.1` has the Gram matrix `[[0, 0, 1], [0, 1, 0], [1, 0, 1]]`, of signature
  `(2, 1)`, and the lattices `3.1.d.⋯` of the tests have negative determinants (`-1000` for
  `3.1.1000.3.3.3b.1`), so `n₊ = 2` and `n₋ = 1`. Since 2026-06-16 (commit `dc4e0db`) the code of
  k3s-lmfdb, like its Magma port, writes `n₊` there instead: the two agree exactly for the positive
  definite genera, and the labels of the other genera would change if the data were computed again
  with that code.
* `jᵢ` is the string of base `62` digits of the ranks `n_v` of the Jordan constituents of scale
  `pᵢ ^ v` for `1 ≤ v ≤ m`, `m` being the largest scale exponent of a nonzero constituent: only
  `n₀`, which is `r` minus the others, is omitted, as the text of the knowl says. The knowl's
  example is wrong: the pairs (valuation, rank) `(3, 1), (4, 10), (6, 37)` are encoded as `001a0B`,
  not `01a0B`, which omits `n₁` as well. The LMFDB labels `9.9.8.001.76` (`v₂(d) = 3`, so `m ≤ 3`,
  and a rank code of length `3`) and `3.1.1000.3.3.3b` (`d = 2³ 5³` and both rank codes `3`, that
  is `n₁ = 3`) cannot omit `n₁`. The encoding `TauCeti.IntegralLattice.GenusLabelData.label` omits
  `n₁`, following the example; `TauCeti.IntegralLattice.GenusLabelData.lmfdbLabel` corrects its rank
  code, and for a lattice the two agree exactly when no square of a prime divides `d`.
* The binary digits of the number written in lowercase hexadecimal as `x` are, from the least
  significant: a `1` for each nonzero dyadic Jordan constituent of type `I` (`0` for type `II`);
  the oddity of each compartment of the canonical `2`-adic symbol, by its three binary digits from
  the least significant; a `1` for each train of sign `-1`, the sign of its first constituent in
  the canonical symbol, that is the product of the signs of its constituents; and, for the odd
  primes dividing `d` in increasing order, a `1` for each nonzero Jordan constituent of sign `-1`,
  by increasing scale. These are the conventions of
  `TauCeti.IntegralLattice.GenusLabelData.labelBits`.

The examples at the end check the encoding on genera of the LMFDB data whose Gram matrices or
determinants the test-suite gives, among them `2.2.10.7b` (an oddity `6`, written `0, 1, 1`) and
`2.2.100.01.01.627` (sign walking, rank codes at `2` and `5`). Decoded with these conventions, each
of the twenty-one genus labels of the test-suite is that of a symbol satisfying the conditions on
the signs and Conway and Sloane's oddity formula, while the other choices fail: the reversed bit
order of the oddities on `2.2.10.7b`, the other bit value of the types on `9.9.8.001.76` (a
constituent of rank `1` and type `II`), of the signs on `3.3.5.77`, and `s = n₊` on
`5.1.648.3.4.46`.

## Main definitions

* `TauCeti.IntegralLattice.GenusLabelData.lmfdbRankCode`: the rank code at a prime in the label.
* `TauCeti.IntegralLattice.GenusLabelData.lmfdbLabel` (LMFDB `lattice.genus_label`): the label
  with these rank codes.
* `TauCeti.IntegralLattice.lmfdbGenusLabel` (LMFDB `lattice.genus_label`): the label of the genus
  of a lattice.

## Main results

* `TauCeti.IntegralLattice.GenusLabelData.toList_rankCode`: the rank code of
  `TauCeti.IntegralLattice.GenusLabelData.label` is the LMFDB rank code without its first digit.
* `TauCeti.IntegralLattice.GenusLabelData.lmfdbLabel_eq_label`: the two labels agree when no square
  of a prime divides `d`.
* `TauCeti.IntegralLattice.SameGenus.lmfdbGenusLabel_eq`: the label is a genus invariant.
* `TauCeti.IntegralLattice.lmfdbGenusLabel_eq_canonicalGenusLabel`: it agrees with
  `TauCeti.IntegralLattice.canonicalGenusLabel` for lattices of squarefree determinant.
* `TauCeti.IntegralLattice.lmfdbGenusLabel_eq_canonicalGenusLabel_iff`: and only for them.
* `TauCeti.IntegralLattice.finsum_jordanRank`: the ranks of the Jordan constituents at a prime add
  up to the rank.
* `TauCeti.IntegralLattice.jordanRank_zero_add_sum_eq_rank`: so the label determines the rank `n₀`
  that its rank codes omit.
-/

open Module

namespace TauCeti.IntegralLattice

namespace GenusLabelData

variable (D : GenusLabelData) (p : ℕ)

/-- The **rank code** at `p` in the label of a genus (LMFDB `lattice.genus_label`): the base `62`
digits of the ranks `n_v` of the Jordan constituents of scale `p ^ v`, `1 ≤ v ≤ m`, where `m` is the
largest scale exponent of a nonzero constituent. -/
def lmfdbRankCode : String :=
  .ofList <| (List.range' 1 ((D.blocks p).getLast?.getD 0)).map (base62Digit <| D.jordanRank p ·)

/-- The **label of a genus** (LMFDB `lattice.genus_label`), `r.s.d.j₁.⋯.jₖ.x`, as the LMFDB
computes it: the rank, the signature `n₊ - n₋`, the absolute determinant, the rank codes
`lmfdbRankCode` at the primes `p` with `p ^ 2 ∣ d`, and the lowercase hexadecimal expansion of the
number with binary digits `labelBits`, from the least significant. -/
def lmfdbLabel : String :=
  s!"{D.rank}.{D.signature}.{D.absDet}" ++
    .join (D.labelPrimes.map fun q ↦ "." ++ D.lmfdbRankCode q) ++ "." ++
    .ofList (Nat.toDigits 16 (D.labelBits.foldr (fun b n ↦ 2 * n + b.toNat) 0))

/-- **The rank code of `label` is the LMFDB rank code without its first digit**, the rank `n₁`. -/
lemma toList_rankCode : (D.rankCode p).toList = (D.lmfdbRankCode p).toList.tail := by
  rw [rankCode, lmfdbRankCode, String.toList_ofList, String.toList_ofList, ← List.map_tail,
    List.tail_range']

/-- **The two labels agree when no square of a prime divides the determinant.** -/
lemma lmfdbLabel_eq_label (h : D.labelPrimes = []) : D.lmfdbLabel = D.label := by
  rw [lmfdbLabel, label, h, List.map_nil, List.map_nil]

lemma le_getD_getLast?_blocks {v : ℕ} (hv : v ∈ D.blocks p) : v ≤ (D.blocks p).getLast?.getD 0 := by
  rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hv), Option.getD_some]
  exact (List.pairwise_le_range.filter _).rel_getLast hv

lemma length_lmfdbRankCode : (D.lmfdbRankCode p).length = (D.blocks p).getLast?.getD 0 := by
  rw [lmfdbRankCode, String.length_ofList, List.length_map, List.length_range']

lemma length_lmfdbLabel (h : ∀ q ∈ D.labelPrimes, (D.blocks q).getLast?.getD 0 ≠ 0) :
    D.lmfdbLabel.length = D.label.length + D.labelPrimes.length := by
  have hcode (q : ℕ) (hq : q ∈ D.labelPrimes) :
      ".".length + (D.lmfdbRankCode q).length = ".".length + (D.rankCode q).length + 1 := by
    rw [add_assoc, Nat.add_left_cancel_iff, D.length_lmfdbRankCode, rankCode, String.length_ofList,
      List.length_map, List.length_range', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (h q hq))]
  have hsum : (D.labelPrimes.map fun q ↦ ".".length + (D.lmfdbRankCode q).length).sum =
      (D.labelPrimes.map fun q ↦ ".".length + (D.rankCode q).length).sum +
        D.labelPrimes.length := by
    rw [List.map_congr_left hcode, List.sum_map_add, List.map_const', List.sum_replicate,
      smul_eq_mul, mul_one]
  simp only [lmfdbLabel, label, String.length_append, String.length_join, List.map_map,
    Function.comp_def]
  omega

end GenusLabelData

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
  (oddity : ℕ → ZMod 8) (trainSign : ℕ → ℤ) {q : ℕ}

variable (L) in
/-- The **label of the genus** (LMFDB `lattice.genus_label`) of a nondegenerate integral lattice
`L`, `r.s.d.j₁.⋯.jₖ.x`, as the LMFDB computes it: the encoding
`TauCeti.IntegralLattice.GenusLabelData.lmfdbLabel` of its rank, signature, absolute determinant,
Jordan ranks, signs at the odd primes, dyadic types, and the oddities of the compartments and the
signs of the trains of its canonical `2`-adic symbol. -/
noncomputable def lmfdbGenusLabel : String :=
  (L.genusLabelData (L.compartmentOddities.getD · 0) (L.trainSigns.getD · 1)).lmfdbLabel

/-- **The label of the genus is a genus invariant** (LMFDB `lattice.genus_label`): lattices in the
same genus have the same label. -/
lemma SameGenus.lmfdbGenusLabel_eq (h : L.SameGenus M) : L.lmfdbGenusLabel = M.lmfdbGenusLabel := by
  rw [lmfdbGenusLabel, lmfdbGenusLabel, h.compartmentOddities_eq, h.trainSigns_eq,
    h.genusLabelData_eq]

/-- **The label agrees with `canonicalGenusLabel` for a squarefree determinant**, when the label
has no rank code. -/
lemma lmfdbGenusLabel_eq_canonicalGenusLabel (hL : Squarefree L.determinant.natAbs) :
    L.lmfdbGenusLabel = L.canonicalGenusLabel :=
  GenusLabelData.lmfdbLabel_eq_label _ <| List.filter_eq_nil_iff.mpr fun q hq hq2 ↦
    (Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp hq)).not_isUnit <|
      hL q (sq q ▸ of_decide_eq_true hq2)

variable (L) in
lemma natAbs_determinant_ne_zero : L.determinant.natAbs ≠ 0 :=
  Int.natAbs_ne_zero.mpr <| L.determinant_ne_zero_iff.mpr L.form_nondegenerate

variable [Fact q.Prime] in
lemma le_getD_getLast?_blocks_genusLabelData {v : ℕ} (hv : L.jordanRank q v ≠ 0) :
    v ≤ ((L.genusLabelData oddity trainSign).blocks q).getLast?.getD 0 :=
  (L.genusLabelData oddity trainSign).le_getD_getLast?_blocks q <| by
    simpa [GenusLabelData.blocks, genusLabelData, (Fact.out : q.Prime), hv] using
      not_lt.mp fun hlt ↦ hv (L.jordanRank_eq_zero_of_lt q hlt)

lemma getD_getLast?_blocks_ne_zero (hq : q ∈ (L.genusLabelData oddity trainSign).labelPrimes) :
    ((L.genusLabelData oddity trainSign).blocks q).getLast?.getD 0 ≠ 0 := by
  rcases List.mem_filter.mp hq with ⟨hq1, hq2⟩
  have hprime : q.Prime := Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp hq1)
  have : Fact q.Prime := ⟨hprime⟩
  intro h0
  have hzero (v : ℕ) (hv : v ≠ 0) : L.jordanRank q v = 0 := by
    by_contra hne
    have hle : v ≤ ((L.genusLabelData oddity trainSign).blocks q).getLast?.getD 0 :=
      le_getD_getLast?_blocks_genusLabelData oddity trainSign hne
    omega
  have hfac : L.determinant.natAbs.factorization q = 0 := by
    rw [L.factorization_natAbs_determinant q]
    refine finsum_eq_zero_of_forall_eq_zero fun k ↦ ?_
    rcases eq_or_ne k 0 with rfl | hk
    · exact zero_mul _
    · rw [hzero k hk, mul_zero]
  have h2 : 2 ≤ L.determinant.natAbs.factorization q :=
    (hprime.pow_dvd_iff_le_factorization L.natAbs_determinant_ne_zero).mp (of_decide_eq_true hq2)
  omega

/-- **The label `canonicalGenusLabel` is the LMFDB label exactly for a squarefree determinant**:
when the square of a prime divides the determinant, its rank codes lack the rank `n₁`. -/
lemma lmfdbGenusLabel_eq_canonicalGenusLabel_iff :
    L.lmfdbGenusLabel = L.canonicalGenusLabel ↔ Squarefree L.determinant.natAbs := by
  refine ⟨fun h ↦ Nat.squarefree_iff_prime_squarefree.mpr fun q hq hqq ↦ ?_,
    lmfdbGenusLabel_eq_canonicalGenusLabel⟩
  have hmem :
      q ∈ (L.genusLabelData (L.compartmentOddities.getD · 0) (L.trainSigns.getD · 1)).labelPrimes :=
    List.mem_filter.mpr ⟨List.mem_dedup.mpr <| Nat.mem_primeFactorsList'.mpr ⟨hq,
      (dvd_mul_right q q).trans hqq, L.natAbs_determinant_ne_zero⟩, decide_eq_true <| sq q ▸ hqq⟩
  have hlen : L.lmfdbGenusLabel.length = L.canonicalGenusLabel.length := congrArg String.length h
  rw [lmfdbGenusLabel, canonicalGenusLabel, genusLabel, GenusLabelData.length_lmfdbLabel _
    fun _ ↦ getD_getLast?_blocks_ne_zero _ _] at hlen
  exact List.ne_nil_of_mem hmem <| List.length_eq_zero_iff.mp <| by omega

variable (L q) [Fact q.Prime] in
/-- **The ranks of the Jordan constituents add up to the rank**: at every prime `q`, the ranks
`n_k` of the constituents of scale `q ^ k` of a nondegenerate integral lattice sum to its rank. -/
lemma finsum_jordanRank : ∑ᶠ k, L.jordanRank q k = finrank ℤ L := by
  let N : ℕ → Submodule ℤ_[q] (L.LocalCarrier q) :=
    (L.exists_isJordanSplitting_localIntegralForm q L.form_nondegenerate).choose
  have h : (L.localIntegralForm q).IsJordanSplitting ((q : ℕ) : ℤ_[q]) N :=
    (L.exists_isJordanSplitting_localIntegralForm q L.form_nondegenerate).choose_spec
  rcases h.exists_forall_eq_bot with ⟨J, hJ⟩
  have hzero (k : ℕ) (hk : J ≤ k) : L.jordanRank q k = 0 := by
    rw [jordanRank_eq q k h, hJ k hk, finrank_bot]
  have hrank : finrank ℤ_[q] (L.LocalCarrier q) = finrank ℤ L :=
    (finrank_eq_card_basis ((Free.chooseBasis ℤ L).baseChange ℤ_[q])).trans
      (finrank_eq_card_chooseBasisIndex ℤ L).symm
  rw [finsum_eq_sum_of_support_subset _ fun k hk ↦ Finset.mem_coe.mpr <| Finset.mem_range.mpr <|
    by_contra fun hkJ ↦ hk (hzero k (not_lt.mp hkJ)),
    ← Fin.sum_univ_eq_sum_range, ← hrank, finrank_eq_card_basis (h.adaptedBasis hJ),
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rfl

variable (L) in
/-- **The label determines the rank `n₀` that its rank codes omit**: at a prime `q`, the rank `r`
of the lattice is `n₀` plus the sum of the ranks `n₁, …, n_m` listed by the rank code at `q`. -/
lemma jordanRank_zero_add_sum_eq_rank (hq : q.Prime) :
    letI D : GenusLabelData := L.genusLabelData oddity trainSign
    D.jordanRank q 0 + ((List.range' 1 ((D.blocks q).getLast?.getD 0)).map (D.jordanRank q)).sum =
      D.rank := by
  have : Fact q.Prime := ⟨hq⟩
  have hsum (f : ℕ → ℕ) (m : ℕ) :
      ((List.range' 1 m).map f).sum = ∑ i ∈ Finset.range m, f (i + 1) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range'_concat, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
        List.map_singleton, List.sum_singleton, one_mul, add_comm 1 m]
  have hD (v : ℕ) : (L.genusLabelData oddity trainSign).jordanRank q v = L.jordanRank q v :=
    dite_eq_left hq
  simp only [hsum, hD]
  rw [add_comm, ← Finset.sum_range_succ']
  exact (finsum_eq_sum_of_support_subset _ fun k hk ↦ Finset.mem_coe.mpr <| Finset.mem_range.mpr <|
    Nat.lt_succ_of_le <| le_getD_getLast?_blocks_genusLabelData oddity trainSign hk).symm.trans
    (L.finsum_jordanRank q)

/-!
### Examples

Labels of the LMFDB data (`lmfdb/lattice/test_lattice.py`, branch `alpha`), with the genus symbols
computed by hand from the Gram matrices given there: `⟨1⟩` (lattice `1.1.1.3.1`),
`[[0, 0, 1], [0, 1, 0], [1, 0, 1]]` of signature `(2, 1)` (`3.1.1.3.1`), `⟨1, 1, 1⟩` (`3.3.1.7.1`),
`⟨2, 5⟩` (`2.2.10.7b.1`), `[[5, 2], [2, 7]]` (`2.2.31.1.2`), `[[8, 2], [2, 13]]`
(`2.2.100.01.01.627.1`) and `⟨45⟩` (`1.1.45.01.3b.1`, the only lattice of rank `1` and determinant
`45`); and the labels `3.1.1000.3.3.3b` and `3.1.8.001.6`, of determinants `-1000` and `-8` there,
which are the labels of `⟨10, 10, -10⟩` and of `U ⊕ ⟨8⟩`, `U` the hyperbolic plane. Where a square
of a prime divides the determinant, `label` differs. Last, the knowl's example of a rank code. The
data are listed in the order of the fields of `TauCeti.IntegralLattice.GenusLabelData`: rank,
signature, absolute determinant, Jordan ranks, signs at the odd primes, dyadic types, oddities of
the compartments and signs of the trains.
-/

example : (⟨1, 1, 1, fun _ v ↦ if v = 0 then 1 else 0, fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 1,
    fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel = "1.1.1.3" := by
  decide +kernel

example : (⟨3, 1, 1, fun _ v ↦ if v = 0 then 3 else 0, fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 1,
    fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel = "3.1.1.3" := by
  decide +kernel

example : (⟨3, 3, 1, fun _ v ↦ if v = 0 then 3 else 0, fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 3,
    fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel = "3.3.1.7" := by
  decide +kernel

example : (⟨2, 2, 10, fun _ v ↦ if v ≤ 1 then 1 else 0, fun _ v ↦ if v = 0 then -1 else 1,
    fun _ ↦ .I, fun _ ↦ 6, fun _ ↦ -1⟩ : GenusLabelData).lmfdbLabel = "2.2.10.7b" := by
  decide +kernel

example : (⟨2, 2, 31, fun p v ↦ if p = 2 then if v = 0 then 2 else 0 else if v ≤ 1 then 1 else 0,
    fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 0, fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel = "2.2.31.1" := by
  decide +kernel

example : (⟨2, 2, 100, fun _ v ↦ if v = 0 ∨ v = 2 then 1 else 0, fun _ _ ↦ -1, fun _ ↦ .I,
    fun _ ↦ 1, fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel = "2.2.100.01.01.627" := by
  decide +kernel

example : (⟨2, 2, 100, fun _ v ↦ if v = 0 ∨ v = 2 then 1 else 0, fun _ _ ↦ -1, fun _ ↦ .I,
    fun _ ↦ 1, fun _ ↦ 1⟩ : GenusLabelData).label = "2.2.100.1.1.627" := by
  decide +kernel

example : (⟨1, 1, 45, fun p v ↦ if v = (45 : ℕ).factorization p then 1 else 0,
    fun p _ ↦ if p = 3 then -1 else 1, fun _ ↦ .I, fun _ ↦ 5, fun _ ↦ -1⟩ :
      GenusLabelData).lmfdbLabel = "1.1.45.01.3b" := by
  decide +kernel

example : (⟨3, 1, 1000, fun _ v ↦ if v = 1 then 3 else 0, fun _ _ ↦ -1, fun _ ↦ .I, fun _ ↦ 5,
    fun _ ↦ -1⟩ : GenusLabelData).lmfdbLabel = "3.1.1000.3.3.3b" := by
  decide +kernel

example : (⟨3, 1, 1000, fun _ v ↦ if v = 1 then 3 else 0, fun _ _ ↦ -1, fun _ ↦ .I, fun _ ↦ 5,
    fun _ ↦ -1⟩ : GenusLabelData).label = "3.1.1000...3b" := by
  decide +kernel

example : (⟨3, 1, 8, fun _ v ↦ if v = 0 then 2 else if v = 3 then 1 else 0, fun _ _ ↦ 1,
    fun v ↦ if v = 0 then .II else .I, fun _ ↦ 1, fun _ ↦ 1⟩ : GenusLabelData).lmfdbLabel =
      "3.1.8.001.6" := by
  decide +kernel

example : (⟨3, 1, 8, fun _ v ↦ if v = 0 then 2 else if v = 3 then 1 else 0, fun _ _ ↦ 1,
    fun v ↦ if v = 0 then .II else .I, fun _ ↦ 1, fun _ ↦ 1⟩ : GenusLabelData).label =
      "3.1.8.01.6" := by
  decide +kernel

example : (⟨48, 48, 2 ^ 265, fun _ v ↦ if v = 3 then 1 else if v = 4 then 10 else if v = 6 then 37
    else 0, fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 0, fun _ ↦ 1⟩ : GenusLabelData).lmfdbRankCode 2 =
      "001a0B" := by
  decide +kernel

example : (⟨48, 48, 2 ^ 265, fun _ v ↦ if v = 3 then 1 else if v = 4 then 10 else if v = 6 then 37
    else 0, fun _ _ ↦ 1, fun _ ↦ .I, fun _ ↦ 0, fun _ ↦ 1⟩ : GenusLabelData).rankCode 2 =
      "01a0B" := by
  decide +kernel

end TauCeti.IntegralLattice
