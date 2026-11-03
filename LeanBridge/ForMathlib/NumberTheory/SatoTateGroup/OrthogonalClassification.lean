import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.KoikeTeradaMonomial
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalMonomial
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OrthogonalWeyl

/-!
# Weyl's classification of the irreducible characters of `O(d)`

An irreducible character `χ` of the ambient group `O(d)` of a Sato–Tate group of even weight has a
Weyl's monomial `c`: `χ` occurs in the monomial `∏ₖ e_{λ'ₖ}` of the partition `λ` with exponent
vector `c`, and every other monomial in which `χ` occurs has a lexicographically larger partition
(`SatoTateGroup.HasOrthogonalMonomial`). We prove Weyl's classification in this form (Weyl, *The
Classical Groups*, Chapter V; Fulton and Harris, *Representation Theory*, §19.5).

* Weyl's monomial labels the irreducible characters as Weyl's construction does: `χ` has monomial
  `c` if and only if it occurs in the image of the traceless tensors under the Young symmetrizer of
  the partition of `c`.
* Weyl's monomial is injective, unlike the highest weight of the identity component, which cannot
  separate `χ` from `χ ⊗ det`, since these have the same restriction to `SO(d)`.
* An exponent vector is Weyl's monomial of an irreducible character if and only if its partition
  satisfies `λ'₁ + λ'₂ ≤ d`.

So in even weight the order of the rows and columns of the moment matrix of a Sato–Tate group
(LMFDB `st_group.moment_matrix`), which is the order of Weyl's monomials, is a linear order.

Reading the highest weight of a character of `O(d)` as Weyl's partition is a convention of this
formalisation. The knowl's words do not force it, and the LMFDB has no data in even weight. It is
the reading in which the monomial of `χ` is again its leading term, as in odd weight: `χ` occurs in
that monomial, and every other character occurring there has a smaller partition. The highest weight
of the identity component gives a different order, and not only on its ties: on `O(2)` the order
here is `1`, `ρ₁` (`e₁`), `det` (`e₂`), `ρ₂` (`e₁²`), `ρ₃`, …, with `ρ_m` the rotations of weight
`m`, although `det` has highest weight `0`, and on `O(3)` it is `1`, `V₁`, `V₁ ⊗ det`, `det`, `V₂`,
`V₂ ⊗ det`, …, with `V_m` the representation of `SO(3)` of highest weight `m` on which `-1` acts by
`(-1)^m`.

The proof has four steps. Since `tr(C_μ M_χ)`, for the column antisymmetriser `C_μ` of `μ` and the
isotypic projector `M_χ`, computes the multiplicity of `χ` in the monomial of `μ`, the minimality of
`c` shows that `χ` occurs in the image of the Young symmetrizer of the partition of `c`, and that
the Young symmetrizer kills the cups after the projector. So `χ` occurs in Weyl's construction.
Secondly, a character occurs in Weyl's construction for at most one partition, and such a
construction contains at most one character, by the first fundamental theorem. Thirdly, Weyl's
construction is nonzero when `λ'₁ + λ'₂ ≤ d`, by an explicit tensor. Lastly, the duality
`e_{d-k} det = e_k` on `O(d)` and `det² = 1` replace two columns with `λ'₁ + λ'₂ > d` by shorter
ones, so such a monomial is not minimal.

## Main definitions

* `SatoTateGroup.columnExponent`: the exponent vector of a family of column lengths.
* `SatoTateGroup.finSuccEmbedding`: the shift of the indices.
* `SatoTateGroup.diagramColumns`: the columns of a Young diagram, as a family of lengths.
* `SatoTateGroup.orthogonalMonomialEquiv`: Weyl's classification of the irreducible characters of
  `O(d)`, as a bijection with the partitions with `λ'₁ + λ'₂ ≤ d`.

## Main results

* `SatoTateGroup.hasOrthogonalMonomial_iff_exists_traceless`: Weyl's monomial is the label of Weyl's
  construction.
* `SatoTateGroup.injective_orthogonalMonomial`: Weyl's monomial is injective on the irreducible
  characters of `O(d)`.
* `SatoTateGroup.exists_hasOrthogonalMonomial_iff`: the exponent vectors which are Weyl's monomials.
* `SatoTateGroup.isLinearOrder_isBeforeInMomentMatrix_of_even`: in even weight, the order of the
  rows and columns of the moment matrix is a linear order.
* `SatoTateGroup.IsBeforeInMomentMatrix.isLinearOrder`: so it is in all weights.
-/

open Filter Function Matrix MeasureTheory Polynomial TauCeti YoungDiagram

open scoped ComplexConjugate

namespace SatoTateGroup

variable {K : Type*} [Fintype K] {w d m : ℕ} {n n' : K → ℕ} {D : YoungDiagram} {j j' : ℕ}
  {A : Matrix (Fin d) (Fin d) ℂ} {c : Fin d → ℕ} {μ ν : m.Partition}
  {χ χ' : IrrepClass ℂ (ambientGroup w d)} {t : (Fin m → Fin d) → ℂ}

variable (n) in
/-- The exponent vector of the monomial `∏ₖ e_{n k}`: the number of columns of each length. -/
def columnExponent (i : Fin d) : ℕ :=
  (Finset.univ.filter fun k ↦ n k = (i : ℕ) + 1).card

variable (d) in
/-- The shift of the indices. -/
def finSuccEmbedding : Fin d ↪ ℕ where
  toFun j := (j : ℕ) + 1
  inj' _ _ h := Fin.ext (Nat.succ_injective h)

lemma finSuccEmbedding_apply (i : Fin d) : finSuccEmbedding d i = (i : ℕ) + 1 :=
  rfl

lemma highestWeight_columnExponent (hn : ∀ k, n k ≤ d) (i : Fin d) :
    highestWeight (columnExponent n) i = (Finset.univ.filter fun k ↦ (i : ℕ) < n k).card := by
  have h₁ : ∀ k ∈ Finset.univ.filter fun k ↦ (i : ℕ) < n k,
      n k ∈ (Finset.Ici i).map (finSuccEmbedding d) := by
    intro k hk
    have h₂ : (i : ℕ) < n k := (Finset.mem_filter.mp hk).2
    have h₃ : n k - 1 < d := by
      have h₄ : n k ≤ d := hn k
      omega
    have h₄ : ((⟨n k - 1, h₃⟩ : Fin d) : ℕ) = n k - 1 := rfl
    refine Finset.mem_map.mpr ⟨⟨n k - 1, h₃⟩, Finset.mem_Ici.mpr (Fin.le_def.mpr ?_), ?_⟩
    · omega
    · rw [finSuccEmbedding_apply]
      omega
  rw [Finset.card_eq_sum_card_fiberwise h₁, Finset.sum_map, highestWeight]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  have h₂ : (i : ℕ) ≤ l := Fin.le_def.mp (Finset.mem_Ici.mp hl)
  refine congrArg Finset.card (Finset.ext fun k ↦ ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [finSuccEmbedding_apply]
  omega

lemma prod_comp_eq_prod_pow (hn : ∀ k, n k ≤ d) (f : ℕ → ℂ) (hf : f 0 = 1) :
    ∏ k, f (n k) = ∏ i : Fin d, f ((i : ℕ) + 1) ^ columnExponent n i := by
  have h₁ : ∏ k, f (n k) = ∏ k ∈ Finset.univ.filter fun k ↦ n k ≠ 0, f (n k) :=
    (Finset.prod_filter_of_ne (p := fun k ↦ n k ≠ 0) fun k _ hk h₂ ↦ hk (by rw [h₂, hf])).symm
  have h₂ : ∀ k ∈ Finset.univ.filter fun k ↦ n k ≠ 0,
      n k ∈ (Finset.univ : Finset (Fin d)).map (finSuccEmbedding d) := by
    intro k hk
    have h₃ : n k ≠ 0 := (Finset.mem_filter.mp hk).2
    have h₄ : n k - 1 < d := by
      have h₅ : n k ≤ d := hn k
      omega
    refine Finset.mem_map.mpr ⟨⟨n k - 1, h₄⟩, Finset.mem_univ _, ?_⟩
    rw [finSuccEmbedding_apply]
    have h₅ : ((⟨n k - 1, h₄⟩ : Fin d) : ℕ) = n k - 1 := rfl
    omega
  rw [h₁, ← Finset.prod_fiberwise_of_maps_to h₂, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h₃ : (Finset.univ.filter fun k ↦ n k ≠ 0).filter (fun k ↦ n k = finSuccEmbedding d i) =
      Finset.univ.filter fun k ↦ n k = (i : ℕ) + 1 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [finSuccEmbedding_apply]
    omega
  rw [h₃, Finset.prod_congr rfl fun k hk ↦ congrArg f (Finset.mem_filter.mp hk).2,
    Finset.prod_const]
  rfl

lemma toLex_highestWeight_lt (hn : ∀ k, n k ≤ d) (h₁ : ∀ k, n' k ≤ n k) {k₀ : K}
    (h₂ : n' k₀ < n k₀) : toLex (highestWeight (columnExponent (d := d) n')) <
      toLex (highestWeight (columnExponent (d := d) n)) := by
  have hn' (k : K) : n' k ≤ d := (h₁ k).trans (hn k)
  have h₃ :
      highestWeight (columnExponent (d := d) n') < highestWeight (columnExponent (d := d) n) := by
    refine lt_of_le_of_ne (fun i ↦ ?_) fun h₄ ↦ ?_
    · rw [highestWeight_columnExponent hn', highestWeight_columnExponent hn]
      refine Finset.card_le_card fun k hk ↦ ?_
      have h₅ : (i : ℕ) < n' k := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, h₅.trans_le (h₁ k)⟩
    · have hi : n k₀ - 1 < d := by
        have h₅ : n k₀ ≤ d := hn k₀
        omega
      have h₅ : highestWeight (columnExponent (d := d) n') ⟨n k₀ - 1, hi⟩ =
          highestWeight (columnExponent (d := d) n) ⟨n k₀ - 1, hi⟩ :=
        congrFun h₄ ⟨n k₀ - 1, hi⟩
      rw [highestWeight_columnExponent hn', highestWeight_columnExponent hn] at h₅
      have h₆ : (Finset.univ.filter fun k ↦ n k₀ - 1 < n' k) ⊂
          Finset.univ.filter fun k ↦ n k₀ - 1 < n k := by
        refine ⟨fun k hk ↦ ?_, fun h₇ ↦ ?_⟩
        · have h₈ : n k₀ - 1 < n' k := (Finset.mem_filter.mp hk).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, h₈.trans_le (h₁ k)⟩
        · have h₈ : k₀ ∈ Finset.univ.filter fun k ↦ n k₀ - 1 < n k :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, by omega⟩
          have h₉ : n k₀ - 1 < n' k₀ := (Finset.mem_filter.mp (h₇ h₈)).2
          omega
      exact absurd h₅ (Finset.card_lt_card h₆).ne
  exact Pi.toLex_strictMono h₃

variable (D) in
/-- The columns of a Young diagram, as a family of lengths. -/
abbrev diagramColumns (k : Fin (D.rowLen 0)) : ℕ :=
  D.colLen k

lemma diagramColumns_le (hD : D.colLen 0 ≤ d) (k : Fin (D.rowLen 0)) : diagramColumns D k ≤ d :=
  (D.colLen_anti _ _ (Nat.zero_le _)).trans hD

lemma highestWeight_columnExponent_diagramColumns (hD : D.colLen 0 ≤ d) (i : Fin d) :
    highestWeight (columnExponent (diagramColumns D)) i = D.rowLen i := by
  rw [highestWeight_columnExponent (diagramColumns_le hD)]
  have h₁ : D.rowLen i ≤ D.rowLen 0 := D.rowLen_anti _ _ (Nat.zero_le _)
  have h₂ : (Finset.univ.filter fun k : Fin (D.rowLen 0) ↦ (i : ℕ) < diagramColumns D k) =
      (Finset.univ.filter fun k : Fin (D.rowLen 0) ↦ (k : ℕ) < D.rowLen i) := by
    simp only [← mem_iff_lt_colLen, ← mem_iff_lt_rowLen]
  rw [h₂, ← Finset.card_map Fin.valEmbedding]
  have h₃ : (Finset.univ.filter fun k : Fin (D.rowLen 0) ↦ (k : ℕ) < D.rowLen i).map
      Fin.valEmbedding = Finset.range (D.rowLen i) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨x, h.trans_le h₁⟩, h, rfl⟩⟩
    rcases h with ⟨k, hk, rfl⟩
    exact hk
  rw [h₃, Finset.card_range]

variable (c) in
lemma exists_partition_rowLen : ∃ (m : ℕ) (μ : m.Partition),
    (ofPartition μ).colLen 0 ≤ d ∧ ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i := by
  let l : List ℕ := List.ofFn (highestWeight c)
  have hl : l.SortedGE := List.sortedGE_ofFn_iff.mpr (highestWeight_antitone c)
  refine ⟨(ofRowLens l hl).card, shapePartition (ofRowLens l hl), ?_, fun i ↦ ?_⟩
  · rw [ofPartition_shapePartition]
    by_contra h
    have h₁ : (d, 0) ∈ ofRowLens l hl := mem_iff_lt_colLen.mpr (not_le.mp h)
    rcases mem_ofRowLens.mp h₁ with ⟨h₂, -⟩
    simp [l] at h₂
  · rw [ofPartition_shapePartition]
    have h₁ : (i : ℕ) < l.length := by
      simp [l]
    have h₂ : (ofRowLens l hl).rowLen (i : ℕ) = l.get ⟨i, h₁⟩ := rowLen_ofRowLens ⟨i, h₁⟩
    simpa [l] using h₂

lemma columnExponent_diagramColumns_eq (hD : D.colLen 0 ≤ d)
    (h : ∀ i : Fin d, D.rowLen i = highestWeight c i) : columnExponent (diagramColumns D) = c :=
  highestWeight_injective (funext fun i ↦
    (highestWeight_columnExponent_diagramColumns hD i).trans (h i))

lemma toLex_rowLen_lt (hd : Dominates μ ν) (hne : ν ≠ μ) (hμ : (ofPartition μ).colLen 0 ≤ d)
    (x y : Fin d → ℕ) (hx : ∀ i : Fin d, x i = (ofPartition ν).rowLen i)
    (hy : ∀ i : Fin d, y i = (ofPartition μ).rowLen i) : toLex x < toLex y := by
  have hsum (D : YoungDiagram) (k : ℕ) :
      (D.rowLens.take k).sum = ∑ i ∈ Finset.range k, D.rowLen i := by
    rw [sum_take_rowLens_eq_card_filter_fst, sum_range_rowLen_eq_card_filter_fst]
  have hdom (k : ℕ) : ∑ i ∈ Finset.range k, (ofPartition ν).rowLen i ≤
      ∑ i ∈ Finset.range k, (ofPartition μ).rowLen i := by
    rw [← hsum, ← hsum, rowLens_ofPartition_eq_sort_parts, rowLens_ofPartition_eq_sort_parts]
    exact dominates_iff.mp hd k
  have hex : ∃ i, (ofPartition ν).rowLen i ≠ (ofPartition μ).rowLen i := by
    by_contra h
    push Not at h
    exact hne (ofPartition_injective (rowLen_injective (funext h)))
  classical
  let i₀ : ℕ := Nat.find hex
  have hi₀ : (ofPartition ν).rowLen i₀ ≠ (ofPartition μ).rowLen i₀ := Nat.find_spec hex
  have hlt (i : ℕ) (hi : i < i₀) : (ofPartition ν).rowLen i = (ofPartition μ).rowLen i := by
    by_contra h
    exact Nat.find_min hex hi h
  have heq : ∑ i ∈ Finset.range i₀, (ofPartition ν).rowLen i =
      ∑ i ∈ Finset.range i₀, (ofPartition μ).rowLen i :=
    Finset.sum_congr rfl fun i hi ↦ hlt i (Finset.mem_range.mp hi)
  have hle : (ofPartition ν).rowLen i₀ ≤ (ofPartition μ).rowLen i₀ := by
    have h₁ : ∑ i ∈ Finset.range (i₀ + 1), (ofPartition ν).rowLen i ≤
        ∑ i ∈ Finset.range (i₀ + 1), (ofPartition μ).rowLen i :=
      hdom (i₀ + 1)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, heq] at h₁
    omega
  have hlt₀ : (ofPartition ν).rowLen i₀ < (ofPartition μ).rowLen i₀ := lt_of_le_of_ne hle hi₀
  have hi₀d : i₀ < d := by
    have h₁ : (i₀, 0) ∈ ofPartition μ := mem_iff_lt_rowLen.mpr (by omega)
    exact (mem_iff_lt_colLen.mp h₁).trans_le hμ
  refine ⟨⟨i₀, hi₀d⟩, fun i hi ↦ ?_, ?_⟩
  · have h₁ : (i : ℕ) < i₀ := hi
    exact (hx i).trans ((hlt i h₁).trans (hy i).symm)
  · have h₁ : x ⟨i₀, hi₀d⟩ < y ⟨i₀, hi₀d⟩ := by
      rw [hx, hy]
      exact hlt₀
    exact h₁

lemma colLen_eq_conjugateHighestWeight (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) (k : ℕ) :
    (ofPartition μ).colLen k = conjugateHighestWeight c (k + 1) := by
  refine eq_of_forall_lt_iff fun l ↦ ?_
  by_cases hl : l < d
  · have h₁ : l < conjugateHighestWeight c (k + 1) ↔ k + 1 ≤ highestWeight c ⟨l, hl⟩ :=
      lt_conjugateHighestWeight_iff c (k + 1) ⟨l, hl⟩
    rw [← hμ ⟨l, hl⟩] at h₁
    exact (mem_iff_lt_colLen.symm.trans mem_iff_lt_rowLen).trans h₁.symm
  · have h₁ : (ofPartition μ).colLen k ≤ d :=
      ((ofPartition μ).colLen_anti _ _ (Nat.zero_le _)).trans hμ₀
    have h₂ : conjugateHighestWeight c (k + 1) ≤ d := conjugateHighestWeight_le c _
    exact ⟨fun h₃ ↦ absurd (h₃.trans_le h₁) hl, fun h₃ ↦ absurd (h₃.trans_le h₂) hl⟩

lemma esymm_sub_mul_det (hA : A * Aᵀ = 1) (hj : j ≤ d) :
    A.charpoly.roots.esymm (d - j) * A.det = A.charpoly.roots.esymm j := by
  have hA' : IsUnit A := IsUnit.of_mul_eq_one _ hA
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA'
  have hP :
      A.charpoly = (-1) ^ Fintype.card (Fin d) * C (Ring.inverse A.det) * A.charpoly.reverse := by
    have h₁ : A⁻¹.charpoly = (-1) ^ Fintype.card (Fin d) * C (Ring.inverse A.det) * A.charpolyRev :=
      charpoly_inv A hA'
    rwa [inv_eq_right_inv hA, charpoly_transpose, ← reverse_charpoly] at h₁
  have hv {l : ℕ} (hl : l ≤ d) :
      A.charpoly.coeff (d - l) = (-1) ^ l * A.charpoly.roots.esymm l := by
    rw [coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits A.charpoly) (by simp),
      A.charpoly_monic.leadingCoeff, charpoly_natDegree_eq_dim, Fintype.card_fin,
      Nat.sub_sub_self hl, one_mul]
  have hrev : A.charpoly.reverse.coeff j = A.charpoly.coeff (d - j) := by
    rw [coeff_reverse, charpoly_natDegree_eq_dim, Fintype.card_fin, revAt_le hj]
  have h₂ : A.charpoly.coeff j = (-1) ^ (d - j) * A.charpoly.roots.esymm (d - j) := by
    rw [← hv (Nat.sub_le d j), Nat.sub_sub_self hj]
  have h₃ : Ring.inverse A.det * A.det = 1 := Ring.inverse_mul_cancel _ hdet
  have h₄ : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by
    rw [← mul_pow]
    simp
  have h₅ : ((-1 : ℂ) ^ (d - j)) * (-1) ^ (d - j) = 1 := by
    rw [← mul_pow]
    simp
  have h₆ : (-1 : ℂ) ^ d = (-1) ^ (d - j) * (-1) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  have h₁ : A.charpoly.coeff j =
      ((-1) ^ Fintype.card (Fin d) * C (Ring.inverse A.det) * A.charpoly.reverse).coeff j :=
    congrArg (fun p ↦ coeff p j) hP
  rw [Fintype.card_fin, ← C_1, ← C_neg, ← C_pow, ← C_mul, coeff_C_mul, hrev, h₂, hv hj, h₆] at h₁
  linear_combination ((-1 : ℂ) ^ (d - j) * A.det) * h₁ -
    A.charpoly.roots.esymm (d - j) * A.det * h₅ +
      A.charpoly.roots.esymm j * ((-1) ^ (d - j) * (-1) ^ (d - j) * (-1) ^ j * (-1) ^ j) * h₃ +
        A.charpoly.roots.esymm j * ((-1) ^ j * (-1) ^ j) * h₅ + A.charpoly.roots.esymm j * h₄

lemma esymm_sub_mul_esymm_sub (hA : A * Aᵀ = 1) (hj : j ≤ d) (hj' : j' ≤ d) :
    A.charpoly.roots.esymm (d - j) * A.charpoly.roots.esymm (d - j') =
      A.charpoly.roots.esymm j * A.charpoly.roots.esymm j' := by
  have hdet : A.det * A.det = 1 := by
    have h₁ : (A * Aᵀ).det = 1 := by
      rw [hA, det_one]
    rwa [det_mul, det_transpose] at h₁
  rw [← esymm_sub_mul_det hA hj, ← esymm_sub_mul_det hA hj']
  linear_combination
    -(A.charpoly.roots.esymm (d - j) * A.charpoly.roots.esymm (d - j')) * hdet

lemma ambientMonomial_columnExponent (hn : ∀ k, n k ≤ d) (g : ambientGroup w d) :
    ambientMonomial (columnExponent n) g =
      ∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm (n k) :=
  (prod_comp_eq_prod_pow hn (fun l ↦ (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm l)
    (Multiset.esymm_zero _)).symm

variable (n) in
lemma HasOrthogonalMonomial.integral_prod_esymm_eq_zero (hc : HasOrthogonalMonomial χ c)
    (h : (∀ k, n k ≤ d) → toLex (highestWeight (columnExponent (d := d) n)) <
      toLex (highestWeight c)) : ∫ g : ambientGroup w d,
        (∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm (n k)) *
          conj (ambientCharacter w d χ g) ∂haarProb (ambientGroup w d) = 0 := by
  by_cases hn : ∀ k, n k ≤ d
  · by_contra h₀
    have h₁ : OccursInMonomial χ (columnExponent n) := by
      simpa only [OccursInMonomial, ambientMonomial_columnExponent hn] using h₀
    exact absurd (hc.2 _ h₁) (not_le.mpr (h hn))
  · push Not at hn
    rcases hn with ⟨k₀, hk₀⟩
    refine integral_eq_zero_of_ae (Eventually.of_forall fun g ↦ ?_)
    have h₁ : ∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm (n k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k₀)
        (esymm_roots_charpoly_eq_zero _ (by rwa [Fintype.card_fin]))
    simp only [h₁, zero_mul, Pi.zero_apply]

variable [DecidableEq K] in
lemma HasOrthogonalMonomial.add_le (hw : Even w) (hc : HasOrthogonalMonomial χ (columnExponent n))
    (hn : ∀ k, n k ≤ d) {k₀ k₁ : K} (hk : k₀ ≠ k₁) : n k₀ + n k₁ ≤ d := by
  by_contra hlt
  push Not at hlt
  let n' : K → ℕ := update (update n k₀ (d - n k₁)) k₁ (d - n k₀)
  have h₀ : n' k₀ = d - n k₁ := (update_of_ne hk _ _).trans (update_self ..)
  have h₁ : n' k₁ = d - n k₀ := update_self ..
  have h₂ (r : {r // r ≠ k₀ ∧ r ≠ k₁}) : n' r = n r :=
    (update_of_ne r.2.2 _ _).trans (update_of_ne r.2.1 _ _)
  have hle (k : K) : n' k ≤ n k := by
    by_cases hk₁ : k = k₁
    · rw [hk₁, h₁]
      omega
    · by_cases hk₀ : k = k₀
      · rw [hk₀, h₀]
        omega
      · exact (h₂ ⟨k, hk₀, hk₁⟩).le
  have hlt₀ : n' k₀ < n k₀ := by
    have h₃ : n k₁ ≤ d := hn k₁
    rw [h₀]
    omega
  refine hc.1 ?_
  simp only [ambientMonomial_columnExponent hn]
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun g ↦ ?_))
    (hc.integral_prod_esymm_eq_zero n' fun _ ↦ toLex_highestWeight_lt hn hle hlt₀)
  beta_reduce
  rw [prod_eq_mul_mul_prod_subtype hk, prod_eq_mul_mul_prod_subtype hk, h₀, h₁]
  simp only [h₂]
  rw [← mul_assoc, ← mul_assoc,
    ← esymm_sub_mul_esymm_sub (mul_transpose_self_ambient hw g) (hn k₀) (hn k₁)]
  ring1

variable (χ ν) in
lemma columnOp_mul_isotypicMatrix_eq_zero_iff_partition :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol ν) *
      (isotypicMatrix χ : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ).mulVecLin = 0 ↔
      ∫ g : ambientGroup w d, (∏ k, (g : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm
        (diagramColumns (ofPartition ν) k)) * conj (ambientCharacter w d χ g)
          ∂haarProb (ambientGroup w d) = 0 := by
  rw [columnOp_mul_isotypicMatrix_eq_zero_iff]
  simp only [card_partitionCol]

lemma HasOrthogonalMonomial.columnOp_mul_ne_zero (hc : HasOrthogonalMonomial χ c)
    (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) *
      (isotypicMatrix χ : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ).mulVecLin ≠ 0 := by
  intro h₀
  refine hc.1 ?_
  rw [← columnExponent_diagramColumns_eq hμ₀ hμ]
  simp only [ambientMonomial_columnExponent (diagramColumns_le hμ₀)]
  exact (columnOp_mul_isotypicMatrix_eq_zero_iff_partition μ χ).mp h₀

lemma HasOrthogonalMonomial.columnOp_mul_eq_zero (hc : HasOrthogonalMonomial χ c)
    (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) (hd : Dominates μ ν)
    (hne : ν ≠ μ) : columnOp (slotRep (Fin m) (Fin d)) (partitionCol ν) *
      (isotypicMatrix χ : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ).mulVecLin = 0 := by
  rw [columnOp_mul_isotypicMatrix_eq_zero_iff_partition]
  refine hc.integral_prod_esymm_eq_zero _ fun hn ↦ ?_
  have hν₀ : (ofPartition ν).colLen 0 ≤ d := by
    by_cases h₀ : (ofPartition ν).rowLen 0 = 0
    · have h₁ : (0, 0) ∉ ofPartition ν := fun h₂ ↦ by
        have h₃ : 0 < (ofPartition ν).rowLen 0 := mem_iff_lt_rowLen.mp h₂
        omega
      have h₂ : (ofPartition ν).colLen 0 = 0 := by
        by_contra h₃
        exact h₁ (mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h₃))
      omega
    · exact hn ⟨0, Nat.pos_of_ne_zero h₀⟩
  exact toLex_rowLen_lt hd hne hμ₀ _ _ (highestWeight_columnExponent_diagramColumns hν₀)
    fun i ↦ (hμ i).symm

lemma HasOrthogonalMonomial.columnOp_isotypicMatrix_mulVec_eq_zero (hw : Even w)
    (hc : HasOrthogonalMonomial χ c) (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) {p q : Fin m} (hpq : p ≠ q)
    (ht : IsCupAt p q t) :
    columnOp (slotRep (Fin m) (Fin d)) (partitionCol μ) (isotypicMatrix χ *ᵥ t) = 0 := by
  rcases ht.exists_eq_cupMap with ⟨y, rfl⟩
  rw [isotypicMatrix_mulVec_cupMap χ hw hpq]
  refine columnOp_cupMap_eq_zero (partitionCol μ) hpq fun _ ↦ ?_
  let col' : {r : Fin m // r ≠ p ∧ r ≠ q} → Fin ((ofPartition μ).rowLen 0) :=
    fun r ↦ partitionCol μ r.1
  have h₁ :
      columnOp (slotRep _ (Fin d)) col' * (isotypicMatrix χ : Matrix _ _ ℂ).mulVecLin = 0 := by
    refine (columnOp_mul_isotypicMatrix_eq_zero_iff χ col').mpr
      (hc.integral_prod_esymm_eq_zero _ fun _ ↦ ?_)
    rw [← columnExponent_diagramColumns_eq hμ₀ hμ]
    have hle (k : Fin ((ofPartition μ).rowLen 0)) :
        Fintype.card {r // col' r = k} ≤ diagramColumns (ofPartition μ) k := by
      rw [diagramColumns, ← card_partitionCol μ k]
      exact Fintype.card_le_of_injective (fun r ↦ ⟨r.1.1, r.2⟩) fun r r' h ↦
        Subtype.ext (Subtype.ext (congrArg (fun x ↦ (x.1 : Fin m)) h))
    have hlt : Fintype.card {r // col' r = partitionCol μ p} <
        diagramColumns (ofPartition μ) (partitionCol μ p) := by
      rw [diagramColumns, ← card_partitionCol μ]
      refine Fintype.card_lt_of_injective_of_notMem (fun r ↦ ⟨r.1.1, r.2⟩) (b := ⟨p, rfl⟩)
        (fun r r' h ↦ Subtype.ext (Subtype.ext (congrArg (fun x ↦ (x.1 : Fin m)) h))) ?_
      rintro ⟨r, hr⟩
      exact r.1.2.1 (congrArg (fun x ↦ (x.1 : Fin m)) hr)
    exact toLex_highestWeight_lt (diagramColumns_le hμ₀) hle hlt
  exact LinearMap.congr_fun h₁ _

lemma HasOrthogonalMonomial.youngOp_isotypicMatrix_mulVec_eq_zero (hw : Even w)
    (hc : HasOrthogonalMonomial χ c) (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i)
    (ht : t ∈ cupSpan (Fin m) (Fin d)) : youngOp d μ (isotypicMatrix χ *ᵥ t) = 0 := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨p, q, hpq, hx⟩
    rw [youngOp_apply, hc.columnOp_isotypicMatrix_mulVec_eq_zero hw hμ₀ hμ hpq hx, map_zero]
  | zero => rw [mulVec_zero, map_zero]
  | add x y _ _ hx hy => rw [mulVec_add, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [mulVec_smul, map_smul, hx, smul_zero]

lemma HasOrthogonalMonomial.exists_traceless (hw : Even w) (hc : HasOrthogonalMonomial χ c)
    (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) :
    ∃ h ∈ traceless (Fin m) (Fin d), isotypicMatrix χ *ᵥ youngOp d μ h ≠ 0 := by
  have h₁ :
      youngOp d μ * (isotypicMatrix χ : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ).mulVecLin ≠ 0 :=
    asAlgebraHom_youngSymmetrizer_mul_ne_zero _ (commute_mulVecLin_slotRep χ)
      (hc.columnOp_mul_ne_zero hμ₀ hμ) fun ν hd hne ↦ hc.columnOp_mul_eq_zero hμ₀ hμ hd hne
  rcases DFunLike.ne_iff.mp h₁ with ⟨f, hf⟩
  rcases exists_eq_add_traceless_cupSpan f with ⟨h, hh, c', hc', rfl⟩
  refine ⟨h, hh, fun h₀ ↦ hf ?_⟩
  have h₂ : youngOp d μ (isotypicMatrix χ *ᵥ h) = 0 := by
    rw [youngOp_isotypicMatrix_mulVec, h₀]
  have h₃ : (youngOp d μ *
      (isotypicMatrix χ : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ).mulVecLin) (h + c') =
        youngOp d μ (isotypicMatrix χ *ᵥ (h + c')) :=
    rfl
  rw [h₃, mulVec_add, map_add, h₂, hc.youngOp_isotypicMatrix_mulVec_eq_zero hw hμ₀ hμ hc', add_zero]
  rfl

lemma hasOrthogonalMonomial_of_traceless (hw : Even w)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i)
    (ht : t ∈ traceless (Fin m) (Fin d)) (hne : isotypicMatrix χ *ᵥ youngOp d μ t ≠ 0) :
    HasOrthogonalMonomial χ c := by
  rcases exists_partition_rowLen (orthogonalMonomial χ hw) with ⟨m₀, μ₀, hμ₀', hμ'⟩
  rcases (hasOrthogonalMonomial_orthogonalMonomial χ hw).exists_traceless hw hμ₀' hμ' with
    ⟨h₀, hh₀, hne₀⟩
  have h₁ : ofPartition μ₀ = ofPartition μ := ofPartition_eq_of_traceless hw hh₀ ht hne₀ hne
  have h₂ : orthogonalMonomial χ hw = c := highestWeight_injective (funext fun i ↦ by
    rw [← hμ' i, ← hμ i, h₁])
  exact h₂ ▸ hasOrthogonalMonomial_orthogonalMonomial χ hw

/-- **Weyl's monomial labels the irreducible characters of `O(d)` as Weyl's construction does**: the
character `χ` has monomial `c` if and only if it occurs in the image of the traceless tensors under
the Young symmetrizer of the partition of `c`. -/
lemma hasOrthogonalMonomial_iff_exists_traceless (hw : Even w) (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) : HasOrthogonalMonomial χ c ↔
      ∃ h ∈ traceless (Fin m) (Fin d), isotypicMatrix χ *ᵥ youngOp d μ h ≠ 0 :=
  ⟨fun hc ↦ hc.exists_traceless hw hμ₀ hμ, fun ⟨_, ht, hne⟩ ↦
    hasOrthogonalMonomial_of_traceless hw hμ ht hne⟩

/-- **Weyl's monomial is injective on the irreducible characters of `O(d)`.** -/
lemma injective_orthogonalMonomial (hw : Even w) :
    Injective fun χ : IrrepClass ℂ (ambientGroup w d) ↦ orthogonalMonomial χ hw := by
  intro χ χ' he
  have hc : HasOrthogonalMonomial χ (orthogonalMonomial χ hw) :=
    hasOrthogonalMonomial_orthogonalMonomial χ hw
  have hc' : HasOrthogonalMonomial χ' (orthogonalMonomial χ hw) := by
    have h₁ : orthogonalMonomial χ hw = orthogonalMonomial χ' hw := he
    rw [h₁]
    exact hasOrthogonalMonomial_orthogonalMonomial χ' hw
  rcases exists_partition_rowLen (orthogonalMonomial χ hw) with ⟨m, μ, hμ₀, hμ⟩
  rcases hc.exists_traceless hw hμ₀ hμ with ⟨h, hh, hne⟩
  rcases hc'.exists_traceless hw hμ₀ hμ with ⟨h', hh', hne'⟩
  exact eq_of_traceless hw hh hh' hne hne'

lemma HasOrthogonalMonomial.colLen_add_colLen_le (hw : Even w) (hc : HasOrthogonalMonomial χ c)
    (hμ₀ : (ofPartition μ).colLen 0 ≤ d)
    (hμ : ∀ i : Fin d, (ofPartition μ).rowLen i = highestWeight c i) :
    (ofPartition μ).colLen 0 + (ofPartition μ).colLen 1 ≤ d := by
  by_contra hlt
  push Not at hlt
  have hb : 0 < (ofPartition μ).colLen 1 := by
    omega
  have h₁ : 1 < (ofPartition μ).rowLen 0 := mem_iff_lt_rowLen.mp (mem_iff_lt_colLen.mpr hb)
  rw [← columnExponent_diagramColumns_eq hμ₀ hμ] at hc
  exact absurd (hc.add_le hw (diagramColumns_le hμ₀) (k₀ := ⟨0, by omega⟩) (k₁ := ⟨1, h₁⟩)
    (by simp)) (not_le.mpr hlt)

variable (c) in
/-- **Weyl's classification of the partitions labelling the irreducible characters of `O(d)`**: an
exponent vector is Weyl's monomial of an irreducible character of `O(d)` if and only if its
partition `λ` satisfies `λ'₁ + λ'₂ ≤ d`. -/
lemma exists_hasOrthogonalMonomial_iff (hw : Even w) :
    (∃ χ : IrrepClass ℂ (ambientGroup w d), HasOrthogonalMonomial χ c) ↔
      conjugateHighestWeight c 1 + conjugateHighestWeight c 2 ≤ d := by
  rcases exists_partition_rowLen c with ⟨m, μ, hμ₀, hμ⟩
  rw [← colLen_eq_conjugateHighestWeight hμ₀ hμ 0, ← colLen_eq_conjugateHighestWeight hμ₀ hμ 1]
  refine ⟨fun ⟨χ, hχ⟩ ↦ hχ.colLen_add_colLen_le hw hμ₀ hμ, fun hd ↦ ?_⟩
  rcases exists_isotypicMatrix_mulVec_ne_zero (w := w)
    (youngOp_columnOp_weylTensor_ne_zero μ hd) with ⟨χ, hχ⟩
  exact ⟨χ, hasOrthogonalMonomial_of_traceless hw hμ (columnOp_weylTensor_mem_traceless μ hd) hχ⟩

variable (w d) in
/-- **Weyl's classification of the irreducible characters of `O(d)`**: Weyl's monomial is a
bijection from them to the partitions `λ` with `λ'₁ + λ'₂ ≤ d`, given by their exponent vectors. -/
noncomputable def orthogonalMonomialEquiv (hw : Even w) : IrrepClass ℂ (ambientGroup w d) ≃
    {c : Fin d → ℕ // conjugateHighestWeight c 1 + conjugateHighestWeight c 2 ≤ d} :=
  .ofBijective (fun χ ↦ ⟨orthogonalMonomial χ hw, (exists_hasOrthogonalMonomial_iff _ hw).mp
      ⟨χ, hasOrthogonalMonomial_orthogonalMonomial χ hw⟩⟩)
    ⟨fun _ _ h ↦ injective_orthogonalMonomial hw (congrArg Subtype.val h), fun c ↦ by
      rcases (exists_hasOrthogonalMonomial_iff c.1 hw).mpr c.2 with ⟨χ, hχ⟩
      exact ⟨χ, Subtype.ext ((hasOrthogonalMonomial_orthogonalMonomial χ hw).eq hχ)⟩⟩

variable (χ) in
lemma coe_orthogonalMonomialEquiv (hw : Even w) :
    (orthogonalMonomialEquiv w d hw χ : Fin d → ℕ) = orthogonalMonomial χ hw :=
  rfl

variable {G : SatoTateGroup}

/-- **In even weight, the order of the rows and columns of the moment matrix is a linear order.** -/
lemma isLinearOrder_isBeforeInMomentMatrix_of_even (hG : Even G.weight) :
    IsLinearOrder (IrrepClass ℂ (ambientGroup G.weight G.degree)) G.IsBeforeInMomentMatrix := by
  rw [isBeforeInMomentMatrix_eq_invImage hG]
  exact InvImage.isLinearOrder (injective_orthogonalMonomial hG)

variable (G) in
/-- **The order of the rows and columns of the moment matrix is a linear order, in all weights.** -/
lemma IsBeforeInMomentMatrix.isLinearOrder :
    IsLinearOrder (IrrepClass ℂ (ambientGroup G.weight G.degree)) G.IsBeforeInMomentMatrix :=
  (Nat.even_or_odd G.weight).elim isLinearOrder_isBeforeInMomentMatrix_of_even
    (isLinearOrder_isBeforeInMomentMatrix G)

end SatoTateGroup
