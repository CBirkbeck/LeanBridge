import LeanBridge.ForMathlib.Algebra.Module.ZLattice.PerfectArithmetic
import LeanBridge.ForMathlib.Algebra.Module.ZLattice.SimilarityInvariant
import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet

/-!
# Voronoi's finiteness theorem for perfect lattices

There are only finitely many similarity classes of perfect lattices of `ℝⁿ` (LMFDB
`lattice.perfect`), for every `n`.

Let `L` be a perfect lattice of `ℝⁿ` with minimal norm `m`. Its minimal vectors span `ℝⁿ`, so
some of them, `b₁, …, bₙ`, form a basis of `ℝⁿ`. Write `K = (n + 1)ⁿ`.

* For every `y ∈ L` there is an integer `1 ≤ q ≤ K` such that the coordinates of `q y` in the basis
  `b` are integers. By Dirichlet's simultaneous approximation theorem (Tau Ceti's
  `TauCeti.simultaneous_dirichlet`) the coordinates of `q y` are within `1 / (n + 1)` of integers
  `rᵢ` for some such `q`; then `q y - ∑ rᵢ bᵢ` is a vector of `L` of norm less than `m`, so it is
  zero.
* The coordinates of a minimal vector `y` have absolute value at most `K`: if the `i`-th one, `t`,
  is not zero, the same argument for the vector `bᵢ` and the vectors `y` and `bⱼ`, `j ≠ i`, gives
  `q bᵢ = r y + ∑ rⱼ bⱼ` with integers `r` and `rⱼ`, so `q = r t` and `|t| ≤ q`.

So the coordinate vectors of the minimal vectors of `L`, and those of the vectors of `L` with
coordinates in `[0, 1)`, lie in a finite set `ZLattice.coordBox` depending only on `n`, and they
determine the coordinate vectors of `L`. If two perfect lattices `L` and `L'` with such bases have
the same two sets of coordinate vectors, the linear map taking one basis to the other carries `L`
onto `L'` and the minimal vectors of `L` onto those of `L'`, so it is a similitude, because a
perfect lattice is determined by its minimal vectors
(`ZLattice.IsPerfect.isSimilarLattice_of_mapsTo`). Hence there are at most as many similarity
classes as pairs of subsets of that finite set.

## Main definitions

* `ZLattice.coordBound`: the bound `K = (n + 1)ⁿ`.
* `ZLattice.coordBox`: the finite set of the coordinate vectors with entries `a / K!`, `a ∈ ℤ`,
  of absolute value at most `K`.
* `ZLattice.perfectSimilaritySetoid`: similarity, as an equivalence relation on the perfect
  lattices of `ℝⁿ`.

## Main results

* `ZLattice.exists_nsmul_eq_sum_zsmul`: in a lattice with minimal norm at least `m`, a real linear
  combination `w ∈ L` of `k` vectors of `L` of norm at most `m` has a multiple `q w`,
  `1 ≤ q ≤ (k + 1)ᵏ`, that is an integral linear combination of them.
* `ZLattice.IsPerfect.exists_basis_mem_minimalVectors`: a perfect lattice has a basis of `ℝⁿ`
  consisting of minimal vectors.
* `ZLattice.finite_quotient_perfectSimilaritySetoid` (LMFDB `lattice.perfect`): Voronoi's
  finiteness theorem.
* `ZLattice.exists_finite_forall_isPerfect_exists_isSimilarLattice` (LMFDB `lattice.perfect`):
  finitely many perfect lattices of `ℝⁿ` represent all of them up to similarity.

## References

* G. Voronoi, *Nouvelles applications des paramètres continus à la théorie des formes
  quadratiques. Premier mémoire*, J. Reine Angew. Math. 133 (1908), 97–178.
* J. Martinet, *Perfect Lattices in Euclidean Spaces*, Springer, 2003, Theorem 3.5.4.
-/

open Module Set

open scoped InnerProductSpace

open LinearMap (BilinForm)

namespace ZLattice

/-- The **coordinate bound** `K = (n + 1)ⁿ` of dimension `n`, the cardinality of `J`: it bounds the
coordinates of the minimal vectors of a lattice of `ℝⁿ` in a basis of minimal vectors, and the
denominators of the coordinates of all its vectors. -/
def coordBound (J : Type*) [Fintype J] : ℕ :=
  (Fintype.card J + 1) ^ Fintype.card J

section Frame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {m : ℝ}
  {J : Type*} [Fintype J] {v : J → E} {w : E}

/-- **A multiple of a real linear combination of short vectors of a lattice is an integral linear
combination of them**: if the nonzero vectors of `L` have norm at least `m > 0`, the `k` vectors
`vⱼ ∈ L` have norm at most `m`, and `w ∈ L` is a real linear combination `∑ uⱼ vⱼ` of them, then
`q w = ∑ rⱼ vⱼ` for integers `rⱼ` and `1 ≤ q ≤ (k + 1)ᵏ`. By Dirichlet's theorem the `q uⱼ` are
simultaneously within `1 / (k + 1)` of integers `rⱼ`, and then `q w - ∑ rⱼ vⱼ ∈ L` has norm less
than `m`. -/
lemma exists_nsmul_eq_sum_zsmul (hm : 0 < m) (hL : ∀ z ∈ L, z ≠ 0 → m ≤ ‖z‖) (hv : ∀ j, v j ∈ L)
    (hvm : ∀ j, ‖v j‖ ≤ m) (hw : w ∈ L) (hwv : w ∈ Submodule.span ℝ (range v)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ coordBound J ∧ ∃ r : J → ℤ, q • w = ∑ j, r j • v j := by
  rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwv with ⟨u, hu⟩
  rcases isEmpty_or_nonempty J with _ | _
  · refine ⟨1, one_pos, by simp [coordBound], fun _ ↦ 0, ?_⟩
    rw [← hu]
    simp
  rcases TauCeti.simultaneous_dirichlet u (Q := Fintype.card J + 1)
    (by simpa using Fintype.card_pos (α := J)) with ⟨r, y, hy, hyQ, hr⟩
  lift y to ℕ using hy.le
  have hz : y • w - ∑ j, r j • v j = ∑ j, (u j * y - r j) • v j := by
    rw [← hu, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sub_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]
  have hnorm : ‖y • w - ∑ j, r j • v j‖ < m := by
    rw [hz]
    refine (norm_sum_le _ _).trans_lt ((Finset.sum_le_card_nsmul _ _
      (((Fintype.card J : ℝ) + 1)⁻¹ * m) fun j _ ↦ ?_).trans_lt ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_sub_comm]
      exact mul_le_mul (hr j) (hvm j) (norm_nonneg _) (by positivity)
    · rw [Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
      refine mul_lt_of_lt_one_left hm ?_
      rw [mul_inv_lt_iff₀ (by positivity)]
      linarith
  have h0 : y • w - ∑ j, r j • v j = 0 := by
    by_contra h
    exact hnorm.not_ge <| hL _ (L.sub_mem (L.smul_of_tower_mem y hw)
      (L.sum_mem fun j _ ↦ L.smul_mem (r j) (hv j))) h
  exact ⟨y, by exact_mod_cast hy, by exact_mod_cast hyQ, r, sub_eq_zero.mp h0⟩

variable {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) {y : E}

lemma exists_nat_mul_repr_eq_intCast (hb : ∀ i, b i ∈ minimalVectors L) (hy : y ∈ L) :
    ∃ q : ℕ, 0 < q ∧ q ≤ coordBound ι ∧ ∀ i, ∃ a : ℤ, q * b.repr y i = a := by
  classical
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_pos, by simp [coordBound], fun i ↦ isEmptyElim i⟩
  rcases exists_nsmul_eq_sum_zsmul (minimum_pos_of_mem_minimalVectors (hb i₀))
    (fun z hz hz₀ ↦ minimum_le_norm hz hz₀) (fun i ↦ (hb i).1) (fun i ↦ (hb i).2.2.le) hy
    (b.mem_span y) with ⟨q, hq, hqn, r, hr⟩
  refine ⟨q, hq, hqn, fun i ↦ ⟨r i, ?_⟩⟩
  have h : b.repr (q • y) i = b.repr (∑ j, r j • b j) i := by
    rw [hr]
  simpa [Finsupp.single_apply] using h

lemma abs_repr_le_coordBound (hb : ∀ i, b i ∈ minimalVectors L) (hy : y ∈ L) (hym : ‖y‖ ≤ minimum L)
    (i : ι) : |b.repr y i| ≤ coordBound ι := by
  classical
  rcases eq_or_ne (b.repr y i) 0 with h0 | h0
  · rw [h0, abs_zero]
    positivity
  have hu : ∑ j, (if j = i then (b.repr y i)⁻¹ else -((b.repr y i)⁻¹ * b.repr y j)) •
      (if j = i then y else b j) = b i := by
    have hterm (j : ι) : (if j = i then (b.repr y i)⁻¹ else -((b.repr y i)⁻¹ * b.repr y j)) •
        (if j = i then y else b j) = (if j = i then (b.repr y i)⁻¹ • y + b i else 0) -
          (b.repr y i)⁻¹ • b.repr y j • b j := by
      rcases eq_or_ne j i with rfl | hj
      · rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, smul_smul, inv_mul_cancel₀ h0,
          one_smul, add_sub_cancel_right]
      · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj, neg_smul, zero_sub, mul_smul]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_univ i), ← Finset.smul_sum, b.sum_repr, add_sub_cancel_left]
  rcases exists_nsmul_eq_sum_zsmul (minimum_pos_of_mem_minimalVectors (hb i))
    (fun z hz hz₀ ↦ minimum_le_norm hz hz₀) (v := fun j ↦ if j = i then y else b j)
    (fun j ↦ by split_ifs; exacts [hy, (hb j).1])
    (fun j ↦ by split_ifs; exacts [hym, (hb j).2.2.le]) (hb i).1
    ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨_, hu⟩) with ⟨q, hq, hqn, r, hr⟩
  have hqr : (q : ℝ) = r i * b.repr y i := by
    have h : b.repr (q • b i) i = b.repr (∑ j, r j • if j = i then y else b j) i := by
      rw [hr]
    rw [map_nsmul, Finsupp.smul_apply, b.repr_self, Finsupp.single_eq_same, nsmul_eq_mul, mul_one,
      map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i (fun j _ hj ↦ ?_)
      fun hi ↦ absurd (Finset.mem_univ i) hi, ite_eq_left rfl, map_zsmul, Finsupp.smul_apply,
      zsmul_eq_mul] at h
    · exact h
    · rw [ite_eq_right hj, map_zsmul, Finsupp.smul_apply, b.repr_self,
        Finsupp.single_eq_of_ne' hj, smul_zero]
  have hr1 : (1 : ℝ) ≤ |(r i : ℝ)| := by
    have hri : r i ≠ 0 := by
      rintro hri
      rw [hri, Int.cast_zero, zero_mul] at hqr
      exact hq.ne' (by exact_mod_cast hqr)
    exact_mod_cast Int.one_le_abs hri
  refine (le_mul_of_one_le_left (abs_nonneg _) hr1).trans ?_
  rw [← abs_mul, ← hqr, Nat.abs_cast]
  exact_mod_cast hqn

variable (ι) in
/-- The **coordinate box** of dimension `n`: the finite set (`ZLattice.finite_coordBox`) of the
vectors of `ℝⁿ` whose entries are the numbers `a / K!`, `a ∈ ℤ`, of absolute value at most
`K = (n + 1)ⁿ` (`ZLattice.coordBound`). In a basis of `ℝⁿ` consisting of minimal vectors of a
lattice `L`, it contains the coordinate vectors of the minimal vectors of `L` and of the vectors
of `L` with coordinates in `[0, 1)`. -/
def coordBox : Set (ι → ℝ) :=
  {t | ∀ i, |t i| ≤ coordBound ι ∧ ∃ a : ℤ, ((coordBound ι).factorial : ℝ) * t i = a}

lemma finite_coordBox : (coordBox ι).Finite := by
  have hbox : (univ.pi fun _ : ι ↦ Icc (-((coordBound ι).factorial * coordBound ι : ℤ))
      ((coordBound ι).factorial * coordBound ι)).Finite :=
    Finite.pi fun _ ↦ finite_Icc _ _
  refine (hbox.image fun (a : ι → ℤ) i ↦ (a i : ℝ) / (coordBound ι).factorial).subset
    fun t ht ↦ ?_
  choose a ha using fun i ↦ (ht i).2
  refine ⟨a, fun i _ ↦ ?_, funext fun i ↦ ?_⟩
  · have h : |(a i : ℝ)| ≤ (coordBound ι).factorial * (coordBound ι : ℝ) := by
      rw [← ha i, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (ht i).1 (Nat.cast_nonneg _)
    exact abs_le.mp (by exact_mod_cast h)
  · exact (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))).mpr
      ((ha i).symm.trans (mul_comm _ _))

lemma equivFun_mem_coordBox (hb : ∀ i, b i ∈ minimalVectors L) (hy : y ∈ L)
    (hK : ∀ i, |b.repr y i| ≤ coordBound ι) : b.equivFun y ∈ coordBox ι := by
  rcases exists_nat_mul_repr_eq_intCast b hb hy with ⟨q, hq, hqn, ha⟩
  refine fun i ↦ ⟨hK i, ?_⟩
  rcases Nat.dvd_factorial hq hqn with ⟨k, hk⟩
  rcases ha i with ⟨a, ha⟩
  refine ⟨k * a, ?_⟩
  rw [b.equivFun_apply, hk]
  push_cast
  rw [← ha]
  ring1

lemma mem_image_equivFun_iff (hb : ∀ i, b i ∈ minimalVectors L) (t : ι → ℝ) :
    t ∈ b.equivFun '' (L : Set E) ↔
      (fun i ↦ Int.fract (t i)) ∈ b.equivFun '' (L : Set E) ∩ coordBox ι := by
  have hfloor (z : E) : (ZSpan.floor b z : E) ∈ L :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (hb i).1) (ZSpan.floor b z).2
  have hfract (z : E) : b.equivFun (ZSpan.fract b z) = fun i ↦ Int.fract (b.equivFun z i) :=
    funext fun i ↦ ZSpan.repr_fract_apply b z i
  refine ⟨?_, ?_⟩
  · rintro ⟨z, hz, rfl⟩
    have hzL : ZSpan.fract b z ∈ L := L.sub_mem hz (hfloor z)
    refine ⟨⟨ZSpan.fract b z, hzL, hfract z⟩, ?_⟩
    rw [← hfract]
    refine equivFun_mem_coordBox b hb hzL fun i ↦ ?_
    rw [ZSpan.repr_fract_apply, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le.trans (Nat.one_le_cast.mpr (Nat.one_le_pow _ _ (Nat.succ_pos _)))
  · rintro ⟨⟨z, hz, hzt⟩, -⟩
    refine ⟨b.equivFun.symm t, ?_, b.equivFun.apply_symm_apply t⟩
    have h1 : ZSpan.fract b (b.equivFun.symm t) = z :=
      b.equivFun.injective (by rw [hfract, hzt, b.equivFun.apply_symm_apply])
    rw [← sub_add_cancel (b.equivFun.symm t) (ZSpan.floor b (b.equivFun.symm t)),
      ← ZSpan.fract_apply, h1]
    exact L.add_mem hz (hfloor _)

end Frame

variable {ι : Type*} [Fintype ι] {L L' : Submodule ℤ (EuclideanSpace ℝ ι)}

/-- **A perfect lattice has a basis of `ℝⁿ` consisting of minimal vectors**, its minimal vectors
spanning `ℝⁿ`. -/
lemma IsPerfect.exists_basis_mem_minimalVectors (h : IsPerfect L) :
    ∃ b : Basis ι ℝ (EuclideanSpace ℝ ι), ∀ i, b i ∈ minimalVectors L := by
  classical
  rcases exists_linearIndependent ℝ (minimalVectors L) with ⟨T, hT, hspan, hli⟩
  let b₀ : Basis T ℝ (EuclideanSpace ℝ ι) :=
    Basis.mk hli (by rw [Subtype.range_coe, hspan, h.span_minimalVectors])
  refine ⟨b₀.reindex (b₀.indexEquiv (PiLp.basisFun 2 ℝ ι)), fun i ↦ ?_⟩
  rw [Basis.reindex_apply, Basis.coe_mk]
  exact hT (Subtype.coe_prop _)

lemma IsPerfect.isSimilarLattice_of_coord_eq (h : IsPerfect L)
    {b b' : Basis ι ℝ (EuclideanSpace ℝ ι)} (hb : ∀ i, b i ∈ minimalVectors L)
    (hb' : ∀ i, b' i ∈ minimalVectors L')
    (hA : b.equivFun '' (L : Set (EuclideanSpace ℝ ι)) ∩ coordBox ι =
      b'.equivFun '' (L' : Set (EuclideanSpace ℝ ι)) ∩ coordBox ι)
    (hB : b.equivFun '' minimalVectors L = b'.equivFun '' minimalVectors L') :
    BilinForm.IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L (innerₗ (EuclideanSpace ℝ ι))
      L' := by
  have hψ (z : EuclideanSpace ℝ ι) :
      b'.equivFun (b.equivFun.trans b'.equivFun.symm z) = b.equivFun z :=
    b'.equivFun.apply_symm_apply _
  have hΛ : b.equivFun '' (L : Set (EuclideanSpace ℝ ι)) =
      b'.equivFun '' (L' : Set (EuclideanSpace ℝ ι)) :=
    Set.ext fun t ↦ by rw [mem_image_equivFun_iff b hb, mem_image_equivFun_iff b' hb', hA]
  refine h.isSimilarLattice_of_mapsTo (b.equivFun.trans b'.equivFun.symm)
    (Submodule.ext fun z' ↦ ⟨?_, fun hz' ↦ ?_⟩) fun z hz ↦ ?_
  · rintro ⟨z, hz, rfl⟩
    rcases hΛ ▸ Set.mem_image_of_mem b.equivFun hz with ⟨x, hx, hxz⟩
    exact b'.equivFun.injective (hxz.trans (hψ z).symm) ▸ hx
  · rcases hΛ.symm ▸ Set.mem_image_of_mem b'.equivFun hz' with ⟨z, hz, hzz'⟩
    exact ⟨z, hz, b'.equivFun.injective ((hψ z).trans hzz')⟩
  · rcases hB ▸ Set.mem_image_of_mem b.equivFun hz with ⟨x, hx, hxz⟩
    exact b'.equivFun.injective (hxz.trans (hψ z).symm) ▸ hx

variable (ι) in
/-- **Similarity of perfect lattices**: the equivalence relation of similarity (LMFDB
`lattice.similarity`, `LinearMap.BilinForm.IsSimilarLattice`) on the perfect lattices of `ℝⁿ`
(LMFDB `lattice.perfect`). Its classes are the similarity classes of perfect lattices of
dimension `n`. -/
def perfectSimilaritySetoid : Setoid {L : Submodule ℤ (EuclideanSpace ℝ ι) // IsPerfect L} where
  r L M := BilinForm.IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L.1
    (innerₗ (EuclideanSpace ℝ ι)) M.1
  iseqv := ⟨fun L ↦ BilinForm.isSimilarLattice_refl _ L.1, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

/-- **Voronoi's finiteness theorem** (LMFDB `lattice.perfect`): there are only finitely many
similarity classes of perfect lattices of `ℝⁿ`, for every `n`. -/
lemma finite_quotient_perfectSimilaritySetoid : Finite (Quotient (perfectSimilaritySetoid ι)) := by
  choose b hb using fun L : {L : Submodule ℤ (EuclideanSpace ℝ ι) // IsPerfect L} ↦
    L.2.exists_basis_mem_minimalVectors
  let T : Set (Set (ι → ℝ) × Set (ι → ℝ)) := 𝒫 coordBox ι ×ˢ 𝒫 coordBox ι
  have hT : Finite T := (finite_coordBox.powerset.prod finite_coordBox.powerset).to_subtype
  refine Finite.of_injective (β := T) (fun q ↦ ⟨((b q.out).equivFun ''
      (q.out.1 : Set (EuclideanSpace ℝ ι)) ∩ coordBox ι,
      (b q.out).equivFun '' minimalVectors q.out.1), Set.inter_subset_right, ?_⟩)
    fun q q' hqq' ↦ ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact equivFun_mem_coordBox _ (hb _) hz.1 fun i ↦
      abs_repr_le_coordBound _ (hb _) hz.1 hz.2.2.le i
  · exact Quotient.out_equiv_out.mp <| q.out.2.isSimilarLattice_of_coord_eq (hb _) (hb _)
      (congrArg (fun p ↦ p.1.1) hqq') (congrArg (fun p ↦ p.1.2) hqq')

/-- **Finitely many perfect lattices represent all perfect lattices up to similarity** (LMFDB
`lattice.perfect`): there is a finite set of perfect lattices of `ℝⁿ` such that every perfect
lattice of `ℝⁿ` is similar to one of them. -/
lemma exists_finite_forall_isPerfect_exists_isSimilarLattice :
    ∃ S : Set (Submodule ℤ (EuclideanSpace ℝ ι)), S.Finite ∧ (∀ M ∈ S, IsPerfect M) ∧
      ∀ L, IsPerfect L → ∃ M ∈ S, BilinForm.IsSimilarLattice (innerₗ (EuclideanSpace ℝ ι)) L
        (innerₗ (EuclideanSpace ℝ ι)) M := by
  have hfin : Finite (Quotient (perfectSimilaritySetoid ι)) :=
    finite_quotient_perfectSimilaritySetoid
  refine ⟨Set.range fun q : Quotient (perfectSimilaritySetoid ι) ↦ q.out.1, Set.finite_range _,
    ?_, fun L hL ↦ ⟨_, ⟨⟦⟨L, hL⟩⟧, rfl⟩, ?_⟩⟩
  · rintro _ ⟨q, rfl⟩
    exact q.out.2
  · exact (Quotient.mk_out (s := perfectSimilaritySetoid ι) ⟨L, hL⟩).symm

end ZLattice
