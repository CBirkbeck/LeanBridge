import Mathlib.FieldTheory.Finite.GaloisField
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2Dickson
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2ExceptionalType
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SplitCartanNormalizerConjugacy

/-!
# The normalizers of Cartan subgroups of `GL₂(𝔽_p)` are maximal subgroups

The LMFDB's normalizer of a Cartan subgroup of `GL₂(𝔽_p)` (LMFDB `gl2.normalizer_cartan`,
`gl2.normalizer_split_cartan`) is a maximal subgroup of `GL₂(𝔽_p)`, except for the normalizer of a
split Cartan subgroup when `p = 3` or `p = 5`, and for the normalizer of the non-split Cartan
subgroup when `p = 2`, which is all of `GL₂(𝔽₂)`. Every such normalizer is conjugate to `Ns` or
`Nn`: the split ones by `Matrix.GeneralLinearGroup.IsSplitCartanNormalizer.exists_map_conj_eq`, the
non-split ones because, for odd `p`, a unit of a Cartan subgroup outside the scalars has order prime
to `p`, its étale algebra being reduced, so it is conjugate into `Cs` or `Cn`
(`Matrix.GeneralLinearGroup.exists_conj_mem_cartan`), and the Cartan subgroup, which is its
centralizer, then has a conjugate inside `Cs` or equal to `Cn`.

The groups `Ns`, for `p ≥ 7`, and `Nn`, for `p ≥ 5`, are maximal by Dickson's classification
(`Matrix.GeneralLinearGroup.exists_holds`). A subgroup `H` strictly containing `N = Ns` or `Nn` is
`GL₂(𝔽_p)` if it contains `SL₂(𝔽_p)`, the determinant being onto on `N`. It does not lie in a
conjugate of the Borel subgroup or of `Cs`, `Cn`, `Ns`, `Nn`: its order is a multiple `k |N|`,
`k ≥ 2`, too large or not dividing theirs (for `Nn` in a Borel subgroup, the matrix of `ω` would
have an eigenvalue). And its image in `PGL₂(𝔽_p)` is not `A₄`, `S₄` or `A₅`, whose elements have
order at most `5`, since `N` has an element of order `p - 1`, resp. `p + 1`, at least `6`, modulo
scalars. For `p = 2` (`Ns`) and `p = 3` (`Nn`) the index is `3`, a prime. The argument breaks down
for `Ns` at `p = 3` and `p = 5`, where the image of `Ns` in `PGL₂(𝔽_p)`, a dihedral group of order
`2 (p - 1) ≤ 8`, lies in an `S₄`.

## Main results

* `Matrix.GeneralLinearGroup.isCoatom_labelNs` (LMFDB `gl2.normalizer_split_cartan`): `Ns` is a
  maximal subgroup of `GL₂(𝔽_p)` unless `p = 3` or `p = 5`.
* `Matrix.GeneralLinearGroup.isCoatom_labelNn` (LMFDB `gl2.normalizer_cartan`): for odd `p`, `Nn`
  is a maximal subgroup of `GL₂(𝔽_p)`.
* `Matrix.GeneralLinearGroup.IsCartanSubgroup.normal_of_eq_two` (LMFDB `gl2.normalizer_cartan`,
  `gl2.normalizer_split_cartan`): the Cartan subgroups of `GL₂(𝔽₂)` are normal.
* `Matrix.GeneralLinearGroup.IsCartanSubgroup.exists_map_conj_le_diagonalTorus_or_eq_labelCn`: for
  odd `p`, a Cartan subgroup of `GL₂(𝔽_p)` has a conjugate inside `Cs` or equal to `Cn`.
* `Matrix.GeneralLinearGroup.IsNonsplitCartanSubgroup.exists_map_conj_eq_labelCn` (LMFDB
  `gl2.nonsplit_cartan`): every non-split Cartan subgroup is conjugate to `Cn`, for every prime `p`.
* `Matrix.GeneralLinearGroup.IsNonsplitCartanSubgroup.nonempty_mulEquiv_units_galoisField` and
  `Matrix.GeneralLinearGroup.IsNonsplitCartanSubgroup.isCyclic` (LMFDB `gl2.nonsplit_cartan`):
  every non-split Cartan subgroup is a cyclic group isomorphic to `𝔽_{p²}ˣ`.
* `Matrix.GeneralLinearGroup.IsNonsplitCartanNormalizer.exists_map_conj_eq` (LMFDB
  `gl2.normalizer_nonsplit_cartan`): every normalizer of a non-split Cartan subgroup is conjugate
  to `Nn`.
* `Matrix.GeneralLinearGroup.IsSplitCartanNormalizer.isCoatom` (LMFDB
  `gl2.normalizer_split_cartan`): the normalizer of a split Cartan subgroup is a maximal subgroup
  unless `p = 3` or `p = 5`.
* `Matrix.GeneralLinearGroup.IsNonsplitCartanNormalizer.isCoatom` and
  `Matrix.GeneralLinearGroup.IsNonsplitCartanNormalizer.not_isCoatom` (LMFDB
  `gl2.normalizer_cartan`): the normalizer of a non-split Cartan subgroup is a maximal subgroup for
  odd `p`, and not for `p = 2`, where it is `GL₂(𝔽₂)`.
* `Matrix.GeneralLinearGroup.IsCartanNormalizer.isCoatom_or` (LMFDB `gl2.normalizer_cartan`): for
  `p > 2`, the normalizer of a Cartan subgroup is a maximal subgroup, except for the normalizer of a
  split Cartan subgroup when `p = 3` or `p = 5`.
-/

open Matrix Module TauCeti

namespace Matrix.GeneralLinearGroup

lemma orderOf_perm_fin_four_le_four (σ : Equiv.Perm (Fin 4)) : orderOf σ ≤ 4 := by
  have h : σ ^ 4 = 1 ∨ σ ^ 3 = 1 := by
    revert σ
    decide
  rcases h with h | h
  · exact orderOf_le_of_pow_eq_one (by norm_num) h
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)

lemma orderOf_alternatingGroup_fin_five_le_five (σ : alternatingGroup (Fin 5)) :
    orderOf σ ≤ 5 := by
  have h : ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ ^ 2 = 1 ∨ τ ^ 3 = 1 ∨ τ ^ 5 = 1 := by
    decide +kernel
  rw [← Subgroup.orderOf_coe]
  rcases h σ σ.2 with h | h | h
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
  · exact (orderOf_le_of_pow_eq_one (by norm_num) h).trans (by norm_num)
  · exact orderOf_le_of_pow_eq_one (by norm_num) h

section Cartan

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A] (b : Basis (Fin 2) F A)

lemma mul_comm_of_mem_cartanSubgroup {g h : GL (Fin 2) F} (hg : g ∈ cartanSubgroup b)
    (hh : h ∈ cartanSubgroup b) : g * h = h * g := by
  rcases hg with ⟨u, rfl⟩
  rcases hh with ⟨v, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

lemma unitsLeftMulMatrix_mem_center_iff (w : Aˣ) :
    unitsLeftMulMatrix b w ∈ Subgroup.center (GL (Fin 2) F) ↔ (w : A) ∈ (⊥ : Subalgebra F A) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Subgroup.mem_center_iff.mpr fun g ↦ Units.ext ?_⟩
  · rw [GeneralLinearGroup.center_eq_range_scalar] at h
    rcases h with ⟨c, hc⟩
    refine Algebra.mem_bot.mpr ⟨c, Algebra.leftMulMatrix_injective b ?_⟩
    rw [AlgHom.commutes, ← coe_unitsLeftMulMatrix, ← hc]
    simp [Matrix.algebraMap_eq_diagonal]
  · rcases Algebra.mem_bot.mp h with ⟨c, hc⟩
    rw [Units.val_mul, Units.val_mul, coe_unitsLeftMulMatrix, ← hc, AlgHom.commutes]
    exact (Algebra.commutes c g.val).symm

lemma mem_diagonalTorus_of_mul_comm {D M : GL (Fin 2) F} (hD : D ∈ diagonalTorus F 2)
    (hne : D 0 0 ≠ D 1 1) (h : M * D = D * M) : M ∈ diagonalTorus F 2 := by
  have hd : (D : Matrix (Fin 2) (Fin 2) F).IsDiag := mem_diagonalTorus_iff.mp hD
  have h₀₁ : D 0 1 = 0 := hd (show (0 : Fin 2) ≠ 1 by decide)
  have h₁₀ : D 1 0 = 0 := hd (show (1 : Fin 2) ≠ 0 by decide)
  have e₁ : (M * D : GL (Fin 2) F) 0 1 = (D * M : GL (Fin 2) F) 0 1 := by rw [h]
  have e₂ : (M * D : GL (Fin 2) F) 1 0 = (D * M : GL (Fin 2) F) 1 0 := by rw [h]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h₀₁, h₁₀] at e₁ e₂
  refine mem_diagonalTorus_of_fin_two F ?_ ?_
  · exact (mul_eq_zero.mp (by linear_combination e₁ : M 0 1 * (D 1 1 - D 0 0) = 0)).resolve_right
      (sub_ne_zero.mpr hne.symm)
  · exact (mul_eq_zero.mp (by linear_combination e₂ : M 1 0 * (D 0 0 - D 1 1) = 0)).resolve_right
      (sub_ne_zero.mpr hne)

end Cartan

variable {p : ℕ} [Fact p.Prime] {H N C : Subgroup (GL (Fin 2) (ZMod p))}

lemma not_dvd_orderOf_of_mem_cartanSubgroup {A : Type} [CommRing A] [Algebra (ZMod p) A]
    [Algebra.Etale (ZMod p) A] (b : Basis (Fin 2) (ZMod p) A) {x : GL (Fin 2) (ZMod p)}
    (hx : x ∈ cartanSubgroup b) : ¬p ∣ orderOf x := by
  intro hdvd
  have : Nontrivial A := nontrivial_of_ne _ _ (b.ne_zero 0)
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field (ZMod p) A
  have : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p
  have hy : orderOf (x ^ (orderOf x / p)) = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd
  rcases pow_mem hx (orderOf x / p) with ⟨a, ha⟩
  have h₁ : (x ^ (orderOf x / p)) ^ p = 1 := by
    have h : (x ^ (orderOf x / p)) ^ orderOf (x ^ (orderOf x / p)) = 1 := pow_orderOf_eq_one _
    rwa [hy] at h
  have hap : a ^ p = 1 := unitsLeftMulMatrix_injective b (by rw [map_pow, ha, h₁, map_one])
  have ha₁ : (a : A) - 1 = 0 := IsReduced.eq_zero _ ⟨p, by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hap, Units.val_one, one_pow, sub_self]⟩
  have ha₂ : a = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.mp ha₁)
  rw [← ha, ha₂, map_one, orderOf_one] at hy
  exact (Fact.out : p.Prime).one_lt.ne hy

lemma IsCartanSubgroup.natCard_eq_one_or_eq_three (hC : IsCartanSubgroup C) (hp : p = 2) :
    Nat.card C = 1 ∨ Nat.card C = 3 := by
  subst hp
  have h₂ : ¬2 ∣ Nat.card C := fun h ↦ by
    rcases exists_prime_orderOf_dvd_card' 2 h with ⟨x, hx⟩
    rcases hC with ⟨A, _, _, _, b, rfl⟩
    exact not_dvd_orderOf_of_mem_cartanSubgroup b x.2 (by rw [Subgroup.orderOf_coe, hx])
  have hdvd : Nat.card C ∣ 6 :=
    natCard_GL_fin_two_of_card_eq_two (ZMod.card 2) ▸ Subgroup.card_subgroup_dvd_card C
  have hle : Nat.card C ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card C <;> simp_all

lemma index_eq_two_of_natCard_eq_three {K : Subgroup (GL (Fin 2) (ZMod 2))} (h : Nat.card K = 3) :
    K.index = 2 := by
  have h' : Nat.card K * K.index = Nat.card (GL (Fin 2) (ZMod 2)) := K.card_mul_index
  rw [h, natCard_GL_fin_two_of_card_eq_two (ZMod.card 2)] at h'
  omega

/-- **For `p = 2`, every Cartan subgroup of `GL₂(𝔽₂)` is normal** (LMFDB `gl2.normalizer_cartan`,
`gl2.normalizer_split_cartan`): it has no element of order `2`, so its order is an odd divisor of
`6`, and it is trivial or of index `2`. -/
lemma IsCartanSubgroup.normal_of_eq_two (hC : IsCartanSubgroup C) (hp : p = 2) : C.Normal := by
  subst hp
  rcases hC.natCard_eq_one_or_eq_three rfl with h₁ | h₃
  · rw [Subgroup.card_eq_one.mp h₁]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two (index_eq_two_of_natCard_eq_three h₃)

/-- **For odd `p`, a Cartan subgroup of `GL₂(𝔽_p)` has a conjugate inside `Cs` or equal to
`Cn`**: a unit `u` of its algebra outside `𝔽_p` has order prime to `p`, so the matrix of `u` is
conjugate into `Cs` or `Cn` (`exists_conj_mem_cartan`), and the Cartan subgroup is the centralizer
of that matrix. -/
lemma IsCartanSubgroup.exists_map_conj_le_diagonalTorus_or_eq_labelCn (hC : IsCartanSubgroup C)
    (hp : p ≠ 2) : (∃ g, C.map (MulAut.conj g).toMonoidHom ≤ diagonalTorus (ZMod p) 2) ∨
      ∃ g, C.map (MulAut.conj g).toMonoidHom = labelCn p := by
  rcases hC with ⟨A, _, _, _, b, rfl⟩
  rcases exists_unit_notMem_bot b (two_ne_zero_of_ne_two p hp) with ⟨w, hw⟩
  have hU : unitsLeftMulMatrix b w ∉ Subgroup.center (GL (Fin 2) (ZMod p)) :=
    fun h ↦ hw ((unitsLeftMulMatrix_mem_center_iff b w).mp h)
  rcases exists_conj_mem_cartan hp (n := orderOf (unitsLeftMulMatrix b w))
    (fun h ↦ not_dvd_orderOf_of_mem_cartanSubgroup b ⟨w, rfl⟩ ((ZMod.natCast_eq_zero_iff _ p).mp h))
    (by rw [pow_orderOf_eq_one]; exact one_mem _) with ⟨P, hP | hP⟩
  · refine .inl ⟨P⁻¹, ?_⟩
    rintro - ⟨y, hy, rfl⟩
    refine mem_diagonalTorus_of_mul_comm hP (fun h ↦ hU (mem_center_of_mulAut_conj_mem
      (mem_center_iff_entries.mpr ⟨?_, ?_, h⟩))) ?_
    · exact mem_diagonalTorus_iff.mp hP (show (0 : Fin 2) ≠ 1 by decide)
    · exact mem_diagonalTorus_iff.mp hP (show (1 : Fin 2) ≠ 0 by decide)
    · simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
      rw [mul_comm_of_mem_cartanSubgroup b hy ⟨w, rfl⟩]
  · refine .inr ⟨P⁻¹, ?_⟩
    rw [cartanSubgroup_map_conj]
    rcases hP with ⟨v, hv⟩
    rw [← unitsLeftMulMatrix_conjBasis] at hv
    have hv' : (v : NonsplitCartanAlgebra p) ∉ (⊥ : Subalgebra (ZMod p) _) := fun h ↦ hU <|
      mem_center_of_mulAut_conj_mem (P := P⁻¹) <| by
        rw [← unitsLeftMulMatrix_conjBasis, ← hv]
        exact (unitsLeftMulMatrix_mem_center_iff _ v).mpr h
    refine le_antisymm (fun c hc ↦ ?_) (fun c hc ↦ ?_)
    · refine mem_cartanSubgroup_of_commute (nonsplitCartanBasis p) hv' ?_
      rw [← coe_unitsLeftMulMatrix, ← Units.val_mul, ← Units.val_mul, hv]
      exact congr_arg Units.val (mul_comm_of_mem_cartanSubgroup _ hc ⟨w, rfl⟩)
    · refine mem_cartanSubgroup_of_commute (conjBasis b P⁻¹) hw ?_
      rw [← coe_unitsLeftMulMatrix, ← Units.val_mul, ← Units.val_mul, ← hv]
      exact congr_arg Units.val (mul_comm_of_mem_cartanSubgroup _ hc ⟨v, rfl⟩)

/-- **Every non-split Cartan subgroup of `GL₂(𝔽_p)` is conjugate to `Cn`** (LMFDB
`gl2.nonsplit_cartan`), for every prime `p`: for odd `p` by the classification of the Cartan
subgroups, and for `p = 2`, where it is nontrivial, so of order `3`, it is the unique subgroup `Cn`
of index `2`. -/
lemma IsNonsplitCartanSubgroup.exists_map_conj_eq_labelCn (hC : IsNonsplitCartanSubgroup C) :
    ∃ g, C.map (MulAut.conj g).toMonoidHom = labelCn p := by
  by_cases hp : p = 2
  · subst hp
    have hne : Nat.card C ≠ 1 := fun h ↦ hC.2 1 <| by
      rw [Subgroup.card_eq_one.mp h, Subgroup.map_bot]
      exact bot_le
    have h₃ : Nat.card C = 3 := (hC.1.natCard_eq_one_or_eq_three rfl).resolve_left hne
    refine ⟨1, ?_⟩
    rw [← labelCn_two_eq_of_index_eq_two (index_eq_two_of_natCard_eq_three h₃)]
    ext x
    simp
  · exact (hC.1.exists_map_conj_le_diagonalTorus_or_eq_labelCn hp).resolve_left
      fun ⟨g, hg⟩ ↦ hC.2 g hg

/-- **Every non-split Cartan subgroup of `GL₂(𝔽_p)` is isomorphic to `𝔽_{p²}ˣ`** (LMFDB
`gl2.nonsplit_cartan`), for every prime `p`: it is conjugate to `Cn`, the image of the units of the
field `NonsplitCartanAlgebra p` with `p²` elements. -/
lemma IsNonsplitCartanSubgroup.nonempty_mulEquiv_units_galoisField
    (hC : IsNonsplitCartanSubgroup C) : Nonempty (C ≃* (GaloisField p 2)ˣ) := by
  rcases hC.exists_map_conj_eq_labelCn with ⟨g, hg⟩
  have : Finite (NonsplitCartanAlgebra p) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm
  exact ⟨(C.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans <|
    (MulEquiv.subgroupCongr hg).trans <|
      (MonoidHom.ofInjective (unitsLeftMulMatrix_injective (nonsplitCartanBasis p))).symm.trans <|
        Units.mapEquiv (GaloisField.algEquivGaloisField p 2
          (natCard_nonsplitCartanAlgebra p)).toMulEquiv⟩

/-- **Every non-split Cartan subgroup of `GL₂(𝔽_p)` is cyclic** (LMFDB `gl2.nonsplit_cartan`), as
the unit group of the finite field `𝔽_{p²}` is. -/
lemma IsNonsplitCartanSubgroup.isCyclic (hC : IsNonsplitCartanSubgroup C) : IsCyclic C := by
  rcases hC.nonempty_mulEquiv_units_galoisField with ⟨e⟩
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Every normalizer of a non-split Cartan subgroup of `GL₂(𝔽_p)` is conjugate to `Nn`** (LMFDB
`gl2.normalizer_nonsplit_cartan`), for every prime `p`: for odd `p` the non-split Cartan subgroup is
conjugate to `Cn`, and for `p = 2` both groups are `GL₂(𝔽₂)`. -/
lemma IsNonsplitCartanNormalizer.exists_map_conj_eq (hH : IsNonsplitCartanNormalizer H) :
    ∃ g, H.map (MulAut.conj g).toMonoidHom = labelNn p := by
  by_cases hp : p = 2
  · subst hp
    refine ⟨1, ?_⟩
    rw [hH.eq_top rfl, labelNn_two]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj 1).surjective
  · rcases hH with ⟨C, hC, h⟩
    rw [ite_eq_right hp] at h
    rcases hC.exists_map_conj_eq_labelCn with ⟨g, hg⟩
    exact ⟨g, by rw [h, Subgroup.map_equiv_normalizer_eq, hg, labelNn_eq_normalizer p hp]⟩

lemma not_hasExceptionalType_of_mem {x : GL (Fin 2) (ZMod p)} (hx : x ∈ H)
    (hxk : ∀ k, 0 < k → k ≤ 5 → x ^ k ∉ Subgroup.center (GL (Fin 2) (ZMod p)))
    (t : ExceptionalType) : ¬HasExceptionalType H t := by
  intro ht
  let y : projectiveImage H := ⟨ProjGenLinGroup.mk x, Subgroup.mem_map_of_mem _ hx⟩
  have hy : 0 < orderOf y ∧ orderOf y ≤ 5 := by
    cases t <;> rcases ht with ⟨e⟩ <;> rw [← e.orderOf_eq y] <;> refine ⟨orderOf_pos _, ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact (orderOf_perm_fin_four_le_four _).trans (by norm_num)
    · exact (orderOf_perm_fin_four_le_four _).trans (by norm_num)
    · exact orderOf_alternatingGroup_fin_five_le_five _
  refine hxk (orderOf y) hy.1 hy.2 (ProjGenLinGroup.mk_eq_one.mp ?_)
  rw [map_pow]
  exact congrArg Subtype.val (pow_orderOf_eq_one y)

lemma eq_top_of_det_ker_le (hker : (det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker ≤ H)
    (hdet : ∀ c : (ZMod p)ˣ, ∃ g ∈ H, det g = c) : H = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  rcases hdet (det g) with ⟨h, hh, hgh⟩
  have hg : g * h⁻¹ ∈ H :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel])
  simpa using mul_mem hg hh

lemma eq_top_of_forall_not_le (hdet : ∀ c : (ZMod p)ˣ, ∃ g ∈ H, det g = c)
    (hX : ∀ X ∈ ({GL2Borel (ZMod p), diagonalTorus (ZMod p) 2, labelCn p, labelNs p, labelNn p} :
      Set (Subgroup (GL (Fin 2) (ZMod p)))), ∀ P, ¬H ≤ X.map (MulAut.conj P).toMonoidHom)
    {x : GL (Fin 2) (ZMod p)} (hx : x ∈ H)
    (hxk : ∀ k, 0 < k → k ≤ 5 → x ^ k ∉ Subgroup.center (GL (Fin 2) (ZMod p))) : H = ⊤ := by
  rcases exists_holds H with ⟨S, hS⟩
  cases S
  · rcases hS with ⟨K, hK, hk⟩
    exact eq_top_of_det_ker_le (det_ker_le_of_mem_subgroupConjClass hK hk) hdet
  · rcases hS with ⟨K, hK, hKX, -⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
    exact absurd hP (hX _ (by simp) P)
  · rcases hS with ⟨K, hK, hKX⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
    exact absurd hP (hX _ (by simp) P)
  · rcases hS with ⟨⟨K, hK, hKX⟩, -⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
    exact absurd hP (hX _ (by simp) P)
  · rcases hS with ⟨K, hK, hKX, -⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
    exact absurd hP (hX _ (by simp) P)
  · rcases hS with ⟨⟨K, hK, hKX, -⟩, -⟩
    rcases exists_le_map_conj_of_mem_subgroupConjClass hK hKX with ⟨P, hP⟩
    exact absurd hP (hX _ (by simp) P)
  all_goals
    rcases hS with ⟨K, hK, ht, -⟩
    exact absurd (ht.of_mem_subgroupConjClass hK) (not_hasExceptionalType_of_mem hx hxk _)

lemma relIndex_mul_natCard_eq (hNH : N ≤ H) : N.relIndex H * Nat.card N = Nat.card H := by
  simpa [inf_eq_left.mpr hNH] using N.relIndex_mul_card H

lemma two_le_relIndex (hNH : N < H) : 2 ≤ N.relIndex H := by
  have h₀ : N.relIndex H ≠ 0 := fun h₀ ↦ by
    have h : N.relIndex H * Nat.card N = Nat.card H := relIndex_mul_natCard_eq hNH.le
    rw [h₀, zero_mul] at h
    exact Nat.card_pos.ne h
  have h₁ : N.relIndex H ≠ 1 := fun h₁ ↦ hNH.not_ge (Subgroup.relIndex_eq_one.mp h₁)
  omega

lemma relIndex_mul_natCard_dvd (hNH : N ≤ H) {X : Subgroup (GL (Fin 2) (ZMod p))}
    {P : GL (Fin 2) (ZMod p)} (hHX : H ≤ X.map (MulAut.conj P).toMonoidHom) :
    N.relIndex H * Nat.card N ∣ Nat.card X := by
  have hX : Nat.card (X.map (MulAut.conj P).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj P).injective
  rw [relIndex_mul_natCard_eq hNH, ← hX]
  exact Subgroup.card_dvd_of_le hHX

variable (p)

lemma natCard_labelNs : Nat.card (labelNs p) = 2 * (p - 1) ^ 2 := by
  have h : (diagonalTorus (ZMod p) 2).relIndex (labelNs p) *
      Nat.card (diagonalTorus (ZMod p) 2 ⊓ labelNs p : Subgroup (GL (Fin 2) (ZMod p))) =
      Nat.card (labelNs p) := (diagonalTorus (ZMod p) 2).relIndex_mul_card (labelNs p)
  rw [relIndex_diagonalTorus_labelNs, inf_eq_left.mpr (diagonalTorus_le_labelNs p),
    natCard_diagonalTorus, Nat.card_zmod] at h
  exact h.symm

lemma natCard_labelNn : Nat.card (labelNn p) = 2 * (p ^ 2 - 1) := by
  have h : (labelCn p).relIndex (labelNn p) *
      Nat.card (labelCn p ⊓ labelNn p : Subgroup (GL (Fin 2) (ZMod p))) = Nat.card (labelNn p) :=
    (labelCn p).relIndex_mul_card (labelNn p)
  rw [relIndex_labelCn_labelNn, inf_eq_left.mpr (labelCn_le_labelNn p), natCard_labelCn] at h
  exact h.symm

lemma natCard_GL_fin_two_zmod : Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p * (p - 1)) := by
  rw [natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card]

lemma exists_mem_labelNs_pow_notMem_center (hp : 7 ≤ p) :
    ∃ x ∈ labelNs p, ∀ k, 0 < k → k ≤ 5 → x ^ k ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  rcases IsCyclic.exists_generator (α := (ZMod p)ˣ) with ⟨g, hg⟩
  have hg' : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  refine ⟨diagGL ![g, 1], diagonalTorus_le_labelNs p ⟨_, rfl⟩, fun k hk hk₅ hc ↦ ?_⟩
  have h : (diagGL ![g, 1] ^ k) 0 0 = (diagGL ![g, 1] ^ k) 1 1 := (mem_center_iff_entries.mp hc).2.2
  rw [← map_pow, diagGL_coe] at h
  have h' : g ^ k = 1 := Units.ext (by simpa using h)
  have hle : p - 1 ≤ k := Nat.le_of_dvd hk (hg' ▸ orderOf_dvd_of_pow_eq_one h')
  omega

lemma exists_mem_labelNn_pow_notMem_center (hp : 5 ≤ p) :
    ∃ x ∈ labelNn p, ∀ k, 0 < k → k ≤ 5 → x ^ k ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  have : Finite (NonsplitCartanAlgebra p) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd _ _).symm
  rcases IsCyclic.exists_generator (α := (NonsplitCartanAlgebra p)ˣ) with ⟨u, hu⟩
  have hu' : orderOf u = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, natCard_nonsplitCartanAlgebra]
  refine ⟨unitsLeftMulMatrix (nonsplitCartanBasis p) u, labelCn_le_labelNn p ⟨u, rfl⟩,
    fun k hk hk₅ hc ↦ ?_⟩
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  rcases hc with ⟨c, hc⟩
  have h₁ : unitsLeftMulMatrix (nonsplitCartanBasis p) u ^ (k * (p - 1)) = 1 := by
    rw [pow_mul, ← hc, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  have h₂ : p ^ 2 - 1 ∣ k * (p - 1) := by
    rw [← hu', ← orderOf_injective _ (unitsLeftMulMatrix_injective (nonsplitCartanBasis p)) u]
    exact orderOf_dvd_of_pow_eq_one h₁
  rcases Nat.exists_eq_add_one_of_ne_zero (by omega : p ≠ 0) with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  have hsq : (q + 1) ^ 2 - 1 = q * (q + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [hsq, Nat.add_sub_cancel] at h₂
  nlinarith [Nat.le_of_dvd (by positivity) h₂]

lemma eq_two_or_seven_le (h₃ : p ≠ 3) (h₅ : p ≠ 5) : p = 2 ∨ 7 ≤ p := by
  have hp : p.Prime := Fact.out
  have h₂ : 2 ≤ p := hp.two_le
  rcases Nat.lt_or_ge p 7 with h₇ | h₇
  · interval_cases p
    · exact .inl rfl
    · exact absurd rfl h₃
    · exact absurd hp (by decide)
    · exact absurd rfl h₅
    · exact absurd hp (by decide)
  · exact .inr h₇

/-- **`Ns` is a maximal subgroup of `GL₂(𝔽_p)` unless `p = 3` or `p = 5`** (LMFDB
`gl2.normalizer_split_cartan`): for `p = 2` it has index `3`, and for `p ≥ 7` a subgroup strictly
containing it is `GL₂(𝔽_p)` by Dickson's classification. -/
lemma isCoatom_labelNs (h₃ : p ≠ 3) (h₅ : p ≠ 5) : IsCoatom (labelNs p) := by
  rcases eq_two_or_seven_le p h₃ h₅ with rfl | hp
  · refine Subgroup.isCoatom_of_index_prime ?_
    have h : Nat.card (labelNs 2) * (labelNs 2).index = Nat.card (GL (Fin 2) (ZMod 2)) :=
      (labelNs 2).card_mul_index
    rw [natCard_labelNs, natCard_GL_fin_two_zmod] at h
    rw [show (labelNs 2).index = 3 by norm_num at h; omega]
    exact Nat.prime_three
  rcases Nat.exists_eq_add_one_of_ne_zero (by omega : p ≠ 0) with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  have hsq : (q + 1) ^ 2 - 1 = q * (q + 2) := Nat.sub_eq_of_eq_add (by ring)
  refine ⟨fun h ↦ ?_, fun H hNH ↦ ?_⟩
  · have h' : Nat.card (labelNs (q + 1)) = Nat.card (⊤ : Subgroup (GL (Fin 2) (ZMod (q + 1)))) :=
      by rw [h]
    simp only [natCard_labelNs, Subgroup.card_top, natCard_GL_fin_two_zmod, Nat.add_sub_cancel]
      at h'
    nlinarith
  rcases exists_mem_labelNs_pow_notMem_center (q + 1) hp with ⟨x, hx, hxk⟩
  refine eq_top_of_forall_not_le (fun c ↦ ⟨diagGL ![c, 1],
    hNH.le (diagonalTorus_le_labelNs _ ⟨_, rfl⟩), by simp⟩) (fun X hX P hHX ↦ ?_) (hNH.le hx) hxk
  have hk : 2 ≤ (labelNs (q + 1)).relIndex H := two_le_relIndex hNH
  have hdvd : (labelNs (q + 1)).relIndex H * Nat.card (labelNs (q + 1)) ∣ Nat.card X :=
    relIndex_mul_natCard_dvd hNH.le hHX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rw [natCard_labelNs, Nat.add_sub_cancel] at hdvd
  rcases hX with rfl | rfl | rfl | rfl | rfl
  · rw [GL2Borel.card_eq, ZMod.card, Nat.add_sub_cancel, ← mul_assoc] at hdvd
    have h₂ : 2 ∣ q + 1 :=
      (dvd_mul_left 2 _).trans (Nat.dvd_of_mul_dvd_mul_right (pow_pos hq 2) hdvd)
    have h₂' : 2 = q + 1 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : (q + 1).Prime)).mp h₂
    omega
  · rw [natCard_diagonalTorus, Nat.card_zmod, Nat.add_sub_cancel] at hdvd
    nlinarith [Nat.le_of_dvd (pow_pos hq 2) hdvd]
  · rw [natCard_labelCn, hsq] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]
  · rw [natCard_labelNs, Nat.add_sub_cancel] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]
  · rw [natCard_labelNn, hsq] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]

/-- **For odd `p`, `Nn` is a maximal subgroup of `GL₂(𝔽_p)`** (LMFDB `gl2.normalizer_cartan`): for
`p = 3` it has index `3`, and for `p ≥ 5` a subgroup strictly containing it is `GL₂(𝔽_p)` by
Dickson's classification. -/
lemma isCoatom_labelNn (hp : p ≠ 2) : IsCoatom (labelNn p) := by
  have hp₂ : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_cases hp₃ : p = 3
  · subst hp₃
    refine Subgroup.isCoatom_of_index_prime ?_
    have h : Nat.card (labelNn 3) * (labelNn 3).index = Nat.card (GL (Fin 2) (ZMod 3)) :=
      (labelNn 3).card_mul_index
    rw [natCard_labelNn, natCard_GL_fin_two_zmod] at h
    rw [show (labelNn 3).index = 3 by norm_num at h; omega]
    exact Nat.prime_three
  have hp₅ : 5 ≤ p := by
    have h₄ : p ≠ 4 := fun h ↦ absurd (h ▸ (Fact.out : p.Prime)) (by decide)
    omega
  rcases Nat.exists_eq_add_one_of_ne_zero (by omega : p ≠ 0) with ⟨q, rfl⟩
  have hq : 0 < q := by omega
  have hsq : (q + 1) ^ 2 - 1 = q * (q + 2) := Nat.sub_eq_of_eq_add (by ring)
  refine ⟨fun h ↦ ?_, fun H hNH ↦ ?_⟩
  · have h' : Nat.card (labelNn (q + 1)) = Nat.card (⊤ : Subgroup (GL (Fin 2) (ZMod (q + 1)))) :=
      by rw [h]
    simp only [natCard_labelNn, Subgroup.card_top, natCard_GL_fin_two_zmod, Nat.add_sub_cancel]
      at h'
    have h₃ : 3 ≤ (q + 1) * q := by nlinarith
    have hpos : 0 < q * (q + 2) := by positivity
    nlinarith [Nat.mul_le_mul_left (q * (q + 2)) h₃]
  rcases exists_mem_labelNn_pow_notMem_center (q + 1) hp₅ with ⟨x, hx, hxk⟩
  refine eq_top_of_forall_not_le (fun c ↦ ?_) (fun X hX P hHX ↦ ?_) (hNH.le hx) hxk
  · rcases exists_mem_labelCn_det_eq c with ⟨g, hg, hgc⟩
    exact ⟨g, hNH.le (labelCn_le_labelNn _ hg), hgc⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | hX
  · have hω : omegaGL (q + 1) ∈ (GL2Borel (ZMod (q + 1))).map (MulAut.conj P).toMonoidHom :=
      hHX (hNH.le (labelCn_le_labelNn _ (omegaGL_mem_labelCn _)))
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, ← inv_inv P, inv_inv P⁻¹] at hω
    rcases GL2Borel.exists_det_sub_algebraMap_eq_zero hω with ⟨t, ht⟩
    rw [coe_omegaGL, Matrix.det_fin_two] at ht
    refine sq_ne_nonsplitCartanA_add (q + 1) t ?_
    simp [Matrix.algebraMap_matrix_apply] at ht
    linear_combination ht
  have hk : 2 ≤ (labelNn (q + 1)).relIndex H := two_le_relIndex hNH
  have hdvd : (labelNn (q + 1)).relIndex H * Nat.card (labelNn (q + 1)) ∣ Nat.card X :=
    relIndex_mul_natCard_dvd hNH.le hHX
  rw [natCard_labelNn, hsq] at hdvd
  rcases hX with rfl | rfl | rfl | rfl
  · rw [natCard_diagonalTorus, Nat.card_zmod, Nat.add_sub_cancel] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]
  · rw [natCard_labelCn, hsq] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]
  · rw [natCard_labelNs, Nat.add_sub_cancel] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]
  · rw [natCard_labelNn, hsq] at hdvd
    nlinarith [Nat.le_of_dvd (by positivity) hdvd]

variable {p}

/-- **The normalizer of a split Cartan subgroup of `GL₂(𝔽_p)` is a maximal subgroup unless `p = 3`
or `p = 5`** (LMFDB `gl2.normalizer_split_cartan`): it is conjugate to `Ns`. -/
lemma IsSplitCartanNormalizer.isCoatom (hH : IsSplitCartanNormalizer H) (h₃ : p ≠ 3) (h₅ : p ≠ 5) :
    IsCoatom H := by
  rcases hH.exists_map_conj_eq with ⟨g, hg⟩
  have h : IsCoatom (H.map (MulAut.conj g).toMonoidHom) := hg ▸ isCoatom_labelNs p h₃ h₅
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff H).mp h

/-- **For odd `p`, the normalizer of a non-split Cartan subgroup of `GL₂(𝔽_p)` is a maximal
subgroup** (LMFDB `gl2.normalizer_cartan`): it is conjugate to `Nn`. -/
lemma IsNonsplitCartanNormalizer.isCoatom (hH : IsNonsplitCartanNormalizer H) (hp : p ≠ 2) :
    IsCoatom H := by
  rcases hH.exists_map_conj_eq with ⟨g, hg⟩
  have h : IsCoatom (H.map (MulAut.conj g).toMonoidHom) := hg ▸ isCoatom_labelNn p hp
  exact ((MulAut.conj g).mapSubgroup.isCoatom_iff H).mp h

/-- **For `p = 2`, the normalizer of a non-split Cartan subgroup is not a maximal subgroup**
(LMFDB `gl2.normalizer_cartan`): it is all of `GL₂(𝔽₂)`. -/
lemma IsNonsplitCartanNormalizer.not_isCoatom (hH : IsNonsplitCartanNormalizer H) (hp : p = 2) :
    ¬IsCoatom H :=
  fun h ↦ h.1 (hH.eq_top hp)

/-- **For `p > 2`, the normalizer of a Cartan subgroup of `GL₂(𝔽_p)` is a maximal subgroup, except
for the normalizer of a split Cartan subgroup when `p = 3` or `p = 5`** (LMFDB
`gl2.normalizer_cartan`). -/
lemma IsCartanNormalizer.isCoatom_or (hH : IsCartanNormalizer H) (hp : p ≠ 2) :
    IsCoatom H ∨ IsSplitCartanNormalizer H ∧ (p = 3 ∨ p = 5) := by
  rcases hH with ⟨C, hC, h⟩
  by_cases hs : ∃ g, C.map (MulAut.conj g).toMonoidHom ≤ diagonalTorus (ZMod p) 2
  · have hH : IsSplitCartanNormalizer H := ⟨C, ⟨hC, hs⟩, h⟩
    by_cases h₃₅ : p = 3 ∨ p = 5
    · exact .inr ⟨hH, h₃₅⟩
    · exact .inl (hH.isCoatom (fun h₃ ↦ h₃₅ (.inl h₃)) fun h₅ ↦ h₃₅ (.inr h₅))
  · exact .inl (IsNonsplitCartanNormalizer.isCoatom ⟨C, ⟨hC, fun g hg ↦ hs ⟨g, hg⟩⟩, h⟩ hp)

end Matrix.GeneralLinearGroup
