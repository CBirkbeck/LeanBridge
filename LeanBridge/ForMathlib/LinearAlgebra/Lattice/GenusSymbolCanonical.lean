import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusLabel
import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolDyadic
import Mathlib.Data.List.SplitBy

/-!
# The canonical `2`-adic symbol of an integral lattice

At the prime `2`, the Conway genus symbol (LMFDB `lattice.conway_genus_symbol`; Conway and Sloane,
*Sphere Packings, Lattices and Groups*, Chapter 15, §7.3–7.6) of a nondegenerate integral lattice
records, for a Jordan decomposition `L ⊗ ℤ_2 = ⊕_q q f_q` over the powers `q = 2 ^ k`, the rank
`n_q`, the type `I` or `II`, the sign `ε_q = χ₈(det f_q)` and the oddity `t_q` of every constituent.
The ranks and types do not depend on the decomposition, the signs and oddities do. Conway and Sloane
group the nonzero constituents into *compartments*, the maximal runs of constituents of type `I` at
consecutive scales, and *trains*, the maximal runs in which, of any two constituents at consecutive
scales (zero constituents, of type `II`, included), one at least has type `I`. They bring the symbol
to a canonical form by *oddity fusion*, which keeps only the total oddity of each compartment, and
*sign walking*, which walks the signs to the first constituent of their train, each step between
consecutive scales changing the oddity of a compartment by `4`. The canonical symbol records the
oddity of every compartment and the sign of every train; these are what the label of a genus
(LMFDB `lattice.genus_label`) encodes.

This file defines the compartments and trains of a list of constituents, the sign of a train and
the oddity of a compartment in the canonical symbol, in closed form: the sign of a train is the
product of its signs, and the oddity of a compartment is its total oddity plus `4` for every sign
walk that touches it. This is the reduction of Conway and Sloane as implemented in Sage's
`canonical_2_adic_reduction`, which the LMFDB uses; a walk between constituents of scales `v` and
`v + 2` passes the zero constituent in between and touches two compartments. For a lattice these
data are computed from the dyadic Jordan splitting chosen by Tau Ceti. The numbers of compartments
and trains are the counts used by the label in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusLabel`.

The numbers of compartments and of trains and the product of the signs of the trains, which is the
Jacobi symbol `(2 | m)` of the odd part `m` of the determinant, are proved to be genus invariants,
and so is the whole `2`-adic symbol of a lattice whose dyadic localization is modular (for instance
of odd determinant). The signs of the individual trains are proved to be genus invariants in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolStopSign`. The invariance of the oddities of
the individual compartments, the rest of Conway and Sloane's theorem that the canonical symbol is a
genus invariant, is not proved, nor that the symbol determines the dyadic localization.

## Main definitions

* `TauCeti.IntegralLattice.DyadicBlock`: a constituent of a `2`-adic symbol.
* `TauCeti.IntegralLattice.DyadicBlock.trains` and
  `TauCeti.IntegralLattice.DyadicBlock.compartments` (LMFDB `lattice.conway_genus_symbol`): the
  trains and compartments of a `2`-adic symbol.
* `TauCeti.IntegralLattice.DyadicBlock.trainSign`, `TauCeti.IntegralLattice.DyadicBlock.signWalks`
  and `TauCeti.IntegralLattice.DyadicBlock.canonicalOddity` (LMFDB `lattice.conway_genus_symbol`):
  the sign of a train, the sign walks and the oddity of a compartment in the canonical symbol.
* `TauCeti.IntegralLattice.dyadicJordanSign` and `TauCeti.IntegralLattice.dyadicJordanOddity`: the
  signs and oddities of the constituents of the chosen dyadic Jordan splitting of a lattice.
* `TauCeti.IntegralLattice.dyadicConstituents` (LMFDB `lattice.conway_genus_symbol`): the `2`-adic
  symbol of a lattice read off the chosen splitting.
* `TauCeti.IntegralLattice.compartmentOddities` and `TauCeti.IntegralLattice.trainSigns`
  (LMFDB `lattice.conway_genus_symbol`): the oddities of the compartments and the signs of the
  trains of the canonical `2`-adic symbol of a lattice.

## Main results

* `TauCeti.IntegralLattice.DyadicBlock.length_trains` and
  `TauCeti.IntegralLattice.DyadicBlock.length_compartments`: the numbers of trains and compartments
  are those counted in the label of a genus.
* `LinearMap.BilinForm.IsJordanSplitting.prod_dyadicSign_eq_χ₈`: the product of the dyadic signs of
  a Jordan splitting is `χ₈` of the unit part of the determinant.
* `LinearMap.BilinForm.IsJordanSplitting.prod_dyadicSign_eq`: it is an isometry invariant.
* `TauCeti.IntegralLattice.eq_one_or_eq_neg_one_of_mem_trainSigns`: the signs of the trains are
  `±1`.
* `TauCeti.IntegralLattice.prod_trainSigns_eq_χ₈`: the product of the signs of the trains of a
  lattice is `χ₈` of the odd part of its determinant.
* `TauCeti.IntegralLattice.SameGenus.prod_trainSigns_eq`: it is a genus invariant.
* `TauCeti.IntegralLattice.SameGenus.length_compartmentOddities_eq` and
  `TauCeti.IntegralLattice.SameGenus.length_trainSigns_eq`: the numbers of compartments and trains
  are genus invariants.
* `TauCeti.IntegralLattice.SameGenus.dyadicConstituents_eq_of_jordanRank_eq_zero`: the `2`-adic
  symbol of a lattice with a modular dyadic localization is a genus invariant.
-/

open List Module

open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

/-- A **constituent of a `2`-adic symbol** (LMFDB `lattice.conway_genus_symbol`; Conway and Sloane,
*Sphere Packings, Lattices and Groups*, Chapter 15, §7.3): a form `q f_q`, `q = 2 ^ k`, recorded
by its scale exponent `k`, the rank `n_q` and the type `I` or `II` of the unimodular form `f_q`,
its sign `ε_q = ±1` and its oddity `t_q ∈ ℤ/8`. In the `2`-adic symbol it is written
`q^{ε_q n_q}_{t_q}` when `f_q` has type `I` and `q^{ε_q n_q}` when it has type `II`. -/
@[ext]
structure DyadicBlock where
  /-- The scale exponent `k` of the scale `q = 2 ^ k`. -/
  scale : ℕ
  /-- The rank `n_q`. -/
  rank : ℕ
  /-- The type, `I` or `II`. -/
  type : ConwayType
  /-- The sign `ε_q`. -/
  sign : ℤ
  /-- The oddity `t_q`. -/
  oddity : ZMod 8
  deriving DecidableEq

namespace DyadicBlock

variable (l T C : List DyadicBlock) (r : DyadicBlock → DyadicBlock → Bool) (a b c : DyadicBlock)
  (g : List DyadicBlock)

/-- Two consecutive nonzero constituents `b` and `c` of a `2`-adic symbol, of scale exponents
`v < w`, lie in the same **train** (Conway and Sloane, LMFDB `lattice.conway_genus_symbol`) when
`w = v + 1` and one of them has type `I`, or `w = v + 2` and both have type `I`. These are the
conditions under which, counting the zero constituents in between (of type `II`), of any two
constituents of consecutive scales one at least has type `I`. -/
def sameTrain : Bool :=
  c.scale == b.scale + 1 && (b.type == .I || c.type == .I) ||
    c.scale == b.scale + 2 && b.type == .I && c.type == .I

/-- Two consecutive nonzero constituents `b` and `c` of a `2`-adic symbol lie in the same
**compartment** (Conway and Sloane, LMFDB `lattice.conway_genus_symbol`) when both have type `I`
and their scales are consecutive. -/
def sameCompartment : Bool :=
  c.scale == b.scale + 1 && b.type == .I && c.type == .I

/-- The **trains** (Conway and Sloane, LMFDB `lattice.conway_genus_symbol`) of a `2`-adic symbol,
given by the list `l` of its nonzero constituents in increasing order of scale: the maximal runs of
consecutive constituents in which any two neighbours lie in the same train. -/
def trains : List (List DyadicBlock) :=
  l.splitBy sameTrain

/-- The **compartments** (Conway and Sloane, LMFDB `lattice.conway_genus_symbol`) of a `2`-adic
symbol, given by the list `l` of its nonzero constituents in increasing order of scale: the maximal
runs of constituents of type `I` with consecutive scales. -/
def compartments : List (List DyadicBlock) :=
  (l.splitBy sameCompartment).filter (·.all (·.type == .I))

/-- The **sign of a train** `T` (LMFDB `lattice.conway_genus_symbol`): the product of the signs of
its constituents, which sign walking carries to the first constituent of `T`. -/
def trainSign : ℤ :=
  (T.map sign).prod

/-- The **sign walks** of a train `T = [b₀, …, bₘ]` in the reduction of a `2`-adic symbol to its
canonical form (Conway and Sloane, §7.5–7.6): walking the signs to the start of `T`, from its end,
moves a sign `-1` from `bₗ` to `bₗ₋₁` exactly when the product of the signs of `bₗ, …, bₘ` is
`-1`. These are the pairs `(bₗ₋₁, bₗ)` returned. -/
def signWalks : List (DyadicBlock × DyadicBlock) :=
  ((T.zip T.tail).zip T.tail.tails).filterMap fun p ↦ if trainSign p.2 = -1 then some p.1 else none

/-- The **oddity of a compartment** `C` in the canonical `2`-adic symbol of Conway and Sloane
(LMFDB `lattice.conway_genus_symbol`), whose nonzero constituents form the list `l`: the total
oddity of the constituents of `C` (oddity fusion), plus `4` for every sign walk between two
constituents one of which lies in `C` (sign walking: each step between consecutive scales changes
the oddity of a compartment by `4`, and a walk between scales `v` and `v + 2` is two steps). -/
def canonicalOddity : ZMod 8 :=
  (C.map oddity).sum + 4 * ((trains l).flatMap signWalks |>.countP fun p ↦ p.1 ∈ C ∨ p.2 ∈ C)

lemma trainSign_eq_one_or_eq_neg_one (hT : ∀ b ∈ T, b.sign = 1 ∨ b.sign = -1) :
    trainSign T = 1 ∨ trainSign T = -1 :=
  Int.isUnit_iff.mp <| List.prod_isUnit fun s hs ↦ by
    rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
    exact Int.isUnit_iff.mpr (hT b hb)

lemma prod_map_trainSign : ((trains l).map trainSign).prod = (l.map sign).prod := by
  conv_rhs => rw [← List.flatten_splitBy sameTrain l]
  rw [List.map_flatten, List.prod_flatten, List.map_map]
  rfl

lemma splitBy_loop_eq_append (acc : List (List DyadicBlock)) :
    splitBy.loop r l b g acc = acc.reverse ++ splitBy.loop r l b g [] := by
  induction l generalizing b g acc with
  | nil => simp [splitBy.loop]
  | cons c l ih =>
    cases hbc : r b c
    · simp only [splitBy.loop, hbc]
      rw [ih c [] ((b :: g).reverse :: acc), ih c [] [(b :: g).reverse]]
      simp
    · simp [splitBy.loop, hbc, ih _ _ acc]

lemma splitBy_loop_append_singleton :
    splitBy.loop r l b (g ++ [a]) [] = (splitBy.loop r l b g []).modifyHead (a :: ·) := by
  induction l generalizing b g with
  | nil => simp [splitBy.loop]
  | cons c l ih =>
    cases hbc : r b c
    · simp [splitBy.loop, hbc, splitBy_loop_eq_append l r c [] [_]]
    · simpa [splitBy.loop, hbc] using ih c (b :: g)

lemma splitBy_cons_cons : (a :: b :: l).splitBy r =
    if r a b then ((b :: l).splitBy r).modifyHead (a :: ·) else [a] :: (b :: l).splitBy r := by
  cases hab : r a b
  · simp [List.splitBy, splitBy.loop, hab, splitBy_loop_eq_append l r b [] [[a]]]
  · simpa [List.splitBy, splitBy.loop, hab] using splitBy_loop_append_singleton l r a b []

lemma trains_singleton : trains [a] = [[a]] :=
  rfl

/-- **The trains are those counted in the label of a genus**: their number is
`TauCeti.IntegralLattice.GenusLabelData.trainCount` of the scales and types of the constituents. -/
lemma length_trains :
    (trains l).length = GenusLabelData.trainCount (l.map fun b ↦ (b.scale, b.type)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [List.map_cons] at ih
      rw [trains, splitBy_cons_cons, List.map_cons, List.map_cons, GenusLabelData.trainCount,
        ← ih, trains]
      by_cases hab : sameTrain a b = true
      · rw [ite_eq_left hab, List.length_modifyHead, ite_eq_left, zero_add]
        simpa [sameTrain, and_assoc] using hab
      · rw [ite_eq_right hab, List.length_cons, ite_eq_right, add_comm]
        simpa [sameTrain] using hab

/-- **The compartments are those counted in the label of a genus**: their number is
`TauCeti.IntegralLattice.GenusLabelData.compartmentCount` of the scales and types of the
constituents. -/
lemma length_compartments : (compartments l).length =
    GenusLabelData.compartmentCount (l.map fun b ↦ (b.scale, b.type)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => cases ha : a.type <;> simp [compartments, List.splitBy, splitBy.loop,
        GenusLabelData.compartmentCount, ha]
    | cons b l =>
      rw [List.map_cons] at ih
      rw [compartments, splitBy_cons_cons, List.map_cons, List.map_cons,
        GenusLabelData.compartmentCount, ← ih, compartments]
      by_cases hab : sameCompartment a b = true
      · rw [ite_eq_left hab]
        simp only [sameCompartment, Bool.and_eq_true, beq_iff_eq] at hab
        rw [ite_eq_right fun h ↦ h.2 ⟨hab.1.1, hab.2⟩, zero_add]
        rcases h : (b :: l).splitBy sameCompartment with _ | ⟨g, G⟩
        · exact absurd h (List.splitBy_ne_nil.mpr (List.cons_ne_nil b l))
        · simp only [List.modifyHead_cons, List.filter_cons, List.all_cons, hab.1.2,
            beq_self_eq_true, Bool.true_and]
          split_ifs <;> rfl
      · rw [ite_eq_right hab]
        simp only [sameCompartment, Bool.and_eq_true, beq_iff_eq] at hab
        by_cases ha : a.type = .I
        · rw [ite_eq_left ⟨ha, fun h ↦ hab ⟨⟨h.1, ha⟩, h.2⟩⟩]
          simp [ha, add_comm]
        · rw [ite_eq_right fun h ↦ ha h.1]
          simp [ha]

end DyadicBlock

end TauCeti.IntegralLattice

namespace LinearMap.BilinForm

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup M'] [Module ℤ_[2] M']
  {B : BilinForm ℤ_[2] M} {B' : BilinForm ℤ_[2] M'} {N : ℕ → Submodule ℤ_[2] M}
  {N' : ℕ → Submodule ℤ_[2] M'} {J j : ℕ} (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N)
  (h' : B'.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N') {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma IsometryEquiv.toMatrix₂_basis_map (e : B.IsometryEquiv B') (b : Basis ι ℤ_[2] M) :
    toMatrix₂ (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) B' = toMatrix₂ b b B := by
  ext a c
  rw [toMatrix₂_apply, toMatrix₂_apply, Basis.map_apply, Basis.map_apply,
    IsometryEquiv.coe_toLinearEquiv, e.map_app]

lemma IsJordanSplitting.pow_mul_unitForm (x y : N j) :
    ((2 : ℕ) : ℤ_[2]) ^ j * h.unitForm j x y = B x y := by
  rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.smul_apply, h.pow_smul_unitForm]
  rfl

lemma IsJordanSplitting.unitForm_equivalent_of_eq_top (hj : N j = ⊤) (hj' : N' j = ⊤)
    (hBB' : B.Equivalent B') : (h.unitForm j).Equivalent (h'.unitForm j) := by
  rcases hBB' with ⟨e⟩
  refine ⟨⟨(LinearEquiv.ofTop (N j) hj).trans
    (e.toLinearEquiv.trans (LinearEquiv.ofTop (N' j) hj').symm), fun x y ↦ ?_⟩⟩
  refine mul_left_cancel₀ (pow_ne_zero j PadicInt.irreducible_p.ne_zero) ?_
  rw [h'.pow_mul_unitForm, h.pow_mul_unitForm]
  exact e.map_app y x

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

lemma IsJordanSplitting.dyadicOddity_eq_of_unitForm_equivalent (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hC : (h.unitForm j).Equivalent (h'.unitForm j)) : h.dyadicOddity j = h'.dyadicOddity j :=
  dyadicOddity_eq_of_equivalent (h.isPerfPair_unitForm j) (h.isSymm_unitForm hB)
    (h'.isPerfPair_unitForm j) (h'.isSymm_unitForm hB') hC

lemma IsJordanSplitting.dyadicSign_eq_one (hj : finrank ℤ_[2] (N j) = 0) : h.dyadicSign j = 1 := by
  have : IsEmpty (Fin (finrank ℤ_[2] (N j))) := hj.symm ▸ Fin.isEmpty'
  rw [IsJordanSplitting.dyadicSign, Matrix.det_isEmpty, map_one, map_one]

lemma IsJordanSplitting.det_toMatrix₂_adaptedBasis (hJ : ∀ j, J ≤ j → N j = ⊥) :
    (toMatrix₂ (h.adaptedBasis hJ) (h.adaptedBasis hJ) B).det =
      ((2 : ℕ) : ℤ_[2]) ^ (∑ j : Fin J, (j : ℕ) * finrank ℤ_[2] (N j)) * ∏ j : Fin J,
        (toMatrix₂ (finBasis ℤ_[2] (N j)) (finBasis ℤ_[2] (N j)) (h.unitForm j)).det := by
  rw [h.toMatrix₂_adaptedBasis hJ, Matrix.det_blockDiagonal']
  simp only [Matrix.det_smul, Fintype.card_fin, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

lemma IsJordanSplitting.prod_dyadicSign : ∏ j : Fin J, h.dyadicSign j =
    ZMod.χ₈ (PadicInt.toZModPow 3 (∏ j : Fin J,
      (toMatrix₂ (finBasis ℤ_[2] (N j)) (finBasis ℤ_[2] (N j)) (h.unitForm j)).det)) := by
  simp only [IsJordanSplitting.dyadicSign, map_prod]

variable [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']

lemma IsJordanSplitting.dyadicSign_eq_of_unitForm_equivalent
    (hC : (h.unitForm j).Equivalent (h'.unitForm j)) : h.dyadicSign j = h'.dyadicSign j := by
  rcases hC with ⟨E⟩
  rw [h.dyadicSign_eq (finBasis ℤ_[2] (N j)),
    h'.dyadicSign_eq ((finBasis ℤ_[2] (N j)).map E.toLinearEquiv), E.toMatrix₂_basis_map]

/-- **The product of the dyadic signs is `χ₈` of the unit part of the determinant.** If `N` is a
Jordan splitting of a bilinear form `B` over `ℤ_2`, with constituents `N j` of ranks `n_j`
vanishing from the index `J` on, and the determinant of `B` in some basis is `2 ^ ∑_j j n_j * m`,
then the product of the signs `ε_q = χ₈(det f_q)` of the constituents is `χ₈(m)`. -/
lemma IsJordanSplitting.prod_dyadicSign_eq_χ₈ (hJ : ∀ j, J ≤ j → N j = ⊥) (c : Basis ι ℤ_[2] M)
    {m : ℤ_[2]} (hm : (toMatrix₂ c c B).det =
      ((2 : ℕ) : ℤ_[2]) ^ (∑ j : Fin J, (j : ℕ) * finrank ℤ_[2] (N j)) * m) :
    ∏ j : Fin J, h.dyadicSign j = ZMod.χ₈ (PadicInt.toZModPow 3 m) := by
  have hcard : Fintype.card (Σ j : Fin J, Fin (finrank ℤ_[2] (N j))) = Fintype.card ι := by
    rw [← finrank_eq_card_basis (h.adaptedBasis hJ), ← finrank_eq_card_basis c]
  have hdet : (toMatrix₂ c c B).det =
      (((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard)).toMatrix c).det *
        (toMatrix₂ (h.adaptedBasis hJ) (h.adaptedBasis hJ) B).det *
          (((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard)).toMatrix c).det := by
    rw [← LinearMap.toMatrix₂_mul_basis_toMatrix
      ((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard))
      ((h.adaptedBasis hJ).reindex (Fintype.equivOfCardEq hcard)), Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, det_toMatrix₂_reindex]
  rw [h.det_toMatrix₂_adaptedBasis hJ, hm, mul_left_comm, mul_assoc] at hdet
  rw [h.prod_dyadicSign, mul_left_cancel₀ (pow_ne_zero _ PadicInt.irreducible_p.ne_zero) hdet,
    PadicInt.χ₈_toZModPow_mul_mul
      (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))]

/-- **The product of the dyadic signs of the Jordan constituents is an isometry invariant.** If
two bilinear forms over `ℤ_2` are isometric, then Jordan splittings of them, with constituents
vanishing from the index `J` on, have the same product of the signs `ε_q = χ₈(det f_q)` of their
constituents. -/
lemma IsJordanSplitting.prod_dyadicSign_eq (hJ : ∀ j, J ≤ j → N j = ⊥) (hJ' : ∀ j, J ≤ j → N' j = ⊥)
    (hBB' : B.Equivalent B') : ∏ j : Fin J, h.dyadicSign j = ∏ j : Fin J, h'.dyadicSign j := by
  classical
  rcases hBB' with ⟨e⟩
  have hrank (j : ℕ) : finrank ℤ_[2] (N j) = finrank ℤ_[2] (N' j) :=
    h.finrank_eq_of_equivalent h' ⟨e⟩ PadicInt.irreducible_p.ne_zero
      PadicInt.irreducible_p.not_isUnit j
  rw [h.prod_dyadicSign_eq_χ₈ hJ ((h'.adaptedBasis hJ').map e.symm.toLinearEquiv) ?_,
    h'.prod_dyadicSign]
  rw [e.symm.toMatrix₂_basis_map, h'.det_toMatrix₂_adaptedBasis hJ']
  simp only [hrank]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate] (k : ℕ)

variable (L) in
/-- The **dyadic sign** `ε_q = χ₈(det f_q)` (LMFDB `lattice.conway_genus_symbol`) of the
constituent `q f_q`, `q = 2 ^ k`, of the dyadic Jordan splitting of a nondegenerate integral
lattice `L` chosen by Tau Ceti: `+1` when `det f_q ≡ ±1 mod 8` and `-1` when `det f_q ≡ ±3 mod 8`,
`1` for a zero constituent. Unlike the rank and the type, it depends on the splitting (sign
walking). -/
noncomputable def dyadicJordanSign : ℤ :=
  (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose_spec.dyadicSign k

variable (L) in
/-- The **oddity** `t_q` (LMFDB `lattice.conway_genus_symbol`) of the constituent `q f_q`,
`q = 2 ^ k`, of the dyadic Jordan splitting of a nondegenerate integral lattice `L` chosen by Tau
Ceti: the trace modulo `8` of a diagonalization of `f_q` if it has type `I`, `0` if it has type
`II`. It depends on the splitting (oddity fusion and sign walking). -/
noncomputable def dyadicJordanOddity : ZMod 8 :=
  (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose_spec.dyadicOddity k

variable (L) in
/-- The **`2`-adic symbol** (LMFDB `lattice.conway_genus_symbol`) of a nondegenerate integral
lattice `L` read off the dyadic Jordan splitting chosen by Tau Ceti: its nonzero constituents, in
increasing order of scale, with their scale exponents, ranks, types, signs and oddities. The scale
exponents up to the valuation of the determinant are scanned, which covers all the nonzero
constituents. -/
noncomputable def dyadicConstituents : List DyadicBlock :=
  ((List.range (L.determinant.natAbs.factorization 2 + 1)).filter (L.jordanRank 2 · ≠ 0)).map
    fun v ↦ ⟨v, L.jordanRank 2 v, L.dyadicJordanType v, L.dyadicJordanSign v,
      L.dyadicJordanOddity v⟩

variable (L) in
/-- The **oddities of the compartments** of the canonical `2`-adic symbol (LMFDB
`lattice.conway_genus_symbol`) of a nondegenerate integral lattice `L`, in increasing order of
scale: the total oddity of each compartment after oddity fusion and sign walking, computed from the
chosen dyadic Jordan splitting as in Conway and Sloane, §7.5–7.6, and Sage's
`canonical_2_adic_reduction`. -/
noncomputable def compartmentOddities : List (ZMod 8) :=
  (DyadicBlock.compartments L.dyadicConstituents).map
    (DyadicBlock.canonicalOddity L.dyadicConstituents)

variable (L) in
/-- The **signs of the trains** of the canonical `2`-adic symbol (LMFDB
`lattice.conway_genus_symbol`) of a nondegenerate integral lattice `L`, in increasing order of
scale: the product of the signs of the constituents of each train, which sign walking carries to
its first constituent. -/
noncomputable def trainSigns : List ℤ :=
  (DyadicBlock.trains L.dyadicConstituents).map DyadicBlock.trainSign

/-- **The signs of the trains are `±1`.** -/
lemma eq_one_or_eq_neg_one_of_mem_trainSigns {s : ℤ} (hs : s ∈ L.trainSigns) : s = 1 ∨ s = -1 := by
  rcases List.mem_map.mp hs with ⟨T, hT, rfl⟩
  refine DyadicBlock.trainSign_eq_one_or_eq_neg_one T fun b hb ↦ ?_
  have hbl : b ∈ L.dyadicConstituents := by
    rw [← List.flatten_splitBy DyadicBlock.sameTrain L.dyadicConstituents]
    exact List.mem_flatten.mpr ⟨T, hT, hb⟩
  rcases List.mem_map.mp hbl with ⟨v, -, rfl⟩
  exact (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.dyadicSign_eq_one_or_eq_neg_one

lemma dyadicJordanSign_eq_one (hk : L.jordanRank 2 k = 0) : L.dyadicJordanSign k = 1 :=
  (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.dyadicSign_eq_one hk

lemma prod_trainSigns : L.trainSigns.prod =
    ∏ j : Fin (L.determinant.natAbs.factorization 2 + 1), L.dyadicJordanSign j := by
  rw [trainSigns, DyadicBlock.prod_map_trainSign, dyadicConstituents, List.map_map,
    ← Finset.prod_range, ← Finset.prod_filter_of_ne fun i _ ↦ mt (dyadicJordanSign_eq_one i),
    Finset.prod_eq_multiset_prod, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.map_coe, Multiset.prod_coe]
  rfl

lemma dyadicJordanSplitting_eq_bot {j : ℕ} (hj : L.determinant.natAbs.factorization 2 < j) :
    (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose j = ⊥ :=
  Submodule.finrank_eq_zero.mp (L.jordanRank_eq_zero_of_lt 2 hj)

/-- **The product of the signs of the trains is the Jacobi symbol `(2 | m)` of the odd part `m`
of the determinant**: `χ₈(m)`, `+1` when `m ≡ ±1 mod 8` and `-1` when `m ≡ ±3 mod 8`, where
`det L = 2 ^ v * m` with `m` odd. -/
lemma prod_trainSigns_eq_χ₈ :
    L.trainSigns.prod = ZMod.χ₈ (L.determinant / 2 ^ L.determinant.natAbs.factorization 2 : ℤ) := by
  have hv : ∑ j : Fin (L.determinant.natAbs.factorization 2 + 1), (j : ℕ) * finrank ℤ_[2]
      ((L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose j) =
        L.determinant.natAbs.factorization 2 := by
    refine ((L.factorization_natAbs_determinant 2).trans ?_).symm
    rw [finsum_eq_sum_of_support_subset _
      (s := Finset.range (L.determinant.natAbs.factorization 2 + 1)) fun k hk ↦ ?_,
      Finset.sum_range]
    · rfl
    rw [Finset.coe_range, Set.mem_Iio, Nat.lt_succ_iff]
    by_contra hkv
    exact Function.mem_support.mp hk <| by
      rw [L.jordanRank_eq_zero_of_lt 2 (not_le.mp hkv), mul_zero]
  have h2 : (2 : ℤ) ^ L.determinant.natAbs.factorization 2 ∣ L.determinant := by
    exact_mod_cast Int.natCast_dvd.mpr (Nat.ordProj_dvd _ 2)
  have hdet : (LinearMap.toMatrix₂ ((Free.chooseBasis ℤ L).baseChange ℤ_[2])
      ((Free.chooseBasis ℤ L).baseChange ℤ_[2]) (L.localIntegralForm 2)).det =
        (L.determinant : ℤ_[2]) :=
    L.det_toMatrix_localIntegralForm 2 _
  have hχ : ZMod.χ₈ (L.determinant / 2 ^ L.determinant.natAbs.factorization 2 : ℤ) =
      ZMod.χ₈ (PadicInt.toZModPow 3
        ((L.determinant / 2 ^ L.determinant.natAbs.factorization 2 : ℤ) : ℤ_[2])) := by
    rw [map_intCast (PadicInt.toZModPow 3)]
  rw [prod_trainSigns, hχ]
  refine (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.prod_dyadicSign_eq_χ₈
    (fun j hj ↦ dyadicJordanSplitting_eq_bot hj) ((Free.chooseBasis ℤ L).baseChange ℤ_[2]) ?_
  rw [hdet, hv, Nat.cast_ofNat]
  exact_mod_cast (Int.mul_ediv_cancel' h2).symm

/-- **The product of the signs of the trains is a genus invariant**: it is the product of the
dyadic signs of all the Jordan constituents, an isometry invariant of the dyadic localization. -/
lemma SameGenus.prod_trainSigns_eq (h : L.SameGenus M) : L.trainSigns.prod = M.trainSigns.prod := by
  rw [prod_trainSigns, prod_trainSigns, ← h.natAbs_determinant_eq]
  exact (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.prod_dyadicSign_eq
    (M.exists_isJordanSplitting_localIntegralForm 2 M.form_nondegenerate).choose_spec
    (fun j hj ↦ dyadicJordanSplitting_eq_bot hj)
    (fun j hj ↦ dyadicJordanSplitting_eq_bot (h.natAbs_determinant_eq ▸ hj))
    (h.localIntegralForm_equivalent 2)

lemma SameGenus.dyadicConstituents_eq (h : L.SameGenus M)
    (hsign : ∀ k, L.jordanRank 2 k ≠ 0 → L.dyadicJordanSign k = M.dyadicJordanSign k)
    (hodd : ∀ k, L.jordanRank 2 k ≠ 0 → L.dyadicJordanOddity k = M.dyadicJordanOddity k) :
    L.dyadicConstituents = M.dyadicConstituents := by
  rw [dyadicConstituents, dyadicConstituents, ← h.natAbs_determinant_eq,
    List.filter_congr fun k _ ↦ by rw [h.jordanRank_eq 2 k]]
  refine List.map_congr_left fun k hk ↦ ?_
  have hk' : L.jordanRank 2 k ≠ 0 := by
    rw [h.jordanRank_eq 2 k]
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  exact DyadicBlock.ext rfl (h.jordanRank_eq 2 k) (h.dyadicJordanType_eq k) (hsign k hk')
    (hodd k hk')

lemma SameGenus.map_dyadicConstituents_eq (h : L.SameGenus M) :
    L.dyadicConstituents.map (fun b ↦ (b.scale, b.type)) =
      M.dyadicConstituents.map (fun b ↦ (b.scale, b.type)) := by
  rw [dyadicConstituents, dyadicConstituents, ← h.natAbs_determinant_eq,
    List.filter_congr fun k _ ↦ by rw [h.jordanRank_eq 2 k], List.map_map, List.map_map]
  exact List.map_congr_left fun k _ ↦ by
    rw [Function.comp_apply, Function.comp_apply, h.dyadicJordanType_eq k]

/-- **The number of compartments of the canonical `2`-adic symbol is a genus invariant.** -/
lemma SameGenus.length_compartmentOddities_eq (h : L.SameGenus M) :
    L.compartmentOddities.length = M.compartmentOddities.length := by
  rw [compartmentOddities, compartmentOddities, List.length_map, List.length_map,
    DyadicBlock.length_compartments, DyadicBlock.length_compartments, h.map_dyadicConstituents_eq]

/-- **The number of trains of the canonical `2`-adic symbol is a genus invariant.** -/
lemma SameGenus.length_trainSigns_eq (h : L.SameGenus M) :
    L.trainSigns.length = M.trainSigns.length := by
  rw [trainSigns, trainSigns, List.length_map, List.length_map, DyadicBlock.length_trains,
    DyadicBlock.length_trains, h.map_dyadicConstituents_eq]

lemma dyadicJordanSplitting_eq_top (hk : ∀ j, j ≠ k → L.jordanRank 2 j = 0) :
    (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose k = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.isInternal.submodule_iSup_eq_top]
  refine iSup_le fun j ↦ ?_
  rcases eq_or_ne j k with rfl | hjk
  · exact le_rfl
  · rw [Submodule.finrank_eq_zero.mp (hk j hjk)]
    exact bot_le

/-- **The `2`-adic symbol of a lattice with a modular dyadic localization is a genus invariant.**
If the dyadic Jordan decompositions of a nondegenerate lattice `L` have a single nonzero
constituent, of scale `2 ^ k` (for instance when the determinant of `L` is odd, `k = 0`), then
lattices in the genus of `L` have the same constituents, with the same signs and oddities. -/
lemma SameGenus.dyadicConstituents_eq_of_jordanRank_eq_zero (h : L.SameGenus M)
    (hk : ∀ j, j ≠ k → L.jordanRank 2 j = 0) : L.dyadicConstituents = M.dyadicConstituents := by
  have hk' (j : ℕ) (hj : j ≠ k) : M.jordanRank 2 j = 0 :=
    (h.jordanRank_eq 2 j).symm.trans (hk j hj)
  have hC : (((L.exists_isJordanSplitting_localIntegralForm 2
      L.form_nondegenerate).choose_spec.unitForm k).Equivalent
      ((M.exists_isJordanSplitting_localIntegralForm 2
        M.form_nondegenerate).choose_spec.unitForm k)) :=
    (L.exists_isJordanSplitting_localIntegralForm 2
      L.form_nondegenerate).choose_spec.unitForm_equivalent_of_eq_top
      (M.exists_isJordanSplitting_localIntegralForm 2 M.form_nondegenerate).choose_spec
      (dyadicJordanSplitting_eq_top k hk) (dyadicJordanSplitting_eq_top k hk')
      (h.localIntegralForm_equivalent 2)
  refine h.dyadicConstituents_eq (fun j hj ↦ ?_) fun j hj ↦ ?_
  · rcases eq_or_ne j k with rfl | hjk
    · exact (L.exists_isJordanSplitting_localIntegralForm 2
        L.form_nondegenerate).choose_spec.dyadicSign_eq_of_unitForm_equivalent _ hC
    · exact absurd (hk j hjk) hj
  · rcases eq_or_ne j k with rfl | hjk
    · exact (L.exists_isJordanSplitting_localIntegralForm 2
        L.form_nondegenerate).choose_spec.dyadicOddity_eq_of_unitForm_equivalent _
        (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2) hC
    · exact absurd (hk j hjk) hj

end TauCeti.IntegralLattice
