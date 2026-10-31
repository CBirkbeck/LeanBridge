import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolDeterminant

/-!
# Labels of genera of integral lattices

The LMFDB labels a genus of nondegenerate integral lattices (LMFDB `lattice.genus_label`) by a
string `r.s.d.j₁.⋯.jₖ.x`, a deterministic encoding of the Conway genus symbol
(LMFDB `lattice.conway_genus_symbol`):

* `r` is the rank, `s = n₊ - n₋` the signature and `d` the absolute value of the determinant;
* for the primes `p₁ < ⋯ < pₖ` with `pᵢ ^ 2 ∣ d`, `jᵢ` encodes the ranks of the Jordan
  constituents at `pᵢ` in base `62`, one digit `0`–`9`, `a`–`z`, `A`–`Z` per rank;
* `x` is the hexadecimal expansion of a number whose binary digits, from the least significant,
  are: the types of the nonzero dyadic Jordan constituents, the oddities modulo `8` of the
  compartments of the `2`-adic symbol (three bits each), the signs of its trains, and, for every
  odd prime `p ∣ d` in increasing order, the signs of the nonzero Jordan constituents at `p`.

The encoding is formalised as a function `TauCeti.IntegralLattice.GenusLabelData.label` of these
data. For a nondegenerate lattice `L`, the rank, signature, absolute determinant
(`TauCeti.IntegralLattice.SameGenus.natAbs_determinant_eq`), Jordan ranks, signs at the odd primes
and dyadic types (`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolSign`) are genus
invariants, and the compartments and trains are determined by the dyadic types. The oddities of the
compartments and the signs of the trains of Conway and Sloane's canonical `2`-adic symbol, which
are genus invariants by oddity fusion and sign walking, are not formalised: they enter as
parameters of the label of `L`, which is a genus invariant for given parameters
(`TauCeti.IntegralLattice.SameGenus.genusLabel_eq`).

The knowl leaves some conventions open, which are fixed as follows.

* "Rank decompositions ..., omitting the first": `jᵢ` lists the ranks `n_v` of the constituents of
  scale `pᵢ ^ v` for `2 ≤ v ≤ m`, `m` the largest scale exponent of a nonzero constituent, and is
  empty when `m ≤ 1`. This is the reading under which the knowl's example holds with its pairs
  read as (scale exponent, rank): `(3, 1), (4, 10), (6, 37)` give `01a0B`, that is `n₂, …, n₆`,
  while omitting only `n₀`, as the text says, would give `001a0B`. The example also fits the text
  if its first entries are positions counted from `1` (scale exponent plus one), the code being
  then `n₁, …, n_m`: the knowl does not settle which. Since `∑_v v n_v` is the valuation of `d` at
  `pᵢ` (`TauCeti.IntegralLattice.factorization_natAbs_determinant`), the ranks `n₀` and `n₁` are
  determined by `r`, this valuation and the others, and the primes with `pᵢ ∥ d` carry no
  information (`n₁ = 1`).
* A bit `1` stands for the type `I` and for the sign `-1`; the bits of an oddity are its binary
  digits from the least significant. Only the scale exponents up to the valuation of `d` are
  scanned, which covers all the nonzero constituents of a lattice
  (`TauCeti.IntegralLattice.jordanRank_eq_zero_of_lt`).

## Main definitions

* `TauCeti.IntegralLattice.base62Digit`: the base `62` digits.
* `TauCeti.IntegralLattice.GenusLabelData` (LMFDB `lattice.genus_label`): the data encoded in the
  label.
* `TauCeti.IntegralLattice.GenusLabelData.blocks` and
  `TauCeti.IntegralLattice.GenusLabelData.dyadicBlocks`: the nonzero Jordan constituents.
* `TauCeti.IntegralLattice.GenusLabelData.rankCode` and
  `TauCeti.IntegralLattice.GenusLabelData.labelPrimes`: the rank codes and the primes that carry
  them.
* `TauCeti.IntegralLattice.GenusLabelData.compartmentCount` and
  `TauCeti.IntegralLattice.GenusLabelData.trainCount`: the numbers of compartments and trains of
  a list of dyadic constituents.
* `TauCeti.IntegralLattice.GenusLabelData.labelBits`: the bits of the last component.
* `TauCeti.IntegralLattice.GenusLabelData.label` (LMFDB `lattice.genus_label`): the label.
* `TauCeti.IntegralLattice.genusLabelData` and `TauCeti.IntegralLattice.genusLabel`
  (LMFDB `lattice.genus_label`): the label data and the label of a lattice, for given oddities of
  the compartments and signs of the trains.

## Main results

* `TauCeti.IntegralLattice.SameGenus.natAbs_determinant_eq`: lattices in the same genus have the
  same absolute determinant.
* `TauCeti.IntegralLattice.SameGenus.genusLabelData_eq` and
  `TauCeti.IntegralLattice.SameGenus.genusLabel_eq`: the label data and the label are genus
  invariants.
-/

open Module

open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

lemma associated_determinant_of_equivalent (p : ℕ) [Fact p.Prime]
    (hLM : (L.localIntegralForm p).Equivalent (M.localIntegralForm p)) :
    Associated (L.determinant : ℤ_[p]) (M.determinant : ℤ_[p]) := by
  classical
  rcases hLM with ⟨e⟩
  have hG : (L.localIntegralForm p).toMatrix ((Free.chooseBasis ℤ L).baseChange ℤ_[p]) =
      (M.localIntegralForm p).toMatrix
        (((Free.chooseBasis ℤ L).baseChange ℤ_[p]).map e.toLinearEquiv) := by
    ext i j
    rw [BilinForm.toMatrix_apply, BilinForm.toMatrix_apply, Basis.map_apply, Basis.map_apply,
      e.coe_toLinearEquiv, e.map_app]
  have hcard :
      Fintype.card (Free.ChooseBasisIndex ℤ M) = Fintype.card (Free.ChooseBasisIndex ℤ L) := by
    rw [← finrank_eq_card_basis ((Free.chooseBasis ℤ M).baseChange ℤ_[p]),
      ← finrank_eq_card_basis ((Free.chooseBasis ℤ L).baseChange ℤ_[p])]
    exact e.toLinearEquiv.finrank_eq.symm
  rw [← L.det_toMatrix_localIntegralForm p (Free.chooseBasis ℤ L),
    ← M.det_toMatrix_localIntegralForm p
      ((Free.chooseBasis ℤ M).reindex (Fintype.equivOfCardEq hcard)), hG,
    ← BilinForm.toMatrix_mul_basis_toMatrix
      (((Free.chooseBasis ℤ M).reindex (Fintype.equivOfCardEq hcard)).baseChange ℤ_[p]),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm, ← mul_assoc]
  exact associated_unit_mul_left _ _ <| (Matrix.isUnit_det_of_right_inverse
    (Basis.toMatrix_mul_toMatrix_flip _ _)).mul (Matrix.isUnit_det_of_right_inverse
    (Basis.toMatrix_mul_toMatrix_flip _ _))

variable [L.IsNondegenerate] [M.IsNondegenerate]

/-- **Lattices in the same genus have the same absolute determinant**: the determinants agree up
to a unit of `ℤ_p` at every prime `p`. -/
lemma SameGenus.natAbs_determinant_eq (h : L.SameGenus M) :
    L.determinant.natAbs = M.determinant.natAbs := by
  have hdvd (p : ℕ) (hp : p.Prime) (n : ℕ) :
      p ^ n ∣ L.determinant.natAbs ↔ p ^ n ∣ M.determinant.natAbs := by
    have : Fact p.Prime := ⟨hp⟩
    rcases associated_determinant_of_equivalent p (h.localIntegralForm_equivalent p) with ⟨u, hu⟩
    rw [← Int.natCast_dvd, ← Int.natCast_dvd, Nat.cast_pow, ← PadicInt.norm_int_le_pow_iff_dvd,
      ← PadicInt.norm_int_le_pow_iff_dvd, ← hu, norm_mul, PadicInt.isUnit_iff.mp u.isUnit,
      mul_one]
  have hL : L.determinant.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)
  have hM : M.determinant.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (M.determinant_ne_zero_iff.mpr M.form_nondegenerate)
  refine Nat.dvd_antisymm ((Nat.factorization_prime_le_iff_dvd hL hM).mp fun p hp ↦ ?_)
    ((Nat.factorization_prime_le_iff_dvd hM hL).mp fun p hp ↦ ?_)
  · exact (hp.pow_dvd_iff_le_factorization hM).mp ((hdvd p hp _).mp (Nat.ordProj_dvd _ p))
  · exact (hp.pow_dvd_iff_le_factorization hL).mp ((hdvd p hp _).mpr (Nat.ordProj_dvd _ p))

/-- The **base `62` digit** of `n < 62` (LMFDB `lattice.genus_label`): `0`–`9` for `n < 10`, then
`a`–`z`, then `A`–`Z`. -/
def base62Digit (n : ℕ) : Char :=
  if n < 10 then .ofNat (48 + n) else if n < 36 then .ofNat (87 + n) else .ofNat (29 + n)

/-- The data encoded in the **label of a genus** of integral lattices (LMFDB `lattice.genus_label`):
the rank, the signature `n₊ - n₋`, the absolute value of the determinant, the ranks and signs of the
Jordan constituents at every prime, the types of the dyadic Jordan constituents, and the oddities of
the compartments and the signs of the trains of the canonical `2`-adic symbol. -/
structure GenusLabelData where
  /-- The rank `r`. -/
  rank : ℕ
  /-- The signature `s = n₊ - n₋`. -/
  signature : ℤ
  /-- The absolute value `d` of the determinant. -/
  absDet : ℕ
  /-- The rank of the Jordan constituent of scale `p ^ v` at the prime `p`. -/
  jordanRank : ℕ → ℕ → ℕ
  /-- The sign of the Jordan constituent of scale `p ^ v` at the odd prime `p`. -/
  jordanSign : ℕ → ℕ → ℤ
  /-- The type of the dyadic Jordan constituent of scale `2 ^ v`. -/
  dyadicType : ℕ → ConwayType
  /-- The oddity of the `i`-th compartment of the canonical `2`-adic symbol, from scale `1` up. -/
  compartmentOddity : ℕ → ZMod 8
  /-- The sign of the `i`-th train of the canonical `2`-adic symbol, from scale `1` up. -/
  trainSign : ℕ → ℤ

namespace GenusLabelData

variable (D : GenusLabelData) (p : ℕ)

/-- The scale exponents `v ≤ v_p(d)` of the nonzero Jordan constituents at `p`, increasing. -/
def blocks : List ℕ :=
  (List.range (D.absDet.factorization p + 1)).filter (D.jordanRank p · ≠ 0)

/-- The **rank code** at `p` in the label (LMFDB `lattice.genus_label`): the base `62` digits of the
ranks `n_v` of the Jordan constituents of scale `p ^ v`, `2 ≤ v ≤ m`, where `m` is the largest
scale exponent of a nonzero constituent. -/
def rankCode : String :=
  .ofList <| (List.range' 2 ((D.blocks p).getLast?.getD 0 - 1)).map
    (base62Digit <| D.jordanRank p ·)

/-- The primes `p` with `p ^ 2 ∣ d`, increasing, whose rank codes enter the label. -/
def labelPrimes : List ℕ :=
  D.absDet.primeFactorsList.dedup.filter (· ^ 2 ∣ D.absDet)

/-- The **number of compartments** (Conway and Sloane) of a list of nonzero dyadic Jordan
constituents, given by their scale exponents and types in increasing order: the maximal runs of
constituents of type `I` with consecutive scale exponents. It counts the constituents of type `I`
which do not continue into the next one. -/
def compartmentCount : List (ℕ × ConwayType) → ℕ
  | [] => 0
  | [(_, s)] => if s = .I then 1 else 0
  | (v, s) :: (w, t) :: l => (if s = .I ∧ ¬(w = v + 1 ∧ t = .I) then 1 else 0) +
    compartmentCount ((w, t) :: l)

/-- The **number of trains** (Conway and Sloane) of a list of nonzero dyadic Jordan constituents,
given by their scale exponents and types in increasing order: the maximal runs in which, counting
the zero constituents in between, of any two constituents of consecutive scales one at least has
type `I`. Two consecutive nonzero constituents of scale exponents `v < w` are in the same train when
`w = v + 1` and one of them has type `I`, or `w = v + 2` and both have type `I`. -/
def trainCount : List (ℕ × ConwayType) → ℕ
  | [] => 0
  | [_] => 1
  | (v, s) :: (w, t) :: l =>
    (if w = v + 1 ∧ (s = .I ∨ t = .I) ∨ w = v + 2 ∧ s = .I ∧ t = .I then 0 else 1) +
      trainCount ((w, t) :: l)

/-- The nonzero dyadic Jordan constituents, by their scale exponents and types. -/
def dyadicBlocks : List (ℕ × ConwayType) :=
  (D.blocks 2).map fun v ↦ (v, D.dyadicType v)

/-- The bits of the last component of the label (LMFDB `lattice.genus_label`), from the least
significant: the types of the nonzero dyadic constituents (`1` for type `I`), the oddities of the
compartments (three bits each), the signs of the trains, and the signs of the nonzero constituents
at the odd primes dividing `d`, increasing (`1` for the sign `-1`). -/
def labelBits : List Bool :=
  (D.dyadicBlocks.map fun b ↦ decide (b.2 = .I)) ++
    (List.range (compartmentCount D.dyadicBlocks)).flatMap
      (fun i ↦ [(D.compartmentOddity i).val.testBit 0, (D.compartmentOddity i).val.testBit 1,
        (D.compartmentOddity i).val.testBit 2]) ++
    (List.range (trainCount D.dyadicBlocks)).map (fun i ↦ decide (D.trainSign i = -1)) ++
    (D.absDet.primeFactorsList.dedup.filter (· ≠ 2)).flatMap
      fun q ↦ (D.blocks q).map fun v ↦ decide (D.jordanSign q v = -1)

/-- The **label of a genus** (LMFDB `lattice.genus_label`), `r.s.d.j₁.⋯.jₖ.x`: the rank, the
signature, the absolute determinant, the rank codes at the primes `p` with `p ^ 2 ∣ d`, and the
lowercase hexadecimal expansion of the number with binary digits `labelBits`. -/
def label : String :=
  s!"{D.rank}.{D.signature}.{D.absDet}" ++ .join (D.labelPrimes.map fun q ↦ "." ++ D.rankCode q) ++
    "." ++ .ofList (Nat.toDigits 16 (D.labelBits.foldr (fun b n ↦ 2 * n + b.toNat) 0))

end GenusLabelData

variable (oddity : ℕ → ZMod 8) (trainSign : ℕ → ℤ)

open scoped Classical in
variable (L) in
/-- The **data of the label of the genus** (LMFDB `lattice.genus_label`) of a nondegenerate
integral lattice `L`: its rank, signature, absolute determinant, Jordan ranks, signs at the odd
primes and dyadic types, with given oddities of the compartments and signs of the trains of the
canonical `2`-adic symbol, whose definition is not formalised. -/
noncomputable def genusLabelData : GenusLabelData where
  rank := finrank ℤ L
  signature := L.sigPos - L.sigNeg
  absDet := L.determinant.natAbs
  jordanRank q v :=
    if hq : q.Prime then
      haveI : Fact q.Prime := ⟨hq⟩
      L.jordanRank q v
    else 0
  jordanSign q v :=
    if hq : q.Prime then
      haveI : Fact q.Prime := ⟨hq⟩
      L.jordanSign q v
    else 1
  dyadicType := L.dyadicJordanType
  compartmentOddity := oddity
  trainSign := trainSign

variable (L) in
/-- The **label of the genus** (LMFDB `lattice.genus_label`) of a nondegenerate integral lattice
`L`, with given oddities of the compartments and signs of the trains of the canonical `2`-adic
symbol. -/
noncomputable def genusLabel : String :=
  (L.genusLabelData oddity trainSign).label

/-- **The label data are genus invariants**, for given oddities of the compartments and signs of
the trains. -/
lemma SameGenus.genusLabelData_eq (h : L.SameGenus M) :
    L.genusLabelData oddity trainSign = M.genusLabelData oddity trainSign := by
  have hrank : finrank ℤ L = finrank ℤ M := by
    rw [L.finrank_carrier, M.finrank_carrier, ← L.signature_sum_eq_finrank,
      ← M.signature_sum_eq_finrank]
    exact congrArg (fun s : ℕ × ℕ × ℕ ↦ s.1 + s.2.1 + s.2.2) h.signature_eq
  have hsig : (L.sigPos : ℤ) - L.sigNeg = M.sigPos - M.sigNeg :=
    congrArg (fun s : ℕ × ℕ × ℕ ↦ (s.1 : ℤ) - s.2.2) h.signature_eq
  rw [genusLabelData, genusLabelData, hrank, hsig, h.natAbs_determinant_eq,
    GenusLabelData.mk.injEq]
  refine ⟨rfl, rfl, rfl, funext fun q ↦ funext fun v ↦ ?_, funext fun q ↦ funext fun v ↦ ?_,
    funext h.dyadicJordanType_eq, rfl, rfl⟩
  · split_ifs with hq
    · have : Fact q.Prime := ⟨hq⟩
      exact h.jordanRank_eq q v
    · rfl
  · split_ifs with hq
    · have : Fact q.Prime := ⟨hq⟩
      exact h.jordanSign_eq q v
    · rfl

/-- **The label is a genus invariant**, for given oddities of the compartments and signs of the
trains. -/
lemma SameGenus.genusLabel_eq (h : L.SameGenus M) :
    L.genusLabel oddity trainSign = M.genusLabel oddity trainSign :=
  congrArg GenusLabelData.label (h.genusLabelData_eq oddity trainSign)

end TauCeti.IntegralLattice
