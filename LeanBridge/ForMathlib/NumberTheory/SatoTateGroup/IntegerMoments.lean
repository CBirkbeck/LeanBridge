import LeanBridge.ForMathlib.LinearAlgebra.Matrix.Compound
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.TraceMoments
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# The moments of a Sato–Tate group are integers

The moment statistics of a Sato–Tate group `G ⊆ U(d)` (LMFDB `st_group.moments`) are the moments
`E[Xⁿ]`, for the Haar probability measure of `G`, of the coefficients `aᵢ` of the characteristic
polynomial, of the elementary symmetric functions `eᵢ = (-1)ⁱ aᵢ` of the eigenvalues and of their
power sums `sᵢ`. The knowl says that these moment sequences are integer sequences. This file
proves it for every Sato–Tate group, a closed subgroup of `U(d)`, with no further hypothesis.

The function `eᵢ` is the character of the `i`th exterior power `⋀ⁱ ℂ^d` of the standard
representation: in the basis of the wedges of the standard basis vectors, `g` acts on it by its
`i`th compound matrix `Cᵢ(g)`, whose trace is the coefficient of `Xⁱ` in `det(1 + X g)`
(`Matrix.trace_compound`). Hence `eᵢⁿ` is the character of `(⋀ⁱ ℂ^d)^{⊗n}`, and `E[eᵢⁿ]` is the
dimension of the invariants of `G` in that representation, the multiplicity of the trivial
representation (Tau Ceti's `ContRepresentation.integral_character_eq_finrank_invariants`), while
`E[aᵢⁿ] = (-1)^{in} E[eᵢⁿ]`. Here `aᵢ` is the coefficient of `x^{d-i}`, as in the LMFDB's data; the
coefficient of `xⁱ`, the knowl's `aᵢ`, is `a_{d-i}`, so its moments are integers as well.

More generally, the characters of the continuous matrix representations of a compact group are
closed under products (Kronecker products), so that their integer linear combinations, the virtual
characters, form a ring on which the Haar integral takes integer values. The `aᵢ` and `eᵢ` are
virtual characters, and so is each power sum `sᵢ`, an integer polynomial in the `eⱼ` by Newton's
identities, as the knowl says. Hence every integer polynomial in the `aᵢ` has an integer
expectation: the moments of the `sᵢ` and the mixed moments of the moment simplex are integers too.
The knowl's "(or any random variable)" cannot extend the integrality to every random variable,
which fails already for `|a₁|` on `SU(2)`: the integer moment sequences are those of the `aᵢ`, `eᵢ`
and `sᵢ`, and of the integer polynomials in them.

## Main definitions

* `ContRepresentation.ofMatrix`: the continuous representation given by a matrix representation.
* `ContRepresentation.matrixCharacters`: the characters of the continuous matrix representations of
  a topological group.
* `ContRepresentation.virtualCharacterRing`: the ring of virtual characters, which they generate.
* `SatoTateGroup.matrixHom`: the standard representation of a Sato–Tate group, in matrices.
* `SatoTateGroup.exteriorTensorHom`: its representation on `(⋀ⁱ ℂ^d)^{⊗n}`, in matrices.

## Main results

* `ContRepresentation.integral_trace_eq_finrank_invariants`: the Haar integral of the trace of a
  continuous matrix representation of a compact group is the dimension of its invariants.
* `ContRepresentation.exists_integral_eq_intCast`: the Haar integral of a virtual character is an
  integer.
* `SatoTateGroup.moment_esymmEigen_eq_finrank_invariants` (LMFDB `st_group.moments`): `E[eᵢⁿ]` is
  the dimension of the invariants of `G` in `(⋀ⁱ ℂ^d)^{⊗n}`.
* `SatoTateGroup.moment_charpolyCoeff_eq_finrank_invariants` (LMFDB `st_group.moments`):
  `E[aᵢⁿ] = (-1)^{in} E[eᵢⁿ]`, an integer.
* `SatoTateGroup.powerSum_mem_closure_esymmEigen` (LMFDB `st_group.moments`): `sᵢ` is an integer
  polynomial in the `eⱼ`, by Newton's identities.
* `SatoTateGroup.powerSum_mem_closure_charpolyCoeff` (LMFDB `st_group.moments`): `sᵢ` is an integer
  polynomial in the `aⱼ`.
* `SatoTateGroup.moment_eq_integral_map` (LMFDB `st_group.moments`): `E[Xⁿ]` is the `n`th moment of
  the distribution of `X`, the pushforward of the Haar probability measure.
* `SatoTateGroup.exists_moment_eq_intCast`: the moments of a virtual character are integers.
* `SatoTateGroup.exists_moment_powerSum_eq_intCast` (LMFDB `st_group.moments`): `E[sᵢⁿ]` is an
  integer.
* `SatoTateGroup.exists_expectation_aeval_eq_intCast`: the expectation of an integer polynomial in
  the `aᵢ` is an integer.
* `SatoTateGroup.exists_mixedMoment_eq_intCast` (LMFDB `st_group.moment_simplex`): the mixed
  moments `E[a₁^{e₁} ⋯ a_g^{e_g}]` are integers.
-/

open Matrix MeasureTheory Module MvPolynomial Set TauCeti

open scoped Kronecker

namespace ContRepresentation

variable {K ι : Type*} [Group K] [Fintype ι] [DecidableEq ι] (ρ : K →* Matrix ι ι ℂ)

/-- The continuous representation of a group `K` on `EuclideanSpace ℂ ι` given by a matrix
representation `ρ`: `g` acts by the matrix `ρ g`. -/
noncomputable def ofMatrix : ContRepresentation ℂ K (EuclideanSpace ℂ ι) :=
  .ofMonoidHom ((toEuclideanCLM (n := ι) (𝕜 := ℂ) :
    Matrix ι ι ℂ →* EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι).comp ρ)

lemma ofMatrix_apply (g : K) : ofMatrix ρ g = toEuclideanCLM (n := ι) (𝕜 := ℂ) (ρ g) :=
  rfl

variable [TopologicalSpace K] {ρ}

lemma continuous_ofMatrix (hρ : Continuous ρ) : Continuous (ofMatrix ρ) := by
  refine continuous_clm_apply.mpr fun y ↦ ?_
  refine (EuclideanSpace.equiv ι ℂ).symm.continuous.comp (continuous_pi fun a ↦ ?_)
  exact continuous_finsetSum _ fun b _ ↦ (hρ.matrix_elem a b).mul continuous_const

lemma character_ofMatrix (hρ : Continuous ρ) (g : K) :
    character (ofMatrix ρ) (continuous_ofMatrix hρ) g = (ρ g).trace := by
  rw [character_apply, ofMatrix_apply, coe_toEuclideanCLM_eq_toEuclideanLin,
    toEuclideanLin_eq_toLin_orthonormal, trace_toLin_eq]

variable (K) in
/-- The **characters of the continuous matrix representations** of a topological group `K`: the
functions `g ↦ tr σ(g)` for the continuous homomorphisms `σ` from `K` to the square complex
matrices indexed by a finite type. They form a submonoid of the functions on `K`, the character of
a Kronecker product of representations being the product of their characters. -/
def matrixCharacters : Submonoid (K → ℂ) where
  carrier := {f | ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (σ : K →* Matrix κ κ ℂ),
    Continuous σ ∧ ∀ g, (σ g).trace = f g}
  one_mem' := ⟨Unit, inferInstance, inferInstance, 1, continuous_const, fun _ ↦ by simp⟩
  mul_mem' := by
    rintro f₁ f₂ ⟨κ₁, _, _, σ₁, hσ₁, hf₁⟩ ⟨κ₂, _, _, σ₂, hσ₂, hf₂⟩
    refine ⟨κ₁ × κ₂, inferInstance, inferInstance,
      { toFun g := σ₁ g ⊗ₖ σ₂ g
        map_one' := by simp only [map_one, one_kronecker_one]
        map_mul' g h := by simp only [map_mul, mul_kronecker_mul] }, ?_, fun g ↦ ?_⟩
    · exact continuous_matrix fun a b ↦ (hσ₁.matrix_elem a.1 b.1).mul (hσ₂.matrix_elem a.2 b.2)
    · simp only [MonoidHom.coe_mk, OneHom.coe_mk, trace_kronecker, hf₁, hf₂, Pi.mul_apply]

variable (K) in
/-- The ring of **virtual characters** of a topological group `K`: the subring of the functions on
`K` generated by the characters of its continuous matrix representations, that is, their integer
linear combinations. -/
def virtualCharacterRing : Subring (K → ℂ) :=
  Subring.closure (matrixCharacters K)

variable [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- **The Haar integral of the trace of a continuous matrix representation of a compact group is
the dimension of its invariants**, the multiplicity of the trivial representation in it. -/
lemma integral_trace_eq_finrank_invariants (hρ : Continuous ρ) :
    ∫ g, (ρ g).trace ∂haarProb K = Module.finrank ℂ (ofMatrix ρ).invariants := by
  rw [← integral_character_eq_finrank_invariants _ (continuous_ofMatrix hρ)]
  exact integral_congr_ae (.of_forall fun g ↦ (character_ofMatrix hρ g).symm)

/-- **The Haar integral of a virtual character of a compact group is an integer**, a difference of
dimensions of spaces of invariants. -/
lemma exists_integral_eq_intCast {f : K → ℂ} (hf : f ∈ virtualCharacterRing K) :
    ∃ m : ℤ, ∫ g, f g ∂haarProb K = m := by
  rw [virtualCharacterRing, Subring.mem_closure_iff, Submonoid.closure_eq] at hf
  suffices h : Continuous f ∧ ∃ m : ℤ, ∫ g, f g ∂haarProb K = m from h.2
  induction hf using AddSubgroup.closure_induction with
  | mem f hf =>
    rcases hf with ⟨κ, _, _, σ, hσ, hf⟩
    refine ⟨?_, Module.finrank ℂ (ofMatrix σ).invariants, ?_⟩
    · simpa only [← funext hf] using hσ.matrix_trace
    · simp only [← hf, integral_trace_eq_finrank_invariants hσ, Int.cast_natCast]
  | zero => exact ⟨continuous_const, 0, by simp⟩
  | add f₁ f₂ _ _ h₁ h₂ =>
    rcases h₁ with ⟨hc₁, m₁, hm₁⟩
    rcases h₂ with ⟨hc₂, m₂, hm₂⟩
    refine ⟨hc₁.add hc₂, m₁ + m₂, ?_⟩
    rw [Pi.add_def, integral_add (hc₁.integrable_of_hasCompactSupport (.of_compactSpace _))
      (hc₂.integrable_of_hasCompactSupport (.of_compactSpace _)), hm₁, hm₂, Int.cast_add]
  | neg f _ h =>
    rcases h with ⟨hc, m, hm⟩
    exact ⟨hc.neg, -m, by rw [Pi.neg_def, integral_neg, hm, Int.cast_neg]⟩

end ContRepresentation

lemma Multiset.sum_map_pow_eq_mul_esymm_sub_sum {R : Type*} [CommRing R] (s : Multiset R) {k : ℕ}
    (hk : 0 < k) : (s.map (· ^ k)).sum = (-1) ^ (k + 1) * k * s.esymm k -
      ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Set.Ioo 0 k,
        (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  classical
  have h := congrArg (aeval fun x : s.ToType ↦ (x : R)) (psum_eq_mul_esymm_sub_sum s.ToType R k hk)
  have hpsum (j : ℕ) :
      aeval (fun x : s.ToType ↦ (x : R)) (psum s.ToType R j) = (s.map (· ^ j)).sum := by
    rw [← Multiset.map_univ_comp_coe, Finset.sum_map_val]
    simp [psum]
  simpa only [hpsum, map_sub, map_mul, map_pow, map_neg, map_one, map_natCast,
    aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe, map_sum] using h

namespace SatoTateGroup

open ContRepresentation

variable (G : SatoTateGroup) (i n : ℕ) (g : G.toSubgroup) (P : MvPolynomial ℕ ℤ)
  {X : G.toSubgroup → ℂ}

/-- The **standard representation** of a Sato–Tate group `G ⊆ U(d)`, as a homomorphism to the
`d × d` complex matrices. -/
def matrixHom : G.toSubgroup →* Matrix (Fin G.degree) (Fin G.degree) ℂ :=
  (unitary (Matrix (Fin G.degree) (Fin G.degree) ℂ)).subtype.comp G.toSubgroup.subtype

lemma matrixHom_apply : G.matrixHom g = G.matrix g :=
  rfl

lemma continuous_matrixHom : Continuous G.matrixHom :=
  continuous_subtype_val.comp continuous_subtype_val

lemma charpolyCoeff_eq_neg_one_pow_mul_trace :
    G.charpolyCoeff i g = (-1) ^ i * (compound i (G.matrix g)).trace := by
  rw [charpolyCoeff, reverse_charpoly, charpolyRev, sub_eq_add_neg, ← smul_neg,
    ← Matrix.map_neg _ (map_neg Polynomial.C), ← trace_compound, trace_compound_neg]

lemma esymmEigen_eq_trace : G.esymmEigen i g = (compound i (G.matrix g)).trace := by
  rcases le_or_gt i G.degree with hi | hi
  · rw [G.esymmEigen_eq hi, charpolyCoeff_eq_neg_one_pow_mul_trace, ← mul_assoc, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_mul]
  · have : IsEmpty (powersetCard (Fin G.degree) i) := not_nonempty_iff.mp fun h ↦
      (powersetCard.nonempty_iff.mp h).not_gt (by rwa [Fintype.card_fin])
    rw [esymmEigen, Multiset.esymm_of_card_lt (IsAlgClosed.card_roots_eq_natDegree.trans_lt
      (by rwa [G.natDegree_charpoly])), trace_eq_zero_of_isEmpty]

lemma charpolyCoeff_eq_neg_one_pow_mul_esymmEigen :
    G.charpolyCoeff i = (-1) ^ i * G.esymmEigen i :=
  funext fun g ↦ by
    rw [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, esymmEigen_eq_trace,
      charpolyCoeff_eq_neg_one_pow_mul_trace]

/-- The representation `(⋀ⁱ ℂ^d)^{⊗n}` of a Sato–Tate group `G ⊆ U(d)`, the `n`th tensor power of
the `i`th exterior power of its standard representation, in matrices: `g` acts by the Kronecker
power of its `i`th compound matrix `Cᵢ(g)`, on the functions on the `n`-tuples of `i`-element
subsets of `Fin d`. -/
noncomputable def exteriorTensorHom : G.toSubgroup →*
    Matrix (Fin n → powersetCard (Fin G.degree) i) (Fin n → powersetCard (Fin G.degree) i) ℂ where
  toFun g := tensorRep (P := Fin n) (compound i (G.matrixHom g))
  map_one' := by
    rw [map_one, map_one, tensorRep_one]
  map_mul' g h := by
    rw [map_mul, map_mul, tensorRep_mul]

lemma exteriorTensorHom_apply (a b : Fin n → powersetCard (Fin G.degree) i) :
    G.exteriorTensorHom i n g a b = ∏ p, compound i (G.matrixHom g) (a p) (b p) :=
  rfl

lemma continuous_exteriorTensorHom : Continuous (G.exteriorTensorHom i n) := by
  refine continuous_matrix fun a b ↦ ?_
  simp only [exteriorTensorHom_apply]
  exact continuous_finsetProd _ fun p _ ↦
    (G.continuous_matrixHom.matrix_compound i).matrix_elem (a p) (b p)

/-- **The moment `E[eᵢⁿ]` is the dimension of the invariants of `G` in `(⋀ⁱ ℂ^d)^{⊗n}`** (LMFDB
`st_group.moments`), the multiplicity of the trivial representation, a nonnegative integer: `eᵢⁿ`
is the character of that representation. -/
lemma moment_esymmEigen_eq_finrank_invariants :
    G.moment (G.esymmEigen i) n = finrank ℂ (ofMatrix (G.exteriorTensorHom i n)).invariants := by
  rw [← integral_trace_eq_finrank_invariants (G.continuous_exteriorTensorHom i n), moment,
    expectation]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [Pi.pow_apply, esymmEigen_eq_trace]
  exact (trace_tensorRep (P := Fin n) _).trans (by rw [Fintype.card_fin, matrixHom_apply]) |>.symm

/-- **The moment `E[aᵢⁿ]` is `(-1)^{in}` times the dimension of the invariants of `G` in
`(⋀ⁱ ℂ^d)^{⊗n}`** (LMFDB `st_group.moments`): the moments of the coefficients of the characteristic
polynomial are integers. -/
lemma moment_charpolyCoeff_eq_finrank_invariants : G.moment (G.charpolyCoeff i) n =
    (-1) ^ (i * n) * finrank ℂ (ofMatrix (G.exteriorTensorHom i n)).invariants := by
  rw [← moment_esymmEigen_eq_finrank_invariants, moment, moment, expectation, expectation,
    ← integral_const_mul, charpolyCoeff_eq_neg_one_pow_mul_esymmEigen]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.neg_apply, Pi.one_apply]
  rw [mul_pow, ← pow_mul]

lemma esymmEigen_mem_matrixCharacters : G.esymmEigen i ∈ matrixCharacters G.toSubgroup :=
  ⟨powersetCard (Fin G.degree) i, inferInstance, inferInstance, (compound i).comp G.matrixHom,
    G.continuous_matrixHom.matrix_compound i, fun g ↦ (G.esymmEigen_eq_trace i g).symm⟩

lemma esymmEigen_mem_virtualCharacterRing :
    G.esymmEigen i ∈ virtualCharacterRing G.toSubgroup :=
  Subring.subset_closure (G.esymmEigen_mem_matrixCharacters i)

lemma charpolyCoeff_mem_virtualCharacterRing :
    G.charpolyCoeff i ∈ virtualCharacterRing G.toSubgroup :=
  G.charpolyCoeff_eq_neg_one_pow_mul_esymmEigen i ▸
    mul_mem (pow_mem (neg_mem (one_mem _)) i) (G.esymmEigen_mem_virtualCharacterRing i)

lemma powerSum_zero : G.powerSum 0 = G.degree :=
  funext fun g ↦ by
    simp [powerSum, IsAlgClosed.card_roots_eq_natDegree]

/-- **Newton's identities: the power sum `sᵢ` of the eigenvalues is an integer polynomial in the
elementary symmetric functions `eⱼ`** (LMFDB `st_group.moments`), as a random variable on a
Sato–Tate group: it lies in the subring generated by the `eⱼ`. -/
lemma powerSum_mem_closure_esymmEigen : G.powerSum i ∈ Subring.closure (range G.esymmEigen) := by
  induction i using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact G.powerSum_zero ▸ natCast_mem _ _
    · have h : G.powerSum k = (-1) ^ (k + 1) * k * G.esymmEigen k -
          ∑ a ∈ Finset.antidiagonal k with a.1 ∈ Ioo 0 k,
            (-1) ^ a.1 * G.esymmEigen a.1 * G.powerSum a.2 :=
        funext fun g ↦ by
          simpa [powerSum, esymmEigen] using Multiset.sum_map_pow_eq_mul_esymm_sub_sum _ hk
      rw [h]
      refine sub_mem (mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (natCast_mem _ _))
        (Subring.subset_closure ⟨k, rfl⟩)) (sum_mem fun a ha ↦ mul_mem (mul_mem
          (pow_mem (neg_mem (one_mem _)) _) (Subring.subset_closure ⟨a.1, rfl⟩)) (ih a.2 ?_))
      rw [Finset.mem_filter, Finset.mem_antidiagonal, mem_Ioo] at ha
      omega

lemma esymmEigen_eq_neg_one_pow_mul_charpolyCoeff :
    G.esymmEigen i = (-1) ^ i * G.charpolyCoeff i := by
  rw [charpolyCoeff_eq_neg_one_pow_mul_esymmEigen, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]

/-- **Newton's identities: the power sum `sᵢ` of the eigenvalues is an integer polynomial in the
coefficients `aⱼ` of the characteristic polynomial** (LMFDB `st_group.moments`), as a random
variable on a Sato–Tate group: it lies in the subring generated by the `aⱼ`. -/
lemma powerSum_mem_closure_charpolyCoeff : G.powerSum i ∈ Subring.closure (range G.charpolyCoeff) :=
  Subring.closure_le.mpr (range_subset_iff.mpr fun j ↦
    G.esymmEigen_eq_neg_one_pow_mul_charpolyCoeff j ▸
      mul_mem (pow_mem (neg_mem (one_mem _)) j) (Subring.subset_closure ⟨j, rfl⟩))
    (G.powerSum_mem_closure_esymmEigen i)

lemma powerSum_mem_virtualCharacterRing : G.powerSum i ∈ virtualCharacterRing G.toSubgroup :=
  Subring.closure_le.mpr (range_subset_iff.mpr G.esymmEigen_mem_virtualCharacterRing)
    (G.powerSum_mem_closure_esymmEigen i)

/-- **The moment `E[Xⁿ]` of a random variable `X` on a Sato–Tate group is the `n`th moment of its
distribution** (LMFDB `st_group.moments`), the pushforward of the Haar probability measure. -/
lemma moment_eq_integral_map (hX : AEMeasurable X (haarProb G.toSubgroup)) :
    G.moment X n = ∫ z, z ^ n ∂(haarProb G.toSubgroup).map X :=
  (integral_map hX (continuous_pow n).aestronglyMeasurable).symm

/-- **The moments of a virtual character of a Sato–Tate group are integers.** -/
lemma exists_moment_eq_intCast (hX : X ∈ virtualCharacterRing G.toSubgroup) :
    ∃ m : ℤ, G.moment X n = m :=
  exists_integral_eq_intCast (pow_mem hX n)

/-- **The moments `E[sᵢⁿ]` of the power sums of the eigenvalues are integers** (LMFDB
`st_group.moments`). -/
lemma exists_moment_powerSum_eq_intCast : ∃ m : ℤ, G.moment (G.powerSum i) n = m :=
  G.exists_moment_eq_intCast n (G.powerSum_mem_virtualCharacterRing i)

lemma aeval_charpolyCoeff_mem_virtualCharacterRing :
    (fun g ↦ aeval (fun j ↦ G.charpolyCoeff j g) P) ∈ virtualCharacterRing G.toSubgroup := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eq_intCast, map_intCast]
    exact intCast_mem (virtualCharacterRing G.toSubgroup) a
  | add p q hp hq =>
    simp only [map_add]
    exact add_mem hp hq
  | mul_X p j hp =>
    simp only [map_mul, aeval_X]
    exact mul_mem hp (G.charpolyCoeff_mem_virtualCharacterRing j)

/-- **The expectation of an integer polynomial in the coefficients `aᵢ` of the characteristic
polynomial is an integer**, on every Sato–Tate group. -/
lemma exists_expectation_aeval_eq_intCast :
    ∃ m : ℤ, G.expectation (fun g ↦ aeval (fun j ↦ G.charpolyCoeff j g) P) = m :=
  exists_integral_eq_intCast (G.aeval_charpolyCoeff_mem_virtualCharacterRing P)

/-- **The mixed moments `E[a₁^{e₁} ⋯ a_g^{e_g}]` of a Sato–Tate group are integers** (LMFDB
`st_group.moment_simplex`). -/
lemma exists_mixedMoment_eq_intCast (e : ℕ →₀ ℕ) : ∃ m : ℤ, G.mixedMoment e = m := by
  simpa only [aeval_monomial, map_one, one_mul, mixedMoment] using
    G.exists_expectation_aeval_eq_intCast (monomial e 1)

end SatoTateGroup
