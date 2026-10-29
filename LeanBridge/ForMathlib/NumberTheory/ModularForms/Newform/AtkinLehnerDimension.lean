import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Sign

/-!
# Dimensions of the Atkin–Lehner subspaces of a newspace

Let `N` be a level and `k` a weight. For every prime `p ∣ N`, the normalized Atkin–Lehner operator
`𝒲_{p^{v_p(N)}}` (Tau Ceti's `TauCeti.Nat.IsExactDivisor.normalizedAtkinLehnerOperatorCusp`) is an
involution of `S_k(Γ₀(N))` that preserves its new subspace `S_k^new(Γ₀(N))`, and it scales every
newform of trivial character by its Atkin–Lehner sign `±1`
(`HeckeRing.GL2.Newform.atkinLehnerSign`). For a vector `ε = (ε_p)_{p ∣ N}` of signs, the
**Atkin–Lehner subspace** `S_k^new(Γ₀(N))^ε` is the subspace of the newspace on which each
`𝒲_{p^{v_p(N)}}` acts by `ε_p`, and the LMFDB shows its dimension for each of the `2 ^ j` sign
vectors, where `j` is the number of primes dividing `N`, ordered lexicographically with `1` before
`-1` (LMFDB `cmf.atkin_lehner_dims`). As these operators are commuting involutions, the newspace
is the direct sum of the Atkin–Lehner subspaces, whose dimensions therefore add up to that of the
newspace. The knowl writes `S_k^new(Γ₀(N), χ)`, but for a nontrivial character `χ` the
Atkin–Lehner operators need not preserve the space of character `χ` and need not square to `1`:
the signs `±1` of the knowl are those of newforms of trivial character, on whose space
`S_k(Γ₀(N))` the LMFDB defines the operators (LMFDB `cmf.atkin-lehner`), the case formalised here.

## Main definitions

* `TauCeti.cuspFormsNewGamma0`: the new subspace `S_k^new(Γ₀(N))` of `S_k(Γ₀(N))`.
* `TauCeti.atkinLehnerSubspace` (LMFDB `cmf.atkin_lehner_dims`): the Atkin–Lehner subspace
  `S_k^new(Γ₀(N))^ε` for a sign vector `ε`.
* `TauCeti.atkinLehnerDim` (LMFDB `cmf.atkin_lehner_dims`): its dimension.
* `TauCeti.atkinLehnerDims` (LMFDB `cmf.atkin_lehner_dims`): the list of these dimensions in the
  LMFDB's order.
* `HeckeRing.GL2.Newform.atkinLehnerSignVector`: the vector of Atkin–Lehner signs of a newform of
  trivial character.

## Main results

* `TauCeti.iSupIndep_atkinLehnerSubspace`: the Atkin–Lehner subspaces are independent.
* `TauCeti.iSup_atkinLehnerSubspace`: they span the newspace.
* `TauCeti.sum_atkinLehnerDim`: their dimensions add up to the dimension of the newspace.
* `HeckeRing.GL2.Newform.toCuspFormGamma0_mem_atkinLehnerSubspace`: a newform of trivial
  character lies in the Atkin–Lehner subspace of its sign vector.
-/

open CongruenceSubgroup Matrix SpecialLinearGroup Module TauCeti

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {g : Module.End K V} {μ : K}

lemma eigenspace_eq_bot_of_mul_self_eq_one (hg : g * g = 1) (hμ₁ : μ ≠ 1) (hμ₂ : μ ≠ -1) :
    g.eigenspace μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_eigenspace_iff] at hv
  have h : (μ ^ 2 - 1) • v = 0 := by
    have hv' : g (g v) = v := by
      rw [← mul_apply, hg, one_apply]
    rw [hv, map_smul, hv, smul_smul] at hv'
    rw [sub_smul, one_smul, sq, hv', sub_self]
  have hμ : μ ^ 2 - 1 ≠ 0 := by
    intro h0
    have h' : (μ - 1) * (μ + 1) = 0 := by
      linear_combination h0
    rcases mul_eq_zero.mp h' with h₁ | h₁
    · exact hμ₁ (sub_eq_zero.mp h₁)
    · exact hμ₂ (eq_neg_of_add_eq_zero_left h₁)
  exact (smul_eq_zero.mp h).resolve_left hμ

variable [NeZero (2 : K)] in
lemma maxGenEigenspace_eq_eigenspace_of_mul_self_eq_one (hg : g * g = 1) :
    g.maxGenEigenspace μ = g.eigenspace μ := by
  have hss : g.IsSemisimple := by
    refine isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ 2 - 1) ?_ ?_
    · have h : Squarefree (Polynomial.X ^ 2 - Polynomial.C (1 : K)) :=
        (Polynomial.separable_X_pow_sub_C (1 : K) (by exact_mod_cast two_ne_zero)
          one_ne_zero).squarefree
      rwa [map_one] at h
    · simp [sq, hg]
  exact hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

end Module.End

namespace TauCeti

lemma commute_normalizedAtkinLehnerOperatorCusp_primePow {N : ℕ} {k : ℤ} (p q : N.primeFactors) :
    Commute ((Nat.isExactDivisor_primePow (N := N) (p := p.1)).normalizedAtkinLehnerOperatorCusp k)
      ((Nat.isExactDivisor_primePow (N := N) (p := q.1)).normalizedAtkinLehnerOperatorCusp k) :=
  LinearMap.ext fun f ↦ by
    rw [End.mul_apply, End.mul_apply]
    exact Nat.isExactDivisor_primePow.normalizedAtkinLehnerOperatorCusp_comm _ k f

variable (N : ℕ) [NeZero N] (k : ℤ) (ε : N.primeFactors → ℤˣ)

/-- The **new subspace** `S_k^new(Γ₀(N))` of the cusp forms of weight `k` on `Γ₀(N)`, that is of
trivial character (LMFDB `cmf.newspace`): the cusp forms whose restriction to `Γ₁(N)` lies in the
new subspace `S_k(Γ₁(N))^new` (`TauCeti.cuspFormsNew`). -/
noncomputable def cuspFormsNewGamma0 : Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  (cuspFormsNew N k).comap (CuspForm.restrictₗ k ℂ (Gamma1_map_le_Gamma0_map N))

/-- The **Atkin–Lehner subspace** `S_k^new(Γ₀(N))^ε` (LMFDB `cmf.atkin_lehner_dims`) for a sign
vector `ε = (ε_p)_{p ∣ N}`, with `ε_p ∈ ℤˣ = {1, -1}`: the subspace of the new subspace
`S_k^new(Γ₀(N))` on which, for every prime `p ∣ N`, the normalized Atkin–Lehner operator
`𝒲_{p^{v_p(N)}}` acts as the scalar `ε_p`. -/
noncomputable def atkinLehnerSubspace : Submodule ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  cuspFormsNewGamma0 N k ⊓ ⨅ p : N.primeFactors, End.eigenspace
    ((Nat.isExactDivisor_primePow (p := p.1)).normalizedAtkinLehnerOperatorCusp k) ((ε p : ℤ) : ℂ)

/-- The **dimension** of the Atkin–Lehner subspace `S_k^new(Γ₀(N))^ε` (LMFDB
`cmf.atkin_lehner_dims`). As the newforms of trivial character form a basis of the newspace, it is
the number of newforms of level `N`, weight `k` and trivial character with Atkin–Lehner signs `ε`,
which is not proved here. -/
noncomputable def atkinLehnerDim : ℕ :=
  Module.finrank ℂ (atkinLehnerSubspace N k ε)

/-- The `i`-th sign vector in the LMFDB's lexicographic order on the `2 ^ j` vectors
`(ε_{p_1}, …, ε_{p_j})` of signs at the primes `p_1 < ⋯ < p_j` dividing `N`, with `1` before `-1`,
counting from `i = 0`: `ε_{p_m} = -1` exactly when the binary digit of `i` of weight `2 ^ (j - m)`
is `1`. -/
noncomputable def atkinLehnerLexSignVector (i : ℕ) : N.primeFactors → ℤˣ := fun p ↦
  if i.testBit (N.primeFactors.card - 1 - (N.primeFactors.sort (· ≤ ·)).idxOf p.1) then -1 else 1

/-- The **dimensions of the Atkin–Lehner subspaces** (LMFDB `cmf.atkin_lehner_dims`) as the LMFDB
lists them: the dimensions `dim S_k^new(Γ₀(N))^ε` for the `2 ^ j` sign vectors `ε`, where `j` is
the number of primes dividing `N`, ordered lexicographically with `1` before `-1`
(`atkinLehnerLexSignVector`). -/
noncomputable def atkinLehnerDims : List ℕ :=
  (List.range (2 ^ N.primeFactors.card)).map fun i ↦
    atkinLehnerDim N k (atkinLehnerLexSignVector N i)

variable {N k} in
lemma atkinLehnerSubspace_le_cuspFormsNewGamma0 :
    atkinLehnerSubspace N k ε ≤ cuspFormsNewGamma0 N k :=
  inf_le_left

/-- **The Atkin–Lehner subspaces are independent**: they lie in the simultaneous generalised
eigenspaces of the commuting operators `𝒲_{p^{v_p(N)}}`, which are independent. -/
lemma iSupIndep_atkinLehnerSubspace : iSupIndep (atkinLehnerSubspace N k) := by
  refine ((End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun p : N.primeFactors ↦
    (Nat.isExactDivisor_primePow (N := N) (p := p.1)).normalizedAtkinLehnerOperatorCusp k)
    fun i j φ ↦ End.mapsTo_maxGenEigenspace_of_comm
      (commute_normalizedAtkinLehnerOperatorCusp_primePow j i) φ).comp
    (f := fun (ε : N.primeFactors → ℤˣ) p ↦ ((ε p : ℤ) : ℂ)) ?_).mono fun ε ↦ ?_
  · intro ε ε' h
    funext p
    exact Units.ext (Int.cast_injective (congrFun h p))
  · exact inf_le_right.trans (iInf_mono fun p ↦ End.eigenspace_le_maxGenEigenspace)

/-- **The Atkin–Lehner subspaces span the newspace**: the restrictions of the operators
`𝒲_{p^{v_p(N)}}` to the finite-dimensional newspace commute, so that it is the sum of their
simultaneous generalised eigenspaces, and these are eigenspaces with eigenvalues `±1`, as the
operators are involutions. -/
lemma iSup_atkinLehnerSubspace : ⨆ ε, atkinLehnerSubspace N k ε = cuspFormsNewGamma0 N k := by
  refine le_antisymm (iSup_le fun ε ↦ inf_le_left) ?_
  have hV (p : N.primeFactors) (x : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
      (hx : x ∈ cuspFormsNewGamma0 N k) :
      (Nat.isExactDivisor_primePow (N := N) (p := p.1)).normalizedAtkinLehnerOperatorCusp k x ∈
        cuspFormsNewGamma0 N k :=
    Nat.isExactDivisor_primePow.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew hx
  let g : N.primeFactors → Module.End ℂ (cuspFormsNewGamma0 N k) := fun p ↦
    ((Nat.isExactDivisor_primePow (N := N) (p := p.1)).normalizedAtkinLehnerOperatorCusp k).restrict
      (hV p)
  have hg (p : N.primeFactors) : g p * g p = 1 := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rw [End.mul_apply, End.one_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
    have hQ : Nat.IsExactDivisor (p.1 ^ N.factorization p.1) N :=
      Nat.isExactDivisor_primePow
    exact hQ.normalizedAtkinLehnerOperatorCusp_involutive k x.1
  have hcomm : Pairwise fun p q ↦ Commute (g p) (g q) := by
    intro p q _
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    rw [End.mul_apply, End.mul_apply, LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply,
      LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
    exact Nat.isExactDivisor_primePow.normalizedAtkinLehnerOperatorCusp_comm _ k x.1
  have htop : ⨆ χ : N.primeFactors → ℂ, ⨅ p, (g p).maxGenEigenspace (χ p) = ⊤ :=
    End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute g hcomm
      fun p ↦ End.iSup_maxGenEigenspace_eq_top (g p)
  rw [← Submodule.map_subtype_top (cuspFormsNewGamma0 N k), ← htop, Submodule.map_iSup]
  refine iSup_le fun χ ↦ ?_
  simp_rw [End.maxGenEigenspace_eq_eigenspace_of_mul_self_eq_one (hg _)]
  by_cases hχ : ∀ p, χ p = 1 ∨ χ p = -1
  · let ε : N.primeFactors → ℤˣ := fun p ↦ if χ p = 1 then 1 else -1
    have hε (p : N.primeFactors) : ((ε p : ℤ) : ℂ) = χ p := by
      rcases hχ p with h | h <;> norm_num [ε, h]
    refine le_iSup_of_le ε ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.mem_inf.mpr ⟨v.2, (Submodule.mem_iInf _).mpr fun p ↦ ?_⟩
    have hvp : g p v = χ p • v :=
      End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv p)
    rw [End.mem_eigenspace_iff, hε]
    exact congrArg Subtype.val hvp
  rcases not_forall.mp hχ with ⟨p, hp⟩
  rcases not_or.mp hp with ⟨hp₁, hp₂⟩
  rw [eq_bot_iff.mpr ((iInf_le _ p).trans
    (End.eigenspace_eq_bot_of_mul_self_eq_one (hg p) hp₁ hp₂).le), Submodule.map_bot]
  exact bot_le

/-- **The Atkin–Lehner dimensions add up to the dimension of the newspace**
`S_k^new(Γ₀(N))`, the newspace being the direct sum of the Atkin–Lehner subspaces. -/
lemma sum_atkinLehnerDim :
    ∑ ε, atkinLehnerDim N k ε = Module.finrank ℂ (cuspFormsNewGamma0 N k) := by
  classical
  rw [← iSup_atkinLehnerSubspace, Submodule.iSup_eq_range_dfinsupp_lsum,
    LinearMap.finrank_range_of_inj (iSupIndep_atkinLehnerSubspace N k).dfinsupp_lsum_injective]
  exact (Module.finrank_directSum ℂ fun ε ↦ atkinLehnerSubspace N k ε).symm

end TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (hχ : f.χ = 1)

/-- The **Atkin–Lehner sign vector** `(ε_p(f))_{p ∣ N}` of a newform `f` of trivial character: its
Atkin–Lehner signs `ε_{p^{v_p(N)}}(f) = ±1` (`HeckeRing.GL2.Newform.atkinLehnerSign`) at the
primes `p` dividing `N`. -/
noncomputable def atkinLehnerSignVector : N.primeFactors → ℤˣ := fun p ↦
  if f.atkinLehnerSign hχ (Nat.isExactDivisor_primePow (p := p.1)) = 1 then 1 else -1

lemma coe_atkinLehnerSignVector (p : N.primeFactors) : ((f.atkinLehnerSignVector hχ p : ℤ) : ℂ) =
    f.atkinLehnerSign hχ (Nat.isExactDivisor_primePow (p := p.1)) := by
  rcases f.atkinLehnerSign_eq_one_or_neg_one hχ (Nat.isExactDivisor_primePow (p := p.1)) with
    h | h <;> norm_num [atkinLehnerSignVector, h]

/-- **A newform of trivial character lies in the Atkin–Lehner subspace of its sign vector.** -/
lemma toCuspFormGamma0_mem_atkinLehnerSubspace :
    f.toCuspFormGamma0 hχ ∈ atkinLehnerSubspace N k (f.atkinLehnerSignVector hχ) := by
  refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun p ↦ ?_⟩
  · rw [cuspFormsNewGamma0, Submodule.mem_comap, CuspForm.restrictₗ_apply,
      restrict_toCuspFormGamma0]
    exact f.isNew
  · rw [End.mem_eigenspace_iff,
      normalizedAtkinLehnerOperatorCusp_toCuspFormGamma0_eq_atkinLehnerSign_smul,
      coe_atkinLehnerSignVector]

end HeckeRing.GL2.Newform
