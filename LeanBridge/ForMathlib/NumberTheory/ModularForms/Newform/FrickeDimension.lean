import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.AtkinLehnerDimension

/-!
# The dimensions of the plus and minus subspaces

For a space of modular forms of trivial character, the LMFDB displays its dimension as the sum of
the dimensions of its plus and minus subspaces (LMFDB `cmf.display_dim`), the eigenspaces of the
Fricke involution `w_N` with eigenvalues `1` and `-1` (LMFDB `cmf.plus_space`, `cmf.minus_space`).
The normalized Fricke operator of Tau Ceti, the normalized Atkin–Lehner operator `𝒲_Q` at `Q = N`,
is an involution of `S_k(Γ₀(N))`, which is therefore the direct sum of its `±1` eigenspaces (Tau
Ceti's `TauCeti.Nat.IsExactDivisor.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp`), so its
dimension is the sum of theirs.

The spaces whose dimensions the LMFDB's tables show are the newspaces `S_k^new(N, χ)`, for trivial
`χ` the new subspace `S_k^new(Γ₀(N))` of `S_k(Γ₀(N))` (`TauCeti.cuspFormsNewGamma0`). The operator
`𝒲_Q` maps it to itself (Tau Ceti's
`TauCeti.Nat.IsExactDivisor.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew`), so the
newspace is the direct sum of its intersections with the two eigenspaces,
`f = (f + 𝒲_Q f) / 2 + (f - 𝒲_Q f) / 2`, and its dimension is again the sum of theirs. Both
statements hold for every exact divisor `Q ∥ N`; the Fricke involution is the case `Q = N`.

## Main results

* `TauCeti.Nat.IsExactDivisor.finrank_eigenspace_add_finrank_eigenspace` (LMFDB `cmf.display_dim`):
  the dimension of `S_k(Γ₀(N))` is the sum of the dimensions of its plus and minus subspaces.
* `TauCeti.Nat.IsExactDivisor.finrank_inf_eigenspace_add_finrank_inf_eigenspace` (LMFDB
  `cmf.display_dim`): the dimension of `S_k^new(Γ₀(N))` is the sum of the dimensions of its plus
  and minus subspaces.
-/

open CongruenceSubgroup Matrix SpecialLinearGroup Module TauCeti

open scoped ExactDivisor

namespace TauCeti.Nat.IsExactDivisor

variable {N Q : ℕ} [NeZero N] (h : Q ∥ N) (k : ℤ)

/-- **The dimension of `S_k(Γ₀(N))` is the sum of the dimensions of its plus and minus subspaces**
(LMFDB `cmf.display_dim`), the eigenspaces of the normalized Atkin–Lehner involution `𝒲_Q` with
eigenvalues `1` and `-1`, which are complementary; for `Q = N` these are the plus and minus
subspaces of the Fricke involution (LMFDB `cmf.plus_space`, `cmf.minus_space`). -/
lemma finrank_eigenspace_add_finrank_eigenspace :
    finrank ℂ (End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) 1) +
      finrank ℂ (End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) (-1)) =
    finrank ℂ (CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  Submodule.finrank_add_eq_of_isCompl (h.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp k)

/-- **The dimension of the newspace `S_k^new(Γ₀(N))` is the sum of the dimensions of its plus and
minus subspaces** (LMFDB `cmf.display_dim`), its intersections with the eigenspaces of `𝒲_Q` with
eigenvalues `1` and `-1`: as `𝒲_Q` is an involution that preserves the newspace, every newform `f`
of trivial character is `(f + 𝒲_Q f) / 2 + (f - 𝒲_Q f) / 2`. For `Q = N` these are the plus and
minus subspaces of the Fricke involution, whose dimensions the LMFDB shows for the newspaces of
trivial character. -/
lemma finrank_inf_eigenspace_add_finrank_inf_eigenspace :
    finrank ℂ ↥(cuspFormsNewGamma0 N k ⊓ End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) 1) +
      finrank ℂ ↥(cuspFormsNewGamma0 N k ⊓
        End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) (-1)) =
    finrank ℂ (cuspFormsNewGamma0 N k) := by
  have hbot : (cuspFormsNewGamma0 N k ⊓ End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) 1) ⊓
      (cuspFormsNewGamma0 N k ⊓ End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) (-1)) = ⊥ :=
    eq_bot_iff.mpr <| (inf_le_inf inf_le_right inf_le_right).trans
      (h.isCompl_eigenspace_normalizedAtkinLehnerOperatorCusp k).inf_eq_bot.le
  have hsup : (cuspFormsNewGamma0 N k ⊓ End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) 1) ⊔
      (cuspFormsNewGamma0 N k ⊓ End.eigenspace (h.normalizedAtkinLehnerOperatorCusp k) (-1)) =
      cuspFormsNewGamma0 N k := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun f hf ↦ ?_
    have hWf : h.normalizedAtkinLehnerOperatorCusp k f ∈ cuspFormsNewGamma0 N k :=
      h.restrict_normalizedAtkinLehnerOperatorCusp_mem_cuspFormsNew hf
    have hWW :
        h.normalizedAtkinLehnerOperatorCusp k (h.normalizedAtkinLehnerOperatorCusp k f) = f :=
      h.normalizedAtkinLehnerOperatorCusp_involutive k f
    refine Submodule.mem_sup.mpr ⟨(2 : ℂ)⁻¹ • (f + h.normalizedAtkinLehnerOperatorCusp k f),
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hf hWf), ?_⟩,
      (2 : ℂ)⁻¹ • (f - h.normalizedAtkinLehnerOperatorCusp k f),
      Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hf hWf), ?_⟩, ?_⟩
    · rw [End.mem_eigenspace_iff, map_smul, map_add, hWW, add_comm _ f, one_smul]
    · rw [End.mem_eigenspace_iff, map_smul, map_sub, hWW, neg_one_smul, ← smul_neg, neg_sub]
    · rw [← smul_add, add_add_sub_cancel, ← two_smul ℂ f, smul_smul, inv_mul_cancel₀ two_ne_zero,
        one_smul]
  rw [← Submodule.finrank_sup_add_finrank_inf_eq, hsup, hbot, finrank_bot, add_zero]

end TauCeti.Nat.IsExactDivisor
