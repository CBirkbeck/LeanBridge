import Mathlib.RingTheory.Invariant.Profinite

/-!
# Inertia groups under a quotient by a profinite group

Let a group `G` act on a ring `S` and a group `G'` on a ring `R ⊆ S`, compatibly along a surjection
`f : G → G'` whose kernel contains a subgroup `H` with `R = S^H`. Mathlib's
`Ideal.map_inertia_of_surjective` shows that `f` maps the inertia group of a prime `q` of `S` onto
that of the prime `q ∩ R`, when `H` is finite. The same holds when `H` is a profinite group acting
continuously on the discrete ring `S`, with the same proof: the two finite inputs, transitivity of
`H` on the primes over `q ∩ R` and surjectivity of the stabilizer onto the automorphisms of the
residue field, have profinite versions in Mathlib
(`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite` and
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`). The proofs below are those of
`Ideal.map_stabilizer_of_surjective` and `Ideal.map_inertia_of_surjective` with these inputs.

## Main results

* `Ideal.map_stabilizer_of_surjective_of_profinite`: `f` maps the decomposition group of `q`
  onto that of `q ∩ R`.
* `Ideal.map_inertia_of_surjective_of_profinite`: `f` maps the inertia group of `q` onto that of
  `q ∩ R`.
-/

open Algebra MulAction

open scoped Pointwise

namespace Ideal

universe u

variable {R S G' : Type*} {G : Type u} [CommRing R] [CommRing S] [Algebra R S] [Group G] [Group G']
  [MulSemiringAction G S] [MulSemiringAction G' R] (f : G →* G') (H : Subgroup G)

lemma smulCommClass_of_le_ker (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) : SMulCommClass H R S :=
  ⟨fun h x y ↦ by simp [Algebra.smul_def, H.smul_def, ← hf, f.mem_ker.mp (hf_ker h.2)]⟩

variable [TopologicalSpace H] [CompactSpace H] [TotallyDisconnectedSpace H] [IsTopologicalGroup H]
  [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul H S] [Algebra.IsInvariant R S H]
  (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsPrime]

/-- **A surjection with profinite kernel maps decomposition groups onto decomposition groups**:
the profinite version of `Ideal.map_stabilizer_of_surjective`, with the same proof. -/
lemma map_stabilizer_of_surjective_of_profinite (hf_surj : Function.Surjective f)
    (hf_ker : H ≤ f.ker) (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (stabilizer G q).map f = stabilizer G' p := by
  have : SMulCommClass H R S := smulCommClass_of_le_ker f H hf_ker hf
  replace hf_ker (h : H) : f h = 1 := hf_ker h.2
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩
    ext x
    rw [SetLike.mem_coe, mem_stabilizer_iff] at hg
    simp_rw [mem_pointwise_smul_iff_inv_smul_mem, over_def q p, mem_under, ← map_inv, hf,
      ← mem_pointwise_smul_iff_inv_smul_mem, hg]
  · intro g hg
    rcases hf_surj g with ⟨g, rfl⟩
    have h : (g • q).under R = q.under R := by
      ext x
      rw [mem_under, mem_pointwise_smul_iff_inv_smul_mem, ← hf, ← mem_under, ← over_def q p,
        map_inv, ← mem_pointwise_smul_iff_inv_smul_mem, hg]
    rcases IsInvariant.exists_smul_of_under_eq_of_profinite (G := H) (g • q) q h with ⟨g', hg'⟩
    exact ⟨g' * g, by simpa [mul_smul, eq_comm], by simp [hf_ker]⟩

/-- **A surjection with profinite kernel maps inertia groups onto inertia groups**: the profinite
version of `Ideal.map_inertia_of_surjective`, with the same proof. -/
lemma map_inertia_of_surjective_of_profinite (hf_surj : Function.Surjective f) (hf_ker : H ≤ f.ker)
    (hf : ∀ g x, algebraMap R S (f g • x) = g • algebraMap R S x) :
    (q.inertia G).map f = p.inertia G' := by
  have h_stab : stabilizer G' p ≤ (stabilizer G q).map f :=
    (map_stabilizer_of_surjective_of_profinite f H p q hf_surj hf_ker hf).ge
  have : SMulCommClass H R S := smulCommClass_of_le_ker f H hf_ker hf
  replace hf_ker (h : H) : f h = 1 := hf_ker h.2
  apply le_antisymm
  · rintro - ⟨g, hg, rfl⟩ x
    simpa [over_def q p, hf] using hg (algebraMap R S x)
  · intro g hg
    rcases h_stab (p.inertia_le_stabilizer hg) with ⟨g, hgq, rfl⟩
    let φ : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
      { __ := Quotient.stabilizerHom q (q.under ℤ) G ⟨g, hgq⟩
        commutes' x := by
          rcases Quotient.mk_surjective x with ⟨x, rfl⟩
          have hx : f g • x - x ∈ p.toAddSubgroup := hg x
          rw [Submodule.mem_toAddSubgroup, over_def q p, mem_under, map_sub, hf,
            ← Quotient.eq] at hx
          simpa }
    rcases Quotient.stabilizerHom_surjective_of_profinite (G := H) p q φ with ⟨g', hg'⟩
    let v : stabilizer G q := ⟨g', g'.2⟩⁻¹ * ⟨g, hgq⟩
    refine ⟨v, ?_, by simp [v, hf_ker]⟩
    rw [SetLike.mem_coe, coe_mem_inertia, ← Quotient.ker_stabilizerHom q (q.under ℤ) G,
      MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    rw [AlgEquiv.ext_iff] at hg' ⊢
    exact hg'

end Ideal
