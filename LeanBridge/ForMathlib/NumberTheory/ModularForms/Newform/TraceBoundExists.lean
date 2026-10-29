import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.TraceBound
import Mathlib.RingTheory.Trace.Basic

/-!
# The trace bound exists if Galois conjugates of newforms are newforms

In weight `k ≥ 2`, assume that every Galois conjugate `σ(f)` of a newform `f` of level `N` and
weight `k` is again a newform of level `N` and weight `k`. This is a theorem (Shimura), which is not
proved in LeanBridge: it needs a `ℚ`-structure on `S_k(Γ₁(N))` stable under the Hecke operators,
such as a basis with rational Fourier coefficients, or the Eichler–Shimura isomorphism at level `N`.
Under that assumption, the trace `Tr_{ℚ(f)/ℚ}(aₙ)` is the sum of the `aₙ` over the Galois orbit of
`f`, and since newforms are linearly independent, the traces of all the coefficients distinguish
the Galois orbits. There are finitely many newforms, so the traces of the first `m` coefficients do
for some `m`, and the trace bound (LMFDB `cmf.trace_bound`) is the least such `m`.

## Main results

* `HeckeRing.GL2.Newform.coeffTrace_eq_sum`: `Tr(aₙ(f))` is the sum of `aₙ` over the Galois orbit.
* `HeckeRing.GL2.Newform.isGaloisConjugate_of_coeffTrace_eq`: newforms whose coefficients have the
  same traces are Galois conjugate.
* `HeckeRing.GL2.Newform.exists_tracesDistinguishNewforms`: the traces of finitely many
  coefficients distinguish the Galois orbits, so that the trace bound is positive and has its
  defining property.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix SpecialLinearGroup

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The trace of a coefficient is its sum over the Galois orbit**: in weight at least two, if
every Galois conjugate of a newform of level `N` and weight `k` is a newform, then
`Tr_{ℚ(f)/ℚ}(aₙ(f)) = ∑_{g ∈ [f]} aₙ(g)`. -/
lemma coeffTrace_eq_sum (hk : 2 ≤ k)
    (hS : ∀ (g : Newform N k) (σ : Gal(ℂ/ℚ)), ∃ g' : Newform N k, g.IsGaloisConjugateBy σ g')
    (f : Newform N k) (n : ℕ) : (f.coeffTrace n : ℂ) =
      ∑ g ∈ f.finite_galoisOrbit.toFinset, (qExpansion 1 g.toCuspForm).coeff n := by
  have : NumberField (CoefficientField f) := numberField_CoefficientField f hk
  rw [← eq_ratCast (algebraMap ℚ ℂ), coeffTrace, trace_eq_sum_embeddings]
  symm
  refine Finset.sum_bij (fun g hg ↦ f.galoisOrbitEmbedding ⟨g, by simpa using hg⟩)
    (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro g _ g' _ h
    simpa using f.galoisOrbitEmbedding_injective h
  · intro ι _
    rcases galoisOrbitEmbedding_surjective (hS f) ι with ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, by simpa using hg, rfl⟩
  · intro g hg
    exact (isEmbedding_galoisOrbitEmbedding ⟨g, by simpa using hg⟩).coeff n

/-- **The traces of the coefficients distinguish the Galois orbits**: in weight at least two, if
every Galois conjugate of a newform of level `N` and weight `k` is a newform, then newforms `f` and
`g` with `Tr(aₙ(f)) = Tr(aₙ(g))` for all `n ≥ 1` are Galois conjugate. Otherwise the sums of their
Galois orbits would have the same `q`-expansion, against the linear independence of newforms. -/
lemma isGaloisConjugate_of_coeffTrace_eq (hk : 2 ≤ k)
    (hS : ∀ (g : Newform N k) (σ : Gal(ℂ/ℚ)), ∃ g' : Newform N k, g.IsGaloisConjugateBy σ g')
    {f g : Newform N k} (h : ∀ n, 0 < n → f.coeffTrace n = g.coeffTrace n) :
    f.IsGaloisConjugate g := by
  classical
  have : Fintype (Newform N k) := Fintype.ofFinite _
  let L : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] PowerSeries ℂ :=
    { toFun x := qExpansion 1 x
      map_add' x y := ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map N) x y
      map_smul' a x :=
        ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N) a x }
  have hL : LinearIndependent ℂ fun x : Newform N k ↦ L x.toCuspForm :=
    linearIndependent_toCuspForm.map' L <| LinearMap.ker_eq_bot.mpr <|
      CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N)
  by_contra hfg
  have hc : ((if f ∈ f.finite_galoisOrbit.toFinset then 1 else 0) -
      if f ∈ g.finite_galoisOrbit.toFinset then 1 else 0 : ℂ) = 0 :=
    Fintype.linearIndependent_iff.mp hL (fun x ↦
      (if x ∈ f.finite_galoisOrbit.toFinset then 1 else 0) -
        if x ∈ g.finite_galoisOrbit.toFinset then 1 else 0) ?_ f
  · simp [mem_galoisOrbit, isGaloisConjugate_comm, hfg, IsGaloisConjugate.refl] at hc
  · refine PowerSeries.ext fun n ↦ ?_
    simp only [sub_smul, ite_smul, one_smul, zero_smul, Finset.sum_sub_distrib,
      Finset.sum_ite_mem, Finset.univ_inter, map_sub, map_sum, map_zero]
    rcases n with _ | n
    · simp [L, CuspFormClass.qExpansion_coeff_zero _ one_pos (one_mem_strictPeriods_Gamma1_map N)]
    · rw [sub_eq_zero]
      exact (coeffTrace_eq_sum hk hS f _).symm.trans <| by
        rw [h _ n.succ_pos, coeffTrace_eq_sum hk hS g]
        rfl

/-- **The trace bound exists**: in weight at least two, if every Galois conjugate of a newform of
level `N` and weight `k` is a newform, then the traces of the first `m` coefficients distinguish the
Galois orbits of newforms of nebentypus `χ` for some `m ≥ 1`. So `traceBound N k χ` is then the
least such `m`, and not the junk value `0`. -/
lemma exists_tracesDistinguishNewforms (hk : 2 ≤ k)
    (hS : ∀ (g : Newform N k) (σ : Gal(ℂ/ℚ)), ∃ g' : Newform N k, g.IsGaloisConjugateBy σ g')
    (χ : (ZMod N)ˣ →* ℂˣ) : ∃ m, 0 < m ∧ TracesDistinguishNewforms N k χ m := by
  have : Fintype (Newform N k) := Fintype.ofFinite _
  have hn : ∀ p : Newform N k × Newform N k,
      ∃ n, 0 < n ∧ (p.1.IsGaloisConjugate p.2 ∨ p.1.coeffTrace n ≠ p.2.coeffTrace n) := by
    intro p
    by_cases hp : p.1.IsGaloisConjugate p.2
    · exact ⟨1, one_pos, .inl hp⟩
    · have hne : ¬∀ n, 0 < n → p.1.coeffTrace n = p.2.coeffTrace n :=
        fun H ↦ hp <| isGaloisConjugate_of_coeffTrace_eq hk hS H
      push Not at hne
      rcases hne with ⟨n, hn, hne⟩
      exact ⟨n, hn, .inr hne⟩
  choose F hF0 hF using hn
  refine ⟨Finset.univ.sup F + 1, Nat.succ_pos _, fun f g _ _ hfg ↦ ?_⟩
  rcases hF (f, g) with h | h
  · exact h
  · exact absurd (hfg _ ⟨hF0 (f, g), (Finset.le_sup (Finset.mem_univ (f, g))).trans
      (Nat.le_succ _)⟩) h

end HeckeRing.GL2.Newform
