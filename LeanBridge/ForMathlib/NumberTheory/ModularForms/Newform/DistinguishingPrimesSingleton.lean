import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.DistinguishingPrimes

/-!
# Hecke characteristic polynomials at a newform with a single Galois conjugate

That the Hecke operators `T_p` with `p ∤ N` distinguish the newforms of `S_k^{new}(N, χ)` (LMFDB
`cmf.distinguishing_primes`) is proved here only for the Galois orbits with a single element. For
such an orbit, the characteristic polynomial of `T_p` on `V_f` is `X - a_p(f)`, so it records the
eigenvalue itself and strong multiplicity one at fixed level applies.

In general, the characteristic polynomials record the multisets `{a_p(h) : h ∈ [f]}` one prime at a
time, and not which conjugate takes which value at which prime. Separating orbits from this data is
not strong multiplicity one for two newforms. It is strong multiplicity one for the isobaric sums of
the conjugates, on the traces of their Satake parameters, in the manner of Jacquet and Shalika (*On
Euler products and the classification of automorphic forms II*), and it rests on the nonvanishing
`L(1, h × conj h') ≠ 0` for `h ≠ h'` (Shahidi, *On certain `L`-functions*). Alternatively, it
follows from the Galois representations of Deligne and of Deligne–Serre, with the Chebotarev density
theorem and the Brauer–Nesbitt theorem. Neither that nonvanishing, nor these Galois representations,
nor the Brauer–Nesbitt theorem are in the pinned libraries or on the main branch of Tau Ceti (Tau
Ceti does have the Chebotarev density theorem), and the Rankin–Selberg statements of
`LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.CuspForm`, which exclude a pole at
`σ = 1` only for different nebentypes, do not exclude a zero there.

## Main results

* `HeckeRing.GL2.Newform.eq_of_galoisOrbit_eq_singleton_of_forall_heckeCharpoly_eq`: a newform with
  a single Galois conjugate is determined by its Hecke characteristic polynomials at the primes not
  dividing the level.
* `HeckeRing.GL2.Newform.distinguishesNewforms_of_forall_galoisOrbit_eq_singleton`: the primes not
  dividing the level distinguish the newforms of a space all of whose Galois orbits have a single
  element.
-/

open UpperHalfPlane Polynomial

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} {χ : (ZMod N)ˣ →* ℂˣ}

private lemma heckeCharpoly_eq_of_galoisOrbit_eq_singleton (hf : f.galoisOrbit = {f}) {p : ℕ}
    (hp : p.Prime) : f.heckeCharpoly hp = X - C ((qExpansion 1 f.toCuspForm).coeff p) := by
  have hS : f.finite_galoisOrbit.toFinset = {f} := Finset.ext fun h ↦ by
    rw [f.finite_galoisOrbit.mem_toFinset, hf, Set.mem_singleton_iff, Finset.mem_singleton]
  rw [heckeCharpoly_eq_prod, hS, Finset.prod_singleton]

/-- **A newform with a single Galois conjugate is determined by its Hecke characteristic
polynomials**: if the Galois orbit of `f` is `{f}`, and `g` has the nebentypus of `f` and the Hecke
characteristic polynomials of `f` at every prime not dividing the level, then `g = f`. -/
lemma eq_of_galoisOrbit_eq_singleton_of_forall_heckeCharpoly_eq (hf : f.galoisOrbit = {f})
    (hχ : f.χ = g.χ)
    (h : ∀ (p : ℕ) (hp : p.Prime), ¬p ∣ N → f.heckeCharpoly hp = g.heckeCharpoly hp) : f = g := by
  rcases Nat.exists_infinite_primes (N + 1) with ⟨p₀, hp₀', hp₀⟩
  have hp₀N : ¬p₀ ∣ N := Nat.not_dvd_of_pos_of_lt (NeZero.pos N) (by omega)
  have hcard : g.finite_galoisOrbit.toFinset.card ≤ 1 := by
    have hdeg : (f.heckeCharpoly hp₀).natDegree = (g.heckeCharpoly hp₀).natDegree :=
      congrArg natDegree (h p₀ hp₀ hp₀N)
    rw [heckeCharpoly_eq_of_galoisOrbit_eq_singleton hf, heckeCharpoly_eq_prod, natDegree_X_sub_C,
      natDegree_finsetProd_X_sub_C_eq_card] at hdeg
    exact hdeg.symm.le
  have hg : g.galoisOrbit = {g} := Set.eq_singleton_iff_unique_mem.mpr
    ⟨g.self_mem_galoisOrbit, fun a ha ↦ Finset.card_le_one.mp hcard a
      (g.finite_galoisOrbit.mem_toFinset.mpr ha) g
      (g.finite_galoisOrbit.mem_toFinset.mpr g.self_mem_galoisOrbit)⟩
  refine eq_of_forall_prime_eigenvalue_eq hχ fun p hp hpN ↦ ?_
  have hfg : (qExpansion 1 f.toCuspForm).coeff p = (qExpansion 1 g.toCuspForm).coeff p :=
    C_injective <| sub_right_inj.mp <| by
      rw [← heckeCharpoly_eq_of_galoisOrbit_eq_singleton hf hp,
        ← heckeCharpoly_eq_of_galoisOrbit_eq_singleton hg hp]
      exact h p hp <| hp.coprime_iff_not_dvd.mp hpN
  rw [← f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN,
    ← g.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ hpN]
  exact hfg

/-- **The primes not dividing the level distinguish the newforms of a space all of whose Galois
orbits have a single element** (LMFDB `cmf.distinguishing_primes`). -/
lemma distinguishesNewforms_of_forall_galoisOrbit_eq_singleton
    (h : ∀ f : Newform N k, f.χ = χ → f.galoisOrbit = {f}) :
    DistinguishesNewforms N k χ {p | ¬(p : ℕ) ∣ N} := fun f g hf hg hfg ↦ by
  rw [eq_of_galoisOrbit_eq_singleton_of_forall_heckeCharpoly_eq (h f hf) (hf.trans hg.symm)
    fun p hp hpN ↦ hfg ⟨p, hp⟩ hpN]
  exact IsGaloisConjugate.refl g

end HeckeRing.GL2.Newform
