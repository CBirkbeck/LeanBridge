import Mathlib.Algebra.Module.Lattice
import Mathlib.Tactic.LinearCombination
import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.WeakEquivalence

/-!
# Weakly equivalent fractional ideals have the same multiplier ring

Let `R` be an order in an étale `ℚ`-algebra `K`, a subring whose additive group is finitely
generated and spans `K` over `ℚ` (`Submodule.IsLattice`). The multiplier ring of a fractional
`R`-ideal `I` is `(I : I) = {x ∈ K | xI ⊆ I}`. If `I` and `J` are weakly equivalent, their
localisations `I_𝔭` and `J_𝔭` being isomorphic `R_𝔭`-modules at every maximal ideal `𝔭`
(`FractionalIdeal.WeaklyEquivalent`), then `(I : I) = (J : J)` (LMFDB `av.weak_equivalence_class`).

The proof is local. Let `x ∈ (I : I)` and `y ∈ J`. At a maximal ideal `𝔭`, an isomorphism
`φ : I_𝔭 ≃ J_𝔭` sends some `i / 1` to `t y / 1`, with `t ∉ 𝔭`. Some multiple `n x`, `n` a positive
integer, lies in `R`, and `n (x i) = (n x) i`, so `n φ(x i / 1) = (n x) t y / 1`; writing
`φ(x i / 1)` as `j / u` and cancelling the unit `n` of `K` gives `s (x y) ∈ J` for some `s ∉ 𝔭`.
As this holds at every maximal ideal, `x y ∈ J`. Nothing else about `K` is used: the result holds
for an order in any `ℚ`-algebra, and for any `R`-submodules `I` and `J` of `K`.

## Main results

* `FractionalIdeal.WeaklyEquivalent.div_self_eq` (LMFDB `av.weak_equivalence_class`): weakly
  equivalent fractional ideals of an order have the same multiplier ring.
-/

open Submodule

variable {K : Type*} [CommRing K] {R : Subalgebra ℤ K}

namespace Subalgebra

variable [Algebra ℚ K]

lemma exists_natCast_mul_mem_of_span_eq_top (hR : span ℚ (R : Set K) = ⊤) (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K) * x ∈ R := by
  have hx : x ∈ span ℚ (R : Set K) := hR ▸ mem_top
  induction hx using span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [Nat.cast_one, one_mul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    rcases hy with ⟨a, ha, hay⟩
    rcases hz with ⟨b, hb, hbz⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : ((a * b : ℕ) : K) * (y + z) = (b : K) * (a * y) + (a : K) * (b * z) := by
      push_cast
      ring1
    rw [h]
    exact R.add_mem (R.mul_mem (R.natCast_mem b) hay) (R.mul_mem (R.natCast_mem a) hbz)
  | smul q y _ hy =>
    rcases hy with ⟨a, ha, hay⟩
    refine ⟨q.den * a, mul_ne_zero q.den_nz ha, ?_⟩
    have hq : (q.den : K) * algebraMap ℚ K q = q.num := by
      rw [← map_natCast (algebraMap ℚ K), ← map_mul, mul_comm, Rat.mul_den_eq_num, map_intCast]
    have h : ((q.den * a : ℕ) : K) * (q • y) = ((q.den : K) * algebraMap ℚ K q) * (a * y) := by
      rw [Algebra.smul_def]
      push_cast
      ring1
    rw [h, hq]
    exact R.mul_mem (R.intCast_mem q.num) hay

end Subalgebra

namespace FractionalIdeal

variable {S : Submonoid R} {I J : FractionalIdeal S K}

lemma exists_mem_primeCompl_mul_mem {𝔭 : Ideal R} [𝔭.IsPrime]
    (φ : LocalizedModule 𝔭.primeCompl (I : Submodule R K) ≃ₗ[Localization.AtPrime 𝔭]
      LocalizedModule 𝔭.primeCompl (J : Submodule R K))
    {x : K} (hx : ∀ i ∈ I, x * i ∈ I) {n : ℕ} (hn : IsUnit (n : K)) (hnx : (n : K) * x ∈ R)
    {y : K} (hy : y ∈ J) : ∃ s ∈ 𝔭.primeCompl, (s : K) * (x * y) ∈ J := by
  rcases IsLocalizedModule.surj 𝔭.primeCompl
    (LocalizedModule.mkLinearMap 𝔭.primeCompl (I : Submodule R K))
    (φ.symm (LocalizedModule.mk ⟨y, hy⟩ 1)) with ⟨⟨i, t⟩, hit⟩
  rcases IsLocalizedModule.surj 𝔭.primeCompl
    (LocalizedModule.mkLinearMap 𝔭.primeCompl (J : Submodule R K))
    (φ (LocalizedModule.mk ⟨x * i, hx i i.2⟩ 1)) with ⟨⟨j, u⟩, hju⟩
  have hφ (r : R) (z : LocalizedModule 𝔭.primeCompl (I : Submodule R K)) : φ (r • z) = r • φ z :=
    LinearMap.map_smul_of_tower φ.toLinearMap r z
  have h1 : φ (LocalizedModule.mk i 1) = LocalizedModule.mk ((t : R) • ⟨y, hy⟩) 1 := by
    rw [← LocalizedModule.mkLinearMap_apply, ← hit, Submonoid.smul_def, hφ,
      LinearEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
  have h2 : (n : R) • (⟨x * i, hx i i.2⟩ : (I : Submodule R K)) = (⟨n * x, hnx⟩ : R) • i := by
    ext
    simp [Subalgebra.smul_def, mul_assoc]
  have h3 : (n : R) • φ (LocalizedModule.mk ⟨x * i, hx i i.2⟩ 1) =
      (⟨n * x, hnx⟩ : R) • LocalizedModule.mk ((t : R) • ⟨y, hy⟩) 1 := by
    rw [← hφ, LocalizedModule.smul'_mk, h2, ← LocalizedModule.smul'_mk, hφ, h1]
  have h4 : LocalizedModule.mk ((n : R) • j) 1 = (LocalizedModule.mk
      ((u : R) • (⟨n * x, hnx⟩ : R) • (t : R) • ⟨y, hy⟩) 1 : LocalizedModule 𝔭.primeCompl _) := by
    rw [← LocalizedModule.smul'_mk, ← LocalizedModule.mkLinearMap_apply, ← hju, Submonoid.smul_def,
      smul_comm, h3, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
  rcases LocalizedModule.mk_eq.mp h4 with ⟨v, hv⟩
  have hv' : ((v : R) : K) * (n * j) =
      ((v : R) : K) * (((u : R) : K) * (n * x * (((t : R) : K) * y))) := by
    simpa [Submonoid.smul_def, Subalgebra.smul_def] using congrArg Subtype.val hv
  refine ⟨v * u * t, (v * u * t).2, ?_⟩
  have h5 : (((v : R) * u * t : R) : K) * (x * y) = ((v : R) : K) * j := by
    refine hn.mul_left_cancel ?_
    push_cast
    linear_combination hv'.symm
  rw [h5]
  simpa [Subalgebra.smul_def] using (J : Submodule R K).smul_mem (v : R) j.2

variable [Algebra ℚ K] [(Subalgebra.toSubmodule R).IsLattice ℚ]

lemma WeaklyEquivalent.div_self_le (h : I.WeaklyEquivalent J) :
    (I : Submodule R K) / I ≤ (J : Submodule R K) / J := by
  intro x hx
  rw [mem_div_iff_forall_mul_mem] at hx ⊢
  intro y hy
  rcases R.exists_natCast_mul_mem_of_span_eq_top
    (IsLattice.span_eq_top (M := Subalgebra.toSubmodule R)) x with ⟨n, hn, hnx⟩
  have hnK : IsUnit (n : K) := by
    rw [← map_natCast (algebraMap ℚ K)]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)).map (algebraMap ℚ K)
  by_contra hxy
  have htop : (J : Submodule R K).colon {x * y} ≠ ⊤ := fun htop ↦ hxy <| by
    simpa using mem_colon_singleton.mp ((Ideal.eq_top_iff_one _).mp htop)
  rcases Ideal.exists_le_maximal _ htop with ⟨𝔭, h𝔭, hle⟩
  rcases h 𝔭 with ⟨φ⟩
  rcases exists_mem_primeCompl_mul_mem φ hx hnK hnx hy with ⟨s, hs, hsxy⟩
  exact hs <| hle <| mem_colon_singleton.mpr <| by simpa [Subalgebra.smul_def] using hsxy

/-- **Weakly equivalent fractional ideals have the same multiplier ring** (LMFDB
`av.weak_equivalence_class`): if `I` and `J` are fractional ideals of an order `R` of a `ℚ`-algebra
`K`, such as an étale one, with isomorphic localisations at every maximal ideal of `R`, then
`(I : I) = (J : J)`, where `(I : I) = {x ∈ K | xI ⊆ I}`. -/
lemma WeaklyEquivalent.div_self_eq (h : I.WeaklyEquivalent J) :
    (I : Submodule R K) / I = (J : Submodule R K) / J :=
  le_antisymm h.div_self_le h.symm.div_self_le

end FractionalIdeal
