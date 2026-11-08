import LeanBridge.ForMathlib.GroupTheory.FiniteAbelian.PrimaryDecomposition
import LeanBridge.ForMathlib.GroupTheory.Socle
import Mathlib.Data.Nat.Squarefree
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RingTheory.Radical.Basic

/-!
# The socle of a finite solvable group

If `G` is a finite solvable group, its socle `soc(G)` is isomorphic to a product of cyclic groups
of prime order (LMFDB `group.socle`). A minimal normal subgroup `N` of `G` is abelian, since its
commutator subgroup is normal in `G` and smaller than `N` by solvability, and for a prime `p`
dividing `|N|` its elements of order dividing `p` form a nontrivial normal subgroup, which is `N`:
so `N` is elementary abelian. Two distinct minimal normal subgroups meet trivially, so they commute,
and `soc(G)` is abelian, of exponent dividing the squarefree radical of `|G|`. In its primary
decomposition, every factor `ZMod q` with `q` a prime power therefore has `q` squarefree, that is,
prime.

## Main results

* `Subgroup.IsMinimalNormal.commutator_eq_bot`: a minimal normal subgroup of a finite solvable
  group is abelian.
* `Subgroup.IsMinimalNormal.exists_prime_forall_pow_eq_one`: it has prime exponent.
* `Subgroup.exists_mulEquiv_pi_zmod_prime_socle` (LMFDB `group.socle`): the socle of a finite
  solvable group is a product of cyclic groups of prime order.
-/

open UniqueFactorizationMonoid

namespace Subgroup

variable {G : Type*} [Group G] {N M : Subgroup G} {x y : G}

lemma IsMinimalNormal.disjoint (hN : N.IsMinimalNormal) (hM : M.IsMinimalNormal) (hNM : N ≠ M) :
    Disjoint N M := by
  have : N.Normal := hN.prop.1
  have : M.Normal := hM.prop.1
  rw [disjoint_iff]
  by_contra h
  exact hNM <| (hN.eq_of_le ⟨inferInstance, h⟩ inf_le_left).symm.trans
    (hM.eq_of_le ⟨inferInstance, h⟩ inf_le_right)

variable [Finite G] [Group.IsSolvable G]

/-- **A minimal normal subgroup of a finite solvable group is abelian**: its commutator subgroup is
normal in `G`, and smaller than it by solvability. -/
lemma IsMinimalNormal.commutator_eq_bot (hN : N.IsMinimalNormal) : ⁅N, N⁆ = ⊥ := by
  have : N.Normal := hN.prop.1
  by_contra h
  have hlt : ⁅N, N⁆ < N := Group.isSolvable_iff_commutator_lt.mp inferInstance N hN.prop.2
  exact hlt.ne (hN.eq_of_le ⟨inferInstance, h⟩ (commutator_le_left N N))

/-- **A minimal normal subgroup of a finite solvable group has prime exponent**: for a prime `p`
dividing its order, its elements of order dividing `p` form a nontrivial normal subgroup of `G`. -/
lemma IsMinimalNormal.exists_prime_forall_pow_eq_one (hN : N.IsMinimalNormal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card G ∧ ∀ x ∈ N, x ^ p = 1 := by
  have hNn : N.Normal := hN.prop.1
  have hcomm (x : G) (hx : x ∈ N) (y : G) (hy : y ∈ N) : Commute x y :=
    mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hN.commutator_eq_bot hy) x hx
  have : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN.prop.2
  rcases Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.mpr this).ne' with
    ⟨p, hp, hpN⟩
  have : Fact p.Prime := ⟨hp⟩
  rcases exists_prime_orderOf_dvd_card' p hpN with ⟨x, hx⟩
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ N ∧ y ^ p = 1}
      mul_mem' := fun ⟨hy, hy'⟩ ⟨hz, hz'⟩ ↦
        ⟨mul_mem hy hz, by rw [(hcomm _ hy _ hz).mul_pow, hy', hz', one_mul]⟩
      one_mem' := ⟨one_mem N, one_pow p⟩
      inv_mem' := fun ⟨hy, hy'⟩ ↦ ⟨inv_mem hy, by rw [inv_pow, hy', inv_one]⟩ }
  have hΩn : Ω.Normal :=
    ⟨fun y hy g ↦ ⟨hNn.conj_mem y hy.1 g, by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩⟩
  have hx1 : (x : G) ≠ 1 := fun h ↦ hp.one_lt.ne' <| hx.symm.trans <| by
    rw [← orderOf_coe, h, orderOf_one]
  have hΩ : Ω ≠ ⊥ := fun h ↦ hx1 <| (mem_bot.mp <| h ▸
    (⟨x.2, by rw [← orderOf_coe] at hx; rw [← hx, pow_orderOf_eq_one]⟩ : (x : G) ∈ Ω))
  have hΩN : Ω = N := hN.eq_of_le ⟨hΩn, hΩ⟩ fun y hy ↦ hy.1
  exact ⟨p, hp, hpN.trans (card_subgroup_dvd_card N), fun y hy ↦ (hΩN ▸ hy : y ∈ Ω).2⟩

lemma socle_le_centralizer (hN : N.IsMinimalNormal) : socle G ≤ centralizer N :=
  sSup_le fun M (hM : M.IsMinimalNormal) z hz ↦ mem_centralizer_iff.mpr fun w hw ↦ by
    rcases eq_or_ne N M with rfl | hNM
    · exact mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp hN.commutator_eq_bot hz) w hw
    · exact commute_of_normal_of_disjoint N M hN.prop.1 hM.prop.1 (hN.disjoint hM hNM) w z hw hz

lemma mul_comm_of_mem_socle (hx : x ∈ socle G) (hy : y ∈ socle G) : x * y = y * x := by
  have hle : socle G ≤ centralizer {x} := sSup_le fun N (hN : N.IsMinimalNormal) n hn ↦
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (socle_le_centralizer hN hx) n hn)
  exact (mem_centralizer_singleton_iff.mp (hle hy)).symm

lemma pow_radical_eq_one_of_mem_socle (hx : x ∈ socle G) : x ^ radical (Nat.card G) = 1 := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ socle G ∧ y ^ radical (Nat.card G) = 1}
      mul_mem' := fun ⟨hy, hy'⟩ ⟨hz, hz'⟩ ↦ ⟨mul_mem hy hz, by
        rw [Commute.mul_pow (mul_comm_of_mem_socle hy hz), hy', hz', one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow _⟩
      inv_mem' := fun ⟨hy, hy'⟩ ↦ ⟨inv_mem hy, by rw [inv_pow, hy', inv_one]⟩ }
  have hle : socle G ≤ S := sSup_le fun N hN y hy ↦ ⟨le_socle hN hy, by
    rcases hN.exists_prime_forall_pow_eq_one with ⟨p, hp, hpG, hpN⟩
    rcases (dvd_radical_iff_of_irreducible hp.prime.irreducible Nat.card_pos.ne').mpr hpG with
      ⟨k, hk⟩
    rw [hk, pow_mul, hpN y hy, one_pow]⟩
  exact (hle hx).2

/-- **The socle of a finite solvable group is a product of cyclic groups of prime order** (LMFDB
`group.socle`): it is abelian, of exponent dividing the squarefree radical of `|G|`, so the
prime-power orders of the factors of its primary decomposition are primes. -/
lemma exists_mulEquiv_pi_zmod_prime_socle : ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ),
    (∀ i, (p i).Prime) ∧ Nonempty (socle G ≃* Π i, Multiplicative (ZMod (p i))) := by
  classical
  let inst : CommGroup (socle G) :=
    { (inferInstance : Group (socle G)) with
      mul_comm := fun x y ↦ Subtype.ext (mul_comm_of_mem_socle x.2 y.2) }
  rcases AddCommGroup.exists_addEquiv_pi_zmod_isPrimePow (G := Additive (socle G)) with
    ⟨ι, _, q, hq, ⟨e⟩⟩
  refine ⟨ι, inferInstance, q, fun i ↦ ?_,
    ⟨(AddEquiv.toMultiplicativeRight e).trans (MulEquiv.piMultiplicative _)⟩⟩
  have hx : radical (Nat.card G) • e.symm (Pi.single i 1) = 0 :=
    Additive.toMul.injective <| Subtype.ext <| by
      rw [toMul_nsmul, SubgroupClass.coe_pow,
        pow_radical_eq_one_of_mem_socle (Additive.toMul (e.symm (Pi.single i 1))).2]
      rfl
  have hdvd : q i ∣ radical (Nat.card G) := by
    have h : e (radical (Nat.card G) • e.symm (Pi.single i 1)) i = e 0 i :=
      congrFun (congrArg e hx) i
    rw [map_nsmul, e.apply_symm_apply, map_zero, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul,
      mul_one, Pi.zero_apply] at h
    exact (CharP.cast_eq_zero_iff (ZMod (q i)) (q i) _).mp h
  exact Nat.squarefree_and_prime_pow_iff_prime.mp ⟨squarefree_radical.squarefree_of_dvd hdvd, hq i⟩

end Subgroup
