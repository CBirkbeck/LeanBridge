import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Valuation.Integral

/-!
# The `p`-rank of a Weil polynomial

The `p`-rank of an abelian variety `A` over `𝔽_q`, `q = p ^ r`, is the dimension of its geometric
`p`-torsion (LMFDB `av.fq.p_rank`, `TauCeti.AlgebraicGeometry.AbelianVariety.pRank`). By the
theory of Dieudonné modules (Manin; not formalised here) it is the number of roots of the Weil
polynomial of `A` that are `p`-adic units, which is how the LMFDB computes it from the Weil
polynomial indexing the isogeny class of `A`. This file defines the `p`-rank of a polynomial
`h ∈ ℤ[x]` as the number of roots of `h` in the algebraic closure `ℚ̄_p` of `ℚ_p`, counted with
multiplicity, of `p`-adic absolute value `1`, and computes it from the reduction of `h` modulo
`p`: for monic `h` it is `deg h - ord_x (h mod p)`, the length of the horizontal segment of the
Newton polygon of `h` at `p`.

## Main definitions

* `Polynomial.pRank` (LMFDB `av.fq.p_rank`, as the LMFDB computes it): the number of roots of `h`
  in `ℚ̄_p` that are `p`-adic units.
* `Polynomial.pCorank` (LMFDB `av.fq.p_rank`, as the LMFDB computes it): `g` minus the `p`-rank,
  for `deg h = 2 g`.

## Main results

* `Polynomial.pRank_eq`: the `p`-rank of a monic `h` is `deg h - ord_x (h mod p)`.
-/

open Valuation
open scoped Valued

namespace PadicAlgCl

variable {p : ℕ} [Fact p.Prime]

lemma residue_eq_zero_iff_norm_lt_one {x : 𝒪[PadicAlgCl p]} :
    IsLocalRing.residue _ x = 0 ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Integer.not_isUnit_iff_valuation_lt_one, valuation_def, ← NNReal.coe_lt_coe, coe_nnnorm,
    NNReal.coe_one]

instance : CharP 𝓀[PadicAlgCl p] p := by
  refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
  rw [← map_natCast (IsLocalRing.residue _), residue_eq_zero_iff_norm_lt_one,
    SubringClass.coe_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), norm_extends]
  exact Padic.norm_p_lt_one

end PadicAlgCl

namespace Polynomial

variable (p : ℕ) [Fact p.Prime] (h : ℤ[X])

/-- The **`p`-rank** (LMFDB `av.fq.p_rank`) of a polynomial `h ∈ ℤ[x]`: the number of roots of `h`
in the algebraic closure `ℚ̄_p` of `ℚ_p`, counted with multiplicity, that are `p`-adic units. For
the Weil polynomial `h` of an abelian variety `A` over `𝔽_q`, `q = p ^ r`, this is the `p`-rank of
`A`, the dimension of its geometric `p`-torsion (Manin; not formalised here), and it is how the
LMFDB computes the `p`-rank of an isogeny class. It is computed from `h mod p` by
`Polynomial.pRank_eq`. -/
noncomputable def pRank : ℕ :=
  ((h.map (Int.castRingHom (PadicAlgCl p))).roots.filter (‖·‖ = 1)).card

/-- The **`p`-corank** (LMFDB `av.fq.p_rank`) of a polynomial `h ∈ ℤ[x]` of degree `2 g`: the
difference `g - p-rank` between `g` and its `p`-rank `Polynomial.pRank`. For the Weil polynomial of
a `g`-dimensional abelian variety `A` over `𝔽_q`, `q = p ^ r`, this is the `p`-corank of `A`. -/
noncomputable def pCorank : ℕ :=
  h.natDegree / 2 - h.pRank p

variable {p h}

lemma natTrailingDegree_map_of_injective {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : Function.Injective f) (P : R[X]) : (P.map f).natTrailingDegree = P.natTrailingDegree := by
  simp [natTrailingDegree, trailingDegree, support_map_of_injective P hf]

variable (hh : h.Monic) {x : PadicAlgCl p} (hx : x ∈ (h.map (Int.castRingHom (PadicAlgCl p))).roots)

include hh hx in
lemma mem_integer_of_mem_roots : x ∈ 𝒪[PadicAlgCl p] :=
  (integer.integers _).mem_of_integral <| IsIntegral.tower_top ⟨h, hh, (eval_map _ x).symm.trans <|
    isRoot_of_mem_roots hx⟩

include hh hx in
lemma norm_le_one_of_mem_roots : ‖x‖ ≤ 1 :=
  NNReal.coe_le_one.mpr <| mem_integer_of_mem_roots hh hx

include hh in
/-- The `p`-rank of a monic polynomial `h ∈ ℤ[x]` is `deg h - ord_x (h mod p)`: the number of
nonzero roots of `h mod p` in an algebraic closure of `𝔽_p`, or the length of the horizontal
segment of the Newton polygon of `h` at `p`. -/
lemma pRank_eq :
    h.pRank p = h.natDegree - (h.map (Int.castRingHom (ZMod p))).natTrailingDegree := by
  classical
  let S : Multiset 𝒪[PadicAlgCl p] := (h.map (Int.castRingHom (PadicAlgCl p))).roots.attach.map
    fun x ↦ ⟨x.1, mem_integer_of_mem_roots hh x.2⟩
  have hS : S.map Subtype.val = (h.map (Int.castRingHom (PadicAlgCl p))).roots := by
    rw [Multiset.map_map]
    exact Multiset.attach_map_val _
  clear_value S
  have hO : h.map (Int.castRingHom 𝒪[PadicAlgCl p]) = (S.map (X - C ·)).prod := by
    refine map_injective (𝒪[PadicAlgCl p].subtype) Subtype.val_injective ?_
    rw [map_map, Polynomial.map_multiset_prod, Multiset.map_map,
      RingHom.ext_int (𝒪[PadicAlgCl p].subtype.comp _) (Int.castRingHom _),
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (hh.map _), ← hS, Multiset.map_map]
    simp
  have hk : h.map (Int.castRingHom 𝓀[PadicAlgCl p]) =
      ((S.map (IsLocalRing.residue _)).map (X - C ·)).prod := by
    rw [← RingHom.ext_int ((IsLocalRing.residue _).comp (Int.castRingHom 𝒪[PadicAlgCl p]))
      (Int.castRingHom 𝓀[PadicAlgCl p]), ← map_map, hO, Polynomial.map_multiset_prod,
      Multiset.map_map, Multiset.map_map]
    simp
  have htd : (h.map (Int.castRingHom (ZMod p))).natTrailingDegree =
      ((h.map (Int.castRingHom (PadicAlgCl p))).roots.filter (‖·‖ < 1)).card := by
    rw [← natTrailingDegree_map_of_injective (ZMod.castHom_injective 𝓀[PadicAlgCl p]), map_map,
      RingHom.ext_int ((ZMod.castHom _ _).comp _) (Int.castRingHom 𝓀[PadicAlgCl p]),
      ← rootMultiplicity_eq_natTrailingDegree', ← count_roots, hk, roots_multiset_prod_X_sub_C,
      Multiset.count_map, ← hS, Multiset.filter_map, Multiset.card_map]
    exact congrArg _ <| Multiset.filter_congr fun x _ ↦
      eq_comm.trans PadicAlgCl.residue_eq_zero_iff_norm_lt_one
  have hcard : h.natDegree =
      ((h.map (Int.castRingHom (PadicAlgCl p))).roots.filter (‖·‖ < 1)).card + h.pRank p := by
    rw [pRank, ← Multiset.card_add, ← hh.natDegree_map (Int.castRingHom (PadicAlgCl p)),
      (IsAlgClosed.splits _).natDegree_eq_card_roots]
    refine congrArg Multiset.card <| (Multiset.filter_add_not (‖·‖ < 1) _).symm.trans ?_
    exact congrArg _ <| Multiset.filter_congr fun x hx ↦
      not_lt.trans ⟨(norm_le_one_of_mem_roots hh hx).antisymm, ge_of_eq⟩
  rw [hcard, htd, Nat.add_sub_cancel_left]

end Polynomial
