/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Certificate
import LeanBridge.IdealArithmetic.Galois.Determine
import LeanBridge.IdealArithmetic.Galois.EvenSextic
import LeanBridge.IdealArithmetic.Galois.SemidirectA4
import LeanBridge.IdealArithmetic.Signature.ResultantRecursive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.NormNum.Prime

/-!
# Degree-6 showcase: `Gal(X⁶−5X⁴−50X²+125) ≅ A₄×C₂` (6T6)

The headline degree-6 example. `f = X⁶−5X⁴−50X²+125 = g(X²)` where `g = Y³−5Y²−50Y+125` is an
irreducible cyclic cubic (`disc g = 875²`). Its splitting field `L = M(√θ₁,√θ₂,√θ₃)` over
`M = SplittingField g = ℚ(ζ₇)⁺` has degree `24`, and `Gal(f) ≅ A₄×C₂ = 6T6`.

Method (Awtrey–Jakes, *Galois groups of even sextic polynomials*, Canad. Math. Bull. 63 (2020)):
the ±-pairing on the roots is a `Gal`-invariant block system giving `Gal f ↪ C₂≀S₃ = C₂³⋊S₃`; the
block action is `Gal g = C₃` (`galoisGroup_cubic`), so `Gal f ↪ C₂³⋊C₃` (order 24) — the upper
bound. The lower bound *generates* the kernel `Gal(L/M) = C₂³` from a single `p=13` Frobenius
involution (via `Certificate.lean` / Dedekind) together with the cubic's `C₃` symmetry — avoiding
multiquadratic Kummer theory entirely (Route G). See `.mathlib-quality/decomposition.md`, Result R4.

See `.mathlib-quality/tickets.md`, tickets T014–T024.
-/

open Polynomial

namespace IdealArithmetic.Galois.DegSix

attribute [local instance] factSplitsSplittingField

/-- The showcase polynomial `f = X⁶ − 5X⁴ − 50X² + 125 ∈ ℤ[X]`. -/
noncomputable def f : ℤ[X] := X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125

/-- The resolvent cubic `g = Y³ − 5Y² − 50Y + 125 ∈ ℤ[X]`; the roots of `g` are the squares of the
roots of `f`, and `f = g.comp (X ^ 2)`. -/
noncomputable def g : ℤ[X] := X ^ 3 - 5 * X ^ 2 - 50 * X + 125

/-- `f = g(X²)`: the showcase sextic is the resolvent cubic composed with `X²`. -/
theorem f_eq_g_comp : f = g.comp (X ^ 2) := by
  simp only [f, g, sub_comp, add_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
  ring

/-- Over `ℚ`: `f = g(X²)`, the form `restrictComp` consumes. -/
theorem fℚ_eq_gℚ_comp :
    f.map (Int.castRingHom ℚ) = (g.map (Int.castRingHom ℚ)).comp (X ^ 2) := by
  rw [f_eq_g_comp, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]

/-! ### The resolvent cubic `g` is an irreducible cyclic cubic (`Gal g = C₃`) -/

/-- `g` has degree `3`. -/
theorem g_natDegree : g.natDegree = 3 := by unfold g; compute_degree!

/-- `g` is monic. -/
theorem g_monic : g.Monic := by unfold g; monicity!

/-- `g` is irreducible over `ℤ`: it is irreducible mod 3 (a cubic with no roots in `𝔽₃`), lifted by
`Monic.irreducible_of_irreducible_map`. -/
theorem g_irreducible : Irreducible g := by
  apply Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3)) g g_monic
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, g_monic.natDegree_map, g_natDegree]; omega
  · intro x
    simp only [g, Polynomial.IsRoot.def, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat,
      eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
    fin_cases x <;> decide

/-- `g` mapped to `ℚ` is monic. -/
theorem gℚ_monic : (g.map (Int.castRingHom ℚ)).Monic := g_monic.map _

/-- `g` mapped to `ℚ` has degree `3`. -/
theorem gℚ_natDegree : (g.map (Int.castRingHom ℚ)).natDegree = 3 := by
  rw [g_monic.natDegree_map, g_natDegree]

/-- `g` is irreducible over `ℚ`. -/
theorem gℚ_irreducible : Irreducible (g.map (Int.castRingHom ℚ)) := by
  rw [← algebraMap_int_eq]
  exact (Monic.irreducible_iff_irreducible_map_fraction_map g_monic).1 g_irreducible

/-- `disc g = 765625 = 875²` (a perfect square) — hence `Gal g ⊆ A₃`, so `Gal g = C₃`. -/
theorem gℚ_discr : (g.map (Int.castRingHom ℚ)).discr = 765625 := by
  have hdeg : (g.map (Int.castRingHom ℚ)).degree = 3 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num)).2 gℚ_natDegree
  rw [discr_of_degree_eq_three hdeg]
  simp only [Polynomial.coeff_map, g, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_ofNat_zero, Polynomial.coeff_ofNat_succ]
  norm_num [Polynomial.coeff_X]

/-- **(L4.1) `Nat.card (Gal g) = 3`** — `g` is an irreducible cyclic cubic. -/
theorem card_gal_g : Nat.card (g.map (Int.castRingHom ℚ)).Gal = 3 :=
  (galoisGroup_cubic _ gℚ_irreducible gℚ_monic gℚ_natDegree).1 ⟨875, by rw [gℚ_discr]; norm_num⟩

/-! ### Route G: `|Gal f| = 3 · |K|` where `K = ker(restrictComp) = Gal(L/M)` -/

/-- `deg(X²) = 2 ≠ 0` over `ℚ` — the hypothesis `restrictComp` requires. -/
theorem X_sq_natDegree_ne_zero : (X ^ 2 : ℚ[X]).natDegree ≠ 0 := by
  rw [natDegree_X_pow]; norm_num

/-- **(L4.3, showcase).** `|Gal f| = 3 · |K|` with `K = ker(restrictComp (g) (X²))` the sign-change
kernel `Gal(L/M)`. Transports `Gal f = Gal(g(X²))` via `galCongr` and applies the general Lagrange
factorization `card_gal_comp_eq` together with `|Gal g| = 3`. Reduces D6-M1 (`|Gal f| = 24`) to the
kernel-order computation `|K| = 8`. -/
theorem card_gal_f_eq_three_mul_card_ker :
    Nat.card (f.map (Int.castRingHom ℚ)).Gal
      = 3 * Nat.card (MonoidHom.ker (Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
          X_sq_natDegree_ne_zero)) := by
  rw [Nat.card_congr (EvenSextic.galCongr fℚ_eq_gℚ_comp).toEquiv,
    EvenSextic.card_gal_comp_eq (g.map (Int.castRingHom ℚ)) (X ^ 2) X_sq_natDegree_ne_zero,
    card_gal_g]

/-- `g(X²)` evaluated at `0` is its constant term `125`, over **any** `ℚ`-algebra `L`. Stated with an
abstract instance on purpose: over the concrete `SplittingField` instance `simp` refuses to distribute
`aeval` through the polynomial (the `Algebra ℚ (SplittingField _)` instance-diamond), but the abstract
proof instantiates by pure substitution. -/
theorem aeval_zero_gq_comp {L : Type*} [Field L] [Algebra ℚ L] :
    aeval (0 : L) ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)) = 125 := by
  rw [aeval_comp, map_pow, aeval_X, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [g, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, map_add, map_sub, map_mul, map_pow, aeval_X,
    map_ofNat, mul_zero, zero_pow, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_add]

/-- **Nondegenerate blocks.** No root of `f = g(X²)` equals its own negative: `x = -x ⟹ 2x = 0 ⟹
x = 0` (char 0), but `0` is not a root since `g(0) = 125 ≠ 0`. -/
theorem root_ne_neg (x : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).rootSet
      ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField) :
    (x : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField)
      ≠ -(x : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField) := by
  intro hx
  have hx0 : (x : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField) = 0 :=
    (mul_eq_zero.mp (show (2 : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField) * (x : _)
      = 0 by linear_combination hx)).resolve_left two_ne_zero
  have hval := aeval_zero_gq_comp (L := ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField)
  have hroot := (mem_rootSet.mp x.2).2
  rw [hx0, hval] at hroot
  norm_num at hroot

/-- **The resolvent cubic has `3` distinct roots in `L`** (it is separable — irreducible over `ℚ`,
char 0 — and splits in `L = SplittingField (g(X²))`). -/
theorem card_rootSet_gq :
    Nat.card ((g.map (Int.castRingHom ℚ)).rootSet
      ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField) = 3 := by
  rw [Nat.card_eq_fintype_card, ← gℚ_natDegree]
  exact card_rootSet_eq_natDegree gℚ_irreducible.separable
    (Gal.splits_in_splittingField_of_comp (g.map (Int.castRingHom ℚ)) (X ^ 2)
      X_sq_natDegree_ne_zero)

/-! ### The `p = 13` Frobenius certificate (T020): `f mod 13 = (X+2)(X+5)(X−5)(X−2)(X²−2)` -/

/-- `2` is a non-residue mod `13`, so `X² − 2` has no root in `𝔽₁₃` (proved `Fact`-free so `decide`
uses the computable `ZMod 13` instances, not the `Field`-poisoned ones). -/
theorem no_root_X2_sub_2 : ∀ x : ZMod 13, x ^ 2 - 2 ≠ 0 := by decide

/-- `f` is monic. -/
theorem f_monic : f.Monic := by unfold f; monicity!

/-- `f` has nonzero degree. -/
theorem f_natDegree_ne : f.natDegree ≠ 0 := by
  have hd : f.natDegree = 6 := by unfold f; compute_degree!
  omega

/-- `f = ofList [125, 0, −50, 0, −5, 0, 1]` — the coefficient-list form the discriminant engine
consumes. -/
theorem f_ofList : ofList ([125, 0, -50, 0, -5, 0, 1] : List ℤ) = f := by
  unfold f
  simp only [ofList_cons, ofList_nil, mul_zero, add_zero, map_ofNat, map_neg, C_0, C_1, mul_one]
  ring

/-- The subresultant pseudo-remainder sequence for `disc f`, reused verbatim from the ring-of-integers
certificate for this field (`Examples/NF6_4_19208000_1`). -/
def SturmRC : SturmBuilderOfList [[125, 0, -50, 0, -5, 0, 1], [0, -100, 0, -20, 0, 6],
    [-4500, 0, 1200, 0, 60], [0, -35000, 0, 14000], [245000000, 0, -73500000], [0, -321562500000],
    [-4689453125000000]] ([125, 0, -50, 0, -5, 0, 1] : List ℤ) [0, -100, 0, -20, 0, 6] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 6 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [36, 3600, 196000000, 5402250000000000, 103402441406250000000000]
  f := [1, 36, 3600, 196000000, 5402250000000000]
  epos := by decide
  fpos := by decide
  Q := [[0, 6], [0, 360], [0, 840000], [0, -1029000000000], [0, 23634843750000000000]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 5 := by omega
    interval_cases i <;> (dsimp ; decide)

/-- **`disc f = −2⁶·5¹⁵·7⁴ = −4689453125000000`** (`= (−1)³·4³·g(0)·disc(g)²`), via the repo's
recursive-resultant discriminant engine. -/
theorem f_discr : f.discr = -4689453125000000 := by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  · rw [f_ofList]
  · decide

/-- `13 ∤ disc f` — the certificate's separability input. -/
theorem f_disc_mod13 : (Int.castRingHom (ZMod 13)) f.discr ≠ 0 := by rw [f_discr]; decide

/-- **(T020) The `p = 13` Frobenius certificate.** `f mod 13 = (X+2)(X+5)(X−5)(X−2)(X²−2)`: four
`𝔽₁₃`-rational roots (`±2, ±5`) and one irreducible quadratic (`X²−2`, `2` a non-residue), so the
factor degrees are `{1,1,1,1,2}` — the Frobenius at `13` is a single transposition. -/
noncomputable def cert13 : FrobeniusCycleTypeCertificate f where
  p := 13
  hp := by norm_num
  hdisc := f_disc_mod13
  factors := {X + 2, X + 5, X - 5, X - 2, X ^ 2 - 2}
  hirr := by
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    intro q hq
    fin_cases hq
    · rw [show (X + 2 : (ZMod 13)[X]) = X - C (-2) by simp only [map_neg, map_ofNat, sub_neg_eq_add]]
      exact irreducible_X_sub_C _
    · rw [show (X + 5 : (ZMod 13)[X]) = X - C (-5) by simp only [map_neg, map_ofNat, sub_neg_eq_add]]
      exact irreducible_X_sub_C _
    · rw [show (X - 5 : (ZMod 13)[X]) = X - C 5 by rw [map_ofNat]]
      exact irreducible_X_sub_C _
    · rw [show (X - 2 : (ZMod 13)[X]) = X - C 2 by rw [map_ofNat]]
      exact irreducible_X_sub_C _
    · apply irreducible_of_degree_le_three_of_not_isRoot
      · have hd : (X ^ 2 - 2 : (ZMod 13)[X]).natDegree = 2 := by compute_degree!
        rw [Finset.mem_Icc, hd]; omega
      · intro x hx
        exact no_root_X2_sub_2 x
          (by simpa only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_ofNat] using hx)
  hprod := by
    show ({X + 2, X + 5, X - 5, X - 2, X ^ 2 - 2} : Multiset (ZMod 13)[X]).prod
      = f.map (Int.castRingHom (ZMod 13))
    rw [show f = X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125 from rfl]
    simp only [Multiset.insert_eq_cons, Multiset.prod_cons, Multiset.prod_singleton]
    rw [show ((X + 2) * ((X + 5) * ((X - 5) * ((X - 2) * (X ^ 2 - 2)))) : (ZMod 13)[X])
        = ofList [2, 1] * ofList [5, 1] * ofList [-5, 1] * ofList [-2, 1] * ofList [-2, 0, 1] by
      simp only [ofList_cons, ofList_nil, mul_zero, add_zero, C_0, C_1, mul_one, map_ofNat, map_neg]
      ring,
      ← ofList_convolve_eq_mul, ← ofList_convolve_eq_mul, ← ofList_convolve_eq_mul,
      ← ofList_convolve_eq_mul,
      show (X ^ 6 - 5 * X ^ 4 - 50 * X ^ 2 + 125 : ℤ[X]) = ofList [125, 0, -50, 0, -5, 0, 1] from
        f_ofList.symm, ofList_map]
    exact congrArg ofList (by decide)

/-- **The `p = 13` certificate's factor degrees are `{1,1,1,1,2}`.** Four `𝔽₁₃`-rational roots (`±2, ±5`)
and one irreducible quadratic (`X²−2`), so the Frobenius at `13` is a single transposition. -/
private theorem cert13_map_natDegree :
    cert13.factors.map Polynomial.natDegree = ({1, 1, 1, 1, 2} : Multiset ℕ) := by
  haveI : Fact (1 < 13) := ⟨by norm_num⟩
  show ({X + 2, X + 5, X - 5, X - 2, X ^ 2 - 2} : Multiset (ZMod 13)[X]).map Polynomial.natDegree
    = {1, 1, 1, 1, 2}
  rw [show (X + 2 : (ZMod 13)[X]) = X + C 2 by rw [map_ofNat],
      show (X + 5 : (ZMod 13)[X]) = X + C 5 by rw [map_ofNat],
      show (X - 5 : (ZMod 13)[X]) = X - C 5 by rw [map_ofNat],
      show (X - 2 : (ZMod 13)[X]) = X - C 2 by rw [map_ofNat],
      show (X ^ 2 - 2 : (ZMod 13)[X]) = X ^ 2 - C 2 by rw [map_ofNat]]
  simp

/-- **Order-2 ⟹ in the sign-change kernel.** An involution `σ'` of `Gal(g(X²))` lies in
`ker(restrictComp)`: its image in `Gal g` has order dividing `gcd(2, |Gal g|) = gcd(2, 3) = 1`, so is
trivial. (General shape: order coprime to the block-action group forces membership in the normal
kernel; kept local since the `|Gal g| = 3` coprimality is specific to this example.) -/
private theorem mem_ker_restrictComp_of_orderOf_two
    (σ' : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).Gal) (hord : orderOf σ' = 2) :
    σ' ∈ MonoidHom.ker (Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
      X_sq_natDegree_ne_zero) := by
  rw [MonoidHom.mem_ker]
  have hd1 := orderOf_map_dvd (Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
    X_sq_natDegree_ne_zero) σ'
  have hd2 := orderOf_dvd_natCard ((Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
    X_sq_natDegree_ne_zero) σ')
  rw [hord] at hd1
  rw [card_gal_g] at hd2
  have hg : orderOf ((Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
    X_sq_natDegree_ne_zero) σ') ∣ Nat.gcd 2 3 := Nat.dvd_gcd hd1 hd2
  rw [show Nat.gcd 2 3 = 1 by decide] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

open scoped Classical in
/-- **(Route G lower-bound generator — T018/T020).** Every coordinate flip `Pi.single θ 1` is realised
by a kernel element: a single `p=13` Frobenius involution flips one block (`blockSign σ' = Pi.single θ₀ 1`),
and the cubic's `C₃`-symmetry (`blockSign_generates`) spreads it to every block. This is the `hgen`
hypothesis powering both `|K| = 8` and the `Gal f ≅ A₄ × C₂` action identification. -/
theorem blockSign_generates_all :
    ∀ θ : (g.map (Int.castRingHom ℚ)).rootSet
        ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).SplittingField,
      ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
        X_sq_natDegree_ne_zero)),
        EvenSextic.blockSign (g.map (Int.castRingHom ℚ)) gℚ_monic (κ : ((g.map (Int.castRingHom ℚ)).comp
          (X ^ 2)).Gal) = Pi.single θ 1 := by
  -- A `p = 13` arithmetic Frobenius `σf`; its cycle-type partition on the roots of `f` is `{1,1,1,1,2}`.
  obtain ⟨σf, hσf⟩ := @exists_partition_eq_of_certificate f f_monic f_natDegree_ne
    (factSplitsSplittingField (f.map (Int.castRingHom ℚ))) cert13
  -- Transport into the `g(X²)` picture via `galCongr`, then onto the honest root permutation `fRootEquiv`.
  set σ' : ((g.map (Int.castRingHom ℚ)).comp (X ^ 2)).Gal :=
    EvenSextic.galCongr fℚ_eq_gℚ_comp σf
  have h1 := (EvenSextic.galActionHom_partition_galCongr fℚ_eq_gℚ_comp σf).trans hσf
  have hpartsF : (EvenSextic.fRootEquiv (g.map (Int.castRingHom ℚ)) σ').partition.parts
      = ({1, 1, 1, 1, 2} : Multiset ℕ) :=
    ((EvenSextic.galActionHom_partition_parts_eq (g.map (Int.castRingHom ℚ)) σ').symm.trans
      h1).trans cert13_map_natDegree
  -- Cycle type `{2}` ⟹ a single transposition of one `±`-pair ⟹ support of size `2`.
  have hct : (EvenSextic.fRootEquiv (g.map (Int.castRingHom ℚ)) σ').cycleType = {2} := by
    rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, hpartsF]; decide
  have hsupp : (EvenSextic.fRootEquiv (g.map (Int.castRingHom ℚ)) σ').support.card = 2 := by
    rw [← Equiv.Perm.sum_cycleType, hct]; decide
  -- `σ'` is an involution (order 2), hence lies in the sign-change kernel.
  have hord : orderOf σ' = 2 := by
    rw [EvenSextic.orderOf_eq_orderOf_fRootEquiv, ← Equiv.Perm.lcm_cycleType, hct]; decide
  -- One flipped block ⟹ `blockSign σ' = Pi.single θ₀ 1`; the cubic's `C₃`-symmetry spreads it to all
  -- three coordinates, generating the full `(ZMod 2)³`.
  obtain ⟨θ₀, hθ₀⟩ := EvenSextic.blockSign_eq_single_of_support_card_two
    (g.map (Int.castRingHom ℚ)) gℚ_monic root_ne_neg σ' hsupp
  exact fun θ => EvenSextic.blockSign_generates (g.map (Int.castRingHom ℚ))
    X_sq_natDegree_ne_zero gℚ_monic gℚ_irreducible
      (mem_ker_restrictComp_of_orderOf_two σ' hord) hθ₀ θ

/-- **(Route G target — T017–T020).** The sign-change kernel `K = Gal(L/M)` has order `8` (`= |C₂³|`):
upper bound `K ↪ (ZMod 2)³` (the `±`-block system), lower bound `blockSign_generates_all` (a single
`p=13` Frobenius involution together with the cubic's `C₃` symmetry) — avoiding multiquadratic Kummer
theory. So `|K| = 2^(#roots of g) = 2³ = 8` (`exact`, not `rw`, on the final `card_rootSet_gq`: the
`rootSet` term from `card_ker_eq` is only *defeq*, not syntactically equal). -/
theorem card_ker :
    Nat.card (MonoidHom.ker (Gal.restrictComp (g.map (Int.castRingHom ℚ)) (X ^ 2)
      X_sq_natDegree_ne_zero)) = 8 := by
  rw [EvenSextic.card_ker_eq (g.map (Int.castRingHom ℚ)) X_sq_natDegree_ne_zero gℚ_monic
    root_ne_neg blockSign_generates_all, show (8 : ℕ) = 2 ^ 3 from rfl]
  exact congrArg (2 ^ ·) card_rootSet_gq

/-- **D6-M1 (stepping stone).** The splitting field of `f` has degree `24` over `ℚ`, i.e. the Galois
group `Gal f` has order `24`. Proven via Route G: `Gal f ↠ Gal g = C₃` with kernel `Gal(L/M) = C₂³`
generated by a `p=13` Frobenius involution and the cubic's `C₃` symmetry. -/
theorem card_gal_f : Nat.card (f.map (Int.castRingHom ℚ)).Gal = 24 := by
  rw [card_gal_f_eq_three_mul_card_ker, card_ker]

/-! ### D6-M2: `Gal f ≅ A₄ × C₂` (the group `6T6`)

The kernel `K = Gal(L/M) ≅ C₂³` (`card_ker`) is a normal subgroup of `Gal f ≅ Gal(g(X²))` with cyclic
quotient `Gal g ≅ C₃`. Schur–Zassenhaus splits it as `K ⋊ C₃`; the `C₃`-action on the `±`-block signs
is the block permutation `hRoot` of the cubic's `C₃`-symmetry (`blockSign_conj`), and `threeBlockIso`
identifies the resulting `C₂³ ⋊ C₃` with `A₄ × C₂`. -/

/-- `gq = g` viewed over `ℚ` (the resolvent cubic). -/
private noncomputable abbrev gq : ℚ[X] := g.map (Int.castRingHom ℚ)

/-- `Gal f` presented through the composition `g(X²)` (identified with `Gal f` via `galCongr`). -/
private noncomputable abbrev GalP := (gq.comp (X ^ 2)).Gal

/-- Restriction to the resolvent cubic, `Gal(g(X²)) →* Gal g` (the `±`-block permutation action). -/
private noncomputable abbrev rc : GalP →* gq.Gal :=
  Gal.restrictComp gq (X ^ 2) X_sq_natDegree_ne_zero

/-- The sign-change kernel `K = Gal(L/M) = ker(rc) ≅ C₂³`. -/
private noncomputable abbrev K : Subgroup GalP := MonoidHom.ker rc

/-- `|Gal(g(X²))| = 24`, transported from `|Gal f| = 24` along `f = g(X²)`. -/
private theorem cardGalP : Nat.card GalP = 24 := by
  rw [← Nat.card_congr (EvenSextic.galCongr fℚ_eq_gℚ_comp).toEquiv]; exact card_gal_f

/-- **Schur–Zassenhaus: a `C₃` complement of the kernel.** Since `|K| = 8` and `[GalP : K] = 3` are
coprime, the normal kernel `K` has a complement `C` with `|C| = [GalP : K] = 3`. -/
private theorem exists_complement_card_three :
    ∃ C : Subgroup GalP, K.IsComplement' C ∧ Nat.card C = 3 := by
  have hindex : K.index = 3 := by
    have h1 : Nat.card K * K.index = Nat.card GalP := K.card_mul_index
    rw [card_ker, cardGalP] at h1; omega
  obtain ⟨C, hC⟩ : ∃ C : Subgroup GalP, K.IsComplement' C := by
    apply Subgroup.exists_right_complement'_of_coprime (N := K)
    rw [card_ker, hindex]; decide
  exact ⟨C, hC, by have := hC.card_mul; rw [card_ker, cardGalP] at this; omega⟩

open IdealArithmetic.Galois.EvenSextic in
/-- **The block permutation has order 3.** For `c₀ ≠ 1` in the `C₃` complement `C`, the block-label
permutation `hRootHom gq c₀` (the resolvent's `C₃`-symmetry acting on the roots of `g`) has order `3`:
`rc` is injective on `C` (since `C ∩ K = 1`), so `orderOf (hRootHom c₀) = orderOf (rc c₀) = orderOf c₀`,
which divides the prime `|C| = 3` and is `≠ 1`. -/
private theorem orderOf_blockPerm_eq_three (C : Subgroup GalP) (hC : K.IsComplement' C)
    (c₀ : C) (hc0ne : c₀ ≠ 1) (hCcard : Nat.card C = 3) :
    orderOf (hRootHom gq (c₀ : GalP)) = 3 := by
  haveI : Fact ((gq.map (algebraMap ℚ (gq.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp gq (X ^ 2) X_sq_natDegree_ne_zero⟩
  have hinjC : Function.Injective (rc.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]; intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hxK : (C.subtype x) ∈ K := by rw [MonoidHom.mem_ker]; exact hx
    have hd := hC.disjoint; rw [Subgroup.disjoint_def] at hd
    have hx1 : (C.subtype x : GalP) = 1 := hd hxK x.2
    rw [Subgroup.mem_bot]; exact Subtype.ext hx1
  have hhr : hRootHom gq (c₀ : GalP)
      = Gal.galActionHom gq (gq.comp (X ^ 2)).SplittingField (rc (c₀ : GalP)) := by
    apply Equiv.ext; intro θ
    exact (galActionHom_restrictComp_eq_hRoot gq X_sq_natDegree_ne_zero (c₀ : GalP) θ).symm
  -- `orderOf (hRootHom c₀) = orderOf (galActionHom (rc c₀)) = orderOf (rc c₀) = orderOf c₀` (term mode,
  -- so the two `Fact (…Splits)` instances — defeq by proof irrelevance — bridge without `rw`).
  have hord3 : orderOf (hRootHom gq (c₀ : GalP)) = orderOf c₀ :=
    (congrArg orderOf hhr).trans
      ((orderOf_injective (Gal.galActionHom gq (gq.comp (X ^ 2)).SplittingField)
          (Gal.galActionHom_injective gq (gq.comp (X ^ 2)).SplittingField) (rc (c₀ : GalP))).trans
        (orderOf_injective (rc.comp C.subtype) hinjC c₀))
  rw [hord3]
  rcases (Nat.dvd_prime (by norm_num)).mp (hCcard ▸ orderOf_dvd_natCard c₀) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hc0ne
  · exact h

open scoped Classical in
open IdealArithmetic.Galois.EvenSextic in
/-- **Base case of the `C₃`-equivariance (`blockSign_conj`).** Conjugation by the generator `c₀` (the
internal normalizer action `nAct = normalizerMonoidHom ∘ inclusion`) acts on the block-sign coordinates
exactly as precomposition by the block permutation `τ = hRootHom c₀`:
`blockSignEquiv (c₀ κ c₀⁻¹) = precompAut τ (blockSignEquiv κ)`. -/
private theorem blockSignEquiv_conj_eq_precompAut (C : Subgroup GalP)
    (hincl : (C : Subgroup GalP) ≤ Subgroup.normalizer (↑K : Set GalP)) (c₀ : C)
    (τ : Equiv.Perm (gq.rootSet (gq.comp (X ^ 2)).SplittingField))
    (hτdef : τ = hRootHom gq (c₀ : GalP)) (κ : K) :
    blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg blockSign_generates_all
        ((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀ κ)
      = precompAut τ (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg
          blockSign_generates_all κ) := by
  rw [blockSignEquiv_apply, blockSignEquiv_apply]
  show Multiplicative.ofAdd (blockSign gq gℚ_monic (↑((K.normalizerMonoidHom.comp
      (Subgroup.inclusion hincl)) c₀ κ)))
      = Multiplicative.ofAdd ((blockSign gq gℚ_monic (↑κ)) ∘ ⇑τ.symm)
  congr 1; funext θ
  show blockSign gq gℚ_monic (↑((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀ κ)) θ
      = blockSign gq gℚ_monic (↑κ) (τ.symm θ)
  have hsymm : τ.symm θ = hRoot gq (↑c₀ : GalP)⁻¹ θ := by rw [hτdef]; exact rfl
  have hcoe : (↑((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀ κ) : GalP)
      = ↑c₀ * ↑κ * (↑c₀)⁻¹ := by
    show (↑(K.normalizerMonoidHom (Subgroup.inclusion hincl c₀) κ) : GalP) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  rw [hsymm, hcoe, blockSign_conj]

open scoped Classical in
open IdealArithmetic.Galois.EvenSextic in
/-- **Full `C₃`-equivariance of the block-sign isomorphism.** Powering the base case
(`blockSignEquiv_conj_eq_precompAut`) up through the cyclic identification `fG : C ≃* C₃` via
`conj_pow_trans`: the pair `(blockSignEquiv, fG)` intertwines the conjugation action `nAct` of `C` on
the kernel `K` with the precomposition action `blockAction τ` of `C₃` on `C₂^{roots}`. This is the
`compat` hypothesis feeding `SemidirectProduct.congr`. -/
private theorem blockSignEquiv_intertwines_blockAction (C : Subgroup GalP)
    (hincl : (C : Subgroup GalP) ≤ Subgroup.normalizer (↑K : Set GalP)) (c₀ : C)
    (τ : Equiv.Perm (gq.rootSet (gq.comp (X ^ 2)).SplittingField))
    (hτdef : τ = hRootHom gq (c₀ : GalP)) (hτ3 : τ ^ 3 = 1)
    (fG : C ≃* Multiplicative (ZMod 3)) (hfGc0 : fG c₀ = Multiplicative.ofAdd 1) (c : C) :
    ((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c).trans
        (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg blockSign_generates_all)
      = (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg blockSign_generates_all).trans
          (blockAction τ hτ3 (fG c)) := by
  have base : ∀ κ : K,
      blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg blockSign_generates_all
          ((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀ κ)
        = precompAut τ (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg
            blockSign_generates_all κ) :=
    fun κ => blockSignEquiv_conj_eq_precompAut C hincl c₀ τ hτdef κ
  have hpow : c₀ ^ (Multiplicative.toAdd (fG c)).val = c := by
    have h : fG (c₀ ^ (Multiplicative.toAdd (fG c)).val) = fG c := by
      rw [map_pow, hfGc0, ofAdd_one_pow_toAdd_val]
    exact fG.injective h
  have hnact : (K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c
      = ((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀)
          ^ (Multiplicative.toAdd (fG c)).val := by
    conv_lhs => rw [← hpow]
    rw [map_pow]
  have hblk : blockAction τ hτ3 (fG c)
      = (blockAction τ hτ3 (Multiplicative.ofAdd 1)) ^ (Multiplicative.toAdd (fG c)).val := by
    rw [← map_pow]; congr 1; exact (ofAdd_one_pow_toAdd_val (fG c)).symm
  have hgenb : blockAction τ hτ3 (Multiplicative.ofAdd 1) = precompAut τ :=
    zmodPowHom_gen (precompAut τ) (by rw [← map_pow, hτ3, map_one])
  rw [hnact, hblk, hgenb]
  exact MulEquiv.ext
    (conj_pow_trans _ ((K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)) c₀) (precompAut τ)
      base (Multiplicative.toAdd (fG c)).val)

open scoped Classical in
open IdealArithmetic.Galois.EvenSextic in
/-- **D6-M2 (friendly corollary).** `Gal f` is isomorphic to `A₄ × C₂` (the transitive group `6T6`),
where `C₂ = Multiplicative (ZMod 2)`. Schur–Zassenhaus splits `Gal f ≅ Gal(g(X²))` as `K ⋊ C₃` with
`K = Gal(L/M) ≅ C₂³` the sign-change kernel and `C₃ = Gal g`; the `C₃`-action on the block signs is
the resolvent's block permutation (`blockSign_conj`), and `threeBlockIso` sends `C₂³ ⋊ C₃` to
`A₄ × C₂`. -/
theorem gal_f_mulEquiv :
    Nonempty ((f.map (Int.castRingHom ℚ)).Gal ≃*
      alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) := by
  haveI : Fact ((gq.map (algebraMap ℚ (gq.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp gq (X ^ 2) X_sq_natDegree_ne_zero⟩
  -- Schur–Zassenhaus: split off a complement `C ≅ C₃` of the normal kernel `K` (|K|=8, [G:K]=3).
  obtain ⟨C, hC, hCcard⟩ := exists_complement_card_three
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : IsCyclic C := isCyclic_of_prime_card hCcard
  -- Identify `C ≅ Multiplicative (ZMod 3)` and pick the generator `c₀`.
  let fG : C ≃* Multiplicative (ZMod 3) := (hCcard ▸ zmodCyclicMulEquiv (G := C) inferInstance).symm
  set c₀ : C := fG.symm (Multiplicative.ofAdd 1) with hc0
  have hfGc0 : fG c₀ = Multiplicative.ofAdd 1 := by rw [hc0, MulEquiv.apply_symm_apply]
  have hne : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by
    intro h; have h2 : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h
    exact one_ne_zero h2
  have hc0ne : c₀ ≠ 1 := fun h => hne (by rw [← hfGc0, h, map_one])
  -- The block permutation induced by `c₀` (the `C₃`-symmetry acting on the roots of the resolvent).
  set τ : Equiv.Perm (gq.rootSet (gq.comp (X ^ 2)).SplittingField) :=
    hRootHom gq (c₀ : GalP) with hτdef
  -- `rc` is injective on the complement `C` (`C ∩ K = 1`), so `orderOf τ = orderOf c₀ = 3`.
  have hτ : orderOf τ = 3 := orderOf_blockPerm_eq_three C hC c₀ hc0ne hCcard
  have hτ3 : τ ^ 3 = 1 := by have := pow_orderOf_eq_one τ; rwa [hτ] at this
  -- The internal semidirect-product action of `C` on `K` by conjugation (normalizer action).
  have hincl : (C : Subgroup GalP) ≤ Subgroup.normalizer (↑K : Set GalP) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  let nAct : C →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hincl)
  -- **Full equivariance.** `(blockSignEquiv, fG)` intertwines the conjugation action `nAct` of `C` on
  -- `K` with the precomposition action `blockAction τ` of `C₃` — built from `blockSign_conj` powered up.
  have compat : ∀ c : C, (nAct c).trans (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic
        root_ne_neg blockSign_generates_all)
      = (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg blockSign_generates_all).trans
          (blockAction τ hτ3 (fG c)) :=
    blockSignEquiv_intertwines_blockAction C hincl c₀ τ hτdef hτ3 fG hfGc0
  have hcard : Fintype.card (gq.rootSet (gq.comp (X ^ 2)).SplittingField) = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact card_rootSet_gq
  obtain ⟨abstractIso⟩ := threeBlockIso hcard τ hτ hτ3
  -- Compose: `Gal f ≃ Gal(g(X²)) ≃ K ⋊ C ≃ C₂³ ⋊ C₃ ≃ A₄ × C₂`.
  exact ⟨(galCongr fℚ_eq_gℚ_comp).trans
    ((SemidirectProduct.mulEquivSubgroup hC).symm.trans
      ((SemidirectProduct.congr (blockSignEquiv gq X_sq_natDegree_ne_zero gℚ_monic root_ne_neg
        blockSign_generates_all) fG compat).trans abstractIso))⟩

end IdealArithmetic.Galois.DegSix
