import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.Data.Nat.GCD

/-!
# Conway polynomials

The Conway polynomials `f_{p,n} ∈ 𝔽_p[x]` are standard defining polynomials of the finite fields
`𝔽_{p^n}`. The polynomials of degree `n` over `𝔽_p = ℤ/pℤ` are ordered as follows: the elements of
`𝔽_p` are ordered as `0 < 1 < ⋯ < p - 1`, and `f = ∑ aᵢ xⁱ` precedes `g = ∑ bᵢ xⁱ` if for some `j`,
`aᵢ = bᵢ` for `i > j` and `(-1)^(n-j) a_j < (-1)^(n-j) b_j`; that is, the signed coefficients
`(-1)^k a_{n-k}` are compared lexicographically, from the leading one down. The Conway polynomial
`f_{p,n}` is the first polynomial of degree `n` for this order such that

1. a root of `f_{p,n}` has order `p^n - 1` in `𝔽̄_p`, and
2. for every proper divisor `m` of `n`, `f_{p,m}(x^((p^n-1)/(p^m-1))) ≡ 0 (mod f_{p,n})`, that is,
   the `(p^n-1)/(p^m-1)`-th power of a root of `f_{p,n}` is a root of `f_{p,m}`.

The definition is by strong recursion on `n`. That a polynomial with these properties exists for
every `n ≥ 1` is a theorem: given compatible roots `ηₘ` of the `f_{p,m}` for the proper divisors
`m` of `n`, a primitive element of `𝔽_{p^n}` whose norms to the subfields `𝔽_{p^m}` are the `ηₘ`
exists by the Chinese remainder theorem for non-coprime moduli (as `gcd(p^a - 1, p^b - 1)` is
`p^gcd(a, b) - 1`), and its minimal polynomial has the required properties; a root of `f_{p,n}`
compatible with the `ηₘ` is then found among its Frobenius conjugates, again by the Chinese
remainder theorem.

## Main definitions

* `FiniteField.conwayKey` (LMFDB `field.finite.conway_polynomial`): the key of a polynomial for
  the order on polynomials of degree `n` of the definition.
* `FiniteField.IsConwayCompatible` (LMFDB `field.finite.conway_polynomial`): the conditions on the
  Conway polynomial of degree `n`, given those of the proper divisors of `n`.
* `FiniteField.conwayPolynomial` (LMFDB `field.finite.conway_polynomial`): the Conway polynomial
  `f_{p,n}`.
* `FiniteField.IsConwayRootFamily`: a compatible family of roots of the Conway polynomials.

## Main results

* `Nat.exists_modEq_of_pairwise`: the Chinese remainder theorem for pairwise compatible
  congruences.
* `FiniteField.conwayKey_lt_conwayKey_iff`: comparing keys is the order of the definition.
* `FiniteField.conwayKey_injOn`: the key is injective on polynomials of degree at most `n`.
* `FiniteField.exists_isConwayRootFamily`: the Conway polynomials of degree at most `n` exist and
  have compatible roots.
* `FiniteField.isConwayCompatible_conwayPolynomial`: **Conway polynomials exist**: `f_{p,n}` has
  the defining properties for every `n ≥ 1`.
* `FiniteField.minimalFor_conwayPolynomial`, `FiniteField.eq_conwayPolynomial_of_minimalFor`:
  `f_{p,n}` is the first polynomial with these properties, and the only one.
* `FiniteField.monic_conwayPolynomial`, `FiniteField.irreducible_conwayPolynomial`,
  `FiniteField.conwayPolynomial_eq_minpoly`: `f_{p,n}` is monic and irreducible, the minimal
  polynomial of each of its roots.
-/

open Algebra Polynomial

namespace Nat

variable {ι : Type*} {s : Finset ι} {n r : ι → ℕ} {a b c : ℕ} (hn : ∀ i ∈ s, n i ≠ 0)

lemma gcd_lcm_dvd_lcm_gcd (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a.lcm b).gcd c ∣ (a.gcd c).lcm (b.gcd c) := by
  have hac : a.gcd c ≠ 0 := gcd_ne_zero_right hc
  have hbc : b.gcd c ≠ 0 := gcd_ne_zero_right hc
  rw [← factorization_le_iff_dvd (gcd_ne_zero_right hc) (lcm_ne_zero hac hbc),
    factorization_gcd (lcm_ne_zero ha hb) hc, factorization_lcm ha hb, factorization_lcm hac hbc,
    factorization_gcd ha hc, factorization_gcd hb hc]
  intro q
  simp only [Finsupp.inf_apply, Finsupp.sup_apply]
  omega

lemma gcd_mem_properDivisors (ha : a ∈ c.properDivisors) : a.gcd b ∈ c.properDivisors := by
  rcases mem_properDivisors.mp ha with ⟨hac, hlt⟩
  exact mem_properDivisors.mpr
    ⟨(gcd_dvd_left a b).trans hac, (gcd_le_left b (pos_of_mem_properDivisors ha)).trans_lt hlt⟩

include hn in
lemma finset_lcm_gcd_dvd (hc : c ≠ 0) : (s.lcm n).gcd c ∣ s.lcm fun i ↦ (n i).gcd c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s _ ih =>
    have hn' : ∀ i ∈ s, n i ≠ 0 := fun i hi ↦ hn i (Finset.mem_insert_of_mem hi)
    rw [Finset.lcm_insert, Finset.lcm_insert]
    exact (gcd_lcm_dvd_lcm_gcd (hn j (Finset.mem_insert_self j s))
      (Finset.lcm_ne_zero_iff.mpr hn') hc).trans (lcm_dvd_lcm dvd_rfl (ih hn'))

lemma modEq_finset_lcm (h : ∀ i ∈ s, a ≡ b [MOD n i]) : a ≡ b [MOD s.lcm n] :=
  modEq_iff_dvd.mpr <| Int.natCast_dvd.mpr <| Finset.lcm_dvd fun i hi ↦
    Int.natCast_dvd.mp <| modEq_iff_dvd.mp <| h i hi

include hn in
variable (s n r) in
/-- **The Chinese remainder theorem for pairwise compatible congruences**: congruences
`x ≡ rᵢ (mod nᵢ)`, `i ∈ s`, with `rᵢ ≡ rⱼ (mod gcd(nᵢ, nⱼ))` for all `i, j ∈ s`, have a common
solution. -/
lemma exists_modEq_of_pairwise (h : ∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD (n i).gcd (n j)]) :
    ∃ x, ∀ i ∈ s, x ≡ r i [MOD n i] := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i₀ s _ ih =>
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert i₀ s := Finset.mem_insert_of_mem hi
    have hi₀ : i₀ ∈ insert i₀ s := Finset.mem_insert_self i₀ s
    have hn' : ∀ i ∈ s, n i ≠ 0 := fun i hi ↦ hn i (hs i hi)
    rcases ih hn' fun i hi j hj ↦ h i (hs i hi) j (hs j hj) with ⟨x₀, hx₀⟩
    have hcomp : x₀ ≡ r i₀ [MOD (s.lcm n).gcd (n i₀)] :=
      (modEq_finset_lcm fun j hj ↦ ((hx₀ j hj).of_dvd (gcd_dvd_left _ _)).trans
        (h j (hs j hj) i₀ hi₀)).of_dvd (finset_lcm_gcd_dvd hn' (hn i₀ hi₀))
    let k : { k // k ≡ x₀ [MOD s.lcm n] ∧ k ≡ r i₀ [MOD n i₀] } := chineseRemainder' hcomp
    refine ⟨k, fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact k.2.2
    · exact (k.2.1.of_dvd (Finset.dvd_lcm hi)).trans (hx₀ i hi)

lemma pow_modEq_pow_iff {p d : ℕ} (hp : 1 < p) :
    p ^ a ≡ p ^ b [MOD p ^ d - 1] ↔ a ≡ b [MOD d] := by
  have ha : p ^ a - 1 + 1 = p ^ a := Nat.sub_add_cancel (one_le_pow _ _ (by omega))
  have hb : p ^ b - 1 + 1 = p ^ b := Nat.sub_add_cancel (one_le_pow _ _ (by omega))
  have hsub : p ^ a ≡ p ^ b [MOD p ^ d - 1] ↔ p ^ a - 1 ≡ p ^ b - 1 [MOD p ^ d - 1] :=
    ⟨fun h ↦ ModEq.add_right_cancel' 1 (by rwa [ha, hb]),
      fun h ↦ by simpa only [ha, hb] using h.add_right 1⟩
  have h3 : 1 ≤ p ^ (a % d) := one_le_pow _ _ (by omega)
  have h4 : 1 ≤ p ^ (b % d) := one_le_pow _ _ (by omega)
  rw [hsub, ModEq, ModEq, pow_sub_one_mod_pow_sub_one, pow_sub_one_mod_pow_sub_one]
  exact ⟨fun h ↦ Nat.pow_right_injective hp (by omega : p ^ (a % d) = p ^ (b % d)),
    fun h ↦ by rw [h]⟩

end Nat

namespace FiniteField

variable (p : ℕ) [hp : Fact p.Prime] (c : ℕ → (ZMod p)[X]) (n : ℕ) (f : (ZMod p)[X])

local notation "K" => AlgebraicClosure (ZMod p)

/-- The key of a polynomial `f = ∑ aᵢ xⁱ` over `𝔽_p` for the order on polynomials of degree `n`
defining the Conway polynomials (LMFDB `field.finite.conway_polynomial`): the signed coefficients
`(-1)^k a_{n-k}`, for `k = 0, …, n`, each read as an integer in `{0, …, p - 1}`, to be compared
lexicographically. For polynomials of degree `n` this is the order of the LMFDB knowl
(`FiniteField.conwayKey_lt_conwayKey_iff`), and the key determines the polynomial
(`FiniteField.conwayKey_injOn`). -/
def conwayKey : Lex (Fin (n + 1) → ℕ) :=
  toLex fun k ↦ ((-1) ^ (k : ℕ) * f.coeff (n - k)).val

/-- The conditions on the Conway polynomial of degree `n` (LMFDB `field.finite.conway_polynomial`),
given the Conway polynomials `c m` of degree `m` for the proper divisors `m` of `n`: `f` has degree
`n`, a root of `f` has order `p ^ n - 1` in `𝔽̄_p`, and `f` divides `(c m)(x^((p^n-1)/(p^m-1)))`
for every proper divisor `m` of `n`. The LMFDB knowl asks the last condition for every positive
divisor `m` of `n`; for `m = n`, where `f_{p,n}` is the polynomial `f` being tested, it reads
`f(x) ≡ 0 (mod f)` and holds for every `f`. -/
structure IsConwayCompatible : Prop where
  /-- The polynomial has degree `n`. -/
  natDegree_eq : f.natDegree = n
  /-- A root of the polynomial has order `p ^ n - 1` in `𝔽̄_p`. -/
  exists_root : ∃ x : K, aeval x f = 0 ∧ orderOf x = p ^ n - 1
  /-- The polynomial divides `(c m)(x^((p^n-1)/(p^m-1)))` for the proper divisors `m` of `n`. -/
  dvd_comp (m : ℕ) : m ∈ n.properDivisors → f ∣ (c m).comp (X ^ ((p ^ n - 1) / (p ^ m - 1)))

open scoped Classical in
/-- The **Conway polynomial** `f_{p,n}` (LMFDB `field.finite.conway_polynomial`): the first
polynomial of degree `n` over `𝔽_p`, for the order of `FiniteField.conwayKey`, such that a root has
order `p ^ n - 1` in `𝔽̄_p` and for every proper divisor `m` of `n`,
`f_{p,m}(x^((p^n-1)/(p^m-1))) ≡ 0 (mod f_{p,n})`, defined by strong recursion on `n`. It exists for
every `n ≥ 1` (`FiniteField.isConwayCompatible_conwayPolynomial`); the value `0` for `n = 0`, where
the definition is meaningless, is a junk value. -/
noncomputable def conwayPolynomial (n : ℕ) : (ZMod p)[X] :=
  if h : {g | IsConwayCompatible p (fun m ↦ if _ : m < n then conwayPolynomial m else 0) n
    g}.Nonempty then Function.argminOn (conwayKey p n) _ h else 0
termination_by n

variable {p c n f} {m a b : ℕ} {x : AlgebraicClosure (ZMod p)} {η : ℕ → AlgebraicClosure (ZMod p)}
  (hm : 0 < m) (hn : 0 < n) (hηo : ∀ m ∈ n.properDivisors, orderOf (η m) = p ^ m - 1)
  (hηc : ∀ m ∈ n.properDivisors, ∀ m' ∈ n.properDivisors, m' ∣ m →
    η m ^ ((p ^ m - 1) / (p ^ m' - 1)) = η m')

include hn in
lemma pow_sub_one_pos : 0 < p ^ n - 1 :=
  Nat.sub_pos_of_lt <| one_lt_pow₀ hp.out.one_lt hn.ne'

omit hp in
lemma pow_sub_one_dvd_of_mem_properDivisors (h : m ∈ n.properDivisors) : p ^ m - 1 ∣ p ^ n - 1 :=
  Nat.pow_sub_one_dvd_pow_sub_one _ (Nat.mem_properDivisors.mp h).1

lemma pow_eq_pow_iff_of_isPrimitiveRoot {ζ : K} {k : ℕ} (h : IsPrimitiveRoot ζ k) (hk : 0 < k) :
    ζ ^ a = ζ ^ b ↔ a ≡ b [MOD k] := by
  rw [(h.isOfFinOrder hk.ne').pow_eq_pow_iff_modEq, ← h.eq_orderOf]

include hm in
lemma pow_pow_eq_pow_pow_iff (hx : orderOf x = p ^ m - 1) :
    x ^ p ^ a = x ^ p ^ b ↔ a ≡ b [MOD m] := by
  rw [(orderOf_pos_iff.mp (hx ▸ pow_sub_one_pos hm)).pow_eq_pow_iff_modEq, hx,
    Nat.pow_modEq_pow_iff hp.out.one_lt]

variable (f x) in
lemma aeval_pow_pow (i : ℕ) : aeval (x ^ p ^ i) f = aeval x f ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, ← expand_aeval, ZMod.expand_card, map_pow, ih, ← pow_mul]

include hm in
lemma exists_eq_pow_pow (hf : f.natDegree = m) (hx : aeval x f = 0) (hxo : orderOf x = p ^ m - 1)
    {y : K} (hy : aeval y f = 0) : ∃ j < m, x ^ p ^ j = y := by
  classical
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt (hf ▸ hm)
  have hinj : Set.InjOn (fun j ↦ x ^ p ^ j) (Finset.range m) := fun i hi j hj h ↦
    ((pow_pow_eq_pow_pow_iff hm hxo).mp h).eq_of_lt_of_lt (by simpa using hi) (by simpa using hj)
  have hsub : (Finset.range m).image (fun j ↦ x ^ p ^ j) ⊆ (f.aroots K).toFinset := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, -, rfl⟩
    simp [hf0, aeval_pow_pow, hx, hp.out.ne_zero]
  have hcard : (f.aroots K).toFinset.card ≤ ((Finset.range m).image fun j ↦ x ^ p ^ j).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← hf]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
  have hy' : y ∈ ((Finset.range m).image fun j ↦ x ^ p ^ j) := by
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
    simp [hf0, hy]
  simpa using hy'

include hn in
lemma natDegree_minpoly_of_orderOf_eq (hx : orderOf x = p ^ n - 1) :
    (minpoly (ZMod p) x).natDegree = n := by
  have hcop : p.Coprime (p ^ n - 1) := Nat.coprime_pow_sub_one p n hp.out.one_lt hn.ne'
  have hdvd : minpoly (ZMod p) x ∣ cyclotomic (p ^ n - 1) (ZMod p) := by
    refine minpoly.dvd _ _ ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (hx ▸ IsPrimitiveRoot.orderOf x).isRoot_cyclotomic (pow_sub_one_pos hn)
  rw [natDegree_of_dvd_cyclotomic_of_irreducible (f := 1) (by simp) hcop hdvd
    (minpoly.irreducible (IsIntegral.isIntegral x))]
  have key (k : ℕ) : ZMod.unitOfCoprime (p ^ 1) (hcop.pow_left 1) ^ k = 1 ↔ n ∣ k := by
    have h : p ^ k ≡ p ^ 0 [MOD p ^ n - 1] ↔ k ≡ 0 [MOD n] := Nat.pow_modEq_pow_iff hp.out.one_lt
    rw [pow_zero, Nat.modEq_zero_iff_dvd] at h
    rw [← h, Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
      pow_one, ← Nat.cast_pow, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  rw [orderOf_eq_iff hn]
  exact ⟨(key n).mpr dvd_rfl, fun k hk hk0 h ↦
    (Nat.eq_zero_of_dvd_of_lt ((key k).mp h) hk).not_gt hk0⟩

include hn hηo hηc in
lemma exists_orderOf_eq_pow_eq : ∃ ξ : K, orderOf ξ = p ^ n - 1 ∧
    ∀ m ∈ n.properDivisors, ξ ^ ((p ^ n - 1) / (p ^ m - 1)) = η m := by
  classical
  have : NeZero ((p ^ n - 1 : ℕ) : ZMod p) :=
    ⟨by rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
        exact hp.out.coprime_iff_not_dvd.mp (Nat.coprime_pow_sub_one p n hp.out.one_lt hn.ne')⟩
  rcases HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (p ^ n - 1) with ⟨γ, hγ⟩
  -- `γ ^ ((p ^ n - 1) / (p ^ m - 1))` generates the `(p ^ m - 1)`-th roots of unity, and `η m` is
  -- its `c m`-th power.
  have hg (m : ℕ) (hm : m ∈ n.properDivisors) :
      IsPrimitiveRoot (γ ^ ((p ^ n - 1) / (p ^ m - 1))) (p ^ m - 1) :=
    hγ.pow (pow_sub_one_pos hn) (Nat.div_mul_cancel (pow_sub_one_dvd_of_mem_properDivisors hm)).symm
  have hc (m : ℕ) (hm : m ∈ n.properDivisors) :
      ∃ c, (γ ^ ((p ^ n - 1) / (p ^ m - 1))) ^ c = η m := by
    have : NeZero (p ^ m - 1) := ⟨(pow_sub_one_pos (Nat.pos_of_mem_properDivisors hm)).ne'⟩
    rcases (hg m hm).eq_pow_of_pow_eq_one ((hηo m hm) ▸ pow_orderOf_eq_one (η m)) with ⟨c, -, h⟩
    exact ⟨c, h⟩
  choose! c hc using hc
  -- The exponents agree on the common subfields, so they have a common lift `k`.
  have hpair : ∀ m ∈ n.properDivisors, ∀ m' ∈ n.properDivisors,
      c m ≡ c m' [MOD (p ^ m - 1).gcd (p ^ m' - 1)] := by
    intro m hm m' hm'
    rw [Nat.pow_sub_one_gcd_pow_sub_one]
    have hgD : m.gcd m' ∈ n.properDivisors := Nat.gcd_mem_properDivisors hm
    have hl : m.gcd m' ∣ m := Nat.gcd_dvd_left m m'
    have hr : m.gcd m' ∣ m' := Nat.gcd_dvd_right m m'
    have h1 : η m ^ ((p ^ m - 1) / (p ^ m.gcd m' - 1)) = η (m.gcd m') := hηc m hm _ hgD hl
    have h2 : η m' ^ ((p ^ m' - 1) / (p ^ m.gcd m' - 1)) = η (m.gcd m') := hηc m' hm' _ hgD hr
    rw [← hc m hm, ← pow_mul, ← pow_mul, mul_left_comm,
      Nat.div_mul_div (pow_sub_one_dvd_of_mem_properDivisors hm)
        (Nat.pow_sub_one_dvd_pow_sub_one _ hl), mul_comm (c m), pow_mul] at h1
    rw [← hc m' hm', ← pow_mul, ← pow_mul, mul_left_comm,
      Nat.div_mul_div (pow_sub_one_dvd_of_mem_properDivisors hm')
        (Nat.pow_sub_one_dvd_pow_sub_one _ hr), mul_comm (c m'), pow_mul] at h2
    exact (pow_eq_pow_iff_of_isPrimitiveRoot (hg _ hgD)
      (pow_sub_one_pos (Nat.pos_of_mem_properDivisors hgD))).mp (h1.trans h2.symm)
  rcases Nat.exists_modEq_of_pairwise n.properDivisors (fun m ↦ p ^ m - 1) c
    (fun m hm ↦ (pow_sub_one_pos (Nat.pos_of_mem_properDivisors hm)).ne') hpair with ⟨k, hk⟩
  -- The lift `k` is prime to the `p ^ m - 1`, and may be replaced by one prime to `p ^ n - 1`.
  have hcop (m : ℕ) (hm : m ∈ n.properDivisors) : k.Coprime (p ^ m - 1) := by
    have hprim : IsPrimitiveRoot ((γ ^ ((p ^ n - 1) / (p ^ m - 1))) ^ c m) (p ^ m - 1) := by
      rw [hc m hm, ← hηo m hm]
      exact IsPrimitiveRoot.orderOf (η m)
    have h : (c m).Coprime (p ^ m - 1) :=
      ((hg m hm).pow_iff_coprime (pow_sub_one_pos (Nat.pos_of_mem_properDivisors hm)) _).mp hprim
    rwa [Nat.Coprime, ← (hk m hm).gcd_eq] at h
  have hL : n.properDivisors.lcm (fun m ↦ p ^ m - 1) ∣ p ^ n - 1 :=
    Finset.lcm_dvd fun _ hm ↦ pow_sub_one_dvd_of_mem_properDivisors hm
  have hkL : k.Coprime (n.properDivisors.lcm fun m ↦ p ^ m - 1) :=
    (Nat.coprime_prod_right_iff.mpr hcop).coprime_dvd_right (Finset.lcm_dvd_prod _ _)
  have : NeZero (p ^ n - 1) := ⟨(pow_sub_one_pos hn).ne'⟩
  rcases ZMod.unitsMap_surjective hL (ZMod.unitOfCoprime k hkL) with ⟨v, hv⟩
  have hvk : (v : ZMod (p ^ n - 1)).val ≡ k [MOD n.properDivisors.lcm fun m ↦ p ^ m - 1] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ← ZMod.unitsMap_val hL, hv,
      ZMod.coe_unitOfCoprime]
  refine ⟨γ ^ (v : ZMod (p ^ n - 1)).val,
    (hγ.pow_of_coprime _ (ZMod.val_coe_unit_coprime v)).eq_orderOf.symm, fun m hm ↦ ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, ← hc m hm]
  exact (pow_eq_pow_iff_of_isPrimitiveRoot (hg m hm)
    (pow_sub_one_pos (Nat.pos_of_mem_properDivisors hm))).mpr
    ((hvk.of_dvd (Finset.dvd_lcm hm)).trans (hk m hm))

include hn hηo hηc in
lemma exists_aeval_eq_zero_pow_eq (hc : ∀ m ∈ n.properDivisors, (c m).natDegree = m)
    (hηr : ∀ m ∈ n.properDivisors, aeval (η m) (c m) = 0)
    (hf : ∀ m ∈ n.properDivisors, f ∣ (c m).comp (X ^ ((p ^ n - 1) / (p ^ m - 1))))
    (hx : aeval x f = 0) (hxo : orderOf x = p ^ n - 1) : ∃ y : K, aeval y f = 0 ∧
      orderOf y = p ^ n - 1 ∧ ∀ m ∈ n.properDivisors, y ^ ((p ^ n - 1) / (p ^ m - 1)) = η m := by
  classical
  -- The power `x ^ ((p ^ n - 1) / (p ^ m - 1))` is a root of `c m`, a Frobenius conjugate of `η m`.
  have hj (m : ℕ) (hm : m ∈ n.properDivisors) :
      ∃ j < m, η m ^ p ^ j = x ^ ((p ^ n - 1) / (p ^ m - 1)) := by
    refine exists_eq_pow_pow (Nat.pos_of_mem_properDivisors hm) (hc m hm) (hηr m hm) (hηo m hm) ?_
    have h : aeval x ((c m).comp (X ^ ((p ^ n - 1) / (p ^ m - 1)))) = 0 :=
      aeval_eq_zero_of_dvd_aeval_eq_zero (hf m hm) hx
    rwa [aeval_comp, aeval_X_pow] at h
  choose! j hjl hj using hj
  -- The Frobenius twists agree on the common subfields, so they have a common lift `i`.
  have hpair : ∀ m ∈ n.properDivisors, ∀ m' ∈ n.properDivisors,
      m - j m ≡ m' - j m' [MOD m.gcd m'] := by
    intro m hm m' hm'
    have hgD : m.gcd m' ∈ n.properDivisors := Nat.gcd_mem_properDivisors hm
    have hl : m.gcd m' ∣ m := Nat.gcd_dvd_left m m'
    have hr : m.gcd m' ∣ m' := Nat.gcd_dvd_right m m'
    have e (k : ℕ) (hk : k ∈ n.properDivisors) (hgk : m.gcd m' ∣ k) :
        η (m.gcd m') ^ p ^ j k = x ^ ((p ^ n - 1) / (p ^ m.gcd m' - 1)) := by
      rw [← hηc k hk _ hgD hgk, pow_right_comm, hj k hk, ← pow_mul,
        Nat.div_mul_div (pow_sub_one_dvd_of_mem_properDivisors hk)
          (Nat.pow_sub_one_dvd_pow_sub_one _ hgk)]
    have hjj : j m ≡ j m' [MOD m.gcd m'] :=
      (pow_pow_eq_pow_pow_iff (Nat.pos_of_mem_properDivisors hgD) (hηo _ hgD)).mp
        ((e m hm hl).trans (e m' hm' hr).symm)
    refine hjj.add_right_cancel ?_
    rw [Nat.sub_add_cancel (hjl m hm).le, Nat.sub_add_cancel (hjl m' hm').le]
    exact (Nat.modEq_zero_iff_dvd.mpr hl).trans (Nat.modEq_zero_iff_dvd.mpr hr).symm
  rcases Nat.exists_modEq_of_pairwise n.properDivisors id (fun m ↦ m - j m)
    (fun m hm ↦ (Nat.pos_of_mem_properDivisors hm).ne') hpair with ⟨i, hi⟩
  refine ⟨x ^ p ^ i, ?_, ?_, fun m hm ↦ ?_⟩
  · rw [aeval_pow_pow, hx, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  · have hcop : (orderOf x).Coprime (p ^ i) :=
      hxo ▸ ((Nat.coprime_pow_sub_one p n hp.out.one_lt hn.ne').pow_left i).symm
    rw [hcop.orderOf_pow, hxo]
  · rw [pow_right_comm, ← hj m hm, ← pow_mul, ← pow_add]
    refine ((pow_pow_eq_pow_pow_iff (b := 0) (Nat.pos_of_mem_properDivisors hm)
      (hηo m hm)).mpr ?_).trans (by simp)
    have h : j m + i ≡ j m + (m - j m) [MOD m] := (hi m hm).add_left (j m)
    rw [Nat.add_sub_cancel' (hjl m hm).le] at h
    exact h.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl)

variable (hf : IsConwayCompatible p (conwayPolynomial p) n f)

lemma isConwayCompatible_congr {c' : ℕ → (ZMod p)[X]} (h : ∀ m ∈ n.properDivisors, c m = c' m) :
    IsConwayCompatible p c n f ↔ IsConwayCompatible p c' n f :=
  ⟨fun hc ↦ ⟨hc.natDegree_eq, hc.exists_root, fun m hm ↦ h m hm ▸ hc.dvd_comp m hm⟩,
    fun hc ↦ ⟨hc.natDegree_eq, hc.exists_root, fun m hm ↦ (h m hm).symm ▸ hc.dvd_comp m hm⟩⟩

variable (n f) in
lemma isConwayCompatible_dite_iff :
    IsConwayCompatible p (fun m ↦ if _ : m < n then conwayPolynomial p m else 0) n f ↔
      IsConwayCompatible p (conwayPolynomial p) n f :=
  isConwayCompatible_congr fun _ hm ↦ dite_eq_left (Nat.mem_properDivisors.mp hm).2

include hf in
lemma nonempty_setOf_isConwayCompatible :
    {g | IsConwayCompatible p (fun m ↦ if _ : m < n then conwayPolynomial p m else 0) n
      g}.Nonempty :=
  ⟨f, (isConwayCompatible_dite_iff n f).mpr hf⟩

include hf in
lemma isConwayCompatible_conwayPolynomial_of_isConwayCompatible :
    IsConwayCompatible p (conwayPolynomial p) n (conwayPolynomial p n) := by
  rw [conwayPolynomial, dite_eq_left (nonempty_setOf_isConwayCompatible hf)]
  exact (isConwayCompatible_dite_iff n _).mp (Function.argminOn_mem _ _ _).out

include hf in
lemma conwayKey_conwayPolynomial_le : conwayKey p n (conwayPolynomial p n) ≤ conwayKey p n f := by
  rw [conwayPolynomial, dite_eq_left (nonempty_setOf_isConwayCompatible hf)]
  exact Function.argminOn_le _ _ ((isConwayCompatible_dite_iff n f).mpr hf)

lemma val_neg_one_pow_mul_inj {k : ℕ} {u v : ZMod p} :
    ((-1) ^ k * u).val = ((-1) ^ k * v).val ↔ u = v :=
  (ZMod.val_injective p).eq_iff.trans (mul_right_inj' (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))

/-- **Comparing keys is the order of the LMFDB knowl** on polynomials of degree `n`: `f = ∑ aᵢ xⁱ`
precedes `g = ∑ bᵢ xⁱ` if for some `j ≤ n`, `aᵢ = bᵢ` for `j < i ≤ n` and
`(-1)^(n-j) a_j < (-1)^(n-j) b_j`, as integers in `{0, …, p - 1}`. -/
lemma conwayKey_lt_conwayKey_iff {g : (ZMod p)[X]} : conwayKey p n f < conwayKey p n g ↔
    ∃ j ≤ n, (∀ i, j < i → i ≤ n → f.coeff i = g.coeff i) ∧
      ((-1) ^ (n - j) * f.coeff j).val < ((-1) ^ (n - j) * g.coeff j).val := by
  constructor
  · rintro ⟨k, hk, hlt⟩
    refine ⟨n - k, Nat.sub_le n k, fun i hi hin ↦ ?_, ?_⟩
    · exact val_neg_one_pow_mul_inj.mp <| by
        simpa only [conwayKey, Pi.toLex_apply, Nat.sub_sub_self hin] using
          hk ⟨n - i, by omega⟩ (Fin.lt_def.mpr (by simp; omega))
    · simpa [conwayKey, Nat.sub_sub_self (Nat.lt_succ_iff.mp k.2)] using hlt
  · rintro ⟨j, hj, heq, hlt⟩
    refine ⟨⟨n - j, by omega⟩, fun k hk ↦ ?_, ?_⟩
    · have hk' : (k : ℕ) < n - j := hk
      simp only [conwayKey, Pi.toLex_apply]
      rw [heq (n - k) (by omega) (Nat.sub_le n k)]
    · simpa [conwayKey, Nat.sub_sub_self hj] using hlt

variable (p n) in
/-- **The key determines a polynomial of degree at most `n`.** -/
lemma conwayKey_injOn : Set.InjOn (conwayKey p n) {f | f.natDegree ≤ n} := by
  intro f (hf : f.natDegree ≤ n) g (hg : g.natDegree ≤ n) h
  ext i
  rcases le_or_gt i n with hi | hi
  · exact val_neg_one_pow_mul_inj.mp <| by
      simpa only [Nat.sub_sub_self hi] using congrFun (toLex.injective h) ⟨n - i, by omega⟩
  · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hi),
      coeff_eq_zero_of_natDegree_lt (hg.trans_lt hi)]

variable (p n η) in
/-- A **compatible family of roots of the Conway polynomials** of degree at most `n`: for
`1 ≤ d ≤ n`, the Conway polynomial `f_{p,d}` has the defining properties, `η d` is a root of it of
order `p ^ d - 1`, and `η d ^ ((p^d-1)/(p^d'-1)) = η d'` for `d' ∣ d`. Such families exist
(`FiniteField.exists_isConwayRootFamily`), which is how the existence of the Conway polynomials is
proved. -/
structure IsConwayRootFamily : Prop where
  /-- The Conway polynomials of degree at most `n` have the defining properties. -/
  isConwayCompatible (d : ℕ) : d ∈ Finset.Icc 1 n →
    IsConwayCompatible p (conwayPolynomial p) d (conwayPolynomial p d)
  /-- `η d` is a root of `f_{p,d}`. -/
  aeval_eq_zero (d : ℕ) : d ∈ Finset.Icc 1 n → aeval (η d) (conwayPolynomial p d) = 0
  /-- `η d` has order `p ^ d - 1`. -/
  orderOf_eq (d : ℕ) : d ∈ Finset.Icc 1 n → orderOf (η d) = p ^ d - 1
  /-- The roots are compatible along the norms. -/
  pow_eq (d : ℕ) : d ∈ Finset.Icc 1 n → ∀ d' ∈ Finset.Icc 1 n, d' ∣ d →
    η d ^ ((p ^ d - 1) / (p ^ d' - 1)) = η d'

variable (p n) in
/-- **The Conway polynomials of degree at most `n` exist and have compatible roots**, by induction
on `n`: a primitive element of `𝔽_{p^n}` with prescribed norms to the proper subfields exists by the
Chinese remainder theorem, and its minimal polynomial has the defining properties of `f_{p,n}`;
a root of `f_{p,n}` compatible with the given roots is one of its Frobenius conjugates. -/
lemma exists_isConwayRootFamily : ∃ η : ℕ → K, IsConwayRootFamily p n η := by
  induction n with
  | zero => exact ⟨fun _ ↦ 0, ⟨by simp, by simp, by simp, by simp⟩⟩
  | succ n ih =>
    rcases ih with ⟨η, hη⟩
    have hn : 0 < n + 1 := n.succ_pos
    have hD (m : ℕ) (hm : m ∈ (n + 1).properDivisors) : m ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_properDivisors hm,
        Nat.lt_succ_iff.mp (Nat.mem_properDivisors.mp hm).2⟩
    have hηo : ∀ m ∈ (n + 1).properDivisors, orderOf (η m) = p ^ m - 1 :=
      fun m hm ↦ hη.orderOf_eq m (hD m hm)
    have hηc : ∀ m ∈ (n + 1).properDivisors, ∀ m' ∈ (n + 1).properDivisors, m' ∣ m →
        η m ^ ((p ^ m - 1) / (p ^ m' - 1)) = η m' :=
      fun m hm m' hm' h ↦ hη.pow_eq m (hD m hm) m' (hD m' hm') h
    rcases exists_orderOf_eq_pow_eq hn hηo hηc with ⟨ξ, hξo, hξ⟩
    have hF : IsConwayCompatible p (conwayPolynomial p) (n + 1) (minpoly (ZMod p) ξ) :=
      ⟨natDegree_minpoly_of_orderOf_eq hn hξo, ⟨ξ, minpoly.aeval _ _, hξo⟩,
        fun m hm ↦ minpoly.dvd _ _ (by
          rw [aeval_comp, aeval_X_pow, hξ m hm]
          exact hη.aeval_eq_zero m (hD m hm))⟩
    have hC : IsConwayCompatible p (conwayPolynomial p) (n + 1) (conwayPolynomial p (n + 1)) :=
      isConwayCompatible_conwayPolynomial_of_isConwayCompatible hF
    rcases hC.exists_root with ⟨η₀, hη₀, hη₀o⟩
    rcases exists_aeval_eq_zero_pow_eq hn hηo hηc
      (fun m hm ↦ (hη.isConwayCompatible m (hD m hm)).natDegree_eq)
      (fun m hm ↦ hη.aeval_eq_zero m (hD m hm)) hC.dvd_comp hη₀ hη₀o with ⟨y, hy, hyo, hyc⟩
    have hle (d : ℕ) (hd : d ∈ Finset.Icc 1 (n + 1)) (hd' : d ≠ n + 1) : d ∈ Finset.Icc 1 n := by
      rw [Finset.mem_Icc] at hd ⊢
      omega
    refine ⟨Function.update η (n + 1) y, ⟨fun d hd ↦ ?_, fun d hd ↦ ?_, fun d hd ↦ ?_,
      fun d hd d' hd' hdd' ↦ ?_⟩⟩
    · rcases eq_or_ne d (n + 1) with rfl | hdn
      · exact hC
      · exact hη.isConwayCompatible d (hle d hd hdn)
    · rcases eq_or_ne d (n + 1) with rfl | hdn
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hdn]
        exact hη.aeval_eq_zero d (hle d hd hdn)
    · rcases eq_or_ne d (n + 1) with rfl | hdn
      · rwa [Function.update_self]
      · rw [Function.update_of_ne hdn]
        exact hη.orderOf_eq d (hle d hd hdn)
    · rcases eq_or_ne d (n + 1) with rfl | hdn
      · rcases eq_or_ne d' (n + 1) with rfl | hdn'
        · rw [Function.update_self, Nat.div_self (pow_sub_one_pos hn), pow_one]
        · rw [Function.update_self, Function.update_of_ne hdn']
          exact hyc d' (Nat.mem_properDivisors.mpr ⟨hdd', (Finset.mem_Icc.mp hd').2.lt_of_ne hdn'⟩)
      · have hdl : d ∈ Finset.Icc 1 n := hle d hd hdn
        have hdn' : d' ≠ n + 1 := by
          have h1 : d' ≤ d := Nat.le_of_dvd (Finset.mem_Icc.mp hd).1 hdd'
          have h2 : d ≤ n := (Finset.mem_Icc.mp hdl).2
          omega
        rw [Function.update_of_ne hdn, Function.update_of_ne hdn']
        exact hη.pow_eq d hdl d' (hle d' hd' hdn') hdd'

/-- **The Conway polynomials are the only first polynomials with their defining properties**: a
polynomial minimal for the key among those with the properties of the Conway polynomial of degree
`n` is the Conway polynomial. -/
lemma eq_conwayPolynomial_of_minimalFor
    (h : MinimalFor (IsConwayCompatible p (conwayPolynomial p) n) (conwayKey p n) f) :
    f = conwayPolynomial p n := by
  have hC : IsConwayCompatible p (conwayPolynomial p) n (conwayPolynomial p n) :=
    isConwayCompatible_conwayPolynomial_of_isConwayCompatible h.1
  have hle : conwayKey p n (conwayPolynomial p n) ≤ conwayKey p n f :=
    conwayKey_conwayPolynomial_le h.1
  exact conwayKey_injOn p n h.1.natDegree_eq.le hC.natDegree_eq.le (le_antisymm (h.2 hC hle) hle)

include hn

variable (p)

/-- **Conway polynomials exist**: for `n ≥ 1`, the Conway polynomial `f_{p,n}` has degree `n`, a
root of order `p ^ n - 1` in `𝔽̄_p`, and divides `f_{p,m}(x^((p^n-1)/(p^m-1)))` for every proper
divisor `m` of `n`. -/
lemma isConwayCompatible_conwayPolynomial :
    IsConwayCompatible p (conwayPolynomial p) n (conwayPolynomial p n) :=
  (exists_isConwayRootFamily p n).elim fun _ hη ↦
    hη.isConwayCompatible n (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)

/-- **The Conway polynomial is the first polynomial with its defining properties**, for the key
`FiniteField.conwayKey`. -/
lemma minimalFor_conwayPolynomial :
    MinimalFor (IsConwayCompatible p (conwayPolynomial p) n) (conwayKey p n)
      (conwayPolynomial p n) :=
  ⟨isConwayCompatible_conwayPolynomial p hn, fun _ hg _ ↦ conwayKey_conwayPolynomial_le hg⟩

/-- **The Conway polynomial is monic**, as the first polynomial among the multiples of a polynomial
by the nonzero constants. -/
lemma monic_conwayPolynomial : (conwayPolynomial p n).Monic := by
  have hC : IsConwayCompatible p (conwayPolynomial p) n (conwayPolynomial p n) :=
    isConwayCompatible_conwayPolynomial p hn
  have ha : (conwayPolynomial p n).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr <| ne_zero_of_natDegree_gt <| hC.natDegree_eq ▸ hn
  have ha' : (conwayPolynomial p n).leadingCoeff⁻¹ ≠ 0 := inv_ne_zero ha
  have hg : IsConwayCompatible p (conwayPolynomial p) n
      (C (conwayPolynomial p n).leadingCoeff⁻¹ * conwayPolynomial p n) := by
    rcases hC.exists_root with ⟨x, hx, hxo⟩
    exact ⟨by rw [natDegree_C_mul ha', hC.natDegree_eq], ⟨x, by simp [hx], hxo⟩,
      fun m hm ↦ (C_mul_dvd ha').mpr (hC.dvd_comp m hm)⟩
  by_contra h
  refine (conwayKey_conwayPolynomial_le hg).not_gt
    ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), ?_⟩
  have hcoeff : (conwayPolynomial p n).coeff n = (conwayPolynomial p n).leadingCoeff := by
    rw [leadingCoeff, hC.natDegree_eq]
  simp only [conwayKey, Pi.toLex_apply, Fin.val_zero, pow_zero, one_mul, Nat.sub_zero,
    coeff_C_mul, hcoeff, inv_mul_cancel₀ ha, ZMod.val_one]
  have h1 : (conwayPolynomial p n).leadingCoeff.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have h2 : (conwayPolynomial p n).leadingCoeff.val ≠ 1 := by
    rwa [Ne, ZMod.val_eq_one hp.out.one_lt]
  omega

/-- **The Conway polynomial is irreducible**: it is the minimal polynomial of its root of order
`p ^ n - 1`, which has degree `n`. -/
lemma irreducible_conwayPolynomial : Irreducible (conwayPolynomial p n) := by
  have hC : IsConwayCompatible p (conwayPolynomial p) n (conwayPolynomial p n) :=
    isConwayCompatible_conwayPolynomial p hn
  rcases hC.exists_root with ⟨x, hx, hxo⟩
  have hxi : IsIntegral (ZMod p) x := IsIntegral.isIntegral x
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (monic_conwayPolynomial p hn)
    (minpoly.dvd _ _ hx) (by rw [hC.natDegree_eq, natDegree_minpoly_of_orderOf_eq hn hxo])]
  exact minpoly.irreducible hxi

variable {p}

/-- **The Conway polynomial is the minimal polynomial of each of its roots** in `𝔽̄_p`. -/
lemma conwayPolynomial_eq_minpoly (hx : aeval x (conwayPolynomial p n) = 0) :
    conwayPolynomial p n = minpoly (ZMod p) x :=
  minpoly.eq_of_irreducible_of_monic (irreducible_conwayPolynomial p hn) hx
    (monic_conwayPolynomial p hn)

end FiniteField
