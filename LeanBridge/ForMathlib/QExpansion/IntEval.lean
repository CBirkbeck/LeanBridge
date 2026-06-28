import LeanBridge.ForMathlib.QExpansion.Generic

/-!
# Integer-arithmetic evaluation of E₄/E₆ polynomials

The certification of q-coefficients reduces to `decide +kernel` on `evalEisList`, which evaluates
a polynomial in the q-expansions of `E₄, E₆` over `ℚ`. Rational arithmetic in the kernel pays a
gcd-normalization cost on every operation. Working over `ℤ` instead (clearing denominators by a
common scale `D`) is ~2.8× faster and uses ~1.7× less memory.

This file provides a `CommRing`-generic copy of the `evalEisList` machinery (`evalEisListG`),
proves it commutes with ring homomorphisms (`evalEisListG_map`) and constant scaling
(`evalEisListG_smul_coeff`), and combines these into the bridge

`evalEisList_eq_intCast_div`:
  `evalEisList (Pz.map (fun t => (t.1, t.2.1, (t.2.2 : ℚ) / D))) N`
    `= (evalEisListZ Pz N).map (fun z => (z : ℚ) / D)`

so the heavy kernel work can be done over `ℤ` (`evalEisListZ`) while the form-side bridge keeps
using the rational `evalEisList`.
-/

namespace LeanBridge.QExpansion

open List

/-! ## Generic (`CommRing`) truncated power-series operations -/

section Generic
variable {R : Type*} [CommRing R] [DecidableEq R]

/-- Truncating addition over any ring. -/
def addTruncG (n : ℕ) (a b : List R) : List R := (a.addPointwise b).take n
/-- Truncating multiplication (convolution) over any ring. -/
def mulTruncG (n : ℕ) (a b : List R) : List R := (a.convolve b).take n
/-- Truncating scalar multiplication over any ring. -/
def smulTruncG (n : ℕ) (c : R) (l : List R) : List R := (l.mulPointwise c).take n
/-- Unit power series truncated to length `n`, over any ring. -/
def oneTruncG (n : ℕ) : List R := (range n).map fun i => if i = 0 then (1 : R) else 0
/-- Truncating power over any ring. -/
def powTruncG (n : ℕ) (l : List R) : ℕ → List R
  | 0 => oneTruncG n
  | k + 1 => mulTruncG n l (powTruncG n l k)
/-- q-expansion of `E₄` truncated to length `n`, over any ring. -/
def E4G (n : ℕ) : List R := (range n).map fun m => if m = 0 then (1 : R) else 240 * (sigmaKK 3 m : R)
/-- q-expansion of `E₆` truncated to length `n`, over any ring. -/
def E6G (n : ℕ) : List R := (range n).map fun m => if m = 0 then (1 : R) else -504 * (sigmaKK 5 m : R)
/-- Truncated q-expansion of the monomial `c · E₄^a · E₆^b`, over any ring. -/
def monomialEisG (a b : ℕ) (c : R) (n : ℕ) : List R :=
  smulTruncG n c (mulTruncG n (powTruncG n (E4G n) a) (powTruncG n (E6G n) b))
/-- Truncated q-expansion of `Σ (a,b,c) ∈ P, c · E₄^a · E₆^b`, over any ring. -/
def evalEisListG (P : List (ℕ × ℕ × R)) (n : ℕ) : List R :=
  P.foldr (fun abc acc => addTruncG n (monomialEisG abc.1 abc.2.1 abc.2.2 n) acc) []

end Generic

/-- Integer-arithmetic evaluation. -/
abbrev evalEisListZ (P : List (ℕ × ℕ × ℤ)) (n : ℕ) : List ℤ := evalEisListG P n

/-- The rational `evalEisList` is definitionally the `ℚ` instance of the generic one. -/
lemma powTrunc_eq_G (n : ℕ) (l : List ℚ) (a : ℕ) : powTrunc n l a = powTruncG n l a := by
  induction a with
  | zero => rfl
  | succ k ih => simp only [powTrunc, powTruncG, mulTrunc, mulTruncG]; rw [ih]

lemma monomialEisList_eq_G (a b : ℕ) (c : ℚ) (n : ℕ) :
    monomialEisList a b c n = monomialEisG a b c n := by
  simp only [monomialEisList, monomialEisG, powTrunc_eq_G, mulTrunc, mulTruncG, smulTrunc,
    smulTruncG, E4_qexpList, E4G, E6_qexpList, E6G]

lemma evalEisList_eq_G (P : List (ℕ × ℕ × ℚ)) (n : ℕ) :
    evalEisList P n = evalEisListG P n := by
  induction P with
  | nil => rfl
  | cons abc tl ih =>
    simp only [evalEisList, evalEisListG, List.foldr_cons, addTrunc, addTruncG] at *
    rw [← ih, monomialEisList_eq_G]

/-! ## Primitive `List.map` commutation lemmas -/

/-- `List.map` of an additive function distributes over `addPointwise`. -/
lemma addPointwise_map_add {M N : Type*} [AddMonoid M] [AddMonoid N] (g : M → N)
    (hadd : ∀ x y, g (x + y) = g x + g y) (a b : List M) :
    (a.addPointwise b).map g = (a.map g).addPointwise (b.map g) := by
  induction a generalizing b with
  | nil => cases b <;> simp [List.addPointwise]
  | cons x xs ih =>
    cases b with
    | nil => simp [List.addPointwise]
    | cons y ys => simp [List.addPointwise, hadd, ih]

section RingHomMap
variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring hom commutes with `mulPointwise`. -/
lemma mulPointwise_map (f : R →+* S) (c : R) (l : List R) :
    (l.mulPointwise c).map f = (l.map f).mulPointwise (f c) := by
  simp only [List.mulPointwise, List.map_map]
  apply List.map_congr_left
  intro x _
  simp [Function.comp, map_mul]

/-- A ring hom commutes with `convolve`. -/
lemma convolve_map (f : R →+* S) (a b : List R) :
    (a.convolve b).map f = (a.map f).convolve (b.map f) := by
  induction a generalizing b with
  | nil => simp [List.convolve]
  | cons x xs ih =>
    cases b with
    | nil => simp [List.convolve]
    | cons y ys =>
      simp only [List.convolve, List.mulAddPointwise, List.map_cons]
      rw [addPointwise_map_add f (fun x y => map_add f x y)]
      rw [mulPointwise_map, mulPointwise_map]
      simp only [List.map_cons, map_zero, map_one]
      rw [← List.map_cons, ih]

/-- Scaling a list pointwise by `c` then pointwise by `c'` scales by `c' * c`. -/
lemma mulPointwise_map_mul (c c' : R) (l : List R) :
    (l.mulPointwise c).map (fun x => c' * x) = l.mulPointwise (c' * c) := by
  simp only [List.mulPointwise, List.map_map]
  apply List.map_congr_left
  intro x _
  simp [Function.comp, mul_assoc]

end RingHomMap

/-! ## `evalEisListG` commutes with ring homomorphisms -/

section Hom
variable {R S : Type*} [CommRing R] [DecidableEq R] [CommRing S] [DecidableEq S]

lemma mulTruncG_map (f : R →+* S) (n : ℕ) (a b : List R) :
    (mulTruncG n a b).map f = mulTruncG n (a.map f) (b.map f) := by
  simp only [mulTruncG, List.map_take, convolve_map]

lemma addTruncG_map (f : R →+* S) (n : ℕ) (a b : List R) :
    (addTruncG n a b).map f = addTruncG n (a.map f) (b.map f) := by
  simp only [addTruncG, List.map_take, addPointwise_map_add f (fun x y => map_add f x y)]

lemma smulTruncG_map (f : R →+* S) (n : ℕ) (c : R) (l : List R) :
    (smulTruncG n c l).map f = smulTruncG n (f c) (l.map f) := by
  simp only [smulTruncG, List.map_take, mulPointwise_map]

lemma oneTruncG_map (f : R →+* S) (n : ℕ) :
    (oneTruncG (R := R) n).map f = oneTruncG n := by
  simp only [oneTruncG, List.map_map]
  apply List.map_congr_left
  intro i _
  by_cases h : i = 0 <;> simp [Function.comp, h]

lemma E4G_map (f : R →+* S) (n : ℕ) : (E4G (R := R) n).map f = E4G n := by
  simp only [E4G, List.map_map]
  apply List.map_congr_left
  intro m _
  by_cases h : m = 0 <;> simp [Function.comp, h, map_mul, map_natCast, map_ofNat]

lemma E6G_map (f : R →+* S) (n : ℕ) : (E6G (R := R) n).map f = E6G n := by
  simp only [E6G, List.map_map]
  apply List.map_congr_left
  intro m _
  by_cases h : m = 0 <;> simp [Function.comp, h, map_mul, map_natCast, map_ofNat, map_neg]

lemma powTruncG_map (f : R →+* S) (n : ℕ) (l : List R) (a : ℕ) :
    (powTruncG n l a).map f = powTruncG n (l.map f) a := by
  induction a with
  | zero => simp only [powTruncG, oneTruncG_map]
  | succ k ih => simp only [powTruncG, mulTruncG_map, ih]

lemma monomialEisG_map (f : R →+* S) (a b : ℕ) (c : R) (n : ℕ) :
    (monomialEisG a b c n).map f = monomialEisG a b (f c) n := by
  simp only [monomialEisG, smulTruncG_map, mulTruncG_map, powTruncG_map, E4G_map, E6G_map]

lemma evalEisListG_map (f : R →+* S) (P : List (ℕ × ℕ × R)) (n : ℕ) :
    (evalEisListG P n).map f
      = evalEisListG (P.map (fun t => (t.1, t.2.1, f t.2.2))) n := by
  induction P with
  | nil => rfl
  | cons abc tl ih =>
    show (addTruncG n (monomialEisG abc.1 abc.2.1 abc.2.2 n) (evalEisListG tl n)).map f
      = addTruncG n (monomialEisG abc.1 abc.2.1 (f abc.2.2) n)
          (evalEisListG (tl.map (fun t => (t.1, t.2.1, f t.2.2))) n)
    rw [addTruncG_map, monomialEisG_map, ih]

end Hom

/-! ## `evalEisListG` and constant scaling of coefficients -/

section Scale
variable {R : Type*} [CommRing R] [DecidableEq R]

lemma addTruncG_map_mul (c : R) (n : ℕ) (a b : List R) :
    (addTruncG n a b).map (fun x => c * x) = addTruncG n (a.map (fun x => c * x)) (b.map (fun x => c * x)) := by
  simp only [addTruncG, List.map_take, addPointwise_map_add (fun x => c * x) (fun x y => mul_add c x y)]

lemma monomialEisG_smul (c c0 : R) (a b n : ℕ) :
    monomialEisG a b (c * c0) n = (monomialEisG a b c0 n).map (fun x => c * x) := by
  simp only [monomialEisG, smulTruncG, List.map_take, mulPointwise_map_mul]

lemma evalEisListG_smul_coeff (c : R) (P : List (ℕ × ℕ × R)) (n : ℕ) :
    evalEisListG (P.map (fun t => (t.1, t.2.1, c * t.2.2))) n
      = (evalEisListG P n).map (fun x => c * x) := by
  induction P with
  | nil => rfl
  | cons abc tl ih =>
    show addTruncG n (monomialEisG abc.1 abc.2.1 (c * abc.2.2) n)
          (evalEisListG (tl.map (fun t => (t.1, t.2.1, c * t.2.2))) n)
      = (addTruncG n (monomialEisG abc.1 abc.2.1 abc.2.2 n) (evalEisListG tl n)).map (fun x => c * x)
    rw [addTruncG_map_mul, ih, monomialEisG_smul]

end Scale

/-! ## Bridge: rational evaluation via integer arithmetic -/

/-- The slow rational evaluation of a polynomial with coefficients `(z : ℚ) / D` equals the fast
integer evaluation (over `ℤ`) with each result divided by `D`. The heavy `decide +kernel` work
can therefore be performed over `ℤ`. -/
theorem evalEisList_eq_intCast_div (Pz : List (ℕ × ℕ × ℤ)) (D : ℤ) (N : ℕ) :
    evalEisList (Pz.map (fun t => (t.1, t.2.1, (t.2.2 : ℚ) / D))) N
      = (evalEisListZ Pz N).map (fun z : ℤ => (z : ℚ) / D) := by
  rw [evalEisList_eq_G]
  have hcoeff : (fun t : ℕ × ℕ × ℤ => (t.1, t.2.1, (t.2.2 : ℚ) / D))
      = (fun t : ℕ × ℕ × ℚ => (t.1, t.2.1, (D : ℚ)⁻¹ * t.2.2))
        ∘ (fun t : ℕ × ℕ × ℤ => (t.1, t.2.1, (Int.castRingHom ℚ) t.2.2)) := by
    funext t; simp [Function.comp, div_eq_inv_mul]
  rw [hcoeff, ← List.map_map, evalEisListG_smul_coeff, ← evalEisListG_map (Int.castRingHom ℚ),
    List.map_map]
  apply List.map_congr_left
  intro z _
  simp [Function.comp, div_eq_inv_mul]

end LeanBridge.QExpansion
