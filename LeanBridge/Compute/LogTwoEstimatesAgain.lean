/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Estimates on log base 2 of rationals by iterative squaring

This file was ported from https://github.com/b-mehta/exponential-ramsey/blob/main/src/log2_estimates.lean
The idea for the calculation is https://en.wikipedia.org/wiki/Binary_logarithm#Iterative_approximation
-/

noncomputable section

def Int.isNeg : ℤ → Bool := Int.rec (fun _ ↦ false) (fun _ ↦ true)

@[simp] lemma Int.isNeg_iff {z : ℤ} : Int.isNeg z = true ↔ z < 0 := by
  cases z <;> simp [Int.isNeg]

def Int.addNat : ℤ → ℕ → ℤ :=
  Int.rec (fun m n ↦ Int.ofNat (m.add n)) (fun m n ↦ Int.subNatNat n m.succ)

@[simp] lemma Int.addNat_eq_add (m : ℤ) (n : ℕ) : Int.addNat m n = m + Int.ofNat n := by
  cases m <;> rfl

def Int.negOfNat' : ℕ → ℤ :=
  Nat.rec 0 fun m ↦ Int.negSucc m

@[simp] lemma Int.negOfNat'_eq_negOfNat (n : ℕ) : Int.negOfNat' n = Int.negOfNat n := by
  cases n <;> rfl

def Int.mulNat : ℤ → ℕ → ℤ :=
  Int.rec
    (fun m n ↦ Int.ofNat (m.mul n))
    (fun m n ↦ Int.negOfNat (m.succ.mul n))

@[simp] lemma Int.mulNat_eq_mul (m : ℤ) (n : ℕ) : Int.mulNat m n = m * Int.ofNat n := by
  cases m <;> rfl

def Int.mul' : ℤ → ℤ → ℤ :=
  Int.rec
    (fun m ↦ Int.rec (fun n ↦ Int.ofNat (m.mul n)) (fun n ↦ Int.negOfNat (m.mul n.succ)))
    (fun m ↦ Int.rec (fun n ↦ Int.negOfNat (m.succ.mul n)) (fun n ↦ m.succ.mul n.succ))

@[simp] lemma Int.mul'_eq_mul (m n : ℤ) : Int.mul' m n = m * n := by
  cases m <;> cases n <;> rfl

open Real

lemma logb_zpow {b x : ℝ} (m : ℤ) : logb b (x ^ m) = m * logb b x := by
  rw [logb, log_zpow, mul_div_assoc, logb]

namespace Tactic

def LtLogGoal (a : ℤ) (b x y : ℕ) : Prop := b ≠ 0 → x ≠ 0 → y ≠ 0 → (a / b : ℝ) < logb 2 (x / y : ℝ)

namespace LtLogGoal

lemma finish_lower {x a : ℝ} (aa : ℤ) (ab xa xb : ℕ)
    (hx : x = xa / xb) (ha : a = aa / ab)
    (hab : Nat.blt 0 ab) (hxa : Nat.blt 0 xa) (hxb : Nat.blt 0 xb)
    (h : LtLogGoal aa ab xa xb) :
    a < logb 2 x := by
  simp only [Nat.blt_eq, pos_iff_ne_zero] at hab hxa hxb
  convert h hab hxa hxb

lemma finish_upper {x a : ℝ} (aa : ℤ) (ab xa xb : ℕ)
    (hx : x = xa / xb) (ha : a = aa / ab)
    (hab : Nat.blt 0 ab) (hxa : Nat.blt 0 xa) (hxb : Nat.blt 0 xb)
    (h : LtLogGoal (-aa) ab xb xa) :
    logb 2 x < a := by
  simp only [Nat.blt_eq, pos_iff_ne_zero] at hab hxa hxb
  simpa [ha, hx, neg_div, neg_lt (a := (aa / ab : ℝ)), ← logb_inv] using h hab hxb hxa

lemma finish {a₁ a₂ x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (h₁ : a₁ < logb 2 x₁) (h₂ : logb 2 x₂ < a₂) :
    ∀ x ∈ Set.Icc x₁ x₂, logb 2 x ∈ Set.Icc a₁ a₂ := by
  intro x hx
  exact ⟨h₁.le.trans (logb_le_logb_of_le one_lt_two hx₁ hx.1),
         h₂.le.trans' (logb_le_logb_of_le one_lt_two (hx₁.trans_le hx.1) hx.2)⟩

lemma scale' {a b x y} (m : ℕ) (h : LtLogGoal (2 ^ m * a) b (x ^ 2 ^ m) (y ^ 2 ^ m)) :
    LtLogGoal a b x y := by
  intro hb hx hy
  simpa [← div_pow, logb_pow, mul_div_assoc] using h hb (by positivity) (by positivity)

lemma scale (a b x y) (m : ℕ) (a' : ℤ) (x' y' : ℕ)
    (ha' : a'.beq' (a.mulNat (Nat.pow (nat_lit 2) m)))
    (hx' : x'.beq (Nat.pow x (Nat.pow (nat_lit 2) m)))
    (hy' : y'.beq (Nat.pow y (Nat.pow (nat_lit 2) m)))
    (h : LtLogGoal a' b x' y') :
    LtLogGoal a b x y := by
  simp at ha' hx' hy'
  rw [mul_comm] at ha'
  subst ha' hx' hy'
  exact scale' m h

lemma shift_pos' {a : ℤ} {b x y : ℕ} (m : ℕ) (h : LtLogGoal (a + m * b) b (2 ^ m * x) y) :
    LtLogGoal a b x y := by
  intro hb hx hy
  have := h hb (by positivity) (by positivity)
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have hxy : (x / y : ℝ) ≠ 0 := by positivity
  simpa [add_div, mul_div_assoc, logb_mul, hb', hxy, logb_pow, add_comm a] using this

lemma shift_pos (a : ℤ) (b x y m : ℕ) (a' : ℤ) (x' : ℕ)
    (ha' : a'.beq' (a.addNat (m.mul b)))
    (hx' : x'.beq ((Nat.pow (nat_lit 2) m).mul x))
    (h : LtLogGoal a' b x' y) :
    LtLogGoal a b x y := by
  simp at ha' hx'
  subst ha' hx'
  exact shift_pos' m h

lemma shift_neg' {a : ℤ} {b x y : ℕ} (m : ℕ) (h : LtLogGoal (a - m * b) b x (2 ^ m * y)) :
    LtLogGoal a b x y := by
  intro hb hx hy
  have := h hb (by positivity) (by positivity)
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have hxy : (x / y : ℝ) ≠ 0 := by positivity
  simpa [sub_div, hb', mul_comm (2 ^ m), ← div_div, logb_div hxy, logb_pow] using this

lemma shift_neg (a : ℤ) (b x y m : ℕ) (a' : ℤ) (y' : ℕ)
    (ha' : (a'.addNat (m.mul b)).beq' a)
    (hy' : y'.beq ((Nat.pow (nat_lit 2) m).mul y))
    (h : LtLogGoal a' b x y') :
    LtLogGoal a b x y := by
  simp [Nat.mul_eq, Int.beq'_eq, Nat.pow_eq, Nat.beq_eq] at ha' hy'
  replace ha' : a' = a - m * b := by simp [← ha']
  subst ha' hy'
  exact shift_neg' m h

lemma weaken' {a b x y} (x' y' : ℕ) (hx' : x' ≠ 0) (hxy : x' * y ≤ x * y')
    (h : LtLogGoal a b x' y') :
    LtLogGoal a b x y := by
  intro hb hx hy
  have hy' : y' ≠ 0 := by grind [mul_eq_zero]
  apply (h hb hx' hy').trans_le
  refine logb_le_logb_of_le one_lt_two (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mod_cast hxy

lemma weaken {a b x y} (x' y' : ℕ) (hx' : Nat.blt (nat_lit 0) x') (hxy : (x'.mul y).ble (x.mul y'))
    (h : LtLogGoal a b x' y') :
    LtLogGoal a b x y := by
  simp only [Nat.blt_eq, pos_iff_ne_zero, ne_eq, Nat.mul_eq, Nat.ble_eq] at hx' hxy
  exact weaken' x' y' hx' hxy h

lemma cancel' {a} {b x y : ℕ} (a' : ℤ) (b' : ℕ) (hb' : b' ≠ 0) (hxy : a * b' ≤ a' * b)
    (h : LtLogGoal a' b' x y) :
    LtLogGoal a b x y := by
  intro hb hx hy
  refine (h hb' hx hy).trans_le' ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact mod_cast hxy

lemma cancel {a} {b x y : ℕ} (a' : ℤ) (b' : ℕ) (hb' : Nat.blt (nat_lit 0) b')
    (hxy : (a.mulNat b').ble' (a'.mulNat b))
    (h : LtLogGoal a' b' x y) :
    LtLogGoal a b x y := by
  simp [Nat.blt_eq, Int.ofNat_eq_coe, Int.ble'_eq_true] at hb' hxy
  exact cancel' a' b' hb'.ne' hxy h

lemma trivial' {a b x y} (ha : a < 0) (hxy : y ≤ x) : LtLogGoal a b x y := by
  intro hb hx hy
  calc
    (a / b : ℝ) < 0 := div_neg_of_neg_of_pos (by simpa) (by positivity)
    _ ≤ logb 2 (x / y) := logb_nonneg one_lt_two ((one_le_div₀ (by positivity)).2 (mod_cast hxy))

lemma trivial {a b x y} (ha : a.isNeg) (hxy : y.ble x) : LtLogGoal a b x y := by
  simp [Int.isNeg_iff, Nat.ble_eq] at ha hxy
  exact trivial' ha hxy

end LtLogGoal

section

open Lean Elab Meta Tactic Qq

/--
compute ⌊log₂(a/b)⌋ for positive naturals a, b
warning! does not terminate for a = 0, but this function will only be called for
positive rationals
-/
partial def floorLog2 (a b : ℕ) : ℤ :=
  if a = 0 ∨ b = 0 then panic! s!"unreachable code reached in floorLog2 {a} {b}" else
  if b ≤ a then
    if a < 2 * b then 0
    else floorLog2 a (2 * b) + 1
  else
    floorLog2 (2 * a) b - 1

/--
Finds the least m such that 2 ≤ (a/b)^(2^m)

Warning! does not terminate if a ≤ b
-/
def countSquares (a b : ℕ) : ℕ × ℕ × ℕ :=
  if a ≤ b then panic! s!"unreachable code reached in countSquares {a} {b}" else go 0 a b where
  go (n : ℕ) (a b : ℕ) : ℕ × ℕ × ℕ := if 2 * b ≤ a then (n, a, b) else go (n + 1) (a * a) (b * b)
  partial_fixpoint

partial def prove_ltLogGoal (a : ℤ) (b x y : ℕ) (prec : ℕ) (cut : List String) : MetaM Expr := do
  trace[debug] "Proving LtLogGoal {a} {b} {x} {y}"
  if cut.length > 500 then throwError "detected infinite loop in prove_ltLogGoal;\nhistory: {cut}"
  if x = 0 then throwError "attempted to take log₂ 0 (precision may be too low)"
  if Nat.gcd x y ≠ 1 then
    let g := Nat.gcd x y
    let x' : ℕ := x / g
    let y' : ℕ := y / g
    trace[debug] "reducing fraction by gcd {g} to {x'} / {y'}"
    let pf ← prove_ltLogGoal a b x' y' prec ("cancel" :: cut)
    let pf₁ := mkApp6 (mkConst ``LtLogGoal.weaken)
      (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit x') (mkRawNatLit y')
    let pf₁ := mkApp3 pf₁ reflBoolTrue reflBoolTrue pf
    return pf₁
  if y > 2 ^ prec then
    let x' := Int.natAbs (Rat.floor (x / y * 2 ^ prec))
    let y' := 2 ^ prec
    trace[debug] "weaken to {x'} / {y'}"
    let pf ← prove_ltLogGoal a b x' y' prec ("weaken" :: cut)
    let pf₁ := mkApp6 (mkConst ``LtLogGoal.weaken)
      (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit x') (mkRawNatLit y')
    let pf₁ := mkApp3 pf₁ reflBoolTrue reflBoolTrue pf
    return pf₁
  let m := floorLog2 x y
  unless m = 0 do
    if m > 0 then
      let m := Int.natAbs m
      let y' := y * 2 ^ m
      let a' := a - m * b
      trace[debug] "shift neg by {m} to {a'} {b} {x} {y'}"
      let pf ← prove_ltLogGoal a' b x y' prec (s!"shift neg {m}" :: cut)
      let pf₁ := mkApp7 (mkConst ``LtLogGoal.shift_neg)
        (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit m) (mkIntLit a') (mkRawNatLit y')
      let pf₁ := mkApp3 pf₁ reflBoolTrue reflBoolTrue pf
      return pf₁
    else
      let m := Int.natAbs m
      let x' := x * 2 ^ m
      let a' := a + m * b
      trace[debug] "shift pos by {m} to {a'} {b} {x'} {y}"
      let pf ← prove_ltLogGoal a' b x' y prec (s!"shift pos {m}" :: cut)
      let pf₁ := mkApp7 (mkConst ``LtLogGoal.shift_pos)
        (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit m) (mkIntLit a') (mkRawNatLit x')
      let pf₁ := mkApp3 pf₁ reflBoolTrue reflBoolTrue pf
      return pf₁
  -- now 1 ≤ x / y < 2
  -- ie y ≤ x < 2y
  if a < 0 then
    let pf := mkApp4 (mkConst ``LtLogGoal.trivial)
      (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y)
    let pf := mkApp2 pf reflBoolTrue reflBoolTrue
    return pf
  if x ≤ y ∨ b ≤ a then
    throwError "unable to prove inequality; double check that it is true then increase precision"
  let (m, x', y') := countSquares x y
  let a' := 2 ^ m * a
  trace[debug] "scale by {m} to {a'} {b} {x'} {y'}"
  let pf ← prove_ltLogGoal a' b x' y' prec (s!"scale {m}" :: cut)
  let pf₁ := mkApp8 (mkConst ``LtLogGoal.scale)
    (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x) (mkRawNatLit y) (mkRawNatLit m)
    (mkIntLit a') (mkRawNatLit x') (mkRawNatLit y')
  let pf₁ := mkApp4 pf₁ reflBoolTrue reflBoolTrue reflBoolTrue pf
  return pf₁

elab "prove_ltLogGoal" prec:(ppSpace num)? : tactic => liftMetaFinishingTactic fun g ↦ do
  let e ← g.getTypeCleanup
  match_expr e with
  | LtLogGoal a b x y =>
    let prec : ℕ := prec.casesOn 63 (·.getNat)
    let some a := a.int? | throwError "unexpected a"
    let some b := b.nat? | throwError "unexpected b"
    let some x := x.nat? | throwError "unexpected x"
    let some y := y.nat? | throwError "unexpected y"
    let pf ← prove_ltLogGoal a b x y prec []
    g.assign pf
  | _ => throwError "prove_ltLogGoal can only be used on goals of the form LtLogGoal"


def cleanup_rat (e : Q(ℝ)) : MetaM ((ℤ × ℕ) × (a : Q(ℤ)) × (b : Q(ℕ)) × Q($e = $a / $b)) := do
  let ⟨q, a, b, pf⟩ ← Mathlib.Meta.NormNum.deriveRat e q(Real.instDivisionRing)
  let pf' : Q($e = $a / $b) := q(($pf).to_raw_eq)
  return ⟨(q.num, q.den), a, b, pf'⟩

elab "bound_log" prec:(ppSpace num)? : tactic => liftMetaFinishingTactic fun g ↦ do
  let e ← g.getTypeCleanup
  let prec : ℕ := prec.casesOn 128 (·.getNat)
  match_expr e with
  | LT.lt _ _ lhs rhs =>
    match_expr rhs with
    | Real.logb b ex =>
      let some b := b.nat? | throwError "unexpected expression in base"
      unless b == 2 do throwError "only base 2 supported"
      let ⟨(x, y), _, _, pf⟩ ← cleanup_rat ex
      if x ≤ 0 then
        throwError "log of nonpositive number"
      let ⟨(a, b), _, _, pf'⟩ ← cleanup_rat lhs
      withTraceNode `internal (fun _ ↦ return "") do
        let pf'' ← prove_ltLogGoal a b x.natAbs y prec []
        let pf''' := mkApp6 (mkConst ``LtLogGoal.finish_lower)
          ex lhs (mkIntLit a) (mkRawNatLit b) (mkRawNatLit x.natAbs) (mkRawNatLit y)
        let pf''' := mkApp6 pf''' pf pf' reflBoolTrue reflBoolTrue reflBoolTrue pf''
        g.assign pf'''
    | _ =>
      match_expr lhs with
      | Real.logb b ex =>
        let some b := b.nat? | throwError "unexpected expression in base"
        unless b == 2 do throwError "only base 2 supported"
        let ⟨(x, y), _, _, pf⟩ ← cleanup_rat ex
        if x ≤ 0 then
          throwError "log of nonpositive number"
        let ⟨(a, b), _, _, pf'⟩ ← cleanup_rat rhs
        withTraceNode `internal (fun _ ↦ return "") do
          let pf'' ← prove_ltLogGoal (-a) b y x.natAbs prec []
          let pf''' := mkApp6 (mkConst ``LtLogGoal.finish_upper)
            ex rhs (mkIntLit (a)) (mkRawNatLit b) (mkRawNatLit x.natAbs) (mkRawNatLit y)
          let pf''' := mkApp6 pf''' pf pf' reflBoolTrue reflBoolTrue reflBoolTrue pf''
          g.assign pf'''
      | _ => throwError "unacceptable goal for bound_log"
  | _ => throwError "unacceptable goal for bound_log"

end

open LtLogGoal

lemma thing' : LtLogGoal (-24245007367770138463) 100000000000000000000 1000 1183 := by
  prove_ltLogGoal

example : 2.32192 < logb 2 5 := by bound_log
example : logb 2 5 < 2.32193 := by bound_log
example : -0.2424500736777013847 < logb 2 (1000 / 1183) := by bound_log
example : logb 2 (1000 / 1183) < -0.2424500736777013846 := by bound_log
example : logb 2 1.415 < 0.5009 := by bound_log
example : 0.5008 < logb 2 1.415 := by bound_log
example : 0.4997 < logb 2 (1414 / 1000) := by bound_log

end Tactic
