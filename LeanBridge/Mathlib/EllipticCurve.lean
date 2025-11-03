import LeanBridge.ForMathlib.Heights
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open NumberField InfinitePlace

noncomputable instance Rat.instUniqueInfinitePlace : Unique <| InfinitePlace ℚ :=
  uniqueOfSubsingleton Rat.infinitePlace

lemma Rat.eq_infinitePlace (v : InfinitePlace ℚ) : v = Rat.infinitePlace := by
  ext
  simp

lemma Rat.infinitePlace_mult (v : InfinitePlace ℚ) : v.mult = 1 := by
  simp_rw [eq_infinitePlace, mult, if_pos Rat.isReal_infinitePlace]

namespace WeierstrassCurve.Affine.Point

universe u

def mk {R : Type u} [Nontrivial R] [CommRing R] {W : Affine R} [W.IsElliptic] (x y : R)
    (h : W.Equation x y) : W.Point :=
  .some <| equation_iff_nonsingular.mp h

end WeierstrassCurve.Affine.Point

local macro "equation_simp" : tactic => `(tactic| norm_num [WeierstrassCurve.Affine.equation_iff])

abbrev EllipticCurve_389_a1 : WeierstrassCurve.Affine ℚ :=
  ⟨0, 1, 1, -2, 0⟩

namespace WeierstrassCurve.EllipticCurve_389_a1

lemma Δ_eq : EllipticCurve_389_a1.Δ = 389 := by
  norm_num [Δ, b₂, b₄, b₆, b₈]

instance : WeierstrassCurve.IsElliptic EllipticCurve_389_a1 where
  isUnit := by simp [Δ_eq]

lemma j_eq : EllipticCurve_389_a1.j = 1404928 / 389 := by
  norm_num [j, c₄, b₂, b₄, Δ_eq]

abbrev P_neg2_0 : EllipticCurve_389_a1.Point := .mk (-2) 0 <| by equation_simp
abbrev P_neg2_neg1 : EllipticCurve_389_a1.Point := .mk (-2) (-1) <| by equation_simp

abbrev P_neg1_1 : EllipticCurve_389_a1.Point := .mk (-1) 1 <| by equation_simp
abbrev P_neg1_neg2 : EllipticCurve_389_a1.Point := .mk (-1) (-2) <| by equation_simp

abbrev P_0_0 : EllipticCurve_389_a1.Point := .mk 0 0 <| by equation_simp
abbrev P_0_neg1 : EllipticCurve_389_a1.Point := .mk 0 (-1) <| by equation_simp

abbrev P_1_0 : EllipticCurve_389_a1.Point := .mk 1 0 <| by equation_simp
abbrev P_1_neg1 : EllipticCurve_389_a1.Point := .mk 1 (-1) <| by equation_simp

abbrev P_3_5 : EllipticCurve_389_a1.Point := .mk 3 5 <| by equation_simp
abbrev P_3_neg6 : EllipticCurve_389_a1.Point := .mk 3 (-6) <| by equation_simp

abbrev P_4_8 : EllipticCurve_389_a1.Point := .mk 4 8 <| by equation_simp
abbrev P_4_neg9 : EllipticCurve_389_a1.Point := .mk 4 (-9) <| by equation_simp

abbrev P_6_15 : EllipticCurve_389_a1.Point := .mk 6 15 <| by equation_simp
abbrev P_6_neg16 : EllipticCurve_389_a1.Point := .mk 6 (-16) <| by equation_simp

abbrev P_39_246 : EllipticCurve_389_a1.Point := .mk 39 246 <| by equation_simp
abbrev P_39_neg247 : EllipticCurve_389_a1.Point := .mk 39 (-247) <| by equation_simp

abbrev P_133_1539 : EllipticCurve_389_a1.Point := .mk 133 1539 <| by equation_simp
abbrev P_133_neg1540 : EllipticCurve_389_a1.Point := .mk 133 (-1540) <| by equation_simp

abbrev P_188_2584 : EllipticCurve_389_a1.Point := .mk 188 2584 <| by equation_simp
abbrev P_188_neg2585 : EllipticCurve_389_a1.Point := .mk 188 (-2585) <| by equation_simp

lemma neg_P_neg2_0 : -P_neg2_0 = P_neg2_neg1 := by simp [Affine.Point.mk]
lemma P_neg2_0_add_P_neg1_1 : P_neg2_0 + P_neg1_1 = P_3_neg6 := by norm_num [Affine.Point.mk]

end WeierstrassCurve.EllipticCurve_389_a1
