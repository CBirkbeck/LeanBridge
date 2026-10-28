import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.Equation
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# Igusa–Clebsch, Igusa and G2-invariants of genus two curves

A binary sextic `F(x, z) = ∏ᵢ (zᵢ x - xᵢ z)` over a field `L`, with roots `(xᵢ : zᵢ)` for
`i = 1, …, 6` (the leading coefficient absorbed in the first root), has the Igusa–Clebsch invariants

* `I₂ = ∑ (12)²(34)²(56)²`,
* `I₄ = ∑ (12)²(23)²(31)²(45)²(56)²(64)²`,
* `I₆ = ∑ (12)²(23)²(31)²(45)²(56)²(64)²(14)²(25)²(36)²`,
* `I₁₀ = ∏ (12)²`,

where `(ij) = xᵢ zⱼ - xⱼ zᵢ` and each sum runs over the distinct expressions obtained by permuting
the indices. Each expression is the product of `(ij)²` over the edges `ij` of a graph on six
vertices, and the distinct expressions are indexed by the orbit of that graph under `S₆`. For a
sextic `f = c ∏ (x - xᵢ)` the roots are `(c x₁ : c)` and `(xᵢ : 1)`, which gives the LMFDB's
`I₂ = c² ∑ (12)²(34)²(56)²`, and so on; a quintic `f` is read as a binary sextic with a root
`(1 : 0)` at infinity, as Sage and Magma do.

For a genus two curve `y² + h(x)y = f(x)` these are the invariants of the sextic `4f + h²` of its
simplified equation, taken in the splitting field of `4f + h²`. That they lie in the base field (as
symmetric functions of the roots) is not proved here.

## Main definitions

* `Polynomial.sexticOrbitSum`: the sum over the `S₆`-orbit of a graph of the products of the
  squared brackets along its edges.
* `Polynomial.igusaClebsch` (LMFDB `g2c.igusa_clebsch_invariants`): the Igusa–Clebsch invariants
  `I₂, I₄, I₆, I₁₀` of a binary sextic.
* `Polynomial.igusa` (LMFDB `g2c.igusa_invariants`): the Igusa invariants `J₂, …, J₁₀`.
* `Polynomial.g2Invariants` (LMFDB `g2c.g2_invariants`): the G2-invariants `g₁, g₂, g₃`.
* `Polynomial.normalizeWeighted` (LMFDB `g2c.igusa_clebsch_invariants`, `g2c.igusa_invariants`):
  the LMFDB normalisation of integral weighted projective invariants.
* `HyperellipticEquation.igusaClebsch`, `HyperellipticEquation.igusa` and
  `HyperellipticEquation.g2Invariants`: the invariants of a genus two Weierstrass equation.

## Main results

* `Polynomial.sexticOrbitSum_comp`: the orbit sums do not depend on the ordering of the roots.
-/

open Polynomial

variable {K L : Type*} [Field K] [Field L] (r : Fin 6 → L × L) (G : Finset (Sym2 (Fin 6)))

namespace Polynomial

/-- The squared bracket `(xᵢ zⱼ - xⱼ zᵢ)²` of two roots `(xᵢ : zᵢ)` and `(xⱼ : zⱼ)` of a binary
sextic, as a function of the unordered pair `ij`. -/
def sexticBracketSq : Sym2 (Fin 6) → L :=
  Sym2.lift ⟨fun i j ↦ ((r i).1 * (r j).2 - (r j).1 * (r i).2) ^ 2, fun _ _ ↦ by ring1⟩

/-- The orbit of a graph on the vertices `Fin 6` under the permutations of its vertices. -/
def sexticOrbit : Finset (Finset (Sym2 (Fin 6))) :=
  Finset.univ.image fun σ : Equiv.Perm (Fin 6) ↦ G.image (Sym2.map σ)

/-- The sum, over the distinct graphs `H` in the `S₆`-orbit of a graph `G`, of the products of the
squared brackets `(ij)²` of the roots `r` along the edges `ij` of `H`. -/
def sexticOrbitSum : L :=
  ∑ H ∈ sexticOrbit G, ∏ e ∈ H, sexticBracketSq r e

lemma sexticBracketSq_comp (σ : Equiv.Perm (Fin 6)) (e : Sym2 (Fin 6)) :
    sexticBracketSq (r ∘ σ) e = sexticBracketSq r (e.map σ) := by
  induction e using Sym2.ind
  rfl

/-- **The orbit sums do not depend on the ordering of the roots.** -/
lemma sexticOrbitSum_comp (σ : Equiv.Perm (Fin 6)) :
    sexticOrbitSum (r ∘ σ) G = sexticOrbitSum r G := by
  refine Finset.sum_nbij' (fun H ↦ H.image (Sym2.map σ)) (fun H ↦ H.image (Sym2.map σ.symm)) ?_
    ?_ ?_ ?_ ?_
  · intro H hH
    rcases Finset.mem_image.mp hH with ⟨τ, -, rfl⟩
    exact Finset.mem_image.mpr ⟨σ * τ, Finset.mem_univ _, by
      rw [Finset.image_image, ← Sym2.map_comp]; rfl⟩
  · intro H hH
    rcases Finset.mem_image.mp hH with ⟨τ, -, rfl⟩
    exact Finset.mem_image.mpr ⟨σ⁻¹ * τ, Finset.mem_univ _, by
      rw [Finset.image_image, ← Sym2.map_comp]; rfl⟩
  · intro H _
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.symm_comp_self, Sym2.map_id, Finset.image_id]
  · intro H _
    rw [Finset.image_image, ← Sym2.map_comp, Equiv.self_comp_symm, Sym2.map_id, Finset.image_id]
  · intro H _
    rw [Finset.prod_image fun _ _ _ _ h ↦ Sym2.map.injective σ.injective h]
    exact Finset.prod_congr rfl fun e _ ↦ sexticBracketSq_comp r σ e

/-- The graphs on six vertices defining the Igusa–Clebsch invariants `I₂, I₄, I₆, I₁₀`: a perfect
matching `12, 34, 56`, two triangles `123, 456`, two triangles joined by the matching `14, 25, 36`,
and the complete graph. -/
def igusaClebschGraph : Fin 4 → Finset (Sym2 (Fin 6)) :=
  ![{s(0, 1), s(2, 3), s(4, 5)}, {s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3)},
    {s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3), s(0, 3), s(1, 4), s(2, 5)},
    Finset.univ.filter fun e ↦ ¬e.IsDiag]

variable (p : K[X])

/-- The roots `(xᵢ : zᵢ)` of a polynomial `p` of degree `d ≤ 6` read as the binary sextic
`z⁶ p(x/z)`, in the splitting field of `p`: the roots `(xᵢ : 1)` of `p` in some order, then the root
`(1 : 0)` at infinity with multiplicity `6 - d`, the first one multiplied by the leading coefficient
of `p`, so that the binary sextic is the product of the `zᵢ x - xᵢ z`. -/
noncomputable def sexticRoots : Fin 6 → p.SplittingField × p.SplittingField :=
  fun i ↦ (if i = 0 then algebraMap K p.SplittingField p.leadingCoeff else 1) •
    if (i : ℕ) < p.natDegree then ((p.map (algebraMap K _)).roots.toList.getD i 0, 1) else (1, 0)

/-- The **Igusa–Clebsch invariants** `I₂, I₄, I₆, I₁₀` (LMFDB `g2c.igusa_clebsch_invariants`) of a
polynomial `p = c ∏ (x - xᵢ)` of degree at most `6`, read as a binary sextic: `I₂` is
`c² ∑ (12)²(34)²(56)²` over the distinct expressions obtained by permuting the indices, and
similarly for `I₄` and `I₆`, while `I₁₀ = c¹⁰ ∏ (12)²` is the discriminant. They are computed from
the roots in the splitting field of `p`, independently of their ordering
(`Polynomial.sexticOrbitSum_comp`). A quintic has a root at infinity, as in Sage and Magma. -/
noncomputable def igusaClebsch (k : Fin 4) : p.SplittingField :=
  sexticOrbitSum p.sexticRoots <| igusaClebschGraph k

/-- The **Igusa invariants** `J₂, J₄, J₆, J₈, J₁₀` (LMFDB `g2c.igusa_invariants`) of a polynomial
of degree at most `6` read as a binary sextic, computed from its Igusa–Clebsch invariants by the
LMFDB's formulas `J₂ = I₂/8`, `J₄ = (4J₂² - I₄)/96`, `J₆ = (8J₂³ - 160J₂J₄ - I₆)/576`,
`J₈ = (J₂J₆ - J₄²)/4` and `J₁₀ = I₁₀/4096`. These divide by `2` and `3`, so they are only
meaningful in characteristic not `2` or `3`, such as for the LMFDB's curves over `ℚ`; Igusa's
integral formulas for characteristics `2` and `3` are not formalised. -/
noncomputable def igusa : Fin 5 → p.SplittingField :=
  haveI J₂ : p.SplittingField := p.igusaClebsch 0 / 8
  haveI J₄ : p.SplittingField := (4 * J₂ ^ 2 - p.igusaClebsch 1) / 96
  haveI J₆ : p.SplittingField := (8 * J₂ ^ 3 - 160 * J₂ * J₄ - p.igusaClebsch 2) / 576
  ![J₂, J₄, J₆, (J₂ * J₆ - J₄ ^ 2) / 4, p.igusaClebsch 3 / 4096]

open scoped Classical in
/-- The **G2-invariants** `g₁, g₂, g₃` (LMFDB `g2c.g2_invariants`) of a polynomial of degree at most
`6` read as a binary sextic, from its Igusa invariants `J₂, …, J₁₀`: they are
`(J₂⁵/J₁₀, J₂³J₄/J₁₀, J₂²J₆/J₁₀)` if `J₂ ≠ 0`, `(0, J₄⁵/J₁₀², J₄J₆/J₁₀)` if `J₂ = 0` and
`J₄ ≠ 0`, and `(0, 0, J₆⁵/J₁₀³)` if `J₂ = J₄ = 0`. -/
noncomputable def g2Invariants : Fin 3 → p.SplittingField :=
  if p.igusa 0 ≠ 0 then
    ![p.igusa 0 ^ 5 / p.igusa 4, p.igusa 0 ^ 3 * p.igusa 1 / p.igusa 4,
      p.igusa 0 ^ 2 * p.igusa 2 / p.igusa 4]
  else if p.igusa 1 ≠ 0 then
    ![0, p.igusa 1 ^ 5 / p.igusa 4 ^ 2, p.igusa 1 * p.igusa 2 / p.igusa 4]
  else ![0, 0, p.igusa 2 ^ 5 / p.igusa 4 ^ 3]

/-- The **LMFDB normalisation** (LMFDB `g2c.igusa_clebsch_invariants`, `g2c.igusa_invariants`) of
integral invariants `I j` of positive weights `w j` (`1, 2, 3, 5` for `I₂, I₄, I₆, I₁₀` and
`1, 2, 3, 4, 5` for `J₂, …, J₁₀`): divide each `I j` by `d ^ w j`, for the largest positive
integer `d` keeping them integral, then multiply each by `(-1) ^ w j` if the first nonzero
invariant of odd weight is negative. This is the action of `λ = i` on weighted projective space,
where the knowl's text says "multiplying each `I_{2k}` by `(-i)^k`", which is not `i^(2k)`. -/
def normalizeWeighted {n : ℕ} (w : Fin n → ℕ) (I : Fin n → ℤ) : Fin n → ℤ :=
  haveI d : ℕ := Nat.findGreatest (fun d ↦ ∀ j, (d : ℤ) ^ w j ∣ I j) (∑ j, (I j).natAbs)
  haveI s : ℤ := match (List.finRange n).find? fun j ↦ Odd (w j) ∧ I j ≠ 0 with
    | some j => if I j < 0 then -1 else 1
    | none => 1
  fun j ↦ s ^ w j * (I j / (d : ℤ) ^ w j)

end Polynomial

namespace HyperellipticEquation

variable (E : HyperellipticEquation 2 K)

/-- The **Igusa–Clebsch invariants** `I₂, I₄, I₆, I₁₀` (LMFDB `g2c.igusa_clebsch_invariants`) of a
genus two Weierstrass equation `y² + h(x)y = f(x)`: those of the sextic `4f + h²`, as in Sage. -/
noncomputable def igusaClebsch : Fin 4 → E.simplifiedPolynomial.SplittingField :=
  E.simplifiedPolynomial.igusaClebsch

/-- The **Igusa invariants** `J₂, …, J₁₀` (LMFDB `g2c.igusa_invariants`) of a genus two Weierstrass
equation `y² + h(x)y = f(x)`: those of the sextic `4f + h²`. -/
noncomputable def igusa : Fin 5 → E.simplifiedPolynomial.SplittingField :=
  E.simplifiedPolynomial.igusa

/-- The **G2-invariants** `g₁, g₂, g₃` (LMFDB `g2c.g2_invariants`) of a genus two Weierstrass
equation `y² + h(x)y = f(x)`: those of the sextic `4f + h²`. -/
noncomputable def g2Invariants : Fin 3 → E.simplifiedPolynomial.SplittingField :=
  E.simplifiedPolynomial.g2Invariants

end HyperellipticEquation
