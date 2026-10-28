import Mathlib.Algebra.Module.Lattice
import Mathlib.Data.Rat.Sqrt
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Trace.Defs
import TauCeti.Algebra.Quaternion.AlgEquiv

/-!
# Discriminants, Eichler orders and polarizations of quaternion orders

Let `B` be a quaternion algebra over `ℚ`, a central simple `ℚ`-algebra of dimension `4`. Every
element `x` of `B` satisfies `x² - trd(x) x + nrd(x) = 0` for its reduced trace `trd(x)`, half the
trace of left multiplication by `x`, and its reduced norm `nrd(x) = (trd(x)² - trd(x²)) / 2`. For
`B = (c₁, c₂, c₃ / ℚ)` presented as Mathlib's `ℍ[ℚ,c₁,c₂,c₃]` they are `x + x̄` and `x x̄`.

The algebra `B` is ramified at a prime `p` if `B ⊗ ℚ_p` is a division algebra, and split otherwise;
its discriminant is the product of the ramified primes. An order `O` of `B` (LMFDB
`shimcurve.order`) is a subring which is a `ℤ`-lattice spanning `B`; its discriminant is
`|det (trd(x_i x_j))|` for a `ℤ`-basis `x₁, …, x₄` of `O`, a perfect square whose square root is the
reduced discriminant. An Eichler order is an intersection of two maximal orders; over `ℚ` its
reduced discriminant is `D M` with `D = disc(B)` and `gcd(D, M) = 1`, and `M` is its level. A
polarization of an order `O` in an indefinite division quaternion algebra is a unit `μ` with
`μ² ∈ ℤ_{<0}` and `trd(μ x) ∈ ℤ` for all `x ∈ O`, and its degree is the squarefree part of
`nrd(μ) / discrd(O)`.

The algebra `B` is any `ℚ`-algebra here, and is a quaternion algebra in the intended applications;
the reduced trace and norm are given by the formulas above, which agree with Mathlib's
presentation (`QuaternionAlgebra.reducedTrace_quaternionAlgebra` and
`QuaternionAlgebra.reducedNorm_quaternionAlgebra`). The following facts, which make the
definitions meaningful, are not proved: that the discriminant of `B` is a finite product, that the
discriminant of an order does not depend on the basis and is a perfect square, and that the
quotient `nrd(μ) / discrd(O)` is an integer.

## Main definitions

* `QuaternionAlgebra.reducedTrace` and `QuaternionAlgebra.reducedNorm`: the reduced trace and norm.
* `QuaternionAlgebra.IsRamifiedAt` and `QuaternionAlgebra.IsSplitAt` (LMFDB `shimcurve.discb`):
  ramified and split primes.
* `QuaternionAlgebra.discriminant` (LMFDB `shimcurve.discb`): the discriminant of `B`.
* `Subalgebra.IsQuaternionOrder` (LMFDB `shimcurve.order`): orders.
* `Subalgebra.quaternionDisc` and `Subalgebra.quaternionDiscrd` (LMFDB `shimcurve.disco`): the
  discriminant and the reduced discriminant of an order.
* `Subalgebra.IsMaximalQuaternionOrder`: maximal orders.
* `Subalgebra.IsEichlerOrder` and `Subalgebra.IsEichlerOrderOfLevel` (LMFDB `shimcurve.eichler`):
  Eichler orders and their level.
* `Subalgebra.IsPolarization` (LMFDB `shimcurve.polarized_order`): polarizations of an order.
* `PolarizedQuaternionOrder` (LMFDB `shimcurve.polarized_order`): polarized orders.
* `PolarizedQuaternionOrder.degree` (LMFDB `shimcurve.nrdmu`): the polarization degree.

## Main results

* `QuaternionAlgebra.reducedTrace_quaternionAlgebra`: the reduced trace of `ℍ[ℚ,c₁,c₂,c₃]` is
  `x + x̄ = 2 re(x) + c₂ imI(x)`.
* `QuaternionAlgebra.reducedNorm_quaternionAlgebra`: its reduced norm is `x x̄`.
-/

open scoped TensorProduct Quaternion

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B] (x : B) (p : Nat.Primes)

/-- The **reduced trace** `trd(x)` of an element `x` of a quaternion algebra `B` over `ℚ`: half the
trace of left multiplication by `x` on the `4`-dimensional `ℚ`-vector space `B`. -/
noncomputable def reducedTrace : ℚ :=
  LinearMap.trace ℚ B (LinearMap.mulLeft ℚ x) / 2

/-- The **reduced norm** `nrd(x)` of an element `x` of a quaternion algebra `B` over `ℚ`:
`(trd(x)² - trd(x²)) / 2`, so that `x² - trd(x) x + nrd(x) = 0`. -/
noncomputable def reducedNorm : ℚ :=
  (reducedTrace B x ^ 2 - reducedTrace B (x ^ 2)) / 2

/-- A quaternion algebra `B` over `ℚ` is **ramified** at a prime `p` (LMFDB `shimcurve.discb`) if
`B ⊗ ℚ_p` is a division algebra over `ℚ_p`: every nonzero element is a unit. -/
def IsRamifiedAt : Prop :=
  haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
  ∀ y : ℚ_[p] ⊗[ℚ] B, y ≠ 0 → IsUnit y

/-- A quaternion algebra `B` over `ℚ` is **split** at a prime `p` (LMFDB `shimcurve.discb`) if it is
not ramified at `p`: then `B ⊗ ℚ_p` is isomorphic to the matrix algebra `M₂(ℚ_p)`. -/
def IsSplitAt : Prop :=
  ¬IsRamifiedAt B p

open scoped Classical in
/-- The **discriminant** `disc(B)` of a quaternion algebra `B` over `ℚ` (LMFDB `shimcurve.discb`):
the product of the primes at which `B` is ramified. There are finitely many of them (this is not
proved here), and the product is `1` if there were infinitely many. -/
noncomputable def discriminant : ℕ :=
  ∏ᶠ p : Nat.Primes, if IsRamifiedAt B p then (p : ℕ) else 1

/-- `B` is a **division algebra**: every nonzero element is a unit. -/
def IsDivision : Prop :=
  ∀ y : B, y ≠ 0 → IsUnit y

/-- A quaternion algebra `B` over `ℚ` is **indefinite** if it is split at the infinite place: the
real algebra `ℝ ⊗ B`, which is either Hamilton's quaternions or `M₂(ℝ)`, is not a division
algebra. -/
def IsIndefinite : Prop :=
  ¬∀ y : ℝ ⊗[ℚ] B, y ≠ 0 → IsUnit y

variable {c₁ c₂ c₃ : ℚ} (q : ℍ[ℚ,c₁,c₂,c₃])

/-- **The reduced trace of `ℍ[ℚ,c₁,c₂,c₃]` is `x + x̄ = 2 re(x) + c₂ imI(x)`.** -/
lemma reducedTrace_quaternionAlgebra : reducedTrace _ q = 2 * q.re + c₂ * q.imI := by
  rw [reducedTrace, trace_mulLeft]
  ring1

/-- **The reduced norm of `ℍ[ℚ,c₁,c₂,c₃]` is `x x̄`.** -/
lemma reducedNorm_quaternionAlgebra : reducedNorm _ q = (q * star q).re := by
  rw [reducedNorm, reducedTrace_quaternionAlgebra, reducedTrace_quaternionAlgebra]
  simp [sq, re_mul, imI_mul]
  ring1

end QuaternionAlgebra

open QuaternionAlgebra

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] (O : Subalgebra ℤ B)

/-- A subring `O` of a quaternion algebra `B` over `ℚ` is an **order** (LMFDB `shimcurve.order`) if
it is a `ℤ`-lattice in `B`: a finitely generated `ℤ`-module that spans `B` over `ℚ`. -/
def IsQuaternionOrder : Prop :=
  Submodule.IsLattice ℚ (toSubmodule O)

/-- The **discriminant** `|det (trd(x_i x_j))_{i,j}|` of a `ℤ`-basis `x₁, …, x₄` of an order `O`. -/
noncomputable def quaternionDiscOfBasis (x : Module.Basis (Fin 4) ℤ O) : ℚ :=
  |(Matrix.of fun i j ↦ reducedTrace B ((x i : B) * x j)).det|

open scoped Classical in
/-- The **discriminant** `disc(O) = |det (trd(x_i x_j))_{i,j}|` of an order `O` of a quaternion
algebra over `ℚ` (LMFDB `shimcurve.disco`), for a `ℤ`-basis `x₁, …, x₄` of `O`, chosen here, and
`0` when `O` has no basis of four elements. It does not depend on the basis, since a change of basis
multiplies the determinant by the square `±1` of the determinant of an integral matrix with integral
inverse (this is not proved here). -/
noncomputable def quaternionDisc : ℚ :=
  if h : Nonempty (Module.Basis (Fin 4) ℤ O) then O.quaternionDiscOfBasis h.some else 0

/-- The **reduced discriminant** `discrd(O)` of an order `O` of a quaternion algebra over `ℚ` (LMFDB
`shimcurve.disco`): the positive integer whose square is `disc(O)`, here the rational square root
`Rat.sqrt`, which is that integer since `disc(O)` is the square of an integer (this is not proved
here). -/
noncomputable def quaternionDiscrd : ℚ :=
  Rat.sqrt O.quaternionDisc

/-- An order of a quaternion algebra is **maximal** if it is not contained in a larger order. -/
def IsMaximalQuaternionOrder : Prop :=
  Maximal IsQuaternionOrder O

/-- An order `O` of a quaternion algebra is an **Eichler order** (LMFDB `shimcurve.eichler`) if it
is the intersection of two, not necessarily distinct, maximal orders. -/
def IsEichlerOrder : Prop :=
  ∃ O₁ O₂ : Subalgebra ℤ B, O₁.IsMaximalQuaternionOrder ∧ O₂.IsMaximalQuaternionOrder ∧ O = O₁ ⊓ O₂

/-- An Eichler order `O` of a quaternion algebra `B` over `ℚ` is **Eichler of level `M`** (LMFDB
`shimcurve.eichler`) if its reduced discriminant is `D M` with `D = disc(B)` and `gcd(D, M) = 1`. -/
def IsEichlerOrderOfLevel (M : ℕ) : Prop :=
  O.IsEichlerOrder ∧ O.quaternionDiscrd = discriminant B * M ∧ (discriminant B).Coprime M

/-- A **polarization** (LMFDB `shimcurve.polarized_order`) of an order `O` of a quaternion algebra
`B` over `ℚ`, which is indefinite and a division algebra for the LMFDB: a unit `μ` of `B` with
`μ² ∈ ℤ_{<0}` and `trd(μ x) ∈ ℤ` for every `x ∈ O`. -/
structure IsPolarization (μ : Bˣ) : Prop where
  /-- The square of a polarization is a negative integer. -/
  exists_sq_eq : ∃ m : ℤ, m < 0 ∧ (μ : B) ^ 2 = m
  /-- The reduced trace of `μ x` is an integer for every `x ∈ O`. -/
  exists_reducedTrace_mul_eq : ∀ x ∈ O, ∃ k : ℤ, reducedTrace B (μ * x) = k

end Subalgebra

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- A **polarized order** (LMFDB `shimcurve.polarized_order`) of an indefinite division quaternion
algebra `B` over `ℚ`: a pair `(O, μ)` of an order `O` of `B` and a polarization `μ` of `O`. -/
structure PolarizedQuaternionOrder where
  /-- `B` is a division algebra. -/
  isDivision : IsDivision B
  /-- `B` is indefinite. -/
  isIndefinite : IsIndefinite B
  /-- The order `O`. -/
  order : Subalgebra ℤ B
  /-- `O` is an order. -/
  isQuaternionOrder : order.IsQuaternionOrder
  /-- The polarization `μ`. -/
  polarization : Bˣ
  /-- `μ` is a polarization of `O`. -/
  isPolarization : order.IsPolarization polarization

namespace PolarizedQuaternionOrder

variable {B} (O : PolarizedQuaternionOrder B)

/-- The **polarization degree** `deg(μ)` of a polarized order `(O, μ)` (LMFDB `shimcurve.nrdmu`):
the squarefree part `∏_p p^(v_p(n) mod 2)` of the integer `n = nrd(μ) / discrd(O)`, here the
absolute value of the numerator of the rational number `nrd(μ) / discrd(O)`, which is that integer
`n` (its integrality is not proved here). -/
noncomputable def degree : ℕ :=
  letI n : ℕ := (reducedNorm B O.polarization / O.order.quaternionDiscrd).num.natAbs
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

end PolarizedQuaternionOrder
