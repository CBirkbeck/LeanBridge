import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix

/-!
# Second countability of matrices and of the unitary group

The topology of `Matrix m n α` is the product topology of `m → n → α`, so matrices with countably
many rows and columns over a second-countable space are second countable, and so is the unitary
group `Matrix.unitaryGroup n α`, a subspace. Tau Ceti's main branch, past the pin, has the instance
for matrices; at the bump it goes from here.

Mathlib's instance for subspaces is stated for the subtypes of sets, which instance search does not
match against the subtypes of subgroups or submonoids, such as the unitary group and its
subgroups: these take the instance by hand.
-/

open TopologicalSpace

variable {n α : Type*} [TopologicalSpace α] [SecondCountableTopology α]

instance {m : Type*} [Countable m] [Countable n] : SecondCountableTopology (Matrix m n α) :=
  inferInstanceAs (SecondCountableTopology (m → n → α))

instance [Fintype n] [DecidableEq n] [CommRing α] [StarRing α] :
    SecondCountableTopology (Matrix.unitaryGroup n α) :=
  Subtype.secondCountableTopology _
