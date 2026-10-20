import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Borel
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.NonsplitCartan
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SplitCartan

/-!
# Sutherland's labels for subgroups of `GL₂(𝔽_ℓ)`

The LMFDB identifies a subgroup of `GL₂(𝔽_ℓ)` lying in a Borel subgroup or in the normalizer of a
Cartan subgroup, up to conjugacy, by Sutherland's label `ℓS.a.b.c`, where `S` is one of `B`, `Cs`,
`Ns`, `Cn`, `Nn` and `a`, `b`, `c` are optional positive integers. Each label names an explicit
subgroup of `GL₂(𝔽_ℓ)`, defined in the files of the five families; a subgroup has a label when it is
conjugate to the subgroup the label names. The labels `A4`, `S4`, `A5` of exceptional subgroups
record the type of their image in `PGL₂(𝔽_ℓ)` (`Matrix.GeneralLinearGroup.HasExceptionalType`) and
are not listed here.

## Main definitions

* `Matrix.GeneralLinearGroup.SutherlandLabel` (LMFDB `ec.galois_rep_modell_image`): the part
  `S.a.b.c` of a label.
* `Matrix.GeneralLinearGroup.SutherlandLabel.subgroup`: the subgroup of `GL₂(𝔽_ℓ)` it names.
-/

open Matrix

namespace Matrix.GeneralLinearGroup

/-- The part `S.a.b.c` of Sutherland's label `ℓS.a.b.c` of a subgroup of `GL₂(𝔽_ℓ)` contained in a
Borel subgroup or in the normalizer of a Cartan subgroup (LMFDB `ec.galois_rep_modell_image`). -/
inductive SutherlandLabel
  /-- `B`, the Borel subgroup of upper triangular matrices. -/
  | B
  /-- `B.a.b`, see `labelBAB`. -/
  | BAB (a b : ℕ)
  /-- `Cs`, the split Cartan subgroup of diagonal matrices. -/
  | Cs
  /-- `Cs.a.b`, see `labelCsAB`. -/
  | CsAB (a b : ℕ)
  /-- `Ns`, the normalizer of the split Cartan subgroup, see `labelNs`. -/
  | Ns
  /-- `Ns.a.b`, see `labelNsAB`. -/
  | NsAB (a b : ℕ)
  /-- `Ns.a.b.c`, see `labelNsABC`. -/
  | NsABC (a b c : ℕ)
  /-- `Cn`, the non-split Cartan subgroup, see `labelCn`. -/
  | Cn
  /-- `Cn.a.b`, see `labelCnAB`. -/
  | CnAB (a b : ℕ)
  /-- `Nn`, the normalizer of the non-split Cartan subgroup, see `labelNn`. -/
  | Nn
  /-- `Nn.a.b`, see `labelNnAB`. -/
  | NnAB (a b : ℕ)

/-- The subgroup of `GL₂(𝔽_ℓ)` named by Sutherland's label `ℓS.a.b.c` (LMFDB
`ec.galois_rep_modell_image`). -/
noncomputable def SutherlandLabel.subgroup (ℓ : ℕ) [Fact ℓ.Prime] :
    SutherlandLabel → Subgroup (GL (Fin 2) (ZMod ℓ))
  | .B => TauCeti.GL2Borel (ZMod ℓ)
  | .BAB a b => labelBAB ℓ a b
  | .Cs => TauCeti.diagonalTorus (ZMod ℓ) 2
  | .CsAB a b => labelCsAB ℓ a b
  | .Ns => labelNs ℓ
  | .NsAB a b => labelNsAB ℓ a b
  | .NsABC a b c => labelNsABC ℓ a b c
  | .Cn => labelCn ℓ
  | .CnAB a b => labelCnAB ℓ a b
  | .Nn => labelNn ℓ
  | .NnAB a b => labelNnAB ℓ a b

end Matrix.GeneralLinearGroup
