import Verso
import VersoManual
import VersoBlueprint
import LeanBridgeBlueprint.Prelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Miscellaneous" =>
%%%
tag := "background-miscellaneous"
file := "Background-miscellaneous"
%%%

This section lists the LMFDB definitions in the category `crystals`. Each definition links back to its LMFDB knowl.

:::definition "crystals.crystal"
*Crystal.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/crystals.crystal))

A *($`U_q(\mathfrak{g})`-)crystal* is a nonempty set $`B` together with maps

$$`\begin{aligned}
   &\mathrm{wt}: B \to P\\
   &e_i, f_i : B \to B \cup \{0\} \quad \text{for all } i\in I.
\end{aligned}`

Here $`\mathfrak{g}` is a Lie or Kac-Moody algebra of a particular type with index set $`I`.

The map $`\mathrm{wt}` is called the weight function which maps a crystal element to a weight in the weight lattice $`P`. The maps $`e_i` and $`f_i` are called Kashiwara raising and lowering operators.
:::

:::definition "crystals.highest_weight"
*Highest weight crystals.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/crystals.highest_weight))

Highest weight crystals are {bpref "crystals.crystal"}[Crystal] which have a highest weight element. A highest weight element $`b` is annihilated by all Kashiwara raising operators:

$$`e_i b = 0 \quad \text{for all } i\in I.`

The weight of the highest weight element is used to label the crystal.

Depends on: {uses "crystals.crystal"}[]
:::

:::definition "crystals.littelmann_path"
*Littelmann path model for crystals.* ([LMFDB](https://beta.lmfdb.org/knowledge/show/crystals.littelmann_path))

The Littelmann path model provides a unified combinatorial model for highest weight crystals that applies to all symmetrizable Kac-Moody algebras.

Let $`P` be the weight lattice in the dual of a Cartan subalgebra of the semisimple Lie algebra $`\mathfrak{g}`.
A Littelmann path is a piecewise-linear mapping

$$`\pi:[0,1]\cap \mathbf{Q} \rightarrow P\otimes_{\mathbf{Z}}\mathbf{Q}`

such that $`\pi(0) = 0` and $`\pi(1)` are weights. Littelmann defined the Kashiwara raising and lowering operators $`e_i` and $`f_i` on these paths.
:::
