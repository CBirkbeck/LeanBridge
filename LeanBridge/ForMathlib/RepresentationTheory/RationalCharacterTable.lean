import LeanBridge.ForMathlib.GroupTheory.RationalConjugacy
import LeanBridge.ForMathlib.RepresentationTheory.RationalCharacter

/-!
# The rational character table

The rational character table of a finite group `G` tabulates the values of the irreducible
rational characters of `G` (the sums of the Galois conjugates of the irreducible complex
characters, `FDRep.rationalCharacter`) on the rational conjugacy classes of `G`
(`RatConjClasses`). We define it as a function of an irreducible rational character and a rational
class, evaluating the character at a chosen representative of the class. That rational characters
are constant on rational classes, so that this does not depend on the choice, and that the table is
square, are not proved here.

## Main definitions

* `FDRep.irreducibleRationalCharacters` (LMFDB `group.rational_character_table`): the irreducible
  rational characters of `G`, the rows of the table.
* `FDRep.rationalCharacterTable` (LMFDB `group.rational_character_table`): the rational character
  table.
-/

open CategoryTheory

namespace FDRep

variable (G : Type) [Group G]

/-- The **irreducible rational characters** of `G`: the rational characters `∑ σ ∘ χ` attached to
the irreducible complex representations of `G`, without repetition. -/
def irreducibleRationalCharacters : Set (G → ℂ) :=
  {ψ | ∃ X : FDRep ℂ G, Simple X ∧ X.rationalCharacter = ψ}

/-- The **rational character table** of `G` (LMFDB `group.rational_character_table`): the value
of each irreducible rational character on each rational conjugacy class, evaluated at a chosen
representative of the class. -/
noncomputable def rationalCharacterTable :
    irreducibleRationalCharacters G → RatConjClasses G → ℂ :=
  fun ψ c => (ψ : G → ℂ) c.out

end FDRep
