import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Basic

/-!
# Minimal and twist minimal newforms

A newform is *minimal* (LMFDB `cmf.minimal`) if it is not a twist of a newform of lower level, and
*twist minimal* (LMFDB `cmf.twist_minimal`) if its level is the least level in its twist class.
Since twist equivalence is symmetric, the two notions agree, and every twist class contains twist
minimal newforms, which all have the same level.

The level of Tau Ceti's newform `f : HeckeRing.GL2.Newform N k` is `N`, the level of `Γ₁(N)`, as
for the newforms of `S_k^new(N, χ)` in the LMFDB. Twists are taken in the sense of twist
equivalence, `HeckeRing.GL2.Newform.IsTwistEquivalent`.

The LMFDB designates as the *minimal twist* of a twist class its twist minimal newform of minimal
character with the lexicographically least label (LMFDB `cmf.minimal_twist`). That choice is a
database convention and is not formalised.

## Main definitions

* `HeckeRing.GL2.Newform.IsMinimal`: `f` is not a twist of a newform of lower level
  (LMFDB `cmf.minimal`).
* `HeckeRing.GL2.Newform.IsTwistMinimal`: the level of `f` is the least level in its twist class
  (LMFDB `cmf.twist_minimal`).

## Main results

* `HeckeRing.GL2.Newform.isMinimal_iff_isTwistMinimal`: minimal and twist minimal newforms are the
  same.
* `HeckeRing.GL2.Newform.exists_isTwistMinimal`: every twist class contains a twist minimal
  newform.
* `HeckeRing.GL2.Newform.IsTwistMinimal.eq_of_isTwistEquivalent`: twist equivalent twist minimal
  newforms have the same level.
-/

namespace HeckeRing.GL2.Newform

variable {N N' : ℕ} [NeZero N] [NeZero N'] {k : ℤ} {f : Newform N k} {g : Newform N' k}

variable (f) in
/-- A newform `f` of level `N` is **minimal** (LMFDB `cmf.minimal`) if it is not a twist of a
newform of lower level, i.e. if no newform of level less than `N` is twist equivalent to it. Twist
equivalent newforms have the same weight, a theorem that is not proved here, so the newforms of
lower level are taken of the weight of `f`. -/
def IsMinimal : Prop :=
  ¬∃ (L : ℕ+) (g : Newform L k), (L : ℕ) < N ∧ g.IsTwistEquivalent f

variable (f) in
/-- A newform `f` of level `N` is **twist minimal** (LMFDB `cmf.twist_minimal`) if `N` is the least
level of the newforms in its twist class. -/
def IsTwistMinimal : Prop :=
  ∀ x ∈ f.twistClass, N ≤ x.1

/-- **Minimal and twist minimal newforms are the same**: a newform is not a twist of a newform of
lower level exactly when its level is the least in its twist class. -/
lemma isMinimal_iff_isTwistMinimal : f.IsMinimal ↔ f.IsTwistMinimal :=
  ⟨fun hf x hx ↦ not_lt.mp fun hxN ↦ hf ⟨x.1, x.2, hxN, (mem_twistClass.mp hx).symm⟩,
    fun hf ⟨L, g, hL, hgf⟩ ↦ (hf ⟨L, g⟩ hgf.symm).not_gt hL⟩

variable (f) in
/-- **Every twist class contains a twist minimal newform**: one of least level. -/
lemma exists_isTwistMinimal : ∃ x ∈ f.twistClass, x.2.IsTwistMinimal := by
  have hS : N ∈ {L : ℕ | ∃ x ∈ f.twistClass, (x.1 : ℕ) = L} := ⟨_, f.self_mem_twistClass, rfl⟩
  rcases Nat.sInf_mem ⟨_, hS⟩ with ⟨x, hx, hxL⟩
  exact ⟨x, hx, fun y hy ↦ hxL ▸ Nat.sInf_le ⟨y, (mem_twistClass.mp hx).trans hy, rfl⟩⟩

/-- **Twist minimal newforms in a twist class have the same level.** -/
lemma IsTwistMinimal.eq_of_isTwistEquivalent (hf : f.IsTwistMinimal) (hg : g.IsTwistMinimal)
    (hfg : f.IsTwistEquivalent g) : N = N' :=
  (hf ⟨⟨N', NeZero.pos N'⟩, g⟩ hfg).antisymm (hg ⟨⟨N, NeZero.pos N⟩, f⟩ hfg.symm)

end HeckeRing.GL2.Newform
