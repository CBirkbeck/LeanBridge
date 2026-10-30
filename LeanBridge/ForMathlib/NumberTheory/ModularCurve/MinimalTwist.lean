import LeanBridge.ForMathlib.NumberTheory.ModularCurve.CongruenceSubgroupOfOpen

/-!
# Twists and minimal twists of modular curves

Open subgroups `H₁, H₂ ≤ GL₂(ℤ̂)` are twists if `H₁ ∩ SL₂(ℤ̂) = H₂ ∩ SL₂(ℤ̂)`. The minimal twist of
the modular curve `X_H` of an open subgroup `H` with `det(H) = ℤ̂ˣ` is the modular curve whose label
is minimal among those of the twists `H'` of `H` with `det(H') = ℤ̂ˣ`.

Twists with `det = ℤ̂ˣ` have the same index (`Matrix.GeneralLinearGroup.IsTwist.index_eq`), since
for such a twist `H'` the index of `H'` in `GL₂(ℤ̂)` is that of `H' ∩ SL₂(ℤ̂)` in `SL₂(ℤ̂)`. The
label `N.i.g.c.n` (or `N.i.g-M.c.m.n`, see `LeanBridge.ForMathlib.NumberTheory.ModularCurve.Label`)
starts with the level `N`, and the knowl says that the minimal twist has the least level among
these twists; it does not say how labels are compared beyond that. Among the twists of least level,
which have the same index (and the same genus, which is not formalised), the minimal twist is
singled out by the remaining entries of its label: the ordinals `c` and `n` when `-I ∈ H`, and when
`-I ∉ H` (then `-I`, which lies in `SL₂(ℤ̂)`, lies in no twist of `H`) the level `M` of
`⟨H', -I⟩`, which is mathematical, and the ordinals `c`, `m` and `n`. The ordinals are LMFDB
database numberings that the knowl does not specify, and so is the order in which the entries are
compared after the level: there is nothing more to formalise in this choice. The mathematically
defined part of the notion is formalised: the twists of `H` with `det = ℤ̂ˣ` of least level, one of
which is the minimal twist. That the modular curves of twists `H₁` and `H₂` become isomorphic over
every cyclotomic field `ℚ(ζ_n)` with `n` divisible by the levels of `H₁` and `H₂` is not formalised.

As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product
`∏_ℓ GL₂(ℤ_ℓ)`, and `det(H) = ℤ̂ˣ` is written `H.map adelicDet = ⊤`.

## Main definitions

* `Matrix.GeneralLinearGroup.IsTwist` (LMFDB `modcurve.minimal_twist`): twists.
* `Matrix.GeneralLinearGroup.fullDetTwists`: the open twists `H'` of `H` with `det(H') = ℤ̂ˣ`.
* `Matrix.GeneralLinearGroup.minimalTwistLevel` (LMFDB `modcurve.minimal_twist`): their least
  level, the level of the minimal twist.
* `Matrix.GeneralLinearGroup.IsMinimalLevelTwist` (LMFDB `modcurve.minimal_twist`): the twists
  with `det = ℤ̂ˣ` of least level, among which the minimal twist is chosen.

## Main results

* `Matrix.GeneralLinearGroup.isTwist_equivalence`: being twists is an equivalence relation.
* `Matrix.GeneralLinearGroup.index_eq_relIndex_adelicSL`: for `det(H) = ℤ̂ˣ`, the index of `H` in
  `GL₂(ℤ̂)` is that of `H ∩ SL₂(ℤ̂)` in `SL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.IsTwist.index_eq`: twists with `det = ℤ̂ˣ` have the same index.
* `Matrix.GeneralLinearGroup.exists_isMinimalLevelTwist`: an open subgroup with `det(H) = ℤ̂ˣ` has
  a twist with `det = ℤ̂ˣ` of least level.
-/

open MulAction

namespace Matrix.GeneralLinearGroup

variable (H : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))
  {H₁ H₂ : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])}

variable (H₁ H₂) in
/-- Two subgroups `H₁` and `H₂` of `GL₂(ℤ̂)` are **twists** (LMFDB `modcurve.minimal_twist`) if
`H₁ ∩ SL₂(ℤ̂) = H₂ ∩ SL₂(ℤ̂)`. The LMFDB applies this to open subgroups, whose modular curves
`X_{H₁}` and `X_{H₂}` are then isomorphic over the cyclotomic fields `ℚ(ζ_n)` with `n` divisible by
the levels of `H₁` and `H₂` (not formalised). -/
def IsTwist : Prop :=
  H₁ ⊓ adelicSL = H₂ ⊓ adelicSL

/-- **Being twists is an equivalence relation** on the subgroups of `GL₂(ℤ̂)`. -/
lemma isTwist_equivalence : Equivalence IsTwist :=
  ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- The **twists with full determinant** of a subgroup `H` of `GL₂(ℤ̂)`: the open subgroups `H'` of
`GL₂(ℤ̂)` with `det(H') = ℤ̂ˣ` that are twists of `H` (LMFDB `modcurve.minimal_twist`). -/
def fullDetTwists : Set (Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) :=
  {H' | IsOpen (H' : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) ∧ H'.map adelicDet = ⊤ ∧
    IsTwist H H'}

/-- The **level of the minimal twist** (LMFDB `modcurve.minimal_twist`) of a subgroup `H` of
`GL₂(ℤ̂)`: the least level of an open twist `H'` of `H` with `det(H') = ℤ̂ˣ`, and `0` when there is
none. -/
noncomputable def minimalTwistLevel : ℕ :=
  sInf (adelicLevel ⊤ '' fullDetTwists H)

variable (H₂) in
/-- `H₂` is a **twist of least level** of `H` (LMFDB `modcurve.minimal_twist`): an open twist of
`H` with `det(H₂) = ℤ̂ˣ` whose level is the least level of such twists. The minimal twist of `X_H`
is the modular curve of one of them, chosen by the remaining entries of the LMFDB labels (the level
of `⟨H₂, -I⟩` when `-I ∉ H`, and database numberings), compared in an order that the knowl does not
specify. -/
def IsMinimalLevelTwist : Prop :=
  H₂ ∈ fullDetTwists H ∧ adelicLevel ⊤ H₂ = minimalTwistLevel H

lemma minimalTwistLevel_le (h : H₂ ∈ fullDetTwists H) : minimalTwistLevel H ≤ adelicLevel ⊤ H₂ :=
  Nat.sInf_le ⟨H₂, h, rfl⟩

/-- **An open subgroup `H` of `GL₂(ℤ̂)` with `det(H) = ℤ̂ˣ` has a twist of least level** among its
open twists with `det = ℤ̂ˣ`. -/
lemma exists_isMinimalLevelTwist (hH : IsOpen (H : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])))
    (hdet : H.map adelicDet = ⊤) : ∃ H', IsMinimalLevelTwist H H' := by
  have hne : (fullDetTwists H).Nonempty := ⟨H, hH, hdet, rfl⟩
  exact Nat.sInf_mem (hne.image _)

lemma isPretransitive_adelicSL (hdet : H.map adelicDet = ⊤) :
    IsPretransitive adelicSL ((∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) := by
  refine ⟨fun x y ↦ ?_⟩
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  rcases Subgroup.mem_map.mp (hdet ▸ Subgroup.mem_top (adelicDet (a * b⁻¹))) with ⟨h, hh, hdeth⟩
  refine ⟨⟨b * h * a⁻¹, ?_⟩, ?_⟩
  · rw [adelicSL, MonoidHom.mem_ker, map_mul, map_mul, map_inv, hdeth, map_mul, map_inv,
      mul_inv_eq_one, mul_comm, inv_mul_cancel_right]
  · rw [Subgroup.mk_smul, Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, inv_mul_cancel_right]
    simpa using inv_mem hh

/-- **For `det(H) = ℤ̂ˣ`, the index of `H` in `GL₂(ℤ̂)` is that of `H ∩ SL₂(ℤ̂)` in `SL₂(ℤ̂)`**:
`SL₂(ℤ̂)` acts transitively on `GL₂(ℤ̂) / H`, with stabilizer `H ∩ SL₂(ℤ̂)` at the coset `H`. -/
lemma index_eq_relIndex_adelicSL (hdet : H.map adelicDet = ⊤) : H.index = H.relIndex adelicSL := by
  have : IsPretransitive adelicSL ((∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) ⧸ H) :=
    isPretransitive_adelicSL H hdet
  rw [Subgroup.index_eq_card, ← index_stabilizer_of_transitive adelicSL
    (QuotientGroup.mk 1 : _ ⧸ H), ← stabilizer_subgroupOf, stabilizer_quotient, Subgroup.relIndex]

/-- **Twists with full determinant have the same index**: for twists `H₁` and `H₂` with
`det(H₁) = det(H₂) = ℤ̂ˣ`, the index of each is that of `H₁ ∩ SL₂(ℤ̂) = H₂ ∩ SL₂(ℤ̂)` in
`SL₂(ℤ̂)`. -/
lemma IsTwist.index_eq (h : IsTwist H₁ H₂) (h₁ : H₁.map adelicDet = ⊤) (h₂ : H₂.map adelicDet = ⊤) :
    H₁.index = H₂.index := by
  rw [index_eq_relIndex_adelicSL H₁ h₁, index_eq_relIndex_adelicSL H₂ h₂,
    ← Subgroup.inf_relIndex_right, h, Subgroup.inf_relIndex_right]

end Matrix.GeneralLinearGroup
