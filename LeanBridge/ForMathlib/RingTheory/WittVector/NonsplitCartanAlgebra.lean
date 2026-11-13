import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPow
import Mathlib.RingTheory.WittVector.Complete

/-!
# The non-split algebra over `ℤ/p^eℤ` as truncated Witt vectors

Let `p` be a prime and `e ≥ 1`. The ring `W_e(𝔽_{p²})` of Witt vectors of length `e` over `𝔽_{p²}`
is the non-split algebra over `ℤ/p^eℤ` (LMFDB `gl2.cartan`). It has `(p²)^e` elements and `p^e = 0`
in it, so it is a `ℤ/p^eℤ`-algebra. The zeroth coefficient `W(𝔽_{p²}) → 𝔽_{p²}` factors through
`W_e(𝔽_{p²})`, giving a surjection `W_e(𝔽_{p²}) → 𝔽_{p²}` whose kernel is `p W_e(𝔽_{p²})`: a Witt
vector over the perfect field `𝔽_{p²}` with zeroth coefficient `0` is a multiple of `p` (Mathlib's
`WittVector.ker_constantCoeff`). The non-split algebra, being formally smooth, therefore lifts to
an isomorphism onto `W_e(𝔽_{p²})`. A ring has at most one `ℤ/p^eℤ`-algebra structure, so this ring
isomorphism is an isomorphism of `ℤ/p^eℤ`-algebras.

## Main results

* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_truncatedWittVector` (LMFDB `gl2.cartan`): the
  non-split algebra `NonsplitCartanAlgebraPow p e` is isomorphic to `W_e(𝔽_{p²})`.
-/

namespace Matrix.GeneralLinearGroup

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

/-- **The non-split algebra is the ring of Witt vectors of length `e` over `𝔽_{p²}`** (LMFDB
`gl2.cartan`): `NonsplitCartanAlgebraPow p e` is isomorphic to
`TruncatedWittVector p e (GaloisField p 2)`. -/
lemma nonempty_ringEquiv_truncatedWittVector :
    Nonempty (NonsplitCartanAlgebraPow p e ≃+* TruncatedWittVector p e (GaloisField p 2)) := by
  have hker : RingHom.ker (WittVector.truncate e : WittVector p (GaloisField p 2) →+* _) ≤
      RingHom.ker WittVector.constantCoeff := fun x hx ↦
    (WittVector.mem_ker_truncate e x).mp hx 0 (Nat.pos_of_ne_zero (NeZero.ne e))
  let g : TruncatedWittVector p e (GaloisField p 2) →+* GaloisField p 2 :=
    (WittVector.truncate e).liftOfSurjective (WittVector.truncate_surjective p e _)
      ⟨WittVector.constantCoeff, hker⟩
  have hg (x : WittVector p (GaloisField p 2)) :
      g (WittVector.truncate e x) = WittVector.constantCoeff x :=
    RingHom.liftOfSurjective_comp_apply _ _ _ x
  have hpe : ((p ^ e : ℕ) : TruncatedWittVector p e (GaloisField p 2)) = 0 := by
    rw [← map_natCast (WittVector.truncate e), ← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro i hi
    rw [Nat.cast_pow]
    exact (WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ e).mp
      (Ideal.mem_span_singleton_self _) i hi
  let _ : Algebra (ZMod (p ^ e)) (TruncatedWittVector p e (GaloisField p 2)) :=
    ZMod.algebra' _ _ (ringChar.dvd hpe)
  let _ : Algebra (ZMod (p ^ e)) (GaloisField p 2) :=
    ZMod.algebra' _ p (dvd_pow_self p (NeZero.ne e))
  let _ : Algebra (ZMod (p ^ e)) (ZMod p) := ZMod.algebra' (ZMod p) p (dvd_pow_self p (NeZero.ne e))
  let _ : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have hcard : Nat.card (TruncatedWittVector p e (GaloisField p 2)) = p ^ (2 * e) := by
    rw [Nat.card_eq_fintype_card, TruncatedWittVector.card, ← Nat.card_eq_fintype_card,
      GaloisField.card p 2 two_ne_zero, ← pow_mul]
  have hsurj : Function.Surjective g := fun y ↦ by
    rcases WittVector.constantCoeff_surjective p y with ⟨x, rfl⟩
    exact ⟨_, hg x⟩
  have hker' (w : TruncatedWittVector p e (GaloisField p 2)) (hw : g.toZModAlgHom (p ^ e) w = 0) :
      ∃ w', w = (p : ZMod (p ^ e)) • w' := by
    rcases WittVector.truncate_surjective p e _ w with ⟨x, rfl⟩
    rw [RingHom.coe_toZModAlgHom, hg, ← RingHom.mem_ker, WittVector.ker_constantCoeff,
      Ideal.mem_span_singleton'] at hw
    rcases hw with ⟨y, rfl⟩
    exact ⟨WittVector.truncate e y, by rw [Algebra.smul_def, map_natCast, map_mul, map_natCast,
      mul_comm]⟩
  rcases nonempty_algEquiv_nonsplitCartanAlgebraPow_of_surjective hcard.ge (g := g.toZModAlgHom _)
    hsurj hker' (RingEquiv.refl _) with ⟨φ⟩
  exact ⟨φ.toRingEquiv⟩

end Matrix.GeneralLinearGroup
