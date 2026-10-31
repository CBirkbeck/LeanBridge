import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.GaloisOrbitLabel
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisStability
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.PiLex

/-!
# The letter labels of the Galois orbits of newforms

The LMFDB labels the Galois orbits of newforms (LMFDB `cmf.galois_orbit`) in a space of newforms
`S_k^{new}(N, [χ])` with letters (LMFDB `cmf.hecke_galois_orbit`): the orbits of the space are
ordered by the lexicographic order of their trace sequences `(Tr(a₁), Tr(a₂), Tr(a₃), …)`, where
`Tr` is the trace from the coefficient field down to `ℚ`, and the orbit in position `i`, counted
from `0`, is labelled by the letter code of `i` (`DirichletCharacter.letterCode`). The traces are
rational integers in weight at least two (`HeckeRing.GL2.Newform.exists_int_coeffTrace`); they are
kept in `ℚ`, whose order agrees with that of `ℤ`.

The space `S_k^{new}(N, [χ])` is the sum of the spaces `S_k^{new}(N, χ')` over the characters `χ'`
in the Galois orbit `[χ]` of `χ` (Tau Ceti's `MulChar.galoisOrbit`), so the newform orbits in it
are those whose nebentypus lies in `[χ]`. Galois conjugate newforms have Galois conjugate
nebentypus, so `[χ]` is an invariant of the newform orbit
(`HeckeRing.GL2.NewformOrbit.characterOrbit`).

The position of an orbit is the number of orbits of its space with a smaller trace sequence. It
is a strictly increasing function of the trace sequence on the orbits of a space, smaller than
their number. Distinct orbits have distinct trace sequences as soon as every Galois conjugate of a
newform is a newform (LeanBridge issue #38), and so distinct orbits of a space then have distinct
labels, the labels of the `m` orbits of a space being the letter codes of `0, …, m - 1`; this is
proved here under the hypothesis `TauCeti.HasRationalHeckeForm`, equivalent to issue #38 in weight
at least two, not unconditionally. The letter code itself is injective
(`DirichletCharacter.letterCode_injective`).

The knowl lists the labels as `a, b, c, …, z, aa, ba, …`; the letter code writes `25, 26, 27` as
`z, ba, bb`, and `aa` does not occur.

## Main definitions

* `HeckeRing.GL2.NewformOrbit.characterOrbit`: the Galois orbit `[χ]` of the nebentypus of a newform
  orbit, which determines its space of newforms `S_k^{new}(N, [χ])`.
* `HeckeRing.GL2.NewformOrbit.traceSeq`: the trace sequence `(Tr(a₁), Tr(a₂), …)` of a newform
  orbit, in the lexicographic order (LMFDB `cmf.hecke_galois_orbit`).
* `HeckeRing.GL2.NewformOrbit.labelIndex`: the position of a newform orbit in its space
  (LMFDB `cmf.hecke_galois_orbit`).
* `HeckeRing.GL2.NewformOrbit.letterLabel`: the letter label of a newform orbit
  (LMFDB `cmf.hecke_galois_orbit`).

## Main results

* `DirichletCharacter.letterCode_injective`: the letter code is injective.
* `HeckeRing.GL2.Newform.exists_int_coeffTrace`: in weight at least two the traces `Tr(aₙ)` are
  integers.
* `HeckeRing.GL2.NewformOrbit.labelIndex_lt_labelIndex`: within a space, an orbit with a smaller
  trace sequence has a smaller position.
* `HeckeRing.GL2.NewformOrbit.labelIndex_lt_ncard`: the position of an orbit is smaller than the
  number of orbits of its space.
* `HeckeRing.GL2.NewformOrbit.traceSeq_injective_of_hasRationalHeckeForm`: in weight at least two,
  if the rational Hecke algebra is a `ℚ`-form, distinct orbits have distinct trace sequences.
* `HeckeRing.GL2.NewformOrbit.labelIndex_eq_iff_of_hasRationalHeckeForm`,
  `HeckeRing.GL2.NewformOrbit.letterLabel_eq_iff_of_hasRationalHeckeForm`: then distinct orbits of
  a space have distinct positions and distinct letter labels.
* `HeckeRing.GL2.NewformOrbit.image_labelIndex_of_hasRationalHeckeForm`: then the positions of the
  `m` orbits of a space are `0, …, m - 1`.
-/

open UpperHalfPlane TauCeti

namespace DirichletCharacter

variable {n : ℕ}

variable (n) in
lemma toList_letterCode : (letterCode n).toList = if n = 0 then ['a'] else
    (Nat.digits 26 n).reverse.map fun d ↦ Char.ofNat (97 + d) := by
  unfold letterCode
  split_ifs
  · rfl
  · exact String.toList_ofList

lemma letterCode_decode : ∀ d : Fin 26, (Char.ofNat (97 + d)).toNat - 97 = d := by
  decide

lemma map_decode_letterCode (l : List ℕ) (hl : ∀ d ∈ l, d < 26) :
    (l.map fun d ↦ Char.ofNat (97 + d)).map (fun c ↦ c.toNat - 97) = l := by
  rw [List.map_map]
  refine (List.map_congr_left fun d hd ↦ ?_).trans (List.map_id l)
  exact letterCode_decode ⟨d, hl d hd⟩

lemma map_toList_letterCode (hn : n ≠ 0) :
    (letterCode n).toList.map (fun c ↦ c.toNat - 97) = (Nat.digits 26 n).reverse := by
  rw [toList_letterCode, ite_eq_right hn, map_decode_letterCode _ fun d hd ↦
    Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd)]

lemma eq_zero_of_letterCode_eq_a (h : letterCode n = "a") : n = 0 := by
  by_contra hn
  have h₁ : (Nat.digits 26 n).reverse = [0] := by
    rw [← map_toList_letterCode hn, h]
    rfl
  have h₂ : Nat.digits 26 n = [0] := by
    simpa using congrArg List.reverse h₁
  exact hn <| by rw [← Nat.ofDigits_digits 26 n, h₂, Nat.ofDigits_singleton]

/-- **The letter code is injective**: distinct natural numbers have distinct letter codes, the
letters `a, …, z` being the digits `0, …, 25` of the base-`26` expansion. -/
lemma letterCode_injective : Function.Injective letterCode := by
  intro m n h
  rcases eq_or_ne m 0 with rfl | hm
  · exact (eq_zero_of_letterCode_eq_a h.symm).symm
  rcases eq_or_ne n 0 with rfl | hn
  · exact eq_zero_of_letterCode_eq_a h
  exact Nat.digits_inj_iff.mp <| List.reverse_injective <| (map_toList_letterCode hm).symm.trans <|
    (congrArg (fun s : String ↦ s.toList.map fun c ↦ c.toNat - 97) h).trans
      (map_toList_letterCode hn)

end DirichletCharacter

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace Newform

variable {f g : Newform N k} {σ : Gal(ℂ/ℚ)}

lemma IsGaloisConjugateBy.dirichletLift_apply (hfg : f.IsGaloisConjugateBy σ g) (x : ZMod N) :
    g.dirichletLift x = σ (f.dirichletLift x) :=
  dirichletLift_apply_eq_of_forall_χ hfg.χ_apply x

lemma IsGaloisConjugateBy.dirichletLift_mem_galoisOrbit (hfg : f.IsGaloisConjugateBy σ g) :
    g.dirichletLift ∈ f.dirichletLift.galoisOrbit :=
  MulChar.mem_galoisOrbit_iff_exists_algHom.mpr
    ⟨(σ : ℂ →ₐ[ℚ] ℂ).comp (IntermediateField.val _), hfg.dirichletLift_apply⟩

lemma IsGaloisConjugate.galoisOrbit_dirichletLift_eq (hfg : f.IsGaloisConjugate g) :
    g.dirichletLift.galoisOrbit = f.dirichletLift.galoisOrbit :=
  hfg.elim fun _ hσ ↦ MulChar.galoisOrbit_eq_galoisOrbit_iff.mpr hσ.dirichletLift_mem_galoisOrbit

variable (f) in
/-- **The traces of the coefficients of a newform are integers** in weight at least two: the
coefficients are algebraic integers. -/
lemma exists_int_coeffTrace (hk : 2 ≤ k) (n : ℕ) : ∃ m : ℤ, f.coeffTrace n = m := by
  have : NumberField (CoefficientField f) := numberField_CoefficientField f hk
  have hn : IsIntegral ℤ (f.orbitQExpansion.coeff n) :=
    (isIntegral_algHom_iff (CoefficientField f).val.toIntAlgHom Subtype.val_injective).mp <| by
      simpa using f.isIntegral_qExpansion_coeff hk n
  rcases IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hn) with ⟨m, hm⟩
  exact ⟨m, by rw [coeffTrace, ← hm, eq_intCast]⟩

end Newform

namespace NewformOrbit

variable (O : NewformOrbit N k) {O' : NewformOrbit N k}

/-- The **Galois orbit `[χ]` of the nebentypus** of a newform orbit
(LMFDB `cmf.hecke_galois_orbit`): the Galois orbit of the nebentypus of any of its newforms, as
Dirichlet characters, which does not depend on the newform. The newform orbit lies in the space of
newforms `S_k^{new}(N, [χ])`. -/
noncomputable def characterOrbit : Set (DirichletCharacter ℂ N) :=
  Quotient.lift (fun f : Newform N k ↦ f.dirichletLift.galoisOrbit)
    (fun (f g : Newform N k) (h : f.IsGaloisConjugate g) ↦ h.galoisOrbit_dirichletLift_eq.symm) O

/-- The **trace sequence** `(Tr(a₁), Tr(a₂), Tr(a₃), …)` of a newform orbit
(LMFDB `cmf.hecke_galois_orbit`), where `Tr` is the trace from the coefficient field to `ℚ`, as an
element of the sequences `ℕ → ℚ` with the lexicographic order. It is indexed from `0`, the term
of index `n` being `Tr(aₙ₊₁)`, and does not depend on the newform of the orbit. -/
noncomputable def traceSeq : Lex (ℕ → ℚ) :=
  Quotient.lift (fun f : Newform N k ↦ toLex fun n ↦ f.coeffTrace (n + 1))
    (fun (f g : Newform N k) (h : f.IsGaloisConjugate g) ↦
      congrArg toLex (funext fun n ↦ h.coeffTrace_eq (n + 1))) O

/-- The **position** of a newform orbit in its space of newforms `S_k^{new}(N, [χ])`
(LMFDB `cmf.hecke_galois_orbit`), counted from `0`: the number of newform orbits of the same space
whose trace sequence is lexicographically smaller. -/
noncomputable def labelIndex : ℕ :=
  {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit ∧ O'.traceSeq < O.traceSeq}.ncard

/-- The **letter label** of a newform orbit in its space of newforms
(LMFDB `cmf.hecke_galois_orbit`): the letter code `a, b, …, z, ba, bb, …` of its position, the
orbits of the space being ordered by their trace sequences. -/
noncomputable def letterLabel : String :=
  DirichletCharacter.letterCode O.labelIndex

variable (f : Newform N k)

lemma characterOrbit_newformOrbit : f.newformOrbit.characterOrbit = f.dirichletLift.galoisOrbit :=
  rfl

lemma traceSeq_newformOrbit : f.newformOrbit.traceSeq = toLex fun n ↦ f.coeffTrace (n + 1) :=
  rfl

/-- **Within a space of newforms, a smaller trace sequence gives a smaller position.** -/
lemma labelIndex_lt_labelIndex (h : O'.characterOrbit = O.characterOrbit)
    (hlt : O'.traceSeq < O.traceSeq) : O'.labelIndex < O.labelIndex :=
  Set.ncard_lt_ncard ⟨fun _ hO ↦ ⟨hO.1.trans h, hO.2.trans hlt⟩,
    fun hsub ↦ (hsub ⟨h, hlt⟩).2.false⟩ (Set.toFinite _)

/-- **The position of a newform orbit is smaller than the number of orbits of its space.** -/
lemma labelIndex_lt_ncard :
    O.labelIndex < {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}.ncard :=
  Set.ncard_lt_ncard ⟨fun _ hO ↦ hO.1, fun hsub ↦ (hsub rfl).2.false⟩ (Set.toFinite _)

/-- **Distinct newform orbits have distinct trace sequences, if the rational Hecke algebra is a
`ℚ`-form**, in weight at least two: then every Galois conjugate of a newform is a newform, and the
traces of the coefficients distinguish the Galois orbits. -/
lemma traceSeq_injective_of_hasRationalHeckeForm (hk : 2 ≤ k) (hH : HasRationalHeckeForm N k) :
    Function.Injective (traceSeq (N := N) (k := k)) := by
  intro O O'
  induction O using Quotient.inductionOn with | h f =>
  induction O' using Quotient.inductionOn with | h g =>
  intro h
  refine Quotient.sound <| Newform.isGaloisConjugate_of_coeffTrace_eq hk
    (fun f σ ↦ Newform.exists_isGaloisConjugateBy_of_hasRationalHeckeForm f σ hH) fun n hn ↦ ?_
  have hfg : f.coeffTrace (n - 1 + 1) = g.coeffTrace (n - 1 + 1) :=
    congrFun (toLex.injective h) (n - 1)
  rwa [Nat.sub_add_cancel hn] at hfg

/-- **Distinct newform orbits of a space have distinct positions, if the rational Hecke algebra is
a `ℚ`-form**, in weight at least two. -/
lemma labelIndex_eq_iff_of_hasRationalHeckeForm (hk : 2 ≤ k) (hH : HasRationalHeckeForm N k)
    (h : O'.characterOrbit = O.characterOrbit) : O'.labelIndex = O.labelIndex ↔ O' = O := by
  refine ⟨fun hO ↦ ?_, fun hO ↦ hO ▸ rfl⟩
  rcases lt_trichotomy O'.traceSeq O.traceSeq with hlt | heq | hgt
  · exact absurd hO (labelIndex_lt_labelIndex O h hlt).ne
  · exact traceSeq_injective_of_hasRationalHeckeForm hk hH heq
  · exact absurd hO (labelIndex_lt_labelIndex O' h.symm hgt).ne'

/-- **Distinct newform orbits of a space have distinct letter labels, if the rational Hecke algebra
is a `ℚ`-form**, in weight at least two: their positions are distinct, and the letter code is
injective. -/
lemma letterLabel_eq_iff_of_hasRationalHeckeForm (hk : 2 ≤ k) (hH : HasRationalHeckeForm N k)
    (h : O'.characterOrbit = O.characterOrbit) : O'.letterLabel = O.letterLabel ↔ O' = O :=
  DirichletCharacter.letterCode_injective.eq_iff.trans <|
    labelIndex_eq_iff_of_hasRationalHeckeForm O hk hH h

/-- **The positions of the newform orbits of a space are `0, …, m - 1`**, where `m` is the number
of orbits of the space, if the rational Hecke algebra is a `ℚ`-form, in weight at least two: the
orbits of a space of newforms are labelled by the letter codes of `0, …, m - 1`. -/
lemma image_labelIndex_of_hasRationalHeckeForm (hk : 2 ≤ k) (hH : HasRationalHeckeForm N k) :
    labelIndex '' {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit} =
      Set.Iio {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}.ncard := by
  have hmaps : Set.MapsTo labelIndex {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}
      (Set.Iio {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit}.ncard) :=
    fun O' hO' ↦ (labelIndex_lt_ncard O').trans_eq <| by rw [Set.mem_ofPred_eq.mp hO']
  have hinj : Set.InjOn labelIndex {O' : NewformOrbit N k | O'.characterOrbit = O.characterOrbit} :=
    fun O₁ h₁ O₂ h₂ h ↦ (labelIndex_eq_iff_of_hasRationalHeckeForm O₂ hk hH
      ((Set.mem_ofPred_eq.mp h₁).trans (Set.mem_ofPred_eq.mp h₂).symm)).mp h
  refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmaps) ?_ (Set.toFinite _)
  rw [hinj.ncard_image, Set.ncard_Iio_nat]

end NewformOrbit

end HeckeRing.GL2
