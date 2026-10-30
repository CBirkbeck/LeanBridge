import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Conductor
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.ComplexMultiplication.Basic

/-!
# The conductor and CM parts of the labels of elliptic curves

The LMFDB labels an elliptic curve `E` over a number field `K` by `N.a1` (LMFDB `ec.curve_label`),
where `N` is the label of its conductor, `a` the label of its isogeny class and `1` the index of
`E` in its isogeny class, and prefixes the label of `K` to obtain a full label, such as the knowl's
`3.1.23.1-89.1-A1`. The label `N.i` of the conductor (LMFDB `ec.conductor_label`), an integral
ideal of `K`, is its norm `N` followed by the index `i` of the conductor in a list of the integral
ideals of norm `N`. The Cremona label of an elliptic curve over `ℚ` (LMFDB `ec.q.cremona_label`),
such as `11a1` or `10050bf2`, consists of its conductor, letters for its isogeny class and the
number of the curve in its class.

Several of these components are numberings of the databases that the knowls do not define, and they
are not formalised: the order of the integral ideals of a given norm, recorded in the database
except over imaginary quadratic fields, the order of the curves in an isogeny class over a number
field, and Cremona's orders of isogeny classes and of the curves in a class, which follow the order
in which they were computed. As the knowl `ec.q.cremona_label` states, Cremona's isogeny class
letters agree with those of the LMFDB label for conductors over `230000`: there they are
`WeierstrassCurve.isogenyClassLetters` of `WeierstrassCurve.lmfdbIsogenyClassIndex`. Two components
are described by the knowls but rest on what is not available here: over imaginary quadratic fields
the order of the ideals of a given norm is the standard labelling of ideals (LMFDB
`nf.ideal_labels`), and the order of the isogeny classes over a number field is based on the
lexicographic order of the Dirichlet coefficients of their L-series, for the standard order of the
primes of `K`, and matches the labels of the associated modular forms where possible. What is
formalised here is:

* the norm `N` of the conductor, the conductor norm of LMFDB `ec.conductor`; over `ℚ`, `N` is the
  conductor at the start of the Cremona label and of the LMFDB label `WeierstrassCurve.lmfdbLabel`
  (LMFDB `ec.q.lmfdb_label`). Only finitely many integral ideals have norm `N` (Mathlib's
  `Ideal.finite_setOfPred_absNorm_eq`), so that the index `i` of the conductor in a list of them is
  a positive integer;
* the prefix `CM` of the isogeny class label of a curve over an imaginary quadratic field `K` with
  complex multiplication by an order of `K`.

The knowl `ec.q.cremona_label` also states that the curve numbered `1` in each isogeny class is the
`Γ₀(N)`-optimal curve. That needs the modular parametrisation `X₀(N) → E`, which is not available,
and it fails for the class `990h`, whose optimal curve is `990h3` (LMFDB `ec.q.optimal`).

## Main definitions

* `WeierstrassCurve.conductorNorm` (LMFDB `ec.conductor_label`, `ec.curve_label`,
  `ec.q.cremona_label`): the norm of the conductor.
* `WeierstrassCurve.HasCMLabelPrefix` (LMFDB `ec.curve_label`): the isogeny class label of a curve
  over an imaginary quadratic field has the prefix `CM`.
-/

open IsDedekindDomain IsLocalRing NumberField

namespace WeierstrassCurve

variable (O : Type*) [CommRing O] [IsDedekindDomain O] [Infinite O]
  [∀ v : HeightOneSpectrum O, PerfectField (ResidueField (Localization.AtPrime v.asIdeal))]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- The **conductor norm** (LMFDB `ec.conductor`; the norm `N` of LMFDB `ec.conductor_label` and
`ec.curve_label`, and the conductor of `ec.q.cremona_label`) of an elliptic curve `W` over the
fraction field `K` of a Dedekind domain `O`: the absolute norm `[O : 𝔑]` of its conductor `𝔑`, Tau
Ceti's algorithmic conductor `WeierstrassCurve.algorithmicConductor`, which is the conductor by
Ogg's formula. For a number field `K` and `O = 𝓞 K` it is the norm `N` that begins the conductor
label `N.i`, and for `K = ℚ` and `O = ℤ` it is the conductor that begins the Cremona label. -/
noncomputable def conductorNorm : ℕ :=
  Ideal.absNorm (algorithmicConductor O W)

lemma conductorNorm_smul (C : VariableChange K) : (C • W).conductorNorm O = W.conductorNorm O := by
  rw [conductorNorm, conductorNorm, algorithmicConductor_smul]

variable [Module.Free ℤ O] [Module.Finite ℤ O] in
lemma conductorNorm_pos : 0 < W.conductorNorm O :=
  Nat.pos_of_ne_zero <| Ideal.absNorm_eq_zero_iff.not.mpr <| algorithmicConductor_ne_bot O W

variable [NumberField K] in
/-- The isogeny class label of an elliptic curve `W` over a number field `K` **has the prefix `CM`**
(LMFDB `ec.curve_label`) if `K` is imaginary quadratic and `W` has complex multiplication by an
order of `K`: its endomorphism ring over `K` is larger than `ℤ` (`WeierstrassCurve.HasCM`, LMFDB
`ec.complex_multiplication`). Over an imaginary quadratic field `K` this is complex multiplication
by an order of `K` itself, as the endomorphism ring over `K` acts on the invariant differentials,
a `K`-vector space of dimension one, which embeds its fraction field, the CM field, into `K` (not
formalised here). Isogenous curves share this property (not formalised here either), so that the
prefix belongs to the isogeny class. The Bianchi modular forms conjecturally attached to these
curves are not cuspidal, which is why the LMFDB marks them. -/
def HasCMLabelPrefix : Prop :=
  IsTotallyComplex K ∧ Module.finrank ℚ K = 2 ∧ W.HasCM

end WeierstrassCurve
