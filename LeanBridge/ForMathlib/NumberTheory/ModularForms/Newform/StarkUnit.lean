import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.GaloisRepresentation
import TauCeti.NumberTheory.LSeries.EntireExtension
import TauCeti.NumberTheory.ModularForms.LFunction.Basic

/-!
# Stark units of newforms of weight one

Let `f = ∑ aₙ qⁿ` be a newform of weight one, `E = ℚ(aₙ)` its coefficient field,
`Δ = Gal(E / ℚ)` and `f^α = ∑ α(aₙ) qⁿ` for `α ∈ Δ`. Stark's conjecture for the Galois
representation of `f`, in Stark's formulation for weight-one forms, says that for every `b ∈ E^×`
there are an integer `m ≥ 1` and a unit `ε` of the Artin field of `f`, the Stark unit, with
`exp(m ∑_{α ∈ Δ} α(b) L'(0, f^α)) = ε`; Chinburg conjectured that `m = 1` works when the
coefficients of `Tr(b f)` are integers, as for `b = 1`, and the LMFDB computes the Stark unit for
`b = m = 1`.

The value `L'(0, f^α)` depends only on the coefficients `α(aₙ)`: it is the derivative at `0` of
the entire continuation of the Dirichlet series `∑ α(aₙ) n^{-s}` (Tau Ceti's
`LSeries.HasEntireExtension`, which determines it uniquely). This continuation exists, and is the
L-function of the cusp form `f^α`, as soon as `f^α` is a newform
(`HeckeRing.GL2.Newform.galoisConjLFunction_eq_L`), as it is for `α = 1`. That every Galois
conjugate of a newform is a newform (LeanBridge issue #38) is not proved, so for `α ≠ 1` the
existence of the continuation is not known here: `L(s, f^α)` is defined to be `0` when there is
none, a junk value that does not occur but is not excluded. Likewise the sum over `Δ` is `0` if the
coefficient field has infinite degree, which does not happen (it is an abelian number field) but is
not proved in weight one. So the values below are those of the LMFDB only up to these two unproved
facts. Stark's conjecture itself is not proved: the Stark unit is defined as a property of a unit
of the Artin field (`HeckeRing.GL2.Newform.IsStarkUnit`), the Artin field being that of a given
Galois representation of `f` (whose existence is the Deligne–Serre theorem), and the number
computed by the LMFDB as the complex number `exp(∑_{α ∈ Δ} L'(0, f^α))`
(`HeckeRing.GL2.Newform.starkUnit`).

## Main definitions

* `HeckeRing.GL2.Newform.galoisConjCoeff`: the coefficients `α(aₙ)` of `f^α`.
* `HeckeRing.GL2.Newform.galoisConjLFunction`: the L-function `L(s, f^α)`.
* `HeckeRing.GL2.Newform.starkValue` (LMFDB `cmf.stark_unit`):
  `exp(m ∑_{α ∈ Δ} α(b) L'(0, f^α))`.
* `HeckeRing.GL2.Newform.IsStarkUnit` (LMFDB `cmf.stark_unit`): a unit of the Artin field is a
  Stark unit of `f` for `b` and `m`.
* `HeckeRing.GL2.Newform.starkUnit` (LMFDB `cmf.stark_unit`): the Stark unit for `b = m = 1`, as
  a complex number.

## Main results

* `HeckeRing.GL2.Newform.galoisConjLFunction_eq_L`: if `f^α` is a newform, `L(s, f^α)` is its
  entire L-function.
* `HeckeRing.GL2.Newform.galoisConjLFunction_eq_L_of_isGaloisConjugateBy`: the same for a Galois
  conjugate `σ(f)` of `f` by an automorphism `σ` of `ℂ` extending `α`.
* `HeckeRing.GL2.Newform.galoisConjLFunction_one`: `L(s, f^1)` is the L-function of `f`.
-/

open UpperHalfPlane TauCeti NumberField

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] (f : Newform N 1) (α : CoefficientField f ≃ₐ[ℚ] CoefficientField f)

/-- The coefficients `α(aₙ)` of the Galois conjugate `f^α = ∑ α(aₙ) qⁿ` of a newform `f` of weight
one by an automorphism `α` of its coefficient field `E = ℚ(aₙ)` (LMFDB `cmf.stark_unit`). -/
noncomputable def galoisConjCoeff (n : ℕ) : ℂ :=
  α ⟨(qExpansion 1 f.toCuspForm).coeff n, f.qExpansion_coeff_mem_coefficientField n⟩

open Classical in
/-- The **L-function** `L(s, f^α)` (LMFDB `cmf.lfunction`, `cmf.stark_unit`) of the Galois conjugate
`f^α` of a newform `f` of weight one: the entire continuation of the Dirichlet series
`∑ α(aₙ) n^{-s}`, unique when it exists (`LSeries.HasEntireExtension.unique`), and `0` otherwise.
It exists, and is the L-function of `f^α`, when `f^α` is a newform (`galoisConjLFunction_eq_L`); in
weight one the arithmetic and analytic normalisations agree. That `f^α` is always a newform
(LeanBridge issue #38) is not proved, so for `α ≠ 1` the junk value `0` is not excluded. -/
noncomputable def galoisConjLFunction : ℂ → ℂ :=
  if h : LSeries.HasEntireExtension (f.galoisConjCoeff α) then h.exists_extension.choose else 0

/-- The **Stark value** `exp(m ∑_{α ∈ Δ} α(b) L'(0, f^α))` (LMFDB `cmf.stark_unit`) of a newform `f`
of weight one, for `b` in its coefficient field `E` and an integer `m`, with `Δ = Gal(E / ℚ)` and
`L(s, f^α)` as in `galoisConjLFunction`. The sum is `0` if `Δ` were infinite; `E` is a number field
(an abelian one, in weight one), which is not proved here. Stark's conjecture predicts that for
`b ≠ 0` and some `m ≥ 1` it is a unit of the Artin field of `f` (`IsStarkUnit`). -/
noncomputable def starkValue (b : CoefficientField f) (m : ℕ) : ℂ :=
  Complex.exp (m * ∑ᶠ α : CoefficientField f ≃ₐ[ℚ] CoefficientField f,
    (α b : ℂ) * deriv (f.galoisConjLFunction α) 0)

/-- A unit `ε` of the Artin field of a newform `f` of weight one is a **Stark unit** of `f` for `b`
and `m` (LMFDB `cmf.stark_unit`) if `exp(m ∑_{α ∈ Δ} α(b) L'(0, f^α)) = ε` (`starkValue`) for an
embedding of the Artin field into `ℂ`. The Artin field is that of a Galois representation `ρ`
attached to `f` (`GaloisRep.artinField`); it is Galois over `ℚ`, so its image in `ℂ` does not
depend on the embedding. Stark's conjecture says that for every `b ≠ 0` there are `m ≥ 1` and a
Stark unit, Chinburg's that `m = 1` suffices for `b = 1`. -/
def IsStarkUnit (ρ : f.GaloisRep) (b : CoefficientField f) (m : ℕ) (ε : (𝓞 ρ.artinField)ˣ) : Prop :=
  ∃ ι : ρ.artinField →ₐ[ℚ] ℂ, ι (ε : 𝓞 ρ.artinField) = f.starkValue b m

/-- The **Stark unit** (LMFDB `cmf.stark_unit`) of a newform `f` of weight one as the LMFDB
computes it, for `b = m = 1`: the complex number `exp(∑_{α ∈ Δ} L'(0, f^α))`, conjecturally (Stark,
Chinburg) the image of a Stark unit of `f` in `ℂ` (`IsStarkUnit`). -/
noncomputable def starkUnit : ℂ :=
  f.starkValue 1 1

variable {f α} {g : Newform N 1}

lemma hasEntireExtension_galoisConjCoeff
    (hg : ∀ n, (qExpansion 1 g.toCuspForm).coeff n = f.galoisConjCoeff α n) :
    LSeries.HasEntireExtension (f.galoisConjCoeff α) := by
  rw [← funext hg]
  simpa only [CongruenceSubgroup.strictWidthInfty_Gamma1] using
    CuspForm.hasEntireExtension_qExpansion_coeff one_pos g.toCuspForm

/-- **`L(s, f^α)` is the L-function of `f^α` when `f^α` is a newform**: if a newform `g` of weight
one has the coefficients `α(aₙ)`, then `L(s, f^α)` is the entire L-function of `g`. -/
lemma galoisConjLFunction_eq_L
    (hg : ∀ n, (qExpansion 1 g.toCuspForm).coeff n = f.galoisConjCoeff α n) :
    f.galoisConjLFunction α = ModularForm.L one_pos g.toCuspForm := by
  have h : LSeries.HasEntireExtension (f.galoisConjCoeff α) := hasEntireExtension_galoisConjCoeff hg
  rw [galoisConjLFunction, dite_eq_left h]
  refine (CuspForm.eq_strictWidthInfty_cpow_mul_L g.toCuspForm one_pos
    h.exists_extension.choose_spec.1 fun {s} hs ↦ ?_).trans ?_
  · have hab :
        LSeries.abscissaOfAbsConv (f.galoisConjCoeff α) ≤ (((1 : ℤ) / 2 : ℝ) : EReal) + 1 := by
      simpa only [CongruenceSubgroup.strictWidthInfty_Gamma1, funext hg] using
        CuspForm.abscissaOfAbsConv_qExpansion_coeff_le g.toCuspForm
    simp only [CongruenceSubgroup.strictWidthInfty_Gamma1, funext hg]
    exact h.exists_extension.choose_spec.2 <| hab.trans_lt <| by exact_mod_cast hs
  · simp

/-- **`L(s, f^α)` is the L-function of the Galois conjugate `σ(f)` when `σ(f)` is a newform**, for
an automorphism `σ` of `ℂ` extending `α` (LMFDB `cmf.galois_conjugate`). That `σ(f)` is always a
newform is not proved here. -/
lemma galoisConjLFunction_eq_L_of_isGaloisConjugateBy {σ : Gal(ℂ/ℚ)}
    (hσ : ∀ x : CoefficientField f, σ x = α x) (hfg : f.IsGaloisConjugateBy σ g) :
    f.galoisConjLFunction α = ModularForm.L one_pos g.toCuspForm :=
  galoisConjLFunction_eq_L fun n ↦
    (hfg.coeff n).trans <| hσ ⟨_, f.qExpansion_coeff_mem_coefficientField n⟩

variable (f) in
/-- **`L(s, f^1)` is the L-function of `f`.** -/
lemma galoisConjLFunction_one : f.galoisConjLFunction 1 = ModularForm.L one_pos f.toCuspForm :=
  galoisConjLFunction_eq_L fun _ ↦ rfl

end HeckeRing.GL2.Newform
