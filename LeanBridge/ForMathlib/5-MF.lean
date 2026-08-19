import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.FieldTheory.Relrank
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Classical modular form definitions for LeanBridge (chapter 5)

Definitions from the LMFDB classical-modular-form knowls that are not (yet) in mathlib, written
here in mathlib style for the LeanBridge blueprint audit.
-/

open scoped MatrixGroups

namespace CongruenceSubgroup

/-- A positive integer `N` is a **level** of a subgroup `Γ` of `SL(2, ℤ)` if `Γ` contains the
principal congruence subgroup `Γ(N)`; a modular form on `Γ` is then said to have level `N`
(LMFDB [`cmf.level`](https://www.lmfdb.org/knowledge/show/cmf.level)). -/
def IsLevel (N : ℕ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  N ≠ 0 ∧ Gamma N ≤ Γ

/-- The **level** of a subgroup `Γ` of `SL(2, ℤ)`: the least positive integer `N` such that `Γ`
contains the principal congruence subgroup `Γ(N)`, or `0` if there is no such `N`, i.e. if `Γ` is
not a congruence subgroup. The LMFDB defines the level of a newform as the least level of its
group of invariance (LMFDB [`cmf.level`](https://www.lmfdb.org/knowledge/show/cmf.level)). -/
noncomputable def level (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  sInf {N | IsLevel N Γ}

/-- A prime `p` is a **bad prime** for a modular form on a subgroup `Γ` of `SL(2, ℤ)` when it
divides the level of `Γ`
(LMFDB [`cmf.bad_prime`](https://www.lmfdb.org/knowledge/show/cmf.bad_prime)). -/
def IsBadPrime (p : ℕ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  p.Prime ∧ p ∣ level Γ

/-- A prime `p` is a **good prime** for a modular form on a subgroup `Γ` of `SL(2, ℤ)` when it
does not divide the level of `Γ`, i.e. when it is not a bad prime
(LMFDB [`cmf.bad_prime`](https://www.lmfdb.org/knowledge/show/cmf.bad_prime)). -/
def IsGoodPrime (p : ℕ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  p.Prime ∧ ¬ p ∣ level Γ

end CongruenceSubgroup

namespace DirichletCharacter

/-- The **character field** `ℚ(χ)` of a Dirichlet character `χ` with values in `ℂ`: the number
field generated over `ℚ` by the values of `χ`. This is the base field over which the LMFDB
measures the relative dimension of a newform
(LMFDB [`cmf.relative_dimension`](https://www.lmfdb.org/knowledge/show/cmf.relative_dimension)). -/
noncomputable def valueField {N : ℕ} (χ : DirichletCharacter ℂ N) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range χ)

end DirichletCharacter

namespace ModularForm

open UpperHalfPlane CongruenceSubgroup

/-- A function `f : ℍ → ℂ` transforms with **character** (or nebentypus) `χ` mod `N` in weight `k`
under a subgroup `Γ` of `SL(2, ℤ)` if `f(γz) = χ(d)(cz+d)^k f(z)` for all `γ = !![*, *; c, d]` in
`Γ`, that is, `f ∣[k] γ = χ(d) • f`. The LMFDB states this for a modular form on a group `Γ`
containing `Γ(N)` (see `CongruenceSubgroup.IsLevel`), typically `Γ₀(N)`
(LMFDB [`cmf.character`](https://www.lmfdb.org/knowledge/show/cmf.character)). -/
def HasCharacter (Γ : Subgroup SL(2, ℤ)) (k : ℤ) {N : ℕ} (χ : DirichletCharacter ℂ N)
    (f : ℍ → ℂ) : Prop :=
  ∀ γ ∈ Γ, f ∣[k] γ = χ (γ 1 1 : ZMod N) • f

/-- The **analytic conductor** of a newform of level `N` and weight `k`: the real number
`N * (exp (ψ (k / 2)) / (2 * π)) ^ 2`, where `ψ = Γ'/Γ` is the digamma function. Mathlib defines
the digamma function only on `ℂ`; for `k ≥ 1` its value at `k / 2` is real, and this definition
takes its real part
(LMFDB [`cmf.analytic_conductor`](https://www.lmfdb.org/knowledge/show/cmf.analytic_conductor)). -/
noncomputable def analyticConductor (N : ℕ) (k : ℤ) : ℝ :=
  N * (Real.exp (Complex.digamma (k / 2)).re / (2 * Real.pi)) ^ 2

/-- The **Sturm bound** of a space `M_k(N, χ)` of modular forms of weight `k`, level `N` and
character `χ`: the integer `⌊k * [SL(2, ℤ) : Γ₀(N)] / 12⌋`, where the index of `Γ₀(N)` is used
for every character `χ`. Two forms in `M_k(N, χ)` whose Fourier coefficients agree up to this
bound are equal
(LMFDB [`cmf.sturm_bound`](https://www.lmfdb.org/knowledge/show/cmf.sturm_bound)). -/
noncomputable def sturmBound (N : ℕ) (k : ℤ) : ℕ :=
  (k * (Gamma0 N).index / 12).toNat

/-- The **Sturm bound for `Γ₁(N)`** of a space `M_k(Γ₁(N))` of modular forms of weight `k` and
level `N`: the integer `⌊k * [SL(2, ℤ) : Γ₁(N)] / 12⌋`
(LMFDB [`cmf.sturm_bound_gamma1`](https://www.lmfdb.org/knowledge/show/cmf.sturm_bound_gamma1)). -/
noncomputable def sturmBoundGamma1 (N : ℕ) (k : ℤ) : ℕ :=
  (k * (Gamma1 N).index / 12).toNat

/-- The **relative dimension** of a newform in `S_k^new(Γ₀(N), χ)` with coefficient field `F`:
the degree of `F` over the character field `ℚ(χ)`. The coefficient field (the subfield of `ℂ`
generated by the Fourier coefficients, LMFDB `cmf.coefficient_field`) is taken here as an
explicit argument. `IntermediateField.relfinrank` computes `[F : ℚ(χ) ⊓ F]`, which agrees with
the degree `[F : ℚ(χ)]` since `ℚ(χ) ≤ F` for the coefficient field of a newform
(LMFDB [`cmf.relative_dimension`](https://www.lmfdb.org/knowledge/show/cmf.relative_dimension)). -/
noncomputable def relativeDimension {N : ℕ} (χ : DirichletCharacter ℂ N)
    (F : IntermediateField ℚ ℂ) : ℕ :=
  χ.valueField.relfinrank F

/-- The **coefficient ring** of a modular form `f`: the subring `ℤ[a₁, a₂, a₃, …]` of `ℂ`
generated by the coefficients `aₙ`, `n ≥ 1`, of its `q`-expansion `∑ aₙ qⁿ` at the infinite cusp
(taken with period `1`, i.e. `q = e^(2πiz)`, as for forms on `Γ₀(N)`). For a newform this is also
called the Hecke ring, the `aₙ` being Hecke eigenvalues
(LMFDB [`cmf.coefficient_ring`](https://www.lmfdb.org/knowledge/show/cmf.coefficient_ring)). -/
noncomputable def coefficientRing (f : ℍ → ℂ) : Subring ℂ :=
  Subring.closure (Set.range fun n : ℕ => (qExpansion 1 f).coeff (n + 1))

/-- The **coefficient field** of a modular form `f`: the subfield of `ℂ` generated over `ℚ` by
the coefficients `aₙ`, `n ≥ 1`, of its `q`-expansion `∑ aₙ qⁿ` at the infinite cusp (period `1`,
as in `ModularForm.coefficientRing`). For a Hecke eigenform this is a number field, also called
the Hecke field, and the relative dimension of a newform `f` in `S_k^new(Γ₀(N), χ)` is
`relativeDimension χ (coefficientField f)`
(LMFDB [`cmf.coefficient_field`](https://www.lmfdb.org/knowledge/show/cmf.coefficient_field)). -/
noncomputable def coefficientField (f : ℍ → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range fun n : ℕ => (qExpansion 1 f).coeff (n + 1))

/-- The **embedding** `ι(f)` of a modular form `f` along a field embedding `ι : F → ℂ`, where `F`
is a subfield of `ℂ` containing every `q`-expansion coefficient `aₙ` of `f` (for a newform, its
coefficient field): the function on `ℍ` with `q`-expansion `∑ ι(aₙ) qⁿ`, defined as the sum of
that series in `q = e^(2πiτ)`. Its value is junk where the series diverges; convergence on all of
`ℍ`, and modularity of `ι(f)`, are theorems about newforms and are not part of the definition
(LMFDB [`cmf.embedding`](https://www.lmfdb.org/knowledge/show/cmf.embedding)). -/
noncomputable def embeddedForm {F : IntermediateField ℚ ℂ} (f : ℍ → ℂ) (ι : F →+* ℂ)
    (hf : ∀ n, (qExpansion 1 f).coeff n ∈ F) : ℍ → ℂ :=
  fun τ => ∑' n : ℕ, ι ⟨(qExpansion 1 f).coeff n, hf n⟩ * Function.Periodic.qParam 1 τ ^ n

/-- Two cusp forms `f = ∑ aₙ qⁿ` and `g = ∑ bₙ qⁿ` on `Γ₁(N)` are **Galois conjugate** if there
is an automorphism `σ` with `bₙ = σ(aₙ)` for all `n ≥ 1`; since cusp forms have `a₀ = 0`, the
`q`-expansion of `g` is then the full coefficientwise image of that of `f`, i.e. `g = σ(f)`. The
LMFDB states this for newforms — newform-ness of `f` and `g` is not encoded — and takes
`σ ∈ Gal(ℚ̄/ℚ)`; here `σ` ranges over the `ℚ`-automorphisms of `ℂ`, which restrict to — and, by
the axiom of choice, extend from — automorphisms of `ℚ̄`, so for newforms, whose coefficients are
algebraic, the two formulations agree
(LMFDB [`cmf.galois_conjugate`](https://www.lmfdb.org/knowledge/show/cmf.galois_conjugate)). -/
def IsGaloisConjugate {N : ℕ} {k : ℤ} (f g : CuspForm ↑(Gamma1 N) k) : Prop :=
  ∃ σ : ℂ ≃ₐ[ℚ] ℂ, ∀ n : ℕ, n ≠ 0 → (qExpansion 1 ⇑g).coeff n = σ ((qExpansion 1 ⇑f).coeff n)

/-- The **Galois orbit** `[f]` of a newform `f`: the set `{σ(f) : σ ∈ Gal(ℚ̄/ℚ)}` of its
coefficientwise Galois conjugates within the cusp forms on `Γ₁(N)`, also called the newform
orbit. For a genuine newform this is the LMFDB's finite orbit `[f]`; its finiteness, and the
fact that it is a basis of the newform subspace it spans, are theorems and not part of the
definition
(LMFDB [`cmf.galois_orbit`](https://www.lmfdb.org/knowledge/show/cmf.galois_orbit)). -/
def galoisOrbit {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : Set (CuspForm ↑(Gamma1 N) k) :=
  {g | IsGaloisConjugate f g}

/-- The **trace form** `Tr(f)` of a newform `f` whose coefficient field is `F`: the sum
`∑ᵢ ι(f)` of the embeddings of `f` over all field embeddings `ι : F → ℂ`, equivalently the sum
of the distinct Galois conjugates of `f`. Its q-expansion is the coefficientwise field trace
`∑ Tr_{F/ℚ}(aₙ) qⁿ`, with integer coefficients and `a₁` the dimension of the newform — both
theorems, not encoded. The `finsum` is junk `0` unless `F` admits only finitely many embeddings,
as a number field does; and the sum counts each conjugate once only when `F` is exactly the
coefficient field of `f`, as the LMFDB prescribes
(LMFDB [`cmf.trace_form`](https://www.lmfdb.org/knowledge/show/cmf.trace_form)). -/
noncomputable def traceForm {F : IntermediateField ℚ ℂ} (f : ℍ → ℂ)
    (hf : ∀ n, (qExpansion 1 f).coeff n ∈ F) : ℍ → ℂ :=
  ∑ᶠ ι : F →+* ℂ, embeddedForm f ι hf

/-- The **Hecke operator** `T_n` on modular forms of weight `k`, level `N` and character `χ`, in
its `q`-expansion model: `T_n f` is the function on `ℍ` whose `q`-expansion has coefficients
`a_m(T_n f) = ∑_{d ∣ gcd(m,n)} χ(d) d^(k-1) a_(mn/d²)(f)`, summed here as a series in
`q = e^(2πiτ)`. Of the two equivalent classical models this implements the coefficient formula,
not the double-coset sum. That `T_n f` is again a modular form in `M_k(N, χ)`, linearity in `f`,
and the commutation and eigenbasis properties are theorems, not encoded; the sum is junk where
it diverges
(LMFDB [`cmf.hecke_operator`](https://www.lmfdb.org/knowledge/show/cmf.hecke_operator)). -/
noncomputable def heckeOperator {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) (n : ℕ)
    (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => ∑' m : ℕ,
    (∑ d ∈ (m.gcd n).divisors, χ d * (d : ℂ) ^ (k - 1) * (qExpansion 1 f).coeff (m * n / d ^ 2))
      * Function.Periodic.qParam 1 τ ^ m

/-- An **admissible Atkin-Lehner matrix** `W_Q` for level `N` and a divisor `Q` of `N`: the LMFDB
requires `Q` positive with `gcd(Q, N/Q) = 1`, and `W_Q = [[Qx, y], [Nz, Qt]]` of determinant `Q`
for some integers `x, y, z, t` — the existential shape is recorded equivalently as divisibility
of the entries, the witnesses being the quotients
(LMFDB [`cmf.atkin-lehner`](https://www.lmfdb.org/knowledge/show/cmf.atkin-lehner)). -/
structure IsAtkinLehnerMatrix (N Q : ℕ) (W : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  level_pos : 0 < N
  pos : 0 < Q
  dvd : Q ∣ N
  coprime : Nat.Coprime Q (N / Q)
  q_dvd_upper_left : (Q : ℤ) ∣ W 0 0
  n_dvd_lower_left : (N : ℤ) ∣ W 1 0
  q_dvd_lower_right : (Q : ℤ) ∣ W 1 1
  det_eq : W.det = Q

/-- The **Atkin-Lehner involution** `w_Q` of weight `k` attached to an admissible Atkin-Lehner
matrix `W_Q` for an exact divisor `Q` of `N`: the classical operator
`w_Q f = Q^(k/2) (Nz·τ + Qt)^(-k) f(W_Q·τ)`, written as the slash action `f ∣[k] W_Q` scaled by
`Q^(1 - k/2)` to convert mathlib's determinant normalization `det^(k-1)` into the classical
`det^(k/2)`, under which `w_Q` squares to the identity on `Γ₀(N)`-invariant forms. On a form of
`S_k(Γ₀(N))` — trivial character — that is an eigenform for every `T_p` with `p ∤ N`, it acts
with eigenvalue `±1`; for nontrivial nebentypus `w_Q` does not preserve the `χ`-space, and the
Atkin-Li pseudo-eigenvalues have modulus `1`, not `±1`. Independence of the choice of admissible
matrix and commutation with the Hecke operators `T_p`, `p ∤ Q`, are theorems, not encoded
(LMFDB [`cmf.atkin-lehner`](https://www.lmfdb.org/knowledge/show/cmf.atkin-lehner)). -/
noncomputable def atkinLehner (k : ℤ) {N Q : ℕ} {W : Matrix (Fin 2) (Fin 2) ℤ}
    (hW : IsAtkinLehnerMatrix N Q W) (f : ℍ → ℂ) : ℍ → ℂ :=
  (Q : ℂ) ^ (1 - (k : ℂ) / 2) •
    (f ∣[k] Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix W) (by
      rw [← RingHom.map_det, hW.det_eq, map_natCast]
      exact_mod_cast hW.pos.ne'))

/-- The **Fricke involution** `w_N` of weight `k` on forms of level `N`: the Atkin-Lehner
involution for the full level `Q = N`, represented by the admissible matrix `[[0, -1], [N, 0]]`.
For a newform in `S_k^new(Γ₀(N))`, the sign of the functional equation of its L-function is
`i^(-k)` times its `w_N`-eigenvalue — a theorem, not encoded
(LMFDB [`cmf.fricke`](https://www.lmfdb.org/knowledge/show/cmf.fricke)). -/
noncomputable def fricke (k : ℤ) {N : ℕ} (hN : 0 < N) (f : ℍ → ℂ) : ℍ → ℂ :=
  atkinLehner k (W := !![0, -1; (N : ℤ), 0])
    { level_pos := hN
      pos := hN
      dvd := dvd_rfl
      coprime := by simp [Nat.div_self hN]
      q_dvd_upper_left := by simp
      n_dvd_lower_left := by simp
      q_dvd_lower_right := by simp
      det_eq := by simp [Matrix.det_fin_two_of] }
    f

/-- The **Hecke orbit** of a cusp form `f` in `S_k(N, χ)` — a bundled cusp form on `Γ₁(N)`
together with nebentypus `χ` under `Γ₀(N)`: the subspace of functions on `ℍ` generated by the
images `T_p f` of `f` under the Hecke operators at all primes `p` coprime to the level `N`. The
orbit lives in the ambient space of functions since stability of cusp forms under the `T_p` is a
theorem, not encoded
(LMFDB [`cmf.hecke_orbit`](https://www.lmfdb.org/knowledge/show/cmf.hecke_orbit)). -/
noncomputable def heckeOrbit {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (f : CuspForm ↑(Gamma1 N) k) (_hf : HasCharacter (Gamma0 N) k χ ⇑f) :
    Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ {g | ∃ p : ℕ, p.Prime ∧ p.Coprime N ∧ g = heckeOperator χ k p ⇑f}

open Classical in
/-- The **Hecke characteristic polynomial** of a newform `f` at a prime `p`: the characteristic
polynomial of the Hecke operator `T_p` acting on the newform subspace `V_f`, the span of the
Galois orbit of `f` inside the cusp forms on `Γ₁(N)`. Finite-dimensionality of `V_f` is an
instance hypothesis (it holds for genuine newforms), and the action is the linear endomorphism
of `V_f` agreeing pointwise with `heckeOperator χ k p` — unique when it exists, since its values
are forced — with junk value `0` when no such endomorphism exists. Primality of `p` is not
required by the formula; the LMFDB uses good primes
(LMFDB [`cmf.heckecharpolys`](https://www.lmfdb.org/knowledge/show/cmf.heckecharpolys)). -/
noncomputable def heckeCharpoly {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) (p : ℕ)
    (f : CuspForm ↑(Gamma1 N) k) (_hf : HasCharacter (Gamma0 N) k χ ⇑f)
    [Module.Finite ℂ (Submodule.span ℂ (galoisOrbit f))] : Polynomial ℂ :=
  if h : ∃ T : Submodule.span ℂ (galoisOrbit f) →ₗ[ℂ] Submodule.span ℂ (galoisOrbit f),
      ∀ v, ⇑(T v : CuspForm ↑(Gamma1 N) k) = heckeOperator χ k p ⇑(v : CuspForm ↑(Gamma1 N) k) then
    h.choose.charpoly
  else 0

/-- A finite set `P` of primes indexes **distinguishing Hecke operators** `𝒯 = {T_p : p ∈ P}`
for a family `f : ι → CuspForm (Γ₁(N)) k` of nonconjugate newforms with nebentypus `χ`: the
primes are good (`p ∤ N`, the LMFDB's convenience restriction), and the sets `X_(f i)(𝒯)` of
Hecke characteristic polynomials of the `T_p` on the newform subspaces are pairwise distinct.
If the family contains conjugate newforms the proposition is unsatisfiable, so `ι` should index
orbit representatives. The particular ordered sequence of such primes recorded by the LMFDB (via
its strictly increasing refinement count) is a database convention, not formalized
(LMFDB [`cmf.distinguishing_primes`](https://www.lmfdb.org/knowledge/show/cmf.distinguishing_primes)). -/
def DistinguishesNewforms {ι : Type*} {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (f : ι → CuspForm ↑(Gamma1 N) k) (hf : ∀ i, HasCharacter (Gamma0 N) k χ ⇑(f i))
    [∀ i, Module.Finite ℂ (Submodule.span ℂ (galoisOrbit (f i)))] (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, p.Prime ∧ ¬ p ∣ N) ∧
    Function.Injective fun i => (fun p => heckeCharpoly χ k p (f i) (hf i)) '' (P : Set ℕ)

/-- The **coefficient ring generator bound** of a newform `f` with `q`-expansion `∑ aₙ qⁿ`: the
least positive integer `n` such that `ℤ[a₁, …, aₙ]` is the entire coefficient ring
`ℤ[a₁, a₂, a₃, …]`, or junk `0` if no finite prefix of the coefficients generates it
(LMFDB [`cmf.hecke_ring_generators`](https://www.lmfdb.org/knowledge/show/cmf.hecke_ring_generators)). -/
noncomputable def heckeRingGeneratorBound (f : ℍ → ℂ) : ℕ :=
  sInf {n | 0 < n ∧
    Subring.closure ((fun m => (qExpansion 1 f).coeff m) '' Set.Icc 1 n) = coefficientRing f}

/-- The **trace bound** of a family `f : ι → CuspForm (Γ₁(N)) k` of nonconjugate newforms with
nebentypus `χ` spanning the Galois orbits of a newspace: the least positive integer `m` such
that the traces down to `ℚ` of the coefficients `aₙ`, `n ≤ m`, distinguish the orbits — the
trace of `aₙ` being the sum of `ι(aₙ)` over the embeddings `ι` of the coefficient field, as in
`ModularForm.traceForm`. Unlike the universal Sturm bound this is the least such bound for the
particular space; it is junk `0` if no prefix separates the family, e.g. if `ι` contains
conjugate newforms, which share all traces
(LMFDB [`cmf.trace_bound`](https://www.lmfdb.org/knowledge/show/cmf.trace_bound)). -/
noncomputable def traceBound {ι : Type*} {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (f : ι → CuspForm ↑(Gamma1 N) k) (_hf : ∀ i, HasCharacter (Gamma0 N) k χ ⇑(f i)) : ℕ :=
  sInf {m | 0 < m ∧ Function.Injective fun i => fun j : Fin m =>
    ∑ᶠ e : coefficientField ⇑(f i) →+* ℂ,
      e ⟨(qExpansion 1 ⇑(f i)).coeff ((j : ℕ) + 1),
        IntermediateField.subset_adjoin ℚ _ ⟨(j : ℕ), rfl⟩⟩}

/-- The **level-raising map** (degeneracy map) `V_d = ι_d`: `(V_d f)(τ) = f(dτ)` for a positive
integer `d` — the classical normalization, with no stray power of `d`. For `d ∣ N/M` it maps
`S_k(M, χ_M)` into `S_k(N, χ)`, and its images from proper divisor levels span the old subspace
(LMFDB [`cmf.oldspace`](https://www.lmfdb.org/knowledge/show/cmf.oldspace)). -/
def levelRaisingMap (d : ℕ+) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun τ => f ⟨((d : ℕ) : ℂ) * τ, by
    simpa [Complex.mul_im] using mul_pos (by exact_mod_cast d.pos : (0 : ℝ) < (d : ℕ)) τ.im_pos⟩

/-- The **old subspace** `S_k^old(N, χ)` of the cusp forms of weight `k`, level `N` and
character `χ`: the span of the images `f(dτ)` of the cusp forms `f ∈ S_k(M, χ_M)` over all
proper divisors `M` of `N` carrying a character `χ_M` that induces `χ` (which forces `M` to be
divisible by the conductor of `χ`), and all divisors `d` of `N/M`. The knowl's direct-sum
decomposition into newspaces is a theorem, not encoded; the span lives in the ambient functions
on `ℍ` since modularity of the raised forms at level `N` is likewise a theorem
(LMFDB [`cmf.oldspace`](https://www.lmfdb.org/knowledge/show/cmf.oldspace)). -/
noncomputable def oldspace {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) :
    Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ
    {g | ∃ (M : ℕ) (hM : M ∣ N) (_ : M ≠ N) (χ' : DirichletCharacter ℂ M)
      (_ : DirichletCharacter.changeLevel hM χ' = χ) (d : ℕ+) (_ : (d : ℕ) ∣ N / M)
      (f : CuspForm ↑(Gamma1 M) k) (_ : HasCharacter (Gamma0 M) k χ' ⇑f),
      g = levelRaisingMap d ⇑f}

/-- The **new subspace** `S_k^new(N, χ)`: the orthogonal complement of the old subspace with
respect to the Petersson inner product, expressed relative to a pairing `B` — the space of `f`
with `B f g = 0` for every `g` in the old subspace, an intersection of kernels. Here `B f g`
stands for the Petersson pairing of `f` and `g` with the arguments ordered so that `B` is
linear in `f`: since the classical Petersson product is conjugate-linear in one slot, the
intended instantiation puts `f` in the linear slot (for mathlib's integrand, which conjugates
its first argument, this means `B f g = ⟨g, f⟩`). `B` is an input until the product is defined
(see `cmf.petersson_scalar_product`); the direct-sum decomposition `S_k = S_k^old ⊕ S_k^new`
and the newform basis are theorems, not encoded
(LMFDB [`cmf.newspace`](https://www.lmfdb.org/knowledge/show/cmf.newspace)). -/
noncomputable def newspace {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)) : Submodule ℂ (ℍ → ℂ) :=
  ⨅ g : ↥(oldspace χ k), LinearMap.ker ((LinearMap.proj (g : ℍ → ℂ)).comp B)

/-- The **plus subspace** of `S_k(Γ₀(N))`: the eigenspace of the Fricke involution `w_N` with
eigenvalue `+1`, here the set of functions fixed by `fricke k hN`. That it is a linear subspace
of the cusp forms — linearity of `w_N` — is a theorem, not encoded
(LMFDB [`cmf.plus_space`](https://www.lmfdb.org/knowledge/show/cmf.plus_space)). -/
def plusSpace (k : ℤ) {N : ℕ} (hN : 0 < N) :
    Set (CuspForm ↑(Gamma0 N) k) :=
  {f | fricke k hN ⇑f = ⇑f}

/-- The **minus subspace** of `S_k(Γ₀(N))`: the eigenspace of the Fricke involution `w_N` with
eigenvalue `-1`, here the set of functions negated by `fricke k hN`. That it is a linear
subspace of the cusp forms — linearity of `w_N` — is a theorem, not encoded
(LMFDB [`cmf.minus_space`](https://www.lmfdb.org/knowledge/show/cmf.minus_space)). -/
def minusSpace (k : ℤ) {N : ℕ} (hN : 0 < N) :
    Set (CuspForm ↑(Gamma0 N) k) :=
  {f | fricke k hN ⇑f = -⇑f}

/-- The **old subspace** `M_k^old(N, χ)` of the full space of modular forms of weight `k`,
level `N` and character `χ`: the span of the images `f(dτ)` of the modular forms
`f ∈ M_k(M, χ_M)` over proper divisors `M ∣ N` carrying a character `χ_M` that induces `χ`, and
divisors `d ∣ N/M` — the same degeneracy-map construction as the cuspidal `oldspace`. Of the
knowl's remaining content, the cuspidal subspace is mathlib's `ModularForm.cuspFormSubmodule`,
the Eisenstein subspace and its new part are `cmf.eisenstein_form`/`cmf.eisenstein_newspace`,
and the three direct-sum decompositions are theorems, not encoded
(LMFDB [`cmf.subspaces`](https://www.lmfdb.org/knowledge/show/cmf.subspaces)). -/
noncomputable def modularOldspace {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) :
    Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ
    {g | ∃ (M : ℕ) (hM : M ∣ N) (_ : M ≠ N) (χ' : DirichletCharacter ℂ M)
      (_ : DirichletCharacter.changeLevel hM χ' = χ) (d : ℕ+) (_ : (d : ℕ) ∣ N / M)
      (f : ModularForm ↑(Gamma1 M) k) (_ : HasCharacter (Gamma0 M) k χ' ⇑f),
      g = levelRaisingMap d ⇑f}

/-- A **newform** of weight `k`, level `N` and character `χ`: a cusp form in the new subspace
`S_k^new(N, χ)` that is a Hecke eigenform, normalized so that its `q`-expansion has `a₁ = 1`.
The eigenform condition is stated for the operators `T_n` with `n` coprime to the level; that a
member of the new subspace eigen away from the level is automatically an eigenform for all
`T_n` — the knowl's phrasing — is Diamond–Shurman Thm 5.8.2, a theorem, not a definition field.
The pairing `B` is the stand-in for the Petersson product defining the new subspace (see
`ModularForm.newspace`), and that the newforms form a basis of it is likewise a theorem
(LMFDB [`cmf.newform`](https://www.lmfdb.org/knowledge/show/cmf.newform)). -/
structure IsNewform {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)) (f : CuspForm ↑(Gamma1 N) k) : Prop where
  level_pos : 0 < N
  hasCharacter : HasCharacter (Gamma0 N) k χ ⇑f
  mem_newspace : ⇑f ∈ newspace χ k B
  eigen_away : ∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ, heckeOperator χ k n ⇑f = c • ⇑f
  normalized : (qExpansion 1 ⇑f).coeff 1 = 1

/-- The **newform subspace** `V_f` of a newform `f` in `S_k^new(N, χ)`: the subspace of the cusp
forms on `Γ₁(N)` generated by the Galois conjugates of `f` — the span already used by
`ModularForm.heckeCharpoly`. That every newspace decomposes canonically into newform subspaces
is a theorem (see `cmf.decomposition.new.gamma0chi`), not encoded
(LMFDB [`cmf.newform_subspace`](https://www.lmfdb.org/knowledge/show/cmf.newform_subspace)). -/
noncomputable def newformSubspace {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : CuspForm ↑(Gamma1 N) k)
    (_hf : IsNewform χ k B f) : Submodule ℂ (CuspForm ↑(Gamma1 N) k) :=
  Submodule.span ℂ (galoisOrbit f)

/-- The **Atkin-Lehner subspace of `f`** at level `N` and weight `k`: the functions satisfying
every Atkin-Lehner eigen-equation that `f` satisfies — `g` belongs when, for each admissible
`W_Q` and each `ε` with `w_Q f = ε • f`, also `w_Q g = ε • g`. Quantifying over all admissible
matrices avoids choosing one, but identifying this set with the classical Atkin-Lehner subspace
of a trivial-character newform relies on two theorems, not encoded: such a newform is an
eigenform of every `w_Q`, and all admissible matrices for a given `Q` induce the same operator
on the relevant forms
(LMFDB [`cmf.maximal`](https://www.lmfdb.org/knowledge/show/cmf.maximal)). -/
def atkinLehnerSubspaceOf (k : ℤ) (N : ℕ) (f : ℍ → ℂ) : Set (ℍ → ℂ) :=
  {g | ∀ {Q : ℕ} {W : Matrix (Fin 2) (Fin 2) ℤ} (hW : IsAtkinLehnerMatrix N Q W) (ε : ℂ),
    atkinLehner k hW f = ε • f → atkinLehner k hW g = ε • g}

/-- The newspace of the **character orbit** `[χ]`: the subspace `S_k^new(N, [χ])`, the span
`⨆_σ S_k^new(N, σ∘χ)` of the newspaces at all Galois conjugates of `χ`. Galois conjugation
sends a newform of nebentypus `χ` to one of nebentypus `σ∘χ`, so a full Galois orbit of
newforms spans a subspace of this space, not of the fixed-`χ` component; LMFDB newspaces are
labelled by character orbits accordingly
(LMFDB [`cmf.newspace`](https://www.lmfdb.org/knowledge/show/cmf.newspace)). -/
noncomputable def newspaceCharOrbit {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)) : Submodule ℂ (ℍ → ℂ) :=
  ⨆ σ : ℂ ≃ₐ[ℚ] ℂ, newspace (χ.ringHomComp (σ : ℂ →+* ℂ)) k B

/-- A newform `f` is **maximal** if its Galois orbit spans the ambient subspace containing it:
for nontrivial character the entire newspace of the character orbit `S_k^new(N, [χ])` — the full
Galois orbit meets every conjugate-character component, so the fixed-`χ` component would be too
small — and for trivial character its Atkin-Lehner subspace within the newspace (the
eigenvalue-matching set `atkinLehnerSubspaceOf`; the trivial character is Galois-stable). The
spans are taken in the ambient functions on `ℍ`, where the newspaces live
(LMFDB [`cmf.maximal`](https://www.lmfdb.org/knowledge/show/cmf.maximal)). -/
def IsMaximalNewform {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : CuspForm ↑(Gamma1 N) k)
    (_hf : IsNewform χ k B f) : Prop :=
  (χ ≠ 1 → Submodule.span ℂ ((fun g : CuspForm ↑(Gamma1 N) k => ⇑g) '' galoisOrbit f) =
    newspaceCharOrbit χ k B) ∧
  (χ = 1 →
    (Submodule.span ℂ ((fun g : CuspForm ↑(Gamma1 N) k => ⇑g) '' galoisOrbit f) :
      Set (ℍ → ℂ)) = ↑(newspace χ k B) ∩ atkinLehnerSubspaceOf k N ⇑f)

/-- A newform `f` is the **largest** newform in its ambient subspace if its dimension — the
dimension of its newform subspace — strictly exceeds that of every nonconjugate newform of the
same character in the same ambient subspace (for trivial character, sharing the Atkin-Lehner
subspace of `f`; for nontrivial character the ambient is the whole newspace)
(LMFDB [`cmf.maximal`](https://www.lmfdb.org/knowledge/show/cmf.maximal)). -/
def IsLargestNewform {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : CuspForm ↑(Gamma1 N) k)
    (hf : IsNewform χ k B f) : Prop :=
  ∀ g, ∀ hg : IsNewform χ k B g, ¬ IsGaloisConjugate f g →
    (χ = 1 → ⇑g ∈ atkinLehnerSubspaceOf k N ⇑f) →
    Module.finrank ℂ (newformSubspace g hg) < Module.finrank ℂ (newformSubspace f hf)

/-- The **decomposition of the newspace into newforms** along a family
`f : ι → CuspForm (Γ₁(N)) k` of newforms: the spans of their Galois orbits (taken in the ambient
functions, where the newspaces live) are independent and jointly span the character-orbit
newspace `S_k^new(N, [χ])` — full Galois orbits meet every conjugate-character component, so
the ambient is `newspaceCharOrbit`, not the fixed-`χ` component. The internal direct-sum
statement is phrased as a proposition about a supplied family rather than as definitional data;
that such a family exists, that each piece is irreducible and Hecke-stable, and that its
dimension equals the degree of the coefficient field of its newform are theorems, not encoded
(LMFDB [`cmf.decomposition.new.gamma0chi`](https://www.lmfdb.org/knowledge/show/cmf.decomposition.new.gamma0chi)). -/
def IsNewformDecomposition {ι : Type*} {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : ι → CuspForm ↑(Gamma1 N) k)
    (_hf : ∀ i, IsNewform χ k B (f i)) : Prop :=
  iSupIndep
    (fun i => Submodule.span ℂ
      ((fun g : CuspForm ↑(Gamma1 N) k => ⇑g) '' galoisOrbit (f i))) ∧
  ⨆ i, Submodule.span ℂ ((fun g : CuspForm ↑(Gamma1 N) k => ⇑g) '' galoisOrbit (f i)) =
    newspaceCharOrbit χ k B

/-- The **trace form of a newspace**: the modular form obtained by summing its canonical basis
of newforms, expressed as the sum `∑ᵢ Tr(fᵢ)` of the orbit trace forms over a finite family of
newforms decomposing the character-orbit newspace — the canonical basis is the union of the
Galois orbits, and summing within each orbit gives its trace form `ModularForm.traceForm`. The
coefficient-field membership of the `q`-coefficients is an input; for a genuine cusp form it is
provable, the constant term vanishing by `qExpansion_coeff_zero` with the `Γ₁(N)` period lemma
`strictPeriods_Gamma1` and the higher coefficients being generators
(LMFDB [`cmf.space_trace_form`](https://www.lmfdb.org/knowledge/show/cmf.space_trace_form)). -/
noncomputable def spaceTraceForm {ι : Type*} [Fintype ι] {N : ℕ}
    {χ : DirichletCharacter ℂ N} {k : ℤ} {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)}
    (f : ι → CuspForm ↑(Gamma1 N) k) (hf : ∀ i, IsNewform χ k B (f i))
    (_hdec : IsNewformDecomposition f hf)
    (hmem : ∀ i n, (qExpansion 1 ⇑(f i)).coeff n ∈ coefficientField ⇑(f i)) : ℍ → ℂ :=
  ∑ i, traceForm ⇑(f i) (hmem i)

open Classical in
/-- The **holomorphic Eisenstein series** `E_k^(χ₁,χ₂)` of weight `k` attached to primitive
Dirichlet characters `χ₁` mod `N₁` and `χ₂` mod `N₂`:
`½ (δ_(χ₁=1) L(1-k, χ₂) + δ_(k=1) δ_(χ₂=1) L(0, χ₁)) + ∑_(n≥1) σ_(k-1)^(χ₁,χ₂)(n) qⁿ`, where
`σ_(k-1)^(χ₁,χ₂)(n) = ∑_(m∣n) χ₁(n/m) χ₂(m) m^(k-1)` and `L` is the analytically continued
Dirichlet L-function `DirichletCharacter.LFunction`. This character-pair series is deliberately
distinct from mathlib's residue-pair-indexed `EisensteinSeries.eisensteinSeries`; relating the
two, and modularity of this series in `M_k(N₁N₂, χ₁χ₂)`, are theorems, not encoded
(LMFDB [`cmf.eisenstein_series`](https://www.lmfdb.org/knowledge/show/cmf.eisenstein_series)). -/
noncomputable def eisensteinSeriesChar {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (k : ℤ) (_hk : 0 < k)
    (_h₁ : χ₁.IsPrimitive) (_h₂ : χ₂.IsPrimitive) : ℍ → ℂ :=
  fun τ =>
    (1 / 2) * ((if χ₁ = 1 then DirichletCharacter.LFunction χ₂ (1 - (k : ℂ)) else 0) +
      (if k = 1 ∧ χ₂ = 1 then DirichletCharacter.LFunction χ₁ 0 else 0)) +
    ∑' n : ℕ, (∑ m ∈ (n + 1).divisors, χ₁ (((n + 1) / m : ℕ)) * χ₂ m * (m : ℂ) ^ (k - 1))
      * Function.Periodic.qParam 1 τ ^ (n + 1)

/-- The **Eisenstein subspace** `E_k(Γ)`: the orthogonal complement of the cusp forms
`S_k(Γ)` (mathlib's `cuspFormSubmodule`) inside `M_k(Γ)` with respect to the Petersson inner
product, expressed relative to a pairing `B`, as for `ModularForm.newspace` — the intersection
of the kernels `f ↦ B f g` over cusp forms `g`. Here `B f g` stands for the Petersson pairing
of `f` and `g` with the arguments ordered so that `B` is linear in `f`: since the classical
Petersson product is conjugate-linear in one slot, the intended instantiation puts `f` in the
linear slot (for mathlib's integrand, which conjugates its first argument, this means
`B f g = ⟨g, f⟩`). `B` is an input until the product is defined (see
`cmf.petersson_scalar_product`)
(LMFDB [`cmf.eisenstein_form`](https://www.lmfdb.org/knowledge/show/cmf.eisenstein_form)). -/
noncomputable def eisensteinSubspace (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) [Γ.HasDetOne]
    (B : ModularForm Γ k →ₗ[ℂ] (ModularForm Γ k → ℂ)) : Submodule ℂ (ModularForm Γ k) :=
  ⨅ g : ↥(cuspFormSubmodule Γ k), LinearMap.ker ((LinearMap.proj (g : ModularForm Γ k)).comp B)

/-- An **Eisenstein form** of weight `k`, level `N` and character `χ`: a modular form in the
Eisenstein subspace `E_k(Γ₁(N))` that transforms with nebentypus `χ` — the membership predicate
of the space `E_k(N, χ)`. The knowl's spanning description of `E_k(N, χ)` by the series
`E_k^(χ₁,χ₂)(dτ)` with `χ₁χ₂ = χ` and `d·N₁·N₂ ∣ N` (with the non-holomorphic `E₂` correction
`E₂(τ) - d·E₂(dτ)` at `k = 2`, `χ = 1`) is a theorem, deliberately not the definition
(LMFDB [`cmf.eisenstein_form`](https://www.lmfdb.org/knowledge/show/cmf.eisenstein_form)). -/
def IsEisensteinForm {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ)
    (B : ModularForm ↑(Gamma1 N) k →ₗ[ℂ] (ModularForm ↑(Gamma1 N) k → ℂ))
    (f : ModularForm ↑(Gamma1 N) k) : Prop :=
  f ∈ eisensteinSubspace ↑(Gamma1 N) k B ∧ HasCharacter (Gamma0 N) k χ ⇑f

open Classical in
/-- The **new Eisenstein subspace** `E_k^new(N, χ)`: the span of the Eisenstein series
`E_k^(χ₁,χ₂)` over pairs of primitive characters with the parity compatibility
`χ₁(-1)χ₂(-1) = (-1)^k` (required for the series to be a modular form; given `χ₁χ₂ = χ` it is
equivalent to `χ(-1) = (-1)^k`, so the space is `⊥` for wrong-parity `(k, χ)`), with `χ₁χ₂ = χ`
(as characters mod `N`, via `changeLevel`) and `N₁N₂ = N` exactly — except in the case `k = 2`,
`χ = 1`, where
`E₂^new(N) = 0` for composite `N` and, for `N = p` prime, the space is spanned by the corrected
series `E₂^(1,1)(τ) - p E₂^(1,1)(pτ)`. The old Eisenstein subspace, span of the degeneracy
images from proper divisor levels, is the `cmf.oldspace`/`cmf.subspaces` construction at
Eisenstein level; the decomposition `E_k = E_k^old ⊕ E_k^new` is a theorem, not encoded
(LMFDB [`cmf.eisenstein_newspace`](https://www.lmfdb.org/knowledge/show/cmf.eisenstein_newspace)). -/
noncomputable def eisensteinNewspace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℤ) :
    Submodule ℂ (ℍ → ℂ) :=
  if k = 2 ∧ χ = 1 then
    if hN : N.Prime then
      Submodule.span ℂ
        {eisensteinSeriesChar 1 1 2 two_pos DirichletCharacter.isPrimitive_one_level_one
            DirichletCharacter.isPrimitive_one_level_one -
          (N : ℂ) • levelRaisingMap ⟨N, hN.pos⟩
            (eisensteinSeriesChar 1 1 2 two_pos DirichletCharacter.isPrimitive_one_level_one
              DirichletCharacter.isPrimitive_one_level_one)}
    else ⊥
  else
    Submodule.span ℂ
      {g | ∃ (N₁ N₂ : ℕ) (h₁ : NeZero N₁) (h₂ : NeZero N₂) (_ : N₁ * N₂ = N)
        (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)
        (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (hk : 0 < k)
        (hd₁ : N₁ ∣ N) (hd₂ : N₂ ∣ N),
        χ₁ (-1) * χ₂ (-1) = (-1) ^ k ∧
        DirichletCharacter.changeLevel hd₁ χ₁ * DirichletCharacter.changeLevel hd₂ χ₂ = χ ∧
        g = @eisensteinSeriesChar N₁ N₂ h₁ h₂ χ₁ χ₂ k hk hp₁ hp₂}

/-- An **Eisenstein newform** of weight `k`, level `N` and character `χ`: a form in the new
Eisenstein subspace `E_k^new(N, χ)` that is a Hecke eigenform, normalized so that its
`q`-expansion has `a₁ = 1`. As in `ModularForm.IsNewform`, the eigenform condition is stated for
the operators `T_n` with `n` positive and coprime to the level, the full-eigenform statement of
the knowl being the analogous theorem of Eisenstein newform theory; that the Eisenstein
newforms are a basis of `E_k^new(N, χ)` is likewise a theorem, not encoded
(LMFDB [`cmf.eisenstein_newform`](https://www.lmfdb.org/knowledge/show/cmf.eisenstein_newform)). -/
structure IsEisensteinNewform {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℤ)
    (f : ℍ → ℂ) : Prop where
  mem_newspace : f ∈ eisensteinNewspace χ k
  eigen_away : ∀ n : ℕ, 0 < n → n.Coprime N → ∃ c : ℂ, heckeOperator χ k n f = c • f
  normalized : (qExpansion 1 f).coeff 1 = 1

/-- The cusp form `g` is the **twist** `f ⊗ ψ` of `f` by a primitive Dirichlet character `ψ` mod
`M`, in the coefficientwise sense: `aₙ(g) = ψ(n) aₙ(f)` for all `n ≥ 1` coprime to the level `N`
of `f` and to the conductor of `ψ` — which is `M` itself, `ψ` being primitive. This is the
defining relation only; that for a newform `f` there exists a unique newform `g` satisfying it
(so that `f ⊗ ψ` is well defined) is a theorem, not encoded, as is the newform context itself
(LMFDB [`cmf.twist`](https://www.lmfdb.org/knowledge/show/cmf.twist)). -/
def IsTwist {N N' : ℕ} {M : ℕ+} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (g : CuspForm ↑(Gamma1 N') k) (ψ : DirichletCharacter ℂ M) (_hψ : ψ.IsPrimitive) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime N → n.Coprime M →
    (qExpansion 1 ⇑g).coeff n = ψ n * (qExpansion 1 ⇑f).coeff n

/-- Two cusp forms are **twist related** when one is a twist of the other by some primitive
Dirichlet character. On newforms this is the LMFDB's twist equivalence and its class is the
twist class — but that the relation is symmetric and transitive there (twisting back by the
conjugate character, composing characters) is a theorem, not encoded, so the generic relation
is named `IsTwistRelated` rather than an equivalence
(LMFDB [`cmf.twist`](https://www.lmfdb.org/knowledge/show/cmf.twist)). -/
def IsTwistRelated {N N' : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (g : CuspForm ↑(Gamma1 N') k) : Prop :=
  ∃ (M : ℕ+) (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive), IsTwist f g ψ hψ

/-- The cusp form `g` is the **dual** of `f`: every coefficient of the `q`-expansion of `g` is
the complex conjugate of the corresponding coefficient of `f`. The dual of a form of character
`χ` has character `χ̄` at the same level, its L-function is the dual L-function, and the
coefficient field of a non-self-dual newform is a CM field — all theorems, not encoded
(LMFDB [`cmf.dualform`](https://www.lmfdb.org/knowledge/show/cmf.dualform)). -/
def IsDualForm {N : ℕ} {k : ℤ} (f g : CuspForm ↑(Gamma1 N) k) : Prop :=
  ∀ n : ℕ, (qExpansion 1 ⇑g).coeff n = starRingEnd ℂ ((qExpansion 1 ⇑f).coeff n)

/-- A cusp form is **self dual** if it is its own dual, i.e. every `q`-expansion coefficient is
fixed by complex conjugation — equivalently, the coefficients are real numbers, and the
L-function of the form is self-dual. The dichotomy that a newform's coefficient field is totally
real or CM according to self-duality is a theorem, not encoded
(LMFDB [`cmf.selfdual`](https://www.lmfdb.org/knowledge/show/cmf.selfdual)). -/
def IsSelfDual {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : Prop :=
  IsDualForm f f

/-- A cusp form `f` **admits a self-twist** by a primitive Dirichlet character `χ` if
`a_p(f) = χ(p) a_p(f)` for all but finitely many primes `p`, stated as finiteness of the
exceptional set. That a nontrivial self-twist character must be quadratic — the Kronecker
character of a quadratic field, giving CM or RM by the sign of its discriminant — and the
weight-one dihedral constraints are theorems, not encoded
(LMFDB [`cmf.self_twist`](https://www.lmfdb.org/knowledge/show/cmf.self_twist)). -/
def AdmitsSelfTwist {N : ℕ} {M : ℕ+} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (χ : DirichletCharacter ℂ M) (_hχ : χ.IsPrimitive) : Prop :=
  {p : ℕ | p.Prime ∧
    (qExpansion 1 ⇑f).coeff p ≠ χ p * (qExpansion 1 ⇑f).coeff p}.Finite

/-- The pair `(χ, σ)` is an **inner twist** of the cusp form `f`: `σ` is a `ℚ`-automorphism of
the coefficient field of `f` and `σ(a_p(f)) = χ(p) a_p(f)` for all but finitely many primes `p`,
stated as finiteness of the exceptional set. The knowl's primary phrasing — Galois conjugate
newforms `f, g` with `a_p(g) = χ(p) a_p(f)` — is recovered with `g = σ(f)`, which is Ribet's
theorem; that each inner twist is determined by its primitive `χ`, and that the pairs form a
group, are likewise theorems, not encoded. The trivial automorphism recovers the self-twist
condition of `cmf.self_twist`
(LMFDB [`cmf.inner_twist`](https://www.lmfdb.org/knowledge/show/cmf.inner_twist)). -/
def IsInnerTwist {N : ℕ} {M : ℕ+} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (χ : DirichletCharacter ℂ M) (_hχ : χ.IsPrimitive)
    (σ : coefficientField ⇑f ≃ₐ[ℚ] coefficientField ⇑f) : Prop :=
  {p : ℕ | ∃ hp : p.Prime,
    (σ ⟨(qExpansion 1 ⇑f).coeff p,
      IntermediateField.subset_adjoin ℚ _ ⟨p - 1, by simp [Nat.sub_add_cancel hp.pos]⟩⟩ : ℂ) ≠
      χ p * (qExpansion 1 ⇑f).coeff p}.Finite

/-- An inner twist `(χ, σ)` of `f` is **nontrivial** if it is not the self twist by the trivial
character, i.e. the pair is not `(1, 1)`: the twisting character is nontrivial and/or the Galois
action is
(LMFDB [`cmf.nontrivial_twist`](https://www.lmfdb.org/knowledge/show/cmf.nontrivial_twist)). -/
def IsNontrivialInnerTwist {N : ℕ} {M : ℕ+} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive)
    (σ : coefficientField ⇑f ≃ₐ[ℚ] coefficientField ⇑f) : Prop :=
  IsInnerTwist f χ hχ σ ∧ ¬(χ = 1 ∧ σ = 1)

/-- The **inner twist count** of a cusp form `f`: the number of distinct inner-twist pairs
`(χ, σ)` — `χ` a primitive Dirichlet character at any modulus, `σ` a `ℚ`-automorphism of the
coefficient field — with self twists and the trivial pair `(1, 1)` included. A primitive
character determines its modulus, so the sigma-type does not double count. `Nat.card` returns
junk `0` if the set of pairs were infinite; its finiteness for a newform (the pairs form a
finite group) is a theorem, not encoded
(LMFDB [`cmf.inner_twist_count`](https://www.lmfdb.org/knowledge/show/cmf.inner_twist_count)). -/
noncomputable def innerTwistCount {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : ℕ :=
  Nat.card {x : Σ M : ℕ+, DirichletCharacter ℂ M ×
    (coefficientField ⇑f ≃ₐ[ℚ] coefficientField ⇑f) //
    ∃ h : x.2.1.IsPrimitive, IsInnerTwist f x.2.1 h x.2.2}

/-- The **inner twist multiplicity** of a cusp form `f` at the Galois orbit of a primitive
Dirichlet character `ψ`: the number of characters `φ` in the orbit of `ψ` — its conjugates
`ψ^σ` under `ℚ`-automorphisms of `ℂ` — by which `f` admits an inner twist. The knowl attaches
this number to the orbit via any embedding of `f`; its independence of the embedding is a
theorem, not encoded, and `Nat.card` returns the count of a finite set as usual
(LMFDB [`cmf.inner_twist_multiplicity`](https://www.lmfdb.org/knowledge/show/cmf.inner_twist_multiplicity)). -/
noncomputable def innerTwistMultiplicity {N : ℕ} {M : ℕ+} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k)
    (ψ : DirichletCharacter ℂ M) (_hψ : ψ.IsPrimitive) : ℕ :=
  Nat.card {χ : DirichletCharacter ℂ M //
    (∃ σ : ℂ ≃ₐ[ℚ] ℂ, χ = ψ.ringHomComp (σ : ℂ →+* ℂ)) ∧
    ∃ (h : χ.IsPrimitive) (σf : coefficientField ⇑f ≃ₐ[ℚ] coefficientField ⇑f),
      IsInnerTwist f χ h σf}

/-- A cusp form `f` of level `N` is **minimal** if it is not a twist of a cusp form of lower
level: there is no `g` on `Γ₁(N')` with `N' < N` and primitive `ψ` such that
`f` is the twist `g ⊗ ψ`. This is the cuspidal specialization of the LMFDB notion `cmf.minimal`,
which is stated for modular forms in general.
(LMFDB [`cmf.minimal`](https://www.lmfdb.org/knowledge/show/cmf.minimal)). -/

def IsMinimal {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : Prop :=
  ¬ ∃ (N' : ℕ) (_ : N' < N) (g : CuspForm ↑(Gamma1 N') k) (M : ℕ+)
    (ψ : DirichletCharacter ℂ M) (hψ : ψ.IsPrimitive), IsTwist g f ψ hψ

/-- A newform `f` of level `N` is **twist minimal** if its level achieves the minimum within
its twist class: every newform twist related to `f` — with its own character and newspace
pairing — has level at least `N`
(LMFDB [`cmf.twist_minimal`](https://www.lmfdb.org/knowledge/show/cmf.twist_minimal)). -/
def IsTwistMinimal {N : ℕ} {χ : DirichletCharacter ℂ N} {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : CuspForm ↑(Gamma1 N) k)
    (_hf : IsNewform χ k B f) : Prop :=
  ∀ (N' : ℕ) (χ' : DirichletCharacter ℂ N') (B' : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ))
    (g : CuspForm ↑(Gamma1 N') k) (_hg : IsNewform χ' k B' g),
  IsTwistRelated f g → N ≤ N'

/- `cmf.minimal_twist` is intentionally not formalized here: its LMFDB definition includes
database-specific tie-breaking by lexicographically minimal label. We formalize the underlying
mathematical notions (`IsTwistRelated`, `IsTwistMinimal`, etc.) separately instead. -/

/-- The **twist multiplicity** of a cusp form orbit `[g]` as a twist of `[f]` by the Galois orbit
of a primitive character `ψ`: the number of distinct characters `ψ'` in the orbit of `ψ` for
which the twist `f ⊗ ψ'` lies in `[g]` — here, for which some Galois conjugate of `g` is the
coefficientwise twist of `f` by `ψ'`. Independence of the chosen representatives `f`, `g`, and
the equality with the inner twist count when `g` is an inner twist of `f`, are theorems, not
encoded
(LMFDB [`cmf.twist_multiplicity`](https://www.lmfdb.org/knowledge/show/cmf.twist_multiplicity)). -/
noncomputable def twistMultiplicity {N N' : ℕ} {M : ℕ+} {k : ℤ}
    (f : CuspForm ↑(Gamma1 N) k) (g : CuspForm ↑(Gamma1 N') k)
    (ψ : DirichletCharacter ℂ M) (_hψ : ψ.IsPrimitive) : ℕ :=
  Nat.card {ψ' : DirichletCharacter ℂ M //
    (∃ σ : ℂ ≃ₐ[ℚ] ℂ, ψ' = ψ.ringHomComp (σ : ℂ →+* ℂ)) ∧
    ∃ (h : ψ'.IsPrimitive) (t : CuspForm ↑(Gamma1 N') k),
      IsTwist f t ψ' h ∧ IsGaloisConjugate g t}

/-- A cusp form has **complex multiplication** (CM) if it admits a self twist by the Kronecker
character of an imaginary quadratic field. Mathlib has no Kronecker characters, so the classical
dictionary identifies them among Dirichlet characters: primitive quadratic characters of
conductor `|D|` correspond to fundamental discriminants `D`, the field being imaginary exactly
when the character is odd. The twisting character is therefore required to be primitive,
quadratic (`χ² = 1`, `χ ≠ 1`) and odd (`χ(-1) = -1`); that this matches the Kronecker character
of an imaginary quadratic field is the standard correspondence, a theorem
(LMFDB [`cmf.cm_form`](https://www.lmfdb.org/knowledge/show/cmf.cm_form)). -/
def IsCMForm {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : Prop :=
  ∃ (M : ℕ+) (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (_hne : χ ≠ 1),
    χ ^ 2 = 1 ∧ χ (-1) = -1 ∧ AdmitsSelfTwist f χ hχ

/-- A cusp form has **real multiplication** (RM) if it admits a self twist by the Kronecker
character of a real quadratic field: as in `ModularForm.IsCMForm`, a primitive quadratic
character, here even (`χ(-1) = 1`), corresponding to a positive fundamental discriminant. That
only weight-one forms can have real multiplication is a theorem, not encoded
(LMFDB [`cmf.rm_form`](https://www.lmfdb.org/knowledge/show/cmf.rm_form)). -/
def IsRMForm {N : ℕ} {k : ℤ} (f : CuspForm ↑(Gamma1 N) k) : Prop :=
  ∃ (M : ℕ+) (χ : DirichletCharacter ℂ M) (hχ : χ.IsPrimitive) (_hne : χ ≠ 1),
    χ ^ 2 = 1 ∧ χ (-1) = 1 ∧ AdmitsSelfTwist f χ hχ

/-- The **Satake parameters** of a newform `f` of weight `k` and character `χ` at a good prime
`p`: the reciprocal roots of the normalized local factor `L_p(p^(-(k-1)/2) t)`, where
`L_p(t) = 1 - a_p t + χ(p) p^(k-1) t²` — equivalently, the roots of the reversed quadratic
`X² - (a_p / p^((k-1)/2)) X + χ(p)`, as a multiset via `Polynomial.roots`, so a double root is
counted with multiplicity two. The knowl's identification `L_p(t) = det(1 - t T_p)` on the
newform subspace, and the unit-circle location of the parameters (Deligne), are theorems, not
encoded
(LMFDB [`cmf.satake_parameters`](https://www.lmfdb.org/knowledge/show/cmf.satake_parameters)). -/
noncomputable def satakeParameters {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (p : ℕ) (f : CuspForm ↑(Gamma1 N) k)
    (_hf : IsNewform χ k B f) (_hp : p.Prime) (_hpN : ¬ p ∣ N) : Multiset ℂ :=
  (Polynomial.X ^ 2 -
    Polynomial.C ((qExpansion 1 ⇑f).coeff p / (p : ℂ) ^ (((k : ℂ) - 1) / 2)) * Polynomial.X +
    Polynomial.C (χ p)).roots

/-- The **Satake angles** `θ_p = arg α_p` of a newform at a good prime `p`: the arguments of the
Satake parameters, as a multiset via `Complex.arg`. Mathlib's `arg` takes values in `(-π, π]`,
which realizes the knowl's range `[-π, π]`
(LMFDB [`cmf.satake_angles`](https://www.lmfdb.org/knowledge/show/cmf.satake_angles)). -/
noncomputable def satakeAngles {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (p : ℕ) (f : CuspForm ↑(Gamma1 N) k)
    (hf : IsNewform χ k B f) (hp : p.Prime) (hpN : ¬ p ∣ N) : Multiset ℝ :=
  (satakeParameters χ p f hf hp hpN).map Complex.arg

/-- The classification of the **identity component** of the Sato-Tate group of a newform of
weight `k > 1`: `SU(2)` in the generic case, the diagonally embedded `U(1)` in the CM case.
The CM dichotomy determines only this identity component; the full Sato-Tate group carries
further component-group structure (tied to inner-twist data) and is left unformalized
(LMFDB [`cmf.sato_tate`](https://www.lmfdb.org/knowledge/show/cmf.sato_tate)). -/
inductive SatoTateIdentityComponent
  /-- The generic case: a newform of weight `k > 1` without complex multiplication has
  Sato-Tate group with identity component `SU(2)`. -/
  | su2
  /-- The CM case: the identity component is the diagonally embedded `U(1)`. -/
  | u1

open Classical in
/-- The identity component of the **Sato-Tate group** of a newform of weight `k > 1`: `SU(2)`
for a newform without complex multiplication, the diagonal `U(1)` for a CM newform — the
assignment is the CM dichotomy of `ModularForm.IsCMForm`. The full Sato-Tate group (its
component group requires inner-twist data), the compact-group and Galois-representation content
of the knowl, the weight-one Artin case, and the (proved) equidistribution statement are not
formalized
(LMFDB [`cmf.sato_tate`](https://www.lmfdb.org/knowledge/show/cmf.sato_tate)). -/
noncomputable def satoTateIdentityComponent {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℤ}
    {B : (ℍ → ℂ) →ₗ[ℂ] ((ℍ → ℂ) → ℂ)} (f : CuspForm ↑(Gamma1 N) k)
    (_hf : IsNewform χ k B f) (_hk : 1 < k) : SatoTateIdentityComponent :=
  if IsCMForm f then .u1 else .su2

open MeasureTheory in
/-- The **Petersson scalar product** `⟨f, g⟩_G` of two functions on `ℍ`, with respect to a
finite-index subgroup `G` of `SL(2, ℤ)` and a fundamental domain `𝔉` for `G`:
`(1/[SL(2,ℤ):G]) ∫_𝔉 f(z) conj(g(z)) y^k dμ`, where `dμ = dxdy/y²` is mathlib's invariant
measure on `ℍ` (its `MeasureSpace` instance). The integrand is mathlib's
`UpperHalfPlane.petersson k g f` — mathlib conjugates the first slot, the knowl the second, so
the arguments are swapped and `⟨f, g⟩_G` is `ℂ`-linear in `f`, as the pairing inputs `B` of
`ModularForm.newspace` and `ModularForm.eisensteinSubspace` expect. The Bochner integral is
junk `0` when not integrable; the knowl's existence statement (the product converges when one
of `f`, `g` is a cusp form) and independence of the chosen fundamental domain are theorems, not
encoded
(LMFDB [`cmf.petersson_scalar_product`](https://www.lmfdb.org/knowledge/show/cmf.petersson_scalar_product)). -/
noncomputable def peterssonProduct (k : ℤ) (G : Subgroup SL(2, ℤ)) [G.FiniteIndex] (𝔉 : Set ℍ)
    (_h𝔉 : IsFundamentalDomain G 𝔉) (f g : ℍ → ℂ) : ℂ :=
  (G.index : ℂ)⁻¹ * ∫ τ in 𝔉, petersson k g f τ

end ModularForm
