import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.HalfIntegralWeight
import Mathlib.NumberTheory.Modular
import TauCeti.GroupTheory.Index.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Newform

/-!
# The Shimura decomposition of spaces of cusp forms of half-integral weight

For an odd `k ≥ 3`, `4 ∣ N` and a Dirichlet character `χ` modulo `N`, Shimura's lift relates cusp
forms of weight `k/2` and character `χ` to modular forms of weight `k - 1` and character `χ²`. Let
`S₀(N, χ)` be the subspace of `S_{3/2}(N, χ)` spanned by the unary theta series
`∑_{n ∈ ℤ} ψ(n) n q^{tn²}` (`ψ` odd, `t ≥ 1`) when `k = 3`, and `S₀(N, χ) = 0` when `k > 3`, and
`S₀'(N, χ)` its orthogonal complement in `S_{k/2}(N, χ)` for the Petersson product. Then
`S₀'(N, χ) = ⊕_F S_{k/2}(N, χ, F)` (LMFDB `mf.half_integral_weight.shimura_decomposition`), where
`F` runs over the newforms of weight `k - 1`, level dividing `N/2` and character `χ²`, and
`S_{k/2}(N, χ, F)` is the subspace of the `g ∈ S₀'(N, χ)` with `T_{p²} g = a_p(F) g` for every
prime `p ∤ N`; `T_{p²}` is Shimura's Hecke operator, given on `q`-expansions by
`a(n) ↦ a(p²n) + χ(p) ((-1)^λ n / p) p^{λ-1} a(n) + χ(p²) p^{k-2} a(n/p²)`, `λ = (k - 1)/2`.

The decomposition rests on Shimura's theorem and is stated here, not proved. The knowl defines
`S₀'(N, χ)` as the orthogonal complement of `S₀(N, χ)` in `S_{3/2}(N, χ)`; it is the complement in
`S_{k/2}(N, χ)`, of which the `S_{k/2}(N, χ, F)` are subspaces. The knowl does not say which theta
series span `S₀(N, χ)`; they are Shimura's unary theta series. The orthogonality is that of the
Petersson product `∫ g h̄ y^{k/2} dμ` over a fundamental domain of `Γ₀(N)`, whose integral
converges for cusp forms; as that is not proved here, the integrability is part of the definition
of `S₀'(N, χ)`.

## Main definitions

* `ModularForm.unaryThetaSeries`: the theta series `∑ ψ(n) n q^{tn²}`.
* `ModularForm.shimuraThetaSpace` (LMFDB `mf.half_integral_weight.shimura_decomposition`): the
  space `S₀(N, χ)`.
* `ModularForm.halfIntegralPetersson`: the Petersson product of weight `k/2` on `Γ₀(N)`.
* `ModularForm.HalfIntegralPeterssonOrthogonal`: orthogonality for the Petersson product.
* `ModularForm.shimuraComplement` (LMFDB `mf.half_integral_weight.shimura_decomposition`): the
  space `S₀'(N, χ)`.
* `ModularForm.halfIntegralHeckeCoeff`: Shimura's Hecke operator `T_{p²}` on `q`-expansions.
* `ModularForm.shimuraEigenspace` (LMFDB `mf.half_integral_weight.shimura_decomposition`): the
  space `S_{k/2}(N, χ, F)`.
* `ModularForm.ShimuraIndex`: the newforms `F` of the decomposition.
* `ModularForm.ShimuraDecomposition` (LMFDB `mf.half_integral_weight.shimura_decomposition`): the
  decomposition `S₀'(N, χ) = ⊕_F S_{k/2}(N, χ, F)`, as a statement.

## Main results

* `ModularForm.shimuraComplement_eq_of_ne`: for `k ≠ 3`, `S₀'(N, χ) = S_{k/2}(N, χ)`.
-/

open CongruenceSubgroup ModularGroup Complex Real MeasureTheory HeckeRing GL2

open scoped ComplexConjugate MatrixGroups Pointwise

open UpperHalfPlane hiding I

namespace ModularForm

variable {N : ℕ} (χ : DirichletCharacter ℂ N) (k : ℤ) {g g' h : ℍ → ℂ} (c : ℂ) (p : ℕ) {a b : ℕ → ℂ}

/-- The **unary theta series** `θ_{ψ,t}(z) = ∑_{n ∈ ℤ} ψ(n) n e^{2πitn²z}` of a Dirichlet character
`ψ` and `t ≥ 1`. For odd `ψ` of conductor `r` it is a cusp form of weight `3/2` (on `Γ₀(4r²t)`), and
these series span the space `S₀(N, χ)` of the Shimura decomposition. -/
noncomputable def unaryThetaSeries {r : ℕ} (ψ : DirichletCharacter ℂ r) (t : ℕ) (z : ℍ) : ℂ :=
  ∑' n : ℤ, ψ n * n * cexp (2 * π * I * t * n ^ 2 * z)

/-- The space `S₀(N, χ)` (LMFDB `mf.half_integral_weight.shimura_decomposition`): for `k = 3`, the
subspace of `S_{3/2}(N, χ)` spanned by the unary theta series `∑ ψ(n) n q^{tn²}`, `ψ` odd and
`t ≥ 1`, that lie in `S_{3/2}(N, χ)`; for `k ≠ 3`, the zero space. -/
noncomputable def shimuraThetaSpace : Submodule ℂ (ℍ → ℂ) :=
  if k = 3 then Submodule.span ℂ {f | f ∈ halfIntegralWeightCuspSpace χ 3 ∧
    ∃ (r : ℕ) (ψ : DirichletCharacter ℂ r) (t : ℕ), ψ.Odd ∧ 0 < t ∧ f = unaryThetaSeries ψ t}
  else ⊥

lemma shimuraThetaSpace_le : shimuraThetaSpace χ k ≤ halfIntegralWeightCuspSpace χ k := by
  rw [shimuraThetaSpace]
  split_ifs with hk
  · exact Submodule.span_le.mpr fun f hf ↦ hk ▸ hf.1
  · exact bot_le

variable (N) in
/-- The fundamental domain `⋃_q q⁻¹ 𝒟ᵒ` of `Γ₀(N)` acting on the upper half-plane, the union over
the cosets `q` of `Γ₀(N)·{±1}` in `SL(2, ℤ)` (Tau Ceti's
`ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter`). -/
noncomputable def gamma0FundamentalDomain : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ (Gamma0 N).withCenter, (q.out : SL(2, ℤ))⁻¹ • fdo

variable (g h) in
/-- The integrand `g(z) conj(h(z)) y^{k/2}` of the Petersson product of weight `k/2`. -/
noncomputable def halfIntegralPeterssonIntegrand (z : ℍ) : ℂ :=
  g z * conj (h z) * (z.im ^ ((k : ℝ) / 2) : ℝ)

lemma halfIntegralPeterssonIntegrand_add : halfIntegralPeterssonIntegrand k (g + g') h =
    halfIntegralPeterssonIntegrand k g h + halfIntegralPeterssonIntegrand k g' h := by
  ext z
  simp [halfIntegralPeterssonIntegrand, add_mul]

lemma halfIntegralPeterssonIntegrand_smul :
    halfIntegralPeterssonIntegrand k (c • g) h = c • halfIntegralPeterssonIntegrand k g h := by
  ext z
  simp [halfIntegralPeterssonIntegrand, mul_assoc]

variable (h) in
lemma halfIntegralPeterssonIntegrand_zero_left : halfIntegralPeterssonIntegrand k 0 h = 0 := by
  ext z
  simp [halfIntegralPeterssonIntegrand]

variable (g) in
lemma halfIntegralPeterssonIntegrand_zero_right : halfIntegralPeterssonIntegrand k g 0 = 0 := by
  ext z
  simp [halfIntegralPeterssonIntegrand]

variable (N g h) in
/-- The **Petersson product** `⟨g, h⟩ = ∫ g(z) conj(h(z)) y^{k/2} dμ` of weight `k/2` on `Γ₀(N)`,
over the fundamental domain `gamma0FundamentalDomain N`, `dμ = dx dy / y²`. It is linear in `g` and
conjugate-linear in `h` when the integrals converge, as they do for cusp forms. -/
noncomputable def halfIntegralPetersson : ℂ :=
  ∫ z in gamma0FundamentalDomain N, halfIntegralPeterssonIntegrand k g h z

variable (N g h) in
/-- `g` is **orthogonal** to `h` for the Petersson product of weight `k/2` on `Γ₀(N)`: the integrand
`g(z) conj(h(z)) y^{k/2}` is integrable over the fundamental domain and `⟨g, h⟩ = 0`. The
integrability, which holds for cusp forms but is not proved here, is part of the condition, the
Bochner integral of a non-integrable function being `0`. -/
def HalfIntegralPeterssonOrthogonal : Prop :=
  IntegrableOn (halfIntegralPeterssonIntegrand k g h) (gamma0FundamentalDomain N) ∧
    halfIntegralPetersson N k g h = 0

variable {k} in
lemma halfIntegralPeterssonOrthogonal_of_integrand_eq_zero
    (hgh : halfIntegralPeterssonIntegrand k g h = 0) : HalfIntegralPeterssonOrthogonal N k g h := by
  rw [HalfIntegralPeterssonOrthogonal, halfIntegralPetersson, hgh]
  exact ⟨integrableOn_zero, integral_zero _ _⟩

/-- The space `S₀'(N, χ)` (LMFDB `mf.half_integral_weight.shimura_decomposition`): the orthogonal
complement of `S₀(N, χ)` in `S_{k/2}(N, χ)` for the Petersson product of weight `k/2` on `Γ₀(N)`.
The knowl writes `S_{3/2}(N, χ)` for `S_{k/2}(N, χ)`. The convergence of the Petersson integrals,
which holds for cusp forms but is not proved here, is part of the definition
(`ModularForm.HalfIntegralPeterssonOrthogonal`). -/
noncomputable def shimuraComplement : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | f ∈ halfIntegralWeightCuspSpace χ k ∧
    ∀ e ∈ shimuraThetaSpace χ k, HalfIntegralPeterssonOrthogonal N k f e}
  add_mem' {f f'} hf hf' := ⟨add_mem hf.1 hf'.1, fun e he ↦ by
    rcases hf.2 e he with ⟨hi, h₀⟩
    rcases hf'.2 e he with ⟨hi', h₀'⟩
    rw [halfIntegralPetersson] at h₀ h₀'
    rw [HalfIntegralPeterssonOrthogonal, halfIntegralPetersson, halfIntegralPeterssonIntegrand_add,
      integral_add' hi hi', h₀, h₀', add_zero]
    exact ⟨hi.add hi', rfl⟩⟩
  zero_mem' := ⟨zero_mem _, fun e _ ↦ halfIntegralPeterssonOrthogonal_of_integrand_eq_zero <|
    halfIntegralPeterssonIntegrand_zero_left k e⟩
  smul_mem' d f hf := ⟨Submodule.smul_mem _ d hf.1, fun e he ↦ by
    rcases hf.2 e he with ⟨hi, h₀⟩
    rw [halfIntegralPetersson] at h₀
    rw [HalfIntegralPeterssonOrthogonal, halfIntegralPetersson, halfIntegralPeterssonIntegrand_smul]
    refine ⟨hi.smul d, ?_⟩
    rw [Pi.smul_def, integral_smul, h₀, smul_zero]⟩

/-- **For `k ≠ 3` the space `S₀'(N, χ)` is `S_{k/2}(N, χ)`**, as `S₀(N, χ) = 0`. -/
lemma shimuraComplement_eq_of_ne (hk : k ≠ 3) :
    shimuraComplement χ k = halfIntegralWeightCuspSpace χ k := by
  ext f
  refine ⟨fun hf ↦ hf.1, fun hf ↦ ⟨hf, fun e he ↦ ?_⟩⟩
  simp only [shimuraThetaSpace, hk, ↓reduceIte, Submodule.mem_bot] at he
  rw [he]
  exact halfIntegralPeterssonOrthogonal_of_integrand_eq_zero <|
    halfIntegralPeterssonIntegrand_zero_right k f

variable (a) in
/-- **Shimura's Hecke operator `T_{p²}`** of weight `k/2` and character `χ`, on `q`-expansions: for
`g = ∑ a(n) qⁿ`, `T_{p²} g = ∑ b(n) qⁿ` with
`b(n) = a(p²n) + χ(p) ((-1)^λ n / p) p^{λ-1} a(n) + χ(p²) p^{k-2} a(n/p²)`, `λ = (k - 1)/2`, where
`(· / p)` is the Legendre symbol and `a(n/p²) = 0` unless `p² ∣ n` (Shimura; Koblitz, IV.3). -/
noncomputable def halfIntegralHeckeCoeff (n : ℕ) : ℂ :=
  a (p ^ 2 * n) +
    χ p * jacobiSym ((-1) ^ ((k - 1) / 2).toNat * n) p * (p : ℂ) ^ ((k - 1) / 2 - 1) * a n +
      χ (p ^ 2) * (p : ℂ) ^ (k - 2) * if p ^ 2 ∣ n then a (n / p ^ 2) else 0

lemma halfIntegralHeckeCoeff_add : halfIntegralHeckeCoeff χ k p (a + b) =
    halfIntegralHeckeCoeff χ k p a + halfIntegralHeckeCoeff χ k p b := by
  ext n
  simp only [halfIntegralHeckeCoeff, Pi.add_apply]
  split_ifs <;> ring1

lemma halfIntegralHeckeCoeff_smul :
    halfIntegralHeckeCoeff χ k p (c • a) = c • halfIntegralHeckeCoeff χ k p a := by
  ext n
  simp only [halfIntegralHeckeCoeff, Pi.smul_apply]
  split_ifs <;> ring1

variable {M : ℕ} [NeZero M] (F : Newform M (k - 1))

/-- The space `S_{k/2}(N, χ, F)` (LMFDB `mf.half_integral_weight.shimura_decomposition`) of a
newform `F = ∑ a_n(F) qⁿ` of weight `k - 1`: the `g ∈ S₀'(N, χ)` with `T_{p²} g = a_p(F) g` for
every prime `p ∤ N`, where `a_p(F)` is the eigenvalue `λ_p(F)` of `T_p` on the normalised newform
`F` and `T_{p²}` acts on the `q`-expansion `g = ∑ a(n) qⁿ` (`halfIntegralHeckeCoeff`). -/
noncomputable def shimuraEigenspace : Submodule ℂ (ℍ → ℂ) where
  carrier := {f | f ∈ shimuraComplement χ k ∧ ∃ a : ℕ → ℂ,
    (∀ z : ℍ, HasSum (fun n ↦ a n * cexp (2 * π * I * n * z)) (f z)) ∧ ∀ p, p.Prime → ¬p ∣ N →
      halfIntegralHeckeCoeff χ k p a = (qExpansion 1 F.toCuspForm).coeff p • a}
  add_mem' {f f'} hf hf' := by
    rcases hf with ⟨hf, a, ha, hap⟩
    rcases hf' with ⟨hf', b, hb, hbp⟩
    refine ⟨add_mem hf hf', a + b, fun z ↦ by simpa [add_mul] using (ha z).add (hb z),
      fun p hp hpN ↦ ?_⟩
    rw [halfIntegralHeckeCoeff_add, hap p hp hpN, hbp p hp hpN, smul_add]
  zero_mem' := ⟨zero_mem _, 0, fun z ↦ by simp, fun p _ _ ↦ by
    ext n
    simp [halfIntegralHeckeCoeff]⟩
  smul_mem' d f hf := by
    rcases hf with ⟨hf, a, ha, hap⟩
    refine ⟨Submodule.smul_mem _ d hf, d • a, fun z ↦ by simpa [mul_assoc] using (ha z).mul_left d,
      fun p hp hpN ↦ ?_⟩
    rw [halfIntegralHeckeCoeff_smul, hap p hp hpN, smul_comm]

variable (N) in
/-- The newforms `F` of the Shimura decomposition of `S₀'(N, χ)`: the newforms of weight `k - 1`,
of a level `M` dividing `N/2` (`2M ∣ N`), and of character `χ²`, that is, whose nebentypus `χ_F`
satisfies `χ_F(d) = χ(d)²` for every `d` prime to `N`. -/
def ShimuraIndex : Type :=
  Σ M : ℕ+, {F : Newform M (k - 1) // 2 * (M : ℕ) ∣ N ∧
    ∀ d : ℕ, d.Coprime N → χ d ^ 2 = F.dirichletLift d}

/-- **The Shimura decomposition** (LMFDB `mf.half_integral_weight.shimura_decomposition`), as a
statement: `S₀'(N, χ) = ⊕_F S_{k/2}(N, χ, F)`, where `F` runs over the newforms of weight `k - 1`,
level dividing `N/2` and character `χ²`. It holds for odd `k ≥ 3` and `4 ∣ N`, by Shimura's
theorem, and is not proved here. -/
structure ShimuraDecomposition : Prop where
  iSupIndep : iSupIndep fun F : ShimuraIndex N χ k ↦ shimuraEigenspace χ k F.2.1
  iSup_eq : ⨆ F : ShimuraIndex N χ k, shimuraEigenspace χ k F.2.1 = shimuraComplement χ k

end ModularForm
