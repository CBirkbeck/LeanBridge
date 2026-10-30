import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IgusaRing

/-!
# Vector-valued Siegel modular forms of weight `det^k ⊗ Sym²` on `Sp(4, ℤ)`

For Siegel modular forms `f ∈ M_k(Γ₂)` and `g ∈ M_j(Γ₂)` of degree 2 on `Γ₂ = Sp(4, ℤ)`, the Satoh
bracket `[f, g] = (2πi)⁻¹ (k⁻¹ g df/dZ - j⁻¹ f dg/dZ)`, where
`d/dZ = (∂/∂τ, ½∂/∂z; ½∂/∂z, ∂/∂ω)` for `Z = (τ, z; z, ω)`, is a vector-valued Siegel modular form
of weight `det^{k+j} ⊗ Sym²`: the terms coming from the derivative of the automorphy factor cancel.
Here a symmetric matrix `M` is identified with `∑_{a, b} M_{ab} e_a e_b ∈ Sym²(ℂ²)`, which is
`GL(2, ℂ)`-equivariant (`gMgᵀ` corresponds to `Sym²(g)`). Satoh proved that for even `k`,
`M_{k,2}(Γ₂) = M_{k-10}[ψ₄, ψ₆] ⊕ M_{k-14}[ψ₄, χ₁₀] ⊕ M_{k-16}[ψ₄, χ₁₂] ⊕ V_{k-16}[ψ₆, χ₁₀] ⊕
V_{k-18}[ψ₆, χ₁₂] ⊕ W_{k-22}[χ₁₀, χ₁₂]`, with `V_k = M_k ∩ ℂ[ψ₆, χ₁₀, χ₁₂]` and
`W_k = M_k ∩ ℂ[χ₁₀, χ₁₂]`. It is stated here (`SatohStructure`), not proved.

Two statements of the knowl are corrected:
* the knowl says `[f, g] ∈ M_{k,2}(Γ₂)`; the weight is `k + j`, as the knowl's own decomposition
  uses (`[ψ₄, ψ₆]` has weight 10);
* the knowl's last summand is `V_{k-22}[χ₁₀, χ₁₂]`, and it defines `W_k` without using it. With `V`
  the sum is not direct: the brackets satisfy `h[f, g] + f[g, h] + g[h, f] = 0` (as
  `[f, g] = fg (df/dZ / kf - dg/dZ / jg)`), so `ψ₆[χ₁₀, χ₁₂] = χ₁₀[ψ₆, χ₁₂] - χ₁₂[ψ₆, χ₁₀]` lies in
  `V₆[χ₁₀, χ₁₂]` and in `V₁₂[ψ₆, χ₁₀] + V₁₀[ψ₆, χ₁₂]` (weight `k = 28`), and it is nonzero. The
  summand is `W_{k-22}[χ₁₀, χ₁₂]`, as in Satoh's theorem.

The knowl names the generators `A = ψ₄`, `B = ψ₆`, `C = χ₁₀`, `D = χ₁₂` on its sample pages, while
the knowl `mf.siegel.family.sp4z` names `C = -4χ₁₀` and `D = 12χ₁₂`.

## Main definitions

* `SiegelUpperHalfSpace.symSqDeriv`: the derivative `df/dZ`, as a function to `Sym²(ℂ²)`.
* `SiegelUpperHalfSpace.satohBracket` (LMFDB `mf.siegel.family.sp4z_2`): the Satoh bracket.
* `SiegelUpperHalfSpace.Satoh.V`, `SiegelUpperHalfSpace.Satoh.W` (LMFDB
  `mf.siegel.family.sp4z_2`): the spaces `V_k` and `W_k`.
* `SiegelUpperHalfSpace.Satoh.mulRight`: the multiplication `h ↦ h b` of scalar functions by a
  vector-valued one.
* `SiegelUpperHalfSpace.Satoh.summand`: the six summands of the decomposition of `M_{k,2}(Γ₂)`.
* `SiegelUpperHalfSpace.Satoh.SatohStructure` (LMFDB `mf.siegel.family.sp4z_2`): Satoh's theorem, as
  a statement.
* `SiegelUpperHalfSpace.Satoh.A`, `B`, `C`, `D` (LMFDB `mf.siegel.family.sp4z_2`): the names of the
  generators on the sample pages.
-/

open Complex Real SiegelUpperHalfSpace Igusa

open scoped TensorProduct

namespace SiegelUpperHalfSpace

variable (f g : SiegelUpperHalfSpace (Fin 2) → ℂ)

/-- The derivative `df/dZ = (∂f/∂τ, ½∂f/∂z; ½∂f/∂z, ∂f/∂ω)` of `f : ℋ₂ → ℂ` at
`Ω = (τ, z; z, ω)`, as the element `∂f/∂τ e₁² + ∂f/∂z e₁e₂ + ∂f/∂ω e₂²` of `Sym²(ℂ²)` (the symmetric
matrix `M` corresponding to `∑_{a, b} M_{ab} e_a e_b`). -/
noncomputable def symSqDeriv (Ω : SiegelUpperHalfSpace (Fin 2)) : Sym[ℂ]^2 (Fin 2 → ℂ) :=
  directionalDeriv !![1, 0; 0, 0] f Ω • SymmetricPower.tprod ℂ ![Pi.single 0 1, Pi.single 0 1] +
    directionalDeriv !![0, 1; 1, 0] f Ω • SymmetricPower.tprod ℂ ![Pi.single 0 1, Pi.single 1 1] +
    directionalDeriv !![0, 0; 0, 1] f Ω • SymmetricPower.tprod ℂ ![Pi.single 1 1, Pi.single 1 1]

/-- The **Satoh bracket** `[f, g] = (2πi)⁻¹ (k⁻¹ g df/dZ - j⁻¹ f dg/dZ)` (LMFDB
`mf.siegel.family.sp4z_2`) of `f` of weight `k` and `g` of weight `j`, with values in `Sym²(ℂ²)`
(`symSqDeriv`). For Siegel modular forms `f ∈ M_k(Γ₂)`, `g ∈ M_j(Γ₂)` of positive weights it is a
Siegel modular form of weight `det^{k+j} ⊗ Sym²` (not `det^k ⊗ Sym²`, as the knowl says), which is
not proved here. -/
noncomputable def satohBracket (k j : ℕ) : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^2 (Fin 2 → ℂ) :=
  fun Ω ↦ (2 * π * I)⁻¹ • (((k : ℂ)⁻¹ * g Ω) • symSqDeriv f Ω - ((j : ℂ)⁻¹ * f Ω) • symSqDeriv g Ω)

namespace Satoh

variable (k : ℤ)

/-- The space `V_k(Γ₂) = M_k(Γ₂) ∩ ℂ[ψ₆, χ₁₀, χ₁₂]` (LMFDB `mf.siegel.family.sp4z_2`). -/
noncomputable def V : Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → ℂ) :=
  scalarModularForms k gamma2 ⊓ (Algebra.adjoin ℂ {psi 6, chi10, chi12}).toSubmodule

/-- The space `W_k(Γ₂) = M_k(Γ₂) ∩ ℂ[χ₁₀, χ₁₂]` (LMFDB `mf.siegel.family.sp4z_2`). -/
noncomputable def W : Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → ℂ) :=
  scalarModularForms k gamma2 ⊓ (Algebra.adjoin ℂ {chi10, chi12}).toSubmodule

/-- The multiplication `h ↦ h b` of scalar functions on `ℋ₂` by a vector-valued function `b`. -/
noncomputable def mulRight (b : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^2 (Fin 2 → ℂ)) :
    (SiegelUpperHalfSpace (Fin 2) → ℂ) →ₗ[ℂ] SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^2 (Fin 2 → ℂ) :=
  LinearMap.pi fun Ω ↦ (LinearMap.proj Ω).smulRight (b Ω)

/-- The six summands `M_{k-10}[ψ₄, ψ₆]`, `M_{k-14}[ψ₄, χ₁₀]`, `M_{k-16}[ψ₄, χ₁₂]`,
`V_{k-16}[ψ₆, χ₁₀]`, `V_{k-18}[ψ₆, χ₁₂]`, `W_{k-22}[χ₁₀, χ₁₂]` of Satoh's decomposition of
`M_{k,2}(Γ₂)` (LMFDB `mf.siegel.family.sp4z_2`), where `X[f, g]` is the space of the `h[f, g]` with
`h ∈ X`. -/
noncomputable def summand :
    Fin 6 → Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^2 (Fin 2 → ℂ)) :=
  ![(scalarModularForms (k - 10) gamma2).map (mulRight (satohBracket (psi 4) (psi 6) 4 6)),
    (scalarModularForms (k - 14) gamma2).map (mulRight (satohBracket (psi 4) chi10 4 10)),
    (scalarModularForms (k - 16) gamma2).map (mulRight (satohBracket (psi 4) chi12 4 12)),
    (V (k - 16)).map (mulRight (satohBracket (psi 6) chi10 6 10)),
    (V (k - 18)).map (mulRight (satohBracket (psi 6) chi12 6 12)),
    (W (k - 22)).map (mulRight (satohBracket chi10 chi12 10 12))]

/-- **Satoh's theorem** (LMFDB `mf.siegel.family.sp4z_2`), as a statement: the Satoh bracket of
`f ∈ M_k(Γ₂)` and `g ∈ M_j(Γ₂)` of positive weights is a vector-valued Siegel modular form of weight
`det^{k+j} ⊗ Sym²` on `Γ₂ = Sp(4, ℤ)`, and for even `k`,
`M_{k,2}(Γ₂) = M_{k-10}[ψ₄, ψ₆] ⊕ M_{k-14}[ψ₄, χ₁₀] ⊕ M_{k-16}[ψ₄, χ₁₂] ⊕ V_{k-16}[ψ₆, χ₁₀] ⊕
V_{k-18}[ψ₆, χ₁₂] ⊕ W_{k-22}[χ₁₀, χ₁₂]` (`summand`). The knowl writes `M_{k,2}` for the weight of
the bracket and `V_{k-22}` for the last summand; both are corrected (see the module docstring). It
is a theorem of Satoh, which is not proved here. -/
structure SatohStructure : Prop where
  satohBracket_mem : ∀ k j : ℕ, 0 < k → 0 < j → ∀ f ∈ scalarModularForms k gamma2,
    ∀ g ∈ scalarModularForms j gamma2, satohBracket f g k j ∈ modularFormsKJ (k + j) 2 gamma2
  iSupIndep : ∀ k : ℤ, Even k → iSupIndep (summand k)
  iSup_eq : ∀ k : ℤ, Even k → ⨆ i, summand k i = modularFormsKJ k 2 gamma2

/-- The generator `A = ψ₄` (LMFDB `mf.siegel.family.sp4z_2`), as named on the sample pages. -/
noncomputable def A : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  psi 4

/-- The generator `B = ψ₆` (LMFDB `mf.siegel.family.sp4z_2`), as named on the sample pages. -/
noncomputable def B : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  psi 6

/-- The generator `C = χ₁₀` (LMFDB `mf.siegel.family.sp4z_2`), as named on the sample pages; the
knowl `mf.siegel.family.sp4z` uses `C = -4χ₁₀` (`SiegelUpperHalfSpace.Igusa.C`). -/
noncomputable def C : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  chi10

/-- The generator `D = χ₁₂` (LMFDB `mf.siegel.family.sp4z_2`), as named on the sample pages; the
knowl `mf.siegel.family.sp4z` uses `D = 12χ₁₂` (`SiegelUpperHalfSpace.Igusa.D`). -/
noncomputable def D : SiegelUpperHalfSpace (Fin 2) → ℂ :=
  chi12

end Satoh

end SiegelUpperHalfSpace
