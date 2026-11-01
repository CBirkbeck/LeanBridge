import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftParabolic

/-!
# The Fourier–Jacobi expansion of the Maass lift

When its series converges absolutely, the Maass lift `F(Z) = ∑ a(n, r, m) e^{2πi(nτ + rz + mω)}`
of `φ` (`SiegelUpperHalfSpace.maassLift`, LMFDB `mf.siegel.lift.maass`) has the Fourier–Jacobi
expansion `F(Z) = ∑_m φ_m(τ, z) e^{2πimω}`, where `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}`
is `φ ∣ V_m` for `m ≥ 1`, the image of `φ` under the index raising operator of Eichler and Zagier,
and `c(0, 0)` times the Eisenstein series of weight `k` for `m = 0`. The partial inversion
`J₁ : (τ, z, ω) ↦ (-1/τ, z/τ, ω - z²/τ)` acts on each term through the transformation law of
`φ_m` under `(0, -1; 1, 0)`, so that `F(J₁Z) = τ^k F(Z)` as soon as each `φ_m` is a Jacobi form of
weight `k` and index `m`. With the transformation law under the Siegel parabolic subgroup and the
generation of `Sp(4, ℤ)` by it and `J₁`, this reduces the theorem of Maass (`MaassLiftTheorem`,
Eichler and Zagier, Theorem 6.2) to the absolute convergence of the series, the holomorphy of the
lift, and the theorem of Eichler and Zagier (Theorem 4.2) that `V_m` maps `J_{k,1}` to `J_{k,m}`.

## Main definitions

* `SiegelUpperHalfSpace.maassFourierJacobi` (LMFDB `mf.siegel.lift.maass`): the Fourier–Jacobi
  coefficients `φ_m` of the Maass lift.

## Main results

* `SiegelUpperHalfSpace.maassLift_partialInversion_smul`: `F(J₁Z) = τ^k F(Z)`, if the series
  converges absolutely and every `φ_m` transforms under `(0, -1; 1, 0)` like a Jacobi form of
  weight `k` and index `m`.
* `SiegelUpperHalfSpace.maassLift_mem_scalarModularForms_of_summable`: the Maass lift of
  `φ ∈ J_{k,1}` is a Siegel modular form of weight `k` on `Sp(4, ℤ)` if its series converges
  absolutely, it is holomorphic and every `φ_m` is a Jacobi form of weight `k` and index `m`.
-/

open Complex ModularForm ModularGroup Real SymplecticGroup

open scoped UpperHalfPlane

namespace SiegelUpperHalfSpace

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} (m : ℤ) (x : ℍ × ℂ) (Z : SiegelUpperHalfSpace (Fin 2))

variable (k φ) in
/-- The `m`-th **Fourier–Jacobi coefficient** `φ_m(τ, z) = ∑_{n, r} a(n, r, m) e^{2πi(nτ + rz)}` of
the Maass lift `(Vφ)(τ, z, ω) = ∑_m φ_m(τ, z) e^{2πimω}` (LMFDB `mf.siegel.lift.maass`) of
`φ : ℍ × ℂ → ℂ`, where `a(n, r, m)` are the Fourier coefficients of the lift (`maassCoeff`). For
`m ≥ 1` it is the image `φ ∣ V_m` of `φ` under the index raising operator
`V_m : J_{k,1} → J_{k,m}` of Eichler and Zagier (§4), defined by its Fourier coefficients
`∑_{d ∣ (n, r, m)} d^{k-1} c(nm/d², r/d)`; for `m = 0` it is `c(0, 0)` times the Eisenstein series
`-B_k/2k + ∑_{n ≥ 1} σ_{k-1}(n) qⁿ`, and it vanishes for `m < 0`. The `tsum` is the junk value `0`
where the series does not converge absolutely. -/
noncomputable def maassFourierJacobi : ℂ :=
  ∑' q : ℤ × ℤ, maassCoeff k (jacobiCoeff φ) q.1 q.2 m * jacobiFourierExp q x

/-- The point `(τ, z) ∈ ℍ × ℂ` of `Z = (τ, z; z, ω) ∈ ℋ₂`. -/
private noncomputable def jacobiPoint : ℍ × ℂ :=
  (UpperHalfPlane.mk (Z.val 0 0) (Z.posDef_im.diag_pos (i := 0)), Z.val 0 1)

private lemma liftExp_eq_mul (q : ℤ × ℤ) : liftExp 1 q.1 q.2 m Z =
    jacobiFourierExp q (jacobiPoint Z) * cexp (2 * π * I * m * Z.val 1 1) := by
  rw [liftExp, jacobiFourierExp, ← Complex.exp_add]
  congr 1
  simp [jacobiPoint]
  ring1

/-- The bijection `ℤ × ℤ² ≃ ℤ³`, `(m, (n, r)) ↦ (n, r, m)`. -/
private def fiberEquiv : ℤ × (ℤ × ℤ) ≃ ℤ × ℤ × ℤ :=
  (Equiv.prodComm ℤ (ℤ × ℤ)).trans (Equiv.prodAssoc ℤ ℤ ℤ)

private lemma maassLift_eq_tsum (hs : Summable fun p : ℤ × ℤ × ℤ ↦
    maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z) :
    maassLift k φ Z =
      ∑' m : ℤ, maassFourierJacobi k φ m (jacobiPoint Z) * cexp (2 * π * I * m * Z.val 1 1) := by
  rw [maassLift, ← fiberEquiv.tsum_eq]
  refine (fiberEquiv.summable_iff.mpr hs).tsum_prod.trans <| tsum_congr fun m ↦ ?_
  rw [maassFourierJacobi, ← tsum_mul_right]
  refine tsum_congr fun q ↦ ?_
  rw [mul_assoc, ← liftExp_eq_mul]
  rfl

private lemma jacobiPoint_partialInversion_smul :
    jacobiPoint (map (Int.castRingHom ℝ) partialInversion • Z) =
      (S • (jacobiPoint Z).1, (jacobiPoint Z).2 / UpperHalfPlane.denom S (jacobiPoint Z).1) := by
  refine Prod.ext (UpperHalfPlane.ext ?_) ?_
  · rw [UpperHalfPlane.modular_S_smul]
    simp [jacobiPoint, val_partialInversion_smul]
  · rw [ModularGroup.denom_S]
    simp [jacobiPoint, val_partialInversion_smul]

private lemma maassFourierJacobi_of_neg (hm : m < 0) : maassFourierJacobi k φ m x = 0 := by
  rw [maassFourierJacobi]
  refine (tsum_congr fun q ↦ ?_).trans tsum_zero
  rw [maassCoeff, ite_eq_right (by omega), ite_eq_right (by omega), zero_mul]

/-- **The transformation law of the Maass lift under the partial inversion**
`J₁ : (τ, z; z, ω) ↦ (-1/τ, z/τ; z/τ, ω - z²/τ)`, `F(J₁Z) = τ^k F(Z)`, from its Fourier–Jacobi
expansion `F(Z) = ∑_m φ_m(τ, z) e^{2πimω}`: if the series of the lift converges absolutely on
`ℋ₂`, so that it can be summed over `m` first, and every Fourier–Jacobi coefficient `φ_m`
transforms under `(0, -1; 1, 0)` like a Jacobi form of weight `k` and index `m`,
`φ_m(-1/τ, z/τ) = τ^k e^{2πimz²/τ} φ_m(τ, z)`, then the factor `e^{2πimz²/τ}` cancels against the
shift `ω ↦ ω - z²/τ`. -/
lemma maassLift_partialInversion_smul (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2),
    Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hS : ∀ (m : ℕ) (x : ℍ × ℂ),
      maassFourierJacobi k φ m (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
        jacobiFactor k m x S * maassFourierJacobi k φ m x) :
    maassLift k φ (map (Int.castRingHom ℝ) partialInversion • Z) =
      Z.val 0 0 ^ k * maassLift k φ Z := by
  rw [maassLift_eq_tsum _ (hs _), maassLift_eq_tsum _ (hs Z), ← tsum_mul_left,
    jacobiPoint_partialInversion_smul]
  refine tsum_congr fun m ↦ ?_
  rcases lt_or_ge m 0 with hm | hm
  · rw [maassFourierJacobi_of_neg _ _ hm, maassFourierJacobi_of_neg _ _ hm, zero_mul, zero_mul,
      mul_zero]
  · rcases Int.eq_ofNat_of_zero_le hm with ⟨m, rfl⟩
    rw [hS m (jacobiPoint Z), jacobiFactor, ModularGroup.denom_S,
      val_partialInversion_smul]
    generalize maassFourierJacobi k φ m (jacobiPoint Z) = c
    have he : cexp (2 * π * I * m * Z.val 0 1 ^ 2 / Z.val 0 0) *
        cexp (2 * π * I * m * (Z.val 1 1 - Z.val 0 1 ^ 2 / Z.val 0 0)) =
          cexp (2 * π * I * m * Z.val 1 1) := by
      rw [← Complex.exp_add]
      congr 1
      ring1
    simp [jacobiPoint]
    linear_combination (Z.val 0 0 ^ k * c) * he

/-- **The theorem of Maass, reduced to the index raising operators and convergence** (LMFDB
`mf.siegel.lift.maass`): for `φ ∈ J_{k,1}`, if the series of the Maass lift converges absolutely on
`ℋ₂`, the lift is holomorphic, and every Fourier–Jacobi coefficient `φ_m` of the lift is a Jacobi
form of weight `k` and index `m`, then the Maass lift is a Siegel modular form of weight `k` on
`Sp(4, ℤ)`. For `m ≥ 1` the last condition is the theorem of Eichler and Zagier (Theorem 4.2) that
the index raising operator `V_m` maps `J_{k,1}` to `J_{k,m}`, and for `m = 0` it says that
`c(0, 0)` times the Eisenstein series `-B_k/2k + ∑ σ_{k-1}(n) qⁿ` is a modular form of weight
`k`. -/
lemma maassLift_mem_scalarModularForms_of_summable (hφ : φ ∈ jacobiFormSpace k 1)
    (hs : ∀ Z : SiegelUpperHalfSpace (Fin 2), Summable fun p : ℤ × ℤ × ℤ ↦
      maassCoeff k (jacobiCoeff φ) p.1 p.2.1 p.2.2 * liftExp 1 p.1 p.2.1 p.2.2 Z)
    (hF : IsHolomorphic (maassLift k φ))
    (hV : ∀ m : ℕ, maassFourierJacobi k φ m ∈ jacobiFormSpace k m) :
    maassLift k φ ∈ scalarModularForms k (integral (Fin 2)) :=
  maassLift_mem_scalarModularForms hφ hF fun Z ↦
    maassLift_partialInversion_smul Z hs fun m ↦ (hV m).2.1 S

end SiegelUpperHalfSpace
