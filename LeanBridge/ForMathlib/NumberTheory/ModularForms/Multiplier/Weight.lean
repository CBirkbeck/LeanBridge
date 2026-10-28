import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# The weight of an elliptic modular form

The weight of a modular form `f` with character `χ` on `Γ₀(N)` is the number `k` in its
transformation law `f(γz) = χ(d) (cz + d)^k f(z)`. For integral `k` this is Tau Ceti's nebentypus
law of `M_k(Γ₁(N), χ)`. For half-integral `k` the power `(cz + d)^k` has to be corrected by
Shimura's theta multiplier: the law is `f(γz) = χ(d) j(γ, z)^(2k) f(z)` on `Γ₀(N)` with `4 ∣ N`,
where `j(γ, z) = (c/d) ε_d⁻¹ (cz + d)^(1/2)` is the automorphy factor of `θ(z) = Σ q^(n²)`, `(c/d)`
is Shimura's extension of the Jacobi symbol and `ε_d` is `1` or `i` as `d ≡ 1` or `3 (mod 4)`. In
both cases a nonzero `f` determines `k`.

## Main definitions

* `ModularForm.shimuraSymbol`: Shimura's symbol `(c/d)` for odd `d` of either sign.
* `ModularForm.thetaFactor`: the theta multiplier `j(γ, z)`.
* `ModularForm.weightFactor`: the automorphy factor of weight `n / 2`.
* `ModularForm.HasWeight` (LMFDB `cmf.weight`).

## Main results

* `ModularForm.HasWeight.unique`: a nonzero function satisfies the transformation law of at most
  one weight.
* `ModularForm.mem_modFormCharSpace_iff_hasWeight`: in integral weight `k`, the transformation law
  is the nebentypus law of Tau Ceti's `M_k(Γ₁(N), χ)`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. 97 (1973), 440–481.
* N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, 2nd ed., GTM 97, Chapter IV.
-/

open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace ModularForm

variable {f : ℍ → ℂ} {N N' : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {w w' : ℚ} {k : ℤ} (n : ℤ) (γ : SL(2, ℤ)) (z : ℍ) (c d : ℤ)

/-- **Shimura's symbol** `(c/d)` for odd `d` of either sign: the Jacobi symbol `(c/|d|)`, negated
when `c < 0` and `d < 0`; in particular `(0/±1) = 1`. -/
def shimuraSymbol : ℤ :=
  if c < 0 ∧ d < 0 then -jacobiSym c d.natAbs else jacobiSym c d.natAbs

/-- The constant `ε_d` of the theta multiplier: `1` if `d ≡ 1 (mod 4)` and `i` otherwise (that is,
if `d ≡ 3 (mod 4)` for odd `d`). -/
noncomputable def thetaEpsilon : ℂ :=
  if d % 4 = 1 then 1 else Complex.I

/-- **Shimura's theta multiplier** `j(γ, z) = (c/d) ε_d⁻¹ (cz + d)^(1/2)`, with the principal
square root: for `γ ∈ Γ₀(4)` it is the automorphy factor `θ(γz) / θ(z)` of the theta function
`θ(z) = Σ q^(n²)`, the automorphy factor of weight `1/2`. -/
noncomputable def thetaFactor : ℂ :=
  shimuraSymbol (γ 1 0) (γ 1 1) * (thetaEpsilon (γ 1 1))⁻¹ * denom γ z ^ (1 / 2 : ℂ)

lemma thetaFactor_neg_one : thetaFactor (-1) z = 1 := by
  have h : (-1 : ℂ) ^ (2⁻¹ : ℂ) = Complex.I := by
    rw [cpow_def_of_ne_zero (neg_ne_zero.mpr one_ne_zero), log_neg_one, mul_assoc,
      mul_comm Complex.I, ← mul_assoc, ← div_eq_mul_inv, exp_pi_div_two_mul_I]
  rw [thetaFactor, ModularGroup.denom_apply]
  simp [shimuraSymbol, thetaEpsilon, h]

/-- The **automorphy factor of weight `n / 2`**: `(cz + d)^(n/2)` for even `n`, and `j(γ, z)^n`
for odd `n`, where `j` is the theta multiplier. -/
noncomputable def weightFactor : ℂ :=
  if Even n then denom γ z ^ (n / 2) else thetaFactor γ z ^ n

variable (f N χ w) in
/-- A function `f : ℍ → ℂ` **has weight** (LMFDB `cmf.weight`) `w` for `Γ₀(N)` and the Dirichlet
character `χ` modulo `N` if `w` is an integer or a half-integer and
`f(γz) = χ(d) (cz + d)^w f(z)` for every `γ = (a, b; c, d) ∈ Γ₀(N)` and `z ∈ ℍ`. For half-integral
`w` the factor `(cz + d)^w` is replaced by `j(γ, z)^(2w)`, where `j` is Shimura's theta multiplier
(`thetaFactor`), and `4 ∣ N` is required. The LMFDB's formula `χ(d) (cz + d)^w` omits the theta
multiplier, without which the law has no nonzero solution for half-integral `w` (at `γ = -I` it
reads `f = ± i χ(-1) f`). By `HasWeight.unique`, the weight of a nonzero `f` is unique. -/
def HasWeight : Prop :=
  ∃ m : ℤ, (m : ℚ) = 2 * w ∧ (Odd m → 4 ∣ N) ∧
    ∀ γ ∈ Gamma0 N, ∀ z, f (γ • z) = χ (γ 1 1) * weightFactor m γ z * f z

/-- The lower unipotent matrix `(1, 0; c, 1)` of `SL(2, ℤ)`. -/
private def lowerUnipotent : SL(2, ℤ) :=
  ⟨!![1, 0; c, 1], by simp⟩

private lemma norm_weightFactor_lowerUnipotent :
    ‖weightFactor n (lowerUnipotent c) z‖ = ‖(c : ℂ) * z + 1‖ ^ ((n : ℝ) / 2) := by
  have hd : denom (lowerUnipotent c) z = c * z + 1 := by
    rw [ModularGroup.denom_apply]
    simp [lowerUnipotent]
  rw [weightFactor]
  split_ifs with hn
  · rcases hn with ⟨m, rfl⟩
    have hm : (m + m) / 2 = m := by omega
    rw [hd, norm_zpow, hm, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring1
  · have h2 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    have hθ : thetaFactor (lowerUnipotent c) z = (c * z + 1) ^ (1 / 2 : ℂ) := by
      rw [thetaFactor, hd]
      simp [lowerUnipotent, shimuraSymbol, thetaEpsilon]
    rw [hθ, norm_zpow, h2, norm_cpow_real, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring1

variable {c} in
private lemma lowerUnipotent_mem_Gamma0 (hc : (N : ℤ) ∣ c) : lowerUnipotent c ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simpa [lowerUnipotent, ZMod.intCast_zmod_eq_zero_iff_dvd] using hc

variable (N N') in
private lemma one_lt_norm [NeZero N] [NeZero N'] :
    1 < ‖((((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ) : ℤ) : ℂ) * z + 1‖ := by
  refine lt_of_lt_of_le ?_ (abs_im_le_norm _)
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
  have hN' : (1 : ℝ) ≤ N' := Nat.one_le_cast.mpr NeZero.one_le
  have hm : 1 < ((⌈z.im⁻¹⌉₊ : ℝ) + 1) * z.im := by
    nlinarith [Nat.le_ceil z.im⁻¹, z.im_pos, inv_mul_cancel₀ z.im_pos.ne']
  simp only [Int.cast_natCast, add_im, mul_im, natCast_re, natCast_im, coe_im, one_im]
  refine lt_of_lt_of_le ?_ (le_abs_self _)
  push_cast
  nlinarith [mul_le_mul hN hN' zero_le_one (zero_le_one.trans hN), z.im_pos]

/-- **The weight is determined by the form**: a nonzero function satisfies the transformation
laws of at most one weight, whatever the (positive) levels and the characters. The proof compares
the two laws at `(1, 0; c, 1)` for a large multiple `c` of both levels, where `|cz + 1| > 1`. -/
lemma HasWeight.unique [NeZero N] [NeZero N'] (hf : f ≠ 0) (h : HasWeight f N χ w)
    (h' : HasWeight f N' χ' w') : w = w' := by
  rcases h with ⟨m, hm, -, h⟩
  rcases h' with ⟨m', hm', -, h'⟩
  rcases Function.ne_iff.mp hf with ⟨z, hz⟩
  have hγ : lowerUnipotent ((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ) ∈ Gamma0 N :=
    lowerUnipotent_mem_Gamma0 ⟨((⌈z.im⁻¹⌉₊ + 1) * N' : ℕ), by push_cast; ring1⟩
  have hγ' : lowerUnipotent ((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ) ∈ Gamma0 N' :=
    lowerUnipotent_mem_Gamma0 ⟨((⌈z.im⁻¹⌉₊ + 1) * N : ℕ), by push_cast; ring1⟩
  have hw : weightFactor m (lowerUnipotent ((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ)) z =
      weightFactor m' (lowerUnipotent ((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ)) z := by
    refine mul_right_cancel₀ hz ?_
    simpa [lowerUnipotent] using (h _ hγ z).symm.trans (h' _ hγ' z)
  have h1 : 1 < ‖((((⌈z.im⁻¹⌉₊ + 1) * N * N' : ℕ) : ℤ) : ℂ) * z + 1‖ := one_lt_norm N N' z
  have hm2 : (m : ℝ) / 2 = m' / 2 := by
    refine (Real.rpow_right_inj (zero_lt_one.trans h1) h1.ne').mp ?_
    rw [← norm_weightFactor_lowerUnipotent, ← norm_weightFactor_lowerUnipotent, hw]
  have hmm : m = m' := by exact_mod_cast (div_left_inj' two_ne_zero).mp hm2
  rw [hmm] at hm
  linarith

variable (k) in
lemma hasWeight_intCast_iff :
    HasWeight f N χ k ↔ ∀ γ ∈ Gamma0 N, ∀ z, f (γ • z) = χ (γ 1 1) * denom γ z ^ k * f z := by
  have he : ∀ γ z, weightFactor (2 * k) γ z = denom γ z ^ k := fun γ z ↦ by
    simp [weightFactor]
  constructor
  · rintro ⟨m, hm, -, h⟩
    have hm : m = 2 * k := by exact_mod_cast hm
    rw [hm] at h
    exact fun γ hγ z ↦ he γ z ▸ h γ hγ z
  · exact fun h ↦ ⟨2 * k, by push_cast; rfl, fun hk ↦
      absurd (even_two_mul k) (Int.not_even_iff_odd.mpr hk), fun γ hγ z ↦ (he γ z).symm ▸ h γ hγ z⟩

private lemma slash_eq_smul_iff (a : ℂ) :
    f ∣[k] mapGL ℝ γ = a • f ↔ ∀ z, f (γ • z) = a * denom γ z ^ k * f z := by
  have e : f ∣[k] mapGL ℝ γ = f ∣[k] γ := rfl
  rw [e, funext_iff]
  refine forall_congr' fun z ↦ ?_
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, zpow_neg, ← div_eq_mul_inv,
    div_eq_iff (zpow_ne_zero _ (denom_ne_zero _ _)), mul_right_comm]

/-- **In integral weight the transformation law is the nebentypus law**: a modular form of weight
`k` for `Γ₁(N)` lies in Tau Ceti's `M_k(Γ₁(N), χ)` exactly when it has weight `k` for `Γ₀(N)` and
`χ`, so that its weight in the sense of `HasWeight` is the weight `k` of its type. -/
lemma mem_modFormCharSpace_iff_hasWeight (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    g ∈ modFormCharSpace k χ.toUnitHom ↔ HasWeight g N χ k := by
  rw [mem_modFormCharSpace_iff_nebentypus, hasWeight_intCast_iff]
  refine ⟨fun h γ hγ ↦ ?_, fun h γ ↦ (slash_eq_smul_iff γ _).mpr ?_⟩
  · simpa [Gamma0Map_apply] using (slash_eq_smul_iff γ _).mp (h ⟨γ, hγ⟩)
  · simpa [Gamma0Map_apply] using h γ γ.2

end ModularForm
