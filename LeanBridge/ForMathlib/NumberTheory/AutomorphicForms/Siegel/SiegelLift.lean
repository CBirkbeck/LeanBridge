import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MiyawakiLift
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SaitoKurokawaLift
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeParameters

/-!
# Lifts of Siegel modular forms

A Siegel eigenform is a **lift** (LMFDB `mf.siegel.lift`) if its Euler factors are products of
Euler factors that arise from Siegel modular forms of lower degree. The Euler factors of a Siegel
Hecke eigenform `F` of level `Sp(2g, ℤ)` at `p` are the spinor and standard Euler factors of its
Satake parameters at `p` (`SiegelUpperHalfSpace.IsSatakeParameter`,
`SiegelUpperHalfSpace.spinorEulerFactor`, `SiegelUpperHalfSpace.standardEulerFactor`). The knowl
says neither which Euler factors nor which products: here a lift has, for one kind of Euler factor,
products of shifted Euler factors of eigenforms of lower degree and of the Riemann zeta function.

The Saito–Kurokawa lift (LMFDB `mf.siegel.lift.saito_kurokawa`) of `f ∈ S_{2k}(SL(2, ℤ))` with
Satake parameters `γ_±` at `p` has the Satake parameters `(p^{k-1}; γ₊ p^{1-k}, γ₋ p^{1-k})`, whose
spinor Euler factor is `Q_p(f, X)(1 - p^{k-1} X)(1 - p^k X)`: so `L(s, F) = L(s, f) ζ(s + 1/2)
ζ(s - 1/2)` in the analytic normalisation of the knowl. The conjectural Miyawaki lift of type II
(LMFDB `mf.siegel.lift.miyawaki2`) of `f ∈ S_{2k-2}(SL(2, ℤ))` and `g ∈ S_{k-2}(SL(2, ℤ))`, with
Satake parameters `γ_±` and `δ_±`, has the standard and spinor Euler factors of the knowl, which are
those of the one point `(δ₋ p^{k-1}; γ₊ p^{1-k}, γ₋ p^{1-k}, δ₊/δ₋)`.

Satake's theorem, that the Satake parameters of an eigenform exist and are unique up to the Weyl
group, is not proved in any degree. Its two consequences stated here,
`SiegelUpperHalfSpace.SatakeParametersExist` and `SiegelUpperHalfSpace.EulerFactorsWellDefined`, are
proved in degree `2` (`SiegelUpperHalfSpace.SiegelEigenform.exists_isSatakeParameter`,
`SiegelUpperHalfSpace.SiegelEigenform.eq_of_isEulerFactor`) and not in the other degrees. The Hecke
equivariance of the Saito–Kurokawa lift, `SiegelUpperHalfSpace.SaitoKurokawaSpinTheorem`, is proved
(`SiegelUpperHalfSpace.saitoKurokawaSpinTheorem`). Not proved: the existence of a Saito–Kurokawa
lift of each newform (Kohnen's theorem), and the existence of the Miyawaki lifts of type II, a
conjecture.

## Main definitions

* `HeckeRing.GL2.Newform.miyawaki2StandardEulerFactor`,
  `HeckeRing.GL2.Newform.miyawaki2SpinorEulerFactor`: the Euler factors of the knowl
  `mf.siegel.lift.miyawaki2`.
* `SiegelUpperHalfSpace.SaitoKurokawaSpinTheorem`: the spin `L`-function of the Saito–Kurokawa
  lifts, as a statement.
* `SiegelUpperHalfSpace.IsMiyawakiLiftTypeII`: a Miyawaki lift of type II.
* `SiegelUpperHalfSpace.EulerFactorKind`: the spinor and the standard Euler factors.
* `SiegelUpperHalfSpace.SiegelEigenform`: a Siegel Hecke eigenform of level `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.SiegelEigenform.IsEulerFactor`: an Euler factor of a Siegel eigenform.
* `SiegelUpperHalfSpace.SiegelEigenform.IsLift`: a lift.
* `SiegelUpperHalfSpace.SatakeParametersExist`, `SiegelUpperHalfSpace.EulerFactorsWellDefined`:
  Satake's theorem, as statements.

## Main theorems

* `HeckeRing.GL2.Newform.spinorEulerFactor_saitoKurokawa`,
  `HeckeRing.GL2.Newform.standardEulerFactor_saitoKurokawa`: the Euler factors of the Satake
  parameters of the Saito–Kurokawa lift.
* `HeckeRing.GL2.Newform.eval_spinorEulerFactor_saitoKurokawa`: the spinor Euler factor of the
  Saito–Kurokawa lift in the analytic normalisation.
* `HeckeRing.GL2.Newform.standardEulerFactor_miyawaki2`,
  `HeckeRing.GL2.Newform.spinorEulerFactor_miyawaki2`: the Euler factors of the Miyawaki lift of
  type II are those of one point.
* `SiegelUpperHalfSpace.saitoKurokawaSpinTheorem_of_isSatakeParameter`: the spin `L`-function of
  the Saito–Kurokawa lifts follows from their Satake parameters.
* `SiegelUpperHalfSpace.SiegelEigenform.isLift_const_two`: the constant of degree `2` is a lift.
-/

open Polynomial UpperHalfPlane

namespace HeckeRing.GL2.Newform

/-! ### The Saito–Kurokawa lift -/

section SaitoKurokawa

variable {k : ℤ} (f : Newform 1 (2 * k)) (p : ℕ) {a b : ℂ}

/-- **The spinor Euler factor of the Saito–Kurokawa lift** (LMFDB `mf.siegel.lift.saito_kurokawa`):
for Satake parameters `{a, b}` of `f ∈ S_{2k}(SL(2, ℤ))` at `p`, so that `a b = p^{2k-1}`, the
spinor Euler factor of `(p^{k-1}; a p^{1-k}, b p^{1-k})` is `Q_p(f, X)(1 - p^{k-1} X)(1 - p^k X)`,
the Euler factor of `L(f, s) ζ(s - k + 1) ζ(s - k)`. -/
lemma spinorEulerFactor_saitoKurokawa (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b}) :
    SiegelUpperHalfSpace.spinorEulerFactor ((p : ℂ) ^ (k - 1))
        ![a * (p : ℂ) ^ (1 - k), b * (p : ℂ) ^ (1 - k)] =
      f.ellipticEulerFactor p * (1 - C ((p : ℂ) ^ (k - 1)) * X) * (1 - C ((p : ℂ) ^ k) * X) := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e₁ (x : ℂ) : (p : ℂ) ^ (k - 1) * (x * (p : ℂ) ^ (1 - k)) = x := by
    rw [mul_left_comm, ← zpow_add₀ hp', sub_add_sub_cancel', sub_self, zpow_zero, mul_one]
  have e₂ : (p : ℂ) ^ (k - 1) * (a * (p : ℂ) ^ (1 - k) * (b * (p : ℂ) ^ (1 - k))) =
      (p : ℂ) ^ k := by
    rw [mul_mul_mul_comm, hab, ← mul_assoc, ← zpow_add₀ hp', ← zpow_add₀ hp', ← zpow_add₀ hp']
    exact congrArg _ (by ring1)
  rw [SiegelUpperHalfSpace.spinorEulerFactor_fin_two, ellipticEulerFactor_eq_prod, hf]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
  ring1

/-- **The standard Euler factor of the Saito–Kurokawa lift** (LMFDB
`mf.siegel.lift.saito_kurokawa`): for Satake parameters `{a, b}` of `f ∈ S_{2k}(SL(2, ℤ))` at `p`,
the standard Euler factor of `(a p^{1-k}, b p^{1-k})` is
`(1 - X) Q_p(f, p^{1-k} X) Q_p(f, p^{-k} X)`, the Euler factor of
`ζ(s) L(f, s + k - 1) L(f, s + k)`. -/
lemma standardEulerFactor_saitoKurokawa (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b}) :
    SiegelUpperHalfSpace.standardEulerFactor ![a * (p : ℂ) ^ (1 - k), b * (p : ℂ) ^ (1 - k)] =
      (1 - X) * (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (1 - k)) * X) *
        (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (-k)) * X) := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e (x y : ℂ) (hxy : x * y = (p : ℂ) ^ (2 * k - 1)) :
      (x * (p : ℂ) ^ (1 - k))⁻¹ = y * (p : ℂ) ^ (-k) :=
    inv_eq_of_mul_eq_one_right <| by
      rw [mul_mul_mul_comm, hxy, ← zpow_add₀ hp', ← zpow_add₀ hp', ← zpow_zero (p : ℂ)]
      exact congrArg _ (by ring1)
  simp only [SiegelUpperHalfSpace.standardEulerFactor, Fin.prod_univ_two, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [e a b hab, e b a ((mul_comm b a).trans hab), ellipticEulerFactor_eq_prod, hf]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, mul_comp, sub_comp, one_comp, C_comp, X_comp,
    map_mul]
  ring1

/-- **The spinor Euler factor of the Saito–Kurokawa lift in the analytic normalisation** (LMFDB
`mf.siegel.lift.saito_kurokawa`): at `X = p^{-(s + k - 1/2)}`, `Q_p(f, X)(1 - p^{k-1} X)(1 - p^k X)`
is `Q_p(f, X)(1 - p^{-(s + 1/2)})(1 - p^{-(s - 1/2)})`, the Euler factor of the knowl's
`L(s, f) ζ(s + 1/2) ζ(s - 1/2)`. -/
lemma eval_spinorEulerFactor_saitoKurokawa (hp : p ≠ 0) (s : ℂ) :
    (f.ellipticEulerFactor p * (1 - C ((p : ℂ) ^ (k - 1)) * X) * (1 - C ((p : ℂ) ^ k) * X)).eval
        ((p : ℂ) ^ (-(s + k - 1 / 2))) =
      (f.ellipticEulerFactor p).eval ((p : ℂ) ^ (-(s + k - 1 / 2))) *
        (1 - (p : ℂ) ^ (-(s + 1 / 2))) * (1 - (p : ℂ) ^ (-(s - 1 / 2))) := by
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e (j : ℤ) (w : ℂ) (hw : (j : ℂ) - (s + k - 1 / 2) = w) :
      (p : ℂ) ^ j * (p : ℂ) ^ (-(s + k - 1 / 2)) = (p : ℂ) ^ w := by
    rw [← Complex.cpow_intCast, ← Complex.cpow_add _ _ hp', ← hw]
    congr 1
  rw [eval_mul, eval_mul, eval_sub, eval_sub, eval_one, eval_mul, eval_mul, eval_C, eval_C, eval_X,
    e (k - 1) (-(s + 1 / 2)) (by push_cast; ring1), e k (-(s - 1 / 2)) (by ring1)]

end SaitoKurokawa

/-! ### The Miyawaki lift of type II -/

section Miyawaki

variable {k : ℤ} (f : Newform 1 (2 * k - 2)) (g : Newform 1 (k - 2)) (p : ℕ) {a b c d : ℂ}

/-- The **standard Euler factor of the Miyawaki lift of type II** (LMFDB
`mf.siegel.lift.miyawaki2`) of normalised Hecke eigenforms `f ∈ S_{2k-2}(SL(2, ℤ))` and
`g ∈ S_{k-2}(SL(2, ℤ))` at `p`: `Q_p(f, p^{1-k}X) Q_p(f, p^{2-k}X) Q_p^st(g, X)`, the Euler factor
of `L(f, s + k - 1) L(f, s + k - 2) L^st(g, s)`. It is the standard Euler factor
`SiegelUpperHalfSpace.standardEulerFactor` of explicit Satake parameters
(`HeckeRing.GL2.Newform.standardEulerFactor_miyawaki2`). -/
noncomputable def miyawaki2StandardEulerFactor : ℂ[X] :=
  (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (1 - k)) * X) *
    (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (2 - k)) * X) * g.standardEulerFactor p

/-- The **spinor Euler factor of the Miyawaki lift of type II** (LMFDB
`mf.siegel.lift.miyawaki2`) of normalised Hecke eigenforms `f ∈ S_{2k-2}(SL(2, ℤ))` and
`g ∈ S_{k-2}(SL(2, ℤ))` at `p`: `Q_p(g, p^{k-1}X) Q_p(g, p^{k-2}X) Q_p(f ⊗ g, X)`, the Euler factor
of `L(g, s - k + 1) L(g, s - k + 2) L(f ⊗ g, s)`. -/
noncomputable def miyawaki2SpinorEulerFactor : ℂ[X] :=
  (g.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (k - 1)) * X) *
    (g.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (k - 2)) * X) * f.rankinSelbergEulerFactor g p

/-- **The standard Euler factor of the Miyawaki lift of type II is that of an explicit point**
(LMFDB `mf.siegel.lift.miyawaki2`): for Satake parameters `{a, b}` of `f` and `{c, d}` of `g` at
`p`, the knowl's standard Euler factor is the standard Euler factor
`(1 - X) ∏_i (1 - α_i X)(1 - α_i⁻¹ X)` of `(α_0, α_1, α_2) = (a p^{1-k}, b p^{1-k}, c/d)`. -/
lemma standardEulerFactor_miyawaki2 (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b})
    (hg : g.satakeParameters p = {c, d}) :
    SiegelUpperHalfSpace.standardEulerFactor
        ![a * (p : ℂ) ^ (1 - k), b * (p : ℂ) ^ (1 - k), c / d] =
      f.miyawaki2StandardEulerFactor g p := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e (x y : ℂ) (hxy : x * y = (p : ℂ) ^ (2 * k - 2 - 1)) :
      (x * (p : ℂ) ^ (1 - k))⁻¹ = y * (p : ℂ) ^ (2 - k) :=
    inv_eq_of_mul_eq_one_right <| by
      rw [mul_mul_mul_comm, hxy, ← zpow_add₀ hp', ← zpow_add₀ hp', ← zpow_zero (p : ℂ)]
      exact congrArg _ (by ring1)
  simp only [SiegelUpperHalfSpace.standardEulerFactor, Fin.prod_univ_three, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [e a b hab, e b a ((mul_comm b a).trans hab), inv_div, miyawaki2StandardEulerFactor,
    ellipticEulerFactor_eq_prod, hf, standardEulerFactor, g.satakeRatios_eq p hg]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, mul_comp, sub_comp, one_comp, C_comp, X_comp,
    map_mul]
  ring1

/-- **The spinor Euler factor of the Miyawaki lift of type II is that of the same point** (LMFDB
`mf.siegel.lift.miyawaki2`): for Satake parameters `{a, b}` of `f` and `{c, d}` of `g` at `p`, the
knowl's spinor Euler factor is the spinor Euler factor `∏_{S ⊆ {0, 1, 2}} (1 - α₀ ∏_{i ∈ S} α_i X)`
of `α₀ = d p^{k-1}` and `(α_0, α_1, α_2) = (a p^{1-k}, b p^{1-k}, c/d)`, whose standard Euler factor
is the knowl's standard one (`HeckeRing.GL2.Newform.standardEulerFactor_miyawaki2`); and
`α₀² α_0 α_1 α_2 = p^{3k-6}` (`HeckeRing.GL2.Newform.sq_mul_prod_miyawaki2`), as for the Satake
parameters of an eigenform of weight `k` and degree `3`. -/
lemma spinorEulerFactor_miyawaki2 (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b})
    (hg : g.satakeParameters p = {c, d}) :
    SiegelUpperHalfSpace.spinorEulerFactor (d * (p : ℂ) ^ (k - 1))
        ![a * (p : ℂ) ^ (1 - k), b * (p : ℂ) ^ (1 - k), c / d] =
      f.miyawaki2SpinorEulerFactor g p := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hd : d ≠ 0 := g.ne_zero_of_mem_satakeParameters p hp
    (hg ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self d))
  have e₁ (x : ℂ) : d * (p : ℂ) ^ (k - 1) * (x * (p : ℂ) ^ (1 - k)) = x * d := by
    rw [mul_mul_mul_comm, ← zpow_add₀ hp', sub_add_sub_cancel', sub_self, zpow_zero, mul_one,
      mul_comm]
  have e₂ : d * (p : ℂ) ^ (k - 1) * (c / d) = c * (p : ℂ) ^ (k - 1) := by
    field_simp
  have e₃ : d * (p : ℂ) ^ (k - 1) * (a * (p : ℂ) ^ (1 - k) * (b * (p : ℂ) ^ (1 - k))) =
      d * (p : ℂ) ^ (k - 2) := by
    rw [mul_mul_mul_comm a, hab, mul_assoc, ← mul_assoc ((p : ℂ) ^ (k - 1)),
      ← zpow_add₀ hp', ← zpow_add₀ hp', ← zpow_add₀ hp']
    exact congrArg _ (congrArg _ (by ring1))
  have e₄ (x : ℂ) : d * (p : ℂ) ^ (k - 1) * (x * (p : ℂ) ^ (1 - k) * (c / d)) = x * c := by
    rw [← mul_assoc, e₁]
    field_simp
  have e₅ : d * (p : ℂ) ^ (k - 1) *
      (a * (p : ℂ) ^ (1 - k) * (b * (p : ℂ) ^ (1 - k) * (c / d))) = c * (p : ℂ) ^ (k - 2) := by
    rw [← mul_assoc (a * _), ← mul_assoc, e₃]
    field_simp
  rw [SiegelUpperHalfSpace.spinorEulerFactor_fin_three]
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [e₅, e₄ a, e₄ b, e₃, e₂, e₁ a, e₁ b, miyawaki2SpinorEulerFactor, ellipticEulerFactor_eq_prod,
    rankinSelbergEulerFactor, hf, hg]
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_product,
    Multiset.zero_product, Multiset.map_cons, Multiset.map_zero, Multiset.map_add,
    Multiset.prod_add, Multiset.prod_cons, Multiset.prod_zero, mul_comp, sub_comp, one_comp, C_comp,
    X_comp, map_mul]
  ring1

lemma sq_mul_prod_miyawaki2 (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b})
    (hg : g.satakeParameters p = {c, d}) :
    (d * (p : ℂ) ^ (k - 1)) ^ 2 * (a * (p : ℂ) ^ (1 - k) * (b * (p : ℂ) ^ (1 - k) * (c / d))) =
      (p : ℂ) ^ (3 * k - 6) := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rcases (g.satakeParameters_eq_pair_iff p).mp hg with ⟨-, hcd⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  rw [g.dirichletLift_natCast_eq_one, one_mul] at hcd
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hd : d ≠ 0 := g.ne_zero_of_mem_satakeParameters p hp
    (hg ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self d))
  have e :
      (d * (p : ℂ) ^ (k - 1)) ^ 2 * (a * (p : ℂ) ^ (1 - k) * (b * (p : ℂ) ^ (1 - k) * (c / d))) =
        a * b * (c * d) * ((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (1 - k)) ^ 2 := by
    field_simp
  rw [e, hab, hcd, ← zpow_add₀ hp' (k - 1), sub_add_sub_cancel', sub_self, zpow_zero, one_pow,
    mul_one, ← zpow_add₀ hp']
  exact congrArg _ (by ring1)

end Miyawaki

end HeckeRing.GL2.Newform

namespace SiegelUpperHalfSpace

open HeckeRing GL2

/-! ### The Saito–Kurokawa and Miyawaki lifts -/

/-- **The spin `L`-function of a Saito–Kurokawa lift** (LMFDB `mf.siegel.lift.saito_kurokawa`), as
a statement: for a normalised Hecke eigenform `f ∈ S_{2k}(SL(2, ℤ))` and a Saito–Kurokawa lift `F`
of `f` (of weight `k + 1`, `SiegelUpperHalfSpace.IsSaitoKurokawaLift`), at every prime `p`, `F` has
Satake parameters whose spinor Euler factor is `Q_p(f, X)(1 - p^{k-1} X)(1 - p^k X)`, so that
`L^spin(F, s) = L(f, s) ζ(s - k + 1) ζ(s - k)` in the classical normalisation, which is the knowl's
`L(s, F) = L(s, f) ζ(s + 1/2) ζ(s - 1/2)` in the analytic one
(`HeckeRing.GL2.Newform.eval_spinorEulerFactor_saitoKurokawa`). It amounts to the Satake parameters
`(p^{k-1}; γ₊ p^{1-k}, γ₋ p^{1-k})` of `F`, `γ_±` being those of `f`
(`HeckeRing.GL2.Newform.spinorEulerFactor_saitoKurokawa`), that is, to the Hecke equivariance of the
Saito–Kurokawa lift (Eichler and Zagier, §6, Theorem 6.3). It is proved as
`SiegelUpperHalfSpace.saitoKurokawaSpinTheorem`, through
`SiegelUpperHalfSpace.saitoKurokawaSpinTheorem_of_heckeOperator`, which reduces it to the
nonvanishing of the lifts and to their eigenvalues under `T(p)` and `T_1(p²)`. -/
def SaitoKurokawaSpinTheorem : Prop :=
  ∀ (k : ℤ) (f : Newform 1 (2 * k)) (F : SiegelUpperHalfSpace (Fin 2) → ℂ),
    IsSaitoKurokawaLift k f F → ∀ (p : ℕ) [Fact p.Prime], ∃ (α₀ : ℂˣ) (α : Fin 2 → ℂˣ),
      IsSatakeParameter p (TauCeti.detPowerRep ℂ 2 (k + 1)) F α₀ α ∧
        spinorEulerFactor (α₀ : ℂ) (fun i ↦ (α i : ℂ)) =
          f.ellipticEulerFactor p * (1 - C ((p : ℂ) ^ (k - 1)) * X) * (1 - C ((p : ℂ) ^ k) * X)

/-- **The spin `L`-function of the Saito–Kurokawa lifts follows from their Satake parameters**:
`SiegelUpperHalfSpace.SaitoKurokawaSpinTheorem` holds as soon as every Saito–Kurokawa lift of `f`
has, at every prime `p`, the Satake parameters `(p^{k-1}; γ₊ p^{1-k}, γ₋ p^{1-k})`, `γ_±` being
those of `f`. -/
lemma saitoKurokawaSpinTheorem_of_isSatakeParameter
    (h : ∀ (k : ℤ) (f : Newform 1 (2 * k)) (F : SiegelUpperHalfSpace (Fin 2) → ℂ),
      IsSaitoKurokawaLift k f F → ∀ (p : ℕ) [Fact p.Prime] (a b : ℂ),
        f.satakeParameters p = {a, b} → ∃ (α₀ : ℂˣ) (α : Fin 2 → ℂˣ),
          IsSatakeParameter p (TauCeti.detPowerRep ℂ 2 (k + 1)) F α₀ α ∧
            (α₀ : ℂ) = (p : ℂ) ^ (k - 1) ∧
              (fun i ↦ (α i : ℂ)) = ![a * (p : ℂ) ^ (1 - k), b * (p : ℂ) ^ (1 - k)]) :
    SaitoKurokawaSpinTheorem := by
  intro k f F hF p _
  rcases f.exists_satakeParameters_eq_pair p with ⟨a, b, hab⟩
  rcases h k f F hF p a b hab with ⟨α₀, α, hα, h₀, h₁⟩
  refine ⟨α₀, α, hα, ?_⟩
  rw [h₀, h₁]
  exact f.spinorEulerFactor_saitoKurokawa p (Fact.out : p.Prime).ne_zero hab

/-- `F` is a **Miyawaki lift of type II** (LMFDB `mf.siegel.lift.miyawaki2`, a conjectural lift) of
normalised Hecke eigenforms `f ∈ S_{2k-2}(SL(2, ℤ))` and `g ∈ S_{k-2}(SL(2, ℤ))`, `k` even: `F` is a
Siegel cusp form of weight `k` on `Sp(6, ℤ)` (a modular form whose Fourier coefficients vanish off
the positive definite matrices, the cusp forms of level `1`) and, at every prime `p`, a Hecke
eigenform with Satake parameters whose standard and spinor Euler factors are
`Q_p^st(F, X) = Q_p(f, p^{1-k} X) Q_p(f, p^{2-k} X) Q_p^st(g, X)` and
`Q_p^spin(F, X) = Q_p(g, p^{k-1} X) Q_p(g, p^{k-2} X) Q_p(f ⊗ g, X)`, the Euler factors of
`L^st(F, s) = L(f, s + k - 1) L(f, s + k - 2) L^st(g, s)` and
`L^spin(F, s) = L(g, s - k + 1) L(g, s - k + 2) L(f ⊗ g, s)`. Both are the Euler factors of the one
point `(δ₋ p^{k-1}; γ₊ p^{1-k}, γ₋ p^{1-k}, δ₊/δ₋)`
(`HeckeRing.GL2.Newform.standardEulerFactor_miyawaki2`,
`HeckeRing.GL2.Newform.spinorEulerFactor_miyawaki2`). -/
def IsMiyawakiLiftTypeII {k : ℤ} (f : Newform 1 (2 * k - 2)) (g : Newform 1 (k - 2))
    (F : SiegelUpperHalfSpace (Fin 3) → ℂ) : Prop :=
  Even k ∧ F ∈ scalarModularForms k (SymplecticGroup.integral (Fin 3)) ∧
    (∃ a : dualLattice (SymplecticGroup.integral (Fin 3)) → ℂ,
      HasSiegelFourierExpansion (SymplecticGroup.integral (Fin 3)) F a ∧
        ∀ T, a T ≠ 0 → (T : Matrix (Fin 3) (Fin 3) ℚ).PosDef) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ (α₀ : ℂˣ) (α : Fin 3 → ℂˣ),
        IsSatakeParameter p (TauCeti.detPowerRep ℂ 3 k) F α₀ α ∧
          standardEulerFactor (fun i ↦ (α i : ℂ)) = f.miyawaki2StandardEulerFactor g p ∧
            spinorEulerFactor (α₀ : ℂ) (fun i ↦ (α i : ℂ)) = f.miyawaki2SpinorEulerFactor g p

/-! ### The Euler factors of a Siegel eigenform and lifts -/

/-- The two kinds of **Euler factors** of a Siegel Hecke eigenform (LMFDB `mf.siegel.lift`): the
spinor Euler factor `SiegelUpperHalfSpace.spinorEulerFactor` and the standard Euler factor
`SiegelUpperHalfSpace.standardEulerFactor`. -/
inductive EulerFactorKind
  | spinor
  | standard

variable {n : ℕ} [NeZero n]

/-- The Euler factor of kind `t` of the Satake parameters `(α₀; α)`. -/
noncomputable def EulerFactorKind.eulerFactor : EulerFactorKind → ℂ → (Fin n → ℂ) → ℂ[X]
  | .spinor, α₀, α => spinorEulerFactor α₀ α
  | .standard, _, α => standardEulerFactor α

/-- A **Siegel Hecke eigenform** of level `Sp(2g, ℤ)` (LMFDB `mf.siegel.lift`), of some degree
`g ≥ 1` and weight `ρ`: a nonzero holomorphic `Sp(2g, ℤ)`-invariant function of weight `ρ` that is
an eigenvector of every Hecke operator (`SiegelUpperHalfSpace.IsHeckeEigenform`). -/
structure SiegelEigenform where
  /-- The degree `g`. -/
  degree : ℕ
  [neZero : NeZero degree]
  /-- The space of values. -/
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module ℂ V]
  /-- The weight. -/
  ρ : Representation ℂ (GL (Fin degree) ℂ) V
  /-- The eigenform. -/
  form : slashInvariants ρ
  isHeckeEigenform : IsHeckeEigenform ρ form

attribute [instance] SiegelEigenform.neZero SiegelEigenform.addCommGroup SiegelEigenform.module

variable (F : SiegelEigenform) (t : EulerFactorKind) (p : ℕ) [Fact p.Prime]

/-- `Q` is an **Euler factor of kind `t`** of the Siegel eigenform `F` at `p` (LMFDB
`mf.siegel.lift`): the Euler factor of kind `t` of a Satake parameter of `F` at `p`. By Satake's
theorem the Satake parameters form one orbit of the Weyl group of signed permutations, on which the
Euler factors are constant, so that `Q` is unique (`SiegelUpperHalfSpace.EulerFactorsWellDefined`).
In degree `2` the uniqueness is `SiegelUpperHalfSpace.SiegelEigenform.eq_of_isEulerFactor`, the
Euler factors being functions of the Satake map; in the other degrees it is not proved. -/
def SiegelEigenform.IsEulerFactor (Q : ℂ[X]) : Prop :=
  ∃ α₀ α, IsSatakeParameter p F.ρ (F.form : SiegelUpperHalfSpace (Fin F.degree) → F.V) α₀ α ∧
    t.eulerFactor (α₀ : ℂ) (fun i ↦ (α i : ℂ)) = Q

/-- A Siegel eigenform `F` is a **lift** (LMFDB `mf.siegel.lift`) if its Euler factors are products
of Euler factors that arise from Siegel eigenforms of lower degree: for one kind of Euler factor of
`F` (spinor or standard; the knowl does not say which, and the LMFDB's lifts use both), finitely
many eigenforms `G_i` of degree less than that of `F`, kinds `u_i` and integer shifts `a_i`, and
shifts `c_j` of Euler factors `1 - p^{c_j} X` of degree `0` (those of the Riemann zeta function, the
`L`-function of the Siegel modular forms of degree `0`), at every prime `p`,
`Q_p(F, X) = ∏_i Q_p^{u_i}(G_i, p^{a_i} X) ∏_j (1 - p^{c_j} X)`. Rankin–Selberg factors
`Q_p(f ⊗ g, X)` of two forms are not counted as Euler factors of lower degree; the Saito–Kurokawa,
Yoshida, Klingen and Ikeda lifts are lifts in this sense through their spinor or standard Euler
factors, and the Miyawaki lifts through their standard Euler factors. -/
def SiegelEigenform.IsLift : Prop :=
  ∃ (t : EulerFactorKind) (m : ℕ) (G : Fin m → SiegelEigenform) (u : Fin m → EulerFactorKind)
    (a : Fin m → ℤ) (c : Multiset ℤ), (∀ i, (G i).degree < F.degree) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ (Q : ℂ[X]) (R : Fin m → ℂ[X]), F.IsEulerFactor t p Q ∧
        (∀ i, (G i).IsEulerFactor (u i) p (R i)) ∧
          Q = (∏ i, (R i).comp (C ((p : ℂ) ^ a i) * X)) *
            (c.map fun j ↦ 1 - C ((p : ℂ) ^ j) * X).prod

/-- **The existence of Satake parameters** (Satake; Andrianov, *Quadratic forms and Hecke
operators*, Theorem 3.3.30), as a statement: every Siegel eigenform has Satake parameters at every
prime `p`, so that it has Euler factors of both kinds. It follows from the isomorphism of the
Satake map onto the invariants of the Weyl group `W_g` of signed permutations in the Laurent
polynomials, which is not proved here. In degree `2` it is
`SiegelUpperHalfSpace.SiegelEigenform.exists_isSatakeParameter`, from generators of the local Hecke
algebra; in the other degrees it is not proved. -/
def SatakeParametersExist : Prop :=
  ∀ (G : SiegelEigenform) (q : ℕ) [Fact q.Prime], ∃ α₀ α,
    IsSatakeParameter q G.ρ (G.form : SiegelUpperHalfSpace (Fin G.degree) → G.V) α₀ α

/-- **The Euler factors of a Siegel eigenform are well defined**, as a statement: the Euler factors
of each kind of the Satake parameters of a Siegel eigenform at `p` are all equal. It follows from
Satake's theorem, by which the Satake parameters form one orbit of the Weyl group `W_g` of signed
permutations, and from the invariance of the Euler factors under `W_g`, generated by the
permutations of `α_0, …, α_{g-1}` and by `(α₀; α) ↦ (α₀ α_j; …, α_j⁻¹, …)` (proved for both
Euler factors); the first is not proved here. In degree `2` it is
`SiegelUpperHalfSpace.SiegelEigenform.eq_of_isEulerFactor`, the Euler factors being functions of the
Satake map; in the other degrees it is not proved. -/
def EulerFactorsWellDefined : Prop :=
  ∀ (G : SiegelEigenform) (u : EulerFactorKind) (q : ℕ) [Fact q.Prime] (Q Q' : ℂ[X]),
    G.IsEulerFactor u q Q → G.IsEulerFactor u q Q' → Q = Q'

variable (n) in
/-- The constant `1` of trivial weight in degree `n`, a Siegel eigenform. -/
noncomputable def SiegelEigenform.const : SiegelEigenform where
  degree := n
  V := ℂ
  ρ := Representation.trivial ℂ (GL (Fin n) ℂ) ℂ
  form := ⟨Function.const _ 1, ((mem_modularForms_iff_slashInvariants _ _).mp
    (const_mem_modularForms (SymplecticGroup.integral (Fin n)) 1)).2⟩
  isHeckeEigenform := isHeckeEigenform_const one_ne_zero

variable (n) in
lemma SiegelEigenform.isEulerFactor_const :
    (SiegelEigenform.const n).IsEulerFactor .spinor p (spinorEulerFactor
      (((primeUnit p ^ slashExponent (Representation.trivial ℂ (GL (Fin n) ℂ) ℂ) : ℂˣ) : ℂ))
        fun i : Fin n ↦ ((primeUnit p ^ (n - (i : ℕ)) : ℂˣ) : ℂ)) :=
  ⟨_, _, isSatakeParameter_const p (one_ne_zero : (1 : ℂ) ≠ 0), rfl⟩

/-- **The constant of degree `2` is a lift of the constant of degree `1`** (LMFDB
`mf.siegel.lift`): with `e_g` the exponent of the multiplier in the slash operator of trivial weight
in degree `g`, its spinor Euler factor `∏_{i=0}^3 (1 - p^{e_2 + i} X)` is the product of the spinor
Euler factors `(1 - p^{e_1} X)(1 - p^{e_1 + 1} X)` of the constant of degree `1` at
`p^{e_2 - e_1} X` and at `p^{e_2 - e_1 + 2} X`. So `SiegelUpperHalfSpace.SiegelEigenform.IsLift` is
satisfied. -/
lemma SiegelEigenform.isLift_const_two : (SiegelEigenform.const 2).IsLift := by
  refine ⟨.spinor, 2, fun _ ↦ .const 1, fun _ ↦ .spinor,
    ![slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) -
      slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ),
      slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) -
        slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ) + 2], 0,
    fun _ ↦ Nat.one_lt_two, fun q _ ↦ ⟨_, _, isEulerFactor_const 2 q,
      fun _ ↦ isEulerFactor_const 1 q, ?_⟩⟩
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hu (m : ℤ) : ((primeUnit q ^ m : ℂˣ) : ℂ) = (q : ℂ) ^ m := by
    rw [Units.val_zpow_eq_zpow_val, primeUnit, Units.val_mk0]
  have hu' (m : ℕ) : ((primeUnit q ^ m : ℂˣ) : ℂ) = (q : ℂ) ^ m := by
    rw [Units.val_pow_eq_pow_val, primeUnit, Units.val_mk0]
  have h₂ : (q : ℂ) ^ slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) =
      (q : ℂ) ^ slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ) *
        (q : ℂ) ^ (slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) -
          slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ)) := by
    rw [← zpow_add₀ hq, add_sub_cancel]
  have h₃ : (q : ℂ) ^ (slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) -
      slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ) + 2) =
        (q : ℂ) ^ (slashExponent (Representation.trivial ℂ (GL (Fin 2) ℂ) ℂ) -
          slashExponent (Representation.trivial ℂ (GL (Fin 1) ℂ) ℂ)) * (q : ℂ) ^ 2 := by
    rw [zpow_add₀ hq, zpow_two, sq]
  simp only [spinorEulerFactor_fin_two, spinorEulerFactor_fin_one, hu, hu', Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, h₂, h₃, Multiset.map_zero, Multiset.prod_zero,
    mul_comp, sub_comp, one_comp, C_comp, X_comp, map_mul, Fin.val_zero, Fin.val_one]
  ring1

end SiegelUpperHalfSpace
