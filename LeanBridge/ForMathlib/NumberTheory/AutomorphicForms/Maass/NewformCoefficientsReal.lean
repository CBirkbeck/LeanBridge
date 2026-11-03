import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSelfAdjoint
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.HeckeSineExpansion

/-!
# The coefficients of a normalised Maass newform are real

Let `F` be a Maass newform of weight `0` on `Γ₀(N)` with trivial character
(`UpperHalfPlane.IsMaassNewform`) with a cosine or sine expansion
`F(x + iy) = ∑_{n ≥ 1} a(n) √y K_{iR}(2πny) cos(2πnx)` (resp. `sin(2πnx)`) (LMFDB
`mf.maass.mwf.coefficients`). For a prime `p ∤ N` with `T_p F = λ_p F`, the uniqueness of the
coefficients gives the Hecke relation `a(pm) + a(m/p) = λ_p a(m)` for every `m ≥ 1` (the second
term only for `p ∣ m`), and `λ_p` is real (`UpperHalfPlane.IsMaassNewform.conj_heckeEigenvalue`,
from the self-adjointness of `T_p`). By induction on `n`, the coefficients `a(n) / a(1)` of the
newform normalised by `a(1) = 1` are real for every `n` prime to `N`, and if `a(1) = 0`, then
`a(n) = 0` for every `n` prime to `N`; at level `1` this forces `F = 0`, so `a(1) ≠ 0`.

At every level `N ≠ 0`, `a(1) ≠ 0` and `a(n) / a(1)` is real for every `n`, `gcd(n, N) > 1` included
(`UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_cosine`,
`UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_cosine` and the sine versions, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner`), by the Main Lemma
of Atkin and Lehner for Maass forms. That a newform is an eigenfunction of the operators `U_p`,
`p ∣ N`, with real eigenvalues `0` or `±p^{-1/2}` for trivial character, is not proved and not
needed; the definition `IsMaassNewform` only asks for the `T_p`, `p ∤ N`.

## Main results

* `UpperHalfPlane.HasMaassCosineExpansion.coeff_mul_add_eq`,
  `UpperHalfPlane.HasMaassSineExpansion.coeff_mul_add_eq`: the Hecke relation
  `a(pm) + a(m/p) = λ_p a(m)` for a `T_p`-eigenfunction.
* `UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_hasMaassCosineExpansion`,
  `UpperHalfPlane.IsMaassNewform.conj_coeff_div_of_hasMaassSineExpansion`: the coefficients
  `a(n) / a(1)`, `n` prime to `N`, of the normalised Maass newform are real.
* `UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_hasMaassCosineExpansion`,
  `UpperHalfPlane.IsMaassNewform.coeff_one_ne_zero_of_hasMaassSineExpansion`: a Maass newform of
  level `1` has `a(1) ≠ 0`.
-/

open scoped ComplexConjugate

namespace UpperHalfPlane

variable {N p : ℕ} {eigenvalue r e : ℂ} {F : ℍ → ℂ} {c : ℕ+ → ℂ} {f : ℂ → ℂ}

/-- **The Hecke relation for a sine expansion**: if `f` has the sine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) sin(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`c(pm) + c(m/p) = λ_p c(m)` for every `m ≥ 1`, the second term only for `p ∣ m`. -/
lemma HasMaassSineExpansion.coeff_mul_add_eq (hp : p.Prime) (h : HasMaassSineExpansion f r c)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = e * f z) (m : ℕ+) :
    c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m := by
  have hb : HasMaassSineExpansion (maassHeckeOperator p f) r fun n ↦ e * c n := by
    intro z
    rw [hT z z.im_pos]
    simpa only [mul_assoc] using (h z).mul_left e
  exact congrFun ((hasMaassSineExpansion_maassHeckeOperator hp.ne_zero h).unique hb) m

/-- **The Hecke relation for a cosine expansion**: if `f` has the cosine expansion
`f(x + iy) = ∑ c(n) √y K_{iR}(2πny) cos(2πnx)` and `T_p f = λ_p f` on `ℍ` for a prime `p`, then
`c(pm) + c(m/p) = λ_p c(m)` for every `m ≥ 1`, the second term only for `p ∣ m`, by the
uniqueness of the Fourier coefficients of `T_p f`. -/
lemma HasMaassCosineExpansion.coeff_mul_add_eq (hp : p.Prime) (h : HasMaassCosineExpansion f r c)
    (hT : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p f z = e * f z) (m : ℕ+) :
    c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m := by
  let a : ℤ → ℂ := fun n ↦
    if 0 < n then c n.toNat.toPNat' / 2 else if n < 0 then c (-n).toNat.toPNat' / 2 else 0
  have ha : HasMaassFourierExpansion f r a := h.hasMaassFourierExpansion
  have hb : HasMaassFourierExpansion (maassHeckeOperator p f) r fun n ↦ e * a n := by
    intro z
    rw [hT z z.im_pos]
    simpa only [mul_assoc] using (ha z).mul_left e
  have ha' (k : ℕ+) : a ((k : ℕ) : ℤ) = c k / 2 := by
    simp [a]
  rcases (Complex.I * r).exists_besselK_ne_zero with ⟨x, hx, hK⟩
  have key' : a (p * ((m : ℕ) : ℤ)) + (if (p : ℤ) ∣ ((m : ℕ) : ℤ) then a (((m : ℕ) : ℤ) / p)
      else 0) = e * a ((m : ℕ) : ℤ) :=
    mul_right_cancel₀ hK <| by
      simpa only [two_pi_mul_div m hx] using
        (hasMaassFourierExpansion_maassHeckeOperator hp.ne_zero ha).mul_besselK_eq hb
          ((m : ℕ) : ℤ) (div_pos hx (by positivity : (0 : ℝ) < 2 * Real.pi * (m : ℕ)))
  have e1 : (p : ℤ) * ((m : ℕ) : ℤ) = (((p.toPNat' * m : ℕ+) : ℕ) : ℤ) := by
    rw [PNat.mul_coe, PNat.toPNat'_coe hp.pos, Nat.cast_mul]
  rw [e1, ha', ha'] at key'
  by_cases hpm : p ∣ (m : ℕ)
  · have hq : 0 < (m : ℕ) / p := Nat.div_pos (Nat.le_of_dvd m.pos hpm) hp.pos
    have e2 : ((m : ℕ) : ℤ) / (p : ℤ) = ((((m : ℕ) / p).toPNat' : ℕ) : ℤ) := by
      rw [PNat.toPNat'_coe hq, Int.natCast_div]
    rw [ite_eq_left (Int.natCast_dvd_natCast.mpr hpm), e2, ha'] at key'
    rw [ite_eq_left hpm]
    linear_combination 2 * key'
  · rw [ite_eq_right (mt Int.natCast_dvd_natCast.mp hpm)] at key'
    rw [ite_eq_right hpm]
    linear_combination 2 * key'

lemma coeff_of_coprime {P Q : ℂ → Prop} (h0 : P 0) (hP : ∀ e x y, Q e → P x → P y → P (e * x - y))
    (hc1 : P (c 1)) (hrec : ∀ p : ℕ, p.Prime → ¬p ∣ N → ∃ e : ℂ, Q e ∧ ∀ m : ℕ+,
      c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) : P (c n) := by
  induction hnk : (n : ℕ) using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    by_cases h1 : n = 1
    · rwa [h1]
    · rcases Nat.exists_prime_and_dvd fun h ↦ h1 (PNat.coe_eq_one_iff.mp h) with ⟨p, hp, hpn⟩
      have hpN : ¬p ∣ N := fun h ↦
        hp.one_lt.ne' ((hn.coprime_dvd_left hpn).eq_one_of_dvd h)
      rcases hrec p hp hpN with ⟨e, he, hrec'⟩
      have hm : (((n : ℕ) / p).toPNat' : ℕ) = (n : ℕ) / p :=
        PNat.toPNat'_coe (Nat.div_pos (Nat.le_of_dvd n.pos hpn) hp.pos)
      have hnm : p.toPNat' * ((n : ℕ) / p).toPNat' = n := by
        apply PNat.eq
        rw [PNat.mul_coe, PNat.toPNat'_coe hp.pos, hm, Nat.mul_div_cancel' hpn]
      have hmk : (((n : ℕ) / p).toPNat' : ℕ) < k := by
        rw [hm, ← hnk]
        exact Nat.div_lt_self n.pos hp.one_lt
      have hmc : (((n : ℕ) / p).toPNat' : ℕ).Coprime N := by
        rw [hm]
        exact hn.coprime_dvd_left (Nat.div_dvd_of_dvd hpn)
      have key : c (p.toPNat' * ((n : ℕ) / p).toPNat') + (if p ∣ (((n : ℕ) / p).toPNat' : ℕ) then
          c ((((n : ℕ) / p).toPNat' : ℕ) / p).toPNat' else 0) = e * c ((n : ℕ) / p).toPNat' :=
        hrec' _
      rw [hnm] at key
      rw [eq_sub_of_add_eq key]
      refine hP e _ _ he (ih _ hmk hmc rfl) ?_
      split_ifs with hpm
      · have hq0 : 0 < (((n : ℕ) / p).toPNat' : ℕ) / p :=
          Nat.div_pos (Nat.le_of_dvd (PNat.pos _) hpm) hp.pos
        refine ih _ ((Nat.div_lt_self (PNat.pos _) hp.one_lt).trans hmk) ?_ (PNat.toPNat'_coe hq0)
        rw [PNat.toPNat'_coe hq0]
        exact hmc.coprime_dvd_left (Nat.div_dvd_of_dvd hpm)
      · exact h0

lemma conj_coeff_div_of_coprime (hc1 : c 1 ≠ 0)
    (hrec : ∀ p : ℕ, p.Prime → ¬p ∣ N → ∃ e : ℂ, conj e = e ∧ ∀ m : ℕ+,
      c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) : conj (c n / c 1) = c n / c 1 :=
  coeff_of_coprime (c := fun n ↦ c n / c 1) (P := fun x ↦ conj x = x) (Q := fun e ↦ conj e = e)
    (map_zero _) (fun e x y he hx hy ↦ by rw [map_sub, map_mul, he, hx, hy])
    (by rw [div_self hc1, map_one]) (fun p hp hpN ↦ (hrec p hp hpN).imp fun e he ↦ ⟨he.1, fun m ↦ by
      rw [← mul_div_assoc, ← he.2 m, add_div, ite_div, zero_div]⟩) hn

lemma coeff_eq_zero_of_coprime (hc1 : c 1 = 0)
    (hrec : ∀ p : ℕ, p.Prime → ¬p ∣ N → ∃ e : ℂ, ∀ m : ℕ+,
      c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) : c n = 0 :=
  coeff_of_coprime (P := (· = 0)) (Q := fun _ ↦ True) rfl
    (fun e x y _ hx hy ↦ by rw [hx, hy, mul_zero, sub_zero]) hc1
    (fun p hp hpN ↦ (hrec p hp hpN).imp fun _ he ↦ ⟨trivial, he⟩) hn

variable [NeZero N]

lemma IsMaassNewform.exists_maassHeckeOperator_eq (hF : IsMaassNewform N 1 eigenvalue F)
    (hp : p.Prime) (hpN : ¬p ∣ N) : ∃ heckeEigenvalue : ℂ, conj heckeEigenvalue = heckeEigenvalue ∧
      ∀ z : ℂ, 0 < z.im →
        maassHeckeOperator p (F ∘ ofComplex) z = heckeEigenvalue * (F ∘ ofComplex) z := by
  rcases hF.2.2 p hp hpN with ⟨e, he⟩
  rw [maassHeckeOperatorChar_one (hp.coprime_iff_not_dvd.mpr hpN)] at he
  refine ⟨e, hF.conj_heckeEigenvalue hp hpN he, fun z hz ↦ ?_⟩
  rw [Function.comp_apply, ofComplex_apply_of_im_pos hz]
  exact he ⟨z, hz⟩

/-- **The normalised coefficients of an even Maass newform are real** at the indices prime to the
level (LMFDB `mf.maass.mwf.coefficients`): for an even Maass newform `F` of weight `0` on `Γ₀(N)`
with trivial character and the cosine expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) cos(2πnx)`
with `a(1) ≠ 0`, the coefficient `a(n) / a(1)` of the newform normalised by `a(1) = 1` is real for
every `n` prime to `N`. -/
lemma IsMaassNewform.conj_coeff_div_of_hasMaassCosineExpansion
    (hF : IsMaassNewform N 1 eigenvalue F) (hc : HasMaassCosineExpansion (F ∘ ofComplex) r c)
    (hc1 : c 1 ≠ 0) {n : ℕ+} (hn : (n : ℕ).Coprime N) : conj (c n / c 1) = c n / c 1 :=
  conj_coeff_div_of_coprime hc1 (fun _ hp hpN ↦
    (hF.exists_maassHeckeOperator_eq hp hpN).imp fun _ he ↦ ⟨he.1, hc.coeff_mul_add_eq hp he.2⟩)
    hn

/-- **The normalised coefficients of an odd Maass newform are real** at the indices prime to the
level (LMFDB `mf.maass.mwf.coefficients`): for an odd Maass newform `F` of weight `0` on `Γ₀(N)`
with trivial character and the sine expansion `F(x + iy) = ∑ a(n) √y K_{iR}(2πny) sin(2πnx)` with
`a(1) ≠ 0`, the coefficient `a(n) / a(1)` of the newform normalised by `a(1) = 1` is real for
every `n` prime to `N`. -/
lemma IsMaassNewform.conj_coeff_div_of_hasMaassSineExpansion (hF : IsMaassNewform N 1 eigenvalue F)
    (hc : HasMaassSineExpansion (F ∘ ofComplex) r c) (hc1 : c 1 ≠ 0) {n : ℕ+}
    (hn : (n : ℕ).Coprime N) : conj (c n / c 1) = c n / c 1 :=
  conj_coeff_div_of_coprime hc1 (fun _ hp hpN ↦
    (hF.exists_maassHeckeOperator_eq hp hpN).imp fun _ he ↦ ⟨he.1, hc.coeff_mul_add_eq hp he.2⟩)
    hn

/-- **A Maass newform of level `1` with a cosine expansion has `a(1) ≠ 0`**: otherwise the Hecke
relations give `a(n) = 0` for every `n`, and the expansion gives `F = 0`. -/
lemma IsMaassNewform.coeff_one_ne_zero_of_hasMaassCosineExpansion
    (hF : IsMaassNewform 1 1 eigenvalue F) (hc : HasMaassCosineExpansion (F ∘ ofComplex) r c) :
    c 1 ≠ 0 := by
  intro hc1
  have hc0 (n : ℕ+) : c n = 0 := coeff_eq_zero_of_coprime hc1 (fun _ hp hpN ↦
    (hF.exists_maassHeckeOperator_eq hp hpN).imp fun _ he ↦ hc.coeff_mul_add_eq hp he.2)
    (Nat.coprime_one_right _)
  refine hF.2.1 (funext fun τ ↦ ?_)
  have h : (F ∘ ofComplex) τ = 0 := (hc τ).unique (by simp [hc0])
  simpa using h

/-- **A Maass newform of level `1` with a sine expansion has `a(1) ≠ 0`**: otherwise the Hecke
relations give `a(n) = 0` for every `n`, and the expansion gives `F = 0`. -/
lemma IsMaassNewform.coeff_one_ne_zero_of_hasMaassSineExpansion
    (hF : IsMaassNewform 1 1 eigenvalue F) (hc : HasMaassSineExpansion (F ∘ ofComplex) r c) :
    c 1 ≠ 0 := by
  intro hc1
  have hc0 (n : ℕ+) : c n = 0 := coeff_eq_zero_of_coprime hc1 (fun _ hp hpN ↦
    (hF.exists_maassHeckeOperator_eq hp hpN).imp fun _ he ↦ hc.coeff_mul_add_eq hp he.2)
    (Nat.coprime_one_right _)
  refine hF.2.1 (funext fun τ ↦ ?_)
  have h : (F ∘ ofComplex) τ = 0 := (hc τ).unique (by simp [hc0])
  simpa using h

end UpperHalfPlane
