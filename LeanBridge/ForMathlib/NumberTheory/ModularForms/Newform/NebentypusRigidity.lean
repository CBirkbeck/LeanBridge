import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.CuspForm
import LeanBridge.ForMathlib.NumberTheory.ModularForms.RankinSelberg.SquareFactor
import TauCeti.NumberTheory.ModularForms.Newforms.Satake
import TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# Nebentypus rigidity for newforms

Two newforms `f`, `g` of the same weight and of any levels, whose coefficients `a_p` agree at all
but finitely many primes `p`, have the same nebentypus: `χ_f` and `χ_g` induce the same character
at every common level. This is the part of strong multiplicity one across levels (Miyake, *Modular
Forms*, Theorem 4.6.19) that is not about the level. Agreement of `a_n` at all `n` prime to a fixed
integer gives it at once, from `a_{p ^ 2} = a_p ^ 2 - χ(p) p ^ (k - 1)`, but agreement at primes
alone says nothing on `a_{p ^ 2}`.

The proof is by a weak form of the Rankin–Selberg method, with no Euler product and no statement
on an `L`-function at `s = 1`. Let `P` be a multiple of the levels containing the exceptional
primes, and let `F`, `G` be the parts of `f`, `g` with coefficients prime to `P`.

1. A good prime `q` satisfies `a_q = χ(q) conj(a_q)`. So `a_q(f) = a_q(g)` with `χ_f(q) ≠ χ_g(q)`
   forces `a_q(f) = 0`, and the Hecke recursion then gives `a_{q ^ (2 j + 1)}(f) = 0` and
   `|a_{q ^ (2 j)}(f)| = q ^ (j (k - 1))`.
2. So every `n` prime to `P` with `a_n(f) ≠ 0` is uniquely `m t ^ 2`, where the prime factors of `m`
   have `χ_f(q) = χ_g(q)` and those of `t` have `χ_f(q) ≠ χ_g(q)`. Then `a_{m t ^ 2}(g) = a_m(f)` on
   the first factor, and on the second the value of `a_{t ^ 2}(f) conj(a_{t ^ 2}(g))` is
   `χ_f(t) conj(χ_g(t)) t ^ (2 (k - 1))`.
3. So the Rankin–Selberg series of `F` against `F` and of `F` against `G` are the same series over
   `m` times Dirichlet series in `t ^ (-2σ)`, the first at most `ζ(2)`, the second at least
   `2 - ζ(2) > 0` in absolute value.
4. If the characters differed, the series of `F` against `G` would have no pole at `σ = 1` by
   `RankinSelberg.tendsto_sub_one_mul_integral_stripFun_petersson`, while that of `F` against `F`
   has one by `RankinSelberg.exists_le_sub_one_mul_re_integral_stripFun_petersson`.

## Main results

* `HeckeRing.GL2.Newform.comp_unitsMap_eq_of_eventually_coeff_eq`: nebentypus rigidity.
-/

open UpperHalfPlane RankinSelberg CongruenceSubgroup Matrix SpecialLinearGroup TauCeti

open scoped ComplexConjugate Real

namespace HeckeRing.GL2.Newform

variable {N N' P : ℕ} [NeZero N] [NeZero N'] {k : ℤ} (f : Newform N k) (g : Newform N' k)
    {p m n t : ℕ} {σ : ℝ}

variable (n) in
/-- The `n`-th coefficient of the `q`-expansion of a newform. -/
private noncomputable abbrev coeff : ℂ :=
  (qExpansion 1 f.toCuspForm).coeff n

private lemma coeff_mul (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) (hmN : m.Coprime N)
    (hnN : n.Coprime N) : coeff f (m * n) = coeff f m * coeff f n :=
  f.toEigenformAwayFromLevel.qExpansion_coeff_mul f.isNorm (m := ⟨m, Nat.pos_of_ne_zero hm⟩)
    (n := ⟨n, Nat.pos_of_ne_zero hn⟩) hmn hmN hnN

private lemma coeff_prime_pow_add_two (hp : p.Prime) (hpN : p.Coprime N) (r : ℕ) :
    coeff f (p ^ (r + 2)) = coeff f p * coeff f (p ^ (r + 1)) -
      f.dirichletLift p * (p : ℂ) ^ (k - 1) * coeff f (p ^ r) := by
  rw [f.dirichletLift_apply_of_coprime hpN]
  exact f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm (p := ⟨p, hp.pos⟩)
    hp hpN r

private lemma coeff_prime_pow_odd (hp : p.Prime) (hpN : p.Coprime N) (h0 : coeff f p = 0) (j : ℕ) :
    coeff f (p ^ (2 * j + 1)) = 0 := by
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [mul_add_one, add_right_comm, coeff_prime_pow_add_two f hp hpN, ih, h0]
    ring1

private lemma coeff_prime_pow_even (hp : p.Prime) (hpN : p.Coprime N) (h0 : coeff f p = 0) (j : ℕ) :
    coeff f (p ^ (2 * j)) = (-(f.dirichletLift p * (p : ℂ) ^ (k - 1))) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [mul_add_one, coeff_prime_pow_add_two f hp hpN, ih, h0, pow_succ]
    ring1

private lemma norm_coeff_prime_pow_even (hp : p.Prime) (hpN : p.Coprime N) (h0 : coeff f p = 0)
    (j : ℕ) : ‖coeff f (p ^ (2 * j))‖ = ((p : ℝ) ^ (k - 1)) ^ j := by
  rw [coeff_prime_pow_even f hp hpN h0, norm_pow, norm_neg, norm_mul,
    f.dirichletLift_apply_of_coprime hpN, norm_coe_char, one_mul, norm_zpow, Complex.norm_natCast]

private lemma coeff_prime_pow_congr (hp : p.Prime) (hpN : p.Coprime N) (hpN' : p.Coprime N')
    (ha : coeff g p = coeff f p) (hχ : g.dirichletLift p = f.dirichletLift p) (r : ℕ) :
    coeff g (p ^ r) = coeff f (p ^ r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using ha
  | more r ih₀ ih₁ =>
    rw [coeff_prime_pow_add_two f hp hpN, coeff_prime_pow_add_two g hp hpN', ih₀, ih₁, ha, hχ]

private lemma coeff_eq_zero_of_dirichletLift_ne (hp : p.Prime) (hpN : p.Coprime N)
    (hpN' : p.Coprime N') (hgf : coeff g p = coeff f p)
    (hne : f.dirichletLift p ≠ g.dirichletLift p) : coeff f p = 0 := by
  by_contra ha
  have hg₁ : coeff g p = g.dirichletLift p * conj (coeff g p) :=
    g.qExpansion_coeff_eq_dirichletLift_mul_conj hp hpN'
  rw [hgf] at hg₁
  have hconj : conj (coeff f p) ≠ 0 := (map_ne_zero _).mpr ha
  exact hne <| mul_right_cancel₀ hconj <|
    (f.qExpansion_coeff_eq_dirichletLift_mul_conj hp hpN).symm.trans hg₁

variable (P) in
/-- The positive integers whose prime factors `q` are prime to `P` with `χ_f(q) = χ_g(q)`. -/
private def splitSet : Set ℕ :=
  {m | m ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ m → q.Coprime P ∧ f.dirichletLift q = g.dirichletLift q}

variable (P) in
/-- The positive integers whose prime factors `q` are prime to `P` with `χ_f(q) ≠ χ_g(q)`. -/
private def inertSet : Set ℕ :=
  {t | t ≠ 0 ∧ ∀ q : ℕ, q.Prime → q ∣ t → q.Coprime P ∧ f.dirichletLift q ≠ g.dirichletLift q}

private lemma one_mem_splitSet : 1 ∈ splitSet P f g :=
  ⟨one_ne_zero, fun _ hq hq1 ↦ absurd (Nat.dvd_one.mp hq1) hq.ne_one⟩

private lemma one_mem_inertSet : 1 ∈ inertSet P f g :=
  ⟨one_ne_zero, fun _ hq hq1 ↦ absurd (Nat.dvd_one.mp hq1) hq.ne_one⟩

variable {f g}

private lemma coprime_of_mem_splitSet (hm : m ∈ splitSet P f g) : m.Coprime P :=
  Nat.coprime_of_dvd fun q hq hqm hqP ↦
    hq.ne_one (Nat.eq_one_of_dvd_coprimes (hm.2 q hq hqm).1 dvd_rfl hqP)

private lemma coprime_of_mem_inertSet (ht : t ∈ inertSet P f g) : t.Coprime P :=
  Nat.coprime_of_dvd fun q hq hqt hqP ↦
    hq.ne_one (Nat.eq_one_of_dvd_coprimes (ht.2 q hq hqt).1 dvd_rfl hqP)

private lemma coprime_of_mem_of_mem (hm : m ∈ splitSet P f g) (ht : t ∈ inertSet P f g) :
    m.Coprime t :=
  Nat.coprime_of_dvd fun q hq hqm hqt ↦ (ht.2 q hq hqt).2 (hm.2 q hq hqm).2

private lemma injective_mul_sq :
    Function.Injective fun z : (splitSet P f g) × (inertSet P f g) ↦ (z.1 : ℕ) * (z.2 : ℕ) ^ 2 := by
  rintro ⟨⟨m, hm⟩, ⟨t, ht⟩⟩ ⟨⟨m', hm'⟩, ⟨t', ht'⟩⟩ h
  have h' : m * t ^ 2 = m' * t' ^ 2 := h
  have h₁ : m ∣ m' := ((coprime_of_mem_of_mem hm ht').pow_right 2).dvd_of_dvd_mul_right
    (h' ▸ dvd_mul_right m (t ^ 2))
  have h₂ : m' ∣ m := ((coprime_of_mem_of_mem hm' ht).pow_right 2).dvd_of_dvd_mul_right
    (h'.symm ▸ dvd_mul_right m' (t' ^ 2))
  have hmm : m = m' := Nat.dvd_antisymm h₁ h₂
  subst hmm
  have htt : t = t' := Nat.pow_left_injective (by norm_num)
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm.1) h')
  subst htt
  rfl

private lemma coeff_eq_of_mem_splitSet (hNP : N ∣ P) (hN'P : N' ∣ P)
    (hgf : ∀ q : ℕ, q.Prime → q.Coprime P → coeff g q = coeff f q) (hm : m ∈ splitSet P f g) :
    coeff g m = coeff f m := by
  induction m using Nat.recOnPrimePow with
  | zero => exact absurd rfl hm.1
  | one => simp
  | prime_pow_mul b q r hq hqb hr ih =>
    have hb0 : b ≠ 0 := fun h ↦ hqb (h ▸ dvd_zero q)
    have hb : b ∈ splitSet P f g :=
      ⟨hb0, fun q' hq' hqb' ↦ hm.2 q' hq' (dvd_mul_of_dvd_right hqb' _)⟩
    rcases hm.2 q hq (dvd_mul_of_dvd_left (dvd_pow_self q hr.ne') _) with ⟨hqP, hχ⟩
    have hqb' : q.Coprime b := hq.coprime_iff_not_dvd.mpr hqb
    have hbP : b.Coprime P := coprime_of_mem_splitSet hb
    have hq0 : q ^ r ≠ 0 := pow_ne_zero _ hq.ne_zero
    rw [coeff_mul f hq0 hb0 (hqb'.pow_left r) ((hqP.coprime_dvd_right hNP).pow_left r)
      (hbP.coprime_dvd_right hNP), coeff_mul g hq0 hb0 (hqb'.pow_left r)
      ((hqP.coprime_dvd_right hN'P).pow_left r) (hbP.coprime_dvd_right hN'P), ih hb,
      coeff_prime_pow_congr f g hq (hqP.coprime_dvd_right hNP) (hqP.coprime_dvd_right hN'P)
        (hgf q hq hqP) hχ.symm r]

private lemma norm_coeff_sq (hNP : N ∣ P)
    (hvan : ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0)
    (ht : t ∈ inertSet P f g) : ‖coeff f (t ^ 2)‖ = (t : ℝ) ^ (k - 1) := by
  induction t using Nat.recOnPrimePow with
  | zero => exact absurd rfl ht.1
  | one => simp
  | prime_pow_mul b q r hq hqb hr ih =>
    have hb0 : b ≠ 0 := fun h ↦ hqb (h ▸ dvd_zero q)
    have hb : b ∈ inertSet P f g :=
      ⟨hb0, fun q' hq' hqb' ↦ ht.2 q' hq' (dvd_mul_of_dvd_right hqb' _)⟩
    rcases ht.2 q hq (dvd_mul_of_dvd_left (dvd_pow_self q hr.ne') _) with ⟨hqP, hχ⟩
    have hqN : q.Coprime N := hqP.coprime_dvd_right hNP
    have hbN : b.Coprime N := (coprime_of_mem_inertSet hb).coprime_dvd_right hNP
    have hqb' : q.Coprime b := hq.coprime_iff_not_dvd.mpr hqb
    rw [mul_pow, ← pow_mul, mul_comm r 2, coeff_mul f (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hb0)
        ((hqb'.pow_left _).pow_right _) (hqN.pow_left _) (hbN.pow_left _), norm_mul,
      norm_coeff_prime_pow_even f hq hqN (hvan q hq hqP hχ), ih hb]
    push_cast
    rw [mul_zpow, ← zpow_natCast (q : ℝ) r, ← zpow_natCast _ r, zpow_comm]

private lemma coeff_sq_mul_conj (hNP : N ∣ P) (hN'P : N' ∣ P)
    (hvan : ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0)
    (hgf : ∀ q : ℕ, q.Prime → q.Coprime P → coeff g q = coeff f q) (ht : t ∈ inertSet P f g) :
    coeff f (t ^ 2) * conj (coeff g (t ^ 2)) =
      f.dirichletLift t * conj (g.dirichletLift t) * (((t : ℝ) ^ (k - 1)) ^ 2 : ℝ) := by
  induction t using Nat.recOnPrimePow with
  | zero => exact absurd rfl ht.1
  | one => simp
  | prime_pow_mul b q r hq hqb hr ih =>
    have hb0 : b ≠ 0 := fun h ↦ hqb (h ▸ dvd_zero q)
    have hb : b ∈ inertSet P f g :=
      ⟨hb0, fun q' hq' hqb' ↦ ht.2 q' hq' (dvd_mul_of_dvd_right hqb' _)⟩
    rcases ht.2 q hq (dvd_mul_of_dvd_left (dvd_pow_self q hr.ne') _) with ⟨hqP, hχ⟩
    have hqN : q.Coprime N := hqP.coprime_dvd_right hNP
    have hqN' : q.Coprime N' := hqP.coprime_dvd_right hN'P
    have hbP : b.Coprime P := coprime_of_mem_inertSet hb
    have hqb' : q.Coprime b := hq.coprime_iff_not_dvd.mpr hqb
    have h0 : coeff f q = 0 := hvan q hq hqP hχ
    have h0' : coeff g q = 0 := (hgf q hq hqP).trans h0
    rw [mul_pow, ← pow_mul, mul_comm r 2, coeff_mul f (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hb0)
        ((hqb'.pow_left _).pow_right _) (hqN.pow_left _) ((hbP.coprime_dvd_right hNP).pow_left _),
      coeff_mul g (pow_ne_zero _ hq.ne_zero) (pow_ne_zero _ hb0)
        ((hqb'.pow_left _).pow_right _) (hqN'.pow_left _) ((hbP.coprime_dvd_right hN'P).pow_left _),
      map_mul, mul_mul_mul_comm, ih hb, coeff_prime_pow_even f hq hqN h0,
      coeff_prime_pow_even g hq hqN' h0']
    have hQ : conj ((q : ℂ) ^ (k - 1)) = (q : ℂ) ^ (k - 1) := by
      rw [map_zpow₀, Complex.conj_natCast]
    have hval : (-(f.dirichletLift q * (q : ℂ) ^ (k - 1))) ^ r *
        conj ((-(g.dirichletLift q * (q : ℂ) ^ (k - 1))) ^ r) =
        (f.dirichletLift q * conj (g.dirichletLift q)) ^ r * (((q : ℂ) ^ (k - 1)) ^ 2) ^ r := by
      rw [map_pow, map_neg, map_mul, hQ, ← mul_pow, ← mul_pow]
      congr 1
      ring1
    have hlift :
        ∀ {L : ℕ} (χ : DirichletCharacter ℂ L), χ ((q ^ r * b : ℕ) : ZMod L) = χ q ^ r * χ b :=
      fun χ ↦ by rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
    have hpow : ((q : ℂ) ^ r) ^ (k - 1) = ((q : ℂ) ^ (k - 1)) ^ r := by
      rw [← zpow_natCast (q : ℂ) r, ← zpow_natCast _ r, zpow_comm]
    rw [hval, hlift f.dirichletLift, hlift g.dirichletLift, map_mul, map_pow]
    push_cast
    rw [mul_zpow, hpow]
    ring1

private lemma exists_eq_mul_sq (hNP : N ∣ P)
    (hvan : ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0)
    (hn : n ≠ 0) (hnP : n.Coprime P) (ha : coeff f n ≠ 0) :
    ∃ m ∈ splitSet P f g, ∃ t ∈ inertSet P f g, n = m * t ^ 2 := by
  induction n using Nat.recOnPrimePow with
  | zero => exact absurd rfl hn
  | one => exact ⟨1, one_mem_splitSet f g, 1, one_mem_inertSet f g, by norm_num⟩
  | prime_pow_mul b q r hq hqb hr ih =>
    have hb0 : b ≠ 0 := fun h ↦ hqb (h ▸ dvd_zero q)
    have hqP : q.Coprime P := hnP.coprime_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self q hr.ne') _)
    have hbP : b.Coprime P := hnP.coprime_dvd_left (dvd_mul_left b _)
    have hqN : q.Coprime N := hqP.coprime_dvd_right hNP
    have hqb' : q.Coprime b := hq.coprime_iff_not_dvd.mpr hqb
    rw [coeff_mul f (pow_ne_zero _ hq.ne_zero) hb0 (hqb'.pow_left _) (hqN.pow_left _)
      (hbP.coprime_dvd_right hNP)] at ha
    rcases ih hb0 hbP (right_ne_zero_of_mul ha) with ⟨m, hm, t, ht, rfl⟩
    have hmem : ∀ {q' j : ℕ}, q'.Prime → q' ∣ q ^ j → q' = q := fun hq' hqd ↦
      (Nat.prime_dvd_prime_iff_eq hq' hq).mp (hq'.dvd_of_dvd_pow hqd)
    by_cases hχ : f.dirichletLift q = g.dirichletLift q
    · refine ⟨q ^ r * m, ⟨mul_ne_zero (pow_ne_zero _ hq.ne_zero) hm.1, fun q' hq' hqd ↦ ?_⟩, t, ht,
        by ring1⟩
      rcases hq'.dvd_mul.mp hqd with h | h
      · rw [hmem hq' h]
        exact ⟨hqP, hχ⟩
      · exact hm.2 q' hq' h
    · have h0 : coeff f q = 0 := hvan q hq hqP hχ
      rcases Nat.even_or_odd' r with ⟨j, rfl | rfl⟩
      · refine ⟨m, hm, q ^ j * t, ⟨mul_ne_zero (pow_ne_zero _ hq.ne_zero) ht.1,
          fun q' hq' hqd ↦ ?_⟩, by ring1⟩
        rcases hq'.dvd_mul.mp hqd with h | h
        · rw [hmem hq' h]
          exact ⟨hqP, hχ⟩
        · exact ht.2 q' hq' h
      · exact absurd (coeff_prime_pow_odd f hq hqN h0 j) (left_ne_zero_of_mul ha)

private lemma mellinKernel_mul_sq (s : ℝ) (hm : m ≠ 0) (ht : t ≠ 0) :
    mellinKernel s (m * t ^ 2) = mellinKernel s m * (t : ℝ) ^ (-(2 * s)) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)
  have h1 : 1 / (4 * π * ((m * t ^ 2 : ℕ) : ℝ)) = 1 / (4 * π * m) * ((t : ℝ) ^ 2)⁻¹ := by
    push_cast
    field_simp
  have h2 : (((t : ℝ) ^ 2)⁻¹) ^ s = (t : ℝ) ^ (-(2 * s)) := by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_two, ← Real.rpow_mul ht0.le,
      Real.rpow_neg ht0.le]
  rw [mellinKernel, mellinKernel, h1, Real.mul_rpow (by positivity) (by positivity), h2]
  ring1

variable (σ) in
private lemma zpow_sq_mul_rpow (ht : t ≠ 0) :
    ((t : ℝ) ^ (k - 1)) ^ 2 * (t : ℝ) ^ (-(2 * ((k : ℝ) + σ - 1))) = (t : ℝ) ^ (-(2 * σ)) := by
  have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le, ← Real.rpow_add ht0]
  congr 1
  push_cast
  ring1

variable [NeZero P] (hNP : N ∣ P) (hN'P : N' ∣ P)

variable (f) in
/-- The cusp form of level `P²` obtained from a newform `f` of level `N ∣ P` by removing the
coefficients at the indices not prime to `P`: the twist of `f` by the principal character. -/
private noncomputable def coprimeFilter : CuspForm ((Gamma1 (P * P)).map (mapGL ℝ)) k :=
  CuspForm.twist (⇑(1 : DirichletCharacter ℂ P)) (mul_dvd_mul_right hNP P) dvd_rfl f.toCuspForm

variable (f n) in
private lemma coeff_coprimeFilter :
    (qExpansion 1 (f.coprimeFilter hNP)).coeff n = if n.Coprime P then coeff f n else 0 := by
  have h :
      (qExpansion 1 (f.coprimeFilter hNP)).coeff n = (1 : DirichletCharacter ℂ P) n * coeff f n :=
    CuspForm.qExpansion_twist_coeff _ _ _ _ n
  rw [h]
  split_ifs with hn
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n P).mpr hn), one_mul]
  · rw [MulChar.map_nonunit _ fun h ↦ hn ((ZMod.isUnit_iff_coprime n P).mp h), zero_mul]

variable (f) in
private lemma coprimeFilter_mem_cuspFormCharSpace :
    f.coprimeFilter hNP ∈ cuspFormCharSpace k (f.χ.comp (ZMod.unitsMap (hNP.mul_right P))) := by
  have h : f.coprimeFilter hNP ∈ cuspFormCharSpace k (f.χ.comp (ZMod.unitsMap
      (dvd_of_mul_right_dvd (mul_dvd_mul_right hNP P))) *
        (((1 : DirichletCharacter ℂ P).toUnitHom).comp
          (ZMod.unitsMap (dvd_of_mul_left_dvd (dvd_rfl : P * P ∣ P * P)))) ^ 2) :=
    CuspForm.twist_mem_cuspFormCharSpace (1 : DirichletCharacter ℂ P)
      (mul_dvd_mul_right hNP P) dvd_rfl f.mem_charSpace
  have hone : (((1 : DirichletCharacter ℂ P).toUnitHom).comp (ZMod.unitsMap
      (dvd_of_mul_left_dvd (dvd_rfl : P * P ∣ P * P)))) ^ 2 = 1 := by
    ext u
    simp
  have hmul : f.χ.comp (ZMod.unitsMap (dvd_of_mul_right_dvd (mul_dvd_mul_right hNP P))) * 1 =
      f.χ.comp (ZMod.unitsMap (hNP.mul_right P)) :=
    MonoidHom.ext fun u ↦ by rw [MonoidHom.mul_apply, MonoidHom.one_apply, mul_one]
  rwa [hone, hmul] at h

variable (f) in
private lemma coprimeFilter_ne_zero : f.coprimeFilter hNP ≠ 0 := by
  intro h0
  have h1 :
      (qExpansion 1 (f.coprimeFilter hNP)).coeff 1 = if Nat.Coprime 1 P then coeff f 1 else 0 :=
    coeff_coprimeFilter f 1 hNP
  rw [ite_eq_left (Nat.coprime_one_left P), h0] at h1
  simp only [FunLike.coe_zero, qExpansion_zero] at h1
  exact zero_ne_one <| h1.trans f.isNorm

private lemma norm_sq_coeff_coprimeFilter_mul_sq
    (hvan : ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0)
    (hm : m ∈ splitSet P f g) (ht : t ∈ inertSet P f g) :
    ‖(qExpansion 1 (f.coprimeFilter hNP)).coeff (m * t ^ 2)‖ ^ 2 *
        mellinKernel ((k : ℝ) + σ - 1) (m * t ^ 2) =
      ‖(qExpansion 1 (f.coprimeFilter hNP)).coeff m‖ ^ 2 * mellinKernel ((k : ℝ) + σ - 1) m *
        (t : ℝ) ^ (-(2 * σ)) := by
  have hmP : m.Coprime P := coprime_of_mem_splitSet hm
  have htP : t.Coprime P := coprime_of_mem_inertSet ht
  rw [coeff_coprimeFilter, coeff_coprimeFilter, ite_eq_left (hmP.mul_left (htP.pow_left 2)),
    ite_eq_left hmP,
    coeff_mul f hm.1 (pow_ne_zero _ ht.1) ((coprime_of_mem_of_mem hm ht).pow_right 2)
      (hmP.coprime_dvd_right hNP) ((htP.pow_left 2).coprime_dvd_right hNP), norm_mul,
    norm_coeff_sq hNP hvan ht, mellinKernel_mul_sq _ hm.1 ht.1, ← zpow_sq_mul_rpow σ ht.1]
  ring1

private lemma coeff_coprimeFilter_mul_conj_mul_sq
    (hvan : ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0)
    (hgf : ∀ q : ℕ, q.Prime → q.Coprime P → coeff g q = coeff f q) (hm : m ∈ splitSet P f g)
    (ht : t ∈ inertSet P f g) : (qExpansion 1 (f.coprimeFilter hNP)).coeff (m * t ^ 2) *
        conj ((qExpansion 1 (g.coprimeFilter hN'P)).coeff (m * t ^ 2)) *
        (mellinKernel ((k : ℝ) + σ - 1) (m * t ^ 2) : ℂ) =
      ((‖(qExpansion 1 (f.coprimeFilter hNP)).coeff m‖ ^ 2 *
          mellinKernel ((k : ℝ) + σ - 1) m : ℝ) : ℂ) *
        (f.dirichletLift t * conj (g.dirichletLift t) * (((t : ℝ) ^ (-(2 * σ)) : ℝ) : ℂ)) := by
  have hmP : m.Coprime P := coprime_of_mem_splitSet hm
  have htP : t.Coprime P := coprime_of_mem_inertSet ht
  have hmt : (m * t ^ 2).Coprime P := hmP.mul_left (htP.pow_left 2)
  have hsq : ‖coeff f m‖ ^ 2 = coeff f m * conj (coeff f m) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [coeff_coprimeFilter, coeff_coprimeFilter, coeff_coprimeFilter, ite_eq_left hmt,
    ite_eq_left hmt, ite_eq_left hmP,
    coeff_mul f hm.1 (pow_ne_zero _ ht.1) ((coprime_of_mem_of_mem hm ht).pow_right 2)
      (hmP.coprime_dvd_right hNP) ((htP.pow_left 2).coprime_dvd_right hNP),
    coeff_mul g hm.1 (pow_ne_zero _ ht.1) ((coprime_of_mem_of_mem hm ht).pow_right 2)
      (hmP.coprime_dvd_right hN'P) ((htP.pow_left 2).coprime_dvd_right hN'P),
    coeff_eq_of_mem_splitSet hNP hN'P hgf hm, mellinKernel_mul_sq _ hm.1 ht.1,
    ← zpow_sq_mul_rpow σ ht.1, map_mul]
  have hval : coeff f (t ^ 2) * conj (coeff g (t ^ 2)) =
      f.dirichletLift t * conj (g.dirichletLift t) * (((t : ℝ) ^ (k - 1)) ^ 2 : ℝ) :=
    coeff_sq_mul_conj hNP hN'P hvan hgf ht
  push_cast at hval ⊢
  rw [hsq]
  linear_combination (coeff f m * conj (coeff f m) * (mellinKernel ((k : ℝ) + σ - 1) m : ℂ) *
    (((t : ℝ) ^ (-(2 * ((k : ℝ) + σ - 1))) : ℝ) : ℂ)) * hval

private lemma zero_le_weight_of_ne_zero {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hF : F ≠ 0) :
    0 ≤ k := by
  by_contra hk
  have h : CuspForm.toModularFormₗ F = 0 :=
    ModularForm.isZero_of_neg_weight (not_le.mp hk) (CuspForm.toModularFormₗ F)
  exact hF <| CuspForm.toModularFormₗ_injective <| h.trans (map_zero _).symm

private lemma mul_re_integral_le_norm_integral
    (hgf : ∀ q : ℕ, q.Prime → q.Coprime P → coeff g q = coeff f q) (hσ : σ ∈ Set.Ioc (1 : ℝ) 2) :
    (2 - π ^ 2 / 6) / (π ^ 2 / 6) *
        (∫ τ, stripFun (petersson k (f.coprimeFilter hNP) (f.coprimeFilter hNP)) σ τ).re ≤
      ‖∫ τ, stripFun (petersson k (g.coprimeFilter hN'P) (f.coprimeFilter hNP)) σ τ‖ := by
  classical
  have hk : (0 : ℝ) ≤ k := by exact_mod_cast zero_le_weight_of_ne_zero f.ne_zero
  have hs : 0 < (k : ℝ) + σ - 1 := by linarith [hσ.1]
  have hvan :
      ∀ q : ℕ, q.Prime → q.Coprime P → f.dirichletLift q ≠ g.dirichletLift q → coeff f q = 0 :=
    fun q hq hqP hne ↦ coeff_eq_zero_of_dirichletLift_ne f g hq (hqP.coprime_dvd_right hNP)
      (hqP.coprime_dvd_right hN'P) (hgf q hq hqP) hne
  have hx : HasSum (fun n : ℕ ↦ ‖(qExpansion 1 (f.coprimeFilter hNP)).coeff n‖ ^ 2 *
      mellinKernel ((k : ℝ) + σ - 1) n)
      (∫ τ, stripFun (petersson k (f.coprimeFilter hNP) (f.coprimeFilter hNP)) σ τ).re := by
    simpa only [Complex.ofReal_re] using
      Complex.hasSum_re (hasSum_norm_sq_mul_mellinKernel_stripFun (f.coprimeFilter hNP) hσ hs)
  have hzero : ∀ n : ℕ, (∀ m ∈ splitSet P f g, ∀ t ∈ inertSet P f g, n ≠ m * t ^ 2) →
      (qExpansion 1 (f.coprimeFilter hNP)).coeff n = 0 := by
    intro n hn
    rw [coeff_coprimeFilter]
    split_ifs with hnP
    · by_contra ha
      rcases eq_or_ne n 0 with rfl | hn0
      · exact ha (CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos
          (one_mem_strictPeriods_Gamma1_map N))
      · rcases exists_eq_mul_sq hNP hvan hn0 hnP ha with ⟨m, hm, t, ht, rfl⟩
        exact hn m hm t ht rfl
    · rfl
  refine mul_le_norm_of_hasSum_of_hasSum
    (u := fun n ↦ if n ∈ inertSet P f g then f.dirichletLift n * conj (g.dirichletLift n) else 0)
    hσ.1.le (fun n ↦ mul_nonneg (sq_nonneg _) (mellinKernel_nonneg hs n)) injective_mul_sq
    (fun n hn ↦ ?_) (fun n hn ↦ ?_) (fun m hm t ht ↦ ?_) (fun m hm t ht ↦ ?_) (fun n ↦ ?_)
    (fun n hn ↦ ite_eq_right hn) ?_ hx
    (hasSum_coeff_mul_conj_mul_mellinKernel_stripFun _ _ hσ hs)
  · rw [hzero n hn, norm_zero]
    simp
  · rw [hzero n hn, zero_mul, zero_mul]
  · exact norm_sq_coeff_coprimeFilter_mul_sq hNP hvan hm ht
  · rw [ite_eq_left ht]
    exact coeff_coprimeFilter_mul_conj_mul_sq hNP hN'P hvan hgf hm ht
  · split_ifs
    · rw [norm_mul, RCLike.norm_conj]
      exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans
        (DirichletCharacter.norm_le_one _ _)
    · simp
  · simp [one_mem_inertSet f g]

variable (f g) in
/-- **Nebentypus rigidity**: two newforms of the same weight, of any levels `N` and `N'`, whose
coefficients `a_p` agree at all but finitely many primes `p` have nebentypes inducing the same
character at every common level `L`. -/
lemma comp_unitsMap_eq_of_eventually_coeff_eq {L : ℕ} (hNL : N ∣ L) (hN'L : N' ∣ L)
    (h : ∀ᶠ p in Filter.cofinite, p.Prime → (qExpansion 1 g.toCuspForm).coeff p =
      (qExpansion 1 f.toCuspForm).coeff p) :
    f.χ.comp (ZMod.unitsMap hNL) = g.χ.comp (ZMod.unitsMap hN'L) := by
  have hfin : {p : ℕ | ¬(p.Prime → coeff g p = coeff f p)}.Finite := Filter.eventually_cofinite.mp h
  have hS₀ : ∀ q ∈ hfin.toFinset, q ≠ 0 := fun q hq ↦
    (Classical.not_imp.mp (hfin.mem_toFinset.mp hq)).1.ne_zero
  let P : ℕ := N * N' * ∏ q ∈ hfin.toFinset, q
  have hP : NeZero P := ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne N'))
    (Finset.prod_ne_zero_iff.mpr hS₀)⟩
  have hNP : N ∣ P := (dvd_mul_right N N').mul_right _
  have hN'P : N' ∣ P := (dvd_mul_left N' N).mul_right _
  have hgf : ∀ q : ℕ, q.Prime → q.Coprime P → coeff g q = coeff f q := fun q hq hqP ↦ by
    by_contra hne
    exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hqP dvd_rfl (dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun q ↦ q) (hfin.mem_toFinset.mpr fun h' ↦ hne (h' hq))) _))
  have hkey :
      f.χ.comp (ZMod.unitsMap (hNP.mul_right P)) = g.χ.comp (ZMod.unitsMap (hN'P.mul_right P)) :=
    eq_of_forall_mul_re_integral_le_norm_integral
      (div_pos two_sub_pi_sq_div_six_pos (by positivity))
      (coprimeFilter_mem_cuspFormCharSpace f hNP) (coprimeFilter_mem_cuspFormCharSpace g hN'P)
      (coprimeFilter_ne_zero f hNP) fun σ hσ ↦ mul_re_integral_le_norm_integral hNP hN'P hgf hσ
  have hlcm : f.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_left N N')) =
      g.χ.comp (ZMod.unitsMap (Nat.dvd_lcm_right N N')) := by
    refine (MonoidHom.cancel_right
      (ZMod.unitsMap_surjective ((Nat.lcm_dvd hNP hN'P).mul_right P))).mp ?_
    rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, ZMod.unitsMap_comp, ZMod.unitsMap_comp]
    exact hkey
  rw [← ZMod.unitsMap_comp (Nat.dvd_lcm_left N N') (Nat.lcm_dvd hNL hN'L),
    ← ZMod.unitsMap_comp (Nat.dvd_lcm_right N N') (Nat.lcm_dvd hNL hN'L), ← MonoidHom.comp_assoc,
    ← MonoidHom.comp_assoc, hlcm]

end HeckeRing.GL2.Newform
