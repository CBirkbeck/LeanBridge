import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# Herbrand functions and ambiguities of families of extensions of local fields

The LMFDB groups the extensions of a `p`-adic field `K` into families `I / K`, indexed by a
Herbrand invariant `I = (r_1, …, r_w)_ε^f`: the rams `r_1 ≤ ⋯ ≤ r_w`, the tame part `ε` of the
ramification index `ε p ^ w` and the residue degree `f`. The Swan slopes `s_k` of `I` are
determined by the rams, and the Herbrand function and the ambiguity of `I / K` depend only on `I`
and `K`, so we define them on the Herbrand invariant, given as data.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant`: the data `(r_1, …, r_w)_ε^f` of a Herbrand
  invariant.
* `IsNonarchimedeanLocalField.HerbrandInvariant.swanSlope`: its Swan slopes `s_k`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction` (LMFDB `lf.herbrand_function`).
* `IsNonarchimedeanLocalField.HerbrandInvariant.ambiguity` (LMFDB `lf.family_ambiguity`).

## Main theorems

* `IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction_of_mem_Icc`: on `[r_k, r_{k + 1}]`
  the Herbrand function is the segment from `(r_k, s_k)` of slope `1 / (ε p ^ k)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.herbrandFunction_of_le`: on `[r_w, ∞)` it is the ray
  from `(r_w, s_w)` of slope `1 / (ε p ^ w)`.
-/

open ValuativeRel Finset

namespace IsNonarchimedeanLocalField

/-- The data of a **Herbrand invariant** `I = (r_1, …, r_w)_ε^f` at a prime `p` (LMFDB
`lf.herbrand_invariant`): a length `w`, rams `0 < r_1 ≤ ⋯ ≤ r_w`, stored as a monotone sequence
`ram` with `ram 0 = 0` (the LMFDB's convention `r_0 = 0`) and constant from `w` on, and positive
integers `ε` and `f` with `p ∤ ε`. The arithmetic conditions for `I` to be the invariant of an
extension of a given `p`-adic field (compatibility) are not imposed. -/
@[ext]
structure HerbrandInvariant (p : ℕ) where
  /-- The number `w` of rams, i.e. the `p`-adic valuation of the ramification index. -/
  w : ℕ
  /-- The rams `r_0 = 0, r_1, …, r_w`, continued by `r_w`. -/
  ram : ℕ → ℚ
  /-- The tame part `ε` of the ramification index `ε p ^ w`. -/
  ε : ℕ
  /-- The residue degree `f`. -/
  f : ℕ
  ram_zero : ram 0 = 0
  zero_lt_ram_one : 0 < w → 0 < ram 1
  monotone_ram : Monotone ram
  ram_of_le : ∀ k, w ≤ k → ram k = ram w
  ε_pos : 0 < ε
  f_pos : 0 < f
  not_dvd_ε : ¬p ∣ ε

namespace HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p)

/-- The `k`-th **Swan slope** `s_k` of a Herbrand invariant (LMFDB `lf.slopes`), for `k ≤ w`:
`s_0 = 0` and `s_{j + 1} = s_j + (r_{j + 1} - r_j) / (ε p ^ j)`, equivalently
`s_k = (p m_k - m_{k - 1}) / (p - 1)` with `m_k = ∑_{j ≤ k} (p - 1) r_j / (ε p ^ j)`, as in LMFDB
`lf.herbrand_invariant`. -/
def swanSlope (k : ℕ) : ℚ :=
  ∑ j ∈ range k, (I.ram (j + 1) - I.ram j) / (I.ε * p ^ j)

/-- The **Herbrand function** `φ_{I/K}` of a family `I / K` (LMFDB `lf.herbrand_function`): the
piecewise linear function on `[0, ∞)` joining `(0, 0), (r_1, s_1), …, (r_w, s_w)`, followed by the
ray of slope `1 / (ε p ^ w)` from `(r_w, s_w)`. Its segment ending at `(r_k, s_k)` has slope
`1 / (ε p ^ (k - 1))`, so it is `x ↦ ∑_{j < w} (min x r_{j + 1} - min x r_j) / (ε p ^ j) +
max (x - r_w) 0 / (ε p ^ w)`. -/
noncomputable def herbrandFunction (x : ℝ) : ℝ :=
  ∑ j ∈ range I.w, (min x (I.ram (j + 1)) - min x (I.ram j)) / (I.ε * p ^ j) +
    max (x - I.ram I.w) 0 / (I.ε * p ^ I.w)

lemma ram_le_ram {j k : ℕ} (h : j ≤ k) : (I.ram j : ℝ) ≤ I.ram k :=
  Rat.cast_le.mpr <| I.monotone_ram h

/-- On `[r_k, r_{k + 1}]`, for `k < w`, the Herbrand function is the segment from `(r_k, s_k)` of
slope `1 / (ε p ^ k)`. -/
lemma herbrandFunction_of_mem_Icc {k : ℕ} (hk : k < I.w) {x : ℝ}
    (hx : x ∈ Set.Icc (I.ram k : ℝ) (I.ram (k + 1))) :
    I.herbrandFunction x = I.swanSlope k + (x - I.ram k) / (I.ε * p ^ k) := by
  have h₁ : ∑ j ∈ Ico (k + 1) I.w, (min x (I.ram (j + 1)) - min x (I.ram j)) /
      (I.ε * p ^ j : ℝ) = 0 :=
    sum_eq_zero fun j hj ↦ by
      rw [mem_Ico] at hj
      rw [min_eq_left <| hx.2.trans <| I.ram_le_ram hj.1,
        min_eq_left <| hx.2.trans <| I.ram_le_ram <| hj.1.trans j.le_succ, sub_self, zero_div]
  have h₂ : ∑ j ∈ range k, (min x (I.ram (j + 1)) - min x (I.ram j)) / (I.ε * p ^ j : ℝ) =
      ∑ j ∈ range k, ((I.ram (j + 1) : ℝ) - I.ram j) / (I.ε * p ^ j) :=
    sum_congr rfl fun j hj ↦ by
      rw [min_eq_right <| (I.ram_le_ram <| mem_range.mp hj).trans hx.1,
        min_eq_right <| (I.ram_le_ram <| Nat.le_of_lt <| mem_range.mp hj).trans hx.1]
  rw [herbrandFunction, ← sum_range_add_sum_Ico _ hk, sum_range_succ, h₁, h₂,
    max_eq_right <| sub_nonpos.mpr <| hx.2.trans <| I.ram_le_ram hk, min_eq_left hx.2,
    min_eq_right hx.1, swanSlope]
  push_cast
  ring1

/-- On `[r_w, ∞)` the Herbrand function is the ray from `(r_w, s_w)` of slope `1 / (ε p ^ w)`. -/
lemma herbrandFunction_of_le {x : ℝ} (hx : I.ram I.w ≤ x) :
    I.herbrandFunction x = I.swanSlope I.w + (x - I.ram I.w) / (I.ε * p ^ I.w) := by
  rw [herbrandFunction, max_eq_left <| sub_nonneg.mpr hx, swanSlope]
  push_cast
  rw [sum_congr rfl fun j hj ↦ ?_]
  rw [min_eq_right <| (I.ram_le_ram <| mem_range.mp hj).trans hx,
    min_eq_right <| (I.ram_le_ram <| Nat.le_of_lt <| mem_range.mp hj).trans hx]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open Classical in
/-- The **ambiguity** `Amb(I / K)` (LMFDB `lf.family_ambiguity`) of a Herbrand invariant
`I = (r_1, …, r_w)_ε^f` over a nonarchimedean local field `K` of residue characteristic `p`:
`f · gcd(ε, q - 1) · ∏_j gcd(p ^ ρ_j, q)`, where `q = #𝓀[K] ^ f` (which is `p ^ (f₀ f)` for the
residue degree `f₀` of `K / ℚ_p`) and the product runs over the distinct integral rams of `I`,
with multiplicities `ρ_j`. The LMFDB defines it for `I` compatible with `K`. -/
noncomputable def ambiguity : ℕ :=
  I.f * I.ε.gcd (Nat.card 𝓀[K] ^ I.f - 1) *
    ∏ b ∈ ((Icc 1 I.w).image I.ram).filter (fun b : ℚ ↦ b.den = 1),
      (p ^ #{k ∈ Icc 1 I.w | I.ram k = b}).gcd (Nat.card 𝓀[K] ^ I.f)

end HerbrandInvariant

end IsNonarchimedeanLocalField
