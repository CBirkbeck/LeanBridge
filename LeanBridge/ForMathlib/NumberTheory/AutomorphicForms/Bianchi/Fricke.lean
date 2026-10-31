import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformOfWeight

/-!
# The Fricke involution and the sign of Bianchi newforms

Let `K` be an imaginary quadratic field, embedded in `ℂ` by `σ`, and `(n)` a nonzero principal
ideal of `𝒪_K`. The **Fricke involution** `W_n` is the matrix `(0, -1; n, 0)` of `GL₂(K)` (LMFDB
`mf.bianchi.sign`). It normalises the level `Γ₀(n)`: `W_n (a, b; c, d) W_n⁻¹ = (d, -c/n; -nb, a)`.
So the slash operator of `W_n` maps Bianchi modular forms of weight `k` and level `Γ₀(n)` to Bianchi
modular forms of the same weight and level, and since `W_n² = -n` acts trivially on `ℋ₃`, it is an
involution of `M_k(Γ₀(n))`, whose eigenvalues are `±1`.

A Bianchi newform `F` of level `(n)` is an eigenform of `W_n`, and its **sign** is minus the
eigenvalue. That every newform is an eigenform of `W_n` is a consequence of multiplicity one for
the newspace, not proved here: the sign is defined for the newforms which are eigenforms of `W_n`,
and is then `±1` and unique. Its equality with the sign of the functional equation of the
L-function of `F`, and the parity of the analytic rank, are theorems, not proved here.

## Main definitions

* `HyperbolicThreeSpace.frickeMatrix` (LMFDB `mf.bianchi.sign`): the matrix `W_n = (0, -1; n, 0)`.
* `HyperbolicThreeSpace.bianchiFricke` (LMFDB `mf.bianchi.sign`): the Fricke involution of
  `M_k(Γ₀(n))`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasSign` (LMFDB `mf.bianchi.sign`): a newform of
  level `(n)` has sign `ε`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.sign` (LMFDB `mf.bianchi.sign`): the sign of a
  newform which is an eigenform of `W_n`.

## Main results

* `HyperbolicThreeSpace.frickeMatrix_mul_mul_inv_mem`: `W_n` normalises `Γ₀(n)`.
* `HyperbolicThreeSpace.bianchiFricke_bianchiFricke`: `W_n` is an involution of `M_k(Γ₀(n))`.
* `HyperbolicThreeSpace.eq_one_or_eq_neg_one_of_bianchiFricke_eq_smul`: its eigenvalues are `±1`.
* `HyperbolicThreeSpace.hasBianchiSign_iff`: on `M_k(Γ₀(n))`, `HasBianchiSign` is the eigenvalue
  condition for `bianchiFricke`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasSign.eq_one_or_eq_neg_one`: the sign of a newform
  is `±1`.
* `HyperbolicThreeSpace.BianchiNewformOfWeight.HasSign.eq`: the sign of a newform is unique.
-/

open Matrix NumberField HilbertModularGroup

open scoped MatrixGroups

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ) (k : ℕ) (n : 𝓞 K) [NeZero n]
  {G : HyperbolicThreeSpace → Fin (k + 1) → ℂ} {c ε ε' : ℂ}

instance : NeZero (Ideal.span {n}) :=
  ⟨fun h ↦ NeZero.ne n (Ideal.span_singleton_eq_bot.mp h)⟩

/-- The **Fricke involution** `W_n = (0, -1; n, 0)` (LMFDB `mf.bianchi.sign`) of a nonzero
`n ∈ 𝒪_K`, as an element of `GL₂(K)`. It normalises the level `Γ₀(n)`
(`frickeMatrix_mul_mul_inv_mem`), and acts on Bianchi modular forms of level `Γ₀(n)` by an
involution (`bianchiFricke`). -/
noncomputable def frickeMatrix : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; (n : K), 0] <| by
    simpa using NeZero.ne n

lemma frickeMatrix_map : ((frickeMatrix n : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ =
    !![0, -1; σ n, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeMatrix]

lemma coe_slRepresentative_frickeMatrix :
    (slRepresentative σ (frickeMatrix n) : Matrix (Fin 2) (Fin 2) ℂ) =
      (σ n ^ (2⁻¹ : ℂ))⁻¹ • !![0, -1; σ n, 0] := by
  simp only [slRepresentative, frickeMatrix_map]
  norm_num

lemma slRepresentative_frickeMatrix_mul_self :
    slRepresentative σ (frickeMatrix n) * slRepresentative σ (frickeMatrix n) = -1 := by
  have hσ : σ n ≠ 0 := (map_ne_zero σ).mpr <| RingOfIntegers.coe_ne_zero_iff.mpr <| NeZero.ne n
  have hs : (σ n ^ (2⁻¹ : ℂ)) ^ 2 = σ n := by simp
  refine Subtype.ext ?_
  rw [SpecialLinearGroup.coe_mul, coe_slRepresentative_frickeMatrix, SpecialLinearGroup.coe_neg,
    SpecialLinearGroup.coe_one]
  generalize σ n ^ (2⁻¹ : ℂ) = r at hs
  rw [← hs] at hσ ⊢
  have hr : r ≠ 0 := fun hr ↦ hσ (by rw [hr, zero_pow two_ne_zero])
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

variable [IsTotallyComplex K]

/-- **The Fricke involution normalises `Γ₀(n)`**: for `x ∈ Γ₀(n)`, `W_n x W_n⁻¹ ∈ Γ₀(n)`, as
`W_n (a, b; c, d) W_n⁻¹ = (d, -c/n; -nb, a)`. -/
lemma frickeMatrix_mul_mul_inv_mem {x : GL (Fin 2) K}
    (hx : x ∈ bianchiGammaZero (Ideal.span {n})) :
    frickeMatrix n * x * (frickeMatrix n)⁻¹ ∈ bianchiGammaZero (Ideal.span {n}) := by
  rcases (mem_bianchiGammaZero_iff x).mp hx with ⟨γ, hγ, rfl⟩
  rcases Ideal.mem_span_singleton'.mp hγ with ⟨c, hc⟩
  have hdet : IsUnit (!![γ.val 1 1, -c; -(n * γ.val 0 1), γ.val 0 0]).det := by
    have h : (!![γ.val 1 1, -c; -(n * γ.val 0 1), γ.val 0 0]).det =
        (GeneralLinearGroup.det γ : 𝓞 K) := by
      rw [GeneralLinearGroup.val_det_apply, det_fin_two_of, det_fin_two, ← hc]
      ring1
    rw [h]
    exact Units.isUnit _
  refine (mem_bianchiGammaZero_iff _).mpr ⟨GeneralLinearGroup.mk'' _ hdet, ?_, ?_⟩
  · exact Ideal.mem_span_singleton'.mpr ⟨-γ.val 0 1, by simp; ring1⟩
  · rw [eq_mul_inv_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [frickeMatrix, mul_apply, ← hc, mul_comm]

lemma bianchiSlash_frickeMatrix_mem
    (hG : G ∈ bianchiSlashInvariants σ k (bianchiGammaZero (Ideal.span {n}))) :
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) G ∈
      bianchiSlashInvariants σ k (bianchiGammaZero (Ideal.span {n})) := by
  intro γ hγ g hg
  rw [← bianchiSlash_mul]
  exact bianchiSlash_eq_of_mul_inv_mem hG (frickeMatrix_mul_mul_inv_mem n hγ)
    (isSLRepresentative_slRepresentative _) ((isSLRepresentative_slRepresentative _).mul hg)

variable {σ k n} in
lemma IsBianchiModularForm.bianchiSlash_frickeMatrix
    (hG : IsBianchiModularForm σ (Ideal.span {n}).gamma0GL k G) :
    IsBianchiModularForm σ (Ideal.span {n}).gamma0GL k
      (bianchiSlash k (slRepresentative σ (frickeMatrix n)) G) where
  analyticAt := analyticAt_extend_bianchiSlash _ hG.analyticAt
  invariant := (isBianchiSlashInvariant_iff_mem _).mpr
    (bianchiSlash_frickeMatrix_mem σ k n hG.mem_bianchiSlashInvariants)
  harmonic := hG.harmonic.bianchiSlash _
  growth := hG.growth.bianchiSlash (isSLRepresentative_slRepresentative _)

/-- The **Fricke involution** `W_n` (LMFDB `mf.bianchi.sign`) of the space `M_k(Γ₀(n))` of Bianchi
modular forms of weight `k` and level `Γ₀(n)`, `n ≠ 0`, over a totally complex `K` (imaginary
quadratic for the LMFDB) embedded in `ℂ` by `σ`: `F ↦ F ∣_k g` for an `SL(2, ℂ)`-representative `g`
of the matrix `(0, -1; n, 0)`, which maps `M_k(Γ₀(n))` to itself as `W_n` normalises `Γ₀(n)`
(`frickeMatrix_mul_mul_inv_mem`). It is an involution (`bianchiFricke_bianchiFricke`), and does not
depend on the representative (`hasBianchiSign_iff`). -/
noncomputable def bianchiFricke :
    Module.End ℂ (bianchiModularForms σ (Ideal.span {n}).gamma0GL k) where
  toFun Φ := ⟨bianchiSlash k (slRepresentative σ (frickeMatrix n)) Φ,
    IsBianchiModularForm.bianchiSlash_frickeMatrix Φ.2⟩
  map_add' _ _ := Subtype.ext <| bianchiSlash_add ..
  map_smul' _ _ := Subtype.ext <| bianchiSlash_smul ..

variable (Φ : bianchiModularForms σ (Ideal.span {n}).gamma0GL k)

lemma coe_bianchiFricke : (bianchiFricke σ k n Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
    bianchiSlash k (slRepresentative σ (frickeMatrix n)) Φ :=
  rfl

/-- **The Fricke involution is an involution** of `M_k(Γ₀(n))`: `W_n² = -n` acts on `ℋ₃` as the
identity, through the representative `-1` of `1 ∈ Γ₀(n)`. -/
lemma bianchiFricke_bianchiFricke : bianchiFricke σ k n (bianchiFricke σ k n Φ) = Φ :=
  Subtype.ext <| by
    rw [coe_bianchiFricke, coe_bianchiFricke, ← bianchiSlash_mul,
      slRepresentative_frickeMatrix_mul_self]
    exact IsBianchiModularForm.invariant Φ.2 1 (one_mem _) (-1) (-1) (by simp)

variable {Φ} in
/-- **The eigenvalues of the Fricke involution are `±1`**: if `W_n Φ = c Φ` for a nonzero `Φ`, then
`c² = 1`. -/
lemma eq_one_or_eq_neg_one_of_bianchiFricke_eq_smul (hΦ : Φ ≠ 0)
    (h : bianchiFricke σ k n Φ = c • Φ) : c = 1 ∨ c = -1 := by
  have h₁ : (c * c) • Φ = (1 : ℂ) • Φ := by
    rw [mul_smul, ← h, ← map_smul, ← h, bianchiFricke_bianchiFricke, one_smul]
  exact mul_self_eq_one_iff.mp <| smul_left_injective ℂ hΦ h₁

/-- **`HasBianchiSign` is the eigenvalue condition of the Fricke involution**: a Bianchi modular
form `Φ` of level `Γ₀(n)` satisfies `Φ ∣_k g = -ε Φ` for every representative `g` of `W_n` exactly
when `W_n Φ = -ε Φ`. -/
lemma hasBianchiSign_iff : HasBianchiSign σ k (F := Φ) n ε ↔ bianchiFricke σ k n Φ = -ε • Φ := by
  refine ⟨fun h ↦ Subtype.ext <| h _ _ <| coe_slRepresentative_frickeMatrix σ n, fun h g s hg ↦ ?_⟩
  have hg' : IsSLRepresentative σ (frickeMatrix n) g := ⟨s, by rw [frickeMatrix_map]; exact hg⟩
  rw [bianchiSlash_eq_of_mul_inv_mem Φ.2.mem_bianchiSlashInvariants
    (by rw [mul_inv_cancel]; exact one_mem _) (isSLRepresentative_slRepresentative _) hg']
  exact congrArg Subtype.val h

variable [NumberField K] [IsPrincipalIdealRing (𝓞 K)]

namespace BianchiNewformOfWeight

variable {σ k n} (F : BianchiNewformOfWeight σ k (Ideal.span {n}))

/-- A Bianchi newform `F` of weight `k` and principal level `(n)` has **sign** `ε` (LMFDB
`mf.bianchi.sign`) if it is an eigenform of the Fricke involution `W_n` (`bianchiFricke`) with
eigenvalue `-ε`. The sign is then `±1` (`HasSign.eq_one_or_eq_neg_one`) and unique (`HasSign.eq`).
That every newform of level `(n)` has a sign, that is, is an eigenform of `W_n`, is a consequence
of multiplicity one, not proved here; the LMFDB states that the sign is the sign of the functional
equation of the L-function of `F`, also not proved here. -/
def HasSign (ε : ℂ) : Prop :=
  bianchiFricke σ k n F.toBianchiModularForm = -ε • F.toBianchiModularForm

lemma hasSign_iff_hasBianchiSign : F.HasSign ε ↔ HasBianchiSign σ k (F := F.toFun) n ε :=
  (hasBianchiSign_iff σ k n F.toBianchiModularForm).symm

variable {F}

lemma toBianchiModularForm_ne_zero (hF : F.toFun ≠ 0) : F.toBianchiModularForm ≠ 0 :=
  fun h ↦ hF <| congrArg Subtype.val h

/-- **The sign of a Bianchi newform is `±1`**, as the eigenvalues of the Fricke involution are
`±1`. -/
lemma HasSign.eq_one_or_eq_neg_one (hF : F.toFun ≠ 0) (h : F.HasSign ε) : ε = 1 ∨ ε = -1 := by
  rcases eq_one_or_eq_neg_one_of_bianchiFricke_eq_smul σ k n (toBianchiModularForm_ne_zero hF) h
    with h₁ | h₁
  · exact Or.inr (neg_eq_iff_eq_neg.mp h₁)
  · exact Or.inl (neg_inj.mp h₁)

/-- **The sign of a Bianchi newform is unique.** -/
lemma HasSign.eq (hF : F.toFun ≠ 0) (h : F.HasSign ε) (h' : F.HasSign ε') : ε = ε' :=
  neg_inj.mp <| smul_left_injective ℂ (toBianchiModularForm_ne_zero hF) <| h.symm.trans h'

variable (hW : ∃ c : ℂ, bianchiFricke σ k n F.toBianchiModularForm = c • F.toBianchiModularForm)

/-- The **sign** (LMFDB `mf.bianchi.sign`) of a Bianchi newform `F` of weight `k` and principal
level `(n)`: minus the eigenvalue of the Fricke involution `W_n` on `F`. It is defined under the
hypothesis `hW` that `F` is an eigenform of `W_n`, which holds for every newform by multiplicity
one for the newspace (a theorem, not proved here); it is then `±1` for `F ≠ 0`. -/
noncomputable def sign : ℂ :=
  -hW.choose

lemma hasSign_sign : F.HasSign (F.sign hW) := by
  rw [HasSign, sign, neg_neg]
  exact hW.choose_spec

end BianchiNewformOfWeight

end HyperbolicThreeSpace
