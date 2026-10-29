import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CoefficientField
import Mathlib.FieldTheory.Galois.Notation

/-!
# Galois conjugates and Galois orbits of Siegel modular forms

An automorphism `σ` of `ℂ` acts on a Siegel modular form `F` with Fourier expansion
`F(τ) = ∑ a(n) e^{2πi tr(nτ)}` through its Fourier coefficients: `σ(F)` is the function with
Fourier coefficients `σ(a(n))`. For a vector-valued form `F : ℋ_g → V`, `σ` acts on the
coordinates of the coefficients `a(n) ∈ V` in a fixed basis of `V`, as for the coefficient field
(`SiegelUpperHalfSpace.vectorCoefficientField`); for `V = ℂ` with its standard basis it acts on the
coefficients themselves. The Hecke eigenforms fall into Galois orbits (LMFDB
`mf.siegel.galois_orbit`), the classes of Galois conjugacy, whose members are conjugate over `ℚ`.

The LMFDB takes `σ ∈ Gal(ℚ̄/ℚ)`; here `σ` is an automorphism of `ℂ`, which is the same for forms
with algebraic Fourier coefficients, such as suitably normalised eigenforms. Fourier expansions on
an arithmetic subgroup `Γ` of `Sp(2g, ℚ)` are unique, as its translation lattice contains the
`N (E_ij + E_ji)` for some `N ≠ 0`, so Galois conjugacy is an equivalence relation on the forms
with a Fourier expansion. That `σ(F)` exists, i.e. that the `σ(a(n))` are the Fourier coefficients
of a Siegel modular form, and that it is a Hecke eigenform when `F` is one, is not proved here.

## Main definitions

* `SiegelUpperHalfSpace.IsGaloisConjugateBy`: `G = σ(F)` (LMFDB `mf.siegel.galois_orbit`).
* `SiegelUpperHalfSpace.IsGaloisConjugate`: Galois conjugacy (LMFDB `mf.siegel.galois_orbit`).
* `SiegelUpperHalfSpace.galoisOrbit` (LMFDB `mf.siegel.galois_orbit`): the Galois orbit of a Hecke
  eigenform.

## Main results

* `SiegelUpperHalfSpace.smul_mem_translationLattice_of_isArithmetic`: the translation lattice of
  an arithmetic subgroup `Γ` contains the `m! (E_ij + E_ji)`, where `m` is the index of
  `Γ ∩ Sp(2g, ℤ)` in `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.isGaloisConjugateBy_singleton_iff`: for scalar-valued forms, `G = σ(F)`
  exactly when the Fourier coefficients of `G` are the `σ(a(n))`.
* `SiegelUpperHalfSpace.IsGaloisConjugateBy.unique`: `σ(F)` is unique.
* `SiegelUpperHalfSpace.IsGaloisConjugateBy.map_vectorCoefficientField`: `σ` maps the coefficient
  field of `F` onto that of `σ(F)`.
* `SiegelUpperHalfSpace.IsGaloisConjugate.trans`: Galois conjugacy is transitive on an arithmetic
  subgroup; it is reflexive on forms with a Fourier expansion and symmetric.
* `SiegelUpperHalfSpace.galoisOrbit_eq_iff`, `SiegelUpperHalfSpace.disjoint_galoisOrbit`: the
  Hecke eigenforms with a Fourier expansion fall into disjoint Galois orbits.
-/

open Matrix Module

namespace SiegelUpperHalfSpace

private lemma transpose_single_add_single {l R : Type*} [DecidableEq l] [Semiring R] (i j : l) :
    (single i j (1 : R) + single j i 1)ᵀ = single i j 1 + single j i 1 := by
  rw [transpose_add, transpose_single, transpose_single, add_comm]

variable {l : Type*} [Fintype l] [DecidableEq l] {Γ : Subgroup (symplecticGroup l ℚ)} (i j : l)
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} [NeZero n]
    (ρ : Representation ℂ (GL (Fin n) ℂ) V) (Γ₀ : Subgroup (symplecticGroup (Fin n) ℚ))
    [Fact (SymplecticGroup.IsArithmetic Γ₀)] {b : Basis ι ℂ V} {σ τ : Gal(ℂ/ℚ)}
    {f g h : SiegelUpperHalfSpace l → V} {a a' : dualLattice Γ → V}

private lemma map_single_add_single :
    (single i j (1 : ℤ) + single j i 1).map (Int.castRingHom ℚ) = single i j 1 + single j i 1 := by
  rw [← RingHom.mapMatrix_apply, map_add, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
    map_single, map_single, map_one]

/-- The translation `(1, s; 0, 1)` of `Sp(2g, ℤ)` by the symmetric matrix `s = E_ij + E_ji`. -/
private def translation : symplecticGroup l ℤ :=
  ⟨fromBlocks 1 (single i j 1 + single j i 1) 0 1, by
    rw [SymplecticGroup.mem_iff', fromBlocks_transpose, transpose_single_add_single]
    simp [J, fromBlocks_multiply]⟩

private lemma coe_map_translation_pow (m : ℕ) :
    (SymplecticGroup.map (Int.castRingHom ℚ) (translation i j) ^ m).val =
      fromBlocks 1 ((m : ℚ) • (single i j 1 + single j i 1)) 0 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Submonoid.coe_mul, ih, SymplecticGroup.coe_map_apply, translation, fromBlocks_map,
      map_single_add_single, fromBlocks_multiply]
    simp [add_smul]
    abel

/-- **The translation lattice of an arithmetic subgroup `Γ` contains `m! (E_ij + E_ji)`** for all
`i, j`, where `m` is the index of `Γ ∩ Sp(2g, ℤ)` in `Sp(2g, ℤ)`: for `s = E_ij + E_ji`, some power
`(1, s; 0, 1)^k` with `0 < k ≤ m` lies in `Γ`, so `(1, m! s; 0, 1)` does. Fourier expansions on `Γ`
are then unique (`SiegelUpperHalfSpace.HasSiegelFourierExpansion.unique`). -/
lemma smul_mem_translationLattice_of_isArithmetic (hΓ : SymplecticGroup.IsArithmetic Γ) :
    ((Γ.relIndex (SymplecticGroup.integral l)).factorial : ℚ) • (single i j 1 + single j i 1) ∈
      translationLattice Γ :=
  ⟨by rw [transpose_smul, transpose_single_add_single], _,
    (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hΓ.1.relIndex_ne_zero
      ⟨translation i j, trivial, rfl⟩ fun _ hm hle ↦ Nat.dvd_factorial hm hle).1,
    coe_map_translation_pow i j _⟩

lemma HasSiegelFourierExpansion.unique_of_isArithmetic (hΓ : SymplecticGroup.IsArithmetic Γ)
    (ha : HasSiegelFourierExpansion Γ f a) (ha' : HasSiegelFourierExpansion Γ f a') : a = a' :=
  ha.unique (Nat.factorial_ne_zero _) (smul_mem_translationLattice_of_isArithmetic · · hΓ) ha'

variable (Γ b σ f g) in
/-- For an automorphism `σ` of `ℂ`, the function `g : ℋ_g → V` is the **Galois conjugate**
`σ(f)` of `f : ℋ_g → V` on `Γ`, relative to a basis `b` of `V` (LMFDB `mf.siegel.galois_orbit`):
`f` and `g` have Fourier expansions `∑ a(n) e^{2πi tr(nτ)}` and `∑ a'(n) e^{2πi tr(nτ)}` on `Γ`
whose coefficients have coordinates `b^*_i(a'(n)) = σ(b^*_i(a(n)))` in `b`. For scalar-valued
forms and the standard basis of `ℂ`, this says `a'(n) = σ(a(n))`
(`SiegelUpperHalfSpace.isGaloisConjugateBy_singleton_iff`). The LMFDB takes `σ ∈ Gal(ℚ̄/ℚ)`, which
is the same for forms with algebraic Fourier coefficients. -/
def IsGaloisConjugateBy : Prop :=
  ∃ a a' : dualLattice Γ → V, HasSiegelFourierExpansion Γ f a ∧ HasSiegelFourierExpansion Γ g a' ∧
    ∀ n i, b.repr (a' n) i = σ (b.repr (a n) i)

/-- **Galois conjugacy of scalar-valued forms** acts on the Fourier coefficients: `G = σ(F)` for
the standard basis of `ℂ` exactly when `F` and `G` have Fourier expansions with coefficients
`a(n)` and `σ(a(n))`. -/
lemma isGaloisConjugateBy_singleton_iff {F G : SiegelUpperHalfSpace l → ℂ} :
    IsGaloisConjugateBy Γ (Basis.singleton Unit ℂ) σ F G ↔ ∃ a a' : dualLattice Γ → ℂ,
      HasSiegelFourierExpansion Γ F a ∧ HasSiegelFourierExpansion Γ G a' ∧ ∀ n, a' n = σ (a n) := by
  simp [IsGaloisConjugateBy]

variable (b) in
lemma isGaloisConjugateBy_one (ha : HasSiegelFourierExpansion Γ f a) :
    IsGaloisConjugateBy Γ b 1 f f :=
  ⟨a, a, ha, ha, fun _ _ ↦ rfl⟩

lemma IsGaloisConjugateBy.symm (hfg : IsGaloisConjugateBy Γ b σ f g) :
    IsGaloisConjugateBy Γ b σ⁻¹ g f := by
  rcases hfg with ⟨a, a', ha, ha', h⟩
  exact ⟨a', a, ha', ha, fun n i ↦ by rw [h, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]⟩

lemma IsGaloisConjugateBy.trans (hΓ : SymplecticGroup.IsArithmetic Γ)
    (hfg : IsGaloisConjugateBy Γ b σ f g) (hgh : IsGaloisConjugateBy Γ b τ g h) :
    IsGaloisConjugateBy Γ b (τ * σ) f h := by
  rcases hfg with ⟨a, a', ha, ha', hfg⟩
  rcases hgh with ⟨c, c', hc, hc', hgh⟩
  refine ⟨a, c', ha, hc', fun n i ↦ ?_⟩
  rw [hgh, ← ha'.unique_of_isArithmetic hΓ hc, hfg, AlgEquiv.mul_apply]

/-- **Uniqueness of `σ(f)`**: on an arithmetic subgroup, at most one function is the Galois
conjugate `σ(f)` of `f`, its Fourier coefficients being determined by those of `f`. -/
lemma IsGaloisConjugateBy.unique {g' : SiegelUpperHalfSpace l → V}
    (hΓ : SymplecticGroup.IsArithmetic Γ) (hfg : IsGaloisConjugateBy Γ b σ f g)
    (hfg' : IsGaloisConjugateBy Γ b σ f g') : g = g' := by
  rcases hfg with ⟨a, a', ha, ha', hfg⟩
  rcases hfg' with ⟨c, c', hc, hc', hfg'⟩
  have hac : a' = c' := funext fun n ↦ b.repr.injective <| Finsupp.ext fun i ↦ by
    rw [hfg, hfg', ha.unique_of_isArithmetic hΓ hc]
  funext x
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, sub_eq_zero]
  exact (ha' x φ).unique (hac ▸ hc' x φ)

/-- **`σ` maps the coefficient field of `f` onto that of `σ(f)`**, on an arithmetic subgroup. -/
lemma IsGaloisConjugateBy.map_vectorCoefficientField (hΓ : SymplecticGroup.IsArithmetic Γ)
    (hfg : IsGaloisConjugateBy Γ b σ f g) :
    (vectorCoefficientField Γ b f).map (σ : ℂ →+* ℂ) = vectorCoefficientField Γ b g := by
  rcases hfg with ⟨a, a', ha, ha', hfg⟩
  have hN : (Γ.relIndex (SymplecticGroup.integral l)).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [vectorCoefficientField, vectorCoefficientField, RingHom.map_field_closure,
    vectorFourierCoeffs_eq_range hN (smul_mem_translationLattice_of_isArithmetic · · hΓ) ha,
    vectorFourierCoeffs_eq_range hN (smul_mem_translationLattice_of_isArithmetic · · hΓ) ha',
    ← Set.range_comp]
  exact congrArg _ <| congrArg _ <| funext fun p ↦ (hfg p.1 p.2).symm

variable (Γ b f g) in
/-- Two functions `f, g : ℋ_g → V` are **Galois conjugate** on `Γ`, relative to a basis `b` of `V`
(LMFDB `mf.siegel.galois_orbit`), if `g = σ(f)` for some automorphism `σ` of `ℂ`. -/
def IsGaloisConjugate : Prop :=
  ∃ σ : Gal(ℂ/ℚ), IsGaloisConjugateBy Γ b σ f g

lemma IsGaloisConjugateBy.isGaloisConjugate (hfg : IsGaloisConjugateBy Γ b σ f g) :
    IsGaloisConjugate Γ b f g :=
  ⟨σ, hfg⟩

variable (b) in
lemma IsGaloisConjugate.refl (ha : HasSiegelFourierExpansion Γ f a) : IsGaloisConjugate Γ b f f :=
  ⟨1, isGaloisConjugateBy_one b ha⟩

lemma IsGaloisConjugate.symm (hfg : IsGaloisConjugate Γ b f g) : IsGaloisConjugate Γ b g f :=
  hfg.elim fun _ hσ ↦ hσ.symm.isGaloisConjugate

/-- **Galois conjugacy is transitive** on an arithmetic subgroup, Fourier expansions being unique
there; it is also symmetric, and reflexive on the functions with a Fourier expansion. -/
lemma IsGaloisConjugate.trans (hΓ : SymplecticGroup.IsArithmetic Γ)
    (hfg : IsGaloisConjugate Γ b f g) (hgh : IsGaloisConjugate Γ b g h) :
    IsGaloisConjugate Γ b f h :=
  hfg.elim fun _ hσ ↦ hgh.elim fun _ hτ ↦ (hσ.trans hΓ hτ).isGaloisConjugate

variable (b) {F G : slashInvariantsOf ρ (heckeMonoidOf Γ₀) (heckeGammaOf Γ₀)}
    {a₀ : dualLattice Γ₀ → V}

variable (F) in
/-- The **Galois orbit** (LMFDB `mf.siegel.galois_orbit`) of a Hecke eigenform `F` of weight `ρ` on
an arithmetic subgroup `Γ₀` of `Sp(2g, ℚ)`, relative to a basis `b` of `V`: the Hecke eigenforms
`G` that are Galois conjugate to `F`, `G = σ(F)` for an automorphism `σ` of `ℂ`. The Hecke
eigenforms with a Fourier expansion fall into disjoint Galois orbits
(`SiegelUpperHalfSpace.galoisOrbit_eq_iff`, `SiegelUpperHalfSpace.disjoint_galoisOrbit`). -/
def galoisOrbit : Set (slashInvariantsOf ρ (heckeMonoidOf Γ₀) (heckeGammaOf Γ₀)) :=
  {G | IsHeckeEigenform ρ G ∧ IsGaloisConjugate Γ₀ b F G}

lemma mem_galoisOrbit :
    G ∈ galoisOrbit ρ Γ₀ b F ↔ IsHeckeEigenform ρ G ∧ IsGaloisConjugate Γ₀ b F G :=
  Iff.rfl

lemma self_mem_galoisOrbit (hF : IsHeckeEigenform ρ F) (ha : HasSiegelFourierExpansion Γ₀ F a₀) :
    F ∈ galoisOrbit ρ Γ₀ b F :=
  ⟨hF, IsGaloisConjugate.refl b ha⟩

/-- **Galois orbits of Galois conjugate eigenforms are equal**: for a Hecke eigenform `G` with a
Fourier expansion, the Galois orbits of `F` and `G` are equal exactly when `F` and `G` are Galois
conjugate. -/
lemma galoisOrbit_eq_iff (hG : IsHeckeEigenform ρ G) (ha : HasSiegelFourierExpansion Γ₀ G a₀) :
    galoisOrbit ρ Γ₀ b F = galoisOrbit ρ Γ₀ b G ↔ IsGaloisConjugate Γ₀ b F G :=
  ⟨fun h ↦ (h.symm ▸ self_mem_galoisOrbit ρ Γ₀ b hG ha).2,
    fun h ↦ Set.ext fun _ ↦ and_congr_right fun _ ↦ ⟨h.symm.trans Fact.out, h.trans Fact.out⟩⟩

/-- **Galois orbits are disjoint**: the Galois orbits of two eigenforms that are not Galois
conjugate are disjoint. -/
lemma disjoint_galoisOrbit (h : ¬IsGaloisConjugate Γ₀ b F G) :
    Disjoint (galoisOrbit ρ Γ₀ b F) (galoisOrbit ρ Γ₀ b G) :=
  Set.disjoint_left.mpr fun _ hF hG ↦ h <| hF.2.trans Fact.out hG.2.symm

end SiegelUpperHalfSpace
