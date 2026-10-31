import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolSign
import TauCeti.LinearAlgebra.BilinearForm.Henselian
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.RingTheory.Henselian.Basic

/-!
# The Conway genus symbol at the odd primes determines the localizations

The Conway genus symbol (LMFDB `lattice.conway_genus_symbol`) of a nondegenerate integral lattice,
together with its signature, determines its genus (Conway and Sloane, *Sphere Packings, Lattices
and Groups*, Chapter 15, Theorem 10). This file proves the part of this theorem that concerns the
odd primes: at an odd prime `p`, the ranks `n_q` and signs `ε_q` of the Jordan constituents
determine the localization `L ⊗ ℤ_p` up to isometry. Over `ℤ_p`, `p` odd, unimodular forms of the
same rank whose determinants have the same Legendre symbol are isometric (Tau Ceti's
classification of unimodular forms over Henselian rings, and Hensel's lemma for the square
classes), so the constituents of two Jordan splittings with the same ranks and signs are isometric
one by one, and so are the orthogonal sums.

Consequently two nondegenerate lattices are in the same genus exactly when the formalised part of
their Conway genus symbols (`TauCeti.IntegralLattice.ConwayGenusSymbolSigned`: type, signature,
Jordan ranks, signs at the odd primes and dyadic types) agree and their dyadic localizations are
isometric (`TauCeti.IntegralLattice.sameGenus_iff_conwayGenusSymbolSigned_eq`). What remains of
the theorem is the dyadic part: that the canonical `2`-adic symbol, with its compartment oddities
and train signs, determines the dyadic localization.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.equivalent_of_forall_equivalent`: two forms with Jordan
  splittings whose constituents are isometric one by one are isometric.
* `LinearMap.BilinForm.IsJordanSplitting.equivalent_restrict`: over `ℤ_p`, `p` odd, Jordan
  constituents with the same rank and sign are isometric.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_of_jordanSign_eq`: at an odd prime, the
  Jordan ranks and signs determine the localization of a lattice.
* `TauCeti.IntegralLattice.sameGenus_iff_conwayGenusSymbolSigned_eq`: the formalised part of the
  Conway genus symbol and the dyadic localization determine the genus.
-/

open Module TauCeti

open LinearMap (BilinForm)

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

lemma isSquare_mul_of_quadraticChar_eq (hp : p ≠ 2) {d d' : ℤ_[p]} (hd : IsUnit d) (hd' : IsUnit d')
    (h : quadraticChar (ZMod p) (toZMod d) = quadraticChar (ZMod p) (toZMod d')) :
    IsSquare (d * d') := by
  have h0 : toZMod (d * d') ≠ 0 := ((hd.mul hd').map toZMod).ne_zero
  have hsq : IsSquare (toZMod (d * d')) := by
    rw [← quadraticChar_one_iff_isSquare h0, map_mul, map_mul, h, ← sq,
      quadraticChar_sq_one (hd'.map toZMod).ne_zero]
  rcases hsq with ⟨y, hy⟩
  rcases ZMod.ringHom_surjective toZMod y with ⟨x, rfl⟩
  have hx : IsUnit x := by
    by_contra hx
    have hmem : x ∈ RingHom.ker (toZMod (p := p)) := by
      rw [ker_toZMod]
      exact (IsLocalRing.mem_maximalIdeal x).mpr hx
    rw [RingHom.mem_ker] at hmem
    exact h0 (by rw [hy, hmem, mul_zero])
  rcases HenselianLocalRing.exists_pow_eq_of_residue_pow_eq (n := 2) (u := d * d')
    (by exact_mod_cast isUnit_two hp) hx
    (residueField.injective (by rw [map_pow]; exact (sq _).trans hy.symm)) with ⟨z, hz, -⟩
  exact ⟨z, by rw [← hz, sq]⟩

end PadicInt

namespace LinearMap.BilinForm

variable {p : ℕ} [Fact p.Prime] {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M']
  [Module ℤ_[p] M'] {B : BilinForm ℤ_[p] M} {B' : BilinForm ℤ_[p] M'} {N : ℕ → Submodule ℤ_[p] M}
  {N' : ℕ → Submodule ℤ_[p] M'} {j : ℕ}

/-- **Forms whose Jordan constituents are isometric one by one are isometric.** If `N` and `N'` are
Jordan splittings of `B` and `B'` over `ℤ_p` and the restrictions of `B` to `N j` and of `B'` to
`N' j` are isometric for every `j`, then `B` and `B'` are isometric: the isometries of the
constituents add up, the constituents being orthogonal. -/
lemma IsJordanSplitting.equivalent_of_forall_equivalent (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (h' : B'.IsJordanSplitting (p : ℤ_[p]) N')
    (he : ∀ j, (B.restrict (N j)).Equivalent (B'.restrict (N' j))) : B.Equivalent B' := by
  classical
  let e (j : ℕ) : (B.restrict (N j)).IsometryEquiv (B'.restrict (N' j)) := (he j).some
  let F : (DirectSum ℕ fun j ↦ N j) →ₗ[ℤ_[p]] M' := DirectSum.coeLinearMap N' ∘ₗ
    (DirectSum.congrLinearEquiv fun j ↦ (e j).toLinearEquiv).toLinearMap
  have key : B'.compl₁₂ F F = B.compl₁₂ (DirectSum.coeLinearMap N) (DirectSum.coeLinearMap N) := by
    refine DirectSum.linearMap_ext _ fun i ↦ LinearMap.ext fun a ↦ DirectSum.linearMap_ext _
      fun k ↦ LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply, F, LinearEquiv.coe_coe,
      DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
    by_cases hik : i = k
    · subst hik
      exact (e i).map_app c a
    · rw [h'.apply_eq_zero i k hik _ ((e i).toLinearEquiv a).2 _ ((e k).toLinearEquiv c).2,
        h.apply_eq_zero i k hik _ a.2 _ c.2]
  have hN : Function.Bijective (DirectSum.coeLinearMap N) := h.isInternal
  have hN' : Function.Bijective (DirectSum.coeLinearMap N') := h'.isInternal
  let E : M ≃ₗ[ℤ_[p]] M' := (LinearEquiv.ofBijective _ hN).symm ≪≫ₗ
    DirectSum.congrLinearEquiv (fun j ↦ (e j).toLinearEquiv) ≪≫ₗ LinearEquiv.ofBijective _ hN'
  have hE (x y : M) : B' (E x) (E y) = B x y := by
    rcases (LinearEquiv.ofBijective _ hN).surjective x with ⟨X, rfl⟩
    rcases (LinearEquiv.ofBijective _ hN).surjective y with ⟨Y, rfl⟩
    simpa only [LinearMap.compl₁₂_apply, F, LinearMap.comp_apply, LinearEquiv.coe_coe, E,
      LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply,
      LinearEquiv.ofBijective_symm_apply_apply] using LinearMap.congr_fun₂ key X Y
  exact ⟨⟨E, hE⟩⟩

variable [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M']
  [Module.Finite ℤ_[p] M']

/-- **Over `ℤ_p`, `p` odd, Jordan constituents with the same rank and sign are isometric.** Their
unit forms are unimodular of the same rank, with determinants of the same Legendre symbol, hence
with product a square in `ℤ_p` by Hensel's lemma, and such forms are isometric. -/
lemma IsJordanSplitting.equivalent_restrict (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (h' : B'.IsJordanSplitting (p : ℤ_[p]) N') (hB : B.IsSymm) (hB' : B'.IsSymm) (hp : p ≠ 2)
    (hrank : finrank ℤ_[p] (N j) = finrank ℤ_[p] (N' j)) (hsign : h.sign j = h'.sign j) :
    (B.restrict (N j)).Equivalent (B'.restrict (N' j)) := by
  rw [h.sign_eq_quadraticChar hB (finBasis ℤ_[p] (N j)), h'.sign_eq_quadraticChar hB'
    ((finBasis ℤ_[p] (N' j)).reindex (finCongr hrank.symm))] at hsign
  rcases ((h.isSymm_unitForm hB).equivalent_iff_isSquare_det_mul_det (h'.isSymm_unitForm hB')
    (by exact_mod_cast PadicInt.isUnit_two hp) (finBasis ℤ_[p] (N j))
    ((finBasis ℤ_[p] (N' j)).reindex (finCongr hrank.symm))
    (isUnit_det_toMatrix₂_of_isPerfPair _ (h.isPerfPair_unitForm j))
    (isUnit_det_toMatrix₂_of_isPerfPair _ (h'.isPerfPair_unitForm j))).mpr
    (PadicInt.isSquare_mul_of_quadraticChar_eq hp
      (isUnit_det_toMatrix₂_of_isPerfPair _ (h.isPerfPair_unitForm j))
      (isUnit_det_toMatrix₂_of_isPerfPair _ (h'.isPerfPair_unitForm j)) hsign) with ⟨e⟩
  rw [← h.pow_smul_unitForm, ← h'.pow_smul_unitForm]
  refine ⟨⟨e.toLinearEquiv, fun x y ↦ ?_⟩⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  exact congrArg ((p : ℤ_[p]) ^ j • ·) (e.map_app y x)

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]

variable (L) in
lemma sigNull_eq_zero : L.sigNull = 0 :=
  Nat.eq_zero_of_not_pos fun h ↦ L.isDegenerate_iff_not_nondegenerate.mp
    (L.isDegenerate_iff_sigNull_pos.mpr h) L.form_nondegenerate

/-- **At an odd prime, the Jordan ranks and signs determine the localization**: two nondegenerate
lattices whose Jordan constituents at an odd prime `p` have the same ranks and signs at every scale
have isometric localizations at `p`. -/
lemma localIntegralForm_equivalent_of_jordanSign_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hrank : ∀ k, L.jordanRank p k = M.jordanRank p k)
    (hsign : ∀ k, L.jordanSign p k = M.jordanSign p k) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  (L.exists_isJordanSplitting_localIntegralForm p
    L.form_nondegenerate).choose_spec.equivalent_of_forall_equivalent
    (M.exists_isJordanSplitting_localIntegralForm p M.form_nondegenerate).choose_spec fun k ↦
    (L.exists_isJordanSplitting_localIntegralForm p
      L.form_nondegenerate).choose_spec.equivalent_restrict
    (M.exists_isJordanSplitting_localIntegralForm p M.form_nondegenerate).choose_spec
    (L.isSymm_localIntegralForm p) (M.isSymm_localIntegralForm p) hp (hrank k) (hsign k)

/-- **The formalised part of the Conway genus symbol and the dyadic localization determine the
genus**: two nondegenerate lattices are in the same genus exactly when they have the same type,
signature, Jordan ranks, signs at the odd primes and dyadic types, and isometric localizations at
`2`. -/
lemma sameGenus_iff_conwayGenusSymbolSigned_eq : L.SameGenus M ↔
    L.conwayGenusSymbolSigned = M.conwayGenusSymbolSigned ∧
      (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) := by
  refine ⟨fun h ↦ ⟨h.conwayGenusSymbolSigned_eq, h.localIntegralForm_equivalent 2⟩, ?_⟩
  rintro ⟨hsym, h2⟩
  have hsig : (L.sigPos, L.sigNeg) = (M.sigPos, M.sigNeg) :=
    congrArg (fun s : ConwayGenusSymbolSigned ↦ s.signature) hsym
  refine (sameGenus_iff L M).mpr ⟨?_, fun p hp ↦ ?_⟩
  · rcases Prod.mk_inj.mp hsig with ⟨hpos, hneg⟩
    rw [signature, signature, L.sigNull_eq_zero, M.sigNull_eq_zero, hpos, hneg]
  rcases eq_or_ne p 2 with rfl | hp2
  · exact h2
  · exact localIntegralForm_equivalent_of_jordanSign_eq hp2
      (fun k ↦ congrArg (fun s : ConwayGenusSymbolSigned ↦ s.jordanRank ⟨p, hp.out⟩ k) hsym)
      (fun k ↦ congrArg (fun s : ConwayGenusSymbolSigned ↦ s.jordanSign ⟨p, hp.out⟩ k) hsym)

end TauCeti.IntegralLattice
