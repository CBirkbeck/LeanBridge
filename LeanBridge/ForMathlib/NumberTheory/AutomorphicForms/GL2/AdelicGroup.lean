import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Topology.Instances.Matrix
import TauCeti.NumberTheory.NumberField.Global.Ideles.Basic
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Place

/-!
# The adelic group `GL₂(𝔸_F)`

Let `F` be a number field, `𝔸_F = F_∞ × 𝔸_F^f` its adele ring, where `F_∞ = ∏_v F_v` is the product
of the completions at the infinite places and `𝔸_F^f` the ring of finite adeles. This file sets up
the group `GL₂(𝔸_F)` on which the automorphic forms of `GL(2)` over `F` live, and its two factors
`GL₂(𝔸_F) = GL₂(F_∞) × GL₂(𝔸_F^f)`.

The archimedean factor is taken over the mixed space `E = ℝ^{r₁} × ℂ^{r₂}` of `F`, which Mathlib
identifies with `F_∞` (`InfiniteAdeleRing.ringEquiv_mixedSpace`) and which, unlike `F_∞`, is a
normed real algebra with a star operation. So
`GL₂(F_∞) = GL₂(E) = ∏_{v real} GL₂(ℝ) × ∏_{v complex} GL₂(ℂ)`, on which differential calculus
makes sense.

## Main definitions

* `AdelicGL2`: the group `GL₂(𝔸_F)`.
* `AdelicGL2.split`: the isomorphism `GL₂(𝔸_F) ≃ GL₂(E) × GL₂(𝔸_F^f)`, with its components
  `AdelicGL2.toInf` and `AdelicGL2.toFin`.
* `AdelicGL2.ofInf`, `AdelicGL2.ofFin`: the inclusions of the two factors.
* `AdelicGL2.ofGlobal`: the diagonal inclusion of `GL₂(F)`.
* `AdelicGL2.scalar`: the inclusion of the centre `𝔸_Fˣ`.
* `AdelicGL2.unipotent`: the matrices `(1, x; 0, 1)`, `x ∈ 𝔸_F`.
-/

open IsDedekindDomain Matrix NumberField

open mixedEmbedding (mixedSpace)

open scoped AdeleRing MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {n A R S : Type*} [DecidableEq n] [CommRing A] [CommRing R] [CommRing S]

private lemma fst_one_apply (e : A ≃+* R × S) (i j : n) :
    (e ((1 : Matrix n n A) i j)).1 = (1 : Matrix n n R) i j := by
  rcases eq_or_ne i j with rfl | h <;> simp [*]

private lemma snd_one_apply (e : A ≃+* R × S) (i j : n) :
    (e ((1 : Matrix n n A) i j)).2 = (1 : Matrix n n S) i j := by
  rcases eq_or_ne i j with rfl | h <;> simp [*]

variable [Fintype n]

/-- For a ring isomorphism `A ≃ R × S`, the isomorphism `GL_n(A) ≃ GL_n(R) × GL_n(S)`. -/
def prodEquiv (e : A ≃+* R × S) : GL n A ≃* GL n R × GL n S where
  toFun g := (map ((RingHom.fst R S).comp e) g, map ((RingHom.snd R S).comp e) g)
  invFun p :=
    { val := of fun i j ↦ e.symm (p.1 i j, p.2 i j)
      inv := of fun i j ↦ e.symm ((p.1⁻¹ : GL n R) i j, (p.2⁻¹ : GL n S) i j)
      val_inv := by
        ext i j
        apply e.injective
        have h₁ : ((p.1 : Matrix n n R) * (p.1⁻¹ : GL n R)) i j = (1 : Matrix n n R) i j := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have h₂ : ((p.2 : Matrix n n S) * (p.2⁻¹ : GL n S)) i j = (1 : Matrix n n S) i j := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [mul_apply] at h₁ h₂
        simp only [mul_apply, of_apply, map_sum, map_mul, RingEquiv.apply_symm_apply]
        refine Prod.ext ?_ ?_
        · rw [fst_one_apply]
          simpa [Prod.fst_sum] using! h₁
        · rw [snd_one_apply]
          simpa [Prod.snd_sum] using! h₂
      inv_val := by
        ext i j
        apply e.injective
        have h₁ : (((p.1⁻¹ : GL n R) : Matrix n n R) * p.1) i j = (1 : Matrix n n R) i j := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have h₂ : (((p.2⁻¹ : GL n S) : Matrix n n S) * p.2) i j = (1 : Matrix n n S) i j := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [mul_apply] at h₁ h₂
        simp only [mul_apply, of_apply, map_sum, map_mul, RingEquiv.apply_symm_apply]
        refine Prod.ext ?_ ?_
        · rw [fst_one_apply]
          simpa [Prod.fst_sum] using! h₁
        · rw [snd_one_apply]
          simpa [Prod.snd_sum] using! h₂ }
  left_inv g := by
    ext i j
    simp
  right_inv p := by
    refine Prod.ext ?_ ?_ <;> ext i j <;> simp
  map_mul' g h := by
    simp only [map_mul, Prod.mk_mul_mk]

end Matrix.GeneralLinearGroup

/-- The group **`GL₂(𝔸_F)`** of invertible `2 × 2` matrices over the adele ring of a number field,
with the topology of the units of the matrix ring. -/
abbrev AdelicGL2 (F : Type*) [Field F] [NumberField F] : Type _ :=
  GL (Fin 2) 𝔸[F]

namespace AdelicGL2

open GeneralLinearGroup

variable (F : Type*) [Field F] [NumberField F]

/-- The decomposition `𝔸_F ≃ E × 𝔸_F^f` of the adele ring, where `E = ℝ^{r₁} × ℂ^{r₂}` is the mixed
space of `F`, the product of the completions of `F` at its infinite places. -/
noncomputable def adeleEquiv : 𝔸[F] ≃+* mixedSpace F × 𝔸ᶠ[F] :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).prodCongr (RingEquiv.refl _)

/-- The decomposition **`GL₂(𝔸_F) ≃ GL₂(E) × GL₂(𝔸_F^f)`** into the archimedean and the finite
factor, where `E = ℝ^{r₁} × ℂ^{r₂}` is the mixed space of `F`. -/
noncomputable def split : AdelicGL2 F ≃* GL (Fin 2) (mixedSpace F) × GL (Fin 2) 𝔸ᶠ[F] :=
  prodEquiv (adeleEquiv F)

/-- The archimedean component `GL₂(𝔸_F) → GL₂(E)`. -/
noncomputable def toInf : AdelicGL2 F →* GL (Fin 2) (mixedSpace F) :=
  (MonoidHom.fst _ _).comp (split F).toMonoidHom

/-- The finite component `GL₂(𝔸_F) → GL₂(𝔸_F^f)`. -/
noncomputable def toFin : AdelicGL2 F →* GL (Fin 2) 𝔸ᶠ[F] :=
  (MonoidHom.snd _ _).comp (split F).toMonoidHom

/-- The inclusion `GL₂(E) → GL₂(𝔸_F)` of the archimedean factor. -/
noncomputable def ofInf : GL (Fin 2) (mixedSpace F) →* AdelicGL2 F :=
  (split F).symm.toMonoidHom.comp (MonoidHom.inl _ _)

/-- The inclusion `GL₂(𝔸_F^f) → GL₂(𝔸_F)` of the finite factor. -/
noncomputable def ofFin : GL (Fin 2) 𝔸ᶠ[F] →* AdelicGL2 F :=
  (split F).symm.toMonoidHom.comp (MonoidHom.inr _ _)

/-- The diagonal inclusion `GL₂(F) → GL₂(𝔸_F)`. -/
noncomputable def ofGlobal : GL (Fin 2) F →* AdelicGL2 F :=
  map (algebraMap F 𝔸[F])

/-- The inclusion `𝔸_Fˣ → GL₂(𝔸_F)` of the centre, by scalar matrices. -/
noncomputable def scalar : IdeleGroup (𝓞 F) F →* AdelicGL2 F :=
  GeneralLinearGroup.scalar (Fin 2)

variable {F}

/-- The **unipotent matrix** `(1, x; 0, 1) ∈ GL₂(𝔸_F)`, for an adele `x`. -/
noncomputable def unipotent (x : 𝔸[F]) : AdelicGL2 F :=
  upperRightHom x

variable (x : GL (Fin 2) (mixedSpace F)) (y : GL (Fin 2) 𝔸ᶠ[F]) (g : AdelicGL2 F)

@[simp]
lemma toInf_ofInf : toInf F (ofInf F x) = x := by
  simp [toInf, ofInf]

@[simp]
lemma toFin_ofInf : toFin F (ofInf F x) = 1 := by
  simp [toFin, ofInf]

@[simp]
lemma toInf_ofFin : toInf F (ofFin F y) = 1 := by
  simp [toInf, ofFin]

@[simp]
lemma toFin_ofFin : toFin F (ofFin F y) = y := by
  simp [toFin, ofFin]

variable {g} in
lemma ext_toInf_toFin {g' : AdelicGL2 F} (hi : toInf F g = toInf F g')
    (hf : toFin F g = toFin F g') : g = g' :=
  (split F).injective <| Prod.ext hi hf

lemma ofInf_mul_ofFin : ofInf F (toInf F g) * ofFin F (toFin F g) = g := by
  refine ext_toInf_toFin ?_ ?_ <;> simp

lemma ofFin_mul_ofInf : ofFin F y * ofInf F x = ofInf F x * ofFin F y := by
  refine ext_toInf_toFin ?_ ?_ <;> simp

lemma toInf_apply (i j : Fin 2) :
    (toInf F g : Matrix (Fin 2) (Fin 2) (mixedSpace F)) i j =
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((g : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j).1 :=
  rfl

lemma toFin_apply (i j : Fin 2) :
    (toFin F g : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j = ((g : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j).2 :=
  rfl

variable (γ : GL (Fin 2) F)

lemma toInf_ofGlobal : toInf F (ofGlobal F γ) = map (mixedEmbedding F) γ :=
  GeneralLinearGroup.ext fun _ _ ↦ (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm

lemma toFin_ofGlobal : toFin F (ofGlobal F γ) = map (algebraMap F 𝔸ᶠ[F]) γ :=
  GeneralLinearGroup.ext fun _ _ ↦ rfl

end AdelicGL2
