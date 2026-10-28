import LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Deligne modules

A Deligne module for the isogeny class of abelian varieties over `𝔽_q` with Weil polynomial `h` is a
finitely generated free `ℤ`-module `M` with an endomorphism `F` of characteristic polynomial `h`
that induces an action of the Frobenius order `ℤ[F, V]` on `M`. By Deligne, the category of
ordinary abelian varieties over `𝔽_q` is equivalent to a category of Deligne modules, and by
Centeleghe–Stix the same holds for the abelian varieties over `𝔽_p` whose Weil polynomials have no
real roots; when `h` is squarefree, a Deligne module is a fractional `ℤ[F, V]`-ideal of the étale
algebra `ℚ[F]`. None of these theorems is formalised here. As in
`LeanBridge.ForMathlib.NumberTheory.NumberField.WeilPolynomial.FrobeniusOrder`, the Frobenius order
is built from a Weil `q`-polynomial `h`.

## Main definitions

* `Module.End.IsDeligneModule` (LMFDB `av.deligne_module`): `(M, F)` is a Deligne module for `h`.

## Main results

* `Module.End.IsDeligneModule.exists_mul_eq_natCast`: the endomorphism `F` of a Deligne module has
  an endomorphism `V` with `F V = V F = q`.
-/

open Polynomial

namespace Module.End

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {q : ℕ} {h : ℤ[X]}
  {F : Module.End ℤ M}

variable (q h F) in
/-- A finitely generated free `ℤ`-module `M` with an endomorphism `F` is a **Deligne module**
(LMFDB `av.deligne_module`) for the isogeny class of abelian varieties over `𝔽_q` with Weil
polynomial `h` if `F` has characteristic polynomial `h` and induces an action of the Frobenius
order `ℤ[F, V]` of `h`: a ring homomorphism from `ℤ[F, V]` to the endomorphisms of `M` sending the
Frobenius to `F`. Such an action makes `F` semisimple over `ℚ`, as the Frobenius of an abelian
variety is, since the radical of `h` vanishes at the Frobenius of `ℤ[F, V]`. The LMFDB's `h` is the
Weil polynomial of an isogeny class; here it is any Weil `q`-polynomial (which of them come from
isogeny classes is Honda–Tate theory). -/
structure IsDeligneModule : Prop where
  /-- The polynomial `h` is a Weil `q`-polynomial. -/
  isWeilPolynomial : h.IsWeilPolynomial q
  /-- The characteristic polynomial of `F` is `h`. -/
  charpoly_eq : F.charpoly = h
  /-- The endomorphism `F` induces an action of the Frobenius order `ℤ[F, V]`. -/
  exists_algHom : ∃ ρ : h.frobeniusOrder q →ₐ[ℤ] Module.End ℤ M,
    ρ ⟨EtaleAlgebra.frobenius h, h.frobenius_mem_frobeniusOrder q⟩ = F

/-- The endomorphism `F` of a Deligne module for a Weil `q`-polynomial has an endomorphism `V` with
`F V = V F = q`, the action of the Verschiebung. -/
lemma IsDeligneModule.exists_mul_eq_natCast (hF : F.IsDeligneModule q h) :
    ∃ V : Module.End ℤ M, F * V = q ∧ V * F = q := by
  rcases hF.exists_algHom with ⟨ρ, hρ⟩
  let V : h.frobeniusOrder q :=
    ⟨EtaleAlgebra.verschiebung q h, h.verschiebung_mem_frobeniusOrder q⟩
  have hFV : ⟨EtaleAlgebra.frobenius h, h.frobenius_mem_frobeniusOrder q⟩ * V = q :=
    Subtype.ext hF.isWeilPolynomial.frobenius_mul_verschiebung
  refine ⟨ρ V, ?_, ?_⟩
  · rw [← hρ, ← map_mul, hFV, map_natCast]
  · rw [← hρ, ← map_mul, mul_comm, hFV, map_natCast]

end Module.End
