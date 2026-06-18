#!/usr/bin/env sage
"""
Generate a Lean file certifying the q-expansion of a level-1 LMFDB modular form
via the polynomial-in-(E₄, E₆) framework. Supports arbitrary-degree Hecke fields
by decomposing each K-coefficient as a ℚ-polynomial in the algebraic generator α.

Emits:
- Polynomial decomposition (one rational `polyData` per power of α)
- Form definition `lmfdb_1_k_a_orbit := f_0 + α · f_1 + α² · f_2 + …`
- Bridge lemmas connecting each rational piece to its `evalEisPS`
- Coefficient decomposition lemma
- Named per-coefficient lemmas for every i ∈ {0, 1, …, sturm-1}
- Uniqueness theorem `identifies_lmfdb_1_k_a_orbit` via `eq_of_sturm_bound`

Usage:
    sage scripts/lmfdb_qexp_to_e4e6_v3.sage <weight> [<form_index>] [<output_path>]
"""
import sys
import os


def fmt_rat(c):
    n = c.numerator()
    d = c.denominator()
    if d == 1:
        return f"({n})" if n < 0 else f"{n}"
    return f"((-({-n} / {d})))" if n < 0 else f"({n} / {d})"


def fmt_int(z):
    z = int(z)
    return f"({z})" if z < 0 else f"{z}"


MIN_CERTIFY = 10  # certify at least this many q-coefficients (Sturm bound takes precedence if larger)


def newform_decomposition(k, form_idx=0):
    sturm = k // 12 + 1
    n_certify = max(sturm, MIN_CERTIFY)
    M = ModularForms(1, k)
    cusp = M.cuspidal_subspace()
    if cusp.dimension() == 0:
        raise ValueError(f"S_{k} is zero-dimensional")
    forms = cusp.newforms('a')
    f = forms[form_idx]
    K = f.hecke_eigenvalue_field()
    d = K.degree()

    prec = n_certify + 5
    qexp = f.qexp(prec)
    if qexp[1] != 0:
        qexp = qexp / K(qexp[1])

    minpoly = K.gen().minpoly()
    minpoly_coeffs = list(minpoly)

    basis_pairs = [(a, b) for a in range(k // 4 + 1) for b in range(k // 6 + 1)
                   if 4 * a + 6 * b == k]
    n_basis = len(basis_pairs)

    E4 = eisenstein_series_qexp(4, prec, normalization='constant')
    E6 = eisenstein_series_qexp(6, prec, normalization='constant')

    R = PowerSeriesRing(K, 'q', prec)
    E4_K = R(E4)
    E6_K = R(E6)
    basis_qexps = [E4_K ** a * E6_K ** b for (a, b) in basis_pairs]

    A = matrix(K, n_basis, n_basis,
               [[K(basis_qexps[j][i]) for j in range(n_basis)]
                for i in range(n_basis)])
    b_vec = vector(K, [K(qexp[i]) for i in range(n_basis)])
    coeffs = A.solve_right(b_vec)

    poly_per_power = [[] for _ in range(d)]
    for (a, b), c in zip(basis_pairs, coeffs):
        c_parts = c.list()
        while len(c_parts) < d:
            c_parts.append(QQ(0))
        for j in range(d):
            if c_parts[j] != 0:
                poly_per_power[j].append((int(a), int(b), c_parts[j]))

    qexp_decomp = []
    for n in range(prec):
        c_parts = K(qexp[n]).list()
        while len(c_parts) < d:
            c_parts.append(QQ(0))
        qexp_decomp.append(c_parts)

    return poly_per_power, minpoly_coeffs, sturm, qexp_decomp


def emit_alpha_block(weight, minpoly_coeffs, alpha_name):
    d = len(minpoly_coeffs) - 1
    # Build the polynomial as Polynomial ℂ
    poly_terms = []
    poly_terms.append("Polynomial.X ^ " + str(d) if d > 1 else "Polynomial.X")
    if d == 1:
        poly_terms = ["Polynomial.X"]
    else:
        poly_terms = [f"Polynomial.X ^ {d}"]
    for i in range(d):
        c = minpoly_coeffs[i]
        if c == 0:
            continue
        if i == 0:
            poly_terms.append(f"Polynomial.C {fmt_rat(c)}")
        elif i == 1:
            poly_terms.append(f"Polynomial.C {fmt_rat(c)} * Polynomial.X")
        else:
            poly_terms.append(f"Polynomial.C {fmt_rat(c)} * Polynomial.X ^ {i}")
    poly_def = " +\n    ".join(poly_terms)

    # Concrete polynomial relation (used in α_is_root)
    rel_terms = [f"{alpha_name} ^ {d}"] if d > 1 else [f"{alpha_name}"]
    if d == 1:
        rel_terms = [f"{alpha_name}"]
    else:
        rel_terms = [f"{alpha_name} ^ {d}"]
    for i in range(d):
        c = minpoly_coeffs[i]
        if c == 0:
            continue
        if i == 0:
            rel_terms.append(fmt_rat(c))
        elif i == 1:
            rel_terms.append(f"{fmt_rat(c)} * {alpha_name}")
        else:
            rel_terms.append(f"{fmt_rat(c)} * {alpha_name} ^ {i}")
    rel_expr = " +\n      ".join(rel_terms)

    return f"""/-- Minimal polynomial of α (degree {d}) as `Polynomial ℂ`. -/
noncomputable def {alpha_name}_minpoly : Polynomial ℂ :=
  {poly_def}

lemma {alpha_name}_minpoly_natDegree : {alpha_name}_minpoly.natDegree = {d} := by
  unfold {alpha_name}_minpoly
  compute_degree!

lemma {alpha_name}_minpoly_degree_ne_zero : {alpha_name}_minpoly.degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree (fun h => by
    have := {alpha_name}_minpoly_natDegree
    rw [h, Polynomial.natDegree_zero] at this
    exact absurd this (by decide))]
  rw [{alpha_name}_minpoly_natDegree]
  decide

/-- α is some root of the degree-{d} minimal polynomial in ℂ. -/
noncomputable def {alpha_name} : ℂ :=
  (IsAlgClosed.exists_root {alpha_name}_minpoly {alpha_name}_minpoly_degree_ne_zero).choose

lemma {alpha_name}_isRoot : Polynomial.IsRoot {alpha_name}_minpoly {alpha_name} :=
  (IsAlgClosed.exists_root {alpha_name}_minpoly {alpha_name}_minpoly_degree_ne_zero).choose_spec

/-- Explicit polynomial relation: minpoly evaluated at α is zero. -/
lemma {alpha_name}_is_root :
    {rel_expr} = 0 := by
  have h := {alpha_name}_isRoot
  unfold Polynomial.IsRoot {alpha_name}_minpoly at h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X] at h
  linear_combination h"""


def emit_polydata(name, poly):
    if not poly:
        return f"def {name} : List (ℕ × ℕ × ℚ) := []"
    entries = ", ".join(f"({a}, {b}, {fmt_rat(c)})" for (a, b, c) in poly)
    return f"def {name} : List (ℕ × ℕ × ℚ) :=\n  [{entries}]"


def piece_scale_and_int(poly):
    """Common denominator `D` and integer-coefficient polynomial `[(a, b, int(c*D))]`."""
    D = 1
    for (a, b, c) in poly:
        D = lcm(D, c.denominator())
    int_poly = [(int(a), int(b), int(c * D)) for (a, b, c) in poly]
    return int(D), int_poly


def emit_polydataZ(name, int_poly):
    if not int_poly:
        return f"def {name} : List (ℕ × ℕ × ℤ) := []"
    entries = ", ".join(f"({a}, {b}, {fmt_int(z)})" for (a, b, z) in int_poly)
    return f"def {name} : List (ℕ × ℕ × ℤ) :=\n  [{entries}]"


def emit_qexplistZ(name, int_qexp):
    if not int_qexp:
        return f"def {name} : List ℤ := []"
    entries = ", ".join(fmt_int(z) for z in int_qexp)
    return f"def {name} : List ℤ :=\n  [{entries}]"


def emit_part_file(weight, j, n_certify, int_poly, D, int_qexp):
    """A standalone module holding the heavy integer-arithmetic `decide +kernel` for piece j.
    Isolated so `lake` builds all pieces (of all forms) in parallel across cores."""
    header = f"""import LeanBridge.ForMathlib.QExpansion.IntEval

set_option maxHeartbeats 0
set_option maxRecDepth 4000

/-!
# LMFDB level-1 weight-{weight} form `1.{weight}.a`, piece {j}: integer q-coefficient certificate

Heavy `decide +kernel` over `ℤ` (denominators cleared by the scale `D = {D}`), isolated in its own
module so `lake` schedules it in parallel with the other pieces. Generated by
`scripts/lmfdb_qexp_to_e4e6_v3.sage`.
-/

namespace LeanBridge.QExpansion.LMFDB.W{weight}

open LeanBridge.QExpansion
"""
    body = "\n\n".join([
        emit_polydataZ(f"f_{weight}_part_{j}_polyDataZ", int_poly),
        f"def f_{weight}_part_{j}_scale : ℤ := {fmt_int(D)}",
        emit_qexplistZ(f"f_{weight}_part_{j}_qExpListZ", int_qexp),
        f"""/-- Integer-arithmetic certificate (the heavy kernel computation). -/
lemma f_{weight}_part_{j}_evalEisListZ_eq :
    evalEisListZ f_{weight}_part_{j}_polyDataZ {n_certify} = f_{weight}_part_{j}_qExpListZ := by
  decide +kernel""",
    ])
    return header + "\n" + body + f"\n\nend LeanBridge.QExpansion.LMFDB.W{weight}\n"


def emit_form_def(name, weight, poly):
    if not poly:
        return f"noncomputable def {name} : ModularForm 𝒮ℒ {weight} := 0"
    terms = []
    for (a, b, c) in poly:
        terms.append(f"({fmt_rat(c)} : ℂ) • mkMonomForm {a} {b} {weight} (by decide)")
    body = " +\n  ".join(terms)
    return f"noncomputable def {name} : ModularForm 𝒮ℒ {weight} :=\n  {body}"


def emit_bridge_lemma(name, polydata_name, form_name, n_monoms):
    if n_monoms == 0:
        return f"""lemma {name} :
    qExpansion 1 ({form_name} : ℍ → ℂ) = evalEisPS {polydata_name} := by
  unfold {form_name} {polydata_name} evalEisPS
  simp [qExpansion_zero]"""

    rw_lines = []
    for _ in range(n_monoms - 1):
        rw_lines.append("ModularForm.coe_add")
        rw_lines.append("ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL")
    for _ in range(n_monoms):
        rw_lines.append("ModularForm.IsGLPos.coe_smul")
    for _ in range(n_monoms):
        rw_lines.append("ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL")
    for _ in range(n_monoms):
        rw_lines.append("qExpansion_mkMonomForm")
    rw_chain = ",\n    ".join(rw_lines)

    return f"""lemma {name} :
    qExpansion 1 ({form_name} : ℍ → ℂ) = evalEisPS {polydata_name} := by
  unfold {form_name}
  rw [{rw_chain}]
  unfold evalEisPS {polydata_name} monomialEisPS
  simp only [List.foldr_cons, List.foldr_nil, add_zero]
  push_cast
  module"""


def emit_combined_form(weight, n_pieces, alpha_name):
    terms = [f"f_{weight}_part_0"]
    for j in range(1, n_pieces):
        if j == 1:
            terms.append(f"{alpha_name} • f_{weight}_part_{j}")
        else:
            terms.append(f"{alpha_name} ^ {j} • f_{weight}_part_{j}")
    body = " +\n  ".join(terms)
    return f"""noncomputable def lmfdb_1_{weight}_a_orbit : ModularForm 𝒮ℒ {weight} :=
  {body}"""


def emit_coeff_decomp(weight, n_pieces, alpha_name):
    rhs_terms = []
    for j in range(n_pieces):
        coeff_term = f"(PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_{weight}_part_{j} : ℍ → ℂ))"
        if j == 0:
            rhs_terms.append(coeff_term)
        elif j == 1:
            rhs_terms.append(f"{alpha_name} * {coeff_term}")
        else:
            rhs_terms.append(f"{alpha_name} ^ {j} * {coeff_term}")
    rhs = "\n        + ".join(rhs_terms)

    if n_pieces <= 1:
        # Single-piece (degree-1 Hecke field): orbit IS just the unique form
        return f"""lemma lmfdb_1_{weight}_a_orbit_coeff_decomp (n : ℕ) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (lmfdb_1_{weight}_a_orbit : ℍ → ℂ))
      = {rhs} := by
  rfl"""

    n_smuls = n_pieces - 1
    rw_lines = []
    for _ in range(n_pieces - 1):
        rw_lines.append("ModularForm.coe_add")
        rw_lines.append("ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL")
    for _ in range(n_smuls):
        rw_lines.append("ModularForm.IsGLPos.coe_smul")
    for _ in range(n_smuls):
        rw_lines.append("ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL")
    rw_chain = ",\n    ".join(rw_lines)

    return f"""lemma lmfdb_1_{weight}_a_orbit_coeff_decomp (n : ℕ) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (lmfdb_1_{weight}_a_orbit : ℍ → ℂ))
      = {rhs} := by
  unfold lmfdb_1_{weight}_a_orbit
  rw [{rw_chain}]
  simp [smul_eq_mul]"""


def emit_precomputed_list(weight, j, n_certify, piece_qexp):
    """Emit the precomputed (rational) q-expansion list for piece j and the bridge lemma that
    reduces `evalEisList` (over ℚ) to the integer certificate `…_evalEisListZ_eq` (over ℤ),
    proven in the per-piece part module."""
    entries = ", ".join(fmt_rat(c) for c in piece_qexp)
    return f"""/-- Precomputed first {n_certify} q-coefficients of `f_{weight}_part_{j}` (rational). -/
def f_{weight}_part_{j}_qExpList : List ℚ :=
  [{entries}]

/-- Bridge: the symbolic `evalEisList` (over ℚ) equals the precomputed list. The heavy kernel work
is the integer certificate `f_{weight}_part_{j}_evalEisListZ_eq`; the steps here are cheap rational
list checks. -/
lemma f_{weight}_part_{j}_evalEisList_eq :
    evalEisList f_{weight}_part_{j}_polyData {n_certify} = f_{weight}_part_{j}_qExpList := by
  have h : f_{weight}_part_{j}_polyData
      = f_{weight}_part_{j}_polyDataZ.map
          (fun t => (t.1, t.2.1, (t.2.2 : ℚ) / f_{weight}_part_{j}_scale)) := by
    decide +kernel
  rw [h, evalEisList_eq_intCast_div, f_{weight}_part_{j}_evalEisListZ_eq]
  decide +kernel"""


def emit_named_coeff_lemma(weight, n, n_certify, qexp_decomp_n, n_pieces, alpha_name):
    """Named lemma for coefficient n of `lmfdb_1_{weight}_a_orbit`.
    Uses the precomputed `_qExpList` (cheap list lookup) instead of `evalEisList` (slow)."""
    rhs_parts = []
    for j, c in enumerate(qexp_decomp_n):
        if c == 0:
            continue
        cs = fmt_rat(c)
        if j == 0:
            rhs_parts.append(cs)
        elif j == 1:
            rhs_parts.append(f"{cs} * {alpha_name}")
        else:
            rhs_parts.append(f"{cs} * {alpha_name} ^ {j}")
    rhs = " + ".join(rhs_parts) if rhs_parts else "0"

    coeff_thm_rws = ",\n    ".join(
        f"f_{weight}_part_{j}_qExpansion_coeff {n_certify} {n} (by decide)"
        for j in range(n_pieces))
    eval_eq_rws = ",\n    ".join(
        f"f_{weight}_part_{j}_evalEisList_eq"
        for j in range(n_pieces))
    list_value_rws = []
    for j in range(n_pieces):
        c = qexp_decomp_n[j] if j < len(qexp_decomp_n) else 0
        list_value_rws.append(
            f"show f_{weight}_part_{j}_qExpList.getD {n} 0 = "
            f"({fmt_rat(c)} : ℚ) from by decide +kernel"
        )
    list_rws = ",\n    ".join(list_value_rws)

    return f"""lemma lmfdb_1_{weight}_a_orbit_qExpansion_coeff_{n} :
    (PowerSeries.coeff (R := ℂ) {n})
      (qExpansion 1 (lmfdb_1_{weight}_a_orbit : ℍ → ℂ)) = {rhs} := by
  rw [lmfdb_1_{weight}_a_orbit_coeff_decomp,
    {coeff_thm_rws},
    {eval_eq_rws},
    {list_rws}]
  push_cast; ring"""


def emit_uniqueness_theorem(weight, sturm, qexp_decomp, n_pieces, alpha_name):
    """Uniqueness theorem: f = lmfdb_1_{weight}_a_orbit if first sturm coeffs match."""
    # Hypotheses: one per i ∈ {0, …, sturm-1}
    hypotheses = []
    for i in range(sturm):
        rhs_parts = []
        for j, c in enumerate(qexp_decomp[i]):
            if c == 0:
                continue
            cs = fmt_rat(c)
            if j == 0:
                rhs_parts.append(cs)
            elif j == 1:
                rhs_parts.append(f"{cs} * {alpha_name}")
            else:
                rhs_parts.append(f"{cs} * {alpha_name} ^ {j}")
        rhs = " + ".join(rhs_parts) if rhs_parts else "0"
        hypotheses.append(
            f"    (h_{i} : (PowerSeries.coeff (R := ℂ) {i}) (qExpansion 1 (f : ℍ → ℂ)) = {rhs})")
    hyp_block = "\n".join(hypotheses)

    # Cases: one per i
    case_lines = []
    for i in range(sturm):
        case_lines.append(
            f"  · rw [h_{i}, lmfdb_1_{weight}_a_orbit_qExpansion_coeff_{i}]")
    cases = "\n".join(case_lines)

    return f"""/-- **Uniqueness theorem.** Any level-1 weight-{weight} modular form `f` whose first {sturm}
q-coefficients match the LMFDB-published values for `1.{weight}.a.{{a..}}` is equal to our
explicit construction `lmfdb_1_{weight}_a_orbit`. Proven via `ModularForm.eq_of_sturm_bound`. -/
theorem identifies_lmfdb_1_{weight}_a_orbit (f : ModularForm 𝒮ℒ {weight})
{hyp_block} :
    f = lmfdb_1_{weight}_a_orbit := by
  apply ModularForm.eq_of_sturm_bound
  intro i hi
  have : i ≤ {sturm - 1} := by omega
  interval_cases i
{cases}"""


def emit_full(weight, form_idx=0):
    poly_per_power, minpoly_coeffs, sturm, qexp_decomp = newform_decomposition(weight, form_idx)
    n_pieces = len(poly_per_power)
    alpha_name = f"α_{weight}"
    n_certify = max(sturm, MIN_CERTIFY)

    # Per-piece integer data + standalone part modules (heavy `decide +kernel` lives here).
    part_files = {}
    for j in range(n_pieces):
        D, int_poly = piece_scale_and_int(poly_per_power[j])
        int_qexp = [int(D * (qexp_decomp[n][j] if j < len(qexp_decomp[n]) else 0))
                    for n in range(n_certify)]
        part_files[j] = emit_part_file(weight, j, n_certify, int_poly, D, int_qexp)

    part_imports = "\n".join(
        f"import LeanBridge.ForMathlib.QExpansion.LMFDB.Weight_{weight}_part_{j}"
        for j in range(n_pieces))

    parts = [f"""import LeanBridge.ForMathlib.QExpansion.IntEval
import LeanBridge.ForMathlib.QExpansion.Sturm
import Mathlib.Analysis.Complex.Polynomial.Basic
{part_imports}

set_option maxHeartbeats 0
set_option maxRecDepth 2000

/-!
# LMFDB level-1 modular form orbit `1.{weight}.a.{{a..}}` (Hecke field degree {n_pieces})

The Hecke field `K = ℚ(α)` is degree {n_pieces} over ℚ. The LMFDB lists q-coefficients as
elements of `K`, which we decompose as `c_0 + c_1 · α + … + c_{{{n_pieces - 1}}} · α^{n_pieces - 1}`.
The combined form is `f = f_0 + α · f_1 + … + α^{n_pieces - 1} · f_{{{n_pieces - 1}}}`, with each
`f_j` a level-1 weight-{weight} form with rational coefficients in `(E₄, E₆)`.

The Sturm bound for weight {weight} is `⌊{weight}/12⌋ + 1 = {sturm}`. After certifying agreement
on the first {sturm} q-coefficients, `ModularForm.eq_of_sturm_bound` lets us conclude that any
form with the same coefficients equals our explicit `lmfdb_1_{weight}_a_orbit`.

Generated by `scripts/lmfdb_qexp_to_e4e6_v3.sage`.
-/

namespace LeanBridge.QExpansion.LMFDB.W{weight}

open LeanBridge.QExpansion ModularForm EisensteinSeries PowerSeries UpperHalfPlane
open scoped MatrixGroups
"""]

    parts.append(emit_alpha_block(weight, minpoly_coeffs, alpha_name))

    for j in range(n_pieces):
        parts.append(f"\n/-! ## Piece {j}: coefficient of α^{j} -/\n")
        parts.append(emit_polydata(f"f_{weight}_part_{j}_polyData", poly_per_power[j]))
        n_monoms = len(poly_per_power[j])
        parts.append(emit_form_def(f"f_{weight}_part_{j}", weight, poly_per_power[j]))
        parts.append(emit_bridge_lemma(
            f"f_{weight}_part_{j}_qExpansion_eq_evalEisPS",
            f"f_{weight}_part_{j}_polyData",
            f"f_{weight}_part_{j}",
            n_monoms))
        parts.append(f"""theorem f_{weight}_part_{j}_qExpansion_coeff (N n : ℕ) (hn : n < N) :
    (PowerSeries.coeff (R := ℂ) n) (qExpansion 1 (f_{weight}_part_{j} : ℍ → ℂ))
      = ((evalEisList f_{weight}_part_{j}_polyData N).getD n 0 : ℚ) :=
  qexp_coeff_via_E4E6 _ _ f_{weight}_part_{j}_qExpansion_eq_evalEisPS N n hn""")
        # Precomputed (rational) q-expansion list + bridge to the integer certificate
        piece_qexp = [qexp_decomp[n][j] if j < len(qexp_decomp[n]) else 0
                      for n in range(n_certify)]
        parts.append(emit_precomputed_list(weight, j, n_certify, piece_qexp))

    parts.append("\n/-! ## Combined LMFDB form -/\n")
    parts.append(emit_combined_form(weight, n_pieces, alpha_name))
    parts.append(emit_coeff_decomp(weight, n_pieces, alpha_name))

    parts.append(f"\n/-! ## Coefficient lemmas (n = 0, …, {n_certify - 1})\n\n"
                 f"Sturm bound is {sturm}; we certify {n_certify} coefficients for added\n"
                 f"redundancy beyond the minimum mathematically required for uniqueness. -/\n")
    for n in range(n_certify):
        parts.append(emit_named_coeff_lemma(
            weight, n, n_certify, qexp_decomp[n], n_pieces, alpha_name))

    parts.append("\n/-! ## Uniqueness theorem -/\n")
    parts.append(emit_uniqueness_theorem(weight, sturm, qexp_decomp, n_pieces, alpha_name))

    parts.append(f"\nend LeanBridge.QExpansion.LMFDB.W{weight}")
    return "\n\n".join(parts), part_files


def main():
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        sys.exit(1)
    weight = int(sys.argv[1])
    form_idx = int(sys.argv[2]) if len(sys.argv) >= 3 else 0
    out_path = sys.argv[3] if len(sys.argv) >= 4 else None

    code, part_files = emit_full(weight, form_idx)

    if out_path:
        out_dir = os.path.dirname(os.path.abspath(out_path))
        os.makedirs(out_dir, exist_ok=True)
        with open(out_path, 'w') as f:
            f.write(code)
        print(f"Wrote {out_path}", file=sys.stderr)
        # Part modules: Weight_{k}_part_{j}.lean next to the assembly file.
        base = os.path.basename(out_path)
        stem = base[:-5] if base.endswith('.lean') else base  # strip .lean
        for j, part_code in part_files.items():
            part_path = os.path.join(out_dir, f"{stem}_part_{j}.lean")
            with open(part_path, 'w') as f:
                f.write(part_code)
        print(f"Wrote {len(part_files)} part modules", file=sys.stderr)
    else:
        sys.stdout.write(code)


main()
