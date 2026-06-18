import re

def polynomial_to_lean(poly, var_name, is_int_poly=False):
    """
    Converts a Sage polynomial to a string representation suitable for Lean,
    using the specified variable name and the '^' exponentiation operator.
    """
    s = str(poly)
    # Replace the variable 'x' with the Lean variable name (e.g., 'K_gen_int')
    s = re.sub(r'x', var_name, s)
    # Replace Sage/Python '**' and '^' with Lean's '^'
    s = re.sub(r'\*\*', r'^', s)
    s = re.sub(r'\^', r'^', s)

    # Replace implicit multiplication like '2*x' with explicit '2 * x'
    s = s.replace('*', ' * ')

    # Handle fractions (e.g., 1/2) by ensuring they are wrapped in parentheses
    s = re.sub(r'(\d)/(\d)', r'\((\1) / (\2)\)', s)

    # Clean up and simplify
    s = re.sub(r' \^ 0', '', s) # Remove x^0 terms
    s = s.replace('  ', ' ')
    s = s.strip()

    # Special formatting for the `Polynomial ℤ` definition
    if is_int_poly:
        # Convert coefficients to the (c) * Polynomial.X ^ n format
        terms = []
        # Ensure we are dealing with integer coefficients
        int_poly = poly.map_coefficients(lambda c: ZZ(c))

        for deg in range(int_poly.degree() + 1):
            c = int_poly.coefficient(deg)
            if c != 0:
                coeff_str = f"({c})"
                if deg == 0:
                    terms.append(coeff_str)
                elif deg == 1:
                    terms.append(f"{coeff_str} * Polynomial.X")
                else:
                    terms.append(f"{coeff_str} * Polynomial.X ^ {deg}")

        # Join with '+' and handle potential leading negatives by ensuring the first
        # term is always wrapped if it starts with a negative.
        lean_int_poly = " + ".join(terms)
        return lean_int_poly.replace('+ -', '- ')

    return s.replace(f"{var_name} ^ 1", var_name) # Remove explicit ^ 1

def generate_lmfdb_id(min_poly):
    """
    Generates a simple identifier string based on the minimal polynomial's
    coefficients.
    """
    coeffs = min_poly.list()
    # Use only integer coefficients and join them
    coeff_part = "_".join(str(ZZ(c)).replace('-', 'minus') for c in reversed(coeffs))
    return f"deg{min_poly.degree()}_{coeff_part}"

def unit_basis_certificate_lean_file(min_poly, lmfdb_id_suffix=""):
    """
    Generates a single Lean file containing the full number field setup
    and the unit certificates for all fundamental units.
    """
    R = min_poly.parent()
    K = NumberField(min_poly, 'a')

    # 1. Determine Naming Convention
    if not lmfdb_id_suffix:
         lmfdb_id_suffix = generate_lmfdb_id(min_poly)

    lmfdb_id = lmfdb_id_suffix

    min_poly_id = f"min_poly_{lmfdb_id}"
    min_poly_int_id = f"{min_poly_id}_int"
    field_id = f"K_{lmfdb_id}"

    # Calculate the integer polynomial representation for the Lean abbrev
    min_poly_int_lean = polynomial_to_lean(min_poly, 'Polynomial.X', is_int_poly=True)

    # 2. Get Fundamental Units
    try:
        U = K.unit_group()
        units = U.fundamental_units()
    except Exception as e:
        return f"Error computing unit group: {e}"

    # 3. Start Lean Content (Template)

    # Get the minimal polynomial in the form for the K_gen_int_pol lemma statement
    lean_min_poly_statement = polynomial_to_lean(min_poly, 'K_gen_int')
    lean_min_poly_suffices = polynomial_to_lean(min_poly, 'K_gen')

    lean_content = f"""
import Mathlib
import LeanBridge.ForMathlib.tactics.LMFDB_search
-- import LeanBridge.ForMathlib.tactics.LMFDB_Proof_{lmfdb_id}

noncomputable section

open NumberField

-- Minimal polynomial over ℤ
abbrev {min_poly_int_id} : Polynomial ℤ := {min_poly_int_lean}

-- Minimal polynomial over ℚ
abbrev {min_poly_id} : Polynomial ℚ := (({min_poly_int_id}).mapRingHom (Int.castRingHom ℚ))

-- The number field K = ℚ[x] / <f(x)>
abbrev {field_id} := AdjoinRoot {min_poly_id}

-- ASSUME: Irreducibility and LMFDB axioms are proved/stated elsewhere
lemma irreducible_poly : Irreducible {min_poly_id} := sorry
instance: Fact (Irreducible {min_poly_id}) := ⟨irreducible_poly⟩
axiom LMFDB_NF_{lmfdb_id}_discr : NumberField.discr {field_id} = sorry
axiom LMFDB_NF_{lmfdb_id}_isGalois : IsGalois ℚ {field_id}
axiom LMFDB_NF_{lmfdb_id}_classNumber : NumberField.classNumber {field_id} = sorry

lemma unit_rank : NumberField.Units.rank {field_id} = {len(units)} := by
  simp_rw [Units.rank]
  sorry

-- The generator 'a' of the number field
abbrev K_gen : {field_id} := AdjoinRoot.root {min_poly_id}

-- Assuming a lemma exists to prove the generator is integral
lemma K_int : IsIntegral ℤ K_gen := sorry

-- The generator as an algebraic integer (element of the ring of integers 𝓞 K)
def K_gen_int : 𝓞 {field_id} := ⟨K_gen, K_int⟩

-- Lemma stating that the polynomial identity for the generator holds
lemma K_gen_int_pol : {lean_min_poly_statement} = 0 := by
  simp [K_gen_int, {min_poly_id}]
  suffices {lean_min_poly_suffices} = 0 by
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  simpa [K_gen, {min_poly_id}] using AdjoinRoot.eval₂_root {min_poly_id}

"""

    # 4. Append Unit Definitions (All in one file)
    for i, unit in enumerate(units):
        unit_idx = i + 1
        unit_name = f"fundamental_unit_{unit_idx}"

        # Get components
        unit_inverse = unit.inverse()
        poly_u = unit.polynomial()
        poly_u_inv = unit_inverse.polynomial()

        # Calculate the certificate poly_id
        P_x = (poly_u * poly_u_inv) - R(1)
        poly_id = P_x / min_poly

        # Convert polynomials to Lean syntax
        lean_poly_u = polynomial_to_lean(poly_u, 'K_gen_int')
        lean_poly_u_inv = polynomial_to_lean(poly_u_inv, 'K_gen_int')
        lean_poly_id = polynomial_to_lean(poly_id, 'K_gen_int')

        # The key identity: (poly_u) * (poly_u_inv) = 1 + poly_id * min_poly(K_gen_int)
        # Note the (poly_id) is explicitly wrapped for clarity, as required.
        identity_lemma = f"({lean_poly_u}) * ({lean_poly_u_inv}) = 1 + ({lean_poly_id}) * {lean_min_poly_statement}"

        # Append the definition to the content
        lean_content += f"""
def {unit_name} : (𝓞 {field_id})ˣ where
  val := {lean_poly_u}
  inv := {lean_poly_u_inv}
  val_inv := by
    -- Proof that val * inv = 1, using the polynomial identity certificate
    have : {identity_lemma} := by ring
    simp [ K_gen_int_pol ] at this
    grind
  inv_val := by
    -- Proof that inv * val = 1 (using commutativity)
    have : {identity_lemma} := by ring
    simp [ K_gen_int_pol ] at this
    grind

"""
    lean_content += "\nend\n" # Close the noncomputable section

    # 5. Write the content to a single file
    file_name = f"{min_poly_id}.lean"
    with open(file_name, 'w') as f:
        f.write(lean_content)

    return f"Successfully generated a single Lean unit certificate file: **{file_name}**"

# -------------------------------------------------------------
## Example Usage (Only run this once to produce a single file)
# -------------------------------------------------------------

# We'll use the specific polynomial x^2 - 2 and the LMFDB suffix 'test'
# to match your template exactly.

R = PolynomialRing(QQ, 'x')
f = R('x^5 - 2')

# ONLY RUN THIS ONCE to generate the file min_poly_2_2_8_1.lean
# which will contain fundamental_unit_1 (and more if the rank were higher).
print(unit_basis_certificate_lean_file(f, lmfdb_id_suffix="unittest"))
