#!/usr/bin/env python3
"""LMFDB number field search using direct PostgreSQL queries.

Uses psycopg2 directly instead of lmfdb-lite to avoid importing sage.all,
which is slow and has dependency issues (e.g. Singular not on PATH).
"""
import sys
import json

# Fields stored as smallint (0/1) in LMFDB, not boolean
SMALLINT_BOOL_FIELDS = frozenset({
    'is_galois', 'gal_is_abelian', 'gal_is_cyclic', 'gal_is_solvable',
    'cm', 'monogenic', 'is_minimal_sibling'
})

def main():
    if len(sys.argv) != 2:
        print("Usage: python lmfdb_query_range.py '<json_params>'", file=sys.stderr)
        sys.exit(1)

    try:
        import psycopg2
    except ImportError:
        print("Error: psycopg2 not installed. Install with: pip install psycopg2-binary", file=sys.stderr)
        sys.exit(1)

    try:
        params = json.loads(sys.argv[1])
    except json.JSONDecodeError as e:
        print(f"Error parsing JSON: {e}", file=sys.stderr)
        sys.exit(1)

    # Build WHERE clauses
    conditions = []
    values = []

    def add_range(field, min_key, max_key):
        if min_key in params and params[min_key] is not None:
            conditions.append(f'"{field}" >= %s')
            values.append(params[min_key])
        if max_key in params and params[max_key] is not None:
            conditions.append(f'"{field}" <= %s')
            values.append(params[max_key])

    # Range queries
    add_range('degree', 'degree_min', 'degree_max')
    add_range('r2', 'r2_min', 'r2_max')
    add_range('disc_abs', 'disc_abs_min', 'disc_abs_max')
    add_range('rd', 'rd_min', 'rd_max')
    add_range('grd', 'grd_min', 'grd_max')
    add_range('num_ram', 'num_ram_min', 'num_ram_max')
    add_range('regulator', 'regulator_min', 'regulator_max')

    # Integer exact-match fields
    for field in ['class_number', 'narrow_class_number', 'disc_sign']:
        if field in params and params[field] is not None:
            conditions.append(f'"{field}" = %s')
            values.append(int(params[field]))

    # Boolean fields stored as smallint in LMFDB: convert True/False → 1/0
    for field in SMALLINT_BOOL_FIELDS:
        if field in params and params[field] is not None:
            conditions.append(f'"{field}" = %s')
            values.append(1 if params[field] else 0)

    # String exact-match fields
    for field in ['galois_label']:
        if field in params and params[field] is not None:
            conditions.append(f'"{field}" = %s')
            values.append(params[field])

    # Handle signature: [r1, r2] → degree = r1 + 2*r2, r2 = r2
    if 'signature' in params and params['signature'] is not None:
        sig_str = params['signature']
        if sig_str:
            try:
                import ast
                sig = ast.literal_eval(sig_str)
                if isinstance(sig, list) and len(sig) == 2:
                    r1, r2 = sig
                    conditions.append('"r2" = %s')
                    values.append(r2)
                    conditions.append('"degree" = %s')
                    values.append(r1 + 2 * r2)
            except Exception as e:
                print(f"Warning: could not parse signature '{sig_str}': {e}", file=sys.stderr)

    # Coefficients search: comma-separated string like "-57,-1,1" → integer array
    if 'coeffs' in params and params['coeffs'] is not None:
        coeffs_str = params['coeffs']
        try:
            if isinstance(coeffs_str, str):
                coeffs = [int(c.strip()) for c in coeffs_str.split(',')]
            elif isinstance(coeffs_str, list):
                coeffs = [int(c) for c in coeffs_str]
            else:
                coeffs = None
            if coeffs is not None:
                conditions.append('"coeffs" = %s::numeric[]')
                values.append(coeffs)
        except (ValueError, TypeError) as e:
            print(f"Warning: could not parse coefficients '{coeffs_str}': {e}", file=sys.stderr)

    # Array fields
    for field in ['class_group', 'narrow_class_group',
                  'ramps', 'unramified_primes', 'inessentialp']:
        if field in params and params[field] is not None:
            val = params[field]
            if isinstance(val, str) and val.startswith('['):
                try:
                    val = json.loads(val)
                except json.JSONDecodeError:
                    pass
            conditions.append(f'"{field}" = %s')
            values.append(val)

    limit = params.get('limit', 50)

    where_clause = " AND ".join(conditions) if conditions else "TRUE"
    sql = f"""
        SELECT label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
        FROM nf_fields
        WHERE {where_clause}
        ORDER BY degree, disc_abs, disc_sign, iso_number
        LIMIT %s
    """
    values.append(limit)

    try:
        conn = psycopg2.connect(
            host="devmirror.lmfdb.xyz",
            port=5432,
            dbname="lmfdb",
            user="lmfdb",
            password="lmfdb",
            connect_timeout=15
        )
        cursor = conn.cursor()
        cursor.execute(sql, values)
        results = cursor.fetchall()
        cursor.close()
        conn.close()
    except psycopg2.OperationalError as e:
        print(f"Error connecting to LMFDB database: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)

    if results:
        print(f"LMFDB_RECORDS_FOUND:{len(results)}")
        for row in results:
            label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm = row
            class_number = int(class_number) if class_number is not None else 0
            is_galois_str = "True" if is_galois else "False"
            coeffs_str = ','.join(map(str, coeffs))
            disc_abs_str = str(disc_abs)
            disc_sign = int(disc_sign) if disc_sign is not None else 0
            cm_str = "True" if cm else "False"
            print(f"{label} {class_number} {is_galois_str} {coeffs_str} {disc_abs_str} {disc_sign} {cm_str}")
    else:
        print("No fields found")

if __name__ == "__main__":
    main()
