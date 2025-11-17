#!/usr/bin/env python3
import sys
import json
from decimal import Decimal

def decimal_default(obj):
    """JSON serializer for Decimal objects"""
    if isinstance(obj, Decimal):
        return str(obj)
    raise TypeError

def main():
    if len(sys.argv) != 2:
        print("Usage: python lmfdb_query_range.py '<json_params>'", file=sys.stderr)
        sys.exit(1)

    try:
        from lmf import db
    except ImportError:
        print("Error: lmfdb-lite not installed", file=sys.stderr)
        sys.exit(1)

    # Parse JSON parameters
    try:
        params = json.loads(sys.argv[1])
    except json.JSONDecodeError as e:
        print(f"Error parsing JSON: {e}", file=sys.stderr)
        sys.exit(1)

    print(f"DEBUG: Received parameters: {params}", file=sys.stderr)

    # Build query using lmfdb-lite query language
    query = {}

    # Range helpers
    def add_range(field, min_key, max_key):
        if min_key in params and max_key in params:
            query[field] = {'$gte': params[min_key], '$lte': params[max_key]}
        elif min_key in params:
            query[field] = {'$gte': params[min_key]}
        elif max_key in params:
            query[field] = {'$lte': params[max_key]}

    # Ranges
    add_range('degree', 'degree_min', 'degree_max')
    add_range('r2', 'r2_min', 'r2_max')
    add_range('disc_abs', 'disc_abs_min', 'disc_abs_max')
    add_range('rd', 'rd_min', 'rd_max')
    add_range('grd', 'grd_min', 'grd_max')
    add_range('num_ram', 'num_ram_min', 'num_ram_max')
    add_range('regulator', 'regulator_min', 'regulator_max')

    # Exact matches
    for field in ['class_number', 'narrow_class_number', 'disc_sign',
                  'is_galois', 'gal_is_abelian', 'gal_is_cyclic', 'gal_is_solvable',
                  'cm', 'monogenic', 'is_minimal_sibling', 'galois_label']:
        if field in params and params[field] is not None:
            query[field] = params[field]

    # Handle signature specially - convert to r2
    if 'signature' in params and params['signature'] is not None:
        sig_str = params['signature']
        if sig_str:
            try:
                # Parse signature like "[1,2]" -> [r1, r2]
                import ast
                sig = ast.literal_eval(sig_str)
                if isinstance(sig, list) and len(sig) == 2:
                    r1, r2 = sig
                    # Set r2 constraint
                    query['r2'] = r2
                    # Set degree = r1 + 2*r2
                    degree = r1 + 2 * r2
                    query['degree'] = degree
                    print(f"DEBUG: Parsed signature {sig} -> r2={r2}, degree={degree}", file=sys.stderr)
            except Exception as e:
                print(f"DEBUG: Could not parse signature '{sig_str}': {e}", file=sys.stderr)

    # String/array fields (skip signature as we handled it above)
    for field in ['class_group', 'narrow_class_group',
                  'ramps', 'unramified_primes', 'inessentialp']:
        if field in params and params[field] is not None:
            val = params[field]
            # Try to parse as JSON array if it looks like one
            if isinstance(val, str) and val.startswith('['):
                try:
                    query[field] = json.loads(val)
                except:
                    query[field] = val
            else:
                query[field] = val

    limit = params.get('limit', 50)

    print(f"DEBUG: Query dict: {query}", file=sys.stderr)

    try:
        # Use lmfdb-lite to search
        results = list(db.nf_fields.search(
            query,
            ['label', 'class_number', 'is_galois', 'coeffs', 'disc_abs', 'disc_sign', 'cm'],
            limit=limit
        ))

        print(f"DEBUG: Found {len(results)} results", file=sys.stderr)

        # Format output for Lean parsing
        if results:
            print(f"LMFDB_RECORDS_FOUND:{len(results)}")
            for row in results:
                label = row['label']
                class_number = int(row['class_number']) if row['class_number'] is not None else 0
                is_galois = "True" if row['is_galois'] else "False"
                coeffs = ','.join(map(str, row['coeffs']))
                disc_abs = str(row['disc_abs'])
                disc_sign = int(row['disc_sign']) if row['disc_sign'] is not None else 0
                cm = "True" if row.get('cm') else "False"

                print(f"{label} {class_number} {is_galois} {coeffs} {disc_abs} {disc_sign} {cm}")
        else:
            print("No fields found")

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
