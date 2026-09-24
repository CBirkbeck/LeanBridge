# lmfdb_query.py (Final attempt at fixing the logic)

import sys
import psycopg2
import json

def main():
    if len(sys.argv) != 4:
        print("Usage: python lmfdb_query.py <degree> <r2> <D_abs>", file=sys.stderr)
        sys.exit(1)

    try:
        # Arguments are degree, r2, D_abs
        degree = int(sys.argv[1])
        r2 = int(sys.argv[2])
        d_abs = int(sys.argv[3])
    except ValueError:
        print("Error: Arguments must be integers.", file=sys.stderr)
        sys.exit(1)

    conn_string = "host=devmirror.lmfdb.xyz port=5432 dbname=lmfdb user=lmfdb password=lmfdb"

    try:
        conn = psycopg2.connect(conn_string)
        cursor = conn.cursor()

        # SQL query now selects all 7 required fields
        sql_query = """
        SELECT label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
        FROM nf_fields
        WHERE degree = %s AND r2 = %s AND disc_abs = %s;
        """
        cursor.execute(sql_query, (degree, r2, d_abs))
        results = cursor.fetchall()

        cursor.close()
        conn.close()

    except psycopg2.OperationalError as e:
        print(f"Error connecting to the database: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error during SQL execution: {e}", file=sys.stderr)
        sys.exit(1)

    if not results:
        # Crucial Debug: Print a distinct failure message to stdout
        print("No fields found: SQL returned 0 rows")
        return

    # Critical Debugging Line to tell Lean how many records were found:
    print(f"LMFDB_RECORDS_FOUND:{len(results)}")

    # Robust unpacking and printing
    for i, result in enumerate(results):
        try:
            # Unpacks 7 columns: label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
            label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm = result

            # Ensure booleans are capitalized strings for Lean parsing
            is_galois_str = str(is_galois).capitalize()
            cm_str = str(cm).capitalize()

            # Use list comprehension to ensure all coefficients are clean strings
            coeffs_str = ','.join(map(str, coeffs))

            # Output 7 space-separated values for the Lean tactic to parse
            print(f"{label} {class_number} {is_galois_str} {coeffs_str} {disc_abs} {disc_sign} {cm_str}")

        except Exception as e:
            # Log failure of a single record, but let the script continue
            print(f"Failed to process record {i} ({label}): {e}", file=sys.stderr)
            continue


if __name__ == "__main__":
    main()
