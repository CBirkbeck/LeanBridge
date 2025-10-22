# lmfdb_query.py

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

        # UPDATED: Selects disc_abs and disc_sign
        sql_query = """
        SELECT label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm
        FROM nf_fields
        WHERE degree = %s AND r2 = %s AND disc_abs = %s;
        """
        cursor.execute(sql_query, (degree, r2, d_abs))
        # Now fetches 6 columns
        results = cursor.fetchall()

        cursor.close()
        conn.close()

    except psycopg2.OperationalError as e:
        print(f"Error connecting to the database: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error querying the database: {e}", file=sys.stderr)
        sys.exit(1)

    if not results:
        print("No fields found")
        return

    # UPDATED: Prints 6 parts of data
    for result in results:
        label, class_number, is_galois, coeffs, disc_abs, disc_sign, cm = result
        coeffs_str = ','.join(map(str, coeffs))
        # Output is now: label, class_number, is_galois, coeffs_str, disc_abs, disc_sign, cm
        print(f"{label} {class_number} {is_galois} {coeffs_str} {disc_abs} {disc_sign} {cm}")

if __name__ == "__main__":
    main()
