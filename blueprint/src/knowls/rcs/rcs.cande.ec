\subsection{Completeness of elliptic curve data}
\begin{definition}\label{rcs.cande.ec}
\uses{ec.good_reduction,ec.invariants,ec.isogeny,mf.hilbert.weight_vector,nf,nf.degree,nf.discriminant,nf.signature,nf.totally_real,rcs.cande.mf.bianchi}
{% if ecnf_summary is defined %}
  {{ ecnf_summary|safe}}
{% else %}
  This information can only be displayed with a more recent version of the LMFDB.
{% endif %}

### Imaginary quadratic fields
Over each imaginary quadratic {{KNOWL('nf', 'number field')}} of absolute discriminant less than \(700\),  the database contains elliptic curves of {{KNOWL('ec.invariants', 'conductor norm')}} up to  a bound that depends on the field, corresponding to the {{KNOWL('rcs.cande.mf.bianchi', 'level norm bound')}} for Bianchi modular forms over that field.
<!---
<table>
<tr>
<th>{{KNOWL('nf.discriminant', 'Discriminant')}}<td>-3<td>-4<td>-7<td>-8<td>-11<td>-19<td>-43<td>-67<td>-163<td>-23<td>-31
</tr>
<th>Bound<td>150000<td>100000<td>50000<td>50000<td>50000<td>15000<td>15000<td>10000<td>5000<td>2000<td>5000
</tr>
</table>
--->
Within these bounds the database contains all *modular* elliptic curves; however, modularity has not yet been proved for elliptic curves over imaginary quadratic fields in general, and non-modular curves (if any exist) are not in the database.  Assuming modularity, the database is complete within these bounds, by comparison with the database of Bianchi modular forms.

In addition the database contains a small number of elliptic curves with everywhere {{KNOWL('ec.good_reduction', 'good reduction')}} defined over some other imaginary quadratic fields.

### {{KNOWL('nf.totally_real', 'Totally real')}} fields
The database contains elliptic curves defined over totally real fields of {{KNOWL('nf.degree', 'degree')}} \(2, 3, 4, 5\) and \(6\).  For each field the database contains curves of conductor norm up to a bound which depends on the field.  Over totally real fields of degree \(2\) and \(3\),  it is known that all elliptic curves are modular, and hence the database is complete for these fields, by comparison with the database of Hilbert Modular Forms.  In higher degrees the database contains elliptic curves matching each of the Hilbert Modular Forms (of {{KNOWL('mf.hilbert.weight_vector', 'parallel weight')}} \(2\), trivial character and rational coefficients) over the field in question, for fields of degree up to \(6\), and hence contains all modular elliptic curves of conductor norm up to the bound for that field.

### Other fields
The only other field for which the database contains elliptic curves is the mixed {{KNOWL('nf.signature', 'signature')}} cubic field 3.1.23.1.  The elliptic curves here have conductor norm up to \(20000\) and match automorphic forms over this field.  No results on modularity are known for this field, but the curves in the database include all modular curves within these bounds.

For the complete list of fields over which the database contains elliptic curves, the numbers of curves and {{KNOWL('ec.isogeny', 'isogeny classes')}}, and the bounds on the conductor norms in each case, see [this page](http://www.lmfdb.org/EllipticCurve/browse).
\end{definition}


