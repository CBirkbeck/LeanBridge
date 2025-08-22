\subsection{Completeness and extent of global number field data}
\begin{definition}\label{rcs.cande.nf}
\uses{gg.tnumber,nf.degree,nf.root_discriminant}
<p>
 The PARI database contains complete lists of fields with the absolute
 discriminant $|D|$ less than given bounds, and was compiled from the
 work of several authors.  Fields from Voight extend these lists in cases
 where the number of complex places is \(0\) or \(1\).  In other cases, the
 bounds have been extended by Jones and Roberts.  The bounds for octics
 come from results of Diaz y Diaz and Battistoni and those for nonics are due to Battistoni.
<p>
<table>
{% set row_class = cycler("odd", "even") %}
<tr>
<th>degree</th>
<th>signature(s)</th>
<th>absolute discriminant bound</th>
</tr>
<tr class="{{ row_class.next() }}"><td>1<td align="center">[1,0]<td>\(1\)</tr>
<tr class="{{ row_class.next() }}"><td>2<td align="center">all<td>\(2\cdot 10^6\)</tr>
<tr class="{{ row_class.next() }}"><td>3<td align="center">all<td>\(3{,}375{,}000\)</tr>
<tr class="{{ row_class.next() }}"><td>4<td align="center">[4,0]<td>\(10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>4<td align="center">[2,1]<td>\(4\cdot 10^6\)</tr>
<tr class="{{ row_class.next() }}"><td>4<td align="center">[0,2]<td>\(4\cdot 10^6\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td align="center">[5,0]<td>\(10^8\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td align="center">[3,1]<td>\(1.2\cdot10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td align="center">[1,2]<td>\(1.2\cdot10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>6<td align="center">[6,0]<td>\(481{,}890{,}304\)</tr>
<tr class="{{ row_class.next() }}"><td>6<td align="center">[4,1]<td>\(10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>6<td align="center">[2,2]<td>\(10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>6<td align="center">[0,3]<td>\(10^7\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td align="center">[7,0]<td>\(214{,}942{,}297\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td align="center">[5,1]<td>\(2\cdot 10^8\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td align="center">[3,2]<td>\(2\cdot 10^8\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td align="center">[1,3]<td>\(2\cdot10^8\)</tr>

<tr class="{{ row_class.next() }}"><td>8<td align="center">[6,1]<td>\(79{,}259{,}702\)</tr>
<tr class="{{ row_class.next() }}"><td>8<td align="center">[4,2]<td>\(20{,}829{,}049\)</tr>
<tr class="{{ row_class.next() }}"><td>8<td align="center">[2,3]<td>\(5{,}726{,}300\)</tr>
<tr class="{{ row_class.next() }}"><td>8<td align="center">[0,4]<td>\(1{,}656{,}109\)</tr>

<tr class="{{ row_class.next() }}"><td>9<td align="center">[3,3]<td>\(146{,}723{,}910\)</tr>
<tr class="{{ row_class.next() }}"><td>9<td align="center">[1,4]<td>\(39{,}657{,}561\)</tr>
</table>
</p>

<p>For fields computed by Jones and Roberts, the  number fields in the LMFDB are complete in the following cases.
The {{KNOWL('nf.degree', 'degree')}} of a field is given by \(n\).
</p>
<p>
<table>
{% set row_class = cycler("odd", "even") %}
<tr class="{{ row_class.next() }}"><td>Degree $2$ fields unramified outside \(\{2,3,5,7,11,13,17,19,23,29\}\)
<tr class="{{ row_class.next() }}"><td>Degree $3$ fields unramified outside \(\{2,3,5,7,11,13,17,19,23,29\}\)
<tr class="{{ row_class.next() }}"><td>Degree $4$ fields unramified outside \(\{2,3,5,7,11,13\}\)
<tr class="{{ row_class.next() }}"><td>Degree $5$ fields unramified outside \(\{2,3,5,7\}\)
<tr class="{{ row_class.next() }}"><td>Fields unramified outside \(\{2,3\}\)
 with \(n\leq 7\)
</tr>
<tr class="{{ row_class.next() }}"><td>Fields ramified at only one prime \(p\) with \(p<102\) with \(n\leq 7\) </tr>
<tr class="{{ row_class.next() }}"><td>Fields ramified at only two primes \(p\lt q \lt 500\) with \(n\leq 4\) </tr>
<tr class="{{ row_class.next() }}"><td>Fields ramified at only two primes \(p\lt q \leq 5\) with \(5\leq n\leq 7\) </tr>
<tr class="{{ row_class.next() }}"><td>Fields ramified at only three primes \(p\lt q \lt r \lt 100\) with \(n\leq 4\) </tr>
<tr class="{{ row_class.next() }}"><td>All abelian fields of degree $\leq 47$ and conductor $\leq 1000$ </tr>
<tr class="{{ row_class.next() }}"><td>Degree $8$ fields with Galois group $Q_8$ which are unramified outside of $\{2,3,5,7,11,13,17,19,23\}$
</table>
</p>
<p>
For the remaining cases, the bound depends on the Galois group.  Galois groups
are given by {{KNOWL('gg.tnumber', '\(t\)-number')}}.
The bound \(B\) is for the
{{KNOWL('nf.root_discriminant', 'root discriminant')}}.
</p>
<p>
<table>
<tr valign="top">
 <td>
<table>
{% set row_class = cycler("odd", "even") %}
<tr> <th colspan="2">Degree 7</th></tr>
<tr>
<th>\(t\)</th>
<th>\(B\)</th>
</tr>
<tr class="{{ row_class.next() }}"><td>3<td>\(26\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td>\(38\)</tr>
  </table>
 </td>
 <td>
  <table>
{% set row_class = cycler("odd", "even") %}
<tr> <th colspan="2">Degree 8</th></tr>
<tr>
<th>\(t\)</th>
<th>\(B\)</th>
</tr>
<tr class="{{ row_class.next() }}"><td>3<td>\(20\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td>\(512\)</tr>
<tr class="{{ row_class.next() }}"><td>15<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>18<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>22<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>26<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>29<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>32<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>34<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>36<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>39<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>41<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>45<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>46<td>\(15\)</tr>
  </table>
 </td>
 <td>
  <table>
{% set row_class = cycler("odd", "even") %}
<tr> <th colspan="2">Degree 9</th></tr>
<tr>
<th>\(t\)</th>
<th>\(B\)</th>
</tr>
<tr class="{{ row_class.next() }}"><td>2<td>\(20\)</tr>
<tr class="{{ row_class.next() }}"><td>5<td>\(20\)</tr>
<tr class="{{ row_class.next() }}"><td>6<td>\(20\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td>\(30\)</tr>
<tr class="{{ row_class.next() }}"><td>7<td>\(30\)</tr>
<tr class="{{ row_class.next() }}"><td>8<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>12<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>13<td>\(12\)</tr>
<tr class="{{ row_class.next() }}"><td>14<td>\(18\)</tr>
<tr class="{{ row_class.next() }}"><td>15<td>\(18\)</tr>
<tr class="{{ row_class.next() }}"><td>16<td>\(12\)</tr>
<tr class="{{ row_class.next() }}"><td>17<td>\(18\)</tr>
<tr class="{{ row_class.next() }}"><td>18<td>\(12\)</tr>
<tr class="{{ row_class.next() }}"><td>19<td>\(18\)</tr>
<tr class="{{ row_class.next() }}"><td>21<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>23<td>\(17\)</tr>
<tr class="{{ row_class.next() }}"><td>24<td>\(12\)</tr>
<tr class="{{ row_class.next() }}"><td>25<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>26<td>\(15\)</tr>
<tr class="{{ row_class.next() }}"><td>29<td>\(10\)</tr>
<tr class="{{ row_class.next() }}"><td>30<td>\(10\)</tr>
<tr class="{{ row_class.next() }}"><td>31<td>\(10\)</tr>
</table>
</td>
</tr>
</table>

<p>Selected fields from the Kl&uuml;ners-Malle database, plus the work of others for the Galois group 17T7,
provide examples of fields with many different Galois groups.  As
a result, the LMFDB contains at least one field for each
Galois group (transitive subgroup of $S_n$ up to conjugation)
which in degree $n<20$.
</ul>

\end{definition}


