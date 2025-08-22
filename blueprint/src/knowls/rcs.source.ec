\subsection{Source of elliptic curve data}
\begin{definition}\label{rcs.source.ec}
\uses{ag.base_field,ec,ec.base_change,ec.complex_multiplication,ec.global_minimal_model,ec.good_reduction,ec.invariants,ec.isogeny,ec.local_data,group.generators,mf.bianchi.weight,mf.bianchi.weight2,mf.hilbert,nf.abs_discriminant,nf.class_number,nf.discriminant,nf.prime,nf.totally_real}
## Source of the curves

The elliptic curves over number fields other than $\Q$ come from several sources.

### Imaginary quadratic fields
The curves defined over the first five (Euclidean) imaginary quadratic fields of class number one include the curves in John Cremona's 1981 thesis, extended by him with Warren Moore in 2014 and subsequently.   In 2021-2022 the other fields of class number one were included; for the fields of {{KNOWL('nf.discriminant', 'discriminant')}} $-19$, $-43$, $-67$ (of class number $1$), some of the curves appeared first in Elise Whitley's [1990 PhD thesis](https://ore.exeter.ac.uk/repository/handle/10871/8427).  Also in 2021-2024, curves defined over all fields of {{KNOWL('nf.abs_discriminant', 'absolute discriminant')}} up to \(700\) were included, with conductor norm less than some bound depending on the field.

For the field of {{KNOWL('nf.discriminant', 'discriminant')}} $-20$ (of class number $2$), some of the curves appeared first in Jeremy Bygott's [1999 PhD thesis](https://ore.exeter.ac.uk/repository/handle/10871/8322);  for the fields of {{KNOWL('nf.discriminant', 'discriminant')}} $-23$ and $-31$ (of class number $3$), some of the curves appeared first in Mark Lingham's [2005 PhD thesis](http://eprints.nottingham.ac.uk/10138/).  In all cases, curves were found to match almost all the {{KNOWL('mf.bianchi.weight2', 'cuspidal')}} Bianchi newforms (with trivial character, {{KNOWL('mf.bianchi.weight', 'weight')}} \(2\) and rational coefficients) in the database, originally using custom code by Cremona and Moore, but with the vast majority found by Magma's <tt>EllipticCurveSearch</tt> function written by Steve Donnelly; in some of the remaining cases it has been proved that there is no matching curve.

Additionally, for the fields with class number \(1\), curves with CM by the field in question, which are not associated to cuspidal Bianchi newforms, were found from their $j$-invariants by Cremona.  

### {{KNOWL('nf.totally_real', 'Totally real')}} fields
Over $\Q(\sqrt{5})$ the curves of {{KNOWL('ec.invariants', 'conductor norm')}} up to about $5000$ were provided by Alyson Deines from joint work of Jonathan Bober, Alyson Deines, Ariah Klages-Mundt, Benjamin LeVeque, R. Andrew Ohana, Ashwath Rabindranath, Paul Sharaba and William Stein (see [http://arxiv.org/abs/1202.6612](http://arxiv.org/abs/1202.6612)).  All the other curves were found from their associated Hilbert newforms using Magma's <tt>EllipticCurveSearch</tt> function, using a script written by John Cremona.  Hence the extent of the data matches that of the {{KNOWL('mf.hilbert', 'Hilbert Modular Form')}} data for totally real fields of degrees 2, 3, 4, 5 and 6.

### Other fields
- Steve Donnelly, Paul E. Gunnells, Ariah Klages-Mundt, and Dan Yasaki provided the curves over the mixed cubic field 3.1.23.1.
- Marc Masdeu provided $\Q$-curves over quadratic fields.
- Haluk Sengun provided curves with everywhere {{KNOWL('ec.good_reduction', 'good reduction')}} over imaginary quadratic fields.
- S. Yokoyama and Masdeu provided curves with everywhere good reduction over real quadratic fields (see  [here](http://www2.math.kyushu-u.ac.jp/~s-yokoyama/ECtable.html)).

In some cases the same curve occurs in more than one of the above sources, in which case efforts have been made not to include it more than once in the database.

## Source of the data for each curve

### Models
For each curve, the model in the database is a {{KNOWL('ec.global_minimal_model', 'global minimal model')}} where one exists (for example when the {{KNOWL('ag.base_field', 'base field')}} has {{KNOWL('nf.class_number', 'class number')}} one), and otherwise a semi-minimal model which is nonminimal at precisely one {{KNOWL('nf.prime', 'prime')}}.  These (semi-)minimal models we computed in SageMath using code written by John Cremona.  Among all (semi-)minimal models we scale by units in order to minimize the archimedean embeddings of \(c_4\) and \(c_4\) simultaneously using a lattice basis reduction method, also implemented in SageMath by John Cremona.

### {{KNOWL('ec.local_data', 'Local data')}}
Conductors and local reduction data were computed using Tate's Algorithm, as implemented in SageMath by John Cremona, except for the local root numbers which were computed using Tim Dokchitser's implementation in Magma.

### Isogenies
Complete {{KNOWL('ec.isogeny', 'isogeny classes')}} were computed using implementations in SageMath by John Cremona and Ciaran Schembri of Billerey's algorithm (to determine the reducible primes) and Kohel-V&eacute;lu formulas.

### Mordell-Weil groups and {{KNOWL('group.generators', 'generators')}} and Birch--Swinnerton-Dyer data
These were computed by John Cremona using Magma's <tt>MordellWeilShaInformation</tt> and <tt>AnalyticRank</tt> functions, implemented by Steve Donnelly and Mark Watkins;  the special L-values were in some cases computed using the pari library.

### Galois representations
The images of mod-\(\ell\) Galois representations were computed using Andrew Sutherland's Magma implemention of his methods described in \cite{doi:10.1017/fms.2015.33,arxiv:1504.07618} (including a generalization to handle curves with {{KNOWL('ec.complex_multiplication','complex multiplication')}}).

### {{KNOWL('ec.base_change', 'Base change')}} and \(\mathbb{Q}\)-curves
The property of being the base change of an {{KNOWL('ec', 'elliptic curve')}} over \(\mathbb{Q}\) and of being a \(\mathbb{Q}\)-curve were computed by John Cremona using his implementation in SageMath of the algorithm described in \cite{doi:10.1007/s40993-021-00270-0,  arxiv:2004.10054}.
\end{definition}


