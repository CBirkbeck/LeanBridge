\subsection{Reliability of elliptic curve data over $\Q$}
\begin{definition}\label{rcs.rigor.ec.q}
\uses{ag.mordell_weil,character.dirichlet.principal,cmf,cmf.character,cmf.fouriercoefficients,cmf.level,cmf.weight,ec,ec.analytic_sha_order,ec.complex_multiplication,ec.galois_rep,ec.isogeny,ec.iwasawa_invariants,ec.local_data,ec.mordell_weil_group,ec.q.bsdconjecture,ec.q.conductor,ec.q.cremona_label,ec.q.integral_points,ec.q.manin_constant,ec.q.optimal,ec.q.real_period,ec.q.regulator,ec.q.torsion_growth,ec.q.torsion_subgroup,ec.rank,group.element_order,group.generators}
### Completeness of the  collection

All {{ KNOWL('ec', 'elliptic curves') }} defined over \(\mathbb{Q}\) are known to be modular, and hence arise (up to isogeny)  via the Eichler-Shimura construction from {{KNOWL('cmf', 'classical modular forms')}} of {{KNOWL('cmf.weight', 'weight')}} \(2\), {{KNOWL('character.dirichlet.principal', 'trivial')}} {{KNOWL('cmf.character', 'character')}}, {{KNOWL('cmf.level', 'level')}} \(N\) equal to the {{KNOWL('ec.q.conductor', 'conductor')}} of the curve, and having rational {{KNOWL('cmf.fouriercoefficients', 'Fourier coefficients')}}.  

<ul>
<li>
For conductors less than 500000, where modular symbol methods were used to determine the curves (see \cite{href{https://johncremona.github.io/book/fulltext/index.html}{Cremona97}}), the reliability of the completeness of the data thus relies on the rigour and correct implementation of the modular symbol algorithms used to compute them, together with the correctness of the algorithms used to compute complete {{KNOWL('ec.isogeny', 'isogeny classes')}} from any one elliptic curve.  
<li>
For smooth conductors, completeness relies on the work of Matschke and Von Kahnel \cite{arxiv:1605.06079} and Matschke and Best \cite{arxiv:2007.10535}.  
<li>
For prime conductors, completeness relies on the work of Bennett, Gherga and Rechnitzer \cite{href{https://www.ams.org/journals/mcom/2019-88-317/S0025-5718-2018-03370-1/}{BGR2019}}.
</ul>
### Individual curve data

####Equation
The \(c_4\) and \(c_6\)-invariants of the {{KNOWL('ec.q.optimal', 'optimal')}} curve in each isogeny class were computed from numerical approximations obtained using modular symbols.  See J. E. Cremona [Algorithms for modular elliptic curves](http://homepages.warwick.ac.uk/staff/J.E.Cremona/book/amec.html), 2nd edn., Cambridge 1997.

For additional justification that the equations obtained are rigorously correct, see J. E. Cremona, Appendix to a paper by Amod Agashe, Ken Ribet and William Stein:  *The {{KNOWL('ec.q.manin_constant', 'Manin Constant')}}*, Pure and Applied Mathematics Quarterly, Vol. 2 no.2 (2006), pp. 617-636, supplemented for conductors over $130000$ by [updated notes](https://raw.githubusercontent.com/JohnCremona/ecdata/master/doc/manin.txt).  Note  that for conductors greater than $270000$ we have not always identified the optimal curve in each class rigorously, but expect that it is always the curve whose {{KNOWL('ec.q.cremona_label', 'Cremona label')}} number is 1.

####{{KNOWL('ec.q.conductor', 'Conductor')}} , {{KNOWL('ec.local_data', 'local data')}} and basic invariants
These are rigorously computed.

####{{KNOWL('ec.mordell_weil_group', 'Mordell-Weil group')}} and {{KNOWL('group.generators', 'generators')}}, and {{ KNOWL('ec.q.bsdconjecture', 'BSD invariants') }}
The analytic {{KNOWL('ec.rank', 'rank')}} \(r_{an}\) is computed using modular symbols and is rigorous for \(r_{an}\le3\) and {{KNOWL('ec.q.conductor', 'conductor')}} \(N\le500000\).  When \(r_{an}\le1\), it is a theorem that \(r_{an}\) equals the {{KNOWL('ag.mordell_weil', 'Mordell-Weil rank')}} \(r\) of the curve.  When \(r=1\) the generator is obtained from <tt>mwrank</tt> or using Heegner points.  When \(r_{an}\ge2\), the Mordell-Weil rank and generators are obtained from <tt>mwrank</tt>.  The {{KNOWL('ec.q.torsion_subgroup', 'torsion subgroup')}} and generators are obtained using standard rigorous algorithms, based on Mazur's classification.  When \(r_{an}\ge4\) we cannot compute the exact value, and when we claim that \(r_{an}=4\) we only know rigorously that \(r_{an}\in\{2,4\}\).

The heights of generators of infinite {{KNOWL('group.element_order', 'order')}} are given approximately; currently we do not guarantee the precision.  Similarly for the {{KNOWL('ec.q.regulator', 'regulator')}}, the {{KNOWL('ec.q.real_period', 'real period')}} and the special L-value. The {{KNOWL('ec.analytic_sha_order', 'analytic order of &#1064;')}} was computed exactly for curves of rank $0$, where the quotient of the special L-value \(L(E,1)\) and the real period is a positive rational number, that was computed using modular symbols for curves with {{KNOWL('ec.q.conductor', 'conductor')}} \(N\le500000\) and using a rigorous algorithm of William Stein for larger conductors.  For curves of positive rank the analytic order of &#1064; was computed approximately and rounded.  Note that for rank $1$ curves, while it is possible in principal to compute the analytic order of &#1064; exactly, this has only been done for conductors less than $5000$.  For curves of rank greater than 1, the quantity predicted by the {{ KNOWL('ec.q.bsdconjecture', 'BSD conjecture') }} to be the order of &#1064; is not even known to be rational and can only be computed as a floating point approximation.

####{{KNOWL('ec.q.integral_points', 'Integral points')}}
These were computed rigorously, using independent implementations in Magma and SageMath which were compared as a consistency check.

####{{KNOWL('ec.galois_rep', 'Galois representations')}}
The images of the mod-$\ell$ and $\ell$-adic Galois representations were computed rigorously.  In particular, for the mod-$\ell$ representations a variant of Sutherland's algorithm \cite{doi:10.1017/fms.2015.33,arxiv:1504.07618} was used to rigorously compute the image of the mod-$\ell$ representation for all primes $\ell<1000$, and for elliptic curves over $\Q$ without {{KNOWL('ec.complex_multiplication','complex multiplication')}} Zywina's algorithm \cite{arxiv:1508.07661} was used to verify the surjectivity of the mod $\ell$ representation for all primes $\ell \ge 1000$.

####{{KNOWL('ec.iwasawa_invariants','Iwasawa invariants')}}
These were computed rigorously.

####{{KNOWL('ec.q.torsion_growth', 'Torsion growth')}}
The torsion growth data was computed rigorously.
\end{definition}


