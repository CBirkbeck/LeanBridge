\subsection{\href{https://beta.lmfdb.org/knowledge/show/rcs.rigor.ec}{Reliability of elliptic curve data}}
\begin{definition}\label{rcs.rigor.ec}
\uses{ec,ec.analytic_sha_order,ec.bsdconjecture,ec.canonical_height,ec.invariants,ec.period,ec.regulator,g2c.hasse_weil_conjecture,lfunction,lfunction.analytic_rank,lfunction.leading_coeff,nf,nf.class_number,nf.degree,nf.totally_real}
The reliability of the completeness claims for the \hyperref[ec]{elliptic curves} over each \hyperref[nf]{number field} represented in the database depends on the field and the current status of modularity of elliptic curves over the field in question.  Over all \hyperref[nf.totally_real]{totally real} fields of \hyperref[nf.degree]{degree} \(2\) and \(3\), and most of degree $4$,  it is known that all elliptic curves are modular (see \cite{doi:10.1007/s00222-014-0550-z}
 for degree $2$, \cite{arxiv:1901.03436} for degree $3$ and \cite{doi: https://doi.org/10.1090/tran/8557} for degree $4$) and hence the database contains all curves of \hyperref[ec.invariants]{conductor norm} up to the bound for that field.  Over other fields we can only say that the database contains all *modular* elliptic curves within this range.  Over totally real fields of degrees $4$, $5$ and $6$ all the curves in the database have been proved to be modular, using the criteria of \cite{doi:10.1007/s00222-014-0550-z}, and over imaginary quadratic fields of \hyperref[nf.class_number]{class number} $1$, all the curves in the database have also been proved to be modular using the $2$-adic Faltings-Serre method or its $3$-adic analogue.

All the data for each individual elliptic curve has been computed rigorously with no unproved conjectures or assumptions being used, except for some of the \hyperref[ec.bsdconjecture]{BSD invariants}:

\begin{itemize}
\item  the \hyperref[lfunction.analytic_rank]{analytic rank} and \hyperref[lfunction.leading_coeff]{special L-value} were computed using either the Magma function <tt>AnalyticRank()</tt>, which assumes that the \hyperref[lfunction]{L-function} satisfies the \hyperref[g2c.hasse_weil_conjecture]{Hasse-Weil conjecture} and computes successive derivatives at the critial point to a fixed precision until it finds a non-zero value; or using the pari library's <tt>lfun</tt> function.  This assumption on the Hasse-Weil conjecture is satisfied by all the elliptic curves in the database which are known to be modular.
\item  the \hyperref[ec.analytic_sha_order]{analytic order of $\Sha$} was in all cases computed approximately from its definition, given by the \hyperref[ec.bsdconjecture]{BSD formula}, and rounded to the nearest integer; in all cases this is a positive integer square. 
\item  the \hyperref[ec.canonical_height]{heights} of generators, \hyperref[ec.regulator]{regulators}, and \hyperref[ec.period]{periods} have been computed to 128-bit precision in all cases (with the \hyperref[ec.regulator]{regulator} being exactly 1 for curves of rank 0).
\item   the \hyperref[lfunction.leading_coeff]{special L-value} and \hyperref[ec.analytic_sha_order]{analytic order of $\Sha$} have been computed to the same precision over fields of degree 2 and 3, and to lower precision over fields of higher degree.
\end{itemize}
\end{definition}


