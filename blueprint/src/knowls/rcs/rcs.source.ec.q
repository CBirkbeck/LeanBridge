\subsection{\href{https://beta.lmfdb.org/knowledge/show/rcs.source.ec.q}{Source of elliptic curve data over $\Q$}}
\begin{definition}\label{rcs.source.ec.q}
\uses{ec.complex_multiplication,ec.conductor,ec.galois_rep,ec.isogeny,ec.iwasawa_invariants,ec.q.integral_points,ec.q.serre_invariants,ec.q.torsion_growth,ec.rank,lfunction}
The elliptic curves over $\Q$ in the LMFDB come from three sources:

\begin{itemize}
\item  Complete lists of elliptic curves defined over $\Q$ for a given \hyperref[ec.conductor]{conductor} $N$ were computed for $N\le500000$ by John Cremona using the modular symbols method described in \cite{href{http://homepages.warwick.ac.uk/~masgaj/book/fulltext/index.html}{Cremona97}, MR1628193}, as implemented in his eclib package \cite{doi:10.5281/zenodo.29671}.
\item  For conductors only divisible by primes $p\le7$, complete lists of curves were computed by Benjamin Matschke and Rafael von
\end{itemize}
K\"anel by solving appropriate Mordell equations \cite{arxiv:1605.06079}, and independently by Michael Bennett, Adela Gherga, and Andrew Rechnitzer \cite{href{https://www.ams.org/journals/mcom/2019-88-317/S0025-5718-2018-03370-1/}{BGR2019}}.
\begin{itemize}
\item  For prime conductors, extensive but incomplete lists of curves were computed by William Stein and Mark Watkins as part of the Stein-Watkins database \cite{href{http://modular.math.washington.edu/papers/stein-watkins/}{SW2002}}.  Independently, complete lists were computed by Bennett, Gherga and Rechnitzer \cite{href{https://www.ams.org/journals/mcom/2019-88-317/S0025-5718-2018-03370-1/}{BGR2019}}, both extending the range of the Stein-Watkins table and including curves omitted there.
\end{itemize}

The additional data for each curve and \hyperref[ec.isogeny]{isogeny} class was also computed by John Cremona using a combination of eclib, Magma, SageMath, and Pari/GP unless otherwise
specified.

\begin{itemize}
\item   Isogeny classes were computed using with eclib or Sage, which uses
\end{itemize}
methods of Cremona, Tsukazaki and Watkins to compute isogenies of
prime degree.
\begin{itemize}
\item   The ranks and generators were mostly computed using
\end{itemize}
mwrank (part of eclib), with larger generators of \hyperref[ec.rank]{rank} 1 curves
computed using either Pari/GP's ellheegner function (implemented by
Bill Allombert using his enhancements of the algorithm developed by
John Cremona, Christophe Delaunay and Mark Watkins) or Magma's
HeegnerPoint function (implemented by Steve Donnelly and Mark Watkins,
based on the same method).
\begin{itemize}
\item  \hyperref[ec.q.integral_points]{Integral points} were computed using both the
\end{itemize}
Sage implementation of the method based on bounds on elliptic
logarithms and LLL-reduction, implemented by John Cremona with Michael
Mardaus and Tobias Nagell, and also the Magma implementation of Steve Donnelly (which uses some additional unpublished ideas)
\begin{itemize}
\item  Modular degrees were computed using Mark Watkins's sympow library via Sage.
\item  Special values of the \hyperref[lfunction]{L-function} were computed by Pari/GP via Sage.
\item  The graphs of the real locus were computed using David Roe's function implemented in Sage.
\item  \hyperref[ec.iwasawa_invariants]{Iwasawa invariants} were computed by Robert Pollack.
\item  \hyperref[ec.q.torsion_growth]{Torsion growth} data was computed by Enrique Gonz&aacute;lez Jim\'e;nez and Filip Najman.
\item  \hyperref[ec.galois_rep]{mod-$\ell$ Galois image} data was computed by Andrew Sutherland using the methods of
\end{itemize}
\cite{doi:10.1017/fms.2015.33,arXiv:1504.07618} (including a generalization to handle curves with \hyperref[ec.complex_multiplication]{complex multiplication}).
\begin{itemize}
\item  \hyperref[ec.galois_rep]{2-adic Galois image} data was computed using Jeremy Rouse's Magma implementation of the algorithm of Rouse and Zureick-Brown \cite{doi:10.1007/s40993-015-0013-7,arXiv:1402.5997}.
\item  \hyperref[ec.galois_rep]{$\ell$-adic Galois image} data was computed using the algorithm of Rouse, Sutherland, and Zureick-Brown \cite{doi:10.1017/fms.2022.38arXiv:2106.11141} ([GitHub repository](https://github.com/AndrewVSutherland/ell-adic-galois-images)).
\item  \hyperref[ec.galois_rep]{adelic Galois image} data was computed using Zywina's algorithm \cite{arXiv:2206.14959} ([GitHub repository](https://github.com/davidzywina/OpenImage)).
\item  \hyperref[ec.q.serre_invariants]{Serre invariants} were computed using Samuele Anni's implementation of Kraus' algorithm \cite{mr:1446614}.
\end{itemize}



\end{definition}


