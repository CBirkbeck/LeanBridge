\subsection{\href{https://beta.lmfdb.org/knowledge/show/rcs.rigor.lfunction.ec}{Reliability of Elliptic Curve L-function Data}}
\begin{definition}\label{rcs.rigor.lfunction.ec}
\uses{ec,ec.rank,lfunction.analytic_rank,lfunction.zeros}
L-functions of \hyperref[ec]{elliptic curves} over $\Q$ in the database have been precomputed using heuristic precision bounds that should (but are not guaranteed to) ensure that all \hyperref[lfunction.zeros]{zeros} and special values are accurate to the displayed precision (up to an error in the last digit), and that the list of zeros is complete (within the region covered by the list, including the \hyperref[lfunction.zeros]{lowest zero}).

For L-functions of elliptic curves over $\Q$ the displayed \hyperref[lfunction.analytic_rank]{analytic rank} is known to be correct in all but one case, the L-function of the elliptic curve $\texttt{234446.a1}$, which is the unique curve of  \hyperref[ec.rank]{Mordell-Weil rank} 4 in the database.  For this L-function the analytic rank is known to be either 2 or 4.

\end{definition}


