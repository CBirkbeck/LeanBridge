\subsection{\href{https://beta.lmfdb.org/knowledge/show/ec.ring}{Elliptic curve over a ring}}
\begin{definition}\label{ec.ring}
\uses{ec,ec.good_reduction,ec.scheme,ring}
An \textbf{elliptic curve} over a \hyperref[ring]{commutative ring} $R$ is an \hyperref[ec.scheme]{elliptic scheme} $E \to \operatorname{Spec} R$.

For example, an elliptic curve over $\Z[1/N]$ is the same as an \hyperref[ec]{elliptic curve} over $\Q$ with \hyperref[ec.good_reduction]{good reduction} at all primes not dividing $N$.  (More precisely, the latter is the generic fiber of the former.)
\end{definition}
