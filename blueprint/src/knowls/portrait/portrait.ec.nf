\subsection{\href{https://beta.lmfdb.org/knowledge/show/portrait.ec.nf}{Pictures for elliptic curves over number fields}}
\begin{definition}\label{portrait.ec.nf}
\uses{ec,nf,nf.complex_embedding,nf.real_embedding,nf.totally_imaginary}
\leanok
For each \hyperref[ec]{elliptic curve}  $E$ over a \hyperref[nf]{number field} $K$, the plot displayed consists of the graphs of the real points of $E$ with respect to each \hyperref[nf.real_embedding]{real embedding} of $K$.   \hyperref[nf.complex_embedding]{Complex embeddings} of $K$ are ignored, so for example there is no plot shown when $K$ is a \hyperref[nf.totally_imaginary]{totally complex} field such as an imaginary quadratic field.

The plots are produced using SageMath, which uses plotting logic designed by David Roe to determine which subset of $E(\mathbb{R})$ in the real affine plane to include in the plot.
\end{definition}


