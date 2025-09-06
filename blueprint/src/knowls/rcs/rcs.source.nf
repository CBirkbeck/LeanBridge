\subsection{\href{https://beta.lmfdb.org/knowledge/show/rcs.source.nf}{Source of global number field data}}
\begin{definition*}\label{rcs.source.nf}
\uses{nf.elkies}
Number fields were drawn from the following sources.
<ul>
<li>The PARI database from the Bordeaux PARI group \cite{href{https://pari.math.u-bordeaux.fr/pub/numberfields/}{pari.math.u-bordeaux.fr/pub/numberfields/}}, which in turn, was a combination of work by several authors:
 <ul>
 <li> M. Olivier for degree 3 fields;
 <li> J. Buchmann, D. Ford, and M. Pohst for degree 4 fields \cite{MR:1176706};
 <li> A. Schwarz, M. Pohst, and F. Diaz y Diaz for degree 5 fields \cite{MR:1219705};
 <li> M. Olivier for degree 6 fields \cite{MR:1106977}, \cite{MR:1149805}, \cite{MR:1116107}, \cite{MR:1096589}, \cite{MR:1061760}, \cite{MR:1050276}, and with A.-M. Berg\'e; and J. Martinet \cite{MR:1011438};
 <li> P. L\'e;tard for degree 7 fields.
</ul>
<li>Totally real fields of degrees from 6 to 10 computed by
  John Voight \cite{arXiv:0802.0194, href{https://math.dartmouth.edu/~jvoight/nf-tables/index.html}{math.dartmouth.edu/~jvoight/nf-tables/index.html}}.
<li>Almost totally real fields computed by John Voight. \cite{arXiv:1408.2001,MR:3384884}.
<li>Octic and nonic fields of small discriminant from Francesco Battistoni \cite{MR3912944,MR4174280}
<li>Fields from John Jones-David Roberts database. \cite{arXiv:1404.0266,MR:3356048,href{https://hobbes.la.asu.edu/NFDB}{hobbes.la.asu.edu/NFDB}}.
<li>Fields from J&uuml;rgen Kl&uuml;ners-Gunter Malle database. \cite{arXiv:math/0102232,href{http://galoisdb.math.upb.de/}{galoisdb.math.upb.de/}}.
<li>Fields of degrees 2 and 3 unramified outside {2,3,5,...,29} from Benjamin Matschke.
<li> Octic fields with Galois group $Q_8$ from Fabian Gundlach.
<li>\hyperref[nf.elkies]{Some fields} from Noam Elkies.
<li>Fields from Johan Bosman \cite{arXiv:1109.6879}
<li>Fields which have arisen because they are connected to other objects in the LMFDB.
</ul>

Complete lists of global number fields were computed using two techniques, Hunter searches (see Section 9.3 of \cite{MR:1728313,doi:10.1007/978-1-4419-8489-0}) and class field theory (see Chapter 5 and Section 9.2 of \cite{MR:1728313,doi:10.1007/978-1-4419-8489-0}). Hunter searches are named for named for John Hunter \cite{MR:0091309}, whose technique was refined significantly by M. Pohst \cite{MR:0644904}. In some cases, the Hunter searches are "targeted" in that they focused on specific prime ramification \cite{MR:1986816,doi:10.1090/S0025-5718-03-01510-2}.

Class groups of imaginary quadratic fields with $|D|<2^{40}$ were computed by A. Mosunov and M. J. Jacobson, Jr. \cite{MR:3471116,doi:10.1090/mcom3050}.

Data on whether or not a field is monogenic, its index, and its inessential primes were computed using pair-gp and are based on Ga&aacute;l \cite{MR:1896601}, Gras \cite{MR:0846964}, &Sacute;liwa \cite{MR:0678997}, Nart \cite{MR:0779058}, Mushtaq et. al. \cite{MR:3844199}, and a classical theorem of Dedekind.

\end{definition*}


