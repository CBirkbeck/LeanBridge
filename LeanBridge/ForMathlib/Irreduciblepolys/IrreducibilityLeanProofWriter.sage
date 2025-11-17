#!/usr/bin/env python
# coding: utf-8

# In[ ]:


## LEAN PROOF GENERATOR FOR IRREDUCIBILITY OF POLYNOMIALS


# In[115]:


# SQUARE AND MULTIPLY MOD f

# Efficiently computes t ^ p mod f using the square-and multiply algorithm
# and outputs the intermediate steps.

# Input :
# t : the starting value
# f : a polynomial used for reduction (modulus)
# p : the exponent

# Output:
# hp : list with values of t ^ i mod f in the partial steps of the exponentiation algorithm.
# gp : list with polynomials certifying the reduction in each intermediate step.

from io import StringIO

def sqpow(t, f, p) :
    s = p.bit_length() - 1
    binary_list = [int(bit) for bit in bin(p)[2:]]
    bit = binary_list[::-1]
    hp = [0 for i in range(s)] + [t]
    gp = [0 for i in range(s)]
    for i in range(s-1,-1,-1):
        gp[i], hp[i] = (hp[i+1] ^ 2 * t^(bit[i])).quo_rem(f)
    return hp, gp


# In[116]:


# Generates a certificate of irreducibility for a polynomial f mod p (based on Rabin's test)
# as a term of type CertificateIrreducibleZModList (with t = 2) in our Lean formalization.
# This does not require factoring the degree of f.

# Input:
# f : a polynomial over F_p
# p : the prime
# N : a label for naming the term. The resulting term in named PpPN
# doc : the file where the Lean code is written.


def CertificateIrrModpF (f, p, N, doc):
    R.<X>= PolynomialRing(GF(p))
    s = p.bit_length() - 1
    binary_list = [int(bit) for bit in bin(p)[2:]]
    bit = binary_list[::-1]
    n = f.degree()

    if n == 1:
        h = [X,X]
        gaux = [(X^p - X)/f]
    else :
        dn = [0 for i in range(n)]
        h = [X] + [0 for i in range(n)]

        gaux = [0 for i in range(n)]
        h = [X] + [0 for i in range(n)]
        for i in range(n):
            gaux[i], h[i+1] = (h[i] ^ p).quo_rem(f)

    hprime = [[] for i in range(n)]
    gprime = [[] for i in range(n)]

    for i in range(n):
            (hp, gp) = sqpow(h[i],f,p)
            hprime[i] = hp
            gprime[i] = gp

    a = [0 for i in range(n)]
    b = [0 for i in range(n)]
    d = [0 for i in range(n)]

    for m in range(1,n):
        if n % m == 0:
            d[m], a[m], b[m] = xgcd(f, h[m] - X)

    h = [list(h[i]) for i in range(n + 1)]
    hprime = [[list(R(hprime[i][j])) for j in range(s+1)] for i in range(n)]
    g = [[list(R(gprime[i][j])) for j in range(s)] for i in range(n)]
    a = [list(R(a[i])) for i in range(n)]
    b = [list(R(b[i])) for i in range(n)]

    if n == 1:
        hprime[0][0] = [0,1]
        if s > 1:
            g[0][0] = []
        else :
            g[0][0] = (R((X ^ 2 * X ^ (bit[0]) - X)/f)).list()

    print(f'def P{p}P{N} : CertificateIrreducibleZModOfList {p} {n} 2 {s} {f.list()} where', file = doc)
    print(' hlen := by decide', file = doc)
    print(' htr := by decide', file = doc)
    print(f' bit := !{bit}', file = doc)
    print(' hbits := by decide', file = doc)
    print(f' h := !{h}', file = doc)
    strg = ""
    for i in range(len(g)):
        if i != len(g) -1 :
            strg = strg + '!' + str(g[i]) + ','
        else :
            strg = strg + '!' + str(g[i])
    print(' g := ![' + strg + ']', file = doc)
    strh = ""
    for i in range(len(hprime)):
        if i != len(hprime) -1 :
            strh = strh + '!' + str(hprime[i]) + ','
        else :
            strh = strh + '!' + str(hprime[i])
    print(' h\' := ![' + strh + ']', file = doc)
    print(' hs := by decide', file = doc)
    print(' hz := by decide', file = doc)
    print(' hmul := by decide', file = doc)
    print(f' a := !{a}', file = doc)
    print(f' b := !{b}', file = doc)
    print(' hhz := by decide', file = doc)
    print(' hhn := by decide', file = doc)
    print(' hgcd := by decide', file = doc)


# In[117]:


# Generates a certifcate of irreducibility for the polynomial f mod p (based on Rabin's test)
# as a term of type CertificateIrreducibleZModList' (with t = 2) in our Lean formalization.
# This does require factoring the degree of f.

# Input:
# f : a polynomial over F_p
# p : the prime
# N : a label for naming the term. The resulting term in named PpPN
# doc : the file where the Lean code is written.


def CertificateIrrModpFFP (f, p, N, doc):
    R.<X>= PolynomialRing(GF(p))
    s = p.bit_length() - 1
    binary_list = [int(bit) for bit in bin(p)[2:]]
    bit = binary_list[::-1]
    n = f.degree()
    F = factor(n)
    P = [x[0] for x in F]
    E = [x[1] for x in F]

    if n == 1:
        h = [X,X]
        gaux = [(X^p - X)/f]
    else :
        dn = [0 for i in range(n)]
        h = [X] + [0 for i in range(n)]

        gaux = [0 for i in range(n)]
        h = [X] + [0 for i in range(n)]
        for i in range(n):
            gaux[i], h[i+1] = (h[i] ^ p).quo_rem(f)

    hprime = [[] for i in range(n)]
    gprime = [[] for i in range(n)]

    for i in range(n):
            (hp, gp) = sqpow(h[i],f,p)
            hprime[i] = hp
            gprime[i] = gp

    a = [0 for i in range(n)]
    b = [0 for i in range(n)]
    d = [0 for i in range(n)]

    for x in P:
        d[n / x], a[n / x], b[n / x] = xgcd(f, h[n / x] - X)

    h = [list(h[i]) for i in range(n + 1)]
    hprime = [[list(R(hprime[i][j])) for j in range(s+1)] for i in range(n)]
    g = [[list(R(gprime[i][j])) for j in range(s)] for i in range(n)]
    a = [list(R(a[i])) for i in range(n)]
    b = [list(R(b[i])) for i in range(n)]

    if n == 1:
        hprime[0][0] = [0,1]
        if s > 1:
            g[0][0] = []
        else :
            g[0][0] = (R((X ^ 2 * X ^ (bit[0]) - X)/f)).list()

    print(f'def P{p}P{N} : CertificateIrreducibleZModOfList\' {p} {n} 2 {s} {f.list()} where', file = doc)
    print(f' m := {len(P)}', file = doc)
    print(f' P := !{P}', file = doc)
    print(f' exp := !{E} ', file = doc)
    print(' hneq := by decide', file = doc)
    print(' hP := by decide', file = doc)
    print(' hlen := by decide', file = doc)
    print(' htr := by decide', file = doc)
    print(f' bit := !{bit}', file = doc)
    print(' hbits := by decide', file = doc)
    print(f' h := !{h}', file = doc)
    strg = ""
    for i in range(len(g)):
        if i != len(g) -1 :
            strg = strg + '!' + str(g[i]) + ','
        else :
            strg = strg + '!' + str(g[i])
    print(' g := ![' + strg + ']', file = doc)
    strh = ""
    for i in range(len(hprime)):
        if i != len(hprime) -1 :
            strh = strh + '!' + str(hprime[i]) + ','
        else :
            strh = strh + '!' + str(hprime[i])
    print(' h\' := ![' + strh + ']', file = doc)
    print(' hs := by decide', file = doc)
    print(' hz := by decide', file = doc)
    print(' hmul := by decide', file = doc)
    print(f' a := !{a}', file = doc)
    print(f' b := !{b}', file = doc)
    print(' hhz := by decide', file = doc)
    print(' hhn := by decide', file = doc)
    print(' hgcd := by decide', file = doc)


# In[118]:


# Produces a list containing the irreducible factors of T mod p (in list form).

def factorLists (T,p):
    F = factor(GF(p)[x](T))
    Fp = [x for x in F]
    Fp[0] = (F.unit() * F[0][0], F[0][1])
    lF = []
    for p in Fp:
        lF = lF + p[1] * [p[0].list()]
    return lF


# In[119]:


# For a polynomial over the integers T that is shown to be irreducible by degree analysis,
# this writes a certificate in Lean, which is a term of type IrreducibleCertificateIntPolynomial
# in our formalization.

# Input:
# T : a polynomial over the integers.
# lprimes : a list of primes used for degree analysis.
# f : the file where the Lean code will be written.

def GlobalCertificateIrrF (T, lprimes, f):
    m = [len(factorLists(T,p)) for p in lprimes]
    print('noncomputable def C : IrreducibleCertificateIntPolynomial T l where', file = f)
    print(' hpol := T_ofList\'', file = f)
    print(f' n := {len(lprimes)}', file = f)
    print(f' d := {T.degree()}', file = f)
    print(' hprim := by decide', file = f)
    print(' hdeg := by decide', file = f)
    print(' hnn := by decide', file = f)
    print(' hdn := by decide', file = f)
    print(f' p := !{lprimes}', file = f)
    print(''' hp := by
  intro i
  fin_cases i''', file = f)
    for p in lprimes:
        print(f'  exact hp{p}\'.out', file = f)
    print(f' hlc := by decide', file = f)
    print(f' m := !{m}', file = f)
    print(''' F := fun i =>
  match i with ''', file = f)
    for i in range(len(lprimes)):
        print(f'  | {i} => !{factorLists(T,lprimes[i])}', file = f)
    print(''' D := fun i =>
  match i with ''', file = f)
    for i in range(len(lprimes)):
        print(f'  | {i} => !{[len(factorLists(T,lprimes[i])[j]) - 1 for j in range(m[i])]}', file = f)
    print(' hl := by decide', file = f)
    print(''' hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j''', file = f)

    for p in lprimes:
        F = factor(GF(p)[x](T))
        for i in range(len(F)):
            if F[i][0].degree() == 1:
                for j in range(F[i][1]):
                    print(f'  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) (by decide)', file = f )
            else :
                for j in range(F[i][1]):
                    print(f'  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList\' P{p}P{i}', file = f)
    print(' hm := by decide', file = f)
    print(' hprod := by decide', file = f)
    print(' hinter := by decide', file = f)


# In[120]:


# Given the polynomial T and the prime p, produces a list of the degrees of the factors of T modulo p.

def ListDegree (T , p):
    deg = T.degree()
    R.<x>=PolynomialRing(GF(p))
    d = []
    for P in factor(R(T)):
        d = d + P[1] * [P[0].degree()]
    return d


# In[121]:


# Computes the subset sums of a list l.

from itertools import combinations
def SubSums (l) :
    sub = [0]
    for i in range(1, len(l) + 1):
        combs = [list(x) for x in combinations(l, i)]
        if len(combs)>0:
            aux = [sum(c) for c in combs]
            sub = sub + aux
    return sub


# In[122]:


# Given a list of primes l, computes the intersection of the lists of subset sums of the list of degrees
# in the factorizations of T modulo those primes.

def IntersectListDegrees (T, l):
    inter = SubSums(ListDegree(T,l[0]))
    for p in l:
        inter = set(inter).intersection(set(SubSums(ListDegree(T,p))))
    return inter


# In[123]:


# Finds the best lower bound for the degree of the factors of T by looking
# at the reductions of T modulo different primes.

# Input:
# T : a polynomial with integer coefficients
# size : The size of the list of primes to consider.
# rangep : an upper bound for the primes to be considered.

#Output:

# dmin : a lower bound for the degree of a factor of T
# Cp : a list of lists of primes within the specified range that certify this lower bound.

def FindMinimalCommonDegree (T, size, rangep):
    C = []
    dmin = 1
    GPrimes = [p for p in primes(rangep) if T.leading_coefficient() % p != 0]
    for l in [list(x) for x in combinations(GPrimes, size)]:
        if min((IntersectListDegrees (T, l)) - {0}) >= dmin :
            dmin = min((IntersectListDegrees (T, l)) - {0})
            C = C + [(dmin, l)]
    Cp = []
    for x in C:
        if x[0] == dmin :
            Cp = Cp + [x[1]]
    return dmin, Cp


# In[124]:


# Given a polynomial and a list of primes l, it gives a score according to the total size of the Lean certificates
# required to certify the irreducibility of the factors of T modulo l[i].

def ScoreCertificate(T, l):
    M = 0
    for p in l:
        M = float(M + sum([i^2 for i in ListDegree(T,p)]) * log(p))
    return M


# In[125]:


# Finds the 'best' certificate (smallest score) of a given length that certifies the best
# degree bound found for T.

def BestCertificateSize (T, size, rangep) :
    M = 0
    Best = []
    dmin, C = FindMinimalCommonDegree (T, size, rangep)
    N = Infinity
    for c in C:
        M = ScoreCertificate(T, c)
        if  M < N :
            N = M
            Best = c
    return dmin, Best, N


# In[126]:


# Given an upper bound for the length of the list of primes and an upper bound for the primes, it finds
# the 'best' list of primes that certifies the biggest lower bound for the minimal degree of a factor of T.

def BestCertificate (T, ranges, rangep):
    N = Infinity
    dmin = - Infinity
    Best = []
    for i in range(1, ranges + 1):
        d, C , M = BestCertificateSize(T, i, rangep)
        if d > dmin:
            dmin = d
            N = M
            Best = C
        elif d == dmin:
            if M < N :
                N = M
                Best = C
    return dmin, Best, N


# In[127]:


# Cauchy Bound for the roots of a polynomial given scaling factor s > 0.

# Input
# l : a polynomial in list form
# s : scaling factor

# Output: the value of the (scaled) Cauchy bound.

def CauchyBoundScale(l,s):
    m = len(l)
    an = l[-1]
    aux = [abs(l[i]/an) * s^(i - (m - 1) + 1) for i in range(m - 1)]
    return (s + max(aux))


# Computes the value of s that gives the optimal Cauchy bound (in 1/4 increments).

# Input:
# l : a polynomial in list form.

# Output:
# j : the optimal scaling factor (in 1/4 increments)
# B : the cauchy bound for l calculated using this scaling factor.


def CauchyBoundScaleOpt(l):
    B = Infinity
    j = 0
    n = len(l) - 1
    an = l[-1]

    # Computes the maximum of the arguments of the minima of the piece components in the Cauchy bound.
    S = max([float((abs(l[i]/an) * (n - i - 1)) ^ (1 / (n - i))) for i in range(n)])

    # By increments of 1/4, search for the scaling factor that gives the best bound.
    for i in range(1 , ceil(S * 4)):
        if CauchyBoundScale(l, i / 4) < B:
            B = CauchyBoundScale(l ,i / 4)
            j = i/4
    return j, B


# In[128]:


# After giving a lower bound d for the degree of the irreducible factors of T, the algorithm tries to find
# a value |m| > B + 1 , such that |f(m)| = sp with s < (|m| - B) ^ d and p is a 'small' prime.

# We look for m in the range B + 1 < |m| < B + 1 + k.

#Input:
# f : a polynomial
# B, k : bound the search range
# d : known lower degree bound for the factors of f

#Output:
# m : the value at which f is evaluated
# prime : a prime witness satisfying the conditions.

def FindPrimeFactorLPFW(f, B, d, k):
    t = ceil(B + 1)
    m = 0
    flagC = 0
    prime = Infinity
    rangeL = []
    cont = 0
    for i in range(t, t + k):
        rangeL = rangeL + [i , -i]
    for i in rangeL:
        cont = cont + 1
        sB = (abs(i) - B) ^ d
        V = abs(f.subs(X=i))
        F = factor(V)
        for p in F:
            if V / (p[0]) < sB and p[0] < prime:
                flagC = 1
                prime = p[0]
                m = i
                break
    if flagC == 1:
        return True, m, prime
    else :
        return False, 0, 0


# In[129]:


# The Large Prime Factor Witness certificate. https://doi.org/10.1007/978-3-030-52200-1_46
# This generates an irreducibility certificate for a polynomial T based on the LPFW certificate.
# This is given as a term of type CertificateIrreducibleIntOfPrimeDegreeAnalysis in our Lean formalization.

# Input:
# T : an irreducible polynomial
# lprimes : A list of primes that certify a degree bound for the factors of T.
# dmin : a lower bound for the degree of the factors of T
# f : the scaling factor used in the Cauchy bound
# rho : the Cauchy bound
# M : the evaluation argument
# prime : the prime witness
# doc: the file where the Lean code will be written.

def GlobalCertificateLPFWDegree (T, lprimes, dmin, f, rho, M, prime, doc) :
    l = T.list()
    s = abs(T(M))/ prime

    m = [len(factorLists(T,p)) for p in lprimes]

    print(f'noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where', file = doc)
    print(f' hpol := T_ofList\'', file = doc)
    print(f' hdeg := by decide', file = doc)
    print(f' hprim := by decide', file = doc)
    print(f' n := {len(lprimes)}', file = doc)
    print(f' d := {dmin}', file = doc)
    print(f' s := {s}', file = doc)
    print(f' P := {prime}', file = doc)
    print(f' M := {M}', file = doc)
    print(f' r := {f}', file = doc)
    print(f' ρ := {rho}', file = doc)
    if floor(log(prime,10) + 1) < 7 :
        print(' hPPrime := by norm_num', file = doc) # If the prime witness is small, we can prove it with norm_num
    else :
        print(' hPPrime := sorry -- Consider using Pratt certificate', file = doc) # Otherwise we 'sorry' the proof.
    print(f' hrpos := by norm_num', file = doc)
    print(f' hnn := by decide', file = doc)
    print(f' hdn := by decide', file = doc)
    print(f' p := !{lprimes}', file = doc)
    print(''' hp := by
  intro i
  fin_cases i''', file = doc)
    for p in lprimes:
        print(f'  exact hp{p}\'.out', file = doc)
    print(f' hlc := by decide', file = doc)
    print(f' m := !{m}', file = doc)
    print(''' F := fun i =>
  match i with ''', file = doc)
    for i in range(len(lprimes)):
        print(f'  | {i} => !{factorLists(T,lprimes[i])}', file = doc)
    print(''' D := fun i =>
  match i with ''', file = doc)
    for i in range(len(lprimes)):
        print(f'  | {i} => !{[len(factorLists(T,lprimes[i])[j]) - 1 for j in range(m[i])]}', file = doc)
    print(f' hl := by decide', file = doc)
    print(f''' hirr := by
  intro i ; intro j
  fin_cases i <;> fin_cases j''', file = doc)
    for p in lprimes:
        F = factor(GF(p)[x](T))
        for i in range(len(F)):
            if F[i][0].degree() == 1:
                for j in range(F[i][1]):
                    print(f'  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) (by decide)', file = doc)
            else :
                for j in range(F[i][1]):
                    print(f'  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList\' P{p}P{i}', file = doc)
    print(f' hm := by decide', file = doc)
    print(f' hprod := by decide +kernel', file = doc)
    print(f' hinter := by decide +kernel', file = doc)
    print(f' hrhoeq := by decide +kernel', file = doc)
    print(f' hrho := by decide +kernel', file = doc)
    print(f' hs := by norm_num', file = doc)
    print(f' heval := by norm_num', file = doc)


# In[130]:


# The Large Prime Factor Witness certificate. https://doi.org/10.1007/978-3-030-52200-1_46
# without degree analysis.
# This generates an irreducibility certificate for a polynomial T based on the LPFW certificate using
# the trivial lower degree bound d = 1 for the factors of T.
("")
# This is a term of type CertificateIrreducibleIntOfPrime in our Lean formalization.

# Input:
# T : an irreducible polynomial
# f : the scaling factor used in the Cauchy bound
# rho : the Cauchy bound
# M : the evaluation argument
# prime : the prime witness
# doc: the file where the Lean code will be written.


def GlobalCertificateLPFW (T, f, rho, M, prime, doc) :
    s = abs(T(M))/ prime
    print('noncomputable def C : CertificateIrreducibleIntOfPrime T l where', file = doc)
    print(' hpol := T_ofList\'', file = doc)
    print(' hdeg := by decide', file = doc)
    print(' hprim := by decide', file = doc)
    print(' hlz := by decide', file = doc)
    print(f' s := {s}', file = doc)
    print(f' P := {prime}', file = doc)
    print(f' M := {M}', file = doc)
    print(f' r := {f}', file = doc)
    print(f' ρ := {rho}', file = doc)
    if floor(log(prime,10) + 1) < 7 :
        print(' hPPrime := by norm_num', file = doc) # If the prime witness is small, we can prove it with norm_num
    else :
        print(' hPPrime := sorry -- Consider using Pratt certificate', file = doc) # Otherwise we 'sorry' the proof.
    print(' hrpos := by norm_num', file = doc)
    print(' hrhoeq := by decide +kernel', file = doc)
    print(' hrho := by decide +kernel', file = doc)
    print(' hs := by norm_num', file = doc)
    print(' heval := by norm_num', file = doc)


# In[131]:


# Writes a complete Lean proof of the irreducibility of a polynomial T.

# If a small prime witness can be quickly found using the trivial degree bound d = 1, then
# we use the LPFW certificate without degree analysis.

# Otherwise, if the irreducibility can be established through degree analysis by reducing modulo certain primes,
# then this is the proof provided.
# If degree analysis gives a lower bound dmin < T.degree() for the factors of T,
# then the LPFW certificate is used.
# If dmin = 1 or the value of s is already small enough, no additional
# advantage is gained from the degree analysis, and we use the LPFW certificate without degree analysis.

# Input :
# T : an irreducible polynomial
# doc : the file where the Lean code will be written.

def LeanProofIrreducible(T, doc):
    flagP = 0
    dmin = 0
    l = T.list()
    f , rho = CauchyBoundScaleOpt(l)
    flag, M, prime = FindPrimeFactorLPFW(T, rho, 1, 20)

    # If we quickly find a small prime witness assuming d = 1,
    # we give the LPFW certificate without degree analysis.
    if prime != 0 and floor(log(prime,10) + 1) < 7 :
        flagP = 1
    else :
        dmin, lprimes, N = BestCertificate(T, 3, 40) # we look for certificates based on
        # reductions of at most three primes smaller than 40
    if dmin == T.degree() and flagP == 0:
        print(f'''import LeanBridge.Mathlib.Irreduciblepolys.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import LeanBridge.Mathlib.Irreduciblepolys.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => ({T} : ℤ[X])

local notation "l" => {T.list()}

lemma T_ofList' : T = ofList l := by norm_num ; ring
    ''', file = doc)
        for p in lprimes:
            print(f'instance hp{p}\' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)', file = doc)
        print('', file = doc)

        for p in lprimes:
            F = factor(GF(p)[X](T))
            for N in range(len(F)):
                if (F[N][0].degree()) > 1:
                    if N == 0:
                        CertificateIrrModpFFP(F.unit() * F[N][0], p, N, doc)
                        print('', file = doc)
                    else :
                        CertificateIrrModpFFP(F[N][0], p, N, doc)
                        print('', file = doc)
        GlobalCertificateIrrF(T, lprimes, doc)
        print('', file = doc)
        print('theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C ', file = doc)
        doc.close()
    else :
        print(f'''

open Polynomial

local notation "T" => ({T} : ℤ[X])

local notation "l" => {T.list()}

lemma T_ofList' : T = ofList l := by norm_num ; ring
    ''', file = doc)
        if flagP == 0:
            flag, M, prime = FindPrimeFactorLPFW(T, rho, dmin, 50)
        if abs(T(M))/ prime >= abs(M) - rho and dmin > 1 and flagP == 0 :
            for p in lprimes:
                print(f'instance hp{p}\' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)', file = doc)
            print('', file = doc)

            for p in lprimes:
                F = factor(GF(p)[X](T))
                for N in range(len(F)):
                    if (F[N][0].degree()) > 1:
                        if N == 0:
                            CertificateIrrModpFFP(F.unit() * F[N][0], p, N, doc)
                            print('', file = doc)
                        else :
                            CertificateIrrModpFFP(F[N][0], p, N, doc)
                            print('', file = doc)
            GlobalCertificateLPFWDegree(T, lprimes, dmin, f, rho, M, prime, doc)
            print('', file = doc)
            print('theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C ', file = doc)
            doc.close()
        else :
            GlobalCertificateLPFW (T, f, rho, M, prime, doc)
            print('', file = doc)
            print('theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C ', file = doc)
            doc.close()


def polynomial_to_lean(poly, var_name):
    """Convert Sage polynomial to Lean syntax"""
    import re
    s = str(poly)
    s = re.sub(r'x', var_name, s)
    s = s.replace('*', ' * ')
    s = re.sub(r'(\d)/(\d)', r'((\1) / (\2))', s)
    s = s.replace('  ', ' ')
    return s.strip()

def generate_unit_certificates(T, label):
    """Generate fundamental unit certificates for number field defined by T"""
    try:
        K = NumberField(T, 'a')
        U = K.unit_group()
        units = U.fundamental_units()

        if len(units) == 0:
            return ""  # No units to generate

        lines = []
        lines.append('')
        lines.append('-- Fundamental Units')
        lines.append('')

        # Define the generator as an algebraic integer

        lines.append('')
        lines.append(f'lemma K_int_{label} : IsIntegral ℤ K_gen_{label} := by')
        lines.append('  sorry')
        lines.append('')
        lines.append(f'def K_gen_int_{label} : 𝓞 K_{label} := ⟨K_gen_{label}, K_int_{label}⟩')
        lines.append('')

        # Work in QQ[x] for certificate calculations
        Rx.<x> = PolynomialRing(QQ)
        T_QQ = Rx(T)  # Convert minimal polynomial to QQ[x]

        for i, unit in enumerate(units):
            unit_idx = i + 1
            unit_name = f"fundamental_unit_{label}_{unit_idx}"

            unit_inverse = unit.inverse()
            poly_u = Rx(unit.polynomial())  # Ensure it's in QQ[x]
            poly_u_inv = Rx(unit_inverse.polynomial())  # Ensure it's in QQ[x]

            # Certificate polynomial: (u * u_inv - 1) should be divisible by T
            P_x = (poly_u * poly_u_inv) - Rx(1)

            # Verify divisibility (should be exact)
            quotient, remainder = P_x.quo_rem(T_QQ)
            if remainder != 0:
                lines.append(f'-- Warning: unit {unit_idx} certificate has non-zero remainder\n')

            # Convert to Lean
            lean_poly_u = polynomial_to_lean(poly_u, f'K_gen_int_{label}')
            lean_poly_u_inv = polynomial_to_lean(poly_u_inv, f'K_gen_int_{label}')

            lines.append(f'def {unit_name} : (𝓞 K_{label})ˣ where')
            lines.append(f'  val := {lean_poly_u}')
            lines.append(f'  inv := {lean_poly_u_inv}')
            lines.append('  val_inv := by sorry')
            lines.append('  inv_val := by sorry')
            lines.append('')

        return '\n'.join(lines)

    except Exception as e:
        return f'-- Unit generation failed: {e}\n'

class UnclosableStringIO(StringIO):
    """StringIO that ignores close() calls"""
    def close(self):
        pass  # Do nothing

    def really_close(self):
        StringIO.close(self)

def main_sage(coeffs_str, label, generate_units='false'):
    global X, x

    try:
        coeffs_list = [QQ(c.strip()) for c in coeffs_str.split(',')]
    except Exception as e:
        print(f"Error parsing coefficients string: {e}", file=sys.stderr)
        sys.exit(1)

    R.<X> = PolynomialRing(ZZ)
    x = X

    try:
        T = R(coeffs_list)
    except Exception as e:
        print(f"Error converting coefficients to Z[X] polynomial: {e}", file=sys.stderr)
        sys.exit(1)

    # Generate irreducibility proof to a buffer that can't be closed
    proof_buffer = UnclosableStringIO()
    LeanProofIrreducible(T, proof_buffer)
    proof_output = proof_buffer.getvalue()
    proof_buffer.really_close()

    # Print the proof
    print(proof_output, end='')

    # Optionally generate unit certificates
    if generate_units.lower() == 'true':
        unit_code = generate_unit_certificates(T, label)
        print(unit_code)

# The execution block is simplified and safe for external calls
if __name__ == "__main__":
    # If run directly, it expects command line arguments.
    if len(sys.argv) == 3:
        # If run directly (not via load()), sys.argv[0] is the script name.
        # We assume main_sage is called here if run interactively,
        # but the Lean tactic explicitly calls main_sage(arg1, arg2).
        main_sage(sys.argv[1], sys.argv[2])
    # The Lean tactic execution (load() followed by function call) bypasses this.





# In[132]:


## EXAMPLE

#R.<X>= PolynomialRing(ZZ)
#T = X^8 - X^6 + 2*X^4 + X^2 + 1
#f = open(f"ExampleLeanProof8.lean", "w")
#LeanProofIrreducible(T,f)


# In[134]:


## EXAMPLE
#R.<X>= PolynomialRing(ZZ)
#T = X^5 - 150*X^3 - 100*X^2 + 8025*X + 28260
#f = open(f"ExampleLeanProof.lean", "w")
#LeanProofIrreducible(T,f)
