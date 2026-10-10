#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 06-260925 · sequences and series in Q_p, topology of Q_p, finite fields
// The boxed "III/2" on p1 is disregarded.
// HEADINGS sections 12-14 from source (missing word in "Sequences and ... in Q_p" read as "series")
// DROPPED
//   [p3] claim lim p^n = 0: repeats 04-260918 p3; [p2] notation "sum a_n < infinity" for convergence
// CORRECTIONS
//   [p2] S_n = sum_{i=1}^n -> sum_{i=0}^n, matching the series from n = 0
//   [p3] "smallest integer n with r <= p^(-n)" -> largest; {|x - a| < p^(-(n+1))} -> <=
//   [p5] phi: F_p -> F_p -> F_q -> F_q
//   [p7] C = R u {i} -> C = R(i)
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: index bounds made consistent (n >= N)
//   [p2] A: completeness of Q_p cited in the converse; sum of a digit series is the series itself
//   [p3] A: open balls open, closed balls closed; closed balls of positive radius open; value set of |.|_p
//   [p3] C: Q_p admits no field ordering (source: "no ordering in Q_p")
//   [p4] A: proof of total disconnectedness; B: proof of compactness of Z_p
//   [p4] A: characteristic, |F| = p^n, a^q = a; B: cyclicity of F^x
//   [p5] A: recalled facts on F_q[x]/(f) and F_q(alpha); notation F_(q^m); root existence
//   [p6] A: subfield argument completing the distinctness proof; splitting from the root count
//   [p7] A: degree and minimal polynomial defined

// [p1]
= Sequences and series in $QQ_p$

#theorem[
  A sequence $(a_n)$ in $QQ_p$ is a Cauchy sequence if and only if for every $epsilon > 0$ there is $N in NN$ with $|a_(n + 1) - a_n|_p < epsilon$ for all $n >= N$.
] <thm-cauchy-qp>

#proof[
  If $(a_n)$ is Cauchy and $epsilon > 0$, there is $N in NN$ with $|a_n - a_m|_p < epsilon$ for all $n, m >= N$. For $n >= N$ also $n + 1 >= N$, so $|a_(n + 1) - a_n|_p < epsilon$.

  Conversely, let $epsilon > 0$ and choose $N$ with $|a_(n + 1) - a_n|_p < epsilon$ for all $n >= N$. Let $m, n >= N$. If $n = m$, then $|a_n - a_m|_p = 0 < epsilon$. Otherwise assume $n > m$ and write $n = m + l$ with $l in NN$. Then
  $ |a_n - a_m|_p = |(a_(m + l) - a_(m + l - 1)) + (a_(m + l - 1) - a_(m + l - 2)) + dots.c + (a_(m + 1) - a_m)|_p. $
  Since the $p$-adic absolute value is non-archimedean,
  $ |a_n - a_m|_p <= max {|a_(m + i) - a_(m + i - 1)|_p : 1 <= i <= l}. $
  // [p2]
  The maximum is attained at some $1 <= i_0 <= l$, and $m + i_0 - 1 >= N$, so $|a_n - a_m|_p <= |a_(m + i_0) - a_(m + i_0 - 1)|_p < epsilon$.
]

#corollary[
  Let $(a_n)_(n >= 0)$ be a sequence in $QQ_p$. Then $sum_(n = 0)^infinity a_n$ converges if and only if $lim_(n -> infinity) a_n = 0$.
] <cor-series>

#proof[
  Let $S_n = sum_(i = 0)^n a_i$ be the partial sums. If the series converges, then $(S_n)$ converges and hence is Cauchy. Let $epsilon > 0$; there is $N in NN$ with $|S_(n + 1) - S_n|_p < epsilon$ for all $n >= N$. Since $|S_(n + 1) - S_n|_p = |a_(n + 1)|_p$, we get $|a_n|_p < epsilon$ for all $n > N$.

  Conversely, let $lim_(n -> infinity) a_n = 0$ and $epsilon > 0$. There is $N in NN$ with $|a_n|_p < epsilon$ for all $n > N$, hence $|S_(n + 1) - S_n|_p = |a_(n + 1)|_p < epsilon$ for all $n >= N$. By @thm-cauchy-qp, $(S_n)$ is Cauchy, and it converges because $QQ_p$ is complete (@thm-completion).
]

// [p3]
#proposition[
  Every series $sum_(n = n_0)^infinity a_n p^n$ with $n_0 in ZZ$ and $a_n in {0, 1, dots, p - 1}$ converges in $QQ_p$, and its sum is the $p$-adic number with digits $a_n$.
] <prop-digit-series>

#proof[
  $|a_n p^n|_p <= p^(-n) -> 0$, so the series converges by @cor-series. Its partial sums are the rational numbers $s_n$ of part 3) of the proof of @thm-completion, which converge to the $p$-adic number with digits $a_n$.
]

= Topology on $QQ_p$

The $p$-adic metric induces a topology on $QQ_p$. For $a in QQ_p$ and $r > 0$ write $B(a, r) = {x in QQ_p : |x - a|_p < r}$ for the open ball and $overline(B)(a, r) = {x in QQ_p : |x - a|_p <= r}$ for the closed ball. As in every metric space, open balls are open and closed balls are closed. The values of $|dot|_p$ on $QQ_p$ are $0$ and the powers $p^k$, $k in ZZ$.

#remark(cited: true)[
  $QQ_p$ admits no ordering compatible with its field operations.
]

#theorem[
  In $QQ_p$ every open ball is closed, and every closed ball of positive radius is open.
]

#proof[
  Let $B(a, r)$ be an open ball and let $n$ be the largest integer with $r <= p^(-n)$, so $p^(-(n + 1)) < r <= p^(-n)$. No $p$-adic number has absolute value strictly between $p^(-(n + 1))$ and $p^(-n)$, hence
  $ B(a, r) = {x in QQ_p : |x - a|_p < p^(-n)} = {x in QQ_p : |x - a|_p <= p^(-(n + 1))} = overline(B)(a, p^(-(n + 1))), $
  which is closed.

  Let $overline(B)(a, r)$ be a closed ball with $r > 0$ and $x in overline(B)(a, r)$. For $y in B(x, r)$, $|y - a|_p <= max {|y - x|_p, |x - a|_p} <= r$, so $B(x, r) subset.eq overline(B)(a, r)$. Hence $overline(B)(a, r)$ is open.
]

// [p4]
#corollary[
  $ZZ_p$ is both closed and open in $QQ_p$.
]

#proof[
  By @thm-completion, $ZZ_p = {x in QQ_p : |x|_p <= 1} = overline(B)(0, 1)$ is a closed ball, hence closed. By the theorem, it is open as well.
]

#corollary[
  $QQ_p$ is totally disconnected, that is, its only connected subsets are the empty set and the singletons.
]

#proof[
  Let $A subset.eq QQ_p$ contain distinct points $a, b$ and put $r = |a - b|_p$. The ball $U = B(a, r)$ is open and closed, contains $a$ and not $b$. Hence $A = (A inter U) union (A without U)$ is a decomposition into two disjoint nonempty sets that are open in $A$, and $A$ is not connected.
]

#theorem[
  $ZZ_p$ is compact.
]

#proof[
  $ZZ_p$ is a metric space, so it suffices to show that every sequence $(x_n)$ in $ZZ_p$ has a convergent subsequence. Infinitely many $x_n$ share the same first digit; among these, infinitely many share the same second digit; continuing, we obtain infinite index sets $I_1 supset.eq I_2 supset.eq dots.c$ such that all $x_n$ with $n in I_k$ have the same truncation $(x_n)_k$. Choose $n_1 < n_2 < dots.c$ with $n_k in I_k$. For $j, l >= k$ the truncations $(x_(n_j))_k$ and $(x_(n_l))_k$ agree, so $|x_(n_j) - x_(n_l)|_p <= p^(-k)$, and $(x_(n_k))$ is Cauchy. It converges in $QQ_p$ by @thm-completion, and its limit lies in $ZZ_p$, which is closed.
]

= Finite fields

#definition(title: [Finite field])[
  A _finite field_ is a field $F$ with $|F| < infinity$. The _characteristic_ $"char" F$ is the least $n in NN$ with $n dot 1 = 0$ in $F$. A finite field with $q$ elements is denoted $FF_q$, and $FF_p = ZZ slash p ZZ$ for a prime $p$.
]

#theorem[
  Let $F$ be a finite field. Then $"char" F$ is a prime $p$, and $|F| = p^n$ for some $n in NN$. The multiplicative group $F^* = F^times = F without {0}$ is cyclic, $F^times = chevron.l g chevron.r$; a generator $g$ is called a _primitive element_ of $F$. Consequently $a^q = a$ for every $a in FF_q$.
] <thm-finite-field>

#proof[
  Since $F$ is finite, the elements $n dot 1$ are not pairwise distinct, so $"char" F$ exists. If $"char" F = a b$ with $1 < a, b$, then $(a dot 1)(b dot 1) = 0$ with both factors nonzero, which is impossible in a field; so $"char" F = p$ is prime. Then ${n dot 1 : n in ZZ}$ is a subfield isomorphic to $FF_p$, and $F$ is a finite-dimensional vector space over it, of dimension $n$ say, so $|F| = p^n$.

  Let $|F| = q$. The proof of @thm-prim-exist in the case $m = p$ applies to $F^times$, which has order $q - 1$: every element has an order dividing $q - 1$, a polynomial $x^d - 1$ over the field $F$ has at most $d$ roots, and $sum_(d divides q - 1) phi(d) = q - 1$ by @thm-phi-sum. Hence $F^times$ has $phi(q - 1) >= 1$ elements of order $q - 1$, and it is cyclic. Finally $a^(q - 1) = 1$ for $a != 0$, so $a^q = a$ for every $a in F$.
]

#lemma[
  Let $p$ be a prime. Then $p divides binom(p, j)$ for all $0 < j < p$.
]

#proof[
  We have $binom(p, j) = p! slash ((p - j)! j!)$, and
  // [p5]
  $ p / j binom(p - 1, j - 1) = p / j dot (p - 1)! / ((j - 1)! (p - j)!) = p! / ((p - j)! j!) = binom(p, j). $
  Hence $j binom(p, j) = p binom(p - 1, j - 1)$, so $p divides j binom(p, j)$. Since $(p, j) = 1$, $p divides binom(p, j)$.
]

#theorem[
  Let $FF_q$ be a finite field with $"char" FF_q = p$. Then $phi: FF_q -> FF_q$, $phi(a) = a^p$, is a ring homomorphism.
] <thm-frobenius>

#proof[
  Let $a, b in FF_q$; $FF_q$ is commutative. Then $phi(a b) = (a b)^p = a^p b^p = phi(a) phi(b)$, and by the binomial theorem and the lemma,
  $ phi(a + b) = (a + b)^p = a^p + sum_(j = 1)^(p - 1) binom(p, j) a^j b^(p - j) + b^p = a^p + b^p = phi(a) + phi(b). $
  From $phi(a - b) + phi(b) = phi(a)$ we get $phi(a - b) = a^p - b^p = phi(a) - phi(b)$.
]

#remark(title: [Recall])[
  Let $f in FF_q [x]$ be irreducible of degree $m$. Then $FF_q [x] slash (f)$ is a field containing a copy of $FF_q$, with $q^m$ elements, in which the class of $x$ is a root of $f$. If $K supset.eq FF_q$ is a field and $alpha in K$ is a root of $f$, then $FF_q (alpha) = {g(alpha) : g in FF_q [x], deg g < m}$ has exactly $q^m$ elements. We write $FF_(q^m)$ for a field with $q^m$ elements that contains $FF_q$.
] <rem-recall-ext>

#lemma[
  Let $f in FF_q [x]$ be irreducible with $deg f = m$. Then $f$ has a root $alpha$ in some $FF_(q^m)$, and for every such root the roots of $f$ in $FF_(q^m)$ are exactly the $m$ pairwise distinct elements $alpha, alpha^q, alpha^(q^2), dots, alpha^(q^(m - 1))$.
] <lem-roots-irred>

#proof[
  A root exists in $FF_q [x] slash (f)$ by @rem-recall-ext. Let $beta in FF_(q^m)$ be a root of $f$. We claim $f(beta^q) = 0$.
  // [p6]
  Let $f(x) = sum_(i = 0)^m a_i x^i$. Since $a_i in FF_q$, $a_i^q = a_i$ by @thm-finite-field, and $x mapsto x^q$ is a ring homomorphism, being an iterate of the map in @thm-frobenius because $q$ is a power of $p$. Hence
  $ f(beta^q) = a_0 + a_1 beta^q + a_2 (beta^2)^q + dots.c + a_m (beta^m)^q \
    = a_0^q + (a_1 beta)^q + dots.c + (a_m beta^m)^q \
    = (a_0 + a_1 beta + dots.c + a_m beta^m)^q = f(beta)^q = 0. $
  It follows that $alpha, alpha^q, (alpha^q)^q, dots, alpha^(q^(m - 1))$ are roots of $f$.

  Suppose $alpha^(q^i) = alpha^(q^j)$ with $0 <= i < j <= m - 1$. Raising to the power $q^(m - j)$ gives $alpha^(q^(m - j + i)) = alpha^(q^m) = alpha$, by @thm-finite-field applied to $FF_(q^m)$. So $alpha$ is a root of $x^(q^k) - x$ with $k = m - j + i$ and $1 <= k < m$. The set $L = {beta in FF_(q^m) : beta^(q^k) = beta}$ is a subfield, because $beta mapsto beta^(q^k)$ is a ring homomorphism and $(beta^(-1))^(q^k) = (beta^(q^k))^(-1)$. It contains $FF_q$ and $alpha$, hence $FF_q (alpha)$, which has $q^m$ elements by @rem-recall-ext. But $L$ consists of roots of $x^(q^k) - x$, so $|L| <= q^k < q^m$, a contradiction, since $f(alpha) = 0$, $deg f = m$ and $f$ is irreducible. Hence the $m$ elements are pairwise distinct. A polynomial of degree $m$ has at most $m$ roots in a field, so these are all the roots of $f$ in $FF_(q^m)$, and $f$ splits completely over $FF_(q^m)$.
]

#definition(title: [Conjugates])[
  Let $FF_q subset.eq FF_(q^m)$ and $alpha in FF_(q^m)$. The elements $alpha, alpha^q, alpha^(q^2), dots, alpha^(q^(m - 1))$ are called the _conjugates_ of $alpha$ with respect to $FF_q$.
]

// [p7]
#example[
  For fields $K subset.eq L$, the _degree_ $[L : K]$ is the dimension of $L$ as a vector space over $K$, and the _minimal polynomial_ $m_alpha$ of $alpha in L$ is the monic polynomial of least degree over $K$ with root $alpha$. For $RR subset CC = RR(i)$ we have $[CC : RR] = 2$, $m_i (x) = x^2 + 1$ and $CC tilde.equiv RR[x] slash (x^2 + 1)$. The roots of $x^2 + 1$ are $i$ and $-i$. Complex conjugation $overline(a + b i) = a - b i$ satisfies $overline(i) = -i$, so it interchanges the roots of the irreducible polynomial $x^2 + 1$.
]

#definition(title: [Automorphism over $FF_q$])[
  An _automorphism of $FF_(q^m)$ over $FF_q$_ is an isomorphism of $FF_(q^m)$ onto itself that leaves every element of $FF_q$ invariant.
]

#remark[
  Such a map is also called an _$FF_q$-automorphism_.
]

#example[
  For $RR subset CC$, conjugation $z mapsto overline(z)$ fixes the real numbers, so it is an $RR$-automorphism of $CC$.
]
