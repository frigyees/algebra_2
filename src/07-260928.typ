#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 07-260928 · worked exercises on Q_p, trace and norm
// Scan pages: p1 = IMG_0705, p2 = IMG_0706, p3 = IMG_0707.
// HEADINGS sections 15, 16 coined
// DROPPED
//   [p1] ex. 2: digit-by-digit proof that a_0 != 0 implies a unit; repeats Proposition 8.10
//   [p3] doodles
// CORRECTIONS
//   [p1] ex. 1c: 1/2 = 2 + 3 + 3^3 + ... -> 2 + 3 + 3^2 + 3^3 + ...; 1/6 = 2*3^-1 + 1 + 3^2 + ... -> 2*3^-1 + 1 + 3 + 3^2 + ... (final answer changed)
//   [p1] ex. 3: a = sum_{n>=0} -> sum_{n>=-m}, as the solution uses a_{-m}
//   [p2] ex. 7: n = v_p(z) in Z^+ -> n in Z
//   [p3] ex. 9: "x^2 + 1 reducible over Q_2, = (x + 1)^2" -> reducible over Q_5 (the identity holds only in F_2[x]; x^2 + 1 is irreducible over Q_2)
//   [p3] ex. 9: "x^4 + 1 reducible over every Q_p" -> every odd p; (x^2-1)^2 + 2x and -(-2)x -> 2x^2, -(-2)x^2
//   [p3] lemma: alpha in F_q -> alpha in F_(q^m); tr = -m a_(m-1) -> -(m/r) a_(r-1); N = a_0^(m/r) -> (-1)^m a_0^(m/r)
// ADDITIONS (A filled in, C cited)
//   [p1] A: geometric series lemma; v_p on Q_p; truncation framing of the congruence method
//   [p1] A: 2/3 completed via ex. 3; divergence of sum (-1)^n; grouping of 2 sum (-3)^n justified
//   [p1] A: ex. 2 reduced to Proposition 8.10 plus |a|_p = 1
//   [p1] A: ex. 3 hypotheses a != 0, a_(-m) != 0; induction completing the digit process
//   [p2] A: counting argument in Legendre's formula; limit and x^2 = 6 in ex. 5
//   [p2] A: statement of the unit characterization; hypothesis x != 0 in ex. 7
//   [p2] A: ex. 8: rational non-squares, remaining odd cases, Hensel lifts, proof that 17 is a square in Q_2
//   [p3] A: ex. 9: easy implication, irreducibility of x^4 + 1 over Q, one of -1, 2, -2 is a residue, lifts to Q_p
//   [p3] C: irreducibility of x^4 + 1 over Q_2
//   [p3] A: r | m, the product identity, coefficient comparison in the lemma

// [p1]
= Worked exercises on $p$-adic numbers

#lemma[
  Let $x in QQ_p$ with $|x|_p < 1$. Then $sum_(n = 0)^infinity x^n$ converges in $QQ_p$ and its sum is $1 slash (1 - x)$.
] <lem-geometric>

#proof[
  By @lem-strict-ultra, $|1 - x|_p = max {1, |x|_p} = 1$, so $1 - x != 0$. The partial sums are $S_N = sum_(n = 0)^N x^n = (1 - x^(N + 1)) slash (1 - x)$, hence
  $ |S_N - 1 / (1 - x)|_p = (|x|_p^(N + 1)) / (|1 - x|_p) = |x|_p^(N + 1) -> 0. $
]

#remark[
  For $x in QQ_p$ we write $v_p (x) = v(x)$, with $v$ as in @thm-completion. By part 1) of that theorem this extends the $p$-adic valuation of $QQ$, and $|x|_p = p^(-v_p (x))$ for all $x != 0$.
]

#example[
  Find the $p$-adic expansions of $2 slash 3$ in $QQ_2$, of $-1 slash 6$ in $QQ_7$ and of $1 slash 6$ in $QQ_3$.
]

#solution[
  *$2 slash 3$ in $QQ_2$.* Since $|-2|_2 = 1 slash 2 < 1$, @lem-geometric gives $1 / 3 = 1 / (1 - (-2)) = sum_(n = 0)^infinity (-2)^n$. This is a convergent series but not an expansion, since the digits must be $0$ and $1$. Similarly
  $ -1 = 1 / (1 - 2) = sum_(n = 0)^infinity 2^n, quad -1 / 3 = 1 / (1 - 4) = sum_(n = 0)^infinity 4^n = 1 + 2^2 + 2^4 + dots.c, $
  and the latter is an expansion. Hence
  $ 2 / 3 = -2 dot (-1 / 3) = -2 sum_(n = 0)^infinity 4^n = -(2 + 2^3 + 2^5 + dots.c). $
  By @ex-neg with $p = 2$, lowest digit $a_1 = 1$ and $a_n = 1$ exactly for odd $n$, the negation has digits $2 - a_1 = 1$ at $2^1$ and $1 - a_n$ at $2^n$ for $n >= 2$:
  $ 2 / 3 = 2 + 2^2 + 2^4 + 2^6 + dots.c. $

  Alternatively, $2 slash 3 in ZZ_2$ by @rem-ab-in-zp, and its truncations $x_k$ satisfy $3 x_k equiv 2 pmod(2^k)$, so they are found by solving congruences. If $3 x equiv 2 pmod(2)$, then $x equiv 0 pmod(2)$ and $x = 2 y$. Then $3 (2 y) equiv 2 pmod(4)$ gives $2 y equiv 2 pmod(4)$, so $y equiv 1 pmod(2)$, $y = 2 z + 1$ and $x = 4 z + 2$. Then $3 (4 z + 2) equiv 2 pmod(8)$ gives $4 z + 6 equiv 2 pmod(8)$, that is, $2 z + 3 equiv 1 pmod(4)$, so $z equiv 1 pmod(2)$, $z = 2 w + 1$ and
  $ x = 4 (2 w + 1) + 2 = 8 w + 6. $
  So $x_3 = 6 = 0 + 1 dot 2 + 1 dot 2^2$, in agreement with the first three digits above.

  *$-1 slash 6$ in $QQ_7$.* By @lem-geometric, $-1 / 6 = 1 / (1 - 7) = sum_(n = 0)^infinity 7^n = 1 + 7 + 7^2 + dots.c$, which is an expansion. Alternatively, the truncations satisfy $6 x_k equiv -1 pmod(7^k)$. Modulo $7$, $6 x equiv -1$ gives $x equiv 1 pmod(7)$, so $x = 7 y + 1$. Then $6 (7 y + 1) equiv -1 pmod(49)$ gives $42 y + 6 equiv -1 pmod(49)$, that is, $6 y + 1 equiv 0 pmod(7)$, so $y equiv 1 pmod(7)$ and $x_2 = 1 + 1 dot 7$.

  *$1 slash 6$ in $QQ_3$.* We have $1 / 6 = 1 / 2 dot 1 / 3$. The formula $1 / 2 = 1 / (1 - (-1))$ does not help: $|-1|_3 = 1$, so the terms of $sum (-1)^n$ do not tend to $0$ and the series diverges by @cor-series. Instead,
  $ 1 / 2 = 2 / 4 = 2 / (1 - (-3)) = 2 sum_(n = 0)^infinity (-3)^n. $
  The digits must be $0, 1, 2$, and the terms with odd $n$ have coefficient $-2$. Using $-2 dot 3^(2 k + 1) = (1 - 3) dot 3^(2 k + 1) = 3^(2 k + 1) - 3^(2 k + 2)$,
  $ 2 (-3)^(2 k + 1) + 2 (-3)^(2 k + 2) = 3^(2 k + 1) - 3^(2 k + 2) + 2 dot 3^(2 k + 2) = 3^(2 k + 1) + 3^(2 k + 2). $
  Grouping the terms in consecutive pairs after the first replaces the sequence of partial sums by a subsequence, which has the same limit. Hence
  $ 1 / 2 = 2 + sum_(k = 0)^infinity (3^(2 k + 1) + 3^(2 k + 2)) = 2 + 3 + 3^2 + 3^3 + dots.c, $
  and multiplying by $3^(-1)$ shifts the digits:
  $ 1 / 6 = 2 dot 3^(-1) + 1 + 3 + 3^2 + dots.c. $
]

#example[
  Let $a = a_0 + a_1 p + a_2 p^2 + dots.c in ZZ_p$. Show that $a$ is a unit of $ZZ_p$ if and only if $a_0 != 0$, and that this holds if and only if $|a|_p = 1$.
] <ex-units>

#solution[
  The first equivalence is part of @prop-qp-field. For $a in ZZ_p$ we have $v_p (a) >= 0$, and $v_p (a) = 0$ holds if and only if $a_0 != 0$. Hence $a_0 != 0$ if and only if $|a|_p = p^0 = 1$.
]

#example[
  Let $0 != a in QQ_p$ with expansion $a = sum_(n = -m)^infinity a_n p^n$, where $m in ZZ$ and $a_(-m) != 0$. Find the expansion of $-a$.
] <ex-neg>

#solution[
  Write $-a = sum_(n = -m)^infinity b_n p^n$; its lowest index is at least $-m$ because $v_p (-a) = v_p (a)$. Then $a + (-a) = 0$. Multiplying by $p^m$,
  $ alpha = p^m a = a_(-m) + a_(-m + 1) p + dots.c + a_0 p^m + a_1 p^(m + 1) + dots.c, quad beta = p^m (-a) = b_(-m) + b_(-m + 1) p + dots.c, $
  with $alpha, beta in ZZ_p$ and $alpha + beta = 0$. So the truncations satisfy $alpha_k + beta_k equiv 0 pmod(p^k)$ for every $k in NN$.

  For $k = 1$: $a_(-m) + b_(-m) equiv 0 pmod(p)$, and $1 <= a_(-m) + b_(-m) <= 2 p - 1$, so $a_(-m) + b_(-m) = p$ and $b_(-m) = p - a_(-m)$. Hence $alpha_1 + beta_1 = p$.

  // [p2]
  Continuing the process, suppose $alpha_k + beta_k = p^k$. Then
  $ alpha_(k + 1) + beta_(k + 1) = p^k + (a_(k - m) + b_(k - m)) p^k equiv 0 pmod(p^(k + 1)), $
  so $1 + a_(k - m) + b_(k - m) equiv 0 pmod(p)$. Since $1 <= 1 + a_(k - m) + b_(k - m) <= 2 p - 1$, this gives $1 + a_(k - m) + b_(k - m) = p$, that is, $b_(k - m) = p - 1 - a_(k - m)$, and $alpha_(k + 1) + beta_(k + 1) = p^(k + 1)$. By induction,
  $ -a = (p - a_(-m)) p^(-m) + (p - 1 - a_(-m + 1)) p^(-m + 1) + dots.c + (p - 1 - a_0) + (p - 1 - a_1) p + dots.c. $
]

#example(title: [Legendre's formula])[
  Let $n in NN$ and let $p$ be a prime. Show that
  $ v_p (n!) = sum_(i = 1)^infinity floor(n / p^i), $
  where the sum is finite because its terms vanish for $p^i > n$. Consequently $n! = product_(p <= n) p^(alpha_p)$ with $alpha_p = sum_(i >= 1) floor(n slash p^i)$.
]

#solution[
  Since $n! = 1 dot 2 dot dots.c dot n$, @prop-vp gives $v_p (n!) = sum_(j = 1)^n v_p (j)$, and $v_p (j)$ is the number of $i >= 1$ with $p^i divides j$. Exchanging the order of summation,
  $ v_p (n!) = sum_(j = 1)^n sum_(i >= 1, space p^i divides j) 1 = sum_(i >= 1) \#{1 <= j <= n : p^i divides j}. $
  The factors divisible by $p$ are $p, 2 p, dots, t p$, where $t p <= n < (t + 1) p$, so there are $t = floor(n slash p)$ of them. In the same way, exactly $floor(n slash p^2)$ factors are divisible by $p^2$, and $floor(n slash p^i)$ by $p^i$. The prime divisors of $n!$ are the primes $p <= n$, which gives the factorization.
]

#example[
  Show that $x^2 = 6$ has a solution in $QQ_5$.
] <ex-sqrt6>

#solution[
  $x^2 equiv 6 pmod(5)$ has the solution $x equiv 1 pmod(5)$. We prove by induction that there are integers $x_n$, $n >= 1$, with $x_n^2 equiv 6 pmod(5^n)$, $x_1 = 1$ and $x_(n + 1) equiv x_n pmod(5^n)$. Given $x_n$ with $x_n equiv 1 pmod(5)$, write $x_n^2 = 5^n s + 6$ and $x_(n + 1) = x_n + t 5^n$ with $t in ZZ$. Then
  $ x_(n + 1)^2 = x_n^2 + 2 x_n t 5^n + t^2 5^(2 n) equiv 6 pmod(5^(n + 1)) $
  holds if and only if
  $ 2 x_n t + (x_n^2 - 6) / 5^n equiv 0 pmod(5). $
  Since $(2 x_n, 5) = 1$, this linear congruence has a solution $t$ (@rem-linear), which is the lifting step of @thm-hensel. Then $x_(n + 1) equiv x_n equiv 1 pmod(5)$.

  Since $|x_(n + 1) - x_n|_5 <= 5^(-n)$, the sequence $(x_n)$ is Cauchy by @thm-cauchy-qp and converges to some $x in QQ_5$ by @thm-completion; $x in ZZ_5$ since $ZZ_5$ is closed. Finally $|x + x_n|_5 <= 1$, so
  $ |x^2 - 6|_5 <= max {|x - x_n|_5 |x + x_n|_5, |x_n^2 - 6|_5} <= max {|x - x_n|_5, 5^(-n)} -> 0, $
  and $x^2 = 6$.
]

#example[
  Consider $QQ$ with the $5$-adic metric and the triangle with vertices $A = 2 slash 15$, $B = 1 slash 5$, $C = 7 slash 15$. Compute its side lengths.
]

#solution[
  Recall that $v_p (a slash b) = v_p (a) - v_p (b)$ and $|x|_p = p^(-v_p (x))$ for $x != 0$. Here $v_5 (-1) = 0$ and $v_5 (15) = 1$. Hence
  $ |A - B|_5 = |2 / 15 - 3 / 15|_5 = |-1 / 15|_5 = 1 / 5^(-1) = 5, \
    |B - C|_5 = |-4 / 15|_5 = 5, quad |C - A|_5 = |5 / 15|_5 = |1 / 3|_5 = 1. $
  In agreement with @thm-isosceles, the two longest sides are equal.
]

#example[
  Characterize the units of $ZZ_p$ in terms of $v_p$. Prove that $0 != x in QQ_p$ is a square in $QQ_p$ if and only if $x = p^(2 n) y^2$ with $n in ZZ$ and $y$ a unit of $ZZ_p$.
]

#solution[
  By @thm-completion 2), $x in QQ_p$ lies in $ZZ_p$ if and only if $v_p (x) >= 0$. By @ex-units, an element of $ZZ_p$ is a unit if and only if $v_p = 0$. Hence $ZZ_p^times = {x in QQ_p : v_p (x) = 0}$.

  If $x = p^(2 n) y^2$, then $p^(2 n) = (p^n)^2$ and $x = (p^n y)^2$ with $p^n y in QQ_p$. Conversely, let $x = z^2$ with $z in QQ_p$; then $z != 0$. By @prop-qp-field, $z = p^n y$ with $n = v_p (z) in ZZ$ and $y in ZZ_p^times$. Hence $x = z^2 = (p^n y)^2 = p^(2 n) y^2$, and $y^2 = y dot y in ZZ_p^times$.
]

#example[
  Prove that $(x^2 - 2)(x^2 - 17)(x^2 - 34) = 0$ has a root in $QQ_p$ for every $p <= infinity$, but no root in $QQ$.
]

#solution[
  None of $2, 17, 34$ is the square of a rational number, since $v_q (z^2) = 2 v_q (z)$ is even for every prime $q$ and every $0 != z in QQ$, whereas $v_2 (2) = v_17 (17) = v_2 (34) = 1$. So there is no rational root.

  *$p = infinity$.* $QQ_infinity = RR$ and $sqrt(2) in RR$ is a root.

  *$p$ odd, $p != 17$.* Then $p divides.not 2 dot 17 dot 34$. If $ls(2, p) = 1$ or $ls(17, p) = 1$, one of $2, 17$ is a quadratic residue modulo $p$. Otherwise $ls(2, p) = ls(17, p) = -1$, and by @prop-legendre 2)
  $ ls(34, p) = ls(2, p) ls(17, p) = (-1)(-1) = 1, $
  so there is $x$ with $x^2 equiv 34 pmod(p)$. In each case some $a in {2, 17, 34}$ and $c in ZZ$ satisfy $c^2 equiv a pmod(p)$, and $p divides.not c$. For $f(x) = x^2 - a$ we have $f'(c) = 2 c equiv.not 0 pmod(p)$, so as in the solution of @ex-sqrt2, @thm-hensel yields $alpha in ZZ_p$ with $alpha^2 = a$.

  *$p = 17$.* $6^2 = 36 equiv 2 pmod(17)$ and $f'(6) = 12 equiv.not 0 pmod(17)$ for $f(x) = x^2 - 2$, so $2$ is a square in $QQ_17$ in the same way.

  *$p = 2$.* We show that $17$ is a square in $QQ_2$; @thm-hensel does not apply, since $f'(x) = 2 x equiv 0 pmod(2)$. We construct odd integers $x_k$, $k >= 3$, with $x_k^2 equiv 17 pmod(2^k)$ and $x_(k + 1) equiv x_k pmod(2^(k - 1))$. Take $x_3 = 1$. Given $x_k$, write $x_k^2 - 17 = 2^k s$ and put $x_(k + 1) = x_k + t 2^(k - 1)$ with $t in {0, 1}$. Then
  $ x_(k + 1)^2 = x_k^2 + t x_k 2^k + t^2 2^(2 k - 2) equiv 17 + 2^k (s + t x_k) pmod(2^(k + 1)), $
  since $2 k - 2 >= k + 1$ for $k >= 3$. As $x_k$ is odd, $t equiv s pmod(2)$ makes $s + t x_k$ even, and $x_(k + 1)^2 equiv 17 pmod(2^(k + 1))$. Now $|x_(k + 1) - x_k|_2 <= 2^(-(k - 1))$, so $(x_k)$ converges to some $x in ZZ_2$, and the argument at the end of the solution of @ex-sqrt6 gives $x^2 = 17$.
]

// [p3]
#example[
  Let $f in ZZ[x]$. Is it true that $f$ is irreducible in $QQ[x]$ if and only if $f$ is irreducible in $QQ_p [x]$ for every prime $p$?
]

#solution[
  One implication holds. If $f$ is reducible over $QQ$, that is, $f = g h$ with $g, h in QQ[x]$ of positive degree, then this is a factorization in $QQ_p [x]$, so $f$ is reducible over $QQ_p$. Hence irreducibility over every $QQ_p$ implies irreducibility over $QQ$.

  The other implication fails. $x^2 + 1$ is irreducible over $QQ$, since $-1$ is not a rational square. It is reducible over $QQ_5$: $2^2 equiv -1 pmod(5)$ and $f'(2) = 4 equiv.not 0 pmod(5)$ for $f(x) = x^2 + 1$, so @thm-hensel gives $iota in ZZ_5$ with $iota^2 = -1$, and $x^2 + 1 = (x - iota)(x + iota)$.

  A stronger example: $x^4 + 1$ is irreducible over $QQ$ but reducible over $QQ_p$ for every odd prime $p$.

  _Irreducibility over $QQ$._ It has no rational root, since $x^4 >= 0 > -1$ for real $x$. In $RR[x]$,
  $ x^4 + 1 = (x^2 + 1)^2 - 2 x^2 = (x^2 - sqrt(2) x + 1)(x^2 + sqrt(2) x + 1), $
  and both factors are irreducible over $RR$ (discriminant $2 - 4 < 0$). By unique factorization in $RR[x]$, a monic quadratic factor of $x^4 + 1$ over $QQ$ would equal one of them, but neither has rational coefficients.

  _Reducibility over $QQ_p$, $p$ odd._ Recall from @prop-legendre that
  $ ls(-1, p) = cases(1 & "if" p equiv 1 pmod(4), -1 & "if" p equiv 3 pmod(4)), quad ls(2, p) = cases(1 & "if" p equiv plus.minus 1 pmod(8), -1 & "if" p equiv plus.minus 3 pmod(8).) $
  Since $ls(-1, p) ls(2, p) = ls(-2, p)$, at least one of $-1, 2, -2$ is a quadratic residue modulo $p$; in particular $ls(-2, p) = 1$ if and only if $p equiv 1, 3 pmod(8)$. As in the previous example, @thm-hensel lifts a square root modulo $p$ of $-1$, $2$ or $-2$ to $QQ_p$, since $p$ is odd.
  - If $ls(2, p) = 1$, there is $a in ZZ_p$ with $a^2 = 2$, and $x^4 + 1 = (x^2 + 1)^2 - 2 x^2 = (x^2 + 1 - a x)(x^2 + 1 + a x)$.
  - If $ls(-2, p) = 1$, there is $b in ZZ_p$ with $b^2 = -2$, and
    $ x^4 + 1 = (x^2 - 1)^2 + 2 x^2 = (x^2 - 1)^2 - (-2) x^2 = (x^2 - 1 - b x)(x^2 - 1 + b x). $
  - If $ls(-1, p) = 1$, that is, $p equiv 1 pmod(4)$, there is $c in ZZ_p$ with $c^2 = -1$, and $x^4 + 1 = x^4 - (-1) = (x^2 - c)(x^2 + c)$.
]

#remark(cited: true)[
  The prime $2$ is a genuine exception: $x^4 + 1$ is irreducible over $QQ_2$, although $x^4 + 1 equiv (x + 1)^4 pmod(2)$. Likewise $x^2 + 1$ is irreducible over $QQ_2$, although $x^2 + 1 equiv (x + 1)^2 pmod(2)$.
]

= Trace and norm

Throughout, $q$ is a prime power, $m in NN$, and $FF_q subset.eq FF_(q^m)$ as in @rem-recall-ext.

#definition(title: [Trace])[
  Let $alpha in FF_(q^m)$. The _relative trace_ of $alpha$ over $FF_q$ is
  $ tr_(FF_(q^m) | FF_q) (alpha) = alpha + alpha^q + dots.c + alpha^(q^(m - 1)). $
  If $FF_q = FF_p$ with $p$ prime, then $tr_(FF_(p^m) | FF_p)$ is called the _trace_.
]

#definition(title: [Norm])[
  Let $L = FF_(q^m)$, $K = FF_q$ and $alpha in L$. The _relative norm_ of $alpha$ over $K$ is
  $ nrm_(L | K) (alpha) = alpha dot alpha^q dot dots.c dot alpha^(q^(m - 1)). $
]

#lemma[
  Let $alpha in FF_(q^m)$. Then $tr_(FF_(q^m) | FF_q) (alpha) in FF_q$ and $nrm_(FF_(q^m) | FF_q) (alpha) in FF_q$. More precisely, if $m_alpha (x) = sum_(i = 0)^r a_i x^i$ is the minimal polynomial of $alpha$ over $FF_q$, then $r divides m$ and
  $ tr_(FF_(q^m) | FF_q) (alpha) = -m / r dot a_(r - 1), quad nrm_(FF_(q^m) | FF_q) (alpha) = (-1)^m a_0^(m slash r). $
]

#proof[
  $alpha$ is a root of $x^(q^m) - x$ by @thm-finite-field, so it has a minimal polynomial $m_alpha in FF_q [x]$, which is monic and irreducible, of degree $r = [FF_q (alpha) : FF_q]$; so $a_r = 1$. By @rem-recall-ext, $FF_q (alpha)$ is a field with $q^r$ elements containing $FF_q$. Since $FF_(q^m)$ is a vector space over $FF_q (alpha)$ of some dimension $s$, we get $q^m = (q^r)^s$, so $r divides m$ and $m = r s$.

  By @lem-roots-irred applied to $m_alpha$ and the field $FF_q (alpha)$, $m_alpha (x) = product_(i = 0)^(r - 1) (x - alpha^(q^i))$. By @thm-finite-field applied to $FF_q (alpha)$, $alpha^(q^r) = alpha$, hence $alpha^(q^(j r)) = alpha$ and $alpha^(q^(i + j r)) = (alpha^(q^(j r)))^(q^i) = alpha^(q^i)$ for all $i, j >= 0$. Splitting $0 <= i <= m - 1$ into $m slash r$ blocks of length $r$,
  $ product_(i = 0)^(m - 1) (x - alpha^(q^i)) = product_(i = 0)^(r - 1) (x - alpha^(q^i)) dot product_(i = 0)^(r - 1) (x - alpha^(q^(i + r))) dot dots.c dot product_(i = 0)^(r - 1) (x - alpha^(q^(i + r (m slash r - 1)))) = m_alpha (x)^(m slash r). $
  So the coefficients of the left side lie in $FF_q$. Its coefficient of $x^(m - 1)$ is $-(alpha + alpha^q + dots.c + alpha^(q^(m - 1))) = -tr(alpha)$, and its constant term is $(-1)^m alpha dot alpha^q dot dots.c dot alpha^(q^(m - 1)) = (-1)^m nrm(alpha)$. On the right, the coefficient of $x^(m - 1)$ in $(x^r + a_(r - 1) x^(r - 1) + dots.c + a_0)^(m slash r)$ is $(m slash r) a_(r - 1)$, and the constant term is $a_0^(m slash r)$. Comparing coefficients gives both formulas.
]
