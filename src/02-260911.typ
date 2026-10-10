#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 02-260911 · binomial congruences, Legendre and Jacobi symbols, Hensel's lemma
// Scan pages are in reverse order: reading order p11 -> p1. The boxed "I/2" on p11 is disregarded.
// HEADINGS sections 4-6 coined
// CORRECTIONS
//   [p7] "a is a QR iff a^((p-1)/2) = -1" -> = 1
//   [p9] ind_22 -> ind_2; "z = 2, 8 (mod 6)" -> (mod 12)
//   [p4] (a/mn) = (a/n) + (a/m) -> product
//   [p1] c_(n-1) -> c_(k-1)
// NOTATION
//   exponent letter read as k (ell-like glyph); polynomial degree renamed to n; Legendre/Jacobi subscripts dropped
// ADDITIONS (A filled in, B supplied proof)
//   [p11] A: k in N; recalled linear congruences; proof of sufficiency and of the solution count
//   [p8]  A: proof of the residue count; proof of a^((p-1)/2) = +-1
//   [p7]  A: proof of Euler's criterion and of properties 1, 3
//   [p6]  B: Gauss's lemma, parity lemma, proofs of (2/p) and of quadratic reciprocity; p != q in the law
//   [p6]  A: primality of 1783, 7523 stated; justifications in the (1783/7523) chain; forward references to the Jacobi results
//   [p5]  A: coincidence with the Legendre symbol; parity lemma; proofs of all Jacobi properties
//   [p4]  A: (m, n) = 1 and a proof for Jacobi reciprocity; remark on (a/n) = 1 vs solvability
//   [p3]  A: lifting sentence and formal derivative; f in Z[x], j >= 1; uniqueness step c_k = c_(k-1) (mod p^(k-1)); existence direction

// [p11]
Let $p$ be a prime, $a in ZZ$ with $(a, p) = 1$, and $k in NN$. We consider the congruence $x^k equiv a pmod(p)$.

#remark(title: [Recall])[
  Let $n in NN$ and $a, b in ZZ$. The congruence $a y equiv b pmod(n)$ is solvable if and only if $(a, n) divides b$, and then it has exactly $(a, n)$ pairwise incongruent solutions modulo $n$.
] <rem-linear>

#theorem[
  Let $p$ be a prime, $a in ZZ$ with $(a, p) = 1$, and $k in NN$. The congruence $x^k equiv a pmod(p)$ is solvable if and only if
  $ a^((p - 1) slash (k, p - 1)) equiv 1 pmod(p). $
  In that case the number of pairwise incongruent solutions is $(k, p - 1)$. If $g$ is a primitive root modulo $p$, the condition is equivalent to $(k, p - 1) divides ind_g a$.
] <thm-binomial>

#proof[
  Let $g$ be a primitive root modulo $p$ (@thm-prim-exist) and $e = (k, p - 1)$. Every solution $x$ satisfies $p divides.not x$, since $p divides.not a$. By the definition of the index and @prop-ind, $x mapsto ind_g x$ is a bijection from the residue classes modulo $p$ not divisible by $p$ onto the residue classes modulo $p - 1$. We seek solutions in the form $x equiv g^(ind_g x) pmod(p)$. Then
  $ x^k equiv (g^(ind_g x))^k = g^(k ind_g x) quad "and" quad a equiv g^(ind_g a) pmod(p), $
  // [p10]
  so by @prop-ind, $x^k equiv a pmod(p)$ if and only if $k ind_g x equiv ind_g a pmod(p - 1)$. Put $y = ind_g x$. The solutions $x$ modulo $p$ correspond bijectively to the solutions $y$ modulo $p - 1$ of the linear congruence
  $ k y equiv ind_g a pmod(p - 1). $
  By @rem-linear it is solvable if and only if $e divides ind_g a$, and then it has exactly $e$ solutions.

  It remains to show that $e divides ind_g a$ if and only if $a^((p - 1) slash e) equiv 1 pmod(p)$. We have
  $ a^((p - 1) slash e) equiv (g^(ind_g a))^((p - 1) slash e) = g^(ind_g a dot (p - 1) slash e) pmod(p). $
  By @prop-order with $ord(p, g) = p - 1$, this is congruent to $1$ if and only if $p - 1 divides ind_g a dot (p - 1) slash e$, that is, if and only if $e divides ind_g a$.
]

#example[
  Solve $5 x^22 equiv 6 pmod(13)$.
]

#solution[
  Let $y = x^22$. Then $5 y equiv 6 pmod(13)$ with $(5, 13) = 1$. Multiplying by $5$ gives $25 y equiv 30 pmod(13)$, and $25 equiv -1$, $30 equiv 4$, so $-y equiv 4$ and $y equiv -4 equiv 9 pmod(13)$. It remains to solve $x^22 equiv 9 pmod(13)$.

  Here $phi(13) = 12 = 2^2 dot 3$. Since $2^4 = 16 equiv 3$ and $2^6 = 64 equiv -1 pmod(13)$, @proc-prim shows that $2$ is a primitive root modulo $13$, that is, $ord(13, 2) = 12$. Taking indices to the base $2$ and using @thm-ind,
  $ 22 ind_2 x equiv ind_2 9 pmod(12). $
  // [p9]
  The powers of $2$ modulo $13$ are:
  #align(center, table(
    columns: 13,
    $n$, ..range(1, 13).map(n => [#n]),
    $2^n$, ..(2, 4, 8, 3, 6, 12, 11, 9, 5, 10, 7, 1).map(v => [#v]),
  ))
  Hence $ind_2 9 = 8$. Let $z = ind_2 x$. Then $22 z equiv 8 pmod(12)$, and $(22, 12) = 2 divides 8$, so there are two solutions modulo $12$. Dividing by $2$ gives $11 z equiv 4 pmod(6)$, that is, $-z equiv 4$, so $z equiv -4 equiv 2 pmod(6)$. Thus $z equiv 2$ or $z equiv 8 pmod(12)$.
  // [p8]
  From $ind_2 x equiv 2$ we get $x equiv 2^2 = 4$, and from $ind_2 x equiv 8$ we get $x equiv 2^8 equiv 9 pmod(13)$. The solutions are $x equiv 4$ and $x equiv 9 pmod(13)$.
]

#corollary[
  Let $p$ be an odd prime and $a in ZZ$ with $(a, p) = 1$. Then $a$ is a quadratic residue modulo $p$ if and only if $a^((p - 1) slash 2) equiv 1 pmod(p)$, and in that case $x^2 equiv a pmod(p)$ has exactly $2$ pairwise incongruent solutions. Among the $p - 1$ residue classes coprime to $p$ there are $(p - 1) slash 2$ quadratic residues and $(p - 1) slash 2$ quadratic non-residues.
] <cor-qr>

#proof[
  Since $p$ is odd, $(2, p - 1) = 2$, and the first two statements are @thm-binomial with $k = 2$. The map $x mapsto x^2$ sends the $p - 1$ residue classes coprime to $p$ onto the quadratic residues, and each quadratic residue has exactly $2$ preimages. Hence there are $(p - 1) slash 2$ quadratic residues, and the remaining $(p - 1) slash 2$ classes are non-residues.
]

#proposition[
  Let $p$ be an odd prime and $a in ZZ$ with $p divides.not a$. Then $a^((p - 1) slash 2) equiv plus.minus 1 pmod(p)$, and $a$ is a quadratic residue modulo $p$ if and only if $a^((p - 1) slash 2) equiv 1 pmod(p)$.
] <prop-pm1>

#proof[
  Let $b = a^((p - 1) slash 2)$. By Fermat's theorem $b^2 = a^(p - 1) equiv 1 pmod(p)$, so $p divides (b - 1)(b + 1)$. Since $p$ is prime, $b equiv 1$ or $b equiv -1 pmod(p)$. The criterion is @cor-qr.
]

// [p7]
= The Legendre symbol and quadratic reciprocity

#definition(title: [Legendre symbol])[
  Let $p > 2$ be a prime and $a in ZZ$ with $(a, p) = 1$. The _Legendre symbol_ is
  $ ls(a, p) = cases(1 & "if" a "is a quadratic residue modulo" p, -1 & "if" a "is a quadratic non-residue modulo" p.) $
]

#corollary(title: [Euler's criterion])[
  Let $p > 2$ be a prime and $a in ZZ$ with $(a, p) = 1$. Then $ls(a, p) equiv a^((p - 1) slash 2) pmod(p)$.
] <cor-euler>

#proof[
  By @prop-pm1, $a^((p - 1) slash 2) equiv 1 = ls(a, p)$ if $a$ is a quadratic residue, and otherwise $a^((p - 1) slash 2) equiv -1 = ls(a, p)$.
]

#proposition[
  Let $p > 2$ be a prime and $a, b in ZZ$ with $(a, p) = (b, p) = 1$. Then:
  + If $a equiv b pmod(p)$, then $ls(a, p) = ls(b, p)$.
  + $ls(a, p) ls(b, p) = ls(a b, p)$.
  // [p6]
  + $ls(-1, p) = 1$ if $p equiv 1 pmod(4)$, and $ls(-1, p) = -1$ if $p equiv -1 pmod(4)$.
  + $ls(2, p) = 1$ if $p equiv plus.minus 1 pmod(8)$, and $ls(2, p) = -1$ if $p equiv plus.minus 3 pmod(8)$.
] <prop-legendre>

// [p7]
#proof[
  1) If $x^2 equiv a pmod(p)$, then $x^2 equiv b pmod(p)$, and conversely.

  2) By @cor-euler, $ls(a b, p) equiv (a b)^((p - 1) slash 2) = a^((p - 1) slash 2) b^((p - 1) slash 2) equiv ls(a, p) ls(b, p) pmod(p)$. Both sides lie in ${1, -1}$ and $p > 2$, so the congruence is an equality.

  3) By @cor-euler, $ls(-1, p) equiv (-1)^((p - 1) slash 2) pmod(p)$, and as in 2) this is an equality. The exponent $(p - 1) slash 2$ is even if and only if $p equiv 1 pmod(4)$.

  4) is proved after @lem-gauss.
]

#lemma(title: [Gauss])[
  Let $p$ be an odd prime, $a in ZZ$ with $p divides.not a$, and $S = {1, 2, dots, (p - 1) slash 2}$. For $j in S$ let $t_j$ be the least positive residue of $j a$ modulo $p$, and let $mu$ be the number of $j in S$ with $t_j > p slash 2$. Then $ls(a, p) = (-1)^mu$.
] <lem-gauss>

#proof[
  For $j in S$ put $s_j = t_j$ if $t_j < p slash 2$ and $s_j = p - t_j$ otherwise. Then $s_j in S$ and $s_j equiv plus.minus j a pmod(p)$, with the minus sign for exactly $mu$ values of $j$. If $s_i = s_j$, then $i a equiv plus.minus j a$, so $i equiv plus.minus j pmod(p)$ because $p divides.not a$. Since $2 <= i + j <= p - 1$, the minus sign is impossible, so $i = j$. Hence $j mapsto s_j$ is a permutation of $S$, and
  $ product_(j in S) j a equiv (-1)^mu product_(j in S) s_j = (-1)^mu ((p - 1) / 2)! pmod(p). $
  The left side is $a^((p - 1) slash 2) ((p - 1) slash 2)!$. Cancelling the unit $((p - 1) slash 2)!$ gives $a^((p - 1) slash 2) equiv (-1)^mu$, and @cor-euler gives $ls(a, p) equiv (-1)^mu pmod(p)$. Both sides lie in ${1, -1}$ and $p > 2$, so they are equal.
]

#proof(title: [Proof of @prop-legendre 4)])[
  Take $a = 2$ in @lem-gauss. For $j in S$ we have $2 j <= p - 1$, so $t_j = 2 j$, and $mu$ is the number of $j in S$ with $j > p slash 4$, namely $mu = (p - 1) slash 2 - floor(p slash 4)$. Writing $p = 8 l + r$ with $r in {1, 3, 5, 7}$:
  $ r = 1: mu = 4 l - 2 l = 2 l, & quad r = 3: mu = (4 l + 1) - 2 l = 2 l + 1, \
    r = 5: mu = (4 l + 2) - (2 l + 1) = 2 l + 1, & quad r = 7: mu = (4 l + 3) - (2 l + 1) = 2 l + 2. $
  So $mu$ is even for $p equiv plus.minus 1 pmod(8)$ and odd for $p equiv plus.minus 3 pmod(8)$.
]

#lemma[
  Let $p$ be an odd prime, $a$ an odd integer with $p divides.not a$, and $mu$ as in @lem-gauss. Then
  $ mu equiv sum_(j = 1)^((p - 1) slash 2) floor((j a) / p) pmod(2). $
] <lem-parity-floor>

#proof[
  With the notation of @lem-gauss, $j a = p floor(j a slash p) + t_j$. Let $u_1, dots, u_lambda$ be the $t_j$ below $p slash 2$ and $v_1, dots, v_mu$ those above. By the proof of @lem-gauss, the numbers $u_1, dots, u_lambda, p - v_1, dots, p - v_mu$ are $1, dots, (p - 1) slash 2$ in some order. Summing over $j in S$,
  $ a sum_(j in S) j = p sum_(j in S) floor((j a) / p) + sum_i u_i + sum_i v_i, quad sum_(j in S) j = sum_i u_i + mu p - sum_i v_i. $
  Subtracting, $(a - 1) sum_(j in S) j = p (sum_(j in S) floor(j a slash p) - mu) + 2 sum_i v_i$. The left side is even because $a$ is odd, and $p$ is odd, so $sum_(j in S) floor(j a slash p) - mu$ is even.
]

#theorem(title: [Quadratic reciprocity law])[
  Let $p$ and $q$ be distinct odd primes. Then
  $ ls(p, q) = cases(-ls(q, p) & "if" p equiv q equiv -1 pmod(4), ls(q, p) & "otherwise".) $
  Equivalently, $ls(p, q) ls(q, p) = (-1)^((p - 1) / 2 dot (q - 1) / 2)$.
] <thm-qr>

#proof[
  The two forms are equivalent: both symbols are $plus.minus 1$, and $(p - 1) / 2 dot (q - 1) / 2$ is odd if and only if both factors are odd, that is, if and only if $p equiv q equiv -1 pmod(4)$.

  By @lem-gauss and @lem-parity-floor, $ls(q, p) = (-1)^A$ and $ls(p, q) = (-1)^B$ with
  $ A = sum_(j = 1)^((p - 1) slash 2) floor((j q) / p), quad B = sum_(k = 1)^((q - 1) slash 2) floor((k p) / q). $
  Consider the lattice points $(j, k)$ with $1 <= j <= (p - 1) slash 2$ and $1 <= k <= (q - 1) slash 2$; there are $(p - 1) / 2 dot (q - 1) / 2$ of them. None satisfies $q j = p k$, since $p divides.not q j$. For fixed $j$, the points with $k < q j slash p$ are those with $1 <= k <= floor(q j slash p)$, and $floor(q j slash p) <= (q - 1) slash 2$ because $q j slash p < q slash 2$. So $A$ counts the points with $q j > p k$, and symmetrically $B$ counts those with $q j < p k$. Hence $A + B = (p - 1) / 2 dot (q - 1) / 2$.
]

#example[
  Compute $ls(12, 31)$.
]

#solution[
  $ ls(12, 31) = ls(2^2 dot 3, 31) = ls(2, 31)^2 ls(3, 31) = ls(3, 31) = -ls(31, 3) = -ls(1, 3) = -1. $
  The fourth equality is @thm-qr with $3 equiv 31 equiv -1 pmod(4)$, and the fifth uses $31 equiv 1 pmod(3)$. Hence $x^2 equiv 12 pmod(31)$ has no solution.
]

#example[
  Compute $ls(1783, 7523)$, where $1783$ and $7523$ are primes.
]

#solution[
  $ ls(1783, 7523) = -ls(7523, 1783) = -ls(391, 1783) = ls(1783, 391) = ls(219, 391) = ls(3, 391) ls(73, 391). $
  The first equality is @thm-qr with $1783 equiv 7523 equiv -1 pmod(4)$, and the second uses $7523 = 4 dot 1783 + 391$. From here on $391 = 17 dot 23$ appears as a denominator, so the symbols with denominator $391$ are Jacobi symbols. The third equality is @thm-jacobi-rec with $391 equiv 1783 equiv -1 pmod(4)$, the fourth is @prop-jacobi 1) with $1783 = 4 dot 391 + 219$, and the fifth is @prop-jacobi 2) with $219 = 3 dot 73$.
  // [p5]
  $ ls(3, 391) ls(73, 391) = -ls(391, 3) ls(391, 73) = -ls(1, 3) ls(26, 73) = -ls(2, 73) ls(13, 73) = -ls(13, 73) \
    = -ls(73, 13) = -ls(8, 13) = -ls(2, 13)^3 = -(-1)^3 = 1. $
  The first equality is @thm-jacobi-rec with $3 equiv 391 equiv -1 pmod(4)$ and $73 equiv 1 pmod(4)$. The remaining symbols have prime denominators. We used $391 = 130 dot 3 + 1$, $391 = 5 dot 73 + 26$, $ls(2, 73) = 1$ since $73 equiv 1 pmod(8)$, @thm-qr with $13 equiv 1 pmod(4)$, $73 = 5 dot 13 + 8$, and $ls(2, 13) = -1$ since $13 equiv -3 pmod(8)$.
]

= The Jacobi symbol

#definition(title: [Jacobi symbol])[
  Let $n in NN$ be odd with $n > 1$, let $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$ with distinct primes $p_i$, and let $a in ZZ$ with $(a, n) = 1$. The _Jacobi symbol_ is
  $ ls(a, n) = ls(a, p_1)^(alpha_1) dots.c ls(a, p_r)^(alpha_r), $
  where the factors are Legendre symbols. For $n$ prime it coincides with the Legendre symbol, which justifies the notation.
]

#lemma[
  For odd integers $u$ and $v$,
  $ (u v - 1) / 2 equiv (u - 1) / 2 + (v - 1) / 2 pmod(2), quad (u^2 v^2 - 1) / 8 equiv (u^2 - 1) / 8 + (v^2 - 1) / 8 pmod(2). $
] <lem-parity-odd>

#proof[
  The differences are $(u - 1)(v - 1) slash 2$ and $(u^2 - 1)(v^2 - 1) slash 8$. In the first, $4 divides (u - 1)(v - 1)$. In the second, $8$ divides each of $u^2 - 1$ and $v^2 - 1$, since each is a product of two consecutive even numbers, so $64 divides (u^2 - 1)(v^2 - 1)$.
]

#proposition[
  Let $m, n in NN$ be odd with $m, n > 1$, and let $a, b in ZZ$.
  + If $(a, n) = 1$ and $a equiv b pmod(n)$, then $ls(a, n) = ls(b, n)$.
  + If $(a b, n) = 1$, then $ls(a b, n) = ls(a, n) ls(b, n)$.
  + $ls(-1, n) = 1$ if $n equiv 1 pmod(4)$, and $ls(-1, n) = -1$ if $n equiv -1 pmod(4)$.
  // [p4]
  + $ls(2, n) = 1$ if $n equiv plus.minus 1 pmod(8)$, and $ls(2, n) = -1$ if $n equiv plus.minus 3 pmod(8)$.
  + If $(a, m n) = 1$, then $ls(a, m n) = ls(a, m) ls(a, n)$.
] <prop-jacobi>

// [p5]
#proof[
  1) and 2) follow factor by factor from @prop-legendre 1) and 2), since $a equiv b pmod(n)$ implies $a equiv b pmod(p_i)$. 5) holds because the prime factorization of $m n$ is obtained by adding the exponents in those of $m$ and $n$.

  For 3) and 4), @prop-legendre gives $ls(-1, p) = (-1)^((p - 1) slash 2)$ and $ls(2, p) = (-1)^((p^2 - 1) slash 8)$ for odd primes $p$; for the second, $p equiv plus.minus 1 pmod(8)$ gives $p^2 equiv 1 pmod(16)$ and $p equiv plus.minus 3 pmod(8)$ gives $p^2 equiv 9 pmod(16)$. By @lem-parity-odd, $n mapsto (-1)^((n - 1) slash 2)$ and $n mapsto (-1)^((n^2 - 1) slash 8)$ are multiplicative on odd integers. Hence $ls(-1, n) = (-1)^((n - 1) slash 2)$ and $ls(2, n) = (-1)^((n^2 - 1) slash 8)$, and the same computations modulo $4$ and $16$ give the stated cases.
]

// [p4]
#theorem(title: [Reciprocity for the Jacobi symbol])[
  Let $m, n in NN$ be odd with $m, n > 1$ and $(m, n) = 1$. Then
  $ ls(m, n) = cases(-ls(n, m) & "if" n equiv m equiv -1 pmod(4), ls(n, m) & "otherwise".) $
] <thm-jacobi-rec>

#proof[
  As in @thm-qr, the claim is equivalent to $ls(m, n) ls(n, m) = (-1)^((m - 1) / 2 dot (n - 1) / 2)$. Write $m = p_1 dots.c p_s$ and $n = q_1 dots.c q_t$ as products of not necessarily distinct primes; $p_i != q_j$ since $(m, n) = 1$. By @prop-jacobi 2) and 5),
  $ ls(m, n) ls(n, m) = product_(i, j) ls(p_i, q_j) ls(q_j, p_i) = product_(i, j) (-1)^(P_i Q_j) = (-1)^((sum_i P_i)(sum_j Q_j)), $
  where $P_i = (p_i - 1) slash 2$, $Q_j = (q_j - 1) slash 2$, and the middle equality is @thm-qr. By @lem-parity-odd, $sum_i P_i equiv (m - 1) slash 2$ and $sum_j Q_j equiv (n - 1) slash 2 pmod(2)$.
]

#example[
  Compute $ls(31, 95)$.
]

#solution[
  $ls(31, 95) = -ls(95, 31) = -ls(2, 31) = -1$, by @thm-jacobi-rec with $31 equiv 95 equiv -1 pmod(4)$, then $95 = 3 dot 31 + 2$, and $ls(2, 31) = 1$ since $31 equiv -1 pmod(8)$.
]

#example[
  Compute $ls(60, 101)$.
]

#solution[
  $ ls(60, 101) = ls(2^2 dot 15, 101) = ls(2, 101)^2 ls(15, 101) = ls(15, 101) = ls(101, 15) \
    = ls(11, 15) = -ls(15, 11) = -ls(4, 11) = -ls(2, 11)^2 = -1. $
  The fourth equality is @thm-jacobi-rec with $101 equiv 1 pmod(4)$, the fifth uses $101 = 6 dot 15 + 11$, and the sixth is @thm-jacobi-rec with $11 equiv 15 equiv -1 pmod(4)$.
]

#remark[
  If $x^2 equiv a pmod(n)$ is solvable, then $a$ is a quadratic residue modulo every prime divisor of $n$, so $ls(a, n) = 1$. Hence $ls(a, n) = -1$ implies that $x^2 equiv a pmod(n)$ has no solution. The converse fails: $ls(2, 15) = ls(2, 3) ls(2, 5) = (-1)(-1) = 1$, but $x^2 equiv 2 pmod(3)$ has no solution, so neither has $x^2 equiv 2 pmod(15)$.
]

= Polynomial congruences and Hensel's lemma

#definition(title: [Polynomial congruence])[
  Let $f(x) = a_n x^n + dots.c + a_1 x + a_0$ with $a_i in ZZ$ and $a_n != 0$, and let $m in NN$. A _polynomial congruence_ is a congruence $f(x) equiv 0 pmod(m)$.
]

// [p3]
Let $p$ be a prime. Starting from a solution of $f(x) equiv 0 pmod(p)$, we lift it to solutions modulo $p^k$. Here $f'$ denotes the formal derivative of $f$, which again lies in $ZZ[x]$.

#theorem(title: [Hensel])[
  Let $f in ZZ[x]$, $p$ a prime, and $c in ZZ$ with $f(c) equiv 0 pmod(p)$ and $f'(c) equiv.not 0 pmod(p)$. Then for every $k in NN$ the congruence $f(x) equiv 0 pmod(p^k)$ has exactly one solution $x equiv c_k pmod(p^k)$ with $c_k equiv c pmod(p)$.
] <thm-hensel>

#lemma[
  Let $f in ZZ[x]$, $p$ a prime, $a, t in ZZ$ and $j in NN$. Then
  $ f(a + t p^j) equiv f(a) + t p^j f'(a) pmod(p^(j + 1)). $
] <lem-hensel>

#proof[
  For a polynomial of degree $n$ the Taylor expansion is exact:
  $ f(a + t p^j) = f(a) + t p^j f'(a) + t^2 p^(2 j) (f''(a)) / (2!) + dots.c + t^n p^(n j) (f^((n))(a)) / (n!). $
  Each $f^((r))(a) slash r!$ is an integer, because $(x^s)^((r)) = s(s - 1) dots.c (s - r + 1) x^(s - r)$ and $s(s - 1) dots.c (s - r + 1) slash r! = binom(s, r)$. Every term with $r >= 2$ is divisible by $p^(2 j)$, and $2 j >= j + 1$ since $j >= 1$.
]

#proof(title: [Proof of @thm-hensel])[
  We proceed by induction on $k$. For $k = 1$, $c_1 = c$ is a solution, and every solution congruent to $c$ modulo $p$ is congruent to $c_1$.

  Let $k >= 2$ and assume that $f(x) equiv 0 pmod(p^(k - 1))$ has exactly one solution $x equiv c_(k - 1) pmod(p^(k - 1))$ with $c_(k - 1) equiv c pmod(p)$.
  // [p2]
  Let $x$ be a solution of $f(x) equiv 0 pmod(p^k)$ with $x equiv c pmod(p)$. Then $f(x) equiv 0 pmod(p^(k - 1))$, so $x equiv c_(k - 1) pmod(p^(k - 1))$ by the uniqueness in the induction hypothesis, that is, $x = c_(k - 1) + t p^(k - 1)$ with $t in ZZ$. By @lem-hensel with $j = k - 1 >= 1$,
  $ f(c_(k - 1) + t p^(k - 1)) equiv f(c_(k - 1)) + t p^(k - 1) f'(c_(k - 1)) pmod(p^k). $
  By the induction hypothesis $p^(k - 1) divides f(c_(k - 1))$, and $f'(c_(k - 1)) equiv f'(c) pmod(p)$ since $c_(k - 1) equiv c pmod(p)$ and $f' in ZZ[x]$. Hence $f(c_(k - 1) + t p^(k - 1)) equiv 0 pmod(p^k)$ if and only if
  $ f(c_(k - 1)) / p^(k - 1) + t f'(c) equiv 0 pmod(p). $
  This is a linear congruence modulo $p$ in $t$, and $f'(c) equiv.not 0 pmod(p)$, so by @rem-linear it has exactly one solution $t equiv t_0 pmod(p)$.
  // [p1]
  Writing $t = t_0 + s p$ with $s in ZZ$,
  $ x = c_(k - 1) + (t_0 + s p) p^(k - 1) = c_(k - 1) + t_0 p^(k - 1) + s p^k, $
  so every such solution satisfies $x equiv c_(k - 1) + t_0 p^(k - 1) pmod(p^k)$. Conversely, $c_k = c_(k - 1) + t_0 p^(k - 1)$ is a solution, and $c_k equiv c_(k - 1) equiv c pmod(p)$. Hence the solution is unique modulo $p^k$.
]
