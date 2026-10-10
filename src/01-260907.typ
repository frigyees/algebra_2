#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 01-260907 · order, primitive roots, index, quadratic residues
// HEADINGS all three coined
// CORRECTIONS
//   [p1] "under RH, n(p) < c (ln p)^2" -> Shoup's GRH bound; (log p)^2 alone is Ankeny's bound for the least non-residue
//   [p1] checking step: exponent (p-1)/q_1 -> (p-1)/q_i
//   [p3] "no effective algorithm is known" -> no polynomial-time classical algorithm is known
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: definition of order; recalled phi formula, Euler-Fermat, Lagrange
//   [p1] A: primitive root defined for a in Z (source: Z^+), as all later statements use g in Z
//   [p1] A: d >= 0 (not d > 0) in the order proof; m >= 2 and alpha >= 1 in the existence theorem;
//        existence hypothesis in the counting theorem; n >= 3 in the phi estimate; c = c(eps) in Burgess
//   [p1] A: lemma on the order of a power; proofs of the mod-12 remark, the counting theorem, the checking procedure
//   [p1] B: proof of the existence theorem
//   [p1] C: phi estimate, Burgess, Shoup, prime number theorem
//   [p2] A: definition of a reduced residue system (margin); hypothesis (g, m) = 1 in the residue-system theorem
//        (false for m = 2 without it); p ∤ a in the index definition and theorem; converse directions in proofs
//   [p3] A: statement of the cyclic-group remark

// [p1]
= Order and primitive roots

#remark(title: [Recall])[
  Let $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$ with distinct primes $p_i$ and $alpha_i in NN$. Then $phi(n) = n product_(i=1)^r (1 - 1/p_i)$, and $phi$ is multiplicative. If $m in NN$, $a in ZZ$ and $(a, m) = 1$, then $a^(phi(m)) equiv 1 pmod(m)$ (Euler--Fermat).
] <rem-recall-phi>

#definition(title: [Order])[
  Let $m in NN$ and $a in ZZ$ with $(a, m) = 1$. The _order_ of $a$ modulo $m$, denoted $ord(m, a)$, is the least $k in NN$ with $a^k equiv 1 pmod(m)$. It exists by @rem-recall-phi.
]

#proposition[
  Let $m in NN$, $a in ZZ$ with $(a, m) = 1$, and $k, s, t in ZZ_(>= 0)$. Then:
  + $a^k equiv 1 pmod(m)$ if and only if $ord(m, a) divides k$. In particular $ord(m, a) divides phi(m)$.
  + $a^s equiv a^t pmod(m)$ if and only if $s equiv t pmod(ord(m, a))$.
] <prop-order>

#proof[
  Write $d = ord(m, a)$.

  1) If $d divides k$, then $k = d e$ with $e in ZZ_(>= 0)$, and $a^k = (a^d)^e equiv 1 pmod(m)$. Conversely, let $a^k equiv 1 pmod(m)$ and write $k = q d + r$ with $q in ZZ_(>= 0)$ and $0 <= r < d$. Then $1 equiv a^k = (a^d)^q a^r equiv a^r pmod(m)$. Since $r < d$ and $d$ is the least positive exponent with this property, $r = 0$, so $d divides k$. The particular case follows from @rem-recall-phi.

  2) By symmetry assume $s >= t$. Since $(a, m) = 1$, $a^t$ is invertible modulo $m$. Hence $a^s equiv a^t pmod(m)$ holds if and only if $a^(s - t) equiv 1 pmod(m)$, which by 1) holds if and only if $d divides s - t$, that is, $s equiv t pmod(d)$.
]

#example[
  Compute $ord(23, 5)$.
]

#solution[
  By @prop-order, $ord(23, 5) divides phi(23) = 22$, so $ord(23, 5) in {1, 2, 11, 22}$. Here $5 equiv.not 1$ and $5^2 = 25 equiv 2 equiv.not 1 pmod(23)$. For $5^11$ use $11 = (1011)_2 = 8 + 2 + 1$ and repeated squaring: $5^2 equiv 2$, $5^4 equiv 4$, $5^8 equiv 16 pmod(23)$. Thus
  $ 5^11 = 5^8 dot 5^2 dot 5 equiv 16 dot 2 dot 5 = 160 equiv -1 pmod(23), $
  since $160 = 7 dot 23 - 1$. Hence $5^11 equiv.not 1$ and $ord(23, 5) = 22$.
]

#definition(title: [Primitive root])[
  Let $m in NN$. An integer $a in ZZ$ with $(a, m) = 1$ is a _primitive root_ modulo $m$ if $ord(m, a) = phi(m)$.
]

#lemma[
  Let $m in NN$, $a in ZZ$ with $(a, m) = 1$, $d = ord(m, a)$ and $j in ZZ_(>= 0)$. Then $ord(m, a^j) = d slash (j, d)$.
] <lem-power-order>

#proof[
  Let $e = (j, d)$. For $k in NN$, @prop-order gives $(a^j)^k equiv 1 pmod(m)$ if and only if $d divides j k$, that is, $d slash e divides (j slash e) k$. Since $(d slash e, j slash e) = 1$, this holds if and only if $d slash e divides k$. The least such $k$ is $d slash e$.
]

#remark(title: [Recall])[
  Let $p$ be a prime and $f in ZZ[x]$ a polynomial of degree $n >= 1$ whose leading coefficient is not divisible by $p$. Then $f(x) equiv 0 pmod(p)$ has at most $n$ pairwise incongruent solutions (Lagrange).
] <rem-lagrange>

#theorem[
  Let $m >= 2$. There exists a primitive root modulo $m$ if and only if $m = 2$, $m = 4$, $m = p^alpha$ or $m = 2 p^alpha$, where $p$ is an odd prime and $alpha in NN$.
] <thm-prim-exist>

#proof[
  *The cases $m = 2, 4$.* $ord(2, 1) = 1 = phi(2)$. Since $3 equiv.not 1$ and $3^2 = 9 equiv 1 pmod(4)$, $ord(4, 3) = 2 = phi(4)$.

  *The case $m = p$, $p$ an odd prime.* For $d divides p - 1$ let $psi(d)$ be the number of residues $a$ modulo $p$ with $p divides.not a$ and $ord(p, a) = d$. By @prop-order every such order divides $p - 1$, so $sum_(d divides p - 1) psi(d) = p - 1$. Let $d divides p - 1$ with $psi(d) >= 1$, and let $a$ have order $d$. By @prop-order the residues $1, a, dots, a^(d - 1)$ are pairwise incongruent, and they are roots of $x^d - 1$. By @rem-lagrange, $x^d - 1$ has no other roots modulo $p$, so every residue of order $d$ is congruent to some $a^j$ with $0 <= j < d$. By @lem-power-order, $a^j$ has order $d$ if and only if $(j, d) = 1$. Hence $psi(d) = phi(d)$ whenever $psi(d) >= 1$, and so $psi(d) <= phi(d)$ for every $d divides p - 1$. Since $sum_(d divides p - 1) phi(d) = p - 1$ by @thm-phi-sum, equality holds for every $d$. In particular $psi(p - 1) = phi(p - 1) >= 1$.

  *The case $m = p^alpha$, $p$ an odd prime, $alpha >= 2$.* Let $g$ be a primitive root modulo $p$. We may assume $g^(p - 1) equiv.not 1 pmod(p^2)$. Indeed, $g + p$ is also a primitive root modulo $p$, and by the binomial theorem
  $ (g + p)^(p - 1) equiv g^(p - 1) + (p - 1) p g^(p - 2) equiv g^(p - 1) - p g^(p - 2) pmod(p^2). $
  If $g^(p - 1) equiv 1 pmod(p^2)$, then $(g + p)^(p - 1) equiv 1 - p g^(p - 2) equiv.not 1 pmod(p^2)$, because $p divides.not g$; in that case replace $g$ by $g + p$.

  So $g^(p - 1) = 1 + p u$ with $p divides.not u$. We claim that for every $k in NN$ there is $u_k in ZZ$ with $p divides.not u_k$ and $g^((p - 1) p^(k - 1)) = 1 + p^k u_k$. For $k = 1$ take $u_1 = u$. If the claim holds for $k$, then
  $ g^((p - 1) p^k) = (1 + p^k u_k)^p = 1 + p^(k + 1) u_k + sum_(i = 2)^p binom(p, i) p^(i k) u_k^i. $
  For $2 <= i <= p - 1$ the prime $p$ divides $binom(p, i)$, so the term is divisible by $p^(2 k + 1)$, and $2 k + 1 >= k + 2$. The term $i = p$ is divisible by $p^(p k)$, and $p k >= 3 k >= k + 2$. Hence the sum equals $p^(k + 2) w$ with $w in ZZ$, and $u_(k + 1) = u_k + p w$ is not divisible by $p$.

  Now let $d = ord(p^alpha, g)$. From $g^d equiv 1 pmod(p)$ and @prop-order modulo $p$ we get $p - 1 divides d$. Also $d divides phi(p^alpha) = (p - 1) p^(alpha - 1)$. Hence $d = (p - 1) p^i$ with $0 <= i <= alpha - 1$. If $i <= alpha - 2$, then $d divides (p - 1) p^(alpha - 2)$ and so $g^((p - 1) p^(alpha - 2)) equiv 1 pmod(p^alpha)$. By the claim with $k = alpha - 1$, however, $g^((p - 1) p^(alpha - 2)) = 1 + p^(alpha - 1) u_(alpha - 1)$ with $p divides.not u_(alpha - 1)$, which is not congruent to $1$ modulo $p^alpha$. Hence $d = phi(p^alpha)$.

  *The case $m = 2 p^alpha$, $p$ an odd prime, $alpha >= 1$.* Let $g$ be a primitive root modulo $p^alpha$. Replacing $g$ by $g + p^alpha$ if necessary, $g$ is odd; it remains a primitive root modulo $p^alpha$, and $(g, 2 p^alpha) = 1$. If $g^d equiv 1 pmod(2 p^alpha)$, then $g^d equiv 1 pmod(p^alpha)$, so $phi(p^alpha) divides d$. Since $phi(2 p^alpha) = phi(p^alpha)$, @prop-order gives $ord(2 p^alpha, g) = phi(2 p^alpha)$.

  *No primitive root otherwise.* Let $m >= 2$ be of none of the listed forms, and write $m = 2^beta n$ with $n$ odd. If $n = 1$, then $beta >= 3$. If $n$ has two distinct prime divisors, write $n = p^alpha n'$ with $p divides.not n'$ and $n' >= 3$, and put $m_1 = 2^beta p^alpha$, $m_2 = n'$. If $n = p^alpha$, then $beta >= 2$; put $m_1 = 2^beta$, $m_2 = p^alpha$. So either $m = 2^beta$ with $beta >= 3$, or $m = m_1 m_2$ with $(m_1, m_2) = 1$ and $m_1, m_2 >= 3$.

  In the first case, $a^(2^(k - 2)) equiv 1 pmod(2^k)$ for every odd $a$ and every $k >= 3$. For $k = 3$, $a^2 - 1 = (a - 1)(a + 1)$ is a product of two consecutive even numbers, hence divisible by $8$. If $a^(2^(k - 2)) = 1 + 2^k t$, then $a^(2^(k - 1)) = 1 + 2^(k + 1) t + 2^(2 k) t^2 equiv 1 pmod(2^(k + 1))$. Hence $ord(2^beta, a) <= 2^(beta - 2) < 2^(beta - 1) = phi(2^beta)$.

  In the second case, note that $phi(n)$ is even for $n >= 3$: if an odd prime $p$ divides $n$, then $p - 1 divides phi(n)$ by @rem-recall-phi; otherwise $n = 2^gamma$ with $gamma >= 2$ and $phi(n) = 2^(gamma - 1)$. Let $L$ be the least common multiple of $phi(m_1)$ and $phi(m_2)$. Both are even, so $L <= phi(m_1) phi(m_2) slash 2 = phi(m) slash 2$. For $(a, m) = 1$, Euler--Fermat gives $a^L equiv 1$ modulo $m_1$ and modulo $m_2$, hence modulo $m = m_1 m_2$. So $ord(m, a) <= L < phi(m)$.
]

#remark[
  There is no primitive root modulo $12$. Indeed, $phi(12) = 4$, and each of $1, 5, 7, 11$ has square congruent to $1$ modulo $12$, so every order is at most $2$.
]

#theorem[
  Let $m >= 2$ and suppose that $g$ is a primitive root modulo $m$. Then the primitive roots modulo $m$ are, up to congruence, exactly the powers $g^j$ with $1 <= j <= phi(m)$ and $(j, phi(m)) = 1$. Hence there are $phi(phi(m))$ of them. In particular, for a prime $p$ there are $phi(phi(p)) = phi(p - 1)$ primitive roots modulo $p$.
] <thm-prim-count>

#proof[
  A primitive root $a$ satisfies $(a, m) = 1$. By @thm-rrs and $g^(phi(m)) equiv 1 = g^0 pmod(m)$, $a$ is congruent to exactly one $g^j$ with $1 <= j <= phi(m)$. By @lem-power-order, $ord(m, g^j) = phi(m) slash (j, phi(m))$, which equals $phi(m)$ if and only if $(j, phi(m)) = 1$. The number of such $j$ is $phi(phi(m))$.
]

#theorem(cited: true)[
  There is a constant $c > 0$ such that $phi(n) > c n slash log log n$ for every $n >= 3$.
]

#procedure(title: [Checking primitive roots])[
  Let $p$ be a prime and $g in ZZ$ with $p divides.not g$.
  + Compute the prime divisors $q_1, dots, q_s$ of $p - 1$.
  + Check that $g^((p - 1) slash q_i) equiv.not 1 pmod(p)$ for every $1 <= i <= s$.
  Then $g$ is a primitive root modulo $p$ if and only if every check in step 2 succeeds.
] <proc-prim>

#proof[
  If $g$ is a primitive root, then $ord(p, g) = p - 1$ does not divide $(p - 1) slash q_i < p - 1$, so $g^((p - 1) slash q_i) equiv.not 1$ by @prop-order. Conversely, suppose $d = ord(p, g) < p - 1$. Since $d divides p - 1$, the quotient $(p - 1) slash d > 1$ has a prime divisor $q_i$, and then $d divides (p - 1) slash q_i$, so $g^((p - 1) slash q_i) equiv 1 pmod(p)$.
]

#theorem(title: [Burgess], cited: true)[
  For a prime $p$ let $n(p)$ be the least primitive root modulo $p$ in $NN$. For every $epsilon > 0$ there is $c(epsilon) > 0$ such that $n(p) < c(epsilon) p^(1 slash 4 + epsilon)$ for all primes $p$.
]

#theorem(title: [Shoup], cited: true)[
  Assume the generalized Riemann hypothesis for Dirichlet $L$-functions. Then there is an absolute constant $c > 0$ such that for every prime $p >= 3$
  $ n(p) <= c omega(p - 1)^4 (log omega(p - 1) + 1)^4 (log p)^2, $
  where $omega(k)$ is the number of distinct prime divisors of $k$. In particular $n(p) = O((log p)^6)$.
]

#theorem(title: [Prime number theorem], cited: true)[
  Let $pi(x)$ be the number of primes not exceeding $x$. There is $c > 0$ such that
  $ pi(x) = integral_2^x (d t) / (log t) + O(x e^(-c sqrt(log x))) quad (x -> infinity). $
  If the Riemann hypothesis holds, the error term is $O(sqrt(x) log x)$.
]

// [p2]
#definition(title: [Reduced residue system])[
  Let $m in NN$. Integers $a_1, dots, a_(phi(m))$ form a _reduced residue system_ modulo $m$ if $(a_i, m) = 1$ for every $i$ and $a_i equiv.not a_j pmod(m)$ for all $i != j$. Such a system contains exactly one element of each residue class coprime to $m$, since there are $phi(m)$ such classes.
]

#theorem[
  Let $m in NN$ and $g in ZZ$ with $(g, m) = 1$. Then $g$ is a primitive root modulo $m$ if and only if $1, g, g^2, dots, g^(phi(m) - 1)$ form a reduced residue system modulo $m$.
] <thm-rrs>

#proof[
  Every power of $g$ is coprime to $m$. Suppose $g$ is a primitive root and $g^i equiv g^j pmod(m)$ with $0 <= j <= i <= phi(m) - 1$. By @prop-order, $i equiv j pmod(phi(m))$, and $0 <= i - j < phi(m)$ forces $i = j$. So the $phi(m)$ powers are pairwise incongruent.

  Conversely, if the powers form a reduced residue system, then $g^j equiv.not g^0 = 1 pmod(m)$ for $1 <= j <= phi(m) - 1$, because they are pairwise incongruent. Hence $ord(m, g) >= phi(m)$, and $ord(m, g) divides phi(m)$ by @prop-order, so $ord(m, g) = phi(m)$.
]

= The index

#definition(title: [Index, discrete logarithm])[
  Let $p$ be a prime, $g$ a primitive root modulo $p$, and $a in ZZ$ with $p divides.not a$. The _index_ or _discrete logarithm_ of $a$ to the base $g$ modulo $p$ is the unique $k$ with $1 <= k <= p - 1$ and $g^k equiv a pmod(p)$. It is denoted $ind_g a$. Existence and uniqueness follow from @thm-rrs, since $g^(p - 1) equiv 1 = g^0 pmod(p)$.
]

#proposition[
  Let $p$ be a prime and $g$ a primitive root modulo $p$. For $i, j in ZZ_(>= 0)$, $g^i equiv g^j pmod(p)$ if and only if $i equiv j pmod(p - 1)$. For $a, b in ZZ$ with $p divides.not a b$, $a equiv b pmod(p)$ if and only if $ind_g a equiv ind_g b pmod(p - 1)$.
] <prop-ind>

#proof[
  The first statement is @prop-order 2) with $ord(p, g) = phi(p) = p - 1$. For the second, $a equiv b pmod(p)$ holds if and only if $g^(ind_g a) equiv g^(ind_g b) pmod(p)$, and the first statement applies.
]

#theorem[
  Let $p$ be a prime, $g$ and $h$ primitive roots modulo $p$, $a, b in ZZ$ with $p divides.not a b$, and $n in ZZ_(>= 0)$. Then, modulo $p - 1$:
  + $ind_g (a b) equiv ind_g a + ind_g b$,
  + $ind_g (a^n) equiv n ind_g a$,
  + $ind_h a equiv ind_h g dot ind_g a$.
] <thm-ind>

#proof[
  1) $g^(ind_g (a b)) equiv a b$ and $g^(ind_g a + ind_g b) = g^(ind_g a) g^(ind_g b) equiv a b pmod(p)$; apply @prop-ind.

  2) $g^(ind_g (a^n)) equiv a^n$ and $g^(n ind_g a) = (g^(ind_g a))^n equiv a^n pmod(p)$; apply @prop-ind.

  3) $h^(ind_h a) equiv a equiv g^(ind_g a) equiv (h^(ind_h g))^(ind_g a) = h^(ind_h g dot ind_g a) pmod(p)$; apply @prop-ind with base $h$.
]

#remark[
  Indices are computed with an index table: list $g^n$ modulo $p$ for $n = 1, dots, p - 1$ and read the table in reverse.
]

#example[
  Find a primitive root $g$ modulo $17$ and compute $ind_g 11$.
]

#solution[
  Here $phi(17) = 16$, whose only prime divisor is $2$, so by @proc-prim an integer $g$ with $17 divides.not g$ is a primitive root if and only if $g^8 equiv.not 1 pmod(17)$. Since $2^8 = 256 = 15 dot 17 + 1 equiv 1$, the integer $2$ is not a primitive root. Since $3^4 = 81 equiv -4$ and $3^8 equiv 16 equiv -1 pmod(17)$, the integer $3$ is a primitive root. The powers of $3$ modulo $17$ are:
  #align(center, table(
    columns: 17,
    $n$, ..range(1, 17).map(n => [#n]),
    $3^n$, ..(3, 9, 10, 13, 5, 15, 11, 16, 14, 8, 7, 4, 12, 2, 6, 1).map(v => [#v]),
  ))
  Reading the table in reverse, $ind_3 11 = 7$.
]

// [p3]
#remark(title: [Discrete logarithm problem])[
  Given a prime $p$, a primitive root $g$ modulo $p$ and an integer $k$ with $1 <= k <= p - 1$, find $x$ with $1 <= x <= p - 1$ and $g^x equiv k pmod(p)$. No classical algorithm solving this problem in time polynomial in $log p$ is known.
]

#remark[
  The index generalizes to any finite cyclic group $G = chevron.l g chevron.r$ of order $N$: for $b in G$, $ind_g b$ is the unique $k$ with $1 <= k <= N$ and $g^k = b$. The discrete logarithm problem is posed in the same way.
]

= Binomial congruences and quadratic residues

#definition(title: [Quadratic residue])[
  Let $p > 2$ be a prime and $a in ZZ$ with $(a, p) = 1$. Then $a$ is a _quadratic residue_ modulo $p$ if $x^2 equiv a pmod(p)$ has a solution, and a _quadratic non-residue_ otherwise.
]
