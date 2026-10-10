#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 04-260918 · p-adic numbers, p-adic metric, Ostrowski, completion (translated from Hungarian)
// HEADINGS sections 8, 9 from source
// DROPPED
//   [p1] phi = mu * id example: repeats 03-260914 p3; [p3] literature list
// CORRECTIONS
//   [p1] 3^2 - 2 + 14 a_1 -> 3^2 - 2 + 14 * 3 a_1 (the stated conclusion 1 + 6 a_1 = 0 already uses it)
//   [p2] |xy| <= |x||y| -> |xy| = |x||y|
// READINGS
//   [p2] second root read as 4 + 5*7 + 4*7^2; 4 is the value forced by alpha + alpha' = 0
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: truncations and their compatibility; operations on Z_p via truncations; ring structure
//   [p1] A: embedding of Z; verification of -3/2 in Z_3; proof of the a/b observation
//   [p1] A: operations on Q_p, field property, units of Z_p; embedding of Q
//   [p1] A: existence of the square root of 2 via Hensel
//   [p2] A: Q_infinity = R; C: Hasse-Minkowski
//   [p2] A: |1| = |-1| = 1 and the metric axioms; well-definedness and properties of v_p; proof that |.|_p is an absolute value
//   [p3] A: trivial absolute value; B: proof of Ostrowski's theorem (conclusion |.| = |.|_*^c, which gives equivalence)
//   [p3] B: extension of |.|_p to Q_p, density of Q, completeness, Z_p as unit ball, Q not complete

// [p1]
= $p$-adic numbers

Let $p$ be a prime. Every $n in ZZ_(>= 0)$ has a unique expansion $n = a_0 + a_1 p + dots.c + a_k p^k$ with $0 <= a_i < p$.

#definition(title: [$p$-adic integer])[
  A _$p$-adic integer_ is a formal series $alpha = a_0 + a_1 p + a_2 p^2 + dots.c$ with digits $a_i in {0, 1, dots, p - 1}$. The set of $p$-adic integers is denoted $ZZ_p$. For $k in NN$ the _truncation_ of $alpha$ is $alpha_k = sum_(i = 0)^(k - 1) a_i p^i$.
]

#remark[
  Let $(y_k)_(k >= 1)$ be integers with $y_(k + 1) equiv y_k pmod(p^k)$ for every $k$. Then there is exactly one $alpha in ZZ_p$ with $alpha_k equiv y_k pmod(p^k)$ for every $k$. Indeed, let $x_k$ be the least non-negative residue of $y_k$ modulo $p^k$. Then $x_(k + 1) equiv x_k pmod(p^k)$ and $0 <= x_k < p^k$ give $x_(k + 1) = x_k + a_k p^k$ with $0 <= a_k < p$, and $alpha = sum_k a_k p^k$ is the required series. Uniqueness holds because $0 <= alpha_k < p^k$ determines $alpha_k$ from its residue, and the truncations determine the digits.
] <rem-truncations>

#definition(title: [Operations on $ZZ_p$])[
  For $alpha, beta in ZZ_p$, the sum $alpha + beta$ and the product $alpha beta$ are the $p$-adic integers with
  $ (alpha + beta)_k equiv alpha_k + beta_k pmod(p^k), quad (alpha beta)_k equiv alpha_k beta_k pmod(p^k) quad (k in NN). $
  They exist and are unique by @rem-truncations, since the sequences $alpha_k + beta_k$ and $alpha_k beta_k$ satisfy its compatibility condition. Each ring axiom holds modulo every $p^k$, so $ZZ_p$ is a commutative ring with zero $0 + 0 p + dots.c$ and identity $1 + 0 p + dots.c$.
]

#example[
  $-1 = (p - 1) + (p - 1) p + (p - 1) p^2 + dots.c$ in $ZZ_p$, because the truncations of the right side are $(p - 1)(1 + p + dots.c + p^(k - 1)) = p^k - 1 equiv -1 pmod(p^k)$.
]

#example[
  Let $alpha, beta in ZZ_3$ with $alpha = 2 + 1 dot 3 + dots.c$ and $beta = 1 + 2 dot 3 + dots.c$. Then $(alpha + beta)_1 equiv 2 + 1 equiv 0 pmod(3)$. Further $alpha_2 = 5$ and $beta_2 = 7$, so $(alpha + beta)_2 equiv 12 equiv 3 pmod(3^2)$. Hence $alpha + beta = 0 + 1 dot 3 + dots.c$.
]

#remark[
  $ZZ subset ZZ_p$: the integer $n$ is identified with the $p$-adic integer whose truncations satisfy $alpha_k equiv n pmod(p^k)$. For $n >= 0$ this is the base-$p$ expansion of $n$ followed by zero digits. The map is an injective ring homomorphism, since distinct integers differ modulo $p^k$ for large $k$.
]

#example[
  The equation $2 x + 3 = 0$ has no solution in $ZZ$, but it has one in $ZZ_3$. Formally,
  $ -3 / 2 = 3 / (-2) = 3 / (1 - 3) = 3 dot 1 / (1 - 3) = 3 (1 + 3 + 3^2 + dots.c), $
  which suggests $gamma = 0 + 1 dot 3 + 1 dot 3^2 + dots.c$. Indeed, $gamma_k = 3 + 3^2 + dots.c + 3^(k - 1) = (3^k - 3) slash 2$, so $2 gamma_k + 3 = 3^k equiv 0 pmod(3^k)$ for every $k$, and $2 gamma + 3 = 0$ in $ZZ_3$.
]

#remark[
  Let $x = a slash b$ with $a, b in ZZ$ and $p divides.not b$. Then there is exactly one $xi in ZZ_p$ with $b xi = a$, and we write $xi = a slash b$. Indeed, $b$ is invertible modulo every $p^k$; if $b_k^(-1)$ denotes an inverse modulo $p^k$, then $y_k = a b_k^(-1)$ satisfies $y_(k + 1) equiv y_k pmod(p^k)$, and the $xi$ of @rem-truncations satisfies $(b xi)_k equiv a pmod(p^k)$ for all $k$. If $b xi = b xi'$, then $b (xi - xi')_k equiv 0 pmod(p^k)$, so $(xi - xi')_k = 0$ for all $k$ and $xi = xi'$.
] <rem-ab-in-zp>

#definition(title: [$p$-adic number])[
  A _$p$-adic number_ is a formal series $x = sum_(k = -N)^infinity a_k p^k$ with $N in ZZ_(>= 0)$ and digits $a_k in {0, dots, p - 1}$; series that differ only by leading zero digits are identified. The set of $p$-adic numbers is denoted $QQ_p$, and $ZZ_p subset QQ_p$ consists of the series with $a_k = 0$ for $k < 0$.
]

#proposition[
  For $alpha in ZZ_p$ and $N in ZZ_(>= 0)$ let $p^(-N) alpha$ denote the series whose digit at $p^(k - N)$ is the digit of $alpha$ at $p^k$. Every $x in QQ_p$ has this form, and $p^(-N) alpha = p^(-N - 1) (p alpha)$. Define
  $ p^(-N) alpha + p^(-N) beta = p^(-N) (alpha + beta), quad (p^(-N) alpha)(p^(-N) beta) = p^(-2 N) (alpha beta). $
  Then $QQ_p$ is a field containing $ZZ_p$ as a subring. An element $u in ZZ_p$ is a unit of $ZZ_p$ if and only if its digit $a_0$ is nonzero, and every $x in QQ_p$ with $x != 0$ can be written uniquely as $x = p^v u$ with $v in ZZ$ and $u$ a unit of $ZZ_p$.
] <prop-qp-field>

#proof[
  Multiplication by $p$ in $ZZ_p$ shifts the digits up by one, since $(p alpha)_(k + 1) = p alpha_k$. This gives $p^(-N) alpha = p^(-N - 1)(p alpha)$, so the definitions do not depend on the choice of a common $N$, and the ring axioms follow from those of $ZZ_p$.

  If $u$ has $a_0 != 0$, then every $u_k$ is coprime to $p$. Let $w_k$ be an inverse of $u_k$ modulo $p^k$; then $w_(k + 1) equiv w_k pmod(p^k)$, and the resulting $w in ZZ_p$ satisfies $(u w)_k equiv 1$ for all $k$, so $u w = 1$. Conversely, $u w = 1$ gives $u_1 w_1 equiv 1 pmod(p)$, so $a_0 = u_1 != 0$.

  For $x != 0$ let $v$ be the least index of a nonzero digit. Shifting the digits gives $x = p^v u$ with $u in ZZ_p$ whose digit $a_0$ is nonzero, so $u$ is a unit, and $v$ and $u$ are determined by $x$. Then $x^(-1) = p^(-v) u^(-1)$, so $QQ_p$ is a field.
]

#remark[
  $QQ subset QQ_p$: every nonzero rational number is $p^v a slash b$ with $v in ZZ$ and $p divides.not a b$, and $a slash b in ZZ_p$ by @rem-ab-in-zp. This gives an injective field homomorphism $QQ -> QQ_p$.
]

#example[
  Is $x^2 - 2 = 0$ solvable in $ZZ_7$?
] <ex-sqrt2>

#solution[
  Let $alpha = a_0 + a_1 dot 7 + a_2 dot 7^2 + dots.c$ be a solution. Then $a_0^2 equiv 2 pmod(7)$, so $a_0 = 3$ or $a_0 = 4$, that is, $alpha_1 = 3$ or $alpha_1 = 4$.

  Let $alpha_1 = 3$. We seek $alpha_2 = a_0 + a_1 dot 7$ modulo $49$:
  $ alpha_2^2 - 2 = (a_0 + a_1 dot 7)^2 - 2 = a_0^2 - 2 + 2 dot 7 a_0 a_1 + a_1^2 7^2 equiv 0 pmod(7^2) $
  if and only if $a_0^2 - 2 + 14 a_0 a_1 equiv 0 pmod(7^2)$, that is, $3^2 - 2 + 14 dot 3 a_1 equiv 0 pmod(49)$, which gives $1 + 6 a_1 equiv 0 pmod(7)$ and $a_1 = 1$.
  // [p2]
  Continuing recursively, $alpha = 3 + 1 dot 7 + 2 dot 7^2 + 6 dot 7^3 + dots.c$. The other solution is $alpha = 4 + 5 dot 7 + 4 dot 7^2 + dots.c$.

  Both solutions exist: $f(x) = x^2 - 2$ has $f'(3) = 6 equiv.not 0$ and $f'(4) = 8 equiv.not 0 pmod(7)$, so @thm-hensel gives compatible solutions $c_k$ modulo $7^k$, and by @rem-truncations they define $alpha in ZZ_7$ with $(alpha^2 - 2)_k = 0$ for every $k$, that is, $alpha^2 = 2$.
]

#remark[
  Write $QQ_infinity = RR$, and let $p <= infinity$ range over the primes and $infinity$. If a polynomial equation with rational coefficients has a solution in $QQ$, then it has a solution in $QQ_p$ for every $p <= infinity$, since $QQ subset QQ_p$.
]

#theorem(title: [Hasse--Minkowski], cited: true)[
  Let $f(x_1, dots, x_n) in QQ[x_1, dots, x_n]$ be a quadratic form. The equation $f(x_1, dots, x_n) = 0$ has a nontrivial solution in $QQ$ if and only if it has a nontrivial solution in $QQ_p$ for every $p <= infinity$.
]

= The $p$-adic metric

#definition(title: [Absolute value])[
  Let $F$ be a field. A map $|dot|: F -> RR_(>= 0)$ is an _absolute value_ if for all $x, y in F$:
  + $|x| = 0$ if and only if $x = 0$,
  + $|x y| = |x| |y|$,
  + $|x + y| <= |x| + |y|$.
  It is _non-archimedean_ if moreover $|x + y| <= max {|x|, |y|}$ for all $x, y in F$.
]

#remark[
  From $|1| = |1|^2$ and $|1| != 0$ we get $|1| = 1$, and from $|-1|^2 = |1|$ we get $|-1| = 1$. Hence an absolute value induces a metric $d(x, y) = |x - y|$ on $F$.
]

#definition(title: [Ultrametric space])[
  A metric space whose metric is induced by a non-archimedean absolute value is called _ultrametric_. Its metric satisfies $d(x, z) <= max {d(x, y), d(y, z)}$.
]

#definition(title: [$p$-adic valuation])[
  The _$p$-adic valuation_ is the function $v_p: QQ -> ZZ union {infinity}$ defined as follows. For $0 != x in ZZ$, $v_p (x)$ is the unique non-negative integer with $x = p^(v_p (x)) x'$ and $p divides.not x'$. For $x in QQ without ZZ$, write $x = a slash b$ with $a, b in ZZ$, $b != 0$, and put $v_p (x) = v_p (a) - v_p (b)$. Finally $v_p (0) = infinity$.
]

#proposition[
  The valuation $v_p$ is well defined, and for all $x, y in QQ$:
  + $v_p (x y) = v_p (x) + v_p (y)$,
  + $v_p (x + y) >= min {v_p (x), v_p (y)}$.
] <prop-vp>

#proof[
  On nonzero integers, $v_p (a b) = v_p (a) + v_p (b)$ by unique factorization. If $a slash b = a' slash b'$, then $a b' = a' b$, so $v_p (a) + v_p (b') = v_p (a') + v_p (b)$, and the definition does not depend on the representation. Property 1 follows from the integer case. For 2 we may assume $x, y != 0$; write $x = p^v a slash b$ and $y = p^w c slash d$ with $p divides.not a b c d$ and $v <= w$. Then $x + y = p^v (a d + p^(w - v) c b) slash (b d)$, and $p divides.not b d$, so $v_p (x + y) >= v$.
]

#definition(title: [$p$-adic absolute value])[
  The _$p$-adic absolute value_ $|dot|_p: QQ -> RR_(>= 0)$ is $|x|_p = p^(-v_p (x))$ for $x != 0$ and $|0|_p = 0$.
]

#theorem[
  $|dot|_p$ is a non-archimedean absolute value on $QQ$.
] <thm-abs-p>

#proof[
  $|x|_p = 0$ only for $x = 0$. By @prop-vp, $|x y|_p = p^(-v_p (x) - v_p (y)) = |x|_p |y|_p$ and $|x + y|_p <= p^(-min {v_p (x), v_p (y)}) = max {|x|_p, |y|_p}$, which also implies the triangle inequality.
]

// [p3]
#remark[
  $lim_(n -> infinity) p^n = 0$ in the $p$-adic metric. Indeed, let $epsilon > 0$ and choose $N in NN$ with $1 slash N < epsilon$. Since $p^N > N$, we have $1 slash p^N < epsilon$, so for $n >= N$, $|p^n|_p = 1 slash p^n < epsilon$.
]

#definition(title: [Equivalent absolute values])[
  Two absolute values on a field are _equivalent_ if they induce the same topology. The _trivial_ absolute value is $|x| = 1$ for $x != 0$, $|0| = 0$. The _standard_ absolute value on $QQ$ is denoted $|dot|_infinity$.
]

#theorem(title: [Ostrowski])[
  Every nontrivial absolute value on $QQ$ is equivalent to $|dot|_infinity$ or to $|dot|_p$ for some prime $p$.
]

#proof[
  Let $|dot|$ be a nontrivial absolute value on $QQ$. It suffices to find $c > 0$ with $|x| = |x|_infinity^c$ for all $x$, or $|x| = |x|_p^c$ for all $x$: then the open balls of $|dot|$ of radius $r$ are the balls of the other absolute value of radius $r^(1 slash c)$, so the topologies agree. Since $|-1| = 1$ and $|dot|$ is multiplicative, it suffices to determine $|n|$ for $n in NN$. For $n in NN$ the triangle inequality gives $|n| <= n$.

  *Case 1: $|n| <= 1$ for every $n in NN$.* If $|n| = 1$ for all $n in NN$, then $|dot|$ is trivial by multiplicativity. So some $n in NN$ has $|n| < 1$; let $n_0$ be the least one. Then $n_0 > 1$, and $n_0$ is a prime $p$: if $n_0 = a b$ with $1 < a, b < n_0$, then $|a| = |b| = 1$ and $|n_0| = 1$. Suppose a prime $q != p$ also has $|q| < 1$. Choose $M in NN$ with $|p|^M < 1 slash 2$ and $|q|^M < 1 slash 2$. Since $(p^M, q^M) = 1$, there are $u, w in ZZ$ with $u p^M + w q^M = 1$, and then $1 = |1| <= |u| |p|^M + |w| |q|^M < 1 slash 2 + 1 slash 2 = 1$, because $|u|, |w| <= 1$. This is a contradiction, so $|q| = 1$ for every prime $q != p$. Put $c = -log |p| slash log p > 0$, so $|p| = p^(-c)$. For $n = p^v n'$ with $p divides.not n'$ we get $|n| = p^(-c v) = |n|_p^c$.

  *Case 2: $|n_1| > 1$ for some $n_1 in NN$.* We first show that for all integers $m, n > 1$,
  $ |m| <= max {1, |n|}^(log m slash log n). $
  Let $k in NN$ and write $m^k = sum_(i = 0)^s d_i n^i$ in base $n$, with $0 <= d_i < n$ and $s <= k log m slash log n$. Then $|d_i| <= d_i < n$, and
  $ |m|^k <= sum_(i = 0)^s |d_i| |n|^i <= (s + 1) n max {1, |n|}^s <= (1 + k (log m) / (log n)) n max {1, |n|}^(k log m slash log n). $
  Taking $k$-th roots and letting $k -> infinity$ gives the inequality. Applying it with $m = n_1$ shows $1 < |n_1| <= max {1, |n|}^(log n_1 slash log n)$, so $|n| > 1$ for every $n > 1$. Hence $|m|^(1 slash log m) <= |n|^(1 slash log n)$ for all $m, n > 1$, and by symmetry equality holds. So $|n|^(1 slash log n) = e^c$ for a constant $c$, with $c > 0$ since $|n| > 1$. Then $|n| = n^c = |n|_infinity^c$ for $n > 1$, and also for $n = 1$.
]

#remark(title: [Recall])[
  A _completion_ of a metric space $X$ is a complete metric space $hat(X)$ together with an isometric embedding $X -> hat(X)$ whose image is dense. A completion exists and is unique up to an isometry that is the identity on $X$.
]

#theorem(title: [Construction of $QQ_p$ and $ZZ_p$])[
  For $0 != x in QQ_p$ let $v(x)$ be the least index of a nonzero digit of $x$, and put $|x|_p = p^(-v(x))$, $|0|_p = 0$. Then:
  + $|dot|_p$ is a non-archimedean absolute value on $QQ_p$ that extends the $p$-adic absolute value of $QQ$;
  + $ZZ_p = {x in QQ_p : |x|_p <= 1}$;
  + $QQ$ is dense in $QQ_p$;
  + $QQ_p$ is complete.
  Hence $QQ_p$ is the completion of $QQ$ with respect to $|dot|_p$. The field $QQ$ itself is not complete under the $p$-adic metric.
] <thm-completion>

#proof[
  We use one fact throughout: for $alpha, beta in ZZ_p$ and $k in NN$, $|alpha - beta|_p <= p^(-k)$ holds if and only if $alpha_k = beta_k$. Indeed, $(alpha - beta)_k equiv alpha_k - beta_k pmod(p^k)$ and $0 <= alpha_k, beta_k < p^k$, and $|alpha - beta|_p <= p^(-k)$ means that the first $k$ digits of $alpha - beta$ vanish.

  1) In the notation of @prop-qp-field, $x = p^v u$ with $u$ a unit gives $v(x) = v$. For $x = p^v u$ and $y = p^w u'$, $x y = p^(v + w) u u'$ with $u u'$ a unit, so $|x y|_p = |x|_p |y|_p$. For the ultrametric inequality, write $x = p^(-N) alpha$ and $y = p^(-N) beta$ with $alpha, beta in ZZ_p$. If the first $k$ digits of $alpha$ and $beta$ vanish, then $(alpha + beta)_k equiv alpha_k + beta_k = 0$, so those of $alpha + beta$ vanish; hence $v(x + y) >= min {v(x), v(y)}$. For rational $x = p^v a slash b$ with $p divides.not a b$, the element $a slash b in ZZ_p$ has first digit $a b^(-1) equiv.not 0 pmod(p)$, so it is a unit and $v(x) = v = v_p (x)$.

  2) $x in ZZ_p$ if and only if $x$ has no nonzero digit of negative index, that is, $v(x) >= 0$.

  3) Let $x = sum_(k >= -N) a_k p^k$ and let $s_n = sum_(k = -N)^(n - 1) a_k p^k in QQ$. The first nonzero digit of $x - s_n$ has index at least $n$, so $|x - s_n|_p <= p^(-n) -> 0$.

  4) Let $(x_n)$ be a Cauchy sequence in $QQ_p$. It is bounded, so there is $N$ with $|x_n|_p <= p^N$ for all $n$; then $y_n = p^N x_n in ZZ_p$ by 2), and $(y_n)$ is Cauchy. Choose $n_1 < n_2 < dots.c$ with $|y_n - y_m|_p <= p^(-k)$ for $n, m >= n_k$. By the fact above, $(y_n)_k = (y_(n_k))_k =: z_k$ for $n >= n_k$. Then $z_(k + 1) = (y_(n_(k + 1)))_(k + 1) equiv (y_(n_(k + 1)))_k = z_k pmod(p^k)$, so by @rem-truncations there is $eta in ZZ_p$ with $eta_k = z_k$. For $n >= n_k$ we get $(y_n)_k = eta_k$, that is, $|y_n - eta|_p <= p^(-k)$. So $y_n -> eta$ and $x_n -> p^(-N) eta$.

  By 1), 3) and 4), $QQ_p$ with $|dot|_p$ is a completion of $QQ$. Finally, $QQ$ is not complete: for $p = 7$, the truncations of the element $alpha$ with $alpha^2 = 2$ constructed in the example on $x^2 - 2$ form a Cauchy sequence in $QQ$ by 3). Its limit in $QQ_7$ is $alpha$, which is not rational, since $2$ is not the square of a rational number.
]
