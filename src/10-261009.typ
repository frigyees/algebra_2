#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 10-261009 · fundamental theorem part II, worked exercises on fields
// Scans are tablet screenshots; p5 repeats the top of exercise 8 from p4.
// HEADINGS section 19 coined
// DROPPED
//   [p1] "(From 3. session)"; [p5] exam-date note
// CORRECTIONS
//   [p2] ex. 1(2): N(c alpha) = c N(alpha) -> c^m N(alpha) (final answer changed)
//   [p2] ex. 3: f in L[x] -> f irreducible (false otherwise: (x - 1)^2)
//   [p3] ex. 5, F_3 case: a(b + d) = 0 -> a(d - b) = 0; results unchanged
//   [p4] ex. 6: "purely ired" -> purely inseparable
//   [p4] ex. 7: false for x + 1 -> degree >= 2
//   [p4] ex. 8: x^(p^n) -> x^(q^n); step 2 congruence test -> gcd test (f = x(x^2+x+1)(x^3+x+1) over F_2 passes the congruence test but is reducible; final answer changed)
//   [p5] ex. 9: "Q(4th root 2)|Q(sqrt 2) is not normal" -> Q(4th root 2)|Q
//   [p5] ex. 10: epsilon^2 cbrt 2 -> epsilon^2 cbrt 3
// ADDITIONS (A filled in)
//   [p1] A: (2) F-monomorphisms K -> Omega are restrictions of elements of G; (3) well-definedness, kernel via part I, surjectivity; (4) H = Gal(E|K)
//   [p2] A: ex. 1-2 setting and Frobenius additivity; ex. 3 transitivity of algebraicity, common splitting field
//   [p3] A: ex. 5: no roots via x^4 in {0, 1}; degree-2 reduction; irreducibility of the two factors
//   [p4] A: ex. 6: induction with deg g = 0 case, remark m_alpha linear over finite F; ex. 8: both inclusions, root field, correctness proof of the algorithm
//   [p5] A: ex. 9: irreducibility of x^4 - 2, degrees via the tower law; ex. 10: irreducibility of x^3 - 3

// [p1]
#theorem(title: [Fundamental theorem of Galois theory, part II])[
  Let $E | F$ be a finite Galois extension with $G = Gal(E | F)$, let $H <= G$, and let $K = cal(F)(H)$ be the intermediate field fixed by $H$. Then:
  + $E | K$ is a Galois extension.
  + $K | F$ is normal if and only if $H$ is a normal subgroup of $G$.
  + If $H$ is normal in $G$, then $Gal(K | F) tilde.equiv G slash H = Gal(E | F) slash Gal(E | K)$.
  + $[K : F] = |G : H|$, whether or not $K | F$ is normal.
] <thm-fundamental-2>

#proof[
  1) $E | K$ is normal by @cor-normal-top and separable by @thm-sep-tower.

  2) Let $Omega$ be an algebraic closure of $E$. We first show that the $F$-monomorphisms $K -> Omega$ are exactly the restrictions $sigma|_K$ with $sigma in G$. Each $sigma|_K$ is one. Conversely, let $tau: K -> Omega$ be an $F$-monomorphism. By @lem-extend, applied to $E | K$, $tau$ extends to an $F$-monomorphism $tau': E -> Omega$. Since $E | F$ is normal, $tau'(E) = E$ by @prop-normal-crit, so $tau' in G$ and $tau = tau'|_K$.

  By @prop-normal-crit applied to $K | F$, it follows that $K | F$ is normal if and only if $sigma(K) = K$ for every $sigma in G$. Since $K = cal(F)(H)$ and $sigma(cal(F)(H)) = cal(F)(sigma H sigma^(-1))$ by @thm-fundamental-1 2), this holds if and only if $cal(F)(sigma H sigma^(-1)) = cal(F)(H)$ for every $sigma in G$. As $cal(F)$ is injective by @thm-fundamental-1 1), this is equivalent to $sigma H sigma^(-1) = H$ for every $sigma in G$, that is, to $H$ being normal in $G$.

  3) Let $H$ be normal in $G$. By 2), $sigma(K) = K$ for every $sigma in G$, so $sigma|_K in Gal(K | F)$, and
  $ G -> Gal(K | F), quad sigma mapsto sigma|_K, $
  is a group homomorphism. Its kernel is ${sigma in G : sigma|_K = "id"} = Gal(E | K) = cal(G)(cal(F)(H)) = H$, by @thm-fundamental-1 1). It is surjective: every $rho in Gal(K | F)$, composed with the inclusion $K -> Omega$, is an $F$-monomorphism $K -> Omega$, hence the restriction of some $sigma in G$ by the first paragraph of 2). By the first isomorphism theorem, $G slash H tilde.equiv Gal(K | F)$.

  4) By @thm-fundamental-1 1), $H = Gal(E | K)$. Since $E | F$ and $E | K$ are Galois, @prop-gal-order gives $|G| = [E : F]$ and $|H| = [E : K]$. By the tower law $[E : F] = [E : K] [K : F]$, so $|G| = |H| [K : F]$, and by Lagrange's theorem $|G : H| = |G| slash |H| = [K : F]$.
]

= Worked exercises on fields

Throughout the first two exercises, $q$ is a prime power, $m in NN$, $L = FF_(q^m)$ and $K = FF_q$; we write $nrm = nrm_(L | K)$ and $tr = tr_(L | K)$. By @thm-finite-field, $c^q = c$ for every $c in K$.

#example[
  Show that for $alpha, beta in L$ and $a, c in K$:
  + $nrm(alpha beta) = nrm(alpha) nrm(beta)$;
  + $nrm(c alpha) = c^m nrm(alpha)$;
  + $nrm(a) = a^m$.
]

#solution[
  1) Rearranging the factors,
  $ nrm(alpha) nrm(beta) = alpha alpha^q dots.c alpha^(q^(m - 1)) dot beta beta^q dots.c beta^(q^(m - 1)) = (alpha beta)(alpha beta)^q dots.c (alpha beta)^(q^(m - 1)) = nrm(alpha beta). $
  // [p2]
  2) Since $c^(q^i) = c$ for every $i$,
  $ nrm(c alpha) = c alpha dot (c alpha)^q dots.c (c alpha)^(q^(m - 1)) = (c c^q dots.c c^(q^(m - 1)))(alpha alpha^q dots.c alpha^(q^(m - 1))) = c^m nrm(alpha). $

  3) $nrm(a) = a a^q dots.c a^(q^(m - 1)) = a^m$, since $a^(q^i) = a$.
]

#example[
  Show that for $alpha, beta in L$ and $a, c in K$:
  + $tr(alpha + beta) = tr(alpha) + tr(beta)$;
  + $tr(c alpha) = c tr(alpha)$;
  + $tr(a) = m a$.
]

#solution[
  1) $alpha mapsto alpha^(q^i)$ is a ring homomorphism (@thm-frob-aut), so
  $ tr(alpha + beta) = (alpha + beta) + (alpha + beta)^q + dots.c + (alpha + beta)^(q^(m - 1)) \
    = alpha + beta + alpha^q + beta^q + dots.c + alpha^(q^(m - 1)) + beta^(q^(m - 1)) = tr(alpha) + tr(beta). $
  2) Using $c^(q^i) = c$,
  $ tr(c alpha) = c alpha + (c alpha)^q + dots.c + (c alpha)^(q^(m - 1)) = c alpha + c alpha^q + dots.c + c alpha^(q^(m - 1)) = c tr(alpha). $
  3) $tr(a) = a + a^q + dots.c + a^(q^(m - 1)) = m a$, since $a^(q^i) = a$.
]

#definition(title: [Perfect field])[
  A field $F$ is _perfect_ if every irreducible polynomial in $F[x]$ is separable.
]

By @lem-sep-deriv and @thm-finite-sep, fields of characteristic $0$ and finite fields are perfect.

#example[
  Show that an algebraic extension of a perfect field is perfect.
]

#solution[
  Let $K$ be perfect and $L | K$ algebraic. Let $f in L[x]$ be irreducible; we show that $f$ is separable. Let $E$ be a splitting field of $f$ over $L$ and $alpha_1 in E$ a root of $f$. Since $f$ is irreducible, it is a scalar multiple of $m_(alpha_1, L)$.

  The element $alpha_1$ is algebraic over $K$. Indeed, the coefficients of $f$ are algebraic over $K$, so they generate a finite extension $K'$ of $K$ (tower law). As $alpha_1$ is algebraic over $K'$, $[K'(alpha_1) : K]$ is finite, and $alpha_1$ is algebraic over $K$.

  Let $g = m_(alpha_1, K)$. Then $g in K[x] subset.eq L[x]$ and $g(alpha_1) = 0$, so $f divides g$ in $L[x]$. Since $K$ is perfect, $g$ is separable: in a splitting field $E'$ of $g$ over $E$, $g = (x - alpha_1) dots.c (x - alpha_r)$ with pairwise distinct $alpha_i$. As $f divides g$, $f$ splits in $E'[x]$ into pairwise distinct linear factors. Hence $f$ is separable, and $L$ is perfect.
]

#example[
  Let $p$ be a prime and $a in FF_p$. Show that $f(x) = x^p - x + a$ is separable over $FF_p$.
]

#solution[
  // [p3]
  $f'(x) = p x^(p - 1) - 1 = -1$ in $FF_p [x]$. Hence $gcd(f, f') = 1$, and $f$ is separable by @prop-sep-gcd.
]

#example[
  Is $x^4 - 7$ irreducible over $FF_5$? Determine the irreducible factors of $x^4 + 1$ over $FF_3$.
]

#solution[
  Over $FF_5$, $x^4 - 7 = x^4 - 2$. By @thm-finite-field, $x^4 in {0, 1}$ for $x in FF_5$, so $x^4 - 2$ has no root and no linear factor. If it were reducible, it would therefore be a product of two monic quadratics:
  $ x^4 - 2 = (x^2 + a x + b)(x^2 + c x + d) = x^4 + (a + c) x^3 + (b + d + a c) x^2 + (a d + b c) x + b d. $
  Comparing coefficients, $a + c = 0$, $b + d + a c = 0$, $a d + b c = 0$, $b d = -2$. So $c = -a$, $b + d = a^2$, $a (d - b) = 0$ and $b d = -2$.
  - If $a = 0$, then $b + d = 0$ and $-b^2 = -2$, so $b^2 = 2$. But $ls(2, 5) = -1$, since $5 equiv -3 pmod(8)$.
  - If $a != 0$, then $b = d$ and $b^2 = -2$. But $ls(-2, 5) = ls(-1, 5) ls(2, 5) = 1 dot (-1) = -1$.
  So $x^4 - 7$ is irreducible over $FF_5$.

  Over $FF_3$, $x^4 + 1 in {1, 2}$ for every $x in FF_3$, again since $x^4 in {0, 1}$, so there is no linear factor. With the same ansatz, $c = -a$, $b + d = a^2$, $a (d - b) = 0$ and $b d = 1$. In $FF_3$ the units $plus.minus 1$ are their own inverses, so $b d = 1$ forces $b = d = 1$ or $b = d = -1$.
  - If $b = d = 1$, then $a^2 = 2$, which has no solution in $FF_3$.
  - If $b = d = -1$, then $a^2 = -2 = 1$, so $a = 1$, $c = -1$ is a solution.
  Hence
  $ x^4 + 1 = (x^2 + x - 1)(x^2 - x - 1) quad "in" FF_3 [x], $
  which can be checked directly: the product is $(x^2 - 1)^2 - x^2 = x^4 - 3 x^2 + 1 = x^4 + 1$. Both factors are irreducible, since neither has a root in $FF_3$: $x^2 + x - 1$ takes the values $-1, 1, 2$ and $x^2 - x - 1$ the values $-1, -1, 1$ at $x = 0, 1, 2$.
]

// [p4]
#definition(title: [Purely inseparable polynomial])[
  Let $F$ be a field with algebraic closure $overline(F)$. A nonconstant $f in F[x]$ is _purely inseparable_ if it has exactly one root in $overline(F)$.
]

#example[
  Let $F$ be a finite field and $f in F[x]$ purely inseparable, with root $alpha in overline(F)$. Prove that $f = c dot m_(alpha, F)^k$ for some $k in NN$ and $c in F^times$.
]

#solution[
  We proceed by induction on $n = deg f >= 1$. Since $m_(alpha, F)$ divides $f$ in $F[x]$, write $f = m_(alpha, F) g$ with $g in F[x]$ and $deg g < n$. If $deg g = 0$, then $g = c in F^times$ and $f = c dot m_(alpha, F)$. Otherwise $g$ has a root in $overline(F)$, and every root of $g$ is a root of $f$, so $g$ is purely inseparable with the root $alpha$. By the induction hypothesis $g = a_0 dot m_(alpha, F)^(k_0)$ with $k_0 in NN$ and $a_0 in F^times$, hence
  $ f = m_(alpha, F) dot g = a_0 dot m_(alpha, F)^(k_0 + 1). $
  The case $n = 1$ is the case $deg g = 0$. The argument uses only that $F$ is a field. For finite $F$ more is true: $m_(alpha, F)$ is separable by @thm-finite-sep, and its only root is $alpha$, so $m_(alpha, F) = x - alpha$ and $alpha in F$.
]

#example[
  Show that no irreducible polynomial of degree at least $2$ over $FF_2$ has an even number of nonzero terms.
]

#solution[
  Let $f = x^k + epsilon_(k - 1) x^(k - 1) + dots.c + epsilon_1 x + epsilon_0$ with $k >= 2$ and $epsilon_i in {0, 1}$. Then $f(1)$ is the number of nonzero terms modulo $2$. If this number is even, then $f(1) = 0$, so $x - 1$ divides $f$, and since $deg f >= 2$, $f$ is reducible. The degree condition is needed: $x + 1$ is irreducible with two nonzero terms.
]

#example[
  Let $q$ be a prime power and $d in NN$. Prove that $x^(q^d) - x$ is the product of all monic irreducible $f in FF_q [x]$ with $deg f divides d$, each with multiplicity $1$. Design an algorithm that tests whether a polynomial over $FF_q$ is irreducible.
]

#solution[
  Let $P = x^(q^d) - x$. Since $P' = q^d x^(q^d - 1) - 1 = -1$, $gcd(P, P') = 1$, so by @prop-sep-gcd $P$ has no multiple roots and no irreducible factor of multiplicity greater than $1$. As $P$ is monic, it is the product of its distinct monic irreducible factors. It remains to show that a monic irreducible $f in FF_q [x]$ divides $P$ if and only if $deg f divides d$. Let $r = deg f$.

  Suppose $r divides d$. In the field $FF_q [x] slash (f)$, which has $q^r$ elements (@rem-recall-ext), the class $alpha$ of $x$ is a root of $f$ and satisfies $alpha^(q^r) = alpha$ by @thm-finite-field. Iterating $d slash r$ times gives $alpha^(q^d) = alpha$, so $P(alpha) = 0$, and $f = m_(alpha, FF_q)$ divides $P$.

  Conversely, suppose $f divides P$. Let $E$ be a splitting field of $P$ over $FF_q$ and $R subset.eq E$ the set of roots of $P$; it has exactly $q^d$ elements, since the roots are simple. $R$ is a subfield, as in the proof of @lem-roots-irred, and it contains $FF_q$. A root $alpha in E$ of $f$ lies in $R$, so $FF_q (alpha) subset.eq R$. Then $R$ is a vector space over $FF_q (alpha)$, which has $q^r$ elements, so $q^d = (q^r)^s$ for some $s in NN$, and $r divides d$.

  *Algorithm.* Let $f in FF_q [x]$ be monic of degree $n >= 1$.
  + If $x^(q^n) equiv.not x pmod(f)$, answer NO.
  + If $gcd(f, x^(q^(n slash r)) - x) != 1$ for some prime $r divides n$, answer NO.
  + Otherwise answer YES.
  The powers $x^(q^k) mod f$ are computed by repeated $q$-th powering modulo $f$.

  _Correctness._ Let $f$ be irreducible. By the first part $f divides x^(q^n) - x$, so step 1 passes. For a prime $r divides n$, $gcd(f, x^(q^(n slash r)) - x)$ is $1$ or $f$, and it is not $f$, since $n divides.not n slash r$. So the answer is YES. Conversely, suppose the answer is YES. By step 1, $f divides x^(q^n) - x$, so by the first part $f$ is a product of distinct monic irreducible factors whose degrees divide $n$. If $f$ were reducible, it would have a factor $g$ of degree $e < n$ with $e divides n$. Choose a prime $r$ dividing $n slash e$; then $e divides n slash r$, so $g divides x^(q^(n slash r)) - x$ and step 2 answers NO. Hence $f$ is irreducible.

  Step 2 cannot be replaced by the congruence test $x^(q^(n slash r)) equiv x pmod(f)$. Over $FF_2$, $f = x (x^2 + x + 1)(x^3 + x + 1)$ has degree $6$ and passes step 1, since all factor degrees divide $6$. Neither $x^(2^3) equiv x$ nor $x^(2^2) equiv x pmod(f)$ holds, because $2 divides.not 3$ and $3 divides.not 2$; yet $f$ is reducible.
]

// [p5]
#example[
  Give fields $F subset.eq K subset.eq L$ such that $L | K$ and $K | F$ are normal, but $L | F$ is not normal.
]

#solution[
  Take $QQ subset.eq QQ(sqrt(2)) subset.eq QQ(root(4, 2))$, where $root(4, 2)$ is the positive real fourth root of $2$ and $sqrt(2) = root(4, 2)^2$.

  First, $x^4 - 2$ is irreducible over $QQ$. Its complex roots are $plus.minus a$ and $plus.minus i a$ with $a = root(4, 2)$, and none is rational, since $v_2 (z^4) = 4 v_2 (z) != 1$. A monic quadratic factor over $QQ$ would be $(x - r)(x - r')$ for two of these roots, with constant term $r r' in {-sqrt(2), sqrt(2), plus.minus i sqrt(2)}$, none of which is rational. Hence $[QQ(root(4, 2)) : QQ] = 4$, and by the tower law $[QQ(root(4, 2)) : QQ(sqrt(2))] = 2$.

  $QQ(sqrt(2)) | QQ$ and $QQ(root(4, 2)) | QQ(sqrt(2))$ have degree $2$, so both are normal (@ex-normal); the relevant polynomials are $x^2 - 2$ and $x^2 - sqrt(2)$. But $QQ(root(4, 2)) | QQ$ is not normal: the irreducible $x^4 - 2$ has the root $root(4, 2) in QQ(root(4, 2))$, while its roots $plus.minus i root(4, 2)$ are not real and so do not lie in $QQ(root(4, 2)) subset.eq RR$.
]

#example[
  Prove that $QQ(root(3, 3)) | QQ$ is not normal.
]

#solution[
  $x^3 - 3$ is irreducible over $QQ$, since it has degree $3$ and no rational root ($z^3 = 3$ would give $3 v_3 (z) = 1$). Its roots are $root(3, 3)$, $epsilon root(3, 3)$, $epsilon^2 root(3, 3)$, where $epsilon$ is a primitive third root of unity. The root $epsilon root(3, 3)$ is not real, so $epsilon root(3, 3) in.not QQ(root(3, 3)) subset.eq RR$.
]
