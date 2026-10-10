#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 05-260921 · worked exercises, geometry of Q_p
// HEADINGS section 10 coined; section 11 from source, placed before the lemma that precedes it in the source
// DROPPED
//   [p2] (31/95): repeats 02-260911 p4; doodles on p2
// CORRECTIONS
//   [p1] ex. 2: congruence "90c = -119 = -8 (27)" -> 18c + 18 = 0 (27); result unchanged
//   [p1] ex. 5: (101/11) = (4/11) -> (2/11); the 7! chain after (5/83)(7/83) rewritten; results unchanged
//   [p2] ex. 8: "log d * 1{n = 1}" -> log n * 1{n = 1}
//   [p2] lemma: "ultrametric space K" -> field with a non-archimedean absolute value; unjustified |x + y| > |y| removed
// READINGS
//   [p2] ex. 6 denominator read as 1999 (1999 = 3 * 589 + 232 matches the next step; 1899 does not)
//   [p2] ex. 8 function read as Lambda
// ADDITIONS (A filled in)
//   [p1] A: statements of the exercises; roots mod 3 in ex. 2; uniqueness via Hensel
//   [p1] A: g^((p-1)/2) = -1 in ex. 3; p > 2 in ex. 4; conclusion for x^2 = 30 (77)
//   [p2] A: gcd check in ex. 6; definitions of Lambda, lambda, totally multiplicative, indicator
//   [p2] A: definitions of triangle, collinear, right triangle; "two longest sides are equal" in the isosceles theorem

// [p1]
= Worked exercises

#example[
  Show that $2$ is a primitive root modulo $11$ and solve $7 x^8 equiv 5 pmod(11)$.
]

#solution[
  $ord(11, 2) divides phi(11) = 10$, so $ord(11, 2) in {1, 2, 5, 10}$. Since $2^1 = 2$, $2^2 = 4$ and $2^5 = 32 equiv -1 pmod(11)$, $ord(11, 2) = 10$, and $2$ is a primitive root modulo $11$. Taking indices, @thm-ind gives $ind_2 (7 x^8) equiv ind_2 5 pmod(10)$, that is, $ind_2 7 + 8 ind_2 x equiv ind_2 5 pmod(10)$. The tables of powers and indices are:
  #align(center, table(
    columns: 11,
    $a$, ..range(1, 11).map(n => [#n]),
    $2^a$, ..(2, 4, 8, 5, 10, 9, 7, 3, 6, 1).map(v => [#v]),
    $ind_2 a$, ..(10, 1, 8, 2, 4, 9, 7, 3, 6, 5).map(v => [#v]),
  ))
  So $7 + 8 ind_2 x equiv 4 pmod(10)$, that is, $8 ind_2 x equiv 7 pmod(10)$. Since $(8, 10) = 2 divides.not 7$, there is no solution (@rem-linear).
]

#example[
  Solve $x^3 - x^2 - 1 equiv 0 pmod(27)$.
]

#solution[
  Here $27 = 3^3$. Let $f(x) = x^3 - x^2 - 1$. Modulo $3$, $f(0) equiv f(1) equiv -1$ and $f(2) = 3 equiv 0$, so $x equiv -1 pmod(3)$ is the only solution. Since $f'(-1) = 5 equiv.not 0 pmod(3)$, @thm-hensel gives exactly one solution modulo $27$.

  Write $x = 3 b - 1$. Modulo $9$,
  $ (3 b)^3 - 3 (3 b)^2 + 3 (3 b) - 1 - (3 b)^2 + 2 dot 3 b - 1 - 1 equiv 6 b - 3 pmod(9), $
  and $6 b - 3 equiv 0 pmod(9)$ if and only if $2 b - 1 equiv 0 pmod(3)$, that is, $b equiv 2 pmod(3)$. So $b = 3 c + 2$ and $x = 3(3 c + 2) - 1 = 9 c + 5$. Modulo $27$,
  $ (9 c)^3 + 3 dot 5 (9 c)^2 + 3 dot 5^2 (9 c) + 5^3 - (9 c)^2 - 2 dot 5 (9 c) - 5^2 - 1 equiv 585 c + 99 equiv 18 c + 18 pmod(27), $
  and $18 c + 18 equiv 0 pmod(27)$ if and only if $c equiv -1 pmod(3)$. Hence $x equiv 9 dot (-1) + 5 = -4 pmod(27)$. Equivalently, the solution is found digit by digit in the form $x = a + 3 b + 3^2 c$.
]

#example[
  Let $p > 2$ be a prime. Show that $(p - 1)! equiv -1 pmod(p)$.
]

#solution[
  Let $g$ be a primitive root modulo $p$. Both $1, 2, dots, p - 1$ and, by @thm-rrs, $1, g, g^2, dots, g^(p - 2)$ form reduced residue systems modulo $p$, so
  $ (p - 1)! equiv g^(1 + 2 + dots.c + (p - 2)) = g^((p - 2)(p - 1) slash 2) = (g^((p - 1) slash 2))^(p - 2) equiv (-1)^(p - 2) = -1 pmod(p). $
  Here $g^((p - 1) slash 2) equiv -1$ by @prop-pm1, since $g^((p - 1) slash 2) equiv.not 1$ because $ord(p, g) = p - 1$; and $p - 2$ is odd.
]

#example[
  Let $p > 2$ be a prime and $g$ a primitive root modulo $p$. Show that $g$ is a quadratic non-residue modulo $p$.
]

#solution[
  If $g$ were a quadratic residue, then $g^((p - 1) slash 2) equiv 1 pmod(p)$ by @prop-pm1, contradicting $ord(p, g) = p - 1$.
]

#example[
  Decide whether $x^2 equiv 66 pmod(101)$, $x^2 equiv 7! pmod(83)$ and $x^2 equiv 30 pmod(77)$ are solvable.
]

#solution[
  Using $101 equiv 1 pmod(4)$, $101 equiv -3 pmod(8)$, $101 = 33 dot 3 + 2 = 9 dot 11 + 2$:
  $ ls(66, 101) = ls(2 dot 3 dot 11, 101) = ls(2, 101) ls(3, 101) ls(11, 101) \
    = -ls(101, 3) ls(101, 11) = -ls(2, 3) ls(2, 11) = -(-1)(-1) = -1, $
  so $x^2 equiv 66 pmod(101)$ has no solution.

  Next, $7! = 1 dot 2 dot dots.c dot 7$ and $ls(4, 83) = 1$, $ls(6, 83) = ls(2, 83) ls(3, 83)$, so
  $ ls(7!, 83) = ls(1, 83) ls(2, 83) dots.c ls(7, 83) = ls(5, 83) ls(7, 83) \
    = ls(83, 5) dot (-ls(83, 7)) = -ls(3, 5) ls(6, 7) = -ls(3, 5) ls(-1, 7) = -(-1)(-1) = -1, $
  using $5 equiv 1 pmod(4)$, $7 equiv 83 equiv -1 pmod(4)$, $83 = 16 dot 5 + 3 = 11 dot 7 + 6$, $ls(3, 5) = -1$ and $ls(-1, 7) = -1$. So $x^2 equiv 7! pmod(83)$ has no solution.

  Finally $77 = 7 dot 11$, and we check the two primes separately. Modulo $7$,
  $ ls(30, 7) = ls(2 dot 3 dot 5, 7) = ls(2, 7) ls(3, 7) ls(5, 7) \
    = 1 dot (-ls(7, 3)) ls(7, 5) = -ls(1, 3) ls(2, 5) = -1 dot (-1) = 1, $
  so $x^2 equiv 30 pmod(7)$ is solvable. Modulo $11$, $ls(30, 11) = ls(8, 11) = ls(2, 11)^3 = (-1)^3 = -1$, so $x^2 equiv 30 pmod(11)$ is not solvable. A solution modulo $77$ would be a solution modulo $11$, so $x^2 equiv 30 pmod(77)$ has no solution.
]

// [p2]
#example[
  Compute $ls(1234567, 225)$ and $ls(589, 1999)$.
]

#solution[
  Since $1234567$ has digit sum $28$ and last digit $7$, $(1234567, 15) = 1$. By @prop-jacobi 5),
  $ ls(1234567, 225) = ls(1234567, 15^2) = ls(1234567, 15)^2 = 1. $

  Using $589 equiv 1 pmod(4)$, $1999 = 3 dot 589 + 232$, $232 = 2^3 dot 29$, $589 equiv 5 pmod(8)$, $29 equiv 1 pmod(4)$ and $589 = 20 dot 29 + 9$,
  $ ls(589, 1999) = ls(1999, 589) = ls(232, 589) = ls(2^3 dot 29, 589) = ls(2, 589)^3 ls(29, 589) = (-1)^3 ls(29, 589) \
    = -ls(589, 29) = -ls(9, 29) = -ls(3, 29)^2 = -1. $
]

#definition[
  An arithmetic function $f$ is _totally multiplicative_ if $f(m n) = f(m) f(n)$ for all $m, n in NN$. The _von Mangoldt function_ is $Lambda(n) = log p$ if $n = p^k$ for a prime $p$ and $k in NN$, and $Lambda(n) = 0$ otherwise. The _Liouville function_ is $lambda(n) = (-1)^(Omega(n))$. For a statement $P$, $bb(1){P}$ is $1$ if $P$ holds and $0$ otherwise.
]

#example[
  Show that $sum_(d divides n) Lambda(d) = log n$ for $n in NN$.
]

#solution[
  Let $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$. Only the prime-power divisors $p_i^j$ with $1 <= j <= alpha_i$ contribute, so
  $ sum_(d divides n) Lambda(d) = sum_(p^alpha divides n) Lambda(p^alpha) = sum_(i = 1)^r sum_(j = 1)^(alpha_i) Lambda(p_i^j) = sum_(i = 1)^r sum_(j = 1)^(alpha_i) log p_i \
    = sum_(i = 1)^r alpha_i log p_i = sum_(i = 1)^r log (p_i^(alpha_i)) = log (p_1^(alpha_1) dots.c p_r^(alpha_r)) = log n. $
  For $n = 1$ both sides are $0$.
]

#example[
  Show that $Lambda(n) = -sum_(d divides n) mu(d) log d$.
]

#solution[
  By the previous example and @thm-mobius,
  $ Lambda(n) = sum_(d divides n) mu(d) log (n / d) = sum_(d divides n) mu(d) (log n - log d) \
    = log n sum_(d divides n) mu(d) - sum_(d divides n) mu(d) log d \
    = log n dot bb(1){n = 1} - sum_(d divides n) mu(d) log d = -sum_(d divides n) mu(d) log d, $
  using @prop-mu and $log 1 = 0$.
]

#example[
  Show that $sum_(d divides n) lambda(d) = bb(1){n "is a square"}$.
]

#solution[
  Since $Omega(m n) = Omega(m) + Omega(n)$ for all $m, n in NN$, $lambda(m n) = (-1)^(Omega(m) + Omega(n)) = lambda(m) lambda(n)$, so $lambda$ is totally multiplicative, in particular multiplicative. By @thm-summation-mult its summation function $F$ is multiplicative. For a prime power,
  $ F(p^alpha) = sum_(d divides p^alpha) lambda(d) = lambda(1) + lambda(p) + dots.c + lambda(p^alpha) = 1 - 1 + (-1)^2 + (-1)^3 + dots.c + (-1)^alpha = bb(1){2 divides alpha}. $
  Hence $F(n) = F(p_1^(alpha_1)) dots.c F(p_r^(alpha_r)) = bb(1){"every" alpha_i "is even"} = bb(1){n "is a square"}$.
]

= Geometry of $QQ_p$

#lemma[
  Let $F$ be a field with a non-archimedean absolute value $|dot|$, and let $x, y in F$ with $|x| != |y|$. Then $|x + y| = max {|x|, |y|}$.
] <lem-strict-ultra>

#proof[
  Assume $|x| > |y|$. Since $|dot|$ is non-archimedean, $|x + y| <= max {|x|, |y|} = |x|$. Also $x = (x + y) - y$, so $|x| <= max {|x + y|, |-y|} = max {|x + y|, |y|}$. Since $|x| > |y|$, the maximum is $|x + y|$, and $|x| <= |x + y|$. Hence $|x + y| = |x|$.
]

#definition[
  In a metric space $(X, d)$, a _triangle_ is a triple of distinct points $a, b, c$, with side lengths $d(a, b)$, $d(a, c)$, $d(b, c)$. It is _isosceles_ if two of its side lengths are equal. Three distinct points are _collinear_ if, after relabelling, $d(a, c) = d(a, b) + d(b, c)$, and they form a _right triangle_ if, after relabelling, $d(a, c)^2 = d(a, b)^2 + d(b, c)^2$. We write $d_p (x, y) = |x - y|_p$ on $QQ_p$.
]

#theorem[
  Every triangle in $QQ_p$ is isosceles. More precisely, its two longest sides have equal length.
] <thm-isosceles>

#proof[
  Let $a, b, c in QQ_p$ be distinct. If $d_p (a, b) = d_p (b, c)$, the triangle is isosceles. Otherwise $|a - b|_p != |b - c|_p$, and since $(a - b) + (b - c) = a - c$, @lem-strict-ultra gives $|a - c|_p = max {|a - b|_p, |b - c|_p}$. So $|a - c|_p$ equals $|a - b|_p$ or $|b - c|_p$, namely the larger of the two. In both cases the two longest sides are equal.
]

#theorem[
  No three distinct points of $QQ_p$ are collinear.
]

#proof[
  Suppose $a, b, c in QQ_p$ are distinct and $d_p (a, c) = d_p (a, b) + d_p (b, c)$. Since $d_p (a, b), d_p (b, c) > 0$, we get $d_p (a, c) > d_p (a, b), d_p (b, c)$. So the side $a c$ is strictly the longest, which contradicts @thm-isosceles.
]

#theorem[
  There are no right triangles in $QQ_p$.
]

#proof[
  Suppose $a, b, c in QQ_p$ form a right triangle with $d_p (a, c)^2 = d_p (a, b)^2 + d_p (b, c)^2$. Again $d_p (a, c) > d_p (a, b), d_p (b, c)$. Since the triangle is isosceles, $d_p (a, b) = d_p (b, c)$, so $a c$ is the base, it is the longest side, and $d_p (a, c) = sqrt(2) d_p (a, b)$. By @thm-isosceles, however, the base of a triangle in $QQ_p$ that is not equilateral is its shortest side, a contradiction.
]
