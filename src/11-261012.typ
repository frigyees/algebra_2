#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 11-261012 · cyclotomic fields, ruler and compass constructions
// HEADINGS section 20 from source; section 21 from source ("Solvability by ruler and compass" -> "Ruler and compass constructions")
// DROPPED
//   [p1] [p2] crossed-out marginal drawings
// CORRECTIONS
//   [p1] "the n-th roots of unity form a multiplicative group E*" -> a cyclic subgroup of order n of E^x
//   [p1] Gal(E|F) = U_n and [E:F] = phi(n) for every F -> Gal(E|F) embeds in U_n; equality over Q (false e.g. for F = Q(i), n = 4)
//   [p2] K_n = R -> K_n subset R
//   [p2] trisection: "irreducible because f(x+1) = 8x^3 + 24x^2 + 18x + 1" does not prove irreducibility -> rational root test on y^3 - 3y - 1, y = 2x
// SCOPE
//   [p1] Galois property of F(zeta_n)|F stated for char F = 0 or F finite; the general case needs a result the notes do not contain
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: char F does not divide n; cyclicity of mu_n; E = F(zeta_n); sigma(zeta) = zeta^r with gcd(r, n) = 1; injectivity of Gal -> U_n
//   [p1] A: x^n - 1 = prod Phi_d: partition of mu_n by order; Gauss's lemma recalled for f, g in Z[x]
//   [p1] A: irreducibility proof: arbitrary root theta in place of zeta_n, x^n - 1 separable mod p, successive prime powers made explicit
//   [p2] A: definition of constructible point made precise; constructible real number; lines and circles over K_(i-1)
//   [p2] A: lemma cases line-line, line-circle, circle-circle; degree count via K_(i-1)(x_i) in the theorem
//   [p2] A: segment of length alpha gives (alpha, 0); 60 degree angle constructible from P_0; irreducibility of x^3 - 2
//   [p2] C: Lindemann (pi transcendental)

// [p1]
= Cyclotomic fields

#definition(title: [Cyclotomic extension])[
  Let $F$ be a field and $n in NN$ with $"char" F divides.not n$. A _cyclotomic extension_ of $F$ is a splitting field $E$ of $x^n - 1$ over $F$.
]

#proposition[
  Let $E$ be a cyclotomic extension of $F$ for $x^n - 1$. The roots of $x^n - 1$ in $E$, the _$n$-th roots of unity_, form a cyclic subgroup $mu_n$ of order $n$ of $E^times$. A generator of $mu_n$ is a _primitive $n$-th root of unity_, denoted $zeta_n$, and $E = F(zeta_n)$.
] <prop-mu-n>

#proof[
  The derivative of $x^n - 1$ is $n x^(n - 1)$, which is nonzero because $"char" F divides.not n$ and vanishes only at $0$. Hence $gcd(x^n - 1, n x^(n - 1)) = 1$, and $x^n - 1$ has $n$ distinct roots in $E$ by @prop-sep-gcd. They form a subgroup of $E^times$, since $(alpha beta^(-1))^n = alpha^n beta^(-n) = 1$. A finite subgroup of the multiplicative group of a field is cyclic: the second paragraph of the proof of @thm-finite-field uses only that a polynomial $x^d - 1$ has at most $d$ roots in a field. So $mu_n = {1, zeta_n, dots, zeta_n^(n - 1)}$, and $E$, being generated over $F$ by $mu_n$, equals $F(zeta_n)$.
]

#example[
  For a prime $p$, $QQ(zeta_p)$ is a cyclotomic extension of $QQ$.
]

#proposition[
  Let $E = F(zeta_n)$ be a cyclotomic extension. For $sigma in Gal(E | F)$ there is $r_sigma in ZZ$ with $gcd(r_sigma, n) = 1$ and $sigma(zeta_n) = zeta_n^(r_sigma)$, and $sigma mapsto r_sigma mod n$ is an injective group homomorphism $Gal(E | F) -> U_n$, where $U_n = (ZZ slash n ZZ)^times$. In particular $Gal(E | F)$ is abelian. If $"char" F = 0$ or $F$ is finite, then $E | F$ is Galois and $[E : F] = |Gal(E | F)|$ divides $phi(n)$.
] <prop-cyclo-gal>

#proof[
  By @thm-perm-roots, $sigma$ maps $mu_n$ into itself, and it preserves orders of elements, since it is an injective homomorphism of $E^times$. So $sigma(zeta_n)$ is a primitive $n$-th root of unity, $sigma(zeta_n) = zeta_n^(r_sigma)$ with $gcd(r_sigma, n) = 1$, and $r_sigma$ is determined modulo $n$. For $sigma, tau in Gal(E | F)$,
  $ (tau sigma)(zeta_n) = tau(zeta_n^(r_sigma)) = tau(zeta_n)^(r_sigma) = zeta_n^(r_tau r_sigma), $
  so the map is a homomorphism. It is injective, since $sigma$ is determined by $sigma(zeta_n)$ on $E = F(zeta_n)$.

  If $"char" F = 0$ or $F$ is finite, every irreducible polynomial over $F$ is separable by @lem-sep-deriv and @thm-finite-sep, so $E | F$ is separable. It is normal by @thm-normal-split, being a splitting field. Hence it is Galois, and the last statement follows from @prop-gal-order and Lagrange's theorem, as $|U_n| = phi(n)$.
]

From now on $F = QQ$ and $zeta_n = e^(2 pi i slash n) in CC$. The primitive $n$-th roots of unity in $CC$ are $zeta_n^r$ with $1 <= r <= n$ and $gcd(r, n) = 1$.

#definition(title: [Cyclotomic polynomial])[
  The _$n$-th cyclotomic polynomial_ is
  $ Phi_n (x) = product_(1 <= r <= n, space gcd(r, n) = 1) (x - zeta_n^r), quad deg Phi_n = phi(n). $
]

#proposition[
  For every $n in NN$, $x^n - 1 = product_(d divides n) Phi_d (x)$.
] <prop-xn-prod>

#proof[
  Both sides are monic with simple roots, so it suffices to compare roots. If $zeta^n = 1$ and $zeta$ has order $d$ in $CC^times$, then $d divides n$ and $zeta$ is a primitive $d$-th root of unity, that is, a root of $Phi_d$. Conversely, if $d divides n$, every root $zeta$ of $Phi_d$ satisfies $zeta^n = (zeta^d)^(n slash d) = 1$. Since every root of unity has exactly one order, the roots of the $Phi_d$, $d divides n$, are pairwise distinct.
]

#example[
  If $n = p$ is prime, then $Phi_p (x) = (x^p - 1) / (x - 1) = x^(p - 1) + x^(p - 2) + dots.c + x + 1$, by @prop-xn-prod with $Phi_1 (x) = x - 1$.
]

#proposition[
  $Phi_n in ZZ[x]$ for every $n in NN$.
] <prop-phi-int>

#proof[
  Induction on $n$. For $n = 1$, $Phi_1 (x) = x - 1$. Let $n > 1$ and assume $Phi_k in ZZ[x]$ for every $k <= n - 1$. By @prop-xn-prod,
  $ x^n - 1 = product_(d divides n) Phi_d (x) = Phi_n (x) product_(d divides n, space d != n) Phi_d (x), quad "so" quad Phi_n (x) = (x^n - 1) / (product_(d divides n, space d != n) Phi_d (x)). $
  The denominator is monic and lies in $ZZ[x]$ by the induction hypothesis. Division with remainder by a monic polynomial in $ZZ[x]$ stays in $ZZ[x]$, and the remainder is $0$, so $Phi_n in ZZ[x]$.
]

#remark(title: [Recall])[
  _Gauss's lemma._ If $h in ZZ[x]$ is monic and $h = f g$ with monic $f, g in QQ[x]$, then $f, g in ZZ[x]$.
] <rem-gauss-lemma>

#theorem[
  $Phi_n$ is irreducible over $QQ$. Consequently $[QQ(zeta_n) : QQ] = phi(n)$ and $Gal(QQ(zeta_n) | QQ) tilde.equiv U_n$.
] <thm-phi-irred>

#proof[
  Let $f$ be the minimal polynomial over $QQ$ of a primitive $n$-th root of unity $theta$. Then $f$ is monic and $f divides x^n - 1$, so $x^n - 1 = f g$ with $f, g in ZZ[x]$ monic, by @rem-gauss-lemma. We show that $theta^p$ is a root of $f$ for every prime $p divides.not n$.

  Suppose $f(theta^p) != 0$. Since $(theta^p)^n - 1 = 0 = f(theta^p) g(theta^p)$, we get $g(theta^p) = 0$. So $theta$ is a root of $g(x^p)$, and $f(x) divides g(x^p)$ in $QQ[x]$, hence $g(x^p) = f(x) h(x)$ with $h in ZZ[x]$ by @rem-gauss-lemma. Reduce modulo $p$ and work in $FF_p [x]$; for $q = sum a_i x^i in ZZ[x]$ write $overline(q) = sum (a_i mod p) x^i$. By @thm-frobenius and $a^p = a$ for $a in FF_p$,
  $ overline(g)(x^p) = overline(g)(x)^p = overline(f)(x) overline(h)(x) in FF_p [x]. $
  Hence any irreducible factor of $overline(f)$ divides $overline(g)^p$, hence $overline(g)$, so $overline(f)$ and $overline(g)$ have a common factor. Reducing $x^n - 1 = f g$ gives $x^n - 1 = overline(f) overline(g)$ in $FF_p [x]$, so $x^n - 1$ has a multiple root over $FF_p$. But its derivative $n x^(n - 1)$ is nonzero in $FF_p [x]$, since $p divides.not n$, and $gcd(x^n - 1, n x^(n - 1)) = 1$, contradicting @prop-sep-gcd.

  Since $theta^p$ is again a primitive $n$-th root of unity and $f$, being monic and irreducible with the root $theta^p$, is also its minimal polynomial, the argument applies to $theta^p$ in place of $theta$. Every primitive $n$-th root of unity is $zeta_n^r$ with $gcd(r, n) = 1$, and writing $r = p_1 dots.c p_k$ as a product of primes not dividing $n$, it is obtained from $zeta_n$ by successive prime powers. Hence all primitive $n$-th roots of unity are roots of $f = m_(zeta_n, QQ)$, so $Phi_n$, whose roots are simple, divides $f$ in $QQ[x]$. Since $f$ is irreducible and $Phi_n$ is monic and nonconstant, $f = Phi_n$. The last statement follows from @prop-cyclo-gal, since $|Gal(QQ(zeta_n) | QQ)| = phi(n) = |U_n|$.
]

// [p2]
= Ruler and compass constructions

The two admissible operations in the plane $RR^2$ are:
+ _ruler_: draw the straight line through two given points;
+ _compass_: draw the circle with a given point as centre passing through a given point.

#definition(title: [Constructible point])[
  Let $P_0 subset.eq RR^2$. A point $r in RR^2$ is _constructible_ from $P_0$ if there is a sequence $r_1, dots, r_n = r$ of points such that for each $i = 1, dots, n$, the point $r_i$ is an intersection point of two distinct lines or circles drawn by operations 1 or 2 from points of $P_(i - 1) = P_0 union {r_1, dots, r_(i - 1)}$. A real number $x$ is _constructible_ if $(x, 0)$ is constructible from ${(0, 0), (1, 0)}$.
]

With each stage we associate a subfield of $RR$. Let $KK_0$ be the subfield of $RR$ generated by the coordinates of the points of $P_0$. If $r_i = (x_i, y_i)$, put inductively $KK_i = KK_(i - 1)(x_i, y_i)$. Then $KK_0 subset.eq KK_1 subset.eq dots.c subset.eq KK_n subset.eq RR$.

#lemma[
  For each $i$, the coordinates $x_i$ and $y_i$ are zeros of polynomials of degree at most $2$ over $KK_(i - 1)$.
] <lem-constr-quad>

#proof[
  All points of $P_(i - 1)$ have coordinates in $KK_(i - 1)$. The line through $A = (p, q)$ and $B = (r, s)$ is
  $ (s - q)(x - p) = (r - p)(y - q), $
  a linear equation with coefficients in $KK_(i - 1)$. The circle with centre $C = (t, u)$ through $D = (v, w)$ is
  $ (x - t)^2 + (y - u)^2 = rho^2, quad rho^2 = (v - t)^2 + (w - u)^2 in KK_(i - 1), $
  that is, $x^2 + y^2 + a x + b y + c = 0$ with $a, b, c in KK_(i - 1)$.

  _Two lines._ The intersection point solves a $2 times 2$ linear system over $KK_(i - 1)$ with nonzero determinant, so $x_i, y_i in KK_(i - 1)$ by Cramer's rule.

  _A line and a circle._ If the line is not vertical, it is $y = m x + k$ with $m, k in KK_(i - 1)$. Substituting into the circle gives a polynomial of degree $2$ over $KK_(i - 1)$ vanishing at $x_i$, and $y_i = m x_i + k$ satisfies the polynomial obtained by substituting $x = (y - k) slash m$ if $m != 0$, or $y_i = k$ if $m = 0$. A vertical line $x = k$ gives $x_i = k$ and a quadratic equation for $y_i$.

  _Two circles._ Subtracting the equations of two distinct circles $x^2 + y^2 + a x + b y + c = 0$ and $x^2 + y^2 + a' x + b' y + c' = 0$ gives the linear equation $(a - a') x + (b - b') y + (c - c') = 0$. If $a = a'$ and $b = b'$, the circles are concentric and distinct and do not meet. Otherwise this is a line over $KK_(i - 1)$ through every common point, and we are in the previous case.
]

#theorem[
  If $r = (x, y)$ is constructible from $P_0 subset.eq RR^2$ and $KK_0$ is the subfield of $RR$ generated by the coordinates of the points of $P_0$, then $[KK_0 (x) : KK_0]$ and $[KK_0 (y) : KK_0]$ are powers of $2$.
] <thm-constr-deg>

#proof[
  By @lem-constr-quad, $[KK_(i - 1)(x_i) : KK_(i - 1)] in {1, 2}$, and $y_i$ is a zero of a polynomial of degree at most $2$ over $KK_(i - 1) subset.eq KK_(i - 1)(x_i)$, so $[KK_(i - 1)(x_i, y_i) : KK_(i - 1)(x_i)] in {1, 2}$. By the tower law
  $ [KK_(i - 1)(x_i, y_i) : KK_(i - 1)] = [KK_(i - 1)(x_i, y_i) : KK_(i - 1)(x_i)] [KK_(i - 1)(x_i) : KK_(i - 1)] in {1, 2, 4}. $
  Since $KK_i = KK_(i - 1)(x_i, y_i)$, the tower law gives that $[KK_n : KK_0]$ is a power of $2$. As $x = x_n in KK_n$, $[KK_n : KK_0] = [KK_n : KK_0 (x)] [KK_0 (x) : KK_0]$, so $[KK_0 (x) : KK_0]$ divides a power of $2$ and is itself a power of $2$. The same holds for $y$.
]

Below, $P_0 = {(0, 0), (1, 0)}$, so $KK_0 = QQ$. We use the elementary fact that if a segment of length $ell$ has been constructed, so has $(ell, 0)$: transfer the segment to the origin and intersect the circle of radius $ell$ about $(0, 0)$ with the $x$-axis.

#theorem(title: [Duplication of the cube])[
  The cube cannot be duplicated with ruler and compass: there is no construction from $P_0$ of the side of a cube whose volume is twice the volume of the unit cube.
]

#proof[
  The unit cube has volume $1$. A cube of volume $2$ has side $alpha = root(3, 2)$, so a duplication would make $(alpha, 0)$ constructible from $P_0$. By @thm-constr-deg, $[QQ(alpha) : QQ]$ would be a power of $2$. But $alpha$ is a root of $x^3 - 2$, which is irreducible over $QQ$, since it has degree $3$ and no rational root ($3 v_2 (z) = 1$ is impossible). So $[QQ(alpha) : QQ] = 3$, which is not a power of $2$.
]

#theorem(title: [Trisection of the angle])[
  The angle $60 degree$ cannot be trisected with ruler and compass.
]

#proof[
  The angle $60 degree$ is constructible from $P_0$: the circles of radius $1$ about $(0, 0)$ and $(1, 0)$ meet at $(1 slash 2, sqrt(3) slash 2)$. A trisection would make the point $(cos 20 degree, sin 20 degree)$, and hence $alpha = cos 20 degree$, constructible from $P_0$. Recall $cos(3 beta) = 4 cos^3 beta - 3 cos beta$. With $beta = 20 degree$,
  $ 1 / 2 = cos 60 degree = 4 cos^3 20 degree - 3 cos 20 degree <==> 8 cos^3 20 degree - 6 cos 20 degree - 1 = 0, $
  so $alpha$ is a root of $f(x) = 8 x^3 - 6 x - 1$. Putting $y = 2 x$, $f(x) = y^3 - 3 y - 1$. A rational root of the monic integer polynomial $y^3 - 3 y - 1$ would be an integer dividing $1$, but $1 - 3 - 1 = -3$ and $-1 + 3 - 1 = 1$. So $y^3 - 3 y - 1$ has no rational root, and being cubic, it is irreducible over $QQ$; hence so is $f$. Therefore $[QQ(cos 20 degree) : QQ] = 3$, not a power of $2$, contradicting @thm-constr-deg.
]

#theorem(title: [Squaring the circle])[
  The circle cannot be squared with ruler and compass: there is no construction of a square whose area equals that of a given circle.
]

#proof[
  Take the unit circle with centre $(0, 0)$, so $P_0$ is as above. A square of area $pi$ has side $sqrt(pi)$, so squaring the circle would make $(sqrt(pi), 0)$ constructible. By @thm-constr-deg, $[QQ(sqrt(pi)) : QQ]$ would be a power of $2$, in particular finite, so $sqrt(pi)$ and hence $pi = (sqrt(pi))^2$ would be algebraic over $QQ$. This contradicts the following theorem.
]

#theorem(title: [Lindemann], cited: true)[
  $pi$ is transcendental over $QQ$.
]
