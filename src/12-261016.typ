#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 12-261016 · Fermat primes, regular polygons, worked exercises on Galois groups, solvable groups
// Scans are tablet screenshots.
// HEADINGS section 21 continued; section 22 coined; section 23 from source ("Solvable groups")
// DROPPED
//   [p1] decorative sketch of the angle 2 pi / n (listed, not drawn); Hungarian gloss "Feloldhato csoport"
// CORRECTIONS
//   [p1] n-gon theorem: "odd prime divisors of n are distinct Fermat primes" -> n = 2^k p_1 ... p_r, p_i distinct Fermat primes (each to the first power)
//   [p1] n = p_1^a_1 + ... + p_r^a_r -> product
//   [p1] cos^2(2 pi / 2) -> cos^2(2 pi / n)
//   [p1] x^4 - 2 = (x + 4rt2)(x - 4rt2)(x - 4rt2)(x + 4rt2) -> (x - 4rt2)(x + 4rt2)(x - i 4rt2)(x + i 4rt2)
//   [p2] G = <s, s^2, s^3, 1, t, st, s^2 t^2, s t^3> -> {1, s, s^2, s^3, t, st, s^2 t, s^3 t}; tau fixed as complex conjugation
//   [p2] roots of x^3 + 2: x_1 = cbrt 2 -> -cbrt 2
//   [p3] ex. 4: alpha_i - c_i -> alpha_i - c
//   [p4] A_n simple: "has no nontrivial subgroup" -> no normal subgroup other than 1 and A_n
//   [p4] ex. 7: "f(x) is irreducible over Q" false for general a (a = 10/3 gives the rational root 2) -> shown for a = 5
// MISSING
//   [p4] ex. 7: statement of the exercise not recorded
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: Fermat prime lemma completed (t odd forces t = 1); definition of constructible n-gon; degree argument via Q(cos)(i sin)
//   [p1] C: sufficiency in the Gauss-Wantzel theorem
//   [p1-2] A: ex. 1: degree 8, existence of sigma and tau, relation checked on i, D_4 presentation
//   [p2] A: ex. 2: Eisenstein, roots in Q(alpha), sigma^2(alpha) = -alpha; ex. 3: Eisenstein, degree 6, injectivity into S_3
//   [p3] A: ex. 3b: sqrt 5 not in Q(sqrt 2); ex. 4: definition of the Galois group of a polynomial; ex. 5: F is the root set, fundamental theorem used
//   [p4] A: ex. 6: angle arithmetic recalled; 1 degree -> 20 degrees; ex. 7: figure redrawn, a = 5 worked out
//   [p4] B: derived series vs abelian normal series; products; cyclic refinement; S_n solvable iff n <= 4
//   [p4] C: simplicity of A_n

// [p1]
#lemma[
  Let $t in NN$. If $2^t + 1$ is prime, then $t$ is a power of $2$.
] <lem-fermat>

#proof[
  If $t$ is odd, then $2 equiv -1 pmod(3)$ gives $2^t equiv (-1)^t = -1 pmod(3)$, so $3 divides 2^t + 1$; as $2^t + 1$ is prime, $2^t + 1 = 3$ and $t = 1 = 2^0$. In general write $t = 2^k r$ with $k >= 0$ and $r$ odd. Then
  $ 2^t + 1 = (2^(2^k))^r + 1 equiv (-1)^r + 1 = 0 pmod(2^(2^k) + 1), $
  so $2^(2^k) + 1$ divides the prime $2^t + 1$. Since $2^(2^k) + 1 > 1$, it equals $2^t + 1$, so $r = 1$ and $t = 2^k$.
]

#definition(title: [Fermat numbers])[
  The _Fermat numbers_ are $F_n = 2^(2^n) + 1$, $n >= 0$. A prime of this form is a _Fermat prime_. The first five, $F_0 = 3$, $F_1 = 5$, $F_2 = 17$, $F_3 = 257$, $F_4 = 65537$, are prime.
]

#definition[
  Let $n >= 3$. The regular $n$-gon is _constructible_ by ruler and compass if the point $(cos(2 pi slash n), sin(2 pi slash n))$ is constructible from $P_0 = {(0, 0), (1, 0)}$.
]

#theorem(title: [Regular $n$-gon])[
  Let $n >= 3$. The regular $n$-gon is constructible by ruler and compass if and only if $n = 2^k p_1 dots.c p_r$ with $k, r >= 0$ and $p_1, dots, p_r$ pairwise distinct Fermat primes.
] <thm-ngon>

#proof[
  We prove necessity; sufficiency is cited below. Suppose the regular $n$-gon is constructible. Then $c = cos(2 pi slash n)$ is a coordinate of a constructible point, so $[QQ(c) : QQ]$ is a power of $2$ by @thm-constr-deg. Let $s = sin(2 pi slash n)$ and $epsilon_n = c + i s = zeta_n$. Since
  $ (i s)^2 = -s^2 = c^2 - 1 in QQ(c), $
  the degree $[QQ(c)(i s) : QQ(c)]$ is $1$ or $2$, so $[QQ(c, i s) : QQ]$ is a power of $2$. As $epsilon_n in QQ(c, i s)$, the tower law and @thm-phi-irred show that $phi(n) = [QQ(epsilon_n) : QQ]$ divides a power of $2$, so $phi(n) = 2^m$ for some $m$.

  // [p1-p2]
  Write $n = 2^k p_1^(alpha_1) dots.c p_r^(alpha_r)$ with distinct odd primes $p_i$ and $alpha_i >= 1$. Then
  $ phi(n) = phi(2^k) (p_1^(alpha_1) - p_1^(alpha_1 - 1)) dots.c (p_r^(alpha_r) - p_r^(alpha_r - 1)) = phi(2^k) p_1^(alpha_1 - 1) dots.c p_r^(alpha_r - 1) (p_1 - 1) dots.c (p_r - 1) = 2^m. $
  As the $p_i$ are odd, $alpha_i = 1$ and $p_i - 1 = 2^(beta_i)$ for every $i$. By @lem-fermat each $p_i = 2^(beta_i) + 1$ is a Fermat prime.
]

#theorem(title: [Gauss], cited: true)[
  If $n = 2^k p_1 dots.c p_r$ with pairwise distinct Fermat primes $p_i$, then the regular $n$-gon is constructible.
]

= Worked exercises on Galois groups

#remark(title: [Recall])[
  _Schönemann--Eisenstein criterion._ Let $f = a_n x^n + dots.c + a_0 in ZZ[x]$ and $p$ a prime with $p divides.not a_n$, $p divides a_i$ for $i < n$ and $p^2 divides.not a_0$. Then $f$ is irreducible over $QQ$.
] <rem-eisenstein>

#example[
  Determine $G = Gal(QQ(root(4, 2), i) | QQ)$.
]

#solution[
  Let $a = root(4, 2) > 0$. Over $CC$,
  $ x^4 - 2 = (x^2 + sqrt(2))(x^2 - sqrt(2)) = (x - a)(x + a)(x - i a)(x + i a), $
  so $E = QQ(a, i)$ is the splitting field of $x^4 - 2$, and $E | QQ$ is normal by @thm-normal-split and Galois since $"char" QQ = 0$. By @rem-eisenstein with $p = 2$, $x^4 - 2$ is irreducible over $QQ$, so $[QQ(a) : QQ] = 4$. Since $i in.not QQ(a) subset.eq RR$, $[E : QQ(a)] = 2$, and $|G| = [E : QQ] = 8$ by @prop-gal-order. By the tower law $[E : QQ(i)] = 4$, so $x^4 - 2$ is the minimal polynomial of $a$ over $QQ(i)$.

  Let $tau$ be complex conjugation restricted to $E$; it maps $E$ onto $E$ by @prop-normal-crit, so $tau in G$, with $tau(a) = a$, $tau(i) = -i$. By @lem-extend, the $QQ(i)$-embedding $QQ(i)(a) -> CC$ with $a mapsto i a$ exists, and it maps $E$ onto $E$ by @prop-normal-crit; call it $sigma$. So $sigma(a) = i a$, $sigma(i) = i$, and
  // [p2]
  $ sigma^2 (a) = sigma(i a) = -a, quad sigma^3 (a) = sigma(-a) = -i a, quad sigma^4 (a) = a. $
  Hence $sigma$ has order $4$, $tau$ has order $2$, and the eight elements $1, sigma, sigma^2, sigma^3, tau, sigma tau, sigma^2 tau, sigma^3 tau$ are pairwise distinct, since they differ on $a$ or on $i$. So
  $ G = {1, sigma, sigma^2, sigma^3, tau, sigma tau, sigma^2 tau, sigma^3 tau}. $
  Checking on the generators, $tau^(-1) sigma tau (a) = tau sigma(a) = tau(i a) = -i a = sigma^3 (a)$ and $tau^(-1) sigma tau (i) = i = sigma^3 (i)$, so $tau^(-1) sigma tau = sigma^3 = sigma^(-1)$. Therefore $G tilde.equiv D_4 = chevron.l sigma, tau mid(|) sigma^4 = tau^2 = 1, tau sigma tau = sigma^(-1) chevron.r$, the dihedral group of order $8$.
]

#example[
  Determine $G = Gal(QQ(sqrt(2 + sqrt(2))) | QQ)$.
]

#solution[
  Let $alpha = sqrt(2 + sqrt(2))$. Then
  $ alpha^2 = 2 + sqrt(2) <==> alpha^2 - 2 = sqrt(2) ==> (alpha^2 - 2)^2 = 2 <==> alpha^4 - 4 alpha^2 + 2 = 0. $
  By @rem-eisenstein with $p = 2$, $x^4 - 4 x^2 + 2$ is irreducible, so $m_(alpha, QQ) = x^4 - 4 x^2 + 2$ and $[QQ(alpha) : QQ] = 4$. Its roots are $plus.minus sqrt(2 plus.minus sqrt(2))$. Let $beta = sqrt(2 - sqrt(2))$; since $alpha beta = sqrt(4 - 2) = sqrt(2)$, we get $beta = sqrt(2) slash alpha = (alpha^2 - 2) slash alpha in QQ(alpha)$. So all roots lie in $QQ(alpha)$, which is their splitting field; $QQ(alpha) | QQ$ is normal and separable, hence Galois, and $|G| = 4$.

  Let $sigma in G$ with $sigma(alpha) = beta$; it exists by @thm-embed-count and @prop-normal-crit, since $beta$ is a root of $m_(alpha, QQ)$. Then
  // [p2-p3]
  $ 2 + sigma(sqrt(2)) = sigma(2 + sqrt(2)) = sigma(alpha^2) = sigma(alpha)^2 = beta^2 = 2 - sqrt(2), $
  so $sigma(sqrt(2)) = -sqrt(2)$, and
  $ sigma^2 (alpha) = sigma(beta) = sigma(sqrt(2) / alpha) = sigma(sqrt(2)) / sigma(alpha) = (-sqrt(2)) / beta = -alpha. $
  Hence $sigma^2 != "id"$, $sigma$ has order $4$, and $G = chevron.l sigma chevron.r tilde.equiv ZZ_4$.
]

#example[
  Determine the Galois groups of $x^3 + 2$ and $x^4 - 7 x^2 + 10$ over $QQ$.
]

#solution[
  _$x^3 + 2$._ Since $x^3 + 2 = x^3 + (root(3, 2))^3 = (x + root(3, 2))(x^2 - root(3, 2) x + root(3, 4))$, the roots are
  $ x_1 = -root(3, 2), quad x_2 = root(3, 2) / 2 + (i sqrt(3) root(3, 2)) / 2, quad x_3 = root(3, 2) / 2 - (i sqrt(3) root(3, 2)) / 2. $
  The splitting field is $E = QQ(root(3, 2), i sqrt(3))$. By @rem-eisenstein with $p = 2$, $x^3 + 2$ is irreducible, so $[QQ(root(3, 2)) : QQ] = 3$, and $i sqrt(3) in.not QQ(root(3, 2)) subset.eq RR$ gives $[E : QQ] = 6 = |G|$ by @prop-gal-order. Each $sigma in G$ permutes ${x_1, x_2, x_3}$ by @thm-perm-roots and is determined by this permutation, since $E$ is generated by the roots. This gives an injective homomorphism $G -> S_3$, and as $|S_3| = 3! = 6 = |G|$, $G tilde.equiv S_3$.

  // [p3]
  _$x^4 - 7 x^2 + 10 = (x^2 - 5)(x^2 - 2)$._ The roots are $plus.minus sqrt(5), plus.minus sqrt(2)$, and the splitting field is $E = QQ(sqrt(2), sqrt(5))$. Here $sqrt(5) in.not QQ(sqrt(2))$: if $sqrt(5) = u + v sqrt(2)$ with $u, v in QQ$, then $5 = u^2 + 2 v^2 + 2 u v sqrt(2)$ forces $u v = 0$, and $v = 0$ or $u = 0$ would make $sqrt(5)$ or $sqrt(5 slash 2)$ rational. Hence $[E : QQ] = 4 = |G|$. As in the example on $QQ(i, sqrt(5))$ in Section 18, the elements of $G$ are given by sign changes:
  $ sigma: sqrt(5) mapsto -sqrt(5), space sqrt(2) mapsto sqrt(2); quad tau: sqrt(2) mapsto -sqrt(2), space sqrt(5) mapsto sqrt(5); quad sigma tau: sqrt(2) mapsto -sqrt(2), space sqrt(5) mapsto -sqrt(5). $
  Each satisfies $sigma^2 = tau^2 = (sigma tau)^2 = "id"$, so $G = {"id", sigma, tau, sigma tau} tilde.equiv ZZ_2 times ZZ_2$, the Klein four-group.
]

#definition(title: [Galois group of a polynomial])[
  Let $F$ be a field and $f in F[x]$ nonconstant. The _Galois group of $f$ over $F$_ is $Gal(E | F)$, where $E$ is a splitting field of $f$ over $F$.
]

#example[
  Let $F$ be a field, $f in F[x]$ and $c in F$. Show that the Galois groups of $f(x)$ and $f(x + c)$ over $F$ are isomorphic.
]

#solution[
  Let $alpha_1, dots, alpha_n$ be the roots of $f$ in an algebraic closure $overline(F)$. Then $f(beta + c) = 0$ if and only if $beta + c = alpha_i$ for some $i$, so the roots of $f(x + c)$ are $alpha_1 - c, dots, alpha_n - c$. Their splitting fields in $overline(F)$ are
  $ L = F(alpha_1, dots, alpha_n), quad L' = F(alpha_1 - c, dots, alpha_n - c), $
  and $L = L'$, since $c in F$. So both Galois groups equal $Gal(L | F)$.
]

#example[
  Let $F$ be a finite field with $"char" F = p$ and $|F| = p^n$. Show that $F | FF_p$ is a Galois extension whose Galois group is generated by the Frobenius automorphism $sigma(x) = x^p$.
]

#solution[
  Let $f(x) = x^(p^n) - x$. Then $f'(x) = p^n x^(p^n - 1) - 1 = -1$, so $f$ is separable by @prop-sep-gcd. By @thm-finite-field every element of $F$ is a root of $f$, and $f$ has at most $p^n$ roots, so $F$ is exactly the set of roots of $f$ and is a splitting field of $f$ over $FF_p$. Hence $F | FF_p$ is normal (@thm-normal-split) and separable (@thm-finite-sep), so it is a Galois extension.

  // [p3-p4]
  Let $G = Gal(F | FF_p)$. By @thm-frob-aut with $q = p$, $sigma in G$, so $FF_p subset.eq cal(F)(chevron.l sigma chevron.r)$. The fixed field of $chevron.l sigma chevron.r$ consists of the roots of $x^p - x$ in $F$, so it has at most $p$ elements; hence $cal(F)(chevron.l sigma chevron.r) = FF_p$. By @thm-fundamental-1, $chevron.l sigma chevron.r = cal(G)(FF_p) = G$. This reproves part of @thm-frob-aut for $q = p$.
]

// [p4]
#remark(title: [Recall])[
  For angles, measured in degrees: an angle $alpha$ is _constructible_ if $(cos alpha, sin alpha)$ is constructible from $P_0 = {(0, 0), (1, 0)}$. Sums and differences of constructible angles are constructible, and so is half of a constructible angle.
]

#example[
  For which $n in NN$ is the angle $n degree$ constructible?
]

#solution[
  We show that $n degree$ is constructible if and only if $3 divides n$. By @thm-ngon the regular $5$-gon is constructible, $5$ being a Fermat prime, so $72 degree$ is constructible. The angle $60 degree$ is constructible, hence so are $12 degree = 72 degree - 60 degree$, $3 degree$ (bisecting twice) and every multiple $3 k degree$.

  Conversely, if $(3 k + 1) degree$ were constructible, so would be $1 degree = (3 k + 1) degree - 3 k degree$. If $(3 k + 2) degree$ were constructible, so would be $1 degree = 3 (k + 1) degree - (3 k + 2) degree$. Then $20 degree$, a sum of twenty copies of $1 degree$, would be constructible, and the angle $60 degree$ could be trisected, contradicting the trisection theorem of Section 21.
]

#example[
  #missing[p4][statement of the exercise not recorded; the solution concerns an isosceles triangle with legs $a$, base $2 b$, height $f_a$ and inscribed circle of radius $r$]
]

#solution[
  #figure(
    box(width: 5cm, height: 4.2cm, {
      let A = (2.5cm, 0.2cm)
      let B = (0.5cm, 3.4cm)
      let C = (4.5cm, 3.4cm)
      let M = (2.5cm, 3.4cm)
      let r = 1.07cm
      place(line(start: A, end: B, stroke: 0.6pt))
      place(line(start: A, end: C, stroke: 0.6pt))
      place(line(start: B, end: C, stroke: 0.6pt))
      place(line(start: A, end: M, stroke: (paint: black, thickness: 0.5pt, dash: "dashed")))
      place(dx: 2.5cm - r, dy: 3.4cm - 2 * r, circle(radius: r, stroke: 0.5pt + rule-colour.darken(30%)))
      let lab(x, y, body) = place(dx: x, dy: y, box(width: 0pt, height: 0pt, align(center + horizon, box(fill: white, inset: 1.5pt, text(size: 9pt, body)))))
      lab(3.75cm, 1.6cm, $a$)
      lab(1.5cm, 3.75cm, $b$)
      lab(3.5cm, 3.75cm, $b$)
      lab(2.25cm, 1.0cm, $f_a$)
      lab(2.75cm, 2.6cm, $r$)
    }),
    caption: [Isosceles triangle with legs $a$, base $2 b$, height $f_a$ and inradius $r$.],
  ) <fig-isosceles>
  The height is $f_a = sqrt(a^2 - b^2)$ and the semiperimeter is $S = (2 a + 2 b) slash 2 = a + b$. Computing the area in two ways,
  $ (2 b dot f_a) / 2 = b f_a, quad r S = r (a + b), $
  where $r$ is the radius of the inscribed circle. Hence $b sqrt(a^2 - b^2) = r (a + b)$, so $b^2 (a^2 - b^2) = r^2 (a + b)^2$, and dividing by $a + b > 0$,
  $ b^2 (a - b) = r^2 (a + b) <==> b^3 - a b^2 + r^2 a + r^2 b = 0. $
  With $r = 1$, $b$ is a root of $f(x) = x^3 - a x^2 + x + a$.

  Whether $f$ is irreducible over $QQ$ depends on $a$: for $a = 10 slash 3$, $f(2) = 8 - 40 slash 3 + 2 + 10 slash 3 = 0$. Take $a = 5$. Then $f(x) = x^3 - 5 x^2 + x + 5$ has no rational root, since $f(1) = 2$, $f(-1) = -2$, $f(5) = 10$, $f(-5) = -150$, so it is irreducible over $QQ$. It has roots in $(1, 2)$ and $(4, 5)$, since $f(1) = 2 > 0 > -5 = f(2)$ and $f(4) = -7 < 0 < 10 = f(5)$; each gives an isosceles triangle with leg $5$ and inradius $1$. For both, $[QQ(b) : QQ] = 3$, which is not a power of $2$, so $b$ is not constructible from the data $a = 5$, $r = 1$ by @thm-constr-deg.
]

= Solvable groups

#remark(title: [Recall])[
  For a group $G$, the _commutator subgroup_ $G' = chevron.l g^(-1) h^(-1) g h : g, h in G chevron.r$ is a normal subgroup of $G$. For $N lt.closed.eq G$, the quotient $G slash N$ is abelian if and only if $G' <= N$. If $phi: G -> H$ is a surjective homomorphism, then $phi(G') = H'$.
]

#definition(title: [Derived series, solvable group])[
  The _derived series_ (commutator series) of a group $G$ is $G^((0)) = G$, $G^((n + 1)) = (G^((n)))'$ for $n >= 0$. The group $G$ is _solvable_ if $G^((k)) = 1$ for some $k in NN$.
]

#definition(title: [Normal series])[
  A _normal series_ of $G$ is a chain $1 = H_0 lt.closed.eq H_1 lt.closed.eq dots.c lt.closed.eq H_n = G$ of subgroups, each normal in the next. Its _factors_ are the groups $H_(i + 1) slash H_i$.
]

#proposition[
  A group $G$ is solvable if and only if it has a normal series with abelian factors.
] <prop-solv-series>

#proof[
  $(arrow.r.double)$ If $G^((k)) = 1$, then $1 = G^((k)) lt.closed.eq G^((k - 1)) lt.closed.eq dots.c lt.closed.eq G^((0)) = G$, and $G^((i)) slash G^((i + 1)) = G^((i)) slash (G^((i)))'$ is abelian.

  $(arrow.l.double)$ Let $1 = H_0 lt.closed.eq dots.c lt.closed.eq H_n = G$ have abelian factors. We show $G^((i)) <= H_(n - i)$ by induction on $i$. For $i = 0$ this is $G = H_n$. If $G^((i)) <= H_(n - i)$, then $G^((i + 1)) = (G^((i)))' <= (H_(n - i))' <= H_(n - i - 1)$, the last inclusion because $H_(n - i) slash H_(n - i - 1)$ is abelian. For $i = n$ we get $G^((n)) <= H_0 = 1$.
]

#proposition[
  If $G$ and $H$ are solvable groups, then so is $G times H$.
]

#proof[
  Commutators in $G times H$ are formed componentwise, so $(G times H)' = G' times H'$, and by induction $(G times H)^((i)) = G^((i)) times H^((i))$. If $G^((k)) = 1$ and $H^((l)) = 1$, then $(G times H)^((max(k, l))) = 1$.
]

#proposition[
  A finite group $G$ is solvable if and only if it has a normal series whose factors are cyclic.
] <prop-solv-cyclic>

#proof[
  Cyclic groups are abelian, so one direction is @prop-solv-series. Conversely, take a normal series with abelian factors. It suffices to refine each step $H_i lt.closed.eq H_(i + 1)$ with $A = H_(i + 1) slash H_i$ finite abelian. By induction on $|A|$, $A$ has a chain $1 = A_0 <= A_1 <= dots.c <= A_s = A$ with cyclic factors: for $A != 1$ choose $1 != g in A$, put $A_1 = chevron.l g chevron.r$, and lift a chain of $A slash A_1$, which is smaller. Every subgroup of the abelian group $A$ is normal in it, and the preimages of the $A_j$ in $H_(i + 1)$ form a chain from $H_i$ to $H_(i + 1)$, each normal in the next, with factors $A_(j + 1) slash A_j$.
]

#definition(title: [Alternating group])[
  $A_n$ is the group of even permutations of ${1, dots, n}$; $|A_n| = n! slash 2$ for $n >= 2$. A group is _simple_ if its only normal subgroups are $1$ and itself.
]

#theorem(cited: true)[
  $A_n$ is simple for $n >= 5$.
]

#theorem[
  $S_n$ is solvable if and only if $n <= 4$.
] <thm-sn-solvable>

#proof[
  $S_1$ and $S_2$ are abelian. $1 lt.closed.eq A_3 lt.closed.eq S_3$ has factors of orders $3$ and $2$. For $S_4$, let $V = {"id", (1 2)(3 4), (1 3)(2 4), (1 4)(2 3)}$, which is normal in $S_4$, being the union of $"id"$ and a conjugacy class. Then $1 lt.closed.eq V lt.closed.eq A_4 lt.closed.eq S_4$ has factors $V tilde.equiv ZZ_2 times ZZ_2$, $A_4 slash V$ of order $3$, and $S_4 slash A_4$ of order $2$, all abelian. By @prop-solv-series these groups are solvable.

  Let $n >= 5$. Since $(1 2 3)(3 4 5) != (3 4 5)(1 2 3)$, $A_n$ is not abelian, so $A_n' != 1$. As $A_n'$ is normal in the simple group $A_n$, $A_n' = A_n$, and the derived series of $A_n$ is constant. Since $A_n <= S_n$, induction gives $A_n = A_n^((i)) <= S_n^((i))$ for every $i$, so the derived series of $S_n$ never reaches $1$, and $S_n$ is not solvable.
]
