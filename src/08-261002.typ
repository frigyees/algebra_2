#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 08-261002 · Frobenius automorphism, separability, embeddings, primitive element, normal extensions
// Translated from Hungarian. The printed sheet visible under the notebook on p2 and p4 is not part of the notes.
// HEADINGS section 17 from source ("Testbővítések"); subsections 17.1-17.4 coined
// DROPPED
//   [p1] all: repeats 06-260925 (p | binom(p, j), Frobenius map, roots of irreducibles, conjugates, automorphism, examples)
//   [p2] trace, norm and their lemma: repeats 07-260928
// CORRECTIONS
//   [p2] "let beta in F_q" -> beta in F_(q^m)
//   [p3] "over a finite field every polynomial is separable" -> every irreducible polynomial ((x + 1)^2 over F_2 is not separable)
//   [p3] separability defined for irreducible f only, but applied to (x - 1)^2 (x - 2) and to arbitrary f -> defined for every nonzero f
// READINGS
//   [p3] last line of the finite-field proof read as "contradiction, since f' = 0"; completed via f = h^p
// ADDITIONS (A filled in, B supplied proof)
//   [p2] A: f taken as the minimal polynomial of a generator of F_(q^m)^x; Phi fixes F_q; distinctness of the powers; psi = Phi^k from psi(beta)
//   [p3] A: recalled results on extensions; gcd unchanged under extension; char-0 and f' != 0 lemma
//   [p3] A: f' = 0 => f in F[x^p]; surjectivity of Frobenius; f = h^p
//   [p4] A: tower theorem: alpha algebraic over K, m_(alpha,K) | m_(alpha,F)
//   [p4] A: irreducibility of x^p - t and t^(1/p) not in F_p(t)
//   [p4] A: permutation statement: injectivity on the finite root set
//   [p4-5] A: embedding theorem stated for an algebraically closed target L (needed for the induction; L = F-bar is the source's case)
//   [p5] A: well-definedness of psi, g irreducible and separable, bijection between extensions of sigma and roots of g
//   [p5] B: proof of the primitive element theorem; A: remark on the two meanings of "primitive element" (F_9 example)
//   [p5] A: F subset E subset C in the normality theorem; irreducibility of x^3 - 2; normality of every quadratic extension
//   [p5] A: tau(E) = E by dimension; existence of tau via the embedding theorem in characteristic 0

// [p2]
= Field extensions

== The Frobenius automorphism

#definition(title: [Frobenius automorphism])[
  The map $Phi: FF_(q^m) -> FF_(q^m)$, $Phi(alpha) = alpha^q$, is the _Frobenius automorphism_ of $FF_(q^m)$ over $FF_q$.
]

#theorem[
  The $FF_q$-automorphisms of $FF_(q^m)$ are exactly $Phi, Phi^2, dots, Phi^m = "id"$, and these are pairwise distinct.
] <thm-frob-aut>

#proof[
  $Phi$ is an iterate of $a mapsto a^p$, where $p = "char" FF_q$, since $q$ is a power of $p$; so it is a ring homomorphism by @thm-frobenius. It fixes $FF_q$, since $a^q = a$ for $a in FF_q$ by @thm-finite-field. It is injective: $Phi(alpha) = Phi(beta)$ if and only if $Phi(alpha - beta) = 0$, if and only if $(alpha - beta)^q = 0$, if and only if $alpha = beta$. An injective map of the finite set $FF_(q^m)$ into itself is surjective. So $Phi$ is an $FF_q$-automorphism, and so are its powers. By @thm-finite-field applied to $FF_(q^m)$, $Phi^m (alpha) = alpha^(q^m) = alpha$, so $Phi^m = "id"$.

  Let $beta$ be a generator of $FF_(q^m)^times$ (@thm-finite-field). Then $FF_q (beta) = FF_(q^m)$, so by @rem-recall-ext the minimal polynomial $f(x) = x^m + a_(m - 1) x^(m - 1) + dots.c + a_0 in FF_q [x]$ of $beta$ has degree $m$. By @lem-roots-irred its roots in $FF_(q^m)$ are the pairwise distinct elements $beta, beta^q, dots, beta^(q^(m - 1))$. Hence $Phi^k (beta) = beta^(q^k)$, $1 <= k <= m$, are pairwise distinct, and so are $Phi, dots, Phi^m$.

  Now let $psi$ be an $FF_q$-automorphism of $FF_(q^m)$. Then
  $ 0 = psi(0) = psi(f(beta)) = psi(beta^m + a_(m - 1) beta^(m - 1) + dots.c + a_0). $
  Since $psi$ is an $FF_q$-automorphism, it fixes the coefficients, hence
  $ psi(f(beta)) = psi(beta)^m + a_(m - 1) psi(beta)^(m - 1) + dots.c + a_1 psi(beta) + a_0 = f(psi(beta)). $
  So $psi(beta)$ is a root of $f$, that is, $psi(beta) = beta^(q^k) = Phi^k (beta)$ for some $1 <= k <= m$. Two $FF_q$-automorphisms that agree on $beta$ agree on every $g(beta)$ with $g in FF_q [x]$, that is, on $FF_q (beta) = FF_(q^m)$. Hence $psi = Phi^k$.
]

// [p3]
== Separable extensions

#remark(title: [Recall])[
  Let $F$ be a field. We write $E | F$ for a field extension $F subset.eq E$.
  + $[E : F]$ is the dimension of $E$ over $F$, and $E | F$ is _finite_ if it is finite. For $F subset.eq K subset.eq E$, $[E : F] = [E : K] [K : F]$ (tower law).
  + $alpha in E$ is _algebraic_ over $F$ if $g(alpha) = 0$ for some $0 != g in F[x]$. Then its minimal polynomial $m_(alpha, F)$ is irreducible, divides every $g in F[x]$ with $g(alpha) = 0$, and $[F(alpha) : F] = deg m_(alpha, F)$. Every element of a finite extension is algebraic; $E | F$ is _algebraic_ if every element of $E$ is.
  + If $f in F[x]$ is irreducible, then $F[x] slash (f)$ is an extension of degree $deg f$ containing a root of $f$. If $alpha$ is a root of $f$ in an extension, then $g(x) + (f) mapsto g(alpha)$ is an isomorphism $F[x] slash (f) -> F(alpha)$.
  + Every nonzero $f in F[x]$ has a _splitting field_, an extension in which $f$ is a product of linear factors and which is generated by the roots of $f$; it is unique up to $F$-isomorphism.
  + Every field $F$ has an _algebraic closure_ $overline(F)$, an algebraic extension in which every nonconstant polynomial has a root. $CC$ is algebraically closed.
  + The monic greatest common divisor of $f, g in F[x]$ is the same in $K[x]$ for every extension $K | F$, since the Euclidean algorithm runs in $F[x]$.
  + If $S$ is an infinite subset of a field $L$, a nonzero $P in L[c_1, dots, c_k]$ does not vanish on all of $S^k$.
  A ring homomorphism between fields is injective; it is called an _embedding_ or _monomorphism_, and an _$F$-monomorphism_ if it fixes $F$ pointwise.
] <rem-recall-fields>

#definition(title: [Separable polynomial])[
  A nonzero polynomial $f in F[x]$ is _separable_ if every root of $f$ in its splitting field is simple.
]

#example[
  $x^2 + 1 in RR[x]$ has splitting field $CC$ and simple roots $plus.minus i$, so it is separable. $(x - 1)^2 (x - 2) in QQ[x]$ is not separable, since $1$ is a double root.
]

#proposition[
  A nonzero $f in F[x]$ is not separable if and only if $deg gcd(f, f') >= 1$.
] <prop-sep-gcd>

#proof[
  Let $E$ be the splitting field of $f$; by @rem-recall-fields 6) the gcd may be computed in $E[x]$.

  $(arrow.r.double)$ Let $alpha in E$ be a multiple root. Then $f(x) = (x - alpha)^r h(x)$ with $r >= 2$ and $h in E[x]$, so
  $ f'(x) = r (x - alpha)^(r - 1) h(x) + (x - alpha)^r h'(x). $
  Hence $x - alpha$ is a common divisor of $f$ and $f'$, and $deg gcd(f, f') >= 1$.

  $(arrow.l.double)$ Let $g = gcd(f, f')$ with $deg g >= 1$. Since $g divides f$, $g$ splits in $E$; let $alpha in E$ be a root of $g$. Then $x - alpha$ divides $f$ and $f'$. Write $f(x) = (x - alpha)^r h(x)$ with $r >= 1$ and $h(alpha) != 0$, and suppose $r = 1$. Then $f'(x) = h(x) + (x - alpha) h'(x)$, and $f'(alpha) = 0$ forces $h(alpha) = 0$, a contradiction. So $alpha$ is a multiple root of $f$.
]

#lemma[
  An irreducible $f in F[x]$ is separable if and only if $f' != 0$. In particular, if $"char" F = 0$, every irreducible polynomial is separable.
] <lem-sep-deriv>

#proof[
  Since $f$ is irreducible, $gcd(f, f')$ is $1$ or $f$ up to a unit. If $f' != 0$, then $deg f' < deg f$ and $f divides.not f'$, so the gcd is $1$ and $f$ is separable by @prop-sep-gcd. If $f' = 0$, the gcd is $f$, of degree at least $1$. In characteristic $0$, $f' != 0$ whenever $deg f >= 1$.
]

#theorem[
  Over a finite field every irreducible polynomial is separable.
] <thm-finite-sep>

#proof[
  Let $F$ be finite, $f in F[x]$ irreducible, and suppose that $f$ is not separable. By @lem-sep-deriv, $f' = 0$. Let $"char" F = p$ (@thm-finite-field). Since $(x^p)' = p x^(p - 1) = 0$, the condition $f' = sum_i i a_i x^(i - 1) = 0$ holds exactly when $a_i = 0$ for $p divides.not i$, so
  $ f(x) = a_0 + a_1 x^p + dots.c + a_n (x^p)^n. $
  By @thm-frob-aut with $q = p$, the map $b mapsto b^p$ is surjective on $F$, so $a_i = b_i^p$ with $b_i in F$. The binomial argument of @thm-frobenius holds in every commutative ring of characteristic $p$, in particular in $F[x]$, hence
  $ f(x) = b_0^p + b_1^p x^p + dots.c + b_n^p x^(n p) = (b_0 + b_1 x + dots.c + b_n x^n)^p. $
  As $deg f >= 1$ and $p >= 2$, this contradicts the irreducibility of $f$.
]

#definition(title: [Separable extension])[
  Let $E | F$ be an extension. An element $alpha in E$ is _separable_ over $F$ if it is algebraic over $F$ and its minimal polynomial is separable. The extension is _separable_ if every element of $E$ is separable over $F$.
]

// [p4]
#theorem[
  Let $F subset.eq K subset.eq E$ be fields with $E$ separable over $F$. Then $E$ is separable over $K$, and $K$ is separable over $F$.
] <thm-sep-tower>

#proof[
  1) $K | F$ is separable: every $beta in K$ lies in $E$, and is therefore separable over $F$.

  2) $E | K$ is separable: let $alpha in E$. Then $alpha$ is separable over $F$, in particular algebraic over $F$, hence over $K$. Since $m_(alpha, F) in F[x] subset.eq K[x]$ vanishes at $alpha$, @rem-recall-fields 2) gives $m_(alpha, K) divides m_(alpha, F)$. So every root of $m_(alpha, K)$ in a splitting field of $m_(alpha, F)$ is a root of $m_(alpha, F)$ of at least the same multiplicity. As $m_(alpha, F)$ has only simple roots, so does $m_(alpha, K)$, and $alpha$ is separable over $K$.
]

#example(title: [A non-separable extension])[
  Fix a prime $p$, let $t$ be an indeterminate and $F = FF_p (t)$, the field of rational functions over $FF_p$. Let $E$ be obtained by adjoining to $F$ a root $s$ of $x^p - t$. Then $x^p - t$ is irreducible over $F$, and $E | F$ is not separable: in $E[x]$,
  $ x^p - t = x^p - s^p = (x - s)^p. $
]

#proof(title: [Irreducibility of $x^p - t$])[
  First, $s in.not F$: if $s = g slash h$ with $g, h in FF_p [t]$, $h != 0$, then $g^p = t h^p$, and comparing degrees in $t$ gives $p deg g = 1 + p deg h$, which is impossible. A monic factor of $x^p - t$ in $F[x]$ divides $(x - s)^p$ in $E[x]$, so it equals $(x - s)^k$ with $0 <= k <= p$. Its coefficient of $x^(k - 1)$ is $-k s$, which lies in $F$. For $1 <= k <= p - 1$, $k$ is invertible in $FF_p$, so $s in F$, a contradiction. Hence the only monic factors are $1$ and $x^p - t$.
]

#theorem[
  Let $E | F$ be an extension, $sigma: E -> E$ an $F$-monomorphism, and $f in F[x]$ a polynomial that splits over $E$. If $alpha in E$ is a root of $f$, then so is $sigma(alpha)$. Hence $sigma$ permutes the roots of $f$ in $E$.
] <thm-perm-roots>

#proof[
  Let $f(x) = b_0 + b_1 x + dots.c + b_n x^n in F[x]$ with $f(alpha) = b_0 + b_1 alpha + dots.c + b_n alpha^n = 0$. Then
  $ 0 = sigma(0) = sigma(b_0 + b_1 alpha + dots.c + b_n alpha^n) = sigma(b_0) + sigma(b_1 alpha) + dots.c + sigma(b_n alpha^n) \
    = b_0 + b_1 sigma(alpha) + dots.c + b_n sigma(alpha)^n = f(sigma(alpha)), $
  since $sigma$ is an $F$-monomorphism and fixes the coefficients. So $sigma$ maps the finite set of roots of $f$ in $E$ into itself, and it is injective, hence it permutes this set.
]

== Embeddings and primitive elements

#theorem[
  Let $E | F$ be a finite separable extension with $[E : F] = n$, let $L$ be an algebraically closed field, and let $sigma: F -> L$ be an embedding. Then $sigma$ has exactly $n$ extensions to embeddings $E -> L$. In particular this holds for $L = overline(F)$.
] <thm-embed-count>

#proof[
  We proceed by induction on $n$. For $n = 1$, $E = F$ and $sigma$ is its own unique extension.

  Let $n > 1$, choose $alpha in E without F$, and let $r = deg m_(alpha, F) > 1$. In the tower $F subset.eq F(alpha) subset.eq E$,
  $ n = [E : F] = [E : F(alpha)] [F(alpha) : F] = n / r dot r. $
  // [p5]
  Let $g = sigma(m_(alpha, F)) in sigma(F)[x]$ be the polynomial obtained by applying $sigma$ to the coefficients. Since $sigma: F -> sigma(F)$ is an isomorphism, it induces a ring isomorphism $F[x] -> sigma(F)[x]$ compatible with derivatives and gcds, so $g$ is irreducible and $deg gcd(g, g') = deg gcd(m_(alpha, F), m'_(alpha, F))$, which is $0$ by @prop-sep-gcd because $alpha$ is separable over $F$. By @prop-sep-gcd, $g$ is separable, so it has exactly $r$ distinct roots in the algebraically closed field $L$.

  For each root $beta in L$ of $g$ define
  $ psi: F(alpha) -> sigma(F)(beta), quad psi(b_0 + b_1 alpha + dots.c + b_k alpha^k) = sigma(b_0) + sigma(b_1) beta + dots.c + sigma(b_k) beta^k. $
  This is well defined and an isomorphism, being the composite $F(alpha) tilde.equiv F[x] slash (m_(alpha, F)) tilde.equiv sigma(F)[x] slash (g) tilde.equiv sigma(F)(beta)$ of the isomorphisms of @rem-recall-fields 3). Its restriction to $F$ is $sigma$. Conversely, every extension $psi$ of $sigma$ to $F(alpha)$ satisfies $g(psi(alpha)) = psi(m_(alpha, F)(alpha)) = 0$, by the computation in the proof of @thm-perm-roots, and is determined by $psi(alpha)$. So $sigma$ has exactly $r$ extensions to $F(alpha)$, one for each root $beta$ of $g$.

  $E | F(alpha)$ is separable by @thm-sep-tower, and $[E : F(alpha)] = n slash r < n$. By the induction hypothesis each of the $r$ embeddings $psi$ has exactly $n slash r$ extensions to $E$. Distinct $psi$ have no common extension, and every extension of $sigma$ to $E$ restricts to some $psi$. Hence $sigma$ has exactly $n / r dot r = n$ extensions.
]

#theorem(title: [Primitive element theorem])[
  If $E | F$ is a finite separable extension, then $E = F(gamma)$ for some $gamma in E$. Such a $gamma$ is called a _primitive element_ of $E | F$.
] <thm-prim-elem>

#proof[
  If $F$ is finite, so is $E$, and a generator $gamma$ of $E^times$ (@thm-finite-field) satisfies $E = F(gamma)$.

  Let $F$ be infinite and $n = [E : F]$. Write $E = F(alpha_1, dots, alpha_k)$, for instance with a basis. By @thm-embed-count applied to the inclusion $F -> overline(F)$, there are exactly $n$ distinct $F$-embeddings $sigma_1, dots, sigma_n: E -> overline(F)$. An $F$-embedding of $E$ is determined by its values on $alpha_1, dots, alpha_k$, so for $i != j$ some $l$ has $sigma_i (alpha_l) != sigma_j (alpha_l)$. Hence
  $ P(c_1, dots, c_k) = product_(i < j) sum_(l = 1)^k c_l (sigma_i (alpha_l) - sigma_j (alpha_l)) in overline(F)[c_1, dots, c_k] $
  is a product of nonzero linear forms, so $P != 0$. By @rem-recall-fields 7) there is $(c_1, dots, c_k) in F^k$ with $P(c_1, dots, c_k) != 0$. Put $gamma = sum_l c_l alpha_l in E$. Then the elements $sigma_i (gamma) = sum_l c_l sigma_i (alpha_l)$ are pairwise distinct, and each is a root of $m_(gamma, F)$ by the computation in the proof of @thm-perm-roots. So $[F(gamma) : F] = deg m_(gamma, F) >= n = [E : F]$, and since $F(gamma) subset.eq E$, $F(gamma) = E$.
]

#remark[
  For a finite field $E$, a generator of $E^times$, called a primitive element of $E$ in @thm-finite-field, is a primitive element of $E | F$ for every subfield $F$. The converse fails: $x^2 + 1$ is irreducible over $FF_3$, so $FF_9 = FF_3 (i)$ with $i^2 = -1$, but $i$ has order $4$ in $FF_9^times$, which has order $8$.
]

== Normal extensions

#definition(title: [Normal extension])[
  An algebraic extension $E | F$ is _normal_ if every irreducible polynomial in $F[x]$ that has at least one root in $E$ splits into linear factors in $E[x]$.
]

#example[
  $QQ(root(3, 2)) | QQ$ is not normal. The polynomial $x^3 - 2$ is irreducible over $QQ$: it has degree $3$ and no rational root, since $z^3 = 2$ would give $3 v_2 (z) = 1$. Its roots are $root(3, 2)$, $epsilon root(3, 2)$, $epsilon^2 root(3, 2)$, where $epsilon = e^(2 pi i slash 3)$ is a primitive third root of unity. The last two are not real, while $QQ(root(3, 2)) subset.eq RR$, so they do not lie in $QQ(root(3, 2))$.

  $QQ(sqrt(2)) | QQ$ is normal; the roots of $x^2 - 2$ are $plus.minus sqrt(2)$. More generally, every extension $E | F$ with $[E : F] = 2$ is normal. If $f in F[x]$ is irreducible with a root $alpha in E$, then $f$ is a scalar multiple of $m_(alpha, F)$ and $deg f = [F(alpha) : F]$ divides $2$. If $deg f = 1$, $f$ is linear. If $deg f = 2$, then $f = c (x - alpha)(x - alpha')$ in $E[x]$, where $x - alpha'$ is the quotient of $f slash c$ by $x - alpha$ in $E[x]$, so $alpha' in E$.
] <ex-normal>

#theorem[
  Let $F subset.eq E subset.eq CC$ be fields with $[E : F]$ finite. Then $E | F$ is normal if and only if every $F$-monomorphism $tau: E -> CC$ is an $F$-automorphism of $E$, that is, $tau(E) = E$.
] <thm-normal-C>

#proof[
  $(arrow.r.double)$ Let $E | F$ be normal and $tau: E -> CC$ an $F$-monomorphism. For $gamma in E$, the irreducible polynomial $m_(gamma, F)$ has the root $gamma in E$, so it splits into linear factors in $E[x]$. By the computation in the proof of @thm-perm-roots, $tau(gamma)$ is a root of $m_(gamma, F)$, hence $tau(gamma) in E$. So $tau(E) subset.eq E$. Since $tau$ is an injective $F$-linear map of the finite-dimensional $F$-space $E$ into itself, it is surjective, and $tau$ is an $F$-automorphism of $E$.

  $(arrow.l.double)$ Let $f in F[x]$ be irreducible with a root $alpha in E$, and let $beta in CC$ be any root of $f$, that is, a conjugate of $alpha$ over $F$. As in the proof of @thm-embed-count, $g(alpha) mapsto g(beta)$ defines an $F$-embedding $psi: F(alpha) -> CC$. Since $"char" F = 0$, $E | F(alpha)$ is separable by @lem-sep-deriv, and $CC$ is algebraically closed, so by @thm-embed-count $psi$ extends to an $F$-monomorphism $tau: E -> CC$, with $tau(alpha) = beta$. By hypothesis $tau(E) = E$, so $beta in E$. Thus every root of $f$ in $CC$ lies in $E$; since $f$ splits into linear factors over $CC$, it splits into linear factors in $E[x]$. Hence $E | F$ is normal.
]
