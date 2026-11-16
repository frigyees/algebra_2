#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 16-261106 · factorization of module morphisms, commutative diagrams, exact sequences, four lemma
// Scans are tablet screenshots; the proof of four lemma (2) breaks off at the end of p3.
// HEADINGS section 27 coined
// CORRECTIONS
//   [p1] example: "h(n) = h(2n) = 1" -> h(2n) = n; conclusion 2h(1) = 1 unchanged
//   [p1] first theorem, uniqueness: "since g is surjective" -> f
//   [p1] second theorem: "h is an R-monomorphism" (hypothesis) -> f
//   [p2] square example: f' alpha = beta gamma -> beta f
//   [p3] four lemma (1): b' = beta(b) + beta(f(a)) - beta(b' + f(a)) -> beta(b + f(a))
// MISSING
//   [p3] four lemma (2): end of the proof not recorded; completed below
// ADDITIONS (A filled in)
//   [p1] A: example statement; R-morphism facts of 26.x cited; ker h = 0 iff injective
//   [p2] A: exactness at M_i; proof of the mono/epi/iso theorem; 0 -> M and N -> 0 maps named
//   [p2] A: example: exactness checked at each place; quotient groups as Z-modules
//   [p3] A: proof of the kernel theorem; four lemma (2) completed; exactness used named at each step
//   FIGURES all diagrams redrawn with lib/diagram.typ

// [p1]
= Exact sequences

#example[
  There is no $ZZ$-morphism $h: ZZ -> ZZ$ with $h compose (times 2) = id_ZZ$, where $times 2: ZZ -> ZZ$ is $n mapsto 2 n$.
  #cd(
    ((0, 0, $ZZ$), (0, 1, $ZZ$), (1, 0, $ZZ$)),
    (
      (from: (0, 0), to: (0, 1), label: $id_ZZ$),
      (from: (0, 0), to: (1, 0), label: $times 2$, side: "right"),
      (from: (1, 0), to: (0, 1), label: $h$, side: "right", dashed: true),
    ),
  )
]

#solution[
  Such an $h$ would satisfy $h(2 n) = n$ for every $n in ZZ$. For $n = 1$, $2 h(1) = h(2) = 1$, so $h(1) = 1 slash 2 in.not ZZ$. A map of sets with this property exists by @thm-sets-factor-1, since $times 2$ is injective; it is the $ZZ$-linearity that fails.
]

#theorem[
  Let $A, B, C$ be $R$-modules, $f: A -> B$ an $R$-epimorphism and $g: A -> C$ an $R$-morphism.
  #cd(
    ((0, 0, $A$), (0, 1, $C$), (1, 0, $B$)),
    (
      (from: (0, 0), to: (0, 1), label: $g$),
      (from: (0, 0), to: (1, 0), label: $f$, side: "right"),
      (from: (1, 0), to: (0, 1), label: $h$, side: "right", dashed: true),
    ),
  )
  The following are equivalent:
  + there is a unique $R$-morphism $h: B -> C$ with $h compose f = g$;
  + $ker f subset.eq ker g$.
  Moreover, such an $h$ is a monomorphism if and only if $ker f = ker g$.
] <thm-factor-epi>

#proof[
  1) $=>$ 2): if $x in ker f$, then $g(x) = h(f(x)) = h(0) = 0$, so $x in ker g$.

  2) $=>$ 1): let $x, y in A$ with $f(x) = f(y)$. Then $f(x - y) = 0$, so $x - y in ker f subset.eq ker g$, and $g(x) - g(y) = g(x - y) = 0$. By @thm-sets-factor-1 there is a map $h: B -> C$ with $h compose f = g$, and it is unique since $f$ is surjective (@cor-surjective). It is an $R$-morphism: since $f$ is surjective, every element of $B$ is of the form $f(x)$, and
  $ h(f(x) + f(y)) = h(f(x + y)) = g(x + y) = g(x) + g(y) = h(f(x)) + h(f(y)), $
  $ h(lambda f(x)) = h(f(lambda x)) = g(lambda x) = lambda g(x) = lambda h(f(x)). $

  An $R$-morphism is injective if and only if its kernel is ${0}$. Let $h$ be a monomorphism. If $x in ker g$, then $h(f(x)) = g(x) = 0$, so $f(x) in ker h = {0}$ and $x in ker f$; with 2), $ker f = ker g$. Conversely, let $ker f = ker g$ and $b in ker h$. Since $f$ is surjective, $b = f(y)$ for some $y in A$, and $0 = h(b) = h(f(y)) = g(y)$. So $y in ker g = ker f$ and $b = f(y) = 0$. Hence $ker h = {0}$, and $h$ is injective.
]

#theorem[
  Let $A, B, C$ be $R$-modules, $f: B -> A$ an $R$-monomorphism and $g: C -> A$ an $R$-morphism.
  #cd(
    ((0, 1, $C$), (1, 0, $B$), (1, 1, $A$)),
    (
      (from: (0, 1), to: (1, 1), label: $g$),
      (from: (1, 0), to: (1, 1), label: $f$, side: "right"),
      (from: (0, 1), to: (1, 0), label: $h$, side: "right", dashed: true),
    ),
  )
  The following are equivalent:
  + there is a unique $R$-morphism $h: C -> B$ with $g = f compose h$;
  + $im g subset.eq im f$.
  // [p2]
  Moreover, such an $h$ is an epimorphism if and only if $im g = im f$.
] <thm-factor-mono>

#proof[
  1) $=>$ 2): for every $c in C$, $g(c) = f(h(c)) in im f$.

  2) $=>$ 1): by @thm-sets-factor-2 there is a map $h: C -> B$ with $f compose h = g$, and it is unique since $f$ is injective. It is an $R$-morphism: for $c, d in C$ and $lambda in R$,
  $ f(h(c + d)) = g(c + d) = g(c) + g(d) = f(h(c)) + f(h(d)) = f(h(c) + h(d)), $
  $ f(h(lambda c)) = g(lambda c) = lambda g(c) = lambda f(h(c)) = f(lambda h(c)), $
  and $f$ is injective, so $h(c + d) = h(c) + h(d)$ and $h(lambda c) = lambda h(c)$.

  If $h$ is surjective, then for every $b in B$ there is $c in C$ with $b = h(c)$, so $f(b) = f(h(c)) = g(c)$; hence $im f subset.eq im g$, and with 2), $im g = im f$. Conversely, let $im g = im f$ and $b in B$. Then $f(b) = g(c)$ for some $c in C$, so $f(b) = f(h(c))$ and $b = h(c)$, as $f$ is injective. Hence $h$ is surjective.
]

#definition(title: [Commutative diagram])[
  A diagram of sets and maps is _commutative_ if all composite maps from any given departure set to any given arrival set are equal.
]

#example[
  The diagram
  #cd(
    ((0, 0, $A$), (0, 1, $B$), (0, 2, $C$), (1, 0, $A'$), (1, 1, $B'$), (1, 2, $C'$)),
    (
      (from: (0, 0), to: (0, 1), label: $f$),
      (from: (0, 1), to: (0, 2), label: $g$),
      (from: (1, 0), to: (1, 1), label: $f'$, side: "right"),
      (from: (1, 1), to: (1, 2), label: $g'$, side: "right"),
      (from: (0, 0), to: (1, 0), label: $alpha$, side: "right"),
      (from: (0, 1), to: (1, 1), label: $beta$, side: "right"),
      (from: (0, 2), to: (1, 2), label: $gamma$, side: "right"),
    ),
  )
  is commutative if and only if $f' compose alpha = beta compose f$ and $g' compose beta = gamma compose g$. Then also $g' compose f' compose alpha = gamma compose g compose f$.
]

#definition(title: [Exact sequence])[
  A _sequence_ of $R$-modules and $R$-morphisms is a diagram
  $ dots.c ar(#none) M_(i - 1) ar(f_(i - 1)) M_i ar(f_i) M_(i + 1) ar(f_(i + 1)) dots.c $
  It is _exact at $M_i$_ if $im f_(i - 1) = ker f_i$, and _exact_ if it is exact at every $M_i$ that has both an incoming and an outgoing morphism.
]

#theorem[
  Let $f: M -> N$ be an $R$-morphism, and let $0 -> M$ and $N -> 0$ denote the inclusion of the zero module and the zero map, respectively. Then $f$ is
  + a monomorphism if and only if $0 ar(#none) M ar(f) N$ is exact;
  + an epimorphism if and only if $M ar(f) N ar(#none) 0$ is exact;
  + an isomorphism if and only if $0 ar(#none) M ar(f) N ar(#none) 0$ is exact.
] <thm-exact-mono-epi>

#proof[
  1) The image of $0 -> M$ is ${0}$, so exactness at $M$ means $ker f = {0}$, that is, $f$ is injective. 2) The kernel of $N -> 0$ is $N$, so exactness at $N$ means $im f = N$. 3) follows from 1) and 2).
]

#example[
  Let $f: A -> B$ be a morphism of abelian groups. Then
  $ 0 ar(#none) ker f ar(alpha) A ar(beta) A slash ker f ar(#none) 0 quad "and" quad 0 ar(#none) im f ar(#none) B ar(#none) B slash im f ar(#none) 0 $
  are exact, where $alpha$ is the inclusion map and $beta$ the natural epimorphism $a mapsto a + ker f$, and similarly in the second sequence. Indeed, $alpha$ is injective, $beta$ is surjective, and $ker beta = ker f = im alpha$.
]

#definition(title: [Short exact sequence])[
  An exact sequence of the form $0 ar(#none) M' ar(#none) M ar(#none) M'' ar(#none) 0$ is called a _short exact sequence_.
]

// [p3]
#theorem[
  Let
  #cd(
    ((0, 2, $A$), (1, 0, $0$), (1, 1, $X$), (1, 2, $Y$), (1, 3, $Z$)),
    (
      (from: (0, 2), to: (1, 2), label: $alpha$),
      (from: (1, 0), to: (1, 1)),
      (from: (1, 1), to: (1, 2), label: $f$, side: "right"),
      (from: (1, 2), to: (1, 3), label: $g$, side: "right"),
      (from: (0, 2), to: (1, 1), label: $h$, side: "right", dashed: true),
    ),
  )
  be a diagram of $R$-modules and $R$-morphisms in which the row is exact and $g compose alpha = 0$. Then there is a unique $R$-morphism $h: A -> X$ such that the completed diagram commutes, that is, $f compose h = alpha$.
] <thm-lift-exact>

#proof[
  By exactness at $Y$, $im alpha subset.eq ker g = im f$, since $g compose alpha = 0$. By exactness at $X$ and @thm-exact-mono-epi, $f$ is a monomorphism. By @thm-factor-mono there is a unique $R$-morphism $h: A -> X$ with $f compose h = alpha$.
]

#theorem[
  Let $f: M -> N$ be an $R$-morphism and $iota: ker f -> M$ the inclusion map. Then $f compose iota = 0$, and if $P$ is an $R$-module and $g: P -> M$ an $R$-morphism with $f compose g = 0$, then there is a unique $R$-morphism $beta: P -> ker f$ such that the following diagram commutes, that is, $iota compose beta = g$:
  #cd(
    ((0, 1, $P$), (1, 0, $ker f$), (1, 1, $M$), (1, 2, $N$)),
    (
      (from: (0, 1), to: (1, 1), label: $g$),
      (from: (1, 0), to: (1, 1), label: $iota$, side: "right", pad: (22, 15)),
      (from: (1, 1), to: (1, 2), label: $f$, side: "right"),
      (from: (0, 1), to: (1, 0), label: $beta$, side: "right", dashed: true),
    ),
  )
] <thm-kernel-up>

#proof[
  $f(iota(x)) = f(x) = 0$ for $x in ker f$. The row $0 ar(#none) ker f ar(iota) M ar(f) N$ is exact: $iota$ is injective and $im iota = ker f$. Apply @thm-lift-exact with $A = P$ and $alpha = g$.
]

#theorem(title: [Four lemma])[
  Suppose the diagram of $R$-modules and $R$-morphisms
  #cd(
    ((0, 0, $A$), (0, 1, $B$), (0, 2, $C$), (0, 3, $D$), (1, 0, $A'$), (1, 1, $B'$), (1, 2, $C'$), (1, 3, $D'$)),
    (
      (from: (0, 0), to: (0, 1), label: $f$),
      (from: (0, 1), to: (0, 2), label: $g$),
      (from: (0, 2), to: (0, 3), label: $h$),
      (from: (1, 0), to: (1, 1), label: $f'$, side: "right"),
      (from: (1, 1), to: (1, 2), label: $g'$, side: "right"),
      (from: (1, 2), to: (1, 3), label: $h'$, side: "right"),
      (from: (0, 0), to: (1, 0), label: $alpha$, side: "right"),
      (from: (0, 1), to: (1, 1), label: $beta$, side: "right"),
      (from: (0, 2), to: (1, 2), label: $gamma$, side: "right"),
      (from: (0, 3), to: (1, 3), label: $delta$, side: "right"),
    ),
  )
  is commutative with exact rows. Then:
  + if $alpha$ and $gamma$ are epimorphisms and $delta$ is a monomorphism, then $beta$ is an epimorphism;
  + if $alpha$ is an epimorphism and $beta$ and $delta$ are monomorphisms, then $gamma$ is a monomorphism.
] <thm-four-lemma>

#proof[
  We use diagram chasing.

  1) Let $b' in B'$. Since $gamma$ is surjective, there is $c in C$ with $gamma(c) = g'(b')$. By commutativity and exactness at $C'$,
  $ delta(h(c)) = h'(gamma(c)) = h'(g'(b')) = 0. $
  So $h(c) in ker delta = {0}$, as $delta$ is injective. Hence $c in ker h = im g$ by exactness at $C$, and $c = g(b)$ for some $b in B$. By commutativity of the middle square,
  $ g'(b') = gamma(c) = gamma(g(b)) = g'(beta(b)), $
  so $g'(b' - beta(b)) = 0$ and $b' - beta(b) in ker g' = im f'$ by exactness at $B'$. So $b' - beta(b) = f'(a')$ for some $a' in A'$. Since $alpha$ is surjective, $a' = alpha(a)$ for some $a in A$, and by commutativity of the left square
  $ b' - beta(b) = f'(alpha(a)) = beta(f(a)), quad "so" quad b' = beta(b) + beta(f(a)) = beta(b + f(a)) in im beta. $
  Hence $beta$ is surjective.

  2) Let $c in ker gamma$. Then $delta(h(c)) = h'(gamma(c)) = h'(0) = 0$, so $h(c) in ker delta = {0}$ and $h(c) = 0$. Hence $c in ker h = im g$, and $c = g(b)$ for some $b in B$, with
  $ 0 = gamma(c) = gamma(g(b)) = g'(beta(b)). $
  So $beta(b) in ker g' = im f'$, and $beta(b) = f'(a')$ for some $a' in A'$. Since $alpha$ is surjective, $a' = alpha(a)$ for some $a in A$, and $beta(b) = f'(alpha(a)) = beta(f(a))$. As $beta$ is injective, $b = f(a)$, so $c = g(f(a)) = 0$ by exactness at $B$. Hence $ker gamma = {0}$, and $gamma$ is injective.
]
