#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 20-261120 · tensor examples, right exactness of the tensor product, projective modules (translated from Hungarian)
// HEADINGS subsection 29.4 from source ("Tenzorszorzat es egzaktsag"); section 30 coined
// NOTATION (normalized)
//   Ker, Im -> ker, im; "pl." examples -> Example blocks; R-mod. -> R-module; maps of the splitting proof renamed (f: F -> P -> p)
// DROPPED
//   [p1] first line "Z (x)_Z Q = {0}": false (Example 29.26: Z (x) Q = Q); no context on the page
//   [p2] crossed-out first attempt of the Q (x) Q computation
// CORRECTIONS
//   [p2] im(1 (x) f) in ker(1 (x) g): (1 (x) f) o (1 (x) g) = 1 (x) (fg) -> (1 (x) g) o (1 (x) f) = 1 (x) (g o f)
//   [p1] Z/5Z (x) Z/7Z: conclusion "= 0" missing; side computation 1 = 3*5 - 2*7 kept as the source's alternative
// ADDITIONS (A filled in)
//   [p1] A: torsion of Q/Z made explicit; y/u read in Q/Z
//   [p2] A: Q (x) Q: additivity of x |-> x (x) 1 and why beta' is bijective
//   [p2-p3] A: pi exists by Lemma 28.7; reduction "pi injective => exact"; psi defined on all of M x N'' (g surjective); bilinearity of psi checked
//   [p3] A: projective definition: exact bottom row means g surjective
//   [p4] A: free => projective: h well defined since X is a basis; choice of the a_x
//   [p4] A: 1 => 2 splitting via the short five lemma (the source asserts B = A (+) P from the section h)
//   [p4] A: 2 => 3: P is a quotient of a free module, proved via Proposition 29.15
//   [p5] A: 3 => 1: inclusion i and projection pi made explicit
//   FIGURES diagrams redrawn with lib/diagram.typ

// [p1]
#example[
  Show that $QQ slash ZZ times.o_ZZ QQ slash ZZ = {0}$.
]

#solution[
  Let $x in QQ slash ZZ$. Then there is $u in ZZ$, $u > 0$, with $u x = 0$: if $x = [a slash b]$ with $b > 0$, take $u = b$. Let $y = [q] in QQ slash ZZ$ be arbitrary and put $y slash u = [q slash u]$, so that $u (y slash u) = y$. Then
  $ x times.o y = x times.o (u dot y / u) = u (x times.o y / u) = (u x) times.o y / u = 0 times.o y / u = 0. $
  Since the elements $x times.o y$ generate the tensor product (@prop-tensor-rules), $QQ slash ZZ times.o_ZZ QQ slash ZZ = {0}$.
]

#example[
  Show that $ZZ slash 5 ZZ times.o_ZZ ZZ slash 7 ZZ = {0}$.
]

#solution[
  Let $m in ZZ slash 5 ZZ$ and $u in ZZ slash 7 ZZ$. Then
  $ m times.o 5 u = 5 (m times.o u) = (5 m) times.o u = 0 times.o u = 0, $
  $ 2 m times.o u = 7 m times.o u = 7 (m times.o u) = m times.o 7 u = 0, $
  using $2 m = 7 m$ in $ZZ slash 5 ZZ$. Hence
  $ 0 = 5 m times.o u - 2 (2 m times.o u) = 5 m times.o u - (4 m) times.o u = m times.o u. $
  Equivalently, $1 = 3 dot 5 - 2 dot 7$ gives $m times.o u = 3 (5 m times.o u) - 2 (m times.o 7 u) = 0$. So all generators vanish, and $ZZ slash 5 ZZ times.o ZZ slash 7 ZZ = {0}$.
]

#example[
  Determine $QQ times.o_ZZ QQ$.
]

#solution[
  Let $x in QQ$ and $a slash b in QQ$ with $a, b in ZZ$, $b != 0$. Then
  $ x times.o a / b = (x / b dot b) times.o a / b = b (x / b times.o a / b) = x / b times.o (b dot a / b) = x / b times.o a = x / b times.o a dot 1 = (a dot x / b) times.o 1 = (a x) / b times.o 1. $
  // [p2]
  So every generator has the form $z times.o 1$ with $z in QQ$, and if $u_i in ZZ$ and $x_i in QQ$, then
  $ sum_i u_i (x_i times.o 1) = (sum_i u_i x_i) times.o 1. $
  Hence $QQ times.o QQ = {x times.o 1 : x in QQ}$.

  The map $beta: QQ times QQ -> QQ$, $beta(x, y) = x y$, is $ZZ$-bilinear, so by @thm-tensor-univ there is a unique $ZZ$-morphism $beta': QQ times.o_ZZ QQ -> QQ$ with $beta'(x times.o y) = x y$. Then $beta'(x times.o 1) = x$. As every element of $QQ times.o QQ$ is $x times.o 1$ for some $x$, $beta'$ is injective ($beta'(x times.o 1) = 0$ forces $x = 0$) and surjective. Hence $QQ times.o_ZZ QQ tilde.equiv QQ$.
]

== Tensor product and exactness

#remark(title: [Recall])[
  Let $M$ be an $R$-module and $N ar(f) N' ar(g) N''$ $R$-morphisms. Tensoring with $M$ gives
  $ M times.o N ar(1_M times.o f) M times.o N' ar(1_M times.o g) M times.o N'', $
  and $(1_M times.o g) compose (1_M times.o f) = 1_M times.o (g compose f)$ by @cor-tensor-comp. Moreover $1_M times.o 1_N = 1_(M times.o N)$.
]

#theorem(title: [Right exactness of the tensor product])[
  Let $N', N, N''$ be $R$-modules. If
  $ N' ar(f) N ar(g) N'' ar(#none) 0 $
  is exact, then
  $ M times.o N' ar(1_M times.o f) M times.o N ar(1_M times.o g) M times.o N'' ar(#none) 0 $
  is exact for every $R$-module $M$.
] <thm-right-exact>

#proof[
  We have to show that $1_M times.o g$ is surjective and that $im(1_M times.o f) = ker(1_M times.o g)$.

  _$1_M times.o g$ is surjective._ Its image is a submodule, so it suffices to show that every generator $m times.o u''$ of $M times.o N''$ has a preimage. Since $g$ is surjective, there is $u in N$ with $g(u) = u''$. Then $(1_M times.o g)(m times.o u) = 1_M (m) times.o g(u) = m times.o u''$.

  _$im(1_M times.o f) subset.eq ker(1_M times.o g)$._ By exactness $im f = ker g$, so $g compose f = 0$, and
  $ (1_M times.o g) compose (1_M times.o f) = 1_M times.o (g compose f) = 1_M times.o 0 = 0. $

  _$ker(1_M times.o g) subset.eq im(1_M times.o f)$._ Write $I = im(1_M times.o f)$ and $K = ker(1_M times.o g)$. Since $I subset.eq K$, @lem-induced applied to $1_(M times.o N)$ gives an $R$-morphism $(M times.o N) slash I -> (M times.o N) slash K$, and composing it with the isomorphism $(M times.o N) slash K tilde.equiv M times.o N''$ of @thm-first-iso (as $1_M times.o g$ is surjective) gives the $R$-morphism
  $ pi: (M times.o N) slash I -> M times.o N'', quad pi(x times.o y + I) = x times.o g(y). $
  Its kernel is $K slash I$. So it suffices to show that $pi$ is injective, for then $K slash I = 0$ and $K = I$; we construct a left inverse.

  // [p3]
  Define $psi: M times N'' -> (M times.o N) slash I$ by $psi(x, y'') = x times.o y + I$, where $y in N$ is any element with $g(y) = y''$; such $y$ exists since $g$ is surjective. $psi$ is well defined: if $g(y_1) = g(y_2) = y''$, then $g(y_1 - y_2) = 0$, so $y_1 - y_2 in ker g = im f$, and there is $y' in N'$ with $f(y') = y_1 - y_2$. Then
  $ x times.o y_1 - x times.o y_2 = x times.o (y_1 - y_2) = x times.o f(y') = (1_M times.o f)(x times.o y') in I, $
  so $x times.o y_1 + I = x times.o y_2 + I$. $psi$ is $R$-bilinear: if $g(y_1) = y''_1$ and $g(y_2) = y''_2$, then $g(y_1 + y_2) = y''_1 + y''_2$, and $psi(x, y''_1 + y''_2) = x times.o (y_1 + y_2) + I = psi(x, y''_1) + psi(x, y''_2)$; the other identities are checked in the same way. By @thm-tensor-univ there is a unique $R$-morphism $psi'$ such that the diagram
  #cd(
    ((0, 0, $M times N''$), (0, 1, $M times.o N''$), (1, 1, $(M times.o N) slash I$)),
    (
      (from: (0, 0), to: (0, 1), label: $phi$, pad: (26, 28)),
      (from: (0, 0), to: (1, 1), label: $psi$, side: "right", pad: (26, 40)),
      (from: (0, 1), to: (1, 1), label: $psi'$),
    ),
    dx: 3cm,
  )
  commutes, where $phi(x, y'') = x times.o y''$. So $psi'(x times.o y'') = x times.o y + I$ whenever $g(y) = y''$.

  We claim $psi' compose pi = 1_((M times.o N) slash I)$ and $pi compose psi' = 1_(M times.o N'')$; the first already shows that $pi$ is injective. It suffices to check this on generators:
  $ (psi' compose pi)(x times.o y + I) = psi'(x times.o g(y)) = x times.o y + I, $
  $ (pi compose psi')(x times.o y'') = pi(x times.o y + I) = x times.o g(y) = x times.o y'', $
  where $g(y) = y''$. Hence $pi$ is an isomorphism, $K = I$, and the sequence is exact.
]

= Projective and injective modules

#definition(title: [Projective module])[
  An $R$-module $P$ is _projective_ if for every diagram of $R$-modules and $R$-morphisms
  #cd(
    ((0, 1, $P$), (1, 0, $A$), (1, 1, $B$), (1, 2, $0$)),
    (
      (from: (0, 1), to: (1, 1), label: $f$),
      (from: (1, 0), to: (1, 1), label: $g$, side: "right"),
      (from: (1, 1), to: (1, 2)),
      (from: (0, 1), to: (1, 0), label: $h$, side: "right", dashed: true),
    ),
  )
  with exact bottom row, that is, with $g$ surjective, there is an $R$-morphism $h: P -> A$ with $f = g compose h$, that is, the completed diagram commutes.
] <def-projective>

// [p4]
#proposition[
  Every free $R$-module is projective.
] <prop-free-proj>

#proof[
  Let $F$ be free with basis $X$, and let $f: F -> B$ and $g: A -> B$ be $R$-morphisms with $g$ surjective. For $x in X$, since $g$ is surjective, there is $a_x in A$ with $g(a_x) = f(x)$; choose one for each $x$. Let $h': X -> A$, $h'(x) = a_x$. Since $X$ is a basis, every element of $F$ is uniquely of the form $sum_i c_i x_i$ with $c_i in R$ and distinct $x_i in X$, so
  $ h: F -> A, quad h(sum_i c_i x_i) = sum_i c_i h'(x_i), $
  is a well-defined $R$-morphism extending $h'$. For $x in X$, $f(x) = g(a_x) = g(h(x))$. So the $R$-morphisms $f$ and $g compose h$ agree on the basis $X$, hence on $F$.
]

#definition(title: [Split exact sequence])[
  A short exact sequence $0 ar(#none) A ar(f) B ar(g) C ar(#none) 0$ _splits_ if $B tilde.equiv A plus.o C$.
]

#lemma[
  Every $R$-module $P$ is the image of a free $R$-module under an $R$-morphism.
] <lem-free-cover>

#proof[
  Let $F_P$ be the free module on the set $P$ (@def-free-on-set). By @prop-free-univ there is an $R$-morphism $p: F_P -> P$ with $p(e_x) = x$ for every $x in P$, and it is surjective.
]

#theorem[
  For an $R$-module $P$ the following are equivalent:
  + $P$ is projective;
  + every exact sequence $0 ar(#none) A ar(f) B ar(g) P ar(#none) 0$ splits, that is, $B tilde.equiv A plus.o P$;
  + $F tilde.equiv K plus.o P$ for some free $R$-module $F$ and some $R$-module $K$.
] <thm-projective>

#proof[
  1) $=>$ 2): apply the definition to $f = "id"_P$ and the surjection $g$:
  #cd(
    ((0, 1, $P$), (1, 0, $B$), (1, 1, $P$), (1, 2, $0$)),
    (
      (from: (0, 1), to: (1, 1), label: $"id"_P$),
      (from: (1, 0), to: (1, 1), label: $g$, side: "right"),
      (from: (1, 1), to: (1, 2)),
      (from: (0, 1), to: (1, 0), label: $h$, side: "right", dashed: true),
    ),
  )
  There is $h: P -> B$ with $g compose h = "id"_P$. Let $theta: A plus.o P -> B$, $theta(a, p) = f(a) + h(p)$, an $R$-morphism. In the diagram
  #cd(
    ((0, 0, $0$), (0, 1, $A$), (0, 2, $A plus.o P$), (0, 3, $P$), (0, 4, $0$), (1, 0, $0$), (1, 1, $A$), (1, 2, $B$), (1, 3, $P$), (1, 4, $0$)),
    (
      (from: (0, 0), to: (0, 1)), (from: (0, 1), to: (0, 2), pad: (14, 22)), (from: (0, 2), to: (0, 3), pad: (22, 14)), (from: (0, 3), to: (0, 4)),
      (from: (1, 0), to: (1, 1)), (from: (1, 1), to: (1, 2), label: $f$, side: "right"), (from: (1, 2), to: (1, 3), label: $g$, side: "right"), (from: (1, 3), to: (1, 4)),
      (from: (0, 1), to: (1, 1), label: $"id"_A$, side: "right"),
      (from: (0, 2), to: (1, 2), label: $theta$, side: "right"),
      (from: (0, 3), to: (1, 3), label: $"id"_P$, side: "right"),
    ),
    dx: 1.8cm,
  )
  the top row consists of $a mapsto (a, 0)$ and $(a, p) mapsto p$ and is exact. The squares commute: $theta(a, 0) = f(a)$, and $g(theta(a, p)) = g(f(a)) + g(h(p)) = 0 + p$. By @cor-short-five, $theta$ is an isomorphism, so $B tilde.equiv A plus.o P$.

  2) $=>$ 3): by @lem-free-cover there are a free module $F$ and a surjective $R$-morphism $p: F -> P$. The sequence
  $ 0 ar(#none) ker p ar(#none) F ar(p) P ar(#none) 0 $
  is exact, so by 2), $F tilde.equiv ker p plus.o P$, and $K = ker p$ works.

  // [p5]
  3) $=>$ 1): identify $F$ with $K plus.o P$, and let $i: P -> F$, $p mapsto (0, p)$, and $pi: F -> P$, $(k, p) mapsto p$, so $pi compose i = "id"_P$. Let $f: P -> B$ and $g: A -> B$ be $R$-morphisms with $g$ surjective. $F$ is free, hence projective by @prop-free-proj, so there is $h': F -> A$ with $g compose h' = f compose pi$:
  #cd(
    ((0, 1, $F$), (1, 1, $P$), (2, 0, $A$), (2, 1, $B$), (2, 2, $0$)),
    (
      (from: (0, 1), to: (1, 1), label: $pi$),
      (from: (1, 1), to: (2, 1), label: $f$),
      (from: (2, 0), to: (2, 1), label: $g$, side: "right"),
      (from: (2, 1), to: (2, 2)),
      (from: (0, 1), to: (2, 0), label: $h'$, side: "right", dashed: true, pad: (12, 14)),
      (from: (1, 1), to: (2, 0), label: $h$, dashed: true, pad: (12, 14)),
    ),
  )
  Let $h = h' compose i$. Then $g compose h = g compose h' compose i = f compose pi compose i = f compose "id"_P = f$.
]
