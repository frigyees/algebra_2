#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 21-261123 · injective and divisible modules, linear representations, group algebra, Maschke's theorem
// HEADINGS section 31 from source ("Intro to representation theory")
// NOTATION
//   injective module written J (the source's script letter clashes with the ideal I)
// DROPPED
//   [p1] sketch of a triangle with symmetry axes next to the S_3 example (decorative)
// CORRECTIONS
//   [p1] divisible module: "divisible by every element of R" -> every nonzero element (only 0 is divisible by 0; Q would not be divisible)
//   [p1] Baer: "I a R" for R not commutative -> left ideal
//   [p2] simple module: M != 0 added
//   [p1] group algebra: G arbitrary -> coefficients zero for all but finitely many g
// GAPS
//   [p2] "irreducible representation" used in the remark but not defined; supplied after the definition of invariant subspace
//   [p2] the multiplication example in QS_3 is announced but not recorded; one product computed
//   [p2] Maschke: existence of a projection V -> W assumed; supplied via extension of a basis (cited)
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] C: Baer's criterion (stated without proof in the source)
//   [p1] A: Q divisible; R commutative for rR = (r) in the lemma; case I = 0 in the PID theorem
//   [p1] A: GL(V) is a group; GL(V) = GL(n, R) via matrices; C_p example checked (rho(g^p) = I)
//   [p1] A: S_3 example: composition right to left; homomorphism property verified on all products
//   [p2] A: RG-module axioms; R-module structure via r |-> r e; rho(g) invertible with inverse rho(g^-1)
//   [p2] A: Maschke: im pi' in W; V = W (+) ker P lemma; reindexing h^-1 g
//   FIGURES diagram redrawn with lib/diagram.typ

// [p1]
#definition(title: [Injective module])[
  Let $R$ be a ring with $1 in R$. An $R$-module $J$ is _injective_ if for every diagram of $R$-modules and $R$-morphisms
  #cd(
    ((0, 2, $J$), (1, 0, $0$), (1, 1, $A$), (1, 2, $B$)),
    (
      (from: (1, 1), to: (0, 2), label: $f$),
      (from: (1, 0), to: (1, 1)),
      (from: (1, 1), to: (1, 2), label: $g$, side: "right"),
      (from: (1, 2), to: (0, 2), label: $h$, side: "right", dashed: true),
    ),
  )
  with exact bottom row, that is, with $g$ injective, there is an $R$-morphism $h: B -> J$ with $f = h compose g$.
] <def-injective>

#theorem(title: [Baer's criterion], cited: true)[
  An $R$-module $J$ is injective if and only if for every left ideal $I$ of $R$, every $R$-morphism $I -> J$ can be extended to an $R$-morphism $R -> J$.
] <thm-baer>

#definition(title: [Divisible module])[
  Let $M$ be an $R$-module. If $m in M$ and $r in R$, we say that $m$ is _divisible by $r$_ if there is $m' in M$ with $m = r m'$. The module $M$ is _divisible_ if every element of $M$ is divisible by every nonzero element of $R$.
]

#example[
  $QQ$ is a divisible $ZZ$-module: if $q in QQ$ and $0 != r in ZZ$, then $q = r (q slash r)$.
]

#lemma[
  If $R$ is an integral domain and $M$ is an injective $R$-module, then $M$ is divisible.
] <lem-inj-div>

#proof[
  Let $m in M$ and $r in R$ with $r != 0$. We need $x in M$ with $m = r x$. Let
  $ f: (r) = r R -> M, quad a r mapsto a m. $
  $f$ is well defined because $R$ is an integral domain: $a r = a' r$ with $r != 0$ implies $a = a'$; and it is an $R$-morphism. Since $M$ is injective and the inclusion $(r) -> R$ is injective, there is $h: R -> M$ with $h|_((r)) = f$. Thus
  $ m = f(r) = h(r) = h(r dot 1) = r h(1). $
  Let $x = h(1)$.
]

#theorem[
  Let $R$ be a principal ideal domain and $M$ an $R$-module. Then $M$ is injective if and only if $M$ is divisible.
]

#proof[
  Suppose that $M$ is divisible. By @thm-baer it is enough to show that for every ideal $I$ of $R$, every $R$-morphism $f: I -> M$ can be extended to $R$. Since $R$ is a principal ideal domain, $I = (a)$ for some $a in R$. If $a = 0$, then $f = 0$ extends to the zero map. Otherwise, since $M$ is divisible, there is $m in M$ with $f(a) = a m$. Let $h: R -> M$, $r mapsto r m$; it is an $R$-morphism. If $r in I$, then $r = s a$ for some $s in R$, and
  $ h(r) = r m = s a m = s f(a) = f(s a) = f(r), $
  so $h$ extends $f$. Hence $M$ is injective.

  Conversely, if $M$ is injective, then $M$ is divisible by @lem-inj-div, since a principal ideal domain is an integral domain.
]

= Introduction to representation theory

Let $G$ be a finite group and $R$ a commutative ring with $1 in R$. For an $R$-module $V$ we denote by $GL(V)$ the set of invertible $R$-morphisms $V -> V$; it is a group under composition. If $V tilde.equiv R^n$ is a free module of rank $n$, then, by representing morphisms by matrices with respect to a basis, $GL(V) tilde.equiv GL(n, R)$, the group of invertible $n times n$ matrices over $R$.

#definition(title: [Linear representation])[
  A _linear representation_ of $G$ over $R$ is a group homomorphism $rho: G -> GL(V)$, where $V$ is an $R$-module.
]

#example[
  For any group $G$ and commutative ring $R$ we can take $V = R$ and $rho(g) = 1$ for all $g in G$, the _trivial representation_.
]

#example[
  Let $G = S_3 tilde.equiv D_3$, with permutations composed from right to left. A representation $rho: S_3 -> GL(2, ZZ)$ is given by
  $ () mapsto mat(1, 0; 0, 1), quad (1 2) mapsto mat(0, 1; 1, 0), quad (1 3) mapsto mat(-1, 0; -1, 1), $
  $ (2 3) mapsto mat(1, -1; 0, -1), quad (1 2 3) mapsto mat(0, -1; 1, -1), quad (1 3 2) mapsto mat(-1, 1; -1, 0). $
  One checks on all $36$ products that $rho(sigma tau) = rho(sigma) rho(tau)$; for instance $rho((1 2)) rho((2 3)) = mat(0, -1; 1, -1) = rho((1 2 3))$, and indeed $(1 2)(2 3) = (1 2 3)$.
]

#example[
  Let $R = FF_p$, $V = R^2$ and $G = C_p = chevron.l g chevron.r$. Then $rho(g^r) = mat(1, 0; r, 1)$ is a representation: it is well defined, since $rho(g^p) = mat(1, 0; p, 1) = mat(1, 0; 0, 1)$ in $FF_p$, and $mat(1, 0; r, 1) mat(1, 0; s, 1) = mat(1, 0; r + s, 1)$.
]

Let $rho: G -> GL(V)$ be a representation, $v in V$ and $g in G$, and write $g v = rho(g)(v) in V$. The rules of multiplication are
$ g (lambda v + mu w) = lambda g v + mu g w, quad (g h) v = g (h v), quad 1 v = v $
for $g, h in G$, $v, w in V$ and $lambda, mu in R$. Thus a representation is a linear action of $G$ on $V$.

#definition(title: [Group algebra])[
  Let $G$ be a group and $R$ a commutative ring with $1 in R$. The _group algebra_ is
  $ R G = R[G] = {sum_(g in G) a_g g : a_g in R, space a_g = 0 "for all but finitely many" g}, $
  with componentwise addition and the multiplication
  $ (sum_(g in G) a_g g)(sum_(h in G) b_h h) = sum_(k in G) (sum_(g h = k) a_g b_h) k. $
]

// [p2]
#example[
  In $QQ S_3$ the identity element is the empty permutation $()$. Elements are, for instance, $(1 2) - (2 3)$ or $4 / 5 (1 2 3) + 6 (1 2) - 1 / 7 (2 3)$. As an example of multiplying two linear combinations, using $(1 2)(2 3) = (1 2 3)$ and $(2 3)(1 2) = (1 3 2)$,
  $ ((1 2) - (2 3))((1 2) + (2 3)) = () + (1 2 3) - (1 3 2) - () = (1 2 3) - (1 3 2). $
]

#theorem[
  A representation of $G$ over $R$ has the structure of a unital $R G$-module. Conversely, every unital $R G$-module provides a representation of $G$ over $R$.
]

#proof[
  Given a representation $rho: G -> GL(V)$, define an action of $R G$ on $V$ by
  $ (sum_g a_g g) v = sum_g a_g rho(g)(v). $
  It is additive in both arguments, since each $rho(g)$ is $R$-linear, and it is associative: for $alpha = sum_g a_g g$ and $beta = sum_h b_h h$,
  $ alpha (beta v) = sum_(g, h) a_g b_h rho(g)(rho(h)(v)) = sum_(g, h) a_g b_h rho(g h)(v) = (alpha beta) v, $
  as $rho$ is a homomorphism. It is unital, since $rho(1) = "id"_V$.

  Given a unital $R G$-module $V$, $V$ is an $R$-module via $r v = (r 1) v$. For $g in G$ the map $rho(g): V -> V$, $v mapsto g v$, is $R$-linear, $rho(g_1) rho(g_2) = rho(g_1 g_2)$ by associativity, and $rho(1) = "id"_V$. Hence $rho(g)$ is an automorphism of $V$ with inverse $rho(g^(-1))$, and $rho: G -> GL(V)$ is a representation.
]

#definition(title: [Simple module])[
  An $R$-module $M$ is _simple_ if $M != 0$ and $M$ has no $R$-submodules other than $0$ and $M$.
]

#definition(title: [Invariant subspace])[
  Let $rho: G -> GL(V)$ be a representation. If $rho(g) w in W$ for all $g in G$ and $w in W$ for a submodule $W$ of $V$, then $W$ is called _stable_ or a _$G$-invariant_ submodule (subspace). The representation is _irreducible_ if $V != 0$ and its only $G$-invariant submodules are $0$ and $V$.
]

#remark[
  The $G$-invariant submodules of $V$ are exactly the $R G$-submodules. Hence the representation $rho$ is irreducible if and only if $V$ is a simple $R G$-module.
]

#lemma[
  Let $V$ be a vector space, $W$ a subspace and $P: V -> V$ a linear map with $im P subset.eq W$ and $P(w) = w$ for every $w in W$. Then $V = W plus.o ker P$.
] <lem-proj-split>

#proof[
  Every $v in V$ is $v = P(v) + (v - P(v))$ with $P(v) in W$ and $P(v - P(v)) = P(v) - P(v) = 0$, since $P(v) in W$. If $w in W inter ker P$, then $w = P(w) = 0$.
]

#theorem(title: [Maschke])[
  Let $V$ be a representation of the finite group $G$ over a field $FF$, and assume that $|G|$ is invertible in $FF$. Let $W$ be an invariant subspace of $V$. Then there exists an invariant subspace $W_1$ of $V$ such that $V = W plus.o W_1$ as representations.
] <thm-maschke>

#proof[
  Consider a projection $pi: V -> W$ of vector spaces, that is, a linear map with $pi(w) = w$ for all $w in W$. It exists: extend a basis of $W$ to a basis of $V$ and send the added basis vectors to $0$. That a basis of $W$ extends to a basis of $V$ is cited, like @thm-vs-basis. Regard $pi$ as a map $V -> V$, and consider
  $ pi' = 1 / (|G|) sum_(g in G) g pi g^(-1): V -> V. $
  $pi'$ is linear, and $im pi' subset.eq W$, since $pi(g^(-1) v) in W$ and $W$ is invariant. For $w in W$, $g^(-1) w in W$, so
  $ pi'(w) = 1 / (|G|) sum_(g in G) g pi(g^(-1) w) = 1 / (|G|) sum_(g in G) g g^(-1) w = 1 / (|G|) (sum_(g in G) 1) w = 1 / (|G|) |G| w = w. $
  By @lem-proj-split, $V = W plus.o ker pi'$.

  $pi'$ is a $G$-morphism: for $h in G$ and $v in V$, substituting $g = h g'$,
  $ pi'(h v) = 1 / (|G|) sum_(g in G) g pi(g^(-1) h v) = 1 / (|G|) sum_(g' in G) h g' pi(g'^(-1) v) = h pi'(v). $
  So if $v in ker pi'$, then $pi'(h v) = h pi'(v) = 0$ and $h v in ker pi'$. Hence $W_1 = ker pi'$ is invariant, and $V = W plus.o W_1$ as representations.
]
