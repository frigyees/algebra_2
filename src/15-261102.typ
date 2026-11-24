#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 15-261102 · submodules, generated submodules, modular law, morphisms, images and preimages, maps between sets
// HEADINGS section 26 coined; subsections "Morphisms" and "Diagram completion" from source ("Morphisms", "Diagram"), "Submodules" coined
// RECALL
//   modules, rings and algebras are used but not defined in the notes; no lecture is missing (the preceding session was the midterm); the Recall block states the definitions
// DROPPED
//   [p2] marginal sketch next to the image/preimage proposition
// CORRECTIONS
//   [p1] submodule criterion stated without N nonempty -> N nonempty
//   [p1] subalgebra criterion: x - y in B, lambda x in B -> also xy in B
//   [p1] "the intersection of all submodules of M is the smallest" -> of all submodules containing S
//   [p1] "We also know that LC subset <S>" -> justified: every submodule containing S contains LC(S)
//   [p2] sets theorem: dangling "(3)" after condition (2) dropped
// NOTATION
//   LC(S) -> span written as the set of linear combinations; f^-> and f^<- kept
// ADDITIONS (A filled in, B supplied proof)
//   [p1] A: recalled definitions of ring, left module, algebra; I nonempty in the intersection proposition
//   [p1] A: proof of the sum proposition (P*(I) = nonempty finite subsets)
//   [p1] A: Z-linearity of additive maps; M^n componentwise
//   [p2] A: proofs of the image/preimage proposition, its corollary and the five properties of morphisms
//   [p2] A: proofs of the three set-theoretic theorems (the surjective cases use the axiom of choice)
//   [p2] FIGURE diagram completion triangle redrawn with lib/diagram.typ

// [p1]
= Modules

== Submodules

#remark(status: "I", title: [Recall])[
  Throughout, $R$ is a ring with identity $1_R$. A _left $R$-module_ is an abelian group $(M, +)$ together with a map $R times M -> M$, $(lambda, x) mapsto lambda x$, such that for all $lambda, mu in R$ and $x, y in M$:
  $ lambda (x + y) = lambda x + lambda y, quad (lambda + mu) x = lambda x + mu x, quad (lambda mu) x = lambda (mu x), quad 1_R x = x. $
  We say _$R$-module_ for left $R$-module. If $R$ is commutative, an _$R$-algebra_ is an $R$-module $A$ with a multiplication making $A$ a ring such that $lambda (x y) = (lambda x) y = x (lambda y)$ for all $lambda in R$ and $x, y in A$. Elementary consequences are $0_R x = 0_M$, $lambda 0_M = 0_M$ and $(-lambda) x = -(lambda x)$.
]

#definition(status: "S", title: [Submodule])[
  Let $M$ be an $R$-module. A _submodule_ $N$ of $M$ is a subgroup of $M$ such that $lambda x in N$ for all $x in N$ and $lambda in R$.
]

#proposition(status: "C")[
  Let $M$ be an $R$-module and $N subset.eq M$. The following are equivalent:
  + $N$ is a submodule of $M$;
  + $N != emptyset$, and $x - y in N$ and $lambda x in N$ for all $x, y in N$ and $lambda in R$;
  + $N != emptyset$, and $lambda x + mu y in N$ for all $x, y in N$ and $lambda, mu in R$.
] <prop-submod-crit>

#proof(status: "S")[
  1) $=>$ 2) is immediate, since $0 in N$. 2) $=>$ 1): $N$ is a subgroup by the subgroup criterion. 2) $=>$ 3): if $x, y in N$ and $lambda, mu in R$, then $lambda x in N$ and $-mu y = (-mu) y in N$, so $lambda x + mu y = lambda x - (-mu y) in N$. 3) $=>$ 2): take $lambda = 1_R$, $mu = -1_R$, then $x - y in N$; take $mu = 0$, then $lambda x in N$.
]

#remark(status: "C")[
  Similarly, if $A$ is an $R$-algebra, a subset $B subset.eq A$ is a _subalgebra_ of $A$ if $B != emptyset$ and $x - y in B$, $lambda x in B$ and $x y in B$ for all $x, y in B$ and $lambda in R$.
]

#example(status: "S")[
  $R$ is an $R$-module with the multiplication of $R$ as action, denoted $attach(R, tl: R)$. By @prop-submod-crit, the submodules of $attach(R, tl: R)$ are exactly the left ideals of $R$.
]

// [p1]
#proposition(status: "S")[
  Let $M$ be an $R$-module and $(M_i)_(i in I)$ a nonempty family of submodules of $M$. Then $inter.big_(i in I) M_i$ is a submodule of $M$.
] <prop-submod-inter>

#proof(status: "S")[
  $inter.big_(i in I) M_i$ is nonempty, since every $M_i$ is a subgroup and contains $0$. If $x, y in inter.big_(i in I) M_i$, then $x, y in M_i$ for every $i in I$, hence $x - y in M_i$ for every $i$, and $x - y in inter.big_(i in I) M_i$. If moreover $lambda in R$, then $lambda x in M_i$ for every $i in I$, hence $lambda x in inter.big_(i in I) M_i$. By @prop-submod-crit the intersection is a submodule.
]

#definition(status: "C", title: [Generated submodule])[
  Let $M$ be an $R$-module and $S subset.eq M$. The intersection of all submodules of $M$ that contain $S$ is a submodule by @prop-submod-inter (the family is nonempty, as it contains $M$). It is the smallest submodule of $M$ containing $S$ with respect to inclusion, and is called the submodule _generated_ by $S$, denoted $chevron.l S chevron.r$.
]

#definition(status: "I", title: [Linear combination])[
  Let $M$ be an $R$-module and $emptyset != S subset.eq M$. A _linear combination_ of elements of $S$ is a finite sum $sum_(k = 1)^n lambda_k s_k$ with $n in NN$, $lambda_k in R$ and $s_k in S$. The set of linear combinations of elements of $S$ is denoted $"LC"(S)$.
]

#proposition(status: "S")[
  Let $M$ be an $R$-module and $S subset.eq M$. Then
  $ chevron.l S chevron.r = cases({0} & "if" S = emptyset, "LC"(S) & "otherwise".) $
] <prop-generated>

#proof(status: "C")[
  If $S = emptyset$, then ${0}$ is a submodule containing $S$, and it is contained in every submodule, so it is the smallest one.

  Let $S != emptyset$. $"LC"(S)$ is nonempty, and for linear combinations $x = sum_k lambda_k s_k$, $y = sum_l mu_l t_l$ and $lambda in R$, both $x - y = sum_k lambda_k s_k + sum_l (-mu_l) t_l$ and $lambda x = sum_k (lambda lambda_k) s_k$ are linear combinations. So $"LC"(S)$ is a submodule by @prop-submod-crit, and $S subset.eq "LC"(S)$, since $s = 1_R s$. As $chevron.l S chevron.r$ is the smallest submodule containing $S$, $chevron.l S chevron.r subset.eq "LC"(S)$. Conversely, every submodule containing $S$ contains each $lambda_k s_k$ and their finite sums, so it contains $"LC"(S)$; in particular $"LC"(S) subset.eq chevron.l S chevron.r$. Hence $chevron.l S chevron.r = "LC"(S)$.
]

#definition(status: "S", title: [Sum of submodules])[
  Let $M$ be an $R$-module and $(M_i)_(i in I)$ a family of submodules of $M$. The smallest submodule of $M$ that contains $M_i$ for every $i in I$, that is, $chevron.l union.big_(i in I) M_i chevron.r$, is the _sum_ of the family, denoted $sum_(i in I) M_i$. For two submodules we write $A + B$.
]

#proposition(status: "S")[
  Let $(M_i)_(i in I)$ be a family of submodules of $M$, and let $P^*(I)$ denote the set of nonempty finite subsets of $I$. Then $sum_(i in I) M_i$ consists of all finite sums $sum_(j in J) m_j$ with $J in P^*(I)$ and $m_j in M_j$ for every $j in J$.
] <prop-sum>

#proof(status: "A")[
  If $I = emptyset$, both sides are ${0}$, reading the empty union as $emptyset$ and the set of sums as ${0}$. Let $I != emptyset$ and let $T$ be the set of the finite sums described. Every such sum is a linear combination of elements of $union.big_i M_i$ with coefficients $1_R$, so $T subset.eq sum_i M_i$ by @prop-generated. Conversely, a linear combination $sum_k lambda_k s_k$ with $s_k in M_(i_k)$ has $lambda_k s_k in M_(i_k)$; collecting the terms with the same index $i_k$ gives a sum of the described form, since each $M_i$ is closed under addition. So $sum_i M_i = "LC"(union.big_i M_i) subset.eq T$.
]

#theorem(status: "S", title: [Modular law])[
  Let $M$ be an $R$-module and $A, B, C$ submodules of $M$ with $C subset.eq A$. Then
  $ A inter (B + C) = (A inter B) + C. $
] <thm-modular>

#proof(status: "S")[
  Since $C subset.eq A$, $A + C = A$. Hence $(A inter B) + C subset.eq A + C = A$ and $(A inter B) + C subset.eq B + C$, so
  $ (A inter B) + C subset.eq (A + C) inter (B + C) = A inter (B + C). $
  Conversely, let $a in A inter (B + C)$. Then $a in A$, and by @prop-sum $a = b + c$ for some $b in B$ and $c in C$. Since $C subset.eq A$, $c in A$, so $b = a - c in A$, and $b in A inter B$. Hence $a = b + c in (A inter B) + C$.
]

== Morphisms

#definition(status: "S", title: [Morphism])[
  Let $M, N$ be $R$-modules. A map $f: M -> N$ is an _$R$-morphism_ if it preserves the operations, that is,
  $ f(x + y) = f(x) + f(y), quad f(lambda x) = lambda f(x) quad "for all" x, y in M, space lambda in R. $
  An injective $R$-morphism is an _$R$-monomorphism_, a surjective one an _$R$-epimorphism_, a bijective one an _$R$-isomorphism_. An $R$-morphism $f: M -> M$ is an _$R$-endomorphism_ of $M$.
]

#example(status: "S")[
  Abelian groups are $ZZ$-modules, with $n x$ the $n$-fold sum. The $ZZ$-morphisms between abelian groups are exactly the group morphisms: a group morphism $f$ satisfies $f(n x) = n f(x)$ for $n >= 0$ by induction, and for $n < 0$ since $f(-x) = -f(x)$.
]

#example(status: "S")[
  Let $M^n = M times dots.c times M$ with componentwise addition and $R$-action. For $1 <= i <= n$, the projection $"pr"_i: M^n -> M$, $(x_1, dots, x_n) mapsto x_i$, is an $R$-epimorphism.
]

// [p2]
#definition(status: "S", title: [Image and preimage])[
  Let $f: M -> N$ be an $R$-morphism. For every submodule $X$ of $M$ put $f^(arrow.r)(X) = {f(x) : x in X}$, and for every submodule $Y$ of $N$ put $f^(arrow.l)(Y) = {x in M : f(x) in Y}$.
]

#theorem(status: "S")[
  Let $f: M -> N$ be an $R$-morphism. For every submodule $X$ of $M$, $f^(arrow.r)(X)$ is a submodule of $N$, and for every submodule $Y$ of $N$, $f^(arrow.l)(Y)$ is a submodule of $M$.
] <thm-img-preimg>

#proof(status: "S")[
  $f^(arrow.r)(X) != emptyset$, since $0 in X$. If $y, z in f^(arrow.r)(X)$, there are $a, b in X$ with $f(a) = y$ and $f(b) = z$. As $X$ is a submodule of $M$, $y - z = f(a) - f(b) = f(a - b) in f^(arrow.r)(X)$, and for $lambda in R$, $lambda y = lambda f(a) = f(lambda a) in f^(arrow.r)(X)$. Hence $f^(arrow.r)(X)$ is a submodule of $N$.

  Since $Y$ is a submodule of $N$, $f(0) = 0 in Y$, so $0 in f^(arrow.l)(Y) != emptyset$. If $a, b in f^(arrow.l)(Y)$, then $f(a), f(b) in Y$, so $f(a - b) = f(a) - f(b) in Y$ and $a - b in f^(arrow.l)(Y)$. For $lambda in R$, $f(lambda a) = lambda f(a) in Y$, so $lambda a in f^(arrow.l)(Y)$. Hence $f^(arrow.l)(Y)$ is a submodule of $M$.
]

#definition(status: "S", title: [Image and kernel])[
  For an $R$-morphism $f: M -> N$, the submodule $f^(arrow.r)(M)$ of $N$ is the _image_ of $f$, denoted $im f$, and the submodule $f^(arrow.l)({0_N})$ of $M$ is the _kernel_ of $f$, denoted $ker f$.
]

#proposition(status: "S")[
  Let $f: M -> N$ be an $R$-morphism, $A$ a submodule of $M$ and $B$ a submodule of $N$. Then:
  + $f^(arrow.r)(A inter f^(arrow.l)(B)) = f^(arrow.r)(A) inter B$;
  + $f^(arrow.l)(B + f^(arrow.r)(A)) = f^(arrow.l)(B) + A$.
] <prop-img-preimg>

#proof(status: "A")[
  1) If $x in A inter f^(arrow.l)(B)$, then $f(x) in f^(arrow.r)(A)$ and $f(x) in B$. Conversely, if $y in f^(arrow.r)(A) inter B$, then $y = f(a)$ with $a in A$, and $f(a) in B$ gives $a in f^(arrow.l)(B)$, so $y in f^(arrow.r)(A inter f^(arrow.l)(B))$.

  2) If $x = u + a$ with $u in f^(arrow.l)(B)$ and $a in A$, then $f(x) = f(u) + f(a) in B + f^(arrow.r)(A)$. Conversely, if $f(x) = b + f(a)$ with $b in B$ and $a in A$, then $f(x - a) = b in B$, so $x - a in f^(arrow.l)(B)$ and $x = (x - a) + a in f^(arrow.l)(B) + A$.
]

#corollary(status: "S")[
  Let $f: M -> N$ be an $R$-morphism, $A$ a submodule of $M$ and $B$ a submodule of $N$. Then
  $ f^(arrow.r)(f^(arrow.l)(B)) = B inter im f, quad f^(arrow.l)(f^(arrow.r)(A)) = A + ker f. $
] <cor-img-preimg>

#proof(status: "A")[
  Apply @prop-img-preimg 1) with $A = M$, and 2) with $B = {0}$.
]

#proposition(status: "S", title: [Properties of morphisms])[
  Let $f: M -> N$ and $g: N -> P$ be maps between $R$-modules.
  + If $f$ and $g$ are $R$-morphisms, then so is $g compose f$.
  + If $f$ and $g$ are $R$-epimorphisms, then so is $g compose f$.
  + If $f$ and $g$ are $R$-monomorphisms, then so is $g compose f$.
  + If $f$ and $g$ are $R$-morphisms and $g compose f$ is an epimorphism, then $g$ is an epimorphism.
  + If $f$ and $g$ are $R$-morphisms and $g compose f$ is a monomorphism, then $f$ is a monomorphism.
] <prop-morph-props>

#proof(status: "A")[
  1) $g(f(x + y)) = g(f(x) + f(y)) = g(f(x)) + g(f(y))$ and $g(f(lambda x)) = g(lambda f(x)) = lambda g(f(x))$. 2) and 3) follow from 1), since compositions of surjections are surjective and compositions of injections are injective. 4) $im(g compose f) subset.eq im g$, so $im g = P$. 5) If $f(x) = f(y)$, then $g(f(x)) = g(f(y))$, so $x = y$.
]

== Diagram completion

Let $A, B, C$ be $R$-modules and $f: A -> B$, $g: A -> C$ $R$-morphisms. The _diagram completion problem_ asks under which conditions there exists an $R$-morphism $h: B -> C$ such that the diagram
#cd(
  ((0, 0, $A$), (0, 1, $B$), (1, 1, $C$)),
  (
    (from: (0, 0), to: (0, 1), label: $f$),
    (from: (0, 0), to: (1, 1), label: $g$, side: "right"),
    (from: (0, 1), to: (1, 1), label: $h$, dashed: true),
  ),
)
commutes, that is, $h compose f = g$. We first treat the problem for sets and maps.

#theorem(status: "S")[
  Let $A, B, C$ be nonempty sets and $f: A -> B$, $g: A -> C$ maps. The following are equivalent:
  + there is a map $h: B -> C$ with $h compose f = g$;
  + for all $x, y in A$, $f(x) = f(y)$ implies $g(x) = g(y)$.
  If $f$ is surjective, such an $h$ is unique.
] <thm-sets-factor-1>

#proof(status: "A")[
  1) $=>$ 2): if $f(x) = f(y)$, then $g(x) = h(f(x)) = h(f(y)) = g(y)$. 2) $=>$ 1): for $b in im f$, choose $x in A$ with $f(x) = b$ and put $h(b) = g(x)$; by 2) this does not depend on the choice of $x$. For $b in.not im f$, let $h(b)$ be a fixed element of $C$, which exists as $C != emptyset$. Then $h(f(x)) = g(x)$ for every $x in A$. If $f$ is surjective, $h$ is determined on $B = im f$ by $h(f(x)) = g(x)$.
]

#theorem(status: "S")[
  Let $A, B, C$ be nonempty sets and $f: B -> A$, $g: C -> A$ maps. The following are equivalent:
  + there is a map $h: C -> B$ with $f compose h = g$;
  + $im g subset.eq im f$.
  If $f$ is injective, such an $h$ is unique.
] <thm-sets-factor-2>

#proof(status: "A")[
  1) $=>$ 2): $g(c) = f(h(c)) in im f$. 2) $=>$ 1): for $c in C$, $g(c) in im f$; choose $h(c) in B$ with $f(h(c)) = g(c)$ (axiom of choice). If $f$ is injective, $h(c)$ is the unique element of $f^(-1)(g(c))$.
]

#corollary(status: "S")[
  Let $A, B$ be nonempty sets and $f: A -> B$. The following are equivalent:
  + $f$ is injective;
  + there is $g: B -> A$ with $g compose f = id_A$;
  + $f$ is _left cancellable_: $f compose h = f compose k$ implies $h = k$ for all maps $h, k: X -> A$ from any set $X$.
] <cor-injective>

#proof(status: "A")[
  1) $<=>$ 2): condition 2) of @thm-sets-factor-1 with $C = A$ and $g = id_A$ reads: $f(x) = f(y)$ implies $x = y$, which is injectivity of $f$. 2) $=>$ 3): $h = g compose f compose h = g compose f compose k = k$. 3) $=>$ 1): if $f(x) = f(y)$, let $X = {*}$, $h(*) = x$, $k(*) = y$; then $f compose h = f compose k$, so $h = k$ and $x = y$.
]

#corollary(status: "S")[
  Let $A, B$ be nonempty sets and $f: A -> B$. The following are equivalent:
  + $f$ is surjective;
  + there is $g: B -> A$ with $f compose g = id_B$;
  + $f$ is _right cancellable_: $h compose f = k compose f$ implies $h = k$ for all maps $h, k: B -> Y$ into any set $Y$.
] <cor-surjective>

#proof(status: "A")[
  1) $=>$ 2): $im id_B = B = im f$, so @thm-sets-factor-2 applies. 2) $=>$ 3): $h = h compose f compose g = k compose f compose g = k$. 3) $=>$ 1): let $Y = {0, 1}$, $h = 1$ constant, and $k(b) = 1$ for $b in im f$, $k(b) = 0$ otherwise. Then $h compose f = k compose f$, so $h = k$, which forces $im f = B$.
]
