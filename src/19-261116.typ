#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 19-261116 · free module on a set, functoriality and properties of the tensor product
// HEADINGS continues subsection 29.2; subsection 29.3 coined
// DROPPED
//   [p1] remark (1), (2) on tensor rules and generators: repeats 18-261113 p4 (Proposition 29.6)
//   [p1] example Z (x) Z/2Z vs 2Z (x) Z/2Z: repeats 18-261113 p4
//   [p1] definitions of basis, linear independence, free, rank: repeat 18-261113 p4 (the more detailed wording was used there)
// CORRECTIONS
//   [p1] free module proof: "then f in M" -> f in F_S
//   [p1] commutativity proof: f: M x N -> M (x) N, (x, y) |-> y (x) x -> codomain N (x) M
//   [p2] f (x) g theorem: phi: M x N -> M' x N' -> M' (x) N'
//   [p2] composition corollary: g: N -> N -> N -> N'; (f (x) g)(f' (x) g') = (f'f) (x) (g'g) -> (f' (x) g') o (f (x) g) = (f' o f) (x) (g' o g), which is what the proof computes
//   [p2] R (x) M = M proof: "f is surjective/injective" -> f'
// GAPS
//   [p2] direct sum used without definition; supplied
//   [p2] associativity and distributivity stated without proof; supplied (B)
//   [p2] example Z (x) Z/3Z only shows one generator is 0; completed. "Determine Z (x)_Z Q" left open in the source; solved
// ADDITIONS (A filled in, B supplied proof)
//   [p1] A: e_s well defined in F_S; spanning and independence of {e_s} written out; phi_g is an R-morphism
//   [p1-p2] A: bilinearity of (x, y) |-> y (x) x checked; h' o f' = id via uniqueness in Theorem 29.4
//   [p2] B: associativity via fixing z; distributivity via the two universal maps
//   [p2] A: R (x) M = M: injectivity argument made explicit
//   FIGURES diagrams redrawn with lib/diagram.typ

// [p1]
#definition(status: "S", title: [Free module on a set])[
  Let $S$ be a set. The _free $R$-module on $S$_ is
  $ F_S = {f: S -> R : f(s) = 0 "for all but finitely many" s in S}, $
  with pointwise addition and $R$-action. For $s in S$, let $e_s in F_S$ be defined by $e_s (s) = 1$ and $e_s (t) = 0$ for $t != s$.
] <def-free-on-set>

#proposition(status: "S")[
  ${e_s : s in S}$ is a basis of $F_S$; in particular $F_S$ is free.
]

#proof(status: "S")[
  Let $f in F_S$ and let $s_1, dots, s_n$ be the elements of $S$ with $f(s_i) != 0$. Then $f = f(s_1) e_(s_1) + dots.c + f(s_n) e_(s_n)$, since both sides take the value $f(s_i)$ at $s_i$ and $0$ elsewhere; so the $e_s$ generate $F_S$. If $s_1, dots, s_n in S$ are distinct and $r_1, dots, r_n in R$, then $sum_i r_i e_(s_i)$ takes the value $r_i$ at $s_i$; so $sum_i r_i e_(s_i) = 0$ implies $r_i = 0$ for every $i$, and ${e_s}$ is linearly independent.
]

#proposition(status: "S", title: [Universal property of free modules])[
  Let $F_S$ be the free module on a set $S$. For every $R$-module $N$ and every map $g: S -> N$ there is a unique $R$-morphism $phi_g: F_S -> N$ such that $phi_g (e_s) = g(s)$ for all $s in S$.
] <prop-free-univ>

#proof(status: "S+")[
  Define $phi_g (f) = sum_(s in S) f(s) g(s)$; the sum is finite, since $f(s) = 0$ for all but finitely many $s$. Then $phi_g (f + f') = sum_s (f(s) + f'(s)) g(s) = phi_g (f) + phi_g (f')$ and $phi_g (a f) = a phi_g (f)$, so $phi_g$ is an $R$-morphism, and $phi_g (e_s) = g(s)$. If $psi_g: F_S -> N$ is another $R$-morphism with $psi_g (e_s) = g(s)$ for all $s in S$, then for $f = sum_s f(s) e_s$,
  $ psi_g (f) = sum_s f(s) psi_g (e_s) = sum_s f(s) g(s) = phi_g (f), $
  so $phi_g$ is unique.
]

== Properties of the tensor product

#theorem(status: "S")[
  The tensor product is commutative: if $M, N$ are $R$-modules, then $M times.o_R N tilde.equiv N times.o_R M$.
] <thm-tensor-comm>

#proof(status: "C")[
  Let $g: M times N -> M times.o N$, $g(x, y) = x times.o y$, and $g': N times M -> N times.o M$, $g'(y, x) = y times.o x$, be the bilinear maps of @thm-tensor-univ. The map $f: M times N -> N times.o M$, $(x, y) mapsto y times.o x$, is $R$-bilinear by @prop-tensor-rules. By @thm-tensor-univ there is an $R$-morphism $f': M times.o N -> N times.o M$ such that the diagram
  #cd(
    ((0, 0, $M times N$), (0, 1, $M times.o N$), (1, 1, $N times.o M$)),
    (
      (from: (0, 0), to: (0, 1), label: $g$, pad: (24, 26)),
      (from: (0, 0), to: (1, 1), label: $f$, side: "right", pad: (24, 26)),
      (from: (0, 1), to: (1, 1), label: $f'$),
    ),
    dx: 2.6cm,
  )
  commutes. So for $(x, y) in M times N$, $f'(x times.o y) = f'(g(x, y)) = f(x, y) = y times.o x$.

  Similarly, $h: N times M -> M times.o N$, $h(y, x) = x times.o y$, is bilinear, and there is an $R$-morphism $h': N times.o M -> M times.o N$ with $h' compose g' = h$, that is, $h'(y times.o x) = x times.o y$. Then $(h' compose f')(x times.o y) = x times.o y$, so $h' compose f'$ and $"id"_(M times.o N)$ agree on the generators $x times.o y$, and $h' compose f' = "id"_(M times.o N)$. Similarly $f' compose h' = "id"_(N times.o M)$. Hence $f'$ and $h'$ are mutually inverse isomorphisms, and $M times.o N tilde.equiv N times.o M$.
]

// [p2]
#theorem(status: "S")[
  The tensor product is associative: if $M, N, P$ are $R$-modules, then $(M times.o N) times.o P tilde.equiv M times.o (N times.o P)$, with $(x times.o y) times.o z mapsto x times.o (y times.o z)$.
] <thm-tensor-assoc>

#proof(status: "A")[
  Fix $z in P$. The map $M times N -> M times.o (N times.o P)$, $(x, y) mapsto x times.o (y times.o z)$, is bilinear by @prop-tensor-rules, so by @thm-tensor-univ there is an $R$-morphism $phi_z: M times.o N -> M times.o (N times.o P)$ with $phi_z (x times.o y) = x times.o (y times.o z)$. The map $(M times.o N) times P -> M times.o (N times.o P)$, $(u, z) mapsto phi_z (u)$, is bilinear: it is linear in $u$ since each $phi_z$ is, and $phi_(z + z')$, $phi_z + phi_(z')$ agree on the generators $x times.o y$, as do $phi_(a z)$ and $a phi_z$. So there is an $R$-morphism $Phi: (M times.o N) times.o P -> M times.o (N times.o P)$ with $Phi((x times.o y) times.o z) = x times.o (y times.o z)$. In the same way there is an $R$-morphism $Psi$ in the opposite direction with $Psi(x times.o (y times.o z)) = (x times.o y) times.o z$. The composites $Psi compose Phi$ and $Phi compose Psi$ fix the elements $(x times.o y) times.o z$, respectively $x times.o (y times.o z)$, which generate the two modules by @prop-tensor-rules 2), applied twice. Hence they are the identities.
]

#theorem(status: "S")[
  Let $f: M -> M'$ and $g: N -> N'$ be $R$-morphisms. Then there is a unique $R$-morphism $f times.o g: M times.o N -> M' times.o N'$ such that $(f times.o g)(x times.o y) = f(x) times.o g(y)$ for all $(x, y) in M times N$.
] <thm-tensor-maps>

#proof(status: "C")[
  Define $phi: M times N -> M' times.o N'$, $(x, y) mapsto f(x) times.o g(y)$. Since $f, g$ are $R$-morphisms, $phi$ is $R$-bilinear by @prop-tensor-rules. By @thm-tensor-univ there is a unique $R$-morphism $phi' = f times.o g: M times.o N -> M' times.o N'$ such that the diagram
  #cd(
    ((0, 0, $M times N$), (0, 1, $M times.o N$), (1, 1, $M' times.o N'$)),
    (
      (from: (0, 0), to: (0, 1), label: $psi$, pad: (24, 26)),
      (from: (0, 0), to: (1, 1), label: $phi$, side: "right", pad: (24, 28)),
      (from: (0, 1), to: (1, 1), label: $phi'$),
    ),
    dx: 2.6cm,
  )
  commutes, where $psi(x, y) = x times.o y$. Then
  $ f(x) times.o g(y) = phi(x, y) = (phi' compose psi)(x, y) = phi'(x times.o y) = (f times.o g)(x times.o y). $
]

#corollary(status: "C")[
  Let $f: M -> M'$, $f': M' -> M''$, $g: N -> N'$ and $g': N' -> N''$ be $R$-morphisms. Then
  $ (f' times.o g') compose (f times.o g) = (f' compose f) times.o (g' compose g). $
] <cor-tensor-comp>

#proof(status: "S")[
  By @thm-tensor-maps, $f times.o g: M times.o N -> M' times.o N'$ and $f' times.o g': M' times.o N' -> M'' times.o N''$, so both sides are $R$-morphisms $M times.o N -> M'' times.o N''$. It suffices to show that they agree on the generators $x times.o y$:
  $ (f' times.o g')((f times.o g)(x times.o y)) = (f' times.o g')(f(x) times.o g(y)) = f'(f(x)) times.o g'(g(y)), $
  $ ((f' compose f) times.o (g' compose g))(x times.o y) = (f' compose f)(x) times.o (g' compose g)(y) = f'(f(x)) times.o g'(g(y)). $
]

#corollary(status: "S")[
  If $1_M: M -> M$ and $1_N: N -> N$ are the identity maps, then $1_M times.o 1_N = 1_(M times.o N)$.
]

#proof(status: "A")[
  Both are $R$-morphisms sending $x times.o y$ to $x times.o y$, and these elements generate $M times.o N$.
]

#corollary(status: "S")[
  If $f: M -> M'$ and $g: N -> N'$ are $R$-isomorphisms, then so is $f times.o g: M times.o N -> M' times.o N'$.
] <cor-tensor-iso>

#proof(status: "S")[
  Let $f^(-1)$ and $g^(-1)$ be the inverses. By @cor-tensor-comp and the previous corollary,
  $ (f^(-1) times.o g^(-1)) compose (f times.o g) = (f^(-1) compose f) times.o (g^(-1) compose g) = 1_M times.o 1_N = 1_(M times.o N), $
  and similarly $(f times.o g) compose (f^(-1) times.o g^(-1)) = 1_(M' times.o N')$.
]

#definition(status: "I", title: [Direct sum])[
  The _direct sum_ $M plus.o N$ of $R$-modules $M$ and $N$ is the set $M times N$ with componentwise addition and $R$-action.
]

#theorem(status: "S")[
  Let $M, N, P$ be $R$-modules. Then $(M plus.o N) times.o P tilde.equiv (M times.o P) plus.o (N times.o P)$, with $(x, y) times.o z mapsto (x times.o z, y times.o z)$.
] <thm-tensor-distr>

#proof(status: "A")[
  The map $(M plus.o N) times P -> (M times.o P) plus.o (N times.o P)$, $((x, y), z) mapsto (x times.o z, y times.o z)$, is bilinear by @prop-tensor-rules, so @thm-tensor-univ gives an $R$-morphism $Phi$ with $Phi((x, y) times.o z) = (x times.o z, y times.o z)$. Conversely, the inclusions $iota_1: M -> M plus.o N$, $x mapsto (x, 0)$, and $iota_2: N -> M plus.o N$, $y mapsto (0, y)$, give by @thm-tensor-maps the $R$-morphisms $iota_1 times.o 1_P$ and $iota_2 times.o 1_P$, and $Psi(u, v) = (iota_1 times.o 1_P)(u) + (iota_2 times.o 1_P)(v)$ is an $R$-morphism $(M times.o P) plus.o (N times.o P) -> (M plus.o N) times.o P$. On generators,
  $ Psi(Phi((x, y) times.o z)) = (x, 0) times.o z + (0, y) times.o z = (x, y) times.o z, $
  $ Phi(Psi(x times.o z, 0)) = Phi((x, 0) times.o z) = (x times.o z, 0 times.o z) = (x times.o z, 0), $
  and similarly for $(0, y times.o z)$. The elements $(x times.o z, 0)$ and $(0, y times.o z)$ generate $(M times.o P) plus.o (N times.o P)$, so $Psi compose Phi$ and $Phi compose Psi$ are the identities.
]

#theorem(status: "S")[
  Let $M$ be an $R$-module, and regard $R$ as the $R$-module $attach(R, tl: R)$. Then $R times.o_R M tilde.equiv M$, with $a times.o x mapsto a x$.
] <thm-r-tensor>

#proof(status: "C")[
  The map $f: R times M -> M$, $(a, x) mapsto a x$, is $R$-bilinear by the module axioms. By @thm-tensor-univ there is a unique $R$-morphism $f': R times.o M -> M$ such that the diagram
  #cd(
    ((0, 0, $R times M$), (0, 1, $R times.o M$), (1, 1, $M$)),
    (
      (from: (0, 0), to: (0, 1), label: $g$, pad: (22, 24)),
      (from: (0, 0), to: (1, 1), label: $f$, side: "right", pad: (22, 14)),
      (from: (0, 1), to: (1, 1), label: $f'$),
    ),
  )
  commutes, where $g(a, y) = a times.o y$; so $f'(a times.o x) = f(a, x) = a x$.

  $f'$ is surjective: for $x in M$, $f'(1 times.o x) = 1 x = x$. It is injective: an arbitrary element of $R times.o M$ is
  $ sum_i a_i times.o x_i = sum_i a_i (1 times.o x_i) = sum_i 1 times.o a_i x_i = 1 times.o sum_i a_i x_i = 1 times.o m, quad m = sum_i a_i x_i. $
  If $1 times.o m in ker f'$, then $0 = f'(1 times.o m) = m$, so $1 times.o m = 1 times.o 0 = 0$. Hence $ker f' = {0}$, and $f'$ is an isomorphism.
]

#example(status: "S")[
  Determine $ZZ slash 2 ZZ times.o_ZZ ZZ slash 3 ZZ$.
]

#solution(status: "S+")[
  For $x in ZZ slash 2 ZZ$ and $y in ZZ slash 3 ZZ$, using $2 x = 0$ and $3 y = 0$,
  $ x times.o y = (3 - 2)(x times.o y) = x times.o 3 y - 2 x times.o y = x times.o 0 - 0 times.o y = 0. $
  For instance $[1]_2 times.o [2]_3 = [1]_2 times.o 2 [1]_3 = 2 ([1]_2 times.o [1]_3) = [2]_2 times.o [1]_3 = 0$. As the elements $x times.o y$ generate the tensor product (@prop-tensor-rules), $ZZ slash 2 ZZ times.o_ZZ ZZ slash 3 ZZ = 0$.
]

#example(status: "S")[
  Determine $ZZ times.o_ZZ QQ$.
]

#solution(status: "A")[
  By @thm-r-tensor with $R = ZZ$ and $M = QQ$, $ZZ times.o_ZZ QQ tilde.equiv QQ$, with $n times.o q mapsto n q$.
]
