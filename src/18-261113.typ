#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 18-261113 · second and third isomorphism theorems, tensor product, free modules (translated from Hungarian)
// HEADINGS section 28 continued; section 29 from source ("Modulusok tenzorszorzata"); subsection 29.1 coined, 29.2 from source ("Szabad modulusok")
// NOTATION (normalized to the earlier fragments)
//   submodule relation N <= M -> "N is a submodule of M"; natural map written as a script d (d_P, d_N) -> pi_P, pi_N
//   classes {u}_P -> [u]_P; f^=> -> f^->; "R-izomorfizmus" -> R-isomorphism; field of reals written R -> RR (R is the ring)
//   Hungarian theorem names "masodik/harmadik izomorfizmus-tetel" kept as second/third (the numbering used for the first isomorphism theorem)
// DROPPED
//   [p4] decorative sketch in the margin
// CORRECTIONS
//   [p1] second iso proof: "h o pi_N epimorphism => h epimorphism" justified via Lemma 28.7 (b), not commutativity alone
//   [p2] "V := R^2 (x) R^2" with R both the reals and the ring -> RR^2 (x) RR^2
//   [p4] tensor product defined for arbitrary R -> R commutative (otherwise a(x (x) y) is not defined and M (x)_R N is not an R-module)
//   [p4] Z (x) Z/2Z: claim 2 (x) [1]_2 != 0 in 2Z (x) Z/2Z stated without reason -> justified
//   [p4] rank "the number of basis elements" -> well defined for commutative nonzero R (cited)
// GAPS
//   bilinear map and Hom_R are used but not defined in the notes; supplied
//   the existence proof uses the free module on M x N and its universal property, which appear only in 19-261116; forward references
//   [p1] third isomorphism theorem stated without proof; supplied
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: hypotheses P subset N; why N/P is a submodule; application of Lemma 28.7 spelled out
//   [p2] A: motivation example computed for x = (2, 3), y = (4, 5); identification RR^2 (x) RR^2 = RR^4 labelled as a remark
//   [p2-p3] A: universal property stated with R-bilinear g; existence: D, T = F/D, bilinearity of g; f' well defined; uniqueness
//   [p3] A: uniqueness of (T, g) up to isomorphism (the two-diagram argument written out)
//   [p4] A: x (x) 0 = 0 derived; generation statement
//   [p4] A: R_R free with basis {1}; definitions of linear independence and basis taken from the more detailed repeat in 19-261116 p1
//   [p4] C: every vector space has a basis; invariance of rank

// [p1]
#theorem(title: [Second isomorphism theorem])[
  Let $M$ be an $R$-module and $N, P$ submodules of $M$ with $P subset.eq N$. Then $N slash P$ is a submodule of $M slash P$, and there is a unique $R$-isomorphism $h: M slash N -> (M slash P) slash (N slash P)$ such that the diagram
  #cd(
    ((0, 0, $M$), (0, 1, $M slash P$), (1, 0, $M slash N$), (1, 1, $(M slash P) slash (N slash P)$)),
    (
      (from: (0, 0), to: (0, 1), label: $pi_P$),
      (from: (0, 0), to: (1, 0), label: $pi_N$, side: "right"),
      (from: (0, 1), to: (1, 1), label: $pi$),
      (from: (1, 0), to: (1, 1), label: $h$, side: "right", dashed: true, pad: (26, 50)),
    ),
    dx: 3.4cm,
  )
  commutes, where $pi$ is the natural epimorphism of $M slash P$ onto $(M slash P) slash (N slash P)$.
] <thm-second-iso>

#proof[
  $N slash P = pi_P^(arrow.r)(N) = {[u]_P : u in N}$ is a submodule of $M slash P$ by @thm-img-preimg. Apply @lem-induced to $f = pi_P: M -> M slash P$ with $A = N$ and $B = N slash P$. Condition 1) holds, since $pi_P^(arrow.r)(N) = N slash P$. So there is a unique $R$-morphism $h: M slash N -> (M slash P) slash (N slash P)$ with $h compose pi_N = pi compose pi_P$.

  // [p2]
  By @lem-induced (b), $h$ is an epimorphism, since $N slash P + im pi_P = N slash P + M slash P = M slash P$. By @lem-induced (a), $h$ is a monomorphism, since by @cor-img-preimg and $P subset.eq N$,
  $ pi_P^(arrow.l)(N slash P) = pi_P^(arrow.l)(pi_P^(arrow.r)(N)) = N + ker pi_P = N + P = N. $
  Hence $h$ is an isomorphism.
]

#theorem(title: [Third isomorphism theorem])[
  Let $A, B$ be submodules of an $R$-module $M$. Then
  $ A slash (A inter B) tilde.equiv (A + B) slash B. $
] <thm-third-iso>

#proof[
  Let $f: A -> (A + B) slash B$, $a mapsto [a]_B$, the restriction of $pi_B$ to $A$; it is an $R$-morphism. It is surjective: an element of $(A + B) slash B$ is $[a + b]_B$ with $a in A$, $b in B$, and $[a + b]_B = [a]_B = f(a)$, since $(a + b) - a in B$. Its kernel is ${a in A : a in B} = A inter B$. By @thm-first-iso, $A slash (A inter B) = A slash ker f tilde.equiv im f = (A + B) slash B$.
]

= Tensor products of modules

Throughout this section $R$ is a commutative ring with identity. The aim is to treat bilinear maps defined on $M times N$ as linear maps defined on a new module.

== The tensor product

#definition(title: [Bilinear map])[
  Let $M, N, P$ be $R$-modules. A map $f: M times N -> P$ is _$R$-bilinear_ if it is an $R$-morphism in each variable when the other is fixed:
  $ f(x + x', y) = f(x, y) + f(x', y), quad f(x, y + y') = f(x, y) + f(x, y'), \
    f(a x, y) = a f(x, y) = f(x, a y) $
  for all $x, x' in M$, $y, y' in N$ and $a in R$. The set of such maps is denoted $Bil_R (M times N, P)$, and the set of $R$-morphisms $M -> P$ is denoted $Hom_R (M, P)$.
]

#example[
  The map $f: RR^2 times RR^2 -> RR$, $f(x, y) = x_1 y_1 + x_2 y_2$, is $RR$-bilinear but not linear on $RR^4 = RR^2 times RR^2$. Assign to $(x, y)$ the vector
  $ x times.o y = (x_1 y_1, x_1 y_2, x_2 y_1, x_2 y_2) in RR^4. $
  Then $f(x, y) = tilde(f)(x times.o y)$ for the linear map $tilde(f): RR^4 -> RR$, $tilde(f)(z) = z_1 + z_4$. For instance, with $x = (2, 3)$ and $y = (4, 5)$,
  $ x times.o y = (8, 10, 12, 15), quad tilde(f)(x times.o y) = 8 + 15 = 23 = 2 dot 4 + 3 dot 5 = f(x, y). $
  So the bilinear map $f$ becomes a linear map on the space $RR^4$, which plays the role of $RR^2 times.o RR^2$.
]

#remark[
  The construction below achieves this in general: it produces an $R$-module $M times.o_R N$ with $Bil_R (M times N, P) tilde.equiv Hom_R (M times.o_R N, P)$ for every $R$-module $P$.
]

#theorem(title: [Universal property of the tensor product])[
  Let $M, N$ be $R$-modules. There is a pair $(T, g)$, where $T$ is an $R$-module and $g: M times N -> T$ an $R$-bilinear map, such that for every $R$-module $P$ and every $R$-bilinear map $f: M times N -> P$ there is a unique $R$-morphism $f': T -> P$ for which the diagram
  // [p2]
  #cd(
    ((0, 0, $M times N$), (0, 1, $T$), (1, 1, $P$)),
    (
      (from: (0, 0), to: (0, 1), label: $g$, pad: (24, 12)),
      (from: (0, 0), to: (1, 1), label: $f$, side: "right", pad: (24, 12)),
      (from: (0, 1), to: (1, 1), label: $f'$, dashed: true),
    ),
  )
  commutes, that is, $f = f' compose g$. The pair is unique up to isomorphism: if $(T, g)$ and $(T', g')$ both have this property, then there is an $R$-isomorphism $t: T -> T'$ with $g' = t compose g$.
] <thm-tensor-univ>

#proof[
  _Existence._ Let $F$ be the free $R$-module on the set $M times N$ (@def-free-on-set). Its elements are the formal linear combinations $sum_(i = 1)^n a_i (x_i, y_i)$ with $a_i in R$ and $(x_i, y_i) in M times N$. Let $D$ be the submodule of $F$ generated by all elements of the forms
  $ (x + x', y) - (x, y) - (x', y), quad (x, y + y') - (x, y) - (x, y'), quad (a x, y) - a (x, y), quad (x, a y) - a (x, y), $
  with $x, x' in M$, $y, y' in N$ and $a in R$. Let $T = F slash D$, and write $x times.o y$ for the class $(x, y) + D$ of $(x, y)$. The elements $x times.o y$ generate $T$, since the $(x, y)$ generate $F$: every element of $T$ has the form
  $ sum_(i = 1)^n a_i (x_i times.o y_i) = sum_(i = 1)^n a_i (x_i, y_i) + D. $

  // [p2-p3]
  For $x, x' in M$ and $y in N$, the element $(x + x', y) - (x, y) - (x', y)$ lies in $D$, hence
  $ (x + x', y) + D = ((x, y) + D) + ((x', y) + D), quad "that is," quad (x + x') times.o y = x times.o y + x' times.o y. $
  In the same way $x times.o (y + y') = x times.o y + x times.o y'$, and for $a in R$, $(a x, y) - a (x, y) in D$ gives $(a x) times.o y = a (x times.o y)$, and similarly $x times.o (a y) = a (x times.o y)$. So $g: M times N -> T$, $g(x, y) = x times.o y$, is $R$-bilinear.

  // [p3]
  Let $P$ be an $R$-module and $f: M times N -> P$ an $R$-bilinear map. By the universal property of free modules (@prop-free-univ), $f$ extends to a unique $R$-morphism $overline(f): F -> P$ with $overline(f)((x, y)) = f(x, y)$. Then $overline(f)$ maps the generators of $D$, hence all of $D$, to $0$. For instance,
  $ overline(f)((x + x', y) - (x, y) - (x', y)) = f(x + x', y) - f(x, y) - f(x', y) = 0 $
  by bilinearity of $f$, and the same holds for the other three forms. So $D subset.eq ker overline(f)$. Since $ker pi_D = D$, @thm-factor-epi gives a unique $R$-morphism $f': T = F slash D -> P$ with $f' compose pi_D = overline(f)$, that is,
  $ f'(x times.o y) = overline(f)((x, y)) = f(x, y). $
  Hence $f' compose g = f$.

  _Uniqueness of $f'$._ Let $f_1: T -> P$ be an $R$-morphism with $f = f_1 compose g$. Then for $(x, y) in M times N$,
  $ f_1 (x times.o y) = f_1 (g(x, y)) = f(x, y) = f'(g(x, y)) = f'(x times.o y). $
  The elements $x times.o y$ generate $T$, so $f_1 = f'$ on all of $T$.

  // [p3-p4]
  _Uniqueness of $(T, g)$._ Let $(T', g')$ also have the property. Applied to $(T, g)$ and the bilinear map $g'$, it gives a unique $R$-morphism $t: T -> T'$ with $g' = t compose g$; applied to $(T', g')$ and $g$, it gives a unique $t': T' -> T$ with $g = t' compose g'$. Then $g = t' compose t compose g$ and $g' = t compose t' compose g'$. But $"id"_T$ also satisfies $g = "id"_T compose g$, so by the uniqueness part of the property for $(T, g)$, $t' compose t = "id"_T$; similarly $t compose t' = "id"_(T')$. Hence $t$ is an isomorphism.
]

#definition(title: [Tensor product])[
  Let $M, N$ be $R$-modules. The $R$-module $T$ constructed in the proof of @thm-tensor-univ is the _tensor product_ of $M$ and $N$, denoted $M times.o_R N$, and $x times.o y$ is the _tensor product_ of $x in M$ and $y in N$. We write $M times.o N$ when $R$ is clear.
]

#remark[
  By @thm-tensor-univ, $f mapsto f'$ is a bijection $Bil_R (M times N, P) -> Hom_R (M times.o_R N, P)$, with inverse $f' mapsto f' compose g$.
]

#proposition[
  Let $M, N$ be $R$-modules.
  + For all $x, x' in M$, $y, y' in N$ and $a in R$:
    $ (x + x') times.o y = x times.o y + x' times.o y, quad x times.o (y + y') = x times.o y + x times.o y', $
    $ (a x) times.o y = a (x times.o y) = x times.o (a y), quad 0 times.o y = x times.o 0 = 0. $
  + $M times.o N$ is generated by the elements $x times.o y$ with $x in M$ and $y in N$. If ${x_i}_(i in I)$ generates $M$ and ${y_j}_(j in J)$ generates $N$, then ${x_i times.o y_j}_((i, j) in I times J)$ generates $M times.o N$.
] <prop-tensor-rules>

#proof[
  1) The first five identities were shown in the proof of @thm-tensor-univ. Then $0 times.o y = (0 + 0) times.o y = 0 times.o y + 0 times.o y$, so $0 times.o y = 0$, and similarly $x times.o 0 = 0$.

  2) The first statement was shown in the proof of @thm-tensor-univ. If $x = sum_i a_i x_i$ and $y = sum_j b_j y_j$, then by 1) $x times.o y = sum_(i, j) a_i b_j (x_i times.o y_j)$.
]

#example[
  Consider the $ZZ$-modules $ZZ$, $2 ZZ$ and $ZZ slash 2 ZZ$. In $ZZ times.o_ZZ ZZ slash 2 ZZ$,
  $ 2 times.o [1]_2 = (2 dot 1) times.o [1]_2 = 2 (1 times.o [1]_2) = 1 times.o 2 [1]_2 = 1 times.o [0]_2 = 0. $
  In $2 ZZ times.o_ZZ ZZ slash 2 ZZ$, however, $2 times.o [1]_2 != 0$, although $2 ZZ subset.eq ZZ$: the step $2 times.o [1]_2 = 2 (1 times.o [1]_2)$ is unavailable, as $1 in.not 2 ZZ$. Indeed, $phi: ZZ -> 2 ZZ$, $n mapsto 2 n$, is a $ZZ$-isomorphism, so by @cor-tensor-iso and @thm-r-tensor
  $ 2 ZZ times.o ZZ slash 2 ZZ tilde.equiv ZZ times.o ZZ slash 2 ZZ tilde.equiv ZZ slash 2 ZZ, quad 2 times.o [1]_2 mapsto 1 times.o [1]_2 mapsto [1]_2 != 0. $
  So the tensor product does not preserve inclusions: the inclusion $2 ZZ -> ZZ$ induces the zero map on the generator $2 times.o [1]_2$.
]

// [p4]
== Free modules

#definition(title: [Basis, free module])[
  Let $M$ be an $R$-module and $S subset.eq M$. The set $S$ is _linearly independent_ if for any distinct $s_1, dots, s_n in S$ and $r_1, dots, r_n in R$, $sum_(i = 1)^n r_i s_i = 0$ implies $r_1 = dots.c = r_n = 0$. It is a _basis_ of $M$ if it generates $M$, that is, $chevron.l S chevron.r = M$, and it is linearly independent. An $R$-module is _free_ if it has a basis. The _rank_ of a free $R$-module is the cardinality of a basis.
]

#remark(cited: true)[
  If $R$ is commutative and nonzero, any two bases of a free $R$-module have the same cardinality, so the rank is well defined.
]

#example[
  The module $attach(R, tl: R)$ is free with basis ${1_R}$: every $r in R$ is $r 1_R$, and $r 1_R = 0$ implies $r = 0$.
]

#theorem(cited: true)[
  Every vector space over a field $K$ has a basis; in particular it is a free $K$-module.
]
