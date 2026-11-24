#import "../lib/style.typ": *
#import "../lib/macros.typ": *
#import "../lib/diagram.typ": *

// 17-261109 · five lemma, quotient modules, correspondence theorem, induced morphisms, first isomorphism theorem
// p3 is a separate photo continuing the lecture.
// HEADINGS section 28 from source ("Quotient modules")
// CORRECTIONS
//   [p1] five lemma: rows not required exact -> exact rows; bottom row ends in E -> E'
//   [p1] definition: natural map called an R-epimorphism before M/E has a module structure -> stated after the theorem
//   [p2] correspondence: "submodules of A" -> submodules of M containing N; "isomorphism" -> inclusion-preserving bijection
//   [p2] lemma: "f is injective iff A = f^<-(B)" -> f_*; "B + im f = N" kept
//   [p2] lemma proof: "theorem of sets and maps" -> its R-module version (factorization through an epimorphism)
//   [p3] first isomorphism theorem: "a unique R-morphism lambda" -> unique R-isomorphism
// NOTATION
//   class {x}_E -> [x]_E (braces read as a singleton); natural surjection a_E, f_N, f_A -> pi_E, pi_N, pi_A
// ADDITIONS (A filled in)
//   [p1] A: five lemma: which hypotheses each application of the four lemma uses; corollary via zero modules
//   [p1] A: (1) => (2) of the quotient theorem; module axioms on M/E; uniqueness via right cancellation
//   [p1] A: (2) => (3): [0]_E is a submodule, x - y = 0 (E) iff x = y (E)
//   [p2] A: bijection proposition: well-definedness of the inverse; cosets x + N
//   [p2] A: correspondence: f_N^<-(P) contains N; inclusion preserved both ways
//   [p2] A: lemma (b) argument completed; uniqueness from Theorem 27.2
//   [p3] A: f^+ is an epimorphism; lambda surjective via lemma (b)
//   FIGURES diagrams redrawn with lib/diagram.typ

// [p1]
#theorem(status: "C", title: [Five lemma])[
  Suppose that the diagram of $R$-modules and $R$-morphisms
  #cd(
    ((0, 0, $A$), (0, 1, $B$), (0, 2, $C$), (0, 3, $D$), (0, 4, $E$), (1, 0, $A'$), (1, 1, $B'$), (1, 2, $C'$), (1, 3, $D'$), (1, 4, $E'$)),
    (
      (from: (0, 0), to: (0, 1)), (from: (0, 1), to: (0, 2)), (from: (0, 2), to: (0, 3)), (from: (0, 3), to: (0, 4)),
      (from: (1, 0), to: (1, 1)), (from: (1, 1), to: (1, 2)), (from: (1, 2), to: (1, 3)), (from: (1, 3), to: (1, 4)),
      (from: (0, 0), to: (1, 0), label: $alpha_1$, side: "right"),
      (from: (0, 1), to: (1, 1), label: $alpha_2$, side: "right"),
      (from: (0, 2), to: (1, 2), label: $alpha_3$, side: "right"),
      (from: (0, 3), to: (1, 3), label: $alpha_4$, side: "right"),
      (from: (0, 4), to: (1, 4), label: $alpha_5$, side: "right"),
    ),
    dx: 1.7cm,
  )
  is commutative with exact rows. If $alpha_1, alpha_2, alpha_4$ and $alpha_5$ are isomorphisms, then so is $alpha_3$.
] <thm-five-lemma>

#proof(status: "S")[
  @thm-four-lemma 2), applied to the squares between $A, B, C, D$, with $alpha_1$ an epimorphism and $alpha_2, alpha_4$ monomorphisms, shows that $alpha_3$ is a monomorphism. @thm-four-lemma 1), applied to the squares between $B, C, D, E$, with $alpha_2, alpha_4$ epimorphisms and $alpha_5$ a monomorphism, shows that $alpha_3$ is an epimorphism.
]

#corollary(status: "S", title: [Short five lemma])[
  Suppose that the diagram of $R$-modules and $R$-morphisms
  #cd(
    ((0, 0, $0$), (0, 1, $A$), (0, 2, $B$), (0, 3, $C$), (0, 4, $0$), (1, 0, $0$), (1, 1, $A'$), (1, 2, $B'$), (1, 3, $C'$), (1, 4, $0$)),
    (
      (from: (0, 0), to: (0, 1)), (from: (0, 1), to: (0, 2)), (from: (0, 2), to: (0, 3)), (from: (0, 3), to: (0, 4)),
      (from: (1, 0), to: (1, 1)), (from: (1, 1), to: (1, 2)), (from: (1, 2), to: (1, 3)), (from: (1, 3), to: (1, 4)),
      (from: (0, 1), to: (1, 1), label: $alpha$, side: "right"),
      (from: (0, 2), to: (1, 2), label: $beta$, side: "right"),
      (from: (0, 3), to: (1, 3), label: $gamma$, side: "right"),
    ),
    dx: 1.7cm,
  )
  commutes and has exact rows. If $alpha$ and $gamma$ are isomorphisms, then so is $beta$.
] <cor-short-five>

#proof(status: "A")[
  Apply @thm-five-lemma with the zero maps $0 -> 0$ as the outer vertical morphisms; they are isomorphisms.
]

= Quotient modules

Let $M$ be an $R$-module and $E$ an equivalence relation on $M$. We write $x equiv y space (E)$ if $x$ and $y$ are related, $[x]_E$ for the class of $x$, and $M slash E$ for the set of equivalence classes of $M$ with respect to $E$. The _natural surjection_ is $pi_E: M -> M slash E$, $x mapsto [x]_E$.

#theorem(status: "S")[
  Let $M$ be an $R$-module and $E$ an equivalence relation on $M$. The following are equivalent:
  + there are a unique addition $([x]_E, [y]_E) mapsto [x]_E + [y]_E$ and a unique $R$-action $(lambda, [x]_E) mapsto lambda [x]_E$ such that $M slash E$ is an $R$-module and $pi_E$ is an $R$-epimorphism;
  + $E$ is _compatible_ with the structure of $M$: if $x equiv a space (E)$ and $y equiv b space (E)$, then $x + y equiv a + b space (E)$, and if $x equiv a space (E)$ and $lambda in R$, then $lambda x equiv lambda a space (E)$;
  + there is a submodule $M_E$ of $M$ such that $x equiv y space (E)$ if and only if $x - y in M_E$.
] <thm-quotient>

#proof(status: "S+")[
  #extra[
  1) $=>$ 2): if $x equiv a$ and $y equiv b$, then $pi_E (x + y) = pi_E (x) + pi_E (y) = pi_E (a) + pi_E (b) = pi_E (a + b)$, so $x + y equiv a + b$. Similarly $pi_E (lambda x) = lambda pi_E (x) = lambda pi_E (a) = pi_E (lambda a)$.
  ]

  2) $=>$ 1): consider the diagrams
  #cd(
    ((0, 0, $M times M$), (0, 1, $M slash E$), (1, 0, $M slash E times M slash E$), (0, 2, $R times M$), (0, 3, $M slash E$), (1, 2, $R times M slash E$)),
    (
      (from: (0, 0), to: (0, 1), label: $g$, pad: (26, 18)),
      (from: (0, 0), to: (1, 0), label: $f$, side: "right"),
      (from: (1, 0), to: (0, 1), side: "right", dashed: true, pad: (30, 18)),
      (from: (0, 2), to: (0, 3), label: $g'$, pad: (24, 18)),
      (from: (0, 2), to: (1, 2), label: $f'$, side: "right"),
      (from: (1, 2), to: (0, 3), side: "right", dashed: true, pad: (30, 18)),
    ),
    dx: 2.8cm,
  )
  where $f(x, y) = ([x]_E, [y]_E)$, $g(x, y) = [x + y]_E$, $f'(lambda, x) = (lambda, [x]_E)$ and $g'(lambda, x) = [lambda x]_E$. Compatibility says precisely that $f(x, y) = f(a, b)$ implies $g(x, y) = g(a, b)$, and $f'(lambda, x) = f'(lambda, a)$ implies $g'(lambda, x) = g'(lambda, a)$. By @thm-sets-factor-1 there are maps completing both diagrams, that is, operations with $[x]_E + [y]_E = [x + y]_E$ and $lambda [x]_E = [lambda x]_E$; they are unique since $f$ and $f'$ are surjective (right cancellation, @cor-surjective). Each module axiom for $M slash E$ follows from the same axiom in $M$ by applying $pi_E$, for instance $lambda ([x]_E + [y]_E) = [lambda (x + y)]_E = [lambda x + lambda y]_E = lambda [x]_E + lambda [y]_E$. By construction $pi_E$ is an $R$-morphism, and it is surjective. Conversely, any operations making $pi_E$ an $R$-morphism satisfy these formulas, which proves uniqueness.

  2) $=>$ 3): suppose that $E$ is compatible and let $M_E = [0]_E$. If $x equiv 0$ and $y equiv 0$, then $x - y = x + (-1_R) y equiv 0 + 0 = 0$, and $lambda x equiv lambda 0 = 0$; also $0 in [0]_E$. So $[0]_E$ is a submodule of $M$ (@prop-submod-crit). If $x equiv y$, then $x - y equiv y - y = 0$, so $x - y in M_E$. Conversely, if $x - y equiv 0$, then $x = (x - y) + y equiv 0 + y = y$.

  3) $=>$ 2): let $M_E$ be a submodule with $x equiv y space (E)$ if and only if $x - y in M_E$. If $x equiv a$ and $y equiv b$, then $x - a, y - b in M_E$, so $(x + y) - (a + b) in M_E$ and $x + y equiv a + b$. For $lambda in R$, $lambda x - lambda a = lambda (x - a) in M_E$, so $lambda x equiv lambda a$.
]

// [p2]
#definition(status: "C", title: [Quotient module])[
  If $M$ is an $R$-module and $E$ a compatible equivalence relation on $M$, the $R$-module $M slash E$ of @thm-quotient is the _quotient module_ of $M$ by $E$, and $pi_E$ is the _natural epimorphism_.
]

#proposition(status: "S")[
  The map $E mapsto [0]_E$ is a bijection from the set of compatible equivalence relations on $M$ onto the set of submodules of $M$.
] <prop-compat-submod>

#proof(status: "S")[
  By @thm-quotient, $[0]_E$ is a submodule, and $x equiv y space (E)$ if and only if $x - y in [0]_E$. Hence $E$ is determined by $[0]_E$, and the map is injective: if $[0]_E = [0]_F$, then $x equiv y space (E)$ if and only if $x equiv y space (F)$. It is surjective: if $N$ is a submodule of $M$, the relation $x equiv y space (F) <=> x - y in N$ is an equivalence relation, compatible by @thm-quotient 3) $=>$ 2), and $[0]_F = {x : x - 0 in N} = N$.
]

#remark(status: "S")[
  For a submodule $N$ of $M$ we write $M slash N$ for the quotient by the corresponding compatible relation, and $pi_N$ for the natural epimorphism. The class $[x]_N$ is the coset $x + N = {x + n : n in N}$: indeed $y in [x]_N$ if and only if $y - x in N$, if and only if $y = x + n$ for some $n in N$. Moreover $ker pi_N = [0]_N = N$.
]

#theorem(status: "S", title: [Correspondence theorem])[
  Let $N$ be a submodule of an $R$-module $M$. Then $A mapsto A slash N = {[a]_N : a in A}$ is an inclusion-preserving bijection from the set of submodules of $M$ that contain $N$ onto the set of submodules of $M slash N$, and its inverse $P mapsto pi_N^(arrow.l)(P)$ also preserves inclusion.
] <thm-correspondence>

#proof(status: "C")[
  Let $phi(A) = A slash N = pi_N^(arrow.r)(A)$, a submodule of $M slash N$ by @thm-img-preimg. If $N subset.eq A$, then by @cor-img-preimg
  $ pi_N^(arrow.l)(phi(A)) = pi_N^(arrow.l)(pi_N^(arrow.r)(A)) = A + ker pi_N = A + N = A. $
  So $phi(A) = phi(B)$ implies $A = B$, and $phi$ is injective. If $P$ is a submodule of $M slash N$, then $pi_N^(arrow.l)(P)$ is a submodule of $M$ (@thm-img-preimg) containing $pi_N^(arrow.l)({0}) = N$, and by @cor-img-preimg
  $ phi(pi_N^(arrow.l)(P)) = pi_N^(arrow.r)(pi_N^(arrow.l)(P)) = P inter im pi_N = P inter M slash N = P. $
  So $phi$ is surjective with inverse $P mapsto pi_N^(arrow.l)(P)$. Both images and preimages preserve inclusion.
]

#corollary(status: "S")[
  Every submodule of $M slash N$ is of the form $A slash N$, where $A$ is a submodule of $M$ that contains $N$.
]

#lemma(status: "C")[
  Let $M, N$ be $R$-modules and $f: M -> N$ an $R$-morphism. Let $A$ be a submodule of $M$ and $B$ a submodule of $N$. The following are equivalent:
  + $f^(arrow.r)(A) subset.eq B$;
  + there is a unique $R$-morphism $f_*: M slash A -> N slash B$ such that the diagram
  #cd(
    ((0, 0, $M$), (0, 1, $N$), (1, 0, $M slash A$), (1, 1, $N slash B$)),
    (
      (from: (0, 0), to: (0, 1), label: $f$),
      (from: (0, 0), to: (1, 0), label: $pi_A$, side: "right"),
      (from: (0, 1), to: (1, 1), label: $pi_B$),
      (from: (1, 0), to: (1, 1), label: $f_*$, side: "right", dashed: true, pad: (24, 22)),
    ),
    dx: 2.9cm,
  )
  commutes, that is, $f_* compose pi_A = pi_B compose f$.
  Moreover, if such an $f_*$ exists, then it is
  #enum(numbering: "(a)", [a monomorphism if and only if $A = f^(arrow.l)(B)$;], [an epimorphism if and only if $B + im f = N$.])
] <lem-induced>

#proof(status: "C")[
  $pi_A$ is an epimorphism, so by @thm-factor-epi applied to $pi_A$ and $pi_B compose f$, an $R$-morphism $f_*$ with $f_* compose pi_A = pi_B compose f$ exists, and is then unique, if and only if $ker pi_A subset.eq ker(pi_B compose f)$. Here
  $ x in ker pi_A <=> [x]_A = [0]_A <=> x in A, quad x in ker(pi_B compose f) <=> [f(x)]_B = [0]_B <=> f(x) in B. $
  So the condition reads: $x in A$ implies $f(x) in B$, which is 1).

  By the formula $f_*([x]_A) = [f(x)]_B$,
  $ ker f_* = {[x]_A : f(x) in B} = {[x]_A : x in f^(arrow.l)(B)} = f^(arrow.l)(B) slash A, $
  where $A subset.eq f^(arrow.l)(B)$ by 1). By @thm-correspondence, $f^(arrow.l)(B) slash A$ is the zero submodule $A slash A$ if and only if $f^(arrow.l)(B) = A$. This proves (a).

  // [p2-p3]
  For (b), $im f_* = {[f(x)]_B : x in M}$. So $f_*$ is surjective if and only if for every $n in N$ there is $x in M$ with $[n]_B = [f(x)]_B$, that is, $n - f(x) in B$. This holds if and only if every $n in N$ lies in $B + im f$, that is, $N = B + im f$.
]

// [p3]
#theorem(status: "S", title: [First isomorphism theorem])[
  Let $f: M -> N$ be an $R$-morphism and $f^+: M -> im f$, $x mapsto f(x)$. Then there is a unique $R$-isomorphism $lambda: M slash ker f -> im f$ such that the diagram
  #cd(
    ((0, 0, $M$), (0, 1, $im f$), (1, 0, $M slash ker f$)),
    (
      (from: (0, 0), to: (0, 1), label: $f^+$, pad: (14, 22)),
      (from: (0, 0), to: (1, 0), label: $pi_(ker f)$, side: "right"),
      (from: (1, 0), to: (0, 1), label: $lambda$, side: "right", dashed: true, pad: (26, 18)),
    ),
  )
  commutes, that is, $lambda compose pi_(ker f) = f^+$.
] <thm-first-iso>

#proof(status: "S+")[
  Apply @lem-induced to $f^+: M -> im f$ with $A = ker f$ and $B = {0}$. Here $N slash {0}$ is identified with $N$ through the isomorphism $pi_({0})$, whose kernel is ${0}$. Condition 1) holds, since $(f^+)^(arrow.r)(ker f) = {0}$. So there is a unique $R$-morphism $lambda$ with $lambda compose pi_(ker f) = f^+$. It is a monomorphism by (a), since $ker f = f^(arrow.l)({0})$, and an epimorphism by (b), since $f^+$ is surjective, so ${0} + im f^+ = im f$. Hence $lambda$ is an isomorphism.
]
