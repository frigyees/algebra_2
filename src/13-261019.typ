#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 13-261019 · radical extensions, Kummer theory, solvability by radicals
// HEADINGS section 24 coined
// DROPPED
//   [p1] [p2] crossed-out marginal drawings
// CORRECTIONS
//   [p1] lemma (1): "if F and E are both radical extensions of K, then so are FE|F, FE|E" -> FE|F is a root extension whenever E|K is, for any F
//   [p1] lemma (3) proof: normal closure "is the completion of these root extensions" -> compositum of the conjugates of F
//   [p2] main theorem: K_(i+1) = K_i(m_i-th root of a_i), a_i in K -> a_i in K_i
//   [p2] example: f(3) = 180 -> 189; "at most 3 real roots" -> exactly 3 (intermediate value theorem gives at least 3)
// READINGS
//   [p2] (<=): Gal(K_i|K_(i-1)) read as G_(i-1)/G_i
// SCOPE
//   [p1] Kummer: char K not dividing n -> char K = 0; the notes' "x^n - a separable, thus F|K Galois" is proved here only in characteristic 0, the only case used
// ADDITIONS (A filled in, B supplied proof, C cited)
//   [p1] A: radical extension K(b), b^n = a; fixed algebraic closure; definition of solvable by radicals made precise
//   [p1] A: Kummer (1): a = 0 case, distinctness of roots, Galois via Theorem 17.21 and Lemma 17.7; (2): sigma(rho) computed, rho^n in K via Theorem 18.8
//   [p1] B: Dedekind's lemma on independence of automorphisms
//   [p1] A: remark K(zeta_n)|K refers to Proposition 20.4; normal closure defined; lemma (2), (3) proved
//   [p2] A: (=>) exponents of the tower over K(zeta_m) divide m; normality of L_(j+1)|L_j; Gal(F|K) quotient of Gal(L|K), solvable via the derived series
//   [p2] A: (<=) K_i|K_(i-1) Galois via Theorem 18.12; natural irrationalities: Gal(E_i|E_(i-1)) embeds in Gal(K_i|K_(i-1))
//   [p2] A: example: Eisenstein p = 2, Rolle twice, complex conjugation in G, 5-cycle from cycle type
//   [p2] B: p-cycle and transposition generate S_p; C: Cauchy's theorem

// [p1]
= Solvability by radicals

Throughout, all fields considered over a field $KK$ lie in a fixed algebraic closure $Omega$ of $KK$.

#definition(title: [Radical extension])[
  An extension $KK subset.eq KK(b)$ with $b^n = a in KK$ for some $n in NN$ is a _radical extension_; we write $KK(b) = KK(root(n, a))$.
]

#remark[
  The notation $root(n, a) = b$ only says $b^n = a$, $b in Omega$, and is ambiguous: $x^n - a$ has several roots. When $KK$ contains the $n$-th roots of unity, $KK(root(n, a))$ contains all roots of $x^n - a$, namely $root(n, a) dot zeta$ with $zeta^n = 1$, so the field does not depend on the choice.
]

#definition(title: [Radical tower, root extension])[
  A tower $KK = KK_0 subset.eq KK_1 subset.eq dots.c subset.eq KK_ell$ in which every $KK_i | KK_(i - 1)$ is a radical extension is a _radical tower_. Then $KK_ell | KK$ is a _root extension_, and the elements of $KK_ell$ are said to be _expressible by radicals_ over $KK$.
]

#definition(title: [Solvable by radicals])[
  A polynomial $f in KK[x]$ is _solvable by radicals_ over $KK$ if all its roots in $Omega$ lie in a root extension of $KK$.
]

#definition(title: [Cyclic extension])[
  A _cyclic extension_ is a Galois extension $FF | KK$ whose Galois group $Gal(FF | KK)$ is cyclic.
]

#lemma(title: [Dedekind])[
  Let $FF$ be a field and $sigma_1, dots, sigma_n$ pairwise distinct automorphisms of $FF$. If $c_1, dots, c_n in FF$ satisfy $c_1 sigma_1 (x) + dots.c + c_n sigma_n (x) = 0$ for all $x in FF$, then $c_1 = dots.c = c_n = 0$.
] <lem-dedekind>

#proof[
  Suppose not, and take a nontrivial relation with the least number of nonzero coefficients; renumbering, $c_1 sigma_1 + dots.c + c_k sigma_k = 0$ with all $c_i != 0$. Then $k >= 2$, since $sigma_1 (1) = 1 != 0$. Choose $y in FF$ with $sigma_1 (y) != sigma_k (y)$. For all $x$, $sum_i c_i sigma_i (y x) = sum_i c_i sigma_i (y) sigma_i (x) = 0$, and also $sigma_k (y) sum_i c_i sigma_i (x) = 0$. Subtracting,
  $ sum_(i = 1)^(k - 1) c_i (sigma_i (y) - sigma_k (y)) sigma_i (x) = 0 quad "for all" x in FF, $
  a relation with fewer nonzero terms whose first coefficient $c_1 (sigma_1 (y) - sigma_k (y))$ is nonzero. This contradicts minimality.
]

#theorem(title: [Kummer])[
  Let $n in NN$, let $"char" KK = 0$, and assume that $KK$ contains the $n$-th roots of unity.
  + For $a in KK$ let $FF = KK(root(n, a))$. Then $FF | KK$ is cyclic of degree $d$ for some $d divides n$.
  + If $FF | KK$ is cyclic of degree $n$, then $FF = KK(root(n, a))$ for some $a in KK$.
] <thm-kummer>

#proof[
  By @prop-mu-n, $KK$ contains a primitive $n$-th root of unity $xi$, and the $n$-th roots of unity are $xi^i$, $0 <= i <= n - 1$, pairwise distinct.

  1) If $a = 0$, then $FF = KK$ and the claim holds with $d = 1$. Let $a != 0$ and $b = root(n, a)$, so $b != 0$. The roots of $x^n - a$ are the $n$ distinct elements $b xi^i$, $0 <= i <= n - 1$, all in $FF$. So $FF$ is the splitting field of $x^n - a$ over $KK$, hence normal (@thm-normal-split). Since $"char" KK = 0$, $FF | KK$ is separable by @lem-sep-deriv, so it is Galois, and $|Gal(FF | KK)| = [FF : KK]$ by @prop-gal-order. Each $sigma in Gal(FF | KK)$ is determined by $sigma(b) = b xi^(i_sigma)$, with $i_sigma in ZZ_n$, by @thm-perm-roots. The map $Gal(FF | KK) -> ZZ_n$, $sigma mapsto i_sigma$, is injective, and it is a homomorphism: since $xi in KK$ is fixed,
  $ (tau sigma)(b) = tau(b xi^(i_sigma)) = tau(b) xi^(i_sigma) = b xi^(i_tau + i_sigma). $
  The map need not be surjective. Hence $Gal(FF | KK)$ is isomorphic to a subgroup of $ZZ_n$, that is, cyclic of some order $d divides n$, and $[FF : KK] = d$.

  2) Let $Gal(FF | KK) = chevron.l sigma chevron.r$ with $|sigma| = n$. For $alpha in FF$ define the _Lagrange resolvent_
  $ (alpha, xi) = alpha + xi sigma(alpha) + xi^2 sigma^2 (alpha) + dots.c + xi^(n - 1) sigma^(n - 1)(alpha). $
  The automorphisms $1, sigma, dots, sigma^(n - 1)$ are pairwise distinct, so by @lem-dedekind the map $1 + xi sigma + dots.c + xi^(n - 1) sigma^(n - 1)$ is not identically $0$; choose $alpha in FF$ with $rho = (alpha, xi) != 0$. Since $xi in KK$ and $sigma^n = 1$,
  $ sigma(rho) = sigma(alpha) + xi sigma^2 (alpha) + dots.c + xi^(n - 1) sigma^n (alpha) = xi^(-1) (xi sigma(alpha) + dots.c + xi^(n - 1) sigma^(n - 1)(alpha) + xi^n alpha) = xi^(-1) rho. $
  // [p1-p2]
  Hence $sigma(rho^n) = xi^(-n) rho^n = rho^n$, so $rho^n$ lies in the fixed field of $chevron.l sigma chevron.r = Gal(FF | KK)$, which is $KK$ by @thm-fixed. For $0 < i < n$, $sigma^i (rho) = xi^(-i) rho != rho$, since $xi$ is primitive and $rho != 0$; so $sigma^i in.not Gal(FF | KK(rho))$. Thus $Gal(FF | KK(rho)) = {"id"}$, and by @thm-fundamental-1, $KK(rho) = cal(F)({"id"}) = FF$. With $a = rho^n in KK$, $FF = KK(rho) = KK(root(n, a))$.
]

#remark[
  Let $"char" KK = 0$ and $zeta_n$ a primitive $n$-th root of unity. Then $KK subset.eq KK(zeta_n)$ is a Galois extension with abelian Galois group, by @prop-cyclo-gal.
]

#definition(title: [Compositum, normal closure])[
  For fields $FF, EE subset.eq Omega$, the _compositum_ $FF EE$ is the smallest subfield of $Omega$ containing $FF union EE$. For a finite extension $FF = KK(gamma_1, dots, gamma_s)$, the _normal closure_ of $FF | KK$ is the splitting field in $Omega$ over $KK$ of $product_j m_(gamma_j, KK)$.
]

#lemma[
  Let $"char" KK = 0$.
  + If $EE | KK$ is a root extension and $FF supset.eq KK$ is any field, then $FF EE | FF$ is a root extension.
  + If $FF | KK$ and $EE | KK$ are root extensions, then so is $FF EE | KK$.
  + If $FF | KK$ is a root extension, then so is its normal closure $LL | KK$.
] <lem-root-ext>

#proof[
  1) Let $KK = EE_0 subset.eq dots.c subset.eq EE_ell = EE$ with $EE_i = EE_(i - 1)(b_i)$ and $b_i^(n_i) in EE_(i - 1)$. Then $FF EE = FF(b_1, dots, b_ell)$, and $b_i^(n_i) in EE_(i - 1) subset.eq FF(b_1, dots, b_(i - 1))$. So $FF subset.eq FF(b_1) subset.eq dots.c subset.eq FF(b_1, dots, b_ell)$ is a radical tower. For instance, if $EE = KK(root(n, a))$, then $FF EE = FF(root(n, a))$.

  2) By 1), $FF EE | FF$ is a root extension. Appending its radical tower to one of $FF | KK$ gives a radical tower from $KK$ to $FF EE$.

  3) $FF | KK$ is finite, so $FF = KK(gamma_1, dots, gamma_s)$ with $gamma_j$ algebraic, and $LL$ is finite over $KK$, being generated by the finitely many roots of $product_j m_(gamma_j, KK)$. We show that $LL$ is the compositum of the fields $tau(FF)$, where $tau$ runs over the finitely many $KK$-monomorphisms $FF -> Omega$. Each $tau(gamma_j)$ is a root of $m_(gamma_j, KK)$ by @thm-perm-roots, so $tau(FF) subset.eq LL$. Conversely, for a root $beta$ of $m_(gamma_j, KK)$ there is a $KK$-embedding $KK(gamma_j) -> Omega$ with $gamma_j mapsto beta$, as in the proof of @thm-embed-count, and it extends to $FF$ by @lem-extend; so $beta in tau(FF)$ for some $tau$. If $KK = FF_0 subset.eq dots.c subset.eq FF_ell = FF$ is a radical tower with $FF_i = FF_(i - 1)(b_i)$, then $tau(FF_i) = tau(FF_(i - 1))(tau(b_i))$ and $tau(b_i)^(n_i) = tau(b_i^(n_i)) in tau(FF_(i - 1))$, so each $tau(FF) | KK$ is a root extension. By 2), applied finitely many times, $LL | KK$ is a root extension.
]

// [p2]
#theorem(title: [Galois])[
  Let $"char" KK = 0$, $f in KK[x]$, and let $FF$ be the splitting field of $f$ over $KK$. Then $f$ is solvable by radicals if and only if $Gal(FF | KK)$ is solvable.
] <thm-galois-radicals>

#proof[
  $(arrow.r.double)$ Assume that $f$ is solvable by radicals. Each root of $f$ lies in a root extension of $KK$; by @lem-root-ext 2), their compositum is a root extension containing all roots of $f$. So there is a radical tower $KK = KK_0 subset.eq KK_1 subset.eq dots.c subset.eq KK_n$ with $KK_(i + 1) = KK_i (b_i)$, $b_i^(m_i) = a_i in KK_i$, and $FF subset.eq KK_n$. Let $m = lcm(m_0, dots, m_(n - 1))$, $xi$ a primitive $m$-th root of unity, $EE_0 = KK(xi)$ and $EE_(i + 1) = EE_i (b_i)$. Then $EE_0 | KK$ is abelian Galois by @prop-cyclo-gal, and each $EE_(i + 1) | EE_i$ is cyclic by @thm-kummer 1), since $m_i divides m$ and $EE_i$ contains the $m_i$-th roots of unity $xi^(m slash m_i dot j)$.

  Let $LL$ be the normal closure of $EE_n | KK$. By the proof of @lem-root-ext 3), $LL$ is the compositum of the fields $tau(EE_n)$ for the $KK$-monomorphisms $tau: EE_n -> Omega$. Since $tau(xi)$ is a primitive $m$-th root of unity, $KK(tau(xi)) = KK(xi)$, both being the splitting field of $x^m - 1$. So $tau(EE_n) = KK(xi)(tau(b_0), dots, tau(b_(n - 1)))$ with $tau(b_i)^(m_i) = tau(a_i) in tau(EE_i)$. Concatenating these towers for the finitely many $tau$ gives
  $ KK subset.eq KK(xi) = LL_0 subset.eq LL_1 subset.eq dots.c subset.eq LL_N = LL, quad LL_(j + 1) = LL_j (c_j), quad c_j^(e_j) in LL_j, quad e_j divides m. $
  As above, each $LL_(j + 1) | LL_j$ is cyclic by @thm-kummer 1), and $LL_0 | KK$ is abelian Galois. $LL | KK$ is Galois, being normal (@thm-normal-split) in characteristic $0$, and $FF subset.eq LL$, as $LL$ contains all roots of $f$.

  Let $G = Gal(LL | KK)$ and $G_j = Gal(LL | LL_j)$, so $G >= G_0 >= G_1 >= dots.c >= G_N = 1$. Since $LL_(j + 1) | LL_j$ is normal, @thm-fundamental-2 applied to the Galois extension $LL | LL_j$ (@cor-normal-top) gives $G_(j + 1) lt.closed.eq G_j$ and
  $ G_j slash G_(j + 1) = Gal(LL | LL_j) slash Gal(LL | LL_(j + 1)) tilde.equiv Gal(LL_(j + 1) | LL_j), $
  which is abelian. Likewise $G_0 lt.closed.eq G$ with $G slash G_0 tilde.equiv Gal(LL_0 | KK)$ abelian. By @prop-solv-series, $G$ is solvable. Finally $FF | KK$ is normal and $KK subset.eq FF subset.eq LL$, so by @thm-fundamental-2,
  $ Gal(FF | KK) tilde.equiv Gal(LL | KK) slash Gal(LL | FF), $
  The projection $pi: Gal(LL | KK) -> Gal(FF | KK)$ is surjective, so $pi(H') = pi(H)'$ for every subgroup $H$, and by induction $pi(G^((i))) = Gal(FF | KK)^((i))$. As $G^((k)) = 1$ for some $k$, $Gal(FF | KK)^((k)) = 1$, and $Gal(FF | KK)$ is solvable.

  $(arrow.l.double)$ Assume $Gal(FF | KK)$ is solvable. By @prop-solv-cyclic there is a normal series
  $ 1 = G_n lt.closed.eq G_(n - 1) lt.closed.eq dots.c lt.closed.eq G_0 = Gal(FF | KK) $
  with $G_(i - 1) slash G_i$ cyclic of order $m_i$. Let $KK_i = cal(F)(G_i)$. Then $KK = KK_0 subset.eq KK_1 subset.eq dots.c subset.eq KK_n = FF$, by @thm-fixed and @thm-fundamental-1. By @thm-fundamental-1, $G_(i - 1) = Gal(FF | KK_(i - 1))$, and since $G_i lt.closed.eq G_(i - 1)$, @thm-fundamental-2 applied to $FF | KK_(i - 1)$ shows that $KK_i | KK_(i - 1)$ is Galois with $Gal(KK_i | KK_(i - 1)) tilde.equiv G_(i - 1) slash G_i$, cyclic of order $m_i$.

  Let $m = lcm(m_1, dots, m_n)$, $EE_0 = KK(xi_m)$ and $EE_i = EE_0 KK_i$, so $EE_i = EE_(i - 1) KK_i$. By @thm-normal-split, $KK_i$ is the splitting field over $KK_(i - 1)$ of some $g in KK_(i - 1)[x]$, so $EE_i = EE_(i - 1)(text("roots of") g)$ is the splitting field of $g$ over $EE_(i - 1)$, and $EE_i | EE_(i - 1)$ is Galois. For $sigma in Gal(EE_i | EE_(i - 1))$, $sigma$ permutes the roots of $g$ (@thm-perm-roots), so $sigma(KK_i) = KK_i$, and $sigma|_(KK_i)$ fixes $KK_(i - 1) subset.eq EE_(i - 1)$. The restriction $Gal(EE_i | EE_(i - 1)) -> Gal(KK_i | KK_(i - 1))$ is an injective homomorphism, since $EE_i$ is generated over $EE_(i - 1)$ by the roots of $g$. Hence $Gal(EE_i | EE_(i - 1))$ is isomorphic to a subgroup of a cyclic group of order $m_i$, so it is cyclic of some order $d_i divides m_i$. The field $EE_(i - 1) supset.eq EE_0$ contains the primitive $d_i$-th root of unity $xi_m^(m slash d_i)$, so by @thm-kummer 2), $EE_i = EE_(i - 1)(root(d_i, c_i))$ with $c_i in EE_(i - 1)$. Together with $EE_0 = KK(root(m, 1))$, this shows that $EE_n | KK$ is a root extension. It contains $KK_n = FF$, hence all roots of $f$, so $f$ is solvable by radicals.
]

#remark(title: [Recall])[
  _Cauchy's theorem._ If $G$ is a finite group and $p$ is a prime dividing $|G|$, then $G$ has an element of order $p$.
]

#lemma[
  Let $p$ be a prime and $G <= S_p$. If $G$ contains a $p$-cycle and a transposition, then $G = S_p$.
] <lem-sp-gen>

#proof[
  Let $(a space b) in G$ be a transposition and $c in G$ a $p$-cycle. Some power $c^k$ with $1 <= k < p$ maps $a$ to $b$; since $p$ is prime, $c^k$ is again a $p$-cycle. Relabelling the points, $a = 1$, $b = 2$ and $c^k = (1 space 2 space dots space p)$. Conjugating $(1 space 2)$ by $(c^k)^j$ gives $(j + 1 space j + 2)$, so $G$ contains all transpositions $(i space i + 1)$, $1 <= i <= p - 1$, which generate $S_p$.
]

#example[
  Show that $f(x) = x^5 - 20 x + 6 in QQ[x]$ is not solvable by radicals.
]

#solution[
  By @rem-eisenstein with $p = 2$, $f$ is irreducible over $QQ$. Let $EE subset.eq CC$ be its splitting field. Since $"char" QQ = 0$, $f$ is separable (@lem-sep-deriv) and has five distinct roots $alpha_1, dots, alpha_5$. $G = Gal(EE | QQ)$ permutes the roots and is determined by this action, so $G <= S_5$. As $[QQ(alpha_i) : QQ] = 5$, the tower law gives $5 divides [EE : QQ] = |G|$. By Cauchy's theorem $G$ has an element of order $5$; an element of $S_5$ of order $5$ has cycle lengths with least common multiple $5$, so it is a $5$-cycle.

  Now $f'(x) = 5 x^4 - 20$ and $f''(x) = 20 x^3$. As $f''$ has a single real zero, $f'$ has at most $2$ real zeros by Rolle's theorem, and so $f$ has at most $3$ real zeros. From the values
  #align(center, table(
    columns: 5,
    $x$, $-3$, $0$, $1$, $3$,
    $f(x)$, $-177$, $6$, $-13$, $189$,
  ))
  and the intermediate value theorem, $f$ has at least $3$ real zeros. So $f$ has exactly three real roots $alpha_1, alpha_2, alpha_3 in RR$ and two nonreal roots $alpha_4, alpha_5 in CC$ with $overline(alpha_4) = alpha_5$. Complex conjugation maps $EE$ onto $EE$ by @prop-normal-crit, so its restriction lies in $G$; it fixes $alpha_1, alpha_2, alpha_3$ and swaps $alpha_4, alpha_5$, so $(4 space 5) in G$. By @lem-sp-gen, $G = S_5$, which is not solvable by @thm-sn-solvable. By @thm-galois-radicals, $f$ is not solvable by radicals.
]
