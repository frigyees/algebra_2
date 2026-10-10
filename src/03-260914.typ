#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 03-260914 · Hensel example, arithmetic functions, Möbius inversion
// HEADINGS section 7 from source
// CORRECTIONS
//   [p1] t = 2 (mod 5) -> t = -2 (mod 5); range 1 <= j < 5 -> 0 <= j <= 4 (adds the lifts 14, 19)
//   [p1] sigma(n) = sum_i sum_j p_i^j -> product_i sum_j p_i^j
//   [p2] sum_{i=0}^alpha phi(i) -> phi(p^i); "F(n) = sum f(n)" -> sum f(d); second inner sum d_2 | m -> d_2 | n
// ADDITIONS (A filled in)
//   [p1] A: residues of f mod 5 and mod 125 for the rejected lifts; the f'(c) = 0 case stated in full; solution count
//   [p1] A: product formulas for d and sigma derived; multiplicativity of d, sigma from them; f not identically 0 in property 1
//   [p2] A: existence, uniqueness and bijectivity in the divisor lemma; multiplicativity of mu; n = 1 cases
//   [p2] A: exchange of summation justified in the inversion proof
//   [p3] A: Theorem 7.9 cited in the example; squarefree reduction of the sum

// [p1]
#example[
  Solve $x^3 + 2 x - 22 equiv 0 pmod(125)$.
]

#solution[
  Let $f(x) = x^3 + 2 x - 22$, so $f'(x) = 3 x^2 + 2$ and $125 = 5^3$.

  *Modulo 5.* The values of $f(0), dots, f(4)$ modulo $5$ are $3, 1, 0, 1, 0$, so $x equiv 2$ or $x equiv 4 equiv -1 pmod(5)$.

  *Case 1: $x equiv 2 pmod(5)$.* Here $f'(2) = 14 equiv -1 equiv.not 0 pmod(5)$, so by @thm-hensel there is exactly one solution modulo $125$ in this class. Write $x = 5 t + 2$ with $t in ZZ$. Modulo $25$,
  $ (5 t + 2)^3 + 2(5 t + 2) - 22 equiv 60 t + 8 + 10 t + 4 - 22 = 70 t - 10 pmod(25), $
  and $70 t - 10 equiv 0 pmod(25)$ if and only if $-5 t equiv 10 pmod(25)$, that is, $t equiv -2 pmod(5)$. So $t = 5 s - 2$ with $s in ZZ$, and $x = 5(5 s - 2) + 2 = 25 s - 8$. Modulo $125$, @lem-hensel gives
  $ f(25 s - 8) equiv f(-8) + 25 s f'(-8) = -550 + 25 s dot 194 equiv -50 + 25 s dot 194 pmod(125), $
  which vanishes modulo $125$ if and only if $-2 + 194 s equiv 0 pmod(5)$, that is, $s equiv -2 pmod(5)$. So $s = 5 r - 2$ with $r in ZZ$, and $x = 25(5 r - 2) - 8 = 125 r - 58$. Hence $x equiv -58 equiv 67 pmod(125)$.

  *Case 2: $x equiv -1 pmod(5)$.* Here $f'(-1) = 5 equiv 0 pmod(5)$, and @thm-hensel does not apply. By the proof of @thm-hensel, if $c_(k - 1) equiv -1 pmod(5)$ solves the congruence modulo $5^(k - 1)$, then $c_(k - 1) + t 5^(k - 1)$ solves it modulo $5^k$ if and only if $f(c_(k - 1)) slash 5^(k - 1) + t f'(-1) equiv 0 pmod(5)$, that is, if and only if $5^k divides f(c_(k - 1))$. So either every lift is a solution or none is.

  Since $f(-1) = -25 equiv 0 pmod(25)$, every $x equiv -1 pmod(5)$ solves $f(x) equiv 0 pmod(25)$, namely $x equiv 4, 9, 14, 19, 24 pmod(25)$. For each such $c$ and $j in ZZ$, @lem-hensel and $5 divides f'(c)$ give $f(c + 25 j) equiv f(c) pmod(125)$. Now $f(4) = 50$, $f(9) = 725 equiv 100$, $f(24) = 13850 equiv 100$, while $f(14) = 2750 = 22 dot 125$ and $f(19) = 6875 = 55 dot 125$. So the solutions in this class are $x equiv 14 + 25 j$ and $x equiv 19 + 25 j pmod(125)$ with $0 <= j <= 4$.

  Altogether the congruence has $11$ solutions modulo $125$: $x equiv 67$, and $x equiv 14 + 25 j$, $19 + 25 j$ for $0 <= j <= 4$.
]

= Arithmetic functions

#definition(title: [Arithmetic function])[
  An _arithmetic function_ is a function $f: NN -> CC$. It is _multiplicative_ if $f(a b) = f(a) f(b)$ for all $a, b in NN$ with $(a, b) = 1$, and _additive_ if $f(a b) = f(a) + f(b)$ for all $a, b in NN$ with $(a, b) = 1$.
]

#example[
  Let $d(n)$, also written $tau(n)$, be the number of positive divisors of $n$. If $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$ with distinct primes $p_i$, then $d(n) = product_(i = 1)^r (1 + alpha_i)$, because the divisors of $n$ are exactly the products $p_1^(beta_1) dots.c p_r^(beta_r)$ with $0 <= beta_i <= alpha_i$. Hence $d$ is multiplicative: for $(m, n) = 1$ the prime divisors of $m$ and $n$ are disjoint, and $d(m n) = d(m) d(n)$.
]

#example[
  Let $sigma(n)$ be the sum of the positive divisors of $n$; for instance $sigma(6) = 1 + 2 + 3 + 6 = 12$. For $n = product_(i = 1)^r p_i^(alpha_i)$ as above, summing over the divisors described in the previous example gives
  $ sigma(n) = product_(i = 1)^r sum_(j = 0)^(alpha_i) p_i^j. $
  As for $d$, this formula shows that $sigma$ is multiplicative.
]

#example[
  Euler's function $phi$ is multiplicative (@rem-recall-phi). Let $omega(n)$ be the number of distinct prime divisors of $n$; then $omega$ is additive. Let $Omega(n)$ be the number of prime divisors of $n$ counted with multiplicity, so $Omega(n) = sum_(i = 1)^r alpha_i$ for $n$ as above; then $Omega$ is additive.
]

#proposition[
  + If $f$ is multiplicative and not identically $0$, then $f(1) = 1$.
  + If $f$ is additive, then $f(1) = 0$.
]

#proof[
  1) Choose $a$ with $f(a) != 0$. Since $(1, a) = 1$, $f(a) = f(1 dot a) = f(1) f(a)$, so $f(1) = 1$.

  2) Since $(1, 1) = 1$, $f(1) = f(1 dot 1) = f(1) + f(1)$, so $f(1) = 0$.
]

#definition(title: [Summation function])[
  Let $f: NN -> CC$ be an arithmetic function. Its _summation function_ is $f^+ (n) = F(n) = sum_(d divides n) f(d)$, where $d$ runs over the positive divisors of $n$.
]

// [p2]
#lemma[
  Let $a, b in NN$ with $(a, b) = 1$ and let $d divides a b$. Then there are unique $d_1, d_2 in NN$ with $d_1 divides a$, $d_2 divides b$ and $d = d_1 d_2$. Hence $(d_1, d_2) mapsto d_1 d_2$ is a bijection from the pairs of positive divisors of $a$ and $b$ onto the positive divisors of $a b$.
] <lem-divisor-split>

#proof[
  Put $d_1 = (d, a)$ and $d_2 = (d, b)$. They are coprime and both divide $d$, so $d_1 d_2 divides d$. Conversely, let $q^e$ be the exact power of a prime $q$ dividing $d$. Since $q$ divides at most one of $a, b$, say $a$, and $q^e divides a b$, we get $q^e divides a$ and so $q^e divides d_1$. Hence $d divides d_1 d_2$, and $d = d_1 d_2$. If also $d = e_1 e_2$ with $e_1 divides a$ and $e_2 divides b$, then $e_1 divides (d, a) = d_1$ and $e_2 divides d_2$, and $e_1 e_2 = d_1 d_2$ forces $e_1 = d_1$, $e_2 = d_2$. Every product $d_1 d_2$ with $d_1 divides a$, $d_2 divides b$ divides $a b$, which gives the bijection.
]

#theorem[
  If $f: NN -> CC$ is multiplicative, then $F(n) = sum_(d divides n) f(d)$ is multiplicative.
] <thm-summation-mult>

#proof[
  Let $(m, n) = 1$. By @lem-divisor-split, and since $(d_1, d_2) = 1$ for $d_1 divides m$, $d_2 divides n$,
  $ F(m n) = sum_(d divides m n) f(d) = sum_(d_1 divides m, space d_2 divides n) f(d_1 d_2) = sum_(d_1 divides m, space d_2 divides n) f(d_1) f(d_2) = sum_(d_1 divides m) f(d_1) sum_(d_2 divides n) f(d_2) = F(m) F(n). $
]

#theorem[
  For every $n in NN$, $phi^+ (n) = sum_(d divides n) phi(d) = n$.
] <thm-phi-sum>

#proof[
  For $n = 1$ both sides equal $1$. For a prime power $n = p^alpha$ with $alpha >= 1$,
  $ F(p^alpha) = sum_(d divides p^alpha) phi(d) = sum_(i = 0)^alpha phi(p^i) = 1 + (p - 1) + (p^2 - p) + dots.c + (p^alpha - p^(alpha - 1)) = p^alpha. $
  For $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$, $F$ is multiplicative by @thm-summation-mult, so $F(n) = F(p_1^(alpha_1)) dots.c F(p_r^(alpha_r)) = p_1^(alpha_1) dots.c p_r^(alpha_r) = n$.
]

#definition(title: [Möbius function])[
  The _Möbius function_ is
  $ mu(n) = cases(1 & "if" n = 1, (-1)^r & "if" n = p_1 dots.c p_r "with distinct primes" p_i, 0 & "otherwise".) $
  So $mu(n) != 0$ if and only if $n$ is square-free. For example, $mu(10) = (-1)^2 = 1$.
]

#proposition[
  The function $mu$ is multiplicative, and
  $ mu^+ (n) = sum_(d divides n) mu(d) = cases(1 & "if" n = 1, 0 & "otherwise".) $
] <prop-mu>

#proof[
  Let $(m, n) = 1$. If $m$ or $n$ is not square-free, neither is $m n$, and both sides of $mu(m n) = mu(m) mu(n)$ vanish. Otherwise $m$ and $n$ are products of $r$ and $s$ distinct primes, the primes of $m$ and $n$ are distinct, and $mu(m n) = (-1)^(r + s) = mu(m) mu(n)$.

  For $n = 1$, $mu^+ (1) = mu(1) = 1$. For $n = p^alpha$ with $alpha >= 1$, $mu^+ (p^alpha) = mu(1) + mu(p) + dots.c + mu(p^alpha) = 1 + (-1) = 0$. For $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$ with $r >= 1$, $mu^+$ is multiplicative by @thm-summation-mult, so $mu^+ (n) = mu^+ (p_1^(alpha_1)) dots.c mu^+ (p_r^(alpha_r)) = 0$.
]

#theorem(title: [Möbius inversion formula])[
  Let $f, F: NN -> CC$ be arithmetic functions with $F(n) = sum_(d divides n) f(d)$ for every $n in NN$. Then $f(n) = sum_(d divides n) mu(d) F(n slash d)$ for every $n in NN$.
] <thm-mobius>

#proof[
  The pairs $(d, c)$ of positive integers with $d divides n$ and $c divides n slash d$ are exactly those with $c d divides n$, that is, with $c divides n$ and $d divides n slash c$. Hence, using @prop-mu,
  $ sum_(d divides n) mu(d) F(n / d) = sum_(d divides n) mu(d) sum_(c divides n slash d) f(c) = sum_(c divides n) f(c) sum_(d divides n slash c) mu(d) = f(n), $
  since the inner sum is $1$ for $c = n$ and $0$ otherwise.
]

#theorem[
  Let $f, F: NN -> CC$ with $F(n) = sum_(d divides n) f(d)$ for every $n$. If $F$ is multiplicative, then $f$ is multiplicative.
]

#proof[
  Let $(m, n) = 1$. By @thm-mobius and @lem-divisor-split, writing $d = d_1 d_2$ with $d_1 divides m$, $d_2 divides n$,
  $ f(m n) = sum_(d divides m n) mu(d) F((m n) / d) = sum_(d_1 divides m, space d_2 divides n) mu(d_1 d_2) F(m / d_1 dot n / d_2) \
    = sum_(d_1 divides m) mu(d_1) F(m / d_1) sum_(d_2 divides n) mu(d_2) F(n / d_2) = f(m) f(n). $
  The third equality uses that $mu$ and $F$ are multiplicative, with $(d_1, d_2) = 1$ and $(m slash d_1, n slash d_2) = 1$.
]

// [p3]
#example[
  Let $F(n) = n$. Compute $f$ with $F = f^+$.
]

#solution[
  By @thm-phi-sum, $F = phi^+$, so @thm-mobius gives
  $ phi(n) = sum_(d divides n) mu(d) F(n / d) = n sum_(d divides n) mu(d) / d. $
  Both $F$ and $phi$ are multiplicative. For $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$, only square-free $d$ contribute, that is, products of distinct $p_i$, so
  $ phi(n) = n - n / p_1 - dots.c - n / p_r + n / (p_1 p_2) + dots.c + n / (p_(r - 1) p_r) - n / (p_1 p_2 p_3) \
    - dots.c + (-1)^r n / (p_1 dots.c p_r) \
    = n product_(i = 1)^r (1 - 1 / p_i). $
]
