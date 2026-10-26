#import "../lib/style.typ": *
#import "../lib/macros.typ": *

// 14-261026 · a quintic not solvable by radicals; review exercises
// HEADINGS section 25 coined (source: "Midterm")
// DROPPED
//   [p1] note on the exam scope; [p2] ex. 3 (Q(4th root 2)|Q not normal): repeats 10-261009 ex. 9
//   [p3] whole page: duplicate scan of 13-261019 p1
// CORRECTIONS
//   [p2] ex. 4: (x - sqrt 3)(x + sqrt 3)(x - 5)(x + 5) -> (x - sqrt 5)(x + sqrt 5)
//   [p2] ex. 5: 2^8 = -1 (mod 13) -> 2^8 = 9; order 12 shown via 2^4 = 3 and 2^6 = -1; result unchanged
//   [p2] ex. 5: power table, entry at alpha = 12 read as 0 -> 1
//   [p2] ex. 5: 3x^7 = 8 (mod 12) -> (mod 13)
// READINGS
//   [p2] ex. 6: "(-1)^(sum p_i) (-1)^(sum alpha_i)" read as (-1)^(sum p_i) (-1)^(sum q_j)
// STATEMENTS
//   ex. 1-6 statements taken from the printed problem sheet (scans/14-261026-sheet.png); ex. 3 still dropped as a repeat
// ADDITIONS (A filled in)
//   [p1] A: Eisenstein p = 2; Rolle via the real zeros of f'; sign changes located; complex conjugation in G; Cauchy, Lemma 24.13
//   [p1] A: ex. 1: residues mod 5, uniqueness by Hensel, check f(13) = 76 * 25
//   [p1] A: ex. 2: reciprocity and Legendre properties cited; p > 3 ensures p not 2, 3
//   [p2] A: ex. 4: sqrt 5 not in Q(sqrt 3); all four maps exist; group table; ex. 5: ind_2 3, ind_2 8 read from the table; check
//   [p2] A: ex. 5: 2 is the smallest positive primitive root (1 has order 1)
//   [p2] A: ex. 6: F multiplicative via Theorem 7.7, case 2 | n made explicit

// [p1]
#example[
  Is $f(x) = x^5 - 2 x^3 - 8 x + 2 in QQ[x]$ solvable by radicals?
]

#solution[
  No. By @rem-eisenstein with $p = 2$, $f$ is irreducible over $QQ$. We have
  $ f'(x) = 5 x^4 - 6 x^2 - 8 = (x^2 - 2)(5 x^2 + 4), $
  whose real zeros are $plus.minus sqrt(2)$. By Rolle's theorem $f$ has at most $3$ real zeros. From
  #align(center, table(
    columns: 5,
    $x$, $-3$, $0$, $1$, $3$,
    $f(x)$, $-163$, $2$, $-7$, $167$,
  ))
  and the intermediate value theorem, $f$ has zeros in $(-3, 0)$, $(0, 1)$ and $(1, 3)$. So its roots are $a_1, a_2, a_3 in RR$ and $a_4, a_5 in CC without RR$ with $overline(a_4) = a_5$.

  Let $KK$ be the splitting field of $f$ over $QQ$ and $G = Gal(KK | QQ) <= S_5$. Complex conjugation restricts to an element $sigma in G$ (@prop-normal-crit) with $sigma(a_4) = a_5$, fixing $a_1, a_2, a_3$, so $G$ contains a transposition. Since $f$ is irreducible, $5 = [QQ(a_1) : QQ]$ divides $[KK : QQ] = |G|$, and by Cauchy's theorem $G$ contains an element of order $5$, that is, a $5$-cycle. By @lem-sp-gen, $G = S_5$; for instance $S_5 = chevron.l (1 space 2 space 3 space 4 space 5), (4 space 5) chevron.r$. $S_5$ is not solvable (@thm-sn-solvable), since $A_5$ is simple, so $f$ is not solvable by radicals by @thm-galois-radicals.
]

= Review exercises

#example[
  Solve $x^3 - 2 x^2 + 3 x + 2 equiv 0 pmod(25)$.
]

#solution[
  Let $f(x) = x^3 - 2 x^2 + 3 x + 2$. Modulo $5$, the values $f(0), dots, f(4)$ are $2, 4, 3, 0, 1$, so $x equiv 3 pmod(5)$ is the only solution. Since $f'(x) = 3 x^2 - 4 x + 3$ and $f'(3) = 27 - 12 + 3 = 18 equiv.not 0 pmod(5)$, @thm-hensel gives exactly one solution modulo $25$.

  Write $x = 5 t + 3$. By @lem-hensel,
  $ f(5 t + 3) equiv f(3) + 5 t f'(3) = 20 + 90 t pmod(25), $
  so $90 t + 20 equiv 0 pmod(25)$, that is, $18 t + 4 equiv 0 pmod(5)$, or $3 t + 4 equiv 0 pmod(5)$. Multiplying by $2$ gives $6 t + 8 equiv t + 3 equiv 0 pmod(5)$, so $t equiv 2 pmod(5)$ and
  $ x equiv 13 pmod(25). $
  Indeed $f(13) = 1900 = 76 dot 25$.
]

#example[
  Let $p > 3$ be a prime. Compute $ls(3, p)$.
]

#solution[
  Since $p != 2, 3$, the symbol is defined and @thm-qr applies with $3 equiv -1 pmod(4)$. We use @prop-legendre 1) and $ls(1, 3) = 1$, $ls(2, 3) = -1$.

  _Case I: $p equiv -1 pmod(4)$._ By @thm-qr,
  $ ls(3, p) = -ls(p, 3) = cases(-ls(1, 3) = -1 & "if" p equiv 1 pmod(3), -ls(2, 3) = -(-1) = 1 & "if" p equiv -1 pmod(3).) $

  _Case II: $p equiv 1 pmod(4)$._ By @thm-qr,
  $ ls(3, p) = ls(p, 3) = cases(ls(1, 3) = 1 & "if" p equiv 1 pmod(3), ls(2, 3) = -1 & "if" p equiv -1 pmod(3).) $

  Combining the conditions modulo $4$ and $3$ by the Chinese remainder theorem:
  - $p equiv -1 pmod(4)$, $p equiv 1 pmod(3)$: $p = 4 t - 1$ with $4 t - 1 equiv 1 pmod(3)$, so $t equiv 2 pmod(3)$ and $p equiv 7 pmod(12)$; $ls(3, p) = -1$.
  - $p equiv -1 pmod(4)$, $p equiv -1 pmod(3)$: $4 t - 1 equiv -1 pmod(3)$, so $t equiv 0 pmod(3)$ and $p equiv -1 pmod(12)$; $ls(3, p) = 1$.
  - $p equiv 1 pmod(4)$, $p equiv 1 pmod(3)$: $p = 4 t + 1$ with $4 t + 1 equiv 1 pmod(3)$, so $t equiv 0 pmod(3)$ and $p equiv 1 pmod(12)$; $ls(3, p) = 1$.
  - $p equiv 1 pmod(4)$, $p equiv -1 pmod(3)$: $4 t + 1 equiv -1 pmod(3)$, that is, $4 t equiv 1 pmod(3)$, so $t equiv 1 pmod(3)$ and $p equiv 5 pmod(12)$; $ls(3, p) = -1$.
  Hence
  $ ls(3, p) = cases(1 & "if" p equiv plus.minus 1 pmod(12), -1 & "if" p equiv plus.minus 5 pmod(12).) $
]

// [p2]
#example[
  Prove that the field extension $QQ subset.eq QQ(sqrt(3), sqrt(5))$ is Galois and determine its Galois group.
]

#solution[
  We need that $QQ(sqrt(3), sqrt(5)) | QQ$ is normal and separable. It is separable since $"char" QQ = 0$ (@lem-sep-deriv). The minimal polynomials are $m_(sqrt(3)) (x) = x^2 - 3$ and $m_(sqrt(5)) (x) = x^2 - 5$, and
  $ (x^2 - 3)(x^2 - 5) = (x - sqrt(3))(x + sqrt(3))(x - sqrt(5))(x + sqrt(5)), $
  so $QQ(sqrt(3), sqrt(5))$ is the splitting field of $(x^2 - 3)(x^2 - 5)$, hence normal (@thm-normal-split), and the extension is Galois.

  $sqrt(5) in.not QQ(sqrt(3))$: if $sqrt(5) = u + v sqrt(3)$ with $u, v in QQ$, then $5 = u^2 + 3 v^2 + 2 u v sqrt(3)$ forces $u v = 0$, and either case makes $sqrt(5)$ or $sqrt(5 slash 3)$ rational. So
  $ [QQ(sqrt(3), sqrt(5)) : QQ] = [QQ(sqrt(3), sqrt(5)) : QQ(sqrt(3))] [QQ(sqrt(3)) : QQ] = 2 dot 2 = 4, $
  and $G = Gal(QQ(sqrt(3), sqrt(5)) | QQ)$ has order $4$ (@prop-gal-order). For $sigma in G$, $sigma(3) = 3$ gives $sigma(sqrt(3))^2 = sigma(3) = 3$, so $sigma(sqrt(3)) = plus.minus sqrt(3)$, and similarly $sigma(sqrt(5)) = plus.minus sqrt(5)$. These are four possibilities, and $|G| = 4$, so all occur:
  $ "id": & sqrt(3) mapsto sqrt(3), space sqrt(5) mapsto sqrt(5), quad alpha: sqrt(3) mapsto -sqrt(3), space sqrt(5) mapsto sqrt(5), \
    beta: & sqrt(3) mapsto sqrt(3), space sqrt(5) mapsto -sqrt(5), quad gamma: sqrt(3) mapsto -sqrt(3), space sqrt(5) mapsto -sqrt(5). $
  Then $(alpha beta)(sqrt(3)) = -sqrt(3) = gamma(sqrt(3))$ and $(alpha beta)(sqrt(5)) = -sqrt(5) = gamma(sqrt(5))$, so $alpha beta = gamma$. Likewise $(alpha gamma)(sqrt(3)) = sqrt(3)$, $(alpha gamma)(sqrt(5)) = -sqrt(5)$, so $alpha gamma = beta$, and similarly $gamma beta = alpha$. Every element has order at most $2$, so $G tilde.equiv ZZ_2 times ZZ_2$, the Klein four-group.
]

#example[
  Find the smallest positive primitive root modulo $13$. Make an index table and solve $3 x^7 equiv 8 pmod(13)$.
]

#solution[
  $phi(13) = 12$, so $ord(13, 2) divides 12$ by @prop-order, that is, $ord(13, 2) in {1, 2, 3, 4, 6, 12}$. By @proc-prim it suffices to check $2^(12 slash 2) = 2^6$ and $2^(12 slash 3) = 2^4$: $2^4 = 16 equiv 3$ and $2^6 = 64 equiv -1 pmod(13)$. Hence $ord(13, 2) = 12$, and $2$ is a primitive root modulo $13$. Since $ord(13, 1) = 1$, $2$ is the smallest positive primitive root. The powers of $2$ modulo $13$ are:
  #align(center, table(
    columns: 14,
    $alpha$, ..range(0, 13).map(n => [#n]),
    $2^alpha$, ..(1, 2, 4, 8, 3, 6, 12, 11, 9, 5, 10, 7, 1).map(v => [#v]),
  ))
  From the table, $ind_2 3 = 4$ and $ind_2 8 = 3$. Taking indices in $3 x^7 equiv 8 pmod(13)$, @thm-ind gives
  $ ind_2 3 + 7 ind_2 x equiv ind_2 8 pmod(12), quad "that is," quad 4 + 7 ind_2 x equiv 3 pmod(12), $
  so $7 ind_2 x equiv -1 pmod(12)$.
  Put $y = ind_2 x$ and multiply by $5$: $35 y equiv -5 pmod(12)$. Since $35 equiv -1 pmod(12)$, $-y equiv -5$ and $y equiv 5 pmod(12)$. Hence $x equiv 2^5 = 32 equiv 6 pmod(13)$. Indeed $6^7 equiv 7 pmod(13)$ and $3 dot 7 = 21 equiv 8 pmod(13)$.
]

#example[
  For $n = p_1^(alpha_1) p_2^(alpha_2) dots.c p_r^(alpha_r)$, define the arithmetic function
  $ f(n) = cases((-1)^(p_1 + p_2 + dots.c + p_r) & "if" n > 1, 1 & "if" n = 1.) $
  Prove that $f$ is multiplicative and determine its summation function.
]

#solution[
  Here the $p_i$ are distinct primes and $alpha_i >= 1$. Let $F(n) = sum_(d divides n) f(d)$ be the summation function.

  _$f$ is multiplicative._ Let $m = q_1^(beta_1) dots.c q_s^(beta_s)$ with distinct primes $q_j$, and $gcd(n, m) = 1$, so $p_i != q_j$ for all $i, j$. Then the distinct prime divisors of $m n$ are the $p_i$ and the $q_j$, and
  $ f(m n) = f(p_1^(alpha_1) dots.c p_r^(alpha_r) q_1^(beta_1) dots.c q_s^(beta_s)) = (-1)^(p_1 + dots.c + p_r + q_1 + dots.c + q_s) = (-1)^(sum_i p_i) (-1)^(sum_j q_j) = f(n) f(m). $
  If $n = 1$ or $m = 1$, this holds since $f(1) = 1$.

  _$F$._ By @thm-summation-mult, $F$ is multiplicative, so it suffices to compute it on prime powers. For $alpha >= 1$,
  $ F(p^alpha) = sum_(d divides p^alpha) f(d) = f(1) + f(p) + dots.c + f(p^alpha) = 1 + alpha (-1)^p = cases(alpha + 1 & "if" p = 2, 1 - alpha & "if" p > 2.) $
  Hence, for $n = p_1^(alpha_1) dots.c p_r^(alpha_r)$,
  $ F(n) = product_(i = 1)^r F(p_i^(alpha_i)) = cases(product_(i = 1)^r (1 - alpha_i) & "if" 2 divides.not n, (1 + alpha_1) product_(i = 2)^r (1 - alpha_i) & "if" 2 divides n "and" p_1 = 2.) $
]
