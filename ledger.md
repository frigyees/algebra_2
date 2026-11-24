# Source ledger

Why the document diverges from the scans. The provenance of every environment, proof and solution is recorded in the source as its `status:` argument, which is authoritative and decides what the course edition contains. This file gives the reasons: one row per block that diverges from the scans, that is, every block whose status is not S, and S blocks with a minor divergence worth recording. Blocks taken over from the scans without change have no row. Headings and unnumbered prose paragraphs, which carry no tag, are listed here when they diverge. Block numbers refer to the current build; the full and course editions share them.

## Status codes

| Code | Meaning |
|---|---|
| S | In the scans. Translation, notation and wording may differ; the mathematical content does not. |
| S+ | In the scans, completed: hypotheses, steps or justifications were supplied. The note says what. |
| C | In the scans with an error, corrected here. The note gives the scans' version. |
| I | Not in the scans, but the scans use it without stating it (likely said in the lecture). |
| A | Not in the scans. Added in typesetting. |
| B | Not in the scans: the scans state the result without proof, and a standard proof was supplied. |

The course edition keeps S, S+ and C. A proof listed in several rows (parts) is tagged with a course status if any part is lecture content; parts with status A inside such a proof, and added sentences inside lecture blocks, are wrapped in `#extra` and are absent from the course edition (currently: Proof 28.1, (1) ⇒ (2); the justification in Rem 1.9; the pointer "4) is proved after Lemma 4.4" in Proof 4.3).

Scan references have the form `NNNNNN pK` (lecture date, scan page).

Policy: where the scans' own argument is correct, the document keeps it, completed if necessary; a block is replaced only where the scans are false or the argument does not work. Added material is kept only where the document needs it: a definition or result that later blocks use, or a proof of a result the lectures stated. No lecture took place on 30 October (midterm).

## 01-260907

Dropped: the textbook reference in the margin of p1 (Freud–Gyarmati) and the midterm note "ZH Oct 30".

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 1 | A | | |
| Rem 1.1 (recall: φ, Euler–Fermat) | S | 260907 p1 | Margin recall. Multiplicativity of φ added. |
| Def 1.2 (order) | S+ | 260907 p1 | The scans have the heading "Def (order)" only; the definition itself was supplied. |
| Proof 1.3 | C | 260907 p1 | The scans write k = d·O_m(a) with d ∈ ℤ⁺, which misses k = 0; corrected to d ≥ 0. Otherwise as in the scans. |
| Lem 1.6 (order of a power) | A | | Needed by the supplied proofs. |
| Proof 1.6 | A | | |
| Rem 1.7 (recall: Lagrange) | A | | Needed by the supplied existence proof. |
| Thm 1.8 (existence of primitive roots) | S | 260907 p1 | Hypotheses m ≥ 2 and α ≥ 1 made explicit. |
| Proof 1.8 | A | | No proof in the scans. |
| Proof of Rem 1.9 (inside the remark) | A | | |
| Thm 1.10 (number of primitive roots) | C | 260907 p1 | The scans state "the number of primitive roots mod m is φ(φ(m))" for every m; false when none exists (m = 12). Corrected: "if a primitive root exists". The case m = p is in the scans. |
| Proof 1.10 | A | | |
| Thm 1.11 (φ(n) > cn / log log n) | S | 260907 p1 | Cited. n ≥ 3 added (log log n must be defined). |
| Proc 1.12 (checking primitive roots) | C | 260907 p1 | The scans write the exponent as (p−1)/q_1 for every i; corrected to (p−1)/q_i. |
| Proof 1.12 | A | | |
| Thm 1.13 (Burgess) | S | 260907 p1 | Cited. c depends on ε (added). |
| Thm 1.14 (bound under GRH) | C | 260907 p1 | The scans: "if the Riemann hypothesis is true, then n(p) < c (ln p)²". Under GRH the (log p)² bound is Ankeny's bound for the least quadratic non-residue; for the least primitive root the known bound is Shoup's, stated here. Cited. |
| Thm 1.15 (prime number theorem) | S | 260907 p1 | Cited. Includes the error term under RH, as in the scans. |
| Def 1.16 (reduced residue system) | S | 260907 p2 | Margin note. |
| Thm 1.17 (primitive roots and reduced residue systems) | S | 260907 p2 | (g, m) = 1 made explicit. |
| Heading 2 | A | | |
| Def 2.1 (index) | S | 260907 p2 | p ∤ a made explicit. |
| Rem 2.6 (discrete log problem) | C | 260907 p3 | The scans: "no effective algorithm is known". Brute force is an effective algorithm; corrected to "no classical algorithm polynomial in log p is known". |
| Rem 2.7 (cyclic groups) | S | 260907 p3 | The scans say only that it generalizes; the formulation was added. |
| Heading 3 | A | | |

## 02-260911

Scan pages are in reverse order; reading order is p11 to p1. The boxed "I/2" on p11 is not content.

| Block | Status | Scan | Note |
|---|---|---|---|
| Rem 3.2 (recall: linear congruences) | A | | Used in the scans without being stated. |
| Thm 3.3 (solvability of x^k ≡ a) | S | 260911 p11 | Includes the solution count and the index form of the condition. |
| Proof 3.3 | S+ | 260911 p11-10 | The reduction to k·y ≡ ind_g a (mod p−1) and the direction "(k, p−1) ∣ ind_g a ⇒ a^((p−1)/(k,p−1)) ≡ 1" are in the scans. Added: the converse direction and the solution count. |
| Solution 3.4 | C | 260911 p10-8 | The scans write "ind_22" for ind_2 and "z ≡ 2, 8 (mod 6)"; corrected to mod 12. Final answer x ≡ 4, 9 (mod 13) as in the scans. |
| Proof 3.5 | A | | |
| Prop 3.6 (a^((p−1)/2) ≡ ±1) | C | 260911 p8-7 | The scans: "a is a quadratic residue iff a^((p−1)/2) ≡ −1"; corrected to ≡ 1. |
| Proof 3.6 | S+ | 260911 p8 | Fermat's little theorem is cited in the scans; the factorization step was added. |
| Heading 4 | A | | |
| Proof 4.2 | A | | |
| Proof 4.3 | S+ | 260911 p7 | Property 2 is proved in the scans. Proofs of 1 and 3 added; 4 is proved via Lem 4.4 (added). |
| Lem 4.4 (Gauss's lemma) | A | | |
| Proof 4.4 | A | | |
| Proof of Prop 4.3 (4) | A | | |
| Lem 4.5 (parity of the floor sum) | A | | |
| Proof 4.5 | A | | |
| Thm 4.6 (quadratic reciprocity) | S | 260911 p6 | p ≠ q made explicit. The product form is added. |
| Proof 4.6 | A | | |
| Solution 4.8 | S+ | 260911 p6-5 | Chain and result 1 are in the scans. Added: justification of each step and the note that symbols with denominator 391 are Jacobi symbols. |
| Heading 5 | A | | |
| Lem 5.2 (parity identities) | A | | |
| Proof 5.2 | A | | |
| Prop 5.3 (properties 1–5 of the Jacobi symbol) | C | 260911 p5-4 | Property 5 in the scans: (a/mn) = (a/n) + (a/m); corrected to a product. |
| Proof 5.3 | A | | |
| Thm 5.4 (Jacobi reciprocity) | S | 260911 p4 | (m, n) = 1 made explicit. |
| Proof 5.4 | A | | |
| Heading 6 | S | 260911 p4 | "Polynomial congruences". |
| Prose (lifting to p^k) | A | | |
| Proof 6.2 | S+ | 260911 p3-1 | Induction, the linear congruence for t and t = t_0 + sp are in the scans. Added: the uniqueness step c_k ≡ c_(k−1) (mod p^(k−1)) and the existence direction. Corrected: c_(n−1) to c_(k−1). |

## 03-260914

| Block | Status | Scan | Note |
|---|---|---|---|
| Solution 6.4 | C | 260914 p1 | The scans conclude t ≡ 2 (mod 5) from −5t ≡ 10 (mod 25); corrected to t ≡ −2, which the scans' next step t = 5s − 2 already uses. In case 2 the scans list x = 14 + 25j, 19 + 25j with 1 ≤ j < 5, which omits 14 and 19 although the scans themselves verify them; corrected to 0 ≤ j ≤ 4 (11 roots in total). Added: residues of f mod 5, the argument for case 2 written out. |
| Ex 7.2 (d(n)) | S+ | 260914 p1 | Formula and multiplicativity are in the scans; the reasons were added. |
| Ex 7.3 (σ(n)) | C | 260914 p1 | The scans give σ(n) = Σ_i Σ_j p_i^j; corrected to the product Π_i Σ_j p_i^j. |
| Lem 7.7 (splitting divisors) | S | 260914 p2 | "Observation" in the scans. |
| Proof 7.7 | A | | |
| Proof 7.9 | C | 260914 p2 | The scans write Σ_{i=0}^{α} φ(i); corrected to φ(p^i). Added: the case n = 1. |
| Proof 7.11 | S+ | 260914 p2 | Multiplicativity is called "obvious" in the scans; the argument and the case n = 1 were added. |
| Thm 7.13 (F multiplicative ⇒ f multiplicative) | C | 260914 p2 | The scans write "F(n) = Σ f(n)"; corrected to Σ f(d). |
| Proof 7.13 | C | 260914 p2 | The scans write the second sum over d₂ ∣ m; corrected to d₂ ∣ n. |

## 04-260918

Translated from Hungarian. Dropped: the φ = μ ∗ id example at the top of p1 (repeat of Ex 7.14) and the literature list on p3.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 8 | S | 260918 p1 | "p-adikus számok". |
| Def 8.1 (p-adic integer, Z_p) | S | 260918 p1 | Truncations α_k added. |
| Rem 8.2 (compatible truncations define a p-adic integer) | A | | |
| Def 8.3 (operations on Z_p via truncations) | I | | The scans compute sums through truncations (Ex 8.5) but never define the operations. |
| Ex 8.4 (−1 in Z_p) | S | 260918 p1 | Verification added. |
| Rem 8.6 (Z ⊂ Z_p) | S | 260918 p1 | Stated as "Z ⊂ Z_p"; the identification and injectivity were added. |
| Ex 8.7 (−3/2 in Z_3) | S | 260918 p1 | Verification via truncations added. |
| Rem 8.8 (a/b ∈ Z_p for p ∤ b) | S | 260918 p1 | "Observation" in the scans; the proof was added. |
| Prop 8.10 (Q_p is a field; units of Z_p; x = p^v u) | I | | The scans treat Q_p as a field of numbers without stating or proving this. The unit criterion appears in the scans of 260928 (Ex 15.3). |
| Proof 8.10 | A | | |
| Rem 8.11 (Q ⊂ Q_p) | S | 260918 p1 | Stated; the embedding was added. |
| Solution 8.12 | C | 260918 p1-2 | The scans write 3² − 2 + 14a₁ ≡ 0 (mod 49); corrected to 3² − 2 + 14·3a₁, which gives the scans' own next line 1 + 6a₁ ≡ 0. Both roots as in the scans. Added: existence of the roots via Hensel's lemma. |
| Rem 8.13 (solvable in Q ⇒ solvable in every Q_p) | S | 260918 p2 | Q_∞ = R made explicit. |
| Thm 8.14 (Hasse–Minkowski) | S | 260918 p2 | Stated without proof in the scans; marked cited. |
| Heading 9 | S | 260918 p2 | "p-adikus metrika". |
| Def 9.1 (absolute value, non-archimedean) | C | 260918 p2 | The scans give the axiom |xy| ≤ |x||y|; corrected to equality. |
| Rem 9.2 (induced metric) | S | 260918 p2 | The metric d(x, y) = |x − y| is in the scans; |1| = |−1| = 1 was added. |
| Prop 9.5 (properties of v_p) | S | 260918 p2 | Well-definedness added to the statement. |
| Proof 9.5 | A | | |
| Proof 9.7 | A | | |
| Rem 9.8 (p^n → 0) | S | 260918 p3 | Including the proof. |
| Def 9.9 (equivalent absolute values) | S | 260918 p3 | The trivial absolute value and the notation |·|_∞ were added. |
| Proof 9.10 | A | | |
| Rem 9.11 (recall: completion) | A | | |
| Thm 9.12 (Q_p is the completion of Q; Z_p is the unit ball) | S | 260918 p3 | The scans state that Q is not complete, that Q_p is its completion, and Z_p = {|x|_p ≤ 1}. The definition of v(x) on Q_p and parts 1)–4) were added. |
| Proof 9.12 | A | | |

## 05-260921

The scans give exercises 1–9 as bare solutions; the statements in the PDF are reconstructed from them. Dropped: exercise 6's (31/95), a repeat of Ex 5.5, and the doodles on p2.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 10 | A | | |
| Ex 10.1 (2 primitive root mod 11; 7x⁸ ≡ 5) | S | 260921 p1 | Statement reconstructed. |
| Solution 10.2 | C | 260921 p1 | The scans' intermediate congruence "90c ≡ −119 ≡ −8 (27)" is wrong; the correct one is 18c + 18 ≡ 0 (mod 27). The scans' conclusion c ≡ −1 (mod 3) and x ≡ −4 (mod 27) are correct. Added: roots mod 3 and uniqueness by Hensel's lemma. |
| Solution 10.3 | S+ | 260921 p1 | Added: why g^((p−1)/2) ≡ −1. |
| Solution 10.5 | C | 260921 p1 | (66/101): the scans write (101/11) = (4/11); 101 ≡ 2 (mod 11), so it is (2/11). (7!/83): the chain after (5/83)(7/83) contains wrong intermediate symbols; rewritten. Both final answers (no solution) are as in the scans. x² ≡ 30 (mod 77) as in the scans; the concluding sentence was added. |
| Ex 10.6 ((1234567/225), (589/1999)) | C | 260921 p2 | The scans' denominator reads 1899, but their next step uses 1999 = 3·589 + 232; computed for 1999. |
| Solution 10.6 | S | 260921 p2 | gcd check for 1234567 and 15 added. |
| Def 10.7 (totally multiplicative, Λ, λ, indicator) | I | | Used in exercises 7–9 of the scans without definition. |
| Solution 10.9 | C | 260921 p2 | The scans write log d · 𝟙{n = 1}; corrected to log n · 𝟙{n = 1}. |
| Heading 11 | S | 260921 p2 | Moved above the lemma that precedes it in the scans. |
| Lem 11.1 (|x + y| = max if |x| ≠ |y|) | C | 260921 p2 | The scans state it for "an ultrametric space K"; absolute values are needed, so corrected to a field with a non-archimedean absolute value. |
| Proof 11.1 | S+ | 260921 p2 | The scans assert |x + y| > |y| without reason; the step was replaced by the argument that the maximum must be |x + y|. |
| Def 11.2 (triangle, isosceles, collinear, right triangle) | I | | The scans use these notions in Q_p without definitions; for right triangles they invoke "the Pythagorean theorem", which has no meaning in Q_p. Collinear and right triangle are defined here by the distance equations the scans' proofs use. |
| Thm 11.3 (triangles in Q_p are isosceles) | S | 260921 p2 | "More precisely, the two longest sides are equal" added. |

## 06-260925

The boxed "III/2" on p1 is not content. Dropped: claim "lim pⁿ = 0" on p3 (repeat of Rem 9.8) and the notation "Σ aₙ < ∞" for convergence (p2).

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 12 | S | 260925 p1 | One word is missing in the scans ("Sequences and ___ in Q_p"); read as "series". |
| Proof 12.2 | C | 260925 p2 | The scans define Sₙ = Σ_{i=1}^n aᵢ for a series starting at n = 0; corrected to i = 0. Added: completeness of Q_p cited in the converse. |
| Proof 12.3 | A | | |
| Prose (balls, values of |·|_p) | S+ | 260925 p3 | "The p-adic metric induces a topology" is in the scans; ball notation and the value set of |·|_p were added. |
| Rem 13.1 (no ordering on Q_p) | S | 260925 p3 | "No ordering in Q_p" in the scans; made precise as "no ordering compatible with the field operations"; cited. |
| Thm 13.2 (open balls are closed and conversely) | S | 260925 p3 | The scans say "and vice versa"; "of positive radius" added. |
| Proof 13.2 | C | 260925 p3 | The scans let n be the smallest integer with r ≤ p^(−n); it must be the largest. The scans write the resulting set with < p^(−(n+1)); it is ≤. The proof that closed balls are open was added. |
| Proof 13.4 | A | | |
| Proof 13.5 | A | | |
| Def 14.1 (finite field, characteristic) | S+ | 260925 p4 | |F| < ∞ is in the scans; characteristic and the notation F_q were added. |
| Thm 14.2 (|F| = pⁿ, F^× cyclic, primitive element) | S | 260925 p4 | Added to the statement: char F is prime; a^q = a (used later in the scans). |
| Proof 14.2 | A | | |
| Thm 14.4 (Frobenius is a homomorphism) | C | 260925 p5 | The scans give the map as F_p → F_p while working in F_q; corrected to F_q → F_q. |
| Rem 14.5 (recall: F_q[x]/(f), F_q(α)) | A | | |
| Proof 14.6 | S+ | 260925 p5-6 | f(β^q) = 0 and the distinctness argument are in the scans. The scans conclude from "α is a root of x^(q^k) − x with k < m" directly; the subfield argument making this a contradiction was added. Also added: existence of a root. |
| Ex 14.8 (R ⊂ C) | C | 260925 p7 | The scans write C = R ∪ {i}; corrected to C = R(i). Definitions of degree and minimal polynomial were added. |

## 07-260928

Scan pages: p1 = IMG_0705, p2 = IMG_0706, p3 = IMG_0707. The scans give exercises 1–9 by number; statements are as in the scans where written, otherwise reconstructed. Dropped: doodles on p3.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 15 | A | | |
| Lem 15.1 (geometric series in Q_p) | I | | Used throughout exercise 1 of the scans without being stated. |
| Proof 15.1 | A | | |
| Rem 15.2 (v_p on Q_p) | A | | |
| Solution 15.3 | C | 260928 p1 | 2/3 and −1/6 as in the scans, including the congruence alternative; the expansion of 2/3 is finished via Ex 15.5 (the scans stop at 2 + 2² + ⋯). 1/6 in Q_3: the scans give 1/2 = 2 + 3 + 3³ + ⋯ and hence 1/6 = 2·3⁻¹ + 1 + 3² + ⋯; correct is 1/2 = 2 + 3 + 3² + 3³ + ⋯ and 1/6 = 2·3⁻¹ + 1 + 3 + 3² + ⋯. **Final answer changed.** Added: why Σ(−1)ⁿ diverges; why pairing terms is allowed. |
| Ex 15.5 (expansion of −a) | C | 260928 p1 | The scans write a = Σ_{n≥0} aₙpⁿ but then use a_(−m); corrected to Σ_{n≥−m}. a ≠ 0, a_(−m) ≠ 0 added. |
| Solution 15.5 | S+ | 260928 p1-2 | The first two digits are in the scans; "continue the process" was written out as an induction. |
| Solution 15.6 | S+ | 260928 p2 | The counting of multiples of p, p², … is in the scans; the exchange of summation was added. |
| Solution 15.7 | S+ | 260928 p2 | Added: that the limit satisfies x² = 6. |
| Solution 15.9 | C | 260928 p2 | The scans write n = v_p(z) ∈ Z⁺; v_p(z) can be negative, corrected to n ∈ Z. Added: the characterization Z_p^× = {v_p = 0}, which the exercise asks for but the scans do not write. |
| Solution 15.10 | S+ | 260928 p2 | p = ∞, the odd case with both symbols −1, "17 is a square in Q_2" and 6² ≡ 2 (mod 17) are in the scans. Added: no rational root; the other odd cases; the Hensel lifts; the proof that 17 is a square in Q_2. |
| Solution 15.11 | C | 260928 p3 | The scans: "x² + 1 is reducible over Q_2, x² + 1 = (x + 1)²"; that identity holds only mod 2, and x² + 1 is irreducible over Q_2. Replaced by x² + 1 over Q_5. The scans: "x⁴ + 1 is reducible over every Q_p"; false for p = 2, restricted to odd p. The scans write (x² − 1)² + 2x and −(−2)x; corrected to 2x² and −(−2)x². Added: irreducibility of x⁴ + 1 over Q; the lifts to Q_p. |
| Heading 16 | A | | |
| Lem 16.3 (trace and norm lie in F_q; formulas) | C | 260928 p3 | Membership in F_q is the scans' statement. The scans' formulas tr(α) = −m·a_(m−1) and N(α) = a₀^(m/r) are wrong; corrected to −(m/r)·a_(r−1) and (−1)^m·a₀^(m/r). |
| Proof 16.3 | C | 260928 p3 | The scans take α ∈ F_q; corrected to α ∈ F_(q^m). Product identity and coefficient comparison are in the scans; r ∣ m and the periodicity α^(q^r) = α were added. |

## 08-261002

Translated from Hungarian. Dropped as repeats: all of p1 (repeat of 260925: p ∣ binom(p, j), Frobenius map, roots of irreducibles, conjugates, automorphisms, examples) and the trace/norm definitions and lemma on p2 (repeat of 260928). The printed sheet visible under the notebook is not part of the notes.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 17 | S | 261002 p2 | "Testbővítések". |
| Heading 17.1 | A | | |
| Proof 17.2 | C | 261002 p2 | The scans take β ∈ F_q as a root of f; corrected to β ∈ F_(q^m). Added: f is the minimal polynomial of a generator of F_(q^m)^×; Φ fixes F_q; Φ^m = id; the powers are distinct; ψ = Φ^k follows from ψ(β). Homomorphism, injectivity and the computation ψ(f(β)) = f(ψ(β)) are in the scans. |
| Heading 17.2 | A | | |
| Rem 17.3 (recall: facts on field extensions) | A | | |
| Def 17.4 (separable polynomial) | C | 261002 p3 | The scans define separability for irreducible f only, then apply it to (x − 1)²(x − 2) and to arbitrary f; defined here for every nonzero f. |
| Proof 17.6 | S | 261002 p3 | Computing the gcd in the splitting field was added. |
| Lem 17.7 (irreducible f separable iff f′ ≠ 0) | A | | |
| Proof 17.7 | A | | |
| Thm 17.8 (finite fields: irreducible polynomials are separable) | C | 261002 p3 | The scans: "over a finite field every polynomial is separable"; false, e.g. (x + 1)² over F_2. Corrected to every irreducible polynomial. |
| Proof 17.8 | S+ | 261002 p3 | f′ = 0 ⇒ f ∈ F[x^p], a_i = b_i^p via Frobenius and f = (Σ b_i x^i)^p are in the scans. Added: why Frobenius is surjective; why f is a p-th power in F[x]. The scans reuse a_i for the coefficient of x^(ip); written c_j = a_(jp) here. |
| Proof 17.10 | S+ | 261002 p4 | Added: why m_(α,K) divides m_(α,F). |
| Ex 17.11 (F_p(t), x^p − t) | S | 261002 p4 | The scans state that x^p − t is irreducible. |
| Proof 17.11 (irreducibility of x^p − t) | A | | |
| Proof 17.12 | S+ | 261002 p4 | The computation is in the scans; "permutes" (injectivity on a finite set) was added. |
| Heading 17.3 | A | | |
| Thm 17.13 (n extensions of an embedding) | S | 261002 p4 | The scans state it for the target F̄; generalized to any algebraically closed L, which the induction needs. |
| Proof 17.13 | S+ | 261002 p4-5 | Induction on n, g = σ(m_α), ψ, r choices of β and n/r < n are in the scans. Added: g is separable; ψ is well defined; extensions correspond to roots of g; the final count. |
| Proof 17.14 | A | | |
| Heading 17.4 | A | | |
| Ex 17.16 (Q(∛2) not normal, Q(√2) normal) | S | 261002 p5 | Added: irreducibility of x³ − 2; every quadratic extension is normal. |
| Thm 17.17 (normal iff every F-monomorphism into C is an automorphism) | S | 261002 p5 | F ⊆ E ⊆ C made explicit. |
| Proof 17.17 | S+ | 261002 p5 | Both directions are in the scans. Added: τ(E) = E by dimension; existence of τ via Thm 17.13. |

## 09-261005

Dropped: the opening recall of the definition of a normal extension (repeats Def 17.15) and the literature reference.

| Block | Status | Scan | Note |
|---|---|---|---|
| Lem 17.18 (extension of an embedding into an algebraically closed field) | A | | Needed because the scans invoke Thm 17.17, stated for subfields of ℂ, for arbitrary fields. |
| Proof 17.18 | A | | |
| Prop 17.19 (normality criterion over an algebraically closed Ω) | A | | Same reason as Lem 17.18. |
| Proof 17.19 | A | | |
| Proof 17.20 | S+ | 261005 p1 | Both directions are in the scans. (⇒) Added: f_i splits because it is irreducible with a root in E. (⇐) The scans conclude "since previous theorem" (Thm 17.17, which concerns ℂ); the reference is replaced by Prop 17.19. |
| Heading 18 | S | 261005 p1 | "Galois theory". |
| Def 18.2 (Galois group) | S | 261005 p1 | Group axioms one clause, added. |
| Prop 18.3 (|Gal(E∣F)| = [E:F]) | S | 261005 p1 | A remark in the scans: n F-monomorphisms into the algebraic closure, all automorphisms by normality. |
| Proof 18.3 | S+ | 261005 p1 | Added: the bijection σ ↦ ι∘σ. |
| Ex 18.4 (Gal(Q(∛2)∣Q) trivial) | S | 261005 p1 | The scans state the result only. The argument (unique real cube root) and the comparison with Prop 18.3 are A. |
| Def 18.5 (fixed field) | C | 261005 p1 | The scans define F(H) for H normal in G; it is used for every subgroup, so defined for every H ≤ G. Subfield property added. |
| Ex 18.7 (C∣R Galois, group Z/2Z) | S | 261005 p1 | The justification is A. |
| Proof 18.8, part 1 | S+ | 261005 p1 | The scans: G ⊆ Gal(E∣F₀), E∣F₀ Galois, equal orders, degrees equal. Added: equality of the groups; tower law. |
| Proof 18.8, part 2 | S | 261005 p2 | Primitive element, f = ∏(x − σ(α)), invariance under τ, degree contradiction are all in the scans. |
| Solution 18.10 | C | 261005 p2 | The four automorphisms and the subgroups are in the scans. The scans list the fixed fields of {σ₁,σ₂}, {σ₁,σ₃}, {σ₁,σ₄} as Q(√5), Q(i), Q(i√5), and the figure labels the edge to Q(√5) with σ₂ and to Q(i) with σ₃. Since σ₂ negates √5 and σ₃ negates i, the first two are swapped: F({σ₁,σ₂}) = Q(i), F({σ₁,σ₃}) = Q(√5). Added: normality, degree 4, existence of all four maps, proof that the fixed fields are equal to these fields. |
| Figure (lattice of Q(i, √5)) | C | 261005 p2 | Redrawn; labels σ₂, σ₃ swapped as above. |
| Proof 18.11, part 1 | S+ | 261005 p2 | Both compositions are in the scans. Added: E∣F(H) and E∣K are Galois (Cor 17.21, Thm 17.10), needed to apply Thm 18.8. |
| Proof 18.11, part 2 | C | 261005 p2 | The scans write (σσ⁻¹)(x) = σ⁻¹(x) in the second line; corrected to (τσ⁻¹)(x) = σ⁻¹(x). Otherwise identical. |

## 10-261009

Tablet screenshots; p5 repeats the top of exercise 8 from p4. Dropped: "(From 3. session)" and the exam-date note "OKT 31 ZH". The exercise numbers 1–10 of the scans are Ex 19.1, 19.2, 19.4–19.6, 19.8–19.12.

| Block | Status | Scan | Note |
|---|---|---|---|
| Proof 18.12, part 1 | S | 261009 p1 | "Inherits normality and separability"; references added. |
| Proof 18.12, part 2 | S+ | 261009 p1 | The chain K∣F normal ⇔ σ(K) = K ∀σ ⇔ F(σHσ⁻¹) = F(H) ⇔ σHσ⁻¹ = H is in the scans, with "extended by normality". Added: the extension via Lem 17.18 and Prop 17.19. |
| Proof 18.12, part 3 | S+ | 261009 p1 | Homomorphism σ ↦ σ|_K, kernel H = Gal(E∣K), surjectivity, first isomorphism theorem are in the scans. Added: why σ|_K ∈ Gal(K∣F); the argument for surjectivity. |
| Heading 19 | A | | The scans: "Exercises". |
| Prose (setting q, m, L, K; c^q = c) | S | 261009 p2 | The scans write F = F_(q^m), K = F_q; renamed L, K. |
| Ex 19.1 (norm identities) | C | 261009 p2 | The scans state and conclude N(cα) = cN(α); the computation in the scans gives c·c^q⋯c^(q^(m−1)) = c^m. Corrected to c^m N(α). |
| Solution 19.1 | C | 261009 p2 | As above; otherwise identical. |
| Solution 19.2 | S | 261009 p2-3 | Frobenius additivity cited, added. |
| Def 19.3 (perfect field) | S | 261009 p3 | Part of exercise 3 in the scans. |
| Solution 19.4 | C | 261009 p3 | The scans take "f ∈ L[x]"; irreducibility is required (false for (x − 1)²) and is assumed in "f is the minimal polynomial of α₁ over L". Added: α₁ algebraic over K by transitivity; the common splitting field E′. |
| Solution 19.6 | C | 261009 p3 | Both computations and the factorization (x² + x − 1)(x² − x − 1) are in the scans. In the F₃ case the scans write a(b + d) = 0 for a(d − b) = 0; results unchanged. Added: absence of roots via x⁴ ∈ {0, 1} (the scans assert it); (2/5) = −1 in the case a = 0 (the scans: "no solution"); the check of the product; irreducibility of both quadratic factors. |
| Def 19.7 (purely inseparable polynomial) | C | 261009 p4 | The scans write "purely irreducible" in the definition and "purely inseparable" afterwards; the latter kept. The scans restrict to finite F. |
| Solution 19.8 | S+ | 261009 p4 | Induction is in the scans. Added: the case deg g = 0; the closing remark that for finite F one gets m_α = x − α. |
| Ex 19.9 (no irreducible poly over F₂ with an even number of terms) | C | 261009 p4 | False for x + 1; degree ≥ 2 added. |
| Solution 19.10, product | S+ | 261009 p4 | The scans: derivative −1 ⇒ multiplicity 1; f irreducible dividing x^(q^d) − x ⇒ deg f ∣ d (sketched). Added: both directions in full. |
| Solution 19.10, algorithm | C | 261009 p4-5 | The scans write x^(p^n) for x^(q^n), and step 2 as "if x^(p^(n/r)) ≡ x (mod f) for a prime r ∣ n, answer NO". That test is wrong: f = x(x² + x + 1)(x³ + x + 1) over F₂ passes it and is reducible. Replaced by gcd(f, x^(q^(n/r)) − x) ≠ 1. Correctness proof and counterexample are A. |
| Solution 19.11 | C | 261009 p5 | The example Q ⊆ Q(√2) ⊆ Q(⁴√2) and the four roots are in the scans. The scans' conclusion "Q(⁴√2)∣Q(√2) is not normal" contradicts their own previous line; corrected to Q(⁴√2)∣Q. Added: irreducibility of x⁴ − 2; degrees. |
| Solution 19.12 | C | 261009 p5 | The scans list the third root as ε²∛2; corrected to ε²∛3. Irreducibility of x³ − 3 added. |

## 11-261012

Dropped: crossed-out marginal drawings on both pages.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 20 | S | 261012 p1 | "Cyclotomic fields". |
| Def 20.1 (cyclotomic extension) | S | 261012 p1 | The assumption char F ∤ n appears two lines later in the scans. |
| Prop 20.2 (μ_n cyclic of order n; E = F(ζ_n)) | C | 261012 p1 | The scans: "the n-th roots of unity form a multiplicative group E*"; corrected to a cyclic subgroup μ_n of order n of E^×. Primitive root of order n, notation ζ_n, are in the scans. E = F(ζ_n) is A. |
| Proof 20.2 | A | | |
| Prop 20.4 (Gal(E∣F) ↪ U_n) | C | 261012 p1 | The scans: σ(ζ_n) = ζ_n^r with gcd(r, n) = 1, hence Gal(E∣F) ≅ U_n and [E:F] = φ(n), for arbitrary F. False in general (F = Q(i), n = 4: E = F, Gal trivial, φ(4) = 2). Corrected: the map is an injective homomorphism into U_n; Galois and [E:F] ∣ φ(n) for char F = 0 or F finite. Equality over Q is Thm 20.10. |
| Proof 20.4 | A | | |
| Prop 20.6 (x^n − 1 = ∏ Φ_d) | S | 261012 p1 | A "Claim" in the scans. |
| Proof 20.6 | S+ | 261012 p1 | Both inclusions of roots are in the scans. Added: both sides monic with simple roots; disjointness of the root sets. |
| Proof 20.8 | S | 261012 p1 | "Polynomial division algorithm" spelled out in one sentence. |
| Rem 20.9 (recall: Gauss's lemma) | I | | Used in the scans ("x^n − 1 = fg where f, g ∈ Z[x]", "∃h ∈ Z[x]") without statement. |
| Thm 20.10 (Φ_n irreducible) | S | 261012 p1 | Consequences [Q(ζ_n):Q] = φ(n), Gal ≅ U_n are A here; the scans state them in Prop 20.4. |
| Proof 20.10 | S+ | 261012 p1 | The scans' argument (f(ζ^p) = 0 for p ∤ n via reduction mod p, multiple root of x^n − 1; successive prime powers; degree comparison) is kept. Added: the argument is run for an arbitrary primitive root θ, which "successive prime powers" requires; gcd(x^n − 1, nx^(n−1)) = 1 over F_p. |
| Heading 21 | S | 261012 p2 | The scans: "Solvability by ruler and compass". |
| Def 21.1 (constructible point) | S | 261012 p2 | Made precise: P_(i−1) explicit; "constructible real number" is A. |
| Prose (fields K_i) | C | 261012 p2 | The scans: K₀ ⊆ K₁ ⊆ ⋯ ⊆ K_n = R; corrected to K_n ⊆ R. |
| Lem 21.2 (coordinates are roots of degree ≤ 2 polynomials over K_(i−1)) | S | 261012 p2 | The scans say "quadratic polynomials"; "degree at most 2" is equivalent. |
| Proof 21.2 | S+ | 261012 p2 | Equations of a line and a circle are in the scans. Added: the three intersection cases. |
| Prose (P₀ = {(0,0),(1,0)}, segment transfer) | S | 261012 p2 | P₀ and K₀ = Q are in the scans; the segment-transfer remark is A. |
| Proof 21.4 | S+ | 261012 p2 | Irreducibility of x³ − 2 added. |
| Proof 21.5 | C | 261012 p2 | The triple-angle computation and 8x³ − 6x − 1 are in the scans. The scans justify irreducibility by "f(x + 1) = 8x³ + 24x² + 18x + 1", which proves nothing (no Eisenstein prime). Replaced by the rational root test on y³ − 3y − 1, y = 2x. Constructibility of 60° added. |
| Thm 21.7 (Lindemann, cited) | S | 261012 p2 | Stated without proof in the scans. |

## 12-261016

Tablet screenshots. Dropped: the sketch of the angle 2π/n next to the n-gon proof; the Hungarian gloss "Feloldható csoport". The exercise numbers of the scans: 4/1 = Ex 22.2, 2 = Ex 22.3, 3 = Ex 22.4, 4 = Ex 22.6, 5 = Ex 22.7, 6 = Ex 22.9, 7* = Ex 22.10. Item 8* is the section on solvable groups.

| Block | Status | Scan | Note |
|---|---|---|---|
| Lem 21.8 (2^t + 1 prime ⇒ t power of 2) | S | 261016 p1 | Not stated as a lemma in the scans; the two cases are written below "Let 2^t + 1 be a prime". |
| Proof 21.8 | S+ | 261016 p1 | Both congruences are in the scans. Added: the conclusions (t odd ⇒ t = 1; r = 1). |
| Def 21.10 (constructible regular n-gon) | A | | |
| Thm 21.11 (regular n-gon) | C | 261016 p1 | The scans: "constructible iff the odd prime divisors of n are distinct Fermat primes". False as stated (n = 9). Corrected to n = 2^k p₁⋯p_r with pairwise distinct Fermat primes, which is what the scans' proof derives (α_i = 1). |
| Proof 21.11 | C | 261016 p1 | Necessity as in the scans: (i sin)² ∈ Q(cos), degree of ε_n over Q(cos) is 1 or 2, φ(n) = 2^k, α_i = 1, p_i − 1 = 2^(β_i). Typos corrected: n = p₁^(α₁) + ⋯ + p_r^(α_r) → product. Added: the tower-law step; reference to Lem 21.8. Sufficiency is not proved in the scans. |
| Thm 21.12 (Gauss, cited) | A | | Sufficiency, implicit in the scans' "if and only if". |
| Heading 22 | A | | |
| Rem 22.1 (recall: Eisenstein) | A | | Used below to justify irreducibility claims that the scans assert. |
| Solution 22.2 | C | 261016 p1-2 | x⁴ − 2 irreducible, |G| = 8, σ(⁴√2) = i⁴√2, its powers, τ⁻¹στ = σ³, G ≅ D₄ are in the scans. Corrections: the factorization (x + ⁴√2)(x − ⁴√2)(x − ⁴√2)(x + ⁴√2) lacks the factors x ∓ i⁴√2; the scans give τ two incompatible values (τ(⁴√2) = −i⁴√2 and τ(⁴√2) = i⁴√2), so τ is fixed as complex conjugation; the element list ⟨σ, σ², σ³, 1, τ, στ, σ²τ², στ³⟩ is replaced by {1, σ, σ², σ³, τ, στ, σ²τ, σ³τ}. Added: degree 8, existence of σ and τ, distinctness of the elements, the relation checked on generators. |
| Solution 22.3 | S+ | 261016 p2 | Minimal polynomial, σ(√2) = −√2, σ² ≠ id, G ≅ Z₄ are in the scans. Added: Eisenstein; β ∈ Q(α) via αβ = √2 (the scans only assert "normal"); existence of σ. |
| Solution 22.4, x³ + 2 | C | 261016 p2 | The scans list x₁ = ∛2 (root of x³ − 2); corrected to −∛2. The scans write |G| = 3 and then |S₃| = 6 = |G|; corrected to |G| = 6. Added: irreducibility, degree 6, the injection into S₃. |
| Solution 22.4, x⁴ − 7x² + 10 | S+ | 261016 p2-3 | Roots, splitting field of degree 4, σ, τ, στ of order 2, Klein group are in the scans. Added: √5 ∉ Q(√2). |
| Def 22.5 (Galois group of a polynomial) | I | | Used in the scans' exercises 3 and 4. |
| Solution 22.6 | C | 261016 p3 | The scans write the roots as α_i − c_i; corrected to α_i − c. Otherwise identical. |
| Solution 22.7 | S+ | 261016 p3 | f′ = −1, splitting field, separable ⇒ Galois, F_p ⊆ F(⟨σ⟩), |F(⟨σ⟩)| ≤ p, G = ⟨σ⟩ are in the scans. Added: why F is the root set; the appeal to the fundamental theorem. |
| Rem 22.8 (recall: constructible angles) | A | | |
| Solution 22.9 | S+ | 261016 p4 | 72°, 12°, 3°, 3k° and the reduction to 1° and 20° are in the scans. Added: the arithmetic for 3k + 1 and 3k + 2. |
| Ex 22.10 (isosceles triangle) | S | 261016 p4 | Statement not recorded in the scans (marked as missing in the document). |
| Solution 22.10 | C | 261016 p4 | The derivation of x³ − ax² + x + a (r = 1) is in the scans. The scans conclude "f is irreducible over Q, deg b = 3" for arbitrary a; false (a = 10/3 gives the root 2). Shown for a = 5 instead: rational root test and location of the roots are A. |
| Heading 23 | S | 261016 p4 | "Solvable groups". |
| Rem 23.1 (recall: commutator subgroup) | I | | Used in the definition of the derived series. |
| Def 23.2 (derived series, solvable) | S | 261016 p4 | The scans add "smallest" k; dropped, since it does not affect the definition. |
| Prop 23.4 (solvable iff abelian factors) | S | 261016 p4 | Stated without proof in the scans. |
| Proof 23.4 | B | | |
| Prop 23.5 (G × H solvable) | S | 261016 p4 | Stated without proof. |
| Proof 23.5 | B | | |
| Prop 23.6 (finite: cyclic factors) | S | 261016 p4 | Stated without proof. |
| Proof 23.6 | B | | |
| Def 23.7 (alternating group, simple group) | S | 261016 p4 | Definition of "simple" is A. |
| Thm 23.8 (A_n simple for n ≥ 5, cited) | C | 261016 p4 | The scans gloss "simple" as "has no nontrivial subgroup"; false (A₅ has subgroups of order 2, 3, 5, …). Corrected to normal subgroups. |
| Thm 23.9 (S_n solvable iff n ≤ 4) | S | 261016 p4 | Stated without proof. |
| Proof 23.9 | B | | |

## 13-261019

Dropped: crossed-out marginal drawings on both pages.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 24 | A | | |
| Prose (fixed algebraic closure Ω) | A | | |
| Lem 24.6 (Dedekind) | I | | The scans use "1, σ, …, σ^(n−1) are linearly independent over F" without statement. |
| Proof 24.6 | B | | |
| Proof 24.7, part 1 | S+ | 261019 p1 | a = 0, the n distinct roots, "x^n − a separable, thus F∣K Galois", the homomorphism Gal → Z_n, not necessarily surjective, are in the scans. The fact that a splitting field of a separable polynomial is Galois is marked as cited (proved in the notes only for char 0). |
| Proof 24.7, part 2 | S | 261019 p1 | Lagrange resolvent, Dedekind, σ(ρ) = ξ⁻¹ρ, ρ^n ∈ K, F = K(ρ) are in the scans. Computation of σ(ρ) written out. |
| Def 24.9 (compositum, normal closure) | S | 261019 p1 | The compositum is defined inside Lemma (1) in the scans; normal closure is used there without definition (I). |
| Lem 24.10 (compositum and normal closure of root extensions) | S | 261019 p1 | Part 1 in the scans: "if F and E are radical extensions of K, then FE∣F and FE∣E are radical". True; generalized here to E∣K a root extension and F arbitrary, which the proof of part 2 needs. |
| Proof 24.10 | S+ | 261019 p1 | (1) E = K(ⁿ√a) ⇒ FE = F(ⁿ√a) and (2) "apply (1) multiple times" are in the scans. (3) The scans argue finiteness and that L is "the completion of these root extensions", i.e. the compositum of the conjugates of F; made precise. |
| Proof 24.11, (⇒) | C | 261019 p2 | The scans write K_(i+1) = K_i(^(m_i)√a_i) with a_i ∈ K; corrected to a_i ∈ K_i. The rest is in the scans: m = lcm, E₀ = K(ξ_m), normal closure L as join of conjugates, tower L_j, G_j = Gal(L∣L_j), abelian factors, Gal(F∣K) ≅ Gal(L∣K)/Gal(L∣F) "also solvable". Added: e_j ∣ m for the conjugate towers; normality of L_(j+1)∣L_j; quotients of solvable groups are solvable. |
| Proof 24.11, (⇐) | C | 261019 p2 | The scans write Gal(K_i∣K_(i−1)) ≅ G₀/G_(i−1); read as G_(i−1)/G_i. The rest (E_i = E₀K_i, Gal(E_i∣E_(i−1)) a subgroup of Gal(K_i∣K_(i−1)), cyclic, radical by Kummer) is in the scans. Added: why E_i∣E_(i−1) is Galois and the restriction is injective; d_i-th roots of unity in E_(i−1). |
| Rem 24.12 (recall: Cauchy) | I | | Used in the example. |
| Lem 24.13 (p-cycle and transposition generate S_p) | S | 261019 p2 | A "Recall" in the scans, without proof. |
| Proof 24.13 | B | | |
| Solution 24.14 | C | 261019 p2 | Eisenstein, separability, G ≤ S₅, 5 ∣ |G|, Cauchy, 5-cycle, f″ = 20x³ ⇒ at most 3 real roots, (4 5) ∈ G, G = S₅ are in the scans. Corrections: f(3) = 180 → 189; the scans conclude "at most 3 real roots" from the table, which shows at least 3; corrected to exactly 3. "Mean value theorem" kept as Rolle's theorem. Added: complex conjugation maps E onto E. |

## 14-261026

Dropped: the note "No p-adics on midterm"; p3 (duplicate photograph of 261019 p1). Exercise statements 1–6 are taken from the printed problem sheet (scans/14-261026-sheet.png). The scans' midterm exercise 3 (Q(⁴√2)∣Q is not normal: x⁴ − 2 irreducible, roots ±⁴√2, ±i⁴√2, i ∉ Q(⁴√2)) is dropped as a repeat; its content is in Solution 19.11. For exam selection it counts as lecture content of this session.

| Block | Status | Scan | Note |
|---|---|---|---|
| Solution 24.15 | S+ | 261026 p1 | f′ = (x² − 2)(5x² + 4), sign table, three real and two conjugate roots, σ(a₄) = a₅, 5 ∣ |G|, 5-cycle, G ≅ S₅ = ⟨(12345), (45)⟩, A₅ simple are in the scans. Added: Eisenstein; Rolle; exact values in the table (the scans give signs at −3 and 3); complex conjugation lies in G; references to Lem 24.13 and Thm 24.11. |
| Heading 25 | S | 261026 p1 | The scans: "Midterm". |
| Solution 25.1 | S+ | 261026 p1 | x ≡ 3 (mod 5), f′(3) ≢ 0, x = 5t + 3, the binomial expansion 90t + 20, t ≡ 2, x ≡ 13 are in the scans. Added: the table of residues mod 5; uniqueness via Hensel; the check f(13) = 76·25. |
| Solution 25.2 | S | 261026 p1 | Both cases and the four CRT combinations are in the scans. Added: references to Thm 4.6 and Prop 4.3 1). |
| Solution 25.3 | C | 261026 p2 | The scans factor (x² − 3)(x² − 5) as (x − √3)(x + √3)(x − 5)(x + 5); corrected to (x − √5)(x + √5). The rest is in the scans. Added: √5 ∉ Q(√3); "all four possibilities occur" via |G| = 4. |
| Solution 25.4 | C | 261026 p2 | The scans compute 2⁴ ≡ 3 and 2⁸ ≡ −1 (mod 13) and conclude O₁₃(2) = 12. 2⁸ ≡ 9, and the conclusion does not follow from 2⁸; replaced by 2⁴ ≡ 3, 2⁶ ≡ −1 via Procedure 1.12. Result unchanged. The table entry at α = 12 is 1, not 0. The congruence is mod 13, not mod 12. The index computation and x ≡ 6 are in the scans. Added: 2 is the smallest (1 has order 1); reading ind₂3, ind₂8 from the table; the check. |
| Solution 25.5 | C | 261026 p2 | The scans write (−1)^(Σp_i)(−1)^(Σα_i) in the multiplicativity chain; read as (−1)^(Σq_j). The rest is in the scans. Added: the cases n = 1, m = 1; the reference to Thm 7.8; the case 2 ∣ n made explicit. |

## 15-261102

The preceding session (30 October) was the midterm; no lecture is missing. Rings, modules and algebras are used from the first line without definition. Dropped: marginal sketch ("Nix") next to the image/preimage proposition.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 26 | A | | |
| Heading 26.1 (Submodules) | A | | |
| Rem 26.1 (recall: ring, left module, algebra) | I | | Used without definition. |
| Prop 26.3 (submodule criterion) | C | 261102 p1 | A "Note" in the scans, without the condition N ≠ ∅; the empty set satisfies the scans' condition but is not a submodule. |
| Proof 26.3 | S | 261102 p1 | Both directions of 2) ⇔ 3) are in the scans; 1) ⇔ 2) added. |
| Rem 26.4 (subalgebra) | C | 261102 p1 | The scans: B is a subalgebra if x − y ∈ B and λx ∈ B; that is the submodule condition. Added: B ≠ ∅ and xy ∈ B. |
| Prop 26.6 (intersection of submodules) | S | 261102 p1 | "Nonempty family" added. |
| Def 26.7 (generated submodule) | C | 261102 p1 | The scans: "the intersection of all submodules of M is the smallest"; corrected to all submodules containing S. The scans restrict to S ≠ ∅; the definition here allows S = ∅, as the following proposition requires. |
| Def 26.8 (linear combination, LC(S)) | I | | The scans use LC(S) without definition. |
| Proof 26.9 | C | 261102 p1 | Structure as in the scans. The scans assert "we also know LC ⊆ ⟨S⟩" without reason; justified (every submodule containing S contains LC(S)). Added: LC(S) is a submodule. |
| Def 26.10 (sum of submodules) | S | 261102 p1 | Notation Σ M_i and A + B added. |
| Proof 26.11 | A | | |
| Ex 26.14 (Z-morphisms are group morphisms) | S | 261102 p1 | The argument is A. |
| Ex 26.15 (projections M^n → M are epimorphisms) | S | 261102 p1 | Componentwise structure on M^n is A. |
| Prop 26.19 (f^→(A ∩ f^←(B)) = f^→(A) ∩ B; f^←(B + f^→(A)) = f^←(B) + A) | S | 261102 p2 | Stated without proof. |
| Proof 26.19 | A | | |
| Cor 26.20 (f^→f^←(B) = B ∩ im f; f^←f^→(A) = A + ker f) | S | 261102 p2 | Stated without proof. |
| Proof 26.20 | A | | |
| Prop 26.21 (properties of morphisms 1–5) | S | 261102 p2 | Stated without proof. |
| Proof 26.21 | A | | |
| Heading 26.3 (Diagram completion) | S | 261102 p2 | The scans: "Diagram". |
| Thm 26.22 (h∘f = g exists iff f(x) = f(y) ⇒ g(x) = g(y)) | S | 261102 p2 | The scans have a dangling "(3)" after condition 2; dropped. The uniqueness clause for surjective f is A. |
| Proof 26.22 | A | | |
| Thm 26.23 (f∘h = g exists iff im g ⊆ im f) | S | 261102 p2 | The uniqueness clause for injective f is A. |
| Proof 26.23 | A | | |
| Proof 26.24 | A | | |
| Proof 26.25 | A | | |

## 16-261106

Tablet screenshots. The proof of the four lemma (2) breaks off at the end of p3.

| Block | Status | Scan | Note |
|---|---|---|---|
| Heading 27 | A | | |
| Ex 27.1 (no Z-morphism h with h∘(×2) = id) | S | 261106 p1 | Statement formulated from the scans' diagram. |
| Solution 27.1 | C | 261106 p1 | The scans write h(n) = h(2n) = n for h(2n) = n; conclusion h(1) = 1/2 unchanged. The remark that a map of sets exists is A. |
| Proof 27.2 | C | 261106 p1 | As in the scans, except: the scans justify uniqueness by "since g is surjective"; corrected to f. Added: "an R-morphism is injective iff its kernel is 0". |
| Thm 27.3 (factorization through a monomorphism) | C | 261106 p1-2 | The scans write "h is an R-monomorphism" among the hypotheses; corrected to f, as the proof uses. |
| Proof 27.3 | S | 261106 p2 | The scans' line "Similarly, Im g ⊆ Im f" is replaced by "with 2)". |
| Ex 27.5 (commutative ladder) | C | 261106 p2 | The scans: f′∘α = β∘γ; corrected to β∘f. The consequence g′∘f′∘α = γ∘g∘f is A. |
| Def 27.6 (sequence, exactness) | S | 261106 p2 | "Exact at every M_i with incoming and outgoing morphism" made explicit. |
| Thm 27.7 (mono / epi / iso via exactness) | S | 261106 p2 | Stated without proof. |
| Proof 27.7 | A | | |
| Ex 27.8 (0 → ker f → A → A/ker f → 0, 0 → im f → B → B/im f → 0) | S | 261106 p2 | The exactness check is A. |
| Thm 27.11 (universal property of the kernel) | S | 261106 p3 | Stated without proof. |
| Proof 27.11 | A | | |
| Proof 27.12, part 1 | C | 261106 p3 | The scans' last line: b′ = β(b) + β(f(a)) − β(b′ + f(a)); corrected to β(b + f(a)). The rest is in the scans. |
| Proof 27.12, part 2 | S+ | 261106 p3 | The scans break off after 0 = γ(c) = g′(β(b)). The rest (β(b) ∈ im f′, α surjective, β injective, c = g(f(a)) = 0) is A. |

## 17-261109

p3 is a separate photograph continuing the lecture. Notation: the scans write classes as {x}_E and the natural surjections as a_E, f_N, f_A; written here as [x]_E and π_E, π_N, π_A.

| Block | Status | Scan | Note |
|---|---|---|---|
| Thm 27.13 (five lemma) | C | 261109 p1 | The scans require only a commutative diagram; exact rows are needed (the four lemma assumes them). The scans' bottom row ends in E; corrected to E′. |
| Proof 27.13 | S | 261109 p1 | Added: which hypotheses each application of the four lemma uses. |
| Proof 27.14 | A | | |
| Heading 28 | S | 261109 p1 | "Quotient modules". |
| Prose (notation x ≡ y (E), [x]_E, M/E, π_E) | C | 261109 p1 | A "Def" in the scans that also calls π_E an R-epimorphism before M/E has a module structure; that claim is moved after Thm 28.1. |
| Proof 28.1, (1) ⇒ (2) | A | | The scans prove (1) ⇔ (2) by the factorization diagrams only. |
| Proof 28.1, (2) ⇒ (1) | S+ | 261109 p1 | Diagrams with f, g, f′, g′, Thm 26.22, uniqueness by right cancellation are in the scans. Added: the module axioms on M/E. |
| Proof 28.1, (2) ⇒ (3) | S+ | 261109 p1 | Added: 0 ∈ [0]_E; λx ≡ 0 written out. |
| Def 28.2 (quotient module) | C | 261109 p2 | The scans: "E an equivalence relation"; corrected to compatible. |
| Rem 28.4 (M/N, cosets x + N, ker π_N = N) | S | 261109 p2 | A "Note" in the scans; ker π_N = N is A. |
| Thm 28.5 (correspondence theorem) | S | 261109 p2 | The scans state the bijection from submodules of M/N to submodules of M containing N; written here in the direction of the proof, with the inverse. |
| Proof 28.5 | C | 261109 p2 | As in the scans, except: "the set of all such submodules of A" → of M containing N; the conclusion "φ is an isomorphism" → inclusion-preserving bijection. |
| Lem 28.7 (induced morphism f_*) | C | 261109 p2 | Part (a) in the scans: "f is injective ⇔ A = f^←(B)"; corrected to f_*. |
| Proof 28.7 | C | 261109 p2 | The scans invoke "the theorem of sets and maps"; that gives only a map, so the module version Thm 27.2 is cited. The kernel and image computations are in the scans. Added: in (a), the final step via Thm 28.5; in (b), the equivalence spelled out. |
| Thm 28.8 (first isomorphism theorem) | S | 261109 p3 | The scans state "a unique R-morphism λ" and prove in the next lines that λ is injective and surjective; the statement here says isomorphism. |
| Proof 28.8 | S+ | 261109 p3 | Lem 28.7 with A = ker f, B = 0, λ surjective, ker f = f^←(B) ⇒ injective are in the scans. Added: N/0 ≅ N; why (b) applies. |

## 18-261113

| Block | Status | Scan | Note |
|---|---|---|---|
| Proof 28.9 | S+ | 261113 p1-2 | Monomorphism step: the scans state π_P←(N/P) = N; the derivation via Corollary 26.20 was added. |
| Proof 28.10 | A | | The scans give the statement only. |
| Heading 29 | S | 261113 p2 | "Modulusok tenzorszorzata". |
| Prose, start of §29 | S+ | 261113 p2 | Motivation (bilinear maps as linear maps) is in the scans. The standing assumption "R commutative" is C: the scans make no assumption, but without it the tensor product is not an R-module. |
| Heading 29.1 | A | | |
| Def 29.1 (bilinear map, Bil, Hom) | I | | Bil_R and Hom_R appear on 261113 p2 without definition. |
| Ex 29.2 | S+ | 261113 p2 | f, x⊗y in RR^4 and f~(z) = z_1 + z_4 are in the scans. The numerical check for x = (2,3), y = (4,5) and the closing sentence were added; the scans name these vectors but do not compute. |
| Thm 29.4 (universal property), statement | S | 261113 p2-3 | Including uniqueness of (T, g) up to isomorphism. |
| Proof 29.4, existence | S+ | 261113 p3 | F, D (all four generator types), T = F/D, bilinearity of g, extension f-bar, f' are in the scans. Added: elements of T written as sums; the scans' well-definedness argument (x⊗y = x'⊗y' gives (x,y) − (x',y') ∈ D, so f-bar agrees) is stated for arbitrary classes u + D. |
| Proof 29.6 | A | | The derivation of 0⊗y = 0 and the expansion in generators. |
| Ex 29.7 | S+ | 261113 p4 | The computation 2⊗[1]_2 = 0 in Z⊗Z/2Z and the claim 2⊗[1]_2 ≠ 0 in 2Z⊗Z/2Z are in the scans. The reason for the claim and the closing sentence on inclusions were added. |
| Heading 29.2 | S | 261113 p4 | "Szabad modulusok". |
| Def 29.8 (basis, free, rank) | S | 261113 p4, 261116 p1 | Wording from the 261116 repeat. |
| Rem 29.9 (rank well defined) | A | | Cited. |
| Ex 29.10 (R as a module over itself is free) | S+ | 261113 p4 | The scans state it; the one-line reason was added. |
| Thm 29.11 (vector spaces have bases) | S | 261113 p4 | Stated in the scans without proof; marked cited. |

## 19-261116

Dropped as repeats of 18-261113: the opening remark (tensor rules, generators), the Z⊗Z/2Z example, the definitions of basis, free module and rank.

| Block | Status | Scan | Note |
|---|---|---|---|
| Proof 29.14 | S+ | 261116 p1 | Added: φ_g is an R-morphism. Corrected "f ∈ M" to "f ∈ F_S". |
| Heading 29.3 | A | | |
| Proof 29.15 | C | 261116 p1 | The scans give the codomain of f as M⊗N; it is N⊗M. Added: bilinearity of f, and h'∘f' = id via generators. |
| Proof 29.16 | A | | The scans give the statement only. |
| Proof 29.17 | C | 261116 p2 | The scans give φ: M×N → M'×N'; it is M'⊗N'. |
| Cor 29.18 (composition) | C | 261116 p2 | The scans state (f⊗g)(f'⊗g') = (f'f)⊗(g'g) and write g: N → N; corrected to (f'⊗g')∘(f⊗g) = (f'∘f)⊗(g'∘g) and g: N → N'. |
| Proof 29.19 | A | | |
| Def 29.21 (direct sum) | I | | ⊕ is used on 261116 p2 without definition. |
| Proof 29.22 | A | | The scans give the statement only. |
| Proof 29.23 | C | 261116 p2 | The scans write "f is surjective/injective"; it is f'. |
| Solution 29.24 | S+ | 261116 p2 | The scans compute [1]_2⊗[2]_3 = 0 only. The general argument x⊗y = 0 and the conclusion were added. |
| Ex 29.25 (Z⊗Q) | S | 261116 p2 | Posed in the scans. |
| Solution 29.25 | A | | Left open in the scans. |

## 20-261120

Dropped: the first line "ℤ ⊗_ℤ ℚ = {0}" (p1). It is false (Ex 29.25 gives ℤ ⊗ ℚ ≅ ℚ) and has no context on the page. Also dropped: a crossed-out first attempt at the ℚ ⊗ ℚ computation (p1).

| Block | Status | Scan | Note |
|---|---|---|---|
| Solution 29.26 | S+ | 261120 p1 | Added: how u is chosen; y/u read as [q/u]; the generator argument for the conclusion. |
| Solution 29.27 | S+ | 261120 p1 | Main chain and the side remark 1 = 3·5 − 2·7 are in the scans. Added: the reason 2m = 7m and the conclusion "= {0}", which the scans leave unwritten. |
| Solution 29.28 | S+ | 261120 p1-2 | Computation, β, and ℚ ⊗ ℚ ≅ ℚ are in the scans. Added: why β' is injective and surjective. |
| Heading 29.4 | S | 261120 p2 | "Tenzorszorzat és egzaktság". |
| Proof 29.30 | S+ | 261120 p2-3 | Every step is in the scans. Corrected: the composition order, written (1⊗f)∘(1⊗g) = 1⊗(fg); it is (1⊗g)∘(1⊗f) = 1⊗(g∘f). Added: π obtained from Lemma 28.7 and Thm 28.8; why injectivity of π suffices; that ψ is defined on all of M × N''; the bilinearity check of ψ, which the scans call "trivial". |
| Heading 30 | A | | |
| Def 30.3 (split exact sequence) | S | 261120 p4 | Stated inside the theorem in the scans ("felhasad, azaz B ≅ A ⊕ P"). |
| Lem 30.4 (quotient of a free module) | S | 261120 p4 | Used in the scans as a fact. |
| Proof 30.4 | A | | |
| Proof 30.5, 1 ⇒ 2 | S+ | 261120 p4 | The section h with g∘h = id_P is in the scans. The splitting B ≅ A ⊕ P is only asserted there; the proof via θ and Cor 27.14 was added. |

## 21-261123

Dropped: the triangle sketch next to the S_3 example (p1).

| Block | Status | Scan | Note |
|---|---|---|---|
| Thm 30.7 (Baer's criterion) | S | 261123 p1 | Stated without proof in the scans; marked cited. Corrected: "ideal" to "left ideal". |
| Def 30.8 (divisible) | C | 261123 p1 | The scans require divisibility by every element of R. Only 0 is divisible by 0, so this is corrected to every nonzero element. |
| Ex 30.9 (ℚ divisible) | S+ | 261123 p1 | Reason added. |
| Proof 30.11 | S+ | 261123 p1 | Added: the case a = 0. |
| Heading 31 | S | 261123 p1 | "Intro to representation theory". |
| Prose, start of §31 (GL(V)) | S+ | 261123 p1 | Added: GL(V) is a group; the matrix identification. |
| Ex 31.2 (trivial representation) | S | 261123 p1 | The name "trivial" was added. |
| Ex 31.3 (S_3) | S+ | 261123 p1 | All six matrices are in the scans and verified correct with right-to-left composition. The composition convention and the sample check were added. |
| Ex 31.4 (C_p over F_p) | S+ | 261123 p1 | Well-definedness and the homomorphism check were added. |
| Def 31.5 (group algebra) | S+ | 261123 p1 | Added: coefficients zero for all but finitely many g (needed for infinite G). |
| Ex 31.6 (ℚS_3) | S+ | 261123 p2 | Identity and sample elements are in the scans. The product computation is A: the scans announce it without recording it. |
| Proof 31.7 | S+ | 261123 p2 | Both constructions are in the scans. Added: the module axioms, the R-module structure via r ↦ r·1, and the inverse ρ(g⁻¹). |
| Def 31.8 (simple module) | C | 261123 p2 | Added: M ≠ 0. |
| Def 31.9 (invariant subspace, irreducible) | S+ | 261123 p2 | Invariant subspace is in the scans (stated after Maschke's theorem; moved before it). "Irreducible" is used in the scans but not defined; its definition is I. |
| Rem 31.10 (irreducible ⇔ simple) | S+ | 261123 p2 | First sentence added. |
| Lem 31.11 (projection splitting) | A | | Used implicitly in the scans ("⇒ V = W ⊕ ker π'"). |
| Proof 31.11 | A | | |
| Proof 31.12 | S+ | 261123 p2 | π', π'(w) = w, V = W ⊕ ker π', the G-morphism computation and invariance of ker π' are in the scans. Added: existence of π (cited basis extension); im π' ⊆ W; the reindexing g = hg'. |
