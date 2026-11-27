# How far a Lean integer reaches

Christopher Daniel Pang and Hearthline · 26 November 2026

Chris asked what happens when a prime fills the hardware word, whether the distinction can change a mathematical answer, and whether a finite word entered the released RH claim. We used the construction’s pinned Lean 4.33.1 and stock Mathlib. All computations ran on Dust. The core numerical experiment also ran under local Linux with Lean 4.36.0. Both runtimes returned the same bit lengths, remainders and fixed-word values. Cloud charges were zero.

## A prime and a composite in the same 64-bit slot

$$
 p=17,\qquad c=2^{64}+17=18{,}446{,}744{,}073{,}709{,}551{,}633
   =3\cdot6{,}148{,}914{,}691{,}236{,}517{,}211.
$$

As natural numbers the first is prime and the second is composite. Both give 17 on conversion to a `UInt64`. The Lean file proves both claims and the equality of the narrowed readings. A separate ordinary type-check asks whether a proof of primality of 17 fits the larger natural-number proposition. Lean reports a type mismatch. [Runnable Lean example](IntegerWidth.lean) · [Arithmetic and negative control](check_pal_integer_width.py)

The largest prime that fits in an unsigned 64-bit word is $2^{64}-59=18{,}446{,}744{,}073{,}709{,}551{,}557$. The Python replay proves its primality recursively from factorizations of $n-1$ and multiplicative order. It exhibits proper divisors for every larger odd candidate in the word and accounts for every even candidate. The 58 integers immediately above that prime exhaust the rest of the word.

Adding one to the all-ones 64-bit word gives zero. Adding one to the same numerical value as a `Nat` gives $2^{64}$. Natural numbers and signed `Int` values use arbitrary-precision arithmetic. Growing an integer consumes real storage, allocator space and, for some operations, additional working memory. With exactly $B$ bytes for a packed unsigned binary payload, the greatest encoded integer is $2^{8B}-1$. A particular runtime also has limits on allocation and indexing. For example, GMP documents signed integer fields for the count of machine words in an `mpz`; with a 32-bit count and 64-bit words the representation has a ceiling of approximately 16 GiB of magnitude digits per object. The available capacity for an operation depends on the build and its working storage. The runs below establish measured sizes on Dust. [Lean natural-number representation](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/) · [Fixed-precision arithmetic](https://lean-lang.org/doc/reference/latest/Basic-Types/Fixed-Precision-Integers/) · [GMP representation](https://gmplib.org/manual/Integer-Internals.html) · [GMP maintainer’s 64-bit size calculation](https://gmplib.org/list-archives/gmp-discuss/2012-March/004948.html)

## A dense integer with more than two billion bits

The exponent arrives at run time. Lean constructs $n=(1\ll e)-1$ as a `Nat`, converts it to `Int`, and reads arithmetic remainders from the expanded value. The byte counts are the minimum packed binary payload, with allocation overhead excluded.

| Integer | Bits | Packed bytes | Remainder mod 17 | Last nine decimal digits |
|---|---:|---:|---:|---:|
| $P=2^{136279841}-1$ | 136,279,841 | 17,034,981 | 1 | 486871551 |
| $K=2^{17\cdot136279841}-1$ | 2,316,757,297 | 289,594,663 | 1 | 548764671 |

$P$ is the GIMPS prime with 41,024,320 decimal digits. Its primality is from the published GIMPS computation. Our test concerns holding the integer and doing arithmetic on it. The larger value consumes about 276.18 MiB of magnitude data and is composite. Set $x=2^{17}$. Then $K=x^{136279841}-1$ is divisible by $x-1=131071$. Lean also returned zero for that remainder. [GIMPS discovery and primality work](https://www.mersenne.org/primes/?press=M136279841) · [Machine outputs and source pins](2026-11-26-pal-integer-width.json)

## Putting the carry back

In the base-5 squaring ladder for the released example, the first intermediate exceeding a 64-bit word is
$$
5^{32}=1262\cdot2^{64}+3273344365508751233 .
$$
The low word alone records $3273344365508751233$. The high word carries 1262 units of $2^{64}$. Keeping both parts restores the exact product.

The independent Python implementation stores magnitude digits in base $2^{32}$ and carries after every product. Each inner sum fits within $2^{64}-1$, because $(2^{32}-1)^2+2(2^{32}-1)=2^{64}-1$. It recovers every full-width order-test residue for the actual released prime and agrees with Python's separate modular exponentiation. The replay performs 1,604 multi-digit products with 234,169 nonzero partial carries. Deliberately dropping all parts above 64 bits instead gives $5625304617532669953$ at the final exponent, where the original calculation gives 1. These are two specified arithmetic models. The experiment measures the consequence of removing the carry. [Explicit digit arithmetic](check_pal_lucas_carries.py) · [General reconstruction identity](IntegerWidth.lean)

## Going past any fixed limit on paper

For every $k\ge0$, $(2^{64})^{k+1}+17$ retains the 64-bit word 17 and is divisible by 3. Its first term is 1 modulo 3. Taking $k=2^{94}-1$ gives $2^{2^{100}}+17$. Its expanded magnitude needs $2^{97}+1$ bytes. The same finite argument covers it without computing that expansion.

We can also name a particular **prime** beyond that storage scale. Put $m=2^{2^{100}}$ and let $p$ be the least prime factor of $m!+1$. Every prime at most $m$ divides $m!$ and therefore leaves remainder one in $m!+1$. Hence $p>m$. Lean checked the general least-factor argument and its specialization. This identifies the prime by an exact rule and proves a lower bound on its size. Its digits were not calculated.

There is a separate generalization to any finite collection of positive moduli. Let $M$ be their product and $p$ any prime. The larger composite $p(M+1)$ agrees with $p$ modulo every divisor of $M$. If the low word must read 17 even for an arbitrarily large **prime**, apply Dirichlet’s theorem to the class of 17 modulo $2^w$. The two are coprime at every width $w$. Choose such a prime above the requested bound and use $p(2^w+1)$ for the larger composite. Both have the same low $w$ bits. The proof file uses stock Mathlib's theorem on primes in arithmetic progressions for precisely this last existence assertion. [Mathlib source at the release pin](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/PrimesInAP.lean)

## What the released RH deduction reads

At release commit `40e56bab026552e089d7afcfeff08d2defb9c005`, the headline theorem has type `RiemannHypothesis` and uses `rhOfAll`. That declaration passes the all-character nonvanishing theorem to `Formalism.VW.rh_of_every`. Given an arbitrary complex $s$ strictly to the right of the critical line, the latter specializes to the trivial character of modulus 1 and rewrites its L-function as the Riemann zeta function. The preceding reflection argument treats the opposite half-plane. Stock Mathlib's target quantifies over complex $s$ and uses ordinary `Nat` for the index of a trivial zero. These quantifiers impose no word-size cutoff. [Headline theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean#L4) · [Route into nonvanishing](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Supplements/Kernels/MainTheorems.lean#L9) · [Actual modulus-one specialization](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/GammaFactorNonvanishing/CritLine.lean#L29) · [Stock target](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L185)

There is a direct arithmetic test inside this same release. Its declaration `prime_large` is a 385-bit natural number with a Lucas certificate. An independent integer replay gives $5^{p-1}\bmod p=1$ and the necessary order checks on the full modulus. Its low 64 bits give $586678051033346049=3\cdot195559350344448683$. Repeating the base-5 operation on that narrowed value gives $497633511686448868$, so even the first test changes. Its low 32 bits happen to be the prime $1029468161$, as direct trial division also checks. During our own first attempt at the composite subgoal, an automatic decision procedure reached the kernel recursion limit and produced an error. Giving the explicit factor 3 discharges the same claim in the final file. The evidence at the release example is the full-width order calculation. [Pinned 116-digit declaration](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/LocalRingCardinality/SpanPowerMembership/Primes.lean#L518) · [Full integer certificate](check_release_prime_large.py)

We also tried the reverse error across all 972 candidates of our earlier norm reconstruction. Full-width arithmetic finds primes at parameters 363, 663 and 972. Retaining only the low 64 bits gives **45 prime readings and zero overlap** with the three actual primes. At parameter 26 the full integer is divisible by 3, while its residue $2813010139532958721$ is prime. Every composite verdict is witnessed by a failed Fermat test, and all 45 positive narrowed verdicts have recursively checked order certificates. The release supplies the example at 972. The 972-candidate sweep is our audit construction. [Prior norm classification](../proofs/the-three-prime-norms-in-the-released-example.md) · [All finite order witnesses](word_prime_order_witnesses.json)

**The first width that gets every one of those 972 classifications right is 385 bits.** At every smaller positive width except 14, at least one of the three genuine primes either reads as 1 or fails Fermat’s test at base 2. Width 14 keeps the three but calls 365 candidates prime. For instance parameter 2 is composite by the factor 3 and has prime low word 15361. At width 385 every candidate fits in full. This is an exact cutoff for this audit family, proved by covering every width from 1 through 385.

We checked the pinned Git tree against the paths examined in the source search, including filenames with non-ASCII characters. All **175,187** Lean files under `src/` were covered. The search found zero explicit occurrences of the listed fixed-width integer type names and conversions, machine-size integer names and conversions, `BitVec`, `Float` and `Float32`. The receipt gives the exact pattern. This is a statement about the release’s application source. Alias expansion, transitive Mathlib code and the correctness of the underlying runtime are separate questions. We found no evidence linking the demonstrated word collision to the published RH inference. [Source scan and coverage control](check_pal_integer_width.py)

From the `pal-rh` Lake project with the pinned dependencies built, run `lake env lean --run ../receipt-archives/IntegerWidth.lean 136279841` or use exponent `2316757297` for the larger case. The Python replayer accepts `--project` for both Lean runs and the rejection control, and `--release` for a local checkout of the published source.
