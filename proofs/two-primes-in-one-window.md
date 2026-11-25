# Two primes break one window budget

**Corpus and derivation.** This result was developed in Christopher Daniel Pang’s PAL research program with Hearthline. Pang asked to keep the actual scale fixed while combining arithmetic contributions that fit separately. Hearthline wrote the mathematical argument. [PAL v2.4-M, Mathematical Realization Atlas](../corpus/PAL_v2.4-M_Mathematical_Realization_Atlas.docx) · [Cluster-Layer Entropy Focus v1.0](../corpus/CLEF_cluster_layer_entropy_focus_v1_0.pdf)

**Proof inputs and the release.** The release supplies the window budget and its eventual quantifiers. The two-prime example is a pointwise failure at the stated scale.

[Proof collection](README.md) · [Dated receipt and supporting checks](../receipt-archives/2026-11-24-two-primes-break-one-window-budget.md) · [Contribution record](PROVENANCE.md)

**24 November 2026.** Taking `rhOfAll` apart puts two earlier arithmetic witnesses in the same sum. For the fixed legal choice $\epsilon=1/55$, there is a scale at which **each individual lower bound fits the released budget and their sum exceeds it**. The pointwise field predicate `VAt` fails, including at every possible scale in a specified outer interval and for every permitted page there. The published `VWinAt` includes a later threshold. Its prime-size condition has enough room for both witnesses together. [Four-character reconstruction](../receipt-archives/2026-11-24-taking-rhofall-apart-at-the-four-characters.md) · [Pointwise predicate and quantifiers](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L39-L49) · [Exact rational certificate](../receipt-archives/check_rhofall_reassembly.py)

## The small calculation

Take $x=2^{55}$. The budget in `VAt` is
$$B(x)=\sqrt{\exp(x^{1/55})}=\exp(1).$$
The host contains the real conductor-256 cyclotomic field. A strict class of order 577 at twist 296 survives there, since restriction from $\mathbb Q$ followed by corestriction multiplies the original class by a power of two. The twist is inside the cutoff $t=\lfloor x^{401}\rfloor$. Take the singleton prime set $\{577\}$. If all the required lengths are finite, its weighted sum is at least $\log577>6>\exp(1)$. An infinite required length violates the separate finiteness clause. Both permitted page numbers, 118 and 119, fail this pointwise test. [Order and local conditions](../receipt-archives/2026-11-24-the-577-class-on-paper.md) · [Transport to these hosts](../receipt-archives/2026-11-24-a-class-inside-the-zeta-windows.md) · [Field and page check](../receipt-archives/2026-11-24-two-dyadic-pages-behind-one-prime-sum.md) · [Exact finite sums](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L12-L17)

## The test which needs both primes

Fix the trivial character. Write $v=x^{401}$ and $t=\lfloor v\rfloor$. On the same $E_e=\mathbb Q(\zeta_{2^{e+2}})^+(\sqrt{-q},\sqrt{-d})$, for every $e\ge6$ the two known contributions force
$$D_2=(\log2)\lfloor t/2\rfloor,\qquad
D_{577}=(\log577)\left\lfloor\frac{t+279}{576}\right\rfloor.$$
At 2 there is at least one length unit at every positive odd twist. At 577 the same residual coefficient recurs at $296,872,\ldots,296+576k<t$. Its inertia at 577 has order 72, so the local invariants needed to introduce a spurious coboundary vanish. The old argument supplies one length unit at each of these twists. The release requires the inequality for **every finite set of primes**, including $\{2,577\}$. Thus $D_2+D_{577}\le B(x)$ is necessary. The two source groups use different coefficient primes and occupy distinct summands. [Dyadic class and two local witnesses](../receipt-archives/2026-11-24-dyadic-class-enters-late.md) · [Residual progression and its length](../receipt-archives/2026-11-24-a-class-inside-the-zeta-windows.md) · [Independent 577 computation](../receipt-archives/fixed-character-577/fourier_witness.py)

Put
$$z=117162393/200,\qquad X=z^{55}.$$
This scale lies between $2^{1053}$ and $2^{1054}$. At $x=X$ there are rational certificates for
$$0.349 < B(X)/X^{401}=\exp(z/2-22055\log z)<0.350.$$
To check the close comparison on paper, write $\log z=19\log2+\log(z/2^{19})$. For $a>1$ set $h=(a-1)/(a+1)$. The first 32 terms of $2\sum_{j\ge0}h^{2j+1}/(2j+1)$ give a lower bound for $\log a$, with remainder at most $2h^{65}/[65(1-h^2)]$. Apply it also to $1000/349$ and $20/7$ and compare logarithms. The replay performs these comparisons with rational numbers.

| Known contribution at $X$ | Fraction of $X^{401}$ |
| --- | ---: |
| $D_2$ | at most $\log2/2<0.347$ |
| $D_{577}$ | at most $(1/576+1/X^{401})\log577<0.013$ |
| $D_2+D_{577}$ | greater than $0.355-16/X^{401}$ |
| Released budget | between $0.349$ and $0.350$ |

Indeed $\log2/2+\log577/576>0.355$ using $\log2>0.69$ and $\log577>6$. The floors, including the floor in $t$, cost less than $2(\log2+\log577)<16$. At this scale the combined bound exceeds the budget even though each known contribution separately falls below it. Each entry in the first two rows concerns the **proved lower bound** from that prime. Either full group could be larger.

## Every candidate subwindow in this test fails

Take $Y_0=2^{40}$, $J=\log X/\log Y_0$, and either of the two certified pairs with $q=3$ at $Y_0$. Thus $J>2$ and $X^{1/J}=Y_0$ as required by the outer window test. Every $x\in[Y_0,X]$ has permitted pages $e\ge6$. Put $s=\log x$. The logarithm of the normalized budget is the convex function
$$\log(B(x)/x^{401})=\tfrac12\exp(s/55)-401s.$$
Its maximum on this interval occurs at an endpoint. At $Y_0$ the budget is less than 3 and $Y_0^{401}=2^{16040}$. At $X$ the ratio is less than $0.350$. Throughout the interval the known contributions exceed $0.355x^{401}-16>0.350x^{401}$, so `VAt` fails everywhere in it. This excludes every candidate $[Y,Y^2]$ with $X^{1/J}\le Y$ and $Y^2\le X$ for these outer parameters. The underlying class arguments also apply to any other primes with the stated arithmetic host conditions. The earlier dyadic-only calculation had already excluded $[2^{40},2^{1053}]$. [Certified input pairs](../receipt-archives/2026-11-24-prime-pair-readouts.md#two-actual-congruence-windows) · [Earlier excluded interval](../receipt-archives/2026-11-24-dyadic-class-enters-late.md) · [Actual subwindow requirement](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean#L41-L49)

## Unresolved

The released order is $\forall\epsilon,\ \forall$ eligible page functions, $\exists J,X_0,\ \forall X\ge X_0,\ldots$. The explicit $J,X$ above test an instance of its inner demand. To refute that eventual assertion with this approach would require one fixed $\epsilon$ and one admissible page function for which **every** proposed $J,X_0$ fails.

There is a concrete reason the pair of classes above does not suffice. On the selected late scales the producer requires $q>2X^{401}+1$. The prime window gives $\log q\le (X^{1/J})^{\epsilon/5}\le x^{\epsilon/5}$. For $X\ge2$ these imply $x^\epsilon/2\ge(\log q)^5/2>401\log X$, so $B(x)>X^{401}\ge x^{401}$. Meanwhile $D_2+D_{577}<t$ for $t\ge16$, by $\log2<0.70$, $\log577<7$, and $D_{577}\le(t/576+1)\log577$. This independently pays for both demonstrated lower bounds. The full sum over primes and twists on that same host still requires its own estimate. [Required prime size](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/bigpair.lean#L6-L22) · [Where the source imposes it](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean#L54-L75) · [Where the total is used](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean#L119-L129)
