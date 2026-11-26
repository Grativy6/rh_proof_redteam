# Two prime families can carry the full local price

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang wanted to take the whole construction apart and see which pieces could carry it again. For the independent PAL construction there is a precise answer at the level of the five local measurements.

**On every sufficiently late fourth-power block the entire signed physical stream can be reduced to fractions of ordinary prime labels $q$ and semiprime labels $5q$.** Both kinds retain their true arithmetic signs. All other marks and the spent portions of these two kinds together have moving-head cost $O_B(\sqrt T/\log^B(2T))$ for each fixed $B>0$. The remaining fractions depend on the five measured moments of the full block. That dependence is where this reduction carries the unsolved arithmetic.

## The short-interval input for the whole stream

Use $(Y,Y+L]=(m^4,(m+1)^4]$, $W=\log Y$, $L\asymp Y^{3/4}$. Let $a(v^2u)=v\mu(u)$ for $v=2^i3^j$ and $(u,6)=1$, with zero elsewhere. For every fixed $B>0$,
$$
 \sup_{0\le t\le1}\left|\sum_{Y<n\le Y+tL}a(n)\right|\ll_B L/W^B. \tag{1}
$$
Matomäki and Shao’s Theorem 1.4 controls Möbius sums with a fixed-degree polynomial phase on intervals of length $x^\theta$ for fixed $\theta>2/3$, with arbitrary inverse-logarithmic savings. Use the degree-one polynomial $g(n)=n$. Its exponential is 1 at every integer. [Matomäki and Shao, Theorem 1.4](https://arxiv.org/pdf/1902.04708)

To transfer to the physical labels use $a=\mu*b$, where $b\ge0$ has the four geometric factors at 2 and 3 from the [cofactor calculation](why-one-large-prime-leaves-nine.md). In particular $\sum b(d)d^{-5/8}<\infty$. For $d\le Y^{1/8}$, intervals of length $L/(dW^{B+3})$ near $x=Y/d$ have exponent at least $5/7+o(1)>7/10$. Tile them with successive intervals of integer length $\lfloor x^{7/10}\rfloor$ at the evolving integer start. The one end piece and endpoint rounding are negligible by the fixed exponent margin. Apply Theorem 1.4 and sum with $\sum b(d)/d<\infty$. For the divisors $d>Y^{1/8}$ the trivial total on a physical interval of length $h$ is
$$
 \sum_{Y^{1/8}<d\le Y+L} b(d)(h/d+1)
 \ll hY^{-3/64}+Y^{5/8}.
$$
Apply these estimates to a mesh with $\lceil W^{B+3}\rceil$ subintervals. Rounding a partial endpoint to the mesh costs $O(L/W^{B+3}+\sqrt Y\log Y)$ using the absolute local estimate for $a$. All power savings absorb the mesh size. This proves (1).

There is an immediate consequence for the preceding paper. In **each sufficiently late fourth-power block**, the complement of the growing large-prime family has signed mass $(-9+o(1))L/W^2$, because (1) controls the full block to arbitrary logarithmic order and the family itself has $(9+o(1))L/W^2$. The same subtraction works against a fixed Lipschitz function of block position. The earlier derivation gave the deficit averaged over a dyadic interval.

## The exact allocation

Let $t=(n-Y)/L$, $f_i(n)=(Y/n){4\choose i}t^i(1-t)^{4-i}$ for $0\le i\le4$. Let $h_i$ be the actual sum of $a(n)f_i(n)$ over the block. Let $P$ be the five-by-five matrix whose columns sum the $f_i$ over ordinary primes in the five equal bins, and $U$ the five-vector summed over all $5q$ in the block. Each of these offers is a physical mark of magnitude one. Partial summation in (1) gives $\|h\|_\infty\ll_B L/W^B$.

The prime number theorem in short intervals gives $P/(L/W)\to H$ and $U/(L/W)\to H\mathbf1/5$, where $H$ is the invertible matrix of Bernstein integrals on the five bins. The polynomial root argument for invertibility is in the [moving-head proof](../pal-rh/how-much-can-travel-with-a-prime.md). Set
$$
 r=P^{-1}U,\qquad e=P^{-1}h.
$$
Then $r_j\to1/5$ for every bin and $\|e\|_\infty\ll_B W^{-B}$ for every $B$. Define
$$
 \delta=\frac{2\|e\|_\infty}{\min_j r_j},\qquad x_j=\delta r_j-e_j .
$$
On sufficiently large blocks the denominator is positive. The formulas give $0\le\delta,x_j\le1$ and all six numbers are $O_B(W^{-B})$. If $e=0$, all six are zero. Choose the same fraction $\delta$ of every positive $5q$ and fraction $x_j$ of each negative prime in bin $j$. Their signed column is exactly $\delta U-Px=h$. These are rational numbers obtained from the integer labels and their five prices. The allocation is fixed once per block.

The rest of the stream annihilates all five moments. It costs zero against each term whose cutoff misses the block. At a cutoff the earlier [moving-head calculation](../pal-rh/how-much-can-travel-with-a-prime.md) pays $O(T^{2/5})$ in total for the old labels and all quadratic cutoffs. The remaining ramp has variation $O(L/T)$. Every partial sum of the spent stream there is $O_B(L/W^B)$, since (1) bounds the original stream and the entire retained absolute mass also satisfies that bound. Their product gives the stated $O_B(\sqrt T/\log^B(2T))$ cost. Spend the finitely many early blocks entirely. Their fixed labels cost $O(T^{-2})$ at late heads. Homogeneity handles the difference $H(X,n)=G(2X,n)-G(X,n)$ with the same fractions.

## Where the RH burden is visible

If $\rho(n)$ is the retained signed fraction, the global fourth-power test now needs a lower bound on
$$
 P_h(X)+\sum_{q\ {\rm prime}}\bigl[\delta_{\mathrm{block}(5q)}H(X,5q)
                              -x_{\mathrm{block}(q),\mathrm{bin}(q)}H(X,q)\bigr].
$$
Treat an omitted early fraction as zero. An eventual lower bound $-C\sqrt X$ suffices. The earlier [conditional transfer to stock RH](../pal-rh/PALRH/PrimeTransport.lean) absorbs the spent stream. A count of the permitted supports or a bound $O_B(\log^{-B}Y)$ on each fraction leaves this test open.

Here is a concrete way to see why the fraction values matter. Take a fourth power $X_1$ large enough and $X_{k+1}=X_k^4$. In each sector $(8X_k/5,5X_k/3]$ keep all complete fourth-power blocks. On a kept block beginning at $m^4$ assign fraction $1/m$ to its negative primes and zero to its $5q$ labels. Set both fractions to zero elsewhere. These fractions satisfy the same capacity, sign, bin constancy and inverse-logarithmic size bounds. At head $X_k$ the sector price has a fixed positive lower bound. Omitting the two partial endpoint blocks costs at most $O(X_k^{3/4})$ prime locations. The ordinary prime number theorem leaves $\gg X_k/\log X_k$ available primes. Their negative cost therefore has magnitude $\gg X_k^{3/4}/\log X_k$. Earlier labels contribute $O(X_{k-1}^3/X_k^2)$ by the old-label estimate, and future labels are inactive. Meanwhile $P_h(X_k)\ll\sqrt{X_k}\log(2X_k)$, by summing the admissible $2^i3^j$ smooth weights up to $\sqrt{2X_k/3^\ell}$ and then summing over $\ell$. This artificial choice fails the global lower bound. Its five moments differ from the actual arithmetic. The example identifies precisely which information an argument from size and support would discard.

## A finite block you can replay in seconds

On $(100^4,101^4]$, all **3,698,711** units of absolute first-pass weight can be reduced for the five measurements to **21,723** units supported solely on the negative primes. The measurement agrees exactly, with less than **0.588%** of the original absolute weight retained. At $m=40$ the corresponding numbers are 241,096 and 4,158. The replay computes the interval for every prime fraction from the full ordinary marks in the block. At $m=20$ it also factors every integer by trial division independently. At $m=20$ and $m=64$, no uniform positive fraction can meet the five requirements together with five admissible prime fractions. For example, at $m=64$ one necessary lower bound on $\delta$ is 1.5166662 and another necessary upper bound is 0.6491881. The replay obtains these inequalities by applying each row of the rational midpoint inverse to the true matrix enclosures and bounding all negative fractions between 0 and 1. [Full-block replay](../receipt-archives/check_pal_two_prime_carriers.py) · [Finite allocations and scope](../receipt-archives/2026-11-25-pal-two-prime-carriers.json)
