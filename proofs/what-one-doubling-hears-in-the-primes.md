# What one doubling hears in the primes

Christopher Daniel Pang and Hearthline, 26 November 2026 (New York).

At the square **4**, look from 2 to 8. A weight rises linearly in logarithmic distance to its maximum at 4, then falls to zero at 8. The three primes strictly inside are 3, 5 and 7. There is also the square of 2.

| Reading at 4 | Value |
| --- | ---: |
| Smooth reference | 0.97056274… |
| Primes 3, 5 and 7 | 0.69368138… |
| Contribution of $4=2^2$ | $(\log2)^2/2=0.24022650\ldots$ |
| Full prime-power reading | 0.93390789… |

The all-powers reading is within $1/5$ of the reference. Removing the square leaves a shortfall of $0.27688\ldots$. Turning the inequality around leads somewhere different. **The assertion that the primes alone always stay below the reference on these square heads is equivalent to RH.** The unbounded inequality remains the intended theorem to earn.

## Where Dyson’s question enters

Montgomery’s first-person account dates the tea meeting to April 1972 and credits Chowla with making the introduction. [Montgomery’s recollection, §2.8](https://www.ams.org/notices/202107/rnoti-p1140.pdf)

Hugh Montgomery’s 1973 paper studied differences of the imaginary parts of zeta zeros. Its theorem assumes RH and determines a restricted Fourier range. Its full pair-correlation prediction is $1-(\sin(\pi u)/(\pi u))^2$. Dyson recognized the same two-point law for large complex Hermitian or unitary random matrices. His later quasicrystal proposal asks about reconstructing a real-line point distribution from frequency information at logarithms of primes and prime powers. These are different measurements. The prime-side formula below includes the pole and the contribution at infinity. [Montgomery, pp. 181–184](https://public.websites.umich.edu/~hlm/paircor1.pdf) · [Dyson, *Birds and Frogs*, pp. 214–215](https://wucj.lab.westlake.edu.cn/Others/Dyson_Birds_and_Frogs.pdf)

We can test the quasicrystal idea against our earlier object. The unsigned square-root zoom of our arithmetic marks is $\kappa\,dt+A\delta_z$. Its Fourier transform, with the $e^{-2\pi i t\xi}$ convention, is $\kappa\delta_0+A e^{-2\pi i z\xi}\,d\xi$. The continuous part in the original zoom is already visible. Dyson’s proposed discrete real-line pattern requires a different observation. This leads us to read the prime-power logs themselves and keep their amplitudes. [Classification of the original zoom](what-can-move-inside-a-square-root-window.md)

Take an exactly soluble example respecting conjugation and reflection about the critical line. Place two points at each of $1/2+i\gamma$ and $1/2-i\gamma$. In the second configuration split each double point into the pair with real parts $1/2-a$ and $1/2+a$. Every height, multiplicity of each height and difference of heights agrees. In this example we can ask precisely what the height-only view has missed.

Let one observing turn be $L=\log2$. Choose $\gamma=2\pi/L$ and $a=\log(9/8)/L$, strictly between zero and one half. Read each point $\rho$ as $e^{(\rho-1/2)u}$. At $u=0$ both configurations give 4. At $u=L$ their angular phases have returned to one. The centered response is still 4. The split response is
$$
 2(9/8+8/9)=145/36=4+1/36 .
$$
For a genuine finite positive real-frequency spectrum the energy of a difference of two observations is nonnegative. The two-by-two matrix here has diagonal 4 and off-diagonal $145/36$. On the difference vector $(1,-1)$ it gives **$-1/18$**. A doublet at the same height can be distinguished by the amplitude it carries over one doubling. These four points are a constructed comparison. [Exact Lean calculation](../pal-rh/PALRH/DysonOctave.lean)

One positive test on a large collection can still conceal the split. For instance an additional centered conjugate pair with angular frequency $\pi/L$ adds 2 to the diagonal and −2 to this off-diagonal. The measured pair now has positive energy in both directions at this turn. The arithmetic test below has a proof that addresses every possible off-line pole in the full response.

## The finite question at each square

Write $[y]_+=\max(0,y)$, $L=\log2$, and
$$
 w_x(n)=[L-|\log(n/x)|]_+,\qquad c=4(\sqrt2+1/\sqrt2-2).
$$
There are two readings. In $T(x)$ sum $(\log p)w_x(p^k)/\sqrt{p^k}$ over all prime powers $p^k$. In $P(x)$ keep just $k=1$. Both sums have support strictly between $x/2$ and $2x$. The continuous comparison for the full reading is the ordinary integral $\int_0^\infty w_x(t)t^{-1/2}\,dt=c\sqrt x$.

Each of the following statements is equivalent to stock RH **on paper**.

1. At every integer $j\ge2$, $\big|T(j^2)-cj\big|\le1/5$. Either one of its two inequalities also suffices.
2. At every integer $j\ge2$, $P(j^2)<cj$. There is no free constant in this primes-only upper test.

For a complex displacement $z$ from the critical line, integrating the triangular window gives
$$
 K(z)=\frac{e^{Lz}+e^{-Lz}-2}{z^2}
     =\frac{(e^{Lz}-1)^2}{e^{Lz}z^2},\qquad K(0)=L^2 .
$$
When $\Re z>0$, $|e^{Lz}|>1$, so the numerator cannot vanish. On the line itself $K(i\gamma)=(2\sin(L\gamma/2)/\gamma)^2\ge0$. The squared sine here comes from two copies of a box in log scale. Its algebraic role differs from the pair-spacing density in Montgomery’s paper.

The full prime-power reading at square 2663² is 1292.3477731… against a reference of 1292.3042996…. Prime squares supply 0.2383943…, and higher powers 0.0148736…. In the full scan through root 2663 the smallest and largest full-minus-reference readings were about −0.063145 and +0.075657. The prime-only *lower* test with the same fifth-unit allowance failed at 2,612 roots. The prime-only *upper* test passed throughout this finite scan. A second calculation at root 2663 recovered the log weights from the integer divisor-product identity and summed the 668,062 primes, 234 prime squares and 28 higher powers directly. [Directed arithmetic and controls](../receipt-archives/2026-11-26-pal-dyson-octave.json)

## Why the square makes a permanent difference

At head $j^2$ the prime-square part is
$$
 \sum_p\frac{\log p}{p}[L-2|\log(p/j)|]_+
 \ \longrightarrow\ \int_{-L/2}^{L/2}(L-2|u|)\,du
 =\frac{L^2}{2}.
$$
This follows from the ordinary prime number theorem by partial summation. The higher powers together tend to zero, since for $k\ge3$ there are only $O(x^{1/3}\log x)$ candidate bases and exponents up to $2x$. Thus removing all repetitions shifts the reading down by about **0.24023** even at arbitrarily large heads. That exceeds the entire allowable oscillation of the smoothed zero response under RH. At the very first square the single omitted copy of 2 already has precisely that limiting price. [Derivation, pole test, diagonal and explicit finite coverage](../pal-rh/the-dyson-response-and-prime-squares.md)

**Some shortfalls must return at arbitrarily large squares.** We proved unconditionally that the full reading falls more than 0.127 below its reference infinitely often, and that the primes-only reading falls more than 0.367 below infinitely often. The full reading also rises more than 0.07565 above the reference infinitely often. Under RH this follows by bringing finitely many zero phases back together on whole doublings and paying for the remaining frequencies. If RH fails, any finite one-sided ceiling or floor would contradict the pole test. [Sharp recurrence argument](../pal-rh/the-dyson-response-and-prime-squares.md#a-shortfall-that-must-recur-unconditionally)

The dyadic response is the product of two one-turn integrals. Lean derives its nonnegative energy on the critical line, its nonvanishing to the right, and the exact price of omitting 4. [Formal observation and first-square identity](../pal-rh/PALRH/DysonObservation.lean)

The return calculation and the complex analytic implication to the stock target are formalized. The latter takes, as its explicit premise, a holomorphic extension of the centered response agreeing with the ordinary prime-power Dirichlet series on its half-plane of absolute convergence. The derivation of that extension from the finite prime inequalities and the converse bounds are given on paper. [Independent analytic challenge](../pal-rh/checks/dyson-response/DysonChallenge.lean) · [Solution](../pal-rh/checks/dyson-response/DysonSolution.lean)

Pang brought the Dyson lead, the one-turn-per-doubling idea, RPL’s retained and discarded readings, and the instruction to try both orientations. Hearthline constructed the finite comparison, chose the log window and derived these arithmetic tests. Pair correlation, the explicit formula, the completed-zeta trace identity and prime-square bias have classical sources. No priority claim about an equivalent formulation is needed for this derivation. [Corpus contribution record](PROVENANCE.md)

## Unresolved

The remaining primes-only claim has a fixed direction and an explicit right-hand side. Does the weighted mass of the actual primes in $(j^2/2,2j^2)$ stay below $4(\sqrt2+1/\sqrt2-2)j$ for all $j\ge2$? A finite computation can settle a given $j$. The proof for every $j$ is open in this program.
