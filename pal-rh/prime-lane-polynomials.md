# Prime lane polynomials and the turn they cannot see

Christopher Daniel Pang and Hearthline · 26 November 2026

Write $e(t)=\exp(2\pi it)$. For a finite increasing list of positive labels $d_i\le M$, let $t(d)=\lceil\alpha\log d\rceil$, $\alpha=1/\log(1+1/x)$, and let $S_{i-1}=\sum_{k<i}t(d_k)$. On the actual boards these labels are all primes in $(x,M]$ and $x=4\sqrt M(j+1)^2$. The lane that receives the first tick of arrival $i$ is $S_{i-1}\bmod x$. An extra fixed turn $\eta$ per arrival gives the polynomial
$$
 P_N(\eta)=\sum_{i=1}^{N} e\big(S_{i-1}/x+(i-1)\eta\big).
$$

**Theorem.** For the full retained-prime list with $N=\pi(M)-\pi(x)$, the supremum over $\eta$ of $|P_N(\eta)|$ is between $\sqrt N$ and $C\sqrt N$ with one absolute constant on all sufficiently large boards. The upper bound holds for every prefix of that list. For any fixed nonzero integer harmonic $h$, replacing $S_{i-1}/x$ by $h S_{i-1}/x$ gives the analogous result with a constant depending on $h$. There is no RH assumption.

## The cost away from a whole turn

It suffices to take $h>0$ by conjugation and reversing $\eta$. The increment is $\lambda_i=h\,t(d_i)/x+\eta$ and is nondecreasing. On a run with $k+\delta\le\lambda_i\le k+1-\delta$ for one integer $k$ and $0<\delta\le1/4$, write $z_i=e(h S_{i-1}/x+(i-1)\eta)$ and $g(t)=1/(e(t)-1)$. Then $z_i=g(\lambda_i)(z_{i+1}-z_i)$. Summation by parts bounds the run sum by twice the maximum of $|g|$ plus the total variation of $g(\lambda_i)$. Here
$$
 g(t)=-\tfrac12-\tfrac i2\cot(\pi t).
$$
Its real part is constant. The imaginary part is monotone within the strip, so its total variation is at most $\cot(\pi\delta)$. Since $\sin(\pi\delta)\ge2\delta$, the whole run costs at most $1/\delta$. This is the elementary Kuzmin–Landau first-difference argument. It applies to the actual discrete increments. [Summation-by-parts identity and norm inequality in Lean](PALRH/PhaseBound.lean) · [Arias de Reyna on the classical lemma](https://arxiv.org/abs/2002.05982)

## Counting the labels near a whole turn

On a dyadic piece $Y<d_i\le2Y$, put $\mu(d)=(h\alpha/x)\log d+\eta$. We have $1\le\alpha/x\le1+1/x$ and $0\le\lambda_i-\mu(d_i)<h/x$. There are at most $5h$ relevant integer boundaries, and at most $5h$ complementary unit strips, including a truncated last piece. For each integer boundary the exceptional labels lie in an interval of length at most $4Y\delta/h+2Y/x$, since $\mu'(d)\ge h/(2Y)$. For arbitrary distinct integer labels the exceptional count is at most $5h+20Y\delta+10hY/x$. Summing the nonresonant cost gives another $5h/\delta$. If $Y\ge16h$ take $\delta=\sqrt{h/Y}$, otherwise count all positions in the piece. Summing powers of two gives the explicit upper bound
$$
 1+100\sqrt{hM}+20hM/x .
$$
An arbitrary list here generates its own cumulative states. All estimates are uniform in $\eta$.

For primes, use $\delta=\sqrt{h\log Y/Y}$ on sufficiently large pieces with $h$ fixed. With $x\ge\sqrt M$, each of the exceptional intervals can be enlarged to length $O_h(\sqrt{Y\log Y})$. The Brun–Titchmarsh bound $\pi(A+B)-\pi(A)\le2B/\log B$ for $A>0,B>1$ reduces the exceptional count to $O_h(\sqrt{Y/\log Y})$. The run sums have the same bound. The sum over all dyadic pieces ending by $M$ is $O_h(\sqrt{M/\log M})$. For example pieces below $\sqrt M$ cost $O_h(M^{1/4})$, and the remaining ones have logarithms comparable to $\log M$. The ordinary prime number theorem gives $N\sim M/\log M$ on our boards. Finally, orthogonality of $e((i-1)\eta)$ for distinct $i$ gives $\int_0^1|P_N(\eta)|^2\,d\eta=N$. This proves the lower bound for the supremum as well. [Montgomery and Vaughan, Theorem 2 and equation (1.12)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf)

The integer-label root bound cannot be improved to $o(\sqrt M)$ uniformly over input lists on these boards. With $\beta=\alpha/x$, take $D=\lfloor\exp(\lfloor\beta\log M\rfloor/\beta)\rfloor$ and the last $\lfloor\sqrt M/20\rfloor$ consecutive integers ending at $D$. Eventually $D\ge M/e-1$ and the labels lie above $x$. Their increments are all within $11\lfloor\sqrt M/20\rfloor/M+1/x$ of the same integer, by the mean value theorem. Across the whole list the total possible drift is less than $1/12$ of a turn for large $M$. Its arrows therefore have real parts greater than one half when started at zero. This control uses consecutive integers. The prime-list supremum already has its own lower bound by orthogonality.

## The unrounded primorial consequence

For a fixed numeration base $b>1$, let $Q_n=\prod_{k=1}^n p_k$. The same argument without tick rounding gives, uniformly in real $\lambda$,
$$
 \sup_{0\le c<d\le1}\left|\frac1N\#\{n\le N:
       \{\log_b Q_n+\lambda n\}\in[c,d)\}-(d-c)\right|\ll_b N^{-1/3}.
$$
Massé and Schneider proved ordinary Benford behavior of primorials. Their Theorem 3.4 gives a discrepancy bound of order $(\log\log N)^{1/2}/(\log N)^{1/9}$. The displayed power rate is a stronger bound than that stated estimate. This comparison concerns that identified paper. Priority for the power rate has not been established here. [Massé and Schneider, Theorem 3.4](https://www.impan.pl/shop/en/publication/transaction/download/product/82868)

For the proof, the consecutive phase increments at harmonic $h$ have the form $(h/\log b)\log p+\eta$, with a possible shift of one prime index and a constant rotation of the sum. For $1\le h\le N^{1/3}$, treat labels below $2h^2$ trivially at a cost $O(h^2)$. In a remaining dyadic piece $Y\ge h^2$ take $\delta=\sqrt{h\log Y/Y}$; it is at most $1/4$ for all sufficiently large such $Y$. There are $O_b(h)$ resonant intervals. Enlarge each to length comparable, with constants depending only on $b$, to $\sqrt{Y\log Y/h}$. Its logarithm is bounded below by a fixed positive multiple of $\log Y$ because $h\le\sqrt Y$. Brun–Titchmarsh bounds all these primes together by $O_b(\sqrt{hY/\log Y})$. The $O_b(h)$ nonresonant strips give the same cost by the first-difference estimate. Constants are independent of $h,N,\eta$. Summing through $p_{N+1}$ and using $p_{N+1}/\log p_{N+1}\asymp N$ gives
$$
 \left|\sum_{n\le N}e(h\log_b Q_n+n\eta)\right|
 \ll_b h^2+\sqrt{hN}\ll_b\sqrt{hN}.
$$
The last inequality uses $h^3\le N$. In the Erdős–Turán inequality take the harmonic cutoff $\lfloor N^{1/3}\rfloor$ and $\eta=h\lambda$. Its two error terms are $O(N^{-1/3})$ and $O_b(N^{-1/2}\sum_{h\le N^{1/3}}h^{-1/2})$. This proves the claim. [Erdős–Turán formulation in the primorial paper, Lemma 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/82868)

## What the actual fast and slow readings distinguish

Adding $x$ to the tick count of each true prime adds $i-1$ whole turns before arrival $i$. Every coefficient of $P_N$ is identical for the altered and original streams. This includes every choice of $\eta$. At sixteen sites their unshifted sum is $3+i$ in both cases.

| Observed cut | Original arrivals | Largest prefix magnitude at $\eta=0$ | One tested rational $\eta$ | Enclosure of terminal magnitude at that $\eta$ |
|---:|---:|---:|---|---|
| 65,536 | 3,724 | $83.10858\ldots$ | $7537/8192$ | 89.7706 to 89.7930 |
| 1,048,576 | 68,394 | $333.67969\ldots$ | $36715/262144$ | 499.7640 to 500.1740 |
| 16,777,216 | 1,013,709 | $1363.78322\ldots$ | $765853/2097152$ | 2402.2963 to 2408.3731 |

A floating FFT selected the displayed offsets. The reported enclosures come from an independent rational calculation. At zero offset it uses directed complex multiplication from exact quadrant anchors. At each selected offset it rounds the exact rational phase to the nearest of $2^{20}$ grid points and includes the full possible phasor error $\pi N/2^{20}$. The sample is a lower witness for the true supremum. [All intervals, cut witnesses and altered stream](../receipt-archives/2026-11-26-pal-lane-phase.json)

To read the actual excess define the slower integer phase $b_m=\sum_{d\le m}t_d-x(m-x)_+$ with period $n=x^2$, and let $A=x\lfloor x/13\rfloor$. At each physical cut test whether its ordinary nonnegative residue $r_m=b_m\bmod n$ satisfies $r_m\le A$ or $r_m\ge n-A$. One cannot swap a whole turn without encountering the forbidden interval. Indeed $p\le16^j=2^{4j}$ gives $t_p\le4jx$ since $(x+1)^x\ge2x^x$, and $2(4j+1)\le x$ on every board. The jump of $b_m$ consequently has absolute value at most $n/2$. Neighboring translates of $[-A,A]$ are separated by $n-2A>n/2$. Starting at zero, induction keeps the same lift, and hence $|b_m|\le A$. Positive triangular reweighting gives the true one-sided budget and stock RH. Conversely the established RH bound $|b_m|\le cx^2$ with $c=(\log 2)^2/(2\pi)$ puts every true cut within the allowed arc, including the small initial boards. [Modular arithmetic and real step size](PALRH/SpokeArc.lean) · [Independent fixed statement](checks/slow-arc/ArcChallenge.lean)

On the deliberately altered stream the fast lanes are identical at every arrival, yet the first forbidden slow reading occurs at primes 46,771, 289,469 and 1,675,873 on the three tested boards respectively. Each uses one extra complete fast column at every retained prime. The true stream passes over these finite horizons. The uniform slow-arc condition is the open RH-scale obligation. Its proof requires information about the unwrapped arithmetic that is absent from even the full fast polynomial.
