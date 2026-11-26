# The boundary of the signed factorial rows

Christopher Daniel Pang and Hearthline · 26 November 2026

## Exact before passing to a limit

Fix a positive integer $N$ and real values $f(1),\dots,f(N)$. Put
$$
G_m=\sum_{k\le N/m}\mu(k) f(mk),\qquad c_m=G_m-G_{m+1}
$$
with $G_m=0$ for $m>N$. Regrouping products and using $\sum_{d\mid n}\mu(d)=\mathbf1_{n=1}$ gives $\sum_{r\le N/d}G_{rd}=f(d)$ separately for each $1\le d\le N$. Telescoping yields
$$
\sum_{m=1}^N c_m\lfloor m/d\rfloor=f(d),\qquad
\sum_m mc_m=f(1),\qquad
\sum_m c_m\log(m!)=\sum_{d\le N}\Lambda(d)f(d).
$$
For the last equality use $\log(m!)=\sum_d\Lambda(d)\lfloor m/d\rfloor$. The triangular matrix of floor readings, taken from the largest $d$ downward, has unit diagonal. This determines the signed coefficients uniquely. The formal source also specializes the last identity directly to the actual prime-power reading at every square. [Finite identities](PALRH/FactorialReturn.lean)

Use $L=\log2$, $w(u)=(L-|u|)_+$ and $h(t)=t^{-1/2}w(\log t)$ on $t>0$. It vanishes outside $[1/2,2]$. Define $g(t)=\sum_{k\ge1}\mu(k)h(kt)$, a finite sum at each positive $t$. Möbius inversion gives $h(t)=\sum_{k\ge1}g(kt)$. For mesh size $M\ge2$ set
$$
c_{m,M}=g(m/M)-g((m+1)/M),\qquad
A_M(t)=\sum_{m\le 2M} c_{m,M}\left\lfloor\frac{m}{Mt}\right\rfloor .
$$
The finite result gives $A_M(d/M)=h(d/M)$ at every positive integer $d$. It also gives $\sum_m m c_{m,M}=h(1/M)=0$.

## What a finer mesh can resolve

The profile $h$ is globally Lipschitz with constant 4. On its support the derivative on each smooth piece has magnitude bounded by $2^{3/2}(1+L/2)<4$, and the endpoint values agree. If $z\ge y>0$, only $k\le2/y$ can contribute to $g(z)-g(y)$. Summing $4k(z-y)$ gives
$$
|g(z)-g(y)|\le16(z-y)/y^2 .
$$
Expanding each floor as a sum of indicators and telescoping gives $A_M(t)=\sum_{k\ge1}g(\lceil Mkt\rceil/M)$. Thus
$$
|h(t)-A_M(t)|\le\frac{16\zeta(2)}{Mt^2},\qquad
\sum_m |c_{m,M}|\le16\zeta(2)M .
$$
The zero first moment cancels all linear parts of the floors. Since each fractional part has magnitude at most one, $|A_M(t)|\le\sum|c_{m,M}|$ also holds arbitrarily close to zero. Both profiles vanish for $t>2$.

## The reading at an actual zero

For $\Re s>1$, integrating a floor term gives $\zeta(s)(m/M)^s/s$ by counting its levels. The bounded whole row then extends the identity to $\Re s>0$, with a removable singularity at 1 because $\sum m c_{m,M}=0$. At any zeta zero $\rho$ in that half-plane the row’s Mellin integral vanishes. The prescribed profile has transform
$$
\int_0^2 h(t)t^{s-1}\,dt=K(s-\tfrac12),\qquad
K(z)=\frac{e^{Lz}+e^{-Lz}-2}{z^2},\qquad K(0)=L^2 .
$$
At a critical zero $\rho=1/2+i\gamma$ this is $2(1-\cos(\gamma L))/\gamma^2$. Our independent enclosure below gives an actual $\gamma$ with $0.019333631<K(i\gamma)<0.019334024$.

Write $E_M=h-A_M$. For every Lipschitz $\varphi$ on $[0,2]$,
$$
\int_0^2 \varphi(t)E_M(t)t^{\rho-1}\,dt
=K(i\gamma)\varphi(0)+O\!\left(\operatorname{Lip}(\varphi)M^{-1/2}\right).
$$
Subtract $\varphi(0)$ and bound by $\operatorname{Lip}(\varphi)t$. On $(0,1/M)$ use $|E_M|\le \|h\|_\infty+16\zeta(2)M$ and integrate $t^{1/2}$. On $[1/M,2]$ use $16\zeta(2)/(Mt^2)$ and integrate $t^{-3/2}/M$. Both costs are $O(M^{-1/2})$. This is convergence against Lipschitz test functions to a point mass of size $K(i\gamma)$. For $\varphi=1$ the equality holds at every mesh. The assertion concerns this complex weighted integral, with no positivity or uniformly bounded variation of the error measures assumed.

The critical weighted absolute error is at least $K(i\gamma)$ on every mesh. Its portion on $[\eta,2]$ is at most $32\zeta(2)/(3M\eta^{3/2})$. Choose $\eta=C M^{-2/3}$ with fixed $C$ large enough to make this less than $K(i\gamma)/2$. For large $M$, $h$ vanishes below $\eta$, where the remaining contribution is at most $2\sqrt{\eta}\sum|c_{m,M}|$. Consequently $\sum|c_{m,M}|\gg M^{1/3}$ for every sufficiently large $M$.

The zeta multiplier of fractional-part rows is classical. For related natural approximants Báez-Duarte distinguished pointwise and norm convergence. Our grid, test class, rate, and the coefficient statement below specify which phenomenon occurs for this triangular profile. [Báez-Duarte, *Arithmetical Aspects*](https://arxiv.org/abs/math/0011254) · [Müntz transforms and general generators](https://arxiv.org/abs/math/0505453)

## Both signs survive at ordinary square heads

Define $B(x)=g(1/x)$. On $\Re s>1$ its Mellin integral over $x>0$, with measure $x^{-s-1}dx$, equals $K(s-\frac12)/\zeta(s)$ by absolute convergence and the Dirichlet series of $\mu$. The contribution from $x<1$ is entire since $B(x)=0$ for $x<1/2$.

At a simple zero $\rho=1/2+i\gamma$ the residue has magnitude $a=|K(i\gamma)/\zeta'(\rho)|$. We prove $\limsup B(x)/\sqrt x\ge a$ and $\liminf B(x)/\sqrt x\le-a$. Suppose, in either orientation, that $U\sqrt x\pm B(x)$ is eventually nonnegative with $0<U<a$. Its Mellin integral from a sufficiently large initial point has meromorphic continuation with no *real* singularities strictly to the right of $1/2$. The ordinary alternating series for zeta excludes any positive real zero there. A nonnegative tail has a singularity at its finite real abscissa of convergence. To see this, expand $x^v$ around a real convergence point using the nonnegative coefficients $(v\log x)^k/k!$. If regularity at the abscissa gave a Taylor disk extending to its left, monotone convergence would give a finite integral inside that disk to its left. Hence the positive integral converges for all real $\sigma>1/2$. Initial compact intervals affect neither residue.

On the real line, its product with $\sigma-1/2$ tends to $U$. On $\sigma+i\gamma$, the magnitude of that product tends to $a$ and is bounded by the corresponding real positive integral times $\sigma-1/2$. This forces $a\le U$. Thus each proposed eventual bound fails.

The prime number theorem gives $\sum_{k\le y}\mu(k)=o(y)$. Partial summation on $k/x\in[1/2,2]$ against the compact functions $h(t)$ and $t h'(t)$, each of bounded variation on its smooth pieces, gives $B(x)=o(x)$ and $B'(x)=o(1)$ wherever the derivative exists. The bounds are uniform on sufficiently late intervals. Locally there are only finitely many corners and $B$ is continuous. Over consecutive squares, at distance $O(\sqrt x)$, it follows that $B(x)/\sqrt x$ changes by $o(1)$. Both lower bounds therefore hold along $x=j^2$. In the *original*, unscaled weights $f_x(d)=x^{-1/2}h(d/x)$, the first tail $G_1=B(x)/\sqrt x$ exceeds $+0.02$ at infinitely many squares and falls below $-0.02$ at infinitely many others. In the continuum normalization $\sum|c_{m,M}|\ge |g(1/M)|$, which exceeds $0.02\sqrt M$ on an unbounded sequence of square meshes.

## Locate and price the zero independently

Riemann’s theta transformation gives
$$
\Xi(t)=\tfrac12-(t^2+\tfrac14)\int_1^\infty
 \sum_{k\ge1}e^{-\pi k^2 y}\,y^{-3/4}\cos((t/2)\log y)\,dy .
$$
Use the first two summands on $[1,9]$ with 32,768 composite Simpson panels. For $a=\pi,4\pi$ the magnitude of the fourth derivative of $e^{-ay}y^{-3/4+it/2}$ is at most $e^{-a}(a+9)^4$ throughout this interval at the two heights below. Indeed each factor $|-3/4+it/2-j|$ for $0\le j\le3$ is less than 9. The sum of the two bounds is below 2,000. Since $e^3>20$, integration of the positive exponential tails for $y>9$ or $k\ge3$ adds less than $3\cdot10^{-12}$. Include both errors before multiplying by $t^2+1/4$. [Riemann’s 1859 paper, Wilkins translation](https://www.claymath.org/wp-content/uploads/2023/04/Wilkins-translation.pdf)

The resulting $\Xi(14.13472)>6.44\cdot10^{-9}$ and $\Xi(14.13474)<-1.98\cdot10^{-8}$ place a critical zero between them. The gamma and elementary factors in $\xi$ are nonzero there. To bound $\zeta'$ throughout that height interval, differentiate the Euler–Maclaurin expansion ending at $N=256$ after its first Bernoulli correction. The remainder is bounded by
$$
\frac{31+225(\log N+2/3)}{18N^{3/2}},
$$
using $|B_2(\{x\})|\le1/6$, $|2s+1|<31$ and $|s(s+1)|<225$. Outward arithmetic yields $0.7584<\Re\zeta'(s)$ and $|\zeta'(s)|<0.82191194$. In particular the zero is simple and $a>0.02352275$. All trigonometric arguments, logarithms and exponential tails are enclosed in the replay. The existence and residue calculation uses no zero table or global zero-location assumption. [Definition of ξ](https://dlmf.nist.gov/25.4) · [Euler–Maclaurin representation](https://dlmf.nist.gov/25.2#iii) · [Arithmetic code](../receipt-archives/check_pal_boundary_zero.py) · [Endpoint results](../receipt-archives/2026-11-26-pal-signed-factorial-boundary.json)

## What a finite number of exact factorials buys

For $x=j^2$ the ordinary coefficient is $x^{-1/2}c_{m,x}$. The Lipschitz estimate gives $|x^{-1/2}c_{m,x}|\le16j/m^2$. Replace $\log(m!)$ for $m\ge M\ge2$ by $(m+1/2)\log m-m+\frac12\log(2\pi)+1/(12m)$. Stirling’s first omitted term bounds the total absolute error by $j/[90(M-1)^4]$. Indeed $\sum_{m\ge M}m^{-5}\le1/[4(M-1)^4]$. The observed local allowance at $j=256,M=5$ is below $0.000001660$.

More generally choose the first omitted Bernoulli index $k$ as the largest even integer $\le M-1$. Since $|B_k|=2k!\zeta(k)/(2\pi)^k$, the total remainder is at most $64j\,6^{-k}$ by the same integral comparison and $k!\le k^k$. Taking $M=2+\lceil\log_6(6400j)\rceil$ suffices for error $1/100$. The remaining signed main terms still depend on the genuine coefficients. Their cancellation at all squares is the outstanding estimate. [Stirling error bounds, DLMF §5.11(ii)](https://dlmf.nist.gov/5.11#ii) · [A signed factorial ratio with explicit prime contributions](counting-the-four-quarters-of-a-factorial.md)
