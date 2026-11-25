# What every copy of one finite reading misses

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked what has to travel with a reading when it carries itself forward. Here is a limit that applies to every possible choice of one finite parent. Pick any finite rational sum $f$ of the legal residue readings. Make as many copies as desired on any positive integer clocks. Allow arbitrary real coefficients and refit them after every step. **Every such fit stays a positive distance from the constant target and from the first tick.** The distance can depend on the parent. The statement also holds with arbitrary real dilation factors at least one in the continuous reciprocal-cell model.

There is a way to teach the mechanism. Stretching a signal changes the phase and size of its response to a logarithmic wave. If the original response was exactly zero, multiplying it by a phase still gives zero. Adding differently stretched copies still gives zero. The work is to show that *every* finite parent has such a missing wave and that the target actually registers it.

## Which wave a row hears

Use $b_d(k)=(k\bmod d)/d$ for $d\ge2$, and give each positive row its actual weight $w_k=1/[k(k+1)]$. Its reciprocal cell is $(1/(k+1),1/k]$. Write $f(x)$ for the corresponding step function and extend it by zero above one. For $s=\sigma+it$ with $\sigma>1/2$, the reading
$$
M_s(h)=\int_0^1h(x)x^{s-1}\,dx
$$
is continuous in the true squared error. Cauchy–Schwarz gives $|M_s(h)|^2\le\|h\|^2/(2\sigma-1)$. The dilation $D_m h(k)=h(\lfloor k/m\rfloor)$ is $h(mx)$ in these cells. Changing variables gives $M_s(D_mh)=m^{-s}M_s(h)$.

Let $f=\sum_d c_db_d$ after collecting identical moduli. Its shape determines a finite exponential polynomial
$$
P_f(s)=\sum_d c_d(1/d-d^{-s}).
$$
For $\Re s>0$ and $s\ne1$ the earlier [cell calculation](README.md#why-the-obligation-reaches-rh) gives $sM_s(f)=\zeta(s)P_f(s)$. It comes from integrating the two floor functions on their actual intervals and continuing the result from $\Re s>1$. Every such $P_f$ vanishes at $s=1$ term by term. At that point the pole of $\zeta$ can cancel the zero. The proof needs a different point.

## A return arbitrarily far up the same line

The zero parent already misses the constant and the tick. For any nonzero parent $P_f$ is not identically zero. Along real $s\to+\infty$ its constant term is the limit. If that term vanishes, multiply by $d_0^s$ for the smallest $d_0$ with $c_{d_0}\ne0$ and obtain a nonzero limit.

For the finitely many moduli in $f$, consider the simultaneous phases $(e^{-in\log d})_d$ for positive integers $n$. This sequence lies in a finite product of circles, which is compact. Take a convergent subsequence and thin it so successive index gaps $T_j$ tend to infinity. Dividing successive phase vectors coordinatewise proves $d^{-iT_j}\to1$ for *all* these moduli at once. An exact common period is unnecessary. Consequently $P_f(z+iT_j)\to P_f(z)$ uniformly on every fixed closed disk, by direct termwise estimation of the finite sum.

Fix any $0<\eta<1/2$. Take a circle centered at $1$ of radius $0<r<\eta$ on which $P_f$ is nowhere zero. Such a circle exists because the center is an isolated zero. Let $b>0$ be the minimum modulus on its boundary. On that boundary the translated function eventually has modulus at least $b/2$, while its value at the center tends to zero. If a translated function had no zero in the closed disk, its reciprocal would be holomorphic there. The maximum modulus principle would bound its reciprocal at the center by $2/b$, which contradicts the center value for all sufficiently large $j$.

Thus $P_f$ has nonreal zeros $s$ with $|\Re s-1|<\eta$ at arbitrarily large heights. Take one. The zeta function is finite there, so $M_s(f)=0$ regardless of the value of $\zeta(s)$. This elementary return-of-zeros argument is classical for almost-periodic Dirichlet series. [E. Bombieri and A. Perelli, *Zeros and poles of Dirichlet series*](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2001_9_12_2_69_0)

## The actual error price

Every linear combination $g$ of scaled copies of $f$ now has $M_s(g)=0$. The constant has reading $1/s$. The first tick occupies $(1/2,1]$ and has reading $(1-2^{-s})/s$, also nonzero since $\sigma>0$. Therefore
$$
E_{\rm constant}(g)\ge\frac{2\sigma-1}{|s|^2},\qquad
E_{\rm tick}(g)\ge\frac{(2\sigma-1)|1-2^{-s}|^2}{|s|^2}.
$$
The inequalities also hold for the norm closure of the whole family. An update rule that keeps forming linear combinations and dilating its own descendants stays in that same family, since $D_mD_n=D_{mn}$. To have any prospect of reaching the target the process needs a new independent reading, an operation outside this family, or parents that vary with the requested accuracy.

## Six rows you can check

Take $f=\tfrac32(b_2+b_3-b_6)$. On rows zero through five it reads
$$
0,\quad 1,\quad \tfrac12,\quad 0,\quad -\tfrac12,\quad \tfrac12.
$$
Its consecutive changes are $1,-1/2,-1/2,-1/2,1,-1/2$. Their mean square is $1/2$. For $2b_2$ the consecutive changes are $1,-1$ and the mean square is $1$. The joint reading earns a real improvement in the cost of some local repairs. Its missed wave survives.

Here $P(s)=1-\tfrac32(2^{-s}+3^{-s}-6^{-s})$. Set $c=(794+17715i)/1000$ and $r=1/1000$. Direct rational enclosures give $|P(c)|<1/3000$ and $\Re P'(c)>1/2$. On the closed disk $|s-c|\le r$ one has $\Re s>0$, so $|P''(s)|<(3/2)(1+4+4)<14$ using $\log2<1$ and $\log3,\log6<2$. The map $s\mapsto s-P(s)/P'(c)$ contracts distances there by at most $7/250$, and the center moves by less than $1/1500$. These bounds send the disk strictly into itself and give an actual zero in it. The enclosed real part exceeds $3/4$, the imaginary part is positive and below $18$, and $|s|^2<325$. Thus **every** mixture of copies of this particular six-row signal has constant-target squared error **greater than $1/650$**. The first-tick error is **greater than $1/10400$** since $|1-2^{-s}|>1/4$. [Integer interval calculation](../receipt-archives/check_pal_single_parent.py)

The actual [row-repair trials](changing-the-first-wrong-row.md) start from $F_0=2b_2$. That initial term can carry a reading of its own, so it needs a separate calculation. Here $sM_s(F_0)=\eta(s)=\sum_{j\ge1}((2j-1)^{-s}-(2j)^{-s})$. Use the first 128 pairs at $c$. The real parts of $1-\eta_{256}(c)$ and $1-2^{-c}-\eta_{256}(c)$ exceed $7/6$ and $3/5$, respectively. The remaining pairs have total magnitude at most $|c|\int_{256}^\infty t^{-\Re c-1}\,dt<3/8$. Throughout the small disk $|\eta'(s)|\le1/\sigma+|s|/\sigma^2<34$ by differentiating the Mellin integral for $F_0$, which takes only values zero and one. Including the derivative of $2^{-s}$ gives a bound of $35$. The two residual readings, after multiplication by $s$, consequently have magnitudes above $3/4$ and $1/6$ at the actual zero. Every fit of the form $2b_2+\sum a_mD_m f$ has constant-target error **greater than $9/10400$** and first-tick error **greater than $1/23400$**. This rules out both initialized policies even if every subsequent coefficient is chosen optimally. The same integer calculation encloses the 128 pairs.

## Try keeping two readings independent

The separate parents $b_2,b_3$ have factors $1/2-2^{-s}$ and $1/3-3^{-s}$. A common zero requires $\sigma=1$ and both $t\log2$ and $t\log3$ to be integer multiples of $2\pi$. For $t\ne0$ this would equate a positive power of two to a positive power of three. The only common factor-zero is $s=1$. At one the original Mellin readings are $\log(2)/2$ and $\log(3)/3$, obtained from the simple pole of residue one and the linear terms of the two factors. In $\Re s>1/2$ the common zero readings of these two separate parents are therefore exactly the zeros of $\zeta$ in that half-plane. A fixed mixture of the same parents reintroduces its own missing wave.

Pang’s PAL v2.4 supplied the question about a retained frame, the RPL sieve supplied the six-row example, and the corpus instruction to reverse the move prompted the comparison with independently adjustable parents. The tools in the proof are the Mellin transform, simultaneous recurrence on a torus, and the maximum modulus principle. The upstream RH construction supplied no mathematical input to this result. We have not established publication priority for this application. [Corpus trail](CORPUS-ROUTES.md)

## Unresolved

Separate coefficients for two parents remove this specific extra Mellin obstruction. Whether their integer dilations can generate a sufficiently accurate fit is a further mathematical question. A common zero test alone does not characterize the closure established here. The independently fixed bare RH target remains open on this branch.
