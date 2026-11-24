# A 577th power locally and a non-power globally

**24 November 2026.** We construct the class for the [fixed character in the actual zeta windows](2026-11-24-a-class-inside-the-zeta-windows.md). The local test reduces to one Taylor coefficient. Its four subtotals are $64,513,513,64$, all on the same field basis vector. Their sum is $2\cdot577$. At another prime the same Kummer class gives a root of unity of exact order 577. These two readings certify the strict local condition and global nonvanishing separately.

## The element and its divisor

Write $\ell=577$, $C=256$, $f=C\ell=147712$, $F=\mathbb Q(\zeta_f)$ and $j=296$. Let $\psi$ be as in the [host calculation](2026-11-24-a-class-inside-the-zeta-windows.md). The radicand character modulo $\ell$ is $\lambda=\bar\psi\omega^{297}$. To see the twist, if $\sigma z=z^{\lambda(\sigma)}$ modulo $\ell$th powers, then conjugation on translations of an $\ell$th root acts by $\omega\lambda^{-1}=\bar\psi^{-1}\omega^{-296}$. The fixed field $B=F^{\ker\lambda}$ is cyclic CM of degree 64. Inertia at $\ell$ maps onto the order-64 image since $5^{297}=20\bmod577$ has order 64. Thus $B$ has a single place at $\ell$, of ramification degree 64 and residue degree one. The extension $F/B$ has degree 1152, prime to 577.

Take $r=1920257=13f+1$, prime, and let $\chi$ send the least primitive root of $\mathbb F_r^\times$ to $\zeta_f$. Use the Jacobi sum
$$J=\sum_{x\ne0,1}\chi^{-1}(x)\chi^{-1}(1-x).$$
For $a\in(\mathbb Z/f)^\times$, choose $w(a)\in[1,576]$ representing $\lambda(a)^{-1}$. With $\sigma_a(\zeta_f)=\zeta_f^a$, set
$$\beta=\prod_a(\sigma_a J)^{w(a)}.$$
It lies in $B$ because the weights are constant on the kernel. Reindexing shows that its power class transforms by $\lambda$. Character orthogonality gives $J\bar J=r$. At the prime taking $\zeta_f$ to the matching primitive $f$th root in $\mathbb F_r$, its conjugate valuation is $v(\sigma_aJ)=\lfloor2a/f\rfloor$ for $0<a<f$. Indeed the reduction is a sum of $x^h(1-x)^h$ with $h=(r-1)(1-a/f)$. Its binomial expansion has a nonzero contribution exactly when exponent $r-1$ occurs. The norm limits the valuation to zero or one. The same calculation works at even conductor. [Full divisor argument](2026-11-24-why-the-classes-stop-at-twenty-five.md#a-divisor-identity-at-a-splitting-prime)

Now $\sum_{a>f/2,\ (a,f)=1}\lambda(a)^{-1}=0\bmod577$. Every conjugate divisor exponent of $\beta$ is a unit multiple of this sum modulo 577. The radicand therefore has valuations divisible by 577 everywhere. Away from 577 this gives an unramified Kummer class over $F$. Descent to the twisted module over $\mathbb Q$ follows from restriction and inflation. Here $[F:\mathbb Q]$ is prime to 577, as are its local ramification indices away from 577. [Divisor and orbit sums](fixed-character-577/bounds.py)

## Why only digit 297 matters

Normalize $v_B$ to take value one on a uniformizer. The 577-adic logarithm and exponential are inverse on all principal units of $B$ at this place, since $64/(577-1)<1$. Taking a 577th power shifts the logarithm by valuation 64. For a unit $\beta$ the criterion is therefore $v_B(\beta^{576}-1)>64$. In a completion of $F$ this is equivalent to $\beta^{576}=1\bmod \ell(1-\zeta_\ell)$. The ramification index there is 576. Raising to $\ell^4-1$ instead of 576 gives the same criterion on $B$, because their quotient is a 577-adic unit and the residue field of $B$ has size 577.

Over $\mathbb Q_\ell$ the 256th roots are in the unramified quartic extension. Write its residue field as $\mathbb F_\ell[Y]/(Y^4-20)$. The element 20 has order 64 and is a nonsquare, so $Y^4-20$ is irreducible and $Y$ has order 256. Choose $\zeta_f$ locally as a 256th root times $\zeta_\ell$. In the indicated quotient put $u=\zeta_\ell-1$. We have $\ell u=0$, $u^{576}=-\ell$ and $u^{577}=0$ from $\Phi_\ell(1+u)=0$. On principal units the formal logarithm truncated through degree 576 and its inverse are valid, since all the denominators up to 576 are units and any product of 577 copies of $u$ vanishes. The ideal $(u)$ is a vector space over the unramified residue field, with basis $X,\ldots,X^{576}$ for $X=\log(1+u)$. An inertia automorphism $a$ sends $X$ to $aX$.

Let $H_n$ count the Jacobi summands with exponent $n\bmod f$. For $v\in(\mathbb Z/256)^\times$ define
$$J_v(X)=\sum_n H_nY^{vn}\exp(nX)\pmod{X^{298}}.$$
Its constant term is a unit since $J\bar J=r$. The logarithm of $\beta^{\ell^4-1}$ is a sum of logarithms. Summing over the inertia variable $a\in\mathbb F_\ell^\times$ with weight $a^{-297}$ annihilates every basis vector except $X^{297}$. The weight-zero digit at $X^{576}$ is killed too. The surviving inertia sum and the exponent $\ell^4-1$ are both $-1\bmod\ell$. The remaining coefficient is
$$\sum_{v\in(\mathbb Z/256)^\times}\bar\psi(v)^{-1}
 [X^{297}]\log\big(J_v(X)/J_v(0)\big).$$
Each of the 128 summands is nonzero. In the ordered basis $1,Y,Y^2,Y^3$, the four subtotals for $v\equiv1,3,5,7\bmod8$ respectively are $64Y,513Y,513Y,64Y$. The zero total proves that $\beta$ is a local 577th power. Changing just the character label from 39 to 37 or 41 in the same calculation gives $416Y^3$ or $70Y^3$, both nonzero. The verifier computes the logarithmic derivative by power-series division using only arithmetic in the four-dimensional finite field. [Single-coefficient verifier](fixed-character-577/fourier_witness.py)

## Detect the global class separately

The prime $D=2363393=16f+1$ splits completely in $F$. At the place defined by its least primitive root, reduce each conjugate of $J$ and evaluate the 577th power-residue symbol of $\beta$. The answer is **1497311 modulo 2363393**. Its 577th power is one and it is different from one. Equivalently its discrete exponent is 333 relative to the root obtained from that primitive root. Thus the global class has order exactly 577. The Fourier verifier uses the two ordinary finite Fourier matrices of sizes 256 and 577 to evaluate all the conjugates. The detecting prime is independent of the moving host primes.

A second program norms $J$ over $\ker\lambda$ in the integer group ring and projects the remaining 64 conjugates. It works modulo $577^2$ for the local condition and modulo $D$ for detection. The group-ring representative may change by a 577th power when the integer weights are reduced during multiplication. It stays in $B$. Modulo $577^2$ the reduction of $\beta^{576}-1$ in the cyclotomic tensor basis has 36,244 nonzero coefficients. All are divisible by 577, and after dividing by 577 it vanishes at $\zeta_\ell=1$. This is exactly divisibility by $\ell(1-\zeta_\ell)$. Globally the independently computed residue symbol again equals **1497311**. [Packed-integer cross-check](fixed-character-577/group_ring_witness.py)

## Prove the upper bound

Any strict residual Kummer class has all valuations divisible by 577 in $B$, also at $\ell$ by the local condition. The ideal obtained by dividing its principal divisor by 577 gives an injection of this odd character sector into $\mathrm{Cl}(B)^-[577]$. The kernel would arise from units. For a CM unit $a$, $a/\bar a$ is a root of unity. There is no $\mu_{577}$ in a field of degree 64. This excludes an odd unit power class.

The relative class number formula gives the 577-adic valuation of $h(B)/h(B^+)$ as the sum of the valuations of $B_{1,\lambda^{-s}}$ for $s=1,3,\ldots,63$, using their Teichmüller lifts. All these characters are primitive of conductor $f$. The powers of two, Hasse unit index and number of roots of unity in the formula are 577-adic units. For each character the upper-half sum is twice its first Bernoulli number. Indeed $a\mapsto a+f/2$ changes the character sign at 256 and fixes $2a\bmod f$, so the remainder term cancels in $\lfloor2a/f\rfloor=(2a-(2a\bmod f))/f$. Modulo $577^2$ only $s=1$ gives an upper-half sum divisible by 577. Its value is $150597=261\cdot577$. Thus the entire 577-part of the minus class group has order 577. This is an unconditional class-number calculation in the degree-64 field. [Relative class number formula, equation (24)](https://www.math.columbia.edu/~chaoli/Eisenstein.pdf) · [All 32 terms](fixed-character-577/bounds.py)

At coefficient order $577^2$ use $F_2=\mathbb Q(\zeta_{256\cdot577^2})$. Restricting a class to this field preserves its order. The finite quotient is abelian and has a central scalar on the coefficients whose difference from one is a unit, so its positive-degree cohomology vanishes. Strict classes again map injectively into the ideal class group in the radicand sector. The possible unit kernel on the minus side now contains cyclotomic roots, but 2-adic inertia fixes these 577-power roots and acts on the desired sector by a primitive 64th root. The two actions are distinct modulo 577.

For an arbitrary splitting prime the Jacobi divisor identity proved above implies that the group-ring sum of $\lfloor2a/(256\cdot577^2)\rfloor\sigma_a^{-1}$ annihilates the ideal class group. Every ideal class is represented at a splitting prime by Chebotarev in the Hilbert class field. In the present character sector the multiplier is $165599=287\cdot577\bmod577^2$. An element of order $577^2$ cannot be killed by it. Higher order would imply an element of order $577^2$. The strict group at twist 296 is therefore **exactly $C_{577}$**. [Order-squared computation](fixed-character-577/bounds.py)

## Reproduce

From `receipt-archives/fixed-character-577` run `python -B fourier_witness.py`, `python -B bounds.py`, and `python -B group_ring_witness.py`. They need Python and NumPy. The last program can use gmpy2 for faster exact multiplication. All three run independently of Lean and of the discovery search.

## Unresolved

The calculation identifies which class reaches the proof. Whether a marked characteristic-zero cuspidal representation realizes its required congruence remains open. [Remaining automorphic obligation](2026-11-24-the-rank-three-obligation-at-577.md)
