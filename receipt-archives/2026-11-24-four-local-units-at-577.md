# Four local units at 577

**24 November 2026.** On the [fixed order-577 class](2026-11-24-the-obstruction-at-the-nonsplit-point.md) the two ordinary tangent directions read **35 and 387** on two explicit local units. Their cross-readings are zero. The two outstanding second-order readings use different units, at depths **35 and 72**. Depth counts powers of a uniformizer in the local splitting field. The number 35 occurring as a first-order character value and the depth 35 of the lower test come from different calculations.

## Fix the local field and the four measurements

Put $p=577$, $z=\bar\psi\omega^{296}$, $\eta=\chi_{-7}$, and let $F=L_y\mathbb Q(\sqrt{-7})$ be the [residual splitting field](2026-11-24-the-affine-resolvent-and-its-class-groups.md). At our place, $F_v/\mathbb Q_p$ has ramification index 72 and residue degree two. Indeed $\omega^{296}$ has inertia order 72, and $\psi(p)=510^{48}=553\bmod p$ lies in that inertia image. The real degree-576 field has residue degree one, the lower class splits there, and $-7$ is a nonsquare modulo $p$. The comparison field $T=\mathbb Q_p(\mu_{1792},\mu_p)$ has ramification index 576 and residue degree 12. The index $[T:F_v]=48$ is prime to $p$.

Use the local convention $Z$ for a primitive $p$th root and $Y$ for a primitive 256th root with $Y^4=\operatorname{Teich}(20)$. Choose a compatible primitive $D$th root $Y_D$ for $D=1792,896$, with $Y_{1792}^7=Y$. Take these to be the prime-to-$p$ parts of the compatible original primitive roots of conductor $Dp$. With the original order-$p$ generator mapping to $Z^{256}$, the original primitive $Dp$th root has local image $Y_D Z^{256/D}$, where the exponent is read modulo $p$. The parameter
$$\pi=\frac1{576}\sum_{s\in\mathbb F_p^\times}\frac{Z^s-1}{[s]}$$
has leading term $Z-1$ and transforms under tame inertia by the Teichmüller character. Brackets $[x]$ on a residue-field element mean its Teichmüller lift. For $a=1,2$ put $D_1=1792$, $D_2=896$, $\phi_a=\eta\bar\psi^a$ on the $D_a$-part, and $\tau_a=\sum_{v\bmod D_a}\phi_a(v)\bar Y_{D_a}^v$. The primitive Gauss sum is nonzero.

| Unit in $F_v$ | Depth in $F_v$ | Character of its logarithm | Role |
| --- | ---: | --- | --- |
| $u_1=\exp([\tau_1^{-1}]\pi^{296})$ | 37 | $\eta z$ modulo $p$ | First ordinary tangent |
| $u_2=\exp([\tau_2^{-1}]\pi^{16})$ | 2 | $\eta z^2$ | Second ordinary tangent |
| $u_-=\exp(Y^{-1}\pi^{280})$ | 35 | $z^{-1}$ | Second-order lower entry |
| $u_0=1+p$ | 72 | Trivial | Second-order diagonal inertia |

The displayed exponentials converge in $T$. The unit logarithms lie in $F_v$ by their characters. In particular $\tau_a^p=\phi_a(p)^{-1}\tau_a$, and $Y^p/Y$ reduces to 553. On principal units of $F_v$ the logarithm and exponential are inverse already at depth one. Raising to $p$ shifts depth by 72. The local unit quotient has graded pieces at depths 1 through 72, each with residue coefficients in $\mathbb F_{p^2}$. Inertia on depth $i$ has character $\omega^{8i}$. The unramified quadratic involution picks one residue line of either sign. This gives one unit line for each of the four indicated characters. Unramified diagonal changes are allowed by the ordinary flag and are invisible on $u_0$.

## Compute the first-order numbers

Normalize the first-order upper arithmetic classes explicitly. Form the circular-unit radicand by weighting the conjugates of $1-Y_{D_a}Z$ by the inverse of $\omega/(\eta z^a)$ modulo $p$, using global cyclotomic roots with those local images. Raise this radicand to $p^{12}-1$. Read the Kummer exponent relative to $Z$. These choices fix the scale of the two tangent vectors in this receipt.

For $i=296,16$ respectively, the leading term of the normalized radicand minus one is $b_a\tau_a\pi^{p-i}$ with $b_1=211$, $b_2=241$. In the truncated logarithm the tame inertia projection kills every lower degree, and the 576 inertia terms at degree $p-i$ contribute $-1\bmod p$. The final power contributes another $-1$. This recovers the signs in the [circular-unit computation](2026-11-24-three-deformation-directions-at-577.md#representatives-for-the-upper-directions).

Use the Hilbert symbol with first argument acting by local reciprocity and uniformizer acting by arithmetic Frobenius on the unramified extension. For $s+t=p$ its exponent on $1+A\pi^s,1+B\pi^t$ is
$$s\,\operatorname{Tr}_{\mathbb F_{p^{12}}/\mathbb F_p}(\bar A\bar B).$$
Here is a derivation. For $x=A\pi^s$, $y=B\pi^t$ the Steinberg identity for $-x(1+y)$ and $1+x+xy$, together with alternation, gives
$$(1+x,1+y)=(-x(1+y),\,1+xy/(1+x)).$$
Terms beyond depth $p$ are $p$th powers by logarithm and exponential. At depth $p$ the equation for the residue of a root $1+\pi w$ is $w^p-w=\bar A\bar B$, since $p/\pi^{p-1}\equiv-1\bmod\pi$. Frobenius adds the residue trace to $w$. This Kummer class is unramified, and the valuation of the first argument is $s$. [Milne, Class Field Theory, Hilbert symbol and local reciprocity](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

Applying the formula to $u_a$ gives exponents $296\cdot12\cdot211=526$ and $16\cdot12\cdot241=112$ modulo 577 in $T$. Restriction sends reciprocity at $T$ to reciprocity of the norm in $F_v$. Each unit belongs to $F_v$ and its norm is its 48th power. Thus the corresponding exponents on $\operatorname{rec}_{F_v}(u_1),\operatorname{rec}_{F_v}(u_2)$ are **35 and 387**. The opposite tangent vanishes at each unit because its tame character differs.

We checked this normalization by global reciprocity using two split primes and a separately constructed Jacobi element at each. Project the Jacobi sum to the odd character $\eta z^a$, and raise it to $p^{12}-1$ too. The third column gives its directly computed degree-$i$ coefficient times $\tau_a$. The fourth column is the Hilbert exponent in $T$.

| Jacobi prime | $a$ | Scaled Jacobi coefficient | Local symbol | Raw circular-unit Frobenius at the Jacobi prime |
| ---: | ---: | ---: | ---: | ---: |
| 12407809 | 1 | 102 | 568 | 61 |
| 12407809 | 2 | 449 | 89 | 139 |
| 19645697 | 1 | 180 | 52 | 481 |
| 19645697 | 2 | 379 | 327 | 206 |

In the cyclotomic field of conductor $D_a p$, the distinguished split prime sends the primitive radicand root $Y_{D_a}Z$ to $g^{(r-1)/(D_a p)}$. The generator in the raw Frobenius table therefore represents **$Z^{D_a}$**. Converting its exponent to $Z$ contributes $D_a\bmod577$, namely 61 or 319. The unnormalized Jacobi valuations at that prime are the upper-half multipliers 445 and 101. Both final $(p^{12}-1)$ powers change the finite exponents by $-1$. All conjugate symbols over the same rational prime coincide because the two radicand characters multiply to $\omega$. The number of places over $r$ divided by the number over $p$ in the common cyclotomic field is $12\cdot576$. Consequently global reciprocity predicts the local exponent $12D_a\cdot(\text{multiplier})\cdot(\text{raw Frobenius})\bmod577$. It agrees in all four rows. The local computation used the actual Jacobi histogram and formal series division in $\mathbb F_{577^{12}}$. [Local and global replay](boundary-577/hilbert_reciprocity.py)

## Read the two outstanding local conditions

Over the residual splitting field the local first-order upper matrices commute. After making the first-order local representative upper, the even correction on this local absolute group is an additive character. Its value on $u_-$ tests the strict lower condition and its diagonal value on $u_0$ tests the ramified change of weight. The character splitting and the unit-line calculation above prove sufficiency of these two tests. On each unit the first-order matrices are zero, so their quadratic readings are unaffected by changing the first-order frame.

There is an integral calibration. The earlier lower Kummer convention measures a first-level coefficient $hY$ after taking the 576th power of the local radicand. Its original radicand has leading coefficient $-hY$ at degree 297. On $u_-$ its exponent relative to $Z$ is $-280\cdot12h/48=507h\bmod577$. In the original lower calculation the primitive root of conductor $256p$ goes to $YZ$ and the detecting prime uses its 256th power as generator of $\mu_p$. Thus the exponent in that global basis is $507h/256=446h$. For the integral relaxed lift at $X=1$, $h=497$ gives **94**. On $u_0$ the principal cyclotomic character acts by $(1+p)^{-144}$ by the norm to $\mathbb Q_p$, so the previously measured weight change 117 gives **462** in the top diagonal convention. [Integral local controls](2026-11-24-the-obstruction-at-the-nonsplit-point.md#where-the-global-obstruction-goes) · [Unit and orbit replay](boundary-577/artin_units.py)

## Unresolved

The two units specify where to evaluate the relaxed second-order lift of each odd tangent. The values 94 and 462 calibrate the integral change of coefficients. The three quadratic evaluations on each unit still require the global even corrections. The [global commutators](2026-11-24-three-global-quadratic-readings.md) give independently computable controls for those corrections.
