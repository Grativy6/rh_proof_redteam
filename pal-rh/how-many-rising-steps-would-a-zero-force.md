# How many rising steps would an off-line zero force?

Christopher Daniel Pang and Hearthline, 25 November 2026 (New York). Pang asked us to try the direction both ways. The two signs of a change of frame can be counted even when its magnitude is hard to estimate.

Put $u_j=B(2j^4)/(2j^4)$ for the actual PAL primitive. **If RH fails**, then for every $0<\eta,\delta<1$ and every sufficiently large integer $J$, there are at least $J^{1-\delta}$ strict rises $u_{j+1}>u_j$ in $[J^\eta,J)$ **and** at least $J^{1-\delta}$ strict falls there. Thus it suffices for RH to find arbitrarily large cutoffs with a power saving in the count of either direction. One may choose the less frequent direction anew at each cutoff. The result is a paper implication. The [fixed integer theorem](../proofs/the-integer-that-turns-at-forty-four.md) takes a stronger eventual sign assumption. Finite counts establish neither assumption at unbounded heads.

## Make a positive compact signal

Write $a(n)$ for the actual first-pass coefficients, $A(s)$ for their Dirichlet series, $M(t)=\sum_{n\le t}a(n)$ and $F(t)=B(t)/t$. Everything below vanishes before $t=1$. Let $h$ have Dirichlet series
$$
 \frac{(1-2^{1-s})(1-2^{-s})}{A(s)}.
$$
In $\Re s>1$ the factor $1/A(s)$ is $\zeta(s)$ times the four fixed Euler factors at 2 and 3. Hence $h$ is a finite linear combination of dilates of the alternating integer sequence: group $\zeta(s)(1-2^{1-s})$ first. The coefficients of $a*h$ at 1, 2 and 4 are respectively $1,-3,2$ and all others vanish. Since $F(t)=\sum_n a(n)(1-n/t)_+/n$, exact grouping of finite products gives
$$
 \sum_{r\le x}\frac{h(r)}r F(x/r)=
 W(x)=(1-1/x)_+-\tfrac32(1-2/x)_++\tfrac12(1-4/x)_+.
$$
Here $W$ is positive on $(1,4)$ and zero outside its closure. Its Mellin integral against $x^{-s}$ equals $(1-2^{-s})(1-2^{1-s})/[s(s-1)]$. This follows by integrating the three ramps first for $\Re s>1$ and then continuing the compact integral. [Finite arithmetic check](../receipt-archives/check_pal_rise_direction.py)

At a zeta zero $\rho$ with $1/2<\beta=\Re\rho<1$, the kernel
$$
 K_\rho(v)=v^\rho\sum_{r\le v}h(r)r^{-\rho}
$$
is uniformly bounded on $v>0$. The alternating series at $\rho$ sums to zero, and partial summation bounds its tail by $O_\rho(v^{-\beta})$. Finite dilations preserve that bound. Multiply the preceding identity by $X^\rho x^{-\rho}$ and integrate up to $X\ge4$. The result is
$$
 X^\rho\int_1^4 W(x)x^{-\rho}dx=\int_1^X F(t)K_\rho(X/t)\,dt.
$$
The left moment is nonzero because both numerator factors are nonzero for this real part. Therefore for every sufficiently large $X$,
$$
 \int_1^X |F(t)|\,dt/\sqrt t\ \gg_\rho\ X^{\beta-1/2}. \tag{1}
$$

## Both signs must supply the bill

Let $b=a*\mathbf1$, the positive smooth source from the [integer calculation](../proofs/the-integer-that-turns-at-forty-four.md). Its total reciprocal mass is 9. Its partial sum is $O(\sqrt z\log(2z))$, since $b(2^i3^j)\le3\sqrt{2^i3^j}$ and one can sum a geometric progression for each power of 3. Hence $J(x)=\sum b(n)(1-n/x)_+/n$ satisfies $9-J(x)=O(\log(2x)/\sqrt x)$ for $x\ge1$, by partial summation.

Use the ordinary square-root reader
$$
 k(v)=\lfloor v\rfloor/\sqrt v-\tfrac12\sum_{n\le v}n^{-1/2}.
$$
For $v\ge1$ it lies between $1/5$ and 1. The divisor identity $\sum_{r\le x}F(x/r)/r=J(x)$, integrated once with constant weight and once with inverse square-root weight, gives
$$
 \int_1^X F(t)k(X/t)\,dt/\sqrt t
 =\int_0^X J(x)\left(1/\sqrt X-1/(2\sqrt x)\right)dx
 =O(\log^2(2X)).
$$
In the last step the constant 9 integrates to zero and the error is integrable with the stated logarithmic loss. The weighted sum of the two sign areas dominates one fifth of (1), and their weighted difference is bounded by the last display. Each of the unweighted positive and negative areas must therefore be $\gg_\rho X^{\beta-1/2}$, at **every** sufficiently large terminal head. [Elementary reader bounds and change of variables](what-the-two-signs-cost-together.md)

## Bound the change in one step

Let $\Theta$ be the supremum of $1/2$ and the real parts of the nontrivial zeta zeros. If $\Theta<1$, choose $\Theta<b_0<1$. The Balazard–Saias bound on any such real line gives $\sum_{n\le x}\mu(n)=O_{b_0}(x^{b_0})$ by partial summation. The four smooth factors have convergent absolute Dirichlet series at $b_0>1/2$, so $M(x)=O_{b_0}(x^{b_0})$ as well. Since $\sum a(n)/n=0$, partial summation gives $F(t)=O_{b_0}(t^{b_0-1})$. If $\Theta=1$, use $b_0=1$, the elementary absolute mass bound and the boundedness of $F$. This uses the actual zero supremum without assigning it a value. [Balazard–Saias bound, Lemma 2.1 reproduced by Báez-Duarte](https://arxiv.org/pdf/math/0202141#page=3)

The identity $F'(t)=M(t)/t^2$ between successive integers now gives, across a fourth-power root step,
$$
 |u_{j+1}-u_j|\ll_{b_0} j^{4b_0-5}. \tag{2}
$$
Control of the value and its change uses the same exponent. The sign of the change is exactly the earlier signed count plus the new weighted strip in the [one-head identity](../proofs/one-quantity-at-each-fourth-power.md).

## Why a few large jumps would not suffice

Fix a zero as above and choose $0<\alpha<1$ with $\alpha(b_0-1/2)<\beta-1/2$. The part of either area up to $X^\alpha$ is $O(X^{\alpha(b_0-1/2)})$. Each sign therefore attains magnitude $\gg_\rho X^{\beta-1}$ between $X^\alpha$ and $X$: the remaining inverse-square-root weights total at most $2\sqrt X$. The [fourth-power chord bound](../proofs/one-quantity-at-each-fourth-power.md) differs from $F$ by $O(t^{-1/2})$ after division by $t$, with nonnegative endpoint weights adding to one. If also $\alpha>2(1-\beta)$, that error is smaller than the required magnitude. One of the two neighboring sample values consequently has the same sign and magnitude up to a fixed factor.

Under failure of RH choose $\beta$ arbitrarily close to $\Theta$ and $b_0$ arbitrarily close above it, with $b_0=1$ in the endpoint case. Both constraints allow $\alpha$ arbitrarily close to 1. Applying the last paragraph with terminal physical head a fixed factor below $2J^4$ therefore gives, for any chosen root exponent $\alpha'<1$ sufficiently below $\alpha$, both signs among $J^{\alpha'}< j<J$, each with magnitude at least $cJ^{4\beta-4}$. The fixed head factor keeps the neighboring root inside $J$.

To count rises, use a negative sample with terminal root $\lfloor J^{1-2\epsilon}\rfloor$ and a positive sample with terminal root $J$. Choose $\alpha'$ close enough to 1 that the first root exceeds $J^{1-3\epsilon}$ and the second exceeds $J^{1-\epsilon}$. The samples are in chronological order. To gain the required $cJ^{4\beta-4}$ between them, (2) requires at least
$$
 c' J^{\,1-4(b_0-\beta)-3\epsilon(5-4b_0)}
$$
strict upward steps, since $4b_0-5<0$. Reverse the two signs to count falls. For the prescribed $\eta,\delta$ choose $\epsilon$ small and $\beta,b_0$ close enough to $\Theta$ to leave strict slack in both exponents. Absorbing the constant for large $J$ proves the claim.

This route has an explicit remaining test. It needs a fixed power saving on arbitrarily late counts of a direction. Observing the same direction on one long finite prefix, or saving only powers of its logarithm, does not establish that test.
