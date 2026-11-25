# The same prime event in two clocks

Christopher Daniel Pang and Hearthline · 25 November 2026

The scalar alternative in the [construction key](CONSTRUCTION-KEY.md) asks whether an inequality already earned for one prime observable can fund the other. Pang’s RPL §§1, 11 and 20 retain the signed effect of genuine prime powers and the chosen clock. The input weights below are the published ones. [Suzuki, equation (1.1)](https://arxiv.org/pdf/2206.03682) · [Riemann–Pang Ledger](https://doi.org/10.5281/zenodo.21894278) · [Released principal ramp](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/StatementOC.lean#L9-L13)

For a prime power $n$, set $\lambda=\log n$ and $w=\Lambda(n)/\sqrt n$. An arithmetic term of the Suzuki/RPL sum on the log clock is $H_n(t)=w(t-\lambda)_+$. Multiply the arithmetic part of the released ramp at $x=e^t$ by $e^{-t/2}$. Its corresponding term is
$$
K_n(t)=e^{-t/2}\Lambda(n)(e^t/n-1)_+
      =2w\sinh((t-\lambda)/2)_+ .
$$
The positive part is taken **after** the displayed scalar function, and both terms start at the same event. On every bounded time interval there are finitely many contributing prime powers. For their sums $H,K$ over all events up to time $t$, the two exact conversions are
$$
H(t)=K(t)-\frac14\int_0^t(t-v)K(v)\,dv,\qquad
K(t)=H(t)+\frac12\int_0^t\sinh((t-v)/2)H(v)\,dv .
$$
It suffices to integrate each individual term after shifting its starting time to zero. Equivalently $2\sinh(u/2)$ has initial value zero, initial derivative one, and second derivative one quarter of itself. The two identities concern the arithmetic sums. The archimedean and centering terms of the full functions must travel separately.

**The order is directional.** The second conversion has a nonnegative kernel for $v\le t$. In the other direction, take the individual genuine events 3 and 5. In the exponential ramp 3 dominates 5 for every $x$. Before $x=5$ the latter term vanishes. After it the difference before the common scale factor is
$$
x(\log3/3-\log5/5)+\log(5/3)>0
$$
because $3^5>5^3$. In the linear hinge clock, 5 eventually dominates 3. Its outgoing slope $\log5/\sqrt5$ exceeds $\log3/\sqrt3$, since $5^3>3^4$ and $\sqrt{5/3}<4/3$. These two actual prime terms rule out a general order-preserving inverse for sums of such events. [Standalone Lean derivation](../receipt-archives/PALPrimeEvents.lean)

## Unresolved

An upper envelope on the normalized ramp cannot be sent backward merely by substituting its upper bound into both terms of the first integral identity. A route through this clock needs a signed estimate comparing the present value with that integral and the actual centering terms, or a directly earned one-sided bound for Suzuki’s function. RPL already explains why paying the absolute size of every loss diverges. The two-event obstruction applies to that transfer shortcut; it does not decide the full trajectory.
