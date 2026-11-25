# Carry one tick into every scale

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked whether a frame can carry itself forward as one and retain what the next frame would otherwise lose. In the arithmetic model, the first positive row can do exactly that. What remains open is isolating that row to **arbitrary** precision with the permitted measurements.

Let $\chi(k)=[k\ge1]$ and $e(k)=[k=1]$, both zero at the supplied origin. A legal fit is any finite rational linear combination of the readings $b_d(k)=(k\bmod d)/d$ for $d\ge2$. Errors are measured over the positive integers with $w_k=1/[k(k+1)]$.

**First-tick theorem.** Approximating $e$ arbitrarily well by legal fits in this norm is equivalent to the branch’s finite rational certificates for $\chi$. It implies Mathlib’s bare RH proposition. The Lean theorem still takes the first-tick approximation as its explicit premise. [Two-way construction and implication](PALRH/OneTick.lean)

## Forward

Put $D_p f(k)=f(\lfloor k/p\rfloor)$. A direct division gives
$$
D_p b_a=b_{pa}-b_p/a .
$$
Thus copying a legal fit to the quotient clock is itself a legal finite fit. Keep the zero at the origin. The consecutive rows $pj,\ldots,p(j+1)-1$ carry the coarser reading $f(j)$ and have combined weight $w_j/p$ for $j\ge1$. The initial incomplete block reads zero. Consequently $\|D_p f\|^2=\|f\|^2/p$ for bounded zero-origin signals. This is an exact identity for infinitely many rows. [Lean dilation proof](PALRH/Dilation.lean)

Now $\chi=e+D_2\chi$. If $g$ approximates $e$ with squared error $u$, start with $F_0=0$ and set $F_{m+1}=g+D_2F_m$. To see it by hand, the perfect first tick opens into $[1,1]$, then $[2,3]$, then $[4,7]$, then $[8,15]$. All of these bands belong on the same integer axis. Each finite $F_m$ is legal. The error update uses the actual overlap, bounded by $(a+b)^2\le3a^2+\tfrac32 b^2$. The factor $1/2$ from the quotient clock makes this a contraction:
$$
E_{m+1}\le3u+\tfrac34 E_m,\qquad E_m\le12u+(3/4)^m .
$$
Choose $u$ small enough and then $m$ large enough for the requested tolerance. The proof converts its span witness back to rational coefficients and pays the finite head and tail guard required by the existing RH bridge.

## Backward

Given a fit $f$ for $\chi$, use $g=f-D_2 f$ for $e$. The same inequality bounds its squared error by $\tfrac{15}4\|\chi-f\|^2$. This already makes the reverse implication rigorous. Using the actual signed observations can give a much better bound.

On the branch's **existing** 61-coefficient fit, the transported values are $g(k)=f(k)-f(\lfloor k/2\rfloor)$. With no new least-squares optimization, exact upward-rounded arithmetic gives
$$
\|\ e-g\ \|^2\le
\frac{353843017516150951}{18446744073709551616}
+\frac{1530169}{500002500}<\frac1{40}.
$$
The first term encloses 200,000 rows. Beyond them, $e=0$ and $|g|\le\sum|c_d|=24.74$, since each difference of two fractional turns lies between $-1$ and 1. The supplied checker also recomputes the first 202 rows directly. [Integer replay](../receipt-archives/check_pal_first_tick.py)

## A turn that changed the toolkit

For the one-tick target, measure $J(f)=-f(1)+f(2)+f(3)-f(4)$. Then $J(e)=-1$ and $J(b_d)=[d=4]$ for all $d\ge2$. If the reading at 4 is missing, weighted Cauchy–Schwarz gives
$$
1\le(2+6+12+20)\|e-f\|^2.
$$
Thus **squarefree moduli alone cannot even isolate the first tick to squared error below $1/40$**. The earlier squarefree-only statement concerned the constant target. When the old fit travels backward, $D_2 b_2$ introduces $b_4$. In our explicit witness the resulting coefficient at 4 is $-0.98$. Both the lower bound and its four-row detector are in [Lean](PALRH/OneTick.lean); the strict crossing is independently replayable rational arithmetic.

More generally, take the existing Möbius coefficient detector $D_d$ defined in the [branch paper](README.md). For $d\ge2$,
$$
D_d(e)=-\mu(d)+[2\mid d]\,\mu(d/2).
$$
Indeed $e(h-1)+e(1)-e(h)=1+[h=2]-[h=1]$, with $e(0)=0$. Hence a necessary dictionary contains all squarefree moduli at least two and every double of an even squarefree modulus. Under RH these suffice: use the squarefree balanced approximants for $\chi$ supplied by the earlier Báez-Duarte argument, then apply $I-D_2$. Going forward from first-tick accuracy uses all legal moduli through the frame updates. The arithmetic classification here is a paper corollary; its decisive $d=4$ instance is formal.

## Unresolved

Construct a sequence of rational residue fits with all-row squared error for the first tick tending to zero. We now have an exact way to spend an improvement at that single row across all scales. Every proposed generator must pay for the later copies that look like row one, retain the cost of reversing a frame, and admit the newly required 4-reading. The finite crossing above decides one barrier, with the all-tolerance construction open.
