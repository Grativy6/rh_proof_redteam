# Changing the first wrong row

Christopher Daniel Pang and Hearthline · 25 November 2026

A strictly better fit can keep overlooking the same wrong row forever. Pang asked us to turn the move around. Can we change one specified row by exactly one, leave every earlier row alone, and put a price on everything that change does later? The answer is yes. The **size** of the correction and the **net gain** on the receiving target have different formulas. Both can be measured. [Why strict improvement can stall](every-fit-has-a-successor.md)

## The row and its echoes

Let $f$ be any finite rational sum of $b_d(k)=(k\bmod d)/d$ with $f(1)=1$. Every such $f$ has $f(0)=0$. For an integer $m\ge2$ take
$$
h_{m,f}(k)=f(\lfloor k/m\rfloor)-f(\lfloor k/(m+1)\rfloor).
$$
This is a legal fit. Before $m$ both clocks read zero. At $m$ they read one and zero. If the current fit needs a change of $a$ at row $m$, add $a h_{m,f}$. The earlier answers stay fixed.

Write $u(t)=f(t)-f(t-1)$ and $w_m=1/[m(m+1)]$. On the rows $mt,\ldots,mt+t-1$, the two clocks see consecutive values of $f$ when $1\le t\le m$. On the rest of that $m$-row block they agree. The band weighs exactly $w_m/t$. All later rows together weigh $w_m$, and their squared amplitude is at most $4\|f\|_\infty^2$. Therefore, for every $m\ge2$,
$$
\sum_{t=1}^m\frac{u(t)^2}{t}
\ \le\ \frac{\|h_{m,f}\|^2}{w_m}
\ \le\ \sum_{t=1}^m\frac{u(t)^2}{t}+4\|f\|_\infty^2.
$$
For fixed $f$, $u$ is periodic. Subtract its mean square $V(f)$ from $u(t)^2$ and the partial sums of the difference are bounded. Summation by parts bounds their harmonic sum uniformly in $m$. Thus $\|h_{m,f}\|^2/(w_m\log m)\to V(f)$. [Exact return bands and whole-tail estimate](PALRH/CloseClocks.lean)

Start with $2b_2$. Its consecutive changes are $1,-1$, so $V=1$. The three-channel choice $f=\tfrac32(b_2+b_3-b_6)$ has changes $1,-1/2,-1/2,-1/2,1,-1/2$ and $V=1/2$. The first change still has full size one. The leading cost of the repeats is halved. Allowing **every** modulus up through 6 improves the optimum further to $4/9$.

## The best leading coefficient at each finite height

Use $f=\sum_{a=2}^B c_a b_a$, $x_a=c_a/a$ and $\sum_a x_a=f(1)=1$. Define
$$
z_e=\sum_{\substack{2\le a\le B\\ e\mid a}}x_a,\qquad
G_B=\sum_{e=2}^B\frac{\mu(e)^2}{\varphi(e)}.
$$
At every height $B\ge2$ the **exact minimum** of $V(f)$ is $1/G_B$. Here $\mu$ is the Möbius function, and $\varphi$ is Euler's totient.

To prove it, the mean of a product of two residue changes in a common period is $(\gcd(a,b)-1)/(ab)$. The identity $\gcd(a,b)=\sum_{e\mid a,\ e\mid b}\varphi(e)$ then gives
$$
V(f)=\sum_{e=2}^B\varphi(e)z_e^2,\qquad
\sum_{e=2}^B\mu(e)z_e=-1.
$$
The second equality follows by summing $\sum_{e\mid a,\ e\ge2}\mu(e)=-1$ against $x_a$. Weighted Cauchy–Schwarz gives $V(f)G_B\ge1$. Equality requires
$$
z_e^*=-\frac{\mu(e)}{\varphi(e)G_B}.
$$
These coordinates actually belong to a legal rational parent. Solve the equations for $x_B,x_{B-1},\ldots,x_2$ in descending order, subtracting the already assigned proper multiples from each $z_e^*$. The constraint gives $\sum x_a=1$. The excess for any other normalized choice is exactly $\sum_{e=2}^B\varphi(e)(z_e-z_e^*)^2$. [Lean proof of the minimum, the attaining parent and the exact row change](PALRH/RowRepair.lean)

This uses the classical Selberg diagonalization of a divisibility quadratic form. Removing the constant divisor and normalizing the first physical row gives the sum starting at $2$. Our application is the transfer from this finite arithmetic optimum to the cost of an admissible correction at a specified reciprocal row. [Selberg’s sieve, equations (4)–(5)](https://www.math.tau.ac.il/~rudnick/courses/sieves2015/selbergsieveintro.pdf)

## A bound when the height changes with the row

Let $K(m)$ be the infimum of the squared norms of all legal fits that are zero on $k<m$ and one at $m$. Set $A=\sum_{a=2}^B |c_a|$. Since $u(t)=1-\sum_a c_a[a\mid t]$, expanding $u^2$ uses just constants, single multiples and multiples of $\operatorname{lcm}(a,b)$. The count of multiples of any $d$ through $n$ differs from $n/d$ by less than one. Hence
$$
\left|\sum_{t\le n}(u(t)^2-V(f))\right|\le 2A+A^2
$$
at every $n$. Summation by parts keeps the same bound after weighting by $1/t$. Also $\|f\|_\infty\le A$. With the optimal parent just constructed, the full finite bound becomes
$$
1\le \frac{K(m)}{w_m}\le \frac{H_m}{G_B}+2A+5A^2,\qquad H_m=\sum_{t=1}^m 1/t.
$$
The lower bound is the cost at the specified row itself. The displayed upper bound is attained as an inequality by the explicit $h_{m,f}$.

For a rate requiring no prime distribution estimate, note $G_B\ge H_B/4-1$. Indeed every nonsquarefree number is a multiple of some $j^2$, $j\ge2$. The sum of reciprocals of all these multiples through $B$ is at most $H_B\sum_{j\ge2}j^{-2}\le3H_B/4$, by the integral bound after $j=2$. For squarefree $e$, $1/\varphi(e)\ge1/e$. Also $G_B\ge1$, so $|z_e^*|\le1$. Finite Möbius inversion gives $x_a=\sum_{j\le B/a}\mu(j)z_{aj}^*$, whence $|c_a|\le B$ and $A\le B^2$. Take $B=\lfloor H_m^{1/8}\rfloor$ for sufficiently large $m$. This supplies a legal correction for each such $m$ and proves
$$
w_m\le K(m)\ll w_m\frac{\log m}{\log\log m}.
$$
In particular the best available price is $o(w_m\log m)$, whereas every fixed finite normalized parent used in this adjacent-clock construction pays a strictly positive multiple of $w_m\log m$. The constant in the bound is absolute. The rate and the all-height comparison in this section are paper derivations.

## What happens on the two actual targets

Start both trials at $F=2b_2$, and always fix the first wrong row exactly. Use the six-row parent above. For the constant, the first repair is $+h_{2,f}$ and lowers total squared error by more than $1/160$. For the first tick, it is $-h_{3,f}$ and lowers total squared error by more than $1/250$. The next wrong rows are 4 and 5 respectively. Forcing those changes with the same parent **increases** total squared error in both trials. The single binary parent already increases both errors on the first change. The comparisons include every later row. [Reproduce the signed arithmetic](../receipt-archives/check_pal_row_repair.py)

For existing residual $r$ and change $a h$, the gain is $2a\langle r,h\rangle-a^2\|h\|^2$. Fixing the pivot controls one term in this sum. The examples above cut off the policy of fixing every earliest row and always reusing one shape. The [single-parent theorem](what-one-parent-misses.md) gives a positive error floor even when the coefficients of that shape's copies can be chosen freely.

Pang’s PAL frame question and RPL’s sieve determine which physical reading is being changed. This derivation uses the earlier two-clock identity, elementary divisor arithmetic and the stated Selberg antecedent. No assertion of literature priority is made. [Corpus roles](CORPUS-ROUTES.md)

## Unresolved

Choose genuinely independent corrections across successive rows and control their signed overlaps with the changing residual. The cost of a single correction is now bounded at every height. Paying for an entire infinite succession of repairs is the outstanding implication.
