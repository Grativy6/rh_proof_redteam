# How much credit crosses a prime cut

Christopher Daniel Pang and Hearthline · 26 November 2026

On the returned board let $z_i=Z_i$ be the number of jobs arrived less the ordinary cells released through distance $i$, with $z_0=0$. At each distance both the incoming jobs and that distance’s ordinary cells are available. A job receives a distinct cell by its arrival. The initial pocket pays for jobs permanently. At a cut the placement can hold up to $K$ unused ordinary cells for later jobs. Discarded cells cease to be available. Thus $K$ counts usable cell positions across a cut. The state used to describe those positions may be much smaller. The reverse orientation exchanges arrivals and ordinary supply, giving the path $-Z$. [Actual source and capacity](../proofs/why-either-side-of-the-pocket-is-enough.md)

## Every cut at the minimum pocket

Put $G=\max_i z_i$, $L_i=\max_{t\le i}z_t$, $R_i=\max_{t\ge i}z_t$. Unlimited storage costs exactly $G$ external cells. If a placement spends precisely that much, at least $L_i$ cells have already been spent by cut $i$. Reaching the future peak requires at least $R_i-z_i$ units of stock and further spending combined. Hence its retained ordinary cells satisfy
$$
 H_i\ge R_i-z_i-(G-L_i)=\min(L_i,R_i)-z_i .
$$

Equality is possible at every cut at once. Set $U_i=\min(L_i,R_i)$ and $H_i=U_i-z_i$. Up to a global maximum $U_i=L_i$ is nondecreasing, and afterwards $U_i=R_i$ is nonincreasing. A rise of $U$ occurs at a rise of $z$ at least as large. Pay that rise of $U$ from the external pocket. A fall of $U$ occurs at a fall of $z$ at least as large. Discard the corresponding ordinary cells. At every step the change in retained stock is exactly $\Delta U-\Delta z$. Stock begins and ends at zero and total pocket spending is $G$. With all other boundaries unrestricted, imposing cap $K$ just at cut $i$ increases the optimum by $(H_i-K)_+$. For this last statement, the minimum-cost prefix has spent $L_i$ and accumulated $L_i-z_i$ ordinary cells before the cap. The suffix needs $R_i-z_i$ available credit, producing the formula by subtraction. [Formal necessary inequality](PALRH/CutInventory.lean)

## A single list prices every storage cap

For fixed $K$, keep as many ordinary cells as possible, spend from them before charging the pocket, and discard surplus above $K$. This greedy rule minimizes pocket draws at every prefix. If a competitor’s cumulative expenditure is $S$ and its stock is $h$, the greedy values $S_*,h_*$ satisfy $S_*\le S$ and $h+S_*\le h_*+S$. Direct substitution preserves both inequalities at the next release and arrival, even if the competitor chose to spend early. [Formal proof for arbitrary competitors](PALRH/CutInventory.lean)

Use a valley below the whole path as a temporary endpoint on either side. Traversing the artificial initial rise adds the same constant independently of $K$ and the final descent costs nothing. Merge consecutive movements in the same direction. Now delete a shortest interior reversal of depth $d$. The neighboring movements each have length at least $d$. For a descent of $a$, rise of $d$, descent of $b$, with $a,b\ge d$, the resulting stored amount equals that after the single descent $a+b-d$. The original path spent exactly $(d-K)_+$ more. In the opposite orientation, a rise of $a$, descent of $d$ and rise of $b$ have the same extra cost and final stock as compared with a single rise of $a+b-d$. These are identities for truncated subtraction and $\min$, valid for any incoming stock up to $K$. Repeating the deletion leaves the largest peak. Thus
$$
 B(K)=G+\sum_{\nu}(d_\nu-K)_+ .
$$

Equivalently, process turning points in a stack and delete the middle two of four consecutive points whenever their connecting edge is no longer than either neighbor. The replacement edge is at least as long as both exterior edges. Only a newly neighboring edge can become a new local minimum, so the stack permits the same reduction in one pass. Once both low endpoints are present, any remaining interior edges have a shortest one and reduce. Equal neighboring readings can be contracted first. The multiset of positive depths is intrinsic since the slope changes of $B(K)$ recover it. This finite calculation is related to upward truncated variation and the play operator, with a distinguished initial pocket and a free terminal discard specified here. [Local elimination identities](PALRH/CutInventory.lean) · [Earlier work on play and truncated variation](https://doi.org/10.1002/mma.3077)

For depths $d_1\ge d_2\ge\cdots$ and an allowed pocket $P\ge G$, the least integer cap is the maximum of zero and
$$
 \max_{r\ge1}\left\lceil\frac{G+\sum_{i=1}^r d_i-P}{r}\right\rceil
$$
over nonempty initial segments of the list. Indeed the sum of positive parts is the maximum of those initial sums less $rK$, including the empty one. For a monotone path the list is empty. At $P=G$ the answer is the deepest single reversal, also $\max_i H_i$. On $0,5,-2,3,1,7$ the finite depths are 7 and 2, giving $B(3)=11$ and $B(7)=7$. [Executable reductions and an independent stock simulation](../receipt-archives/pal_carry_storage.py)

## Actual prime arrivals

Here $P=\lfloor n^2/13\rfloor$. The first three numerical columns are carry capacities divided by $nx$, the volume of a distance column at the full row width. The last counts the positive finite depths in the original orientation. Printed ratios are rounded. Raw integers, failing budgets one cell below the optimum, and both bracketing peaks are in the receipt.

| Last observed distance $M$ | Cap at prescribed pocket | Cap at smallest pocket | Reverse cap at prescribed pocket | Finite depths |
|---:|---:|---:|---:|---:|
| 65,536 | 44.1097 | 251.8832 | 46.0233 | 3,723 |
| 1,048,576 | 180.3544 | 815.0843 | 188.3784 | 68,393 |
| 16,777,216 | 590.3794 | 3,890.1480 | 619.1551 | 1,013,709 |

Every physical distance boundary enters the stock cap. Between consecutive primes $Z$ decreases, so the terminal point of the gap and the point immediately after the arrival suffice to retain every turn. Checking storage only at prime arrivals would change the last board’s normalized minimum from 590.3794 to 575.5208. On the first board the minimum actual cap is 740,037,595,470,834. Reducing it by one puts the required expenditure seventeen cells above the allowed pocket. The replay also enumerates general placements, including advance spending, for 4,375 small path/capacity pairs. [Full finite results](../receipt-archives/2026-11-26-pal-carry-storage.json)

## What the arithmetic forces across cuts

For either orientation, suppose a placement spends $B=O(n^2)$ and retains at most $K$ ordinary cells across any physical cut. On all sufficiently large prescribed boards where such a placement exists,
$$
 K\ \ge\ nx\exp\!\left(c\sqrt{\log M/\log\log M}\right)
$$
for some absolute $c>0$. This necessity allows ordinary cells to remain available arbitrarily long. It uses a lower bound on average discrepancies over many *disjoint* intervals.

For clarity, if $I=(a,b]$ lies in $[M/4,M]$ and has length $y+O(1)$ with $y=M^{o(1)}$, the actual data satisfy
$$
 \frac{Z_b-Z_a}{x(n-a)}=\theta(b)-\theta(a)-(b-a)+o(1).
$$
Indeed $t_p/x=\log p+O((1+\log p)/x)$, and $(n-p)/(n-a)=1+O(y/n)$. Even bounding the number of primes by $y+1$ gives error $O(y\log M/x+y^2\log M/n)=o(1)$. The same weight correction applies to the released ordinary columns. The root lies below these intervals eventually. Integral endpoints can be chosen to include the intended row of primes with an $O(1)$ adjustment to its length.

For disjoint rows $I_r$ let $e_r$ be their $\theta$ discrepancy and let $\sigma=1$ or $-1$ be the chosen orientation. The pocket draw in a row is at least $(\sigma\Delta Z_r-K)_+$. The positive part permits using the smallest physical weight $x(n-M)$ even when individual row discrepancies have opposite signs. With $L$ rows this implies
$$
 \frac{K}{x(n-M)}\ \ge\ \frac1L\sum_r\sigma e_r-o(1)-\frac{B}{Lx(n-M)}.
$$

**The external number-theoretic input.** We use the row total in the proof of Granville and Soundararajan’s Theorem 1.5, before their choice of one extremal row. Put $X=\lfloor M/3\rfloor$. In their Corollary 5.4 take $Q=X^b$ with $b>0$ small enough that $b<1/4$ and their progression estimate holds. It supplies $q=Q^{1-o(1)}$ up to $Q$ and $z\sim2\log Q$. Choose $y=\lfloor\exp(\kappa\sqrt{\log X/\log\log X})\rfloor$ with fixed $\kappa>0$ sufficiently smaller than the constant in their equation (5.3). Then $u=\log y/\log z$ is in the range of Corollary 3.5. The two offsets from that corollary are $X^{o(1)}$. Each sign has $L=X/q+O(1)$ rows beginning at $rq+v_\pm$ with $X/q<r<2X/q$. Their width $y$ is less than $q$, so they are disjoint and lie in our observed range. [Granville and Soundararajan, Corollaries 3.5 and 5.4 and the row sum on page 623](https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n2-p06.pdf)

The mean row sum is $[q/\varphi(q)]$ times the count of reduced residues in the selected length-$y$ interval, with relative error $O(\exp(-\beta\sqrt{\log X/\log\log X}))$ and negligible endpoint terms. All prime factors of $q$ lie between $\sqrt z$ and $z$, so $q/\varphi(q)=O(1)$ by the reciprocal-prime estimate on that range. The individual interval endpoint correction is $O(1)$ in length, and any end correction in replacing the shifted column by the progression at $X,2X$ costs $O(y\log X/L)$ in the mean. Corollary 3.5 consequently gives signed mean excess at least a constant times
$$
 y\exp[-u(\log(u+1)+\log\log(u+2)+O(1))]=y^{1/2+o(1)} .
$$
The absolute progression error is $o(1)$ for the chosen $\kappa$. In particular the mean signed excess is at least $y^{1/3}$ eventually, separately for each sign. Since $L\gg X^{3/4}$ while $x=4\sqrt M(j+1)^2$, the pocket term in the preceding inequality tends to zero. This gives the stated carry lower bound with a possibly smaller positive constant. The interval estimate of Theorem 1.5 in isolation would provide only one row per sign. The disjoint family and its mean are essential here.

There is also a shorter route to a weaker positive-orientation result. Maynard’s Theorem 3.2 gives $\gg X\exp(-\sqrt{\log X})$ intervals of length $\lfloor\log X\rfloor$ with $\gg\log\log X$ primes in each. At least a constant times that many divided by $\log X$ may be chosen disjoint. Each needs $\gg nx\log M\log\log M$ more than it releases, which already forces $K\gg nx\log M\log\log M$. The matrix argument gives the stronger result above in both directions. [Maynard, Theorem 3.2](https://arxiv.org/pdf/1405.2593)

For an upper bound, if both signed readings have magnitude at most $B$, the explicit least-pocket profile holds at most $2B$ ordinary cells. Thus the RH-implied two-sided one-thirteenth estimate also supplies a simultaneous placement with initial pocket $B$ and ordinary stock at most $2B$ at every cut. The unconditional lower bound leaves a gap to this sufficient scale. It also leaves open whether the initial pocket suffices on every board. [Where the original comparison stands](../proofs/one-thirteenth-of-a-returned-layer.md)
