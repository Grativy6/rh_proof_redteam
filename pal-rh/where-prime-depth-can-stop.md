# How deep the prime core has to travel

Christopher Daniel Pang and Hearthline · 25 November 2026

The two-clock grid assigns every squarefree core $r$ coprime to 6 a signed outgoing amount $\mu(r)/(3r)$ for the occupied target. Multiply by $3r$ and its signed mark is exactly $\mu(r)$. This paper follows those marks across **different** cores and gives a finite rule for leaving some of them out. [Origin of the mark](what-five-carries.md)

Write $R(x)=\sum_{n\le x,\ (n,6)=1}\mu(n)$ and $M(x)=\sum_{n\le x}\mu(n)$. Separating factors 2 and 3 gives the exact identity
$$
M(x)=R(x)-R(x/2)-R(x/3)+R(x/6).
$$
Summatory functions at real arguments always use the integer floor. Conversely $R(x)=\sum_{a,b\ge0}M(x/(2^a3^b))$, a finite sum of nonzero terms. For any positive growth exponent, the reverse bound passes through the convergent geometric weights $2^{-a\sigma}3^{-b\sigma}$. Thus the usual square-root-plus-epsilon bound for the full Möbius walk is equivalent to the same bound on the cores.

## An integer stopping rule at each square

Choose a side $j\ge1$ and put $X=j^2$. Take the pool of primes $3<p\le X$. For each positive depth $d$ compute the nonnegative integer
$$
C_d(X)=\sum_{\substack{A\text{ a }d\text{-element subset of the pool}}}
          \left\lfloor\frac{X}{\prod_{p\in A}p}\right\rfloor .
$$
Stop at the **first** $d$ for which $C_d(X)\le j$. Such a depth always exists since an empty collection of subsets has sum zero. Keep only squarefree rough products with **fewer** than $d$ factors. Include 1. Give each product the sign $(-1)^{\#\text{ factors}}$ and call their sum $U(j)$.

Every omitted squarefree core is divisible by the product from at least one of the counted subsets. Its sign has absolute value one. Consequently
$$ |U(j)-R(j^2)|\le C_d(j^2)\le j $$
at every side, regardless of the signs. This is an exact admission rule. It can be evaluated from primes and integer quotients; an equivalent counting method adds $\binom{\omega_{>3}(n)}d$ over all positive $n\le X$.

Between $j^2$ and $(j+1)^2-1$ at most $2j$ more terms can enter. Therefore
$$
\forall\epsilon>0\quad |U(j)|=O_\epsilon(j^{1+\epsilon})
\quad\Longrightarrow\quad \mathrm{RH}.
$$
Indeed the square allowance and the intervening $2j$ terms give $R(x)=O_\delta(x^{1/2+\delta})$ for every $\delta>0$; the four-term identity gives the corresponding bound for $M$. The absolutely convergent Mellin integral of that signed primitive excludes a zeta zero to the right of the line. Under RH the converse follows from Littlewood's bound, the smooth dilation sum for $R$, and the same admission rule. [Formal omission bound, four-core identity and sufficient direction](PALRH/RoughSquares.lean) · [Signed primitive and continuation](PALRH/Octaves.lean) · [Classical converse input](https://arxiv.org/pdf/math/0202141)

At $j=1024$, depth four has $C_4=35135$ and depth five has $C_5=694$. The rule therefore keeps at most four factors. It keeps signed sum $321$. There are actually $450$ omitted squarefree cores, all of sign $-1$, and $R(1024^2)=-129$. At $j=1536$ it keeps at most five factors; the three omitted marks all have sign $+1$. [Integer calculation](../receipt-archives/check_pal_core_squares.py)

## Where absolute pruning changes power

There is a sharp asymptotic calibration for the price of discarding by depth alone. Fix $0<\kappa<1$. In the octave $(H,2H]$, omit the rough squarefree integers with more than $J$ factors, where $J$ is the largest index for which the product of the first $J$ primes greater than three is at most $H^\kappa$. Let $D(k)$ count the omitted integers between $H$ and $k$. Then
$$
\sum_{H<k\le2H}\frac{D(k)^2}{k(k+1)}=H^{\,1-2\kappa+o(1)} .
$$
This is the absolute omission price. The signed contribution can have further cancellation.

To prove the upper bound, a $d$-fold product uses $d!$ distinct orderings. Counting all its multiples bounds the number omitted by $2H(\sum_{p\le2H}1/p)^d/d!$, where $d=J+1$. The prime number theorem gives $p_j\sim j\log j$, so $\log\prod_{i\le J}p_i=(1+o(1))J\log J$ also after omitting 2 and 3. Hence $d=(\kappa+o(1))\log H/\log\log H$. For the needed upper bound on prime reciprocals, set $s=1+1/\log(2H)$. Euler's product gives $\sum_{p\le2H}1/p\le e\log\zeta(s)\le e\log(1+\log(2H))$. The factorial bound now gives $H^{1-\kappa+o(1)}$ omissions. Squaring and summing the weights costs $H^{1-2\kappa+o(1)}$.

For the reverse bound plant the product $P$ of the first $J$ rough primes. It has size $H^{\kappa+o(1)}$. Every prime $p$ in $(H/P,3H/(2P)]$ is larger than its factors for all sufficiently large $H$, and $Pp$ is an omitted squarefree core already present by $3H/2$. The prime number theorem gives $H^{1-\kappa+o(1)}$ such primes. Their accumulated absolute count persists throughout the remaining half octave, which has mass comparable to $1/H$. This proves the lower exponent. The same argument in $[1,X]$ shows that the positive tuple-count stopping depth at $X=j^2$ has leading size $\tfrac12\log X/\log\log X$: the displayed upper bound makes every fixed $\kappa>1/2$ affordable eventually, and the planted multiples forbid every fixed $\kappa<1/2$ eventually. For smaller depths the lower follows as well by counting those multiples; the tuple cap itself need not be monotone in $d$. [Unconditional prime-count input](https://arxiv.org/abs/2204.01980)

At $\kappa=1/2$ absolute omission costs only a subpower on an octave. Beyond $1/2$ it decays by a power. Below $1/2$ a claim that charges every omitted sign in absolute value must pay a positive power. This identifies what can be trimmed without obtaining any estimate for Möbius sign correlations.

## Where the surviving signs cancel

Let $S(k)=R(k)-R(H)$. The exact octave cost expands as
$$
\sum_{H<k\le2H}\frac{S(k)^2}{k(k+1)}
=\sum_{H<u,v\le2H}\mu_6(u)\mu_6(v)
  \left(\frac1{\max(u,v)}-\frac1{2H+1}\right),
\qquad \mu_6(n)=\mu(n)[(n,6)=1].
$$
The diagonal alone is bounded independently of $H$. For any surviving unequal pair write $u=ga$, $v=gb$ with $\gcd(a,b)=1$. All of $g,a,b$ are individually squarefree and pairwise coprime. Their product of signs is $\mu(g)^2\mu(a)\mu(b)=\mu(ab)$. Group the pairs by $ab$. Every summand inside a group has the same sign and a positive geometric weight. Cancellation can occur only **between** different such product groups. The pair $5,7$ and the pair $55,77$ both contribute positively to group $35$. The pair $19,35$ contributes negatively to group $665$. [Direct and grouped arithmetic](../receipt-archives/check_pal_growth_windows.py)

There is already a positive contribution of order $H$ if signs are separated before summing. A positive fraction of $(H,3H/2]$ consists of squarefree integers coprime to 6. For example, first sieve out 2 and 3 and all squares of primes up to a fixed $z$, using the Chinese remainder theorem. The loss to larger prime squares is at most $(H/2)\sum_{p>z}p^{-2}+O(\sqrt H)$, which can be made smaller than half the surviving density. At least half the surviving signs agree. All their pair weights are at least $1/(6H)$. Paying these positive pairs without the negative product groups leaves a linear cost.

At $H=1{,}048{,}576$, charging the absolute rough marks gives an octave cost greater than $11016$. Keeping the signs gives a cost between $0.01002$ and $0.01004$. These are finite measurements of the same rows. The missing estimate concerns the signed totals on increasing heads. The [overlap proof](what-the-next-octave-costs.md#why-the-first-doubling-windows-themselves-suffice) applies with $R$ in place of $M$ and then uses the four-core transfer.

## Credit and unresolved claim

Pang’s RPL square shell, PAL’s retained frame, and the two-clock boundary calculation locate the rough cores. The counting proof uses ordinary divisibility, the factorial cost of ordering distinct primes, and the classical prime number theorem at the explicitly marked asymptotic step. This application and its exact arithmetic controls were developed on the independent branch. [Corpus roles](CORPUS-ROUTES.md)

The retained signed sum $U(j)$ still needs its $j^{1+\epsilon}$ bound. Exact enumeration, the side-length omission allowance, and the sharp cost of absolute pruning isolate that obligation. They do not establish it.
