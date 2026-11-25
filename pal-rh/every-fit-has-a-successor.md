# Every finite constant fit has a strictly better successor

Christopher Daniel Pang and Hearthline · 25 November 2026

Pang asked for an upward move that comes from the arithmetic itself. Here one can start from **any** finite rational remainder fit, protect any specified finite prefix, and produce an actual legal step that strictly reduces the error over **all** rows. This is a progress theorem before the missing all-tolerance theorem. The same construction gives an infinite sequence of productive moves that can never reach even a modest tolerance. Both statements concern the actual residue readings.

For a two-minute example, start with the zero fit. The legal reading $C_2(k)=\lfloor k/2\rfloor\bmod2$ gives $0,1,1,0,0,1,1,\ldots$ on positive rows. It preserves the wrong answer at row one and corrects rows two and three immediately. Those two rows alone save $1/6+1/12=1/4$ of the original total squared error. The argument below says how to find another real improvement after *any* finite history.

Let $F=\sum c_d b_d$ and $r(k)=1-F(k)$, with $w_k=1/[k(k+1)]$ for $k\ge1$. Extend the periodic residual to the phase $k=0$ by its formula, so $r(0)=1$. This phase is used to label future reset rows; the norm assigns no weight to row zero. Take a positive common period $L$ of the moduli, using $L=1$ for the empty fit. For a block of $L$ rows beginning at a positive multiple $z$ of $L$ its signed residual mass is the rational number
$$
R(z)=\sum_{i=0}^{L-1}\frac{r(i)}{(z+i)(z+i+1)}.
$$
Clear denominators with $D(z)=\prod_{j=0}^L(z+j)$. Its numerator is the explicit polynomial
$$
P(z)=\sum_{i=0}^{L-1}r(i)
 \prod_{\substack{0\le j\le L\\j\ne i,\ j\ne i+1}}(z+j).
$$
At zero only $i=0$ survives, giving **$P(0)=L!$**. Consequently $P$ has a highest nonzero coefficient $c_m$. At every $z>1+\sum_{i<m}|c_i/c_m|$ its sign is the sign of $c_m$ because the sum of all lower terms has magnitude at most $z^{m-1}\sum_{i<m}|c_i|$ for $m\ge1$. The constant-polynomial case already has a fixed sign.

Choose an integer $p\ge2$ divisible by $L$, beyond this explicit bound and the prefix to preserve. It is a frame spacing and need not be prime. Use the legal carry
$$
C_p(k)=2b_{2p}(k)-b_p(k)=\lfloor k/p\rfloor\bmod 2.
$$
It vanishes before $p$. On its active blocks $[p,2p),[3p,4p),\ldots$, split each into consecutive $L$-row blocks. Every block mass has the same strict sign as $R(p)$ because its starting point is at least $p$ and is a multiple of $L$. The rearrangement is legitimate since $r$ is bounded and the weights sum to one. In particular $R(p)\langle r,C_p\rangle\ge R(p)^2$. Also $\|C_p\|^2\le\sum_{k\ge p}w_k=1/p$. Choose the **rational** coefficient $a=pR(p)$. Expanding the square gives
$$
E(F+aC_p)\le E(F)-pR(p)^2<E(F).
$$
Both required new readings are admissible; the entire protected prefix is unchanged. This is an existence and finite-construction bound. Root bounds and common periods may make the recipe extremely expensive. The inequality gives a true lower bound on the gain before a new global fit is solved. It also proves that no finite fit attains the infimum over the full dictionary.

**Try the other direction.** Start from zero and always choose $p>1$. Inductively every fit keeps row one at zero, so its squared error is at least $w_1=1/2$ forever. The rule above always supplies another strictly better finite fit, even along this stalled route. Thus “there is a true improvement at every finite stage” cannot discharge the [sustained gain condition](PALRH.lean). A sufficient controller must budget enough gain while the requested tolerance remains unmet and must revisit rows that its current protection policy leaves wrong.

For the first-tick target the same remote improvement works for a nonzero finite fit. On remote rows the residual is $-F$, a nonzero periodic sequence. If its phase at zero vanishes, take the first $j$ with $-F(j)\ne0$. Evaluating the cleared polynomial at $-j$ leaves the term for $j$ and a zero term for $j-1$, so the polynomial is nonzero. At the empty fit a late-only move cannot reach the first tick; the first reading itself must be admitted. For a concrete first-tick trap start from $F=2b_2$. It reads $1$ at both rows one and three. The first is correct and the third is wrong. Retaining those two readings costs at least $1/(3\cdot4)=1/12$ forever, and at every finite stage a still later move can improve the true error. The [two-clock construction](close-clocks.md) supplies additional signed increments where the error is located.

The [Lean derivation](PALRH/Productive.lean) proves eventual sign for every nonzero finite block, both strict-successor theorems and both stalled-row bounds. It regroups the complete convergent sum and chooses a small rational coefficient from the positive overlap. The explicit pencil-and-paper coefficient above gives the displayed quantitative decrease. [Build and replay](../receipt-archives/2026-11-25-pal-strict-successor.json)

## Unresolved

Give a usable lower budget across the **changing** fits that prevents a positive floor, or exhibit a different globally sufficient localization. The degree, coefficient sizes and common period in the root bound above all depend on the previous choices. A lower gain valid at fixed $F$ does not yet control those dependencies. Literature priority is unassessed.
