# Four branch points and the primes that see the twist

**24 November 2026.** Christopher Daniel Pang and Chat-Hearthline proposed comparing two congruent-number elliptic curves after identifying opposite points. Pang’s May paper on shadow lattices asks what can be distinguished from a given observation. His spherical-closure paper asks what happens to directional information on a sphere. Here the quotient and the arithmetic point counts give two explicit observations. Hearthline checked the example on paper and against PARI/GP. [Shadow Lattice and Dispersal Lattice](../corpus/Shadow_Lattice_and_Dispersal_Lattice.pdf) · [The Price of Spherical Closure](../corpus/The_Price_of_Spherical_Closure.pdf)

## The same four points over the rationals

Take $E_d:y^2=x^3-d^2x$ for $d=1,5$. The map to the $x$-line identifies $(x,y)$ with $(x,-y)$. Its branch points are $-d,0,d,\infty$. Use the rational coordinate $u=x/d$ on each quotient. Now the **marked quotient lines already agree over $\mathbf Q$**, with the same four points $-1,0,1,\infty$. Recovering the double cover requires the square root of $d^3(u^3-u)$. The two original curves become isomorphic over $\mathbf Q(\sqrt5)$ via $(x,y)\mapsto(5x,5\sqrt5\,y)$.

The holomorphic one-form $\omega_d=dx/(2y)$ changes sign under negation. Its square descends to the meromorphic quadratic differential
$$q_d=\frac{du^2}{4d(u^3-u)}.$$
It has one simple pole at each branch point, including infinity as substitution $u=1/z$ shows. At a branch point the local double cover has the form $z=t^2$, and $dz^2/z$ pulls back to $4\,dt^2$. The form upstairs is regular there. The pole locations forget the twist, while its coefficient in the chosen coordinates changes by the factor $1/5$. A rational rescaling of the original one-form changes its square by a rational square. This identifies the precise information carried by this marked differential.

## Which primes distinguish the two curves?

For an odd prime $p\ne5$, let $\chi_p$ be its quadratic character with $\chi_p(0)=0$. Counting the affine fibres and the point at infinity gives
$$a_p(E_d)=p+1-\#E_d(\mathbf F_p)=-\sum_{x\bmod p}\chi_p(x^3-d^2x).$$
Changing variables $x=5u$ proves $a_p(E_5)=\chi_p(5)a_p(E_1)$. If $p\equiv3\bmod4$, pairing $u$ with $-u$ cancels the sum for $E_1$. If $p\equiv1\bmod4$, its four rational two-torsion points (including the identity) give $4\mid\#E_1(\mathbf F_p)$, so $a_p(E_1)\equiv2\bmod4$. Quadratic reciprocity gives $\chi_p(5)=-1$ exactly when $p\equiv2,3\bmod5$. Thus the counts differ at precisely the common good primes
$$p\equiv13\ \text{or}\ 17\pmod{20}.$$

| Prime | Points on $E_1$ | Points on $E_5$ |
| ---: | ---: | ---: |
| 3 | 4 | 4 |
| 7 | 8 | 8 |
| 11 | 12 | 12 |
| **13** | **8** | **20** |
| 17 | 16 | 20 |
| **2663** | **2664** | **2664** |

At 13 the Frobenius traces are $6$ and $-6$. This is the first distinguishing point count at a prime of good reduction for both curves. Reduction type distinguishes them at 5 as well. Even though 5 is a nonsquare modulo 2663, the trace that would change sign is already zero.

## Check the ranks without assuming BSD

For $E:y^2=x^3+b x$, descent by the point $(0,0)$ compares $E$ with $E':y^2=x^3-4b x$. The descent map sends a point to the rational squareclass of $x$, sends $(0,0)$ to the class of $b$, and takes the identity to 1. The two isogenies compose to doubling. The kernel of each descent map is the image of the opposite isogeny. For instance the dual map has $x=Y^2/(4X^2)$, and if $x=t^2\ne0$, the preimage equation for $X$ has roots $2x\pm2y/t$. Every squareclass in the image has a squarefree representative dividing $b$ up to sign, by taking valuations in the equation. Both curves being tested have full rational two-torsion, so multiplying the two descent-image sizes gives $2^{r+2}$, where $r$ is the rational rank. [Silverman and Tate, *Rational Points on Elliptic Curves*](https://www.math.brown.edu/johsilve/RPECHome.html)

- For $b=-1$ the first image is $\{1,-1\}$. The partner has $b'=4$, positive nonzero $x$, and image $\{1,2\}$ since $(2,4)$ lies on it. The rank is **zero**.
- For $b=-25$ the first image is $\{1,-1,5,-5\}$, already supplied by the two-torsion. For $b'=100$, the image contains 5 via $(20,100)$. The class 2 would give $N^2=2U^4+50V^4$ for coprime integers $U,V$. With opposite parity this is $2\bmod16$. With both odd it is $20\bmod32$. Neither is a square. This also excludes $10$ by the subgroup law. The image is $\{1,5\}$ and the rank is **one**. The rational point $(-4,6)$ is a generator of the free part in Cremona’s data. [Rank-zero curve data](https://github.com/JohnCremona/ecdata/blob/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allgens/allgens.00000-09999#L58-L59) · [Rank-one curve data](https://github.com/JohnCremona/ecdata/blob/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allgens/allgens.00000-09999#L3892)

## What even the entire L-function forgets

The first descent also gives a stronger test of Pang’s observation. The rationally 2-isogenous curves $y^2=x^3-x$ and $y^2=x^3+4x$ have the same entire elliptic-curve L-function. A rational isogeny induces an isomorphism of rational Tate modules, so the Euler factors agree, including the inertia-invariant factors at bad primes. Their rational-point groups are different. The first has three nonidentity rational points of order two. On the second, $(2,4)$ doubles to $(0,0)$ and has order four. The ranks vanish, and reduction at the good primes 3 and 7 bounds the torsion order by four (the point counts are 4 and 8). The rational groups are therefore $C_2\times C_2$ and $C_4$. This example preserves the full analytic observation while losing the rational torsion-group structure. [Cremona’s two group structures](https://github.com/JohnCremona/ecdata/blob/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/allgens/allgens.00000-09999#L58-L59)

For an independent replay in PARI/GP, `ellrank(ellinit([0,0,0,-d^2,0]))` gives rank bounds $[0,0]$ and $[1,1]$ at $d=1,5$. `ellap(ellinit([0,0,0,-d^2,0]),p)` gives the corresponding traces in the table. BSD concerns the order of vanishing of the global L-function at $s=1$. The rank computations above are algebraic. [Clay Mathematics Institute’s statement](https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/)
