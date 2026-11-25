# Why a better fit has to reopen old answers

Christopher Daniel Pang and Hearthline · 25 November 2026

At the first cutoff the fit $F(k)=2b_2(k)$ is exactly one on **every odd row**, and zero on every even row. Can we correct an even row while keeping all those earlier answers exact? This asks a concrete question about PAL's distinction between retaining what happened and transporting a current prediction. The fit is any finite linear combination of $b_d(k)=(k\bmod d)/d$ with moduli $d\ge2$. The proof works for arbitrary real weights; the Lean version uses the rational coefficients required by our RH endpoint.

**No finite correction can change even one even prediction while preserving all odd predictions.** In fact, the least possible worst error on the odd rows among finite fits satisfying $F(2)=1$ is **exactly $1/2$**.

## The half-tick reflection

Let $L$ be a positive even common multiple of all moduli in the fit. Given $0\le k<L$, the row paired with $k$ is $L-1-k$. If $k$ displays the digit $r$ on a $d$-dial, the paired row displays $d-1-r$. Their readings add to $(d-1)/d$, the reading at $L-1$. Thus
$$
F(k)+F(L-1-k)=F(L-1).
$$
If $k$ is even, both $L-1-k$ and $L-1$ are odd. If the odd predictions all equal one, the right-hand prediction minus its paired prediction is zero. Any extra laps are covered by periodicity. Equivalently, the odd rows determine **every** even prediction of a finite residue fit. Its full squared error under the frozen-odd condition is $\sum_{j\ge1}1/[2j(2j+1)]=1-\log2$. [Digit reflection](PALRH/Frames.lean) · [Whole-family statement](PALRH.lean)

In particular put $k=2$ and take an even common period $L\ge4$. When $F(2)=1$,
$$
[1-F(L-3)]-[1-F(L-1)]=1 .
$$
At least one of these named old odd rows has error of magnitude at least $1/2$. If the fit only approximates row 2, the same lower bound becomes $|F(2)|/2$. A convergent sequence of full fits forces $F(2)\to1$ because row 2 has positive mass $1/6$. Each fixed odd row then approaches target while an odd error of nearly half a unit remains somewhere. This localizes a residue that has to move out to less heavily weighted visits. It does not give the sum of all moving residues.

## Attaining the price

Take $F=b_2+(3/2)b_3$. On rows $1,2,3,4,5,6$ its errors $1-F$ are respectively $0,0,1/2,1/2,-1/2,1$. These repeat. Row 2 is corrected, the maximum odd error is exactly half a unit, and the odd witness pair 3 and 5 attains the difference. Lean also proves from the first 256 rows and a bound for every later row that the full weighted squared error of this fit is strictly below $1/6$. Thus this use of the reopened predictions buys a strict improvement over any fit preserving all earlier odd predictions. [Formal theorem and explicit finite witness](PALRH.lean)

For any integer $p>2$, another unconditional update starts from the old fit $2b_2$ and adds $a b_p$ with $a=1/(3p)$. The old residual is nonnegative everywhere. Row 2 alone contributes $(1/6)(2/p)=a$ to its overlap with $b_p$. The whole squared norm of $b_p$ is at most one. Expanding the square shows a decrease of **at least $a^2=1/(9p^2)$** across all visits. After the update the residual can take either sign, so the positivity argument has to be reopened before it is used again. [All-row Lean proof](PALRH/Gain.lean)

## Unresolved

Place the compulsory old-row changes where they cost little **in total** over every lap, while continuing to correct the actual remaining error. The sharp half-unit displacement is a constraint on the construction and a reason to change the freeze strategy. The [fresh-prime transfer](fresh-prime-transfer.md) prices the next signed correction after the old columns have been refit.
