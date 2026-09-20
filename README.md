# On Erdős Problem #1213 (JSP-001018): equal sums of two distinct consecutive blocks

**Author.** sweetsky123 (GitHub). Written 2026-09-19.
This write-up was prepared with AI assistance; the disclosure is repeated at the end.

**Attribution.** The problem below is [Erdős Problem #1213](https://www.erdosproblems.com/1213), listed as JSP-001018 in [The Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards). The affirmative answer was first proved by N. Hegyvári in [[He86]](#references). This note is an independent, self-contained proof of the same affirmative answer, with an explicit admissible threshold

$$F(a,K)  =  4^{K} a  +  2K\cdot 16^{K}.$$

No priority over [He86] is claimed. The argument below is an elementary
"sliding-window pigeonhole" exposition and does not use any result from [He86].

## The problem

As stated at [erdosproblems.com/1213](https://www.erdosproblems.com/1213):

> Let $a,K\geq 1$. Does there exist $f(a,K)$ such that, if
> $a=a_1<\cdots<a_s$ is a sequence of integers with $a_s> f(a,K)$ and with
> bounded gaps $a_{i+1}-a_i\leq K$, then there are two distinct intervals
> $I$ and $J$ such that $\sum_{i\in I}a_i=\sum_{j\in J}a_j$?

The catalog entry JSP-001018 paraphrases this as: *must every sufficiently long
integer sequence with bounded gaps have two distinct consecutive blocks with
equal sums?* Here a "consecutive block" is an interval of consecutive indices
$\lbraceu,u+1,\dots,v\rbrace$, and "two distinct" blocks means the two index intervals are
not identical. (The problem does **not** require the two blocks to be disjoint,
and the proof below does not need disjointness.)

The answer is **yes**:

## Theorem 1

Let $a$ and $K$ be positive integers, and define

$$F(a,K) := 4^{K} a + 2K\cdot 16^{K}.$$

Let $a_1<a_2<\cdots<a_s$ be a strictly increasing sequence of **integers** such that

1. $a_1 = a$;
2. $a_{i+1}-a_i \le K$ for every $1\le i<s$;
3. $a_s > F(a,K)$.

Then there exist two **distinct** intervals of indices $I\neq J$, each of the form
$\lbraceu,u+1,\dots,v\rbrace$ with $1\le u\le v\le s$, such that

$$\sum_{i\in I} a_i  =  \sum_{j\in J} a_j .$$

In fact, the two intervals can be taken to have **different lengths**.

Taking $f(a,K):=F(a,K)$ answers the problem affirmatively. Since
$F(a,K)\le 2a\cdot 256^{K}=a\cdot e^{O(K)}$ (Remark 1 below), the threshold has the
same shape as the bound $f(a,K)\ll a e^{O(K)}$ recorded for [He86] at
[erdosproblems.com/1213](https://www.erdosproblems.com/1213).

## Notation

Throughout the proof, $a,K,s$ and the sequence $(a_i)$ are as in Theorem 1, and
indices are 1-based. For $1\le u\le v\le s$ write

$$S(u,v) := a_u + a_{u+1} + \cdots + a_v$$

for the sum over the index interval $\lbraceu,\dots,v\rbrace$ (so $S(u,u)=a_u$). Because
$a_1=a\ge 1$ and the sequence is strictly increasing, every $a_i\ge 1$; in
particular all interval sums are positive.

Put

$$M := 4^{K}\ (\text{so } M\ge 4),\qquad W := K M^{2} = K\cdot 16^{K},\qquad X := S(1,M)=a_1+\cdots+a_M,$$

and note $F(a,K) = Ma + 2W$.

## The proof

**Lemma 1 (telescoping the gap bound).** *For all $1\le i\le j\le s$,
$a_j - a_i \le K(j-i)$. In particular, $a_i \le a + K(i-1)$ for every $i$.*

*Proof.* Sum the inequalities $a_{t+1}-a_t\le K$ over $t=i,\dots,j-1$; the terms
telescope to $a_j-a_i$. The second statement is the case $i=1$, using $a_1=a$. ∎

**Lemma 2 (the sequence is long).** *$s > M$.*

*Proof.* Suppose $s\le M$. By Lemma 1,
$$a_s \le a + K(s-1) \le a + KM .$$
Since $M\ge 1$ we have $a \le Ma$ and $KM \le KM^{2}\cdot 2 = 2W$ (indeed $KM\le KM^2$ as $M \ge 1$), hence
$$a_s \le Ma + 2W = F(a,K),$$
contradicting hypothesis 3 of Theorem 1. ∎

**Lemma 3 (first and last window sums).** *For every $1\le r\le M$:*
1. $S(1,r) \le X$;
2. $S(s-r+1, s) \ge a_s > X + W$.

*Proof.* (1): $r\le M$ and all terms are positive, so $S(1,r)\le S(1,M)=X$.
(2): the term $a_s$ occurs in $S(s-r+1,s)$ and all terms are positive, so
$S(s-r+1,s)\ge a_s$. The inequality $a_s > X+W$ follows from hypothesis 3 and
$$X+W  \le  F(a,K):$$
indeed, by Lemma 1, $a_i\le a+K(i-1)\le a+KM$ for $1\le i\le M$, so
$$X=\sum_{i=1}^{M} a_i  \le  M(a+KM) = Ma + KM^{2}  \le  Ma + 2KM^{2} = F(a,K),$$
and $W=KM^{2}\ge 0$. ∎

**Lemma 4 (sliding-window step).** *Fix $1\le r\le M$, and for $1\le i\le s-r+1$
let $T_i := S(i, i+r-1)$ be the sum of the window of length $r$ starting at
index $i$. Then for each $1\le i < s-r+1$:*
$$0 < T_{i+1}-T_i \le K\cdot r .$$

*Proof.* $T_{i+1}-T_i = a_{i+r}-a_i$, which is positive because the sequence is
strictly increasing, and at most $Kr$ by Lemma 1. ∎

**Lemma 5 (every bin is hit).** *Let $1\le r\le M$ and let $q\ge 0$ be an integer
with $(q+1) K r \le W$. Then there exists an index $i$ with $1\le i\le s-r+1$
such that*
$$X + q K r  \le  T_i  <  X + (q+1) K r .$$

*Proof.* Let $T := X + qKr$ and consider
$A := \lbrace  i\in\lbrace1,\dots,s-r+1\rbrace : T_i \ge T  \rbrace$.
The set $A$ is nonempty: by Lemma 3(2),
$T_{s-r+1} = S(s-r+1,s) > X+W \ge X+(q+1)Kr \ge T$.
Let $i$ be the **least** element of $A$, so that $T_i\ge T$.

Suppose, for contradiction, that $T_i \ge X+(q+1)Kr$. Since
$T_1 = S(1,r)\le X < X+(q+1)Kr$ by Lemma 3(1) (note $(q+1)Kr\ge 1>0$), index $i$
cannot be $1$; hence $i\ge 2$. By the minimality of $i$, $T_{i-1} \lt T$. By Lemma 4,
$T_i \le T_{i-1}+Kr < T+Kr = X+(q+1)Kr$, contradicting $T_i\ge X+(q+1)Kr$.
Therefore $T_i < X+(q+1)Kr$, which together with $T_i \ge T$ proves the claim. ∎

**Lemma 6 (harmonic slot count).** *With $M = 4^{K} = 2^{2K}$,*
$$\sum_{r=1}^{M} \left\lfloor \frac{M^{2}}{r} \right\rfloor  >  K M^{2}  =  W .$$

*Proof.* First, the classical estimate $H_{2^{m}} \ge 1 + \tfrac{m}{2}$ for
integers $m\ge 0$, where $H_n := \sum_{r=1}^{n} \tfrac 1r$: it holds for $m=0$
($H_1=1$), and passes from $m$ to $m+1$ because
$$H_{2^{m+1}} - H_{2^{m}}  =  \sum_{j=2^{m}+1}^{2^{m+1}} \frac1j  \ge  2^{m}\cdot\frac{1}{2^{m+1}}  =  \frac12 .$$
With $m = 2K$ this gives $H_M \ge 1+K$. Therefore
$$\sum_{r=1}^{M} \left\lfloor \frac{M^{2}}{r}\right\rfloor  \ge  \sum_{r=1}^{M}\left(\frac{M^{2}}{r}-1\right)  =  M^{2}H_M - M  \ge  M^{2}(1+K) - M  =  W + (M^{2}-M)  >  W,$$
using $\lfloor x\rfloor \ge x-1$ and $M\ge 2$ (indeed $M = 4^K\ge 4$). ∎

**Proof of Theorem 1.** Consider the set of *slots*

$$\Sigma := \left\lbrace  (r,q)  :  1\le r\le M,  q \text{ an integer with } 0\le q < \left\lfloor \tfrac{M^{2}}{r} \right\rfloor  \right\rbrace.$$

For every slot $(r,q)\in\Sigma$ we have
$q+1 \le \lfloor M^{2}/r\rfloor \le M^{2}/r$, hence
$(q+1)Kr \le KM^{2}=W$; so Lemma 5 applies and yields an index
$i(r,q) \in \lbrace1,\dots,s-r+1\rbrace$ whose window sum

$$\sigma(r,q) := T_{i(r,q)}$$

satisfies

$$X + q Kr  \le  \sigma(r,q)  <  X + (q+1) Kr. \tag{†}$$

In particular every $\sigma(r,q)$ is an integer in the half-open interval
$[X, X+W)$, which contains exactly $W$ integers. By Lemma 6, $|\Sigma| > W$, so
by the pigeonhole principle there exist two **distinct** slots
$(r,q)\neq(r',q')$ in $\Sigma$ with

$$\sigma(r,q)  =  \sigma(r',q')  =:  \sigma .$$

We first claim that $r\neq r'$. Suppose $r=r'$. Then $Kr\ge 1$, and $(\dagger)$
applied to both slots gives
$$q Kr \le \sigma - X < (q+1) Kr
\qquad\text{and}\qquad
q' Kr \le \sigma - X < (q'+1) Kr .$$
Dividing by $Kr>0$ and taking floors,
$\big\lfloor (\sigma-X)/(Kr)\big\rfloor = q = q'$, contradicting
$(r,q)\neq(r',q')$. Hence $r\neq r'$.

Now put $i := i(r,q)$ and $i' := i(r',q')$, and define the index intervals

$$I := \lbracei, i+1,\dots,i+r-1\rbrace, \qquad J := \lbracei', i'+1,\dots,i'+r'-1\rbrace .$$

Both are nonempty intervals contained in $\lbrace1,\dots,s\rbrace$, because
$1\le i\le s-r+1$ and $1\le i'\le s-r'+1$. Since $r\neq r'$, the intervals $I$
and $J$ contain different numbers of elements and are therefore distinct.
Finally,

$$\sum_{t\in I} a_t  =  S(i, i+r-1)  =  T_i  =  \sigma  =  T_{i'}  =  S(i', i'+r'-1)  =  \sum_{t\in J} a_t .$$

Thus $I\neq J$ are two distinct intervals of indices with equal sums, and they
even have different lengths. This completes the proof. ∎

## Remarks

1. **Shape of the bound.** For all $a,K\ge 1$: $4^{K}a \le 256^{K}a$; and
   $2K\cdot 16^{K} \le 16^{K}\cdot 16^{K} = 256^{K} \le a\cdot 256^{K}$, where
   $2K\le 16^{K}$ holds for $K=1$ and is preserved inductively
   ($16^{K+1} = 16\cdot 16^{K} \ge 16\cdot 2K \ge 2(K+1)$ for $K\ge 1$).
   Hence $F(a,K)\le 2a\cdot 256^{K} = a\cdot e^{(8\ln 2)K}$, the same
   $a e^{O(K)}$ shape as in [He86]. The problem only asks for the existence of
   some threshold, and no attempt is made to optimize $F$.

2. **Independence of the exposition.** The proof uses only positivity,
   strict monotonicity, the gap bound and a pigeonhole count. It does not
   import or reproduce any argument from [He86]; the statement proved and the
   recorded shape of the bound are consistent with it.

3. **What "distinct" means.** The two intervals produced have different
   lengths, which is stronger than "distinct". The problem does not require
   disjointness, and the two intervals produced may or may not overlap.

4. **Computational spot-check (not part of the proof).** For
   $(a,K)\in\lbrace(1,1),(2,1),(3,1),(5,1),(10,1),(1,2),(2,2),(3,2),(1,3),(2,3)\rbrace$
   a complete depth-first enumeration of all sequences satisfying conditions 1–2
   of Theorem 1 whose interval sums are pairwise distinct (the search trees
   terminate in this range) found maximal last terms
   $3,5,7,11,17,7,8,11,20,23$ respectively — each far below the corresponding
   $F(a,K)=36,40,44,52,72,1040,1056,1072,24640,24704$. This is a sanity check
   only; the proof above does not rely on it.

## References

- **[He86]** N. Hegyvári, *On consecutive sums in sequences*, Acta Mathematica
  Hungarica **48** (1986), 193–200 — as recorded in the JSP-001018 catalog entry
  and at erdosproblems.com. The present note neither reproduces nor depends on
  its contents.
- [Erdős Problem #1213](https://www.erdosproblems.com/1213), accessed 2026-09-19.
- [The Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards),
  entry JSP-001018 (`problems/catalog-1001-1022.md`).

---

*Disclosure: this write-up was prepared with AI assistance, reviewed and adopted
by the account owner (sweetsky123), who submits it as their own exposition of
the solution.*
