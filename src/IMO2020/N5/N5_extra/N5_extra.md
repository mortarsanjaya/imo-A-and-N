# IMO 2020 N5, Generalized Version

*Note*: Some parts of this generalized problem raises a lot of structures.
Thus, our formatting style will be different.

Fix a commutative (additive) cancellative monoid $M$.
Denote $\N^+ = \{1, 2, 3, \ldots\}$.
We call a function $f : \N^+ \to M$ *additive* if $f(xy) = f(x) + f(y)$ for every $x, y \in \N^+$.
Given an additive map $f : \N^+ \to M$,
1. we say that $f$ is *$n$-good* for a positive integer $n$ if $f(k) = f(n - k)$ for all $k < n$,
2. we say that $f$ is *wide* if $f$ is $p$-good for infinitely many primes $p$,
3. for a prime $p$, we say that $f$ is *$p$-strong* if $f$ is $p^k$-good for every $k \geq 1$.

Our aim is to determine all additive maps $f : \N^+ \to M$ that is $n$-good for infinitely many $n \in \N^+$.




# 1. General results

First, we prove that additive maps that are $n$-good for infinitely many $n$ must either be wide or $p$-strong for some $p$ prime.
The converse obviously holds.

> __Lemma 1.1__:
> Let $f : \N^+ \to M$ be an additive map and $n$ be a positive integer such that $f$ is $n$-good.
> Then $f$ is $d$-good for any $d \in \N^+$ such that $d \mid n$.
>
> __Proof__:
> For any $k < d$,
> $$ f(k) + f(n/d) = f(nk/d) = f(n - nk/d) = f(d - k) + f(n/d). $$
> Cancelling $f(n/d)$ from both sides finishes the proof of the lemma.

> __Theorem 1.2__:
> Suppose that there are infinitely many positive integers $n$ for which $f$ is $n$-good.
> Then, $f$ is either wide or $p$-strong for some prime $p$.
>
> __Proof__:
> Suppose that $f$ is not $p$-strong for any prime $p$.
> For each prime $p$, there exists an integer $a_p \geq 0$ such that $f$ is $p^{a_p}$-good but not $p^{a_p + 1}$-good.
> Then for each positive integer $n$ for which $f$ is $n$-good, by Lemma 1.1, we have $\nu_p(n) \leq a_p$.
>
> If $f$ is not wide either, then $a_p = 0$ for all but finitely many $p$.
> But then every positive integer $n$ such that $f$ is $n$-good must divide $\prod_p p^{a_p} < \infty$.
> The product can be taken only over primes $p$ for which $f$ is $p$-good.
> A contradiction, showing that the lemma holds.

Next, we show that if $f$ is $p$-good for some prime $p$, then $f$ is well-behaved in the following sense.

> __Lemma 1.3__:
> Let $p$ be a prime for which $f$ is $p$-good.
> Then, for any positive integers $k, m < p$, we have $f([km]_p) = f(k) + f(m)$.
>
> __Proof__:
> Proceed by strong induction on $k$.
> The base case $k = 1$ is trivial.
> Now, given some $k_0 < p$, suppose that we have $f([km]_p) = f(k) + f(m)$ for all $k < k_0$ and $m < p$.
> Next, we use strong induction on $m$, with the base case $k_0 m < p$ being trivial.
> So, the induction step is now as follows: suppose that $k_0 m_0 \geq p$, $f([km]_p) = f(k) + f(m)$ holds for all $k < k_0$ and $m < p$, and also it holds for $k = k_0$ and for any $m < m_0$.
> We want to show that $f([k_0 m_0]_p) = f(k_0) + f(m_0)$.
>
> Let $k = \lfloor p/m_0 \rfloor < k_0 < p$.
> We can write $p = k m_0 + r$ for some positive integer $r < m_0$; note that $r$ cannot be zero.
> Since $r < m_0$, by induction hypothesis, we have $f([k_0 r]_p) = f(k_0) + f(r)$.
> But $r = p - k m_0$, so using induction hypothesis,
> $$ f([k_0 k m_0]_p) = f([-k_0 k m_0]_p) = f(k_0) + f(k m_0) = f(k_0) + f(k) + f(m_0). $$
> On the other hand, by induction hypothesis, $f([k_0 k m_0]_p) = f(k) + f([k_0 m_0]_p)$.
> Cancelling out $f(k)$ gives us the desired equality $f([k_0 m_0]_p) = f(k_0) + f(m_0)$.
> Induction step is complete; the lemma is proved.

In particular, this also means that $f([k^t]_p) = t f(k)$ for any $0 < k < p$ and $t \geq 0$, if $f$ is $p$-good with $p$ being a prime.



# 2. Results on $p$-strong maps

The following lemma, together with Lemma 1.3, allows us to characterize $p$-strong maps for any prime $p$.

> __Lemma 2.1__:
> Let $f : \N^+ \to M$ be a $p$-strong additive map.
> Then $f(n) = f([n]_p)$ for any positive integer $n$ coprime with $p$.
>
> __Proof__:
> Proceed by strong induction on $n$.
> The base case is $n < p$, for which the result is trivial since $[n]_p = n$.
> So now, let $n > p$, and suppose that $f(m) = f([m]_p)$ for any $m < n$.
>
> Let $a$ be the unique positive integer such that $p^a < n < p^{a + 1}$.
> Let $k = \lfloor p^{a + 1}/n \rfloor$.
> We have $k < p$ since $p^a < n$.
> Then we have $f(k) + f(n) = f(kn) = f(p^{a + 1} - kn)$, where $p^{a + 1} - kn < n$ by construction of $k$.
> But also, since $k < p$ and $\gcd(n, p) = 1$, we have $\gcd(p^{a + 1} - kn, p) = 1$.
> Applying induction hypothesis, we get $f(k) + f(n) = f([-kn]_p) = f([kn]_p)$.
> But since $k < p$, Lemma 1.3 gives us $f([kn]_p) = f(k) + f([n]_p)$.
> Cancelling $f(k)$ out from both sides gives us $f(n) = f([n]_p)$.
> Induction step is complete; the lemma is proved.

> __Theorem 2.2__:
> An additive map $f$ is $p$-strong if and only if there exists $c \in M$ and a homomorphism $\chi : (\Z/p\Z)^* \to M$ with $\chi(-1) = 0$ such that $f(p^k t) = kc + \chi(\overline{t})$ for all $k \geq 0$ and positive integers $t$ coprime with $p$.
> Here, $\overline{t}$ denotes the reduction of $t$ into $\Z/p\Z$.
>
> __Proof__:
> First, given the corresponding $c$ and $\chi$, we can check that the corresponding $f$ is $p$-strong.
> Indeed, for any $k > 0$ and $0 < m < p^k$, we can write $m = p^t n$ and $p^k - m = p^t (p^{k - t} - n)$ for some $t < k$ and $n$ coprime with $p$.
> Then $f(m) = tc + \chi(\overline{n}) = tc + \chi(-\overline{n}) = f(p^k - m)$ since $\overline{p^{k - t} - n} = \overline{-n} = -\overline{n}$ and $\chi(-1) = 0$.
>
> For the converse, let $f$ be a $p$-strong map, and set $c = f(p)$.
> Then $f(p^k t) = kc + f([t]_p)$ for all $k \geq 0$ and $t$ coprime with $p$ by additivity and Lemma 2.1.
> There is a well-defined function $\chi : (\Z/p\Z)^* \to M$ given by $\chi(\overline{t}) = f([t]_p)$, since for any $t, t' \geq 0$,
> $$ \overline{t} = \overline{t'} \iff t \equiv t' \pmod{p} \iff [t]_p = [t']_p. $$
> Lemma 1.3 shows that $\chi$ must be a homomorphism: $\chi(km) = \chi(k) + \chi(m)$ for any $k, m \in (\Z/p\Z)^*$.
> Finally, $\chi(-1) = f(p - 1) = 0$, since $f$ is $p$-good.

Note that $\chi$ and $c$ uniquely determines $f$.
This brings us to the following structural result.

> __Theorem 2.3__:
> Let $S_p(M)$ be the set of $p$-strong additive maps from $\N^+$ to $M$.
> Then $S_p(M)$ is a commutative cancellative monoid under pointwise addition, and it is isomorphic to $M \times \text{Hom}(\Z/\frac{p - 1}{2}\Z, M)$.
>
> __Proof__:
> It is easy to check that $S_p(M)$ is a commutative cancellative monoid; all the properties are inherited from $M$.
> By Theorem 2.2, $S_p(M) \cong M \times G$, where $G$ is the monoid of maps $\chi : (\Z/p\Z)^* \to M$ such that $\chi(-1) = 0$.
> It is easy to see that $G \cong \text{Hom}((\Z/p\Z)^* / \{-1, 1\}, M)$.
> Finally, $(\Z/p\Z)^* / \{-1, 1\} \cong \Z/\frac{p - 1}{2}\Z$.



# 3. Results on wide maps

Unlike $p$-strong maps, wide maps are rather sporadic, except for the case where $M$ is torsion-free, where zero is the only wide map.
Indeed, by Lemma 1.3 and Fermat's little theorem, given a prime $p$ and a $p$-good additive map $f$, we have $(p - 1) f(k) = f([k^{p - 1}]_p) = f(1) = 0$ for any $0 < k < p$.
Then, when $M$ is torsion-free, we get $f(k) = 0$ for all $0 < k < p$.
If $f$ is wide, for each $k > 0$ we get $f(k) = 0$ by taking $p$ large enough.

On the other hand, we give a construction of a non-zero wide map below.

> First, we define a sequence of primes $p_1 < p_2 < p_3 < p_4 < \ldots$ inductively as follows.
> Take $p_1 = 5$.
> Next, suppose that we have define $p_n$ for some $n \geq 1$.
> We take $p_{n + 1}$ to be a prime number greater than $p_n$ such > that $\left(\frac{k}{p_{n + 1}}\right) = \left(\frac{k}{p_n}\right)$ for all $k < p_n$.
> We now show that such $p_{n + 1}$ must exist.
>
> __Proof__: It is well-known that $\left(\frac{a}{4a + b}\right) = \left(\frac{a}{b}\right)$ for all $a, b > 0$ with $\gcd(a, b) = 1$.
> As a result, for any $k < p_n$ and $a > 0$, we have
> $$ \left(\frac{k}{4a (p_n - 1)! + p_n}\right) = \left(\frac{k}{p_n}\right). $$
> But $4(p_n - 1)!$ is coprime with $p_n$ since $p_n \geq p_1 = 5$, so Dirichlet's theorem on arithmetic progressions mean that we can take $a > 0$ such that $a (p_n - 1)! + p_n$ is prime.
> We can then set $p_{n + 1} = a (p_n - 1)! + p_n$, as desired.
> $\square$
>
> By the property of the sequence, there exists a function $g : \N^+ \to \{-1, 1\}$ such that $g(k) = \left(\frac{k}{p_n}\right)$ for any $n \geq 1$ such that $k < p_n$.
> This function is multiplicative; for any $k$ and $m$, taking $n$ large enough gives us
> $$ g(k) g(m) = \left(\frac{k}{p_n}\right) \left(\frac{m}{p_n}\right) = \left(\frac{km}{p_n}\right) = g(km). $$
> We set $f(k) = 1$ if $g(k) = -1$ and $f(k) = 0$ if $g(k) = 1$.
> Working modulo $2$, since $g$ is multiplicative, $f$ is additive.
> Furthermore, for each $n \geq 1$, $f$ is $p_n$-good since one can also check that $g$ is $p_n$-good.
> Thus, $f$ is wide.
> But $f \neq 0$, since $f(2) = 1$.

My comment: I think it is possible to construct a non-zero wide additive map whenever $M$ is not torsion-free.
To show this property, it suffices to construct one for $M = \Z/p\Z$ for any prime $p$.
Our above construction is for the case $p = 2$.
Similar constructions should work, although it is not clear whether the corresponding symbol for $p^{\text{th}}$ roots is periodic with respect to the modulus argument.



# 4. Distinction between $p$-strong and wide maps

It turns out that a map cannot be $p$-strong for more than one value of $p$ unless the map is zero.
Similarly, an additive map cannot be wide and also $p$-strong for some $p$ unless it is zero.
We prove the result below, with the following lemma trivializing them.

> __Lemma 4.1__:
> Let $p$ be a prime, and let $f : \N^+ \to M$ be a $p$-strong homomorphism.
> Suppose that $f$ is $n$-good for some $n > p^2$ coprime with $p$.
> Then $f \equiv 0$.
>
> __Proof__:
> For any $n \in \N^+$, we can write $n = p^k t$ for some $k \geq 0$ and $t$ coprime with $p$.
> Lemma 2.1 then yields $f(n) = k f(p) + f([t]_p)$ with $[t]_p < p$.
> Thus it suffices to show that $f(n) = 0$ for any $n \leq p$.
>
> Since $f$ is $n$-good, for each $k \leq p$ we have $f(pk) = f(n - pk)$.
> But since $\gcd(n, p) = 1$ and $f$ is $p$-strong, Lemma 4 yields $f(n - pk) = f([n]_p)$, which does not depend on $k$.
> So, we get $f(p) + f(k) = f([n]_p) = f(p) + f(1) = f(p)$, which means $f(k) = 0$ for all $k \leq p$, as desired.

Indeed, if $f$ is $p$-strong and $q$-strong for some primes $p < q$, then we can apply Lemma 4.1 with $n = q^2$.
If $f$ is wide and $p$-strong for some $p$, we can apply Lemma 4.1 by picking any suitable prime greater than $p^2$ for $n$.

One can reduce the lower bound to $\frac{p(p - 1)}{2}$.
The same proof above gives $f(k) = 0$ for all $k \leq \frac{p - 1}{2}$, and the fact that $f$ is $p$-good gives us $f(k) = 0$ for all $k < p$.
Since $f$ is also $n$-good with $p \nmid n$, we get $f(p) = f(n - p) = f([n]_p) = 0$.

Using Thue's lemma, one can reduce the bound even further to $n > p^{3/2}$.
Indeed, direct computations now give $f(k) = 0$ just for $k < \sqrt{p}$.
For $\sqrt{p} < k < p$, by Thue's lemma, there exists non-zero integers $a$ and $b$ such that $ak \equiv b \pmod{p}$ and $|a|, |b| < \sqrt{p}$.
Now let $a' = a$ if $a > 0$ and $a' = p - a$ if $a < 0$; define $b'$ similarly.
Then $f(a') = f(b') = 0$, and $a'b' \equiv \pm k \pmod{p}$, so $f(k) = 0$ as well by Lemma 2.1.
