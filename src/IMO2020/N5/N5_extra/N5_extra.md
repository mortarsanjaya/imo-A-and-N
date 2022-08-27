# IMO 2020 N5, Generalized Version

*Note*: Some parts of this generalized problem raises a lot of structures.
Thus, our formatting style will be different.

Fix a commutative (additive) cancellative monoid $M$.
Denote $\N^+ = \{1, 2, 3, \ldots\}$.
We call a function $f : \N^+ \to M$ *additive* if $f(xy) = f(x) + f(y)$ for every $x, y \in \N^+$.
Given a function $f : \N^+ \to M$, a positive integer $n$ is said to be *$f$-good* if $f(k) = f(n - k)$ for all $k < n$.
Our aim is to determine all additive maps $f : \N^+ \to M$ with infinite many $f$-good positive integers.

We will borrow terminologies introduced in the extra file `extra/number_theory/divisor_closed_prop.lean`.
For this `.md` file only, we say that $f : \N^+ \to M$ is wide if the $f$-good predicate is wide.
Similarly, for any $p$ prime, we say that $f$ is $p$-strong if the $f$-good predicate is strong.



# 1. General results

Let $f : \N^+ \to M$ be an additive map.
It is easy to see that the set of $f$-good positive integers is divisor-closed.
Indeed, fix an arbitrary $f$-good positive integer $n$ and let $d$ be a factor of $n$.
Then for any $k < d$,
$$ f(k) + f(n/d) = f(nk/d) = f(n - nk/d) = f(d - k) + f(n/d). $$
Cancelling $f(n/d)$ from both sides shows us that $d$ is $f$-good.
By the result in `extra/number_theory/divisor_closed_prop.lean`, $f$ is either wide or $p$-strong for some $p$ prime.

Next, we show a property of $f$ when a prime is $f$-good.

> __Lemma 1__:
> Let $p$ be an $f$-good prime.
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



# 2. Results on $p$-strong maps

The following lemma, together with Lemma 1, allows us to characterize $p$-strong maps for any prime $p$.

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
> But since $k < p$, Lemma 1 gives us $f([kn]_p) = f(k) + f([n]_p)$.
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
> Lemma 1 shows that $\chi$ must be a homomorphism: $\chi(km) = \chi(k) + \chi(m)$ for any $k, m \in (\Z/p\Z)^*$.
> Finally, $\chi(-1) = f(p - 1) = 0$, since $p$ is $f$-good.



# 3. Results on wide maps

Unlike $p$-strong maps, wide maps are rather sporadic, except for the case where $M$ is torsion-free, where zero is the only wide map.
Indeed, let $f$ be an additive map and $p$ be an $f$-good prime.
Then by Lemma 1 and Fermat's little theorem, we have $(p - 1) f(k) = f([k^{p - 1}]_p) = f(1) = 0$ for any $0 < k < p$.
When $M$ is torsion-free, we get $f(k) = 0$ for all $0 < k < p$.
If $f$ is wide, for each $k > 0$ we get $f(k) = 0$ by taking $p$ large enough.

On the other hand, we give a construction of a non-zero wide map below.

> First, we define a sequence of primes $p_1 < p_2 < p_3 < p_4 < \ldots$ inductively as follows.
> Take $p_1 = 5$.
> Next, suppose that we have define $p_n$ for some $n \geq 1$.
> We take $p_{n + 1}$ to be a prime number greater than $p_n$ such > that $\left(\frac{k}{p_{n + 1}}\right) = \left(\frac{k}{p_n}\right)$ for all $k < p_n$.
> We now show that such $p_{n + 1}$ must exist.
>
> __Proof__:
> It is well-known that $\left(\frac{a}{4a + b}\right) = \left(\frac{a}{b}\right)$ for all $a, b > 0$ with $\gcd(a, b) = 1$.
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
> We also have $f \neq 0$, since $f(2) = 1$.
> Finally, it is easy to see that $p_n$ is $f$-good for each $n \geq 1$, which implies that $f$ is wide.

My comment: I think it is possible to construct a non-zero wide additive map whenever $M$ is not torsion-free.
To show this property, it suffices to construct one for $M = \Z/p\Z$ for any prime $p$.
Our above construction is for the case $p = 2$.
Similar constructions should work, although it is not clear whether the corresponding symbol for $p^{\text{th}}$ roots is periodic with respect to the modulus argument.



# 4. Distinction between $p$-strong and wide maps

It turns out that a map cannot be $p$-strong for more than one value of $p$ unless the map is zero.
Similarly, an additive map cannot be wide and also $p$-strong for some $p$ unless it is zero.
In fact, we have an even more general result, trivializing both the above results.

> __Theorem 4.1__:
> Let $p$ be a prime, and let $f : \N^+ \to M$ be a $p$-strong additive map.
> Suppose that there exists an $f$-good positive integer $n > p$ coprime with $p$.
> Then $f \equiv 0$.
>
> __Proof__:
> Using characterizations of $p$-strong additive maps, we write $f = n \mapsto \nu_p(n) \cdot c + \chi(n/\nu_p(n))$ for some $c \in M$ and homomorphism $\chi : (\Z/p\Z)^* \to M$ with $\chi(-1) = 0$.
> Clearly, we have $f = 0$ if and only if $c = 0$ and $\chi = 0$, if and only if $f(p) = 0$ and $f(k) = 0$ for each $k < p$.
> Thus, it suffices to show that $f(k) = 0$ for each $k \leq p$.
>
> For any $0 < x < p$ such that $x \not\equiv n \pmod{p}$, we have $\chi(x) = \chi(n - x)$ since $n$ is $f$-good.
> Then we have $\chi(nx^{-1} - 1) = 0$.
> As $x$ ranges with the above restriction, the value of $nx^{-1} - 1$ modulo $p$ ranges over all non-zero values except $-1$ and $0$.
> Thus, we get $f(k) = 0$ for $k < p - 1$.
>
> For $k = p - 1$, we get $f(p - 1) = f(1) = 0$ since $p$ is $f$-good.
> Finally, for $k = p$, we get $f(p) = f(n - p) = f([n]_p) = 0$ since $n$ is $f$-good and coprime with $p$.

Indeed, if $f$ is $p$-strong and $q$-strong for some primes $p < q$, then we can apply Theorem 4.1 with $n = q$.
If $f$ is wide and $p$-strong for some $p$, we can apply Theorem 4.1 by picking any suitable prime greater than $p$ for $n$.

Without using characterizations of $p$-strong maps, one could still obtain $f \equiv 0$ with bound $n > p^2$.
The idea is that we have $f(kp) = f(n - kp) = f(n)$ for each $k < n/p$, so that $f(k) = 0$ for each $k < n/p$.
A smart use of the $p$ being $f$-good brings the bound down to $n > \frac{p(p - 1)}{2}$.
Using Thue's lemma, we can lower the bound even further to $n > p^{3/2}$.
