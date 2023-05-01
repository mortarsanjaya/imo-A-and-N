# IMO 2020 N5, Generalized Version

*Note*: This generalized problem raises some extra structures.
Thus, our formatting style will be different.

Denote $\N^+ = \{1, 2, 3, \ldots\}$.
Fix a not-necessarily integral additive monoid $M$.
We call a function $f : \N^+ \to M$ *additive* if $f(xy) = f(x) + f(y)$ for every $x, y \in \N^+$ and $f(1) = 0$.
Note that the criterion $f(1) = 0$ can be deduced from the previous criterion if $M$ is integral; indeed, $f(1) = f(1) + f(1)$ then forces $f(1) = 0$.

Given a function $f : \N^+ \to M$, a positive integer $n$ is said to be *$f$-good* if $f(k) = f(n - k)$ for all $k < n$.
Our aim is to determine all additive maps $f : \N^+ \to M$ with infinitely many $f$-good positive integers, when $M$ is integral.

We will borrow terminologies introduced in the extra file `extra/number_theory/divisor_closed_prop.lean`.
For this `.md` file only, we say that $f : \N^+ \to M$ is wide if the $f$-good predicate is wide.
Similarly, for any $p$ prime, we say that $f$ is $p$-strong if the $f$-good predicate is strong.

For a fixed prime $p$, for any $k \geq 0$, let $\overline{k}$ denote the unique non-negative integer $c$ such that $k \equiv c \pmod{p}$.
The context at which it is applied is usually clear.



# $p$-regular maps

For this section, we do not assume that $M$ is integral.

Let $p$ be a prime number, $c \in M$, and $\chi : (\Z/p\Z)^* \to M$ be a monoid homomorphism.
We denote $f = R_p(c, \chi)$ as the map defined by $f(p^k t) = kc + \chi(\overline{t})$ for all positive integers $t$ coprime with $p$ and $k \geq 0$.
Here, $\overline{t}$ denotes the reduction of $t$ modulo $p$ in $(\Z/p\Z)^*$.
It is easy to check that $f$ is additive map.
An additive map that equals $R_p(c, \chi)$ for some $c$ and $\chi$ is called a *$p$-regular map*.

The following lemma characterizes $p$-regular maps for a fixed prime $p$.

> __Lemma 1.1__:
> An additive map $f : \N^+ \to M$ is regular if and only if $f(t) = f(\overline{t})$ for any $t$ coprime with $p$.
>
> __Proof__:
> For any $c \in M$, $\chi : (\Z/p\Z)^* \to M$, and $t \in \N^+$ coprime with $p$, by definition,
> $$ R_p(c, \chi)(t) = \chi(\overline{t}) = R_p(c, \chi)(\overline{t}). $$
> We use slight abuse of notation; the first $\overline{t}$ denotes reduction of $t$ modulo $p$ in $\Z/p\Z$, while the second one denotes reduction in $\N^+$.
> 
> Conversely, suppose that $f(t) = f(\overline{t})$ for any $t$ coprime with $p$.
> Define $\chi : (\Z/p\Z)^* \to M$ by $\chi(\overline{t}) = f(t)$ for any $t$ coprime with $p$, and take $c = f(p)$.
> Note that $\chi$ is well-defined since the value of $f(t)$ only depends on the value of $\overline{t}$ for $t$ coprime with $p$.
> To show that $\chi$ is a monoid homomorphism, first one see that $\chi(1) = f(1) = 0$.
> Note that $f(1) = 0$ necessarily holds since $M$ is assumed to be integral.
> Next, any element of $(\Z/p\Z)^*$ can be represented as $\overline{k}$ for some $k \in \N^+$ coprime with $p$.
> For any $k, m \in \N^+$ coprime with $p$, we have $f(km) = f(k) + f(m)$.
> Reducing modulo $p$ gives us $\chi(\overline{km}) = \chi(\overline{k}) + \chi(\overline{m})$.
> This shows that $\chi$ is indeed a monoid homomorphism.
>
> Finally, we check that $f = R_p(c, \chi)$.
> Indeed, take an arbitrary positive integer $n = p^k t$, where $k \geq 0$ and $t$ is coprime with $n$.
> Then $f(n) = k f(p) + f(t) = k f(p) + f(\overline{t})$.
> On the other hand, by definition, $R_p(c, \chi)(n) = kc + \chi(\overline{t})$.
> But $c = f(p)$ and $\chi(\overline{t}) = f(t)$, which means $f(n) = R_p(c, \chi)(n)$.

We have one more result: the set of $p$-regular additive maps are independent across distinct $p$ in the sense that the only additive map that is $p$-regular for more than one prime $p$ is the zero map.

> __Lemma 1.2__:
> Let $f : \N^+ \to M$ be an additive map that is $p$-regular and $q$-regular for some distinct primes $p$ and $q$.
> Then $f \equiv 0$.
>
> __Proof__:
> Without loss of generality, suppose that $q > p$.
> By $p$-regularity, $f(q + pk) = f(q + p) = f(q)$ for all $1 \leq k \leq p$.
> By $q$-regularity, dividing by $q$, we get $f(pk) = f(p)$.
> While we cannot cancel out $f(p)$ from both sides directly, there is a work-around solution.
> Since $p$ and $q$ are coprime, there exists $n \in \N^+$ such that $np \equiv 1 \pmod{q}$.
> We have $f(npk) = f(np)$, and then we get $f(k) = f(1) = 0$ by $q$-regularity.
> Thus, this shows that $f(k) = 0$ for all $1 \leq k \leq p$.
>
> Finally, for any $n \in \N^+$, we can write $n = p^k t$ where $k \geq 0$ and $t$ is coprime with $p$.
> Then $f(n) = k f(p) + f(\overline{t}) = k \cdot 0 + 0 = 0$ by $p$-regularity.

The $p$-regular maps appear in the classification of $p$-strong additive maps.
In particular, all of them are $p$-regular, and given $f = R_p(c, \chi)$, $f$ is $p$-strong iff $\chi(-1) = 0$.



# Main results

For this section, we assume that $M$ is integral.

Let $f : \N^+ \to M$ be an additive map.
It is easy to see that the set of $f$-good positive integers is divisor-closed.
Indeed, fix an arbitrary $f$-good positive integer $n$ and let $d$ be a factor of $n$.
Then for any $k < d$,
$$ f(k) + f(n/d) = f(nk/d) = f(n - nk/d) = f(d - k) + f(n/d). $$
Cancelling $f(n/d)$ from both sides shows us that $d$ is $f$-good.
By the result in `extra/number_theory/divisor_closed_prop.lean`, $f$ is either wide or $p$-strong for some $p$ prime.
Before we prove the main results, we prove one important lemma.

> __Lemma 2.1__:
> Let $p$ be an $f$-good prime.
> Then, for any positive integers $k, m < p$, we have $f(\overline{km}) = f(k) + f(m)$.
>
> __Proof__:
> We proceed by two layers of induction; first on $k$ and second on $m$.
> The base case $k = 1$ is trivial.
> Now, given some $k_0 < p$, suppose that we have $f(\overline{km}) = f(k) + f(m)$ for all $k < k_0$ and $m < p$.
> Next, we use strong induction on $m$, with the base case $k_0 m < p$ being trivial.
> So, the induction step is now as follows: suppose that $k_0 m_0 \geq p$, $f(\overline{km}) = f(k) + f(m)$ holds for all $k < k_0$ and $m < p$, and also it holds for $k = k_0$ and for any $m < m_0$.
> We want to show that $f(\overline{k_0 m_0}) = f(k_0) + f(m_0)$.
>
> Let $k = \lfloor p/m_0 \rfloor < k_0 < p$.
> We can write $p = k m_0 + r$ for some positive integer $r < m_0$; note that $r$ cannot be zero.
> Since $r < m_0$, by induction hypothesis, we have $f(\overline{k_0 r}) = f(k_0) + f(r)$.
> But $r = p - k m_0$, so using induction hypothesis,
> $$ f(\overline{k_0 k m_0}) = f(\overline{-k_0 k m_0}) = f(k_0) + f(k m_0) = f(k_0) + f(k) + f(m_0). $$
> On the other hand, by induction hypothesis, $f(\overline{k_0 k m_0}) = f(k) + f(\overline{k_0 m_0})$.
> Cancelling out $f(k)$ gives us the desired equality $f(\overline{k_0 m_0}) = f(k_0) + f(m_0)$.
> Induction step is complete; the lemma is proved.

We now prove the main results.

> __Theorem 2.2__:
> $f$ is $p$-strong if and only if $f = R_p(c, \chi)$ for some $c \in M$ and $\chi : (\Z/p\Z)^* \to M$ with $\chi(-1) = 0$.
>
> __Proof__:
> First, we prove that $R_p(c, \chi)$ is $p$-strong iff $\chi(-1) = 0$.
> If $f = R_p(c, \chi)$ is $p$-strong, then $p$ is $f$-good, so $\chi(-1) = f(p - 1) = f(1) = 0$.
> Conversely, suppose that $\chi(-1) = 0$.
> Take any $k \geq 1$ and a positive integer $m < p^k$.
> Write $m = p^a t$ for some $a < k$ and $t$ coprime with $p$.
> Then $f(p^k - m) = \chi(\overline{p^{k - a} - t}) + ca = \chi(-\overline{t}) + ca = \chi(\overline{t}) + ca$ since $\chi(-1) = 0$.
> On the other hand, $f(m) = \chi(\overline{t}) + ca$ by definition.
> Thus, $f(p^k - m) = f(m)$ for any $k \geq 1$ and $m < p^k$.
> In particular, $p^k$ is $f$-good for each $k \geq 1$, so $f$ is $p$-strong, as desired.
>
> The previous paragraph shows that, if $f = R_p(c, \chi)$ for some $\chi : (\Z/p\Z)^* \to M$ and $c \in M$ with $\chi(-1) = 0$, then $f$ is $p$-strong.
> Conversely, suppose that $f$ is $p$-strong.
> If $f$ is $p$-regular, say $f = R_p(c, \chi)$, then the previous paragraph implies $\chi(-1) = 0$.
> Thus, it remains to show that $f$ must be $p$-regular.
> From a result in the section of $p$-regular maps, this is equivalent to saying that $f(t) = f(\overline{t})$ for any positive integer $t$ coprime with $p$.
> To prove this, we proceed by strong induction on $t$.
>
> The base case is $t < p$, for which the result is trivial since $\overline{t} = t$.
> So now, let $t > p$, and suppose that $f(m) = f(\overline{m})$ for any $m < t$.
> Let $a$ be the unique positive integer such that $p^a < t < p^{a + 1}$.
> Let $k = \lfloor p^{a + 1}/t \rfloor$.
> We have $k < p$ since $p^a < t$.
> Then we have $f(k) + f(t) = f(kt) = f(p^{a + 1} - kt)$, where $p^{a + 1} - kt < t$ by construction of $k$.
> But also, since $k < p$ and $\gcd(t, p) = 1$, we have $\gcd(p^{a + 1} - kt, p) = 1$.
> Applying induction hypothesis, we get $f(k) + f(t) = f(\overline{-kt}) = f(\overline{kt})$.
> But since $k < p$, Lemma 3 gives us $f(\overline{kt}) = f(k) + f(\overline{t})$.
> Cancelling $f(k)$ out from both sides gives us $f(t) = f(\overline{t})$.
> Induction step is complete.

> __Theorem 2.3__:
> Suppose that $M$ is torsion-free.
> Then the only wide map is zero, and the $p$-strong maps are of form $n \mapsto \nu_p(n) \cdot c$ for some $c \in M$ and $p$ prime.
>
> __Proof__:
> Both results, by Lemma 2.1, reduces to checking that $\text{Hom}((\Z/p\Z)^*, M) = 0$ for any $p$ prime.
> This is trivial since $(\Z/p\Z)^*$ is a finite (and thus torsion) monoid and $M$ is torsion-free.

> __Theorem 2.4__:
> Suppose that $M$ is not $2$-torsion-free.
> Then there exists a non-zero wide additive map from $\N^+$ to $M$.
>
> __Proof__:
> We first show that the existence of a certain sequence of primes suffice.
> Suppose that there exists a sequence $p_1 < p_2 < p_3 < \ldots$ of primes with $p_1 \equiv 1 \pmod{4}$ such that $p_{i + 1} \equiv p_i \pmod{4(p_i - 1)!}$ for each $i \geq 1$.
> Define the function $h : \N^+ \to \{-1, 1\}$ by $h(n) = \left(\frac{n}{p_n}\right)$ for all $n \geq 1$.
> Fix some non-zero $c \in M$ with $2c = 0$, and define $s : \{-1, 1\} \to M$ by $s(-1) = c$ and $s(1) = 0$.
> We claim that $f = s \circ h$ is a wide additive map.
>
> Recall a well-known fact that, for any pairwise coprime positive integers $a$ and $b$ and a positive integer $k$, $\left(\frac{a}{b}\right) = \left(\frac{a}{b + 4ka}\right)$.
> With this in mind, the property of the sequence $(p_i)_{i \geq 1}$ implies that $\left(\frac{k}{p_i}\right) = \left(\frac{k}{p_{i + 1}}\right)$ for any positive integers $i$ and $k$ with $k < p_i$.
> Then, by induction on $j$, one gets $\left(\frac{k}{p_i}\right) = \left(\frac{k}{p_j}\right)$ for any positive integers $i \leq j$ and $k$ with $k < p_i$.
> That is, $h(n) = \left(\frac{n}{p_j}\right)$ for all $j, n \geq 1$ with $n < p_j$.
>
> Due to this property, $h$ is multiplicative.
> Indeed, for any $m, n \geq 1$, pick an index $j$ with $mn < p_j$ (e.g. $j = mn$).
> Then we have
> $$ h(mn) = \left(\frac{mn}{p_j}\right) = \left(\frac{m}{p_j}\right) \left(\frac{n}{p_j}\right) = h(m) h(n). $$
>
> We now show that $f$ is a wide additive map.
> The fact that $f$ is additive follows from the fact that $h$ is multiplicative and $s$ is a monoid homomorphism.
> For wideness, it suffices to prove that $p_j$ is $f$-good for each $j \geq 1$.
> Indeed, for any $n < p_j$,
> $$ f(p_j - n) = s\left(\left(\frac{p_j - n}{p_j}\right)\right) = s\left(\left(\frac{-1}{p_j}\right)\right) s\left(\left(\frac{n}{p_j}\right)\right) = s\left(\left(\frac{-1}{p_j}\right)\right) f(p_j). $$
> But $\left(\frac{-1}{p_j}\right) = 1$ since $p_j \equiv 1 \pmod{4}$ by the choice of $p_1$ and the property of $(p_i)_{i \geq 1}$.
> We are done.

It seems that for *any* non-torsion-free integral monoid $M$, there is a non-zero wide additive map from $\N^+$ to $M$.
It suffices to do the construction for $M = \Z/p\Z$, where $p$ is an odd prime.
However, the author still does not know whether they exist.

Finally, we show that non-zero wide additive maps cannot be $p$-regular (and thus cannot be $p$-strong).
We use the same trick as in Lemma 1.2, except we have cancellation to shorten the proof.

> __Lemma 2.5__:
> Let $f : \N^+ \to M$ be a wide additive map.
> Suppose that $f$ is $p$-regular for some $p$ prime.
> Then $f \equiv 0$.
>
> __Proof__:
> Since $f$ is wide, there exists a prime $q > p^2$ that is $f$-good.
> By Lemma 2.1 and $p$-regularity, we have $f(q) = f(q - pk) = f(pk) = f(p) + f(k)$ for all $1 \leq k \leq p$.
> That is, $f(p) + f(k) = f(p) + f(1)$ for all $1 \leq k \leq p$.
> Cancelling $f(p)$ from both sides give us $f(k) = f(1) = 0$.



# Implementation details

We use $\N \to M$ to represent the additive maps, taking advantage of the better `nat` API.
The additive maps are defined in `additive_map.lean`, with an additional criterion $f(0) = 0$ on top of $f(xy) = f(x) + f(y)$ and $f(1) = 0$.
The $p$-regular maps, together with their properties, $p$-regularity predicate, and distinction results are defined in `regular_map.lean`.
The non-zero wide map from Theorem 2.4 is constructed in `legendre_stack_map.lean` using a more general construction.
The rest of the results are put into `N5_general.lean`.

Note that only the construction of the wide map from Theorem 2.4 as an additive map is put into `legendre_stack_map.lean`.
The proof of it being wide is still in `N5_general.lean`.
Furthermore, a concrete construction requires Dirichlet's theorem on arithmetic progressions, which has not been implemented in Lean at the time of writing.
We will state the theorem as an axiom.

We also need some extra code to define $p$-regular maps.
The main issue is that, for any positive integer $n = p^k t$, we want to represent $t$ in $(\Z/p\Z)^*$.
This needs some extra work; we will do them in an extra file `ord_compl_zmod.lean` in the global extra section.
