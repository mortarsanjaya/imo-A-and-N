# IMO 2020 N5, Generalized Version

*Note*: This generalized problem raises a lot of structures.
Thus, our formatting style will be different.

Fix an (additive) integral monoid $M$.
Denote $\N^+ = \{1, 2, 3, \ldots\}$.
We call a function $f : \N^+ \to M$ *additive* if $f(xy) = f(x) + f(y)$ for every $x, y \in \N^+$.
Given a function $f : \N^+ \to M$, a positive integer $n$ is said to be *$f$-good* if $f(k) = f(n - k)$ for all $k < n$.
Our aim is to determine all additive maps $f : \N^+ \to M$ with infinitely many $f$-good positive integers.

We will borrow terminologies introduced in the extra file `extra/number_theory/divisor_closed_prop.lean`.
For this `.md` file only, we say that $f : \N^+ \to M$ is wide if the $f$-good predicate is wide.
Similarly, for any $p$ prime, we say that $f$ is $p$-strong if the $f$-good predicate is strong.

For a fixed prime $p$, for any $k \geq 0$, let $\overline{k}$ denote the unique non-negative integer $c$ such that $k \equiv c \pmod{p}$.
The context at which it is applied is usually clear.



# Constructions

## $p$-regular maps

Let $p$ be a prime number, $\chi : (\Z/p\Z)^* \to M$ be a monoid homomorphism, and $c \in M$.
We denote $f = R_p(\chi, c)$ as the map defined by $f(p^k t) = \chi(\overline{t}) + kc$ for all positive integers $t$ coprime with $p$ and $k \geq 0$.
Here, $\overline{t}$ denotes the reduction of $t$ modulo $p$ in $(\Z/p\Z)^*$.
It is easy to check that $f$ is additive map.
An additive map that equals $R_p(\chi, c)$ is called a $p$-regular map.

Clearly, for any $p$-regular map $f$, we have $f(t) = f(\overline{t})$ for any $t$ coprime with $p$.
Conversely, given an additive map $f$ such that $f(t) = f(\overline{t})$ for any $t$ coprime with $p$, $f$ is $p$-regular.
Indeed, define $\chi : (\Z/p\Z)^* \to M$ by $\chi(\overline{t}) = f(t)$ for any $t$ coprime with $p$, and take $c = f(p)$.
One can check that $\chi$ is a well-defined monoid homomorphism, and that $f = R_p(\chi, c)$.
Thus, an additive map $f$ is $p$-regular if and only if $f(t) = f(\overline{t})$ for any $t$ coprime with $p$.

The $p$-regular maps appear in the classification of $p$-strong additive maps.
In particular, all of them are $p$-regular, and given $f = R_p(\chi, c)$, $f$ is $p$-strong iff $\chi(-1) = 0$.

## Sporadic maps

Let $\overline{\chi} = (\chi_i)_{i \geq 1}$ be a sequence of monoid homomorphisms $\chi_i : (\Z/p_i\Z)^* \to M$, where $p_1 < p_2 < p_3 < \ldots$ is a sequence of primes.
We call $\overline{\chi}$ *compatible* if for any positive integer $k$ and indices $i$, $j$ with $k < p_i$ and $k < p_j$, we have $\chi_i(k) = \chi_j(k)$.
Note that the former and latter $k$ are the image of $k$ in $(\Z/p_i\Z)^*$ and $(\Z/p_j\Z)^*$, respectively.

Given a compatible sequence $\overline{\chi}$, we define the *sporadic* map $f = S(\overline{\chi})$ by $f(k) = \chi_k(k)$ for each $k > 1$.
One can check that $f(k) = \chi_j(k)$ for any indices $j$ such that $k < p_j$.
Furthermore, one can also prove that $f$ is additive.
Indeed, for any $k, m \in \N^+$, one can pick an index $j > \max\{k, m\}$, so that $p_j > \max\{k, m\}$.
Then $f(km) = \chi_j(km) = \chi_j(k) + \chi_j(m) = f(k) + f(m)$.
Thus, $f$ is an additive map.

Unlike the $p$-regular maps, sporadic maps do not have a very good theory.
However, it appears in the classification of wide additive maps.
The wide additive maps are precisely $S(\overline{\chi})$ for some compatible sequence $\overline{\chi}$ with $\chi_i(-1) = 0$ for each $i \geq 1$.
The latter criterion is non-trivial only when $M$ has a $2$-torsion element.

We can show that there exists a non-zero sporadic map.
Our construction below assumes $M = \Z/2\Z$.
Define an auxiliary group homomorphism $s : \{-1, 1\} \to \Z/2\Z$ by $s(-1) = 1$ and $s(1) = 0$.

First take $p_1 = 5$, and define $\chi_1 = k \mapsto s\left(\left(\frac{k}{p_1}\right)\right)$.
By periodicity of the Legendre symbol with respect to the second argument, we have $s\left(\left(\frac{k}{q}\right)\right) = \chi_1(k)$ for any $k \in \{1, 2, 3, 4\}$ and primes $q$ with $q \equiv p_1 \pmod{4(p_1 - 1)!}$.
By Dirichlet's theorem, such $q$ exists (for example, $q = 101$); set $p_2 = q$ and $\chi_2 = k \mapsto s\left(\left(\frac{k}{p_2}\right)\right)$.
Continuing in the same way indefinitely gives us a compatible sequence $\overline{\chi}$.
This gives us a non-zero sporadic map, $S(\overline{\chi})$.






## Distinction between $p$-regular maps and sporadic maps

The $p$-regular and sporadic properties are mutually exclusive in the sense that a non-zero $p$-regular additive map cannot be sporadic or $q$-regular for distinct $q$.
We need the following lemma.

> __Lemma__:
> Let $p$ be a prime and $f : \N \to M$ be a $p$-regular map.
> Suppose that there exists a positive integer $n > p^2$ coprime with $n$ and $c \in M$ such that $f(n - pk) = f(k) + c$ for all $1 \leq k \leq p$.
> Then $f \equiv 0$.
>
> __Proof__:
> Indeed, by $p$-regularity, $f(n - pk) = f(\overline{n}) = f(n - p)$ for each $k \leq p$, so $f(k) = f(1) = 0$ for each $k \leq p$.
> Then $p$-regularity yields $f \equiv 0$.

First suppose that an additive map $f : \N \to M$ is $p$-regular and $q$-regular for distinct primes $p$ and $q$.
Without loss of generality, suppose that $q > p$.
Then $f \equiv 0$ due to the lemma with $n = q^2 > p^2$ and $c = f(p) + f(q - 1)$.
Indeed, $f(q^2 - pk) = f(pk) + f(q - 1) = f(k) + f(p) + f(q - 1)$ by $q$-regularity.

Now suppose that additive map $f : \N \to M$ is $p$-regular for some prime $p$ and also sporadic.
Write $f = S(\overline{\chi})$ for some compatible sequence $\overline{\chi} = (\chi_i : (\Z/q_i\Z)^* \to M)_{i \geq 1}$.
Pick an index $i$ such that $q_i > p^2$, e.g. $i = p^2$.
Then $f(q^2 - pk) = \chi_i(-pk) = \chi_i(-p) + \chi_i(k)$ for all $1 \leq k \leq p$.
On the other hand, by $p$-regularity, $f(q^2 - pk) = f(\overline{q^2})$, so $f(k) = \chi_i(k) = \chi_i(1) = 0$ for all $1 \leq k \leq p$.
This implies $f \equiv 0$, as desired.



# Main results

Let $f : \N^+ \to M$ be an additive map.
It is easy to see that the set of $f$-good positive integers is divisor-closed.
Indeed, fix an arbitrary $f$-good positive integer $n$ and let $d$ be a factor of $n$.
Then for any $k < d$,
$$ f(k) + f(n/d) = f(nk/d) = f(n - nk/d) = f(d - k) + f(n/d). $$
Cancelling $f(n/d)$ from both sides shows us that $d$ is $f$-good.
By the result in `extra/number_theory/divisor_closed_prop.lean`, $f$ is either wide or $p$-strong for some $p$ prime.
The main result to prove is as follows.

> __Theorem 1__:
> $f$ is $p$-strong if and only if $f = R_p(\chi, c)$ for some $c \in M$ and $\chi : (\Z/p\Z)^* \to M$ with $\chi(-1) = 0$.

> __Theorem 2__:
> $f$ is wide if and only if $f = S(\overline{\chi})$ for some compatible sequence $\overline{\chi} = (\chi_i)_{i \geq 1}$ of maps with $\chi_i(-1) = 0$ for each $i \geq 1$.

To prove both Theorem 1 and 2, we need an extra lemma.

> __Lemma 3__:
> Let $p$ be an $f$-good prime.
> Then, for any positive integers $k$ and $m$ coprime with $p$, we have $f(\overline{km}) = f(\overline{k}) + f(\overline{m})$.
>
> __Proof__:
> Without loss of generality, we may assume $k, m < p$.
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

Now, we prove both Theorem 1 and 2.
We start with Theorem 2.

> __Proof of Theorem 2__:
> First suppose that $f = S(\overline{\chi})$ for some compatible sequence $\overline{\chi}$.
> We proved that $f$ is always an additive map, so it remains to prove that $f$ is wide.
> Consider the underlying sequence of primes $p_1 < p_2 < p_3 < \ldots$.
> Then for each $i \geq 1$ and $k < p_i$, we have $f(p - k) = \chi_i(-k) = \chi_i(k) = f(k)$ since $\chi_i(-1) = 0$.
> Then $p_i$ is $f$-good for each $i \geq 1$, which proves that $f$ is wide.
>
> Conversely, suppose that $f$ is wide.
> Consider a sequence $p_1 < p_2 < p_3 < \ldots$ of $f$-good primes.
> For each $i \geq 1$, set $\chi_i = \overline{k} \mapsto f(k)$.
> Note that each $\chi_i$ is a monoid homomorphism due to Lemma 3.
> From the construction, it is now easy to see that $\overline{\chi} = (\chi_i)_{i \geq 1}$ is compatible and $f = S(\overline{\chi})$.

Next, we prove Theorem 1.

> __Proof of Theorem 1__:
> First, we prove that $R_p(\chi, c)$ is $p$-strong iff $\chi(-1) = 0$.
> If $f = R_p(\chi, c)$ is $p$-strong, then $p$ is $f$-good, so $\chi(-1) = f(p - 1) = f(1) = 0$.
> Conversely, suppose that $\chi(-1) = 0$.
> Take any $k \geq 1$ and a positive integer $m < p^k$.
> Write $m = p^a t$ for some $a < k$ and $t$ coprime with $p$.
> Then $f(p^k - m) = \chi(\overline{p^{k - a} - t}) + ca = \chi(-\overline{t}) + ca = \chi(\overline{t}) + ca$ since $\chi(-1) = 0$.
> On the other hand, $f(m) = \chi(\overline{t}) + ca$ by definition.
> Thus, $f(p^k - m) = f(m)$ for any $k \geq 1$ and $m < p^k$.
> In particular, $p^k$ is $f$-good for each $k \geq 1$, so $f$ is $p$-strong, as desired.
>
> The previous paragraph shows that, if $f = R_p(\chi, c)$ for some $\chi : (\Z/p\Z)^* \to M$ and $c \in M$ with $\chi(-1) = 0$, then $f$ is $p$-strong.
> Conversely, suppose that $f$ is $p$-strong.
> If $f$ is $p$-regular, say $f = R_p(\chi, c)$, then the previous paragraph implies $\chi(-1) = 0$.
> Thus, it remains to show that $f$ is $p$-regular.
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

Theorem 2, however, does not say whether the only wide map is zero.
This does not hold for $M = \Z/2\Z$, isomorphic to $\{-1, 1\}$.
Indeed, we just take $f = S(\overline{\chi})$, the non-zero sporadic map we have constructed before.
For each $i \geq 1$, $\chi_i$ is the image of the Legendre symbol modulo $p_i$ in $M$.
From the construction, each $p_i$ is congruent to $1$ modulo $4$, so $\left(\frac{-1}{p_i}\right) = 1$ and thus $\chi_i(-1) = 0$ for each $i \geq 1$.
Theorem 2 then implies that $f$ is wide.

The question of existence of a non-zero wide map over a monoid $M$ can be reduced to the case where $M = \Z/p\Z$ for some $p$ prime or $M = \N$.
In the latter case, wide maps must be zero; this is true whenever $M$ is torsion-free.

> __Lemma 4__:
> The only sporadic map over torsion-free monoid is zero.
>
> __Proof__:
> If $M$ is sporadic, then $\text{Hom}(N, M) = 0$ for any torsion group $N$.
> For each $p$ prime, $(\Z/p\Z)^*$ is a torsion monoid, as it is finite.
> So, the only compatible sequence over $M$ is the zero sequence, which necessarily induces the zero additive map.

When $M = \Z/p\Z$ for $p$ odd, one trivially obtains $\chi(-1) = 0$ for any homomorphism $\chi : (\Z/q\Z)^* \to M$, where $q$ is a prime.
Indeed, $2 \chi(-1) = \chi((-1)^2) = \chi(1) = 0$, but $M$ is $2$-torsion-free.
In particular, an additive map over $\Z/p\Z$ is wide if and only if it is sporadic.
This simplifies the search of wide maps to search of compatible sequence of homomorphisms.

Unfortunately, I have not found a construction or a proof of the non-existence of such compatible sequence.
One possible idea is looking at a general residue symbol.
At least it seems that there must exist a compatible sequence over $M = \Z/3\Z$.



# Implementation details

We use $\N \to M$ to represent the additive maps, taking advantage of the better `nat` API.

All results specifically regarding additive maps and its classes are in a folder `additive_map`.
The rest of the results are about additive maps with infinitely many good positive integers; they are put in `N5_extra.lean`.

The additive maps are implemented in `additive_map/basic.lean` with an extra condition that it takes the $0 \in M$ when evaluated at both $0$ and $1$.
The condition at $1$ is trivial when $M$ is integral, but in general this might not be the case.
The $p$-regular maps, together with their properties and a regularity predicate, are defined in `additive_map/regular_map.lean`.
The sporadic maps, together with their properties and a sporadicity predicate, are defined in `additive_map/special_map.lean`.
The distinguishing result between the two classes of maps are formalized in `additive_map/distinction.lean`.

The non-zero sporadic map construction done above for $M = \Z/2\Z$ requires Dirichlet's theorem on arithmetic progressions, which has not been implemented in Lean at the time of writing.
We will state the theorem but use the placeholder `sorry` in its proof.

We also need some extra code to define $p$-regular maps.
The main issue is that, for any positive integer $n = p^k t$, we want to represent $t$ in $(\Z/p\Z)^*$.
This needs some extra work; we will do them in an extra file `ord_compl_zmod.lean` in the global extra section.
