# Positive Lower Density of Simultaneous Primitive Roots

The simultaneous primitive-root problem for positive integer bases asks for the following assertion.

> [!NOTE]
> **Conjecture (Positive lower density of simultaneous primitive roots).**
>
> Let $A\subset\mathbb Z_{\ge2}$ be a nonempty finite set such that
>
> $$
> \prod_{a\in B}a\text{ is not a square whenever }B\subseteq A\text{ has odd cardinality}.
> $$
>
> There exist constants $c_A>0$ and $x_A\ge2$ such that, for every real $x\ge x_A$,
>
> $$
> \#\{x<p\le2x:p\text{ prime},\ p\nmid\prod_{a\in A}a,\ \operatorname{ord}_p(a)=p-1\text{ for every }a\in A\}
> \ge c_A\frac{x}{\log x}.
> $$

Here $\operatorname{ord}_p(a)$ denotes the multiplicative order of $a$ modulo $p$. The constants may depend on $A$, which remains fixed as $x$ grows. The square condition is necessary: every primitive root modulo an odd prime is a quadratic nonresidue, whereas a square cannot be the product of an odd number of quadratic nonresidues. The pairs $\{2,3\}$ and $\{3,6\}$ satisfy the condition; the triple $\{2,3,6\}$ does not.

This repository presents a proposed proof of this conjecture for submission to **Formal Conjectures**. A proof sketch follows; the [PDF manuscript](PDF/simultaneous-primitive-roots.pdf) contains the detailed argument. The proof takes the analytic estimates stated in Section 2 of the manuscript as inputs.

## Proof sketch

### 1. Choose congruence classes with the required quadratic signs

Write the prime exponents of each $a\in A$ as a vector $v_a$ over $\mathbb F_2$. The square condition says precisely that the equations

$$
v_a\cdot z=1\qquad(a\in A)
$$

are consistent. Quadratic reciprocity and the Chinese remainder theorem then give a reduced residue class modulo a fixed integer $H_0$ in which every base is a quadratic nonresidue. The class can also be chosen so that no odd prime dividing $H_0$ divides $p-1$.

For each further odd prime $\ell\le Y$, retain all residues other than $0,1$ modulo $\ell$. The resulting finite union of classes has relative density

$$
\lambda_{A,Y}=\frac1{\varphi(H_0)}
\prod_{\substack{3\le\ell\le Y\\\ell\text{ prime},\ \ell\nmid H_0}}
\frac{\ell-2}{\ell-1}.
$$

### 2. Count a long prime factor in each fixed class

For fixed $1/2<\alpha<\beta<1$, put

$$
f_x(n)=\sum_{\substack{x^\alpha<Q\le x^\beta\\Q\text{ prime}}}\mathbf1_{Q\mid n},
\qquad
C_x=\sum_{\substack{x^\alpha<Q\le x^\beta\\Q\text{ prime}}}\frac1Q
\longrightarrow\theta=\log(\beta/\alpha).
$$

The required fixed-class statistic is

$$
\sum_p\Phi((p-1)/x)\mathbf1_{p\equiv b\pmod H}
\bigl(f_x(p-1)-C_x\bigr)=o(x/\log x)
$$

for fixed $(b,H)=1$ and a smooth compactly supported cutoff $\Phi$. The manuscript derives this from the marked correlation estimates. A finite Fourier projection preserves the endpoint square estimate; a periodic relation between both endpoints preserves the congruence when shared factors are removed. Dirichlet characters separate the congruence in the one-sided prime replacement.

The sieve uses local density zero at primes dividing $H$ and $1/\ell$ elsewhere. Reallocation preserves the actual product, and a variance estimate removes the auxiliary weights. All moduli and arrays are fixed before taking the $x$ limit.

Choose $0\le\Phi\le1$ supported in $(5/4,7/4)$ and write $m_\Phi=\int\Phi>0$. The candidate weight is then

$$
\bigl(m_\Phi\theta\lambda_{A,Y}+o_{A,Y}(1)\bigr)\frac{x}{\log x}.
$$

### 3. Obtain a uniform splitting estimate

For a fixed base $a$ and sufficiently large prime $q$, the Kummer field

$$
K_q=\mathbb Q(\mu_q,a^{1/q})
$$

has degree $q(q-1)$ and satisfies

$$
\log D_{K_q}+[K_q:\mathbb Q]\ll_a q(q-1)\log(2q).
$$

The common Hecke zero-free strip of width $0<\delta<1/2$ stated among the analytic inputs passes to $\zeta_{K_q}$. A smooth explicit formula, retaining its degree and discriminant dependence, gives

$$
B_{a,q}(x)\ll_a
\frac{x}{q(q-1)\log x}
+\frac{x^{1-\delta}\log(2q)}{\log x},
$$

where $B_{a,q}(x)$ counts primes $x<p\le2x$ with $q\mid p-1$ and $a^{(p-1)/q}\equiv1\pmod p$. The implied constant is independent of $q$ and $x$.

### 4. Remove the remaining order obstructions

Set $\eta=\delta/4$, $\alpha=1-\eta$ and $\beta=1-\eta/2$. Each candidate has a unique long prime factor and can be written

$$
p-1=Qr,\qquad x^{1-\eta}<Q\le x^{1-\eta/2},\qquad r<2x^\eta.
$$

If $a$ is not a primitive root, choose a prime divisor $q$ of $(p-1)/\operatorname{ord}_p(a)$. The quadratic signs exclude $q=2$, and the congruence conditions exclude odd $q\le Y$.

If $q\ne Q$, then $q\mid r$. Summing the splitting estimate over $Y<q<2x^\eta$ removes at most

$$
O_a\!\left(\frac{x}{Y\log x}\right)+o(x/\log x)
$$

primes. If $q=Q$, then $\operatorname{ord}_p(a)<2x^\eta$, so $p$ divides

$$
\prod_{j\le2x^\eta}(a^j-1).
$$

Its logarithm is $O_a(x^{2\eta})$, which removes only $o(x/\log x)$ primes. Sum these bounds over the fixed set $A$.

### 5. Choose the fixed cutoff and retain a positive constant

Writing $N_A(x)$ for the count in the conjecture, the candidate count and the exception bounds give

$$
N_A(x)\ge
\left(m_\Phi\theta\lambda_{A,Y}-\frac{C_A}{Y}+o_{A,Y}(1)\right)
\frac{x}{\log x},
$$

with $C_A$ independent of $Y$. For $Y=2T^2+1$, an elementary product bound gives

$$
\varphi(H_0)\lambda_{A,Y}
\ge\prod_{j=1}^{T^2}\frac{2j-1}{2j}
\ge\frac1{2T}.
$$

Thus the main coefficient decreases at most like $1/T$, while the exception coefficient decreases like $1/T^2$. Fix $T$ large enough that the main term exceeds the loss, and only then let $x$ grow. This leaves the required positive multiple of $x/\log x$.

## Detailed manuscript

- [PDF manuscript](PDF/simultaneous-primitive-roots.pdf)

Public draft 1, 9 October 2026.
