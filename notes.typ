#import "@preview/physica:0.9.5": dd, derivative, arccot
#import "style.typ": *

#show: show-theorion
#show: styling.with(
  course_name: "Analys i en variabel",
  course_code: "SF1673 (HT25)",
  title_size: 30pt,
  title_space: 0em, 

  margin: 0.5cm,
  width: 15cm,
  height: auto,
  size: 12pt,
)

= The Real Numbers

== Reals

=== Prerequisites

#theorem(title: [Induction])[
  If $s in NN$ such that
  + $1 in S$ and
  + when $n in S$ it follows that $n + 1 in S$
  it follows that $S = NN$.
]

#definition(title: [Injective/Surjective/Bijective])[
  $f : X -> Y$ is _injective_ (or one-to-one) if $x_1 != x_2 ==> f(x_1) != f(x_2)$
  or equivalently if $f(x_1) = f(x_2) ==> x_1 = x_2$.
  
  $f$ is _surjective_ if $forall y space exists x : f(x) = y$.
  
  $f$ is _bijective_ if is both injective and surjective or equivalently if each $y$ is mapped to exactly one $x$.
]

=== Comparison

#definition(title: [Equality])[
  $a  = b <==> (forall epsilon > 0 => |a - b| < epsilon)$
]

#theorem(title: [Triangle Inequalities])[
  + $|a + b| <= |a| + |b|$
  + $|a - b| <= |a - c| + |c - b|$
  + $|a - b| >= ||a| - |b||$

  The reverse triangle inequality (iii) is seldom used.
]

=== Bounds

#axiom(title: [Supremum Property or Axiom of Completeness])[
  Every bounded, non-empty set of real numbers has a least upper bound.
]

#note-box[The same does not apply for the rationals.]

#definition(title: [Least Upper Bound])[
  Assume $s in RR$ is an upper bound for a set $A subset.eq RR$. Then,
  $ s = sup A #h(1em) <==> #h(1em) forall epsilon > 0 space exists a in A : s - epsilon < a. $
]

== Cardinality

#definition(title: [Cardinality])[
  $A$ has the same _cardinality_ as $B$ if there exists a bijective $f : A -> B$.
]

#definition(title: [Countable/Uncountable])[
  $A$ is _countable_ if $NN tilde A$.
  Otherwise, $A$ is _uncountable_ if there are infinite elements or _finite_ if there are finite elements.
]

#theorem(title: [Countability of $QQ$, $RR$])[
  $QQ$ is countable.

  #proof[Let $A_1 = {0}$ and let
    $ A_n = {plus.minus p slash q : p, q in NN_+, gcd(p, q) = 1, p + q = n} $
    for all $n >= 2$.
    Each $A_n$ is finite and every rational numbers appears in exactly one set.
  ]

  $RR$ is uncountable.

  #proof[Cantor's diagonalization method.]

  $II$ is uncountable.

  #proof[$II = RR backslash QQ$ where $QQ$ is countable.]
]

#theorem(title: [Density of $QQ$ in $RR$])[
  + $forall a < b in RR space exists r in QQ : a < r < b$

  + $forall y in RR space exists (r_n) in QQ : (r_n) -> y$
]

== Topology

=== Points

#definition(title: [Limit Point])[
  $x$ is a _limit point_ of $A$ if every $V_epsilon (x)$ intersects $A$ at some point other than $x$.
]

#theorem(title: [Sequential Limit Point])[
  $x$ is a limit point of $A$ if $x = lim a_n$ for some $(a_n) subset.eq A : a_n != x space forall n in NN.$
]

#theorem(title: [Nested Interval Property])[
  The intervals $ RR supset.eq I_1 supset.eq I_2 supset.eq I_3 supset.eq dots.h.c$
  all contain a point $a = inter.big_(n=1)^infinity I_n $.
]

=== Opened and Closed Sets

#definition(title: [Open/Closed Set])[
  $A subset.eq RR$ is _open_ if $forall a in A space exists V_epsilon (a) subset.eq A$ or equivalently if its complement is closed.
  
  $A subset.eq RR$ is _closed_ if it contains its limit points or equivalently if its complement is open.
]

#theorem(title: [Clopen Sets])[
  $RR$ and $emptyset$ are _clopen_ (both opened and closed).
]

#theorem(title: [Unions/Intersections])[
  The union of open (closed) sets is open (closed).
  
  The intersection of finitely many open (closed) sets is open (closed).  
]

=== Compactness

#definition(title: [Compact])[
  A set $K$ in a topological space is _compact_ if every open cover has a finite subcover.
]

#theorem(title: [Heine--Borel])[
  A set $K subset.eq RR^n$ is compact if and only if it is closed and bounded.
]

#note-box[Compactness is like a generalization of closed intervals.]

== Sequences

#definition(title: [Sequence])[
  A _sequence_ is a function whose domain is $NN.$
]

#definition(title: [Convergence])[
  A sequence _converges_ to $a$ if
  $ forall epsilon > 0 space exists N in NN : n >= N ==> |a_n - a| < epsilon $
  or equivalently if for any $V_epsilon (a)$ there exists a point in the sequence after which all terms are in $V_epsilon (a)$.
  In other words if every $epsilon$-neighborhood contains all but a finite number of the terms in $(a_n)$.

  We write this $lim_(n->infinity) a_n = lim a_n = a$ or $a_n -> a$.

  #example[Template of a typical convergence proof:
    + Let $epsilon > 0$ be arbitrary.
    + Propose an $N in NN$ (found before writing the proof).
    + Assume $n >= N$.
    4. Show that $|a_n - a| < epsilon.$
  ]
]

#theorem(title: [Uniqueness of Limits])[
  The limit of a sequence, if it exists, is unique.
]

=== Bounded

#definition(title: [Bounded])[
  A sequence is _bounded_ if $exists M > 0 : |a_n| < M space forall n in NN$.
]

#theorem(title: [Convergent/Monotone])[
  Every convergent series is bounded.

  If a sequence is monotone and bounded it converges.

  Subsequences of a convergent series converge to the same limit.
]

#theorem(title: [Bolzano--Weierstrass])[
  Every bounded sequence contains a convergent subsequence.
]

=== Cauchy

#definition(title: [Cauchy Sequence])[
  A sequence $(a_n)$ is a _Cauchy sequence_ if
  $ forall epsilon > 0 space exists N in NN : m, n >= N ==> |a_n - a_m| < epsilon. $
]

#theorem(title: [Cauchy Criterion])[
  A sequence converges if and only if it is a Cauchy sequence.
]

== Series

#definition(title: [Infinite Series])[
  Let $(a_j)^infinity_(j=0)$ and let $(s_n)^infinity_(n=0)$.
  The sum of the infinite series is defined as
  $ sum^infinity_(j=0) a_j = lim_(n->infinity) s_n = lim_(n->infinity) sum^n_(j=0) a_j. $

  If $a_j >= 0$ for every $j$ we say that the series is _positive_.
]

#caution-box[Beware of treating infinite series like elementary algebra,
e.g., by rearranging terms.]

#theorem(title: [Series Term Test])[
  If $sum^infinity_(k=1) a_k$ converges, then $a_k -> 0$.
  However, the reverse implication is false.
]

#theorem[
  The series $sum_(j=1)^infinity 1 slash j$ is divergent.

  #proof[
    
  ]
]

#theorem()[
  The series $sum_(j=1)^infinity 1 slash j^p$ converges if and only if $p > 1$.
  
  #proof[
    
  ]
]

#theorem(title: [Cauchy Condensation Test])[
  Let $(a_n)$ be a decreasing sequence of non-negative real numbers.
  Then $sum_(n=1)^(infinity) a_n$ converges if and only if $sum_(n=0)^(infinity) 2^n a_(2^n)$ converges.
]

// Add theorem 2.7.2

#theorem()[
  Let $sum_(j=0)^infinity a_j$ and $sum_(j=0)^infinity b_j$ be positive series with terms such that
  $ lim_(j->infinity) a_j/b_j = K $
  for some $K != 0.$
  Then, $sum_(j=0)^infinity a_j$ converges if and only if $sum_(j=0)^infinity b_j$ converges.
]

#theorem(title: [Comparison Test])[
  Let $(a_k)$ and $(b_k)$ satisfy $0 <= a_k <= b_k.$ Then,
  + $sum^infinity_(k=1) (a_k)$ converges if $sum^infinity_(k=1) (b_k)$  converges.
  + $sum^infinity_(k=1) (b_k)$ diverges if $sum^infinity_(k=1) (a_k)$  diverges.
]

#theorem(title: [Alternating Series Test])[
  Let $(a_n)$ satisfy
  + $a_1 >= a_2 >= dots.h.c >= a_n >= a_(n+1) >= dots.h.c$ and
  + $(a_n) -> 0$.
  Then, $sum^infinity_(n=1) (-1)^(n+1) a_n$ converges.
]

#definition(title: [Absolutely Convergent])[
  A series $sum_(j=0)^infinity a_j$ is _absolutely convergent_ if $sum_(j=0)^infinity abs(a_j)$ is convergent.
]

#theorem()[
  If a series is absolutely convergent then it is convergent.
]

#theorem(title: [Geometric Series])[
  If $abs(x) < 1$, then
  $ sum_(j=0)^infinity x^j = 1/(1 - x) $
  since
  $ s_n = sum_(j=0)^n x^j = (1 - x^(n+1))/(1 - x). $
]

// Chapter 2.8 can be added.

= Real Functions

== Limits

#theorem(title: [Function Limit])[ 
  Given $f : A -> RR$ with the limit point $c$,
  + $lim_(x->c) f(x) = L$ is equivalent to
  + if $forall (x_n) subset.eq A : (x_n != c "and" x_n -> c)$ it follows that $f(x_n) -> L$.
]

#note-box[
  In the $epsilon delta$-definition of limits,
  the additional restriction that $0 < abs(x - a)$
  is just a way to say $x != c.$
]

#definition(title: [Infinite Limit])[
  Given a limit point $c in D_f$, we say that $lim_(x->c) f(x) = infinity$ if
  $ forall M space exists delta > 0 : 0 <|x - c| < delta ==> f(x) >=M. $
]

== Continuity

#theorem(title: [Continuity])[
  The following are equivalent:
  + $f : A -> RR$ is _continuous_ at $c in RR$.
  + $forall epsilon > 0 space exists delta > 0 : |x - c| < delta ==> |f(x) - f(c)| < epsilon$, where $x in A$.
  + $forall V_epsilon (f(c)) space exists V_delta (c) : x in V_delta inter A ==> f(x) in V_epsilon$
  + $x_n -> c$, where $(x_n) subset.eq A$, implies $f(x_n) -> f(c)$.
  If $c$ is a limit point of $A$:
  5.  $lim_(x->c) f(x) = f(c)$, also written $lim_(h->0)f(c + h) - f(c) = 0$.

  Note that (ii) defines (i). Mostly (v) is used in practice.
]

#theorem(title: [Isolated Continuity])[
  All functions are continuous at isolated points.
]

#theorem(title: [Dirichlet Discontinuous])[ 
  The Dirichlet function $f : RR -> RR$ such that $f(x) = 1$ if $x in QQ$ and
  $f(x) = 0$ if $x in II$ is discontinuous everywhere.
]

=== Composition

#theorem(title: [Composition])[ 
  Given $f : A -> B$ and $g : B -> RR$ with $f(A) subset.eq B$,
  if $f$ is continuous at $c in A$ and $g$ is continuous at $f(c) in B$,
  then $g compose f$ is continuous at $c$.
]

#theorem(title: [Composition Limit])[ 
  If $f$ is continuous at $y$ and $lim_(x->c) g(x) = y$, then
  $ lim_(x->c) f(g(x)) = f(lim_(x->c) g(x)) = f(y). $ 
]

=== Results

#theorem(title: [Intermediate Value])[
  If $f$ is continuous on $[a, b]$, then for any $y$ between $f(a)$ and $f(b)$, there exists some $c in (a, b)$ such that $f(c) = y$.
]

#theorem(title: [Weierstrass Extreme Value])[
  If $f$ is continuous on the compact set $K$, then $f$ attains a maximum and a minimum value on $K$.
] <thm:extreme>

== Derivatives

=== Differentiation

#theorem(title: [Chain Rule])[
  Let $f : X -> Y$ and $g : Y -> RR$.
  If $f$ is differentiable at $c in X$ and $g$ is differentiable at $f(c) in Y$,
  then $g compose f$ is differentable at $c$ with
  $ (g compose f)'(c) = g'(f(c)) f'(c). $
]

#theorem(title: [Basic Derivatives], 
  grid(
    columns: (1fr, 1.2fr),
    [$
      &derivative(,x) (arcsin x) = 1 / sqrt(1 - x^2) \
      &derivative(,x) (arccos x) = -1 / sqrt(1 - x^2) \
      &derivative(,x) (arctan x) = 1 / (1 + x^2) \
      &derivative(,x) (arccot x) = -1 / (1 + x^2) \
      &derivative(,x) (x^a) = a x^(a - 1) #h(0.7em) (a != 0) \
    $],
    [$
      &derivative(,x) (sin x) = cos x \
      &derivative(,x) (cos x) = -sin x \
      &derivative(,x) (tan x) = 1 / (cos^2 x) \
      &derivative(,x) (ln abs(x)) = 1 / x \
      &(f^(-1))'(y) = -1/(f'(x)) #h(0.7em) (f'(x) != 0)
    $],
  )
)

#theorem(title: [L'Hôpital's Rule])[
  Let $f(x)$ and $g(x)$ be defined and, with the possible exception of at the limit point $c$, differentiable. If
  + $lim_(x->c) f(x) = lim_(x->c) g(x) = 0 "or" plus.minus infinity$ and
  + $g'(x) != 0$ for all $x != c$, then
  $ lim_(x->c) (f'(x))/(g'(x)) = L #h(0.7em) ==> #h(0.7em) lim_(x->c) (f(x))/(g(x)) = L. $

  #proof(title: "Proof of the zero case")[Assume the limits are zero.

  Let the functions be differentiable on the open interval $(c, x)$.
  Then, rewriting and applying @thm:gmv gives
  $ lim_(x->c) f(x)/g(x) = lim_(x->c) (f(x)-f(c))/(g(x)-g(c))
  = lim_(x->c) (f'(p))/(g'(p)) = lim_(p->c) (f'(p))/(g'(p)) $
  for some $p "between" c "and" x$.
  ]

  #proof(title: "Proof of the infinity case")[The proof is too complicated.
  // Assume the limits are infinite. We will only prove the right-hand limit.
  // Let $c < a < b$. The @thm:gmv states that there exists a $p in (a, b)$ such that
  // $ f'(p)[g(b) - g(a)] = g'(p)[f(b) - f(a)]. $
  // Solving for $f(a)$, we get 
  // $ f(a) = f(b) + (f'(p)(g(a) - g(b)))/(g'(p)). $
  // We divide by $g(a)$ and get
  // $ f(a)/g(a) = (f'(p))/(g'(p)) + 1/g(a) (f(b)-g(b) (f'(p))/(g'(p))) $
  // which we rewrite as
  // $ f(a)/g(a) - L = (f'(p))/(g'(p)) - L + 1/g(a) (f(b)-g(b) (f'(p))/(g'(p))) $
  ]
]

#important-box[
  This is only an implication, not an equivalence,
  so there may exist some other solution if this method fails.
]

=== Function Character

#theorem(title: [Fermat's or Interior Extremum])[
  Let $f : (a, b) -> RR$  be differentiable at the local extremum $c in (a, b)$. Then $f'(x) = 0$.

  However, note that a zero-derivative point may also be a stationary point of inflection. 
] <thm:fermat>

#theorem(title: [Darboux's])[
  If $f$ is differentiable on $[a, b]$ and if $y$ lies strictly between $f'(a)$ and $f'(b)$, then $exists c in (a, b) : f'(c) = y$.

  In other words, if $f$ is differentiable on an interval,
  then $f'$ satisfies the Intermediate Value Property (IVP).

  #proof[Assume that $f'(a) < y < f'(b).$ // why not ≤? 

  Let $g(x) = f(x) - y x$ with $g'(x) = f'(x) - y$. Note that $f'(c) = y$ if $g'(c) = 0$ for some $c in (a, b)$.
  
  @thm:extreme states that $g$ must have a minimum point $c in [a, b]$.
  More precisely $c in (a, b)$ since, from the assumption, $g'(a) < 0$ and $g'(b) > 0$.
  Furthermore, $g'(c) = 0$ according to @thm:fermat.
  ]
]

#theorem(title: [Newton's Method])[
  Find roots to a differentiable function $f(x)$.

  Given $x_n$ with the coordinates $(x_n, f(x_n))$, the tangent line is given by
  $ T(x) = f'(x_n)(x - x_n) + f(x_n) $
  and intersects the $x$-axis at
  $ T(x_(n+1)) = 0 #h(0.8em) <==> #h(0.8em) x_(n+1) = x_n - f(x_n)/(f'(x_n)). $

  The method fails if it iterates endlessly or $f'(x_n) = 0$.
]

=== The Mean Value Theorems

Let $f$ and $g$ be continuous on $[a, b]$ and differentiable on $(a, b)$.

#theorem(title: [Rolle's])[
  $ f(a) = f(b) ==> exists c in (a, b) : f'(c) = 0 $

  #proof[$f(x)$ is bounded and $f'(x) = 0$ at its extreme points.]
] <thm:rolles>

#theorem(title: [Mean Value])[
  $ exists c in (a, b) : f'(c) = (f(b) - f(a))/(b - a) $

  #proof[Let the signed distance $d$ between the function value $f$ and the secant $y$ through $a$ and $b$ be
  $ d(x) = f(x) - y(x) =  f(x) - (f(b) - f(a))/(b - a) (x - a) - f(a) $
  and note that $d(a) = d(b) = 0$. Then apply @thm:rolles.
  ]
]

#theorem(title: [Generalized Mean Value])[
  $ exists c in (a, b) : [f(b) - f(a)] g'(c) = [g(b) - g(a)] f'(c) $
  If $g'$ is never zero on $(a, b)$, then the above can be stated as
  $ (f'(c))/(g'(c)) = (f(b) - f(a))/(g(b) - g(a)). $

  #proof[Let $h = f(x)[g(b) - g(a)] - g(x)[f(b) - f(a)]$ and then apply @thm:rolles.]
] <thm:gmv>

== Function Graphs

#tip-box(title: [Tip (Sketching Graphs)])[
  ==== Information
  + split into cases
  + symmetries
  + domain → vertical asymptotes
  + factorize → oblique asymptotes & roots
  + first and second derivative and their roots
  + sign tables
  + calculate interesting points: intersection with $y$-axis, defined non-differentiable points, local extremums, endpoints, inflection points
  
  ==== Sketching
  + axes
  + symmetries
  + asymptotes
  + interesting points
  + curves
]

=== Asymptotes

#definition(title: [Asymptote])[
  The line $y = k x + m$ is an _oblique_ asymptote of $f$ if
  $ lim_(x->infinity) (f(x) - (k x + m)) = 0. $

  The line $x = c$ is a _vertical_ asymptote of $f$ if
  $ lim_(x->c+) f(x) = plus.minus infinity #h(1.5em) "or" #h(1.5em) lim_(x->c-) f(x) = plus.minus infinity. $

  The line $y = b$ is a _horizontal_ asymptote of $f$ if
  $ lim_(x->infinity) f(x) = b #h(1.5em) "or" #h(1.5em) lim_(x->-infinity) f(x) = b. $
]

#theorem(title: [Oblique Asymptote])[ 
  If $f(x)$ has an oblique asymptote $y = k x + m$, then
  $ k = lim_(x->infinity) (f(x))/x $ and $ m = lim_(x->infinity) (f(x) - k x). $
]

=== Convexity

#theorem(title: [Convexity])[
  Let $f$ be twice differentiable on $(a, b)$.
  Then, $f''(x) >= 0$ if and only if $f$ is convex on $(a, b)$.
]

#definition(title: [Concave])[
  On $[a, b]$, a function $f : [a, b] -> RR$ is _concave_ if $-f$ is convex.
]

== Taylor's Theorem

#theorem(title: [Taylor's])[
  Let $f(x) : [a, b] -> RR$ and fix $c in [a, b]$.
  Suppose $f$ is continuously differentiable $n$ times on $[a, b]$ and $n + 1$ times on $(a, b)$. Then,
  $ f(x) = P_n (x) + R_n (x), $
  where the _Taylor polynomial_ of degree $n$ about $c$ is
  $ P_n (x) = sum_(k=0)^(n) (f^((k))(c))/k! (x - c)^k $
  and the _Lagrange remainder_ of degree $n$ is
  $ R_n (x) = (f^((n+1))(xi))/(n+1)! (x - c)^(n+1) $
  for some $xi$ between $c$ and $x$.

  Note that other remainder forms exist.

  #proof[Let $h = x - c$ be the deviation from the point. Then,
  $ f(x) = f(c + h) = sum_(k=0)^(n) (f^((k))(c))/k! h^k
  + (f^((n+1))(xi))/(n+1)! h^(n+1) = p_n (h) + r_n (h), $
  where $p_n (h)$ and $r_n (h)$ correspond to $P_n (x)$ and $R_n (x)$.

  Define
  $ F_(n,h)(t) = sum_(k=0)^(n) (f^((k))(t))/k! (c + h - t)^k, $
  with $F_(n,h)(c) = p_n(h)$ and $F_(n,h)(c + h) = f(c + h)$, and derivative
  $ F'_(n,h)(xi) = (f^((n+1))(xi)) / n! (c + h - xi)^n. $

  Also let
  $ g_(n,h) (t) = (c + h - t)^(n+1), $
  with $g_(n,h)(c) = h^(n+1)$ and $g_(n,h)(c + h) = 0$ and
  $ g'_(n,h)(xi) = -(n + 1)(c + h - xi)^n. $

  @thm:gmv gives
  $ (F_(n,h)(c+h) - F_(n,h)(c)) / (g_(n,h)(c+h) - g_(n,h)(c))
  = (F'_(n,h)(xi)) / (g'_(n,h)(xi)) $
  for some $xi$ between $c$ and $c + h$. Substituting,
  $ (f(c + h) - p_n (h))/(0 - h^(n+1)) =
  (f^((n+1))(xi) (c + h - xi)^n slash n!)/(-(n + 1)(c + h - xi)^n) $
  so
  $ f(c + h) - p_n (h) = (f^((n+1))(xi))/(n + 1)! h^(n+1). $
  Hence
  $ f(c + h) = p_n (h) + r_n (h) $
  or in $x$-notation
  $ f(x) = P_n (x) + R_n (x) $
  with $xi$ between $c$ and $x$.
  ]
]

#definition(title: [Radius of Convergence])[
  Fix $x$ and let $R_n (x)$ be the remainder to a Taylor polynomial around a point $c$.
  The _radius of convergence_ is the greatest $r$ such that
  $ abs(x - c) < r ==> lim_(n->infinity) R_n (x) = 0, $
  which implies that $f(x) = P_infinity (x)$.
  
]

=== Function Order

#definition(title: [Big _O_ at Infinity])[
  Let $f$ and $g$ be defined on $(c, infinity)$.
  We say that $f$ belongs to the set _O_ of $g$ as $x -> infinity$,
  writing $O(g(x))$, if there exists $M$ and $x_0$ such that
  $ abs(f(x)) <= M abs(g(x)), $
  for every $x > x_0$.
]

#definition(title: [Big _O_ at a Point])[
  Let $f$ and $g$ be defined on a neighborhood of $c$.
  We say that $f$ belongs to the set _O_ of $g$ around $c$,
  writing $O(g(x))$, if there exists $M$ and $delta > 0$ such that
  $ abs(f(x)) <= M abs(g(x)) $
  for every $x in (c - delta, c + delta)$.
]

#theorem(title: [Big _O_ Behavior])[
  Suppose $f$ and $g$ have $O(f(x))$ and $O(g(x))$
  defined around a point or infinity. Then,
  $ O(f(x)) O(g(x)) = O(f(x) g(x)). $

  If $m <= n$ then around $0$
  $ O(x^m) + O(x^n) = O(x^m) $
  and around $infinity$
  $ O(x^m) + O(x^n) = O(x^n). $
]

#theorem()[
  Let $f(x) : [a, b] -> RR$ and fix $c in [a, b]$.
  Suppose $f$ is continuously differentiable $n$ times on $[a, b]$ and $n + 1$ times on $(a, b)$. Then,
  $ f(x) = sum_(k=0)^n (f^((k))(c))/k! (x - c)^k + O(abs(x - c)^(n+1)) "as" x-> c. $

  Furthermore, the coefficients $f^((k))(c) slash k!$ are unique to each $(x - c)^k$.
]