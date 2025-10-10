#import "style.typ": *
#import "@preview/physica:0.9.5": dd, derivative, arccot

#show: show-theorion
#show: styling.with(
  course_name: "Analys i en variabel",
  course_code: "SF1673 (HT25)",
  title_size: 30pt,
  title_space: 0em, 

  size: 12pt,
  margin: 0.5cm,
  width: 15cm,
  height: auto,
  heading_break: true,
  contents: true,
)

= The Real Numbers

== Reals

=== Prerequisites

#theorem(title: [Induction])[
  Let $S subset.eq NN$. If
  + $1 in S$, and
  + $n in S ==> n + 1 in S$ (inductive step),
  then $S = NN$.
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
  Every bounded, nonempty set of real numbers has a least upper bound.
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
  $A$ is _countably infinite_ if $NN tilde A$.

  $A$ is _countable_ if it is finite or countably infinite.

  Otherwise, $A$ is _uncountable_.
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
  Let $(I_n)$ be a nested sequence of nonempty closed and bounded intervals with
  $ I_1 supset.eq I_2 supset.eq I_3 supset.eq dots.h.c. $
  Then $ inter.big_(n=1)^infinity I_n != emptyset. $
  In particular, there exists $a in inter.big_(n=1)^infinity I_n$.
]

=== Open and Closed Sets

#definition(title: [Open/Closed Set])[
  $A subset.eq RR$ is _open_ if $forall a in A space exists V_epsilon (a) subset.eq A$ or equivalently if its complement is closed.
  
  $A subset.eq RR$ is _closed_ if it contains its limit points or equivalently if its complement is open.
]

#theorem(title: [Clopen Sets])[
  $RR$ and $emptyset$ are _clopen_ (both opened and closed).
]

#theorem(title: [Unions/Intersections])[
  + Arbitrary unions of open sets are open; finite intersections of open sets are open.
  
  + Arbitrary intersections of closed sets are closed; finite unions of closed sets are closed.  
]

=== Compactness

#definition(title: [Compact])[
  A set $K$ in a topological space is _compact_ if every open cover has a finite subcover.
]

#theorem(title: [Heine--Borel])[
  A set $K subset.eq RR^n$ is compact if and only if it is closed and bounded.
]

#note-box[Compactness is like a generalization of closed intervals.]

= Limits

== Sequences

#definition(title: [Sequence])[
  A _sequence_ is a function whose domain is $NN.$
]

#definition(title: [Convergence])[
  A sequence _converges_ to $a$ if
  $ forall epsilon > 0 space exists N in NN : n >= N ==> |a_n - a| < epsilon $
  or equivalently if for any $V_epsilon (a)$ there exists a point
  in the sequence after which all terms are in $V_epsilon (a)$.
  In other words, if every $epsilon$-neighborhood of some point
  contains all but a finite number of the terms in $(a_n)$.

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

#theorem(title: [Convergent])[
  Every convergent sequence is bounded.

  If a sequence is monotone and bounded it converges.

  Subsequences of a convergent sequence converge to the same limit.
]

#theorem(title: [Bolzano--Weierstrass])[
  In a compact set $K subset.eq RR$,
  every bounded sequence contains a convergent subsequence
  whose limit point is in $K$.
] <thm:bolzano-weierstrass>

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

#theorem(title: [Cauchy Criterion for Series])[
  The series $sum_(k=0)^infinity a_k$ converges if and only if
  $ forall epsilon > 0 space exists N : n > m > N ==> abs(a_m + a_(m+1) + dots.h.c + a_(n-1) + a_n) < epsilon. $
]

#corollary(title: [Series Term Test])[
  If $sum^infinity_(k=1) a_k$ converges, then $a_k -> 0$.
  However, the reverse implication is false.
]

#lemma[
  The series $sum_(j=1)^infinity 1 slash j$ is divergent.
]

#theorem()[
  The series $sum_(j=1)^infinity 1 slash j^p$ converges if and only if $p > 1$.
]

#theorem(title: [Ratio Test])[
  Let $(a_n)$ be a sequence of positive terms and define
  $ L = limsup_(n->infinity) abs(a_(n+1)/a_n). $
  Then:
  + If $L < 1$, the series $sum_(n=1)^infinity a_n$ converges.
  + If $L > 1$ (including $L = infinity$), the series diverges.
  + If $L = 1$, the test is inconclusive.
]

#theorem(title: [Cauchy Condensation Test])[
  Let $(a_n)$ be a decreasing sequence of nonnegative real numbers.
  Then $sum_(n=1)^(infinity) a_n$ converges if and only if $sum_(n=0)^(infinity) 2^n a_(2^n)$ converges.
]

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

== Functions

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

=== Existence

#theorem(title: [Continuity])[
  The following are equivalent:
  + $f : A subset.eq RR -> RR$ is _continuous_ at $c in A$.
  + $forall epsilon > 0 space exists delta > 0 : |x - c| < delta ==> |f(x) - f(c)| < epsilon$, where $x in A$.
  + $forall V_epsilon (f(c)) space exists V_delta (c) : x in V_delta (c) inter A ==> f(x) in V_epsilon (f(c))$
  + $x_n -> c$, where $(x_n) subset.eq A$, implies $f(x_n) -> f(c)$.
  If $c$ is a limit point of $A$:
  5.  $lim_(x->c) f(x) = f(c)$, also written $lim_(h->0)f(c + h) - f(c) = 0$.

  Note that (ii) defines (i). Mostly (v) is used in practice.
]

#corollary(title: [Isolated Continuity])[
  All functions are continuous at isolated points.
]

#theorem(title: [Dirichlet Discontinuous])[ 
  The Dirichlet function $f : RR -> RR$ such that $f(x) = 1$ if $x in QQ$ and
  $f(x) = 0$ if $x in II$ is discontinuous everywhere.
]

#definition(title: [Uniform Continuity])[
  We say $f$ is _uniformly continuous_ on $I$ if
  $ forall epsilon > 0 space exists delta > 0 :
  x, y in I, abs(x - y) < delta ==> abs(f(x) - f(y)) < epsilon. $
  In particular, $delta$ can be chosen independent of $y$.
]

#theorem()[
  If a function is uniformly continuous, it is also continuous.
]

#theorem(title: [Heine--Cantor])[
  If $f$ is continuous and defined on a compact set $K$, then it is also uniformly continuous on $K$.

  #proof[Assume the opposite, that $f$ is continuous but not uniformly.
  Since $f$ is not uniformly continuous,
  $ exists epsilon_0 > 0 : forall delta > 0 space exists x, y in K :
  space abs(x - y) < delta "but" abs(f(x) - f(y)) >= epsilon_0. $

  Now, choose $(x_n)$ and $(y_n)$ such that
  $ abs(x_n - y_n) < 1/n space "and" space abs(f(x_n) - f(y_n)) >= epsilon_0. $
  @thm:bolzano-weierstrass asserts that there exists some subsequence
  $x_n_k -> x_0$ for some $x_0 in K$.
  From $abs(x_n - y_n) < 1/n$ it follows that $y_n_k -> x_0$. Thus,
  $ abs(x_n_k - y_n_k) -> 0, $
  and, because $f$ is continuous with $f(x_n_k) -> x_0$ and $f(y_n_k) -> x_0$,
  $ abs(f(x_n_k) - f(x_n_k)) -> 0. $
  However, this contradicts our assumption that
  $ abs(f(x_n_k) -> f(y_n_k)) >= epsilon_0. $
  ]
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
] <thm:intermediate>

#theorem(title: [Weierstrass Extreme Value])[
  If $f$ is continuous on the compact set $K$,
  then $f$ attains a maximum and a minimum value on $K$.
] <thm:extreme>

#theorem(title: [Limit of Bounded Function])[
  If $f$ is bounded then $lim_(h->0) f(h) h = 0.$
]

= Calculus

== The Derivative

=== Differentiation

#definition(title: [Derivative at a Point])[
  Let $f : A -> RR$ and $c$ a limit point of $A$. If
  $ f'(c) = lim_(h->0) (f(c + h) - f(c))/h $
  exists (finite), we say $f$ is _differentiable_ at $c$.
]

#theorem(title: [Chain Rule])[
  Let $f : X -> Y$ and $g : Y -> RR$.
  If $f$ is differentiable at $c in X$ and
  $g$ is differentiable at $f(c) in Y$,
  then $g compose f$ is differentiable at $c$ with
  $ (g compose f)'(c) = g'(f(c)) f'(c). $
] <thm:chain>

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
      &(f^(-1))'(y) = 1/(f'(x)) #h(0.7em) (y = f(x), f'(x) != 0)
    $],
  )
)

#theorem(title: [L'Hôpital's Rule])[
  Let $f$ and $g$ be differentiable on an open interval containing $c$
  (except possibly at $c$), with $g'(x) != 0$ near $c$. Suppose
  + $lim_(x->c) f(x) = lim_(x->c) g(x) = 0$
    (or both $plus.minus infinity$), and
  + $lim_(x->c) (f'(x))/(g'(x)) = L$ exists (or $plus.minus infinity$).
  Then, $ lim_(x->c) (f(x))/(g(x)) = L. $

  #proof(title: "Proof of the zero case")[Assume the limits are zero.

  Let the functions be differentiable on the open interval $(c, x)$.
  Then, rewriting and applying @thm:gmv gives
  $ lim_(x->c) f(x)/g(x) = lim_(x->c) (f(x)-f(c))/(g(x)-g(c))
  = lim_(x->c) (f'(p))/(g'(p)) = lim_(p->c) (f'(p))/(g'(p)) $
  for some $p "between" c "and" x$.
  ]

  #proof(title: "Proof of the infinity case")[The proof is too complicated.
  // Assume the limits are infinite. We will only prove the right-hand limit.
  // Let $c < a < b$.
  // The @thm:gmv states that there exists a $p in (a, b)$ such that
  // $ f'(p)[g(b) - g(a)] = g'(p)[f(b) - f(a)]. $
  // Solving for $f(a)$, we get 
  // $ f(a) = f(b) + (f'(p)(g(a) - g(b)))/(g'(p)). $
  // We divide by $g(a)$ and get
  // $ f(a)/g(a) = (f'(p))/(g'(p)) + 1/g(a) (f(b)-g(b) (f'(p))/(g'(p))) $
  // which we rewrite as
  // $ f(a)/g(a) - L =
  // (f'(p))/(g'(p)) - L + 1/g(a) (f(b)-g(b) (f'(p))/(g'(p))) $
  ]
]

#important-box[
  This is only an implication, not an equivalence,
  so there may exist some other solution if this method fails.
]

=== Function Character

#theorem(title: [Fermat's or Interior Extremum])[
  Let $f : (a, b) -> RR$  be differentiable at the local extremum
  $c in (a, b)$. Then $f'(x) = 0$.

  However, note that a zero-derivative point may also be
  a stationary point of inflection. 
] <thm:fermat>

#theorem(title: [Darboux's])[
  If $f$ is differentiable on $[a, b]$ and if $y$ lies strictly between $f'(a)$ and $f'(b)$, then $exists c in (a, b) : f'(c) = y$.

  In other words, if $f$ is differentiable on an interval,
  then $f'$ satisfies the Intermediate Value Property (IVP).

  #proof[Assume that $f'(a) < y < f'(b).$

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

  #proof[$f(x)$ is bounded and $f'(x) = 0$ at its interior extreme points.]
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
  + symmetries
  + split into cases
  + domain → vertical asymptotes
  + factorize → oblique asymptotes & roots
  + first and second derivative and their roots
  + sign tables
  + calculate interesting points: intersection with $y$-axis, defined nondifferentiable points, local extremums, endpoints, inflection points
  
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

=== Points

#definition(title: [Local Extremum])[
  A _local maximum_ of $f : D subset.eq RR -> RR$ is a point $c$ for which
  there exists an open neighborhood $N(c) subset.eq D$ such that
  $ f(c) >= f(x) quad forall x in N(c). $
]

#definition(title: [Stationary])[
  The point $c$ is a _stationary point_ of $f$ if $f'(c)=0$.

  The _stationary order_ is the smallest $n>=2$ such that
  $ f'(c) =  f''(c)=dots.h.c=f^((n-1))(c)=0 space "but" space f^((n))(c)!=0. $
]

#definition(title: [Critical])[
  The point $c$ is a _critical point_ if $f(c)$ is stationary or undefined.
]

#definition(title: [Inflection])[
  A point $c$ is an _inflection point_ of $f$ if $f$ is continuous at $c$ and if $f$ is convex on one side of $c$ and concave on the other side.
]

#theorem(title: [First Nonzero Derivative])[
  If $f$ has stationary order $n$, then:
  - If $n$ is _even_ $==>$ $f$ has a local extremum at $c$.

    Furthermore: $f^((n))(c)>0$ $==>$ local minimum, $f^((n))(c)<0$ $==>$ local maximum.
  - If $n$ is _odd_ $==>$ $c$ is a stationary inflection point.

  #proof[The Taylor series with remainder simplifies to
  $ f(c +  h)=f(c)+(f^((n))(c))/n! h^n+O(h^(n+1)). $
  Its change close to $c$ is thus
  $ f(c + h) - f(c) approx (f^((n))(c))/n! h^n, $
  which changes sign if and only if $n$ is odd.
  Similarly,
  $  f'(c + h) - f'(c) approx (f^((n-1))(c))/(n-1)! h^(n-1) $
  for the first derivative and
  $ f''(c + h) - f''(c) approx (f^((n-2))(c))/(n-2)! h^(n-2) $
  for the second derivative.
  ]
]

#corollary(title: [Second Derivative Test])[
  If $f''$ is continuous at $c$ and $f'(c)=0$, then:
  - $f''(c)>0$ $==>$ local minimum.
  - $f''(c)<0$ $==>$ local maximum.
  - $f''(c)=0$ and $f^((3))(c)!=0$ $==>$ stationary inflection point.  
  Note: $f''(c)=0$ alone is insufficient for an inflection; the curvature must change sign.
]

#example(title: [Examples])[
  - $f(x)=x^3$: $f'(0)=f''(0)=0$, $f^((3))(0)=6!=0$ (odd $n=3$) $==>$ stationary inflection at $0$.
  - $f(x)=x^4$: $f'(0)=f''(0)=f^((3))(0)=0$, $f^((4))(0)=24>0$ (even $n=4$) $==>$ local minimum at $0$, no inflection.
  - $f(x)=-x^4$: local maximum at $0$, no inflection.
]

== The Riemann Integral

=== Definition

#definition(title: [Partition])[
  A _partition_ of $[a,b]$ is a finite set $ P = {x_0, x_1, dots.h.c, x_n} $
  such that $ a = x_0 < x_1 < dots.h.c < x_n = b, $
  
  The partition $P$ has _subintervals_
  $ [x_(i-1), x_i] quad i = 1, 2, ..., n $
  of which the length of the largest is its _mesh_ or _norm_
  $ norm(P) = max_(1<=i<=n) (x_i - x_(i-1)). $
  A smaller such is indicative of a finer partition.
]

Let $f : [a,b] -> RR$ be bounded. We now define its definite integral.

#definition(title: [Darboux Integral])[
  Define the _lower sum_
  $ L(f,P) = sum_(i=1)^n (inf { f(x) : x in [x_(i-1), x_i] }) (x_i - x_(i-1)). $
  and the _upper sum_
  $ U(f,P) = sum_(i=1)^n (sup { f(x) : x in [x_(i-1), x_i] }) (x_i - x_(i-1)) $
  The function $f$ is _Darboux integrable_ if $sup_P L(f,P) = inf_P U(f,P)$. 
  The common value is denoted as the _definite integral_ $ integral_a^b f(x) dd(x)$.
]

#definition(title: [Alternative Darboux Integral])[
  Let $Phi$ and $Psi$ be the _lower and upper step functions_ such that
  $ Phi(x) <= f(x) <= Psi(x) quad forall x in [a, b], $
  forming the _lower integral_
  $ L(f) = sup{integral_a^b Phi(x) dd(x) : Phi "is a lower step function to" f} $
  and the _upper integral_
  $ U(f) = inf{integral_a^b Psi(x) dd(x) : Psi "is an upper step function to" f} $
  which, if equal, give the definite integral.

  Note that the integral of a step function is simply its signed area.
]

#definition(title: [Riemann Integral])[
  From a partition $P$ of $[a, b]$ pick _sample points_
  $ t_i in [x_(i-1), x_i], quad i = 1, 2, ..., n $
   and form the (tagged) _Riemann sum_
  $ S(f, P, (t_i)) = sum_(i=1)^n f(t_i) (x_i - x_(i-1)). $

  We say $f$ is _Riemann integrable_ if there exists $L in RR$ such that
  $ forall epsilon > 0 space exists delta > 0 : norm(P) < delta ==> |S(f,P,(t_i)) - L| < epsilon $
  for every choice of sample points $(t_i)$. In that case we write
  $ L = integral_a^b f(x) dd(x). $
]

#theorem()[
  The Darboux and Riemann integrals are equivalent.
]

=== Integrability

#theorem(title: [Integrability])[
  Let $f : [a, b] -> RR$ be bounded.

  The function is integrable if and only if:
  + $forall epsilon > 0 space exists P : U(f,P) - L(f,P) < epsilon$.
  + $forall (P_n) : norm(P_n) -> 0 ==> U(f,P_n) - L(f,P_n) -> 0.$
  + (Lebesgue Criterion for Riemann Integrability) \
    Its set of discontinuities has Lebesgue measure zero.
  + $ forall epsilon > 0 space exists Phi, Psi :
    integral_a^b Psi(x) dd(x) - integral_a^b Phi(x) dd(x) < epsilon, $
    where $Phi$ and $Psi$ are lower and upper step functions.
  
  The function is integrable if:
  3. $f$ is _monotone_ on $[a, b]$
  + $f$ is continuous except at finitely many points, or at countably many points where it has only removable or jump discontinuities.
]

#theorem()[
  Assume $f$ is continuous on $[a, b]$. Let
  $ M_i = max_(x in [x_(i-1), x_i]) f(x)
  space "and" space
  m_i = min_(x in [x_(i-1), x_i]) f(x). $
  Then,
  $
  lim_(norm(P)->0) sum_(i=1)^n M_i (x_i - x_(i-1)) =
  lim_(norm(P)->0) sum_(i=1)^n m_i (x_i - x_(i-1)) =
  integral_a^b f(x) dd(x).
  $
]

#theorem(title: [Absolute Value / Triangle])[
  If $f$ integrable, then $|f|$ integrable and
  $ abs(integral_a^b f(x) dd(x)) <= integral_a^b |f(x)| dd(x). $
]

#theorem(title: [Products and Composition])[
  If $f,g$ integrable, then $f g$ is integrable.
  
  If $f$ integrable and $phi$ continuous on a set containing $f([a,b])$, then $phi compose f$ is integrable.
]

#theorem(title: [Uniform Limit])[
  If $(f_n)$ are integrable on $[a,b]$ and $f_n -> f$ uniformly, then $f$ is integrable and
  $ integral_a^b f_n (x) dd(x) -> integral_a^b f(x) dd(x). $
]

=== Properties

#theorem(title: [Linearity])[
  If $f,g$ are integrable and $alpha, beta in RR$, then
  $ integral_a^b (alpha f(x) + beta g(x)) dd(x)
  = alpha integral_a^b f(x) dd(x)  + space  beta integral_a^b g(x) dd(x). $
]

#theorem(title: [Additivity of the Interval])[
  If $c in (a,b)$ and $f$ integrable on $[a,b]$, then
  $ integral_a^b f(x) dd(x) = integral_a^c f(x) dd(x) + integral_c^b f(x) dd(x). $
  It follows that $ integral_a^a f(x) dd(x) = 0$ and $integral_b^a f(x) dd(x) = - integral_a^b f(x) dd(x).$
]

#theorem(title: [Order / Comparison])[
  If $f,g$ integrable and $f(x) <= g(x)$ on $[a,b]$, then
  $ integral_a^b f(x) dd(x) <= integral_a^b g(x) dd(x). $
] <thm:integral-comparison>

#corollary(title: [Positivity])[
  If $f(x) >= 0$ on $[a,b]$, then $ integral_a^b f(x) dd(x) >= 0$. Moreover, if $f$ is continuous and the integral is $0$, then $f equiv 0$.
]

#theorem(title: [Bounding by a Supremum])[
  If $|f(x)| <= M$ on $[a,b]$, then
  $ abs(integral_a^b f(x) dd(x)) <= M (b - a). $
]

#theorem(title: [Mean Value for Integrals])[
  If $f$ is continuous on $[a, b]$, then
  $ integral_a^b f(x) dd(x) = f(xi) (b - a). $
  for some $xi in [a, b]$ or,
  to be more strict if $f$ is not constant, $xi in (a, b)$.
] <thm:mean-integrals>

#theorem(title: [Generalized Mean Value for Integrals])[
  If $f$ is continuous and $g$ is integrable and
  does not change sign on $[a, b]$,
  $ integral_a^b f(x) g(x) dd(x) = f(xi) integral_a^b g(x) dd(x) $
  for some $xi in [a, b]$ or,
  to be more strict if $f$ is not constant, $xi in (a, b)$.
  
  #proof[Let $m = min f(x)$ and $M = max f(x)$ for $x in [a, b].$ Then,
    $ m integral_a^b g(x) <= integral_a^b f(x) g(x) <= M integral_a^b g(x) $
    by @thm:integral-comparison, or rewritten,
    $ m <= 1/(integral_a^b g(x)) integral_a^b f(x) g(x) <= M. $
    Since $m <= f(x) <= M$, @thm:intermediate gives that
    $ f(xi) = 1/(integral_a^b g(x)) integral_a^b f(x) g(x) $
    for some $xi in [a, b]$. Rewritten, this is the theorem.
  ]
]

#theorem(title: [Fundamental Theorems of Calculus])[
  If $f$ is continuous on $[a, b]$, then the two theorems follow:
  
  + Let $F(x) = integral_a^x f(t) dd(t)$ for $x in [a, b]$.
    Then, $F$ is continuous on $[a, b]$,
    differentiable on $(a, b)$, and $F'(x) = f(x).$

    #proof[We want to show that $F'(x) = f(x)$.

      Applying the definition of derivatives,
      $ F'(x) = lim_(h->0) 1/h (F(x+h) - F(x))
      = lim_(h->0) 1/h integral_x^(x+h) f(x) dd(x), $ 
      where $x$ and $x + h$ are in $(a, b)$.
      By @thm:mean-integrals,
      $ integral_x^(x+h) f(t) dd(t) = f(xi) h $
      for some $xi$ between $x$ and $x + h$,
      which in our previous result gives
      $ F'(x) = lim_(h->0) f(xi) = f(x) $
      since $f$ is continuous.
    ]
    
  + If $F'(x) = f(x)$ for $x in (a, b)$, then
    $ integral_a^b f(x) dd(x) = F(b) - F(a). $

    #proof[Let $G(x)$ have $G'(x) = f(x) = F'(x)$ for all $x in (a, b)$.
    Then, $G'(x) - F'(x) = 0$ gives that $G(x) - F(x) = C$ for some constant.
    We have $G(a) - F(a) = C$, but
    $ G(a) = integral_a^a f(t) dd(t) = 0, $
    so $C = -F(a)$ and hence $G(b) = F(b) - F(a)$, but by definition
    $ G(b) = integral_a^b f(t) dd(t), $
    so the statement holds.
    ]
] <thm:fundamental>

=== Integration Techniques

#theorem(title: [Integration by Substitution])[
  Also known as _change of variables_ or _u-substitution_.

  Let $g$ be continuously differentiable on $[a,b]$
  and let $f$ be continuous on $g([a, b])$.
  Then, with $u = g(x)$ and $dd(u) = g'(x) dd(x)$,
  $ integral_a^b f(g(x)) g'(x) dd(x) = integral_(g(a))^(g(b)) f(u) dd(u). $

  Equivalently, if $g$ is strictly monotonic and 
  thus invertible as $x = g^(-1)(u)$,
  $ integral_a^b f(x) dd(x) =
  integral_(g^(-1)(a))^(g^(-1)(b)) f'(g(u)) g'(u) dd(u). $

  #proof[We prove the first formulation of the theorem. We have,
    $
    integral_a^b f(g(x)) g'(x)
    = [f(g(x))]_a^b
    = [f(u)]_(g(a))^(g(b))
    = integral_(g(a))^(g(b)) f(u) dd(u)
    $   
    according to @thm:fundamental (ii) and @thm:chain.
  ]
]

#theorem(title: [Integration by Parts])[
  If $f,g$ are continuously differentiable on $[a,b]$, then
  $ integral_a^b f(x) g(x) dd(x) = [F(x) g(x)]_a^b - integral_a^b F(x) g'(x) dd(x). $
] <thm:parts>

#tip-box(title: [LIATE])[
  The LIATE rule helps choose $f(x)$ and $g(x)$ for integration by parts:
  - Logarithmic: $ln(x)$, $log_a(x)$
  - Inverse trigonometric: $arctan(x)$, $arcsin(x)$, $arccos(x)$
  - Algebraic: $x$, $x^2$, $x^3$, etc.
  - Trigonometric: $sin(x)$, $cos(x)$, $tan(x)$, etc.
  - Exponential: $e^x$, $a^x$
  Choose $g(x)$ as the function that appears first in this list.
]

#tip-box(title: [Arctangent Rules])[
  + Addition: $(a b < 1, "otherwise add or subtract" pi slash 2)$
    $ arctan(a) + arctan(b) = arctan((a + b)/(1 - a b)) $
  + Subtraction: $(a b > 1, "otherwise add or subtract" pi slash 2)$
    $ arctan(a) - arctan(b) = arctan((a - b)/(1 + a b)) $
  + Inverse:
    $ arctan(x) = -arctan(-x) $
  + Integration:
    $
    integral a/(b^2 + c^2 x^2) dd(x)
    &= a/b^2 integral 1/(1 + c^2 x^2 slash b^2) \
    &= vec(u &= c x slash b, dd(u) &= c slash b, delim: "{") \
    &= a/(b c) integral 1/(1 + u^2) dd(u) \
    &= a/(b c) arctan((c x)/b)
    $
]

== Taylor's Theorem

#theorem(title: [Taylor's])[
  Suppose $f$ is continuously differentiable $n$ times on $[a, b]$ and $n + 1$ times on $(a, b)$. Fix $c in [a, b]$. Then,
  $ f(x) = P_n (x) + R_n (x), $
  where the _Taylor polynomial_ of degree $n$ around $c$ is
  $ P_n (x) = sum_(k=0)^(n) (f^((k))(c))/k! (x - c)^k $
  and the _Lagrange remainder_ of degree $n$ around $c$ is
  $ R_n (x) = (f^((n+1))(xi))/(n+1)! (x - c)^(n+1) $
  for some $xi$ strictly between $c$ and $x$.

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
    with $xi$ strictly between $c$ and $x$.
  ]
  
  #proof(title: [Proof using integrals])[From @thm:fundamental (ii) we have
    $ integral_c^x f'(t) dd(t) = f(t) - f(c) $
    which we expand using @thm:parts as
    $ f(x)
    &= f(c) + integral_c^x 1 dot f'(t) dd(t) \
    &= f(c) + [(t-x)f'(t)]_c^x  - integral_c^x (t-x)f''(x) dd(t) \
    &= f(c) + f'(c)(x - c) - ([(t-x)^2/2 f''(t)]_c^x -
    integral_c^x (t-x)^2/2 f^((3))(t) dd(t)) \
    &= f(c) + f'(c)(x-c) + (f''(t))/2 (x-c)^2 +
    integral_c^x (t-x)^2/2 f^((3))(t) dd(t) \
    &= dots.h.c \
    &= P_n (x) + (-1)^n integral_c^x (t-x)^n/n! f^((n+1))(t) dd(t)
    $
  ]
]

#definition(title: [Radius of Convergence])[
  Let $R_n (x)$ be the remainder to the Taylor polynomial around a point $c$.
  The _radius of convergence_ $R$ is the supremum of $r >= 0$ such that
  $ forall x : abs(x - c) < r ==> lim_(n->infinity) R_n (x) = 0, $
  which implies that the Taylor series converges to $f(x)$ for all such $x$ (so $f(x) = P_infinity (x)$).
]

#theorem(title: [Common Maclaurin Series])[
  The following functions have a Maclaurin series with radius of convergence $r = infinity$:
  #block[$
  & e^x = sum_(k=0)^infinity x^k / k! = 1 + x + x^2/2! + x^3/3! + dots.h.c \
  & sin x = sum_(k=0)^infinity (-1)^k x^{2k+1} / (2k+1)! = x - x^3/3! + x^5/5! - dots.h.c \
  & cos x = sum_(k=0)^infinity (-1)^k x^{2k} / (2k)! = 1 - x^2/2! + x^4/4! - dots.h.c \
  & arctan x = sum_(k=0)^infinity (-1)^k x^{2k+1} / (2k+1) = x - x^3/3 + x^5/5 - x^7/7 + dots.h.c quad(|x| <= 1) \
  & ln(1 + x) = sum_(k=1)^infinity (-1)^{k+1} x^k / k = x - x^2/2 + x^3/3 - x^4/4 + dots.h.c quad(|x| < 1) \
  & (1 + x)^a = sum_(k=0)^infinity binom(a, k) x^k quad(|x| < 1) \
  $]
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
  If $h(x) = O(f(x))$ and $k(x) = O(g(x))$ (same limiting regime), then $h(x) k(x) = O(f(x) g(x))$.

  If $m <= n$ then as $x -> 0$, $x^n = O(x^m)$ so $O(x^m) + O(x^n) = O(x^m)$. As $x -> infinity$, $x^m = O(x^n)$ so $O(x^m) + O(x^n) = O(x^n)$.
]

#theorem()[
  Let $f(x) : [a, b] -> RR$ and fix $c in [a, b]$.
  Suppose $f$ is continuously differentiable $n$ times on $[a, b]$ and $n + 1$ times on $(a, b)$. Then,
  $ f(x) = sum_(k=0)^n (f^((k))(c))/k! (x - c)^k + O(abs(x - c)^(n+1)) "as" x-> c. $

  Furthermore, the coefficients $f^((k))(c) slash k!$ are unique to each $(x - c)^k$.
]

== Ordinary Differential Equations

#v(10em)