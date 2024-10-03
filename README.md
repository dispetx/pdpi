# The Public Domain Programming Interface

**Abstract**

This paper introduces public domain internet as a special case of a
concept which we name public domain programming interface. It is based
on the dichotomy between public and not public.

**Introduction**

In mathematics, there exists a notion of a partition. If $X$ is a set, then a
partition of the set $X$ is any collection of sets
$A_{1}, A_{2}, A_{3}, \dots$, such that:

 - $$A_i \subseteq X \text{ for each } i$$,
 - $$A_i \cap A_j = \emptyset \text{ for all } i \neq j$$,
 - $$\bigcup_{i} A_i = X.$$

meaning the sets $A_1, A_2, A_3, \dots$ form a disjoint cover of $X$.


$$\bigcup_{i=1}^{\infty} A_i = X \quad \text{and} \quad A_i \cap A_j = \emptyset \quad \text{for} \quad i \neq j$$


In probability, events are expressed in terms of sets. Every event $A$
induces a natural partition $A \cup A^{c}$ of the sample space $S$ such
that:

$$P(A) + P(A^{c}) = 1.$$

This provides an interface to express or compute the probability of an event in
terms of the complement. In general, the exact definition of an event $A$
determines such a partition and the underlying problem may be easier or harder
depending on a particular choice. This is an interpretation of a general
strategy of decomposing a problem into subproblems.

In any case, the exact choice of a partition or partitions one is willing to
consider is usually not obvious a priori. Although there are natural partitions,
they may not be obvious. Thus, it is important to check if the partition is well
chosen.

In general, one can see any assumption or an implication to induce such an
interface. Thus, it is equally important to check if the assumptions are
well chosen too. The assumptions are arbitrary.

**Public Domain**

**Axiom 1** *All information is public.*

**Axiom 2** *Everyone is root.*

# Public Domain Internet

**Definition** *(Public Domain Internet) A public domain internet is the set
of all public internet hosts which satisfy axioms 1 and 2.*

**Implementation**

Currently, in a Github repository dispetx/ip there is a file ipaddress which
contains the IPv4 address of a public domain internet host. The IPv4 address
changes aproximatelly once a day and such changes are reflected in the ip
repository. 
