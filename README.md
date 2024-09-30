# The Public Domain Programming Interface

**Abstract**

This paper introduces the public domain internet as a special case of a
concept which we name the public domain programming interface. It is based
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
choosen.

In general, one can see any assumption or an implication to induce such an
interface. Thus, it is equally important to check if the assumptions are
well choosen too. The assumptions are arbitrary.

**Public Domain**

In this paper the word public is taken as a primitive just as the increment or 
successor operation is taken as a primitive in Peano's axioms of natural
numbers. We condition on all information being public.

**Axiom 1** *All information is public.*

This is the simplest and the most natural assumption which avoids the question:
Is $X$ public? It just assumes that $X$ is public and we are free to do so.
We follow this axiom because otherwise we would need to define the primitive
public. There are many choices for a possible definition and we want to avoid
all of them.

If we have declared all information as public, didn't we lose the partition of
the problem in it's public and private part? No. The non-public part is an empty
set and we use just the terminology appropriate for discussing the public
part. 

**Axiom 2** *Everyone is root.*

To assume otherwise is to come up with a partition of those who are root and
those who are not root. As before, there are many such choices and we avoid
them all.

**Definition** *(The Public Domain Internet) The public domain internet is the set
of all public internet hosts which satisfy axioms 1 and 2.*
