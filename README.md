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

```coq
(* Import necessary modules for sets and basic types *)
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Powerset_facts.
Require Import Coq.Reals.Rbase.

(* Definitions for the public domain programming interface *)

Module PublicDomainInterface.

  (* Define the set X as an ensemble (type with a membership property) *)
  Variable X : Type.

  (* Define a partition of X as a collection of subsets (Ai) that satisfy disjoint cover properties *)
  Definition is_partition (P : Ensemble (Ensemble X)) : Prop :=
    (forall A B : Ensemble X, A <> B -> Disjoint _ A B) /\
    (forall x : X, exists A : Ensemble X, In _ A x) /\
    (forall A : Ensemble X, In _ P A -> Included _ A X).

  (* Probability definitions *)

  (* Define a type for events as subsets of a sample space S *)
  Variable S : Type.
  Definition Event := Ensemble S.

  (* Probability measure P: Event -> [0, 1] *)
  Variable P : Event -> R.
  
  (* Hypothesis about valid probability values between 0 and 1 *)
  Hypothesis prob_axioms : forall A : Event, 0 <= P A <= 1.

  (* Define the complement of an event *)
  Definition complement (A : Event) : Event := fun s => ~ In _ A s.

  (* Probabilities of complements: P(A) + P(A^c) = 1 *)
  Hypothesis prob_complement : forall A : Event, P A + P (complement A) = 1.

  (* Public Domain Internet Axioms *)

  (* Define the public domain internet set *)
  Variable PublicInternet : Ensemble X.

  (* Axiom 1: All information is public *)
  Axiom public_information : forall x : X, In _ PublicInternet x.

  (* Axiom 2: Everyone is root (full access) *)
  Axiom everyone_is_root : forall x : X, True.

  (* Define the Public Domain Internet as the set of all hosts satisfying the two axioms *)
  Definition PublicDomainInternet (hosts : Ensemble X) :=
    (forall h : X, In _ hosts h -> public_information h) /\
    (forall h : X, In _ hosts h -> everyone_is_root h).

  (* Example of dynamic IP address *)

  (* Define a type for IP address *)
  Variable IP : Type.

  (* Function that returns the current IP address based on a timestamp (daily change) *)
  Variable current_ip : nat -> IP.

  (* Hypothesis that the IP changes approximately once a day *)
  Hypothesis ip_changes_daily : forall t : nat, current_ip t <> current_ip (t + 1).

  (* Simple Statements and Proofs *)

  (* Statement 1: The complement of the complement of an event is the event itself *)
  Lemma complement_involution : forall A : Event, complement (complement A) = A.
  Proof.
    intros A.
    unfold complement.
    apply Extensionality_Ensembles.
    split.
    - intros x H. unfold In in H. unfold not in H. apply NNPP. exact H.
    - intros x H. unfold In. unfold not. intro. contradiction.
  Qed.

  (* Statement 2: The probability of the union of an event and its complement is 1 *)
  Lemma prob_union_complement : forall A : Event, P A + P (complement A) = 1.
  Proof.
    intros A.
    apply prob_complement.
  Qed.

  (* Statement 3: The IP address changes after each day *)
  Lemma ip_changes_daily_example : forall t : nat, current_ip t <> current_ip (t + 1).
  Proof.
    intros t.
    apply ip_changes_daily.
  Qed.

End PublicDomainInterface.
```

It is probably true that any nonsense can be made formal truth. One can come up
with any number of arbitrary axioms and definitions and formalize anything. As
long as nobody finds a contradiction, the theory is considered or believed to
be consistent or true. Before machine-proof-checkers like Coq it was very hard
to be sure about formal reasoning. Formal reasoning is a tricky thing, where it
is easy to overlook something or make other errors in the process. Such errors
can invalidate the whole argument or proof. It takes years of practice to be
able to think "formally" about simple mathematical objects. Although in society
in general everything is formalized to some extent, many such formal structures
are arbitrary and can be changed. We are usually trained to exist inside of
those formal structures, but we are rarely invited to change them or to even
think about them. Let us consider three categories of people: mathematicians,
computer scientists and the rest. For example, let us start with Euler. 

Euler is considered to be one of the most productive mathematicians ever to
live when one considers just the amount of words in mathematical papers. One
of his first discoveries was the fact that the Zeta function of 2 is equal to
$\frac{pi^2}{6}. The Zeta function is an infinite series defined by:

$$\zeta(s) = \sum_{n=1}^{\infy} \frac{1}{n^{s}}$$
