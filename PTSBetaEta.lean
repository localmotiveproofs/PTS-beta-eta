module

public import PTSBetaEta.Main
public import PTSBetaEta.Eta.Counterexample

/-!
# Weak and strong βη-normalization in pure type systems with βη-conversion

The main theorems are in `PTSBetaEta.Main`.
The library has three parts.

* `PTSBetaEta.Beta` is OpenAI's formalization of the β case, copied under the Apache License 2.0.
* `PTSBetaEta.Eta` contains η-reduction, domain erasure and confluence, typing with βη-conversion and its metatheory, and the paradox half of the argument.
* `PTSBetaEta.Normalization` adapts OpenAI's candidate models to typing with βη-conversion. Its candidates are indexed by keys, which are βη-normal forms of erased types, and its observation values are η-canonical.

## Terminology from OpenAI's preprint

The comments in `PTSBetaEta.Beta` and `PTSBetaEta.Normalization` use the terms below.
Most of them come from OpenAI's preprint *Weak and strong normalization in pure type systems*.
Where a comment uses a plain description instead, it gives OpenAI's term in parentheses at its first use in the file.

### Profiles and graphs

* The **profile** of a type `T` (`Profile`) is the set of sorts that the normal form of `T` has as its type.
* `(I, J, K)` is a **profile triple** (`ProfileTriple`) when `K` is the set of sorts `c` such that some rule `(a, b, c)` has `a ∈ I` and `b ∈ J`. It describes the profiles of the domain, the codomain and the whole of a product.
* The **primary graph** (`PrimaryEdge`) has the feasible profiles as vertices. Each profile triple `(I, J, K)` gives a negative edge from `I` to `K` and a positive edge from `J` to `K`, and a profile has a positive edge to each of its proper subsets. The **parity** of a path is the number of its negative edges modulo two.
* A **component** (`IsComponent`) is a strongly connected component of the primary graph. The proof processes the components one at a time, predecessors first.
* For the component `C` being processed, the **secondary graph** (`SecondaryEdge`) starts from the axiom profiles `Ax(s)` of the sorts `s` with `{s} ∈ C`, which OpenAI calls **seeds**.
* A vertex `I` of the secondary graph is **direct** (`DirectLayer`) when some profile triple `(I, J, K)` has `J` and `K` in `C`. It is **active** (`ActiveLayer`) when it has a path to a direct vertex.
* An active vertex is **plain** (`PlainLayer`) when it has paths of both parities to direct vertices. Otherwise it is **free** (`FreeLayer`). A free vertex has **sign `+`** when these paths are even and **sign `−`** when they are odd. OpenAI calls the corresponding values **plus** and **minus** values.
* The **layer** of a type is its profile. A type is active, plain or free when its layer is.
* The **forbidden configuration** (`ForbiddenConfiguration`) is a pattern in the secondary graph. **Relational exclusion** (`RelationalExclusion`) says that it does not occur, and the paradox half of the proof derives this from weak normalization.

### Candidates

* The **context tower** `Ω` (`ContextTower`) is an infinite context that declares every type again arbitrarily late. Its finite prefixes are valid contexts.
* An **actual type** (`ActualType`) is a normal type over the tower that has a sort as its type, or a sort.
* `Top T` is OpenAI's `⊤_T`, the set of strongly normalizing terms of type `T`.
* A **tested stack** at `T` (`TestedStack`) is a list of arguments, each in `Top` of the successive domain of `T`.
* `Ground T` is OpenAI's `G_T`, the set of terms of type `T` whose applications to every tested stack are strongly normalizing. The proof shows `Ground T = Top T` for every actual type, one component at a time.
* A **candidate** at `T` (`IsCandidate`) is a set between `Ground T` and `Top T` that is closed under head expansion.
* The **generic** context is the context `Γ` of a typing judgment before its variables are substituted. An **environment** sends it into the tower by a typed substitution with **raw** images, which need not be normal, together with **parameters** for some declarations.
* The **three cases** for a component are the **signed** case (no closed path of odd parity), the **one-child** case (no profile triple inside the component) and the **observation** case (both), which needs relational exclusion.

### Observation values, used in the third case

* A **base observation** (`Base`) chooses a candidate at every actual type.
* A **frame** at a product type `Π x:D. E` is a normal argument `q` of type `D` whose instantiated codomain `E[x := q]` is active, together with a **payload**. The payload is a parameter for `q` when `D` is active, and is absent otherwise. The type `E[x := q]` is the **target** of the frame.
* A payload has a **tag**, which records whether it is absent, a value of the opposite sign, or a plain value.
* A frame **continues** when its target is free and **exits** when its target is plain. A **gate** (`Gate`) checks that an argument and a payload form a frame and decides whether it exits.
* A **table** assigns a base observation to every finite list of continuing frames and an **exit observation** to every list that ends with an exiting frame. **Slicing** a table fixes its first frame.
* Values at free types of sign `+` (`Plus`) are arbitrary tables whose payloads are values of sign `−`. Values at free types of sign `−` (`Minus`) are built in **stages** `0, 1, 2, …`, and the set of all of them is the union of the stages (OpenAI's **colimit**). A value of sign `−` must be **representable** at a single finite stage, uniformly in all its inputs.
* `Val` is the value of a typing tree in an environment, and `Read` is the candidate that it selects for a term whose type is a sort. **Goodness** (`ValGood`, `ReadGood`) is an extra condition on a typing tree in an environment. Under it, values and `Read`s are preserved by substitution and reduction, and it holds for normal syntax.
* The adaptation in `PTSBetaEta.Normalization` adds **canonical** values (`canonValue`), which forget the data that no observation reads.

### The logical encoding, used for relational exclusion

* Terms carry **modes**, data or proof, and binders carry the corresponding **labels**.
* A **wrapper** turns a type into another type along a fixed path of the primary graph. **Terminals** are fixed types at the ends of negative edges, and **converters** are declared proof transformations between terminals.
* **Channels**, **probes**, **bundles** and **queries** are further terms of this encoding. Their comments refer to the notation of the preprint.
-/
