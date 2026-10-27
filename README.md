# Weak and strong βη-normalization in pure type systems with βη-conversion

A Lean 4 / Mathlib formalization of the **Barendregt–Geuvers–Klop conjecture**, "weak normalization implies strong normalization", for the pure type systems `PTS_βη` of Geuvers, whose conversion rule uses βη-conversion.
Geuvers states the conjecture for all pure type systems (*Logics and Type Systems*, 1993, Conjecture 8.1.2).

## Main results

Let `P` be any PTS specification, given by a type of sorts, an axiom relation and a rule relation.
No functionality, finiteness or decidability is assumed.

A term is legal when, in some valid context of the system `PTS_βη` for `P`, it has a type or is a type.

**Theorem.**

1. If every legal term is weakly βη-normalizing, then every legal term is strongly βη-normalizing.
   (`PureTypeSystem.weak_implies_strong_betaEta`)
2. If every legal term is weakly β-normalizing, then every legal term is strongly βη-normalizing.
   (`PureTypeSystem.weak_beta_implies_strong_betaEta`)

Both parts follow from an intermediate result.

**Intermediate theorem.** If every legal term has a β-reduct with no β-redex outside its λ-domains, then every legal term is strongly β-normalizing.
(`PureTypeSystem.strong_beta_of_eNormalizing_BE`)

Weak βη-normalization gives such a β-reduct.
The proof postpones the η-steps of a normalizing sequence after its β-steps and then works on erased terms.
Weak β-normalization gives one directly, since a β-normal form has no β-redex at all.
Strong β-normalization then implies strong βη-normalization, again by postponing η-steps.

We prove neither the result for the system `PTS^s_βη`, which adds a strengthening rule, nor Geuvers's Conjecture 8.1.3, which says that strong normalization of `PTS_β` implies strong normalization of `PTS_βη`.

## Visual guide

We provide a visual guide ([`guide/proof-map.pdf`](guide/proof-map.pdf)) to OpenAI's proof of the β case and to the βη case proved here.
The guide presents both proofs as one recursion over the strongly connected components of a finite signed graph on sets of sorts, illustrates each construction on a small example, and names the Lean files and declarations behind each figure.
We believe that a visual guide is more useful initially while auditing a large proof over pages of theorems that need weeks or months of concentrated effort. 
The LaTeX source files can be found in [`guide/proof-map.tex`](guide/proof-map.tex).

## Statement of record

[`Challenge.lean`](Challenge.lean) imports only Mathlib and defines everything
it uses:

- annotated pseudo-terms with de Bruijn indices, renaming and substitution
- β- and η-reduction, closed under every term former, including λ-domains and
  product domains
- βη-conversion
- the seven typing rules of `PTS_βη`, valid contexts and legal terms
- weak and strong normalization, where strong normalization is accessibility of the converse of one-step reduction

[`Solution.lean`](Solution.lean) proves the two theorems from the library, and
[`comparator.json`](comparator.json) tells Comparator which declarations to
compare.

## Relation to OpenAI's proof of the β case

- **OpenAI's result.** Weak β-normalization implies strong β-normalization for every `PTS_β`, where the conversion rule uses β-conversion. It is proved in the preprint "Weak and strong normalization in pure type systems" (September 25, 2026) and formalized in Lean at <https://github.com/openai/math>.
- **Why it does not cover `PTS_βη`.** `PTS_βη` may have more legal terms.
- **What this proof does.** It follows OpenAI's argument and changes the parts that depend on β-conversion typing.

The main changes:

- **Weak normalization.** An η-step can delete a λ-annotation, so weak βη-normalization only gives, for each legal term, a β-reduct with no β-redex outside its λ-domains. This property is enough for each step of the argument.
- **Conversion** is handled through domain erasure, under which βη-reduction is confluent.
- **Candidates** are indexed by βη-normal forms of erased types.
- **Observation values**, in the third case of the candidate construction, are made η-canonical, so that βη-convertible terms receive equal values.

## Layout

| Path | Content |
| --- | --- |
| `Challenge.lean` | statement of record (Mathlib only) |
| `Solution.lean` | proofs of the two compared theorems |
| `CheckAxioms.lean` | prints the axioms of the main theorems |
| `PTSBetaEta/Beta/` | OpenAI's formalization of the β case, 33 files (copied, Apache-2.0) |
| `PTSBetaEta/Eta/` | η-reduction, η-postponement, domain erasure and confluence, typing with βη-conversion and its metatheory, strengthening for `PTS_β`, the paradox half for βη |
| `PTSBetaEta/Normalization/` | OpenAI's candidate models adapted to βη-conversion typing: keys, context tower, the three component interpretations, η-canonical observation values |
| `PTSBetaEta/Main.lean` | finite restriction, the case split, and the main theorems |
| `guide/` | visual guide to the proof, as PDF and LaTeX source |

About 48,000 lines of Lean, of which about 30,000 are OpenAI's files.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan). The toolchain is
`leanprover/lean4:v4.35.0`, and Mathlib is pinned to its `v4.35.0` tag.

```sh
lake exe cache get      # download Mathlib build artifacts
lake build              # builds the library, Challenge, Solution, CheckAxioms
```

`lake build` reports:

- the two deliberate `sorry`s of `Challenge.lean`
- the axioms of the main theorems, which are `propext`, `Classical.choice` and
  `Quot.sound`

The proof development contains no `sorry` and no custom axiom.

On Linux with `bwrap` installed, `lake comparator --config comparator.json` compares `Challenge.lean` with `Solution.lean` and replays the proof through the Lean kernel.
Palomar runs the same check, and also the NanoDa and con-ron kernels that come with the toolchain.

## Licence and provenance

Apache License 2.0, see [`LICENSE`](LICENSE).

| Files | Origin |
| --- | --- |
| `PTSBetaEta/Beta/` | modified copies of OpenAI's files from <https://github.com/openai/math>, directory `lean/OAI/Computability/TypeSystem/`, commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The changes: ported to the Lean module system, the outer namespace `OAI` removed, module names changed to `PTSBetaEta.Beta.*`, and the comments reworded. |
| 16 files in `PTSBetaEta/Normalization/` | adapted from OpenAI's files of the same name, from the same directory and commit. The changes: adapted to typing with βη-conversion, and ported to the Lean module system. Each of these files says so in its first line. |

## Authorship and use of AI

- The adaptation of the proof to βη and the Lean code outside `PTSBetaEta/Beta/` were produced with Claude Opus 5.5 (Anthropic), used through Claude Code, under the direction of the human authors.
- `formalization.yaml` records authorship, automation and review.
