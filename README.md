# Finite permutations in Agda — associated code

[![Agda CI](https://github.com/DSLsofMath/PermutationLehmer/actions/workflows/agda-ci.yaml/badge.svg)](https://github.com/DSLsofMath/PermutationLehmer/actions/workflows/agda-ci.yaml)

This is the Agda code accompanying the functional pearl

> Patrik Jansson and Wouter Swierstra, *"niFite semPurtatoni"* (Finite permutations in Agda).
> Submitted to the Journal of Functional Programming.
> Pre-print: <https://hal.science/hal-05746158>

## Abstract
*Finite permutations* have numerous applications in both mathematics and computing, from the classification of finite groups to sorting algorithms. This pearl studies a first-order representation of finite permutations in the dependently typed programming language Agda. This representation is *precise*, encoding exactly the bijective functions between finite sets; yet it supports a direct definition of composition, inversion, and identity. This pearl constructs these operations, proves their correctness, and presents a decision procedure that computes this first-order representation of permutations from any pair of vectors, if it exists.

## Files

- `Permutation.lagda`
  - the whole development in one self-contained literate Agda file, kept in sync with the private working copy that actually feeds the paper's build (LaTeX + lhs2tex + a small custom snippet extractor).
  - The `<<name>>` markers are that extractor's snippet tags: most of the paper's inline code listings are pulled verbatim from the tagged region right below them, so a fragment from the paper can be found here by its tag name.
  - Comments sometimes use |lhs2tex inline pipes|.
  - Agda ignores everything outside `\begin{code}`/`\end{code}`.
  - A handful of paragraphs have been left out of this synced copy; the code itself is unedited.
- `permutation.agda-lib` — library file, so the module type-checks out of the box once `agda-stdlib` is registered (see below).

## Contents of `Permutation.lagda`

The file is organised as one sequence of top-level sections, some further split into `module`s:

| Section / module | Contents |
| --- | --- |
| Prelude and utils | Shared notation, e.g. pointwise function equality `_≐_` |
| `PermutationFexample`, `PermutationVexample` | The two naive representations (`Fin n → Fin n` and `Vec (Fin n) n`) that motivate the first-order `Permutation` type |
| `Permutations` | The core development: `Permutation`, `skip`, `pinch`, semantics `⟦_⟧`, identity `idₚ`, composition `_⊙_`, inverses, injectivity |
| — `Conjugation` | Conjugation of permutations and its properties |
| — `decide-permute` | The decision procedure recovering a `Permutation` from a pair of vectors, given decidable equality on the element type |
| `Utils` | Vector utilities: the right action `_◁_` of a permutation on a `Vec`, the `Permutes` equivalence relation between vectors, `Find` |
| `CheckLehmerInversionCount` | Equivalence between the inductive Lehmer-code encoding and the classical (Wikipedia) inversion-count definition |
| `TableSizeBound`, `TableCompleteness` | Size bound and completeness of `Table` (the type used to represent injections `Fin n → Fin m` in the decision procedure) |

## Requirements

- [Agda](https://agda.readthedocs.io/) 2.8.0 (should also work with nearby 2.7.x/2.8.x versions).
- [agda-stdlib](https://github.com/agda/agda-stdlib) 2.3.

## Type-checking

Register `agda-stdlib` 2.3 with Agda's library manager (see the [stdlib installation instructions](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md)) so that `standard-library-2.3` is available, then run
```sh
agda Permutation.lagda
```
from this directory. (No `lhs2TeX` needed — Agda's own literate mode handles `.lagda` directly, ignoring everything outside `\begin{code}`/`\end{code}`.)

`permutation.agda-lib` should pick up the `standard-library-2.3` dependency automatically.

This is also checked automatically on every push, see `.github/workflows/agda-ci.yaml` and the badge above.

## Citation

The paper is submitted to the Journal of Functional Programming (2026-09); the citation below will be updated when/if there is a reviewed/published version. In the meantime, cite the HAL pre-print:

```bibtex
@misc{JanssonSwierstra2026Permutations,
  author       = {Patrik Jansson and Wouter Swierstra},
  title        = {niFite semPurtatoni (Finite permutations in Agda)},
  year         = {2026},
  note         = {In submission to the Journal of Functional Programming (JFP)},
  howpublished = {Pre-print: \url{https://hal.science/hal-05746158}},
}
```

## License

MIT, see [LICENSE](LICENSE).
