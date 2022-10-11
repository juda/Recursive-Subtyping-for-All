# Recursive Subtyping for All


## Building Instructions



Our Coq proofs are verified in Coq version **Coq 8.13.1**. We rely on the Coq library: [`metalib`](https://github.com/plclub/metalib/releases/tag/coq8.10) for the locally nameless representation in our proofs.

### Prerequisites

1. Install Coq 8.13.1.
   The recommended way to install Coq is via `OPAM`, using `opam pin add coq 8.13.1` command. Please refer to [here](https://coq.inria.fr/opam/www/using.html) for detailed steps.

2. Make sure `Coq` is installed (type `coqc` in the terminal, if you see "command
   not found" this means you have not properly installed Coq), then install `Metalib`:
   1. Download the source code of `Metalib` from `https://github.com/plclub/metalib/releases/tag/coq8.10`.
   2. `cd Metalib`
   3. `make install`

### Build and Compile the Proofs

1. Enter the coq directory you would like to build, for example `cd kernel_fsub_main`

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following (suppose `>` is the prompt):
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC Rules.v
   COQC Infrastructure.v
   ...
   COQC Conservativity.v
   ```
   some warning messages may be printed, but they do not affect the building of the proof.



## Paper to artifact correspondence


### Overview of libraries

The formalization of the paper uses the locally nameless representation [Aydemir, Brian, et al. "Engineering formal metatheory." (2008)] of terms and types. The formalization is built with a third-party library Metalib, which implements the locally nameless representation. 


### Proof Structure

There are three directories in this artifact. Each directory corresponds to a type system discussed in the paper, and can be built independently. In each directory, the dependency of the proofs follows a sequential order. The important lemmas and definitions are documented as follows:

#### `kernel_fsub_main` 

Contains the proofs for the main system presented in Section 3 and Section 4 of the paper.

The paper to proof table:

| Theorem | File | Name in Coq
| ----- | ------- | ------
| Theorem 3.2 Reflexivity | Reflexivity.v | `Reflexivity` |
| Theorem 3.3 Transitivity | Transitivity.v | `sub_transitivity` | 
| Lemma 3.4 Unfolding lemma | Unfolding.v | `unfolding_lemma` |
| Theorem 3.6 Preservation | Preservation.v | `preservation` |
| Theorem 3.7 Progress | Progress.v | `progress` |
| Theorem 3.8 Soundness of algorithmic rules | AlgoTyping.v | `typing_algo_sound` |
| Theorem 3.9 Completeness of algorithmic rules | AlgoTyping.v | `minimum_typing` |
| Lemma 4.5 Generalized unfolding lemma | Unfolding.v | `sub_generalize_intensive` |
| Lemma 4.6 Decidability | Decidability.v | `subtyping_dec` |
| Theorem 4.7 Decidability | Decidability.v | `decidability` |
| Lemma 4.9 Conservativity for Subtyping | Conservativity.v | `sub_conserv` |
| Theorem 4.11 Conservativity | Conservativity.v | `typing_conserv` |


Key definitions in the paper:

| Definition | File | Notation in Paper | Name in Coq
| ----- | ------- | ------ | ------
| Fig. 1. Well-formed Type | Rules.v | $\vdash \Gamma$ | `WF` |
| Fig. 1. Subtyping | Rules.v | $\Gamma \vdash A \le B$ | `sub` |
| Fig. 2. Typing | Rules.v | $\Gamma \vdash e: A $ | `typing` |
| Fig. 2. Reduction | Rules.v | $\Gamma \vdash e_1 \hookrightarrow e_2$ | `step` |
| Fig. 3. Exposure | AlgoTyping.v | $\Gamma \vdash A \Uparrow B$  | `exposure` |
| Fig. 3. Exposure | AlgoTyping.v | $\Gamma \vdash A \Downarrow B$ | `exposure2` |
| Fig. 3. Algorithmic Typing | AlgoTyping.v | $\Gamma_a \vdash e: A $ | `algo_typing` |


#### `kernel_fsub_all`

corresponds to the full system presented in Section 5


The paper to proof table:

| Theorem | File | Name in Coq
| ----- | ------- | ------
| Reflexivity | Reflexivity.v | `Reflexivity` |
| Transitivity | Transitivity.v | `sub_transitivity` | 
| Unfolding lemma | Unfolding.v | `unfolding_lemma` |
| Preservation | Preservation.v | `preservation` |
| Progress | Progress.v | `progress` |
| Soundness of algorithmic rules | AlgoTyping.v | `typing_algo_sound` |
| Completeness of algorithmic rules | AlgoTyping.v | `minimum_typing` |
| Decidability | Decidability.v | `decidability` |
| Conservativity for Subtyping | Conservativity.v | `sub_conserv` |
| Conservativity | Conservativity.v | `typing_conserv` |

Coq Definitions are loacted in a similar way to to `kernel_fsub_main`.


#### `kernel_fsub_minimal` 

We have also developed a minimal calculus extending plain kernel Fsub with iso-recursive subtyping but no records. In that system we employ the traditional kernel rule for subtyping universal types. This calculus has all the same properties that other systems have: reflexivity, transitivity and decidability of subtyping; type-soundness; and conservativity. Moreover, we prove that subtyping is anti-symmetric, which is helpful to simplify the proof of the unfolding lemma.

The paper to proof table:

| Theorem | File | Name in Coq
| ----- | ------- | ------
| Reflexivity | Reflexivity.v | `Reflexivity` |
| Transitivity | Transitivity.v | `sub_transitivity` | 
| Unfolding lemma | Unfolding.v | `unfolding_lemma` |
| Preservation | Preservation.v | `preservation` |
| Progress | Progress.v | `progress` |
| Soundness of algorithmic rules | AlgoTyping.v | `typing_algo_sound` |
| Completeness of algorithmic rules | AlgoTyping.v | `minimum_typing` |
| Decidability | Decidability.v | `decidability` |
| Conservativity for Subtyping | Conservativity.v | `sub_conserv` |
| Conservativity | Conservativity.v | `typing_conserv` |

Coq Definitions are loacted in a similar way to `kernel_fsub_main`.