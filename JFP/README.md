

# Recursive Subtyping for All (Extended Version)


## Proof Structure


- `kernel_fsub_main`: The kernel main system presented in Section 3.1 of the paper
- `full_fsub_main`: The full main system presented in Section 3.2 of the paper
- `kernel_fsub_ext`: The extended kernel system presented in Section 5 of the paper

For a detailed paper-to-proof correspondence, please refer to Section 6 of the paper


## Building Instructions


Our Coq proofs are verified in Coq version **Coq 8.13.1**. We rely on the Coq library: [`metalib`](https://github.com/plclub/metalib/releases/tag/coq8.10) for the locally nameless representation in our proofs.

### Prerequisites

1. Install Coq 8.13.1.
   The recommended way to install Coq is via `OPAM`,
   ```
   # create a local switch for this artifact
   opam switch create iso-fsub 4.12.0 
   # update the shell environment
   eval $(opam env)
   # pin the Coq version to 8.13.1 and install
   opam pin add coq 8.13.1
   ```
   Please refer to [here](https://coq.inria.fr/opam/www/using.html) for detailed steps.

2. Make sure `Coq` is installed, then install `Metalib`:
   1. Download the source code `zip` of `Metalib` from `https://github.com/plclub/metalib/releases/tag/coq8.10`.
   2. unzip the source code `metalib-coq8.10` and `cd` into the directory.
   3. `cd Metalib`
   4. `make install`

### Build and Compile the Proofs

1. Enter the coq directory you would like to build, for example `cd kernel_fsub_main`

2. Type `make` in the terminal to build and compile the proofs.

3. You should see something like the following:
   ```sh
   coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
   COQDEP VFILES
   COQC Rules.v
   COQC Infrastructure.v
   ...
   COQC Conservativity.v
   ```
   some warning messages may be printed, but they do not affect the building of the proof.

4. You can remove the compiled proofs by `make clean`

5. To remove Coq 8.13.1 installed in this artifact, you can run `opam switch remove iso-fsub`

