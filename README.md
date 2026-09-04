# A Machine-Checked Proof of Fermat's Little Theorem

This repository contains a formal proof of **Fermat's Little Theorem** in
Rocq (formerly Coq). The development was completed collaboratively by Michael
Jaber, Jeff Champion, and Vinayak Kumar.

For an integer `a` and a prime `q` such that `a` is nonzero modulo `q`, Fermat's
Little Theorem states

```text
a^(q-1) ≡ 1 (mod q).
```

The theorem appears at the end of [`project.v`](project.v) as:

```coq
Theorem Fermat's_Little_Theorem:
    forall (a: Z) (p: nat),
    prime (Z.of_nat (S p)) /\
    a mod (Z.of_nat (S p)) <> 0 ->
    Zpower_nat a p mod (Z.of_nat (S p)) = 1.
```

Here, `Z.of_nat (S p)` is the prime modulus and `p` is one less than that
modulus.

## Proof strategy

The formalization follows the classical permutation proof. If `a` is nonzero
modulo a prime `q`, multiplication by `a` permutes the nonzero residue classes

```text
1, 2, ..., q-1.
```

Consequently, multiplying all of these residues gives the same result before
and after scaling by `a`. Factoring `a^(q-1)` out of the scaled product and
cancelling the nonzero residue product yields

```text
a^(q-1) ≡ 1 (mod q).
```

The development formalizes the supporting machinery needed for this argument,
including:

- arithmetic modulo an integer and compatibility with addition and
  multiplication;
- existence and uniqueness properties for inverses modulo a prime;
- absence of zero divisors modulo a prime;
- finite lists representing the nonzero residue classes;
- membership bounds and duplicate-freeness for those lists;
- injectivity of multiplication by a nonzero residue;
- permutation of the nonzero residues by multiplication;
- invariance of list products under permutation; and
- extraction and cancellation of the power `a^(q-1)` from the product.

## Repository contents

```text
.
├── project.v   # Definitions, supporting lemmas, and the final theorem
└── README.md   # Project overview and build instructions
```

The current development contains approximately 874 lines of Rocq/Coq,
49 proved theorem or lemma statements, and five definitions/fixpoints.

## Requirements

The project was checked using:

```text
The Coq Proof Assistant, version 8.17.1
```

It relies only on modules from the Coq standard library, including integer
arithmetic, number theory, lists, and permutations.

## Building the proof

After installing Coq 8.17.1, clone the repository and run:

```bash
coqc project.v
```

A successful run may produce no terminal output. Coq will generate compiled
artifacts such as `project.vo` after the kernel has checked the development.

To inspect the proof interactively, open `project.v` in an editor configured
with VsCoq Legacy or another extension compatible with Coq 8.17.1.

## Contributors

This formalization was developed by Michael Jaber, Jeff Champion, and Vinayak
Kumar.
