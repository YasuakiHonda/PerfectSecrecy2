# PerfectSecrecy2

This repository contains a Lean4 formalization of **perfect secrecy** for symmetric-key encryption, based on **Shannon’s information-theoretic definition** and its modern equivalents.

The development is carried out using **probability mass functions (PMFs)** and **game-based formulations**, with the goal of making classical results about perfect secrecy precise, modular, and machine-checked.

---

## Background

In his seminal 1949 paper *“Communication Theory of Secrecy Systems”*, Claude Shannon introduced the notion of **perfect secrecy**, formalizing the idea that a ciphertext reveals no information about the plaintext.  
Shannon showed that perfect secrecy is equivalent to several probabilistic conditions, and derived fundamental limitations such as the **key size lower bound**.

This repository formalizes these ideas in Lean4, focusing on:

- Shannon-style definitions using probability distributions
- Modern indistinguishability-based formulations
- Equivalence theorems between different definitions
- Consequences such as key-size bounds and insecurity under key reuse
- The One-Time Pad (OTP) as a canonical example

It is worth noting that, in the scope of this development, **uniform key distributions are not assumed in general**.
Except for the One-Time Pad example, all results are proved for **arbitrary key distributions**.
In particular, the equivalence theorems, key-size lower bound, and key-reuse impossibility results
do not rely on the key being uniformly distributed.

---

## Design Principles

- **Information-theoretic setting**: No computational assumptions.
- **Finite probability spaces**: Message, key, and ciphertext spaces are modeled as finite types.
- **PMF-based formalization**: Perfect secrecy is expressed using probability mass functions rather than general probability measures.
  This allows Shannon-style definitions to be stated as *pointwise equalities* of probabilities, avoiding “almost everywhere”
  reasoning that would obscure the cryptographic meaning of perfect secrecy.
- **No uniformity assumption on keys**: Except for the OTP example, results are stated for arbitrary key distributions.
- **Modular structure**: Definitions, equivalences, and applications are clearly separated.

Namespaces and sections are used to make logical dependencies explicit and local.

---

## Repository Structure
```text
.
├── lake-manifest.json
├── lakefile.toml
├── lean-toolchain
├── PerfectSecrecy2
│   ├── Defs.lean
│   ├── Equivalences
│   │   ├── IndPS_Eq_IndPriorPS.lean
│   │   └── IndPS_Eq_ShannonPS.lean
│   ├── KeyReuse.lean
│   ├── KeySize.lean
│   └── OTP.lean
├── PerfectSecrecy2.lean
└── README.md

```

---

### `Defs.lean`

Core definitions of perfect secrecy:

- Encryption-induced ciphertext distributions
- Shannon-style perfect secrecy
- Indistinguishability-based perfect secrecy
- Prior-based formulations

This file provides the foundational definitions used throughout the repository.

---

### `Equivalences/`

Formal proofs of equivalence between different definitions of perfect secrecy.

- `IndPS_Eq_IndPriorPS.lean`  
  Equivalence between indistinguishability-based and prior-based definitions.

- `IndPS_Eq_ShannonPS.lean`  
  Equivalence between indistinguishability-based perfect secrecy and Shannon’s original definition.

These results justify treating the different formulations interchangeably.

---

### `KeySize.lean`

Formalization of Shannon’s **key size lower bound**:

- Proof that perfect secrecy implies `|K| ≥ |M|`
- Finite-type and PMF-based formulation

This captures the classical impossibility result underlying perfectly secret encryption schemes.

---

### `KeyReuse.lean`

General results about **key reuse**:

- Formal proof that reusing a key breaks perfect secrecy
- Abstract treatment independent of any specific encryption scheme

This file isolates the core argument behind the insecurity of key reuse.

---

### `OTP.lean`

The One-Time Pad as a concrete instantiation:

- Definition of OTP encryption
- Proof that OTP satisfies perfect secrecy under a **uniform key distribution**
- Application of the general key-reuse result to show that OTP fails under key reuse

Uniformity of the key is assumed **only** for the proof of perfect secrecy of OTP, and is not required elsewhere in the repository.

---

## Relation to Cryptographic Formalizations

While this development is information-theoretic in nature, it is structured to resemble modern cryptographic libraries:

- Game-based reasoning
- Explicit probability distributions
- Clear separation between definitions and consequences

This makes it suitable as a foundation for future extensions toward computational security notions.

---

## Status

- Core definitions: complete
- Equivalence theorems: complete
- Key-size lower bound: complete
- OTP example: complete

The repository is intended as a clean, minimal, and extensible reference formalization of perfect secrecy in Lean4.

---

## References

- C. E. Shannon, *Communication Theory of Secrecy Systems*, Bell System Technical Journal, 1949.
