# TLA++: Higher-Level TLA+ for BFT Protocols Model Checking

**Author:** Inés Araujo Cañas  
**Institution:** École Polytechnique Fédérale de Lausanne (EPFL)  
**Supervisor:** Dr. Gauthier Voron  
**Date:** June 2, 2025

---

## Overview

TLA++ is a syntax extension and compiler for TLA+ designed to simplify the formal specification and model checking of Byzantine fault-tolerant (BFT) distributed protocols. This project introduces new domain-specific constructs for expressing common Byzantine behaviors—such as adversarial voting and divergent leader actions—making specifications more concise, readable, and maintainable without sacrificing verification rigor.

## Motivation

Modeling Byzantine faults in TLA+ is notoriously complex and error-prone, requiring manual duplication of transitions, intricate fairness conditions, and explicit adversarial reasoning. TLA++ addresses these challenges by introducing high-level abstractions that automate the expansion of these patterns, reducing manual effort and the risk of specification errors.

## Key Features

- **Byzantine Comparison Operator:**  
  Abstracts threshold logic for vote counting in quorum protocols, automatically accounting for worst-case Byzantine interference.

- **MODE 1 / MODE 2 Syntax:**  
  Enables modular specification of mutually exclusive behaviors (e.g., honest vs. faulty leader), inspired by the Phase King algorithm.

- **Python-based Compiler:**  
  Transforms TLA++ specifications into standard TLA+ code via an abstract syntax tree (AST) representation, handling fairness, existential quantification, and transition duplication.

- **Syntactic Sugar for Non-Determinism:**  
  Includes constructs for non-deterministic assignments and randomized value selection.

## Getting Started

### Prerequisites

- Python 3.x
- TLA+ Toolbox or Visual Studio Code with TLA+ extension ([see official resources](https://lamport.azurewebsites.net/tla/tla.html)[6])
- Basic familiarity with TLA+ syntax and model checking

### Installation

1. **Clone the Repository:**
   ```bash
   git clone 
   cd 
   ```

2. **Usage:**  
   - Write your specification AST using TLA++ syntax (see `ast/examples`).
   - Use the provided compiler functions to convert TLA++ ASTs into standard TLA+ code
     ```python
      ast().compile()
     ```
   - Save the generated TLA++ code into a `.tla` file, and opem it in the TLA+ Toolbox or VS Code and run the TLC model checker.

## Example

A TLA++ vote-counting expression:
```tla
number_of_honest_votes(v) >= BYZANTINE Quorum
```
is automatically expanded by the compiler into:
```tla
\E x \in 0..MaxByzantineNodes:
    number_of_honest_votes(v) >= Quorum - x
```

## Project Structure

- `ast/`  
  Compiler source code and AST node definitions.
- `README.md`  
  This file.
- `report/`  
  Master project report, including background, design, implementation, evaluation, and future work.

## Evaluation

TLA++ specifications are shown to be 16–41% more concise than their compiled TLA+ equivalents, with formal arguments ensuring preservation of safety and liveness properties. Side-by-side examples and complexity metrics are included in the report.

## Acknowledgements

This project was completed at EPFL under the supervision of Dr. Gauthier Voron. The thesis template used is available at [https://github.com/HexHive/thesis_template]. Special thanks to the EPFL community, family, and friends for their support.

## References

- [TLA+ Official Site](https://lamport.azurewebsites.net/tla/tla.html)
- [TLA+ Toolbox IDE](https://lamport.azurewebsites.net/tla/toolbox.html)