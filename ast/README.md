# TLA+ Abstract Syntax Tree (AST) Representation

This repository contains a Python implementation of an Abstract Syntax Tree (AST) designed to represent the syntax of TLA+ specifications. The AST provides a structured way to parse, analyze, and manipulate TLA+ specifications programmatically.


## Table of Contents
- [TLA+ Abstract Syntax Tree (AST) Representation](#tla-abstract-syntax-tree-ast-representation)
  - [Table of Contents](#table-of-contents)
  - [Overview of the AST](#overview-of-the-ast)
    - [Key Features](#key-features)
  - [How the AST Works](#how-the-ast-works)
    - [1. Specifications](#1-specifications)
      - [`Spec` Class](#spec-class)
        - [Example](#example)
        - [Output Representation](#output-representation)
    - [2. Constants and Variables](#2-constants-and-variables)
      - [`Constants` Class](#constants-class)
        - [Constructor](#constructor)
        - [Example](#example-1)
        - [Output Representation](#output-representation-1)
      - [`Variables` Class](#variables-class)
        - [Constructor](#constructor-1)
        - [Example](#example-2)
        - [Output Representation](#output-representation-2)
    - [3. Definitions](#3-definitions)
      - [`Definition` Class](#definition-class)
      - [Example](#example-3)
    - [4. Temporal Logic Operators](#4-temporal-logic-operators)
      - [`Box` (`[]`)](#box-)
      - [`Diamond` (`<>`)](#diamond-)
      - [`FrameCondition` (`[A]_v`)](#framecondition-a_v)
      - [`WeakFairness` (`WF_v(A)`)](#weakfairness-wf_va)
    - [5. Predicates and Clauses](#5-predicates-and-clauses)
      - [Predicates](#predicates)
      - [Clauses](#clauses)
    - [6. Terms](#6-terms)
      - [Basic Term Types](#basic-term-types)
      - [Arithmetic Operations](#arithmetic-operations)
      - [Record and Mapping Operations](#record-and-mapping-operations)
      - [Set Operations](#set-operations)
    - [7. Byzantine Operations](#7-byzantine-operations)
      - [`ByzantineComparison`](#byzantinecomparison)
      - [Purpose](#purpose)
      - [Constructor](#constructor-2)
      - [Methods](#methods)
        - [`preCompile(spec: Spec)`](#precompilespec-spec)
        - [`compile(spec: Spec) → TLA+ Term`](#compilespec-spec--tla-term)
        - [`byzComparisonToNormal(spec: Spec) → TLA+ Term`](#byzcomparisontonormalspec-spec--tla-term)
        - [`changeAliasTo(old: str, new: str)`](#changealiastoold-str-new-str)
        - [`__check_syntax(spec: Spec)`](#__check_syntaxspec-spec)
    - [`ByzantineLeader`](#byzantineleader)
      - [Purpose](#purpose-1)
        - [Converts this:](#converts-this)
      - [Constructor](#constructor-3)
      - [Methods](#methods-1)
        - [`preCompile(spec: Spec)`](#precompilespec-spec-1)
        - [`compile(spec: Spec) → TLA+ Term`](#compilespec-spec--tla-term-1)
        - [`byzComparisonToNormal(spec: Spec) → ByzantineLeader`](#byzcomparisontonormalspec-spec--byzantineleader)
        - [`changeAliasTo(old: str, new: str)`](#changealiastoold-str-new-str-1)
        - [`__check_syntax(spec: Spec)`](#__check_syntaxspec-spec-1)
    - [8. Syntactic Sugar](#8-syntactic-sugar)
    - [`Havoc`](#havoc)
      - [Purpose](#purpose-2)
        - [Transforms:](#transforms)
      - [Constructor](#constructor-4)
      - [Methods](#methods-2)
        - [`preCompile(spec: Spec)`](#precompilespec-spec-2)
        - [`compile(spec: Spec) → TLA+ Term`](#compilespec-spec--tla-term-2)
        - [`byzComparisonToNormal(spec: Spec) → Havoc`](#byzcomparisontonormalspec-spec--havoc)
        - [`changeAliasTo(old: str, new: str)`](#changealiastoold-str-new-str-2)
    - [`Random`](#random)
      - [Purpose](#purpose-3)
        - [Example:](#example-4)
      - [Constructor](#constructor-5)
      - [Methods](#methods-3)
        - [`preCompile(spec: Spec)`](#precompilespec-spec-3)
        - [`compile(spec: Spec) → TLA+ Term`](#compilespec-spec--tla-term-3)
        - [`byzComparisonToNormal(spec: Spec) → Random`](#byzcomparisontonormalspec-spec--random)
        - [`changeAliasTo(old: str, new: str)`](#changealiastoold-str-new-str-3)
  - [Updates aliases within the wrapped set expression.](#updates-aliases-within-the-wrapped-set-expression)
  - [Getting Started](#getting-started)
    - [Prerequisites](#prerequisites)
    - [Installation](#installation)


## Overview of the AST

The AST implemented in the `src` folder is designed to represent the hierarchical structure of TLA+ specifications. Each node in the AST corresponds to a syntactic construct in TLA+, such as modules, constants, variables, definitions, and expressions.

### Key Features

- **Modularity**: Each TLA+ construct (e.g., `Conjunction`, `Constant`, `Definition`, `Expression`) is represented as a distinct class.
- **Hierarchical Representation**: The AST captures the nested structure of TLA+ specifications, allowing for easy traversal and manipulation.
- **Extensibility**: The implementation is designed to be extensible, making it easy to add support for new TLA+ constructs.


## How the AST Works

The AST is built using a set of Python classes, each representing a specific TLA+ construct. Below is an explanation of the main components of the AST.


![Module Structure](img/general_diagram.png){ width=50% }


### 1. Specifications

#### `Spec` Class

Represents an entire **TLA+ module** as an abstract syntax tree (AST). This class serves as the top-level node in the tree and is responsible for rendering a valid TLA+ specification string.

> ⚠️ **Note**: The validity of the generated TLA+ code depends on the internal consistency and correctness of the tree, especially when using aliases or user-defined names.

##### Example

```python
spec = Spec(
    module="MyModule",
    extends=["Naturals", "Sequences"],
    constants=Constants([Constant("N")]),
    assumptions=None,
    variables=Variables([Variable("x"), Variable("y")]),
    defs=[...]
)

print(repr(spec))
```

##### Output Representation

Calling `repr()` on a `Spec` object returns the full TLA+ module as a formatted string:

```
------------------------ MODULE MyModule ------------------------
EXTENDS Naturals, Sequences
CONSTANTS N

VARIABLE x, y

<definitions here>

=============================================================================
```

### 2. Constants and Variables

The constants and variables of the specification are represented as `Constants` and `Variables` nodes, respectively. These nodes store metadata about the constants and variables declared in the specification.

---

#### `Constants` Class

Represents the `CONSTANTS` declaration in a TLA+ specification.

##### Constructor

```python
Constants(constants: List[Constant])
```

- **constants**: A list of `Constant` objects, each representing a declared constant.

##### Example

```python
from src.ast.constants import Constants
from src.definitions.terms.terms import Constant

c1 = Constant("A")
c2 = Constant("B")
consts = Constants([c1, c2])
print(repr(consts))  # Output: CONSTANTS A, B
```

##### Output Representation

Calling `repr()` on a `Constants` object returns the corresponding TLA+ `CONSTANTS` line as a string:
```
CONSTANTS A, B
```

---

#### `Variables` Class

Represents the `VARIABLES` declaration in a TLA+ specification.

##### Constructor

```python
Variables(variables: List[Variable])
```

- **variables**: A list of `Variable` objects, each representing a declared variable.

##### Example

```python
from src.ast.variables import Variables
from src.definitions.terms.terms import Variable

v1 = Variable("x")
v2 = Variable("y")
vars = Variables([v1, v2])
print(repr(vars))  # Output: VARIABLES x, y
```

##### Output Representation

Calling `repr()` on a `Variables` object returns the corresponding TLA+ `VARIABLES` line as a string:
```
VARIABLES x, y
```

### 3. Definitions

The `Definition` class represents `Name == Expression` constructs in TLA+, optionally with parameters. These definitions correspond to user-defined operators or macros declared in a TLA+ module.

#### `Definition` Class

```python
Definition(
    name: str,
    value: Union[Clause, Predicate],
    arguments: Optional[List[str]] = None
)
```

- **name**: The identifier being defined.
- **value**: The body of the definition, either a `Clause` or a `Predicate`.
- **arguments** *(optional)*: A list of argument names if the definition is parameterized.

#### Example

```python
Definition("MyOp", Predicate("x > 0"), ["x"])
```

Renders as:
```
MyOp(x) == x > 0
```

---

### 4. Temporal Logic Operators

These classes represent temporal constructs in TLA+, which describe how properties evolve across system states. All of them inherit from the `TemporalOperator` base class and implement `__repr__()` to match TLA+ syntax.

#### `Box` (`[]`)

```python
Box(term: Term)
```

Represents the **"always"** operator `[]A`, meaning the formula `A` holds in all states of the system.

```python
Box(Predicate("x > 0"))  # renders: []x > 0
```

#### `Diamond` (`<>`)

```python
Diamond(term: Term)
```

Represents the **"eventually"** operator `<>A`, meaning the formula `A` holds in some state.

```python
Diamond(Predicate("x = 0"))  # renders: <>x = 0
```

#### `FrameCondition` (`[A]_v`)

```python
FrameCondition(action: Term, variables: List[Term])
```

Represents `[A]_v`, which asserts that either the action `A` occurs or the variables `v` remain unchanged between states.

```python
FrameCondition(Predicate("x' = x + 1"), [Term("x")])
# renders: [x' = x + 1]_<<x>>
```

#### `WeakFairness` (`WF_v(A)`)

```python
WeakFairness(action: Term, variables: List[Term])
```

Encodes the weak fairness constraint `WF_v(A)`, meaning the action `A` must eventually occur if it's continuously enabled.

```python
WeakFairness(Predicate("x' = x + 1"), [Term("x")])
# renders: WF_<<x>>(x' = x + 1)
```

Great! Let's start by documenting the **Predicates** and **Clauses** sections clearly and concisely. Here's a markdown section you can add to your `README.md`:

---

### 5. Predicates and Clauses

In this AST implementation, **Predicates** represent boolean-valued expressions that do not involve logical connectives like conjunction or disjunction. **Clauses**, on the other hand, are logical formulas constructed from predicates and other clauses using logical operators.

#### Predicates

Predicates evaluate to `TRUE` or `FALSE`, and are typically the building blocks for logical expressions in TLA+. They support common relational and set operations as well as quantifiers:

| Class | Description |
|-------|-------------|
| `TRUE`, `FALSE` | Boolean constants. |
| `Not` | Logical negation. |
| `UniversalQuantifier` | ∀ quantifier over a set: `∀ x ∈ S: P(x)`. |
| `ExistentialQuantifier` | ∃ quantifier over a set: `∃ x ∈ S: P(x)`. |
| `Equals`, `NotEquals` | Binary predicates for equality and inequality. |
| `LessThan`, `LessThanEquals`, `GreaterThan`, `GreaterThanEquals` | Arithmetic comparison predicates. |
| `In` | Set membership: `x ∈ S`. |
| `SubsetEquals` | Subset equality: `A ⊆ B`. |

Example:
```python
Equals(x, y)        # ((x) = (y))
Not(In(x, S))       # ~(x ∈ S)
UniversalQuantifier([x], S, Predicate(...))
```

---

#### Clauses

Clauses are higher-level logical combinations of predicates or other clauses using connectives:

| Class | Description |
|-------|-------------|
| `Conjunction` | Logical AND: `P ∧ Q ∧ ...`. |
| `Disjunction` | Logical OR: `P ∨ Q ∨ ...`. |
| `Implication` | Logical implication: `P ⇒ Q`. |

Example:
```python
Conjunction([Equals(x, y), In(x, S)])  
# ((x) = (y)) /\ (x ∈ S)

Implication(Predicate(...), Predicate(...))
# P => Q
```

Clauses allow nesting, so you can build arbitrarily complex logical formulas.

### 6. Terms

In TLA+, **Terms** are expressions that represent values, variables, constants, and more complex data structures. Below is a breakdown of the supported term types.

#### Basic Term Types

| Class       | Description |
|-------------|-------------|
| `Scalar`    | Represents a scalar value (a constant in mathematical logic). |
| `Variable`  | Represents a variable, as defined in TLA+ under `VARIABLES`. |
| `Constant`  | Represents a constant, as defined in TLA+ under `CONSTANTS`. |
| `String`    | Represents a string value. |
| `Alias`     | Represents an alias for a definition. |
| `Function`  | A generic class for terms that take one or more terms as arguments and return another term. |
| `Unchanged` | Represents the `UNCHANGED` operator in TLA+. |
| `Choose`    | Represents the `CHOOSE` operator in TLA+. |
| `Enabled`   | Represents the `ENABLED` operator in TLA+. |
| `Range`     | Represents a range of values in TLA+ (e.g., `start..end`). |

Example:
```python
x = Scalar(5)
v = Variable("x")
c = Constant("MAX")
s = String("Hello")
```

---

#### Arithmetic Operations

TLA+ supports arithmetic operations. These operations are implemented as subclasses of `Function`:

| Class       | Description |
|-------------|-------------|
| `Addition`  | Represents the addition operation between two terms. |
| `Substraction` | Represents the subtraction operation between two terms. |
| `Multiplication` | Represents the multiplication operation between two terms. |
| `Division` | Represents the division operation between two terms. |

Example:
```python
term1 = Scalar(3)
term2 = Scalar(4)
result = Addition(term1, term2)  # Represents 3 + 4
```

---

#### Record and Mapping Operations

These terms are used to define and work with records and mappings in TLA+:

| Class       | Description |
|-------------|-------------|
| `Record`    | Represents a record, a collection of named fields with associated types. |
| `RecordInstance` | Represents an instance of a record, with assigned values for each field. |
| `Mapping`   | Represents a function mapping, where a set of input values is mapped to output values. |

Example:
```python
record = Record(fields=["name", "age"], types=[String("John"), Scalar(30)])
record_instance = RecordInstance(fields=["name", "age"], vals=[String("Alice"), Scalar(25)])
mapping = Mapping(vals=[Scalar(1), Scalar(2)], funs=[Scalar(10), Scalar(20)])
```

---

#### Set Operations

TLA+ also supports a variety of operations for manipulating sets:

| Class       | Description |
|-------------|-------------|
| `IndexSet`  | Represents the indexing operation of a set (e.g., `set[index]`). |
| `Subset`    | Represents a subset of a set. |
| `Set`       | Represents a set of elements. |
| `SetOf`     | Creates a set of elements from a subset that satisfies a predicate. |
| `SetFrom`   | Creates a set of elements based on a predicate. |
| `SetExcept` | Creates a set with an entry changed (e.g., `set EXCEPT ![index] = value`). |
| `Cardinality` | Returns the cardinality (number of elements) of a set. |
| `Union`     | Returns the union of two sets. |
| `Intersection` | Returns the intersection of two sets. |

Example:
```python
set1 = Set([Scalar(1), Scalar(2), Scalar(3)])
set2 = Set([Scalar(3), Scalar(4), Scalar(5)])
union_set = Union(set1, set2)  # Represents {1, 2, 3} ∪ {3, 4, 5}
```
---
### 7. Byzantine Operations

#### `ByzantineComparison`

Represents a TLA+ construct that simulates the impact of Byzantine faults in a numeric comparison. Typically used to model threshold-based logic such as voting or quorum systems in fault-tolerant protocols.

#### Purpose

Transforms a standard threshold comparison into an existential quantification that accounts for a configurable number of Byzantine nodes. For example, it converts:

```tla
variable comparison threshold
```

into:

```tla
∃ x ∈ 0..MaxByzantineNodes:
    variable comparison (threshold - x)
```

This models the potential deviation in values caused by up to `MaxByzantineNodes` faulty actors.

#### Constructor

```python
ByzantineComparison(
    variable: NumericTerm,
    comparison: ArithmeticComparison,
    threshold: NumericTerm,
    inNext: bool,
    trace: Trace
)
```

* `variable`: The left-hand side of the comparison, typically a count or measurement.
* `comparison`: A subclass of `ArithmeticComparison` (e.g., `>=`, `<`, etc.).
* `threshold`: The value the variable is compared against.
* `inNext`: Indicates whether this term is in the `Next` clause (for temporal logic purposes).
* `trace`: Call stack trace of definitions leading to the expression, used for splitting `Next`.

#### Methods

##### `preCompile(spec: Spec)`

Prepares the spec for transformation. If the term appears within a `Next` clause, it triggers `precompilationSplitNextFairness`.

---

##### `compile(spec: Spec) → TLA+ Term`

Compiles the high-level term into its TLA+ representation using existential quantification to simulate Byzantine variation.

---

##### `byzComparisonToNormal(spec: Spec) → TLA+ Term`

Returns the original, non-fault-tolerant form of the comparison (i.e., without accounting for Byzantine deviations).

---

##### `changeAliasTo(old: str, new: str)`

Renames any aliases used within `variable` or `threshold`.

---

##### `__check_syntax(spec: Spec)`

Internal method to verify that the inputs are of compatible types and that required constants (like `MaxByzantineNodes`) exist in the spec.

---

### `ByzantineLeader`

Simulates a rotating leader process in a distributed protocol, which may exhibit either honest or Byzantine behavior in each round.

#### Purpose

Transforms dual-leader specifications (honest and Byzantine) into a single guarded expression based on the value of a `king` variable, which may take the special value `"byzantine"`.

##### Converts this:

```tla
HONEST LEADER HonestSpec
BYZANTINE LEADER ByzantineSpec
```

Into this:

```tla
leaderIsByzantine == king ∈ {"byzantine"}

Init == ...
         ∧ king ∈ (OriginalSet ∪ {"byzantine"})

...
∧ leaderIsByzantine => ByzantineSpec
∧ ~leaderIsByzantine => HonestSpec
```

#### Constructor

```python
ByzantineLeader(
    hon_behaviour: Union[Predicate, Clause],
    byz_behaviour: Union[Predicate, Clause]
)
```

* `hon_behaviour`: TLA+ term representing the expected behavior of an honest leader.
* `byz_behaviour`: TLA+ term modeling potential Byzantine misbehavior.

---

#### Methods

##### `preCompile(spec: Spec)`

* Modifies `Init` and any other relevant definitions to extend the domain of `king` to include `"byzantine"`.
* Adds a `leaderIsByzantine` definition to be used as a guard.
* Logs any skipped definitions where the transformation couldn't be applied (e.g., `king` not in a recognizable form).

---

##### `compile(spec: Spec) → TLA+ Term`

Returns a conjunction of implications, routing the behavior according to the current leader’s honesty:

```tla
(~leaderIsByzantine => HonestSpec)
∧ (leaderIsByzantine => ByzantineSpec)
```

---

##### `byzComparisonToNormal(spec: Spec) → ByzantineLeader`

Returns a new `ByzantineLeader` object in which `byzComparisonToNormal` has been applied recursively to both `hon_behaviour` and `byz_behaviour`.

---

##### `changeAliasTo(old: str, new: str)`

Updates aliases inside both the honest and Byzantine behavior specifications.

---

##### `__check_syntax(spec: Spec)`

Validates that:

* `hon_behaviour` and `byz_behaviour` are valid boolean predicates.
* The `king` variable is declared in the spec’s variable list.


---

### 8. Syntactic Sugar

Here's `.md`-style documentation for the `Havoc` and `Random` classes, formatted to match the style used previously.

---

### `Havoc`

Represents non-deterministic assignment of one or more variables to arbitrary values from their associated domains, as defined in the spec’s `TypeOK` clauses.

#### Purpose

Models arbitrary state transitions for selected variables. This is especially useful for modeling uncertainty, testing protocol resilience, or abstract execution steps.

##### Transforms:

```tla
HAVOC x, y, z
```

Into:

```tla
x' ∈ TypeOfX
∧ y' ∈ TypeOfY
∧ z' ∈ TypeOfZ
```

Where `TypeOfX`, etc., are inferred from `TypeOK` declarations in the spec.

---

#### Constructor

```python
Havoc(vars: List[Variable], sets: List[Term], spec: Spec)
```

* `vars`: List of variables to be assigned arbitrary values.
* `sets`: \[**Deprecated in use**] Internally overwritten — actual sets are inferred from the spec.
* `spec`: The TLA+ spec, used to extract `TypeOK` constraints.

> 💡 Raises `ValueError` or `TypeError` if mismatched or undefined variable information is found.

---

#### Methods

##### `preCompile(spec: Spec)`

No-op. Present for interface compatibility.

---

##### `compile(spec: Spec) → TLA+ Term`

Returns a conjunction of statements of the form:

```tla
x' ∈ TypeOK_set
```

If only one variable is affected, returns the statement directly without conjunction.

---

##### `byzComparisonToNormal(spec: Spec) → Havoc`

No-op for `Havoc`, simply returns self.

---

##### `changeAliasTo(old: str, new: str)`

Updates all aliases in the involved sets.

---

### `Random`

Encapsulates the act of choosing a random value from a given set in TLA+, implemented using the `CHOOSE` operator.

#### Purpose

Used to introduce non-determinism or model randomized algorithms. Always selects a single element from a set without any predicate constraint (i.e., always `TRUE`).

##### Example:

```tla
RANDOM {1, 2, 3}
```

Becomes:

```tla
CHOOSE v ∈ {1, 2, 3}: TRUE
```

---

#### Constructor

```python
Random(set: Term)
```

* `set`: The TLA+ set from which to choose a value.

> 💡 Raises `TypeError` if `set` is not a `Term`.

---

#### Methods

##### `preCompile(spec: Spec)`

No-op. Present for interface consistency.

---

##### `compile(spec: Spec) → TLA+ Term`

Compiles into a TLA+ `CHOOSE` construct:

```tla
CHOOSE v ∈ compiled_set: TRUE
```

---

##### `byzComparisonToNormal(spec: Spec) → Random`

No-op for `Random`, returns self.

---

##### `changeAliasTo(old: str, new: str)`

Updates aliases within the wrapped set expression.
---

## Getting Started

### Prerequisites

- Python 3.8 or higher

### Installation

Clone the repository:

```bash
git clone https://github.com/your-username/your-repo-name.git
cd your-repo-name
```
To run the examples:

```bash
python3 examples.py