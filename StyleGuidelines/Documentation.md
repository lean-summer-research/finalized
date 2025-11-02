# Lean/Mathlib Style Guidelines

This document contains comprehensive style guidelines for writing Lean 4 code and contributing to Mathlib.

**Sources:**
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Mathlib naming conventions: <https://leanprover-community.github.io/contribute/naming.html>
* Library Style Guidelines: <https://leanprover-community.github.io/contribute/style.html>

---

## Table of Contents

1. [Quick Reference](#quick-reference)
2. [Naming Conventions](#naming-conventions)
   - [Variable Naming](#variable-naming-conventions)
   - [Case Conventions](#case-conventions)
   - [Naming Dictionary](#naming-dictionary)
   - [Theorem Naming](#theorem-naming)
3. [Documentation Standards](#documentation-standards)
   - [Module Docstrings](#module-docstrings)
   - [Declaration Docstrings](#declaration-docstrings)
   - [Comments](#comments)
   - [File Structure](#file-structure)
4. [Code Formatting](#code-formatting)
   - [Line Length](#line-length)
   - [Hypotheses Placement](#hypotheses-placement)
   - [Tactics](#tactics)
   - [Whitespace and Operators](#whitespace-and-operators)
5. [Best Practices](#best-practices)
   - [Normal Forms](#normal-forms)
   - [Simp Lemmas](#simp-lemmas)
   - [Iff Theorems](#iff-theorems)

---

## Quick Reference

| Aspect | Rule | Example |
|--------|------|---------|
| **Line length** | Max 100 characters | |
| **Theorem names** | `snake_case` | `add_comm`, `le_of_lt` |
| **Type names** | `UpperCamelCase` | `REquiv`, `IsClosed` |
| **Function names** | `lowerCamelCase` | `padicNorm`, `realPart` |
| **Variables (numbers)** | `m`, `n`, `k` | `(n : ℕ)` |
| **Variables (generic)** | `x`, `y`, `z` | `(x y : α)` |
| **Sets/lists** | `s`, `t` | `(s : Set α)` |
| **Predicates** | `p`, `q`, `r` | `(p : α → Prop)` |
| **Idempotent elements** | `e` | `(e : S)` (where `e * e = e`) |
| **Module docs** | `/-! ... -/` | File headers, sections |
| **Declaration docs** | `/-- ... -/` | Above definitions |
| **Comments** | `/- ... -/` or `--` | TODOs, proofs |
| **Hypotheses** | Left of colon preferred | `(h : 1 < n)` not `∀ h, ...` |
| **Tactic separator** | Newlines preferred | One tactic per line |
| **Simp calls** | Don't squeeze terminal ones | Keep `simp [h]` over `simp only [...]` |

---

## Naming Conventions

### Variable Naming Conventions

Use consistent variable names throughout your code:

- `x`, `y`, `z`, `u`, `v`, `w` ... for elements of a generic type (including elements of Semigroups and Monoids!)
- `e` ... for idempotent elements
- `s`, `t` ... for sets and lists
- `p`, `q`, `r` ... for predicates and relations (excluding Green's relations)
- `m`, `n`, `k` ... for natural numbers
- `i`, `j`, `k` ... for integers
- `a`, `b`, `c` ... for propositions
- `S`, `T` ... for semigroups
- `M` ... for monoids
- `G` ... for groups
- `α`, `β`, `γ` ... for generic types
- `u`, `v`, `w` ... for universes
- `h`, `h₁`, ... for assumptions

### Case Conventions

#### `snake_case` (for Propositions)

Use `snake_case` for terms of type `Prop` (e.g., proofs, theorem names).

**Examples:** `add_comm`, `mul_assoc`, `lt_of_succ_le`, `le_of_lt`

#### `UpperCamelCase` (for Types)

Use `UpperCamelCase` for:
1. File names
2. `Prop`s and `Type`s (e.g., inductive types, structures, and classes)

**Examples:** `REquiv`, `RLE`, `REquiv.isEquiv`, `IsClosed`, `Continuous`

#### `lowerCamelCase` (for Terms)

Use `lowerCamelCase` for all other terms of `Type`s (basically anything else).

**Examples:** `REquiv.set`, `padicNorm`, `realPart`

#### Special Cases

**Functions** are named the same way as their return values. For example, a function of type `A → B → C` is named as though it is a term of type `C`.

**Acronyms** like `LE` are written upper or lowercase as a group, depending on what the first character would be. An exception is `Ne` and `Eq`.

**Types in theorem names:** When appearing in the names of theorems, `UpperCamelCase` types get `lowerCamelCase`d.
- Example: `HEquiv.to_rEquiv`

**Namespaced definitions:** When referring to a namespaced definition in a lemma name not in the same namespace, the definition should have its namespace removed. If the definition name is unambiguous without its namespace, it can be used as is. Otherwise, the namespace is prepended back to it in `lowerCamelCase`. This ensures that `_`-separated strings in a lemma name correspond to a definition name or connective.

> **Note:** Within VS Code, hovering over any declaration such as `def Foo ...` will show the fully qualified name, like `MyNamespace.Foo` if `Foo` is declared while the namespace `MyNamespace` is open.

---

### Naming Dictionary

#### Logic Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| ∨ | `\or` | `or` | |
| ∧ | `\and` | `and` | |
| → | `\r` | `of` / `imp` | The conclusion is stated first and the hypotheses are often omitted |
| ↔ | `\iff` | `iff` | Sometimes omitted along with the right hand side of the iff |
| ¬ | `\n` | `not` | |
| ∃ | `\ex` | `exists` | |
| ∀ | `\fo` | `all` / `forall` | |
| = | | `eq` | Often omitted |
| ≠ | `\ne` | `ne` | |
| ∘ | `\o` | `comp` | |

#### Algebra Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| 0 | | `zero` | |
| + | | `add` | |
| - | | `neg` / `sub` | `neg` for unary function, `sub` for binary function |
| 1 | | `one` | |
| * | | `mul` | |
| ^ | | `pow` | |
| / | | `div` | |
| • | `\bu` | `smul` | |
| ⁻¹ | `\-1` | `inv` | |
| ⅟ | `\frac1` | `invOf` | |
| ∣ | `\|` | `dvd` | |
| ∑ | `\sum` | `sum` | |
| ∏ | `\prod` | `prod` | |

#### Set Operations

| Symbol | Shortcut | Name | Notes |
|--------|----------|------|-------|
| ∈ | `\in` | `mem` | |
| ∉ | `\notin` | `notMem` | |
| ∪ | `\cup` | `union` | |
| ∩ | `\cap` | `inter` | |
| ⋃ | `\bigcup` | `iUnion` / `biUnion` | i for "indexed", bi for "bounded indexed" |
| ⋂ | `\bigcap` | `iInter` / `biInter` | i for "indexed", bi for "bounded indexed" |
| \ | `\\` | `sdiff` | |
| ᶜ | `\^c` | `compl` | |
| {x \| p x} | | `setOf` | |
| {x} | | `singleton` | |
| {x, y} | | `pair` | |

#### Order Relations (Lattice)

| Symbol | Shortcut | Name |
|--------|----------|------|
| < | | `lt` / `gt` |
| ≤ | `\le` | `le` / `ge` |

##### Special Rules for `≤` and `<`

In Mathlib, we almost always use `≤` and `<` instead of `≥` and `>`, so we can use both `le`/`lt` and `ge`/`gt` for naming `≤` and `<`. There are a few reasons to use `ge`/`gt`:

1. **Different argument order:** We use `ge`/`gt` if the arguments to `≤` or `<` appear in different orders. We use `le`/`lt` for the first occurrence of `≤`/`<` in the theorem name, and then `ge`/`gt` indicates that the arguments are swapped.

   ```lean
   theorem lt_iff_le_not_ge [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a
   theorem not_le_of_gt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a
   theorem LT.lt.not_ge [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a
   ```

2. **Match argument order of another relation:** We use `ge`/`gt` to match the argument order of another relation, such as `=` or `≠`.

   ```lean
   theorem Eq.ge [Preorder α] {a b : α} (h : a = b) : b ≤ a
   theorem ne_of_gt [Preorder α] {a b : α} (h : b < a) : a ≠ b
   ```

3. **Describe swapped relation:** We use `ge`/`gt` to describe the `≤` or `<` relation with its arguments swapped.

   ```lean
   theorem ge_trans [Preorder α] {a b : α} : b ≤ a → c ≤ b → c ≤ a
   ```

4. **More variable second argument:** We use `ge`/`gt` if the second argument to `≤` or `<` is 'more variable'.

   ```lean
   theorem le_of_forall_gt [LinearOrder α] {a b : α} (H : ∀ (c : α), a < c → b < c) : b ≤ a
   ```

---

### Theorem Naming

#### Descriptive Naming

Definitions and theorem names should describe their conclusion. Use the naming dictionaries above for standard operations in that conclusion.

**Infix operations:** When an operation is written as infix, the theorem names follow suit. For example, we write `neg_mul_neg` rather than `mul_neg_neg` to describe the pattern `-a * -b`.

#### Referring to Hypotheses with `of`

Sometimes, to disambiguate the name of a theorem or better convey the intended reference, it is necessary to describe some of the hypotheses. The word `of` is used to separate these hypotheses.

**Examples:**
- `lt_of_succ_le`
- `lt_of_not_ge`
- `lt_of_le_of_ne`
- `add_lt_add_of_lt_of_le`

**Important:** The hypotheses are listed in the order they appear, not reverse order. For example, the theorem `A → B → C` would be named `C_of_A_of_B`.

#### Axiomatic Naming

Some theorems are better described using axiomatic names. Common "axiomatic" properties of an operation like introduction and elimination are put in a namespace that begins with the name of the operation. In particular, this includes `intro` and `elim` operations for logical connectives, and properties of relations.

**Examples:**
- `And.comm`, `And.intro`, `And.elim`
- `Or.comm`, `Or.intro_left`, `Or.intro_right`
- `Or.resolve_left`, `Or.resolve_right`
- `Eq.trans`, `HEq.trans`
- `Iff.refl`

**Common axiomatic descriptions:**
- `def` (for unfolding a definition)
- `assoc`
- `refl`
- `symm`
- `trans`
- `irrefl`
- `antisymm`
- `asymm`
- `congr`
- `comm`
- `left_comm`
- `right_comm`
- `mul_left_cancel`
- `mul_right_cancel`
- `inj` (injective)

#### Extensionality

- A lemma of the form `(∀ x, f x = g x) → f = g` should be named `.ext`, and labelled with the `@[ext]` attribute.
- A lemma of the form `f = g ↔ ∀ x, f x = g x` should be named `.ext_iff`.

#### Injectivity

Where possible, injectivity lemmas should be written in terms of an `Function.Injective f` conclusion which uses the full word injective, typically as `f_injective`.

In addition to these, a variant should usually be provided as a bidirectional implication, e.g., as `f x = f y ↔ x = y`, which can be obtained from `Function.Injective.eq_iff`. Such lemmas should be named `f_inj` (although if they are in an appropriate namespace `.inj` is good too). Bidirectional injectivity lemmas are often good candidates for `@[simp]`.

An injectivity lemma that uses "left" or "right" should refer to the argument that "changes". For example, a lemma with the statement `a - b = a - c ↔ b = c` could be called `sub_right_inj`.

#### Predicates as Prefixes

Most predicates should be added as prefixes. For example, `IsClosed (Icc a b)` should be called `isClosed_Icc`, not `Icc_isClosed`.

**Exception:** Some widely used predicates don't follow this rule. Those are the predicates that are analogous to an atom already suffixed by the naming convention. Here is a non-exhaustive list:

- We use `_inj` for `f a = f b ↔ a = b`, so we also use `_injective` for `Injective f`, `_surjective` for `Surjective f`, `_bijective` for `Bijective f`...
- We use `_mono` for `a ≤ b → f a ≤ f b` and `_anti` for `a ≤ b → f b ≤ f a`, so we also use `_monotone` for `Monotone f`, `_antitone` for `Antitone f`, `_strictMono` for `StrictMono f`, `_strictAnti` for `StrictAnti f`, etc...

---

## Documentation Standards

### Comments

Use different comment styles for different purposes:

- **Module docs** (`/-! ... -/`): Section headers and separators (incorporated into auto-generated docs)
- **Technical comments** (`/- ... -/`): TODOs, implementation notes, comments in proofs
- **Short comments** (`--`): Short or in-line comments

### Declaration Docstrings

Documentation strings for declarations are delimited with `/-- ... -/`. 

**Rules:**
- Place the docstring directly above the declaration
- When a documentation string spans multiple lines, do not indent subsequent lines
- Every definition and major theorem is required to have a doc string
- Doc strings on lemmas are encouraged, particularly if the lemma has any mathematical content or might be useful in another file
- Use newlines or single spaces between the markers (`/--`, `-/`) and the text
- If a doc string is a complete sentence, it should end in a period
- Named theorems (like the **mean value theorem**) should be bold faced (i.e., with two asterisks before and after)

**Purpose:** Doc strings should convey the mathematical meaning of the definition. They are allowed to lie slightly about the actual implementation.

**Example:**

```lean
/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
```

**Example (slightly abstract but mathematically accurate):**

```lean
/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
```

### Module Docstrings

Each Mathlib file should start with a module docstring containing general documentation, written using **Markdown** and **LaTeX**.

**Format:**
- The open and close delimiters `/-!` and `-/` should appear on their own lines
- The mandatory title of the file is a first level header (`#`)
- It is followed by a summary of the content of the file

**Sections (in this order):**
1. **Main definitions** (optional, can be covered in the summary)
2. **Main statements** (optional, can be covered in the summary)
3. **Notations** (omitted only if no notation is introduced in this file)
4. **Implementation notes** (description of important design decisions or interface features, including use of type classes and `simp` canonical form for new definitions)
5. **References** (references to textbooks or papers, or Wikipedia pages)

**Example:**

```lean
/-!
# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

* <https://en.wikipedia.org/wiki/P-adic_number>
-/
```

### File Structure

It is common to structure a file in sections, where each section contains related declarations. By describing the sections with module documentation `/-! ... -/` at the beginning, these sections can be seen in the documentation.

**Important notes:**
- While these sectioning comments will often correspond to `section` or `namespace` commands, this is not required
- You can use sectioning comments inside of a section or namespace
- You can have multiple sections or namespaces following one sectioning comment
- Sectioning comments are for display and readability only. They have no semantic meaning
- Third-level headers `###` should be used for titles inside sectioning comments
- If the comment is more than one line long, the delimiters `/-!` and `-/` should appear on their own lines

**Example:**

```lean
/-!
### Basic properties

This section contains basic lemmas about the norm.
-/

-- Declarations here...

/-!
### Algebraic properties
-/

-- More declarations...
```

### Examples of Good Documentation

The following files are maintained as examples of good documentation style:
- `Mathlib.NumberTheory.Padics.PadicNorm`
- `Mathlib.Topology.Basic`
- `Analysis.Calculus.ContDiff.Basic`

---

## Code Formatting

### Line Length

Lines must not be longer than **100 characters**.

### Hypotheses Placement

Generally, having arguments to the left of the colon is preferred over having arguments in universal quantifiers or implications, if the proof starts by introducing these variables.

**Preferred:**

```lean
example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
```

**Not preferred:**

```lean
example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
```

### Tactics

#### Multiple Tactics on One Line

For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use `by tac1; tac2; tac3` with semicolons instead of a new line with indentation.

**General rule:** You should put a single tactic invocation per line, unless you are closing a goal with a proof that fits entirely on a single line.

**Acceptable exceptions:** Short sequences of tactics that correspond to a single mathematical idea can also be put on a single line, separated by semicolons:
- `cases bla; clear h`
- `induction n; simp`
- `rw [foo]; simp_rw [bar]`

Even in these scenarios, newlines are preferred.

#### `simp` and `rw` Syntax

When using the tactics `rw` or `simp`, there should be a **space after the left arrow** `←`.

**Examples:**
- `rw [← add_comm a b]`
- `simp [← and_or_left]`

There should also be a space between the tactic name and its arguments: `rw [h]`

### Whitespace and Operators

Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code.

#### The `<|` and `|>` Operators

Sometimes parentheses can be avoided by judicious use of the `<|` operator (or its cousin `|>`).

> **Note:** While `$` is a synonym for `<|`, its use in Mathlib is disallowed in favor of `<|` for consistency as well as because of the symmetry with `|>`.

These operators have the effect of:
- **`<|`**: Parenthesizing everything to the right (note that `(` is curved the same direction as `<`)
- **`|>`**: Parenthesizing everything to the left (note that `)` curves the same way as `>`)

**Common usage of `|>`:** Occurs with dot notation when the term preceding the `.` is a function applied to some arguments.

```lean
-- Instead of: ((foo a).bar b).baz
foo a |>.bar b |>.baz
```

**Common usage of `<|`:** Occurs with dot notation when the term preceding the `.` is a function applied to multiple arguments whose last argument is a proof in tactic mode, especially one that spans multiple lines. Use `<| by ...` instead of `(by ...)`.

```lean
example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith
```

---

## Best Practices

### Normal Forms

Some statements are equivalent. For instance, there are several equivalent ways to require that a subset `s` of a type is nonempty. For another example, given `a : α`, the corresponding element of `Option α` can be equivalently written as `Some a` or `(a : Option α)`.

**General principle:** We try to settle on one standard form, called the **normal form**, and use it both in statements and conclusions of theorems.

**Examples of normal forms:**
- `s.Nonempty` (which gives access to dot notation)
- `(a : Option α)` instead of `Some a`

Often, `simp` lemmas will be registered to convert the other equivalent forms to the normal form.

### Simp Lemmas

#### Squeezing `simp` Calls

Unless performance is particularly poor or the proof breaks otherwise, **terminal `simp` calls should not be squeezed** (replaced by the output of `simp?`).

**Definition:** A `simp` call is terminal if it closes the current goal or is only followed by flexible tactics such as `ring`, `field_simp`, or `aesop`.

**Reasons for not squeezing terminal simp calls:**

1. **Readability:** A squeezed `simp` call might be several lines longer than the corresponding unsqueezed one, and therefore drown the useful information of what key lemmas were added to the unsqueezed `simp` call to close the goal in a sea of basic `simp` lemmas.

2. **Maintenance:** A squeezed `simp` call refers to many lemmas by name, meaning that it will break when one such lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.

### Iff Theorems

Iff theorems should be notated such that the **more normalized version of the statement is on the right side** of the iff.

**Benefits:**
- This allows you to use them with `rw` and `simp` without prepending `←`
- This is also the way that `simp` will try to automatically apply the tactic if you tag it `@[simp]`

**Example:**

```lean
-- Preferred (normalized form on the right)
theorem mem_setOf {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a

-- Not preferred
theorem mem_setOf {a : α} {p : α → Prop} : p a ↔ a ∈ {x | p x}
```

---

## Summary

Following these guidelines will help ensure your Lean code is:
- **Readable** and consistent with the rest of Mathlib
- **Maintainable** as the library evolves
- **Discoverable** through intuitive naming
- **Well-documented** for other mathematicians and developers

When in doubt, look at existing Mathlib files in similar areas for guidance, and don't hesitate to ask the community for advice!
