# Metaprogramming for Software Correctness in Lean 4

Final project exploring how metaprogramming in Lean 4 makes software verification for correctness more practical and maintainable.

## Project Structure

```
.
├── src/                          # Lean 4 source code
│   ├── InsertionSortProof.lean   # Insertion sort with correctness proofs
│   ├── stacks&queues.lean        # Stack/queue with metaprogramming examples
│   └── Palindromes.lean          # Incomplete palindrome file
|__ final_report.pdf              # Complete project report

```

## What to Look At

### Key Files

1. **`src/InsertionSortProof.lean`**
   - Insertion sort implementation on lists
   - Correctness proofs (sortedness + permutation)
   - `MacroVersion` namespace showing macro-based proof refactoring
   - Custom tactic macros: `solve_nil_sorted`, `chain_perms`, `swap_and_cons`

2. **`src/stacks&queues.lean`**
   - Simple stack and queue implementations
   - Tactic macros: `stacks`, `queues`
   - Command macro: `mk_pop_push` (generates theorem declarations)

3. **`final_report.pdf`** - Final writeup

### Running the Code

Requires Lean 4 with mathlib4. Check `lean-toolchain` for version.

```bash
lake build
```

To look at it in an IDE interactively, open any `.lean` file in VS Code with the Lean 4 extension.

## Author

Salamun Nuhin  

