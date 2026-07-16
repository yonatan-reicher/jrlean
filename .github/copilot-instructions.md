# Copilot instructions for `jrlean`

This repository is a **Lean playground** for trying ideas. Structure and semantics change frequently; treat this file as orientation, not a fixed contract.

## Build, test, and lint commands

Lean/Lake setup:
- Toolchain: `leanprover/lean4:v4.30.0` (`lean-toolchain`)
- Project config: `lakefile.toml`
- Default target: `Jrlean` (`lakefile.toml`)

Commands:
- **Full build:** `lake build`
- **Build one module:** `lake build Jrlean.Coc`
- **Single-file check (also runs in-file `#guard`/`#guard_msgs` checks in that file):** `lake env lean Jrlean/Effect.lean`

There are no dedicated test or lint targets configured right now.

## High-level architecture

- **`Jrlean.lean`** is the umbrella module. It re-exports current modules via `public import ...`.
- **Foundation utilities (`Of`, `Relation`, `Coe`, `FiniteType`, `CollectionLemmas`, tactics/macros):** small reusable helpers used across experiments.
- **Type identity and effects stack:** `TypeId` + `HasTypeId` (+ derive handler) + `TypeWithId` underpin `Effect.lean`, which defines an `effect` command, effect descriptors, and the indexed `Effects` monad.
- **Typed C-like experiment:** `Jrlean/C.lean` re-exports active AST/checking modules in `Jrlean/C/{Typ,Expr,Stmt,Check}.lean`; historical evaluator/state code remains as commented sketches in `Jrlean/C.lean`.
- **Calculus of Constructions experiment:** `Jrlean/Coc.lean` re-exports `Jrlean/Coc/*` (variable representation, syntax/notation macros, substitution/binder movement, beta/logical layers).
- **Dependent monad experiments:** `DReader.lean`, `DependentState.lean`, and `DMonad.lean` explore indexed/dependent Reader/State/IMonad formulations.

## Key repository conventions

- Keep file/module headers in Lean style (`module` at top, definitions under `namespace Jrlean` or sub-namespace like `Jrlean.C`).
- Use `public`/`public section` for intended library surface, and expose grouped APIs through re-export modules (`Jrlean.lean`, `Jrlean/C.lean`, `Jrlean/Coc.lean`, `Jrlean/HasTypeId.lean`).
- `@[expose]` is used deliberately on core defs intended for reuse from other modules; preserve this pattern when extending existing APIs.
- Many proofs and rewrites are wired for `grind`/`simp` (`@[grind]`, `@[grind =]`, `@[simp]`); keep new lemmas aligned with this attribute-driven style so automation continues to work.
- Embedded checks are commonly written as `#guard`, `#guard_msgs`, and `#eval` (not a separate test framework), so targeted verification is typically done by checking the specific Lean file.
- The repository intentionally includes exploratory/partially implemented code (including `sorry` and commented prototypes); prefer focused, module-local changes and incremental verification.
