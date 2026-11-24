# CoreX Syntax, Tooling & Ergonomics Wishlist

Canonical dogfooding backlog for **CoreX** (`.cx`) surface syntax proposals, ergonomic refinements, docstring/hover enhancements, and standard library API improvements discovered while authoring real `.cx` code across `core/`, `stdlib/cx/`, and `compiler/`.

---

## 1. Governance & Single-Writer Protocol

1.  **Strictly Propose-Only (Zero Autonomous Syntax Drift):**
    -   Agents and subagents must **never** implement any syntax addition, keyword/operator change, grammar tweak, or public `cx.*` design change from this file without explicit user approval (and a corresponding `DR-XX` specification + `corex upgrade` rule where applicable).
2.  **Single-Writer Subagent Flow (Zero Merge Collisions):**
    -   Parallel subagents must **not** edit this file directly during slice execution. Instead, every subagent includes a `Dogfooding & Escalations` section in its report to the Lead Agent.
    -   The **Lead Agent** deduplicates sightings, verifies exact `file:line` call-site counts across the repository, increments existing entries when a pattern recurs, and presents a concise digest to the user at the end of each phase (culminating in the **Pre-`Phase 12` Syntax Review Checkpoint** after `Phase 11.3`).
3.  **Mandatory Evidence Schema Per Entry:**
    -   **Category:** `New Syntax` | `Syntax Refinement` | `Docstring & IDE UX` | `Stdlib Ergonomics`
    -   **Problem & Friction:** Concrete readability, boilerplate, or UX pain hit in real `.cx` code.
    -   **Candidate CoreX Design(s):** Concise before/after `.cx` snippets (including novel first-principles options alongside any cross-language precedent).
    -   **Compiler & Tooling Impact:** `TokenKind` delta (`121 / 128` budget), `LL(k)` / Pratt ambiguity analysis, `corex fmt` / `corex check` / `corex upgrade` / `corex lsp` / `vscode-ext-corex` impact.
    -   **Real Call-Site Evidence:** Exact count and representative `file:line` locations in `core/`, `stdlib/cx/`, or `compiler/`.

---

## 2. Open Wishlist Proposals

### `SW-001` – Structured `/|` Parameter & Field Docstring Syntax with Hover Formatting, Auto-Sorting & Lint Validation

-   **Category:** `Docstring & IDE UX` (User-Requested Priority)
-   **Problem & Friction:**
    -   Currently (`docs` skill §1), `/|` docstrings use free-form prose and deliberately ban `@param` type lists so parameter types are not duplicated. However, multi-parameter functions, `@constructor` items, and `struct` declarations still need a clean, canonical way to attach a short 1-line explanation to each parameter without repeating its type, default value, or `/` & `*` zone (which already appear in the signature block of the `corex lsp` hover tooltip).
    -   Free-form prose parameter explanations drift out of order when parameters are reordered or renamed, and render as unaligned paragraphs in IDE hover tooltips.
-   **Candidate CoreX Design(s):**
    -   Introduce a lightweight, type-free parameter doc marker inside `/|` blocks (exact sigil/syntax to be chosen via first-principles design – e.g., `/| - param_name: description`, `/| @param param_name: description`, or `/| [param_name] description`):

        ```cx
        /| Copies up to `count` elements from `src` into `dst`, returning bytes written.
        /|
        /| - dst: Destination buffer receiving copied elements.
        /| - src: Source slice read from index `0`.
        /| - count: Maximum number of elements to transfer.
        pub fn copy_bounded[T: Copy](dst: &mut [T], src: &[T], count: usize) -> usize { … }
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (parsed strictly inside `TriviaKind.doc_comment` `/|` lines).
    -   **`corex lsp` & `vscode-ext-corex`:** Renders a clean two-column or bulleted **Parameters** section inside hover tooltips (`param_name` + prose description only – zero redundant types), provides autocomplete for undocumented parameter names inside `/|`, highlights parameter tokens distinctly in `/|` comments, and updates documented parameter names automatically during `F2` rename.
    -   **`corex fmt`:** Automatically sorts parameter doc entries inside `/|` to match the exact parameter declaration order in the signature.
    -   **`corex check` (`W0xxx`):** Emits a warning (with Jaro–Winkler typo suggestion) if a `/|` parameter entry names a non-existent parameter or duplicates an entry.
-   **Real Call-Site Evidence:**
    -   Immediately applicable across `250+` multi-parameter `pub fn` and method items in `core/*.cx` and `stdlib/cx/{mem,col,str,math}.cx` (e.g., `stdlib/cx/mem.cx`, `stdlib/cx/col.cx`, `stdlib/cx/str.cx`, `stdlib/cx/math.cx`), and across all upcoming `Phase 11.2a`–`11.3` stdlib APIs.

### `SW-002` – Structured `/|` Return Value & `T!E` Error-Variant Docstring Syntax with Hover & Error-Set Validation

-   **Category:** `Docstring & IDE UX` (User-Requested Priority)
-   **Problem & Friction:**
    -   Companion to `SW-001`: functions returning non-trivial values or `T!E` error unions (`AllocError`, `IoError`, `ParseIntError`, etc.) currently describe return semantics and error conditions in unstructured prose inside `/|`, which neither renders as structured **Returns** / **Errors** sections in `corex lsp` hover cards nor checks whether the documented error variants actually match `E`.
-   **Candidate CoreX Design(s):**
    -   Pair `SW-001` with dedicated, type-free return and per-error-variant `/|` markers (exact syntax to be evaluated alongside `SW-001` so parameters, returns, and errors form one cohesive `/|` micro-grammar):

        ```cx
        /| Parses a base-`radix` signed integer from `input`.
        /|
        /| - input: UTF-8 byte slice without leading whitespace.
        /| - radix: Numeric base in `2..=36`.
        /| -> Parsed integer value in target type `T`.
        /| ! Empty: `input` has length `0`.
        /| ! InvalidDigit: Encountered a byte outside `0..radix`.
        /| ! Overflow: Value exceeds `T.MIN..=T.MAX`.
        pub fn parse_int_radix[T: Signed](input: str, radix: u32) -> T!ParseIntError { … }
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (parsed inside `/|` doc comments).
    -   **`corex lsp` & `vscode-ext-corex`:** Renders structured **Returns** and **Errors** sections in hover tooltips (without repeating `T` or `ParseIntError`), autocompletes `E`'s enum variants inside `/|`, and updates variant names on `F2` rename.
    -   **`corex fmt`:** Canonically orders `/|` sections (`Summary` → `Parameters` → `Returns` → `Errors`) and sorts error entries to match `enum E`'s variant declaration order.
    -   **`corex check` (`W0xxx`):** Warns if a `/|` error marker is attached to a non-fallible function or names a variant absent from `E`.
-   **Real Call-Site Evidence:**
    -   Immediately applicable across `80+` fallible `T!E` / `T?` functions in `stdlib/cx/{mem,col,str,math}.cx` and critical for `Phase 11.2a`–`11.2b` (`IoError`, `FsError`, `NetError`, `TlsError`, `HttpError`).

### `SW-003` – Multi-Target `impl` Blocks Over Closed `|` Type Unions (`impl Trait for T1 | T2 | …`)

-   **Category:** `New Syntax` (User-Proposed)
-   **Problem & Friction:**
    -   Implementing a trait or inherent helper identically across several concrete primitive or sibling types currently forces copy-pasting the entire `impl` block `N` times (the exact boilerplate problem Rust works around with `macro_rules!`, which CoreX intentionally omits).
    -   In `stdlib/cx/mod.cx:346-440`, `impl Hash` is repeated across `12` separate blocks (`95` lines) where `7` integer types (`u16`, `u32`, `u128`, `i8`, `i16`, `i32`, `i128`) have byte-for-byte identical `@to_le_bytes(self.*)` bodies; `Phase 11.3` (`cx.serde` `Serialize` / `Deserialize`) will face the same `12–16x` primitive repetition.
-   **Candidate CoreX Design(s):**
    -   Allow a closed **`|`-separated type list** (or closed primitive `type` group alias, rather than `[u8, u16]` which already denotes slice types `[T]`) as the target of an `impl` block, desugaring statically to one concrete `impl` per listed type and type-checking the body with `Self` bound to each member type:

        ```cx
        // Before (55+ lines across 7 identical blocks in stdlib/cx/mod.cx:354-432):
        impl Hash for u16 { … }
        impl Hash for u32 { … }
        impl Hash for u128 { … }
        // …

        // After (8 lines, zero macros, zero runtime cost):
        impl Hash for u16 | u32 | u128 | i8 | i16 | i32 | i128 {
            /| Writes `self` in Little-Endian byte order into `state`.
            @no_alloc @no_panic
            pub fn hash[H: Hasher](&self, state: &mut H, /) {
                state.write(&@to_le_bytes(self.*));
            }
        }
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (reuses `TokenKind.pipe` `|`, matching `type G = A | B;` and `[T: A | B]` inline union bounds).
    -   **Grammar & Coherence Soundness:** `100%` unambiguous (`|` is not valid inside a single concrete `Type` outside `[]` bounds, whereas `[u8, …]` collides with slices and `(u8, …)` collides with tuples). Because the union is a closed finite list of concrete types, Pass-1 / Sema simply expands and coherence-checks each concrete `(Trait, Type_k)` pair individually – avoiding open-ended blanket-`impl` solver conflicts while preserving zero-cost monomorphization.
    -   **`corex lsp`:** Hover, go-to-definition, and find-references map all `K` expanded symbols cleanly back to the shared `impl` method span.
-   **Real Call-Site Evidence:**
    -   `stdlib/cx/mod.cx:346-440` (`12` scalar `impl Hash` blocks collapsible into `2–3` blocks, saving ~70 LOC),
    -   `stdlib/cx/str.cx:3661-3744` (`Display` / `Debug` / `Hash` forwarding shared across `String | CowStr`),
    -   Upcoming `Phase 11.3` `stdlib/cx/serde.cx` (`Serialize` & `Deserialize` across `14` primitive scalar types, saving `25+` repeated `impl` blocks).

---

## 3. Decided & Rejected Ledger

| ID | Proposal Summary | Decision | Rationale / Canonical Reference |
| :--- | :--- | :--- | :--- |
| – | *(None yet)* | – | – |
