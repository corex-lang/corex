---
name: docs
description: Strict guidelines for writing module headers, doc comments, inline comments, section separators, and CLI diagnostic formatting in CoreX.
---

# Docs

When working in the `corex` repository, any AI agent or subagent MUST adhere strictly to the following documentation, comment, and separator standards, in accordance with `AGENTS.md` Sections 5, 6, and 7.

---

## 1. Module Headers & Doc Comments

### Module Headers

Start every source file (`/#` in `.cx`, `//!` in Stage 0 `.zig`) – except pure re-export barrel files – with a 3-part header docstring block:

1.  **Title Line:** A **Title Case** title on the first line (or `Title – Concise Summary` capitalized after the en dash).
2.  **Summary Paragraph:** A blank `/#` line (`//!` in `.zig`) followed by a concise 1–2 sentence description of the module's responsibility in the compiler or standard library pipeline.
3.  **Architectural Invariants (Optional):** A blank `/#` line (`//!` in `.zig`) followed by key representation invariants, arena/ownership rules, or phase ordering requirements.

```cx
/# Lock-Free DMA Heap Slab and Descriptor Primitives
/#
/# Packs 64-bit aligned ring descriptors without runtime heap allocation.
/#
/# All slab headers enforce `@repr(C, align: 8, zero_pad: true)` for `IntoBytes` wire safety.
```

### Exported & Internal Declarations

1.  **Mandatory Coverage:** Follow `AGENTS.md` Section 7. Every exported and internal type, struct, enum, union, `bit_field`, trait, field, variant, constant, and function requires a concise **`/|`** outer docstring in `.cx` (`///` in Stage 0 `.zig`). Retired `///`, `//!`, and `/* … */` block comments are rejected in `.cx` with `E0118`.
2.  **Single-Line First & Column 150 Wrapping (CRITICAL):**
    -   Write every docstring and code comment on **one line** whenever the full line stays below column 150 (`< 150` characters).
    -   Do **not** bloat `.cx` docstrings with repetitive `@param` / `@returns` type lists when parameter types, defaults, `/` & `*` zones, and public SemVer contracts (`@no_alloc`, `@no_panic`, `@max_stack`) are already self-documenting in the `.cx` signature (`corex doc` extracts full signatures directly from the AST); document non-obvious semantic preconditions, error conditions, or complexity/ownership invariants instead.
    -   When any docstring or comment line reaches column 150 (`>= 150` characters), break into multiple lines: place each sentence on its own line first, and if a single sentence still reaches column 150, split logically at `;`, `,`, or a clause boundary so every line remains `< 150` characters.
3.  **Units in Docs, Not Names:** Prefer documenting measurement units in the docstring when the type (`Duration`, `ByteSize`) already conveys dimension, or note units explicitly (`/| Timeout before killing hung child process (ms).`).
4.  **Self-Contained Comments (No Hardcoded Drift):** Never enumerate volatile union variants, full token lists, diagnostic code counts, or consumer lists inside comments; describe contracts in general terms or reference canonical table identifiers in backticks.
5.  **Contiguous Attribute/Constant Blocks:** Keep each `/|` docstring, horizontal `@attribute` line (`<= 100` cols per `DR-24` `ADR-24C`), and declaration contiguous without blank lines between adjacent entries; use 65-character internal section separators when grouping distinct sub-clusters.

---

## 2. Code Comments

1.  **Line-Only `//` Comments (`0` Block Comments):** CoreX `.cx` files use **`//`** as the sole code comment (`/* … */` block comments and hard `\t` tab indentation are forbidden via `E0118` and `E0116`; spaceless `///|` and `///#` scan as commented-out docstrings).
2.  **Inline Code Backticks (CRITICAL):** Always wrap identifiers, parameters, types, AST node kinds, CLI flags, file paths, and expressions in backticks `` ` `` inside comments (never quotes).
3.  **Standalone Comments (Own Line):**
    -   Comments written on their own line to describe the upcoming block of code must end with a colon `:` on the final line (e.g., `// Validate token span and advance cursor:`).
    -   Keep standalone comments to 1 line whenever `< 150` characters (maximum 2 lines when wrapping is required). Preceding lines may end with `.` or `;`; replace mid-sentence prose colons with `;` (preserving colons inside backticks).
    -   **Exceptions:** Comments inside empty `{}` blocks (end with `.`) and `// corex fmt: off` / `on` or `// corex check:` directives.
4.  **End-of-Line Comments:** Comments placed on the same line after code must end with a period `.` (e.g., `return fallback_id; // Use sentinel ID on recovery.`), unless a 1–2 word label (`// Fast path`).
5.  **Numbered Step Comments (CRITICAL):** When documenting sequential steps inside a function or pass, always format step numbers with square brackets like `[1]`, `[2]`, `[3]` (e.g., `// [1] Intern identifier bytes:`, `// [2] Emit HIR binding:`), never `1.`, `2.`.
6.  **Prose & Typography:** Follow `AGENTS.md` Section 7 for ellipsis (`…`), en dash (`–`), `e.g.,`, and the ban on em dashes (`—`) and colored emojis.

---

## 3. Section Separators

Use ASCII line-comment section separators to organize `.cx` and Stage 0 `.zig` modules into clear logical regions (`TYPES`, `CONSTS`, `INTERNALS`, `PUBLIC API`, `MAIN`, and optional `TESTS`) and to group sub-clusters.

-   **Widths (Both UTF-8 Bytes and Unicode Codepoints):**
    -   **Top-Level Separators:** Exactly **90 ASCII characters** wide – used for major file-level sections (`indent == 0`).
    -   **Internal Separators:** Exactly **65 ASCII characters** wide – used for sub-sections inside a top-level section, struct, `impl` block, or test suite (leading indentation is not counted toward the 65-character width).
-   **Formatting & Centering:**
    -   Format as `// ---… TITLE …---` with a single space on each side of the ASCII title before the `-` fill characters.
    -   **Parity Rule:** Center the title within the `-` fill characters. When the total number of `-` characters is odd, the **left** side receives **one fewer** `-` than the right side (`len(left) == len(right) - 1`).

**Example (Top-Level, 90 characters, even fill – 40 left, 40 right):**

```cx
// ---------------------------------------- TYPES ----------------------------------------
```

**Example (Top-Level, 90 characters, odd fill – 37 left, 38 right):**

```cx
// ------------------------------------- PUBLIC API --------------------------------------
```

**Example (Internal, 65 characters, odd fill – 24 left, 25 right):**

```cx
// ------------------------ Error Paths -------------------------
```

---

## 4. CLI & Diagnostic Rendering Standards

In accordance with `AGENTS.md` Section 5, all terminal rendering and compiler diagnostic formatting must follow this structural pattern using monochrome Unicode glyphs (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠`) and ANSI styling:

```text
✗ error[E0302]: use of moved value `buffer` after ownership transfer
   ╭─▸ src/net/socket.cx:42:24
   │
40 │     let packet = consume_payload(own buffer);
   │                                  ────────── value moved here
41 │     log_status("dispatched");
42 │     return read_header(buffer);
   │                        ^^^^^^ value used here after move
   │
   ├╴ help: pass a borrowed slice via `buffer.as_slice()` if `consume_payload` does not retain ownership
   ╰───────
```
