---
name: docs
description: Strict guidelines for writing module headers, doc comments, inline comments, section separators, and CLI diagnostic formatting in CoreX.
---

# Docs

When working in the `corex` repository, any AI agent or subagent MUST adhere strictly to the following documentation, comment, and separator standards, in accordance with `AGENTS.md` Sections 5, 6, and 7.

---

## 1. Module Headers & Doc Comments

### Module Headers

Start every source file – except pure re-export barrel files – with a 3-part header comment block:

1.  **Title Line:** A **Title Case** title on the first line (or `Title – Concise Summary` capitalized after the en dash).
2.  **Summary Paragraph:** A blank comment line followed by a concise 1–2 sentence description of the module's responsibility in the compiler or standard library pipeline.
3.  **Architectural Invariants (Optional):** A blank comment line followed by key representation invariants, arena ownership rules, or phase ordering requirements.

### Exported & Internal Declarations

1.  **Mandatory Coverage:** Follow `AGENTS.md` Section 7. Every exported and internal type, struct, enum, constant, and function requires a doc comment.
2.  **Single-Line First & Column 150 Wrapping (CRITICAL):**
    -   Write every doc comment (without multi-tag parameter blocks) and code comment on **one line** whenever the full line stays below column 150 (`< 150` characters).
    -   For complex public functions with parameter/return/error documentation, list parameters in the exact signature order and align descriptions 3 spaces after the longest parameter name.
    -   When any doc comment or comment line reaches column 150 (`>= 150` characters), break into multiple lines: place each sentence on its own line first, and if a single sentence still reaches column 150, split logically at `;`, `,`, or a clause boundary so every line remains `< 150` characters.
3.  **Units in Docs, Not Names:** Document measurement units in the doc comment rather than the identifier name (e.g., `/// Timeout before killing hung child process (ms).`).
4.  **Self-Contained Comments (No Hardcoded Drift):** Never enumerate volatile union variants, full token lists, diagnostic code counts, or consumer lists inside comments; describe contracts in general terms or reference canonical table identifiers in backticks.
5.  **Contiguous Attribute/Constant Blocks:** When documenting a sequence of struct fields, enum variants, or grouped constants inside a section, keep each doc comment and its declaration contiguous without blank lines between adjacent entries; use 65-character internal section separators when grouping distinct sub-clusters.

---

## 2. Code Comments

1.  **Inline Code Backticks (CRITICAL):** Always wrap identifiers, parameters, types, AST node kinds, CLI flags, file paths, and expressions in backticks `` ` `` inside comments (never quotes).
2.  **Standalone Comments (Own Line):**
    -   Comments written on their own line to describe the upcoming block of code must end with a colon `:` on the final line (e.g., `// Validate token span and advance cursor:`).
    -   Keep standalone comments to 1 line whenever `< 150` characters (maximum 2 lines when wrapping is required). Preceding lines may end with `.` or `;`; replace mid-sentence prose colons with `;` (preserving colons inside backticks).
    -   **Exceptions:** Comments inside empty `{}` blocks (end with `.`) and scoped compiler/linter pragmas.
3.  **End-of-Line Comments:** Comments placed on the same line after code must end with a period `.` (e.g., `return fallback_id; // Use sentinel ID on recovery.`), unless a 1–2 word label (`// Fast path`).
4.  **Numbered Step Comments (CRITICAL):** When documenting sequential steps inside a function or pass, always format step numbers with square brackets like `[1]`, `[2]`, `[3]` (e.g., `// [1] Intern identifier bytes:`, `// [2] Emit HIR binding:`), never `1.`, `2.`.
5.  **Prose & Typography:** Follow `AGENTS.md` Section 7 for ellipsis (`…`), en dash (`–`), `e.g.,`, and the ban on em dashes (`—`) and colored emojis.

---

## 3. Section Separators

Use section separators to organize modules into clear logical regions (`TYPES`, `CONSTS`, `INTERNALS`, `PUBLIC API`, `MAIN`) and to separate test groups.

-   **Widths:**
    -   **Top-Level Separators:** Exactly **90 characters** wide – used for major file-level sections.
    -   **Internal Separators:** Exactly **65 characters** wide – used for sub-sections inside a struct, module block, or test suite (leading indentation is not counted toward the 65-character width).
-   **Formatting & Centering:**
    -   Use block-style `/********************************* Title *********************************/` or line-style `// -------------------------------------- TITLE -------------------------------------` consistently per file language convention.
    -   Pad the title with a single space on each side before the `*` or `-` fill characters.
    -   **Parity Rule:** Center the text within the fill characters. When the total number of fill characters is odd, the **left** side receives **one fewer** fill character than the right side (`len(left) == len(right) - 1`).

**Example (Top-Level, 90 characters, even fill):**

```c
/********************************* Variable Definitions *********************************/
```

**Example (Top-Level, 90 characters, odd fill – left has one fewer `-`):**

```c
// -------------------------------------- PUBLIC API -------------------------------------
```

**Example (Internal, 65 characters, odd fill – left has one fewer `*`):**

```c
/************************* Edge Cases ***************************/
```

---

## 4. CLI & Diagnostic Rendering Standards

In accordance with `AGENTS.md` Section 5, all terminal rendering and compiler diagnostic formatting must follow this structural pattern using monochrome Unicode glyphs (`╭`, `│`, `╰`, `├`, `─`, `▸`, `•`, `✓`, `✗`, `⚠`) and ANSI styling:

```text
✗ error[E0302]: use of moved value `buffer` after scope transfer
  ╭─▸ src/net/socket.cx:42:18
  │
40 │     let packet = consume_payload(buffer)
   │                                  ────── value moved here
41 │     log_status("dispatched")
42 │     return read_header(buffer)
   │                        ^^^^^^ value used here after transfer
  │
  ╰─▸ help: pass a borrowed view via `buffer.as_slice()` if `consume_payload` does not retain ownership
```
