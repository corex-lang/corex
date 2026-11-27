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
4.  **Proactive `Deep research` (`DR-XX`) Triage:**
    -   Whenever a wishlist item, tooling surface, or newly encountered subsystem involves non-trivial grammar, diagnostics, IDE, or ecosystem trade-offs where first-principles synthesis would produce a demonstrably superior implementation, the **Lead Agent** must proactively classify it as **`Dedicated DR Recommended`** and prepare a self-contained `Deep research` prompt before implementation rather than designing ad hoc.

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
    -   Immediately applicable across `380+` multi-parameter `pub fn` and method items in `core/*.cx`, `stdlib/cx/{mem,col,str,math}.cx`, and `stdlib/cx/{io,path,fs,time,env,process}.cx` (`+129` new multi-parameter `pub fn` items in `Phase 11.2a` alone: `io.cx` `40`, `path.cx` `29`, `fs.cx` `24`, `time.cx` `20`, `process.cx` `14`, `env.cx` `2`), plus upcoming `Phase 11.2b`–`11.3` stdlib APIs.

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
    -   Immediately applicable across `185+` fallible `T!E` / `T?` functions in `stdlib/cx/{mem,col,str,math,io,path,fs,time,env,process}.cx` (`+105` fallible `pub fn` items added in `Phase 11.2a`: `io.cx` `39`, `fs.cx` `36`, `process.cx` `11`, `time.cx` `7`, `path.cx` `6`, `env.cx` `6`), and critical for `Phase 11.2b` (`NetError`, `TlsError`, `HttpError`).

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

### `SW-005` – Civil Calendar, Timezone & Zero-Allocation Date/Time Formatting in `cx.time`

-   **Category:** `Stdlib Ergonomics` (User-Requested)
-   **Problem & Friction:**
    -   `STD-02` (`Phase 11.2a` `stdlib/cx/time.cx`) specifies monotonic `Instant`, `Duration`, and raw UTC epoch `SystemTime` required to self-host `compiler/*.cx`, but does not yet include civil calendar types (`Date`, `Time`, `DateTime`, `UtcOffset`) or human-readable ISO-8601 / RFC 3339 / pattern formatting and parsing (`Display`, `f"{dt}"`).
-   **Candidate CoreX Design(s):**
    -   Extend `cx.time` (either alongside `Phase 11.2a` if compact and `libc`-free, or in an early `0.x` `cx.time` wave) with Hinnant civil-from-days `Date` / `Time` / `DateTime` / `UtcOffset` value types (`Copy`, zero heap allocation), RFC 3339 / ISO-8601 `parse` & `Display` formatting, and `FmtSpec` integration (`f"{now:%Y-%m-%d %H:%M:%S}"` or canonical specifiers).
-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (pure `stdlib/cx/time.cx` types and traits; unused calendar helpers tree-shake to `0` bytes).
-   **Real Call-Site Evidence:**
    -   Directly usable in `corex lsp` trace/log timestamps, `corex test` / `corex bench` run reports, `pkg_cache` / `corex publish` metadata, and everyday application logging.

### `SW-006` – Statement-Terminated Braced Control Flow (`if` / `match` / `loop`) Before Next-Line `(expr)`

-   **Category:** `Syntax Refinement`
-   **Problem & Friction:**
    -   When a statement-position `if cond { @panic(…); }` or `match` block (without `else`, returning `unit`) is followed on the next line by a parenthesized tail expression such as `(raw_word & 0xFFFF_u32) as u16` or `(ActiveStrOps {}).is_valid_utf8_fast(bytes)`, Pratt postfix continuation treats `(` on the next line as a call on the preceding `if` expression (`if cond { … }(expr)`), requiring an explicit `;` after `}` or unwrapping the outer parentheses.
-   **Candidate CoreX Design(s):**
    -   Following Rust's statement-block rule, terminate braced control-flow expressions (`if`, `match`, `for`, `while`, `loop`, `{ … }`) at `}` in statement position when their type is `unit` (or when separated by a line break before `(` / `[`), rather than parsing next-line `(…)` as a postfix call on the block:

        ```cx
        // Before (requires `;` after `}` or dropping outer parens on tail):
        if idx >= buf.len() {
            panic("out of bounds");
        };
        (buf[idx] as u32 & 0x7F_u32) as u16

        // After (braced statement terminates cleanly at `}`):
        if idx >= buf.len() {
            panic("out of bounds");
        }
        (buf[idx] as u32 & 0x7F_u32) as u16
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (`Parser.parseStmt` / Pratt postfix loop lookahead check on braced statements).
    -   **`corex fmt` & `corex check` (`W0209`):** Eliminates postfix-call hazards when `W0209` (`needless-trailing-return`) strips `return ` before parenthesized tail expressions `(a & b) as u16`.
-   **Real Call-Site Evidence:**
    -   Hit across `stdlib/cx/str.cx:735, 916, 1119, 1301, 4603`, `stdlib/cx/math.cx` bit-extraction tails, and `docs/COMPARISONS.md:259-263` (`12+` sites).

### `SW-007` – Safe Borrow-Propagating `match` Ergonomics on `&Enum` & `@repr(C)` Tagged Unions

-   **Category:** `Syntax Refinement`
-   **Problem & Friction:**
    -   Matching on a shared or mutable reference to a non-`Copy` enum (`self: &CowStr` where `CowStr` holds `Owned(String)`) currently lacks safe `&payload` / `&mut payload` variant projection across `@repr(C)` tagged enums, forcing manual `unsafe` pointer-offset helpers (`CowStr.as_owned_ref(&self) -> *String` in `stdlib/cx/str.cx:3054-3062`) to borrow the inner `String` without moving it.
-   **Candidate CoreX Design(s):**
    -   Support explicit `&binding` / `&mut binding` pattern bindings (or Rust-RFC-2005-style borrow propagation when matching `&Enum` / `&mut Enum`), projecting a lifetime-checked `&T` / `&mut T` directly to the variant payload across both native and `@repr(C)` tagged enums:

        ```cx
        // Before (requires unsafe pointer offset helper in stdlib/cx/str.cx:3054-3062 & 3728-3732):
        match self.* {
            .Borrowed(slice) => .Borrowed(slice),
            .Owned(_) => .Owned(unsafe { self.as_owned_ref().*.clone() }),
        }

        // After (100% safe MVS borrow projection):
        match self {
            .Borrowed(slice) => .Borrowed(slice.*),
            .Owned(&owned_str) => .Owned(owned_str.clone()),
        }
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (uses existing `&` / `&mut` in `Pattern` + `MIR` variant-field `.place_addr` projection).
    -   **`MIR` SAST:** Propagates the scrutinee's loan provenance directly onto `&owned_str` (`Pass 2` NLL + `Pass 3` region escape).
-   **Real Call-Site Evidence:**
    -   `stdlib/cx/str.cx:3054-3062, 3728-3732` (`CowStr`), plus upcoming `Phase 11.2a`–`11.3` recursive/owned ADTs (`cx.io`, `cx.serde.JsonValue`, `cx.serde.TomlValue`, and `compiler/*.cx` AST/HIR enums).

### `SW-008` – First-Class AI-Agent Toolchain, Structured Diagnostics & Zero-Hallucination Context (`Dedicated DR Recommended`)

-   **Category:** `Docstring & IDE UX` / `CLI & Agent Ergonomics` (User-Requested Priority – **Dedicated `Deep research` Recommended**)
-   **Problem & Friction:**
    -   Go and Rust lead AI code-generation benchmarks because Go eliminates syntactic ambiguity while Rust provides a strict, deterministic compiler feedback loop – yet no LLM has CoreX (`.cx`) in its pre-training weights prior to public launch.
    -   Without compact, machine-readable compiler feedback and zero-token-waste CLI introspection, coding agents must regex-parse ANSI box-drawing diagnostics, read multi-thousand-line `stdlib/cx/*.cx` source files to discover signatures/contracts, or guess Rust/Zig/TS syntax on first attempt.
-   **Candidate CoreX Design(s) (To Synthesize via Dedicated `DR-XX`):**
    1.  **Token-Minimal Structured Diagnostics & Patching (`corex check --format=json` / `ndjson`):**
        -   Emit compact, schema-versioned JSON/NDJSON diagnostics (extending the taxonomy hook in `stage0/src/diag/diagnostic.zig:684`) carrying exact UTF-8 byte & 1-based line/col spans, `E0xxx` / `W0xxx/slug` codes, `DR-17` shortest call-chain capability/contract witnesses, and machine-applicable `SuggestedFix` replacement spans (plus single-command targeted application) so agents converge in 1 iteration without regex scraping.
    2.  **Sub-5 ms CLI API & Contract Introspection (`corex doc <symbol_or_module>`):**
        -   Allow agents (and humans) to query exact canonical signatures, `/` & `*` parameter zones, `T!E` error-enum variants, `/|` docstrings, and compiler-inferred `@no_alloc` / `@no_panic` / `@no_block` / `@max_stack` / `EffectCapabilityMask` summaries directly from the terminal (e.g., `corex doc cx.col.Map`, `corex doc --signatures cx.fs`) in `< 5 ms` without loading raw implementation bodies into context.
    3.  **Self-Contained Language & Ownership Spec Embedded in Binary (`corex doc --llm-guide` & `corex init` Agent Rules):**
        -   Embed a version-exact, ultra-dense (~150–250 line) CoreX v1.0 grammar, MVS ownership (`&`, `&mut`, `own`, `&out`), error-handling (`T!E`, `?`, `catch`, `orelse`, `is`, `:=`), and anti-hallucination delta cheat sheet directly inside the `< 1 MB` `corex` binary (`corex doc --llm-guide`), and optionally wire `corex init` (`Stage L0`) to emit a minimal pointer/rule snippet so any coding agent in any offline workspace writes idiomatic `.cx` on turn 1.
    4.  **Agent-Native `corex-lang.org` Endpoints (`Stage L2` Post-`v0.0.1`):**
        -   Generate `/llms.txt`, `/llms-full.txt`, and deterministic `.md` API mirrors (`corex-lang.org/api/cx.fs.md` from `cx-api-docs.json`) alongside human HTML pages for zero-noise agentic browsing.
-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (pure CLI/diagnostic renderer, `corex doc`, `corex init`, and `cx-api-docs.json` surfaces).
    -   **Why a Dedicated `DR` First Pays Off:** A focused `Deep research` report benchmarking how modern coding agents (Claude Code, Antigravity, Codex, Cursor) consume `rustc --message-format=json`, `go doc`, `zig zen`, `oxlint`, MCP/CLI introspection, and `llms.txt` schemas will let us design the highest-signal, lowest-token JSON schema and `--llm-guide` density from first principles before self-hosting the CLI in `Phase 12.7` / `Stage L0`.
-   **Real Call-Site Evidence:**
    -   Applies to `100%` of agent-assisted CoreX workflows across `stage0/src/diag/{diagnostic,renderer}.zig`, `stage0/src/cli/router.zig` (`Phase 12.7` `compiler/main.cx`), `Stage L0` (`corex init` & `corex doc`), and `Stage L2` (`corex-lang/website`).

### `SW-009` – Safe `@no_panic` Inherent Slice Indexing (`get_copy` / `get_range`) & `&[]` Empty Slice Coercion

-   **Category:** `Stdlib Ergonomics` / `Syntax Refinement`
-   **Problem & Friction:**
    -   Direct `slice[idx]` and `slice[start..end]` carry the `may_panic` capability unless discharged locally by Pentagon BCE, which forces `@no_panic` parsers and transcoders to avoid `slice[idx]` whenever index bounds cross helper boundaries. Furthermore, constructing a zero-length non-`u8` slice `&[T]` currently requires `unsafe { @slice_from_raw_parts(@align_of[T]() as *T, 0_usize) }`.
    -   Consequently, `5` of the `6` `STD-02` modules had to define identical private `@std_cap_boundary(clears: [unsafe_op, may_panic])` helpers (`byte_at`, `u16_at`, `subslice_u8`, `subslice_u16`, `empty_str_slice`, `empty_path_slice`).
-   **Candidate CoreX Design(s):**
    -   Provide built-in `@no_alloc @no_panic` inherent `[T]` slice methods (`get`, `get_mut`, `get_copy` for `T: Copy`, `get_range`) alongside zero-cost `&[]` empty slice coercion to `&[T]`:

        ```cx
        // Before (repeated across path.cx, fs.cx, env.cx, process.cx):
        @std_cap_boundary(clears: [unsafe_op])
        fn empty_path_slice() -> &[Path] {
            unsafe { @slice_from_raw_parts(@align_of[Path]() as *Path, 0_usize) }
        }

        // After (100% safe, `@no_alloc @no_panic`, zero unsafe wrappers):
        let sub = raw.get_range(8_usize, srv_end) orelse &[];
        let empty_paths: &[Path] = &[];
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (inherent `[T]` methods + bidirectional empty-array-ref coercion `&[] -> &[T]`).
-   **Real Call-Site Evidence:**
    -   `22` duplicate helper definitions, `383` call sites, and `84` `@slice_from_raw_parts` sites across `stdlib/cx/path.cx:347-411` (`157` calls), `stdlib/cx/env.cx:241-309` (`95` calls), `stdlib/cx/fs.cx:717-760` (`80` calls), `stdlib/cx/process.cx:416-429` (`45` calls), `stdlib/cx/time.cx:284-305` (`6` calls), and `stdlib/cx/io.cx` (`13` raw slice sites).

### `SW-010` – Canonical Null Raw-Pointer Constructor (`.null` / `(*T).null()`) vs. `@default_init[*T]()`

-   **Category:** `Syntax Refinement` / `Stdlib Ergonomics`
-   **Problem & Friction:**
    -   Safe references (`&T`, `&mut T`) are strictly non-null, whereas raw pointers (`*T`, `*mut T`, `*opaque`, `*mut opaque`) represent nullable OS syscall and C-ABI pointers and already expose `.is_null()`. Constructing a typed null raw pointer currently requires `@default_init[*mut opaque]()` or `(0_usize as *mut u8)`, obscuring intent at FFI boundaries.
-   **Candidate CoreX Design(s):**
    -   Support inherent `.null()` (or contextual `.null`) strictly on raw pointer types `*T` / `*mut T` (never on `&T` / `&mut T`):

        ```cx
        // Before:
        win32_read_file(handle, dst_ptr, chunk_u32, &raw mut read_bytes, @default_init[*mut opaque]())

        // After:
        win32_read_file(handle, dst_ptr, chunk_u32, &raw mut read_bytes, .null)
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (`TokenKind.kw_null` / contextual inherent member on `.raw_ptr_ty` only).
-   **Real Call-Site Evidence:**
    -   `155` `@default_init[*…]()` call sites across `STD-02`: `stdlib/cx/fs.cx` (`87`), `stdlib/cx/process.cx` (`30`), `stdlib/cx/env.cx` (`24`), `stdlib/cx/io.cx` (`9`), `core/async.cx` (`3`), `stdlib/cx/time.cx` (`1`), and `core/sys/linux.cx` (`1`).

### `SW-011` – `@cfg(key != "value")` Inequality Predicate Support

-   **Category:** `Syntax Refinement`
-   **Problem & Friction:**
    -   `@cfg(…)` predicates frequently express non-Windows POSIX/WASI gates or architecture exclusions, which currently must be parenthesized as `@cfg(not (target.os == "windows"))`.
-   **Candidate CoreX Design(s):**
    -   Allow `!=` directly inside `@cfg` key-value comparisons alongside `==`:

        ```cx
        // Before:
        @cfg(not (target.os == "windows"))
        // After:
        @cfg(target.os != "windows")
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (reuses `TokenKind.bang_eq` `!=` in `@cfg` evaluator and `corex.toml` target predicates).
-   **Real Call-Site Evidence:**
    -   `77` `@cfg(not (target.os == "…"))` sites across `stdlib/cx/fs.cx` (`41`), `stdlib/cx/process.cx` (`12`), `stdlib/cx/io.cx` (`7`), `core/sys/linux.cx` (`7`), `stdlib/cx/path.cx` (`5`), `core/sys/macos.cx` (`4`), and `stdlib/cx/env.cx` (`1`).

### `SW-012` – `@linear` Obligation Discharge Along `errdefer` + `?` Early-Return Paths

-   **Category:** `Syntax Refinement` / `SAST Ergonomics`
-   **Problem & Friction:**
    -   When performing multiple fallible writes on a `@linear` resource such as `BufWriter` or `StagedAtomicFile` before final `buf_writer.close()?` / `staged.publish()`, each intermediate `?` exits on `.Err` before reaching `.close()`. Authors currently repeat 4-line `catch |err| { buf_writer.discard(); return .Err(err); }` blocks at every step unless `errdefer` can consume the `@linear` binding exclusively along error-unwind edges.
-   **Candidate CoreX Design(s):**
    -   Allow `errdefer own_cleanup(own linear_val);` (or method `errdefer buf_writer.discard();`) in `MIR` SAST Pass 2 to satisfy `@linear` consumption strictly along `.Err` return edges while leaving `linear_val` live on the normal path for `buf_writer.close()?`:

        ```cx
        // Before (repeated on every fallible write before `.close()?`):
        var bw = BufWriter.new(file.as_writer());
        bw.write_all(header) catch |err| {
            bw.discard();
            return .Err(err);
        };
        bw.close()

        // After (1-line error-edge cleanup + normal-edge `.close()`):
        var bw = BufWriter.new(file.as_writer());
        errdefer bw.discard();
        bw.write_all(header)?;
        bw.close()
        ```

-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (`MIR` `errdefer` cleanup CFG edge + `mir_sast.zig` `@linear` Completeness Law).
-   **Real Call-Site Evidence:**
    -   Hit across `stdlib/cx/fs.cx` (`write_atomic` / `StagedAtomicFile` staging flows), `tests/unit/phase11_std02_gates_test.zig:643-703`, and `tests/unit/phase10_lsp_test.zig:4009-4014` (`15+` sites).

### `SW-013` – Static `.data.rel.ro` Promotion for `&CONST_VTABLE` Globals & Typed Optional `fn` Slots on `ReactorVTable`

-   **Category:** `Stdlib Ergonomics` / `Syntax Refinement`
-   **Problem & Friction:**
    -   Taking `&CONST_STRUCT` on a module-level `const` containing `fn(…)` pointers materialize a stack copy unless promoted to static `.rodata` / `.data.rel.ro`, and `core.async.ReactorVTable` currently types its 8 hook slots as `usize` (`0` = null), requiring private shadow structs and pointer casts across `STD-02` consumers.
-   **Candidate CoreX Design(s):**
    -   Promote `const VTABLE: T = …;` containing compile-time `fn` items to static `.data.rel.ro` globals so `&VTABLE` has `'static` provenance (`0` stack spills), and type `ReactorVTable` slots directly as `(extern "C" fn(…))?` (preserving exact `8 * sizeof(usize)` null-niche layout).
-   **Compiler & Tooling Impact:**
    -   **`TokenKind` Delta:** `0` (`hir.zig` `isRelocationFreeValueType` / `const_rodata_map` relocation support + `core/async.cx` field typing).
-   **Real Call-Site Evidence:**
    -   `84` `ReactorVTable` cast/shadow sites across `stdlib/cx/{io,time,env,fs,process}.cx` plus stream vtable dispatch in `stdlib/cx/io.cx` and `stdlib/cx/fs.cx`.

---

## 3. Decided & Rejected Ledger

| ID | Proposal Summary | Decision | Rationale / Canonical Reference |
| :--- | :--- | :--- | :--- |
| `SW-004` | Compact, de-noised hover contract & stack footer (`<sub>` + theme-native CSS variable, dropping `(verified)`) | Approved & Implemented | `stage0/src/lsp_server.zig` (`appendFnHoverContractBullets`) + `../vscode-ext-corex/src/extension.ts` (`toVsDoc` with `supportHtml: true`, `var(--vscode-descriptionForeground)` in Light/Dark themes and un-dimmed High Contrast). |
