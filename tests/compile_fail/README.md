# Negative Safety Verification Suite (`tests/compile_fail/`)

Contains negative compile-fail `.cx` fixtures verifying that invalid CoreX source programs are
deterministically rejected with exact diagnostic codes, byte/line/column spans, and remediation hints.

## Verification Contract

1.  **Exact Diagnostic Code Parity:** Every `.cx` test fixture in this directory declares expected
    `//~ ERROR [E0xxx]: …` or `//~ WARNING [W0xxx]: …` annotations matched against `DiagnosticSink`.
2.  **Zero False Positives:** Adjacent valid constructs must be verified in `tests/run_pass/` and
    `tests/unit/` so tightened static checks never reject well-typed CoreX programs.
3.  **Catalog Drift Guard:** Every `DiagnosticCode` registered in `DIAGNOSTIC_CATALOG` (`E00xx`–`E05xx`
    and `W00xx`–`W05xx`) must be exercised by unit, snapshot, or `compile_fail` fixtures as compiler
    stages (`Stage 1`–`Stage 3`) come online.

## Fixture Annotation Format

```text
// compile-flags: --check
fn use_after_transfer(own buffer: ByteBuffer) {
    let packet = consume_payload(buffer);
    return read_header(buffer); //~ ERROR [E0302]: use of moved value `buffer` after scope transfer
}
```
