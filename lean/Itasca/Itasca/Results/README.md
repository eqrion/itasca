# Public theorems

| Question | Theorem module |
| --- | --- |
| What do accepted bytes and returned metadata describe? When must validation accept? | [Validate](Validate.lean) |
| Do the same bytes always decode to the same syntax? | [Unique](Unique.lean) |
| Which source and scheduler behaviors support streaming validation? | [Stream](Stream.lean) |
| What work does a successfully finished batch certify? | [Batch](Batch.lean) |
| Which callbacks occur, including on rejection? | [Trace](Trace.lean) |

Read each theorem with its [definitions](Definitions/README.md). In validation statements, `.ok (.Ok decoded)` means the extracted computation returned normally **and** Rust accepted. A normal-return theorem alone also permits `.ok (.Err error)`.
