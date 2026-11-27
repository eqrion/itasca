# Reading a theorem’s premises

For validation, read the [WebAssembly module grammar](../../../../WebAssembly/WebAssembly/Binary/Module.lean) for the byte-to-syntax relation and [Validation](Validation.lean) for the certificate tying those bytes to typing and metadata. [Streaming](Streaming.lean) adds obligations on issued batches, workers, and the source. [Observations](Observations.lean) describes what callback traces reveal.

For compilation, start with the [compilation certificate](Compiler/Compilation.lean). For execution, start with the [runtime protocol](Runtime.lean): its store predicate is chosen once and retained across operations. Follow [Host](Host.lean) for callback effects and [Resources](Resources.lean) for the independent source budgets used to exclude resource errors. These definitions are part of the public claims, including the fields of each certificate.
