# Compiling a complete module

[Compilation](Compilation.lean) establishes normal return on arbitrary bytes under allocator correctness. To show that valid input actually produces code, [batch availability](BatchLoopAvailable.lean) combines source validity and resource bounds with the worker loop. [Integration](../../Integration/Compilation.lean) packages the collected functions and initializers into the certificate exposed by [Compile](../../../Results/Compile.lean).
