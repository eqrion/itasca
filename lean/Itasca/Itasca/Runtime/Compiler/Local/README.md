# One compiler callback

A callback can update more than the emitted instruction stream. Branches can leave forward targets to fix up, and branch tables use auxiliary storage. Follow [callback contracts](Callbacks/) for the state changes, [lowering](Lowering/) for instruction effects, and [capacity](Capacity/) for the source demand and allocation premises that make those operations succeed.
