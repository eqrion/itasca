# Callback observations

A visitor can return normally and still reject an instruction. [Visitor contracts](Total.lean) distinguish the premise needed to finish a run from the stronger premise needed to prove acceptance. [Run traces](RunTrace.lean) connects dispatched callbacks to observations, including the callback that rejects. The [public trace theorem](../Results/Trace.lean) applies to any observation function satisfying `Records`.
