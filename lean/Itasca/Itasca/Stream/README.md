# Streaming validation

A returned batch contributes evidence only for work performed on the issued environment and byte region. [Submission](SubmissionSound.lean) and [retirement](RetirementAndFraming.lean) track that evidence across scheduler calls. [Completeness](Completeness.lean) assembles the successful run and specializes it to a contiguous source.

When inspecting an offset, check its origin: entry offsets are relative to the code region, function starts to the batch, and operator positions to the instruction body. The [public streaming premises](../Results/Definitions/Streaming.lean) specify what the source and scheduler must preserve.
