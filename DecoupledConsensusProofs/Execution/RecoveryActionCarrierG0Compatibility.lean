module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.HealingSurface

/-!
# G0 compatibility of the grade-2 action carrier

This is the store-level clearance leaf used by the recovery action argument.
It uses only the fact that the selected SG vote is `g0_clear`; no run-level
delivery or filter-production hypothesis belongs here.
-/
