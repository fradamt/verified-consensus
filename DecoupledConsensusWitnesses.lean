module
public import DecoupledConsensusProofs.Protocol.Grades.LegacyVocabulary
public import DecoupledConsensusWitnesses.Index
public import DecoupledConsensusWitnesses.ModelVocabulary

/-!
# Non-vacuity witnesses for the public consensus bundle

Every public statement in `DecoupledConsensusStatements` has the form
"if the premises hold for a run, then the guarantee holds". This library holds,
for each statement, one concrete kernel-checked run for which EVERY premise
holds, with at least one Byzantine validator, so that the guarantee really
applies to something. `DecoupledConsensusWitnesses/Index.lean` lists the
statements and the witness (or "missing") for each.
-/
