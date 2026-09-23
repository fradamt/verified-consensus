import DecoupledConsensusStatements
import Lean.Util.FoldConsts

open Lean Elab Command

private def moduleOf? (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.header.moduleNames[idx.toNat]?

private def isProjectModule (moduleName : Name) : Bool :=
  ["DecoupledConsensusModel", "DecoupledConsensusInternal",
    "DecoupledConsensusStatements", "DecoupledConsensusProofs",
    "DecoupledConsensusWitnesses"].any (fun pfx =>
      moduleName.toString.startsWith pfx)

private partial def reachableFrom (env : Environment) (pending : List Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | decl :: rest =>
      if seen.contains decl then
        reachableFrom env rest seen
      else
        let seen := seen.insert decl
        match env.find? decl with
        | none => reachableFrom env rest seen
        | some info =>
            reachableFrom env (info.getUsedConstantsAsSet.toList ++ rest) seen

private def isSourceDeclaration (env : Environment) (decl : Name) : Bool :=
  if decl.isInternalDetail || (env.getProjectionFnInfo? decl).isSome then
    false
  else
    match env.find? decl with
    | some (.ctorInfo _) | some (.recInfo _) => false
    | some _ =>
        let final := decl.getString!
        final != "casesOn" && final != "recOn" && final != "noConfusion" &&
          final != "noConfusionType" && final != "ctorIdx" &&
          !final.startsWith "_sizeOf" &&
          !decl.toString.contains ".mk."
    | none => false

private def isApprovedStatementHelper (decl : Name) : Bool :=
  [
    `DecoupledConsensusModel.Internal.honestHMaxBeforeIndex,
    `DecoupledConsensusModel.Statements.finalityStartup_pos,
    `DecoupledConsensusModel.Statements.WeakVoteContinuation,
    `DecoupledConsensusModel.Statements.VoteSourcesSafeAt,
    `DecoupledConsensusModel.Statements.safetyCutBound,
    `DecoupledConsensusModel.Statements.VoteSafetyAfterRecovery,
    `DecoupledConsensusModel.Statements.WeakVoteContinuationSeed,
    `DecoupledConsensusModel.Statements.Instantiation.roundAt,
    `DecoupledConsensusModel.Statements.roundAt_spec,
    `DecoupledConsensusModel.Statements.roundAt_min,
    `DecoupledConsensusModel.Statements.Instantiation.boundedPhaseStartLag,
    `DecoupledConsensusModel.Statements.Instantiation.recoveryRound,
    `DecoupledConsensusModel.Statements.instance,
    `DecoupledConsensusModel.Statements.ourConstants,
    `DecoupledConsensusModel.Statements.Generic.NoFutureRead,
    `DecoupledConsensusModel.Block.preceq.congr_simp,
    `DecoupledConsensusModel.Internal.runBlock,
    `DecoupledConsensusModel.Protocol.voteDutyHead,
    `DecoupledConsensusModel.Proofs.HealingSurface.actionSGBlockAt,
    `DecoupledConsensusModel.Proofs.HealingSurface.fgConfirmationWitness
  ].contains decl

run_cmd do
  let env ← getEnv
  let reachable := reachableFrom env [
    ``DecoupledConsensusModel.Statements.Generic.Consensus.mk,
    ``DecoupledConsensusModel.Statements.Instantiation.Consensus]
  let projectReachable := reachable.toList.filter fun decl =>
    (moduleOf? env decl).any (isProjectModule ·)
  let statementDecls := env.const2ModIdx.keysArray.toList.filter fun decl =>
    (moduleOf? env decl).any fun moduleName =>
      moduleName.toString.startsWith "DecoupledConsensusStatements"
  let statementSources := statementDecls.filter (isSourceDeclaration env)
  let reachableSources := statementSources.filter reachable.contains
  let unreachableSources := statementSources.filter fun decl =>
    isSourceDeclaration env decl && !reachable.contains decl &&
      !isApprovedStatementHelper decl
  IO.println s!"PROJECT_REACHABLE_COUNT {projectReachable.length}"
  IO.println s!"STATEMENT_DECL_COUNT {statementDecls.length}"
  IO.println s!"STATEMENT_SOURCE_COUNT {statementSources.length}"
  IO.println s!"STATEMENT_REACHABLE_COUNT {reachableSources.length}"
  IO.println s!"STATEMENT_UNREACHABLE_COUNT {unreachableSources.length}"
  for decl in statementDecls.filter (isSourceDeclaration env) |>.mergeSort
      (Name.quickCmp · · |>.isLE) do
    let status :=
      if reachable.contains decl then "SR"
      else if isApprovedStatementHelper decl then "SH"
      else "SU"
    IO.println s!"{status}\t{(moduleOf? env decl).getD `unknown}\t{decl}"
  unless unreachableSources.isEmpty do
    throwError "statement source contains {unreachableSources.length} declarations outside Consensus"
