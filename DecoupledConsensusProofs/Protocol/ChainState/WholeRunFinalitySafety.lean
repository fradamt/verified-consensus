module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.WholeRunFinalitySafety
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots
public import DecoupledConsensusProofs.Protocol.Handlers.FinalizationBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Execution.Runtime

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Unconditional whole-run finality safety

Accountable chain safety and the run-wide slashable bound make every two
finalized run-block targets compatible. Store safety uses the named
finalization carrier at each honest store and reuses the named chain result;
it does not reason from a store-pool evidence disjunction. The public entry
points take only `FinalityExecution`: a well-formed event schedule and
run-scoped root collision freedom. They do not use delivery, authenticity,
synchrony, recovery, or liveness premises.

proof note (design note). `WholeRunAccountableFinalitySafety` and
`WholeRunFinalitySafety` now quantify their chain clause over `NamedBlock V`
and `NamedFinalizedAt`, whose producer is `Protocol.chainAccountableSafety`
(`DecoupledConsensusProofs/Safety/NamedMain.lean`). That module is outside the
restated cone and has no built `.olean` yet (branches `safety-main`), so this file
carries a **local, self-contained copy** of its named counting argument —
`namedAccountableSafety_oriented` / `namedChainAccountableSafety` below —
built only from cone modules already green: `NamedFinalityCertificates`
(`finalized_zero_is_genesis`, `finality_certificate`, `height_crossing`),
`NamedStoreRoots` (`chainOrder_derive_named`, `derive_named_anchors_preceq`,
both re-exported from `NamedDerivationGeometry`), `NamedAncestry`
(`erased_ancestor_lift`, for `namedRootInjectiveOnAncestors_of_collisionFree`,
the local copy of `NamedFinalizationBridge.rootInjectiveOnAncestors_of_
collisionFree` from the uncone'd `NamedFinalityComparison.lean`), and the
erased crosswalk already in `Protocol.Main` (`named_row_erase_mem`,
`conflictsWithFinality_erase_of_matchesEntry`, the swap/mono lemmas). The
store-level clauses stay over the erased `Protocol.Store` reached through
`.core`; `storeAccountableSafety_stateBefore` bridges an honest event-prefix
pair to the local named chain result via the named finalization carrier
(`NamedFinalizationBridge.finalization_carrier_stateBefore`, in cone) and
transports the chain-level evidence pool to the store pool with
`Protocol.chain_attestations_subset_store` / `Protocol.hasSlashableWeightBetween_
mono`, exactly as the retired `Proofs.Bridges.storeAccountableSafety_of_
admissibleCore` did before this proof.

Once `Protocol.NamedMain` lands in the cone, `namedAccountableSafety_oriented`
and `namedChainAccountableSafety` below become redundant with
`Protocol.namedAccountableSafety_oriented` / `Protocol.
chainAccountableSafety` and can be deleted in favour of importing that file.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A time-filtered run state is an event prefix when event keys are sorted.
This is the only schedule fact used by the finality transport. -/
private theorem stateAt_eq_stateBefore_of_sorted (S : Setup V) {rho : Run V}
    (sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    (t : Time) : ∃ n : Nat, Run.stateAt S rho t = rho.stateBefore S n := by
  have hpref : rho.events.filter (fun e => decide (e.time ≤ t)) <+: rho.events := by
    rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (p := fun e => decide (e.time ≤ t))
      (fun e f hk hf => by
        simp only [decide_eq_true_eq] at hf ⊢
        exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf) _ sorted]
    exact List.takeWhile_prefix _
  let n := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hpre : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take n := List.prefix_iff_eq_take.mp hpref
  refine ⟨n, ?_⟩
  change (rho.events.filter (fun e => decide (e.time ≤ t))).foldl
      (NamedWorld.step S) NamedWorld.init =
    (rho.events.take n).foldl (NamedWorld.step S) NamedWorld.init
  rw [hpre]


/-- Two run blocks are root-injective on their ancestors under run-wide
collision freedom. Local copy of the un-cone'd `NamedFinalizationBridge.
rootInjectiveOnAncestors_of_collisionFree` (`NamedFinalityComparison.lean`,
), built from cone-only `Proofs.NamedAncestry.erased_ancestor_lift`. -/
private theorem namedRootInjectiveOnAncestors_of_collisionFree
    (S : Setup V) (rho : Run V) (hroot : NamedRootCollisionFree S rho)
    (A B : NamedBlock V) (hA : RunBlock S rho A) (hB : RunBlock S rho B) :
    RootInjectiveOnAncestors A.erase B.erase := by
  intro X Y hX hY hroots
  obtain ⟨Z, hZmem, hXZ⟩ := hX
  obtain ⟨W, hWmem, hYW⟩ := hY
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZmem hWmem
  rcases hZmem with hZmem | hZmem <;> subst hZmem <;>
      rcases hWmem with hWmem | hWmem <;> subst hWmem
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inl hX'anc) (Or.inl hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inl hX'anc) (Or.inr hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inr hX'anc) (Or.inl hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y' (Or.inr hX'anc) (Or.inr hY'anc)
      (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]

/-- **P1's counting argument over the named derivation**, oriented by the
height order. Local copy of `Protocol.namedAccountableSafety_oriented`
(`Safety/NamedMain.lean`), built from cone-only `NamedFinalityCertificates`
and `NamedStoreRoots` producers; see the file header. -/
private theorem namedAccountableSafety_oriented (E : Env V) (cfg : Protocol.HeightConfig)
    {B₁ B₂ : NamedBlock V} {T₁ T₂ : Block V} {h₁ h₂ : Height}
    (hroot : RootInjectiveOnAncestors B₁.erase B₂.erase)
    (hf₁ : NamedFinalizedAt E cfg B₁ T₁ h₁) (hf₂ : NamedFinalizedAt E cfg B₂ T₂ h₂)
    (hle : h₁ ≤ h₂) :
    HasE1WeightAt E ⟨h₁, T₁.root⟩ (chain_attestations B₁.erase)
        (chain_attestations B₂.erase) ∨
      Block.compatible T₁ T₂ = true := by
  obtain ⟨hF₁, hh₁⟩ := hf₁
  obtain ⟨hF₂, hh₂⟩ := hf₂
  by_cases hz : h₁ = 0
  · refine Or.inr ?_
    have hgen : T₁ = Block.genesis := by
      rw [← hF₁]
      exact NamedFinalityCertificates.finalized_zero_is_genesis E cfg B₁
        (by rw [hh₁]; exact hz)
    rw [hgen]
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Protocol.preceq_genesis T₂)
  · obtain ⟨F, _hFB₁, hFerase, QF, hQF, hwF⟩ :=
      NamedFinalityCertificates.finality_certificate E cfg B₁
        (by rw [hh₁]; exact hz)
    have hFroot : F.root = T₁.root := by
      rw [← Proofs.NamedWire.erase_root F, hFerase, hF₁]
    have hB₂h : h₁ < (Protocol.derive_named E cfg B₂).h := by
      refine Nat.lt_of_le_of_lt hle ?_
      rw [← hh₂]
      exact (Proofs.NamedStoreRoots.chainOrder_derive_named E cfg B₂).finalized_below_height
    obtain ⟨X, hXB₂, _hXh, QP, hQP, hwP⟩ :=
      NamedFinalityCertificates.height_crossing E cfg B₂ h₁
        (Nat.one_le_iff_ne_zero.mpr hz) hB₂h
    have hXB₂e : Block.preceq X.erase B₂.erase = true := Proofs.NamedWire.erase_preceq hXB₂
    by_cases hxr : X.root = T₁.root
    · refine Or.inr ?_
      have hT₁B₁ : Block.preceq T₁ B₁.erase = true := by
        rw [← hF₁]
        exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq E cfg B₁).1
      have hT₂B₂ : Block.preceq T₂ B₂.erase = true := by
        rw [← hF₂]
        exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq E cfg B₂).1
      have hXT : X.erase = T₁ :=
        hroot X.erase T₁
          ⟨B₂.erase, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hXB₂e⟩
          ⟨B₁.erase, Finset.mem_insert_self _ _, hT₁B₁⟩
          (by rw [Proofs.NamedWire.erase_root]; exact hxr)
      exact Block.compatible_of_preceq_common (hXT ▸ hXB₂e) hT₂B₂
    · refine Or.inl ⟨QF ∩ QP, quorum_intersection E hQF hQP, fun i hi => ?_⟩
      obtain ⟨hiF, hiP⟩ := Finset.mem_inter.mp hi
      obtain ⟨cF, a, hcF, haF, hav, hap⟩ := hwF i hiF
      obtain ⟨cP, b, hcP, hbP, hbv, hbm⟩ := hwP i hiP
      refine ⟨a.erase, Protocol.named_row_erase_mem hcF haF, b.erase,
        Protocol.named_row_erase_mem hcP hbP, hav, hbv, ?_, ?_⟩
      · simpa only [NamedAttestation.erase, hh₁, hFroot] using hap
      · exact Protocol.conflictsWithFinality_erase_of_matchesEntry hbm hxr

/-- **P1, chain-level accountable safety over the named derivation.** Local
copy of `Protocol.chainAccountableSafety`; see the file header. -/
private theorem namedChainAccountableSafety (E : Env V) (cfg : Protocol.HeightConfig)
    (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height)
    (hroot : RootInjectiveOnAncestors B₁.erase B₂.erase)
    (hf₁ : NamedFinalizedAt E cfg B₁ T₁ h₁)
    (hf₂ : NamedFinalizedAt E cfg B₂ T₂ h₂) :
    HasSlashableWeightBetween E (chain_attestations B₁.erase)
        (chain_attestations B₂.erase) ∨
      Block.compatible T₁ T₂ = true := by
  rcases Nat.le_total h₁ h₂ with hle | hle
  · rcases namedAccountableSafety_oriented E cfg hroot hf₁ hf₂ hle with hev | hcomp
    · exact Or.inl (hasE1WeightAt_toSlashableWeight hev)
    · exact Or.inr hcomp
  · rcases namedAccountableSafety_oriented E cfg
      (Protocol.rootInjectiveOnAncestors_symm hroot) hf₂ hf₁ hle with hev | hcomp
    · exact Or.inl (Protocol.hasSlashableWeightBetween_of_hasE1WeightAt_swap hev)
    · exact Or.inr (Protocol.compatible_comm hcomp)

/-- Two honest event-prefix stores either agree, or their combined evidence
convicts `2q − W` of weight. Bridges the named finalization carrier at both
prefixes into one application of the local named chain-level theorem. -/
private theorem storeAccountableSafety_stateBefore (S : Setup V) {rho : Run V}
    (hroot : RootCollisionFree S rho) {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    (i j : Nat) :
    HasSlashableWeightBetween S.E
        (store_attestations (rho.stateBefore S i u).st.core)
        (store_attestations (rho.stateBefore S j v).st.core) ∨
      Block.compatible (rho.stateBefore S i u).st.core.F
        (rho.stateBefore S j v).st.core.F = true := by
  obtain ⟨Du, hDu, hFu, -⟩ := NamedFinalizationBridge.finalization_carrier_stateBefore S rho i u
  obtain ⟨Dv, hDv, hFv, -⟩ := NamedFinalizationBridge.finalization_carrier_stateBefore S rho j v
  have hBu : RunBlock S rho Du := Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDu
  have hBv : RunBlock S rho Dv := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDv
  have hroot : RootInjectiveOnAncestors Du.erase Dv.erase :=
    namedRootInjectiveOnAncestors_of_collisionFree S rho hroot Du Dv hBu hBv
  have hTu : (rho.stateBefore S i u).st.core.T =
      (rho.stateBefore S i u).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho i u).1.1.1.1
  have hTv : (rho.stateBefore S j v).st.core.T =
      (rho.stateBefore S j v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1.1
  have hDuMem : Du.erase ∈ (rho.stateBefore S i u).st.core.T := by
    rw [hTu]; exact Finset.mem_image_of_mem _ hDu
  have hDvMem : Dv.erase ∈ (rho.stateBefore S j v).st.core.T := by
    rw [hTv]; exact Finset.mem_image_of_mem _ hDv
  rcases namedChainAccountableSafety S.E S.cfg Du Dv
      (rho.stateBefore S i u).st.core.F (rho.stateBefore S j v).st.core.F
      (Protocol.derive_named S.E S.cfg Du).h_F
      (Protocol.derive_named S.E S.cfg Dv).h_F
      hroot ⟨hFu, rfl⟩ ⟨hFv, rfl⟩ with hev | hcomp
  · exact Or.inl (Protocol.hasSlashableWeightBetween_mono hev
      (Protocol.chain_attestations_subset_store hDuMem)
      (Protocol.chain_attestations_subset_store hDvMem))
  · exact Or.inr hcomp

/-- All run-scoped accountability conclusions follow from the narrow finality
execution record, including arbitrary event-prefix stores and horizon-qualified
reads. -/
theorem wholeRunAccountableFinalitySafety (S : Setup V) {rho : Run V}
    (exec : FinalityExecution S rho) : WholeRunAccountableFinalitySafety S rho := by
  refine ⟨?_, ?_, ?_⟩
  · intro B₁ B₂ T₁ T₂ h₁ h₂ hB₁ hB₂ hfin₁ hfin₂
    exact namedChainAccountableSafety S.E S.cfg B₁ B₂ T₁ T₂ h₁ h₂
      (namedRootInjectiveOnAncestors_of_collisionFree S rho
        exec.rootCollisionFree B₁ B₂ hB₁ hB₂) hfin₁ hfin₂
  · intro u hu v hv i j
    exact storeAccountableSafety_stateBefore S exec.rootCollisionFree hu hv i j
  · intro u hu v hv t t'
    obtain ⟨n, hn⟩ := stateAt_eq_stateBefore_of_sorted S exec.sorted t
    obtain ⟨n', hn'⟩ := stateAt_eq_stateBefore_of_sorted S exec.sorted t'
    have hequ : rho.storeAt S u t = (rho.stateBefore S n u).st :=
      congrArg (·.st) (congrFun hn u)
    have heqv : rho.storeAt S v t' = (rho.stateBefore S n' v).st :=
      congrArg (·.st) (congrFun hn' v)
    rw [hequ, heqv]
    exact storeAccountableSafety_stateBefore S exec.rootCollisionFree hu hv n n'

/-- The accountable bound gives agreement for all finalized run blocks and
honest stores. No participation or faulty-weight bound is needed. -/
theorem wholeRunFinalitySafety (S : Setup V) {rho : Run V}
    (exec : FinalityExecution S rho) (hsb : SlashableBound S rho) :
    WholeRunFinalitySafety S rho := by
  have hchain :
      ∀ (B₁ B₂ : NamedBlock V) T₁ T₂ h₁ h₂,
        RunBlock S rho B₁ → RunBlock S rho B₂ →
        NamedFinalizedAt S.E S.cfg B₁ T₁ h₁ →
        NamedFinalizedAt S.E S.cfg B₂ T₂ h₂ →
        Block.compatible T₁ T₂ = true := by
    intro B₁ B₂ T₁ T₂ h₁ h₂ hB₁ hB₂ hfin₁ hfin₂
    rcases namedChainAccountableSafety S.E S.cfg B₁ B₂ T₁ T₂ h₁ h₂
        (namedRootInjectiveOnAncestors_of_collisionFree S rho
          exec.rootCollisionFree B₁ B₂ hB₁ hB₂)
        hfin₁ hfin₂ with hslash | hcompatible
    · exact False.elim (hsb B₁ B₂ hB₁ hB₂ hslash)
    · exact hcompatible
  refine ⟨hchain, ?_⟩
  intro u hu v hv t t'
  obtain ⟨n, hn⟩ := stateAt_eq_stateBefore_of_sorted S exec.sorted t
  obtain ⟨n', hn'⟩ := stateAt_eq_stateBefore_of_sorted S exec.sorted t'
  have hequ : rho.storeAt S u t = (rho.stateBefore S n u).st :=
    congrArg (·.st) (congrFun hn u)
  have heqv : rho.storeAt S v t' = (rho.stateBefore S n' v).st :=
    congrArg (·.st) (congrFun hn' v)
  obtain ⟨Du, hDu, hFu, -⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho n u
  obtain ⟨Dv, hDv, hFv, -⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho n' v
  have hBu : RunBlock S rho Du := Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDu
  have hBv : RunBlock S rho Dv := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDv
  have hfin₁ : NamedFinalizedAt S.E S.cfg Du (rho.storeAt S u t).F
      (Protocol.derive_named S.E S.cfg Du).h_F := by
    rw [hequ]; exact ⟨hFu, rfl⟩
  have hfin₂ : NamedFinalizedAt S.E S.cfg Dv (rho.storeAt S v t').F
      (Protocol.derive_named S.E S.cfg Dv).h_F := by
    rw [heqv]; exact ⟨hFv, rfl⟩
  exact hchain Du Dv (rho.storeAt S u t).F (rho.storeAt S v t').F _ _ hBu hBv hfin₁ hfin₂

/-- Compatibility wrapper: project the narrow finality record from the broader
execution contract before applying the run-scoped agreement theorem. -/
theorem wholeRunFinalitySafety_of_slashableBound (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hsb : SlashableBound S rho) :
    WholeRunFinalitySafety S rho :=
  wholeRunFinalitySafety S
    (FinalityExecution.of_executionValid (ExecutionValid.ofNamedAdmissibleCore adm)) hsb

/-- The Byzantine-weight condition is a derived corollary, not the primary
assumption of finality agreement. No participation premise is needed. -/
theorem wholeRunFinalitySafety_of_belowOneThird (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hbot : BelowOneThird S rho.honest) :
    WholeRunFinalitySafety S rho :=
  wholeRunFinalitySafety S
    (FinalityExecution.of_executionValid (ExecutionValid.ofNamedAdmissibleCore adm))
    (slashableBound_of_admissibleCore_belowOneThird S adm hbot)

/-- The pure accountable-finality theorem, with only the collision-free hash
idealization on the two compared chains. -/
theorem pureAccountableFinalitySafety (S : Setup V) :
    PureAccountableFinalitySafety S :=
  namedChainAccountableSafety S.E S.cfg

/-- Pure finality agreement after excluding slashable weight between the two
chain evidence pools. -/
theorem pureFinalityAgreement (S : Setup V) : PureFinalityAgreement S := by
  intro B₁ B₂ T₁ T₂ h₁ h₂ hroot hfin₁ hfin₂ hbound
  rcases namedChainAccountableSafety S.E S.cfg B₁ B₂ T₁ T₂ h₁ h₂
      hroot hfin₁ hfin₂ with hslash | hcompatible
  · exact False.elim (hbound hslash)
  · exact hcompatible

/-- The complete finality contract is independent of GST, delivery,
authenticity, recovery, and liveness. -/
theorem finalitySafety (S : Setup V) : FinalitySafety S :=
  { accountable := pureAccountableFinalitySafety S
    agreement := pureFinalityAgreement S
    runAccountable := fun _ exec => wholeRunAccountableFinalitySafety S exec
    runAgreement := fun _ exec hsb => wholeRunFinalitySafety S exec hsb }

#print axioms pureAccountableFinalitySafety
#print axioms pureFinalityAgreement
#print axioms wholeRunAccountableFinalitySafety
#print axioms wholeRunFinalitySafety
#print axioms wholeRunFinalitySafety_of_slashableBound
#print axioms wholeRunFinalitySafety_of_belowOneThird
#print axioms finalitySafety

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
