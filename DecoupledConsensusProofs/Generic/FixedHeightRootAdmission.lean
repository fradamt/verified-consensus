module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Fairness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Execution.RawHeightAdapters

@[expose] public section

/-!
# Fixed-height root-target admission

A justification carrier held at a fixed-height root-interference read has a real
acceptance event strictly before that read. After GST, one relay delay is enough
for a later honest proposer to accept it. Accountable finality safety orients
every other delivery guard toward the carrier while the honest raw frontier
remains at height `H`.

The public wrappers remove the prior carrier-admission premise. They expose the
exact later proposal head, the exact relay and horizon inequalities, and the
bounded opening round supplied by either proposer recurrence contract.

sg-selection (design note): the justification carrier is a named body
(`NamedBlock V`), read via `Internal.NamedJustifiedAt`/`derive_named`; `RunBlock`
lives over `NamedBlock`. `FixedHeightRootTargetAdmittedAtProposal` and the
carrier-free composed theorems (`fixedHeightRootTarget_getHead_rebase_or_
hMaxRise`, `_rebase_or_hMaxRise`) are already supplied by
`FixedHeightRootCoreRun`; this module's job narrows to constructing the named
admission witness from a post-GST relay delay and delegating to those.

the prior "unless already rebased" case split is gone: the named finalization
carrier now gives the receiver-finalized-below-carrier fact directly
(`NamedFinalizationBridge.finalized_preceq_of_height_lt`), in the one useful
direction, so the `hnotRebased` premise the prior proof needed to rule out the
other direction is no longer meaningful and has been dropped.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every concrete justification carrier selected at a fixed-height
interference read has exactly the fixed frontier height. -/
theorem FixedHeightJustificationRootAtRead.carrierDerivedHeight
    {S : Setup V} {rho : Run V} {H : Height}
    {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    (adm : Admissible S rho)
    {carrier : NamedBlock V}
    (hcarrierAt : carrier ∈ (rho.storeBeforeTime S w read).bodies)
    (hcarrierJust : Internal.NamedJustifiedAt S.E S.cfg carrier
      (rho.storeBeforeTime S w read).J
      (rho.storeBeforeTime S w read).h_j) :
    (Protocol.derive_named S.E S.cfg carrier).h = H := by
  have hOne : 1 ≤ H :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have hcarrierLower :
      H ≤ (Protocol.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (Proofs.NamedStoreRoots.chainOrder_derive_named
        S.E S.cfg carrier).justified_below_height
    have hjEq : (Protocol.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (Protocol.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcarrierUpper :
      (Protocol.derive_named S.E S.cfg carrier).h ≤ H := by
    have hle := Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
      S rho read w carrier hcarrierAt
    exact hle.trans (le_of_eq h.fixedTarget.frontier)
  exact Nat.le_antisymm hcarrierUpper hcarrierLower

/-- Compatibility corollary for the original strict-read interference record. -/
theorem FixedHeightRootInterferenceAtRead.carrierDerivedHeight
    {S : Setup V} {rho : Run V} {H : Height}
    {w : V} {read : Time} {P : Block V}
    (h : FixedHeightRootInterferenceAtRead S rho H w read P)
    (adm : Admissible S rho)
    {carrier : NamedBlock V}
    (hcarrierAt : carrier ∈ (rho.storeBeforeTime S w read).bodies)
    (hcarrierJust : Internal.NamedJustifiedAt S.E S.cfg carrier
      (rho.storeBeforeTime S w read).J
      (rho.storeBeforeTime S w read).h_j) :
    (Protocol.derive_named S.E S.cfg carrier).h = H :=
  h.toJustificationRootAtRead.carrierDerivedHeight
    adm hcarrierAt hcarrierJust



/-- A named body held at an honest strict read is either genesis or was
accepted, strictly before that read, at the very same named identity (no
root-collision detour is needed since the body is already in hand). -/
private theorem carrierAcceptsBeforeStrictRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (w : V) (read : Time) {D : NamedBlock V}
    (hDmem : D ∈ (rho.storeBeforeTime S w read).bodies) :
    D = NamedBlock.genesis ∨
      ∃ (i : Nat) (t : Time), Run.acceptsAt S rho i w (.block D) t ∧ t < read := by
  obtain ⟨N, hN, hNlt⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed read
  have hDmem' : D ∈ (rho.stateBefore S N w).st.bodies := by
    simpa only [Run.storeBeforeTime, hN] using hDmem
  have hprocessed : Object.processed (rho.stateBefore S N w).st (.block D) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hDmem'
  rcases Protocol.acceptsAt_block_of_processed S rho w N D hprocessed with
    hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl hgen
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have heLt : e.time < read := hNlt i e hiN he
    exact Or.inr ⟨i, t, hacc, by simpa only [het] using heLt⟩

/-- An erased-tree membership fact at a strict read lifts to bodies-membership
of a *specific* named carrier already known to be a run block: any witness
`exists_named_of_mem_stateBeforeTime` returns shares the same root, hence (root
collision freedom) is that same carrier. -/
private theorem namedMem_of_erasedMem_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {read : Time} {D : NamedBlock V}
    (hDrun : RunBlock S rho D)
    (hmem : D.erase ∈ (rho.storeBeforeTime S v read).core.T) :
    D ∈ (rho.storeBeforeTime S v read).bodies := by
  obtain ⟨E, hEmem, hEerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read v hmem
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed read
  have hEmem' : E ∈ (rho.stateBefore S n v).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hEmem
  have hErun : RunBlock S rho E :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hEmem'
  have hrooteq : E.root = D.root := by
    rw [← Proofs.NamedWire.erase_root E, ← Proofs.NamedWire.erase_root D, hEerase]
  have hDE : D = E :=
    adm.toNamedRootCollisionFree.root_injective D E hDrun hErun D E
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self E))
      hrooteq.symm
  rw [hDE]
  exact hEmem

omit [Fintype V] in
private theorem preceq_cases {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      left
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node p s root gf support rows proposer =>
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent, Bool.or_eq_true,
        decide_eq_true_eq] using h

omit [Fintype V] in
private theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      have hB : B = .genesis := by simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
      simpa only [← hB] using hAB
  | node p s root gf support rows proposer ih =>
      rcases preceq_cases hBC with rfl | hparent
      · exact hAB
      · change (decide (A = .node p s root gf support rows proposer) ||
          NamedBlock.preceq A p) = true
        simp only [Bool.or_eq_true]
        exact Or.inr (ih hparent)

private theorem runBlock_ancestor {S : Setup V} {rho : Run V} {D E : NamedBlock V}
    (hD : RunBlock S rho D) (hED : NamedBlock.Preceq E D) : RunBlock S rho E := by
  obtain ⟨B, hB, hDB⟩ := hD
  exact ⟨B, hB, named_preceq_trans hED hDB⟩

omit [Fintype V] in
private theorem mem_named_chain_attestations_own {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) : a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

/-- Two erased witnesses of run blocks with the same root are the same block. -/
private theorem runBlockOf_root_unique
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {X Y : Block V} (hX : RunBlockOf S rho X)
    (hY : RunBlockOf S rho Y)
    (hroot : X.root = Y.root) : X = Y := by
  obtain ⟨DX, hXe, hXrun⟩ := hX
  obtain ⟨DY, hYe, hYrun⟩ := hY
  have hDeq : DX = DY :=
    adm.toNamedRootCollisionFree.root_injective
      DX DY hXrun hYrun DX DY (Or.inl (Proofs.NamedAncestry.named_self DX))
      (Or.inr (Proofs.NamedAncestry.named_self DY))
      (by rw [← Proofs.NamedWire.erase_root DX, ← Proofs.NamedWire.erase_root DY, hXe, hYe]; exact hroot)
  rw [← hXe, ← hYe, hDeq]

/-- The store's justified block is always a named run block at an honest
strict read. -/
private theorem runBlockOfJustified_atStrictRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (read : Time) :
    RunBlockOf S rho (rho.storeBeforeTime S v read).J :=
  Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime
    S adm.toNamedScheduleWellFormed hv read
    (Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho read v)

/-- A `Certificate` at an honest strict-read store's own justification height
and root, built directly from the named justification carrier a
`storeJustificationOnChain` producer supplies (no admissibility premise beyond
what locates the carrier at an honest event-prefix index). -/
private theorem certificateOfNamedJustification_atStrictRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time)
    (hnz : (rho.storeBeforeTime S w read).h_j ≠ 0) :
    Certificate S rho (rho.storeBeforeTime S w read).h_j
      (rho.storeBeforeTime S w read).J.root := by
  obtain ⟨D, hD, hDJ, hDhj⟩ := Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed read
  have hDmem' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDmem'
  have hnzD : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by rw [hDhj]; exact hnz
  obtain ⟨J, hJD, hJerase, Q, hQ, hwit⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg D hnzD
  have hJrun : RunBlock S rho J := runBlock_ancestor hDrun hJD
  have hJeraseEq : J.erase = (rho.storeBeforeTime S w read).J := by
    rw [hJerase]; exact hDJ
  have hroot : J.root = (rho.storeBeforeTime S w read).J.root := by
    rw [← Proofs.NamedWire.erase_root J, hJeraseEq]
  refine ⟨Q, hQ, ?_⟩
  intro u hu
  obtain ⟨carrier, a, hcarrier, harow, hval, hpair⟩ := hwit u hu
  have hcarrierRun : RunBlock S rho carrier := runBlock_ancestor hDrun hcarrier
  have hDhjEq : (Protocol.derive_named S.E S.cfg D).h_j =
      (rho.storeBeforeTime S w read).h_j := hDhj
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun, mem_named_chain_attestations_own harow⟩, hval, ?_⟩
  rw [hpair, hDhjEq, hroot]

/-- Before a no-rise proposal, every earlier honest-store finalization is
compatible with (in fact, precedes) the fixed target's justification carrier.
The carrier's justification height is exactly `H - 1`, so its derived height
has reached `H`; the local finalization carrier's height is strictly below the
capped local frontier, which crosses `H`, so the named finalization-agreement
producer orients this directly (no delivery/freshness case split needed: the
old "already rebased" branch was an artifact of `no_off_can_finalization`'s
`compatible` disjunction and does not arise from `finalized_preceq_of_
height_lt`'s single, correctly-oriented conclusion). -/
private theorem fixedHeightCarrier_finalizedBelowAtPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {carrier : NamedBlock V}
    (hcarrierRun : RunBlock S rho carrier)
    (hcarrierJust : Internal.NamedJustifiedAt S.E S.cfg carrier
      (rho.storeBeforeTime S w read).J
      (rho.storeBeforeTime S w read).h_j)
    {p : V} (hp : p ∈ rho.honest)
    {i : Nat} {proposal : Time}
    (hi : i ≤ (rho.events.filter
      (fun e => decide (e.time < proposal))).length)
    (hcap : honestHMaxAt S rho proposal ≤ H) :
    Block.Preceq (rho.stateBefore S i p).st.core.F carrier.erase := by
  let n := (rho.events.filter (fun e => decide (e.time < proposal))).length
  have hiN : i ≤ n := hi
  have hWorld : rho.stateBeforeTime S proposal = rho.stateBefore S n :=
    Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed proposal
  have hstore : rho.storeBeforeTime S p proposal =
      (rho.stateBefore S n p).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun hWorld p)
  have hstrictCap : (rho.storeBeforeTime S p proposal).h_max ≤ H :=
    ((storeBeforeTime_hMax_le_storeAt
        S adm.toNamedScheduleWellFormed p proposal).trans
      (localHMax_le_honestHMaxAt S rho proposal hp)).trans hcap
  have hpreCap : (rho.stateBefore S i p).st.h_max ≤ H :=
    (stateBefore_hMax_mono S rho p hiN).trans (by
      rw [← hstore]
      exact hstrictCap)
  obtain ⟨Dst, hDstMem, hDstF, hDstBound⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho i p
  have hDrun : RunBlock S rho Dst :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hDstMem
  have hcarrierLower : H ≤ (Protocol.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (Proofs.NamedStoreRoots.chainOrder_derive_named
        S.E S.cfg carrier).justified_below_height
    have hjEq : (Protocol.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    have hOne : 1 ≤ H :=
      Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (Protocol.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcrossed : (Protocol.derive_named S.E S.cfg Dst).h_F <
      (Protocol.derive_named S.E S.cfg carrier).h :=
    lt_of_lt_of_le (hDstBound.trans_le hpreCap) hcarrierLower
  have hpreceq := NamedFinalizationBridge.finalized_preceq_of_height_lt
    S rho carrier Dst hsb adm.toNamedRootCollisionFree hcarrierRun hDrun hcrossed
  rwa [hDstF] at hpreceq

/-- After one post-GST relay delay, the concrete carrier selected at a
fixed-height interference read is present at every later honest strict read,
provided the public honest frontier has not risen above the fixed height. -/
theorem fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {p : V} (hp : p ∈ rho.honest)
    {target : Time}
    (hpost : S.E.t_GST ≤ read)
    (hdelay : read + S.E.Δ ≤ target)
    (hhor : target ≤ rho.horizon)
    (hcap : honestHMaxAt S rho target ≤ H) :
    ∃ carrier : NamedBlock V,
      carrier ∈ (rho.storeBeforeTime S w read).bodies ∧
        RunBlock S rho carrier ∧
        Internal.NamedJustifiedAt S.E S.cfg carrier
          (rho.storeBeforeTime S w read).J
          (rho.storeBeforeTime S w read).h_j ∧
        carrier ∈ (rho.storeBeforeTime S p target).bodies := by
  obtain ⟨carrier, hcarrierAt, hcarrierRun, hcarrierJust⟩ :=
    h.carrierExists
  have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho p carrier target := by
    intro i hi
    exact fixedHeightCarrier_finalizedBelowAtPrefix
      S adm hsb h hcarrierRun hcarrierJust hp hi hcap
  rcases carrierAcceptsBeforeStrictRead S adm w read hcarrierAt with
    hgen | ⟨i, t, hacc, htRead⟩
  · have hzero : H - 1 = 0 := by
      calc
        H - 1 = (rho.storeBeforeTime S w read).h_j :=
          h.fixedTarget.justificationHeight.symm
        _ = (Protocol.derive_named S.E S.cfg carrier).h_j :=
          hcarrierJust.2.symm
        _ = 0 := by rw [hgen]; rfl
    exact False.elim ((Nat.ne_of_gt h.targetHeightPositive) hzero)
  · have hcarrierPos : 0 < carrier.slot := by
      have h' := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
      rw [Proofs.NamedWire.erase_slot] at h'
      exact Nat.zero_lt_of_lt h'
    have htInput : t < target - S.E.Δ := by
      apply (lt_sub_iff_add_lt).2
      exact (Int.add_lt_add_right htRead S.E.Δ).trans_le hdelay
    have hpostInput : S.E.t_GST ≤ target - S.E.Δ := by
      apply (le_sub_iff_add_le).2
      exact (Int.add_le_add_right hpost S.E.Δ).trans hdelay
    have hhop : (target - S.E.Δ) + S.E.Δ = target :=
      sub_add_cancel target S.E.Δ
    have hadmit : Protocol.AdmittedBefore
        S rho p carrier.erase target :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm h.readerHonest hp hcarrierPos hacc htInput hpostInput
          hhop hhor hFhist
    have hcarrierTargetErased : carrier.erase ∈
        (rho.storeBeforeTime S p target).core.T :=
      (Protocol.admittedBefore_mem_and_stamp
        S adm.toNamedScheduleWellFormed hadmit).1
    have hcarrierTarget : carrier ∈
        (rho.storeBeforeTime S p target).bodies :=
      namedMem_of_erasedMem_stateBeforeTime S adm hp hcarrierRun
        hcarrierTargetErased
    exact ⟨carrier, hcarrierAt, hcarrierRun, hcarrierJust,
      hcarrierTarget⟩

/-- A fixed-height carrier in a later honest strict store identifies that
store's selected FG root with the original fixed target whenever the later
local frontier is still at most the fixed height. -/
theorem fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_le
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {p : V} (hp : p ∈ rho.honest)
    {target : Time} {carrier : NamedBlock V}
    (hcarrierAt : carrier ∈ (rho.storeBeforeTime S w read).bodies)
    (hcarrierJust : Internal.NamedJustifiedAt S.E S.cfg carrier
      (rho.storeBeforeTime S w read).J
      (rho.storeBeforeTime S w read).h_j)
    (hcarrierTarget : carrier ∈ (rho.storeBeforeTime S p target).bodies)
    (hlocalCap : (rho.storeBeforeTime S p target).h_max ≤ H) :
    Protocol.get_fg_root
        (rho.storeBeforeTime S p target).toHealing.toFG =
      (rho.storeBeforeTime S w read).J := by
  let later := rho.storeBeforeTime S p target
  have hOne : 1 ≤ H :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have hcarrierLower :
      H ≤ (Protocol.derive_named S.E S.cfg carrier).h := by
    have hjlt :=
      (Proofs.NamedStoreRoots.chainOrder_derive_named
        S.E S.cfg carrier).justified_below_height
    have hjEq : (Protocol.derive_named S.E S.cfg carrier).h_j = H - 1 :=
      hcarrierJust.2.trans h.fixedTarget.justificationHeight
    rw [hjEq] at hjlt
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hOne).symm
      _ ≤ (Protocol.derive_named S.E S.cfg carrier).h :=
        Nat.succ_le_iff.mpr hjlt
  have hcarrierTarget' : carrier ∈ later.bodies := by
    simpa only [later] using hcarrierTarget
  have hHleLater : H ≤ later.h_max :=
    hcarrierLower.trans
      (Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
        S rho target p carrier hcarrierTarget')
  have hlaterCap : later.h_max ≤ H := by simpa only [later] using hlocalCap
  have hlaterMax : later.h_max = H := Nat.le_antisymm hlaterCap hHleLater
  have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg later :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho target p
  have hbelow : later.h_j < later.h_max :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime S rho target p
  have hcarrierHj : (Protocol.derive_named S.E S.cfg carrier).h_j = H - 1 :=
    hcarrierJust.2.trans h.fixedTarget.justificationHeight
  have hcarrierHjLower : H - 1 ≤ later.h_j := by
    rw [← hcarrierHj]
    exact hnoHigh carrier hcarrierTarget'
  have hlaterHj : later.h_j = H - 1 := by
    apply Nat.le_antisymm
    · exact Nat.le_sub_one_of_lt (hbelow.trans_le hlaterCap)
    · exact hcarrierHjLower
  have hHsucc : H - 1 + 1 = H := Nat.sub_add_cancel hOne
  have hlaterGate : later.h_max = later.h_j + 1 := by
    rw [hlaterMax, hlaterHj, hHsucc]
  have hlaterHjNe : later.h_j ≠ 0 := by
    rw [hlaterHj]
    exact Nat.ne_of_gt h.targetHeightPositive
  have hcertLater : Certificate S rho (H - 1) later.J.root := by
    have hcert' := certificateOfNamedJustification_atStrictRead S adm hp target
      (by simpa only [later] using hlaterHjNe)
    have hhjRaw : (rho.storeBeforeTime S p target).h_j = H - 1 := hlaterHj
    rw [hhjRaw] at hcert'
    simpa only [later] using hcert'
  have hrootEq : later.J.root = (rho.storeBeforeTime S w read).J.root :=
    h.fixedTarget.uniqueAtHeight later.J.root hcertLater
  have htargetEq : later.J = (rho.storeBeforeTime S w read).J :=
    runBlockOf_root_unique adm
      (runBlockOfJustified_atStrictRead S adm hp target)
      h.fixedTarget.targetBlock hrootEq
  have hrootLater :
      Protocol.get_fg_root later.toHealing.toFG = later.J := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_pos hlaterGate]
  simpa only [later] using hrootLater.trans htargetEq



/-- One post-GST delay packages both fixed-target persistence and exact
fixed-frontier preservation at an arbitrary later honest strict read. -/
theorem fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {p : V} (hp : p ∈ rho.honest)
    {target : Time}
    (hpost : S.E.t_GST ≤ read)
    (hdelay : read + S.E.Δ ≤ target)
    (hhor : target ≤ rho.horizon)
    (hcap : honestHMaxAt S rho target ≤ H) :
    Protocol.get_fg_root
          (rho.storeBeforeTime S p target).toHealing.toFG =
        (rho.storeBeforeTime S w read).J ∧
      (rho.storeBeforeTime S p target).h_max = H := by
  obtain ⟨carrier, hcarrierAt, _hcarrierRun, hcarrierJust,
      hcarrierTarget⟩ :=
    fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRise
      S adm hsb h hp hpost hdelay hhor hcap
  have hlocalCap :
      (rho.storeBeforeTime S p target).h_max ≤ H :=
    ((storeBeforeTime_hMax_le_storeAt
        S adm.toNamedScheduleWellFormed p target).trans
      (localHMax_le_honestHMaxAt S rho target hp)).trans hcap
  have hroot :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_le
      S adm h hp hcarrierAt hcarrierJust hcarrierTarget hlocalCap
  refine ⟨hroot, ?_⟩
  have hcarrierHeight :
      (Protocol.derive_named S.E S.cfg carrier).h = H :=
    h.carrierDerivedHeight adm hcarrierAt hcarrierJust
  let later := rho.storeBeforeTime S p target
  have hcarrierTarget' : carrier ∈ later.bodies := by
    simpa only [later] using hcarrierTarget
  have hcarrierLocal :
      (Protocol.derive_named S.E S.cfg carrier).h ≤ later.h_max :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
      S rho target p carrier hcarrierTarget'
  have hHle : H ≤ later.h_max := by
    rw [← hcarrierHeight]
    exact hcarrierLocal
  have hlaterCap : later.h_max ≤ H := by
    simpa only [later] using hlocalCap
  have hlaterMax : later.h_max = H :=
    Nat.le_antisymm hlaterCap hHle
  simpa only [later] using hlaterMax



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
