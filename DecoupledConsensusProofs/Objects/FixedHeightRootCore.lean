module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Execution.CertificateUniqueness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.Handlers.Staleness
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison

@[expose] public section


/-! # Clean fixed-height root target
This module isolates the root-interference branch from recovery. At an honest
strict read whose local frontier is exactly `H`, accountable finality safety
rules out the finalized root. Therefore an incompatible selected root is the
active stored justification, its certificate is at `H - 1`, and certificate
uniqueness gives one run-wide target at that fixed height.
The retry interface retains the concrete justification carrier. If that
carrier is admitted at a later honest proposal read, either the honest raw
frontier has risen strictly above `H`, or the exact `get_head` call and the
proposal block produced by that call descend from the previous target. A second
fixed-height conflict after this concrete rebase is impossible.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]




/-- An erased block that is the erasure of some named run block: the
existential form 's C1 recipe uses at an erased `RunBlock` site. -/
def RunBlockOf (S : Setup V) (rho : Run V) (X : Block V) : Prop :=
  ∃ D : NamedBlock V, D.erase = X ∧ RunBlock S rho D

theorem RunBlockOf.of_named {S : Setup V} {rho : Run V} {D : NamedBlock V}
    (h : RunBlock S rho D) : RunBlockOf S rho D.erase := ⟨D, rfl, h⟩

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

/-- Two erased witnesses of run blocks with the same root are the same block:
the named root-collision idealization, transported across `erase`. -/
private theorem runBlockOf_root_unique
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {X Y : Block V} (hX : RunBlockOf S rho X) (hY : RunBlockOf S rho Y)
    (hroot : X.root = Y.root) : X = Y := by
  obtain ⟨DX, hXe, hXrun⟩ := hX
  obtain ⟨DY, hYe, hYrun⟩ := hY
  have hDeq : DX = DY :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      DX DY hXrun hYrun DX DY (Or.inl (Proofs.NamedAncestry.named_self DX))
      (Or.inr (Proofs.NamedAncestry.named_self DY))
      (by rw [← Proofs.NamedWire.erase_root DX, ← Proofs.NamedWire.erase_root DY, hXe, hYe]; exact hroot)
  rw [← hXe, ← hYe, hDeq]

/-- A named body held at an honest strict read is a named run block. -/
private theorem runBlockOf_of_stateBeforeTime_mem
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time)
    {D : NamedBlock V} (hD : D ∈ (rho.storeBeforeTime S w read).bodies) :
    RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
  simpa only [Run.storeBeforeTime, hn] using hD


/-- The store's justified block is always a named run block at an honest
strict read. -/
private theorem runBlockOf_justified_atStrictRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time) :
    RunBlockOf S rho (rho.storeBeforeTime S w read).J := by
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read w
      (Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho read w)
  exact ⟨D, hDe, runBlockOf_of_stateBeforeTime_mem S adm hw read hD⟩


/-- Strict-read form of `certificateOfStoreJustification_atIndex`. -/
private theorem certificateOfStoreJustification_atStrictRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (read : Time)
    (hnz : (rho.storeBeforeTime S w read).h_j ≠ 0) :
    Certificate S rho (rho.storeBeforeTime S w read).h_j
      (rho.storeBeforeTime S w read).J.root := by
  obtain ⟨D, hD, hDJ, hDhj⟩ := Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
  have hDJ' : (Protocol.derive_named S.E S.cfg D).J = (rho.storeBeforeTime S w read).J := hDJ
  have hDhj' : (Protocol.derive_named S.E S.cfg D).h_j =
      (rho.storeBeforeTime S w read).h_j := hDhj
  have hDrun : RunBlock S rho D := runBlockOf_of_stateBeforeTime_mem S adm hw read hD
  have hnzD : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by rw [hDhj']; exact hnz
  obtain ⟨J, hJD, hJerase, Q, hQ, hwit⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg D hnzD
  have hJrun : RunBlock S rho J := runBlock_ancestor hDrun hJD
  have hroot : J.root = (rho.storeBeforeTime S w read).J.root := by
    rw [← Proofs.NamedWire.erase_root J, hJerase, hDJ']
  refine ⟨Q, hQ, ?_⟩
  intro u hu
  obtain ⟨carrier, a, hcarrier, harow, hval, hpair⟩ := hwit u hu
  have hcarrierRun : RunBlock S rho carrier := runBlock_ancestor hDrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun, mem_named_chain_attestations_own harow⟩, hval, ?_⟩
  rw [hpair, hDhj', hroot]

/-- The fixed-`H` justification-root algebra that does not require a protected
incompatible block. -/
structure FixedHeightJustificationRoot
    (S : Setup V) (rho : Run V) (st : Protocol.Store V)
    (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : Certificate S rho (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId,
    Certificate S rho (H - 1) T → T = st.J.root
  targetBlock : RunBlockOf S rho st.J

/-- The recovery-free algebra carried by one fixed-`H` root interference. -/
structure FixedHeightRootTarget
    (S : Setup V) (rho : Run V) (st : Protocol.Store V)
    (P : Block V) (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : Certificate S rho (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId,
    Certificate S rho (H - 1) T → T = st.J.root
  targetBlock : RunBlockOf S rho st.J
  incompatible : Block.compatible st.J P = false

/-- Forget the protected incompatible block from a fixed-height root target. -/
def FixedHeightRootTarget.toJustificationRoot
    {S : Setup V} {rho : Run V} {st : Protocol.Store V}
    {P : Block V} {H : Height}
    (h : FixedHeightRootTarget S rho st P H) :
    FixedHeightJustificationRoot S rho st H :=
  { frontier := h.frontier
    justificationHeight := h.justificationHeight
    gate := h.gate
    certificate := h.certificate
    uniqueAtHeight := h.uniqueAtHeight
    targetBlock := h.targetBlock }

/-- The active fixed-height target is exactly the store's selected FG root. -/
theorem FixedHeightJustificationRoot.fgRoot_eq_target
    {S : Setup V} {rho : Run V} {st : Protocol.Store V}
    {H : Height}
    (h : FixedHeightJustificationRoot S rho st H) :
    Protocol.get_fg_root st.toHealing.toFG = st.J := by
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
    if_pos h.gate]

/-- Any run block certified at this fixed height is the stored target block. -/
theorem FixedHeightJustificationRoot.certificateTarget_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st : Protocol.Store V} {X : Block V} {H : Height}
    (h : FixedHeightJustificationRoot S rho st H)
    (hXrun : RunBlockOf S rho X)
    (hcert : Certificate S rho (H - 1) X.root) :
    X = st.J :=
  runBlockOf_root_unique adm hXrun h.targetBlock (h.uniqueAtHeight X.root hcert)

/-- Two fixed-height root interferences select the same run-wide target. -/
theorem FixedHeightJustificationRoot.target_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st₁ st₂ : Protocol.Store V} {H : Height}
    (h₁ : FixedHeightJustificationRoot S rho st₁ H)
    (h₂ : FixedHeightJustificationRoot S rho st₂ H) :
    st₂.J = st₁.J := by
  exact h₁.certificateTarget_eq adm h₂.targetBlock h₂.certificate

/-- A second same-height target conflict is impossible after the first target
has been concretely rebased into the second protected block. -/
theorem FixedHeightJustificationRoot.not_again_after_target_rebase
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st₁ st₂ : Protocol.Store V} {P₂ : Block V} {H : Height}
    (h₁ : FixedHeightJustificationRoot S rho st₁ H)
    (h₂ : FixedHeightRootTarget S rho st₂ P₂ H)
    (hrebase : Block.Preceq st₁.J P₂) : False := by
  have htarget : st₂.J = st₁.J :=
    h₁.target_eq adm h₂.toJustificationRoot
  have htargetP₂ : Block.Preceq st₂.J P₂ := by
    rw [htarget]
    exact hrebase
  have hcompatible : Block.compatible st₂.J P₂ = true :=
    Block.compatible_of_preceq_common htargetP₂ (Block.preceq_self P₂)
  rw [h₂.incompatible] at hcompatible
  contradiction

/-- Compatibility corollary for the original fixed-height target interface. -/
theorem FixedHeightRootTarget.fgRoot_eq_target
    {S : Setup V} {rho : Run V} {st : Protocol.Store V}
    {P : Block V} {H : Height}
    (h : FixedHeightRootTarget S rho st P H) :
    Protocol.get_fg_root st.toHealing.toFG = st.J :=
  h.toJustificationRoot.fgRoot_eq_target

/-- Compatibility corollary for the original fixed-height target interface. -/
theorem FixedHeightRootTarget.certificateTarget_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st : Protocol.Store V} {P X : Block V} {H : Height}
    (h : FixedHeightRootTarget S rho st P H)
    (hXrun : RunBlockOf S rho X)
    (hcert : Certificate S rho (H - 1) X.root) :
    X = st.J :=
  h.toJustificationRoot.certificateTarget_eq adm hXrun hcert

/-- Compatibility corollary for the original fixed-height target interface. -/
theorem FixedHeightRootTarget.target_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st₁ st₂ : Protocol.Store V} {P₁ P₂ : Block V} {H : Height}
    (h₁ : FixedHeightRootTarget S rho st₁ P₁ H)
    (h₂ : FixedHeightRootTarget S rho st₂ P₂ H) :
    st₂.J = st₁.J :=
  h₁.toJustificationRoot.target_eq adm h₂.toJustificationRoot

/-- Compatibility corollary for the original fixed-height target interface. -/
theorem FixedHeightRootTarget.not_again_after_target_rebase
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {st₁ st₂ : Protocol.Store V} {P₁ P₂ : Block V} {H : Height}
    (h₁ : FixedHeightRootTarget S rho st₁ P₁ H)
    (h₂ : FixedHeightRootTarget S rho st₂ P₂ H)
    (hrebase : Block.Preceq st₁.J P₂) : False :=
  h₁.toJustificationRoot.not_again_after_target_rebase adm h₂ hrebase


/-- One fixed-height justification root at an actual honest strict read,
without a protected incompatible block. The justification carrier and the
protected block are named bodies (design note C1): a bare `Block V`
carrier can no longer be an `Execution.RunBlock`, which now lives over
`NamedBlock V`, so both existentials name a body and record its erasure. -/
structure FixedHeightJustificationRootAtRead
    (S : Setup V) (rho : Run V) (H : Height)
    (w : V) (read : Time) : Prop where
  readerHonest : w ∈ rho.honest
  readInHorizon : read ≤ rho.horizon
  carrierExists : ∃ D : NamedBlock V,
    D ∈ (rho.storeBeforeTime S w read).bodies ∧
      RunBlock S rho D ∧
      Internal.NamedJustifiedAt S.E S.cfg D
        (rho.storeBeforeTime S w read).J
        (rho.storeBeforeTime S w read).h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : FixedHeightJustificationRoot S rho
    (rho.storeBeforeTime S w read).core H


/-- One fixed-height interference at an actual honest strict read. The
justification carrier and the protected block are named bodies (design note C1,
derived-state class): `protectedHeight` merges the prior `protectedBlock` and
`protectedHeight` fields into one named witness, since both need the same
named body behind `P` to state `RunBlock`/`derive_named` at all. -/
structure FixedHeightRootInterferenceAtRead
    (S : Setup V) (rho : Run V) (H : Height)
    (w : V) (read : Time) (P : Block V) : Prop where
  readerHonest : w ∈ rho.honest
  readInHorizon : read ≤ rho.horizon
  protectedProcessed : P ∈ (rho.storeBeforeTime S w read).T
  protectedHeight : ∃ Pn : NamedBlock V, Pn.erase = P ∧ RunBlock S rho Pn ∧
    H ≤ (Protocol.derive_named S.E S.cfg Pn).h
  interference : FGRootInterferenceAt (rho.storeBeforeTime S w read) P
  carrierExists : ∃ D : NamedBlock V,
    D ∈ (rho.storeBeforeTime S w read).bodies ∧
      RunBlock S rho D ∧
      Internal.NamedJustifiedAt S.E S.cfg D
        (rho.storeBeforeTime S w read).J
        (rho.storeBeforeTime S w read).h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : FixedHeightRootTarget S rho
    (rho.storeBeforeTime S w read).core P H

/-- Forget the protected interference from a fixed-height strict-read record. -/
def FixedHeightRootInterferenceAtRead.toJustificationRootAtRead
    {S : Setup V} {rho : Run V} {H : Height}
    {w : V} {read : Time} {P : Block V}
    (h : FixedHeightRootInterferenceAtRead S rho H w read P) :
    FixedHeightJustificationRootAtRead S rho H w read :=
  { readerHonest := h.readerHonest
    readInHorizon := h.readInHorizon
    carrierExists := h.carrierExists
    targetHeightPositive := h.targetHeightPositive
    fixedTarget := h.fixedTarget.toJustificationRoot }










private theorem coherent_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Proofs.NamedStore.Coherent S.E S.cfg (rho.storeBeforeTime S v t) :=
  (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1






private theorem finalizedCompatibleAtFixedHeightRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} (hw : w ∈ rho.honest)
    (read : Time) {P : Block V} {Pn : NamedBlock V}
    (hPnErase : Pn.erase = P) (hPrun : RunBlock S rho Pn)
    (hPheight : H ≤ (Protocol.derive_named S.E S.cfg Pn).h)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = H) :
    Block.compatible (rho.storeBeforeTime S w read).F P = true := by
  let st := rho.storeBeforeTime S w read
  have hco : Proofs.NamedStore.Coherent S.E S.cfg st := coherent_stateBeforeTime S rho read w
  obtain ⟨Dst, hDstMem, hDstF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho read w
  have hDstMem' : Dst ∈ st.bodies := by simpa only [st] using hDstMem
  have hDstF' : (Protocol.derive_named S.E S.cfg Dst).F = st.F := by
    simpa only [st] using hDstF
  have hDrun : RunBlock S rho Dst :=
    runBlockOf_of_stateBeforeTime_mem S adm hw read hDstMem'
  have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg st :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho read w
  have hbelow : st.h_j < st.h_max :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime S rho read w
  have hcrossed : (Protocol.derive_named S.E S.cfg Dst).h_F <
      (Protocol.derive_named S.E S.cfg Pn).h := by
    calc
      (Protocol.derive_named S.E S.cfg Dst).h_F ≤
          (Protocol.derive_named S.E S.cfg Dst).h_j :=
        (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg Dst).heights_ordered
      _ ≤ st.h_j := hnoHigh Dst hDstMem'
      _ < st.h_max := hbelow
      _ = H := by simpa only [st] using hfrontier
      _ ≤ (Protocol.derive_named S.E S.cfg Pn).h := hPheight
  have hpreceq := NamedFinalizationBridge.finalized_preceq_of_height_lt
    S rho Pn Dst hsb adm.toNamedRootCollisionFree hPrun hDrun hcrossed
  rw [hDstF'] at hpreceq
  simp only [Block.compatible, Bool.or_eq_true]
  exact Or.inl (by simpa only [st, hPnErase] using hpreceq)

/-- Construct the complete fixed-height target from a root interference at an
actual honest strict read. -/
theorem fixedHeightRootInterferenceAtRead_of_interference
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} (hw : w ∈ rho.honest)
    {read : Time} (hread : read ≤ rho.horizon) {P : Block V}
    (hPmem : P ∈ (rho.storeBeforeTime S w read).T)
    {Pn : NamedBlock V} (hPnErase : Pn.erase = P) (hPrun : RunBlock S rho Pn)
    (hPheight : H ≤ (Protocol.derive_named S.E S.cfg Pn).h)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = H)
    (hint : FGRootInterferenceAt (rho.storeBeforeTime S w read) P) :
    FixedHeightRootInterferenceAtRead S rho H w read P := by
  let st := rho.storeBeforeTime S w read
  have hFsafe : Block.compatible st.F P = true :=
    finalizedCompatibleAtFixedHeightRead S adm hsb hw read hPnErase hPrun
      hPheight hfrontier
  have hrootBad : Block.compatible
      (Protocol.get_fg_root st.toHealing.toFG) P = false := by
    simpa only [st, FGRootInterferenceAt] using hint
  have hgate : st.h_max = st.h_j + 1 := by
    by_contra hnot
    have hrootF : Protocol.get_fg_root st.toHealing.toFG = st.F := by
      simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_neg hnot]
    rw [hrootF, hFsafe] at hrootBad
    contradiction
  have hrootJ : Protocol.get_fg_root st.toHealing.toFG = st.J := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_pos hgate]
  have hJbad : Block.compatible st.J P = false := by
    rw [hrootJ] at hrootBad
    exact hrootBad
  have hhj : st.h_j = H - 1 := by
    have hfrontier' : st.h_max = H := by simpa only [st] using hfrontier
    exact Nat.eq_sub_of_add_eq (hgate.symm.trans hfrontier')
  have hJne : st.J ≠ Block.genesis := by
    intro hgen
    rw [hgen] at hJbad
    simp [Block.compatible, Protocol.preceq_genesis] at hJbad
  obtain ⟨D, hDmem, hDJeq, hDhjeq⟩ :=
    Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
  have hDmem' : D ∈ st.bodies := by simpa only [st] using hDmem
  have hDrun : RunBlock S rho D := runBlockOf_of_stateBeforeTime_mem S adm hw read hDmem'
  have hhjne : st.h_j ≠ 0 := by
    intro hz
    apply hJne
    exact hDJeq.symm.trans (NamedJustificationCertificates.justified_zero_is_genesis
      S.E S.cfg D (by rw [hDhjeq]; exact hz))
  have hcert : Certificate S rho (H - 1) st.J.root := by
    have hcertSt := certificateOfStoreJustification_atStrictRead S adm hw read hhjne
    have hhjRaw : (rho.storeBeforeTime S w read).h_j = H - 1 := hhj
    rw [hhjRaw] at hcertSt
    simpa only [st] using hcertSt
  have htargetPos : 0 < H - 1 := by
    rw [← hhj]
    exact Nat.zero_lt_of_ne_zero hhjne
  refine
    { readerHonest := hw
      readInHorizon := hread
      protectedProcessed := by simpa only [st] using hPmem
      protectedHeight := ⟨Pn, hPnErase, hPrun, hPheight⟩
      interference := hint
      carrierExists :=
        ⟨D, by simpa only [st] using hDmem', hDrun,
          by simpa only [st] using And.intro hDJeq hDhjeq⟩
      targetHeightPositive := htargetPos
      fixedTarget :=
        { frontier := hfrontier
          justificationHeight := by simpa only [st] using hhj
          gate := by simpa only [st] using hgate
          certificate := by simpa only [st] using hcert
          uniqueAtHeight := ?_
          targetBlock := runBlockOf_justified_atStrictRead S adm hw read
          incompatible := by simpa only [st] using hJbad } }
  intro T hT
  apply certificateTarget_unique S adm hfb (H - 1) T st.J.root hT
  exact hcert

/-- A certified prefix at the fixed frontier makes the selected FG root
compatible with the protected target. -/
theorem getFGRoot_compatible_of_fixedFrontier_certifiedPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} (hw : w ∈ rho.honest)
    {read : Time} (hread : read ≤ rho.horizon) {T : Block V}
    (hTmem : T ∈ (rho.storeBeforeTime S w read).T)
    {Tn : NamedBlock V} (hTnErase : Tn.erase = T) (hTrun : RunBlock S rho Tn)
    (hTheight : H ≤ (Protocol.derive_named S.E S.cfg Tn).h)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = H)
    {C : Block V} {Cn : NamedBlock V}
    (hCnErase : Cn.erase = C) (hCrun : RunBlock S rho Cn)
    (hcert : Certificate S rho (H - 1) C.root)
    (hCT : Block.Preceq C T) :
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T = true := by
  by_contra hnot
  have hrootBad : Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hint : FGRootInterferenceAt (rho.storeBeforeTime S w read) T := by
    simpa only [FGRootInterferenceAt] using hrootBad
  have hfixed := fixedHeightRootInterferenceAtRead_of_interference
    S adm hfb hsb hw hread hTmem hTnErase hTrun hTheight hfrontier hint
  have hCeq : C = (rho.storeBeforeTime S w read).J :=
    hfixed.fixedTarget.certificateTarget_eq adm ⟨Cn, hCnErase, hCrun⟩ hcert
  have hJpre : Block.Preceq (rho.storeBeforeTime S w read).J T := by
    rw [← hCeq]
    exact hCT
  have hcompatible : Block.compatible
      (rho.storeBeforeTime S w read).J T = true :=
    Block.compatible_of_preceq_common hJpre (Block.preceq_self T)
  rw [hfixed.fixedTarget.incompatible] at hcompatible
  contradiction

/-- A certified prefix at the fixed frontier makes both finality-gadget
filters noninterfering for the protected target. -/
theorem finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    (hsb : SlashableBound S rho)
    {H : Height} {w : V} (hw : w ∈ rho.honest)
    {read : Time} (hread : read ≤ rho.horizon) {T : Block V}
    (hTmem : T ∈ (rho.storeBeforeTime S w read).T)
    {Tn : NamedBlock V} (hTnMem : Tn ∈ (rho.storeBeforeTime S w read).bodies)
    (hTnErase : Tn.erase = T) (hTrun : RunBlock S rho Tn)
    (hTheight : H ≤ (Protocol.derive_named S.E S.cfg Tn).h)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = H)
    {C : Block V} {Cn : NamedBlock V}
    (hCnErase : Cn.erase = C) (hCrun : RunBlock S rho Cn)
    (hcert : Certificate S rho (H - 1) C.root)
    (hCT : Block.Preceq C T) :
    FinalityFilterNoninterferenceAtRead S rho w read T := by
  have hcompatible :=
    getFGRoot_compatible_of_fixedFrontier_certifiedPrefix
      S adm hfb hsb hw hread hTmem hTnErase hTrun hTheight hfrontier
      hCnErase hCrun hcert hCT
  unfold FinalityFilterNoninterferenceAtRead
  simp only [Block.compatible, Bool.or_eq_true] at hcompatible
  rcases hcompatible with hrootT | hTroot
  · right
    by_contra hnotFiltered
    have hprogress := filteredOut_hMax_of_root_preceq
      S adm hw hTnMem hTheight (by rw [hTnErase]; exact hrootT)
      (by rw [hTnErase]; exact hnotFiltered)
    rw [hfrontier] at hprogress
    exact (Nat.not_succ_le_self H)
      ((Nat.le_succ (H + 1)).trans hprogress)
  · exact Or.inl hTroot


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
