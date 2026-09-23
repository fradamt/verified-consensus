module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance

public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Execution.EmissionShape

@[expose] public section

/-!
# Directed SG bounds at a read

Actual honest SG emissions below a block bound all three SG-root branches.
The relative-majority branch uses the represented expiry-window majority.
No grade or full-participation assumption is required.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Core admissibility is enough for pooled SG-vote provenance. -/
private theorem honestSGVote_actionEmission_of_mem_storeBeforeTime_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w v : V} {time : Time} {k : Round} {u : Protocol.SGVote V}
    (hv : v ∈ rho.honest) {pre : Protocol.Store V}
    (hstore : (rho.storeBeforeTime S w time).core = pre)
    (hu : u ∈ pre.toHealing.sg_votes k)
    (huv : u.val_index = v) :
    u = actionSGVoteAt S rho v k ∧
      rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) := by
  have huStore : u ∈ (rho.storeBeforeTime S w time).core.toHealing.sg_votes k := by
    rw [hstore]
    exact hu
  change u ∈
      ((rho.stateBeforeTime S time w).st.sg_pool k).image Protocol.sgVote at huStore
  obtain ⟨a, ha, hau⟩ := Finset.mem_image.mp huStore
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed time
  have haN : a ∈ (rho.stateBefore S n w).st.sg_pool k := by
    rw [← hn]
    exact ha
  have haround : a.round = k :=
    Proofs.NamedStoreBridge.sgRounds_stateBefore S rho n w k a
      (List.mem_toFinset.mp haN)
  have hav : a.val_index = v := by
    have h := congrArg Protocol.SGVote.val_index hau
    have havu : a.val_index = u.val_index := by
      simpa only [Protocol.sgVote] using h
    exact havu.trans huv
  obtain ⟨j, e, o, hj, hje, hproc, hcarry⟩ :=
    Proofs.Optimistic.processes_attest_of_mem_sg_pool S rho w n k a haN
  obtain ⟨row, hrowEq, ta, hte, hemit⟩ :
      ∃ row : NamedAttestation V, a = row.erase ∧
        ∃ ta : Time, ta ≤ e.time ∧
          rho.emits S row.val_index (Object.attest row) ta := by
    cases o with
    | block Bl =>
        obtain ⟨row, hrowMem, hrowEq⟩ := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq] at hav
          exact hav
        have hrowHon : row.val_index ∈ rho.honest := by
          rw [hrowV]
          exact hv
        obtain ⟨ta, hte, hemit⟩ := adm.toNamedUnforgeable.carried_attest
          w Bl e.time hproc row hrowMem hrowHon
        exact ⟨row, hrowEq, ta, hte, hemit⟩
    | gfVote voteObj => simp only [Proofs.Optimistic.CarriesRow] at hcarry
    | attest row =>
        have hrowEq : a = row.erase := hcarry
        have hrowV : row.val_index = v := by
          rw [hrowEq] at hav
          exact hav
        have hrowHon : row.val_index ∈ rho.honest := by
          rw [hrowV]
          exact hv
        obtain ⟨ta, hte, hemit⟩ := adm.toNamedUnforgeable.unforgeable
          w (Object.attest row) e.time hproc row.val_index hrowHon rfl
        exact ⟨row, hrowEq, ta, hte, hemit⟩
  have hrowHon : row.val_index ∈ rho.honest := by
    have hrowV : row.val_index = v := by
      rw [hrowEq] at hav
      exact hav
    rw [hrowV]
    exact hv
  have hrowRound : row.round = k := by
    rw [hrowEq] at haround
    exact haround
  have hemitV : rho.emits S v (Object.attest row) ta := by
    have hrowV : row.val_index = v := by
      rw [hrowEq] at hav
      exact hav
    exact hrowV ▸ hemit
  have hshape := Proofs.Optimistic.emits_attest_shape S hemitV
  have htime : ta = S.a k := by
    rw [hshape.2, hrowRound]
  have hiMem : Event.tick v ta ∈ rho.events := by
    obtain ⟨i, hi, -⟩ := hemitV
    exact List.mem_of_getElem? hi
  have hactionHor : S.a k ≤ rho.horizon := by
    have h := (adm.in_horizon (Event.tick v ta) hiMem).2
    simpa only [Event.time, htime] using h
  have hexact := honest_emits_exact_actionAttestationAt_of_awake S
    adm.toNamedScheduleWellFormed hv k
    (by simpa only [hrowRound] using Proofs.Optimistic.emits_attest_awake S hemitV)
    hactionHor
  have hrowAction : row = actionAttestationAt S rho v k :=
    Proofs.Optimistic.emits_attest_unique S adm.toNamedScheduleWellFormed
      hemitV hexact
      (hrowRound.trans (actionAttestationAt_shape S rho v k).2.1.symm)
  refine ⟨?_, hexact⟩
  calc
    u = Protocol.sgVote a := hau.symm
    _ = Protocol.sgVote row.erase := by rw [hrowEq]
    _ = Protocol.sgVote (actionAttestationAt S rho v k).erase := by
      rw [hrowAction]
    _ = actionSGVoteAt S rho v k := by
      have hshapeA := actionAttestationAt_shape S rho v k
      simp only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase,
        hshapeA.1, hshapeA.2.1, hshapeA.2.2]

private theorem roundBatch_card_le_one_stateBeforeTime_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {t : Time} {w : V} {r : Round} {v : V} (hv : v ∈ rho.honest) :
    (Protocol.sg_votes_by
      (Protocol.round_batch (rho.stateBeforeTime S t w).st.core.toHealing.gradeView r)
      v).card ≤ 1 := by
  by_cases hr : r = 0
  · subst r
    simp [Protocol.round_batch, Protocol.sg_votes_by]
  · rw [Finset.card_le_one]
    intro u hu z hz
    obtain ⟨huBatch, huv⟩ := Finset.mem_filter.mp hu
    obtain ⟨hzBatch, hzv⟩ := Finset.mem_filter.mp hz
    have hu' : u ∈ (rho.storeBeforeTime S w t).core.toHealing.sg_votes (r - 1) := by
      simpa only [Protocol.round_batch, hr, Protocol.HealingStore.gradeView] using huBatch
    have hz' : z ∈ (rho.storeBeforeTime S w t).core.toHealing.sg_votes (r - 1) := by
      simpa only [Protocol.round_batch, hr, Protocol.HealingStore.gradeView] using hzBatch
    obtain ⟨huEq, -⟩ := honestSGVote_actionEmission_of_mem_storeBeforeTime_core
      S adm hv rfl hu' huv
    obtain ⟨hzEq, -⟩ := honestSGVote_actionEmission_of_mem_storeBeforeTime_core
      S adm hv rfl hz' hzv
    exact huEq.trans hzEq.symm

private theorem fresh_anchor_preceq_of_honestWeightMajority_core
    (S : Setup V) {Hon : Finset V} {r : Round} {Can : Block V}
    {st : Protocol.HealingStore V}
    (hal : BatchAligned st.gradeView Hon r Can)
    (hmajority : HonestWeightMajority S Hon)
    {A : Block V} (hA : A ∈ Protocol.fresh_anchor S.E S.hc st r) :
    Block.Preceq A Can := by
  by_contra hno
  have hfalse : Block.preceq A Can = false := by
    rw [← Bool.not_eq_true]
    exact hno
  have hm := Protocol.HonestWeightMajority.faulty_lt_m hmajority
  have hg1 : Protocol.G1 S.E st.gradeView S.hc r A = false := by
    simp only [Protocol.G1, decide_eq_false_iff_not, Nat.not_le]
    exact lt_of_le_of_lt
      (Proofs.Optimistic.direct_support_le_faulty S.E hal (B := A) (Can := Can) hfalse) hm
  have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)
  exact absurd hmem.2 (by rw [hg1]; simp)

/-- Resolve an honest pooled SG vote against its exact emitted block. -/
theorem rootOnCan_of_emittedSGHistory_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {r : Round} {B : Block V}
    (hhistory : ∀ v ∈ rho.honest,
      rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho v r) B)
    {pre : Protocol.Store V}
    (hstore : (rho.storeBeforeTime S w time).core = pre)
    {u : Protocol.SGVote V} (hu : u ∈ pre.toHealing.sg_votes r)
    (huh : u.val_index ∈ rho.honest) :
    rootOnCan pre.T B u.confirmed = true := by
  obtain ⟨huEq, hemit⟩ :=
    honestSGVote_actionEmission_of_mem_storeBeforeTime_core S adm huh hstore hu rfl
  have hbelow := hhistory u.val_index huh hemit
  let C := actionSGBlockAt S rho u.val_index r
  have hconfirmed : u.confirmed = some C.root := by
    rw [huEq]
    rfl
  rw [hconfirmed]
  cases hfind : Block.find? pre.T C.root with
  | none => simp only [rootOnCan, hfind]
  | some X =>
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hw time (B := X) (by
            change (rho.stateBeforeTime S time w).st.core = pre at hstore
            rw [hstore]
            exact find?_mem hfind)
      have hCmem : C ∈ (rho.storeBeforeTime S u.val_index (S.a r)).core.T :=
        actionSGBlockAt_mem_storeBeforeTime S rho u.val_index r
      obtain ⟨Cn, hCerase, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed huh (S.a r) hCmem
      have hroot : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXerase, hCerase]
        exact find?_root hfind
      have hnamed := adm.toNamedRootCollisionFree.root_injective
        Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hroot
      have hXC : X = C := hXerase.symm.trans
        ((congrArg NamedBlock.erase hnamed).trans hCerase)
      simpa only [rootOnCan, hfind, hXC] using hbelow


/-- Directed actual emissions align the reader's grade batch. -/
theorem batchAligned_at_read_of_emittedSGHistory
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {r : Round} {B : Block V}
    {pre : Protocol.Store V} (hstore : (rho.storeBeforeTime S w time).core = pre)
    (hhistory : ∀ v ∈ rho.honest,
      rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho v r) B) :
    BatchAligned pre.toHealing.gradeView rho.honest (r + 1) B := by
  constructor
  · intro v hv
    rw [← hstore]
    simpa only [Run.storeBeforeTime, Protocol.HealingStore.gradeView, Protocol.Store.toHealing]
      using roundBatch_card_le_one_stateBeforeTime_core
        S adm (t := time) (w := w) (r := r + 1) (v := v) hv
  · intro v hv u hu
    have huv : u.val_index = v := (Finset.mem_filter.mp hu).2
    have hupool : u ∈ pre.toHealing.sg_votes r := by
      simpa only [Protocol.round_batch, Nat.succ_ne_zero, Nat.add_sub_cancel]
        using (Finset.mem_filter.mp hu).1
    exact rootOnCan_of_emittedSGHistory_at_read S adm hw hhistory hstore hupool (huv ▸ hv)

/-- Directed retained history bounds the SG root, including the round-zero root. -/
theorem getSgRoot_preceq_of_windowHistory_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {base r : Round} {B : Block V} (hspan : base ≤ r - S.hc.η_SG)
    (hhistory : ∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
      rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho v k) B)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {pre : Protocol.Store V}
    (hstore : (rho.storeBeforeTime S w time).core = pre)
    (hwindow : 0 < r → 2 * S.E.electorate.weightOf
        (Protocol.represented_set
          pre.toHealing.sg_votes S.hc.η_SG r \ rho.honest) <
      Protocol.W_r S.E pre.toHealing.sg_votes S.hc.η_SG r)
    (hroot : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B) :
    Block.Preceq (Protocol.get_sg_root S.E S.hc pre.toHealing r) B := by
  by_cases hrzero : r = 0
  · subst r
    rw [get_sg_root_zero]
    exact hroot
  · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
    have hprev : base ≤ r - 1 := hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
    have hbatch := batchAligned_at_read_of_emittedSGHistory S adm hw hstore
      (time := time) (hhistory (r - 1) hprev (Nat.sub_lt hr (by decide)))
    rw [Nat.sub_add_cancel hr] at hbatch
    simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
      Protocol.GradeContract.current, Protocol.currentGradeRead]
    cases hA : Protocol.fresh_anchor S.E S.hc pre.toHealing r with
    | some A =>
        exact fresh_anchor_preceq_of_honestWeightMajority_core
          S hbatch hmajority hA
    | none =>
        dsimp only
        split
        · exact hroot
        · rcases majorityForkChoice_eq_anchor_or_honestLatestHead_of_windowMajority
            S.E (T := pre.T)
            (anchor := Protocol.get_fg_root pre.toHealing.toFG)
            (tree := Protocol.get_filtered_block_tree
              pre.toHealing.toFG) (hwindow hr) with
            hbase | ⟨v, hv, k, hk, u, hu, huv, head, hconfirmed, hfind, _, hpre⟩
          · exact hbase.symm ▸ hroot
          · have hhead := rootOnCan_of_emittedSGHistory_at_read S adm hw
              (hhistory k (hspan.trans (mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk)) hstore hu (huv ▸ hv)
            simp only [rootOnCan, hconfirmed, hfind] at hhead
            exact Block.preceq_trans hpre hhead

#print axioms rootOnCan_of_emittedSGHistory_at_read
#print axioms batchAligned_at_read_of_emittedSGHistory
#print axioms getSgRoot_preceq_of_windowHistory_at_read

end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
